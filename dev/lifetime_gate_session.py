#!/usr/bin/env python3
"""Run beneath spindel-work/bin/exclusive.sh, from this worktree.

Protocol v4: four preregistered AB/BA pairs, at most twelve attempts.
Environmental admission precedes outcomes. Raw attempts are archived; this
runner never replaces historical baselines.
"""
import hashlib
import io
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import uuid


def command(args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def host(own_pids=()):
    return {"at": time.time(), "uptime": command(["uptime"]),
            "load": os.getloadavg()[0],
            "foreign_high_cpu": [line for line in command(
                ["ps", "-eo", "pid=,pcpu=,comm=", "--sort=-pcpu"]).splitlines()
                if float(line.split()[1]) >= 50 and int(line.split()[0]) not in {os.getpid(), *own_pids}]}


SCHEDULE = (("baseline", "candidate"), ("candidate", "baseline")) * 2
MAX_ATTEMPTS = 12


def overloaded(observations, cores):
    return not observations or any(not math.isfinite(o["load"]) or o["load"] < 0
                                   or o["load"] > cores / 2 for o in observations)


def record_host(path, role, window, phase, observation):
    # EDN is read by the pure gate checker. JSON strings/vectors are also EDN.
    row = {"at": observation["at"], "uptime": observation["uptime"],
           "load": observation["load"], "foreign-high-cpu": observation["foreign_high_cpu"],
           "window": window}
    line = "{" + " ".join(":" + k + " " + json.dumps(v, allow_nan=False) for k, v in row.items())
    line += f" :role :{role} :phase :{phase}}}\n"
    with Path(path).open("a") as log:
        log.write(line)


def active_window(path):
    marker = Path(str(path) + ".window")
    return json.loads(marker.read_text()) if marker.exists() else "worker"


def check_pair(paths, host_paths, log_path):
    # Archive enriched v4 reports, then veto environmental invalidity BEFORE
    # evaluating any outcome. No call to evaluate occurs in the invalid branch.
    code = """(require '[clojure.edn :as e] '[clojure.string :as s]
                        '[org.replikativ.spindel.lifetime-gate-rules :as g])
    (let [[bp cp bh ch] *command-line-args*
          read-report (fn [p h]
                        (let [r (assoc (e/read-string (slurp p)) :controller-observations
                                       (mapv e/read-string (s/split-lines (slurp h))))]
                          (spit p (str (pr-str r) "\n")) r))
          b (read-report bp bh) c (read-report cp ch)]
      (if-not (g/pair-load-valid? b c)
        (do (prn {:status :environmental-invalid}) (System/exit 3))
        (try (let [r (g/evaluate b c)]
               (doseq [x r] (prn x))
               (System/exit (if (every? :pass? r) 0 1)))
             (catch Exception x (prn (ex-data x)) (System/exit 2)))))"""
    with log_path.open("w") as log:
        return subprocess.run(["bb", "-cp", "dev", "-e", code, *paths, *host_paths],
                              stdout=log, stderr=subprocess.STDOUT).returncode


def main(output):
    if not Path("/tmp/claude-1000/jvm.lock/owner").exists():
        raise RuntimeError("Use exclusive.sh for the entire session")
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    session = str(uuid.uuid4())
    baseline = command(["git", "rev-parse", "06ce205"])
    candidate = command(["git", "rev-parse", "HEAD"])
    if command(["git", "status", "--porcelain", "--", "src", "dev", "deps.edn", "test"]):
        raise RuntimeError("Commit the measured harness/source/tests before measuring")
    # A source archive in our own worktree, never another contributor's checkout.
    snapshot = Path("target/perf-v4") / session
    snapshot.mkdir(parents=True)
    archive = subprocess.check_output(["git", "archive", baseline, "src"])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
        tree.extractall(snapshot, filter="data")
    cp = command(["clojure", "-Spath", "-M:bench"]).split(os.pathsep)
    classpaths = {
        "baseline": os.pathsep.join(str((snapshot / "src").resolve()) if p == "src" else p for p in cp),
        "candidate": os.pathsep.join(cp),
    }
    manifest = {"id": session, "baseline": baseline, "candidate": candidate,
                "source_trees": {role: command(["git", "rev-parse", rev + ":src"])
                                 for role, rev in [("baseline", baseline), ("candidate", candidate)]},
                "harness_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sorted([*Path("dev").rglob("*.clj*"), Path(__file__)])},
                "protocol_version": 4, "schedule": SCHEDULE,
                "max_attempts": MAX_ATTEMPTS, "aggregation": "all-valid-pairs-must-pass",
                "attempts": []}
    flags = ["-Xmx3g", "-XX:+UseG1GC", "-Dclojure.main.report=stderr"]
    # Use the JVM's actual processor count, the same N recorded in each report.
    cores = int(command(["java", *flags, "-cp", classpaths["candidate"], "clojure.main", "-e",
                         "(print (.availableProcessors (Runtime/getRuntime)))"]))
    manifest["processors"] = cores
    manifest["jvm_flags"] = flags
    accepted = []
    attempt = 0
    manifest_path = output / "session.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    while len(accepted) < len(SCHEDULE) and attempt < MAX_ATTEMPTS:
        attempt += 1
        round_number = len(accepted) + 1
        observation = host()
        entry = {"round": round_number, "attempt": attempt, "order": SCHEDULE[round_number - 1],
                 "admission": observation}
        if overloaded([observation], cores):
            entry["status"] = "environmental-invalid"
            manifest["attempts"].append(entry)
            manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
            time.sleep(30)
            continue
        reports, host_paths = {}, {}
        for index, role in enumerate(SCHEDULE[round_number - 1]):
            revision = baseline if role == "baseline" else candidate
            name = f"r{round_number}-attempt{attempt}-{role}"
            report = output / (name + ".edn")
            host_path = output / (name + "-host.ednlog")
            env = dict(os.environ, SPINDEL_BENCH_SESSION=session, SPINDEL_BENCH_ROUND=str(round_number),
                       SPINDEL_BENCH_ROLE=role, SPINDEL_BENCH_REVISION=revision,
                       SPINDEL_BENCH_HOST_LOG=str(host_path),
                       SPINDEL_BENCH_POSITION=str(2 * (round_number - 1) + index))
            args = ["java", *flags, "-cp", classpaths[role], "clojure.main", "-m",
                    "org.replikativ.spindel.lifetime-gates", "measure", str(report)]
            print("Measuring", name, flush=True)
            record_host(host_path, role, "worker", "start", host())
            with (output / (name + ".log")).open("w") as log:
                process = subprocess.Popen(args, env=env, stdout=log, stderr=subprocess.STDOUT)
                while process.poll() is None:
                    record_host(host_path, role, active_window(host_path), "sample", host([process.pid]))
                    time.sleep(5)
            record_host(host_path, role, "worker", "end", host())
            if process.returncode:
                raise RuntimeError(f"Measurement failed: {name}; see its log")
            reports[role] = str(report)
            host_paths[role] = str(host_path)
        paths = [reports[role] for role in ("baseline", "candidate")]
        gate_log = output / f"r{round_number}-attempt{attempt}-gates.log"
        code = check_pair(paths, [host_paths[role] for role in ("baseline", "candidate")], gate_log)
        if code not in {0, 1, 3}:
            raise RuntimeError("Invalid measurement evidence; no acceptance or baseline publication")
        entry.update(reports=reports, host_logs=host_paths,
                     status="environmental-invalid" if code == 3 else "accepted")
        manifest["attempts"].append(entry)
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
        if code == 3:
            continue
        # A valid failed outcome is retained, never retried for a better result.
        accepted.append(code)
        (output / f"r{round_number}-gates.log").write_bytes(gate_log.read_bytes())
    complete = len(accepted) == len(SCHEDULE)
    all_passed = complete and all(code == 0 for code in accepted)
    manifest.update(status=("passed" if all_passed else "failed") if complete else "inconclusive",
                    gates_passed=all_passed, valid_pairs=len(accepted))
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print("Session:", manifest["status"], flush=True)
    return (0 if all_passed else 1) if complete else 3


if __name__ == "__main__":
    if sys.argv[1] == "observe":
        output, role, window, phase, pid = sys.argv[2:]
        record_host(output, role, window, phase, host([int(pid)]))
        marker = Path(output + ".window")
        temporary = Path(output + ".window.next")
        temporary.write_text(json.dumps(window if phase == "start" else "worker"))
        temporary.replace(marker)
    else:
        sys.exit(main(sys.argv[1]))
