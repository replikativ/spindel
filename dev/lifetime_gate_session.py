#!/usr/bin/env python3
"""Run beneath spindel-work/bin/exclusive.sh, from this worktree.

One session: fresh JVMs alternate MAIN/candidate for three accepted rounds.
Overloaded attempts are retained and repeated as whole pairs. Stored baseline
is a record of round 2; acceptance always uses this session's paired files.
"""
import hashlib
import io
import json
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


def overloaded(observations, cores):
    return any(o["load"] < 0 or o["load"] > cores / 2 for o in observations)


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
    snapshot = Path("target/perf-v3") / session
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
                                   for p in sorted(Path("dev").rglob("*.clj*"))},
                "attempts": []}
    flags = ["-Xmx3g", "-XX:+UseG1GC", "-Dclojure.main.report=stderr"]
    # Use the JVM's actual processor count, the same N recorded in each report.
    cores = int(command(["java", *flags, "-cp", classpaths["candidate"], "clojure.main", "-e",
                         "(print (.availableProcessors (Runtime/getRuntime)))"]))
    manifest["processors"] = cores
    manifest["jvm_flags"] = flags
    accepted = []
    round_number = 1
    attempt = 0
    while round_number <= 3:
        observation = host()
        with (output / "admission.jsonl").open("a") as log:
            log.write(json.dumps(observation) + "\n")
        if overloaded([observation], cores):
            print("Waiting for quiet host:", observation["uptime"], flush=True)
            time.sleep(30)
            continue
        attempt += 1
        observations = [observation]
        paths = []
        for role, revision in [("baseline", baseline), ("candidate", candidate)]:
            name = f"r{round_number}-attempt{attempt}-{role}"
            report = output / (name + ".edn")
            env = dict(os.environ, SPINDEL_BENCH_SESSION=session, SPINDEL_BENCH_ROUND=str(round_number),
                       SPINDEL_BENCH_ROLE=role, SPINDEL_BENCH_REVISION=revision,
                       SPINDEL_BENCH_POSITION=str(2 * (round_number - 1) + (role == "candidate")))
            args = ["java", *flags, "-cp", classpaths[role], "clojure.main", "-m",
                    "org.replikativ.spindel.lifetime-gates", "measure", str(report)]
            print("Measuring", name, flush=True)
            with (output / (name + ".log")).open("w") as log:
                process = subprocess.Popen(args, env=env, stdout=log, stderr=subprocess.STDOUT)
                while process.poll() is None:
                    observations.append(host([process.pid]))
                    time.sleep(5)
            if process.returncode:
                raise RuntimeError(f"Measurement failed: {name}; see its log")
            paths.append(str(report))
        observations.append(host())
        rejected = overloaded(observations, cores)
        # The JVM monitor samples at a different phase; either monitor can veto.
        check_code = """(require '[clojure.edn :as e] '[org.replikativ.spindel.lifetime-gate-rules :as g])
        (let [reports (mapv #(e/read-string (slurp %)) *command-line-args*)]
          (if-not (every? g/host-quiet? reports)
            (System/exit 3)
            (try (let [r (apply g/evaluate reports)]
                   (doseq [x r] (prn x))
                   (System/exit (if (every? :pass? r) 0 1)))
                 (catch Exception x (prn (ex-data x)) (System/exit 2)))))"""
        with (output / f"r{round_number}-attempt{attempt}-gates.log").open("w") as log:
            result = subprocess.run(["bb", "-cp", "dev", "-e", check_code, *paths],
                                    stdout=log, stderr=subprocess.STDOUT)
        if result.returncode not in {0, 1, 3}:
            raise RuntimeError("Invalid measurement evidence; baseline will not be published")
        rejected |= result.returncode == 3
        manifest["attempts"].append({"round": round_number, "attempt": attempt,
                                     "reports": paths, "host": observations,
                                     "status": "repeat-overloaded" if rejected else "accepted"})
        (output / "session.json").write_text(json.dumps(manifest, indent=2) + "\n")
        if rejected:
            print("Repeating overloaded round", round_number, flush=True)
            continue
        accepted.append((paths, result.returncode))
        (output / f"r{round_number}-gates.log").write_bytes(
            (output / f"r{round_number}-attempt{attempt}-gates.log").read_bytes())
        round_number += 1
    # Keep v2 as historical evidence; the canonical main baseline is regenerated.
    stored = Path("dev/org/replikativ/spindel/baselines/main-06ce205.edn")
    (output / "stored-baseline-v3.edn").write_bytes(Path(accepted[1][0][0]).read_bytes())
    # Baseline publication is explicit: only complete, accepted reports reach it.
    stored.write_bytes(Path(accepted[1][0][0]).read_bytes())
    all_passed = all(code == 0 for paths, code in accepted)
    manifest["gates_passed"] = all_passed
    (output / "session.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Session complete; gates passed:", all_passed, flush=True)
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
