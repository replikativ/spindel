#!/usr/bin/env python3
"""Serial, paired JVM measurements. No measurements execute concurrently."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pairs", type=int, default=3)
    parser.add_argument("--cpu", type=int, default=2)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    classes = root / "target" / "agent-classes"
    classes.mkdir(parents=True, exist_ok=True)
    subprocess.run(["javac", "--release", "17", "-d", str(classes),
                    str(root / "bench" / "BytecodeAgent.java")], check=True)
    agent_manifest = root / "target" / "agent-manifest.mf"
    agent_manifest.write_text("Premain-Class: bench.BytecodeAgent\n\n")
    subprocess.run(["jar", "--create", "--file", str(root / "target" / "bytecode-agent.jar"),
                    "--manifest", str(agent_manifest), "-C", str(classes), "."], check=True)
    manifest = {
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "cpu": args.cpu,
        "pairs": args.pairs,
        "load_before": os.getloadavg(),
        "source_sha256": {
            name: hashlib.sha256((root / name).read_bytes()).hexdigest()
            for name in ["deps.edn", "collection_bench.clj", "run.py", "bench/BytecodeAgent.java"]
        },
        "workers": [],
    }
    for pair in range(args.pairs):
        order = ["baseline", "candidate"] if pair % 2 == 0 else ["candidate", "baseline"]
        for mode in order:
            name = f"pair-{pair + 1}-{mode}"
            command = [
                "/usr/bin/time", "-f",
                '{"elapsed_s":%e,"user_s":%U,"system_s":%S,"max_rss_kib":%M}',
                "-o", str(output / f"{name}.resources"),
                "taskset", "-c", str(args.cpu),
                "clojure", f"-M:{mode}", "-m", "collection-bench",
                mode, str(pair + 1), str(output / f"{name}.json"),
            ]
            print("starting", name, flush=True)
            started = time.monotonic()
            with (output / f"{name}.log").open("w") as log:
                result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
            receipt = {
                "name": name,
                "command": command,
                "exit_code": result.returncode,
                "elapsed_s": time.monotonic() - started,
                "load_after": os.getloadavg(),
            }
            manifest["workers"].append(receipt)
            (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            if result.returncode:
                raise SystemExit(f"{name} failed; inspect {output / (name + '.log')}")
            print("finished", name, round(receipt["elapsed_s"], 2), "seconds", flush=True)
    manifest["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
