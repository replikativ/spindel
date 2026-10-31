#!/usr/bin/env python3
"""Aggregate per-process medians, retaining paired ratios and warm-up flags."""
import json
from pathlib import Path
from statistics import median
import sys


def summary(root):
    workers = [json.loads(p.read_text()) for p in sorted(root.glob("pair-*.json"))]
    output = {"compile": [], "runtime": [], "deferred": [], "inference": []}
    for section in output:
        keys = sorted({(r["kind"], r.get("n", r.get("particles", r.get("size"))))
                       for w in workers for r in w[section]})
        for kind, size in keys:
            selected = {mode: [(w["run-id"], r) for w in workers if w["mode"] == mode
                               for r in w[section]
                               if (r["kind"], r.get("n", r.get("particles", r.get("size")))) == (kind, size)]
                        for mode in ["baseline", "candidate"]}
            row = {"kind": kind, "size": size}
            metrics = ["lower-ms", "compile-ms", "class-bytes", "classes", "lowered-nodes"] if section == "compile" else ["ns-per-op", "thread-bytes-per-op", "total-bytes-per-op"]
            for metric in metrics:
                values = {}
                for mode, items in selected.items():
                    values[mode] = {}
                    for run_id, item in items:
                        if metric.endswith("-ms") and section == "compile":
                            value = median(r[metric[:-3]]["ns"] for r in item["rows"]) / 1e6
                        elif section == "compile":
                            value = item[metric]
                        else:
                            value = median(item[metric])
                        values[mode][run_id] = value
                ratios = [values["candidate"][i] / value for i, value in values["baseline"].items()
                          if i in values["candidate"] and value]
                row[metric] = {
                    **{mode: median(v.values()) for mode, v in values.items() if v},
                    "paired-ratios": ratios,
                    "paired-ratio-median": median(ratios) if ratios else None,
                }
            if section != "compile":
                row["warm-stable"] = {mode: [item["warm-stable?"] for _, item in items]
                                       for mode, items in selected.items()}
                row["sample-jit-ms"] = {mode: [sum(item["jit-ms"]) for _, item in items]
                                        for mode, items in selected.items()}
            output[section].append(row)
    return output


if __name__ == "__main__":
    root = Path(sys.argv[1])
    result = summary(root)
    (root / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
