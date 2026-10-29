#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""mine_cost_table.py -- build cost_table.json (module -> coqchk seconds) from a
CI job log.

Input: the job log of a Main-repo CI run that executed parallel_chk with
heartbeats enabled (PCHK-MON lines carry `g<N>:<lines>L:<Module.lemma>` -- the
module currently being kernel-checked by lane N; sampling interval 30s).

Method: per lane, track the current module; each heartbeat-to-heartbeat span
is charged to that span's module. Per-lemma spans are aggregated per MODULE
(the prefix before the first dot of the heartbeat name). Platform/Stdlib
entries are dropped. Modules faster than the heartbeat interval are absent
from the table and default to the median at packing time (parallel_chk v3).

Usage:
  python mine_cost_table.py --log <job_log.txt> --out cost_table.json
"""
import argparse
import io
import json
import re
from datetime import datetime

HB = re.compile(r"g(\d):(\d+)L:(\S+)")


def mine(path):
    raw = io.open(path, encoding="utf-8-sig", errors="replace").read()
    ev = []
    for l in raw.splitlines():
        m = re.match(r"^(\S+Z) (.*)$", l)
        if not m:
            continue
        try:
            ev.append((datetime.fromisoformat(m.group(1).replace("Z", "+00:00")), m.group(2)))
        except Exception:
            pass
    cur = {}
    agg = {}
    for ts, msg in ev:
        for mm in HB.finditer(msg):
            g, name = mm.group(1), mm.group(3)
            if name in ("DONE", ""):
                continue
            if "." not in name:
                continue
            module = name.split(".", 1)[0]
            if module in ("Stdlib", "Coq"):
                continue
            key = (g, name)
            if key in cur:
                sec = (ts - cur[key]).total_seconds()
                a = agg.setdefault(module, {"secs": 0.0, "samples": 0})
                a["secs"] += sec
                a["samples"] += 1
            cur[key] = ts
    return {m: round(v["secs"], 1) for m, v in sorted(agg.items()) if v["secs"] > 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    table = mine(args.log)
    # parallel_chk v3 loader contract: {"modules": {module: seconds}} nested;
    # modules absent from the table default to the table median at packing.
    doc = {"modules": dict(sorted(table.items())), "schema": "cw.cost-table/v1 (mine_cost_table)"}
    io.open(args.out, "w", encoding="utf-8").write(
        json.dumps(doc, ensure_ascii=False, indent=1, sort_keys=True))
    total = sum(table.values())
    print("modules:", len(table), "| total cost:", round(total / 3600, 2), "h |",
          "top:", sorted(table.items(), key=lambda x: -x[1])[:3])
    print("written:", args.out)


if __name__ == "__main__":
    main()
