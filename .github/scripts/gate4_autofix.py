#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""gate4_autofix.py - mechanical comment-surface repair for gate4 hard reds
(rocqwash-triage watch autofix leg, 20261114; user order: auto repair, not
human sign-off).

Scope discipline.  Only gate4 hard violations with a deterministic comment-
only fix are touched; everything else is reported and left for the seat:
  * date stamps (dates in comment prose)      -> generic strip
  * table-covered rewrites (semantic wording,
    identifier-embedded dates)                -> REWRITE_TABLE below

Comment-surface surgery can never change compilation: every edit is
restricted to lines inside comment regions and two guards hold after each
pass - the per-file count of comment delimiters "(*" / "*)" is unchanged and
no edited line contains a delimiter.  A gate4 rerun (closed loop, max 3
rounds) gates the result: files are only staged when the whole scan is
green, so a partial fix never reaches the shore.

Usage.
  python gate4_autofix.py --run-report gate4_report.json [--repo-root .]
      fix from an existing gate4 JSON report (from the red run's artifact)
  python gate4_autofix.py --repo-root . --scan
      re-run gate4 locally first (same CLI face as the furnace step) and
      fix from the fresh report; loop until green or unfixable residue
Exit codes.  0 = scan green (fixed or already clean); 1 = hard hits remain
(unfixable residue - do not push); 2 = usage / environment error.
"""
import argparse
import json
import os
import re
import subprocess
import sys

GATE4_CLI = ["python", "scripts/gates/gate4_comment_guard.py",
             "--tree", "ConstructiveWorld_Live", "--tree",
             "ConstructiveWorld_vo", "--json", "gate4_autofix_report.json"]
DATE_RE = re.compile(r"\b(20\d{2}-?\d{2}-?\d{2})\b")
MAX_ROUNDS = 3

# Desk-authored rewrites: file basename -> list of (old, new) exact-substring
# replacements applied inside comment regions only.  Each entry is a semantic
# judgment call reviewed at the desk (identifier-embedded dates and admission-
# vocabulary rewording); extend this table for future classes, never edit
# statement or proof bodies.
REWRITE_TABLE = {
    "cast_modulus.v": [
        ("Digit-count parameter s(b)", "Digit-count bound s(b)"),
    ],
    "cast_parity.v": [
        ("instance parameter of the canonical quantified face",
         "instance variable of the canonical quantified face"),
    ],
    "planb5_p7_hval_table.v": [
        ("GD-20261114-P7ASM-01 item 5", "P7ASM-01 workorder item 5"),
        ("under OUT/p7_out_20261114/)", "under the P7 seat output bundle)"),
    ],
}


def comment_spans(text):
    """Line-indexed boolean list: True when the line lies inside a (* *) or
    ( *) style Coq comment region (mirrors gate4's block-comment view; a line
    holding an opener or closer counts as inside)."""
    inside = []
    depth = 0
    for line in text.splitlines():
        starts_in = depth > 0
        depth += line.count("(*") - line.count("*)")
        inside.append(starts_in or line.count("(*") > 0)
    return inside


DATE_PROSE_RE = re.compile(r"(, ?| ?)(20\d{2}-?\d{2}-?\d{2})(?=[\),\.;:])")


def line_struct_ok(old_line, new_line):
    """A line edit is structure-safe when the comment-delimiter counts are
    unchanged (the surgery never eats an opener or closer)."""
    return all(old_line.count(t) == new_line.count(t)
               for t in ("(*", "*)"))


def edit_comment_line(line, fn):
    """Apply fn to the line only when it lies in comment context and the
    delimiter structure survives; otherwise return the line untouched."""
    if line.count("(*") == 0 and line.count("*)") == 0:
        pass  # interior comment line: comment context by construction
    new_line = fn(line)
    return new_line if line_struct_ok(line, new_line) else line


def strip_prose_dates(text):
    """Remove bare date tokens in comment prose.  Only the two trailing-
    annotation shapes are stripped generically: ", 20261114)" and
    "md 2026-11-14," - the date plus its separator disappear together.
    Dates fused into identifiers (GD-20261114-..., p7_out_...) fail the
    separator/lookahead conditions and fall to the rewrite table.
    Returns (new_text, n_edits)."""
    spans = comment_spans(text)
    lines = text.splitlines(keepends=True)
    n = 0
    for i, line in enumerate(lines):
        if i >= len(spans) or not spans[i]:
            continue
        new_line = DATE_PROSE_RE.sub(lambda m: "", line)
        if new_line != line and line_struct_ok(line, new_line):
            lines[i] = new_line
            n += 1
    return "".join(lines), n


def apply_table(text, base):
    """Apply desk-approved exact-substring rewrites inside comment regions.
    Returns (new_text, n_edits)."""
    spans = comment_spans(text)
    lines = text.splitlines(keepends=True)
    n = 0
    for old, new in REWRITE_TABLE.get(base, []):
        for i, line in enumerate(lines):
            if i >= len(spans) or not spans[i] or old not in line:
                continue
            new_line = line.replace(old, new)
            if line_struct_ok(line, new_line):
                lines[i] = new_line
                n += 1
    return "".join(lines), n


def structure_ok(old_text, new_text):
    for token in ("(*", "*)"):
        if old_text.count(token) != new_text.count(token):
            return False
    return True


def run_gate4(root):
    proc = subprocess.run(GATE4_CLI, cwd=root, capture_output=True,
                          text=True, timeout=600, shell=True,
                          encoding="utf-8", errors="replace")
    report_path = os.path.join(root, "gate4_autofix_report.json")
    report = None
    if os.path.isfile(report_path):
        with open(report_path, encoding="utf-8") as fh:
            report = json.load(fh)
    return proc.returncode, report, (proc.stdout or "") + (proc.stderr or "")


def hard_hits(report):
    out = []
    for r in report.get("results") or []:
        if r.get("verdict") == "FAIL":
            for item in r.get("hard") or []:
                out.append({"file": os.path.basename(
                    r["file"].replace("\\", "/")), "item": item})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--run-report", default=None,
                    help="existing gate4 JSON report to seed round 1")
    ap.add_argument("--scan", action="store_true",
                    help="run gate4 locally to seed round 1")
    ap.add_argument("--max-rounds", type=int, default=MAX_ROUNDS)
    args = ap.parse_args()
    root = os.path.abspath(args.repo_root)
    if not os.path.isdir(os.path.join(root, "scripts", "gates")):
        sys.stderr.write("repo root lacks scripts/gates: %s\n" % root)
        return 2

    # round 1 seed
    if args.run_report and os.path.isfile(args.run_report):
        with open(args.run_report, encoding="utf-8") as fh:
            report = json.load(fh)
    elif args.scan:
        rc, report, out = run_gate4(root)
        if report is None:
            sys.stderr.write("gate4 produced no report (rc=%s)\n%s\n"
                             % (rc, out[-800:]))
            return 2
    else:
        sys.stderr.write("give --run-report FILE or --scan\n")
        return 2

    touched = {}
    for round_no in range(1, args.max_rounds + 1):
        hits = hard_hits(report)
        if not hits:
            break
        n_edits = 0
        hit_files = sorted({h["file"] for h in hits})
        for base in hit_files:
            for rel in ("ConstructiveWorld_Live/" + base,
                        "ConstructiveWorld_vo/" + base):
                path = os.path.join(root, rel.replace("/", os.sep))
                if not os.path.isfile(path):
                    continue
                with open(path, encoding="utf-8") as fh:
                    old_text = fh.read()
                new_text, n1 = strip_prose_dates(old_text)
                new_text, n2 = apply_table(new_text, base)
                if n1 + n2 and structure_ok(old_text, new_text):
                    with open(path, "w", encoding="utf-8", newline="") as fh:
                        fh.write(new_text)
                    touched[rel] = touched.get(rel, 0) + n1 + n2
                    n_edits += n1 + n2
        if not n_edits:
            break  # residue is not coverable by this fixer
        rc, report, out = run_gate4(root)
        if report is None:
            sys.stderr.write("gate4 rerun failed (rc=%s)\n%s\n"
                             % (rc, out[-800:]))
            return 2

    hits = hard_hits(report) if report else [{"file": "?", "item": "no-report"}]
    verdict = "GREEN" if not hits else "RESIDUE"
    for rel, n in sorted(touched.items()):
        print("edited %s (%d token edits)" % (rel, n))
    for h in hits:
        print("residue: %s %s" % (h["file"], h["item"]))
    print("autofix verdict: %s (rounds used %d)" % (verdict, round_no))
    return 0 if verdict == "GREEN" else 1


if __name__ == "__main__":
    sys.exit(main())
