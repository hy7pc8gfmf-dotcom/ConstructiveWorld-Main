#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸① 毒 token grep 守卫（AX-GUARD 20260925）
============================================
扫树内 .v 文件的 Require 行毒 token（公理载体壳线），命中 exit 1 并列明 文件:行。

设计要点（全部来自实勘教训，出处见 _taxguard_ 报告）：
1. 全名匹配、严格大小写——简称陷阱禁入：token 表一律 stdlib 全名
   （ClassicalDedekindReals / FunctionalExtensionality / Micromega / Lra / Psatz /
   Reals / ClassicalDescription / Logic.Classical），禁项目简称（如 CW_219≠全名类）。
   且 \b 词边界 + 大小写敏感：`RealSetoid` 不配 `Reals`（AX-MATRIX §1.3 grep -i 假配教训）。
2. 剥注释后匹配——`(* Require ... Lra ... *)` 注释行不误报（E422 S12 注释假命中教训；
   白皮书词表口径：只有活 Require 行算命中）。剥注释为 (* *) 嵌套感知，保行号不变。
3. 只看含 `Require` 关键字的行（含 `From Stdlib Require Import/Export` 句式，
   无锚定——E-ARCH 教训：`^Require Import` 锚漏 `From Stdlib` 句式）。
4. fail-loud：命中 exit 1；无命中 exit 0；树不存在 exit 2。

用法：
  python gate1_poison_guard.py [--tree DIR]... [--json OUT] [--text]
  默认树：Main Live 树（ConstructiveWorld_Live）。可多次 --tree 扫多树。
  加 --live-x 可附扫 Live_X（850 件面，含探针脚手架，命中另账不混主树）。

退出码：0=洁净（守卫 PASS）；1=命中毒 token（守卫 FAIL，咬合）；2=树路径无效。
"""
import os, re, sys, json, argparse, datetime

POISON_TOKENS = [
    "Lra", "Psatz", "Reals", "ClassicalDedekindReals", "FunctionalExtensionality",
    "Micromega", "ClassicalDescription", "Logic.Classical",
]
TOKEN_RE = re.compile(
    r"\b(" + "|".join(re.escape(t) for t in POISON_TOKENS) + r")\b"
)  # re.escape 保留 \. 为字面点；\b 在点两侧按词字符判定，Logic.Classical 正确配
REQUIRE_RE = re.compile(r"\bRequire\b")

def strip_comments(text):
    """(* *) 嵌套感知剥注释，非注释字符原样保留（换行保留→行号不变）。"""
    out = []
    depth = 0
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1; i += 2
            out.append("  "); continue
        if text.startswith("*)", i) and depth > 0:
            depth -= 1; i += 2
            out.append("  "); continue
        if depth > 0:
            out.append(text[i] if text[i] == "\n" else " ")
            i += 1; continue
        out.append(text[i]); i += 1
    return "".join(out)

def scan_tree(tree):
    hits = []
    nfiles = 0
    for name in sorted(os.listdir(tree)):
        if not name.endswith(".v"):
            continue
        path = os.path.join(tree, name)
        if not os.path.isfile(path):
            continue
        nfiles += 1
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                raw = f.read()
        except OSError as e:
            hits.append({"file": path, "line": 0, "token": "<IO-ERROR>",
                         "text": str(e), "mtime": None})
            continue
        stripped = strip_comments(raw)
        mtime = datetime.datetime.fromtimestamp(os.path.getmtime(path)).isoformat(timespec="seconds")
        for lineno, (raw_line, st_line) in enumerate(
                zip(raw.splitlines(), stripped.splitlines()), 1):
            if REQUIRE_RE.search(st_line):
                m = TOKEN_RE.search(st_line)
                if m:
                    hits.append({"file": path, "line": lineno, "token": m.group(1),
                                 "text": raw_line.strip(), "mtime": mtime})
    return nfiles, hits

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", action="append", default=None,
                    help="树根目录（可多次）")
    ap.add_argument("--live-x", action="store_true",
                    help="附扫 Live_X 树（默认关）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--text", action="store_true", help="只输出人类可读摘要")
    args = ap.parse_args()

    trees = args.tree or [r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live"]
    if args.live_x:
        trees.append(r"D:\ComplexAnalysis\新算法实践\Live_X")

    now = datetime.datetime.now().isoformat(timespec="seconds")
    report = {"scan_time": now, "tokens": POISON_TOKENS, "trees": {}, "total_hits": 0}
    exit_code = 0
    for tree in trees:
        if not os.path.isdir(tree):
            print(f"[gate1] FATAL: 树不存在: {tree}", file=sys.stderr)
            return 2
        nfiles, hits = scan_tree(tree)
        report["trees"][tree] = {"v_files": nfiles, "hits": hits}
        report["total_hits"] += len(hits)
        status = "FAIL(守卫咬合:命中毒token)" if hits else "PASS(洁净)"
        print(f"[gate1] 树={tree}  .v数={nfiles}  命中={len(hits)}  判定={status}  扫描时点={now}")
        for h in hits:
            print(f"  HIT {h['file']}:{h['line']}  token={h['token']}  mtime={h['mtime']}")
            print(f"      {h['text']}")
    if report["total_hits"]:
        exit_code = 1
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1)
    return exit_code

if __name__ == "__main__":
    sys.exit(main())
