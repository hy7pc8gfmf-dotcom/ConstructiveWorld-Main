#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸③ 跨树毒 token diff：Live 树 vs vo 树 Require 行同步检查器（AX-GUARD 20260925）
==================================================================================
专杀回归路径甲（E957 单树 import 暗雷族／世系倒灌）：同一模块在两树的 Require 面
出现毒 token 单树不对称——一树带 Lra/Psatz 类载体、另一树不带——即 fail（exit 1）。

机制（E957 教训内嵌）：HEAD 双树同源普查对「反向愈合复活」失明；本闸逐模块比对
两树剥注释后的 Require 行集合（正规化空白），分两级报：
  [SINGLE-TREE-POISON]  一树 Require 行带毒 token、另一树同模块无 → exit 1（本闸主咬合面）
  [REQUIRE-DRIFT]       两树 Require 行不等但均无毒 → exit 0 仅登记（卫生信息，供 digest 对账）

用法：
  python gate3_cross_tree_diff.py [--tree-a DIR] [--tree-b DIR] [--json OUT]
  默认 A=Main Live 树，B=vo 镜像树（两树 .v 均在盘）。
退出码：0=无单树毒分歧；1=存在单树毒分歧（暗雷）；2=树路径无效。
"""
import os, re, sys, json, argparse, datetime

POISON_TOKEN_RE = re.compile(
    r"\b(Lra|Psatz|Reals|ClassicalDedekindReals|FunctionalExtensionality|"
    r"Micromega|ClassicalDescription|Logic\.Classical)\b")
REQUIRE_LINE_RE = re.compile(r"\bRequire\b")

def strip_comments(text):
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

def require_face(path):
    """返回该 .v 的 Require 行列表（剥注释、去空白正规化）。"""
    with open(path, encoding="utf-8", errors="replace") as f:
        raw = f.read()
    st = strip_comments(raw)
    reqs = []
    for raw_line, st_line in zip(raw.splitlines(), st.splitlines()):
        if REQUIRE_LINE_RE.search(st_line):
            reqs.append(re.sub(r"\s+", " ", st_line.strip()))
    return reqs

def load_tree(tree):
    mods = {}
    for name in os.listdir(tree):
        if name.endswith(".v") and os.path.isfile(os.path.join(tree, name)):
            mods[name[:-2]] = os.path.join(tree, name)
    return mods

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree-a", default=r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live")
    ap.add_argument("--tree-b", default=r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo")
    ap.add_argument("--json", dest="jsonout", default=None)
    args = ap.parse_args()
    for t in (args.tree_a, args.tree_b):
        if not os.path.isdir(t):
            print(f"[gate3] FATAL: 树不存在: {t}", file=sys.stderr)
            return 2
    A, B = load_tree(args.tree_a), load_tree(args.tree_b)
    now = datetime.datetime.now().isoformat(timespec="seconds")
    common = sorted(set(A) & set(B))
    only_a, only_b = sorted(set(A) - set(B)), sorted(set(B) - set(A))
    poison_div, drift = [], []
    for m in common:
        ra, rb = require_face(A[m]), require_face(B[m])
        pa = [r for r in ra if POISON_TOKEN_RE.search(r)]
        pb = [r for r in rb if POISON_TOKEN_RE.search(r)]
        if pa != pb:  # 毒面单树不对称
            poison_div.append({"module": m, "a_lines": pa, "b_lines": pb})
        elif ra != rb:
            drift.append({"module": m, "a_lines": ra, "b_lines": rb})
    print(f"[gate3] 时点={now}")
    print(f"  树A={args.tree_a}  .v={len(A)}")
    print(f"  树B={args.tree_b}  .v={len(B)}")
    print(f"  共同模块={len(common)}  仅A={len(only_a)}  仅B={len(only_b)}")
    for m in only_a:
        print(f"    ONLY-A {m}.v")
    for m in only_b:
        print(f"    ONLY-B {m}.v")
    if poison_div:
        print(f"  判定=FAIL（单树毒分歧 {len(poison_div)} 件——E957 暗雷族/世系倒灌嫌疑）")
        for d in poison_div:
            print(f"    SINGLE-TREE-POISON {d['module']}.v")
            print(f"      A({os.path.basename(args.tree_a)}): {d['a_lines'] or '（无毒行）'}")
            print(f"      B({os.path.basename(args.tree_b)}): {d['b_lines'] or '（无毒行）'}")
    else:
        print("  判定=PASS（共同模块毒面两树全对称）")
    if drift:
        print(f"  [登记] 无毒 Require 漂移 {len(drift)} 件（卫生信息）:")
        for d in drift[:20]:
            print(f"    REQUIRE-DRIFT {d['module']}.v")
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump({"time": now, "poison_divergence": poison_div,
                       "require_drift": drift, "only_a": only_a, "only_b": only_b},
                      f, ensure_ascii=False, indent=1)
    return 1 if poison_div else 0

if __name__ == "__main__":
    sys.exit(main())
