#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸③ 跨树毒 token diff ＋ 壳模块集隶属检查扩条（AX-GUARD 20260925 ＋ R130 乙案扩条草案 20260926）
================================================================================
【本件=沙箱草案，未落树（禁改仓库 gate 脚本）。差异全文见同目录
 gate3_module_membership_ablation.patch；语义依据=R18 §二裁决（E4）：gate3 扩条必须是
 【模块集隶属检查】而非 diff 型——现闸 diff 逻辑对「两树对称复活」失明（对称=无 diff），
 扩条的独立价值面正在于此。R2 §十.2 同款；gate1 token（乙案态零白名单形）覆盖 Require
 行面，本扩条覆盖文件/模块面，两面合围 ⊇ S3 gate6 的 Require 前缀 grep。】

现闸语义（AX-GUARD 20260925，E957 教训内嵌，零变保留）：
  逐模块比对两树剥注释后的 Require 行集合（正规化空白），分两级报：
  [SINGLE-TREE-POISON] 一树 Require 行带毒 token、另一树同模块无 → exit 1（主咬合面）
  [REQUIRE-DRIFT]      两树 Require 行不等但均无毒 → exit 0 仅登记（卫生信息）

R130 乙案扩条（[M1]，先于现闸毒面比对执行）：
  对 --tree-a/--tree-b 每树独立做【隶属检查】（非两树间比对，故对称复活两树各自咬合）：
  [RESURRECT-MODULE]   树模块集（顶层 .v 基名集）含 CW_ConstructiveWorld_219 → exit 1
                       （壳文件/模块面复活：含改名字节复活、git 检出复活、生成器再运行复活）
  [RESURRECT-REQUIRE]  树内任一 .v 的活 Require 行（剥注释后）含 CW_ConstructiveWorld_219
                       → exit 1（壳依赖行面复活；与 gate1 乙案态 token 同语义双树独立）

R130 落树版增条（单条文件级显式豁免）：唯一豁免面=EXEMPT_FILES={"_t24_probe3.v"}——
  用户禁碰件豁免（内容与存在性受用户明令保护），其壳 Require 行为全树唯余存留处，
  候用户终裁退役与否；仅豁免 [RESURRECT-REQUIRE] 行面且逐笔留账（exempted_hits），
  模块面隶属检查不豁免；除该单件外语义零变。
  响停处置纪律（R13 卡 1 措辞对齐，并入 E4）：命中先跑 digest 三件套（md5＋size＋mtime
  对删除/快照台账）定性「残留 vs 复活」再处置，禁未证先判（R13 B-GO 63/63 残留判例）。

扫描域注记：--tree-a/b 各自顶层平扫（与 gate1 --tree 同域）；CW219_split 不在默认域，
若 split 未随壳消融同票退役（runbook 刀 5），须显式 --tree-a/--tree-b 加扫或接线第三树；
split 退役后自然出域（R7 §二：零消费成立，唯一注意项=coq.yml 第三 --tree 待办作废删除）。

用法：
  python gate3_cross_tree_diff.py [--tree-a DIR] [--tree-b DIR] [--json OUT]
  默认 A=Main Live 树，B=vo 镜像树（两树 .v 均在盘）。
退出码：0=无单树毒分歧且无壳复活隶属命中；1=存在单树毒分歧或壳复活隶属命中（硬红）；
        2=树路径无效。
"""
import os, re, sys, json, argparse, datetime

POISON_TOKEN_RE = re.compile(
    r"\b(Lra|Psatz|Reals|ClassicalDedekindReals|FunctionalExtensionality|"
    r"Micromega|ClassicalDescription|Logic\.Classical)\b")
REQUIRE_LINE_RE = re.compile(r"\bRequire\b")

# [M1] R130 乙案扩条：壳模块隶属禁名单（模块集隶属检查，非 diff 型——对称复活亦咬合）
SHELL_MODULE = "CW_ConstructiveWorld_219"
SHELL_NAME_RE = re.compile(r"\bCW_ConstructiveWorld_219\b")

# 单条文件级显式豁免（用户禁碰件豁免）：_t24_probe3.v 内容与存在性受用户明令保护，
# 其壳 Require 行为全树唯余存留处，候用户终裁退役与否。仅豁免 [RESURRECT-REQUIRE]
# 行面命中且逐笔留账（exempted_hits）；模块面隶属检查（RESURRECT-MODULE）不豁免。
EXEMPT_FILES = {"_t24_probe3.v"}

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

def membership_check(tree_tag, tree, mods):
    """[M1] 模块集隶属检查：模块面＋Require 行面，两树各自独立（对称复活亦咬合）。"""
    hits = []
    exempted = []
    # 面 1：模块集隶属——树模块集 ∩ 禁名单（不豁免：壳文件本体存在即红）
    if SHELL_MODULE in mods:
        hits.append({"tree": tree_tag, "kind": "RESURRECT-MODULE",
                     "module": SHELL_MODULE, "file": mods[SHELL_MODULE],
                     "line": None, "text": "<壳文件/模块存在于树模块集>"})
    # 面 2：Require 行隶属——任一 .v 活 Require 行含壳名（豁免件逐笔留账不咬合；
    # 此处 m 为剥 .v 后缀的模块基名，豁免表存文件名故补后缀比对）
    for m in sorted(mods):
        if (m + ".v") in EXEMPT_FILES:
            try:
                for lineno, r in enumerate(require_face(mods[m]), 1):
                    if SHELL_NAME_RE.search(r):
                        exempted.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                                         "module": m, "file": mods[m], "line": lineno,
                                         "text": r, "exempted": True})
            except OSError:
                pass
            continue
        try:
            for lineno, r in enumerate(require_face(mods[m]), 1):
                if SHELL_NAME_RE.search(r):
                    hits.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                                 "module": m, "file": mods[m], "line": lineno,
                                 "text": r})
        except OSError:
            hits.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                         "module": m, "file": mods[m], "line": 0,
                         "text": "<IO-ERROR>"})
    return hits, exempted

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
    # [M1] 先隶属后 diff：隶属命中=壳复活实锤候选，exit 1 硬红
    rA, eA = membership_check("A", args.tree_a, A)
    rB, eB = membership_check("B", args.tree_b, B)
    resurrect = rA + rB
    exempted_hits = eA + eB
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
    print(f"[gate3] 时点={now}  形态=diff＋壳模块集隶属检查扩条（R18 E4/R2 §十.2）")
    print(f"  树A={args.tree_a}  .v={len(A)}")
    print(f"  树B={args.tree_b}  .v={len(B)}")
    print(f"  共同模块={len(common)}  仅A={len(only_a)}  仅B={len(only_b)}")
    print(f"  [豁免留账] 用户禁碰件豁免命中={len(exempted_hits)} 笔（_t24_probe3.v 壳 Require 行，候用户终裁退役与否）")
    for h in exempted_hits:
        print(f"    EXEMPTED 树{h['tree']} {h['module']}.v:{h['line']}  {h['text']}")
    if resurrect:
        print(f"  判定=FAIL（壳模块集隶属命中 {len(resurrect)} 笔——CW_ConstructiveWorld_219 复活实锤候选）")
        for h in resurrect:
            print(f"    {h['kind']} 树{h['tree']} {h['module']}.v:{h['line'] or '-'}  {h['file']}")
            print(f"      {h['text']}")
        print("  [响停纪律] 先跑 digest 三件套（md5+size+mtime 对删除/快照台账）定性"
              "「残留 vs 复活」再处置，禁未证先判（R13 B-GO 63/63 残留判例）。")
    else:
        print("  [M1] 壳模块集隶属检查=PASS（两树模块集与 Require 行面均无 CW_ConstructiveWorld_219）")
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
    elif not resurrect:
        print("  判定=PASS（共同模块毒面两树全对称＋壳零隶属）")
    if drift:
        print(f"  [登记] 无毒 Require 漂移 {len(drift)} 件（卫生信息）:")
        for d in drift[:20]:
            print(f"    REQUIRE-DRIFT {d['module']}.v")
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump({"time": now, "form": "diff+module-membership (R130 乙案扩条＋单条文件级豁免)",
                       "shell_module": SHELL_MODULE,
                       "exempt_files": sorted(EXEMPT_FILES),
                       "resurrection_hits": resurrect,
                       "exempted_hits": exempted_hits,
                       "poison_divergence": poison_div,
                       "require_drift": drift, "only_a": only_a, "only_b": only_b},
                      f, ensure_ascii=False, indent=1)
    return 1 if (resurrect or poison_div) else 0

if __name__ == "__main__":
    sys.exit(main())
