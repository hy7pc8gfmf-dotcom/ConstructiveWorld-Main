#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸① 毒 token grep 守卫（AX-GUARD 20260925）＋ 壳名防复活 token·乙案态零白名单形（R130 EX-PROBE 预制席 20260926）
================================================================================
【本件=沙箱草案，未落树。差异全文见同目录 gate1_shell_token_ablation_zero_whitelist.patch；
 与 R7 甲案态（ratchet 台账形，_tr130feas_guard_ws 沙箱）的差异说明见
 _tr130exprobe_探针预制报告-20260926.md §三。】

乙案态（壳消融·案 I 落刀后）语义：
  壳 CW_ConstructiveWorld_219 消融落刀后存量壳 Require=0，故【零白名单形】成立——
  壳名 token 入 POISON_TOKENS 后任何命中（=任何新写/残留壳 Require 活行）直接 exit 1，
  无 ratchet 台账、无 --regen-baseline、无豁免面（R8 向量 5「豁免名单机制不需要」）。
  --strict 保留为 no-op 兼容旗标：接受该参数但零行为差异（零白名单形下唯一模式即
  strict；保留仅为与 R7 甲案态命令行/runbook 文案兼容，防接线改动即红）。
  适用时点：壳消融落刀＋split 同票退役之后；落刀前用本形会咬死 1007 行存量壳
  Require（R7 实测矛盾），落刀前窗口仍须用 R7 甲案态 ratchet 形。

R130 乙案扩接 diff（对 AX-GUARD v1.0，96272acb 基准）：
  [T1] POISON_TOKENS 净增 1 token：CW_ConstructiveWorld_219（壳聚合出口全名）。
       全名匹配＋\\b 词边界＋严格大小写：简称 CW_219 不命中；af_CW_ConstructiveWorld_219
       前缀名不命中（_ 为词字符无边界）；UpReqIndex 注释字面非 Require 行不命中
       （剥注释＋Require 行锚定双防，E422 口径）。R2 §十.1「全名 token 零白名单」同款。
  [T2'] --strict 保留 no-op（CLI 兼容旗标，见上）。
  [T3] 其余零变：剥注释（嵌套感知）、Require 行锚定、退出码 0/1/2、--tree/--live-x/--json/--text。

设计要点（全部来自实勘教训，出处见 _taxguard_ 报告）：
1. 全名匹配、严格大小写——简称陷阱禁入：token 表一律全名，禁项目简称（如 CW_219≠全名类）。
   且 \\b 词边界 + 大小写敏感：RealSetoid 不配 Reals（AX-MATRIX §1.3 grep -i 假配教训）。
2. 剥注释后匹配——(* Require ... *) 注释行不误报（E422 教训；白皮书词表口径：
   只有活 Require 行算命中）。剥注释为 (* *) 嵌套感知，保行号不变。
3. 只看含 Require 关键字的行（含 From Stdlib Require Import/Export 句式，无锚定——
   E-ARCH 教训：^Require Import 锚漏 From Stdlib 句式）。
4. fail-loud：命中 exit 1；无命中 exit 0；树不存在 exit 2。禁静默降级（零白名单形
   无台账缺席路径，fail-loud 面比甲案态更窄更硬）。

用法：
  python gate1_poison_guard.py [--tree DIR]... [--json OUT] [--text] [--strict]
  默认树：Main Live 树（ConstructiveWorld_Live）。可多次 --tree 扫多树。
  加 --live-x 可附扫 Live_X（850 件面，含探针脚手架，命中另账不混主树）。
  CI 接线同款（coq.yml gate1 pre-build fail-fast 步）：双树
  --tree ConstructiveWorld_Live --tree ConstructiveWorld_vo，bash -e 非零即 step 红。

R130 落树版增条（单条文件级显式豁免）：
  唯一豁免面=EXEMPT_FILES={"_t24_probe3.v"}——用户禁碰件豁免（该件内容与存在性均受
  用户明令保护，不可删改），其壳 Require 行为全树唯余存留处，候用户终裁退役与否。
  豁免命中仍逐笔留账（exempted_hits，文本与 JSON 双可见），非静默放行；除该单件外
  零白名单语义零变：任何其他文件任何壳名活 Require 命中即 exit 1。

退出码：0=洁净（守卫 PASS，含仅豁免件命中的形态）；1=命中毒 token（守卫咬合，
含壳名复活，豁免件以外）；2=树路径无效。
"""
import os, re, sys, json, argparse, datetime

POISON_TOKENS = [
    "Lra", "Psatz", "Reals", "ClassicalDedekindReals", "FunctionalExtensionality",
    "Micromega", "ClassicalDescription", "Logic.Classical",
    # R130 乙案态 [T1]：壳名防复活 token（全名；乙案零白名单形——命中即红，无台账豁免）
    "CW_ConstructiveWorld_219",
]
TOKEN_RE = re.compile(
    r"\b(" + "|".join(re.escape(t) for t in POISON_TOKENS) + r")\b"
)  # re.escape 保留 \. 为字面点；\b 在点两侧按词字符判定，Logic.Classical 正确配
REQUIRE_RE = re.compile(r"\bRequire\b")

# 单条文件级显式豁免（用户禁碰件豁免）：_t24_probe3.v 内容与存在性受用户明令保护，
# 其壳 Require 行为全树唯余存留处，候用户终裁退役与否。豁免命中逐笔留账，非静默放行。
EXEMPT_FILES = {"_t24_probe3.v"}

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
    exempted = []
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
                    rec = {"file": path, "line": lineno, "token": m.group(1),
                           "text": raw_line.strip(), "mtime": mtime}
                    if os.path.basename(path) in EXEMPT_FILES:
                        rec["exempted"] = True
                        exempted.append(rec)
                    else:
                        hits.append(rec)
    return nfiles, hits, exempted

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", action="append", default=None,
                    help="树根目录（可多次）")
    ap.add_argument("--live-x", action="store_true",
                    help="附扫 Live_X 树（默认关）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--text", action="store_true", help="只输出人类可读摘要")
    ap.add_argument("--strict", action="store_true",
                    help="[乙案态 T2'] 兼容 no-op：零白名单形下唯一模式即任何命中即红，"
                         "本旗标零行为差异，仅为 R7 甲案态命令行兼容保留")
    args = ap.parse_args()

    trees = args.tree or [r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live"]
    if args.live_x:
        trees.append(r"D:\ComplexAnalysis\新算法实践\Live_X")

    now = datetime.datetime.now().isoformat(timespec="seconds")
    report = {"scan_time": now, "tokens": POISON_TOKENS, "trees": {}, "total_hits": 0,
              "total_exempted_hits": 0,
              "exempt_files": sorted(EXEMPT_FILES),
              "form": "ablation-zero-whitelist + single-file exemption (R130 乙案态；"
                      "唯一豁免件 _t24_probe3.v=用户禁碰件，豁免命中逐笔留账)"}
    exit_code = 0
    for tree in trees:
        if not os.path.isdir(tree):
            print(f"[gate1] FATAL: 树不存在: {tree}", file=sys.stderr)
            return 2
        nfiles, hits, exempted = scan_tree(tree)
        report["trees"][tree] = {"v_files": nfiles, "hits": hits, "exempted_hits": exempted}
        report["total_hits"] += len(hits)
        report["total_exempted_hits"] += len(exempted)
        status = "FAIL(守卫咬合:命中毒token)" if hits else "PASS(洁净)"
        print(f"[gate1] 树={tree}  .v数={nfiles}  命中={len(hits)}  "
              f"豁免件命中={len(exempted)}  判定={status}  扫描时点={now}")
        for h in hits:
            print(f"  HIT {h['file']}:{h['line']}  token={h['token']}  mtime={h['mtime']}")
            print(f"      {h['text']}")
        for h in exempted:
            print(f"  EXEMPTED(用户禁碰件豁免留账) {h['file']}:{h['line']}  token={h['token']}")
            print(f"      {h['text']}")
    if report["total_hits"]:
        exit_code = 1
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1)
    return exit_code

if __name__ == "__main__":
    sys.exit(main())
