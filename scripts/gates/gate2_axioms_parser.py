#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸② CI「Axioms 段=0」哨兵：coqchk 日志块状态机解析器（AX-GUARD 20260925）
==========================================================================
对 coqchk（-o）日志做**块状态机**解析，输出实际公理名单；禁朴素 grep。

为什么非朴素 grep（本机实证）：
- 本机 _chk_all.log 有 88 处 `checking cst:` 行名字含 error 字样
  （Corelib.Init.Specif.error / Stdlib.Lists.List.hd_error / nth_error /
  PadeErrorIntegral 族…）——裸词 grep（-i error / -i axiom）全数假匹配。
- E422 教训：2212 条「axiom」裸词命中全为 stdlib NZAxioms/ZAxioms 模块类型名。
- 本解析器的作用域纪律：**只有处于 `Axioms:` 段内部的行才可能被判为公理**，
  段外一切行（checking cst / intern / 模块名）永不入榜——假匹配在结构上不可能。

状态机：
  S0 扫行 → 见 `[*] Axioms:` 头 →
      头行内联 `<none>` → 记空段（CLEAN 证据）→ 回 S0
      头行内联名字   → 记单条
      头行空         → S1 收段
  S1 收段 → 行为缩进条目（≥2 空格起头非空）→ 记公理；
            行为空行 / 下一节头（`*` 开头）/ 非缩进行 → 回 S0

判读（E943 纪律三口径）：
  exit 0 = CLEAN（Axioms 段全空且日志完整「Modules were successfully checked」）
  exit 1 = DIRTY（Axioms 段非空；三靶公理单独列明）
  exit 2 = NO_AXIOMS_SECTION（日志无 Axioms 段——通常系 coqchk 未带 -o，不可判，fail-loud）
  exit 3 = LOG_INCOMPLETE（无「Modules were successfully checked」尾行——日志被截断或在写）

靶公理（AX-RECIPE/AX-MATRIX 定谳三件套，全名锚定）：
  Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
  Stdlib.Reals.ClassicalDedekindReals.sig_not_dec
  Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec

用法：
  python gate2_axioms_parser.py LOG [LOG...] [--json OUT]
  python gate2_axioms_parser.py --naive-demo LOG   # 演示朴素 grep 假匹配 vs 本解析器对照
"""
import os, re, sys, json, argparse, datetime

TARGET_AXIOMS = [
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec",
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
]
# 朴素 grep 假匹配白名单类（标识符名字含 error 字样的合法常量/模块族）——
# 仅用于 --naive-demo 对照说明；本解析器状态机 scope 纪律下这些行永不入榜。
NAIVE_FALSE_CLASSES = [
    r"checking cst:\S*error", r"checking cst:\S*Error",
]
AXIOM_HEADER_RE = re.compile(r"^\*?\s*Axioms:\s*(.*)$")
ENTRY_RE = re.compile(r"^\s{2,}(\S.*?)\s*$")
SECTION_NEXT_RE = re.compile(r"^\*\s?|\s=+$")
COMPLETE_MARK = "Modules were successfully checked"

def parse_log(path):
    """块状态机解析。返回 dict：sections / axioms / complete / stats。"""
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    sections = []          # [{line_no, entries:[...], inline:none|str}]
    axioms = []            # 全部公理（含段归属行号）
    in_axioms = False
    cur = None
    complete = False
    naive_error_lines = 0
    for lineno, line in enumerate(lines, 1):
        if COMPLETE_MARK in line:
            complete = True
        if re.search(r"checking cst:\S*(error|Error)", line):
            naive_error_lines += 1
        if in_axioms:
            if line.strip() == "" or SECTION_NEXT_RE.match(line):
                in_axioms = False
                cur = None
                continue
            m = ENTRY_RE.match(line)
            if m:
                entry = m.group(1).strip()
                axioms.append(entry)
                cur["entries"].append(entry)
                continue
            in_axioms = False
            cur = None
            continue
        m = AXIOM_HEADER_RE.match(line)
        if m:
            rest = m.group(1).strip()
            cur = {"line_no": lineno, "entries": [], "inline": None}
            sections.append(cur)
            if rest == "<none>":
                cur["inline"] = "<none>"
            elif rest:
                cur["inline"] = rest
                axioms.append(rest)
            else:
                in_axioms = True
    return {
        "log": path,
        "log_mtime": datetime.datetime.fromtimestamp(os.path.getmtime(path)).isoformat(timespec="seconds"),
        "complete": complete,
        "sections": sections,
        "axioms": axioms,
        "naive_error_lines": naive_error_lines,
    }

def verdict(res):
    targets = sorted(set(res["axioms"]) & set(TARGET_AXIOMS))
    others = sorted(set(res["axioms"]) - set(TARGET_AXIOMS))
    if not res["sections"]:
        return 2, "NO_AXIOMS_SECTION", targets, others
    if not res["complete"]:
        return 3, "LOG_INCOMPLETE", targets, others
    if res["axioms"]:
        return 1, "DIRTY", targets, others
    return 0, "CLEAN", targets, others

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("logs", nargs="*")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--naive-demo", action="store_true",
                    help="附印朴素 grep 假匹配对照（教育用）")
    args = ap.parse_args()
    if not args.logs:
        ap.error("至少一个日志路径")

    final = 0
    out = []
    for path in args.logs:
        if not os.path.isfile(path):
            print(f"[gate2] FATAL: 日志不存在: {path}", file=sys.stderr)
            return 2
        res = parse_log(path)
        code, v, targets, others = verdict(res)
        final = max(final, code)
        print(f"[gate2] 日志={res['log']}  mtime={res['log_mtime']}")
        print(f"  判定={v}(exit {code})  Axioms段数={len(res['sections'])}  公理总数={len(res['axioms'])}"
              f"  日志完整={res['complete']}")
        if targets:
            print(f"  靶公理命中 {len(targets)}/3:")
            for t in targets:
                print(f"    TARGET {t}")
        for o in others:
            print(f"    OTHER  {o}")
        if v == "NO_AXIOMS_SECTION":
            print("  !! 日志无 Axioms 段——通常系 coqchk 未带 -o（无 CONTEXT SUMMARY）。"
                  "本日志不可作公理判读依据（fail-loud，不静默当 CLEAN）。")
        if v == "LOG_INCOMPLETE":
            print("  !! 日志缺「Modules were successfully checked」尾行——被截断或在写。不可判。")
        if args.naive_demo:
            n_err = res["naive_error_lines"]
            n_axiom_word = 0
            with open(path, encoding="utf-8", errors="replace") as f:
                for ln in f:
                    if re.search(r"[Aa]xiom", ln):
                        n_axiom_word += 1
            print(f"  [naive对照] 裸 grep -i error 假匹配行={n_err}（白名单假匹配类："
                  f"Corelib.Init.Specif.error/hd_error/nth_error/PadeErrorIntegral 族）；"
                  f"裸 grep -i axiom 命中={n_axiom_word}（NZAxioms/ZAxioms 模块名假匹配族，E422 教训）；"
                  f"本解析器实际公理={len(res['axioms'])}。")
        out.append(res)
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(out, f, ensure_ascii=False, indent=1)
    return final

if __name__ == "__main__":
    sys.exit(main())
