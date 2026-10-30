#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""gate2_attest_gate.py — gate2 认证态分支裁定器（ATT-RECON 20261029）。

判定对象：部分日志（本轮仅送检子集）+ 档案覆盖断言 = 可判绿（ATTESTED_CLEAN）；
断言缺一即红（禁降档）。FULL 模式（跳过清单空）语义与旧版 gate2 逐字节等价：
parser 判定即终裁。

断言组（全备才可判 ATTESTED_CLEAN，任一破 → exit 1 红并列 reasons）：
  R1 状态一致   mode==ATTESTED ⇔ 日志附页在场；mode==FULL ⇔ 附页缺席
                （无对账背书的附页 = 证据链断，红；有跳过却无附页 = 同红）。
  R2 附页=清单  附页 ATTEST-SKIP 逐项集合 == 对账步 skipped 集合，计数行 == 集合大小。
  R3 档案指纹   附页 ATTEST-ARCHIVE == 对账步 archive_tree_sha256（绿判绑定档案身份）。
  R4 覆盖划分   skipped ∪ sent_to_chk == cert_surface 且交为空（对账报告内自洽，
                并与 parallel_chk 的并集断言/PCHK-SKIP-UNKNOWN 守卫双重把守）。
  R5 档案有效   对账步 archive_valid=true（契约结构+tree_sha256 自洽已过）。
  R6 解析判定   gate2_axioms_parser 判定 CLEAN（公理空+段非空+日志尾行完整——
                本裁定器按 parser JSON 重导同一判定，parser 1/2/3 不可救，一律红）。
  R7 代际钉     banner Chicken 9.1.0 由 yml 步前置 grep 把守（本裁定器不重查，登记在案）。

退出码：0 = 绿（CLEAN / ATTESTED_CLEAN，见 gate2_attest.json verdict）；
1 = 红（reasons 列明破断言）。
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

GATE_SCHEMA = "cw.gate2att/v1"

APPENDIX_BEGIN = "=== ATTEST-SKIP APPENDIX BEGIN"
APPENDIX_END = "=== ATTEST-SKIP APPENDIX END"


def parse_appendix(log_path: Path) -> dict:
    """从 _chk_all.log 抽认证附页。返回 {present, count, archive, modules}。"""
    out = {"present": False, "count": None, "archive": None, "modules": []}
    try:
        lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return out
    inside = False
    for line in lines:
        if APPENDIX_BEGIN in line:
            inside = True
            out["present"] = True
            out["modules"] = []
            continue
        if APPENDIX_END in line:
            inside = False
            continue
        if inside and line.startswith("ATTEST-SKIP-COUNT "):
            try:
                out["count"] = int(line.split(None, 1)[1])
            except (IndexError, ValueError):
                out["count"] = None
        elif inside and line.startswith("ATTEST-ARCHIVE "):
            out["archive"] = line.split(None, 1)[1].strip()
        elif inside and line.startswith("ATTEST-SKIP "):
            out["modules"].append(line.split(None, 1)[1].strip())
    return out


def parser_verdict(parser_json_path: Path) -> tuple[int, dict]:
    """按 gate2_axioms_parser 的 JSON 输出重导判定（与其 verdict() 同口径）。

    返回 (code, {complete, sections, axioms})；code ∈ {0,1,2,3}；
    JSON 缺失/坏 → (2, {unparseable: true})（= NO_AXIOMS 级，不可判即红）。
    """
    try:
        docs = json.loads(parser_json_path.read_text(encoding="utf-8"))
        if not isinstance(docs, list) or not docs:
            raise ValueError("parser json 非非空数组")
        d = docs[0]  # 单日志口径（yml 只喂 _chk_all.log）
        sections = d.get("sections")
        complete = bool(d.get("complete"))
        axioms = d.get("axioms")
        if not isinstance(sections, list) or not isinstance(axioms, list):
            raise ValueError("parser json 字段形不符")
    except (OSError, ValueError, json.JSONDecodeError):
        return 2, {"unparseable": True}
    code = 2
    if sections:
        code = 3
        if complete:
            code = 1
            if not axioms:
                code = 0
    return code, {
        "complete": complete if sections else None,
        "sections": len(sections) if isinstance(sections, list) else None,
        "axioms": len(axioms) if isinstance(axioms, list) else None,
    }


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="gate2 认证态分支裁定（部分日志+覆盖断言）")
    ap.add_argument("--log", type=Path, required=True)
    ap.add_argument("--parser-json", type=Path, required=True)
    ap.add_argument("--reconcile-json", type=Path, required=True)
    ap.add_argument("--json", dest="jsonout", type=Path, required=True)
    args = ap.parse_args()

    reasons: list[str] = []
    try:
        recon = json.loads(args.reconcile_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        recon = None
        reasons.append(f"对账报告不可读（证据链断）: {exc}")

    mode = (recon or {}).get("mode", "FULL")
    skipped = set((recon or {}).get("skipped") or [])
    surface = set((recon or {}).get("cert_surface") or [])
    sent = set((recon or {}).get("sent_to_chk") or [])
    arch_sha = (recon or {}).get("archive_tree_sha256")
    arch_valid = bool((recon or {}).get("archive_valid"))
    pcode, pinfo = parser_verdict(args.parser_json)
    appendix = parse_appendix(args.log)

    # R4 覆盖划分（对账报告自洽）
    partition_ok = (
        bool(surface)
        and skipped <= surface
        and sent == surface - skipped
        and not (skipped & sent)
    )
    if recon is not None and not partition_ok:
        reasons.append("R4 覆盖划分破: skipped∪sent != surface 或交集非空或面空")

    if mode == "FULL":
        # 旧版语义：parser 判定即终裁；附页在场 = 无对账背书的伪证，红。
        if appendix["present"]:
            reasons.append("R1 状态一致破: FULL 模式下日志含认证附页（无对账背书）")
        green = (pcode == 0) and not reasons
        verdict = "CLEAN" if green else "RED"
    else:
        # 认证态：R1-R6 全备才可判 ATTESTED_CLEAN。
        if not appendix["present"]:
            reasons.append("R1 状态一致破: ATTESTED 模式下日志无认证附页（证据链断）")
        appendix_set = set(appendix["modules"])
        if appendix_set != skipped:
            reasons.append(
                f"R2 附页=清单破: 附页 {len(appendix_set)} 项 vs 对账 skipped {len(skipped)} 项"
                f"（差集样本 {sorted(appendix_set ^ skipped)[:5]}）"
            )
        if appendix["count"] != len(appendix_set) or appendix["count"] is None:
            reasons.append("R2 计数行不符: ATTEST-SKIP-COUNT != 附页集合大小")
        if appendix["archive"] != arch_sha:
            reasons.append(f"R3 档案指纹不符: 附页 {appendix['archive']} vs 对账 {arch_sha}")
        if not arch_valid:
            reasons.append("R5 档案无效: 对账步 archive_valid=false（坏档/自洽破）")
        if pcode != 0:
            reasons.append(f"R6 解析判定非 CLEAN: parser code={pcode} {pinfo}")
        green = not reasons
        verdict = "ATTESTED_CLEAN" if green else "RED"

    doc = {
        "schema": GATE_SCHEMA,
        "mode": mode,
        "verdict": verdict,
        "green": green,
        "parser_code": pcode,
        "parser_info": pinfo,
        "appendix": {
            "present": appendix["present"],
            "count": appendix["count"],
            "archive": appendix["archive"],
            "modules_n": len(appendix["modules"]),
        },
        "reconcile": {
            "mode": mode,
            "archive_valid": arch_valid,
            "archive_tree_sha256": arch_sha,
            "surface_n": len(surface),
            "skipped_n": len(skipped),
            "sent_to_chk_n": len(sent),
            "partition_ok": partition_ok,
        },
        "reasons": reasons,
    }
    args.jsonout.write_text(
        json.dumps(doc, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"[gate2-attest] mode={mode} verdict={verdict} parser_code={pcode}")
    for r in reasons:
        print(f"  !! {r}")
    return 0 if green else 1


if __name__ == "__main__":
    sys.exit(main())
