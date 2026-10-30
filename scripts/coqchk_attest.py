#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""coqchk_attest.py — ConstructiveWorld vo 树认证档案生成器（契约 cw.attest/v1）。

契约（固定）:
    {
      "modules":      {"<模块名>": {"vo_sha256": "<hex>", "size": <int>}, ...},
      "tree_sha256":  "<hex>",
      "generated_by": "coqchk green run",
      "schema":       "cw.attest/v1"
    }

定义:
  * 模块名 = order.txt 行去掉注释（自首个 '#' 起截断）再去空白后的原文（保留 '.v'
    后缀与 'Local/' 类相对路径，如 "S01_BaseRing.v"、"Local/LW0LeibSeparation.v"）。
    对应 vo 件 = 模块名去尾 '.v' 换 '.vo'，在真实 vo 树根下解析。
  * vo_sha256 / size = vo 文件原始字节的 sha256 / 字节数。mtime、任何 stat 元数据
    均不入哈希、不入档案。
  * tree_sha256 = sha256( canonical(modules) )，其中 canonical(modules) 为
    json.dumps(modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    的 UTF-8 字节。与档案文件自身的排版本无关，可跨运行复现。
  * generated_by / schema 为契约定值。本脚本只生成档案与对账，不代行 coqchk 本体。

纪律（只读律）:
  * 真实 vo 树与 order.txt 只读（仅 'rb' / 'r' 打开）。
  * 一切写入（档案、临时夹具、自验残料）只落沙箱目录 = 本脚本所在目录。
    --out 越出沙箱即拒绝。

三态自验 selfTest:
    ok    —— 档案重载后全量重算（重哈希 848 件 vo + 重导 tree_sha256）零差异;
    diff  —— 结构合法但内容不符（模块集不齐 / 哈希或字节数不符 / tree 哈希不符）,
              差异逐条列出;
    error —— 结构性失败（档案缺失/坏 JSON/契约字段错、模块行重复或无 .v 后缀、
              vo 缺失或不可读）。
    退出码: ok=0, diff=1, error=2。

用法:
    python coqchk_attest.py                  # 生成档案 + 自验（默认全流程）
    python coqchk_attest.py --verify         # 只对账既有档案（重跑对账自身）
    python coqchk_attest.py --unit-selftest  # 沙箱内夹具演示三态皆可达
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

SCHEMA = "cw.attest/v1"
GENERATED_BY = "coqchk green run"
DEFAULT_TREE = Path(r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo")
SANDBOX = Path(__file__).resolve().parent

STATE_OK = "ok"
STATE_DIFF = "diff"
STATE_ERROR = "error"
_EXIT = {STATE_OK: 0, STATE_DIFF: 1, STATE_ERROR: 2}


class AttestError(Exception):
    """结构性失败（三态之 error）。"""


# ---------------------------------------------------------------- order.txt --
def parse_order(order_path: Path) -> list[str]:
    """order.txt → 模块名列表（去注释去空格，保序，查重）。

    注释 = 自首个 '#' 至行尾；空行/纯注释行跳过；重复行按 error 处理。
    """
    keys: list[str] = []
    seen: dict[str, int] = {}
    try:
        text = order_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AttestError(f"order.txt 不可读: {order_path}: {exc}") from exc
    except UnicodeDecodeError as exc:
        raise AttestError(f"order.txt 非 UTF-8: {exc}") from exc
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if "#" in line:
            line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if line in seen:
            raise AttestError(
                f"order.txt 重复模块行: {line!r}（第 {seen[line]} 行与第 {lineno} 行）"
            )
        seen[line] = lineno
        keys.append(line)
    if not keys:
        raise AttestError("order.txt 解析为零个模块行")
    return keys


def resolve_vo_rel(key: str) -> str:
    """模块名 → 相对 vo 路径（'X.v' → 'X.vo'）。非 .v 结尾按 error。"""
    if not key.endswith(".v"):
        raise AttestError(f"模块行不以 .v 结尾，无法解析 vo: {key!r}")
    return key[:-2] + ".vo"


# -------------------------------------------------------------------- hashing --
def sha256_file(path: Path) -> tuple[str, int]:
    """文件字节流 sha256 与字节数。不读任何 stat 元数据（mtime 不入哈希）。"""
    h = hashlib.sha256()
    size = 0
    try:
        with open(path, "rb") as fh:
            while True:
                chunk = fh.read(1 << 20)
                if not chunk:
                    break
                h.update(chunk)
                size += len(chunk)
    except OSError as exc:
        raise AttestError(f"vo 不可读: {path}: {exc}") from exc
    return h.hexdigest(), size


def build_modules(tree: Path, keys: list[str]) -> dict[str, dict]:
    """对每个模块名解析 vo 并哈希。任何缺失/不可读 → AttestError（error 态）。"""
    modules: dict[str, dict] = {}
    failures: list[str] = []
    for key in keys:
        rel = resolve_vo_rel(key)  # 非 .v 行 → AttestError，整批判 error
        try:
            digest, size = sha256_file(tree / rel)
        except AttestError as exc:
            failures.append(str(exc))
            continue
        modules[key] = {"vo_sha256": digest, "size": size}
    if failures:
        head = "; ".join(failures[:8])
        tail = f" …共{len(failures)}件" if len(failures) > 8 else ""
        raise AttestError(f"vo 树不完整: {head}{tail}")
    return modules


def canonical_modules_bytes(modules: dict[str, dict]) -> bytes:
    return json.dumps(
        modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def tree_sha256_of(modules: dict[str, dict]) -> str:
    return hashlib.sha256(canonical_modules_bytes(modules)).hexdigest()


# ------------------------------------------------------------------ generate --
def _ensure_in_sandbox(path: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(SANDBOX)
    except ValueError as exc:
        raise AttestError(f"写入路径越出沙箱（只读律: 真实 vo 树只读）: {resolved}") from exc
    return resolved


def generate(tree: Path, order_path: Path, out_path: Path) -> dict:
    """建档并写沙箱。返回档案 dict。真实树零写入。"""
    keys = parse_order(order_path)
    modules = build_modules(tree, keys)
    archive = {
        "modules": modules,
        "tree_sha256": tree_sha256_of(modules),
        "generated_by": GENERATED_BY,
        "schema": SCHEMA,
    }
    out_path = _ensure_in_sandbox(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(archive, fh, ensure_ascii=False, indent=2)
        fh.write("\n")
    tmp.replace(out_path)
    return archive


# ------------------------------------------------------------------ selfTest --
def _load_archive(archive_path: Path) -> dict:
    """读档案并做契约结构校验；坏档 → AttestError（error 态）。"""
    try:
        raw = archive_path.read_bytes()
    except OSError as exc:
        raise AttestError(f"档案不可读: {archive_path}: {exc}") from exc
    try:
        archive = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AttestError(f"档案非合法 JSON/UTF-8: {exc}") from exc
    if not isinstance(archive, dict):
        raise AttestError("档案顶层非 JSON 对象")
    if archive.get("schema") != SCHEMA:
        raise AttestError(f"schema 不符契约: {archive.get('schema')!r} ≠ {SCHEMA!r}")
    if archive.get("generated_by") != GENERATED_BY:
        raise AttestError(
            f"generated_by 不符契约: {archive.get('generated_by')!r} ≠ {GENERATED_BY!r}"
        )
    modules = archive.get("modules")
    if not isinstance(modules, dict) or not modules:
        raise AttestError("modules 缺失或非非空对象")
    for key, entry in modules.items():
        if not isinstance(entry, dict):
            raise AttestError(f"模块条目非对象: {key!r}")
        if set(entry) != {"vo_sha256", "size"}:
            raise AttestError(f"模块条目字段不符契约 {key!r}: {sorted(entry)}")
        if not isinstance(entry["vo_sha256"], str) or len(entry["vo_sha256"]) != 64:
            raise AttestError(f"vo_sha256 非 64 位 hex 字符串: {key!r}")
        if not isinstance(entry["size"], int) or isinstance(entry["size"], bool) or entry["size"] < 0:
            raise AttestError(f"size 非非负整数: {key!r}")
    if not isinstance(archive.get("tree_sha256"), str) or len(archive["tree_sha256"]) != 64:
        raise AttestError("tree_sha256 非 64 位 hex 字符串")
    return archive


def selfTest(archive_path: Path, tree: Path, order_path: Path) -> tuple[str, dict]:
    """三态自验：重载档案 → 从真实树全量重算 → 对账。

    返回 (state, report)；state ∈ {ok, diff, error}。
    """
    report: dict = {
        "archive": str(archive_path),
        "tree": str(tree),
        "modules_in_archive": 0,
        "modules_recomputed": 0,
        "checked": 0,
        "diffs": [],
        "tree_sha256_archive": None,
        "tree_sha256_recomputed": None,
    }
    try:
        archive = _load_archive(archive_path)
        arch_modules = archive["modules"]
        keys = parse_order(order_path)
        rebuilt = build_modules(tree, keys)
    except AttestError as exc:
        report["state"] = STATE_ERROR
        report["reason"] = str(exc)
        return STATE_ERROR, report

    report["modules_in_archive"] = len(arch_modules)
    report["modules_recomputed"] = len(rebuilt)
    report["tree_sha256_archive"] = archive["tree_sha256"]
    report["tree_sha256_recomputed"] = tree_sha256_of(rebuilt)

    diffs: list[str] = []
    arch_keys = set(arch_modules)
    rebuilt_keys = set(rebuilt)
    for k in sorted(arch_keys - rebuilt_keys):
        diffs.append(f"档案多出模块: {k}")
    for k in sorted(rebuilt_keys - arch_keys):
        diffs.append(f"档案缺模块（order.txt 有）: {k}")
    for k in sorted(arch_keys & rebuilt_keys):
        report["checked"] += 1
        if arch_modules[k]["vo_sha256"] != rebuilt[k]["vo_sha256"]:
            diffs.append(
                f"哈希不符: {k}: 档案 {arch_modules[k]['vo_sha256']} "
                f"≠ 重算 {rebuilt[k]['vo_sha256']}"
            )
        if arch_modules[k]["size"] != rebuilt[k]["size"]:
            diffs.append(
                f"字节数不符: {k}: 档案 {arch_modules[k]['size']} "
                f"≠ 重算 {rebuilt[k]['size']}"
            )
    if archive["tree_sha256"] != report["tree_sha256_recomputed"]:
        diffs.append(
            f"tree_sha256 不符: 档案 {archive['tree_sha256']} "
            f"≠ 重算 {report['tree_sha256_recomputed']}"
        )
    report["diffs"] = diffs
    if diffs:
        report["state"] = STATE_DIFF
        return STATE_DIFF, report
    report["state"] = STATE_OK
    return STATE_OK, report


# ------------------------------------------------- unit selftest (夹具三态) --
def run_unit_selftest() -> int:
    """沙箱内合成夹具，验证三态 selfTest 各自可达且判定正确。只写沙箱。"""
    results: list[tuple[str, str, bool]] = []
    work = Path(tempfile.mkdtemp(prefix="attest_unit_", dir=SANDBOX))
    try:
        ftree = work / "fix_tree"
        (ftree / "Local").mkdir(parents=True)
        vo_blobs = {
            "A.vo": b"alpha vo bytes",
            "B.vo": b"beta vo bytes",
            "Local/C.vo": b"gamma vo bytes",
        }
        for rel, blob in vo_blobs.items():
            (ftree / rel).write_bytes(blob)
        (ftree / "order.txt").write_text(
            "A.v#R0-fix\nB.v#R0-fix\nLocal/C.v#R0-fix\n", encoding="utf-8"
        )
        farch = work / "fix_attest.json"

        # 态1 ok：新档自验应零差异
        generate(ftree, ftree / "order.txt", farch)
        st, rep = selfTest(farch, ftree, ftree / "order.txt")
        results.append((STATE_OK, st, st == STATE_OK and rep["checked"] == 3))

        # 态2 diff：篡改 A.v 哈希 + B.v 字节数 → 应报 2 条差异
        doc = json.loads(farch.read_text(encoding="utf-8"))
        doc["modules"]["A.v"]["vo_sha256"] = "0" * 64
        doc["modules"]["B.v"]["size"] += 1
        farch.write_text(json.dumps(doc), encoding="utf-8")
        st, rep = selfTest(farch, ftree, ftree / "order.txt")
        results.append(
            (STATE_DIFF, st, st == STATE_DIFF and len(rep["diffs"]) == 2)
        )

        # 态3 error：删掉 Local/C.vo（档案过期）→ 结构性失败
        (ftree / "Local" / "C.vo").unlink()
        st, rep = selfTest(farch, ftree, ftree / "order.txt")
        reason_norm = rep.get("reason", "").replace("\\", "/")
        results.append(
            (STATE_ERROR, st, st == STATE_ERROR and "Local/C.vo" in reason_norm)
        )
    finally:
        shutil.rmtree(work, ignore_errors=True)

    print("unit-selftest 三态可达性:")
    all_ok = True
    for want, got, verdict_ok in results:
        mark = "PASS" if verdict_ok else "FAIL"
        all_ok = all_ok and verdict_ok
        print(f"  期望 {want:5s} → 实得 {got:5s} [{mark}]")
    print("unit-selftest:", "PASS" if all_ok else "FAIL")
    return 0 if all_ok else 1


# ----------------------------------------------------------------------- main --
def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="cw.attest/v1 认证档案生成器（只读真实树）")
    ap.add_argument("--tree", type=Path, default=DEFAULT_TREE, help="真实 vo 树根（只读）")
    ap.add_argument("--order", type=Path, default=None, help="order.txt（默认 <tree>/order.txt）")
    ap.add_argument("--out", type=Path, default=SANDBOX / "cw_attest.json", help="档案输出路径（须在沙箱内）")
    ap.add_argument("--verify", action="store_true", help="只对账既有档案，不生成")
    ap.add_argument("--unit-selftest", action="store_true", help="沙箱夹具演示三态自验")
    args = ap.parse_args(argv)

    if args.unit_selftest:
        return run_unit_selftest()

    tree = args.tree.resolve()
    order_path = (args.order or tree / "order.txt").resolve()
    out_path = args.out.resolve()
    try:
        _ensure_in_sandbox(out_path)
    except AttestError as exc:
        print(f"[{STATE_ERROR}] {exc}")
        return _EXIT[STATE_ERROR]

    if not tree.is_dir():
        print(f"[{STATE_ERROR}] 真实 vo 树不存在: {tree}")
        return _EXIT[STATE_ERROR]

    if not args.verify:
        try:
            archive = generate(tree, order_path, out_path)
            print(
                f"generated: {out_path}\n"
                f"  modules={len(archive['modules'])} "
                f"tree_sha256={archive['tree_sha256']} schema={archive['schema']}"
            )
        except AttestError as exc:
            print(f"[{STATE_ERROR}] 生成失败: {exc}")
            return _EXIT[STATE_ERROR]

    state, rep = selfTest(out_path, tree, order_path)
    print(json.dumps(rep, ensure_ascii=False, indent=2))
    print(f"selftest: {state.upper()}（退出码 {_EXIT[state]}）")
    return _EXIT[state]


if __name__ == "__main__":
    sys.exit(main())
