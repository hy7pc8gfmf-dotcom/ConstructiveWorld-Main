#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""coqchk_delta_check.py — ConstructiveWorld vo 树 vs 认证档案 四类增量对账。

对账对象（契约 cw.attest/v1，与 coqchk_attest.py 同源）:
    * 模块名 = 档案 modules 键（保 '.v' 后缀与 'Local/' 类相对路径）。
    * 对应 vo 件 = 模块名去尾 '.v' 换 '.vo'，在 vo 树根下解析。
    * 逐件哈希对 = 档案 {vo_sha256, size} vs 现树文件字节流 sha256 / 字节数
      （mtime 等任何 stat 元数据不入对账）。

四类判定（互斥穷尽，对档案键 ∪ 现树寻址 vo 件的全并集逐件判定）:
    unchanged —— 档案有、树有、sha256 与 size 均符;
    changed   —— 档案有、树有、sha256 或 size 任一不符（含篡改检出）;
    removed   —— 档案有、树无（vo 件缺失）;
    added     —— 档案无、树有（未认证 vo 件混入）。

扫描域（added 的发现范围）:
    vo 树根（非递归）+ 档案键涉及的每个子目录（如 Local/，非递归）。
    档案键不寻址的目录（如 _pchk_tmp_* 构建残料）不在对账域内——它们不是
    本档案的认证对象；此范围界定如实载明于报告 scan_domains。

退出码: 0 = 全 unchanged（零增量）; 1 = 有 changed/added/removed; 2 = 结构性失败
    （档案缺失/坏 JSON/契约不符/档案 tree_sha256 自洽性破/vo 树不存在）。

纪律（只读律）:
    * 真实 vo 树与认证档案只读（仅 'rb' / 'r' 打开）。
    * 一切写入（fixture 树、篡改、自验残料）只落沙箱 = 本脚本所在目录;
      --json 越出沙箱即拒绝。

三态闭环 selftest（fixture 在沙箱内，真实 vo 树零改动）:
    ①  从真实树复制若干已认证 .vo 入 fixture 树，以真实档案的对应切片
       （原始哈希原封保留）为对账档案 → 判定须全 unchanged;
    ②  fixture 内 1 件翻转 1 字节 → 对账必须把它标入 changed（篡改检出），
       其余仍 unchanged，removed/added 为零；
    ③  fixture 内删 1 件 → 对账必须把它标入 removed，changed 归零。
    另有附加态④（三态之外自加的验收）：fixture 内放入 1 件档案外 vo →
    判 added。每态验毕即还原，态间互不污染。三态①②③全过才算交付。
    fixture 用毕即删。

用法:
    python coqchk_delta_check.py                       # 真实树 vs 沙箱档案，四类对账
    python coqchk_delta_check.py --tree T --attest A   # 指定 vo 树根与档案
    python coqchk_delta_check.py --json OUT            # 另落逐件 JSON 报告（须在沙箱）
    python coqchk_delta_check.py --selftest            # 沙箱 fixture 三态闭环（含附加态④）
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
import time
from pathlib import Path, PurePosixPath

SCHEMA = "cw.attest/v1"
GENERATED_BY = "coqchk green run"
DELTA_SCHEMA = "cw.delta/v1"
DEFAULT_TREE = Path(r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo")
SANDBOX = Path(__file__).resolve().parent
DEFAULT_ATTEST = SANDBOX / "cw_attest.json"

# selftest 选取的已认证模块（跨类取样，含 1 件 Local/ 子目录件以演练子目录解析）
SELFTEST_PICKS = [
    "AttnSqrt.v",
    "G02_Debt.v",
    "UpCS.v",
    "S15_TailFEPUp.v",
    "Local/LW0LeibSeparation.v",
]
TAMPER_TARGET = "AttnSqrt.v"   # 态②翻转 1 字节的件
REMOVE_TARGET = "G02_Debt.v"   # 态③删除的件
ADDED_TARGET = "ZZ_UnattestedExtra.v"  # 附加态④的档案外混入件

EXIT_CLEAN = 0
EXIT_DELTA = 1
EXIT_ERROR = 2

VERDICTS = ("unchanged", "changed", "added", "removed")


class DeltaError(Exception):
    """结构性失败（退出码 2）。"""


# ------------------------------------------------------------------ 基础件 --
def sha256_file(path: Path) -> tuple[str, int]:
    """文件字节流 sha256 与字节数。不读任何 stat 元数据。"""
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
        raise DeltaError(f"vo 不可读: {path}: {exc}") from exc
    return h.hexdigest(), size


def vo_rel(key: str) -> str:
    """模块名 → 相对 vo 路径（'X.v' → 'X.vo'）。非 .v 结尾按 error。"""
    if not key.endswith(".v"):
        raise DeltaError(f"模块键不以 .v 结尾，无法解析 vo: {key!r}")
    return key[:-2] + ".vo"


def canonical_modules_bytes(modules: dict) -> bytes:
    return json.dumps(
        modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def tree_sha256_of(modules: dict) -> str:
    return hashlib.sha256(canonical_modules_bytes(modules)).hexdigest()


# ------------------------------------------------------------------ 档案载入 --
def load_attest(archive_path: Path) -> dict:
    """读认证档案并做契约结构校验 + tree_sha256 自洽性校验；坏档 → DeltaError。"""
    try:
        raw = archive_path.read_bytes()
    except OSError as exc:
        raise DeltaError(f"档案不可读: {archive_path}: {exc}") from exc
    try:
        archive = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DeltaError(f"档案非合法 JSON/UTF-8: {exc}") from exc
    if not isinstance(archive, dict):
        raise DeltaError("档案顶层非 JSON 对象")
    if archive.get("schema") != SCHEMA:
        raise DeltaError(f"schema 不符契约: {archive.get('schema')!r} ≠ {SCHEMA!r}")
    if archive.get("generated_by") != GENERATED_BY:
        raise DeltaError(
            f"generated_by 不符契约: {archive.get('generated_by')!r} ≠ {GENERATED_BY!r}"
        )
    modules = archive.get("modules")
    if not isinstance(modules, dict) or not modules:
        raise DeltaError("modules 缺失或非非空对象")
    for key, entry in modules.items():
        if not isinstance(entry, dict):
            raise DeltaError(f"模块条目非对象: {key!r}")
        if set(entry) != {"vo_sha256", "size"}:
            raise DeltaError(f"模块条目字段不符契约 {key!r}: {sorted(entry)}")
        if not isinstance(entry["vo_sha256"], str) or len(entry["vo_sha256"]) != 64:
            raise DeltaError(f"vo_sha256 非 64 位 hex 字符串: {key!r}")
        if (
            not isinstance(entry["size"], int)
            or isinstance(entry["size"], bool)
            or entry["size"] < 0
        ):
            raise DeltaError(f"size 非非负整数: {key!r}")
    if not isinstance(archive.get("tree_sha256"), str) or len(archive["tree_sha256"]) != 64:
        raise DeltaError("tree_sha256 非 64 位 hex 字符串")
    recomputed = tree_sha256_of(modules)
    if recomputed != archive["tree_sha256"]:
        raise DeltaError(
            f"档案 tree_sha256 自洽性破: 档案 {archive['tree_sha256']} "
            f"≠ 按 modules 重算 {recomputed}"
        )
    return archive


# -------------------------------------------------------------------- 对账 --
def scan_domains_of(modules: dict) -> list[str]:
    """档案键寻址的子目录集（含根 '.'）。added 的发现范围即根 + 这些目录。"""
    dirs = {"."}
    for key in modules:
        parent = PurePosixPath(vo_rel(key)).parent
        if str(parent) not in (".", ""):
            dirs.add(str(parent))
    return sorted(dirs)


def discover_tree_vos(tree: Path, modules: dict) -> dict[str, Path]:
    """在扫描域（根 + 档案键子目录，各非递归）发现 vo 件 → {模块名: 路径}。"""
    found: dict[str, Path] = {}
    for domain in scan_domains_of(modules):
        base = tree if domain == "." else tree.joinpath(*PurePosixPath(domain).parts)
        if not base.is_dir():
            continue
        for p in sorted(base.glob("*.vo")):
            rel = p.name if domain == "." else f"{domain}/{p.name}"
            found[rel[:-3] + ".v"] = p
    return found


def reconcile(tree: Path, archive: dict) -> dict:
    """四类增量对账。逐件哈希对入 entries。只读树与档案。"""
    modules = archive["modules"]
    tree_vos = discover_tree_vos(tree, modules)
    entries: list[dict] = []
    counts = {v: 0 for v in VERDICTS}
    for key in sorted(set(modules) | set(tree_vos)):
        ent = modules.get(key)
        if ent is None:
            digest, size = sha256_file(tree_vos[key])
            counts["added"] += 1
            entries.append(
                {
                    "module": key,
                    "verdict": "added",
                    "attest_sha256": None,
                    "attest_size": None,
                    "tree_sha256": digest,
                    "tree_size": size,
                    "match": False,
                }
            )
            continue
        path = tree.joinpath(*PurePosixPath(vo_rel(key)).parts)
        if key not in tree_vos or not path.is_file():
            counts["removed"] += 1
            entries.append(
                {
                    "module": key,
                    "verdict": "removed",
                    "attest_sha256": ent["vo_sha256"],
                    "attest_size": ent["size"],
                    "tree_sha256": None,
                    "tree_size": None,
                    "match": False,
                }
            )
            continue
        digest, size = sha256_file(path)
        ok = digest == ent["vo_sha256"] and size == ent["size"]
        verdict = "unchanged" if ok else "changed"
        counts[verdict] += 1
        entries.append(
            {
                "module": key,
                "verdict": verdict,
                "attest_sha256": ent["vo_sha256"],
                "attest_size": ent["size"],
                "tree_sha256": digest,
                "tree_size": size,
                "match": ok,
            }
        )
    return {
        "tree": str(tree),
        "attest": None,  # 由调用方补填
        "scan_domains": scan_domains_of(modules),
        "counts": counts,
        "entries": entries,
    }


def short(hexstr: str | None) -> str:
    return "—" if hexstr is None else f"{hexstr[:8]}…{hexstr[-8:]}"


def print_report(rep: dict) -> None:
    c = rep["counts"]
    print(f"对账域（scan_domains）: {', '.join(rep['scan_domains'])}")
    print(
        f"四类判定: unchanged={c['unchanged']}  changed={c['changed']}  "
        f"added={c['added']}  removed={c['removed']}"
    )
    print("逐件哈希对（档案 vs 现树）:")
    for e in rep["entries"]:
        print(
            f"  {e['verdict']:9s} {e['module']:42s} "
            f"档案 {short(e['attest_sha256'])} ({e['attest_size']} B)  "
            f"树 {short(e['tree_sha256'])} ({e['tree_size']} B)  "
            f"{'==' if e['match'] else '!!'}"
        )
    clean = c["changed"] == c["added"] == c["removed"] == 0
    print(f"判定: {'CLEAN（全 unchanged，零增量）' if clean else 'DELTA（存在增量，见上）'}")


def _ensure_in_sandbox(path: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(SANDBOX)
    except ValueError as exc:
        raise DeltaError(f"写入路径越出沙箱（只读律: 真实 vo 树只读）: {resolved}") from exc
    return resolved


# ----------------------------------------------------------------- selftest --
def _copy_real_vo(tree: Path, key: str, dest: Path) -> None:
    """从真实树只读复制 1 件 vo 入 fixture。源仅 'rb'。"""
    src = tree.joinpath(*PurePosixPath(vo_rel(key)).parts)
    try:
        blob = src.read_bytes()
    except OSError as exc:
        raise DeltaError(f"真实 vo 不可读: {src}: {exc}") from exc
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(blob)


def _subset_archive(archive: dict, keys: list[str]) -> dict:
    """真实档案的键切片：原始 vo_sha256/size 原封保留（篡改检出锚定认证哈希），
    tree_sha256 按同款 canonical 重算，使切片本身是合法 cw.attest/v1 档案。"""
    sub_modules = {k: dict(archive["modules"][k]) for k in keys}
    return {
        "modules": sub_modules,
        "tree_sha256": tree_sha256_of(sub_modules),
        "generated_by": GENERATED_BY,
        "schema": SCHEMA,
    }


def _counts_of(rep: dict) -> dict:
    return dict(rep["counts"])


def run_selftest() -> int:
    """沙箱 fixture 三态闭环（①全unchanged ②1 changed ③1 removed + 附加态④added）。"""
    results: list[tuple[str, bool, str]] = []
    work = Path(tempfile.mkdtemp(prefix="delta_fixture_", dir=SANDBOX))
    try:
        archive = load_attest(DEFAULT_ATTEST)
        real_tree = DEFAULT_TREE.resolve()
        ftree = work / "fix_tree"
        ftree.mkdir()

        # 复制真实 .vo 数件（含 Local/ 子目录件）→ fixture 树
        for key in SELFTEST_PICKS:
            _copy_real_vo(real_tree, key, ftree.joinpath(*PurePosixPath(vo_rel(key)).parts))
        # fixture 对账档案 = 真实档案对应切片（原始哈希锚）
        sub = _subset_archive(archive, SELFTEST_PICKS)

        def once() -> dict:
            return reconcile(ftree, sub)

        def ok_counts(rep: dict, want: dict) -> bool:
            return rep["counts"] == want

        # 态① 全 unchanged
        rep1 = once()
        want1 = {"unchanged": len(SELFTEST_PICKS), "changed": 0, "added": 0, "removed": 0}
        results.append(
            (
                "① 复制真实 .vo 数件 → 全 unchanged",
                ok_counts(rep1, want1),
                f"counts={_counts_of(rep1)}（期望 {want1}）",
            )
        )

        # 态② fixture 内 1 件翻 1 字节 → 必标 changed（篡改检出）
        tamper_path = ftree.joinpath(*PurePosixPath(vo_rel(TAMPER_TARGET)).parts)
        blob = tamper_path.read_bytes()
        tamper_path.write_bytes(blob[:0] + bytes([blob[0] ^ 0xFF]) + blob[1:])
        rep2 = once()
        changed2 = {e["module"] for e in rep2["entries"] if e["verdict"] == "changed"}
        cond2 = (
            rep2["counts"]["changed"] == 1
            and changed2 == {TAMPER_TARGET}
            and rep2["counts"]["unchanged"] == len(SELFTEST_PICKS) - 1
            and rep2["counts"]["removed"] == 0
            and rep2["counts"]["added"] == 0
        )
        tam_e = next(e for e in rep2["entries"] if e["module"] == TAMPER_TARGET)
        detail2 = (
            f"changed={sorted(changed2)} 篡改件哈希对 档案{short(tam_e['attest_sha256'])}"
            f" vs 树{short(tam_e['tree_sha256'])} counts={_counts_of(rep2)}"
        )
        results.append(("② 改 1 件 1 字节 → 标入 changed", cond2, detail2))
        # 还原（重抄真实件，态间互不污染）
        _copy_real_vo(real_tree, TAMPER_TARGET, tamper_path)

        # 态③ fixture 内删 1 件 → 标 removed
        remove_path = ftree.joinpath(*PurePosixPath(vo_rel(REMOVE_TARGET)).parts)
        remove_path.unlink()
        rep3 = once()
        removed3 = {e["module"] for e in rep3["entries"] if e["verdict"] == "removed"}
        cond3 = (
            rep3["counts"]["removed"] == 1
            and removed3 == {REMOVE_TARGET}
            and rep3["counts"]["unchanged"] == len(SELFTEST_PICKS) - 1
            and rep3["counts"]["changed"] == 0
            and rep3["counts"]["added"] == 0
        )
        results.append(
            (
                "③ 删 1 件 → 标入 removed",
                cond3,
                f"removed={sorted(removed3)} counts={_counts_of(rep3)}",
            )
        )
        # 还原
        _copy_real_vo(real_tree, REMOVE_TARGET, remove_path)

        # 附加态④（三态之外自加）: 混入 1 件档案外 vo → 标 added
        (ftree / vo_rel(ADDED_TARGET)).write_bytes(b"fixture unattested extra bytes")
        rep4 = once()
        added4 = {e["module"] for e in rep4["entries"] if e["verdict"] == "added"}
        cond4 = (
            rep4["counts"]["added"] == 1
            and added4 == {ADDED_TARGET}
            and rep4["counts"]["unchanged"] == len(SELFTEST_PICKS)
            and rep4["counts"]["changed"] == 0
            and rep4["counts"]["removed"] == 0
        )
        results.append(
            (
                "④（附加）混入档案外 vo → 标入 added",
                cond4,
                f"added={sorted(added4)} counts={_counts_of(rep4)}",
            )
        )
    except DeltaError as exc:
        print(f"[error] selftest 结构性失败: {exc}")
        shutil.rmtree(work, ignore_errors=True)
        return EXIT_ERROR
    finally:
        shutil.rmtree(work, ignore_errors=True)

    print("三态闭环（沙箱 fixture，真实树零改动，fixture 用毕已删）:")
    all_ok = True
    for name, ok, detail in results:
        all_ok = all_ok and ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        print(f"         {detail}")
    verdict = "PASS（①②③全过，附加④亦过）" if all_ok else "FAIL"
    print("selftest:", verdict)
    return EXIT_CLEAN if all_ok else EXIT_DELTA


# ----------------------------------------------------------------------- main --
def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="cw.attest/v1 vo 树四类增量对账（只读真实树）")
    ap.add_argument("--tree", type=Path, default=DEFAULT_TREE, help="vo 树根（只读）")
    ap.add_argument("--attest", type=Path, default=DEFAULT_ATTEST, help="认证档案（只读）")
    ap.add_argument("--json", type=Path, default=None, help="逐件 JSON 报告输出路径（须在沙箱内）")
    ap.add_argument("--selftest", action="store_true", help="沙箱 fixture 三态闭环自验")
    args = ap.parse_args(argv)

    t0 = time.time()
    if args.selftest:
        rc = run_selftest()
        print(f"耗时 {time.time() - t0:.1f}s，退出码 {rc}")
        return rc

    tree = args.tree.resolve()
    try:
        archive = load_attest(args.attest.resolve())
        if not tree.is_dir():
            raise DeltaError(f"vo 树不存在: {tree}")
        rep = reconcile(tree, archive)
        if args.json is not None:
            out = _ensure_in_sandbox(args.json)
            report = dict(rep)
            report["attest"] = str(args.attest.resolve())
            report["schema"] = DELTA_SCHEMA
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
            )
            print(f"JSON 报告已落: {out}")
    except DeltaError as exc:
        print(f"[error] {exc}")
        return EXIT_ERROR

    print(f"对账: 树 {tree}  vs  档案 {args.attest.resolve()}")
    rep["attest"] = str(args.attest.resolve())
    print_report(rep)
    c = rep["counts"]
    rc = EXIT_CLEAN if (c["changed"] == c["added"] == c["removed"] == 0) else EXIT_DELTA
    print(f"耗时 {time.time() - t0:.1f}s，退出码 {rc}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
