#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸⑤ .vo/.vos/.vok 二进制依赖层检疫（GATE-VOQ 20260926）
========================================================
源面闸①（gate1）扫不到的半径：休眠毒代二进制。判例 E-STAGING-AXFORENSIC-1
（cw-ci-sop §6·B 第四型）：R109/R111 期落件编译的带毒 .vo 休眠于沙箱世界，
跨批播种按文件名不按 digest 复活三经典公理——gate1 源面绿与 coqchk Axioms
现形两口径不相交，载体躲在 .vo 依赖串表层。本闸在聚合 coqchk 消费闭包前
对全 .vo/.vos/.vok 二进制做黑名单 token 串表扫描＋毒 digest 黑名单对照。

设计要点（全部来自实勘判例，出处见 _tgatevoq_ 检疫半径扩展报告）：
1. 解压感知扫描（VO-SCAN/AXFORENSIC 双判例）：.vo 的依赖串表在 gzip 流内，
   裸二进制 grep 得零命中假象——须对 raw 字节＋全部 gzip 流（\\x1f\\x8b）＋
   zlib 流（\\x78\\x9c）解压后逐 blob 扫描。
2. platform 对照组内建（防 glob 假象，fail-loud）：扫描器对平台自带
   ClassicalDedekindReals.vo 必须自命中（SELF-HIT）；对照文件缺失或自命中
   失败＝方法不可证，一律 exit 2 非绿（零命中在无对照自检时不可信）。
3. token 五族全扫全报，硬/软分层（主树 2477 件实勘校准 20260926）：
   - 硬四族（命中即 exit 1）：Lra / Reals / ClassicalDedekindReals /
     FunctionalExtensionality——已认证净主树（Axioms=<none>）实测 0/0/0/0，
     而五毒代（43f866e8 等）全携 Lra；\\b 词边界＋大小写敏感（gate1 同款），
     ConstructiveReals/Qreals 等项目净件名不误配。
   - 软一族（记录不红，--strict-psatz 升硬）：Psatz——净主树 172 件串表携带
     （Lia 依赖闭包的 micromega Q 域供给，AXFORENSIC §1.1 判例「非毒」）；
     源面 Require Psatz 拉公理链由 gate1 硬闸把守，二进制层串不构成载体证据。
4. 毒 digest 黑名单（md5）：同名 vo 即净假设不成立（主树 a4b1c953 净 vs
   P2 世界 43f866e8 毒判例），一切按 digest 对账；命中列出黑名单册名，
   盘上文件名与册名不符时 name_mismatch=true 亮出（改名投毒检测）。
5. fail-loud：命中 exit 1；无可扫面／树无效／对照失效／黑名单空／扫描出错
   （面不完整）一律 exit 2；exit 0 必须是「扫全＋对照过＋零命中」三件齐。

用法：
  python gate5_vodep_quarantine.py [--tree DIR]... [--blacklist FILE]
      [--control PATH|off] [--strict-psatz] [--json OUT] [--text]
  默认树：主 vo 树 ConstructiveWorld_vo（可多次 --tree 扫多树/世界，递归）。

退出码：0=洁净（扫全＋对照过＋零命中）；1=命中（硬 token 或黑名单 digest，
检疫咬合）；2=无可扫面/树无效/对照组失效/黑名单空/扫描出错（不可判绿，红）。
"""
import os, re, sys, io, zlib, gzip, json, hashlib, argparse, datetime

HARD_TOKENS = ["Lra", "Reals", "ClassicalDedekindReals", "FunctionalExtensionality"]
SOFT_TOKENS = ["Psatz"]  # 信息档；--strict-psatz 升硬（§3 校准注）
ALL_TOKENS = HARD_TOKENS + SOFT_TOKENS
TOKEN_RES = {
    t: re.compile(rb"(?<![A-Za-z0-9_])" + t.encode() + rb"(?![A-Za-z0-9_])")
    for t in ALL_TOKENS
}
SCAN_SUFFIXES = (".vo", ".vos", ".vok")
MAX_FILE_BYTES = 512 * 1024 * 1024  # 单件 IO 安全帽，超出计 ERR（fail-loud）

CONTROL_NAME = "ClassicalDedekindReals.vo"
CONTROL_TOKEN = "ClassicalDedekindReals"
CONTROL_BASES = [
    "C:/Rocq-Platform~9.1~2026.01/lib/coq",  # 钉代优先（SW2：继承 env 可能是 9.0 旧值）
    os.environ.get("COQLIB"),
    os.environ.get("ROCQLIB"),
]


def blobs_of(path):
    """raw ＋全部 gzip 流＋zlib 流解压 blob（VO-SCAN 原型同源，判例已验）。"""
    with open(path, "rb") as f:
        data = f.read()
    blobs = [data]
    i = 0
    while True:
        i = data.find(b"\x1f\x8b", i)
        if i < 0:
            break
        try:
            blobs.append(gzip.GzipFile(fileobj=io.BytesIO(data[i:])).read())
        except Exception:
            pass
        i += 1
    j = 0
    while True:
        j = data.find(b"\x78\x9c", j)
        if j < 0:
            break
        try:
            blobs.append(zlib.decompressobj().decompress(data[j : j + 2000000]))
        except Exception:
            pass
        j += 1
    return blobs


def scan_tokens(path):
    """返回 (命中 token 集合, err 或 None)。"""
    try:
        hits = set()
        for b in blobs_of(path):
            for t in ALL_TOKENS:
                if t not in hits and TOKEN_RES[t].search(b):
                    hits.add(t)
        return hits, None
    except Exception as e:  # OSError/EOFError/MemoryError 等——fail-loud 记账
        return set(), str(e)[:80]


def md5_of(path):
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def find_control():
    """platform 对照组定位：COQLIB/ROCQLIB/标准装机路径下找 ClassicalDedekindReals.vo。"""
    cands = []
    for base in CONTROL_BASES:
        if not base or not os.path.isdir(base):
            continue
        for rel in (
            os.path.join("user-contrib", "Stdlib", "Reals", CONTROL_NAME),
            os.path.join("Stdlib", "Reals", CONTROL_NAME),
        ):
            p = os.path.join(base, rel)
            if os.path.isfile(p):
                return p
        for dp, dn, fn in os.walk(base):
            if CONTROL_NAME in fn:
                cands.append(os.path.join(dp, CONTROL_NAME))
                break
    return cands[0] if cands else None


def load_blacklist(path):
    """毒 digest 黑名单：每行首字段=32 位小写 md5，行内 # 后为注释。"""
    entries = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.split()
            digest = parts[0].lower()
            name = parts[1] if len(parts) > 1 else ""
            if not re.fullmatch(r"[0-9a-f]{32}", digest):
                raise ValueError(f"blacklist 格式非法: {digest!r} in {path}")
            entries[digest] = name
    return entries


def scan_tree(tree, blacklist, strict_psatz):
    files = errors = 0
    token_hits = []   # 硬命中（strict 时含 Psatz）
    soft_hits = []    # Psatz 信息档
    digest_hits = []
    for dp, dn, fn in os.walk(tree):
        for name in sorted(fn):
            if not name.endswith(SCAN_SUFFIXES):
                continue
            path = os.path.join(dp, name)
            rel = os.path.relpath(path, tree)
            try:
                if os.path.getsize(path) > MAX_FILE_BYTES:
                    raise OSError(f"file exceeds {MAX_FILE_BYTES} bytes cap")
            except OSError as e:
                errors += 1
                token_hits.append({"file": rel, "token": "<IO-ERROR>", "digest": None,
                                   "name_mismatch": None, "err": str(e)})
                continue
            files += 1
            hits, err = scan_tokens(path)
            if err:
                errors += 1
                token_hits.append({"file": rel, "token": "<SCAN-ERROR>", "digest": None,
                                   "name_mismatch": None, "err": err})
            digest = None
            if blacklist:
                try:
                    digest = md5_of(path)
                except OSError as e:
                    errors += 1
                    token_hits.append({"file": rel, "token": "<MD5-ERROR>", "digest": None,
                                       "name_mismatch": None, "err": str(e)[:80]})
                else:
                    if digest in blacklist:
                        digest_hits.append({
                            "file": rel, "digest": digest,
                            "blacklist_name": blacklist[digest],
                            "name_mismatch": os.path.basename(path) != blacklist[digest],
                        })
            for t in sorted(hits):
                rec = {"file": rel, "token": t, "digest": digest,
                       "name_mismatch": None, "err": None}
                if t in HARD_TOKENS or (strict_psatz and t in SOFT_TOKENS):
                    token_hits.append(rec)
                else:
                    soft_hits.append(rec)
    return {"files": files, "errors": errors,
            "token_hits": token_hits, "soft_hits": soft_hits,
            "digest_hits": digest_hits}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", action="append", default=None,
                    help="树/世界根目录（可多次，递归扫 .vo/.vos/.vok）")
    ap.add_argument("--blacklist", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "poison_digest_blacklist_v2.txt"),
        help="毒 digest 黑名单（默认=同目录 vendored v2）")
    ap.add_argument("--control", default="auto",
                    help="platform 对照组 ClassicalDedekindReals.vo 路径；auto=自动定位；off=关闭（自担零命中不可信风险）")
    ap.add_argument("--strict-psatz", action="store_true",
                    help="Psatz 由信息档升为硬命中（默认关：净主树 172 件串表携带判例）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--text", action="store_true", help="只输出人类可读摘要")
    args = ap.parse_args()

    now = datetime.datetime.now().isoformat(timespec="seconds")
    trees = args.tree or [
        r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo"]
    report = {
        "scan_time": now, "tool": "gate5_vodep_quarantine",
        "hard_tokens": HARD_TOKENS, "soft_tokens": SOFT_TOKENS,
        "strict_psatz": args.strict_psatz, "trees": {}, "control": {},
        "blacklist": {}, "total_files": 0, "total_errors": 0,
        "total_token_hits": 0, "total_soft_hits": 0, "total_digest_hits": 0,
    }
    exit_code = 0
    fatal = None

    # 黑名单载入：文件缺失/为空/格式非法＝方法失效，exit 2（fail-loud）
    try:
        blacklist = load_blacklist(args.blacklist)
        if not blacklist:
            raise ValueError("blacklist 为空")
    except Exception as e:
        print(f"[gate5] FATAL: 黑名单不可用: {args.blacklist} ({e})", file=sys.stderr)
        return 2
    report["blacklist"] = {"path": args.blacklist, "entries": len(blacklist)}

    # 对照组自检：SELF-HIT 不成立＝扫描方法不可证，exit 2（防 glob 零命中假象）
    if args.control != "off":
        cpath = args.control if args.control != "auto" else find_control()
        if not cpath or not os.path.isfile(cpath):
            print("[gate5] FATAL: 对照组 ClassicalDedekindReals.vo 未定位到——"
                  "无 SELF-HIT 校准的零命中不可信（glob 假象判例）", file=sys.stderr)
            report["control"] = {"path": cpath, "status": "CONTROL-ABSENT"}
            fatal = "control-absent"
        else:
            hits, err = scan_tokens(cpath)
            ok = CONTROL_TOKEN in hits and err is None
            report["control"] = {"path": cpath, "status": "CONTROL-SELF-HIT-PASS" if ok
                                 else "CONTROL-SELF-HIT-FAIL", "tokens": sorted(hits),
                                 "err": err}
            if not ok:
                print(f"[gate5] FATAL: 对照组自命中失败: {cpath} hits={sorted(hits)} err={err}",
                      file=sys.stderr)
                fatal = "control-fail"
            else:
                print(f"[gate5] 对照组 SELF-HIT PASS: {cpath} tokens={sorted(hits)}")
        if fatal:
            if args.jsonout:
                with open(args.jsonout, "w", encoding="utf-8") as f:
                    json.dump(report, f, ensure_ascii=False, indent=1)
            print(f"[gate5] GATE5-VERDICT: {fatal.upper()} exit 2（不可判绿，fail-loud）")
            return 2

    for tree in trees:
        if not os.path.isdir(tree):
            print(f"[gate5] FATAL: 树不存在: {tree}", file=sys.stderr)
            report["trees"][tree] = {"error": "tree-missing"}
            fatal = "tree-missing"
            break
        res = scan_tree(tree, blacklist, args.strict_psatz)
        report["trees"][tree] = res
        for k, t in (("total_files", "files"), ("total_errors", "errors"),
                     ("total_token_hits", None), ("total_soft_hits", None),
                     ("total_digest_hits", None)):
            report[k] += res[t] if t is not None else len(res[k.replace("total_", "")])
        status = ("HIT(检疫咬合)" if res["token_hits"] or res["digest_hits"]
                  else "PASS(洁净)" if res["errors"] == 0 else "INCOMPLETE(扫描出错,不可判绿)")
        print(f"[gate5] 树={tree}  可扫件={res['files']}  硬命中={len(res['token_hits'])}  "
              f"软命中(Psatz信息档)={len(res['soft_hits'])}  digest命中={len(res['digest_hits'])}  "
              f"出错={res['errors']}  判定={status}  扫描时点={now}")
        for h in res["token_hits"]:
            print(f"  HIT {tree}{os.sep}{h['file']}  token={h['token']}"
                  + (f"  err={h['err']}" if h["err"] else ""))
        for h in res["digest_hits"]:
            print(f"  DIGEST-HIT {tree}{os.sep}{h['file']}  md5={h['digest']}"
                  f"  册名={h['blacklist_name']}"
                  + ("  [改名投毒:name_mismatch]" if h["name_mismatch"] else ""))
        for h in res["soft_hits"]:
            print(f"  soft {tree}{os.sep}{h['file']}  token={h['token']}（信息档非硬命中）")
        if res["token_hits"] or res["digest_hits"]:
            exit_code = max(exit_code, 1)
        if res["errors"]:
            fatal = fatal or "incomplete-surface"

    total_hit = report["total_token_hits"] + report["total_digest_hits"]
    if exit_code == 0 and report["total_files"] == 0:
        print("[gate5] FATAL: 无可扫面（0 件 .vo/.vos/.vok）——不可判绿", file=sys.stderr)
        fatal = fatal or "no-scannable-surface"
    if fatal:
        exit_code = 2 if exit_code == 0 else exit_code
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1)
    if exit_code == 0:
        print(f"[gate5] GATE5-VERDICT: CLEAN exit 0（扫 {report['total_files']} 件＋"
              f"硬 token 0 命中＋digest 0 命中＋对照 SELF-HIT 过；"
              f"Psatz 信息档 {report['total_soft_hits']} 件已记录）")
    elif exit_code == 1:
        print(f"[gate5] GATE5-VERDICT: HIT exit 1（硬命中 {total_hit} 处——检疫咬合，"
              "处置循 VO-RES-CLEAN 纪律：删毒代＋净源重编消费者闭包＋Axioms=<none> 复证）")
    else:
        print(f"[gate5] GATE5-VERDICT: {str(fatal).upper()} exit 2（不可判绿，fail-loud）")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
