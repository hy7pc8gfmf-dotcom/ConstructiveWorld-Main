# -*- coding: utf-8 -*-
"""gen_order_stable.py — order.txt 稳定锚列生成器（A4 patch 包交付件，零 apply）

使命：根治「order 行号随注册波平移、论文引裸行号必锈」。
每行格式：<件名>#<入册轮次>-<commit前6>（如 UpAblLogSelOracle.v#R113-1719a2）；
入册轮次不可考者统一 #R0-d66910（R113 基线 md5 d6691094 前 6）。
# 后内容为元数据列：所有消费者必须先剥 # 列（见 consumer_tolerance.patch）。

模式：
  --backfill            存量一次性补 ID（读各树 order.txt，重写同树文件；三树跑同脚本即三树同值）
  --append FILE.v --round R1xx --commit <hash>   注册波尾插一行（禁重排；E1 查重/E3 查幽灵）
  --verify              卫生门：三树同值 + 零重复(E1) + 零幽灵(E3) + ID 列格式合法
fail-loud：任何门失败非零退出，禁静默。
"""
import argparse, hashlib, os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREES = [os.path.join(REPO, "ConstructiveWorld_Live"),
         os.path.join(REPO, "ConstructiveWorld_vo"),
         os.path.join(REPO, "scripts")]
MAP_FILE = os.path.join(REPO, "scripts", "order_stable_map.tsv")
BASELINE6 = "d66910"  # R113 基线 order.txt md5=d6691094... 前 6
ID_RE = re.compile(r"^(?P<fn>[A-Za-z0-9_]+\.v)#(?P<rnd>R\d+)-(?P<h6>[0-9a-f]{6})$")


def read_order(tree):
    p = os.path.join(tree, "order.txt")
    with open(p, encoding="utf-8") as f:
        return p, [l.rstrip("\r\n") for l in f]


def strip_id(line):
    return line.split("#", 1)[0].strip()


def load_map():
    m = {}
    if os.path.exists(MAP_FILE):
        with open(MAP_FILE, encoding="utf-8") as f:
            for ln in f:
                parts = ln.rstrip("\n").split("\t")
                if len(parts) >= 3 and parts[0] != "filename":
                    m[parts[0]] = (parts[1], parts[2])
    return m


def save_map(m):
    with open(MAP_FILE, "w", encoding="utf-8", newline="\n") as f:
        f.write("filename\tround\tcommit6\n")
        for fn in sorted(m):
            f.write(f"{fn}\t{m[fn][0]}\t{m[fn][1]}\n")


def gates(orders_by_tree, live_tree):
    errs = []
    seqs = {t: [strip_id(l) for l in o] for t, o in orders_by_tree.items()}
    canon = seqs[TREES[0]]
    for t, s in seqs.items():                      # G1 三树同值（内容级）
        if s != canon:
            errs.append(f"G1 三树不同值: {t}")
    seen = {}
    for i, fn in enumerate(canon):                 # E1 零重复
        seen.setdefault(fn, []).append(i + 1)
    dups = {k: v for k, v in seen.items() if len(v) > 1}
    if dups:
        errs.append(f"E1 重复行: {dups}")
    for fn in canon:                               # E3 零幽灵（两树实存）
        for t in (TREES[0], TREES[1]):
            if not os.path.exists(os.path.join(t, fn)):
                errs.append(f"E3 幽灵行: {fn} 不在 {os.path.basename(t)}")
                break
    for t, o in orders_by_tree.items():            # ID 列格式合法
        for i, l in enumerate(o, 1):
            if l.strip() and not ID_RE.match(l.strip()):
                errs.append(f"ID格式: {os.path.basename(t)}:{i} [{l}]")
    return errs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backfill", action="store_true")
    ap.add_argument("--append", metavar="FILE.v")
    ap.add_argument("--round", metavar="R1xx")
    ap.add_argument("--commit", metavar="HASH")
    ap.add_argument("--verify", action="store_true")
    a = ap.parse_args()

    orders = {t: read_order(t)[1] for t in TREES}
    if a.verify or a.backfill:
        pass  # gates run below for verify; backfill pre-checks E1/E3 first

    if a.verify:
        errs = gates(orders, TREES[0])
        for e in errs:
            print("[FAIL]", e)
        print("verify:", "PASS" if not errs else f"FAIL ({len(errs)})")
        sys.exit(1 if errs else 0)

    if a.append:
        if not (a.round and a.commit):
            sys.exit("FATAL: --append 需 --round 与 --commit")
        fn = os.path.basename(a.append)
        for t in (TREES[0], TREES[1]):             # E3 预检
            if not os.path.exists(os.path.join(t, fn)):
                sys.exit(f"FATAL E3: {fn} 不在 {os.path.basename(t)}，禁注册幽灵件")
        for t, o in orders.items():                # E1 预检
            if fn in [strip_id(l) for l in o]:
                sys.exit(f"FATAL E1: {fn} 已在 {os.path.basename(t)}/order.txt，禁重复注册")
        line = f"{fn}#{a.round}-{a.commit[:6]}"
        for t, o in orders.items():                # 尾插（禁重排）
            o.append(line)
            with open(os.path.join(t, "order.txt"), "w", encoding="utf-8", newline="\n") as f:
                f.write("\n".join(o) + "\n")
        m = load_map(); m[fn] = (a.round, a.commit[:6]); save_map(m)
        print(f"appended: {line} -> 3 trees + map")
        return

    if a.backfill:
        m = load_map()
        errs = []
        for t, o in orders.items():
            names = [strip_id(l) for l in o]
            dups = {k for k in names if names.count(k) > 1}
            if dups:
                errs.append(f"E1 {os.path.basename(t)}: {sorted(dups)}")
            for fn in names:  # E3 仅查 Live/vo 两树（scripts 树无 .v，属正常）
                for vt in (TREES[0], TREES[1]):
                    if not os.path.exists(os.path.join(vt, fn)):
                        errs.append(f"E3 {os.path.basename(t)}: 幽灵 {fn}")
                        break
        if errs:
            for e in errs:
                print("[FAIL]", e)
            sys.exit("backfill 预检失败，未写任何文件")
        for t, o in orders.items():
            out = []
            for l in o:
                fn = strip_id(l)
                rnd, c6 = m.get(fn, ("R0", BASELINE6))
                out.append(f"{fn}#{rnd}-{c6}")  # R0 亦带统一锚 #R0-d66910
            with open(os.path.join(t, "order.txt"), "w", encoding="utf-8", newline="\n") as f:
                f.write("\n".join(out) + "\n")
        print(f"backfill done: {len(orders)} trees x {len(out)} lines")
        errs = gates({t: read_order(t)[1] for t in TREES}, TREES[0])
        for e in errs:
            print("[FAIL]", e)
        sys.exit(1 if errs else 0)

    ap.print_help()


if __name__ == "__main__":
    main()
