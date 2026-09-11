#!/bin/bash
# ============================================================================
# merge220.sh — releases/CW_ConstructiveWorld_220.v 确定性生成器（2026-09-10）
# ============================================================================
# 事故背景：CI #27（af82fa6）报 `Error: positive_dist already exists`（L115662）。
# 旧合并轨为历轮扁平手拼（基座 219 + 各新库原文拼接），新库重复定义基座已有名即炸。
# 处置（用户裁决 20260910）：源级改名方案——新库侧（attn 的 Up*/CW220_Extensions.v）
# 已按 scripts/rename-ledger-20260910.md 完成 150 名源级改名；本生成器以扁平拼接
# 确定性重生成合并轨，并内置【撞名闸门】：逐名比对前序模块与基座已定义名，
# 发现撞名立即 FAIL 并报出名字与文件——把本次事故变永久关卡。
#
# 输入：
#   基座  = ConstructiveWorld_vo/CW_ConstructiveWorld_219.v（仓库已入库正名，只读）
#   模块  = scripts/order.txt 前 34 项（"220 合并区：34 模块"既定范围）；
#           模块源当前取 attn 工作区（本席位改名后版本；主会话捆绑入库后，
#           如 ConstructiveWorld_vo 已同步同名版，可切换 MOD_SRC=repo 再跑，产物不变）。
#   排除  = CW214KL_scan.v / AttnHardLimit218.v（基座已内联其内容的只读垫片件，
#           合并轨不内联；.vo 扁平库经 Import 遮蔽合法消费）。
# 变换：基座原样置顶；其后每模块剥除非 Stdlib 的 Require 行（项目内依赖已由
#       基座/前序块就地满足，实测外部名 100% 由基座供给），其余字节原样。
# 幂等：头部"生成时间"取输入文件最新 mtime（确定性），同输入 → 字节同产物。
# 产物：releases/CW_ConstructiveWorld_220.v（首跑前旧件自动备份 .bak）
# ============================================================================
set -u
REPO="D:/ComplexAnalysis/ConstructiveWorld-Main"
ATTN="D:/ComplexAnalysis/新算法实践/attn"
BASE="$REPO/ConstructiveWorld_vo/CW_ConstructiveWorld_219.v"
ORDER="$REPO/scripts/order.txt"
OUT="$REPO/releases/CW_ConstructiveWorld_220.v"
MOD_SRC="${MOD_SRC:-attn}"    # attn|repo
NMERGE=34                     # 合并区模块数（v4 既定 34）

[ -f "$BASE" ] || { echo "FAIL: missing base $BASE"; exit 2; }
[ -f "$ORDER" ] || { echo "FAIL: missing $ORDER"; exit 2; }

# 旧件备份（仅首跑）
if [ -f "$OUT" ] && [ ! -f "$OUT.bak" ]; then
  cp -p "$OUT" "$OUT.bak" && echo "[bak] 旧合并轨已备份 -> CW_ConstructiveWorld_220.v.bak"
fi

python - "$BASE" "$ORDER" "$OUT" "$MOD_SRC" "$ATTN" "$REPO" "$NMERGE" <<'PYEOF'
import sys, os, re, hashlib
from collections import OrderedDict
from datetime import datetime

BASE, ORDER, OUT, MOD_SRC, ATTN, REPO, NMERGE = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7])
REPO_VO = os.path.join(REPO, "ConstructiveWorld_vo")

HEAD = re.compile(r"^(?:Program\s+)?(Definition|Theorem|Lemma|Corollary|Remark|Fact|Example|Proposition|Instance|Fixpoint|CoFixpoint|Function|Inductive|CoInductive|Class|Record|Structure|Scheme)\b\s*([^:={(*]*?)(?:\s*[:({:=]|$)")
CTOR = re.compile(r"^\|\s*([A-Za-z_][A-Za-z0-9_']*)\s*[:(]")
INLINE = re.compile(r":=\s*([A-Za-z_][A-Za-z0-9_']*)\s*[:({]")
FIELD = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*)\s*:")
REQLINE = re.compile(r"^\s*(?:From\s+[A-Za-z0-9_.']+\s+)?Require\s+Import\s+([A-Za-z0-9_'.]+)")

def sha1(p):
    return hashlib.sha1(open(p, "rb").read()).hexdigest()

def strip_comments(lines):
    out, cdepth, instr = [], 0, False
    for raw in lines:
        line = raw.rstrip("\r\n")
        buf, i, n = [], 0, len(line)
        while i < n:
            c2 = line[i]; two = line[i:i+2]
            if cdepth > 0:
                if two == "(*": cdepth += 1; i += 2
                elif two == "*)": cdepth -= 1; i += 2
                else: i += 1
            elif instr:
                if two == '\\"': i += 2
                elif c2 == '"': instr = False; i += 1
                else: i += 1
            else:
                if two == "(*": cdepth += 1; i += 2
                elif c2 == '"': instr = True; buf.append(" "); i += 1
                else: buf.append(c2); i += 1
        out.append("".join(buf))
    return out

def scan(path, stripped=None):
    """根命名空间定义（Module 隔离 / Section 拍平 / 构造子字段随宿主）"""
    names = OrderedDict()
    pend = None
    stack = []
    if stripped is None:
        with open(path, encoding="utf-8", errors="replace", newline="") as fh:
            raw_lines = fh.readlines()
        stripped = strip_comments(raw_lines)
    in_mod = any(k == "M" for k, _ in stack)
    for ln, s in enumerate(stripped, 1):
        s = s.strip()
        if not s: continue
        ms = re.match(r"^(?:Declare\s+)?Module\s+([A-Za-z0-9_']+)", s)
        if ms:
            stack.append(("M", ms.group(1))); pend = None; continue
        me = re.match(r"^End\s+([A-Za-z0-9_']+)", s)
        if me and stack:
            if stack[-1][1] == me.group(1): stack.pop()
            pend = None; continue
        ss = re.match(r"^Section\s+([A-Za-z0-9_']+)", s)
        if ss:
            stack.append(("S", ss.group(1))); continue
        if any(k == "M" for k, _ in stack): continue
        m = HEAD.match(s)
        if m:
            tok = (m.group(2).strip().split() or [""])[0]
            kw = m.group(1)
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tok):
                names.setdefault(tok, ln)
            pend = tok if kw in ("Inductive", "CoInductive", "Record", "Structure") else None
            if pend:
                ic = INLINE.search(s)
                if ic: names.setdefault(ic.group(1), ln)
            continue
        if s.startswith("|"):
            c = CTOR.match(s)
            if c and pend: names.setdefault(c.group(1), ln); continue
        if pend in ("Record", "Structure"):
            f2 = FIELD.match(s)
            if f2: names.setdefault(f2.group(1), ln)
        if "}" in s or "=>" in s or s == "." or s.startswith("End"):
            pend = None
    return names

def module_path(f):
    if MOD_SRC == "attn":
        p = os.path.join(ATTN, f)
        if os.path.exists(p): return p
    p2 = os.path.join(REPO_VO, f)
    if os.path.exists(p2): return p2
    return None

order = [l.strip() for l in open(ORDER, encoding="utf-8") if l.strip()]
mods = order[:NMERGE]
paths = []
for f in mods:
    p = module_path(f)
    if not p:
        print("GATE-FAIL: 模块缺失 %s（MOD_SRC=%s）" % (f, MOD_SRC)); sys.exit(1)
    paths.append((f, p))

# ---------- 撞名闸门（事故变永久关卡）----------
dup = OrderedDict()
def seen_before(n, label, ln):
    dup.setdefault(n, []).append((label, ln))
seen_map = OrderedDict()   # name -> first (label, line)
with open(BASE, encoding="utf-8", errors="replace", newline="") as fh:
    base_lines = fh.readlines()
base_stripped = strip_comments(base_lines)
for n, ln in scan(BASE, base_stripped).items():
    seen_map.setdefault(n, ("CW_ConstructiveWorld_219.v", ln))
gate = []
for f, p in paths:
    for n, ln in scan(p).items():
        if n in seen_map:
            gate.append((n, seen_map[n], (f, ln)))
        else:
            seen_map[n] = (f, ln)
if gate:
    print("GATE-FAIL: 撞名 %d 处——合并轨拒绝生成（名字 | 首定义 | 重定义）：" % len(gate))
    for n, first, second in gate:
        print("  %s | %s@L%d | %s@L%d" % (n, first[0], first[1], second[0], second[1]))
    sys.exit(1)
print("GATE-OK: 基座+%d 模块逐名比对零撞名" % NMERGE)

# ---------- 拼接 ----------
def strip_local_requires(path):
    """剥除非 Stdlib Require 行（项目内依赖已就地满足）；其余字节原样"""
    with open(path, encoding="utf-8", errors="replace", newline="") as fh:
        lines = fh.readlines()
    kept, dropped = [], 0
    for raw in lines:
        rm = REQLINE.match(raw)
        if rm and re.match(r"^(CW[0-9]|CW_|Up[A-Z])", rm.group(1)):
            dropped += 1
            continue
        kept.append(raw)
    return kept, dropped

mt = max(os.path.getmtime(p) for p in [BASE] + [p for _, p in paths])
gen_time = datetime.fromtimestamp(mt).strftime("%Y-%m-%d %H:%M:%S %z")
hdr = []
hdr.append("(* ============================================================================\n")
hdr.append("    CW_ConstructiveWorld_220.v — 合并轨确定性产物 · merge220.sh 生成\n")
hdr.append("    生成时间·输入最新mtime: %s\n" % gen_time)
hdr.append("    基座: CW_ConstructiveWorld_219.v sha1=%s · %d 行 · 原样置顶\n"
           % (sha1(BASE), len(base_lines)))
hdr.append("    模块清单: order.txt 前 %d 项 · 源=%s · 已剥项目内 Require 行\n" % (NMERGE, MOD_SRC))
for f, p in paths:
    hdr.append("      %-24s sha1=%s\n" % (f, sha1(p)))
hdr.append("    撞名闸门: 基座+%d 模块逐名比对零撞名（本头部使正文行号整体下移）\n" % NMERGE)
hdr.append("    改名依据: scripts/rename-ledger-20260910.md · 源级改名方案 2026-09-10\n")
hdr.append("============================================================================ *)\n")
head_txt = "".join(hdr)
assert "(*" not in head_txt[2:] and "*)" not in head_txt[:-3], "header comment safety"
parts = [head_txt]
parts.extend(base_lines)
total_dropped = 0
for f, p in paths:
    kept, dropped = strip_local_requires(p)
    total_dropped += dropped
    parts.append("(* ==================== 合并模块 %s ==================== *)\n" % f)
    parts.extend(kept)
os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w", encoding="utf-8", newline="") as fh:
    fh.writelines(parts)
n_out = sum(1 for _ in open(OUT, encoding="utf-8", errors="replace"))
print("OUT=%s" % OUT)
print("OUT_LINES=%d" % n_out)
print("OUT_SHA1=%s" % sha1(OUT))
print("STRIPPED_REQUIRE_LINES=%d" % total_dropped)
PYEOF
rc=$?
[ $rc -ne 0 ] && { echo "merge220: FAILED (rc=$rc)"; exit $rc; }
echo "merge220: OK"
