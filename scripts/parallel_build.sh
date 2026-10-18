#!/bin/bash
# parallel_build.sh — 全树构建·依赖分层并行版（20261018 双机同源）
#
# 原理：rocq dep 生成依赖图 → Kahn 拓扑分层（层内模块互不依赖）→ 逐层并行：
# 层内缺失/陈旧 .vo 的件经 xargs -P 并行 coqc（层间必须串行——依赖在先层落盘）。
# 指纹 SKIP 语义不变（.vo 新于 .v 即跳）；本脚本只预编缺失/陈旧件，终审 build 面
# 由 yml 后续 Build 步（build.sh/cw_build）承担——双保险口径与 mac Bootstrap 先例一致。
#
# 环境变量：COQC（coqc 路径，Windows 默认 Rocq-Platform 9.1 推导·mac 侧 yml 步显式
# export mac_rocq shim）/ CHK_ROCQDEP（rocq 路径覆盖）/ BLDJ_JOBS（并行度，默认 3）/
# PYTHON。fail-loud：任何件编译红 → 红件清单落 /tmp/_pbld_fail.txt + exit 1。
set -u
cd "$(dirname "$0")/../ConstructiveWorld_vo" || { echo "PBLD-PWD-FAIL"; exit 2; }
COQC_BIN="${COQC:-C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe}"
JOBS="${BLDJ_JOBS:-3}"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || PY=python

# SW2 同源导出（与 coqchk_all.sh/parallel_chk.sh 同协议）
case "$COQC_BIN" in
  */bin/coqc.exe) COQLIB="${COQC_BIN%/coqc.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqc)     COQLIB="${COQC_BIN%/coqc}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$COQC_BIN" in
  *coqc.exe) ROCQDEP="${COQC_BIN%coqc.exe}rocq.exe" ;;
  *coqc)     ROCQDEP="${COQC_BIN%coqc}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

# ① 全源清单+依赖图（`_` 前缀暂态件排除）
find . -maxdepth 1 -name '*.v' ! -name '_*' | sed 's|^\./||' | sort > /tmp/_pbld_allv.txt
NALL=$(wc -l < /tmp/_pbld_allv.txt)
"$ROCQDEP" dep -Q . "" $(cat /tmp/_pbld_allv.txt) > /tmp/_pbld_deps.txt 2>/dev/null || true

# ② Kahn 分层：层=入度零批次的逐波剥离（层内并行安全）
"$PY" - <<'PYEOF' > /tmp/_pbld_layers.txt
from collections import defaultdict, deque
import os
allv = [l.strip() for l in open('/tmp/_pbld_allv.txt') if l.strip()]
allset = set(allv)
deps = defaultdict(set)
for line in open('/tmp/_pbld_deps.txt'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    src = vt[0].replace('\\', '/').split('/')[-1][:-3] + '.v'
    if src not in allset:
        continue
    for t in right.split():
        if t.endswith('.vo') and not t.startswith('/'):
            d = t.replace('\\', '/').split('/')[-1][:-3] + '.v'
            if d != src and d in allset:
                deps[src].add(d)
indeg = {f: len(deps[f] & allset) for f in allv}
rdeps = defaultdict(list)
for f, ds in deps.items():
    for d in ds & allset:
        rdeps[d].append(f)
q = deque(sorted(f for f in allv if indeg[f] == 0))
placed = set()
layers = []
while q:
    layer = sorted(q); q = deque()
    layers.append(layer)
    placed |= set(layer)
    for f in layer:
        for c in sorted(rdeps[f]):
            if c in placed:
                continue
            indeg[c] -= 1
            if indeg[c] == 0:
                q.append(c)
rest = sorted(allset - placed)
if rest:
    print("WARN-DEP-CYCLE %d" % len(rest), __import__('sys').stderr)
    layers.append(rest)
for layer in layers:
    print('\x1f'.join(layer))
PYEOF

# ③ 逐层并行编译（缺失/陈旧才编——指纹 SKIP 语义保持）
: > /tmp/_pbld_fail.txt
nbuilt=0; nskip=0; nfail=0; layer_i=0
while IFS= read -r layer; do
  [ -n "$layer" ] || continue
  layer_i=$((layer_i+1))
  todo=""
  for f in $(printf '%s' "$layer" | tr '\037' ' '); do
    v="${f%.v}.vo"
    if [ -f "$v" ] && [ "$v" -nt "$f" ]; then nskip=$((nskip+1)); continue; fi
    todo="$todo $f"
  done
  [ -n "$todo" ] || continue
  echo "$todo" | tr ' ' '\n' | grep -v '^$' | \
    xargs -P "$JOBS" -I{} bash -c '
      f="{}"; v="${f%.v}.vo"
      log="/tmp/_pbld_${f//\//_}.log"
      if "'"$COQC_BIN"'" -native-compiler no -q -Q . "" "$f" > "$log" 2>&1; then
        echo "OK $f"
      else
        echo "FAIL $f" | tee -a /tmp/_pbld_fail.txt
      fi' | while read -r st f; do echo "  [L$layer_i] $st $f"; done
done
# 计数直读（E-STAGING-R84-GATECHAIN 教义：管道计数短路坑规避——独立统计）
nb=$(ls /tmp/_pbld_*.log 2>/dev/null | wc -l)
nf=$(grep -c '^FAIL' /tmp/_pbld_fail.txt 2>/dev/null || true)
[ "${nf:-0}" -eq 0 ] || nfail=$nf
echo "parallel_build: layers=$layer_i total=$NALL compiled_logs=$nb skip_or_fresh≈$nskip fail=${nfail:-0}"

if [ "${nfail:-0}" -eq 0 ]; then
  echo "PARALLEL_BUILD_PASS"
  exit 0
fi
echo "PARALLEL_BUILD_FAIL — red files:"
cat /tmp/_pbld_fail.txt
exit 1
