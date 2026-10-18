#!/bin/bash
# parallel_chk.sh — 全树内核认证·根分组均衡并行版（20261018 双机同源）
#
# 历史判例守线（coqchk_all.sh 头注）：逐件循环 O(n²) 闭包重验已否决（99 件=3-8h）；
# 单遍全模块共享闭包为 CPU 成本下界但本质串行（842 件基线 3h04m、含大计算件时 4h+）。
#
# 本版原理：认证面按「依赖顶根」（无下游消费者的模块）的传递闭包做均衡装箱，
# 切成 K 组（CHK_JOBS，默认 3）；每组一次 rocqchk 调用（组内共享闭包·组间重复
# 仅共享基座）。墙钟 ≈ max(组闭包) + 基座税，目标 ≤2h。模块级完备性不变：
# 每个模块至少在其所属组的调用中被内核检查，且作为后组闭包被递归重验。
#
# gate2 兼容：K 路日志按组序合并为 _chk_all.log（每路自带 Chicken 9.1.0 banner，
# gate2 grep -q 语义不受影响；Axioms 段逐模块保全）。
# fail-loud：任一路非 0、或合并日志缺 "Modules were successfully checked" → exit 1。
# 温控：组数=并行度（CHK_JOBS）；整体由 yml 层 cpu_guard 包裹（负载>阈值错峰）。
# 环境变量：COQCHK（二进制路径，同 coqchk_all.sh 协议）/ CHK_JOBS（并行度）/ PYTHON。
set -u
cd "$(dirname "$0")/../ConstructiveWorld_vo" || { echo "PCHK-PWD-FAIL"; exit 2; }
K="${COQCHK:-C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe}"
JOBS="${CHK_JOBS:-3}"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || PY=python

# COQLIB/ROCQLIB 同源导出（E-STAGING-SW2 教义：bin/lib 必须同源）
case "$K" in
  */bin/coqchk.exe) COQLIB="${K%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     COQLIB="${K%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$K" in
  *coqchk.exe) ROCQDEP="${K%coqchk.exe}rocq.exe" ;;
  *coqchk)     ROCQDEP="${K%coqchk}rocq" ;;
esac
# rocq dep 可显式覆盖（mac shim 目录无 rocq 时指真工具链 rocq）
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

# ① 认证面清单（`_` 前缀探针/暂态 .vo 不入闭包——CI#46 教训）
: > /tmp/_pchk_mods.txt
for f in *.vo; do
  case "$f" in _*) continue ;; esac
  printf '%s\n' "$(basename "$f" .vo)" >> /tmp/_pchk_mods.txt
done
NMOD=$(wc -l < /tmp/_pchk_mods.txt)
[ "$NMOD" -gt 0 ] || { echo "PCHK-NO-MODS"; exit 2; }

# ② 依赖图（rocq dep 同款环境）→ 顶根闭包均衡装箱
"$ROCQDEP" dep -Q . "" $(ls *.v 2>/dev/null | grep -v '^_') > /tmp/_pchk_deps.txt 2>/dev/null || true
CHK_JOBS="$JOBS" "$PY" - <<'PYEOF' > /tmp/_pchk_groups.txt
import os
from collections import defaultdict
deps = defaultdict(set); rdeps = defaultdict(set)
allm = [l.strip() for l in open('/tmp/_pchk_mods.txt') if l.strip()]
allset = set(allm)
for line in open('/tmp/_pchk_deps.txt'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    src = vt[0].replace('\\', '/').split('/')[-1][:-3]
    if src not in allset:
        continue
    for t in right.split():
        if t.endswith('.vo') and not t.startswith('/'):
            d = t.replace('\\', '/').split('/')[-1][:-3]
            if d != src and d in allset:
                deps[src].add(d); rdeps[d].add(src)
def closure(m):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        st.extend(deps.get(x, ()))
    return seen
K = max(1, int(os.environ.get('CHK_JOBS', '3')))
roots = sorted(m for m in allm if not rdeps.get(m))
items = sorted(((len(closure(r)), r) for r in roots), reverse=True)
loads = [0] * K
groups = [[] for _ in range(K)]
assigned = set()
for sz, r in items:
    cl = closure(r)
    if cl & assigned:
        continue  # 闭包与已装箱根重叠——留给并集面，防同组双计
    assigned |= cl
    i = loads.index(min(loads))
    groups[i].append(r)
    loads[i] += sz
orphans = allset - assigned
if orphans:
    i = loads.index(max(loads))
    groups[i].extend(sorted(orphans))
for g in groups:
    if not g:
        print('')
        continue
    uni = set()
    for r in g:
        uni |= closure(r)
    print('\x1f'.join(sorted(uni)))
PYEOF

# ③ K 路并行（组数=并行度）
i=0
while IFS= read -r grp; do
  [ -n "$grp" ] || continue
  mods=$(printf '%s' "$grp" | tr '\037' ' ')
  nm=$(printf '%s' "$mods" | wc -w | tr -d ' ')
  echo "PCHK group $((i+1)): $nm modules"
  ( "$K" -o -Q . "" $mods > "/tmp/_pchk_g$i.log" 2>&1; echo $? > "/tmp/_pchk_g$i.rc" ) &
  i=$((i+1))
done < /tmp/_pchk_groups.txt
NGRP=$i
[ "$NGRP" -gt 0 ] || { echo "PCHK-NO-GROUPS"; exit 2; }
wait

# ④ 日志按组序合并（gate2 兼容）+ fail-loud 终审
: > _chk_all.log
rc_total=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "/tmp/_pchk_g$j.rc" 2>/dev/null || echo 1)
  [ "$rc" -eq 0 ] || rc_total=1
  cat "/tmp/_pchk_g$j.log" >> _chk_all.log 2>/dev/null || rc_total=1
done
grep -q "Modules were successfully checked" _chk_all.log || rc_total=1
tail -5 _chk_all.log
if [ "$rc_total" -eq 0 ]; then
  echo "COQCHK_ALL_PASS (parallel, $NGRP groups, $NMOD modules)"
  exit 0
fi
echo "COQCHK_FAIL (parallel; merged=_chk_all.log, per-group=/tmp/_pchk_g*.log)"
exit 1
