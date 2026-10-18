#!/bin/bash
# parallel_chk.sh — 全树内核认证·均衡分组并行版 v2（20261019 set1557 修订）
#
# v1→v2 修订缘由（run#267 Windows coqchk 红根因）：
#   R1 Windows python /tmp 路径修复：同 parallel_build.sh R1——v1 heredoc Python
#      open('/tmp/...') 在 Windows 原生 python 下解析为 <盘>:\tmp\... → FileNotFoundError
#      → 分组输出 0 字节 → 零组 → PCHK-NO-GROUPS exit 2（run#267 实证，盘面
#      /tmp/_pchk_groups.txt 0 字节 + CI 日志 PCHK-NO-GROUPS 双证）。v2 全部 Python
#      数据面走 cwd 相对路径（_pchk_tmp/）。
#   R2 装箱算法重设计：v1 按依赖顶根闭包装箱，「大闭包根独占 + 其余成 orphans 倾入
#      单组」——实采数据重放（run#267 在飞 _pchk_deps.txt，841 模块 406 根）得组形
#      811/23/22：96% 全树挤单组=并行名存实亡 + 811 模块单 argv 逼 Windows CreateProcess
#      32K 参数墙。v2 全模块按闭包规模降序 + 预算封顶贪心（CAP=⌈1.15·N/K⌉）：
#      实测组形 281/280/280·闭包并集 393/452/412·argv≈5K。
#   R3 语义红线机械化：并集覆盖断言（每组模块列表恰一次列出·并集==全模块集·违者
#      exit 2）；order.txt 注册面覆盖断言（认证面 ⊇ 注册面·缺件 exit 2）；退化守卫
#      （NMOD>200 而组数<2 = 退化单遍，exit 2）。
#
# 认证语义（红线）：每模块恰被一组的 rocqchk 调用列出（恰一次）；组内核沿传递闭包
# 整链核验；跨组共享基座被重复核验=更强保障非缺口；三组日志按组序合并为 _chk_all.log
# （每路自带 Chicken 9.1.0 banner·Axioms 段逐模块保全·gate2 块状态机零改动兼容）。
#
# fail-loud：任一路非 0、或合并日志缺 "Modules were successfully checked" → exit 1。
# 温控：组数=并行度（CHK_JOBS）；整体由 yml 层 cpu_guard 包裹（负载>阈值错峰）。
# 环境变量：COQCHK / CHK_JOBS（并行度）/ CHK_ROCQDEP / PYTHON / PCHK_PACK_ONLY=1
# （仅装箱打印组形即退·调试旗标）。
set -u
cd "$(dirname "$0")/../ConstructiveWorld_vo" || { echo "PCHK-PWD-FAIL"; exit 2; }
K="${COQCHK:-C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe}"
JOBS="${CHK_JOBS:-3}"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || { echo "PCHK-NO-PYTHON: python3/python/py 全缺席"; exit 2; }

# COQLIB/ROCQLIB 同源导出（E-STAGING-SW2 教义：bin/lib 必须同源）
case "$K" in
  */bin/coqchk.exe) COQLIB="${K%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     COQLIB="${K%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$K" in
  *coqchk.exe) ROCQDEP="${K%coqchk.exe}rocq.exe" ;;
  *coqchk)     ROCQDEP="${K%coqchk}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

WORK="_pchk_tmp"
rm -rf "$WORK"; mkdir -p "$WORK"

# ① 认证面清单（`_` 前缀探针/暂态 .vo 不入闭包——CI#46 教训）
: > "$WORK/mods.txt"
for f in *.vo; do
  [ -e "$f" ] || continue
  case "$f" in _*) continue ;; esac
  printf '%s\n' "${f%.vo}" >> "$WORK/mods.txt"
done
NMOD=$(wc -l < "$WORK/mods.txt")
[ "$NMOD" -gt 0 ] || { echo "PCHK-NO-MODS"; exit 2; }

# ①a 注册面覆盖断言（禁漏件门：order.txt 全注册 .v 须有 .vo 且入认证面）
# 子目录注册行（Local/*，order L478 R160 判例）：build 面自编自管（build.sh 逐件走）·
# 认证面 membership 断言仅约束顶层（历史 coqchk_all 顶层 glob 语义）——Local 件经
# 依赖闭包随组核验，不单列。
covfail=0
while IFS= read -r line; do
  f=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '\r' | tr -d ' ')
  case "$f" in *.v) ;; *) continue ;; esac
  case "$f" in */*) continue ;; esac
  m="${f%.v}"
  if [ ! -f "${m}.vo" ]; then echo "PCHK-COV-NO-VO: 注册面 $f 无 .vo（先修 build）"; covfail=1; continue; fi
  grep -qxF "$m" "$WORK/mods.txt" || { echo "PCHK-COV-EXCLUDED: 注册面 $m 未入认证面"; covfail=1; }
done < order.txt
[ "$covfail" -eq 0 ] || { echo "PCHK-COVERAGE-FAIL: 注册面覆盖断言红——fail-loud"; exit 2; }

# ② 依赖图 → 均衡分组
"$ROCQDEP" dep -Q . "" $(ls *.v 2>/dev/null | grep -v '^_') > "$WORK/deps.txt" 2>/dev/null || true
[ -s "$WORK/deps.txt" ] || echo "PCHK-WARN-EMPTYDEP: rocq dep 零输出（闭包退化=每组仅列模块——fail-loud 留痕）"
CHK_JOBS="$JOBS" "$PY" - "$WORK/mods.txt" "$WORK/deps.txt" > "$WORK/groups.txt" <<'PYEOF'
import sys, os, math
from collections import defaultdict
mods_f, deps_f = sys.argv[1], sys.argv[2]
allm = [l.strip() for l in open(mods_f, encoding='utf-8', errors='replace') if l.strip()]
allset = set(allm)
deps = defaultdict(set)
for line in open(deps_f, encoding='utf-8', errors='replace'):
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
                deps[src].add(d)
def closure(m):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        st.extend(deps.get(x, ()))
    return seen
clmemo = {m: closure(m) for m in allm}
N = len(allm)
K = max(1, int(os.environ.get('CHK_JOBS', '3')))
if N > 200 and K < 2:
    sys.stderr.write('PCHK-DEGENERATE: NMOD=%d 但 CHK_JOBS=%d（退化单遍禁）\n' % (N, K))
    sys.exit(2)
CAP = math.ceil(N / K * 1.15)
items = sorted(((len(clmemo[m]), m) for m in allm), reverse=True)
loads = [0] * K
groups = [[] for _ in range(K)]
assigned = set()
for sz, m in items:
    if m in assigned:
        continue
    S = (clmemo[m] - assigned) | {m}
    best = -1; bestload = None
    for i in range(K):
        nl = loads[i] + len(S)
        if nl <= CAP and (bestload is None or nl < bestload):
            best = i; bestload = nl
    if best < 0:
        best = min(range(K), key=lambda i: loads[i])
    groups[best].extend(sorted(S))
    loads[best] += len(S)
    assigned.update(S)
for m in sorted(allset - assigned):
    i = min(range(K), key=lambda i: loads[i])
    groups[i].append(m)
    loads[i] += 1
    assigned.add(m)
if assigned != allset:
    sys.stderr.write('PCHK-UNION-BROKEN: 并集覆盖断言红 assigned=%d allset=%d\n' % (len(assigned), len(allset)))
    sys.exit(2)
for gi, g in enumerate(groups):
    uni = set()
    for m in g:
        uni |= clmemo[m]
    sys.stderr.write('PCHK-PACK: group=%d listed=%d closure_union=%d argv_chars=%d\n'
                     % (gi + 1, len(g), len(uni), sum(len(m) + 1 for m in g)))
for g in groups:
    print('\x1f'.join(sorted(g)))
PYEOF
[ $? -eq 0 ] || { echo "PCHK-PACK-FAIL: 装箱断言红（见上方 stderr 诊断）——fail-loud"; exit 2; }
[ -s "$WORK/groups.txt" ] || { echo "PCHK-NO-GROUPS: 分组输出 0 字节（python 崩或空输入）——fail-loud"; exit 2; }

# ③ K 路并行（组数=并行度）
i=0
while IFS= read -r grp; do
  [ -n "$grp" ] || continue
  mods=$(printf '%s' "$grp" | tr '\037' ' ')
  nm=$(printf '%s' "$mods" | wc -w | tr -d ' ')
  echo "PCHK group $((i+1)): $nm modules"
  if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then i=$((i+1)); continue; fi
  ( "$K" -o -Q . "" $mods > "/tmp/_pchk_g$i.log" 2>&1; echo $? > "/tmp/_pchk_g$i.rc" ) &
  i=$((i+1))
done < "$WORK/groups.txt"
NGRP=$i
[ "$NGRP" -gt 0 ] || { echo "PCHK-NO-LANES: 零可用组——fail-loud"; exit 2; }
if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then echo "PCHK_PACK_ONLY: $NGRP groups packed — dry exit 0"; exit 0; fi
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
