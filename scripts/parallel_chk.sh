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

WORK="$PWD/_pchk_tmp_$$"   # 实例唯一＋绝对化（lane cd 进副本后相对 WORK 即失配——att 链实证）
rm -rf "$WORK"; mkdir -p "$WORK"

echo "::group::PCHK 1/4 module list + coverage assertion"
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

echo "::endgroup::"
echo "::group::PCHK 2/4 dependency graph + balanced packing"
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
sys.stdout.reconfigure(newline='\n')  # 20261019 CRLF 定谳：禁 Windows 文本模式把组行写成 \r\n（源侧根治）
for g in groups:
    print('\x1f'.join(sorted(g)))
PYEOF
[ $? -eq 0 ] || { echo "PCHK-PACK-FAIL: 装箱断言红（见上方 stderr 诊断）——fail-loud"; exit 2; }
[ -s "$WORK/groups.txt" ] || { echo "PCHK-NO-GROUPS: 分组输出 0 字节（python 崩或空输入）——fail-loud"; exit 2; }

echo "::endgroup::"
echo "::group::PCHK 3/4 per-lane vo copies + scan-drain"
# ③ K 路并行（组数=并行度）
# ③a Windows 并发共载缺陷对策（20261019 att1-3 三连实证：同树 4 并发 coqchk 全灭——
# mmap 共载竞态两型：CI 面 Cannot find library（文件在盘魔数正·单发复现 CLEAN）/本地面
# intern 中静默 rc1；顺序单发/全组单发皆 CLEAN·mac POSIX 侧同版无恙）——CHK_TREE_COPY=1
# 时每 lane 先复制独立 vo 副本再验（断共享·保并行度；副本目录 _pchk_tmp/vo_gN 下划线守卫域）。
LANE_ARR=()
if [ "${CHK_TREE_COPY:-0}" = "1" ]; then
  echo "PCHK: materializing per-lane vo copies (Windows concurrent-mmap defect countermeasure)"
  for c in $(seq 0 $((JOBS-1))); do
    rm -rf "$WORK/vo_g$c"; mkdir -p "$WORK/vo_g$c"
    cp ./*.vo "$WORK/vo_g$c"/ 2>/dev/null || true
    if [ -d Local ]; then mkdir -p "$WORK/vo_g$c/Local"; cp Local/*.vo "$WORK/vo_g$c/Local"/ 2>/dev/null || true; fi
    LANE_ARR+=("$WORK/vo_g$c")
  done
fi
# ③c 扫描疏引流（20261019 万相归一定谳：全部并发失败=coqchk 开「刚写完的 .vo」撞
# Defender 排他扫描窗——build 后 23 fresh/copies 1700 fresh 两源同病·顺序单发恒过=窗已过）。
# lane 发射前对全部待开文件做读开放直至洁净（Defender 按文件+版本缓存扫描结果·读尽即排空）。
if [ "${CHK_TREE_COPY:-0}" = "1" ] && [ -n "${LANE_ARR[*]:-}" ]; then
  for pass in 1 2 3 4; do
    miss=0
    for d in "${LANE_ARR[@]}"; do
      while IFS= read -r f; do
        head -c 16 "$f" >/dev/null 2>&1 || { miss=$((miss+1)); sleep 1; }
      done < <(find "$d" -name '*.vo' 2>/dev/null)
    done
    echo "PCHK scan-drain pass=$pass pending=$miss"
    [ "$miss" -eq 0 ] && break
  done
fi
echo "::endgroup::"
echo "::group::PCHK 4/4 K-lane certification"
i=0
while IFS= read -r grp; do
  [ -n "$grp" ] || continue
  # 20261019 CRLF 定谳：groups.txt 行尾 \r 黏在末位件名上→coqchk Cannot find library(名\r)
  # （Windows Python 文本模式写 \n→\r\n·mac POSIX 无此翻译故同版无恙·CI att1-3 三连红恒为各
  #  lane 末位参即铁证）——此处连同 \037 一并翻译为空格，消费侧兜底。
  mods=$(printf '%s' "$grp" | tr '\037\r' '  ')
  nm=$(printf '%s' "$mods" | wc -w | tr -d ' ')
  echo "PCHK group $((i+1)): $nm modules"
  if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then i=$((i+1)); continue; fi
  ldir="${LANE_ARR[$i]:-}"
  # 20261019 并发失效对策三件：错峰启动（45s/lane——通道建立窗错开）＋实例域用户隔离
  # （USER/USERNAME 进 lane 环境——通道名可能含用户域）＋独立副本（CHK_TREE_COPY）。
  # 实测组合：四 lane 共存全程推进（旧配置秒死窗不复现）。
  if [ -n "$ldir" ] && [ -d "$ldir" ]; then
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; cd "$ldir" && "$K" -o -Q . "" $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  else
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; "$K" -o -Q . "" $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  fi
  i=$((i+1))
done < "$WORK/groups.txt"
echo "::endgroup::"
NGRP=$i
[ "$NGRP" -gt 0 ] || { echo "PCHK-NO-LANES: 零可用组——fail-loud"; exit 2; }
if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then echo "PCHK_PACK_ONLY: $NGRP groups packed — dry exit 0"; exit 0; fi

# ③b 活性仪表盘（20261019 假死定谳反制·用户令「环节显式表达」）：lane 静默期每
# PCHK_MON_SEC（默认30）s 向控制台打单行心跳——elapsed／各 lane checking 行数＋末模块／
# rc 收割数；lane 完结即时播报里程碑。只写控制台，不进 lane 日志与合并日志（gate2
# 口径零污染）。mac bash 3.2 兼容（纯 POSIX 形）。宕机/卡死时刻可由心跳断流精确到 30s。
echo "[PCHK-MON] $NGRP lanes launched — heartbeat every ${PCHK_MON_SEC:-30}s (console only; lane logs = WORK/g*.log)"
MON_T0=$(date +%s); MON_PREV=0
(
  while :; do
    sleep "${PCHK_MON_SEC:-30}"
    el=$(( $(date +%s) - MON_T0 ))
    rcdone=0; line=""
    for k in $(seq 0 $((NGRP-1))); do
      if [ -f "$WORK/g$k.rc" ]; then
        rcdone=$((rcdone+1))
        line="$line g$k=DONE(rc=$(cat "$WORK/g$k.rc"))"
      else
        lc=$(grep -c 'checking' "$WORK/g$k.log" 2>/dev/null)
        lc=${lc:-0}
        lm=$(tail -n 1 "$WORK/g$k.log" 2>/dev/null | sed 's/.*checking cst://;s/^[[:space:]]*//' | cut -c1-42)
        line="$line g$k:${lc}L:${lm}"
      fi
    done
    echo "[PCHK-MON t=${el}s]${line} (done=${rcdone}/${NGRP})"
    if [ "$rcdone" -gt "$MON_PREV" ]; then
      echo "[PCHK-MON] milestone: ${rcdone}/${NGRP} lanes finished at t=${el}s"
      MON_PREV=$rcdone
    fi
  done
) &
MON_PID=$!
wait
kill "$MON_PID" 2>/dev/null || true
wait "$MON_PID" 2>/dev/null || true

# ③d lane 单次重试（扫描窗残余/瞬态自愈——真伤恒红 fail-loud 不变）
retry_done=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -ne 0 ] && [ "$retry_done" -eq 0 ]; then
    retry_done=1
    echo "PCHK retry: group $((j+1)) rc=$rc — single retry after 60s settle"
    sleep 60
    ldir="${LANE_ARR[$j]:-}"
    mods=$(sed -n "$((j+1))p" "$WORK/groups.txt" | tr '\037\r' '  ')
    if [ -n "$ldir" ] && [ -d "$ldir" ]; then
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; cd "$ldir" && "$K" -o -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    else
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; "$K" -o -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    fi
  fi
done
wait

# ④ 日志按组序合并（gate2 兼容）+ fail-loud 终审
: > _chk_all.log
rc_total=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -eq 0 ]; then
    rc_total=$rc_total
  else
    rc_total=1
    # lane 失败直进 run 摘要注记（20261019 假死反制：失败面无需开日志即见）
    echo "::error::PCHK lane g$j FAILED (rc=$rc) — last module: $(tail -n 1 "$WORK/g$j.log" 2>/dev/null | sed 's/.*checking cst://;s/^[[:space:]]*//' | cut -c1-60)"
  fi
  cat "$WORK/g$j.log" >> _chk_all.log 2>/dev/null || rc_total=1
done
grep -q "Modules were successfully checked" _chk_all.log || rc_total=1
tail -5 _chk_all.log
# ④a Step Summary 终表（run 摘要页直读每 lane 状态——环节显式表达收口）
if [ -n "${GITHUB_STEP_SUMMARY:-}" ] && [ -w "$GITHUB_STEP_SUMMARY" ]; then
  {
    echo "### coqchk certification (parallel K=$NGRP, $NMOD modules listed)"
    echo ""
    echo "| lane | status | checking lines |"
    echo "|---|---|---|"
    for j in $(seq 0 $((NGRP-1))); do
      rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
      lc=$(grep -c 'checking' "$WORK/g$j.log" 2>/dev/null); lc=${lc:-0}
      if [ "$rc" -eq 0 ]; then st="PASS"; else st="FAIL(rc=$rc)"; fi
      echo "| g$j | $st | $lc |"
    done
  } >> "$GITHUB_STEP_SUMMARY"
fi
if [ "$rc_total" -eq 0 ]; then
  echo "COQCHK_ALL_PASS (parallel, $NGRP groups, $NMOD modules)"
  exit 0
fi
echo "COQCHK_FAIL (parallel; merged=_chk_all.log, per-group=$WORK/g*.log)"
exit 1
