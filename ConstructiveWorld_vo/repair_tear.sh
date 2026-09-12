#!/bin/bash
# repair_tear.sh v2 — digest-aware 撕裂自愈（E-STAGING-RT2 升级；接口兼容 v1/9b42d46）
#
# 判据①（v1 保留）：消费方 .vo mtime < 其 Require 依赖 .vo mtime ⟹ 撕裂。
# v1 盲区（P9/HC2 卡实证）：mtime 正常但 .vo 内嵌 digest 断代——上游重编后消费方 mtime
#   被 touch/播种回填，或上游 .vo 缺失待重编（重编后 digest 必变），CI 三轮漏网
#   （UpReqEntropyDeficitTemp 形态）。v2 增补双判据：
# 判据②（结构性断代，零成本）：dep .v 在树而 dep .vo 缺失、消费方 .vo 却在 ⟹ build
#   重编 dep 后 digest 必新 ⟹ 消费方必断代，删。
# 判据③（digest 冒烟，秒级/件）：高嫌疑集（历史 coqchk 撕裂同族=温度/桥接/对齐/Gibbs/
#   TVAbs 族）单件 `coqchk -silent -o`（全闭包；实测捕获 "Inconsistent assumptions"。
#   -norec 在 Rocq 9.0.1 内部崩溃 Invalid_argument，禁用）。输出含撕裂签名 ⟹ 删；
#   EXIT!=0 无签名=工具缺席/环境故障 ⟹ 保守保全（run #53 教训，139 件误删复盘）。
# 伞件白名单（HC2 判别式落地）：源 `grep -cE "^(Definition|Fixpoint|Theorem|Lemma|
#   Corollary|Instance)"`=0 的伞件（如 CW_ConstructiveWorld_219 薄壳：小体积+零 cst
#   属结构必然）标记 UMBRELLA 豁免内容猜疑——删除只认 digest 阳性证据，绝不安尺寸/零
#   cst 单罪定断。
# 级联：本轮已删件的 Require 消费方一并删（重编后 digest 必断代），单轮 build 全愈。
# 坑位遵守（LC/HC2 卡）：依赖名提取用字面 grep（本环境 awk 字符类静默零输出）；
#   _CoqProject 与比对一律 tr -d '\r'（本树实测混合行尾，CRLF 行 v1 静默跳过）。
# 接口（兼容 CI workflow coq.yml build 步）：build 前调用、输出 TEAR 清单、零交互、
#   恒 exit 0。coqchk 取 PATH，缺席兜底 9.0 全路径（run #53 教训）；可 COQCHK=覆盖。
# 环境开关（默认全关，CI 默认行为=删；不设即与 v1 语义兼容）：
#   TRT2_DRYRUN=1    只报告不删（诊断/验收用）
#   TRT2_SUSPECT=RE  覆盖高嫌疑集正则（对 .v 基名整体匹配，-i）
#   COQCHK=路径      覆盖 coqchk 可执行
cd "$(dirname "$0")"
DRYRUN="${TRT2_DRYRUN:-0}"
# RT3 回归修正（E-STAGING-RT3）：默认族名子串匹配 .*族.*。原默认锚定 ^(...)$ 整体匹配
#   使真实族名（UpReqEntropyDeficitTemp/UpReqTVAbsEps 等含族词的基名）零命中，
#   判据③ digest 冒烟在默认 CI 环境沦为死代码（沙箱 TTempFam 实证：纯 digest 撕裂 0 感知）。
SUSPECT="${TRT2_SUSPECT:-.*Temp.*|.*Bridge.*|.*Gibbs.*|.*Align.*|.*TVAbs.*|.*Entropy.*}"
# run #53 教训：自托管 runner 的 bash 无 coqchk 于 PATH——裸 `coqchk` 得 EXIT=127。
COQCHK_BIN="${COQCHK:-$(command -v coqchk 2>/dev/null || echo "C:/Rocq-Platform~9.0~2025.08/bin/coqchk.exe")}"
n=0
declare -A REMOVED
note() { echo "repair_tear: $*"; }
remove_vo() { # $1=.v路径 $2=原因标签
  local v="${1%.v}.vo"
  if [ "$DRYRUN" = "1" ]; then
    echo "TEAR($2): $v -> would be removed for rebuild (dryrun)"
  else
    echo "TEAR($2): $v -> removed for rebuild"
    rm -f "$v"
  fi
  REMOVED["${1%.v}"]=1
  n=$((n+1))
}
while IFS= read -r f; do
  f=$(printf '%s' "$f" | tr -d '\r')
  [ -n "$f" ] || continue
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  [ -f "$v" ] || continue
  base="${f%.v}"
  torn=""
  # ---- 判据②+①：依赖缺失/级联/mtime 倒挂（依赖名提取与 v1 逐字一致）----
  for dep in $(grep -oE 'Require[[:space:]]+(Import|Export)?[[:space:]]*[A-Za-z0-9_ ]+' "$f" \
      | sed 's/^Require[[:space:]]*//;s/^Import[[:space:]]*//;s/^Export[[:space:]]*//' \
      | tr ' ' '\n' | grep -E '^[A-Za-z0-9_]+$' | sort -u); do
    if [ -f "$dep.v" ] && [ ! -f "$dep.vo" ]; then
      torn="dep-missing:$dep"; break
    fi
    if [ -n "${REMOVED[$dep]:-}" ]; then
      torn="cascade:$dep"; break
    fi
    d="$dep.vo"
    if [ -f "$d" ] && [ "$d" -nt "$v" ]; then
      torn="mtime-older-than:$d"; break
    fi
  done
  # ---- 判据③ digest 冒烟（仅高嫌疑集；便宜判据已撕裂则免烟）----
  if [ -z "$torn" ]; then
    bname="$(basename "$base")"
    if printf '%s' "$bname" | grep -qiE "^($SUSPECT)$"; then
      smokelog="$(mktemp)"
      "$COQCHK_BIN" -silent -o -Q . "" "$base" > "$smokelog" 2>&1
      ec=$?
      # run #53 事故修正：删除只认撕裂签名；非零退出但无签名=工具缺席/环境故障，
      # 一律保守保全（旧判据「非零即删」曾把 139 件健康 .vo 全数误删）。
      if grep -qE 'Inconsistent assumptions|Anomaly|Fatal' "$smokelog"; then
        torn="digest-smoke:coqchk EXIT=$ec $(head -c 120 "$smokelog" | tr '\n' ' ')"
      elif [ "$ec" -ne 0 ]; then
        note "digest-smoke SKIP($base): coqchk EXIT=$ec 非撕裂签名，保守保全"
      fi
      rm -f "$smokelog"
    elif [ "$(grep -cE '^(Definition|Fixpoint|Theorem|Lemma|Corollary|Instance)' "$f")" -eq 0 ]; then
      note "UMBRELLA(benign whitelist): $f — 0 source Definitions, exempt from content suspicion"
    fi
  fi
  if [ -n "$torn" ]; then
    remove_vo "$f" "$torn"
  fi
done < <(grep '\.v$' _CoqProject | tr -d '\r')
echo "repair_tear: $n torn .vo removed"
exit 0
