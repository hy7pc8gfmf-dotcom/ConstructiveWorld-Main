#!/bin/bash
# ConstructiveWorld-Main 增量构建：.vo 比 .v 新则跳过（指纹信任缓存语义）
cd "$(dirname "$0")"
C="${COQC:-coqc}"
# SW2 换装（2026-09-15）：机器级【用户环境变量】COQLIB/ROCQLIB 钉在 9.0 lib，
# 会压过 9.1 版 coq_environment.txt → 9.1 coqc 暗载 9.0 stdlib，产物魔数 90001
# 被 9.1 coqchk 拒（bad version，期望 90100）。故随 COQC 路径推导导出，保证 bin/lib 同源
# （E-STAGING-SW2 沙箱实证：COQLIB 同源后 90100 roundtrip，coqchk EXIT=0）。
case "$C" in
  */bin/coqc.exe) export COQLIB ROCQLIB; COQLIB="${C%/coqc.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
  */bin/coqc)     export COQLIB ROCQLIB; COQLIB="${C%/coqc}";     COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
esac
fail=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  if [ -f "$v" ] && [ "$v" -nt "$f" ]; then
    echo "$f SKIP(vo 新于源)"
    continue
  fi
  # -native-compiler no：规避本机 Rocq 9.0 实测 coqnative 子进程挂死（E-STAGING-WangWW-native 卡）；
  # 9.1 换装后沿用保守旗标（PROBE91 全绿实证），不改变逻辑 digest，coqchk 认证不受影响。
  # 仅影响运行时 Compute 原生加速，不改变逻辑 digest，coqchk 认证不受影响。
  "$C" -native-compiler no -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
  e=$?
  echo "$f EXIT=$e"
  if [ $e -ne 0 ]; then fail=1; tail -6 "_${f%.v}.build.log"; fi
done < <(tr -d '\r' < order.txt | sed 's/#.*//' | grep '\.v$')
exit $fail
