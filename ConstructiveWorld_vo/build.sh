#!/bin/bash
# ConstructiveWorld-Main 增量构建：.vo 比 .v 新则跳过（指纹信任缓存语义）
cd "$(dirname "$0")"
C="${COQC:-coqc}"
fail=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  if [ -f "$v" ] && [ "$v" -nt "$f" ]; then
    echo "$f SKIP(vo 新于源)"
    continue
  fi
  # -native-compiler no：规避本机 Rocq 9.0 触发 coqnative 子进程挂死（E-STAGING-WangWW-native 卡）。
  # 仅影响运行时 Compute 原生加速，不改变逻辑 digest，coqchk 认证不受影响。
  "$C" -native-compiler no -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
  e=$?
  echo "$f EXIT=$e"
  if [ $e -ne 0 ]; then fail=1; tail -6 "_${f%.v}.build.log"; fi
done < <(tr -d '\r' < order.txt | grep '\.v$')
exit $fail
