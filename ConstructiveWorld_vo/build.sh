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
  "$C" -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
  e=$?
  echo "$f EXIT=$e"
  if [ $e -ne 0 ]; then fail=1; tail -6 "_${f%.v}.build.log"; fi
done < <(grep '\.v$' _CoqProject)
exit $fail
