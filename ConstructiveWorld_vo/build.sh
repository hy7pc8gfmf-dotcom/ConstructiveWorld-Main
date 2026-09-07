#!/bin/bash
# ConstructiveWorld220 模块树编译（依赖拓扑序；基座走信任缓存 219.vo）
cd "$(dirname "$0")"
C="${COQC:-coqc}"
fail=0
for f in $(grep -v '^-' _CoqProject | grep '\.v$'); do
  if [ ! -f "${f%.v}.vo" ]; then
    "$C" -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
    e=$?
    echo "$f EXIT=$e"
    [ $e -ne 0 ] && { fail=1; tail -4 "_${f%.v}.build.log"; }
  else
    echo "$f SKIP(vo 已存在)"
  fi
done
exit $fail
