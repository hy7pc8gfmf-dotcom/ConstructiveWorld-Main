#!/bin/bash
# repair_tear.sh — digest 撕裂自愈（E-STAGING-LC 处方脚本化）
# 判据：消费方 .vo mtime < 其 Require 依赖 .vo mtime ⟹ 撕裂，删之交 build.sh 重编。
# 坑位遵守：依赖名提取用字面 grep（本环境 awk 字符类静默零输出）；From X Require 行天然兼容。
cd "$(dirname "$0")"
n=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  [ -f "$v" ] || continue
  for dep in $(grep -oE 'Require[[:space:]]+(Import|Export)?[[:space:]]*[A-Za-z0-9_ ]+' "$f" \
      | sed 's/^Require[[:space:]]*//;s/^Import[[:space:]]*//;s/^Export[[:space:]]*//' \
      | tr ' ' '\n' | grep -E '^[A-Za-z0-9_]+$' | sort -u); do
    d="$dep.vo"
    if [ -f "$d" ] && [ "$d" -nt "$v" ]; then
      echo "TEAR: $v older than $d -> removed for rebuild"
      rm -f "$v"; n=$((n+1)); break
    fi
  done
done < <(grep '\.v$' _CoqProject)
echo "repair_tear: $n torn .vo removed"
exit 0
