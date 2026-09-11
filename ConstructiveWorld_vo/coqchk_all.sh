#!/bin/bash
# coqchk_all.sh — 全树内核认证（共享闭包版：一次传全部模块，依赖只验一遍）
# 旧版逐件循环为 O(n²)（每件重验全部依赖闭包，99 件 = 3-8h）；本版一次传入 ≈ 单次全树。
cd "$(dirname "$0")"
K="${COQCHK:-coqchk}"
# 认证面=登记库件；`_` 前缀探针/暂态 .vo 不入认证闭包（CI#46 教训：
# 杂散 _z3_g3.vo 陈旧 digest 撕裂全树认证——Inconsistent assumptions over UpReqAlign4）
MODULES=$(for f in *.vo; do case "$f" in _*) continue;; esac; basename "$f" .vo; done | tr '\n' ' ')
[ -n "$MODULES" ] || { echo "no .vo found"; exit 1; }
echo "coqchk batch: $(echo $MODULES | wc -w) modules (shared closure)"
"$K" -Q . "" $MODULES > "_chk_all.log" 2>&1
e=$?
tail -5 "_chk_all.log"
if [ $e -eq 0 ] && grep -q "Modules were successfully checked" "_chk_all.log"; then
  echo "COQCHK_ALL_PASS"
  exit 0
fi
echo "COQCHK_FAIL (see _chk_all.log)"
exit 1
