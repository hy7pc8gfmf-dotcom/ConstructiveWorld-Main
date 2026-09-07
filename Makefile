# ConstructiveWorld-Main — 双版本构建 Makefile（模块化信任缓存版 + 合并单文件版）
#
# 用法：
#   make modules   # 按 scripts/order.txt 拓扑序编译 28 模块（.vo 已存在则跳过）
#   make check     # 全树 coqchk 内核独立复验（29 件含基座）
#   make merged    # 合并单文件版全量编译（约 40 分钟；部分后台上下文会冻结，建议交互终端/CI）
#   make clean     # 清产物（保留 .v）
#
# 变量覆盖（Windows 本地示例）：
#   make COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe" COQCHK="C:/Rocq-Platform~9.0~2025.08/bin/coqchk.exe"

COQC   ?= coqc
COQCHK ?= coqchk
ORDER  := scripts/order.txt
VODIR  := ConstructiveWorld_vo

modules:
	cd $(VODIR) && bash build.sh

check:
	cd $(VODIR) && bash coqchk_all.sh

merged:
	cd $(VODIR) && $(COQC) -Q . "" CW_ConstructiveWorld_220.v || \
	cd ../releases && $(COQC) -Q . "" CW_ConstructiveWorld_220.v

clean:
	cd $(VODIR) && rm -f *.vo *.vos *.vok *.glob _*.build.log _chk_*.log

.PHONY: modules check merged clean
