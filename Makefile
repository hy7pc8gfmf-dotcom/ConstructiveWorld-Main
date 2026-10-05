# ConstructiveWorld-Main — 构建入口 Makefile（信任缓存增量版；历史合并版配方保留退役）
#
# 用法：
#   make modules   # 按 scripts/order.txt 拓扑序编译在册模块（当前 531 个，.vo 已存在则跳过）
#   make check     # 全树 coqchk 内核复验（共享闭包一次传入；当前认证规模 554 模块，CI run #178）
#   make merged    # （已退役）220 版历史单文件合并编译配方，仅存 releases/ 供历史复现（见 README 附录）；
#                  #  非现役认证面，日常验证请用 modules + check
#   make clean     # 清产物（保留 .v）
#
# 变量覆盖（Windows 本地示例）：
#   make COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe" COQCHK="C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe"

COQC   ?= coqc
COQCHK ?= coqchk
ORDER  := scripts/order.txt
VODIR  := ConstructiveWorld_vo

modules:
	cd $(VODIR) && bash build.sh

check:
	cd $(VODIR) && bash coqchk_all.sh

# （已退役）220 版历史合并配方：目标文件为 releases/CW_ConstructiveWorld_220.v（史料保留）。
# 现役构建与认证面为上方 modules / check 两目标。
merged:
	cd $(VODIR) && $(COQC) -Q . "" CW_ConstructiveWorld_220.v || \
	cd ../releases && $(COQC) -Q . "" CW_ConstructiveWorld_220.v

clean:
	cd $(VODIR) && rm -f *.vo *.vos *.vok *.glob _*.build.log _chk_*.log

.PHONY: modules check merged clean
