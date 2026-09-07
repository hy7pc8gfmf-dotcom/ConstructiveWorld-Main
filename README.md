# ConstructiveWorld220 — 构造世界 220 版模块化代码库

220 版 = 219 基座（信任缓存）+ 28 个独立模块（本工作流 2026-09-07/08 交付件）。

## 设计目标（用户规划）
后续开发直接调用本地库 & 云端镜像的**编译产物**实现快速编译与快速锁定问题：
- 每个模块一个 .v + 一个 .vo——**坏哪块，锁哪块**（产物名 = 问题位置）
- 基座 `CW_ConstructiveWorld_219.vo` 走信任缓存，永不重编（6MB 级编译在部分上下文会阻塞）
- `docs/BLOCKERS-220.md` 记录单文件 220 版的全部阻塞点及模块级映射

## 目录
| 路径 | 内容 |
|---|---|
| `ConstructiveWorld_Live/` | 活源码树：基座 .v + 28 模块 .v + _CoqProject + build.sh |
| `ConstructiveWorld_vo/` | 产物树：同上 + 每模块 .vo（基座 .vo = 信任缓存直拷） |
| `releases/` | 单文件全量合并版 CW_ConstructiveWorld_220.v（129K 行） |
| `docs/` | 合并指引、甄别报告、阻塞图谱 |

## 编译
```bash
cd ConstructiveWorld_vo
bash build.sh        # 拓扑序增量编译（.vo 已存在则跳过）
```
全量重编基座（可选，建议在交互终端跑）：`coqc -Q . "" CW_ConstructiveWorld_219.v`

## 模块清单（28，依赖拓扑序）
第 0 层：UpCS UpHlogZ UpDebtSqrtAbs UpDebtDual UpEntropyGain UpSigMigrate UpMinP UpAlignId UpProj UpFirewall UpTempWindow UpKVEv UpAuditBridge UpPredRelax UpPLA UpStepKLM3 UpRecast UpCLQuery UpSLM
第 1 层：UpBudgetReal↑UpHlogZ · UpArchAttn↑BudgetReal · UpConstitution↑BudgetReal · UpProjBPC↑Proj · UpEvictId · UpDebtGibbsT · UpDPOLip
第 2 层：UpDissip↑Constitution · UpStopTime↑BudgetReal+Constitution

已吸收进基座（勿重编）：UpStepKL UpLogMono AttnDoeblin AttnHardLimit218 AttnSqrt UpFEP UpPPO UpGRPO(→UpGRPO219) UpExtras(→UpExtras219)
