# Live_X 命名规范（S/G 双系 + 旧名壳）

- **S 系** `S<NN>_<Theme>`：219 大库拆分组（S01–S15，收录自 _CW219_split 模式）。
- **G 系** `G<NN>_<Theme>`：小件有限合并组（合并判据：同主题 + <60KB + 低被依赖 + 碰撞预检通过）。
- **独立件**：枢纽件（被依赖≥3，如 UpReqAlgebra/UpRealLeB/UpReqDist）与中大型件保持原名。
- **旧名已消融（无壳）**：G 组成员旧文件名不再存在；全库对其 `Require Import 旧名` 已由构建脚本统一改写为 `Require Import G<NN>_<Theme>`。
- **CW_ConstructiveWorld_219.v**：219 壳 → S01–S15 全链（下游基座引用唯一聚合点，属合并本体非薄壳）。
- **CW214KL_scan**：已退役——名字级验证 219 ⊇ 214（3,943/3,943 名命中，仅 214 有=0），依赖者 Require 已改挂 `CW_ConstructiveWorld_219`。
- 后缀语义表：`Req`=req setoid 迁移版；`B`=B 形升格（Or 形绕行）；`D`=放电件；`_P2`=第二阶段；`M3`=M3 实验。
- 编译序：order.txt（S 系 → 219 壳 → 拓扑序独立件与 G 组）。

## G 组清单
- **G01_CoreMicro**: UpHlogZ + UpExtras + UpFEP + UpLogMono + UpPPO
- **G02_Debt**: UpDebtSqrtAbs + UpDebtDual + UpDebtGibbsT
- **G04_ProjFam**: UpPLA + UpPredRelax + UpProj + UpProjBPC
- **G05_LogSmall**: UpReqLogPrimD + UpReqLogD + UpReqLogLinD
- **G06_BForm**: UpReqPPOB + UpReqSumB + UpReqMinPProjB + UpReqLatticeB
- **G07_KLWall**: UpReqKLCvx + UpReqPowB + UpReqJensen + UpReqKLStrict + UpReqKLEnergy
- **G08_Gibbs**: UpReqHlogZD + UpReqGibbsD + UpReqGibbsE2
- **G09_MiscSmall**: UpReqPCT + UpReqBoltzDirect + UpReqSqPos + UpReqOrderArgmin
- **G10_LoebFam**: UpLoeb + UpLoebD2 + UpRefuted + UpQKBound
- **G11_IDLFam**: UpCLQuery + UpIDL
- **G12_ZPosFam**: UpReqZPosD + UpReqZPosI + UpReqZPosI2 + UpReqZAuto + UpReqZPosFinal
- **G13_EvictFam**: UpEvictId + UpEvictIdReq