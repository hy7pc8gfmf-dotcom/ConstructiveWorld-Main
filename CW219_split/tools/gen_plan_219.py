# -*- coding: utf-8 -*-
"""219 基座拆分规划文档生成器（Phase 1 落盘）。"""
import sys, io, json
sys.path.insert(0, 'D:/ComplexAnalysis/ConstructiveWorld-Main/CW219_split/tools')
from shards_def import SHARDS
src = r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo\CW_ConstructiveWorld_219.v"
text = io.open(src, 'r', encoding='utf-8').read()
lines = text.split('\n')
units = json.load(open(r'D:\ComplexAnalysis\ConstructiveWorld-Main\CW219_split\tools\units219.json'))

DESC = {
 "S01_BaseRing": "基础接口层：RealInterface/RealInterfaceEnhanced/DecidableOrder 类、环论引理、Hilbert、命题收敛核心（PCC）、语言模型/热力学实例",
 "S02_CauchyComplete": "柯西实数：乘法、完备性骨架、完备性战役（real_cauchy_complete 零 Variable 里程碑）、双柯西反例",
 "S03_QExp": "Q-Exp 层：QExpPartial/QExpEOSplit（有理数指数偏函数与 EO 拆分）、配对战役（备份 92 合入）",
 "S04_RealExpLogConv": "Real ExpLog 接口、收敛定理/柯西收敛、KeyProofs、小节群（损失聚合/梯度下降/吸引子/Boltzmann）、自由能最小化",
 "S05_AlignmentGRPO": "对齐主战场：Alignment(4.5k 行)/U2FixedPoint/GRPO/自然梯度/涨落耗散/七条预测/时间之箭",
 "S06_DiffSamplingGibbs": "可微性：GramSchmidt/ProbDist/KL/DifferentiableLemmas/熵可微/LogDiffPhase3/多元可微/第二定律 + AttentionGibbsBridge + MinP/TopP 采样",
 "S07_RealSetoidExpLog": "RealSetoid 核心/RealSetoid 模块、ExpPlus 两阶段、LogStage3（内嵌 DpoPrelude/LogMono/EnhancedMain/LogLinearMain 四嵌套 Section）、FullInstance/EnhancedSetoidMain/RealInterfaceEnhancedMod",
 "S08_RealMainlineDPO": "Real 主役群：OppMult/GibbsCore/RealListSum/DPO 三部曲/RealGrpo/RealAttn/RealMinP/RealTopK/RealPPO/RealRLHF + LogDiffPhase4（内嵌 Phase2/2b）",
 "S09_EntropyReal": "熵实数层：EntropyDiffReal(4.6k)/RealGapOne/RealKappa/RealKappaSignReal/ExpLogGroupIso/ExpInequalities",
 "S10_KVQuantTrig": "KV 量化主件 RealKVQuantMain + 顶层巨块（DPO 损失凸性、cauchy_real_sin/cos 三角战役）+ AttentionGibbsBridgeSetoid",
 "S11_TP3B5": "T-π3(b5 系)前段：N10Channel/A3HscToF1 + Q 层 sin-cos-arctan-π 引擎巨块(5.9k) + B5A_Ode/B5A_Item1/B5bEndpointBridge/B5B_Endpoint/B5A_Item1B",
 "S12_B5RecycleSF": "迭代 212 批量回收（b5 item1c 闭式等，8.7k 顶层块）+ SF 系列 18 个 Section（SFSetLayerQ..SFBiasBlock）",
 "S13_NLiveAudit": "N 系（Symplectic/LAC/Bipolar/TransDim/Branch）+ LCAudit + KLProjection/AlgHelpers/UContraction/BoundedSoftmax/SqrtWitnessGeneral/AttnHardLimit",
 "S14_B5BatchBlock": "迭代 212-215 b5 批量回收顶层巨块（b5c/b5d/b5dL/b5i 前缀，14.3k 行）——全文件最大单块",
 "S15_TailFEPUp": "尾部：FEPAttention/RowView/PPOClipDecomp + 顶层 KL 界块 + UpGRPO219（GRPONoDup/RealGrpoSigma）/UpExtras219（FEPLogZ/GRPOCounterEx/RealVarNonNeg）",
}
KEYTHM = {
 "S01_BaseRing": "RealInterface/RealInterfaceEnhanced/DecidableOrder（Class 全集）、plus_inv_unique/opp_plus 等环论引理、orthogonal_decomposition_exists、NatLe_drop/lift、boltzmann_prob_pos、prediction_fluctuation_scale",
 "S02_CauchyComplete": "real_lim_unique、real_cauchy_complete（零 Variable）、real_lim_plus/scal/mult、real_square_not_negative、step_not_unif_pointwise（构造性反例）",
 "S03_QExp": "q_exp_partial 闭式族（全 Lemma 无独立 Theorem：q_pow_diff_bound 引擎族）、配对战役全绿块",
 "S04_RealExpLogConv": "real_exp/log 接口桥、收敛定理族（ConvergenceTheorem/ConvergenceCauchy）、entropy_gradient_strict_mono、gradient_step_recurrence、FreeEnergyMinimization 主件",
 "S05_AlignmentGRPO": "pi_star_normalized、rlhf_optimal(_unique)、dpo_optimal、ppo_conservative、align_objective_advantage_decomp",
 "S06_DiffSamplingGibbs": "gram_schmidt_step/pair、kl_nonneg、kl_zero_iff_eq、differentiable_plus/mult/compose、minp_markov_kernel_normalized（MinP）、top_p 采样主件、AttentionGibbsBridge 全套",
 "S07_RealSetoidExpLog": "RealSetoid.real_le_id_l 等 setoid 环序、Real_RealInterfaceSetoidCore/Real_RealInterfaceSetoid/RealEnhancedReal 实例、ExpPlus/LogStage3 闭式主件",
 "S08_RealMainlineDPO": "real_dpo_loss_pi_star_bounded_both、real_dpo_reward_recovers_up_to_baseline、real_grpo_advantage_zero_mean、real_attention_is_gibbs、real_minp_markov_kernel_normalized、LogDiffPhase4 全套",
 "S09_EntropyReal": "real_gradient_zero_entropy_max、real_gradient_step_contraction、real_grad_decay_positive_iter、ExpLogGroupIso 主件、RealKappa 界族",
 "S10_KVQuantTrig": "attention_is_gibbs_setoid、steady_state_boltzmann_attn_setoid、real_db_breaking_bound_eps、KV 量化战役 432 定理块、cauchy_real_sin/cos 加法公式",
 "S11_TP3B5": "a3_closure_f1、B5A_Ode/B5A_Item1/B5B_Endpoint 主件（arctan/ODE/端点桥）、Q 层 sin-cos 部分函数引擎",
 "S12_B5RecycleSF": "b5a_sin_atan_diff_closed_r、SF 系列 113 Theorem（sf_q_sq_ge_0T、sf_pipe_den_pos 等）",
 "S13_NLiveAudit": "rot_preserves_symp、lac_lookup/translate、KLProjection/UContraction/BoundedSoftmax 主件、AttnHardLimit 主件",
 "S14_B5BatchBlock": "b5d1_b3rr_atan_deriv_lin 及 b5c/b5d/b5dL/b5i 批量回收族（286 定理/引理，全 Lemma 形态）",
 "S15_TailFEPUp": "attention_minimizes_free_energy_unique、ppo_clipped_improvement、real_step_kl_eta_bound_eps、GRPONoDup/RealGrpoSigma/RealVarNonNeg（Var>=0 收官）",
}

def secs_in(a, b):
    return [(s, k, nm.rstrip('.')) for (s, e, k, nm) in units if a <= s <= b]

H = []
A = H.append
A("# 219 基座拆分规划（2026-09-08）")
A("")
A("> 席位：219 基座拆分规划施工席（规划+分阶段施工一体）")
A("> 目标：把 114,222 行单文件基座拆为可独立编译的分片模块树，使基座获得模块化信任缓存（改哪片编哪片，坏哪片锁哪片）。")
A("> 红线：纯切割——分片内容 = 基座原文连续行区间，首部补机械生成的头部（Require/状态重放），零内容改写、零重排；基座本体 `ConstructiveWorld_vo/CW_ConstructiveWorld_219.v/.vo` 一字不动。")
A("")
A("## 0. 底料与全量结构扫描")
A("")
A("- 底料：`docs/219结构地图-20260908.md`（148 个 Section/Module 开边界）")
A("- 本次全量扫描补充：`^End` 共 148 处，与开边界平衡（嵌套深度终值 0）。")
A("- **嵌套修正**：结构地图的 148 边界中有 21 个实为嵌套边界（不可作为切割点），例如：")
A("  - `Module PropositionConvergenceCore`(L1452) 内嵌 `Section PCC`(L1454)；同型：LMI(L1775/1777)、SLM(L2019/2020)、ThermodynamicsInstance(L2939/2940)")
A("  - `Section LogStage3`(L34872) 内嵌 `DpoPreludeMain/DpoPrelude`(L38524/38525)、`LogMono`(L38685)、`EnhancedMain`(L39194)、`LogLinearMain`(L40656)")
A("  - `Section LogDiffPhase4`(L43939) 内嵌 `LogDiffPhase2`(L43940)、`LogDiffPhase2b`(L44102)")
A("  - `Module UpGRPO219`(L113511) 内嵌 `GRPONoDup`(L113533)、`RealGrpoSigma`(L113857)；`Module UpExtras219`(L113991) 内嵌至 EOF")
A("- 顶层（深度 0）单元全集：**127 个**（Section/Module），另加前奏 L1-345 与 124 段顶层散装内容（战役回收块）。")
A("- **散装顶层巨块**（地图未标出、本扫描发现，均已按连续区间归片）：")
A("  - L4381-6982（2.6k）：完备性战役（双柯西反例 + Bishop 正则化）→ S02")
A("  - L11863-13800（1.9k）：Q-Exp 配对战役 → S03")
A("  - L54966-66136（11.2k）：DPO 损失凸性 + cauchy_real_sin/cos 三角函数战役 → S10")
A("  - L67995-73922（5.9k）：Q 层 sin-cos-arctan-π 引擎 → S11")
A("  - L79153-87819（8.7k）：迭代 212 批量回收（b5 item1c 等）→ S12")
A("  - L97867-112163（14.3k）：迭代 212-215 b5 批量回收巨块 → S14（全文件最大单块）")
A("")
A("## 1. 切割合法性判据（Coq 硬约束）")
A("")
A("1. **只在深度 0 切**：每个分片 = 顶层单元（或其散装块）的整数倍集合，绝不切入任何 Section/Module 内部。Section 变量在 `End` 处放电，原文中后段对前段定理的引用本就是放电后形态，故 Require 后逐字可用。")
A("2. **声明先于使用**：原文件整体线性编译通过，故每个标识符在引用点之前已定义；分片保持行序，依赖图必为线性链 S01→S02→…→S15（grep 验证法见 §4）。")
A("3. **状态重放**（普通 `Import`/`Opaque`/选项不跨 Require 传播，头部机械重放，属头部补齐而非内容改写）：")
A("   - 所有分片头部：外部 Require 块（原文 L54-58 的 QArith/List/Bool/Arith/Setoid/Morphisms/Lia/Qminmax）+ `Import ListNotations.`")
A("   - S05 起头部：`Import PropositionConvergenceCore.`（复现原文 L15519 的普通 Import 语义）")
A("   - S08 起头部：`Opaque Qred.`（复现原文 L33494/L46819 的透明度状态，该状态不跨文件传播）")
A("   - S13 起头部：`From Stdlib Require Import Psatz.`（复现原文 L78208）")
A("   - S15 头部：`From Stdlib Require Import ZArith.Znat.`（复现原文 L95607）")
A("4. **纯切割可机械验证**：分片文件去掉头部 N 行（N 按片记录于头部注释）后按序拼接 ≡ 原文逐字节（含 CRLF 行尾）；验收脚本 `tools/verify_split.py`。")
A("")
A("## 2. 分片总表（15 片，8-15 上限内取满粒度）")
A("")
A("| # | 分片 | 行区间 | 行数 | 依赖 |")
A("|---|------|--------|------|------|")
for i, (name, a, b, d) in enumerate(SHARDS):
    dep = "外部 Stdlib" if i == 0 else "S01..S%02d" % i
    A("| %d | `%s` | L%d-L%d | %s | %s |" % (i+1, name, a, b, format(b-a+1, ','), dep))
A("| 合计 | 15 片 | L1-L114222 | 114,222 | 线性链 |")
A("")
A("## 3. 各分片详情（Section 清单 / 关键暴露 / 依赖）")
for i, (name, a, b, d) in enumerate(SHARDS):
    A("")
    A("### %d. %s（L%d-L%d，%s 行）" % (i+1, name, a, b, format(b-a+1, ',')))
    A("- **知识域**：" + DESC[name])
    secs = secs_in(a, b)
    A("- **Section/Module 清单**（%d 个顶层单元）：" % len(secs))
    for s, k, nm in secs:
        A("  - L%d %s %s" % (s, k, nm))
    A("- **对外暴露关键定理**：" + KEYTHM[name])
    dep = "仅外部 Stdlib" if i == 0 else "S01..S%02d 全部前序（线性链，声明先于使用）" % i
    A("- **对前序依赖**：" + dep)
A("")
A("## 4. 依赖序 grep 验证法")
A("")
A("- 对每片 P 声明的顶层标识符（`Definition/Lemma/Theorem/Inductive/Class/Record/Module/Fixpoint/Instance/Ltac` 后首词），`grep -n '^<名称>'` 原文确认定义行号 < 分片起始行 ⟹ 落于某前序分片或本片更早位置。")
A("- 线性链性质由原文可编译性保证：任何违规在原文中即为未定义错误。编译即最终验证（Phase 2 逐片 coqc，-async-proofs off）。")
A("")
A("## 5. Phase 2 施工规约")
A("")
A("- 产物目录：`ConstructiveWorld-Main/CW219_split/`（新建，不触碰 ConstructiveWorld_Live / ConstructiveWorld_vo / releases / docs 的 analysis 域）")
A("- 文件名：`S01_BaseRing.v` … `S15_TailFEPUp.v`（扁平命名空间，`-Q CW219_split \"\"`）")
A("- 编译器：`C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe`（Rocq 9.1.0，与基座 .vo 同源）")
A("- 命令模板（大分片一律 `-async-proofs off`，防 -vos 确定性冻结，见经验卡 E-STAGING-WangWW-runcoqc泛化 终版机制节）：")
A("  ```")
A("  cd ConstructiveWorld-Main")
A("  C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe -async-proofs off -Q CW219_split \"\" CW219_split/S01_BaseRing.v")
A("  ```")
A("- 失败处置：记录错误+定位词 → 微调切割点重试；同片 3 次不过标记 BLOCKED 继续后续片（后续片因缺依赖连带 BLOCKED，如实记录）。")
A("- 交付：全部 .v+.vo、BLOCKED 清单（含精确错误头）、经验卡 `E-STAGING-CW219Split-<slug>.md` 回填索引。")
A("")
A("## 6. 与 148 边界地图的偏差说明")
A("")
A("- 地图 148 边界 = 127 顶层开边界 + 21 嵌套边界；嵌套者不单独成片，随其宿主单元归属（逐片清单见 §3，已全量列出）。")
A("- 地图未含 `^End` 行与 124 段顶层散装块；本规划以全量深度扫描补齐，切割点全集 = 深度 0 的行。")
A("- 分片粒度按知识域聚簇为 15 片，满足 8-15 要求；S01/S02 域相邻但体量小（合计 3,071 行），保持 2 片以获得更细的锁片粒度。")

out = r"D:\ComplexAnalysis\ConstructiveWorld-Main\docs\219基座拆分规划-20260908.md"
io.open(out, 'w', encoding='utf-8', newline='\n').write('\n'.join(H) + '\n')
print("written:", out, len(H), "lines")
