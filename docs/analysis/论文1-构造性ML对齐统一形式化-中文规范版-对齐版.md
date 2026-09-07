# 有限状态单步目标理论的构造性机器检查统一：RLHF、DPO、PPO 代理目标与 GRPO 组统计量

**英文标题**：A Constructive Machine-Checked Library for Finite-State RLHF/DPO/PPO/GRPO Objective Theory

**目标会议/期刊**：CPP / ITP / Journal of Formalized Reasoning

---

## 摘要（Abstract）

本工作报告了据我们所知首个（范围界定见 §2.3：纯构造性 Coq 单一文件、零 Axiom、Set 层可提取 OCaml，且已系统排除 Isabelle/AFP 与 Lean/mathlib 中的相邻工作）针对 RLHF、DPO、PPO、GRPO 四族对齐算法目标理论的统一机器检查形式化；其范围限定于**有限离散状态空间上的单步目标理论**——全状态精确求和，不含采样与 minibatch 期望、轨迹级 MDP、神经网络参数化与连续动作空间。整个形式化在纯构造性逻辑下完成：零 Axiom、零 Admitted，仅依赖 Coq 标准库。我们证明了 RLHF 的 KL 正则化最优策略闭式解及其唯一性，DPO 隐式奖励恢复定理族，PPO 裁剪代理目标的保守性（静态性质）与未裁剪代理目标的单调改进条件，以及 GRPO 组相对优势的零均值与中心二阶矩恒等式。所有定理共享同一套基于 Cauchy 实数、Boltzmann 分布、自由能与 KL 散度的构造性基座。**所有定理均在抽象接口 `RealInterfaceEnhanced` 上陈述并证明。该接口的 setoid 对应物已由具体柯西实数 `Real` 实例化——`Real_RealInterfaceSetoid`（L39407）与 `RealEnhancedReal`（L41115），且全部字段均已实值化。抽象定理签名向 setoid 实例的整体迁移尚未完成（即"正在进行的工作"）；当前最强表述为：抽象接口定理 + setoid 接口实例 + 部分 Real 层逐 eps 复刻。部分核心定理（清单见 §1.2 贡献 7）另有 Real 层逐 eps 版本直接证明（见 §9.1.1）。** 本文给出了核心定理陈述、证明策略概述、与现有形式化工作的对比，并明确声明了当前形式化的边界与前提。

> 【对齐标注 2026-09-08 · 220 基态】本文全部定理引用与行号以 219 单文件为锚（SHA-1 7BBE42EA83D178901C94FA13FB18E0A3B975D09A，114,222 行，实测与本地逐字一致）；自 220 起该内容的维护形态为模块化树（基座信任缓存 + 28 个独立模块，逐模块 .vo 内核校验），行号锚零平移。逐处口径见各节【对齐标注】；修订依据清单见 `docs/analysis/论文1-220基态-论文代码对应矩阵.md`。

---

**Abstract (English)**

This work reports what we believe to be the first—within the scope delimited in §2.3, i.e. an axiom-free, Set-level, OCaml-extractable, single-file Coq development, after systematically reviewing and excluding adjacent Isabelle/AFP and Lean/mathlib work—unified machine-checked formalization of objective theory for the alignment algorithms RLHF, DPO, PPO, and GRPO, in the ConstructiveWorld library. Its scope is deliberately narrow: single-step objective theory over a finite discrete state space with exact full-state sums—no sampling or minibatch expectations, no trajectory-level MDPs, no neural parameterization, and no continuous action spaces. The entire formalization is carried out constructively: zero Axioms, zero Admitted proof obligations, and relying only on the Coq standard library. We prove the closed-form optimal policy of KL-regularized RLHF and its uniqueness, the DPO implicit-reward recovery theorem family, the static conservativeness of the PPO clipped surrogate objective together with monotonic-improvement conditions for the unclipped surrogate, and the zero-mean and centered-second-moment identity of group relative advantages in GRPO. All theorems share a single constructive base built from Cauchy reals, Boltzmann distributions, free energy, and KL divergence. **All theorems are stated and proved at the abstract `RealInterfaceEnhanced` level. The setoid counterpart of this interface is instantiated on the concrete Cauchy reals (`Real_RealInterfaceSetoid`, L39407; `RealEnhancedReal`, L41115), with all fields concretely instantiated. The full migration of the abstract-layer theorem signatures to the setoid counterparts is ongoing work (the "work in progress" phrasing); the strongest current statement is: abstract interface theorems + setoid interface instances + pointwise-epsilon re-proofs of part of the Real layer. A subset of the core theorems (as listed in §1.2, contribution 7) are additionally proved directly at the `Real` layer in pointwise-epsilon form (see §9.1.1).** We present the core theorem statements, outline the proof strategies, compare with existing formalization work, and explicitly declare the current boundaries and assumptions.

---

## 1 引言

### 1.1 动机

RLHF（Reinforcement Learning from Human Feedback）、DPO（Direct Preference Optimization）、PPO（Proximal Policy Optimization）和 GRPO（Group Relative Policy Optimization）构成了当前大语言模型对齐的主流算法族。它们的优化理论基础在机器学习文献中已十分成熟：RLHF 的最优解可写成 Boltzmann 形式，DPO 将奖励隐式参数化为策略对数比，PPO 通过裁剪代理目标控制策略更新幅度，GRPO 通过组相对优势降低方差。然而，就 §2.3 的系统检索所及，在纯构造性 Coq 形式化的范围内，这些定理的统一机器检查形式化尚不存在；Isabelle/HOL（AFP）与 Lean（mathlib）生态中的相邻工作——MDP 动态规划算法的收敛验证与测度论信息论工具——均不覆盖本文的"对齐目标理论族"，逐条对照与排除见 §2.3。

形式化的价值不仅在于"验证已知结论"。对齐算法的部署场景日益安全关键，而现有纸笔证明存在三类常见漏洞：
1. 分布正性、归一化、KL 有限性等前提被隐式假设；
2. 存在性结论可能依赖排中律；
3. 多个算法族的符号约定和前提不一致，导致跨算法组合时产生隐藏假设冲突。

ConstructiveWorld 项目的目标是在同一逻辑立场（纯构造性、零 Axiom）内，把统计力学、信息论、语言模型与对齐算法统一为单一机器检查库，从而暴露并最小化上述漏洞。

### 1.2 贡献

本工作的贡献按数学性质分三层陈述，并给出分层逻辑——**旗舰结果**（真定理：收敛率/唯一性/精确恢复与恒等）承载全文贡献密度；**支撑性质**（收敛辅助、界引理与初等统计事实）的价值在前提显式化而非数学深度，不与核心定理并列；**基础设施**（Set 层桥梁与接口实例化）提供构造性基座与具体数系落地。

**旗舰结果（真定理：收敛率/唯一性/精确恢复）**

1. **RLHF 最优性闭合（旗舰实质为闭式解与唯一性）**：KL 正则化对齐目标的最优策略 π* ∝ π_ref·exp(r/β) 的闭式解（定理 4.1）与唯一性（定理 4.2）（§4）。显式次优间隙恒等式 J* − J(π) == β·KL(π‖π*)（定理 4.3）与近优单调刻画（定理 4.4）不属独立新不等式，按支撑层（见下）处理：定理 4.3 是自由能分解的一次移项重写（附录 B.1 自评），其价值在为间隙单调（定理 4.7）、聚合损失轨道单调（定理 5.10）与能量耗散型论证提供间隙恒等通道；定理 4.4 是「前向 KL 到 π* 不增 ⟹ 目标单调」的支撑性质。
2. **策略迭代精确动力学**：相对熵镜像下降单步 π_{t+1} ∝ π_t^{1−η}·(π*)^η（几何插值形式，§4.3.1）的向后 KL 精确加权递推与显式收缩因子 κ = 1−η（定理 4.5）、间隙显式恒等式（定理 4.6）、间隙单调（定理 4.7）与诚实接口 `step_kl_eta_bound` 下向后 KL 的**真几何率上界 (1−η)^t**（定理 4.8，κ := 1−η、c := 0）〔注：定理 4.8 的真几何率 (1−η)^t 在诚实接口 `step_kl_eta_bound`（Section Variable，L23114）下成立——该接口的 Real 层对应定理族已随 219 入根：插值不等式 `real_interp_Z_le_one_eps`（L112890）与 eta-bound 对应定理 `real_step_kl_eta_bound_eps`（L113142），连同支撑件 exp 两点凸性 `real_exp_two_point_cvx_eps`（L112669）与逐点 AM-GM `real_amgm_pointwise_eps`（L112817）（见定理 4.8 状态脚注与 §10.2 第 8 项），discharge 链经 2026-09 设计复核收缩后按此执行：最重种子 `real_exp_ge_linear_eps`（L40962，e^t ≥ 1+t，对全部 t 含负）已在根，原估算「需自建有限和 Jensen/Hölder 基建」在本几何插值特形坍缩为 exp 两点凸性（Varberg 锥论证）+ 逐点 AM-GM + 求和保序的组装（数学真值另经 §4.3.1 纸笔证明确认，见定理 4.8 状态脚注）；Real 层对应物入根后，定理 4.8 的抽象层陈述维持诚实接口表述（Real 层 eps 形态与抽象接口签名分属两层，直连消费属 §10.2 第 0 项签名对接）；其 `(1−η)^t` 结论不变〕。该族把「静态最优性（π* 闭式）」推进为「动态迭代的精确量化」，是全文数学含量最集中的部分。
3. **DPO 隐式奖励恢复族 + 审计 = KL 投影（对齐审计的双定理结构，§5）**：隐式奖励精确恢复真实奖励至配分函数基线（定理 5.4）、奖励差分无偏（定理 5.5）、对数比差分等价（定理 5.6）——对齐审计的**测量基座**：DPO 隐式奖励确为真实奖励的仿射像；审计的**作用形式**由 §5.3 定理化：布尔安全过滤器 + 通过集重归一化恰为到通过分布的 KL 投影（`projected_distribution_minimizes_kl`，L95587〔219 实测〕，附精确分解 `kl_sum_split` L95527）——DPO 恢复定理提供「审什么」的基座，KL 投影定理给出「审计如何作用」的形式。
4. **统一自由能视角**：RLHF/DPO/PPO/GRPO 共享同一自由能-KL 基座（`rlhf_free_energy_kl`（L20290）为数学锚点），"统一"有定理支撑而非口号（§8）。

**支撑性质（收敛辅助、界引理、初等统计事实）**：除下列编号条目外，§4 的次优间隙恒等（定理 4.3）与近优单调（定理 4.4）亦归本层——前者是自由能分解的一次移项重写（附录 B.1 自评），后者是「前向 KL 到 π* 不增 ⟹ 目标单调」的支撑性质（见旗舰 1 的定位说明）；两者均不列入旗舰并列贡献。

5. **PPO 代理目标性质（范围限定：裁剪代理目标的静态保守性性质与未裁剪代理目标的改进条件，非"PPO 算法端到端验证"）**：裁剪代理目标的**静态保守性**（定理 6.1/6.7：裁剪代理目标 ≤ 未裁剪 IS 目标）与**未裁剪代理目标**的单调改进条件（定理 6.3/6.4/6.5）——保守性即裁剪机制安全性的形式化（§6）；裁剪代理上的组合定理以**单侧**形式闭合（E1–E3：`ppo_is_decomp`/`clip_error_nonneg`/`ppo_clipped_improvement`，218 基态入根，L112398/L112408/L112439——IS 目标 == 裁剪代理 + clip 误差的无前提分解、clip 误差非负、裁剪代理非负 ⟹ 价值改进；反向界在无界比率下为假（反例），不宣称，见 §6.2 诚实边界），本文不宣称 PPO 算法的端到端验证（§6 范围界定与边界声明一/二/三、定理 6.7 表述与此一致）。
6. **GRPO 组统计量**：组相对优势零均值（定理 7.1）、中心二阶矩恒等式（定理 7.2）与基线方差归约（定理 7.3）——初等代数，其价值在把"减均值降方差"的部署前提（组枚举覆盖、正性、平方非负的构造性边界）显式化（§7）。
7. **Real 层逐 eps 复刻与界引理**：部分核心定理在具体柯西实数层的 eps 化版本（定理 4.9、5.8、5.9、5.11 族、6.6、7.4——即 Real 层逐 eps 复刻覆盖的精确清单，见 §9.2；其余如唯一性 4.2、间隙 4.3/4.4、迭代族 4.5–4.8/5.10、GRPO 中心二阶矩/方差族 7.2/7.3、DPO 相对精确 5.5/5.6 暂无 Real 版），承载抽象接口定理的具体数学内容。

**基础设施（Set 层桥梁与实例化）**

8. **统一形式化基座**：Cauchy 实数、Boltzmann 分布、自由能、KL 散度的构造性定理化与 softmax/Gibbs 等价性；Set 层 `And`/`sigT` 信息性证明与可提取 OCaml 路线（§3）。
9. **构造性纪律与实例化**：全库零 Axiom、零 Admitted，仅依赖 Coq stdlib；接口假设显式分类（§3.4、§9.1），Setoid 系接口实例字段实值化（§9.1.1）。抽象定理签名向 setoid 实例的整体迁移尚未完成——其预计工作量（数人天–数周级机械性工程）、主要摩擦点与迁移完成后的可用性影响见 §9.1.1「Setoid 签名迁移的状态与影响」段与 §10.2 第 0 项。

分层同时回答"形式化一段易证的数学有什么用"：DPO 恢复定理（5.4/5.5）是对齐审计（隐式奖励 = 真实奖励的仿射像）的机器检查依据；PPO 保守性是裁剪安全性的形式化；GRPO 统计量与界引理的价值在前提显式化——论文对支撑层的初等性如实标注（§7.2 术语说明、§4.3.1 定理 4.8 定位段），不把高中代数与核心定理并列为同层贡献。

### 1.3 论文结构

§2 介绍相关工作；§3 描述构造性基座；§4–§7 分别展开四个算法族；§8 给出统一视角；§9 讨论边界与局限；§10 总结并展望未来。

---

## 2 相关工作

### 2.1 机器学习对齐理论

RLHF 的 KL 正则化最优解 π* ∝ π_ref·exp(r/β) 源自相对熵策略搜索（Peters et al.）与线性可解 MDP（Todorov）。DPO 通过隐式奖励 r(s)=β(log π(s)−log π_ref(s)) 绕过显式奖励建模（Rafailov et al., 2023）。PPO 的裁剪目标与单调改进条件见 Schulman et al. (2017)。GRPO 的组相对优势与二阶矩性质见 DeepSeek-AI (2024)。

### 2.2 形式化工作

- **C-CoRN / NuPRL**：构造性分析学的先驱，但规模与主题均未触及 ML 对齐。
- **mathlib / Lean**：分析、测度、信息论覆盖面广，但基于经典逻辑，与本库的构造性立场不同。
- **coq-proba / Infotheo**（Affeldt 等）：离散概率、KL、互信息、AEP 的形式化，但未涉及 RLHF / DPO / PPO / GRPO。
- **神经网络安全性质形式化**（如 CoqNNet、NeuralNetCert）：聚焦鲁棒性、可验证控制器，而非对齐算法的优化理论。

据我们所知（系统检索与逐条排除见 §2.3），在纯构造性 Coq 单一文件、零 Axiom、Set 层可提取 OCaml 的形式化范围内，本文首次将对齐算法优化理论族（RLHF/DPO/PPO/GRPO）在同一证明助手中统一机器检查地形式化。
**与现有形式化工作的对比**（“—”表示不涉及）：

| 工作 | 逻辑立场 | 实数基座 | 状态空间 | 期望类型 | 覆盖内容 | 对齐目标理论 |
|---|---|---|---|---|---|---|
| Infotheo / coq-proba | 经典 | 有理数 / 离散 | 有限离散 | 离散和 | KL、互信息、AEP；不含对齐算法 | 无（信息论工具层） |
| C-CoRN / NuPRL | 构造性 | 构造性实数 | 一般 | — | 分析学基础；不含对齐算法 | 无（分析基础层） |
| mathlib / Lean | 经典 | 经典实数 | 一般（测度空间） | 测度论积分 | 信息论工具（KL 散度 `klDiv`、Gibbs 不等式、测度指数倾斜）；不含对齐目标理论 | 无（`Tilted`/`klDiv` 已覆盖 Boltzmann 权重与几何插值结构，但定位为分析工具，未进对齐目标理论——本工作增值在「分析工具→算法优化理论」的垂直贯通） |
| CoqNNet / NeuralNetCert | 经典 | 经典实数 | 连续 | 积分 | 神经网络鲁棒性；非对齐 | 无（非优化理论） |
| AFP `Markov_Models`（Hölzl & Nipkow 2012） | 经典（HOL） | 经典实数 | 有限/可数 | 轨迹 pmf/测度 | Markov 链/MDP、pCTL 模型检验、可达性；不含一般奖励优化准则与对齐目标理论 | 无（轨迹性质与模型检验） |
| AFP `MDP-Rewards` / `MDP-Algorithms`（Schäffeler & Abdulaziz 2021） | 经典（HOL） | 经典实数 | 有限 | 折扣期望回报（轨迹） | Bellman 算子最优性方程、值迭代/策略迭代（含修正/GS 加速）收敛到最优策略；无 KL 正则化等目标理论 | 无 KL 正则化最优性/隐式奖励恢复/裁剪代理保守性（折扣回报动态规划准则，非本工作目标理论族） |
| Chevallier & Fleuriot 2021（Isabelle/HOL） | 经典（HOL） | 经典实数 | 有限 | 折扣期望回报（轨迹） | 有限 MDP 基础：Bellman 方程、ε-最优值迭代、最优策略迭代；无对齐目标理论 | 无 KL 正则化最优性/隐式奖励恢复/裁剪代理保守性（同左） |
| 本文 | 构造性、零 Axiom | Cauchy 实数（Setoid 实例） | 有限离散 | 全状态精确和 | RLHF 最优性、DPO 隐式奖励恢复、PPO 裁剪上界、GRPO 组统计量 | 有：KL 正则化最优性/唯一性（§4）、隐式奖励恢复（§5）、裁剪代理保守性与改进条件（§6）、组统计量（§7） |

**注（对齐目标理论列）**：本列标注各条目是否形式化 RLHF/DPO/PPO/GRPO 的**目标理论**（KL 正则化最优性、隐式奖励恢复、裁剪代理保守性、组相对优势统计量）。mathlib 的 `Tilted`（测度指数倾斜）与 `klDiv` 已覆盖本工作所用 Boltzmann 权重/几何插值结构的分析工具层面（§2.3(b) 详述），但未进入对齐算法目标理论；本工作的增值恰在把该类分析工具垂直贯通为算法优化理论（§4–§7），而非停留于工具本身。

**mathlib 行框架差异补注**：mathlib 的 `Tilted`/`klDiv` 工作于**一般测度论框架**——`klDiv` 以 Lebesgue 积分定义、取值于 ℝ≥0∞，需管理绝对连续性与可积性；本库的对齐目标理论限定于**有限离散状态空间上的全状态精确和**（`sum_over_S`，Set 层逐点精确求和，无测度论积分与可积性机制）。这一框架差异（测度论积分 vs 全状态精确和）恰是本库无需重复测度论工具层、而在有限离散精确和框架内垂直贯通对齐目标理论（§4–§7）的原因，也是其 scoped claim（§2.3）成立的范围依据。

**逻辑立场列注**：表中「逻辑立场」列标注各工作所用逻辑：本库与 C-CoRN/NuPRL 为**构造性**（不依赖排中律与三分律），mathlib / Infotheo / AFP 条目为**经典**（可自由使用排中律/选择公理）。该列差异不是口号而是可观察的定理形态差异：经典库可陈述精确序结论（如 `min(x,y) ≤ x` 无余量），构造性编码须把序关系以逐 eps 余量陈述并把前提显式化、给存在性结论以构造见证（§3.1、§9.4 实例、§9.1.1）——本库与 mathlib 的核心差异正在于此；本库与 C-CoRN 虽同为构造性立场，但主题不同（C-CoRN 为分析学基础、本库为对齐算法优化理论，见「覆盖内容」列），差异不在逻辑立场而在主题与目标理论覆盖。



### 2.3 Isabelle/HOL 与 Lean 生态相邻工作的系统检索与排除

我们按三个主题对 Isabelle AFP、Lean mathlib 与 Coq/Rocq 生态作了系统检索（检索截至 2026-09；条目与 URL 见参考文献 [9]–[15]），逐一说明其与本文的关系：

**（a）MDP 动态规划：值迭代/策略迭代的机器检查（Isabelle AFP 与非 AFP 条目）。**

- `Markov_Models`（Hölzl & Nipkow，AFP 2012 [10]；期刊版 Hölzl 2016 [9]）：离散时间 Markov 链与有限 MDP、pCTL 模型检验与可达性分析；未引入一般奖励与优化准则，主题是轨迹性质。
- `MDP-Rewards`（Schäffeler & Abdulaziz，AFP 2021 [11]）：在 Hölzl 的 MDP 之上加入奖励，验证无限视界折扣总回报准则下 Bellman 算子的迭代规则、最优性方程与最优平稳确定策略的存在性。
- `MDP-Algorithms`（Schäffeler & Abdulaziz，AFP 2021 [12]）：把 Bellman 算子导出为可执行的值迭代、策略迭代及其 Gauss-Seidel/修正策略迭代（MPI）加速版，在有限 MDP 上验证其收敛到最优解（覆盖 Puterman 第 6 章），并附带代码导出。
- Chevallier & Fleuriot（arXiv:2112.05996，2021 [13]）：在 Isabelle/HOL 中自建有限 MDP + 奖励模型，从第一性原理导出 Bellman 方程，证明折扣因子 < 1 时普遍最优策略存在，并证明值迭代/策略迭代在有限时间内分别给出 ε-最优与最优策略。

这些条目与本文 §4.3.1 主题相邻，但验证对象是**轨迹级动态规划算法**（折扣期望回报的 Bellman 方程/最优性/算法收敛），而非 RLHF 的 KL 正则化最优性（闭式 π* 与唯一性）、DPO 的隐式奖励恢复、PPO 裁剪代理目标的保守性、GRPO 组统计量——即本文 §4–§7 的"对齐目标理论族"。

**（b）信息论与指数族工具（Lean mathlib）。**

- `Mathlib.InformationTheory.KullbackLeibler` [14]：在一般测度上定义 KL 散度 `klDiv`（取值于 ℝ≥0∞），含 Gibbs 不等式（KL ≥ 0，`integral_llr_add_sub_measure_univ_nonneg`）与"KL = 0 ⟺ 测度相等"（`klDiv_eq_zero_iff`）；`Mathlib.MeasureTheory.Measure.Tilted` 形式化测度的指数倾斜（`μ_tilted ∝ e^{f}·μ`）——与本文的 Boltzmann 权重/几何插值结构数学上同源。其定位于一般测度空间上的分析工具（经典逻辑、需管理绝对连续性与可积性），未进入有限状态对齐算法目标理论。

**（c）构造性实数/分析（Coq/Rocq 生态）。**

C-CoRN、NuPRL 与 O'Connor 2008（见 §9.3）之外，Coq 8.12 起标准库随附构造性 Cauchy 实数模块 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` [15]（**Rocq 9.1 实测存留**：`Require Import Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 通过，2026-09-03 环境核验），其收敛/完备性路线与本库 Set 层自建 Cauchy 实数并行；构造性分析方向上未见覆盖对齐算法目标理论的条目。

**排除结论与 scoped 主张。** 上述检索未发现同时满足以下四点的条目：(i) 对齐算法（RLHF/DPO/PPO/GRPO）单步目标理论；(ii) KL 正则化最优性/隐式奖励恢复/裁剪代理保守性/组统计量这一族定理；(iii) 纯构造性逻辑（零 Axiom）；(iv) Set 层 `sigT` 信息性证明与可提取 OCaml 路线。故本文的"首次"应读作有条件的 scoped claim：**在纯构造性 Coq（零 Axiom、Set 层信息性证明、可提取 OCaml）的单一文件形式化范围内、并同时覆盖上述四族目标理论的意义上，据我们所检索为首次**；同一范围内的相邻工作在 (a)–(c) 中逐一对照与排除（汇总表见 §2.2）。

> 【对齐标注 2026-09-08 · 220 基态】scoped claim 的四点界定与"单一文件"限定语**维持不变**（其锚为 219 单文件，SHA-1 7BBE42EA83D178901C94FA13FB18E0A3B975D09A，114,222 行，实测与本地一致）。基线维护形态自 220 起为**模块化树**（基座 `CW_ConstructiveWorld_219` 信任缓存 + 28 个独立模块，各模块 .vo 经内核校验）——这是同一单文件内容的工程打包形态，不扩大也不改写本节 claim 的范围；追加模块层（宪法/防火墙/投影/逐出/耗散币制等治理与新算法件）不属于本文四族目标理论，不参与本 claim。

---

## 3 构造性基座与库设计

### 3.1 Cauchy 实数与等式类型

本库不引入经典实数公理，而是从有理数 Cauchy 序列构造实数 `Real`，并显式使用 setoid 等式 `Id`（Leibniz 等价的构造性版本）以及可计算序 `le`/`lt`。所有存在性结论均要求给出构造性见证；例如 `inv_pos` 要求输入正性证明，避免非构造性的"x>0 或 x≤0"判断。

### 3.2 概率分布与信息论

有限状态空间 `S` 上的分布由函数 `S -> R` 表示，配合归一化 `normalized` 与正性 `positive_dist` 假设。核心定义包括：
- `sum_over_S`：有限求和算子。
- `relative_entropy p q`：KL 散度 `Σ p(s)·(log p(s) − log q(s))`。
- `boltzmann_dist energy beta`：Boltzmann 分布 `exp(−energy(s)/β) / Z`。

### 3.3 自由能与 Boltzmann 最小化

对齐目标被嵌入自由能框架：

```
Definition free_energy (energy : S -> R) (beta : R) (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (energy s))
  + mult beta (sum_over_S (fun s => mult (p s) (log (p s)))).
```

库内已证：
- `free_energy_kl_decomp`（L16259）：`F[p] = F[p_b] + β·KL(p‖p_b)`。
- `gibbs_inequality`（L16629）：`KL(p‖q) ≥ 0`。
- `min_free_energy_is_boltzmann`（L16838）：Boltzmann 分布是自由能全局最小点。

这些结果构成 RLHF 与 DPO 最优性证明的共享基础。

### 3.4 诚实接口纪律

库内所有未证假设均显式声明为 `Variable` 并分类管理：A 类（接口字段）、B 类（Section 局部假设）、C 类（已证定理）。本文中引用的定理均来自 C 类；仍在使用的假设将在 §9 显式列出。

---

## 4 RLHF：KL 正则化对齐的最优性

**KL 方向约定**：全文 `KL(p‖q)` 一律指前向 KL `Σ_s p(s)·(log p(s) − log q(s))`（§3.2 `relative_entropy p q` 定义），方向由符号顺序决定、KL 不对称：`KL(π‖π*)` 为**前向** KL（π 相对 π*），`KL(π*‖π)` 为**后向** KL（π* 相对 π）。方向敏感告示：间隙恒等取前向（定理 4.3：`J*−J(π) == β·KL(π‖π*)`），迭代收缩取后向（定理 4.8：`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0)`），两方向在单纯形上不可比、不可互换，目标间隙的几何率亦不可由二者直接组装（见 §4.3 定理 4.3 注、§4.3.1 定位注与 §10.2 第 7 项诚实注记）；读者核对各定理陈述时请以符号顺序为准。

### 4.1 问题设定

给定奖励函数 `r : S -> R`、参考策略 `pi_ref : S -> R`、温度参数 `beta > 0`，定义对齐目标：

```
Definition align_objective (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (reward s))
  - mult beta (kl_to_ref pi).
```

其中 `kl_to_ref pi = KL(pi‖pi_ref)`。目标是找到最大化 `align_objective` 的策略 π。

### 4.2 最优策略闭式

最优策略的闭式定义如下（逐字抽取自代码库 L18761–L18768）：

```coq
(* L18761 *)
Definition Z_align : R :=
  sum_over_S (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* L18766 *)
Definition pi_star (s : S) : R :=
  mult (inv_pos Z_align Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
```

`exp_neg x` 表示 e^(−x)，因此 `exp_neg (opp (r(s)/β))` = e^(+r(s)/β)，与标准 RLHF 最优策略 π\* ∝ π_ref·e^{r/β} 一致。`Z_align` 为配分函数（其正性 `Z_align_pos` 为 Section 变量，L18764），保证 `pi_star` 归一化且正（`pi_star_pos`（L18771）`pi_star_normalized`（L18783）。

### 4.3 核心定理

**定理 4.1**（`rlhf_optimal`, L19049）：对任意归一化且正的概率分布 `pi`，
```
le (align_objective pi) (align_objective pi_star).
```

**证明概要**：
1. 由 `min_free_energy_is_boltzmann`，Boltzmann 分布在自由能上最小化；
2. 由 `align_boltzmann_is_pi_star`，Boltzmann 分布逐点等于 `pi_star`；
3. 取负（`opp_le_compat`）将对齐目标的不等式反向，得到结论。

**定理 4.2**（`rlhf_optimal_unique`, L19128）：若 `pi_star` 与另一策略给出相同对齐目标值，则两者逐点相等。

**证明概要**：由自由能分解恒等式 `F[p] = F[p_b] + β·KL(p‖p_b)`，若 `F[p]=F[p_b]` 则 `KL(p‖p_b)=0`；再由 `gibbs_equality` 得 `p=p_b`。

**定理 4.3**（`rlhf_suboptimality_gap`, L20554）：对任意归一化且正分布 `pi`，对齐目标的次优间隙可显式写成**前向** KL 的形式：
```
Id (minus (align_objective pi_star) (align_objective pi))
   (mult beta (relative_entropy pi pi_star)).
```
即 `J* − J(π) == β·KL(π‖π*)`（L20554–L20558 实测语句；方向注意：本恒等是**前向** KL `KL(π‖π*)`，与定理 4.8 收缩的**后向** KL `KL(π*‖π_t)` 方向不同，见 §4.3.1 与 §10.2 诚实注记）。

**定理 4.4**（`rlhf_policy_improvement`, L20591）：对任意归一化且正的两策略 `p_old`、`p_new`（`normalized`/`positive_dist`），若新策略到最优策略的**前向** KL 不增，则对齐目标单调：
```
le (relative_entropy p_new pi_star) (relative_entropy p_old pi_star) ->
le (align_objective p_old) (align_objective p_new).
```
即 `KL(p_new‖π*) ≤ KL(p_old‖π*) ⟹ J(p_old) ≤ J(p_new)`——「越接近 π*（前向 KL 意义下）目标越高」（L20591–L20596 实测语句）。注意：本定理与附录 B.2 的「改进条件」推导是**两回事**——4.4 的前提是两策略到 π* 的 KL 序，不含优势函数与 `advantage_nonneg`；附录 B.2 的 `exact_improvement_identity` 路线对应的是 §6 的 `ppo_monotonic_improvement`（定理 6.3）/`kl_penalty_sufficient`（定理 6.4），旧稿把 B.2 挂于 4.4 名下系归因错误，本版已按代码实况修正（212/217/218/219 复核一致；该区 210/212/217/218/219 逐字一致——219 复核：根前 112,462 行与 218 版逐字节 diff 零命中〔承接 218 复核的 79,608 行对 212 零命中链〕，见 §9.1.1 Artifact 段）。

**证明概要**：把定理 4.3 的次优间隙恒等分别用于 `p_old` 与 `p_new`（`J*−J(p) == β·KL(p‖π*)`，L20599–L20606）；由前提与 `β > 0` 的保序（`le_mult_compat_r`，L20607–L20610）得 `J*−J(p_new) ≤ J*−J(p_old)`；差分翻转（`le_plus_compat` + `minus`/`opp` 消去，约 20 步装配收口）即 `J(p_old) ≤ J(p_new)`。

### 4.3.1 策略迭代的更新规则

定理 4.5–4.8 依赖以下显式定义（逐字对应代码库 `Section Alignment` 的 policy 定义区，L21240 起）。步长参数与正则性假设：

```coq
Variable eta         : R.
Variable eta_pos     : lt zero eta.        (* 0 < η *)
Variable eta_le_one  : le eta one.         (* η ≤ 1 *)
```

增广优势与相对熵镜像下降单步（对 `pi_t` 的 KL 信任域步）：

```coq
Definition advantage_aug (pi_t : S -> R) (s : S) : R :=
  minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s)))).

Definition Z_rel (pi_t : S -> R) : R :=
  sum_over_S (fun s => mult (pi_t s)
    (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).

Definition pi_next (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S) : R :=
  mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
       (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).
```

即 `pi_next(pi_t)(s) ∝ pi_t(s)·exp(+(η/β)·A_aug(pi_t, s))`——Boltzmann 更新权重。**指数内的符号是"+"**：代码写作 `exp_neg (opp (mult …))`，依 §4.2 约定 `exp_neg x = e^{−x}`，`exp_neg (opp x) = e^{+x}`，故散文公式应为 `exp(+(η/β)·A_aug)` 而非 `exp(−(η/β)·A_aug)`。这一"−"与"+"之争的判据是更新方向：取"−"则权重随优势递减、更新背离 π*，与定理 4.5–4.8 的全部机器检查恒等式矛盾；取"+"（代码语义，与 §4.2 π* ∝ π_ref·e^{r/β} 同一符号约定）则单步即向 π* 的**几何插值桥**（见下），恒等式族全部成立。几何插值的指数化含义：对权重取对数得 `log π_{t+1}(s) = log π_t(s) + (η/β)·A_aug(π_t, s) − log Z_rel(π_t)`；代入 `A_aug := r − β·(log π_t − log π_ref)` 与 `log π*(s) = log π_ref(s) + r(s)/β − log Z_align`（定理 5.1 证明概要）即得 `log π_{t+1}(s) = (1−η)·log π_t(s) + η·log π*(s) + const`，亦即

π_{t+1} ∝ π_t^{1−η}·(π*)^η

——策略在对数几率空间中向 π* 作 (1−η):η 的凸插值（0 < η ≤ 1；η = 1 一步到 π*，η → 0 原地不动）。同一计算解释两个结构事实：其一，π* 是单步不动点——代换得 `A_aug(π*, ·) ≡ β·log Z_align` 为常数（与状态无关），于是 `Z_rel(π*) = Z_align^η` 且 `pi_next(π*)(s) = π*(s)`；其二，向后 KL 递推的收缩系数正来自该几何插值——机器检查的单步引理 `policy_iter_backward_kl_step_le`（L22790）为 `KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1})`（等号恒等版含可弃项 `−η·KL(π_t‖π*) ≤ 0`，见代码 `policy_iter_backward_kl_step`（L22686）恒等版与 L22780 的 le 版注释），第一项系数 1−η 即 `log π_t` 的插值权重，第二项为单步 KL 残差、即 `step_kl_weighted` 的来源。迭代打包与加权步长 KL 和：

```coq
Fixpoint policy_iterate (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s))
  : { pi' : S -> R & forall s : S, lt zero (pi' s) } := ...   (* L22879 起 *)

Fixpoint step_kl_weighted (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s)) : R :=
  (* S(0) = 0;  S(S m) = KL(pi_m‖pi_{S m}) + (1−η)·S(m) *)   (* L22903 起 *)
```

步长诚实接口（升级后唯一接口：步长 KL 被**前向** KL 到最优控制；Real 层路线经 2026-09 复核收缩为逐点 AM-GM 组装——种子已在根、对应定理已随 219 入根，见下方定位段、定理 4.8 状态脚注与 discharge 注）：

```coq
Variable step_kl_eta_bound : forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
  le (relative_entropy pi_t (pi_next pi_t pi_t_pos))
     (mult eta (relative_entropy pi_t pi_star)).               (* L23114 *)
```

**定理 4.8 的准确定位**：针对旧形式「`(1−η+c)^t` 缺 `c < η` 不构成收敛率」的批评已由代码解决（迭代 200 起收紧，按 219 基态复核）：`policy_iter_kl_geom_step`（219 现测 L23146）/`policy_iter_kl_geom_iter`（219 现测 L23181）现陈述**真几何率 κ := 1−η（c := 0）**，即下文的 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`——**是**（无需附加 `c < η` 假设的）收敛率定理。升级的关键是接口替换：旧 `step_kl_ratio_bound`（「前向 KL ≤ c·向后 KL」）对任意常数 c 并非定理——两方向 KL 在单纯形上不可比，前向 KL 可无界而 `KL(pi*‖pi_t)` 有界，比值无界（sR21 反例族论证；代码 L23102–L23113 注释实录）；新单一诚实接口 `step_kl_eta_bound`（L23114）把步长 KL 控到**同向**（前向）KL：`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`，数学上为真（≡ 插值不等式 `log Z ≤ 0`，Z := Σ_s pi_t(s)^{1−η}·pi*(s)^η；Real 层证明路线经 2026-09 复核收缩为逐点 AM-GM——种子 `real_exp_ge_linear_eps`（L40962）已在根，见下方 discharge 注与 §10.2 第 8 项）。自迭代 200 收紧后 policy 区无改动，219 复核仍成立（与 210/212/217/218 逐字一致——219 复核：根前 112,462 行与 218 版逐字节 diff 零命中，见 §9.1.1 Artifact 段）。

**该前提的数学地位与 discharge 状态（Real 层对应物已入根，残余如实标注）**：接口升级（`step_kl_ratio_bound` → `step_kl_eta_bound`（L23114））已在代码层完成：新接口 + 真几何率 `(1−η)^t`（`policy_iter_kl_geom_step`/`iter`，L23146/L23181）。`step_kl_eta_bound` 在纸笔文献中对应相对熵（镜像）下降三点引理族把步长 KL 控到前向 KL 的收缩估计；其数学真值 ≡ 插值不等式 `log Z ≤ 0`（Z := Σ_s pi_t(s)^{1−η}·pi*(s)^η，几何插值 π_{t+1} ∝ π_t^{1−η}(π*)^η 的配分函数；π* 为单步不动点，残差 `KL(pi_t‖pi_{t+1})` 可经 `Z_rel` 展开为 log-sum-exp，见本节定义处）。**Real 层 discharge 已完成（219 入根；数学真值另经纸笔证明确认——见下纸笔草图、Proof Outline 与定理 4.8 状态脚注）**：该插值不等式在 **Real 层**的对应定理已入主库——Set 层接口公理集不含实数 Hölder/指数凸性，纯 Set 层代数推演不可达，故按 Real 层逐 eps 复刻路线（与定理 4.9、6.6 同型）完成。**设计复核把该路线的基建需求收缩**：最重解析种子 `real_exp_ge_linear_eps`（L40962：`forall t eps, real_lt real_zero eps -> real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) eps)`，即 e^t ≥ 1+t 的 Bishop 逐 eps 版、对全部 t 含负成立）**已在基线库内证明**（§10.2 第 8 项撰写时点未计入）；插值不等式 Z ≤ 1 的 Real 层证明由此坍缩为「exp 两点凸性（Varberg 锥论证，只消费该种子）+ 逐点 AM-GM + 求和保序（`real_sum_over_S_le/add` 既有）」三步——不再需要自建有限和 Jensen/Hölder 基建（数学核与引理清单见下方 Proof Outline 修订版；217 另入根 `real_expf_realizable`（L96364）——expf 五字段迷你接口在具体柯西实数上的 sigT 放电——供「exp 凸性接口化」的可选封装，未入根）。对应定理（`real_interp_Z_le_one_eps`，L112890 / `real_step_kl_eta_bound_eps`，L113142）已随 219 入主库（连同支撑件 `real_exp_two_point_cvx_eps`（L112669）/`real_amgm_pointwise_eps`（L112817）/`real_pow_pos`（L112814），均以自然数步进枚举 `seq 0 n` 为载体、归一化以 `real_eq`（Σ==1）前提、逐点正性以显式证书（HZ/Hqv 型）接口化，见定理 4.8 状态脚注与 §10.2 第 8 项）——诚实接口的 Real 层对应物由此在主库机器检查闭合，定理 4.8 的 `(1−η)^t` 结论不变（其抽象层陈述维持诚实接口表述，见状态脚注）。该 policy 区 210/212/217/218/219 逐字一致（219 复核：根前 112,462 行与 218 版逐字节 diff 零命中），无新增代码改动。

**`step_kl_eta_bound` 的几何插值直觉与 `log Z ≤ 0` 纸笔草图（纸笔论证，非机器检查）**：为何几何插值 `π_{t+1} ∝ π_t^{1−η}·(π*)^η` 蕴含单步 KL 上界 `KL(π_t‖π_{t+1}) ≤ η·KL(π_t‖π*)`？因为该单步 KL 恰可展开为「η 倍前向 KL 到 π* + 插值配分函数的对数」，而后者 ≤ 0 由 log-sum-exp（Boltzmann 归一化）的凸性保证。非形式直觉：对数几率空间中的插值 `log π_{t+1} = (1−η)·log π_t + η·log π* − log Z`（见本节定义处的几何插值推导）把 `π_t` 沿指数族测地线向 `π*` 平移 η 比例，被跳过的 KL 残差不超过整段前向 KL 的 η 倍——KL 到插值点的距离沿插值凸方向收缩，这正是 log 配分函数凸性（等价于 Hölder/加权 Young）的体现。形式上，把 `A_aug` 展开并利用 `π* ∝ π_ref·e^{r/β}`（定理 5.1 概要）代入配分函数定义（L21240 区）：

```
Z_rel(π_t) = Σ_s π_t(s)·exp((η/β)·A_aug(π_t, s))                      （§4.3.1 定义）
           = Σ_s π_t(s)^{1−η}·π_ref(s)^η·exp((η/β)·r(s))               （A_aug 展开，π_t^{−η} 吸收）
           = Z_align^η · Σ_s π_t(s)^{1−η}·π*(s)^η                      （π* 闭式代换，归一化吸收）
```

记 `Z := Σ_s π_t(s)^{1−η}·π*(s)^η = Z_rel(π_t)/Z_align^η`（即定理 4.8 定位注中 `log Z ≤ 0` 的 `Z`；退化端 η = 1 时 `Z = Σ_s π* = 1`、η = 0 时 `Z = Σ_s π_t = 1`，两端平凡）。由归一化 `Σ_s π_{t+1}(s) = 1` 得逐点形 `π_{t+1}(s) = π_t(s)^{1−η}·π*(s)^η / Z`，代回单步 KL：

```
KL(π_t‖π_{t+1}) = Σ_s π_t(s)·[log π_t(s) − log π_{t+1}(s)]
                = Σ_s π_t(s)·[η·(log π_t(s) − log π*(s)) + log Z]
                = η·KL(π_t‖π*) + log Z                                 （Σ_s π_t = 1）
```

故 `step_kl_eta_bound ⟺ log Z ≤ 0`。而 `log Z ≤ 0` 是 log-sum-exp 凸性的直接推论（p := 1/(1−η)、q := 1/η 的 Hölder/加权 Young 同族）：

```
log Z = log Σ_s exp((1−η)·log π_t(s) + η·log π*(s))
      ≤ (1−η)·log Σ_s exp(log π_t(s)) + η·log Σ_s exp(log π*(s))       （log-sum-exp 凸性）
      = (1−η)·log Σ_s π_t(s) + η·log Σ_s π*(s)
      = (1−η)·log 1 + η·log 1 = 0                                       （π_t、π* 均归一化）
```

等号当且仅当 `π_t = π*` 逐点（log-sum-exp 严格凸侧）。上述推导为纸笔层面论证，用于解释诚实接口 `step_kl_eta_bound`（L23114）的数学地位与 Real 层证明的路线。**Real 层机器状态**：本不等式在 Real 层的对应定理已随 219 入根（插值不等式 `real_interp_Z_le_one_eps`（L112890）与 eta-bound 对应定理 `real_step_kl_eta_bound_eps`（L113142），连同支撑件 `real_exp_two_point_cvx_eps`（L112669）/`real_amgm_pointwise_eps`（L112817），见定理 4.8 状态脚注与 §10.2 第 8 项）；其证明路线经设计复核收缩——所需 Jensen/Hölder 基建在本几何插值特形坍缩为 exp 两点凸性（Varberg 锥论证）+ 逐点 AM-GM + 求和保序，最重种子 `real_exp_ge_linear_eps`（L40962，e^t ≥ 1+t）已在根（见上 discharge 注与 §10.2 第 8 项）——入根定理的组装与该路线一致；入根形态为 Real 层 eps 定理，不改变定理 4.8 的抽象层陈述（诚实接口表述，见状态脚注）。

**`step_kl_eta_bound` 的 Real 层 Proof Outline（该路线已随 219 入根闭合）**：把上面纸笔草图扩展为 Real 层闭合的证明计划；其引理路线（exp 两点凸性/逐点 AM-GM/插值不等式与 eta-bound 对应物）已随 219 入主库——`real_exp_two_point_cvx_eps`（L112669）/`real_amgm_pointwise_eps`（L112817）/`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142），见定理 4.8 状态脚注与 §10.2 第 8 项。目标：在 Real 层（柯西实数、逐 eps 余量）证明插值不等式 `log Z ≤ 0`（Z := Σ_s π_t(s)^{1−η}·π*(s)^η），为诚实接口 `step_kl_eta_bound` 提供 Real 层 eps 对应物（定理 4.8 的抽象层陈述因此维持不变，见状态脚注）。所需 Real 层引理清单（设计复核修订：原列 1–3 的有限和 Jensen/log-sum-exp 凸性/Hölder 在本几何插值特形统一坍缩为「逐点 AM-GM + 求和保序」——最重种子已在根，见下；原引理 4 维持为组装步）：
1. **exp 两点凸性（Real 层 eps 化）**：`(1−η)·e^x + η·e^y ≥ e^{(1−η)x+ηy} − eps`——Varberg 锥论证：记 `z := (1−η)x + ηy`，则 `x−z = η(x−y)`、`y−z = (1−η)(y−x)`；由种子得 `e^{x−z} ≥ 1 + η(x−y)` 与 `e^{y−z} ≥ 1 − η(x−y)`（Bishop 逐 eps 形态），乘正元 `e^z > 0` 加权合并即收口——**只用已证种子 `real_exp_ge_linear_eps`（L40962，e^t ≥ 1+t，对全部 t 含负），无符号分支、无三分、无需新建 Jensen 基建**（两处 eps 簿记：各 `eps/2` 或正乘加权，模板同附录 C.2）；
2. **逐点 AM-GM**：`a^{1−η}·b^η ≤ (1−η)·a + η·b`（a、b > 0）——第 1 条在 `(x,y) := (log a, log b)` 的实例，经 `real_pow_pos` 定义（`a^α := exp(α·log a)`）与 `cauchy_real_exp_plus/wd`（既有）换形；
3. **求和保序与归一化吸收**：`Z := Σ_s π_t^{1−η}·π*^η ≤ 1 + eps`——逐点 AM-GM 逐点求和（`real_sum_over_S_le` 接口既有）+ 归一化 `Σπ_t == Σπ* == 1` 吸收；
4. **log 侧严格化与组装**：由 `Z ≤ 1 + eps/2` 与 `1 + eps/2 < e^{eps}`（种子在 t := eps/2 的严格化）得 `Z < e^{eps}`，经 log 单调 lt 版（`cw_log` 路线既有）得 `log Z < eps`；代回单步 KL 展开 `KL(π_t‖π_{t+1}) == η·KL(π_t‖π*) + log Z`（见上纸笔草图）→ 以 `real_le` 的 inl（lt）支收口为 `real_step_kl_eta_bound_eps`；随后沿 §4.3.1 迭代组装（定理 4.5–4.8 同型路线）即可闭合定理 4.8 的 `(1−η)^t` 上界在 Real 层的对应物。上述引理均为标准事实的有限和/eps 化形态，M1/M2 核心为**天级组装**（种子已在根，无需自建凸性基建；见 §10.2 第 8 项），未发现潜在逻辑障碍——该路线已随 219 入根兑现（四件行号见本节首段与定理 4.8 状态脚注）；定理 4.8 的陈述维持「诚实接口下成立」的抽象层表述。

**定理 4.5**（`policy_iter_backward_kl_iter_le`, L22915）：策略迭代 `pi_{t+1} := pi_next pi_t`（相对熵镜像下降单步）的向后 KL 满足**精确加权递推上界**：
```
le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
   (plus (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi))
         (step_kl_weighted t pi pi_pos)).
```
即 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0) + Σ_{i<t} (1−η)^{t−1−i}·KL(pi_i‖pi_{i+1})`——κ := 1−η 显式收缩因子，步长 KL 加权和显式保留（`step_kl_weighted` Fixpoint，L22903；迭代打包 `policy_iterate`（L22879），sigT 正性内嵌`policy_iter_norm`（L22890），归一化保持）。

**证明概要**：归纳组装 `policy_iter_backward_kl_step_le`（单步递推）——归纳前提乘 κ（`le_mult_compat_weak` + `mult_comm` 换形，κ ≥ 0 由 `le_minus_nonneg`(η≤1)）→ `le_plus_compat` 加步长 KL → `distrib`/`plus_assoc`/`plus_comm`/`mult_assoc` 四步代数收口。

**定理 4.6**（`policy_iter_gap_diff`, L23000）：间隙单步**显式恒等式**——策略改进量恰为 β·加权 KL 对：
```
Id (minus (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t))
   (mult beta (plus (mult (minus (inv_pos eta eta_pos) one)
                          (relative_entropy (pi_next pi_t pi_t_pos) pi_t))
                    (mult (inv_pos eta eta_pos)
                          (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
```
即 `J(pi_{t+1}) − J(pi_t) == β·[(1/η−1)·KL(pi_{t+1}‖pi_t) + (1/η)·KL(pi_t‖pi_{t+1})]`——把 `policy_improvement_mono`（L22065）证明体内的 `Hbeta_form` 链（`surrogate_diff_identity` + `inv_pos` 左逆 + 分配/减法分布）提取为独立定理（单步改进 ≤ 的定量恒等强化；注意它强化的是 REPS 型单步改进 `policy_improvement_mono`，与定理 4.4 的 KL-到-π* 序陈述是两回事）。

**证明概要**：J 分解（`J_pi_t_t12`/`J_pi_next_t12`）→ `surrogate_diff_identity` ÷η（`inv_pos_correct` 吸收）→ 减法重组（`plus_assoc`/`plus_comm`）→ β 分配（`distrib` + `mult_minus_distr_r_t12`）收口。

**定理 4.7**（`policy_iter_gap_mono`, L23086）：间隙单调不增——`gap_{t+1} := J* − J_{t+1} ≤ J* − J_t =: gap_t`。

**证明概要**：`policy_improvement_mono` + `opp_le_compat` + `le_plus_compat`（`minus` 定义展开即闭）。

**定理 4.8**（`policy_iter_kl_geom_iter`, L23181）：诚实接口 `step_kl_eta_bound`（步长 KL 被前向 KL 控制：`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`，L23114；≡ 插值不等式 `log Z ≤ 0`；Real 层证明路线经 2026-09 复核收缩为逐点 AM-GM——种子 `real_exp_ge_linear_eps`（L40962）已在根、对应定理已随 219 入根（`real_interp_Z_le_one_eps` L112890 / `real_step_kl_eta_bound_eps` L113142），见状态脚注与 §10.2 第 8 项；零公理）下，向后 KL **真几何收缩率 κ := 1−η（c := 0）**：
```
le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
   (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi)).
```
即 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`——单步真几何收缩（`policy_iter_kl_geom_step`, L23146：`KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)`）归纳组装；因 0 < η ≤ 1 有 κ ∈ [0,1)，`(1−η)^t` 为显式指数衰减——较旧条件化形式 `(1−η+c)^t` 更紧且**无需** `c < η` 假设。

**状态脚注**：`step_kl_eta_bound` 的**数学真值已确认**——其 ≡ 插值不等式 `log Z ≤ 0` 的等价与纸笔论证见本节上文（定理 4.8 定位注、discharge 注、纸笔草图与 Proof Outline）；**机器检查 discharge 的路线经设计复核收缩**——所需 Jensen/Hölder 基建在本几何插值特形坍缩为逐点 AM-GM + 求和保序（最重种子 `real_exp_ge_linear_eps`（L40962，e^t ≥ 1+t）已在根；217 另入根 `real_expf_realizable`（L96364）供 expf 迷你接口放电），Real 层核心不等式族（插值不等式 `Z ≤ 1 + eps` 与 eta-bound 对应物及其支撑件）已按此**随 219 入主库**：`real_exp_two_point_cvx_eps`（L112669，exp 两点凸性）、`real_amgm_pointwise_eps`（L112817，逐点 AM-GM）、`real_interp_Z_le_one_eps`（L112890，插值不等式 `Z ≤ 1 + eps`）与 `real_step_kl_eta_bound_eps`（L113142，eta-bound 对应定理）——均以自然数步进枚举（`seq 0 n`）为载体、以归一化 `real_eq` 前提（Σ==1）与显式证书前提（HZ：插值配分函数正性；Hqv：逐点正性）接口化。定理 4.8 的抽象层陈述维持「诚实接口下成立」的现有表述（Real 层 eps 定理与抽象接口分属两层，接口的抽象层消解仍受 Set 层接口公理集限制，见定位注），其 `(1−η)^t` 结论不变。英文脚注原文：*The mathematical truth of `step_kl_eta_bound` (equivalently `log Z ≤ 0`) is established by pen-and-paper argument in §4.3.1. A 2026-09 design review shows that, for this geometric-interpolation special case, the required infrastructure collapses to pointwise AM-GM assembled from the machine-checked seed `real_exp_ge_linear_eps` (L40962, e^t ≥ 1+t) together with sum order-preservation. The Real-layer core inequalities have been merged into the main library (219): the two-point convexity lemma `real_exp_two_point_cvx_eps` (L112669), the pointwise AM-GM lemma `real_amgm_pointwise_eps` (L112817), the interpolation bound `real_interp_Z_le_one_eps` (L112890, Z ≤ 1 + eps over a normalized finite enumeration with explicit positivity certificates) and the eta-bound counterpart theorem `real_step_kl_eta_bound_eps` (L113142, the pointwise-epsilon form of the step-KL bound with explicit positivity certificates HZ/Hqv), all stated over natural-number initial segments `seq 0 n`. Theorem 4.8 itself remains stated under the honest-interface formulation at the abstract layer; its (1−η)^t bound is unchanged.*

**证明概要**：单步：精确三 KL 恒等 `policy_iter_backward_kl_step`（L22686）给出 `KL(pi*‖pi_{t+1}) == (1−η)·KL(pi*‖pi_t) − η·KL(pi_t‖pi*) + KL(pi_t‖pi_{t+1})`，`step_kl_eta_bound` 保证 `KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`，两 η 项抵消（`plusA_opp_cancel_le` 辅助收口）即得单步收缩；迭代：归纳前提乘 κ（κ ≥ 0 由 `le_minus_nonneg`（η ≤ 1）保证；`le_mult_compat_weak` + `mult_comm` 换形）→ `r_pow` 结合换形收口。

**定理 4.9**（`real_rlhf_optimal_eps`, L43804）：RLHF 最优性的 **Real 层复刻（eps 化）**——柯西实数层对齐目标满足：
```
real_le (real_opp (real_free_energy pi Hpi))
        (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))
                   (real_mult D eps)).
```
即 `J(π) ≤ J(π*) + D·eps`（eps 加权残差形态；Real 层 KL ≥ 0 只有 eps 版 `real_gibbs_sum_eps`，构造性边界诚实标注）。

**证明概要**：熵侧 KL 分解经诚实接口 `real_kl_decomp_full`（L43730，常数消去桥：F(p) == F(p_b) + D·Σkl）——逐点 `log p == log p_b + kl_term` 抵消链 + Σ ext + sum_add + `real_kl_term_equiv` → 自由能 KL 分解接口 → gibbs eps（0 ≤ Σkl + eps）→ D 正乘（`real_le_mult_compat` + comm 换形）→ `le_plus_compat`（F(p_b) ≤ F(π) + D·eps）→ opp 取负（`real_opp_le_compat` + 环恒等 A == (A+oppC)+C 收口）。诚实接口（零公理）：`real_boltzmann_log_decomp`/`real_boltzmann_normalized`/`real_kl_term_equiv`/`real_pi_star_align`/`real_gibbs_sum_eps`/`real_kl_decomp_full`——全部 Real 层可实例化（`real_rlhf_optimal_eps` 的证明实际消费 `real_kl_decomp_full`，L43816）。

---

## 5 DPO：隐式奖励的精确恢复

### 5.1 DPO 损失与隐式奖励

DPO 将奖励函数隐式定义为：

```coq
Definition dpo_implicit_reward (pi : S -> R) (s : S) : R :=
  mult beta (minus (log (pi s)) (log (pi_ref s))).
```

聚合形式的 DPO 损失为对齐目标的负值：

```coq
(* L19090 *)
Definition dpo_loss (pi : S -> R) : R :=
  opp (align_objective pi).
```

### 5.1.1 逐对 Bradley-Terry 损失

对数几率比与逐对 DPO 损失定义如下（L20880–L20888）：

```coq
(* L20880 *)
Definition log_ratio (pi : S -> R) (s : S) : R :=
  minus (log (pi s)) (log (pi_ref s)).

(* L20885：成对 DPO 损失，偏好 s_w ≻ s_l *)
Definition dpo_loss_pair (pi : S -> R) (s_w s_l : S) : R :=
  opp (log (sigmoid (minus (mult beta (log_ratio pi s_w))
                           (mult beta (log_ratio pi s_l))))).
```

即标准 DPO 的 Bradley-Terry 形式

\[
\mathcal{L}_{\text{DPO}}(\pi; s_w, s_l) = -\log\sigma\!\left(\beta\log\frac{\pi(s_w)}{\pi_{\text{ref}}(s_w)} - \beta\log\frac{\pi(s_l)}{\pi_{\text{ref}}(s_l)}\right).
\]

**定理 5.1**（`dpo_loss_at_pi_star`, L20892）：在最优策略处，逐对损失精确退化为真实奖励差的对数几率：

```coq
forall s_w s_l : S,
  Id (dpo_loss_pair pi_star s_w s_l)
     (opp (log (sigmoid (minus (reward s_w) (reward s_l))))).
```

**证明概要**：由 `log_pi_star` 展开 `log (pi_star s)` = `−log Z_align + log (pi_ref s) + r(s)/β`；`π_ref` 项与 `Z_align` 项在差分中严格消去，`β·(1/β) = 1` 由 `inv_pos_correct` 完成。约 30 步构造性代数链。

**边界声明**：本工作形式化了 DPO 的**逐对损失在最优策略处的精确取值**与**隐式奖励恢复**。尚未形式化：偏好数据集上的期望总损失、梯度、以及优化算法的收敛性。两个「单调」陈述的对象须分清：(i) 定理 5.7（`dpo_total_loss_monotone`，L20181）的「总损失单调」指**有限偏好列表 fold 求和** `dpo_total_loss`（L20153）的泛单调性——逐对损失 `dpo_pair_loss`（L20111）逐项不增 ⟹ 列表和不增，语句**不含 π***、**不含改进方向**；(ii) **聚合损失** `dpo_loss`（`opp (align_objective)`，定义 L19090）沿策略改进轨道单调不增见定理 5.10（`dpo_loss_iter_step_le`/`dpo_loss_iter_mono`，L23244/L23256）——「沿改进方向单调」的准确所指。二者均不是逐对偏好损失的期望。

### 5.2 核心定理

**定理 5.2**（`dpo_optimal`, L19096）：对任意归一化正分布 `pi`，
```
le (dpo_loss pi_star) (dpo_loss pi).
```

**证明概要**：直接复用 `rlhf_optimal`，并对不等式取负。

**定理 5.3**（`dpo_reward_is_implicit`, L19616）——命名桥引理（定义性后承，reflexivity 级）：显式对数形式与隐式奖励定义逐点相等。两定义（`dpo_reward_explicit` L19613 / `dpo_implicit_reward` L19086）实为同一项，证明即 `unfold dpo_reward_explicit, dpo_implicit_reward; reflexivity`（L19620）——按 §1.2 分层属**定义性后承**而非独立结果，列此仅为命名对应，不计入恢复定理族并列贡献。

**定理 5.4**（`dpo_reward_recovers_up_to_baseline`, L19626）：在最优策略 `pi_star` 处，隐式奖励满足
```
r_DPO(pi*, s) = r(s) − beta·log Z_align.
```

即 DPO 隐式奖励精确恢复真实奖励，差一个与状态无关的配分函数基线。

**定理 5.5**（`dpo_reward_relative_exact`, L19717）：对任意状态 s, s'，
```
Id (minus (dpo_implicit_reward pi_star s) (dpo_implicit_reward pi_star s'))
   (minus (reward s) (reward s')).
```

**证明概要**：基线项在差分中严格消去，因此相对奖励无偏。

**定理 5.6**（`dpo_reward_diff_is_log_ratio_diff`, L19802）：DPO 隐式奖励差分等于最优策略与参考策略对数比之差，差分形式下的等价性为 DPO 损失与 Bradley-Terry 偏好模型的一致性提供形式化基础。

**定理 5.7**（`dpo_total_loss_monotone`, L20181）：在有限偏好列表上（fold 求和，非数据集期望），总损失满足 **fold-plus 的泛单调性**：若对列表内每个偏好样本都成立 `le (dpo_pair_loss pi2 pref) (dpo_pair_loss pi1 pref)`，则 `le (dpo_total_loss pi2) (dpo_total_loss pi1)`——语句**不含 π*** 也**不含改进方向**（它只把逐对损失逐项不增抬升为 fold 求和不增；`dpo_pair_loss` L20111、`dpo_total_loss` L20153）。「π* 处总损失取显式闭式值」见 `dpo_total_loss_at_star`（L20171）；「沿策略改进轨道单调不增」是**聚合损失** `dpo_loss`（L19090）的性质（定理 5.10），勿与本节混淆。

**证明概要**：对偏好列表归纳（fold 结构归纳）：基例 `zero ≤ zero`；归纳步把逐点前提与归纳假设经 `le_plus_compat` 相加（L20187–L20189 起，约 10 步）。

**定理 5.8**（`real_dpo_loss_pi_star_bounded_both`, L42715）：Real 层 DPO 逐对损失在 `pi_star` 处满足**双侧定量界**——对任意赢/输样本 `s_w, s_l`，
```
real_lt (reward s_l) (reward s_w) ->
And (real_lt real_zero (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l))
    (real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
             (real_log (real_plus real_one real_one) real_two_pos)).
```
即 `r_l < r_w ⟹ 0 < L_DPO(π*, s_w, s_l) < log 2`。

**证明概要**：上界复用 `real_dpo_sigmoid_loss_bounded`；下界链为 `1 < 1+e^{−x}`（平移）→ `σ(x) < 1`（inv 反序 + inv 1 == 1）→ `log σ < log 1 == 0`（log 严格递增）→ `0 < −log σ`（opp 反向）→ 经 `real_dpo_loss_at_pi_star`（L42439）换形。`inv 1 == 1` 块内自证（`real_inv_one_local`，走 `real_inv_unique` 路线：`inv_pos_correct` + `real_mult_one` 两前提）。零新增公理、纯构造性、Set 层（`And` 为 Set 值）。

**定理 5.9**（`real_dpo_reward_recovers_up_to_baseline`, L42761）：DPO 隐式奖励恢复的 **Real 层复刻**——柯西实数层 `pi_star` 处隐式奖励精确恢复真实奖励（差配分基线偏移）：
```
real_eq (real_dpo_reward_explicit real_pi_star real_pi_star_pos s)
        (real_plus (reward s) (real_opp (real_mult beta (real_log Z_align Z_align_pos)))).
```
即 `β·(log π*(s) − log π_ref(s)) == r(s) − β·log Z_align`——抽象层定理 5.4（`dpo_reward_recovers_up_to_baseline`，基线恢复）的 Real 值域版（`real_dpo_reward_explicit` 定义 L42756）。

**证明概要**：`real_log_pi_star`（闭式解 log 形式）→ 消去 `log π_ref`（`real_plus_assoc`/`real_plus_comm`/`real_plus_opp` 抵消链）→ `real_distrib` 分配 → `β·opp(logZ) == opp(β·logZ)`（`real_mult_comm` + `real_opp_mult_r` 反向 + `RealSetoid.real_eq_opp_compat`）→ `β·((1/β)·r) == r`（`real_mult_assoc` + `real_inv_pos_correct` + 1·r）→ `real_plus_comm` 收口。零新增公理、纯构造性。

**定理 5.10**（`dpo_loss_iter_step_le`, L23244 / `dpo_loss_iter_mono`, L23256）：**聚合损失 `dpo_loss` 沿策略改进轨道单调不增**——把 DPO 从"π* 处损失有界"升级为"沿改进轨道损失动态单调"：
```
le (dpo_loss (pi_next pi_t pi_t_pos)) (dpo_loss pi_t)        （单步）
le (dpo_loss (projT1 (policy_iterate (S t) pi pi_pos)))
   (dpo_loss (projT1 (policy_iterate t pi pi_pos)))          （迭代轨道）
```
即沿相对 Boltzmann 改进算子 `pi_{t+1} := pi_next pi_t`（定理 4.5 的策略迭代），聚合损失（`dpo_loss := opp (align_objective)`，L19090）单调不增——与定理 4.7（间隙单调）互为对偶：`policy_improvement_mono` + `opp_le_compat` 一步组装，迭代版经 `policy_iter_norm` 保持归一化后逐点应用。零新增公理、纯构造性。

**定理 5.11**（Real 层 DPO logit 损失形状族）：单样本 DPO 损失 `ℓ(x) := −log σ(x)`（`real_dpo_logit`, L54982）的构造性形状刻画：

1. **softplus 连接**（`real_softplus_sigmoid_eq`, L55038）：`−log σ(x) == log(1+e^{−x})`——BT 损失与 softplus 形态的机器检查恒等（inv 对合 + `log(inv x) == −log x` + log 等价替换组装）；
2. **二阶导正性证据**（`real_sigmoid_deriv_mass_pos`, L55026）：`σ(x)·(1−σ(x)) > 0`——经典二阶导 `σ(1−σ)` 的构造性正性（`σ(x) > 0` 与 `1−σ(x) > 0`（L41819/L55017）正乘）；
3. **损失严格单调**（`real_dpo_logit_loss_decr`, L55075）：`x < y ⟹ ℓ(y) < ℓ(x)`——偏好 logit 越强损失越低（sigmoid 严格增 + log 严格增 + 取负反序），DPO 梯度下降收敛论证的单调前提。

诚实边界：完整 t-参数化凸性（Young/加权 Jensen）需要非 eps 的 `(a−b)² ≥ 0`（构造性边界：实数上三分不可判定）与 log 的 eps-连续性——二阶导正性证据与严格单调已机器检查闭合。零新增公理、纯构造性。

### 5.3 对齐审计与安全投影：审计 = KL 投影

贡献 3 把 DPO 恢复定理族定位为对齐审计的测量基座（DPO 隐式奖励是真实奖励的仿射像，定理 5.4/5.5）。本小节把审计的**作用形式**定理化：对策略分布做布尔安全过滤（拒绝集置零）+ 通过集上重归一化，恰为到通过分布的 **KL 投影**——机器检查主定理 `projected_distribution_minimizes_kl` 于库内 `Section KLProjection`（L95420 起；215/216/217/218/219 基底逐字未动，行号〔219 实测〕）。

**定义**（`Section KLProjection`，L95420）：安全过滤器为布尔谓词 `post_aud : S -> bool`（`true` = 通过）。给定参考分布 `p`（归一化 `Hp_norm`、逐点正 `Hp_pos`），通过集质量为
```
Z_aud := Σ_s (if post_aud s then p s else zero)              （L95442）
```
（`HZ : lt zero Z_aud` 保证通过集质量严格正），审计输出（投影分布）为
```
projected_distribution(s) := if post_aud s then mult (p s) (inv_pos Z_aud HZ) else zero   （L95446）
```
——在通过集上按 p 重归一化、在拒绝集上置零。库内已证：`projected_normalized`（L95476，投影分布归一化）、`Z_aud_le_one`（L95459，通过集质量 ≤ 总质量 1，p 归一化时 ≤ 1）。

**审计投影主定理**（`projected_distribution_minimizes_kl`，L95587）：对任意与审计兼容的分布 `q`（归一化 `Hq_norm`、逐点正 `Hq_pos`，且 `Hq_fail : forall s, Id (post_aud s) false -> Id (q s) zero`——q 在拒绝集上质量为零），只要 `HlogZ : le (log Z_aud) zero`：
```
le (relative_entropy q projected_distribution) (relative_entropy q p)
```
即 `KL(q‖proj(p)) ≤ KL(q‖p)`——审计不增加任意兼容分布 q 到 p 的 KL 代价（且按下方分解，在 `Z_aud < 1` 的意义下严格减少）。

**精确分解（审计的信息成本）**（`kl_sum_split`，L95527 + `kl_tail_eval`，L95551；`kl_minus_split`（L95498：`a−c == (a−b)+(b−c)`）为证明中的通用 R 层恒等式）：同一前提组下
```
relative_entropy q p == relative_entropy q projected_distribution + opp (log Z_aud)
```
即 `KL(q‖p) == KL(q‖proj) + (−log Z_aud)`——审计的 KL 代价恰等于通过集质量亏损的对数：`Z_aud ≤ 1`（`Z_aud_le_one`）且 `log Z_aud ≤ 0`（`HlogZ`）时 `−log Z_aud ≥ 0` 为审计的信息成本（通过集越小、被拒质量越多，成本越大）。

**诚实标注**：
- `HlogZ : le (log Z_aud) zero` 为定理**显式前件**（定理语句未改）。消解路线已闭合（219）：`Z_aud_le_one`（L95459，+ p 归一化 ⟹ `Z_aud ≤ 1`）+ log 单调 le 版（218 入根 `real_log_le_mono`，L112106：lt 支 `real_log_lt_mono` / eq 支 `real_log_wd` 逐支组装）+ `real_log_le_zero_of_le_one`（L112121，`Z ≤ 1 ⟹ log Z ≤ 0` 的直用形态）——见 §10.2 第 10 项 (e)；
- `Hq_fail` 语义须显式：主定理对**与审计兼容**的 q 成立（q 不含被拒质量），不声称无条件成立；
- 可选蓝图 `free_energy_with_audit_decomp`（把审计接入 §8 统一自由能视角的分解：`F[proj] == F[p] + (−log Z_aud)` 型）未实现（代码注释实录），列 §10.2 第 10 项 (e)；
- **DPO 审计桥（叙事组合，无新代码）**：定理 5.4/5.5（隐式奖励 = 真实奖励的仿射像）+ 本小节投影定理 ⟹ 对 DPO 模型执行安全过滤等价于对其隐式奖励诱导分布做 KL 投影——「DPO 恢复定理（审计的测量基座）+ KL 投影定理（审计的作用形式）」构成贡献 3 的双定理结构。

> 【对齐标注 2026-09-08 · 220 基态】本小节陈述的抽象层 KLProjection 块（L95420–95604）在 220 模块化基态下行号零平移（219 根逐字节未动）。追加层另有该定理族的 **Real 层实例化模块**（论文正文不消费、仅作实例面注记）：模块 `UpAuditBridge`（31 Qed，四关绿）——`real_minp_kernel_is_projection`（Min-P 截断核 = 到通过集的 KL 投影）、`real_minp_kl_cost`、`real_minp_projection_eps`，其 KL 方向与本节主定理一致：对**与截断兼容**的 q（被截集上质量为零，`Hq_fail` 同款语义显式保留）有 KL(q‖minp(p)) ≤ KL(q‖p)，精确分解同型为 KL(q‖p) == KL(q‖minp(p)) + (−log Z_kept)；配套 `UpMinP`（32 Qed）给出截断的熵刻画（`entropy_ge_neg_log_p_max`）与弃置质量界（`dropped_le_one_minus_exp_neg_S`/`dropped_le_one_minus_inv_n`）。二者属采样管道层实例（§9.2 第 6 项同口径），不改变 §2.3 scoped claim，亦不构成本节定理的新证明。

---

## 6 PPO 裁剪代理目标的静态性质：保守性与改进条件

**范围界定**：本章是 PPO 裁剪机制的抽象（结构）形式化，而非工程 PPO 算法的端到端验证。其边界有三：其一，代理目标与保守性定理对任意符号的优势函数成立（保守性指 clipped surrogate ≤ IS surrogate 的逐点上界性质，非统计学含义；定理 6.7 无前提），改进条件定理（6.3/6.4）则把步长可接受性化为 KL 惩罚的显式充分条件；其二，全部求和均在有限状态空间上精确进行，不含采样与 minibatch 估计误差；其三，重要性比率的分子固定为 `pi_star`（"单步向最优策略靠近"的受限设定），策略参数空间上的迭代优化不在本章范围内（见 §10.2）。三条边界的精确形态如下：

**边界声明一（代理目标形式）**：库内采用 `min(r, clip(r)) · A` 形式，而非标准 PPO 的 `min(r·A, clip(r)·A)`。区别在于 `min` 与优势 `A` 的运算次序：标准形式对任意符号的 `A` 均满足保守性；本形式在 `A < 0` 时不等号会反转。

**边界声明二（优势非负前提）**：库中 `advantage_nonneg : forall s, le zero (advantage_fn s)`（L19497）是显式声明的 Section 变量，定理 6.1 在该前提下成立，此时 `min(r, clip(r))·A` 与标准形式等价。实际 PPO 中优势函数可取负值，因此本定理刻画的是**优势非负的受限设定**，不是一般 PPO 的保守性。

**边界声明三（比率分子）**：`importance_ratio`（L19502）的分子是 `pi_star`，而不是标准 PPO 中可优化的当前策略 `pi_new`（后者在本库中未定义）。这是「单步向最优策略靠近」的受限设定，代理目标在给定 `pi_star` 下为常量；本工作不形式化策略参数空间上的迭代优化。

### 6.1 定义

PPO 在单步 bandit 设定下使用重要性采样比率：

```coq
(* L19502 *)
Definition importance_ratio (s : S) : R :=
  mult (pi_star s) (inv_pos (pi_old s) (pi_old_pos s)).

(* L19506 *)
Definition clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (minus one epsilon).

(* L19510 *)
Definition ppo_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
    (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))).
```

未裁剪 IS 目标为：

```coq
(* L19515 *)
Definition is_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
    (mult (importance_ratio s) (advantage_fn s))).
```

### 6.2 核心定理

**定理 6.1**（`ppo_conservative`, L19526）：在 `advantage_nonneg`（L19497），即 `forall s, le zero (advantage_fn s)`）与 `pi_old_pos` 下，
```
le ppo_objective is_objective.
```

**证明概要**：对每一点，由 `min_le_l` 得 `min(r, clip(r)) ≤ r`；由 `advantage_nonneg` 与 `pi_old_pos` 知乘因子非负，故逐点保序；再由 `sum_over_S_le` 提升为全局不等式。

（上述结论在 `advantage_nonneg`（L19497）下成立，该前提由 `End Section` 自动泛化为定理前件。）

**定理 6.2**（`exact_improvement_identity`, L19904）：
```
Id (minus (align_objective pi_new) (align_objective pi_ref))
   (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
          (mult beta (kl_to_ref pi_new))).
```

该恒等式将真实对齐目标改进分解为期望优势减去 KL 惩罚。

**定理 6.3**（`ppo_monotonic_improvement`, L19940）：若代理优势非负，即
```
le zero (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
            (mult beta (kl_to_ref pi_new)))
```
则 `align_objective pi_ref ≤ align_objective pi_new`。

**证明概要**：应用 `exact_improvement_identity` 将真实改进替换为代理优势，再利用代理优势非负得到结论。

**定理 6.4**（`kl_penalty_sufficient`, L19967）：若 `KL(pi_new‖pi_ref) ≤ eps` 且 `E_{pi_new}[A_ref] ≥ beta·eps`，则策略改进成立。该定理给出了 PPO 步长可接受的一个充分条件。

**定理 6.5**（`ppo_surrogate_raw_is_value_improvement`, L20720）：裁剪代理目标的改进与真实对齐目标改进满足显式恒等关系，即代理目标优化可直接控制策略价值改进。

**定理 6.6**（`real_ppo_conservative_eps`, L43556）：PPO 保守性的 **Real 层复刻（eps 化）**——柯西实数层裁剪代理目标不超过未裁剪目标加 eps 加权残差：
```
real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                   (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
        (real_plus (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s))))
                   (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))).
```
即 `ppo_objective ≤ is_objective + Σ π_old·(eps·adv)`——eps 加权残差形态：Real 层 `real_min` 只有 eps 界（`real_min_le_l_eps`），无精确 `min ≤ r`，构造性边界诚实标注。

**证明概要**：逐点 `min ≤ ρ+eps`（eps 界）→ ×adv（strict 正乘 `real_le_mult_compat`，前提 `real_advantage_pos`）→ 右分配（`real_mult_comm` + `real_distrib` 链）→ ×π_old（strict 正乘 + comm 换形）→ Σ 保序（`real_sum_over_S_le` 接口）→ `real_sum_over_S_add` 拆项 + ext（`real_distrib` 逐点）收口。诚实接口（零公理）：`real_sum_over_S_ext/le/add` + `real_advantage_pos`/`real_pi_old_pos`。

**定理 6.7**（`std_ppo_conservative`, L19559）：**标准 PPO 代理目标的无前提保守性**——`std_ppo_objective := E_pi_old[min(r·A, clip(r)·A)]`（L19553，标准形式）满足：
```
le std_ppo_objective is_objective.
```
**无需 `advantage_nonneg`**——`min(rA, clip(rA)) ≤ rA` 是 `min_le_l` 的定义性直接推论（裁剪项也在乘法内部，与优势符号无关），由此消除 §6 边界声明一「代理目标形式非标准」的限制（标准形式 `min(r·A, clip(r)·A)` 与 §6.1 的非标准形式 `min(r, clip(r))·A` 并存：前者无需符号前提，后者需 `advantage_nonneg`（定理 6.1））。库内同时具备：带自由变量 `pi` 的标准形式代理 `ppo_surrogate`（L19590，分子任意策略）、其**无前提**保守性 `ppo_surrogate_conservative`（L21209，`le (ppo_surrogate pi pi_old adv eps Hpi_old_pos) (is_objective_of pi pi_old adv Hpi_old_pos)`）与未裁剪对照的命名封装 `is_objective_of`（L19599）——「标准形式代理 + 无前提保守性」由此闭合。

**诚实边界（单侧闭合；反向不可闭）**：改进条件定理（6.3/6.4，对象为 `align_objective` 的改进，路线经 `exact_improvement_identity`（L19904））与裁剪代理 `ppo_surrogate` 之间缺口的**单侧**半边已由 218 基态入根的三件组合定理闭合（Section `PPOClipDecomp`，L112330 起）：E1 `ppo_is_decomp`（L112398）——IS 目标 `is_objective_of` == 裁剪代理 `ppo_surrogate` + clip 误差 `clip_error` 的**无前提恒等式**（逐点 `u == min(u,c) + (u − min(u,c))` 拆分 + `sum_over_S_add`）；E2 `clip_error_nonneg`（L112408）——clip 误差**非负**（min 在乘积内部，**无优势符号前提**）；E3 `ppo_clipped_improvement`（L112439）——裁剪代理非负 ⟹ 价值改进 `V(p_old) ≤ V(pi)`（E1 + E2 + 未裁剪 IS 恒等 `V(pi) − V(p_old)`（定理 6.5，L20720）+ 序代数）——「裁剪代理 + 保守性 + 改进条件」三件齐备的**单侧**形态由此机器检查闭合（219 实测：Section `PPOClipDecomp` 自 L112330、三件声明 L112398–L112439）。**反向界维持不宣称**：不存在常数 C 使「价值改进 ≤ 裁剪代理 + C·eps」型上界成立——比率无界（ρ → ∞）时 clip 误差 `A·(ρ − 1 − ε)` 无界（经典反例，源模块头注实录）。零新增公理、纯构造性。

**PPO 裁剪代理的两种形式与保守性定理覆盖范围（示意图，对应 §6.1 定义与定理 6.1/6.7）**：

```
设 r(s) := importance_ratio(s)（L19502，分子为 π*），clip(r) := r_max (min r (1+ε)) (1−ε)（L19506），
A := advantage_fn（L19496）。逐点形式：

非标准形式（库内 ppo_objective，L19510）        标准形式（库内 std_ppo_objective，L19553）
    min(r, clip(r)) · A                            min(r·A, clip(r·A))
        │                                              │
        │ 需 advantage_nonneg（A ≥ 0，L19497）        │ 无需 A 的符号前提（min 在乘积内部）
        ▼                                              ▼
定理 6.1 ppo_conservative（L19526）            定理 6.7 std_ppo_conservative（L19559）
  ppo_objective ≤ is_objective                     std_ppo_objective ≤ is_objective
  （前提：A ≥ 0 且 π_old > 0）                      （无前提；min_le_l 定义性直接推论）
```

**覆盖注**：定理 6.1 覆盖**非标准形式**（§6.1 的 `min(r, clip(r))·A`，需优势非负前提）；定理 6.7 覆盖**标准形式**（`min(r·A, clip(r·A))`，无前提），二者均以未裁剪 IS 目标 `is_objective`（L19515）为上界，即「裁剪代理 ≤ 未裁剪代理」的保守性。定理 6.1 与 6.7 的保守性本身**不**覆盖裁剪代理上的改进条件——该缺口的**单侧**闭合由 E1–E3 组合定理给出（`ppo_is_decomp`/`clip_error_nonneg`/`ppo_clipped_improvement`，218 基态入根，见上诚实边界）；改进条件定理（6.3/6.4）作用对象是真实对齐目标 `align_objective`（经 `exact_improvement_identity`），其与裁剪代理之间的组合通道现经 E1–E3 接通（单侧）。

**未覆盖区**：本示意图的未覆盖区 = 两列定理（6.1/6.7）的保守性覆盖之外、裁剪代理与价值改进之间的区域——其**单侧**半边已由 E1–E3 闭合（裁剪代理非负 ⟹ 价值改进，见上诚实边界与覆盖注）；**反向**半边（价值改进 ≤ 裁剪代理 + 常数·eps 型上界）在无界比率设定下为假（反例：ρ → ∞ 时误差无界），维持不宣称——该区未全覆盖是数学事实而非可闭缺口，与零新增公理、纯构造性的纪律一致。

---

## 7 GRPO：组相对优势的统计量

### 7.1 定义

GRPO 对同一问题采样一组输出 `Group`，奖励函数为 `reward_group : Group -> R`，组大小为 `group_size`，组均值为：

```coq
Definition group_mean : R :=
  mult (inv_pos (of_nat group_size) group_size_pos)
       (list_sum_g reward_group group_enum).
```

组相对优势定义为：

```coq
Definition grpo_advantage (i : Group) : R :=
  minus (reward_group i) group_mean.
```

**枚举假设（显式列出，`Section GRPO`，L23793 起）**：本节全部定理依赖以下 Section 变量与定义——`Group : Set`；`group_enum : list Group`；`group_cover : forall i : Group, InT i group_enum`（覆盖）；**`group_size` 定义为 `length group_enum`**（非独立假设）；`group_size_pos : lt zero (of_nat group_size)`；`reward_group : Group -> R`。两点诚实说明：其一，`NoDup group_enum` 当前**未**假设——若枚举含重复元素，组均值按列表计权（无重复前提的**不可去性**已机器检查定理化：双副本枚举在 indicator 求和下给质量 2 ≠ 1，见下），均匀均值解读即失效；把组均值解读为 `Group` 上的均匀均值需补无重复假设。该前提的计数刻画与均匀均值定理已在根落位——词表计数机器族（217 基态入根 `count_token`/`removeT`/`split_count_one` 等，对元素类型完全泛型——仅依赖可判定相等与 list 归纳）平移至 GRPO 枚举 + Set 层无重复前提（`nodup_g`）后的 B1–B3 已随 219 入根：`UpGRPO219.grpo_count_one`（L113775，覆盖 + 无重复 ⟹ 每元素恰计一次）、`UpGRPO219.grpo_indicator_sum_one`（L113793，indicator 求和 == 1）与 `UpGRPO219.grpo_uniform_mass`（L113832，组均值中每 delta_j 的质量恰为 1/G）；NoDup 前提不可去的双副本反例亦已定理化（`UpExtras219.counter_ex_indicator_sum_two`（L114140，双副本 indicator 求和 == 2 ≠ 1）/`UpExtras219.counter_ex_reward_sum_two_c`（L114151，双副本常数奖励总计 == 2c ≠ c））——见 §10.2 第 10 项 (b)。其二，实际 GRPO 常用标准化优势 `A_i = (r_i − mean)/std`；本节零均值定理对任意常数缩放成立（可取 `c = 1/std`）。population-std 下 `(1/G)·Σ A_i^2 = 1` 的单位二阶矩**全装配未入根**（开放计划，精化项）；其构造性 σ 见证核心已随 219 入根——`real_sqrt_exists`（L96475〔219 实测〕：`forall d, real_le real_zero d -> sigT (fun r => And (real_le real_zero r) (real_eq (real_mult r r) d))`，经 `exp(½·log d)` 拼装，Or 前提左支携带正间隙证书、右支给 r := 0 精确相等，217 基态入根）使 σ := √Var **可构造**：σ sigT 见证 `UpGRPO219.real_sigma_witness`（L113928，`0 < σ ∧ σ² == Var`）与投影 `UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`（L113948/L113953/L113961）随 219 入根，σ > 0 的正性证书与除法所需正性衔接由 sqrt 的 Or 形态供给（单位矩精化装配见 §10.2 第 10 项 (c)）。

### 7.2 核心定理

**定理 7.1**（`grpo_advantage_zero_mean`, L23915）：对任意缩放因子 `c`，
```
Id (list_sum_g (fun i => mult (grpo_advantage i) c) group_enum) zero.
```

**证明概要**：求和线性化后，`Σ(r_i − μ) = Σr_i − group_size·μ`；代入 `group_mean` 的定义并化简 `group_size·inv_pos(group_size)=1`，得到 `Σr_i − Σr_i = 0`。

**定理 7.2**（`grpo_variance_identity`, L24096）：**中心二阶矩恒等式**（组内平方偏差和 `Σ_i (r_i − μ)^2`，**未除以组大小 G**，故按下方术语说明不称"方差"——"方差"一词保留给归一化版本 `group_variance_identity`（L24264），见定理 7.3 与术语说明）：
```
Id group_centered_second_moment
   (minus group_raw_second_moment
          (mult (of_nat group_size) (mult group_mean group_mean))).
```

即：
```
Σ_i (r_i − μ)^2 = Σ_i r_i^2 − G·μ^2.
```

**术语说明**：标识符仍命名为 `grpo_variance_identity`，但严格而言本定理是**中心二阶矩恒等式**（或平方和恒等式），因为库内 `group_centered_second_moment`（L23972）定义为 `list_sum_g (fun i => mult (grpo_advantage i) (grpo_advantage i)) group_enum`，**未除以组大小 G**，故不是方差恒等式。**归一化版本亦已实现**：库内另有 `group_variance := mult (inv_pos (of_nat group_size) group_size_pos) group_centered_second_moment` 及其恒等式 `group_variance_identity`（Var == (1/G)·Σr² − μ²，由 `grpo_variance_identity` 两侧乘 inv(G) + `mult_minus_distr_l` 分配 + `inv_G_absorb` 消去推导，零 admit、纯构造性）。

**证明概要**：逐点展开 `(r−μ)^2 = r^2 − 2rμ + μ^2`（约 20 步构造性代数链，库内引理 `grpo_square_expand`），求和线性化，交叉项 `Σ r_i` 用零均值性质消去，最终合并为 `−G·μ^2`。

**定理 7.3**（`group_variance_le_raw_second_moment`, L24327）：**基线方差归约**——归一化组方差不超过原始二阶矩均值：
```
le group_variance
   (mult (inv_pos (of_nat group_size) group_size_pos)
         (group_raw_second_moment)).
```
即 `Var ≤ (1/G)·Σ r_i²`，归约量恰为 `μ²`（`group_variance_identity` 中 Var == (1/G)·Σr² − μ² 与平方非负 `square_nonneg` 组装）；这形式化了 GRPO 的核心动机"**组相对优势（减均值）降低二阶矩**"。

**证明概要**：`group_variance_identity` 给出 Var == (1/G)·Σr² − μ²；`grpo_le_minus`（0 ≤ b ⟹ a−b ≤ a，自证辅助）把减项消去；`square_nonneg` 为诚实接口 Variable（构造性有序域无三分律，通用平方非负需接口字段，同 NaturalGradient 模式），等号当且仅当组均值零（`square_zero` 双向夹另行证明）。另注：正向 eps 形式 `real_square_nonneg_eps`（L44842）已在 Real 层证明（`Qsquare_nonneg` 逐点成立 + 极限保 eps 余量），可作为该假设在 Cauchy 实数上的正向 discharge 证据。零经典、纯构造性。

**定理 7.4**（`real_grpo_advantage_zero_mean`, L43100）：组相对优势零均值的 **Real 层复刻**——柯西实数层：
```
real_eq (real_list_sum_g (fun i => real_mult (real_grpo_advantage i) c) group_enum) real_zero.
```
即 `Σ_i (r_i − μ)·c == 0`（对任意缩放 c）——抽象层定理 7.1 的 Real 值域版（`real_grpo_advantage`/`real_group_mean` 定义于 RealGrpoMain Section）。

**证明概要**：`Σ(r_i − μ) == Σr − Σμ`（`real_list_sum_g_minus`）→ `Σμ == G·μ`（`real_list_sum_g_const`，G := length group_enum）→ `G·μ == Σr`（`real_mult_assoc` + `real_inv_pos_correct` 吸收 G·(1/G) == 1 + 1·Σr 换形）→ `Σr − Σr == 0`（`real_plus_opp`）→ 主链（`real_mult_comm` 换序 → `real_list_sum_g_linear` 提取 c → `real_mult_zero` 收口）。基础设施：`real_of_nat`（nat→Real 嵌入）+ `real_list_sum_g` 族（ext/add/linear/opp/minus/const 六引理，归纳组装）+ `real_distrib_r_local`（右分配自证，避前向引用）。诚实接口（零公理）：`Group` 有限集 + `group_enum` + `group_cover`（InT 枚举覆盖）+ `real_group_size_pos` + `reward_group`。

---

## 8 统一视角：对齐即自由能最小化

四个算法族可纳入同一自由能框架：
- **RLHF**：最大化 `E_π[r] − β·KL(π‖π_ref)`，等价于最小化以 `−r` 为能量的自由能；最优解为 Boltzmann 分布。
- **DPO**：负对齐目标作为损失，隐式奖励恢复定理保证其最优解与 RLHF 一致。
- **PPO**：在参考策略附近用代理目标近似真实对齐改进，裁剪保证保守性，KL 惩罚保证改进条件。
- **GRPO**：组相对优势的零均值与中心二阶矩恒等式为基线估计提供无偏性与二阶矩控制。

库内定理 `rlhf_free_energy_kl`（L20290）将 RLHF 目标显式连接到自由能-KL 分解，构成统一视角的数学锚点。

---

## 9 形式化边界与前提

### 9.1 接口假设与实例化状态

本形式化依赖以下 `Variable`（诚实接口假设；**A/B/C 类打标**：按下文 §3.4 的编码给每项假设标注——A 类=接口字段（`RealInterfaceEnhanced` Class 字段）、B 类=Section 局部假设（待证明/discharge）、C 类=已证定理（该假设若已由 Real 层证据消解即入 C 类；可消解候选与已消解证据在条内注明）；下列清单以 A/B 类为主，C 类为各假设的消解状态，均在正文与 §9.2 标注）：
- `reward : S -> R`，`pi_ref : S -> R` 及其正性（`pi_ref_pos`，L18757）、归一化（`pi_ref_norm`，L18758）〔B 类：Section 局部假设，Real 层逐 eps 复刻时逐一实值化〕；
- `beta_pos : lt zero beta`（L18755）、`Z_align_pos : lt zero Z_align`（L18764；注：`Z_align_pos` 与 Real 层对应假设均为 Variable（Real 层 `Z_align_pos`（L42308））〔B 类：Section 局部假设；可消解候选（C 类方向）：同形状的 `Z_rel_pos`（L21253）路径表明，`Z_align_pos` 可由 `sum_over_S_pos` 型接口（L21245，Variable）与 `exp_neg_pos`（L182，接口字段）推出——即「消解」实为把该假设换成另一组接口假设，两假设的 Real 层实例化均待列表和正性回填（见 §9.1.1 的 exp_neg_pos 回填叙事：exp_neg_pos 已回填，列表和正性未回填）〕；
- `exp_neg_pos` 接口字段（L182）等实函数正性〔A 类：接口字段；已消解（C 类证据）：`exp_neg_positive`（L1872）已在语言模型实例中证明；Real 层通用字段已由 setoid 系接口实例回填（`exp_neg_pos := cauchy_real_exp_pos`，L39450，见 §9.1.1）；
- `log_differentiable`（L26365）等实函数可微性假设〔B 类：Section 局部假设（诚实接口字段，Real 层解析证明待闭合，见 §9.1.1/§10.2）〕；
- **策略迭代族（§4.3.1，支撑定理 4.5–5.10 全体）**：`sum_over_S_pos`（L21245）、`eta`/`eta_pos`/`eta_le_one`（L21240–L21242）、`step_kl_eta_bound`（L23114；升级后唯一诚实接口，旧 `step_kl_ratio`/`step_kl_ratio_pos`/`step_kl_ratio_bound` 三件套已退役）〔均 B 类：Section 局部假设；`step_kl_eta_bound` 为唯一剩余诚实接口，其 Real 层对应物已随 219 入根（`real_interp_Z_le_one_eps` L112890 / `real_step_kl_eta_bound_eps` L113142 等，放电种子 `real_exp_ge_linear_eps`（L40962，e^t ≥ 1+t）此前已在根；discharge 路线（特形坍缩为逐点 AM-GM）与入根清单见 §10.2 第 8 项）〕；
- PPO 中的 `pi_old`、`pi_old_pos`、`advantage_fn`（L19496）、`advantage_nonneg`（L19497）、`epsilon`（L19498）〔B 类：Section 局部假设〕；
- GRPO 中的 `reward_group`、`group_size_pos`〔B 类：Section 局部假设；`square_nonneg`（L24301）同列，Real 层正向证据 `real_square_nonneg_eps`（L44842）见 §7.2/§10.2 第 8 项；σ := √Var 的构造性见证核心已随 219 入根——`real_sqrt_exists`（L96475，217 基态入根）之上装配的 σ sigT 见证 `UpGRPO219.real_sigma_witness`（L113928）与投影三件（`UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`，L113948/L113953/L113961），见 §10.2 第 10 项 (c)〕。

这些假设对应于纸笔文献中通常默认的前提；显式声明它们是本库「诚实接口纪律」的一部分。

### 9.1.1 假设的封装方式

所有接口假设均以构造性方式封装，不构成隐藏公理：

1. `RealInterfaceEnhanced` 是 **Class**（L217），以 `Context {RI : RealInterfaceEnhanced}.` 引入（如 L347、L1285、L1456 等），不是顶层自由 `Variable`；
2. `End Section` 后 Coq 自动对 `RI` 泛化，接口字段成为定理的显式（隐式）前件；
3. 实证：Rocq 9.0/9.1 `Print Assumptions rlhf_optimal` 返回 **`Closed under the global context`**——零 Axiom、零未封装 Variable（对 `dpo_optimal`、`boltzmann_factor_pos`、`minp_markov_kernel_normalized` 审计结果相同）。

因此本工作的核心定理应读作：`forall {RI : RealInterfaceEnhanced}, <结论>`，即**对任意满足接口的实例成立**。

**接口与实例化**：本文定理在抽象接口 `RealInterfaceEnhanced` 上陈述。该接口的 setoid 对应物 `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid`（L40464，log 族带正性前提）已由具体柯西实数实例化为 `RealInterfaceEnhancedMod.RealEnhancedReal`（L41115），字段逐一取自 `Real` 层已证引理；同属 Setoid 系接口的基础版 `Real_RealInterfaceSetoidCore`（L33433）与完整版 `Real_RealInterfaceSetoid`（L39407）亦已装配（57 字段全实值）。**具体数学内容的 Real 层承载经两条路径实现**：其一是上述实例的字段回填（exp 族、log 族、度量与完备性全部实值化），其二是 **Real 层逐 eps 复刻**路径上对**部分核心定理**的直接证明（覆盖清单：定理 4.9、5.8、5.9、5.11 族、6.6、7.4——见 §1.2 贡献 7 与 §9.2；该路径上的 KL 不等式 `real_gibbs_inequality_eps`、log 可微性 `real_log_differentiable`、compose/entropy 可微性等是支撑复刻的 Real 层**基座引理**，而非核心定理镜像）——即本文抽象定理的数学内容在构造性实数上已有对应物。**可提取性**：全库定义均置于 Set 层：sigT/`And` 中的有理数序谓词一律使用 Set 值判定谓词 `QltT`/`QleT`，`And` 不实例化到 Prop；`real_mult`、`cauchy_real_exp` 等核心构造可提取为不含 Prop 残留的 OCaml 代码（提取验证在独立验证文件中完成）。本库使用自定义 Set 层合取 `And (A B : Set) : Set := A * B`（L68），非 Coq 标准的 Prop 层 `and`。**Artifact**：单文件库 ConstructiveWorld.v（**219 基态，114,222 行**，内容锚 SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`，.vo 锚 SHA-1 `B8838C418A2CD2719FC295FEA1A1B8224E020C21`，发布锚登记 anchors L13；同源归档快照 `演变\代码库归档\ConstructiveWorld-219.v`；历史基线：218 版 112,462 行 / SHA-1 `409A8F10BD09C90925EA51ADA2628B67022CB9F0`（归档 `演变\代码库归档\ConstructiveWorld-218.v`）、217 版 111,775 行 / SHA-1 `131A7318BC2D2BCC014D906A5E30A4FFA2E76B04`（217 staging 工作副本 `演变\.ablation\sc2_217_stage\ConstructiveWorld.v`）、212 版 79,608 行 / SHA-1 `0503C05B5E11916DA6C570D95FFECAFC4C3932DF`（归档 `演变\代码库归档\ConstructiveWorld-212.v`）、210 版 71,223 行 / SHA-1 `CA52225CAA6F2AE7EBE5E201AF8105FCEB3D04F4`），Rocq 9.1 编译通过（219：`coqc -Q . CW ConstructiveWorld.v` rc=0，.vo 已生成），仅依赖 Coq stdlib；全库禁词扫描 `Axiom / Admitted / Abort / Classical_Prop.classic` 零命中（全量而非抽样）；全部声明以 `Qed.`/`Defined.` 闭合（audit_full.ps1 三验：**2,930 处行首 Qed、51 处行首 Defined**，零 Abort）；批量 `Print Assumptions`（`Closed under the global context`）、`coqchk` 校验与提取 smoke test（旗舰链提取 OCaml 零类型级 `__`、ocamlc 4.14.2 通过、数值样例运行）随 artifact 脚本交付。**行号基底稳定性**：219 根前 112,462 行与 218 版逐字节一致（逐行 diff 零命中），故本文全部既有行号引用（均 < L112,462）原样有效，219 复核零平移（219 = 218 + 文件尾追加块 28–30，L112,463–114,222）；219 相对 218 的新增内容（L112,463 起：块 28 插值不等式 Real 层族（`real_exp_two_point_cvx_eps`（L112669）/`real_amgm_pointwise_eps`（L112817）/`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142），见定理 4.8 状态脚注与 §10.2 第 8 项）、块 29 GRPO NoDup 均匀化与 σ 见证族（Module `UpGRPO219`——`grpo_count_one`（L113775）/`grpo_indicator_sum_one`（L113793）/`grpo_uniform_mass`（L113832）/`real_sigma_witness`（L113928），见 §10.2 第 10 项 (b)/(c)）、块 30 前提不可去反例（Module `UpExtras219`——`counter_ex_indicator_sum_two`（L114140）/`counter_ex_reward_sum_two_c`（L114151），见 §10.2 第 10 项 (b)））；218 相对 212 的新增内容（L79,609 起：213/214 迭代新增内容、214-KL KLProjection 块（L95,420–95,604，§5.3 审计小节引用）、215 收口单位、块 22 AttnDoeblin（L95611–L96383）、块 23 AttnSqrt（L96386–L96641）、块 24 AttnHardLimit（L96643–L97866——218 补回 `eq_inv2_double`（L97558）与 TV 收口链 `tv_hard_le_decay_scale`（L97618）/`hard_attention_limit`（L97679），块 24 共 39 处 Qed，见 §10.2 第 9 项）、块 25–27（L112077–L112460，本文引用其中的 Real 层 log 单调 le 版族与 PPO clip 单侧误差族——`real_log_le_mono`（L112106）/`real_log_le_zero_of_le_one`（L112121）/`ppo_is_decomp`（L112398）/`clip_error_nonneg`（L112408）/`ppo_clipped_improvement`（L112439），见 §10.2 第 8/10 项）），本文引用其行号处均按 219 基态实测标注。**单文件设计决策**：单文件形态旨在保证零外部依赖与可审计的内容锚定（SHA-1），便于 artifact 复现与完整性核验；未来模块化重构将在抽象层签名对接（§10.2 第 0 项）完成后考虑。

> 【对齐标注 2026-09-08 · 220 基态】artifact 面现状（实测核验）：219 内容锚在模块化树中逐字节未动（本地 `CW_ConstructiveWorld_219.v` SHA-1 与本文登记一致，114,222 行），其上以**追加式工程模块化**组织维护基线——28 个独立模块（依赖拓扑三层：第 0 层 19 件 / 第 1 层 7 件 / 第 2 层 2 件，合计 625 处 `Qed.` 行），基座以信任缓存 .vo 直拷，逐模块 .vo 经内核校验（coqchk 29/29）；追加层另有单文件汇聚形态 `CW220_Extensions.v`（15,254 行，27 单元，553 处行首 Qed + 11 处 Defined，coqchk 通过，SHA256 14d4f48a…cee6）。两点口径须分清：其一，该模块化是**基座不动的工程打包**，不是本文未来工作所指「按语义边界切分基座」的重构，亦不是第 0 项的定理级签名迁移（两层口径依 §9.1.1 既有区分，不得混写）；其二，单文件全量拼接形态 `CW_ConstructiveWorld_220.v`（129,396 行）目前**仅为源码合并形态**——其全量编译未闭合，阻塞点为追加文本与基座吸收内容的顶层同名声明冲突（如 `sqrt_witness`，L114786）及同类跨件同名 8 件、Q_scope 泄漏、6MB 级编译的上下文阻塞（登记于 `docs/BLOCKERS-220.md`），该形态不得表述为「编译通过」。合并覆盖差：UpSLM（55 处 Qed）未入 Extensions/单文件，仅以模块化树形态交付。

`exp_neg_pos` 等字段的构造性实例化依赖正性链证明工作，其状态如下：

| 环节 | 状态 | 行号 |
| --- | --- | --- |
| `esq_eq_corr`（主恒等式） | **已证 `Lemma`** | L12837 → `Qed` L12868 |
| `exp_even_neg_pos` | 已证 | L12969 |
| `exp_partial_tail_pos` | 已证 | L13011 |
| `cauchy_real_exp_zero` | 已证 | L8348 |
| **`cauchy_real_exp_pos`（Real 层 exp 正性）** | **已证 `Lemma`** | L13383 |
| **setoid 系接口实例** | **已完成**：`Real_RealInterfaceSetoidCore`（L33433）/ `Real_RealInterfaceSetoid`（L39407）/ `RealEnhancedReal`（L41115），全部字段实值化（exp 族、log 族、度量与完备性） | L33433 / L39407 / L41115 |

即：该正性链全链（含 Real 层 `cauchy_real_exp_pos`）已闭合，为 `exp_neg_pos` 字段在具体 `Real` 上的实例化提供了完整的构造性材料；该字段经 setoid 系接口实例的字段回填（`exp_neg_pos := cauchy_real_exp_pos`，L39450）与 Real 层逐 eps 定理完成（见 §9.1.1 上文接口与实例化段，及正文定理 4.9、5.8、5.9、5.11 族、6.6、7.4 的 Real 层复刻）。

**Setoid 签名迁移的状态与影响**：本文定理的签名仍在抽象 Id 等式系接口 `RealInterfaceEnhanced`（Class，L217）上，其结论"对任意满足该接口的实例成立"（见本节上文）；`Real` 目前实例化的是 **req** 等式系 setoid 接口族（`Real_RealInterfaceSetoidCore`（L33433）/`Real_RealInterfaceSetoid`（L39407）/`RealEnhancedReal`（L41115），全部字段实值化），因此抽象定理**不直接**经 `RealEnhancedReal` 消费——定理与实例分属 Id/req 两套签名族，签名迁移（§10.2 第 0 项）正是要消除这一缝隙。

(a) **预计工作量（如实估）**：该迁移预计为**数人天–数周级的机械性工程**，无新数学内容、无预期逻辑障碍。工作量主体不是定理内容而是装配：把定理签名与证明链中的 `Id` 等式批量替换为 `req`，并逐一验证/补注册所用代数与序引理在 `req` 上的 Proper 兼容性（注册面规模取决于被定理链引用的引理数，见 (b)）。**迁移顺序建议**：按依赖序自底向上——先 §3 基座层（自由能分解、KL、有限和与逐点提升）定理，再 §4–§7 各算法族核心（每族以其 Real 层逐 eps 版定理 4.9/5.8/5.9/5.11 族/6.6/7.4 为语义对照），最后支撑性质与界引理。

(b) **主要摩擦点**：其一，`eq_ind`（Leibniz 归纳原理）在 `req` setoid 等价下的**消除受限**——`req` 非 Leibniz 等式，凡现证明链中以 `eq_ind`/Leibniz 等式消去（`rewrite` 直通）的步骤，在 `req` 下不能作 Leibniz 归纳，须改为 setoid 重写并依赖对应 Proper 实例；其二，`rewrite`→`setoid_rewrite` 的**自动化适配**——`req` 上下文中 `rewrite` 需换成 `setoid_rewrite`，且每个被重写位置须有 Proper/`req` 兼容实例，否则自动化停摆；其三，**Proper 实例注册面**——`RealSetoid` 上乘加、min/max、exp/log 与 `sum_over_S` 逐点提升、`le`/`lt` 对 `req` 的 Proper 实例需系统化注册（Q 层已有先例 `Qinv_comp_proper`（L8370）/`q_pow_comp_proper`（L8373），但抽象层定理链所引引理在 `req` 上的注册尚未铺开）。三者均为工程性适配，不涉及新的数学内容（与 §10.2 第 0 项一致）。

(c) **迁移完成后的可用性影响（诚实对比，不夸）**：现状——抽象定理的数学内容落到具体柯西实数上，目前经两条路径承载：req 系接口实例的**字段回填**（接口级事实，exp/log 族、度量与完备性字段在 `Real` 上实值）与**部分核心定理的 Real 层逐 eps 复刻**（清单见 §9.2）；逐 eps 复刻路径逐条证明，是"按定理逐个落数系"。迁移完成后——定理签名直接落在 req 系 setoid 接口上，可**直接经 `RealEnhancedReal`（L41115）实例化消费**其全字段回填，全库定理在具体柯西实数上统一直接可用，无需再为每条定理走逐 eps 复刻（逐 eps 版定理仍保留：实数序的 eps 余量形态是构造性表述的固有部分，两者并存而非互斥；迁移消除的是"每定理逐条复刻"的必要性，不改变任何定理的数学内容）。

**已验证的降压通道**：对个别卡在 Id→req 替换上的假设密集区，AttnDoeblin 模块提供了一条已验证的替代架构——「最小假设接口 + `sigT` 可满足性放电」：`real_expf_realizable`（L96364〔219 实测〕）把 expf 五字段迷你接口（pos/zero/plus/mono_lt/mono_le）整体放电到具体柯西实数 `cauchy_real_exp`（mono_le 经 `real_le = Or (real_lt) (real_eq)` 的构造性析取逐支组装，见 §4.3.1 放电注与 §10.2 第 10 项 (a)）。这使假设可先重述为迷你接口并在 Real 层放电，绕开全量 Proper 实例注册面——是迁移期的**缓解**而非替代（第 0 项的机械迁移仍是主线）。

### 9.2 不覆盖的内容

**实例化与承载路径（接口族细节见 §9.1.1 上文，此处不再重复叙述）。** 全库核验：Setoid 系接口 `Instance` 声明为 **3 处**——`Real_RealInterfaceSetoidCore`（L33433）、`Real_RealInterfaceSetoid`（L39407）、`RealEnhancedReal`（L41115，实例化 `RealInterfaceEnhancedSetoid`（L40464）），三者均属 Setoid 系接口（以 setoid 相等 `req` 与带正性前提的 `log_inv : forall x, lt zero x -> R` 表述），**全部字段已由具体 `Real` 实值化**。其余 14 处为 Section 内的 `Local Existing Instance RI_base` 超类解析注册与 Q 层 Proper 实例（`Qinv_comp_proper`（L8370）/`q_pow_comp_proper`（L8373）），不构成实数接口实例。Real 层承载路径为**部分核心定理的逐 eps 复刻**，其精确覆盖清单如下——**核心定理中已有 Real 层逐 eps 版本的**：定理 4.9（`real_rlhf_optimal_eps`，L43804）、5.8（`real_dpo_loss_pi_star_bounded_both`，L42715）、5.9（`real_dpo_reward_recovers_up_to_baseline`，L42761）、5.11（`real_dpo_logit` 族，L54982/L55026/L55038/L55075）、6.6（`real_ppo_conservative_eps`，L43556）、7.4（`real_grpo_advantage_zero_mean`，L43100）；KL 不等式 `real_gibbs_inequality_eps`（L41704）、log 可微性 `real_log_differentiable`（L46386）、compose/entropy 可微性等是支撑上述复刻的 **Real 层基座引理**（主文件 2,930 处行首 Qed〔219 基态实测；218 为 2,888、217 为 2,873、212 为 2,166〕，零 Axiom），**不是**核心定理本身的镜像。尚未有 Real 层版本的：唯一性（4.2）、间隙恒等（4.3/4.4）、策略迭代族（4.5–4.8、5.10）、GRPO 中心二阶矩/方差族（7.2/7.3）、DPO 相对精确（5.5/5.6）。**量化口径与阻碍分析（计数口径：族内多件按族计、5.11 族计为族，同 §1.2 贡献 7，不另立外部「核心定理总数」式计数）**：核心定理中 Real 层逐 eps 复刻覆盖 4.9/5.8/5.9/5.11 族/6.6/7.4（族内多件，如 5.11 族 4 件），未复刻 4.2/4.3/4.4/4.5–4.8/5.10/5.5/5.6/7.2/7.3。对未复刻各族的阻碍分析——均为**工作量/基建依赖型缺口，非逻辑障碍**：唯一性 4.2 的 Real 层复刻需 `gibbs_equality` 逐点化的接口装配；策略迭代族 4.5–4.8/5.10 依赖诚实接口 `step_kl_eta_bound`（L23114）的 Real 层解析证明（Real 层有限和 Jensen/Hölder 基建，见 §4.3.1 纸笔草图与 §10.2 第 8 项）；GRPO 方差族 7.2/7.3 依赖 `square_nonneg` 接口在 Real 层的装配（正向 eps 证据 `real_square_nonneg_eps`（L44842）已 Real 层证，见 §7.2）；DPO 相对精确 5.5/5.6 需 Real 层比例缩放（差分消去/基线抵消）基建；间隙恒等 4.3/4.4 的 Real 层形态属逐点化装配型工作量（Real 层 KL 分解接口与 eps 链模板已有，见定理 4.9/附录 C.2）。**量化分级**：上述缺口按阻碍性质分两级——(a) **纯装配/接口型工作量**（4.2/4.3/4.4/5.5/5.6/7.2/7.3：Real 层接口与 eps 链模板已有，闭合仅余逐点化装配，无新数学内容）；(b) **需新分析基建型（2026-09 复核后收缩为组装型）**（4.5–4.8/5.10：依赖诚实接口 `step_kl_eta_bound`（L23114）的 Real 层解析证明——原估需 Real 层有限和 Jensen/Hölder 基建、属数天–数周级新分析基建；设计复核表明最重种子 `real_exp_ge_linear_eps`（L40962）已在根，本几何插值特形坍缩为逐点 AM-GM + 求和保序的组装，接口的 Real 层对应定理（`real_interp_Z_le_one_eps` L112890 / `real_step_kl_eta_bound_eps` L113142）已随 219 入根（见 §10.2 第 8 项）；该族（4.5–4.8/5.10）的 Real 层迭代镜像仍为工作量型开放项）。全部缺口均判为工作量/基建依赖型，**无潜在逻辑障碍**（无证据表明存在原理性不可证）。这意味着：

- 本工作证明了「对任意满足接口的实例，RLHF/DPO/PPO/GRPO 定理成立」，而该接口的 setoid 对应物已由具体 `Real` 实例化（`Real_RealInterfaceSetoid` / `RealEnhancedReal`）；
- 上述清单中的部分核心定理另有 `Real` 层逐 eps 版本直接证明（见上），其余核心定理的 Real 层承载留待抽象层签名对接后的逐 eps 复刻（见 §10.2 第 0 项）。

因此本工作的准确定性是「**抽象接口层的形式化与部分核心定理的 Real 层逐 eps 复刻**」——抽象定理为结构性推演，其 setoid 对应物已实例化，部分核心定理在构造性实数上的逐 eps 对应物已独立证明。抽象层与实例层之间的签名对接为后续工程（见 §10.2）。

其余不覆盖的内容：

1. **神经网络近似**：策略 `pi` 是抽象函数，未绑定到 Transformer 参数化。
2. **连续动作空间**：当前形式化限定于有限离散状态/动作空间。
3. **样本复杂度与泛化界**：未涉及有限样本下的统计学习理论。
4. **经典逻辑结论**：所有存在性结论均为构造性；未与经典逻辑版本做等价比较。
5. **偏好数据集级损失**：`dpo_total_loss` 定义在**有限偏好列表**上（fold），不是数据集上的期望；未定义 `list Preference` 上的期望损失，也未形式化梯度下降的收敛性。
6. **采样管道层（与 217/218 基态新增块对应）**：注意力 softmax 的温度动力学与硬注意力极限属于采样管道层，**不是本文目标理论本体**——库内 217 基态入根的块 22 AttnDoeblin（有界 logits softmax 核的显式 TV 收缩族，L95611–L96383）、块 23 AttnSqrt（构造性平方根 `real_sqrt_exists`，L96386–L96641）、块 24 AttnHardLimit（词表计数/温度权重族，L96643–L97556；硬注意力 TV 收口链 218 补回，块尾至 L97866，39 处 Qed）均不改变本文 §2.3 scoped claim，本文定理的陈述与证明不消费它们；其与本文的关联仅为 §10.2 第 9 项的温度两极陈述（T→0 半边的 `hard_attention_limit` 现已在库内机器检查，见该项）与 §9.1.1 Artifact 段的行号基底记录。

   【对齐标注 2026-09-08 · 220 基态】220 模块化树在上述块之上追加的 28 个模块（治理与新算法层：改进声明宪法、熵防火墙、投影记账、逐出动力学、耗散币制、停时原语等，出处为圆桌实验与九条外推推导；模块清单与代表定理见 `docs/analysis/论文1-220基态-论文代码对应矩阵.md` 反向清单）同属**本文范围之外**——本文定理的陈述与证明不消费它们，scoped claim 不变。其中与本文相邻的仅有实例面注记两处：§5.3 的 Real 层审计实例族（UpAuditBridge/UpMinP，见该节对齐注）与 §10.2 第 9 项的温度窗口 T→∞ 半边（UpTempWindow，见该项对齐注）。

**注**：`dpo_total_loss_monotone`（L20181）的「总损失」实为有限偏好列表上的 fold 和（`dpo_total_loss`，L20153），非数据集期望；该定理只陈述逐对损失单调 ⟹ fold 和单调，**不含 π*** 亦**不含改进方向**——「沿改进轨道单调」是聚合损失 `dpo_loss`（L19090）的性质（定理 5.10，L23244/L23256）。保留原标识符以免破坏下游引用。

### 9.3 与 O'Connor 2008 等先例的关系

构造性分析学已有丰富先例（C-CoRN、NuPRL、O'Connor 2008）。本库的贡献不在于分析学本身，而在于将对齐算法优化理论置于构造性分析基座上，并揭示它们共享的自由能-KL 结构。本库 `Real` 与 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 独立构建、构造路径并行；未来工作将评估二者等价性，以促进社区复用与互操作。

**技术差异**：自建 `Real` 与既有构造性实数路线的差异集中在**实数表示与完备性证明策略**。本库 `Real` 采用**有理数 Cauchy 序列 + 逐点 eps 判定（Set 层 `QleT`/`QltT` 判定谓词）的收敛/完备性证明、并以 sigT 打包完备性见证**（存在性结论携带构造见证，见 §3.1/§9.1.1）；O'Connor 2008 采用**正则函数表示**（以 Lipschitz 界函数控制收敛的序列表示实数）；C-CoRN 采用 **C1 集/函数空间 + 代数完备化**的构造路线。三者差异是表示与完备性证明策略的选择，逻辑立场同为构造性（均不依赖排中律，见 §9.4 的经典解释相容性说明）。本库的表示选择服务于 Set 层可提取性（信息性证明可直接提取 OCaml，见 §9.1.1）与 eps 化接口消费（接口与定理以逐 eps 余量陈述，如定理 4.9/6.6 形态）——与 O'Connor/C-CoRN 的"另起炉灶"系表示工程与消费接口之差，而非分析学内容之差。

### 9.4 与经典逻辑版本的对比

对齐算法领域的主流分析以经典逻辑（含排中律与三分律）陈述。本节说明本库构造性版本与这类经典版本的关系，口径与 §9.2 项 4、§10.2 项 4 一致：

- **前提更强（显式化）**：经典证明常隐式假设分布正性、归一化、KL 有限性与函数可微性；本库把这些前提逐一显式声明为 Section `Variable` 或接口字段（§9.1），正性必须给出构造性见证（如 `pi_ref_pos`、`Z_align_pos`）。因此本库定理的假设集在表述上比经典文献更细、更显式。
- **结论在经典解释下成立**：纯构造性逻辑是经典逻辑的子系统——任何在构造性规则下完成的证明，其推导步骤亦均为经典逻辑接受的有效推导（经典逻辑仅在构造性公理之上增加排中律等，不删除任何可证命题）。故凡本库以抽象接口假设陈述并证明的定理，把接口前提原样读作经典实数分析（或任一经典意义下满足这些前提的结构）中的相应条件，其结论在经典解释下依然成立——本库结论的存在性均由显式 witness 给出（如闭式 `pi_star`、`policy_iterate` 的 sigT 打包），不依赖排中律的析取/存在形态，故不存在"构造性证明在经典解释下失效"的问题。
- **不作等价性主张**：上述"结论在经典解释下成立"是单向的（构造性可证 ⟹ 经典可证），本库**未**形式化经典逻辑版本，也未机器检查"构造性 ⟺ 经典"或经典 ⟹ 构造性的反向传递（后者一般需排中律，如实数三分，见 §9.2 项 4 与 §10.2 项 4）——读者不应把本库表述理解为对经典版本的等价比对或超越。
- **经典解释下可增强的形态**：若干以 eps 余量或诚实接口陈述的构造性边界（如 Real 层 `real_min` 只有 eps 界 `real_min_le_l_eps`（定理 6.6）、`square_nonneg` 为接口 Variable（定理 7.3））源于构造性有序域无三分律，且 `le` 以 `Or (lt) (req)` 编码、非严格序只能以逐 eps 余量陈述（接口实例化的语义说明，见 §9.1.1）。在经典解释下（三分律可用）这些可增强为精确形式；本库按构造性编码下可达的最强形式陈述，不把经典增强冒充为库内定理。

**例（`real_min_le_l_eps`；解释性实例，不新增任何机器检查断言）**：以 Real 层的 eps 余量界 `real_min_le_l_eps`（L40023，219 基态实测；定理 6.6 所引）为例说明上述原则。该引理陈述 `forall a b eps, real_lt real_zero eps -> real_le (real_min a b) (real_plus a eps)`——即 `min(a,b) ≤ a + eps`，**须带 eps > 0 的余量**（无精确 `min ≤ r`，见定理 6.6/附录 A 行）。经典解释下（三分律/排中律可用）同一事实可增强为精确形式：`forall a b, real_le (real_min a b) a`——`min(a,b) ≤ a` 恒真且无需 eps，因为经典逻辑可对「`a ≤ b` 或 `b < a`」作排中分支：前者 `min(a,b) = a`（精确等号成立）、后者 `min(a,b) = b < a`（严格小）。但该精确形式在**本库的构造性编码下不可达**：本库的 `le`/`real_le` 以 `Or (lt) (req)` 编码（需显式分支选择，见 §9.1.1 接口实例化说明），证明 `min(a,b) ≤ a` 必须交出显式析取见证——`min(a,b) < a`（需 `b < a` 的见证）或 `min(a,b) == a`（需 `a ≤ b` 的见证）；而「`a ≤ b` 还是 `b < a`」对构造性实数不可判定（序三分律缺失，判定 `x == 0` 之类无构造性判别程序），析取见证无法构造性产生。库内可达的最强形式因此是 `real_min_le_l_eps` 的 eps 余量形态：以 eps 吸收「分支不可判定」的缝隙。本库未形式化「精确版不可证」这一元理论判断（§9.4 为解释性说明），仅陈述库内可达形态——这正是本节的抽象原则：同一数学事实在经典解释下可精确陈述、在构造性编码下以 eps 余量陈述，二者不矛盾，本库只陈述后者。

**注**：本节为解释性说明，不新增任何机器检查断言；其内容不改变 §9.1–§9.3 的边界声明。

---

## 10 结论与未来工作

### 10.1 结论

我们给出了 RLHF、DPO、PPO、GRPO 的有限状态目标理论在 Coq 中的统一构造性机器检查形式化（在 §2.3 界定的范围内据我们所检索为首个）。所有核心定理均从 Cauchy 实数、Boltzmann 分布、自由能与 KL 散度的基座出发，零 Axiom、零 Admitted 地证明。该工作为对齐算法的安全关键部署提供了可审计的数学基础。

### 10.2 未来工作

（以下按优先级排列，第 0 项为最高优先。）

0. **抽象层签名对接**：把本文定理的签名迁移到接口的 setoid 对应物（`Real_RealInterfaceSetoid`（L39407）`RealEnhancedReal`（L41115），在单一签名下直接消费已装配的实例，使全库定理在具体数系上既有抽象陈述又有具体实例。该迁移预计为**机械性工程，无预期数学障碍**：主要工作量在于把定理签名与证明链中的 `Id` 等式批量替换为 setoid 等价 `req`，并逐一验证所用代数/序引理在 `req` 上的 Proper 兼容性（实例字段已全部实值化，见 §9.1.1）。潜在摩擦点包括 `Id` 等式对 `eq_ind`（Leibniz 归纳原理）的依赖在 `req` setoid 等价下的消除，以及 `rewrite` 在 `req` 上下文向 `setoid_rewrite` 的自动化适配；二者均为工程性适配，不涉及新的数学内容。****该迁移预计为**数人天–数周级的机械性工程**——工作量主体是 Id→req 批量替换与 Proper 实例注册面的逐一验证/补注册（无新数学、无预期逻辑障碍，如实估，不虚报）；**迁移顺序建议**：按依赖序自底向上，先 §3 基座层定理、再 §4–§7 各算法族核心（每族以 Real 层逐 eps 版为语义对照）、后支撑性质。**迁移完成后的可用性影响**：当前抽象定理不直接消费已装配的 req 系实例（定理与实例分属 Id/req 两套签名族，见 §9.1.1）；迁移后定理签名直接落在 req 系接口上，可经 `RealEnhancedReal`（L41115）直接实例化消费全字段回填，全库定理在具体柯西实数上统一直接可用。三要素详细版见 §9.1.1「Setoid 签名迁移的状态与影响」段。
1. **连续动作空间**：将有限状态分布扩展为连续空间上的测度形式化。
2. **神经网络参数化**：将策略函数绑定到具体神经网络架构，验证反向传播与对齐损失的组合。
3. **样本复杂度**：引入 PAC-Bayes / 信息论工具，给出有限样本下的泛化界。
4. **经典逻辑比较**：证明构造性版本与经典版本的等价性，便于与现有经典分析库互操作。
5. **由 exp 正性链实例化 `exp_neg_pos`（已闭合）**：主恒等式 `esq_eq_corr`（L12837）及收尾簇 `exp_even_neg_pos`（L12969）`exp_partial_tail_pos`（L13011）已证明，Real 层 `cauchy_real_exp_pos`（L13383）亦已闭合，exp 正性链至此完整；`exp_neg_pos` 字段已由 setoid 系接口实例回填（`Real_RealInterfaceSetoid`（L39407） 中 `exp_neg_pos := cauchy_real_exp_pos`），Boltzmann 分布的构造性基底已实例化——余下仅第 0 项的抽象层签名对接（消费该实例）。
6. **形式化真正的策略迭代**：补齐 `pi_new` 与策略参数空间，把 §6 的「单步向最优策略靠近」升级为带优化变量的 PPO 迭代。（注：归一化的 `group_variance` 及方差恒等式亦已实现，见 §7.2 术语说明。）
7. **诚实注记（前向/后向 KL 方向）**：定理 4.3 的次优间隙恒等 `J*−J(π) == β·KL(π‖π*)` 是**前向** KL（`relative_entropy pi pi_star`，L20554），定理 4.8 的几何收缩是**后向** KL（`relative_entropy pi_star …`，L23181）；两方向 KL 在单纯形上不可比（前向 KL 可无界，见 §4.3.1 定位注的 sR21 论证）。因此**目标间隙 `J*−J(π_t)` 的几何率不能由定理 4.3 与 4.8 直接组装**——其闭合需要 KL 强凸性/Pinsker 型材料（把 KL 间隙控到 TV 或二次下界），本文不主张该率已证，防过度声明。**辨析（勿与 §10.2 第 8 项混淆）**：第 8 项的坍缩（逐点 AM-GM）只针对 `step_kl_eta_bound` 的插值不等式 `Z ≤ 1`（向后 KL 递推的收口）；目标间隙几何率是另一回事（KL 强凸性/Pinsker 型传递），217 入根的有界 softmax 核 TV 收缩率 `(1−e^{−2Δ/T})ⁿ` 属采样管道层、与策略迭代轨道对象不同，**不构成**该传递——库内无 Pinsker 材料，两项均维持不主张。
8. **诚实接口 discharge 路线图**：对 §9.1 列出的剩余诚实接口给出排期口径与依赖方向。`step_kl_eta_bound`（L23114，策略迭代几何收敛定理 4.8 的唯一剩余诚实接口）：其 discharge 的 Real 层路线经设计复核重估——**原估算「需自建 Real 层有限和 Jensen/Hölder 基建（库内尚无）、数天–数周级新分析基建」已收缩**：放电链最重解析种子 `real_exp_ge_linear_eps`（L40962：`e^t ≥ 1+t` 的 Bishop 逐 eps 版，对全部 t 含负成立）**已在基线库内证明**（撰写时点未计入——见 §4.3.1 放电注）；插值不等式 `log Z ≤ 0` 的 Real 层证明在本几何插值特形坍缩为「exp 两点凸性（Varberg 锥论证，只消费该种子）+ 逐点 AM-GM + 求和保序（`real_sum_over_S_le/add` 既有）」三步——数学核与引理清单见 §4.3.1 Proof Outline 修订版；对应定理 `real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142）已随 219 入主库（连同支撑件 exp 两点凸性 `real_exp_two_point_cvx_eps`（L112669）与逐点 AM-GM `real_amgm_pointwise_eps`（L112817）；语句形态：自然数步进枚举 `seq 0 n` 载体 + 归一化 `real_eq` 前提（Σ==1）+ 显式证书前提（HZ/Hqv），路线见 §4.3.1 Proof Outline 修订版与定理 4.8 状态脚注），核心工作量由数天–数周级新分析基建**下调为天级组装并已完成**（数学真值另经 §4.3.1 纸笔证明确认——见定理 4.8 状态脚注；4.5–4.8/5.10 Real 镜像仍为开放项，本项不主张超出 eta-bound 对应物（M2）的范围）；217 另入根 `real_expf_realizable`（L96364，expf 五字段迷你接口在 cauchy_real_exp 上的 sigT 放电）供「exp 凸性接口化」的可选封装（`expf_convex` 字段，未入根）。`square_nonneg`（L24301，基线方差归约定理 7.3 的诚实接口）：其正向 eps 形式 `real_square_nonneg_eps`（L44842）**已在 Real 层证明**（见 §7.2）——**诚实落位为 Real 层镜像**：抽象层 discharge（把 Variable 换成已证引理）**不可行**——`le zero (a·a)` 的 Or 编码需分支见证，接口无三分/弱三分字段（构造性边界，§9.4 同源叙事）；可行路线是 Real 层 7.2/7.3 镜像定理 `real_group_variance_le_raw_eps`（`Var ≤ (1/G)·Σr² + eps`，经 `real_square_nonneg_eps` 装配；`real_grpo_centered_second_moment` 中心二阶矩恒等式的 Real 镜像为副产品）——未入根（草案）。两项闭合均不改变现有定理陈述（定理 4.8 的 `(1−η)^t` 上界与定理 7.3 的 `Var ≤ (1/G)·Σr²` 结论不变，见 §4.3.1/§7.2）。

9. **采样层的温度两极与硬注意力极限（诚实标注：属采样管道层，非本文目标理论本体，不改变 §2.3 scoped claim——§9.2 第 6 项）**：库内入根的两件采样层定理族（块 22/块 24；T→∞ 端与 T→0 端，L95611–L97866〔219 实测〕），为注意力 softmax 的温度动力学提供显式界。**T→∞ 端（有界 logits softmax 核的显式 Doeblin/TV 收缩，块 22 AttnDoeblin）**：`u_tv_contraction`（L95931——双点 TV 收缩 `tv(Kμ,Kν) ≤ (1−δ)·tv(μ,ν)`，参考分布只需归一化，免平稳性/免详细平衡/免 transition 非负前提）、`u_tv_iter`（L96019——几何率 `(1−δ)ⁿ`）、`bs_minorization`（L96286——显式 Doeblin 下界 `δ*·U ≤ K(s,·)`，δ* := `lo·lo` = `e^{−2Δ/T}`，经 `bs_lo_hi_eq`（L96181）精确化、无 eps 损耗）、`bounded_softmax_tv_contraction`/`bounded_softmax_tv_iter`（L96331/L96344——有界 logits（−Δ ≤ z ≤ Δ）softmax 核的收缩率 `(1−e^{−2Δ/T})ⁿ`）：T 增大则单步近全混合。**T→0 端（硬注意力极限，块 24 AttnHardLimit——218 补回收口链，已闭合）**：词表/计数机器（`count_token` L96860/`removeT` L96871/`split_count_one` L96992/`sum_pos_nonempty_aux` L97061 等）与温度权重定义（`factor_T`/`ZT`/`w_T`/`tv_hard`，L97146–L97177；`decay_T` := `e^{−γ/T}`，L97173）及 `vocab_len_pos`（L97540）自 217 入根；**218 补回 TV 收口链**——`eq_inv2_double`（L97558，根域自足化）、`tv_hard_le_decay_scale`（L97618，逐固定 T 的上界 `tv_hard T ≤ |vocab|·e^{−γ/T}`）与 `hard_attention_limit`（L97679：T→0 的 TV 收敛、**∃T₀ sigT 量词翻转**——`∀ eps>0, ∃T₀>0, ∀T（0<T<T₀）, tv_hard T ≤ eps`，Qed L97864）——**量词翻转已机器检查**，T→0 半边由「未闭合/闭合中」状态升格为库内定理（块 24 计 39 处 Qed）；可选温度窗口定理（`∃T₁T₂`：`T < T₁ ⟹ TV(w_T, δ_m) ≤ eps` 且 `T > T₂ ⟹ TV(w_T, U) ≤ eps`）的两半现已分别机器检查——T→0 半边即上述 `hard_attention_limit`（在根）；T→∞ 半边为 220 模块化树追加件 `UpTempWindow.temp_window_T_infty`（`∀eps>0, ∃T₂>0, ∀T>T₂, tv_unif T ≤ eps`，sigT 量词翻转；模块 70 处 Qed 四关绿，并收入 `CW220_Extensions.v`）。两半的 TV 极限对象不同质（δ_m 点质量 vs 均匀分布 U）、分居根与模块，「∃T₁T₂ 双端合一」的单一陈述未合成，仍属开放。**红线（与第 7 项同口径）**：上述 TV 层几何率**不构成**目标间隙 `J*−J(π_t)` 的收敛材料——目标间隙几何率需 KL↔TV 的 Pinsker 型传递，库内无此材料，TV 率仅作采样层独立陈述，不写入 §4.3.1 收敛主张。

> 【对齐标注 2026-09-08 · 220 基态】`temp_window_T_infty` 的 T→∞ 界同属本项采样层口径：其 TV 率仅陈述温度窗口半边，不与 §4.3.1 的策略迭代收敛主张组合（红线维持）；该件出自追加模块 `UpTempWindow`，其头注与防火墙件同口径自设边界（不主张 TV-熵传递），引用时应保留该前提语义。
10. **217/218/219 基态新增定理的 discharge 与消费路线（库内 219 实况——块 22/23/24 定理族、块 25/27 新入根件、块 28–30 随 219 新入根件与 §5.3 审计定理族的后续；除已注明入根者外均为开放计划（非已证））**：(a) **`step_kl_eta_bound` Real 层对应物**（旗舰 discharge——已随 219 入根：`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142）等四件，见第 8 项）；(b) **GRPO 均匀均值（NoDup discharge——已随 219 入根）**：`UpGRPO219.grpo_count_one`（L113775）/`UpGRPO219.grpo_indicator_sum_one`（L113793）/`UpGRPO219.grpo_uniform_mass`（L113832）（每元素在无重复枚举中恰计一次 ⟹ indicator 求和 == 1 ⟹ 每 delta_j 在组均值中质量恰为 1/G）已机器检查——构件（217 入根的词表计数机器族 `count_token`/`removeT`/`split_count_one`（L96992，唯一元素计数拆分）等，对元素类型泛型、仅依赖可判定相等与 list 归纳）平移至 GRPO `Group` 枚举 + NoDup（Set 层 `nodup_g`）前提后机械闭合；前提不可去反例已定理化——双副本枚举下 indicator 求和 == 2 ≠ 1 且常数奖励总计 == 2c ≠ c（`UpExtras219.counter_ex_indicator_sum_two`（L114140）/`UpExtras219.counter_ex_reward_sum_two_c`（L114151），§7.1 诚实注记的机器检查见证）；(c) **GRPO 标准化优势的单位二阶矩（方案 C——σ 见证核心已随 219 入根，单位矩全装配仍开放）**：`real_grpo_standardized_second_moment`（`∃σ>0`：σ² == 中心二阶矩 ∧ `(1/G)·Σ(A_i/σ)² == 1`）未入根；其构造性 σ 见证核心已入根——`real_sqrt_exists`（L96475）使 σ := √Var 可构造（Or 前提左支携带正间隙证书，恰与除法所需正性衔接），σ sigT 见证 `UpGRPO219.real_sigma_witness`（L113928：`forall Hvar : real_lt real_zero Var, sigT (fun sigma => And (real_lt real_zero sigma) (real_eq (real_mult sigma sigma) Var))`，Var 为组内中心二阶矩）与投影三件 `UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`（L113948/L113953/L113961）及四因子交换辅助 `UpGRPO219.real_mult_exchange`（L113872）随 219 入根；单位矩全装配（`(1/G)·Σ(A_i/σ)² == 1`，经 `inv_pos_mult_distr`（L95695）吸收 Var）为精化开放项（§7.1 注记同步）；(d) **PPO clip 单侧误差恒等式（方案 E——已随 218 入根，§6.2 诚实边界已改写）**：`ppo_is_decomp`（L112398，E1：IS 目标 == 裁剪代理 + clip 误差，无前提恒等式）、`clip_error_nonneg`（L112408，E2：无优势符号前提）与 `ppo_clipped_improvement`（L112439，E3：裁剪代理非负 ⟹ 价值改进——三件齐备的**单侧**闭合）已机器检查（组合：逐点恒等 `u == min(u,c) + (u − min(u,c))` + `sum_over_S_add` + 定理 6.5，无优势符号前提）；**反向界维持不宣称**——无界比率（ρ → ∞）下误差 `A·(ρ − 1 − ε)` 无界，无常数 C 使「价值改进 ≤ 裁剪代理 + C·eps」型上界成立（经典反例，源模块头注实录）；(e) **审计前提 discharge（§5.3 的 HlogZ——消解路径已闭合（219））**：`le (log Z_aud) zero` 的消解材料已随 218 入根——log 单调 le 版 `real_log_le_mono`（L112106：lt 支 `real_log_lt_mono` / eq 支 `real_log_wd` 逐支组装）与直用形态 `real_log_le_zero_of_le_one`（L112121：`Z ≤ 1 ⟹ log Z ≤ 0`），配既有 `Z_aud_le_one`（L95459，+ p 归一化 ⟹ `Z_aud ≤ 1`）与 `log 1 == 0`（`real_log_one`）——HlogZ 消解路径闭合；`free_energy_with_audit_decomp` 蓝图（审计接入 §8 统一自由能视角：`F[proj] == F[p] + (−log Z_aud)` 型）未实现；(f) **`Z_align_pos`（G4）与 `square_nonneg`（G5）的 Real 层镜像**：`Z_align_pos` 的 Real 层装配可经 `sum_pos_nonempty_aux`（L97061，非空表逐项正 ⟹ 和正，Real 层 list 形态）+ `cauchy_real_exp_pos` 平移；`square_nonneg` 的诚实落位为 Real 层镜像 `real_group_variance_le_raw_eps`（见第 8 项）——两件均未入根。

**模块化重构的优先级评估（建议性质，非已排期工程）**：单文件形态（114,222 行〔219 基态〕，见 §9.1.1 Artifact 段）保证零外部依赖与 SHA-1 内容锚定，但阅读/编译/合入的维护成本随库增长。**优先级取舍**：若把模块化拆分放在第 0 项签名迁移之前，可先行降低单文件维护成本，但拆分将增大签名迁移的跨文件追踪与 Proper 注册协调面（迁移为 Id→req 的全库机械替换，在单文件内一次成型最易审计与逐族回归，见第 0 项）；若把模块化拆分放在签名迁移之后，则可先在已锚定（SHA-1）的单文件上完成签名迁移与回归，再按稳定后的语义边界机械拆分，拆分不改变任何定理内容。**本稿建议维持「先签名迁移（第 0 项）、后模块化拆分」的现状顺序**——与 §9.1.1 单文件设计决策一致；模块化按「抽象层签名对接完成后按语义边界切分（§3 基座 / §4–§7 算法族 / §9 边界与实例）」启动，属路线图建议而非承诺排期。

> 【对齐标注 2026-09-08 · 220 基态】上文顺序建议按 220 实况修订表述：**追加式工程模块化已经落地**（基座信任缓存 + 28 个独立模块，逐模块编译与内核校验；见 §9.1.1 对齐注），其与本文所论「按语义边界切分基座」的重构、以及第 0 项签名迁移三者相互解耦——追加式打包不改动基座行号锚（本文引用面零平移），故不改变第 0 项在基座层的机械替换面；本文建议的「先签名迁移、后语义切分」顺序仅对后者仍然有效。`docs/BLOCKERS-220.md` 登记的单文件拼接阻塞不反证模块化路径，引用 artifact 时按「模块化树 + `CW220_Extensions.v`（27 单元）」口径陈述，缺件（UpSLM）如实标注。

---

## 参考文献

1. Peters, J., M"{u}lling, K., & Altun, Y. (2010). Relative Entropy Policy Search. *AAAI*.
2. Todorov, E. (2006). Linearly-solvable Markov decision problems. *NeurIPS*.
3. Schulman, J., Wolski, F., Dhariwal, P., Radford, A., & Klimov, O. (2017). Proximal Policy Optimization Algorithms. *arXiv:1707.06347*.
4. Rafailov, R., Sharma, A., Mitchell, E., Ermon, S., Manning, C. D., & Finn, C. (2023). Direct Preference Optimization: Your Language Model is Secretly a Reward Model. *NeurIPS*.
5. DeepSeek-AI. (2024). DeepSeekMath: Pushing the Limits of Mathematical Reasoning in Open Language Models. *arXiv:2402.03300*.
6. Geuvers, H., Niqui, M., & Wiedijk, F. (2000). Constructive Reals in Coq: Axioms and Categoricity. *TYPES*.
7. O'Connor, R. (2008). Certified Exact Transcendental Real Number Computation in Coq. *TPHOLs*.
8. Affeldt, R., et al. Infotheo / coq-proba: A Coq Library for Information Theory. *MathComp*.
9. Hölzl, J. (2016). Markov Chains and Markov Decision Processes in Isabelle/HOL. *Journal of Automated Reasoning*, 59(3), 345–387. https://doi.org/10.1007/s10817-016-9401-5
10. Hölzl, J., & Nipkow, T. (2012). Markov Models. *Archive of Formal Proofs*. https://isa-afp.org/entries/Markov_Models.html
11. Schäffeler, M., & Abdulaziz, M. (2021). Markov Decision Processes with Rewards. *Archive of Formal Proofs*. https://isa-afp.org/entries/MDP-Rewards.html
12. Schäffeler, M., & Abdulaziz, M. (2021). Verified Algorithms for Solving Markov Decision Processes. *Archive of Formal Proofs*. https://isa-afp.org/entries/MDP-Algorithms.html
13. Chevallier, M., & Fleuriot, J. (2021). Formalising the Foundations of Discrete Reinforcement Learning in Isabelle/HOL. *arXiv:2112.05996*. https://arxiv.org/abs/2112.05996
14. The mathlib Community (leanprover-community/mathlib4，持续更新). Mathlib.InformationTheory.KullbackLeibler（`klDiv`、Gibbs 不等式）与 Mathlib.MeasureTheory.Measure.Tilted（测度指数倾斜）. https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/KullbackLeibler/Basic.html
15. The Coq Development Team. Coq.Reals.Cauchy.ConstructiveCauchyReals（构造性 Cauchy 实数，Coq 8.12+ 标准库随附；Rocq 9.1 以 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 存留，环境实测 2026-09-03）. https://coq.inria.fr/doc/V8.12+beta1/stdlib/Coq.Reals.Cauchy.ConstructiveCauchyReals.html

---

## 附录 A：核心定理清单

| 定理 | 文件行号 | 内容摘要 | 前提/备注 |
|---|---|---|---|
| `rlhf_optimal` | L19049 | 对齐目标在 π* 处最大 | π 归一化且正（`normalized`/`positive_dist`）；接口前件 `beta_pos`/`Z_align_pos` 等 |
| `rlhf_optimal_unique` | L19128 | 最优策略唯一 | 同 `rlhf_optimal`（两策略均归一化且正） |
| `rlhf_suboptimality_gap` | L20554 | 次优间隙 = β·KL（前向 KL） | π 归一化且正；前向 KL 方向（与定理 4.8 的后向 KL 不同，见 §4.3/§10.2） |
| `rlhf_policy_improvement` | L20591 | 前向 KL 到 π* 不增 ⟹ 目标单调 | `p_old`/`p_new` 归一化且正；不含优势函数前提（勿与定理 6.3/6.4 混淆） |
| `policy_iter_backward_kl_step_le` | L22790 | 单步向后 KL 收缩上界：`KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1})`（定理 4.5 单步引理） | 策略迭代族 Section 变量：`eta_pos`/`eta_le_one`、`pi_t` 逐点正（§4.3.1） |
| `policy_iter_backward_kl_iter_le` | L22915 | 策略迭代向后 KL 加权递推上界（定理 4.5） | 同 `policy_iter_backward_kl_step_le`（迭代打包 `policy_iterate` 保归一化/正性） |
| `policy_iter_gap_diff` | L23000 | 间隙单步显式恒等式：改进量 == β·加权 KL 对（定理 4.6） | 同策略迭代族；`pi_t` 逐点正 |
| `policy_iter_gap_mono` | L23086 | 间隙单调不增（定理 4.7） | 同策略迭代族（经 `policy_improvement_mono`） |
| `policy_iter_kl_geom_step` | L23146 | 单步真几何收缩：`KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t)`（定理 4.8 前提，诚实接口 `step_kl_eta_bound`（L23114）下） | **诚实接口 `step_kl_eta_bound`（Variable，L23114）**；0 < η ≤ 1 |
| `policy_iter_kl_geom_iter` | L23181 | 向后 KL 真几何率上界 `(1−η)^t`（定理 4.8） | 同 `policy_iter_kl_geom_step`（诚实接口表述；接口的 Real 层对应物已随 219 入根——`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142），见 §4.3.1 状态脚注） |
| `real_rlhf_optimal_eps` | L43804 | RLHF 最优性 Real 层逐 eps 复刻（定理 4.9） | Real 层复刻；诚实接口 `real_kl_decomp_full` 等（零公理，全部可实例化） |
| `pi_star` | L18766 | 闭式最优策略（含 `opp`，即 e^{+r/β}） | 定义；依赖 `Z_align_pos` 正性前件（L18764） |
| `dpo_optimal` | L19096 | DPO 损失在 π* 处最小 | π 归一化且正（推论自 `rlhf_optimal` 取负） |
| `log_ratio` | L20880 | 对数几率比 log π − log π_ref | 定义；log 定义域隐含正性 |
| `dpo_loss_pair` | L20885 | 逐对 Bradley-Terry DPO 损失 | 定义 |
| `dpo_loss_at_pi_star` | L20892 | π* 处逐对损失 = 真实奖励差的对数几率 | 前提：`pi_ref` 正且归一化、`Z_align_pos`（π* 闭式） |
| `dpo_reward_is_implicit` | L19616 | 显式/隐式奖励逐点相等（命名桥引理：定义性后承，reflexivity；非独立结果） | 无前提（定义性后承，不计入并列贡献） |
| `dpo_reward_recovers_up_to_baseline` | L19626 | π* 处隐式奖励恢复真实奖励至基线 | 前提：π* 闭式（`log_pi_star`） |
| `dpo_reward_relative_exact` | L19717 | 隐式奖励差分 = 真实奖励差分 | 同 `dpo_reward_recovers_up_to_baseline`（基线消去） |
| `dpo_reward_diff_is_log_ratio_diff` | L19802 | DPO 隐式奖励差分 = 对数比差分 | 同 5.4（差分形式等价） |
| `dpo_total_loss_monotone` | L20181 | 逐对损失单调 ⟹ fold 总损失单调（不含 π*/改进方向） | 前提：逐对损失逐点不增（fold 泛单调；有限偏好列表） |
| `real_dpo_loss_pi_star_bounded_both` | L42715 | Real 层 π* 处损失双侧定量界：`r_l < r_w ⟹ 0 < L < log 2` | Real 层；前提 `r_l < r_w` |
| `real_dpo_reward_recovers_up_to_baseline` | L42761 | Real 层 π* 处隐式奖励恢复真实奖励至基线（定理 5.9） | Real 层复刻（定理 5.4 的 Real 值域版） |
| `dpo_loss_iter_step_le` | L23244 | 聚合损失 `dpo_loss` 单步沿改进轨道单调不增（定理 5.10） | 策略迭代族前提（同 4.5 区） |
| `dpo_loss_iter_mono` | L23256 | 聚合损失沿迭代轨道单调不增（定理 5.10） | 同 `dpo_loss_iter_step_le`（经 `policy_iter_norm` 保归一化） |
| `real_dpo_logit` | L54982 | Real 层单样本 DPO logit 损失 `ℓ(x) := −log σ(x)`（定理 5.11 定义锚） | Real 层定义 |
| `real_softplus_sigmoid_eq` | L55038 | Real 层损失形态连接：`−log σ(x) == log(1+e^{−x})` | Real 层恒等（无附加前提） |
| `real_sigmoid_deriv_mass_pos` | L55026 | `σ(x)·(1−σ(x)) > 0`（−log σ 二阶导的构造性正性证据） | Real 层（`σ(x)>0`、`1−σ(x)>0` 已证：L41819/L55017） |
| `real_dpo_logit_loss_decr` | L55075 | logit 损失严格递减：`x < y ⟹ ℓ(y) < ℓ(x)`（DPO 收敛单调前提） | Real 层；前提 `x < y` |
| `projected_distribution_minimizes_kl` | L95587 | 审计投影主定理：`KL(q‖proj(p)) ≤ KL(q‖p)`（§5.3；214-KL 块，219 复核未动） | 前提：`post_aud`/`Hp_norm`/`Hp_pos`/`HZ` + `Hq_fail`/`HlogZ`（显式前件；HlogZ 消解材料已随 218 入根——`real_log_le_mono` L112106/`real_log_le_zero_of_le_one` L112121，见 §10.2 第 10 项 (e)） |
| `kl_sum_split` | L95527 | 审计精确分解：`KL(q‖p) == KL(q‖proj) + (−log Z_aud)`（§5.3） | 同主定理前提组（尾项求值 `kl_tail_eval` L95551） |
| `ppo_conservative` | L19526 | 裁剪目标 ≤ 未裁剪目标（前提 `advantage_nonneg`（L19497） | **前提：`advantage_nonneg`（A ≥ 0，L19497）+ `pi_old_pos`** |
| `exact_improvement_identity` | L19904 | 真实改进 = 期望优势 − KL 惩罚 | 恒等（无附加序前提） |
| `ppo_monotonic_improvement` | L19940 | 代理优势非负 ⟹ 真实改进 | 前提：代理优势非负（`le zero (E−β·KL)`） |
| `kl_penalty_sufficient` | L19967 | KL 约束 + 优势条件 ⟹ 改进 | 前提：`KL ≤ eps` 且 `E ≥ β·eps`（定理 6.3 的显式 eps 形式） |
| `ppo_surrogate_raw_is_value_improvement` | L20720 | 代理目标改进控制价值改进（仅未裁剪代理） | 前提：`pi` 归一化且正、`p_old` 正；仅未裁剪代理（裁剪代理侧单侧组合 E1–E3 已于 218 入根，见 §6.2 诚实边界） |
| `real_ppo_conservative_eps` | L43556 | PPO 保守性 Real 层逐 eps 复刻（定理 6.6） | Real 层 eps 版；诚实接口 `real_min_le_l_eps` 等（`real_min` 无精确 `min ≤ r`） |
| `std_ppo_conservative` | L19559 | 标准 PPO 代理目标无前提保守性（定理 6.7） | **无前提**（`min(rA, clip(rA)) ≤ rA` 定义性；任意符号 A） |
| `grpo_advantage_zero_mean` | L23915 | 组相对优势零均值 | 前提：`group_enum` 覆盖（`group_cover`）、`group_size_pos`；任意缩放 `c` |
| `grpo_variance_identity` | L24096 | 组**中心二阶矩**恒等式（非方差，未除以 G） | 同 7.1（组枚举覆盖；未除 G，见 §7.2 术语说明） |
| `group_variance_le_raw_second_moment` | L24327 | 基线方差归约：`Var ≤ (1/G)·Σr²`（减均值降低二阶矩） | **诚实接口 `square_nonneg`（Variable，L24301）**；`real_square_nonneg_eps`（L44842）为 Real 层正向证据 |
| `real_grpo_advantage_zero_mean` | L43100 | GRPO 组相对优势零均值 Real 层复刻（定理 7.4） | Real 层复刻（定理 7.1 的 Real 值域版；`real_group_size_pos` 等） |

**补充陈述一**（`ppo_surrogate_raw_is_value_improvement`，L20720）：

```coq
forall (pi p_old : S -> R) (Hpos : positive_dist p_old) (Hnorm : normalized pi),
  Id (sum_over_S (fun s => mult (p_old s)
     (mult (policy_ratio pi p_old s (Hpos s)) (advantage p_old s))))
     (minus (state_value pi) (state_value p_old)).
```

即未裁剪代理目标的期望恰为状态价值改进量 `V(pi) − V(p_old)`（逐点消去 `p_old·(pi/p_old) = pi` 后由和的线性收口）。

**补充陈述二**（归一化方差恒等式 `group_variance_identity`，L24264）：`Var == (1/G)·Σ r_i^2 − μ^2`，其中 `Var := (1/G)·Σ (r_i − μ)^2`；由中心二阶矩恒等式（定理 7.2）两侧乘 `inv(G)` 经分配与逆元消去推得。


---

## 附录 B：间隙恒等与改进条件定理的代数推导

以下给出 `rlhf_suboptimality_gap`（L20554）与 `ppo_monotonic_improvement`/`kl_penalty_sufficient`（L19940/L19967）的完整代数骨架：B.1 补足 §4.3 定理 4.3 的证明概要；B.2 给出 §6.2 改进条件定理（6.3/6.4）的推导（**注**：RLHF 定理 4.4 `rlhf_policy_improvement`（L20591）走次优间隙恒等 ×2 路线，见 §4.3 正文，与本附录 B.2 的 `exact_improvement_identity` 路线无关——旧版误挂，已归位）。

### B.1 `rlhf_suboptimality_gap`

**目标**：`align_objective pi_star − align_objective pi == β · KL(pi ‖ pi_star)`。

推导：

1. 由 `rlhf_free_energy_kl`（L20290）把对齐目标改写为自由能形式：
   `align_objective p == −F[p]`（能量取 `−r`，温度为 `β`）。
2. 由 `free_energy_kl_decomp`（L16259）对 `p = pi`、Boltzmann 分布 `p_b = pi_star` 展开：
   `F[pi] == F[pi_star] + β·KL(pi ‖ pi_star)`。
3. 两侧取 `opp`，得
   `−F[pi_star] − (−F[pi]) == β·KL(pi ‖ pi_star)`，即
   `align_objective pi_star − align_objective pi == β·KL(pi ‖ pi_star)`。
4. 非负性由 `gibbs_inequality`（L16629）给出；`β > 0`（`beta_pos` L18755）保证间隙非负。

**要点**：该定理**不是**独立的新不等式，而是 `free_energy_kl_decomp` 在 RLHF 参数化下的一次移项重写。真正的数学内容已在 §3.3 的自由能分解中。

### B.2 `ppo_monotonic_improvement`（定理 6.3）与 `kl_penalty_sufficient`（定理 6.4）

**目标**：`E_{pi_new}[A_ref] − β·KL(pi_new ‖ pi_ref) ≥ 0` ⟹ `align_objective pi_ref ≤ align_objective pi_new`（定理 6.3，L19940）；其显式 `eps` 形式：`KL(pi_new‖pi_ref) ≤ eps` 且 `E_{pi_new}[A_ref] ≥ β·eps` ⟹ 同上（定理 6.4，L19967）。

推导（eps 形式；直接形式只需第 1、4 步）：

1. 由 `exact_improvement_identity`（L19904）：
   `align_objective pi_new − align_objective pi_ref == E_{pi_new}[A_ref] − β·KL(pi_new ‖ pi_ref)`。
2. 由 `β > 0` 与 `KL ≤ eps` 得 `β·KL ≤ β·eps`（`lt_mult_compat` / `le_mult_compat_weak`）。
3. 由假设 `E_{pi_new}[A_ref] ≥ β·eps ≥ β·KL` 得右端 `≥ 0`。
4. 故 `align_objective pi_new − align_objective pi_ref ≥ 0`，即改进成立（`le_minus_nonneg` 收口）。

**要点**：这是 `exact_improvement_identity` 与一次线性序传递的直接组合；`kl_penalty_sufficient`（定理 6.4）是 `ppo_monotonic_improvement`（定理 6.3）在显式 `eps` 条件（`KL ≤ eps`、`E ≥ β·eps`）下的重述。二者在数学内容上等价，保留两个陈述分别对应「恒等式形式」与「充分条件形式」的引用需求。

**归位注**：旧版把本推导挂于 `rlhf_policy_improvement`（定理 4.4）名下，与代码不符——定理 4.4 的前提是「新策略到 π* 的前向 KL 不增」（证明经次优间隙恒等 ×2 + β 保序，见 §4.3 正文），本附录推导的对象是 PPO 改进条件定理（6.3/6.4）。归因已按代码实况修正（212 复核：`rlhf_policy_improvement` 实测 L20591，与 210 一致；不依赖本附录的 `exact_improvement_identity` 路线）。

---

## 附录 C：Coq 证明骨架

> 本附录以「目标 → 关键引理 → 子目标 → 收口」的证明图形式，给出两个代表性定理的 Coq 层组装路径（tactics 级序列见代码库；此处给出关键引理调用链与每步的构造性要点，行号按 219 基态实测；policy 区 <L23275 行号 210/212/217/218/219 一致）。

### C.1 `policy_iter_backward_kl_step_le`（L22790）与 `policy_iter_kl_geom_iter`（L23181）的组装

**定理 4.5 单步引理 `policy_iter_backward_kl_step_le`（L22790）**：

- **目标**：`le (relative_entropy pi_star (pi_next pi_t pi_t_pos)) (plus (mult (minus one eta) (relative_entropy pi_star pi_t)) (relative_entropy pi_t (pi_next pi_t pi_t_pos)))`
- **关键引理**：恒等版 `policy_iter_backward_kl_step`（L22686）给出三 KL 精确分解
  `KL(pi*‖pi_{t+1}) == (1−η)·KL(pi*‖pi_t) − η·KL(pi_t‖pi*) + KL(pi_t‖pi_{t+1})`；
- **子目标 1**：可弃项非正——由 `gibbs_inequality`（L16629，KL ≥ 0）与 `eta_pos` 得 `le (opp (mult eta (relative_entropy pi_t pi_star))) zero`；
- **子目标 2**：恒等右端按环律重排（`plus_assoc`/`plus_comm`/`mult_comm`/`minus` 定义展开），使形如 `A == B + C` 且 `C ≤ 0`；
- **收口**：`le_plus_compat` + `plusA_opp_cancel_le` 型辅助（A == B + C、C ≤ 0 ⟹ A ≤ B）把恒等降为 le 版。

**迭代归纳 `policy_iter_kl_geom_iter`（L23181，定理 4.8）**（「归纳 + 代数」案例）：

- **目标**：`le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos))) (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi))`
- **归纳结构**：对 `t` 归纳；基例 `t = 0` 由 `policy_iterate` 定义与 `refl`/`le` 自反闭合；
- **归纳步（t → S t）**：
  - 关键引理 1：单步真几何收缩 `policy_iter_kl_geom_step`（L23146）——`KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)`，其内部把 C.1 的 le 版递推与诚实接口 `step_kl_eta_bound`（L23114，`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`）组合，两 η 项抵消（`plusA_opp_cancel_le` 收口）；
  - 关键引理 2：归纳假设 IH：`KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`；
  - 子目标：两侧乘 κ := 1−η——κ ≥ 0 由 `le_minus_nonneg`（前提 `eta_le_one`）保证，保序乘用 `le_mult_compat_weak`，`mult_comm` 换形把因子放右端；
  - 关键引理 3：`r_pow` 结合律换形（`r_pow κ (S t)` 展开为 `mult κ (r_pow κ t)`，`mult_assoc` 归位）；
- **收口**：序传递链：`KL(pi*‖pi_{t+1}) ≤ κ·KL(pi*‖pi_t) ≤ κ·(κ^t·KL(pi*‖pi_0)) == κ^{S t}·KL(pi*‖pi_0)`（`le` 传递性 + `r_pow` 结合换形）。

### C.2 `real_rlhf_optimal_eps`（L43804）的 Real 层 eps 证明模板

**目标**：`real_le (real_opp (real_free_energy pi Hpi)) (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)) (real_mult D eps))`，即 `J(π) ≤ J(π*) + D·eps`。

- **关键引理 1（常数消去桥）**：诚实接口 `real_kl_decomp_full`（L43730）把熵侧 KL 分解的常数差吸收进 `D`（`F(p) == F(p_b) + D·Σkl` 型），避免逐项常数额外 eps；
- **子目标 1（逐点抵消链）**：`log p == log p_b + kl_term` 逐点展开，经 Σ ext + `real_sum_over_S_add` + `real_kl_term_equiv` 把 KL 项收拢为 `Σkl`；
- **关键引理 2（KL ≥ 0 的 eps 版）**：`real_gibbs_sum_eps`——Real 层 KL 非负只有 eps 余量形式 `le zero (plus Σkl eps)`（构造性边界：非严格序不可判定，Real 层序关系以逐 eps 余量陈述）；
- **子目标 2**：`D` 正乘（`real_le_mult_compat` + comm 换形）把 `0 ≤ Σkl + eps` 提升为 `0 ≤ D·(Σkl + eps)` 的加权余量；
- **关键引理 3**：`le_plus_compat` 把 `F(p_b) ≤ F(π) + D·eps` 与自由能分解接口合并；
- **收口**：`real_opp_le_compat` 取负并消环恒等（`A == (A + opp C) + C` 型），得 `real_le (real_opp F(π)) (real_opp F(p_b) + D·eps)`。

**模板要点（"eps/3" 结构的库内实例）**：本定理的 eps 余量**只在 `real_gibbs_sum_eps` 一步引入一次**，并由常数 `D` 加权成 `D·eps` 的单一残差（证明体内无三分 eps 的必要——误差源唯一）。「eps/3 分割」式模板对应的是多误差源组合的证明（如逐点 log 抵消与 gibbs 各自带余量的情形）；库内 `real_rlhf_optimal_eps` 是 eps 余量链的**最简形态**，其「单点引入 → 正乘加权 → le_plus_compat 组装 → 取负收口」骨架与定理 6.6（`real_ppo_conservative_eps`，L43556）同型。

---

## 附录 D：artifact 验证脚本与复现步骤

> 本附录给出正文 §9.1.1 Artifact 段所引验证的真实脚本路径与复现步骤（219 基态，2026-09-06 复核；所有路径相对仓库根 `D:\ComplexAnalysis\ConstructiveWorld`，主文件 `ConstructiveWorld.v`（219：114,222 行，SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`，.vo 锚 `B8838C418A2CD2719FC295FEA1A1B8224E020C21`，anchors L13）；历史基线的同类归档为 218 快照 `ConstructiveWorld-218.v`（`演变\代码库归档\ConstructiveWorld-218.v`，SHA-1 `409A8F10BD09C90925EA51ADA2628B67022CB9F0`）、217 快照 `ConstructiveWorld-217.v`（SHA-1 `131A7318BC2D2BCC014D906A5E30A4FFA2E76B04`，217 staging 工作副本 `演变\.ablation\sc2_217_stage\ConstructiveWorld.v`）、212 快照 `ConstructiveWorld-212.v`（`演变\代码库归档\ConstructiveWorld-212.v`，SHA-1 `0503C05B5E11916DA6C570D95FFECAFC4C3932DF`）与 210 快照 `ConstructiveWorld-210.v`，SHA-1 `CA52225CAA6F2AE7EBE5E201AF8105FCEB3D04F4`）。

1. **audit_full.ps1 三验（行首闭合标记 + 禁词扫描）**：脚本位于 `演变\.ablation\规划\audit_full.ps1`（单文件，无外部依赖）。复现：`pwsh -File 演变\.ablation\规划\audit_full.ps1 -Path ConstructiveWorld.v -Label 219`，输出口径 `lines=114222 Qed=2930 Defined=51 Admitted/admit=0 Axiom=0 Abort=0` 与桥引理计数（2,930 与 51 为两项独立行首计数，不可相加，见 §9.1.1 Artifact 段）。
2. **`Print Assumptions` 批量探针**：探针文件与断言脚本位于 `演变\.ablation\sc2_parallel\sL_assumptions\`（`probe_full.v` 为 81 条主定理/主定义的 `Print Assumptions` 探针源；`R2.5-断言脚本-草案.ps1` 为 CI 化断言脚本：生成探针 → `coqc` 编译（`-Q` 映射仓库根为 `CW`）→ 扫描 log 断言无 `Axioms:` 非空段；`parse_pa_log.ps1` 为 log 解析器）。批量结果与判定规则文档：`演变\.ablation\sc2_parallel\sL_assumptions\R2.5-PrintAssumptions-基态198-20260903.md`——基态 198 完成 81/81 CLEAN（`Closed under the global context`），基态 206 复核确认；212–219 未整体重跑该 81 条批量（如实——207–219 新增内容经行首零命中 + `coqc` rc=0 + 编译通过维持，口径同 210 批先例；判定规则以该 R2.5 文档与 §9.1.1 Artifact 段为准）。
3. **提取验证（Set 层可提取 OCaml）**：迭代 210（历史基线）的提取探针 `演变\.ablation\sc2_210_final\probe_210.v`（`Extraction Language OCaml`，输出目录同目录，提取 `real_mult`/`cauchy_real_exp`/`cauchy_real_sin`/`cauchy_real_cos` 等旗舰链），编译产物 `probe_210.ml`/`probe_210.mli` 已生成（`coqc -Q . CW probe_210.v`，log 见 `probe_210.log`）——该探针及目录名为 210 基态历史事实，当前基线 219 的同类复核（旗舰链提取零类型级 `__`、`ocamlc` 通过、数值样例运行）随 artifact 脚本与 rc=0 交付；历史更早基线的同类探针 `演变\.ablation\sc2_202_b1\probe_202.v`（产物 `probe_202.ml`/`.mli`，基线 202）亦可作对照。ocamlc 4.14.2 编译与数值样例运行步骤随 artifact 交付（脚本化复核口径：旗舰链提取 OCaml 零类型级 `__`、`ocamlc` 通过、数值样例运行）。**`__` 语义说明**：Coq 提取 OCaml 时，`__` 占位符通常对应不可计算/被擦除的内容——典型为 Prop 层证明残留或依赖不可计算字段的类型。旗舰链提取结果中**零类型级 `__`** 表明这些构造不含 Prop 残留，即 Set 层信息性证明（sigT/`And` 见证）成功提取为可执行 OCaml 代码（§9.1.1 可提取性段）。
4. **编译命令（独立环境复现）**：仓库根执行 `coqc -Q . CW ConstructiveWorld.v`（Rocq 9.0/9.1，RC=0，约 3–5 分钟）；`coqchk` 校验与全库禁词全量扫描（`Axiom / Admitted / Abort / Classical_Prop.classic` 零命中）随同一 artifact 链交付。**红线**：所有探针只 `Require + Print Assumptions`/`Extraction`，不修改源文件；`coqc` 输出以重定向（`*>>`）落 log，不走管道（沙箱边界，见断言脚本头部注释）。
5. **一键复现路径（部分执行）**：一键复现 = 依序运行 (i) **audit_full.ps1 三验**（本条第 1 项）与 (ii) **根探针三连**——**内容 Check**：`演变\.ablation\sc2_210_final\check210.v`（`Require Import CW.ConstructiveWorld` + 关键引理/定义 `Check`，210 快照关键符号在位核验；文件名与目录为 210 基态历史事实，219 基态下 `check210.v` 直接 `Require` 当前根 `ConstructiveWorld.v`（219）作同型核验亦可）；**`Print Assumptions` 探针**：`演变\.ablation\sc2_parallel\sL_assumptions\`（本条第 2 项，`probe_full.v` + `R2.5-断言脚本-草案.ps1`）；**提取探针**：`演变\.ablation\sc2_210_final\probe_210.v`（本条第 3 项，210 基态历史目录）。四项均照本条第 1–3 项的命令与口径执行、`coqc` RC=0 即复现成功。把该步骤链封装为单一 `make audit` 命令（makefile/dune 集成，供 CI 复用）属工具侧任务，由库维护方另行产出——本版先给出手工可逐条执行的路径链。

6. **【对齐标注 2026-09-08 · 220 基态】模块化树复现路径（220 起的维护基线）**：仓库 `ConstructiveWorld-Main\`。① 锚核验：`ConstructiveWorld_Live\CW_ConstructiveWorld_219.v` 的 SHA-1 应为 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`（114,222 行）——与本文 §9.1.1 登记锚一致，保证全部行号引用有效；② 拓扑序增量编译：`ConstructiveWorld_vo\` 内 `bash build.sh`（.vo 已存在则跳过；基座 .vo 为信任缓存直拷，不在后台上下文全量重编）；③ 单模块重验：`coqc -Q . "" Up<Name>.v`；④ 内核校验：9.0 平台 coqchk（注意 .vo 不可跨构建复用、一律从 .v 重建）；⑤ 追加层单文件 `releases\CW220_Extensions.v`（553 处行首 Qed + 11 处 Defined，SHA256 14d4f48a…cee6）可独立按第 1 项口径三验；⑥ **禁入项**：单文件拼接形态 `releases\CW_ConstructiveWorld_220.v` 的全量编译未闭合（顶层同名声明冲突等，登记于 `docs/BLOCKERS-220.md`），不得用作复现入口。本文正文引用仍以 219 锚为唯一行号基准（零平移）。

---

*版本注记（2026-09-06 · 218 基态同步）：基线库更新至 218（112,462 行 / 行首 Qed 2,888 / Defined 51 / 零 Axiom；内容锚 SHA-1 409A8F10BD09C90925EA51ADA2628B67022CB9F0，.vo 锚 E653CA828ECA6DE56FFCB35714E008F3484C6132，anchors L12；既有行号引用零平移）。随 218 入根并落位本文：PPO clip 单侧误差恒等式三件（ppo_is_decomp L112398 / clip_error_nonneg L112408 / ppo_clipped_improvement L112439）把 §6.2 诚实边界改写为「三件齐备（单侧）+ 反向不可闭反例」；Real 层 log 单调 le 版两件（real_log_le_mono L112106 / real_log_le_zero_of_le_one L112121）闭合 §5.3 的 HlogZ 消解路径（§10.2 第 10 项 (e)）；块 24 TV 收口链补回（eq_inv2_double L97558 / tv_hard_le_decay_scale L97618 / hard_attention_limit L97679，块 24 共 39 处 Qed）使 §10.2 第 9 项 T→0 半边升格为库内定理。§4.3.1 状态脚注与 §10.2 第 8 项登记 Real 层核心不等式在未合入主库的先行件中的机器闭合（41 处 Qed）。审计数字、行号基底声明与附录 D 复现口径按 218 复核更新（R2.5 81 条批量未整体重跑，如实）。*

---

*版本注记（2026-09-06 · 219 基态同步）：基线库更新至 219（114,222 行 / 行首 Qed 2,930 / Defined 51 / 零 Axiom；内容锚 SHA-1 7BBE42EA83D178901C94FA13FB18E0A3B975D09A，.vo 锚 B8838C418A2CD2719FC295FEA1A1B8224E020C21，anchors L13；219 = 218 + 文件尾追加块 28–30，全部既有行号引用零平移）。随 219 入根并落位本文：step_kl 诚实接口的 Real 层对应定理族（净名：exp 两点凸性 real_exp_two_point_cvx_eps L112669 / 逐点 AM-GM real_amgm_pointwise_eps L112817 / 插值不等式 real_interp_Z_le_one_eps L112890 / eta-bound 对应定理 real_step_kl_eta_bound_eps L113142，自然数步进枚举载体 + 归一化 real_eq 前提 + 显式证书 HZ/Hqv）——§4.3.1 状态脚注、discharge 注、Proof Outline 与 §10.2 第 8 项由「未合入主库的先行件（41 处 Qed）」改写为入根事实（定理 4.8 抽象层陈述不变）；GRPO NoDup 均匀化 B1–B3（UpGRPO219.grpo_count_one L113775 / grpo_indicator_sum_one L113793 / grpo_uniform_mass L113832）与其前提不可去双副本反例（UpExtras219.counter_ex_indicator_sum_two L114140 / counter_ex_reward_sum_two_c L114151）落位 §7.1 注记与 §10.2 第 10 项 (b)；σ sigT 见证族（UpGRPO219.real_sigma_witness L113928 / proj_sigma 三件 L113948–L113961）落位 §7.1 注记与 §10.2 第 10 项 (c)（单位矩全装配仍开放）。审计数字、行号基底声明、Artifact 段新增块清单与附录 D 复现口径按 219 复核更新（R2.5 81 条批量未整体重跑，如实；行号全部 219 实测）。*


---

> *版本注记（2026-09-08 · 220 基态同步，分析席对齐稿）：本文自本稿起增加「对齐版」形态（母版 `演变\相关论文\论文1-构造性ML对齐统一形式化-中文规范版.md` 原样保留、零改动）。基线库维护形态更新为 220 模块化基态（`ConstructiveWorld-Main\`：基座 `CW_ConstructiveWorld_219` 信任缓存 + 28 个独立模块，逐模块 .vo 内核校验 coqchk 29/29；追加层单文件 `CW220_Extensions.v` 553 处行首 Qed + 11 处 Defined、coqchk 通过）。锚核验实测：219 内容锚 SHA-1 与本文 §9.1.1 登记逐字一致，本文全部行号引用在 220 基态下零平移（抽验 77 处定理/定义/Section 锚全部行号精确命中）。本稿改动了八处（摘要、§2.3、§5.3、§9.1.1 Artifact 段、§9.2 第 6 项、§10.2 第 9 项、§10.2 模块化评估段、附录 D 第 6 项），均以【对齐标注】标明依据：摘要与 §2.3（维护形态口径，scoped claim 四点界定不变）、§5.3（Real 层审计实例面注记，KL 方向与 Hq_fail 语义显式）、§9.1.1 Artifact 段（220 基线口径与单文件阻塞表述）、§9.2 第 6 项（追加模块层范围注）、§10.2 第 9 项（温度窗口 T→∞ 半边升格为模块内定理 `UpTempWindow.temp_window_T_infty`，两半合一仍开放；TV 层口径红线维持）、§10.2 模块化评估段（追加式模块化已落地，与语义切分及签名迁移解耦）、附录 D 第 6 项（模块化树复现路径）。开放项核查结论：§10.2 第 0 项签名迁移、第 8 项 `real_group_variance_le_raw_eps`、第 10 项 (c) 单位矩全装配、(f) `Z_align_pos` Real 镜像、§5.3 审计分解蓝图，在 220 基态下均仍开放（grep 零命中），本文相应表述维持。*
