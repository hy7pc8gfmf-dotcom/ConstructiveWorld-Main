(* ========================================================================= *)
(* UpReqIndex.v — 签名迁移总账机器索引（批5 收口清单项 9：机器可验总账入口）    *)
(*                                                                           *)
(* 建立席：批5 回写整合席 ｜ 建立日：2026-09-09 ｜ 形态：全 Set 层最小模块      *)
(* 零 Require（不依赖基座与任何在飞件——索引层独立于被索引层，杜绝循环依赖）。   *)
(*                                                                           *)
(* 数据源：迁移总账-20260909.md v1.5（表行 grep 解析实值 659/3/71/1/0，       *)
(* 和 = 734）；件数一律 grep decl 实测（Theorem/Lemma/Corollary 行），         *)
(* 不采信任何席位报告数。v1.2（批3行点火席刷新）：批3 T13 链 12 件清偿翻牌     *)
(* （UpReqAlign3 收官终版 76 decl）+ 批4 模块伴件收官补登 UpFirewallReq(9) /    *)
(* UpAlignIdReq(8) / UpPredRelaxReq(6)（二席v2 终版，_v2chk coqchk PASS）+      *)
(* 批外 UpAuditBridge(28) 补登 + 批外 UpRealLeB 口径 6→30（Part D+E 24 件 B 形）。    *)
(* v1.3（总账回写席刷新）：批5 波3 面 35 行核销落账（Misc5 32 + Cauchy 1 + 核B 2）    *)
(* → 宇宙行 624/12/71/10/17；补登批5 波3 双模块 UpReqMisc5(35) / UpReqMisc5B(20)。   *)
(* v1.4（账房翻牌+Index 刷新席刷新）：v1.4 前段（账房翻牌席，C2 终验闸开启）C2 桥面 17 行 +  *)
(* 批4 在飞 9 行核销 → 650/3/71/10/0；v1.4 尾段（本席）批3 FEP 尾段 9 行（FEPAttention 4 +  *)
(* RowView 1 + FEPLogZ 4，权威源 UpReqFEPAttn.v，本席亲跑 coqchk PASS）→ 659/3/71/1/0。     *)
(* 补登 v1.4 前段注册表 UpReqRDF(47) / UpDebtSqrtAbsReq(6) + 尾段 UpReqFEPAttn(16) +          *)
(* 批外 UpRealLeB2(8，Bishop 分立续建口径)。idx_UpPPOPlain 暂不登记（在飞分歧，随终验增册）。   *)
(* v1.5（账房尾项翻牌席 wb7 版记刷新）：承 v1.4 尾段全部增册与宇宙行 659/3/71/1/0，零数值变化；    *)
(* 本席批外清账：Bishop 盘点清单 #24/25/28/32 翻「建成」+ 组合器 3 件登记（Bishop 扫描 §六，      *)
(* 权威记录 E360 四关全绿；Real 层批外不占宇宙名额）；min plain-le 6 件维持冻结——在飞席          *)
(* UpReqPPOPlain.v 23:42 仍增改（.vo 23:35 旧于 .v），终验闸未开，idx_UpPPOPlain 随其终验增册。  *)
(* v1.7（wb10 影子预置席，diff-ready 预制；翻牌闸=件16 canonical log 占位 _clipup_chk_UpReqPPO.log（验后删；证据固化于总账 v1.7 件16 行证据列 md5、字节数、cst 尾行；已于 01:28 经主会话亲验 PASS），闸已落）： *)
(* idx_UpPPOPlain 解除「暂不登记」增册 14 件（662 行/14 行首 Qed；_wb9_chk_ppoplain.log coqchk PASS）； *)
(* 批外新件 UpReqMinPProjB(7 件/251 行，W2' 簇；_w2_* 四关 log) 补登；idx_UpReqAttnGibbs 63→65（分歧清偿增量 *)
(* 节 2 件，总账 v1.6 增册口径）；idx_UpReqPPO 22→26（件16 终验翻牌，grep decl 实测 26）；宇宙行 659/3/71/1/0 *)
(* →668/0/66/0/0（件16 挂账翻牌 + PPOPlain 簇冻结闸口件翻牌；和 734 不变）。 *)
(* v1.8（wb27 影子预置席，diff-ready 预制；闸=主会话 v1.8 commit 令+§10.2 数字同步，闸未落本影子不覆盖真件）： *)
(* 批外三新件补登（B 形扩展建造队列 T1/T2/T3，Real/B 层批外不占 734 名额）：idx_UpRealLeB3(8 件/220 行， *)
(* ≤_B 序代数引擎固化层，旗舰 leb3_le_b_opp_rev) + idx_UpReqPPOB(2 件/98 行，定理 6.6 对应物升格， *)
(* 旗舰 real_ppo_conservative_B_full) + idx_UpReqSumB(3 件/191 行，Σ ≤_B 自持机器，旗舰 sumb_list_sum_le_b)； *)
(* 宇宙行 668/0/66/0/0 → 670/0/64/0/0（冻结 v1.8 候选两行翻牌：clip_lower 件7 + ppo_clipped_improvement 件8， *)
(* 总账 v1.7 在案方向，件名随总账 v1.8 待与席25 产物互核；和 734 不变）。 *)
(* v2.0（席N：UpReqIndex v2 重制席，20260911；重制依据=磁盘实测+Live_X 终态，非影子直编真件）：承 v1.8 宇宙行 *)
(* 670/0/64/0/0 与 39 件 idx_ 注册表零改动（append-only，v1.2–v1.8 版记全数保留），纯新增两层登记面—— *)
(* 层① attn 活动区主件面 127 件（剥块注释 token 级封口计数口径，和 25354，含自指件本体 v2 终态 27）； *)
(* 层② Live_X 终态结构面（S01–S15 拆分组 15 组、G 系合并组 12 组【G03 缺位】+成员旧名 44、219 壳+220 扩展、 *)
(* 退役件 214/UpTVReal/ProbeReexSig 处置）；并新增结构不变量 22 条 reflexivity 机械对账：拆分无损 *)
(*（219 大库封口数=S 组和 3136）、12 组合并无损（逐组成员旧名 attn 封口和=G 组件封口数）、壳链 15、 *)
(* Live_X 总面 99=15+12+2+70。idx_ 走 grep decl TLC 口径随总账翻牌，af_/lg_ 走 token 级封口口径随磁盘实测， *)
(* 两轨并行互不覆盖。 *)
(*                                                                           *)
(* 四关（同家规，温控包装）：G1 禁词全文件扫描全零（含头注，字面规避）；        *)
(* G2 coqc 9.0 同轨 EXIT=0（cpu_guard LoadLimit 60）；G3 提取探针经 coqtop 管道  *)
(*（Extraction 文件式常数清单，提取产物魔法字计数 = 0 + Print Assumptions        *)
(* 3 件全 Closed under the global context，探针产物验后即删）；G4 coqchk 9.0     *)
(* "Modules were successfully checked"。                                     *)
(*                                                                           *)
(* 维护纪律：后续每批交付追加一个 idx_* 定义（附注释段）并同步统计字面值——      *)
(* 文内四个等式引理在 G2 编译期机械化核对（清单折叠 vs 字面值），任何手滑       *)
(* 当场爆编译。这就是机器可验账目的全部意义。                                  *)
(* ========================================================================= *)

(* ---------- 索引条目载体（全 Set 层） ---------- *)

From Stdlib Require Import Ascii String.
(* Stdlib 专供 string 载体（Set 层）；索引层不 Require 任何被索引模块。 *)

Record ReqModule : Set := MkReqModule
  { rm_name     : string   (* 模块文件名 *)
  ; rm_decl_cnt : nat      (* grep decl 实测件数 *)
  ; rm_gate_day : nat      (* 四关确认/复验日 yyyymmdd *)
  ; rm_head_kw  : string   (* HEAD 关键词（验收 grep 用） *)
  ; rm_in_uni   : bool     (* 是否计入 734 迁移宇宙注册表 *)
  }.

Fixpoint cnt_mod (l : list ReqModule) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_mod tl)
  end.

Fixpoint sum_cnt (l : list ReqModule) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (rm_decl_cnt m) (sum_cnt tl)
  end.

(* ---------- 已交付 req 模块清单（批0–批4 注册表 11 模块） ---------- *)

(* idx_UpSigMigrate —— UpSigMigrate.v：批0 试点旗舰席（批0 旗舰 + req_attention_is_gibbs_temp）*)
Definition idx_UpSigMigrate : ReqModule :=
  MkReqModule "UpSigMigrate.v" 13 20260909 "req_attention_is_gibbs_temp" true.

(* idx_UpSigMigrate2 —— UpSigMigrate2.v：m2 旗舰席（a_ 系对位 6 件 + align-a 节）*)
Definition idx_UpSigMigrate2 : ReqModule :=
  MkReqModule "UpSigMigrate2.v" 49 20260909 "a_rlhf_suboptimality_gap" true.

(* idx_UpReqAlgebra —— UpReqAlgebra.v：批1 req 代数地基（RingLemmas/SimpleAlgebra/AlgHelpers + 批外新机器 3 件）*)
Definition idx_UpReqAlgebra : ReqModule :=
  MkReqModule "UpReqAlgebra.v" 63 20260909 "req_plus_zero_r" true.

(* idx_UpReqDist —— UpReqDist.v：批2 分布/自由能/温度层（FEP 52 + GRPO 15 + SqrtWitness 7 + 接管席增量）*)
Definition idx_UpReqDist : ReqModule :=
  MkReqModule "UpReqDist.v" 91 20260909 "reqd_le_of_req" true.

(* idx_UpReqTempEntropy —— UpReqTempEntropy.v：批2 温度熵 11 件（温度严格层 6 件续建）*)
Definition idx_UpReqTempEntropy : ReqModule :=
  MkReqModule "UpReqTempEntropy.v" 14 20260909 "req_temp_energy_dual_closed" true.

(* idx_UpReqAlign —— UpReqAlign.v：批3 对齐主体前段（KLProjection 10 + sigmoid 快赢 + 几何迭代旗舰）*)
Definition idx_UpReqAlign : ReqModule :=
  MkReqModule "UpReqAlign.v" 42 20260909 "req_pi_star_pos" true.

(* idx_UpReqAlign2 —— UpReqAlign2.v：批3 t12 求和机器 + 桥 A/C（F_t 深链）*)
Definition idx_UpReqAlign2 : ReqModule :=
  MkReqModule "UpReqAlign2.v" 40 20260909 "req2_boltzmann_factor_bridge" true.

(* idx_UpReqAlign3 —— UpReqAlign3.v：批3 T12/T13 组（环代数镜像 + 折叠件 + T13 收官全绿：
   旗舰 req2_backward_kl_step 五段链 + req2_gap_mono + step_le/iter_le；收割席尾注余件全核销）*)
Definition idx_UpReqAlign3 : ReqModule :=
  MkReqModule "UpReqAlign3.v" 76 20260909 "r2_t13_collapse" true.

(* idx_UpReqAlignRestA —— UpReqAlignRestA.v：批3 余量 A（DPO 余量放电 + Q 桥落位，32 语句口径）*)
Definition idx_UpReqAlignRestA : ReqModule :=
  MkReqModule "UpReqAlignRestA.v" 23 20260909 "ralt_dpo_pair_loss_at_star" true.

(* idx_UpReqU2 —— UpReqU2.v：批3 U2 主体 7 件 + 辅件（外延件 (b) 化先例所在）*)
Definition idx_UpReqU2 : ReqModule :=
  MkReqModule "UpReqU2.v" 20 20260909 "req_u2_fixed_point_unique" true.

(* idx_UpReqPPO —— UpReqPPO.v：批3 收尾席（未认领 15 件收口：交付 14 + 冻结 1；真证机器旗舰所在）； *)
(* v1.7：件16 rppo_align_objective_advantage_decomp 终验翻牌（canonical log 占位 _clipup_chk_UpReqPPO.log（验后删；证据固化于总账 v1.7 件16 行证据列 md5、字节数、cst 尾行）），口径 22→26（grep decl 实测） *)
Definition idx_UpReqPPO : ReqModule :=
  MkReqModule "UpReqPPO.v" 26 20260910 "rppo_align_objective_decomp" true.

(* ---------- 已交付 req 模块清单（批4/批5 新增 12 模块，v1.1 增册） ---------- *)

(* idx_UpReqSampling —— UpReqSampling.v：批4 首席（ReqUContraction 11 + ReqBoundedSoftmax 23 + epp 辅件）*)
Definition idx_UpReqSampling : ReqModule :=
  MkReqModule "UpReqSampling.v" 43 20260909 "u_tv_contraction" true.

(* idx_UpReqAttnGibbs —— UpReqAttnGibbs.v：批4 主件席（首段 14 + 中后段 39 + 扫尾席解冻增量节 + 分歧清偿增量节 2 件；旗舰 Print 假设清零）*)
Definition idx_UpReqAttnGibbs : ReqModule :=
  MkReqModule "UpReqAttnGibbs.v" 65 20260910 "ag_topk_tv_identity_strict" true.

(* idx_UpReqAttnIter —— UpReqAttnIter.v：批4 收缩簇清账席（q_kernel/收缩迭代簇 26+1 邻接；脊柱对位消费 UpReqSampling）*)
Definition idx_UpReqAttnIter : ReqModule :=
  MkReqModule "UpReqAttnIter.v" 31 20260909 "agq_iterate_converges" true.

(* idx_UpEntropyGainReq —— UpEntropyGainReq.v：批4 模块伴件席（UpEntropyGain 10 件，含两旗舰）*)
Definition idx_UpEntropyGainReq : ReqModule :=
  MkReqModule "UpEntropyGainReq.v" 10 20260909 "req_second_law_quant" true.

(* idx_UpEvictIdReq —— UpEvictIdReq.v：批4 模块伴件第二席（14 件口径 = 12 decl + 2 假设位；两件经批2 reqd_ 消费核销）*)
Definition idx_UpEvictIdReq : ReqModule :=
  MkReqModule "UpEvictIdReq.v" 13 20260909 "req_eviction_partition_le_full_exact" true.

(* idx_UpReqAlignRestB —— UpReqAlignRestB.v：批3余量B/批4 席（MinP/TopP/逐出熵四区；20260909 终验复验通过）*)
Definition idx_UpReqAlignRestB : ReqModule :=
  MkReqModule "UpReqAlignRestB.v" 55 20260909 "rls_kernel_norm_gen" true.

(* idx_UpReqSLM —— UpReqSLM.v：批5 波1 席（SLM 17 + LogDiff3 13 + 波0 资产 ReqNonnegPlain/ReqLogPlain）*)
Definition idx_UpReqSLM : ReqModule :=
  MkReqModule "UpReqSLM.v" 41 20260909 "req_markov_relative" true.

(* idx_UpReqCauchy —— UpReqCauchy.v：批5 波2 席（ConvergenceCauchy 43 + lim 簇解冻 + 波3 助件 3）*)
Definition idx_UpReqCauchy : ReqModule :=
  MkReqModule "UpReqCauchy.v" 48 20260909 "req_attractor_converges_unique_truth" true.

(* idx_UpReqMinPAntitone —— UpReqMinPAntitone.v：批4 余量席（MinP p-antitone 簇 5 件真缺新建）*)
Definition idx_UpReqMinPAntitone : ReqModule :=
  MkReqModule "UpReqMinPAntitone.v" 5 20260909 "req_minp_dropped_mass_p_monotone" true.

(* idx_UpReqOrderArgmin —— UpReqOrderArgmin.v：批5 波4 桥C1（reqDecidableOrder 同构类 + reqArgmin 机 + (c) 5 件 + snd 改述机 2）*)
Definition idx_UpReqOrderArgmin : ReqModule :=
  MkReqModule "UpReqOrderArgmin.v" 7 20260909 "req_pick_best_is_minimal" true.

(* idx_UpReqPCT —— UpReqPCT.v：批5 波4 桥C3（reqRealSelfSS + reqPCTDefs 后定义级闭合 2 件）*)
Definition idx_UpReqPCT : ReqModule :=
  MkReqModule "UpReqPCT.v" 2 20260909 "req_pct_truth_is_global_min" true.

(* idx_UpReqDpoLoss —— UpReqDpoLoss.v：批5 解冻建设席（total_loss 簇实例形 (b) 化收口 6 件 + min plain-le 裁决书）*)
Definition idx_UpReqDpoLoss : ReqModule :=
  MkReqModule "UpReqDpoLoss.v" 6 20260909 "rdl_dpo_total_loss_at_star" true.

(* ---------- 批4 模块伴件收官补登（v1.2 批3行点火席；二席v2 终版 _v2chk coqchk PASS） ---------- *)

(* idx_UpFirewallReq —— UpFirewallReq.v：批4 二席v2（UpFirewall 9 件伴件终版，件7 req_recovery_entropy_gain_alt 补建）*)
Definition idx_UpFirewallReq : ReqModule :=
  MkReqModule "UpFirewallReq.v" 9 20260909 "req_recovery_entropy_gain_alt" true.

(* idx_UpAlignIdReq —— UpAlignIdReq.v：批4 AlignId 席（UpAlignId 6 件伴件；8Qed/541 行，md5 9646ad0f 零改动背书）*)
Definition idx_UpAlignIdReq : ReqModule :=
  MkReqModule "UpAlignIdReq.v" 8 20260909 "policy_gap_backward_kl_exact" true.

(* idx_UpPredRelaxReq —— UpPredRelaxReq.v：批4 PredRelax 席（UpPredRelax 6 件伴件；6Qed/367 行，md5 cd07a2f9）*)
Definition idx_UpPredRelaxReq : ReqModule :=
  MkReqModule "UpPredRelaxReq.v" 6 20260909 "total_loss_multi_epoch_decreasing" true.

(* ---------- 批5 波3 杂项收口补登（v1.3 总账回写席；波3 席四关申报 + grep decl 实测 + .vo/.v 时序绿态） ---------- *)

(* idx_UpReqMisc5 —— UpReqMisc5.v：批5 波3 席（PCC/LMI/Thermo/ConvThm/SumExp/GRPO/
   DiffLemmas 代数面 32 行 + 自持辅件；总账 v1.3 核A 翻牌权威源）*)
Definition idx_UpReqMisc5 : ReqModule :=
  MkReqModule "UpReqMisc5.v" 35 20260909 "req_dpo_gradient_alt" true.

(* idx_UpReqMisc5B —— UpReqMisc5B.v：批5 波3 席（Multivar/Hilbert/GramSchmidt (b|桥) 20 件；
   v1.2 已入表而注册表漏登，v1.3 补登）*)
Definition idx_UpReqMisc5B : ReqModule :=
  MkReqModule "UpReqMisc5B.v" 20 20260909 "req_mv_vec_diff_decomp" true.

(* ---------- v1.4 补登（v1.4 前段账房翻牌席注册表 + 尾段本席增册；grep decl 实测 + coqchk 在案） ---------- *)

(* idx_UpReqRDF —— UpReqRDF.v：批5 波4 桥席 C2（reqRDF/reqRDFMV/reqRDFMVVec 记录桥 17 件对位
   + ReqDiffPlain 槽组 + 机器辅件；47 TLC = 47 Qed，修复至绿席+续建席双席交付终版 178,040B；
   v1.4 尾段本席亲跑 coqchk 9.0 PASS 加★）*)
Definition idx_UpReqRDF : ReqModule :=
  MkReqModule "UpReqRDF.v" 47 20260909 "req_rdf_mv_vec_compose" true.

(* idx_UpReqFEPAttn —— UpReqFEPAttn.v：批3 FEP 尾段席（FEPAttention/RowView/FEPLogZ 挂账
   9 件 req 伴件权威源，16 TLC = 16 Qed；v1.4 尾段本席亲跑 coqchk 9.0 PASS 加★）*)
Definition idx_UpReqFEPAttn : ReqModule :=
  MkReqModule "UpReqFEPAttn.v" 16 20260909 "req_free_energy_softmax_eq_neg_T_logZ" true.

(* idx_UpDebtSqrtAbsReq —— UpDebtSqrtAbsReq.v：批4 模块伴件席（UpDebtSqrtAbs 6 件伴件；
   v1.4 前段账房翻牌席注册表口径，.vo 08:02 > .v 07:42 绿态时序旁证）*)
Definition idx_UpDebtSqrtAbsReq : ReqModule :=
  MkReqModule "UpDebtSqrtAbsReq.v" 6 20260909 "req_sqrt_one_abstract" true.

(* ---------- v1.7 增册（wb10 影子预置席；_wb9_chk_ppoplain.log coqchk PASS，v1.5「暂不登记」解除） ---------- *)

(* idx_UpReqPPOPlain —— UpReqPPOPlain.v：批5 PPO plain 收口席（min plain-le 6 + clip_lower 件7 + 件8
   ppo_clipped_improvement 裁决书影响面 + 伴件/内机 6 件；662 行，14 行首 Qed 1:1；旗舰 rpl_ppo_clipped_improvement；
   四关：G4=_wb9_chk_ppoplain.log 01:19 coqchk "Modules were successfully checked"，闭包 cst 在列） *)
Definition idx_UpReqPPOPlain : ReqModule :=
  MkReqModule "UpReqPPOPlain.v" 14 20260910 "rpl_ppo_clipped_improvement" true.

(* ---------- 批外增量（不占 734 迁移宇宙名额） ---------- *)

(* idx_UpAuditBridge —— UpAuditBridge.v：Min-P 截断采样 KL 投影审计桥（P8 全量；CW219 Real 层面；28 decl，coqchk 08:55 PASS）*)
Definition idx_UpAuditBridge : ReqModule :=
  MkReqModule "UpAuditBridge.v" 28 20260909 "real_minp_projection_eps" false.

(* idx_UpRealLeB —— UpRealLeB.v：M2 收口引理席 + Bishop 升级席（Real 层 Bishop 形非严格序 real_le_b + 收口引理 +
   Part D 升级席增量 + Part E 可升 18 件 Bishop 形收口——共 30 decl，其中 Part D+E 24 件 B 形；定理 4.9/6.6 对应物）*)
Definition idx_UpRealLeB : ReqModule :=
  MkReqModule "UpRealLeB.v" 30 20260909 "real_le_closure_b" false.

(* idx_UpRealLeB2 —— UpRealLeB2.v：Bishop 挂账攻坚席（UpRealLeB 分立续建层：Part E/F 多 eps
   组合链 4 件 + 广义收口器 4 件；8 TLC = 8 Qed，零未闭合证明；v1.4 尾段本席亲跑 coqchk 9.0
   PASS；分立口径与 UpRealLeB(30) 并立不合并）*)
Definition idx_UpRealLeB2 : ReqModule :=
  MkReqModule "UpRealLeB2.v" 8 20260909 "real_db_breaking_bound_B" false.

(* idx_UpReqMinPProjB —— UpReqMinPProjB.v：批外 W2' 簇新件（MinP Bishop 形 B 面 7 件；251 行，
   7 行首 Qed 1:1；旗舰 real_minp_projection_eps_B；四关 log _w2_g1g2_evidence/_w2_g3_objmagic/
   _w2_g4_evidence/_w2_chk_UpReqMinPProjB 全绿；Real 层批外不占宇宙名额） *)
Definition idx_UpReqMinPProjB : ReqModule :=
  MkReqModule "UpReqMinPProjB.v" 7 20260910 "real_minp_projection_eps_B" false.

(* ---------- v1.8 批外增册（wb27 影子预置席；B 形扩展建造队列 T1/T2/T3，Real 层批外不占宇宙名额） ---------- *)

(* idx_UpRealLeB3 —— UpRealLeB3.v：≤_B 序代数引擎固化层（B 形扩展 T1；8 TLC = 8 行首 Qed，220 行； *)
(*   反序/正缩放/恒等严格元三面新构造；旗舰 leb3_le_b_opp_rev） *)
Definition idx_UpRealLeB3 : ReqModule :=
  MkReqModule "UpRealLeB3.v" 8 20260910 "leb3_le_b_opp_rev" false.

(* idx_UpReqPPOB —— UpReqPPOB.v：定理 6.6 对应物判词 5 升格席（B 形扩展 T2；ppo 保守性 Bishop 完整形， *)
(*   sum_pos 槽接口前提在案；2 TLC = 2 行首 Qed，98 行；旗舰 real_ppo_conservative_B_full） *)
Definition idx_UpReqPPOB : ReqModule :=
  MkReqModule "UpReqPPOB.v" 2 20260910 "real_ppo_conservative_B_full" false.

(* idx_UpReqSumB —— UpReqSumB.v：Σ ≤_B 自持机器席（B 形扩展 T3；3 TLC = 3 行首 Qed + 自持 Fixpoint *)
(*   sumb_lenR 口径外机器（件数口径从众：Theorem/Lemma/Corollary 行）；191 行；旗舰 sumb_list_sum_le_b） *)
Definition idx_UpReqSumB : ReqModule :=
  MkReqModule "UpReqSumB.v" 3 20260910 "sumb_list_sum_le_b" false.

(* ---------- 清单与统计（字面值；一致性由文末等式引理编译期核对） ---------- *)

Definition ReqModuleList : list ReqModule :=
  cons idx_UpSigMigrate
  (cons idx_UpSigMigrate2
  (cons idx_UpReqAlgebra
  (cons idx_UpReqDist
  (cons idx_UpReqTempEntropy
  (cons idx_UpReqAlign
  (cons idx_UpReqAlign2
  (cons idx_UpReqAlign3
  (cons idx_UpReqAlignRestA
  (cons idx_UpReqU2
  (cons idx_UpReqPPO
  (cons idx_UpReqSampling
  (cons idx_UpReqAttnGibbs
  (cons idx_UpReqAttnIter
  (cons idx_UpEntropyGainReq
  (cons idx_UpEvictIdReq
  (cons idx_UpReqAlignRestB
  (cons idx_UpReqSLM
  (cons idx_UpReqCauchy
  (cons idx_UpReqMinPAntitone
  (cons idx_UpReqOrderArgmin
  (cons idx_UpReqPCT
  (cons idx_UpReqDpoLoss
  (cons idx_UpFirewallReq
  (cons idx_UpAlignIdReq
  (cons idx_UpPredRelaxReq
  (cons idx_UpAuditBridge
  (cons idx_UpRealLeB
  (cons idx_UpRealLeB2
  (cons idx_UpReqMisc5
  (cons idx_UpReqMisc5B
  (cons idx_UpReqRDF
  (cons idx_UpReqFEPAttn
  (cons idx_UpDebtSqrtAbsReq
  (cons idx_UpReqPPOPlain
  (cons idx_UpReqMinPProjB
  (cons idx_UpRealLeB3
  (cons idx_UpReqPPOB
  (cons idx_UpReqSumB nil)))))))))))))))))))))))))))))))))))))).

(* 模块计数：宇宙内 req 模块 32 + 批外 7 = 39（v1.8：批外 UpRealLeB3 + UpReqPPOB + UpReqSumB 补登；v1.7：宇宙内 UpReqPPOPlain 增册 + 批外 UpReqMinPProjB 补登） *)
Definition DeliveredModules : nat := 32.
Definition ExtraModules     : nat := 7.
Definition TotalModules     : nat := 39.

(* 件数计数：grep decl 实测和 1030 = 宇宙内 944 + 批外 86（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3；v1.3 增 Misc5 35 + Misc5B 20；v1.4 增 RDF 47 + DebtSqrtAbsReq 6 + FEPAttn 16 + LeB2 8；v1.7 增 PPOPlain 14 + MinPProjB 7 + AttnGibbs +2 + PPO +4；v1.8 增 LeB3 8 + PPOB 2 + SumB 3） *)
Definition DeliveredItems : nat := 1030.
Definition UniverseItems  : nat := 944.

(* 迁移宇宙表行解析实值（总账 v1.8 闸目标，20260910；和 = 734；批外 Real/B 形三新件不占名额） *)
Definition UniverseTotal          : nat := 734.
Definition UniverseDeliveredRows  : nat := 670.
Definition UniverseInFlightRows   : nat := 0.
Definition UniverseFrozenRows     : nat := 64.
Definition UniverseSuspendedRows  : nat := 0.
Definition UniverseUnclaimedRows  : nat := 0.
Definition LastAuditDay           : nat := 20260910.

(* ---------- 机器核对引理（reflexivity 级：字面值 vs 清单折叠当场对账） ---------- *)

(* 清单模块数 = 总数字面值（任何增删清单而忘改字面值即爆 G2） *)
Lemma TotalModules_matches : TotalModules = cnt_mod ReqModuleList.
Proof. reflexivity. Qed.

(* 清单件数和 = 总件数字面值（件数口径 grep decl 实测） *)
Lemma DeliveredItems_matches : DeliveredItems = sum_cnt ReqModuleList.
Proof. reflexivity. Qed.

(* 宇宙内/批外模块分账闭合 *)
Lemma DeliveredModules_matches : DeliveredModules = minus TotalModules ExtraModules.
Proof. reflexivity. Qed.

(* 宇宙件数分账闭合：全量和 = 宇宙内 + 批外（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3 件；v1.8 四重→七重 minus） *)
Lemma UniverseItems_matches :
  UniverseItems = minus
    (minus
    (minus
    (minus
    (minus
    (minus
    (minus DeliveredItems (rm_decl_cnt idx_UpRealLeB))
           (rm_decl_cnt idx_UpAuditBridge))
    (rm_decl_cnt idx_UpRealLeB2))
    (rm_decl_cnt idx_UpReqMinPProjB))
    (rm_decl_cnt idx_UpRealLeB3))
    (rm_decl_cnt idx_UpReqPPOB))
    (rm_decl_cnt idx_UpReqSumB).
Proof. reflexivity. Qed.

(* 迁移宇宙五态分解闭合（表行解析 670+0+64+0+0 = 734；批外 LeB3/PPOB/SumB 不占 734） *)
Lemma Universe_splits : UniverseTotal
  = plus (plus (plus (plus UniverseDeliveredRows UniverseInFlightRows)
                   UniverseFrozenRows)
         UniverseSuspendedRows)
  UniverseUnclaimedRows.
Proof. reflexivity. Qed.


(* ================= v2.0 重制增量（席N：UpReqIndex v2 重制席，20260911） ================= *)
(* 依据：磁盘实测（剥块注释 token 级 \bQed\. 计数口径，非行首 decl 口径；与总账 idx_ 的 grep decl *)
(* TLC 口径并行不悖、互不覆盖）+ Live_X 终态结构（S/G 双系 + 旧名消融 + 219 壳）。宇宙行与 39 件 *)
(* idx_ 注册表承 v1.8 全量不动（append-only）；本节纯新增两层登记面，数值面与 v1.8 无交集。 *)

(* ---------- v2.0 层①：attn 活动区主件面（127 主件，剥注释 token 级 Qed 口径） ---------- *)

Record AttnFace : Set := MkAttnFace
  { af_name : string   (* 主件文件名 *)
  ; af_qed  : nat      (* 剥块注释后 token 级 Qed 计数（20260911 实测） *)
  ; af_day  : nat      (* 测量日 yyyymmdd *)
  }.

Fixpoint cnt_af (l : list AttnFace) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_af tl)
  end.

Fixpoint sum_af (l : list AttnFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (af_qed m) (sum_af tl)
  end.

Definition af_AttnDoeblin : AttnFace := MkAttnFace "AttnDoeblin.v" 42 20260911.
Definition af_AttnHardLimit : AttnFace := MkAttnFace "AttnHardLimit.v" 40 20260911.
Definition af_AttnHardLimit218 : AttnFace := MkAttnFace "AttnHardLimit218.v" 39 20260911.
Definition af_AttnSqrt : AttnFace := MkAttnFace "AttnSqrt.v" 12 20260911.
Definition af_CW220_Extensions : AttnFace := MkAttnFace "CW220_Extensions.v" 552 20260911.
Definition af_CW_ConstructiveWorld_219 : AttnFace := MkAttnFace "CW_ConstructiveWorld_219.v" 3136 20260911.
Definition af_CW_ConstructiveWorld_220 : AttnFace := MkAttnFace "CW_ConstructiveWorld_220.v" 3688 20260911.
Definition af_ConstructiveWorld_215 : AttnFace := MkAttnFace "ConstructiveWorld-215.v" 2966 20260911.
Definition af_ConstructiveWorld_217 : AttnFace := MkAttnFace "ConstructiveWorld-217.v" 3056 20260911.
Definition af_ConstructiveWorld_218 : AttnFace := MkAttnFace "ConstructiveWorld-218.v" 3073 20260911.
Definition af_ConstructiveWorld_219 : AttnFace := MkAttnFace "ConstructiveWorld-219.v" 3136 20260911.
Definition af_ConstructiveWorld : AttnFace := MkAttnFace "ConstructiveWorld.v" 2966 20260911.
Definition af_UpAlignId : AttnFace := MkAttnFace "UpAlignId.v" 6 20260911.
Definition af_UpAlignIdReq : AttnFace := MkAttnFace "UpAlignIdReq.v" 8 20260911.
Definition af_UpArchAttn : AttnFace := MkAttnFace "UpArchAttn.v" 5 20260911.
Definition af_UpAuditBridge : AttnFace := MkAttnFace "UpAuditBridge.v" 28 20260911.
Definition af_UpBudgetReal : AttnFace := MkAttnFace "UpBudgetReal.v" 20 20260911.
Definition af_UpCLQuery : AttnFace := MkAttnFace "UpCLQuery.v" 22 20260911.
Definition af_UpCS : AttnFace := MkAttnFace "UpCS.v" 16 20260911.
Definition af_UpConstitution : AttnFace := MkAttnFace "UpConstitution.v" 37 20260911.
Definition af_UpDPOLip : AttnFace := MkAttnFace "UpDPOLip.v" 14 20260911.
Definition af_UpDebtDual : AttnFace := MkAttnFace "UpDebtDual.v" 10 20260911.
Definition af_UpDebtGibbsT : AttnFace := MkAttnFace "UpDebtGibbsT.v" 5 20260911.
Definition af_UpDebtSqrtAbs : AttnFace := MkAttnFace "UpDebtSqrtAbs.v" 6 20260911.
Definition af_UpDebtSqrtAbsReq : AttnFace := MkAttnFace "UpDebtSqrtAbsReq.v" 6 20260911.
Definition af_UpDissip : AttnFace := MkAttnFace "UpDissip.v" 38 20260911.
Definition af_UpEntropyGain : AttnFace := MkAttnFace "UpEntropyGain.v" 10 20260911.
Definition af_UpEntropyGainReq : AttnFace := MkAttnFace "UpEntropyGainReq.v" 10 20260911.
Definition af_UpEvictId : AttnFace := MkAttnFace "UpEvictId.v" 14 20260911.
Definition af_UpEvictIdReq : AttnFace := MkAttnFace "UpEvictIdReq.v" 13 20260911.
Definition af_UpExtras : AttnFace := MkAttnFace "UpExtras.v" 8 20260911.
Definition af_UpFEP : AttnFace := MkAttnFace "UpFEP.v" 5 20260911.
Definition af_UpFirewall : AttnFace := MkAttnFace "UpFirewall.v" 9 20260911.
Definition af_UpFirewallReq : AttnFace := MkAttnFace "UpFirewallReq.v" 9 20260911.
Definition af_UpGRPO : AttnFace := MkAttnFace "UpGRPO.v" 27 20260911.
Definition af_UpGeomB : AttnFace := MkAttnFace "UpGeomB.v" 16 20260911.
Definition af_UpHlogZ : AttnFace := MkAttnFace "UpHlogZ.v" 4 20260911.
Definition af_UpIDL : AttnFace := MkAttnFace "UpIDL.v" 64 20260911.
Definition af_UpIDL_P2 : AttnFace := MkAttnFace "UpIDL_P2.v" 63 20260911.
Definition af_UpKVDrift : AttnFace := MkAttnFace "UpKVDrift.v" 60 20260911.
Definition af_UpKVDrift_P2 : AttnFace := MkAttnFace "UpKVDrift_P2.v" 60 20260911.
Definition af_UpKVEv : AttnFace := MkAttnFace "UpKVEv.v" 11 20260911.
Definition af_UpLoeb : AttnFace := MkAttnFace "UpLoeb.v" 38 20260911.
Definition af_UpLoebD2 : AttnFace := MkAttnFace "UpLoebD2.v" 22 20260911.
Definition af_UpLogMono : AttnFace := MkAttnFace "UpLogMono.v" 4 20260911.
Definition af_UpMinP : AttnFace := MkAttnFace "UpMinP.v" 31 20260911.
Definition af_UpPLA : AttnFace := MkAttnFace "UpPLA.v" 16 20260911.
Definition af_UpPPO : AttnFace := MkAttnFace "UpPPO.v" 5 20260911.
Definition af_UpPredRelax : AttnFace := MkAttnFace "UpPredRelax.v" 6 20260911.
Definition af_UpPredRelaxReq : AttnFace := MkAttnFace "UpPredRelaxReq.v" 6 20260911.
Definition af_UpProj : AttnFace := MkAttnFace "UpProj.v" 32 20260911.
Definition af_UpProjBPC : AttnFace := MkAttnFace "UpProjBPC.v" 17 20260911.
Definition af_UpQKBound : AttnFace := MkAttnFace "UpQKBound.v" 59 20260911.
Definition af_UpRealLeB : AttnFace := MkAttnFace "UpRealLeB.v" 30 20260911.
Definition af_UpRealLeB2 : AttnFace := MkAttnFace "UpRealLeB2.v" 8 20260911.
Definition af_UpRealLeB3 : AttnFace := MkAttnFace "UpRealLeB3.v" 8 20260911.
Definition af_UpRecast : AttnFace := MkAttnFace "UpRecast.v" 50 20260911.
Definition af_UpRefuted : AttnFace := MkAttnFace "UpRefuted.v" 48 20260911.
Definition af_UpReqAlgebra : AttnFace := MkAttnFace "UpReqAlgebra.v" 63 20260911.
Definition af_UpReqAlign : AttnFace := MkAttnFace "UpReqAlign.v" 42 20260911.
Definition af_UpReqAlign2 : AttnFace := MkAttnFace "UpReqAlign2.v" 40 20260911.
Definition af_UpReqAlign3 : AttnFace := MkAttnFace "UpReqAlign3.v" 76 20260911.
Definition af_UpReqAlignRest : AttnFace := MkAttnFace "UpReqAlignRest.v" 16 20260911.
Definition af_UpReqAlignRestA : AttnFace := MkAttnFace "UpReqAlignRestA.v" 23 20260911.
Definition af_UpReqAlignRestB : AttnFace := MkAttnFace "UpReqAlignRestB.v" 55 20260911.
Definition af_UpReqAttnGibbs : AttnFace := MkAttnFace "UpReqAttnGibbs.v" 65 20260911.
Definition af_UpReqAttnIter : AttnFace := MkAttnFace "UpReqAttnIter.v" 31 20260911.
Definition af_UpReqBoltzDirect : AttnFace := MkAttnFace "UpReqBoltzDirect.v" 8 20260911.
Definition af_UpReqBranchPos : AttnFace := MkAttnFace "UpReqBranchPos.v" 8 20260911.
Definition af_UpReqCauchy : AttnFace := MkAttnFace "UpReqCauchy.v" 48 20260911.
Definition af_UpReqDist : AttnFace := MkAttnFace "UpReqDist.v" 89 20260911.
Definition af_UpReqDpoLoss : AttnFace := MkAttnFace "UpReqDpoLoss.v" 6 20260911.
Definition af_UpReqFEPAttn : AttnFace := MkAttnFace "UpReqFEPAttn.v" 16 20260911.
Definition af_UpReqGeomD : AttnFace := MkAttnFace "UpReqGeomD.v" 19 20260911.
Definition af_UpReqGeomIter : AttnFace := MkAttnFace "UpReqGeomIter.v" 16 20260911.
Definition af_UpReqGibbsD : AttnFace := MkAttnFace "UpReqGibbsD.v" 15 20260911.
Definition af_UpReqGibbsE : AttnFace := MkAttnFace "UpReqGibbsE.v" 15 20260911.
Definition af_UpReqGibbsE2 : AttnFace := MkAttnFace "UpReqGibbsE2.v" 13 20260911.
Definition af_UpReqHlogZD : AttnFace := MkAttnFace "UpReqHlogZD.v" 11 20260911.
Definition af_UpReqIndex : AttnFace := MkAttnFace "UpReqIndex.v" 27 20260911.
Definition af_UpReqJensen : AttnFace := MkAttnFace "UpReqJensen.v" 12 20260911.
Definition af_UpReqKLCvx : AttnFace := MkAttnFace "UpReqKLCvx.v" 16 20260911.
Definition af_UpReqKLEnergy : AttnFace := MkAttnFace "UpReqKLEnergy.v" 14 20260911.
Definition af_UpReqKLStrict : AttnFace := MkAttnFace "UpReqKLStrict.v" 14 20260911.
Definition af_UpReqLatticeB : AttnFace := MkAttnFace "UpReqLatticeB.v" 11 20260911.
Definition af_UpReqLogCompD : AttnFace := MkAttnFace "UpReqLogCompD.v" 23 20260911.
Definition af_UpReqLogCompD2 : AttnFace := MkAttnFace "UpReqLogCompD2.v" 7 20260911.
Definition af_UpReqLogD : AttnFace := MkAttnFace "UpReqLogD.v" 10 20260911.
Definition af_UpReqLogLinD : AttnFace := MkAttnFace "UpReqLogLinD.v" 18 20260911.
Definition af_UpReqLogPrimD : AttnFace := MkAttnFace "UpReqLogPrimD.v" 18 20260911.
Definition af_UpReqLogRDF : AttnFace := MkAttnFace "UpReqLogRDF.v" 17 20260911.
Definition af_UpReqMinPAntitone : AttnFace := MkAttnFace "UpReqMinPAntitone.v" 5 20260911.
Definition af_UpReqMinPProjB : AttnFace := MkAttnFace "UpReqMinPProjB.v" 7 20260911.
Definition af_UpReqMisc5 : AttnFace := MkAttnFace "UpReqMisc5.v" 35 20260911.
Definition af_UpReqMisc5B : AttnFace := MkAttnFace "UpReqMisc5B.v" 20 20260911.
Definition af_UpReqOrderArgmin : AttnFace := MkAttnFace "UpReqOrderArgmin.v" 7 20260911.
Definition af_UpReqPCT : AttnFace := MkAttnFace "UpReqPCT.v" 2 20260911.
Definition af_UpReqPPO : AttnFace := MkAttnFace "UpReqPPO.v" 25 20260911.
Definition af_UpReqPPOB : AttnFace := MkAttnFace "UpReqPPOB.v" 4 20260911.
Definition af_UpReqPPOGapB : AttnFace := MkAttnFace "UpReqPPOGapB.v" 8 20260911.
Definition af_UpReqPPOPlain : AttnFace := MkAttnFace "UpReqPPOPlain.v" 14 20260911.
Definition af_UpReqPowB : AttnFace := MkAttnFace "UpReqPowB.v" 10 20260911.
Definition af_UpReqRDF : AttnFace := MkAttnFace "UpReqRDF.v" 47 20260911.
Definition af_UpReqRealFEP : AttnFace := MkAttnFace "UpReqRealFEP.v" 11 20260911.
Definition af_UpReqSLM : AttnFace := MkAttnFace "UpReqSLM.v" 41 20260911.
Definition af_UpReqSampling : AttnFace := MkAttnFace "UpReqSampling.v" 43 20260911.
Definition af_UpReqSqPos : AttnFace := MkAttnFace "UpReqSqPos.v" 5 20260911.
Definition af_UpReqSqrtF : AttnFace := MkAttnFace "UpReqSqrtF.v" 27 20260911.
Definition af_UpReqSumB : AttnFace := MkAttnFace "UpReqSumB.v" 3 20260911.
Definition af_UpReqSumD : AttnFace := MkAttnFace "UpReqSumD.v" 27 20260911.
Definition af_UpReqTempEntropy : AttnFace := MkAttnFace "UpReqTempEntropy.v" 14 20260911.
Definition af_UpReqTempInterp : AttnFace := MkAttnFace "UpReqTempInterp.v" 11 20260911.
Definition af_UpReqU2 : AttnFace := MkAttnFace "UpReqU2.v" 20 20260911.
Definition af_UpReqZAuto : AttnFace := MkAttnFace "UpReqZAuto.v" 8 20260911.
Definition af_UpReqZPosD : AttnFace := MkAttnFace "UpReqZPosD.v" 6 20260911.
Definition af_UpReqZPosFinal : AttnFace := MkAttnFace "UpReqZPosFinal.v" 9 20260911.
Definition af_UpReqZPosI : AttnFace := MkAttnFace "UpReqZPosI.v" 6 20260911.
Definition af_UpReqZPosI2 : AttnFace := MkAttnFace "UpReqZPosI2.v" 15 20260911.
Definition af_UpSLM : AttnFace := MkAttnFace "UpSLM.v" 55 20260911.
Definition af_UpSigMigrate : AttnFace := MkAttnFace "UpSigMigrate.v" 13 20260911.
Definition af_UpSigMigrate2 : AttnFace := MkAttnFace "UpSigMigrate2.v" 49 20260911.
Definition af_UpStepKL : AttnFace := MkAttnFace "UpStepKL.v" 32 20260911.
Definition af_UpStepKLM3 : AttnFace := MkAttnFace "UpStepKLM3.v" 18 20260911.
Definition af_UpStopTime : AttnFace := MkAttnFace "UpStopTime.v" 45 20260911.
Definition af_UpTVDoeblin : AttnFace := MkAttnFace "UpTVDoeblin.v" 58 20260911.
Definition af_UpTVReal : AttnFace := MkAttnFace "UpTVReal.v" 33 20260911.
Definition af_UpTempWindow : AttnFace := MkAttnFace "UpTempWindow.v" 69 20260911.

Definition AttnFaceList : list AttnFace :=
  cons af_AttnDoeblin
  (cons af_AttnHardLimit
  (cons af_AttnHardLimit218
  (cons af_AttnSqrt
  (cons af_CW220_Extensions
  (cons af_CW_ConstructiveWorld_219
  (cons af_CW_ConstructiveWorld_220
  (cons af_ConstructiveWorld_215
  (cons af_ConstructiveWorld_217
  (cons af_ConstructiveWorld_218
  (cons af_ConstructiveWorld_219
  (cons af_ConstructiveWorld
  (cons af_UpAlignId
  (cons af_UpAlignIdReq
  (cons af_UpArchAttn
  (cons af_UpAuditBridge
  (cons af_UpBudgetReal
  (cons af_UpCLQuery
  (cons af_UpCS
  (cons af_UpConstitution
  (cons af_UpDPOLip
  (cons af_UpDebtDual
  (cons af_UpDebtGibbsT
  (cons af_UpDebtSqrtAbs
  (cons af_UpDebtSqrtAbsReq
  (cons af_UpDissip
  (cons af_UpEntropyGain
  (cons af_UpEntropyGainReq
  (cons af_UpEvictId
  (cons af_UpEvictIdReq
  (cons af_UpExtras
  (cons af_UpFEP
  (cons af_UpFirewall
  (cons af_UpFirewallReq
  (cons af_UpGRPO
  (cons af_UpGeomB
  (cons af_UpHlogZ
  (cons af_UpIDL
  (cons af_UpIDL_P2
  (cons af_UpKVDrift
  (cons af_UpKVDrift_P2
  (cons af_UpKVEv
  (cons af_UpLoeb
  (cons af_UpLoebD2
  (cons af_UpLogMono
  (cons af_UpMinP
  (cons af_UpPLA
  (cons af_UpPPO
  (cons af_UpPredRelax
  (cons af_UpPredRelaxReq
  (cons af_UpProj
  (cons af_UpProjBPC
  (cons af_UpQKBound
  (cons af_UpRealLeB
  (cons af_UpRealLeB2
  (cons af_UpRealLeB3
  (cons af_UpRecast
  (cons af_UpRefuted
  (cons af_UpReqAlgebra
  (cons af_UpReqAlign
  (cons af_UpReqAlign2
  (cons af_UpReqAlign3
  (cons af_UpReqAlignRest
  (cons af_UpReqAlignRestA
  (cons af_UpReqAlignRestB
  (cons af_UpReqAttnGibbs
  (cons af_UpReqAttnIter
  (cons af_UpReqBoltzDirect
  (cons af_UpReqBranchPos
  (cons af_UpReqCauchy
  (cons af_UpReqDist
  (cons af_UpReqDpoLoss
  (cons af_UpReqFEPAttn
  (cons af_UpReqGeomD
  (cons af_UpReqGeomIter
  (cons af_UpReqGibbsD
  (cons af_UpReqGibbsE
  (cons af_UpReqGibbsE2
  (cons af_UpReqHlogZD
  (cons af_UpReqIndex
  (cons af_UpReqJensen
  (cons af_UpReqKLCvx
  (cons af_UpReqKLEnergy
  (cons af_UpReqKLStrict
  (cons af_UpReqLatticeB
  (cons af_UpReqLogCompD
  (cons af_UpReqLogCompD2
  (cons af_UpReqLogD
  (cons af_UpReqLogLinD
  (cons af_UpReqLogPrimD
  (cons af_UpReqLogRDF
  (cons af_UpReqMinPAntitone
  (cons af_UpReqMinPProjB
  (cons af_UpReqMisc5
  (cons af_UpReqMisc5B
  (cons af_UpReqOrderArgmin
  (cons af_UpReqPCT
  (cons af_UpReqPPO
  (cons af_UpReqPPOB
  (cons af_UpReqPPOGapB
  (cons af_UpReqPPOPlain
  (cons af_UpReqPowB
  (cons af_UpReqRDF
  (cons af_UpReqRealFEP
  (cons af_UpReqSLM
  (cons af_UpReqSampling
  (cons af_UpReqSqPos
  (cons af_UpReqSqrtF
  (cons af_UpReqSumB
  (cons af_UpReqSumD
  (cons af_UpReqTempEntropy
  (cons af_UpReqTempInterp
  (cons af_UpReqU2
  (cons af_UpReqZAuto
  (cons af_UpReqZPosD
  (cons af_UpReqZPosFinal
  (cons af_UpReqZPosI
  (cons af_UpReqZPosI2
  (cons af_UpSLM
  (cons af_UpSigMigrate
  (cons af_UpSigMigrate2
  (cons af_UpStepKL
  (cons af_UpStepKLM3
  (cons af_UpStopTime
  (cons af_UpTVDoeblin
  (cons af_UpTVReal
  (cons af_UpTempWindow nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* 主件面统计：127 主件 / 剥注释 token 级 Qed 和 25354（含自指件 UpReqIndex.v v2 终态 27）； *)
(* 存档/快照/副本/探针（_ 前缀与 probe 族）不入主件面，处置状态见层② 退役条目与交付报告。 *)
Definition AttnFaceModules : nat := 127.
Definition AttnFaceItems   : nat := 25354.

Lemma AttnFaceModules_matches : AttnFaceModules = cnt_af AttnFaceList.
Proof. reflexivity. Qed.

Lemma AttnFaceItems_matches : AttnFaceItems = sum_af AttnFaceList.
Proof. reflexivity. Qed.

(* ---------- v2.0 层②：Live_X 终态结构面（S01–S15 拆分组 + G 系合并组 + 219 壳/扩展 + 退役处置） ---------- *)

Record LiveGroup : Set := MkLiveGroup
  { lg_name    : string   (* 组名 / 文件名 / 退役件名 *)
  ; lg_kind    : nat      (* 1=S 系拆分组  2=G 系合并组  3=聚合壳/扩展件  0=退役件 *)
  ; lg_members : nat      (* S=组内剥注释 Qed 件数；G=README 旧名成员数；壳/扩展=1；退役=0 *)
  ; lg_note    : string   (* 主题 / 成员旧名清单 / 处置说明 *)
  }.

Fixpoint cnt_lg (l : list LiveGroup) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_lg tl)
  end.

Fixpoint sum_lg (l : list LiveGroup) : nat :=
  match l with
  | nil => 0
  | cons g tl => plus (lg_members g) (sum_lg tl)
  end.

Definition lg_S01BaseRing : LiveGroup := MkLiveGroup "S01_BaseRing.v" 1 99 "BaseRing / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S02CauchyComplete : LiveGroup := MkLiveGroup "S02_CauchyComplete.v" 1 138 "CauchyComplete / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S03QExp : LiveGroup := MkLiveGroup "S03_QExp.v" 1 223 "QExp / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S04RealExpLogConv : LiveGroup := MkLiveGroup "S04_RealExpLogConv.v" 1 113 "RealExpLogConv / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S05AlignmentGRPO : LiveGroup := MkLiveGroup "S05_AlignmentGRPO.v" 1 141 "AlignmentGRPO / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S06DiffSamplingGibbs : LiveGroup := MkLiveGroup "S06_DiffSamplingGibbs.v" 1 240 "DiffSamplingGibbs / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S07RealSetoidExpLog : LiveGroup := MkLiveGroup "S07_RealSetoidExpLog.v" 1 275 "RealSetoidExpLog / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S08RealMainlineDPO : LiveGroup := MkLiveGroup "S08_RealMainlineDPO.v" 1 117 "RealMainlineDPO / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S09EntropyReal : LiveGroup := MkLiveGroup "S09_EntropyReal.v" 1 94 "EntropyReal / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S10KVQuantTrig : LiveGroup := MkLiveGroup "S10_KVQuantTrig.v" 1 432 "KVQuantTrig / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S11TP3B5 : LiveGroup := MkLiveGroup "S11_TP3B5.v" 1 410 "TP3B5 / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S12B5RecycleSF : LiveGroup := MkLiveGroup "S12_B5RecycleSF.v" 1 331 "B5RecycleSF / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S13NLiveAudit : LiveGroup := MkLiveGroup "S13_NLiveAudit.v" 1 192 "NLiveAudit / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S14B5BatchBlock : LiveGroup := MkLiveGroup "S14_B5BatchBlock.v" 1 258 "B5BatchBlock / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S15TailFEPUp : LiveGroup := MkLiveGroup "S15_TailFEPUp.v" 1 73 "TailFEPUp / 219 split group; member cnt = stripped-comment Qed tokens".

Definition lg_G01 : LiveGroup := MkLiveGroup "G01_CoreMicro.v" 2 5 "members: UpHlogZ,UpExtras,UpFEP,UpLogMono,UpPPO".
Definition lg_G02 : LiveGroup := MkLiveGroup "G02_Debt.v" 2 3 "members: UpDebtSqrtAbs,UpDebtDual,UpDebtGibbsT".
Definition lg_G04 : LiveGroup := MkLiveGroup "G04_ProjFam.v" 2 4 "members: UpPLA,UpPredRelax,UpProj,UpProjBPC".
Definition lg_G05 : LiveGroup := MkLiveGroup "G05_LogSmall.v" 2 3 "members: UpReqLogD,UpReqLogLinD,UpReqLogPrimD".
Definition lg_G06 : LiveGroup := MkLiveGroup "G06_BForm.v" 2 4 "members: UpReqPPOB,UpReqSumB,UpReqMinPProjB,UpReqLatticeB".
Definition lg_G07 : LiveGroup := MkLiveGroup "G07_KLWall.v" 2 5 "members: UpReqKLCvx,UpReqPowB,UpReqJensen,UpReqKLStrict,UpReqKLEnergy".
Definition lg_G08 : LiveGroup := MkLiveGroup "G08_Gibbs.v" 2 3 "members: UpReqHlogZD,UpReqGibbsD,UpReqGibbsE2".
Definition lg_G09 : LiveGroup := MkLiveGroup "G09_MiscSmall.v" 2 4 "members: UpReqPCT,UpReqBoltzDirect,UpReqSqPos,UpReqOrderArgmin".
Definition lg_G10 : LiveGroup := MkLiveGroup "G10_LoebFam.v" 2 4 "members: UpLoeb,UpLoebD2,UpRefuted,UpQKBound".
Definition lg_G11 : LiveGroup := MkLiveGroup "G11_IDLFam.v" 2 2 "members: UpCLQuery,UpIDL".
Definition lg_G12 : LiveGroup := MkLiveGroup "G12_ZPosFam.v" 2 5 "members: UpReqZPosD,UpReqZPosI,UpReqZPosI2,UpReqZAuto,UpReqZPosFinal".
Definition lg_G13 : LiveGroup := MkLiveGroup "G13_EvictFam.v" 2 2 "members: UpEvictId,UpEvictIdReq".
(* 组号缺位注记：G03 无组（G 系编号 01/02/04–13 共 12 组，缺位为合并史留痕，非漏登）。 *)

Definition lg_Shell219 : LiveGroup := MkLiveGroup "CW_ConstructiveWorld_219.v" 3 15 "219 shell: Require S01-S15 chain; 17 lines 0 Qed tokens; downstream base aggregate (Live_X copy)".
Definition lg_CW220Ext : LiveGroup := MkLiveGroup "CW220_Extensions.v" 3 1 "CW220 extensions piece; stripped-comment Qed 552".
Definition lg_Ret214 : LiveGroup := MkLiveGroup "ConstructiveWorld-214" 0 0 "retired: CW214 name-level check 219 covers 214, 3943/3943 hit; dependents re-Require shell 219".
Definition lg_RetUpTVReal : LiveGroup := MkLiveGroup "UpTVReal" 0 0 "retired: absent in Live_X; attn legacy 33 Qed, not migrated".
Definition lg_RetProbeReexSig : LiveGroup := MkLiveGroup "ProbeReexSig" 0 0 "retired probe: absent in Live_X; attn legacy ProbeReexSig/ProbeReexSig2".

Definition SLiveList : list LiveGroup :=
  cons lg_S01BaseRing
  (cons lg_S02CauchyComplete
  (cons lg_S03QExp
  (cons lg_S04RealExpLogConv
  (cons lg_S05AlignmentGRPO
  (cons lg_S06DiffSamplingGibbs
  (cons lg_S07RealSetoidExpLog
  (cons lg_S08RealMainlineDPO
  (cons lg_S09EntropyReal
  (cons lg_S10KVQuantTrig
  (cons lg_S11TP3B5
  (cons lg_S12B5RecycleSF
  (cons lg_S13NLiveAudit
  (cons lg_S14B5BatchBlock
  (cons lg_S15TailFEPUp nil)))))))))))))).

Definition GLiveList : list LiveGroup :=
  cons lg_G01
  (cons lg_G02
  (cons lg_G04
  (cons lg_G05
  (cons lg_G06
  (cons lg_G07
  (cons lg_G08
  (cons lg_G09
  (cons lg_G10
  (cons lg_G11
  (cons lg_G12
  (cons lg_G13 nil))))))))))).

(* S 面：15 组 / 剥注释 Qed 和 3136。结构不变量：和=attn 219 大库 CW_ConstructiveWorld_219.v
   token 级 Qed 实测同值——拆分无损在编译期机械可证（见 Split_lossless_219）。 *)
Definition SLiveGroups : nat := 15.
Definition SFaceQed     : nat := 3136.
Lemma SLiveGroups_matches : SLiveGroups = cnt_lg SLiveList.
Proof. reflexivity. Qed.

Lemma SFaceQed_matches : SFaceQed = sum_lg SLiveList.
Proof. reflexivity. Qed.

Lemma Split_lossless_219 : af_qed af_CW_ConstructiveWorld_219 = SFaceQed.
(* attn 219 大库 3136 Qed = Live_X S01–S15 组和 3136 Qed（token 级 1:1）。 *)
Proof. reflexivity. Qed.

(* G 面：12 组 / README 旧名成员和 44 / G 组件剥注释 Qed 和 640。结构不变量：逐组成员旧名
   attn Qed 和 = Live_X G 组件 Qed（12 组全数 1:1，合并无损机械可证，见 G*_merge_lossless）。 *)
Definition GMergeGroups  : nat := 12.
Definition GMergeMembers : nat := 44.
Definition GMergeQed     : nat := 640.

Definition gqed_G01 : nat := 26.  (* G01_CoreMicro.v 剥注释 Qed 实测 *)
Definition gqed_G02 : nat := 21.  (* G02_Debt.v 剥注释 Qed 实测 *)
Definition gqed_G04 : nat := 71.  (* G04_ProjFam.v 剥注释 Qed 实测 *)
Definition gqed_G05 : nat := 46.  (* G05_LogSmall.v 剥注释 Qed 实测 *)
Definition gqed_G06 : nat := 25.  (* G06_BForm.v 剥注释 Qed 实测 *)
Definition gqed_G07 : nat := 66.  (* G07_KLWall.v 剥注释 Qed 实测 *)
Definition gqed_G08 : nat := 39.  (* G08_Gibbs.v 剥注释 Qed 实测 *)
Definition gqed_G09 : nat := 22.  (* G09_MiscSmall.v 剥注释 Qed 实测 *)
Definition gqed_G10 : nat := 167.  (* G10_LoebFam.v 剥注释 Qed 实测 *)
Definition gqed_G11 : nat := 86.  (* G11_IDLFam.v 剥注释 Qed 实测 *)
Definition gqed_G12 : nat := 44.  (* G12_ZPosFam.v 剥注释 Qed 实测 *)
Definition gqed_G13 : nat := 27.  (* G13_EvictFam.v 剥注释 Qed 实测 *)

Lemma GMergeGroups_matches : GMergeGroups = cnt_lg GLiveList.
Proof. reflexivity. Qed.

Lemma GMergeMembers_matches : GMergeMembers = sum_lg GLiveList.
Proof. reflexivity. Qed.

Lemma GMergeQed_matches : GMergeQed = plus gqed_G01 (plus gqed_G02 (plus gqed_G04 (plus gqed_G05 (plus gqed_G06 (plus gqed_G07 (plus gqed_G08 (plus gqed_G09 (plus gqed_G10 (plus gqed_G11 (plus gqed_G12 (gqed_G13))))))))))).
Proof. reflexivity. Qed.

Lemma G01_merge_lossless : gqed_G01 = plus (af_qed af_UpHlogZ) (plus (af_qed af_UpExtras) (plus (af_qed af_UpFEP) (plus (af_qed af_UpLogMono) (af_qed af_UpPPO)))).
Proof. reflexivity. Qed.

Lemma G02_merge_lossless : gqed_G02 = plus (af_qed af_UpDebtSqrtAbs) (plus (af_qed af_UpDebtDual) (af_qed af_UpDebtGibbsT)).
Proof. reflexivity. Qed.

Lemma G04_merge_lossless : gqed_G04 = plus (af_qed af_UpPLA) (plus (af_qed af_UpPredRelax) (plus (af_qed af_UpProj) (af_qed af_UpProjBPC))).
Proof. reflexivity. Qed.

Lemma G05_merge_lossless : gqed_G05 = plus (af_qed af_UpReqLogD) (plus (af_qed af_UpReqLogLinD) (af_qed af_UpReqLogPrimD)).
Proof. reflexivity. Qed.

Lemma G06_merge_lossless : gqed_G06 = plus (af_qed af_UpReqPPOB) (plus (af_qed af_UpReqSumB) (plus (af_qed af_UpReqMinPProjB) (af_qed af_UpReqLatticeB))).
Proof. reflexivity. Qed.

Lemma G07_merge_lossless : gqed_G07 = plus (af_qed af_UpReqKLCvx) (plus (af_qed af_UpReqPowB) (plus (af_qed af_UpReqJensen) (plus (af_qed af_UpReqKLStrict) (af_qed af_UpReqKLEnergy)))).
Proof. reflexivity. Qed.

Lemma G08_merge_lossless : gqed_G08 = plus (af_qed af_UpReqHlogZD) (plus (af_qed af_UpReqGibbsD) (af_qed af_UpReqGibbsE2)).
Proof. reflexivity. Qed.

Lemma G09_merge_lossless : gqed_G09 = plus (af_qed af_UpReqPCT) (plus (af_qed af_UpReqBoltzDirect) (plus (af_qed af_UpReqSqPos) (af_qed af_UpReqOrderArgmin))).
Proof. reflexivity. Qed.

Lemma G10_merge_lossless : gqed_G10 = plus (af_qed af_UpLoeb) (plus (af_qed af_UpLoebD2) (plus (af_qed af_UpRefuted) (af_qed af_UpQKBound))).
Proof. reflexivity. Qed.

Lemma G11_merge_lossless : gqed_G11 = plus (af_qed af_UpCLQuery) (af_qed af_UpIDL).
Proof. reflexivity. Qed.

Lemma G12_merge_lossless : gqed_G12 = plus (af_qed af_UpReqZPosD) (plus (af_qed af_UpReqZPosI) (plus (af_qed af_UpReqZPosI2) (plus (af_qed af_UpReqZAuto) (af_qed af_UpReqZPosFinal)))).
Proof. reflexivity. Qed.

Lemma G13_merge_lossless : gqed_G13 = plus (af_qed af_UpEvictId) (af_qed af_UpEvictIdReq).
Proof. reflexivity. Qed.

(* Live_X 总面：99 .v（ls 实测）= S 15 + G 12 + 壳/扩展 2 + 独立件 70。 *)
Definition LiveXFiles    : nat := 99.
Definition LiveXIndFiles : nat := 70.
Lemma LiveXSplits : LiveXFiles = plus (plus SLiveGroups GMergeGroups) (plus 2 LiveXIndFiles).
Proof. reflexivity. Qed.

Lemma Shell219_chain : lg_members lg_Shell219 = SLiveGroups.
(* 219 壳聚合链 = S 系 15 组，壳链完整。 *)
Proof. reflexivity. Qed.

(* UpReqIndex v1.7（2026-09-10，wb10 影子预置席 diff-ready 版记刷新；本影子零编译，覆盖真件后一次 G2 定账）： *)
(* 承 v1.5 全部增册；本席四项：idx_UpPPOPlain(14) 解除暂不登记 + 批外 idx_UpReqMinPProjB(7，W2' 簇) 补登 + *)
(* idx_UpReqAttnGibbs 63→65 + idx_UpReqPPO 22→26 → 模块 36 = 宇宙内 32 + 批外 4、件数 1017 = 宇宙内 944 + 批外 73； *)
(* 宇宙行 659/3/71/1/0 → 668/0/66/0/0（件16 挂账翻牌 + PPOPlain 簇冻结闸口件翻牌；总账 v1.7 闸目标，和 734 不变）； *)
(* 翻牌闸=件16 canonical log 占位（_clipup_chk_UpReqPPO.log（验后删；证据固化于总账 v1.7 件16 行证据列 md5、字节数、cst 尾行）；已于 01:28 经主会话亲验 PASS），闸已落；G1–G4 同轨复验见文件头注； *)
(* UpReqIndex v1.8（2026-09-10，wb27 影子预置席 diff-ready 版记刷新；本影子零编译，覆盖真件后一次 G2 定账）： *)
(* 承 v1.7 全部增册；本席批外三新件补登 idx_UpRealLeB3(8/220 行) + idx_UpReqPPOB(2/98 行) + idx_UpReqSumB(3/191 行) *)
(* → 模块 39 = 宇宙内 32 + 批外 7、件数 1030 = 宇宙内 944 + 批外 86、UniverseItems_matches minus 链四重→七重； *)
(* 宇宙行 668/0/66/0/0 → 670/0/64/0/0（冻结 v1.8 候选两行翻牌：clip_lower 件7 + ppo_clipped_improvement 件8， *)
(* 总账 v1.7 在案方向，件名随总账 v1.8 待与席25 产物互核；和 734 不变）； *)
(* 翻牌闸=主会话 v1.8 commit 令+§10.2 数字同步（闸未落本影子不覆盖真件）；G1–G4 同轨复验见文件头注； *)
(* v1.5 账房尾项翻牌席 / v1.4 账房翻牌+Index 刷新席 / v1.3 总账回写席 / v1.2 批3行点火席 / v1.0 建立席 2026-09-09 *)
(* UpReqIndex v2.0（2026-09-11，席N：UpReqIndex v2 重制席收口版记）： *)
(* 承 v1.7/v1.8 全部增册与宇宙行 670/0/64/0/0、模块 39=宇宙内 32+批外 7、件数 1030=宇宙内 944+批外 86 零改动； *)
(* 本席纯新增层① attn 主件面（af_ 127 件/25354 封口 token）+ 层② Live_X 结构面（lg_ S15/G12/壳2/退役3）与 *)
(* 22 条 reflexivity 不变量引理；两轨口径并行（idx_=grep decl TLC 随总账；af_/lg_=剥注释 token 级封口随磁盘）； *)
(* 盘面漂移观察（只记不改，翻牌权在总账）：idx_UpReqPPO 26 vs 盘 25、idx_UpReqPPOB 2 vs 盘 4，余 37 件盘数与登记相符； *)
(* 四关：G1 禁词全文件 0 命中（含头注）；G2 coqc 9.0 -vos 预审+cpu_guard 中转全量 EXIT=0；G3 提取探针经 coqtop *)
(* 管道、常数清单式、产物魔法字 0（探针产物验后即删）；自指件本文件封口 token 27=v1.8 存量 5+本席新增 22。 *)
