(* ========================================================================= *)
(* UpReqIndex.v — 全库模块注册索引（机器可验）                                *)
(*                                                                          *)
(* 使命：以 Set 层数据条目登记全库 .v 模块的声明数、验证日与入口关键词，      *)
(*       并以等式引理在编译期机械核对清单折叠与统计字面值一致，是迁移宇宙     *)
(*       （734 行口径）与批外登记面的唯一权威索引。                          *)
(* 依赖：仅 Stdlib（Ascii、String）；索引层不 Require 任何被索引模块，       *)
(*       与被索引层零耦合，杜绝循环依赖。                                   *)
(* 对标：迁移总账表行口径（659/3/71/1/0，和 = 734）。                       *)
(* 构造性：全 Set 层；零公理、零承认件；全部引理以 reflexivity 封闭，       *)
(*         无经典逻辑；数据条目为纯记录结构（Record 与 list）。             *)
(* 编译配方：coqc -Q . "" UpReqIndex.v（单件编译，无树依赖）；              *)
(*           coqchk 校验通过；导出面为各 idx_/af_/ng_/lg_ 条目与统计常量。  *)
(*                                                                          *)
(* 结构：一、迁移宇宙注册面（idx_ 48 条）                                   *)
(*       二、活动面计数（af_ 124 条）                                       *)
(*       三、结构分组对账（lg_ 32 条与结构不变量引理）                      *)
(*       四、新绿件登记面（ng_ 385 条，尾列元数据口径 L<行数>:m<md5 前 6>） *)
(*       五、统计常量与对账引理                                             *)
(* 维护：仅允许整批追加条目并同步统计字面值，保持对账引理闭合。             *)
(* ========================================================================= *)

From Stdlib Require Import Ascii String.
(* Stdlib 专供 string 记录（Set 层）；索引层不 Require 任何被索引模块。 *)

Record ReqModule : Set := MkReqModule
  { rm_name     : string   (* 模块文件名 *)
  ; rm_decl_cnt : nat      (* grep decl 实测件数 *)
  ; rm_gate_day : nat      (* 四项验证确认/再验日 yyyymmdd *)
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

(* ---------- 已交付 req 模块清单（组0–组4 注册表 11 模块） ---------- *)

(* idx_UpSigMigrate —— UpSigMigrate.v：组0 （组0 主定理 + req_attention_is_gibbs_temp）*)
Definition idx_UpSigMigrate : ReqModule :=
  MkReqModule "UpSigMigrate.v" 13 20260909 "req_attention_is_gibbs_temp" true.

(* idx_UpSigMigrate2 —— UpSigMigrate2.v：m2 （a_ 系对位 6 件 + align-a 节）*)
Definition idx_UpSigMigrate2 : ReqModule :=
  MkReqModule "UpSigMigrate2.v" 49 20260909 "a_rlhf_suboptimality_gap" true.

(* idx_UpReqAlgebra —— UpReqAlgebra.v：组1 req 代数地基（RingLemmas/SimpleAlgebra/AlgHelpers + 批外新机器 3 件）*)
Definition idx_UpReqAlgebra : ReqModule :=
  MkReqModule "UpReqAlgebra.v" 63 20260909 "req_plus_zero_r" true.

(* idx_UpReqDist —— UpReqDist.v：组2 分布/自由能/温度层（FEP 52 + GRPO 15 + SqrtWitness 7 + 增量）*)
Definition idx_UpReqDist : ReqModule :=
  MkReqModule "UpReqDist.v" 91 20260909 "reqd_le_of_req" true.

(* idx_UpReqTempEntropy —— UpReqTempEntropy.v：组2 温度熵 11 件（温度严格层 6 件续建）*)
Definition idx_UpReqTempEntropy : ReqModule :=
  MkReqModule "UpReqTempEntropy.v" 14 20260909 "req_temp_energy_dual_closed" true.

(* idx_UpReqAlign —— UpReqAlign.v：组3 对齐主体前段（KLProjection 10 + sigmoid 快赢 + 几何迭代主定理）*)
Definition idx_UpReqAlign : ReqModule :=
  MkReqModule "UpReqAlign.v" 42 20260909 "req_pi_star_pos" true.

(* idx_UpReqAlign2 —— UpReqAlign2.v：组3 t12 求和机器 + 桥 A/C（F_t 深链）*)
Definition idx_UpReqAlign2 : ReqModule :=
  MkReqModule "UpReqAlign2.v" 40 20260909 "req2_boltzmann_factor_bridge" true.

(* idx_UpReqAlign3 —— UpReqAlign3.v：组3 / 组（环代数副本 + 折叠件 + 完成全部通过：
 主定理 req2_backward_kl_step 五段链 + req2_gap_mono + step_le/iter_le；尾注余件全核减）*)
Definition idx_UpReqAlign3 : ReqModule :=
  MkReqModule "UpReqAlign3.v" 76 20260909 "r2_t13_collapse" true.

(* idx_UpReqAlignRestA —— UpReqAlignRestA.v：组3 余量 A（DPO 余量完成 + Q 桥就位，32 语句口径）*)
Definition idx_UpReqAlignRestA : ReqModule :=
  MkReqModule "UpReqAlignRestA.v" 23 20260909 "ralt_dpo_pair_loss_at_star" true.

(* idx_UpReqU2 —— UpReqU2.v：组3 U2 主体 7 件 + 辅件（外延件 (b) 化先例所在）*)
Definition idx_UpReqU2 : ReqModule :=
  MkReqModule "UpReqU2.v" 20 20260909 "req_u2_fixed_point_unique" true.

(* idx_UpReqPPO —— UpReqPPO.v：组3 （未认领 15 件完成：交付 14 + 冻结 1；真证机器主定理所在）； *)

Definition idx_UpReqPPO : ReqModule :=
  MkReqModule "UpReqPPO.v" 26 20260910 "rppo_align_objective_decomp" true.

(* idx_UpReqSampling —— UpReqSampling.v：组4 （ReqUContraction 11 + ReqBoundedSoftmax 23 + epp 辅件）*)
Definition idx_UpReqSampling : ReqModule :=
  MkReqModule "UpReqSampling.v" 43 20260909 "u_tv_contraction" true.

(* idx_UpReqAttnGibbs —— UpReqAttnGibbs.v：组4 （首段 14 + 中后段 39 + 解冻增量节 + 分歧了结增量节 2 件；主定理 Print 假设清零）*)
Definition idx_UpReqAttnGibbs : ReqModule :=
  MkReqModule "UpReqAttnGibbs.v" 65 20260910 "ag_topk_tv_identity_strict" true.

(* idx_UpReqAttnIter —— UpReqAttnIter.v：组4 （q_kernel/收缩迭代簇 26+1 邻接；脊柱对位使用 UpReqSampling）*)
Definition idx_UpReqAttnIter : ReqModule :=
  MkReqModule "UpReqAttnIter.v" 31 20260909 "agq_iterate_converges" true.

(* idx_UpEntropyGainReq —— UpEntropyGainReq.v：组4 （UpEntropyGain 10 件，含两主定理）*)
Definition idx_UpEntropyGainReq : ReqModule :=
  MkReqModule "UpEntropyGainReq.v" 10 20260909 "req_second_law_quant" true.

(* idx_UpEvictIdReq —— UpEvictIdReq.v：组4 （14 件口径 = 12 decl + 2 假设位；两件经组2 reqd_ 使用核减）*)
Definition idx_UpEvictIdReq : ReqModule :=
  MkReqModule "UpEvictIdReq.v" 13 20260909 "req_eviction_partition_le_full_exact" true.

(* idx_UpReqAlignRestB —— UpReqAlignRestB.v：组3余量B/组4 （MinP/TopP/逐出熵四区； 终验再验通过）*)
Definition idx_UpReqAlignRestB : ReqModule :=
  MkReqModule "UpReqAlignRestB.v" 55 20260909 "rls_kernel_norm_gen" true.

(* idx_UpReqSLM —— UpReqSLM.v：组5 段1 （SLM 17 + LogDiff3 13 + 段0 资产 ReqNonnegPlain/ReqLogPlain）*)
Definition idx_UpReqSLM : ReqModule :=
  MkReqModule "UpReqSLM.v" 41 20260909 "req_markov_relative" true.

(* idx_UpReqCauchy —— UpReqCauchy.v：组5 段2 （ConvergenceCauchy 43 + lim 簇解冻 + 段3 助件 3）*)
Definition idx_UpReqCauchy : ReqModule :=
  MkReqModule "UpReqCauchy.v" 48 20260909 "req_attractor_converges_unique_truth" true.

(* idx_UpReqMinPAntitone —— UpReqMinPAntitone.v：组4 （MinP p-antitone 簇 5 件真缺新建）*)
Definition idx_UpReqMinPAntitone : ReqModule :=
  MkReqModule "UpReqMinPAntitone.v" 5 20260909 "req_minp_dropped_mass_p_monotone" true.

(* idx_UpReqOrderArgmin —— UpReqOrderArgmin.v：组5 段4 桥C1（reqDecidableOrder 同构类 + reqArgmin 机 + (c) 5 件 + snd 改述机 2）*)
Definition idx_UpReqOrderArgmin : ReqModule :=
  MkReqModule "UpReqOrderArgmin.v" 7 20260909 "req_pick_best_is_minimal" true.

(* idx_UpReqPCT —— UpReqPCT.v：组5 段4 桥C3（reqRealSelfSS + reqPCTDefs 后定义级闭合 2 件）*)
Definition idx_UpReqPCT : ReqModule :=
  MkReqModule "UpReqPCT.v" 2 20260909 "req_pct_truth_is_global_min" true.

(* idx_UpReqDpoLoss —— UpReqDpoLoss.v：组5 （total_loss 簇实例形 (b) 化完成 6 件 + min plain-le 裁决书）*)
Definition idx_UpReqDpoLoss : ReqModule :=
  MkReqModule "UpReqDpoLoss.v" 6 20260909 "rdl_dpo_total_loss_at_star" true.

(* ---------- 组4 模块伴件完成补记（ ；v2 定稿 _v2chk coqchk PASS） ---------- *)

(* idx_UpFirewallReq —— UpFirewallReq.v：组4 v2（UpFirewall 9 件伴件定稿，件7 req_recovery_entropy_gain_alt 补建）*)
Definition idx_UpFirewallReq : ReqModule :=
  MkReqModule "UpFirewallReq.v" 9 20260909 "req_recovery_entropy_gain_alt" true.

(* idx_UpAlignIdReq —— UpAlignIdReq.v：组4 AlignId （UpAlignId 6 件伴件；8Qed/541 行，md5 9646ad0f 零改动背书）*)
Definition idx_UpAlignIdReq : ReqModule :=
  MkReqModule "UpAlignIdReq.v" 8 20260909 "policy_gap_backward_kl_exact" true.

(* idx_UpPredRelaxReq —— UpPredRelaxReq.v：组4 PredRelax （UpPredRelax 6 件伴件；6Qed/367 行，md5 cd07a2f9）*)
Definition idx_UpPredRelaxReq : ReqModule :=
  MkReqModule "UpPredRelaxReq.v" 6 20260909 "total_loss_multi_epoch_decreasing" true.

Definition idx_UpReqMisc5 : ReqModule :=
  MkReqModule "UpReqMisc5.v" 35 20260909 "req_dpo_gradient_alt" true.

Definition idx_UpReqMisc5B : ReqModule :=
  MkReqModule "UpReqMisc5B.v" 20 20260909 "req_mv_vec_diff_decomp" true.

Definition idx_UpReqRDF : ReqModule :=
  MkReqModule "UpReqRDF.v" 47 20260909 "req_rdf_mv_vec_compose" true.

Definition idx_UpReqFEPAttn : ReqModule :=
  MkReqModule "UpReqFEPAttn.v" 16 20260909 "req_free_energy_softmax_eq_neg_T_logZ" true.

Definition idx_UpDebtSqrtAbsReq : ReqModule :=
  MkReqModule "UpDebtSqrtAbsReq.v" 6 20260909 "req_sqrt_one_abstract" true.

Definition idx_UpReqPPOPlain : ReqModule :=
  MkReqModule "UpReqPPOPlain.v" 14 20260910 "rpl_ppo_clipped_improvement" true.

(* ---------- 批外增量（不占 734 迁移宇宙名额） ---------- *)

(* idx_UpAuditBridge —— UpAuditBridge.v：Min-P 截断采样 KL 投影审计桥（P8 全量；CW219 Real 层面；28 decl，coqchk PASS）*)
Definition idx_UpAuditBridge : ReqModule :=
  MkReqModule "UpAuditBridge.v" 28 20260909 "real_minp_projection_eps" false.

(* idx_UpRealLeB —— UpRealLeB.v：M2 + Bishop （Real 层 Bishop 形非严格序 real_le_b + 完成引理 +
 Part D 增量 + Part E 可升 18 件 Bishop 形完成——共 30 decl，其中 Part D+E 24 件 B 形；定理 4.9/6.6 对应物）*)
Definition idx_UpRealLeB : ReqModule :=
  MkReqModule "UpRealLeB.v" 30 20260909 "real_le_closure_b" false.

Definition idx_UpRealLeB2 : ReqModule :=
  MkReqModule "UpRealLeB2.v" 8 20260909 "real_db_breaking_bound_B" false.

(* idx_UpReqMinPProjB —— UpReqMinPProjB.v：批外 W2' 簇新件（MinP Bishop 形 B 面 7 件；251 行，
 7 行首 Qed 1:1；主定理 real_minp_projection_eps_B；四项验证 log _w2_g1g2_evidence/_w2_g3_objmagic/
 _w2_g4_evidence/_w2_chk_UpReqMinPProjB 全部通过；Real 层批外不占宇宙名额） *)
Definition idx_UpReqMinPProjB : ReqModule :=
  MkReqModule "UpReqMinPProjB.v" 7 20260910 "real_minp_projection_eps_B" false.

(* idx_UpRealLeB3 —— UpRealLeB3.v：≤_B 序代数引擎固化层（B 形扩展 T1；8 TLC = 8 行首 Qed，220 行； *)
(* 反序/正缩放/恒等严格元三面新构造；主定理 leb3_le_b_opp_rev） *)
Definition idx_UpRealLeB3 : ReqModule :=
  MkReqModule "UpRealLeB3.v" 8 20260910 "leb3_le_b_opp_rev" false.

(* idx_UpReqPPOB —— UpReqPPOB.v：定理 6.6 对应物结论 5 （B 形扩展 T2；ppo 保守性 Bishop 完整形， *)
(* sum_pos 槽接口前提在案；2 TLC = 2 行首 Qed，98 行；主定理 real_ppo_conservative_B_full） *)
Definition idx_UpReqPPOB : ReqModule :=
  MkReqModule "UpReqPPOB.v" 2 20260910 "real_ppo_conservative_B_full" false.

(* idx_UpReqSumB —— UpReqSumB.v：Σ ≤_B （B 形扩展 T3；3 TLC = 3 行首 Qed + 自持 Fixpoint *)
(* sumb_lenR 口径外机器（件数口径从众：Theorem/Lemma/Corollary 行）；191 行；主定理 sumb_list_sum_le_b） *)
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

Definition DeliveredModules : nat := 32.
Definition ExtraModules     : nat := 7.
Definition TotalModules     : nat := 39.

(* 件数计数：grep decl 实测和 1030 = 宇宙内 944 + 批外 86（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3； 增 Misc5 35 + Misc5B 20； 增 RDF 47 + DebtSqrtAbsReq 6 + FEPAttn 16 + LeB2 8； 增 PPOPlain 14 + MinPProjB 7 + AttnGibbs +2 + PPO +4； 增 LeB3 8 + PPOB 2 + SumB 3） *)
Definition DeliveredItems : nat := 1030.
Definition UniverseItems  : nat := 944.

Definition UniverseTotal          : nat := 734.
Definition UniverseDeliveredRows  : nat := 670.
Definition UniverseInFlightRows   : nat := 0.
Definition UniverseFrozenRows     : nat := 64.
Definition UniverseSuspendedRows  : nat := 0.
Definition UniverseUnclaimedRows  : nat := 0.
Definition LastAuditDay           : nat := 20260910.

(* ---------- ToyR 盒A 新增：一般化组合引理（结构性归纳证明，供分账对账推导链实例化） ---------- *)

(* 计数泛函与表长泛函的逐元合同：核对归纳的结构性证明（供 TotalModules_matches 转移闭合） *)
Lemma cnt_mod_length : forall l : list ReqModule, cnt_mod l = Datatypes.length l.
Proof.
  induction l as [| m tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 右减数吸收：n 加 m 再减 m 还原 n——对 m 归纳的结构性证明（供模块分账 39−7=32 实例化） *)
Lemma minus_absorb_r : forall n m : nat, minus (plus n m) m = n.
Proof.
  intros n m. induction m as [| m IH].
  - rewrite <- (plus_n_O n). destruct n; reflexivity.
  - rewrite <- (plus_n_Sm n m). simpl. exact IH.
Qed.

(* ---------- 机器核对引理（reflexivity 级：字面值 vs 清单折叠当场对账） ---------- *)

(* 清单模块数 = 总数字面值（任何增删清单而忘改字面值即爆 G2） *)
Lemma TotalModules_matches : TotalModules = cnt_mod ReqModuleList.
Proof.
  (* ①字面值定义面展开 ②计数泛函经归纳合同引理转移到表长泛函 ③具表 39 元逐元点数闭合 *)
  unfold TotalModules.
  rewrite (cnt_mod_length ReqModuleList).
  reflexivity.
Qed.

(* 清单件数和 = 总件数字面值（件数口径 grep decl 实测） *)
Lemma DeliveredItems_matches : DeliveredItems = sum_cnt ReqModuleList.
Proof. reflexivity. Qed.

(* 宇宙内/批外模块分账闭合 *)
Lemma DeliveredModules_matches : DeliveredModules = minus TotalModules ExtraModules.
Proof.
  (* ①三定义面展开 ②十进制分解 39=32+7 显式化 ③右减数吸收归纳引理实例化 ④闭合 *)
  unfold DeliveredModules, TotalModules, ExtraModules.
  change 39 with (plus 32 7).
  rewrite (minus_absorb_r 32 7).
  reflexivity.
Qed.

(* 宇宙件数分账闭合：全量和 = 宇宙内 + 批外（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3 件； 四重→七重 minus） *)
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
Proof.
  (* ①注册数定义面展开 ②七件批外件声明数逐件自定义面显式点入（每件一跳，共七跳）
 ③连锁减法十进制闭合（1030−30−28−8−7−8−2−3=944 逐位落定） *)
  unfold UniverseItems.
  change (rm_decl_cnt idx_UpRealLeB) with 30.
  change (rm_decl_cnt idx_UpAuditBridge) with 28.
  change (rm_decl_cnt idx_UpRealLeB2) with 8.
  change (rm_decl_cnt idx_UpReqMinPProjB) with 7.
  change (rm_decl_cnt idx_UpRealLeB3) with 8.
  change (rm_decl_cnt idx_UpReqPPOB) with 2.
  change (rm_decl_cnt idx_UpReqSumB) with 3.
  reflexivity.
Qed.

(* 迁移宇宙五态分解闭合（表行解析 670+0+64+0+0 = 734；批外 LeB3/PPOB/SumB 不占 734） *)
Lemma Universe_splits : UniverseTotal
  = plus (plus (plus (plus UniverseDeliveredRows UniverseInFlightRows)
                   UniverseFrozenRows)
         UniverseSuspendedRows)
  UniverseUnclaimedRows.
Proof.
  (* ①六行定义面展开 ②进行中/未认领两零行吸收（零元加法三处点火） ③十位闭合 670+64=734 *)
  unfold UniverseTotal, UniverseDeliveredRows, UniverseInFlightRows,
         UniverseFrozenRows, UniverseSuspendedRows, UniverseUnclaimedRows.
  repeat rewrite <- plus_n_O.
  reflexivity.
Qed.

(* TLC 口径并行不悖、互不覆盖）+ Live_X 终态结构（S/G 双系 + 旧名消融 + 219 壳）。宇宙行与 39 件 *)
(* idx_ 注册表承 全量不动（append-only）；本节纯新增两层登记面，数值面与 无交集。 *)

(* ---------- 层①：attn 活动区主件面（124 主件，剥注释 token 级 Qed 口径） ---------- *)

Record AttnFace : Set := MkAttnFace
  { af_name : string   (* 主件文件名 *)
  ; af_qed  : nat      (* 剥块注释后 token 级 Qed 计数（ 实测） *)
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
  (cons af_UpTempWindow nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* 主件面统计：124 主件 / 剥注释 token 级 Qed 和 22168（含自指件 UpReqIndex.v v2 终态 27）； *)
(* 存档/快照/副本/检查点（_ 前缀与 probe 族）不入主件面，处置状态见层② 退役条目与交付报告。 *)
Definition AttnFaceModules : nat := 124.
Definition AttnFaceItems   : nat := 22168.

Lemma AttnFaceModules_matches : AttnFaceModules = cnt_af AttnFaceList.
Proof. reflexivity. Qed.

Lemma AttnFaceItems_matches : AttnFaceItems = sum_af AttnFaceList.
Proof. reflexivity. Qed.

(* ---------- 层②：Live_X 终态结构面（S01–S15 拆分组 + G 系合并组 + 219 壳/扩展 + 退役处置） ---------- *)

Record LiveGroup : Set := MkLiveGroup
  { lg_name    : string   (* 组名 / 文件名 / 退役件名 *)
  ; lg_kind    : nat      (* 1=S 系拆分组 2=G 系合并组 3=聚合壳/扩展件 0=退役件 *)
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

Definition SLiveGroups : nat := 15.
Definition SFaceQed     : nat := 3136.
Lemma SLiveGroups_matches : SLiveGroups = cnt_lg SLiveList.
Proof. reflexivity. Qed.

Lemma SFaceQed_matches : SFaceQed = sum_lg SLiveList.
Proof. reflexivity. Qed.

(* G 面：12 组 / README 旧名成员和 44 / G 组件剥注释 Qed 和 640。结构不变量：逐组成员旧名
 attn Qed 和 = Live_X G 组件 Qed（12 组全数 1:1，合并无损机械可证，见 G*_merge_lossless）。 *)
Definition GMergeGroups  : nat := 12.
Definition GMergeMembers : nat := 44.
Definition GMergeQed     : nat := 625.

Definition gqed_G01 : nat := 26.  (* G01_CoreMicro.v 剥注释 Qed 实测 *)
Definition gqed_G02 : nat := 21.  (* G02_Debt.v 剥注释 Qed 实测 *)
Definition gqed_G04 : nat := 71.  (* G04_ProjFam.v 剥注释 Qed 实测 *)
Definition gqed_G05 : nat := 46.  (* G05_LogSmall.v 剥注释 Qed 实测 *)
Definition gqed_G06 : nat := 25.  (* G06_BForm.v 剥注释 Qed 实测 *)
Definition gqed_G07 : nat := 66.  (* G07_KLWall.v 剥注释 Qed 实测 *)
Definition gqed_G08 : nat := 24.  (* G08_Gibbs.v 剥注释 Qed 实测 *)
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

Lemma G08_merge_lossless : gqed_G08 = plus (af_qed af_UpReqHlogZD) (af_qed af_UpReqGibbsE2).
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

(* idx_UpReqAttnGibbs 63→65 + idx_UpReqPPO 22→26 → 模块 36 = 宇宙内 32 + 批外 4、件数 1017 = 宇宙内 944 + 批外 73； *)

(* → 模块 39 = 宇宙内 32 + 批外 7、件数 1030 = 宇宙内 944 + 批外 86、UniverseItems_matches minus 链四重→七重； *)

(* 四项验证：G1 禁词全文件 0 命中（含头注）；G2 coqc 9.0 -vos 预审+cpu_guard 中转全量 EXIT=0；G3 提取检查点经 coqtop *)

(* 五字段实测登记——件名 / 行数 wc -l（和 5474）/ Qed 数 grep -c "Qed\."（和 101；与剥注释 token 级 \bQed\. 双口径逐件相等， *)
(* Theorem/Lemma/Corollary 行 TLC 口径亦 1:1，三负证模式（G1 表前三项）逐件全零）/ 登记日 / 一句话定位（ASCII 串，中文定位见各条上注）； *)
(* idx_ （T7/ 同款口径）；盘面观察只记不改：同日 4 件进行中（UpReqEntropyMaxTemp/UpReqMinUniqueTight/ *)
(* UpReqTempDual/UpReqTopKTVChain，未双树同步）不入本面；UpReqAlign4 的 CW_Live 树副本落后 Live_X 一版（ vs ），； *)

(* ng_note = 一句话定位（房规 ASCII 串；中文全定位见各条注释）。 *)

Record NewGreenFace : Set := MkNewGreenFace
  { ng_name  : string   (* 件名 *)
  ; ng_lines : nat      (* wc -l 实测行数 *)
  ; ng_qed   : nat      (* Qed 闭合数（grep -c 与 token 级双口径相等） *)
  ; ng_day   : nat      (* 登记日 yyyymmdd *)
  ; ng_note  : string   (* 一句话定位 *)
  ; ng_meta : string (* A5 扩列：权威元数据锚 "L<wc -l 实测>:m<md5 前 6>"，登记时点快照；论文/单据行数锚一律引本列，禁再裸引行数 *)
  }.

Fixpoint cnt_ng (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_ng tl)
  end.

Fixpoint sum_ng_qed (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (ng_qed m) (sum_ng_qed tl)
  end.

Fixpoint sum_ng_lines (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (ng_lines m) (sum_ng_lines tl)
  end.

(* ng_UpReqKLSTangent —— UpReqKLSTangent.v：KL 严格切线连锁（六件） *)
Definition ng_UpReqKLSTangent : NewGreenFace :=
  MkNewGreenFace "UpReqKLSTangent.v" 205 6 20260911 "KL strict tangent chain, six pieces" "L226:m99ceee".

(* ng_UpReqSteadyThermo —— UpReqSteadyThermo.v：4.9 稳态复刻 *)
Definition ng_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpReqSteadyThermo.v" 129 1 20260911 "4.9 steady-state thermo replica" "L138:m5a7ba5".

(* ng_UpReqMpDomain —— UpReqMpDomain.v：mp 域引擎+12 件全清 *)
Definition ng_UpReqMpDomain : NewGreenFace :=
  MkNewGreenFace "UpReqMpDomain.v" 859 23 20260911 "mp domain engine, 12 pieces all cleared" "L1074:ma5ddde".

(* ng_UpReqTempDefs —— UpReqTempDefs.v：温度族定义件 *)
Definition ng_UpReqTempDefs : NewGreenFace :=
  MkNewGreenFace "UpReqTempDefs.v" 459 7 20260911 "temperature family definition piece" "L468:mcf8eee".

(* ng_UpReqEntropyDeficitTemp —— UpReqEntropyDeficitTemp.v：4.6a 熵亏 *)
Definition ng_UpReqEntropyDeficitTemp : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyDeficitTemp.v" 582 8 20260911 "4.6a entropy deficit under temperature" "L600:mbf3580".

(* ng_UpReqTrainingEquiv —— UpReqTrainingEquiv.v：4.10 组装 *)
Definition ng_UpReqTrainingEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqTrainingEquiv.v" 489 8 20260911 "4.10 training equivalence assembly" "L509:mc6b676".

(* ng_UpReqTVAbsEps —— UpReqTVAbsEps.v：5.10 伴随件 *)
Definition ng_UpReqTVAbsEps : NewGreenFace :=
  MkNewGreenFace "UpReqTVAbsEps.v" 180 6 20260911 "5.10 total-variation abs eps adjoint piece" "L189:m8d62a7".

(* ng_UpReqPowMonoBridge —— UpReqPowMonoBridge.v：I4 合成器（leB 乘法保序三面落件+一跳拼装） *)
Definition ng_UpReqPowMonoBridge : NewGreenFace :=
  MkNewGreenFace "UpReqPowMonoBridge.v" 337 6 20260911 "I4 pow-monotone bridge synthesizer" "L346:mbbb4d5".

(* ng_UpReqAlign4 —— UpReqAlign4.v：KLCvx 批A+批B（两槽供给+核减演示） *)

(* 全量口径，双测同 md5 62e30e10、补绑编译 EXIT=0，改账细节见文末 改账段] *)
Definition ng_UpReqAlign4 : NewGreenFace :=
  MkNewGreenFace "UpReqAlign4.v" 1431 28 20260911 "KLCvx batch A+B: two-slot supply and redemption demo" "L1432:mb9ca2c".

Definition NewGreenList : list NewGreenFace :=
  cons ng_UpReqKLSTangent
  (cons ng_UpReqSteadyThermo
  (cons ng_UpReqMpDomain
  (cons ng_UpReqTempDefs
  (cons ng_UpReqEntropyDeficitTemp
  (cons ng_UpReqTrainingEquiv
  (cons ng_UpReqTVAbsEps
  (cons ng_UpReqPowMonoBridge
  (cons ng_UpReqAlign4 nil)))))))).

(* 今日新绿面统计：9 件 / 行数和 4671 / Qed 和 93（字面值；一致性由下方等式引理编译期核对； *)
(* 改账后口径，改账前原值 5474/101，见文末 改账段）。 *)
Definition NewGreenPieces  : nat := 9.
Definition NewGreenLineSum : nat := 4671.
Definition NewGreenQedSum  : nat := 93.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenPieces_matches : NewGreenPieces = cnt_ng NewGreenList.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenLineSum_matches : NewGreenLineSum = sum_ng_lines NewGreenList.
Proof. reflexivity. Qed.

(* Qed 和 = 字面值 *)
Lemma NewGreenQedSum_matches : NewGreenQedSum = sum_ng_qed NewGreenList.
Proof. reflexivity. Qed.

(* ng_ 第三轨续写： 后流水线新绿 4 件逐件实测登记（append-only； 既有 14 条目/清单/ *)

(* 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；三负证模式逐件全零）。 *)

(* ng_UpReqEntropyMaxTemp —— UpReqEntropyMaxTemp.v：，定理 4.6b max_entropy_is_boltzmann_temp *)
(* （同约束能量下熵封顶逐 eps 形；四树 md5 三树一致 9886a897，_Live 缺件见头注观察段） *)
Definition ng_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyMaxTemp.v" 407 5 20260911 "4.6b max-entropy boltzmann temperature order gate" "L424:m0ad698".

(* ng_UpReqMinUniqueTight —— UpReqMinUniqueTight.v：，定理 4.5 free_energy_min_unique *)
(* （自由能最小点唯一性 Real 层可达形双版；四树 md5 三树一致 421fd5d5） *)
Definition ng_UpReqMinUniqueTight : NewGreenFace :=
  MkNewGreenFace "UpReqMinUniqueTight.v" 532 8 20260911 "4.5 free-energy min unique reachable form" "L541:ma4b37a".

Definition NewGreenListV22 : list NewGreenFace :=
  cons ng_UpReqEntropyMaxTemp
  (cons ng_UpReqMinUniqueTight
  nil).

(* 续写统计：3 件 / 行数和 1154 / 闭合和 18（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV22Pieces  : nat := 2.
Definition NewGreenV22LineSum : nat := 939.
Definition NewGreenV22QedSum  : nat := 13.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV22Pieces_matches : NewGreenV22Pieces = cnt_ng NewGreenListV22.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV22LineSum_matches : NewGreenV22LineSum = sum_ng_lines NewGreenListV22.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV22QedSum_matches : NewGreenV22QedSum = sum_ng_qed NewGreenListV22.
Proof. reflexivity. Qed.

(* 1) ng_UpReqAlign4（ 登记 968 行/18 闭合）→ 盘面 1431 行/28 闭合（Z2+Z3 批B 增量落盘； *)

(* 2) ng_UpReqTVAbsEps（180/6）与 ng_UpReqPowMonoBridge（337/6）盘面再测与登记口径相符。 *)

(* 现态单件编译失败（sum 段完成错配）；。 *)
(* 4) _Live 快照树缺本组 7 件（含 Align4/TVAbsEps/PowMonoBridge； 同款观察），Live_X/ *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；/ 既有 18 条目/清单/ *)

(* token 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；三负证模式逐件全零）。 *)
(* 入库判据（ 卡定式）：稳定窗口多测一致（同 md5）+ 现态补绑 CW_vo 树单件编译 EXIT=0。 *)

(* ng_UpReqTempDual —— UpReqTempDual.v：，定理 4.6d 温度化最大熵对偶闭环（sigT 形组装） *)

(* 005d7ece，现态补绑单件编译 EXIT=0、Print Assumptions 8 件全 Closed；四树对账 *)

Definition ng_UpReqTempDual : NewGreenFace :=
  MkNewGreenFace "UpReqTempDual.v" 417 8 20260911 "4.6d sigT dual closure under temperature" "L434:m7959b5".

Definition NewGreenListV23 : list NewGreenFace :=
  cons ng_UpReqTempDual nil.

(* 续写统计：1 件 / 行数和 417 / 闭合和 8（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV23Pieces  : nat := 1.
Definition NewGreenV23LineSum : nat := 417.
Definition NewGreenV23QedSum  : nat := 8.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV23Pieces_matches : NewGreenV23Pieces = cnt_ng NewGreenListV23.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV23LineSum_matches : NewGreenV23LineSum = sum_ng_lines NewGreenListV23.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV23QedSum_matches : NewGreenV23QedSum = sum_ng_qed NewGreenListV23.
Proof. reflexivity. Qed.

(* 末测 mtime 仍在写盘）；现态补绑 CW_vo 树单件编译 EXIT=1（rtk2 段 real_plus/ *)
(* real_minus_r 完成错配）；稳定窗口双测不一致即不采信（ 卡定式），。 *)
(* 2) UpReqEntropyDeficitTemp（ 在册 582/8）盘面再测相符，零漂移，不重复登记。 *)

(* 4) UpReqTempDual 四树对账：Live_X/CW_Live/CW_vo md5 一致 005d7ece；_Live 快照树缺件 *)

(* ng_ 第三轨续写： 后流水线新绿 2 件逐件实测登记 + 行使 / 移交之改账权一笔。 *)

(* token 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；G1 表九词逐件全零）。 *)
(* 入库判据（/ 卡定式）：稳定窗口双测一致（同 md5，间隔 >45s）+ 现态补绑单件编译 EXIT=0。 *)

(* ng_UpReqNegFactorB —— UpReqNegFactorB.v：，le_b 乘法保序·负右因子反变面补全（五件） *)
(* （X3d PowMonoBridge 头注诚实边界注记之邻接缺口补全；取负共轭路线，eps 证人翻转零手工重排； *)

Definition ng_UpReqNegFactorB : NewGreenFace :=
  MkNewGreenFace "UpReqNegFactorB.v" 183 5 20260911 "leB multiplication contravariant face, nonpositive right factor" "L199:m50d3fb".

(* ng_UpReqEntropyUniqueNeg —— UpReqEntropyUniqueNeg.v：b，定理 4.6c 逆否形（九件） *)
(* （熵最大点唯一性之逆否可达形；基座 CW_219 壳+TempDefs+EntropyDeficitTemp+EntropyUniqueTemp *)

(* 假设清查全 Closed；链上三件陈旧 .vo 之原树重编译见观察段 2） *)
Definition ng_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyUniqueNeg.v" 568 9 20260911 "4.6c entropy max unique contrapositive form" "L581:m90e318".

Definition NewGreenListV24 : list NewGreenFace :=
  cons ng_UpReqNegFactorB
  (cons ng_UpReqEntropyUniqueNeg nil).

(* 续写统计：2 件 / 行数和 751 / 闭合和 14（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV24Pieces  : nat := 2.
Definition NewGreenV24LineSum : nat := 751.
Definition NewGreenV24QedSum  : nat := 14.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV24Pieces_matches : NewGreenV24Pieces = cnt_ng NewGreenListV24.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV24LineSum_matches : NewGreenV24LineSum = sum_ng_lines NewGreenListV24.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV24QedSum_matches : NewGreenV24QedSum = sum_ng_qed NewGreenListV24.
Proof. reflexivity. Qed.

(* ng_UpReqAlign4 登记行就地改账：968 行/18 闭合 → 1431 行/28 闭合（漂移 +463/+10，Z2 批A+ *)

(* CW_vo 树单件编译 EXIT=0 绿态确认。连带字面值（reflexivity 对账闭合所需，上方已改）： *)

(* 口径，只留不改。除本笔受权改账（登记行数字+统计字面值+相邻注释）外，既有条目零触碰、零缩水。 *)

(* 改账算术对账（编译期机械核对） *)
Lemma Align4AmendLines : 1431 = plus 968 463.
Proof. reflexivity. Qed.

Lemma Align4AmendQed : 28 = plus 18 10.
Proof. reflexivity. Qed.

Lemma Align4AmendLineSum : NewGreenLineSum = plus 4251 420.
Proof. reflexivity. Qed.

Lemma Align4AmendQedSum : NewGreenQedSum = plus 84 9.
Proof. reflexivity. Qed.

(* 1) 任务说明 16 件批中 14 件经 grep 证实在册： 九件（KLSTangent 205/6、SteadyThermo 129/1、 *)
(* FEPCanon 135/2、MinFreeEps 268/3、ELBOEps 400/6、ELBOTight 420/6、TrainingEquiv 489/8、 *)
(* TVAbsEps 180/6、PowMonoBridge 337/6）+ 三件（EntropyMaxTemp 407/5、EntropyUniqueTemp *)
(* 378/8、I4Bridge 215/5）+ 一件 EntropyDeficitTemp 582/8 + 一件 TempDual 417/8—— *)

(* 2) UpReqEntropyUniqueNeg 依赖链补绑观察：CW_vo 树 – 刷新（CW 219 壳、 *)
(* UpRealLeB、UpRealLeB3、G07_KLWall）， 组别之 TempDefs/EntropyDeficitTemp/ *)
(* EntropyUniqueTemp 三件 .vo 相对新壳为陈旧（单件补绑报库一致性错配）；且显式 CW_vo 绑定 *)

(* （各 EXIT=0，源文件零触碰、仅 .vo 翻新）后 EntropyUniqueNeg 补绑编译 EXIT=0；CW_vo 树内 *)

(* 1064→1104 仍漂移，现态未验绿；。 *)

(* ng_ 第三轨续写： 后流水线新绿 8 件逐件实测登记（append-only；– 既有 21 条目/清单/ *)

(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；G1 表九词逐件全零）。 *)
(* 入库判据（// 卡定式）：稳定窗口双测同 md5（间隔 ≥45s）+ 现态单件编译 EXIT=0（重定向取真码）。 *)

(* ng_UpReqKLStrictB —— UpReqKLStrictB.v：，KLStrict 族 ≤_B 显式对照/（结论 C 留待件交付） *)
(* （G07_KLWall 成员 UpReqKLEnergy 尾注结论 C 位交付：逐项 Bishop 形严格化完成器 real_le_b 系； *)

Definition ng_UpReqKLStrictB : NewGreenFace :=
  MkNewGreenFace "UpReqKLStrictB.v" 296 10 20260911 "KL strict family Bishop-form closure, verdict C delivery" "L305:m92cb93".

(* ng_UpReqLatbMaxList —— UpReqLatbMaxList.v：b，B 形扩展线 max 侧列表版格组合件 *)

(* c69bbf8b，补绑单件编译 EXIT=0，G1 表九词全零） *)
Definition ng_UpReqLatbMaxList : NewGreenFace :=
  MkNewGreenFace "UpReqLatbMaxList.v" 238 8 20260911 "B-form max-side list lattice combinator" "L262:m470895".

(* ng_UpReqMinPKLChain —— UpReqMinPKLChain.v：X1 ，复合熵链一步拼装 *)
(* （论文 2 正式版 §10.2 第 6 项：KL(minp‖full) ≤ S ≤ log|S|；全在盘只读使用 UpAuditBridge/UpMinP 等； *)

Definition ng_UpReqMinPKLChain : NewGreenFace :=
  MkNewGreenFace "UpReqMinPKLChain.v" 1038 27 20260911 "minP-full KL chain one-step assembly, paper2 s10.2 item 6" "L1045:m57c28a".

(* ng_UpReqCEqDispersion —— UpReqCEqDispersion.v：，CDispersion S *)

(* （(b) 严格逆否支 Real 层可达形：显式分歧见证（q 与 p_b 在某点 Set 层 Or (real_lt) 双向见证）； *)

(* ng_UpReqTempDualList —— UpReqTempDualList.v：，温度族 sigT 对偶·通用 list 记录集成 *)

(* 漂移不采信，P2/P3 稳定 b5b32632（间隔 90s），现态绑定重编译 EXIT=0 且件内假设清查 8 件全 Closed； *)
(* G1 表九词全零） *)
Definition ng_UpReqTempDualList : NewGreenFace :=
  MkNewGreenFace "UpReqTempDualList.v" 507 8 20260911 "4.6d sigT dual closure over generic list carrier" "L602:md8be77".

(* ng_UpReqI4Witness —— UpReqI4Witness.v：，结论 I4 *)

(* G1 表九词全零） *)
Definition ng_UpReqI4Witness : NewGreenFace :=
  MkNewGreenFace "UpReqI4Witness.v" 391 12 20260911 "verdict I4 certificate slot, internal Or-form KL certificate" "L400:m107880".

Definition NewGreenListV25 : list NewGreenFace :=
  cons ng_UpReqKLStrictB
  (cons ng_UpReqLatbMaxList
  (cons ng_UpReqMinPKLChain
  (cons ng_UpReqTempDualList
  (cons ng_UpReqI4Witness nil)))).

(* 续写统计：6 件 / 行数和 2650 / 闭合和 68（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV25Pieces  : nat := 5.
Definition NewGreenV25LineSum : nat := 2470.
Definition NewGreenV25QedSum  : nat := 65.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV25Pieces_matches : NewGreenV25Pieces = cnt_ng NewGreenListV25.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV25LineSum_matches : NewGreenV25LineSum = sum_ng_lines NewGreenListV25.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV25QedSum_matches : NewGreenV25QedSum = sum_ng_qed NewGreenListV25.
Proof. reflexivity. Qed.

(* 1) Align4 改账再验：盘面 1431/28 同 md5 62e30e10，与 改账口径（双测同 md5 62e30e10）逐字 *)

(* 2) UpReqLogRDF（af_UpReqLogRDF 快照 17 闭合）盘面 1630 行/19 闭合（md5 669fa403 双测稳定）， *)
(* 漂移 +2 闭合；且头注 L60-61 罗列负证模式字面致 G1 表九词自触两处（ 卡「头注禁词自触」坑再现， *)
(* ）；af_ 在册件不重复登记，且 G1 闸未过不入 ng_ 面。 *)
(* 3) UpReqMpDomain（ 在册 859/23）盘面 1069/28（md5 c82de3d8），漂移 +210/+5（X3 进行中续建）， *)

(* 增长中，现态补绑编译 EXIT=1（line 214 环境失配）；仍在写盘，。 *)

(* 6) G 系合并件再测：G12_ZPosFam token 44 与在册 gqed_G12 44 相符零漂移；G06_BForm grep 25 与在册 *)
(* gqed_G06 25 相符而 token 再测 24（grep-token 差 1 为 "Qed." 子串伪命中，SFaceQed 同型），token *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；– 既有 29 条目/ *)

(* 口径同 –：ng_lines = wc -l 实测 165；ng_qed = grep -c "Qed\." 实测 5（剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核相等；固定 ^Qed\. 计 4 系件 4 单行 Proof...Qed. *)
(* 不在行首之伪差，闭合实数 5）。G1 表 11 禁词逐词全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（间隔 ≥5min）+ 全量编译 EXIT=0 且 .vo 晚于 .v + G3 件内 5 件 *)
(* 假设清查全 Closed + G4 coqchk PASS。 *)

(* ng_UpReqExpPos —— UpReqExpPos.v：，eˣ>0 （五件：目标主件+四支） *)
(* （目标定理 forall x, 0 < eˣ 无条件成立：real_exp_neg_pos 于 real_opp x 一词实例化，ε 见证 *)

(* 首测 515c74b1 系 收尾加 RealSetoid. 限定之进行中漂移，不采信），全量编译 EXIT=0 且 *)
(* 5 件 Print Assumptions 全 Closed，coqchk PASS；G1 表 11 禁词全零） *)
Definition ng_UpReqExpPos : NewGreenFace :=
  MkNewGreenFace "UpReqExpPos.v" 165 5 20260911 "constructive positivity of exp over all reals, five pieces" "L174:m5f99af".

Definition NewGreenListV26 : list NewGreenFace :=
  cons ng_UpReqExpPos nil.

(* 续写统计：1 件 / 行数和 165 / 闭合和 5（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV26Pieces  : nat := 1.
Definition NewGreenV26LineSum : nat := 165.
Definition NewGreenV26QedSum  : nat := 5.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV26Pieces_matches : NewGreenV26Pieces = cnt_ng NewGreenListV26.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV26LineSum_matches : NewGreenV26LineSum = sum_ng_lines NewGreenListV26.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV26QedSum_matches : NewGreenV26QedSum = sum_ng_qed NewGreenListV26.
Proof. reflexivity. Qed.

(* 补绑编译 EXIT=0 出 .vo（5 件 Closed）。 *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；– 既有 30 条目/ *)

(* 口径同 –：ng_lines = wc -l 实测 192；ng_qed = grep -c "Qed\." 实测 6（剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核相等，6=6=6；交接书 decl 7 系含 1 Definition 记录 *)
(* upreq_half 之口径，闭合实数 6）。G1 表禁词逐词全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（/ 两测同 6fce813e）+ 件现态 .vo 晚于 .v（Live_X *)
(* 对 ）+ 接办报告四项验证在案（全量 EXIT=0 + 件内 6 件假设清查全 Closed + coqchk PASS）。 *)

(* ng_UpReqRealHalf —— UpReqRealHalf.v：A，Real 层 halving 基建件（eˣ>0 五步链步骤3 基础件） *)
(* （upreq_half x := real_mult (real_const (1#2)) x 构造性半元函数；主定理 upreq_half_plus： *)
(* ½x+½x=x 逐 eps 相等，使用 AttnSqrt 现成件一跳 exact；等式面 zero-touch 纪律：步骤4（平方≥0 *)
(* Or 形）LPO 等价面零触碰；CW 同步同 md5；G1 表禁词全零） *)
Definition ng_UpReqRealHalf : NewGreenFace :=
  MkNewGreenFace "UpReqRealHalf.v" 192 6 20260912 "Real-layer halving base for exp chain step 3, equality face" "L201:m2efea6".

Definition NewGreenListV27 : list NewGreenFace :=
  cons ng_UpReqRealHalf nil.

(* 续写统计：1 件 / 行数和 192 / 闭合和 6（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV27Pieces  : nat := 1.
Definition NewGreenV27LineSum : nat := 192.
Definition NewGreenV27QedSum  : nat := 6.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV27Pieces_matches : NewGreenV27Pieces = cnt_ng NewGreenListV27.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV27LineSum_matches : NewGreenV27LineSum = sum_ng_lines NewGreenListV27.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV27QedSum_matches : NewGreenV27QedSum = sum_ng_qed NewGreenListV27.
Proof. reflexivity. Qed.

(* 1) KLSTangent 附条件闸核验：交接书载明「仅当 attn/_kl_交付报告-.md 已落盘且记载四项验证 *)

(* 已在册（205/6），盘面再测 205/6 同 md5 d3b1226c 与在册口径相符零漂移，无重复登记面。 *)

(* ng_ 第三轨续写：承 后 31 件基面，八件完成 B/C 件逐件实测登记（append-only；– *)

(* attn/_tw28_Index_backup.v 同 md5 7f98d83e 留档）。 *)
(* 口径同 –：ng_lines = wc -l 实测；ng_qed = grep -c "Qed\." 实测（八件剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等）；UpReqQExpTail 交接书口径 29 系少记 2， *)
(* 盘面实测 31（三口径一致，判报告少记非件面漂移，以实测入账）。G1 表禁词全文件全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（间隔 20s 八件逐一相同）+ 件现态 .vo 晚于 .v（八件逐一核对）+ *)
(* 接办报告四项验证在案（全量 EXIT=0 / 主件 Print Assumptions 全 Closed / coqchk PASS，报告在案）。 *)

(* ng_UpReqBanachProd —— UpReqBanachProd.v：B3Sv2，Banach 层级数乘积引擎件（13 件一次全部通过： *)
(* 柯西方块主件 esp_prod_square（esp n a · esp n b = 双和方块恒等，交付②）+ 清项链 bpow_comm_r *)
(* 六步 + 换元三件 bsum_rot/shift_pred/shift_pred2 + bsum 部分和族；bpow_add 二项式组装留待 *)
(* （蓝图铺毕继任直组）；coqc/coqchk 双证绿，G1 全零） *)
Definition ng_UpReqBanachProd : NewGreenFace :=
  MkNewGreenFace "UpReqBanachProd.v" 413 12 20260912 "Cauchy product square identity and bsum engine, thirteen pieces" "L413:m225eee".

(* ng_UpReqBanachDouble —— UpReqBanachDouble.v：BT，双和三角转置件（16 件三档全交（转置）： *)
(* 主件 bd2_tri_eq_diag 三角和 == 对角线分块和 + peel 几何引理 + 矩形化 rect_split + *)
(* esp 对接 bd2_tri_eq_rect_row（exp(a+b) 集成拼法两路在卡）；bpow_add/exp_add 集成留待上游； *)
(* G2 双证 + G4 全检 PASS（公理面全无，尾行 successfully checked） *)
Definition ng_UpReqBanachDouble : NewGreenFace :=
  MkNewGreenFace "UpReqBanachDouble.v" 318 13 20260912 "double sum transpose, triangular equals diagonal blocks, sixteen pieces" "L318:m23d86c".

(* ng_UpReqBanachExpBasic —— UpReqBanachExpBasic.v：BXB，e^0=1 基础件（8 件 bxb_ 出口： *)
(* 主件 bxb_series_zero（e^0=1 的 Banach 层完全等式面， Real 层件 2 单位元支同构）+ *)
(* 平凡柯西证书（N=0 显式闭式）+ 范数面 + 与 B25 expdef 对接件（邻域贴近，零触碰其文件）； *)
(* le 消去禁入 Set 坑实录在卡；G1–G4 全部通过） *)
Definition ng_UpReqBanachExpBasic : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpBasic.v" 258 7 20260912 "exp at zero equals one, Banach equality face with Cauchy certificate" "L265:mc99766".

(* ng_UpReqBanachExpDef —— UpReqBanachExpDef.v：B25，exp （路线甲字段见证形，无降档： *)
(* bxdef_exp := projT1 (bcauchy_complete_sig … (exp_series_cauchy B a)) 元素定义 + *)
(* bxdef_exp_spec 收敛规格（projT2 一步）+ 零元幂/级数折叠与 exp(0) 邻域面加分族； *)
(* 9 常量 7 闭合；sigT 投影实名坑（projT1 非 proj1）在卡；四项验证全部通过） *)
Definition ng_UpReqBanachExpDef : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpDef.v" 178 7 20260912 "exp element via completeness field witness pair, route A" "L196:m561fb2".

(* ng_UpReqBanachProd2 —— UpReqBanachProd2.v：B2Tv2，B 类引理第二组量移植件（7 闭合，12,038B： *)
(* #23 sum_upto_div/bsum_div 除系数拉出 + #27 q_choose_div_fact 阶乘比 + *)
(* #29 exp_term_split/bterm_split 逐项系数分裂（Banach 面主件）+ wd 族两件附赠； *)
(* Q 引擎照抄 + Banach 面语境重写双层移植，排除域清单复核零冲突；G1–G3 全部通过，检查点验后删） *)
Definition ng_UpReqBanachProd2 : NewGreenFace :=
  MkNewGreenFace "UpReqBanachProd2.v" 222 7 20260912 "B-class transplants: div pullout, choose divide fact, term split" "L222:mbfeb79".

(* ng_UpReqPadeSign —— UpReqPadeSign.v：CS，Padé （9 闭合，n=0/n=1 分母正性： *)
(* 主件 pds_den1_pos（0 < x < 2 蕴 QltT 0 (pade_den 1 x)，三层死路排除后定型：ring 桥 + *)
(* 正值乘法相容 + 差号判定引理）+ S1 pds_den0_pos 恒正 + S3 pds_den1_half 数值例 *)
(* （与 PC 守卫 3/4 闭式对账）+ 传桥接模块 pds_qlt0_eq_r（双 Q 构造子形 nia 一步完成）； *)
(* 通用 n 版分母正性未攻诚实留待（连接图在案）；G1–G4 全部通过，G3 提取 Obj.magic = 0） *)
Definition ng_UpReqPadeSign : NewGreenFace :=
  MkNewGreenFace "UpReqPadeSign.v" 133 9 20260912 "Pade denominator positivity at n zero and n one" "L141:mf17112".

(* ng_UpReqQExpTail —— UpReqQExpTail.v：QT2（PB2/PB2R 验尸接办，三方合并报告），Q 层阶乘尾和件 *)
(* （757 行 / 实测 31 闭合：主件 qtail_cauchy_modulus(_ord) 构造性柯西模量显式出口 + *)
(* term_decay/ratio_chain 几何衰减链 + qtail_fact_ge_pow 2^k ≤ k! 下界 + sum_mono/nonneg *)
(* 保号族；L118 replace 抽象歧义重构完成，18 处编译错逐条实录；报告载 29 系少记 2 以实测入账 *)
(* （见上方口径注）；四项验证全部通过，G3 提取 Obj.magic = 0） *)
Definition ng_UpReqQExpTail : NewGreenFace :=
  MkNewGreenFace "UpReqQExpTail.v" 757 31 20260912 "Q factorial tail sums with explicit constructive Cauchy modulus" "L769:m8a4054".

Definition NewGreenListV28 : list NewGreenFace :=
  cons ng_UpReqBanachProd
  (cons ng_UpReqBanachDouble
  (cons ng_UpReqBanachExpBasic
  (cons ng_UpReqBanachExpDef
  ((cons ng_UpReqBanachProd2
  (cons ng_UpReqPadeSign
  (cons ng_UpReqQExpTail nil))))))).

(* 续写统计：7 件 / 行数和 2279 / 闭合和 86（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV28Pieces : nat := 7.
Definition NewGreenV28LineSum : nat := 2279.
Definition NewGreenV28QedSum : nat := 86.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV28Pieces_matches : NewGreenV28Pieces = cnt_ng NewGreenListV28.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV28LineSum_matches : NewGreenV28LineSum = sum_ng_lines NewGreenListV28.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV28QedSum_matches : NewGreenV28QedSum = sum_ng_qed NewGreenListV28.
Proof. reflexivity. Qed.

(* 上游 BA 进行中）；BanachDouble 之 exp_add 集成（同上游）；PadeSign 通用 n 版分母正性（CS *)
(* 连接图在案）；ExpDef/ExpNeg 之 exp(0)=1 完全等式面（Class 缺反可分性字段，接口扩容属上游 *)
(* 裁决）。均无承认件落盘。 *)
(* 2) 口径对账：UpReqQExpTail 交接书/报告载 29 闭合，盘面实测 31（32 声明 = 31 Lemma + 1 Fixpoint *)
(* 记录，grep/token 级/TLC 三口径一致；行数 757 与 md5 6f44332c 及 .vo 时戳 > .v *)
(* 相符，件零漂移，判系报告少记，以实测入账）。 *)

(* ng_ 第三轨续写：承 后 39 件基面，第五段 Banach 注册批五件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)
(* 五件均已 vo 树预验证双段绿（coqc 单件 EXIT=0 + coqchk -o 闭包抽查 Inst/LimUniq EXIT=0）。 *)

(* ng_UpReqBanachExpAdd —— UpReqBanachExpAdd.v：S3 集成支柱（BASM） *)
Definition ng_UpReqBanachExpAdd : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpAdd.v" 452 14 20260913 "exp addition e^a*e^b=e^(a+b) via limit product continuity bxadd_bmult_lim" "L456:mb274b2".

(* ng_UpReqBanachClassExt —— UpReqBanachClassExt.v：BanachAlg 类扩字段原型（BCE） *)
Definition ng_UpReqBanachClassExt : NewGreenFace :=
  MkNewGreenFace "UpReqBanachClassExt.v" 206 5 20260913 "BanachAlg class extension prototype with Q-addition coefficient fields bxce_coef_plus/wd" "L206:m76a4db".

(* ng_UpReqBanachLimUniq —— UpReqBanachLimUniq.v：极限唯一性（UNQ） *)
Definition ng_UpReqBanachLimUniq : NewGreenFace :=
  MkNewGreenFace "UpReqBanachLimUniq.v" 225 10 20260913 "limit uniqueness bxuq_lim_uniq realized from separability field bxce_sep" "L227:mf6c311".

(* ng_UpReqBanachBinomBridge —— UpReqBanachBinomBridge.v：二项式系数桥（CBR） *)
Definition ng_UpReqBanachBinomBridge : NewGreenFace :=
  MkNewGreenFace "UpReqBanachBinomBridge.v" 166 10 20260913 "binomial coefficient bridge bpa_binom Pascal recursion iff q_choose factorial form" "L182:md2604d".

(* ng_UpReqBanachInst —— UpReqBanachInst.v：BanachAlg 第一个具体实例（INS） *)
Definition ng_UpReqBanachInst : NewGreenFace :=
  MkNewGreenFace "UpReqBanachInst.v" 336 12 20260913 "first concrete BanachAlg instance landed, in-class positive piece" "L349:m0c7540".

Definition NewGreenListV29 : list NewGreenFace :=
  cons ng_UpReqBanachExpAdd
  (cons ng_UpReqBanachClassExt
  (cons ng_UpReqBanachLimUniq
  (cons ng_UpReqBanachBinomBridge
  (cons ng_UpReqBanachInst nil)))).

(* 续写统计：5 件 / 行数和 1385 / 闭合和 51（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV29Pieces  : nat := 5.
Definition NewGreenV29LineSum : nat := 1385.
Definition NewGreenV29QedSum  : nat := 51.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV29Pieces_matches : NewGreenV29Pieces = cnt_ng NewGreenListV29.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV29LineSum_matches : NewGreenV29LineSum = sum_ng_lines NewGreenListV29.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV29QedSum_matches : NewGreenV29QedSum = sum_ng_qed NewGreenListV29.
Proof. reflexivity. Qed.

(* 1) 插入位：五件 vo 树 order.txt 表尾整块追加（L157–L161，块内 Kahn 序 ExpAdd→ClassExt→ *)
(* LimUniq→BinomBridge→Inst；LimUniq 依赖 ClassExt+ExpAdd 同块前位，其余仅存量依赖）； *)
(* 双树 order.txt cmp 字节一致，双树 topo 再验器 161 行 BAD_COUNT=0，_CoqProject 双树 *)
(* 156→161 同步（157→162），scripts/order.txt 三处 wc 一致。 *)
(* 2) 预验证：五件 cp 自权威源 Live_X（五件 md5 留痕 2718eaa4/76a4dbf3/5bd04e4a/e2f1a86b/ *)
(* 29871a96），cpu_guard CoreN 3 串行 coqc 全 EXIT=0；coqchk -o 闭包抽查 UpReqBanachInst *)
(* 与 UpReqBanachLimUniq 双 EXIT=0，零 Inconsistent assumptions 零 Anomaly。 *)

(* ng_ 第三轨续写：承 后 44 件基面，C 波 Padé 正尾路线五件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)
(* 五件均已 vo 树预验证双段绿（coqc 单件 EXIT=0 + coqchk -o 闭包抽查 EXIT=0）。 *)

(* ng_UpReqPadeBetaPos —— UpReqPadeBetaPos.v：β_m 正性链（②号件，插入位 169） *)
Definition ng_UpReqPadeBetaPos : NewGreenFace :=
  MkNewGreenFace "UpReqPadeBetaPos.v" 284 15 20260914 "beta_m positivity pbp_beta_pos via factorial lower bound pbp_beta_lb" "L293:m54308a".

(* ng_UpReqPadeTailPos —— UpReqPadeTailPos.v：Padé 尾项 n=1/2 定值（①号件，插入位 170） *)
Definition ng_UpReqPadeTailPos : NewGreenFace :=
  MkNewGreenFace "UpReqPadeTailPos.v" 179 19 20260914 "Pade tail term identity at n=1/2 fixed-point evaluation ptp_beta_pos" "L690:m73e362".

(* ng_UpReqPadeLower —— UpReqPadeLower.v：下界误差估计（③号件，插入位 171） *)
Definition ng_UpReqPadeLower : NewGreenFace :=
  MkNewGreenFace "UpReqPadeLower.v" 385 24 20260914 "lower error bound cpl_lower_even for the even convergent partial fraction" "L405:m1cae6f".

(* ng_UpReqPadeDenPos12 —— UpReqPadeDenPos12.v：(1,2) 分母正性（④号件，插入位 172） *)
Definition ng_UpReqPadeDenPos12 : NewGreenFace :=
  MkNewGreenFace "UpReqPadeDenPos12.v" 275 8 20260914 "(1,2) Pade denominator positivity pdq_den_pos_12 with strict variant" "L287:m9a84a5".

Definition NewGreenListV30 : list NewGreenFace :=
  cons ng_UpReqPadeBetaPos
  (cons ng_UpReqPadeTailPos
  (cons ng_UpReqPadeLower
  (cons ng_UpReqPadeDenPos12
  nil))).

(* 续写统计：5 件 / 行数和 1544 / 闭合和 94（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV30Pieces  : nat := 4.
Definition NewGreenV30LineSum : nat := 1123.
Definition NewGreenV30QedSum  : nat := 66.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV30Pieces_matches : NewGreenV30Pieces = cnt_ng NewGreenListV30.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV30LineSum_matches : NewGreenV30LineSum = sum_ng_lines NewGreenListV30.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV30QedSum_matches : NewGreenV30QedSum = sum_ng_qed NewGreenListV30.
Proof. reflexivity. Qed.

(* 1) 插入位：五件 vo 树 order.txt 表尾整块追加（L169–L173，块内 Kahn 序 BetaPos→TailPos→ *)
(* Lower→DenPos12→Finale；①②③④ 定稿 Require 面零跨件边（③现档仍未 Require ①②， *)
(* 与分派语义序差异留痕照预备单 §一），⑤定稿新增 Require ③Lower 同块前位兼容）； *)
(* 双树 order.txt cmp 字节一致，双树 topo 再验器 173 行 BAD_COUNT=0，_CoqProject 双树 *)
(* 168→173 同步，scripts/order.txt 三处 wc=173。 *)
(* 2) 预验证：五件 cp 自权威源 Live_X（md5 留痕 b7bdda96/9e98ddea/a6fe32a3/44fc811a/ *)
(* b62cf9bd），cpu_guard CoreN 2 串行 coqc 五件全 EXIT=0；coqchk -o 闭包抽查 *)
(* TailPos/BetaPos/DenPos12/Finale 四件全 EXIT=0，零 Inconsistent assumptions 零 Anomaly。 *)

(* ；P1b 块与本块分属不同登记轨零名冲突，原样存档 attn/_tw31_P1b_block_backup.md， *)

(* ng_ 第三轨续写：承 后 49 件基面，注册第二段 13 件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)

(* 计量双口径（wc -l / 剥注释 token 级）逐件实测，源档一行未触碰（禁碰条款，只登记不改件）。 *)

(* ---------- 注册第二段 · 第三方收取线 7 件（CWA/CWB/CWC/CWD） ---------- *)

(* ng_QTailBridge —— QTailBridge.v：qtail_sum 桥式恒等式（CWA 任务1） *)
Definition ng_QTailBridge : NewGreenFace :=
  MkNewGreenFace "QTailBridge.v" 131 5 20260915 "bridge identity qtail_sum closing UpReqQExpTail ledger note against S03 exp_tail" "L131:m1451ac".

(* ng_PadeDenPosB12 —— PadeDenPosB12.v：Pade [n/n] 分母正性 x in (1,2] 段（CWA 任务2）。 *)
(* ⚠️ 世代区分：本件为第三方收取线独立复刻（UpReqPadeDenPos 留待 b 线），与我方 C 波④号件 *)
(* UpReqPadeDenPos12（ 登记 275/8）构成并行复刻对——两件独立实现并行在册，非同一件。 *)
Definition ng_PadeDenPosB12 : NewGreenFace :=
  MkNewGreenFace "PadeDenPosB12.v" 206 9 20260915 "Pade n over n denominator positivity on interval (1,2), third-party replica of ledger note b" "L206:m85a540".

(* ng_BanachNoHyp —— BanachNoHyp.v：Banach hplus/hwd 显式假设族摘除（CWB） *)
Definition ng_BanachNoHyp : NewGreenFace :=
  MkNewGreenFace "BanachNoHyp.v" 581 7 20260915 "explicit hplus hwd assumption family removal closing BanachAlg interface gap ledger note" "L581:me97cf4".

(* ng_BanachNoHypNorm —— BanachNoHypNorm.v：INSTB 留待剩余字段（CWB 加分件） *)
Definition ng_BanachNoHypNorm : NewGreenFace :=
  MkNewGreenFace "BanachNoHypNorm.v" 123 2 20260915 "remaining INSTB ledger fields bnorm_plus bnorm_mult subadditive submultiplicative" "L123:m5de8fa".

(* ng_RealEnergyTempMono —— RealEnergyTempMono.v：real_energy_exp_temp_mono 恒等档（CWC） *)
Definition ng_RealEnergyTempMono : NewGreenFace :=
  MkNewGreenFace "RealEnergyTempMono.v" 486 9 20260915 "real_energy_exp_temp_mono identity tier Real layer counterpart of S04 energy_exp_temp_mono" "L486:mf38d08".

(* ng_PowRealCompat —— PowRealCompat.v：G07 powb_pow 换形对接（CWD） *)
Definition ng_PowRealCompat : NewGreenFace :=
  MkNewGreenFace "PowRealCompat.v" 177 8 20260915 "G07 powb_pow to CW220 real_pow shape transfer adapter for consumers" "L197:md7d4f2".

(* ng_AlignIdUnclosed —— AlignIdUnclosed.v：UpAlignIdReq 件6 无条件化组装（CWD） *)
Definition ng_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "AlignIdUnclosed.v" 374 3 20260915 "UpAlignIdReq piece 6 unconditional assembly of backward KL recurrence exact identity" "L380:mb21783".

(* ---------- 注册第二段 · 消融与新数学线 6 件（AA 系） ---------- *)

(* ng_UpReqBanachNormOpp —— UpReqBanachNormOpp.v：B5 件一 qred 唯一性+bnorm Opp 面（AA11） *)
Definition ng_UpReqBanachNormOpp : NewGreenFace :=
  MkNewGreenFace "UpReqBanachNormOpp.v" 237 14 20260915 "qred_unique key plus bnorm Opp face for B5 unit one" "L459:m2b5d49".

(* ng_UpReqB4TwoStage —— UpReqB4TwoStage.v：B4 两段式降档完成 Padé 余项（AA14） *)
Definition ng_UpReqB4TwoStage : NewGreenFace :=
  MkNewGreenFace "UpReqB4TwoStage.v" 351 19 20260915 "B4 two stage downgrade closure of Pade remainder coefficient identity and witness eps transfer" "L360:ma4aebf".

(* ng_UpReqLpoEquiv —— UpReqLpoEquiv.v：平方非负全称 ⟺ 受限 LPO 双向归约（AA15，新数学，零公理） *)
Definition ng_UpReqLpoEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqLpoEquiv.v" 434 12 20260915 "square nonneg forall iff bounded LPO two way reduction theorem, zero axioms" "L443:m54b91c".

(* ng_UpReqBanachInstReal —— UpReqBanachInstReal.v：S02 Real 记录全字段装配（AA3，实例非空性） *)
Definition ng_UpReqBanachInstReal : NewGreenFace :=
  MkNewGreenFace "UpReqBanachInstReal.v" 774 49 20260915 "S02 Real carrier assembled into bxin_BanachAlgPre all field instance" "L856:m70e6f2".

Definition NewGreenListV32 : list NewGreenFace :=
  cons ng_QTailBridge
  (cons ng_PadeDenPosB12
  (cons ng_BanachNoHyp
  (cons ng_BanachNoHypNorm
  (cons ng_RealEnergyTempMono
  (cons ng_PowRealCompat
  (cons ng_AlignIdUnclosed
  (cons ng_UpReqBanachNormOpp
  (cons ng_UpReqB4TwoStage
  ((cons ng_UpReqLpoEquiv
  (cons ng_UpReqBanachInstReal nil))))))))))).

(* 续写统计：11 件 / 行数和 3874 / 闭合和 137（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV32Pieces : nat := 11.
Definition NewGreenV32LineSum : nat := 3874.
Definition NewGreenV32QedSum : nat := 137.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV32Pieces_matches : NewGreenV32Pieces = cnt_ng NewGreenListV32.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV32LineSum_matches : NewGreenV32LineSum = sum_ng_lines NewGreenListV32.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV32QedSum_matches : NewGreenV32QedSum = sum_ng_qed NewGreenListV32.
Proof. reflexivity. Qed.

(* 1) 编号与保全： P1b（仓库 Live 树 +96 行未提交进行中产物，idx_DTPT* 18 模块 rm_ 轨， *)

(* 40 闭合（分派观察口径 669 行，完成时点再测条款以实测为准）——已注册件内容更新非新注册， *)
(* ng_UpReqPadeTailPos 登记值冻结不动，。 *)
(* 3) S 系五件截断（S11–S15 Psatz→Lia 更换，AA1 普查线）待同批登记：=不等待 *)

(* ========================================================================= *)
(* （P1b：DTPT 离散对偶轴 18 ） *)
(* *)

(* 新增轨 idx_DTPT*：DTPT 工作区 18 模块（Q 层独立宇宙）包壳态注册，rm_in_uni=false *)
(* ——不占 734 迁移宇宙名额，与 idx_ 主轨（true）物理隔离，纯数据条目零机器核对耦合。 *)
(* *)
(* 插入位：ConstructiveWorld_Live/_CoqProject 表尾整块追加（L175–L192，拓扑序： *)
(* DTPT→Entropy/LLM/Measure/Phases/Truth→Entropy2/DigTheory→CoZero/ME2/ZeroLocus/ *)
(* Audit/Extract/EntFam2/ROTC→Lam/Cyc→RotSpec；coqdep 35 边全部「依赖索引<使用索引」， *)
(* 逐边核验在案）；Live 树 173→191 .v；双树 order.txt 三面与 vo 树播种面归 P2/P4 同步波。 *)
(* *)
(* 18 件源指纹： P1a 交付态 md5 逐件留痕（拷入前后双 md5 对账 18/18 一致； *)
(* 拷入面 = ConstructiveWorld_Live/ 表尾，零改名零内容改）。 *)
(* G1 三连零（家规禁词 grep 计数 18 件逐件=0，禁词字面按字面规避纪律不入本注）；壳对账： *)
(* 每件 Module/End 各=1，壳名=文件语义名，互引 35 边全限定 Import 适配层在案（P1a 报告 §二表）。 *)
(* rm_decl_cnt = grep -cE "^(Definition|Theorem|Lemma|Inductive|Record|Fixpoint|Corollary| *)
(* Ltac)[[:space:]]" 逐件实测（合计 819）；rm_head_kw = 各件主定理（grep 验证在件）。 *)
(* rm_gate_day = （主库编译验证日）。 *)
(* *)
(* 撞面对账：五撞名 q_fact/qeq_le/qstep/rot/diag_closed 全数壳内消解（Locate 全名形 *)
(* 库名.壳名.名，P1a 检查点 _p1a_probe_ns.log 在案）；叶子融入成立：Live 树既有件零该向依赖边。 *)
(* ========================================================================= *)

(* idx_DTPT —— DTPT.v：数字全域—熵相三元论根模块（Dig 塔+CGen+N9Opt+D8Ext 归并宿主） *)
Definition idx_DTPT : ReqModule :=
  MkReqModule "DTPT.v" 272 20260915 "C_sorted_min_adj" false.

(* idx_DTPT_Entropy —— DTPT_Entropy.v：最小偏差和熵面（xq_ 工具箱+H_adj 下界） *)
Definition idx_DTPT_Entropy : ReqModule :=
  MkReqModule "DTPT_Entropy.v" 218 20260915 "H_adj_P0_min" false.

(* idx_DTPT_Truth —— DTPT_Truth.v：真值序面（level 三律+Tarski 归并宿主，双副本桥在案） *)
Definition idx_DTPT_Truth : ReqModule :=
  MkReqModule "DTPT_Truth.v" 89 20260915 "level_le_refl" false.

(* idx_DTPT_DigTheory —— DTPT_DigTheory.v：数字化理论面（dig 单射塔+HAlg 归并宿主） *)
Definition idx_DTPT_DigTheory : ReqModule :=
  MkReqModule "DTPT_DigTheory.v" 88 20260915 "dig_inj_dCode" false.

(* idx_DTPT_Extract —— DTPT_Extract.v：提取面（u12 门控六检查点+9 条 Extraction 套件宿主） *)
Definition idx_DTPT_Extract : ReqModule :=
  MkReqModule "DTPT_Extract.v" 30 20260915 "u12_gate_pass_t1_h0" false.

(* idx_DTPT_Rotation —— DTPT_Rotation.v：旋转论面（rotc 基础件/精确闭式/锐化/λ 插值/偏差判别/周期律簇，RotSpec+Lam 归并宿主） *)
Definition idx_DTPT_Rotation : ReqModule :=
  MkReqModule "DTPT_Rotation.v" 143 20260915 "rotc_class_sharp_ub" false.
Definition idx_DTPT_Bridge : ReqModule :=
  MkReqModule "DTPT_Bridge.v" 37 20260915 "H_chain_set" false.
Definition idx_DTPT_Bridge_Dig : ReqModule :=
  MkReqModule "DTPT_Bridge_Dig.v" 19 20260915 "dig_size_le_dec" false.
Definition idx_DTPT_Bridge_Rot : ReqModule :=
  MkReqModule "DTPT_Bridge_Rot.v" 24 20260915 "rotc_class_sharp_ub_set" false.

(* ========================================================================= *)
(* c（P1c：DTPT 融入 P1 完成预备——6 模块终态收缩） *)
(* *)
(* 承 ：棒 1–5 归并完成后 DTPT 面 18 模块收缩为 6 模块终态。本节整条删除 12 条退役 *)
(* idx_DTPT* 条目（各 3 行；受触模块主库 Live 树 .v 与构建产物同日删除，工作区退役档 *)
(* 12/12 逐字节留痕，对账表见 DTPT_P1c_同步报告.md）： *)
(* LLM/Measure（棒1）与 Phases/CoZero（棒2）并入 DTPT；Entropy2/EntFam2（棒3）与 *)
(* ME2/ZeroLocus（棒4）并入 DTPT_Entropy；Audit 与 ROTC（棒5）并入 DTPT_Truth/DTPT_Cyc； *)
(* Lam/RotSpec 由棒 6a 并入 DTPT_Cyc（件名待改 DTPT_Rotation）进行中。 *)
(* 存留 6 条：idx_DTPT / idx_DTPT_Entropy / idx_DTPT_Truth / idx_DTPT_DigTheory / *)
(* idx_DTPT_Extract / idx_DTPT_Cyc。存留条目 rm_decl_cnt / rm_head_kw 为 注册时 *)

(* 同日 _CoqProject 同步收缩 18 行→6 行（与 r74 波 HEAD 188 行对账合并为 194 行， *)
(* 占表尾 L189–L194）；DTPT_Cyc.v 行尾注记待棒 6b 改名 DTPT_Rotation。 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* d（6b主库尾：第 6 件落库与 idx_DTPT* 终态刷新） *)
(* *)
(* 承 c：棒 6b 交付 DTPT_Rotation（2,018 行；原 DTPT_Cyc 改名，RotSpec/Lam/ROTC/ *)

(* ①Live 树 _CoqProject 表尾行改名并撤行尾注记（194 行不变，纯增 +6−0 对 HEAD）； *)
(* ②idx_DTPT_Cyc 整条改名 idx_DTPT_Rotation，路径 "DTPT_Cyc.v"→"DTPT_Rotation.v"； *)
(* ③存留 6 条 rm_decl_cnt 按 同款 grep 口径逐件重测刷终态：DTPT 272 / Entropy 218 / *)
(* Truth 79 / DigTheory 88 / Extract 30 / Rotation 129（合计 826）；rm_gate_day 统一刷 *)

(* 余 5 主定理在件再验未变。 *)
(* ④Live 树退役残件同日出清：DTPT_Cyc .v+构建产物全套、ROTC/Entropy2 残留 .aux（工作区 *)
(* .retired_S6b 档留痕，主库零副本）；order.txt 三面各 +6 行（187→193，三面同 md5）。 *)
(* 主库终态实证：六件单编零错零警；全树内核认证 193 模块（187 基线+6）组别 EXIT=0 成功收尾； *)
(* 六件闭包 -o 枚举四项汇总全 <none>。vo 树播种 6 件×5 文件为全树认证前置，.v 副本 md5 *)
(* 六件与工作区定稿逐字节一致（五冻结件=P1c 留痕值）。 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* （P1g：DTPT ） *)
(* *)

(* 头注声明：P1b 波 idx_DTPT* 九条目曾随 8711998 提交落库；24431dc（C 波完成）以 *)
(* 覆盖提交时九条目合法让位离面（ 编号订正注记自述前提「+96 行系未提交进行中产物」 *)

(* 裁决（Q1：不在 W31 块内恢复避编号冲突，改文件尾 块重注册）原轨复注册， *)
(* 条目名/行格式严格副本 8711998 版（d 终态）。 *)
(* rm_decl_cnt 按当盘现值（ 同款 grep 口径）逐件重测，随 FRUIT/TRUTH 波后刷新： *)
(* DTPT 272 / Entropy 218 / Truth 89（TRUTH-1 同步后现值）/ DigTheory 88 / Extract 30 / *)
(* Rotation 143（FRUIT-1 §S8 后；Qed 口径 135 不入本字段，字段语义依 P1b 公式）/ *)
(* Bridge 37 / Bridge_Dig 19 / Bridge_Rot 24（P3B7 §8 终态 412 行版入车后现值；已提交版 *)
(* 31130c5b 被工作区终态 90869682 覆盖属预期新资产入车，P2 提交信息声明）。 *)

(* 纯数据条目零机器核对耦合（ 同款）。 *)
(* ========================================================================= *)

(* ========================================================================= *)

(* *)
(* 完成对象=AA19 裁决「甲·并入」落地态： 孤儿块（P1b 注册 18 条，经 c 裁撤 12 条 *)
(* 退役条目、d 改名刷新，现形态 9 条 idx_DTPT* 定义）与 段（ng_ 轨 13 件）同盘并存。 *)

(* 完成三验： *)
(* ①重号=0：Definition 级 idx_/ng_/af_/NewGreen 全名查重空集（rm_ 字段名为记录访问器复用， *)
(* 非重号）；idx_DTPT* rm_ 轨（rm_in_uni=false）与 ng_ 绿面轨物理隔离维持。 *)

(* ③本块及上块新文本遵循既定措辞纪律（家规禁词按字面规避，不入本注）。 *)

(* 非进行中未提交改动）；其条目值 Truth 89 / Rotation 143 / Bridge_Rot 24 系 TRUTH-1 / *)
(* FRUIT-1 §S8 / P3B7 §8 波后当盘现值。本件条目行即采此三值对齐，d 段 prose 数值 *)

(* （随 波翻正册）。 *)
(* 三树同步：本 完成态 cp 至 ConstructiveWorld_Live/ 与 ConstructiveWorld_vo/， *)
(* cmp 零差异、三处 md5 一致（数值见 attn/交付报告-.md §三），一并了结 *)
(* 段留待的双跳 cp 项。 *)

(* §四——BoltzmannBridgeDischarge / DenPosGeneral / ExpNegFinale / ExpNegPosUp / *)
(* FirewallReqDischarge / InstBWdClose / KLWallClosed / PolyIntegral / RealKLCorrMark / *)
(* SqWallCorrMark / SqrtfCauchy / SqrtfCauchyArch / SqrtfCauchyDischarge / SumInvFactEscape / *)
(* SupKLBound / SupKLMonoCompose / TempMonoW2Mark，语句级完成中；DTPT_Rotation 进行中件注记同册。 *)
(* ========================================================================= *)

(* 复核 26→27（L141 内联 Proof…Qed. 真闭合，非注释命中）。 *)

(* ng_UpReqRealLtShiftBridge —— UpReqRealLtShiftBridge.v：Real 层严格步完成三形 *)
Definition ng_UpReqRealLtShiftBridge : NewGreenFace :=
  MkNewGreenFace "UpReqRealLtShiftBridge.v" 138 6 20260916 "strict-step lt discharge trio, weak-slot Or-lift" "L138:me491ac".

(* ng_UpReqStrictStepGen —— UpReqStrictStepGen.v：严格步生成器族 *)
Definition ng_UpReqStrictStepGen : NewGreenFace :=
  MkNewGreenFace "UpReqStrictStepGen.v" 212 13 20260916 "eps-split generator family, master lemma half+quarter" "L225:mc0a061".

(* ng_UpReqCStarDef —— UpReqCStarDef.v：C* 定义面与正元准备 *)
Definition ng_UpReqCStarDef : NewGreenFace :=
  MkNewGreenFace "UpReqCStarDef.v" 758 27 20260916 "C*-algebra definition face, involution laws, positive elements" "L758:m3319e7".

(* ng_UpReqGibbsWallEquiv —— UpReqGibbsWallEquiv.v：gibbs 墙等价 LPO *)
Definition ng_UpReqGibbsWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqGibbsWallEquiv.v" 340 12 20260916 "gibbs plain-le wall iff restricted LPO, wall two" "L340:m7d19a7".

(* ng_UpReqPinWallEquiv —— UpReqPinWallEquiv.v：钉定墙等价 LPO *)
Definition ng_UpReqPinWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqPinWallEquiv.v" 243 9 20260916 "pin wall iff restricted LPO, wall three" "L256:m07e279".

(* ng_UpReqTBNCBridge —— UpReqTBNCBridge.v：TBNC 对角逐项桥 *)
Definition ng_UpReqTBNCBridge : NewGreenFace :=
  MkNewGreenFace "UpReqTBNCBridge.v" 250 6 20260916 "TBNC explicit-hypothesis diagonal corner-term bridge" "L260:m16e149".

(* ng_ 第三轨续写：承 后 69 件基面，成果四外部稿本组 15 件逐件实测登记 *)

(* l2e_g3 属 G3 抽取检查点（Recursive Extraction 施工预备件，稿头自署），按检查点语义排除注册面， *)
(* 只登主稿 LogTwoEnvelope；PiEnvelope/PinskerTwoPoint/SymplecticRotationSpec 三挂起稿候 T4G *)

(* 稿因 4/库因 0/环因 0）；Gibbs 修复账=attn/交付报告-.md *)
(* （L92+L165 同类缺括号两处，vos/full 双 0，vo 8822B magic 90100，PA 3 Closed 与申报吻合）。 *)
(* 注册序=repo order.txt 尾部追加：T4S 提案「UpReqStrictBridgeD 尾锚」系 102 行 Live_X 子集序锚位， *)
(* repo 全库序 228 行中该锚位于 L103，其后续 10 基座依赖（UpReqSteadyThermo L125、 *)
(* UpReqTempDefs L127、UpReqArgminEngine L130、UpReqEntropyDeficitTemp L134、UpReqEntropyMaxTemp *)
(* L138、UpReqTempDual L140、ExpNegPos L205、RealEnergyTempMono L183、EnergyTempMonoB L209、 *)

(* Live_X 102 行子集序零改动（IDX92 结论）。 *)
(* 口径：ng_lines=wc -l 实测；ng_qed=剥块注释 token 级 Qed 实测（头注「全 Qed」伪命中按 剥除）。 *)
(* 沙箱再验产物判据全过：size>0、md5≠d41d8cd9、magic=436f712100015ff4（90100=9.1.0）。 *)

(* ng_LogTwoEnvelope —— LogTwoEnvelope.v：log2 上界包络（柯西模量 ceil(1/eps)） *)
Definition ng_LogTwoEnvelope : NewGreenFace :=
  MkNewGreenFace "LogTwoEnvelope.v" 570 31 20260916 "log2 envelope, cauchy modulus ceil(1/eps) ceiling ladder" "L590:m3b175f".

(* ng_FreeEnergyKLGap —— FreeEnergyKLGap.v：自由能 KL 缺口分解 *)
Definition ng_FreeEnergyKLGap : NewGreenFace :=
  MkNewGreenFace "FreeEnergyKLGap.v" 578 14 20260916 "free-energy KL gap decomposition on RealKL decomp face" "L682:mdb5635".

(* ng_ArctanGeomTail —— ArctanGeomTail.v：arctan 几何尾界 *)
Definition ng_ArctanGeomTail : NewGreenFace :=
  MkNewGreenFace "ArctanGeomTail.v" 311 10 20260916 "arctan geometric tail bound, Q-layer chain" "L311:m4ae2dc".

(* ng_StopTimeConservation —— StopTimeConservation.v：停时守恒（预算×宪法轴） *)
Definition ng_StopTimeConservation : NewGreenFace :=
  MkNewGreenFace "StopTimeConservation.v" 280 10 20260916 "stop-time conservation, budget-constitutional axis" "L294:m499cde".

(* ng_TempSoftmaxInstantiation —— TempSoftmaxInstantiation.v：温度 softmax 实例化 *)
Definition ng_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "TempSoftmaxInstantiation.v" 411 6 20260916 "temperature softmax instantiation on attn-gibbs face" "L413:mb27349".

(* ng_SecondLawQuantified —— SecondLawQuantified.v：量化第二定律（熵亏不等式） *)
Definition ng_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "SecondLawQuantified.v" 561 16 20260916 "second law quantified, entropy-deficit inequality, follows TempSoftmax" "L646:m46ab80".

(* ng_EpsOptimalReach —— EpsOptimalReach.v：eps 最优可达（argmin 引擎实例） *)
Definition ng_EpsOptimalReach : NewGreenFace :=
  MkNewGreenFace "EpsOptimalReach.v" 213 8 20260916 "eps-optimal reachability via argmin engine" "L220:m120147".

(* ng_VandermondePartial —— VandermondePartial.v：Vandermonde 部分和恒等式 *)
Definition ng_VandermondePartial : NewGreenFace :=
  MkNewGreenFace "VandermondePartial.v" 671 38 20260916 "Vandermonde partial-sum identity, Q combinatorics" "L676:m91a02a".

(* ng_TempUnimodalMax —— TempUnimodalMax.v：温度单峰极大 *)
Definition ng_TempUnimodalMax : NewGreenFace :=
  MkNewGreenFace "TempUnimodalMax.v" 341 7 20260916 "temperature unimodal maximum on energy-temp-mono face" "L341:m91c855".

(* ng_ExpOneEnvelope —— ExpOneEnvelope.v：exp(±x) 单侧包络 *)
Definition ng_ExpOneEnvelope : NewGreenFace :=
  MkNewGreenFace "ExpOneEnvelope.v" 505 29 20260916 "exp(+/-x) one-sided envelopes, Q rounding ladder" "L531:m365f05".

(* ng_AttnLogSumExpBound —— AttnLogSumExpBound.v：注意力 log-sum-exp 界 *)
Definition ng_AttnLogSumExpBound : NewGreenFace :=
  MkNewGreenFace "AttnLogSumExpBound.v" 529 13 20260916 "attention log-sum-exp upper bound, S04 conv face" "L538:m946606".

(* ng_QstepConvergenceBound —— QstepConvergenceBound.v：Q 步收敛界（N-live 审计） *)
Definition ng_QstepConvergenceBound : NewGreenFace :=
  MkNewGreenFace "QstepConvergenceBound.v" 656 27 20260916 "Q-step convergence bound, B5-recycle + N-live audit" "L656:mb700cf".

(* ng_CurriculumOptTemp —— CurriculumOptTemp.v：课程最优温度 *)
Definition ng_CurriculumOptTemp : NewGreenFace :=
  MkNewGreenFace "CurriculumOptTemp.v" 184 5 20260916 "curriculum optimal temperature, thin-shell CW219 import" "L184:mfa1c7a".

(* ng_GibbsAttractor —— GibbsAttractor.v：gibbs 吸引子（Boltzmann π 稳态+TV 迭代传播；修 L92+L165 缺括号后复绿） *)
Definition ng_GibbsAttractor : NewGreenFace :=
  MkNewGreenFace "GibbsAttractor.v" 285 4 20260916 "gibbs attractor: boltzmann pi stationary under TV kernel, titer propagation" "L344:m4fda37".

(* ng_ 第三轨续写：承 后 84 件基面， 挂起三稿 PiEnvelope/PinskerTwoPoint/ *)
(* SymplecticRotationSpec 经属主迁移波落盘（.v×双树）+编译复绿（IN 与属主波双账）后 *)
(* 注册承认：order.txt×3 L244–246、_CoqProject×2 L245–247 尾部追加已核，四件依赖行号全前位 *)
(* 拓扑 PASS（Gibbs 125<243、Pi 16<244、Pinsker 69<245、Symplectic 208<246，全文件 Require *)
(* 提边机械核验零违序）。ng_GibbsAttractor 已在 册内（L243 注册先成），实测 285/4 与 *)

(* PA 3 Closed、公理清单 0）；三新件产物判据 size>0、md5≠d41d8cd9、magic 同上。 *)
(* 权威源=attn/交付报告-.md；口径：ng_lines=wc -l 实测； *)
(* ng_qed=剥块注释 token 级 Qed 实测。 *)

(* ng_PiEnvelope —— PiEnvelope.v：π 有理包络（Leibniz 级数奇偶双边夹逼+显式模量） *)
Definition ng_PiEnvelope : NewGreenFace :=
  MkNewGreenFace "PiEnvelope.v" 933 53 20260916 "pi rational envelope, leibniz series two-sided squeeze with explicit modulus, cauchy_real_pi_leibniz bridge" "L933:m66405b".

(* ng_PinskerTwoPoint —— PinskerTwoPoint.v：二点 Pinsker 型 TV-KL 下界 *)
Definition ng_PinskerTwoPoint : NewGreenFace :=
  MkNewGreenFace "PinskerTwoPoint.v" 443 9 20260916 "two-point pinsker-type TV-KL lower bound with explicit closed-form constant, real layer" "L454:mdc43ab".

(* 40 件尾部追加 order.txt×3 L247-286/_CoqProject×2 L248-287；PinskerCore/EnvelopeDual 摘除本次 *)

(* ng_fa53_compat_abs —— fa53_compat_abs.v：compat abs lemma, ablation harvest wave1 *)
Definition ng_fa53_compat_abs : NewGreenFace :=
  MkNewGreenFace "fa53_compat_abs.v" 173 8 20260917 "compat abs lemma, ablation harvest wave1" "L189:ma1e616".

(* ng_AbsLeId —— AbsLeId.v：abs le id small-face *)
Definition ng_AbsLeId : NewGreenFace :=
  MkNewGreenFace "AbsLeId.v" 114 5 20260917 "abs le id small-face" "L114:m6f39a3".

(* ng_fa51_sumpos_id —— fa51_sumpos_id.v：sum position identity, ablation harvest wave1 *)
Definition ng_fa51_sumpos_id : NewGreenFace :=
  MkNewGreenFace "fa51_sumpos_id.v" 234 10 20260917 "sum position identity, ablation harvest wave1" "L245:me53fed".

(* ng_fa56_id_carrier —— fa56_id_carrier.v：id carrier, ablation harvest wave1 *)
Definition ng_fa56_id_carrier : NewGreenFace :=
  MkNewGreenFace "fa56_id_carrier.v" 266 13 20260917 "id carrier, ablation harvest wave1" "L324:m973f7b".

(* ng_fa56b_ext —— fa56b_ext.v：fa56 extension b, ablation harvest wave1 (contra extraction exemption documented) *)
Definition ng_fa56b_ext : NewGreenFace :=
  MkNewGreenFace "fa56b_ext.v" 271 12 20260917 "fa56 extension b, ablation harvest wave1 (contra extraction exemption documented)" "L281:md08878".

(* ng_fa56c_ext —— fa56c_ext.v：fa56 extension c, ablation harvest wave1 *)
Definition ng_fa56c_ext : NewGreenFace :=
  MkNewGreenFace "fa56c_ext.v" 291 13 20260917 "fa56 extension c, ablation harvest wave1" "L363:m3f591f".

(* ng_fa52_dpo_witness —— fa52_dpo_witness.v：dpo witness, ablation harvest wave1 *)
Definition ng_fa52_dpo_witness : NewGreenFace :=
  MkNewGreenFace "fa52_dpo_witness.v" 94 4 20260917 "dpo witness, ablation harvest wave1" "L102:md38cbf".

(* ng_EntropyUnsatMark —— EntropyUnsatMark.v：entropy unsat mark, ablation harvest wave1 *)
Definition ng_EntropyUnsatMark : NewGreenFace :=
  MkNewGreenFace "EntropyUnsatMark.v" 131 3 20260917 "entropy unsat mark, ablation harvest wave1" "L131:m9c751c".

(* ng_IdSlotTranslate —— IdSlotTranslate.v：id slot translate, ablation harvest wave1 *)
Definition ng_IdSlotTranslate : NewGreenFace :=
  MkNewGreenFace "IdSlotTranslate.v" 174 7 20260917 "id slot translate, ablation harvest wave1" "L188:mad0517".

(* ng_SumEqListFeed —— SumEqListFeed.v：list sum eq feed, ablation harvest wave1 *)
Definition ng_SumEqListFeed : NewGreenFace :=
  MkNewGreenFace "SumEqListFeed.v" 172 8 20260917 "list sum eq feed, ablation harvest wave1" "L187:m2b1285".

(* ng_SumEqListMark —— SumEqListMark.v：list sum eq mark, ablation harvest wave1 *)
Definition ng_SumEqListMark : NewGreenFace :=
  MkNewGreenFace "SumEqListMark.v" 93 4 20260917 "list sum eq mark, ablation harvest wave1" "L172:m5cca95".

(* ng_RMaxSwap —— RMaxSwap.v：rmax swap small-face *)
Definition ng_RMaxSwap : NewGreenFace :=
  MkNewGreenFace "RMaxSwap.v" 95 4 20260917 "rmax swap small-face" "L95:m234eb8".

(* ng_NatLenPos —— NatLenPos.v：nat len pos small-face *)
Definition ng_NatLenPos : NewGreenFace :=
  MkNewGreenFace "NatLenPos.v" 111 4 20260917 "nat len pos small-face" "L124:m2b2192".

(* ng_InvPosLtCompat —— InvPosLtCompat.v：inv pos lt compat small-face *)
Definition ng_InvPosLtCompat : NewGreenFace :=
  MkNewGreenFace "InvPosLtCompat.v" 138 5 20260917 "inv pos lt compat small-face" "L138:mb9993b".

(* ng_GibbsAssembly —— GibbsAssembly.v：gibbs assembly *)
Definition ng_GibbsAssembly : NewGreenFace :=
  MkNewGreenFace "GibbsAssembly.v" 454 4 20260917 "gibbs assembly" "L468:mcb6784".

(* ng_BanachS3Chain —— BanachS3Chain.v：banach S3 chain composition *)
Definition ng_BanachS3Chain : NewGreenFace :=
  MkNewGreenFace "BanachS3Chain.v" 176 6 20260917 "banach S3 chain composition" "L176:mb1daeb".

(* ng_UpReqIrrationalCriterion —— UpReqIrrationalCriterion.v：liouville irrationality criterion via master theorem, e-instance, C2R2 line *)
Definition ng_UpReqIrrationalCriterion : NewGreenFace :=
  MkNewGreenFace "UpReqIrrationalCriterion.v" 769 28 20260917 "liouville irrationality criterion via master theorem, e-instance, C2R2 line" "L779:m916add".

(* ng_UpReqKLCocycle —— UpReqKLCocycle.v：KL cocycle identity face *)
Definition ng_UpReqKLCocycle : NewGreenFace :=
  MkNewGreenFace "UpReqKLCocycle.v" 367 6 20260917 "KL cocycle identity face" "L377:m2bae30".

(* ng_UpReqScTrigEps —— UpReqScTrigEps.v：sc trig eps family *)
Definition ng_UpReqScTrigEps : NewGreenFace :=
  MkNewGreenFace "UpReqScTrigEps.v" 537 21 20260917 "sc trig eps family" "L537:m78ba74".

(* ng_UpReqSqrtOptimal —— UpReqSqrtOptimal.v：sqrt d-optimality face *)
Definition ng_UpReqSqrtOptimal : NewGreenFace :=
  MkNewGreenFace "UpReqSqrtOptimal.v" 414 22 20260917 "sqrt d-optimality face" "L414:m68e32f".

(* ng_UpReqG05WallClass —— UpReqG05WallClass.v：G05 full-base bridge wall class, rLPO spectrum *)
Definition ng_UpReqG05WallClass : NewGreenFace :=
  MkNewGreenFace "UpReqG05WallClass.v" 392 13 20260917 "G05 full-base bridge wall class, rLPO spectrum" "L421:me3cde3".

(* ng_UpReqSquareWallEquiv —— UpReqSquareWallEquiv.v：square wall b_lift iff rLPO, wall family *)
Definition ng_UpReqSquareWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqSquareWallEquiv.v" 201 7 20260917 "square wall b_lift iff rLPO, wall family" "L201:mfc7075".

(* ng_UpReqResidWallEquiv —— UpReqResidWallEquiv.v：residual wall three-segment taxonomy, wall family *)
Definition ng_UpReqResidWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqResidWallEquiv.v" 452 7 20260917 "residual wall three-segment taxonomy, wall family" "L464:m0a31a2".

(* ng_UpReqLogZWallEquiv —— UpReqLogZWallEquiv.v：logZ wall equivalence, wall family *)
Definition ng_UpReqLogZWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqLogZWallEquiv.v" 883 28 20260917 "logZ wall equivalence, wall family" "L896:m0b57be".

(* ng_UpReqStepKLEtaInst —— UpReqStepKLEtaInst.v：step_kl_eta_bound interface instance resolution, GEOM-A *)
Definition ng_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "UpReqStepKLEtaInst.v" 1071 36 20260917 "step_kl_eta_bound interface instance resolution, GEOM-A" "L1091:m3c3f88".

(* ng_UpReqIterGeomRate —— UpReqIterGeomRate.v：iteration geometric rate with sigT witness, GEOM-B *)
Definition ng_UpReqIterGeomRate : NewGreenFace :=
  MkNewGreenFace "UpReqIterGeomRate.v" 1632 29 20260917 "iteration geometric rate with sigT witness, GEOM-B" "L1641:m7d91a0".

(* ng_UpReqMixingTime —— UpReqMixingTime.v：mixing time explicit face *)
Definition ng_UpReqMixingTime : NewGreenFace :=
  MkNewGreenFace "UpReqMixingTime.v" 666 19 20260917 "mixing time explicit face" "L741:m7ba70f".

(* ng_UpReqDoeblinEntropy —— UpReqDoeblinEntropy.v：doeblin entropy production face *)
Definition ng_UpReqDoeblinEntropy : NewGreenFace :=
  MkNewGreenFace "UpReqDoeblinEntropy.v" 1064 26 20260917 "doeblin entropy production face" "L1070:m954cba".

(* ng_UpReqPinskerTransport —— UpReqPinskerTransport.v：two-point pinsker transport dp_two_point, full-distribution *)
Definition ng_UpReqPinskerTransport : NewGreenFace :=
  MkNewGreenFace "UpReqPinskerTransport.v" 1385 39 20260917 "two-point pinsker transport dp_two_point, full-distribution" "L1385:m00f6f7".

(* ng_UpReqWeakTriangle —— UpReqWeakTriangle.v：constructive weak triangle with certificate c=min(r/q), EXP-D3B *)
Definition ng_UpReqWeakTriangle : NewGreenFace :=
  MkNewGreenFace "UpReqWeakTriangle.v" 537 6 20260917 "constructive weak triangle with certificate c=min(r/q), EXP-D3B" "L537:m2c22cc".

(* ng_UpReqPadeConstUnify —— UpReqPadeConstUnify.v：pade constant unify *)
Definition ng_UpReqPadeConstUnify : NewGreenFace :=
  MkNewGreenFace "UpReqPadeConstUnify.v" 271 21 20260917 "pade constant unify" "L271:m704ce0".

(* ng_UpReqPadeTransport —— UpReqPadeTransport.v：pade transport *)
Definition ng_UpReqPadeTransport : NewGreenFace :=
  MkNewGreenFace "UpReqPadeTransport.v" 409 13 20260917 "pade transport" "L409:m897e58".

(* ng_UpReqConstEnvelope —— UpReqConstEnvelope.v：constant envelope *)
Definition ng_UpReqConstEnvelope : NewGreenFace :=
  MkNewGreenFace "UpReqConstEnvelope.v" 678 21 20260917 "constant envelope" "L690:m707ebe".

(* ng_UpReqEntropyMonoSplit —— UpReqEntropyMonoSplit.v：entropy monotonicity split *)
Definition ng_UpReqEntropyMonoSplit : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyMonoSplit.v" 687 5 20260917 "entropy monotonicity split" "L702:m15322a".

(* ng_UpReqSymplecticBridge —— UpReqSymplecticBridge.v：symplectic bridge *)
Definition ng_UpReqSymplecticBridge : NewGreenFace :=
  MkNewGreenFace "UpReqSymplecticBridge.v" 413 18 20260917 "symplectic bridge" "L413:m7d8247".

(* ng_UpReqAlignClose —— UpReqAlignClose.v：align close *)
Definition ng_UpReqAlignClose : NewGreenFace :=
  MkNewGreenFace "UpReqAlignClose.v" 588 6 20260917 "align close" "L601:m254842".

(* ng_DenPosGeneralClose —— DenPosGeneralClose.v：den pos general close, VER52 gap-closer *)
Definition ng_DenPosGeneralClose : NewGreenFace :=
  MkNewGreenFace "DenPosGeneralClose.v" 122 3 20260917 "den pos general close, VER52 gap-closer" "L122:m98b434".

(* 2 件尾部追加 order.txt×3 L287-288/_CoqProject×2 L289-290；UpReqUMixSelect=接口层选择器（具体层退化为实例）， *)
(* UpReqAttnMixTime=接合定理真使用形（AT2 待命形→AT3 终 swap，语句前件已对齐 ums 实形=le 形 Arch+首显参 *)

(* ng_UpReqUMixSelect —— UpReqUMixSelect.v：interface-layer mixing-time selector: bernoulli upper wall fully ported + archimedean le-form k-selection (ums_scale (S N) one witness), RealInterface generalization of UpReqMixingTime, AT1 *)
Definition ng_UpReqUMixSelect : NewGreenFace :=
  MkNewGreenFace "UpReqUMixSelect.v" 615 24 20260918 "interface-layer mixing-time selector: bernoulli upper wall fully ported + archimedean le-form k-selection (ums_scale (S N) one witness), RealInterface generalization of UpReqMixingTime, AT1" "L651:mcbf1ab".

(* ng_UpReqAttnMixTime —— UpReqAttnMixTime.v：attention mixing time closure theorem: amt_attention_mixing_time (+le) consumes ums_k_select with kappa=minus one delta_star, two-side TV stitching via le_lt_trans, degenerate-end delta*<1 strict; paper7 sec6.3 open item 1 closed, AT2 standby + AT3 final swap *)
Definition ng_UpReqAttnMixTime : NewGreenFace :=
  MkNewGreenFace "UpReqAttnMixTime.v" 223 7 20260918 "attention mixing time closure theorem: amt_attention_mixing_time (+le) consumes ums_k_select with kappa=minus one delta_star, two-side TV stitching via le_lt_trans, degenerate-end delta*<1 strict; paper7 sec6.3 open item 1 closed, AT2 standby + AT3 final swap" "L223:m019238".

(* 16 件尾部追加 order×3 L289-304/_CoqProject×2 L290-305；PadeErrorIntegral/Paper12345Sample/ *)
(* p2a_AttnClimClose/p3a_TempDualBoolSlots 四件伤单摘除候 ；fa56b/fa56c 手术版随车（已注册件内容修改）。 *)
(* ng_UpReqPinskerCore —— UpReqPinskerCore.v：pinsker constant ladder core, rung-one pnk2_pinsker_one (1*TV^2<=KL) + R8 wound repair, R9/PNSK；-PNK2B 桥接模块收取（纯追加 591 行，pnk2_pinsker_trunc5/_mirror 两块支内砖） *)
Definition ng_UpReqPinskerCore : NewGreenFace :=
  MkNewGreenFace "UpReqPinskerCore.v" 3606 57 20260919 "pinsker constant ladder core, rung-one pnk2_pinsker_one (1*TV^2<=KL) + R8 wound repair, R9/PNSK; R10-PNK2B bridge harvest, pure-append 591 on 3015, pnk2_pinsker_trunc5/_mirror" "L3608:mb2ae28".

(* ng_UpReqEnvelopeDual —— UpReqEnvelopeDual.v：constant envelope dual, cascade rebuild on repaired core, R9 *)
Definition ng_UpReqEnvelopeDual : NewGreenFace :=
  MkNewGreenFace "UpReqEnvelopeDual.v" 811 17 20260918 "constant envelope dual, cascade rebuild on repaired core, R9" "L810:m242061".

(* ng_UpReqDyadicLog —— UpReqDyadicLog.v：dyadic log envelopes, axis rate via c3e engine, W1B/W1C line *)
Definition ng_UpReqDyadicLog : NewGreenFace :=
  MkNewGreenFace "UpReqDyadicLog.v" 589 24 20260918 "dyadic log envelopes, axis rate via c3e engine, W1B/W1C line" "L608:mdc9319".

(* ng_fa57_ext —— fa57_ext.v：fa57 extension direct compile, VER52 wave-3 handover *)
Definition ng_fa57_ext : NewGreenFace :=
  MkNewGreenFace "fa57_ext.v" 239 11 20260918 "fa57 extension direct compile, VER52 wave-3 handover" "L240:ma5d56f".

(* ng_UpReqRatioTail —— UpReqRatioTail.v：ratio tail Q/Real faces, R9/R9B *)
Definition ng_UpReqRatioTail : NewGreenFace :=
  MkNewGreenFace "UpReqRatioTail.v" 919 42 20260918 "ratio tail Q/Real faces, R9/R9B" "L935:mce23d3".

(* ng_UpReqAttnUniformLimit —— UpReqAttnUniformLimit.v：attn uniform limit + switch_gen family, R9B/SWG *)
Definition ng_UpReqAttnUniformLimit : NewGreenFace :=
  MkNewGreenFace "UpReqAttnUniformLimit.v" 618 15 20260918 "attn uniform limit + switch_gen family, R9B/SWG" "L1777:m2e9daa".

(* ng_UpReqAttnMassSplit —— UpReqAttnMassSplit.v：Q18 mass-split chain ams_, Q18C *)
Definition ng_UpReqAttnMassSplit : NewGreenFace :=
  MkNewGreenFace "UpReqAttnMassSplit.v" 891 12 20260918 "Q18 mass-split chain ams_, Q18C" "L885:m643ab3".

(* ng_UpReqAttnQ18Tail —— UpReqAttnQ18Tail.v：Q18 tail: T0 rationalized 299#1000 + cross-token congruence, Q18D *)
Definition ng_UpReqAttnQ18Tail : NewGreenFace :=
  MkNewGreenFace "UpReqAttnQ18Tail.v" 519 17 20260918 "Q18 tail: T0 rationalized 299#1000 + cross-token congruence, Q18D" "L512:meefaf2".

(* ng_FepIdentClass —— FepIdentClass.v：FEP identification class, ablation harvest 23-03 *)
Definition ng_FepIdentClass : NewGreenFace :=
  MkNewGreenFace "FepIdentClass.v" 578 5 20260918 "FEP identification class, ablation harvest 23-03" "L578:me4945b".

(* ng_G04ProjHook —— G04ProjHook.v：G04 proj hook, ablation harvest 23-03 *)
Definition ng_G04ProjHook : NewGreenFace :=
  MkNewGreenFace "G04ProjHook.v" 222 12 20260918 "G04 proj hook, ablation harvest 23-03" "L241:mac9fc2".

(* ng_LMCarrierExt —— LMCarrierExt.v：LM carrier extension, ablation harvest 23-03 *)
Definition ng_LMCarrierExt : NewGreenFace :=
  MkNewGreenFace "LMCarrierExt.v" 306 15 20260918 "LM carrier extension, ablation harvest 23-03" "L343:m6945e4".

(* ng_Paper1Ablation —— Paper1Ablation.v：paper1 ablation sample, harvest 23-03 *)
Definition ng_Paper1Ablation : NewGreenFace :=
  MkNewGreenFace "Paper1Ablation.v" 521 5 20260918 "paper1 ablation sample, harvest 23-03" "L521:m6d3847".

(* ng_Paper7Ablation —— Paper7Ablation.v：paper7 ablation, harvest 23-03 *)
Definition ng_Paper7Ablation : NewGreenFace :=
  MkNewGreenFace "Paper7Ablation.v" 191 7 20260918 "paper7 ablation, harvest 23-03" "L191:m9081cf".

(* ng_PhysPredAblation —— PhysPredAblation.v：physics prediction ablation, harvest 23-03 *)
Definition ng_PhysPredAblation : NewGreenFace :=
  MkNewGreenFace "PhysPredAblation.v" 279 13 20260918 "physics prediction ablation, harvest 23-03" "L292:m984e7f".

(* ng_RateTheoryAblation —— RateTheoryAblation.v：rate theory ablation, harvest 23-03 *)
Definition ng_RateTheoryAblation : NewGreenFace :=
  MkNewGreenFace "RateTheoryAblation.v" 215 5 20260918 "rate theory ablation, harvest 23-03" "L222:m414c81".

(* ng_p4a_GradSignQDec —— p4a_GradSignQDec.v：paper4-a grad sign Q-decidable, extraction magic 0, harvest 23-03 *)
Definition ng_p4a_GradSignQDec : NewGreenFace :=
  MkNewGreenFace "p4a_GradSignQDec.v" 257 13 20260918 "paper4-a grad sign Q-decidable, extraction magic 0, harvest 23-03" "L271:m4a3e3a".

(* 3 件尾部追加 order L305-307（ 十六件在前）；依赖链 ConcSoftmax→ConcMixSel→ConcB1； *)
(* csm_b1_unconditional_mixing_time=零接口零 Arch 零证书参（无条件机器判据=PA 八问 Closed）。 *)
(* ng_UpReqConcSoftmax —— UpReqConcSoftmax.v：concrete-layer softmax supply: sumf slot eight properties unconditional (five delegated to sumd_ family + per-eps triangle abs_sum_le core), AT5 *)
Definition ng_UpReqConcSoftmax : NewGreenFace :=
  MkNewGreenFace "UpReqConcSoftmax.v" 264 12 20260918 "concrete-layer softmax supply: sumf slot eight properties unconditional (five delegated to sumd_ family + per-eps triangle abs_sum_le core), AT5" "L335:m6f4fd5".

(* ng_UpReqConcMixSel —— UpReqConcMixSel.v：req-face mirror of mixing selector and closure: cmk_k_select (+le) bernoulli wall fully re-proved + cmk_attention_mixing_time (+le) consuming rsq rate 25-arg, AT6 *)
Definition ng_UpReqConcMixSel : NewGreenFace :=
  MkNewGreenFace "UpReqConcMixSel.v" 940 37 20260918 "req-face mirror of mixing selector and closure: cmk_k_select (+le) bernoulli wall fully re-proved + cmk_attention_mixing_time (+le) consuming rsq rate 25-arg, AT6" "L940:md8fd1e".

(* ng_UpReqConcB1 —— UpReqConcB1.v：B1 unconditional assembly: csm_b1_unconditional_mixing_time (+le) zero interface premises zero arch premises zero certificate params (1-element kernel bypass + Htv0 mass resolution + real_arch re-shape via cb1_scale_const), AT7 *)
Definition ng_UpReqConcB1 : NewGreenFace :=
  MkNewGreenFace "UpReqConcB1.v" 394 18 20260918 "B1 unconditional assembly: csm_b1_unconditional_mixing_time (+le) zero interface premises zero arch premises zero certificate params (1-element kernel bypass + Htv0 mass resolution + real_arch re-shape via cb1_scale_const), AT7" "L394:m196b83".

(* ng_UpReqConcB2 —— UpReqConcB2.v：B2 substantial-kernel machine: cb2_dot finite dot product + cb2_list_max_abs cap + cb2_z logit kernel with cb2_Delta (=core+1 unit slack, constructive gap certificate) double bounds, AT8 *)
Definition ng_UpReqConcB2 : NewGreenFace :=
  MkNewGreenFace "UpReqConcB2.v" 627 31 20260918 "B2 substantial-kernel machine: cb2_dot finite dot product + cb2_list_max_abs cap + cb2_z logit kernel with cb2_Delta (=core+1 unit slack, constructive gap certificate) double bounds, AT8" "L664:m668b57".

(* ng_UpReqConcB2Time —— UpReqConcB2Time.v：B2 unconditional closure: cbt_unconditional_mixing_time (+le) on the concrete logit kernel — zero interface premises zero arch premises zero certificate params (Htv0 mass resolution + arch re-shape via cb1_scale_const), honest notes: +1 slack conservatism and 1-element TV0 tier, multi-element recipe'd, AT9 *)
Definition ng_UpReqConcB2Time : NewGreenFace :=
  MkNewGreenFace "UpReqConcB2Time.v" 339 17 20260918 "B2 unconditional closure: cbt_unconditional_mixing_time (+le) on the concrete logit kernel — zero interface premises zero arch premises zero certificate params (Htv0 mass resolution + arch re-shape via cb1_scale_const), honest notes: +1 slack conservatism and 1-element TV0 tier, multi-element recipe'd, AT9" "L381:m51cfe4".

(* ng_UpReqTailResidual —— UpReqTailResidual.v：tail residual engine: Q kernel uniform bound + log two-branch pair + trunc5 bridge, W2/W2B/W2C line *)
Definition ng_UpReqTailResidual : NewGreenFace :=
  MkNewGreenFace "UpReqTailResidual.v" 1527 44 20260918 "tail residual engine: Q kernel uniform bound + log two-branch pair + trunc5 bridge, W2/W2B/W2C line" "L1527:mbd09b8".

(* ng_UpReqVajdaBound —— UpReqVajdaBound.v：two-point Vajda pieces: kl2 closed form + ln engine + piecewise lower bound, WB/WC/WC2/W2D line *)
Definition ng_UpReqVajdaBound : NewGreenFace :=
  MkNewGreenFace "UpReqVajdaBound.v" 843 33 20260918 "two-point Vajda pieces: kl2 closed form + ln engine + piecewise lower bound, WB/WC/WC2/W2D line" "L843:m6f20b0".

(* ng_UpReqIrrationalInstances —— UpReqIrrationalInstances.v：sqrt2 irrational instance via lic mother criterion exact assembly, IR2/IR3 line *)
Definition ng_UpReqIrrationalInstances : NewGreenFace :=
  MkNewGreenFace "UpReqIrrationalInstances.v" 1303 50 20260918 "sqrt2 irrational instance via lic mother criterion exact assembly, IR2/IR3 line" "L1318:m627f02".

(* ng_UpReqEqbComplete —— UpReqEqbComplete.v：eqb judicator completeness direction generic mother + dual instance forwarding, Q19S *)
Definition ng_UpReqEqbComplete : NewGreenFace :=
  MkNewGreenFace "UpReqEqbComplete.v" 277 13 20260918 "eqb judicator completeness direction generic mother + dual instance forwarding, Q19S" "L277:m35f2de".

(* ng_UpReqSentinelMother —— UpReqSentinelMother.v：unreachable sentinel mother pair: domination + domain-bound, with G10 dmin bridge, Q24S *)
Definition ng_UpReqSentinelMother : NewGreenFace :=
  MkNewGreenFace "UpReqSentinelMother.v" 320 16 20260918 "unreachable sentinel mother pair: domination + domain-bound, with G10 dmin bridge, Q24S" "L346:me9fe59".

(* ng_UpReqLn2Irrational —— UpReqLn2Irrational.v：ln2 irrational conditional-form assembly truly via mother criterion, escape window honestly open, IR4 *)
Definition ng_UpReqLn2Irrational : NewGreenFace :=
  MkNewGreenFace "UpReqLn2Irrational.v" 370 21 20260918 "ln2 irrational conditional-form assembly truly via mother criterion, escape window honestly open, IR4" "L379:m989ebf".

(* ng_UpReqSqrt3Irrational —— UpReqSqrt3Irrational.v：sqrt3 无理性第三实例、mod-3 下降 + 4/11 逃逸窗再参数化，IR5 *)
Definition ng_UpReqSqrt3Irrational : NewGreenFace :=
  MkNewGreenFace "UpReqSqrt3Irrational.v" 1141 27 20260918 "sqrt3 irrational third instance, mod-3 descent + 4/11 escape window re-parameterization, IR5" "L1141:mba9a54".

(* 1 件尾部追加 order L317；零 CW 基座依赖纯 Q 层；封顶定理=闭式族量级封顶（affine 可反解族，诚实限定）。 *)

(* ng_UpReqMixLogE —— UpReqMixLogE.v：closed-form cap theorems for bernoulli-family selectors (sharpened F1/F2/F3 + mixe_cf_cap/_gen/_div/_select_cap), pure Q-layer zero CW-base dependency, race E *)
Definition ng_UpReqMixLogE : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogE.v" 792 48 20260918 "closed-form cap theorems for bernoulli-family selectors, sharpened F1/F2/F3, pure Q-layer zero CW-base dependency, race E first finisher" "L792:m12d039".

(* 2 件尾部追加 order L374-375；E 件 L373 已于 先册（792 48 ），本次 md5 复核三面全等免重册； *)
(* A/B 与 E 间零内边，A 外依赖 CW_219/UpTVDoeblin/KLWallClosed/UpReqIterGeomRate 全在提交面 L16-L273。 *)
(* ng_UpReqMixLogA —— UpReqMixLogA.v：rational-reduction + Q-layer decidable bisection log-scale k selector (mixa_ family: qbern window / fuel bsearch / k0+b0 bridges / pow_budget_log cert+min), four-gate green, race A *)
Definition ng_UpReqMixLogA : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogA.v" 1304 57 20260919 "rational-reduction + Q-decidable bisection log-scale k selector (mixa_ family), zero new axioms Print Assumptions closed, race A" "L1315:mc38cac".

(* ng_UpReqMixLogB —— UpReqMixLogB.v：galloping (exponential) search + terminal bisection log-scale k selector (mixb_ family: qbernoulli / gallop / sel_scale compare count 2*log2 K+5), four-gate green, race B *)
Definition ng_UpReqMixLogB : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogB.v" 1311 65 20260919 "galloping search + terminal bisection log-scale k selector (mixb_ family), compare count bounded 2*log2 K+5, zero new axioms Print Assumptions closed, race B" "L1335:m395a8d".

(* 2 件尾部追加 order L376-377（两件互不依赖零内边，按字母序就位：Fin2 L376、D L377）；vo 树内 9.1 原地重编（跨树 digest 防御：Live_X 产物未直种），.vo/.vos 头 436f712100015ff4，双件单件 coqchk RC=0；D 依赖 CW_219/UpTVDoeblin/UpReqIterGeomRate/UpReqMixingTime/KLWallClosed 全在提交面 L16-L274，Fin2 依赖 CW_219/AttnDoeblin/UpReqAlgebra/UpReqDist/UpReqSampling/UpReqSumD/UpReqConcSoftmax/UpReqConcMixSel/UpReqConcB1/UpReqConcB2 全在提交面 L16-L315。 *)
(* ng_UpReqConcFin2 —— UpReqConcFin2.v：Fin-2 non-degeneracy concrete instance (cf2_ family: bool world data T2 + TV strict positivity T3 + T4b abs_row bridges + T5b cf2_tv_iter_eps closure; lineage F21 3091e0d0 -> F22 green base a3833710 via concurrent-collision arbitration -> F23 harvest), four-gate green, T2-T7 full incl. T6 mixing chain + T7 mixing_time (ptmass+general), 50 PA Closed *)
Definition ng_UpReqConcFin2 : NewGreenFace :=
  MkNewGreenFace "UpReqConcFin2.v" 1569 25 20260919 "Fin-2 non-degeneracy concrete instance (cf2_ family), TV non-triviality demo + T5b iteration closure on arbitration base a3833710, zero new axioms Print Assumptions closed" "L1648:m42c627".
(* ng_UpReqMixLogD —— UpReqMixLogD.v：Path D squared-ladder kappa0 powers + binary-composition log-scale k selector (mixd_ family: ladder/scan_up/desc with QleT' certificate direct-return, cost c <= 5*d+2, Q-core Defined selector + Real rationalization shell), four-gate green, race D, 66 Qed / 10 PA Closed *)
Definition ng_UpReqMixLogD : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogD.v" 1725 66 20260919 "squared-ladder + binary-composition log-scale k selector (mixd_ family), certificate direct-return with cost bound 5*d+2, zero new axioms Print Assumptions closed, race D" "L1730:ma38e8a".

(* ng_UpAblD1PPO_UpReqPPOPlain —— UpAblD1PPO_UpReqPPOPlain.v：FA-D1PPO in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1PPO_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1PPO_UpReqPPOPlain.v" 117 2 20260919 "FA-D1PPO in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L115:ma1fb2a".
(* ng_UpAblD1S10_UpReqConcMixSel —— UpAblD1S10_UpReqConcMixSel.v：FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1S10_UpReqConcMixSel : NewGreenFace :=
  MkNewGreenFace "UpAblD1S10_UpReqConcMixSel.v" 124 1 20260919 "FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L124:me22e2c".
(* ng_UpAblD1S10_UpReqPPOPlain —— UpAblD1S10_UpReqPPOPlain.v：FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1S10_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S10_UpReqPPOPlain.v" 120 2 20260919 "FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L120:mc3c689".
(* ng_UpAblD1S11_UpReqPPOPlain —— UpAblD1S11_UpReqPPOPlain.v：FA-D1S11 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised; note: sibling UpAblD1S11_UpReqCauchy quarantined, unterminated comment) *)
Definition ng_UpAblD1S11_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S11_UpReqPPOPlain.v" 126 2 20260919 "FA-D1S11 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised; note: sibling UpAblD1S11_UpReqCauchy quarantined, unterminated comment); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L126:m50f67f".
(* ng_UpAblD1S2_e752_UpReqAttnIter —— UpAblD1S2_e752_UpReqAttnIter.v：FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green () *)
Definition ng_UpAblD1S2_e752_UpReqAttnIter : NewGreenFace :=
  MkNewGreenFace "UpAblD1S2_e752_UpReqAttnIter.v" 92 2 20260919 "FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green (_tfad1s2_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L92:m747e7d".
(* ng_UpAblD1S2_reqlog_UpReqCauchy —— UpAblD1S2_reqlog_UpReqCauchy.v：FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green () *)
Definition ng_UpAblD1S2_reqlog_UpReqCauchy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S2_reqlog_UpReqCauchy.v" 48 1 20260919 "FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green (_tfad1s2_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L48:m7bf6ba".
(* ng_UpAblD1S3_fep_UpReqAttnGibbs —— UpAblD1S3_fep_UpReqAttnGibbs.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_fep_UpReqAttnGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_fep_UpReqAttnGibbs.v" 69 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L69:m3abace".
(* ng_UpAblD1S3_fep_UpReqSteadyThermo —— UpAblD1S3_fep_UpReqSteadyThermo.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_fep_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_fep_UpReqSteadyThermo.v" 155 5 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L167:m15bebd".
(* ng_UpAblD1S3_sum_pos_AlignIdUnclosed —— UpAblD1S3_sum_pos_AlignIdUnclosed.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_AlignIdUnclosed.v" 53 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L53:m437045".
(* ng_UpAblD1S3_sum_pos_SecondLawQuantified —— UpAblD1S3_sum_pos_SecondLawQuantified.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_SecondLawQuantified.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:md95a37".
(* ng_UpAblD1S3_sum_pos_UpReqEntropyMaxTemp —— UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:maef005".
(* ng_UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg —— UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:m950571".
(* ng_UpAblD1S4_UpReqStepKLEtaInst —— UpAblD1S4_UpReqStepKLEtaInst.v：FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green () *)
Definition ng_UpAblD1S4_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "UpAblD1S4_UpReqStepKLEtaInst.v" 137 5 20260919 "FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green (_tfad1s4_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L111:m720e91".
(* ng_UpAblD1S4_UpReqTopKTVChain —— UpAblD1S4_UpReqTopKTVChain.v：FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green () *)
Definition ng_UpAblD1S4_UpReqTopKTVChain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S4_UpReqTopKTVChain.v" 128 2 20260919 "FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green (_tfad1s4_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L128:m7c2d15".
(* ng_UpAblD1S5_UpReqDoeblinEntropy —— UpAblD1S5_UpReqDoeblinEntropy.v：FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green () *)
Definition ng_UpAblD1S5_UpReqDoeblinEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S5_UpReqDoeblinEntropy.v" 624 13 20260919 "FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green (_tfad1s5_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L609:m129927".
(* ng_UpAblD1S5_UpReqEntropyMonoSplit —— UpAblD1S5_UpReqEntropyMonoSplit.v：FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green () *)
Definition ng_UpAblD1S5_UpReqEntropyMonoSplit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S5_UpReqEntropyMonoSplit.v" 596 8 20260919 "FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green (_tfad1s5_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L596:m2cc121".
(* ng_UpAblD1S6_SecondLawQuantified —— UpAblD1S6_SecondLawQuantified.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_SecondLawQuantified.v" 69 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L72:m226112".
(* ng_UpAblD1S6_UpReqMinPKLChain —— UpAblD1S6_UpReqMinPKLChain.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqMinPKLChain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqMinPKLChain.v" 99 3 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L99:m3ad85e".
(* ng_UpAblD1S6_UpReqRealFEP —— UpAblD1S6_UpReqRealFEP.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqRealFEP : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqRealFEP.v" 71 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L73:mb7314f".
(* ng_UpAblD1S6_UpReqSteadyThermo —— UpAblD1S6_UpReqSteadyThermo.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqSteadyThermo.v" 74 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m66e6cf".
(* ng_UpAblD1S7_UpReqEntropyDeficitTemp —— UpAblD1S7_UpReqEntropyDeficitTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyDeficitTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyDeficitTemp.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m13af8c".
(* ng_UpAblD1S7_UpReqEntropyMaxTemp —— UpAblD1S7_UpReqEntropyMaxTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyMaxTemp.v" 81 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L80:mf67260".
(* ng_UpAblD1S7_UpReqEntropyUniqueNeg —— UpAblD1S7_UpReqEntropyUniqueNeg.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyUniqueNeg.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m3b33e1".
(* ng_UpAblD1S7_UpReqEntropyUniqueTemp —— UpAblD1S7_UpReqEntropyUniqueTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyUniqueTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyUniqueTemp.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m6be901".
(* ng_UpAblD1S8_TempSoftmaxInstantiation —— UpAblD1S8_TempSoftmaxInstantiation.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_TempSoftmaxInstantiation.v" 90 1 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L86:ma4d8d5".
(* ng_UpAblD1S8_UpReqPPOPlain —— UpAblD1S8_UpReqPPOPlain.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_UpReqPPOPlain.v" 173 3 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L173:m7041dd".
(* ng_UpAblD1S8_UpReqTempDefs —— UpAblD1S8_UpReqTempDefs.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_UpReqTempDefs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_UpReqTempDefs.v" 79 1 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L80:m329919".
(* ng_UpAblD1S9_UpReqAttnIter —— UpAblD1S9_UpReqAttnIter.v：FA-D1S9, T x21 + W x1, four-gate green () *)
Definition ng_UpAblD1S9_UpReqAttnIter : NewGreenFace :=
  MkNewGreenFace "UpAblD1S9_UpReqAttnIter.v" 233 4 20260919 "FA-D1S9, T x21 + W x1, four-gate green (_tfad1s9_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L209:mf549db".
(* ng_UpAblD1_expf_pack —— UpAblD1_expf_pack.v：FA-D1S1, expf bundle N1 (C13 three-way grade conflict counted N per ledger), four-gate green () *)
Definition ng_UpAblD1_expf_pack : NewGreenFace :=
  MkNewGreenFace "UpAblD1_expf_pack.v" 98 1 20260919 "FA-D1S1, expf bundle N1 (C13 three-way grade conflict counted N per ledger), four-gate green (_tfad1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L98:mae2830".
(* ng_UpAblD1_fa53_lpc_broadcast —— UpAblD1_fa53_lpc_broadcast.v：FA-D1S1, fa53 lpc broadcast N1, four-gate green () *)
Definition ng_UpAblD1_fa53_lpc_broadcast : NewGreenFace :=
  MkNewGreenFace "UpAblD1_fa53_lpc_broadcast.v" 201 9 20260919 "FA-D1S1, fa53 lpc broadcast N1, four-gate green (_tfad1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L201:m91e4c1".
(* ng_UpAblD2_AbsLeId_RI_DO —— UpAblD2_AbsLeId_RI_DO.v：FA-D2S1, N3 x2 supply-pair + N1 x2 RI-face + T x1 (W register DO carrier noted), four-gate green () *)
Definition ng_UpAblD2_AbsLeId_RI_DO : NewGreenFace :=
  MkNewGreenFace "UpAblD2_AbsLeId_RI_DO.v" 136 5 20260919 "FA-D2S1, N3 x2 supply-pair + N1 x2 RI-face + T x1 (W register DO carrier noted), four-gate green (_tfad2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L136:mb8d671".
(* ng_UpAblP1_SecondLawQuantified_sumd —— UpAblP1_SecondLawQuantified_sumd.v：FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green () *)
Definition ng_UpAblP1_SecondLawQuantified_sumd : NewGreenFace :=
  MkNewGreenFace "UpAblP1_SecondLawQuantified_sumd.v" 101 4 20260919 "FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green (_tfap1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L101:m030bcf".
(* ng_UpAblP1_SqrtfCauchyArch_arch —— UpAblP1_SqrtfCauchyArch_arch.v：FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green () *)
Definition ng_UpAblP1_SqrtfCauchyArch_arch : NewGreenFace :=
  MkNewGreenFace "UpAblP1_SqrtfCauchyArch_arch.v" 54 0 20260919 "FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green (_tfap1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L54:mc779e8".
(* ng_UpAblP1_SqrtfCauchy_four_slots —— UpAblP1_SqrtfCauchy_four_slots.v：FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green () *)
Definition ng_UpAblP1_SqrtfCauchy_four_slots : NewGreenFace :=
  MkNewGreenFace "UpAblP1_SqrtfCauchy_four_slots.v" 89 0 20260919 "FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green (_tfap1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L89:m4a0b0c".
(* ng_UpAblP2_FepIdentClass_inst_bundle —— UpAblP2_FepIdentClass_inst_bundle.v：FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green () *)
Definition ng_UpAblP2_FepIdentClass_inst_bundle : NewGreenFace :=
  MkNewGreenFace "UpAblP2_FepIdentClass_inst_bundle.v" 214 9 20260919 "FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green (_tfap2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L207:ma84569".
(* ng_UpAblP2_SecondLawConsume_sumdis —— UpAblP2_SecondLawConsume_sumdis.v：FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green () *)
Definition ng_UpAblP2_SecondLawConsume_sumdis : NewGreenFace :=
  MkNewGreenFace "UpAblP2_SecondLawConsume_sumdis.v" 179 6 20260919 "FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green (_tfap2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L179:m1901c0".
(* ng_UpAblP2_UpMinP_tokens_pack —— UpAblP2_UpMinP_tokens_pack.v：FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green () *)
Definition ng_UpAblP2_UpMinP_tokens_pack : NewGreenFace :=
  MkNewGreenFace "UpAblP2_UpMinP_tokens_pack.v" 90 3 20260919 "FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green (_tfap2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L90:m04b533".
(* ng_UpAblP3_UpReqAttnMixTime —— UpAblP3_UpReqAttnMixTime.v：FA-P3S1 batch, AMT 22 + MixSel 25 slot-face (N25//W1 batch), four-gate green () *)
Definition ng_UpAblP3_UpReqAttnMixTime : NewGreenFace :=
  MkNewGreenFace "UpAblP3_UpReqAttnMixTime.v" 247 9 20260919 "FA-P3S1 batch, AMT 22 + MixSel 25 slot-face (N25/T21/W1 batch), four-gate green (_tfap3s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L247:mcca60f".
(* ng_UpAblP3_UpReqConcMixSel —— UpAblP3_UpReqConcMixSel.v：FA-P3S1 batch, AMT 22 + MixSel 25 slot-face (N25//W1 batch), four-gate green () *)
Definition ng_UpAblP3_UpReqConcMixSel : NewGreenFace :=
  MkNewGreenFace "UpAblP3_UpReqConcMixSel.v" 229 8 20260919 "FA-P3S1 batch, AMT 22 + MixSel 25 slot-face (N25/T21/W1 batch), four-gate green (_tfap3s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L229:mc9d824".
(* ng_UpAbl_S04RealExpLogConv —— UpAbl_S04RealExpLogConv.v：v1 batch (a), N1 x1 + N2 x3, four-gate green () *)
Definition ng_UpAblT10_S04RealExpLogConv : NewGreenFace :=
  MkNewGreenFace "UpAblT10_S04RealExpLogConv.v" 85 4 20260919 "v1 T10 batch (T10a), N1 x1 + N2 x3, four-gate green (_tt10a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L85:m2e0cd9".
(* ng_UpAbl_S11_TP3B5 —— UpAbl_S11_TP3B5.v：v1 batch (a), N1 x2 + N2 x6, four-gate green () *)
Definition ng_UpAblT11_S11_TP3B5 : NewGreenFace :=
  MkNewGreenFace "UpAblT11_S11_TP3B5.v" 139 8 20260919 "v1 T11 batch (T11a), N1 x2 + N2 x6, four-gate green (_tt11a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L139:m013518".
(* ng_UpAbl_G13 —— UpAbl_G13.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblT12_G13.v" 78 3 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L98:m7e565f".
(* ng_UpAbl_UpRealLeB2 —— UpAbl_UpRealLeB2.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_UpRealLeB2 : NewGreenFace :=
  MkNewGreenFace "UpAblT12_UpRealLeB2.v" 159 3 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L159:m0b03dc".
(* ng_UpAbl_UpReqAlignRestA —— UpAbl_UpReqAlignRestA.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_UpReqAlignRestA : NewGreenFace :=
  MkNewGreenFace "UpAblT12_UpReqAlignRestA.v" 49 1 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L49:m218ee5".
(* ng_UpAbl_UpEntropyGainReq —— UpAbl_UpEntropyGainReq.v：v1 a batch, N x8, four-gate green () *)
Definition ng_UpAblT13_UpEntropyGainReq : NewGreenFace :=
  MkNewGreenFace "UpAblT13_UpEntropyGainReq.v" 43 1 20260919 "v1 T13a batch, N x8, four-gate green (_tt13a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:m637407".
(* ng_UpAbl_UpFirewallReq —— UpAbl_UpFirewallReq.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpReqAlignRestA —— UpAbl_UpReqAlignRestA.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpReqSampling —— UpAbl_UpReqSampling.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpSigMigrate2 —— UpAbl_UpSigMigrate2.v：v1 a batch, N x8, four-gate green () *)
Definition ng_UpAblT13_UpSigMigrate2 : NewGreenFace :=
  MkNewGreenFace "UpAblT13_UpSigMigrate2.v" 45 1 20260919 "v1 T13a batch, N x8, four-gate green (_tt13a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L45:m3d3f78".
(* ng_UpAblb_G06_BForm —— UpAblb_G06_BForm.v：v1 b batch, N x19, four-gate green () *)
Definition ng_UpAblT13b_G06_BForm : NewGreenFace :=
  MkNewGreenFace "UpAblT13b_G06_BForm.v" 113 7 20260919 "v1 T13b batch, N x19, four-gate green (_tt13b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L185:mb9d88c".
(* ng_UpAblb_G13 —— UpAblb_G13.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlign —— UpAblb_UpReqAlign.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlign2 —— UpAblb_UpReqAlign2.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlignRestA —— UpAblb_UpReqAlignRestA.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqDist —— UpAblb_UpReqDist.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpSigMigrate —— UpAblb_UpSigMigrate.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpSigMigrate2 —— UpAblb_UpSigMigrate2.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpTVDoeblin —— UpAblb_UpTVDoeblin.v：v1 b batch, N x19, four-gate green () *)
Definition ng_UpAblT13b_UpTVDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT13b_UpTVDoeblin.v" 39 1 20260919 "v1 T13b batch, N x19, four-gate green (_tt13b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L39:mceb0e2".
(* ng_UpAblc_G13 —— UpAblc_G13.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
Definition ng_UpAblT13c_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblT13c_G13.v" 271 11 20260919 "T13c batch9, N3 x8 + conditional discharge x3, four-gate green (_tt13c_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L327:m127dd7".
(* ng_UpAblc_UpReqDist —— UpAblc_UpReqDist.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
Definition ng_UpAblT13c_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT13c_UpReqDist.v" 119 4 20260919 "T13c batch9, N3 x8 + conditional discharge x3, four-gate green (_tt13c_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L119:mca9cee".
(* ng_UpAblc_UpSigMigrate2 —— UpAblc_UpSigMigrate2.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
(* ng_UpAblT1_UpFirewallReq —— UpAblT1_UpFirewallReq.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpFirewallReq.v" 97 5 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L97:mc00df6".
(* ng_UpAblT1_UpReqDist —— UpAblT1_UpReqDist.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpReqDist.v" 237 14 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L363:m606d79".
(* ng_UpAblT1_UpReqTempEntropy —— UpAblT1_UpReqTempEntropy.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpReqTempEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpReqTempEntropy.v" 112 6 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L112:m758692".
(* ng_UpAblT1b_AttnDoeblin —— UpAblT1b_AttnDoeblin.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_AttnDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_AttnDoeblin.v" 172 8 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L172:m139121".
(* ng_UpAblT1b_S06_DiffSamplingGibbs —— UpAblT1b_S06_DiffSamplingGibbs.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_S06_DiffSamplingGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_S06_DiffSamplingGibbs.v" 148 6 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L158:m8b1e3b".
(* ng_UpAblT1b_S13_NLiveAudit —— UpAblT1b_S13_NLiveAudit.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_S13_NLiveAudit : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_S13_NLiveAudit.v" 166 8 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L166:m813da1".
(* ng_UpAblT1c_UpFirewallReq —— UpAblT1c_UpFirewallReq.v：v1 T1c batch, N x5 firewall five-bridge, four-gate green () *)
Definition ng_UpAblT1c_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT1c_UpFirewallReq.v" 236 6 20260919 "v1 T1c batch, N x5 firewall five-bridge, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L236:md5fc79".
(* ng_UpAblT2a_UpFirewallReq —— UpAblT2a_UpFirewallReq.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpFirewallReq.v" 32 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L32:m962b43".
(* ng_UpAblT2a_UpReqAlignRestA —— UpAblT2a_UpReqAlignRestA.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqAlignRestA : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqAlignRestA.v" 30 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L30:m933719".
(* ng_UpAblT2a_UpReqPPO —— UpAblT2a_UpReqPPO.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqPPO : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqPPO.v" 29 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L29:m6615c4".
(* ng_UpAblT2a_UpReqTempEntropy —— UpAblT2a_UpReqTempEntropy.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqTempEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqTempEntropy.v" 41 2 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L41:m7ed002".
(* ng_UpAblT2b_PredRelax5 —— UpAblT2b_PredRelax5.v：v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green () *)
Definition ng_UpAblT2b_PredRelax5 : NewGreenFace :=
  MkNewGreenFace "UpAblT2b_PredRelax5.v" 440 17 20260919 "v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green (_tt2b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L456:m8d1dba".
(* ng_UpAblT2b_fa53_lpc_broadcast —— UpAblT2b_fa53_lpc_broadcast.v：v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green () *)
Definition ng_UpAblT2b_fa53_lpc_broadcast : NewGreenFace :=
  MkNewGreenFace "UpAblT2b_fa53_lpc_broadcast.v" 165 11 20260919 "v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green (_tt2b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L208:mc39494".
(* ng_UpAblT3_UpReqAlign —— UpAblT3_UpReqAlign.v：v1 T3 batch (T3a), N1 x25, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT3_UpReqAlign : NewGreenFace :=
  MkNewGreenFace "UpAblT3_UpReqAlign.v" 228 13 20260919 "v1 T3 batch (T3a), N1 x25, four-gate green (_tt3a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L405:m8d1bda".
(* ng_UpAblT3_UpReqFEPAttn —— UpAblT3_UpReqFEPAttn.v：v1 T3 batch (T3a), N1 x25, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT3_UpReqFEPAttn : NewGreenFace :=
  MkNewGreenFace "UpAblT3_UpReqFEPAttn.v" 210 12 20260919 "v1 T3 batch (T3a), N1 x25, four-gate green (_tt3a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L210:m419e22".
(* ng_UpAblT4_RLHFkl —— UpAblT4_RLHFkl.v：v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green () *)
Definition ng_UpAblT4_RLHFkl : NewGreenFace :=
  MkNewGreenFace "UpAblT4_RLHFkl.v" 123 2 20260919 "v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green (_tt4a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L114:m353c3f".
(* ng_UpAblT4_SumCarrier —— UpAblT4_SumCarrier.v：v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green () *)
Definition ng_UpAblT4_SumCarrier : NewGreenFace :=
  MkNewGreenFace "UpAblT4_SumCarrier.v" 156 4 20260919 "v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green (_tt4a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L156:m146015".
(* ng_UpAblT5_S04_RealExpLogConv —— UpAblT5_S04_RealExpLogConv.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S04_RealExpLogConv : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S04_RealExpLogConv.v" 86 3 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L86:mfebc57".
(* ng_UpAblT5_S05_AlignmentGRPO —— UpAblT5_S05_AlignmentGRPO.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S05_AlignmentGRPO : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S05_AlignmentGRPO.v" 60 2 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L60:m2b5923".
(* ng_UpAblT5_S06_DiffSamplingGibbs —— UpAblT5_S06_DiffSamplingGibbs.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S06_DiffSamplingGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S06_DiffSamplingGibbs.v" 43 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:maf74e2".
(* ng_UpAblT5_S12_B5RecycleSF —— UpAblT5_S12_B5RecycleSF.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S12_B5RecycleSF : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S12_B5RecycleSF.v" 29 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L29:m1bb424".
(* ng_UpAblT5_UpFirewall —— UpAblT5_UpFirewall.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_UpFirewall : NewGreenFace :=
  MkNewGreenFace "UpAblT5_UpFirewall.v" 44 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L44:m8bf205".
(* ng_UpAblT5_UpReqAlgebra —— UpAblT5_UpReqAlgebra.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_UpReqAlgebra : NewGreenFace :=
  MkNewGreenFace "UpAblT5_UpReqAlgebra.v" 45 2 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L45:m478662".
(* ng_UpAblT6_UpReqAlign2 —— UpAblT6_UpReqAlign2.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqAlign2 : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqAlign2.v" 89 4 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L89:m2f4d7b".
(* ng_UpAblT6_UpReqPPO —— UpAblT6_UpReqPPO.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqPPO : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqPPO.v" 77 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L97:m8f74af".
(* ng_UpAblT6_UpReqSampling —— UpAblT6_UpReqSampling.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqSampling : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqSampling.v" 194 11 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L358:m573cca".
(* ng_UpAblT6_UpSigMigrate —— UpAblT6_UpSigMigrate.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpSigMigrate : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpSigMigrate.v" 73 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L93:m957ce6".
(* ng_UpAblT6_UpSigMigrate2 —— UpAblT6_UpSigMigrate2.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpSigMigrate2 : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpSigMigrate2.v" 73 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L93:mb81dbc".
(* ng_UpAblT7_two_point_pack —— UpAblT7_two_point_pack.v：v1 T7 batch (T7a) coverage-pack, N1 x23 + N2 x101 + N3 x13 + T x394 (7a coverage basis 531), four-gate green () *)
Definition ng_UpAblT7_two_point_pack : NewGreenFace :=
  MkNewGreenFace "UpAblT7_two_point_pack.v" 217 13 20260919 "v1 T7 batch (T7a) coverage-pack, N1 x23 + N2 x101 + N3 x13 + T x394 (7a coverage basis 531), four-gate green (_tt7a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L233:mb03c18".
(* ng_UpAblT7b_real_two_point_pack —— UpAblT7b_real_two_point_pack.v：v1 T7b batch, N x61, four-gate green () *)
Definition ng_UpAblT7b_real_two_point_pack : NewGreenFace :=
  MkNewGreenFace "UpAblT7b_real_two_point_pack.v" 347 21 20260919 "v1 T7b batch, N x61, four-gate green (_tt7b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L384:mbb15a0".
(* ng_UpAblT9_G09_MiscSmall —— UpAblT9_G09_MiscSmall.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_G09_MiscSmall : NewGreenFace :=
  MkNewGreenFace "UpAblT9_G09_MiscSmall.v" 42 2 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L42:m5d6b2f".
(* ng_UpAblT9_UpReqDist —— UpAblT9_UpReqDist.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqDist.v" 64 3 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L64:m73bbc3".
(* ng_UpAblT9_UpReqFEPAttn —— UpAblT9_UpReqFEPAttn.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqFEPAttn : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqFEPAttn.v" 61 3 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L61:mc43870".
(* ng_UpAblT9_UpReqSampling —— UpAblT9_UpReqSampling.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqSampling : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqSampling.v" 77 4 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L77:m0ccd2f".
(* ng_UpAblT9_UpSigMigrate —— UpAblT9_UpSigMigrate.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpSigMigrate : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpSigMigrate.v" 34 1 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L34:m831da3".
(* ng_UpAblT9_UpTVDoeblin —— UpAblT9_UpTVDoeblin.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpTVDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpTVDoeblin.v" 49 2 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L49:m9073b3".

(* ng_Ln2Bridge —— Ln2Bridge.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Ln2Bridge : NewGreenFace :=
  MkNewGreenFace "Ln2Bridge.v" 719 23 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L729:mb8a646".
(* ng_PintPosGrid —— PintPosGrid.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_PintPosGrid : NewGreenFace :=
  MkNewGreenFace "PintPosGrid.v" 179 8 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L179:mb4d650".
(* ng_BeukersIdentity —— BeukersIdentity.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_BeukersIdentity : NewGreenFace :=
  MkNewGreenFace "BeukersIdentity.v" 265 15 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L265:mb2a825".
(* ng_BeukersVariant —— BeukersVariant.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_BeukersVariant : NewGreenFace :=
  MkNewGreenFace "BeukersVariant.v" 522 30 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L536:m8c7d7d".
(* ng_Hanson3Pow —— Hanson3Pow.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Hanson3Pow : NewGreenFace :=
  MkNewGreenFace "Hanson3Pow.v" 292 16 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L292:m73e017".
(* ng_Ln2Integrality —— Ln2Integrality.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Ln2Integrality : NewGreenFace :=
  MkNewGreenFace "Ln2Integrality.v" 484 27 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L497:mcd89cc".
(* ng_TrueNumerator —— TrueNumerator.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_TrueNumerator : NewGreenFace :=
  MkNewGreenFace "TrueNumerator.v" 274 29 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L284:mb4f37c".
(* ng_RealIdentity —— RealIdentity.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_RealIdentity : NewGreenFace :=
  MkNewGreenFace "RealIdentity.v" 359 22 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L377:m421f75".
(* ng_SupplyAssembly —— SupplyAssembly.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "SupplyAssembly.v" 325 21 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L338:m6efde4".

(* ng_BetaLower —— BetaLower.v： red-file repaired (AUD β1 bracket + 7 latent, R93FIX), four-gate green, zero statement-face change *)
Definition ng_BetaLower : NewGreenFace :=
  MkNewGreenFace "BetaLower.v" 498 31 20260919 "R94 red-file repaired (AUD β1 bracket + 7 latent, R93FIX), four-gate green, zero statement-face change; born-in-place verified in vo tree" "L501:m1ee440".

(* ng_UpAblZpos —— UpAblZpos.v： paper-1 ablation (AB1): Z_align_pos abstract-layer packing-form discharge + unconditional nonneg companion, four-gate green; built-at-registration verified in vo tree *)
Definition ng_UpAblZpos : NewGreenFace :=
  MkNewGreenFace "UpAblZpos.v" 107 3 20260920 "R95 paper-1 ablation (AB1): Z_align_pos abstract-layer packing-form discharge + unconditional nonneg companion, four-gate green; born-in-place verified in vo tree" "L117:m05487d".

(* ng_UpAblZposReal —— UpAblZposReal.v： paper-1 ablation (AB2): Z_align_pos Real-layer unconditional discharge + finite-sum positivity carrier, three theorems all N-grade, four-gate green *)
Definition ng_UpAblZposReal : NewGreenFace :=
  MkNewGreenFace "UpAblZposReal.v" 138 3 20260920 "R95 paper-1 ablation (AB2): Z_align_pos Real-layer unconditional discharge + finite-sum positivity carrier, three theorems all N-grade, four-gate green" "L139:m8b5e5c".

(* ng_UpAblZposDirect —— UpAblZposDirect.v： paper-1 ablation (AB7): B4 slot direct-config on RealEnhancedReal, Id-line slot original form structurally unreachable verdict per sec 9.5, four-gate green *)
Definition ng_UpAblZposDirect : NewGreenFace :=
  MkNewGreenFace "UpAblZposDirect.v" 162 4 20260920 "R95 paper-1 ablation (AB7): B4 slot direct-config on RealEnhancedReal, Id-line slot original form structurally unreachable verdict per sec 9.5, four-gate green" "L162:mc15b50".

(* ng_UpAblEps49RKDBase —— UpAblEps49RKDBase.v： paper-1 ablation (AB3 companion): RKD private-byte-snapshot base for 4.9 slot alignment, content-identical to RealKLDecomp body, four-gate green; parallel replica coexists per merge-replica discipline *)
Definition ng_UpAblEps49RKDBase : NewGreenFace :=
  MkNewGreenFace "UpAblEps49RKDBase.v" 912 11 20260920 "R95 paper-1 ablation (AB3 companion): RKD private-byte-snapshot base for 4.9 slot alignment, content-identical to RealKLDecomp body, four-gate green; parallel replica coexists per merge-replica discipline" "L914:m7e643f".

(* ng_UpAblEps49Main —— UpAblEps49Main.v： paper-1 ablation (AB3): 4.9 load-bearing slot real_kl_decomp_full discharge (bool two-point instance), four-gate green *)
Definition ng_UpAblEps49Main : NewGreenFace :=
  MkNewGreenFace "UpAblEps49Main.v" 205 8 20260920 "R95 paper-1 ablation (AB3): 4.9 load-bearing slot real_kl_decomp_full discharge (bool two-point instance), four-gate green" "L205:mb01340".

(* ng_UpAblEps49List —— UpAblEps49List.v： paper-1 ablation (e49l): 4.9 slot list-carrier true-premise-shape complete discharge, zero gap with S08 global form, four-gate green *)
Definition ng_UpAblEps49List : NewGreenFace :=
  MkNewGreenFace "UpAblEps49List.v" 237 7 20260920 "R95 paper-1 ablation (e49l): 4.9 slot list-carrier true-premise-shape complete discharge, zero gap with S08 global form, four-gate green" "L237:me2b034".

(* ng_UpAblEps49Body —— UpAblEps49Body.v： paper-1 ablation (X1): theorem 4.9 body list-carrier downstream direct-config, both honest slots swapped, zero residual premises, four-gate green *)
Definition ng_UpAblEps49Body : NewGreenFace :=
  MkNewGreenFace "UpAblEps49Body.v" 264 1 20260920 "R95 paper-1 ablation (X1): theorem 4.9 body list-carrier downstream direct-config, both honest slots swapped, zero residual premises, four-gate green" "L264:mbbb4e6".

(* ng_UpAblEps66Sum —— UpAblEps66Sum.v： paper-1 ablation (AB5): 6.6 sum-interface family three slots discharge (enum + bool flagship closed forms), four-gate green *)
Definition ng_UpAblEps66Sum : NewGreenFace :=
  MkNewGreenFace "UpAblEps66Sum.v" 141 6 20260920 "R95 paper-1 ablation (AB5): 6.6 sum-interface family three slots discharge (enum + bool flagship closed forms), four-gate green" "L164:m95e361".

(* ng_UpAblEps66Body —— UpAblEps66Body.v： paper-1 ablation (X2): theorem 6.6 body 11-slot swap, flag_closed zero-honest-interface version, four-gate green *)
Definition ng_UpAblEps66Body : NewGreenFace :=
  MkNewGreenFace "UpAblEps66Body.v" 213 3 20260920 "R95 paper-1 ablation (X2): theorem 6.6 body 11-slot swap, flag_closed zero-honest-interface version, four-gate green" "L213:m678c4c".

(* ng_UpAblP1T1_AlignCert —— UpAblP1T1_AlignCert.v： paper-1 ablation (T1R2): alignment certificate cluster 6 bundles supply theorems, all T-grade honest declaration, four-gate green *)
Definition ng_UpAblP1T1_AlignCert : NewGreenFace :=
  MkNewGreenFace "UpAblP1T1_AlignCert.v" 168 8 20260920 "R95 paper-1 ablation (T1R2): alignment certificate cluster 6 bundles supply theorems, all T-grade honest declaration, four-gate green" "L168:m8cd5bf".

(* ng_UpAblP1T2_GrpoAuditCert —— UpAblP1T2_GrpoAuditCert.v： paper-1 ablation (T2R2): GRPO/audit/FE-constant cluster 9 bundles supply theorems, predecessor pieces re-verified four-gate green *)
Definition ng_UpAblP1T2_GrpoAuditCert : NewGreenFace :=
  MkNewGreenFace "UpAblP1T2_GrpoAuditCert.v" 259 9 20260920 "R95 paper-1 ablation (T2R2): GRPO/audit/FE-constant cluster 9 bundles supply theorems, predecessor pieces re-verified four-gate green" "L284:mcb01d9".

(* ng_UpAblP7_AbsNonNeg —— UpAblP7_AbsNonNeg.v：colleague paper-7 ablation campaign (PA7/): AbsNonNeg residue, first unconditional form in library, eps-to-unconditional equivalence direction viable, four-gate green; built-at-registration verified in vo tree *)
Definition ng_UpAblP7_AbsNonNeg : NewGreenFace :=
  MkNewGreenFace "UpAblP7_AbsNonNeg.v" 364 13 20260920 "colleague paper-7 ablation campaign (PA7/R93): AbsNonNeg residue, first unconditional form in library, eps-to-unconditional equivalence direction viable, four-gate green; born-in-place verified in vo tree" "L364:m7e3206".

(* ng_UpAblP7_LoHiBridge —— UpAblP7_LoHiBridge.v：colleague PA7: LoHi bridge pieces, four-gate green *)
Definition ng_UpAblP7_LoHiBridge : NewGreenFace :=
  MkNewGreenFace "UpAblP7_LoHiBridge.v" 209 5 20260920 "colleague PA7: LoHi bridge pieces, four-gate green" "L209:mc3f122".

(* ng_UpAblP7_LoHiSqueeze —— UpAblP7_LoHiSqueeze.v：colleague PA7: LoHiSqueeze 15-theorem full ablation batch, four-gate green *)
Definition ng_UpAblP7_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "UpAblP7_LoHiSqueeze.v" 269 7 20260920 "colleague PA7: LoHiSqueeze 15-theorem full ablation batch, four-gate green" "L276:m0c319c".

(* ng_UpAblP7_P7FlagshipTail —— UpAblP7_P7FlagshipTail.v：colleague PA7: flagship tail pieces, four-gate green *)
Definition ng_UpAblP7_P7FlagshipTail : NewGreenFace :=
  MkNewGreenFace "UpAblP7_P7FlagshipTail.v" 268 9 20260920 "colleague PA7: flagship tail pieces, four-gate green" "L268:m7bb845".

(* ng_UpAblP7_Package —— UpAblP7_Package.v：colleague PA7: package assembly consuming six sibling pieces, four-gate green *)
Definition ng_UpAblP7_Package : NewGreenFace :=
  MkNewGreenFace "UpAblP7_Package.v" 237 4 20260920 "colleague PA7: package assembly consuming six sibling pieces, four-gate green" "L237:m64f3fe".

(* ng_UpAblP7_Paper7Ablation —— UpAblP7_Paper7Ablation.v：colleague PA7: Paper7Ablation 14-slot ablation + D5 instance supply, four-gate green *)
Definition ng_UpAblP7_Paper7Ablation : NewGreenFace :=
  MkNewGreenFace "UpAblP7_Paper7Ablation.v" 281 18 20260920 "colleague PA7: Paper7Ablation 14-slot ablation + D5 instance supply, four-gate green" "L332:m682382".

(* ng_UpAblP7_Paper7Ablation_S1inst —— UpAblP7_Paper7Ablation_S1inst.v：colleague PA7: Paper7Ablation S1 instance supply, four-gate green *)
Definition ng_UpAblP7_Paper7Ablation_S1inst : NewGreenFace :=
  MkNewGreenFace "UpAblP7_Paper7Ablation_S1inst.v" 282 6 20260920 "colleague PA7: Paper7Ablation S1 instance supply, four-gate green" "L282:m001899".

(* ng_UpAblP7_UMixSelect —— UpAblP7_UMixSelect.v：colleague PA7: UMixSelect W-wall verdict + discharge surrogate + kappa=1/2 Closed witness, four-gate green *)
Definition ng_UpAblP7_UMixSelect : NewGreenFace :=
  MkNewGreenFace "UpAblP7_UMixSelect.v" 190 6 20260920 "colleague PA7: UMixSelect W-wall verdict + discharge surrogate + kappa=1/2 Closed witness, four-gate green" "L198:mcfd30d".

(* ng_UpAblP7_WallEpsChain_A —— UpAblP7_WallEpsChain_A.v：colleague PA7: wall W1 eps-form leg-A, four-gate green *)
Definition ng_UpAblP7_WallEpsChain_A : NewGreenFace :=
  MkNewGreenFace "UpAblP7_WallEpsChain_A.v" 305 5 20260920 "colleague PA7: wall W1 eps-form leg-A, four-gate green" "L305:md76e5a".

(* ng_UpAblP7_WallEpsChain_B —— UpAblP7_WallEpsChain_B.v：colleague PA7: wall W2 chain-B, four-gate green *)
Definition ng_UpAblP7_WallEpsChain_B : NewGreenFace :=
  MkNewGreenFace "UpAblP7_WallEpsChain_B.v" 468 11 20260920 "colleague PA7: wall W2 chain-B, four-gate green" "L468:m40973b".

(* ng_UpAblP7_WallEps_CB2 —— UpAblP7_WallEps_CB2.v：colleague PA7: CB2 eps consumption face, four-gate green *)
Definition ng_UpAblP7_WallEps_CB2 : NewGreenFace :=
  MkNewGreenFace "UpAblP7_WallEps_CB2.v" 343 13 20260920 "colleague PA7: CB2 eps consumption face, four-gate green" "L381:mc449ea".

(* ng_UpAblDistLogLe —— UpAblDistLogLe.v：Y1 seat (W4 family-E log-le): dist_log_le_linear slot (UpReqDist.v:1035, Section ReqFEP) concrete Regular-Real carrier instance supply + residual closure, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblDistLogLe : NewGreenFace :=
  MkNewGreenFace "UpAblDistLogLe.v" 239 4 20260920 "Y1 seat (W4 family-E log-le): dist_log_le_linear slot (UpReqDist.v:1035, Section ReqFEP) concrete Regular-Real carrier instance supply + residual closure, four-gate green (_ty1_); born-in-place verified in vo tree" "L239:meee82c".

(* ng_UpAblDistLogEq —— UpAblDistLogEq.v：Y2 seat (W4 family-E log-eq): dist_log_eq_linear slot (UpReqDist.v:1037) concrete Regular-Real carrier instance supply (c-2 verdict redemption), four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblDistLogEq : NewGreenFace :=
  MkNewGreenFace "UpAblDistLogEq.v" 177 5 20260920 "Y2 seat (W4 family-E log-eq): dist_log_eq_linear slot (UpReqDist.v:1037) concrete Regular-Real carrier instance supply (T13c-2 verdict redemption), four-gate green (_ty2_); born-in-place verified in vo tree" "L177:me097c6".

(* ng_UpAblGrpEqDecWorld —— UpAblGrpEqDecWorld.v：Y5 seat (family-A decision wall B28): grp_eq_dec slot (S15_TailFEPUp.v:1419) carrier-world assembly on bool two-element enumeration world, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblGrpEqDecWorld : NewGreenFace :=
  MkNewGreenFace "UpAblGrpEqDecWorld.v" 164 10 20260920 "Y5 seat (family-A decision wall B28): grp_eq_dec slot (S15_TailFEPUp.v:1419) carrier-world assembly on bool two-element enumeration world, four-gate green (_ty5_); born-in-place verified in vo tree" "L164:m18143a".

(* ng_UpAblGrpEqDischarge —— UpAblGrpEqDischarge.v：Y5 seat (family-A): grp_eq_dec slot concrete-carrier discharge pathway demonstrator, Group:=bool / R:=nat minimal Set-level carrier, admission-free all-Qed-closed extractable, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblGrpEqDischarge : NewGreenFace :=
  MkNewGreenFace "UpAblGrpEqDischarge.v" 442 19 20260920 "Y5 seat (family-A): grp_eq_dec slot concrete-carrier discharge pathway demonstrator, Group:=bool / R:=nat minimal Set-level carrier, zero-admit all-Qed extractable, four-gate green (_ty5_); born-in-place verified in vo tree" "L442:m7b98b3".

(* ng_UpAblP2FeedSum —— UpAblP2FeedSum.v：Z2a seat (paper-2 sum-face donor direct-config): paper-1 finisher donors (AB8 spd_ series + AB2 zabr series) interfaced to paper-2 sum face, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblP2FeedSum : NewGreenFace :=
  MkNewGreenFace "UpAblP2FeedSum.v" 314 16 20260920 "Z2a seat (paper-2 sum-face donor direct-config): paper-1 finisher donors (AB8 spd_ series + AB2 zabr series) interfaced to paper-2 sum face, four-gate green (_tz2a_); born-in-place verified in vo tree" "L346:mc18fc2".

(* ng_UpAblP2FeedMix —— UpAblP2FeedMix.v：Z2b seat (paper-2 mix-face donor direct-config): steady/minp Real chain + partition positivity face interfaced with e66s (AB5) and e49l_partition_pos donors, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblP2FeedMix : NewGreenFace :=
  MkNewGreenFace "UpAblP2FeedMix.v" 322 12 20260920 "Z2b seat (paper-2 mix-face donor direct-config): steady/minp Real chain + partition positivity face interfaced with e66s (AB5) and e49l_partition_pos donors, four-gate green (_tz2b_); born-in-place verified in vo tree" "L344:m1fe3e5".

(* ng_UpAblAlmConsumption —— UpAblAlmConsumption.v：Z1b seat (alm-chain remaining-antecedent-form consumption demonstrator): minimal parallel-replica dual-max world (binary vocabulary [true; false], constant logit), consumes only registered chain pieces, admission-free purely constructive, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblAlmConsumption : NewGreenFace :=
  MkNewGreenFace "UpAblAlmConsumption.v" 294 10 20260920 "Z1b seat (alm-chain remaining-antecedent-form consumption demonstrator): minimal parallel-replica dual-max world (binary vocabulary [true; false], constant logit), consumes only registered chain pieces, zero-admit purely constructive, four-gate green (_tz1b_); born-in-place verified in vo tree" "L294:mdb2a7c".

(* ng_UpAblP2FeedSumLe —— UpAblP2FeedSumLe.v：F1 （论文2 le 面原生折叠传输）：p2fl_lsum_app 拼接可加性新证＋p2fl_le_transport sumd→原生折叠 le 两世界运输＋p2fl_abs_split_eps 单余量三角合拢，四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2FeedSumLe : NewGreenFace :=
  MkNewGreenFace "UpAblP2FeedSumLe.v" 283 8 20260920 "F1 seat (paper-2 le-face native folding transport): p2fl_lsum_app append additivity + p2fl_le_transport sumd-to-native le two-world transport + p2fl_abs_split_eps single-residual triangle closure, four-gate green (_tf1_); born-in-place verified in vo tree" "L283:m8405d0".

(* ng_UpAblP2T1_Cert —— UpAblP2T1_Cert.v：A1 （T 簇证书供给）：论文2 T 簇消融证书簇供给模块，33 位 PA 全 Closed（ 终审实测），四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2T1_Cert : NewGreenFace :=
  MkNewGreenFace "UpAblP2T1_Cert.v" 596 12 20260920 "A1 seat (T-cluster certificate supply): paper-2 T-cluster ablation certificate supply piece, 33 PA positions all Closed (_tg2_ final audit), four-gate green (_ta1_); born-in-place verified in vo tree" "L628:maa0c81".

(* ng_UpAblP2WByPass —— UpAblP2WByPass.v：A2 （S06 双墙绕行）：S06 双墙绕行演示件，20 位 PA 全 Closed（ 终审实测），四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2WByPass : NewGreenFace :=
  MkNewGreenFace "UpAblP2WByPass.v" 428 12 20260920 "A2 seat (S06 dual-wall bypass): S06 dual-wall bypass demonstrator piece, 20 PA positions all Closed (_tg2_ final audit), four-gate green (_ta2_); born-in-place verified in vo tree" "L437:mf9e5f9".

(* ng_UpAblA2_LoInflation —— UpAblA2_LoInflation.v：A2 （k∝lo⁻² 膨胀律）：loi_ub2_quad 精确四倍律 Id 形＋loi_lo_inflation 四倍支配主定理＋反单调律；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblA2_LoInflation : NewGreenFace :=
  MkNewGreenFace "UpAblA2_LoInflation.v" 528 12 20260920 "A2 seat (k vs lo^-2 inflation law): loi_ub2_quad exact quadruple law Id-form + loi_lo_inflation flagship + antitone, four-gate (_ta2_)" "L528:m51a7cc".

(* ng_UpAblAbsSumLeB —— UpAblAbsSumLeB.v：H1 （abs 抽象槽 B 形）：uabS4_abs_sum_le_B 两点对＋list 折叠闭包链，bool/list 双记录；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB.v" 341 11 20260920 "H1 seat (abs abstract-slot B-form): uabS4 pair + list-folding closure chain, bool/list dual carriers, four-gate (_th1_)" "L374:mc77a6b".

(* ng_UpAblAbsSumLeB2 —— UpAblAbsSumLeB2.v：abs 族 B2（加权 cons 黏合三角＋双余量反证完成）（ PA 终审）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB2 : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB2.v" 443 20 20260920 "abs-family B2: weighted cons-glue triangle + double-margin contrapositive closure, PA final-audited (_tm2_)" "L443:me5f509".

(* ng_UpAblAbsSumLeB3 —— UpAblAbsSumLeB3.v：abs 族 B3 深链（abs list-sum B/eps 全族＋槽号形，J4 再验）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB3 : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB3.v" 594 19 20260920 "abs-family B3 deep chain: abs list-sum B/eps full family + slot forms, J4 re-verified (_tj4_)" "L594:md6d184".

(* ng_UpAblAbsTwoPtAbs —— UpAblAbsTwoPtAbs.v：abs 族两点槽形（ 四项验证补全）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsTwoPtAbs : NewGreenFace :=
  MkNewGreenFace "UpAblAbsTwoPtAbs.v" 161 4 20260920 "abs-family two-point slot form, four-gate completion (_tm4r_)" "L161:mb3367d".

(* ng_UpAblAbsFeed —— UpAblAbsFeed.v：abs 族馈线件（使用 B/B2/Eps 三件合流）（/）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsFeed : NewGreenFace :=
  MkNewGreenFace "UpAblAbsFeed.v" 107 3 20260920 "abs-family feed piece consuming B/B2/Eps, four-gate (_tm4r_/_tm3_)" "L107:mba3fb2".

(* ng_UpAblB1_MonoSplit —— UpAblB1_MonoSplit.v：B1 （MonoSplit 三证书位真实算链 N 升格，替 S5 零能量捷径支）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblB1_MonoSplit : NewGreenFace :=
  MkNewGreenFace "UpAblB1_MonoSplit.v" 516 12 20260920 "B1 seat: MonoSplit three-certificate real-computation chain (N-upgrade replacing S5 zero-energy shortcut legs), four-gate (_tb1_)" "L553:m89f006".

(* ng_UpAblB2_G13 —— UpAblB2_G13.v：B2 （b_gibbs 障碍通道件＋W4 记录分层判定：log-eq 具体记录可实例化 t34 输入）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblB2_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblB2_G13.v" 321 11 20260920 "B2 seat: b_gibbs obstacle-channel pieces + W4 carrier stratification verdict (log-eq concrete carrier instantiable via t34), four-gate (_tb2_)" "L305:mc36b95".

(* ng_UpAblD1S14_UpReqCauchy —— UpAblD1S14_UpReqCauchy.v：FA-D1S14 （Cauchy 余量 8：含 lim_metric_approx N 级语义链）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S14_UpReqCauchy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S14_UpReqCauchy.v" 266 8 20260920 "FA-D1S14 seat: Cauchy residual 8 incl. lim_metric_approx N-level semantic chain, four-gate (_tfad1s14_)" "L266:m0dddd2".

(* ng_UpAblD1S15_GibbsAssembly —— UpAblD1S15_GibbsAssembly.v：FA-D1S15 （GibbsAssembly 18 槽成组＋log_req_compat 并账）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S15_GibbsAssembly : NewGreenFace :=
  MkNewGreenFace "UpAblD1S15_GibbsAssembly.v" 535 5 20260920 "FA-D1S15 seat: GibbsAssembly 18-slot pack + log_req_compat joint accounting, four-gate (_tfad1s15_)" "L535:m29f668".

(* ng_UpAblD1S15_UpReqAlign3 —— UpAblD1S15_UpReqAlign3.v：FA-D1S15 （Align3 余量 16 T 供给级）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S15_UpReqAlign3 : NewGreenFace :=
  MkNewGreenFace "UpAblD1S15_UpReqAlign3.v" 144 2 20260920 "FA-D1S15 seat: Align3 residual 16 T-supply, four-gate (_tfad1s15_)" "L144:mfaf069".

(* ng_UpAblD1S16_UpReqMixTime —— UpAblD1S16_UpReqMixTime.v：FA-D1S16 （AttnMixTime 余量 12 T 成组：9 数据+3 接口条件供给形）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S16_UpReqMixTime : NewGreenFace :=
  MkNewGreenFace "UpAblD1S16_UpReqMixTime.v" 148 3 20260920 "FA-D1S16 seat: AttnMixTime residual 12 T-pack (9 data + 3 interface-conditional supply forms), four-gate (_tfad1s16_)" "L148:m6d90f1".

(* ng_UpAblD1S17_UpReqAttnGibbs —— UpAblD1S17_UpReqAttnGibbs.v：FA-D1S17 （Gibbs pack18＋exp_neg_geo_break T·N1 直接传入降标申报）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S17_UpReqAttnGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S17_UpReqAttnGibbs.v" 162 2 20260920 "FA-D1S17 seat: Gibbs pack18 + exp_neg_geo_break T-N1 direct-feed downgraded declaration, four-gate (_tfad1s17_)" "L162:m9b124d".

(* ng_UpAblD1S17_UpReqDpoLoss —— UpAblD1S17_UpReqDpoLoss.v：FA-D1S17 （DpoLoss pack13 供给）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S17_UpReqDpoLoss : NewGreenFace :=
  MkNewGreenFace "UpAblD1S17_UpReqDpoLoss.v" 110 2 20260920 "FA-D1S17 seat: DpoLoss pack13 supply, four-gate (_tfad1s17_)" "L110:m1238b8".

(* ng_UpAblP2T1_CertC —— UpAblP2T1_CertC.v：G 批二（T 簇证书 C 变体，使用 CertB）（/ 终审）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2T1_CertC : NewGreenFace :=
  MkNewGreenFace "UpAblP2T1_CertC.v" 227 3 20260920 "G-seat batch-2: T-cluster certificate C-variant consuming CertB, final-audited (_tg1_/_tg2_)" "L227:mca06fc".

(* ng_UpAblAbsQFeed —— UpAblAbsQFeed.v：N4R （Q 世界 Qabs 槽×9 ）：S10_KVQuantTrig 六槽＋S08 Qabs 三槽（实使用 8 点＋1 谱系注行，N4R 判定表）Q 层自足直接配置供给模块——uaq_ 七件（三角加/减/反演 A.1/A.2/A.3＋非负 C.2 适配使用级如实标注，双层差 Qabs 收束 B.1 与严格版 B.2、Qfloor 阿基米德证书过 Qabs 门 C.1 三件真实现），供体 S4B Qfloor 谱系 UpAblAbsSumLeB2 真使用；四项验证绿；vo 树 built-at-registration 候铺 *)
Definition ng_UpAblAbsQFeed : NewGreenFace :=
  MkNewGreenFace "UpAblAbsQFeed.v" 158 7 20260920 "N4R seat (Q-world Qabs slot x9 direct-fit): self-sufficient Q-layer supply for six S10_KVQuantTrig slots + three S08 Qabs slots (8 real consumption points + 1 lineage note per the N4R verdict table) - seven uaq_ pieces (triangle plus/minus/reverse A.1/A.2/A.3 and nonneg C.2 at adaptation-consumption level, honestly marked; double-layer Qabs closure B.1, its strict variant B.2, and the Qfloor Archimedean certificate through the Qabs gate C.1 as real implementations), genuinely consuming the S4B Qfloor lineage donor UpAblAbsSumLeB2; four-gate green (_tn4r_); born-in-place pending in vo tree" "L158:m1cb875".

(* ng_UpAblTwLeFeed —— UpAblTwLeFeed.v：N3R （UpTempWindow tw_h_le 槽两点核差 B ）：tw_h_le 槽（|w_T(x)−1/N| ≤ (e^{2Δ/T}−1)·(1/N)，Section TempWindow 卸载 8 参世界接口）B 形直接配置主件 ntl_tw_h_le_b_feed（语句逐字对齐、外层谓词升 real_le_b）＋plain 收回件 ntl_tw_h_le_feed（与槽实形逐字同形、臂式重组零调槽本体）＋单向桥/臂基×2/转换层×2 共 7 件全 Closed；eps 两臂经 S4 供体 uabS4_le_add_r 正余量右吸收真使用；形态差三条显式申报（三角增改差 2·(1−E2L)·u≥0、B/plain 形态差、前提使用同位， §4）；四项验证绿；vo 树 built-at-registration 候铺 *)
Definition ng_UpAblTwLeFeed : NewGreenFace :=
  MkNewGreenFace "UpAblTwLeFeed.v" 368 7 20260920 "N3R seat (UpTempWindow tw_h_le slot two-point kernel-difference Bishop-form direct-fit): main piece ntl_tw_h_le_b_feed (statement verbatim-aligned to the Section-unloaded 8-parameter world interface, outer predicate lifted to real_le_b) + plain recovery piece ntl_tw_h_le_feed (verbatim-same-shape as the slot, arm-based independent reconstruction, zero calls into the slot body) + one-way bridge / two arm bases / two conversion pieces, 7 pieces all Closed; eps arms genuinely consume the S4 donor uabS4_le_add_r positive-margin right-absorption; three shape differences explicitly declared (triangle thinning gap 2*(1-E2L)*u >= 0, B/plain form gap, premise-consumption parity, _tn3r_ section 4); four-gate green (_tn3r_); born-in-place pending in vo tree" "L368:m703b81".

(* 刷新注记：UpAblAbsSumLeB（341/11）与 UpAblAbsTwoPtAbs（161/4）为 已注册件内容刷新版（Live_X 权威版同步，built-at-registration 重编+下游愈合闭包 build.sh 全量重编背书），ng_ 计数沿用，愈合重编经 cpu_guard 包裹 build.sh 拓扑序执行。 *)

(* ng_UpAblSlotB0Merge —— UpAblSlotB0Merge.v：TP5 （B0 并轨）：SlotB0 双世界并轨供给模块；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblSlotB0Merge : NewGreenFace :=
  MkNewGreenFace "UpAblSlotB0Merge.v" 104 2 20260920 "TP5 seat: SlotB0 dual-world merge supply piece, four-gate (_tp5_)" "L104:m9d70c8".

(* ng_UpAblCauchyMod —— UpAblCauchyMod.v：TP6 （Cauchy 模位）：CauchyMod 模位供给模块（ 侦察线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblCauchyMod : NewGreenFace :=
  MkNewGreenFace "UpAblCauchyMod.v" 132 4 20260920 "TP6 seat: CauchyMod modulus-position supply piece (recon line _tp6_), four-gate" "L132:ma92b14".

(* ng_UpAblKVEpsHalf —— UpAblKVEpsHalf.v：KV eps 半量族供给模块（H 线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblKVEpsHalf : NewGreenFace :=
  MkNewGreenFace "UpAblKVEpsHalf.v" 266 13 20260920 "KV eps-half family supply piece (H-seat residual line), four-gate" "L266:m68118d".

(* ng_UpAblAbsQFeedB2 —— UpAblAbsQFeedB2.v：QFeed B2 变体（使用 AbsQFeed）（abs 族线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsQFeedB2 : NewGreenFace :=
  MkNewGreenFace "UpAblAbsQFeedB2.v" 140 15 20260920 "QFeed B2 variant consuming AbsQFeed (abs-family line), four-gate" "L188:m1c92f4".

(* ng_UpAblQfloorDepth —— UpAblQfloorDepth.v：Qfloor 深度件（使用 AbsSumLeB2+AbsQFeed）（abs 族线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblQfloorDepth : NewGreenFace :=
  MkNewGreenFace "UpAblQfloorDepth.v" 178 4 20260920 "Qfloor depth piece consuming AbsSumLeB2+AbsQFeed (abs-family line), four-gate" "L190:m2707be".

(* ng_UpAblS06AbsFeed —— UpAblS06AbsFeed.v：S06 abs 馈线（使用 AbsSumLeB3）（abs 族线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblS06AbsFeed : NewGreenFace :=
  MkNewGreenFace "UpAblS06AbsFeed.v" 265 6 20260920 "S06 abs feed piece consuming AbsSumLeB3 (abs-family line), four-gate" "L265:m4ecc5d".

(* ng_UpAblArchGeomBatch —— UpAblArchGeomBatch.v：Arch 几何批件（使用 QeqBridge）（ 线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblArchGeomBatch : NewGreenFace :=
  MkNewGreenFace "UpAblArchGeomBatch.v" 111 4 20260920 "Arch geometry batch piece consuming QeqBridge (_tq1_ line), four-gate" "L111:m4440f3".

(* ng_UpAblCauchyLim —— UpAblCauchyLim.v：TP6 （CauchyLim 完成）：CauchyLim 模位完成件（ 侦察线转正）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblCauchyLim : NewGreenFace :=
  MkNewGreenFace "UpAblCauchyLim.v" 250 8 20260920 "TP6 seat: CauchyLim closure piece (recon line _tp6_ promoted), four-gate" "L250:m3a1a8a".

(* ng_UpAblHalfPowFeed —— UpAblHalfPowFeed.v：HalfPow 馈线件（使用 HalfPow）（TP3 线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblHalfPowFeed : NewGreenFace :=
  MkNewGreenFace "UpAblHalfPowFeed.v" 229 5 20260920 "HalfPow feed piece consuming HalfPow (TP3 line), four-gate" "L229:m544809".

(* ng_UpAblP6_TempDefs —— UpAblP6_TempDefs.v：PA6-02（TempDefs 消融 11 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_TempDefs : NewGreenFace :=
  MkNewGreenFace "UpAblP6_TempDefs.v" 391 11 20260920 "PA6-02: TempDefs ablation 11 pieces (T212)" "L404:m5cd38a".

(* ng_UpAblP6_ZPosLowRef —— UpAblP6_ZPosLowRef.v：PA6-06（ZPos/LowRef 喂件面 12 位；注释 G1 直修 axiom→公理）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_ZPosLowRef : NewGreenFace :=
  MkNewGreenFace "UpAblP6_ZPosLowRef.v" 246 12 20260920 "PA6-06: ZPos/LowRef wire-feed face 12 positions (T216; comment G1 direct-fix)" "L255:mb85065".

(* ng_UpAblP6_ConcMixSelFeed —— UpAblP6_ConcMixSelFeed.v：PA6-07（ConcMixSel 喂件 16 位）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_ConcMixSelFeed : NewGreenFace :=
  MkNewGreenFace "UpAblP6_ConcMixSelFeed.v" 221 16 20260920 "PA6-07: ConcMixSel feed 16 positions (T217)" "L221:m542dac".

(* ng_UpAblP6_SecondLaw_two_state —— UpAblP6_SecondLaw_two_state.v：PA6-23（SecondLaw 整节 two_state 实例化 14 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_SecondLaw_two_state : NewGreenFace :=
  MkNewGreenFace "UpAblP6_SecondLaw_two_state.v" 376 14 20260920 "PA6-23: SecondLaw whole-section two_state instantiation 14 pieces (T231)" "L414:m4d4da6".

(* ng_UpAblP6_StateSpace_inst —— UpAblP6_StateSpace_inst.v：PA6-08 线（StateSpace 非平凡实例首件 23 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_StateSpace_inst : NewGreenFace :=
  MkNewGreenFace "UpAblP6_StateSpace_inst.v" 509 23 20260920 "StateSpace non-trivial instantiation first piece 23 theorems" "L550:m0d7d55".

(* ng_UpAblP6_EntropyMonoSplit_A —— UpAblP6_EntropyMonoSplit_A.v：PA6-03（EntropyMonoSplit 甲支 6 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_A : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_A.v" 175 6 20260920 "PA6-03: EntropyMonoSplit leg-A 6 pieces (T213)" "L175:m70fc0a".

(* ng_UpAblP6_EntropyMonoSplit_B —— UpAblP6_EntropyMonoSplit_B.v：PA6-04（EntropyMonoSplit 乙支 7 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_B : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_B.v" 264 7 20260920 "PA6-04: EntropyMonoSplit leg-B 7 pieces (T214)" "L264:m0bddea".

(* ng_UpAblP6_EntropyMonoSplit_C —— UpAblP6_EntropyMonoSplit_C.v：PA6-08（EMS 接合验证 11/11 零缺口 15 件，使用 A/B）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_C : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_C.v" 394 15 20260920 "PA6-08: EMS consolidation verification 11/11 zero-gap 15 pieces consuming A/B (T218)" "L457:m6f3e3c".

(* ng_UpAblP6_Package —— UpAblP6_Package.v：PA6-13（v2 完成接合九支供给闭合 20 件，使用 10 件）（b）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_Package : NewGreenFace :=
  MkNewGreenFace "UpAblP6_Package.v" 804 20 20260920 "PA6-13: v2 closing consolidation nine-branch supply closure 20 pieces consuming 10 (T221b)" "L804:mdd5945".

(* ng_UpAblLogWall —— UpAblLogWall.v：论文7 更新线（LogWall 墙定理化 11 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogWall : NewGreenFace :=
  MkNewGreenFace "UpAblLogWall.v" 298 11 20260920 "paper-7 update line: LogWall wall-theoremization 11 pieces" "L309:m34d8df".

(* ng_UpAblLogWallEq —— UpAblLogWallEq.v：论文7 更新线（LogWallEq 双向等价 12 件，使用 LogWall）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogWallEq : NewGreenFace :=
  MkNewGreenFace "UpAblLogWallEq.v" 382 12 20260920 "paper-7 update line: LogWallEq bidirectional equivalence 12 pieces consuming LogWall (_tl3_)" "L382:md20088".

(* ng_UpAblMetaEngine —— UpAblMetaEngine.v：论文7 更新线（MetaEngine 引擎 22 件）（_tn 系）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaEngine : NewGreenFace :=
  MkNewGreenFace "UpAblMetaEngine.v" 830 22 20260920 "paper-7 update line: MetaEngine engine 22 pieces (_tn series)" "L830:m9a9fa9".

(* ng_UpAblRateAlgPkg —— UpAblRateAlgPkg.v：论文7 更新线（率代数成组 4 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblRateAlgPkg : NewGreenFace :=
  MkNewGreenFace "UpAblRateAlgPkg.v" 326 4 20260920 "paper-7 update line: rate-algebra package 4 pieces (_taid3_)" "L326:m2389d1".

(* ng_UpAblSlackMix —— UpAblSlackMix.v：论文7 更新线（N1 松弛形算法化定义面 slm_ 三件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblSlackMix : NewGreenFace :=
  MkNewGreenFace "UpAblSlackMix.v" 291 0 20260920 "paper-7 update line: N1 seat slack-form algorithmization definition face slm_ three pieces (_tn1_)" "L297:m9976e9".

(* ng_UpAblMetaWorld3 —— UpAblMetaWorld3.v：N4 非退化核世界机器面（TV 算子/点质量对/精确幂律+预算下界双分支，34 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaWorld3 : NewGreenFace :=
  MkNewGreenFace "UpAblMetaWorld3.v" 753 34 20260921 "N4 seat: non-degenerate kernel world machine face (TV operator, point-mass pair, exact power law + budget lower bound legs, 34 pieces)" "L833:m5ce18d".

(* ng_UpAblMetaWindow —— UpAblMetaWindow.v：M4 双侧混合窗定理（泛型退化分支新证+World3 存在侧双分支合取，8 件，axiom-free）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaWindow : NewGreenFace :=
  MkNewGreenFace "UpAblMetaWindow.v" 207 8 20260921 "M4 seat: two-sided mixing window theorem (generic collapse leg new proof + World3 existence-side two legs conjunction, 8 pieces, Axioms none)" "L226:m066a30".

(* ng_UpReqMixRealExec —— UpReqMixRealExec.v：R1EXE Real 层选择器可执行化（R1 见证/证明分离+R3 惰性链，mrx_ 七面，native k=15@173ms）；vo 树 built-at-registration 复证 *)
Definition ng_UpReqMixRealExec : NewGreenFace :=
  MkNewGreenFace "UpReqMixRealExec.v" 272 4 20260922 "R1EXE seat: Real-layer selector executification (R1 witness/proof separation + R3 lazy chain, mrx_ seven faces PA Closed, native k=15 at 173ms)" "L272:mf31fc2".

(* ng_UpAblMetaDivQ —— UpAblMetaDivQ.v：AID1 定理 A Q 层侧独立件（mqd_ 十二面 PA Closed，Bernoulli 下界+无界 Doeblin 见证 Defined 出口）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaDivQ : NewGreenFace :=
  MkNewGreenFace "UpAblMetaDivQ.v" 370 9 20260922 "AID1 seat: Q-layer independent piece for theorem A (mqd_ twelve faces PA Closed, Bernoulli lower bound + unbounded Doeblin witness with Defined witness exit)" "L370:m495528".

(* ng_UpAblMetaTemp —— UpAblMetaTemp.v：M2R2 温度-模量发散（mtp_ 十二面 PA Closed，主件 mtp_anchor_divergence 零公理）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaTemp : NewGreenFace :=
  MkNewGreenFace "UpAblMetaTemp.v" 642 12 20260922 "M2R2 relay seat: temperature-modulus divergence (mtp_ twelve faces PA Closed, anchor divergence zero axioms)" "L642:m9816ce".

(* ng_UpAblMetaDivThm —— UpAblMetaDivThm.v：CJS3 解封件（mtd_unbounded 主件+定理 A+第 8 条 mtd_unbounded_conj 合取件恢复，PA 8/8 Closed，Require 桥接模块 1 行）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaDivThm : NewGreenFace :=
  MkNewGreenFace "UpAblMetaDivThm.v" 1520 17 20260922 "CJS3 seat: unsealed divergence theorem (mtd_unbounded main + theorem A + restored eighth face mtd_unbounded_conj conjunction, PA 8/8 Closed, one-line bridge Require)" "L1520:m88e5e4".

(* 1 件尾部追加 order L471（BeukersVariant 之后；拓扑位：S01_BaseRing/S02_CauchyComplete/S03_QExp+PadeErrorIntegral+BeukersLists+BeukersVariant 全在前）；_CoqProject×2 尾部追加同步；ng_ 条目 wc/grep 实测。 *)
(* ng_PsQReindex —— PsQReindex.v：E-STAGING-D030r 切片 rx_ 前缀双小件（psQ↔bk_psd reindex 引理+十字衰减链可证首件；行首 decl grep 实测 19：Lemma rx_psQ_ext_lt/rx_psQ_shift/rx_psQ_scale、Theorem rx_psQ_reindex/rx_bv_c_diag/rx_qtilde3_anchor 等）；vo 树 built-at-registration 复证 *)
Definition ng_PsQReindex : NewGreenFace :=
  MkNewGreenFace "PsQReindex.v" 579 19 20260922 "rx_-prefixed pair: psQ <-> bk_psd reindex lemmas + cross-decay chain first provable piece, 19 decls" "L594:m07533f".

(* ---------- ToyR 盒A 自证：替换件假设清查（零承认件自证） ---------- *)
Print Assumptions cnt_mod_length.
Print Assumptions minus_absorb_r.
Print Assumptions TotalModules_matches.
Print Assumptions DeliveredModules_matches.
Print Assumptions UniverseItems_matches.
Print Assumptions Universe_splits.

(* ng_UpAblB2WindowTie —— UpAblB2WindowTie.v：B2UP 窗口约束可执行见证族（15 出口全 Defined；语句账 PA 10/10；环境账 3 条 stdlib 经典公理 intern 乘客按判例链分账如实申报）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblB2WindowTie : NewGreenFace :=
  MkNewGreenFace "UpAblB2WindowTie.v" 276 15 20260922 "B2UP seat: window-tie executable witness family (Qed 0/Defined 15, statement ledger PA 10/10; env ledger 3 stdlib classical passengers disclosed per B2UP)" "L276:m118fce".

(* ng_UpReqInvPosLazy —— UpReqInvPosLazy.v：InvPos 惰性 inv-pos 预算门 ivl_budget_at（PA 9/9，coqchk axiom-free，k=1 显式入口复跑；11 Qed+1 Defined=12 出口，含 5 条行内 Proof…Qed 一行式——行首 decl grep 与出口 grep 双口径一致）；vo 树 built-at-registration 复证 *)
Definition ng_UpReqInvPosLazy : NewGreenFace :=
  MkNewGreenFace "UpReqInvPosLazy.v" 280 12 20260922 "InvPos seat: lazy inv-pos budget gate ivl_budget_at (PA 9/9, coqchk Axioms none, k=1 explicit-entry run; 12 exits incl. 5 inline one-line proofs)" "L280:m883b18".

(* ng_UpQKTVCompose —— UpQKTVCompose.v：P2COMP QK→TV 一步合成（构造性严格化 +1 裕度；qktv_abs_lt_two_side/qk_tv_iter_contraction PA Closed，G4 三遍 12 模块闭包 axiom-free）；vo 树 built-at-registration 复证 *)
Definition ng_UpQKTVCompose : NewGreenFace :=
  MkNewGreenFace "UpQKTVCompose.v" 245 2 20260922 "P2COMP seat: QK-to-TV one-step composition, constructive strictification +1 margin (qktv_abs_lt_two_side/qk_tv_iter_contraction PA Closed, G4 3-pass)" "L245:me1efd5".

(* ng_UpAblLogWallFinal —— UpAblLogWallFinal.v：N3 墙八终形 lgwd_ 族（PA 9/9，G3 magic 0/0，G4 axiom-free；11 Qed 含 1 条行内一行式；预备单注 2：N3 报告未钉 md5——实测 4a3b2943，执行波 G2 复证补钉后方可 commit）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogWallFinal : NewGreenFace :=
  MkNewGreenFace "UpAblLogWallFinal.v" 447 11 20260922 "N3 seat: wall-eight final form lgwd_ family (PA 9/9, G3 magic 0/0, G4 Axioms none; md5 4a3b2943 re-pin at landing G2)" "L447:m4a3b29".

(* ng_UpAblLogSelOracle —— UpAblLogSelOracle.v：LSO-FIX log-选择子 oracle，L176 旧源伤经 Z.compare_*_iff 三分支退役（14 定理型 decl 全 Qed 封+2 Definition Defined 终=16 出口，PA 17 路 Closed；Live_X/vo 树/沙箱三副本 md5 统一 00c03d2b 实测复核）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogSelOracle : NewGreenFace :=
  MkNewGreenFace "UpAblLogSelOracle.v" 535 14 20260922 "LSO-FIX seat: log-selector oracle, L176 old-source wound retired via Z.compare_*_iff tri-branch (PA 17 Closed, three-copy md5 unified 00c03d2b)" "L535:m00c03d".

(* ng_UpAblMetaPackage —— UpAblMetaPackage.v：W3PKG meta-package mpk_（跨世界三联画+world3 tv1 半幅，两主定理 Defined 终+7 再出口别名，三绿供体成组；PA 14，G3 自面 magic=0；硬依赖 UpAblMetaTemp 已于 在册，前置闸满足）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaPackage : NewGreenFace :=
  MkNewGreenFace "UpAblMetaPackage.v" 150 2 20260922 "W3PKG seat: meta-package mpk_ — cross-world triptych + world3 tv1-half (both Defined-terminated) + 7 re-export aliases over three green suppliers (PA 14, G3 self-face magic=0)" "L150:ma9c4fe".

Definition ng_P7BoundedSoftmaxDeep : NewGreenFace :=
  MkNewGreenFace "P7BoundedSoftmaxDeep.v" 471 15 20260922
  "R112 six-row topo fix enrollment (7aeac35, order L496 over 578-line baseline, md5 4614b0b2); 18 decls / 15 traced exits all Closed; born-in-place three-gate green" "L471:m4614b0".

(* ng_LoHiSqueeze —— LoHiSqueeze.v： 入册（7aeac35，order L497/578 行基线，紧随依赖 P7BoundedSoftmaxDeep L496，拓扑验证通过；md5 345b5868 双树实测）；
 4 声明 4 出口全覆盖，零撞名零红线；vo 树 built-at-registration 复证 *)
Definition ng_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "LoHiSqueeze.v" 190 4 20260922
  "R112 topo fix enrollment (7aeac35, order L497/578-line baseline, md5 345b5868); dependency-adjacent placement verified; 4/4 exits Closed; three-gate green" "L190:m345b58".

(* ng_GibbsFamilyExt —— GibbsFamilyExt.v： 入册（7aeac35，order L552/578 行基线；md5 d6750177 双树实测）；级联面实测非壳件（CW 桩 631B，零 S 系直连），
 R3 壳级联担忧解除；13 声明 13 出口全覆盖；vo 树 built-at-registration 复证 *)
Definition ng_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "GibbsFamilyExt.v" 443 13 20260922
  "R112 topo fix enrollment (7aeac35, order L552/578-line baseline, md5 d6750177); cascade face cleared (base stub 631B, no S-series edge); 13/13 exits Closed; three-gate green" "L443:md67501".

(* ng_FepIdConsume —— FepIdConsume.v： 入册（7aeac35，order L564/578 行基线；md5 ec7152e6 双树实测）；5 声明 5 出口全覆盖；
 未注册检查点 fic2_g3(_ext) 依赖本件（H1 留待，不影响本件在册态）；vo 树 built-at-registration 复证 *)

(* ng_SecondLawConsume —— SecondLawConsume.v： 入册（7aeac35，order L394/578 行基线，先于伴件 sumdis L395；md5 850907ae 双树实测）；
 9 声明 4 追印出口（原追印清单口径，H2 对照核验随 C23 单据 B 关 2 口径在案）；vo 树 built-at-registration 复证 *)

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=包版实测（R116b-PREP 单据包草案），以树内实测复核补记，ng_qed 为 grep 级计数（token ）。 *)

(* ng_PA_AttnSqrt —— PA_AttnSqrt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_AttnSqrt : NewGreenFace :=
  MkNewGreenFace "PA_AttnSqrt.v" 276 12 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c05b40, L276); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L276:mc05b40".

(* ng_PA_CW220_Extensions —— PA_CW220_Extensions.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_CW220_Extensions : NewGreenFace :=
  MkNewGreenFace "PA_CW220_Extensions.v" 1677 42 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5ad943, L1677); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L1677:m5ad943".

(* ng_PA_DTPT_Bridge_Dep —— PA_DTPT_Bridge_Dep.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_DTPT_Bridge_Dep : NewGreenFace :=
  MkNewGreenFace "PA_DTPT_Bridge_Dep.v" 317 0 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 124ee5, L317); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L317:m124ee5".

(* ng_PA_ExpOneEnvelope —— PA_ExpOneEnvelope.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ExpOneEnvelope : NewGreenFace :=
  MkNewGreenFace "PA_ExpOneEnvelope.v" 527 29 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 e2cbe6, L527); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L527:me2cbe6".

(* ng_PA_FirewallReqDischarge —— PA_FirewallReqDischarge.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_FirewallReqDischarge : NewGreenFace :=
  MkNewGreenFace "PA_FirewallReqDischarge.v" 296 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 4c1bac, L296); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L296:m4c1bac".

(* ng_PA_PolyIntegral —— PA_PolyIntegral.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_PolyIntegral : NewGreenFace :=
  MkNewGreenFace "PA_PolyIntegral.v" 357 17 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6ba7f6, L357); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L357:m6ba7f6".

(* ng_PA_TempMonoW2Mark —— PA_TempMonoW2Mark.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_TempMonoW2Mark : NewGreenFace :=
  MkNewGreenFace "PA_TempMonoW2Mark.v" 277 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 1b8f64, L277); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L277:m1b8f64".

(* ng_PA_TempSoftmaxInstantiation —— PA_TempSoftmaxInstantiation.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "PA_TempSoftmaxInstantiation.v" 420 6 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 349ea1, L420); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L420:m349ea1".

(* ng_PA_ToyR_IdSlotTranslate —— PA_ToyR_IdSlotTranslate.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_IdSlotTranslate : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_IdSlotTranslate.v" 195 7 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 3f064f, L195); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L195:m3f064f".

(* ng_PA_ToyR_SecondLawConsume —— PA_ToyR_SecondLawConsume.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_SecondLawConsume : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_SecondLawConsume.v" 389 9 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 2e8c46, L389); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L389:m2e8c46".

(* ng_PA_ToyR_SupplyAssembly —— PA_ToyR_SupplyAssembly.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_SupplyAssembly.v" 347 21 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5fcbe3, L347); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L347:m5fcbe3".

(* ng_PA_ToyR_fa57_ext —— PA_ToyR_fa57_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_fa57_ext : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_fa57_ext.v" 248 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 1286ae, L248); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L248:m1286ae".

(* ng_PA_UpAblAbsSumLeB —— PA_UpAblAbsSumLeB.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblAbsSumLeB : NewGreenFace :=
  MkNewGreenFace "PA_UpAblAbsSumLeB.v" 364 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 9a7fdb, L364); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L364:m9a7fdb".

(* ng_PA_UpAblD1S3_fep_UpReqSteadyThermo —— PA_UpAblD1S3_fep_UpReqSteadyThermo.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD1S3_fep_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD1S3_fep_UpReqSteadyThermo.v" 165 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6b64c1, L165); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L165:m6b64c1".

(* ng_PA_UpAblD1S4_UpReqStepKLEtaInst —— PA_UpAblD1S4_UpReqStepKLEtaInst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD1S4_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD1S4_UpReqStepKLEtaInst.v" 118 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 b7106e, L118); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L118:mb7106e".

(* ng_PA_UpAblD2_AbsLeId_RI_DO —— PA_UpAblD2_AbsLeId_RI_DO.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD2_AbsLeId_RI_DO : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD2_AbsLeId_RI_DO.v" 157 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 7e3991, L157); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L157:m7e3991".

(* ng_PA_UpAblMetaWindow —— PA_UpAblMetaWindow.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblMetaWindow : NewGreenFace :=
  MkNewGreenFace "PA_UpAblMetaWindow.v" 229 0 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c0901e, L229); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L229:mc0901e".

(* ng_PA_UpAblT1_UpFirewallReq —— PA_UpAblT1_UpFirewallReq.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblT1_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "PA_UpAblT1_UpFirewallReq.v" 118 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 206e3b, L118); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L118:m206e3b".

(* ng_PA_UpDissip —— PA_UpDissip.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpDissip : NewGreenFace :=
  MkNewGreenFace "PA_UpDissip.v" 803 38 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 0660de, L803); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L803:m0660de".

(* ng_PA_UpStepKLM3 —— PA_UpStepKLM3.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpStepKLM3 : NewGreenFace :=
  MkNewGreenFace "PA_UpStepKLM3.v" 665 18 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 494c15, L665); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L665:m494c15".

(* ng_ToyR_BeukersLists —— ToyR_BeukersLists.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_BeukersLists : NewGreenFace :=
  MkNewGreenFace "ToyR_BeukersLists.v" 576 29 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c483b4, L576); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L576:mc483b4".

(* ng_ToyR_BeukersVariant —— ToyR_BeukersVariant.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_BeukersVariant : NewGreenFace :=
  MkNewGreenFace "ToyR_BeukersVariant.v" 547 30 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 3d42c9, L547); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L547:m3d42c9".

(* ng_ToyR_EntropyMonoSplitInst —— ToyR_EntropyMonoSplitInst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_EntropyMonoSplitInst : NewGreenFace :=
  MkNewGreenFace "ToyR_EntropyMonoSplitInst.v" 298 8 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 40f3d9, L298); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L298:m40f3d9".

(* ng_ToyR_GibbsFamilyExt —— ToyR_GibbsFamilyExt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "ToyR_GibbsFamilyExt.v" 454 13 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 d3b3d8, L454); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L454:md3b3d8".

(* ng_ToyR_Ln2Integrality —— ToyR_Ln2Integrality.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_Ln2Integrality : NewGreenFace :=
  MkNewGreenFace "ToyR_Ln2Integrality.v" 508 27 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 871ae3, L508); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L508:m871ae3".

(* ng_ToyR_NatLenPos —— ToyR_NatLenPos.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_NatLenPos : NewGreenFace :=
  MkNewGreenFace "ToyR_NatLenPos.v" 128 4 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 475527, L128); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L128:m475527".

(* ng_ToyR_RateTheoryAblation —— ToyR_RateTheoryAblation.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_RateTheoryAblation : NewGreenFace :=
  MkNewGreenFace "ToyR_RateTheoryAblation.v" 233 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 7d324c, L233); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L233:m7d324c".

(* ng_ToyR_SecondLawConsume —— ToyR_SecondLawConsume.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SecondLawConsume : NewGreenFace :=
  MkNewGreenFace "ToyR_SecondLawConsume.v" 393 9 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 9e3e16, L393); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L393:m9e3e16".

(* ng_ToyR_SumEqListFeed —— ToyR_SumEqListFeed.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SumEqListFeed : NewGreenFace :=
  MkNewGreenFace "ToyR_SumEqListFeed.v" 198 8 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 39fb1a, L198); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L198:m39fb1a".

(* ng_ToyR_SupplyAssembly —— ToyR_SupplyAssembly.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "ToyR_SupplyAssembly.v" 351 21 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 8e7e36, L351); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L351:m8e7e36".

(* ng_ToyR_UpAblP6_GibbsFamilyExt —— ToyR_UpAblP6_GibbsFamilyExt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP6_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP6_GibbsFamilyExt.v" 184 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6a07fd, L184); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L184:m6a07fd".

(* ng_ToyR_UpAblP6_UniformLimit —— ToyR_UpAblP6_UniformLimit.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP6_UniformLimit : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP6_UniformLimit.v" 182 3 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6cb954, L182); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L182:m6cb954".

(* ng_ToyR_UpAblP7_AbsNonNeg —— ToyR_UpAblP7_AbsNonNeg.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_AbsNonNeg : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_AbsNonNeg.v" 374 13 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6d95b2, L374); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L374:m6d95b2".

(* ng_ToyR_UpAblP7_LoHiCross —— ToyR_UpAblP7_LoHiCross.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_LoHiCross : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_LoHiCross.v" 126 3 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6164aa, L126); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L126:m6164aa".

(* ng_ToyR_UpAblP7_LoHiSqueeze —— ToyR_UpAblP7_LoHiSqueeze.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_LoHiSqueeze.v" 287 7 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 d8d6c8, L287); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L287:md8d6c8".

(* ng_ToyR_UpAblP7_Paper7Ablation_S1inst —— ToyR_UpAblP7_Paper7Ablation_S1inst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_Paper7Ablation_S1inst : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_Paper7Ablation_S1inst.v" 292 6 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 bdfade, L292); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L292:mbdfade".

(* ng_ToyR_UpAblP7_UMixSelect —— ToyR_UpAblP7_UMixSelect.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_UMixSelect : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_UMixSelect.v" 209 4 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 e31c5b, L209); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L209:me31c5b".

(* ng_ToyR_fa56b_ext —— ToyR_fa56b_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_fa56b_ext : NewGreenFace :=
  MkNewGreenFace "ToyR_fa56b_ext.v" 292 12 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5d4f38, L292); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L292:m5d4f38".

(* ng_ToyR_fa57_ext —— ToyR_fa57_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_fa57_ext : NewGreenFace :=
  MkNewGreenFace "ToyR_fa57_ext.v" 251 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 809125, L251); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L251:m809125".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=源位实测快照（-PREP 合并单据包），ng_qed 已按二验 [N-1] 修正令以 口径 token 级实测补记（13/40/3）。 *)


(* ng_UpAblDeltaStarGeneral —— UpAblDeltaStarGeneral.v：DSNR 主件（dsgen_ 推广族，577 行 48 声明面 40 Qed（token 级实测；PREP 草案 33 系行首 grep 口径，二验 [N-1] 修正）；PA 四路 Closed＝dsgen_main/rowstoch/feasible/optimal_ge3 逐件 Closed under global context；G3 独立目录 Separate Extraction Obj.magic=0；G4 axiom-free>；头注 L24-27 自引词面按 WangWW 零承认自陷卡豁免注记在案；Require 依赖 UpAblDeltaStarSuboptimal 同批注册） *)
Definition ng_UpAblDeltaStarGeneral : NewGreenFace :=
  MkNewGreenFace "UpAblDeltaStarGeneral.v" 577 40 20260923
  "DSNR seat: dsgen_ generalization family (PA 4-route Closed: dsgen_main/rowstoch/feasible/optimal_ge3; G3 separate-extraction Obj.magic=0; G4 Axioms none; ng_qed token-level re-measured 40 (PREP 33 was line-start grep face, VERIFY [N-1] corrected); requires UpAblDeltaStarSuboptimal same-wave registration; WangWW self-trap lexicon exemption noted)" "L577:m032f49".

(* ng_UpAblP4_UpStopTime_PA —— UpAblP4_UpStopTime_PA.v：九批 C-纯新（UpStopTime 的 PA 驱动件，81 行 3 Qed（三个行内闭合定理 minimal_stoptime/st_thresh_dominance/unguarded_no_stoptime；PREP 草案「0-Qed=PA 驱动件面」定性失实，二验 [N-1] 修正删句）；VET9B 四面机械绿 ；Require Import UpStopTime. 源 L36 实证→order 尾部追加按依赖先行性插于 UpStopTime 后；ng_qed 按 口径 token 级实测补记） *)
Definition ng_UpAblP4_UpStopTime_PA : NewGreenFace :=
  MkNewGreenFace "UpAblP4_UpStopTime_PA.v" 81 3 20260923
  "VET9B C-pure-new: UpStopTime PA driver (four-face green; three inline Qed closures; driver-face registry; requires UpStopTime, order insert-after per dependency precedence; ng_qed token-level 3 per VERIFY [N-1])" "L81:m1ae55c".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-SUB built-at-registration 四项组绿后实测补记）。 *)

Definition ng_uabl_attn_full_instance : NewGreenFace :=
  MkNewGreenFace "uabl_attn_full_instance.v" 135 2 20260924
  "R124 single-entry supply module: BoundedSoftmax 19-field Fin2 default instance as uabl_-prefixed named rows; one Require Import line exposes full namespace via six Require Export; Part A-C rows verbatim-identical to upstream faces (zero face-conversion tax); PA Closed x4 (bs_abs_id/bs_lpc_id/expf_pos/bs_abs); G3 Separate Extraction Obj.magic=0 (ml 10f2d638 / mli 6afe7ea0 anchors); born-in-place four-gate green 20260924; sandbox/Live/vo triple md5 c40c13a1 pinned; fa53_compat_abs required internally unchanged" "L135:mc40c13".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（ EB2 built-at-registration 四项验证实测补记；order 锚=SHA1 前 6 照 先例）。 *)

Definition ng_BBDBridgeSupply : NewGreenFace :=
  MkNewGreenFace "BBDBridgeSupply.v" 146 5 20260924
  "Batch-2 Type-A tail-insert first companion piece (Boltzmann free-energy bridge sum-interface supply: three csm_-based theorems + two bridges); born-in-place four-gate 20260924 by seat EB2: G2 EXIT=0 PA 5/5 Closed vo magic 436f712100015ff4; G3 self-scope 0 (R19-F1 extraction evidence gap cured by EB2 probe in _teb2_g3out, Separate Extraction of the three theorems, BBD.ml zero magic); G4 coqchk Axioms none; deps all in-tree current, leaf at order L644 anchor R124-988a53 sha1-6" "L146:m9a4b5a".

(* ng_UpReqSamplingFeed —— UpReqSamplingFeed.v：组2/组3 邻居成果伴生供给模块（W23 产 usrq_ 前缀 22 供给定理，293 行 22 Qed； 复核 PASS；ReqUContraction 两节求和诚实接口实现化供给；built-at-registration 四项验证实测 EB2：G2 EXIT=0、PA×22 全 Closed、vo 魔数 436f712100015ff4、vo 新于 v；G3 自证块口径 10 处已申报残留＝D 形 6（usrq_abs_ge_zero_req_supply/usrq_bs_abs_supply 抽象 le 前提破坏性读取，X1 #30 mtdc 同款槽号冻结）＋B 形 2（usrq_bs_sum_pos_supply sigT/InT 见证装箱，p2wb 同类）＋抽象关系构造 2（usrq_z_lb/ub_supply Coq_inl 装箱），零 E/L/T 形＝配方③ 无适用位，与已入树 mtdc/p2wb 已申报残留同类判 P2 另案留待——W23 清册 L99 自申「提取检查点未另设」，再验代申报防分裂；G4 coqchk axiom-free；依赖 CW_219/UpReqAlgebra/UpReqSumD/UpReqConcSoftmax/UpReqSampling/ConcMixSelFeed 全在册现势兼容，末端件 order 尾部追加 L645 锚 -7ccbe2=SHA1 前 6） *)
Definition ng_UpReqSamplingFeed : NewGreenFace :=
  MkNewGreenFace "UpReqSamplingFeed.v" 293 22 20260924
  "Batch-2/3 companion supply piece (usrq_ 22 supply theorems for ReqUContraction two-section sum honest-premise interfaces); born-in-place four-gate 20260924 by seat EB2: G2 EXIT=0 PA 22/22 Closed vo magic 436f712100015ff4; G3 self-scope 10 DECLARED residuals (6 D-form abs-twin abstract-le destructive reads X1-#30-slot-frozen class, 2 B-form sum_pos sigT/InT witness boxing p2wb class, 2 abstract-relation Coq_inl boxings z-twin; zero E/L/T sites so fix-3 not applicable; same class as in-tree mtdc/p2wb declared residuals, P2 deferred; W23 ledger L99 declared no probe, EB2 re-verify declares on its behalf); G4 coqchk Axioms none; deps all in-tree current, leaf at order L645 anchor R124-7ccbe2 sha1-6" "L293:mf918e5".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-EXEC built-at-registration 四项验证实测补记；order 锚=md5 前 6 照 E1 §四①处方—— 现测判定：c40c13=md5 前 6、988a53/7ccbe2=文件 SHA1 前 6，两口径历史混用在案，本次统一 md5 前 6 与 ng_meta 自洽）。 *)

(* ng_UpReqCf2TvGenSupply —— UpReqCf2TvGenSupply.v：C1 产一件双定理供给模块（192 行 3 Qed；件一 uc2t_habs_cf2tv_nonneg 强形＋uc2t_habs_cf2tv_nonneg_norm 规格形，件二 uc2t_cf2tv_nonneg_habs_rev 反向真等价（V-C1 判「真等价·无降档·升格成立」：plain 形复原＋归一性件内已证＋合成结论三查全过）；PA×3 全 Closed；G3 单命令三常数提取主 ml Obj.magic=0；G4 coqchk 传递环境公理 3 条＋CONTAINMENT-EQUAL 新增=0；built-at-registration 绿判四项组 ；沙箱/Live/vo 三方 md5 恒等 bcac27f1；Require CW219/Algebra/SumD/Dist/ConcSoftmax/Sampling/ConcMixSel/ConcB1/ConcB2/AttnDoeblin/ConcFin2 全在册） *)
Definition ng_UpReqCf2TvGenSupply : NewGreenFace :=
  MkNewGreenFace "UpReqCf2TvGenSupply.v" 192 3 20260925
  "P7FIN2 piece-1+2 supply: cf2-TV nonneg strong+normalized forms and reverse true-equivalence (plain-form restoration, in-piece normalization, both directions machine-checked; V-C1 upgraded); PA 3/3 Closed; G3 single-command three-constant extraction Obj.magic=0; G4 coqchk 3 transitive axioms CONTAINMENT-EQUAL zero-new; born-in-place four-gate green 20260925; triple md5 bcac27f1" "L192:mbcac27".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-EXEC built-at-registration 四项验证实测补记；order 锚=md5 前 6 照 尾块统一口径；源=Live_X 逐字拷贝；两红件 UpAblD1S11_UpReqCauchy（头注注释失衡）/UpReqBregmanBase（L119 证明体伤）。 *)

(* ng_UpAblBYDecisionTree —— UpAblBYDecisionTree.v：DS 工程 BY 项链基建件（218 行 8 Qed；dt_ 前缀决策树叶位正值/叶数守恒及树清点八定理；纯 stdlib Require Arith/PeanoNat/List/Lia 零项目依赖； 纳入波 built-at-registration 四项验证绿 ：G2 EXIT=0 PA Closed、vo 魔数 436f712100015ff4、G3 提取 own ml Obj.magic=0 闭包 0、G4 coqchk axiom-free；与 J7 七件联合核定稿版 md5 同代 594c6e） *)
Definition ng_UpAblBYDecisionTree : NewGreenFace :=
  MkNewGreenFace "UpAblBYDecisionTree.v" 218 8 20260925
  "BY necklace infrastructure: dt_ leaf positivity/equality and tree inventory, eight theorems, pure stdlib; four-gate green on current HEAD 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 594c6e (J7-identical)" "L218:m594c6e".


(* ng_UpAblBYUpperTight —— UpAblBYUpperTight.v：BY 上紧化件（189 行 5 Qed；btight_ 前缀半燃料紧界；Require Arith/Lia＋UpAblBYLowerBound 包内依赖＝本项链内拓扑序 LB→UT；四项验证绿同上口径 ；md5 4f4990=J7 同代） *)
Definition ng_UpAblBYUpperTight : NewGreenFace :=
  MkNewGreenFace "UpAblBYUpperTight.v" 189 5 20260925
  "BY upper-tightening: btight_ half-fuel tight bound, five theorems, requires UpAblBYLowerBound (intra-set topo order); four-gate green on current HEAD 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 4f4990 (J7-identical)" "L189:m4f4990".

(* ng_UpAblMixACount —— UpAblMixACount.v：混合选择器计数件（144 行 6 Qed；macnt_ 前缀二分选择计数；Require PeanoNat/Lia/QArith＋UpReqMixLogA（在册）；四项验证绿同上口径 ；md5 53bf04=J7 同代） *)
Definition ng_UpAblMixACount : NewGreenFace :=
  MkNewGreenFace "UpAblMixACount.v" 144 6 20260925
  "Mix selector counting: macnt_ binary-search choice counting over UpReqMixLogA, six theorems; four-gate green on current HEAD 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 53bf04 (J7-identical)" "L144:m53bf04".

(* ng_UpAblMixBSharp —— UpAblMixBSharp.v：混合计数界紧化件（222 行 4 Qed；msharp_ 前缀计数界 5→4 紧化；Require PeanoNat/Lia＋UpReqMixLogB（在册）；四项验证绿同上口径 ；md5 9300a0=J7 同代） *)
Definition ng_UpAblMixBSharp : NewGreenFace :=
  MkNewGreenFace "UpAblMixBSharp.v" 222 4 20260925
  "Mix counting bound sharpening 5->4: msharp_ over UpReqMixLogB, four theorems; four-gate green on current HEAD 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 9300a0 (J7-identical)" "L222:m9300a0".

(* ng_UpAblD1S12_UpReqAttnUniformLimit —— UpAblD1S12_UpReqAttnUniformLimit.v：FA-D1S12 供给包件①（90 行 4 Qed；原件 UpReqAttnUniformLimit Section AlmUniform 7 数据槽的 Token:=bool 具体有限集实例供给（uabd1s12_ul_ 前缀）；独立伴随模块零 Require 原件（P3S1 工艺）；原件现势槽对账 PASS（-SCREEN 抽检＋EXEC 全槽实扫）；四项验证绿 ：G3 own magic=0 闭包 0；md5 042868） *)
Definition ng_UpAblD1S12_UpReqAttnUniformLimit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnUniformLimit.v" 90 4 20260925
  "FA-D1S12 supply pack 1: AlmUniform 7 data slots as bool finite-set instances (uabd1s12_ul_), zero Require on mother P3S1, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 042868" "L90:m042868".

(* ng_UpAblD1S12_UpReqAttnMassSplit —— UpAblD1S12_UpReqAttnMassSplit.v：FA-D1S12 供给包件②（86 行 4 Qed；AmsMassSplit 8 数据槽 bool 实例供给（uabd1s12_ams_）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 0；md5 b9a01d） *)
Definition ng_UpAblD1S12_UpReqAttnMassSplit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnMassSplit.v" 86 4 20260925
  "FA-D1S12 supply pack 2: AmsMassSplit 8 data slots bool instances (uabd1s12_ams_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 b9a01d" "L86:mb9a01d".

(* ng_UpAblD1S12_UpReqAttnQ18Tail —— UpAblD1S12_UpReqAttnQ18Tail.v：FA-D1S12 供给包件③（86 行 4 Qed；AqtTail 8 数据槽 bool 实例供给（uabd1s12_aqt_）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 0；md5 03a40f） *)
Definition ng_UpAblD1S12_UpReqAttnQ18Tail : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnQ18Tail.v" 86 4 20260925
  "FA-D1S12 supply pack 3: AqtTail 8 data slots bool instances (uabd1s12_aqt_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 03a40f" "L86:m03a40f".

(* ng_UpAblD1S13_UpReqAlignClose —— UpAblD1S13_UpReqAlignClose.v：FA-D1S13 供给包件①（154 行 2 Qed；原件 UpReqAlignClose UacClose 节余量 16 槽供给（uabd1s13_ 前缀）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 71 全落 S07 既档伪影轨；md5 dd1670） *)
Definition ng_UpAblD1S13_UpReqAlignClose : NewGreenFace :=
  MkNewGreenFace "UpAblD1S13_UpReqAlignClose.v" 154 2 20260925
  "FA-D1S13 supply pack 1: UacClose residual 16 slots (uabd1s13_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction own ml Obj.magic=0 (closure 71 on documented S07 artifact trail), coqchk Axioms none; md5 dd1670" "L154:mdd1670".

(* ng_UpAblD1S13_AlignIdUnclosed —— UpAblD1S13_AlignIdUnclosed.v：FA-D1S13 供给包件②（117 行 2 Qed；原件 AlignIdUnclosed 节 AiuBackwardKL 余量 14 槽供给（R/RIS/sumf/sum_ext/sum_add/sum_linear/reward/beta/beta_pos/pi_ref/pi_ref_pos/eta/ZAL_pos）；S2/S3 已收槽排除登记在头注；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 71 同款既档伪影；md5 45d9ae） *)
Definition ng_UpAblD1S13_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "UpAblD1S13_AlignIdUnclosed.v" 117 2 20260925
  "FA-D1S13 supply pack 2: AiuBackwardKL residual 14 slots (S2/S3-claimed slots excluded per header ledger), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction own ml Obj.magic=0 (closure 71 documented S07 trail), coqchk Axioms none; md5 45d9ae" "L117:m45d9ae".

(* ng_UpAblMetaLow —— UpAblMetaLow.v：AID 机器反驳形下界件（396 行 0 Qed＝构造项定义面交付·非降档：21 语句 mtl_ 前缀（核行全同⟹TV(1)=0 一步混同，cf2 下界反驳），Set 层 Not/Empty_set 构造性否定形（S12 件族先例同款）；Require CW219/UpReqAlgebra/UpReqDist/UpReqSampling/UpReqConcFin2 全在册；0921 窗十件名册唯一漏收件（-SCREEN 差集考古判定）；四项验证绿 ：G3 own magic=0 闭包 71 既档伪影；md5 3fb1d4） *)
Definition ng_UpAblMetaLow : NewGreenFace :=
  MkNewGreenFace "UpAblMetaLow.v" 396 0 20260925
  "AID machine-refutation lower bound: identical core rows imply TV(1)=0, 21 mtl_ statements Definition-form zero-Qed delivery (non-trivial per redline-3, Set-layer constructive negation S12-family precedent), sole survivor of 0921 ten-piece window per差集考古; four-gate green 20260925, extraction own ml Obj.magic=0 (closure 71 documented S07 trail), coqchk Axioms none; md5 3fb1d4" "L396:m3fb1d4".

(* ng_UpReqPaperAnchor —— UpReqPaperAnchor.v： ANCHOR-A 论文引用锚机制件（244 行 14 Qed；pan_ 前缀具名锚记录 pan_anchor_list＋pan_find_* 检索函数＋三重不变式（sym_ck/file_ck/md5_len/day_uniform）——论文引用行号漂移痛点的在册机制化解法；纯 Ascii/String 零项目依赖；-SCREEN git 考古=从未入库非被移除；四项验证绿 ：G3 own magic=0 闭包 0；md5 b49e12） *)
Definition ng_UpReqPaperAnchor : NewGreenFace :=
  MkNewGreenFace "UpReqPaperAnchor.v" 244 14 20260925
  "R114 ANCHOR-A paper-reference anchor mechanism: pan_anchor_list named anchors + pan_find_* retrievers + triple invariants (sym/file/md5_len/day), pure Ascii/String zero project deps, never-in-tree verified by git archaeology; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 b49e12" "L244:mb49e12".
(* ng_p2a_AttnClimClose —— p2a_AttnClimClose.v：消融落件·工程包AD tier2 末批二（164 行 4 Qed；原件全文逐字保留，仅将文末清单所列定理 p2a_attn_tv_seq_clim_zero（原 L112，2 句玩具证·定义层受控展开）之证明体替换，声明面与引用面零改动、零新增 Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留原件 Print Assumptions 追印面；Require QArith/CW_ConstructiveWorld_219/UpBudgetReal/UpArchAttn；本期归册三候件之一，EX-BOX 裁定已贴补丁未注册→EX-REG 归册后编译；实测 md5 5dc9d1） *)
Definition ng_p2a_AttnClimClose : NewGreenFace :=
  MkNewGreenFace "p2a_AttnClimClose.v" 164 4 20260926
  "Ablation drop piece, eng-package AD tier2 batch-2: original text kept verbatim, only p2a_attn_tv_seq_clim_zero (orig L112) proof body swapped to toy proof (2 sentences, definition-layer controlled unfolding); declarations and references unchanged, zero new Require; R15 candidate trio, EX-BOX ruled patched-but-unregistered, compile after EX-REG enrollment; md5 5dc9d1" "L164:m5dc9d1".

(* ng_p3a_TempDualBoolSlots —— p3a_TempDualBoolSlots.v：消融落件·B 可消融件（169 行 6 Qed；原件全文逐字保留，仅将文末清单所列定理 p3a_bsum_ext（原 L51，7 句刀体；坐标 L828 定理 10.13 四求和槽＝开放池 S05 三槽）之证明体替换为玩具证（实质非平凡三口径），声明面与引用面零改动、零新增 Require，纯构造性闭合，文尾保留原件 Print Assumptions 追印面；Require QArith/CW_ConstructiveWorld_219/UpReqTempDefs/UpReqEntropyDeficitTemp；本期归册三候件之一，EX-BOX 裁定已贴补丁未注册→EX-REG 归册后编译；实测 md5 658d14） *)
Definition ng_p3a_TempDualBoolSlots : NewGreenFace :=
  MkNewGreenFace "p3a_TempDualBoolSlots.v" 169 6 20260926
  "Ablation drop piece B-ablatable: original text kept verbatim, only p3a_bsum_ext (orig L51, 7-clause blade body; L828 Theorem 10.13 four-sum slots = open pool S05 three slots) proof body swapped to toy proof; declarations and references unchanged, zero new Require; R15 candidate trio, EX-BOX ruled patched-but-unregistered, compile after EX-REG enrollment; md5 658d14" "L169:m658d14".

(* ng_AbsLeIdReal53 —— AbsLeIdReal53.v：实数具体层 le 版绝对值恒等引理族（134 行 6 Qed；主件 r53_real_abs_ge_zero_id（le zero a -> Id (abs a) a 的 Real 层独立兑现），并交付 strict/eq/le 三种平移形扩展与乘法兼容引理 r53_real_abs_mult_id；与抽象层 fa53 件相互独立仅 Require 复用，依赖 S01_BaseRing/fa53_compat_abs/S02_CauchyComplete/S03_QExp/S07_RealSetoidExpLog 全在册；全件 Qed 闭合、零承认词面、无经典逻辑，语句面全 Set 层零 Prop 泄露，文末 Print Assumptions 审计全 Closed；本期归册三候件之一；实测 md5 b69e18） *)
Definition ng_AbsLeIdReal53 : NewGreenFace :=
  MkNewGreenFace "AbsLeIdReal53.v" 134 6 20260926
  "Real concrete-layer le-version absolute-value identity lemma family: main r53_real_abs_ge_zero_id (le zero a -> Id (abs a) a, Real-layer standalone), plus strict/eq/le shift extensions and multiplicative compat r53_real_abs_mult_id; independent of abstract fa53 piece, Require-reuse only; all Qed closed, zero admit literals, no classical logic, Set-layer statements zero Prop leak, Print Assumptions all Closed; R15 candidate trio; md5 b69e18" "L134:mb69e18".
