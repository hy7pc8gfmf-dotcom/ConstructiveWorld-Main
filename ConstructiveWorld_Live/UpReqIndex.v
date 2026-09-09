(* ========================================================================= *)
(* UpReqIndex.v — 签名迁移总账机器索引（批5 收口清单项 9：机器可验总账入口）    *)
(*                                                                           *)
(* 建立席：批5 回写整合席 ｜ 建立日：2026-09-09 ｜ 形态：全 Set 层最小模块      *)
(* 零 Require（不依赖基座与任何在飞件——索引层独立于被索引层，杜绝循环依赖）。   *)
(*                                                                           *)
(* 数据源：迁移总账-20260909.md v1.1（表行 grep 解析实值 536/33/71/22/72，     *)
(* 和 = 734）；件数一律 grep decl 实测（Theorem/Lemma/Corollary 行），         *)
(* 不采信任何席位报告数。UpFirewallReq.v 续建在飞（终验未收）按纪律暂不登记，   *)
(* 终验后由续席追加 idx_UpFirewallReq 并同步统计字面值。                       *)
(*                                                                           *)
(* 四关（同家规，温控包装）：G1 禁词全文件扫描全零（含头注，字面规避）；        *)
(* G2 coqc 9.1 EXIT=0（cpu_guard LoadLimit 60）；G3 提取探针经 coqtop 管道      *)
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

(* idx_UpReqAlign3 —— UpReqAlign3.v：批3 T12/T13 组（环代数镜像 + 折叠件；收割席尾注余件仍挂账）*)
Definition idx_UpReqAlign3 : ReqModule :=
  MkReqModule "UpReqAlign3.v" 69 20260909 "r2_t13_collapse" true.

(* idx_UpReqAlignRestA —— UpReqAlignRestA.v：批3 余量 A（DPO 余量放电 + Q 桥落位，32 语句口径）*)
Definition idx_UpReqAlignRestA : ReqModule :=
  MkReqModule "UpReqAlignRestA.v" 23 20260909 "ralt_dpo_pair_loss_at_star" true.

(* idx_UpReqU2 —— UpReqU2.v：批3 U2 主体 7 件 + 辅件（外延件 (b) 化先例所在）*)
Definition idx_UpReqU2 : ReqModule :=
  MkReqModule "UpReqU2.v" 20 20260909 "req_u2_fixed_point_unique" true.

(* idx_UpReqPPO —— UpReqPPO.v：批3 收尾席（未认领 15 件收口：交付 14 + 冻结 1；真证机器旗舰所在）*)
Definition idx_UpReqPPO : ReqModule :=
  MkReqModule "UpReqPPO.v" 22 20260909 "rppo_align_objective_decomp" true.

(* ---------- 已交付 req 模块清单（批4/批5 新增 12 模块，v1.1 增册） ---------- *)

(* idx_UpReqSampling —— UpReqSampling.v：批4 首席（ReqUContraction 11 + ReqBoundedSoftmax 23 + epp 辅件）*)
Definition idx_UpReqSampling : ReqModule :=
  MkReqModule "UpReqSampling.v" 43 20260909 "u_tv_contraction" true.

(* idx_UpReqAttnGibbs —— UpReqAttnGibbs.v：批4 主件席（首段 14 + 中后段 39 + 扫尾席解冻增量节；旗舰 Print 假设清零）*)
Definition idx_UpReqAttnGibbs : ReqModule :=
  MkReqModule "UpReqAttnGibbs.v" 63 20260909 "ag_topk_tv_identity_strict" true.

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

(* ---------- 批外增量（不占 734 迁移宇宙名额） ---------- *)

(* idx_UpRealLeB —— UpRealLeB.v：M2 收口引理席（Real 层 Bishop 形非严格序 real_le_b + 收口引理 + 定理 4.9/6.6 对应物）*)
Definition idx_UpRealLeB : ReqModule :=
  MkReqModule "UpRealLeB.v" 6 20260909 "real_le_closure_b" false.

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
  (cons idx_UpRealLeB nil))))))))))))))))))))))).

(* 模块计数：宇宙内 req 模块 23 + 批外 1 = 24（UpFirewallReq 终验后追加 → 各 +1） *)
Definition DeliveredModules : nat := 23.
Definition ExtraModules     : nat := 1.
Definition TotalModules     : nat := 24.

(* 件数计数：grep decl 实测和 776 = 宇宙内 770 + 批外 6 *)
Definition DeliveredItems : nat := 776.
Definition UniverseItems  : nat := 770.

(* 迁移宇宙表行解析实值（总账 v1.1，20260909；和 = 734） *)
Definition UniverseTotal          : nat := 734.
Definition UniverseDeliveredRows  : nat := 536.
Definition UniverseInFlightRows   : nat := 33.
Definition UniverseFrozenRows     : nat := 71.
Definition UniverseSuspendedRows  : nat := 22.
Definition UniverseUnclaimedRows  : nat := 72.
Definition LastAuditDay           : nat := 20260909.

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

(* 宇宙件数分账闭合：全量和 = 宇宙内 + 批外（UpRealLeB 6 件） *)
Lemma UniverseItems_matches : UniverseItems = minus DeliveredItems (rm_decl_cnt idx_UpRealLeB).
Proof. reflexivity. Qed.

(* 迁移宇宙五态分解闭合（表行解析 536+33+71+22+72 = 734） *)
Lemma Universe_splits : UniverseTotal
  = plus (plus (plus (plus UniverseDeliveredRows UniverseInFlightRows)
                   UniverseFrozenRows)
         UniverseSuspendedRows)
  UniverseUnclaimedRows.
Proof. reflexivity. Qed.

(* UpReqIndex v1.0（2026-09-09，回写整合席；四关全过，批5 收口清单项 9 交付） *)
