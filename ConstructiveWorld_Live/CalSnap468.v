(* ===================================================================== *)
(* CalSnap468.v — KR 校准附册数据模块（自包含独立模块）                    *)
(* 使命：登记 468 树级校准快照数据：树级指纹 + 643→468 移动差（删/增/漂移/  *)
(*       存活四计数）+ K1/K2 校准四类计数，编码为 Record+list，             *)
(*       供目标侧 Require 或摘录。K1/K2 主数据（K1 的 new_line/status、     *)
(*       K2 的宿主归宿）对 643 树有效；468 树以本附册为准。                 *)
(* 依赖：零库树 Require；仅标准库 Stdlib.Strings.String 一件                *)
(*       （同 K1/K2/K3 范式）；list/nat/bool/option 均出自预启环境。        *)
(* 对标：基座 ConstructiveWorld_Live/ 468 .v 与 order.txt 422 行；全部      *)
(*       指纹数值以件内 snapshot 字段为权威。                               *)
(* 构造性：纯 Set 层数据 + 全 Defined 函数 + 布尔自洽；                     *)
(*       无 Axiom/Admitted/Prop 语句。                                      *)
(* 编译配方：独立编译 rocq c CalSnap468.v（零库树依赖，任何目标池可嵌入）。 *)
(* 数据来源：anchor-cal 与 lineage-cal 两册校准 JSON 及 643→468 逐件        *)
(*       diff 实测；链 md5=逐件 "md5  file\n"（字典序）连接体的 md5。       *)
(* ===================================================================== *)

From Stdlib.Strings Require Import String.
(* 本环境实测：9.1 预启无 string；导入 String 后 string_scope               *)
(* 亦不自动开启，需显式 Open——K1/K3 池未需，环境细节差异，如实记录。        *)
Open Scope string_scope.

(* ---- 红线计数（嵌套注释剥离后语句面词边界口径，468 树实测全零）---- *)
Record RedlineCounts : Set := mkRL {
  rl_axiom : nat;
  rl_admitted : nat;
  rl_classical : nat
}.

(* ---- 树级校准快照 ---- *)
Record CalSnapshot468 : Set := mkCal {
  snap_tree : string;
  snap_order_md5 : string;
  snap_order_lines : nat;
  snap_coqproject_md5 : string;
  snap_file_count : nat;
  snap_total_bytes : nat;
  snap_total_lines : nat;
  snap_redline : RedlineCounts;
  snap_vo_magic : string;
  snap_chain_md5 : string;
  snap_prev_file_count : nat;
  snap_deleted_count : nat;
  snap_added_count : nat;
  snap_drifted_count : nat;
  snap_unchanged_count : nat;
  k1_anchors_total : nat;
  k1cal_still_valid : nat;
  k1cal_need_shift : nat;
  k1cal_dead_file : nat;
  k1cal_not_found : nat;
  k1cal_tier_a : nat;
  k1cal_tier_b : nat;
  k1_prev_mechanical : nat;
  k2cal_mapping_valid : nat;
  k2cal_rehosted : nat;
  k2cal_mapping_lost : nat;
  k2cal_gone_confirmed : nat;
  k2_decl_total : nat;
  k2_absorb_hosts_alive : nat;
  k2_absorb_hosts_total : nat
}.

Definition snapshot : CalSnapshot468 :=
  mkCal
    "ConstructiveWorld_Live/"
    "44843d67f70722b821e67ca388aebfff"
    422
    "343630c9b3bdecff54895248e226194a"
    468
    21218506
    414772
    (mkRL 0 0 0)
    "436f712100015ff4"
    "a6589ee40cbf162ba62388eba872ac9e"
    643
    193
    18
    70
    380
    1533
    1015
    31
    139
    348
    991
    55
    1220
    179
    10
    2
    25
    216
    8
    10.

(* ---- 643→468 删除件清单（193 件，字典序）---- *)
Definition deleted_files : list string :=
  cons "BanachNoHypNorm.v" (cons "BanachS3Chain.v" (cons "DTPT_Bridge_All.v" (cons "ExpLinearLower.v" (cons "ExpNegFinale.v" (cons "ExpNegPosUp.v" (cons "FepIdConsume.v" (cons "FirewallReqDischarge.v" (cons "GibbsAssembly.v" (cons "GibbsAttractor.v" (cons "InstBWdClose.v" (cons "LoHiSqueeze.v" (cons "LogTwoBridge.v" (cons "LogTwoEnvelope.v" (cons "PA_AttnSqrt.v" (cons "PA_CW220_Extensions.v" (cons "PA_FirewallReqDischarge.v" (cons "PA_PolyIntegral.v" (cons "PA_ToyR_SupplyAssembly.v" (cons "PA_ToyR_fa57_ext.v" (cons "PA_UpAblMetaWindow.v" (cons "PA_UpDissip.v" (cons "PadeDenPosA.v" (cons "QuickDischargeA.v" (cons "SecondLawConsume.v" (cons "SupKLBound.v" (cons "SymplecticRotationSpec.v" (cons "TempMonoW2Mark.v" (cons "ToyR_AbsLeId.v" (cons "ToyR_BeukersLists.v" (cons "ToyR_BeukersVariant.v" (cons "ToyR_GibbsFamilyExt.v" (cons "ToyR_Ln2Integrality.v" (cons "ToyR_NatLenPos.v" (cons "ToyR_Paper12345Sample.v" (cons "ToyR_PhysPredAblation.v" (cons "ToyR_RateTheoryAblation.v" (cons "ToyR_SecondLawConsume.v" (cons "ToyR_SumEqListFeed.v" (cons "ToyR_SumEqListMark.v" (cons "ToyR_UpAblP6_GibbsFamilyExt.v" (cons "ToyR_UpAblP6_UniformLimit.v" (cons "ToyR_ZPosSlotFeed.v" (cons "ToyR_fa52_dpo_witness.v" (cons "ToyR_fa52_entropy_diff_unsat.v" (cons "ToyR_fa57_ext.v" (cons "UpAblA2_LoInflation.v" (cons "UpAblAbsQFeedB2.v" (cons "UpAblAbsSumLeB3.v" (cons "UpAblAbsSumLeEps.v" (cons "UpAblAbsTwoPtAbs.v" (cons "UpAblB1_MonoSplit.v" (cons "UpAblBYDecisionTree.v" (cons "UpAblBYLowerBound.v" (cons "UpAblCauchyLim.v" (cons "UpAblCauchyMod.v" (cons "UpAblD1S2_reqlog_AlignIdUnclosed.v" (cons "UpAblD1S2_reqlog_GibbsAssembly.v" (cons "UpAblD1S2_reqlog_UpReqAlign3.v" (cons "UpAblD1S2_reqlog_UpReqAlignClose.v" (cons "UpAblD1S2_reqlog_UpReqDpoLoss.v" (cons "UpAblD1S3_sum_pos_SecondLawQuantified.v" (cons "UpAblD1S3_sum_pos_TempSoftmaxInstantiation.v" (cons "UpAblD1S3_sum_pos_UpReqAlign3.v" (cons "UpAblD1S3_sum_pos_UpReqAlignClose.v" (cons "UpAblD1S3_sum_pos_UpReqAttnGibbs.v" (cons "UpAblD1S3_sum_pos_UpReqEntropyDeficitTemp.v" (cons "UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v" (cons "UpAblD1S3_sum_pos_UpReqEntropyMonoSplit.v" (cons "UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v" (cons "UpAblD1S3_sum_pos_UpReqEntropyUniqueTemp.v" (cons "UpAblD1S3_sum_pos_UpReqTempDefs.v" (cons "UpAblDeltaStarSuboptimal.v" (cons "UpAblDistLogEq.v" (cons "UpAblDistLogLe.v" (cons "UpAblEps49Fam.v" (cons "UpAblEps49Main.v" (cons "UpAblEps66Pos.v" (cons "UpAblGrpEqDecWorld.v" (cons "UpAblGrpEqDischarge.v" (cons "UpAblHalfPow.v" (cons "UpAblKVEpsHalf.v" (cons "UpAblLeEqCompat.v" (cons "UpAblLogSelOracle.v" (cons "UpAblLogWallFinal.v" (cons "UpAblMetaConjBridge.v" (cons "UpAblMetaDivQ.v" (cons "UpAblMetaLow.v" (cons "UpAblMetaTemp.v" (cons "UpAblMixACount.v" (cons "UpAblMixBSharp.v" (cons "UpAblP1T1_AlignCert.v" (cons "UpAblP1T2_GrpoAuditCert.v" (cons "UpAblP1_SecondLawQuantified_sumd.v" (cons "UpAblP1_SqrtfCauchyArch_arch.v" (cons "UpAblP2FeedMix.v" (cons "UpAblP2T1_CertB.v" (cons "UpAblP2_FepIdentClass_inst_bundle.v" (cons "UpAblP2_UpMinP_tokens_pack.v" (cons "UpAblP3_UpReqAttnMixTime.v" (cons "UpAblP3_UpReqConcMixSel.v" (cons "UpAblP4_UpStopTime_PA.v" (cons "UpAblP6_EntropyMonoSplit_A.v" (cons "UpAblP6_GibbsFamilyExt.v" (cons "UpAblP6_S5SlotWire.v" (cons "UpAblP6_UniformLimit.v" (cons "UpAblP7_AbsNonNeg.v" (cons "UpAblP7_LoHiBridge.v" (cons "UpAblP7_LoHiCross.v" (cons "UpAblP7_P7FlagshipTail.v" (cons "UpAblP7_P7KappaFlagship.v" (cons "UpAblP7_Paper7Ablation.v" (cons "UpAblP7_Paper7Ablation_S1inst.v" (cons "UpAblP7_WallEps_CB2.v" (cons "UpAblP7_WallEps_CSM.v" (cons "UpAblQeqBridge.v" (cons "UpAblQfloorDepth.v" (cons "UpAblRateAlgPkg.v" (cons "UpAblSlackMix.v" (cons "UpAblSlotB0Merge.v" (cons "UpAblSposDirect.v" (cons "UpAblT13_UpFirewallReq.v" (cons "UpAblT13_UpReqAlignRestA.v" (cons "UpAblT13_UpReqSampling.v" (cons "UpAblT13_UpSigMigrate2.v" (cons "UpAblT13b_G13.v" (cons "UpAblT13b_UpReqAlign.v" (cons "UpAblT13b_UpReqAlign2.v" (cons "UpAblT13b_UpReqAlignRestA.v" (cons "UpAblT13b_UpReqDist.v" (cons "UpAblT13b_UpSigMigrate.v" (cons "UpAblT13b_UpSigMigrate2.v" (cons "UpAblT13b_UpTVDoeblin.v" (cons "UpAblT13c_UpSigMigrate2.v" (cons "UpAblT2a_UpFirewallReq.v" (cons "UpAblT2a_UpReqAlign.v" (cons "UpAblT2a_UpReqAlign2.v" (cons "UpAblT2a_UpReqAlignRestA.v" (cons "UpAblT2a_UpReqDist.v" (cons "UpAblT2a_UpReqFEPAttn.v" (cons "UpAblT2a_UpReqMisc5.v" (cons "UpAblT2a_UpReqPPO.v" (cons "UpAblT2a_UpSigMigrate2.v" (cons "UpAblT5_S12_B5RecycleSF.v" (cons "UpAblT9_G09_MiscSmall.v" (cons "UpAblT9_UpReqFEPAttn.v" (cons "UpAblT9_UpSigMigrate.v" (cons "UpAblTwLeFeed.v" (cons "UpAblZposDirect.v" (cons "UpAlignId.v" (cons "UpArchAttn.v" (cons "UpDPOLip.v" (cons "UpDissip.v" (cons "UpEntropyGain.v" (cons "UpFirewall.v" (cons "UpKVDrift.v" (cons "UpKVEv.v" (cons "UpMinP.v" (cons "UpQKTVCompose.v" (cons "UpReqArgminEngine.v" (cons "UpReqAttnQ18Tail.v" (cons "UpReqB4TwoStage.v" (cons "UpReqBanachBinomBridge.v" (cons "UpReqBanachExpAddEq.v" (cons "UpReqBanachExpNeg.v" (cons "UpReqBanachExpOppOne.v" (cons "UpReqBanachInstEMult.v" (cons "UpReqBanachSepThm.v" (cons "UpReqBanachStrong.v" (cons "UpReqBishopFull.v" (cons "UpReqCEqDispersion.v" (cons "UpReqCf2TvGenWorld.v" (cons "UpReqCf2TvW3.v" (cons "UpReqExpPosWitness.v" (cons "UpReqForwardKLFamily.v" (cons "UpReqI4Bridge.v" (cons "UpReqIrrationalInstances.v" (cons "UpReqLogCompD2.v" (cons "UpReqLogZWallEquiv.v" (cons "UpReqMixLazy.v" (cons "UpReqMixLogD.v" (cons "UpReqMpDomain.v" (cons "UpReqPPO.v" (cons "UpReqPadeBetaPos.v" (cons "UpReqPadeDenPos12.v" (cons "UpReqPadeFinale.v" (cons "UpReqPadeSignXfer.v" (cons "UpReqPadeTransport.v" (cons "UpReqStrictBridgeD.v" (cons "UpReqTailResidual.v" (cons "UpStepKLM3.v" (cons "fa52_entropy_diff_unsat.v" (cons "fka_weak_triangle_ref.v" (nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* ---- 643→468 新增件清单（18 件，字典序）---- *)
Definition added_files : list string :=
  cons "Arch_Banach_01.v" (cons "Arch_GibbsA_01.v" (cons "Arch_PA_01.v" (cons "Arch_PA_02.v" (cons "Arch_PA_03.v" (cons "Arch_PA_04.v" (cons "Arch_SumEqL_01.v" (cons "Arch_ToyR_01.v" (cons "Arch_ToyR_02.v" (cons "Arch_ToyR_03.v" (cons "Arch_ToyR_04.v" (cons "Arch_UpAbl_01.v" (cons "Arch_UpAbl_02.v" (cons "Arch_UpAbl_03.v" (cons "Arch_UpAbl_30.v" (cons "Arch_UpReq_10.v" (cons "Arch_Up_01.v" (cons "Arch_Up_02.v" (nil)))))))))))))))))).

(* ---- 布尔自洽检查（目标侧 Compute all_green 应全 true）---- *)
(* 预启无 List 库（existsb/length 不在预启，同 K1/K3 手写范式） *)
Fixpoint in_list (x : string) (l : list string) {struct l} : bool :=
  match l with
  | nil => false
  | cons y t => orb (String.eqb x y) (in_list x t)
  end.
Fixpoint slist_len (l : list string) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (slist_len t)
  end.
Definition check_del_len : bool := Nat.eqb (slist_len deleted_files) 193.
Definition check_add_len : bool := Nat.eqb (slist_len added_files) 18.
Definition check_inventory : bool :=
  Nat.eqb (643 - 193 + 18) (snap_file_count snapshot).
Definition check_k1_sum : bool :=
  Nat.eqb (k1cal_still_valid snapshot + k1cal_need_shift snapshot
           + k1cal_dead_file snapshot + k1cal_not_found snapshot) 1533.
Definition check_k1_mech : bool :=
  Nat.eqb (k1cal_still_valid snapshot + k1cal_need_shift snapshot) 1046.
Definition check_k2_sum : bool :=
  Nat.eqb (k2cal_mapping_valid snapshot + k2cal_rehosted snapshot
           + k2cal_mapping_lost snapshot + k2cal_gone_confirmed snapshot) 216.
Definition check_k2_gone : bool :=
  Nat.eqb (k2cal_gone_confirmed snapshot) 25.
Definition check_order_md5 : bool :=
  String.eqb (snap_order_md5 snapshot) "44843d67f70722b821e67ca388aebfff".
Definition check_cp_md5 : bool :=
  String.eqb (snap_coqproject_md5 snapshot) "343630c9b3bdecff54895248e226194a".
Definition check_chain_md5 : bool :=
  String.eqb (snap_chain_md5 snapshot) "a6589ee40cbf162ba62388eba872ac9e".
Definition check_redline_zero : bool :=
  andb (Nat.eqb (rl_axiom (snap_redline snapshot)) 0)
    (andb (Nat.eqb (rl_admitted (snap_redline snapshot)) 0)
      (Nat.eqb (rl_classical (snap_redline snapshot)) 0)).
Definition check_magic : bool :=
  String.eqb (snap_vo_magic snapshot) "436f712100015ff4".
(* 抽锚四处：删除表字典序首尾件在表/新增件在表/存活件不在删除表 *)
Definition check_spot_del_first : bool :=
  in_list "BanachNoHypNorm.v" deleted_files.
Definition check_spot_del_last : bool :=
  in_list "fka_weak_triangle_ref.v" deleted_files.
Definition check_spot_add : bool :=
  in_list "Arch_ToyR_01.v" added_files.
Definition check_spot_surv : bool :=
  negb (in_list "S01_BaseRing.v" deleted_files).

(* 总闸：全部检查项取合取（目标侧 Compute all_green 应得 true） *)
Definition all_green : bool :=
  andb check_del_len (andb check_add_len (andb check_inventory (andb check_k1_sum (andb check_k1_mech (andb check_k2_sum (andb check_k2_gone (andb check_order_md5 (andb check_cp_md5 (andb check_chain_md5 (andb check_redline_zero (andb check_magic (andb check_spot_del_first (andb check_spot_del_last (andb check_spot_add (check_spot_surv))))))))))))))).