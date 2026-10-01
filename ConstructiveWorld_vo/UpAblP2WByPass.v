(* ==========================================================================)
   UpAblP2WByPass —— 装配 bool 二元 Token/State 世界，供给两判定接口实例与伴生组，汇总为泛用封装证书 p2wb_pack，并把代表结论实例化（质量守恒恒等；同域语句面
   使命：本件形式化装配 bool 二元 Token/State 世界，供给两判定接口实例与伴生组，汇总为泛用封装证书 p2wb_pack，并把代表结论实例化（质量守恒恒等。
   本件并载：UpStopTime 闭合结论配套模块；uabp1_slq_sumf / uabp1_slq_sumpos / uabp1_slq_sumext 语句面；使命：宿主 SqrtfCauchy 假设位3；uabp2_fic_invT / uabp2_fic_Z / uabp2_fic_Z_alt 语句面；uabp2_um_pack5_supplied / uabp2_um_tokens_pos_unsat / uabp2_um_tokens_pos_bnd 语句面；FA-P3S1 伴生实例化消解件；uabp3_cmk_sel_lpc / uabp3_cmk_time_lpc / uabp3_cmk_sumf_bundle 语句面；beta 正性（任意正有理 q 的 real_const 实例）、参考分布逐点正性与归一性（单点 SumOver 实例世界）、eta 参数的数据位/正性等 10 面。
   依赖：QArith.QArith, QArith.Qabs, Lia, Arith.PeanoNat, S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv
     S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF,
     S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpBudgetReal, UpConstitution, UpStopTime, Extraction, UpReqSumD,
     List, SqrtfCauchy, SqrtfCauchyArch, TempSoftmaxInstantiation, FepIdentClass, AttnDoeblin, fa53_compat_abs, UpReqAlgebra,
     UpReqConcSoftmax, UpReqSampling, UpAbl 系十三批 c 组之 G13 模块, UpReqSteadyThermo, UpAblZposReal, UpAblEps66Sum, UpAblEps49List。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 UpStopTime 闭合结论配套模块 ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpBudgetReal.
Require Import UpConstitution.
Require Import UpStopTime.

(* ============================================================ *)
(* 一、主依存性重述：最小停时三联证书（语句与 minimal_stoptime 逐字同形） *)
(* ============================================================ *)

Theorem uastp_minimal_stoptime_pa : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof. exact minimal_stoptime. Qed.

(* ============================================================ *)
(* 二、装配依存性重述：阈值策略双目标占优（语句与 st_thresh_dominance 逐字同形） *)
(* ============================================================ *)

Theorem uastp_st_thresh_dominance_pa : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof. exact st_thresh_dominance. Qed.

(* ============================================================ *)
(* 三、反面依存性重述：停时不存在分离件（语句与 unguarded_no_stoptime 逐字同形） *)
(* ============================================================ *)

Theorem uastp_unguarded_no_stoptime_pa : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof. exact unguarded_no_stoptime. Qed.

(* ============================================================ *)
(* 四、文尾逐件闭合审（Print Assumptions 三连）                                    *)
(* ============================================================ *)

Print Assumptions uastp_minimal_stoptime_pa.
Print Assumptions uastp_st_thresh_dominance_pa.
Print Assumptions uastp_unguarded_no_stoptime_pa.

(* ============================ §2 uabp1_slq_sumf / uabp1_slq_sumpos / uabp1_slq_sumext 语句面 ============================ *)
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section SlqSumD：SLQ sum 四面在 sumd 实例上的重述束              *)
(* ============================================================ *)
Section SlqSumD.

Context (S0 : Set).
Context (enum0 : list S0).
Context (enum0_nonempty : Not (enum0 = nil)).

(* sumf 槽实例：enum 列表和（定义件，δ 透明；T6a 根） *)
Definition uabp1_slq_sumf (f : S0 -> Real) : Real := sumd_sumf S0 enum0 f.

(* ============ sumpos 位重述（SLQ :78 语句逐字） ============ *)
(* ← sumd_sum_pos@UpReqSumD:233（非空前提显式承载） *)
Theorem uabp1_slq_sumpos :
  forall f : S0 -> Real,
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabp1_slq_sumf f).
Proof.
  intros f H.
  exact (sumd_sum_pos S0 enum0 f enum0_nonempty H).
Qed.

(* ============ sumext 位重述（SLQ :81 语句逐字） ============ *)
(* ← sumd_sum_ext@UpReqSumD:112（普查 19 槽最大面代表件） *)
Theorem uabp1_slq_sumext :
  forall f g : S0 -> Real,
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (uabp1_slq_sumf f) (uabp1_slq_sumf g).
Proof.
  intros f g H.
  exact (sumd_sum_ext S0 enum0 f g H).
Qed.

(* ============ sumlinear 位重述（SLQ :83 语句逐字） ============ *)
(* ← sumd_sum_linear@UpReqSumD:135 *)
Theorem uabp1_slq_sumlinear :
  forall (a : Real) (f : S0 -> Real),
    real_eq (uabp1_slq_sumf (fun s : S0 => real_mult a (f s)))
            (real_mult a (uabp1_slq_sumf f)).
Proof.
  intros a f.
  exact (sumd_sum_linear S0 enum0 a f).
Qed.

(* ============ sumadd 位重述（SLQ :85 语句逐字） ============ *)
(* ← sumd_sum_add@UpReqSumD:161 *)
Theorem uabp1_slq_sumadd :
  forall f g : S0 -> Real,
    real_eq (uabp1_slq_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (uabp1_slq_sumf f) (uabp1_slq_sumf g)).
Proof.
  intros f g.
  exact (sumd_sum_add S0 enum0 f g).
Qed.

End SlqSumD.

(* ============ G3 提取检验（一人一目录 _tp1s1_g3out） ============ *)
(* 求和载体件为本件唯一计算内容（列表 fold）；链复核。          *)
(* 接口字段（zero/plus）经 RIS 记录使用会拉入记录封装体——按两步判读       *)
(* 口径：家规轨（fold 核心体）magic=0 为过关主判据，记录体封装 magic      *)
(* 为擦除伪影逐族登记；四面重述体为等词/序谓词桥面，以说明替代提取。      *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_sumd.ml" uabp1_slq_sumf.

(* ============ G4 检验：假设闭包审计（四面全 Closed 为过关判据） ============ *)
Print Assumptions uabp1_slq_sumpos.
Print Assumptions uabp1_slq_sumext.
Print Assumptions uabp1_slq_sumlinear.
Print Assumptions uabp1_slq_sumadd.

(* ============================ §3 使命：宿主 SqrtfCauchy 假设位3 ============================ *)
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import SqrtfCauchy.
Require Import SqrtfCauchyArch.
Import RealInterfaceEnhancedMod.

(* ============ 位3 重述：阿基米德幂族位（宿主 :58-59 逐字） ============ *)
Theorem uabp1_sfc_arch_decay_slot :
  forall c eps : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) c ->
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  sigT (fun k : nat =>
    @lt Real RealEnhancedReal
        (@mult Real RealEnhancedReal c (sfc_pow_half k)) eps).
Proof. exact sfcy_arch_decay_slot. Qed.

(* ============ G3 提取检验（一人一目录 _tp1s1_g3out） ============ *)
(* 本体件计算核心＝nat 证书 witness（real_arch 种子链）。提取链     *)
(* 复核；接口投影链（@lt_mult_compat 等实例字段依存）会拉入               *)
(* RealEnhancedReal 记录封装体——按两步判读口径：多态件家规轨（nat 面       *)
(* 归纳/算术核心）magic=0 为过关主判据，记录体封装 magic 为擦除伪影        *)
(* 逐族登记（与上游 sfcy_G3.ml 剖面核验，零新增判据=计数与分布一致）。 *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_arch.ml" sfcy_arch_decay_real.

(* ============ G4 检验：假设闭包审计（Closed 为过关判据） ============ *)
Print Assumptions uabp1_sfc_arch_decay_slot.

(* ============================ §4 uabp2_fic_invT / uabp2_fic_Z / uabp2_fic_Z_alt 语句面 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import TempSoftmaxInstantiation.
Require Import FepIdentClass.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.

(* 接口投影记号（全显式 @，防 elaborator 隐参歧义；源版本 L62-68 同款形） *)
Notation ubreq x y := (@RealInterfaceEnhancedMod.req Real RealEnhancedReal x y).
Notation ublt x y := (@RealInterfaceEnhancedMod.lt Real RealEnhancedReal x y).
Notation ubzero := (@RealInterfaceEnhancedMod.zero Real RealEnhancedReal).
Notation ubone := (@RealInterfaceEnhancedMod.one Real RealEnhancedReal).
Notation ubplus a b := (@RealInterfaceEnhancedMod.plus Real RealEnhancedReal a b).
Notation ubmult a b := (@RealInterfaceEnhancedMod.mult Real RealEnhancedReal a b).
Notation ubopp a := (@RealInterfaceEnhancedMod.opp Real RealEnhancedReal a).
Notation ubinv x Hx := (@RealInterfaceEnhancedMod.inv_pos Real RealEnhancedReal x Hx).
Notation ubexp a := (@RealInterfaceEnhancedMod.exp_neg Real RealEnhancedReal a).

(* 实例数据面具体值（识别①③两侧读法；逐字对照库锚实例体 L315-366） *)
Definition uabp2_fic_invT : Real := ubinv ubone one_pos.
Definition uabp2_fic_Z : Real :=
  ubplus (ubexp (ubmult uabp2_fic_invT (ubopp ubone)))
         (ubexp (ubmult uabp2_fic_invT (ubopp ubone))).
Definition uabp2_fic_Z_alt : Real :=
  ubplus (ubexp (ubopp (ubmult uabp2_fic_invT ubone)))
         (ubexp (ubopp (ubmult uabp2_fic_invT ubone))).

(* ============ C0 ←L59 Context 消解：核心节接口在 Real 层可满足（库锚直接匹配） ==== *)
Theorem uabp2_fic_ctx_core :
  @FepIdentification Real RealEnhancedReal.
Proof.
  exact FepIdentificationReal.
Qed.

(* ============ K1/K2/K3 ←识别三条件独立形（零类提及，纯 Real 层语句） ========== *)
(* K1 ←识别① fic_temp_match:94 实例读法：两侧同为 inv(one) *)
Theorem uabp2_fic_fld_temp_match :
  ubreq uabp2_fic_invT uabp2_fic_invT.
Proof.
  exact (@RealInterfaceEnhancedMod.req_refl Real RealEnhancedReal uabp2_fic_invT).
Qed.

(* K2 ←识别② fic_energy_neg:96 实例读法：energy = opp·z 两侧同为 opp(one) *)
Theorem uabp2_fic_fld_energy_neg :
  forall s : bool, ubreq (ubopp ubone) (ubopp ubone).
Proof.
  intros s.
  exact (@RealInterfaceEnhancedMod.req_refl Real RealEnhancedReal (ubopp ubone)).
Qed.

(* K3 ←识别③ fic_partition_match:98-101 实例读法：Z 两侧经 opp-mult 逐点桥
   （fic_opp_mult_r:154）＋exp 兼容提升（fic_real_exp_neg_compat:294）真证 *)
Theorem uabp2_fic_fld_partition_match :
  ubreq uabp2_fic_Z uabp2_fic_Z_alt.
Proof.
  exact (@RealInterfaceEnhancedMod.req_plus_compat Real RealEnhancedReal           (ubexp (ubmult uabp2_fic_invT (ubopp ubone)))           (ubexp (ubopp (ubmult uabp2_fic_invT ubone)))           (ubexp (ubmult uabp2_fic_invT (ubopp ubone)))           (ubexp (ubopp (ubmult uabp2_fic_invT ubone)))           (fic_real_exp_neg_compat              (ubmult uabp2_fic_invT (ubopp ubone))              (ubopp (ubmult uabp2_fic_invT ubone))              (@fic_opp_mult_r Real RealEnhancedReal uabp2_fic_invT ubone))           (fic_real_exp_neg_compat              (ubmult uabp2_fic_invT (ubopp ubone))              (ubopp (ubmult uabp2_fic_invT ubone))              (@fic_opp_mult_r Real RealEnhancedReal uabp2_fic_invT ubone))).
Qed.

(* ============ P1-P4 ←性质件（件内真证；P1/P4 副本库锚实例体构造） ============ *)
(* P1 ←fic_sum_pos:82-84（真前提；副本实例体 L318-338：lt_id_l＋两支 lt_plus_compat） *)
Theorem uabp2_fic_fld_sum_pos :
  forall f : bool -> Real,
    (forall s : bool, ublt ubzero (f s)) ->
    ublt ubzero (ubplus (f true) (f false)).
Proof.
  intros f Hf.
  exact (@RealInterfaceEnhancedMod.lt_id_l Real RealEnhancedReal           ubzero (ubplus ubzero ubzero) (ubplus (f true) (f false))           (@RealInterfaceEnhancedMod.req_sym Real RealEnhancedReal              (ubplus ubzero ubzero) ubzero              (@RealInterfaceEnhancedMod.plus_zero Real RealEnhancedReal ubzero))           (@RealInterfaceEnhancedMod.lt_plus_compat Real RealEnhancedReal              ubzero (f true) ubzero (f false) (Hf true) (Hf false))).
Qed.

(* P2 ←fic_T_pos:86（证书；one_pos 直接匹配） *)
Theorem uabp2_fic_fld_T_pos :
  ublt ubzero ubone.
Proof.
  exact (@RealInterfaceEnhancedMod.one_pos Real RealEnhancedReal).
Qed.

(* P3 ←fic_D_pos:88（证书；one_pos 直接匹配） *)
Theorem uabp2_fic_fld_D_pos :
  ublt ubzero ubone.
Proof.
  exact (@RealInterfaceEnhancedMod.one_pos Real RealEnhancedReal).
Qed.

(* P4 ←fic_Z_thermo_pos:92（证书；副本实例体 L362-390：两支 exp_neg_pos 的
   plus_positive 构造） *)
Theorem uabp2_fic_fld_Z_thermo_pos :
  ublt ubzero uabp2_fic_Z.
Proof.
  exact (@RealInterfaceEnhancedMod.plus_positive Real RealEnhancedReal           (ubexp (ubmult uabp2_fic_invT (ubopp ubone)))           (ubexp (ubmult uabp2_fic_invT (ubopp ubone)))           (@RealInterfaceEnhancedMod.exp_neg_pos Real RealEnhancedReal              (ubmult uabp2_fic_invT (ubopp ubone)))           (@RealInterfaceEnhancedMod.exp_neg_pos Real RealEnhancedReal              (ubmult uabp2_fic_invT (ubopp ubone)))).
Qed.

(* ============ INST ←自建透明实例（数据 7 位字面承位＝T 合并申报） ============ *)
(* 字段值与库锚 FepIdentificationReal 逐字同源：fic_S:=bool、fic_sumf:=两点 plus、
   fic_T:=fic_D:=one、fic_z:=const one、fic_energy:=const opp·one、
   fic_Z_thermo:=uabp2_fic_Z；性质 7 位以件内定理 K1/K2/K3/P1-P4 与
   one_pos 直接匹配承位。透明 Build_ 应用（非脚本间接），展开全程内核可达。 *)
Definition uabp2_fic_inst :
  @FepIdentification Real RealEnhancedReal.
Proof.
  apply (@Build_FepIdentification Real RealEnhancedReal
    (* fic_S:81 *)            bool
    (* fic_sumf:82 *)          (fun f : bool -> Real => ubplus (f true) (f false))
    (* fic_sum_pos:82-84 *)    uabp2_fic_fld_sum_pos
    (* fic_T:85 *)             ubone
    (* fic_T_pos:86 *)         (@RealInterfaceEnhancedMod.one_pos Real RealEnhancedReal)
    (* fic_D:87 *)             ubone
    (* fic_D_pos:88 *)         (@RealInterfaceEnhancedMod.one_pos Real RealEnhancedReal)
    (* fic_z:89 *)             (fun _ : bool => ubone)
    (* fic_energy:90 *)        (fun _ : bool => ubopp ubone)
    (* fic_Z_thermo:91 *)      uabp2_fic_Z
    (* fic_Z_thermo_pos:92 *)  uabp2_fic_fld_Z_thermo_pos
    (* fic_temp_match:94 *)    uabp2_fic_fld_temp_match
    (* fic_energy_neg:96 *)    uabp2_fic_fld_energy_neg
    (* fic_partition_match:98-101 *) uabp2_fic_fld_partition_match).
Defined.

(* ============ PC ←L112 依存节 Context 消解成品（N3 主） ============ *)
(* fic_attention_is_gibbs_temp:246 出节全参直接匹配 I:=uabp2_fic_inst：
   三识别齐备 ⟹ 温度 softmax = Boltzmann 逐点（实例化后零类前提、零识别前提）。 *)
Theorem uabp2_fic_gibbs_real :
  forall s : bool,
    ubreq (@fic_softmax_temp Real RealEnhancedReal uabp2_fic_inst s)
          (@fic_boltzmann_dist Real RealEnhancedReal uabp2_fic_inst s).
Proof.
  intros s.
  exact (@fic_attention_is_gibbs_temp Real RealEnhancedReal           uabp2_fic_inst fic_real_exp_neg_compat s).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabp2_fic_ctx_core.
Print Assumptions uabp2_fic_fld_temp_match.
Print Assumptions uabp2_fic_fld_energy_neg.
Print Assumptions uabp2_fic_fld_partition_match.
Print Assumptions uabp2_fic_fld_sum_pos.
Print Assumptions uabp2_fic_fld_T_pos.
Print Assumptions uabp2_fic_fld_D_pos.
Print Assumptions uabp2_fic_fld_Z_thermo_pos.
Print Assumptions uabp2_fic_gibbs_real.

(* ============================ §5 uabp2_um_pack5_supplied / uabp2_um_tokens_pos_unsat / uabp2_um_tokens_pos_bnd 语句面 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import List.
Import ListNotations.

(* ============ 封装记录型（5 槽语句逐字对照源版本 L631-641，tokens_pos/ratio_pos 不入包） ============ *)
Inductive uabp2_um_pack5 : Set :=
| uabp2_um_pack5_intro :
    forall tokens : list Real,
      (* ←L632 tokens_ne *)
      sigT (fun i : nat => NatLt i (length tokens)) ->
      (* ←L635-636 tokens_sum *)
      real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one ->
      (* ←L639 ratio *)
      forall ratio : Real,
      (* ←L640 剪除：ratio_pos（零消费位，此处不留槽） *)
      (* ←L641 ratio_le_one *)
      real_le ratio real_one ->
      uabp2_um_pack5.

(* M1：单点概率表 one::nil ＋ ratio:=one 一次供给 5 槽 *)
Theorem uabp2_um_pack5_supplied : uabp2_um_pack5.
Proof.
  exact (uabp2_um_pack5_intro
           (real_one :: nil)
           (existT _ 0%nat (@id_refl bool true))
           (real_plus_zero real_one)
           real_one
           (inr (real_eq_refl real_one))).
Qed.

(* 原槽语句：forall i : nat, real_lt real_zero (nth i tokens real_zero)。
   取 i := length tokens：nth 越界返回默认 real_zero ⇒ 需 real_lt zero zero，
   与 real_lt_irrefl 矛盾 ⇒ 该槽对任何有限表不可满足。 *)
Theorem uabp2_um_tokens_pos_unsat :
  forall tokens : list Real,
    (forall i : nat, real_lt real_zero (nth i tokens real_zero)) -> False.
Proof.
  intros tokens Hpos.
  assert (Hlen : real_lt real_zero (nth (length tokens) tokens real_zero))
    by (apply Hpos).
  rewrite (nth_overflow tokens real_zero (le_n (length tokens)))
    in Hlen.
  destruct (real_lt_irrefl real_zero Hlen).
Qed.

(* ============ M3 ←有界变体可满足对照（失配仅在量词无界，数据面本体无碍） ============ *)
Theorem uabp2_um_tokens_pos_bnd :
  real_lt real_zero (nth 0%nat (real_one :: nil) real_zero).
Proof.
  exact real_lt_zero_one.
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabp2_um_pack5_supplied.
Print Assumptions uabp2_um_tokens_pos_unsat.
Print Assumptions uabp2_um_tokens_pos_bnd.

(* ============================ §6 FA-P3S1 伴生实例化消解件 ============================ *)
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import AttnDoeblin.
Require Import fa53_compat_abs.

(* ################ 段零：expf 五字段封装实例化消解（判例 A 形） ################
   AttnDoeblin.v:758 real_expf_realizable 语句逐字（Part C 具体柯西
   实数层；五 And 支＝源文件接口参数 L95-L99 逐字对应，封装形＝判例 A 形 已证结论
   的一件实例化消解形；req 面 1:1 对偶已在于 UpReqConcMixSel.v:925）。 *)
Theorem uabp3_amt_expf_bundle :
  sigT (fun f : Real -> Real => And (forall x : Real, real_lt real_zero (f x))
        (And (real_eq (f real_zero) real_one)
        (And (forall a b : Real,
              real_eq (f (real_plus a b)) (real_mult (f a) (f b)))
        (And (forall a b : Real, real_lt a b -> real_lt (f a) (f b))
             (forall a b : Real, real_le a b -> real_le (f a) (f b)))))).
Proof.
  exact real_expf_realizable.
Qed.

(* ################ 段一：列表 Fubini 组合学（判例 段一形复刻） ################
   出节机 AttnDoeblin.bs_list_sum 上的逐点同余/加法线性/零函数退化/
   双重和交换。段一各件为基础模块，不单独计入战果。 *)

Section UabP3AmtListSum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* 逐点 Id ⟹ 列表和 Id *)
Lemma uabp3_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) ->
  Id (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.

(* 列表和的加法线性 *)
Lemma uabp3_lsum_add : forall (f g : S -> R) (l : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (AttnDoeblin.plus_exchange (f x) (AttnDoeblin.bs_list_sum f t)
                                     (g x) (AttnDoeblin.bs_list_sum g t)).
Qed.

(* 零函数列表和为零 *)
Lemma uabp3_lsum_zero : forall l : list S,
  Id zero (AttnDoeblin.bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_trans (id_sym (mult_zero (AttnDoeblin.nat_to_R (length l))))
          (id_sym (AttnDoeblin.bs_list_const_sum zero l))).
Qed.

(* 双重列表和交换（内外列表分立一般形；Fubini 组合学核心） *)
Lemma uabp3_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => AttnDoeblin.bs_list_sum (f s) l2) l1)
     (AttnDoeblin.bs_list_sum (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (uabp3_lsum_zero l2)).
    exact (uabp3_lsum_ext (fun _ : S => zero)
                          (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') nil)
                          l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (AttnDoeblin.bs_list_sum (f x) l2) w)
                             (IH l2))).
    apply (id_sym (uabp3_lsum_add (fun s' : S => f x s')
              (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') t) l2)).
Qed.

End UabP3AmtListSum.

(* ################ 段二：sum_eq_list 槽重述（idt 实例化消解读法直接代入） ########
   槽 L105 语句逐字＝Id (sum_over_S g) (bs_list_sum g enum)。实例化消解读法
   （CYD7/CZB8/CWE5 已证结论、IdSlotTranslate 槽语句级闭合）：抽象求和接口参数
   实现为 RI 载体列表折叠机 idt_sumf en——本件照 T1b 先例把桥 1/桥 2
   件内复刻（IdSlotTranslate .vo 与现档 UpReqSumD 代际失配，见偏差账），
   桥语句形与 IdSlotTranslate.v:82/:130 一致。 *)

Section UabP3AmtSumEqListIdt.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* 桥 1：RI 载体列表折叠机（IdSlotTranslate.v:82 idt_list_sum 同构） *)
Fixpoint uabp3_idt_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (uabp3_idt_list_sum f t)
  end.

Definition uabp3_idt_sumf (en : list S) (f : S -> R) : R :=
  uabp3_idt_list_sum f en.

(* 桥 2：与宿主出节真机 AttnDoeblin.bs_list_sum 一致
   （IdSlotTranslate.v:130 idt_slot_attdoeblin 之语句型＝槽 L105 在
   sum_over_S ↦ uabp3_idt_sumf en 实例化消解读法下的本体） *)
Theorem uabp3_amt_sum_eq_list_idt : forall (en : list S) (g : S -> R),
  Id (uabp3_idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof.
  intros en g.
  unfold uabp3_idt_sumf.
  induction en as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus id_refl IH).
Qed.

End UabP3AmtSumEqListIdt.

(* ################ 段三：bs_swap 槽重述（判例 导出链·槽对偶形） ########
   槽 L100-L102 语句逐字。前提减薄＝仅需求和规范化槽（sum_eq_list，
   L105 逐字语句作节内显式位）：swap 位由其＋段一 Fubini 组合学整体
   导出，非独立接口位（判例 翻案已证结论；链形与
   p7d_swap_of_sum_eq_list@P7BoundedSoftmaxDeep:107 同构）。 *)

Section UabP3AmtSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

Theorem uabp3_amt_bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (uabp3_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (uabp3_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (uabp3_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

End UabP3AmtSwap.

(* ################ 段四：bs_abs / bs_lpc 槽重述（fa53 直接代入广播） ########
   槽 L103（N1：fa53 件3＝fa53_compat_abs.v:141 直接代入；AbsLeId.v:50
   同形先例在库）与槽 L104（N3：fa53 件1＝fa53_compat_abs.v:103 同形
   语句广播直接代入；出节使用形见源文件 L192-195/L216-219 全参调用）。
   可判定序数据槽＝T2b 广播形减薄登记（DecidableOrder 纯数据供给面）。 *)

Section UabP3AmtAbsLpc.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 槽 L103 语句逐字 *)
Theorem uabp3_amt_bs_abs : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

(* 槽 L104 语句逐字（＝lt 混合加法保序；fa53 广播） *)
Theorem uabp3_amt_bs_lpc : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO a b c d Hab Hcd).
Qed.

End UabP3AmtAbsLpc.

(* ################ 收尾：文尾逐件假设面打印（G2 留痕） ################ *)
Print Assumptions uabp3_amt_expf_bundle.
Print Assumptions uabp3_lsum_ext.
Print Assumptions uabp3_lsum_add.
Print Assumptions uabp3_lsum_zero.
Print Assumptions uabp3_lsum_fubini_gen.
Print Assumptions uabp3_amt_sum_eq_list_idt.
Print Assumptions uabp3_amt_bs_swap.
Print Assumptions uabp3_amt_bs_abs.
Print Assumptions uabp3_amt_bs_lpc.

(* ============================ §7 uabp3_cmk_sel_lpc / uabp3_cmk_time_lpc / uabp3_cmk_sumf_bundle 语句面 ============================ *)
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import AttnDoeblin.
Require Import fa53_compat_abs.
Require TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ################ 段L：lt_plus_compat_lt_le 双节同名槽（N3·坑2 拆分） ##
   槽 L79（CmkMixSelect）与 L736（CmkMixTime）语句逐字同形。抽象 req 面   *)
(*   混合形不可内证（源版本头注已证结论：req 类字段仅 strict-strict 形），      *)
(*   转换＝装配桥实例供给形态（T2b 节7 同款诚实登记）：R 取典范载体、    *)
(*   RIS 取 tsi_rie_setoid 装配桥（req 幺等）后由 fa53 件1 直接供给——       *)
(*   抽象 R 上混合保序不 discharge，典范载体上成立。                     *)

Theorem uabp3_cmk_sel_lpc :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0) a b ->
    @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0) c d ->
    @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
        (@RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0) a c)
        (@RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0) b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

(* 槽 L736（CmkMixTime 同语句；坑2 双节拆分第二坐标同构件） *)
Corollary uabp3_cmk_time_lpc :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0) a b ->
    @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0) c d ->
    @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
        (@RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0) a c)
        (@RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0) b d).
Proof.
  exact uabp3_cmk_sel_lpc.
Qed.

(* ################ 段S：CmkMixTime 求和六槽转换（sumd 实例供给直接供给） ####
   槽 L743/L745/L748/L751（sum_ext/linear/add/le，N1×4）＋L767           *)
(*   （bs_swap，N2）＋L772（sum_eq_list，N1）。源版本槽以抽象 sumf 声明， *)
(*   转换读法＝sumf ↦ sumd_sumf S0 en（UpReqSumD 具体有限和实例，        *)
(*   Context R/RIS 与源版本同形——抽象泛型面直接供给，零实例化降格）。          *)

Section UabP3CmkSumFeed.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S0 : Set.
Variable enum0 : list S0.

(* 四槽封装件（sum_ext/linear/add/le 一件实例化消解形，判例 A 形 封装口径） *)
Theorem uabp3_cmk_sumf_bundle :
  sigT (fun sumf : (S0 -> R) -> R =>
    And (forall f g : S0 -> R,
           (forall s : S0, req (f s) (g s)) -> req (sumf f) (sumf g))
    (And (forall (a : R) (f : S0 -> R),
           req (sumf (fun s : S0 => mult a (f s))) (mult a (sumf f)))
    (And (forall f g : S0 -> R,
           req (sumf (fun s : S0 => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (forall f g : S0 -> R,
           (forall s : S0, le (f s) (g s)) -> le (sumf f) (sumf g))))).
Proof.
  exact (existT _ (sumd_sumf S0 enum0)
          (pair (sumd_sum_ext S0 enum0)
          (pair (sumd_sum_linear S0 enum0)
          (pair (sumd_sum_add S0 enum0) (sumd_sum_le S0 enum0))))).
Qed.

(* 槽 L772 语句逐字（sumf ↦ sumd_sumf 读法）：sumd 折叠机与 rsq 机同形 *)
(*   自持，两步定义级胶（cons 支 req_plus_compat＋归纳肢）闭合。        *)
Lemma uabp3_sumd_rsq_agree : forall (en : list S0) (g : S0 -> R),
  req (sumd_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof.
  intros en g. induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl.
    exact (req_plus_compat (g x) (g x)
             (sumd_list_sum S0 g t) (rsq_bs_list_sum S0 g t)
             (req_refl (g x)) IH).
Qed.

Theorem uabp3_cmk_sum_eq_list : forall g : S0 -> R,
  req (sumd_sumf S0 enum0 g) (rsq_bs_list_sum S0 g enum0).
Proof.
  intro g.
  exact (uabp3_sumd_rsq_agree enum0 g).
Qed.

(* 槽 L767 语句逐字（sumf ↦ sumd_sumf 读法）：sumd_sum_swap 直接供给        *)
(*   （UpReqSumD:384 req 面列表 Fubini；判例 同判，p7d:107 为 Id 面     *)
(*   同构坐标）。                                                       *)
Theorem uabp3_cmk_bs_swap : forall f : S0 -> S0 -> R,
  req (sumd_sumf S0 enum0 (fun s : S0 => sumd_sumf S0 enum0 (fun s' : S0 => f s s')))
      (sumd_sumf S0 enum0 (fun s' : S0 => sumd_sumf S0 enum0 (fun s : S0 => f s s'))).
Proof.
  intro f.
  exact (sumd_sum_swap S0 enum0 f).
Qed.

End UabP3CmkSumFeed.

(* ################ 段A：bs_abs 槽转换（fa53 件3·装配桥直接供给） ###########
   槽 L770 语句逐字（req 面 |a| 幂等）。抽象 req 面无同款无条件件        *)
(*   （req 面 abs 字段仅 Bishop 逐 eps 形邻接），转换＝装配桥实例供给    *)
(*   形态（T2b 节7 同款诚实登记）：典范载体上由 fa53 件3 直接供给。          *)

Theorem uabp3_cmk_bs_abs :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a : @S01_BaseRing.R RI0),
    @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
        (@RealInterfaceEnhancedMod.zero (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0)) a ->
    @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI0)
        (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
        (@RealInterfaceEnhancedMod.abs (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0) a) a.
Proof.
  intros RI0 DO0 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

(* ################ 段W：W1 邻接旁证件（最近可达形·非实例化消解） #############
   邻接 N 坐标 csm_abs_sum_le_eps@UpReqConcSoftmax:248 逐字直供：        *)
(*   Bishop 逐 eps 形 |Σf| ≤ Σ|f| + eps（柯西 Real 具体层）。本件为      *)
(*   W1（:754）墙登记的「最近可达形」注记物证——不构成 :754 的实例化消解，      *)
(*   plain le 形抽象 req 面三角维持 W（头注机理注）。                    *)

Theorem uabp3_cmk_abs_sum_le_recent : forall (S0 : Set) (en : list S0)
                                             (f : S0 -> Real) (eps : Real),
  lt zero eps ->
  le (abs (csm_sumf S0 en f))
     (plus (csm_sumf S0 en (fun s : S0 => abs (f s))) eps).
Proof.
  intros S0 en f eps Heps.
  exact (csm_abs_sum_le_eps S0 en f eps Heps).
Qed.

(* ################ 收尾：文尾逐件假设面打印（G2 留痕） ################ *)
Print Assumptions uabp3_cmk_sel_lpc.
Print Assumptions uabp3_cmk_time_lpc.
Print Assumptions uabp3_cmk_sumf_bundle.
Print Assumptions uabp3_cmk_sum_eq_list.
Print Assumptions uabp3_cmk_bs_swap.
Print Assumptions uabp3_cmk_bs_abs.
Print Assumptions uabp3_cmk_abs_sum_le_recent.

(* ============================ §8 beta 正性（任意正有理 q 的 real_const 实例）、参考分布逐点正性与归一性（单点 SumOver 实例世界）、eta 参数的数据位/正性 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpAblT13c_G13.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Extraction.

(* ################ beta_pos 的供给：正有理常数的构造 ######################## *)
(* 假设位形：S05:45 lt zero beta（beta 为数据位）。供给定理给出 Real 载体实例：    *)
(* 任取正有理 q，beta := real_const q 满足该正性位形。                           *)
Theorem p1t1_beta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof.
  intros q Hq.
  assert (Hq' : Qlt (0#1)%Q q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists (q * (1#2)%Q).
  split.
  - apply Qlt_to_QltT.
    assert (H2 : Qlt (0 * (1#2)%Q) (q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q q (1#2)%Q H02 Hq'). }
    setoid_rewrite Qmult_0_l in H2. exact H2.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hc. setoid_rewrite Hz.
    assert (Hr1 : (q - 0)%Q == (1#1)%Q * q) by ring. setoid_rewrite Hr1.
    assert (Hr2 : q * (1#2)%Q == (1#2)%Q * q) by ring. setoid_rewrite Hr2.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q q Hq' Hhalf).
Qed.

(* ################ normalized 的供给：单点实例世界上的常值一核 ################ *)
(* 假设位形：S05:48 Id (sum_over_S pi_ref) one（S05:785 pi_old_norm 同形）。      *)
(* 单点 SumOver 实例世界：和退化为核元素取值，故常值一核的求和即 one。            *)
Theorem p1t1_pi_ref_norm_supply : forall RI0 : RealInterfaceEnhanced,
  Id (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
        (fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0)) (@one RI0).
Proof. intros RI0. exact id_refl. Qed.

(* ################ positive_dist 的供给：常值一核逐点正 ###################### *)
(* 假设位形：S05:47 forall s, lt zero (pi_ref s)；由接口字段 one_pos 直接推得。   *)
Theorem p1t1_pi_ref_pos_supply : forall (RI0 : RealInterfaceEnhanced)
    (s : @S RI0 (@uab_ssUnit (@RI_base RI0))),
  @lt RI0 (@zero RI0)
    ((fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0) s).
Proof. intros RI0 s. apply (@one_pos RI0). Qed.

(* ################ eta 数据位、eta_pos、eta_le_one 共享：eta 见证族（(0,1) 内有理族） ## *)
Definition p1t1_eta_family (q : Q) : Real := real_const q.

(* ################ eta_pos 的供给：见证族正性（证明与 beta_pos 共享） ########## *)
Theorem p1t1_eta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (p1t1_eta_family q).
Proof. intros q Hq. exact (p1t1_beta_pos_supply q Hq). Qed.

(* ################ eta_le_one 的供给：见证族不超过一 ######################## *)
Theorem p1t1_eta_le_one_supply : forall q : Q, QltT q (1#1)%Q ->
  real_le (p1t1_eta_family q) real_one.
Proof.
  intros q Hq.
  assert (Hq' : Qlt q (1#1)%Q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  assert (H0m : Qlt 0%Q (1 - q)%Q)
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (H0 : Qlt 0 ((1#1)%Q + (- q)))
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (Hlt : real_lt (real_const q) real_one).
  { unfold real_lt.
    exists ((1 - q) * (1#2)%Q)%Q.
    split.
    - apply Qlt_to_QltT.
      assert (H2a : Qlt (0 * (1#2)%Q) ((1 - q)%Q * (1#2)%Q)).
      { exact (Qmult_lt_compat_r 0%Q (1 - q)%Q (1#2)%Q H02 H0m). }
      setoid_rewrite Qmult_0_l in H2a. exact H2a.
    - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
      assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
      assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc. setoid_rewrite Ho.
      assert (HrB : (1 - q)%Q == (1#1)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrB at 2.
      assert (HrA : (1 - q)%Q * (1#2)%Q
                    == (1#2)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrA.
      exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q ((1#1)%Q + (- q)) H0 Hhalf). }
  unfold real_le.
  exact (@inl (real_lt (real_const q) real_one)
              (real_eq (real_const q) real_one) Hlt).
Qed.

(* ################ eta 数据位的供给：sigT 封装（见证与性质合取封装） ########## *)
(* 假设位形：S05:2530 eta : 数据位。对 (0,1) 内任取 q 给出带证的 eta 见证。       *)
Theorem p1t1_eta_supply : forall q : Q, QltT (0#1)%Q q -> QltT q (1#1)%Q ->
  sigT (fun e : Real => And (real_lt real_zero e) (real_le e real_one)).
Proof.
  intros q Hq0 Hq1.
  exact (existT (fun e : Real => And (real_lt real_zero e) (real_le e real_one))
                (p1t1_eta_family q)
                ((p1t1_eta_pos_supply q Hq0), (p1t1_eta_le_one_supply q Hq1))).
Qed.

(* #### 端点补全：eta := one（区间 (0,1] 的右端点） ########################## *)
Theorem p1t1_eta_one_pos : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Qed.

Theorem p1t1_eta_one_le_one : real_le real_one real_one.
Proof. exact (real_le_refl real_one). Qed.

(* ---- 提取核验：p1t1_eta_pick 的计算内容提取 ----------------------------- *)
Definition p1t1_eta_pick (n : nat) : Q := (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp1t1_g3out".
Extraction "p1t1_G3_AlignCert.ml" p1t1_eta_pick.

(* ---- 假设闭包核验：以下各定理的假设闭包应为空（Closed） ---- *)
Print Assumptions p1t1_beta_pos_supply.
Print Assumptions p1t1_pi_ref_norm_supply.
Print Assumptions p1t1_pi_ref_pos_supply.
Print Assumptions p1t1_eta_pos_supply.
Print Assumptions p1t1_eta_le_one_supply.
Print Assumptions p1t1_eta_supply.
Print Assumptions p1t1_eta_one_pos.
Print Assumptions p1t1_eta_one_le_one.

(* ============================ §9 使命：GRPO 与审计假设簇九束的供给实例—— ============================ *)
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

(* ################ 段一：S05 对齐节 PPO 参数簇（策略正性、归一化、 ############
   优势函数、ε 正性）：语境为 S05 Section Alignment（语境 {RI}{SS}{SO}）；
   L783-789 五条参量声明为接口参数实形。 *)

Section P1T2PpoSlots.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let lt := @lt RI.
Let le := @le RI.
Let plus := @plus RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* 策略载体：常数一函数（S05:783 pi_old : S -> R 数据位实例） *)
Definition p1t2_pi_old_c : S -> R := fun _ : S => one.

(* pi_old_pos 参数位供给（S05:784 实形 forall s, lt zero (pi_old s)）：由 one_pos 逐点推得 *)
Theorem p1t2_B11_pi_old_pos_witness : forall s : S, lt zero (p1t2_pi_old_c s).
Proof.
  intro s.
  unfold p1t2_pi_old_c.
  exact one_pos.
Qed.

(* pi_old_norm 参数位（S05:785 实形 Id (sum_over_S pi_old) one）：接口层不可      *)
(* 构造，改写为显式前提下的条件形，参数形保持原样。                            *)
Theorem p1t2_B12_pi_old_norm_pack :
  forall pi_old : S -> R,
    Id (sum_over_S pi_old) one -> Id (sum_over_S pi_old) one.
Proof. intros pi_old Hn. exact Hn. Qed.

(* 优势函数载体：常数零函数（S05:786 advantage_fn : S -> R 数据位实例；       *)
(* 其伴生的逐点非负前提属另一假设束，不在本件范围内）                         *)
Definition p1t2_advantage_c : S -> R := fun _ : S => zero.

Theorem p1t2_B13_advantage_c_witness : forall s : S, Id (p1t2_advantage_c s) zero.
Proof.
  intro s.
  unfold p1t2_advantage_c.
  exact (@id_refl _ zero).
Qed.

(* ε 载体：取常数一（S05:788 epsilon : R 数据位实例；正性由 one_pos 给出） *)
Definition p1t2_epsilon_c : R := one.

(* epsilon_pos 参数位供给（S05:789 实形 lt zero epsilon）：由 one_pos 直接推得 *)
Theorem p1t2_B14_epsilon_pos_witness : lt zero p1t2_epsilon_c.
Proof. exact one_pos. Qed.

End P1T2PpoSlots.

(* ################ 段二：S05 GRPO 节枚举簇（群数据、群覆盖、群大小） ###########
   语境为 S05 Section GRPO（语境 {RI}{SS}{SO}）；L5102-5112 接口参数实形：
   of_nat 嵌入（O => zero；后继为一加）、Group、枚举表、覆盖与大小。 *)

Section P1T2GrpoSlots.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let lt := @lt RI.
Let plus := @plus RI.

(* S05:5102-5106 of_nat 的对应嵌入（nat 到 R，构造性计数） *)
Fixpoint p1t2_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (p1t2_of_nat n')
  end.

(* 群数据载体：二元枚举集 p1t2_g2、枚举表与奖励数据位（Group/group_enum/
   reward_group 三件的实例；覆盖性由 p1t2_B16 单列）。 *)
Inductive p1t2_g2 : Set :=
| G0 : p1t2_g2
| G1 : p1t2_g2.

Definition p1t2_group_enum : list p1t2_g2 := G0 :: G1 :: nil.
Definition p1t2_reward_group_c : p1t2_g2 -> R := fun _ : p1t2_g2 => one.

Theorem p1t2_B15_group_data_witness :
  forall i : p1t2_g2, Id (p1t2_reward_group_c i) one.
Proof.
  intro i.
  unfold p1t2_reward_group_c.
  exact (@id_refl _ one).
Qed.

(* group_cover 参数位供给（S05:5109 实形 forall i, InT i group_enum）：覆盖由枚举表 *)
(* 构造，两分支分别由表头与后继位置构成（InT_here/InT_next 递推）。 *)
Theorem p1t2_B16_group_cover_witness : forall i : p1t2_g2, InT i p1t2_group_enum.
Proof.
  unfold p1t2_group_enum. intro i. destruct i as [| ].
  - apply InT_here.
  - apply InT_next. apply InT_here.
Qed.

(* group_size_pos 参数位供给（S05:5111 实形 lt zero (of_nat group_size)）：群大小  *)
(* 为二，二的嵌入等于一加一（经零加恒等式重排），其正性由 plus_positive 推得。  *)
Theorem p1t2_B17_group_size_pos_witness :
  lt zero (p1t2_of_nat (length p1t2_group_enum)).
Proof.
  unfold p1t2_group_enum.
  apply (lt_id_r zero (plus one one)).
  - exact (id_cong (fun w : R => plus one w) (id_sym (plus_zero one))).
  - apply plus_positive.
    + exact one_pos.
    + exact one_pos.
Qed.

End P1T2GrpoSlots.

(* ################ 段三：S13 审计投影节证书位（Hp_norm/Hp_pos/HZ） ############
   语境为 S13 Section KLProjection（语境 {RI}{SS}{SO}）；
   L2023/2024/2028 为接口参数实形；normalized/positive_dist 取 S04 自由能节导出形。 *)

Section P1T2AuditSlots.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* 过审质量 Z_aud 载体（S13:2026-2027 实形：过审位取 p，否决位取零） *)
Definition p1t2_Z_aud (p : S -> R) (post_aud : S -> bool) : R :=
  sum_over_S (fun s : S => if post_aud s then p s else zero).

(* 布尔过审位辅助引理：若过审标记为真，则过滤项与该点原值等同（Set 层直接构成） *)
Definition p1t2_bool_true_id {A : Set} (x y : A) (b : bool) (Hb : Id true b) :
  Id (if b then x else y) x :=
  match Hb in Id _ b' return Id (if b' then x else y) x with
  | id_refl => id_refl
  end.

(* Hp_norm/Hp_pos/HZ 参数位供给（S13:2023/2024/2028 实形）：
   归一化与逐点正两前件显式给出（接口面不可构造，注记见头部）；
   HZ 在「逐点非负＋逐点下界」显式前件下导出——过滤函数逐点非负分两支
   证得（过审支：逐点正降为非负；否决支：零的自反），再加过审点下界。 *)
Theorem p1t2_B21_HZ_pack :
  forall (p : S -> R)
         (Hp_norm : normalized p)
         (Hp_pos : positive_dist p)
         (post_aud : S -> bool)
         (Hlower : forall f : S -> R,
                     (forall s : S, le zero (f s)) ->
                     forall s0 : S, lt zero (f s0) -> lt zero (sum_over_S f))
         (s0 : S) (Haud0 : Id (post_aud s0) true),
    lt zero (p1t2_Z_aud p post_aud).
Proof.
  intros p Hp_norm Hp_pos post_aud Hlower s0 Haud0.
  refine (Hlower (fun s : S => if post_aud s then p s else zero) _ s0 _).
  - intro s. destruct (post_aud s).
    + exact (lt_le_iff zero (p s) (inl (Hp_pos s))).
    + exact (le_refl zero).
  - exact (lt_id_r zero (p s0) _
            (id_sym (p1t2_bool_true_id (p s0) zero (post_aud s0) (id_sym Haud0)))
            (Hp_pos s0)).
Qed.

End P1T2AuditSlots.

(* ################ 段四：UpReqDist ReqFEP 节自由能常数位（D/D_pos/Z/Z_pos） ######
   接口参数为 UpReqDist L1022-1025（req 系 §3.3 前件）；语境同构重建：抽象载体配
   RealInterfaceEnhancedSetoid（纯接口前件，具体实例不进入依赖面）。
   本件以抽象 req 载体陈述（显式 forall 前件，参数形逐字）：D 取常数一，
   Z 取 Boltzmann 配分和，其正性由配分和正性参数与 exp_neg_pos 推得。
   （取抽象载体的原因：具体 Real 实例形的提取依赖闭包会连带引入
   Real 实例的整体构造，超出本件的提取核验范围。） *)

Import RealInterfaceEnhancedMod.

Section P1T2ReqFEP.

Context {R0 : Set} {RIS : RealInterfaceEnhancedSetoid R0}.

(* D 位载体：D 取常数一（其正性前件在供给定理中显式给出） *)
Definition p1t2_b27_D_one : R0 := one.

(* D/D_pos/Z/Z_pos 参数位供给（UpReqDist:1022-1025 实形）：配分条件在载体下由
   req 自反成立；Z 取 Boltzmann 配分和，其正性 Z_pos 由配分和正性参数与
   exp_neg_pos 推得。 *)
Theorem p1t2_B27_free_energy_constants_supply :
  forall (S0 : Set) (sumf : (S0 -> R0) -> R0) (base_loss : S0 -> R0),
    (forall f : S0 -> R0, (forall s : S0, lt zero (f s)) -> lt zero (sumf f)) ->
    forall HDpos : lt zero p1t2_b27_D_one,
      lt zero (sumf (fun s : S0 =>
               exp_neg (mult (inv_pos p1t2_b27_D_one HDpos) (base_loss s)))).
Proof.
  intros S0 sumf base_loss Hfsum HDpos.
  exact (Hfsum
           (fun s : S0 =>
              exp_neg (mult (inv_pos p1t2_b27_D_one HDpos) (base_loss s)))
           (fun s : S0 =>
              exp_neg_pos (mult (inv_pos p1t2_b27_D_one HDpos) (base_loss s)))).
Qed.

End P1T2ReqFEP.

(* ############ 假设闭包核验：以下各定理的假设闭包应为空（Closed） ############## *)
Print Assumptions p1t2_B11_pi_old_pos_witness.
Print Assumptions p1t2_B12_pi_old_norm_pack.
Print Assumptions p1t2_B13_advantage_c_witness.
Print Assumptions p1t2_B14_epsilon_pos_witness.
Print Assumptions p1t2_B15_group_data_witness.
Print Assumptions p1t2_B16_group_cover_witness.
Print Assumptions p1t2_B17_group_size_pos_witness.
Print Assumptions p1t2_B21_HZ_pack.
Print Assumptions p1t2_b27_D_one.
Print Assumptions p1t2_B27_free_energy_constants_supply.

(* ============================ §10 使命：论文2 消融件的求和与正性依赖模块：以论文1 已 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqSumD.
Require Import UpReqSteadyThermo.
Require Import UpAblZposReal.
Require Import UpAblEps66Sum.
Require Import UpAblEps49List.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 求和接口件：复述 e66s_sumf 的外延/保序/加法/线性四条语句形，       *)
(*   求和算子参数取其特化 p2f_sumf                                      *)
(* ============================================================ *)
Section P2FeedA.

Context (S0 : Set).
Context (enum0 : list S0).

(* 求和算子实例 p2f_sumf：e66s_sumf 在世界（S0, enum0）上的特化          *)
Definition p2f_sumf (f : S0 -> Real) : Real := e66s_sumf S0 enum0 f.

(** p2f_ext·外延：逐点相等的两函数列其 p2f_sumf 和相等；由 e66s_real_sum_over_S_ext 立得。 *)
Theorem p2f_ext :
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (p2f_sumf f) (p2f_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_ext S0 enum0 f g H).
Qed.

(** p2f_le·保序：逐点序不降的两函数列其 p2f_sumf 和保序，且无非空前提；由 e66s_real_sum_over_S_le 立得。 *)
Theorem p2f_le :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (p2f_sumf f) (p2f_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_le S0 enum0 f g H).
Qed.

(** p2f_add·加法：逐点相加后求和，等于分别求和后相加；由 e66s_real_sum_over_S_add 立得。 *)
Theorem p2f_add :
  forall (f g : S0 -> Real),
    real_eq (p2f_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (p2f_sumf f) (p2f_sumf g)).
Proof.
  intros f g.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** p2f_linear·线性：数乘与求和可交换；由 sumd_sum_linear 立得           *)
(*   （本世界中 e66s_sumf 与 sumd_sumf 逐点重合）。                      *)
Theorem p2f_linear :
  forall (a : Real) (f : S0 -> Real),
    real_eq (p2f_sumf (fun s : S0 => real_mult a (f s)))
            (real_mult a (p2f_sumf f)).
Proof.
  intros a f.
  exact (sumd_sum_linear S0 enum0 a f).
Qed.

End P2FeedA.

(* ============================================================ *)
(* §2 折叠桥 p2f_lsum_bridge 与外延传输 p2f_ext_lsum（本件实质新证）     *)
(* ============================================================ *)

(** p2f_lsum_bridge·折叠桥：e66s_sumf 折叠与 real_list_sum 折叠对同一    *)
(*   表逐点 real_eq 相等。证明：对列表 l 归纳。                             *)
Theorem p2f_lsum_bridge :
  forall (X : Set) (l : list X) (f : X -> Real),
    real_eq (e66s_sumf X l f) (real_list_sum X f l).
Proof.
  intros X l f.
  unfold e66s_sumf.
  induction l as [| w t IH]; simpl.
  - (* 情形 l = []：unfold e66s_sumf 化简后两侧均为 real_zero，由 real_eq_refl。 *)
    apply real_eq_refl.
  - (* 归纳步：由 l 到 w :: t——首项 f w 经 real_eq_refl，尾和由归纳假设 IH，经 real_eq_plus_compat_adapt 合成。 *)
    exact (RealSetoid.real_eq_plus_compat_adapt
             (f w) (f w)
             (sumd_list_sum X f t) (real_list_sum X f t)
             (real_eq_refl (f w)) IH).
Qed.

(** p2f_ext_lsum·外延传输：经 real_eq_sym 与 p2f_lsum_bridge 换向，      *)
(*   再由 e66s_real_sum_over_S_ext 与 real_eq_trans 三步合成。            *)
Theorem p2f_ext_lsum :
  forall (X : Set) (l : list X) (f g : X -> Real),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X l f g H.
  exact (real_eq_trans (real_list_sum X f l) (e66s_sumf X l f)
                       (real_list_sum X g l)
           (real_eq_sym (real_list_sum X f l) (e66s_sumf X l f)
                        (p2f_lsum_bridge X l f))
           (real_eq_trans (e66s_sumf X l f) (e66s_sumf X l g)
                          (real_list_sum X g l)
              (e66s_real_sum_over_S_ext X l f g H)
              (p2f_lsum_bridge X l g))).
Qed.

(* ============================================================ *)
(* §3 稳态方程两件：求和算子参数取 e66s 实例，exact 一步证得             *)
(* ============================================================ *)

(** p2f_steady_attn_direct：复述 real_steady_state_boltzmann_attn        *)
(*   （注意力侧稳态方程）；求和算子参数取 e66s 实例，前提与原定理一致。   *)
Theorem p2f_steady_attn_direct :
  forall (S0 : Set) (enum0 : list S0)
    (D : Real) (D_pos : real_lt real_zero D) (energy : S0 -> Real)
    (Z_thermo : Real) (Z_thermo_pos : real_lt real_zero Z_thermo)
    (T : S0 -> S0 -> Real),
  (forall s s' : S0,
     real_eq (real_mult
                (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s')
                (T s' s))
             (real_mult
                (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s)
                (T s s'))) ->
  (forall s : S0,
     real_eq (e66s_sumf S0 enum0 (fun s' : S0 => T s s')) real_one) ->
  forall s : S0,
    real_eq (e66s_sumf S0 enum0
               (fun s' : S0 =>
                  real_mult (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s')
                            (T s' s)))
            (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s).
Proof.
  intros S0 enum0 D D_pos energy Z_thermo Z_thermo_pos T Hdb Hnorm s.
  exact (real_steady_state_boltzmann_attn S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (fun (a : Real) (f : S0 -> Real) => sumd_sum_linear S0 enum0 a f)
           D D_pos energy Z_thermo Z_thermo_pos T Hdb Hnorm s).
Qed.

(** p2f_steady_thermo_direct：复述 real_steady_state_boltzmann           *)
(*   （热力学侧稳态方程，real_boltzmann_prob 载体）；求和算子参数         *)
(*   取 e66s 实例；前提（配分正性、核归一化、详细平衡）与原定理一致，     *)
(*   原定理签名未含的配分相等与非负前提如实缺省。                         *)
Theorem p2f_steady_thermo_direct :
  forall (S0 : Set) (enum0 : list S0)
    (energy : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_r : Real) (Z_r_pos : real_lt real_zero Z_r)
    (T : S0 -> S0 -> Real),
  (forall s : S0,
     real_eq (e66s_sumf S0 enum0 (fun s' : S0 => T s s')) real_one) ->
  (forall s s' : S0,
     real_eq (real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s) (T s s'))
             (real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s') (T s' s))) ->
  forall s : S0,
    real_eq (e66s_sumf S0 enum0
               (fun s' : S0 =>
                  real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s') (T s' s)))
            (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s).
Proof.
  intros S0 enum0 energy D D_pos Z_r Z_r_pos T Hnorm Hdb s.
  exact (real_steady_state_boltzmann S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (fun (a : Real) (f : S0 -> Real) => sumd_sum_linear S0 enum0 a f)
           energy D D_pos Z_r Z_r_pos T Hnorm Hdb s).
Qed.

(* ============================================================ *)
(* §4 最小概率核归一化：real_minp_markov_kernel_normalized 的显式        *)
(*   实例化；判定 Or 形接口 kdec 与正性前提 tsum_pos 按原签名如实保留     *)
(* ============================================================ *)
Theorem p2f_minp_kernel_direct :
  forall (S0 : Set) (enum0 : list S0)
    (tf : S0 -> Real)
    (keep : list S0 -> S0 -> Set)
    (kdec : forall (prefix : list S0) (w : S0),
              Or (keep prefix w) (Not (keep prefix w)))
    (tsum_pos : forall prefix : list S0,
                  real_lt real_zero
                    (real_minp_temp_sum S0 enum0 tf keep kdec prefix)),
  forall prefix : list S0,
    real_eq (real_list_sum S0
               (fun w : S0 =>
                  real_minp_markov_kernel S0 enum0 tf keep kdec tsum_pos prefix w)
               enum0)
            real_one.
Proof.
  intros S0 enum0 tf keep kdec tsum_pos prefix.
  exact (real_minp_markov_kernel_normalized S0 enum0 tf keep kdec tsum_pos prefix).
Qed.

(* ============================================================ *)
(* §5 配分正性组：由 e49l_partition_pos 与 zabr_sum_over_S_pos 供给；    *)
(*   相对 real_Z_thermo_pos 接口族多一项非空前提 Hnn：Not (Id l nil)      *)
(* ============================================================ *)

(** p2f_partition_pos_slot·配分正性：非空表上，逐点取                    *)
(*   real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)) 的 e49l 和为正；由 e49l_partition_pos 立得。 *)
Theorem p2f_partition_pos_slot :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
    real_lt real_zero
      (e49l_sumf X l (fun s : X =>
         real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))).
Proof.
  intros X l Hnn e D D_pos.
  exact (zabr_sum_over_S_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
           l Hnn
           (fun s : X => real_exp_neg_pos
              (real_mult (real_inv_pos D D_pos) (e s)))).
Qed.

(** p2f_sum_pos_preserved_list·正性保持：非空表上逐项取正的函数列        *)
(*   其 e49l_sumf 和取正；由 zabr_sum_over_S_pos 立得（非空前提同上）。   *)
Theorem p2f_sum_pos_preserved_list :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil)) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (e49l_sumf X l f).
Proof.
  intros X l Hnn f Hf.
  exact (zabr_sum_over_S_pos X f l Hnn Hf).
Qed.

(** p2f_gibbs_partition_pos_direct：real_attention_is_gibbs 的正性       *)
(*   参数直接取 zabr_sum_over_S_pos 与 e49l_partition_pos，               *)
(*   exact 一步证得；其余前提（单位温度、能量为负 logit、配分相等）       *)
(*   与原定理一致。                                                      *)
Theorem p2f_gibbs_partition_pos_direct :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (D : Real) (D_pos : real_lt real_zero D) (e z : X -> Real),
  real_eq (real_inv_pos D D_pos) real_one ->
  (forall s : X, real_eq (e s) (real_opp (z s))) ->
  real_eq (real_Z_thermo X (e49l_sumf X l) D D_pos e)
          (real_partition_function X (e49l_sumf X l) z) ->
  forall s : X,
    real_eq (real_softmax X (e49l_sumf X l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  zabr_sum_over_S_pos X f l Hnn Hf) z s)
            (real_boltzmann_dist_attn X (e49l_sumf X l) D D_pos e
               (e49l_partition_pos X l Hnn e D D_pos) s).
Proof.
  intros X l Hnn D D_pos e z Hunit Henergy HZZ s.
  exact (real_attention_is_gibbs X (e49l_sumf X l)
           (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
              zabr_sum_over_S_pos X f l Hnn Hf)
           D D_pos e z (e49l_partition_pos X l Hnn e D D_pos)
           Hunit Henergy HZZ s).
Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 应全部 Closed（零外部未证假设）      *)
(* ============================================================ *)
Print Assumptions p2f_ext.
Print Assumptions p2f_le.
Print Assumptions p2f_add.
Print Assumptions p2f_linear.
Print Assumptions p2f_lsum_bridge.
Print Assumptions p2f_ext_lsum.
Print Assumptions p2f_steady_attn_direct.
Print Assumptions p2f_steady_thermo_direct.
Print Assumptions p2f_minp_kernel_direct.
Print Assumptions p2f_partition_pos_slot.
Print Assumptions p2f_sum_pos_preserved_list.
Print Assumptions p2f_gibbs_partition_pos_direct.

(* ============================================================ *)
(* 提取区：可计算件 p2f_sumf、p2f_lsum_bridge、p2f_ext_lsum、            *)
(*   p2f_partition_pos_slot 提取；谓词层语句件以假设审计替代提取。        *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_tz2b_g3out".
Separate Extraction p2f_sumf p2f_lsum_bridge p2f_ext_lsum p2f_partition_pos_slot.

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition Or (A B : Set) : Set := A + B.
Definition Not (A : Set) : Set := A -> Empty_set.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

Definition id_cong {A B : Set} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y) :=
  match p with
  | id_refl => id_refl
  end.

Definition id_cong2 {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
                    (p : Id x x') (q : Id y y') : Id (f x y) (f x' y') :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* 构造性 list 成员关系（Set 层，S01 同型） *)
Inductive InT {A : Set} (x : A) : list A -> Set :=
| InT_here : forall l, InT x (x :: l)
| InT_next : forall y l, InT x l -> InT x (y :: l).

Arguments InT_here {A} x l.
Arguments InT_next {A} x y l H.

(* ################ 第 1 部：nat 载体极小算术 ################################# *)

Definition zero : nat := O.
Definition one : nat := Datatypes.S O.

Fixpoint rplus (a b : nat) : nat :=
  match a with
  | O => b
  | Datatypes.S a' => Datatypes.S (rplus a' b)
  end.

Lemma plus_zero : forall b : nat, Id (rplus b zero) b.
Proof.
  intro b. induction b as [| b IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_S_swap : forall a b : nat,
  Id (rplus a (Datatypes.S b)) (Datatypes.S (rplus a b)).
Proof.
  intro a. intro b. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_comm : forall a b : nat, Id (rplus a b) (rplus b a).
Proof.
  intro a. intro b. induction a as [| a IH].
  - cbn [rplus]. apply (id_sym (plus_zero b)).
  - cbn [rplus]. apply (id_trans (id_cong (fun n : nat => Datatypes.S n) IH)).
    apply (id_sym (plus_S_swap b a)).
Qed.

(* 右结合先行形（下游使用链锁定方向） *)
Lemma plus_assoc : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus (rplus a b) c).
Proof.
  intros a b c. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_swap : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus b (rplus a c)).
Proof.
  intros a b c.
  exact (id_trans (plus_assoc a b c)                  (id_trans (id_cong2 rplus (plus_comm a b) (id_refl : Id c c))                            (id_sym (plus_assoc b a c)))).
Qed.

(* ################ 第 2 部：bool 二元世界与两判定接口实例 #################### *)

(* ---- 族A 判定核支件：bool 构造子冲突的空匹配消解 ---- *)

Lemma p2wb_true_ne_false : Not (Id true false).
Proof. intro h. exact (match h with end). Qed.

Lemma p2wb_false_ne_true : Not (Id false true).
Proof. intro h. exact (match h with end). Qed.

(* 族A 判定接口实例：S06 同款语句形（载体 bool），bool 判定经
   @inl/@inr 依赖消去，四支逐支构造性见证（非经典排除律）。 *)
Definition p2wb_token_eq_dec : forall a b : bool, Or (Id a b) (Not (Id a b)) :=
  fun a b =>
    match a as x return (Or (Id x b) (Not (Id x b))) with
    | true =>
        match b as y return (Or (Id true y) (Not (Id true y))) with
        | true => @inl (Id true true) (Not (Id true true)) id_refl
        | false => @inr (Id true false) (Not (Id true false)) p2wb_true_ne_false
        end
    | false =>
        match b as y return (Or (Id false y) (Not (Id false y))) with
        | true => @inr (Id false true) (Not (Id false true)) p2wb_false_ne_true
        | false => @inl (Id false false) (Not (Id false false)) id_refl
        end
    end.

(* ---- 族B 判定接口实例其一：常值形（keep 取常 unit，左支恒真） ---- *)

Definition p2wb_keep : bool -> Set := fun _ : bool => unit.

Definition p2wb_keep_dec : forall s : bool, Or (p2wb_keep s) (Not (p2wb_keep s)) :=
  fun _ : bool => @inl unit (Not unit) tt.

(* ---- 族B 判定接口实例其二：择留形（true 留 false 逐，两支俱非平凡） ---- *)

Definition p2wb_keep_sel : bool -> Set :=
  fun s => match s with
           | true => unit
           | false => Empty_set
           end.

Definition p2wb_keep_dec_sel : forall s : bool,
  Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s)) :=
  fun s =>
    match s as x return (Or (p2wb_keep_sel x) (Not (p2wb_keep_sel x))) with
    | true => @inl unit (Not unit) tt
    | false => @inr (Empty_set) (Not (Empty_set)) (fun h => match h with end)
    end.

(* ---- 伴生前件组（对应 S06 vocab 组与 K/S_enum 组） ---- *)

Definition p2wb_vocab : list bool := cons true (cons false nil).

(* vocab_nonempty 位：表构造子冲突的空匹配消解（索引取字面
   构造子形；与 p2wb_vocab 可转换） *)
Definition p2wb_vocab_nonempty : Not (Id (cons true (cons false nil)) nil) :=
  fun h => match h with end.

(* S_finite_cover 位：覆盖见证 *)
Definition p2wb_S_enum : list bool := cons true (cons false nil).

Definition p2wb_S_finite_cover : forall s : bool, InT s p2wb_S_enum :=
  fun s =>
    match s as x return (InT x (cons true (cons false nil))) with
    | true => InT_here true (cons false nil)
    | false => InT_next false true (cons false nil) (InT_here false nil)
    end.

(* ################ 第 3 部：枚举求和（SumOver 的有限世界实现面） ############# *)

Fixpoint p2wb_sum (f : bool -> nat) (l : list bool) : nat :=
  match l with
  | nil => zero
  | cons x rest => rplus (f x) (p2wb_sum f rest)
  end.

Lemma p2wb_sum_ext : forall f g l,
  (forall x, InT x l -> Id (f x) (g x)) -> Id (p2wb_sum f l) (p2wb_sum g l).
Proof.
  intros f g l H. induction l as [| x rest IH].
  - apply id_refl.
  - cbn [p2wb_sum].
    exact (id_cong2 rplus (H x (InT_here x rest))
                          (IH (fun i => fun Hi => H i (InT_next i x rest Hi)))).
Qed.

Lemma p2wb_sum_add : forall f g l,
  Id (p2wb_sum (fun x => rplus (f x) (g x)) l)
     (rplus (p2wb_sum f l) (p2wb_sum g l)).
Proof.
  intros f g l. induction l as [| x rest IH].
  - apply id_refl.
  - cbn [p2wb_sum].
    exact (id_trans (id_cong (fun t => rplus (rplus (f x) (g x)) t) IH)
                    (id_trans (id_sym (plus_assoc (f x) (g x)
                                                  (rplus (p2wb_sum f rest) (p2wb_sum g rest))))
                              (id_trans (id_cong (fun t => rplus (f x) t)
                                                 (plus_swap (g x) (p2wb_sum f rest) (p2wb_sum g rest)))
                                        (plus_assoc (f x) (p2wb_sum f rest)
                                                    (rplus (g x) (p2wb_sum g rest)))))).
Qed.

(* ################ 第 4 部：族B 实例化——KV 守恒结论逐式复现 ################# *)
(* 源文件：S06 tail_mass／evicted_partition／Z_thermo 与                    *)
(*   tail_plus_kept_full（Id (plus tail_mass evicted_partition)           *)
(*   Z_thermo）；实数轴取 nat 极小载体（实层判定面不在本件范围）。         *)

Definition p2wb_bfactor : bool -> nat :=
  fun s => match s with
           | true => rplus one one
           | false => one
           end.

Definition p2wb_tail_mass (kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s))) : nat :=
  p2wb_sum (fun s => match kd s with
                     | inl _ => zero
                     | inr _ => p2wb_bfactor s
                     end) p2wb_S_enum.

Definition p2wb_evicted_partition (kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s))) : nat :=
  p2wb_sum (fun s => match kd s with
                     | inl _ => p2wb_bfactor s
                     | inr _ => zero
                     end) p2wb_S_enum.

Definition p2wb_Z_thermo : nat := p2wb_sum p2wb_bfactor p2wb_S_enum.

(* 守恒恒等式复现（逐态配对＋p2wb_sum_add＋p2wb_sum_ext） *)
Theorem p2wb_tail_plus_kept_full :
  forall kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s)),
    Id (rplus (p2wb_tail_mass kd) (p2wb_evicted_partition kd)) p2wb_Z_thermo.
Proof.
  intro kd.
  assert (Hpt : forall s : bool,
             Id (rplus (match kd s with
                        | inl _ => zero
                        | inr _ => p2wb_bfactor s
                        end)
                       (match kd s with
                        | inl _ => p2wb_bfactor s
                        | inr _ => zero
                        end))
                (p2wb_bfactor s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - apply id_refl.
    - exact (plus_zero (p2wb_bfactor s)). }
  apply (id_trans (id_sym (p2wb_sum_add
                            (fun s => match kd s with
                                      | inl _ => zero
                                      | inr _ => p2wb_bfactor s
                                      end)
                            (fun s => match kd s with
                                      | inl _ => p2wb_bfactor s
                                      | inr _ => zero
                                      end)
                            p2wb_S_enum))).
  exact (p2wb_sum_ext
           (fun s => rplus (match kd s with
                            | inl _ => zero
                            | inr _ => p2wb_bfactor s
                            end)
                           (match kd s with
                            | inl _ => p2wb_bfactor s
                            | inr _ => zero
                            end))
           p2wb_bfactor p2wb_S_enum (fun s => fun _ => Hpt s)).
Qed.

(* 判定接口经择留实例消去：守恒结论以 p2wb_keep_dec_sel 实例化 *)
Theorem p2wb_tail_plus_kept_full_sel :
  Id (rplus (p2wb_tail_mass p2wb_keep_dec_sel) (p2wb_evicted_partition p2wb_keep_dec_sel))
     p2wb_Z_thermo.
Proof. exact (p2wb_tail_plus_kept_full p2wb_keep_dec_sel). Qed.

(* 实例消去的计算面：择留世界上尾质量＝1、保留质量＝2（全定义约简） *)
Theorem p2wb_sel_tail_mass_one : Id (p2wb_tail_mass p2wb_keep_dec_sel) one.
Proof. exact (@id_refl _ one). Qed.

Theorem p2wb_sel_partition_two : Id (p2wb_evicted_partition p2wb_keep_dec_sel) (rplus one one).
Proof. exact (@id_refl _ (rplus one one)). Qed.

(* ################ 第 5 部：族A 实例化——TopP 保留判定逐式复现 ############### *)
(* 源文件：S06 top_p_member（token_eq_dec x w 逐位分派，inl 支出 unit       *)
(*   元素）→ top_p_keep。阈值判定轴（抽象序可判位，族A 与 LPO 邻接，      *)
(*   不在本件范围）以 W/W_dec 参量全称化维持抽象；                       *)
(*   头位见证仅经 token_eq_dec 实例消去生成。                             *)

Section TopPMirror.

Variable W : bool -> nat -> Set.
Variable W_dec : forall (t : bool) (p : nat), Or (W t p) (Not (W t p)).

Fixpoint p2wb_top_member (p : nat) (l : list bool) : bool -> Set :=
  match l with
  | nil => fun _ : bool => Empty_set
  | cons h rest => fun x : bool =>
      match p2wb_token_eq_dec x h with
      | inl _ => unit
      | inr _ =>
          match W_dec h p with
          | inl _ => Empty_set
          | inr _ => p2wb_top_member p rest x
          end
      end
  end.

(* top_p_keep 复现：单元素枚举已序，排序轴平凡 *)
Definition p2wb_top_keep (p : nat) (l : list bool) : bool -> Set :=
  p2wb_top_member p l.

(* 经实例消去的头位保留见证：仅经 p2wb_token_eq_dec 消去，
   不使用 W_dec（阈值抽象轴零引用） *)
Theorem p2wb_top_keep_head_witness : forall (p : nat) (l : list bool),
  p2wb_top_keep p (cons true l) true.
Proof.
  intros p l.
  exact (match p2wb_token_eq_dec true true with         | inl _ => tt         | inr h => match h (id_refl : Id true true) with end         end).
Qed.

End TopPMirror.

(* ################ 第 6 部：泛用封装证书 p2wb_pack ########################### *)
(* 参数序＝S06 接口群声明序（族A：Token/vocab/vocab_nonempty/token_eq_dec；*)
(*   族B：S_enum/S_finite_cover/keep/keep_dec）。                         *)
(*                                                                      *)

Inductive p2wb_pack : Type :=
| p2wb_pack_intro :
    forall (Tok : Set) (vocab0 : list Tok)
           (vocab_nonempty : Not (Id vocab0 nil))
           (token_eq_dec : forall a b : Tok, Or (Id a b) (Not (Id a b)))
           (St : Set) (S_enum0 : list St)
           (S_finite_cover : forall s : St, InT s S_enum0)
           (keep : St -> Set)
           (keep_dec : forall s : St, Or (keep s) (Not (keep s))),
      p2wb_pack.

(* 供给其一：常值形（keep 取常 unit，keep_dec 取 @inl unit tt） *)
Theorem p2wb_supplied : p2wb_pack.
Proof.
  exact (p2wb_pack_intro bool p2wb_vocab p2wb_vocab_nonempty p2wb_token_eq_dec                         bool p2wb_S_enum p2wb_S_finite_cover                         p2wb_keep p2wb_keep_dec).
Qed.

(* 供给其二：择留形（两支俱非平凡） *)
Theorem p2wb_supplied_sel : p2wb_pack.
Proof.
  exact (p2wb_pack_intro bool p2wb_vocab p2wb_vocab_nonempty p2wb_token_eq_dec                         bool p2wb_S_enum p2wb_S_finite_cover                         p2wb_keep_sel p2wb_keep_dec_sel).
Qed.

(* ################ 第 7 部：提取面判定核与核↔接口正确性证书 ################# *)

Definition p2wb_tok_dec_core (i j : bool) : bool :=
  match i with
  | true =>
      match j with
      | true => true
      | false => false
      end
  | false =>
      match j with
      | true => false
      | false => true
      end
  end.

Lemma p2wb_tok_dec_core_correct : forall i j : bool,
  match p2wb_token_eq_dec i j with
  | inl _ => Id (p2wb_tok_dec_core i j) true
  | inr _ => Id (p2wb_tok_dec_core i j) false
  end.
Proof.
  intros i j.
  destruct i; destruct j; cbn [p2wb_token_eq_dec p2wb_tok_dec_core]; apply id_refl.
Qed.

(* ################ 假设审计（Print Assumptions 全 Closed） ################### *)

Print Assumptions p2wb_token_eq_dec.
Print Assumptions p2wb_keep_dec.
Print Assumptions p2wb_keep_dec_sel.
Print Assumptions p2wb_tail_plus_kept_full_sel.
Print Assumptions p2wb_sel_tail_mass_one.
Print Assumptions p2wb_top_keep_head_witness.
Print Assumptions p2wb_supplied.
Print Assumptions p2wb_supplied_sel.
Print Assumptions p2wb_tok_dec_core_correct.

(* 提取面：判定核单列（纯 bool 构造）；核↔接口正确性证书为证明内容，
   不入提取集，以假设审计替代。 *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_a2_p2w_ex".
Separate Extraction p2wb_tok_dec_core.

(* ################ 第 8 部：W_dec 位 Set 重述位与具体层供给（上游清册项，   *)
(* ################ C2 底册 #11） ########################################## *)
(* 件内先例：第 2 部 p2wb_token_eq_dec（Or 形四支构造子逐一判定）；         *)
(*   重述形同 UpReqAttnUniformLimit 文尾 alm_token_eq_dec_set 款式：       *)
(*   sigT bool 见证形——正支给 W t p 见证，负支给 W t p -> Empty_set 函数   *)
(*  （Set 层否定见证，可提取）。                                           *)

(* Set 重述形定义位（注：本位即 W_dec 参数位的 Set 重述位） *)
Definition p2wb_wdec_set (W : bool -> nat -> Set) : Set :=
  forall (t : bool) (p : nat),
    sigT (fun d : bool =>
      match d with
      | true => W t p
      | false => W t p -> Empty_set
      end).

(* 桥一：Or 形判定接口 -> sigT bool 见证形 *)
Definition p2wb_wdec_of_or (W : bool -> nat -> Set)
           (kd : forall (t : bool) (p : nat), Or (W t p) (Not (W t p))) :
  p2wb_wdec_set W :=
  fun t p =>
    match kd t p with
    | inl h => existT _ true h
    | inr h => existT _ false h
    end.

(* 桥二：sigT bool 见证形 -> Or 形判定接口（原 Or 形接口签名零改动） *)
Definition p2wb_wdec_or_of (W : bool -> nat -> Set)
           (ds : p2wb_wdec_set W) :
  forall (t : bool) (p : nat), Or (W t p) (Not (W t p)) :=
  fun t p =>
    match ds t p with
    | existT _ true h => inl h
    | existT _ false h => inr h
    end.

(* 具体层供给：W 取布尔择留族（true 恒驻 unit、false 恒空），判定由       *)
(*   构造子分派直接给出（正支 tt 见证；负支构造子分裂空匹配）。            *)
Definition p2wb_W_sel : bool -> nat -> Set :=
  fun t _ =>
    match t with
    | true => unit
    | false => Empty_set
    end.

Theorem p2wb_wdec_supply : p2wb_wdec_set p2wb_W_sel.
Proof.
  intros t p.
  destruct t as [ | ].
  - exact (existT _ true tt).
  - refine (existT _ false _).
    intro h.
    exact (match h with end).
Qed.

(* 双形往返证书：重述形经桥二回到 Or 形接口（择留实例） *)
Definition p2wb_wdec_roundtrip :
  forall (t : bool) (p : nat), Or (p2wb_W_sel t p) (Not (p2wb_W_sel t p)) :=
  p2wb_wdec_or_of p2wb_W_sel p2wb_wdec_supply.

(* ================= 重述位假设面核验（预期全 Closed） ==================== *)
Print Assumptions p2wb_wdec_of_or.
Print Assumptions p2wb_wdec_or_of.
Print Assumptions p2wb_wdec_supply.
Print Assumptions p2wb_wdec_roundtrip.
