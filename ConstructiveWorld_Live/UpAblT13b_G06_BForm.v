(* ==========================================================================)
   同域语句面；同域语句面
   使命：本件形式化同域语句面。
   本件并载：同域语句面；同域语句面；同域语句面；同域语句面；同域语句面；同域语句面；同域语句面。
   依赖：QArith.Qring, S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog
     S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp,
     UpAuditBridge, G06_BForm, List, G13_EvictFam, TempSoftmaxInstantiation, UpReqAlign, UpReqAlign2, UpSigMigrate2,
     UpSigMigrate。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
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
Require Import UpAuditBridge.
Require Import G06_BForm.
From Stdlib Require Import List.

(* 位1 ←:32（求和外延槽：实和实例材料化） *)
Theorem uabT13b_g06_ros_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum S f rest)
             (g w) (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Qed.

(* 位2 ←:34（求和单调槽） *)
Theorem uabT13b_g06_ros_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (real_le_plus_compat (f w) (g w) (real_list_sum S f rest)
             (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Qed.

(* 位3 ←:36（求和可加槽） *)
Theorem uabT13b_g06_ros_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_eq_trans _
             (real_plus (real_plus (f w) (g w))
                        (real_plus (real_list_sum S f rest)
                                   (real_list_sum S g rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (f w) (g w))
               (real_list_sum S (fun w0 : S => real_plus (f w0) (g w0)) rest)
               (real_plus (f w) (g w))
               (real_plus (real_list_sum S f rest) (real_list_sum S g rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_plus_swap_mid (f w) (g w) (real_list_sum S f rest)
               (real_list_sum S g rest)).
Qed.

(* 位4 ←:40（求和线性槽） *)
Theorem uabT13b_g06_ros_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - apply (real_eq_trans _
             (real_plus (real_mult a (f w))
                        (real_mult a (real_list_sum S f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult a (f w))
               (real_list_sum S (fun w0 : S => real_mult a (f w0)) rest)
               (real_mult a (f w))
               (real_mult a (real_list_sum S f rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum S f rest)))
               (real_plus (real_mult a (f w)) (real_mult a (real_list_sum S f rest)))).
      apply (real_distrib a (f w) (real_list_sum S f rest)).
Qed.

(* 位5 ←:59（残差权聚合正；词表非空前提显式参） *)
Theorem uabT13b_g06_lebR_weight_pos :
  forall (X : Set) (vocab : list X), Not (Id vocab nil) ->
    real_lt real_zero
      (lebR_res_weight X (fun f : X -> Real => real_list_sum X f vocab)
                        (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  intros X vocab Hne.
  unfold lebR_res_weight.
  apply (rplb_sum_pos_discharged X
           (fun s : X => real_mult real_one real_one) vocab Hne).
  intro s.
  exact (real_mult_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.

(* 位6 ←:464（截断质量正；保留判定全保留实例供入+逐项正/非空前提显式参） *)
Theorem uabT13b_g06_uabtemp_sum_pos :
  forall (Token : Type) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> vocab <> nil ->
    forall prefix : list Token,
      real_lt real_zero
        (@uab_temp_sum Token vocab rtf
             (fun (_ : list Token) (_ : Token) => unit)
             (fun (_ : list Token) (_ : Token) => inl tt : Or unit (Not unit))
             prefix).
Proof.
  intros Token vocab rtf Hf Hne prefix.
  exact (real_list_sum_pos Token rtf vocab Hf Hne).
Qed.

(* 位7 ←:470（完整配分正；逐项正/非空前提显式参） *)
Theorem uabT13b_g06_Zfull_pos :
  forall (Token : Type) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> vocab <> nil ->
    real_lt real_zero (Z_full Token vocab rtf).
Proof.
  intros Token vocab rtf Hf Hne.
  unfold Z_full.
  induction vocab as [| w rest IH]; simpl.
  - exfalso. exact (Hne eq_refl).
  - destruct rest as [| w' rest'].
    + apply (RealSetoid.real_lt_id_r real_zero (rtf w) (real_plus (rtf w) real_zero)).
      * apply (real_eq_sym (real_plus (rtf w) real_zero) (rtf w)).
        apply (real_plus_zero (rtf w)).
      * exact (Hf w).
    + apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
               (real_plus (rtf w) (real_list_sum Token rtf (w' :: rest')))).
      * apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
        apply (real_plus_zero real_zero).
      * apply (real_lt_plus_compat real_zero (rtf w) real_zero
                 (real_list_sum Token rtf (w' :: rest'))).
        -- exact (Hf w).
        -- apply IH. discriminate.
Qed.

(* ---- 收尾段（逐件假设面打印） ---- *)
Print Assumptions uabT13b_g06_ros_ext.
Print Assumptions uabT13b_g06_ros_le.
Print Assumptions uabT13b_g06_ros_add.
Print Assumptions uabT13b_g06_ros_linear.
Print Assumptions uabT13b_g06_lebR_weight_pos.
Print Assumptions uabT13b_g06_uabtemp_sum_pos.
Print Assumptions uabT13b_g06_Zfull_pos.

(* ============================ §1 同域语句面（G13 支） ============================ *)
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
Require Import G13_EvictFam.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bEvq.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:455（正和面加逐点正；正和参数位显式参） *)
Theorem uabT13b_evq_Zthermo_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R0) (D_pos : lt zero D) (energy : S -> R0),
    lt zero (@evq_Z_thermo R0 (tsi_rie_setoid RI0) S sumf D D_pos energy).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold evq_Z_thermo, evq_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Qed.

(* 位2 ←:484（保留判定具体实例全保留供入+正和面逐点正） *)
Theorem uabT13b_evq_evicted_partition_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R0) (D_pos : lt zero D) (energy : S -> R0),
    lt zero (@evq_evicted_partition R0 (tsi_rie_setoid RI0) S sumf D D_pos energy
               (fun (_ : S) => unit)
               (fun (_ : S) => inl tt : Or unit (Not unit))).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold evq_evicted_partition, evq_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Qed.

End UabT13bEvq.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_evq_Zthermo_pos.
Print Assumptions uabT13b_evq_evicted_partition_pos.

(* ============================ §2 同域语句面（UpReqAlign 支） ============================ *)
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
Require Import UpReqAlign.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bAlign.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:100（正和面加逐点双正链实例化消解；正和数据参数位显式参） *)
Theorem uabT13b_align_Zalign_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_req R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_req.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bAlign.

(* ---- 收尾段（逐件假设面打印，判读全闭） ---- *)
Print Assumptions uabT13b_align_Zalign_pos.

(* ============================ §3 同域语句面（UpReqAlign2 支） ============================ *)
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
Require Import UpReqAlign2.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bAlign2.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:106（正和面加逐点双正链实例化消解；正和数据参数位显式参） *)
Theorem uabT13b_align2_Zalign_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@req2_Z_align R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold req2_Z_align.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bAlign2.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_align2_Zalign_pos.

(* ============================ §4 同域语句面（UpReqAlignRestA 支） ============================ *)
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
Require Import UpReqAlign.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bRestA.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:77（正和面加逐点双正链实例化消解；正和数据参数位显式参） *)
Theorem uabT13b_ralt_Zalign_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_req R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_req.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bRestA.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_ralt_Zalign_pos.

(* ============================ §5 同域语句面（UpReqDist 支） ============================ *)
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
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* 位1 ←:1026（两状态实例装配；Z:=two_state_Z、sumf:=bsum、D:=real_one、          *)
(*   base_loss:=two_state_loss，配分条件实形=c_partition 语句转换同一） *)
Theorem uabT13b_dist_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_dist_partition_cond.

(* ============================ §6 同域语句面（UpSigMigrate 支） ============================ *)
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
Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bSigm.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:49（配分条件迁移正和正性；正和参数位与配分参数位显式参） *)
Theorem uabT13b_sigm_Zpos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R0) (D : R0) (D_pos : lt zero D) (Z : R0),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (@lt_id_r R0 (tsi_rie_setoid RI0) zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* 位3 ←:549（正和面加逐点正；正和参数位显式参） *)
Theorem uabT13b_sigm_Zthermo_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R0) (D_pos : lt zero D) (energy : S -> R0),
    lt zero (@sigm_Z_thermo R0 (tsi_rie_setoid RI0) S sumf D D_pos energy).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold sigm_Z_thermo, sigm_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Qed.

End UabT13bSigm.

(* 位2 ←:50（两状态具体实例供给；实载体 Real 载体面，全局实例消解） *)
Theorem uabT13b_sigm_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_sigm_Zpos.
Print Assumptions uabT13b_sigm_Zthermo_pos.
Print Assumptions uabT13b_sigm_partition_cond.

(* ============================ §7 同域语句面（UpSigMigrate2 支） ============================ *)
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
Require Import UpSigMigrate2.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bSigm2.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:111（配分条件迁移正和正性；正和参数位与配分参数位显式参） *)
Theorem uabT13b_sigm2_Zpos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R0) (D : R0) (D_pos : lt zero D) (Z : R0),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (@lt_id_r R0 (tsi_rie_setoid RI0) zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* 位2 ←:891（正和面加逐点双正链；正和参数位显式参） *)
Theorem uabT13b_sigm2_Zalign_a_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R0) (beta : R0) (beta_pos : lt zero beta)
         (pi_ref : S -> R0) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_a_sum R0 (tsi_rie_setoid RI0) S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_a_sum.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Qed.

End UabT13bSigm2.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_sigm2_Zpos.
Print Assumptions uabT13b_sigm2_Zalign_a_pos.
