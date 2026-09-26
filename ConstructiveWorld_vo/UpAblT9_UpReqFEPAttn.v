(* ==========================================================================)
   UpAblT9_UpReqFEPAttn.v — 配分正性的上下文重述
   使命: uabT9_fep_ctx_Zf_pos、uabT9_row_ctx_Zrow_pos、uabT9_lz_ctx_Zf_pos 三件（正性核前提 ⟹ 配分/行配分严格正）。
   依赖: CW_ConstructiveWorld_219、UpReqFEPAttn
   对标: Boltzmann 配分函数正性（正权和原理的实例重述）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)
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
Require Import UpReqFEPAttn.
Import RealInterfaceEnhancedMod.

(* 位1 ←:71（rep@:121；R/RIS 实例位材料化） *)
Theorem uabT9_fep_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : lt zero T),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    lt zero (Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@Zf_pos Real RealEnhancedReal S sumf Hsum z T T_pos).
Qed.

(* 位2 ←:259（rep@:280；R/RIS 实例位材料化） *)
Theorem uabT9_row_ctx_Zrow_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (temp : Real) (temp_pos : lt zero temp)
         (z2 : S -> S -> Real) (expf : Real -> Real),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    (forall x : Real, lt zero (expf x)) ->
    forall s : S, lt zero (req_Zrow S sumf temp temp_pos z2 expf s).
Proof.
  intros S sumf temp temp_pos z2 expf Hsum Hexpf s.
  exact (@req_Zrow_pos Real RealEnhancedReal S sumf Hsum temp temp_pos z2 expf Hexpf s).
Qed.

(* 位3 ←:331（rep@:366；R/RIS 实例位材料化） *)
Theorem uabT9_lz_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : lt zero T),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    lt zero (lz_Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@lz_Zf_pos Real RealEnhancedReal S sumf Hsum z T T_pos).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_fep_ctx_Zf_pos.
Print Assumptions uabT9_row_ctx_Zrow_pos.
Print Assumptions uabT9_lz_ctx_Zf_pos.
