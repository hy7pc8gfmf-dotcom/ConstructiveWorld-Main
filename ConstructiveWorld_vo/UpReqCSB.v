(* ==========================================================================)
   UpReqCSB.v — Cauchy–Schwarz 的 ≤_B 形
   使命: real_cauchy_schwarz_B（dotp^2 ≤_B sql·sql，单件转化）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、UpCS
   对标: Cauchy–Schwarz 不等式的 ε-一致序（≤_B）转化。
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
Require Import UpRealLeB.
Require Import UpCS.

(* 主件：C-S 结论的 ≤_B 形态（§10.2 第 6 项升格对照件） *)
Lemma real_cauchy_schwarz_B :
  forall a b : list Real,
    real_le_b (real_mult (dotp a b) (dotp a b))
              (real_mult (sql a) (sql b)).
Proof.
  intros a b.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (real_cauchy_schwarz a b eps Heps).
Qed.

(* 尾注：单步完成=源件逐 eps 面显式应用特化完成器；出口与 eps 形等价可达。 *)
Print Assumptions real_cauchy_schwarz_B.
