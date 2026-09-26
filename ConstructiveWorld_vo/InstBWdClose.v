(* ==========================================================================)
   InstBWdClose.v — bxib 范数的相反数不变
   使命: ibw_bnorm_opp（‖−a‖ == ‖a‖，Id 形）与 ibw_bnorm_opp_qeqt（QeqT 形）两件。
   依赖: S01_BaseRing、S02_CauchyComplete、UpReqBanachInstB、UpReqBanachInstReal；Stdlib QArith
   对标: 赋范空间范数的绝对齐次性（‖−a‖ = ‖a‖）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* 主件：bnorm_opp 位（E-载体面字段，UpReqBanachInstB.v:573 声明）   *)
(* 语句面逐字对齐冻结类字段 bxin_bnorm_opp 形（载体 bxib_E 面）。    *)
(* ============================================================ *)
Theorem ibw_bnorm_opp : forall a : bxib_E,
  Id (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. unfold bxib_bnorm.
  change (bxib_ev (bxib_eopp a)) with (Qopp (bxib_ev a)).
  exact (bxra_qabs_opp_norm (bxib_ev a)).
Qed.

(* QeqT 面（bxip_norm_wd_qeqt 同款派生形，供 QeqT 使用位） *)
Lemma ibw_bnorm_opp_qeqt : forall a : bxib_E,
  QeqT (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. apply bxib_qeqT_of_id. apply ibw_bnorm_opp.
Qed.

(* ============================================================ *)
(* 既有供给指针（零新件；对应语句位的使用位直取下列已证引理）：       *)
(*   bplus_wd 位 := bxem_bplus_wd（EMult:242，逐位同语句）          *)
(*   bopp_wd  位 := bxem_bopp_wd （EMult:260，逐位同语句）          *)
(*   Q 面引理位 := bxra_qabs_opp_norm（InstReal，逐字同语句）。      *)
(* ============================================================ *)

(* ============================================================ *)
(* 假设审计：文末对全件执行 Print Assumptions。                     *)
(* ============================================================ *)
Print Assumptions ibw_bnorm_opp.
Print Assumptions ibw_bnorm_opp_qeqt.
