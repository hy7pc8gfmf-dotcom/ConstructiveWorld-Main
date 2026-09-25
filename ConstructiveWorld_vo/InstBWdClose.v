(* ============================================================ *)
(* InstBWdClose.v                                                *)
(*                                                               *)
(* 目的：补齐 INSTB 实例 E-载体层的 bnorm_opp 良定义性——负变元下    *)
(*       bnorm 取值不变（点态 Id 形）。                            *)
(* 主件：ibw_bnorm_opp :                                          *)
(*       forall a : bxib_E,                                       *)
(*         Id (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a)；          *)
(*       派生件 ibw_bnorm_opp_qeqt 给出 QeqT 形。                  *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、UpReqBanachInstB、       *)
(*       UpReqBanachInstReal；Stdlib QArith.QArith、QArith.Qabs。   *)
(* 备注：本件证明的是 UpReqBanachInstB.v:573 声明位——E-载体面       *)
(*       字段 bnorm_opp 的点态 Id 形，其语句面与冻结类字段          *)
(*       bxin_bnorm_opp（UpReqBanachInst.v:263）逐字对齐，此前       *)
(*       全库未证。上游另有三个同形语句位已有现成引理，直接引用      *)
(*       不重复建件：bplus_wd 位 := bxem_bplus_wd                  *)
(*       （UpReqBanachInstEMult.v:242）、bopp_wd 位 :=              *)
(*       bxem_bopp_wd（UpReqBanachInstEMult.v:260）、bxib_qabs_opp  *)
(*       _norm 位 := bxra_qabs_opp_norm（UpReqBanachInstReal）。    *)
(*       证明不复制 Z 层链，经 ev 展开退化后直取 bxra_qabs_opp_norm *)
(*       （bxem 同款 change 面）；零新算术。全件 Qed；无公理、       *)
(*       无承认式、无经典逻辑；结论全为 Set 层 Id / QeqT 形。       *)
(*       文末对全件附 Print Assumptions 审计。                     *)
(* ============================================================ *)

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
