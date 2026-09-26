(* ============================================================ *)
(* UpReqBishopFull.v —— R2RBF 席：Bishop 主定理无显式前件版            *)
(*   （Hqarch 前件接线消解，Bishop 路线 100% 闭合最后一步）             *)
(*   2026-09-24                                                      *)
(* ============================================================ *)
(* 使命：消费 R2BishopLogSel.mix_k_select_bishop（库树 L330，只读）     *)
(*   与 UpReqQArchSite.qarch_site（RBB 席四关绿交付，只读），           *)
(*   把主定理显式前件 Hqarch 从陈述中消解——接线即闭合。                *)
(* 复用件（绿盘只读 Require）：                                        *)
(*   R2BishopLogSel —— mix_k_select_bishop（五前件原主定理）           *)
(*   UpReqQArchSite —— qarch_site（Hqarch 构造性闭合件）               *)
(* 红线：零禁词；Set 层零 Prop 泄漏；陈述与任务书逐字一致，禁改。       *)

(* Require 面与 R2BishopLogSel 源环境同源照抄（其头部 Require 非 Export，
   Real/real_lt/real_le_b/rb_gval 不入传递导出面——须本件自行拉齐） *)
From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpReqMixLogA.
Require Import UpReqMixLogE.
Require Import R2BishopLogSel.
Require Import UpReqQArchSite.

Open Scope nat_scope.

Theorem mix_k_select_bishop_full : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_le_b (rb_gval kappa TV0 k) budget).
Proof.
  intros kappa TV0 budget Hk0 Hk1 Ha0 Hb0.
  exact (mix_k_select_bishop kappa TV0 budget Hk0 Hk1 Ha0 Hb0 qarch_site).
Qed.
