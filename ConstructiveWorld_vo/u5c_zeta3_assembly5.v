(* ===================================================================== *)
(*  u5c_zeta3_assembly5.v —— ζ(3) 装配面 M2′ 有界形一次代入＋零前提段 [5,14] *)
(* ===================================================================== *)
(*  一 使命：                                                            *)
(*    承 zb3j_base15 的 HM2 面 [1,15] 段实例（zb3j_HM2_face_15），把       *)
(*    u5c_zeta3_assembly4 首前提（M2′ 全称形 forall n ≥ 1,                *)
(*    zb3m_HM2_face n）替换为其 [1,15] 有界形，m 范围相应约束至 [5,14]：    *)
(*      · u5c_zeta3_assembly5：HM2 面 [1,15] 有界形＋NatLe 5 m＋          *)
(*        NatLe m 14 ⟹ supply_chain（S m ∈ [6,15] 档 HM2 位逐点代入）。    *)
(*      · u5c_zeta3_assembly5_base：NatLe 5 m ＋ NatLe m 14 ⟹             *)
(*        supply_chain 零前提——零前提段自 [5,9] 扩张至 [5,14]              *)
(*        （S m ∈ [6,15] ⊆ [1,15] 机器可达段）。                           *)
(*    缺口单调收缩账：零前提段 [5,9] → [5,14]；m ≥ 15 段残余两位不变      *)
(*    （[16,42] 档一元表示界内不可达＋n ≥ 43 档熵不等式解析段）。          *)
(*  二 依赖：                                                            *)
(*    库内 zb3j_base15（HM2 面 [1,15] 段正本）、zb3p_hpw（Hpw 零前提      *)
(*    证书）、u5c_zeta3_assembly2/3（槽形正本，零重述）、                  *)
(*    u5c_z3_m2p_ledger（HM2 槽形）。                                      *)
(*  三 构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面；两主件 Defined 透明供提取。         *)
(*  四 编译配方：                                                        *)
(*    rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly5.v          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.
Require Import abl_z3_itg_carrier.
Require Import abl_z3_decay.
Require Import abl_z3_tail.
Require Import zb3p_hpw.
Require Import u5c_zeta3_assembly.
Require Import abl_z3_hws.
Require Import u5c_zeta3_assembly2.
Require Import u5c_z3_m2p_ledger.
Require Import u5c_zeta3_assembly3.
Require Import zb3j_base15.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 有界形主件：HM2 面 [1,15] 有界形 ＋ NatLe 5 m ＋ NatLe m 14           *)
(*    ⟹ supply_chain（HM2 位于 S m ∈ [6,15] 一次代入）                      *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly5 : forall (m M : nat),
  (forall n : nat, (1 <= n)%nat -> (n <= 15)%nat -> zb3m_HM2_face n) ->
  NatLe 5 m -> NatLe m 14 -> u5c_z3_supply_chain m M.
Proof.
  intros m M HM2b Hm5 Hm14.
  pose proof (NatLe_drop _ _ Hm14) as H14.
  apply (u5c_zeta3_assembly2.u5c_zeta3_assembly2 m M).
  split.
  - exact Hm5.
  - split.
    + intros j Hj. apply (zb3r_Hpw_closed m j).
      pose proof (NatLe_drop _ _ Hm5). lia.
    + apply HM2b; lia.
Defined.

(* ============================================================ *)
(* §2 零前提判定：m ∈ [5,14] 段供给链全闭合                                 *)
(*    HM2 位由 zb3j_HM2_face_15 无条件供给。                                *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly5_base : forall (m M : nat),
  NatLe 5 m -> NatLe m 14 -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hm5 Hm14.
  apply (u5c_zeta3_assembly5 m M zb3j_HM2_face_15 Hm5 Hm14).
Defined.

(* ============================================================ *)
(* §3 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly5 u5c_zeta3_assembly5_base.

Print Assumptions u5c_zeta3_assembly5.
Print Assumptions u5c_zeta3_assembly5_base.
