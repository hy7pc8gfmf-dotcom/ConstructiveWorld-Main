(* ===================================================================== *)
(*  u5c_zeta3_assembly4.v —— ζ(3) 装配面 2→1 收缩＋[5,9] 段零前提闭合        *)
(* ===================================================================== *)
(*  一 使命：                                                            *)
(*    承 zb3p_hpw 的 ①Hpw 逐点封顶证书零前提闭合（无窗全称形），把装配槽    *)
(*    u5c_z3_assembly_slot3 的第二前提（Hpw）一次代入移出槽外：            *)
(*      · u5c_zeta3_assembly4：M2′ 全称形＋NatLe 5 m ⟹ supply_chain       *)
(*      · u5c_zeta3_assembly4_base：NatLe 5 m ＋ NatLe m 9 ⟹ supply_chain  *)
(*        （M2′ 位由 zb3m_C_le_3pow_base 无条件闭合——[5,9] 段              *)
(*         ζ(3) 装配面零前提·B4 线首个全闭合供给段）。                      *)
(*    缺口单调收缩账：装配槽前提 4 → 3 → 2 → 1（全称 m≥10 段唯一残余＝     *)
(*    M2′ 全称形·Hanson 链面所有）；[5,9] 段 = 0。                         *)
(*  二 依赖：                                                            *)
(*    库内 zb3p_hpw（①Hpw 零前提证书正本）、u5c_zeta3_assembly3（槽形与    *)
(*    基座分段正本·零重述）、u5c_z3_m2p_ledger（HM2 面）。                  *)
(*  三 构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面；两主件 Defined 透明供提取。          *)
(*  四 编译配方：                                                        *)
(*    rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly4.v          *)
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

Open Scope Q_scope.

(* ============================================================ *)
(* §1 收缩主件：M2′ 全称形 ＋ NatLe 5 m ⟹ supply_chain（唯一残位＝M2′）     *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly4 : forall (m M : nat),
  (forall n : nat, (1 <= n)%nat -> zb3m_HM2_face n) ->
  NatLe 5 m -> u5c_z3_supply_chain m M.
Proof.
  intros m M HM2u Hm5.
  apply (u5c_zeta3_assembly3.u5c_zeta3_assembly3 m M HM2u).
  split.
  - exact Hm5.
  - intros j Hj. apply (zb3r_Hpw_closed m j).
    pose proof (NatLe_drop _ _ Hm5). lia.
Defined.

(* ============================================================ *)
(* §2 基座段零前提闭合：m ∈ [5,9] ⟹ supply_chain（装配面零前提）            *)
(*    Hpw 位一次代入 ＋ M2′ 位由账本基座 zb3m_C_le_3pow_base 无条件供给。   *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly4_base : forall (m M : nat),
  NatLe 5 m -> NatLe m 9 -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hm5 Hm9.
  apply (u5c_zeta3_assembly3.u5c_zeta3_assembly3_base m M Hm5 Hm9).
  intros j Hj. apply (zb3r_Hpw_closed m j).
  pose proof (NatLe_drop _ _ Hm5). lia.
Defined.

(* ============================================================ *)
(* §3 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly4 u5c_zeta3_assembly4_base.

Print Assumptions u5c_zeta3_assembly4.
Print Assumptions u5c_zeta3_assembly4_base.
