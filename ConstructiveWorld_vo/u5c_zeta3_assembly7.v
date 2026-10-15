(* ===================================================================== *)
(*  u5c_zeta3_assembly7.v —— ζ(3) 装配面 base42 一次代入＋零前提供给段       *)
(*                          [5,15] 扩张至 [5,41]（DM-Z3N2）        *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    承 zb3z_base42 的 HM2 面 [1,42] 段实例（zb3z_HM2_face_42·Z 换岸      *)
(*    born 正本），把 u5c_zeta3_assembly6 首前提（HM2 面 [1,16] 有界形）   *)
(*    替换为其 [1,42] 有界形，m 范围相应放行至 [5,41]：                    *)
(*      · u5c_zeta3_assembly7：HM2 面 [1,42] 有界形＋NatLe 5 m＋          *)
(*        NatLe m 41 ⟹ supply_chain（S m ∈ [6,42] 档 HM2 位逐点代入）。     *)
(*      · u5c_zeta3_assembly7_base：NatLe 5 m ＋ NatLe m 41 ⟹             *)
(*        supply_chain 零前提——零前提供给段自 [5,15] 扩张至 [5,41]。       *)
(*    新扩展段 m ∈ [16,41]（S m ∈ [17,42]）全通申报：16 档全由 Z 换岸      *)
(*    born 链（zb3z_blk1..blk10·C(41) 锚在卷）无条件供给。                 *)
(*    缺口单调收缩账：零前提段 [5,9]→[5,14]→[5,15]→[5,41]；m ≥ 42 段残余   *)
(*    仅剩 n ≥ 43 熵段（Σ1/a_i=1 熵相消 nat 化·专项工程·Z3N §四判定维持）。 *)
(*  依赖：                                                            *)
(*    池内 zb3z_base42（HM2 面 [1,42] 段正本·Z 换岸三件正典化）、          *)
(*    zb3p_hpw（Hpw 零前提证书）、u5c_zeta3_assembly2（三前提槽形正本，    *)
(*    零重述）、u5c_z3_m2p_ledger（HM2 槽形）。                            *)
(*  构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面；两主件 Defined 透明供提取。         *)
(*  编译配方：                                                        *)
(*    cd 池 && source Live/toolchain/env.sh && cpu_guard 包裹单飞；         *)
(*    rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly7.v          *)
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
Require Import zb3z_base42.

Close Scope Q_scope.

(* ============================================================ *)
(* §1 有界形主件：HM2 面 [1,42] 有界形 ＋ NatLe 5 m ＋ NatLe m 41           *)
(*    ⟹ supply_chain（HM2 位于 S m ∈ [6,42] 一次代入）                      *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly7 : forall (m M : nat),
  (forall n : nat, (1 <= n)%nat -> (n <= 42)%nat -> zb3m_HM2_face n) ->
  NatLe 5 m -> NatLe m 41 -> u5c_z3_supply_chain m M.
Proof.
  intros m M HM2b Hm5 Hm41.
  pose proof (NatLe_drop _ _ Hm41) as H41.
  apply (u5c_zeta3_assembly2.u5c_zeta3_assembly2 m M).
  split.
  - exact Hm5.
  - split.
    + intros j Hj. apply (zb3r_Hpw_closed m j).
      pose proof (NatLe_drop _ _ Hm5). lia.
    + apply HM2b; lia.
Defined.

(* ============================================================ *)
(* §2 零前提判定：m ∈ [5,41] 段供给链全闭合                                 *)
(*    HM2 位由 zb3z_HM2_face_42 无条件供给（base15 段＋[16,42] Z 换岸段）。  *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly7_base : forall (m M : nat),
  NatLe 5 m -> NatLe m 41 -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hm5 Hm41.
  apply (u5c_zeta3_assembly7 m M zb3z_HM2_face_42 Hm5 Hm41).
Defined.

(* ============================================================ *)
(* §3 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly7 u5c_zeta3_assembly7_base.

Print Assumptions u5c_zeta3_assembly7.
Print Assumptions u5c_zeta3_assembly7_base.
