(* ===================================================================== *)
(*  u5c_zeta3_assembly2.v —— ζ(3) 装配面 Hws 放行件（四前提收缩为三）        *)
(* ===================================================================== *)
(*  使命：承 abl_z3_hws.v 的 Hws 独立消解（zb3_ia_Wsum_step_T），把装配     *)
(*    主件 u5c_zeta3_assembly 的残位槽 u5c_z3_assembly_slot（NatLe 5 m ＋   *)
(*    Hpw ＋ Hws ＋ HM2 四前提）收缩为 u5c_z3_assembly_slot2（NatLe 5 m ＋  *)
(*    Hpw ＋ HM2 三前提）：Hws 槽自此对 ζ(2)/ζ(3) 双线永久放行。             *)
(*    supply_chain 四层面（0 ≤ d、d ≤ 3^(m+1)、Σ ≤ (1/4)(1/40)^m、          *)
(*    d³·Σ < 1）逐字同源（Require 使用 v1 正本，零重述）。缺口单调收缩账：   *)
(*    装配槽残位 4 → 3（余 Hpw① 与 HM2③ 两处，均非本件新增）。              *)
(*  依赖：缓存根 S01_BaseRing S02_CauchyComplete S03_QExp HansonLcm；       *)
(*    abl_z2_valbridge、u5c_zeta2_gapB、abl_z3_itg_carrier、abl_z3_decay、   *)
(*    abl_z3_tail、u5c_zeta3_assembly（v1 正本）、abl_z3_hws。               *)
(*  对标：Beukers 1979 ζ(3) 级数估计（同 v1 装配面）。                       *)
(*  构造性：纯构造性、零假设声明、零承认词面、零经典逻辑；主件 Defined       *)
(*    透明供提取；语句面全 Set 层（sigT/And/NatLe/QleT'/QeqT）。             *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly2.v       *)
(*    （cpu_guard v3 包裹·串行≤1）；PA 2/2 Closed；提取 Obj.magic=0。        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.
Require Import abl_z3_itg_carrier.
Require Import abl_z3_decay.
Require Import abl_z3_tail.
Require Import u5c_zeta3_assembly.
Require Import abl_z3_hws.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 Hws 放行后的装配槽（三前提：NatLe 5 m ＋ Hpw ＋ HM2）                  *)
(* ============================================================ *)

Definition u5c_z3_assembly_slot2 (m M : nat) : Set :=
  And (NatLe 5 m)
    (And (forall j : nat, (j <= m * m + 2 * m)%nat ->
            QleT' (zb3_term (Datatypes.S m) j
                   * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
                  ((1 # 8) * q_pow (1 # 40) m))
      (NatLe (z2v_C (Datatypes.S m)) (3 ^ (Datatypes.S m)))).

(* ============================================================ *)
(* §2 全链装配主件（使命语句）：三前提给定 ⟹ ζ(3) 供给链 inhabited          *)
(*    证体＝Hws 槽以 zb3_ia_Wsum_step_T 逐字供给＋其余逐位转递 v1 主件。    *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly2 : forall (m M : nat),
  u5c_z3_assembly_slot2 m M -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hs.
  destruct Hs as [Hm5 [Hpw HM2]].
  apply (u5c_zeta3_assembly.u5c_zeta3_assembly m M).
  split.
  - exact Hm5.
  - split.
    + exact Hpw.
    + split.
      * intro J'. apply qeq_imp_qeqT. apply zb3_ia_Wsum_step.
      * exact HM2.
Defined.

(* ============================================================ *)
(* §3 提取与假设审计（零全局假设复核）                                   *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly2.

Print Assumptions u5c_z3_assembly_slot2.
Print Assumptions u5c_zeta3_assembly2.
