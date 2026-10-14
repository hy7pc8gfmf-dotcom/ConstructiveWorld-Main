(* ===================================================================== *)
(*  u5c_zeta3_assembly3.v —— ζ(3) 装配面收缩件（装配槽三前提收缩为两）        *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    承 u5c_z3_m2p_ledger 的 Hanson 熵界基座证书（z2v_C n ≤ 3^n 于        *)
(*    n ∈ [1,10] 档）与槽形接口 zb3m_HM2_face（n ↦ NatLe (z2v_C n) (3^n)，  *)
(*    与 u5c_z3_assembly_slot2 第三前提同型），把装配槽                    *)
(*    u5c_z3_assembly_slot3 前提账收缩：NatLe 5 m ＋ Hpw ＋ HM2 三前提      *)
(*    → NatLe 5 m ＋ Hpw 两前提。HM2 位由 zb3m_HM2_face_from_M2 一次       *)
(*    代入供给，M2′ 残位自此以全称形（forall n ≥ 1, zb3m_HM2_face n）      *)
(*    显式居于语句首前提位。supply_chain 四层面逐字同源（Require 使用      *)
(*    u5c_zeta3_assembly2 正本，零重述）。缺口单调收缩账：装配槽前提       *)
(*    4 → 3 → 2。                                                        *)
(*    分段终态：m ∈ [5,9] 档由 zb3m_C_le_3pow_base 无条件闭合，该段装配    *)
(*    唯一残余为 Hpw（u5c_zeta3_assembly3_base）；m ≥ 10 档残余两位        *)
(*    ＝Hpw（逐点封顶证书）与 M2′ 全称形（z2v_C ≤ 3^n 的解析闭合）。       *)
(*  依赖：                                                            *)
(*    缓存根 S01_BaseRing S02_CauchyComplete S03_QExp HansonLcm；池内      *)
(*    abl_z2_valbridge、u5c_zeta2_gapB、abl_z3_itg_carrier、abl_z3_decay、  *)
(*    abl_z3_tail、u5c_zeta3_assembly、abl_z3_hws、u5c_zeta3_assembly2、    *)
(*    u5c_z3_m2p_ledger（HM2 槽接口与基座证书正本，零重述）。               *)
(*  构造性注记：                                                      *)
(*    纯构造性、零假设声明、零承认词面、零经典逻辑；两主件 Defined 透明供   *)
(*    提取；语句面全 Set 层（sigT/And/NatLe/QleT'/QeqT）。                 *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly3.v  *)
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
Require Import u5c_zeta3_assembly.
Require Import abl_z3_hws.
Require Import u5c_zeta3_assembly2.
Require Import u5c_z3_m2p_ledger.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 收缩后装配槽（两前提：NatLe 5 m ＋ Hpw）                              *)
(*    两前提与 u5c_z3_assembly_slot2 前两位逐字同源；HM2 位已由             *)
(*    zb3m_HM2_face_from_M2 的一次代入移出槽外（语句首前提位全称形）。       *)
(* ============================================================ *)

Definition u5c_z3_assembly_slot3 (m M : nat) : Set :=
  And (NatLe 5 m)
    (forall j : nat, (j <= m * m + 2 * m)%nat ->
       QleT' (zb3_term (Datatypes.S m) j
              * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
             ((1 # 8) * q_pow (1 # 40) m)).

(* ============================================================ *)
(* §2 收缩主件：M2′ 全称形给定 ⟹ 两前提槽 ⟹ ζ(3) 供给链 inhabited           *)
(*    证体＝槽形构造＋HM2 位一次代入（zb3m_HM2_face_from_M2）＋             *)
(*    其余逐位转递 u5c_zeta3_assembly2 主件。                              *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly3 : forall (m M : nat),
  (forall n : nat, (1 <= n)%nat -> zb3m_HM2_face n) ->
  u5c_z3_assembly_slot3 m M -> u5c_z3_supply_chain m M.
Proof.
  intros m M HM2u Hs.
  destruct Hs as [Hm5 Hpw].
  apply (u5c_zeta3_assembly2.u5c_zeta3_assembly2 m M).
  split.
  - exact Hm5.
  - split.
    + exact Hpw.
    + exact (zb3m_HM2_face_from_M2 HM2u m).
Defined.

(* ============================================================ *)
(* §3 基座分段闭合：m ∈ [5,9] 档供给链唯一残余为 Hpw                         *)
(*    HM2 位由账本基座证书 zb3m_C_le_3pow_base 无条件供给                   *)
(*    （S m ∈ [6,10] ⊆ [1,10] 机器可达段）。                                *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly3_base : forall (m M : nat),
  NatLe 5 m -> NatLe m 9 ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb3_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 8) * q_pow (1 # 40) m)) ->
  u5c_z3_supply_chain m M.
Proof.
  intros m M Hm5 Hm9 Hpw.
  pose proof (NatLe_drop _ _ Hm9) as H9.
  apply (u5c_zeta3_assembly2.u5c_zeta3_assembly2 m M).
  split.
  - exact Hm5.
  - split.
    + exact Hpw.
    + apply NatLe_lift. apply zb3m_C_le_3pow_base; lia.
Defined.

(* ============================================================ *)
(* §4 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly3 u5c_zeta3_assembly3_base.

Print Assumptions u5c_z3_assembly_slot3.
Print Assumptions u5c_zeta3_assembly3.
Print Assumptions u5c_zeta3_assembly3_base.
