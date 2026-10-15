(* ===================================================================== *)
(*  u5c_zeta3_assembly6.v —— ζ(3) 装配面 base15 一次代入＋HM2@16 适配衔接     *)
(*                          ＋零前提供给段 [5,14] 扩张至 [5,15]              *)
(* ===================================================================== *)
(*  使命：（DM-Z3P）                                         *)
(*    承 u5c_zeta3_assembly5（零前提段 [5,14]）与 zb3j_base15（HM2 面       *)
(*    [1,15] 段正本），补 HM2 位 n = 16 档一档（C(16) = 2·C(15) 符号桥，    *)
(*    全程零 vm_compute·零深转换），经 [1,15]→[1,16] 面适配衔接把 m 上界    *)
(*    自 14 放行至 15：                                                    *)
(*      · u5c_zeta3_assembly6：HM2 面 [1,16] 有界形＋NatLe 5 m＋           *)
(*        NatLe m 15 ⟹ supply_chain（S m ∈ [6,16] 档 HM2 位逐点代入）。     *)
(*      · u5c_zeta3_assembly6_base：NatLe 5 m ＋ NatLe m 15 ⟹             *)
(*        supply_chain 零前提——零前提段自 [5,14] 扩张至 [5,15]。            *)
(*    缺口单调收缩账：零前提段 [5,9] → [5,14] → [5,15]；m ≥ 16 段残余不变  *)
(*    （[16,42] 档一元表示界内不可达＋n ≥ 43 档熵不等式解析段）。           *)
(*  依赖：                                                            *)
(*    池内 zb3j_base15（HM2 面 [1,15] 段正本＋C 链 11..15 值＋3^13 锚）、   *)
(*    u5c_zeta2_gapB（C 步进机 zb2gb_C_step 正本）、u5c_z3_m2p_ledger      *)
(*    （zb3m_HM2_face/zb3m_G_ext）、zb3p_hpw（Hpw 零前提证书）、           *)
(*    u5c_zeta3_assembly2（三前提槽形正本，零重述）。                      *)
(*  构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面、零经典逻辑（Nat.eq_dec 为构造       *)
(*    判决）；主件 Defined 透明供提取。n = 16 档比较面走 Nat.mul_le_mono    *)
(*    ＋Nat.pow_succ_r' 符号化改写，免于物化 3^14 的一元展开。             *)
(*  编译配方：                                                        *)
(*    cd 池 && source Live/toolchain/env.sh && cpu_guard 包裹单飞；         *)
(*    rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly6.v          *)
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
Require Import zb3j_base15.

(* 本件全 nat 层（C 链与比较面）——照 zb3j_base15 正本头部同款关 Q 作用域，  *)
(* 防 Qmult 传染（Z3I 坑位·c1 红发实录）。                                  *)
Close Scope Q_scope.

(* ============================================================ *)
(* §1 C(16) 一档链：C(16)·G(16,16) = 16·C(15)、G(16,16) = 8                 *)
(*    （zb3m_G_ext 折回四因子截断面）⟹ C(16) = 2·C(15) 因子化承载。         *)
(*    乘数对齐 16 = 8·2 走结合律改写，取消面 Nat.mul_cancel_l（IFF 取       *)
(*    proj1）——zb3j §2 配方逐字同款，常数桥全在内核小数值域。               *)
(* ============================================================ *)

Lemma zb3p_C16_eq_2C15 : z2v_C 16 = 2 * (3 * (13 * (11 * 2520))).
Proof.
  pose proof zb3j_C_vals_11_15 as (_ & _ & _ & _ & WF).
  pose proof zb3m_a4_gt42 as Ha4.
  pose proof (zb2gb_C_step 15 ltac:(lia)) as E16.
  assert (G16 : z2gb_G 16 16 = 8).
  { rewrite (zb3m_G_ext 16 4 16 ltac:(lia) ltac:(lia) ltac:(lia)).
    reflexivity. }
  rewrite G16 in E16. rewrite WF in E16.
  rewrite (Nat.mul_comm (z2v_C 16) 8) in E16.
  assert (H16r : forall x : nat, (16 * x = 8 * (2 * x))%nat).
  { intros x. rewrite (Nat.mul_assoc 8 2 x). reflexivity. }
  rewrite (H16r (3 * (13 * (11 * 2520)))) in E16.
  assert (H8z : (8 <> 0)%nat) by discriminate.
  exact (proj1 (Nat.mul_cancel_l (z2v_C 16)
                   (2 * (3 * (13 * (11 * 2520)))) 8 H8z) E16).
Qed.

(* ============================================================ *)
(* §2 HM2@16 比较面：C(16) = 2·C(15) ≤ 2·3^13 ≤ 3·3^13 = 3^14 ≤ 3^16。      *)
(*    三跳全符号（mul_le_mono 左右乘＋pow_succ_r'＋pow_le_mono_r），        *)
(*    深层一元值零物化（3^13 锚直取 zb3j_C15_le_anchor 绿判正本）。          *)
(* ============================================================ *)

Lemma zb3p_C16_le_3pow16 : (2 * (3 * (13 * (11 * 2520))) <= 3 ^ 16)%nat.
Proof.
  apply Nat.le_trans with (m := 2 * 3 ^ 13).
  - apply Nat.mul_le_mono_l. exact zb3j_C15_le_anchor.
  - apply Nat.le_trans with (m := 3 * 3 ^ 13).
    + apply Nat.mul_le_mono_r. lia.
    + rewrite <- (Nat.pow_succ_r' 3 13).
      apply Nat.pow_le_mono_r; lia.
Qed.

Theorem zb3p_HM2_face_16_pt : zb3m_HM2_face 16.
Proof.
  unfold zb3m_HM2_face. apply NatLe_lift.
  rewrite zb3p_C16_eq_2C15. exact zb3p_C16_le_3pow16.
Qed.

(* ============================================================ *)
(* §3 面适配衔接：[1,15] 段正本（zb3j_HM2_face_15）＋16 档新铸件            *)
(*    ＝ [1,16] 段实例（n ≤ 16 构造二分：n = 16 走新铸、余段走正本）。       *)
(* ============================================================ *)

Theorem zb3p_HM2_face_16 : forall n : nat,
  (1 <= n)%nat -> (n <= 16)%nat -> zb3m_HM2_face n.
Proof.
  intros n H1 H16.
  destruct (Nat.eq_dec n 16) as [Hn | Hn].
  - subst n. exact zb3p_HM2_face_16_pt.
  - apply zb3j_HM2_face_15; lia.
Qed.

(* ============================================================ *)
(* §4 有界形主件：HM2 面 [1,16] 有界形 ＋ NatLe 5 m ＋ NatLe m 15           *)
(*    ⟹ supply_chain（HM2 位于 S m ∈ [6,16] 一次代入）                      *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly6 : forall (m M : nat),
  (forall n : nat, (1 <= n)%nat -> (n <= 16)%nat -> zb3m_HM2_face n) ->
  NatLe 5 m -> NatLe m 15 -> u5c_z3_supply_chain m M.
Proof.
  intros m M HM2b Hm5 Hm15.
  pose proof (NatLe_drop _ _ Hm15) as H15.
  apply (u5c_zeta3_assembly2.u5c_zeta3_assembly2 m M).
  split.
  - exact Hm5.
  - split.
    + intros j Hj. apply (zb3r_Hpw_closed m j).
      pose proof (NatLe_drop _ _ Hm5). lia.
    + apply HM2b; lia.
Defined.

(* ============================================================ *)
(* §5 零前提判定：m ∈ [5,15] 段供给链全闭合                                 *)
(*    HM2 位由 zb3p_HM2_face_16 无条件供给（base15 正本＋16 档新铸）。       *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly6_base : forall (m M : nat),
  NatLe 5 m -> NatLe m 15 -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hm5 Hm15.
  apply (u5c_zeta3_assembly6 m M zb3p_HM2_face_16 Hm5 Hm15).
Defined.

(* ============================================================ *)
(* §6 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly6 u5c_zeta3_assembly6_base.

Print Assumptions zb3p_C16_eq_2C15.
Print Assumptions zb3p_C16_le_3pow16.
Print Assumptions zb3p_HM2_face_16_pt.
Print Assumptions zb3p_HM2_face_16.
Print Assumptions u5c_zeta3_assembly6.
Print Assumptions u5c_zeta3_assembly6_base.
