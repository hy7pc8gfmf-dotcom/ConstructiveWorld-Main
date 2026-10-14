(* ===================================================================== *)
(*  zb3j_base15.v —— Hanson C 值链的机器可达扩张：[1,10] 基座升至 [1,15]    *)
(* ===================================================================== *)
(*  一 使命：                                                            *)
(*    将 M2′ 语句 forall n ≥ 1, z2v_C n ≤ 3^n 的已证段自 [1,10] 扩张至     *)
(*    [1,15]：C 步进机（zb2gb_C_step）自账本十档常数表续推五档；增值积      *)
(*    G(14,14) = 14、G(15,15) = 5 经 zb3m_G_ext 折返四因子截断面直算        *)
(*    （n ≤ 42 < a_4 = 1807 折返界）。比较面以 3^13 = 1594323 为基准，     *)
(*    n = 14、15 档经 Nat.pow_le_mono_r 单调折返，免于物化 3^14、3^15      *)
(*    的一元展开。常数因子化承载（22·2520、13·(11·2520) 等），链面常数桥    *)
(*    全部压在内核转换实测界内（≤ 55440 层），布尔判定折返一律走            *)
(*    Nat.leb 范形（深层一元值不出虚拟机堆）。                             *)
(*    主语句 zb3j_base15 为 nat 层支撑面（账本同款地位）；Set 面出口       *)
(*    zb3j_HM2_face_15（NatLe 承载，与账本 zb3m_HM2_face_base 同构）。     *)
(*  二 依赖：                                                            *)
(*    缓存根 HansonLcm Hanson3Pow S01_BaseRing S02_CauchyComplete；库内    *)
(*    abl_z2_dub3、abl_z2_valbridge、u5c_zeta2_gapB（C 步进机与增值积      *)
(*    引擎正本）、u5c_z3_m2p_ledger（十档常数表与 G 对角值，零重述）。      *)
(*  三 构造性注记：                                                      *)
(*    零假设声明、零承认、零经典逻辑；语句面为精确 nat 恒等式与有界判定。   *)
(*    诚实接口：无独立可执行提取见证——z2v_C 直算触发 fact 一元表示界，    *)
(*    判定义务由 Prop 链式常数折返承担（账本 §4 先例同款）。                *)
(*  四 编译配方：                                                        *)
(*    rocq c -native-compiler no -q -Q . "" zb3j_base15.v                  *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith.
From Stdlib Require Import Arith.Factorial Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import abl_z2_dub3.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.
Require Import u5c_z3_m2p_ledger.

Close Scope Q_scope.

(* ============================================================ *)
(* §1 对角增值积 14、15 档折返值（zb3m_G_ext 折回四因子截断面）             *)
(* ============================================================ *)

Lemma zb3j_G_diag_14_15 : z2gb_G 14 14 = 14 /\ z2gb_G 15 15 = 5.
Proof.
  pose proof zb3m_a4_gt42 as Ha4.
  assert (G14 : z2gb_G 14 14 = 14).
  { rewrite (zb3m_G_ext 14 4 14 ltac:(lia) ltac:(lia) ltac:(lia)).
    reflexivity. }
  assert (G15 : z2gb_G 15 15 = 5).
  { rewrite (zb3m_G_ext 15 4 15 ltac:(lia) ltac:(lia) ltac:(lia)).
    reflexivity. }
  exact (conj G14 G15).
Qed.

(* ============================================================ *)
(* §2 C 值链 11..15（步进机链·因子化常数承载·零 fact 直展）                 *)
(*    C(11)·1 = 11·C(10)、C(12)·24 = 12·C(11)、C(13)·1 = 13·C(12)、        *)
(*    C(14)·14 = 14·C(13)、C(15)·5 = 15·C(14)。24 = 12·2、15 = 5·3         *)
(*    乘数对齐走结合律改写，取消面统一 Nat.mul_cancel_l（IFF 取 proj1）。   *)
(* ============================================================ *)

Lemma zb3j_C_vals_11_15 :
  z2v_C 11 = 22 * 2520 /\ z2v_C 12 = 11 * 2520 /\
  z2v_C 13 = 13 * (11 * 2520) /\ z2v_C 14 = 13 * (11 * 2520) /\
  z2v_C 15 = 3 * (13 * (11 * 2520)).
Proof.
  pose proof zb3m_C_vals_chain
    as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VA).
  destruct zb3m_G_diag_vals
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GA & GB & GC & GD).
  destruct zb3j_G_diag_14_15 as (GE & GF).
  pose proof (zb2gb_C_step 10 ltac:(lia)) as E11.
  pose proof (zb2gb_C_step 11 ltac:(lia)) as E12.
  pose proof (zb2gb_C_step 12 ltac:(lia)) as E13.
  pose proof (zb2gb_C_step 13 ltac:(lia)) as E14.
  pose proof (zb2gb_C_step 14 ltac:(lia)) as E15.
  rewrite GB in E11. rewrite GC in E12. rewrite GD in E13.
  rewrite GE in E14. rewrite GF in E15.
  rewrite VA in E11.
  assert (H2z : (2 <> 0)%nat) by discriminate.
  assert (H12z : (12 <> 0)%nat) by discriminate.
  assert (H14z : (14 <> 0)%nat) by discriminate.
  assert (H5z : (5 <> 0)%nat) by discriminate.
  assert (VAc : z2v_C 10 = 2 * 2520) by exact VA.
  assert (H24r : forall x : nat, (x * 24 = 12 * (2 * x))%nat).
  { intros x. rewrite (Nat.mul_comm x 24).
    rewrite (Nat.mul_assoc 12 2 x). reflexivity. }
  assert (H15d : forall x : nat, (15 * x = 5 * (3 * x))%nat).
  { intros x. rewrite (Nat.mul_assoc 5 3 x). reflexivity. }
  rewrite Nat.mul_1_r in E11.
  assert (HC11 : (11 * (2 * 2520) = 22 * 2520)%nat) by reflexivity.
  assert (W11 : z2v_C 11 = 22 * 2520).
  { transitivity (11 * (2 * 2520)); [exact E11 | exact HC11]. }
  rewrite W11 in E12.
  rewrite (H24r (z2v_C 12)) in E12.
  assert (W12a : (2 * z2v_C 12 = 22 * 2520)%nat)
    by exact (proj1 (Nat.mul_cancel_l (2 * z2v_C 12) (22 * 2520) 12 H12z)
                 E12).
  assert (HC12 : (22 * 2520 = 2 * (11 * 2520))%nat) by reflexivity.
  assert (W12 : z2v_C 12 = 11 * 2520)
    by exact (proj1 (Nat.mul_cancel_l (z2v_C 12) (11 * 2520) 2 H2z)
                 (eq_trans W12a HC12)).
  rewrite Nat.mul_1_r in E13.
  rewrite W12 in E13.
  assert (W13 : z2v_C 13 = 13 * (11 * 2520)) by exact E13.
  rewrite W13 in E14.
  rewrite (Nat.mul_comm (z2v_C 14) 14) in E14.
  assert (W14 : z2v_C 14 = 13 * (11 * 2520))
    by exact (proj1 (Nat.mul_cancel_l (z2v_C 14)
                       (13 * (11 * 2520)) 14 H14z) E14).
  rewrite W14 in E15.
  rewrite (Nat.mul_comm (z2v_C 15) 5) in E15.
  rewrite (H15d (13 * (11 * 2520))) in E15.
  assert (W15 : z2v_C 15 = 3 * (13 * (11 * 2520)))
    by exact (proj1 (Nat.mul_cancel_l (z2v_C 15)
                       (3 * (13 * (11 * 2520))) 5 H5z) E15).
  exact (conj W11 (conj W12 (conj W13 (conj W14 W15)))).
Qed.

(* ============================================================ *)
(* §3 比较面：3^13 基准与单调折返（布尔判定折返走 Nat.leb 范形）            *)
(* ============================================================ *)

(* 基准档：13·(11·2520) = 360360 ≤ 3^13 = 1594323、
   3·360360 = 1081080 ≤ 3^13（判定器范形内层计算，深层一元不出虚拟机堆） *)
Lemma zb3j_C13_le_anchor : (13 * (11 * 2520) <= 3 ^ 13)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma zb3j_C15_le_anchor : (3 * (13 * (11 * 2520)) <= 3 ^ 13)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

(* 主语句：[1,15] 全段 C 值序界（[1,10] 肢直取账本基座） *)
Theorem zb3j_base15 : forall n : nat,
  (1 <= n)%nat -> (n <= 15)%nat -> (z2v_C n <= 3 ^ n)%nat.
Proof.
  intros n H1 H15.
  pose proof zb3j_C_vals_11_15 as (WB & WC & WD & WE & WF).
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n16]]]]]]]]]]]]]]]].
  - lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - apply zb3m_C_le_3pow_base; lia.
  - rewrite WB. apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite WC. apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite WD. exact zb3j_C13_le_anchor.
  - rewrite WE. apply Nat.le_trans with (m := 3 ^ 13).
    + exact zb3j_C13_le_anchor.
    + apply Nat.pow_le_mono_r; lia.
  - rewrite WF. apply Nat.le_trans with (m := 3 ^ 13).
    + exact zb3j_C15_le_anchor.
    + apply Nat.pow_le_mono_r; lia.
  - lia.
Qed.

(* ============================================================ *)
(* §4 Set 面出口：HM2 面之 [1,15] 段实例（NatLe 承载）                      *)
(* ============================================================ *)

Theorem zb3j_HM2_face_15 : forall n : nat,
  (1 <= n)%nat -> (n <= 15)%nat -> zb3m_HM2_face n.
Proof.
  intros n H1 H15. unfold zb3m_HM2_face.
  apply NatLe_lift. apply zb3j_base15; assumption.
Qed.

(* ============================================================ *)
(* §5 假设审计（零全局假设复核）                                            *)
(* ============================================================ *)

Print Assumptions zb3j_G_diag_14_15.
Print Assumptions zb3j_C_vals_11_15.
Print Assumptions zb3j_C13_le_anchor.
Print Assumptions zb3j_C15_le_anchor.
Print Assumptions zb3j_base15.
Print Assumptions zb3j_HM2_face_15.
