(* ========================================================================== *)
(* abl_sqrtf_tail.v — SqrtF 收敛链尾程三段（Q 层实例闭合） *)
(* 模块名：abl_sqrtf_tail *)
(* 数学使命：UpReqSqrtF §8 尾程三段以供给定理闭合： *)
(*   ① 取档步：Q 层 sqrt2 Newton 具体实例显式 K:=1（s(z_1) == 1/12 ≤ m0:=1，数值定装零公设）＋阿基米德同位槽 Q 供给定理 sft_arch_le/sft_arch_hits（显式见证 K:=Z.to_nat(Qnum c)，2^K ≥ c）； *)
(*   ② 几何尾和逐 eps 上界：单步差=残差（望远镜）＋半化衰减＋几何级数和，显式 N 见证；主件 sft_q2_newton_cauchy（Qabs(·−·) 作 metric 同位，对应 UpReqSqrtF §2 被注释的 sqrtf_newton_cauchy 目标语形，严格 lt 出口）； *)
(*   ③ 方形非负位：接口层 nsq 假设位保持原样、不在此闭合（依原文判定）；Q 层同位件即 S02 Qsquare_nonneg 在册（本件 sft_q_square_nonneg 定名转发）。 *)
(* 依赖：S01_BaseRing、S02_CauchyComplete（Qsquare_nonneg/QleT'/桥）、S13_NLiveAudit（qle_congr_l/r）、QstepConvergenceBound（QltT'/序小件）、UpReqSqrtF（宿主链）。 *)
(* 对标：UpReqSqrtF §2 sqrtf_newton_cauchy 语形／§5 恒等式 g(y)² == 2 + s(y)²／§8 尾程三段结构；S02 Qsquare_nonneg 同位转发源。 *)
(* 构造性：全件 Qed 闭合、零承认词面、无经典逻辑；出口 QleT'/QltT'/sigT Set 面；中间层 Prop(Qle/Qlt) 仅供内部，出口零 Prop 泄露。 *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <编译目录> && 并发限 1：rocq c -native-compiler no -q -Q <缓存根> "" abl_sqrtf_tail.v *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S13_NLiveAudit.
Require Import QstepConvergenceBound.
Require Import UpReqSqrtF.

(* ============================================================ *)
(* §0 字面值与序小件                                              *)
(* ============================================================ *)

Lemma sft_q_0_lt_1 : Qlt 0 1.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_0_lt_2 : Qlt 0 2.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_0_lt_half : Qlt 0 (1#2)%Q.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_0_lt_sixth : Qlt 0 (1#6)%Q.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_sixth_lt_third : Qlt (1#6)%Q (1#3)%Q.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_2_half_one : Qeq ((2#1) * (1#2)%Q) 1.
Proof. reflexivity. Qed.

Lemma sft_q_double : forall b : Q, Qeq (b + b) (2 * b).
Proof. intro b. ring. Qed.

Lemma sft_q_neq0_of_lt : forall q : Q, Qlt 0 q -> ~ (q == 0).
Proof.
  intros q Hq Heq. apply (Qlt_not_eq 0 q Hq). symmetry. exact Heq.
Qed.

Lemma sft_q_plus_pos : forall u v : Q, Qlt 0 u -> Qlt 0 v -> Qlt 0 (u + v).
Proof.
  intros u v Hu Hv.
  apply (Qlt_le_trans 0 u (u + v) Hu).
  apply (qle_congr_l (u + 0) u (u + v)).
  - apply Qplus_0_r.
  - apply (Qplus_le_compat u u 0 v).
    + apply Qle_refl.
    + exact (Qlt_le_weak 0 v Hv).
Qed.

Lemma sft_q_inv_pos0 : forall q : Q, Qlt 0 q -> Qlt 0 (/ q).
Proof.
  intros q Hq.
  destruct (Qlt_le_dec 0 (/ q)) as [H | H].
  - exact H.
  - exfalso.
    assert (Hq0 : ~ (q == 0)) by (apply (sft_q_neq0_of_lt q Hq)).
    assert (Hstep : Qle ((/ q) * q) (0 * q)).
    { apply (Qmult_le_compat_r (/ q) 0 q).
      - exact H.
      - exact (Qlt_le_weak 0 q Hq). }
    assert (H1 : Qeq ((/ q) * q) 1).
    { rewrite (Qmult_comm (/ q) q). apply Qmult_inv_r. exact Hq0. }
    assert (H2 : Qeq (0 * q) 0) by apply Qmult_0_l.
    assert (Hfinal : Qle 1 0).
    { apply (qle_congr_r 1 (0 * q) 0).
      - exact H2.
      - apply (qle_congr_l ((/ q) * q) 1 (0 * q)).
        + exact H1.
        + exact Hstep. }
    exact (Qlt_irrefl 0 (Qlt_le_trans 0 1 0 sft_q_0_lt_1 Hfinal)).
Qed.

Lemma sft_q_div_pos : forall u q : Q, Qlt 0 u -> Qlt 0 q -> Qlt 0 (u / q).
Proof.
  intros u q Hu Hq. unfold Qdiv.
  pose proof (sft_q_inv_pos0 q Hq) as Hi.
  pose proof (Qmult_lt_compat_r 0 u (/ q) Hi Hu) as Hlt.
  rewrite Qmult_0_l in Hlt. exact Hlt.
Qed.

Lemma sft_q_half_pos0 : forall u : Q, Qlt 0 u -> Qlt 0 (u / 2).
Proof. intros u Hu. exact (sft_q_div_pos u (2#1)%Q Hu sft_q_0_lt_2). Qed.

(* 正因子消去（≤ 与 < 两向） *)
Lemma sft_q_le_cancel_pos : forall x y c : Q, Qlt 0 c -> Qle (x * c) (y * c) -> Qle x y.
Proof.
  intros x y c Hc H.
  destruct (Qlt_le_dec x y) as [Hlt | Hle].
  - exact (Qlt_le_weak x y Hlt).
  - assert (Hyc : Qle (y * c) (x * c)) by (apply (Qmult_le_compat_r y x c Hle (Qlt_le_weak 0 c Hc))).
    assert (Heq : Qeq (x * c) (y * c)) by (apply Qle_antisym; assumption).
    assert (Hc0 : ~ (c == 0)) by (apply (sft_q_neq0_of_lt c Hc)).
    assert (Hxy : Qeq x y).
    { transitivity ((x * c) * (/ c)).
      - rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hc0.
        symmetry. apply Qmult_1_r.
      - rewrite Heq.
        transitivity (y).
        + rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hc0.
          apply Qmult_1_r.
        + apply Qeq_refl. }
    apply (qle_congr_l y x y).
    + apply Qeq_sym. exact Hxy.
    + apply Qle_refl.
Qed.

Lemma sft_q_lt_cancel_pos : forall x y c : Q, Qlt 0 c -> Qlt (x * c) (y * c) -> Qlt x y.
Proof.
  intros x y c Hc H.
  destruct (Qlt_le_dec x y) as [Hlt | Hle].
  - exact Hlt.
  - exfalso.
    pose proof (Qmult_le_compat_r y x c Hle (Qlt_le_weak 0 c Hc)) as Hyc.
    exact (Qlt_irrefl (x * c) (Qlt_le_trans (x * c) (y * c) (x * c) H Hyc)).
Qed.

(* ============================================================ *)
(* §1 阿基米德同位槽 Q 供给定理（取档步配方位）：显式见证 2^K ≥ c       *)
(* ============================================================ *)

Fixpoint sft_p2 (k : nat) : Q :=
  match k with
  | Datatypes.O => 1
  | Datatypes.S j => 2 * sft_p2 j
  end.

Lemma sft_p2_pos : forall k : nat, Qlt 0 (sft_p2 k).
Proof.
  induction k as [| k IH].
  - exact sft_q_0_lt_1.
  - cbn [sft_p2].
    pose proof (Qmult_lt_compat_r 0 2 (sft_p2 k) IH sft_q_0_lt_2) as Hlt.
    rewrite Qmult_0_l in Hlt. exact Hlt.
Qed.

Lemma sft_p2_ge_half : forall k : nat, Qle (1#2)%Q (sft_p2 k).
Proof.
  induction k as [| k IH].
  - cbn [sft_p2]. unfold Qle. cbn [Qnum Qden]. lia.
  - cbn [sft_p2].
    apply (Qle_trans (1#2)%Q ((1#2)%Q * 2) (2 * sft_p2 k)).
    + assert (Hq : Qeq ((1#2)%Q * 2) 1) by (vm_compute; reflexivity).
      rewrite Hq. unfold Qle. cbn [Qnum Qden]. lia.
    + pose proof (Qmult_le_compat_r (1#2)%Q (sft_p2 k) 2 IH (Qlt_le_weak 0 2 sft_q_0_lt_2)) as Hm.
      apply (qle_congr_r ((1#2)%Q * 2) (sft_p2 k * 2) (2 * sft_p2 k)).
      * apply Qmult_comm.
      * exact Hm.
Qed.

Lemma sft_p2_le_succ : forall k : nat, Qle (sft_p2 k) (sft_p2 (Datatypes.S k)).
Proof.
  intro k. cbn [sft_p2].
  pose proof (sft_p2_pos k) as Hpos.
  apply (qle_congr_r (sft_p2 k) (sft_p2 k + sft_p2 k) (2 * sft_p2 k)).
  - apply sft_q_double.
  - apply (qle_congr_l (sft_p2 k + 0) (sft_p2 k) (sft_p2 k + sft_p2 k)).
    + apply Qplus_0_r.
    + apply (Qplus_le_compat (sft_p2 k) (sft_p2 k) 0 (sft_p2 k)).
      * apply Qle_refl.
      * exact (Qlt_le_weak 0 (sft_p2 k) Hpos).
Qed.

Lemma sft_p2_ge_one : forall k : nat, Qle 1 (sft_p2 k).
Proof.
  induction k as [| k IH].
  - apply Qle_refl.
  - cbn [sft_p2]. apply (Qle_trans 1 (sft_p2 k) (2 * sft_p2 k)).
    + exact IH.
    + exact (sft_p2_le_succ k).
Qed.

Lemma sft_p2_mono : forall j k : nat, (j <= k)%nat -> Qle (sft_p2 j) (sft_p2 k).
Proof.
  intros j k H. induction H as [| k Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans (sft_p2 j) (sft_p2 k) (sft_p2 (Datatypes.S k)) IH).
    apply sft_p2_le_succ.
Qed.

Lemma sft_qden_ge1 : forall q : Q, (1 <= Z.pos (Qden q))%Z.
Proof.
  intro q. destruct (Qden q) as [p | p | p]; lia.
Qed.

Lemma sft_qnum_pos_of_lt : forall q : Q, Qlt 0 q -> (0 < Qnum q)%Z.
Proof.
  intros q Hq. unfold Qlt in Hq.
  cbn [Qnum Qden] in Hq. lia.
Qed.

Lemma sft_p2_ge_Q1 : forall k : nat, (1 <= k)%nat -> Qle ((Z.of_nat k # 1)%Q) (sft_p2 k).
Proof.
  induction k as [| k IH]; intro Hk.
  - exfalso. lia.
  - destruct k as [| k'].
    + replace (Z.of_nat 1 # 1) with (1#1)%Q by reflexivity.
      exact (sft_p2_ge_one 1).
    + cbn [sft_p2].
      assert (Hsucc : Qeq ((Z.of_nat (Datatypes.S (Datatypes.S k')) # 1)%Q)
                          ((Z.of_nat (Datatypes.S k') # 1)%Q + 1)).
      { unfold Qeq, Qplus. cbn [Qnum Qden Qplus]. lia. }
      rewrite Hsucc.
      apply (Qle_trans ((Z.of_nat (Datatypes.S k') # 1)%Q + 1)
                       (sft_p2 (Datatypes.S k') + 1)
                       (2 * sft_p2 (Datatypes.S k'))).
      * apply (Qplus_le_compat (Z.of_nat (Datatypes.S k') # 1)%Q
                               (sft_p2 (Datatypes.S k')) 1 1).
        -- apply IH. lia.
        -- apply Qle_refl.
      * apply (Qle_trans (sft_p2 (Datatypes.S k') + 1)
                         (sft_p2 (Datatypes.S k') + sft_p2 (Datatypes.S k'))
                         (2 * sft_p2 (Datatypes.S k'))).
        -- apply (Qplus_le_compat (sft_p2 (Datatypes.S k')) (sft_p2 (Datatypes.S k'))
                    1 (sft_p2 (Datatypes.S k'))).
           ++ apply Qle_refl.
           ++ exact (sft_p2_ge_one (Datatypes.S k')).
        -- apply (qle_congr_r (sft_p2 (Datatypes.S k') + sft_p2 (Datatypes.S k'))
                              (sft_p2 (Datatypes.S k') + sft_p2 (Datatypes.S k'))
                              (2 * sft_p2 (Datatypes.S k'))).
           ++ apply sft_q_double.
           ++ apply Qle_refl.
Qed.

Definition sft_arch_witness (c : Q) : nat := Z.to_nat (Qnum c).

(* 阿基米德同位槽 Q 供给定理：显式见证 K := Z.to_nat (Qnum c)，2^K ≥ c。
   （接口层取档步所缺的阿基米德公设位，在 Q 层构造性供给。） *)
Lemma sft_arch_le : forall c : Q, Qlt 0 c -> Qle c (sft_p2 (sft_arch_witness c)).
Proof.
  intros c Hc. unfold sft_arch_witness.
  pose proof (sft_qnum_pos_of_lt c Hc) as Hp.
  pose proof (sft_qden_ge1 c) as Hq.
  assert (Hc1 : Qle c ((Qnum c # 1)%Q)).
  { unfold Qle. cbn [Qnum Qden].
    rewrite (Z.mul_comm (Qnum c) 1). rewrite (Z.mul_comm (Qnum c) (Z.pos (Qden c))).
    apply Z.mul_le_mono_nonneg_r.
    - lia.
    - exact Hq. }
  assert (Hnat : (1 <= Z.to_nat (Qnum c))%nat) by lia.
  pose proof (sft_p2_ge_Q1 (Z.to_nat (Qnum c)) Hnat) as Hc2.
  assert (Hznn : Qeq ((Qnum c # 1)%Q) ((Z.of_nat (Z.to_nat (Qnum c)) # 1)%Q)).
  { unfold Qeq. cbn [Qnum Qden].
    rewrite Z.mul_1_r. rewrite Z.mul_1_r.
    rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hc3 : Qle (Qnum c # 1)%Q (sft_p2 (Z.to_nat (Qnum c)))).
  { rewrite Hznn. exact Hc2. }
  exact (Qle_trans c (Qnum c # 1)%Q (sft_p2 (Z.to_nat (Qnum c))) Hc1 Hc3).
Qed.

Lemma sft_arch_hits : forall c : Q, Qlt 0 c -> QleT' c (sft_p2 (sft_arch_witness c)).
Proof.
  intros c Hc. apply Qle_to_QleT'. apply sft_arch_le. exact Hc.
Qed.

(* ============================================================ *)
(* §2 Q 层除式工具箱（quotient 正规化）                             *)
(* ============================================================ *)

Lemma sft_q_div_eq_r : forall x y z : Q, ~ (y == 0) -> Qeq (x / y) z -> Qeq x (z * y).
Proof.
  intros x y z Hy H.
  assert (Hre : Qeq x ((x / y) * y)).
  { unfold Qdiv. rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ y) y). rewrite Qmult_inv_r by exact Hy.
    rewrite Qmult_1_r. apply Qeq_refl. }
  transitivity ((x / y) * y).
  - exact Hre.
  - rewrite H. apply Qeq_refl.
Qed.

Lemma sft_q_div_eq_l : forall x y z : Q, ~ (y == 0) -> Qeq x (z * y) -> Qeq (x / y) z.
Proof.
  intros x y z Hy H.
  assert (Hre : Qeq ((z * y) / y) z).
  { unfold Qdiv. rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r by exact Hy. rewrite Qmult_1_r. apply Qeq_refl. }
  transitivity ((z * y) / y).
  - rewrite H. apply Qeq_refl.
  - exact Hre.
Qed.

Lemma sft_q_quot_scale : forall c u v : Q, Qeq (c * (u / v)) ((c * u) / v).
Proof. intros c u v. unfold Qdiv. rewrite <- Qmult_assoc. apply Qeq_refl. Qed.

Lemma sft_q_quot_same : forall u w v : Q, Qeq u w -> Qeq (u / v) (w / v).
Proof.
  intros u w v H. unfold Qdiv. rewrite H. apply Qeq_refl.
Qed.

Lemma sft_q_mult_cancel_r : forall x y z : Q, ~ (z == 0) -> Qeq (x * z) (y * z) -> Qeq x y.
Proof.
  intros x y z Hz H.
  transitivity ((x * z) * (/ z)).
  - rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hz.
    symmetry. apply Qmult_1_r.
  - rewrite H. rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r by exact Hz.
    apply Qmult_1_r.
Qed.

Lemma sft_q_eq_mul_r : forall x y d : Q, ~ (d == 0) -> Qeq (x * d) (y * d) -> Qeq x y.
Proof. intros x y d Hd H. apply (sft_q_mult_cancel_r x y d Hd H). Qed.

Lemma sft_q_le_mul_ge_one : forall c P : Q, Qle 0 c -> Qle 1 P -> Qle (1 * c) (P * c).
Proof.
  intros c P Hc0 HP1.
  exact (Qmult_le_compat_r 1 P c HP1 Hc0).
Qed.

Lemma sft_q_mul_neq0 : forall v t : Q, ~ (v == 0) -> ~ (t == 0) -> ~ (v * t == 0).
Proof.
  intros v t Hv Ht H. apply Hv.
  transitivity ((v * t) * (/ t)).
  - rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Ht.
    symmetry. apply Qmult_1_r.
  - rewrite H. apply Qmult_0_l.
Qed.

Lemma sft_q_two_mul_neq0 : forall y : Q, ~ (y == 0) -> ~ (2 * y == 0).
Proof.
  intros y Hy. apply (sft_q_mul_neq0 2 y).
  - apply sft_q_neq0_of_lt. exact sft_q_0_lt_2.
  - exact Hy.
Qed.

Lemma sft_q_quot_mul_cancel : forall u v : Q, ~ (v == 0) -> Qeq ((u / v) * v) u.
Proof.
  intros u v Hv. unfold Qdiv. rewrite <- Qmult_assoc.
  rewrite (Qmult_comm (/ v) v). rewrite Qmult_inv_r by exact Hv.
  apply Qmult_1_r.
Qed.

Lemma sft_q_div_neq0 : forall u v : Q, ~ (u == 0) -> ~ (v == 0) -> ~ (u / v == 0).
Proof.
  intros u v Hu Hv H. apply Hu.
  transitivity ((u / v) * v).
  - symmetry. exact (sft_q_quot_mul_cancel u v Hv).
  - rewrite H. apply Qmult_0_l.
Qed.

Lemma sft_q_quot_mul : forall u v w t : Q, ~ (v == 0) -> ~ (t == 0) ->
  Qeq ((u / v) * (w / t)) ((u * w) / (v * t)).
Proof.
  intros u v w t Hv Ht.
  assert (Hvt : ~ (v * t == 0)) by (apply (sft_q_mul_neq0 v t); assumption).
  field; repeat split; assumption.
Qed.

Lemma sft_q_sub_quot : forall a u v : Q, ~ (v == 0) -> Qeq (a - u / v) ((a * v - u) / v).
Proof. intros a u v Hv. field; repeat split; assumption. Qed.

Lemma sft_q_add_quot : forall u v a : Q, ~ (v == 0) -> Qeq (u / v + a) ((u + a * v) / v).
Proof. intros u v a Hv. field; repeat split; assumption. Qed.

Lemma sft_q_mult_minus_distr_l : forall x y z : Q, Qeq (x * (y - z)) (x * y - x * z).
Proof. intros x y z. ring. Qed.

Lemma sft_q_mult_minus_distr_r : forall x y z : Q, Qeq ((x - y) * z) (x * z - y * z).
Proof. intros x y z. ring. Qed.

Lemma sft_q_const_div_quot : forall c u v : Q,
  ~ (u == 0) -> ~ (v == 0) -> Qeq (c / (u / v)) ((c * v) / u).
Proof.
  intros c u v Hu Hv.
  assert (Huv : ~ (u / v == 0)) by (apply (sft_q_div_neq0 u v Hu Hv)).
  field; repeat split; assumption.
Qed.

Lemma sft_q_quot_div_quot : forall u v w t : Q, ~ (v == 0) -> ~ (w == 0) -> ~ (t == 0) ->
  Qeq ((u / v) / (w / t)) ((u * t) / (v * w)).
Proof.
  intros u v w t Hv Hw Ht.
  assert (Hwt : ~ (w / t == 0)) by (apply (sft_q_div_neq0 w t Hw Ht)).
  assert (Hvw : ~ (v * w == 0)) by (apply (sft_q_mul_neq0 v w); assumption).
  field; repeat split; assumption.
Qed.

Lemma sft_q_quot_quot_const : forall u v w : Q, ~ (v == 0) -> ~ (w == 0) ->
  Qeq ((u / v) / w) (u / (v * w)).
Proof.
  intros u v w Hv Hw.
  assert (Hvw : ~ (v * w == 0)) by (apply (sft_q_mul_neq0 v w); assumption).
  field; repeat split; assumption.
Qed.

(* ============================================================ *)
(* §3 Q 层 sqrt2 Newton 实例与取档步（显式 K:=1）                   *)
(*    方形墙 Q 同位件（S02 Qsquare_nonneg 定名转发）置首——§4 压缩链    *)
(*    的 t² ≥ 0 由它供给（接口层 nsq 假设位不闭合的可行残形）。             *)
(* ============================================================ *)

Lemma sft_q_square_nonneg : forall q : Q, Qle 0 (q * q).
Proof. intro q. exact (Qsquare_nonneg q). Qed.

Lemma sft_q_0_lt_3 : Qlt 0 3.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Lemma sft_q_0_lt_twelfth : Qlt 0 (1#12)%Q.
Proof. unfold Qlt. apply Z.ltb_lt. cbn [Qnum Qden]. lia. Qed.

Definition sft_q2_step (y : Q) : Q := (1#2)%Q * (y + 2 / y).
Definition sft_q2_slack (y : Q) : Q := (1#2)%Q * (y - 2 / y).
Definition sft_q2_metric (u v : Q) : Q := Qabs (u - v).

Fixpoint sft_q2_newton (n : nat) : Q :=
  match n with
  | Datatypes.O => 1
  | Datatypes.S m => sft_q2_step (sft_q2_newton m)
  end.

Lemma sft_q2_newton_succ : forall n : nat,
  Qeq (sft_q2_newton (Datatypes.S n)) (sft_q2_step (sft_q2_newton n)).
Proof. intro n. reflexivity. Qed.

Lemma sft_q2_step_pos : forall y : Q, Qlt 0 y -> Qlt 0 (sft_q2_step y).
Proof.
  intros y Hy. unfold sft_q2_step.
  pose proof (sft_q_div_pos 2 y sft_q_0_lt_2 Hy) as Hd.
  pose proof (sft_q_plus_pos y (2 / y) Hy Hd) as Hp.
  pose proof (Qmult_lt_compat_r 0 (1#2)%Q (y + 2 / y) Hp sft_q_0_lt_half) as Hm.
  rewrite Qmult_0_l in Hm. exact Hm.
Qed.

Lemma sft_q2_newton_pos : forall n : nat, Qlt 0 (sft_q2_newton n).
Proof.
  induction n as [| n IH].
  - exact sft_q_0_lt_1.
  - exact (sft_q2_step_pos (sft_q2_newton n) IH).
Qed.

Lemma sft_qabs_pos_self : forall q : Q, Qlt 0 q -> Qeq (Qabs q) q.
Proof.
  intros [a b] Hq. unfold Qlt in Hq. cbn [Qnum Qden] in Hq.
  cbn [Qabs].
  assert (Hz : (Z.abs a = a)%Z) by (apply Z.abs_eq; lia).
  rewrite Hz. apply Qeq_refl.
Qed.

Lemma sft_qabs_nonneg_self : forall q : Q, Qle 0 q -> Qeq (Qabs q) q.
Proof.
  intros [a b] Hq. unfold Qle in Hq. cbn [Qnum Qden] in Hq.
  cbn [Qabs].
  assert (Hz : (Z.abs a = a)%Z) by (apply Z.abs_eq; lia).
  rewrite Hz. apply Qeq_refl.
Qed.

Lemma sft_qabs_eq : forall u v : Q, Qeq u v -> Qeq (Qabs u) (Qabs v).
Proof.
  intros [a b] [c d] H. unfold Qeq in H. cbn [Qnum Qden] in H.
  unfold Qabs, Qeq. cbn [Qnum Qden].
  assert (Hb1 : (1 <= Z.pos b)%Z) by exact (sft_qden_ge1 (a # b)%Q).
  assert (Hd1 : (1 <= Z.pos d)%Z) by exact (sft_qden_ge1 (c # d)%Q).
  transitivity (Z.abs (a * Z.pos d)).
  - rewrite Z.abs_mul. rewrite (Z.abs_eq (Z.pos d)) by lia. reflexivity.
  - rewrite H. rewrite Z.abs_mul. rewrite (Z.abs_eq (Z.pos b)) by lia. reflexivity.
Qed.

(* 数值定装：s(z_1) == 1/12（z_1 = step 1 = 3/2），零公设。 *)
Lemma sft_q2_slack_z1 : Qeq (sft_q2_slack (sft_q2_newton 1)) (1#12)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 取档步：显式见证 K := 1，|s(z_1)| == 1/12 ≤ m0 := 1。 *)
Lemma sft_q2_fetch : QleT' (Qabs (sft_q2_slack (sft_q2_newton 1))) (1#1)%Q.
Proof.
  apply Qle_to_QleT'.
  assert (Hpos : Qlt 0 (sft_q2_slack (sft_q2_newton 1)))
    by (vm_compute; reflexivity).
  rewrite (sft_qabs_pos_self _ Hpos).
  rewrite sft_q2_slack_z1.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma sft_q2_fetch_ex : sigT (fun K : nat => QleT' (Qabs (sft_q2_slack (sft_q2_newton K))) (1#1)%Q).
Proof.
  exact (existT (A := nat) (fun K : nat => QleT' (Qabs (sft_q2_slack (sft_q2_newton K))) (1#1)%Q)
           1%nat sft_q2_fetch).
Qed.

(* ============================================================ *)
(* §4 压缩链：§5 恒等式同位 + 平方下界（非负性事实在此引入）+ 半化衰减       *)
(* ============================================================ *)

Lemma sft_q2_step_eq : forall y : Q, ~ (y == 0) -> Qeq (sft_q2_step y) ((y * y + 2) / (2 * y)).
Proof.
  intros y Hy.
  assert (H2y : ~ (2 * y == 0)) by (apply sft_q_two_mul_neq0; exact Hy).
  unfold sft_q2_step. field; repeat split; assumption.
Qed.

Lemma sft_q2_slack_eq : forall y : Q, ~ (y == 0) -> Qeq (sft_q2_slack y) ((y * y - 2) / (2 * y)).
Proof.
  intros y Hy.
  assert (H2y : ~ (2 * y == 0)) by (apply sft_q_two_mul_neq0; exact Hy).
  unfold sft_q2_slack. field; repeat split; assumption.
Qed.

(* §5 恒等式 Q 同位：g(y)² == 2 + s(y)²（宿主 UpReqSqrtF §5 的 Q 层对应形） *)
Lemma sft_q2_step_sq : forall y : Q, ~ (y == 0) ->
  Qeq (sft_q2_step y * sft_q2_step y) (2 + sft_q2_slack y * sft_q2_slack y).
Proof. intros y Hy. unfold sft_q2_step, sft_q2_slack. field; repeat split; assumption. Qed.

(* 压缩比率恒等式 Q 同位：2·g(y)·s(g(y)) == s(y)²（nsq_slack_contraction 同位） *)
Lemma sft_q2_contract : forall y : Q, Qlt 0 y ->
  Qeq (2 * sft_q2_step y * sft_q2_slack (sft_q2_step y)) (sft_q2_slack y * sft_q2_slack y).
Proof.
  intros y Hy.
  assert (Hy0 : ~ (y == 0)) by (apply sft_q_neq0_of_lt; exact Hy).
  assert (Hn2 : ~ (y * y + 2 == 0)).
  { intro Hs.
    assert (Hle : Qle 0 (-2)%Q).
    { apply (qle_congr_r 0 (y * y) (-2)%Q).
      - transitivity ((y * y + 2) - 2).
        + ring.
        + rewrite Hs. ring.
      - exact (sft_q_square_nonneg y). }
    unfold Qle in Hle. cbn [Qnum Qden] in Hle. lia. }
  unfold sft_q2_step, sft_q2_slack. field; repeat split; assumption.
Qed.

(* g(y) ≥ 1：由 (y-1)² + 1 ≥ 0（Qsquare_nonneg 供给）交叉乘出 *)
Lemma sft_q2_step_ge_one : forall y : Q, Qlt 0 y -> Qle 1 (sft_q2_step y).
Proof.
  intros y Hy.
  assert (Hsq1 : Qle 0 ((y - 1) * (y - 1))) by (apply sft_q_square_nonneg).
  assert (HW : Qle 0 ((y - 1) * (y - 1) + 1)).
  { apply (qle_congr_l (0 + 0) 0 ((y - 1) * (y - 1) + 1)).
    - apply Qplus_0_l.
    - apply (Qplus_le_compat 0 ((y - 1) * (y - 1)) 0 1).
      + exact Hsq1.
      + exact (Qlt_le_weak 0 1 sft_q_0_lt_1). }
  assert (H2y : Qle (2 * y) (y * y + 2)).
  { apply (qle_congr_l (2 * y + 0) (2 * y) (y * y + 2)).
    - apply Qplus_0_r.
    - apply (qle_congr_r (2 * y + 0) (2 * y + ((y - 1) * (y - 1) + 1)) (y * y + 2)).
      + ring.
      + apply (Qplus_le_compat (2 * y) (2 * y) 0 ((y - 1) * (y - 1) + 1)).
        * apply Qle_refl.
        * exact HW. }
  assert (Hy0 : ~ (y == 0)) by (apply sft_q_neq0_of_lt; exact Hy).
  assert (Hden0 : ~ (2 * y == 0)) by (apply sft_q_two_mul_neq0; exact Hy0).
  assert (H2ypos : Qlt 0 (2 * y)).
  { pose proof (Qmult_lt_compat_r 0 2 y Hy sft_q_0_lt_2) as Hm.
    rewrite Qmult_0_l in Hm. exact Hm. }
  assert (Hinv : Qlt 0 (/ (2 * y))) by (apply sft_q_inv_pos0; exact H2ypos).
  pose proof (Qmult_le_compat_r (2 * y) (y * y + 2) (/ (2 * y)) H2y
                (Qlt_le_weak 0 (/ (2 * y)) Hinv)) as Hm.
  rewrite (Qmult_inv_r (2 * y) Hden0) in Hm.
  apply (qle_congr_r 1 ((y * y + 2) * / (2 * y)) (sft_q2_step y)).
  - exact (Qeq_sym (sft_q2_step y) ((y * y + 2) / (2 * y)) (sft_q2_step_eq y Hy0)).
  - exact Hm.
Qed.

(* 平方下界：z_n² ≥ 2（n ≥ 1）——逐步 = 2 + s(z_n)²，非负性事实 s² ≥ 0 供给 *)
Lemma sft_q2_z_sq_ge : forall n : nat, (1 <= n)%nat -> Qle 2 (sft_q2_newton n * sft_q2_newton n).
Proof.
  induction n as [| n IH]; intro Hn.
  - exfalso. lia.
  - destruct n as [| k].
    + assert (Hz1 : Qeq (sft_q2_newton 1 * sft_q2_newton 1) (9#4)%Q)
        by (vm_compute; reflexivity).
      rewrite Hz1. unfold Qle. cbn [Qnum Qden]. lia.
    + rewrite (sft_q2_newton_succ (Datatypes.S k)).
      assert (Hz0 : ~ (sft_q2_newton (Datatypes.S k) == 0))
        by (apply sft_q_neq0_of_lt; apply sft_q2_newton_pos).
      rewrite (sft_q2_step_sq (sft_q2_newton (Datatypes.S k)) Hz0).
      apply (qle_congr_l (2 + 0) 2
              (2 + sft_q2_slack (sft_q2_newton (Datatypes.S k))
                   * sft_q2_slack (sft_q2_newton (Datatypes.S k)))).
      * apply Qplus_0_r.
      * apply (Qplus_le_compat 2 2 0
              (sft_q2_slack (sft_q2_newton (Datatypes.S k))
               * sft_q2_slack (sft_q2_newton (Datatypes.S k)))).
        -- apply Qle_refl.
        -- apply sft_q_square_nonneg.
Qed.

(* s(step y) ≥ 0：由压缩恒等式 s(g) == s(y)²/(2g) 与非负性事实 *)
Lemma sft_q2_slack_step_nonneg : forall y : Q, Qlt 0 y -> Qle 0 (sft_q2_slack (sft_q2_step y)).
Proof.
  intros y Hy.
  assert (Hy0 : ~ (y == 0)) by (apply sft_q_neq0_of_lt; exact Hy).
  assert (Hg0 : ~ (sft_q2_step y == 0))
    by (apply sft_q_neq0_of_lt; apply sft_q2_step_pos; exact Hy).
  assert (H2g : Qlt 0 (2 * sft_q2_step y)).
  { pose proof (Qmult_lt_compat_r 0 2 (sft_q2_step y) (sft_q2_step_pos y Hy) sft_q_0_lt_2) as Hm.
    rewrite Qmult_0_l in Hm. exact Hm. }
  assert (H2g0 : ~ (2 * sft_q2_step y == 0)) by (apply sft_q_neq0_of_lt; exact H2g).
  pose proof (sft_q2_contract y Hy) as E.
  assert (Es : Qeq (sft_q2_slack (sft_q2_step y))
                   ((sft_q2_slack y * sft_q2_slack y) / (2 * sft_q2_step y))).
  { apply (sft_q_eq_mul_r (sft_q2_slack (sft_q2_step y))
             ((sft_q2_slack y * sft_q2_slack y) / (2 * sft_q2_step y))
             (2 * sft_q2_step y) H2g0).
    rewrite (sft_q_quot_mul_cancel (sft_q2_slack y * sft_q2_slack y)
               (2 * sft_q2_step y) H2g0).
    transitivity (2 * sft_q2_step y * sft_q2_slack (sft_q2_step y)).
    - ring.
    - exact E. }
  pose proof (Qmult_le_compat_r 0 (sft_q2_slack y * sft_q2_slack y)
                (/ (2 * sft_q2_step y)) (sft_q_square_nonneg _)
                (Qlt_le_weak 0 (/ (2 * sft_q2_step y))
                   (sft_q_inv_pos0 (2 * sft_q2_step y) H2g))) as Hraw.
  rewrite Qmult_0_l in Hraw.
  apply (qle_congr_r 0 ((sft_q2_slack y * sft_q2_slack y) * / (2 * sft_q2_step y))
                      (sft_q2_slack (sft_q2_step y))).
  - exact (Qeq_sym (sft_q2_slack (sft_q2_step y))
             ((sft_q2_slack y * sft_q2_slack y) / (2 * sft_q2_step y)) Es).
  - exact Hraw.
Qed.

Lemma sft_q2_slack_nonneg : forall n : nat, (1 <= n)%nat -> Qle 0 (sft_q2_slack (sft_q2_newton n)).
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - replace (sft_q2_newton (Datatypes.S k))
      with (sft_q2_step (sft_q2_newton (Nat.pred (Datatypes.S k)))) by reflexivity.
    apply sft_q2_slack_step_nonneg. apply sft_q2_newton_pos.
Qed.

Lemma sft_q_sub_le : forall z s : Q, Qle 0 s -> Qle (z - s) z.
Proof.
  intros z s Hs. apply (qle_minus_pos (z - s) z).
  apply (qle_congr_r 0 s (z - (z - s))).
  - ring.
  - exact Hs.
Qed.

Lemma sft_q2_telescope : forall y : Q, Qeq (sft_q2_step y) (y - sft_q2_slack y).
Proof. intros y. unfold sft_q2_step, sft_q2_slack. ring. Qed.

Lemma sft_q2_step_le : forall n : nat, (1 <= n)%nat -> Qle (sft_q2_newton (Datatypes.S n)) (sft_q2_newton n).
Proof.
  intros n Hn.
  rewrite (sft_q2_newton_succ n).
  rewrite (sft_q2_telescope (sft_q2_newton n)).
  apply sft_q_sub_le.
  apply (sft_q2_slack_nonneg n Hn).
Qed.

Lemma sft_q2_mono : forall d n : nat, (1 <= n)%nat -> Qle (sft_q2_newton (n + d)) (sft_q2_newton n).
Proof.
  induction d as [| d IH]; intros n Hn.
  - rewrite Nat.add_0_r. apply Qle_refl.
  - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d)) by lia.
    rewrite (sft_q2_newton_succ (n + d)).
    apply (Qle_trans (sft_q2_step (sft_q2_newton (n + d)))
                     (sft_q2_newton (n + d)) (sft_q2_newton n)).
    + apply sft_q2_step_le. lia.
    + apply IH. exact Hn.
Qed.

(* 半化：2·s(g(y)) ≤ s(y)（0 < y, y² ≥ 2, 0 ≤ s(y) ≤ 1） *)
Lemma sft_q2_halving : forall y : Q, Qlt 0 y -> Qle 2 (y * y) -> Qle 0 (sft_q2_slack y) ->
  Qle (sft_q2_slack y) 1 -> Qle (2 * sft_q2_slack (sft_q2_step y)) (sft_q2_slack y).
Proof.
  intros y Hy Hsq Hs0 Hs1.
  assert (Hg1 : Qle 1 (sft_q2_step y)) by (apply sft_q2_step_ge_one; exact Hy).
  assert (Hsg0 : Qle 0 (2 * sft_q2_slack (sft_q2_step y))).
  { pose proof (Qmult_le_compat_r 0 2 (sft_q2_slack (sft_q2_step y))
                  (Qlt_le_weak 0 2 sft_q_0_lt_2) (sft_q2_slack_step_nonneg y Hy)) as Hm.
    rewrite Qmult_0_l in Hm. exact Hm. }
  pose proof (sft_q2_contract y Hy) as E.
  pose proof (sft_q_le_mul_ge_one (2 * sft_q2_slack (sft_q2_step y)) (sft_q2_step y)
                Hsg0 Hg1) as Hc1.
  pose proof (Qmult_le_compat_r (sft_q2_slack y) 1 (sft_q2_slack y) Hs1 Hs0) as Hss.
  apply (Qle_trans (2 * sft_q2_slack (sft_q2_step y))
                   (sft_q2_slack y * sft_q2_slack y)
                   (sft_q2_slack y)).
  - rewrite <- E.
    apply (qle_congr_l (1 * (2 * sft_q2_slack (sft_q2_step y)))
                       (2 * sft_q2_slack (sft_q2_step y))
                       (2 * sft_q2_step y * sft_q2_slack (sft_q2_step y))).
    + apply Qmult_1_l.
    + apply (qle_congr_r (1 * (2 * sft_q2_slack (sft_q2_step y)))
                         (sft_q2_step y * (2 * sft_q2_slack (sft_q2_step y)))
                         (2 * sft_q2_step y * sft_q2_slack (sft_q2_step y))).
      * ring.
      * exact Hc1.
  - apply (qle_congr_r (sft_q2_slack y * sft_q2_slack y)
                       (1 * sft_q2_slack y)
                       (sft_q2_slack y)).
    + apply Qmult_1_l.
    + exact Hss.
Qed.

Lemma sft_q2_two_slack_nonneg : forall n : nat, (1 <= n)%nat ->
  Qle 0 (2 * sft_q2_slack (sft_q2_newton n)).
Proof.
  intros n Hn.
  pose proof (Qmult_le_compat_r 0 2 (sft_q2_slack (sft_q2_newton n))
                (Qlt_le_weak 0 2 sft_q_0_lt_2) (sft_q2_slack_nonneg n Hn)) as Hm.
  rewrite Qmult_0_l in Hm. exact Hm.
Qed.

(* 尾和衰减：2·s(z_n)·2^(n-1) ≤ 1/6（n ≥ 1；基例 2·(1/12)·1 = 1/6 数值定装） *)
Lemma sft_q2_tail_decay : forall n : nat, (1 <= n)%nat ->
  Qle ((2 * sft_q2_slack (sft_q2_newton n)) * sft_p2 (Nat.pred n)) (1#6)%Q.
Proof.
  induction n as [| n IH]; intro Hn.
  - exfalso. lia.
  - destruct n as [| k'].
    + (* n = 1：数值定装 *)
      assert (H : Qeq ((2 * sft_q2_slack (sft_q2_newton 1)) * sft_p2 (Nat.pred 1))
                      (1#6)%Q) by (vm_compute; reflexivity).
      apply (qle_congr_r ((2 * sft_q2_slack (sft_q2_newton 1)) * sft_p2 (Nat.pred 1))
                         ((2 * sft_q2_slack (sft_q2_newton 1)) * sft_p2 (Nat.pred 1))
                         (1#6)%Q).
      * exact H.
      * apply Qle_refl.
    + (* n = S (S k') ≥ 2 *)
      assert (Hk1 : (1 <= Datatypes.S k')%nat) by lia.
      pose proof (IH Hk1) as HIH.
      assert (Hs1 : Qle (sft_q2_slack (sft_q2_newton (Datatypes.S k'))) 1).
      { pose proof (sft_q_le_mul_ge_one (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                      (sft_p2 k')
                      (sft_q2_two_slack_nonneg (Datatypes.S k') Hk1)
                      (sft_p2_ge_one k')) as Hc0.
        rewrite (Qmult_1_l (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))) in Hc0.
        rewrite (Qmult_comm (sft_p2 k')
                   (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))) in Hc0.
        pose proof (Qle_trans (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                      ((2 * sft_q2_slack (sft_q2_newton (Datatypes.S k'))) * sft_p2 k')
                      (1#6)%Q Hc0 HIH) as H2s6.
        apply (Qle_trans (sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                         (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k'))) (1#1)%Q).
        - apply (qle_congr_l (1 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                             (sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                             (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))).
          + apply Qmult_1_l.
          + exact (sft_q_le_mul_ge_one (sft_q2_slack (sft_q2_newton (Datatypes.S k'))) 2
                     (sft_q2_slack_nonneg (Datatypes.S k') Hk1) (sft_p2_ge_one 1)).
        - apply (Qle_trans (2 * sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                           (1#6)%Q (1#1)%Q).
          + exact H2s6.
          + unfold Qle. cbn [Qnum Qden]. lia. }
      assert (Hhalv : Qle (2 * sft_q2_slack (sft_q2_newton (Datatypes.S (Datatypes.S k'))))
                          (sft_q2_slack (sft_q2_newton (Datatypes.S k')))).
      { apply sft_q2_halving.
        - apply sft_q2_newton_pos.
        - apply sft_q2_z_sq_ge. exact Hk1.
        - apply sft_q2_slack_nonneg. exact Hk1.
        - exact Hs1. }
      assert (H2P : Qlt 0 (2 * sft_p2 k')).
      { pose proof (Qmult_lt_compat_r 0 2 (sft_p2 k') (sft_p2_pos k') sft_q_0_lt_2) as Hm.
        rewrite Qmult_0_l in Hm. exact Hm. }
      apply (Qle_trans ((2 * sft_q2_slack (sft_q2_newton (Datatypes.S (Datatypes.S k'))))
                        * (2 * sft_p2 k'))
                       (sft_q2_slack (sft_q2_newton (Datatypes.S k')) * (2 * sft_p2 k'))
                       (1#6)%Q).
      * apply (Qmult_le_compat_r (2 * sft_q2_slack (sft_q2_newton (Datatypes.S (Datatypes.S k'))))
                                 (sft_q2_slack (sft_q2_newton (Datatypes.S k')))
                                 (2 * sft_p2 k') Hhalv (Qlt_le_weak 0 _ H2P)).
      * assert (Hab : Qeq (sft_q2_slack (sft_q2_newton (Datatypes.S k')) * (2 * sft_p2 k'))
                          ((2 * sft_q2_slack (sft_q2_newton (Datatypes.S k'))) * sft_p2 k'))
          by ring.
        rewrite Hab. exact HIH.
Qed.

Lemma sft_q2_slack_le_one : forall n : nat, (1 <= n)%nat -> Qle (sft_q2_slack (sft_q2_newton n)) 1.
Proof.
  intros n Hn.
  pose proof (sft_q2_tail_decay n Hn) as Hk.
  pose proof (sft_q_le_mul_ge_one (2 * sft_q2_slack (sft_q2_newton n))
                (sft_p2 (Nat.pred n))
                (sft_q2_two_slack_nonneg n Hn) (sft_p2_ge_one (Nat.pred n))) as Hc0.
  rewrite (Qmult_1_l (2 * sft_q2_slack (sft_q2_newton n))) in Hc0.
  rewrite (Qmult_comm (sft_p2 (Nat.pred n))
             (2 * sft_q2_slack (sft_q2_newton n))) in Hc0.
  pose proof (Qle_trans (2 * sft_q2_slack (sft_q2_newton n))
                ((2 * sft_q2_slack (sft_q2_newton n)) * sft_p2 (Nat.pred n))
                (1#6)%Q Hc0 Hk) as H2s6.
  apply (Qle_trans (sft_q2_slack (sft_q2_newton n))
                   (2 * sft_q2_slack (sft_q2_newton n)) (1#1)%Q).
  - apply (qle_congr_l (1 * sft_q2_slack (sft_q2_newton n))
                       (sft_q2_slack (sft_q2_newton n))
                       (2 * sft_q2_slack (sft_q2_newton n))).
    + apply Qmult_1_l.
    + exact (sft_q_le_mul_ge_one (sft_q2_slack (sft_q2_newton n)) 2
               (sft_q2_slack_nonneg n Hn) (sft_p2_ge_one 1)).
  - apply (Qle_trans (2 * sft_q2_slack (sft_q2_newton n)) (1#6)%Q (1#1)%Q).
    + exact H2s6.
    + unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 尾和：z_n − z_{n+d} ≤ 2·s(z_n)（n ≥ 1）——不变式
   J(e)：z_n − z_{n+e} + 2·s(z_{n+e}) ≤ 2·s(z_n)，半化步进。 *)
Lemma sft_q2_tail_sum : forall d n : nat, (1 <= n)%nat ->
  Qle (sft_q2_newton n - sft_q2_newton (n + d)) (2 * sft_q2_slack (sft_q2_newton n)).
Proof.
  intros d n Hn.
  assert (J : forall e : nat,
    Qle (sft_q2_newton n - sft_q2_newton (n + e)
         + 2 * sft_q2_slack (sft_q2_newton (n + e)))
        (2 * sft_q2_slack (sft_q2_newton n))).
  { induction e as [| e IHe].
    - rewrite Nat.add_0_r.
      apply (qle_congr_r (sft_q2_newton n - sft_q2_newton n
                          + 2 * sft_q2_slack (sft_q2_newton n))
                         (sft_q2_newton n - sft_q2_newton n
                          + 2 * sft_q2_slack (sft_q2_newton n))
                         (2 * sft_q2_slack (sft_q2_newton n))).
      + ring.
      + apply Qle_refl.
    - replace (n + Datatypes.S e)%nat with (Datatypes.S (n + e)) by lia.
      change (Qle (sft_q2_newton n
                   - sft_q2_step (sft_q2_newton (n + e))
                   + 2 * sft_q2_slack (sft_q2_step (sft_q2_newton (n + e))))
                  (2 * sft_q2_slack (sft_q2_newton n))).
      assert (Hne1 : (1 <= n + e)%nat) by lia.
      pose proof (sft_q2_halving (sft_q2_newton (n + e))
                    (sft_q2_newton_pos (n + e))
                    (sft_q2_z_sq_ge (n + e) Hne1)
                    (sft_q2_slack_nonneg (n + e) Hne1)
                    (sft_q2_slack_le_one (n + e) Hne1)) as Hhalv.
      assert (HA : Qeq (sft_q2_newton n - sft_q2_step (sft_q2_newton (n + e)))
                       ((sft_q2_newton n - sft_q2_newton (n + e))
                        + sft_q2_slack (sft_q2_newton (n + e)))).
      { transitivity (sft_q2_newton n
                      - (sft_q2_newton (n + e) - sft_q2_slack (sft_q2_newton (n + e)))).
        - rewrite (sft_q2_telescope (sft_q2_newton (n + e))). apply Qeq_refl.
        - ring. }
      rewrite HA.
      apply (Qle_trans ((sft_q2_newton n - sft_q2_newton (n + e))
                        + sft_q2_slack (sft_q2_newton (n + e))
                        + 2 * sft_q2_slack (sft_q2_step (sft_q2_newton (n + e))))
                       ((sft_q2_newton n - sft_q2_newton (n + e))
                        + sft_q2_slack (sft_q2_newton (n + e))
                        + sft_q2_slack (sft_q2_newton (n + e)))
                       (2 * sft_q2_slack (sft_q2_newton n))).
      + apply (Qplus_le_compat
                 ((sft_q2_newton n - sft_q2_newton (n + e))
                  + sft_q2_slack (sft_q2_newton (n + e)))
                 ((sft_q2_newton n - sft_q2_newton (n + e))
                  + sft_q2_slack (sft_q2_newton (n + e)))
                 (2 * sft_q2_slack (sft_q2_step (sft_q2_newton (n + e))))
                 (sft_q2_slack (sft_q2_newton (n + e)))).
        * apply Qle_refl.
        * exact Hhalv.
      + assert (Hab : Qeq ((sft_q2_newton n - sft_q2_newton (n + e))
                           + sft_q2_slack (sft_q2_newton (n + e))
                           + sft_q2_slack (sft_q2_newton (n + e)))
                          (sft_q2_newton n - sft_q2_newton (n + e)
                           + 2 * sft_q2_slack (sft_q2_newton (n + e)))) by ring.
        rewrite Hab. exact IHe. }
  assert (Hnd : (1 <= n + d)%nat) by lia.
  apply (Qle_trans (sft_q2_newton n - sft_q2_newton (n + d))
                   (sft_q2_newton n - sft_q2_newton (n + d)
                    + 2 * sft_q2_slack (sft_q2_newton (n + d)))
                   (2 * sft_q2_slack (sft_q2_newton n))).
  - apply (qle_congr_l (sft_q2_newton n - sft_q2_newton (n + d) + 0)
                       (sft_q2_newton n - sft_q2_newton (n + d))
                       (sft_q2_newton n - sft_q2_newton (n + d)
                        + 2 * sft_q2_slack (sft_q2_newton (n + d)))).
    + apply Qplus_0_r.
    + apply (Qplus_le_compat (sft_q2_newton n - sft_q2_newton (n + d))
                             (sft_q2_newton n - sft_q2_newton (n + d))
                             0
                             (2 * sft_q2_slack (sft_q2_newton (n + d)))).
      * apply Qle_refl.
      * exact (sft_q2_two_slack_nonneg (n + d) Hnd).
  - exact (J d).
Qed.

(* 逐 eps 界（p ≤ q 有序对）：|z_p − z_q| ≤ eps/2——
   取档（sft_arch_le 显式见证）＋尾和＋几何级数和（显式 N 链）。 *)
Lemma sft_q2_cauchy_bound : forall p q : nat, (1 <= p)%nat -> (p <= q)%nat -> forall eps : Q,
  Qlt 0 eps -> Qle (/ (3 * eps)) (sft_p2 (Nat.pred p)) ->
  Qle (Qabs (sft_q2_newton p - sft_q2_newton q)) ((1#2)%Q * eps).
Proof.
  intros p q Hp1 Hpq eps Heps Harchp.
  assert (H3e : Qlt 0 (3 * eps)).
  { pose proof (Qmult_lt_compat_r 0 3 eps Heps sft_q_0_lt_3) as Hm.
    rewrite Qmult_0_l in Hm. exact Hm. }
  assert (H3e0 : ~ (3 * eps == 0)) by (apply sft_q_neq0_of_lt; exact H3e).
  assert (Hmono : Qle (sft_q2_newton q) (sft_q2_newton p)).
  { replace q with (p + (q - p))%nat by lia.
    apply (sft_q2_mono (q - p) p Hp1). }
  assert (Hnn : Qle 0 (sft_q2_newton p - sft_q2_newton q)).
  { apply (qle_pos_minus (sft_q2_newton q) (sft_q2_newton p)). exact Hmono. }
  pose proof (sft_q2_tail_sum (q - p) p Hp1) as Hts.
  assert (Hqeq : (p + (q - p) = q)%nat) by lia.
  rewrite Hqeq in Hts.
  pose proof (sft_q2_tail_decay p Hp1) as Hdec.
  pose proof (sft_q2_two_slack_nonneg p Hp1) as HB0.
  assert (HBP : Qle ((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p)))
                    (sft_p2 (Nat.pred p) * (2 * sft_q2_slack (sft_q2_newton p)))).
  { exact (Qmult_le_compat_r (/ (3 * eps)) (sft_p2 (Nat.pred p))
             (2 * sft_q2_slack (sft_q2_newton p)) Harchp HB0). }
  assert (HBP2 : Qle ((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p)))
                     ((2 * sft_q2_slack (sft_q2_newton p)) * sft_p2 (Nat.pred p))).
  { apply (qle_congr_r ((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p)))
                       (sft_p2 (Nat.pred p) * (2 * sft_q2_slack (sft_q2_newton p)))
                       ((2 * sft_q2_slack (sft_q2_newton p)) * sft_p2 (Nat.pred p))).
    - ring.
    - exact HBP. }
  assert (HBC : Qle ((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p))) (1#6)%Q).
  { exact (Qle_trans _ _ _ HBP2 Hdec). }
  assert (Hmul : Qle (((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p))) * (3 * eps))
                     ((1#6)%Q * (3 * eps))).
  { exact (Qmult_le_compat_r _ (1#6)%Q (3 * eps) HBC (Qlt_le_weak 0 (3 * eps) H3e)). }
  assert (HLHS : Qeq (((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p))) * (3 * eps))
                      (2 * sft_q2_slack (sft_q2_newton p))).
  { transitivity ((2 * sft_q2_slack (sft_q2_newton p))
                  * ((/ (3 * eps)) * (3 * eps))).
    - ring.
    - rewrite (Qmult_comm (/ (3 * eps)) (3 * eps)).
      rewrite (Qmult_inv_r (3 * eps) H3e0).
      ring. }
  assert (HRHS : Qeq ((1#6)%Q * (3 * eps)) ((1#2)%Q * eps)) by ring.
  assert (Hfin : Qle (2 * sft_q2_slack (sft_q2_newton p)) ((1#2)%Q * eps)).
  { apply (qle_congr_l (((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p))) * (3 * eps))
                       (2 * sft_q2_slack (sft_q2_newton p))
                       ((1#2)%Q * eps)).
    - exact HLHS.
    - apply (qle_congr_r (((/ (3 * eps)) * (2 * sft_q2_slack (sft_q2_newton p))) * (3 * eps))
                          ((1#6)%Q * (3 * eps))
                          ((1#2)%Q * eps)).
      + exact HRHS.
      + exact Hmul. }
  rewrite (sft_qabs_nonneg_self _ Hnn).
  apply (Qle_trans (sft_q2_newton p - sft_q2_newton q)
                   (2 * sft_q2_slack (sft_q2_newton p))
                   ((1#2)%Q * eps)).
  - exact Hts.
  - exact Hfin.
Qed.

(* 方形非负位定格：接口层 nsq_square_nonneg 假设位（UpReqSqrtF.v:693，
   le zero (mult t t)）保持显式假设位原样——本件不闭合该位；其可行残形即
   Q 层同位件 sft_q_square_nonneg（S02 Qsquare_nonneg 定名转发，
   §4 压缩链的 s² ≥ 0 与 (y-1)² ≥ 0 均由它供给）。 *)

(* 主件：Q 层 sqrt2 Newton 逐 eps Cauchy（对应 UpReqSqrtF §2 被注释的
   sqrtf_newton_cauchy 目标语形；Qabs(·−·) 作 metric 同位；严格 lt 出口
   QltT'；显式 N 见证 = S(sft_arch_witness (1/(3·eps)))）。 *)
Lemma sft_q2_newton_cauchy : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    QltT' (sft_q2_metric (sft_q2_newton m) (sft_q2_newton n)) eps).
Proof.
  intros eps Heps.
  assert (H3e : Qlt 0 (3 * eps)).
  { pose proof (Qmult_lt_compat_r 0 3 eps Heps sft_q_0_lt_3) as Hm.
    rewrite Qmult_0_l in Hm. exact Hm. }
  assert (Hc'0 : Qlt 0 (/ (3 * eps))) by (apply sft_q_inv_pos0; exact H3e).
  pose proof (sft_arch_le (/ (3 * eps)) Hc'0) as Harch.
  apply (existT _ (Datatypes.S (sft_arch_witness (/ (3 * eps))))).
  intros m n Hm Hn.
  assert (Harchm : Qle (/ (3 * eps)) (sft_p2 (Nat.pred m))).
  { apply (Qle_trans (/ (3 * eps)) (sft_p2 (sft_arch_witness (/ (3 * eps))))
                     (sft_p2 (Nat.pred m))).
    - exact Harch.
    - apply sft_p2_mono. lia. }
  assert (Harchn : Qle (/ (3 * eps)) (sft_p2 (Nat.pred n))).
  { apply (Qle_trans (/ (3 * eps)) (sft_p2 (sft_arch_witness (/ (3 * eps))))
                     (sft_p2 (Nat.pred n))).
    - exact Harch.
    - apply sft_p2_mono. lia. }
  assert (Hlt : Qlt ((1#2)%Q * eps) eps).
  { destruct (Qlt_le_dec ((1#2)%Q * eps) eps) as [Hx | Hbad].
    - exact Hx.
    - exfalso.
      pose proof (Qmult_le_compat_r eps ((1#2)%Q * eps) 2 Hbad
                    (Qlt_le_weak 0 2 sft_q_0_lt_2)) as Hm1.
      assert (Heq2 : Qeq ((1#2)%Q * eps * 2) eps) by ring.
      pose proof (qle_congr_r (eps * 2) ((1#2)%Q * eps * 2) eps Heq2 Hm1) as Hm2.
      assert (Hm3 : Qle (2 * eps) (1 * eps)).
      { apply (qle_congr_l (eps * 2) (2 * eps) (1 * eps)).
        - ring.
        - apply (qle_congr_r (eps * 2) eps (1 * eps)).
          + exact (Qeq_sym (1 * eps) eps (Qmult_1_l eps)).
          + exact Hm2. }
      assert (H21 : Qle 2 1) by (apply (sft_q_le_cancel_pos 2 1 eps Heps); exact Hm3).
      unfold Qle in H21. cbn [Qnum Qden] in H21. lia. }
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (Hn1 : (1 <= n)%nat) by lia.
  destruct (le_lt_dec m n) as [Hmn | Hnm].
  - apply (Qlt_to_QltT' _ _).
    apply (Qle_lt_trans (Qabs (sft_q2_newton m - sft_q2_newton n)) ((1#2)%Q * eps) eps).
    + exact (sft_q2_cauchy_bound m n Hm1 Hmn eps Heps Harchm).
    + exact Hlt.
  - assert (Hswap : Qeq (Qabs (sft_q2_newton m - sft_q2_newton n))
                        (Qabs (sft_q2_newton n - sft_q2_newton m))).
    { transitivity (Qabs (- (sft_q2_newton n - sft_q2_newton m))).
      - apply (sft_qabs_eq (sft_q2_newton m - sft_q2_newton n)
                           (- (sft_q2_newton n - sft_q2_newton m))). ring.
      - apply Qabs_opp. }
    apply (Qlt_to_QltT' _ _).
    apply (Qle_lt_trans (Qabs (sft_q2_newton m - sft_q2_newton n)) ((1#2)%Q * eps) eps).
    + apply (qle_congr_l (Qabs (sft_q2_newton n - sft_q2_newton m))
                         (Qabs (sft_q2_newton m - sft_q2_newton n))
                         ((1#2)%Q * eps)).
      * exact (Qeq_sym (Qabs (sft_q2_newton m - sft_q2_newton n))
                       (Qabs (sft_q2_newton n - sft_q2_newton m)) Hswap).
      * exact (sft_q2_cauchy_bound n m Hn1 (Nat.lt_le_incl n m Hnm) eps Heps Harchn).
    + exact Hlt.
Qed.

(* ################ 取证（在册件同口径） ################ *)
Print Assumptions sft_q2_newton_cauchy.
Print Assumptions sft_q2_fetch.
Print Assumptions sft_q_square_nonneg.
Print Assumptions sft_arch_hits.
