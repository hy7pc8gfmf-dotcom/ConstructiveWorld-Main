(* ============================================================ *)
(* UpAblMetaEngine.v                                            *)
(*                                                              *)
(* 目的：M1 席（亚稳标度·发散/低界引擎席）引擎件两件：           *)
(*   件① mte_inv_divergence：1/T 发散见证——任意正 delta、任意    *)
(*        nat 界 M，可取正 T0 = delta·inv(M+1)，一切 0<T<T0      *)
(*        满足 M·T < delta。                                     *)
(*   件② mte_exp_pow_iter（exp 的 nat 倍迭代：                  *)
(*        exp(x·n) == (exp x)^n）与 mte_exp_divergence（正向发散  *)
(*        低界：x>0 时幂列 (e^x)^n 最终超过任意 nat 界）。        *)
(* 依赖：S01/S02/S03 具体柯西实数层；S07 顶层序引理、阿基米德件、 *)
(*       exp 种子（gt_one / minus_one_pos / 加法性 / 换形）。      *)
(* 语句纪律：全 Set 层（存在性 sigT、合取 S01.And:=A*B），前件    *)
(*       显式（delta/x 正性证书），无 Prop 泄露。                 *)
(* 注记：本件为中文头注之零承认件（无公理面），独立新件，mte_ 前缀。 *)
(*       具体柯西实数层内 S02/S03 无 nat 嵌入实名，故本件自备     *)
(*       mte_nat_to_R（形状同 S04 接口层同名件：零 ↦ 零、         *)
(*       后继 ↦ 壹 + 递降），并在交付报告中如实申报。             *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ---------- 局部载体 ---------- *)

Fixpoint mte_nat_to_R (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S m => real_plus real_one (mte_nat_to_R m)
  end.

Fixpoint mte_rpow (b : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult b (mte_rpow b m)
  end.

(* ---------- 逐点 Q 级加法平移（eps 见证直构） ---------- *)

(* a < b ⟹ a+c < b+c *)
Lemma mte_lt_plus_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    assert (Hpt : projT1 (real_plus b c) n - projT1 (real_plus a c) n
                  == projT1 b n - projT1 a n).
    { assert (Ha : projT1 (real_plus a c) n == projT1 a n + projT1 c n)
        by (apply real_plus_proj).
      assert (Hb : projT1 (real_plus b c) n == projT1 b n + projT1 c n)
        by (apply real_plus_proj).
      rewrite Hb, Ha. field.
    }
    assert (Hcmp : Qcompare eps (projT1 (real_plus b c) n - projT1 (real_plus a c) n)
                 = Qcompare eps (projT1 b n - projT1 a n)).
    { apply (Qcompare_comp eps eps (Qeq_refl eps)). exact Hpt. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact (HN n Hn).
Qed.

(* 任意 z：z < 壹 + z *)
Lemma mte_lt_plus_one : forall z : Real,
  real_lt z (real_plus real_one z).
Proof.
  intro z.
  destruct real_lt_zero_one as [eps [Heps [N HN]]].
  unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    assert (Hpt : projT1 (real_plus real_one z) n - projT1 z n
                  == projT1 real_one n - projT1 real_zero n).
    { assert (Hp : projT1 (real_plus real_one z) n == projT1 real_one n + projT1 z n)
        by (apply real_plus_proj).
      assert (H1v : projT1 real_one n == 1%Q) by reflexivity.
      assert (H0v : projT1 real_zero n == 0%Q) by reflexivity.
      rewrite Hp, H1v, H0v. field.
    }
    assert (Hcmp : Qcompare eps (projT1 (real_plus real_one z) n - projT1 z n)
                 = Qcompare eps (projT1 real_one n - projT1 real_zero n)).
    { apply (Qcompare_comp eps eps (Qeq_refl eps)). exact Hpt. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact (HN n Hn).
Qed.

(* ---------- 序运输 ---------- *)

(* 相等换左端 *)
Lemma mte_le_congr : forall a b c : Real,
  real_eq a b -> real_le a c -> real_le b c.
Proof.
  intros a b c Heq Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqc].
  - left. exact (real_eq_lt_lt b a c (real_eq_sym a b Heq) Hlt).
  - right. exact (real_eq_trans b a c (real_eq_sym a b Heq) Heqc).
Qed.

(* 相等换左端（反方向）：a == b ⟹ b ≤ c ⟹ a ≤ c *)
Lemma mte_le_congr_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Heq Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqc].
  - left. exact (real_eq_lt_lt a b c Heq Hlt).
  - right. exact (real_eq_trans a b c Heq Heqc).
Qed.

(* 相等换右端 *)
Lemma mte_le_congr_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hle Heq.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heqb].
  - left. exact (real_lt_eq_lt a b c Hlt Heq).
  - right. exact (real_eq_trans a b c Heqb Heq).
Qed.

(* 严格+弱 传递拼接 *)
Lemma mte_lt_le_trans : forall a b c : Real,
  real_lt a b -> real_le b c -> real_lt a c.
Proof.
  intros a b c Hlt Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt2 | Heq2].
  - exact (real_lt_trans a b c Hlt Hlt2).
  - exact (real_lt_eq_lt a b c Hlt Heq2).
Qed.

(* 严格左加法：u < v ⟹ w+u < w+v *)
Lemma mte_lt_plus_l : forall u v w : Real,
  real_lt u v -> real_lt (real_plus w u) (real_plus w v).
Proof.
  intros u v w Huv.
  apply (real_eq_lt_lt (real_plus w u) (real_plus u w) (real_plus w v)).
  - exact (real_plus_comm w u).
  - exact (real_lt_eq_lt (real_plus u w) (real_plus v w) (real_plus w v)
             (mte_lt_plus_r u v w Huv) (real_plus_comm v w)).
Qed.

(* ≤ 加法双兼容 *)
Lemma mte_le_plus_compat : forall a b c d : Real,
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hle1 Hle2.
  unfold real_le in Hle1, Hle2.
  destruct Hle1 as [Hlt1 | Heq1]; destruct Hle2 as [Hlt2 | Heq2].
  - left. exact (real_lt_plus_compat a b c d Hlt1 Hlt2).
  - left. exact (real_lt_eq_lt (real_plus a c) (real_plus b c) (real_plus b d)
                   (mte_lt_plus_r a b c Hlt1)
                   (RealSetoid.real_eq_plus_compat b c b d (real_eq_refl b) Heq2)).
  - left. exact (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
                   (RealSetoid.real_eq_plus_compat a c b c Heq1 (real_eq_refl c))
                   (mte_lt_plus_l c d b Hlt2)).
  - right. exact (RealSetoid.real_eq_plus_compat a c b d Heq1 Heq2).
Qed.

(* ≤ 乘法右兼容 *)
Lemma mte_le_mult_compat_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hle Hc.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - left. exact (real_mult_lt_compat a b c Hlt Hc).
  - right. exact (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c)).
Qed.

(* ---------- nat 嵌入的正性 ---------- *)

(* n·z ≥ 零（z > 零 严格前件） *)
Lemma mte_nat_mult_pos : forall (n : nat) (z : Real),
  real_lt real_zero z -> real_le real_zero (real_mult (mte_nat_to_R n) z).
Proof.
  intros n z Hz.
  induction n as [| n IH].
  - right.
    exact (real_eq_sym _ _
             (real_eq_trans (real_mult (mte_nat_to_R 0) z)
                            (real_mult z (mte_nat_to_R 0)) real_zero
                 (real_mult_comm (mte_nat_to_R 0) z) (real_mult_zero z))).
  - assert (E : real_eq (real_mult (mte_nat_to_R (Datatypes.S n)) z)
                        (real_plus (real_mult (mte_nat_to_R n) z) z)).
    { apply (real_eq_trans _ (real_mult z (real_plus real_one (mte_nat_to_R n)))).
      - exact (real_mult_comm (real_plus real_one (mte_nat_to_R n)) z).
      - apply (real_eq_trans _
                 (real_plus (real_mult z real_one) (real_mult z (mte_nat_to_R n)))).
        + exact (real_distrib z real_one (mte_nat_to_R n)).
        + apply (real_eq_trans _ (real_plus z (real_mult z (mte_nat_to_R n)))).
          * exact (RealSetoid.real_eq_plus_compat (real_mult z real_one)
                     (real_mult z (mte_nat_to_R n))
                     z (real_mult z (mte_nat_to_R n))
                     (real_mult_one z)
                     (real_eq_refl (real_mult z (mte_nat_to_R n)))).
          * exact (real_eq_trans (real_plus z (real_mult z (mte_nat_to_R n)))
                     (real_plus (real_mult z (mte_nat_to_R n)) z)
                     (real_plus (real_mult (mte_nat_to_R n) z) z)
                     (real_plus_comm z (real_mult z (mte_nat_to_R n)))
                     (RealSetoid.real_eq_plus_compat (real_mult z (mte_nat_to_R n)) z
                        (real_mult (mte_nat_to_R n) z) z
                        (real_mult_comm z (mte_nat_to_R n)) (real_eq_refl z))).
    }
    unfold real_le in IH.
    destruct IH as [HltI | HeqI].
    + left.
      apply (real_lt_eq_lt real_zero (real_plus z (real_mult (mte_nat_to_R n) z))
               (real_mult (mte_nat_to_R (Datatypes.S n)) z)).
      * exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus z (real_mult (mte_nat_to_R n) z))
                 (real_eq_sym (real_plus real_zero real_zero) real_zero
                    (real_plus_zero real_zero))
                 (real_lt_plus_compat real_zero z real_zero
                    (real_mult (mte_nat_to_R n) z) Hz HltI)).
      * exact (real_eq_trans (real_plus z (real_mult (mte_nat_to_R n) z))
                 (real_plus (real_mult (mte_nat_to_R n) z) z)
                 (real_mult (mte_nat_to_R (Datatypes.S n)) z)
                 (real_plus_comm z (real_mult (mte_nat_to_R n) z))
                 (real_eq_sym _ _ E)).
    + left.
      apply (real_lt_eq_lt real_zero z (real_mult (mte_nat_to_R (Datatypes.S n)) z) Hz).
      * apply (real_eq_trans z (real_plus z real_zero)).
        -- exact (real_eq_sym (real_plus z real_zero) z (real_plus_zero z)).
        -- apply (real_eq_trans _ (real_plus z (real_mult (mte_nat_to_R n) z))).
           ++ exact (RealSetoid.real_eq_plus_compat z real_zero z
                        (real_mult (mte_nat_to_R n) z)
                        (real_eq_refl z) HeqI).
           ++ apply (real_eq_trans _
                        (real_plus (real_mult (mte_nat_to_R n) z) z)).
              ** exact (real_plus_comm z (real_mult (mte_nat_to_R n) z)).
              ** exact (real_eq_sym _ _ E).
Qed.

(* 后继嵌入严格正 *)
Lemma mte_nat_to_R_S_pos : forall n : nat,
  real_lt real_zero (mte_nat_to_R (Datatypes.S n)).
Proof.
  intro n.
  destruct (mte_nat_mult_pos n real_one real_lt_zero_one) as [HltH | HeqH].
  - assert (Hn : real_lt real_zero (mte_nat_to_R n))
      by (exact (real_lt_eq_lt real_zero (real_mult (mte_nat_to_R n) real_one)
                   (mte_nat_to_R n) HltH (real_mult_one (mte_nat_to_R n)))).
    exact (real_plus_positive real_one (mte_nat_to_R n) real_lt_zero_one Hn).
  - apply (real_lt_eq_lt real_zero real_one).
    + exact real_lt_zero_one.
    + apply (real_eq_trans _ (real_plus real_one real_zero)).
      * exact (real_eq_sym (real_plus real_one real_zero) real_one (real_plus_zero real_one)).
      * exact (RealSetoid.real_eq_plus_compat real_one real_zero real_one
                 (mte_nat_to_R n)
                 (real_eq_refl real_one)
                 (real_eq_sym (mte_nat_to_R n) real_zero
                    (real_eq_trans (mte_nat_to_R n)
                       (real_mult (mte_nat_to_R n) real_one) real_zero
                       (real_eq_sym _ _ (real_mult_one (mte_nat_to_R n)))
                       (real_eq_sym _ _ HeqH)))).
Qed.

(* ---------- 常量桥（real_const ↔ mte_nat_to_R） ---------- *)

(* Q 相等换实常量相等 *)
Lemma mte_const_ext : forall c d : Q, c == d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd. apply real_eq_of_zero_diff. intro k.
  assert (H1 : projT1 (real_const c) k == c) by (unfold real_const; reflexivity).
  assert (H2 : projT1 (real_const d) k == d) by (unfold real_const; reflexivity).
  rewrite H1, H2.
  destruct c as [a ca]; destruct d as [b cb].
  unfold Qeq in Hcd. simpl in Hcd.
  unfold Qminus, Qeq. simpl.
  rewrite Hcd. ring.
Qed.

(* 实常量加法同态 *)
Lemma mte_const_plus : forall c d : Q,
  real_eq (real_plus (real_const c) (real_const d)) (real_const (c + d)%Q).
Proof.
  intros c d. apply real_eq_of_zero_diff. intro k.
  assert (H1 : projT1 (real_plus (real_const c) (real_const d)) k
               == projT1 (real_const c) k + projT1 (real_const d) k)
    by (apply real_plus_proj).
  rewrite H1.
  assert (H2 : projT1 (real_const c) k == c) by (unfold real_const; reflexivity).
  assert (H3 : projT1 (real_const d) k == d) by (unfold real_const; reflexivity).
  assert (H4 : projT1 (real_const (c + d)%Q) k == (c + d)%Q)
    by (unfold real_const; reflexivity).
  rewrite H2, H3, H4. field.
Qed.

(* nat 嵌入 == 常量嵌入（real_arch 消费之桥） *)
Lemma mte_nat_const_eq : forall n : nat,
  real_eq (mte_nat_to_R n) (real_const (Z.of_nat n # 1)%Q).
Proof.
  intro n. induction n as [| n IH].
  - apply real_eq_of_zero_diff. intro k.
    assert (H1 : projT1 (mte_nat_to_R 0) k == 0%Q) by reflexivity.
    assert (H2 : projT1 (real_const (Z.of_nat 0 # 1)%Q) k == (Z.of_nat 0 # 1)%Q)
      by (unfold real_const; reflexivity).
    rewrite H1, H2.
    assert (Hz : Z.of_nat 0 = 0%Z) by reflexivity.
    rewrite Hz. field.
  - assert (Hzs : Z.of_nat (Datatypes.S n) = Z.succ (Z.of_nat n)) by lia.
    assert (Hzq : (Z.of_nat (Datatypes.S n) # 1)%Q == (1 + (Z.of_nat n # 1))%Q).
    { unfold Qeq. rewrite Hzs. cbn [Qnum Qden Qplus]. lia. }
    apply (real_eq_trans _ (real_plus real_one (real_const (Z.of_nat n # 1)%Q))).
    + exact (RealSetoid.real_eq_plus_compat real_one (mte_nat_to_R n) real_one
               (real_const (Z.of_nat n # 1)%Q)
               (real_eq_refl real_one) IH).
    + apply (real_eq_trans _ (real_const (1 + (Z.of_nat n # 1))%Q)).
      * apply (real_eq_trans _
                 (real_plus (real_const (1#1)%Q) (real_const (Z.of_nat n # 1)%Q))).
        -- apply (RealSetoid.real_eq_plus_compat real_one
                       (real_const (Z.of_nat n # 1)%Q)
                       (real_const (1#1)%Q) (real_const (Z.of_nat n # 1)%Q)).
           ++ apply real_eq_of_zero_diff. intro k.
              assert (Ha : projT1 (real_const (1#1)%Q) k == (1#1)%Q)
                by (unfold real_const; reflexivity).
              assert (Hb1 : projT1 real_one k == 1%Q) by reflexivity.
              rewrite Ha, Hb1. field.
           ++ exact (real_eq_refl (real_const (Z.of_nat n # 1)%Q)).
        -- exact (mte_const_plus (1#1)%Q (Z.of_nat n # 1)%Q).
      * apply (mte_const_ext (1 + (Z.of_nat n # 1))%Q
                 (Z.of_nat (Datatypes.S n) # 1)%Q).
        exact (Qeq_sym _ _ Hzq).
Qed.

(* ---------- 幂的基本性 ---------- *)

Lemma mte_rpow_pos : forall (b : Real) (n : nat),
  real_lt real_zero b -> real_lt real_zero (mte_rpow b n).
Proof.
  intros b n Hb. induction n as [| n IH].
  - exact real_lt_zero_one.
  - exact (real_mult_pos_compat b (mte_rpow b n) Hb IH).
Qed.

(* 底 > 壹 ⟹ 幂逐步严格增 *)
Lemma mte_rpow_step_lt : forall (b : Real) (n : nat),
  real_lt real_one b -> real_lt (mte_rpow b n) (mte_rpow b (Datatypes.S n)).
Proof.
  intros b n Hb.
  assert (Hbp : real_lt real_zero b)
    by (exact (real_lt_trans real_zero real_one b real_lt_zero_one Hb)).
  assert (Hstep : real_lt (real_mult (mte_rpow b n) real_one)
                          (real_mult (mte_rpow b n) b)).
  { exact (real_mult_lt_compat_l real_one b (mte_rpow b n) Hb
             (mte_rpow_pos b n Hbp)). }
  apply (real_lt_eq_lt _ (real_mult (mte_rpow b n) b)).
  - exact (real_eq_lt_lt (mte_rpow b n) (real_mult (mte_rpow b n) real_one)
             (real_mult (mte_rpow b n) b)
             (real_eq_sym (real_mult (mte_rpow b n) real_one) (mte_rpow b n)
                (real_mult_one (mte_rpow b n))) Hstep).
  - exact (real_mult_comm (mte_rpow b n) b).
Qed.

(* 底 > 壹 ⟹ m 处幂 < m+S d 处幂 *)
Lemma mte_rpow_mono_add : forall (b : Real) (m d : nat),
  real_lt real_one b -> real_lt (mte_rpow b m) (mte_rpow b (m + Datatypes.S d)).
Proof.
  intros b m d Hb.
  induction d as [| d IH].
  - rewrite (Nat.add_succ_r m 0%nat). rewrite (Nat.add_0_r m).
    exact (mte_rpow_step_lt b m Hb).
  - rewrite (Nat.add_succ_r m (Datatypes.S d)).
    exact (real_lt_trans (mte_rpow b m) (mte_rpow b (m + Datatypes.S d))
             (mte_rpow b (Datatypes.S (m + Datatypes.S d))) IH
             (mte_rpow_step_lt b (m + Datatypes.S d) Hb)).
Qed.

(* 底相等换幂相等 *)
Lemma mte_rpow_ext : forall (a b : Real) (n : nat),
  real_eq a b -> real_eq (mte_rpow a n) (mte_rpow b n).
Proof.
  intros a b n Heq. induction n as [| n IH].
  - exact (real_eq_refl real_one).
  - exact (RealSetoid.real_eq_mult_compat a (mte_rpow a n) b (mte_rpow b n) Heq IH).
Qed.

(* ---------- 伯努利型下界：(壹+h)^n ≥ 壹 + n·h ---------- *)

Lemma mte_pow_ge : forall (h : Real) (n : nat),
  real_lt real_zero h ->
  real_le (real_plus real_one (real_mult (mte_nat_to_R n) h))
          (mte_rpow (real_plus real_one h) n).
Proof.
  intros h n Hh. induction n as [| n IH].
  - right.
    apply (real_eq_trans _ (real_plus real_one real_zero)).
    + exact (RealSetoid.real_eq_plus_compat real_one
               (real_mult (mte_nat_to_R 0) h) real_one real_zero
               (real_eq_refl real_one)
               (real_eq_trans (real_mult (mte_nat_to_R 0) h)
                  (real_mult h (mte_nat_to_R 0)) real_zero
                  (real_mult_comm (mte_nat_to_R 0) h) (real_mult_zero h))).
    + exact (real_plus_zero real_one).
  - (* 归纳步：(壹+n̄h)(壹+h) = 壹+n̄h+h+n̄(hh) ≥ 壹+n̄h+h = 壹+(S n)·h *)
    assert (H1h : real_lt real_zero (real_plus real_one h))
      by (exact (real_plus_positive real_one h real_lt_zero_one Hh)).
    assert (Hsq : real_le real_zero (real_mult (mte_nat_to_R n) (real_mult h h)))
      by (exact (mte_nat_mult_pos n (real_mult h h) (real_mult_pos_compat h h Hh Hh))).
    assert (Eshift : real_eq (real_mult (mte_nat_to_R (Datatypes.S n)) h)
                             (real_plus (real_mult (mte_nat_to_R n) h) h)).
    { apply (real_eq_trans _ (real_mult h (real_plus real_one (mte_nat_to_R n)))).
      - exact (real_mult_comm (real_plus real_one (mte_nat_to_R n)) h).
      - apply (real_eq_trans _
                 (real_plus (real_mult h real_one) (real_mult h (mte_nat_to_R n)))).
        + exact (real_distrib h real_one (mte_nat_to_R n)).
        + apply (real_eq_trans _ (real_plus h (real_mult h (mte_nat_to_R n)))).
          * exact (RealSetoid.real_eq_plus_compat (real_mult h real_one)
                     (real_mult h (mte_nat_to_R n))
                     h (real_mult h (mte_nat_to_R n))
                     (real_mult_one h)
                     (real_eq_refl (real_mult h (mte_nat_to_R n)))).
          * exact (real_eq_trans (real_plus h (real_mult h (mte_nat_to_R n)))
                     (real_plus h (real_mult (mte_nat_to_R n) h))
                     (real_plus (real_mult (mte_nat_to_R n) h) h)
                     (RealSetoid.real_eq_plus_compat h (real_mult h (mte_nat_to_R n))
                        h (real_mult (mte_nat_to_R n) h)
                        (real_eq_refl h) (real_mult_comm h (mte_nat_to_R n)))
                     (real_plus_comm h (real_mult (mte_nat_to_R n) h))).
    }
    (* 展开恒等：L == (壹+n̄h) + (h + n̄·(h·h))，其中 L = (壹+n̄h)·(壹+h) *)
    assert (HAh : real_eq (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                          (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
    { apply (real_eq_trans _ (real_mult h (real_plus real_one (real_mult (mte_nat_to_R n) h)))).
      - exact (real_mult_comm (real_plus real_one (real_mult (mte_nat_to_R n) h)) h).
      - apply (real_eq_trans _
                 (real_plus (real_mult h real_one)
                            (real_mult h (real_mult (mte_nat_to_R n) h)))).
        + exact (real_distrib h real_one (real_mult (mte_nat_to_R n) h)).
        + exact (RealSetoid.real_eq_plus_compat (real_mult h real_one)
                   (real_mult h (real_mult (mte_nat_to_R n) h))
                   h (real_mult (mte_nat_to_R n) (real_mult h h))
                   (real_mult_one h)
                   (real_eq_trans (real_mult h (real_mult (mte_nat_to_R n) h))
                      (real_mult (real_mult (mte_nat_to_R n) h) h)
                      (real_mult (mte_nat_to_R n) (real_mult h h))
                      (real_mult_comm h (real_mult (mte_nat_to_R n) h))
                      (real_eq_sym _ _ (real_mult_assoc (mte_nat_to_R n) h h)))).
    }
    assert (EL : real_eq (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                    (real_plus real_one h))
                         (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                    (real_plus h
                                       (real_mult (mte_nat_to_R n) (real_mult h h))))).
    { apply (real_eq_trans _
               (real_plus (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) real_one)
                          (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h))).
      - exact (real_distrib (real_plus real_one (real_mult (mte_nat_to_R n) h))
                 real_one h).
      - apply (real_eq_trans _
                 (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                            (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h))))).
        + exact (RealSetoid.real_eq_plus_compat
                    (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) real_one)
                    (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                    (real_plus real_one (real_mult (mte_nat_to_R n) h))
                    (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))
                    (real_mult_one (real_plus real_one (real_mult (mte_nat_to_R n) h)))
                    HAh).
        + exact (real_eq_refl
                    (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                               (real_plus h
                                          (real_mult (mte_nat_to_R n) (real_mult h h))))).
    }
    (* 目标换形：壹+(S n)·h == (壹+n̄h)+h *)
    assert (E5 : real_eq (real_plus real_one
                            (real_mult (mte_nat_to_R (Datatypes.S n)) h))
                         (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)).
    { apply (real_eq_trans _
               (real_plus real_one
                  (real_plus (real_mult (mte_nat_to_R n) h) h))).
      - exact (RealSetoid.real_eq_plus_compat real_one
                  (real_mult (mte_nat_to_R (Datatypes.S n)) h)
                  real_one (real_plus (real_mult (mte_nat_to_R n) h) h)
                  (real_eq_refl real_one) Eshift).
      - apply (real_eq_trans _
                 (real_plus real_one
                    (real_plus h (real_mult (mte_nat_to_R n) h)))).
        + apply (RealSetoid.real_eq_plus_compat real_one
                    (real_plus (real_mult (mte_nat_to_R n) h) h)
                    real_one (real_plus h (real_mult (mte_nat_to_R n) h))
                    (real_eq_refl real_one)
                    (real_plus_comm (real_mult (mte_nat_to_R n) h) h)).
        + apply (real_eq_trans _
                     (real_plus (real_plus real_one h)
                                (real_mult (mte_nat_to_R n) h))).
          * exact (real_plus_assoc real_one h (real_mult (mte_nat_to_R n) h)).
          * apply (real_eq_trans _
                       (real_plus (real_mult (mte_nat_to_R n) h)
                                  (real_plus real_one h))).
            -- exact (real_plus_comm (real_plus real_one h)
                        (real_mult (mte_nat_to_R n) h)).
            -- apply (real_eq_trans _
                         (real_plus (real_plus (real_mult (mte_nat_to_R n) h) real_one) h)).
               ++ exact (real_plus_assoc (real_mult (mte_nat_to_R n) h) real_one h).
               ++ exact (RealSetoid.real_eq_plus_compat
                            (real_plus (real_mult (mte_nat_to_R n) h) real_one)
                            h
                            (real_plus real_one (real_mult (mte_nat_to_R n) h))
                            h
                            (real_plus_comm (real_mult (mte_nat_to_R n) h) real_one)
                            (real_eq_refl h)).
    }
    assert (Hle_h : real_le h
                      (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
    { apply (mte_le_congr (real_plus h real_zero) h).
      - exact (real_plus_zero h).
      - assert (Hhh : real_le h h).
        { right. exact (real_eq_refl h). }
        exact (mte_le_plus_compat h h real_zero
                 (real_mult (mte_nat_to_R n) (real_mult h h)) Hhh Hsq).
    }
    assert (Hle3 : real_le (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                           (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus h
                                         (real_mult (mte_nat_to_R n) (real_mult h h))))).
    { apply (mte_le_plus_compat
               (real_plus real_one (real_mult (mte_nat_to_R n) h))
               (real_plus real_one (real_mult (mte_nat_to_R n) h))
               h (real_plus h (real_mult (mte_nat_to_R n) (real_mult h h)))).
      - right. exact (real_eq_refl (real_plus real_one (real_mult (mte_nat_to_R n) h))).
      - exact Hle_h.
    }
    assert (Hle4 : real_le (real_plus (real_plus real_one (real_mult (mte_nat_to_R n) h)) h)
                           (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus real_one h))).
    { apply (mte_le_congr_r _ _ _ Hle3 (real_eq_sym _ _ EL)). }
    assert (Hle5 : real_le (real_plus real_one
                              (real_mult (mte_nat_to_R (Datatypes.S n)) h))
                           (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                      (real_plus real_one h))).
    { apply (mte_le_congr_l _ _ _ E5 Hle4). }
    exact (real_le_trans
             (real_plus real_one (real_mult (mte_nat_to_R (Datatypes.S n)) h))
             (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                        (real_plus real_one h))
             (mte_rpow (real_plus real_one h) (Datatypes.S n))
             Hle5
             (mte_le_congr_r (real_mult (real_plus real_one (real_mult (mte_nat_to_R n) h))
                                (real_plus real_one h))
                (real_mult (mte_rpow (real_plus real_one h) n) (real_plus real_one h))
                (mte_rpow (real_plus real_one h) (Datatypes.S n))
                (mte_le_mult_compat_r (real_plus real_one (real_mult (mte_nat_to_R n) h))
                   (mte_rpow (real_plus real_one h) n)
                   (real_plus real_one h) IH H1h)
                (real_mult_comm (mte_rpow (real_plus real_one h) n)
                   (real_plus real_one h)))).

Qed.

(* ---------- 件②a：exp 的 nat 倍迭代 ---------- *)

Theorem mte_exp_pow_iter : forall (x : Real) (n : nat),
  real_eq (cauchy_real_exp (real_mult x (mte_nat_to_R n)))
          (mte_rpow (cauchy_real_exp x) n).
Proof.
  intros x n. induction n as [| n IH].
  - apply (real_eq_trans _ real_one).
    + apply (real_eq_trans _ (cauchy_real_exp real_zero)).
      * exact (cauchy_real_exp_wd _ _ (real_mult_zero x)).
      * exact cauchy_real_exp_zero.
    + exact (real_eq_refl real_one).
  - apply (real_eq_trans _
               (cauchy_real_exp (real_plus (real_mult x real_one)
                                           (real_mult x (mte_nat_to_R n))))).
    + exact (cauchy_real_exp_wd _ _ (real_distrib x real_one (mte_nat_to_R n))).
    + apply (real_eq_trans _
                 (cauchy_real_exp (real_plus x (real_mult x (mte_nat_to_R n))))).
      * apply (cauchy_real_exp_wd _ _).
        exact (RealSetoid.real_eq_plus_compat (real_mult x real_one)
                   (real_mult x (mte_nat_to_R n))
                   x (real_mult x (mte_nat_to_R n))
                   (real_mult_one x) (real_eq_refl (real_mult x (mte_nat_to_R n)))).
      * apply (real_eq_trans _
                   (real_mult (cauchy_real_exp x)
                              (cauchy_real_exp (real_mult x (mte_nat_to_R n))))).
        -- exact (cauchy_real_exp_plus x (real_mult x (mte_nat_to_R n))).
        -- apply (real_eq_trans _
                       (real_mult (cauchy_real_exp x)
                                  (mte_rpow (cauchy_real_exp x) n))).
           ++ exact (RealSetoid.real_eq_mult_compat (cauchy_real_exp x)
                        (cauchy_real_exp (real_mult x (mte_nat_to_R n)))
                        (cauchy_real_exp x) (mte_rpow (cauchy_real_exp x) n)
                        (real_eq_refl (cauchy_real_exp x)) IH).
           ++ exact (real_eq_refl
                        (real_mult (cauchy_real_exp x)
                                   (mte_rpow (cauchy_real_exp x) n))).
Qed.

(* ---------- 件①：1/T 发散见证 ---------- *)

Theorem mte_inv_divergence : forall delta : Real,
  real_lt real_zero delta ->
  forall M : nat,
  sigT (fun T0 => And (real_lt real_zero T0)
         (forall T : Real, real_lt real_zero T -> real_lt T T0 ->
            real_lt (real_mult (mte_nat_to_R M) T) delta)).
Proof.
  intros delta Hdelta M.
  destruct M as [| M].
  - exists (real_mult delta (real_inv_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))).
    split.
    + exact (real_mult_pos_compat delta
                (real_inv_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))
                Hdelta (real_inv_pos_pos (mte_nat_to_R 1) (mte_nat_to_R_S_pos 0))).
    + intros T HTpos HTlt.
      apply (real_eq_lt_lt (real_mult (mte_nat_to_R 0) T) real_zero delta).
      * exact (real_eq_trans (real_mult (mte_nat_to_R 0) T)
                 (real_mult T (mte_nat_to_R 0)) real_zero
                 (real_mult_comm (mte_nat_to_R 0) T) (real_mult_zero T)).
      * exact Hdelta.
  - assert (HMpos : real_lt real_zero (mte_nat_to_R (Datatypes.S M)))
      by (exact (mte_nat_to_R_S_pos M)).
    assert (Hinvpos : real_lt real_zero
                        (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
      by (exact (real_inv_pos_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
    exists (real_mult delta (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
    split.
    + exact (real_mult_pos_compat delta
                (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                Hdelta Hinvpos).
    + intros T HTpos HTlt.
      assert (H1 : real_lt (real_mult (mte_nat_to_R (Datatypes.S M)) T)
                           (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_mult delta
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))).
      { exact (real_mult_lt_compat_l T
                  (real_mult delta (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                  (mte_nat_to_R (Datatypes.S M)) HTlt HMpos). }
      assert (E2 : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_mult delta
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))
                           (real_mult delta
                                      (real_mult (mte_nat_to_R (Datatypes.S M))
                                                 (real_inv_pos
                                                    (mte_nat_to_R (Datatypes.S M))
                                                    HMpos)))).
      { apply (real_eq_trans _
                   (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                              (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))).
        - exact (real_mult_assoc (mte_nat_to_R (Datatypes.S M)) delta
                    (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)).
        - exact (real_eq_trans
                    (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                               (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                    (real_mult (real_mult delta (mte_nat_to_R (Datatypes.S M)))
                               (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                    (real_mult delta
                               (real_mult (mte_nat_to_R (Datatypes.S M))
                                          (real_inv_pos (mte_nat_to_R (Datatypes.S M))
                                                        HMpos)))
                    (RealSetoid.real_eq_mult_compat
                       (real_mult (mte_nat_to_R (Datatypes.S M)) delta)
                       (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                       (real_mult delta (mte_nat_to_R (Datatypes.S M)))
                       (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)
                       (real_mult_comm (mte_nat_to_R (Datatypes.S M)) delta)
                       (real_eq_refl (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))
                    (real_eq_sym _ _
                       (real_mult_assoc delta (mte_nat_to_R (Datatypes.S M))
                          (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))).
      }
      assert (E3 : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                      (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                           real_one)
        by (exact (real_inv_pos_correct (mte_nat_to_R (Datatypes.S M)) HMpos)).
      assert (Edelta : real_eq (real_mult (mte_nat_to_R (Datatypes.S M))
                                          (real_mult delta
                                                     (real_inv_pos (mte_nat_to_R (Datatypes.S M))
                                                                  HMpos)))
                               delta).
      { apply (real_eq_trans _
                   (real_mult delta
                              (real_mult (mte_nat_to_R (Datatypes.S M))
                                         (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))).
        - exact E2.
        - apply (real_eq_trans _ (real_mult delta real_one)).
          + exact (RealSetoid.real_eq_mult_compat delta
                       (real_mult (mte_nat_to_R (Datatypes.S M))
                                  (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos))
                       delta real_one (real_eq_refl delta) E3).
          + exact (real_mult_one delta).
      }
      exact (real_lt_eq_lt (real_mult (mte_nat_to_R (Datatypes.S M)) T)
               (real_mult (mte_nat_to_R (Datatypes.S M))
                          (real_mult delta
                                     (real_inv_pos (mte_nat_to_R (Datatypes.S M)) HMpos)))
               delta H1 Edelta).
Qed.

(* ---------- 件②b：expf 正向发散低界 ---------- *)

Theorem mte_exp_divergence : forall x : Real,
  real_lt real_zero x ->
  forall M : nat,
  sigT (fun N => forall n : nat, Nat.le N n ->
    real_lt (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n)).
Proof.
  intros x Hx M.
  assert (Hb : real_lt real_one (cauchy_real_exp x))
    by (exact (cauchy_real_exp_gt_one x Hx)).
  set (h := real_plus (cauchy_real_exp x) (real_opp real_one)).
  assert (Hh : real_lt real_zero h)
    by (exact (cauchy_real_exp_minus_one_pos x Hx)).
  assert (Hinv : real_lt real_zero (real_inv_pos h Hh))
    by (exact (real_inv_pos_pos h Hh)).
  assert (Eexp : real_eq (cauchy_real_exp x) (real_plus real_one h)).
  { assert (Hneg : real_eq (real_plus (real_opp real_one) real_one) real_zero)
      by (exact (real_eq_trans (real_plus (real_opp real_one) real_one)
                  (real_plus real_one (real_opp real_one)) real_zero
                  (real_plus_comm (real_opp real_one) real_one)
                  (real_plus_opp real_one))).
    apply (real_eq_sym (real_plus real_one h) (cauchy_real_exp x)).
    apply (real_eq_trans _
               (real_plus (real_plus (cauchy_real_exp x) (real_opp real_one)) real_one)).
    - apply (real_eq_trans _ (real_plus h real_one)).
      + exact (real_plus_comm real_one h).
      + exact (real_eq_refl (real_plus h real_one)).
    - apply (real_eq_trans _
                 (real_plus (cauchy_real_exp x)
                            (real_plus (real_opp real_one) real_one))).
      + exact (real_eq_sym _
                   (real_plus (real_plus (cauchy_real_exp x) (real_opp real_one))
                              real_one)
                   (real_plus_assoc (cauchy_real_exp x) (real_opp real_one) real_one)).
      + apply (real_eq_trans _ (real_plus (cauchy_real_exp x) real_zero)).
        * exact (RealSetoid.real_eq_plus_compat (cauchy_real_exp x)
                     (real_plus (real_opp real_one) real_one)
                     (cauchy_real_exp x) real_zero
                     (real_eq_refl (cauchy_real_exp x)) Hneg).
        * exact (real_plus_zero (cauchy_real_exp x)).
  }
  assert (Hbp : real_lt real_zero (cauchy_real_exp x))
    by (exact (real_lt_trans real_zero real_one (cauchy_real_exp x)
                 real_lt_zero_one Hb)).
  destruct (real_arch (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)))
    as [n0 [Hn2 HBlt]].
  assert (Einv : real_eq (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
                         (mte_nat_to_R M)).
  { apply (real_eq_trans _
               (real_mult (mte_nat_to_R M) (real_mult (real_inv_pos h Hh) h))).
    - exact (real_eq_sym (real_mult (mte_nat_to_R M) (real_mult (real_inv_pos h Hh) h))
                   (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
                   (real_mult_assoc (mte_nat_to_R M) (real_inv_pos h Hh) h)).
    - apply (real_eq_trans _
                   (real_mult (mte_nat_to_R M) (real_mult h (real_inv_pos h Hh)))).
      + exact (RealSetoid.real_eq_mult_compat (mte_nat_to_R M)
                   (real_mult (real_inv_pos h Hh) h)
                   (mte_nat_to_R M) (real_mult h (real_inv_pos h Hh))
                   (real_eq_refl (mte_nat_to_R M)) (real_mult_comm (real_inv_pos h Hh) h)).
      + apply (real_eq_trans _ (real_mult (mte_nat_to_R M) real_one)).
        * exact (RealSetoid.real_eq_mult_compat (mte_nat_to_R M)
                     (real_mult h (real_inv_pos h Hh))
                     (mte_nat_to_R M) real_one
                     (real_eq_refl (mte_nat_to_R M)) (real_inv_pos_correct h Hh)).
        * exact (real_mult_one (mte_nat_to_R M)).
  }
  assert (H5 : real_lt (mte_nat_to_R M) (real_mult (mte_nat_to_R n0) h)).
  { apply (real_lt_eq_lt _ (real_mult (real_const (Z.of_nat n0 # 1)%Q) h)).
    - exact (real_eq_lt_lt (mte_nat_to_R M)
               (real_mult (real_mult (mte_nat_to_R M) (real_inv_pos h Hh)) h)
               (real_mult (real_const (Z.of_nat n0 # 1)%Q) h)
               (real_eq_sym _ _ Einv)
               (real_mult_lt_compat (real_mult (mte_nat_to_R M) (real_inv_pos h Hh))
                  (real_const (Z.of_nat n0 # 1)%Q) h HBlt Hh)).
    - exact (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat n0 # 1)%Q) h
                 (mte_nat_to_R n0) h
                 (real_eq_sym _ _ (mte_nat_const_eq n0)) (real_eq_refl h)).
  }
  assert (Hpow : real_le (real_plus real_one (real_mult (mte_nat_to_R n0) h))
                         (mte_rpow (cauchy_real_exp x) n0)).
  { apply (mte_le_congr_r _ (mte_rpow (real_plus real_one h) n0)).
    - exact (mte_pow_ge h n0 Hh).
    - exact (mte_rpow_ext (real_plus real_one h) (cauchy_real_exp x) n0
               (real_eq_sym _ _ Eexp)).
  }
  assert (Hbase : real_lt (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n0)).
  { apply (mte_lt_le_trans (mte_nat_to_R M)
               (real_plus real_one (real_mult (mte_nat_to_R n0) h))).
    - exact (real_lt_trans (mte_nat_to_R M) (real_mult (mte_nat_to_R n0) h)
               (real_plus real_one (real_mult (mte_nat_to_R n0) h)) H5
               (mte_lt_plus_one (real_mult (mte_nat_to_R n0) h))).
    - exact Hpow.
  }
  exists n0. intros n Hn.
  destruct (Nat.eq_dec n n0) as [Heq | Hne].
  - rewrite Heq. exact Hbase.
  - assert (Hgt : (n = n0 + Datatypes.S (n - Datatypes.S n0))%nat) by lia.
    rewrite Hgt.
    exact (real_lt_trans (mte_nat_to_R M) (mte_rpow (cauchy_real_exp x) n0)
             (mte_rpow (cauchy_real_exp x)
                (n0 + Datatypes.S (n - Datatypes.S n0)))
             Hbase (mte_rpow_mono_add (cauchy_real_exp x) n0
                      (n - Datatypes.S n0) Hb)).
Qed.

(* ---------- 验证打印：全件零公理面（G2 关卡证据） ---------- *)
Print Assumptions mte_lt_plus_r.
Print Assumptions mte_lt_plus_one.
Print Assumptions mte_le_congr.
Print Assumptions mte_le_congr_r.
Print Assumptions mte_lt_le_trans.
Print Assumptions mte_le_plus_compat.
Print Assumptions mte_le_mult_compat_r.
Print Assumptions mte_nat_mult_pos.
Print Assumptions mte_nat_to_R_S_pos.
Print Assumptions mte_const_ext.
Print Assumptions mte_const_plus.
Print Assumptions mte_nat_const_eq.
Print Assumptions mte_rpow_pos.
Print Assumptions mte_rpow_step_lt.
Print Assumptions mte_rpow_mono_add.
Print Assumptions mte_rpow_ext.
Print Assumptions mte_pow_ge.
Print Assumptions mte_exp_pow_iter.
Print Assumptions mte_inv_divergence.
Print Assumptions mte_exp_divergence.
