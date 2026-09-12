(* ===== UpReqExpPosQBound.v —— 席PA2：Q 层偶阶截断正下界显式见证（1/(1+B) 形） =====
   路线（评审003 路径 A.3.1 余量，与席PA 的 1/C 形不同源）：
     S_{2m}(−a)·S_{2m}(a) == 1 + corr m a（S03 实名 exp_even_mul_eq）
     + S_{2m}(a) 构造性上界 B(m,a) := (2m+1)·(1+a)^{2m}（upqb 自建保守界，S03 无现成单侧和上界引擎）
     ⟹ S_{2m}(−a) ≥ 1/B 且 1/(1+B) < 1/B ⟹ q := 1/(1+B) > 0 可计算。
   纯基座路线：不 Require 席PA 的 UpReqExpPosWitness（1/C 形）。
   语句面全 Set 层：QltT/QleT（S02），存在 sigT，合取 prod（%type 标注）；
   Prop 版 Qle/Qlt 仅用于证明体内部，出口经 Qlt_to_QltT 桥（S02 先例）。
   复用（禁重定义）：exp_partial/q_pow/q_fact/q_pow_mono/q_fact_pos/corr/corr_nonneg/
   exp_even_mul_eq/exp_even_neg_pos（S03）；QltT/QleT/QleT'/Qlt_to_QltT/QltT_to_Qlt/
   qeq_imp_qle/qeq_le（S02/S03）；Id/id_refl（S01）。G1 禁词零命中、纯构造。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Lia.

(* ============ S1 定义面：upqb_exp_partial 复用别名 + 暖身 ============ *)

Definition upqb_exp_partial := exp_partial.

Lemma upqb_exp_partial_eq : forall (n : nat) (x : Q), upqb_exp_partial n x == exp_partial n x.
Proof. reflexivity. Qed.

Lemma upqb_qlt_0_1 : Qlt 0 1.
Proof. unfold Qlt; simpl; lia. Qed.

Lemma upqb_qle_0_1 : Qle 0 1.
Proof. apply Qlt_le_weak. exact upqb_qlt_0_1. Qed.

(* 暖身①：m=0（S_0 ≡ 1 与 a 无关）：显式 q := 1/2，QltT 两面 reflexivity 级闭合 *)
Lemma upqb_witness_m0 : forall a : Q,
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (upqb_exp_partial 0 a)))%type).
Proof.
  intros a. exists (1#2)%Q. split; reflexivity.
Qed.

(* 暖身②：具体例 m=1, a=1：S_2(−1) = 1−1+1/2 = 1/2 > 1/3 > 0（计算级闭合） *)
Lemma upqb_witness_m1_a1 :
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (exp_partial 2 (Qopp 1)%Q)))%type).
Proof. exists (1#3)%Q. split; reflexivity. Qed.

(* ============ S2 前置：QleT 消去与序小件 ============ *)

(* QleT → Qle（S02 无 QleT_to_Qle，upqb 自建；右支经 Id/id_refl 消去） *)
Lemma upqb_qleT_to_qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [Hlt | Hid].
  - apply (Qlt_le_weak x y). exact (QltT_to_Qlt x y Hlt).
  - destruct Hid. apply Qle_refl.
Qed.

Lemma upqb_qle_le_plus : forall a : Q, Qle a (1 + a)%Q.
Proof.
  intro a.
  apply (Qle_trans a (a + 0)%Q (1 + a)%Q).
  - apply qeq_le. ring.
  - apply (Qle_trans (a + 0)%Q (a + 1)%Q (1 + a)%Q).
    + apply (Qplus_le_compat a a 0 1).
      * apply Qle_refl.
      * exact upqb_qle_0_1.
    + apply qeq_le. ring.
Qed.

Lemma upqb_qle_1_plus : forall a : Q, Qle 0 a -> Qle 1 (1 + a)%Q.
Proof.
  intros a Ha.
  apply (Qle_trans 1 (1 + 0)%Q (1 + a)%Q).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat 1 1 0 a).
    + apply Qle_refl.
    + exact Ha.
Qed.

(* ============ S2 前置：上界引擎小件 ============ *)

Lemma upqb_qfact_ge_one : forall k : nat, Qle 1 (q_fact k).
Proof.
  induction k as [| k IH].
  - apply Qle_refl.
  - change (q_fact (Datatypes.S k)) with ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)%Q.
    apply (Qmult_le_compat_nonneg 1 (Z.of_nat (Datatypes.S k) # 1) 1 (q_fact k)).
    + split; [exact upqb_qle_0_1 | unfold Qle; simpl; lia].
    + split; [exact upqb_qle_0_1 | exact IH].
Qed.

Lemma upqb_one_le_pow : forall (b : Q) (n : nat), Qle 1 b -> Qle 1 (q_pow b n).
Proof.
  intros b n Hb. induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply (Qmult_le_compat_nonneg 1 b 1 (q_pow b n)).
    + split; [exact upqb_qle_0_1 | exact Hb].
    + split; [exact upqb_qle_0_1 | exact IH].
Qed.

Lemma upqb_pow_step : forall (b : Q) (n : nat), Qle 1 b ->
  Qle (q_pow b n) (q_pow b (Datatypes.S n)).
Proof.
  intros b n Hb.
  change (q_pow b (Datatypes.S n)) with (b * q_pow b n)%Q.
  apply (Qle_trans (q_pow b n) (1 * q_pow b n)%Q (b * q_pow b n)%Q).
  - apply qeq_le. ring.
  - apply (Qmult_le_compat_nonneg 1 b (q_pow b n) (q_pow b n)).
    + split; [exact upqb_qle_0_1 | exact Hb].
    + split; [exact (Qle_trans 0 1 (q_pow b n) upqb_qle_0_1 (upqb_one_le_pow b n Hb))
             | apply Qle_refl].
Qed.

Lemma upqb_pow_idx_mono : forall (b : Q) (k n : nat), Qle 1 b -> (k <= n)%nat ->
  Qle (q_pow b k) (q_pow b n).
Proof.
  intros b k n Hb Hkn. induction n as [| n IH].
  - assert (Hk : k = 0%nat) by lia. subst k. apply Qle_refl.
  - destruct (Nat.eq_dec k (Datatypes.S n)) as [He | Hne].
    + subst k. apply Qle_refl.
    + apply (Qle_trans (q_pow b k) (q_pow b n) (q_pow b (Datatypes.S n))).
      * apply IH. lia.
      * apply (upqb_pow_step b n Hb).
Qed.

(* 上界主件：0 ≤ a ⟹ S_n(a) ≤ (n+1)·(1+a)^n（逐项丢 k! ≥ 1、同底幂单调、几何控比） *)
(* 逆序引理：0 < x ≤ y ⟹ /y ≤ /x（upqb 自建；stdlib 无直接形） *)
Lemma upqb_inv_le_pos : forall x y : Q, Qlt 0 x -> Qle x y -> Qle (Qinv y) (Qinv x).
Proof.
  intros x y Hx Hxy.
  assert (Hypos : Qlt 0 y) by (apply (Qlt_le_trans 0 x y); [exact Hx | exact Hxy]).
  assert (Hinvx : Qlt 0 (Qinv x)) by (apply Qinv_lt_0_compat; exact Hx).
  assert (Hx0 : x * Qinv x == 1) by (apply Qmult_inv_r; apply (q_neq_of_lt x Hx)).
  assert (Hy0 : y * Qinv y == 1) by (apply Qmult_inv_r; apply (q_neq_of_lt y Hypos)).
  assert (Hyinv : Qlt 0 (Qinv y)) by (apply Qinv_lt_0_compat; exact Hypos).
  assert (S1 : Qle 1 (y * Qinv x)).
  { apply (Qle_trans 1 (x * Qinv x) (y * Qinv x)).
    - apply qeq_le. symmetry. exact Hx0.
    - apply (Qmult_le_compat_r x y (Qinv x)).
      + exact Hxy.
      + apply (Qlt_le_weak 0 (Qinv x)). exact Hinvx. }
  assert (S3 : Qinv y * (y * Qinv x) == Qinv x).
  { transitivity ((y * Qinv y) * Qinv x).
    - ring.
    - rewrite Hy0. ring. }
  apply (Qle_trans (Qinv y) (Qinv y * 1)%Q (Qinv x)).
  - apply qeq_le. ring.
  - apply (Qle_trans (Qinv y * 1)%Q (Qinv y * (y * Qinv x)) (Qinv x)).
    + apply (Qmult_le_compat_nonneg (Qinv y) (Qinv y) 1 (y * Qinv x)).
      * split; [apply (Qlt_le_weak 0 (Qinv y)); exact Hyinv | apply Qle_refl].
      * split; [exact upqb_qle_0_1 | exact S1].
    + apply qeq_le. exact S3.
Qed.

Lemma upqb_sum_le : forall (a : Q) (n : nat), Qle 0 a ->
  Qle (exp_partial n a) ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n).
Proof.
  intros a n Ha. induction n as [| n IH].
  - unfold Qle; simpl; lia.
  - change (exp_partial (Datatypes.S n) a) with
      (exp_partial n a + q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))%Q.
    assert (Hb1 : Qle 1 (1 + a)%Q) by (apply upqb_qle_1_plus; exact Ha).
    assert (Hab : Qle a (1 + a)%Q) by (apply upqb_qle_le_plus).
    assert (Hinv1 : Qinv 1 == 1).
    { pose proof (Qmult_inv_r 1 (q_neq_of_lt 1 upqb_qlt_0_1)) as Hx.
      rewrite Qmult_1_l in Hx. exact Hx. }
    (* a^k/k! ≤ b^k/k! ≤ b^k，b := 1+a *)
    assert (Hstep : Qle (q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))
                        (q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qle_trans _ (q_pow (1 + a)%Q (Datatypes.S n) / q_fact (Datatypes.S n)) _).
      - apply (Qmult_le_compat_r (q_pow a (Datatypes.S n)) (q_pow (1 + a)%Q (Datatypes.S n))
                                 (Qinv (q_fact (Datatypes.S n)))).
        + apply (q_pow_mono a (1 + a)%Q (Datatypes.S n)); [exact Ha | exact Hab].
        + apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S n)))).
          apply Qinv_lt_0_compat. apply q_fact_pos.
      - unfold Qdiv.
        apply (Qle_trans _ (q_pow (1 + a)%Q (Datatypes.S n) * 1)%Q _).
        + apply (Qmult_le_compat_nonneg (q_pow (1 + a)%Q (Datatypes.S n))
                                        (q_pow (1 + a)%Q (Datatypes.S n))
                                        (Qinv (q_fact (Datatypes.S n))) 1).
          * split;
              [apply (Qle_trans 0 1 (q_pow (1 + a)%Q (Datatypes.S n)));
                [exact upqb_qle_0_1
                | exact (upqb_one_le_pow (1 + a)%Q (Datatypes.S n) Hb1)]
              | apply Qle_refl].
          * split;
              [apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S n))));
                apply Qinv_lt_0_compat; apply q_fact_pos
              | apply (Qle_trans (Qinv (q_fact (Datatypes.S n))) (Qinv 1) 1);
                [ apply (upqb_inv_le_pos 1 (q_fact (Datatypes.S n)));
                  [ exact upqb_qlt_0_1
                  | exact (upqb_qfact_ge_one (Datatypes.S n)) ]
                | apply qeq_le; exact Hinv1 ]].
        + apply qeq_le. ring. }
    (* b^n ≤ b^{S n} 与系数递推 *)
    assert (Hpow : Qle (q_pow (1 + a)%Q n) (q_pow (1 + a)%Q (Datatypes.S n)))
      by (apply (upqb_pow_step (1 + a)%Q n Hb1)).
    assert (HB : Qle ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n)
                     ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qmult_le_compat_nonneg (Z.of_nat (Datatypes.S n) # 1) (Z.of_nat (Datatypes.S n) # 1)
                                    (q_pow (1 + a)%Q n) (q_pow (1 + a)%Q (Datatypes.S n))).
      - split;
          [apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S n) # 1));
            apply (Qlt_of_nat_lt 0 (Datatypes.S n)); lia
          | apply Qle_refl].
      - split;
          [ apply (Qle_trans 0 1 (q_pow (1 + a)%Q n));
            [ exact upqb_qle_0_1
            | exact (upqb_one_le_pow (1 + a)%Q n Hb1) ]
          | exact Hpow]. }
    assert (Hfinal : Qle ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n)
                          + q_pow (1 + a)%Q (Datatypes.S n))
                         ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                          * q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qle_trans _ ((Qplus (Z.of_nat (Datatypes.S n) # 1) 1)%Q
                          * q_pow (1 + a)%Q (Datatypes.S n)) _).
      - apply qeq_le. ring.
      - apply (Qmult_le_compat_r ((Qplus (Z.of_nat (Datatypes.S n) # 1) 1)%Q)
                                 ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
                                 (q_pow (1 + a)%Q (Datatypes.S n))).
        + assert (Hz : (Z.of_nat (Datatypes.S (Datatypes.S n))
                        = Z.of_nat (Datatypes.S n) + 1)%Z) by lia.
          rewrite Hz. unfold Qle; simpl; lia.
        + apply (Qle_trans 0 1 (q_pow (1 + a)%Q (Datatypes.S n))).
          * exact upqb_qle_0_1.
          * exact (upqb_one_le_pow (1 + a)%Q (Datatypes.S n) Hb1). }
    apply (Qle_trans _ (exp_partial n a + q_pow (1 + a)%Q (Datatypes.S n)) _).
    + apply (Qplus_le_compat (exp_partial n a) (exp_partial n a)
                             (q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))
                             (q_pow (1 + a)%Q (Datatypes.S n))).
      * apply Qle_refl.
      * exact Hstep.
    + apply (Qle_trans _
        ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n)
         + q_pow (1 + a)%Q (Datatypes.S n)) _).
      * apply (Qplus_le_compat (exp_partial n a)
                               ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))
                               (q_pow (1 + a)%Q (Datatypes.S n))
                               (q_pow (1 + a)%Q (Datatypes.S n))).
        -- exact (Qle_trans (exp_partial n a)
                            ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n)
                            ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))
                            IH HB).
        -- apply Qle_refl.
      * exact Hfinal.
Qed.

(* ============ S2 主件：B、q 定义与显式见证 ============ *)

Definition upqb_B (a : Q) (m : nat) : Q :=
  (Z.of_nat (Datatypes.S (2 * m)) # 1) * q_pow (1 + a)%Q (2 * m).

Definition upqb_q (a : Q) (m : nat) : Q := Qinv (1 + upqb_B a m)%Q.

Lemma upqb_B_pos : forall (a : Q) (m : nat), Qle 0 a -> Qlt 0 (upqb_B a m).
Proof.
  intros a m Ha. unfold upqb_B.
  apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (2 * m)) # 1)
                           (q_pow (1 + a)%Q (2 * m))).
  - unfold Qlt; simpl; lia.
  - apply (Qlt_le_trans 0 1 (q_pow (1 + a)%Q (2 * m))).
    + exact upqb_qlt_0_1.
    + exact (upqb_one_le_pow (1 + a)%Q (2 * m) (upqb_qle_1_plus a Ha)).
Qed.

(* 主件：0 ≤T a ⟹ 显式 q := 1/(1+B)，0 <T q <T S_{2m}(−a)（Set 层 sigT×prod 见证） *)
Lemma upqb_even_witness : forall (a : Q) (m : nat), QleT 0 a ->
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (exp_partial (2 * m) (Qopp a))))%type).
Proof.
  intros a m HaT.
  assert (Ha : Qle 0 a) by exact (upqb_qleT_to_qle 0 a HaT).
  assert (Hxpos : Qlt 0 (exp_partial (2 * m) (Qopp a)))
    by exact (exp_even_neg_pos a m Ha).
  (* ① 1 ≤ x·S(a)：exp_even_mul_eq + corr_nonneg（乘积恒等路线核心） *)
  assert (Hmul : Qle 1 (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)).
  { rewrite (exp_even_mul_eq a m).
    apply (Qle_trans 1%Q (1 + 0)%Q (1 + corr m a)).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      + apply Qle_refl.
      + exact (corr_nonneg a m Ha). }
  (* ② S(a) ≤ B ⟹ 1 ≤ x·B ⟹ 1 < x·(1+B) *)
  assert (HBle : Qle (exp_partial (2 * m) a) (upqb_B a m))
    by exact (upqb_sum_le a (2 * m) Ha).
  assert (Hxposle : Qle 0 (exp_partial (2 * m) (Qopp a)))
    by exact (Qlt_le_weak 0 (exp_partial (2 * m) (Qopp a)) Hxpos).
  assert (HmulB : Qle 1 (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
  { apply (Qle_trans 1 (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)
                       (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
    - exact Hmul.
    - apply (Qle_trans (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)
                       (exp_partial (2 * m) a * exp_partial (2 * m) (Qopp a))
                       (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
      + apply qeq_le. ring.
      + apply (Qle_trans (exp_partial (2 * m) a * exp_partial (2 * m) (Qopp a))
                         (upqb_B a m * exp_partial (2 * m) (Qopp a))
                         (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
        * apply (Qmult_le_compat_r (exp_partial (2 * m) a) (upqb_B a m)
                                   (exp_partial (2 * m) (Qopp a))).
          -- exact HBle.
          -- exact Hxposle.
        * apply qeq_le. ring. }
  assert (HposB : Qlt 0 (upqb_B a m)) by exact (upqb_B_pos a m Ha).
  assert (Hfin : Qlt 1 ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                        + exp_partial (2 * m) (Qopp a))).
  { apply (Qle_lt_trans 1 ((exp_partial (2 * m) (Qopp a) * upqb_B a m) + 0)
                         ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                          + exp_partial (2 * m) (Qopp a))).
    - apply (Qle_trans 1 (exp_partial (2 * m) (Qopp a) * upqb_B a m)
                        ((exp_partial (2 * m) (Qopp a) * upqb_B a m) + 0)).
      + exact HmulB.
      + apply qeq_le. ring.
    - apply (proj2 (Qplus_lt_r 0 (exp_partial (2 * m) (Qopp a))
                                (exp_partial (2 * m) (Qopp a) * upqb_B a m)) Hxpos). }
  (* ③ 乘 /（1+B）> 0：q := 1/(1+B) 满足 0 < q < x *)
  assert (Honeb : (1 + upqb_B a m)%Q * Qinv (1 + upqb_B a m)%Q == 1).
  { apply Qmult_inv_r. apply (q_neq_of_lt (1 + upqb_B a m)%Q).
    apply (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q).
    - exact upqb_qlt_0_1.
    - apply upqb_qle_1_plus.
      apply (Qlt_le_weak 0 (upqb_B a m)). exact HposB. }
  exists (upqb_q a m). split.
  - apply Qlt_to_QltT. unfold upqb_q.
    exact (Qinv_lt_0_compat (1 + upqb_B a m)%Q
             (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q upqb_qlt_0_1
                (upqb_qle_1_plus (upqb_B a m)
                   (Qlt_le_weak 0 (upqb_B a m) HposB)))).
  - apply Qlt_to_QltT. unfold upqb_q.
    assert (Hraw : Qlt (1 * Qinv (1 + upqb_B a m)%Q)
                       (((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                         + exp_partial (2 * m) (Qopp a))
                        * Qinv (1 + upqb_B a m)%Q)).
    { apply (Qmult_lt_compat_r 1
               ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                + exp_partial (2 * m) (Qopp a))
               (Qinv (1 + upqb_B a m)%Q)).
      - apply Qinv_lt_0_compat.
        apply (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q).
        + exact upqb_qlt_0_1.
        + apply upqb_qle_1_plus.
          apply (Qlt_le_weak 0 (upqb_B a m)). exact HposB.
      - exact Hfin. }
    assert (E2 : ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                  + exp_partial (2 * m) (Qopp a))
                 * Qinv (1 + upqb_B a m)%Q == exp_partial (2 * m) (Qopp a)).
    { transitivity (exp_partial (2 * m) (Qopp a)
                    * ((1 + upqb_B a m)%Q * Qinv (1 + upqb_B a m)%Q)).
      - ring.
      - rewrite Honeb. ring. }
    setoid_rewrite (Qmult_1_l (Qinv (1 + upqb_B a m)%Q)) in Hraw.
    setoid_rewrite E2 in Hraw.
    exact Hraw.
Qed.

(* S3 面：见证函数 Q→Q 提取形（projT1 消去，验证可提取性用） *)
Definition upqb_witness_fun (a : Q) (m : nat) (Ha : QleT 0 a) : Q :=
  projT1 (upqb_even_witness a m Ha).
