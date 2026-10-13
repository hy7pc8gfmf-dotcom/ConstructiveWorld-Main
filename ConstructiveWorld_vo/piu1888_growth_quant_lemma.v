(* ============================================================
   模块名: piu1888_growth_quant_lemma
   数学使命: pi 分离核载量尺度量 T0=(2n)!/n! 的定量核心——步进恒等式
     qfact(2(S n))*qfact n == 2*(2n+1 作为 Q)*qfact(2n)*qfact(S n)、
     倍增单调肢 2*T0n <= T0(S n)（乘积形）、正性配套肢、除法转移引理。
   依赖清单: Stdlib QArith, Stdlib Lia (nat 侧线性算术记录)。
   对标行: LW0LeibSeparation.v K=BF*C1+BFd*C2+1/8 (:5469);
     闭式坐标 f^(d)(q)=(-1)^n b^n q^(2n-d) d!/((d-n)!(2n-d)!) (n<=d<=2n)。
   构造性注记: 语句 Prop 层 Qle/Qlt; 定义透明; 无 Axiom/Admitted;
     Qinv 只经 piu1888_div_le 单点化; 闭数值步 vm_compute 收尾（辅助计算）。
   编译配方: coqc -q piu1888_growth_quant_lemma.v (COQLIB=Rocq 9.1)
   ============================================================ *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.

Fixpoint piu1888_qN (n : nat) : Q :=
  match n with
  | O => 0#1
  | S k => (1#1) + piu1888_qN k
  end.

Fixpoint piu1888_qfact (n : nat) : Q :=
  match n with
  | O => 1#1
  | S k => piu1888_qN (S k) * piu1888_qfact k
  end.

Fixpoint piu1888_qpow (q : Q) (m : nat) : Q :=
  match m with
  | O => 1#1
  | S k => q * piu1888_qpow q k
  end.

Lemma piu1888_qN_step : forall k, piu1888_qN (S k) == (1#1) + piu1888_qN k.
Proof. reflexivity. Qed.

Lemma piu1888_qfact_step : forall k, piu1888_qfact (S k) == piu1888_qN (S k) * piu1888_qfact k.
Proof. reflexivity. Qed.

Lemma piu1888_mul_ge0 : forall a b : Q, (0#1) <= a -> (0#1) <= b -> (0#1) <= a * b.
Proof. intros a b Ha Hb. apply Qmult_le_0_compat; assumption. Qed.

Lemma piu1888_qN_double : forall n, piu1888_qN (2 * n) == (2#1) * piu1888_qN n.
Proof.
  induction n as [|n IH].
  - vm_compute. reflexivity.
  - assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
    rewrite H2n.
    rewrite piu1888_qN_step, piu1888_qN_step, IH.
    rewrite piu1888_qN_step.
    rewrite (Qmult_plus_distr_r (2#1) (1#1) (piu1888_qN n)).
    rewrite Qmult_1_r.
    rewrite Qplus_assoc.
    reflexivity.
Qed.

Lemma piu1888_qN_ge0 : forall k, (0#1) <= piu1888_qN k.
Proof.
  induction k as [|k IHk].
  - vm_compute. discriminate.
  - rewrite piu1888_qN_step.
    apply (Qplus_le_compat (0#1) (1#1) (0#1) (piu1888_qN k)).
    + vm_compute. discriminate.
    + exact IHk.
Qed.

Lemma piu1888_qN_ge1 : forall k, (1#1) <= piu1888_qN (S k).
Proof.
  intros k. rewrite piu1888_qN_step.
  apply (Qle_trans ((1#1)) ((1#1) + (0#1)) ((1#1) + piu1888_qN k)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN k)).
    + apply Qle_refl.
    + apply piu1888_qN_ge0.
Qed.

Lemma piu1888_qN_pos : forall k, (0#1) < piu1888_qN (S k).
Proof.
  intros k. apply (Qlt_le_trans (0#1) (1#1) (piu1888_qN (S k))).
  - vm_compute. reflexivity.
  - apply piu1888_qN_ge1.
Qed.

Lemma piu1888_qfact_ge1 : forall n, (1#1) <= piu1888_qfact n.
Proof.
  induction n as [|n IH].
  - vm_compute. discriminate.
  - rewrite piu1888_qfact_step.
    apply (Qle_trans ((1#1)) (piu1888_qfact n) (piu1888_qN (S n) * piu1888_qfact n)).
    + exact IH.
    + apply (Qle_trans (piu1888_qfact n) ((1#1) * piu1888_qfact n)
               (piu1888_qN (S n) * piu1888_qfact n)).
      * rewrite Qmult_1_l. apply Qle_refl.
      * apply (Qmult_le_compat_r (1#1) (piu1888_qN (S n)) (piu1888_qfact n)).
        -- exact (piu1888_qN_ge1 n).
        -- apply (Qle_trans (0#1) (1#1) (piu1888_qfact n)).
           ++ vm_compute. discriminate.
           ++ exact IH.
Qed.

Lemma piu1888_qfact_pos : forall n, (0#1) < piu1888_qfact n.
Proof.
  intros n. apply (Qlt_le_trans (0#1) (1#1) (piu1888_qfact n)).
  - vm_compute. reflexivity.
  - apply piu1888_qfact_ge1.
Qed.

Lemma piu1888_qpow_pos : forall q m, (0#1) < q -> (0#1) < piu1888_qpow q m.
Proof.
  intros q m Hq. induction m as [|m IH]; [vm_compute; reflexivity|].
  simpl. apply Qmult_lt_0_compat; assumption.
Qed.

Lemma piu1888_Qmul_cancel : forall a b c : Q, ~ (c == 0) -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc Heq.
  assert (H1 : a * c * / c == b * c * / c) by (rewrite Heq; reflexivity).
  rewrite <- (Qmult_assoc a c (/ c)) in H1.
  rewrite <- (Qmult_assoc b c (/ c)) in H1.
  rewrite (Qmult_inv_r c Hc) in H1.
  rewrite Qmult_1_r in H1.
  rewrite Qmult_1_r in H1.
  exact H1.
Qed.

Lemma piu1888_prod_shuffle : forall a b c d : Q,
  a * b * (c * d) == a * c * (b * d).
Proof.
  intros a b c d.
  rewrite <- (Qmult_assoc a b (c * d)).
  rewrite <- (Qmult_assoc a c (b * d)).
  rewrite (Qmult_comm b (c * d)).
  rewrite <- (Qmult_assoc c d b).
  rewrite (Qmult_comm d b).
  reflexivity.
Qed.

Lemma piu1888_le_mul_r : forall w v : Q, (0#1) <= w -> (1#1) <= v -> w <= w * v.
Proof.
  intros w v Hw Hv.
  apply (Qle_trans ((w)) ((v * w)) ((w * v))).
  - apply (Qle_trans ((w)) ((1#1) * w) ((v * w))).
    + rewrite Qmult_1_l. apply Qle_refl.
    + apply (Qmult_le_compat_r (1#1) v w).
      * exact Hv.
      * exact Hw.
  - rewrite (Qmult_comm v w). apply Qle_refl.
Qed.

(* T0 = (2n)!/n! *)
Definition piu1888_T0 (n : nat) : Q := piu1888_qfact (2 * n) * / piu1888_qfact n.

Lemma piu1888_T0_pos : forall n, (0#1) < piu1888_T0 n.
Proof.
  intros n. unfold piu1888_T0. apply Qmult_lt_0_compat.
  - apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply piu1888_qfact_pos.
Qed.

(* 步进恒等式（乘积形）: (2(S n))! * n! == 2*(2n+1 作为 Q) * (2n)! * (S n)! *)
Lemma piu1888_T0_prod_step : forall n,
  piu1888_qfact (2 * S n) * piu1888_qfact n ==
  (2#1) * piu1888_qN (S (2 * n)) * piu1888_qfact (2 * n) * piu1888_qfact (S n).
Proof.
  intros n.
  assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
  rewrite H2n.
  rewrite piu1888_qfact_step, piu1888_qfact_step.
  rewrite piu1888_qN_step, piu1888_qN_step, piu1888_qN_double.
  rewrite piu1888_qfact_step, piu1888_qN_step.
  assert (Hc : (1#1) + ((1#1) + (2#1) * piu1888_qN n) == (2#1) * ((1#1) + piu1888_qN n)).
  { rewrite (Qmult_plus_distr_r (2#1) (1#1) (piu1888_qN n)).
    rewrite Qmult_1_r.
    rewrite Qplus_assoc.
    reflexivity. }
  rewrite Hc.
  rewrite (Qmult_assoc ((2#1) * ((1#1) + piu1888_qN n))
                       ((1#1) + (2#1) * piu1888_qN n) (piu1888_qfact (2 * n))).
  rewrite <- (Qmult_assoc (2#1) ((1#1) + piu1888_qN n)
                       ((1#1) + (2#1) * piu1888_qN n)).
  rewrite (Qmult_comm ((1#1) + piu1888_qN n) ((1#1) + (2#1) * piu1888_qN n)).
  rewrite (Qmult_assoc (2#1) ((1#1) + (2#1) * piu1888_qN n)
                       ((1#1) + piu1888_qN n)).
  rewrite <- (Qmult_assoc ((2#1) * ((1#1) + (2#1) * piu1888_qN n) *
                       ((1#1) + piu1888_qN n)) (piu1888_qfact (2 * n))
                       (piu1888_qfact n)).
  rewrite (piu1888_prod_shuffle ((2#1) * ((1#1) + (2#1) * piu1888_qN n))
            ((1#1) + piu1888_qN n) (piu1888_qfact (2 * n)) (piu1888_qfact n)).
  reflexivity.
Qed.

(* 倍增单调肢（乘积形）: 2*(2n)!*n! <= (2(S n))!*(S n)! *)
Lemma piu1888_T0_mono_prod : forall n,
  (2#1) * (piu1888_qfact (2 * n) * piu1888_qfact n) <=
  piu1888_qfact (2 * S n) * piu1888_qfact (S n).
Proof.
  intros n.
  assert (Hx0 : (0#1) <= piu1888_qN n) by apply piu1888_qN_ge0.
  assert (HQ1 : (1#1) <= (1#1) + (2#1) * piu1888_qN n).
  { apply (Qle_trans ((1#1)) ((1#1) + (0#1)) ((1#1) + (2#1) * piu1888_qN n)).
    - rewrite Qplus_0_r. apply Qle_refl.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) ((2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + apply piu1888_mul_ge0.
        * vm_compute. discriminate.
        * exact Hx0. }
  assert (HQ0 : (0#1) <= (1#1) + (2#1) * piu1888_qN n).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + (2#1) * piu1888_qN n)).
    - vm_compute. discriminate.
    - exact HQ1. }
  assert (HP0 : (0#1) <= (1#1) + ((1#1) + (2#1) * piu1888_qN n)).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + ((1#1) + (2#1) * piu1888_qN n))).
    - vm_compute. discriminate.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) ((1#1) + (2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + exact HQ0. }
  assert (HP1 : (2#1) <= (1#1) + ((1#1) + (2#1) * piu1888_qN n)).
  { apply (Qle_trans ((1#1) + (1#1)) ((1#1) + (1#1))
             ((1#1) + ((1#1) + (2#1) * piu1888_qN n))).
    - apply Qle_refl.
    - apply (Qplus_le_compat (1#1) (1#1) (1#1) ((1#1) + (2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + exact HQ1. }
  assert (H1x : (0#1) <= (1#1) + piu1888_qN n).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + piu1888_qN n)).
    - vm_compute. discriminate.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN n)).
      + apply Qle_refl.
      + exact Hx0. }
  assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
  rewrite H2n.
  rewrite (piu1888_qfact_step (S (2 * n))).
  rewrite (piu1888_qfact_step n).
  rewrite piu1888_qN_step, piu1888_qN_step, piu1888_qN_double, piu1888_qN_step.
  rewrite (piu1888_qfact_step (2 * n)).
  rewrite piu1888_qN_step, piu1888_qN_double.
  rewrite piu1888_prod_shuffle.
  rewrite <- (Qmult_assoc ((1#1) + (2#1) * piu1888_qN n)
             (piu1888_qfact (2 * n)) (piu1888_qfact n)).
  rewrite (Qmult_assoc (((1#1) + ((1#1) + (2#1) * piu1888_qN n))
             * ((1#1) + piu1888_qN n)) ((1#1) + (2#1) * piu1888_qN n)
             (piu1888_qfact (2 * n) * piu1888_qfact n)).
  apply (Qmult_le_compat_r (2#1)
           (((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n)
              * ((1#1) + (2#1) * piu1888_qN n))
           (piu1888_qfact (2 * n) * piu1888_qfact n)).
  - apply (Qle_trans (2#1) ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
             ((((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
                * ((1#1) + (2#1) * piu1888_qN n))).
    + exact HP1.
    + apply (Qle_trans ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
               (((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
               ((((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
                  * ((1#1) + (2#1) * piu1888_qN n))).
      * apply (piu1888_le_mul_r ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
                 ((1#1) + piu1888_qN n)).
        -- exact HP0.
        -- apply (Qle_trans (1#1) ((1#1) + (0#1)) ((1#1) + piu1888_qN n)).
           ++ rewrite Qplus_0_r. apply Qle_refl.
           ++ apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN n)).
              ** apply Qle_refl.
              ** exact Hx0.
      * apply (piu1888_le_mul_r (((1#1) + ((1#1) + (2#1) * piu1888_qN n))
                     * ((1#1) + piu1888_qN n))
                 ((1#1) + (2#1) * piu1888_qN n)).
        -- apply piu1888_mul_ge0.
           ++ exact HP0.
           ++ exact H1x.
        -- exact HQ1.
  - apply piu1888_mul_ge0; apply Qlt_le_weak; apply piu1888_qfact_pos.
Qed.

(* 除法转移（Qinv 单点化） *)
Lemma piu1888_inv_mul_swap : forall s t : Q,
  (0#1) < s -> (0#1) < t -> t * / (s * t) == / s.
Proof.
  intros s t Hs Ht.
  assert (Hst : ~ (s * t == 0)).
  { intros Hc. exact (Qlt_not_eq (0#1) (s * t) (Qmult_lt_0_compat s t Hs Ht)
                       (Qeq_sym (s * t) (0#1) Hc)). }
  assert (Hs0 : ~ (s == 0)).
  { intros Hc. exact (Qlt_not_eq (0#1) s Hs (Qeq_sym s (0#1) Hc)). }
  assert (H1 : s * (t * / (s * t)) == s * / s).
  { rewrite (Qmult_assoc s t (/(s * t))).
    rewrite (Qmult_inv_r (s * t) Hst).
    rewrite (Qmult_inv_r s Hs0).
    reflexivity. }
  rewrite (Qmult_comm s (t * / (s * t))) in H1.
  rewrite (Qmult_comm s (/ s)) in H1.
  exact (piu1888_Qmul_cancel (t * / (s * t)) (/ s) s Hs0 H1).
Qed.

Lemma piu1888_div_le : forall u v s t : Q,
  (0#1) < s -> (0#1) < t -> u * t <= v * s -> u * / s <= v * / t.
Proof.
  intros u v s t Hs Ht H.
  assert (H1 : u * t * / (s * t) <= v * s * / (s * t)).
  { apply (Qmult_le_compat_r (u * t) (v * s) (/(s * t))).
    - exact H.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; assumption. }
  rewrite <- (Qmult_assoc u t (/(s * t))) in H1.
  rewrite <- (Qmult_assoc v s (/(s * t))) in H1.
  rewrite (piu1888_inv_mul_swap s t Hs Ht) in H1.
  rewrite (Qmult_comm s t) in H1.
  rewrite (piu1888_inv_mul_swap t s Ht Hs) in H1.
  exact H1.
Qed.

Lemma piu1888_T0_le : forall n, (2#1) * piu1888_T0 n <= piu1888_T0 (S n).
Proof.
  intros n. unfold piu1888_T0.
  rewrite (Qmult_assoc (2#1) (piu1888_qfact (2 * n)) (/ (piu1888_qfact n))).
  apply (piu1888_div_le ((2#1) * piu1888_qfact (2 * n)) (piu1888_qfact (2 * S n))
                        (piu1888_qfact n) (piu1888_qfact (S n))).
  - apply piu1888_qfact_pos.
  - apply piu1888_qfact_pos.
  - rewrite (piu1888_T0_prod_step n).
    apply (Qmult_le_compat_r ((2#1) * piu1888_qfact (2 * n))
             ((2#1) * piu1888_qN (S (2 * n)) * piu1888_qfact (2 * n))
             (piu1888_qfact (S n))).
    + apply (Qmult_le_compat_r (2#1) ((2#1) * piu1888_qN (S (2 * n)))
                                (piu1888_qfact (2 * n))).
      * apply (Qle_trans ((2#1)) ((1#1) * (2#1))
                 ((2#1) * piu1888_qN (S (2 * n)))).
        -- rewrite Qmult_1_l. apply Qle_refl.
        -- rewrite (Qmult_comm (2#1) (piu1888_qN (S (2 * n)))).
           apply (Qmult_le_compat_r (1#1) (piu1888_qN (S (2 * n))) (2#1)).
           ++ exact (piu1888_qN_ge1 (2 * n)).
           ++ vm_compute. discriminate.
      * apply (Qle_trans (0#1) (1#1) (piu1888_qfact (2 * n))).
        -- vm_compute. discriminate.
        -- apply piu1888_qfact_ge1.
    + apply Qlt_le_weak; apply piu1888_qfact_pos.
Qed.
