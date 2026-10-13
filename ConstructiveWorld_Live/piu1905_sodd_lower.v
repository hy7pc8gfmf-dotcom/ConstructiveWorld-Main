(* ============================================================
   模块名: piu1905_sodd_lower
   数学使命: 奇侧坐标交错和的非相消下界
     Sodd >= (62125/82944)*T0, 其中 T0=(2n)!/n!,
     带域 35/12 <= q <= 41/12, n >= 3。
     奇侧交错和 sodd = sum_k (-1)^k T(n,q,2k+1) (2k+1<=n),
     坐标项 T(n,q,m) = q^m * (2n-m)! / ((n-m)! * m!) (b^n 规一格)。
   依赖清单: piu1888_growth_quant_lemma (qpow/qfact/T0/qN);
     Stdlib QArith, Qring, Lia (nat 线性算术)。
   对标行: LW0LeibSeparation.v K=BF*C1+BFd*C2+1/8 (:5469);
     常数 62125/82944 = (35/24)*(1775/3456), 1775/3456 = 1 - 1681/3456,
     1681/3456 = (41/12)^2/24, 常数面经精确有理数算术逐位复核。
   构造性注记: 有名语句与字段位全 Set 承载 (QleT/QeqT/QltT/band
     包装归纳型); 体内构造性 Prop 推导合法; 定义透明;
     无 Axiom/Admitted/Abort; 非可判定前提为零, 带域与界均以
     显式前提逐肢供给; 非相消关键步 = 相邻奇项递减
     (T(2k+3) <= (q^2/24) T(2k+1)) 与交错和非相消地板。
   编译配方: coqc -q piu1905_sodd_lower.v (COQLIB=Rocq 9.1,
     依赖 piu1888_growth_quant_lemma.vo 同目录)
   ============================================================ *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qring.
Require Import piu1888_growth_quant_lemma.

Inductive piu1905_QleT (x y : Q) : Set :=
  piu1905_qleT_intro : x <= y -> piu1905_QleT x y.
Inductive piu1905_QltT (x y : Q) : Set :=
  piu1905_qltT_intro : x < y -> piu1905_QltT x y.
Inductive piu1905_QeqT (x y : Q) : Set :=
  piu1905_qeqT_intro : x == y -> piu1905_QeqT x y.
Inductive piu1905_band (q : Q) : Set :=
  piu1905_band_intro : (35#12) <= q -> q <= (41#12) -> piu1905_band q.

Definition piu1905_T (q : Q) (n m : nat) : Q :=
  piu1888_qpow q m * piu1888_qfact (2 * n - m) *
  / (piu1888_qfact (n - m) * piu1888_qfact m).
Definition piu1905_sodd_term (q : Q) (n k : nat) : Q :=
  if Nat.even k then piu1905_T q n (2 * k + 1)
                else Qopp (piu1905_T q n (2 * k + 1)).
Fixpoint piu1905_sodd (q : Q) (n k : nat) {struct k} : Q :=
  match k with
  | O => piu1905_sodd_term q n 0
  | S k' => piu1905_sodd q n k' + piu1905_sodd_term q n (S k')
  end.
Fixpoint piu1905_half (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (piu1905_half n')
  end.
Definition piu1905_sodd_full (q : Q) (n : nat) : Q :=
  piu1905_sodd q n (piu1905_half (Nat.pred n)).

Lemma piu1905_prod_rotate : forall a b c : Q, a * (b * c) == b * (a * c).
Proof.
  intros a b c.
  rewrite (Qmult_assoc a b c).
  rewrite (Qmult_comm a b).
  rewrite <- (Qmult_assoc b a c).
  reflexivity.
Qed.

Lemma piu1905_T_pos : forall (q : Q) (n m : nat),
  (0#1) < q -> (m <= n)%nat -> piu1905_QltT (0#1) (piu1905_T q n m).
Proof.
  intros q n m Hq Hm. apply piu1905_qltT_intro. unfold piu1905_T.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply piu1888_qpow_pos. exact Hq.
    + apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      [apply piu1888_qfact_pos | apply piu1888_qfact_pos].
Qed.

Lemma piu1905_T0_pos : forall n : nat, piu1905_QltT (0#1) (piu1888_T0 n).
Proof.
  intros n. apply piu1905_qltT_intro. apply piu1888_T0_pos.
Qed.

Lemma piu1905_opp_le : forall x y : Q,
  piu1905_QleT x y -> piu1905_QleT (Qopp y) (Qopp x).
Proof.
  intros x y H. destruct H as [H]. apply piu1905_qleT_intro.
  apply (Qle_trans (Qopp y) (Qopp y + (y + Qopp x)) (Qopp x)).
  - apply (Qle_trans (Qopp y) (Qopp y + (0#1)) (Qopp y + (y + Qopp x))).
    + rewrite (Qplus_0_r (Qopp y)). apply Qle_refl.
    + apply (Qplus_le_compat (Qopp y) (Qopp y) (0#1) (y + Qopp x)).
      * apply Qle_refl.
      * apply (Qle_trans (0#1) (x + Qopp x) (y + Qopp x)).
        -- rewrite Qplus_opp_r. apply Qle_refl.
        -- apply (Qplus_le_compat x y (Qopp x) (Qopp x)).
           ++ exact H.
           ++ apply Qle_refl.
  - rewrite (Qplus_assoc (Qopp y) y (Qopp x)).
    rewrite (Qplus_comm (Qopp y) y).
    rewrite (Qplus_opp_r y).
    rewrite (Qplus_comm (0#1) (Qopp x)).
    rewrite (Qplus_0_r (Qopp x)). apply Qle_refl.
Qed.

Lemma piu1905_minus_le : forall a b c : Q,
  piu1905_QleT a b -> piu1905_QleT (c - b) (c - a).
Proof.
  intros a b c H. destruct H as [H]. apply piu1905_qleT_intro.
  apply (Qplus_le_compat c c (Qopp b) (Qopp a)).
  - apply Qle_refl.
  - apply piu1905_opp_le. apply piu1905_qleT_intro. exact H.
Qed.

Lemma piu1905_le_cancel : forall (c a b : Q),
  (0#1) < c -> piu1905_QleT (c * a) (c * b) -> piu1905_QleT a b.
Proof.
  intros c a b Hc H. destruct H as [H]. apply piu1905_qleT_intro.
  assert (Hc0 : ~ (c == 0)).
  { intro Heq. apply (Qlt_not_eq (0#1) c Hc). rewrite Heq. reflexivity. }
  assert (H1 : a * c <= b * c).
  { rewrite (Qmult_comm a c). rewrite (Qmult_comm b c). exact H. }
  assert (H2 : a * / c <= b * / c)
    by (apply (piu1888_div_le a b c c); assumption).
  assert (Ha : a == a * / c * c).
  { rewrite <- (Qmult_assoc a (/ c) c).
    rewrite (Qmult_comm (/ c) c).
    rewrite (Qmult_inv_r c Hc0).
    rewrite Qmult_1_r. reflexivity. }
  assert (Hb : b == b * / c * c).
  { rewrite <- (Qmult_assoc b (/ c) c).
    rewrite (Qmult_comm (/ c) c).
    rewrite (Qmult_inv_r c Hc0).
    rewrite Qmult_1_r. reflexivity. }
  rewrite Ha. rewrite Hb.
  apply (Qmult_le_compat_r (a * / c) (b * / c) c).
  - exact H2.
  - apply Qlt_le_weak. exact Hc.
Qed.

Lemma piu1905_qN_add : forall a b : nat,
  piu1905_QeqT (piu1888_qN (a + b)) (piu1888_qN a + piu1888_qN b).
Proof.
  intros a b. apply piu1905_qeqT_intro.
  induction b as [|b IH].
  - replace (a + 0)%nat with a by lia.
    replace (piu1888_qN 0) with (0#1) by (vm_compute; reflexivity).
    rewrite Qplus_0_r. reflexivity.
  - replace (a + S b)%nat with (S (a + b)) by lia.
    rewrite piu1888_qN_step, piu1888_qN_step, IH.
    rewrite (Qplus_assoc (1#1) (piu1888_qN a) (piu1888_qN b)).
    rewrite (Qplus_comm (1#1) (piu1888_qN a)).
    rewrite <- (Qplus_assoc (piu1888_qN a) (1#1) (piu1888_qN b)).
    reflexivity.
Qed.

Lemma piu1905_qN_mono : forall a b : nat,
  (a <= b)%nat -> piu1905_QleT (piu1888_qN a) (piu1888_qN b).
Proof.
  intros a b Hab. apply piu1905_qleT_intro.
  assert (Hsplit : piu1888_qN b == piu1888_qN a + piu1888_qN (b - a)).
  { assert (Hbr : b = (a + (b - a))%nat) by lia.
    destruct (piu1905_qN_add a (b - a)) as [Heq].
    rewrite Hbr at 1.
    rewrite Heq. reflexivity. }
  rewrite Hsplit.
  apply (Qle_trans (piu1888_qN a) (piu1888_qN a + (0#1))
                   (piu1888_qN a + piu1888_qN (b - a))).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (piu1888_qN a) (piu1888_qN a) (0#1)
                           (piu1888_qN (b - a))).
    + apply Qle_refl.
    + apply piu1888_qN_ge0.
Qed.

Lemma piu1905_qpow_shift2 : forall (q : Q) (k : nat),
  piu1888_qpow q (k + 2) == q * q * piu1888_qpow q k.
Proof.
  intros q k. induction k as [|k IH].
  - cbn [piu1888_qpow Nat.add]. rewrite !Qmult_1_r. reflexivity.
  - cbn [piu1888_qpow Nat.add]. rewrite IH.
    rewrite (piu1905_prod_rotate q (q * q) (piu1888_qpow q k)).
    reflexivity.
Qed.

Lemma piu1905_T1_identity : forall (q : Q) (n : nat),
  (1 <= n)%nat -> piu1905_QeqT ((2#1) * piu1905_T q n 1) (q * piu1888_T0 n).
Proof.
  intros q n Hn. apply piu1905_qeqT_intro.
  unfold piu1905_T, piu1888_T0.
  cbn [piu1888_qpow]. rewrite Qmult_1_r.
  assert (Hq2 : piu1888_qfact (2 * n) == piu1888_qN (2 * n) * piu1888_qfact (2 * n - 1)).
  { replace (2 * n)%nat with (S (2 * n - 1)) by lia.
    rewrite piu1888_qfact_step.
    replace (S (2 * n - 1) - 1)%nat with (2 * n - 1)%nat by lia.
    reflexivity. }
  assert (Hqn : piu1888_qfact n == piu1888_qN n * piu1888_qfact (n - 1)).
  { replace n with (S (n - 1)) by lia.
    rewrite piu1888_qfact_step.
    replace (S (n - 1) - 1)%nat with (n - 1)%nat by lia.
    reflexivity. }
  assert (Hc1 : piu1888_qfact 1 == (1#1)) by (vm_compute; reflexivity).
  rewrite Hq2, Hqn, Hc1, (piu1888_qN_double n).
  rewrite Qmult_1_r.
  assert (HB0 : ~ (piu1888_qfact (n - 1) == 0)).
  { intro Heq.
    apply (Qlt_not_eq (0#1) (piu1888_qfact (n - 1)) (piu1888_qfact_pos (n - 1))).
    rewrite Heq. reflexivity. }
  assert (HK0 : ~ (piu1888_qN n * piu1888_qfact (n - 1) == 0)).
  { intro Heq.
    assert (Hlt : (0#1) < piu1888_qN n).
    { replace n with (S (n - 1))%nat by lia.
      apply piu1888_qN_pos. }
    apply (Qlt_not_eq (0#1) (piu1888_qN n * piu1888_qfact (n - 1))
            (Qmult_lt_0_compat _ _ Hlt (piu1888_qfact_pos (n - 1)))).
    rewrite Heq. reflexivity. }
  apply (piu1888_Qmul_cancel
          ((2#1) * (q * piu1888_qfact (2 * n - 1) * / piu1888_qfact (n - 1)))
          (q * ((2#1) * piu1888_qN n * piu1888_qfact (2 * n - 1)
                * / (piu1888_qN n * piu1888_qfact (n - 1))))
          (piu1888_qN n * piu1888_qfact (n - 1)) HK0).
  rewrite <- (Qmult_assoc (2#1)
              (q * piu1888_qfact (2 * n - 1) * / piu1888_qfact (n - 1))
              (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (q * piu1888_qfact (2 * n - 1))
                       (/ piu1888_qfact (n - 1))
                       (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_comm (/ piu1888_qfact (n - 1))
                      (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (piu1888_qN n) (piu1888_qfact (n - 1))
                       (/ piu1888_qfact (n - 1))).
  rewrite (Qmult_inv_r (piu1888_qfact (n - 1)) HB0).
  rewrite Qmult_1_r.
  rewrite <- (Qmult_assoc q
              (((2#1) * piu1888_qN n) * piu1888_qfact (2 * n - 1)
               * / (piu1888_qN n * piu1888_qfact (n - 1)))
              (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (((2#1) * piu1888_qN n) * piu1888_qfact (2 * n - 1))
                       (/ (piu1888_qN n * piu1888_qfact (n - 1)))
                       (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_comm (/ (piu1888_qN n * piu1888_qfact (n - 1)))
                      (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_inv_r (piu1888_qN n * piu1888_qfact (n - 1)) HK0).
  rewrite Qmult_1_r.
  rewrite <- (Qmult_assoc (2#1) (piu1888_qN n) (piu1888_qfact (2 * n - 1))).
  rewrite (piu1905_prod_rotate q (2#1)
            (piu1888_qN n * piu1888_qfact (2 * n - 1))).
  rewrite (piu1905_prod_rotate q (piu1888_qN n)
            (piu1888_qfact (2 * n - 1))).
  rewrite (Qmult_comm (piu1888_qN n)
            (q * piu1888_qfact (2 * n - 1))).
  reflexivity.
Qed.

(* ---- 带域配套 ---- *)

Lemma piu1905_band_pos : forall q : Q,
  piu1905_band q -> (0#1) < q.
Proof.
  intros q Hb. destruct Hb as [Hlo Hhi].
  apply (Qlt_le_trans (0#1) (35#12) q).
  - vm_compute. reflexivity.
  - exact Hlo.
Qed.

Lemma piu1905_band_qq_le : forall q : Q,
  piu1905_band q -> piu1905_QleT (q * q) (24#1).
Proof.
  intros q Hb. destruct Hb as [Hlo Hhi]. apply piu1905_qleT_intro.
  apply (Qle_trans (q * q) ((41#12) * (41#12)) (24#1)).
  - apply (Qle_trans (q * q) ((41#12) * q) ((41#12) * (41#12))).
    + apply (Qmult_le_compat_r q (41#12) q).
      * exact Hhi.
      * apply Qlt_le_weak.
        apply (piu1905_band_pos q (piu1905_band_intro q Hlo Hhi)).
    + rewrite (Qmult_comm (41#12) q).
      apply (Qmult_le_compat_r q (41#12) (41#12)).
      * exact Hhi.
      * vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.


(* ---- qN 核心不等式 (2/3/4 分解) ---- *)

Lemma piu1905_qN_sum_ge0 : forall a b : nat,
  piu1905_QleT (0#1) (piu1888_qN a + piu1888_qN b).
Proof.
  intros a b. apply piu1905_qleT_intro.
  apply (Qle_trans (0#1) ((0#1) + (0#1)) (piu1888_qN a + piu1888_qN b)).
  - vm_compute. discriminate.
  - apply (Qplus_le_compat (0#1) (piu1888_qN a) (0#1) (piu1888_qN b)).
    + apply piu1888_qN_ge0.
    + apply piu1888_qN_ge0.
Qed.

Lemma piu1905_qN_core : forall (a2 a1 b2 b1 e3 e2 m : nat),
  (b2 = (a2 + m))%nat -> (b1 = (a1 + m))%nat ->
  (a2 <= m)%nat -> (a1 <= m)%nat ->
  (3 <= e3)%nat -> (2 <= e2)%nat ->
  piu1905_QleT ((24#1) * piu1888_qN a2 * piu1888_qN a1)
               (piu1888_qN b2 * (piu1888_qN e3 * (piu1888_qN e2 * piu1888_qN b1))).
Proof.
  intros a2 a1 b2 b1 e3 e2 m Hb2 Hb1 Ha2m Ha1m He3 He2.
  subst b2. subst b1.
  apply piu1905_qleT_intro.
  destruct (piu1905_qN_add a2 m) as [E2A].
  destruct (piu1905_qN_add a1 m) as [E1A].
  rewrite E2A, E1A.
  assert (Hmono2 : piu1905_QleT (piu1888_qN a2) (piu1888_qN m))
    by (apply piu1905_qN_mono; exact Ha2m).
  assert (Hmono1 : piu1905_QleT (piu1888_qN a1) (piu1888_qN m))
    by (apply piu1905_qN_mono; exact Ha1m).
  assert (HE3 : piu1905_QleT (piu1888_qN 3) (piu1888_qN e3))
    by (apply piu1905_qN_mono; exact He3).
  assert (HE2 : piu1905_QleT (piu1888_qN 2) (piu1888_qN e2))
    by (apply piu1905_qN_mono; exact He2).
  destruct HE3 as [HE3]. destruct HE2 as [HE2].
  assert (Hv3 : piu1888_qN 3 == (3#1)) by (vm_compute; reflexivity).
  assert (Hv2 : piu1888_qN 2 == (2#1)) by (vm_compute; reflexivity).
  rewrite Hv3 in HE3. rewrite Hv2 in HE2.
  assert (HA : piu1905_QleT ((2#1) * piu1888_qN a2)
                             (piu1888_qN a2 + piu1888_qN m)).
  { apply piu1905_qleT_intro.
    rewrite (Qmult_comm (2#1) (piu1888_qN a2)).
    assert (H2l : (2#1) == (1#1) + (1#1)) by (vm_compute; reflexivity).
    rewrite H2l, Qmult_plus_distr_r, Qmult_1_r.
    apply (Qplus_le_compat (piu1888_qN a2) (piu1888_qN a2)
                           (piu1888_qN a2) (piu1888_qN m)).
    - apply Qle_refl.
    - destruct Hmono2 as [Hm2]. exact Hm2. }
  assert (HB : piu1905_QleT ((2#1) * piu1888_qN a1)
                             (piu1888_qN a1 + piu1888_qN m)).
  { apply piu1905_qleT_intro.
    rewrite (Qmult_comm (2#1) (piu1888_qN a1)).
    assert (H2lb : (2#1) == (1#1) + (1#1)) by (vm_compute; reflexivity).
    rewrite H2lb, Qmult_plus_distr_r, Qmult_1_r.
    apply (Qplus_le_compat (piu1888_qN a1) (piu1888_qN a1)
                           (piu1888_qN a1) (piu1888_qN m)).
    - apply Qle_refl.
    - destruct Hmono1 as [Hm1]. exact Hm1. }
  assert (H4B : piu1905_QleT ((4#1) * piu1888_qN a1)
                             (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))).
  { apply piu1905_qleT_intro.
    assert (H4 : (4#1) == (2#1) * (2#1)) by (vm_compute; reflexivity).
    rewrite H4.
    apply (Qle_trans (((2#1) * (2#1)) * piu1888_qN a1)
                     ((piu1888_qN a1 + piu1888_qN m) * (2#1))
                     (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))).
    - rewrite <- (Qmult_assoc (2#1) (2#1) (piu1888_qN a1)).
      rewrite (Qmult_comm (2#1) (2 * piu1888_qN a1)).
      apply (Qmult_le_compat_r (2 * piu1888_qN a1)
               (piu1888_qN a1 + piu1888_qN m) (2#1)).
      + destruct HB as [HBx]. exact HBx.
      + vm_compute. discriminate.
    - rewrite (Qmult_comm (piu1888_qN a1 + piu1888_qN m) (2#1)).
      apply (Qmult_le_compat_r (2#1) (piu1888_qN e2)
               (piu1888_qN a1 + piu1888_qN m)).
      + exact HE2.
      + destruct (piu1905_qN_sum_ge0 a1 m) as [Hs1m]. exact Hs1m. }
  assert (Hrest : piu1905_QleT ((3#1) * ((4#1) * piu1888_qN a1))
                             (piu1888_qN e3 *
                              (piu1888_qN e2 *
                               (piu1888_qN a1 + piu1888_qN m)))).
  { apply piu1905_qleT_intro.
    apply (Qle_trans ((3#1) * ((4#1) * piu1888_qN a1))
                     ((3#1) * (piu1888_qN e2 *
                               (piu1888_qN a1 + piu1888_qN m)))
                     (piu1888_qN e3 *
                      (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))).
    - rewrite (Qmult_comm (3#1) ((4#1) * piu1888_qN a1)).
      rewrite (Qmult_comm (3#1) (piu1888_qN e2 *
                                 (piu1888_qN a1 + piu1888_qN m))).
      apply (Qmult_le_compat_r ((4#1) * piu1888_qN a1)
                               (piu1888_qN e2 *
                                (piu1888_qN a1 + piu1888_qN m)) (3#1)).
      + destruct H4B as [H4B']. exact H4B'.
      + vm_compute. discriminate.
    - apply (Qmult_le_compat_r (3#1) (piu1888_qN e3)
                               (piu1888_qN e2 *
                                (piu1888_qN a1 + piu1888_qN m))).
      + exact HE3.
      + apply piu1888_mul_ge0.
        * apply piu1888_qN_ge0.
        * destruct (piu1905_qN_sum_ge0 a1 m) as [Hs1m2]. exact Hs1m2. }
  assert (Hsp : ((24#1) * piu1888_qN a2) * piu1888_qN a1 ==
                ((2#1) * piu1888_qN a2) * ((3#1) * ((4#1) * piu1888_qN a1))).
  { rewrite <- (Qmult_assoc (24#1) (piu1888_qN a2) (piu1888_qN a1)).
    assert (H24 : (24#1) == (2#1) * ((3#1) * (4#1)))
      by (vm_compute; reflexivity).
    rewrite H24.
    rewrite <- (Qmult_assoc (2#1) ((3#1) * (4#1)) (piu1888_qN a2 * piu1888_qN a1)).
    rewrite <- (Qmult_assoc (3#1) (4#1) (piu1888_qN a2 * piu1888_qN a1)).
    rewrite (piu1905_prod_rotate (4#1) (piu1888_qN a2) (piu1888_qN a1)).
    rewrite (Qmult_assoc (3#1) (piu1888_qN a2) ((4#1) * piu1888_qN a1)).
    rewrite (Qmult_comm (3#1) (piu1888_qN a2)).
    rewrite <- (Qmult_assoc (piu1888_qN a2) (3#1) ((4#1) * piu1888_qN a1)).
    rewrite (Qmult_assoc (2#1) (piu1888_qN a2)
              ((3#1) * ((4#1) * piu1888_qN a1))).
    reflexivity. }
  rewrite Hsp.
  apply (Qle_trans ((2#1) * piu1888_qN a2 *
                     ((3#1) * ((4#1) * piu1888_qN a1)))
                   ((piu1888_qN a2 + piu1888_qN m) *
                    ((3#1) * ((4#1) * piu1888_qN a1)))
                   ((piu1888_qN a2 + piu1888_qN m) *
                    (piu1888_qN e3 *
                     (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))))).
  - destruct HA as [HA'].
    apply (Qmult_le_compat_r ((2#1) * piu1888_qN a2)
             (piu1888_qN a2 + piu1888_qN m)
             ((3#1) * ((4#1) * piu1888_qN a1))).
    + exact HA'.
    + apply piu1888_mul_ge0.
      * vm_compute. discriminate.
      * apply piu1888_mul_ge0.
        -- vm_compute. discriminate.
        -- apply piu1888_qN_ge0.
  - destruct Hrest as [Hrest'].
    rewrite (Qmult_comm (piu1888_qN a2 + piu1888_qN m)
              ((3#1) * ((4#1) * piu1888_qN a1))).
    rewrite (Qmult_comm (piu1888_qN a2 + piu1888_qN m)
              (piu1888_qN e3 *
               (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))).
    apply (Qmult_le_compat_r ((3#1) * ((4#1) * piu1888_qN a1))
             (piu1888_qN e3 *
              (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))
             (piu1888_qN a2 + piu1888_qN m)).
    + exact Hrest'.
    + destruct (piu1905_qN_sum_ge0 a2 m) as [Hs2m]. exact Hs2m.
Qed.


(* ---- 相邻奇项递减 (L-dec) 与地板配套 ---- *)

Lemma piu1905_T_pos' : forall (q : Q) (n m : nat),
  (0#1) < q -> piu1905_QltT (0#1) (piu1905_T q n m).
Proof.
  intros q n m Hq. apply piu1905_qltT_intro. unfold piu1905_T.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply piu1888_qpow_pos. exact Hq.
    + apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      [apply piu1888_qfact_pos | apply piu1888_qfact_pos].
Qed.

Lemma piu1905_floor_const_eq : (35#24) * (1775#3456) == (62125#82944).
Proof. vm_compute. reflexivity. Qed.

Lemma piu1905_negb_inv : forall b : bool, negb (negb b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma piu1905_even_succ : forall k, Nat.even (S k) = negb (Nat.even k).
Proof.
  induction k as [|[|k] IH].
  - reflexivity.
  - reflexivity.
  - cbn [Nat.even] in IH |- *.
    rewrite IH.
    rewrite piu1905_negb_inv.
    reflexivity.
Qed.

Lemma piu1905_nat_double_ind : forall P : nat -> Prop,
  P 0%nat -> P 1%nat -> (forall k, P k -> P (S (S k))) -> forall k, P k.
Proof.
  intros P H0 H1 HS k.
  assert (Ha : P k /\ P (S k)).
  { induction k as [|k [IH1 IH2]].
    - split; assumption.
    - split; [exact IH2 | apply HS; exact IH1]. }
  destruct Ha as [Ha _]. exact Ha.
Qed.

Lemma piu1905_even_plus2 : forall a b : nat,
  Nat.even (a + S (S b)) = Nat.even (a + b).
Proof.
  induction a as [|a IH].
  - cbn [Nat.add]. cbn [Nat.even]. reflexivity.
  - intros b. cbn [Nat.add].
    rewrite piu1905_even_succ.
    rewrite piu1905_even_succ.
    rewrite IH. reflexivity.
Qed.

Lemma piu1905_even_2k : forall k, Nat.even (2 * k) = true.
Proof.
  apply piu1905_nat_double_ind.
  - reflexivity.
  - reflexivity.
  - intros k IH.
    cbn [Nat.mul Nat.add Nat.even].
    rewrite (piu1905_even_plus2 k (k + 0)%nat).
    exact IH.
Qed.

Lemma piu1905_even_2k1 : forall k, Nat.even (2 * k + 1) = false.
Proof.
  intros k. replace (2 * k + 1)%nat with (S (2 * k))%nat by lia.
  rewrite piu1905_even_succ, piu1905_even_2k. reflexivity.
Qed.

Lemma piu1905_sodd_two_step : forall q n k,
  piu1905_sodd q n (S (S k)) ==
  piu1905_sodd q n k + (piu1905_sodd_term q n (S k) +
                        piu1905_sodd_term q n (S (S k))).
Proof.
  intros q n k. cbn [piu1905_sodd]. rewrite Qplus_assoc. reflexivity.
Qed.

Lemma piu1905_term_even : forall q n k, Nat.even k = true ->
  piu1905_sodd_term q n k == piu1905_T q n (2 * k + 1).
Proof.
  intros q n k H. unfold piu1905_sodd_term. rewrite H. reflexivity.
Qed.

Lemma piu1905_term_odd : forall q n k, Nat.even k = false ->
  piu1905_sodd_term q n k == Qopp (piu1905_T q n (2 * k + 1)).
Proof.
  intros q n k H. unfold piu1905_sodd_term. rewrite H. reflexivity.
Qed.

Lemma piu1905_T_odd_dec : forall (q : Q) (n i : nat),
  (0#1) < q -> (2 * i + 3 <= n)%nat ->
  (24#1) * piu1905_T q n (2 * i + 3) <= q * q * piu1905_T q n (2 * i + 1).
Proof.
  intros q n i Hq Hi.
  assert (Hqshift : piu1888_qpow q (2*i+3) == q * q * piu1888_qpow q (2*i+1)).
  { replace (2*i+3)%nat with (2*i+1+2)%nat by lia.
    rewrite piu1905_qpow_shift2. reflexivity. }
  assert (HfL : piu1888_qfact (n - (2*i+1)) ==
                piu1888_qN (n - (2*i+1)) *
                (piu1888_qN (n - (2*i+2)) * piu1888_qfact (n - (2*i+3)))).
  { replace (n - (2*i+1))%nat with (S (n - (2*i+2)))%nat by lia.
    rewrite piu1888_qfact_step.
    replace (n - (2*i+2))%nat with (S (n - (2*i+3)))%nat by lia.
    rewrite piu1888_qfact_step.
    reflexivity. }
  assert (HfG : piu1888_qfact (2*n - (2*i+1)) ==
                piu1888_qN (2*n - (2*i+1)) *
                (piu1888_qN (2*n - (2*i+2)) * piu1888_qfact (2*n - (2*i+3)))).
  { replace (2*n - (2*i+1))%nat with (S (2*n - (2*i+2)))%nat by lia.
    rewrite piu1888_qfact_step.
    replace (2*n - (2*i+2))%nat with (S (2*n - (2*i+3)))%nat by lia.
    rewrite piu1888_qfact_step.
    reflexivity. }
  assert (HfE : piu1888_qfact (2*i+3) ==
                piu1888_qN (2*i+3) *
                (piu1888_qN (2*i+2) * piu1888_qfact (2*i+1))).
  { replace (2*i+3)%nat with (S (2*i+2))%nat by lia.
    rewrite piu1888_qfact_step.
    replace (2*i+2)%nat with (S (2*i+1))%nat by lia.
    rewrite piu1888_qfact_step.
    reflexivity. }
  unfold piu1905_T.
  rewrite (Qmult_assoc (24#1)
            (piu1888_qpow q (2*i+3) * piu1888_qfact (2*n - (2*i+3)))
            (/ (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+3)))).
  rewrite (Qmult_assoc (q*q)
            (piu1888_qpow q (2*i+1) * piu1888_qfact (2*n - (2*i+1)))
            (/ (piu1888_qfact (n - (2*i+1)) * piu1888_qfact (2*i+1)))).
  apply (piu1888_div_le
          ((24#1) * (piu1888_qpow q (2*i+3) * piu1888_qfact (2*n - (2*i+3))))
          (q * q * (piu1888_qpow q (2*i+1) * piu1888_qfact (2*n - (2*i+1))))
          (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+3))
          (piu1888_qfact (n - (2*i+1)) * piu1888_qfact (2*i+1))).
  - apply Qmult_lt_0_compat; apply piu1888_qfact_pos.
  - apply Qmult_lt_0_compat; apply piu1888_qfact_pos.
  - rewrite Hqshift, HfL, HfG, HfE.
    assert (E1 : ((24#1) * (((q*q) * piu1888_qpow q (2*i+1)) *
                             piu1888_qfact (2*n - (2*i+3)))) *
                 ((piu1888_qN (n - (2*i+1)) *
                   (piu1888_qN (n - (2*i+2)) * piu1888_qfact (n - (2*i+3)))) *
                  piu1888_qfact (2*i+1)) ==
                 ((24#1) * piu1888_qN (n - (2*i+1)) * piu1888_qN (n - (2*i+2))) *
                 ((((q*q) * piu1888_qpow q (2*i+1)) *
                   piu1888_qfact (2*n - (2*i+3))) *
                  (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1))))
      by ring.
    assert (E2 : ((q*q) * (piu1888_qpow q (2*i+1) *
                            (piu1888_qN (2*n - (2*i+1)) *
                             (piu1888_qN (2*n - (2*i+2)) *
                              piu1888_qfact (2*n - (2*i+3)))))) *
                 (piu1888_qfact (n - (2*i+3)) *
                  (piu1888_qN (2*i+3) *
                   (piu1888_qN (2*i+2) * piu1888_qfact (2*i+1)))) ==
                 (piu1888_qN (2*n - (2*i+1)) *
                  (piu1888_qN (2*i+3) *
                   (piu1888_qN (2*i+2) * piu1888_qN (2*n - (2*i+2))))) *
                 ((((q*q) * piu1888_qpow q (2*i+1)) *
                   piu1888_qfact (2*n - (2*i+3))) *
                  (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1))))
      by ring.
    rewrite E1, E2.
    apply (Qmult_le_compat_r
            ((24#1) * piu1888_qN (n - (2*i+1)) * piu1888_qN (n - (2*i+2)))
            (piu1888_qN (2*n - (2*i+1)) *
             (piu1888_qN (2*i+3) *
              (piu1888_qN (2*i+2) * piu1888_qN (2*n - (2*i+2)))))
            ((((q*q) * piu1888_qpow q (2*i+1)) *
              piu1888_qfact (2*n - (2*i+3))) *
             (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1)))).
    + assert (HCORE : piu1905_QleT
                        ((24#1) * piu1888_qN (n - (2*i+1)) *
                         piu1888_qN (n - (2*i+2)))
                        (piu1888_qN (2*n - (2*i+1)) *
                         (piu1888_qN (2*i+3) *
                          (piu1888_qN (2*i+2) *
                           piu1888_qN (2*n - (2*i+2)))))).
      * apply (piu1905_qN_core (n - (2*i+1)) (n - (2*i+2))
                 (2*n - (2*i+1)) (2*n - (2*i+2)) (2*i+3) (2*i+2) n).
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
      * destruct HCORE as [HC]. exact HC.
    + apply piu1888_mul_ge0.
      * apply piu1888_mul_ge0.
        -- apply Qmult_le_0_compat.
           ++ apply Qmult_le_0_compat; apply Qlt_le_weak; exact Hq.
           ++ apply Qlt_le_weak. apply piu1888_qpow_pos. exact Hq.
        -- apply Qlt_le_weak. apply piu1888_qfact_pos.
      * apply piu1888_mul_ge0; apply Qlt_le_weak; apply piu1888_qfact_pos.
Qed.


(* ---- 相邻奇项单调 (band 收紧) 与地板（交错级数非相消下界）配套 ---- *)

Lemma piu1905_Qle_sub0 : forall A B : Q,
  piu1905_QleT B A -> piu1905_QleT (0#1) (A - B).
Proof.
  intros A B H. destruct (piu1905_minus_le B A A H) as [Hm].
  apply piu1905_qleT_intro.
  apply (Qle_trans (0#1) (A - A) (A - B)).
  - change (A - A) with (A + Qopp A).
    rewrite (Qplus_opp_r A). apply Qle_refl.
  - exact Hm.
Qed.

Lemma piu1905_sodd_SS : forall q n k,
  piu1905_sodd q n (S (S k)) ==
  piu1905_sodd q n (S k) + piu1905_sodd_term q n (S (S k)).
Proof.
  intros q n k. reflexivity.
Qed.

Lemma piu1905_sodd_one : forall q n,
  piu1905_sodd q n 1 == piu1905_T q n 1 - piu1905_T q n 3.
Proof.
  intros q n. reflexivity.
Qed.

Lemma piu1905_T_odd_mono_dec : forall (q : Q) (n i : nat),
  (0#1) < q -> (2 * i + 3 <= n)%nat ->
  piu1905_QleT (piu1905_T q n (2 * i + 3))
               ((q*q*/(24#1)) * piu1905_T q n (2 * i + 1)).
Proof.
  intros q n i Hq Hi.
  assert (Hc24 : (0#1) < (24#1)) by (vm_compute; reflexivity).
  apply (piu1905_le_cancel (24#1) (piu1905_T q n (2 * i + 3))
          ((q*q*/(24#1)) * piu1905_T q n (2 * i + 1)) Hc24).
  apply piu1905_qleT_intro.
  assert (Ec : (24#1) * ((q*q*/(24#1)) * piu1905_T q n (2 * i + 1)) ==
               q * q * piu1905_T q n (2 * i + 1)) by field.
  rewrite Ec.
  pose proof (piu1905_T_odd_dec q n i Hq Hi) as HTD. exact HTD.
Qed.

Lemma piu1905_T_odd_mono : forall (q : Q) (n i : nat),
  (0#1) < q -> piu1905_band q -> (2 * i + 3 <= n)%nat ->
  piu1905_QleT (piu1905_T q n (2 * i + 3)) (piu1905_T q n (2 * i + 1)).
Proof.
  intros q n i Hq Hb Hi.
  apply piu1905_qleT_intro.
  apply (Qle_trans (piu1905_T q n (2 * i + 3))
                   ((q*q*/(24#1)) * piu1905_T q n (2 * i + 1))
                   (piu1905_T q n (2 * i + 1))).
  - destruct (piu1905_T_odd_mono_dec q n i Hq Hi) as [Hmd]. exact Hmd.
  - assert (Hscale : ((q*q)*/(24#1)) <= (1#1)).
    { apply (Qle_trans ((q*q)*/(24#1)) ((24#1)*/(24#1)) (1#1)).
      - apply (Qmult_le_compat_r (q*q) (24#1) (/(24#1))).
        + destruct (piu1905_band_qq_le q Hb) as [Hqq]. exact Hqq.
        + vm_compute. discriminate.
      - apply piu1905_qleT_intro. vm_compute. discriminate. }
    apply (Qle_trans (((q*q)*/(24#1)) * piu1905_T q n (2 * i + 1))
                     ((1#1) * piu1905_T q n (2 * i + 1))
                     (piu1905_T q n (2 * i + 1))).
    + apply (Qmult_le_compat_r ((q*q)*/(24#1)) (1#1)
               (piu1905_T q n (2 * i + 1))).
      * exact Hscale.
      * destruct (piu1905_T_pos' q n (2 * i + 1) Hq) as [Hp1].
        apply Qlt_le_weak. exact Hp1.
    + rewrite (Qmult_1_l (piu1905_T q n (2 * i + 1))). apply Qle_refl.
Qed.

Lemma piu1905_half_le : forall m, (2 * piu1905_half m <= m)%nat.
Proof.
  apply piu1905_nat_double_ind.
  - cbn [piu1905_half]. lia.
  - cbn [piu1905_half]. lia.
  - intros m IH. cbn [piu1905_half]. lia.
Qed.

Lemma piu1905_half_ge1 : forall m, (2 <= m)%nat -> (1 <= piu1905_half m)%nat.
Proof.
  assert (Hd : forall m, (1 <= piu1905_half m)%nat \/ (m <= 1)%nat).
  { apply (piu1905_nat_double_ind
             (fun m => (1 <= piu1905_half m)%nat \/ (m <= 1)%nat)).
    - right. lia.
    - right. lia.
    - intros k IH. left. cbn [piu1905_half]. lia. }
  intros m H. destruct (Hd m) as [Hge1 | Hle1].
  - exact Hge1.
  - lia.
Qed.

Lemma piu1905_even_odd_split : forall k : nat,
  {m : nat | k = (2 * m)%nat} + {m : nat | k = (2 * m + 1)%nat}.
Proof.
  induction k as [|k IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[m Hm]|[m Hm]].
    + right. exists m. lia.
    + left. exists (S m). lia.
Qed.

Lemma piu1905_even_2m : forall k, Nat.even k = true -> {m : nat | k = (2 * m)%nat}.
Proof.
  intros k. destruct (piu1905_even_odd_split k) as [[m Hm]|[m Hm]].
  - intros _. exists m. exact Hm.
  - intros H. rewrite Hm in H. rewrite (piu1905_even_2k1 m) in H. discriminate H.
Qed.

Lemma piu1905_odd_2m1 : forall k, Nat.even k = false -> {m : nat | k = (2 * m + 1)%nat}.
Proof.
  intros k. destruct (piu1905_even_odd_split k) as [[m Hm]|[m Hm]].
  - intros H. rewrite Hm in H. rewrite (piu1905_even_2k m) in H. discriminate H.
  - intros _. exists m. exact Hm.
Qed.

Lemma piu1905_floor2 : forall (q : Q) (n k : nat),
  (0#1) < q -> piu1905_band q -> (2 * k + 3 <= n)%nat ->
  piu1905_QleT (piu1905_T q n 1 - piu1905_T q n 3) (piu1905_sodd q n k) *
  piu1905_QleT (piu1905_T q n 1 - piu1905_T q n 3)
               (piu1905_sodd q n (S k)).
Proof.
  intros q n k Hq Hb. induction k as [|k IH].
  - intros Hk3. split.
    + apply piu1905_qleT_intro.
      destruct (piu1905_T_pos' q n 3 Hq) as [Hp].
      assert (H03 : piu1905_QleT (0#1) (piu1905_T q n 3))
        by (apply piu1905_qleT_intro; apply Qlt_le_weak; exact Hp).
      destruct (piu1905_minus_le (0#1) (piu1905_T q n 3) (piu1905_T q n 1)
                  H03) as [Hm].
      apply (Qle_trans (piu1905_T q n 1 - piu1905_T q n 3)
                       (piu1905_T q n 1 - (0#1))
                       (piu1905_sodd q n 0)).
      * exact Hm.
      * change (piu1905_sodd q n 0) with (piu1905_T q n 1).
        change (piu1905_T q n 1 - (0#1)) with (piu1905_T q n 1 + Qopp (0#1)).
        assert (E0 : Qopp (0#1) == (0#1)) by (vm_compute; reflexivity).
        rewrite E0. rewrite Qplus_0_r. apply Qle_refl.
    + apply piu1905_qleT_intro. rewrite piu1905_sodd_one. apply Qle_refl.
  - intros Hk5. destruct (IH ltac:(lia)) as [IH1 IH2]. split.
    + exact IH2.
    + apply piu1905_qleT_intro.
      destruct (Nat.even k) eqn:Hk.
      * assert (HP2 : Nat.even (S (S k)) = true) by (cbn [Nat.even]; exact Hk).
        rewrite piu1905_sodd_SS.
        rewrite (piu1905_term_even q n (S (S k)) HP2).
        replace (2 * S (S k) + 1)%nat with (2 * k + 5)%nat by lia.
        apply (Qle_trans (piu1905_T q n 1 - piu1905_T q n 3)
                         (piu1905_sodd q n (S k))
                         (piu1905_sodd q n (S k) + piu1905_T q n (2 * k + 5))).
        -- destruct IH2 as [IH2]. exact IH2.
        -- apply (Qle_trans (piu1905_sodd q n (S k))
                            (piu1905_sodd q n (S k) + (0#1))
                            (piu1905_sodd q n (S k)
                             + piu1905_T q n (2 * k + 5))).
           ++ rewrite Qplus_0_r. apply Qle_refl.
           ++ apply (Qplus_le_compat (piu1905_sodd q n (S k))
                       (piu1905_sodd q n (S k)) (0#1)
                       (piu1905_T q n (2 * k + 5))).
              ** apply Qle_refl.
              ** destruct (piu1905_T_pos' q n (2 * k + 5) Hq) as [Hp5].
                 apply Qlt_le_weak. exact Hp5.
      * assert (HP1 : Nat.even (S k) = true)
          by (rewrite piu1905_even_succ, Hk; reflexivity).
        assert (HP2 : Nat.even (S (S k)) = false) by (cbn [Nat.even]; exact Hk).
        rewrite piu1905_sodd_two_step.
        rewrite (piu1905_term_even q n (S k) HP1).
        rewrite (piu1905_term_odd q n (S (S k)) HP2).
        replace (2 * S k + 1)%nat with (2 * k + 3)%nat by lia.
        replace (2 * S (S k) + 1)%nat with (2 * k + 5)%nat by lia.
        apply (Qle_trans (piu1905_T q n 1 - piu1905_T q n 3)
                         (piu1905_sodd q n k)
                         (piu1905_sodd q n k +
                          (piu1905_T q n (2 * k + 3) +
                           Qopp (piu1905_T q n (2 * k + 5))))).
        -- destruct IH1 as [IH1x]. exact IH1x.
        -- apply (Qle_trans (piu1905_sodd q n k)
                            (piu1905_sodd q n k + (0#1))
                            (piu1905_sodd q n k +
                             (piu1905_T q n (2 * k + 3) +
                              Qopp (piu1905_T q n (2 * k + 5))))).
           ++ rewrite Qplus_0_r. apply Qle_refl.
           ++ apply (Qplus_le_compat (piu1905_sodd q n k)
                       (piu1905_sodd q n k) (0#1)
                       (piu1905_T q n (2 * k + 3) +
                        Qopp (piu1905_T q n (2 * k + 5)))).
              ** apply Qle_refl.
              ** destruct (piu1905_T_odd_mono q n (S k) Hq Hb ltac:(lia)) as [Hmono].
              replace (2 * S k + 3)%nat with (2 * k + 5)%nat in Hmono by lia.
              replace (2 * S k + 1)%nat with (2 * k + 3)%nat in Hmono by lia.
              destruct (piu1905_Qle_sub0 (piu1905_T q n (2 * k + 3))
                          (piu1905_T q n (2 * k + 5))
                          (piu1905_qleT_intro _ _ Hmono)) as [Hs0].
              exact Hs0.
Qed.

Lemma piu1905_sodd_floor : forall (q : Q) (n : nat),
  (0#1) < q -> piu1905_band q -> (3 <= n)%nat ->
  piu1905_QleT (piu1905_T q n 1 - piu1905_T q n 3) (piu1905_sodd_full q n).
Proof.
  intros q n Hq Hb Hn. unfold piu1905_sodd_full.
  assert (HK1 : (1 <= piu1905_half (Nat.pred n))%nat)
    by (apply piu1905_half_ge1; lia).
  assert (HKb : (2 * piu1905_half (Nat.pred n) + 1 <= n)%nat).
  { pose proof (piu1905_half_le (Nat.pred n)) as HH. lia. }
  destruct (Nat.even (piu1905_half (Nat.pred n))) eqn:HK.
  - destruct (piu1905_even_2m (piu1905_half (Nat.pred n)) HK) as [j Hj].
    rewrite Hj.
    replace (2 * j)%nat with (S (2 * j - 1))%nat by lia.
    destruct (piu1905_floor2 q n (2 * j - 1) Hq Hb ltac:(lia)) as [_ Hf2].
    exact Hf2.
  - destruct (piu1905_odd_2m1 (piu1905_half (Nat.pred n)) HK) as [j Hj].
    rewrite Hj.
    replace (2 * j + 1)%nat with (S (2 * j))%nat by lia.
    destruct (piu1905_floor2 q n (2 * j) Hq Hb ltac:(lia)) as [_ Hf2].
    exact Hf2.
Qed.

(* ---- 主定理（下界）：奇侧交错和非相消地板常数 ---- *)

Lemma piu1905_sodd_lower : forall (q : Q) (n : nat),
  (3 <= n)%nat -> piu1905_band q ->
  piu1905_QleT ((62125#82944) * piu1888_T0 n) (piu1905_sodd_full q n).
Proof.
  intros q n Hn Hb.
  destruct Hb as [Hlo Hhi].
  assert (Hbq : piu1905_band q) by (apply piu1905_band_intro; assumption).
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (Hq : (0#1) < q) by (apply (piu1905_band_pos q Hbq)).
  destruct (piu1905_T0_pos n) as [HT0p].
  assert (HT00 : (0#1) <= piu1888_T0 n) by (apply Qlt_le_weak; exact HT0p).
  assert (Hc2 : (0#1) < (2#1)) by (vm_compute; reflexivity).
  assert (H2ne : ~ ((2#1) == (0#1)))
    by (intro Hc; vm_compute in Hc; discriminate).
  assert (Hu0 : (0#1) <= q * / (2#1)).
  { apply (Qmult_le_0_compat q (/ (2#1))).
    - apply Qlt_le_weak. exact Hq.
    - vm_compute. discriminate. }
  destruct (piu1905_T1_identity q n Hn1) as [Hid].
  assert (HT1 : piu1905_T q n 1 == (q * / (2#1)) * piu1888_T0 n).
  { apply (piu1888_Qmul_cancel (piu1905_T q n 1)
             ((q * / (2#1)) * piu1888_T0 n) (2#1) H2ne).
    assert (E2 : ((q * / (2#1)) * piu1888_T0 n) * (2#1) == q * piu1888_T0 n)
      by field.
    rewrite E2. rewrite <- Hid. ring. }
  assert (Hu : piu1905_QleT ((35#24)) (q * / (2#1))).
  { apply (piu1905_le_cancel (2#1) (35#24) (q * / (2#1)) Hc2).
    apply piu1905_qleT_intro.
    assert (Er2 : (2#1) * (q * / (2#1)) == q) by field.
    assert (El : (2#1) * (35#24) == (35#12)) by (vm_compute; reflexivity).
    rewrite Er2. rewrite El. exact Hlo. }
  assert (Hqq4 : q * q <= (41#12) * (41#12)).
  { apply (Qle_trans (q*q) ((41#12)*q) ((41#12)*(41#12))).
    - apply (Qmult_le_compat_r q (41#12) q).
      + exact Hhi.
      + apply Qlt_le_weak. exact Hq.
    - rewrite (Qmult_comm (41#12) q).
      apply (Qmult_le_compat_r q (41#12) (41#12)).
      + exact Hhi.
      + vm_compute. discriminate. }
  assert (Hq2c : piu1905_QleT ((q*q)*/(24#1)) ((1681#3456))).
  { apply piu1905_qleT_intro.
    apply (Qle_trans ((q*q)*/(24#1))
                     (((41#12)*(41#12))*/(24#1))
                     ((1681#3456))).
    - apply (Qmult_le_compat_r (q*q) ((41#12)*(41#12)) (/(24#1))).
      + exact Hqq4.
      + vm_compute. discriminate.
    - assert (Ec2 : ((41#12)*(41#12))*/(24#1) == (1681#3456))
        by (vm_compute; reflexivity).
      rewrite Ec2. apply Qle_refl. }
  destruct Hu as [Hu]. destruct Hq2c as [Hq2c].
  assert (Hac : (35#24) * piu1888_T0 n <= (q * / (2#1)) * piu1888_T0 n)
    by (apply (Qmult_le_compat_r (35#24) (q * / (2#1)) (piu1888_T0 n));
        [exact Hu | exact HT00]).
  assert (HdC : piu1905_QleT ((q*q*/(24#1)) * ((q * / (2#1)) * piu1888_T0 n))
                             ((1681#3456) * ((q * / (2#1)) * piu1888_T0 n))).
  { apply piu1905_qleT_intro.
    apply (Qmult_le_compat_r ((q*q)*/(24#1)) (1681#3456)
             ((q * / (2#1)) * piu1888_T0 n)).
    - exact Hq2c.
    - apply piu1888_mul_ge0; [exact Hu0 | exact HT00]. }
  apply piu1905_qleT_intro.
  assert (EMAIN : (62125#82944) * piu1888_T0 n ==
                  (35#24) * piu1888_T0 n
                  - (1681#3456) * ((35#24) * piu1888_T0 n)) by ring.
  rewrite EMAIN.
  apply (Qle_trans ((35#24) * piu1888_T0 n
                    - (1681#3456) * ((35#24) * piu1888_T0 n))
                   (piu1905_T q n 1
                    - (q*q*/(24#1)) * piu1905_T q n 1)
                   (piu1905_sodd_full q n)).
  - apply (Qle_trans ((35#24) * piu1888_T0 n
                      - (1681#3456) * ((35#24) * piu1888_T0 n))
                     ((q * / (2#1)) * piu1888_T0 n
                      - (1681#3456) * ((q * / (2#1)) * piu1888_T0 n))
                     (piu1905_T q n 1
                      - (q*q*/(24#1)) * piu1905_T q n 1)).
    + assert (EA : ((35#24) * piu1888_T0 n
                    - (1681#3456) * ((35#24) * piu1888_T0 n)) ==
                   ((35#24) * piu1888_T0 n) * ((1#1) - (1681#3456))) by ring.
      assert (EC : ((q * / (2#1)) * piu1888_T0 n
                    - (1681#3456) * ((q * / (2#1)) * piu1888_T0 n)) ==
                   ((q * / (2#1)) * piu1888_T0 n) * ((1#1) - (1681#3456))) by ring.
      rewrite EA. rewrite EC.
      apply (Qmult_le_compat_r ((35#24) * piu1888_T0 n)
               ((q * / (2#1)) * piu1888_T0 n) ((1#1) - (1681#3456))).
      * exact Hac.
      * vm_compute. discriminate.
    + apply (Qle_trans ((q * / (2#1)) * piu1888_T0 n
                        - (1681#3456) * ((q * / (2#1)) * piu1888_T0 n))
                       ((q * / (2#1)) * piu1888_T0 n
                        - (q*q*/(24#1)) * ((q * / (2#1)) * piu1888_T0 n))
                       (piu1905_T q n 1
                        - (q*q*/(24#1)) * piu1905_T q n 1)).
      * destruct (piu1905_minus_le
                    ((q*q*/(24#1)) * ((q * / (2#1)) * piu1888_T0 n))
                    ((1681#3456) * ((q * / (2#1)) * piu1888_T0 n))
                    ((q * / (2#1)) * piu1888_T0 n) HdC) as [Hm2].
        exact Hm2.
      * rewrite <- HT1. apply Qle_refl.
  - apply (Qle_trans (piu1905_T q n 1 - (q*q*/(24#1)) * piu1905_T q n 1)
                     (piu1905_T q n 1 - piu1905_T q n 3)
                     (piu1905_sodd_full q n)).
    + destruct (piu1905_minus_le (piu1905_T q n 3)
                  ((q*q*/(24#1)) * piu1905_T q n 1)
                  (piu1905_T q n 1)
                  (piu1905_T_odd_mono_dec q n 0%nat Hq ltac:(lia))) as [Hml].
      exact Hml.
    + destruct (piu1905_sodd_floor q n Hq Hbq Hn) as [Hf]. exact Hf.
Qed.
