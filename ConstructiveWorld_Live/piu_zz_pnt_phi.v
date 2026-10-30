(* ==========================================================================
   Module: piu_zz_pnt_phi
   Mission: Lower bound for Phi_n, the product of the primes of the kept
     window set P_n: window endpoints b_k = 2n/(2k+1), a_k = 3n/(3k+2),
     boolean window membership discharging the certified window-set
     condition, the width sum over the kept windows dominating
     n*(322/500) - 302, the per-window product of window primes dividing
     Phi_n, the pairwise coprimality of these products from window
     disjointness, and the assembled bound zz_pnt_phi_lower dominating
     zq (Phi_n) by a product of Taylor partial sums, with the theta
     content of each window carried as an explicit universally
     quantified premise slot discharged at section close.
   Dependencies: S03_QExp, piu_zz_padic_clearing, piu_zz_poincare_engine,
     piu_zz_pnt_window, piu_zz_pnt_winsum, piu_zz_pnt_qexp,
     piu_zz_pnt_lcmpow, Stdlib QArith/ZArith/Arith/PArith/Lia/Bool/
     Znumtheory.
   References: the window-theta content and K = 150 window budget faces
     of the kb34 statement draft, sections 4-5; the window-sum
     certificate 322/500 over k < 150 (piu_zz_pnt_winsum); the
     integer-certificate budget with D = 10^4 (kb33, section 6.3).
   Constructivity: statement faces Set-carried (QleT', BidT, Bdiv);
     definitions are transparent; symbolic faces close by cross-multiplied
     conversion with nia/lia; the theta slot is a universally quantified
     premise generalized at section close, no global assumption.
   Build: coqc -native-compiler no -q -Q <certified vo tree> ""
     -Q <kb35 born tree> "" -Q <this dir> "" piu_zz_pnt_phi.v
     (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import QArith ZArith Arith PArith Lia Bool.
From Stdlib Require Import Znumtheory.
Require Import S03_QExp.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_pnt_window.
Require Import piu_zz_pnt_winsum.
Require Import piu_zz_pnt_qexp.
Require Import piu_zz_pnt_lcmpow.

Local Open Scope Q_scope.

(* ================= Section 1. Order helpers on QleT' ================= *)

Lemma zz_pnt_phi_qleT_trans : forall a b c : Q,
  QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c H1 H2. destruct H1 as [H1]. destruct H2 as [H2].
  apply qleT_intro. apply (Qle_trans a b c H1 H2).
Qed.

Lemma zz_pnt_phi_qleT_plus : forall a b c d : Q,
  QleT' a b -> QleT' c d -> QleT' (a + c) (b + d).
Proof.
  intros a b c d H1 H2. destruct H1 as [H1]. destruct H2 as [H2].
  apply qleT_intro. apply (Qplus_le_compat a b c d H1 H2).
Qed.

Lemma zz_pnt_phi_qmult_le_compat_r : forall x y z : Q,
  QleT' x y -> QleT' (Qmake 0 1) z -> QleT' (x * z) (y * z).
Proof.
  intros x y z H Hz. destruct H as [H]. destruct Hz as [Hz].
  apply qleT_intro. apply (Qmult_le_compat_r x y z H Hz).
Qed.

Lemma zz_pnt_phi_qleT_eq_l : forall a b c : Q,
  a == b -> QleT' a c -> QleT' b c.
Proof.
  intros a b c Hab H. destruct H as [H]. apply qleT_intro.
  rewrite <- Hab. exact H.
Qed.

Lemma zz_pnt_phi_qleT_eq_r : forall a b c : Q,
  QleT' a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc. destruct H as [H]. apply qleT_intro.
  rewrite Hbc in H. exact H.
Qed.

(* Two-sided product compatibility: the right-factor comm dance covers
   the missing left-compat lemma. *)
Lemma zz_pnt_phi_qmult_le_compat : forall x y u v : Q,
  QleT' x y -> QleT' u v -> QleT' (Qmake 0 1) u ->
  QleT' (Qmake 0 1) v -> QleT' (Qmake 0 1) y ->
  QleT' (x * u) (y * v).
Proof.
  intros x y u v Hxy Huv Hu Hv Hy.
  apply zz_pnt_phi_qleT_trans with (y * u).
  - apply zz_pnt_phi_qmult_le_compat_r; [exact Hxy | exact Hu].
  - apply zz_pnt_phi_qleT_eq_r with (b := v * y) (c := y * v).
    + apply zz_pnt_phi_qleT_eq_l with (a := u * y).
      * unfold Qeq. apply Qmult_comm.
      * apply zz_pnt_phi_qmult_le_compat_r; [exact Huv | exact Hy].
    + unfold Qeq. apply Qmult_comm.
Qed.

Lemma zz_pnt_phi_zq_pos : forall w : Z,
  (0 < w)%Z -> QleT' (Qmake 0 1) (zq w).
Proof.
  intro w. intro Hw. apply qleT_intro. unfold Qle, zq. cbn. lia.
Qed.

(* ================= Section 2. Window endpoints and membership ================= *)

Definition zz_pnt_phi_x0 : nat := 664 * 1000 * 1000.

(* Numerical anchor for the base point: the constant exceeds 400 * 1000.
   The product-of-small-literals representation keeps every numeral below
   the abstraction threshold (no of_num_uint abstraction: 664, 1000 are
   plain literals), so the ordering and all its downstream transfers stay
   within linear arithmetic with the magnitude fully visible. *)
Lemma zz_pnt_x0_big : (400 * 1000 < zz_pnt_phi_x0)%nat.
Proof. unfold zz_pnt_phi_x0. lia. Qed.

Definition zz_pnt_bk (n k : nat) : nat := 2 * n / (2 * k + 1)%nat.

Definition zz_pnt_ak (n k : nat) : nat := 3 * n / (3 * k + 2)%nat.

(* Window hit: the two multiplication-form inequalities of window k,
   equivalent to a_k < q <= b_k for the integer endpoints above. *)
Definition zz_pnt_winhit (n k q : nat) : bool :=
  andb (Nat.leb (q * (2 * k + 1)%nat) (2 * n)%nat)
       (Nat.ltb (3 * n)%nat (q * (3 * k + 2)%nat)).

Lemma zz_pnt_winhit_bounds : forall n k q : nat,
  zz_pnt_winhit n k q = true ->
  prod (BidT (Nat.ltb (zz_pnt_ak n k) q))
       (BidT (Nat.leb q (zz_pnt_bk n k))).
Proof.
  intros n k q Hhit.
  apply Bool.andb_true_iff in Hhit. destruct Hhit as [Hlo Hhi].
  apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
  split.
  - apply BidT_intro. apply Nat.ltb_lt. unfold zz_pnt_ak.
    apply Nat.div_lt_upper_bound; lia.
  - apply BidT_intro. apply Nat.leb_le. unfold zz_pnt_bk.
    apply Nat.div_le_lower_bound; lia.
Qed.

(* A prime hitting window k (k below the kept budget 150) belongs to
   the certified window set: zz_in_Pn n q holds. *)
Lemma zz_pnt_winhit_in_Pn : forall n k q : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (k < 150)%nat ->
  zz_pnt_winhit n k q = true -> zz_primeb q = true ->
  BidT (zz_in_Pn n q).
Proof.
  intros n k q Hn Hk Hhit Hq.
  pose proof zz_pnt_x0_big as Hbig.
  assert (Hn2 : (400 * 1000 < n)%nat) by lia.
  unfold zz_pnt_winhit in Hhit.
  apply Bool.andb_true_iff in Hhit. destruct Hhit as [Hlo Hhi].
  apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
  assert (Hq5 : (5 < q)%nat).
  { assert (Hk149 : (3 * k + 2 <= 449)%nat) by lia.
    assert (Hcross : (3 * n < q * 449)%nat)
      by (apply (Nat.lt_le_trans (3 * n) (q * (3 * k + 2)) (q * 449));
          [exact Hhi | apply Nat.mul_le_mono;
          [apply Nat.le_refl | exact Hk149]]).
    lia. }
  assert (Hsqrt : (3 * n < q * q)%nat)
    by (apply (zz_pnt_window_above_sqrt n 149 k q); lia).
  apply (zz_pnt_window_subset n k q).
  - apply BidT_intro. exact Hq.
  - exact Hq5.
  - exact Hsqrt.
  - exact Hlo.
  - exact Hhi.
Qed.

(* Width fold: the Z-valued sum of the window widths (b_k - a_k),
   peeled from the front so that both folds index-align. *)
Fixpoint zz_pnt_width_part (n s K : nat) : Z :=
  match K with
  | O => 0%Z
  | S K' => (Z.of_nat (zz_pnt_bk n s) - Z.of_nat (zz_pnt_ak n s))%Z
            + zz_pnt_width_part n (S s) K'
  end.

(* Per-window face: one window keeps at least n*t_k - 2, the unit
   rounding losses of the two integer endpoints booked as 2. *)
Lemma zz_pnt_width_window : forall n s : nat,
  (zz_pnt_phi_x0 <= n)%nat ->
  QleT' (Qminus (Qmult (zq (Z.of_nat n)) (zz_pnt_win_term s)) (Qmake 2 1))
        (zq (Z.of_nat (zz_pnt_bk n s) - Z.of_nat (zz_pnt_ak n s))).
Proof.
  intros n s Hn. unfold zz_pnt_bk, zz_pnt_ak.
  pose proof (Nat.div_mod_eq (2 * n) (2 * s + 1)%nat) as Hdm1.
  assert (Hne1 : (2 * s + 1 <> 0)%nat) by lia.
  pose proof (Nat.mod_upper_bound (2 * n) (2 * s + 1)%nat Hne1) as Hmb1.
  pose proof (Nat.div_mod_eq (3 * n) (3 * s + 2)%nat) as Hdm2.
  assert (Hne2 : (3 * s + 2 <> 0)%nat) by lia.
  pose proof (Nat.mod_upper_bound (3 * n) (3 * s + 2)%nat Hne2) as Hmb2.
  assert (HB : (Z.of_nat (2 * s + 1) * Z.of_nat (2 * n / (2 * s + 1)%nat)
                >= Z.of_nat (2 * n) - Z.of_nat (2 * s + 1))%Z) by lia.
  assert (HA : (Z.of_nat (3 * s + 2) * Z.of_nat (3 * n / (3 * s + 2)%nat)
                <= Z.of_nat (3 * n))%Z) by lia.
  assert (HBm : (Z.of_nat (3 * s + 2)
                 * (Z.of_nat (2 * s + 1) * Z.of_nat (2 * n / (2 * s + 1)%nat))
                 >= Z.of_nat (3 * s + 2)
                    * (Z.of_nat (2 * n) - Z.of_nat (2 * s + 1)))%Z) by nia.
  assert (HAm : (Z.of_nat (2 * s + 1)
                 * (Z.of_nat (3 * s + 2) * Z.of_nat (3 * n / (3 * s + 2)%nat))
                 <= Z.of_nat (2 * s + 1) * Z.of_nat (3 * n))%Z) by nia.
  assert (Hrel : (Z.of_nat (2 * s + 1) * Z.of_nat (3 * s + 2)
                  * (Z.of_nat (2 * n / (2 * s + 1)%nat)
                     - Z.of_nat (3 * n / (3 * s + 2)%nat))
                  >= Z.of_nat n
                     - 2 * (Z.of_nat (2 * s + 1) * Z.of_nat (3 * s + 2)))%Z)
    by nia.
  apply qleT_intro. unfold Qle, zq.
  cbn [Qnum Qden Qmult Qminus Qopp Qplus zz_pnt_win_term].
  rewrite Pos.mul_1_l, Pos.mul_1_r. rewrite <- (positive_nat_Z (zz_pnt_win_den s)). rewrite zz_pnt_win_den_nat.
  nia.
Qed.

Lemma zz_pnt_width_lb_gen : forall K n s : nat,
  (zz_pnt_phi_x0 <= n)%nat ->
  QleT' (Qminus (Qmult (zq (Z.of_nat n)) (zz_pnt_winsum_part s K))
                (zq (2 * Z.of_nat K)))
        (zq (zz_pnt_width_part n s K)).
Proof.
  induction K as [|K IH]; intros n s Hn.
  - apply qleT_intro. unfold Qle, zq.
    cbn [zz_pnt_winsum_part zz_pnt_width_part Qnum Qden Qmult Qplus Qminus Qopp].
    lia.
  - apply zz_pnt_phi_qleT_eq_r
      with (b := Qplus (zq (Z.of_nat (zz_pnt_bk n s) - Z.of_nat (zz_pnt_ak n s)))
                       (zq (zz_pnt_width_part n (S s) K))).
    + apply zz_pnt_phi_qleT_eq_l with
        (Qplus (Qminus (Qmult (zq (Z.of_nat n)) (zz_pnt_win_term s)) (Qmake 2 1))
               (Qminus (Qmult (zq (Z.of_nat n)) (zz_pnt_winsum_part (S s) K))
                       (zq (2 * Z.of_nat K)))).
      * unfold zq, Qeq.
        cbn [Qnum Qden Qmult Qminus Qplus Qopp zz_pnt_winsum_part].
        repeat rewrite Pos.mul_1_l; repeat rewrite Pos.mul_1_r;
          repeat rewrite Pos2Z.inj_mul; repeat rewrite Nat2Z.inj_succ.
        ring.
      * apply zz_pnt_phi_qleT_plus.
        -- apply zz_pnt_width_window. exact Hn.
        -- apply IH. exact Hn.
    + unfold zq, Qeq.
      cbn [Qnum Qden Qplus Qmult Qopp zz_pnt_width_part].
      repeat rewrite Pos.mul_1_l; repeat rewrite Pos.mul_1_r;
        repeat rewrite Pos2Z.inj_mul; repeat rewrite Nat2Z.inj_succ.
      ring.
Qed.

(* The K = 150 width certificate: n*(322/500) - 302 <= total width,
   consuming the born window-sum lower bound (node B2.3a). *)
Lemma zz_pnt_width_150_lb : forall n : nat,
  (zz_pnt_phi_x0 <= n)%nat ->
  QleT' (Qminus (Qmult (zq (Z.of_nat n)) (Qmake 322 500)) (Qmake 302 1))
        (zq (zz_pnt_width_part n 0 150)).
Proof.
  intros n Hn.
  pose proof zz_pnt_winsum_150_lb as Hw.
  apply BidT_elim in Hw.
  pose proof zz_pnt_x0_big as Hbig.
  assert (Hpart : (Qmake 322 500) <= zz_pnt_winsum_part 0 150)
    by (apply (proj1 (Qle_bool_iff (Qmake 322 500)
                     (zz_pnt_winsum_part 0 150))); exact Hw).
  assert (Hn0 : QleT' (Qmake 0 1) (zq (Z.of_nat n)))
    by (apply zz_pnt_phi_zq_pos; lia).
  apply zz_pnt_phi_qleT_trans with
    (Qminus (Qmult (zq (Z.of_nat n)) (zz_pnt_winsum_part 0 150))
            (zq (2 * Z.of_nat 150))).
  - apply zz_pnt_phi_qleT_plus.
    + apply zz_pnt_phi_qleT_eq_l
        with (a := Qmult (Qmake 322 500) (zq (Z.of_nat n))).
      * apply Qmult_comm.
      * apply zz_pnt_phi_qleT_eq_r
          with (b := Qmult (zz_pnt_winsum_part 0 150) (zq (Z.of_nat n))).
        -- apply zz_pnt_phi_qmult_le_compat_r.
           ++ apply qleT_intro. exact Hpart.
           ++ exact Hn0.
        -- apply Qmult_comm.
    + apply qleT_intro. unfold Qle, zq. cbn [Qnum Qden Qopp]. lia.
  - apply zz_pnt_width_lb_gen. exact Hn.
Qed.

(* ================= Section 3. Window products and coprimality ================= *)

(* Product over [1..K] of the primes of the window (a, b]. *)
Fixpoint zz_pnt_wprod (n a b K : nat) : Z :=
  match K with
  | O => 1%Z
  | S K' =>
      if andb (andb (Nat.ltb a (S K')) (Nat.leb (S K') b))
              (zz_primeb (S K'))
      then zz_pnt_wprod n a b K' * Z.of_nat (S K')
      else zz_pnt_wprod n a b K'
  end.

Lemma zz_pnt_wprod_pos : forall n a b K : nat,
  (0 < zz_pnt_wprod n a b K)%Z.
Proof.
  intros n a b K. induction K as [|K IH].
  - cbn [zz_pnt_wprod]. lia.
  - cbn [zz_pnt_wprod].
    destruct (andb (andb (Nat.ltb a (S K)) (Nat.leb (S K) b))
                   (zz_primeb (S K)));
      nia.
Qed.

(* Right-multiplicative transfer for Bdiv. *)
Lemma zz_pnt_phi_bdiv_mul_cancel_r : forall a b c : Z,
  Bdiv a b -> Bdiv (a * c) (b * c).
Proof.
  intros a b c H. destruct H as [z Hz]. apply Bid_elim in Hz.
  exists z. apply Bid_intro.
  replace (a * c * z)%Z with (a * z * c)%Z by ring.
  rewrite Hz. reflexivity.
Qed.

(* Every window prime (kept budget 150) enters the certified fold
   zz_prodf: the window product divides it, no coprimality needed. *)
Lemma zz_pnt_wprod_bdiv_prodf : forall n k K : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (k < 150)%nat ->
  Bdiv (zz_pnt_wprod n (zz_pnt_ak n k) (zz_pnt_bk n k) K) (zz_prodf n K).
Proof.
  intros n k K Hn Hk. induction K as [|K IH].
  - exists 1%Z. apply Bid_intro. cbn [zz_pnt_wprod zz_prodf]. ring.
  - cbn [zz_pnt_wprod zz_prodf].
    destruct (andb (andb (Nat.ltb (zz_pnt_ak n k) (S K))
                         (Nat.leb (S K) (zz_pnt_bk n k)))
                   (zz_primeb (S K))) eqn:Esel.
    + assert (Hin : zz_in_Pn n (S K) = true).
      { apply Bool.andb_true_iff in Esel. destruct Esel as [E12 Ep].
        apply Bool.andb_true_iff in E12. destruct E12 as [Elo Ehi].
        apply Nat.ltb_lt in Elo. unfold zz_pnt_ak in Elo.
        apply Nat.leb_le in Ehi. unfold zz_pnt_bk in Ehi.
        apply BidT_elim. apply (zz_pnt_winhit_in_Pn n k (S K)); try assumption.
        - unfold zz_pnt_winhit. apply Bool.andb_true_iff. split.
          + apply Nat.leb_le. unfold zz_pnt_bk.
            pose proof (Nat.div_mod_eq (2 * n) (2 * k + 1)%nat).
            assert (Hne : (2 * k + 1 <> 0)%nat) by lia.
            pose proof (Nat.mod_upper_bound (2 * n) (2 * k + 1)%nat Hne).
            nia.
          + apply Nat.ltb_lt. unfold zz_pnt_ak.
            pose proof (Nat.div_mod_eq (3 * n) (3 * k + 2)%nat).
            assert (Hne : (3 * k + 2 <> 0)%nat) by lia.
            pose proof (Nat.mod_upper_bound (3 * n) (3 * k + 2)%nat Hne).
            nia. }
      rewrite Hin. apply zz_pnt_phi_bdiv_mul_cancel_r. exact IH.
    + destruct (zz_in_Pn n (S K)) eqn:E.
      * apply zz_bdiv_mul_absorb_r. exact IH.
      * exact IH.
Qed.

(* Disjointness: the later window lies strictly below the earlier one. *)
Lemma zz_pnt_win_disj : forall n i j : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (i < j)%nat -> (j < 150)%nat ->
  (zz_pnt_bk n j < zz_pnt_ak n i)%nat.
Proof.
  intros n i j Hn Hij Hj.
  pose proof zz_pnt_x0_big as Hbig.
  assert (Hn2 : (400 * 1000 < n)%nat) by lia.
  unfold zz_pnt_bk, zz_pnt_ak.
  apply Nat.div_lt_upper_bound; [lia|].
  pose proof (Nat.div_mod_eq (3 * n) (3 * i + 2)%nat) as Hdm.
  assert (Hne : (3 * i + 2 <> 0)%nat) by lia.
  pose proof (Nat.mod_upper_bound (3 * n) (3 * i + 2)%nat Hne) as Hmb.
  assert (Hmon : ((2 * j + 1) * (3 * n / (3 * i + 2))
                  >= (2 * i + 3) * (3 * n / (3 * i + 2)))%nat)
    by (apply Nat.mul_le_mono; lia).
  assert (Hkey : (2 * n * (3 * i + 2)
                  < (2 * i + 3) * (3 * n) - (2 * i + 3) * (3 * i + 1))%nat)
    by nia.
  assert (Hlower : (2 * n < (2 * i + 3) * (3 * n / (3 * i + 2)))%nat).
  { destruct (Nat.le_gt_cases
                ((2 * i + 3) * (3 * n / (3 * i + 2))) (2 * n)) as [Hc | Hc];
      [|lia].
    exfalso. nia. }
  nia.
Qed.

(* Bezout composition on the shared right factor. *)
Lemma zz_pnt_phi_rel_prime_mul_r : forall a b c : Z,
  rel_prime a c -> rel_prime b c -> rel_prime (a * b) c.
Proof.
  intros a b c H1 H2.
  apply bezout_rel_prime.
  destruct (rel_prime_bezout a c H1) as [u v Hu].
  destruct (rel_prime_bezout b c H2) as [u' v' Hv].
  apply Bezout_intro with (u := (u * u')%Z)
                          (v := (a * v' * u + b * v * u' + c * v * v')%Z).
  transitivity (((u * a + v * c) * (u' * b + v' * c))%Z).
  - ring.
  - rewrite Hu. rewrite Hv. reflexivity.
Qed.

(* A prime distinct from every member of window j is Bezout-coprime to
   the whole window-j product. *)
Lemma zz_pnt_wprod_rel_prime_out : forall n j K q : nat,
  zz_primeb q = true ->
  (forall m : nat,
     (zz_pnt_ak n j < m)%nat -> (m <= zz_pnt_bk n j)%nat ->
     zz_primeb m = true -> (m <> q)%nat) ->
  rel_prime (Z.of_nat q)
            (zz_pnt_wprod n (zz_pnt_ak n j) (zz_pnt_bk n j) K).
Proof.
  intros n j K q Hq Hout. induction K as [|K IH].
  - apply rel_prime_sym. apply rel_prime_1.
  - cbn [zz_pnt_wprod].
    destruct (andb (andb (Nat.ltb (zz_pnt_ak n j) (S K))
                         (Nat.leb (S K) (zz_pnt_bk n j)))
                   (zz_primeb (S K))) eqn:Esel.
    + apply Bool.andb_true_iff in Esel. destruct Esel as [E12 Eb].
      apply Bool.andb_true_iff in E12. destruct E12 as [E1 E2].
      apply rel_prime_sym. apply zz_pnt_phi_rel_prime_mul_r.
      * apply rel_prime_sym. exact IH.
      * apply zz_rel_prime_prime_pair.
        -- exact Eb.
        -- exact Hq.
        -- apply Nat.ltb_lt in E1. apply Nat.leb_le in E2.
           apply (Hout (S K)); assumption.
    + exact IH.
Qed.

(* Pairwise coprimality of the window products. *)
Lemma zz_pnt_wprod_pair_rel_prime : forall n i j K : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (i < j)%nat -> (j < 150)%nat ->
  rel_prime (zz_pnt_wprod n (zz_pnt_ak n i) (zz_pnt_bk n i) K)
            (zz_pnt_wprod n (zz_pnt_ak n j) (zz_pnt_bk n j) K).
Proof.
  intros n i j K Hn Hij Hj. induction K as [|K IH].
  - apply rel_prime_1.
  - cbn [zz_pnt_wprod].
    destruct (andb (andb (Nat.ltb (zz_pnt_ak n i) (S K))
                         (Nat.leb (S K) (zz_pnt_bk n i)))
                   (zz_primeb (S K))) eqn:Ei;
    destruct (andb (andb (Nat.ltb (zz_pnt_ak n j) (S K))
                         (Nat.leb (S K) (zz_pnt_bk n j)))
                   (zz_primeb (S K))) eqn:Ej.
    + exfalso.
      pose proof (zz_pnt_win_disj n i j Hn Hij Hj) as Hdis.
      apply Bool.andb_true_iff in Ei. destruct Ei as [Ei12 _].
      apply Bool.andb_true_iff in Ei12. destruct Ei12 as [Ei1 _].
      apply Nat.ltb_lt in Ei1.
      apply Bool.andb_true_iff in Ej. destruct Ej as [Ej12 _].
      apply Bool.andb_true_iff in Ej12. destruct Ej12 as [_ Ej2].
      apply Nat.leb_le in Ej2.
      lia.
    + pose proof (zz_pnt_win_disj n i j Hn Hij Hj) as Hdis.
      apply Bool.andb_true_iff in Ei. destruct Ei as [Ei12 Ei2].
      apply Bool.andb_true_iff in Ei12. destruct Ei12 as [Ei1 _].
      apply Nat.ltb_lt in Ei1.
      apply zz_pnt_phi_rel_prime_mul_r.
      * exact IH.
      * apply (zz_pnt_wprod_rel_prime_out n j K (S K)).
        -- exact Ei2.
        -- intros m Hm1 Hm2 Hm3. lia.
    + pose proof (zz_pnt_win_disj n i j Hn Hij Hj) as Hdis.
      apply Bool.andb_true_iff in Ej. destruct Ej as [Ej12 Ej2].
      apply Bool.andb_true_iff in Ej12. destruct Ej12 as [Ej1 Ej3].
      apply Nat.ltb_lt in Ej1. apply Nat.leb_le in Ej3.
      apply rel_prime_sym. apply zz_pnt_phi_rel_prime_mul_r.
      * apply rel_prime_sym. exact IH.
      * apply (zz_pnt_wprod_rel_prime_out n i K (S K)).
        -- exact Ej2.
        -- intros m Hm1 Hm2 Hm3. lia.
    + exact IH.
Qed.

(* Fold of the window products over the kept budget. *)
Fixpoint zz_pnt_wwfold (n K : nat) : Z :=
  match K with
  | O => 1%Z
  | S K' => zz_pnt_wwfold n K'
            * zz_pnt_wprod n (zz_pnt_ak n K') (zz_pnt_bk n K') (2 * n)%nat
  end.

Lemma zz_pnt_wwfold_pos : forall n K : nat,
  (0 < zz_pnt_wwfold n K)%Z.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_pnt_wwfold]. lia.
  - cbn [zz_pnt_wwfold].
    pose proof (zz_pnt_wprod_pos n (zz_pnt_ak n K) (zz_pnt_bk n K)
                         (2 * n)%nat). nia.
Qed.

Lemma zz_pnt_phi_prodf_pos : forall n K : nat, (0 < zz_prodf n K)%Z.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. lia.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)); nia.
Qed.

Lemma zz_pnt_wwfold_rel_prime_last : forall n K : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (K <= 149)%nat ->
  rel_prime (zz_pnt_wwfold n K)
            (zz_pnt_wprod n (zz_pnt_ak n K) (zz_pnt_bk n K) (2 * n)%nat).
Proof.
  intros n K Hn.
  assert (Hgen : forall (K0 j : nat),
            (K0 <= 149)%nat -> (K0 < j)%nat -> (j <= 149)%nat ->
            rel_prime (zz_pnt_wwfold n K0)
                      (zz_pnt_wprod n (zz_pnt_ak n j) (zz_pnt_bk n j)
                                     (2 * n)%nat)).
  { induction K0 as [|K0 IH]; intros j HK0 Hlt Hj.
    - cbn [zz_pnt_wwfold]. apply rel_prime_1.
    - cbn [zz_pnt_wwfold]. apply zz_pnt_phi_rel_prime_mul_r.
      + apply IH; lia.
      + apply (zz_pnt_wprod_pair_rel_prime n K0 j); lia. }
  induction K as [|K IH]; intros HK.
  - apply rel_prime_1.
  - cbn [zz_pnt_wwfold]. apply zz_pnt_phi_rel_prime_mul_r.
    + apply Hgen; lia.
    + apply (zz_pnt_wprod_pair_rel_prime n K (S K)); lia.
Qed.

(* The window-product fold divides Phi_n: Gauss combination along the
   coprime chain. *)
Theorem zz_pnt_wwfold_bdiv : forall n K : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (K <= 150)%nat ->
  Bdiv (zz_pnt_wwfold n K) (zz_Phi n).
Proof.
  intros n K Hn. induction K as [|K IH]; intros HK.
  - exists (zz_Phi n). apply Bid_intro.
    cbn [zz_pnt_wwfold]. ring.
  - cbn [zz_pnt_wwfold]. apply zz_bdiv_coprime_combine.
    + apply zz_pnt_wwfold_pos.
    + exact (IH ltac:(lia)).
    + apply (zz_pnt_wprod_bdiv_prodf n K (2 * n)%nat Hn); lia.
    + apply (proj2 (Zgcd_1_rel_prime _ _)).
      apply zz_pnt_wwfold_rel_prime_last; lia.
Qed.

(* ================= Section 4. Assembly with the theta slot ================= *)

(* Content numerator of window k: (1 - 1/6600)(b - a) - (1/6600)(b + a)
   - 2 over the common denominator 6600. *)
Definition zz_pnt_win_cnum (n k : nat) : Z :=
  (66 * 100 - 1) * (Z.of_nat (zz_pnt_bk n k) - Z.of_nat (zz_pnt_ak n k))
    - (Z.of_nat (zz_pnt_bk n k) + Z.of_nat (zz_pnt_ak n k))
    - 2 * (66 * 100).

Definition zz_pnt_win_c (n k : nat) : Q :=
  Qmake (zz_pnt_win_cnum n k) (66 * 100).

Lemma zz_pnt_phi_win_c_nonneg : forall n k : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (k < 150)%nat ->
  QleT' (Qmake 0 1) (zz_pnt_win_c n k).
Proof.
  intros n k Hn Hk. unfold zz_pnt_bk, zz_pnt_ak.
  unfold zz_pnt_phi_x0 in Hn.
  pose proof zz_pnt_x0_big as Hbig.
  assert (Hn2 : (400 * 1000 < n)%nat) by lia.
  pose proof (Nat.div_mod_eq (2 * n) (2 * k + 1)%nat) as Hdm1.
  assert (Hne1 : (2 * k + 1 <> 0)%nat) by lia.
  pose proof (Nat.mod_upper_bound (2 * n) (2 * k + 1)%nat Hne1) as Hmb1.
  pose proof (Nat.div_mod_eq (3 * n) (3 * k + 2)%nat) as Hdm2.
  assert (Hne2 : (3 * k + 2 <> 0)%nat) by lia.
  pose proof (Nat.mod_upper_bound (3 * n) (3 * k + 2)%nat Hne2) as Hmb2.
  assert (Hb1 : (Z.of_nat (2 * k + 1) * Z.of_nat (2 * n / (2 * k + 1)%nat)
                 <= Z.of_nat (2 * n))%Z) by lia.
  assert (Hb2 : (Z.of_nat (2 * n)
                 <= Z.of_nat (2 * k + 1) * Z.of_nat (2 * n / (2 * k + 1)%nat)
                    + Z.of_nat (2 * k + 1))%Z) by lia.
  assert (Ha1 : (Z.of_nat (3 * k + 2) * Z.of_nat (3 * n / (3 * k + 2)%nat)
                 <= Z.of_nat (3 * n))%Z) by lia.
  assert (Ha2 : (Z.of_nat (3 * n)
                 <= Z.of_nat (3 * k + 2) * Z.of_nat (3 * n / (3 * k + 2)%nat)
                    + Z.of_nat (3 * k + 2))%Z) by lia.
  assert (HD : (0 < Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2))%Z) by lia.
  assert (Hbd : (Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2)
                 * Z.of_nat (2 * n / (2 * k + 1)%nat)
                 >= Z.of_nat (2 * n) * Z.of_nat (3 * k + 2)
                    - Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2))%Z) by nia.
  assert (Hbu : (Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2)
                 * Z.of_nat (2 * n / (2 * k + 1)%nat)
                 <= Z.of_nat (2 * n) * Z.of_nat (3 * k + 2))%Z) by nia.
  assert (Had : (Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2)
                 * Z.of_nat (3 * n / (3 * k + 2)%nat)
                 <= Z.of_nat (3 * n) * Z.of_nat (2 * k + 1))%Z) by nia.
  apply qleT_intro. unfold Qle, zz_pnt_win_c, zz_pnt_win_cnum.
  cbn [Qnum Qden].
  assert (HAub : (Z.of_nat (2 * k + 1) <= 301)%Z) by lia.
  assert (HBub : (Z.of_nat (3 * k + 2) <= 452)%Z) by lia.
  assert (HAlo : (1 <= Z.of_nat (2 * k + 1))%Z) by lia.
  assert (HBlo : (1 <= Z.of_nat (3 * k + 2))%Z) by lia.
  assert (HC : (4804 <= (2 * (66 * 100) - 4) * Z.of_nat (3 * k + 2)
                        - (3 * (66 * 100)) * Z.of_nat (2 * k + 1))%Z) by lia.
  unfold zz_pnt_bk, zz_pnt_ak in *.
  clear Hbig Hdm1 Hmb1 Hne1 Hdm2 Hmb2 Hne2 Hb1 Hb2 Ha1 Ha2 Hbu Hn2.
  replace ((66 * 100 - 1) * (Z.of_nat (2 * n / (2 * k + 1)%nat)
            - Z.of_nat (3 * n / (3 * k + 2)%nat))
            - (Z.of_nat (2 * n / (2 * k + 1)%nat)
               + Z.of_nat (3 * n / (3 * k + 2)%nat)) - 2 * (66 * 100))%Z
    with ((66 * 100 - 2) * Z.of_nat (2 * n / (2 * k + 1)%nat)
          - (66 * 100) * Z.of_nat (3 * n / (3 * k + 2)%nat)
          - 2 * (66 * 100))%Z by ring.
  remember (Z.of_nat (2 * k + 1) * Z.of_nat (3 * k + 2))%Z as T eqn:HT.
  remember ((66 * 100 - 2) * Z.of_nat (2 * n / (2 * k + 1)%nat)
            - (66 * 100) * Z.of_nat (3 * n / (3 * k + 2)%nat)
            - 2 * (66 * 100))%Z as W eqn:HW.
  assert (HP : (0 <= Z.of_nat n * ((2 * (66 * 100) - 4) * Z.of_nat (3 * k + 2)
                                   - (3 * (66 * 100)) * Z.of_nat (2 * k + 1))
                - (3 * (66 * 100) - 2) * T)%Z) by nia.
  assert (Hkey : (T * W >= Z.of_nat n * ((2 * (66 * 100) - 4)
                                          * Z.of_nat (3 * k + 2)
                                         - (3 * (66 * 100))
                                           * Z.of_nat (2 * k + 1))
                  - (3 * (66 * 100) - 2) * T)%Z) by nia.
  nia.
Qed.

Lemma zz_pnt_phi_exp_nonneg : forall (J : nat) (x : Q),
  QleT' (Qmake 0 1) x -> QleT' (Qmake 0 1) (exp_partial J x).
Proof.
  intros J x Hx. induction J as [|J IH].
  - apply qleT_intro. cbn [exp_partial]. unfold Qle. cbn. lia.
  - cbn [exp_partial]. apply qleT_intro.
    apply (Qle_trans (Qmake 0 1) (Qmake 0 1 + Qmake 0 1)
                     (exp_partial J x + q_pow x (S J) / q_fact (S J))).
    + unfold Qle. cbn. lia.
    + apply (Qplus_le_compat (Qmake 0 1) (exp_partial J x) (Qmake 0 1)
               (q_pow x (S J) / q_fact (S J))).
      * destruct IH as [IH]. exact IH.
      * apply q_pow_fact_nonneg. destruct Hx as [Hx0]. exact Hx0.
Qed.

Section PhiAssembly.

(* The window-theta content slot: each kept window carries enough
   exponential content below its prime product. *)
Variable h_pnt_win_theta : forall (n k J : nat),
  (zz_pnt_phi_x0 <= n)%nat -> (k < 150)%nat ->
  QleT' (exp_partial J (zz_pnt_win_c n k))
        (zq (zz_pnt_wprod n (zz_pnt_ak n k) (zz_pnt_bk n k) (2 * n)%nat)).

Fixpoint zz_pnt_lbprod (n J K : nat) : Q :=
  match K with
  | O => Qmake 1 1
  | S K' => zz_pnt_lbprod n J K' * exp_partial J (zz_pnt_win_c n K')
  end.

Lemma zz_pnt_lbprod_le_wwfold : forall n J K : nat,
  (zz_pnt_phi_x0 <= n)%nat -> (K <= 150)%nat ->
  QleT' (zz_pnt_lbprod n J K) (zq (zz_pnt_wwfold n K)).
Proof.
  intros n J K Hn. induction K as [|K IH]; intros HK.
  - cbn [zz_pnt_lbprod]. apply qleT_intro. unfold Qle, zq. cbn. lia.
  - cbn [zz_pnt_lbprod zz_pnt_wwfold].
    pose proof (h_pnt_win_theta n K J Hn ltac:(lia)) as Hslot.
    pose proof (zz_pnt_phi_exp_nonneg J (zz_pnt_win_c n K)
                (zz_pnt_phi_win_c_nonneg n K Hn ltac:(lia))) as Hexp0.
    pose proof (zz_pnt_phi_zq_pos
                (zz_pnt_wprod n (zz_pnt_ak n K) (zz_pnt_bk n K) (2 * n)%nat)
                (zz_pnt_wprod_pos n (zz_pnt_ak n K) (zz_pnt_bk n K)
                                   (2 * n)%nat)) as Hw0.
    assert (Hwy : QleT' (Qmake 0 1) (zq (zz_pnt_wwfold n K))).
    { apply zz_pnt_phi_zq_pos. apply zz_pnt_wwfold_pos. }
    replace (zq (zz_pnt_wwfold n K
                 * zz_pnt_wprod n (zz_pnt_ak n K) (zz_pnt_bk n K) (2 * n)%nat))
      with (zq (zz_pnt_wwfold n K)
              * zq (zz_pnt_wprod n (zz_pnt_ak n K) (zz_pnt_bk n K)
                                   (2 * n)%nat))
      by (unfold zq; cbn [Qnum Qden Qmult]; reflexivity).
    apply zz_pnt_phi_qmult_le_compat;
      [exact (IH ltac:(lia)) | exact Hslot | exact Hexp0 | exact Hw0
      | exact Hwy].
Qed.

(* The assembled lower bound: the theta content of the 150 kept windows
   dominates Phi_n through the dividing window-product fold. *)
Theorem zz_pnt_phi_lower : forall n J : nat,
  (zz_pnt_phi_x0 <= n)%nat ->
  QleT' (zz_pnt_lbprod n J 150) (zq (zz_Phi n)).
Proof.
  intros n J Hn.
  apply zz_pnt_phi_qleT_trans with (zq (zz_pnt_wwfold n 150)).
  - apply zz_pnt_lbprod_le_wwfold; [exact Hn | lia].
  - destruct (zz_pnt_wwfold_bdiv n 150 Hn ltac:(lia)) as [z Hz].
    apply Bid_elim in Hz.
    apply qleT_intro. unfold Qle, zq. cbn [Qnum Qden].
    assert (Hwp : (0 < zz_pnt_wwfold n 150)%Z)
      by (apply zz_pnt_wwfold_pos).
    assert (HPh : (0 < zz_Phi n)%Z) by (apply zz_pnt_phi_prodf_pos).
    assert (Hzp : (0 < z)%Z) by nia.
    nia.
Qed.

End PhiAssembly.

(* ================= Section 5. Certification face ================= *)

Print Assumptions zz_pnt_width_150_lb.
Print Assumptions zz_pnt_wprod_bdiv_prodf.
Print Assumptions zz_pnt_wwfold_bdiv.
Print Assumptions zz_pnt_phi_lower.

From Stdlib Require Import Extraction.
Separate Extraction zz_pnt_bk zz_pnt_ak zz_pnt_winhit zz_pnt_wprod
  zz_pnt_wwfold zz_pnt_win_c zz_pnt_lbprod zz_pnt_winhit_bounds
  zz_pnt_winhit_in_Pn zz_pnt_width_150_lb zz_pnt_wwfold_bdiv
  zz_pnt_phi_lower.
