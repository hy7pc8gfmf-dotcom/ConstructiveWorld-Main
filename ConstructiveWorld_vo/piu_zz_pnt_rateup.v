(* ==========================================================================
   Module: piu_zz_pnt_rateup
   Mission: assembly spine for the effective-PNT consumption chain — the
     eventual upper rate face for L_n = lcm(1..4n)/Phi_n. From the born
     chain faces (Phi*L = lcm, lcm | Psi, prodf positivity) it proves
     L_n <= Psi(4n)/Phi_n rationally, then assembles the final face
       { N0 : nat & forall n >= N0, QleT' (zq (zz_L n)) ((29#1)^n) }
     from two explicit Set-carried eventual-bound slots: (A) the lcm-side
     bound Psi(4n) <= 55^n eventually (the analytic effective theta input
     lives behind it); (B) the denominator bound (19/10)^n <= Phi_n
     eventually (the window-prime product lower bound lives behind it).
     The closing arithmetic is fully discharged here:
     55 * 10/19 = 550/19 < 29 (true constants: e^4 = 54.60 < 55).
   Dependencies: piu_zz_padic_clearing (zz_Phi, zz_L, zz_prodf,
     zz_prodf_divides_P, zz_j_div_lcm_P, zz_Pn_window_spec,
     zz_Pn_bounded, zz_primeb_prime, Bdiv/Bid), piu_zz_poincare_engine
     (zq, QleT', qleT_intro), piu_zz_pnt_lcmpow (zz_lcm_range_div_psi,
     zz_lcm_range_pos), piu_zz_pnt_psi (zz_psi, zz_iroot, zz_prim_neq0),
     piu_zz_pnt_qexp (zz_qmul_d_le), piu_zz_tau_enclosure_base
     (piu_zz_qpow, piu_zz_qpow_mono), Stdlib QArith/ZArith/Arith/Lia.
   References: piu_zz_tau_enclosure_base section D rate-slot shape —
     this module proves that face once the two slots are instantiated.
   Constructivity: statement faces Set-carried (QleT', sigT); both slots
     are parameterized Section exports (explicit arguments after the
     Section closes), not global assumptions; every lemma closes with a
     full proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <sandbox with born chain> ""
     piu_zz_pnt_rateup.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)



From Stdlib Require Import QArith ZArith Arith PArith Lia Bool.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_pnt_lcmpow.
Require Import piu_zz_pnt_psi.
Require Import piu_zz_pnt_qexp.

Local Open Scope Q_scope.
Require Import piu_zz_tau_enclosure_base.

(* ================= Section 1. Divisibility spine ================= *)

(* The prodf folding only multiplies prime factors, each at least one,
   so every value of the folding is at least one — the positivity
   anchor used on both sides of the L_n split. *)
Lemma zz_rateup_prodf_ge1 : forall n K : nat, (1 <= zz_prodf n K)%Z.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. lia.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)).
    + pose proof (IH) as IH1.
      assert (Hz : (1 <= Z.of_nat (S K))%Z) by lia.
      lia.
    + exact IH.
Qed.

Lemma zz_rateup_phi_ge1 : forall n : nat, (1 <= zz_Phi n)%Z.
Proof. intro n. apply zz_rateup_prodf_ge1. Qed.

(* Phi_n * L_n = lcm(1..4n): the identity that splits the L_n quotient.
   Every prime index captured by the Phi_n window divides lcm(1..4n)
   (it is a positive index at most 2n, hence at most 4n), so the
   folding divides the lcm, and the quotient L_n multiplies back. *)
Lemma zz_rateup_phi_ln : forall n : nat,
  (zz_Phi n * zz_L n)%Z = zz_lcm_range (4 * n)%nat.
Proof.
  intro n.
  assert (HdP : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  pose proof (zz_rateup_phi_ge1 n) as Hphi1.
  unfold zz_L.
  destruct HdP as [e He]. apply Bid_elim in He.
  replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n))%Z
    by (rewrite Z.mul_comm; exact He).
  rewrite Z.div_mul by lia. apply Z.mul_comm.
Qed.

(* Psi(4n) is at least one: it is a nat folding whose factors are
   primorials, each a nonzero nat value. *)
Lemma zz_rateup_psi_ge1 : forall N : nat, (1 <= zz_psi N)%nat.
Proof.
  intro N. unfold zz_psi.
  generalize (Nat.log2 N) as k. intro k.
  induction k as [|k IH].
  - cbn [zz_psi_prod]. lia.
  - cbn [zz_psi_prod]. unfold zz_psi_fac.
    pose proof (zz_prim_neq0 (zz_iroot (S k) N)) as Hp.
    lia.
Qed.

(* lcm(1..4n) is bounded by Psi(4n): the divisibility lcm | Psi with
   both sides positive makes the divisor the smaller factor. *)
Lemma zz_rateup_lcm_le_psi : forall n : nat, (1 <= n)%nat ->
  (zz_lcm_range (4 * n)%nat <= Z.of_nat (zz_psi (4 * n)%nat))%Z.
Proof.
  intros n Hn.
  assert (Hdiv : Bdiv (zz_lcm_range (4 * n)%nat) (Z.of_nat (zz_psi (4 * n)%nat)))
    by (apply zz_lcm_range_div_psi; lia).
  destruct Hdiv as [w Hw]. apply Bid_elim in Hw.
  pose proof (zz_lcm_range_pos (4 * n)%nat) as Hlcm1.
  pose proof (zz_rateup_psi_ge1 (4 * n)%nat) as Hpsi1.
  assert (Hw1 : (1 <= w)%Z).
  { destruct (Z.le_gt_cases 1 w) as [Hle | Hgt]; [exact Hle |].
    exfalso. lia. }
  nia.
Qed.

(* ================= Section 2. Rational assembly face ================= *)

(* Rational-side spine: zq (L_n) * zq (Phi_n) <= zq (Psi(4n)) — the
   product form consumed by the final division step. *)
Lemma zz_rateup_qsplit : forall n : nat, (1 <= n)%nat ->
  zq (zz_L n) * zq (zz_Phi n) <= zq (Z.of_nat (zz_psi (4 * n)%nat)).
Proof.
  intros n Hn.
  assert (Hprod := zz_rateup_phi_ln n).
  assert (Hle := zz_rateup_lcm_le_psi n Hn).
  unfold zq, Qle, Qmult, Qnum, Qden. cbn [Qnum Qden]. nia.
Qed.

(* Power identities for the closing arithmetic. *)
Lemma zz_rateup_qpow_mul : forall (q r : Q) (k : nat),
  piu_zz_qpow q k * piu_zz_qpow r k == piu_zz_qpow (q * r) k.
Proof.
  intros q r k. induction k as [|k IH].
  - reflexivity.
  - simpl.
    assert (Hr : q * piu_zz_qpow q k * (r * piu_zz_qpow r k)
                 == piu_zz_qpow q k * piu_zz_qpow r k * (q * r)) by ring.
    rewrite Hr. rewrite IH. ring.
Qed.

Lemma zz_rateup_qpow_pos : forall (q : Q) (k : nat),
  (0 < q)%Q -> (0 < piu_zz_qpow q k)%Q.
Proof.
  intros q k Hq. induction k as [|k IH].
  - simpl. unfold Qlt, Qnum, Qden. cbn. lia.
  - simpl. apply Qmult_lt_0_compat; [exact Hq | exact IH].
Qed.

Lemma zz_rateup_qpow_inv : forall (q : Q) (k : nat),
  (0 < q)%Q -> piu_zz_qpow (/ q) k == / (piu_zz_qpow q k).
Proof.
  intros q k Hq. induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite Qinv_mult_distr. reflexivity.
Qed.

Lemma zz_rateup_qinv_anti : forall (x y : Q), (0 < x)%Q -> x <= y -> / y <= / x.
Proof.
  intros x y Hx Hxy.
  destruct (Qlt_le_dec x y) as [Hlt | Heq].
  - apply (Qlt_le_weak (/ y) (/ x)).
    apply (proj1 (Qinv_lt_contravar x y Hx (Qlt_le_trans 0 x y Hx Hxy))).
    exact Hlt.
  - rewrite (Qle_antisym y x Heq Hxy). apply Qle_refl.
Qed.

(* ================= Section 3. Slot-carrying rate face ================= *)

Section B7Spine.

(* Slot A (analytic lcm side): Psi(4n) <= 55^n eventually. The
   effective theta bound on pec_prim (the analytic PNT input) behind
   the Psi upper bound lives here; 55 > e^4 = 54.60 leaves the closing
   margin 550/19 < 29 intact. *)
Hypothesis Hlcm_up : { Np : nat &
  forall n : nat, (Np <= n)%nat ->
    QleT' (zq (Z.of_nat (zz_psi (4 * n)%nat))) (piu_zz_qpow (55 # 1)%Q n) }.

(* Slot B (denominator side): (19/10)^n <= Phi_n eventually. The
   window-prime product lower bound (the B6 face) lives here;
   19/10 = 1.9 < e^{0.6452} = 1.9064 leaves the closing margin intact. *)
Hypothesis Hphi_lo : { Nq : nat &
  forall n : nat, (Nq <= n)%nat ->
    QleT' (piu_zz_qpow (19 # 10)%Q n) (zq (zz_Phi n)) }.

(* Final face: L_n <= 29^n eventually — the discharged form of the
   tau_enclosure_base rate slot. Assembly: zq (L_n) * zq (Phi_n)
   <= zq (Psi(4n)) <= 55^n and (19/10)^n <= zq (Phi_n), hence
   zq (L_n) <= 55^n / (19/10)^n = (550/19)^n <= 29^n, the last step by
   550/19 < 29 and exponent monotonicity. *)
Theorem zz_pnt_rate_up :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
      QleT' (zq (zz_L n)) (piu_zz_qpow (29 # 1)%Q n) }.
Proof.
  destruct Hlcm_up as [Np Hpa].
  destruct Hphi_lo as [Nq Hqb].
  exists (Nat.max (Nat.max Np Nq) 1).
  intros n Hn.
  apply Nat.max_lub_iff in Hn. destruct Hn as [Hn1 Hn3].
  apply Nat.max_lub_iff in Hn1. destruct Hn1 as [Hn1 Hn2].
  assert (Hn4 : (1 <= n)%nat) by lia.
  destruct (Hpa n Hn1) as [Ha].
  destruct (Hqb n Hn2) as [Hb].
  pose proof (zz_rateup_qsplit n Hn4) as Hstep.
  apply qleT_intro.
  (* the denominator side is positive *)
  assert (Hb1 : (1 # 1)%Q <= zq (zz_Phi n)).
  { apply qleT_intro. unfold zq, Qle, Qnum, Qden. cbn [Qnum Qden].
    pose proof (zz_rateup_phi_ge1 n). lia. }
  assert (Hbpos : (0 < zq (zz_Phi n))%Q).
  { apply (Qlt_le_trans 0 (1 # 1)%Q).
    - unfold Qlt, Qnum, Qden; cbn; lia.
    - exact Hb1. }
  assert (Hbne : ~ zq (zz_Phi n) == 0).
  { intro Hc0. rewrite Hc0 in Hbpos.
    unfold Qlt in Hbpos. cbn in Hbpos. discriminate. }
  (* divide the product bound through *)
  assert (Hstep2 : zq (zz_L n) <= zq (Z.of_nat (zz_psi (4 * n)%nat)) / zq (zz_Phi n))
    by (apply zz_qmul_d_le; [exact Hbpos | exact Hstep]).
  unfold Qdiv in Hstep2.
  (* pull in both slots *)
  assert (Hstep3 : zq (Z.of_nat (zz_psi (4 * n)%nat)) * (/ zq (zz_Phi n))
                   <= piu_zz_qpow (55 # 1)%Q n * (/ zq (zz_Phi n)))
    by (apply Qmult_le_compat_r; [exact Ha | apply Qinv_le_0_compat;
         apply (Qlt_le_weak 0); exact Hbpos]).
  assert (Hposq := zz_rateup_qpow_pos (19 # 10)%Q n ltac:(unfold Qlt, Qnum, Qden; cbn; lia)).
  assert (Hinvanti : / zq (zz_Phi n) <= piu_zz_qpow (10 # 19)%Q n).
  { replace (10 # 19)%Q with (/ (19 # 10)%Q) by reflexivity.
    rewrite zz_rateup_qpow_inv by (unfold Qlt, Qnum, Qden; cbn; lia).
    apply zz_rateup_qinv_anti.
    - exact Hposq.
    - exact Hb. }
  assert (Hstep4 : zq (Z.of_nat (zz_psi (4 * n)%nat)) * (/ zq (zz_Phi n))
                   <= piu_zz_qpow (55 # 1)%Q n * piu_zz_qpow (10 # 19)%Q n).
  { apply (Qle_trans _ (piu_zz_qpow (55 # 1)%Q n * (/ zq (zz_Phi n)))).
    - exact Hstep3.
    - assert (Hc7 : piu_zz_qpow (55 # 1)%Q n * (/ zq (zz_Phi n))
                    == (/ zq (zz_Phi n)) * piu_zz_qpow (55 # 1)%Q n) by ring.
      assert (Hc8 : piu_zz_qpow (55 # 1)%Q n * piu_zz_qpow (10 # 19)%Q n
                    == piu_zz_qpow (10 # 19)%Q n * piu_zz_qpow (55 # 1)%Q n) by ring.
      rewrite Hc7. rewrite Hc8.
      apply Qmult_le_compat_r.
      + exact Hinvanti.
      + apply (Qlt_le_weak 0). apply zz_rateup_qpow_pos.
        unfold Qlt, Qnum, Qden; cbn; lia. }
  (* merge the powers and close: 550/19 < 29 *)
  apply (Qle_trans _ (zq (Z.of_nat (zz_psi (4 * n)%nat)) * (/ zq (zz_Phi n)))).
  - exact Hstep2.
  - apply (Qle_trans _ (piu_zz_qpow ((55 # 1)%Q * (10 # 19)%Q) n)).
    + rewrite <- (zz_rateup_qpow_mul (55 # 1)%Q (10 # 19)%Q n).
      exact Hstep4.
    + apply piu_zz_qpow_mono.
      * unfold Qle, Qnum, Qden; cbn; lia.
      * unfold Qle, Qnum, Qden; cbn; lia.
Qed.

End B7Spine.

(* ================= Section 4. Certification face ================= *)

Print Assumptions zz_pnt_rate_up.

From Stdlib Require Import Extraction.
Separate Extraction piu_zz_qpow
  zz_rateup_prodf_ge1 zz_rateup_phi_ge1 zz_rateup_phi_ln
  zz_rateup_psi_ge1 zz_rateup_lcm_le_psi zz_rateup_qsplit
  zz_rateup_qpow_mul zz_rateup_qpow_pos zz_rateup_qpow_inv
  zz_rateup_qinv_anti zz_pnt_rate_up.
