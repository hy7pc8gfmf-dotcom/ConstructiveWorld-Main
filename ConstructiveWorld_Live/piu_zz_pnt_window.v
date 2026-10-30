(* ==========================================================================
   Module: piu_zz_pnt_window
   Mission: Window coverage of the set P_n for the effective-PNT
     consumption chain: a prime p lying in a half-open window
     (3n/(3k+2), 2n/(2k+1)] has fractional part {n/p} in [1/2, 2/3),
     hence belongs to the Zeilberger-Zudilin window set P_n (node B1);
     plus the window-position corollary 3n < p^2 that holds whenever the
     kept windows sit above sqrt(3n).
   Dependencies: piu_zz_padic_clearing (zz_in_Pn, zz_primeb, BidT),
     Stdlib ZArith/Arith/Lia (nia for the bilinear quotient step).
   References: Zeilberger-Zudilin 2020 v2, Lemma 2 — the window set
     P_n = {p prime : p > max(5, sqrt(3n)), 1/2 <= {n/p} < 2/3}; the
     window endpoints a_k = 3n/(3k+2), b_k = 2n/(2k+1) with floor-form
     inequalities p*(3k+2) > 3n and p*(2k+1) <= 2n.
   Constructivity: statement faces Set-carried (BidT boolean identity,
     conjunction distributed over the andb components of zz_in_Pn);
     arithmetic uses Nat.div_mod_eq and nia inside proofs; every lemma
     closes with a full proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <this directory> ""
     piu_zz_pnt_window.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import ZArith Arith Lia Bool.
Require Import piu_zz_padic_clearing.

(* This module is pure nat arithmetic; the imported padic-clearing module
   exports the Z scope, so the nat scope is re-opened locally. *)
Local Open Scope nat_scope.

(* ================= Section 1. Window fraction face ================= *)

(* The discrete fractional-part condition: from the floor-form window
   inequalities p*(2k+1) <= 2n < 2p*(k+1/2)... the quotient q = n/p
   equals k exactly, so 2*(n mod p) >= p and 3*(n mod p) < 2p. *)
Theorem zz_pnt_window_frac : forall n k p : nat,
  (0 < p)%nat ->
  (p * (2 * k + 1) <= 2 * n)%nat ->
  (3 * n < p * (3 * k + 2))%nat ->
  prod (BidT (Nat.leb p (2 * (n mod p))%nat))
       (BidT (Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)).
Proof.
  intros n k p Hp Hlow Hhigh.
  assert (Hd : (n = p * (n / p) + n mod p)%nat) by apply Nat.div_mod_eq.
  assert (Hr : (n mod p < p)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hzn : (Z.of_nat n
                   = Z.of_nat p * Z.of_nat (n / p) + Z.of_nat (n mod p))%Z)
    by lia.
  assert (HlowZ : (Z.of_nat p * (2 * Z.of_nat k + 1) <= 2 * Z.of_nat n)%Z)
    by lia.
  assert (HhighZ : (3 * Z.of_nat n
                      < Z.of_nat p * (3 * Z.of_nat k + 2))%Z)
    by lia.
  assert (HmodZ : (0 <= Z.of_nat (n mod p) < Z.of_nat p)%Z) by lia.
  assert (Hq1 : (Z.of_nat (n / p) <= Z.of_nat k)%Z) by nia.
  assert (Hq2 : (Z.of_nat k <= Z.of_nat (n / p))%Z) by nia.
  assert (HqNat : (n / p = k)%nat) by (apply Nat2Z.inj_iff; lia).
  rewrite HqNat in Hd.
  split.
  - apply BidT_intro. apply Nat.leb_le. lia.
  - apply BidT_intro. apply Nat.ltb_lt. lia.
Qed.

(* ================= Section 2. Window membership ================= *)

(* Node B1 (born face, Set-carried): a prime p above 5 with p^2 > 3n
   lying in window k belongs to the window set, i.e. zz_in_Pn n p is
   true — each andb component discharged from the fraction face. *)
Theorem zz_pnt_window_subset : forall n k p : nat,
  BidT (zz_primeb p) -> (5 < p)%nat ->
  (3 * n < p * p)%nat ->
  (p * (2 * k + 1) <= 2 * n)%nat ->
  (3 * n < p * (3 * k + 2))%nat ->
  BidT (zz_in_Pn n p).
Proof.
  intros n k p Hpb Hp5 Hsqrt Hlow Hhigh.
  apply BidT_elim in Hpb.
  apply BidT_intro. unfold zz_in_Pn.
  apply Bool.andb_true_iff. split; [exact Hpb |].
  apply Bool.andb_true_iff. split; [apply Nat.ltb_lt; exact Hp5 |].
  apply Bool.andb_true_iff. split; [apply Nat.ltb_lt; exact Hsqrt |].
  assert (Hpos : (0 < p)%nat) by lia.
  destruct (zz_pnt_window_frac n k p Hpos Hlow Hhigh) as [Hf1 Hf2].
  apply Bool.andb_true_iff. split.
  - apply BidT_elim. exact Hf1.
  - apply BidT_elim. exact Hf2.
Qed.

(* ================= Section 3. Window position above the square root ================= *)

(* If every kept window index satisfies k <= K and the K-th window still
   lies above the curve, i.e. (3K+2)^2 < 3n, then every window prime
   satisfies 3n < p^2: the window membership condition of Section 2 is
   automatic for large n. *)
Theorem zz_pnt_window_above_sqrt : forall n K k p : nat,
  (k <= K)%nat ->
  (3 * n < p * (3 * k + 2))%nat ->
  ((3 * K + 2) * (3 * K + 2) < 3 * n)%nat ->
  (3 * n < p * p)%nat.
Proof.
  intros n K k p HkK Hwin Hbig.
  assert (HV : p * (3 * k + 2) <= p * (3 * K + 2))
    by (apply Nat.mul_le_mono_l; lia).
  destruct (Nat.le_gt_cases p (3 * K + 2)) as [Hc | Hc].
  - exfalso.
    assert (Hm : p * (3 * K + 2) <= (3 * K + 2) * (3 * K + 2)) by nia.
    lia.
  - assert (Hpp : p * (3 * K + 2) + p <= p * p) by nia.
    lia.
Qed.

(* ================= Section 4. Numeric smoke sample ================= *)

(* Sample run of the fraction face at n = 100, k = 0, p = 160 (window
   (150, 200]): both Set-carried boolean components evaluate true. *)
Lemma zz_pnt_window_frac_sample :
  prod (BidT (Nat.leb 160%nat (2 * (100 mod 160)%nat)%nat))
       (BidT (Nat.ltb (3 * (100 mod 160)%nat)%nat (2 * 160)%nat)).
Proof.
  apply (zz_pnt_window_frac 100 0 160).
  - lia.
  - lia.
  - lia.
Qed.

(* ================= Section 5. Certification face ================= *)

Print Assumptions zz_pnt_window_frac.
Print Assumptions zz_pnt_window_subset.
Print Assumptions zz_pnt_window_above_sqrt.
Print Assumptions zz_pnt_window_frac_sample.

From Stdlib Require Import Extraction.
Separate Extraction zz_pnt_window_frac zz_pnt_window_subset
  zz_pnt_window_above_sqrt zz_pnt_window_frac_sample.
