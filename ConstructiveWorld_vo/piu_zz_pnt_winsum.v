(* ==========================================================================
   Module: piu_zz_pnt_winsum
   Mission: Window-sum certificates for the effective-PNT consumption
     chain: the per-window density term 1/((2k+1)(3k+2)) — equal to the
     window width ratio 2/(2k+1) - 3/(3k+2) — its positivity, its
     monotone decrease, its majoration by the telescoping family
     1/(4k(k+1)), and the explicit K = 150 numeric certificates that feed
     the Phi_n lower bound (node B2).
   Dependencies: piu_zz_padic_clearing (BidT), piu_zz_poincare_engine
     (QleT', qleT_intro), Stdlib QArith/ZArith/Arith/PArith/Lia.
   References: Zeilberger-Zudilin 2020 v2, eq. (10): the full window sum
     equals pi/(2 sqrt(3)) - ln(3 sqrt(3)/4) = 0.6452756...; the partial
     sum over k < 150 equals 0.6441651... (exact rational arithmetic,
     independent cross-check), so the born certificate 322/500 = 0.644
     holds with margin 1.65e-4.
   Constructivity: statement faces Set-carried (QleT' boolean ordering,
     BidT boolean identity); rational denominators are carried in the
     positive component of Q via Pos.of_succ_nat, with the cross-multiplied
     Qmake ordering helper closing each face by kernel conversion over the
     Z-inequality; symbolic steps close by nia over Z, numeric steps by
     vm_compute on boolean comparisons; every lemma closes with a full
     proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <this directory> ""
     piu_zz_pnt_winsum.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import QArith ZArith Arith PArith Lia Bool.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.

Local Open Scope Q_scope.

(* ================= Section 1. Density term ================= *)

(* Cross-multiplied ordering helper for explicit rational constructors:
   Qle (Qmake a p) (Qmake c q) is the Z-inequality a * q <= c * p; the
   kernel conversion discharges the projection reductions. *)
Lemma zz_pnt_qle_make : forall (a c : Z) (p q : positive),
  (a * Z.pos q <= c * Z.pos p)%Z ->
  QleT' (Qmake a p) (Qmake c q).
Proof.
  intros a c p q H. apply qleT_intro. exact H.
Qed.

(* Bridge: positive order reflected to Z from the nat order of
   Pos.to_nat (Pos2Z exposes compare but no direct order injection). *)
Lemma zz_pnt_pos_zle : forall p q : positive,
  (Pos.to_nat p <= Pos.to_nat q)%nat -> (Z.pos p <= Z.pos q)%Z.
Proof.
  intros p q H.
  destruct (Z.compare_spec (Z.pos p) (Z.pos q)) as [Heq | Hlt | Hgt].
  - rewrite Heq. apply Z.le_refl.
  - apply Z.lt_le_incl. exact Hlt.
  - exfalso.
    apply Nat2Z.inj_le in H.
    rewrite !positive_nat_Z in H.
    lia.
Qed.

(* Denominator of the per-window density term, carried as a positive:
   (2k+1)(3k+2), stored as Pos.of_succ_nat of that value minus 1. *)
Definition zz_pnt_win_den (k : nat) : positive :=
  Pos.of_succ_nat ((2 * k + 1) * (3 * k + 2) - 1)%nat.

Definition zz_pnt_win_term (k : nat) : Q := Qmake 1 (zz_pnt_win_den k).

(* Denominator of the telescoping majoration family 1/(4k(k+1)). *)
Definition zz_pnt_win_den_maj (k : nat) : positive :=
  Pos.of_succ_nat (4 * k * (k + 1) - 1)%nat.

Lemma zz_pnt_win_den_nat : forall k : nat,
  Pos.to_nat (zz_pnt_win_den k) = ((2 * k + 1) * (3 * k + 2))%nat.
Proof.
  intro k. unfold zz_pnt_win_den. rewrite SuccNat2Pos.id_succ.
  assert (Hge : ((2 * k + 1) * (3 * k + 2) >= 2)%nat) by nia. lia.
Qed.

Lemma zz_pnt_win_den_maj_nat : forall k : nat, (1 <= k)%nat ->
  Pos.to_nat (zz_pnt_win_den_maj k) = (4 * k * (k + 1))%nat.
Proof.
  intros k HK. unfold zz_pnt_win_den_maj. rewrite SuccNat2Pos.id_succ.
  assert (Hge : (4 * k * (k + 1) >= 2)%nat) by nia. lia.
Qed.

(* Node B2.1a (born face): the density term is nonnegative. *)
Theorem zz_pnt_win_term_pos : forall k : nat,
  QleT' (Qmake 0 1) (zz_pnt_win_term k).
Proof.
  intro k. apply (zz_pnt_qle_make 0 1 1 (zz_pnt_win_den k)).
  rewrite Z.mul_0_l, Z.mul_1_r. apply Z.lt_le_incl. apply Pos2Z.is_pos.
Qed.

(* Node B2.1b (born face): the density term decreases in k, since the
   denominator (2k+1)(3k+2) increases: 6k^2+19k+15 >= 6k^2+7k+2. *)
Theorem zz_pnt_win_term_dec : forall k : nat,
  QleT' (zz_pnt_win_term (S k)) (zz_pnt_win_term k).
Proof.
  intro k.
  apply (zz_pnt_qle_make 1 1 (zz_pnt_win_den (S k)) (zz_pnt_win_den k)).
  rewrite !Z.mul_1_l. apply zz_pnt_pos_zle.
  rewrite !zz_pnt_win_den_nat. nia.
Qed.

(* Node B2.2 (born face): majoration by the telescoping family
   1/(4k(k+1)) — since sum_{k>=K} 1/(4k(k+1)) = 1/(4K), this documents
   the truncation cost of keeping finitely many windows. *)
Theorem zz_pnt_win_term_maj : forall k : nat, (1 <= k)%nat ->
  QleT' (zz_pnt_win_term k) (Qmake 1 (zz_pnt_win_den_maj k)).
Proof.
  intros k HK.
  apply (zz_pnt_qle_make 1 1 (zz_pnt_win_den k) (zz_pnt_win_den_maj k)).
  rewrite !Z.mul_1_l. apply zz_pnt_pos_zle.
  rewrite zz_pnt_win_den_maj_nat by exact HK.
  rewrite !zz_pnt_win_den_nat. nia.
Qed.

(* ================= Section 2. Partial sums and numeric certificates ================= *)

(* Partial window sum: zz_pnt_winsum_part s J = sum_{i=0}^{J-1} term(s+i). *)
Fixpoint zz_pnt_winsum_part (s J : nat) : Q :=
  match J with
  | O => Qmake 0 1
  | S J' => zz_pnt_win_term s + zz_pnt_winsum_part (S s) J'
  end.

(* Node B2.3a (born face): over the K = 150 kept windows (k = 0..149)
   the window-width sum is at least 322/500 = 0.644; the exact partial
   sum is 0.6441651..., cross-checked by independent exact rational
   arithmetic before this statement was fixed. *)
Theorem zz_pnt_winsum_150_lb :
  BidT (Qle_bool (Qmake 322 500) (zz_pnt_winsum_part 0 150%nat)).
Proof.
  apply BidT_intro. vm_compute. reflexivity.
Qed.

(* Node B2.3b (born face): the discarded tail over the next 150 windows
   (k = 150..299) is at most 1/600; the exact value is 0.000555...,
   quantifying the truncation cost recorded in B2.2. *)
Theorem zz_pnt_winsum_tail_150 :
  BidT (Qle_bool (zz_pnt_winsum_part 150 150%nat) (Qmake 1 600)).
Proof.
  apply BidT_intro. vm_compute. reflexivity.
Qed.

(* ================= Section 3. Certification face ================= *)

Print Assumptions zz_pnt_win_term_pos.
Print Assumptions zz_pnt_win_term_dec.
Print Assumptions zz_pnt_win_term_maj.
Print Assumptions zz_pnt_winsum_150_lb.
Print Assumptions zz_pnt_winsum_tail_150.

From Stdlib Require Import Extraction.
Separate Extraction zz_pnt_win_term zz_pnt_winsum_part
  zz_pnt_winsum_150_lb zz_pnt_winsum_tail_150.
