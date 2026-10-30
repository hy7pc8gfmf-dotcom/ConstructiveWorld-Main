(* ==========================================================================
   Module: piu_zz_pnt_assembly
   Mission: the PNT-side total assembly. It tables the five born pieces of
     the pnt consumer line (lcmpow / window / winsum / ipow / phi), takes
     the two L_n rate slots and the window-theta slot as explicit
     parameters (the honest PNT-grade assumption face of
     piu_zz_tau_enclosure_base - parameterized, never discharged), and
     delivers: (1) the multiplicative decomposition face
     zq(zz_L n) * zq(zz_Phi n) <= zq(psi(4n)) composing node B3.4
     (zz_lcm_range_div_psi) with the divisibility algebra of zz_L; (2) the
     Phi lower-bound face re-exported from phi at the theta slot;
     (3) the slot-consumption faces: the L_n eventual-rate wrappers and
     the tau/low face instantiations of piu_zz_tau_enclosure_base SSF.
   Dependencies: piu_zz_tau_enclosure_base, piu_zz_padic_clearing,
     piu_zz_poincare_engine, abl_Pr_erdos_theta, and the five born pieces
     piu_zz_pnt_window / piu_zz_pnt_winsum / piu_zz_pnt_ipow /
     piu_zz_pnt_lcmpow / piu_zz_pnt_psi / piu_zz_pnt_phi.
   References: the five-piece interface table of the KB38S record; nodes
     B3.4 (lcm | psi) and B6 (phi lower) of the pnt line; ZZ 2020 v2
     sections 4-5 for the L_n rate semantics.
   Constructivity: every face is Set-carried (sigT / QleT' / Bdiv); the
     rate slots are explicit section parameters, so the module closes with
     zero assumptions beyond the declared slots; definitions transparent;
     no classical axioms anywhere.
   Build: coqc -native-compiler no -q -Q <certified vo tree> ""
     -Q <this dir> "" piu_zz_pnt_assembly.v (single lane under cpu_guard).
   ========================================================================== *)

From Stdlib Require Import QArith ZArith Arith PArith Lia.
Require Import S03_QExp.
Require Import piu_zz_tau_enclosure_base.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.
Require Import abl_Pr_erdos_theta.
Require Import abl_Pr_erdos_core.
Require Import abl_Pr_core_01.
Require Import piu_zz_pnt_window.
Require Import piu_zz_pnt_winsum.
Require Import piu_zz_pnt_ipow.
Require Import piu_zz_pnt_lcmpow.
Require Import piu_zz_pnt_psi.
Require Import piu_zz_pnt_phi.

Local Open Scope Q_scope.

Section PntAssembly.

Variable HLn_rate_up : { N0 : nat & forall n : nat, (N0 <= n)%nat ->
  QleT' (zq (zz_L n)) (piu_zz_qpow piu_zz_lam_u n) }.
Variable HLn_rate_lo : { N0 : nat & forall n : nat, (N0 <= n)%nat ->
  QleT' (piu_zz_qpow piu_zz_lam_l n) (zq (zz_L n)) }.
Variable h_pnt_win_theta : forall (n k J : nat),
  (zz_pnt_phi_x0 <= n)%nat -> (k < 150)%nat ->
  QleT' (exp_partial J (zz_pnt_win_c n k))
        (zq (zz_pnt_wprod n (zz_pnt_ak n k) (zz_pnt_bk n k) (2 * n)%nat)).

(* ================================================================== *)
(* §1 positivity minis for the two magnitudes                          *)
(* ================================================================== *)

Lemma zz_pnt_asm_prodf_ge1 : forall n K : nat, (1 <= zz_prodf n K)%Z.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. lia.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)).
    + assert (Hz : (1 <= Z.of_nat (S K))%Z) by lia.
      lia.
    + lia.
Qed.

Lemma zz_pnt_asm_psi_ge1 : forall N : nat, (1 <= N)%nat -> (1 <= zz_psi N)%nat.
Proof.
  intros N HN. unfold zz_psi.
  induction (Nat.log2 N) as [|k IH].
  - cbn [zz_psi_prod]. lia.
  - cbn [zz_psi_prod].
    assert (Hfac : (1 <= zz_psi_fac N (S k))%nat).
    { unfold zz_psi_fac.
      apply pec_prod_ge1. intros x Hx.
      destruct (pec_win_in 1 (zz_iroot (S k) N - 1) x Hx) as [_ [Hx2 _]].
      lia. }
    assert (Hih : (1 <= zz_psi_prod N k)%nat) by exact IH.
    lia.
Qed.

Lemma zz_pnt_asm_zq_le : forall a b : Z, (a <= b)%Z -> QleT' (zq a) (zq b).
Proof.
  intros a b Hab. apply qleT_intro. unfold Qle, zq. cbn. lia.
Qed.

(* ================================================================== *)
(* §2 the multiplicative decomposition: L_n * Phi_n <= psi(4n)         *)
(*    (zz_L n = Z.div lcm(4n) Phi_n and node B3.4 lcm | psi, so the    *)
(*    L_n numerator-fold and the Phi denominator-fold split lcm apart) *)
(* ================================================================== *)

Theorem zz_pnt_asm_Ln_split : forall n : nat, (1 <= n)%nat ->
  QleT' (zq (zz_L n) * zq (zz_Phi n)) (zq (Z.of_nat (zz_psi (4 * n)%nat))).
Proof.
  intros n Hn. unfold zz_L in *.
  assert (HPhi : (1 <= zz_Phi n)%Z) by (apply zz_pnt_asm_prodf_ge1).
  pose proof (Z.div_mod (zz_lcm_range (4 * n)%nat) (zz_Phi n)
              ltac:(lia)) as Hdm.
  assert (Hmod : (0 <= zz_lcm_range (4 * n)%nat mod zz_Phi n)%Z).
  { apply Z.mod_pos_bound. lia. }
  remember (zz_lcm_range (4 * n)%nat / zz_Phi n)%Z as D eqn:ED.
  remember (zz_lcm_range (4 * n)%nat mod zz_Phi n)%Z as M eqn:EM.
  assert (Hmul : (zz_Phi n * D <= zz_lcm_range (4 * n)%nat)%Z) by lia.
  destruct (zz_lcm_range_div_psi (4 * n)%nat ltac:(lia)) as [z Hz].
  apply Bid_elim in Hz.
  assert (Hz1 : (1 <= z)%Z).
  { pose proof (zz_lcm_range_pos (4 * n)%nat) as Hl.
    assert (Hp1 : (1 <= zz_psi (4 * n)%nat)%nat)
      by (apply zz_pnt_asm_psi_ge1; lia).
    assert (Hpz : (1 <= Z.of_nat (zz_psi (4 * n)%nat))%Z) by lia.
    nia. }
  assert (Hlcmpsi : (zz_lcm_range (4 * n)%nat
                     <= Z.of_nat (zz_psi (4 * n)%nat))%Z) by nia.
  apply qleT_intro. unfold Qle, zq. cbn [Qnum Qden Qmult].
  nia.
Qed.

(* ================================================================== *)
(* §3 the Phi lower face re-exported at the window-theta slot          *)
(*    (five-piece [5] phi interface: node B6 deliverable)              *)
(* ================================================================== *)

Definition zz_pnt_asm_Phi_lower : forall (n J : nat),
  (zz_pnt_phi_x0 <= n)%nat ->
  QleT' (zz_pnt_lbprod n J 150) (zq (zz_Phi n)) :=
  zz_pnt_phi_lower h_pnt_win_theta.

(* ================================================================== *)
(* §4 the slot consumption faces                                       *)
(*    (tau_enclosure_base SSF: the two rate slots parameterized, the   *)
(*    eventual wrappers derived, the tau/low faces instantiated)       *)
(* ================================================================== *)

Definition zz_pnt_asm_Ln_up :
  piu_zz_eventual_le piu_zz_lam_u (fun n : nat => zq (zz_L n)).
Proof.
  destruct HLn_rate_up as [N0 H]. exists N0. exact H.
Qed.

Definition zz_pnt_asm_Ln_lo :
  piu_zz_eventual_ge piu_zz_lam_l (fun n : nat => zq (zz_L n)).
Proof.
  destruct HLn_rate_lo as [N0 H]. exists N0. exact H.
Qed.

Definition zz_pnt_asm_tau_face (mag : nat -> Q)
  (Hcage : piu_zz_eventual_le piu_zz_rho_u mag) :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
    QleT' (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q
          (piu_zz_qpow (1 # 6)%Q n) } :=
  piu_zz_tau_face HLn_rate_up mag Hcage.

Definition zz_pnt_asm_low_face (mag : nat -> Q)
  (Hcage : piu_zz_eventual_ge piu_zz_rho_l mag) :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
    QleT' (piu_zz_qpow (1 # 40)%Q n)
          (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q } :=
  piu_zz_low_face HLn_rate_lo mag Hcage.

End PntAssembly.

(* ================================================================== *)
(* §5 certification face                                               *)
(* ================================================================== *)

Print Assumptions zz_pnt_asm_Ln_split.
Print Assumptions zz_pnt_asm_Phi_lower.
Print Assumptions zz_pnt_asm_Ln_up.
Print Assumptions zz_pnt_asm_Ln_lo.
Print Assumptions zz_pnt_asm_tau_face.
Print Assumptions zz_pnt_asm_low_face.

From Stdlib Require Import Extraction.
Separate Extraction zz_pnt_asm_Ln_split zz_pnt_asm_Phi_lower
  zz_pnt_asm_Ln_up zz_pnt_asm_Ln_lo zz_pnt_asm_tau_face
  zz_pnt_asm_low_face.
