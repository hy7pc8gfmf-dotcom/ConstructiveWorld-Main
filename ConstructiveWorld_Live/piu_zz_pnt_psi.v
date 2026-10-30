(* ==========================================================================
   Module: piu_zz_pnt_psi
   Mission: The psi-versus-primorial split for the effective-PNT chain:
     the fold zz_psi_prod N k (product of the primorials of the integer
     i-th roots of N, i = 1..k) is bounded by pec_prim N times the
     (k-1)-st power of pec_prim (zz_iroot 2 N), so the full psi fold
     zz_psi N = zz_psi_prod N (log2 N) satisfies three computable upper
     faces: the factored primorial face, the single power face
     4^(2 N log2 N), and the consumption face pec_prim N * 4^(2 sqrt(N)
     (log2 N - 1)) used by the assembly stage to isolate the analytic
     input on the leading primorial factor alone.
   Dependencies: piu_zz_pnt_lcmpow (zz_iroot, zz_iroot_spec,
     zz_iroot_anti, zz_psi_prod, zz_psi_fac, zz_psi), abl_Pr_erdos_theta
     (pec_prim, pec_prim_monotone, pec_prod_ge1, pec_primorial_linear),
     HansonLcm (hl_le_t, hl_le_to_le_t), Stdlib ZArith/Arith/Lia/Bool/List.
   References: the classical step psi(N) = sum_k theta(N^(1/k)) behind
     the dyadic-tail estimate; the tree face of the theta input slot is
     pec_theta_bound (abl_Pr_erdos_theta), mirrored here at the fold
     level.
   Constructivity: statement faces Set-carried (hl_le_t = Id (Nat.leb _ _)
     true); all auxiliary statements are nat comparisons; definitions
     transparent; every lemma closes with a full proof under the global
     context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <sandbox> ""
     piu_zz_pnt_psi.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import ZArith Arith Lia Bool List.
Require Import HansonLcm.
Require Import piu_zz_padic_clearing.
Require Import abl_Pr_core_01.
Require Import abl_Pr_erdos_core.
Require Import abl_Pr_erdos_theta.
Require Import piu_zz_pnt_lcmpow.

Local Open Scope nat_scope.

(* ================= Section 1. Root positivity and magnitude ================= *)

(* For N >= 1 and k >= 1 the integer k-th root is at least 1: otherwise
   the root spec upper bound would read N < 1^k = 1. *)
Lemma zz_iroot_pos : forall k N : nat, (1 <= k)%nat -> (1 <= N)%nat ->
  (1 <= zz_iroot k N)%nat.
Proof.
  intros k N Hk HN.
  destruct (Nat.le_gt_cases 1 (zz_iroot k N)) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    pose proof (proj2 (zz_iroot_spec k N Hk)) as H2.
    assert (H0 : zz_iroot k N = 0%nat) by lia.
    rewrite H0 in H2. rewrite Nat.pow_1_l in H2. lia.
Qed.

(* The integer square root is at most N: from root^2 <= N, if the root
   exceeded N then root^2 >= 2 * root > N since root >= 1. *)
Lemma zz_iroot_two_le : forall N : nat, (1 <= N)%nat -> (zz_iroot 2 N <= N)%nat.
Proof.
  intros N HN.
  pose proof (proj1 (zz_iroot_spec 2 N ltac:(lia))) as H1.
  destruct (Nat.le_gt_cases (zz_iroot 2 N) N) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hr1 : (1 <= zz_iroot 2 N)%nat) by (apply zz_iroot_pos; lia).
    rewrite Nat.pow_succ_r' in H1. rewrite Nat.pow_1_r in H1.
    assert (H2 : (2 * zz_iroot 2 N <= zz_iroot 2 N * zz_iroot 2 N)%nat)
      by nia.
    lia.
Qed.

(* The primorial is never zero: every window member is a prime above
   the window base, hence at least 2 > 1 (pec_win_in), so the folded
   product is at least one (pec_prod_ge1). *)
Lemma zz_prim_neq0 : forall M : nat, pec_prim M <> 0%nat.
Proof.
  intro M. unfold pec_prim.
  assert (H1 : (1 <= fold_right Nat.mul 1 (pec_win 1 (M - 1)))%nat).
  { apply (pec_prod_ge1 (pec_win 1 (M - 1))).
    intros x Hx.
    destruct (pec_win_in 1 (M - 1) x Hx) as [_ [Hx2 _]]. lia. }
  lia.
Qed.

(* ================= Section 2. The fold bound ================= *)

(* Main fold estimate: for k >= 1 the product of the first k root
   primorials is at most pec_prim N times the (k-1)-st power of the
   square-root primorial. Induction on k: every factor with index >= 2
   is at most the index-2 factor, because the integer root is
   anti-monotone in the index (zz_iroot_anti) and the primorial is
   monotone (pec_prim_monotone). *)
Lemma zz_psi_prod_le : forall N k : nat, (1 <= N)%nat -> (1 <= k)%nat ->
  hl_le_t (zz_psi_prod N k)
    (pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N)) (k - 1))%nat.
Proof.
  intros N k HN. induction k as [|k IH]; intros Hk.
  - exfalso. lia.
  - destruct k as [|k'].
    + (* index 1: the fold is exactly the leading factor *)
      cbn [zz_psi_prod]. unfold zz_psi_fac.
      rewrite zz_iroot_one, Nat.mul_1_l.
      replace (1 - 1)%nat with 0%nat by lia.
      rewrite Nat.pow_0_r, Nat.mul_1_r.
      apply hl_le_to_le_t. apply Nat.le_refl.
    + (* index >= 2: peel the last factor and absorb it into the power *)
      apply hl_le_to_le_t.
      pose proof (IH ltac:(lia)) as HB. apply hl_le_t_to_le in HB.
      replace (S k' - 1)%nat with k'%nat in HB by lia.
      assert (Hfac : (pec_prim (zz_iroot (S (S k')) N)
                      <= pec_prim (zz_iroot 2 N))%nat).
      { apply pec_prim_monotone.
        - apply zz_iroot_pos; lia.
        - apply (zz_iroot_anti (S (S k')) 2 N); lia. }
      cbn [zz_psi_prod]. unfold zz_psi_fac.
      apply Nat.le_trans with
        ((pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N)) k'
          * pec_prim (zz_iroot (S (S k')) N))%nat).
      * apply Nat.mul_le_mono_r. exact HB.
      * apply Nat.le_trans with
          ((pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N)) k'
            * pec_prim (zz_iroot 2 N))%nat).
        -- apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hfac].
        -- replace (S (S k') - 1)%nat with (S k') by lia.
           rewrite Nat.pow_succ_r'. nia.
Qed.

(* ================= Section 3. The three psi upper faces ================= *)

(* Face 1 (factored): zz_psi N is at most pec_prim N times the square
   root primorial to the (log2 N - 1)-st power. The degenerate order
   N = 1 (log2 N = 0) reads 1 <= pec_prim N. *)
Lemma zz_psi_bound : forall N : nat, (1 <= N)%nat ->
  hl_le_t (zz_psi N)
    (pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N)) (Nat.log2 N - 1))%nat.
Proof.
  intros N HN. unfold zz_psi.
  destruct (Nat.log2 N) as [|k'] eqn:E.
  - cbn [zz_psi_prod]. apply hl_le_to_le_t.
    rewrite Nat.pow_0_r, Nat.mul_1_r.
    unfold pec_prim. apply (pec_prod_ge1 (pec_win 1 (N - 1))).
    intros x Hx. destruct (pec_win_in 1 (N - 1) x Hx) as [_ [Hx2 _]]. lia.
  - pose proof (zz_psi_prod_le N (S k') HN ltac:(lia)) as HB.
    apply hl_le_t_to_le in HB.
    replace (S k' - 1)%nat with k'%nat in HB by lia.
    apply hl_le_to_le_t. replace (S k' - 1)%nat with k'%nat by lia.
    exact HB.
Qed.

(* Face 2 (single power): the leading primorial is at most 4^(2 N) by
   pec_primorial_linear, the square-root primorial too since the square
   root is at most N, so the whole fold lands under 4^(2 N log2 N). *)
Lemma zz_psi_bound_pow : forall N : nat, (1 <= N)%nat ->
  hl_le_t (zz_psi N) (Nat.pow 4 (2 * N * Nat.log2 N))%nat.
Proof.
  intros N HN. apply hl_le_to_le_t.
  destruct (Nat.le_gt_cases 1 (Nat.log2 N)) as [Hlog | Hlog0].
  - pose proof (hl_le_t_to_le _ _ (zz_psi_bound N HN)) as HB.
    pose proof (pec_primorial_linear N HN) as Hlead.
    pose proof (pec_primorial_linear (zz_iroot 2 N)
                  (zz_iroot_pos 2 N ltac:(lia) HN)) as Htail.
    assert (HrN : (zz_iroot 2 N <= N)%nat) by (apply zz_iroot_two_le; exact HN).
    assert (Htail2 : (pec_prim (zz_iroot 2 N) <= Nat.pow 4 (2 * N))%nat).
    { apply Nat.le_trans with (Nat.pow 4 (2 * zz_iroot 2 N)).
      - exact Htail.
      - apply Nat.pow_le_mono_r; [lia | apply Nat.mul_le_mono_l; exact HrN]. }
    replace (2 * N * Nat.log2 N)%nat
      with (2 * N + 2 * N * (Nat.log2 N - 1))%nat by nia.
    rewrite Nat.pow_add_r.
    apply Nat.le_trans with
      ((pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N))
        (Nat.log2 N - 1))%nat).
    + exact HB.
    + apply Nat.le_trans with
        ((Nat.pow 4 (2 * N)
          * Nat.pow (Nat.pow 4 (2 * N)) (Nat.log2 N - 1))%nat).
      * apply Nat.mul_le_mono.
        -- exact Hlead.
        -- apply Nat.pow_le_mono_l. exact Htail2.
      * rewrite <- (Nat.pow_mul_r 4 (2 * N) (Nat.log2 N - 1)).
        apply Nat.le_refl.
  - (* order N = 1: the fold is the empty product 1 *)
    assert (Hl0 : Nat.log2 N = 0%nat) by lia.
    destruct (Nat.log2_spec N ltac:(lia)) as [Hl1 Hl2].
    rewrite Hl0 in Hl2. cbn [Nat.pow] in Hl2.
    assert (HN1 : N = 1%nat) by lia.
    rewrite HN1. unfold zz_psi.
    replace (Nat.log2 1)%nat with 0%nat by reflexivity.
    cbn [zz_psi_prod].
    replace (2 * 1 * 0)%nat with 0%nat by lia.
    rewrite Nat.pow_0_r. apply Nat.le_refl.
Qed.

(* Face 3 (consumption face): the tail beyond the leading factor is a
   single power of 4 with exponent 2 sqrt(N) (log2 N - 1), so the
   assembly stage can pair the analytic input on pec_prim N with a
   purely computable dyadic tail. *)
Lemma zz_psi_bound_tail : forall N : nat, (1 <= N)%nat ->
  hl_le_t (zz_psi N)
    (pec_prim N * Nat.pow 4 (2 * zz_iroot 2 N * (Nat.log2 N - 1)))%nat.
Proof.
  intros N HN. apply hl_le_to_le_t.
  destruct (Nat.le_gt_cases 1 (Nat.log2 N)) as [Hlog | Hlog0].
  - pose proof (hl_le_t_to_le _ _ (zz_psi_bound N HN)) as HB.
    pose proof (pec_primorial_linear (zz_iroot 2 N)
                  (zz_iroot_pos 2 N ltac:(lia) HN)) as Htail.
    apply Nat.le_trans with
      ((pec_prim N * Nat.pow (pec_prim (zz_iroot 2 N))
        (Nat.log2 N - 1))%nat).
    + exact HB.
    + apply Nat.mul_le_mono_l.
      apply Nat.le_trans with
        ((Nat.pow 4 (2 * zz_iroot 2 N)) ^ (Nat.log2 N - 1))%nat.
      * apply Nat.pow_le_mono_l. exact Htail.
      * rewrite (Nat.pow_mul_r 4 (2 * zz_iroot 2 N) (Nat.log2 N - 1)).
        apply Nat.le_refl.
  - (* order N = 1: the fold is the empty product 1 *)
    assert (Hl0 : Nat.log2 N = 0%nat) by lia.
    destruct (Nat.log2_spec N ltac:(lia)) as [Hl1 Hl2].
    rewrite Hl0 in Hl2. cbn [Nat.pow] in Hl2.
    assert (HN1 : N = 1%nat) by lia.
    rewrite HN1. unfold zz_psi.
    replace (Nat.log2 1)%nat with 0%nat by reflexivity.
    cbn [zz_psi_prod].
    replace (2 * zz_iroot 2 1 * (0 - 1))%nat with 0%nat by lia.
    rewrite Nat.pow_0_r, Nat.mul_1_r.
    unfold pec_prim. apply (pec_prod_ge1 (pec_win 1 (1 - 1))).
    intros x Hx. destruct (pec_win_in 1 (1 - 1) x Hx) as [_ [Hx2 _]]. lia.
Qed.

(* ================= Section 4. Certification face ================= *)

Print Assumptions zz_psi_prod_le.
Print Assumptions zz_psi_bound.
Print Assumptions zz_psi_bound_pow.
Print Assumptions zz_psi_bound_tail.

From Stdlib Require Import Extraction.
Separate Extraction zz_psi_prod_le zz_psi_bound zz_psi_bound_pow
  zz_psi_bound_tail.
