(* ==========================================================================
   Module: piu_zz_pnt_qexp
   Mission: Q-exponential certificate machinery for the effective-PNT
     consumption chain. (i) The Taylor partial sums of the exponential
     (reused from the certified tree module S03_QExp) are monotone in the
     truncation order for nonnegative arguments, and the numeric anchor
     exp_partial 40 (20) < 664,000,000 holds — feeding the
     eps0 = 1/6600 constant-normalization step of the Dusart input slot
     (ln(6.64e8) >= 20 since e^20 < 6.64e8, and 20^3 = 8000 >= 6600).
     (ii) The Taylor remainder upper bound: for 0 <= x < n + 2 and
     2 <= n, exp_partial (n+J) x <= exp_partial n x * (n+2)/((n+2) - x)
     — the tail of the partial-sum family is majorized by a geometric
     series of ratio x/(n+2), and the final step uses x <= n*(n+1),
     which follows from x < n+2 <= n*(n+1).
   Dependencies: S03_QExp (exp_partial, q_pow, q_fact, q_pow_fact_nonneg),
     piu_zz_padic_clearing (BidT), piu_zz_poincare_engine (QleT', qleT_intro,
     QeqT/QleT' transitivity bridges), Stdlib QArith/ZArith/Arith/Lia.
   References: the two-sided effective theta bound input slot
     (kb34 statement draft, section 4): the integer certificates
     bracketing e^{(1 -+ eps0) M} consume (i) the partial-sum monotone
     family for the lower side and (ii) the Taylor remainder upper bound
     — both sides are discharged by the lemmas of this module.
   Constructivity: statement faces Set-carried (QleT', BidT); the reused
     S03_QExp definitions are transparent Fixpoints; numeric steps close
     by vm_compute on boolean comparisons; every lemma closes with a full
     proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <this directory> ""
     piu_zz_pnt_qexp.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import QArith ZArith Arith PArith Lia Bool.
Require Import S03_QExp.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.

Local Open Scope Q_scope.

(* ================= Section 1. Partial-sum monotonicity ================= *)

(* Node B5.2 (born face): for x >= 0 the Taylor partial sums of the
   exponential are monotone in the truncation order — each refinement
   appends the nonnegative term x^(S n) / (S n)!. This monotone family
   is the lower-side certificate machine: every partial sum is a
   computable rational under-estimate of e^x. *)
Lemma zz_qle_add_r0 : forall a t : Q, Qle 0 t -> Qle a (a + t).
Proof.
  intros a t H. rewrite <- (Qplus_0_r a) at 1.
  apply (proj2 (Qplus_le_r 0 t a)). exact H.
Qed.

Theorem zz_qexp_partial_mono : forall (x : Q) (n : nat),
  QleT' (Qmake 0 1) x ->
  QleT' (exp_partial n x) (exp_partial (S n) x).
Proof.
  intros x n Hx0.
  destruct Hx0 as [Hx0].
  pose proof (q_pow_fact_nonneg x (S n) Hx0) as HT.
  apply qleT_intro. cbn [exp_partial].
  apply zz_qle_add_r0. exact HT.
Qed.

(* ============ Section 2. Taylor remainder upper bound ============ *)

(* Upper-side certificate machine: with r = x/(n+2) and 2 <= n, the
   partial sums beyond level n grow by at most a factor r per level, so
   the tail beyond n is majorized by the geometric series
   t_{n+1} * (1 + r + ... + r^{J-1}), and the geometric sum is bounded
   by (n+2)/((n+2) - x). The last-step inequality uses the side bound
   x <= n * (n+1), which follows from x < n + 2 <= n * (n+1) for n >= 2.
   The premise (2 <= n) is necessary: for n <= 1 the ratio bound
   x < n + 2 does not force the per-level decay, and the statement
   fails (e.g. n = 0, x = 1, J = 2). *)

Lemma zz_qle_add : forall a b c d : Q, Qle a b -> Qle c d -> Qle (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd.
  apply (Qle_trans _ (a + d)).
  - apply (proj2 (Qplus_le_r c d a)). exact Hcd.
  - apply (proj2 (Qplus_le_l a b d)). exact Hab.
Qed.

Lemma zz_qmult_inv_l : forall a : Q, ~ a == 0 -> /a * a == 1.
Proof.
  intros a Ha. rewrite (Qmult_comm (/a) a). apply Qmult_inv_r. exact Ha.
Qed.

Definition zz_qterm (x : Q) (k : nat) : Q := q_pow x k / q_fact k.

Fixpoint qpown (r : Q) (j : nat) : Q :=
  match j with
  | O => 1
  | S j' => qpown r j' * r
  end.

Fixpoint zz_qgeom (r : Q) (J : nat) : Q :=
  match J with
  | O => 0
  | S J' => zz_qgeom r J' + qpown r J'
  end.

Lemma zz_qmul_neq0 : forall a b : Q, ~ a == 0 -> ~ b == 0 -> ~ a * b == 0.
Proof.
  intros a b Ha Hb Heq.
  apply Hb.
  assert (Hid : b == /a * (a * b)).
  { rewrite (Qmult_assoc (/a) a b).
    rewrite (zz_qmult_inv_l a Ha).
    symmetry. apply Qmult_1_l. }
  rewrite Hid, Heq, Qmult_0_r. reflexivity.
Qed.

Lemma zz_qfact_pos : forall k : nat, 0 < q_fact k.
Proof.
  intro k. induction k as [|k IH].
  - cbn [q_fact]. unfold Qlt, Qnum, Qden. cbn. lia.
  - cbn [q_fact]. apply Qmult_lt_0_compat.
    + unfold Qlt, Qnum, Qden. cbn. lia.
    + exact IH.
Qed.

Lemma zz_qfact_neq0 : forall k : nat, ~ q_fact k == 0.
Proof.
  intro k. induction k as [|k IH].
  - cbn [q_fact]. intro Hc. unfold Qeq, Qnum, Qden in Hc. cbn in Hc. lia.
  - cbn [q_fact]. apply zz_qmul_neq0.
    + intro Hc. unfold Qeq, Qnum, Qden in Hc. cbn in Hc. lia.
    + exact IH.
Qed.

Lemma zz_qle0_add : forall a b : Q, Qle 0 a -> Qle 0 b -> Qle 0 (a + b).
Proof.
  intros a b Ha Hb.
  assert (E : a + 0 == a) by ring.
  apply (Qle_trans _ (a + 0)).
  - rewrite E. exact Ha.
  - apply (proj2 (Qplus_le_r 0 b a)). exact Hb.
Qed.

Lemma zz_qexp_ge_0 : forall (x : Q) (m : nat),
  Qle 0 x -> Qle 0 (exp_partial m x).
Proof.
  intros x m Hx. induction m as [|m IH].
  - cbn [exp_partial]. unfold Qle. cbn. lia.
  - cbn [exp_partial]. apply zz_qle0_add.
    + exact IH.
    + apply q_pow_fact_nonneg. exact Hx.
Qed.

Lemma zz_qle_add_l0 : forall t a : Q, Qle 0 t -> Qle a (t + a).
Proof.
  intros t a H. rewrite Qplus_comm. apply zz_qle_add_r0. exact H.
Qed.

Lemma zz_qterm_0 : forall x : Q, zz_qterm x 0 == 1.
Proof. intro x. unfold zz_qterm. cbn [q_pow q_fact]. reflexivity. Qed.

Lemma zz_qterm_S_mul : forall (x : Q) (k : nat),
  zz_qterm x (S k) == zz_qterm x k * (x / ((Z.of_nat k + 1) # 1)).
Proof.
  intros x k. unfold zz_qterm. cbn [q_pow q_fact].
  rewrite Nat2Z.inj_succ.
  change (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1)%Z.
  unfold Qdiv. rewrite Qinv_mult_distr. ring.
Qed.

Lemma zz_qterm_pos : forall (x : Q) (k : nat), Qle 0 x -> Qle 0 (zz_qterm x k).
Proof.
  intros x k Hx. unfold zz_qterm. apply q_pow_fact_nonneg. exact Hx.
Qed.

Lemma zz_qexp_ge_last : forall (x : Q) (m : nat),
  Qle 0 x -> Qle (zz_qterm x m) (exp_partial m x).
Proof.
  intros x m Hx. induction m as [|m IH].
  - rewrite zz_qterm_0. cbn [exp_partial]. apply Qle_refl.
  - cbn [exp_partial]. unfold zz_qterm.
    apply zz_qle_add_l0. apply zz_qexp_ge_0. exact Hx.
Qed.

Lemma zz_qexp_ge_two_terms : forall (x : Q) (n : nat),
  Qle 0 x -> (1 <= n)%nat ->
  Qle (zz_qterm x (n - 1) + zz_qterm x n) (exp_partial n x).
Proof.
  intros x n Hx Hn. destruct n as [|m]; [lia |].
  cbn [exp_partial].
  replace (S m - 1)%nat with m by lia.
  unfold zz_qterm.
  apply zz_qle_add.
  - apply zz_qexp_ge_last. exact Hx.
  - apply Qle_refl.
Qed.

Lemma zz_qpown_pos : forall (r : Q) (j : nat), Qle 0 r -> Qle 0 (qpown r j).
Proof.
  intros r j Hr. induction j as [|j IH].
  - cbn [qpown]. unfold Qle. cbn. lia.
  - cbn [qpown]. apply Qmult_le_0_compat; assumption.
Qed.

Lemma zz_qgeom_mult : forall (r : Q) (J : nat),
  (1 - r) * zz_qgeom r J == 1 - qpown r J.
Proof.
  intros r J. induction J as [|J IH].
  - cbn [zz_qgeom qpown]. ring.
  - cbn [zz_qgeom qpown].
    rewrite (Qmult_comm (1 - r) (zz_qgeom r J + qpown r J)).
    rewrite (Qmult_plus_distr_l (zz_qgeom r J) (qpown r J) (1 - r)).
    rewrite (Qmult_comm (zz_qgeom r J) (1 - r)).
    rewrite IH. ring.
Qed.

Lemma zz_qdiv_le : forall (x a b : Q), 0 <= x -> 0 < a -> a <= b -> x / b <= x / a.
Proof.
  intros x a b Hx Ha Hab.
  unfold Qdiv.
  apply (Qle_trans _ ((/b) * x)).
  - rewrite (Qmult_comm x (/b)). apply Qle_refl.
  - rewrite (Qmult_comm x (/a)). apply Qmult_le_compat_r; [| exact Hx].
    destruct (Qlt_le_dec a b) as [Hlt | Heq].
    + apply (Qlt_le_weak (/b) (/a)).
      apply (proj1 (Qinv_lt_contravar a b Ha
                      ltac:(apply (Qlt_trans 0 a b); [exact Ha | exact Hlt]))).
      exact Hlt.
    + rewrite (Qle_antisym a b Hab Heq). apply Qle_refl.
Qed.

Lemma zz_qdiv_pos : forall (x a : Q), 0 <= x -> 0 < a -> 0 <= x / a.
Proof.
  intros x a Hx Ha. unfold Qdiv. apply Qmult_le_0_compat.
  - exact Hx.
  - apply Qinv_le_0_compat. apply (Qlt_le_weak 0 a). exact Ha.
Qed.

Lemma zz_qpow_pos : forall (x : Q) (m : nat), Qle 0 x -> Qle 0 (q_pow x m).
Proof.
  intros x m Hx. induction m as [|m IH].
  - cbn [q_pow]. unfold Qle. cbn. lia.
  - cbn [q_pow]. apply Qmult_le_0_compat; assumption.
Qed.

Lemma zz_qterm_decay : forall (x : Q) (n j : nat),
  Qle 0 x -> (2 <= n)%nat ->
  Qle (zz_qterm x (n + 1 + j))
      (zz_qterm x (n + 1) * qpown (x / ((Z.of_nat (n + 2)) # 1)) j).
Proof.
  intros x n j Hx Hn. induction j as [|j IH].
  - rewrite Nat.add_0_r.
    cbn [qpown]. unfold zz_qterm. rewrite Qmult_1_r. apply Qle_refl.
  - assert (Hstep : zz_qterm x (n + 1 + S j)
                    == zz_qterm x (n + 1 + j)
                       * (x / ((Z.of_nat (n + 1 + j) + 1) # 1))).
    { replace (n + 1 + S j)%nat with (S (n + 1 + j)) by lia.
      apply zz_qterm_S_mul. }
    rewrite Hstep.
    assert (Hratio : x / ((Z.of_nat (n + 1 + j) + 1) # 1)
                     <= x / ((Z.of_nat (n + 2)) # 1)).
    { apply zz_qdiv_le.
      - exact Hx.
      - unfold Qlt, Qnum, Qden; cbn; lia.
      - unfold Qle, Qnum, Qden; cbn; lia. }
    assert (Hchain : zz_qterm x (n + 1 + j)
                       * (x / ((Z.of_nat (n + 1 + j) + 1) # 1))
                     <= zz_qterm x (n + 1)
                        * qpown (x / ((Z.of_nat (n + 2)) # 1)) (S j)).
    { apply (Qle_trans _ (zz_qterm x (n + 1)
                          * qpown (x / ((Z.of_nat (n + 2)) # 1)) j
                          * (x / ((Z.of_nat (n + 1 + j) + 1) # 1)))).
      - apply Qmult_le_compat_r.
        + exact IH.
        + apply zz_qdiv_pos.
          * exact Hx.
          * unfold Qlt, Qnum, Qden; cbn; lia.
      - apply (Qle_trans _ (zz_qterm x (n + 1)
                            * qpown (x / ((Z.of_nat (n + 2)) # 1)) j
                            * (x / ((Z.of_nat (n + 2)) # 1)))).
        + rewrite (Qmult_comm (zz_qterm x (n + 1)
                    * qpown (x / ((Z.of_nat (n + 2)) # 1)) j)
                    (x / ((Z.of_nat (n + 1 + j) + 1) # 1))).
          rewrite (Qmult_comm (zz_qterm x (n + 1)
                      * qpown (x / ((Z.of_nat (n + 2)) # 1)) j)
                      (x / ((Z.of_nat (n + 2)) # 1))).
          apply Qmult_le_compat_r.
          * exact Hratio.
          * apply Qmult_le_0_compat.
            -- unfold zz_qterm. apply q_pow_fact_nonneg. exact Hx.
            -- apply zz_qpown_pos. apply zz_qdiv_pos.
               ++ exact Hx.
               ++ unfold Qlt, Qnum, Qden; cbn; lia.
        + assert (Hrssoc : zz_qterm x (n + 1)
                           * qpown (x / ((Z.of_nat (n + 2)) # 1)) j
                           * (x / ((Z.of_nat (n + 2)) # 1))
                           == zz_qterm x (n + 1)
                              * (qpown (x / ((Z.of_nat (n + 2)) # 1)) j
                                 * (x / ((Z.of_nat (n + 2)) # 1)))) by ring.
          rewrite Hrssoc. apply Qle_refl.
    }
    exact Hchain.
Qed.

Lemma zz_qexp_step_bound : forall (x : Q) (n J : nat),
  Qle 0 x -> (2 <= n)%nat ->
  Qle (exp_partial (n + J) x)
      (exp_partial n x
       + zz_qterm x (n + 1) * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J).
Proof.
  intros x n J Hx Hn. induction J as [|J IH].
  - replace (n + 0)%nat with n by lia. cbn [zz_qgeom].
    apply zz_qle_add_r0. rewrite Qmult_0_r. apply Qle_refl.
  - assert (Hsplit : exp_partial (n + S J) x
                     == exp_partial (n + J) x + zz_qterm x (S (n + J))).
    { replace (n + S J)%nat with (S (n + J)) by lia.
      cbn [exp_partial]. unfold zz_qterm. reflexivity. }
    rewrite Hsplit.
    replace (S (n + J))%nat with ((n + 1 + J)%nat) by lia.
    cbn [zz_qgeom].
    assert (Hd : zz_qterm x (n + 1)
                 * (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                    + qpown (x / ((Z.of_nat (n + 2)) # 1)) J)
                 == zz_qterm x (n + 1) * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                    + zz_qterm x (n + 1) * qpown (x / ((Z.of_nat (n + 2)) # 1)) J).
    { rewrite (Qmult_comm (zz_qterm x (n + 1))
                (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                 + qpown (x / ((Z.of_nat (n + 2)) # 1)) J)).
      rewrite (Qmult_plus_distr_l (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                                  (qpown (x / ((Z.of_nat (n + 2)) # 1)) J)
                                  (zz_qterm x (n + 1))).
      rewrite (Qmult_comm (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                (zz_qterm x (n + 1))).
      rewrite (Qmult_comm (qpown (x / ((Z.of_nat (n + 2)) # 1)) J)
                (zz_qterm x (n + 1))).
      reflexivity. }
    rewrite Hd.
    apply (Qle_trans _ ((exp_partial n x
                          + zz_qterm x (n + 1)
                          * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                         + zz_qterm x (n + 1 + J))).
    + apply (proj2 (Qplus_le_l (exp_partial (n + J) x)
                  (exp_partial n x
                   + zz_qterm x (n + 1)
                   * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                  (zz_qterm x (n + 1 + J)))).
      exact IH.
    + assert (Hassoc : (exp_partial n x
                        + zz_qterm x (n + 1)
                        * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                       + zz_qterm x (n + 1 + J)
                       == exp_partial n x
                          + (zz_qterm x (n + 1)
                             * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                             + zz_qterm x (n + 1 + J))) by ring.
      rewrite Hassoc.
      apply zz_qle_add; [apply Qle_refl |].
      apply zz_qle_add; [apply Qle_refl | apply (zz_qterm_decay x n J Hx Hn)].
Qed.

Lemma zz_qmul_div_r : forall (u a : Q), ~ a == 0 -> (1 - u / a) * a == a - u.
Proof.
  intros u a Ha. unfold Qdiv.
  assert (Hd : (1 - u * /a) * a == 1 * a - (u * /a) * a) by ring.
  rewrite Hd.
  rewrite <- (Qmult_assoc u (/a) a).
  rewrite (zz_qmult_inv_l a Ha).
  ring.
Qed.

Lemma zz_qgeom_tail_le : forall (x : Q) (n J : nat),
  Qle 0 x -> (2 <= n)%nat ->
  zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J * (((Z.of_nat (n + 2)) # 1) - x)
  <= ((Z.of_nat (n + 2)) # 1).
Proof.
  intros x n J Hx Hn.
  assert (Hapos : 0 < ((Z.of_nat (n + 2)) # 1))
    by (unfold Qlt, Qnum, Qden; cbn; lia).
  assert (Hr0 : 0 <= x / ((Z.of_nat (n + 2)) # 1))
    by (apply zz_qdiv_pos; [exact Hx | exact Hapos]).
  assert (Hane : ~ ((Z.of_nat (n + 2)) # 1) == 0).
  { intro Hc. unfold Qeq, Qnum, Qden in Hc. cbn in Hc. lia. }
  assert (Hshape : ((Z.of_nat (n + 2)) # 1) - x
                   == (1 - x / ((Z.of_nat (n + 2)) # 1))
                      * ((Z.of_nat (n + 2)) # 1)).
  { apply (eq_sym (zz_qmul_div_r x _ Hane)). }
  apply (Qle_trans _ ((zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                       * (1 - x / ((Z.of_nat (n + 2)) # 1)))
                      * ((Z.of_nat (n + 2)) # 1))).
  - assert (Hjoin : zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                      * (((Z.of_nat (n + 2)) # 1) - x)
                    == (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                        * (1 - x / ((Z.of_nat (n + 2)) # 1)))
                       * ((Z.of_nat (n + 2)) # 1)).
    { rewrite Hshape. ring. }
    rewrite Hjoin. apply Qle_refl.
  - apply (Qle_trans _ (1 * ((Z.of_nat (n + 2)) # 1))).
    + apply Qmult_le_compat_r.
      * rewrite (Qmult_comm (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                  (1 - x / ((Z.of_nat (n + 2)) # 1))).
        rewrite zz_qgeom_mult.
        apply (Qle_trans _ ((1 - qpown (x / ((Z.of_nat (n + 2)) # 1)) J)
                            + qpown (x / ((Z.of_nat (n + 2)) # 1)) J)).
        -- apply zz_qle_add_r0. apply zz_qpown_pos. exact Hr0.
        -- assert (Hone : ((1 - qpown (x / ((Z.of_nat (n + 2)) # 1)) J)
                           + qpown (x / ((Z.of_nat (n + 2)) # 1)) J) == 1)
             by ring.
           rewrite Hone. apply Qle_refl.
      * unfold Qle. apply (Qlt_le_weak 0). exact Hapos.
    + rewrite Qmult_1_l. apply Qle_refl.
Qed.

Lemma zz_qdiv_mul_cancel : forall (u v F : Q), ~ F == 0 -> (u / F) * v * F == u * v.
Proof.
  intros u v F HF. unfold Qdiv.
  rewrite <- (Qmult_assoc (u * /F) v F).
  rewrite (Qmult_comm v F).
  rewrite (Qmult_assoc (u * /F) F v).
  rewrite <- (Qmult_assoc u (/F) F).
  rewrite (zz_qmult_inv_l F HF).
  ring.
Qed.

Lemma zz_qmake_mul : forall a b : Z, (a # 1) * (b # 1) == ((a * b) # 1).
Proof. intros a b. reflexivity. Qed.



(* Helper: a product bound by D with D > 0 converts to a quotient bound. *)
Lemma zz_qmul_d_le : forall (x W D : Q), 0 < D -> x * D <= W -> x <= W / D.
Proof.
  intros x W D HD Hle. unfold Qdiv.
  assert (HDne : ~ D == 0).
  { intro Hc. rewrite Hc in HD. unfold Qlt in HD. cbn in HD. discriminate. }
  assert (HDinv : D * /D == 1).
  { rewrite (Qmult_comm D (/D)). apply zz_qmult_inv_l. exact HDne. }
  apply (Qle_trans _ (x * D * /D)).
  - rewrite <- (Qmult_assoc x D (/D)). rewrite HDinv. rewrite Qmult_1_r. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact Hle.
    + apply Qinv_le_0_compat. apply (Qlt_le_weak 0). exact HD.
Qed.

Lemma zz_qexp_core_claim : forall (x : Q) (n : nat),
  Qle 0 x -> x <= ((Z.of_nat n * (Z.of_nat n + 1)) # 1) -> (2 <= n)%nat ->
  Qle (zz_qterm x (n + 1) * ((Z.of_nat (n + 2)) # 1))
      (exp_partial n x * x).
Proof.
  intros x n Hx Hzle Hn. destruct n as [|[|m]]; try lia.
  assert (HF2pos : 0 < q_fact (S (S (S m)))) by apply zz_qfact_pos.
  assert (Hdecomp : q_fact (S (S (S m)))
                    == q_fact (S m)
                       * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)).
  { cbn [q_fact].
    rewrite (Qmult_assoc ((Z.of_nat (S (S (S m))) # 1))
                         ((Z.of_nat (S (S m)) # 1))
                         (((Z.of_nat (S m) # 1) * q_fact m))).
    rewrite (zz_qmake_mul (Z.of_nat (S (S (S m)))) (Z.of_nat (S (S m)))).
    rewrite (Qmult_assoc (((Z.of_nat (S (S (S m))) * Z.of_nat (S (S m))) # 1))
                         ((Z.of_nat (S m) # 1))
                         (q_fact m)).
    rewrite (zz_qmake_mul ((Z.of_nat (S (S (S m))) * Z.of_nat (S (S m)))%Z) (Z.of_nat (S m))).
    rewrite (Qmult_comm (Z.of_nat (S m) # 1) (q_fact m)).
    rewrite <- (Qmult_assoc (q_fact m)
                            ((Z.of_nat (S m) # 1))
                            ((((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))).
    rewrite (zz_qmake_mul (Z.of_nat (S m))
                          (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m)))%Z)).
    rewrite !Nat2Z.inj_succ.
    assert (Hc1 : Z.succ (Z.succ (Z.succ (Z.of_nat m))) = (Z.of_nat m + 3)%Z) by lia.
    assert (Hc2 : Z.succ (Z.succ (Z.of_nat m)) = (Z.of_nat m + 2)%Z) by lia.
    assert (Hc3 : Z.succ (Z.of_nat m) = (Z.of_nat m + 1)%Z) by lia.
    rewrite Hc1, Hc2, Hc3.
    assert (Hc4 : (((Z.of_nat m + 3) * (Z.of_nat m + 2)) * (Z.of_nat m + 1))%Z
                  = ((Z.of_nat m + 1) * (((Z.of_nat m + 2) + 1) * (Z.of_nat m + 2)))%Z)
      by ring.
    rewrite Hc4. apply Qmult_comm. }
  assert (Hqp : q_pow x (S (S (S m))) == q_pow x (S (S m)) * x)
    by (cbn [q_pow]; ring).
  assert (Hqp2 : q_pow x (S (S m)) == q_pow x (S m) * x)
    by (cbn [q_pow]; ring).
  assert (Hqf : q_fact (S m)
                * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)
                == q_fact (S (S m)) * ((Z.of_nat (S (S (S m)))) # 1)).
  { rewrite <- Hdecomp.
    rewrite (Qmult_comm (q_fact (S (S m))) ((Z.of_nat (S (S (S m)))) # 1)).
    reflexivity. }
  assert (P1 : (q_pow x (S m) / q_fact (S m))
               * (x * (q_fact (S m)
                       * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)))
               == q_pow x (S m)
                  * (x * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))).
  { rewrite (Qmult_comm (q_fact (S m))
              ((((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))).
    rewrite (Qmult_assoc x
                ((((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))
                (q_fact (S m))).
    rewrite (Qmult_assoc (q_pow x (S m) / q_fact (S m))
                (x * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))
                (q_fact (S m))).
    rewrite (zz_qdiv_mul_cancel (q_pow x (S m))
                (x * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))
                (q_fact (S m)) (zz_qfact_neq0 (S m))).
    reflexivity. }
  assert (P2 : (q_pow x (S (S m)) / q_fact (S (S m)))
               * (x * (q_fact (S m)
                       * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)))
               == q_pow x (S (S m)) * (x * ((Z.of_nat (S (S (S m)))) # 1))).
  { rewrite Hqf.
    rewrite (Qmult_comm (q_fact (S (S m))) ((Z.of_nat (S (S (S m)))) # 1)).
    rewrite (Qmult_assoc x ((Z.of_nat (S (S (S m)))) # 1) (q_fact (S (S m)))).
    rewrite (Qmult_assoc (q_pow x (S (S m)) / q_fact (S (S m)))
                (x * ((Z.of_nat (S (S (S m)))) # 1)) (q_fact (S (S m)))).
    rewrite (zz_qdiv_mul_cancel (q_pow x (S (S m)))
                (x * ((Z.of_nat (S (S (S m)))) # 1))
                (q_fact (S (S m))) (zz_qfact_neq0 (S (S m)))).
    reflexivity. }
  assert (HsplitQ : ((Z.of_nat (S (S (S (S m))))) # 1)
                    == ((Z.of_nat (S (S (S m)))) # 1) + 1).
  { assert (Hw : forall w : Z, (w + 1)%Z # 1 == (w # 1) + 1).
    { intro w. unfold Qeq, Qplus, Qnum, Qden. cbn. ring. }
    assert (Hz4 : Z.of_nat (S (S (S (S m)))) = (Z.of_nat (S (S (S m))) + 1)%Z) by lia.
    rewrite Hz4. apply Hw. }
  assert (Hge : Qle (zz_qterm x (S m) + zz_qterm x (S (S m)))
                    (exp_partial (S (S m)) x)).
  { pose proof (zz_qexp_ge_two_terms x (S (S m)) Hx ltac:(lia)) as HH.
    replace (S (S m) - 1)%nat with (S m)%nat in HH by lia.
    exact HH. }
  apply (Qle_trans _ ((zz_qterm x (S m) + zz_qterm x (S (S m))) * x)).
  - replace (S (S m) + 1)%nat with (S (S (S m)))%nat by lia.
    replace (S (S m) + 2)%nat with (S (S (S (S m))))%nat by lia.
    apply (proj1 (Qmult_le_r _ _ _ HF2pos)).
    unfold zz_qterm.
    rewrite (zz_qdiv_mul_cancel (q_pow x (S (S (S m))))
                                ((Z.of_nat (S (S (S (S m))))) # 1)
                                (q_fact (S (S (S m)))) ltac:(apply zz_qfact_neq0)).
    rewrite Hdecomp.
    rewrite <- (Qmult_assoc
                  ((q_pow x (S m) / q_fact (S m)) + (q_pow x (S (S m)) / q_fact (S (S m))))
                  x
                  (q_fact (S m)
                   * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))).
    rewrite (Qmult_plus_distr_l (q_pow x (S m) / q_fact (S m))
                                (q_pow x (S (S m)) / q_fact (S (S m)))
                                (x * (q_fact (S m)
                                      * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)))).
    rewrite P1. rewrite P2.
    rewrite Hqp. rewrite HsplitQ.
    rewrite (Qmult_plus_distr_r (q_pow x (S (S m)) * x)
                                ((Z.of_nat (S (S (S m)))) # 1) 1).
    assert (Hswap : (q_pow x (S (S m)) * x) * ((Z.of_nat (S (S (S m)))) # 1)
                    + (q_pow x (S (S m)) * x) * 1
                    == (q_pow x (S (S m)) * x) * 1
                       + (q_pow x (S (S m)) * x) * ((Z.of_nat (S (S (S m)))) # 1)) by ring.
    rewrite Hswap.
    apply zz_qle_add.
    + rewrite Qmult_1_r. rewrite Hqp2.
      assert (Hc5 : q_pow x (S m) * x * x == x * (q_pow x (S m) * x)) by ring.
      assert (Hc6 : q_pow x (S m)
                    * (x * (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1))
                    == (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)
                       * (q_pow x (S m) * x)) by ring.
      rewrite Hc5. rewrite Hc6.
      apply Qmult_le_compat_r.
      * apply (Qle_trans x
                  ((Z.of_nat (S (S m)) * (Z.of_nat (S (S m)) + 1)) # 1)
                  (((Z.of_nat (S (S m)) + 1) * Z.of_nat (S (S m))) # 1)).
        -- exact Hzle.
        -- unfold Qle, Qnum, Qden; cbn; nia.
      * apply Qmult_le_0_compat.
        -- apply zz_qpow_pos. exact Hx.
        -- exact Hx.
    + assert (Hass1 : q_pow x (S (S m)) * x * ((Z.of_nat (S (S (S m)))) # 1)
                      == q_pow x (S (S m)) * (x * ((Z.of_nat (S (S (S m)))) # 1))) by ring.
      rewrite Hass1. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact Hge.
    + exact Hx.
Qed.

Theorem zz_qexp_upper : forall (x : Q) (n J : nat),
  QleT' (Qmake 0 1) x -> QltT x (Qmake (Z.of_nat (n + 2)) 1) -> (2 <= n)%nat ->
  QleT' (exp_partial (n + J) x)
        (exp_partial n x
         * (((Z.of_nat (n + 2)) # 1) / (((Z.of_nat (n + 2)) # 1) - x))).
Proof.
  intros x n J Hx0 Hxn Hn.
  destruct Hx0 as [Hx0]. destruct Hxn as [Hxn].
  assert (HD : 0 < (((Z.of_nat (n + 2)) # 1) - x)).
  { destruct (Qlt_le_dec 0 (((Z.of_nat (n + 2)) # 1) - x)) as [Hpos | Hneg].
    - exact Hpos.
    - exfalso.
      assert (Hdx : (((Z.of_nat (n + 2)) # 1) - x) + x == ((Z.of_nat (n + 2)) # 1)) by ring.
      assert (Hstep : (((Z.of_nat (n + 2)) # 1) - x) + x <= x).
      { assert (Hzero : 0 + x == x) by ring.
        apply (Qle_trans _ (0 + x)).
        - apply zz_qle_add; [exact Hneg | apply Qle_refl].
        - rewrite Hzero. apply Qle_refl. }
      rewrite Hdx in Hstep.
      exact (Qlt_irrefl x (Qlt_le_trans x _ x Hxn Hstep)). }
  assert (Hxle : x <= ((Z.of_nat n * (Z.of_nat n + 1)) # 1)).
  { apply (Qle_trans x ((Z.of_nat (n + 2)) # 1)).
    - apply (Qlt_le_weak x). exact Hxn.
    - unfold Qle, Qnum, Qden; cbn; nia. }
  apply qleT_intro.
  assert (Htarget : exp_partial n x
                    * (((Z.of_nat (n + 2)) # 1) / (((Z.of_nat (n + 2)) # 1) - x))
                    == (exp_partial n x * ((Z.of_nat (n + 2)) # 1))
                       / (((Z.of_nat (n + 2)) # 1) - x)).
  { unfold Qdiv. ring. }
  rewrite Htarget.
  apply zz_qmul_d_le.
  - exact HD.
  - apply (Qle_trans _
            ((exp_partial n x
              + zz_qterm x (n + 1) * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
             * (((Z.of_nat (n + 2)) # 1) - x))).
    + apply Qmult_le_compat_r.
      * apply zz_qexp_step_bound; assumption.
      * apply (Qlt_le_weak 0). exact HD.
    + rewrite (Qmult_plus_distr_l (exp_partial n x)
                (zz_qterm x (n + 1) * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                (((Z.of_nat (n + 2)) # 1) - x)).
      apply (Qle_trans _ (exp_partial n x * (((Z.of_nat (n + 2)) # 1) - x)
                          + zz_qterm x (n + 1) * ((Z.of_nat (n + 2)) # 1))).
      * apply zz_qle_add.
        -- apply Qle_refl.
        -- assert (Htt : (zz_qterm x (n + 1) * zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J)
                         * (((Z.of_nat (n + 2)) # 1) - x)
                         == (zz_qgeom (x / ((Z.of_nat (n + 2)) # 1)) J
                             * (((Z.of_nat (n + 2)) # 1) - x))
                            * zz_qterm x (n + 1)) by ring.
           assert (Htt2 : zz_qterm x (n + 1) * ((Z.of_nat (n + 2)) # 1)
                          == ((Z.of_nat (n + 2)) # 1) * zz_qterm x (n + 1)) by ring.
           rewrite Htt. rewrite Htt2.
           apply Qmult_le_compat_r.
           ++ apply zz_qgeom_tail_le; assumption.
           ++ apply zz_qterm_pos. exact Hx0.
      * apply (Qle_trans _ (exp_partial n x * (((Z.of_nat (n + 2)) # 1) - x)
                            + exp_partial n x * x)).
        -- apply zz_qle_add.
           ++ apply Qle_refl.
           ++ apply (zz_qexp_core_claim x n Hx0 Hxle Hn).
        -- assert (Hjoin : exp_partial n x * (((Z.of_nat (n + 2)) # 1) - x)
                           + exp_partial n x * x
                           == exp_partial n x * (((Z.of_nat (n + 2)) # 1) - x + x)) by ring.
           rewrite Hjoin.
           assert (Hdx2 : (((Z.of_nat (n + 2)) # 1) - x + x) == ((Z.of_nat (n + 2)) # 1)) by ring.
           rewrite Hdx2. apply Qle_refl.
Qed.

Print Assumptions zz_qexp_upper.
Print Assumptions zz_qexp_core_claim.

(* ================= Section 3. Numeric anchor ================= *)

(* Node B5.3 (born face): the 41st Taylor partial sum of e^20 lies below
   664,000,000; the exact value is 485,152,859.44... (true e^20 =
   485,165,195.40...), cross-checked by independent exact rational
   arithmetic before this statement was fixed. Consumption: with
   X0 = 664,000,000 this yields ln X0 >= 20 once phase 3 discharges the
   analytic side, and 20^3 = 8000 >= 6600 fixes eps0 = 1/6600. *)
Theorem zz_qexp_e20_below_X0 :
  BidT (Qle_bool (exp_partial 40%nat (Qmake 20 1)) (Qmake 664000000 1)).
Proof.
  apply BidT_intro. vm_compute. reflexivity.
Qed.

(* ================= Section 4. Certification face ================= *)

Print Assumptions zz_qexp_partial_mono.
Print Assumptions zz_qexp_e20_below_X0.
Print Assumptions zz_qexp_core_claim.
Print Assumptions zz_qexp_upper.

From Stdlib Require Import Extraction.
Separate Extraction exp_partial q_pow q_fact qpown
  zz_qle_add_r0 zz_qle_add zz_qmult_inv_l zz_qterm zz_qgeom
  zz_qmul_neq0 zz_qfact_pos zz_qfact_neq0 zz_qle0_add zz_qexp_ge_0
  zz_qle_add_l0 zz_qterm_0 zz_qterm_S_mul zz_qterm_pos zz_qexp_ge_last
  zz_qexp_ge_two_terms zz_qpown_pos zz_qgeom_mult zz_qdiv_le zz_qdiv_pos
  zz_qpow_pos zz_qterm_decay zz_qexp_step_bound zz_qmul_div_r
  zz_qgeom_tail_le zz_qdiv_mul_cancel zz_qmake_mul zz_qmul_d_le
  zz_qexp_partial_mono zz_qexp_core_claim zz_qexp_upper
  zz_qexp_e20_below_X0.
