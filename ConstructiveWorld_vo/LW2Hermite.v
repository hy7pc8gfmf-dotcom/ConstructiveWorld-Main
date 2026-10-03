(* ========================================================================= *)
(* LW2Hermite - the algebraic core of Hermite interpolation: the truncated   *)
(* antiderivative table and the endpoint identity with explicit integer node coefficients. *)
(* 模块名：LW2Hermite.  数学使命：for a rational polynomial f, the truncated  *)
(* antiderivative table eps K f = sum_{k<K} f^{(k)} satisfies the kernel     *)
(* identity eps K f ' = eps K f - f whenever K is at least the table length  *)
(* of f; shifting f by an integer node j and summing the endpoint values     *)
(* over the intervals [j, j+1], 0 <= j <= n, telescopes to an explicit node  *)
(* functional  lambda n f = sum_j sum_k c_{jk} * f^{(k)}(j)  with c_{jk}     *)
(* explicit integers (c = +1 at node 0, -1 at node n+1, 0 elsewhere), and    *)
(* the identity lambda n f = endpoint n f holds for all n and f.  This is    *)
(* the purely polynomial algebraization of Hermite's 1873 integral identity  *)
(* (the exponential weight never appears as a function; it survives only in  *)
(* the coefficient structure).                                               *)
(* 依赖清单：LW0QPoly (QPoly, qpoly_add/scalar/eval/deriv/deriv_iter and     *)
(* their pointwise laws); Stdlib QArith, Lia.  All higher pieces (the        *)
(* coefficient functional layer, the shifted finite sum, the translation     *)
(* t |-> t + c, the antiderivative table) are built below from scratch.      *)
(* 对标行：Hermite 1873 (C. R. Acad. Sci. Paris 77); Niven, Irrational       *)
(* Numbers (1956), corresponding chapter (both registered as cited by the master work order, not re-verified online). *)
(* 构造性注记：every operation is a structurally recursive Fixpoint with      *)
(* computing content (Defined); statements are quantified equations between  *)
(* rational data carried by Qeq, with no logical premises beyond nat         *)
(* orderings; no admitted goals, no classical principles; the exported       *)
(* constants extract to plain Q arithmetic.                                  *)
(* 编译配方：env COQLIB/ROCQLIB set to the Rocq 9.1 library, then            *)
(* "coqc.exe -q -Q . "" LW2Hermite.v" in a sandbox holding LW0QPoly.vo       *)
(* (byte-identical copy of Live_X/LW0QPoly.v, md5 6f836288); coqchk with     *)
(* the same -Q . "" mapping.                                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith Lia Arith.
Require Import LW0QPoly.

(* ------------------------------------------------------------------ *)
(* Section 1.  Small rational-power and Qmake helpers.                 *)
(* ------------------------------------------------------------------ *)

Fixpoint lw2_qpow (x : Q) (m : nat) : Q :=
  match m with
  | 0 % nat => 1
  | S m' => lw2_qpow x m' * x
  end.

Lemma lw2_qpow_0 : forall x, lw2_qpow x 0 == 1.
Proof.
  intros x.
  reflexivity.
Qed.

Lemma lw2_qpow_S : forall x m, lw2_qpow x (S m) == lw2_qpow x m * x.
Proof.
  intros x m.
  reflexivity.
Qed.

Lemma lw2_qmake_add : forall z1 z2 : Z,
  ((z1 # 1)%Q + (z2 # 1)%Q)%Q == ((z1 + z2) # 1)%Q.
Proof.
  intros z1 z2.
  unfold Qeq; cbn [Qplus Qnum Qden]; lia.
Qed.

Lemma lw2_qmake_succ : forall n : nat,
  ((Z.of_nat (S n)) # 1)%Q == (((Z.of_nat n) # 1)%Q + 1)%Q.
Proof.
  intros n.
  assert (Hz : Z.of_nat (S n) = (Z.of_nat n + 1)%Z) by lia.
  rewrite Hz.
  symmetry.
  apply (lw2_qmake_add (Z.of_nat n) 1).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  The coefficient functional layer.                       *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_coef (j : nat) (p : QPoly) {struct p} : Q :=
  match p with
  | nil => 0
  | cons a p' => match j with
                 | 0 % nat => a
                 | S j' => lw0_coef j' p'
                 end
  end.

Fixpoint lw2_fall (j k : nat) : Q :=
  match k with
  | 0 % nat => 1
  | S m => ((Z.of_nat (S j)) # 1)%Q * lw2_fall (S j) m
  end.

Lemma lw0_coef_beyond : forall j p,
  (length p <= j)%nat -> lw0_coef j p == 0.
Proof.
  intros j p.
  revert j.
  induction p as [|a p IH]; intros j Hj.
  - reflexivity.
  - destruct j as [|j'].
    + simpl in Hj; lia.
    + simpl in Hj.
      cbn [lw0_coef].
      apply (IH j').
      lia.
Qed.

Lemma lw0_coef_add : forall p q j,
  lw0_coef j (qpoly_add p q) == lw0_coef j p + lw0_coef j q.
Proof.
  intros p.
  induction p as [|a p IH]; intros q j.
  - cbn [qpoly_add lw0_coef]; ring.
  - destruct q as [|b q'].
    + cbn [qpoly_add lw0_coef]; ring.
    + replace (qpoly_add (cons a p) (cons b q'))
        with (cons (a + b) (qpoly_add p q')) by reflexivity.
      destruct j as [|j'].
      * cbn [lw0_coef]; ring.
      * cbn [lw0_coef].
        rewrite (IH q' j').
        ring.
Qed.

Lemma lw0_coef_scalar : forall a p j,
  lw0_coef j (qpoly_scalar a p) == a * lw0_coef j p.
Proof.
  intros a p.
  induction p as [|b p IH]; intros j.
  - cbn [qpoly_scalar lw0_coef]; ring.
  - cbn [qpoly_scalar lw0_coef].
    destruct j as [|j'].
    + ring.
    + rewrite IH.
      ring.
Qed.

Lemma lw0_coef_deriv : forall p j,
  lw0_coef j (qpoly_deriv p) == ((Z.of_nat (S j)) # 1)%Q * lw0_coef (S j) p.
Proof.
  intros p.
  induction p as [|a p IH]; intros j.
  - cbn [qpoly_deriv lw0_coef]; ring.
  - cbn [qpoly_deriv].
    rewrite lw0_coef_add.
    destruct j as [|j'].
    + cbn [lw0_coef Z.of_nat]; ring.
    + cbn [lw0_coef].
      rewrite (IH j').
      rewrite (lw2_qmake_succ (S j')).
      ring.
Qed.

Lemma lw0_coef_iter_add : forall k u v j,
  lw0_coef j (qpoly_deriv_iter k (qpoly_add u v)) ==
  lw0_coef j (qpoly_deriv_iter k u) + lw0_coef j (qpoly_deriv_iter k v).
Proof.
  intros k.
  induction k as [|k IH]; intros u v j.
  - apply lw0_coef_add.
  - cbn [qpoly_deriv_iter].
    rewrite !lw0_coef_deriv.
    rewrite (IH u v (S j)).
    ring.
Qed.

Lemma lw0_coef_iter_scalar : forall k a p j,
  lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p)) ==
  a * lw0_coef j (qpoly_deriv_iter k p).
Proof.
  intros k a p.
  induction k as [|k IH]; intros j.
  - apply lw0_coef_scalar.
  - cbn [qpoly_deriv_iter].
    rewrite !lw0_coef_deriv.
    rewrite (IH (S j)).
    ring.
Qed.

Lemma lw0_coef_iter_fall : forall k p j,
  lw0_coef j (qpoly_deriv_iter k p) == lw2_fall j k * lw0_coef (j + k) p.
Proof.
  intros k.
  induction k as [|k IH]; intros p j.
  - cbn [qpoly_deriv_iter lw2_fall].
    rewrite Nat.add_0_r.
    ring.
  - cbn [qpoly_deriv_iter].
    rewrite lw0_coef_deriv.
    rewrite (IH p (S j)).
    cbn [lw2_fall].
    assert (Hj : (S j + k = j + S k)%nat) by lia.
    rewrite Hj.
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  The shifted finite sum and the evaluation bridge.       *)
(* ------------------------------------------------------------------ *)

Fixpoint lw2_qsum0 (g : nat -> Q) (n : nat) : Q :=
  match n with
  | 0 % nat => 0
  | S m => lw2_qsum0 g m + g m
  end.

Lemma lw2_qsum0_ext : forall n (g h : nat -> Q),
  (forall j, (j < n)%nat -> g j == h j) ->
  lw2_qsum0 g n == lw2_qsum0 h n.
Proof.
  intros n g h.
  induction n as [|n IH]; intros H.
  - reflexivity.
  - cbn [lw2_qsum0].
    rewrite (H n (Nat.lt_succ_diag_r n)).
    rewrite IH.
    + ring.
    + intros j Hj.
      apply H.
      lia.
Qed.

Lemma lw2_qsum0_add : forall n (g h : nat -> Q),
  lw2_qsum0 (fun j => g j + h j) n == lw2_qsum0 g n + lw2_qsum0 h n.
Proof.
  intros n g h.
  induction n as [|n IH].
  - cbn [lw2_qsum0]; ring.
  - cbn [lw2_qsum0].
    rewrite IH.
    ring.
Qed.

Lemma lw2_qsum0_scale : forall n (g : nat -> Q) c,
  lw2_qsum0 (fun j => c * g j) n == c * lw2_qsum0 g n.
Proof.
  intros n g c.
  induction n as [|n IH].
  - cbn [lw2_qsum0]; ring.
  - cbn [lw2_qsum0].
    rewrite IH.
    ring.
Qed.

Lemma lw2_qsum0_split : forall (F : nat -> Q) (v x : Q) n,
  lw2_qsum0 (fun j => match j with
                      | 0 % nat => v
                      | S j' => F j' * x
                      end) (S n) == v + lw2_qsum0 F n * x.
Proof.
  intros F v x n.
  induction n as [|n IH].
  - cbn [lw2_qsum0].
    ring.
  - cbn [lw2_qsum0].
    rewrite IH.
    ring.
Qed.

Lemma lw2_qsum0_zero : forall n (g : nat -> Q),
  (forall j, (j < n)%nat -> g j == 0) -> lw2_qsum0 g n == 0.
Proof.
  intros n g.
  induction n as [|n IH]; intros H.
  - reflexivity.
  - cbn [lw2_qsum0].
    rewrite (H n (Nat.lt_succ_diag_r n)).
    rewrite IH.
    + ring.
    + intros j Hj.
      apply H.
      lia.
Qed.

Lemma lw2_qsum0_extend : forall m n (g : nat -> Q),
  (n <= m)%nat ->
  (forall j, (n <= j)%nat -> (j < m)%nat -> g j == 0) ->
  lw2_qsum0 g m == lw2_qsum0 g n.
Proof.
  intros m.
  induction m as [|m IH]; intros n g Hn Hg.
  - assert (Hn0 : (n = 0)%nat) by lia.
    rewrite Hn0.
    reflexivity.
  - destruct (Nat.eq_dec n (S m)) as [Heq | Hne].
    + rewrite Heq.
      reflexivity.
    + assert (Hnm : (n <= m)%nat) by lia.
      cbn [lw2_qsum0].
      rewrite (Hg m Hnm (Nat.lt_succ_diag_r m)).
      assert (Hstep : lw2_qsum0 g m == lw2_qsum0 g n).
      { apply (IH n g Hnm).
        intros j Hj1 Hj2.
        apply (Hg j Hj1).
        lia. }
      rewrite Hstep.
      ring.
Qed.

Lemma lw2_qsum0_telescope : forall (A : nat -> Q) n,
  lw2_qsum0 (fun j => A j - A (S j)) (S n) == A (0 % nat) - A (S n).
Proof.
  intros A n.
  induction n as [|n IH].
  - cbn [lw2_qsum0].
    ring.
  - cbn [lw2_qsum0].
    rewrite IH.
    ring.
Qed.

Lemma lw2_qsum0_dirac : forall n (g : nat -> Q),
  (1 <= n)%nat ->
  (forall j, (1 <= j)%nat -> (j < n)%nat -> g j == 0) ->
  lw2_qsum0 g n == g (0 % nat).
Proof.
  intros n g.
  induction n as [|n IH]; intros H1 H0.
  - lia.
  - destruct n as [|n'].
    + cbn [lw2_qsum0].
      ring.
    + cbn [lw2_qsum0].
      rewrite (H0 (S n') (le_n_S _ _ (Nat.le_0_l n')) (Nat.lt_succ_diag_r (S n'))).
      rewrite (IH (le_n_S _ _ (Nat.le_0_l n'))).
      * ring.
      * intros j Hj1 Hj2.
        apply (H0 j Hj1).
        lia.
Qed.

Lemma lw2_qsum0_shift : forall n (g : nat -> Q),
  lw2_qsum0 (fun k => g (S k)) n == lw2_qsum0 g n - g (0 % nat) + g n.
Proof.
  intros n g.
  induction n as [|n IH].
  - cbn [lw2_qsum0]; ring.
  - cbn [lw2_qsum0].
    rewrite IH.
    ring.
Qed.

(* The bridge: evaluation is the shifted sum of coefficient times power. *)
Lemma lw2_eval_coef_sum : forall p x,
  qpoly_eval p x ==
  lw2_qsum0 (fun j => lw0_coef j p * lw2_qpow x j) (length p).
Proof.
  induction p as [|a p IH]; intros x.
  - reflexivity.
  - cbn [qpoly_eval length].
    assert (Hext :
      lw2_qsum0 (fun j => lw0_coef j (cons a p) * lw2_qpow x j) (S (length p)) ==
      lw2_qsum0 (fun j => match j with
                          | 0 % nat => a * 1
                          | S j' => lw0_coef j' p * lw2_qpow x j' * x
                          end) (S (length p))).
    { apply lw2_qsum0_ext.
      intros j _.
      destruct j as [|j'].
      - cbn [lw0_coef lw2_qpow].
        ring.
      - cbn [lw0_coef lw2_qpow].
        ring. }
    rewrite Hext.
    rewrite (lw2_qsum0_split (fun j => lw0_coef j p * lw2_qpow x j) (a * 1) x (length p)).
    rewrite (IH x).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  Table-length bookkeeping and iterated-derivative        *)
(* vanishing above the degree (the superscript zeroing piece).         *)
(* ------------------------------------------------------------------ *)

Lemma lw2_len_add_max : forall p q,
  length (qpoly_add p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q.
  - destruct q as [|b q'].
    + reflexivity.
    + reflexivity.
  - destruct q as [|b q'].
    + reflexivity.
    + cbn [qpoly_add length].
      rewrite IH.
      reflexivity.
Qed.

Lemma lw2_len_scalar : forall a p, length (qpoly_scalar a p) = length p.
Proof.
  intros a p.
  induction p as [|b p IH].
  - reflexivity.
  - cbn [qpoly_scalar length].
    rewrite IH.
    reflexivity.
Qed.

Lemma lw2_len_deriv : forall p,
  (length (qpoly_deriv p) <= length p)%nat.
Proof.
  induction p as [|a p IH].
  - cbn [qpoly_deriv length]; lia.
  - cbn [qpoly_deriv length].
    rewrite lw2_len_add_max.
    replace (length (cons 0 (qpoly_deriv p))) with (S (length (qpoly_deriv p)))
      by reflexivity.
    lia.
Qed.

Lemma lw2_len_deriv_iter : forall k p,
  (length (qpoly_deriv_iter k p) <= length p)%nat.
Proof.
  intros k.
  induction k as [|k IH]; intros p.
  - cbn [qpoly_deriv_iter]; lia.
  - cbn [qpoly_deriv_iter].
    eapply Nat.le_trans.
    + apply lw2_len_deriv.
    + apply IH.
Qed.

Lemma lw2_deriv_iter_nil : forall k, qpoly_deriv_iter k nil = nil.
Proof.
  intros k.
  induction k as [|k IH].
  - reflexivity.
  - cbn [qpoly_deriv_iter].
    rewrite IH.
    reflexivity.
Qed.

(* The superscript zeroing piece. *)
Lemma lw2_deriv_iter_zero_eval : forall n f x,
  (length f <= n)%nat -> qpoly_eval (qpoly_deriv_iter n f) x == 0.
Proof.
  intros n f x Hn.
  rewrite lw2_eval_coef_sum.
  apply lw2_qsum0_zero.
  intros j Hj.
  rewrite lw0_coef_iter_fall.
  assert (Hjn : (length f <= j + n)%nat) by lia.
  rewrite (lw0_coef_beyond (j + n) f Hjn).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 5.  Evaluation-layer linearity of iterated derivatives.     *)
(* ------------------------------------------------------------------ *)

Lemma lw2_eval_di_add : forall k u v x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_add u v)) x ==
  qpoly_eval (qpoly_deriv_iter k u) x + qpoly_eval (qpoly_deriv_iter k v) x.
Proof.
  intros k u v x.
  rewrite !lw2_eval_coef_sum.
  assert (Hb0 : (length (qpoly_deriv_iter k (qpoly_add u v)) <= length u + length v)%nat).
  { eapply Nat.le_trans.
    - apply lw2_len_deriv_iter.
    - rewrite lw2_len_add_max.
      lia. }
  assert (Hb1 : (length (qpoly_deriv_iter k u) <= length u + length v)%nat).
  { eapply Nat.le_trans.
    - apply lw2_len_deriv_iter.
    - lia. }
  assert (Hb2 : (length (qpoly_deriv_iter k v) <= length u + length v)%nat).
  { eapply Nat.le_trans.
    - apply lw2_len_deriv_iter.
    - lia. }
  assert (H1 : lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k (qpoly_add u v)) * lw2_qpow x j) (length (qpoly_deriv_iter k (qpoly_add u v))) ==
               lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k (qpoly_add u v)) * lw2_qpow x j) (length u + length v)).
  { symmetry.
    apply lw2_qsum0_extend.
    - lia.
    - intros j Hj1 Hj2.
      rewrite (lw0_coef_beyond j (qpoly_deriv_iter k (qpoly_add u v)) Hj1).
      ring. }
  assert (H2 : lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k u) * lw2_qpow x j) (length (qpoly_deriv_iter k u)) ==
               lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k u) * lw2_qpow x j) (length u + length v)).
  { symmetry.
    apply lw2_qsum0_extend.
    - lia.
    - intros j Hj1 Hj2.
      rewrite (lw0_coef_beyond j (qpoly_deriv_iter k u) Hj1).
      ring. }
  assert (H3 : lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k v) * lw2_qpow x j) (length (qpoly_deriv_iter k v)) ==
               lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k v) * lw2_qpow x j) (length u + length v)).
  { symmetry.
    apply lw2_qsum0_extend.
    - lia.
    - intros j Hj1 Hj2.
      rewrite (lw0_coef_beyond j (qpoly_deriv_iter k v) Hj1).
      ring. }
  rewrite H1, H2, H3.
  rewrite <- lw2_qsum0_add.
  apply lw2_qsum0_ext.
  intros j _.
  rewrite lw0_coef_iter_add.
  ring.
Qed.

Lemma lw2_eval_di_scalar : forall k a p x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar a p)) x ==
  a * qpoly_eval (qpoly_deriv_iter k p) x.
Proof.
  intros k a p x.
  rewrite !lw2_eval_coef_sum.
  assert (Hb : (length (qpoly_deriv_iter k (qpoly_scalar a p)) <= length p)%nat).
  { eapply Nat.le_trans.
    - apply lw2_len_deriv_iter.
    - rewrite lw2_len_scalar.
      lia. }
  assert (H1 : lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p)) * lw2_qpow x j) (length (qpoly_deriv_iter k (qpoly_scalar a p))) ==
               lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p)) * lw2_qpow x j) (length p)).
  { symmetry.
    apply lw2_qsum0_extend.
    - lia.
    - intros j Hj1 Hj2.
      rewrite (lw0_coef_beyond j (qpoly_deriv_iter k (qpoly_scalar a p)) Hj1).
      ring. }
  assert (H2 : lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j) (length (qpoly_deriv_iter k p)) ==
               lw2_qsum0 (fun j => lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j) (length p)).
  { symmetry.
    apply lw2_qsum0_extend.
    - apply lw2_len_deriv_iter.
    - intros j Hj1 Hj2.
      rewrite (lw0_coef_beyond j (qpoly_deriv_iter k p) Hj1).
      ring. }
  rewrite H1, H2.
  transitivity
    (lw2_qsum0 (fun j => a * (lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j)) (length p))%Q.
  - apply lw2_qsum0_ext.
    intros j _.
    rewrite lw0_coef_iter_scalar.
    ring.
  - apply (lw2_qsum0_scale (length p)
             (fun j => lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j) a).
Qed.

(* One differentiated step on a cons cell, at evaluation level. *)
Lemma lw2_deriv_cons_shape : forall k b (W : QPoly) x,
  qpoly_eval (qpoly_deriv_iter (S k) (cons b W)) x ==
  ((Z.of_nat (S k)) # 1)%Q * qpoly_eval (qpoly_deriv_iter k W) x
  + x * qpoly_eval (qpoly_deriv_iter (S k) W) x.
Proof.
  intros k.
  induction k as [|k IH]; intros b W x.
  - change (qpoly_deriv_iter (S 0) (cons b W))
      with (qpoly_add W (cons 0 (qpoly_deriv W))).
    change (qpoly_deriv_iter (S 0) W) with (qpoly_deriv W).
    change (qpoly_deriv_iter 0 W) with W.
    rewrite qpoly_eval_add.
    change (qpoly_eval (cons 0 (qpoly_deriv W)) x)
      with (0 + x * qpoly_eval (qpoly_deriv W) x).
    replace ((Z.of_nat (S 0)) # 1)%Q with 1 by reflexivity.
    ring.
  - rewrite qpoly_deriv_iter_commute.
    change (qpoly_deriv (cons b W))
      with (qpoly_add W (cons 0 (qpoly_deriv W))).
    rewrite lw2_eval_di_add.
    rewrite (IH 0 (qpoly_deriv W) x).
    rewrite <- (qpoly_deriv_iter_commute k W).
    rewrite <- (qpoly_deriv_iter_commute (S k) W).
    rewrite (lw2_qmake_succ (S k)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 6.  The translation t |-> t + c.                            *)
(* ------------------------------------------------------------------ *)

Fixpoint lw2_trans (f : QPoly) (c : Q) : QPoly :=
  match f with
  | nil => nil
  | cons a p => qpoly_add (qpoly_scalar c (lw2_trans p c)) (cons a (lw2_trans p c))
  end.

Lemma lw2_trans_eval : forall f c x,
  qpoly_eval (lw2_trans f c) x == qpoly_eval f (x + c).
Proof.
  induction f as [|a p IH]; intros c x.
  - reflexivity.
  - cbn [lw2_trans].
    rewrite qpoly_eval_add, qpoly_eval_scalar.
    cbn [qpoly_eval].
    rewrite (IH c x).
    ring.
Qed.

Lemma lw2_trans_add : forall u v c x,
  qpoly_eval (lw2_trans (qpoly_add u v) c) x ==
  qpoly_eval (lw2_trans u c) x + qpoly_eval (lw2_trans v c) x.
Proof.
  intros u.
  induction u as [|a u IH]; intros v c x.
  - cbn [qpoly_add lw2_trans qpoly_eval].
    ring.
  - destruct v as [|b v].
    + cbn [qpoly_add lw2_trans qpoly_eval].
      ring.
    + replace (qpoly_add (cons a u) (cons b v))
        with (cons (a + b) (qpoly_add u v)) by reflexivity.
      cbn [lw2_trans].
      rewrite !qpoly_eval_add, !qpoly_eval_scalar.
      cbn [qpoly_eval].
      rewrite (IH v c x).
      ring.
Qed.

Lemma lw2_len_trans : forall f c, length (lw2_trans f c) = length f.
Proof.
  induction f as [|a p IH]; intros c.
  - reflexivity.
  - cbn [lw2_trans length].
    rewrite lw2_len_add_max, lw2_len_scalar.
    replace (length (cons a (lw2_trans p c))) with (S (length (lw2_trans p c))) by reflexivity.
    replace (length (cons a p)) with (S (length p)) by reflexivity.
    rewrite IH.
    lia.
Qed.

Lemma lw2_trans_deriv : forall f c x,
  qpoly_eval (qpoly_deriv (lw2_trans f c)) x ==
  qpoly_eval (lw2_trans (qpoly_deriv f) c) x.
Proof.
  induction f as [|a p IH]; intros c x.
  - reflexivity.
  - cbn [lw2_trans].
    rewrite qpoly_eval_deriv_add, qpoly_eval_add.
    rewrite qpoly_eval_deriv_scalar, qpoly_eval_scalar, qpoly_eval_deriv_cons.
    rewrite (IH c x).
    cbn [qpoly_deriv].
    rewrite lw2_trans_add.
    cbn [lw2_trans].
    rewrite qpoly_eval_add, qpoly_eval_scalar.
    change (qpoly_eval (cons 0 (lw2_trans (qpoly_deriv p) c)) x)
      with (0 + x * qpoly_eval (lw2_trans (qpoly_deriv p) c) x).
    ring.
Qed.

(* The chain-rule translation form. *)
Lemma lw2_trans_deriv_iter_eval : forall k f c x,
  qpoly_eval (qpoly_deriv_iter k (lw2_trans f c)) x ==
  qpoly_eval (qpoly_deriv_iter k f) (x + c).
Proof.
  intros k f.
  revert k.
  induction f as [|a p IH]; intros k c x.
  - cbn [lw2_trans].
    rewrite lw2_deriv_iter_nil.
    reflexivity.
  - cbn [lw2_trans].
    rewrite lw2_eval_di_add, lw2_eval_di_scalar.
    destruct k as [|k'].
    + rewrite (IH (0 % nat) c x).
      cbn [qpoly_deriv_iter qpoly_eval].
      rewrite lw2_trans_eval.
      ring.
    + rewrite lw2_deriv_cons_shape.
      rewrite lw2_deriv_cons_shape.
      rewrite (IH (S k') c x).
      rewrite (IH k' c x).
      ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.  The antiderivative table and the kernel identity.       *)
(* ------------------------------------------------------------------ *)

Fixpoint lw2_eps (K : nat) (f : QPoly) : QPoly :=
  match K with
  | 0 % nat => nil
  | S m => qpoly_add (qpoly_deriv_iter m f) (lw2_eps m f)
  end.

Lemma lw2_eps_eval_sum : forall K f x,
  qpoly_eval (lw2_eps K f) x ==
  lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) K.
Proof.
  intros K f x.
  induction K as [|K IH].
  - reflexivity.
  - cbn [lw2_eps].
    rewrite qpoly_eval_add.
    rewrite IH.
    cbn [lw2_qsum0].
    ring.
Qed.

(* Pointwise agreement of the table beyond the table length. *)
Lemma lw2_eps_eval : forall N f x,
  (length f <= N)%nat ->
  qpoly_eval (lw2_eps N f) x == qpoly_eval (lw2_eps (length f) f) x.
Proof.
  intros N f x HN.
  rewrite !lw2_eps_eval_sum.
  apply lw2_qsum0_extend.
  - lia.
  - intros j Hj1 Hj2.
    apply lw2_deriv_iter_zero_eval.
    lia.
Qed.

Lemma lw2_eps_deriv_sum : forall K f x,
  qpoly_eval (qpoly_deriv (lw2_eps K f)) x ==
  lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter (S k) f) x) K.
Proof.
  intros K f x.
  induction K as [|K IH].
  - cbn [lw2_eps qpoly_deriv].
    reflexivity.
  - cbn [lw2_eps].
    rewrite qpoly_eval_deriv_add, qpoly_eval_add.
    rewrite IH.
    rewrite <- qpoly_deriv_iter_succ.
    cbn [lw2_qsum0].
    ring.
Qed.

(* The kernel identity: the algebraized exponential-weight equation. *)
Lemma lw2_eps_deriv_kernel : forall K f x,
  (length f <= K)%nat ->
  qpoly_eval (qpoly_deriv (lw2_eps K f)) x ==
  qpoly_eval (lw2_eps K f) x - qpoly_eval f x.
Proof.
  intros K f x HN.
  rewrite lw2_eps_deriv_sum.
  rewrite lw2_eps_eval_sum.
  assert (Hsh : lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter (S k) f) x) K ==
                lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                - qpoly_eval (qpoly_deriv_iter 0 f) x
                + qpoly_eval (qpoly_deriv_iter K f) x).
  { exact (lw2_qsum0_shift K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)). }
  rewrite Hsh.
  rewrite (lw2_deriv_iter_zero_eval K f x HN).
  assert (Hd0 : qpoly_eval (qpoly_deriv_iter 0 f) x == qpoly_eval f x) by reflexivity.
  rewrite Hd0.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 8.  The node functional with explicit integer coefficients, *)
(* the endpoint value, and the Hermite identity.                       *)
(* ------------------------------------------------------------------ *)

Definition lw2_node (j : nat) : Q := ((Z.of_nat j) # 1)%Q.

(* Explicit integer coefficient table: +1 at node 0, -1 at node S n,    *)
(* 0 at the interior nodes; independent of the derivative order k.      *)
Definition lw2_lambda_coef (n j k : nat) : Z :=
  (if Nat.eqb j 0 then 1 else 0) + (if Nat.eqb j (S n) then (-1) else 0)%Z.

Definition lw2_lambda (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun j =>
    lw2_qsum0 (fun k =>
      ((lw2_lambda_coef n j k) # 1)%Q * qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
      (length f))
    (S (S n)).

Definition lw2_endpoint (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun j =>
    qpoly_eval (lw2_eps (length f) (lw2_trans f (lw2_node j))) 0 -
    qpoly_eval (lw2_eps (length f) (lw2_trans f (lw2_node j))) 1)
    (S n).

Theorem lw2_hermite_identity : forall n f, lw2_lambda n f == lw2_endpoint n f.
Proof.
  intros n f.
  assert (Hevalc : forall (T : QPoly) (u v : Q),
    u == v -> qpoly_eval T u == qpoly_eval T v).
  { intros T. induction T as [|b T' IH]; intros u v Huv.
    - reflexivity.
    - cbn [qpoly_eval].
      rewrite (IH u v Huv).
      rewrite Huv.
      reflexivity. }
  assert (Hpt0 : forall j,
    qpoly_eval (lw2_eps (length f) (lw2_trans f (lw2_node j))) 0 ==
    lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f)).
  { intros j.
    rewrite lw2_eps_eval_sum.
    apply lw2_qsum0_ext.
    intros k _.
    rewrite lw2_trans_deriv_iter_eval.
    apply (Hevalc (qpoly_deriv_iter k f)).
    ring. }
  assert (Hpt1 : forall j,
    qpoly_eval (lw2_eps (length f) (lw2_trans f (lw2_node j))) 1 ==
    lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node (S j))) (length f)).
  { intros j.
    rewrite lw2_eps_eval_sum.
    apply lw2_qsum0_ext.
    intros k _.
    rewrite lw2_trans_deriv_iter_eval.
    apply (Hevalc (qpoly_deriv_iter k f)).
    transitivity (((1 + Z.of_nat j) # 1)%Q).
    - exact (lw2_qmake_add 1 (Z.of_nat j)).
    - assert (Hsj : (1 + Z.of_nat j)%Z = Z.of_nat (S j)) by lia.
      rewrite Hsj.
      reflexivity. }
  (* The node-functional side reorganized. *)
  assert (Hlam : lw2_lambda n f ==
    lw2_qsum0 (fun j =>
      ((lw2_lambda_coef n j 0) # 1)%Q *
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
      (S (S n))).
  { unfold lw2_lambda.
    transitivity
      (lw2_qsum0 (fun j =>
        lw2_qsum0 (fun k =>
          ((lw2_lambda_coef n j 0) # 1)%Q * qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
          (length f))
        (S (S n)))%Q.
    - apply lw2_qsum0_ext.
      intros j _.
      apply lw2_qsum0_ext.
      intros k _.
      assert (Hck : lw2_lambda_coef n j k = lw2_lambda_coef n j 0) by reflexivity.
      rewrite Hck.
      reflexivity.
    - apply lw2_qsum0_ext.
      intros j _.
      rewrite lw2_qsum0_scale.
      reflexivity. }
  (* The endpoint side reorganized. *)
  assert (Hend : lw2_endpoint n f ==
    lw2_qsum0 (fun j =>
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f) -
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node (S j))) (length f))
      (S n)).
  { unfold lw2_endpoint.
    apply lw2_qsum0_ext.
    intros j _.
    rewrite (Hpt0 j), (Hpt1 j).
    reflexivity. }
  rewrite Hlam, Hend.
  (* Telescoping over the intervals. *)
  assert (Htel :
    lw2_qsum0 (fun j =>
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f) -
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node (S j))) (length f))
      (S n) ==
    lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node 0)) (length f) -
    lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node (S n))) (length f)).
  { exact (lw2_qsum0_telescope
             (fun j => lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
             n). }
  rewrite Htel.
  assert (Hc0 : lw2_lambda_coef n 0 0 = (1 + 0)%Z).
  { unfold lw2_lambda_coef.
    reflexivity. }
  assert (HcS : lw2_lambda_coef n (S n) 0 = (-1)%Z).
  { unfold lw2_lambda_coef.
    cbn [Nat.eqb].
    rewrite Nat.eqb_refl.
    reflexivity. }
  change (lw2_qsum0
            (fun j => ((lw2_lambda_coef n j 0) # 1)%Q *
                      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
            (S (S n)))
    with (lw2_qsum0
            (fun j => ((lw2_lambda_coef n j 0) # 1)%Q *
                      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
            (S n)
          + ((lw2_lambda_coef n (S n) 0) # 1)%Q *
            lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node (S n))) (length f)).
  assert (Hdirac :
    lw2_qsum0 (fun j =>
      ((lw2_lambda_coef n j 0) # 1)%Q *
      lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
      (S n) ==
    ((lw2_lambda_coef n 0 0) # 1)%Q *
    lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) (lw2_node 0)) (length f)).
  { apply lw2_qsum0_dirac.
    - lia.
    - intros j Hj1 Hj2.
      assert (Hj0 : Nat.eqb j 0 = false) by (apply Nat.eqb_neq; lia).
      assert (Hjn : Nat.eqb j (S n) = false) by (apply Nat.eqb_neq; lia).
      unfold lw2_lambda_coef.
      rewrite Hj0, Hjn.
      cbn [Z.add].
      ring. }
  rewrite Hdirac, Hc0, HcS.
  cbn [Z.add].
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 9.  Extraction probe and assumption checks.                 *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction lw2_hermite_identity lw2_lambda lw2_endpoint lw2_trans lw2_eps lw2_lambda_coef.

Print Assumptions lw2_hermite_identity.
Print Assumptions lw2_eps_deriv_kernel.
Print Assumptions lw2_deriv_iter_zero_eval.
Print Assumptions lw2_trans_deriv_iter_eval.
Print Assumptions lw2_eps_eval.

(* ------------------------------------------------------------------ *)
(* Section 10.  Item-6 integrality bridge (pure append, seat 86).      *)
(* coef dual-source ruling: this bridge consumes the in-file coef      *)
(* section (Section 2: lw0_coef / lw0_coef_deriv / lw0_coef_iter_fall, *)
(* all green); it does NOT Require LW0Integrality2 (its lw0_coef       *)
(* family and the z_lo/z_hi/lw2z_divides material are not on this      *)
(* bridge path, and its upstream chain S03_QExp / UpReqBanachAdd has   *)
(* not been compiled in this sandbox -- narrowed dependency face, no   *)
(* dual-source mixing).  Integrality witness shape follows the         *)
(* LW0Integrality2 precedent lw0_z_lo_integer:                         *)
(*   sigT (fun z : Z => Qeq v ((z # 1)%Q)).                            *)
(* ------------------------------------------------------------------ *)

Lemma lw2i_qmake_mul : forall x y : Z,
  ((x # 1)%Q * (y # 1)%Q) == (((x * y) # 1)%Q).
Proof.
  intros x y.
  unfold Qeq; cbn [Qplus Qmult Qnum Qden]; lia.
Qed.

(* The integrality predicate on coefficient lists, at Type level:      *)
(* every coefficient carries an explicit integer witness.              *)
Definition lw2i_intpoly (f : QPoly) : Type :=
  forall i : nat, sigT (fun z : Z => Qeq (lw0_coef i f) ((z # 1)%Q)).

(* Step A.  An integral polynomial takes integral values at integer    *)
(* nodes (induction on the polynomial, no power/fall machinery).       *)
Lemma lw2i_eval_int : forall f j,
  lw2i_intpoly f ->
  sigT (fun w : Z => Qeq (qpoly_eval f (lw2_node j)) ((w # 1)%Q)).
Proof.
  intros f.
  induction f as [|a p IH]; intros j Hf.
  - exists 0%Z.
    cbn [qpoly_eval].
    reflexivity.
  - assert (Hp : lw2i_intpoly p).
    { intros i.
      destruct (Hf (S i)) as [z Hz].
      exists z.
      change (lw0_coef (S i) (cons a p)) with (lw0_coef i p).
      exact Hz. }
    destruct (IH j Hp) as [wp Hwp].
    destruct (Hf (0 % nat)) as [za Ha].
    change (lw0_coef 0 (cons a p)) with a in Ha.
    exists (za + Z.of_nat j * wp)%Z.
    cbn [qpoly_eval].
    unfold lw2_node.
    rewrite Ha.
    rewrite Hwp.
    rewrite lw2i_qmake_mul.
    apply (lw2_qmake_add za (Z.of_nat j * wp)%Z).
Qed.

(* Step B.  Formal derivation preserves integrality of coefficients    *)
(* (reuses the green in-file bridge lw0_coef_deriv).                   *)
Lemma lw2i_intpoly_deriv : forall f,
  lw2i_intpoly f -> lw2i_intpoly (qpoly_deriv f).
Proof.
  intros f Hf i.
  destruct (Hf (S i)) as [z Hz].
  exists ((Z.of_nat (S i)) * z)%Z.
  rewrite lw0_coef_deriv.
  rewrite Hz.
  apply lw2i_qmake_mul.
Qed.

(* Step C.  Iterated derivation preserves integrality.                 *)
Lemma lw2i_intpoly_di : forall k f,
  lw2i_intpoly f -> lw2i_intpoly (qpoly_deriv_iter k f).
Proof.
  intros k.
  induction k as [|k IH]; intros f Hf.
  - exact Hf.
  - cbn [qpoly_deriv_iter].
    apply lw2i_intpoly_deriv.
    apply IH.
    exact Hf.
Qed.

(* Step D.  Iterated derivatives take integral values at nodes.        *)
Lemma lw2i_di_eval_int : forall k f j,
  lw2i_intpoly f ->
  sigT (fun w : Z => Qeq
    (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) ((w # 1)%Q)).
Proof.
  intros k f j Hf.
  apply lw2i_eval_int.
  apply lw2i_intpoly_di.
  exact Hf.
Qed.

(* The witness selector: an honest Z-valued function.                  *)
Definition lw2i_wit (f : QPoly) (Hf : lw2i_intpoly f) (k j : nat) : Z :=
  match lw2i_di_eval_int k f j Hf with
  | existT _ w _ => w
  end.

Lemma lw2i_wit_spec : forall k f j (Hf : lw2i_intpoly f),
  Qeq (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
      (((lw2i_wit f Hf k j) # 1)%Q).
Proof.
  intros k f j Hf.
  unfold lw2i_wit.
  destruct (lw2i_di_eval_int k f j Hf) as [w Hw].
  exact Hw.
Qed.

(* Z-level finite sum folding the witness sums.                        *)
Fixpoint lw2i_sumz (g : nat -> Z) (n : nat) : Z :=
  match n with
  | 0 % nat => 0 % Z
  | S m => (lw2i_sumz g m + g m) % Z
  end.

Lemma lw2i_qsum0_zmake : forall n (g : nat -> Z),
  lw2_qsum0 (fun k => ((g k) # 1)%Q) n == ((lw2i_sumz g n) # 1)%Q.
Proof.
  intros n g.
  induction n as [|n IH].
  - reflexivity.
  - cbn [lw2_qsum0 lw2i_sumz].
    rewrite IH.
    apply lw2_qmake_add.
Qed.

(* Generalized folding: a Q-valued family that pointwise carries the Z
   witnesses folds to the Z-sum witness (single apply, no summand-level
   transitivity -- the q_scope notation branch cannot be backtracked). *)
Lemma lw2i_qsum0_zmake_gen : forall n (g : nat -> Z) (h : nat -> Q),
  (forall k : nat, h k == ((g k) # 1)%Q) ->
  lw2_qsum0 h n == ((lw2i_sumz g n) # 1)%Q.
Proof.
  intros n g h H.
  induction n as [|n IH].
  - reflexivity.
  - cbn [lw2_qsum0 lw2i_sumz].
    rewrite (H n).
    rewrite IH.
    apply (lw2_qmake_add (lw2i_sumz g n) (g n)%Z).
Qed.

(* Item 6, main bridge: the node functional lambda n f carries an      *)
(* explicit integer witness whenever f has integral coefficients.      *)
(* Each summand is (c_{jk} # 1) * f^{(k)}(j) with c_{jk} : Z the green *)
(* table lw2_lambda_coef and f^{(k)}(j) integral by Steps A-D; the two *)
(* nested sums fold through lw2i_qsum0_zmake.                          *)
Theorem lw2i_lambda_integer : forall n f,
  lw2i_intpoly f ->
  sigT (fun w : Z => Qeq (lw2_lambda n f) ((w # 1)%Q)).
Proof.
  intros n f Hf.
  unfold lw2_lambda.
  exists (lw2i_sumz
            (fun j : nat =>
               lw2i_sumz (fun k : nat =>
                            (lw2_lambda_coef n j k * lw2i_wit f Hf k j)%Z)
                         (length f))
            (S (S n)))%Z.
  apply (lw2i_qsum0_zmake_gen (S (S n))
           (fun j : nat =>
              lw2i_sumz (fun k : nat =>
                           (lw2_lambda_coef n j k * lw2i_wit f Hf k j)%Z)
                        (length f))
           (fun j : nat =>
              lw2_qsum0 (fun k : nat =>
                           ((lw2_lambda_coef n j k) # 1)%Q *
                           qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
                        (length f))).
  intros j.
  apply (lw2i_qsum0_zmake_gen (length f)
           (fun k : nat => (lw2_lambda_coef n j k * lw2i_wit f Hf k j)%Z)
           (fun k : nat =>
              ((lw2_lambda_coef n j k) # 1)%Q *
              qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))).
  intros k.
  rewrite (lw2i_wit_spec k f j Hf).
  apply lw2i_qmake_mul.
Qed.

(* Consuming the green master identity: the endpoint functional is     *)
(* integral with the same explicit witness.                            *)
Corollary lw2i_endpoint_integer : forall n f,
  lw2i_intpoly f ->
  sigT (fun w : Z => Qeq (lw2_endpoint n f) ((w # 1)%Q)).
Proof.
  intros n f Hf.
  destruct (lw2i_lambda_integer n f Hf) as [w Hw].
  exists w.
  rewrite <- (lw2_hermite_identity n f).
  exact Hw.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 11.  Stretch (S2-lite): the exact kernel identity           *)
(* eps' = eps - f + f^{(K)}, 对一切 K 无条件成立（零假设位）; *)
(* the green kernel lw2_eps_deriv_kernel is its vanishing-tail case.   *)
(* ------------------------------------------------------------------ *)

Lemma lw2i_eps_exact : forall K f x,
  qpoly_eval (qpoly_deriv (lw2_eps K f)) x ==
  qpoly_eval (lw2_eps K f) x - qpoly_eval f x
  + qpoly_eval (qpoly_deriv_iter K f) x.
Proof.
  intros K f x.
  rewrite lw2_eps_deriv_sum.
  rewrite lw2_eps_eval_sum.
  assert (Hsh : lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter (S k) f) x) K ==
                lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                - qpoly_eval (qpoly_deriv_iter 0 f) x
                + qpoly_eval (qpoly_deriv_iter K f) x).
  { exact (lw2_qsum0_shift K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)). }
  rewrite Hsh.
  assert (Hd0 : qpoly_eval (qpoly_deriv_iter 0 f) x == qpoly_eval f x)
    by reflexivity.
  rewrite Hd0.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 12.  Extraction probe and assumption checks (seat 86).      *)
(* ------------------------------------------------------------------ *)

Separate Extraction lw2i_lambda_integer lw2i_endpoint_integer lw2i_eps_exact lw2i_sumz.

Print Assumptions lw2i_lambda_integer.
Print Assumptions lw2i_endpoint_integer.
Print Assumptions lw2i_eps_exact.
