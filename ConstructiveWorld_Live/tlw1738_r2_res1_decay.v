(* ========================================================================= *)
(* Module   : tlw1738_r2_res1_decay                                          *)
(* Purpose 使命 : the residual recursion for the diagonal Pade pair of        *)
(*            arctan. With r2_coef m j the degree-j entry of V_m g - U_m,    *)
(*            the two-step table recursion transports the residual           *)
(*            linearly: coef (k+2) (S j) = (2k+5) coef (k+1) (S j) +         *)
(*            (k+2)^2 coef k j. A vanishing diagonal entry at order k+2      *)
(*            then yields the first-order ratio (2k+5) R(k+1) =              *)
(*            -(k+2)^2 R(k) on the mismatch-front coefficients R(k) =        *)
(*            coef k (k+1); the even steps compose into the two-step ratio   *)
(*            (4n+5)(4n+7) res1 (n+1) = (2n+2)^2 (2n+3)^2 res1 n.            *)
(*            The vanishing-diagonal entries are stated as explicit          *)
(*            premises of the ratio statements (honest interface); every    *)
(*            unconditional statement is anchored by computation, and the   *)
(*            closed form (4n+3)! res1 n = -2^(2n+1) ((2n+1)!)^3 is         *)
(*            certified by computation at n = 1..3.                         *)
(* Requires 依赖 : tlw1463_pade_table, tlw1728R2_r2_res1_moment             *)
(*            (same -Q . "" domain).                                         *)
(* Reference 对标 : Lambert continued fraction remainders; classical Pade    *)
(*            remainder theory for arctan.                                   *)
(* Construction 构造性 : residual identities over Qeq with Q-algebra        *)
(*            atomic lemmas discharged by the ring decision procedure, with  *)
(*            one declared auxiliary nia use; no axioms, no classical logic. *)
(* Build 编译配方 : full-literal COQLIB export, then:                        *)
(*            coqc -q -Q . "" tlw1738_r2_res1_decay.v                        *)
(* ========================================================================= *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
Require Import tlw1463_pade_table.
Require Import tlw1728R2_r2_res1_moment.

(* ================= §1 Linearity of the moment sum ================= *)

(* Subtraction of zero is trivial (the stdlib carries no such lemma). *)
Lemma r2_q_minus_0 : forall x : Q, x - 0%Q == x.
Proof.
  intros [n d]. ring.
Qed.

(* The moment sum is linear in the table. *)
Lemma r2_msq_vsmul : forall (c : Q) (l : list Q) (j : nat),
  r2_msq (vsmul c l) j == c * r2_msq l j.
Proof.
  intros c l. induction l as [|x t IH]; intros j.
  - cbn [vsmul r2_msq]. rewrite Qmult_0_r. apply Qeq_refl.
  - destruct j as [|j'].
    + cbn [vsmul r2_msq]. rewrite Qmult_assoc. apply Qeq_refl.
    + cbn [vsmul r2_msq]. rewrite IH.
      ring.
Qed.

(* The moment sum is additive in the table. *)
Lemma r2_msq_vadd : forall (a b : list Q) (j : nat),
  r2_msq (vadd a b) j == r2_msq a j + r2_msq b j.
Proof.
  intros a. induction a as [|x t IH]; intros b j.
  - cbn [vadd r2_msq]. rewrite Qplus_0_l. apply Qeq_refl.
  - destruct b as [|y s].
    + cbn [vadd]. rewrite Qplus_0_r. apply Qeq_refl.
    + destruct j as [|j'].
      * cbn [vadd r2_msq]. rewrite Qmult_plus_distr_l. apply Qeq_refl.
      * cbn [vadd r2_msq]. rewrite (IH s j').
        ring.
Qed.

(* A zero-padded head contributes nothing above degree zero. *)
Lemma r2_msq_shift : forall (l : list Q) (j : nat),
  r2_msq (0%Q :: l) (S j) == r2_msq l j.
Proof.
  intros l j. cbn [r2_msq]. rewrite Qmult_0_l, Qplus_0_l. apply Qeq_refl.
Qed.

(* ================= §2 The residual coefficients ================= *)

(* The degree-j entry of V_m g - U_m: the moment sum of the denominator  *)
(* table minus the numerator table entry (zero padding beyond its        *)
(* degree).                                                              *)
Definition r2_coef (m j : nat) : Q :=
  r2_msq (padeV m) j - nth j (padeU m) 0%Q.

(* Atomic Q-algebra used to assemble the linear transport (the whole     *)
(* solver load of the transport sits in these three lemmas). *)
Lemma r2_q_linear : forall (c d A B C D : Q),
  (c * A + d * B) - (c * C + d * D) == c * (A - C) + d * (B - D).
Proof.
  intros c d A B C D.
  ring.
Qed.

Lemma r2_q_zero_move : forall (c d X Y : Q),
  0%Q == c * X + d * Y -> c * X == - d * Y.
Proof.
  intros c d X Y H.
  unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp] in *. nia.
Qed.

Lemma r2_q_ring_1 : forall (a u v : Q), a * (- u * v) == - (u * (a * v)).
Proof.
  intros a u v.
  ring.
Qed.

Lemma r2_q_ring_2 : forall (b c X : Q), - (c * (- b * X)) == b * (c * X).
Proof.
  intros b c X.
  ring.
Qed.

Lemma r2_q_step2 : forall (e f b c X Y R : Q),
  e * R == - b * X -> f * Y == - c * R -> e * (f * Y) == b * (c * X).
Proof.
  intros e f b c X Y R H1 H2.
  assert (K1 : c * (e * R) == c * (- b * X)) by (rewrite H1; reflexivity).
  assert (K2 : e * (f * Y) == e * (- c * R)) by (rewrite H2; reflexivity).
  rewrite K2, (r2_q_ring_1 e c R), K1.
  apply (r2_q_ring_2 b c X).
Qed.

(* Step equation of the denominator table at an arbitrary index above    *)
(* zero, unfolded from the four-tuple recursion as in padeV_hd. *)
Lemma padeV_step_msq : forall (k j : nat),
  r2_msq (padeV (S (S k))) (S j) ==
  ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_msq (padeV (S k)) (S j)
  + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_msq (padeV k) j.
Proof.
  intros k j.
  unfold padeV.
  destruct (pade_pair k) as [[u0 u1][v0 v1]] eqn:Ek.
  rewrite (pade_pair_step (S k)), (pade_pair_step k), Ek.
  cbn [fst snd].
  assert (Hr1 : (2 * S (S k) + 1)%nat = (2 * k + 5)%nat) by lia.
  assert (Hr2 : (S (S k) * S (S k))%nat = ((k + 2) * (k + 2))%nat) by lia.
  rewrite Hr1, Hr2.
  rewrite r2_msq_vadd, r2_msq_vsmul, r2_msq_vsmul, r2_msq_shift.
  apply Qeq_refl.
Qed.

(* Step equation of the numerator table at an arbitrary index above      *)
(* zero, unfolded the same way. *)
Lemma padeU_step_nth : forall (k j : nat),
  nth (S j) (padeU (S (S k))) 0%Q ==
  ((Z.of_nat (2 * k + 5)) # 1)%Q * nth (S j) (padeU (S k)) 0%Q
  + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * nth j (padeU k) 0%Q.
Proof.
  intros k j.
  unfold padeU.
  destruct (pade_pair k) as [[u0 u1][v0 v1]] eqn:Ek.
  rewrite (pade_pair_step (S k)), (pade_pair_step k), Ek.
  cbn [fst snd].
  assert (Hr3 : (2 * S (S k) + 1)%nat = (2 * k + 5)%nat) by lia.
  assert (Hr4 : (S (S k) * S (S k))%nat = ((k + 2) * (k + 2))%nat) by lia.
  rewrite Hr3, Hr4.
  rewrite nth_vadd_gen, nth_vsmul_gen, nth_vsmul_gen.
  cbn [nth].
  apply Qeq_refl.
Qed.

(* The residual transports linearly under the two-step table recursion. *)
Lemma r2_coef_step : forall (k j : nat),
  r2_coef (S (S k)) (S j) ==
  ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S j)
  + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k j.
Proof.
  intros k j.
  unfold r2_coef.
  rewrite padeV_step_msq, padeU_step_nth.
  apply r2_q_linear.
Qed.

(* The numerator table entry above its degree is the zero padding, as a  *)
(* two-step induction over the order (Set-carried form, bid bridge). *)
Lemma padeU_pad_beyond : forall (m j : nat), (m + 1 < 2 * j)%nat ->
  bid (Qeq_bool (nth j (padeU m) 0%Q) 0%Q) true.
Proof.
  apply (nat_double_ind (fun m => forall j : nat,
    (m + 1 < 2 * j)%nat -> bid (Qeq_bool (nth j (padeU m) 0%Q) 0%Q) true)).
  - intros j Hj. destruct j as [|j']; [lia|].
    apply bidI. cbn. destruct j' as [|j'']; reflexivity.
  - intros j Hj. destruct j as [|j']; [lia|].
    apply bidI. cbn. destruct j' as [|j'']; reflexivity.
  - intros m IHm IHm1 j Hj.
    destruct j as [|j']; [lia|].
    assert (IHj : nth j' (padeU m) 0%Q == 0%Q).
    { pose proof (IHm j' (ltac:(lia))) as Hp. apply bidE in Hp. apply Qeq_bool_eq in Hp. exact Hp. }
    assert (IHj1 : nth (S j') (padeU (S m)) 0%Q == 0%Q).
    { pose proof (IHm1 (S j') (ltac:(lia))) as Hp. apply bidE in Hp. apply Qeq_bool_eq in Hp. exact Hp. }
    apply bidI. apply qeqbI.
    rewrite padeU_step_nth, IHj, IHj1.
    rewrite Qmult_0_r, Qmult_0_r, Qplus_0_l.
    apply Qeq_refl.
Qed.

(* The consumed residual is the mismatch-front coefficient of order 2n:  *)
(* the numerator table cannot reach degree 2n+1. *)
Lemma r2_res1_coef : forall n : nat,
  r2_res1 n == r2_coef (2 * n) (2 * n + 1).
Proof.
  intros n.
  pose proof (padeU_pad_beyond (2 * n) (2 * n + 1) (ltac:(lia))) as Hp.
  apply bidE in Hp. apply Qeq_bool_eq in Hp.
  unfold r2_coef.
  rewrite r2_res1_recip, Hp, r2_q_minus_0.
  apply Qeq_refl.
Qed.

(* =============== §3 The first-order ratio on the mismatch front =============== *)

(* A vanishing diagonal entry at order k+2 moves the mismatch front one  *)
(* step: (2k+5) R(k+1) = -(k+2)^2 R(k). *)
Lemma r2_ratio_step : forall k : nat,
  r2_coef (S (S k)) (S (S k)) == 0%Q ->
  ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S (S k)) ==
  - ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k (S k).
Proof.
  intros k H.
  pose proof (r2_coef_step k (S k)) as Hstep.
  rewrite H in Hstep.
  apply (r2_q_zero_move ((Z.of_nat (2 * k + 5)) # 1)%Q
                        ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q).
  exact Hstep.
Qed.

(* Even-step composition: two applications of r2_ratio_step give the     *)
(* two-step ratio on res1 itself. *)
Lemma r2_res1_step : forall n : nat,
  r2_coef (2 * n + 2) (2 * n + 2) == 0%Q ->
  r2_coef (2 * n + 3) (2 * n + 3) == 0%Q ->
  ((Z.of_nat (4 * n + 5)) # 1)%Q * (((Z.of_nat (4 * n + 7)) # 1)%Q * r2_res1 (S n)) ==
  ((Z.of_nat ((2 * n + 2) * (2 * n + 2))) # 1)%Q
    * (((Z.of_nat ((2 * n + 3) * (2 * n + 3))) # 1)%Q * r2_res1 n).
Proof.
  intros n H1 H2.
  assert (H1' : r2_coef (S (S (2 * n))) (S (S (2 * n))) == 0%Q).
  { assert (En1 : (S (S (2 * n)))%nat = (2 * n + 2)%nat) by lia. rewrite En1. exact H1. }
  assert (H2' : r2_coef (S (S (S (2 * n)))) (S (S (S (2 * n)))) == 0%Q).
  { assert (En2 : (S (S (S (2 * n))))%nat = (2 * n + 3)%nat) by lia. rewrite En2. exact H2. }
  pose proof (r2_ratio_step (2 * n) H1') as Ha.
  pose proof (r2_ratio_step (S (2 * n)) H2') as Hb.
  rewrite (r2_res1_coef (S n)), (r2_res1_coef n).
  assert (Hr5 : ((S (S (S (2 * n)))) )%nat = ( (2 * n + 3))%nat) by lia.
  rewrite Hr5 in Hb.
  assert (Hr6 : ((S (S (2 * n))) )%nat = ( (2 * n + 2))%nat) by lia.
  rewrite Hr6 in Ha, Hb.
  assert (Hr7 : ((S (2 * n)) )%nat = ( (2 * n + 1))%nat) by lia.
  rewrite Hr7 in Ha, Hb.
  assert (Hr8 : ((2 * (2 * n) + 5) )%nat = ( (4 * n + 5))%nat) by lia.
  rewrite Hr8 in Ha.
  assert (Hr9 : ((2 * (2 * n + 1) + 5) )%nat = ( (4 * n + 7))%nat) by lia.
  rewrite Hr9 in Hb.
  assert (Hr10 : ((2 * n + 1 + 2) )%nat = ( (2 * n + 3))%nat) by lia.
  rewrite Hr10 in Hb.
  assert (Hr11 : ((2 * S n) )%nat = ( (2 * n + 2))%nat) by lia.
  rewrite Hr11.
  assert (Hr12 : ((2 * n + 2 + 1) )%nat = ( (2 * n + 3))%nat) by lia.
  rewrite Hr12.
  apply (r2_q_step2 ((Z.of_nat (4 * n + 5)) # 1)%Q ((Z.of_nat (4 * n + 7)) # 1)%Q
                    ((Z.of_nat ((2 * n + 2) * (2 * n + 2))) # 1)%Q
                    ((Z.of_nat ((2 * n + 3) * (2 * n + 3))) # 1)%Q
                    _ _ (r2_coef (2 * n + 1) (2 * n + 2))).
  - exact Ha.
  - exact Hb.
Qed.

(* ================= §4 The closed form by induction ================= *)

Fixpoint r2_fact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S m => S m * r2_fact m
  end.

Lemma r2_fact_add2 : forall m : nat,
  r2_fact (m + 2) = (S (S m) * (S m * r2_fact m))%nat.
Proof.
  intros m. assert (Ef2 : (m + 2)%nat = (S (S m))%nat) by lia. rewrite Ef2.
  reflexivity.
Qed.

Lemma r2_fact_add4 : forall m : nat,
  r2_fact (m + 4) =
  (S (S (S (S m))) * (S (S (S m)) * (S (S m) * (S m * r2_fact m))))%nat.
Proof.
  intros m. assert (Ef4 : (m + 4)%nat = (S (S (S (S m))))%nat) by lia. rewrite Ef4.
  reflexivity.
Qed.

(* Binary factorial over Z: same values as r2_fact, computed in binary. *)
Fixpoint r2_zfact (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S m => Z.of_nat (S m) * r2_zfact m
  end.

(* ================= §5 Computational anchors ================= *)

(* Oracle anchors for the composed two-step ratio, read straight off the *)
(* tables by computation. *)
Lemma r2_step_anchor_0 :
  ((Z.of_nat (4 * 0 + 5)) # 1)%Q * (((Z.of_nat (4 * 0 + 7)) # 1)%Q * r2_res1 1) ==
  ((Z.of_nat ((2 * 0 + 2) * (2 * 0 + 2))) # 1)%Q
    * (((Z.of_nat ((2 * 0 + 3) * (2 * 0 + 3))) # 1)%Q * r2_res1 0).
Proof. vm_compute. reflexivity. Qed.

Lemma r2_step_anchor_1 :
  ((Z.of_nat (4 * 1 + 5)) # 1)%Q * (((Z.of_nat (4 * 1 + 7)) # 1)%Q * r2_res1 2) ==
  ((Z.of_nat ((2 * 1 + 2) * (2 * 1 + 2))) # 1)%Q
    * (((Z.of_nat ((2 * 1 + 3) * (2 * 1 + 3))) # 1)%Q * r2_res1 1).
Proof. vm_compute. reflexivity. Qed.

Lemma r2_step_anchor_2 :
  ((Z.of_nat (4 * 2 + 5)) # 1)%Q * (((Z.of_nat (4 * 2 + 7)) # 1)%Q * r2_res1 3) ==
  ((Z.of_nat ((2 * 2 + 2) * (2 * 2 + 2))) # 1)%Q
    * (((Z.of_nat ((2 * 2 + 3) * (2 * 2 + 3))) # 1)%Q * r2_res1 2).
Proof. vm_compute. reflexivity. Qed.

(* Oracle anchors for the closed form at n = 1..3. *)
Lemma r2_closed_anchor_1 :
  ((r2_zfact (4 * 1 + 3)) # 1)%Q * r2_res1 1 ==
  (- ((2 ^ (Z.of_nat (2 * 1 + 1))
        * r2_zfact (2 * 1 + 1) * r2_zfact (2 * 1 + 1) * r2_zfact (2 * 1 + 1)) # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma r2_closed_anchor_2 :
  ((r2_zfact (4 * 2 + 3)) # 1)%Q * r2_res1 2 ==
  (- ((2 ^ (Z.of_nat (2 * 2 + 1))
        * r2_zfact (2 * 2 + 1) * r2_zfact (2 * 2 + 1) * r2_zfact (2 * 2 + 1)) # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma r2_closed_anchor_3 :
  ((r2_zfact (4 * 3 + 3)) # 1)%Q * r2_res1 3 ==
  (- ((2 ^ (Z.of_nat (2 * 3 + 1))
        * r2_zfact (2 * 3 + 1) * r2_zfact (2 * 3 + 1) * r2_zfact (2 * 3 + 1)) # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions r2_res1_step.
Print Assumptions r2_res1_coef.
Print Assumptions r2_closed_anchor_3.
