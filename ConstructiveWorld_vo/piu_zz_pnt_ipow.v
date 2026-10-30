(* ==========================================================================
   Module: piu_zz_pnt_ipow
   Mission: Integer-power certificate machinery for the effective-PNT
     consumption chain (node B5.4): nat powers of a rational, the exact
     split (F/p)^M = F^M / p^M as a boolean identity, the two-sided
     floor sandwich floor(a/p) <= a/p <= floor(a/p) + 1 and the matching
     ceiling sandwich (the C = ceil(e^{rD}) certificate face), the
     relative-loss bound x*(D-1)/D <= floor(x) for x >= D >= 2 (the
     D = 10^4 face of the budget, where the unit rounding loss of an
     integer certificate is absorbed), and the power-level instance
     x^M*(D-1)/D <= floor(x^M). The Taylor monotonicity and the e^20
     anchor of the qexp module are re-faced at statement level as the
     numeric consumption points.
   Dependencies: S03_QExp (exp_partial), piu_zz_padic_clearing (BidT),
     piu_zz_poincare_engine (QleT', qleT_intro, zq),
     piu_zz_pnt_qexp (zz_qexp_partial_mono, zz_qexp_e20_below_X0),
     Stdlib QArith/ZArith/Arith/PArith/Lia/Bool.
   References: the integer-certificate budget with D = 10^4 and ceiling
     relative error 1/D (kb33 budget document, section 6.3); the
     certificate interface forms of the kb34 statement draft, sections
     4-5; stdlib Z.div_mod and Z.mod_pos_bound carry the floor and
     ceiling bounds.
   Constructivity: statement faces Set-carried (QleT', BidT); all
     definitions are transparent Fixpoints; symbolic ordering faces
     close by cross-multiplied conversion with nia/lia over Z; numeric
     faces close by ground arithmetic on boolean comparisons; every
     lemma closes with a full proof under the global context.
   Build: coqc -native-compiler no -q
     -Q <certified vo tree> "" -Q <kb35 born tree> "" -Q <this dir> ""
     piu_zz_pnt_ipow.v  (single compile lane under cpu_guard wrap).
   ========================================================================== *)

From Stdlib Require Import QArith ZArith Arith PArith Lia Bool.
Require Import S03_QExp.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_pnt_qexp.

Local Open Scope Q_scope.

(* ================= Section 1. Nat powers of a rational ================= *)

(* Nat-indexed power of a rational, transparent and right-associative. *)
Fixpoint zz_pnt_qnpow (x : Q) (M : nat) : Q :=
  match M with
  | O => Qmake 1 1
  | S m => zz_pnt_qnpow x m * x
  end.

(* Nat-indexed power of an integer: the numerator of (F/p)^M. *)
Fixpoint zz_pnt_znpow (F : Z) (M : nat) : Z :=
  match M with
  | O => 1%Z
  | S m => zz_pnt_znpow F m * F
  end.

(* Nat-indexed power of a positive: the denominator of (F/p)^M, kept
   positive so that Qmake applies directly. *)
Fixpoint zz_pnt_dnpow (d : positive) (M : nat) : positive :=
  match M with
  | O => xH
  | S m => Pos.mul (zz_pnt_dnpow d m) d
  end.

Lemma zz_pnt_qleT_trans : forall a b c : Q,
  QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c H1 H2. destruct H1 as [H1]. destruct H2 as [H2].
  apply qleT_intro. apply (Qle_trans a b c H1 H2).
Qed.

Lemma zz_pnt_qleT_eq_r : forall a b c : Q, QleT' a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc. destruct H as [H]. apply qleT_intro.
  rewrite Hbc in H. exact H.
Qed.

Lemma zz_pnt_qnpow_nonneg : forall (M : nat) (x : Q),
  QleT' (Qmake 0 1) x -> QleT' (Qmake 0 1) (zz_pnt_qnpow x M).
Proof.
  induction M as [|m IH]; intros x Hx0.
  - apply qleT_intro. unfold Qle. cbn. lia.
  - destruct (IH x Hx0) as [Hih]. destruct Hx0 as [Hx0].
    apply qleT_intro. cbn [zz_pnt_qnpow].
    apply Qmult_le_0_compat. exact Hih. exact Hx0.
Qed.

Lemma zz_pnt_qnpow_mono : forall (M : nat) (x y : Q),
  QleT' (Qmake 0 1) x -> QleT' x y ->
  QleT' (zz_pnt_qnpow x M) (zz_pnt_qnpow y M).
Proof.
  induction M as [|m IH]; intros x y Hx0 Hxy.
  - apply qleT_intro. unfold Qle. cbn. lia.
  - destruct (IH x y Hx0 Hxy) as [Hih].
    destruct (zz_pnt_qnpow_nonneg m x Hx0) as [Hxm].
    destruct (zz_pnt_qnpow_nonneg m y
      (zz_pnt_qleT_trans (Qmake 0 1) x y Hx0 Hxy)) as [Hym].
    destruct Hxy as [Hxy]. destruct Hx0 as [Hx0].
    assert (Hle0y : (0 <= y)%Q) by (apply (Qle_trans 0 x y Hx0 Hxy)).
    apply qleT_intro. cbn [zz_pnt_qnpow].
    apply (Qle_trans (zz_pnt_qnpow x m * x) (zz_pnt_qnpow x m * y)
                     (zz_pnt_qnpow y m * y)).
    + rewrite (Qmult_comm (zz_pnt_qnpow x m) x).
      rewrite (Qmult_comm (zz_pnt_qnpow x m) y).
      apply Qmult_le_compat_r. exact Hxy. exact Hxm.
    + apply Qmult_le_compat_r. exact Hih. exact Hle0y.
Qed.

(* Rounding the unit factor: x <= x * 1. *)
Lemma zz_pnt_qmul_r1 : forall x : Q, QleT' x (x * Qmake 1 1).
Proof.
  intro x. apply qleT_intro. unfold Qle. cbn [Qmult Qnum Qden].
  rewrite Pos.mul_1_r, Z.mul_1_r. apply Qle_refl.
Qed.

(* Power monotonicity in the exponent above the unit: x >= 1 implies
   x^M <= x^(M+1). *)
Lemma zz_pnt_qnpow_mono_exp : forall (M : nat) (x : Q),
  QleT' (Qmake 1 1) x ->
  QleT' (zz_pnt_qnpow x M) (zz_pnt_qnpow x (S M)).
Proof.
  intros M x Hx.
  apply (zz_pnt_qleT_trans (zz_pnt_qnpow x M) (zz_pnt_qnpow x M * Qmake 1 1)).
  - apply zz_pnt_qmul_r1.
  - assert (Hx0 : QleT' (Qmake 0 1) x).
    { apply (zz_pnt_qleT_trans (Qmake 0 1) (Qmake 1 1) x).
      - apply qleT_intro. unfold Qle. cbn. lia.
      - exact Hx. }
    destruct (zz_pnt_qnpow_nonneg M x Hx0) as [Ham]. destruct Hx as [Hx].
    apply qleT_intro. cbn [zz_pnt_qnpow].
    apply zz_pnt_qleT_trans with (Qmult (Qmake 1 1) (zz_pnt_qnpow x M)).
    + apply qleT_intro. unfold Qle. cbn [Qmult Qnum Qden]. lia.
    + apply zz_pnt_qleT_eq_r with (b := Qmult x (zz_pnt_qnpow x M)).
      * apply qleT_intro. apply Qmult_le_compat_r. exact Hx. exact Ham.
      * apply Qmult_comm.
Qed.

(* x >= 1 implies x <= x^(S m). *)
Lemma zz_pnt_qnpow_ge1 : forall (m : nat) (x : Q),
  QleT' (Qmake 1 1) x -> QleT' x (zz_pnt_qnpow x (S m)).
Proof.
  induction m as [|m IH]; intros x Hx.
  - apply qleT_intro. cbn [zz_pnt_qnpow]. unfold Qle.
    cbn [Qmult Qnum Qden]. lia.
  - apply (zz_pnt_qleT_trans x (zz_pnt_qnpow x (S m))).
    + apply IH. exact Hx.
    + apply zz_pnt_qnpow_mono_exp. exact Hx.
Qed.

(* x >= 1 and M >= 1 imply x^M >= x. *)
Lemma zz_pnt_qnpow_ge_self : forall (M : nat) (x : Q),
  QleT' (Qmake 1 1) x -> (1 <= M)%nat ->
  QleT' x (zz_pnt_qnpow x M).
Proof.
  intros M x Hx HM. destruct M as [|m]; [lia|].
  apply (zz_pnt_qnpow_ge1 m x Hx).
Qed.

(* ================= Section 2. Exact power split ================= *)

(* The nat power of the fixed-point rational is the rational of the
   powers: (F/p)^M = F^M / p^M exactly. *)
Lemma zz_pnt_qipow_qsplit : forall (F : Z) (d : positive) (M : nat),
  BidT (Qeq_bool (zz_pnt_qnpow (Qmake F d) M)
                 (Qmake (zz_pnt_znpow F M) (zz_pnt_dnpow d M))).
Proof.
  intros F d M. induction M as [|m IH].
  - apply BidT_intro. cbn [zz_pnt_qnpow zz_pnt_znpow zz_pnt_dnpow].
    vm_compute. reflexivity.
  - apply Bid_elim in IH. apply Qeq_bool_eq in IH.
    apply BidT_intro.
    cbn [zz_pnt_qnpow zz_pnt_znpow zz_pnt_dnpow].
    rewrite IH.
    unfold Qeq_bool. rewrite Z.eqb_eq.
    cbn [Qnum Qden Qmult Pos.mul].
    rewrite Pos2Z.inj_mul. ring.
Qed.

(* ================= Section 3. Floor and ceiling sandwiches ================= *)

(* The floor sandwich: for any integer a and positive p, the integer
   certificate q = a/p loses at most one unit against the exact
   rational a/p on each side. *)
Lemma zz_pnt_bdiv_floor_sandwich : forall (a : Z) (p : positive),
  prod (QleT' (Qmake a p)
               (Qmake (Z.div a (Z.pos p) + 1) 1))
       (QleT' (Qmake (Z.div a (Z.pos p)) 1)
              (Qmake a p)).
Proof.
  intros a p.
  assert (Hp : (Z.pos p <> 0)%Z) by lia.
  pose proof (Z.div_mod a (Z.pos p) Hp) as Hdm.
  pose proof (Z.mod_pos_bound a (Z.pos p) ltac:(lia)) as Hmb.
  split.
  - apply qleT_intro. unfold Qle. cbn [Qnum Qden]. nia.
  - apply qleT_intro. unfold Qle. cbn [Qnum Qden]. nia.
Qed.

(* The power-level floor sandwich: the M-th power of the fixed-point
   rational F/p, taken as the exact rational F^M / p^M, keeps integer
   certificates up to the same one-unit loss. *)
Theorem zz_pnt_ipow_floor_sandwich : forall (F : Z) (d : positive) (M : nat),
  prod (QleT' (Qmake (zz_pnt_znpow F M) (zz_pnt_dnpow d M))
               (Qmake (Z.div (zz_pnt_znpow F M)
                             (Z.pos (zz_pnt_dnpow d M)) + 1) 1))
       (QleT' (Qmake (Z.div (zz_pnt_znpow F M)
                            (Z.pos (zz_pnt_dnpow d M))) 1)
              (Qmake (zz_pnt_znpow F M) (zz_pnt_dnpow d M))).
Proof.
  intros F d M. apply zz_pnt_bdiv_floor_sandwich.
Qed.

(* The ceiling certificate ceil(a/p) = - floor(-a/p) brackets the exact
   rational from above with the same one-unit loss; this is the
   integer-certificate face C = ceil(e^{rD}). *)
Definition zz_pnt_bceil (a : Z) (p : positive) : Z :=
  Z.opp (Z.div (Z.opp a) (Z.pos p)).

Lemma zz_pnt_bceil_sandwich : forall (a : Z) (p : positive),
  prod (QleT' (Qmake a p) (Qmake (zz_pnt_bceil a p) 1))
       (QleT' (Qmake (zz_pnt_bceil a p) 1)
              (Qmake (a + Z.pos p) p)).
Proof.
  intros a p.
  destruct (zz_pnt_bdiv_floor_sandwich (Z.opp a) p) as [Hu Hl].
  split.
  - destruct Hl as [Hl]. apply qleT_intro. unfold Qle in Hl.
    cbn [Qnum Qden] in Hl. unfold Qle. unfold zz_pnt_bceil.
    cbn [Qnum Qden]. lia.
  - destruct Hu as [Hu]. apply qleT_intro. unfold Qle in Hu.
    cbn [Qnum Qden] in Hu. unfold Qle. unfold zz_pnt_bceil.
    cbn [Qnum Qden]. lia.
Qed.

(* ================= Section 4. Relative loss face (D = 10^4) ================= *)

(* Multiplicative splitting of the integer power over a factored base. *)
Lemma zz_pnt_znpow_pos_mul : forall (G H : Z) (M : nat),
  zz_pnt_znpow (G * H)%Z M = (zz_pnt_znpow G M * zz_pnt_znpow H M)%Z.
Proof.
  intros G H M. induction M as [|m IH]; cbn [zz_pnt_znpow].
  - ring.
  - rewrite IH. ring.
Qed.

(* The positive power of a positive is the integer power. *)
Lemma zz_pnt_znpow_pos_p : forall (p : positive) (M : nat),
  Z.pos (zz_pnt_dnpow p M) = zz_pnt_znpow (Z.pos p) M.
Proof.
  intros p M. induction M as [|m IH]; cbn [zz_pnt_dnpow zz_pnt_znpow].
  - reflexivity.
  - rewrite Pos2Z.inj_mul, IH. ring.
Qed.

Lemma zz_pnt_znpow_nonneg : forall (H : Z) (M : nat),
  (0 <= H)%Z -> (0 <= zz_pnt_znpow H M)%Z.
Proof.
  intros H M HH. induction M as [|m IH].
  - cbn. lia.
  - cbn [zz_pnt_znpow]. nia.
Qed.

Lemma zz_pnt_znpow_mono : forall (G H : Z) (M : nat),
  (0 <= G)%Z -> (G <= H)%Z -> (zz_pnt_znpow G M <= zz_pnt_znpow H M)%Z.
Proof.
  intros G H M HG HGle. induction M as [|m IH].
  - cbn. lia.
  - cbn [zz_pnt_znpow].
    pose proof (zz_pnt_znpow_nonneg G m ltac:(lia)) as HzG.
    pose proof (zz_pnt_znpow_nonneg H m ltac:(lia)) as HzH.
    nia.
Qed.

(* The base itself never exceeds its powers above the threshold two. *)
Lemma zz_pnt_znpow_D_le : forall (D : Z) (M : nat),
  (2 <= D)%Z -> (1 <= M)%nat -> (D <= zz_pnt_znpow D M)%Z.
Proof.
  intros D M HD HM.
  assert (Hstep : forall k : nat,
    (D <= zz_pnt_znpow D k)%Z -> (D <= zz_pnt_znpow D (S k))%Z).
  { intros k Hk. cbn [zz_pnt_znpow].
    assert (Hz : (0 <= zz_pnt_znpow D k)%Z) by (apply zz_pnt_znpow_nonneg; lia).
    nia. }
  destruct M as [|m]; [lia|].
  induction m as [|m IH].
  - cbn [zz_pnt_znpow]. lia.
  - apply Hstep. apply IH. lia.
Qed.

(* Growth lower bound: from F >= D*p with D >= 2, the M-th power of the
   fixed point dominates D times its denominator. *)
Lemma zz_pnt_znpow_ge : forall (F : Z) (p : positive) (D : Z) (M : nat),
  (1 < D)%Z -> (D * Z.pos p <= F)%Z -> (1 <= M)%nat ->
  (D * Z.pos (zz_pnt_dnpow p M) <= zz_pnt_znpow F M)%Z.
Proof.
  intros F p D M HD Hfp HM.
  assert (Hmono : (zz_pnt_znpow (D * Z.pos p) M <= zz_pnt_znpow F M)%Z)
    by (apply zz_pnt_znpow_mono; lia).
  rewrite zz_pnt_znpow_pos_mul in Hmono.
  rewrite <- zz_pnt_znpow_pos_p in Hmono.
  pose proof (zz_pnt_znpow_D_le D M ltac:(lia) HM) as HDle.
  assert (Hdp : (0 < Z.pos (zz_pnt_dnpow p M))%Z) by (apply Pos2Z.is_pos).
  nia.
Qed.

(* The relative-loss bound: for x = a/p >= D >= 2 the floor certificate
   already dominates x*(D-1)/D — the rounding loss is absorbed once the
   certificate scale D is fixed (D = 10^4 in the budget). *)
Lemma zz_pnt_floor_rel : forall (a : Z) (p D : positive),
  (1 < Z.pos D)%Z ->
  QleT' (Qmake (Z.pos D) 1) (Qmake a p) ->
  QleT' (Qmake (a * (Z.pos D - 1)) (Pos.mul p D))
        (Qmake (Z.div a (Z.pos p)) 1).
Proof.
  intros a p D HD Hx.
  assert (Hp : (Z.pos p <> 0)%Z) by lia.
  pose proof (Z.div_mod a (Z.pos p) Hp) as Hdm.
  pose proof (Z.mod_pos_bound a (Z.pos p) ltac:(lia)) as Hmb.
  destruct Hx as [Hx]. unfold Qle in Hx. cbn [Qnum Qden] in Hx.
  assert (Hq : (Z.pos D <= a / Z.pos p)%Z) by nia.
  apply qleT_intro. unfold Qle. cbn [Qnum Qden].
  rewrite Pos2Z.inj_mul. nia.
Qed.

(* Power-level relative loss: with x = F/p >= D >= 2 and M >= 1, the
   floor of x^M dominates x^M*(D-1)/D. *)
Theorem zz_pnt_ipow_rel_D : forall (F : Z) (p D : positive) (M : nat),
  (1 < Z.pos D)%Z ->
  QleT' (Qmake (Z.pos D) 1) (Qmake F p) ->
  (1 <= M)%nat ->
  QleT' (Qmake (zz_pnt_znpow F M * (Z.pos D - 1))
               (Pos.mul (zz_pnt_dnpow p M) D))
        (Qmake (Z.div (zz_pnt_znpow F M)
                      (Z.pos (zz_pnt_dnpow p M))) 1).
Proof.
  intros F p D M HD HxD HM.
  destruct HxD as [HxD]. unfold Qle in HxD. cbn [Qnum Qden] in HxD.
  assert (Hkey : (Z.pos D * Z.pos (zz_pnt_dnpow p M) <= zz_pnt_znpow F M)%Z).
  { apply (zz_pnt_znpow_ge F p (Z.pos D) M); try lia. }
  apply (zz_pnt_floor_rel (zz_pnt_znpow F M) (zz_pnt_dnpow p M) D HD).
  apply qleT_intro. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ================= Section 5. Numeric consumption points ================= *)

(* Numeric sample of the floor sandwich at the fixed point 271828/10^5:
   its square is 73890461584/10^10 and the integer certificates 7 and 8
   bracket it with the one-unit loss (exact value 7.3890461584). *)
Theorem zz_pnt_ipow_sample :
  prod (QleT' (Qmake 73890461584 10000000000 - Qmake 1 1) (Qmake 7 1))
       (QleT' (Qmake 7 1) (Qmake 73890461584 10000000000)).
Proof.
  split.
  - apply qleT_intro. unfold Qle. cbn. lia.
  - apply qleT_intro. unfold Qle. cbn. lia.
Qed.

(* The Taylor partial-sum monotonicity of the qexp module, consumed at
   the anchor argument x = 20: the order-41 sum dominates the order-40
   sum. *)
Theorem zz_pnt_exp_mono_sample :
  QleT' (exp_partial 40%nat (Qmake 20 1)) (exp_partial 41%nat (Qmake 20 1)).
Proof.
  apply (zz_qexp_partial_mono (Qmake 20 1) 40%nat).
  apply qleT_intro. unfold Qle. cbn. lia.
Qed.

(* The e^20 anchor of the qexp module, re-faced: the order-40 partial
   sum of e^20 lies below 664,000,000. *)
Theorem zz_pnt_e20_below :
  BidT (Qle_bool (exp_partial 40%nat (Qmake 20 1)) (Qmake 664000000 1)).
Proof.
  exact zz_qexp_e20_below_X0.
Qed.

(* ================= Section 6. Certification face ================= *)

Print Assumptions zz_pnt_ipow_floor_sandwich.
Print Assumptions zz_pnt_ipow_rel_D.
Print Assumptions zz_pnt_ipow_sample.
Print Assumptions zz_pnt_exp_mono_sample.

From Stdlib Require Import Extraction.
Separate Extraction zz_pnt_qnpow zz_pnt_znpow zz_pnt_dnpow zz_pnt_bceil
  zz_pnt_ipow_floor_sandwich zz_pnt_ipow_rel_D zz_pnt_ipow_sample
  zz_pnt_exp_mono_sample zz_pnt_e20_below.
