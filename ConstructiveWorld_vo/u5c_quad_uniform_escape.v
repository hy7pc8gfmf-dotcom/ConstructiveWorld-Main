(* Five-field header
   1. Mission: uniform escape parameterization for sqrt-d (GEDAN-sqrt-d P1).
      For every positive integer d carrying a Set-level non-square premise
      (d is not a perfect square), and every rational q, there exists an
      explicit rational constant c > 0 strictly separating the constant
      real c from the real metric distance between the Newton sequence of
      sqrt(d) and the rational point q.  This generalizes the sqrt-2
      closed-measure blueprint to a uniform statement in d: the integer-gap
      core |a^2 - d*b^2| >= 1 (d non-square) replaces the parity descent.
   2. Dependencies: S01_BaseRing, S02_CauchyComplete, S03_QExp,
      SumInvFactEscape, UpReqBanachNormOpp, UpReqIrrationalCriterion,
      UpReqSqrt3Irrational (pure-Q helpers ir2_sq_mono / ir2_sq_diff /
      ir2_abs_sub / ir2_qpos_add / ir2_inv_le / ir2_mult_le_compat_l /
      ir2_le_inv / ir2_inv_pos / ir2_le_mul_inv / ir2_add_le_r /
      ir2_ge0_of_mul / ir2_pow_ge), u5c_dm_escape_window (dmew_Qinv_1p);
      Stdlib QArith, Qabs, ZArith, Znumtheory, Arith, Bool, Lia, Setoid,
      Morphisms, Qfield.  All eight contract files are consumed read-only
      (require-only, zero modification).
   3. Benchmark lines: UpReqIrrationalCriterion.v lic_irrational_criterion
      (mother theorem, conclusion identical to the main theorem statement);
      u5c_sqrt2_closed_measure.v dmcm_margin_closed (four-branch margin
      blueprint) and u5c_sqrt2_closed_measure_q; u5c_dm_escape_window.v
      dmew_e_bnd (uniform window bound); UpReqSqrt3Irrational.v ir2_gap_lower
      (generalized here to u5c_quad_gap_lower), ir2_tail, ir2_vanish.
   4. Constructive notes: the statement face is entirely Set-carried
      (sigT / And / QltT / Id), zero new Prop axioms, zero classical logic.
      The non-square premise is the Set-level boolean identity
      u5c_quad_nonsq d := Id (Z.eqb (sqrt d * sqrt d) d) false (extractable).
      The integer-gap core is carried by the independent Set-level lemma
      u5c_quad_gap_abs : |a^2 - d*(b*b)| >= 1 as Id (Z.leb 1 (Z.abs ...)) true,
      backed by the gcd-descent lemma u5c_quad_sq_z (Prop, proof-internal,
      same convention as ir2_no_sqrtZ in the contract files).  Newton
      sequence x_d(0)=d, x_d(n+1)=(x_d(n)+d/x_d(n))/2 with decay
      delta(n+1) <= delta(n)/4 uniformly in n, e(n) = delta(n)/2, and the
      uniform window index n0 = 2*d + 2*b + K_d (K_d = 4d+8) in nat powers
      of 4.  Proof bodies use Prop reasoning where the pool convention does
      (Qle chains, Z discreteness); all witness-bearing statements stay Set.
   5. Compile recipe:
      C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe -native-compiler no -q
        -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
        -Q D:/ComplexAnalysis/attn/kb58_work_20261029 "" u5c_quad_uniform_escape.v
      (wrapped in _guard_v3.ps1, TempLimit 98, per the thermal-control rule). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_window.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import ZArith.Znumtheory.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0. Set-carried non-square premise and the integer-gap core  *)
(* ============================================================ *)

(* Separation constant rank: K_d = 4d + 8 (positive).  All four margin
   branches have positive slack against 3(d+1) and 6. *)
Definition u5c_quad_K (d : positive) : positive := (4 * d + 8)%positive.

Lemma u5c_quad_K_eq : forall d : positive,
  Z.pos (u5c_quad_K d) = (4 * Z.pos d + 8)%Z.
Proof.
  intro d. unfold u5c_quad_K.
  rewrite Pos2Z.inj_add, Pos2Z.inj_mul. reflexivity.
Qed.

(* Set-carried non-square premise (boolean witness, extractable). *)
Definition u5c_quad_nonsq (d : positive) : Set :=
  Id (Z.eqb (Z.sqrt (Z.pos d) * Z.sqrt (Z.pos d)) (Z.pos d)) false.

Lemma u5c_quad_nonsq_false : forall d : positive,
  u5c_quad_nonsq d ->
  (Z.eqb (Z.sqrt (Z.pos d) * Z.sqrt (Z.pos d)) (Z.pos d)) = false.
Proof.
  intros d H. unfold u5c_quad_nonsq in H.
  destruct (Z.eqb (Z.sqrt (Z.pos d) * Z.sqrt (Z.pos d)) (Z.pos d)) eqn:E.
  - exfalso.
    destruct (match H in Id _ y
                return (match y with true => unit | false => Empty_set end)
              with id_refl => tt end).
  - try (rewrite E). reflexivity.
Qed.

(* Z.sqrt is exact on perfect squares of nonnegative integers. *)
Lemma u5c_quad_sqrt_sq : forall k : Z, (0 <= k)%Z -> Z.sqrt (k * k) = k.
Proof.
  intros k Hk. apply Z.sqrt_unique. split.
  - lia.
  - unfold Z.succ. nia.
Qed.

(* A nonnegative k with k^2 = d contradicts the non-square premise. *)
Lemma u5c_quad_sq_sqrt : forall (d : positive) (k : Z),
  (0 <= k)%Z -> (k * k = Z.pos d)%Z -> u5c_quad_nonsq d -> False.
Proof.
  intros d k Hk0 Hkk Hd.
  assert (Heqb : (Z.eqb (Z.sqrt (Z.pos d) * Z.sqrt (Z.pos d)) (Z.pos d)) = true).
  { apply Z.eqb_eq. rewrite <- Hkk.
    rewrite (u5c_quad_sqrt_sq k Hk0). reflexivity. }
  pose proof (u5c_quad_nonsq_false d Hd) as Hf.
  rewrite Heqb in Hf. discriminate Hf.
Qed.

(* Non-square d is at least 2. *)
Lemma u5c_quad_d_ge2 : forall d : positive, u5c_quad_nonsq d -> (2 <= Z.pos d)%Z.
Proof.
  intros d Hd. destruct (Z_le_gt_dec 2 (Z.pos d)) as [Hle | Hgt].
  - exact Hle.
  - exfalso. apply (u5c_quad_sq_sqrt d 1); [lia | lia | exact Hd].
Qed.

(* Core descent (gcd cancellation): a^2 = d*b^2 with b <> 0 is impossible
   for non-square d.  Standard Bezout descent via Z.gcd. *)
Lemma u5c_quad_sq_z : forall (d : positive), u5c_quad_nonsq d ->
  forall a b : Z, (b <> 0)%Z -> (a * a = Z.pos d * (b * b))%Z -> False.
Proof.
  intros d Hd a b Hb0 Heq.
  pose proof (Z.gcd_divide_l a b) as Hdl.
  pose proof (Z.gcd_divide_r a b) as Hdr.
  pose proof (Z.gcd_nonneg a b) as Hgn.
  remember (Z.gcd a b) as g eqn:Eg.
  assert (Hg0 : (g <> 0)%Z).
  { intro Hgz. apply Hb0.
    destruct Hdr as [q Eq]. rewrite Eq, Hgz. apply Z.mul_0_r. }
  destruct Hdl as [a1 Ea1]. destruct Hdr as [b1 Eb1].
  assert (Hgg0 : (g * g <> 0)%Z).
  { intro Hgg. apply Hg0.
    destruct (proj1 (Z.mul_eq_0 g g) Hgg) as [H | H]; exact H. }
  assert (Ha1 : (a1 * a1 = Z.pos d * (b1 * b1))%Z).
  { apply (proj1 (Z.mul_cancel_l (a1 * a1) (Z.pos d * (b1 * b1)) (g * g) Hgg0)).
    rewrite Ea1, Eb1 in Heq.
    assert (E2 : ((a1 * g) * (a1 * g) = (g * g) * (a1 * a1))%Z) by ring.
    assert (E3 : (Z.pos d * ((b1 * g) * (b1 * g))
                   = (g * g) * (Z.pos d * (b1 * b1)))%Z) by ring.
    rewrite <- E2, <- E3. exact Heq. }
  assert (Hg1 : (Z.gcd a1 b1 = 1)%Z).
  { pose proof (Z.gcd_mul_mono_l a1 b1 g) as Hmm.
    assert (HmL : (Z.gcd (g * a1) (g * b1) = g)%Z).
    { rewrite (Z.mul_comm g a1), (Z.mul_comm g b1), <- Ea1, <- Eb1.
      rewrite Eg. reflexivity. }
    rewrite HmL in Hmm.
    rewrite Z.abs_eq in Hmm by exact Hgn.
    assert (Hc : (1 * g = Z.gcd a1 b1 * g)%Z).
    { rewrite Z.mul_1_l, Z.mul_comm. exact Hmm. }
    symmetry. exact (proj1 (Z.mul_cancel_r 1 (Z.gcd a1 b1) g Hg0) Hc). }
  pose proof (Zgcd_is_gcd a1 b1) as Hgc. rewrite Hg1 in Hgc.
  destruct (Zis_gcd_bezout a1 b1 1 Hgc) as [u v Huv].
  assert (Hdvd1 : Z.divide b1 (a1 * a1)).
  { apply (Zdivide_intro b1 (a1 * a1) (Z.pos d * b1)).
    rewrite Ha1. ring. }
  assert (Hdvd2 : Z.divide b1 a1).
  { apply (Zdivide_intro b1 a1 (u * (Z.pos d * b1) + v * a1)).
    assert (E1 : (a1 = (u * a1 + v * b1) * a1)%Z) by (rewrite Huv; ring).
    assert (E2b : ((u * (Z.pos d * b1) + v * a1) * b1
                   = (u * (Z.pos d * (b1 * b1)) + v * (a1 * b1)))%Z) by ring.
    assert (E3b : (u * (a1 * a1) + v * (a1 * b1)
                   = (u * a1 + v * b1) * a1)%Z) by ring.
    rewrite E2b, <- Ha1, E3b, Huv. ring. }
  assert (Hdvd3 : Z.divide b1 1).
  { rewrite <- Huv. apply Z.divide_add_r.
    - destruct Hdvd2 as [c Hc].
      apply (Zdivide_intro b1 (u * a1) (u * c)). rewrite Hc. ring.
    - apply (Zdivide_intro b1 (v * b1) v). ring. }
  assert (Hb1sq : (b1 * b1 = 1)%Z).
  { destruct (Z.divide_1_r b1 Hdvd3) as [E | E]; rewrite E; reflexivity. }
  rewrite Hb1sq in Ha1.
  assert (Hab : (Z.abs a1 * Z.abs a1 = a1 * a1)%Z).
  { rewrite <- Z.abs_mul. apply Z.abs_eq.
    pose proof Ha1. pose proof (Pos2Z.is_pos d). lia. }
  exfalso. apply (u5c_quad_sq_sqrt d (Z.abs a1)).
  - apply Z.abs_nonneg.
  - lia.
  - exact Hd.
Qed.

(* No rational square root of d. *)
Lemma u5c_quad_no_sqrtQ : forall (d : positive), u5c_quad_nonsq d ->
  forall q : Q, ~ (q * q == (Z.pos d # 1)%Q).
Proof.
  intros d Hd q Hq. destruct q as [a b].
  assert (Heq : (a * a = Z.pos d * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn [Qnum Qden Qmult] in Hq.
    rewrite (Pos2Z.inj_mul b b) in Hq. lia. }
  exact (u5c_quad_sq_z d Hd a (Z.pos b) (ltac:(intro Hz; discriminate Hz)) Heq).
Qed.

(* The mandated integer-gap core, Set-carried:
   |a^2 - d*(b*b)| >= 1 for non-square d. *)
Lemma u5c_quad_gap_abs : forall (d : positive) (a : Z) (b : positive),
  u5c_quad_nonsq d ->
  Id (Z.leb 1 (Z.abs (a * a - Z.pos d * (Z.pos b * Z.pos b)))) true.
Proof.
  intros d a b Hd.
  assert (Hne : (a * a <> Z.pos d * (Z.pos b * Z.pos b))%Z).
  { intro Hc. exact (u5c_quad_sq_z d Hd a (Z.pos b)
        (ltac:(intro Hz; discriminate Hz)) Hc). }
  destruct (Z.leb 1 (Z.abs (a * a - Z.pos d * (Z.pos b * Z.pos b)))) eqn:E.
  - exact (match E with eq_refl => id_refl end).
  - exfalso. apply Z.leb_gt in E.
    pose proof (Z.abs_nonneg (a * a - Z.pos d * (Z.pos b * Z.pos b))) as Hnn.
    assert (Habs0 : Z.abs (a * a - Z.pos d * (Z.pos b * Z.pos b)) = (0)%Z) by lia.
    rewrite (Z.abs_neq (a * a - Z.pos d * (Z.pos b * Z.pos b))
              (ltac:(lia))) in Habs0.
    apply Hne. lia.
Qed.

(* ============================================================ *)
(* S1. The sqrt-d Newton sequence family at Q level             *)
(* ============================================================ *)

Fixpoint u5c_quad_x (d : positive) (n : nat) : Q :=
  match n with
  | O => (Z.pos d # 1)%Q
  | Datatypes.S m =>
      (u5c_quad_x d m + (Z.pos d # 1)%Q / u5c_quad_x d m) * (1 # 2)
  end.

Definition u5c_quad_delta (d : positive) (n : nat) : Q :=
  u5c_quad_x d n * u5c_quad_x d n - (Z.pos d # 1)%Q.

Definition u5c_quad_e (d : positive) (n : nat) : Q :=
  (1 # 2) * u5c_quad_delta d n.

(* 4^n carried as a positive (QDen position; keeps matches reducible). *)
Fixpoint u5c_quad_p4 (n : nat) : positive :=
  match n with
  | O => xH
  | Datatypes.S m => (4 * u5c_quad_p4 m)%positive
  end.

Lemma u5c_quad_p4_Z : forall n : nat,
  Z.pos (u5c_quad_p4 n) = Z.of_nat ((4 ^ n)%nat).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [u5c_quad_p4]. rewrite Pos2Z.inj_mul, IH.
    rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    reflexivity.
Qed.

(* ============================================================ *)
(* S2. Pointwise facts of the sequence                          *)
(* ============================================================ *)

Lemma u5c_quad_qinv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (Qinv x).
Proof.
  intros x Hx.
  pose proof (ir2_inv_pos x Hx) as Hge.
  destruct (Qeq_dec (Qinv x) 0%Q) as [Hz | Hne].
  - exfalso. assert (E : (0%Q == 1%Q)%Q).
    { rewrite <- (Qmult_inv_r x
        ltac:(intro Hc; exact (Qlt_not_eq 0%Q x Hx (Qeq_sym x 0%Q Hc)))).
      rewrite Hz. apply Qeq_sym. apply Qmult_0_r. }
    apply (Qlt_not_eq 0%Q 1%Q); [unfold Qlt; cbn [Qnum Qden]; lia | exact E].
  - destruct (Qlt_le_dec 0%Q (Qinv x)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (Qinv x) 0%Q Hle Hge).
Qed.

Lemma u5c_quad_x_pos : forall (d : positive) (n : nat), Qlt 0 (u5c_quad_x d n).
Proof.
  intros d n. induction n as [|n IH].
  - unfold Qlt. cbn [u5c_quad_x Qnum Qden]. pose proof (Pos2Z.is_pos d). lia.
  - cbn [u5c_quad_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | ].
      unfold Qdiv. apply (Qmult_lt_0_compat ((Z.pos d # 1)%Q)).
      * unfold Qlt. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos d). lia.
      * apply u5c_quad_qinv_pos. exact IH.
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma u5c_quad_delta_succ_mul : forall (d : positive) (n : nat),
  (u5c_quad_delta d (Datatypes.S n) * (4 * (u5c_quad_x d n * u5c_quad_x d n))
    == u5c_quad_delta d n * u5c_quad_delta d n)%Q.
Proof.
  intros d n. unfold u5c_quad_delta. cbn [u5c_quad_x]. field.
  intro Heq. apply (Qlt_not_eq 0%Q (u5c_quad_x d n) (u5c_quad_x_pos d n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma u5c_quad_delta_ge0 : forall (d : positive) (n : nat),
  Qle 0 (u5c_quad_delta d n).
Proof.
  intros d n. induction n as [|n IH].
  - unfold u5c_quad_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [u5c_quad_x Qnum Qden Qmult Qminus Qplus Qopp].
    pose proof (Pos2Z.is_pos d). nia.
  - assert (HM : Qlt 0%Q (4 * (u5c_quad_x d n * u5c_quad_x d n))).
    { apply (Qmult_lt_0_compat (4#1) (u5c_quad_x d n * u5c_quad_x d n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (u5c_quad_x d n) (u5c_quad_x d n));
          exact (u5c_quad_x_pos d n). }
    pose proof (u5c_quad_delta_succ_mul d n) as Hmul.
    assert (Hsq : Qle 0 (u5c_quad_delta d n * u5c_quad_delta d n)).
    { destruct (u5c_quad_delta d n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma u5c_quad_delta_step : forall (d : positive) (n : nat),
  Qle (u5c_quad_delta d (Datatypes.S n)) (((1#4) * u5c_quad_delta d n)%Q).
Proof.
  intros d n.
  pose proof (u5c_quad_x_pos d n) as Hxp.
  assert (Hx2 : Qlt 0%Q (u5c_quad_x d n * u5c_quad_x d n)%Q).
  { apply (Qmult_lt_0_compat _ _); exact Hxp. }
  pose proof (u5c_quad_delta_ge0 d n) as Hd0.
  assert (Hdu : Qle (u5c_quad_delta d n) (u5c_quad_x d n * u5c_quad_x d n)%Q).
  { apply (Qle_trans _ (u5c_quad_delta d n + (Z.pos d # 1)%Q)%Q).
    - apply (Qle_trans (u5c_quad_delta d n) (u5c_quad_delta d n + 0%Q)%Q
               (u5c_quad_delta d n + (Z.pos d # 1)%Q)%Q).
      + apply qeq_le. symmetry. apply Qplus_0_r.
      + apply (Qplus_le_compat (u5c_quad_delta d n) (u5c_quad_delta d n)
                 0%Q ((Z.pos d # 1)%Q)).
        * apply Qle_refl.
        * unfold Qle. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos d). lia.
    - apply qeq_le. unfold u5c_quad_delta.
      apply (lic_qlt_minus_add_r _ ((Z.pos d # 1)%Q)). }
  pose proof (u5c_quad_delta_succ_mul d n) as Hmul.
  assert (HB : Qle ((u5c_quad_delta d (Datatypes.S n)
                      * (4 * (u5c_quad_x d n * u5c_quad_x d n)))%Q)
                    ((u5c_quad_x d n * u5c_quad_x d n) * u5c_quad_delta d n)%Q).
  { rewrite Hmul.
    apply (Qmult_le_compat_r _ _ (u5c_quad_delta d n)); [exact Hdu | exact Hd0]. }
  assert (Hinv0 : Qle 0%Q (Qinv (u5c_quad_x d n * u5c_quad_x d n))).
  { apply ir2_inv_pos. exact Hx2. }
  assert (HC : Qle ((u5c_quad_delta d (Datatypes.S n)
                      * (4 * (u5c_quad_x d n * u5c_quad_x d n)))
                     * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q
                    (((u5c_quad_x d n * u5c_quad_x d n) * u5c_quad_delta d n)
                     * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q).
  { apply (Qmult_le_compat_r _ _ (Qinv (u5c_quad_x d n * u5c_quad_x d n)));
      [exact HB | exact Hinv0]. }
  assert (Einv1 : ((u5c_quad_x d n * u5c_quad_x d n)
                    * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q == (1#1)%Q).
  { apply Qmult_inv_r.
    intro Hc. apply (Qlt_not_eq 0%Q (u5c_quad_x d n * u5c_quad_x d n)%Q Hx2).
    apply Qeq_sym. exact Hc. }
  assert (Einv4 : ((4 * (u5c_quad_x d n * u5c_quad_x d n))
                    * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q == (4#1)%Q).
  { rewrite <- (Qmult_assoc (4#1)%Q (u5c_quad_x d n * u5c_quad_x d n)
                  (Qinv (u5c_quad_x d n * u5c_quad_x d n))).
    rewrite (Qmult_inv_r (u5c_quad_x d n * u5c_quad_x d n)).
    - rewrite Qmult_1_r. apply Qeq_refl.
    - intro Hc. apply (Qlt_not_eq 0%Q (u5c_quad_x d n * u5c_quad_x d n)%Q Hx2).
      apply Qeq_sym. exact Hc. }
  assert (EL : ((u5c_quad_delta d (Datatypes.S n)
                  * (4 * (u5c_quad_x d n * u5c_quad_x d n)))
                 * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q
                == (u5c_quad_delta d (Datatypes.S n) * (4#1))%Q).
  { rewrite <- (Qmult_assoc (u5c_quad_delta d (Datatypes.S n))
                  (4 * (u5c_quad_x d n * u5c_quad_x d n))
                  (Qinv (u5c_quad_x d n * u5c_quad_x d n))).
    rewrite Einv4. apply Qeq_refl. }
  assert (ER : (((u5c_quad_x d n * u5c_quad_x d n) * u5c_quad_delta d n)
                 * Qinv (u5c_quad_x d n * u5c_quad_x d n))%Q
                == (u5c_quad_delta d n)%Q).
  { rewrite <- (Qmult_assoc (u5c_quad_x d n * u5c_quad_x d n)
                  (u5c_quad_delta d n) (Qinv (u5c_quad_x d n * u5c_quad_x d n))).
    rewrite (Qmult_comm (u5c_quad_delta d n)
              (Qinv (u5c_quad_x d n * u5c_quad_x d n))).
    rewrite (Qmult_assoc (u5c_quad_x d n * u5c_quad_x d n)
               (Qinv (u5c_quad_x d n * u5c_quad_x d n)) (u5c_quad_delta d n)).
    rewrite Einv1. apply Qmult_1_l. }
  rewrite (Qmult_comm (1#4) (u5c_quad_delta d n)).
  replace (1#4)%Q with (Qinv (4#1)%Q) by reflexivity.
  apply (ir2_le_mul_inv (u5c_quad_delta d (Datatypes.S n))
          (u5c_quad_delta d n) (4#1)%Q).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - rewrite <- EL. rewrite <- ER. exact HC.
Qed.

Lemma u5c_quad_delta_pos : forall (d : positive), u5c_quad_nonsq d ->
  forall n : nat, Qlt 0 (u5c_quad_delta d n).
Proof.
  intros d Hd n. pose proof (u5c_quad_delta_ge0 d n) as Hge.
  destruct (Qeq_dec (u5c_quad_delta d n) 0%Q) as [Hz | Hne].
  - exfalso. apply (u5c_quad_no_sqrtQ d Hd (u5c_quad_x d n)).
    unfold u5c_quad_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r
                  (u5c_quad_x d n * u5c_quad_x d n) ((Z.pos d # 1)%Q)).
    rewrite Hz. apply Qplus_0_l.
  - destruct (Qlt_le_dec 0%Q (u5c_quad_delta d n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (u5c_quad_delta d n) 0%Q Hle Hge).
Qed.

Lemma u5c_quad_sq_ge_d : forall (d : positive) (n : nat),
  Qle ((Z.pos d # 1)%Q) (u5c_quad_x d n * u5c_quad_x d n)%Q.
Proof.
  intros d n. pose proof (u5c_quad_delta_ge0 d n) as H.
  assert (Hr : ((u5c_quad_x d n * u5c_quad_x d n - (Z.pos d # 1)%Q)
                 + (Z.pos d # 1)%Q == u5c_quad_x d n * u5c_quad_x d n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans ((Z.pos d # 1)%Q) (0%Q + (Z.pos d # 1)%Q)%Q
          ((u5c_quad_x d n * u5c_quad_x d n - (Z.pos d # 1)%Q) + (Z.pos d # 1)%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma u5c_quad_x_lb1 : forall (d : positive) (n : nat), (1#1) <= u5c_quad_x d n.
Proof.
  intros d n. pose proof (u5c_quad_x_pos d n) as Hp.
  pose proof (u5c_quad_sq_ge_d d n) as Hsq.
  destruct (Qlt_le_dec (u5c_quad_x d n) (1#1)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((u5c_quad_x d n) * (u5c_quad_x d n))
                     ((1#1) * (u5c_quad_x d n))).
    { apply (Qmult_lt_compat_r (u5c_quad_x d n) (1#1) (u5c_quad_x d n));
        [exact Hp | exact Hlt]. }
    assert (E1 : ((1#1) * (u5c_quad_x d n))%Q == (u5c_quad_x d n)%Q)
      by apply Qmult_1_l.
    assert (H2 : Qlt ((1#1) * (u5c_quad_x d n)) (1#1)%Q).
    { rewrite E1. exact Hlt. }
    rewrite E1 in H1. rewrite E1 in H2.
    apply (Qlt_not_le (u5c_quad_x d n * u5c_quad_x d n) ((Z.pos d # 1)%Q)).
    + apply (Qlt_le_trans _ (1#1)%Q).
      * exact (Qlt_trans _ _ _ H1 H2).
      * unfold Qle. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos d). lia.
    + exact Hsq.
  - exact Hle.
Qed.

Lemma u5c_quad_x_lb75 : forall (d : positive), u5c_quad_nonsq d ->
  forall n : nat, (7#5) <= u5c_quad_x d n.
Proof.
  intros d Hd n.
  pose proof (u5c_quad_d_ge2 d Hd) as Hd2.
  pose proof (u5c_quad_x_pos d n) as Hp.
  pose proof (u5c_quad_sq_ge_d d n) as Hsq.
  destruct (Qlt_le_dec (u5c_quad_x d n) (7#5)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((u5c_quad_x d n) * (u5c_quad_x d n))
                     ((7#5) * (u5c_quad_x d n))).
    { apply (Qmult_lt_compat_r (u5c_quad_x d n) (7#5) (u5c_quad_x d n));
        [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((7#5) * (u5c_quad_x d n)) ((7#5) * (7#5))).
    { rewrite (Qmult_comm (7#5) (u5c_quad_x d n)).
      apply (Qmult_lt_compat_r (u5c_quad_x d n) (7#5) (7#5)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt ((7#5)*(7#5)) ((Z.pos d # 1)%Q)).
    { unfold Qlt, Qmult. cbn [Qnum Qden Qmult].
      pose proof (Pos2Z.is_pos d). lia. }
    apply (Qlt_not_le (u5c_quad_x d n * u5c_quad_x d n) ((Z.pos d # 1)%Q)).
    + exact (Qlt_trans _ _ _ (Qlt_trans _ _ _ H1 H2) H3).
    + exact Hsq.
  - exact Hle.
Qed.

Lemma u5c_quad_x1 : forall d : positive,
  u5c_quad_x d 1 == ((Z.pos d + 1) # 2)%Q.
Proof.
  intro d. cbn [u5c_quad_x].
  assert (E1 : ((Z.pos d # 1)%Q / (Z.pos d # 1)%Q) == 1%Q).
  { unfold Qdiv. apply Qmult_inv_r.
    intro Hc. apply (Qlt_not_eq 0%Q (Z.pos d # 1)%Q).
    - unfold Qlt. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos d). lia.
    - apply Qeq_sym. exact Hc. }
  assert (E2 : (((Z.pos d # 1)%Q + 1%Q) * (1 # 2)%Q == ((Z.pos d + 1) # 2)%Q)%Q).
  { unfold Qeq, Qplus, Qmult. cbn [Qnum Qden Qplus Qmult].
    rewrite ?Pos2Z.inj_mul. ring. }
  rewrite E1. rewrite E2. apply Qeq_refl.
Qed.

Lemma u5c_quad_mono : forall (d : positive) (n : nat),
  Qle (u5c_quad_x d (Datatypes.S n)) (u5c_quad_x d n).
Proof.
  intros d n. cbn [u5c_quad_x].
  pose proof (u5c_quad_sq_ge_d d n) as H2.
  pose proof (u5c_quad_x_pos d n) as Hxp.
  destruct (u5c_quad_x d n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H2c : (Z.pos d * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H2 as H2'. rewrite ?Ex in H2'.
    unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle ((Z.pos d # 1)%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H2 | exact Hivp].
    - apply qeq_le.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               ((Z.pos d # 1)%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2)) == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma u5c_quad_mono_le : forall (d : positive) (n k : nat),
  (1 <= n)%nat -> (n <= k)%nat -> u5c_quad_x d k <= u5c_quad_x d n.
Proof.
  intros d n k Hn1 Hnk.
  assert (Hgen : forall m : nat, u5c_quad_x d (n + m) <= u5c_quad_x d n).
  { induction m as [|m IHm].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S m)%nat with (Datatypes.S (n + m))%nat by lia.
      apply (Qle_trans _ (u5c_quad_x d (n + m))).
      + apply u5c_quad_mono.
      + exact IHm. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

Lemma u5c_quad_x_ub : forall (d : positive) (n : nat), (1 <= n)%nat ->
  u5c_quad_x d n <= u5c_quad_x d 1.
Proof.
  intros d n Hn. destruct n as [|n'].
  - lia.
  - apply (u5c_quad_mono_le d 1 (Datatypes.S n')); lia.
Qed.

Lemma u5c_quad_e_step : forall (d : positive) (n : nat),
  Qle (u5c_quad_e d (Datatypes.S n)) (((1#4) * u5c_quad_e d n)%Q).
Proof.
  intros d n. unfold u5c_quad_e.
  apply (Qle_trans _ (((1#2) * ((1#4) * u5c_quad_delta d n))%Q)).
  - apply (ir2_mult_le_compat_l (u5c_quad_delta d (Datatypes.S n))
              ((1#4) * u5c_quad_delta d n)%Q (1#2)%Q).
    + apply u5c_quad_delta_step.
    + unfold Qle. cbn [Qnum Qden]. lia.
  - apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* S3. Uniform decay: e(n) <= d^2 / 4^n and the window bound    *)
(* ============================================================ *)

Lemma u5c_quad_pow4_ge_self : forall j : nat, (j <= 4 ^ j)%nat.
Proof.
  assert (H4 : forall j : nat, (4 * j + 4 <= 4 ^ (j + 1))%nat).
  { induction j as [|j IH].
    - cbn. lia.
    - replace (Datatypes.S j + 1)%nat with (Datatypes.S (j + 1))%nat by lia.
      rewrite (Nat.pow_succ_r' 4%nat (j + 1)).
      lia. }
  induction j as [|j IH].
  - cbn. lia.
  - pose proof (H4 j) as Hx.
    replace (j + 1)%nat with (Datatypes.S j)%nat in Hx by lia.
    rewrite (Nat.pow_succ_r' 4%nat j) in Hx.
    rewrite (Nat.pow_succ_r' 4%nat j).
    lia.
Qed.

Lemma u5c_quad_sq_le_pow4 : forall j : nat, (j * j <= 4 ^ (j + j))%nat.
Proof.
  intro j. rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono; apply u5c_quad_pow4_ge_self.
Qed.

Lemma u5c_quad_e_pow_le : forall (d : positive) (n : nat),
  Qle (u5c_quad_e d n) ((Z.pos d * Z.pos d) # (u5c_quad_p4 n))%Q.
Proof.
  intros d n. induction n as [|n IH].
  - unfold u5c_quad_e, u5c_quad_delta. cbn [u5c_quad_x u5c_quad_p4].
    pose proof (Pos2Z.is_pos d) as Hd0.
    unfold Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [Qnum Qden Qmult Qminus Qplus Qopp].
    lia.
  - apply (Qle_trans _ (((1#4) * u5c_quad_e d n)%Q)).
    + apply u5c_quad_e_step.
    + apply (Qle_trans _ (((1#4) * ((Z.pos d * Z.pos d) # (u5c_quad_p4 n)))%Q)).
      * apply (ir2_mult_le_compat_l (u5c_quad_e d n)
                  ((Z.pos d * Z.pos d) # (u5c_quad_p4 n)) (1#4)).
        -- exact IH.
        -- unfold Qle. cbn [Qnum Qden]; lia.
      * assert (Hc : (((1#4) * ((Z.pos d * Z.pos d) # (u5c_quad_p4 n)))%Q
                       == ((Z.pos d * Z.pos d) # (u5c_quad_p4 (Datatypes.S n)))%Q)%Q).
        { unfold Qeq, Qmult. cbn [Qnum Qden Qmult u5c_quad_p4]. ring. }
        apply qeq_le. exact Hc.
Qed.

Lemma u5c_quad_e_bnd : forall (d b : positive) (n : nat),
  (2 * (Z.to_nat (Z.pos d)) + 2 * (Z.to_nat (Z.pos b))
    + (Z.to_nat (Z.pos (u5c_quad_K d))) <= n)%nat ->
  QleT' (u5c_quad_e d n) ((1 # (u5c_quad_K d * (b * b)))%Q).
Proof.
  intros d b n Hn. apply Qle_to_QleT'.
  apply (Qle_trans (u5c_quad_e d n)
          ((Z.pos d * Z.pos d) # (u5c_quad_p4 n))%Q
          ((1 # (u5c_quad_K d * (b * b)))%Q)).
  - apply u5c_quad_e_pow_le.
  - unfold Qle, Qmult. cbn [Qnum Qden Qmult].
    rewrite ?Pos2Z.inj_mul. rewrite u5c_quad_p4_Z.
    assert (Hnat : (Z.to_nat (Z.pos d) * Z.to_nat (Z.pos d)
                     * Z.to_nat (Z.pos (u5c_quad_K d))
                     * (Z.to_nat (Z.pos b) * Z.to_nat (Z.pos b))
                     <= (4 ^ n)%nat)%nat).
    { pose proof (u5c_quad_sq_le_pow4 (Z.to_nat (Z.pos d))) as Hd2.
      pose proof (u5c_quad_sq_le_pow4 (Z.to_nat (Z.pos b))) as Hb2.
      pose proof (u5c_quad_pow4_ge_self (Z.to_nat (Z.pos (u5c_quad_K d)))) as HK.
      assert (Hm1 : (Z.to_nat (Z.pos d) * Z.to_nat (Z.pos d)
                      * Z.to_nat (Z.pos (u5c_quad_K d))
                      <= 4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d))
                        * 4 ^ (Z.to_nat (Z.pos (u5c_quad_K d))))%nat)
        by (apply Nat.mul_le_mono; [exact Hd2 | exact HK]).
      assert (Hm2 : (Z.to_nat (Z.pos d) * Z.to_nat (Z.pos d)
                      * Z.to_nat (Z.pos (u5c_quad_K d))
                      * (Z.to_nat (Z.pos b) * Z.to_nat (Z.pos b))
                      <= (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d))
                           * 4 ^ (Z.to_nat (Z.pos (u5c_quad_K d))))
                        * (4 ^ (Z.to_nat (Z.pos b) + Z.to_nat (Z.pos b))))%nat)
        by (apply Nat.mul_le_mono; [exact Hm1 | exact Hb2]).
      assert (Hfold : (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d))
                        * 4 ^ (Z.to_nat (Z.pos (u5c_quad_K d)))
                        * 4 ^ (Z.to_nat (Z.pos b) + Z.to_nat (Z.pos b))
                        <= 4 ^ n)%nat).
      { rewrite <- !Nat.pow_add_r.
        apply Nat.pow_le_mono_r; lia. }
      apply (Nat.le_trans _ _ _ Hm2 Hfold). }
    apply (Nat2Z.inj_le _ _) in Hnat.
    rewrite !Nat2Z.inj_mul in Hnat.
    pose proof (Z2Nat.id (Z.pos d) (ltac:(pose proof (Pos2Z.is_pos d); lia))) as Ezd.
    pose proof (Z2Nat.id (Z.pos (u5c_quad_K d))
                 (ltac:(pose proof (Pos2Z.is_pos (u5c_quad_K d)); lia))) as EzK.
    pose proof (Z2Nat.id (Z.pos b) (ltac:(pose proof (Pos2Z.is_pos b); lia))) as Ezb.
    rewrite Ezd, EzK, Ezb in Hnat.
    pose proof (u5c_quad_K_eq d) as HK.
    lia.
Qed.

(* ============================================================ *)
(* S4. Tail bound and vanish (lic framework instances)          *)
(* ============================================================ *)

Definition u5c_quad_tail (d : positive) (Hd : u5c_quad_nonsq d) :
  lic_tail_bounded (u5c_quad_x d) (u5c_quad_e d).
Proof.
  intros n k Hn1 Hnk.
  pose proof (u5c_quad_mono_le d n k Hn1 Hnk) as Hmono.
  pose proof (u5c_quad_delta_ge0 d n) as Hd0n.
  pose proof (u5c_quad_delta_pos d Hd n) as Hdpn.
  pose proof (u5c_quad_x_lb75 d Hd n) as Hlbn.
  pose proof (u5c_quad_x_lb75 d Hd k) as Hlbk.
  assert (Habs : Qabs ((u5c_quad_x d k - u5c_quad_x d n)%Q)
                  == (u5c_quad_x d n - u5c_quad_x d k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (u5c_quad_x d n + u5c_quad_x d k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (7#5) (u5c_quad_x d n));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hlbn].
    - apply (Qlt_le_trans 0%Q (7#5) (u5c_quad_x d k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hlbk]. }
  assert (Hsumne : ~ ((u5c_quad_x d n + u5c_quad_x d k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u5c_quad_x d n + u5c_quad_x d k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u5c_quad_x d n - u5c_quad_x d k)
                      == (u5c_quad_delta d n - u5c_quad_delta d k)
                           * Qinv (u5c_quad_x d n + u5c_quad_x d k))%Q).
  { pose proof (bno_mul_div_self (u5c_quad_x d n + u5c_quad_x d k) Hsumne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u5c_quad_x d n - u5c_quad_x d k)
                      * (u5c_quad_x d n + u5c_quad_x d k))
                     * Qinv (u5c_quad_x d n + u5c_quad_x d k))
                    == (u5c_quad_x d n - u5c_quad_x d k))%Q).
    { rewrite <- (Qmult_assoc (u5c_quad_x d n - u5c_quad_x d k)
                    (u5c_quad_x d n + u5c_quad_x d k)
                    (Qinv (u5c_quad_x d n + u5c_quad_x d k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((u5c_quad_x d n * u5c_quad_x d n
                     - u5c_quad_x d k * u5c_quad_x d k)
                    == (u5c_quad_delta d n - u5c_quad_delta d k))%Q)
      by (unfold u5c_quad_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  unfold u5c_quad_e.
  assert (Hsumb : Qle ((14#5)) (u5c_quad_x d n + u5c_quad_x d k)).
  { apply (Qle_trans _ ((7#5) + (7#5))%Q).
    - apply qeq_le. reflexivity.
    - apply (Qplus_le_compat (7#5) (u5c_quad_x d n) (7#5) (u5c_quad_x d k));
        [exact Hlbn | exact Hlbk]. }
  assert (Hinvp : Qle 0%Q (Qinv (u5c_quad_x d n + u5c_quad_x d k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((u5c_quad_delta d n - u5c_quad_delta d k)
                          * Qinv (u5c_quad_x d n + u5c_quad_x d k))
                       (u5c_quad_delta d n * Qinv (u5c_quad_x d n + u5c_quad_x d k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (u5c_quad_delta d n) as [dn dd] eqn:Edn.
      destruct (u5c_quad_delta d k) as [ek ed] eqn:Edk.
      pose proof (u5c_quad_delta_ge0 d k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (u5c_quad_delta d n * Qinv (u5c_quad_x d n + u5c_quad_x d k))
                       (u5c_quad_delta d n * Qinv ((14#5)))).
  { rewrite (Qmult_comm (u5c_quad_delta d n)
              (Qinv (u5c_quad_x d n + u5c_quad_x d k))).
    rewrite (Qmult_comm (u5c_quad_delta d n) (Qinv ((14#5)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (14#5) (u5c_quad_x d n + u5c_quad_x d k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (u5c_quad_delta d n * Qinv ((14#5)))
                       ((1#2) * u5c_quad_delta d n)).
  { destruct (u5c_quad_delta d n) as [dn dd] eqn:Edn.
    pose proof Hdpn as Hdp. unfold Qlt in Hdp.
    cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((u5c_quad_delta d n - u5c_quad_delta d k)
                        * Qinv (u5c_quad_x d n + u5c_quad_x d k))
          (u5c_quad_delta d n * Qinv (u5c_quad_x d n + u5c_quad_x d k))
          ((1#2) * u5c_quad_delta d n)%Q).
  - exact Hstep1.
  - apply (Qle_lt_trans (u5c_quad_delta d n * Qinv (u5c_quad_x d n + u5c_quad_x d k))
            (u5c_quad_delta d n * Qinv ((14#5))) ((1#2) * u5c_quad_delta d n)%Q).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition u5c_quad_vanish (d : positive) (Hd : u5c_quad_nonsq d) :
  lic_vanish (u5c_quad_e d).
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd)%Q Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (1 <= pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (2 * (Z.to_nat (Z.pos d)) + (Z.to_nat (Z.pos pd)) + 1)%nat.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans (u5c_quad_e d (Datatypes.S n'))
            ((Z.pos d * Z.pos d) # (u5c_quad_p4 (Datatypes.S n')))%Q
            ((pn # pd)%Q)).
    + apply u5c_quad_e_pow_le.
    + apply (Qle_lt_trans ((Z.pos d * Z.pos d) # (u5c_quad_p4 (Datatypes.S n')))%Q
              (1 # (2 * pd))%Q ((pn # pd)%Q)).
      * unfold Qle, Qmult. cbn [Qnum Qden Qmult].
        rewrite u5c_quad_p4_Z. rewrite ?Pos2Z.inj_mul.
        assert (Hnat : (2 * (Z.to_nat (Z.pos d) * Z.to_nat (Z.pos d))
                          * Z.to_nat (Z.pos pd)
                          <= (4 ^ (Datatypes.S n'))%nat)%nat).
        { pose proof (u5c_quad_sq_le_pow4 (Z.to_nat (Z.pos d))) as H1.
          pose proof (u5c_quad_pow4_ge_self (Z.to_nat (Z.pos pd))) as H2.
          assert (H3 : ((2 * (Z.to_nat (Z.pos d) * Z.to_nat (Z.pos d)))
                          * Z.to_nat (Z.pos pd)
                          <= (2 * (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d))))
                             * (4 ^ (Z.to_nat (Z.pos pd))))%nat).
          { apply Nat.mul_le_mono.
            - apply Nat.mul_le_mono; [lia | exact H1].
            - exact H2. }
          assert (H4 : (2 * (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d)))
                         * (4 ^ (Z.to_nat (Z.pos pd)))
                         <= 4 ^ (Datatypes.S n'))%nat).
          { rewrite (Nat.pow_succ_r' 4%nat n').
            apply Nat.le_trans with
              (4 * (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d)))
                 * (4 ^ (Z.to_nat (Z.pos pd))))%nat.
            - lia.
            - assert (HE : (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d)
                             + Z.to_nat (Z.pos pd) <= n')%nat) by lia.
              assert (H5 : (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d))
                             * 4 ^ (Z.to_nat (Z.pos pd)) <= 4 ^ n')%nat).
              { rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia. }
              rewrite <- (Nat.mul_assoc 4%nat
                (4 ^ (Z.to_nat (Z.pos d) + Z.to_nat (Z.pos d)))
                (4 ^ (Z.to_nat (Z.pos pd)))).
              apply Nat.mul_le_mono_l. exact H5. }
          apply (Nat.le_trans _ _ _ H3 H4). }
        apply (Nat2Z.inj_le _ _) in Hnat.
        rewrite !Nat2Z.inj_mul in Hnat.
        pose proof (Z2Nat.id (Z.pos d) (ltac:(pose proof (Pos2Z.is_pos d); lia))) as Ezd.
        pose proof (Z2Nat.id (Z.pos pd) (ltac:(pose proof (Pos2Z.is_pos pd); lia))) as Ezp.
        rewrite Ezd, Ezp in Hnat.
        pose proof (Pos2Z.is_pos d) as Hd0. lia.
      * unfold Qlt, Qmult. cbn [Qnum Qden Qmult]. nia.
Qed.

(* ============================================================ *)
(* S5. Margin machinery: conversions, gap-lower, four branches  *)
(* ============================================================ *)

Lemma u5c_quad_qle_add_cancel_r : forall x y z : Q,
  QleT' (x + z)%Q (y + z)%Q -> QleT' x y.
Proof.
  intros [xn xd] [yn yd] [zn zd] H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  unfold Qle, Qplus in Hle |- *.
  cbn [Qnum Qden Qplus] in Hle |- *. nia.
Qed.

(* Generalized gap-lower (generalizes ir2_gap_lower from 2 to any d):
   for v >= 0 with v^2 < d and u >= v an upper-bounded approximant with
   d <= u^2, the distance u - v dominates (d - v^2)/(d+1). *)
Lemma u5c_quad_gap_lower : forall (d : positive) (u v : Q),
  Qle 0 v -> Qle v u -> Qle u ((Z.pos d + 1) # 2)%Q ->
  Qle ((Z.pos d # 1)%Q) (u * u) -> Qlt (v * v) ((Z.pos d # 1)%Q) ->
  Qle ((((Z.pos d # 1)%Q - v * v) * (1 # Pos.succ d))%Q) (u - v).
Proof.
  intros d u v Hv0 Hvu Hub H2 Hsq.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); assumption).
  assert (Huv0 : Qlt 0%Q (u + v)).
  { destruct (Qlt_le_dec 0%Q (u + v)) as [Hlt | Hle].
    - exact Hlt.
    - exfalso.
      assert (Huu : Qle u (u + v)).
      { apply (Qle_trans u (u + 0%Q) (u + v)).
        - apply qeq_le. symmetry. apply Qplus_0_r.
        - apply (Qplus_le_compat u u 0%Q v); [apply Qle_refl | exact Hv0]. }
      assert (Hu : u == 0%Q).
      { apply (Qle_antisym u 0%Q).
        - apply (Qle_trans u (u + v) 0%Q); [exact Huu | exact Hle].
        - exact Hu0. }
      pose proof H2 as H2'. rewrite Hu in H2'.
      unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'.
      pose proof (Pos2Z.is_pos d). lia. }
  assert (Hne : ~ ((u + v)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u + v) Huv0);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u - v) == (u*u - v*v) * Qinv (u + v))%Q).
  { pose proof (bno_mul_div_self (u + v) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u - v) * (u + v)) * Qinv (u + v)) == (u - v))%Q).
    { rewrite <- (Qmult_assoc (u - v) (u + v) (Qinv (u + v))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hw0 : Qle 0%Q ((Z.pos d # 1)%Q - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) ((Z.pos d # 1)%Q) Hsq)).
  assert (Hub1 : Qle (u + v) ((Z.pos d + 1) # 1)%Q).
  { apply (Qle_trans _ (((Z.pos d + 1) # 2) + ((Z.pos d + 1) # 2))%Q).
    - apply (Qplus_le_compat u ((Z.pos d + 1) # 2) v ((Z.pos d + 1) # 2)).
      + exact Hub.
      + apply (Qle_trans v u ((Z.pos d + 1) # 2)); assumption.
    - apply qeq_le. unfold Qeq, Qplus, Qmult.
      cbn [Qnum Qden Qplus Qmult]. rewrite ?Pos2Z.inj_mul. ring. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  assert (HE1 : ((1 # Pos.succ d)%Q == Qinv ((Z.pos d + 1) # 1))%Q).
  { assert (HS : Z.pos (Pos.succ d) = (Z.pos d + 1)%Z)
      by (rewrite Pos2Z.inj_succ; reflexivity).
    rewrite <- HS.
    assert (Hq1 : QeqT (Qinv ((Z.pos (Pos.succ d)) # 1)) (1 # Pos.succ d))
      by apply dmew_Qinv_1p.
    pose proof (qeqT_imp_qeq _ _ Hq1) as Hq1'.
    exact (Qeq_sym _ _ Hq1'). }
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ (((Z.pos d # 1)%Q - v*v) * Qinv (u + v))%Q).
    + rewrite HE1. apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) ((Z.pos d + 1) # 1));
          [exact Huv0 | exact Hub1].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H2.
      * exact Hivp.
  - apply Qle_refl.
Qed.

(* Four-branch margin core: with c = 1/(K_d b^2) and the window e-bound,
   every rational q = a/b sits at distance >= 2c + e(n0) from x_d(n0). *)
Lemma u5c_quad_margin_closed : forall (d : positive) (Hd : u5c_quad_nonsq d)
  (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  QleT' (u5c_quad_e d n0) ((1 # (u5c_quad_K d * (b * b)))%Q) ->
  QleT' (((1 # (u5c_quad_K d * (b * b)))%Q
           + (1 # (u5c_quad_K d * (b * b)))%Q + u5c_quad_e d n0)%Q)
        (Qabs (((a # b)%Q - u5c_quad_x d n0)%Q)).
Proof.
  intros d Hd a b n0 Hn01 Heb.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ Heb) as Heb'.
  pose proof (u5c_quad_K_eq d) as HK.
  pose proof (Pos2Z.is_pos b) as Hb0.
  pose proof (u5c_quad_x_lb1 d n0) as Hxlb.
  pose proof (u5c_quad_x_pos d n0) as Hxpos.
  pose proof (u5c_quad_sq_ge_d d n0) as Hx2.
  pose proof (u5c_quad_x_ub d n0 Hn01) as Hxub0.
  assert (Hxub : Qle (u5c_quad_x d n0) ((Z.pos d + 1) # 2)%Q).
  { apply (Qle_trans _ (u5c_quad_x d 1)).
    - exact Hxub0.
    - apply qeq_le. apply u5c_quad_x1. }
  assert (Hcce : Qle (((1 # (u5c_quad_K d * (b * b)))%Q
                        + (1 # (u5c_quad_K d * (b * b)))%Q)
                       + u5c_quad_e d n0)%Q
                      ((3 # (u5c_quad_K d * (b * b)))%Q)).
  { apply (Qle_trans _ (((1 # (u5c_quad_K d * (b * b)))%Q
                          + (1 # (u5c_quad_K d * (b * b)))%Q)
                         + (1 # (u5c_quad_K d * (b * b)))%Q)%Q).
    - apply Qplus_le_compat; [apply Qle_refl | exact Heb'].
    - apply qeq_le. unfold Qeq, Qplus, Qmult.
      cbn [Qnum Qden Qplus Qmult]. rewrite ?Pos2Z.inj_mul. ring. }
  destruct (Qlt_le_dec 0%Q (a # b)%Q) as [Hq0pos | Hq0neg].
  - destruct (Qlt_le_dec ((a # b)%Q * (a # b)%Q) ((Z.pos d # 1)%Q)) as [Hlt2 | Hge2].
    + (* Branch 2: 0 < q and q^2 < d *)
      assert (Hqx : Qle (a # b)%Q (u5c_quad_x d n0)).
      { destruct (Qlt_le_dec (u5c_quad_x d n0) (a # b)%Q) as [Hxq | Hle].
        - exfalso.
          apply (Qlt_not_le ((a # b)%Q * (a # b)%Q) ((Z.pos d # 1)%Q) Hlt2).
          apply (Qle_trans ((Z.pos d # 1)%Q)
                  (u5c_quad_x d n0 * u5c_quad_x d n0) ((a # b)%Q * (a # b)%Q)).
          + exact Hx2.
          + apply (ir2_sq_mono (a # b)%Q (u5c_quad_x d n0)).
            * apply Qlt_le_weak. exact Hxpos.
            * apply Qlt_le_weak. exact Hxq.
        - exact Hle. }
      rewrite (Qabs_Qminus (a # b)%Q (u5c_quad_x d n0)).
      rewrite (ir2_abs_sub (u5c_quad_x d n0) (a # b)%Q Hqx).
      apply (Qle_trans _ ((3 # (u5c_quad_K d * (b * b)))%Q)).
      * exact Hcce.
      * apply (Qle_trans _ (((1 # (b * b)) * (1 # Pos.succ d))%Q)).
        -- unfold Qle, Qmult. cbn [Qnum Qden Qmult].
           rewrite ?Pos2Z.inj_mul. nia.
        -- apply (Qle_trans _ ((((Z.pos d # 1)%Q
                                      - ((a # b)%Q * (a # b)%Q))
                                     * (1 # Pos.succ d))%Q)).
              ** apply (Qmult_le_compat_r _ _ (1 # Pos.succ d)%Q).
                 --- pose proof Hlt2 as Hh. unfold Qlt, Qmult in Hh.
                     cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh.
                     assert (Hgap : (1 <= Z.pos d * (Z.pos b * Z.pos b) - a * a)%Z)
                       by lia.
                     unfold Qle, Qminus, Qmult, Qplus, Qopp;
                       cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                       rewrite ?Pos2Z.inj_mul; nia.
                 --- unfold Qle. cbn [Qnum Qden]. lia.
              ** exact (u5c_quad_gap_lower d (u5c_quad_x d n0) (a # b)%Q
                          (Qlt_le_weak 0%Q (a # b)%Q Hq0pos) Hqx Hxub Hx2 Hlt2).
    + destruct (Qle_lt_or_eq ((Z.pos d # 1)%Q) ((a # b)%Q * (a # b)%Q) Hge2)
        as [Hlt2 | Heq].
      * destruct (Qlt_le_dec ((Z.pos d + 1) # 2)%Q (a # b)%Q) as [Hqgt | Hq32].
        -- (* Branch 4: q > (d+1)/2 *)
           assert (Hside : Qle (u5c_quad_x d n0) (a # b)%Q).
           { apply (Qle_trans (u5c_quad_x d n0) ((Z.pos d + 1) # 2) (a # b)%Q);
               [exact Hxub | apply Qlt_le_weak; exact Hqgt]. }
           rewrite (ir2_abs_sub (a # b)%Q (u5c_quad_x d n0) Hside).
           apply (Qle_trans _ ((1 # (2 * b))%Q)).
           { apply (Qle_trans _ ((3 # (u5c_quad_K d * (b * b)))%Q)).
             - exact Hcce.
             - unfold Qle, Qmult. cbn [Qnum Qden Qmult].
               rewrite ?Pos2Z.inj_mul. nia. }
           apply (Qle_trans _ (((a # b)%Q - ((Z.pos d + 1) # 2))%Q)).
           { assert (Hgap : (1 <= 2 * a - (Z.pos d + 1) * Z.pos b)%Z).
             { pose proof Hqgt as Hh. unfold Qlt, Qmult in Hh.
               cbn [Qnum Qden] in Hh. nia. }
             unfold Qle, Qminus, Qmult, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qplus Qopp Qmult];
               rewrite ?Pos2Z.inj_mul; nia. }
           apply (Qplus_le_compat (a # b)%Q (a # b)%Q
                    (- ((Z.pos d + 1) # 2))%Q (- u5c_quad_x d n0)%Q).
           { apply Qle_refl. }
           { apply (Qopp_le_compat (u5c_quad_x d n0) ((Z.pos d + 1) # 2)%Q Hxub). }
        -- (* Branch 3: (d+1)/2 >= q and q^2 > d *)
           assert (Hzpos : (Z.pos d * (Z.pos b * Z.pos b) < a * a)%Z).
           { pose proof Hlt2 as Hh. unfold Qlt, Qmult in Hh.
             cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh. nia. }
           assert (Hmu : Qle (1 # (b * b)) (((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q))%Q).
           { unfold Qle, Qminus, Qmult, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qmult Qplus Qopp];
               rewrite ?Pos2Z.inj_mul; nia. }
           assert (Ed : (u5c_quad_delta d n0 == (2#1) * u5c_quad_e d n0)%Q)
             by (unfold u5c_quad_e; ring).
           assert (Hdel : Qle (u5c_quad_delta d n0) ((2 # (u5c_quad_K d * (b * b)))%Q)).
           { rewrite Ed.
             apply (Qle_trans _ ((2#1) * ((1 # (u5c_quad_K d * (b * b)))%Q))).
             - apply (ir2_mult_le_compat_l (u5c_quad_e d n0)
                        ((1 # (u5c_quad_K d * (b * b)))%Q) (2#1));
                 [exact Heb' | unfold Qle; cbn [Qnum Qden]; lia].
             - apply qeq_le. unfold Qeq, Qmult;
                 cbn [Qnum Qden Qmult]; rewrite ?Pos2Z.inj_mul; ring. }
           assert (Hmud : Qle (((1 # (b * b))%Q - (2 # (u5c_quad_K d * (b * b)))%Q))
                              ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                 - u5c_quad_delta d n0)%Q)).
           { apply (Qplus_le_compat (1 # (b * b))
                      (((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q))%Q
                      (- (2 # (u5c_quad_K d * (b * b))))%Q
                      (- u5c_quad_delta d n0)%Q).
             - exact Hmu.
             - apply (Qopp_le_compat (u5c_quad_delta d n0)
                        ((2 # (u5c_quad_K d * (b * b)))%Q) Hdel). }
           assert (HDpos : Qle 0%Q ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                      - u5c_quad_delta d n0)%Q)).
           { apply (Qle_trans 0%Q
                  (((1 # (b * b))%Q - (2 # (u5c_quad_K d * (b * b)))%Q))%Q _).
             - unfold Qle, Qminus, Qmult, Qplus, Qopp;
                 cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; nia.
             - exact Hmud. }
           assert (Hqxp : Qlt 0%Q ((a # b)%Q + u5c_quad_x d n0)%Q).
           { apply (ir2_qpos_add (a # b)%Q (u5c_quad_x d n0));
               [exact Hq0pos | exact Hxpos]. }
           assert (Hqxn : ~ ((a # b)%Q + u5c_quad_x d n0 == 0%Q)).
           { intro Hc. apply (Qlt_not_eq 0%Q ((a # b)%Q + u5c_quad_x d n0) Hqxp).
             apply Qeq_sym. exact Hc. }
           assert (Hbridge : (((a # b)%Q - u5c_quad_x d n0) ==
              ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q) - u5c_quad_delta d n0)%Q
                * Qinv ((a # b)%Q + u5c_quad_x d n0)))%Q).
           { pose proof (bno_mul_div_self ((a # b)%Q + u5c_quad_x d n0) Hqxn) as Hbd.
             unfold Qdiv in Hbd. rewrite Qmult_1_l in Hbd.
             assert (Hpm : (((((a # b)%Q - u5c_quad_x d n0)
                               * ((a # b)%Q + u5c_quad_x d n0))
                              * Qinv ((a # b)%Q + u5c_quad_x d n0))
                             == ((a # b)%Q - u5c_quad_x d n0))%Q).
             { rewrite <- (Qmult_assoc ((a # b)%Q - u5c_quad_x d n0)
                            ((a # b)%Q + u5c_quad_x d n0)
                            (Qinv ((a # b)%Q + u5c_quad_x d n0))).
               rewrite Hbd. apply Qmult_1_r. }
             rewrite ir2_sq_diff in Hpm.
             assert (Hsh : (((a # b)%Q * (a # b)%Q - u5c_quad_x d n0 * u5c_quad_x d n0)
                             == ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                   - u5c_quad_delta d n0)))%Q)
               by (unfold u5c_quad_delta; ring).
             rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
           assert (Hqxb : Qle ((a # b)%Q + u5c_quad_x d n0) ((Z.pos d + 1) # 1)%Q).
           { apply (Qle_trans _ (((Z.pos d + 1) # 2) + ((Z.pos d + 1) # 2))%Q).
             - apply (Qplus_le_compat (a # b)%Q ((Z.pos d + 1) # 2)%Q
                        (u5c_quad_x d n0) ((Z.pos d + 1) # 2)%Q);
                 [exact Hq32 | exact Hxub].
             - apply qeq_le. unfold Qeq, Qplus, Qmult.
               cbn [Qnum Qden Qplus Qmult]. rewrite ?Pos2Z.inj_mul. ring. }
           assert (Hinv : Qle (Qinv ((Z.pos d + 1) # 1))
                              (Qinv ((a # b)%Q + u5c_quad_x d n0))).
           { apply (ir2_inv_le ((a # b)%Q + u5c_quad_x d n0) ((Z.pos d + 1) # 1));
               [exact Hqxp | exact Hqxb]. }
           assert (HS : Z.pos (Pos.succ d) = (Z.pos d + 1)%Z)
             by (rewrite Pos2Z.inj_succ; reflexivity).
           assert (Fc : (((1 # (b * b))%Q - (2 # (u5c_quad_K d * (b * b)))%Q)
                          == (((4 * Z.pos d + 6) # 1)%Q
                               * (1 # (u5c_quad_K d * (b * b)))%Q))%Q).
           { unfold Qeq, Qminus, Qmult, Qopp, Qplus.
             cbn [Qnum Qden Qminus Qmult Qopp Qplus].
             rewrite ?Pos2Z.inj_mul. rewrite HK. ring. }
           assert (Hd3 : Qle ((3 # (u5c_quad_K d * (b * b)))%Q)
                              ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                 - u5c_quad_delta d n0)%Q * (1 # Pos.succ d))%Q).
           { apply (Qle_trans _ ((((4 * Z.pos d + 6) # 1)%Q
                                    * (1 # (u5c_quad_K d * (b * b)))%Q)
                                   * (1 # Pos.succ d))%Q).
             - apply (Qle_trans _ ((((3 * Z.pos (Pos.succ d)) # 1)%Q
                                      * (1 # (u5c_quad_K d * (b * b)))%Q)
                                     * (1 # Pos.succ d))%Q).
               + assert (F1 : ((3 # (u5c_quad_K d * (b * b)))%Q
                                == (((3 * Z.pos (Pos.succ d)) # 1)%Q
                                     * (1 # (u5c_quad_K d * (b * b)))%Q
                                     * (1 # Pos.succ d))%Q)%Q).
                 { unfold Qeq, Qmult. cbn [Qnum Qden Qmult].
                   rewrite ?Pos2Z.inj_mul. ring. }
                 apply qeq_le. exact F1.
               + assert (HZ : (3 * Z.pos (Pos.succ d) <= 4 * Z.pos d + 6)%Z)
                    by lia.
                 apply (Qle_trans _ ((((4 * Z.pos d + 6) # 1)%Q
                                        * (1 # (u5c_quad_K d * (b * b)))%Q)
                                       * (1 # Pos.succ d))%Q).
                 * apply (Qmult_le_compat_r _ _ (1 # Pos.succ d)%Q).
                   -- apply (Qmult_le_compat_r _ _
                        (1 # (u5c_quad_K d * (b * b)))%Q).
                      ** rewrite HS in HZ. unfold Qle. cbn [Qnum Qden]. lia.
                      ** unfold Qle. cbn [Qnum Qden]. lia.
                   -- unfold Qle. cbn [Qnum Qden]. lia.
                 * apply Qle_refl.
             - apply (Qmult_le_compat_r _ _ (1 # Pos.succ d)%Q).
               + apply (Qle_trans _ (((1 # (b * b))%Q
                                        - (2 # (u5c_quad_K d * (b * b)))%Q))%Q).
                 * apply qeq_le. exact (Qeq_sym _ _ Fc).
                 * exact Hmud.
               + unfold Qle. cbn [Qnum Qden]. lia. }
           assert (HE3 : ((1 # Pos.succ d)%Q == Qinv ((Z.pos d + 1) # 1))%Q).
           { rewrite <- HS.
             assert (Hq1 : QeqT (Qinv ((Z.pos (Pos.succ d)) # 1)) (1 # Pos.succ d))
               by apply dmew_Qinv_1p.
             pose proof (qeqT_imp_qeq _ _ Hq1) as Hq1'.
             exact (Qeq_sym _ _ Hq1'). }
           assert (Hbige : Qle ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                   - u5c_quad_delta d n0)%Q * (1 # Pos.succ d))%Q
                                ((a # b)%Q - u5c_quad_x d n0)%Q).
           { rewrite Hbridge. rewrite HE3.
             apply (ir2_mult_le_compat_l (Qinv ((Z.pos d + 1) # 1))
                      (Qinv ((a # b)%Q + u5c_quad_x d n0))
                      ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                         - u5c_quad_delta d n0)%Q)).
             - exact Hinv.
             - exact HDpos. }
           assert (He0 : Qle 0%Q (u5c_quad_e d n0)).
           { unfold u5c_quad_e.
             apply (Qle_trans _ (((1#2) * 0%Q)%Q)).
             - apply qeq_le. reflexivity.
             - apply (ir2_mult_le_compat_l 0%Q (u5c_quad_delta d n0) (1#2));
                 [exact (u5c_quad_delta_ge0 d n0) | unfold Qle; cbn [Qnum Qden]; lia]. }
           assert (Hsum0 : Qle 0%Q (((1 # (u5c_quad_K d * (b * b)))%Q
                                      + (1 # (u5c_quad_K d * (b * b)))%Q
                                      + u5c_quad_e d n0)%Q)).
           { apply (Qle_trans _ (0%Q + 0%Q)%Q).
             - apply qeq_le. reflexivity.
             - apply (Qplus_le_compat 0%Q
                        (((1 # (u5c_quad_K d * (b * b)))%Q
                           + (1 # (u5c_quad_K d * (b * b)))%Q))%Q
                        0%Q (u5c_quad_e d n0)).
               + apply (Qle_trans 0%Q (0%Q + 0%Q)%Q _).
                 * apply qeq_le. reflexivity.
                 * apply (Qplus_le_compat 0%Q ((1 # (u5c_quad_K d * (b * b)))%Q)
                            0%Q ((1 # (u5c_quad_K d * (b * b)))%Q));
                     [unfold Qle; cbn [Qnum Qden]; lia
                     | unfold Qle; cbn [Qnum Qden]; lia].
               + exact He0. }
           assert (Hge0 : Qle 0%Q ((a # b)%Q - u5c_quad_x d n0)%Q).
           { apply (Qle_trans 0%Q
                  (((1 # (u5c_quad_K d * (b * b)))%Q
                     + (1 # (u5c_quad_K d * (b * b)))%Q
                     + u5c_quad_e d n0)%Q) ((a # b)%Q - u5c_quad_x d n0)%Q).
             - exact Hsum0.
             - apply (Qle_trans _ ((3 # (u5c_quad_K d * (b * b)))%Q)).
               + exact Hcce.
               + apply (Qle_trans _ ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                                        - u5c_quad_delta d n0)%Q * (1 # Pos.succ d))%Q).
                 * exact Hd3.
                 * exact Hbige. }
           assert (Hside : Qle (u5c_quad_x d n0) (a # b)%Q).
           { apply (Qle_trans (u5c_quad_x d n0)
                     (((a # b)%Q - u5c_quad_x d n0 + u5c_quad_x d n0)%Q) (a # b)%Q).
             - apply (Qle_trans (u5c_quad_x d n0) (0%Q + u5c_quad_x d n0)%Q
                      (((a # b)%Q - u5c_quad_x d n0 + u5c_quad_x d n0)%Q)).
               + rewrite Qplus_0_l. apply Qle_refl.
               + apply (Qplus_le_compat 0%Q ((a # b)%Q - u5c_quad_x d n0)%Q
                          (u5c_quad_x d n0) (u5c_quad_x d n0));
                   [exact Hge0 | apply Qle_refl].
             - apply qeq_le.
               unfold Qeq, Qminus, Qplus, Qopp;
                 cbn [Qnum Qden Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; ring. }
           rewrite (ir2_abs_sub (a # b)%Q (u5c_quad_x d n0) Hside).
           exact (Qle_trans _
                    ((((a # b)%Q * (a # b)%Q - (Z.pos d # 1)%Q)
                       - u5c_quad_delta d n0)%Q * (1 # Pos.succ d)) _
                    (Qle_trans _ ((3 # (u5c_quad_K d * (b * b)))%Q) _ Hcce Hd3)
                    Hbige).
      * exfalso. exact (u5c_quad_no_sqrtQ d Hd (a # b)%Q (Qeq_sym _ _ Heq)).
  - (* Branch 1: q <= 0 *)
    assert (Hqx : Qle (a # b)%Q (u5c_quad_x d n0)).
    { apply (Qle_trans (a # b)%Q 0%Q (u5c_quad_x d n0)).
      - exact Hq0neg.
      - apply (Qle_trans 0%Q (1#1) (u5c_quad_x d n0)).
        + unfold Qle. cbn [Qnum Qden]. lia.
        + exact Hxlb. }
    rewrite (Qabs_Qminus (a # b)%Q (u5c_quad_x d n0)).
    rewrite (ir2_abs_sub (u5c_quad_x d n0) (a # b)%Q Hqx).
    apply (Qle_trans _ ((3 # (u5c_quad_K d * (b * b)))%Q)).
    + exact Hcce.
    + apply (Qle_trans _ (1#1)%Q).
      * unfold Qle, Qmult. cbn [Qnum Qden Qmult].
        rewrite ?Pos2Z.inj_mul. nia.
      * pose proof (Qopp_le_compat (a # b)%Q 0%Q Hq0neg) as Hnq.
        cbn [Qopp Z.opp] in Hnq.
        apply (Qle_trans (1#1) (u5c_quad_x d n0)
                ((u5c_quad_x d n0 + (- (a # b)))%Q)).
        { exact Hxlb. }
        { apply (Qle_trans (u5c_quad_x d n0) ((u5c_quad_x d n0 + 0%Q)%Q)
                   ((u5c_quad_x d n0 + (- (a # b)))%Q)).
          - rewrite Qplus_0_r. apply Qle_refl.
          - apply (Qplus_le_compat (u5c_quad_x d n0) (u5c_quad_x d n0) 0%Q
                     (- (a # b))%Q); [apply Qle_refl | exact Hnq]. }
Qed.

(* ============================================================ *)
(* S6. The uniform escape window (lic_escape_window instance)   *)
(* ============================================================ *)

Theorem u5c_quad_escape_window (d : positive) (Hd : u5c_quad_nonsq d) :
  lic_escape_window (u5c_quad_x d) (u5c_quad_e d).
Proof.
  intros [a b].
  remember (2 * (Z.to_nat (Z.pos d)) + 2 * (Z.to_nat (Z.pos b))
             + (Z.to_nat (Z.pos (u5c_quad_K d))))%nat as n0 eqn:En0.
  assert (Hn01 : (1 <= n0)%nat) by lia.
  assert (Hbnd : (2 * (Z.to_nat (Z.pos d)) + 2 * (Z.to_nat (Z.pos b))
                   + (Z.to_nat (Z.pos (u5c_quad_K d))) <= n0)%nat) by lia.
  pose proof (u5c_quad_e_bnd d b n0 Hbnd) as Heb.
  pose proof (u5c_quad_margin_closed d Hd a b n0 Hn01 Heb) as HrawT'.
  pose proof (QleT'_to_Qle _ _ HrawT') as Hraw.
  rewrite <- (lic_qlt_minus_add_r (Qabs (((a # b)%Q - u5c_quad_x d n0)%Q))
                (u5c_quad_e d n0)) in Hraw.
  assert (Hmargin : QleT' (((1 # (u5c_quad_K d * (b * b)))%Q
                             + (1 # (u5c_quad_K d * (b * b)))%Q))
                          (((Qabs (((a # b)%Q - u5c_quad_x d n0)%Q))
                             - u5c_quad_e d n0)%Q)).
  { exact (u5c_quad_qle_add_cancel_r _ _ (u5c_quad_e d n0)
             (Qle_to_QleT' _ _ Hraw)). }
  exists n0. split. exact Hn01.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (u5c_quad_e d n0)
          ((u5c_quad_e d n0
             + ((1 # (u5c_quad_K d * (b * b)))%Q
                + (1 # (u5c_quad_K d * (b * b)))%Q))%Q)
          (Qabs (((a # b)%Q - u5c_quad_x d n0)%Q))).
  - apply (lic_qlt_lt_add_r (u5c_quad_e d n0)
            ((1 # (u5c_quad_K d * (b * b)))%Q
             + (1 # (u5c_quad_K d * (b * b)))%Q)%Q).
    unfold Qlt, Qplus. cbn [Qnum Qden Qplus].
    pose proof (Pos2Z.is_pos (u5c_quad_K d * (b * b))). lia.
  - pose proof (QleT'_to_Qle _ _ Hmargin) as Hm.
    rewrite (Qplus_comm (u5c_quad_e d n0)
              ((1 # (u5c_quad_K d * (b * b)))%Q
               + (1 # (u5c_quad_K d * (b * b)))%Q)%Q).
    apply (Qle_trans _ ((((Qabs (((a # b)%Q - u5c_quad_x d n0)%Q))
                           - u5c_quad_e d n0)%Q) + u5c_quad_e d n0)%Q).
    + apply (Qplus_le_compat
               ((1 # (u5c_quad_K d * (b * b)))%Q
                + (1 # (u5c_quad_K d * (b * b)))%Q)%Q
               (((Qabs (((a # b)%Q - u5c_quad_x d n0)%Q))
                  - u5c_quad_e d n0)%Q)
               (u5c_quad_e d n0) (u5c_quad_e d n0)).
      * exact Hm.
      * apply Qle_refl.
    + apply qeq_le. apply lic_qlt_minus_add_r.
Qed.

(* ============================================================ *)
(* S7. Main theorem: uniform escape parameterization for sqrt-d *)
(* ============================================================ *)

Theorem quadratic_uniform_escape : forall (d : positive) (Hd : u5c_quad_nonsq d),
  forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) (u5c_quad_x d)
          (lic_seq_cauchy (u5c_quad_x d) (u5c_quad_e d)
             (u5c_quad_tail d Hd) (u5c_quad_vanish d Hd)))
          (real_const q)))).
Proof.
  intros d Hd q.
  exact (lic_irrational_criterion (u5c_quad_x d) (u5c_quad_e d)
           (u5c_quad_tail d Hd) (u5c_quad_escape_window d Hd)
           (u5c_quad_vanish d Hd) q).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction quadratic_uniform_escape u5c_quad_gap_abs u5c_quad_tail
  u5c_quad_vanish u5c_quad_e_bnd u5c_quad_margin_closed.

Print Assumptions quadratic_uniform_escape.
Print Assumptions u5c_quad_gap_abs.
