(*
  piu_zz_poincare_L1.v — Poincaré engine part 2: sub-lemmas L1a + L1b of the
  root-limit program, consuming the J01 engine as a Require dependency.

  使命 (mission): for the degree-9 recurrence coefficient polynomials
  pzz0..pzz3 (defined in piu_zz_poincare_engine) this file (i) expands all
  four polynomials to power-sum form and reads off the four degree-9 leading
  coefficients 241684560 / -5281230583980 / 309499457280 / -4583055360,
  pinning them to the J01 commensuration quadruple (sub-lemma L1a), and
  (ii) proves the coefficient convergence statement: for every rational
  delta > 0 there is an effective N0 with |A(n)-Ainf|, |B(n)-Binf|,
  |C(n)-Cinf| < delta for all n >= N0, where A(n) = p2(n)/p3(n) etc. and
  Ainf/Binf/Cinf are the J01 limit coefficients (sub-lemma L1b), carried in
  Set via sigT and a QltT carrier.
  依赖 (dependencies): piu_zz_poincare_engine (J01, copied read-only into
  this directory), Stdlib QArith, Qring, Lia, QArith.Qabs, Extraction.
  对标 (references): oSALIKHOVpi3.txt:86-147; Poincaré 1885; Elaydi 3rd ed.
  构造性 (constructive notes): all statements Set-carried (sigT, QltT, QeqT,
  QneqT, bool-Id); Q nonzero facts in the engine's QneqT carrier; mechanical
  ring identities declared inline. (26 refit items
  recast to Set carriers — Qeq→QeqT, neq→QneqT, Zcmp→Z.leb/Z.ltb bool-Id —
  plus the 8 prescription sites using the engine's new
  piu_zz_p3_pos bool-Id form; proof bodies minimally migrated behind
  qeqT_intro / iff-passthrough conversions, derivation chains verbatim.)
  编译配方 (build): rocq c -native-compiler no -q -Q . "" piu_zz_poincare_L1.v
*)

From Stdlib Require Import QArith Qring Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Extraction.
Require Import piu_zz_poincare_engine.

(* ================================================================== *)
(* Section L1a: power-sum expansion and the four leading coefficients. *)
(* ================================================================== *)

(* The four degree-9 leading coefficients, signed as they occur in
   pzz3, pzz2, pzz1, pzz0 respectively. *)
Definition piu_zz_L1_lead_p3 : Z := 241684560%Z.
Definition piu_zz_L1_lead_p2 : Z := (-5281230583980)%Z.
Definition piu_zz_L1_lead_p1 : Z := 309499457280%Z.
Definition piu_zz_L1_lead_p0 : Z := (-4583055360)%Z.

(* Power-sum forms (the n^9 slots are the four Definitions above). *)
Definition piu_zz_L1_powsum3 (n : nat) : Z :=
  (piu_zz_L1_lead_p3 * Z.of_nat n ^ 9 + 4610662992 * Z.of_nat n ^ 8
   + 38691218223 * Z.of_nat n ^ 7 + 187362872196 * Z.of_nat n ^ 6
   + 576700153800 * Z.of_nat n ^ 5 + 1169418475314 * Z.of_nat n ^ 4
   + 1561336723281 * Z.of_nat n ^ 3 + 1322762705706 * Z.of_nat n ^ 2
   + 644871561336 * Z.of_nat n + 137760460992)%Z.

Definition piu_zz_L1_powsum2 (n : nat) : Z :=
  (piu_zz_L1_lead_p2 * Z.of_nat n ^ 9 - 98110439743446 * Z.of_nat n ^ 8
   - 802455461444484 * Z.of_nat n ^ 7 - 3791210320854552 * Z.of_nat n ^ 6
   - 11397185280783672 * Z.of_nat n ^ 5 - 22598286485030202 * Z.of_nat n ^ 4
   - 29539303297937304 * Z.of_nat n ^ 3 - 24533264702236152 * Z.of_nat n ^ 2
   - 11741235794552544 * Z.of_nat n - 2465741252540160)%Z.

Definition piu_zz_L1_powsum1 (n : nat) : Z :=
  (piu_zz_L1_lead_p1 * Z.of_nat n ^ 9 + 5594881417216 * Z.of_nat n ^ 8
   + 44381868956224 * Z.of_nat n ^ 7 + 202598848221440 * Z.of_nat n ^ 6
   + 585981327537280 * Z.of_nat n ^ 5 + 1112531082896768 * Z.of_nat n ^ 4
   + 1385078041360960 * Z.of_nat n ^ 3 + 1089250275716992 * Z.of_nat n ^ 2
   + 490525613560320 * Z.of_nat n + 96306629529600)%Z.

Definition piu_zz_L1_powsum0 (n : nat) : Z :=
  (piu_zz_L1_lead_p0 * Z.of_nat n ^ 9 - 80557248512 * Z.of_nat n ^ 8
   - 617507289088 * Z.of_nat n ^ 7 - 2702460775424 * Z.of_nat n ^ 6
   - 7417406374912 * Z.of_nat n ^ 5 - 13185613626368 * Z.of_nat n ^ 4
   - 15097169462272 * Z.of_nat n ^ 3 - 10654675961856 * Z.of_nat n ^ 2
   - 4160208642048 * Z.of_nat n - 673567211520)%Z.

(* The expansion extraction: each factor-form definition equals its
   power-sum form for every n (mechanical ring identities; the leading
   coefficients are read off the n^9 slots of the Definitions above). *)
Lemma piu_zz_L1_powsum3_expansion : forall n : nat, pzz3 n = piu_zz_L1_powsum3 n.
Proof. intros n. unfold pzz3, piu_zz_L1_powsum3, piu_zz_L1_lead_p3. ring. Qed.

Lemma piu_zz_L1_powsum2_expansion : forall n : nat, pzz2 n = piu_zz_L1_powsum2 n.
Proof. intros n. unfold pzz2, piu_zz_L1_powsum2, piu_zz_L1_lead_p2. ring. Qed.

Lemma piu_zz_L1_powsum1_expansion : forall n : nat, pzz1 n = piu_zz_L1_powsum1 n.
Proof. intros n. unfold pzz1, piu_zz_L1_powsum1, piu_zz_L1_lead_p1. ring. Qed.

Lemma piu_zz_L1_powsum0_expansion : forall n : nat, pzz0 n = piu_zz_L1_powsum0 n.
Proof. intros n. unfold pzz0, piu_zz_L1_powsum0, piu_zz_L1_lead_p0. ring. Qed.

(* The reading: the four leading slots equal the pinned literals, and the
   J01 commensuration scale sends them exactly to the indicial coefficients. *)
Lemma piu_zz_L1_lead_read :
  ((Z.eqb piu_zz_L1_lead_p3 241684560)%Z
   && (Z.eqb piu_zz_L1_lead_p2 (-5281230583980))%Z
   && (Z.eqb piu_zz_L1_lead_p1 309499457280)%Z
   && (Z.eqb piu_zz_L1_lead_p0 (-4583055360))%Z) = true.
Proof. reflexivity. Qed.

Lemma piu_zz_L1_comm_bridge :
  ((Z.eqb (2237820 * 108) piu_zz_L1_lead_p3)%Z
   && (Z.eqb (2237820 * 2359989) (- piu_zz_L1_lead_p2))%Z
   && (Z.eqb (2237820 * 138304) piu_zz_L1_lead_p1)%Z
   && (Z.eqb (2237820 * 2048) (- piu_zz_L1_lead_p0))%Z) = true.
Proof. reflexivity. Qed.

(* vm_compute cross-check of the four expansions at sample points
   (guards against transcription slips; bool is Set-carried). *)
Definition piu_zz_L1_spotcheck : bool :=
  (Z.eqb (pzz3 0%nat) (piu_zz_L1_powsum3 0%nat))
  && (Z.eqb (pzz3 1%nat) (piu_zz_L1_powsum3 1%nat))
  && (Z.eqb (pzz3 2%nat) (piu_zz_L1_powsum3 2%nat))
  && (Z.eqb (pzz3 7%nat) (piu_zz_L1_powsum3 7%nat))
  && (Z.eqb (pzz2 0%nat) (piu_zz_L1_powsum2 0%nat))
  && (Z.eqb (pzz2 1%nat) (piu_zz_L1_powsum2 1%nat))
  && (Z.eqb (pzz2 3%nat) (piu_zz_L1_powsum2 3%nat))
  && (Z.eqb (pzz2 11%nat) (piu_zz_L1_powsum2 11%nat))
  && (Z.eqb (pzz1 0%nat) (piu_zz_L1_powsum1 0%nat))
  && (Z.eqb (pzz1 2%nat) (piu_zz_L1_powsum1 2%nat))
  && (Z.eqb (pzz1 5%nat) (piu_zz_L1_powsum1 5%nat))
  && (Z.eqb (pzz1 13%nat) (piu_zz_L1_powsum1 13%nat))
  && (Z.eqb (pzz0 0%nat) (piu_zz_L1_powsum0 0%nat))
  && (Z.eqb (pzz0 1%nat) (piu_zz_L1_powsum0 1%nat))
  && (Z.eqb (pzz0 3%nat) (piu_zz_L1_powsum0 3%nat))
  && (Z.eqb (pzz0 7%nat) (piu_zz_L1_powsum0 7%nat)).

Lemma piu_zz_L1_spotcheck_true : piu_zz_L1_spotcheck = true.
Proof. vm_compute. reflexivity. Qed.

(* Lower bound on the shift coefficient (denominator engine for L1b). *)
Lemma piu_zz_L1_p3_lower : forall n : nat, (1 <= n)%nat ->
  (Z.leb (241684560 * Z.of_nat n ^ 9) (pzz3 n))%Z = true.
Proof.
  intros n Hn. apply Z.leb_le. unfold pzz3.
  assert (Hm : (0 <= Z.of_nat n)%Z) by lia.
  assert (H1 : (0 <= Z.of_nat n ^ 1)%Z) by (apply Z.pow_nonneg; lia).
  assert (H2 : (0 <= Z.of_nat n ^ 2)%Z) by (apply Z.pow_nonneg; lia).
  assert (H3 : (0 <= Z.of_nat n ^ 3)%Z) by (apply Z.pow_nonneg; lia).
  assert (H4 : (0 <= Z.of_nat n ^ 4)%Z) by (apply Z.pow_nonneg; lia).
  assert (Hq : (559455 * Z.of_nat n ^ 4 <= 559455 * Z.of_nat n ^ 4
                + 3399916 * Z.of_nat n ^ 3 + 7651391 * Z.of_nat n ^ 2
                + 7554302 * Z.of_nat n + 2760952)%Z) by lia.
  nia.
Qed.

(* ================================================================== *)
(* Section L1b: coefficient convergence with an effective rational     *)
(* rate. The remainders 108*p2 + 2359989*p3, 108*p1 - 138304*p3 and    *)
(* 108*p0 + 2048*p3 have vanishing degree-9 part (exactly the J01      *)
(* commensuration), so each normalized coefficient approaches its      *)
(* J01 limit at rate kappa/(26101932480 * n) with                      *)
(* kappa = 2011079399899917312.                                        *)
(* ================================================================== *)

Inductive piu_zz_QltT (a b : Q) : Set :=
| piu_zz_qltT_intro : a < b -> piu_zz_QltT a b.

Definition piu_zz_Acoef (n : nat) : Q := zq (pzz2 n) * Qinv (zq (pzz3 n))%Q.
Definition piu_zz_Bcoef (n : nat) : Q := zq (pzz1 n) * Qinv (zq (pzz3 n))%Q.
Definition piu_zz_Ccoef (n : nat) : Q := zq (pzz0 n) * Qinv (zq (pzz3 n))%Q.

(* Rational helpers over the engine's zq embedding. *)
Lemma pw_zq_inv_pos : forall z : Z, (0 < z)%Z ->
  QeqT (Qinv (zq z)) (1 # Z.to_pos z)%Q.
Proof. intros z Hz. apply qeqT_intro. unfold zq.
  destruct z as [|p|p]; try lia. reflexivity. Qed.

Lemma pw_zq_mul : forall w v : Z, QeqT (zq (w * v)) (zq w * zq v)%Q.
Proof. intros w v. apply qeqT_intro. unfold zq, Qeq.
  cbn [Qmult Qnum Qden Pos.mul]. ring. Qed.

Lemma pw_zq_sub : forall w v : Z, QeqT (zq (w - v)) (zq w - zq v)%Q.
Proof. intros w v. apply qeqT_intro. unfold zq, Qeq, Qminus.
  cbn [Qplus Qopp Qmult Qnum Qden Pos.mul]. ring. Qed.

Lemma pw_zq_ext : forall w v : Z, w = v -> QeqT (zq w) (zq v)%Q.
Proof. intros w v Heq. apply qeqT_intro. rewrite Heq. reflexivity. Qed.

Lemma pw_zq_eq0 : forall z : Z, z <> 0%Z -> QneqT (zq z) 0%Q.
Proof.
  intros z Hz. apply qneqT_intro. intros Heq.
  apply (f_equal Qnum) in Heq. unfold zq in Heq. cbn in Heq.
  apply Hz. exact Heq.
Qed.

Lemma pw_Ainf_split : QeqT piu_zz_Ainf (zq (-2359989) * Qinv (zq 108)%Q).
Proof. apply qeqT_intro. unfold piu_zz_Ainf.
  pose proof (pw_zq_inv_pos (108)%Z ltac:(lia)) as Hi. destruct Hi as [Hi].
  rewrite Hi. unfold zq, Qeq. cbn [Qmult Qnum Qden Pos.mul Z.to_pos]. ring. Qed.

Lemma pw_Binf_split : QeqT piu_zz_Binf (zq 138304 * Qinv (zq 108)%Q).
Proof. apply qeqT_intro. unfold piu_zz_Binf.
  pose proof (pw_zq_inv_pos (108)%Z ltac:(lia)) as Hi. destruct Hi as [Hi].
  rewrite Hi. unfold zq, Qeq. cbn [Qmult Qnum Qden Pos.mul Z.to_pos]. ring. Qed.

Lemma pw_Cinf_split : QeqT piu_zz_Cinf (zq (-2048) * Qinv (zq 108)%Q).
Proof. apply qeqT_intro. unfold piu_zz_Cinf.
  pose proof (pw_zq_inv_pos (108)%Z ltac:(lia)) as Hi. destruct Hi as [Hi].
  rewrite Hi. unfold zq, Qeq. cbn [Qmult Qnum Qden Pos.mul Z.to_pos]. ring. Qed.

Lemma pw_mul_inv_r_cancel : forall x y : Q, ~ (y == 0%Q) ->
  QeqT x (x * y * Qinv y)%Q.
Proof. intros x y Hy. apply qeqT_intro. rewrite <- Qmult_assoc.
  rewrite (Qmult_inv_r y Hy). ring. Qed.

Lemma pw_frac_mul_cancel : forall a c b d : Q, ~ (b == 0%Q) -> ~ (d == 0%Q) ->
  QeqT ((a * Qinv b - c * Qinv d) * (b * d)) (a * d - c * b)%Q.
Proof.
  intros a c b d Hb Hd. apply qeqT_intro.
  transitivity ((a * Qinv b * (b * d) - c * Qinv d * (b * d)))%Q.
  { ring. }
  transitivity ((a * (b * Qinv b * d) - c * (d * Qinv d * b)))%Q.
  { ring. }
  rewrite (Qmult_inv_r b Hb). rewrite (Qmult_inv_r d Hd). ring.
Qed.

Lemma pw_pair_mul_1 : forall (z : Z) (dp : positive),
  QeqT (zq z * (1 # dp)) (z # dp)%Q.
Proof.
  intros z dp. apply qeqT_intro. unfold zq, Qeq. cbn [Qmult Qnum Qden].
  rewrite Pos.mul_1_l. ring.
Qed.

(* The three degree-8 remainders in power-sum form. *)
Definition piu_zz_R2sum (n : nat) : Z :=
  (285186451534920 * Z.of_nat n ^ 8 + 4645659566875275 * Z.of_nat n ^ 7
   + 32723602738674228 * Z.of_nat n ^ 6 + 130110008941671624 * Z.of_nat n ^ 5
   + 319199797754549730 * Z.of_nat n ^ 4 + 494492736061975077 * Z.of_nat n ^ 3
   + 472112847234892818 * Z.of_nat n ^ 2 + 253836325354110552 * Z.of_nat n
   + 58813117301711808)%Z.

Definition piu_zz_R1sum (n : nat) : Z :=
  (-33425941386240 * Z.of_nat n ^ 8 - 557908397841600 * Z.of_nat n ^ 7
   - 4032359068280064 * Z.of_nat n ^ 6 - 16473954697128960 * Z.of_nat n ^ 5
   - 41581895856976512 * Z.of_nat n ^ 4 - 66350685709671744 * Z.of_nat n ^ 3
   - 65304343472527488 * Z.of_nat n ^ 2 - 36211550154499584 * Z.of_nat n
   - 8651706807840768)%Z.

Definition piu_zz_R0sum (n : nat) : Z :=
  (742454968320 * Z.of_nat n ^ 8 + 12548827699200 * Z.of_nat n ^ 7
   + 91853398511616 * Z.of_nat n ^ 6 + 380002026491904 * Z.of_nat n ^ 5
   + 970922765795328 * Z.of_nat n ^ 4 + 1567123307354112 * Z.of_nat n ^ 3
   + 1558313017405440 * Z.of_nat n ^ 2 + 871394424274944 * Z.of_nat n
   + 209388165267456)%Z.

Lemma pw_R2ring : forall n : nat, (108 * pzz2 n + 2359989 * pzz3 n)%Z = piu_zz_R2sum n.
Proof. intros n. unfold pzz2, pzz3, piu_zz_R2sum. ring. Qed.

Lemma pw_R1ring : forall n : nat, (108 * pzz1 n - 138304 * pzz3 n)%Z = piu_zz_R1sum n.
Proof. intros n. unfold pzz1, pzz3, piu_zz_R1sum. ring. Qed.

Lemma pw_R0ring : forall n : nat, (108 * pzz0 n + 2048 * pzz3 n)%Z = piu_zz_R0sum n.
Proof. intros n. unfold pzz0, pzz3, piu_zz_R0sum. ring. Qed.

(* vm_compute cross-check of the three remainder identities. *)
Definition piu_zz_L1_rspotcheck : bool :=
  (Z.eqb (108 * pzz2 2%nat + 2359989 * pzz3 2%nat) (piu_zz_R2sum 2%nat))
  && (Z.eqb (108 * pzz2 9%nat + 2359989 * pzz3 9%nat) (piu_zz_R2sum 9%nat))
  && (Z.eqb (108 * pzz1 4%nat - 138304 * pzz3 4%nat) (piu_zz_R1sum 4%nat))
  && (Z.eqb (108 * pzz1 9%nat - 138304 * pzz3 9%nat) (piu_zz_R1sum 9%nat))
  && (Z.eqb (108 * pzz0 6%nat + 2048 * pzz3 6%nat) (piu_zz_R0sum 6%nat))
  && (Z.eqb (108 * pzz0 9%nat + 2048 * pzz3 9%nat) (piu_zz_R0sum 9%nat)).

Lemma piu_zz_L1_rspotcheck_true : piu_zz_L1_rspotcheck = true.
Proof. vm_compute. reflexivity. Qed.

(* The multiplied-through fraction identities. *)
Lemma pw_bd_nonzero : forall n : nat, QneqT (zq (pzz3 n) * zq 108) 0%Q.
Proof.
  intros n. apply qneqT_intro. intros Heq.
  pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  assert (Hne : (pzz3 n <> 0)%Z) by lia.
  apply (f_equal Qnum) in Heq. unfold zq in Heq. cbn in Heq. lia.
Qed.

Lemma pw_HfracA_mul : forall n : nat,
  QeqT ((piu_zz_Acoef n - piu_zz_Ainf) * (zq (pzz3 n) * zq 108))
       (zq (piu_zz_R2sum n))%Q.
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  apply qeqT_intro.
  assert (Hb : ~ (zq (pzz3 n) == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  assert (Hd : ~ (zq 108 == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  destruct (pw_Ainf_split) as [Ha]. rewrite Ha.
  destruct (pw_frac_mul_cancel (zq (pzz2 n)) (zq (-2359989))
             (zq (pzz3 n)) (zq 108) Hb Hd) as [Hf]. rewrite Hf.
  transitivity (zq (pzz2 n * 108 - (-2359989) * pzz3 n))%Q.
  { destruct (pw_zq_sub (pzz2 n * 108) ((-2359989) * pzz3 n)) as [Hs].
    rewrite Hs.
    destruct (pw_zq_mul (pzz2 n) 108) as [H1]. rewrite H1.
    destruct (pw_zq_mul (-2359989) (pzz3 n)) as [H2]. rewrite H2. reflexivity. }
  apply pw_zq_ext. rewrite <- pw_R2ring. ring.
Qed.

Lemma pw_HfracB_mul : forall n : nat,
  QeqT ((piu_zz_Bcoef n - piu_zz_Binf) * (zq (pzz3 n) * zq 108))
       (zq (piu_zz_R1sum n))%Q.
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  apply qeqT_intro.
  assert (Hb : ~ (zq (pzz3 n) == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  assert (Hd : ~ (zq 108 == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  destruct (pw_Binf_split) as [Hb0]. rewrite Hb0.
  destruct (pw_frac_mul_cancel (zq (pzz1 n)) (zq 138304)
             (zq (pzz3 n)) (zq 108) Hb Hd) as [Hf]. rewrite Hf.
  transitivity (zq (pzz1 n * 108 - 138304 * pzz3 n))%Q.
  { destruct (pw_zq_sub (pzz1 n * 108) (138304 * pzz3 n)) as [Hs].
    rewrite Hs.
    destruct (pw_zq_mul (pzz1 n) 108) as [H1]. rewrite H1.
    destruct (pw_zq_mul 138304 (pzz3 n)) as [H2]. rewrite H2. reflexivity. }
  apply pw_zq_ext. rewrite <- pw_R1ring. ring.
Qed.

Lemma pw_HfracC_mul : forall n : nat,
  QeqT ((piu_zz_Ccoef n - piu_zz_Cinf) * (zq (pzz3 n) * zq 108))
       (zq (piu_zz_R0sum n))%Q.
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  apply qeqT_intro.
  assert (Hb : ~ (zq (pzz3 n) == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  assert (Hd : ~ (zq 108 == 0%Q)).
  { intros Heq. unfold zq, Qeq in Heq. cbn in Heq. lia. }
  destruct (pw_Cinf_split) as [Hc0]. rewrite Hc0.
  destruct (pw_frac_mul_cancel (zq (pzz0 n)) (zq (-2048))
             (zq (pzz3 n)) (zq 108) Hb Hd) as [Hf]. rewrite Hf.
  transitivity (zq (pzz0 n * 108 - (-2048) * pzz3 n))%Q.
  { destruct (pw_zq_sub (pzz0 n * 108) ((-2048) * pzz3 n)) as [Hs].
    rewrite Hs.
    destruct (pw_zq_mul (pzz0 n) 108) as [H1]. rewrite H1.
    destruct (pw_zq_mul (-2048) (pzz3 n)) as [H2]. rewrite H2. reflexivity. }
  apply pw_zq_ext. rewrite <- pw_R0ring. ring.
Qed.

(* The pair-form fraction identities (numerators Rsum, denominator
   Z.to_pos (pzz3 n * 108) > 0). *)
Lemma pw_HfracA_pair : forall n : nat,
  QeqT (piu_zz_Acoef n - piu_zz_Ainf)%Q
       ((piu_zz_R2sum n # Z.to_pos (pzz3 n * 108))%Q).
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  assert (Hp108 : (0 < pzz3 n * 108)%Z) by lia.
  apply qeqT_intro.
  assert (Hbd : ~ (zq (pzz3 n) * zq 108 == 0%Q)).
  { intros Hzero. unfold zq, Qeq in Hzero. cbn in Hzero. lia. }
  transitivity ((piu_zz_Acoef n - piu_zz_Ainf) * (zq (pzz3 n) * zq 108)
                * Qinv (zq (pzz3 n) * zq 108))%Q.
  { destruct (pw_mul_inv_r_cancel (piu_zz_Acoef n - piu_zz_Ainf)%Q
               (zq (pzz3 n) * zq 108) Hbd) as [Hc]. exact Hc. }
  destruct (pw_HfracA_mul n) as [Hm]. rewrite Hm.
  destruct (pw_zq_mul (pzz3 n) 108) as [Hm2]. rewrite <- Hm2.
  destruct (pw_zq_inv_pos (pzz3 n * 108) Hp108) as [Hi]. rewrite Hi.
  destruct (pw_pair_mul_1 (piu_zz_R2sum n)
             (Z.to_pos (pzz3 n * 108))) as [Hp1]. exact Hp1.
Qed.

Lemma pw_HfracB_pair : forall n : nat,
  QeqT (piu_zz_Bcoef n - piu_zz_Binf)%Q
       ((piu_zz_R1sum n # Z.to_pos (pzz3 n * 108))%Q).
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  assert (Hp108 : (0 < pzz3 n * 108)%Z) by lia.
  apply qeqT_intro.
  assert (Hbd : ~ (zq (pzz3 n) * zq 108 == 0%Q)).
  { intros Hzero. unfold zq, Qeq in Hzero. cbn in Hzero. lia. }
  transitivity ((piu_zz_Bcoef n - piu_zz_Binf) * (zq (pzz3 n) * zq 108)
                * Qinv (zq (pzz3 n) * zq 108))%Q.
  { destruct (pw_mul_inv_r_cancel (piu_zz_Bcoef n - piu_zz_Binf)%Q
               (zq (pzz3 n) * zq 108) Hbd) as [Hc]. exact Hc. }
  destruct (pw_HfracB_mul n) as [Hm]. rewrite Hm.
  destruct (pw_zq_mul (pzz3 n) 108) as [Hm2]. rewrite <- Hm2.
  destruct (pw_zq_inv_pos (pzz3 n * 108) Hp108) as [Hi]. rewrite Hi.
  destruct (pw_pair_mul_1 (piu_zz_R1sum n)
             (Z.to_pos (pzz3 n * 108))) as [Hp1]. exact Hp1.
Qed.

Lemma pw_HfracC_pair : forall n : nat,
  QeqT (piu_zz_Ccoef n - piu_zz_Cinf)%Q
       ((piu_zz_R0sum n # Z.to_pos (pzz3 n * 108))%Q).
Proof.
  intros n. pose proof (piu_zz_p3_pos n) as Hp.
  apply Z.ltb_lt in Hp.
  assert (Hp108 : (0 < pzz3 n * 108)%Z) by lia.
  apply qeqT_intro.
  assert (Hbd : ~ (zq (pzz3 n) * zq 108 == 0%Q)).
  { intros Hzero. unfold zq, Qeq in Hzero. cbn in Hzero. lia. }
  transitivity ((piu_zz_Ccoef n - piu_zz_Cinf) * (zq (pzz3 n) * zq 108)
                * Qinv (zq (pzz3 n) * zq 108))%Q.
  { destruct (pw_mul_inv_r_cancel (piu_zz_Ccoef n - piu_zz_Cinf)%Q
               (zq (pzz3 n) * zq 108) Hbd) as [Hc]. exact Hc. }
  destruct (pw_HfracC_mul n) as [Hm]. rewrite Hm.
  destruct (pw_zq_mul (pzz3 n) 108) as [Hm2]. rewrite <- Hm2.
  destruct (pw_zq_inv_pos (pzz3 n * 108) Hp108) as [Hi]. rewrite Hi.
  destruct (pw_pair_mul_1 (piu_zz_R0sum n)
             (Z.to_pos (pzz3 n * 108))) as [Hp1]. exact Hp1.
Qed.

(* Absolute-value bands for the three remainders (kappa folds all
   coefficient sizes: 2011079399899917312 = sum of |coeffs| over the three
   remainder polynomials). *)
Lemma pw_R2band : forall n : nat, (1 <= n)%nat ->
  ((Z.leb (- 2011079399899917312 * Z.of_nat n ^ 8) (piu_zz_R2sum n))%Z
   && (Z.leb (piu_zz_R2sum n) (2011079399899917312 * Z.of_nat n ^ 8))%Z) = true.
Proof.
  intros n Hn.
  assert (Hb : (- 2011079399899917312 * Z.of_nat n ^ 8 <= piu_zz_R2sum n
                <= 2011079399899917312 * Z.of_nat n ^ 8)%Z).
  { unfold piu_zz_R2sum.
  assert (Hm : (1 <= Z.of_nat n)%Z) by lia.
  assert (P1 : (0 <= Z.of_nat n ^ 1)%Z) by (apply Z.pow_nonneg; lia).
  assert (P2 : (0 <= Z.of_nat n ^ 2)%Z) by (apply Z.pow_nonneg; lia).
  assert (P3 : (0 <= Z.of_nat n ^ 3)%Z) by (apply Z.pow_nonneg; lia).
  assert (P4 : (0 <= Z.of_nat n ^ 4)%Z) by (apply Z.pow_nonneg; lia).
  assert (P5 : (0 <= Z.of_nat n ^ 5)%Z) by (apply Z.pow_nonneg; lia).
  assert (P6 : (0 <= Z.of_nat n ^ 6)%Z) by (apply Z.pow_nonneg; lia).
  assert (P7 : (0 <= Z.of_nat n ^ 7)%Z) by (apply Z.pow_nonneg; lia).
  assert (P8 : (0 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_nonneg; lia).
  assert (Q1 : (Z.of_nat n ^ 1 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q2 : (Z.of_nat n ^ 2 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q3 : (Z.of_nat n ^ 3 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q4 : (Z.of_nat n ^ 4 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q5 : (Z.of_nat n ^ 5 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q6 : (Z.of_nat n ^ 6 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q7 : (Z.of_nat n ^ 7 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
  }
  apply andb_true_intro. split.
  - apply Z.leb_le. exact (proj1 Hb).
  - apply Z.leb_le. exact (proj2 Hb).
Qed.

Lemma pw_R1band : forall n : nat, (1 <= n)%nat ->
  ((Z.leb (- 2011079399899917312 * Z.of_nat n ^ 8) (piu_zz_R1sum n))%Z
   && (Z.leb (piu_zz_R1sum n) (2011079399899917312 * Z.of_nat n ^ 8))%Z) = true.
Proof.
  intros n Hn.
  assert (Hb : (- 2011079399899917312 * Z.of_nat n ^ 8 <= piu_zz_R1sum n
                <= 2011079399899917312 * Z.of_nat n ^ 8)%Z).
  { unfold piu_zz_R1sum.
  assert (Hm : (1 <= Z.of_nat n)%Z) by lia.
  assert (P1 : (0 <= Z.of_nat n ^ 1)%Z) by (apply Z.pow_nonneg; lia).
  assert (P2 : (0 <= Z.of_nat n ^ 2)%Z) by (apply Z.pow_nonneg; lia).
  assert (P3 : (0 <= Z.of_nat n ^ 3)%Z) by (apply Z.pow_nonneg; lia).
  assert (P4 : (0 <= Z.of_nat n ^ 4)%Z) by (apply Z.pow_nonneg; lia).
  assert (P5 : (0 <= Z.of_nat n ^ 5)%Z) by (apply Z.pow_nonneg; lia).
  assert (P6 : (0 <= Z.of_nat n ^ 6)%Z) by (apply Z.pow_nonneg; lia).
  assert (P7 : (0 <= Z.of_nat n ^ 7)%Z) by (apply Z.pow_nonneg; lia).
  assert (P8 : (0 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_nonneg; lia).
  assert (Q1 : (Z.of_nat n ^ 1 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q2 : (Z.of_nat n ^ 2 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q3 : (Z.of_nat n ^ 3 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q4 : (Z.of_nat n ^ 4 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q5 : (Z.of_nat n ^ 5 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q6 : (Z.of_nat n ^ 6 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q7 : (Z.of_nat n ^ 7 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
  }
  apply andb_true_intro. split.
  - apply Z.leb_le. exact (proj1 Hb).
  - apply Z.leb_le. exact (proj2 Hb).
Qed.

Lemma pw_R0band : forall n : nat, (1 <= n)%nat ->
  ((Z.leb (- 2011079399899917312 * Z.of_nat n ^ 8) (piu_zz_R0sum n))%Z
   && (Z.leb (piu_zz_R0sum n) (2011079399899917312 * Z.of_nat n ^ 8))%Z) = true.
Proof.
  intros n Hn.
  assert (Hb : (- 2011079399899917312 * Z.of_nat n ^ 8 <= piu_zz_R0sum n
                <= 2011079399899917312 * Z.of_nat n ^ 8)%Z).
  { unfold piu_zz_R0sum.
  assert (Hm : (1 <= Z.of_nat n)%Z) by lia.
  assert (P1 : (0 <= Z.of_nat n ^ 1)%Z) by (apply Z.pow_nonneg; lia).
  assert (P2 : (0 <= Z.of_nat n ^ 2)%Z) by (apply Z.pow_nonneg; lia).
  assert (P3 : (0 <= Z.of_nat n ^ 3)%Z) by (apply Z.pow_nonneg; lia).
  assert (P4 : (0 <= Z.of_nat n ^ 4)%Z) by (apply Z.pow_nonneg; lia).
  assert (P5 : (0 <= Z.of_nat n ^ 5)%Z) by (apply Z.pow_nonneg; lia).
  assert (P6 : (0 <= Z.of_nat n ^ 6)%Z) by (apply Z.pow_nonneg; lia).
  assert (P7 : (0 <= Z.of_nat n ^ 7)%Z) by (apply Z.pow_nonneg; lia).
  assert (P8 : (0 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_nonneg; lia).
  assert (Q1 : (Z.of_nat n ^ 1 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q2 : (Z.of_nat n ^ 2 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q3 : (Z.of_nat n ^ 3 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q4 : (Z.of_nat n ^ 4 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q5 : (Z.of_nat n ^ 5 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q6 : (Z.of_nat n ^ 6 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Q7 : (Z.of_nat n ^ 7 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
  }
  apply andb_true_intro. split.
  - apply Z.leb_le. exact (proj1 Hb).
  - apply Z.leb_le. exact (proj2 Hb).
Qed.

(* The effective N0 witness and its Z-rate. *)
Definition piu_zz_N0 (delta : Q) : nat :=
  S (Z.to_nat (2011079399899917312 * QDen delta
               / (26101932480 * Qnum delta))).

Lemma piu_zz_L1b_rate : forall delta : Q, (0 < delta)%Q -> forall n : nat,
  (piu_zz_N0 delta <= n)%nat ->
  (Z.ltb (2011079399899917312 * QDen delta)
         ((26101932480 * Qnum delta) * Z.of_nat n))%Z = true.
Proof.
  intros delta Hdelta n Hn. apply Z.ltb_lt. unfold piu_zz_N0 in Hn.
  assert (Hqdp : (0 < QDen delta)%Z) by apply Pos2Z.is_pos.
  assert (Hqn : (0 < Qnum delta)%Z) by (unfold Qlt in Hdelta; cbn in Hdelta; lia).
  assert (Ha0 : (0 <= 2011079399899917312 * QDen delta)%Z) by lia.
  assert (Hb0 : (0 < 26101932480 * Qnum delta)%Z) by lia.
  assert (Hbne : ((26101932480 * Qnum delta) <> 0)%Z) by lia.
  assert (Hmp : (0 <= 2011079399899917312 * QDen delta
                   mod (26101932480 * Qnum delta) < 26101932480 * Qnum delta)%Z)
    by (apply Z.mod_pos_bound; lia).
  assert (Hdm : (2011079399899917312 * QDen delta
                = (26101932480 * Qnum delta) * (2011079399899917312 * QDen delta
                    / (26101932480 * Qnum delta))
                + (2011079399899917312 * QDen delta
                   mod (26101932480 * Qnum delta)))%Z)
    by (apply Z.div_mod; exact Hbne).
  assert (Hdq : (0 <= 2011079399899917312 * QDen delta
                   / (26101932480 * Qnum delta))%Z)
    by (apply Z.div_pos; lia).
  remember (2011079399899917312 * QDen delta
            / (26101932480 * Qnum delta))%Z as q.
  remember (2011079399899917312 * QDen delta
            mod (26101932480 * Qnum delta))%Z as r.
  assert (Hzn : (Z.of_nat (Z.to_nat q) = q)%Z) by (apply Znat.Z2Nat.id; lia).
  assert (Hmq : (q + 1 <= Z.of_nat n)%Z) by lia.
  assert (Hb1 : (1 <= 26101932480 * Qnum delta)%Z) by lia.
  assert (Hs1 : ((q + 1) * (26101932480 * Qnum delta)
                 <= Z.of_nat n * (26101932480 * Qnum delta))%Z)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hs2 : ((26101932480 * Qnum delta) * q
                 + (26101932480 * Qnum delta)
                 > 2011079399899917312 * QDen delta)%Z) by lia.
  replace ((q + 1) * (26101932480 * Qnum delta))%Z
    with ((26101932480 * Qnum delta) * q + (26101932480 * Qnum delta))%Z
    in Hs1 by ring.
  lia.
Qed.

(* Both Z-bands at a suitable n. *)
Lemma piu_zz_zbands : forall (Rsum : nat -> Z) (delta : Q) (n : nat),
  (0 < delta)%Q -> (piu_zz_N0 delta <= n)%nat ->
  (forall k : nat, (1 <= k)%nat ->
     (- 2011079399899917312 * Z.of_nat k ^ 8 <= Rsum k
      <= 2011079399899917312 * Z.of_nat k ^ 8)%Z) ->
  ((Z.ltb (Rsum n * QDen delta) (Qnum delta * (pzz3 n * 108)))%Z
   && (Z.ltb (- Rsum n * QDen delta) (Qnum delta * (pzz3 n * 108)))%Z) = true.
Proof.
  intros Rsum delta n Hdelta Hn Hband.
  assert (Hbands : (Rsum n * QDen delta < Qnum delta * (pzz3 n * 108))%Z
                   /\ (- Rsum n * QDen delta < Qnum delta * (pzz3 n * 108))%Z).
  { assert (Hn1 : (1 <= n)%nat) by (unfold piu_zz_N0 in Hn; lia).
  assert (Hm : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hqdp : (0 < QDen delta)%Z) by apply Pos2Z.is_pos.
  assert (Hqn : (0 < Qnum delta)%Z) by (unfold Qlt in Hdelta; cbn in Hdelta; lia).
  pose proof (piu_zz_L1_p3_lower n Hn1) as Hp3.
  apply Z.leb_le in Hp3.
  pose proof (piu_zz_L1b_rate delta Hdelta n Hn) as Hrate.
  apply Z.ltb_lt in Hrate.
  assert (Hm8 : (0 <= Z.of_nat n ^ 8)%Z) by (apply Z.pow_nonneg; lia).
  assert (Hm9 : (Z.of_nat n ^ 9 = Z.of_nat n * Z.of_nat n ^ 8)%Z) by ring.
  destruct (Hband n Hn1) as [Hb1 Hb2].
  assert (Hm8p : (0 < Z.of_nat n ^ 8)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hhop : (2011079399899917312 * QDen delta * Z.of_nat n ^ 8
                  < (26101932480 * Qnum delta) * Z.of_nat n
                    * Z.of_nat n ^ 8)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r _ _ _ Hm8p)). exact Hrate. }
  assert (Hh1 : (Rsum n * QDen delta
                 <= (2011079399899917312 * Z.of_nat n ^ 8) * QDen delta)%Z)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hh5 : (- Rsum n * QDen delta
                 <= (2011079399899917312 * Z.of_nat n ^ 8) * QDen delta)%Z)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hh3 : ((26101932480 * Qnum delta) * Z.of_nat n * Z.of_nat n ^ 8
                 <= (108 * pzz3 n) * Qnum delta)%Z).
  { replace (Z.of_nat n ^ 9)%Z with (Z.of_nat n * Z.of_nat n ^ 8)%Z in Hp3
      by ring.
    replace (26101932480 * Qnum delta * Z.of_nat n * Z.of_nat n ^ 8)%Z
      with ((108 * 241684560 * (Z.of_nat n * Z.of_nat n ^ 8)) * Qnum delta)%Z
      by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  split; lia.
  }
  apply andb_true_intro. split.
  - apply Z.ltb_lt. exact (proj1 Hbands).
  - apply Z.ltb_lt. exact (proj2 Hbands).
Qed.

(* Pair bridge: bands on (numerator, positive denominator) give the
   Set-carried Qabs statement. *)
Lemma piu_zz_band_pair : forall (nu nd : Z) (dp : positive) (x : Q) (delta : Q),
  nd = Z.pos dp ->
  x == (nu # dp)%Q -> (0 < delta)%Q ->
  (nu * QDen delta < Qnum delta * nd)%Z ->
  (- nu * QDen delta < Qnum delta * nd)%Z ->
  piu_zz_QltT (Qabs x) delta.
Proof.
  intros nu nd dp x delta Hnd Hx Hdelta Hr Hl. apply piu_zz_qltT_intro.
  rewrite Hx. unfold Qabs. unfold Qlt. cbn [Qnum Qden].
  rewrite <- Hnd.
  replace (Z.abs nu * QDen delta)%Z
    with (Z.abs (nu * QDen delta))%Z
    by (rewrite Z.abs_mul, (Z.abs_eq (QDen delta)) by lia; lia).
  apply Z.abs_lt. split; lia.
Qed.

(* Sub-lemma L1b, one coefficient. *)
Lemma piu_zz_L1b_half : forall (mk : nat -> Q) (cinf : Q) (Rsum : nat -> Z),
  (forall n : nat, (mk n - cinf)%Q == (Rsum n # Z.to_pos (pzz3 n * 108))%Q) ->
  (forall n : nat, (1 <= n)%nat ->
     (- 2011079399899917312 * Z.of_nat n ^ 8 <= Rsum n
      <= 2011079399899917312 * Z.of_nat n ^ 8)%Z) ->
  forall delta : Q, (0 < delta)%Q -> forall n : nat,
    (piu_zz_N0 delta <= n)%nat -> piu_zz_QltT (Qabs (mk n - cinf)) delta.
Proof.
  intros mk cinf Rsum Hfrac Hband delta Hdelta n Hn.
  pose proof (piu_zz_zbands Rsum delta n Hdelta Hn Hband) as Hzb.
  apply andb_true_iff in Hzb. destruct Hzb as [Hr Hl].
  apply Z.ltb_lt in Hr. apply Z.ltb_lt in Hl.
  assert (Hp108 : (0 < pzz3 n * 108)%Z)
    by (pose proof (piu_zz_p3_pos n) as Hp; apply Z.ltb_lt in Hp; lia).
  apply (piu_zz_band_pair (Rsum n) (pzz3 n * 108)%Z
           (Z.to_pos (pzz3 n * 108)) (mk n - cinf) delta
           (eq_sym (Z2Pos.id (pzz3 n * 108) Hp108)) (Hfrac n) Hdelta).
  - exact Hr.
  - exact Hl.
Qed.

(* Sub-lemma L1b: the three coefficients converge simultaneously, with
   the effective witness N0. Statement carried in Set via the carrier
   below (Set-anchored so the compiled statement stays in Set). *)
Definition piu_zz_L1b_stmt (delta : Q) : Set :=
  (0 < delta)%Q -> { N0 : nat & forall n : nat, (N0 <= n)%nat ->
      piu_zz_QltT (Qabs (piu_zz_Acoef n - piu_zz_Ainf)) delta
      * piu_zz_QltT (Qabs (piu_zz_Bcoef n - piu_zz_Binf)) delta
      * piu_zz_QltT (Qabs (piu_zz_Ccoef n - piu_zz_Cinf)) delta }.

Theorem piu_zz_L1b_coeff_conv : forall delta : Q, piu_zz_L1b_stmt delta.
Proof.
  intros delta Hdelta. unfold piu_zz_L1b_stmt. exists (piu_zz_N0 delta). intros n Hn. split.
  - split.
    + apply (piu_zz_L1b_half piu_zz_Acoef piu_zz_Ainf piu_zz_R2sum
               (fun k => match pw_HfracA_pair k with
                         | qeqT_intro _ _ He => He end)
               (fun k Hk =>
                 let Hbb := proj1 (andb_true_iff _ _) (pw_R2band k Hk) in
                 conj (proj1 (Z.leb_le _ _) (proj1 Hbb))
                      (proj1 (Z.leb_le _ _) (proj2 Hbb)))
               delta Hdelta n Hn).
    + apply (piu_zz_L1b_half piu_zz_Bcoef piu_zz_Binf piu_zz_R1sum
               (fun k => match pw_HfracB_pair k with
                         | qeqT_intro _ _ He => He end)
               (fun k Hk =>
                 let Hbb := proj1 (andb_true_iff _ _) (pw_R1band k Hk) in
                 conj (proj1 (Z.leb_le _ _) (proj1 Hbb))
                      (proj1 (Z.leb_le _ _) (proj2 Hbb)))
               delta Hdelta n Hn).
  - apply (piu_zz_L1b_half piu_zz_Ccoef piu_zz_Cinf piu_zz_R0sum
             (fun k => match pw_HfracC_pair k with
                       | qeqT_intro _ _ He => He end)
             (fun k Hk =>
               let Hbb := proj1 (andb_true_iff _ _) (pw_R0band k Hk) in
               conj (proj1 (Z.leb_le _ _) (proj1 Hbb))
                    (proj1 (Z.leb_le _ _) (proj2 Hbb)))
             delta Hdelta n Hn).
Qed.

(* ================================================================== *)
(* Audit: assumption accounting and data-level extraction probe.       *)
(* ================================================================== *)

Print Assumptions piu_zz_L1_powsum3_expansion.
Print Assumptions piu_zz_L1_powsum0_expansion.
Print Assumptions piu_zz_L1_lead_read.
Print Assumptions piu_zz_L1_comm_bridge.
Print Assumptions piu_zz_L1_spotcheck_true.
Print Assumptions piu_zz_L1_rspotcheck_true.
Print Assumptions piu_zz_L1_p3_lower.
Print Assumptions piu_zz_L1b_rate.
Print Assumptions piu_zz_zbands.
Print Assumptions piu_zz_band_pair.
Print Assumptions piu_zz_L1b_stmt.
Print Assumptions piu_zz_L1b_coeff_conv.
(* refit audit: the 21 refit items not covered above —
   G4 requires Closed for every anchor in the file. *)
Print Assumptions pw_zq_inv_pos.
Print Assumptions pw_zq_mul.
Print Assumptions pw_zq_sub.
Print Assumptions pw_zq_ext.
Print Assumptions pw_zq_eq0.
Print Assumptions pw_Ainf_split.
Print Assumptions pw_Binf_split.
Print Assumptions pw_Cinf_split.
Print Assumptions pw_mul_inv_r_cancel.
Print Assumptions pw_frac_mul_cancel.
Print Assumptions pw_pair_mul_1.
Print Assumptions pw_bd_nonzero.
Print Assumptions pw_HfracA_mul.
Print Assumptions pw_HfracB_mul.
Print Assumptions pw_HfracC_mul.
Print Assumptions pw_HfracA_pair.
Print Assumptions pw_HfracB_pair.
Print Assumptions pw_HfracC_pair.
Print Assumptions pw_R2band.
Print Assumptions pw_R1band.
Print Assumptions pw_R0band.

Extraction "piu_zz_L1_data.ml" pzz0 pzz1 pzz2 pzz3 piu_zz_L1_powsum0
  piu_zz_L1_powsum1 piu_zz_L1_powsum2 piu_zz_L1_powsum3 piu_zz_R0sum
  piu_zz_R1sum piu_zz_R2sum piu_zz_Acoef piu_zz_Bcoef piu_zz_Ccoef
  piu_zz_N0.
