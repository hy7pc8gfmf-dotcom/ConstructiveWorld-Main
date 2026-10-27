(* ========================================================================= *)
(* Module   : piu_zz_mu_assembly                                             *)
(* Mission  : real-layer interface adapters for the pi irrationality measure *)
(*            certificate in rate form |pi - q| >= c0/h(q)^8 (c0=1/71663616, *)
(*            h(q) = 1 + denominator of q): conversion between the pointwise *)
(*            distance certificate lw1m_dist_pt and the rate-form real_lt   *)
(*            statement consumed by the v2 rate-slot bridge; criterion data *)
(*            pins (kappa = 1/(2*c0) = 35831808, sigma = 7*tau = 14,        *)
(*            tau = 2) aligning piu_mu_c0 = 1/(2*kappa) with c0; and the    *)
(*            tau-th power cancellation lemma for piu_mu_criterion.         *)
(* Dependencies: S01_BaseRing, S02_CauchyComplete, S03_QExp, S10_KVQuantTrig,*)
(*            PiEnvelope, LW0MLicBridge, LW1PiMeasure,                      *)
(*            Local.LW0LeibSeparation, piu1932_tight_bound_instantiated,     *)
(*            piu_mu_criterion, piu_zz_bridge_real; Stdlib QArith, Qring,    *)
(*            Lqa, Qpower.                                                  *)
(* References: Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9 (2020)   *)
(*            407-419 (arXiv:1912.06345), Lemma 2; real_lt                  *)
(*            (S02_CauchyComplete), lw1m_dist_pt (LW1PiMeasure),            *)
(*            leibsep_metric_pi_transport (Local/LW0LeibSeparation).        *)
(* Constructivity: every named statement is carried in Set (QltT, QltT',    *)
(*            QeqT, sigT); no unproved goals; no global assumptions; no     *)
(*            classical logic; definitions transparent; lia/lra only as    *)
(*            auxiliary linear-arithmetic steps inside proofs (piu1904 and  *)
(*            piu_mu_criterion precedent).                                  *)
(* Build    : full-literal COQLIB/ROCQLIB export, then coqc -native-compiler *)
(*            no -q with world tree, Local subtree and this directory as    *)
(*            -Q roots (Rocq 9.1.0, thermal guard on every compile).        *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import Local.LW0LeibSeparation.
Require Import piu1932_tight_bound_instantiated.
Require Import piu_mu_criterion.
Require Import piu_zz_bridge_real.

(* ==== Section 1. Criterion data pins (kappa, sigma, tau) ==== *)

(* Exponent data for the linear-form criterion piu_mu_criterion.  Taking
   sigma = 7 * tau keeps the criterion exponent 1 + sigma/tau equal to 8
   exactly, so q^(sigma+tau) = (q^8)^tau and every power in the criterion
   conclusion stays in the integer-exponent domain.  Taking kappa such
   that 2*kappa*c0 = 1 makes the criterion constant piu_mu_c0 = 1/(2*kappa)
   equal to c0 = 1/71663616. *)
Definition piu_zz_mu_tau : nat := 2%nat.
Definition piu_zz_mu_sigma : nat := 14%nat.
Definition piu_zz_mu_kappa : Q := (35831808 # 1)%Q.

Lemma piu_zz_mu_tau_ge1 : piu_mu_NleT 1 piu_zz_mu_tau.
Proof. apply piu_mu_NleT_i. unfold piu_zz_mu_tau. lia. Qed.

Lemma piu_zz_mu_sigma_seven_tau : piu_zz_mu_sigma = (7 * piu_zz_mu_tau)%nat.
Proof. reflexivity. Qed.

(* 2 * kappa * c0 == 1 over Q: the kappa/c0 pairing of the criterion. *)
Example piu_zz_mu_kappa_c0_bool :
  Qeq_bool ((2 # 1) * (piu_zz_mu_kappa * piu_zz_c0_criterion)%Q)%Q
           (1 # 1)%Q = true.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_mu_kappa_c0 :
  QeqT ((2 # 1) * (piu_zz_mu_kappa * piu_zz_c0_criterion)%Q)%Q (1 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ==== Section 2. Cancellation of the tau-th power on the positive domain ==== *)

(* On the positive rationals the t-th power map (integer exponent over the
   nat scale) is order-reflecting, so a power-form inequality x^t <= y^t
   unwinds to x <= y.  This is the Q-layer step that converts tau-power
   conclusions of piu_mu_criterion into first-power bounds. *)
Lemma piu_zz_mu_qpow_inject : forall (t : nat) (x y : Q),
  (1 <= t)%nat -> (0 < x)%Q -> (0 < y)%Q ->
  QleT' (Qpower x (Z.of_nat t)) (Qpower y (Z.of_nat t)) -> QleT' x y.
Proof.
  intros t. induction t as [|t IH]; intros x y Ht Hx Hy Hle.
  - exfalso. lia.
  - pose proof (QleT'_to_Qle _ _ Hle) as HleQ.
    apply Qle_to_QleT'.
    destruct (Qlt_le_dec x y) as [Hlt | Hge].
    + apply Qlt_le_weak. exact Hlt.
    + destruct (Qlt_le_dec y x) as [Hylt | Hyle].
      * (* y < x would force y^(Datatypes.S t) < x^(Datatypes.S t), contradicting the premise. *)
        exfalso.
        assert (Hplus : (Z.of_nat (Datatypes.S t) = 1 + Z.of_nat t)%Z) by lia.
        assert (Hyl1 : (Qpower y (Z.of_nat (Datatypes.S t))
                        == y * Qpower y (Z.of_nat t))%Q).
        { rewrite Hplus at 1. apply Qpower_plus.
          intro H0. rewrite H0 in Hy. lra. }
        assert (Hxl1 : (Qpower x (Z.of_nat (Datatypes.S t))
                        == x * Qpower x (Z.of_nat t))%Q).
        { rewrite Hplus at 1. apply Qpower_plus.
          intro H0. rewrite H0 in Hx. lra. }
        assert (Hs1 : (Qpower y (Z.of_nat t) <= Qpower x (Z.of_nat t))%Q).
        { destruct (Nat.eq_dec t 0%nat) as [Ht0 | Htpos].
          - rewrite Ht0. change (Z.of_nat 0) with 0%Z.
            rewrite !Qpower_0_r. apply Qle_refl.
          - assert (Htz : (0 < t)%nat) by lia.
            assert (Hz1 : (1 <= Z.of_nat t)%Z) by lia.
            destruct (piu_mu_pow_ge x y (Z.of_nat t) Hy
                        (Qlt_le_weak y x Hylt) Hz1) as [Hw]. exact Hw. }
        assert (Hs2 : (y * Qpower y (Z.of_nat t)
                       < x * Qpower y (Z.of_nat t))%Q)
          by (apply Qmult_lt_compat_r; [apply Qpower_0_lt; exact Hy | exact Hylt]).
        assert (Hstrict : (Qpower y (Z.of_nat (Datatypes.S t))
                           < Qpower x (Z.of_nat (Datatypes.S t)))%Q).
        { rewrite Hyl1, Hxl1.
          apply (Qlt_le_trans _ (x * Qpower y (Z.of_nat t)) _).
          - exact Hs2.
          - rewrite (Qmult_comm x (Qpower y (Z.of_nat t))).
            rewrite (Qmult_comm x (Qpower x (Z.of_nat t))).
            apply Qmult_le_compat_r. exact Hs1. lra. }
        lra.
      * exact Hyle.
Qed.

(* ==== Section 3. Rate-form certificate from a pointwise distance certificate ==== *)

(** The pointwise distance certificate lw1m_dist_pt q (d + 2e), tightened
    by the transport margin e of leibsep_metric_pi_transport, yields the
    rate-form certificate real_lt (real_const d) (pi distance q): the
    constant threshold d sits below the Leibniz-sequence distance from
    index max N Nr on, with slack e on both the transport error and the
    tail bound. *)
Theorem piu_zz_realcert_of_distpt : forall (q d e : Q),
  QltT 0 e ->
  lw1m_dist_pt q ((d + (2 # 1) * e)%Q) ->
  real_lt (real_const d) (real_metric real_pi_geom (real_const q)).
Proof.
  intros q d e He [N HN].
  destruct (leibsep_metric_pi_transport q e He) as [Nr HNr].
  exists e. split.
  - exact He.
  - exists (Nat.max N Nr). intros k Hk.
    assert (HkN : NatLe N k).
    { apply NatLe_lift.
      pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
      apply (Nat.le_trans N (Nat.max N Nr) k (Nat.le_max_l N Nr) Hmax). }
    assert (HkNr : NatLe Nr k).
    { apply NatLe_lift.
      pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
      apply (Nat.le_trans Nr (Nat.max N Nr) k (Nat.le_max_r N Nr) Hmax). }
    pose proof (HN k HkN) as Hlow.
    pose proof (HNr k HkNr) as Htr.
    cbn [projT1 real_const].
    pose proof (QltT'_to_Qlt _ _ Hlow) as HlowQ.
    pose proof (QltT_to_Qlt _ _ Htr) as HtrQ.
    pose proof (leibsep_qabs_low _ _ HtrQ) as Hneg.
    apply Qlt_to_QltT.
    set (P := projT1 (real_metric real_pi_geom (real_const q)) k) in *.
    set (X := Qabs ((lw0m_xL k - q)%Q)) in *.
    lra.
Qed.

(** The exact rate-form interface of the v2 rate-slot bridge, expressed as
    a carrier-form statement: a pointwise distance certificate at the
    doubled threshold (ck_alpha c0 8 q + 2e) with margin e delivers the
    rate-face certificate real_lt (real_const (ck_alpha c0 8 q))
    (pi distance q). *)
Theorem piu_zz_Hmu_rateslot_of_distpt : forall q : Q, (0 < q)%Q ->
  sigT (fun ee : Q => And (QltT 0 ee)
    (lw1m_dist_pt q ((piu1932_ck_alpha piu_zz_c0_criterion 8 q
                      + (2 # 1) * ee)%Q))) ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros q Hq [ee [He Hdist]].
  exact (piu_zz_realcert_of_distpt q
          (piu1932_ck_alpha piu_zz_c0_criterion 8 q) ee He Hdist).
Qed.

(* ==== Section 4. Audit ==== *)

Print Assumptions piu_zz_mu_tau_ge1.
Print Assumptions piu_zz_mu_sigma_seven_tau.
Print Assumptions piu_zz_mu_kappa_c0.
Print Assumptions piu_zz_mu_qpow_inject.
Print Assumptions piu_zz_realcert_of_distpt.
Print Assumptions piu_zz_Hmu_rateslot_of_distpt.

(* Data-level extraction check: the named values and Set-carried
   statements compile to OCaml with no Obj.magic. *)
Separate Extraction piu_zz_mu_kappa piu_zz_mu_sigma piu_zz_mu_tau
  piu_zz_mu_kappa_c0 piu_zz_mu_qpow_inject
  piu_zz_realcert_of_distpt piu_zz_Hmu_rateslot_of_distpt.
