(* ================================================================== *)
(* piu1930_domface_negative.v                                          *)
(* 使命 (Mission): band-parameterized monotone mismatch theorem against *)
(*   the supply chain behind the uniform domination premise: for every *)
(*   reduced band point p/q in [35/12, 41/12] and multiplier m >=      *)
(*   m0(q), the raw supply order n0 = 20*(q*m+1)+23 is linear in m     *)
(*   while the reduced height h(pm/qm) = h(p/q) is fixed, so no fixed  *)
(*   (B, c0) budget slot over the family is inhabitable. Negation      *)
(*   targets the platform supply-chain proof ONLY - not a claim that   *)
(*   pi is not badly approximable and not a weakening of effective     *)
(*   mu(pi) <= 2; no implication with the universal form (open).       *)
(* 依赖 (Dependencies): S01_BaseRing S02_CauchyComplete LW1PiMeasure   *)
(*   leibsep_nsel_h_coupling leibsep_band_domain leibsep_band_ck_assembly; *)
(*   Stdlib QArith (Qcanon, Qreduction) ZArith Arith Lia.              *)
(* 对标 (References): LW1PiMeasure lw1m_dom_face and lw1m_dist_face;   *)
(*   leibsep_nsel_h_coupling piu1864_nsel_qden and piu1864_nsel_height;*)
(*   leibsep_band_ck_assembly piu1872_valve_den and piu1880_valve_qchain*)
(*   piu1880_valve_up_height_from_Kcap; tlw1459_fold tlw1459_fold_closed. *)
(* 构造性 (Constructivity): statement face fully Set-carried (Id/NatLe/ *)
(*   sigT/And/QltT/Not := A -> Empty_set); zero Prop statements; the   *)
(*   two negation theorems are proof-only faces outside the extraction *)
(*   value domain; the negation inside each slot fires on its supply   *)
(*   component; constructive Prop derivations confined to proof bodies *)
(*   with lia on auxiliary linear steps and ring on one Z product step *)
(*   (declared here); definitions Defined; no unproved assumptions, no *)
(*   abandoned proofs (Print Assumptions Closed on all statements).    *)
(* 编译配方 (Build): coqc -native-compiler no -q -Q <vo tree> "" -Q <vo tree>/Local Local -Q <dir> "" piu1930_domface_negative.v *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import QArith.Qcanon QArith.Qreduction.
From Stdlib Require Import Arith.Arith Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW1PiMeasure.
Require Import leibsep_nsel_h_coupling.
Require Import leibsep_band_domain.
Require Import leibsep_band_ck_assembly.

(* ==== Section 1. Band family and budget coordinates ==== *)

(* Set-level band membership: band endpoints only through QltT. *)
Definition piu1930_in_band (x : Q) : Set :=
  And (QltT piu1866_band_lo x) (QltT x piu1866_band_hi).

(* Reducedness premise on the point p/q: the true domain of the       *)
(* domination premise is reduced in-band points. *)
Definition piu1930_reduced (p : Z) (q : positive) : Set :=
  Id (Z.gcd p (Z.pos q)) 1%Z.

(* Unreduced family point: (p*m)/(q*m). *)
Definition piu1930_pt (p : Z) (q : positive) (m : nat) : Q :=
  ((p * Z.of_nat m) # (q * Pos.of_nat m)).

(* Explicit threshold m0(q) = 4*q + 2. *)
Definition piu1930_m0 (q : positive) : nat := (4 * Pos.to_nat q + 2)%nat.

(* Raw-representation supply order: the n_sel closed form evaluated   *)
(* on the unreduced point (no Qred normalization on the denominator). *)
Definition piu1930_supply_order (x : Q) : nat := piu1864_nsel x.

(* Demand side: the valve factorial index 2*n_sel+2 anchored at the   *)
(* reduced height (the piu1872_valve_den factorial coordinate). *)
Definition piu1930_demand_index (p : Z) (q : positive) : nat :=
  (2 * piu1864_nsel (Qred (p # q)) + 2)%nat.

(* Set-level transports between the project Id face and Leibniz eq. *)
Definition piu1930_id_of_eq {A : Set} (x y : A) (H : x = y) : Id x y :=
  match H in _ = y' return Id x y' with
  | eq_refl => id_refl
  end.

Definition piu1930_eq_of_id {A : Set} (x y : A) (H : Id x y) : x = y :=
  match H in Id _ y' return x = y' with
  | id_refl => eq_refl
  end.

(* ==== Section 2. Micro arithmetic helpers (nat and Z casts) ==== *)

Lemma piu1930_zpos_pos_of_nat : forall m : nat,
  (1 <= m)%nat -> Z.pos (Pos.of_nat m) = Z.of_nat m.
Proof.
  induction m as [|m' IH]; intro Hm.
  - lia.
  - destruct m' as [|m''].
    + reflexivity.
    + change (Pos.of_nat (Datatypes.S (Datatypes.S m'')))
        with (Pos.succ (Pos.of_nat (Datatypes.S m''))).
      rewrite Pos2Z.inj_succ. rewrite IH by lia.
      symmetry. apply Nat2Z.inj_succ.
Qed.

Lemma piu1930_postonat_pos_of_nat : forall m : nat,
  (1 <= m)%nat -> Pos.to_nat (Pos.of_nat m) = m.
Proof.
  induction m as [|m' IH]; intro Hm.
  - lia.
  - destruct m' as [|m''].
    + reflexivity.
    + change (Pos.of_nat (Datatypes.S (Datatypes.S m'')))
        with (Pos.succ (Pos.of_nat (Datatypes.S m''))).
      rewrite Pos2Nat.inj_succ. rewrite IH by lia. reflexivity.
Qed.

Lemma piu1930_nat_le_mul_left : forall a b : nat,
  (1 <= b)%nat -> (a <= b * a)%nat.
Proof.
  intros a b Hb. induction Hb as [|b' IH].
  - rewrite Nat.mul_1_l. lia.
  - rewrite Nat.mul_succ_l. lia.
Qed.

Lemma piu1930_reduced_eq : forall (p : Z) (q : positive),
  piu1930_reduced p q -> Z.gcd p (Z.pos q) = 1%Z.
Proof.
  intros p q H. destruct H. reflexivity.
Qed.

(* The family point and the base point carry the same rational value. *)
Lemma piu1930_pt_value : forall (p : Z) (q : positive) (m : nat),
  (1 <= m)%nat -> piu1930_pt p q m == (p # q).
Proof.
  intros p q m Hm. unfold piu1930_pt, Qeq. cbn.
  rewrite Pos2Z.inj_mul. rewrite piu1930_zpos_pos_of_nat by exact Hm. ring.
Qed.

(* ==== Section 3. Height invariance: the demand side is fixed ==== *)

(* Reduced height is invariant under unreduced multiplication. *)
Lemma piu1930_height_invariance : forall (p : Z) (q : positive) (m : nat),
  (1 <= m)%nat ->
  Id (lw1m_height (piu1930_pt p q m)) (lw1m_height (p # q)).
Proof.
  intros p q m Hm. apply piu1930_id_of_eq. unfold lw1m_height.
  do 3 f_equal. apply Qred_complete. apply piu1930_pt_value. exact Hm.
Qed.

(* Raw denominator height of the family point: 1 + q*m. *)
Lemma piu1930_raw_height_pt : forall (p : Z) (q : positive) (m : nat),
  (1 <= m)%nat ->
  Id (Datatypes.S (Pos.to_nat (Qden (piu1930_pt p q m))))
     (Pos.to_nat q * m + 1)%nat.
Proof.
  intros p q m Hm. apply piu1930_id_of_eq. unfold piu1930_pt.
  cbn [Qden]. rewrite Pos2Nat.inj_mul.
  rewrite piu1930_postonat_pos_of_nat by exact Hm. lia.
Qed.

(* ==== Section 4. Supply closed form: 20*(q*m+1)+23, linear in m ==== *)

Lemma piu1930_supply_qden : forall x : Q,
  piu1930_supply_order x = (20 * Datatypes.S (Pos.to_nat (Qden x)) + 23)%nat.
Proof.
  intro x. unfold piu1930_supply_order. exact (piu1864_nsel_qden x).
Qed.

Lemma piu1930_supply_pt : forall (p : Z) (q : positive) (m : nat),
  (1 <= m)%nat ->
  Id (piu1930_supply_order (piu1930_pt p q m))
     (20 * (Pos.to_nat q * m + 1) + 23)%nat.
Proof.
  intros p q m Hm. apply piu1930_id_of_eq.
  rewrite piu1930_supply_qden.
  pose proof (piu1930_eq_of_id _ _ (piu1930_raw_height_pt p q m Hm)) as Hraw.
  rewrite Hraw. reflexivity.
Qed.

(* Monotone limb: the supply order is nondecreasing along the family. *)
Lemma piu1930_supply_mono : forall (p : Z) (q : positive) (m1 m2 : nat),
  (1 <= m1)%nat -> (m1 <= m2)%nat ->
  NatLe (piu1930_supply_order (piu1930_pt p q m1))
        (piu1930_supply_order (piu1930_pt p q m2)).
Proof.
  intros p q m1 m2 Hm1 Hm12. apply NatLe_lift.
  pose proof (piu1930_eq_of_id _ _ (piu1930_supply_pt p q m1 Hm1)) as H1.
  pose proof (piu1930_eq_of_id _ _
    (piu1930_supply_pt p q m2 ltac:(lia))) as H2.
  rewrite H1, H2.
  assert (Hmono : (Pos.to_nat q * m1 <= Pos.to_nat q * m2)%nat)
    by (apply Nat.mul_le_mono_l; exact Hm12).
  lia.
Qed.

(* ==== Section 5. Divergence: supply exceeds the demand index ==== *)

(* Demand index in reduced coordinates: 40*h+48 with h the reduced     *)
(* height (no reducedness needed for this identity). *)
Lemma piu1930_demand_index_face : forall (p : Z) (q : positive),
  Id (piu1930_demand_index p q) (40 * lw1m_height (p # q) + 48)%nat.
Proof.
  intros p q. apply piu1930_id_of_eq. unfold piu1930_demand_index.
  rewrite piu1864_nsel_height. lia.
Qed.

(* Reduced base point: the reduced height is 1 + q. *)
Lemma piu1930_height_reduced : forall (p : Z) (q : positive),
  piu1930_reduced p q ->
  Id (lw1m_height (p # q)) (Datatypes.S (Pos.to_nat q))%nat.
Proof.
  intros p q Hred. apply piu1930_id_of_eq. unfold lw1m_height.
  f_equal. f_equal.
  rewrite (Qred_identity (p # q)).
  - reflexivity.
  - cbn. exact (piu1930_reduced_eq p q Hred).
Qed.

(* Strict divergence: for m >= m0(q) the raw supply order exceeds the  *)
(* reduced-coordinate demand index 40*h+48. *)
Lemma piu1930_divergence : forall (p : Z) (q : positive) (m : nat),
  (1 <= m)%nat -> piu1930_reduced p q -> (piu1930_m0 q <= m)%nat ->
  Id (Nat.ltb (piu1930_demand_index p q)
              (piu1930_supply_order (piu1930_pt p q m))) true.
Proof.
  intros p q m Hm Hred Hm0.
  pose proof (Pos2Nat.is_pos q) as Hqpos. cbn in Hqpos.
  pose proof (piu1930_eq_of_id _ _ (piu1930_height_reduced p q Hred)) as Hhr.
  pose proof (piu1930_eq_of_id _ _ (piu1930_demand_index_face p q)) as Hdf.
  pose proof (piu1930_eq_of_id _ _ (piu1930_supply_pt p q m Hm)) as Hsp.
  pose proof (piu1930_nat_le_mul_left m (Pos.to_nat q) Hqpos) as Hqm.
  apply piu1930_id_of_eq. apply Nat.ltb_lt.
  unfold piu1930_m0 in Hm0. rewrite Hdf, Hhr, Hsp. lia.
Qed.

(* ==== Section 6. The band-parameterized mismatch theorem (main) ==== *)

(* For every reduced band point and every m >= m0: height fixed,       *)
(* supply affine in m, supply strictly above the demand index. The     *)
(* witness domain spans the whole family, not a single point.          *)
Theorem piu1930_band_mismatch :
  forall (p : Z) (q : positive),
    piu1930_reduced p q ->
    piu1930_in_band (p # q) ->
    sigT (fun m0 : nat =>
      And (Id m0 (piu1930_m0 q))
          (forall m : nat, NatLe (piu1930_m0 q) m ->
            And (Id (lw1m_height (piu1930_pt p q m)) (lw1m_height (p # q)))
                (And (Id (piu1930_supply_order (piu1930_pt p q m))
                           (20 * (Pos.to_nat q * m + 1) + 23)%nat)
                     (Id (Nat.ltb (piu1930_demand_index p q)
                                  (piu1930_supply_order (piu1930_pt p q m)))
                         true)))).
Proof.
  intros p q Hred Hband.
  exists (piu1930_m0 q). split.
  - apply id_refl.
  - intros m Hm. pose proof (NatLe_drop _ _ Hm) as Hmn.
    split.
    + apply piu1930_height_invariance.
      pose proof Hmn as Hx. unfold piu1930_m0 in Hx. lia.
    + split.
      * apply piu1930_supply_pt.
        pose proof Hmn as Hy. unfold piu1930_m0 in Hy. lia.
      * apply piu1930_divergence;
          [ pose proof Hmn as Hx; unfold piu1930_m0 in Hx; lia
          | exact Hred | exact Hmn ].
Qed.

(* ==== Section 7. Witness point 16/5 ==== *)

Lemma piu1930_wit16_5_band : piu1930_in_band ((16 # 5)%Q).
Proof.
  unfold piu1930_in_band, And. split; vm_compute; reflexivity.
Qed.

Lemma piu1930_reduced_16_5 : piu1930_reduced 16%Z 5%positive.
Proof. vm_compute. reflexivity. Qed.

Lemma piu1930_wit16_5_m0 : Id (piu1930_m0 5%positive) 22%nat.
Proof. vm_compute. reflexivity. Qed.

(* The multiplier m = 10^6 lies inside the parameterized family of the *)
(* band point 16/5 (threshold 22). *)
Lemma piu1930_wit16_5_in_family : NatLe (piu1930_m0 5%positive) (1000 * 1000)%nat.
Proof.
  apply NatLe_lift.
  assert (Hm0 : (piu1930_m0 5%positive = 22)%nat)
    by (unfold piu1930_m0; vm_compute; reflexivity).
  rewrite Hm0. lia.
Qed.

(* ==== Section 8. The domination budget slot and its absence ==== *)

(* The platform slot over one family: a fixed exponent budget B that   *)
(* anchors the demand index and absorbs every family member's supply   *)
(* order, together with a fixed positive constant c0 whose reduced-    *)
(* height distance-rate certificate holds over the whole family. *)
Definition piu1930_dom_slot (p : Z) (q : positive) : Set :=
  sigT (fun B : nat =>
    And (NatLe (piu1930_demand_index p q) B)
        (sigT (fun c0 : Q =>
          And (QltT 0 c0)
              (forall m : nat, NatLe 1 m ->
                And (NatLe (piu1930_supply_order (piu1930_pt p q m)) B)
                    (lw1m_dist_face (piu1930_pt p q m) 2 c0))))).

(* Absence over one family: the absorbed supply order would exceed the *)
(* budget for multipliers past the threshold, so the slot is empty.    *)
Theorem piu1930_family_slot_absent :
  forall (p : Z) (q : positive),
    piu1930_reduced p q -> Not (piu1930_dom_slot p q).
Proof.
  intros p q Hred [B [Hdem [c0 [Hc0 Hrate]]]].
  pose proof (Pos2Nat.is_pos q) as Hqpos. cbn in Hqpos.
  assert (Hm1 : (1 <= piu1930_m0 q + Datatypes.S B)%nat)
    by (unfold piu1930_m0; lia).
  destruct (Hrate (piu1930_m0 q + Datatypes.S B)%nat
              (NatLe_lift 1 _ Hm1)) as [HsB _].
  pose proof (NatLe_drop _ _ HsB) as HsB'.
  pose proof (piu1930_eq_of_id _ _ (piu1930_supply_pt p q
              (piu1930_m0 q + Datatypes.S B)%nat Hm1)) as Hsp.
  rewrite Hsp in HsB'.
  pose proof (piu1930_nat_le_mul_left (piu1930_m0 q + Datatypes.S B)
              (Pos.to_nat q) Hqpos) as Hqm.
  assert (Hstep : ((piu1930_m0 q + Datatypes.S B) + 1
                   <= Pos.to_nat q * (piu1930_m0 q + Datatypes.S B) + 1)%nat)
    by (apply Nat.add_le_mono_r; exact Hqm).
  assert (Hmul : (20 * ((piu1930_m0 q + Datatypes.S B) + 1)
                  <= 20 * (Pos.to_nat q * (piu1930_m0 q + Datatypes.S B) + 1))%nat)
    by (apply Nat.mul_le_mono_l; exact Hstep).
  lia.
Qed.

(* The uniform slot over the whole band: one budget B and one constant  *)
(* c0 covering every reduced band point and every family member. *)
Definition piu1930_unif_band_slot : Set :=
  sigT (fun B : nat =>
    sigT (fun c0 : Q =>
      And (QltT 0 c0)
          (forall (p : Z) (q : positive), piu1930_in_band (p # q) ->
            forall m : nat, NatLe 1 m ->
              And (NatLe (piu1930_demand_index p q) B)
                  (And (NatLe (piu1930_supply_order (piu1930_pt p q m)) B)
                       (lw1m_dist_face (piu1930_pt p q m) 2 c0))))).

(* Absence over the whole band: fires at the witness point 16/5 with a *)
(* multiplier past the threshold; the uniform slot is empty. *)
Theorem piu1930_unif_slot_absent : Not piu1930_unif_band_slot.
Proof.
  intros [B [c0 [Hc0 Hall]]].
  assert (Hm1 : (1 <= piu1930_m0 5%positive + Datatypes.S B)%nat)
    by (unfold piu1930_m0; lia).
  destruct (Hall 16%Z 5%positive piu1930_wit16_5_band
              (piu1930_m0 5%positive + Datatypes.S B)%nat
              (NatLe_lift 1 _ Hm1))
    as [Hdem16 [HsB16 _]].
  pose proof (NatLe_drop _ _ HsB16) as HsB.
  pose proof (piu1930_eq_of_id _ _ (piu1930_supply_pt 16%Z 5%positive
              (piu1930_m0 5%positive + Datatypes.S B)%nat Hm1)) as Hsp.
  rewrite Hsp in HsB.
  assert (Hqm : (piu1930_m0 5%positive + Datatypes.S B
                 <= Pos.to_nat 5 * (piu1930_m0 5%positive + Datatypes.S B))%nat)
    by (apply piu1930_nat_le_mul_left; unfold piu1930_m0; lia).
  assert (Hx : (piu1930_m0 5%positive = 22)%nat)
    by (unfold piu1930_m0; vm_compute; reflexivity).
  assert (Ht : (Pos.to_nat 5%positive = 5)%nat) by (vm_compute; reflexivity).
  rewrite Ht, Hx in HsB. rewrite Ht, Hx in Hqm.
  lia.
Qed.

(* ==== Section 9. Assumption audit and extraction ==== *)

Check piu1930_in_band.
Check piu1930_reduced.
Check piu1930_pt.
Check piu1930_m0.
Check piu1930_supply_order.
Check piu1930_demand_index.
Check piu1930_height_invariance.
Check piu1930_supply_pt.
Check piu1930_supply_mono.
Check piu1930_divergence.
Check piu1930_band_mismatch.
Check piu1930_dom_slot.
Check piu1930_family_slot_absent.
Check piu1930_unif_band_slot.
Check piu1930_unif_slot_absent.
Check piu1930_wit16_5_band.
Check piu1930_reduced_16_5.
Check piu1930_wit16_5_m0.
Check piu1930_wit16_5_in_family.

Print Assumptions piu1930_height_invariance.
Print Assumptions piu1930_supply_pt.
Print Assumptions piu1930_supply_mono.
Print Assumptions piu1930_divergence.
Print Assumptions piu1930_band_mismatch.
Print Assumptions piu1930_family_slot_absent.
Print Assumptions piu1930_unif_slot_absent.
Print Assumptions piu1930_wit16_5_band.
Print Assumptions piu1930_reduced_16_5.
Print Assumptions piu1930_wit16_5_m0.
Print Assumptions piu1930_wit16_5_in_family.

Set Extraction Output Directory "D:/ComplexAnalysis/attn/kb28_work_20261026/extract".
Separate Extraction piu1930_in_band piu1930_reduced piu1930_pt piu1930_m0
  piu1930_supply_order piu1930_demand_index piu1930_id_of_eq piu1930_eq_of_id
  piu1930_dom_slot piu1930_unif_band_slot piu1930_band_mismatch
  piu1930_height_invariance piu1930_supply_pt piu1930_supply_mono
  piu1930_divergence piu1930_wit16_5_band piu1930_reduced_16_5
  piu1930_wit16_5_m0 piu1930_wit16_5_in_family.
