(* ================================================================== *)
(* ucreal_bridge.v —— 库构造实数到标准库 CReal 的适配层                *)
(*                                                                    *)
(* 使命：把库构造实数（显式尾部模量的柯西序列 nat -> Q，               *)
(*       Set 值见证）转换为 Rocq 标准库 ConstructiveCauchyReals.CReal  *)
(*       （Z 索引序列，内嵌收敛模量 2^k 与显式一致界）；经单调         *)
(*       模量包络与负指标绝对值取样传输柯西性质；并将 pi 无理          *)
(*       分离定理以 CReal 形复述。                                     *)
(* 依赖：标准库 QArith、Qpower、Qabs、Lia、Lqa、QExtra、               *)
(*       ConstructiveCauchyReals；库内 S01_BaseRing、                  *)
(*       S02_CauchyComplete、S03_QExp、S10_KVQuantTrig、               *)
(*       LW0LeibSeparation。                                           *)
(* 对标：Stdlib.Reals.Cauchy.ConstructiveCauchyReals                   *)
(* 构造性注记：语句全 Set 层；零公理、零承认件、零经典逻辑；见证       *)
(*       全部显式构造（收敛模量经单调包络自库侧柯西见证构造；          *)
(*       一致界指数经 Qbound_ltabs_ZExp2 构造；分离见证指标经          *)
(*       Qlowbound_ltabs_ZExp2 构造）。                                *)
(* 编译配方：coqc -q -Q . "" ucreal_bridge.v                           *)
(* ================================================================== *)

From Stdlib Require Import QArith.
From Stdlib Require Import Qpower.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Setoid.
From Stdlib Require Import QExtra.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import LW0LeibSeparation.
Require Import LW0MLicBridge.

(* ================================================================== *)
(* Section 1. Rational and integer arithmetic auxiliaries.           *)
(* ================================================================== *)

Lemma ucreal_qlt_0_1 : (0 < 1)%Q.
Proof. unfold Qlt, Qnum, Qden. lia. Qed.

(* The probe sequence eps j = (1#2)^j plays the role of 2^(-j). *)

Definition ucreal_eps (j : nat) : Q := ((1 # 2) ^ Z.of_nat j)%Q.

Lemma ucreal_half_pow_pos : forall j : nat, QltT 0 (ucreal_eps j).
Proof.
  intros j. apply Qlt_to_QltT. apply Qpower_0_lt. apply ucreal_qlt_0_1.
Qed.

Lemma ucreal_half_pow_le1 : forall j : nat, (ucreal_eps j <= 1)%Q.
Proof.
  unfold ucreal_eps.
  induction j as [|j IH].
    - cbn. apply Qle_refl.
    - assert (Hsplit : (Z.of_nat (Datatypes.S j) = Z.of_nat j + 1)%Z) by (rewrite Nat2Z.inj_succ; lia).
      rewrite Hsplit.
      assert (Hpp : ((1#2)^(Z.of_nat j + 1) == (1#2)^(Z.of_nat j) * (1#2))%Q)
        by (apply Qpower_plus; intro Hd; discriminate Hd).
      apply (proj2 (Qle_comp _ _ Hpp 1%Q 1%Q (Qeq_refl 1%Q))).
      cbn. lra.
Qed.

Lemma ucreal_half_pow_anti : forall j1 j2 : nat,
  (j1 <= j2)%nat -> (ucreal_eps j2 <= ucreal_eps j1)%Q.
Proof.
  unfold ucreal_eps. intros j1 j2 H.
    replace j2 with (j1 + (j2 - j1))%nat by lia.
    assert (Hadd : (Z.of_nat (j1 + (j2 - j1)) = Z.of_nat j1 + Z.of_nat (j2 - j1))%Z)
      by (rewrite Nat2Z.inj_add; reflexivity).
    rewrite Hadd.
    assert (Hpp : ((1#2)^(Z.of_nat j1 + Z.of_nat (j2 - j1))
                   == (1#2)^(Z.of_nat j1) * (1#2)^(Z.of_nat (j2 - j1)))%Q)
      by (apply Qpower_plus; intro Hd; discriminate Hd).
    apply (proj2 (Qle_comp _ _ Hpp ((1#2)^(Z.of_nat j1)) ((1#2)^(Z.of_nat j1)) (Qeq_refl _))).
    assert (Hapos : (0 <= (1#2)^(Z.of_nat j1))%Q)
      by (apply Qlt_le_weak; apply Qpower_0_lt; unfold Qlt, Qnum, Qden; lia).
    assert (HM : ((1#2)^(Z.of_nat (j2 - j1)) * (1#2)^(Z.of_nat j1)
                  <= 1 * (1#2)^(Z.of_nat j1))%Q).
    { apply (Qmult_le_compat_r ((1#2)^(Z.of_nat (j2 - j1))) 1 ((1#2)^(Z.of_nat j1))).
      - apply ucreal_half_pow_le1.
      - exact Hapos. }
    apply (proj1 (Qle_comp _ _ (Qmult_comm _ _) _ _ (Qmult_1_l _))).
    exact HM.
Qed.

Lemma ucreal_pow2_ge1 : forall z : Z, (0 <= z)%Z -> (1 <= 2 ^ z)%Q.
Proof.
  intros z Hz.
    replace z with (Z.of_nat (Z.to_nat z)) by (apply Z2Nat.id; exact Hz).
    generalize (Z.to_nat z) as n. induction n as [|n IH].
    - cbn. apply Qle_refl.
    - assert (Hsplit : (Z.of_nat (Datatypes.S n) = Z.of_nat n + 1)%Z) by (rewrite Nat2Z.inj_succ; lia).
      rewrite Hsplit.
      assert (Hpp : ((2)^(Z.of_nat n + 1) == (2)^(Z.of_nat n) * (2)^(1))%Q)
        by (apply Qpower_plus; intro Hd; discriminate Hd).
      apply (proj2 (Qle_comp _ _ (Qeq_refl 1%Q) _ _ Hpp)).
      cbn. lra.
Qed.

Lemma ucreal_pow2_le_mono : forall z z' : Z,
  (z <= z')%Z -> (2 ^ z <= 2 ^ z')%Q.
Proof.
  intros z z' H.
    replace z' with (z + (z' - z))%Z by lia.
    assert (Hpp : (2^(z + (z' - z)) == 2^z * 2^(z' - z))%Q)
      by (apply Qpower_plus; intro Hd; discriminate Hd).
    apply (proj2 (Qle_comp _ _ (Qeq_refl (2^z)) _ _ Hpp)).
    assert (Hd : (1 <= 2^(z' - z))%Q) by (apply ucreal_pow2_ge1; lia).
    assert (H2 : (0 < 2)%Q) by (unfold Qlt, Qnum, Qden; lia).
    assert (Hp : (0 <= 2^z)%Q) by (apply Qpower_0_le; apply Qlt_le_weak; exact H2).
    pose proof (Qmult_le_compat_r 1 (2^(z' - z)) (2^z) Hd Hp) as HH.
    assert (g1 : (1 * 2^z == 2^z)%Q) by apply Qmult_1_l.
    assert (g2 : (2^(z' - z) * 2^z == 2^z * 2^(z' - z))%Q) by apply Qmult_comm.
    apply (proj1 (Qle_comp _ _ g1 _ _ g2)). exact HH.
Qed.

Lemma ucreal_pow2_neg_eq : forall j : nat,
  (2 ^ Z.opp (Z.of_nat j) == ucreal_eps j)%Q.
Proof.
  unfold ucreal_eps.
  induction j as [|j IH].
    - cbn. apply Qeq_refl.
    - assert (Hsplit1 : (Z.opp (Z.of_nat (Datatypes.S j)) = Z.opp (Z.of_nat j) + (-1))%Z)
        by (rewrite Nat2Z.inj_succ; lia).
      rewrite Hsplit1.
      assert (Hsplit2 : (Z.of_nat (Datatypes.S j) = Z.of_nat j + 1)%Z) by (rewrite Nat2Z.inj_succ; lia).
      rewrite Hsplit2.
      assert (Hnz2 : ~ (2 == 0)%Q) by (intro Hd; discriminate Hd).
      assert (Hnz12 : ~ ((1#2) == 0)%Q) by (intro Hd; discriminate Hd).
      assert (Hstep : (2 ^ (Z.opp (Z.of_nat j) + (-1)) == 2 ^ Z.opp (Z.of_nat j) * 2 ^ (-1))%Q)
        by (apply Qpower_plus; exact Hnz2).
      assert (Hr : ((1#2) ^ (Z.of_nat j + 1) == (1#2) ^ Z.of_nat j * (1#2) ^ 1)%Q)
        by (apply Qpower_plus; exact Hnz12).
      cbn in Hr.
      assert (H2 : (2 ^ (-1) == (1#2))%Q) by reflexivity.
      apply (Qeq_trans _ _ _ Hstep).
      apply (Qeq_trans _ _ _ (Qmult_comp _ _ IH _ _ H2)).
      apply Qeq_sym. exact Hr.
Qed.

(* ================================================================== *)
(* Section 2. Monotone modulus envelope built from the library       *)
(* Cauchy witness.                                                   *)
(* ================================================================== *)

Fixpoint ucreal_env (N0 : nat -> nat) (j : nat) : nat :=
  match j with
  | O => N0 O
  | Datatypes.S j' => Nat.max (ucreal_env N0 j') (N0 (Datatypes.S j'))
  end.

Lemma ucreal_env_ge_self : forall (N0 : nat -> nat) (j : nat), (N0 j <= ucreal_env N0 j)%nat.
Proof.
  intros N0 j. destruct j as [|j]; simpl; lia.
Qed.

Lemma ucreal_env_ge_head : forall (N0 : nat -> nat) (j : nat), (N0 O <= ucreal_env N0 j)%nat.
Proof.
  intros N0 j. induction j as [|j IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma ucreal_env_mono : forall (N0 : nat -> nat) (j1 j2 : nat),
  (j1 <= j2)%nat -> (ucreal_env N0 j1 <= ucreal_env N0 j2)%nat.
Proof.
  intros N0 j1 j2 H. induction H as [|j2 H IH].
  - lia.
  - simpl. lia.
Qed.

Definition ucreal_rawmod (u : Qseq) (cu : cauchy u) (j : nat) : nat :=
  projT1 (cu (ucreal_eps j) (ucreal_half_pow_pos j)).

Definition ucreal_mod (u : Qseq) (cu : cauchy u) (j : nat) : nat :=
  Nat.max (ucreal_env (ucreal_rawmod u cu) j) j.

Lemma ucreal_rawmod_spec : forall (u : Qseq) (cu : cauchy u) (j m n : nat),
  (ucreal_rawmod u cu j <= m)%nat -> (ucreal_rawmod u cu j <= n)%nat ->
  QltT (Qabs (u m - u n)) (ucreal_eps j).
Proof.
  intros u cu j m n Hm Hn.
  exact (projT2 (cu (ucreal_eps j) (ucreal_half_pow_pos j)) m n
          (NatLe_lift _ _ Hm) (NatLe_lift _ _ Hn)).
Qed.

Lemma ucreal_mod_spec : forall (u : Qseq) (cu : cauchy u) (j m n : nat),
  (ucreal_mod u cu j <= m)%nat -> (ucreal_mod u cu j <= n)%nat ->
  QltT (Qabs (u m - u n)) (ucreal_eps j).
Proof.
  intros u cu j m n Hm Hn.
  unfold ucreal_mod in Hm, Hn.
  assert (Hs : (ucreal_rawmod u cu j
                <= ucreal_env (ucreal_rawmod u cu) j)%nat)
    by apply ucreal_env_ge_self.
  apply (ucreal_rawmod_spec u cu j m n); lia.
Qed.

Lemma ucreal_mod_mono : forall (u : Qseq) (cu : cauchy u) (j1 j2 : nat),
  (j1 <= j2)%nat -> (ucreal_mod u cu j1 <= ucreal_mod u cu j2)%nat.
Proof.
  intros u cu j1 j2 H.
  assert (H1 : (ucreal_env (ucreal_rawmod u cu) j1
                <= ucreal_env (ucreal_rawmod u cu) j2)%nat)
    by (apply ucreal_env_mono; exact H).
  unfold ucreal_mod. lia.
Qed.

(* ================================================================== *)
(* Section 3. The conversion Real -> CReal.                          *)
(*                                                                    *)
(* Mirrored indexing: n |-> |n| sends both index ends into the deep  *)
(* tail, so the converted Z-sequence is uniformly close to the limit *)
(* on both ends, as the CReal Cauchy condition requires.             *)
(* ================================================================== *)

Definition ucreal_seq (u : Qseq) (cu : cauchy u) : Z -> Q :=
  fun n : Z => u (ucreal_mod u cu (Z.to_nat (Z.abs n))).

Definition ucreal_bnd (u : Qseq) (cu : cauchy u) : Q :=
  (1 + Qabs (u (ucreal_rawmod u cu 0)))%Q.

Definition ucreal_of_real (x : Real) : CReal.
Proof.
  destruct x as [u cu].
  refine (mkCReal (ucreal_seq u cu) (Qbound_ltabs_ZExp2 (ucreal_bnd u cu)) _ _).
  - (* Cauchy transport *)
    intros k p q Hp Hq. unfold ucreal_seq.
    destruct (Z_le_gt_dec 0 k) as [Hk|Hk].
    + (* k >= 0: unconditional tail bound, then eps jp <= 1 <= 2^k *)
      destruct (Nat.le_gt_cases (Z.to_nat (Z.abs p)) (Z.to_nat (Z.abs q)))
        as [Hle|Hgt].
      * pose proof (ucreal_mod_spec u cu (Z.to_nat (Z.abs p))
            (ucreal_mod u cu (Z.to_nat (Z.abs p)))
            (ucreal_mod u cu (Z.to_nat (Z.abs q)))
            (Nat.le_refl _)
            (ucreal_mod_mono u cu (Z.to_nat (Z.abs p)) (Z.to_nat (Z.abs q)) Hle))
          as Ht.
        apply QltT_to_Qlt in Ht.
        apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.abs p)))).
        -- exact Ht.
        -- apply (Qle_trans _ 1%Q).
           ++ apply ucreal_half_pow_le1.
           ++ apply ucreal_pow2_ge1. exact Hk.
      * pose proof (ucreal_mod_spec u cu (Z.to_nat (Z.abs q))
            (ucreal_mod u cu (Z.to_nat (Z.abs q)))
            (ucreal_mod u cu (Z.to_nat (Z.abs p)))
            (Nat.le_refl _)
            (ucreal_mod_mono u cu (Z.to_nat (Z.abs q)) (Z.to_nat (Z.abs p))
              (Nat.lt_le_incl _ _ Hgt)))
          as Ht.
        apply QltT_to_Qlt in Ht.
        rewrite (Qabs_Qminus (u (ucreal_mod u cu (Z.to_nat (Z.abs p))))
                             (u (ucreal_mod u cu (Z.to_nat (Z.abs q))))).
        apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.abs q)))).
        -- exact Ht.
        -- apply (Qle_trans _ 1%Q).
           ++ apply ucreal_half_pow_le1.
           ++ apply ucreal_pow2_ge1. exact Hk.
    + (* k < 0: |p|,|q| >= |k|, so the eps bound is dominated by eps |k| = 2^k *)
      assert (Habsk : Z.abs k = Z.opp k) by (apply Z.abs_neq; lia).
      assert (Habsp : forall a : Z, (a <= k)%Z -> Z.abs a = Z.opp a)
        by (intros a Ha; apply Z.abs_neq; lia).
      assert (HpJ : (Z.to_nat (Z.opp k) <= Z.to_nat (Z.abs p))%nat).
      { apply Z2Nat.inj_le.
        - lia.
        - apply Z.abs_nonneg.
        - rewrite (Habsp p Hp). lia. }
      assert (HqJ : (Z.to_nat (Z.opp k) <= Z.to_nat (Z.abs q))%nat).
      { apply Z2Nat.inj_le.
        - lia.
        - apply Z.abs_nonneg.
        - rewrite (Habsp q Hq). lia. }
      destruct (Nat.le_gt_cases (Z.to_nat (Z.abs p)) (Z.to_nat (Z.abs q)))
        as [Hle|Hgt].
      * pose proof (ucreal_mod_spec u cu (Z.to_nat (Z.abs p))
            (ucreal_mod u cu (Z.to_nat (Z.abs p)))
            (ucreal_mod u cu (Z.to_nat (Z.abs q)))
            (Nat.le_refl _)
            (ucreal_mod_mono u cu (Z.to_nat (Z.abs p)) (Z.to_nat (Z.abs q)) Hle))
          as Ht.
        apply QltT_to_Qlt in Ht.
        apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.opp k)))).
        -- apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.abs p)))).
           ++ exact Ht.
           ++ apply ucreal_half_pow_anti. lia.
        -- rewrite <- (ucreal_pow2_neg_eq (Z.to_nat (Z.opp k))).
           replace (Z.opp (Z.of_nat (Z.to_nat (Z.opp k)))) with k
             by (rewrite Z2Nat.id by lia; lia).
           apply Qle_refl.
      * pose proof (ucreal_mod_spec u cu (Z.to_nat (Z.abs q))
            (ucreal_mod u cu (Z.to_nat (Z.abs q)))
            (ucreal_mod u cu (Z.to_nat (Z.abs p)))
            (Nat.le_refl _)
            (ucreal_mod_mono u cu (Z.to_nat (Z.abs q)) (Z.to_nat (Z.abs p))
              (Nat.lt_le_incl _ _ Hgt)))
          as Ht.
        apply QltT_to_Qlt in Ht.
        rewrite (Qabs_Qminus (u (ucreal_mod u cu (Z.to_nat (Z.abs p))))
                             (u (ucreal_mod u cu (Z.to_nat (Z.abs q))))).
        apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.opp k)))).
        -- apply (Qlt_le_trans _ (ucreal_eps (Z.to_nat (Z.abs q)))).
           ++ exact Ht.
           ++ apply ucreal_half_pow_anti. lia.
        -- rewrite <- (ucreal_pow2_neg_eq (Z.to_nat (Z.opp k))).
           replace (Z.opp (Z.of_nat (Z.to_nat (Z.opp k)))) with k
             by (rewrite Z2Nat.id by lia; lia).
           apply Qle_refl.
  - (* uniform bound transport *)
    intros k. unfold ucreal_seq. unfold ucreal_bnd.
    assert (Hge : (ucreal_rawmod u cu 0
                   <= ucreal_mod u cu (Z.to_nat (Z.abs k)))%nat).
    { unfold ucreal_mod.
      assert (Hh : (ucreal_rawmod u cu 0
                    <= ucreal_env (ucreal_rawmod u cu)
                         (Z.to_nat (Z.abs k)))%nat)
        by apply ucreal_env_ge_head.
      lia. }
    pose proof (ucreal_rawmod_spec u cu 0
        (ucreal_mod u cu (Z.to_nat (Z.abs k))) (ucreal_rawmod u cu 0)
        Hge (Nat.le_refl _)) as Ht.
    replace (ucreal_eps 0) with 1%Q in Ht by reflexivity.
    apply QltT_to_Qlt in Ht.
    apply Qabs_Qlt_condition in Ht. destruct Ht as [Ht1 Ht2].
    assert (Habsur0 : (- Qabs (u (ucreal_rawmod u cu 0))
                       <= u (ucreal_rawmod u cu 0)
                       <= Qabs (u (ucreal_rawmod u cu 0)))%Q).
    { apply Qabs_Qle_condition. apply Qle_refl. }
    destruct Habsur0 as [Habsur1 Habsur2].
    remember (Qabs (u (ucreal_rawmod u cu 0))) as A eqn:HAdef.
    assert (Hbndpos : (0 <= 1 + A)%Q) by lra.
    assert (Hbndle : (1 + A <= 2 ^ Qbound_ltabs_ZExp2 (1 + A))%Q).
    { pose proof (Qbound_ltabs_ZExp2_spec (1 + A)) as Hspec.
      pose proof (Qlt_le_weak (Qabs (1 + A))
                    (2 ^ Qbound_ltabs_ZExp2 (1 + A)) Hspec) as Hspecle.
      pose proof
        (proj1
           (Qle_comp (Qabs (1 + A)) (1 + A) (Qabs_pos _ Hbndpos)
                     (2 ^ Qbound_ltabs_ZExp2 (1 + A))
                     (2 ^ Qbound_ltabs_ZExp2 (1 + A))
                     (Qeq_refl _)) Hspecle) as Hb.
      exact Hb. }
    apply Qabs_Qlt_condition. split; lra.
Defined.

(* ================================================================== *)
(* Section 4. Compatibility of the library equality/order with the   *)
(* stdlib CReal order (Set-layer statements only).                   *)
(* ================================================================== *)

Lemma ucreal_eq_seq_compat : forall x y : Real,
  real_eq x y ->
  sigT (fun E : Q => And (QltT 0 E)
    (forall n : Z,
       QltT (Qabs (seq (ucreal_of_real x) n - seq (ucreal_of_real y) n)) E)).
Proof.
  intros x y Heq.
  exists 4%Q. split.
  - apply Qlt_to_QltT. apply ucreal_qlt_0_1.
  - intros n.
    assert (H1 : QltT 0 1%Q) by (apply Qlt_to_QltT; apply ucreal_qlt_0_1).
    destruct x as [ux cx]. destruct y as [uy cy].
    destruct (Heq 1%Q H1) as [N HN].
    assert (Hsx : forall n0 : Z,
              seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) ux cx)) n0
              = ux (ucreal_mod ux cx (Z.to_nat (Z.abs n0))))
      by (intros; reflexivity).
    assert (Hsy : forall n0 : Z,
              seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) uy cy)) n0
              = uy (ucreal_mod uy cy (Z.to_nat (Z.abs n0))))
      by (intros; reflexivity).
    rewrite (Hsx n), (Hsy n).
    set (j := Z.to_nat (Z.abs n)) in *.
    set (mx := ucreal_mod ux cx j) in *.
    set (my := ucreal_mod uy cy j) in *.
    set (m := Nat.max (Nat.max mx my) N).
    assert (Hmx : (mx <= m)%nat) by lia.
    assert (Hmy : (my <= m)%nat) by lia.
    assert (HmN : (N <= m)%nat) by lia.
    pose proof (ucreal_mod_spec ux cx j mx m (Nat.le_refl _) Hmx) as Htx.
    pose proof (ucreal_mod_spec uy cy j my m (Nat.le_refl _) Hmy) as Hty.
    pose proof (HN m (NatLe_lift _ _ HmN)) as Hxy.
    cbn [projT1] in Hxy.
    apply QltT_to_Qlt in Htx. apply QltT_to_Qlt in Hty.
    apply QltT_to_Qlt in Hxy.
    apply Qabs_Qlt_condition in Htx. destruct Htx as [Htx1 Htx2].
    apply Qabs_Qlt_condition in Hty. destruct Hty as [Hty1 Hty2].
    apply Qabs_Qlt_condition in Hxy. destruct Hxy as [Hxy1 Hxy2].
    assert (Hepsj : (ucreal_eps j <= 1)%Q) by apply ucreal_half_pow_le1.
    assert (Hdecomp : (ux mx - uy my
                       == (ux mx - ux m) + (ux m - uy m) + (uy m - uy my))%Q)
      by lra.
    apply Qlt_to_QltT.
    apply Qabs_Qlt_condition.
    split; lra.
Qed.

Lemma ucreal_lt_compat : forall x y : Real,
  real_lt x y -> CRealLt (ucreal_of_real x) (ucreal_of_real y).
Proof.
  intros x y Hlt.
  destruct x as [ux cx]. destruct y as [uy cy].
  destruct Hlt as [eps0 [Heps0 [N HN]]].
  assert (H0eps0 : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  assert (Hpos4 : (0 < eps0 * (1 # 4))%Q) by lra.
  assert (Hpos4le : (0 <= eps0 * (1 # 4))%Q) by (apply Qlt_le_weak; exact Hpos4).
  pose proof (Qlowbound_lt_ZExp2_spec (eps0 * (1 # 4)) Hpos4) as Hs0.
  remember (Z.min (Qlowbound_ltabs_ZExp2 (eps0 * (1 # 4)))
                  (Z.opp (Z.of_nat N))) as n0 eqn:Hn0def.
  assert (HNneg : (0 <= Z.of_nat N)%Z) by apply Nat2Z.is_nonneg.
  assert (Hn0le : (n0 <= Qlowbound_ltabs_ZExp2 (eps0 * (1 # 4)))%Z)
    by (rewrite Hn0def; apply Z.le_min_l).
  assert (Hn0neg : (n0 <= 0)%Z).
  { rewrite Hn0def.
    assert (Hr := Z.le_min_r (Qlowbound_ltabs_ZExp2 (eps0 * (1 # 4)))
                             (Z.opp (Z.of_nat N))).
    lia. }
  assert (Habsn0 : Z.abs n0 = Z.opp n0).
  { destruct (Z.eq_dec n0 0) as [Hz|Hz].
    - rewrite Hz. reflexivity.
    - apply Z.abs_neq. lia. }
  remember (Z.to_nat (Z.opp n0)) as j eqn:Hjdef.
  assert (HjN : (N <= j)%nat).
  { rewrite Hjdef. rewrite <- (Nat2Z.id N).
    apply Z2Nat.inj_le.
    - apply Nat2Z.is_nonneg.
    - lia.
    - assert (Hr := Z.le_min_r (Qlowbound_ltabs_ZExp2 (eps0 * (1 # 4)))
                               (Z.opp (Z.of_nat N))).
      lia. }
  assert (Hjn : Z.opp (Z.of_nat j) = n0).
  { rewrite Hjdef. rewrite Z2Nat.id by lia. lia. }
  remember (ucreal_mod ux cx j) as mx eqn:Hmxdef.
  remember (ucreal_mod uy cy j) as my eqn:Hmydef.
  remember (Nat.max mx my) as m eqn:Hmdef.
  assert (Hmx : (mx <= m)%nat) by lia.
  assert (Hmy : (my <= m)%nat) by lia.
  assert (Hjmx : (j <= mx)%nat).
  { rewrite Hmxdef. unfold ucreal_mod. lia. }
  assert (HmN : (N <= m)%nat) by lia.
  pose proof (HN m (NatLe_lift _ _ HmN)) as Hval.
  cbn [projT1] in Hval.
  apply QltT_to_Qlt in Hval.
  assert (Hmux : (ucreal_rawmod ux cx j <= mx)%nat).
  { rewrite Hmxdef. unfold ucreal_mod.
    assert (H1 := ucreal_env_ge_self (ucreal_rawmod ux cx) j).
    lia. }
  assert (Hmuy : (ucreal_rawmod uy cy j <= my)%nat).
  { rewrite Hmydef. unfold ucreal_mod.
    assert (H1 := ucreal_env_ge_self (ucreal_rawmod uy cy) j).
    lia. }
  rewrite Hmxdef, Hmydef in *.
  pose proof (ucreal_mod_spec ux cx j (ucreal_mod ux cx j) m
                (Nat.le_refl _) Hmx) as Htx.
  pose proof (ucreal_mod_spec uy cy j (ucreal_mod uy cy j) m
                (Nat.le_refl _) Hmy) as Hty.
  apply QltT_to_Qlt in Htx. apply QltT_to_Qlt in Hty.
  apply Qabs_Qlt_condition in Htx. destruct Htx as [Htx1 Htx2].
  apply Qabs_Qlt_condition in Hty. destruct Hty as [Hty1 Hty2].
  pose proof (ucreal_pow2_le_mono n0
                (Qlowbound_ltabs_ZExp2 (eps0 * (1 # 4))) Hn0le) as Hpow.
  rewrite <- Hjn in Hpow.
  rewrite (ucreal_pow2_neg_eq j) in Hpow.
  exists n0.
  assert (Hsx : seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) ux cx)) n0
            = ux (ucreal_mod ux cx (Z.to_nat (Z.abs n0))))
    by reflexivity.
  assert (Hsy : seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) uy cy)) n0
            = uy (ucreal_mod uy cy (Z.to_nat (Z.abs n0))))
    by reflexivity.
  rewrite Hsx, Hsy.
  replace (Z.to_nat (Z.abs n0)) with j
    by (rewrite Habsn0, Hjdef; reflexivity).
  rewrite <- Hjn.
  rewrite (ucreal_pow2_neg_eq j).
  lra.
Qed.

(* ================================================================== *)
(* Section 5. The pi irrational separation theorem in CReal form.    *)
(* ================================================================== *)

Theorem ucreal_pi_sep_guarded :
  forall (a b : Q) (N : nat) (c0 : Q),
    QltT 0 (Qabs b) ->
    (1 <= N)%nat ->
    QltT 0 c0 ->
    QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - a / b)%Q)) ->
    sigT (fun c : Q => And (QltT 0 c)
            (CRealLt (ucreal_of_real (real_const c))
                     (ucreal_of_real (real_metric real_pi_geom
                        (real_const (a / b)))))).
Proof.
  intros a b N c0 Hb HN1 Hc0 Hguard.
  destruct (leibsep_pi_sep_alpha_guarded a b N c0 Hb HN1 Hc0 Hguard)
    as [c [Hpos Hlt]].
  exists c. split.
  - exact Hpos.
  - apply (ucreal_lt_compat _ _ Hlt).
Qed.

(* ================================================================== *)
(* Section 6. Verification probes.                                   *)
(* ================================================================== *)

From Stdlib Require Import Extraction.
Extraction "ucreal_bridge_extract.ml" ucreal_of_real.

Print Assumptions ucreal_of_real.
Print Assumptions ucreal_eq_seq_compat.
Print Assumptions ucreal_lt_compat.
Print Assumptions ucreal_pi_sep_guarded.
