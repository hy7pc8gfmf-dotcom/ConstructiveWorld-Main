(* ============================================================ *)
(* abl_tvd_stationary.v —— tvd 层定常分布存在性+唯一性                      *)
(* 模块名：abl_tvd_stationary                                     *)
(* 数学使命：补马尔可夫大陆段 7 的 tvd 半边（全簇勘定最高价值缺口            *)
(*   M1/M2）——Id/tvd 层首个「被收缩去的定常对象」：                          *)
(*   ① tvs_coord_cauchy：迭代序列 μₙ＝Kⁿ·u 的逐坐标几何 Cauchy 核件          *)
(*      （率 2·hi·omd^min·(1+len·e)，omd＝1−δ*＝1−e^{−2γ/T}）；              *)
(*   ② tvs_pi：经 S02 real_cauchy_complete（完备性在册，本件直连）逐坐标      *)
(*      取极限得 π : list Real -> Real（全 j 定义，零选择公理）；             *)
(*   ③ tvs_stationary_exists：π 归一化 ∧ K·π == π（逐点，bare j）；          *)
(*   ④ tvs_stationary_unique：两定常对象在枚举坐标上逐点相等（收缩夹出）。     *)
(* 设计依据：S 温度窗注意力设计稿 §③ M1/M2；                                  *)
(*   可逆测度捷径已按设计记录排除（z 非对称），走几何 Cauchy 路线。             *)
(* 依赖清单：UpTVDoeblin（tv_/tvd_ 族主件）、S01/S02（real_cauchy_complete/   *)
(*   real_lim）、S03（real_abs 系）、S07（setoid/exp）、S08（sum 族/real_of_nat）,*)
(*   S09（real_le_mult_compat_r）、S12（real_minus_r）、S13（of_nat aux）、     *)
(*   UpGeomB（geod_b_kappa_lt_one）、Stdlib（Arith/List/QArith）。             *)
(* 对标行：UpTVDoeblin tv_doeblin_iter 收缩配方的定常分布存在性/唯一性重演。   *)
(* 构造性注记：Set 层承载/零承认/零公理；红线四条全守。本库 real_le 为          *)
(*   Or(lt)(eq) 编码——软界（如 TV≤1）在该编码不可证，本件一律改走               *)
(*   「逐 eps 形 + Q 投影沉降」：abs 三角用 real_abs_triangle_le_eps，           *)
(*   饱和闭合用 tvs_eq_zero_of_abs_lt（∀eps |d|<eps ⟹ d≈0）；                   *)
(*   非负性需求由 Q 层逐点 Qabs_nonneg 承担（tvs_qsum_ge_abs）。               *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-Q vo_local_world_unified_0930 ""。 *)
(* ============================================================ *)
From Stdlib Require Import List Arith.Arith.
Import ListNotations.
From Stdlib Require Import QArith.Qring QArith.Qabs Lia micromega.Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpTVDoeblin.
Require Import UpGeomB.

(* ################ Part 0：Q 层原子工具 ################ *)

(* Z.of_nat-型 Q 正性（本项目 Q.of_nat 缺位，直用 (Z.of_nat n # 1) 形） *)
Lemma tvs_qofnat_pos : forall n : nat, (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof.
  intros [| m] H; [ lia | ].
  unfold Qlt. simpl. lia.
Qed.

(* 预算：0 < e、0 < eps ⟹ ∃Nb, 1 < (Z.of_nat Nb # 1)·(e·eps)（q_arch_inv 直取） *)
Lemma tvs_q_budget : forall e eps : Q,
  Qlt 0 e -> Qlt 0 eps ->
  sigT (fun Nb : nat => Qlt 1 ((Z.of_nat Nb # 1) * (e * eps))).
Proof.
  intros e eps He Heps.
  assert (Hep : Qlt 0 (e * eps)).
  { destruct e as [a b]; destruct eps as [c d]; simpl in *.
    unfold Qlt in *; simpl in *.
    destruct (Qlt_le_dec 0 (a # b)) as [H1 | H1].
    - destruct (Qlt_le_dec 0 (c # d)) as [H2 | H2].
      + unfold Qlt. simpl. lia.
      + lia.
    - lia. }
  destruct (q_arch_inv (e * eps) Hep) as [M HM].
  exists (M + 2)%nat.
  assert (HNbpos : Qlt 0 (Z.of_nat (M + 2) # 1))
    by (apply tvs_qofnat_pos; lia).
  assert (Hmul := Qmult_lt_compat_r (1 / (Z.of_nat (M + 2) # 1))
                     (e * eps) (Z.of_nat (M + 2) # 1) HNbpos HM).
  assert (Hone : Qeq ((1 / (Z.of_nat (M + 2) # 1))
                        * (Z.of_nat (M + 2) # 1)) (Qmake 1 1)).
  { field.
    intro Hc. apply (Qlt_not_eq 0 (Z.of_nat (M + 2) # 1) HNbpos).
    apply Qeq_sym. exact Hc. }
  setoid_rewrite Hone in Hmul.
  assert (Hsw : Qeq ((e * eps) * (Z.of_nat (M + 2) # 1))
                     ((Z.of_nat (M + 2) # 1) * (e * eps))) by ring.
  setoid_rewrite Hsw in Hmul. exact Hmul.
Qed.

(* Qabs 库件直连：|t| ≥ t、−t ≤ |t|（Qle_Qabs/Qabs_opp 桥） *)
Lemma tvs_qabs_ge : forall t : Q, Qle t (Qabs t).
Proof. intro t. exact (Qle_Qabs t). Qed.

Lemma tvs_qabs_ge_opp : forall t : Q, Qle (- t) (Qabs t).
Proof.
  intro t. apply (Qle_trans (- t) (Qabs (- t))).
  - exact (Qle_Qabs (- t)).
  - apply qeq_le. exact (Qabs_opp t).
Qed.

(* Q 和逐项非负 ⟹ 和非负（real_list_sum 投影形） *)
Lemma tvs_qsum_nonneg : forall (X : Set) (f : X -> Real) (l : list X) (n : nat),
  (forall v : X, Qle 0 (projT1 (f v) n)) ->
  Qle 0 (projT1 (real_list_sum X f l) n).
Proof.
  intros X f l n. induction l as [| a rest IH]; intro H.
  - cbn [real_list_sum].
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. apply Qle_refl.
  - cbn [real_list_sum].
    setoid_rewrite (real_plus_proj (f a) (real_list_sum X f rest) n).
    apply (Qle_trans 0 (projT1 (f a) n)).
    + apply H.
    + apply (Qle_plus_nonneg_r (projT1 (f a) n)
               (projT1 (real_list_sum X f rest) n)
               (IH (fun v => H v))).
Qed.

(* InT 成员的 |d w|_n ≤ Σ_{v∈l}|d v|_n（Q 层逐点；InT 见证归纳） *)
Lemma tvs_qsum_ge_abs : forall (X : Set) (d : X -> Real) (w : X) (l : list X)
                                   (n : nat),
  InT w l ->
  Qle (projT1 (real_abs (d w)) n)
      (projT1 (real_list_sum X (fun v : X => real_abs (d v)) l) n).
Proof.
  intros X d w l n Hin.
  induction Hin as [l0 | y l0 Hin IH].
  - cbn [real_list_sum].
    setoid_rewrite (real_plus_proj (real_abs (d w))
               (real_list_sum X (fun v : X => real_abs (d v)) l0) n).
    apply (Qle_plus_nonneg_r (projT1 (real_abs (d w)) n)
             (projT1 (real_list_sum X (fun v : X => real_abs (d v)) l0) n)).
    + apply (tvs_qsum_nonneg X (fun v : X => real_abs (d v)) l0 n).
      intro v. setoid_rewrite (real_abs_proj (d v) n). apply Qabs_nonneg.
  - cbn [real_list_sum].
    setoid_rewrite (real_plus_proj (real_abs (d y))
               (real_list_sum X (fun v : X => real_abs (d v)) l0) n).
    apply (Qle_trans _ (projT1 (real_list_sum X
                            (fun v : X => real_abs (d v)) l0) n)).
    + exact IH.
    + setoid_rewrite (real_abs_proj (d y) n).
      apply (Qle_trans _ (projT1 (real_list_sum X
                            (fun v : X => real_abs (d v)) l0) n
                          + Qabs (projT1 (d y) n))).
      * apply (Qle_plus_nonneg_r (projT1 (real_list_sum X
                                  (fun v : X => real_abs (d v)) l0) n)
                   (Qabs (projT1 (d y) n))
                   (Qabs_nonneg (projT1 (d y) n))).
      * apply qeq_le. ring.
Qed.

(* ################ Part 2：rpow 工具 + 几何预算（Q 地板+投影饱和路线） #### *)

(* real_one 的 Q 投影桥 *)
Lemma tvs_one_proj : forall k : nat, Qeq (projT1 real_one k) (Qmake 1 1).
Proof. intro k. unfold real_one. exact (real_const_proj (Qmake 1 1) k). Qed.

(* Q 层 nat 幂（透明 Fixpoint） *)
Fixpoint tvs_qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => (1 # 1)%Q
  | Datatypes.S m => q * tvs_qpow q m
  end.

(* 迭代和承载：X 0 := 1，X (S m) := X m + d（Bernoulli 的 X 项；
   real_of_nat 投影不透明，故自造透明迭代和） *)
Fixpoint tvs_xiter (d : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_plus (tvs_xiter d m) d
  end.

(* —— Q 层助手：w < y − z 且 0 < w ⟹ z < y（sign 可判定 + nia） —— *)
Lemma tvs_qlt_sub_r : forall w y z : Q,
  Qlt 0 w -> Qlt w (y - z) -> Qlt z y.
Proof.
  intros [w1 w2] [y1 y2] [z1 z2] H1 H2.
  unfold Qlt in *; unfold Qminus, Qplus, Qopp, Qinv in H2; simpl in *.
  destruct z1 as [| | z1']; simpl in *; destruct w1 as [| | w1']; simpl in *;
    try (destruct z2 as [| z2']; try (destruct w2 as [| w2'])); try nia.
Qed.

(* —— rpow 基础三件 —— *)

(* rpow 正性：0 < c ⟹ 0 < cⁿ *)
Lemma tvs_rpow_pos : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_lt real_zero (tv_rpow c n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [tv_rpow]. exact (real_mult_positive c (tv_rpow c m) Hc IH).
Qed.

(* rpow ≤ 1：0 < c ≤ 1 ⟹ cⁿ ≤ 1 *)
Lemma tvs_rpow_le_one : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (n : nat),
  real_le (tv_rpow c n) real_one.
Proof.
  intros c Hc0 Hc1 n. induction n as [| m IH].
  - apply real_le_refl.
  - cbn [tv_rpow].
    apply (real_le_trans (real_mult c (tv_rpow c m))
             (real_mult real_one (tv_rpow c m)) real_one).
    + exact (real_le_mult_compat c real_one (tv_rpow c m)
               (tvs_rpow_pos c Hc0 m) Hc1).
    + apply (real_le_trans (real_mult real_one (tv_rpow c m)) (tv_rpow c m)).
      * apply (RealSetoid.real_eq_le _ _).
        exact (real_eq_trans (real_mult real_one (tv_rpow c m))
                 (real_mult (tv_rpow c m) real_one) (tv_rpow c m)
                 (real_mult_comm real_one (tv_rpow c m))
                 (real_mult_one (tv_rpow c m))).
      * exact IH.
Qed.

(* rpow 指数反单调：n ≤ m ⟹ c^m ≤ c^n *)
Lemma tvs_rpow_anti_mono : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (m n : nat),
  (n <= m)%nat -> real_le (tv_rpow c m) (tv_rpow c n).
Proof.
  intros c Hc0 Hc1 m. induction m as [| m' IH]; intros n Hle.
  - assert (Hn : n = 0%nat) by lia. subst. apply real_le_refl.
  - destruct n as [| n'].
    + change (tv_rpow c 0) with real_one.
      exact (tvs_rpow_le_one c Hc0 Hc1 (Datatypes.S m')).
    + assert (Hnm : (n' <= m')%nat) by lia.
      apply (RealSetoid.real_le_id_l (tv_rpow c (Datatypes.S m'))
               (real_mult c (tv_rpow c m')) (real_mult c (tv_rpow c n'))).
      -- exact (real_eq_refl (real_mult c (tv_rpow c m'))).
      -- exact (tvd_le_mult_compat_l c (tv_rpow c m') (tv_rpow c n')
                  Hc0 (IH n' Hnm)).
Qed.

(* 减法反单调：e < d ⟹ 1 − d < 1 − e（负元反号 + 右平移两步） *)
Lemma tvs_lt_minus_antitone : forall (e d : Real),
  real_lt e d -> real_lt (real_minus_r real_one d) (real_minus_r real_one e).
Proof.
  intros e d Hed.
  assert (Hopp : real_lt (real_opp d) (real_opp e))
    by exact (real_opp_lt_compat e d Hed).
  apply (real_eq_lt_lt (real_minus_r real_one d)
           (real_plus real_one (real_opp d))
           (real_plus real_one (real_opp e))).
  - apply real_eq_of_zero_diff. intro n0.
    unfold real_minus_r. cbn [projT1].
    repeat first
      [ rewrite (real_plus_proj _ _ n0)
      | rewrite (real_opp_proj _ _ n0)
      | rewrite (tvs_one_proj n0) ].
    ring.
  - apply (real_eq_lt_lt (real_plus real_one (real_opp d))
             (real_plus (real_opp d) real_one)
             (real_plus real_one (real_opp e))).
    + exact (real_plus_comm real_one (real_opp d)).
    + exact (real_lt_eq_lt (real_plus (real_opp d) real_one)
               (real_plus (real_opp e) real_one)
               (real_plus real_one (real_opp e))
               (real_lt_plus_compat_lt_le (real_opp d) (real_opp e)
                  real_one real_one Hopp (real_le_refl real_one))
               (real_plus_comm (real_opp e) real_one)).
Qed.

(* 零预算：c ≈ 0 ⟹ ∃N ∀n≥N: cⁿ < eps *)
Lemma tvs_geom_budget_zero : forall (c : Real) (Hc : real_eq c real_zero)
    (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow c n) (real_const eps)).
Proof.
  intros c Hc eps Heps. exists 1%nat. intros n Hn.
  destruct n as [| m]; [ exfalso; lia | ].
  cbn [tv_rpow].
  apply (real_eq_lt_lt (real_mult c (tv_rpow c m)) real_zero (real_const eps)).
  - exact (real_eq_trans (real_mult c (tv_rpow c m))
             (real_mult real_zero (tv_rpow c m)) real_zero
             (RealSetoid.real_eq_mult_compat c (tv_rpow c m) real_zero
                (tv_rpow c m) Hc (real_eq_refl (tv_rpow c m)))
             (real_eq_trans (real_mult real_zero (tv_rpow c m))
                (real_mult (tv_rpow c m) real_zero) real_zero
                (real_mult_comm real_zero (tv_rpow c m))
                (real_mult_zero (tv_rpow c m)))).
  - exact (real_const_lt 0 eps (QltT_to_Qlt 0 eps Heps)).
Qed.

(* —— Q 层幂三件 —— *)

(* Q 幂非负 *)
Lemma tvs_qpow_nonneg : forall (q : Q) (Hq : Qle 0 q) (n : nat),
  Qle 0 (tvs_qpow q n).
Proof.
  intros q Hq n. induction n as [| m IH].
  - cbn [tvs_qpow]. exact Qle_0_1.
  - cbn [tvs_qpow]. apply Qmult_le_0_compat; [exact Hq | exact IH].
Qed.

(* Q 幂 ≤ 1：0 ≤ q ≤ 1 ⟹ qⁿ ≤ 1 *)
Lemma tvs_qpow_le_one : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qle q 1) (n : nat),
  Qle (tvs_qpow q n) (Qmake 1 1).
Proof.
  intros q Hq0 Hq1 n. induction n as [| m IH].
  - cbn [tvs_qpow]. apply Qle_refl.
  - cbn [tvs_qpow].
    apply (Qle_trans (q * tvs_qpow q m) (Qmake 1 1 * tvs_qpow q m)
             (Qmake 1 1)).
    + exact (Qmult_le_compat_r q (Qmake 1 1) (tvs_qpow q m) Hq1
               (tvs_qpow_nonneg q Hq0 m)).
    + apply (Qle_trans (Qmake 1 1 * tvs_qpow q m) (tvs_qpow q m)
               (Qmake 1 1)).
      * apply qeq_le. ring.
      * exact IH.
Qed.

(* Q 幂反单调：0 ≤ q ≤ 1、n ≤ m ⟹ qᵐ ≤ qⁿ（tvs_qgeom 闭合依赖） *)
Lemma tvs_qpow_decr : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qle q 1)
    (m n : nat), (n <= m)%nat -> Qle (tvs_qpow q m) (tvs_qpow q n).
Proof.
  intros q Hq0 Hq1 m. induction m as [| m' IH]; intros n Hle.
  - assert (Hn : n = 0%nat) by lia. subst. apply Qle_refl.
  - destruct n as [| n'].
    + change (tvs_qpow q 0) with (Qmake 1 1).
      exact (tvs_qpow_le_one q Hq0 Hq1 (Datatypes.S m')).
    + assert (Hnm : (n' <= m')%nat) by lia.
      cbn [tvs_qpow].
      apply (Qle_trans (q * tvs_qpow q m') (tvs_qpow q m' * q)
               (q * tvs_qpow q n')).
      * apply qeq_le. ring.
      * apply (Qle_trans (tvs_qpow q m' * q) (tvs_qpow q n' * q)
                 (q * tvs_qpow q n')).
        -- exact (Qmult_le_compat_r (tvs_qpow q m') (tvs_qpow q n') q
                    (IH n' Hnm) Hq0).
        -- apply qeq_le. ring.
Qed.

(* Q Bernoulli：(1 + n·(1−q))·qⁿ ≤ 1（0 < q ≤ 1） *)
Lemma tvs_qbern : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qle q 1) (n : nat),
  Qle ((Qmake 1 1 + Qmake (Z.of_nat n) 1 * (1 - q)) * tvs_qpow q n) (Qmake 1 1).
Proof.
  intros q Hq0 Hq1 n.
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  induction n as [| m IH].
  - cbn [tvs_qpow]. simpl. apply qeq_le. ring.
  - cbn [tvs_qpow].
    assert (Hm0 : Qle 0 (Qmake (Z.of_nat m) 1)) by (unfold Qle; simpl; lia).
    assert (Hmq : Qle 0 (Qmake (Z.of_nat m) 1 * (1 - q)))
      by (apply Qmult_le_0_compat;
            [ exact Hm0
            | exact (proj1 (Qle_minus_iff q (Qmake 1 1)) Hq1) ]).
    assert (HA0 : Qle 0 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
    { apply (Qle_trans 0 (Qmake 1 1)
               (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
      - exact Qle_0_1.
      - apply (Qle_trans (Qmake 1 1) (Qmake 1 1 + 0%Q)
                 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
        + apply qeq_le. ring.
        + exact (Qplus_le_compat (Qmake 1 1) (Qmake 1 1) 0%Q
                   (Qmake (Z.of_nat m) 1 * (1 - q))
                   (Qle_refl (Qmake 1 1)) Hmq). }
    assert (H1A : Qle (Qmake 1 1)
                    (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
      by exact (Qplus_le_compat (Qmake 1 1) (Qmake 1 1) 0%Q
                  (Qmake (Z.of_nat m) 1 * (1 - q))
                  (Qle_refl (Qmake 1 1)) Hmq).
    assert (Hstep : Qle ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                           * tvs_qpow q m * q)
                        (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
    { apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                          * tvs_qpow q m * q)
              (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
              (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
      - apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                            * tvs_qpow q m * q)
                 ((Qmake 1 1) * q)
                 (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))).
        + exact (Qmult_le_compat_r
                   ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                      * tvs_qpow q m)
                   (Qmake 1 1) q IH Hq0le).
        + apply (Qle_trans ((Qmake 1 1) * q)
                   ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) * q)
                   (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))).
          * exact (Qmult_le_compat_r (Qmake 1 1)
                     (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) q H1A Hq0le).
          * apply qeq_le. ring.
      - apply (Qle_trans (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
                 ((Qmake 1 1) * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
                 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
        + exact (Qmult_le_compat_r q (Qmake 1 1)
                   (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) Hq1 HA0).
        + apply qeq_le. ring. }
    destruct (Z.eq_dec (Z.of_nat (Datatypes.S m)) (Z.add 1 (Z.of_nat m)))
      as [Hz | Hzn]; [| lia].
    rewrite Hz.
    assert (Hx1 : Qle (q * tvs_qpow q m) (Qmake 1 1))
      by exact (tvs_qpow_le_one q Hq0le Hq1 (Datatypes.S m)).
    assert (H1mq : Qle 0 (Qminus (Qmake 1 1) q))
      by exact (proj1 (Qle_minus_iff q (Qmake 1 1)) Hq1).
    assert (Hbase : forall a b : Z, a = b -> Qeq (Qmake a 1) (Qmake b 1)).
    { intros a b Hab. cbv [Qeq Qnum Qden]. cbn.
      rewrite Hab. reflexivity. }
    assert (Hqadd : Qeq (Qmake (Z.add 1 (Z.of_nat m)) 1)
                        (Qplus (Qmake 1 1) (Qmake (Z.of_nat m) 1))).
    { change (Qeq (Qmake (Z.add 1 (Z.of_nat m)) 1)
                  (Qmake (1 * 1 + Z.of_nat m * 1) (1 * 1))).
      apply Hbase. ring. }
    apply (Qle_trans ((1 + Qmake (Z.add 1 (Z.of_nat m)) 1
                         * (Qminus (Qmake 1 1) q))
                        * (q * tvs_qpow q m))
            ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (Qminus (Qmake 1 1) q))
               * (q * tvs_qpow q m)
               + (Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
            (Qmake 1 1)).
    + rewrite Hqadd. apply qeq_le. ring.
    + apply (Qle_trans _ (Qmake 1 1 * q + Qminus (Qmake 1 1) q)).
      * apply (Qplus_le_compat
                  ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (Qminus (Qmake 1 1) q))
                     * (q * tvs_qpow q m))
                  (Qmake 1 1 * q)
                  ((Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
                  (Qminus (Qmake 1 1) q)).
        -- apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1
                               * (Qminus (Qmake 1 1) q))
                               * (q * tvs_qpow q m))
                   (((Qmake 1 1 + Qmake (Z.of_nat m) 1
                        * (Qminus (Qmake 1 1) q))
                       * tvs_qpow q m) * q)
                   (Qmake 1 1 * q)).
          ++ apply qeq_le. ring.
          ++ exact (Qmult_le_compat_r
                      ((Qmake 1 1 + Qmake (Z.of_nat m) 1
                          * (Qminus (Qmake 1 1) q))
                         * tvs_qpow q m)
                      (Qmake 1 1) q IH Hq0le).
        -- apply (Qle_trans ((Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
                   ((q * tvs_qpow q m) * (Qminus (Qmake 1 1) q))
                   (Qminus (Qmake 1 1) q)).
          ++ apply qeq_le. ring.
          ++ apply (Qle_trans ((q * tvs_qpow q m) * (Qminus (Qmake 1 1) q))
                     ((Qmake 1 1) * (Qminus (Qmake 1 1) q))
                     (Qminus (Qmake 1 1) q)).
            ** exact (Qmult_le_compat_r (q * tvs_qpow q m) (Qmake 1 1)
                       (Qminus (Qmake 1 1) q) Hx1 H1mq).
            ** apply qeq_le. ring.
      * apply qeq_le. ring.
Qed.

(* Q 几何消去：0 < m、a·m < b·m ⟹ a < b *)
Lemma tvs_qmult_lt_cancel_r : forall a b m : Q,
  Qlt 0 m -> Qlt (a * m) (b * m) -> Qlt a b.
Proof.
  intros a b m Hm H.
  assert (H2 := Qmult_lt_compat_r (a * m)%Q (b * m)%Q (Qinv m)
                   (Qinv_lt_0_compat m Hm) H).
  assert (Ha : Qeq ((a * m) * Qinv m) a).
  { field. intro Hc. apply (Qlt_not_eq 0 m Hm). symmetry. exact Hc. }
  assert (Hb : Qeq ((b * m) * Qinv m) b).
  { field. intro Hc. apply (Qlt_not_eq 0 m Hm). symmetry. exact Hc. }
  setoid_rewrite Ha in H2. setoid_rewrite Hb in H2. exact H2.
Qed.

(* Q 几何预算：0 < q < 1 ⟹ ∃N ∀n≥N: qⁿ < eps *)
Lemma tvs_qgeom : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1) (eps : Q)
    (Heps : Qlt 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (tvs_qpow q n) eps).
Proof.
  intros q Hq0 Hq1 eps Heps.
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  assert (Hq1le : Qle q 1) by (apply (Qlt_le_weak q 1); exact Hq1).
  assert (Hone : Qlt 0 (1 - q)%Q) by exact (proj1 (Qlt_minus_iff q (Qmake 1 1)) Hq1).
  assert (Hep : Qlt 0 ((1 - q)%Q * eps)) by (apply Qmult_lt_0_compat; assumption).
  destruct (q_arch_inv ((1 - q)%Q * eps) Hep) as [M HM].
  assert (HNbpos : Qlt 0 (Z.of_nat (M + 2) # 1)) by (apply tvs_qofnat_pos; lia).
  assert (Hmul := Qmult_lt_compat_r (1 / (Z.of_nat (M + 2) # 1))
                     ((1 - q)%Q * eps) (Z.of_nat (M + 2) # 1) HNbpos HM).
  assert (Hinv : Qeq ((1 / (Z.of_nat (M + 2) # 1))
                        * (Z.of_nat (M + 2) # 1)) (Qmake 1 1)).
  { field.
    intro Hc. apply (Qlt_not_eq 0 (Z.of_nat (M + 2) # 1) HNbpos).
    apply Qeq_sym. exact Hc. }
  setoid_rewrite Hinv in Hmul.
  (* 1 < ((1−q)·eps)·Nb；换序到 (Nb·(1−q))·eps *)
  assert (Hsw1 : Qeq ((1 - q)%Q * eps * (Z.of_nat (M + 2) # 1))
                     ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps)) by ring.
  setoid_rewrite Hsw1 in Hmul.
  exists (M + 2)%nat. intros n Hn.
  assert (Hb := tvs_qbern q Hq0 Hq1le n).
  assert (Hkey : Qle ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                     (Qmake 1 1)).
  { assert (HX : Qle ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                     (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    { apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
               (0%Q + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
               (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
      - apply qeq_le. ring.
      - exact (Qplus_le_compat 0%Q (Qmake 1 1)
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 Qle_0_1 (Qle_refl ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))). }
    assert (HX0 : Qle 0 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
      by (apply Qmult_le_0_compat;
            [ apply (Qlt_le_weak 0 (Z.of_nat (M + 2) # 1)); exact HNbpos
            | apply (Qlt_le_weak 0 (1 - q)%Q); exact Hone ]).
    assert (Hdec2 : Qle (tvs_qpow q n) (tvs_qpow q (M + 2)))
      by exact (tvs_qpow_decr q Hq0le Hq1le n (M + 2) Hn).
    apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
             ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))
             (Qmake 1 1)).
    - apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
               (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
               ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))).
      + apply qeq_le. ring.
      + apply (Qle_trans (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                 (tvs_qpow q (M + 2) * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))).
        * exact (Qmult_le_compat_r (tvs_qpow q n) (tvs_qpow q (M + 2))
                   ((Z.of_nat (M + 2) # 1) * (1 - q)%Q) Hdec2 HX0).
        * apply qeq_le. ring.
    - apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q
                          * tvs_qpow q (M + 2))
               ((Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                  * tvs_qpow q (M + 2))
               (Qmake 1 1)).
      + exact (Qmult_le_compat_r ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 (tvs_qpow q (M + 2)) HX (tvs_qpow_nonneg q Hq0le (M + 2))).
      + exact (tvs_qbern q Hq0 Hq1le (M + 2)). }
  assert (HXlt : Qlt ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                     ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps))
    by exact (Qle_lt_trans
                ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                (Qmake 1 1)
                ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps)
                Hkey Hmul).
  assert (HXlt2 : Qlt (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                      (eps * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))).
  { setoid_rewrite (Qmult_comm (tvs_qpow q n)
                      ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    setoid_rewrite (Qmult_comm eps
                      ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    exact HXlt. }
  apply (tvs_qmult_lt_cancel_r (tvs_qpow q n) eps
           ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
  - apply (Qmult_lt_0_compat (Z.of_nat (M + 2) # 1) (1 - q)%Q).
    + apply tvs_qofnat_pos. lia.
    + exact Hone.
  - exact HXlt2.
Qed.

(* ################ Part 3：Q 沉降引擎（幂单调 + 投影桥 + Real 几何预算） #### *)

(* Q 幂左乘单调：0 ≤ a ≤ b ⟹ aⁿ ≤ bⁿ *)
Lemma tvs_qpow_mono : forall (a b : Q) (Hab : Qle a b) (Ha0 : Qle 0 a)
    (n : nat), Qle (tvs_qpow a n) (tvs_qpow b n).
Proof.
  intros a b Hab Ha0 n.
  assert (Hb0 : Qle 0 b) by (apply (Qle_trans 0 a b); [ exact Ha0 | exact Hab ]).
  induction n as [| m IH].
  - cbn [tvs_qpow]. apply Qle_refl.
  - cbn [tvs_qpow].
    apply (Qle_trans (a * tvs_qpow a m) (b * tvs_qpow a m)
             (b * tvs_qpow b m)).
    + exact (Qmult_le_compat_r a b (tvs_qpow a m) Hab (tvs_qpow_nonneg a Ha0 m)).
    + apply (Qle_trans (b * tvs_qpow a m) (tvs_qpow a m * b)
               (b * tvs_qpow b m)).
      * apply qeq_le. ring.
      * apply (Qle_trans (tvs_qpow a m * b) (tvs_qpow b m * b)
                 (b * tvs_qpow b m)).
        -- exact (Qmult_le_compat_r (tvs_qpow a m) (tvs_qpow b m) b IH Hb0).
        -- apply qeq_le. ring.
Qed.

(* tv_rpow 的 Q 投影：projT1 (tv_rpow c n) k == tvs_qpow (projT1 c k) n *)
Lemma tvs_qpow_proj : forall (c : Real) (k n : nat),
  Qeq (projT1 (tv_rpow c n) k) (tvs_qpow (projT1 c k) n).
Proof.
  intros c k n. induction n as [| m IH].
  - exact (tvs_one_proj k).
  - cbn [tv_rpow]. rewrite (real_mult_proj c (tv_rpow c m) k).
    cbn [tvs_qpow]. setoid_rewrite IH. apply Qeq_refl.
Qed.

(* ################ Part 3.5：续建段（Q 微助手 + 预算闭合 + 调度） #### *)

(* Q 微助手一：0 < w ⟹ 1 − w < 1（Qlt_minus_iff 反向 + ring 等价） *)
Lemma tvs_qlt_one_minus_r : forall w : Q,
  Qlt 0 w -> Qlt (Qminus (Qmake 1 1) w) (Qmake 1 1).
Proof.
  intros w Hw.
  apply (proj2 (Qlt_minus_iff (Qminus (Qmake 1 1) w) (Qmake 1 1))).
  assert (Hr : Qeq (Qminus (Qmake 1 1) (Qminus (Qmake 1 1) w)) w) by ring.
  rewrite Hr. exact Hw.
Qed.

(* Q 微助手二：0 < b、b < c − a ⟹ a < c − b（同一差量两次换向） *)
Lemma tvs_qlt_swap_sub : forall a b c : Q,
  Qlt 0 b -> Qlt b (Qminus c a) -> Qlt a (Qminus c b).
Proof.
  intros a b c H1 H2.
  apply (proj2 (Qlt_minus_iff a (Qminus c b))).
  assert (Hr : Qeq (Qminus (Qminus c b) a) (Qminus (Qminus c a) b)) by ring.
  rewrite Hr.
  exact (proj1 (Qlt_minus_iff b (Qminus c a)) H2).
Qed.

(* Q 微助手三：2t == e、p < t ⟹ t < e − p（间隙让位） *)
Lemma tvs_qlt_gap : forall e p t : Q,
  Qeq (Qplus t t) e -> Qlt p t -> Qlt t (Qminus e p).
Proof.
  intros e p t H0 H1.
  apply (proj2 (Qlt_minus_iff t (Qminus e p))).
  rewrite <- H0.
  assert (Hr : Qeq (Qminus (Qminus (Qplus t t) p) t) (Qminus t p)) by ring.
  rewrite Hr.
  exact (proj1 (Qlt_minus_iff p t) H1).
Qed.

(* NatLe 的 max 左/右投影（real_lt 界位为 NatLe 形——.vo 实拍口径） *)
Lemma tvs_natle_max_l : forall a b k : nat, NatLe (Nat.max a b) k -> NatLe a k.
Proof.
  intros a b k H. apply NatLe_lift.
  apply (Nat.le_trans a (Nat.max a b) k (Nat.le_max_l a b)
           (NatLe_drop (Nat.max a b) k H)).
Qed.

Lemma tvs_natle_max_r : forall a b k : nat, NatLe (Nat.max a b) k -> NatLe b k.
Proof.
  intros a b k H. apply NatLe_lift.
  apply (Nat.le_trans b (Nat.max a b) k (Nat.le_max_r a b)
           (NatLe_drop (Nat.max a b) k H)).
Qed.

(* Q 微助手四：0 < eps ⟹ 0 < eps/2（Qlt_shift_div_l 池法，原 L299 同款） *)
Lemma tvs_qlt_half_posT : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 2)%Q.
Proof.
  intro eps. intro Heps.
  apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | ].
  simpl. apply QltT_to_Qlt. exact Heps.
Qed.

Lemma tvs_qlt_half_pos : forall eps : Q, QltT 0 eps -> Qlt 0 (eps / 2)%Q.
Proof.
  intros eps Heps. apply QltT_to_Qlt. exact (tvs_qlt_half_posT eps Heps).
Qed.

(* —— Real 几何预算（缺件补齐至闭合：双侧投影夹出 q := 1 − w1 ∈ (0,1)，Q 沉降闭合） —— *)
Lemma tvs_omd_pow_budget : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_lt c real_one) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow c n) (real_const eps)).
Proof.
  intros c Hc0 Hc1 eps Heps.
  destruct Hc0 as [w0 [Hw0 [N0 HN0]]].
  destruct Hc1 as [w1 [Hw1 [N1 HN1]]].
  assert (Hw0q : Qlt 0 w0) by (apply QltT_to_Qlt; exact Hw0).
  assert (Hw1q : Qlt 0 w1) by (apply QltT_to_Qlt; exact Hw1).
  assert (Hq1 : Qlt (Qminus (Qmake 1 1) w1) (Qmake 1 1))
    by exact (tvs_qlt_one_minus_r w1 Hw1q).
  set (k0 := Nat.max N0 N1).
  assert (Hk0 : QltT w0 (projT1 c k0 - projT1 real_zero k0))
    by (apply HN0; apply NatLe_lift; apply Nat.le_max_l).
  assert (Hk1 : QltT w1 (projT1 real_one k0 - projT1 c k0))
    by (apply HN1; apply NatLe_lift; apply Nat.le_max_r).
  assert (Hck0 : Qlt 0 (projT1 c k0))
    by (apply (tvs_qlt_sub_r w0 (projT1 c k0) (projT1 real_zero k0) Hw0q);
        apply QltT_to_Qlt; exact Hk0).
  assert (Hck1 : Qlt w1 (Qminus (Qmake 1 1) (projT1 c k0)))
    by exact (QltT_to_Qlt w1 (Qminus (Qmake 1 1) (projT1 c k0)) Hk1).
  assert (Hckq : Qlt (projT1 c k0) (Qminus (Qmake 1 1) w1))
    by exact (tvs_qlt_swap_sub (projT1 c k0) w1 (Qmake 1 1) Hw1q Hck1).
  assert (Hq0 : Qlt 0 (Qminus (Qmake 1 1) w1))
    by exact (Qlt_trans 0 (projT1 c k0) (Qminus (Qmake 1 1) w1) Hck0 Hckq).
  assert (Hepsh : Qlt 0 (eps / 2)%Q) by exact (tvs_qlt_half_pos eps Heps).
  destruct (tvs_qgeom (Qminus (Qmake 1 1) w1) Hq0 Hq1 (eps / 2)%Q Hepsh)
    as [Nq HNq].
  exists (Nat.max Nq (Nat.max N0 N1)). intros n Hn.
  unfold real_lt. exists (eps / 2)%Q. split.
  - apply Qlt_to_QltT. exact Hepsh.
  - exists (Nat.max N0 N1). intros k Hk.
    assert (Hk0' : QltT w0 (projT1 c k - projT1 real_zero k))
      by (apply HN0; exact (tvs_natle_max_l N0 N1 k Hk)).
    assert (Hk1' : QltT w1 (projT1 real_one k - projT1 c k))
      by (apply HN1; exact (tvs_natle_max_r N0 N1 k Hk)).
    assert (Hnq' : Qlt (tvs_qpow (Qminus (Qmake 1 1) w1) n) (eps / 2)%Q)
      by (apply HNq;
          exact (Nat.le_trans Nq (Nat.max Nq (Nat.max N0 N1)) n
                   (Nat.le_max_l Nq (Nat.max N0 N1)) Hn)).
    assert (Hck0' : Qlt 0 (projT1 c k))
      by (apply (tvs_qlt_sub_r w0 (projT1 c k) (projT1 real_zero k) Hw0q);
          apply QltT_to_Qlt; exact Hk0').
    assert (Hck1' : Qlt w1 (Qminus (Qmake 1 1) (projT1 c k)))
      by exact (QltT_to_Qlt w1 (Qminus (Qmake 1 1) (projT1 c k)) Hk1').
    assert (Hckq' : Qle (projT1 c k) (Qminus (Qmake 1 1) w1))
      by (apply Qlt_le_weak;
          exact (tvs_qlt_swap_sub (projT1 c k) w1 (Qmake 1 1) Hw1q Hck1')).
    assert (Hmono : Qle (tvs_qpow (projT1 c k) n)
                        (tvs_qpow (Qminus (Qmake 1 1) w1) n))
      by exact (tvs_qpow_mono _ _ Hckq' (Qlt_le_weak 0 _ Hck0') n).
    apply Qlt_to_QltT.
    rewrite (real_const_proj eps k).
    setoid_rewrite (tvs_qpow_proj c k n).
    apply (tvs_qlt_gap eps (tvs_qpow (projT1 c k) n) (eps / 2)%Q).
    + field.
    + exact (Qle_lt_trans _ _ _ Hmono Hnq').
Qed.

(* —— δ 预算调度：δ ≤ 1 的 Or 双支统一（lt 支几何预算、eq 支零预算） —— *)
Lemma tvs_delta_budget : forall (dlt : Real) (Hd0 : real_lt real_zero dlt)
    (Hd1 : real_le dlt real_one) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow (tv_omd dlt) n) (real_const eps)).
Proof.
  intros dlt Hd0 Hd1 eps Heps.
  destruct Hd1 as [Hdlt | Hd1e].
  - exact (tvs_omd_pow_budget (tv_omd dlt) (tv_omd_pos_of_lt dlt Hdlt)
             (geod_b_kappa_lt_one dlt Hd0) eps Heps).
  - exact (tvs_geom_budget_zero (tv_omd dlt) (tv_omd_eq_zero dlt Hd1e) eps Heps).
Qed.

(* —— eq→real_eq 桥 + 迭代拆分（定义性函数等） —— *)
Lemma tvs_eq_real_eq : forall x y : Real, x = y -> real_eq x y.
Proof.
  intros x y Hxy eps Heps.
  rewrite Hxy.
  exists 0%nat. intros n _.
  apply Qlt_to_QltT.
  assert (Hz : Qeq (Qabs (projT1 y n - projT1 y n)) 0).
  { apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. ring.
    - cbn [Qabs]. apply Qeq_refl. }
  rewrite Hz.
  exact (QltT_to_Qlt 0 eps Heps).
Qed.

Lemma tvs_titer_add_eq : forall (states : list (list Real))
    (K : list Real -> list Real -> Real) (m k : nat) (mu : list Real -> Real),
  tv_titer states K (m + k) mu = tv_titer states K m (tv_titer states K k mu).
Proof.
  intros states K m. induction m as [| m IH]; intros k mu.
  - reflexivity.
  - change (Nat.add (Datatypes.S m) k) with (Datatypes.S (Nat.add m k)).
    cbn [tv_titer]. f_equal. apply IH.
Qed.

(* —— Real 层常数桥四件（后续半范数链用） —— *)
Lemma tvs_abs_opp : forall x : Real, real_eq (real_abs (real_opp x)) (real_abs x).
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_abs_proj (real_opp x) n).
  setoid_rewrite (real_abs_proj x n).
  setoid_rewrite (real_opp_proj x n).
  setoid_rewrite (Qabs_opp (projT1 x n)).
  ring.
Qed.

Lemma tvs_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)%Q).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_mult_proj (real_const a) (real_const b) n).
  setoid_rewrite (real_const_proj a n).
  setoid_rewrite (real_const_proj b n).
  ring.
Qed.

Lemma tvs_two_eq : real_eq (real_const (Qmake 2 1)) (real_plus real_one real_one).
Proof.
  apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_const_proj (Qmake 2 1) n).
  setoid_rewrite (real_plus_proj real_one real_one n).
  setoid_rewrite (tvs_one_proj n).
  ring.
Qed.

(* real_of_nat 的 Q 投影逐点形（闭合走 unfold Qeq + Z 乘幺群改写，同 part01 修复） *)
Lemma tvs_ofnat_proj : forall (n k : nat),
  Qeq (projT1 (real_of_nat n) k) (Z.of_nat n # 1).
Proof.
  intro n. induction n as [| m IH].
  - intro k. cbn [real_of_nat].
    replace (Z.of_nat 0)%Z with 0%Z by reflexivity.
    apply real_const_proj.
  - intro k. cbn [real_of_nat].
    rewrite (real_plus_proj real_one (real_of_nat m) k).
    rewrite (tvs_one_proj k).
    rewrite IH.
    unfold Qeq. cbn [Qnum Qden Qplus Qminus Qopp].
    rewrite !Z.mul_1_r.
    replace (Z.of_nat (Datatypes.S m)) with (Z.add 1 (Z.of_nat m)) by lia.
    reflexivity.
Qed.

Lemma tvs_ofnat_const_eq : forall n : nat,
  real_eq (real_of_nat n) (real_const (Qmake (Z.of_nat n) 1)).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  setoid_rewrite (tvs_ofnat_proj n k).
  setoid_rewrite (real_const_proj (Z.of_nat n # 1) k).
  ring.
Qed.

(* ################ Part 4：tvs_tv 半范数收缩链（M1 主引擎，复活批 2） #### *)

(* 无半因子半范数：Σ_{枚举} |μ − ν|（tv_doeblin 的 2 倍量；
   规避 real_inv_pos 投影不可达墙，Or 编码下乘 2 精确消半因子） *)
Definition tvs_tv (states : list (list Real)) (mu nu : list Real -> Real) : Real :=
  real_list_sum (list Real)
    (fun s : list Real => real_abs (real_minus_r (mu s) (nu s))) states.

Lemma tvs_const_two_pos : real_le real_zero (real_const (Qmake 2 1)).
Proof.
  apply tvd_lt_le. apply real_const_lt. unfold Qlt. simpl. lia.
Qed.

Lemma tvs_two_half_one :
  real_eq (real_mult (real_const (Qmake 2 1)) tv_half) real_one.
Proof.
  apply (real_eq_trans (real_mult (real_const (Qmake 2 1)) tv_half)
           (real_mult tv_half (real_const (Qmake 2 1))) real_one).
  - exact (real_mult_comm (real_const (Qmake 2 1)) tv_half).
  - apply (real_eq_trans (real_mult tv_half (real_const (Qmake 2 1)))
             (real_mult tv_half (real_plus real_one real_one)) real_one).
    + apply (RealSetoid.real_eq_mult_compat tv_half (real_const (Qmake 2 1))
               tv_half (real_plus real_one real_one)
               (real_eq_refl tv_half) tvs_two_eq).
    + apply (real_eq_trans (real_mult tv_half (real_plus real_one real_one))
               (real_mult (real_plus real_one real_one) tv_half) real_one).
      * exact (real_mult_comm tv_half (real_plus real_one real_one)).
      * exact (real_inv_pos_correct (real_plus real_one real_one) tv_two_pos).
Qed.

(* tv_doeblin 乘 2 即 tvs_tv（2·(half·Σ) == Σ，纯 eq 代数） *)
Lemma tvs_doeblin_double : forall (states : list (list Real))
    (a b : list Real -> Real),
  real_eq (real_mult (real_const (Qmake 2 1)) (tv_doeblin states a b))
          (tvs_tv states a b).
Proof.
  intros states a b.
  apply (real_eq_trans
           (real_mult (real_const (Qmake 2 1)) (tv_doeblin states a b))
           (real_mult (real_mult (real_const (Qmake 2 1)) tv_half)
                      (tvs_tv states a b))
           (tvs_tv states a b)).
  - exact (real_mult_assoc (real_const (Qmake 2 1)) tv_half
             (tvs_tv states a b)).
  - apply (real_eq_trans
             (real_mult (real_mult (real_const (Qmake 2 1)) tv_half)
                        (tvs_tv states a b))
             (real_mult real_one (tvs_tv states a b))
             (tvs_tv states a b)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_const (Qmake 2 1)) tv_half)
               (tvs_tv states a b) real_one (tvs_tv states a b)
               tvs_two_half_one (real_eq_refl (tvs_tv states a b))).
    + apply (real_eq_trans (real_mult real_one (tvs_tv states a b))
               (real_mult (tvs_tv states a b) real_one)
               (tvs_tv states a b)).
      * exact (real_mult_comm real_one (tvs_tv states a b)).
      * exact (real_mult_one (tvs_tv states a b)).
Qed.

(* 收缩主件：tvs_tv(Kⁿμ, Kⁿν) ≤ omdⁿ · tvs_tv(μ,ν)
   （tv_doeblin_iter 原件 + 乘 2 消半因子；Or 双支经 le_id 传输） *)
Lemma tvs_tv_iter :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
    (Hg : real_lt real_zero gamma) (z : list Real -> list Real -> Real)
    (Hzlo : forall i j : list Real, real_le (real_opp gamma) (z i j))
    (Hzhi : forall i j : list Real, real_le (z i j) gamma)
    (Labs : forall f : list Real -> Real,
       real_le (real_abs (real_list_sum (list Real) f states))
               (real_list_sum (list Real)
                  (fun w : list Real => real_abs (f w)) states))
    (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tvs_tv states
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
          (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                     (tvs_tv states mu nu)).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma Hg z Hzlo Hzhi Labs n mu nu Hmu Hnu.
  assert (Hcon := tv_doeblin_iter states (tvd_K states n_pos Ttemp Ttemp_pos z)
                    (tvd_K_row states n_pos Ttemp Ttemp_pos z)
                    (tvd_u states n_pos) (tvd_u_norm states n_pos)
                    (tvd_dstar Ttemp Ttemp_pos gamma)
                    (tvd_dstar_le_one Ttemp Ttemp_pos gamma Hg)
                    (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hzlo Hzhi)
                    Labs n mu nu Hmu Hnu).
  assert (H2 := real_le_mult_compat_r (real_const (Qmake 2 1))
                   (tv_doeblin states
                      (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                      (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
                   (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                              (tv_doeblin states mu nu))
                   tvs_const_two_pos Hcon).
  assert (HL1 : real_eq (real_mult (real_const (Qmake 2 1))
                          (tv_doeblin states
                             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
                  (tvs_tv states
                     (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                     (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
    by exact (tvs_doeblin_double states _ _).
  assert (HR2 : real_eq (real_mult (real_const (Qmake 2 1))
                          (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                                      (tv_doeblin states mu nu)))
                  (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                              (tvs_tv states mu nu))).
  { apply (real_eq_trans
             (real_mult (real_const (Qmake 2 1))
                (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                           (tv_doeblin states mu nu)))
             (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                (real_mult (real_const (Qmake 2 1)) (tv_doeblin states mu nu)))
             (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                         (tvs_tv states mu nu))).
    - exact (tvd_mult_swap_ab (real_const (Qmake 2 1))
                (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                (tv_doeblin states mu nu)).
    - apply (RealSetoid.real_eq_mult_compat
               (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
               (real_mult (real_const (Qmake 2 1)) (tv_doeblin states mu nu))
               (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
               (tvs_tv states mu nu)
               (real_eq_refl (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n))
               (tvs_doeblin_double states mu nu)). }
  apply (RealSetoid.real_le_id_l
           (tvs_tv states
              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
           (real_mult (real_const (Qmake 2 1))
              (tv_doeblin states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
           (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                       (tvs_tv states mu nu))
           (real_eq_sym (real_mult (real_const (Qmake 2 1))
                           (tv_doeblin states
                              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
              (tvs_tv states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
              HL1)).
  exact (RealSetoid.real_le_id_r
           (real_mult (real_const (Qmake 2 1))
              (tv_doeblin states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
           (real_mult (real_const (Qmake 2 1))
              (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                         (tv_doeblin states mu nu)))
           (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                       (tvs_tv states mu nu))
           HR2 H2).
Qed.

(* 一致基界：归一非负 ν ⟹ tvs_tv(ν, u) < 2 + len + 1（逐点三角 +1 松弛 + 求和） *)
Lemma tvs_tv_unif_bound :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
    (gamma : Real) (z : list Real -> list Real -> Real)
    (nu : list Real -> Real),
  (forall i : list Real, real_le real_zero (nu i)) ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_lt (tvs_tv states nu (tvd_u states n_pos))
          (real_const
             (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                    (Qmake 1 1))).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z nu Hnu Hnorm.
  assert (Hpt : forall i : list Real,
    real_le (real_abs (real_minus_r (nu i) (tvd_u states n_pos i)))
            (real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)).
  { intro i.
    assert (Htri := real_abs_triangle_le_eps (nu i)
                      (real_opp (tvd_u states n_pos i)) real_one real_lt_zero_one).
    assert (Habsnu : real_eq (real_abs (nu i)) (nu i))
      by exact (tvd_abs_le_id (nu i) (Hnu i)).
    assert (Habsu : real_eq (real_abs (real_opp (tvd_u states n_pos i)))
                             (tvd_u states n_pos i)).
    { apply (real_eq_trans (real_abs (real_opp (tvd_u states n_pos i)))
               (real_abs (tvd_u states n_pos i)) (tvd_u states n_pos i)).
      - exact (tvs_abs_opp (tvd_u states n_pos i)).
      - exact (tvd_abs_le_id (tvd_u states n_pos i)
                 (tvd_lt_le real_zero (tvd_u states n_pos i)
                    (real_inv_pos_pos (real_of_nat (length states)) n_pos))). }
    exact (RealSetoid.real_le_id_r
             (real_abs (real_minus_r (nu i) (tvd_u states n_pos i)))
             (real_plus (real_plus (real_abs (nu i))
                          (real_abs (real_opp (tvd_u states n_pos i)))) real_one)
             (real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
             (RealSetoid.real_eq_plus_compat
                (real_plus (real_abs (nu i))
                   (real_abs (real_opp (tvd_u states n_pos i))))
                real_one
                (real_plus (nu i) (tvd_u states n_pos i)) real_one
                (RealSetoid.real_eq_plus_compat (real_abs (nu i))
                   (real_abs (real_opp (tvd_u states n_pos i)))
                   (nu i) (tvd_u states n_pos i) Habsnu Habsu)
                (real_eq_refl real_one))
             Htri). }
  assert (Hsum : real_le (tvs_tv states nu (tvd_u states n_pos))
                   (real_list_sum (list Real)
                      (fun i : list Real =>
                         real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                      states))
    by (apply real_list_sum_le; exact Hpt).
  assert (Hrhs : real_eq
    (real_list_sum (list Real)
       (fun i : list Real =>
          real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one) states)
    (real_plus (real_plus real_one real_one)
       (real_mult (real_of_nat (length states)) real_one))).
  { apply (real_eq_trans
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                states)
             (real_plus
                (real_list_sum (list Real)
                   (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                   states)
                (real_list_sum (list Real) (fun _ : list Real => real_one) states))
             (real_plus (real_plus real_one real_one)
                (real_mult (real_of_nat (length states)) real_one))).
    - exact (real_list_sum_add (list Real)
                (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                (fun _ : list Real => real_one) states).
    - apply (RealSetoid.real_eq_plus_compat
                (real_list_sum (list Real)
                   (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                   states)
                (real_list_sum (list Real) (fun _ : list Real => real_one) states)
                (real_plus real_one real_one)
                (real_mult (real_of_nat (length states)) real_one)).
      + apply (real_eq_trans
                  (real_list_sum (list Real)
                     (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                     states)
                  (real_plus (real_list_sum (list Real) nu states)
                             (real_list_sum (list Real) (tvd_u states n_pos) states))
                  (real_plus real_one real_one)).
        * exact (real_list_sum_add (list Real) nu (tvd_u states n_pos) states).
        * exact (RealSetoid.real_eq_plus_compat (real_list_sum (list Real) nu states)
                    (real_list_sum (list Real) (tvd_u states n_pos) states)
                    real_one real_one Hnorm (tvd_u_norm states n_pos)).
      + exact (tvd_list_sum_const (list Real) real_one states). }
  assert (Hone : real_eq real_one (real_const (Qmake 1 1))).
  { apply real_eq_of_zero_diff. intro n.
    setoid_rewrite (tvs_one_proj n).
    ring. }
  assert (Hlen : real_eq (real_mult (real_of_nat (length states)) real_one)
                   (real_const (Qmake (Z.of_nat (length states)) 1))).
  { apply (real_eq_trans (real_mult (real_of_nat (length states)) real_one)
             (real_mult (real_const (Qmake (Z.of_nat (length states)) 1)) real_one)
             (real_const (Qmake (Z.of_nat (length states)) 1))).
    - apply (RealSetoid.real_eq_mult_compat (real_of_nat (length states))
               real_one (real_const (Qmake (Z.of_nat (length states)) 1)) real_one
               (tvs_ofnat_const_eq (length states)) Hone).
    - exact (real_mult_one (real_const (Qmake (Z.of_nat (length states)) 1))). }
  assert (HC : real_eq
    (real_plus (real_plus real_one real_one)
       (real_mult (real_of_nat (length states)) real_one))
    (real_const
       (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
          (Qmake (Z.of_nat (length states)) 1)))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus real_one real_one)
             (real_mult (real_of_nat (length states)) real_one)
             (real_const (Qplus (Qmake 1 1) (Qmake 1 1)))
             (real_const (Qmake (Z.of_nat (length states)) 1))
             (RealSetoid.real_eq_plus_compat real_one real_one
                (real_const (Qmake 1 1)) (real_const (Qmake 1 1)) Hone Hone)
             Hlen). }
  assert (Hltc : real_lt
    (real_const (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                   (Qmake (Z.of_nat (length states)) 1)))
    (real_const (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                   (Qmake 1 1)))).
  { apply real_const_lt. unfold Qlt. simpl. lia. }
  apply (real_le_lt_trans (tvs_tv states nu (tvd_u states n_pos))
           (real_const
              (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                 (Qmake (Z.of_nat (length states)) 1)))
           (real_const
              (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                     (Qmake 1 1)))).
  - exact (RealSetoid.real_le_id_r (tvs_tv states nu (tvd_u states n_pos))
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                states)
             (real_const
                (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                   (Qmake (Z.of_nat (length states)) 1)))
             (real_eq_trans
                (real_list_sum (list Real)
                   (fun i : list Real =>
                      real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                   states)
                (real_plus (real_plus real_one real_one)
                   (real_mult (real_of_nat (length states)) real_one))
                (real_const
                   (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                      (Qmake (Z.of_nat (length states)) 1))) Hrhs HC)
             Hsum).
  - exact Hltc.
Qed.

(* ################ Part 5：坐标 Cauchy 模量（M1 核心，复活批 3a） #### *)

(* Or 编码下非负乘（四支全构造） *)
Lemma tvs_mult_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b -> real_le real_zero (real_mult a b).
Proof.
  intros a b Ha Hb. destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb].
  - apply tvd_lt_le. exact (real_mult_pos_compat a b Ha Hb).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult a real_zero) real_zero
                (RealSetoid.real_eq_mult_compat a b a real_zero (real_eq_refl a)
                   (real_eq_sym real_zero b Hb))
                (real_mult_zero a))).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult real_zero b) real_zero
                (RealSetoid.real_eq_mult_compat a b real_zero b
                   (real_eq_sym real_zero a Ha) (real_eq_refl b))
                (real_eq_trans (real_mult real_zero b) (real_mult b real_zero)
                   real_zero
                   (real_mult_comm real_zero b) (real_mult_zero b)))).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult real_zero b) real_zero
                (RealSetoid.real_eq_mult_compat a b real_zero b
                   (real_eq_sym real_zero a Ha) (real_eq_refl b))
                (real_eq_trans (real_mult real_zero b)
                   (real_mult real_zero real_zero) real_zero
                   (RealSetoid.real_eq_mult_compat real_zero b real_zero real_zero
                      (real_eq_refl real_zero) (real_eq_sym real_zero b Hb))
                   (real_mult_zero real_zero)))).
Qed.

(* 迭代分布逐坐标非负 *)
Lemma tvs_iter_nonneg :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
    (z : list Real -> list Real -> Real) (t : nat) (i : list Real),
  real_le real_zero
    (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) t
              (tvd_u states n_pos) i).
Proof.
  intros states n_pos Ttemp Ttemp_pos z t. induction t as [| t IH]; intro i.
  - apply tvd_lt_le. exact (real_inv_pos_pos (real_of_nat (length states)) n_pos).
  - unfold tv_step.
    apply real_list_sum_nonneg. intro w.
    exact (tvs_mult_nonneg
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) t
                       (tvd_u states n_pos) w)
             (tvd_K states n_pos Ttemp Ttemp_pos z w i) (IH w)
             (tvd_K_pos states n_pos Ttemp Ttemp_pos z w i)).
Qed.

(* 逐点提取器：tvs_tv(a,b) < eps/2 ⟹ |a(j) − b(j)| < eps（j ∈ 枚举） *)
Lemma tvs_pt_of_tv_lt : forall (states : list (list Real))
    (a b : list Real -> Real) (j : list Real) (eps : Q),
  InT j states -> QltT 0 (eps / 2)%Q ->
  real_lt (tvs_tv states a b) (real_const (eps / 2)%Q) ->
  real_lt (real_abs (real_minus_r (a j) (b j))) (real_const eps).
Proof.
  intros states a b j eps Hj Heph Htv.
  destruct Htv as [wt [Hwt [Nt HNt]]].
  unfold real_lt. exists (eps / 2)%Q. split.
  - exact Heph.
  - exists Nt. intros k Hk.
    apply Qlt_to_QltT.
    setoid_rewrite (real_const_proj eps k).
    apply (tvs_qlt_gap eps (projT1 (real_abs (real_minus_r (a j) (b j))) k)
             (eps / 2)%Q).
    + field.
    + apply (Qle_lt_trans (projT1 (real_abs (real_minus_r (a j) (b j))) k)
               (projT1 (tvs_tv states a b) k) (eps / 2)%Q).
      * exact (tvs_qsum_ge_abs (list Real)
                  (fun i : list Real => real_minus_r (a i) (b i)) j states k Hj).
      * apply (tvs_qlt_sub_r wt (eps / 2)%Q (projT1 (tvs_tv states a b) k)).
        -- exact (QltT_to_Qlt 0 wt Hwt).
        -- exact (QltT_to_Qlt wt
                    (eps / 2 - projT1 (tvs_tv states a b) k)%Q (HNt k Hk)).
Qed.

(* Qeq 常数桥 *)
Lemma tvs_const_eq_of_Qeq : forall a b : Q,
  Qeq a b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b Hab. apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_const_proj a n).
  setoid_rewrite (real_const_proj b n).
  rewrite Hab. ring.
Qed.

(* 迭代零化：c ≈ 0 ⟹ c^(S t) ≈ 0 *)
Lemma tvs_rpow_zero : forall (c : Real) (Hc : real_eq c real_zero) (t : nat),
  real_eq (tv_rpow c (Datatypes.S t)) real_zero.
Proof.
  intros c Hc t. induction t as [| m IH].
  - cbn [tv_rpow].
    exact (real_eq_trans (real_mult c real_one) c real_zero
             (real_mult_one c) Hc).
  - change (tv_rpow c (Datatypes.S (Datatypes.S m)))
      with (real_mult c (tv_rpow c (Datatypes.S m))).
    exact (real_eq_trans (real_mult c (tv_rpow c (Datatypes.S m))) real_zero
             real_zero
             (real_eq_trans (real_mult c (tv_rpow c (Datatypes.S m)))
                (real_mult real_zero (tv_rpow c (Datatypes.S m))) real_zero
                (RealSetoid.real_eq_mult_compat c (tv_rpow c (Datatypes.S m))
                   real_zero (tv_rpow c (Datatypes.S m)) Hc
                   (real_eq_refl (tv_rpow c (Datatypes.S m))))
                (real_eq_trans (real_mult real_zero (tv_rpow c (Datatypes.S m)))
                   (real_mult (tv_rpow c (Datatypes.S m)) real_zero) real_zero
                   (real_mult_comm real_zero (tv_rpow c (Datatypes.S m)))
                   (real_mult_zero (tv_rpow c (Datatypes.S m)))))
             (real_eq_refl real_zero)).
Qed.

(* —— 诚实登记：坐标 Cauchy 主件 tvs_coord_cauchy 结构已定稿未闭合（当时上下文
   预算尽），链路全景：tvs_tv_iter（收缩）+ tvs_tv_unif_bound（一致基界）+
   tvs_delta_budget（omd 几何预算双支调度）+ tvs_pt_of_tv_lt（逐点提取）+
   tvs_iter_nonneg/tvs_mult_nonneg/tvs_rpow_zero（δ*=1 零化链）——全部在册闭合；
   余下仅装配：HNB 参数化 aux（m≤n 直用 + n≤m abs 对称支）+ δ*<1 支经
   tvs_omd_pow_budget/tvs_rpow_pos 严格乘链 + δ*=1 支经 tvs_rpow_zero 零化链。
   设计全文见工作区续建设计稿续建节。 *)

(* ################ 取证（在册件同口径） ################ *)
Print Assumptions tvs_tv_iter.
Print Assumptions tvs_tv_unif_bound.
Print Assumptions tvs_omd_pow_budget.
Print Assumptions tvs_delta_budget.
Print Assumptions tvs_pt_of_tv_lt.
(* —— 诚实登记：tvs_coord_cauchy 装配未闭合（两轮截断保留已闭合前缀）。
   结构定稿：HNB 参数化 aux（m≤n 直用 + n≤m abs 对称支）+ 双支预算。
   全部因子件已绿：tvs_tv_iter/tvs_tv_unif_bound/tvs_delta_budget/
   tvs_pt_of_tv_lt/tvs_iter_nonneg/tvs_mult_nonneg/tvs_rpow_zero/
   tvs_const_eq_of_Qeq/tvs_qlt_*。
   唯一硬墙（经验卡库检索后仍存）：Qlt 目标闭合器缺失——
   stdlib 无 Qlt_0_1；lia/lra 不识 Qlt 与 (a?=b)=Lt 形（快测 t1-t7 实拍）；
   HCQ(0 < CQ) 需 Qlt_le_trans 0 1 CQ，其 Qle 2 ≤ CQ 尾距一步。
   处方已定：Qle_minus_iff proj2 化 Qle 2≤CQ 为 Qle 0 (CQ−1)（LHS=0 池绿形）
   + Qlt 0 1 用 unfold Qlt; simpl; reflexivity（concrete 可闭，快测 ✓）。
   装配正文全稿见工作区续建设计稿续建节。 *)
