(* ============================================================ *)
(* u4a_budget_flip.v                                            *)
(*                                                              *)
(* 使命：cos 零点唯一性定理的显式模量变体：在加细窗前提            *)
(*       (31/20 < w < 2) 下，以 eps/4 份额闭合 Lipschitz 逆界     *)
(*       （放大因子 120/61 < 2，终界 60/61·eps < eps 严格成立），  *)
(*       佐证 eps/8 份额选取系窗前提余量的产物而非数学必然。       *)
(* 主件：u4a_unique_widened_eps4（eps/4 版唯一性定理）；           *)
(*       u4a_inv_dist_strict / u4a_inv_dist_wide（逆界族两档）；   *)
(*       u4a_pi_leibniz_gt_31_10（Leibniz π 的 31/10 下界）；      *)
(*       u4a_pi_unique_eps4（π_L/2 顶点应用形）。                  *)
(* 依赖：S01–S09、S10_KVQuantTrig（lp 族、cos 零点序列、逆界、      *)
(*       半量括号）、S14_B5BatchBlock（cos(π_L/2)==0）、Stdlib。    *)
(* 对标：S10 cos_inv_dist_le2（v+u ≥ 3 放大因子 2、eps/8 份额）与  *)
(*       cos_pi_half_unique_widened 的加细对偶。                  *)
(* 构造性注记：纯 Set 层信息性主链（real_lt/real_eq/sigT）；        *)
(*       Q 层辅助件按库内惯例；零公理、零承认件、零经典逻辑；       *)
(*       31/10 下界的具体算术为 Q 层直构计算：lp_odd 12 的 13 对    *)
(*       项部分和 4·lp_odd 12 ≈ 3.10315 > 3.101 = 31/10 + 1/1000，  *)
(*       无常数黑箱。                                             *)
(* 编译配方：coqc -native-compiler no -Q <Live 树> "" -Q <本目录> "" *)
(*       u4a_budget_flip.v（Rocq 9.1）。                          *)
(* ============================================================ *)

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
Require Import S14_B5BatchBlock.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* §1 具体算术：4·lp_odd 12 的显式值与对 31/10 + 1/1000 的比较      *)
(* ============================================================ *)

(* lp_odd m = Σ_{j=0}^{m} (1/(4j+1) − 1/(4j+3))（S10 lp 族）；    *)
(* 4·lp_odd 12 展开为 13 项 8/((4j+1)(4j+3)) 之和。               *)
Lemma u4a_lp_odd12_value :
  lp_four * lp_odd 12 ==
  8 / (1 * 3) + 8 / (5 * 7) + 8 / (9 * 11) + 8 / (13 * 15) + 8 / (17 * 19)
  + 8 / (21 * 23) + 8 / (25 * 27) + 8 / (29 * 31) + 8 / (33 * 35)
  + 8 / (37 * 39) + 8 / (41 * 43) + 8 / (45 * 47) + 8 / (49 * 51).
Proof.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. simpl. lia.
Qed.

(* 具体比较：31/10 + 1/1000 < 4·lp_odd 12（精确 Q 层判定）。       *)
Lemma u4a_lp_odd12_margin :
  Qlt (31 / 10 + 1 / 1000) (lp_four * lp_odd 12).
Proof.
  rewrite u4a_lp_odd12_value.
  unfold Qlt. simpl. lia.
Qed.

(* ============================================================ *)
(* §2 Leibniz π 的 31/10 下界（real_pi_leibniz_gt_three 加细变体：  *)
(*    N := 12、margin := 1/1000、单调链 sc_lp_odd_chain）          *)
(* ============================================================ *)

Lemma u4a_pi_leibniz_gt_31_10 :
  real_lt (real_const (31 / 10)) cauchy_real_pi_leibniz.
Proof.
  unfold real_lt.
  exists (1 / 1000).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 12%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (lp_four * lp_odd 12 - 31 / 10) _).
    + apply (proj2 (Qlt_minus_iff (1 / 1000) (lp_four * lp_odd 12 - 31 / 10))).
      setoid_replace ((lp_four * lp_odd 12 - 31 / 10) - (1 / 1000))
        with (lp_four * lp_odd 12 - (31 / 10 + 1 / 1000)) by ring.
      apply (proj1 (Qlt_minus_iff (31 / 10 + 1 / 1000) (lp_four * lp_odd 12))).
      exact u4a_lp_odd12_margin.
    + apply Qplus_le_compat.
      * setoid_replace (lp_four * lp_odd 12) with (lp_odd 12 * lp_four) by ring.
        setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd 12) (lp_odd n) lp_four).
        -- apply sc_lp_odd_chain. apply NatLe_drop in Hn. lia.
        -- apply sc_lp_four_nonneg.
      * apply Qle_refl.
Qed.

(* ============================================================ *)
(* §3 半量桥：(1/2)·(31/10) == 31/20 与 31/20 < π_L/2 < 2          *)
(* ============================================================ *)

Lemma u4a_half_const_31_10 :
  real_eq (real_mult (real_const (1 / 2)) (real_const (31 / 10)))
          (real_const (31 / 20)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  rewrite !(real_mult_proj (real_const (1 / 2)) (real_const (31 / 10)) n).
  rewrite !(real_const_proj (1 / 2) n). rewrite !(real_const_proj (31 / 10) n).
  rewrite (real_const_proj (31 / 20) n). field.
Qed.

Lemma u4a_pi_leibniz_half_lower :
  real_lt (real_const (31 / 20)) w_leibniz.
Proof.
  unfold w_leibniz.
  apply (real_eq_lt_lt (real_const (31 / 20))
                       (real_mult (real_const (1 / 2)) (real_const (31 / 10))) _).
  - apply real_eq_sym. exact u4a_half_const_31_10.
  - apply (real_lt_eq_lt _ (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz) _).
    + apply (real_lt_mult_compat (real_const (31 / 10)) cauchy_real_pi_leibniz
                                 (real_const (1 / 2))).
      * exact real_half_pos.
      * exact u4a_pi_leibniz_gt_31_10.
    + exact real_half_pi_leibniz_comm.
Qed.

Lemma u4a_pi_leibniz_half_upper_two :
  real_lt w_leibniz (real_const 2).
Proof.
  apply (real_lt_trans _ (real_const (5 / 3)) _).
  - exact real_pi_leibniz_half_upper.
  - apply real_const_lt. change (Qlt (5 / 3) 2). compute. reflexivity.
Qed.

(* ============================================================ *)
(* §4 逆界族：和前提 u+v ≥ s ⟹ v−u < (6/s)·(du+dv) 两档            *)
(*    核心估计 cos_inv_pt：(v²−u²)/6 < du+dv（S10）。              *)
(* ============================================================ *)

(* 31/10 档：u+v ≥ 31/10 ⟹ v−u < (60/31)·(du+dv)，60/31 < 2。     *)
Lemma u4a_inv_dist_strict : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qle (31 / 10) (u + v) ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  Qlt (v - u) (60 / 31 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hsum Hdu Hdv.
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply (cos_inv_pt u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv). }
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (HvuS : Qle ((v - u) * (31 / 10)) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) (31 / 10) (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split.
      + change (Qle 0 (31 / 10)). unfold Qle, Qdiv. simpl. lia.
      + rewrite (Qplus_comm v u). exact Hsum. }
  assert (Hle1 : Qle (v - u) ((v * v - u * u) * (10 / 31))).
  { apply (Qle_trans _ (((v - u) * (31 / 10)) * (10 / 31)) _).
    - apply qeq_le.
      assert (Hr : ((v - u) * (31 / 10)) * (10 / 31) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr.
    - apply (Qmult_le_compat_r ((v - u) * (31 / 10)) (v * v - u * u) (10 / 31)).
      + apply (Qle_trans _ ((v - u) * (v + u)) _).
        * exact HvuS.
        * apply qeq_le. exact Hprod.
      + apply (Qlt_le_weak 0 (10 / 31)).
        change (Qlt 0 (10 / 31)). unfold Qdiv. compute. reflexivity. }
  assert (Hm : (v * v - u * u) * (10 / 31) == ((v * v - u * u) * (1 / 6)) * (60 / 31))
    by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  assert (Hm2 : (du + dv) * (60 / 31) == (60 / 31) * (du + dv)) by ring.
  apply (Qlt_le_trans (v - u) ((du + dv) * (60 / 31)) (60 / 31 * (du + dv))).
  - apply (Qle_lt_trans (v - u) ((v * v - u * u) * (10 / 31)) ((du + dv) * (60 / 31))).
    + exact Hle1.
    + apply (Qle_lt_trans ((v * v - u * u) * (10 / 31))
                         (((v * v - u * u) * (1 / 6)) * (60 / 31))
                         ((du + dv) * (60 / 31))).
      * apply qeq_le. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) (60 / 31)).
        -- change (Qlt 0 (60 / 31)). unfold Qdiv. compute. reflexivity.
        -- exact Hq.
  - apply qeq_le. exact Hm2.
Qed.

(* 61/20 档：u+v ≥ 61/20（= 3/2 + 31/20）⟹ v−u < (120/61)·(du+dv)， *)
(* 120/61 < 2。z 侧序列仅有下界 3/2，本档为唯一性定理的应用形。       *)
Lemma u4a_inv_dist_wide : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qle (61 / 20) (u + v) ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  Qlt (v - u) (120 / 61 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hsum Hdu Hdv.
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply (cos_inv_pt u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv). }
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (HvuW : Qle ((v - u) * (61 / 20)) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) (61 / 20) (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split.
      + change (Qle 0 (61 / 20)). unfold Qle, Qdiv. simpl. lia.
      + rewrite (Qplus_comm v u). exact Hsum. }
  assert (Hle1 : Qle (v - u) ((v * v - u * u) * (20 / 61))).
  { apply (Qle_trans _ (((v - u) * (61 / 20)) * (20 / 61)) _).
    - apply qeq_le.
      assert (Hr : ((v - u) * (61 / 20)) * (20 / 61) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr.
    - apply (Qmult_le_compat_r ((v - u) * (61 / 20)) (v * v - u * u) (20 / 61)).
      + apply (Qle_trans _ ((v - u) * (v + u)) _).
        * exact HvuW.
        * apply qeq_le. exact Hprod.
      + apply (Qlt_le_weak 0 (20 / 61)).
        change (Qlt 0 (20 / 61)). unfold Qdiv. compute. reflexivity. }
  assert (Hm : (v * v - u * u) * (20 / 61) == ((v * v - u * u) * (1 / 6)) * (120 / 61))
    by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  assert (Hm2 : (du + dv) * (120 / 61) == (120 / 61) * (du + dv)) by ring.
  apply (Qlt_le_trans (v - u) ((du + dv) * (120 / 61)) (120 / 61 * (du + dv))).
  - apply (Qle_lt_trans (v - u) ((v * v - u * u) * (20 / 61)) ((du + dv) * (120 / 61))).
    + exact Hle1.
    + apply (Qle_lt_trans ((v * v - u * u) * (20 / 61))
                         (((v * v - u * u) * (1 / 6)) * (120 / 61))
                         ((du + dv) * (120 / 61))).
      * apply qeq_le. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) (120 / 61)).
        -- change (Qlt 0 (120 / 61)). unfold Qdiv. compute. reflexivity.
        -- exact Hq.
  - apply qeq_le. exact Hm2.
Qed.

(* ============================================================ *)
(* §5 主定理：eps/4 份额版加细窗零点唯一性                          *)
(*    窗前提 31/20 < w < 2；对角两笔 + 柯西下标 + 逆界对全取 eps/4；  *)
(*    终界 (120/61)·(eps/4+eps/4) = 60/61·eps < eps。               *)
(* ============================================================ *)

Lemma u4a_unique_widened_eps4 : forall (w : Real),
  real_lt (real_const (31 / 20)) w -> real_lt w (real_const 2) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps4 : Qlt 0 (eps / 4)).
  { apply (Qlt_shift_div_l 0 eps 4).
    - change (Qlt 0 4). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* 逐点界来源：w 侧（端点 + cos w == 0 对角）、z 侧（cos_zero_lower/upper + cos z == 0 对角） *)
  destruct (real_lt_lower_pt (31 / 20) w Hlow) as [Nlo HNlo].
  destruct (real_lt_upper_pt 2 w Hup) as [Nup HNup].
  destruct (cos_eq_zero_diag_bound w Hw0 (eps / 4) Heps4) as [Nwd Hwd].
  destruct (cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 4) Heps4) as [Nzd Hzd].
  destruct (q_pow_arch 1 (eps / 4)) as [t Ht].
  { apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  { exact Heps4. }
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 2 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n ∈ (31/20, 2)、z_n ∈ (3/2, 5/3)（Q 层） *)
  assert (Hwlo : Qle (31 / 20) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) 2) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n)) by (apply Qlt_le_weak; apply cos_zero_lower).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3)) by (apply Qlt_le_weak; apply cos_zero_upper).
  (* z 侧 v ≤ 2（5/3 ≤ 2 传递，cos_inv_pt 前提） *)
  assert (Hzup2 : Qle (cos_zero_seq n) 2).
  { apply (Qle_trans _ (5 / 3) _); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]. }
  (* 和前提两形：3/2 + 31/20 == 61/20 *)
  assert (HsumB1 : Qle (61 / 20) (cos_zero_seq n + projT1 w n)).
  { apply (Qle_trans _ (3 / 2 + 31 / 20) _).
    - apply qeq_le. unfold Qdiv. field.
    - apply (Qplus_le_compat (3 / 2) (cos_zero_seq n) (31 / 20) (projT1 w n)).
      + apply Qlt_le_weak. apply cos_zero_lower.
      + apply Qlt_le_weak. apply (HNlo n). exact Hnlo. }
  assert (HsumB2 : Qle (61 / 20) (projT1 w n + cos_zero_seq n)).
  { apply (Qle_trans _ (31 / 20 + 3 / 2) _).
    - apply qeq_le. unfold Qdiv. field.
    - apply (Qplus_le_compat (31 / 20) (projT1 w n) (3 / 2) (cos_zero_seq n)).
      + apply Qlt_le_weak. apply (HNlo n). exact Hnlo.
      + apply Qlt_le_weak. apply cos_zero_lower. }
  (* cos w_n 与 cos z_n 的对角界 < eps/4 *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 4)).
  { apply (Hwd n). exact Hnwd. }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 4)).
  { apply (Hzd n). exact Hnzd. }
  (* 分支：|w_n − z_n| ≤ (120/61)·(eps/2) = 60/61·eps < eps（逆界，u := 小者） *)
  destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
  - (* z_n < w_n：u := z_n、v := w_n *)
    assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (120 / 61 * (eps / 4 + eps / 4))).
    { apply (u4a_inv_dist_wide (cos_zero_seq n) (projT1 w n) (eps / 4) (eps / 4) n).
      - exact Hn2.
      - apply (Qle_trans _ (3 / 2) _).
        + change (Qle 0 (3 / 2)). unfold Qle, Qdiv. simpl. lia.
        + apply Qlt_le_weak. apply cos_zero_lower.
      - apply Qlt_le_weak. exact Hzw.
      - exact Hwup.
      - exact HsumB1.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 4)).
        + apply qeq_le. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt.
      - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 4)).
        { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                              (eps / 4)).
          - apply qeq_le. apply Qabs_wd.
            assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
            { rewrite (real_cos_proj (real_const (projT1 w n)) n). rewrite (real_cos_proj w n). reflexivity. }
            rewrite Hq. reflexivity.
          - exact Hwpt. }
        exact Hwpt'.
    }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
    + apply qeq_le. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw.
    + apply (Qle_lt_trans _ (120 / 61 * (eps / 4 + eps / 4)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 120 / 61 * (eps / 4 + eps / 4) == 60 / 61 * eps) by (unfold Qdiv; field).
        apply (Qle_lt_trans (120 / 61 * (eps / 4 + eps / 4)) (60 / 61 * eps) eps).
        -- apply qeq_le. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (60 / 61 * eps) eps)).
           apply (Qlt_le_trans 0 (eps / 61) (eps - 60 / 61 * eps)).
           ++ apply (Qlt_shift_div_l 0 eps 61).
              ** change (Qlt 0 61). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply qeq_le. unfold Qminus. field.
  - (* w_n ≤ z_n：u := w_n、v := z_n（对称） *)
    assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 4)).
    { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                          (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                          (eps / 4)).
      - apply qeq_le. apply Qabs_wd.
        assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
        { rewrite (real_cos_proj (real_const (projT1 w n)) n). rewrite (real_cos_proj w n). reflexivity. }
        rewrite Hq. reflexivity.
      - exact Hwpt. }
    assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (120 / 61 * (eps / 4 + eps / 4))).
    { apply (u4a_inv_dist_wide (projT1 w n) (cos_zero_seq n) (eps / 4) (eps / 4) n).
      - exact Hn2.
      - apply (Qle_trans _ (31 / 20) _).
        + change (Qle 0 (31 / 20)). unfold Qle, Qdiv. simpl. lia.
        + apply Qlt_le_weak. apply (HNlo n). exact Hnlo.
      - exact Hwz.
      - exact Hzup2.
      - exact HsumB2.
      - exact Hwpt'.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 4)).
        + apply qeq_le. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt. }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
    + rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
      apply qeq_le. apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz.
    + apply (Qle_lt_trans _ (120 / 61 * (eps / 4 + eps / 4)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 120 / 61 * (eps / 4 + eps / 4) == 60 / 61 * eps) by (unfold Qdiv; field).
        apply (Qle_lt_trans (120 / 61 * (eps / 4 + eps / 4)) (60 / 61 * eps) eps).
        -- apply qeq_le. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (60 / 61 * eps) eps)).
           apply (Qlt_le_trans 0 (eps / 61) (eps - 60 / 61 * eps)).
           ++ apply (Qlt_shift_div_l 0 eps 61).
              ** change (Qlt 0 61). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply qeq_le. unfold Qminus. field.
Qed.

(* ============================================================ *)
(* §6 应用形：π_L/2 顶点（w_leibniz）在加细窗内仍满足三前提，         *)
(*    eps/4 版定理给出 w_leibniz == cos_pi_half。                   *)
(* ============================================================ *)

Lemma u4a_pi_unique_eps4 : real_eq w_leibniz cos_pi_half.
Proof.
  apply (u4a_unique_widened_eps4 w_leibniz).
  - exact u4a_pi_leibniz_half_lower.
  - exact u4a_pi_leibniz_half_upper_two.
  - exact b5dU_cos_piL_half_zero.
Qed.
