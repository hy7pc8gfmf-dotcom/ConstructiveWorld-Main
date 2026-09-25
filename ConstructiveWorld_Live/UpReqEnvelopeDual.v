(* ==========================================================================)
   UpReqEnvelopeDual.v — log/exp 的倒数对偶包络
   使命: evd_log_ge_inv_one_eps/evd_log_one_plus_ge_inv_eps（log 上下包络 ε 形）、evd_exp_le_one_of_le_zero/evd_exp_le_inv_one_minus_B（exp 上界 ≤_B）、evd_dual_log_ge_gives_exp_pre_inv_B/evd_dual_exp_le_gives_log_ge（对偶互推）与 evd_log_one_plus_pnk_upper_B/evd_log_one_plus_sandwich_B（夹逼件）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、UpReqPinskerCore；Stdlib QArith、Arith
   对标: 初等解析不等式族 log(1+x) 与 exp 的倒数对偶包络（指数-对数双向夹逼）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpReqPinskerCore.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.PeanoNat.

(* ===== 0. 基础设施：倒数代数 / exp 单 / log 外延 / 严格化辅助 ===== *)

(* inv 1 == 1（inv 唯一性一步） *)
Lemma evd_inv_one :
  real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_inv_unique real_one
                         (real_inv_pos real_one real_lt_zero_one) real_one).
  - apply real_inv_pos_correct.
  - exact (real_mult_one real_one).
Qed.

(* inv(inv u) == u（inv 唯一性 + 交换律，零点态） *)
Lemma evd_inv_inv : forall (u : Real) (Hu : real_lt real_zero u),
  real_eq (real_inv_pos (real_inv_pos u Hu) (real_inv_pos_pos u Hu)) u.
Proof.
  intros u Hu.
  apply (real_inv_unique (real_inv_pos u Hu)
                         (real_inv_pos (real_inv_pos u Hu) (real_inv_pos_pos u Hu))
                         u).
  - apply real_inv_pos_correct.
  - apply real_eq_trans with (real_mult u (real_inv_pos u Hu)).
    + apply real_mult_comm.
    + apply real_inv_pos_correct.
Qed.

(* exp 单（等式反射）：e^a == e^b ⟹ a == b（弱三分 + 严格单调） *)
Lemma evd_exp_inj : forall a b : Real,
  real_eq (cauchy_real_exp a) (cauchy_real_exp b) -> real_eq a b.
Proof.
  intros a b Hab.
  apply real_weak_trich.
  - intro Hlt.
    apply (real_lt_not_eq (cauchy_real_exp a) (cauchy_real_exp b)).
    + apply (cauchy_real_exp_mono a b). exact Hlt.
    + exact Hab.
  - intro Hlt.
    apply (real_lt_not_eq (cauchy_real_exp b) (cauchy_real_exp a)).
    + apply (cauchy_real_exp_mono b a). exact Hlt.
    + apply real_eq_sym. exact Hab.
Qed.

(* log 外延（等元换证位）：x == y ⟹ log x == log y（全经 exp 单，
   不触碰 log 的依赖证明位——绕开接口别名伪影坑） *)
Lemma evd_log_ext : forall (x y : Real)
  (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply evd_exp_inj.
  apply real_eq_trans with x.
  - exact (cw_log_exp_right x Hx).
  - apply real_eq_trans with y.
    + exact Hxy.
    + apply real_eq_sym. exact (cw_log_exp_right y Hy).
Qed.

(* 正性翻转：0 < a ⟹ −a < 0（点态一次配平，全件唯一 QltT 手工位） *)
Lemma evd_lt_opp_flip : forall a : Real,
  real_lt real_zero a -> real_lt (real_opp a) real_zero.
Proof.
  intros a Ha. unfold real_lt in Ha. destruct Ha as [mu [Hmu [N HN]]].
  unfold real_lt. exists mu. split.
  - exact Hmu.
  - exists N. intros n Hn. apply Qlt_to_QltT.
    apply (Qlt_le_trans mu (projT1 a n - projT1 real_zero n)).
    + exact (QltT_to_Qlt mu (projT1 a n - projT1 real_zero n) (HN n Hn)).
    + apply qeq_le.
      rewrite (real_opp_proj a n). rewrite (real_const_proj 0 n).
      ring.
Qed.

(* ≤ + 正松量 ⟹ <（两倍松量形）：real_le 之 Or 两支统一出口 *)
Lemma evd_le_lt_double : forall x y z : Real,
  real_lt real_zero z ->
  real_le x (real_plus y z) ->
  real_lt x (real_plus y (real_plus z z)).
Proof.
  intros x y z Hz Hle. unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - (* lt 支：x < y+z，加 0 ≤ z 保严（x+0==x、(y+z)+z==y+(z+z) 两跳换形） *)
    apply (real_lt_eq_lt x (real_plus (real_plus y z) z)
                         (real_plus y (real_plus z z))).
    + apply (real_eq_lt_lt x (real_plus x real_zero)
                           (real_plus (real_plus y z) z)).
      * apply real_eq_of_zero_diff. intro k.
        rewrite (real_plus_proj x real_zero k).
        rewrite (real_const_proj 0 k). ring.
      * apply (real_lt_plus_compat_lt_le x (real_plus y z) real_zero z).
        -- exact Hlt.
        -- unfold real_le. left. exact Hz.
    + apply real_eq_of_zero_diff. intro k.
      rewrite (real_plus_proj _ _ k). rewrite (real_plus_proj _ _ k).
      rewrite (real_plus_proj _ _ k). rewrite (real_plus_proj _ _ k).
      ring.
  - (* eq 支：x == y+z，右端自加正松量换左元 *)
    apply (real_lt_eq_lt x (real_plus (real_plus y z) z)
                         (real_plus y (real_plus z z))).
    + apply (real_eq_lt_lt x (real_plus y z) (real_plus (real_plus y z) z)).
      * exact Heq.
      * exact (real_lt_plus_r_zero (real_plus y z) z Hz).
    + apply real_eq_of_zero_diff. intro k.
      rewrite (real_plus_proj _ _ k). rewrite (real_plus_proj _ _ k).
      rewrite (real_plus_proj _ _ k). rewrite (real_plus_proj _ _ k).
      ring.
Qed.

(* ===== 1. log 下界族 ===== *)

(* ① 主件：log u ≥ 1 − 1/u（eps 余量形）——两跳捷径 *)
Theorem evd_log_ge_inv_one_eps : forall (u : Real) (Hu : real_lt real_zero u)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_plus real_one (real_opp (real_inv_pos u Hu)))
          (real_plus (real_log u Hu) eps).
Proof.
  intros u Hu eps Heps.
  (* 阶段1：log_le（库件）施于 e^{−L}，L := log u *)
  assert (HLpos : real_lt real_zero (cauchy_real_exp (real_opp (real_log u Hu))))
    by apply cauchy_real_exp_pos.
  pose proof (RealInterfaceEnhancedMod.real_log_le_linear_eps
              (cauchy_real_exp (real_opp (real_log u Hu))) eps
              HLpos Heps) as H0.
  (* H0 : log(e^{−L}) ≤ (e^{−L} + (−1)) + eps *)
  assert (Hleft : real_eq (real_log (cauchy_real_exp (real_opp (real_log u Hu))) HLpos)
                          (real_opp (real_log u Hu)))
    by exact (log_inv_exp_neg_thm (real_opp (real_log u Hu)) HLpos).
  assert (HE : real_eq (cauchy_real_exp (real_opp (real_log u Hu)))
                       (real_inv_pos u Hu)).
  { apply real_eq_trans
      with (real_inv_pos (cauchy_real_exp (real_log u Hu))
                         (cauchy_real_exp_pos (real_log u Hu))).
    - exact (exp_neg_recip (real_log u Hu)
               (cauchy_real_exp_pos (real_log u Hu))).
    - apply real_inv_pos_ext. exact (cw_log_exp_right u Hu). }
  (* 运输 → −L ≤ (I + −1) + eps，I := 1/u *)
  assert (H1 : real_le (real_opp (real_log u Hu))
                       (real_plus (real_plus (real_inv_pos u Hu)
                                             (real_opp real_one)) eps)).
  { apply real_le_trans
      with (real_log (cauchy_real_exp (real_opp (real_log u Hu))) HLpos).
    - apply RealSetoid.real_eq_le. apply real_eq_sym. exact Hleft.
    - apply real_le_trans with
        (real_plus (real_plus (cauchy_real_exp (real_opp (real_log u Hu)))
                              (real_opp real_one))
                   eps).
      + exact H0.
      + apply RealSetoid.real_eq_le.
        apply (RealSetoid.real_eq_plus_compat
                 (real_plus (cauchy_real_exp (real_opp (real_log u Hu)))
                            (real_opp real_one))
                 eps
                 (real_plus (real_inv_pos u Hu) (real_opp real_one))
                 eps).
        * apply (RealSetoid.real_eq_plus_compat
                   (cauchy_real_exp (real_opp (real_log u Hu)))
                   (real_opp real_one)
                   (real_inv_pos u Hu) (real_opp real_one)).
          -- exact HE.
          -- apply real_eq_refl.
        * apply real_eq_refl. }
  (* 阶段2：加法代数。两侧加 L：(−L)+L ≤ (I−1)+eps+L，
     左端 == 0、右端 == I−1+eps+L == L+eps−(1−I) 逐点 ring 换形 *)
  assert (H2 : real_le (real_plus (real_opp (real_log u Hu))
                                  (real_log u Hu))
                       (real_plus (real_plus (real_plus (real_inv_pos u Hu)
                                                        (real_opp real_one))
                                             eps)
                                  (real_log u Hu))).
  { apply real_le_plus_compat.
    - exact H1.
    - apply real_le_refl. }
  apply real_le_trans with
    (real_plus (real_plus (real_opp (real_log u Hu)) (real_log u Hu))
               (real_plus real_one (real_opp (real_inv_pos u Hu)))).
  - (* 1−I == (−L+L)+(1−I)：等元入链（显式项点态恒等） *)
    apply RealSetoid.real_eq_le.
    apply real_eq_of_zero_diff. intro k.
    rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
    rewrite (real_plus_proj
               (real_plus (real_opp (real_log u Hu)) (real_log u Hu))
               (real_plus real_one (real_opp (real_inv_pos u Hu))) k).
    rewrite (real_plus_proj (real_opp (real_log u Hu)) (real_log u Hu) k).
    rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
    rewrite (real_opp_proj (real_inv_pos u Hu) k).
    rewrite (real_opp_proj (real_log u Hu) k).
    rewrite (real_const_proj 1 k). ring.
  - apply real_le_trans with
      (real_plus
         (real_plus (real_plus (real_plus (real_inv_pos u Hu) (real_opp real_one))
                               eps)
                    (real_log u Hu))
         (real_plus real_one (real_opp (real_inv_pos u Hu)))).
    + apply real_le_plus_compat.
      * exact H2.
      * apply real_le_refl.
    + (* (I−1+eps+L)+(1−I) == L+eps：等元出链（显式项点态恒等） *)
      apply RealSetoid.real_eq_le.
      apply real_eq_of_zero_diff. intro k.
      rewrite (real_plus_proj
                 (real_plus
                    (real_plus (real_plus (real_inv_pos u Hu) (real_opp real_one))
                               eps)
                    (real_log u Hu))
                 (real_plus real_one (real_opp (real_inv_pos u Hu))) k).
      rewrite (real_plus_proj
                 (real_plus (real_plus (real_inv_pos u Hu) (real_opp real_one))
                            eps)
                 (real_log u Hu) k).
      rewrite (real_plus_proj
                 (real_plus (real_inv_pos u Hu) (real_opp real_one)) eps k).
      rewrite (real_plus_proj (real_inv_pos u Hu) (real_opp real_one) k).
      rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
      rewrite (real_plus_proj (real_log u Hu) eps k).
      rewrite (real_opp_proj (real_inv_pos u Hu) k).
      rewrite (real_opp_proj real_one k).
      rewrite (real_const_proj 1 k). ring.
Qed.

(* ① B 形（Bishop 完成引理单步直连） *)
Corollary evd_log_ge_inv_one_B : forall (u : Real) (Hu : real_lt real_zero u),
  real_le_b (real_plus real_one (real_opp (real_inv_pos u Hu)))
            (real_log u Hu).
Proof.
  intros u Hu. apply real_le_closure_b_one.
  intros eps Heps. exact (evd_log_ge_inv_one_eps u Hu eps Heps).
Qed.

(* ② log(1+x) ≥ x/(1+x)（eps 形；① 于 u := 1+x 实例 + 乘法恒等换形） *)
Theorem evd_log_one_plus_ge_inv_eps : forall (x : Real)
  (Hx1 : real_lt real_zero (real_plus real_one x))
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult x (real_inv_pos (real_plus real_one x) Hx1))
          (real_plus (real_log (real_plus real_one x) Hx1) eps).
Proof.
  intros x Hx1 eps Heps.
  pose proof (evd_log_ge_inv_one_eps (real_plus real_one x) Hx1 eps Heps) as H.
  apply real_le_trans with
    (real_plus real_one
               (real_opp (real_inv_pos (real_plus real_one x) Hx1))).
  - (* x·inv(1+x) == 1 − inv(1+x)（(1+x)·inv == 1 逐点恒等） *)
    apply RealSetoid.real_eq_le.
    apply real_eq_trans with
      (real_plus (real_mult (real_plus real_one x)
                            (real_inv_pos (real_plus real_one x) Hx1))
                 (real_opp (real_inv_pos (real_plus real_one x) Hx1))).
    + (* x·I == (1+x)·I − I：分配律点态恒等（零 Qinv 进环） *)
      apply real_eq_of_zero_diff. intro k.
      rewrite (real_mult_proj x (real_inv_pos (real_plus real_one x) Hx1) k).
      rewrite (real_plus_proj
                 (real_mult (real_plus real_one x)
                            (real_inv_pos (real_plus real_one x) Hx1))
                 (real_opp (real_inv_pos (real_plus real_one x) Hx1)) k).
      rewrite (real_mult_proj (real_plus real_one x)
                 (real_inv_pos (real_plus real_one x) Hx1) k).
      rewrite (real_plus_proj real_one x k).
      rewrite (real_opp_proj (real_inv_pos (real_plus real_one x) Hx1) k).
      rewrite (real_const_proj 1 k). ring.
    + (* (1+x)·I == 1（inv 正确性）⟹ 整体 == 1 − I *)
      apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_plus real_one x)
                          (real_inv_pos (real_plus real_one x) Hx1))
               (real_opp (real_inv_pos (real_plus real_one x) Hx1))
               real_one
               (real_opp (real_inv_pos (real_plus real_one x) Hx1))).
      * exact (real_inv_pos_correct (real_plus real_one x) Hx1).
      * apply real_eq_refl.
  - exact H.
Qed.

(* ② B 形 *)
Corollary evd_log_one_plus_ge_inv_B : forall (x : Real)
  (Hx1 : real_lt real_zero (real_plus real_one x)),
  real_le_b (real_mult x (real_inv_pos (real_plus real_one x) Hx1))
            (real_log (real_plus real_one x) Hx1).
Proof.
  intros x Hx1. apply real_le_closure_b_one.
  intros eps Heps. exact (evd_log_one_plus_ge_inv_eps x Hx1 eps Heps).
Qed.

(* ===== 2. exp 上界族 ===== *)

(* ③ 族底：x ≤ 0 ⟹ e^x ≤ 1（单调 + e^0==1；全库首件） *)
Theorem evd_exp_le_one_of_le_zero : forall x : Real,
  real_le x real_zero -> real_le (cauchy_real_exp x) real_one.
Proof.
  intros x Hx.
  apply real_le_trans with (cauchy_real_exp real_zero).
  - exact (real_exp_le_mono x real_zero Hx).
  - apply RealSetoid.real_eq_le. exact cauchy_real_exp_zero.
Qed.

(* ① B 形升格：0<x<1 ⟹ e^x ≤_B 1/(1−x)（库件 plain 形直连） *)
Theorem evd_exp_le_inv_one_minus_B : forall (x : Real)
  (Hx0 : real_lt real_zero x) (Hx1 : real_lt x real_one),
  real_le_b (cauchy_real_exp x)
            (real_inv_pos (real_plus real_one (real_opp x))
                          (real_lt_opp_plus x real_one Hx1)).
Proof.
  intros x Hx0 Hx1. apply real_le_to_le_b.
  exact (real_exp_le_inv_one_minus x Hx0 Hx1).
Qed.

(* ===== 3. 对偶环：换轴互推双桥 ===== *)

(* 桥A：log≥族 ⟹ exp≤族之「前逆」B 形：1−t ≤_B 1/e^t（0<t<1）。
   全程加法代数 + evd_le_lt_double 严格化；B 倒数反单调待续见头注。 *)
Theorem evd_dual_log_ge_gives_exp_pre_inv_B :
  forall (t : Real) (Ht1 : real_lt real_zero t) (Ht2 : real_lt t real_one),
  real_le_b (real_plus real_one (real_opp t))
            (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)).
Proof.
  intros t Ht1 Ht2. unfold real_le_b. intros d Hd.
  assert (Hh : real_lt real_zero
                 (real_mult d (real_inv_pos pnk_two pnk_two_pos))).
  { apply real_mult_positive.
    - exact Hd.
    - apply real_inv_pos_pos. }
  (* 家族实例：u := e^t（正性在盘），eps := d/2 *)
  pose proof (evd_log_ge_inv_one_eps (cauchy_real_exp t)
              (cauchy_real_exp_pos t)
              (real_mult d (real_inv_pos pnk_two pnk_two_pos)) Hh) as Hfam.
  (* log(e^t) == t 换右元 *)
  assert (Hfam' : real_le
                    (real_plus real_one
                       (real_opp (real_inv_pos (cauchy_real_exp t)
                                               (cauchy_real_exp_pos t))))
                    (real_plus t
                       (real_mult d (real_inv_pos pnk_two pnk_two_pos)))).
  { apply real_le_trans with
      (real_plus (real_log (cauchy_real_exp t) (cauchy_real_exp_pos t))
                 (real_mult d (real_inv_pos pnk_two pnk_two_pos))).
    - exact Hfam.
    - apply RealSetoid.real_eq_le.
      apply (RealSetoid.real_eq_plus_compat
               (real_log (cauchy_real_exp t) (cauchy_real_exp_pos t))
               (real_mult d (real_inv_pos pnk_two pnk_two_pos))
               t
               (real_mult d (real_inv_pos pnk_two pnk_two_pos))).
      + exact (log_inv_exp_neg_thm t (cauchy_real_exp_pos t)).
      + apply real_eq_refl. }
  (* 加法代数：两侧加 W := 1/e^t + (−t) *)
  assert (Hstep : real_le (real_plus real_one (real_opp t))
                          (real_plus (real_inv_pos (cauchy_real_exp t)
                                                   (cauchy_real_exp_pos t))
                                     (real_mult d
                                        (real_inv_pos pnk_two pnk_two_pos)))).
  { apply real_le_trans with
      (real_plus (real_plus real_one
                             (real_opp (real_inv_pos (cauchy_real_exp t)
                                                     (cauchy_real_exp_pos t))))
                 (real_plus (real_inv_pos (cauchy_real_exp t)
                                         (cauchy_real_exp_pos t))
                            (real_opp t))).
    - apply RealSetoid.real_eq_le.
      apply real_eq_of_zero_diff. intro k.
      rewrite (real_plus_proj real_one (real_opp t) k).
      rewrite (real_plus_proj
                 (real_plus real_one (real_opp (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))))
                 (real_plus (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) (real_opp t)) k).
      rewrite (real_plus_proj real_one (real_opp (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))) k).
      rewrite (real_plus_proj (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) (real_opp t) k).
      rewrite (real_opp_proj (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) k).
      rewrite (real_opp_proj t k).
      rewrite (real_const_proj 1 k). ring.
    - apply real_le_trans with
        (real_plus (real_plus t
                               (real_mult d
                                  (real_inv_pos pnk_two pnk_two_pos)))
                   (real_plus (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))
                              (real_opp t))).
      + apply real_le_plus_compat.
        * exact Hfam'.
        * apply real_le_refl.
      + apply RealSetoid.real_eq_le.
        apply real_eq_of_zero_diff. intro k.
        rewrite (real_plus_proj (real_plus t (real_mult d (real_inv_pos pnk_two pnk_two_pos)))
                   (real_plus (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) (real_opp t)) k).
        rewrite (real_plus_proj t (real_mult d (real_inv_pos pnk_two pnk_two_pos)) k).
        rewrite (real_plus_proj (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) (real_opp t) k).
        rewrite (real_plus_proj (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t)) (real_mult d (real_inv_pos pnk_two pnk_two_pos)) k).
        rewrite (real_opp_proj t k).
        ring. }
  (* 严格化：h+h == d（序级代数：分配 + inv2+inv2==2·inv2==1）+ evd_le_lt_double *)
  assert (Hhd : real_eq (real_plus
                           (real_mult d (real_inv_pos pnk_two pnk_two_pos))
                           (real_mult d (real_inv_pos pnk_two pnk_two_pos)))
                        d).
  { apply real_eq_trans with
      (real_mult d
                 (real_plus (real_inv_pos pnk_two pnk_two_pos)
                            (real_inv_pos pnk_two pnk_two_pos))).
    - apply real_eq_of_zero_diff. intro k.
      rewrite (real_plus_proj
                 (real_mult d (real_inv_pos pnk_two pnk_two_pos))
                 (real_mult d (real_inv_pos pnk_two pnk_two_pos)) k).
      rewrite (real_mult_proj d
                 (real_plus (real_inv_pos pnk_two pnk_two_pos)
                            (real_inv_pos pnk_two pnk_two_pos)) k).
      rewrite (real_plus_proj
                 (real_inv_pos pnk_two pnk_two_pos)
                 (real_inv_pos pnk_two pnk_two_pos) k).
      rewrite (real_mult_proj d (real_inv_pos pnk_two pnk_two_pos) k).
      ring.
    - apply real_eq_trans with
        (real_mult d (real_mult pnk_two (real_inv_pos pnk_two pnk_two_pos))).
      + apply (RealSetoid.real_eq_mult_compat d
                 (real_plus (real_inv_pos pnk_two pnk_two_pos)
                            (real_inv_pos pnk_two pnk_two_pos))
                 d
                 (real_mult pnk_two (real_inv_pos pnk_two pnk_two_pos))).
        * apply real_eq_refl.
        * apply real_eq_of_zero_diff. intro k.
          rewrite (real_plus_proj
                     (real_inv_pos pnk_two pnk_two_pos)
                     (real_inv_pos pnk_two pnk_two_pos) k).
          rewrite (real_mult_proj pnk_two
                     (real_inv_pos pnk_two pnk_two_pos) k).
          rewrite (pnk_two_proj k). ring.
      + apply real_eq_trans with (real_mult d real_one).
        * apply (RealSetoid.real_eq_mult_compat d
                   (real_mult pnk_two (real_inv_pos pnk_two pnk_two_pos))
                   d
                   real_one).
          -- apply real_eq_refl.
          -- exact (real_inv_pos_correct pnk_two pnk_two_pos).
        * apply real_mult_one. }
  apply (real_lt_eq_lt (real_plus real_one (real_opp t))
                       (real_plus (real_inv_pos (cauchy_real_exp t)
                                                (cauchy_real_exp_pos t))
                                  (real_plus
                                     (real_mult d
                                        (real_inv_pos pnk_two pnk_two_pos))
                                     (real_mult d
                                        (real_inv_pos pnk_two pnk_two_pos))))
                       (real_plus (real_inv_pos (cauchy_real_exp t)
                                                (cauchy_real_exp_pos t)) d)).
  - exact (evd_le_lt_double (real_plus real_one (real_opp t))
             (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))
             (real_mult d (real_inv_pos pnk_two pnk_two_pos)) Hh Hstep).
  - apply (RealSetoid.real_eq_plus_compat
             (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))
             (real_plus
                (real_mult d (real_inv_pos pnk_two pnk_two_pos))
                (real_mult d (real_inv_pos pnk_two pnk_two_pos)))
             (real_inv_pos (cauchy_real_exp t) (cauchy_real_exp_pos t))
             d).
    + apply real_eq_refl.
    + exact Hhd.
Qed.

(* 桥B：exp≤族（Or 形）⟹ log≥族（Or 形），u ≥ 1 支。
   路线：t := 1−inv(u) ∈ (0,1)，exp≤ 给 e^t ≤ inv(1−t) == u，
   Or 两支分别走 log 严单 / exp 单（evd_exp_inj + evd_log_ext）。 *)
Theorem evd_dual_exp_le_gives_log_ge :
  forall (Hexp : forall (t : Real) (Ht1 : real_lt real_zero t)
                                            (Ht2 : real_lt t real_one),
            real_le (cauchy_real_exp t)
                    (real_inv_pos (real_plus real_one (real_opp t))
                                  (real_lt_opp_plus t real_one Ht2)))
  (u : Real) (Hu : real_lt real_zero u) (Hu1 : real_le real_one u),
  real_le (real_plus real_one (real_opp (real_inv_pos u Hu)))
          (real_log u Hu).
Proof.
  intros Hexp u Hu Hu1. unfold real_le in Hu1.
  destruct Hu1 as [Hult | Hueq].
  - (* 1 < u 支 *)
    pose proof (real_inv_pos_pos u Hu) as HIUp.
    (* inv u < 1 *)
    assert (HIU1 : real_lt (real_inv_pos u Hu) real_one).
    { apply (real_lt_eq_lt (real_inv_pos u Hu)
                           (real_inv_pos real_one real_lt_zero_one) real_one).
      - exact (real_inv_pos_lt_contra real_one u real_lt_zero_one Hu Hult).
      - exact evd_inv_one. }
    (* t := 1 − inv u ∈ (0,1) *)
    assert (Ht1 : real_lt real_zero (real_plus real_one (real_opp (real_inv_pos u Hu))))
      by exact (real_lt_opp_plus (real_inv_pos u Hu) real_one HIU1).
    assert (Ht2 : real_lt (real_plus real_one (real_opp (real_inv_pos u Hu)))
                          real_one).
    { destruct (evd_lt_opp_flip (real_inv_pos u Hu) HIUp)
        as [mu [Hmu [N HN]]].
      exists mu. split.
      - exact Hmu.
      - exists N. intros n Hn. apply Qlt_to_QltT.
        apply (Qlt_le_trans mu
                 (projT1 real_zero n - projT1 (real_opp (real_inv_pos u Hu)) n)).
        + exact (QltT_to_Qlt mu
                   (projT1 real_zero n
                      - projT1 (real_opp (real_inv_pos u Hu)) n) (HN n Hn)).
        + apply qeq_le.
          rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) n).
          rewrite (real_opp_proj (real_inv_pos u Hu) n).
          rewrite (real_const_proj 1 n). rewrite (real_const_proj 0 n). ring. }
    (* exp≤族 @ t：e^t ≤ inv(1−t)；1−t == inv u、inv(inv u) == u *)
    assert (Hkey : real_le (cauchy_real_exp
                              (real_plus real_one
                                         (real_opp (real_inv_pos u Hu)))) u).
    { assert (Hst := Hexp (real_plus real_one (real_opp (real_inv_pos u Hu)))
                          Ht1 Ht2).
      apply real_le_trans with
        (real_inv_pos (real_plus real_one
                                 (real_opp (real_plus real_one
                                                      (real_opp (real_inv_pos u Hu)))))
                      (real_lt_opp_plus (real_plus real_one
                                                   (real_opp (real_inv_pos u Hu)))
                                        real_one Ht2)).
      - exact Hst.
      - apply RealSetoid.real_eq_le.
        apply real_eq_trans with
          (real_inv_pos (real_inv_pos u Hu) (real_inv_pos_pos u Hu)).
        + apply real_inv_pos_ext.
          apply real_eq_of_zero_diff. intro k.
          rewrite (real_plus_proj real_one (real_opp (real_plus real_one (real_opp (real_inv_pos u Hu)))) k).
          rewrite (real_opp_proj (real_plus real_one (real_opp (real_inv_pos u Hu))) k).
          rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
          rewrite (real_opp_proj (real_inv_pos u Hu) k).
          rewrite (real_const_proj 1 k). ring.
        + exact (evd_inv_inv u Hu). }
    unfold real_le in Hkey. destruct Hkey as [Hkeylt | Hkeyeq].
    + (* 严格支：log 严单 *)
      apply real_le_trans with
        (real_log (cauchy_real_exp
                     (real_plus real_one (real_opp (real_inv_pos u Hu))))
                  (cauchy_real_exp_pos
                     (real_plus real_one (real_opp (real_inv_pos u Hu))))).
      * apply RealSetoid.real_eq_le.
        apply real_eq_trans with
          (real_plus real_one (real_opp (real_inv_pos u Hu))).
        -- apply real_eq_of_zero_diff. intro k.
           rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
           rewrite (real_opp_proj (real_inv_pos u Hu) k).
           rewrite (real_const_proj 1 k). ring.
        -- apply real_eq_sym.
           exact (log_inv_exp_neg_thm
                    (real_plus real_one (real_opp (real_inv_pos u Hu)))
                    (cauchy_real_exp_pos
                       (real_plus real_one (real_opp (real_inv_pos u Hu))))).
      * unfold real_le. left.
        apply real_log_lt_mono. exact Hkeylt.
    + (* 相等支：log u == log(e^t) == t == 1 − inv u *)
      assert (Hlogu : real_eq (real_log u Hu)
                              (real_log
                                 (cauchy_real_exp
                                    (real_plus real_one
                                                 (real_opp (real_inv_pos u Hu))))
                                 (cauchy_real_exp_pos
                                    (real_plus real_one
                                                 (real_opp (real_inv_pos u Hu)))))).
      { apply evd_log_ext. exact (real_eq_sym _ _ Hkeyeq). }
      apply RealSetoid.real_eq_le.
      apply real_eq_trans with
        (real_log (cauchy_real_exp
                     (real_plus real_one (real_opp (real_inv_pos u Hu))))
                  (cauchy_real_exp_pos
                     (real_plus real_one (real_opp (real_inv_pos u Hu))))).
      * apply real_eq_trans with
          (real_plus real_one (real_opp (real_inv_pos u Hu))).
      { apply real_eq_of_zero_diff. intro k.
        rewrite (real_plus_proj real_one (real_opp (real_inv_pos u Hu)) k).
        rewrite (real_opp_proj (real_inv_pos u Hu) k).
        rewrite (real_const_proj 1 k). ring. }
      { exact (real_eq_sym _ _
                 (log_inv_exp_neg_thm
                    (real_plus real_one (real_opp (real_inv_pos u Hu)))
                    (cauchy_real_exp_pos
                       (real_plus real_one
                                    (real_opp (real_inv_pos u Hu)))))). }
      * exact (real_eq_sym _ _ Hlogu).

  - (* u == 1 支：两侧归零 *)
    assert (Hinv1 : real_eq (real_inv_pos u Hu)
                            (real_inv_pos real_one real_lt_zero_one)).
    { apply real_inv_pos_ext. apply real_eq_sym. exact Hueq. }
    assert (Hlog1 : real_eq (real_log u Hu)
                            (real_log real_one real_lt_zero_one)).
    { apply evd_log_ext. apply real_eq_sym. exact Hueq. }
    apply RealSetoid.real_eq_le.
    apply real_eq_trans with real_zero.
    + (* 1 − inv u == 0：compat 链（refl + Hinv1 的 opp_compat + 逐点归零） *)
      apply real_eq_trans with (real_plus real_one (real_opp real_one)).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_opp (real_inv_pos u Hu))
                 real_one
                 (real_opp real_one)).
        -- apply real_eq_refl.
        -- apply real_eq_trans with
             (real_opp (real_inv_pos real_one real_lt_zero_one)).
           ++ exact (RealSetoid.real_eq_opp_compat
                       (real_inv_pos u Hu)
                       (real_inv_pos real_one real_lt_zero_one)
                       Hinv1).
           ++ exact (RealSetoid.real_eq_opp_compat
                       (real_inv_pos real_one real_lt_zero_one)
                       real_one
                       evd_inv_one).
      * apply real_eq_of_zero_diff. intro k.
        rewrite (real_plus_proj real_one (real_opp real_one) k).
        rewrite (real_opp_proj real_one k).
        rewrite (real_const_proj 1 k).
        rewrite (real_const_proj 0 k).
        ring.
    + apply real_eq_sym.
      apply real_eq_trans with (real_log real_one real_lt_zero_one).
      * exact Hlog1.
      * exact (log_inv_one_thm real_lt_zero_one).
Qed.

(* ===== 4. evd 下界 × pnk 上界夹逼（三常数引擎接口预埋） ===== *)

(* B 形左乘正数放大器（real_mult_lt_compat_l 的 B 形升格，
   半松量 ε-配平）——夹逼与后续 C3 母定理的公共接口 *)
Lemma evd_le_b_mult_pos_l : forall a b c : Real,
  real_le_b a b -> real_lt real_zero c ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab Hc. unfold real_le_b in *. intros d Hd.
  assert (Hic : real_lt real_zero (real_inv_pos c Hc))
    by apply real_inv_pos_pos.
  (* Hab 于 eps := d·inv(c) *)
  pose proof (Hab (real_mult d (real_inv_pos c Hc))
              (real_mult_positive d (real_inv_pos c Hc) Hd Hic)) as Hlt0.
  assert (Hlt1 : real_lt (real_mult c a)
                         (real_mult c (real_plus b
                            (real_mult d (real_inv_pos c Hc))))).
  { exact (real_mult_lt_compat_l _ _ c Hlt0 Hc). }
  (* 右端换形：c·(b + d·inv c) == c·b + d（分配点态 + inv 正确性序级链） *)
  assert (Hcd : real_eq (real_mult c (real_mult d (real_inv_pos c Hc))) d).
  { apply real_eq_trans with
      (real_mult d (real_mult c (real_inv_pos c Hc))).
    - apply real_eq_trans with
        (real_mult (real_mult c d) (real_inv_pos c Hc)).
      + apply real_eq_of_zero_diff. intro k.
        rewrite (real_mult_proj c
                   (real_mult d (real_inv_pos c Hc)) k).
        rewrite (real_mult_proj
                   (real_mult c d) (real_inv_pos c Hc) k).
        rewrite (real_mult_proj c d k).
        rewrite (real_mult_proj d (real_inv_pos c Hc) k).
        ring.
      + apply real_eq_trans with
          (real_mult (real_mult d c) (real_inv_pos c Hc)).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult c d) (real_inv_pos c Hc)
                   (real_mult d c) (real_inv_pos c Hc)).
          -- apply real_mult_comm.
          -- apply real_eq_refl.
        * apply real_eq_of_zero_diff. intro k.
          rewrite (real_mult_proj
                     (real_mult d c) (real_inv_pos c Hc) k).
          rewrite (real_mult_proj d
                     (real_mult c (real_inv_pos c Hc)) k).
          rewrite (real_mult_proj d c k).
          rewrite (real_mult_proj c (real_inv_pos c Hc) k).
          ring.
    - apply real_eq_trans with (real_mult d real_one).
      + apply (RealSetoid.real_eq_mult_compat d
                 (real_mult c (real_inv_pos c Hc))
                 d
                 real_one).
        * apply real_eq_refl.
        * exact (real_inv_pos_correct c Hc).
      + apply real_mult_one. }
  apply (real_lt_eq_lt (real_mult c a)
                       (real_mult c (real_plus b
                          (real_mult d (real_inv_pos c Hc))))
                       (real_plus (real_mult c b) d)).
  - exact Hlt1.
  - apply real_eq_trans with
      (real_plus (real_mult c b)
                 (real_mult c (real_mult d (real_inv_pos c Hc)))).
    + apply real_eq_of_zero_diff. intro k.
      rewrite (real_mult_proj c
                 (real_plus b (real_mult d (real_inv_pos c Hc))) k).
      rewrite (real_plus_proj b (real_mult d (real_inv_pos c Hc)) k).
      rewrite (real_plus_proj (real_mult c b)
                 (real_mult c (real_mult d (real_inv_pos c Hc))) k).
      rewrite (real_mult_proj c b k).
      rewrite (real_mult_proj c
                 (real_mult d (real_inv_pos c Hc)) k).
      ring.
    + apply (RealSetoid.real_eq_plus_compat (real_mult c b)
               (real_mult c (real_mult d (real_inv_pos c Hc)))
               (real_mult c b) d).
      * apply real_eq_refl.
      * exact Hcd.
Qed.

(* 夹逼上侧：pnk_core @ (1+x) 直实例（零加工） *)
Corollary evd_log_one_plus_pnk_upper_B : forall (x : Real)
  (Hx1 : real_lt real_zero (real_plus real_one x)),
  real_le_b (real_mult (real_plus (real_plus real_one x) real_one)
                       (real_mult pnk_two
                                  (real_log (real_plus real_one x) Hx1)))
            (real_mult (real_plus (real_plus real_one x) (real_opp real_one))
                       (real_plus (real_plus real_one x) pnk_three)).
Proof.
  intros x Hx1. exact (pnk_core (real_plus real_one x) Hx1).
Qed.

(* 夹逼区间件：0 < 1+x ⟹
   (x+2)·2·(x/(1+x)) ≤_B (x+2)·2·log(1+x) ≤_B x(x+4)
   ——evd 下界（左乘放大）× pnk 上界，中间量显式在链 *)
Corollary evd_log_one_plus_sandwich_B : forall (x : Real)
  (Hx1 : real_lt real_zero (real_plus real_one x)),
  real_le_b (real_mult (real_plus (real_plus real_one x) real_one)
                       (real_mult pnk_two
                          (real_mult x
                             (real_inv_pos (real_plus real_one x) Hx1))))
            (real_mult (real_plus (real_plus real_one x) (real_opp real_one))
                       (real_plus (real_plus real_one x) pnk_three)).
Proof.
  intros x Hx1.
  apply (real_le_b_trans
           (real_mult (real_plus (real_plus real_one x) real_one)
                      (real_mult pnk_two
                         (real_mult x
                            (real_inv_pos (real_plus real_one x) Hx1))))
           (real_mult (real_plus (real_plus real_one x) real_one)
                      (real_mult pnk_two
                                 (real_log (real_plus real_one x) Hx1)))).
  - apply evd_le_b_mult_pos_l.
    + apply evd_le_b_mult_pos_l.
      * apply evd_log_one_plus_ge_inv_B.
      * exact pnk_two_pos.
    + apply (real_lt_eq_lt real_zero
               (real_plus real_one (real_plus real_one x))
               (real_plus (real_plus real_one x) real_one)).
      * exact (real_one_plus_pos (real_plus real_one x) Hx1).
      * apply real_eq_of_zero_diff. intro k.
        rewrite (real_plus_proj real_one (real_plus real_one x) k).
        rewrite (real_plus_proj (real_plus real_one x) real_one k).
        rewrite (real_plus_proj real_one x k).
        rewrite (real_const_proj 1 k). ring.
  - apply evd_log_one_plus_pnk_upper_B.
Qed.

(* ===== 5. 公理面核验 ===== *)
Print Assumptions evd_log_ge_inv_one_eps.
Print Assumptions evd_log_one_plus_ge_inv_eps.
Print Assumptions evd_exp_le_one_of_le_zero.
Print Assumptions evd_exp_le_inv_one_minus_B.
Print Assumptions evd_dual_log_ge_gives_exp_pre_inv_B.
Print Assumptions evd_dual_exp_le_gives_log_ge.
Print Assumptions evd_le_b_mult_pos_l.
Print Assumptions evd_log_one_plus_sandwich_B.
