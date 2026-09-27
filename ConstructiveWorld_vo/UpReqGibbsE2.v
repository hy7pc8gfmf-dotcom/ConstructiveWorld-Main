(* ==========================================================================)
   UpReqGibbsE2.v —— Gibbs 不等式族的 Bishop 形序实例化与 Gibbs 等式的有限具体路线
   使命：本件形式化两族结果。其一，Gibbs 不等式族的 Bishop 形序（real_le_b）实例
     化：Bishop 序代数基元（gibbsd_lt_add_opp_r / gibbsd_le_b_opp /
     gibbsd_le_b_id_l / gibbsd_minus_flip / gibbsd_le_b_mult_pos_r）、逐点 Gibbs
     切线 gibbsd_gibbs_pointwise_B、KL 非负 gibbsd_gibbs_inequality 与交叉熵分解
     gibbsd_cross_entropy_decomp（H(p,q) == S[p] + KL(p‖q) 的逐点恒等分解）。
     其二，Gibbs 等式的有限具体路线：Q 层半分 helper（gibbe2_Q_half_pos /
     gibbe2_Q_half_lt）、le_b 补层序机（gibbe2_le_b_id_r / gibbe2_le_b_antisym /
     gibbe2_clamp_head / gibbe2_clamp_head_r）、逐项钳零与有限载体提取
     （gibbe2_list_sum_zero_extract_bool）、逐点切点等式 gibbe2_kl_zero_tangent_eq，
     以及主件 gibbe2_gibbs_equality_bool（KL==0 蕴含逐点 p==q）。
   依赖：S01_BaseRing 至 S15_TailFEPUp 基座链（十五件顺序直调）、UpRealLeB、
     UpReqDist；Stdlib List、QArith.QArith、QArith.Qabs、QArith.Qround、Lia。
   对标：Gibbs 不等式 KL(p‖q) ≥ 0 与交叉熵分解 H(p,q) = S[p] + KL(p‖q) 的构造性
     有限离散对应（Bishop 序谓词形）。
   构造性：全件 Qed 闭合、零承认词面、零公理；序谓词与等词全 Set 值（real_le_b /
     real_eq / real_lt），零 Prop 泄露；零 Or 完成、零三分、零 LPO；有限载体
     可计算提取。诚实边界：log 线性等价桥需强三分/LPO、构造性不可证——
     gibbe2_gibbs_equality_bool 以显式前提注入该桥，无条件形式不主张。
   编译配方：Rocq 9.1 直调 coqc -q -Q . "" -native-compiler no，cpu_guard 包裹限载。
   ========================================================================== *)
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
Require Import UpRealLeB.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 1：Bishop 序代数基元（real_le_b 上的 opp / 数乘 / 换形）        *)
(* ============================================================ *)

(* A1：lt 右端 −eps → +eps 平移（opp 反向件地基） *)
Lemma gibbsd_lt_add_opp_r : forall x y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus x (real_opp e)) y ->
  real_lt x (real_plus y e).
Proof.
  intros x y e Heps Hlt.
  apply (RealSetoid.real_lt_compat
           (real_plus e (real_plus x (real_opp e))) x
           (real_plus e y) (real_plus y e)).
  - apply real_eq_sym.
    apply (real_eq_trans x (real_plus x (real_plus (real_opp e) e))
                         (real_plus e (real_plus x (real_opp e)))).
    + apply (real_eq_trans x (real_plus x real_zero)
                           (real_plus x (real_plus (real_opp e) e))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat x real_zero x
                 (real_plus (real_opp e) e)).
        -- apply real_eq_refl.
        -- apply (real_eq_trans real_zero (real_plus e (real_opp e))
                     (real_plus (real_opp e) e)).
           ++ apply real_eq_sym. apply real_plus_opp.
           ++ apply real_plus_comm.
    + apply (real_eq_trans (real_plus x (real_plus (real_opp e) e))
                           (real_plus (real_plus x (real_opp e)) e)
                           (real_plus e (real_plus x (real_opp e)))).
      * apply real_plus_assoc.
      * apply real_plus_comm.
  - apply real_plus_comm.
  - exact (real_lt_plus_translate e (real_plus x (real_opp e)) y Hlt).
Qed.

(* A2：Bishop 序 opp 反向（req 层 opp_le_compat 的 le_b 对位） *)
Lemma gibbsd_le_b_opp : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply gibbsd_lt_add_opp_r.
  - exact Heps.
  - apply (RealSetoid.real_lt_compat
             (real_opp (real_plus b eps))
             (real_plus (real_opp b) (real_opp eps))
             (real_opp a) (real_opp a)).
    + exact (real_opp_plus b eps).
    + apply real_eq_refl.
    + exact (real_opp_lt_compat a (real_plus b eps) (H eps Heps)).
Qed.

(* A3：Bishop 序左端 real_eq 换形（req 层 le_id_l 的 le_b 对位） *)
Lemma gibbsd_le_b_id_l : forall a b c : Real,
  real_eq a b -> real_le_b b c -> real_le_b a c.
Proof.
  intros a b c Hab H eps Heps. unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat b a (real_plus c eps) (real_plus c eps)
           (real_eq_sym a b Hab) (real_eq_refl (real_plus c eps))
           (H eps Heps)).
Qed.

(* A5：minus 翻转恒等：−(a−b) == b−a（req 层 reqd_minus_one_flip 对位） *)
Lemma gibbsd_minus_flip : forall a b : Real,
  real_eq (real_opp (real_plus a (real_opp b)))
          (real_plus b (real_opp a)).
Proof.
  intros a b.
  apply (real_eq_trans (real_opp (real_plus a (real_opp b)))
                       (real_plus (real_opp a) (real_opp (real_opp b)))
                       (real_plus b (real_opp a))).
  - exact (real_opp_plus a (real_opp b)).
  - apply (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus (real_opp (real_opp b)) (real_opp a))
             (real_plus b (real_opp a))).
    + apply real_plus_comm.
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp (real_opp b)) (real_opp a)
               b (real_opp a)
               (real_opp_opp b) (real_eq_refl (real_opp a))).
Qed.

(* A4：Bishop 序右乘正数保序（req 层 req_le_mult_compat_r 的 le_b 对位） *)
Lemma gibbsd_le_b_mult_pos_r : forall c a b : Real,
  real_lt real_zero c -> real_le_b a b ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc H eps Heps. unfold real_le_b in H.
  set (e0 := real_mult eps (real_inv_pos c Hc)).
  assert (Hpos0 : real_lt real_zero e0).
  { exact (real_mult_positive eps (real_inv_pos c Hc) Heps
             (real_inv_pos_pos c Hc)). }
  apply (RealSetoid.real_lt_compat
           (real_mult c a) (real_mult c a)
           (real_mult c (real_plus b e0))
           (real_plus (real_mult c b) eps)).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_mult c (real_plus b e0))
             (real_plus (real_mult c b) (real_mult c e0))
             (real_plus (real_mult c b) eps)).
    + exact (real_distrib c b e0).
    + exact (RealSetoid.real_eq_plus_compat (real_mult c b) (real_mult c e0)
               (real_mult c b) eps
               (real_eq_refl (real_mult c b))
               (real_eq_trans
                  (real_mult c e0)
                  (real_mult eps (real_mult c (real_inv_pos c Hc))) eps
                  (real_eq_trans
                     (real_mult c e0)
                     (real_mult (real_mult eps c) (real_inv_pos c Hc))
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_eq_trans
                        (real_mult c e0)
                        (real_mult (real_mult c eps) (real_inv_pos c Hc))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc c eps (real_inv_pos c Hc))
                        (RealSetoid.real_eq_mult_compat
                           (real_mult c eps) (real_inv_pos c Hc)
                           (real_mult eps c) (real_inv_pos c Hc)
                           (real_mult_comm c eps)
                           (real_eq_refl (real_inv_pos c Hc))))
                     (real_eq_sym
                        (real_mult eps (real_mult c (real_inv_pos c Hc)))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc eps c (real_inv_pos c Hc))))
                  (real_eq_trans
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_mult eps real_one) eps
                     (RealSetoid.real_eq_mult_compat eps
                        (real_mult c (real_inv_pos c Hc)) eps real_one
                        (real_eq_refl eps) (real_inv_pos_correct c Hc))
                     (real_mult_one eps)))).
  - exact (real_mult_lt_compat_l a (real_plus b e0) c (H e0 Hpos0) Hc).
Qed.

(* ============================================================ *)
(* Part 2：逐点参数位消解前置（eq 层恒等）                              *)
(* ============================================================ *)

(* B0：p·(q/p) == q（分式约分；结合 / 交换 / inv_correct 链） *)
Lemma gibbsd_p_mult_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_mult q (real_inv_pos p Hp)))
           (real_mult q (real_mult p (real_inv_pos p Hp))) q).
  - apply (real_eq_trans
             (real_mult p (real_mult q (real_inv_pos p Hp)))
             (real_mult (real_mult p q) (real_inv_pos p Hp))
             (real_mult q (real_mult p (real_inv_pos p Hp)))).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans
               (real_mult (real_mult p q) (real_inv_pos p Hp))
               (real_mult (real_mult q p) (real_inv_pos p Hp))
               (real_mult q (real_mult p (real_inv_pos p Hp)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q)
                 (real_inv_pos p Hp) (real_mult q p) (real_inv_pos p Hp)
                 (real_mult_comm p q) (real_eq_refl (real_inv_pos p Hp))).
      * apply real_eq_sym.
        exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans
             (real_mult q (real_mult p (real_inv_pos p Hp)))
             (real_mult q real_one) q).
    + apply (RealSetoid.real_eq_mult_compat q
               (real_mult p (real_inv_pos p Hp)) q real_one
               (real_eq_refl q) (real_inv_pos_correct p Hp)).
    + exact (real_mult_one q).
Qed.

(* B1：p·(1 − q/p) == p − q（req 层 reqd_p_minus_ratio 的 Real 对位） *)
Lemma gibbsd_p_minus_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_plus real_one
                         (real_opp (real_mult q (real_inv_pos p Hp)))))
          (real_plus p (real_opp q)).
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_plus real_one
                      (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus (real_mult p real_one)
                      (real_mult p (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus p (real_opp q))).
  - exact (real_distrib p real_one
             (real_opp (real_mult q (real_inv_pos p Hp)))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult p real_one)
             (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
             p (real_opp q)).
    + exact (real_mult_one p).
    + apply (real_eq_trans
               (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
               (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))
               (real_opp q)).
      * apply real_eq_sym.
        exact (real_opp_mult p (real_mult q (real_inv_pos p Hp))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_mult p (real_mult q (real_inv_pos p Hp))) q
                 (gibbsd_p_mult_ratio p q Hp)).
Qed.

(* ============================================================ *)
(* Part 3：Bishop 和层机（real_list_sum 上的逐点→求和升格）             *)
(* ============================================================ *)

Lemma gibbsd_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.

Definition gibbsd_half : Real :=
  real_inv_pos (real_plus real_one real_one) gibbsd_two_pos.

Lemma gibbsd_half_pos : real_lt real_zero gibbsd_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) gibbsd_two_pos).
Qed.

(* 半分配：e·h + e·h == e（eps 对半拆分下的恒等式） *)
Lemma gibbsd_half_sum : forall e : Real,
  real_eq (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half)) e.
Proof.
  intro e.
  apply (real_eq_trans
           (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
           (real_mult e (real_plus gibbsd_half gibbsd_half)) e).
  - apply real_eq_sym.
    exact (real_distrib e gibbsd_half gibbsd_half).
  - apply (real_eq_trans
             (real_mult e (real_plus gibbsd_half gibbsd_half))
             (real_mult e real_one) e).
    + apply (RealSetoid.real_eq_mult_compat e
               (real_plus gibbsd_half gibbsd_half) e real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans (real_plus gibbsd_half gibbsd_half)
                 (real_mult (real_plus real_one real_one) gibbsd_half)
                 real_one).
        -- apply real_eq_sym.
           apply (real_eq_trans
                    (real_mult (real_plus real_one real_one) gibbsd_half)
                    (real_plus (real_mult real_one gibbsd_half)
                               (real_mult real_one gibbsd_half))
                    (real_plus gibbsd_half gibbsd_half)).
           ++ exact (real_eq_sym
                       (real_plus (real_mult real_one gibbsd_half)
                                  (real_mult real_one gibbsd_half))
                       (real_mult (real_plus real_one real_one) gibbsd_half)
                       (real_distrib_r_local real_one real_one gibbsd_half)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult real_one gibbsd_half)
                       (real_mult real_one gibbsd_half)
                       gibbsd_half gibbsd_half).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
        -- exact (real_inv_pos_correct (real_plus real_one real_one)
                    gibbsd_two_pos).
    + exact (real_mult_one e).
Qed.

(* C3：逐点 le_b ⟹ 求和 le_b（req 层 fsum_le 的 Bishop 对位；       *)
(*   eps 对半归纳：eps 拆 e/2 + e/2，nil 余量走 real_lt_plus_r_zero） *)
Lemma gibbsd_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l Hpt.
  unfold real_le_b.
  induction l as [| w l IH].
  - intros eps Heps. simpl.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - intros eps Heps. simpl.
    assert (Hpos : real_lt real_zero (real_mult eps gibbsd_half)).
    { exact (real_mult_positive eps gibbsd_half Heps gibbsd_half_pos). }
    assert (Ha : real_lt (f w)
                   (real_plus (g w) (real_mult eps gibbsd_half))).
    { exact (Hpt w (real_mult eps gibbsd_half) Hpos). }
    assert (Ht : real_lt (real_list_sum X f l)
                   (real_plus (real_list_sum X g l)
                              (real_mult eps gibbsd_half))).
    { exact (IH (real_mult eps gibbsd_half) Hpos). }
    apply (RealSetoid.real_lt_compat
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                        (real_plus (real_list_sum X g l)
                                   (real_mult eps gibbsd_half)))
             (real_plus (real_plus (g w) (real_list_sum X g l)) eps)).
    + apply real_eq_refl.
    + exact (real_eq_trans
               (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                          (real_plus (real_list_sum X g l)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l))
                          (real_plus (real_mult eps gibbsd_half)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l)) eps)
               (real_plus_swap_mid (g w) (real_mult eps gibbsd_half)
                                   (real_list_sum X g l)
                                   (real_mult eps gibbsd_half))
               (RealSetoid.real_eq_plus_compat
                  (real_plus (g w) (real_list_sum X g l))
                  (real_plus (real_mult eps gibbsd_half)
                             (real_mult eps gibbsd_half))
                  (real_plus (g w) (real_list_sum X g l))
                  eps
                  (real_eq_refl (real_plus (g w) (real_list_sum X g l)))
                  (gibbsd_half_sum eps))).
    + exact (real_lt_plus_compat _ _ _ _ Ha Ht).
Qed.

(* C4：Σ(p−q) == Σp − Σq（req 层 fsum_minus 的 Real 对位） *)
Lemma gibbsd_list_sum_minus : forall (X : Type) (p q : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
          (real_plus (real_list_sum X p l)
                     (real_opp (real_list_sum X q l))).
Proof.
  intros X p q l.
  apply (real_eq_trans
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_plus (real_list_sum X p l)
                      (real_list_sum X (fun s => real_opp (q s)) l))
           (real_plus (real_list_sum X p l)
                      (real_opp (real_list_sum X q l)))).
  - exact (real_list_sum_add X p (fun s => real_opp (q s)) l).
  - apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
             (real_list_sum X (fun s => real_opp (q s)) l)
             (real_list_sum X p l)
             (real_opp (real_list_sum X q l))).
    + apply real_eq_refl.
    + exact (real_list_sum_opp X q l).
Qed.

(* ============================================================ *)
(* Part 4：逐点消解主体                                                 *)
(* ============================================================ *)

(* D0【参数位消解】：逐点 Gibbs 切线 p−q ≤_B p·(−log(q/p))。
   Hypothesis dist_log_le_linear（参数位，10 下游）；此处显式应用
   real_log_le_linear_B（UpRealLeB:535）一次闭合，无条件。
   链：参数位 log(q/p) ≤_B q/p−1 → opp 反向 → 1−q/p 换形 →
   p 左乘保序 → p·(1−q/p)==p−q 换形完成。 *)
Lemma gibbsd_gibbs_pointwise_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b (real_plus (p s) (real_opp (q s)))
            (real_kl_term (p s) (q s) Hps Hqs).
Proof.
  intros X p q s Hps Hqs.
  unfold real_kl_term, real_le_b. intros eps Heps.
  set (Rqp := real_mult (q s) (real_inv_pos (p s) Hps)).
  set (Hr := real_mult_positive (q s) (real_inv_pos (p s) Hps) Hqs
               (real_inv_pos_pos (p s) Hps)).
  (* —— 参数位消解：req 层 dist_log_le_linear 使用位，B 形引擎显式应用 —— *)
  assert (Hlin : real_le_b (real_log Rqp Hr)
                           (real_plus Rqp (real_opp real_one))).
  { exact (real_log_le_linear_B Rqp Hr). }
  assert (Hstep2 : real_le_b (real_plus real_one (real_opp Rqp))
                             (real_opp (real_log Rqp Hr))).
  { exact (gibbsd_le_b_id_l _ _ _
             (real_eq_sym _ _ (gibbsd_minus_flip Rqp real_one))
             (gibbsd_le_b_opp _ _ Hlin)). }
  assert (Hstep3 : real_le_b
                     (real_mult (p s)
                        (real_plus real_one (real_opp Rqp)))
                     (real_mult (p s) (real_opp (real_log Rqp Hr)))).
  { exact (gibbsd_le_b_mult_pos_r (p s) _ _ Hps Hstep2). }
  exact (gibbsd_le_b_id_l _ _ _
           (real_eq_sym _ _ (gibbsd_p_minus_ratio (p s) (q s) Hps))
           Hstep3 eps Heps).
Qed.

(* D1【主件】：Gibbs 不等式 Real 实例化——0 ≤_B Σ_s KL(p s‖q s)。
   req_gibbs_inequality（UpReqDist:2122，dist_log_le_linear 10 下游）
   的 Real 实例化消解：归一化前提位照抄 req 层（real_eq 形），求和层
   real_list_sum 机，序 real_le_b，假设位由 D0 逐点件填充。
   语句与 E.13 real_gibbs_inequality_B 同形：E.13 走
   real_gibbs_inequality_eps 完成路，本件走 log 切线参数位消解复演路——双路互证。 *)
Theorem gibbsd_gibbs_inequality :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  assert (Hle : real_le_b
                  (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                  (real_list_sum X
                     (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
  { apply gibbsd_list_sum_le_b.
    intro s. exact (gibbsd_gibbs_pointwise_B X p q s (Hp s) (Hq s)). }
  assert (Hz : real_eq
                 (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                 real_zero).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
             (real_plus (real_list_sum X p l)
                        (real_opp (real_list_sum X q l)))
             real_zero).
    - exact (gibbsd_list_sum_minus X p q l).
    - apply (real_eq_trans
               (real_plus (real_list_sum X p l)
                          (real_opp (real_list_sum X q l)))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
                 (real_opp (real_list_sum X q l)) real_one
                 (real_opp real_one)).
        * exact Hnormp.
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X q l) real_one
                   Hnormq).
      + exact (real_plus_opp real_one).
  }
  exact (gibbsd_le_b_id_l real_zero
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_list_sum X
              (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_eq_sym _ _ Hz) Hle).
Qed.

(* ============================================================ *)
(* Part 5：主件——级联首层 cross_entropy_decomp 同法消解                 *)
(*   （req_cross_entropy_decomp @UpReqDist:2431 的 Real 实例化对位；    *)
(*     逐点恒等经 log 乘法分解向 q == p·(q/p) 闭合，零 log 逆消去）     *)
(* ============================================================ *)

Theorem gibbsd_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
       (real_list_sum X
          (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  apply (real_eq_trans
           (real_list_sum X
              (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
           (real_list_sum X
              (fun s : X => real_plus
                            (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                            (real_kl_term (p s) (q s) (Hp s) (Hq s))) l)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))).
  - apply real_list_sum_ext. intro s0.
    unfold real_kl_term.
    set (Rqp := real_mult (q s0) (real_inv_pos (p s0) (Hp s0))).
    set (Hr := real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0)) (Hq s0)
                 (real_inv_pos_pos (p s0) (Hp s0))).
    set (Hpm := real_mult_positive (p s0) Rqp (Hp s0) Hr).
    assert (Hlogsplit : real_eq (real_log (q s0) (Hq s0))
                          (real_plus (real_log (p s0) (Hp s0))
                                     (real_log Rqp Hr))).
    { apply (real_eq_trans (real_log (q s0) (Hq s0))
                           (real_log (real_mult (p s0) Rqp) Hpm)
                           (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr))).
      - exact (real_log_wd (q s0) (real_mult (p s0) Rqp) (Hq s0) Hpm
                  (real_eq_sym _ _
                     (gibbsd_p_mult_ratio (p s0) (q s0) (Hp s0)))).
      - exact (real_log_mult (p s0) Rqp (Hp s0) Hr).
    }
    apply (real_eq_trans
             (real_mult (p s0) (real_opp (real_log (q s0) (Hq s0))))
             (real_mult (p s0)
                (real_plus (real_opp (real_log (p s0) (Hp s0)))
                           (real_opp (real_log Rqp Hr))))
             (real_plus (real_mult (p s0) (real_opp (real_log (p s0) (Hp s0))))
                        (real_mult (p s0) (real_opp (real_log Rqp Hr))))).
    + apply (RealSetoid.real_eq_mult_compat (p s0)
               (real_opp (real_log (q s0) (Hq s0))) (p s0)
               (real_plus (real_opp (real_log (p s0) (Hp s0)))
                          (real_opp (real_log Rqp Hr)))).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_opp (real_log (q s0) (Hq s0)))
                 (real_opp (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr)))
                 (real_plus (real_opp (real_log (p s0) (Hp s0)))
                            (real_opp (real_log Rqp Hr)))).
        -- exact (RealSetoid.real_eq_opp_compat (real_log (q s0) (Hq s0))
                     (real_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr))
                     Hlogsplit).
        -- exact (real_opp_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr)).
    + exact (real_distrib (p s0) (real_opp (real_log (p s0) (Hp s0)))
               (real_opp (real_log Rqp Hr))).
  - exact (real_list_sum_add X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
             (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Qed.

(* ============================================================ *)
(*   gibbsd_lt_add_opp_r / gibbsd_le_b_opp / gibbsd_le_b_id_l /         *)
(*   gibbsd_minus_flip / gibbsd_le_b_mult_pos_r —— Bishop 序代数 5 件    *)
(*   （req 层 opp_le_compat / le_id_l / req_le_mult_compat_r 的          *)
(*   real_le_b 对位，req 层无此形——B 形引擎显式应用的缺口件）。             *)
(*   gibbsd_p_mult_ratio / gibbsd_p_minus_ratio —— eq 恒等 2 件。       *)
(*   gibbsd_two_pos / gibbsd_half / gibbsd_half_pos / gibbsd_half_sum    *)
(*   + gibbsd_list_sum_le_b / gibbsd_list_sum_minus —— 和层机 6 件      *)
(*   （fsum_le / fsum_minus 的 Bishop 对位；eps 对半归纳免除法）。      *)
(*   gibbsd_gibbs_pointwise_B —— 参数位消解（dist_log_le_linear 显式应用）。 *)

(*   gibbsd_cross_entropy_decomp —— 级联首层主件。                      *)
(*   序异向说明：req 层 Hypothesis 参数位不可由 B 形引擎无条件消解，        *)
(*   本件以 Real 实例化定理形式显式应用该位（详见 Part 4 首注）。         *)
(*   配套 Bishop 序代数基元与和层机见 Part 1 与 Part 3。                *)



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
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qround
               Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============================================================ *)
(* Part 6：Q 层半分 helper                                                     *)
(* ============================================================ *)

Lemma gibbe2_Q_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps * (1#2))%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps (1#2)).
  - apply QltT_to_Qlt. exact Heps.
  - reflexivity.
Qed.

Lemma gibbe2_Q_half_lt : forall eps : Q, QltT 0 eps -> Qlt (eps * (1#2))%Q eps.
Proof.
  intros eps Heps.
  assert (H1 : Qlt ((1#2) * eps) (1 * eps)).
  { apply (Qmult_lt_compat_r (1#2) 1 eps).
    - apply QltT_to_Qlt. exact Heps.
    - reflexivity. }
  rewrite Qmult_1_l in H1.
  rewrite (Qmult_comm (1#2) eps) in H1.
  exact H1.
Qed.

(* ============================================================ *)
(* Part 7：le_b 补层序机                                                       *)
(* ============================================================ *)

(* B1：le_b 右端 eq 换形 *)
Lemma gibbe2_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hbc eps Heps.
  unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat a a (real_plus b eps) (real_plus c eps)           (real_eq_refl a)           (RealSetoid.real_eq_plus_compat b eps c eps Hbc (real_eq_refl eps))           (H eps Heps)).
Qed.

(* B2：le_b 右加平移 *)
Lemma gibbe2_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus z x) (real_plus x z)
           (real_plus z (real_plus y eps)) (real_plus (real_plus y z) eps)).
  - apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z y) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus z y) eps
               (real_plus y z) eps
               (real_plus_comm z y) (real_eq_refl eps)).
  - exact (real_lt_plus_translate z x (real_plus y eps) (H eps Heps)).
Qed.

(* B3：le_b a b ⟹ le_b 0 (b−a) *)
Lemma gibbe2_le_b_nonneg_diff : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus (real_opp a) a)
           real_zero
           (real_plus (real_opp a) (real_plus b eps))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply (real_eq_trans _ (real_plus a (real_opp a)) _).
    + apply real_plus_comm.
    + exact (real_plus_opp a).
  - apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) b) eps
               (real_plus b (real_opp a)) eps
               (real_plus_comm (real_opp a) b) (real_eq_refl eps)).
  - exact (real_lt_plus_translate (real_opp a) a (real_plus b eps) (H eps Heps)).
Qed.

(* B4【核心新件】：le_b Bishop 序反对称（逐 n 构造，零 Or 完成、零 LPO） *)
Lemma gibbe2_le_b_antisym : forall a b : Real,
  real_le_b a b -> real_le_b b a -> real_eq a b.
Proof.
  intros a b H1 H2 eps Heps.
  assert (He2pos : real_lt real_zero (real_const (eps * (1#2))%Q))
    by (apply real_const_pos; apply gibbe2_Q_half_pos; exact Heps).
  assert (Hhe : Qlt (eps * (1#2))%Q eps) by (apply gibbe2_Q_half_lt; exact Heps).
  destruct (H1 _ He2pos) as [g1 [Hg1pos [N1 HN1]]].
  destruct (H2 _ He2pos) as [g2 [Hg2pos [N2 HN2]]].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  rewrite real_plus_proj in HN1, HN2.
  rewrite real_const_proj in HN1, HN2.
  set (x := projT1 a n - projT1 b n).
  set (h := (eps * (1#2))%Q).
  assert (Hg1q : 0 < g1) by (apply QltT_to_Qlt; exact Hg1pos).
  assert (Hg2q : 0 < g2) by (apply QltT_to_Qlt; exact Hg2pos).
  (* 上界：x < h（x := a_n − b_n，环归 + lia 完成） *)
  assert (Hstep1 : projT1 a n - projT1 b n + g1
                   < projT1 a n - projT1 b n
                     + (projT1 b n + eps * (1#2) - projT1 a n)).
  { exact (proj2 (Qplus_lt_r g1 (projT1 b n + eps * (1#2) - projT1 a n)
                   (projT1 a n - projT1 b n)) HN1). }
  assert (Hring1 : projT1 a n - projT1 b n
                   + (projT1 b n + eps * (1#2) - projT1 a n)
                   == eps * (1#2)) by ring.
  rewrite Hring1 in Hstep1.
  assert (Hub : projT1 a n - projT1 b n < eps * (1#2)).
  { apply (Qle_lt_trans _ (projT1 a n - projT1 b n + g1) _).
    - rewrite <- (Qplus_0_r (projT1 a n - projT1 b n)) at 1.
      apply (proj2 (Qplus_le_r 0 g1 (projT1 a n - projT1 b n))).
      exact (b5dH_q_pos_le g1 Hg1q).
    - exact Hstep1. }
  (* 下界：−x < h *)
  assert (Hstep2 : - (projT1 a n - projT1 b n) + g2
                   < - (projT1 a n - projT1 b n)
                     + (projT1 a n + eps * (1#2) - projT1 b n)).
  { exact (proj2 (Qplus_lt_r g2 (projT1 a n + eps * (1#2) - projT1 b n)
                   (- (projT1 a n - projT1 b n))%Q) HN2). }
  assert (Hring2 : - (projT1 a n - projT1 b n)
                   + (projT1 a n + eps * (1#2) - projT1 b n)
                   == eps * (1#2)) by ring.
  rewrite Hring2 in Hstep2.
  assert (Hdn : (- (projT1 a n - projT1 b n))%Q < eps * (1#2)).
  { apply (Qle_lt_trans _ ((- (projT1 a n - projT1 b n))%Q + g2) _).
    - rewrite <- (Qplus_0_r (- (projT1 a n - projT1 b n))%Q) at 1.
      apply (proj2 (Qplus_le_r 0 g2 (- (projT1 a n - projT1 b n))%Q)).
      exact (b5dH_q_pos_le g2 Hg2q).
    - exact Hstep2. }
  (* 终判：|x| < eps（符号两案，Q 可判定，零三分律） *)
  unfold x, h.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (projT1 a n - projT1 b n)) as [Hsx | Hsx].
  - rewrite (Qabs_pos (projT1 a n - projT1 b n) (b5dH_q_pos_le _ Hsx)).
    apply (Qlt_le_trans _ (eps * (1#2)) eps Hub).
    exact (Qlt_le_weak _ _ Hhe).
  - rewrite (Qabs_neg (projT1 a n - projT1 b n) Hsx).
    apply (Qlt_le_trans (- (projT1 a n - projT1 b n))%Q (eps * (1#2)) eps Hdn).
    exact (Qlt_le_weak _ _ Hhe).
Qed.

(* ============================================================ *)
(* Part 8：逐项钳零件族                                                        *)
(* ============================================================ *)

(* C1：二项和零 ⟹ 首项零 *)
Lemma gibbe2_clamp_head : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero a.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_le_b_antisym real_zero a Ha).
  apply (gibbe2_le_b_id_r a (real_plus b a) real_zero).
  - apply (gibbsd_le_b_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_trans a (real_plus a real_zero) (real_plus real_zero a)
                (real_eq_sym _ _ (real_plus_zero a)) (real_plus_comm a real_zero))
             (gibbe2_le_b_translate_r real_zero b a Hb)).
  - apply (real_eq_trans (real_plus b a) (real_plus a b) real_zero
             (real_plus_comm b a) Hsum).
Qed.

(* C2：二项和零 ⟹ 次项零（comm 副本） *)
Lemma gibbe2_clamp_head_r : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero b.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_clamp_head b a Hb Ha).
  apply (real_eq_trans _ (real_plus a b) _).
  - apply real_plus_comm.
  - exact Hsum.
Qed.

(* C3【主件】：有限具体载体 [true;false] 逐项和零提取 *)
Lemma gibbe2_list_sum_zero_extract_bool :
  forall (f : bool -> Real),
    (forall s : bool, real_le_b real_zero (f s)) ->
    real_eq (real_list_sum bool f [true; false]) real_zero ->
    forall s : bool, real_eq real_zero (f s).
Proof.
  intros f Hpt Hsum s. destruct s; simpl in Hsum.
  - exact (gibbe2_clamp_head (f true) (real_plus (f false) real_zero)
             (Hpt true)
             (gibbe2_le_b_id_r real_zero (f false)
                (real_plus (f false) real_zero)
                (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
             Hsum).
  - apply (real_eq_trans real_zero (real_plus (f false) real_zero) (f false)).
    + exact (gibbe2_clamp_head_r (f true) (real_plus (f false) real_zero)
               (Hpt true)
               (gibbe2_le_b_id_r real_zero (f false)
                  (real_plus (f false) real_zero)
                  (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
               Hsum).
    + exact (real_plus_zero (f false)).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* D0：和零 ⟹ 项恒等 *)
Lemma gibbe2_kl_eq_of_w_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq)
                     (real_opp (real_plus p (real_opp q)))) real_zero ->
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)).
Proof.
  intros p q Hp Hq H.
  set (X := real_plus p (real_opp q)).
  set (K := real_kl_term p q Hp Hq).
  set (NX := real_opp X).
  (* kl == (kl + −X) + X *)
  apply (real_eq_trans K (real_plus (real_plus K NX) X) X).
  - apply (real_eq_trans K (real_plus K real_zero) (real_plus (real_plus K NX) X)).
    + exact (real_eq_sym (real_plus K real_zero) K (real_plus_zero K)).
    + apply (real_eq_trans (real_plus K real_zero)
               (real_plus K (real_plus NX X))
               (real_plus (real_plus K NX) X)).
      * apply (RealSetoid.real_eq_plus_compat K real_zero K
                 (real_plus NX X)
                 (real_eq_refl K)
                 (real_eq_trans real_zero (real_plus X NX) (real_plus NX X)
                    (real_eq_sym (real_plus X NX) real_zero (real_plus_opp X))
                    (real_plus_comm X NX))).
      * exact (real_plus_assoc K NX X).
  - (* (kl + −X) + X == 0 + X == X *)
    apply (real_eq_trans (real_plus (real_plus K NX) X)
             (real_plus real_zero X) X).
    + exact (RealSetoid.real_eq_plus_compat (real_plus K NX) X real_zero X
               H (real_eq_refl X)).
    + apply (real_eq_trans (real_plus real_zero X)
               (real_plus X real_zero) X
               (real_plus_comm real_zero X)
               (real_plus_zero X)).
Qed.


Lemma gibbe2_tangent_eq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)) ->
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_mult q (real_inv_pos p Hp))
                     (real_opp real_one)).
Proof.
  intros p q Hp Hq H.
  set (u := real_mult q (real_inv_pos p Hp)).
  set (Hu := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log u Hu).
  (* H : p·(−L) == p + −q *)
  (* 步1：p·L == q + −p（两侧取 opp） *)
  assert (Hs1 : real_eq (real_mult p L) (real_plus q (real_opp p))).
  { apply (real_eq_trans (real_mult p L)
             (real_opp (real_mult p (real_opp L)))
             (real_plus q (real_opp p))).
    - apply (real_eq_sym (real_opp (real_mult p (real_opp L)))
               (real_mult p L)
               (real_eq_trans (real_opp (real_mult p (real_opp L)))
                  (real_mult p (real_opp (real_opp L)))
                  (real_mult p L)
                  (real_opp_mult p (real_opp L))
                  (RealSetoid.real_eq_mult_compat p
                     (real_opp (real_opp L)) p L
                     (real_eq_refl p) (real_opp_opp L)))).
    - apply (real_eq_trans (real_opp (real_mult p (real_opp L)))
               (real_opp (real_plus p (real_opp q)))
               (real_plus q (real_opp p))
               (RealSetoid.real_eq_opp_compat (real_mult p (real_opp L))
                  (real_plus p (real_opp q)) H)
               (gibbsd_minus_flip p q)).
  }
  (* 步2：L == (q−p)·inv p *)
  assert (Hs2 : real_eq L (real_mult (real_plus q (real_opp p))
                                        (real_inv_pos p Hp))).
  { apply (real_eq_trans L
             (real_mult (real_mult p L) (real_inv_pos p Hp))
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))).
    - apply (real_eq_trans L (real_mult L real_one)
               (real_mult (real_mult p L) (real_inv_pos p Hp))).
      + apply (real_eq_sym (real_mult L real_one) L (real_mult_one L)).
      + apply (real_eq_trans (real_mult L real_one)
                 (real_mult L (real_mult p (real_inv_pos p Hp)))
                 (real_mult (real_mult p L) (real_inv_pos p Hp))).
        * apply (RealSetoid.real_eq_mult_compat L real_one
                   L (real_mult p (real_inv_pos p Hp))
                   (real_eq_refl L)
                   (real_eq_sym (real_mult p (real_inv_pos p Hp)) real_one
                      (real_inv_pos_correct p Hp))).
        * apply (real_eq_trans
                   (real_mult L (real_mult p (real_inv_pos p Hp)))
                   (real_mult (real_mult L p) (real_inv_pos p Hp))
                   (real_mult (real_mult p L) (real_inv_pos p Hp))).
          -- exact (real_mult_assoc L p (real_inv_pos p Hp)).
          -- apply (RealSetoid.real_eq_mult_compat (real_mult L p)
                     (real_inv_pos p Hp) (real_mult p L) (real_inv_pos p Hp)
                     (real_mult_comm L p) (real_eq_refl _)).
    - apply (RealSetoid.real_eq_mult_compat (real_mult p L)
               (real_inv_pos p Hp) (real_plus q (real_opp p))
               (real_inv_pos p Hp) Hs1 (real_eq_refl _)).
  }
  (* 步3：(q−p)·inv p == q·inv p + −1 == u + −1 *)
  assert (Hs3 : real_eq (real_mult (real_plus q (real_opp p))
                                   (real_inv_pos p Hp))
                        (real_plus u (real_opp real_one))).
  { apply (real_eq_trans
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
             (real_plus (real_mult (real_inv_pos p Hp) q)
                        (real_mult (real_inv_pos p Hp) (real_opp p)))
             (real_plus u (real_opp real_one))).
    - apply (real_eq_trans
               (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
               (real_mult (real_inv_pos p Hp) (real_plus q (real_opp p)))
               (real_plus (real_mult (real_inv_pos p Hp) q)
                          (real_mult (real_inv_pos p Hp) (real_opp p)))).
      + apply (real_mult_comm (real_plus q (real_opp p)) (real_inv_pos p Hp)).
      + exact (real_distrib (real_inv_pos p Hp) q (real_opp p)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos p Hp) q)
               (real_mult (real_inv_pos p Hp) (real_opp p))
               (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
      + apply (real_mult_comm (real_inv_pos p Hp) q).
      + apply (real_eq_trans (real_mult (real_inv_pos p Hp) (real_opp p))
                   (real_opp (real_mult (real_inv_pos p Hp) p))
                   (real_opp real_one)).
        * apply (real_eq_sym _ _ (real_opp_mult (real_inv_pos p Hp) p)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (real_inv_pos p Hp) p) real_one).
          apply (real_eq_trans (real_mult (real_inv_pos p Hp) p)
                     (real_mult p (real_inv_pos p Hp)) real_one).
          -- apply (real_mult_comm (real_inv_pos p Hp) p).
          -- exact (real_inv_pos_correct p Hp).
  }
  exact (real_eq_trans L _ _ Hs2 Hs3).
Qed.


Lemma gibbe2_kl_zero_tangent_eq :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool,
    real_eq (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                         (Hq s) (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                       (real_opp real_one)).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl.
  set (K := fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : bool => real_plus (p s) (real_opp (q s))).
  set (D := fun s : bool => real_plus (K s) (real_opp (G s))).
  (* 1. Σ(p−q) == 0 *)
  assert (HsumG0 : real_eq (real_list_sum bool G [true; false]) real_zero).
  { apply (real_eq_trans
             (real_list_sum bool G [true; false])
             (real_plus (real_list_sum bool p [true; false])
                        (real_opp (real_list_sum bool q [true; false])))
             real_zero).
    - exact (gibbsd_list_sum_minus bool p q [true; false]).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool p [true; false])
                          (real_opp (real_list_sum bool q [true; false])))
               (real_plus real_one (real_opp real_one)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool p [true; false])
                 (real_opp (real_list_sum bool q [true; false]))
                 real_one (real_opp real_one) Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool q [true; false]) real_one Hnq)).
      + exact (real_plus_opp real_one).
  }
  (* 2. ΣD == 0 *)
  assert (HsumD : real_eq (real_list_sum bool D [true; false]) real_zero).
  { unfold D.
    apply (real_eq_trans
             (real_list_sum bool
                (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
             (real_plus (real_list_sum bool K [true; false])
                        (real_opp (real_list_sum bool G [true; false])))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum bool
                  (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
               (real_plus (real_list_sum bool K [true; false])
                          (real_list_sum bool
                             (fun s : bool => real_opp (G s)) [true; false]))
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))).
      + exact (real_list_sum_add bool K (fun s : bool => real_opp (G s))
                   [true; false]).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_list_sum bool (fun s : bool => real_opp (G s)) [true; false])
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 (real_eq_refl _)
                 (real_list_sum_opp bool G [true; false])).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))
               (real_plus real_zero (real_opp real_zero)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 real_zero (real_opp real_zero) Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool G [true; false]) real_zero HsumG0)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero) real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero (real_opp real_zero)
                   real_zero real_zero (real_eq_refl _) (real_opp_zero)).
        * exact (real_plus_zero real_zero).
  }
  (* 3. 逐点钳零：D s == 0 *)
  assert (Hclamp : forall s : bool, real_eq (D s) real_zero).
  { intro s. apply (real_eq_sym _ _).
    apply (gibbe2_list_sum_zero_extract_bool D).
    - intro s0. exact (gibbe2_le_b_nonneg_diff _ _
                         (gibbsd_gibbs_pointwise_B bool p q s0 (Hp s0) (Hq s0))).
    - exact HsumD. }
  (* 4. 逐点：K s == G s ⟹ 切点等式 *)
  intro s. apply gibbe2_tangent_eq.
  apply gibbe2_kl_eq_of_w_zero.
  exact (Hclamp s).
Qed.

(* ============================================================ *)
(* Part 9：主件·eq-linear 桥显式注入的等式件                                   *)
(* ============================================================ *)

Theorem gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
     real_eq u real_one) ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl Heqlin s.
  assert (Htan := gibbe2_kl_zero_tangent_eq p q Hp Hq Hnp Hnq Hkl s).
  assert (Hu1 : real_eq (real_mult (q s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (Heqlin (real_mult (q s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                (Hq s) (real_inv_pos_pos (p s) (Hp s)))).
    exact Htan. }
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))
           (q s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))).
    + apply (real_eq_sym (real_mult (p s) real_one) (p s)
               (real_mult_one (p s))).
    + apply (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (q s) (Hp s)).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                                    *)
(* ============================================================ *)

Print Assumptions gibbe2_le_b_antisym.
Print Assumptions gibbe2_clamp_head.
Print Assumptions gibbe2_list_sum_zero_extract_bool.
Print Assumptions gibbe2_kl_zero_tangent_eq.
Print Assumptions gibbe2_gibbs_equality_bool.

Print Assumptions gibbe2_le_b_id_r.
