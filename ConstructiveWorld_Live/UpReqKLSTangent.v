(* ==========================================================================)
   UpReqKLSTangent.v — KL 严格性与指数切线多项式
   使命: t1_ep_four_terms（e^(−t) 四项下界多项式）、t1_exp_tangent_neg、t1_gibbe2_gibbs_equality_bool（Gibbs 等号条件）、t1_kl_energy_nonconst 与 t1_kl_sum_strict_from_le（和的严格性）。
   依赖: CW_ConstructiveWorld_219、G07_KLWall、G08_Gibbs；Stdlib QArith、List、Arith、Lia
   对标: 相对熵的严格正性与等号条件（Gibbs 不等式的强化形）及 e^(−t) 的切线下界。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import G07_KLWall.
Require Import G08_Gibbs.
Import ListNotations.

(* ============================================================ *)
(* Part A：主引理——Q 层四项交错部分和下界（使命形重曝光）               *)
(* ============================================================ *)

(* 使命形：1−t+t²/2−t³/6 ≤ ep_n(−t)（n≥3 全体；0≤t≤1 支）。            *)

(* klst_q_pair_nonneg + 偶号正尾项，n=3+m 奇偶分派构造性给 witness）。 *)
Lemma t1_ep_four_terms : forall (m : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  Qle (1 - t + t * t * (1#2) - t * t * t * (1#6))
      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) (- t)).
Proof.
  intros m t Ht0 Ht1.
  exact (klst_ep_four_terms m t Ht0 Ht1).
Qed.

(* Real 载体严格切线（e^w 载体；w := −t 即使命之 e^{−t} 形）。           *)

(* 四项 Q 层下界经 exp_partial_tail_small / exp_series_arch 抬升）。   *)
Lemma t1_exp_tangent_neg : forall w : Real,
  real_lt w real_zero ->
  real_lt (real_plus real_one w) (cauchy_real_exp w).
Proof.
  exact klst_exp_tangent_neg.
Qed.

(* ============================================================ *)
(* Part B：消解(b)核心——「切点⟹一」                                    *)
(* ============================================================ *)

Lemma t1_log_eq_linear_inject : forall (u : Real) (Hu : real_lt real_zero u),
  real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
  real_eq u real_one.
Proof.
  intros u Hu Heq.
  apply (real_weak_trich u real_one).
  - (* 支 1：排除 u < 1。负支切线（0<x<1 ⟹ log x < x−1）+ 恒等代换
       ⟹ u−1 < u−1，real_lt_irrefl 收紧。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log u Hu) (real_plus u (real_opp real_one)))
      by exact (klst_log_tangent_neg u Hu Hlt).
    exact (real_lt_irrefl (real_plus u (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log u Hu)
                             (real_plus u (real_opp real_one))
                             (real_plus u (real_opp real_one))
                             (real_plus u (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus u (real_opp real_one)))
                             Htan)).
  - 
    intro Hlt.
    assert (Htan : real_lt (real_log u Hu) (real_plus u (real_opp real_one)))
      by exact (klst_log_tangent_pos u Hu Hlt).
    exact (real_lt_irrefl (real_plus u (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log u Hu)
                             (real_plus u (real_opp real_one))
                             (real_plus u (real_opp real_one))
                             (real_plus u (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus u (real_opp real_one)))
                             Htan)).
Qed.

(* ============================================================ *)
(* Part C：消解(b)全件——gibbe2 注入前提无条件消除                       *)
(* ============================================================ *)

(* 与 G08_Gibbs.gibbe2_gibbs_equality_bool 同强，但注入前提位
   （forall u Hu, log u == u−1 ⟹ u == 1，原为诚实接口位）已由
   Part B 无条件供给——G08 主件自此零接口前提。 *)
Theorem t1_gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl s.
  exact (gibbe2_gibbs_equality_bool p q Hp Hq Hnp Hnq Hkl           t1_log_eq_linear_inject s).
Qed.

(* ============================================================ *)
(* Part D：消解(a)完成——无条件「能量非常数 ⟹ KL>0」形                  *)
(* ============================================================ *)

(* 使命形重曝光：双归一化 + 逐项全称双向弱序 + s₀ 处严格分离（任一
   方向 Or）⟹ 0 < Σ_s kl_term。相对 klst_kl_sum_strict 的单向弱序
   （p≤q，排除 q>p 支），负支由 klst_gibbs_core_strict_neg 补齐
   （ E401 完成），温度桥两向均入。 *)
Theorem t1_kl_energy_nonconst : forall (X : Type) (l1 : list X) (s0 : X)
  (l2 : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, Or (real_le (p s) (q s)) (real_le (q s) (p s)))
  (Hnormp : real_eq (real_list_sum X p (l1 ++ s0 :: l2)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l1 ++ s0 :: l2)) real_one)
  (Hdiv : Or (real_lt (p s0) (q s0)) (real_lt (q s0) (p s0))),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
       (l1 ++ s0 :: l2)).
Proof.
  intros X l1 s0 l2 p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  exact (klst_kl_energy_nonconst X l1 s0 l2 p q Hp Hq Hpq Hnormp Hnormq           Hdiv).
Qed.

(* 逐项可比前提的定向消解形：逐项单向 p≤q 弱序（Gibbs 温度桥的
   单调侧）+ 单向分离见证 ⟹ KL>0——把 klst_kl_sum_strict 的
   s₀ 分离前提放宽为单向 Or 之外、逐项弱序仍单向时的同强完成，
   由 Part D 的双向可比接口以常值可比见证消解。 *)
Theorem t1_kl_sum_strict_from_le : forall (X : Type) (l1 : list X) (s0 : X)
  (l2 : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, real_le (p s) (q s))
  (Hnormp : real_eq (real_list_sum X p (l1 ++ s0 :: l2)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l1 ++ s0 :: l2)) real_one)
  (Hdiv : real_lt (p s0) (q s0)),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
       (l1 ++ s0 :: l2)).
Proof.
  intros X l1 s0 l2 p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  exact (klst_kl_sum_strict X l1 s0 l2 p q Hp Hq Hpq Hnormp Hnormq Hdiv).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                              *)
(* ============================================================ *)

Print Assumptions t1_ep_four_terms.
Print Assumptions t1_exp_tangent_neg.
Print Assumptions t1_log_eq_linear_inject.
Print Assumptions t1_gibbe2_gibbs_equality_bool.
Print Assumptions t1_kl_energy_nonconst.
Print Assumptions t1_kl_sum_strict_from_le.

(* ============================================================ *)
(* 尾注一（消解(a) 残余结论）：逐项可比前提 Or (p≤q) (q≤p) 在 Set 层     *)
(*   Or 接口（S01:69，A+B）下不可去除——去除它等价于对任意实对给出       *)
(*   三分判定见证（LLPO 形），非直觉主义可证；此为诚实接口下界而非      *)
(*   缺口。具体 Gibbs/softmax 实例经 cauchy_real_exp_mono 严格单调      *)
(*   消解（G07 头注同结论），无条件化的终点件即 klst_kl_energy_nonconst. *)
(*                                                                *)
(* 尾注二（(c) 登记，只登记不动论文）：论文 §10.2 第 1 项「能量非常数    *)
(*   ⟹ KL>0」边界精化为——前提由逐项单向弱序 p≤q 精化为全称双向弱序    *)
(*   Or (p≤q) (q≤p) + s₀ 双向严格分离；gibbe2 主件注入   *)
(*   前提已无条件消除（Part C）。    *)
(* ============================================================ *)
