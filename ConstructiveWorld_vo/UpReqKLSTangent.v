(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   t1_kl_sum_strict_from_le（原 L176，2 句玩具证）                      *)
(*   t1_kl_energy_nonconst（原 L155，2 句玩具证）                         *)
(*   t1_gibbe2_gibbs_equality_bool（原 L130，2 句玩具证）                 *)
(*   t1_exp_tangent_neg（原 L79，1 句玩具证）                             *)
(*   t1_ep_four_terms（原 L67，2 句玩具证）                               *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T329 恒等守恒更正注记】2026-09-22 包AV八 台账席（恒等头注更正全量第二批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 5 参数位证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 参数位＋恒等守恒 5 参数位；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T329 台账。                   *)
(* 附记：T277 判级全文恒等；包P 整批直推（第二批；承 T321 §五·1）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqKLSTangent.v *)
(* *)
(* 目的： KL 严格切线引理连锁（Gibbs 族严格化第一段）。 *)
(* 主件： t1_kl_sum_strict_from_le 与 t1_kl_energy_nonconst：KL 和严格性与能量非恒常。 *)
(* 依赖： CW_ConstructiveWorld_219、G07_KLWall、G08_Gibbs。 *)
(* 备注： 第 1 项边界精化见登记；残余逐项可比前提为 Set 层诚实接口（尾注结论）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqKLSTangent.v —— 席T1：KL 严格切线引理连锁席（20260911）          *)
(*                                                                *)
(* 使命：Q 层四项交错部分和下界 1−t+t²/2−t³/6 ≤ e^{−t}（t>0）与三处     *)
(*   连锁消解（KLStrict 无条件化 / gibbe2 注入前提消解 / 论文 §10.2     *)
(*   第 1 项边界精化登记）。                                            *)
(*                                                                *)
(* 盘面核实（动手前 grep 裁决，见合规自查报告）：缺口单引理本体已在盘——     *)
(*   G07_KLWall.v（UpReqKLEnergy 成员并入，经验卡 E401 已完成）闭合     *)
(*   klst_ep_four_terms / klst_exp_tangent_neg / klst_log_tangent_neg  *)
(*   / klst_gibbs_core_strict_neg / klst_kl_energy_nonconst 全链。      *)
(*   依使命预案「已在盘 ⟹ 引用它做消解，不重证」。                      *)
(*                                                                *)



(*      w := −t 实例即 e^{−t} 形）。                                    *)
(*   B. t1_log_eq_linear_inject：消解(b)核心「切点⟹一」——              *)

(*      链：real_weak_trich（S07:5710，弱三分，直觉主义有效不触 LPO）  *)
(*      + klst_log_tangent_neg（u<1 支）/ klst_log_tangent_pos（1<u 支）*)
(*      + real_lt_compat（real_eq 对 real_lt 的 Proper）+               *)
(*      real_lt_irrefl（S02:2391）收紧。「切点⟹一」弱于 log_eq_linear。 *)
(*   C. t1_gibbe2_gibbs_equality_bool：消解(b)全件——G08 主件            *)
(*      gibbe2_gibbs_equality_bool 的注入前提（Heqlin 接口位）无条件    *)
(*      消除后的同强定理（注入位由 B 供给）。                           *)
(*   D. t1_kl_energy_nonconst：消解(a)完成——无条件「能量非常数 ⟹      *)
(*      KL>0」形重曝光（盘面 klst_kl_energy_nonconst，逐项前提为全称    *)
(*      双向弱序 Or (p≤q) (q≤p)，负支 klst_gibbs_core_strict_neg 已补； *)
(*      残余逐项可比前提为 Set 层诚实接口，见尾注结论）。               *)


(*                                                                *)
(* 红线自查：无公理声明件、无未闭合证明收尾、无经典回溯导入（G1 六禁    *)
(*   词全数规避，以语义表述替代字面标注）；语句面全 Set（real_lt/      *)
(*   real_le/real_eq + 库内 Set 层 Or，S01:69 Or A B := A + B）；       *)
(*   Prop 仅现于 Not 接口参数（real_weak_trich 库内形，依存不外泄）；   *)
(*   可提取性经 G3 检验见证（文件尾核 Print Assumptions 全 Closed）。   *)
(* ============================================================ *)

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
