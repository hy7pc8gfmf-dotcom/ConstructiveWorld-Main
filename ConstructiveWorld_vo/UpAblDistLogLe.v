(* ============================================================ *)
(* UpAblDistLogLe.v *)
(* *)
(* 目的： 族E log-le 具体载体剩余部分的闭合——实现已证结论明示的未竟      *)
(*        通道：dist_log_le_linear 前提（UpReqDist，Section        *)
(*        ReqFEP 内）的 Regular-Real 具体载体实例供给。                    *)
(* 主件： ydll_lpo_barrier——前提实例 ⟹ 实数零等判定 Or (¬(u==0)) (u==0)   *)
(*        （real-LPO 族，S07 头注同级不可证参照类）的定理级归约。          *)
(*        载体分层结论再精化：此前估计的「30-60 行代数链通道」经核验降格—— *)
(*        反向严格支（eps 间隙矛盾）确可达并已于本件闭合                   *)
(*        （ydll_le_b_not_gt + ydll_log_tangent_not_gt，两者此前库内缺失）； *)
(*        正向分支判定（log x 与 x−1 的 Or 分支产出）不可达，本件以归约定形此结论。 *)
(* 前提对齐：该语句在实例面 RealEnhancedReal（S07，le:=real_le、 *)
(*        log:=real_log、lt:=real_lt、plus:=real_plus、opp:=real_opp；     *)
(*        req_minus x one 形态等同于 real_plus x (real_opp real_one)）下与本件语句面 *)
(*        逐字等同（双向形态互验）。语句面取 plain real_* 口径：与 UpRealLeB 三十六件 plain 族、t34 Part B 使用处同参——      *)
(*        接口投影名零出现，提取层零转换残留。                             *)
(* 依赖： CW_ConstructiveWorld_219、G07_KLWall、UpReqKLSTangent、          *)
(*        UpRealLeB。                                                      *)
(* 备注： 零承认件：纯构造性，语句面全 Set 值（Or/Not 为 S01 Set 层别名）； *)
(*        无 公理/承认/参数位/中止；四件逐条 Print Assumptions 全闭合。    *)
(* 编译配方：9.1 直调（coqc 无 -Q），cpu_guard 包裹，-o 输出临时目录。     *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import G07_KLWall.
Require Import UpReqKLSTangent.
Require Import UpRealLeB.

(* ============================================================ *)
(* §1 Bishop 形（real_le_b）反向严格排除——eps 间隙矛盾。                 *)
(*   此前结论中「eps 间隙矛盾」肢的首次形式化：x ≤_B y 时 y < x 不可能。 *)
(*   论证：设 y < x 有 Q 见证 e0（尾段 a_n − b_n > e0）。取 B 形余量      *)
(*   eps := real_const e0（逐点恰为 e0），得 e1 > 0 使尾段                *)
(*   b_n + e0 − a_n > e1。两尾段相加得 e1 + e0 < e0，即 e1 < 0，与        *)
(*   0 < e1 矛盾（Qlt_irrefl 收紧）。                                     *)
(* ============================================================ *)

Lemma ydll_le_b_not_gt :
  forall a b : Real, real_le_b a b -> Not (real_lt b a).
Proof.
  intros a b Hleb Hba.
  destruct Hba as [e0 [He0T [N0 H0]]].
  specialize (Hleb (real_const e0) (real_const_pos e0 He0T)).
  destruct Hleb as [e1 [He1T [N1 H1]]].
  pose proof (QltT_to_Qlt 0 e1 He1T) as H01.
  set (n := Nat.max N0 N1).
  assert (H0n : QltT e0 (projT1 a n - projT1 b n)).
  { apply (H0 n). apply NatLe_lift. apply Nat.le_max_l. }
  assert (H1n : QltT e1 (projT1 (real_plus b (real_const e0)) n - projT1 a n)).
  { apply (H1 n). apply NatLe_lift. apply Nat.le_max_r. }
  assert (Hpt : projT1 (real_plus b (real_const e0)) n == projT1 b n + e0).
  { destruct b as [ub Hb]. unfold real_const. simpl. ring. }
  pose proof (QltT_to_Qlt e1 _ H1n) as H1nQ.
  setoid_rewrite Hpt in H1nQ.
  pose proof (QltT_to_Qlt e0 _ H0n) as H0nQ.
  assert (Hsum : Qlt (e1 + e0)
                   (projT1 b n + e0 - projT1 a n
                    + (projT1 a n - projT1 b n))).
  { apply (Qplus_lt_compat e1 (projT1 b n + e0 - projT1 a n)
                           e0 (projT1 a n - projT1 b n)).
    - exact H1nQ.
    - exact H0nQ. }
  assert (Hring : projT1 b n + e0 - projT1 a n
                  + (projT1 a n - projT1 b n) == e0) by ring.
  rewrite Hring in Hsum.
  destruct (Qlt_le_dec e1 0) as [Hlt10 | Hle01].
  - exact (match Qlt_irrefl e1 (Qle_lt_trans e1 0 e1 (Qlt_le_weak e1 0 Hlt10) H01) with end).
  - assert (Hle' : Qle (0 + e0) (e1 + e0)).
    { apply (Qplus_le_compat 0 e1 e0 e0).
      - exact Hle01.
      - apply Qle_refl. }
    rewrite Qplus_0_l in Hle'.
    exact (match Qlt_irrefl (e1 + e0)
             (Qlt_le_trans (e1 + e0) e0 (e1 + e0) Hsum Hle') with end).
Qed.

(* ============================================================ *)
(* §2 log 切线反向严格排除（该前提的可达剩余半支闭合件）。               *)
(*   对一切 x > 0：¬(x−1 < log x)。材料：UpRealLeB real_log_le_linear_B  *)
(*   （B 形，eps 形源件 S07 real_log_le_linear_eps）+ §1。                *)
(*   此前库内无 plain 形实例件，本件为首个。                             *)
(* ============================================================ *)

Lemma ydll_log_tangent_not_gt :
  forall (x : Real) (Hx : real_lt real_zero x),
  Not (real_lt (real_plus x (real_opp real_one)) (real_log x Hx)).
Proof.
  intros x Hx Hgt.
  apply (ydll_le_b_not_gt (real_log x Hx) (real_plus x (real_opp real_one))).
  - exact (real_log_le_linear_B x Hx).
  - exact Hgt.
Qed.

(* ============================================================ *)
(* §3 前提实例的条件消解件（¬¬ 闭包面）。                                *)
(*   假设位即 :1035 前提的实例面等同形（见文件头对齐节）；在此假设下，   *)
(*   凡知 x ≠ 1 者得严格切线支。eq 支经 t1_log_eq_linear_inject 零新增。 *)
(* ============================================================ *)

Lemma ydll_cond_strict_of_ne_one :
  (forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one))) ->
  forall (x : Real) (Hx : real_lt real_zero x),
  Not (real_eq x real_one) ->
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros Hslot x Hx Hne1.
  destruct (Hslot x Hx) as [Hlt | Heq].
  - exact Hlt.
  - exact (match Hne1 (t1_log_eq_linear_inject x Hx Heq) with end).
Qed.

(* ============================================================ *)
(* §4（主件/结论件）：前提实例 ⟹ 实数零等判定（real-LPO 族）。           *)
(*   论证：任取 u，对 x := e^{−u}（对一切 u 成立：real_exp_neg_pos）用    *)
(*   该前提。左支（log x < x−1）：若 u == 0 则 x == 1、log x == 0、       *)
(*   x−1 == 0，严格支自相矛盾（real_lt_irrefl）——故 u ≠ 0。               *)
(*   右支（log x == x−1）：经 log_inv_exp_neg_thm 得 log x == −u，        *)
(*   即 e^{−u} == 1 − u。u < 0 ⟹ x > 1 ⟹ klst_log_tangent_pos 严格切线    *)
(*   与相等支矛盾；0 < u ⟹ x < 1 ⟹ klst_log_tangent_neg 同理矛盾。        *)
(*   弱三分（real_weak_trich，S07:5719，直觉主义有效）推得 u == 0。        *)
(*   结论：前提实例至少与实数零等判定等强——该判定属 S07 头注自认不可证  *)
(*   的强三分/LPO 参照类。此前「具体载体 30-60 行代数链可达」的估计据此   *)
(*   降格：反向半支可达（§1/§2 已闭合），正向分支判定不可达（本件定理级）。*)
(* ============================================================ *)

Theorem ydll_lpo_barrier :
  (forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one))) ->
  forall u : Real, Or (Not (real_eq u real_zero)) (real_eq u real_zero).
Proof.
  intros Hslot u.
  assert (Hxe : real_lt real_zero (real_exp_neg u))
    by exact (real_exp_neg_pos u).
  destruct (Hslot (real_exp_neg u) Hxe) as [Hlt | Heq].
  - (* 左支 ⟹ u ≠ 0 *)
    apply inl. intro Hu0.
    assert (Hx1 : real_eq (real_exp_neg u) real_one).
    { exact (real_eq_trans (real_exp_neg u)
                           (cauchy_real_exp (real_opp real_zero)) real_one
               (cauchy_real_exp_wd (real_opp u) (real_opp real_zero)
                  (RealSetoid.real_eq_opp_compat u real_zero Hu0))
               (real_eq_trans (cauchy_real_exp (real_opp real_zero))
                              (cauchy_real_exp real_zero) real_one
                  (cauchy_real_exp_wd (real_opp real_zero) real_zero
                     real_opp_zero)
                  cauchy_real_exp_zero)). }
    assert (Hlog0 : real_eq (real_log (real_exp_neg u) Hxe) real_zero).
    { exact (real_eq_trans (real_log (real_exp_neg u) Hxe)
                           (real_log real_one real_lt_zero_one) real_zero
               (real_log_wd (real_exp_neg u) real_one Hxe real_lt_zero_one
                  Hx1)
               (real_log_one real_lt_zero_one)). }
    assert (Hrhs0 : real_eq (real_plus (real_exp_neg u) (real_opp real_one))
                            real_zero).
    { exact (real_eq_trans (real_plus (real_exp_neg u) (real_opp real_one))
                           (real_plus real_one (real_opp real_one)) real_zero
               (RealSetoid.real_eq_plus_compat (real_exp_neg u)
                  (real_opp real_one) real_one (real_opp real_one) Hx1
                  (real_eq_refl (real_opp real_one)))
               (real_plus_opp real_one)). }
    exact (real_lt_irrefl real_zero
             (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                        real_zero
                                        (real_plus (real_exp_neg u)
                                           (real_opp real_one))
                                        real_zero
                                        Hlog0 Hrhs0 Hlt)).
  - (* 右支 ⟹ 双侧切线排除 ⟹ 弱三分推得 u == 0 *)
    assert (Hequ : real_eq (real_log (real_exp_neg u) Hxe) (real_opp u)).
    { exact (log_inv_exp_neg_thm (real_opp u) Hxe). }
    assert (Hreq : real_eq (real_opp u)
                           (real_plus (real_exp_neg u) (real_opp real_one))).
    { exact (real_eq_trans (real_opp u) (real_log (real_exp_neg u) Hxe)
                           (real_plus (real_exp_neg u) (real_opp real_one))
               (real_eq_sym (real_log (real_exp_neg u) Hxe) (real_opp u) Hequ)
               Heq). }
    assert (Hneg : Not (real_lt u real_zero)).
    { intro Hult.
      assert (Houpos : real_lt real_zero (real_opp u)).
      { exact (RealSetoid.real_lt_id_l real_zero (real_opp real_zero)
                 (real_opp u)
                 (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)
                 (real_opp_lt_compat u real_zero Hult)). }
      assert (Hx1lt : real_lt real_one (real_exp_neg u)).
      { exact (RealSetoid.real_lt_id_l real_one (cauchy_real_exp real_zero)
                 (real_exp_neg u)
                 (real_eq_sym (cauchy_real_exp real_zero) real_one
                    cauchy_real_exp_zero)
                 (cauchy_real_exp_mono real_zero (real_opp u) Houpos)). }
      exact (real_lt_irrefl (real_plus (real_exp_neg u) (real_opp real_one))
               (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          Heq
                                          (real_eq_refl (real_plus
                                             (real_exp_neg u)
                                             (real_opp real_one)))
                                          (klst_log_tangent_pos
                                             (real_exp_neg u) Hxe Hx1lt))). }
    assert (Hpos : Not (real_lt real_zero u)).
    { intro Hugt.
      assert (Hxlt1 : real_lt (real_exp_neg u) real_one).
      { exact (RealSetoid.real_lt_id_r (cauchy_real_exp (real_opp u))
                 (cauchy_real_exp real_zero) real_one cauchy_real_exp_zero
                 (cauchy_real_exp_mono (real_opp u) real_zero
                    (real_lt_zero_opp u Hugt))). }
      exact (real_lt_irrefl (real_plus (real_exp_neg u) (real_opp real_one))
               (RealSetoid.real_lt_compat (real_log (real_exp_neg u) Hxe)
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          (real_plus (real_exp_neg u)
                                             (real_opp real_one))
                                          Heq
                                          (real_eq_refl (real_plus
                                             (real_exp_neg u)
                                             (real_opp real_one)))
                                          (klst_log_tangent_neg
                                             (real_exp_neg u) Hxe Hxlt1))). }
    apply inr. exact (real_weak_trich u real_zero Hneg Hpos).
Qed.

(* ============================================================ *)
(* 收尾核验：四件逐条（全须 Closed under the global context）             *)
(* ============================================================ *)

Print Assumptions ydll_le_b_not_gt.
Print Assumptions ydll_log_tangent_not_gt.
Print Assumptions ydll_cond_strict_of_ne_one.
Print Assumptions ydll_lpo_barrier.
