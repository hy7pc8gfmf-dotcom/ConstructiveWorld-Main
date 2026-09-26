(* ============================================================ *)
(* UpDPOLip.v *)
(* *)
(* 目的： DPO softplus 的 Lipschitz 敏感性界。 *)
(* 主件： real_softplus_lipschitz：softplus 的 1-Lipschitz 界；real_softplus_mono / real_softplus_diff_le 单调与差分界。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： β > 0 与参考策略逐点正以显式 Variable 前提给出；序谓词为 Or(lt, eq) 强编码，abs 形态边界见正文。 *)
(* 编译配方：SW2 全字面环境（COQLIB/ROCQLIB/OCAMLLIB/COQPATH 置空）， *)
(*   Rocq 9.1 coqc -q -native-compiler no，-Q 单根。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpDPOLip.v —— A4/B5 升级：DPO softplus-Lipschitz 敏感性界     *)
(* 日期：2026-09-07。源：热点扫描 A4/B5（分析-219平凡定理热点扫描） *)
(* 件 1 real_softplus 定义 + 恒等桥 + 单调性                     *)
(* 件 2 real_softplus_diff_le（序前提单侧核，Lipschitz 数学核）   *)
(*      + real_softplus_lipschitz（Or 序前提 abs/metric 推论）   *)
(* 件 3 real_dpo_pair_loss_sensitivity（DPO 损失敏感性装配）      *)
(* 纪律：纯构造性 / Set 层 / 零 公理 / 零 承认件 / 零经典。    *)
(* 诚实边界：库内 real_le := Or real_lt real_eq（强编码），abs 形  *)
(*   态无条件全称版需序二分（LPO 等价，构造性不可达）；故 abs 版  *)
(*   以 Or (real_le x y) (real_le y x) 为显式 Set 层前提          *)

(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* 件 1：real_softplus 定义、恒等桥、单调性                      *)
(* ============================================================ *)

(* softplus x := log(1 + e^{−x})（DPO logit 损失的 softplus 形态；
   正性证书复用根内 real_sigmoid_denom_pos：1 + e^{−x} > 0）。 *)
Definition real_softplus (x : Real) : Real :=
  real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* 恒等桥：real_softplus x == real_dpo_logit x == −log σ(x)。 *)
Lemma real_softplus_eq_dpo_logit : forall x : Real,
  real_eq (real_softplus x) (real_dpo_logit x).
Proof. intro x. apply real_eq_sym. exact (real_softplus_sigmoid_eq x). Qed.

(* 单调性（递减）：x ≤ y ⟹ softplus y ≤ softplus x
   （exp_neg 递减给 1+e^{−y} ≤ 1+e^{−x}；log 保序完成）。 *)
Lemma real_softplus_mono : forall x y : Real, real_le x y ->
  real_le (real_softplus y) (real_softplus x).
Proof.
  intros x y Hxy.
  apply (real_log_le_mono (real_plus real_one (real_exp_neg y))
                          (real_plus real_one (real_exp_neg x))
                          (real_sigmoid_denom_pos y)
                          (real_sigmoid_denom_pos x)).
  exact (real_le_plus_compat real_one real_one
                             (real_exp_neg y) (real_exp_neg x)
                             (real_le_refl real_one)
                             (real_exp_neg_le_decr x y Hxy)).
Qed.

(* u ≤ 0 ⟹ 1 ≤ e^{−u}（e^0 == 1 换形 + exp_neg 递减）。 *)
Lemma real_one_le_exp_neg_of_le_zero : forall u : Real, real_le u real_zero ->
  real_le real_one (real_exp_neg u).
Proof.
  intros u Hu.
  apply (real_le_trans real_one (real_exp_neg real_zero) (real_exp_neg u)).
  - apply real_eq_le_bridge.
    apply real_eq_sym. exact real_exp_neg_zero.
  - exact (real_exp_neg_le_decr u real_zero Hu).
Qed.

(* b ≤ a ⟹ b − a ≤ 0（减法非正；加法保序 + a + (−a) == 0）。 *)
Lemma real_diff_le_zero : forall a b : Real, real_le b a ->
  real_le (real_plus b (real_opp a)) real_zero.
Proof.
  intros a b Hba.
  apply (real_le_trans (real_plus b (real_opp a))
                       (real_plus a (real_opp a)) real_zero).
  - exact (real_le_plus_compat b a (real_opp a) (real_opp a)
                                  Hba (real_le_refl (real_opp a))).
  - apply real_eq_le_bridge. exact (real_plus_opp a).
Qed.

(* 代数：e^{−b} == e^{−a}·e^{−(b−a)}（参数换形 + exp 加法性）。 *)
Lemma dpo_real_exp_neg_split : forall a b : Real,
  real_eq (real_exp_neg b)
          (real_mult (real_exp_neg a)
                     (real_exp_neg (real_plus b (real_opp a)))).
Proof.
  intros a b.
  apply (real_eq_trans (real_exp_neg b)
                       (real_exp_neg (real_plus a (real_plus b (real_opp a)))) _).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat b (real_plus a (real_plus b (real_opp a)))).
    apply real_eq_sym.
    (* a + (b − a) == b：assoc → comm → assoc⁻¹ → opp 消去 → 右零 *)
    apply (real_eq_trans (real_plus a (real_plus b (real_opp a)))
                         (real_plus (real_plus a b) (real_opp a)) b).
    + exact (real_plus_assoc a b (real_opp a)).
    + apply (real_eq_trans (real_plus (real_plus a b) (real_opp a))
                           (real_plus (real_plus b a) (real_opp a)) b).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                              (real_plus b a) (real_opp a)).
        -- exact (real_plus_comm a b).
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_plus (real_plus b a) (real_opp a))
                             (real_plus b (real_plus a (real_opp a))) b).
        -- apply real_eq_sym.
           exact (real_plus_assoc b a (real_opp a)).
        -- apply (real_eq_trans (real_plus b (real_plus a (real_opp a)))
                                (real_plus b real_zero) b).
           ++ apply (RealSetoid.real_eq_plus_compat b (real_plus a (real_opp a))
                                                    b real_zero).
              ** apply real_eq_refl.
              ** exact (real_plus_opp a).
           ++ exact (real_plus_zero b).
  - exact (real_exp_neg_plus a (real_plus b (real_opp a))).
Qed.

(* ============================================================ *)
(* 件 2：序前提单侧核（Lipschitz 数学核）                        *)
(*   b ≤ a ⟹ softplus b − softplus a ≤ a − b                     *)
(* 数学核：1+e^{−b} ≤ e^{a−b} + e^{−b} == (1+e^{−a})·e^{a−b}     *)
(*   （e^{a−b} ≥ 1 由 b ≤ a），两侧取 log + log 加法性完成。      *)
(* ============================================================ *)
Lemma real_softplus_diff_le : forall a b : Real, real_le b a ->
  real_le (real_plus (real_softplus b) (real_opp (real_softplus a)))
          (real_plus a (real_opp b)).
Proof.
  intros a b Hba.
  set (u := real_plus b (real_opp a)).
  set (E := real_exp_neg u).
  set (A := real_plus real_one (real_exp_neg a)).
  set (B := real_plus real_one (real_exp_neg b)).
  (* 步 1：E = e^{a−b} ≥ 1 *)
  assert (Hu0 : real_le u real_zero) by exact (real_diff_le_zero a b Hba).
  assert (HE1 : real_le real_one E) by exact (real_one_le_exp_neg_of_le_zero u Hu0).
  (* 步 2：恒等式 A·E == E + e^{−b} *)
  assert (HQ : real_eq (real_mult A E) (real_plus E (real_exp_neg b))).
  { apply (real_eq_trans (real_mult A E)
           (real_plus (real_mult E real_one) (real_mult E (real_exp_neg a))) _).
    - apply (real_eq_trans (real_mult A E)
              (real_mult E (real_plus real_one (real_exp_neg a))) _).
      + exact (real_mult_comm A E).
      + exact (real_distrib E real_one (real_exp_neg a)).
    - apply (RealSetoid.real_eq_plus_compat (real_mult E real_one)
                                            (real_mult E (real_exp_neg a))
                                            E (real_exp_neg b)).
      + exact (real_mult_one E).
      + (* E·e^{−a} == e^{−b}：dpo_real_exp_neg_split + 乘法交换 *)
        apply real_eq_sym.
        apply (real_eq_trans (real_exp_neg b)
                             (real_mult (real_exp_neg a) E) _).
        * exact (dpo_real_exp_neg_split a b).
        * exact (real_mult_comm (real_exp_neg a) E).
  }
  (* 步 3：B ≤ A·E（1 ≤ E 加法保序 + 恒等式换形） *)
  assert (HB : real_le B (real_mult A E)).
  { apply (real_le_trans B (real_plus E (real_exp_neg b)) (real_mult A E)).
    - exact (real_le_plus_compat real_one E (real_exp_neg b) (real_exp_neg b)
                                  HE1 (real_le_refl (real_exp_neg b))).
    - apply real_eq_le_bridge. apply real_eq_sym. exact HQ.
  }
  (* 步 4：log 完成：softplus b ≤ softplus a + (a − b) *)
  assert (Hlog : real_le (real_softplus b)
                         (real_plus (real_softplus a) (real_plus a (real_opp b)))).
  { apply (real_le_trans (real_softplus b)
             (real_log (real_mult A E)
                       (real_mult_positive A E (real_sigmoid_denom_pos a)
                                           (real_exp_neg_pos u))) _).
    - apply (real_log_le_mono B (real_mult A E) (real_sigmoid_denom_pos b)
              (real_mult_positive A E (real_sigmoid_denom_pos a)
                                      (real_exp_neg_pos u)) HB).
    - apply real_eq_le_bridge.
      apply (real_eq_trans (real_log (real_mult A E)
                (real_mult_positive A E (real_sigmoid_denom_pos a)
                                        (real_exp_neg_pos u)))
        (real_plus (real_log A (real_sigmoid_denom_pos a))
                   (real_log E (real_exp_neg_pos u))) _).
      + exact (real_log_mult A E (real_sigmoid_denom_pos a) (real_exp_neg_pos u)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log A (real_sigmoid_denom_pos a))
                 (real_log E (real_exp_neg_pos u))
                 (real_softplus a) (real_plus a (real_opp b))).
        * apply real_eq_refl.
        * 
          apply (real_eq_trans (real_log E (real_exp_neg_pos u))
                               (real_opp u) _).
          -- exact (log_inv_exp_neg_thm (real_opp u) (real_exp_neg_pos u)).
          -- apply (real_eq_trans (real_opp u)
                     (real_plus (real_opp b) (real_opp (real_opp a))) _).
             ++ exact (real_opp_plus b (real_opp a)).
             ++ apply (real_eq_trans (real_plus (real_opp b) (real_opp (real_opp a)))
                                     (real_plus (real_opp b) a) _).
                ** apply (RealSetoid.real_eq_plus_compat (real_opp b)
                            (real_opp (real_opp a)) (real_opp b) a).
                   --- apply real_eq_refl.
                   --- exact (real_opp_opp a).
                ** exact (real_plus_comm (real_opp b) a).
  }
  (* 步 5：移项：softplus b − softplus a ≤ a − b *)
  apply (real_le_trans (real_plus (real_softplus b) (real_opp (real_softplus a)))
                       (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                  (real_opp (real_softplus a))) _).
  - exact (real_le_plus_compat (real_softplus b)
                               (real_plus (real_softplus a) (real_plus a (real_opp b)))
                               (real_opp (real_softplus a)) (real_opp (real_softplus a))
                               Hlog (real_le_refl (real_opp (real_softplus a)))).
  - apply real_eq_le_bridge.
    apply (real_eq_trans (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                    (real_opp (real_softplus a)))
                         (real_plus (real_softplus a)
                                    (real_plus (real_plus a (real_opp b))
                                               (real_opp (real_softplus a)))) _).
    + apply real_eq_sym.
      exact (real_plus_assoc (real_softplus a) (real_plus a (real_opp b))
                             (real_opp (real_softplus a))).
    + apply (real_eq_trans (real_plus (real_softplus a)
                              (real_plus (real_plus a (real_opp b))
                                         (real_opp (real_softplus a))))
                           (real_plus (real_softplus a)
                              (real_plus (real_opp (real_softplus a))
                                         (real_plus a (real_opp b)))) _).
      * apply (RealSetoid.real_eq_plus_compat (real_softplus a)
                 (real_plus (real_plus a (real_opp b)) (real_opp (real_softplus a)))
                 (real_softplus a)
                 (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b)))).
        -- apply real_eq_refl.
        -- exact (real_plus_comm (real_plus a (real_opp b))
                                 (real_opp (real_softplus a))).
      * apply (real_eq_trans (real_plus (real_softplus a)
                   (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b))))
                (real_plus (real_plus (real_softplus a) (real_opp (real_softplus a)))
                           (real_plus a (real_opp b))) _).
        -- exact (real_plus_assoc (real_softplus a) (real_opp (real_softplus a))
                                  (real_plus a (real_opp b))).
        -- apply (real_eq_trans (real_plus (real_plus (real_softplus a)
                                             (real_opp (real_softplus a)))
                                           (real_plus a (real_opp b)))
                                (real_plus real_zero (real_plus a (real_opp b))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_softplus a) (real_opp (real_softplus a)))
                       (real_plus a (real_opp b))
                       real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_opp (real_softplus a)).
              ** apply real_eq_refl.
           ++ apply (real_eq_trans (real_plus real_zero (real_plus a (real_opp b)))
                                   (real_plus (real_plus a (real_opp b)) real_zero) _).
              ** exact (real_plus_comm real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_zero (real_plus a (real_opp b))).
Qed.

(* ============================================================ *)
(* 件 2 完成：abs 消解工具 + Or 序前提 Lipschitz 主推论          *)
(* ============================================================ *)

(* 0 ≤ d ⟹ |d| == d（real_abs_pos_req 的 le 版：Or 两支）。 *)
Lemma real_abs_nonneg_eq : forall d : Real, real_le real_zero d ->
  real_eq (real_abs d) d.
Proof.
  intros d Hd. destruct Hd as [Hlt | Heq].
  - exact (real_abs_pos_req d Hlt).
  - apply (real_eq_trans (real_abs d) real_zero d).
    + apply (real_eq_trans (real_abs d) (real_abs real_zero) real_zero).
      * apply (RealSetoid.real_eq_abs_compat d real_zero (real_eq_sym real_zero d Heq)).
      * exact real_abs_zero_req.
    + exact Heq.
Qed.

(* 减法式的反号形态：u − v == −(v − u)。 *)
Lemma real_minus_opp_form : forall u v : Real,
  real_eq (real_plus u (real_opp v)) (real_opp (real_plus v (real_opp u))).
Proof.
  intros u v.
  apply (real_eq_trans (real_plus u (real_opp v))
                       (real_plus (real_opp v) u) _).
  - exact (real_plus_comm u (real_opp v)).
  - apply (real_eq_trans (real_plus (real_opp v) u)
                         (real_plus (real_opp v) (real_opp (real_opp u))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                                            (real_opp v) (real_opp (real_opp u))).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (real_opp_opp u).
    + apply real_eq_sym. exact (real_opp_plus v (real_opp u)).
Qed.

(* d == −e 且 0 ≤ e ⟹ |d| == e（abs 经 opp 对称消解）。 *)
Lemma real_abs_opp_form : forall d e : Real,
  real_eq d (real_opp e) -> real_le real_zero e -> real_eq (real_abs d) e.
Proof.
  intros d e Hd He.
  apply (real_eq_trans (real_abs d) (real_abs e) e).
  - apply (real_eq_trans (real_abs d) (real_abs (real_opp e)) (real_abs e)).
    + apply (RealSetoid.real_eq_abs_compat d (real_opp e) Hd).
    + exact (real_abs_opp e).
  - exact (real_abs_nonneg_eq e He).
Qed.

(* 主推论：softplus 的 1-Lipschitz 敏感性界（metric 形态）。
   前提 Or (real_le x y) (real_le y x) 为显式 Set 层序二分
   （构造性实数上不可整体消去，见文件头诚实边界注记）。 *)
Theorem real_softplus_lipschitz : forall x y : Real,
  Or (real_le x y) (real_le y x) ->
  real_le (real_metric (real_softplus x) (real_softplus y))
          (real_metric x y).
Proof.
  intros x y Hor. unfold real_metric.
  destruct Hor as [Hxy | Hyx].
  - (* 分支 1：x ≤ y。|sp x − sp y| == sp x − sp y；|x − y| == y − x。 *)
    assert (Hdec : real_le (real_softplus y) (real_softplus x))
      by exact (real_softplus_mono x y Hxy).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus x) (real_opp (real_softplus y))))
      by exact (real_le_minus_nonneg_aux (real_softplus y) (real_softplus x) Hdec).
    assert (Hd2 : real_le real_zero (real_plus y (real_opp x)))
      by exact (real_le_minus_nonneg_aux x y Hxy).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus x) (real_opp (real_softplus y))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_nonneg_eq (real_plus (real_softplus x) (real_opp (real_softplus y))) Hd1).
    + apply (real_le_trans (real_plus (real_softplus x) (real_opp (real_softplus y)))
                           (real_plus y (real_opp x)) _).
      * exact (real_softplus_diff_le y x Hxy).
      * apply real_eq_le_bridge. apply real_eq_sym.
        exact (real_abs_opp_form (real_plus x (real_opp y))
                                 (real_plus y (real_opp x))
                                 (real_minus_opp_form x y) Hd2).
  - (* 分支 2：y ≤ x。|sp x − sp y| == sp y − sp x（opp 桥）；|x − y| == x − y。 *)
    assert (Hdec : real_le (real_softplus x) (real_softplus y))
      by exact (real_softplus_mono y x Hyx).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus y) (real_opp (real_softplus x))))
      by exact (real_le_minus_nonneg_aux (real_softplus x) (real_softplus y) Hdec).
    assert (Hd2 : real_le real_zero (real_plus x (real_opp y)))
      by exact (real_le_minus_nonneg_aux y x Hyx).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus y) (real_opp (real_softplus x))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_opp_form (real_plus (real_softplus x) (real_opp (real_softplus y)))
                               (real_plus (real_softplus y) (real_opp (real_softplus x)))
                               (real_minus_opp_form (real_softplus x) (real_softplus y))
                               Hd1).
    + apply (real_le_trans (real_plus (real_softplus y) (real_opp (real_softplus x)))
                           (real_plus x (real_opp y)) _).
      * exact (real_softplus_diff_le x y Hyx).
      * apply real_eq_le_bridge.
        apply real_eq_sym.
        exact (real_abs_nonneg_eq (real_plus x (real_opp y)) Hd2).
Qed.

(* ============================================================ *)
(* 件 3：DPO 损失敏感性装配                                      *)
(*   |L(π; w, l) − L(π*; w, l)| ≤ |β(log_ratio 差分) − (r_w − r_l)| *)
(*   （条件化形态：序二分前提为显式 Set 层 Or）。                *)
(* ============================================================ *)

(* metric 的 eq 兼容。 *)
Lemma real_metric_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_metric a b) (real_metric a' b').
Proof.
  intros a a' b b' Ha Hb. unfold real_metric.
  apply (RealSetoid.real_eq_abs_compat (real_plus a (real_opp b))
                                       (real_plus a' (real_opp b'))).
  apply (RealSetoid.real_eq_plus_compat a (real_opp b) a' (real_opp b') Ha).
  apply (RealSetoid.real_eq_opp_compat b b'). exact Hb.
Qed.

Section UpDpoSensMain.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* 策略 π 的 DPO logit 差：β·(log_ratio(π, w) − log_ratio(π, l))。 *)
Definition real_dpo_logit_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_plus (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_w))
            (real_opp (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_l))).

(* π* 的 DPO logit 差：真实奖励差分 r_w − r_l。 *)
Definition real_dpo_logit_star (s_w s_l : S) : Real :=
  real_plus (reward s_w) (real_opp (reward s_l)).

(* 桥 1：策略 DPO 损失 == softplus(logit 差)（定义性 + softplus 恒等桥）。 *)
Lemma real_dpo_loss_pair_eq_softplus : forall (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
          (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)).
Proof.
  intros pi Hpi s_w s_l.
  apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 桥 2：π* 处 DPO 损失 == softplus(真实奖励差分)
   （real_dpo_loss_at_pi_star + softplus 恒等桥）。 *)
Lemma real_dpo_loss_star_eq_softplus : forall s_w s_l : S,
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
             s_w s_l)
          (real_softplus (real_dpo_logit_star s_w s_l)).
Proof.
  intros s_w s_l.
  apply (real_eq_trans _ (real_dpo_logit (real_dpo_logit_star s_w s_l)) _).
  - exact (real_dpo_loss_at_pi_star S reward beta beta_pos pi_ref pi_ref_pos
                                    Z_align Z_align_pos s_w s_l).
  - apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 主件：DPO 损失敏感性界（metric 形态，序二分前提显式 Set 层 Or）。
   内容：metric L pi L_star ≤ metric logit pi logit_star
   （策略损失到 pi_star 损失的距离 ≤ logit 差分的距离）。 *)
Theorem real_dpo_pair_loss_sensitivity :
  forall (pi : S -> Real) (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  Or (real_le (real_dpo_logit_star s_w s_l) (real_dpo_logit_pair pi Hpi s_w s_l))
      (real_le (real_dpo_logit_pair pi Hpi s_w s_l) (real_dpo_logit_star s_w s_l)) ->
  real_le (real_metric (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                          s_w s_l))
          (real_metric (real_dpo_logit_pair pi Hpi s_w s_l)
                       (real_dpo_logit_star s_w s_l)).
Proof.
  intros pi Hpi s_w s_l Hor.
  assert (HL : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
    by exact (real_dpo_loss_pair_eq_softplus pi Hpi s_w s_l).
  assert (HS : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                             s_w s_l)
                       (real_softplus (real_dpo_logit_star s_w s_l)))
    by exact (real_dpo_loss_star_eq_softplus s_w s_l).
  apply (real_le_trans _ (real_metric (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_softplus (real_dpo_logit_star s_w s_l))) _).
  - apply real_eq_le_bridge.
    exact (real_metric_eq_compat _ _ _ _ HL HS).
  - unfold real_metric.
    destruct Hor as [H | H].
    + (* 分支 1：X* ≤ Xπ ⟹ Lπ ≤ L*；|Lπ − L*| == L* − Lπ ≤ Xπ − X* == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                             (real_softplus (real_dpo_logit_star s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_star s_w s_l)
                                     (real_dpo_logit_pair pi Hpi s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                           (real_softplus (real_dpo_logit_star s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                 (real_opp (real_dpo_logit_star s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_star s_w s_l)
                                           (real_dpo_logit_pair pi Hpi s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_opp_form (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                                 (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                                 (real_minus_opp_form (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                      (real_softplus (real_dpo_logit_star s_w s_l)))
                                 Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                             (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_opp (real_dpo_logit_star s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_dpo_logit_star s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_nonneg_eq (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                                (real_opp (real_dpo_logit_star s_w s_l))) Hd2).
    + (* 分支 2：Xπ ≤ X* ⟹ L* ≤ Lπ；|Lπ − L*| == Lπ − L* ≤ X* − Xπ == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_star s_w s_l))
                             (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_pair pi Hpi s_w s_l)
                                     (real_dpo_logit_star s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_star s_w s_l))
                                           (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_star s_w s_l)
                                 (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_pair pi Hpi s_w s_l)
                                           (real_dpo_logit_star s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_nonneg_eq (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                             (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                             (real_plus (real_dpo_logit_star s_w s_l)
                                        (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_star s_w s_l)
                                        (real_dpo_logit_pair pi Hpi s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_opp_form (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                               (real_opp (real_dpo_logit_star s_w s_l)))
                                    (real_plus (real_dpo_logit_star s_w s_l)
                                               (real_opp (real_dpo_logit_pair pi Hpi s_w s_l)))
                                    (real_minus_opp_form (real_dpo_logit_pair pi Hpi s_w s_l)
                                                         (real_dpo_logit_star s_w s_l))
                                    Hd2).
Qed.

End UpDpoSensMain.
