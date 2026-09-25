(* ==========================================================================)
   UpAblZposReal.v — Z_align 正性的实数层实例件
   使命: zabr_Z_align 定义、zabr_list_sum_pos_cons（cons 求和正性）、zabr_sum_over_S_pos（SumOver 正性）与 zabr_Z_align_pos 主件。
   依赖: S01_BaseRing 至 S08_RealMainlineDPO、UpReqExpPos；Stdlib Extraction。
   对标: 对齐场正性的具体实例供给（逐分支见证构造）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqExpPos.
From Stdlib Require Import Extraction.

(* ===== 1. 配分函数实数层定义（与 S05 主节逐字对齐的对应面） ===== *)
Definition zabr_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : real_lt real_zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => real_mult (pi_ref s)
    (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))) l.

(* ===== 2. 伴件之一：折叠归纳引理 ===== *)
(* 命题形取「任意头 w 的 cons 和」：归纳步尾和恰为前一实例，免去     *)
(* 非空前提参与归纳。基例=单元素（f w + 0 正）；步例=头正 + 尾和正。 *)
Lemma zabr_list_sum_pos_cons :
  forall (X : Set) (f : X -> Real) (l : list X) (w : X),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f (w :: l)).
Proof.
  intros X f l.
  induction l as [| x t IH]; intro w; intro Hf.
  - (* 基例：[w] 的和 = f w + 0 *)
    simpl.
    apply (RealSetoid.real_lt_id_r real_zero (f w) (real_plus (f w) real_zero)).
    + apply (real_eq_sym (real_plus (f w) real_zero) (f w)).
      apply (real_plus_zero (f w)).
    + exact (Hf w).
  - (* 步例：f w 与（w::t 的和）皆正，零侧记录规范形 *)
    simpl.
    apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
             (real_plus (f w) (real_plus (f x) (real_list_sum X f t)))).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (real_lt_plus_compat real_zero (f w) real_zero
               (real_plus (f x) (real_list_sum X f t))).
      * exact (Hf w).
      * exact (IH x Hf).
Qed.

(* ===== 3. 伴件之二：正性求和的实数层等价形 ===== *)
(* 与 S05 的 sum_over_S 正性假设形（forall f，逐项正 ⟹ 和正）对齐；  *)
(* 非空前提为实数层可实现最弱补全（S01 集合层 Not/Id，零命题面泄露）。*)
Theorem zabr_sum_over_S_pos :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros X f l Hnn Hf.
  destruct l as [| w rest].
  - (* 空表：与非空前提直接矛盾 *)
    destruct (Hnn id_refl).
  - (* 非空：化归到折叠归纳引理 zabr_list_sum_pos_cons *)
    exact (zabr_list_sum_pos_cons X f rest w Hf).
Qed.

(* ===== 4. 主定理：Z_align 正性的实数层无条件消解 ===== *)
(* 语句面与 S05 主节逐字对齐：Z_align 体=参考策略逐项乘              *)
(* exp_neg(−r(s)/β) 的有限和；前提=逐项正 + 归一化 + 温度正。         *)
Theorem zabr_Z_align_pos :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : real_lt real_zero beta) (pi_ref : X -> Real),
    (forall s : X, real_lt real_zero (pi_ref s)) ->
    real_eq (real_list_sum X pi_ref l) real_one ->
    real_lt real_zero (zabr_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref Hrefpos Hnorm.
  unfold zabr_Z_align.
  apply (zabr_sum_over_S_pos X _ l).
  - (* 列表非空：归一化给出和=1，空表给出和=0，经零壹分离引理
       upreq_real_zero_ne_one 导出矛盾 *)
    intro Hnil.
    assert (Hsum0 : real_eq (real_list_sum X pi_ref l) real_zero).
    { exact (real_eq_trans (real_list_sum X pi_ref l) (real_list_sum X pi_ref nil)
               real_zero
               (match Hnil in Id _ y return
                  real_eq (real_list_sum X pi_ref l) (real_list_sum X pi_ref y)
                with id_refl => real_eq_refl _ end)
               (real_eq_refl real_zero)). }
    exact (upreq_real_zero_ne_one
            (real_eq_trans real_zero (real_list_sum X pi_ref l) real_one
               (real_eq_sym (real_list_sum X pi_ref l) real_zero Hsum0) Hnorm)).
  - (* 逐项正：参考策略正 × 指数正（real_mult_positive 与 real_exp_neg_pos） *)
    intro s.
    apply real_mult_positive.
    + exact (Hrefpos s).
    + apply real_exp_neg_pos.
Qed.

(* ===== 假设面自检（Print Assumptions） ===== *)
Print Assumptions zabr_list_sum_pos_cons.
Print Assumptions zabr_sum_over_S_pos.
Print Assumptions zabr_Z_align_pos.

(* ===== 提取审计（独立隔离输出目录） ===== *)
Set Extraction Output Directory "../_ab2_zposreal_extract".
Separate Extraction zabr_Z_align.
Separate Extraction zabr_list_sum_pos_cons.
Separate Extraction zabr_sum_over_S_pos.
Separate Extraction zabr_Z_align_pos.
