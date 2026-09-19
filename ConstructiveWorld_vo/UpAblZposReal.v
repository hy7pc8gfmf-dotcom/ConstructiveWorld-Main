(* ============================================================ *)
(* UpAblZposReal.v —— 论文1 假设 B4 的柯西实数层消融件（AB2 席）      *)
(*                                                                *)
(* 目的：S05_AlignmentGRPO 主节第 54 行槽位「配分函数为正」在具体     *)
(*       柯西实数层（裸 Real 函数面）的无条件放电：以显式全参 forall  *)
(*       前件（逐项正 + 归一化 + 温度正）证明 Z_align 对应体为正。    *)
(*       连带收割 B8「正性求和」的实数层等价形（非空有限和）。        *)
(*                                                                *)
(* 主件清单与证明路线：                                            *)
(*   1. zabr_Z_align：配分函数的实数层定义——与 S05 主节 Z_align     *)
(*      定义逐字对齐（sum_over_S↦real_list_sum·l，mult↦real_mult，  *)
(*      exp_neg↦real_exp_neg，opp↦real_opp，inv_pos↦real_inv_pos；   *)
(*      参数序照 S05 迭代节放电形 reward·beta·beta_pos·pi_ref）。    *)
(*   2. zabr_list_sum_pos_cons（伴件·非平凡承载点）：折叠结构归纳。   *)
(*      归纳不变式取「任意头 w 的 cons 和」形，归纳步以头项正+尾和正  *)
(*      经 real_lt_plus_compat 拼接、real_lt_id_l 回写零侧规范形；    *)
(*      基例单元素以 real_lt_id_r + real_plus_zero 收口。全链显式     *)
(*      构造，零占位。                                              *)
(*   3. zabr_sum_over_S_pos（B8 实数层等价形）：逐项正 + 列表非空     *)
(*      ⟹ 和为正。非空前提取 S01 集合层 Not/Id 别名（零命题面泄露）。*)
(*      诚实边界：S05 抽象面无该前提（接口槽直断言）；实数层空表和    *)
(*      归约到 real_zero 不为正，故非空前提为可实现的最弱补全。       *)
(*   4. zabr_Z_align_pos（B4 主放电件）：前件=逐项正+归一化+温度正，   *)
(*      归一化与实数层零壹分离件 upreq_real_zero_ne_one 联合导出列表  *)
(*      非空（自建 Id→real_eq 传输桥 + real_eq_trans 链），再经伴件+  *)
(*      逐项正性链（real_mult_positive：参考策略正 × exp_neg_pos，    *)
(*      后者库内现态 S03 cauchy_real_exp_pos→S07 real_exp_neg_pos）收口。*)
(*                                                                *)
(* 依赖（只读消费，零改动）：S01–S08 全链；UpReqExpPos（零壹分离）。  *)
(* 备注：全件集合层面（Id/Not 用 S01 集合层别名，real_lt/real_eq 为  *)
(*       集合值）；零承认件；纯构造性；头注与注释全中文表述。         *)
(* ============================================================ *)
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

(* ===== 1. 配分函数实数层定义（与 S05 主节逐字对齐的镜像面） ===== *)
Definition zabr_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : real_lt real_zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => real_mult (pi_ref s)
    (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))) l.

(* ===== 2. 伴件之一：折叠归纳承载件（非平凡内容点） ===== *)
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
  - (* 步例：f w 与（w::t 的和）皆正，零侧回写规范形 *)
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

(* ===== 3. 伴件之二：B8 正性求和的实数层等价形 ===== *)
(* 与 S05:2535 槽位形（forall f，逐项正 ⟹ 和正）对齐；非空前提为    *)
(* 实数层可实现最弱补全（S01 集合层 Not/Id，零命题面泄露）。         *)
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
  - (* 非空：化归到折叠归纳承载件 *)
    exact (zabr_list_sum_pos_cons X f rest w Hf).
Qed.

(* ===== 4. 主件：B4 的实数层无条件放电 ===== *)
(* 语句面与 S05 主节 49-54 行逐字对齐：Z_align 体=参考策略逐项乘     *)
(* exp_neg(−r(s)/β) 的有限和；前件=逐项正 + 归一化 + 温度正。        *)
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
  - (* 列表非空：归一化给出和=1，空表给出和=0，零壹分离件裁决矛盾 *)
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
  - (* 逐项正：参考策略正 × 指数正（库内现态链直连） *)
    intro s.
    apply real_mult_positive.
    + exact (Hrefpos s).
    + apply real_exp_neg_pos.
Qed.

(* ===== 审计口：零假设面留痕 ===== *)
Print Assumptions zabr_list_sum_pos_cons.
Print Assumptions zabr_sum_over_S_pos.
Print Assumptions zabr_Z_align_pos.

(* ===== 提取审计：独立隔离目录（一人一目录） ===== *)
Set Extraction Output Directory "../_ab2_zposreal_extract".
Separate Extraction zabr_Z_align.
Separate Extraction zabr_list_sum_pos_cons.
Separate Extraction zabr_sum_over_S_pos.
Separate Extraction zabr_Z_align_pos.
