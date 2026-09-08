(* UpReqDist.v — 签名迁移批 2：分布 / 自由能 / GRPO 簇的 req 系重述与实例化
   母本：签名迁移规划书-20260908.md（批 2 清单，§5）；
   模板：UpSigMigrate.v（13 Qed 试点件）+ UpReqAlgebra.v（批 1 地基，直接消费）。
   纪律：纯构造性；Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）；
   纯 term-mode（req_trans 链 + compat 桥，零 Morphisms 依赖）；
   消费批 1 地基 UpReqAlgebra（57 件）与基内对接面 exp_neg_req_compat_setoid。
   ----------------------------------------------------------------
   诚实签名变化台账（规划书 §7.4）：
   1. log 前提化：setoid log 带 lt zero 前提，free_energy/relative_entropy/
     entropy_dist/cross_entropy 定义逐件加 positive_dist 参数（δ 记账）。
   2. minus 非接口字段：以批 1 req_minus 同形重建（δ 透明）。
   3. T2① 接口缺口桥（ReqFEPBridge 节，保留假设位；Real 实例可满足，
     实例化留待接口扩展批——批 1 ReqLogBridge 同判词）：
     - dist_log_inv_one_inv：log(inv x) = -log x（Id 系 log_inv_one_inv）；
     - dist_log_exp_neg：log(e^{-u}) = -u（Id 系 log_exp_neg）；
     - dist_log_le_linear：log x ≤ x-1 精确切线（Id 接口字段 L299；
       setoid 接口仅备逐 eps 形式 log_le_linear_eps——「深水区」注）；
     - dist_log_eq_linear：切点唯一 x=1（Id 接口字段 L304；setoid 缺）。
   4. SumOver setoid 对接面：批 1/试点件三性质（ext/linear/pos）+ Id 系
     SumOver 字段 sum_over_S_le / sum_over_S_zero_nonneg（L1415/L1426）
     的 req 镜像（sum_le / sum_zero_nonneg），同为 Section Hypothesis。
   5. SecondLaw：Not (Id (dynamics x) x) → Not (req (dynamics x) x)（签名变化）。
   6. square_nonneg（GRPO T1.5）：保持 Id 出口假设位（显式 forall 参数，
     T2 形态①；Id 系 L24301 同为诚实 Variable）。
   7. (a) 类消费：req_free_energy_kl_decomp @ UpSigMigrate 同构重述于本文件
     （消费形态需 UpSigMigrate.vo 锚；attn 树无该 .vo，重述并在对账表标注）。
   ----------------------------------------------------------------
   覆盖对账（req 件名 -> Id 原件 @ CW219 行号；批 2 清单逐条核销见文件尾）：
   【SumLayer（FEP 前 2 件）】reqd_sum_opp<-15801 reqd_sum_minus<-15830
   【FEP】req_boltzmann_normalized<-15846 req_boltzmann_mix_normalized<-15863
     req_boltzmann_log_decomp<-15912 req_free_energy_boltzmann<-15945
     req_energy_in_log_boltzmann<-16116 req_p_times_energy_decomp<-16198
     req_free_energy_kl_decomp<-16259 req_free_energy_kl_diff<-16443
     req_free_energy_diff_kl<-16489 req_relative_entropy_self_zero<-18483
     req_gibbs_pointwise<-16538 req_gibbs_inequality<-16629
     req_gibbs_equality<-16678 req_boltzmann_dist_pos<-16824
     req_min_free_energy_is_boltzmann<-16838 req_free_energy_min_unique<-16888
     req_entropy_neg_sum<-16946 req_free_energy_entropy<-16976
     req_entropy_deficit_kl<-16993 req_cross_entropy_decomp<-18094
     req_elbo_lower_bound<-18359 req_evidence_kl_decomp<-18373
     req_training_equivalence<-18657
   【GRPO】req_grpo_* 14 件<-23828..24096..24264..24327（清单见节头）
   【小节】req_steady_state_boltzmann<-15700 reqd_lt_mult_pos_cancel<-15741
     req_prob_dist_sum_linear<-24901 req_prob_dist_mix<-24910
     req_kl_nonneg<-24982 req_kl_zero_iff_eq<-24992
     req_second_law_irreversible<-27796
   【SqrtWitness】reqd_nat_to_R_plus_hom<-96551 reqd_nat_to_R_mult_hom<-96561
     reqd_nat_to_R_pos<-96586 reqd_sqrt_witness_sq<-96596
     reqd_sqrt_witness_nat_sq<-96602
   【U2 辅件】req_u2_nonneg_sum_zero<-23337 req_u2_minus_minus<-23363
     req_u2_kl_arg2_ext<-23369（主体 7 件待批 3，见尾清单）
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ReqDistCommon：批 2 公共机器（本文件需求生；          *)
(*   reqd_ 前缀避免与批 1 规划件 req_inv_pos_cancel/req_log_cancel 重名） *)
(* ============================================================ *)
Section ReqDistCommon.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* req 蕴含 le（lt_le_iff 右支；exp_neg_req_compat_setoid 同款反射形） *)
Lemma reqd_le_of_req : forall a b : R, req a b -> le a b.
Proof.
  intros a b H. apply (lt_le_iff a b). right. exact H.
Qed.

(* req_minus 的双参数兼容（Id 系 minus 同余；批 1 只有 plus a 同形式） *)
Lemma reqd_minus_compat : forall a b c d : R,
  req a b -> req c d -> req (req_minus a c) (req_minus b d).
Proof.
  intros a b c d Hab Hcd. unfold req_minus.
  exact (req_plus_compat a b (opp c) (opp d) Hab (req_opp_compat c d Hcd)).
Qed.

(* inv_pos 单射（Id 系经 destruct/eq_ind 免费；req 系经 inv_pos_correct
   + req_mult_cancel_l 双乘消去——批 1 §3.2 (c.2) 引擎第一件） *)
Lemma reqd_inv_pos_cancel : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  req (inv_pos a Ha) (inv_pos b Hb) -> req a b.
Proof.
  intros a b Ha Hb Hinv.
  assert (Hm : req (mult (inv_pos b Hb) a) (mult (inv_pos b Hb) b)).
  { apply (req_trans (mult (inv_pos b Hb) a) (mult a (inv_pos b Hb))
                     (mult (inv_pos b Hb) b)).
    - apply mult_comm.
    - apply (req_trans (mult a (inv_pos b Hb)) (mult a (inv_pos a Ha))
                       (mult (inv_pos b Hb) b)).
      + exact (req_mult_compat a a (inv_pos b Hb) (inv_pos a Ha)
                               (req_refl a)
                               (req_sym (inv_pos a Ha) (inv_pos b Hb) Hinv)).
      + apply (req_trans (mult a (inv_pos a Ha)) one (mult (inv_pos b Hb) b)).
        * apply inv_pos_correct.
        * apply (req_trans one (mult b (inv_pos b Hb)) (mult (inv_pos b Hb) b)).
          -- apply (req_sym (mult b (inv_pos b Hb)) one). apply inv_pos_correct.
          -- apply mult_comm. }
  exact (req_mult_cancel_l (inv_pos b Hb) a b (inv_pos_pos b Hb) Hm).
Qed.

(* log 单射（批 1 §3.2 (c.2) 引擎第二件；路线：req_exp_neg_opp_log
   （批 1：e^{log x}=x）+ req_opp_compat + exp_neg_req_compat_setoid（基内
   L66223）——不需要 exp 单射（其逆不可由接口导出，批 1 ReqLogBridge 实测），
   绕行成功，故本件为无条件导出引理而非桥） *)
Lemma reqd_log_cancel : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  req (log a Ha) (log b Hb) -> req a b.
Proof.
  intros a b Ha Hb Hlog.
  apply (req_trans a (exp_neg (opp (log a Ha))) b).
  - apply (req_sym (exp_neg (opp (log a Ha))) a). apply req_exp_neg_opp_log.
  - apply (req_trans (exp_neg (opp (log a Ha))) (exp_neg (opp (log b Hb))) b).
    + apply exp_neg_req_compat_setoid.
      exact (req_opp_compat (log a Ha) (log b Hb) Hlog).
    + apply req_exp_neg_opp_log.
Qed.

(* 乘积非负（Id 系 le_mult_nonneg_t12 的 req 镜像；le_mult_compat_weak
   字段 + mult_zero 运输） *)
Lemma reqd_le_mult_nonneg_t12 : forall a b : R,
  le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_l zero (mult zero b) (mult a b)).
  - exact (req_sym (mult zero b) zero
                   (req_trans (mult zero b) (mult b zero) zero
                              (mult_comm zero b) (mult_zero b))).
  - exact (le_mult_compat_weak zero a b Hb Ha).
Qed.

(* 正乘严格消去（Id 原件 TempStrictTools lt_mult_pos_cancel @15741：
   c > 0 且 a·c > 0 ⟹ a > 0；a == (a·c)·inv c） *)
Lemma reqd_lt_mult_pos_cancel : forall a c : R,
  lt zero c -> lt zero (mult a c) -> lt zero a.
Proof.
  intros a c Hc Hac.
  apply (lt_id_r zero (mult (mult a c) (inv_pos c Hc)) a).
  - apply (req_trans (mult (mult a c) (inv_pos c Hc))
                     (mult a (mult c (inv_pos c Hc))) a).
    + apply (req_sym (mult a (mult c (inv_pos c Hc)))
                     (mult (mult a c) (inv_pos c Hc))). apply mult_assoc.
    + apply (req_trans (mult a (mult c (inv_pos c Hc))) (mult a one) a).
      * exact (req_mult_compat a a (mult c (inv_pos c Hc)) one
                               (req_refl a) (inv_pos_correct c Hc)).
      * apply mult_one.
  - apply mult_positive.
    + exact Hac.
    + apply inv_pos_pos.
Qed.

(* 三项旋转：(a+b)+c == (a+c)+b（FEP 环链辅助） *)
Lemma reqd_plus_rot : forall a b c : R,
  req (plus (plus a b) c) (plus (plus a c) b).
Proof.
  intros a b c.
  apply (req_trans (plus (plus a b) c) (plus (plus a b) (plus c zero))
                   (plus (plus a c) b)).
  - apply (req_sym (plus (plus a b) (plus c zero)) (plus (plus a b) c)).
    exact (req_plus_compat (plus a b) (plus a b) (plus c zero) c
                           (req_refl (plus a b)) (plus_zero c)).
  - apply (req_trans (plus (plus a b) (plus c zero))
                     (plus (plus a c) (plus b zero)) (plus (plus a c) b)).
    + apply req_plus_swap_mid.
    + exact (req_plus_compat (plus a c) (plus a c) (plus b zero) b
                             (req_refl (plus a c)) (plus_zero b)).
Qed.

(* opp zero == zero（Id 系 GRPO 节内 grpo_opp_zero @24012 同型） *)
Lemma reqd_opp_zero : req (opp zero) zero.
Proof.
  exact (req_plus_inv_unique zero (opp zero) zero (plus_opp zero) (plus_zero zero)).
Qed.

(* a - 0 == a（req_minus 右零） *)
Lemma reqd_minus_zero_r : forall a : R, req (req_minus a zero) a.
Proof.
  intro a. unfold req_minus.
  apply (req_trans (plus a (opp zero)) (plus a zero) a).
  - exact (req_plus_compat a a (opp zero) zero (req_refl a) reqd_opp_zero).
  - apply plus_zero.
Qed.
End ReqDistCommon.

(* ============================================================ *)
(* Section ReqSumLayer：SumOver 的 setoid 对接面 + 求和层        *)
(*   三性质沿 UpSigMigrate/基内 sum_req_over_S 规格（F4）；      *)
(*   sum_le / sum_zero_nonneg 为 Id 系 SumOver 字段 L1415/L1426  *)
(*   的 req 镜像（诚实 Hypothesis 位）。                         *)
(* ============================================================ *)
Section ReqSumLayer.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

(* Σ opp f == opp Σ f（Id 原件 FEP sum_opp @15801；沿 UpSigMigrate A/B 区） *)
Lemma reqd_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      exact (req_sym (mult one (f s)) (f s) (req_mult_one_l (f s))).
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_r.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f)))
                       (opp (sumf f))).
      * apply req_opp_mult_r.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)).
        apply req_mult_one_l.
Qed.

(* Σ f - Σ g == Σ (f - g)（Id 原件 FEP sum_over_S_minus @15830） *)
Lemma reqd_sum_minus :
  forall f g : S -> R,
    req (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply sum_add.
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))).
    apply reqd_sum_opp.
Qed.

(* 零函数求和为零（线性 + 外延；req 需求生，Id 系 destruct 免费） *)
Lemma reqd_sum_zero : req (sumf (fun _ : S => zero)) zero.
Proof.
  apply (req_trans (sumf (fun _ : S => zero))
                   (sumf (fun _ : S => mult zero zero)) zero).
  - apply (sum_ext (fun _ : S => zero) (fun _ : S => mult zero zero)).
    intro s. apply (req_sym (mult zero zero) zero). apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => mult zero zero))
                     (mult zero (sumf (fun _ : S => zero))) zero).
    + apply (sum_linear zero (fun _ : S => zero)).
    + apply (req_trans (mult zero (sumf (fun _ : S => zero))) zero zero).
      * exact (req_trans (mult zero (sumf (fun _ : S => zero)))
                         (mult (sumf (fun _ : S => zero)) zero) zero
                         (mult_comm zero (sumf (fun _ : S => zero)))
                         (mult_zero (sumf (fun _ : S => zero)))).
      * apply req_refl.
Qed.

(* Σ a（常数）== G·a 的离散版本由 GRPO 节 list_sum_g 承担；此处免。 *)
End ReqSumLayer.

(* ============================================================ *)
(* Section ReqGRPO：GRPO 簇 req 迁移（Id 原件 §23793-24345，     *)
(*   14 件；group_enum/count 机器为 nat/list 层，原样复用）。    *)
(*   reqd_of_nat / reqd_list_sum_g 以 setoid 运算重建（Id 系     *)
(*   of_nat/list_sum_g 绑定 Id 接口，零改动复用会跨接口）。      *)
(* ============================================================ *)
Section ReqGRPO.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* nat 到 R 的嵌入（构造性计数；0 ⟼ zero，S n ⟼ 1 + of_nat n） *)
Fixpoint reqd_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (reqd_of_nat n')
  end.

Variable Group : Set.
Variable group_enum : list Group.
Definition group_size : nat := length group_enum.
Variable group_size_pos : lt zero (reqd_of_nat group_size).
Variable reward_group : Group -> R.

(* 组求和（列表 fold，同 Id 形） *)
Fixpoint reqd_list_sum_g (f : Group -> R) (l : list Group) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (reqd_list_sum_g f rest)
  end.

(* Id list_sum_g_linear @23828 *)
Lemma req_list_sum_g_linear : forall (a : R) (f : Group -> R) (l : list Group),
  req (reqd_list_sum_g (fun i => mult a (f i)) l)
      (mult a (reqd_list_sum_g f l)).
Proof.
  intros a f l. induction l as [| i rest IH]; simpl.
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - apply (req_trans (plus (mult a (f i)) (reqd_list_sum_g (fun i => mult a (f i)) rest))
                     (plus (mult a (f i)) (mult a (reqd_list_sum_g f rest)))
                     (mult a (plus (f i) (reqd_list_sum_g f rest)))).
    + exact (req_plus_compat (mult a (f i)) (mult a (f i))
                             (reqd_list_sum_g (fun i => mult a (f i)) rest)
                             (mult a (reqd_list_sum_g f rest))
                             (req_refl (mult a (f i))) IH).
    + apply (req_sym (mult a (plus (f i) (reqd_list_sum_g f rest)))
                     (plus (mult a (f i)) (mult a (reqd_list_sum_g f rest)))).
      apply distrib.
Qed.

(* Id list_sum_g_add @23836 *)
Lemma req_list_sum_g_add : forall f g : Group -> R, forall l : list Group,
  req (reqd_list_sum_g (fun i => plus (f i) (g i)) l)
      (plus (reqd_list_sum_g f l) (reqd_list_sum_g g l)).
Proof.
  intros f g l. induction l as [| i rest IH]; simpl.
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - apply (req_trans (plus (plus (f i) (g i))
                          (reqd_list_sum_g (fun i => plus (f i) (g i)) rest))
                     (plus (plus (f i) (g i))
                           (plus (reqd_list_sum_g f rest) (reqd_list_sum_g g rest)))
                     (plus (plus (f i) (reqd_list_sum_g f rest))
                           (plus (g i) (reqd_list_sum_g g rest)))).
    + exact (req_plus_compat (plus (f i) (g i)) (plus (f i) (g i))
                             (reqd_list_sum_g (fun i => plus (f i) (g i)) rest)
                             (plus (reqd_list_sum_g f rest) (reqd_list_sum_g g rest))
                             (req_refl (plus (f i) (g i))) IH).
    + apply req_plus_swap_mid.
Qed.

(* Id list_sum_g_ext @23844 *)
Lemma req_list_sum_g_ext : forall f g : Group -> R, forall l : list Group,
  (forall i : Group, req (f i) (g i)) ->
  req (reqd_list_sum_g f l) (reqd_list_sum_g g l).
Proof.
  intros f g l Hfg. induction l as [| i rest IH]; simpl.
  - apply req_refl.
  - apply (req_trans (plus (f i) (reqd_list_sum_g f rest))
                     (plus (f i) (reqd_list_sum_g g rest))
                     (plus (g i) (reqd_list_sum_g g rest))).
    + exact (req_plus_compat (f i) (f i) (reqd_list_sum_g f rest)
                             (reqd_list_sum_g g rest) (req_refl (f i)) IH).
    + exact (req_plus_compat (f i) (g i) (reqd_list_sum_g g rest)
                             (reqd_list_sum_g g rest) (Hfg i) (req_refl (reqd_list_sum_g g rest))).
Qed.

(* Id list_sum_g_const @23857：Σ_{i∈l} a == of_nat (length l) · a *)
Lemma req_list_sum_g_const : forall (a : R) (l : list Group),
  req (reqd_list_sum_g (fun _ => a) l) (mult (reqd_of_nat (length l)) a).
Proof.
  intros a l. induction l as [| i rest IH]; simpl.
  - exact (req_sym (mult zero a) zero
                   (req_trans (mult zero a) (mult a zero) zero
                              (mult_comm zero a) (mult_zero a))).
  - apply (req_trans (plus a (reqd_list_sum_g (fun _ => a) rest))
                     (plus a (mult (reqd_of_nat (length rest)) a))
                     (mult (plus one (reqd_of_nat (length rest))) a)).
    + exact (req_plus_compat a a (reqd_list_sum_g (fun _ => a) rest)
                             (mult (reqd_of_nat (length rest)) a)
                             (req_refl a) IH).
    + apply (req_trans (plus a (mult (reqd_of_nat (length rest)) a))
                       (plus (mult one a) (mult (reqd_of_nat (length rest)) a))
                       (mult (plus one (reqd_of_nat (length rest))) a)).
      * exact (req_plus_compat a (mult one a)
                               (mult (reqd_of_nat (length rest)) a)
                               (mult (reqd_of_nat (length rest)) a)
                               (req_sym (mult one a) a (req_mult_one_l a))
                               (req_refl (mult (reqd_of_nat (length rest)) a))).
      * apply (req_sym (mult (plus one (reqd_of_nat (length rest))) a)
                       (plus (mult one a) (mult (reqd_of_nat (length rest)) a))).
        apply req_mult_plus_distr_r.
Qed.

(* Id list_sum_g_opp @23875：Σ (-f) == -Σ f *)
Lemma req_list_sum_g_opp : forall f : Group -> R, forall l : list Group,
  req (reqd_list_sum_g (fun i => opp (f i)) l) (opp (reqd_list_sum_g f l)).
Proof.
  intros f l. induction l as [| i rest IH]; simpl.
  - exact (req_sym (opp zero) zero reqd_opp_zero).
  - apply (req_trans (plus (opp (f i)) (reqd_list_sum_g (fun i => opp (f i)) rest))
                     (plus (opp (f i)) (opp (reqd_list_sum_g f rest)))
                     (opp (plus (f i) (reqd_list_sum_g f rest)))).
    + exact (req_plus_compat (opp (f i)) (opp (f i))
                             (reqd_list_sum_g (fun i => opp (f i)) rest)
                             (opp (reqd_list_sum_g f rest))
                             (req_refl (opp (f i))) IH).
    + apply (req_sym (opp (plus (f i) (reqd_list_sum_g f rest)))
                     (plus (opp (f i)) (opp (reqd_list_sum_g f rest)))).
      apply req_opp_plus.
Qed.

(* Id list_sum_g_minus @23890：Σ (f - g) == Σf - Σg *)
Lemma req_list_sum_g_minus : forall f g : Group -> R, forall l : list Group,
  req (reqd_list_sum_g (fun i => req_minus (f i) (g i)) l)
      (req_minus (reqd_list_sum_g f l) (reqd_list_sum_g g l)).
Proof.
  intros f g l. unfold req_minus.
  apply (req_trans (reqd_list_sum_g (fun i => plus (f i) (opp (g i))) l)
                   (plus (reqd_list_sum_g f l)
                         (reqd_list_sum_g (fun i => opp (g i)) l))
                   (plus (reqd_list_sum_g f l) (opp (reqd_list_sum_g g l)))).
  - apply req_list_sum_g_add.
  - exact (req_plus_compat (reqd_list_sum_g f l) (reqd_list_sum_g f l)
                           (reqd_list_sum_g (fun i => opp (g i)) l)
                           (opp (reqd_list_sum_g g l))
                           (req_refl (reqd_list_sum_g f l))
                           (req_list_sum_g_opp g l)).
Qed.

(* 组均值：μ = (1/G)·Σ r_i（Id group_mean @23903 同形） *)
Definition req_group_mean : R :=
  mult (inv_pos (reqd_of_nat group_size) group_size_pos)
       (reqd_list_sum_g reward_group group_enum).

(* 组相对优势：A_i = r_i − μ（Id grpo_advantage @23907 同形） *)
Definition req_grpo_advantage (i : Group) : R :=
  req_minus (reward_group i) req_group_mean.

(* μ 的定义恒等：G·μ == Σr（zero_mean 与 variance_identity 共用） *)
Lemma req_group_mean_def :
  req (mult (reqd_of_nat group_size) req_group_mean)
      (reqd_list_sum_g reward_group group_enum).
Proof.
  unfold req_group_mean.
  apply (req_trans (mult (reqd_of_nat group_size)
                         (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                               (reqd_list_sum_g reward_group group_enum)))
                   (mult (mult (reqd_of_nat group_size)
                               (inv_pos (reqd_of_nat group_size) group_size_pos))
                         (reqd_list_sum_g reward_group group_enum))
                   (reqd_list_sum_g reward_group group_enum)).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (reqd_of_nat group_size)
                                (inv_pos (reqd_of_nat group_size) group_size_pos))
                           (reqd_list_sum_g reward_group group_enum))
                     (mult one (reqd_list_sum_g reward_group group_enum))
                     (reqd_list_sum_g reward_group group_enum)).
    + exact (req_mult_compat (mult (reqd_of_nat group_size)
                                   (inv_pos (reqd_of_nat group_size) group_size_pos))
                             one
                             (reqd_list_sum_g reward_group group_enum)
                             (reqd_list_sum_g reward_group group_enum)
                             (inv_pos_correct (reqd_of_nat group_size) group_size_pos)
                             (req_refl (reqd_list_sum_g reward_group group_enum))).
    + apply (req_trans (mult one (reqd_list_sum_g reward_group group_enum))
                       (mult (reqd_list_sum_g reward_group group_enum) one)
                       (reqd_list_sum_g reward_group group_enum)).
      * apply mult_comm.
      * apply mult_one.
Qed.

(* Id grpo_advantage_zero_mean @23912：Σ A_i·c == 0（任意 c） *)
Theorem req_grpo_advantage_zero_mean :
  forall c : R,
    req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum) zero.
Proof.
  intros c.
  assert (Hext : req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum)
                     (reqd_list_sum_g (fun i => mult c (req_grpo_advantage i)) group_enum)).
  { apply req_list_sum_g_ext. intro i. apply mult_comm. }
  assert (Hlin : req (reqd_list_sum_g (fun i => mult c (req_grpo_advantage i)) group_enum)
                     (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))).
  { exact (req_list_sum_g_linear c (fun i => req_minus (reward_group i) req_group_mean) group_enum). }
  assert (Hcancel : req (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum) zero).
  { assert (Hmin : req (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g (fun _ => req_group_mean) group_enum)))
      by exact (req_list_sum_g_minus reward_group (fun _ => req_group_mean) group_enum).
    assert (Hconst : req (reqd_list_sum_g (fun _ => req_group_mean) group_enum)
                         (mult (reqd_of_nat group_size) req_group_mean))
      by exact (req_list_sum_g_const req_group_mean group_enum).
    assert (Hcc := req_group_mean_def).
    apply (req_trans (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                     (req_minus (reqd_list_sum_g reward_group group_enum)
                                (mult (reqd_of_nat group_size) req_group_mean))
                     zero).
    - apply (req_trans (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g (fun _ => req_group_mean) group_enum))
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (mult (reqd_of_nat group_size) req_group_mean))).
      + exact Hmin.
      + exact (reqd_minus_compat (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g (fun _ => req_group_mean) group_enum)
                                 (mult (reqd_of_nat group_size) req_group_mean)
                                 (req_refl (reqd_list_sum_g reward_group group_enum)) Hconst).
    - apply (req_trans (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (mult (reqd_of_nat group_size) req_group_mean))
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g reward_group group_enum))
                       zero).
      + exact (reqd_minus_compat (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (mult (reqd_of_nat group_size) req_group_mean)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (req_refl (reqd_list_sum_g reward_group group_enum)) Hcc).
      + apply req_minus_self_zero. apply req_refl. }
  apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum)
                   (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))
                   zero).
  - exact (req_trans _ _ _ Hext Hlin).
  - apply (req_trans (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))
                     (mult c zero) zero).
    + exact (req_mult_compat c c
                             (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                             zero (req_refl c) Hcancel).
    + apply mult_zero.
Qed.

(* 组二阶矩 / 中心化二阶矩（Id @24065/24069 同形） *)
Definition req_group_raw_second_moment : R :=
  reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum.
Definition req_group_centered_second_moment : R :=
  reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum.

(* Id grpo_square_expand @24073：(r−μ)² == r² − 2rμ + μ²（非平凡代数链） *)
Lemma req_grpo_square_expand : forall i : Group,
  req (mult (req_grpo_advantage i) (req_grpo_advantage i))
      (plus (mult (reward_group i) (reward_group i))
            (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                  (mult req_group_mean req_group_mean))).
Proof.
  intro i. unfold req_grpo_advantage, req_minus.
  set (r := reward_group i). set (m := req_group_mean).
  (* H1：平方展开（mult_plus_distr_r） *)
  (* 左半：r·(r+(−μ)) == r² + opp(r·μ) *)
  assert (H2 : req (mult r (plus r (opp m)))
                   (plus (mult r r) (opp (mult r m)))).
  { apply (req_trans (mult r (plus r (opp m)))
                     (plus (mult r r) (mult r (opp m)))
                     (plus (mult r r) (opp (mult r m)))).
    - apply distrib.
    - exact (req_plus_compat (mult r r) (mult r r) (mult r (opp m)) (opp (mult r m))
                             (req_refl (mult r r)) (req_opp_mult_l r m)). }
  (* 右半：(−μ)·(r+(−μ)) == opp(μ·r) + μ·μ *)
  assert (H6 : req (mult (opp m) (opp m)) (mult m m)).
  { apply (req_trans (mult (opp m) (opp m)) (opp (mult m (opp m)))
                     (mult m m)).
    - apply req_opp_mult_r.
    - apply (req_trans (opp (mult m (opp m))) (opp (opp (mult m m))) (mult m m)).
      + exact (req_opp_compat (mult m (opp m)) (opp (mult m m)) (req_opp_mult_l m m)).
      + apply req_double_neg. }
  assert (H4 : req (mult (opp m) (plus r (opp m)))
                   (plus (opp (mult m r)) (mult m m))).
  { apply (req_trans (mult (opp m) (plus r (opp m)))
                     (plus (mult (opp m) r) (mult (opp m) (opp m)))
                     (plus (opp (mult m r)) (mult m m))).
    - apply distrib.
    - exact (req_plus_compat (mult (opp m) r) (opp (mult m r))
                             (mult (opp m) (opp m)) (mult m m)
                             (req_opp_mult_r m r) H6). }
  (* H7：交叉项合并 r² + opp(rμ) + opp(μr) + μ² → r² + opp(2rμ) + μ² *)
  assert (Hm2 : req (plus (opp (mult m r)) (opp (mult r m)))
                    (opp (mult (mult (plus one one) r) m))).
  { assert (H2b : req (plus (mult m r) (mult r m)) (mult (mult (plus one one) r) m)).
    { apply (req_trans (plus (mult m r) (mult r m))
                       (plus (mult r m) (mult r m))
                       (mult (mult (plus one one) r) m)).
      - exact (req_plus_compat (mult m r) (mult r m) (mult r m) (mult r m)
                               (mult_comm m r) (req_refl (mult r m))).
      - apply (req_trans (plus (mult r m) (mult r m)) (mult (plus r r) m)
                         (mult (mult (plus one one) r) m)).
        + apply (req_sym (mult (plus r r) m) (plus (mult r m) (mult r m))).
          apply (req_mult_plus_distr_r r r m).
        + apply (req_sym (mult (mult (plus one one) r) m) (mult (plus r r) m)).
          exact (req_mult_compat (mult (plus one one) r) (plus r r) m m
                                 (req_two_mult r) (req_refl m)). }
    apply (req_trans (plus (opp (mult m r)) (opp (mult r m)))
                     (opp (plus (mult m r) (mult r m)))
                     (opp (mult (mult (plus one one) r) m))).
    - apply (req_sym (opp (plus (mult m r) (mult r m)))
                     (plus (opp (mult m r)) (opp (mult r m)))).
      apply (req_opp_plus (mult m r) (mult r m)).
    - exact (req_opp_compat (plus (mult m r) (mult r m))
                            (mult (mult (plus one one) r) m) H2b). }
  assert (H7 : req (plus (plus (mult r r) (opp (mult r m)))
                         (plus (opp (mult m r)) (mult m m)))
                   (plus (mult r r)
                         (plus (opp (mult (mult (plus one one) r) m))
                               (mult m m)))).
  { apply (req_trans (plus (plus (mult r r) (opp (mult r m)))
                           (plus (opp (mult m r)) (mult m m)))
                     (plus (mult r r)
                           (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))
                     (plus (mult r r)
                           (plus (opp (mult (mult (plus one one) r) m))
                                 (mult m m)))).
    - apply (req_trans (plus (plus (mult r r) (opp (mult r m)))
                             (plus (opp (mult m r)) (mult m m)))
                       (plus (plus (mult r r) (opp (mult m r)))
                             (plus (opp (mult r m)) (mult m m)))
                       (plus (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))).
      + apply req_plus_swap_mid.
      + apply (req_sym (plus (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))
                       (plus (plus (mult r r) (opp (mult m r)))
                             (plus (opp (mult r m)) (mult m m)))).
        apply (plus_assoc (mult r r) (opp (mult m r)) (plus (opp (mult r m)) (mult m m))).
    - exact (req_plus_compat (mult r r) (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m)))
                             (plus (opp (mult (mult (plus one one) r) m)) (mult m m))
                             (req_refl (mult r r))
                             (req_trans (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m)))
                                        (plus (plus (opp (mult m r)) (opp (mult r m))) (mult m m))
                                        (plus (opp (mult (mult (plus one one) r) m)) (mult m m))
                                        (plus_assoc (opp (mult m r)) (opp (mult r m)) (mult m m))
                                        (req_plus_compat (plus (opp (mult m r)) (opp (mult r m)))
                                                         (opp (mult (mult (plus one one) r) m))
                                                         (mult m m) (mult m m)
                                                         Hm2 (req_refl (mult m m))))).
  }
  (* 总装：(r+(−μ))·(r+(−μ)) == (r·(r+(−μ))) + ((−μ)·(r+(−μ))) → H2+H4 → H7 *)
  apply (req_trans (mult (plus r (opp m)) (plus r (opp m)))
                   (plus (mult r (plus r (opp m))) (mult (opp m) (plus r (opp m))))
                   (plus (mult r r)
                         (plus (opp (mult (mult (plus one one) r) m))
                               (mult m m)))).
  - apply req_mult_plus_distr_r.
  - apply (req_trans (plus (mult r (plus r (opp m))) (mult (opp m) (plus r (opp m))))
                     (plus (plus (mult r r) (opp (mult r m)))
                           (plus (opp (mult m r)) (mult m m)))
                     (plus (mult r r)
                           (plus (opp (mult (mult (plus one one) r) m))
                                 (mult m m)))).
    + exact (req_plus_compat _ _ _ _ H2 H4).
    + exact H7.
Qed.

(* Id grpo_variance_identity @24093：Σ(r−μ)² == Σr² − G·μ² *)
Theorem req_grpo_variance_identity :
  req req_group_centered_second_moment
      (req_minus req_group_raw_second_moment
                 (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))).
Proof.
  unfold req_group_centered_second_moment, req_group_raw_second_moment.
  (* 逐点展开 *)
  assert (Hext : req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (reqd_list_sum_g (fun i =>
                        plus (mult (reward_group i) (reward_group i))
                             (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                   (mult req_group_mean req_group_mean))) group_enum))
    by (apply req_list_sum_g_ext; intro i; exact (req_grpo_square_expand i)).
  (* 求和线性化两次 *)
  assert (Hadd1 : req (reqd_list_sum_g (fun i =>
                   plus (mult (reward_group i) (reward_group i))
                        (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                              (mult req_group_mean req_group_mean))) group_enum)
                  (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                        (reqd_list_sum_g (fun i =>
                          plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                               (mult req_group_mean req_group_mean)) group_enum)))
    by (apply req_list_sum_g_add).
  assert (Hadd2 : req (reqd_list_sum_g (fun i =>
                   plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                        (mult req_group_mean req_group_mean)) group_enum)
                  (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                        (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
    by (apply req_list_sum_g_add).
  (* Σ opp(2 r μ) == opp(2 Σr μ) *)
  assert (Hopp : req (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                     (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))).
  { assert (Hlin : req (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                       (mult req_group_mean (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum))).
    { apply (req_trans (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                       (reqd_list_sum_g (fun i => mult req_group_mean (mult (plus one one) (reward_group i))) group_enum)
                       (mult req_group_mean (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum))).
      - apply req_list_sum_g_ext. intro i. apply mult_comm.
      - apply req_list_sum_g_linear. }
    assert (Hlin2 : req (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum)
                        (mult (plus one one) (reqd_list_sum_g reward_group group_enum)))
      by exact (req_list_sum_g_linear (plus one one) reward_group group_enum).
    assert (HA : req (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                     (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean)).
    { assert (Hsw : req (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                        (reqd_list_sum_g (fun i => mult req_group_mean (mult (plus one one) (reward_group i))) group_enum))
        by (apply req_list_sum_g_ext; intro i; apply mult_comm).
      assert (Hmid : req (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                         (mult req_group_mean (mult (plus one one) (reqd_list_sum_g reward_group group_enum))))
        by exact (req_trans _ _ _ Hsw
                             (req_trans _ _ _
                              (req_list_sum_g_linear req_group_mean
                                                     (fun i => mult (plus one one) (reward_group i))
                                                     group_enum)
                              (req_mult_compat req_group_mean req_group_mean
                                               (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum)
                                               (mult (plus one one) (reqd_list_sum_g reward_group group_enum))
                                               (req_refl req_group_mean) Hlin2))).
      exact (req_trans _ _ _ Hmid
                           (mult_comm req_group_mean
                                      (mult (plus one one) (reqd_list_sum_g reward_group group_enum)))). }
    apply (req_trans (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                     (opp (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum))
                     (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))).
    - apply req_list_sum_g_opp.
    - exact (req_opp_compat _ _ HA). }
  (* Σ μ² == G·μ²；Σr == G·μ *)
  assert (Hconst : req (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                       (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
    by exact (req_list_sum_g_const (mult req_group_mean req_group_mean) group_enum).
  assert (Hmu : req (reqd_list_sum_g reward_group group_enum)
                    (mult (reqd_of_nat group_size) req_group_mean))
    by exact (req_sym (mult (reqd_of_nat group_size) req_group_mean)
                      (reqd_list_sum_g reward_group group_enum) req_group_mean_def).
  assert (Hcross : req (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                       (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean)))
    by (apply (req_opp_compat _ _ (req_mult_compat (mult (plus one one) (reqd_list_sum_g reward_group group_enum))
                                                   (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean))
                                                   req_group_mean req_group_mean
                                                   (req_mult_compat (plus one one) (plus one one)
                                                                    (reqd_list_sum_g reward_group group_enum)
                                                                    (mult (reqd_of_nat group_size) req_group_mean)
                                                                    (req_refl (plus one one)) Hmu)
                                                   (req_refl req_group_mean)))).
  (* 2x − x == −x（x := G·μ²） *)
  assert (Hcancel2 : req (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                               (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                         (opp (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))).
  { assert (H2a : req (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean)
                      (mult (plus one one) (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))).
    { apply (req_trans (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean)
                       (mult (plus one one) (mult (mult (reqd_of_nat group_size) req_group_mean) req_group_mean))
                       (mult (plus one one) (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))).
      - apply (req_sym (mult (plus one one) (mult (mult (reqd_of_nat group_size) req_group_mean) req_group_mean))
                       (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean)).
        apply mult_assoc.
      - exact (req_mult_compat (plus one one) (plus one one)
                               (mult (mult (reqd_of_nat group_size) req_group_mean) req_group_mean)
                               (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))
                               (req_refl (plus one one))
                               (req_sym (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))
                                        (mult (mult (reqd_of_nat group_size) req_group_mean) req_group_mean)
                                        (mult_assoc (reqd_of_nat group_size) req_group_mean req_group_mean))). }
    set (x := mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)).
    assert (H2c : req (plus (opp (mult (plus one one) x)) x) (opp x)).
    { apply (req_trans (plus (opp (mult (plus one one) x)) x)
                       (plus (opp (plus x x)) x) (opp x)).
      - exact (req_plus_compat (opp (mult (plus one one) x)) (opp (plus x x)) x x
                               (req_opp_compat (mult (plus one one) x) (plus x x) (req_two_mult x))
                               (req_refl x)).
      - apply (req_trans (plus (opp (plus x x)) x) (plus (plus (opp x) (opp x)) x) (opp x)).
        + exact (req_plus_compat (opp (plus x x)) (plus (opp x) (opp x)) x x
                                 (req_opp_plus x x)
                                 (req_refl x)).
        + apply (req_trans (plus (plus (opp x) (opp x)) x) (plus (opp x) (plus (opp x) x)) (opp x)).
          * apply (req_sym (plus (opp x) (plus (opp x) x)) (plus (plus (opp x) (opp x)) x)).
            apply plus_assoc.
          * apply (req_trans (plus (opp x) (plus (opp x) x)) (plus (opp x) zero) (opp x)).
            -- exact (req_plus_compat (opp x) (opp x) (plus (opp x) x) zero (req_refl (opp x))
                                      (req_trans (plus (opp x) x) (plus x (opp x)) zero
                                                 (plus_comm (opp x) x) (plus_opp x))).
            -- apply (req_trans (plus (opp x) zero) (opp x) (opp x)
                                (plus_zero (opp x)) (req_refl (opp x))). }
    exact (req_trans (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                           (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                     (plus (opp (mult (plus one one) x)) x) (opp x)
                     (req_plus_compat (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                      (opp (mult (plus one one) x))
                                      (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)) x
                                      (req_opp_compat _ _ H2a) (req_refl x))
                     H2c). }
  (* 总装：CSM →(Hext/Hadd1/Hadd2/Hopp/Hcross/Hconst)→ Σr² + (opp(2·Gμ·μ) + Gμ²) →(Hcancel2)→ Σr² − Gμ² *)
  assert (Hl1 : req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (reqd_list_sum_g (fun i =>
                              plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                   (mult req_group_mean req_group_mean)) group_enum))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
    - exact (req_trans _ _ _ Hext Hadd1).
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i =>
                               plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                    (mult req_group_mean req_group_mean)) group_enum)
                            (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                            (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                            Hadd2).
  }
  assert (Hl2 : req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
    - exact Hl1.
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                             (req_plus_compat (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                              (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                              (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                              (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                              Hopp
                                              (req_refl (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  }
  assert (Hl3 : req (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                 (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))).
    - exact Hl1.
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                   (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                             (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                             (req_trans (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                                            (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                                            (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                                  (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                                   (req_plus_compat (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                                    (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    Hopp
                                                    (req_refl (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                                   (req_plus_compat (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                    (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))
                                                    Hcross
                                                    Hconst))).
  }
  unfold req_minus.
  exact (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                   (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                         (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                               (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))
                   (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                         (opp (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))
           Hl3
           (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat group_size) req_group_mean)) req_group_mean))
                                  (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                            (opp (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                            (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                            Hcancel2)).
Qed.

(* 组方差（Id group_variance @24242 同形） *)
Definition req_group_variance : R :=
  mult (inv_pos (reqd_of_nat group_size) group_size_pos)
       req_group_centered_second_moment.

(* Id inv_G_absorb @24247：inv(G)·(G·x) == x *)
Lemma req_inv_G_absorb : forall (G : R) (Hg : lt zero G) (x : R),
  req (mult (inv_pos G Hg) (mult G x)) x.
Proof.
  intros G Hg x.
  apply (req_trans (mult (inv_pos G Hg) (mult G x))
                   (mult (mult (inv_pos G Hg) G) x) x).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (inv_pos G Hg) G) x) (mult one x) x).
    + exact (req_mult_compat (mult (inv_pos G Hg) G) one x x
                             (req_trans (mult (inv_pos G Hg) G) (mult G (inv_pos G Hg)) one
                                        (mult_comm (inv_pos G Hg) G) (inv_pos_correct G Hg))
                             (req_refl x)).
    + apply (req_trans (mult one x) (mult x one) x (mult_comm one x) (mult_one x)).
Qed.

(* Id group_variance_identity @24261：Var == (1/G)·Σr² − μ² *)
Theorem req_group_variance_identity :
  req req_group_variance
      (req_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                       req_group_raw_second_moment)
                 (mult req_group_mean req_group_mean)).
Proof.
  unfold req_group_variance.
  apply (req_trans (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                         req_group_centered_second_moment)
                   (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                         (req_minus req_group_raw_second_moment
                                    (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))
                   (req_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                    req_group_raw_second_moment)
                              (mult req_group_mean req_group_mean))).
  - exact (req_mult_compat (inv_pos (reqd_of_nat group_size) group_size_pos)
                           (inv_pos (reqd_of_nat group_size) group_size_pos)
                           req_group_centered_second_moment
                           (req_minus req_group_raw_second_moment
                                      (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                           (req_refl (inv_pos (reqd_of_nat group_size) group_size_pos))
                           req_grpo_variance_identity).
  - apply (req_trans (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                           (req_minus req_group_raw_second_moment
                                      (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))
                     (req_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                      req_group_raw_second_moment)
                                (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                      (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean))))
                     (req_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                      req_group_raw_second_moment)
                                (mult req_group_mean req_group_mean))).
    + apply req_mult_minus_distr_l.
    + exact (reqd_minus_compat (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                     req_group_raw_second_moment)
                               (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                     req_group_raw_second_moment)
                               (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                     (mult (reqd_of_nat group_size) (mult req_group_mean req_group_mean)))
                               (mult req_group_mean req_group_mean)
                               (req_refl (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                               req_group_raw_second_moment))
                               (req_inv_G_absorb (reqd_of_nat group_size) group_size_pos
                                                 (mult req_group_mean req_group_mean))).
Qed.

(* Id grpo_le_minus @24310：0 ≤ b ⟹ a − b ≤ a *)
Lemma req_grpo_le_minus : forall a b : R, le zero b -> le (req_minus a b) a.
Proof.
  intros a b Hb. unfold req_minus.
  apply (le_id_r (plus a (opp b)) (plus a zero) a).
  - apply plus_zero.
  - apply (le_plus_compat a a (opp b) zero).
    + apply le_refl.
    + apply (le_id_r (opp b) (opp zero) zero).
      * exact reqd_opp_zero.
      * apply (opp_le_compat zero b). exact Hb.
Qed.

(* Id group_variance_le_raw_second_moment @24324（T1.5）：
   Var ≤ (1/G)·Σr²。square_nonneg 保持 Id 出口假设位（T2 形态①，
   Id 系 L24301 同为诚实 Variable；构造性有序域无三分律）。 *)
Theorem req_group_variance_le_raw_second_moment :
  (forall a : R, le zero (mult a a)) ->
  le req_group_variance
     (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
           req_group_raw_second_moment).
Proof.
  intros square_nonneg.
  apply (le_id_l req_group_variance
                 (req_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                  req_group_raw_second_moment)
                            (mult req_group_mean req_group_mean))
                 (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                       req_group_raw_second_moment)).
  - exact req_group_variance_identity.
  - apply (req_grpo_le_minus (mult (inv_pos (reqd_of_nat group_size) group_size_pos)
                                   req_group_raw_second_moment)
                             (mult req_group_mean req_group_mean)).
    apply square_nonneg.
Qed.

End ReqGRPO.

(* ============================================================ *)
(* Section ReqFEP：FreeEnergyMinimization 节 req 迁移            *)
(*   （Id 原件 §15759-18721）。对接口 = sum_req_over_S 三性质    *)
(*   + SumOver 字段 sum_le/sum_zero_nonneg 的 req 镜像；         *)
(*   T2① 桥 4 件见节内 Hypothesis（均为 Id 接口字段/已证件，     *)
(*   Real 实例可满足，实例化留待接口扩展批——批 1 同判词）。      *)
(* ============================================================ *)
Section ReqFEP.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis fsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis fsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis fsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis fsum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis fsum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis fsum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- T2① 接口缺口桥（台账 3） ---- *)
Hypothesis dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- 节内定义（setoid 惯例形态；log 前提化见台账 1） ---- *)
Definition positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition normalized (p : S -> R) : Set := req (sumf p) one.
Definition boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Definition free_energy (p : S -> R) (Hp : positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition req_relative_entropy (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
Definition entropy_dist (p : S -> R) (Hp : positive_dist p) : R :=
  sumf (fun s => mult (p s) (opp (log (p s) (Hp s)))).
Definition energy_expectation (p : S -> R) : R :=
  sumf (fun s => mult (p s) (base_loss s)).
Definition cross_entropy (p q : S -> R) (Hq : positive_dist q) : R :=
  sumf (fun s => mult (p s) (opp (log (q s) (Hq s)))).
Definition reqd_elbo (q : S -> R) (Hq : positive_dist q) : R := opp (free_energy q Hq).

Lemma req_boltzmann_positive : forall s : S, lt zero (boltzmann_dist s).
Proof.
  intro s. unfold boltzmann_dist.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.

Definition reqd_evidence : R := opp (free_energy boltzmann_dist req_boltzmann_positive).

(* 节内求和辅助：Σ opp f == opp Σ f（Id sum_opp @15801） *)
Lemma fsum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (fsum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      exact (req_sym (mult one (f s)) (f s) (req_mult_one_l (f s))).
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_r.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + apply (fsum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_r.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)).
        apply req_mult_one_l.
Qed.

(* 节内求和辅助：Σ (f - g) == Σf - Σg（Id sum_over_S_minus @15830） *)
Lemma fsum_minus :
  forall f g : S -> R,
    req (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply fsum_add.
  - exact (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f)) (fsum_opp g)).
Qed.

(* Id boltzmann_normalized @15846（= UpSigMigrate req_boltzmann_normalized 同构） *)
Theorem req_boltzmann_normalized : normalized boltzmann_dist.
Proof.
  apply (req_trans (sumf boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (fsum_linear (inv_pos Z Z_pos)
                       (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z) one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * exact (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                        partition_condition).
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* Id boltzmann_mix_normalized @15863：凸组合 alpha·p + (1-alpha)·q 归一化 *)
Theorem req_boltzmann_mix_normalized :
  forall (p q : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    normalized p -> normalized q ->
    req (sumf (fun s => plus (mult alpha (p s)) (mult (req_minus one alpha) (q s)))) one.
Proof.
  intros p q alpha Halpha Halpha1 Hp Hq.
  apply (req_trans (sumf (fun s => plus (mult alpha (p s)) (mult (req_minus one alpha) (q s))))
                   (plus (sumf (fun s => mult alpha (p s)))
                         (sumf (fun s => mult (req_minus one alpha) (q s))))
                   one).
  - apply fsum_add.
  - apply (req_trans (plus (sumf (fun s => mult alpha (p s)))
                           (sumf (fun s => mult (req_minus one alpha) (q s))))
                     (plus (mult alpha (sumf p)) (mult (req_minus one alpha) (sumf q)))
                     one).
    + exact (req_plus_compat _ _ _ _ (fsum_linear alpha p)
                                     (fsum_linear (req_minus one alpha) q)).
    + apply (req_trans (plus (mult alpha (sumf p)) (mult (req_minus one alpha) (sumf q)))
                       (plus (mult alpha one) (mult (req_minus one alpha) one))
                       one).
      * exact (req_plus_compat _ _ _ _
                               (req_mult_compat alpha alpha (sumf p) one
                                                (req_refl alpha) Hp)
                               (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                                                (sumf q) one (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans (plus (mult alpha one) (mult (req_minus one alpha) one))
                         (plus alpha (req_minus one alpha)) one).
        -- exact (req_plus_compat (mult alpha one) alpha
                                  (mult (req_minus one alpha) one) (req_minus one alpha)
                                  (mult_one alpha)
                                  (mult_one (req_minus one alpha))).
        -- apply (req_trans (plus alpha (req_minus one alpha)) (plus one (plus alpha (opp alpha))) one).
           apply (req_trans (plus alpha (plus one (opp alpha)))
                            (plus (plus alpha one) (opp alpha))
                            (plus one (plus alpha (opp alpha)))).
           ++ apply plus_assoc.
           ++ apply (req_trans (plus (plus alpha one) (opp alpha))
                               (plus (plus one alpha) (opp alpha))
                               (plus one (plus alpha (opp alpha)))).
              ** exact (req_plus_compat (plus alpha one) (plus one alpha) (opp alpha) (opp alpha)
                                        (plus_comm alpha one) (req_refl (opp alpha))).
              ** apply (req_sym (plus one (plus alpha (opp alpha)))
                                (plus (plus one alpha) (opp alpha))).
                 apply plus_assoc.
           ++ apply (req_trans (plus one (plus alpha (opp alpha))) (plus one zero) one).
              ** exact (req_plus_compat one one (plus alpha (opp alpha)) zero
                                        (req_refl one) (plus_opp alpha)).
              ** apply (req_trans (plus one zero) one one
                                  (plus_zero one) (req_refl one)).
Qed.

(* Id boltzmann_log_decomp @15912：log p_b == -log Z - E/D *)
Theorem req_boltzmann_log_decomp :
  forall s : S,
    req (log (boltzmann_dist s) (req_boltzmann_positive s))
        (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s. unfold boltzmann_dist, req_boltzmann_positive.
  assert (Hlm : req (log (mult (inv_pos Z Z_pos)
                              (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                        (mult_positive (inv_pos Z Z_pos)
                                       (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                                       (inv_pos_pos Z Z_pos)
                                       (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                    (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                          (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))).
  { apply log_mult. }
  apply (req_trans _ _ _ Hlm (req_plus_compat (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                                              (opp (log Z Z_pos))
                                              (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                                                   (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                                              (opp (mult (inv_pos D D_pos) (base_loss s)))
                                              (dist_log_inv_one_inv Z Z_pos (inv_pos_pos Z Z_pos))
                                              (dist_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
Qed.

(* req 化 log_div（log(a/b) == log a - log b；由 log_mult + 桥组装） *)
Lemma reqd_log_div :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    req (log (mult a (inv_pos b Hb))
              (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
        (plus (log a Ha) (opp (log b Hb))).
Proof.
  intros a b Ha Hb.
  apply (req_trans (log (mult a (inv_pos b Hb))
                        (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
                   (plus (log a Ha) (log (inv_pos b Hb) (inv_pos_pos b Hb)))
                   (plus (log a Ha) (opp (log b Hb)))).
  - apply log_mult.
  - exact (req_plus_compat (log a Ha) (log a Ha)
                           (log (inv_pos b Hb) (inv_pos_pos b Hb)) (opp (log b Hb))
                           (req_refl (log a Ha))
                           (dist_log_inv_one_inv b Hb (inv_pos_pos b Hb))).
Qed.

(* Id energy_in_log_boltzmann @16116：E == -D·(log p_b + log Z) *)
Lemma req_energy_in_log_boltzmann :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  assert (H2 : req (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                   (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - exact (req_plus_compat (log (boltzmann_dist s) (req_boltzmann_positive s))
                             (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos) (log Z Z_pos)
                             (req_boltzmann_log_decomp s) (req_refl (log Z Z_pos))).
    - apply (req_trans (plus (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos))
                       (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                             (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply reqd_plus_rot.
      + apply (req_trans (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                               (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * exact (req_plus_compat (plus (opp (log Z Z_pos)) (log Z Z_pos)) zero
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                            zero
                                            (plus_comm (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus_opp (log Z Z_pos)))
                                 (req_refl (opp (mult (inv_pos D D_pos) (base_loss s))))).
        * apply req_plus_zero_l. }
  assert (H3 : req (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                                 (log Z Z_pos)))
                   (opp (base_loss s))).
  { apply (req_trans (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                                   (log Z Z_pos)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    - exact (req_mult_compat D D
                             (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                                   (log Z Z_pos))
                             (opp (mult (inv_pos D D_pos) (base_loss s)))
                             (req_refl D) H2).
    - apply (req_trans (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (base_loss s))).
      + apply req_opp_mult_l.
      + apply (req_opp_compat (mult D (mult (inv_pos D D_pos) (base_loss s))) (base_loss s)).
        exact (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                         (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (base_loss s)
                         (mult_assoc D (inv_pos D D_pos) (base_loss s))
                         (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                                    (mult one (base_loss s))
                                    (base_loss s)
                                    (req_mult_compat (mult D (inv_pos D D_pos)) one
                                                     (base_loss s) (base_loss s)
                                                     (inv_pos_correct D D_pos)
                                                     (req_refl (base_loss s)))
                                    (req_trans (mult one (base_loss s))
                                               (mult (base_loss s) one)
                                               (base_loss s)
                                               (mult_comm one (base_loss s))
                                               (mult_one (base_loss s))))).
  }
  apply (req_trans (base_loss s) (opp (opp (base_loss s)))
                   (opp (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                                      (log Z Z_pos))))).
  - apply (req_sym (opp (opp (base_loss s))) (base_loss s)). apply req_double_neg.
  - exact (req_opp_compat (opp (base_loss s))
                          (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s))
                                        (log Z Z_pos)))
                          (req_sym _ _ H3)).
Qed.

(* Σ p_b·log Z == log Z（归一化折叠；Σ p_b·X == X·Σ p_b == X） *)
Lemma fsum_pb_logZ :
  req (sumf (fun s => mult (boltzmann_dist s) (log Z Z_pos))) (log Z Z_pos).
Proof.
  apply (req_trans (sumf (fun s => mult (boltzmann_dist s) (log Z Z_pos)))
                   (sumf (fun s => mult (log Z Z_pos) (boltzmann_dist s)))
                   (log Z Z_pos)).
  - apply (fsum_ext (fun s => mult (boltzmann_dist s) (log Z Z_pos))
                    (fun s => mult (log Z Z_pos) (boltzmann_dist s))).
    intro s. apply mult_comm.
  - apply (req_trans (sumf (fun s => mult (log Z Z_pos) (boltzmann_dist s)))
                     (mult (log Z Z_pos) (sumf boltzmann_dist)) (log Z Z_pos)).
    + exact (fsum_linear (log Z Z_pos) boltzmann_dist).
    + apply (req_trans (mult (log Z Z_pos) (sumf boltzmann_dist))
                       (mult (log Z Z_pos) one) (log Z Z_pos)).
      * exact (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf boltzmann_dist) one
                             (req_refl (log Z Z_pos)) req_boltzmann_normalized).
      * apply (req_trans (mult (log Z Z_pos) one) (mult one (log Z Z_pos)) (log Z Z_pos)
                       (mult_comm (log Z Z_pos) one) (req_mult_one_l (log Z Z_pos))).
Qed.

(* 节内求和辅助：零函数求和为零（ext + linear；ReqSumLayer reqd_sum_zero
   的节内复刻——跨节消费需显式传 8 参，节内直造更省） *)
Lemma fsum_zero : req (sumf (fun _ : S => zero)) zero.
Proof.
  apply (req_trans (sumf (fun _ : S => zero))
                   (sumf (fun _ : S => mult zero zero)) zero).
  - apply (fsum_ext (fun _ : S => zero) (fun _ : S => mult zero zero)).
    intro s. apply (req_sym (mult zero zero) zero). apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => mult zero zero))
                     (mult zero (sumf (fun _ : S => zero))) zero).
    + apply (fsum_linear zero (fun _ : S => zero)).
    + exact (req_trans (mult zero (sumf (fun _ : S => zero)))
                       (mult (sumf (fun _ : S => zero)) zero) zero
                       (mult_comm zero (sumf (fun _ : S => zero)))
                       (mult_zero (sumf (fun _ : S => zero)))).
Qed.

(* 归一化折叠一般形：Σ p·c == c（Hnp : normalized p；fsum_pb_logZ 的
   任意常数泛化，kl_decomp 中 Σ p·log Z 用） *)
Lemma fsum_norm_const :
  forall (p : S -> R) (c : R), normalized p ->
    req (sumf (fun s => mult (p s) c)) c.
Proof.
  intros p c Hnp.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (sumf (fun s => mult c (p s))) c).
  - apply (fsum_ext (fun s => mult (p s) c) (fun s => mult c (p s))).
    intro s. apply mult_comm.
  - apply (req_trans (sumf (fun s => mult c (p s)))
                     (mult c (sumf p)) c).
    + exact (fsum_linear c p).
    + apply (req_trans (mult c (sumf p)) (mult c one) c).
      * exact (req_mult_compat c c (sumf p) one (req_refl c) Hnp).
      * apply (req_trans (mult c one) (mult one c) c
                         (mult_comm c one) (req_mult_one_l c)).
Qed.

(* Id free_energy_boltzmann @15945：F[p_b] == -D·log Z（训练-推理闭环
   的显式闭合值；逐点对数分解 → 求和线性 → 归一化 → 环坍缩） *)
Theorem req_free_energy_boltzmann :
  req (free_energy boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).
Proof.
  unfold free_energy.
  set (Eavg := sumf (fun s => mult (boltzmann_dist s) (base_loss s))).
  set (A := sumf (fun s => mult (boltzmann_dist s)
                                (log (boltzmann_dist s) (req_boltzmann_positive s)))).
  (* 步骤 1：逐点 p_b·log p_b == p_b·(-log Z) + opp((1/D)·p_b·E) *)
  assert (Hpoint :
    forall s : S,
      req (mult (boltzmann_dist s) (log (boltzmann_dist s) (req_boltzmann_positive s)))
          (plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))).
  {
    intro s.
    assert (H1 : req (mult (boltzmann_dist s)
                           (log (boltzmann_dist s) (req_boltzmann_positive s)))
                     (mult (boltzmann_dist s)
                           (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (req_mult_compat (boltzmann_dist s) (boltzmann_dist s)
                                (log (boltzmann_dist s) (req_boltzmann_positive s))
                                (plus (opp (log Z Z_pos))
                                      (opp (mult (inv_pos D D_pos) (base_loss s))))
                                (req_refl (boltzmann_dist s))
                                (req_boltzmann_log_decomp s)).
    apply (req_trans _ _ _ H1).
    apply (req_trans (mult (boltzmann_dist s)
                           (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                           (mult (boltzmann_dist s)
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                           (opp (mult (inv_pos D D_pos)
                                      (mult (boltzmann_dist s) (base_loss s)))))).
    - apply distrib.
    - apply req_plus_compat.
      + apply req_refl.
      + (* p_b·(opp((1/D)·E)) == opp((1/D)·(p_b·E))：opp_mult_l + 交换重组 *)
        apply (req_trans (mult (boltzmann_dist s)
                               (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (boltzmann_dist s)
                                    (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (inv_pos D D_pos)
                                    (mult (boltzmann_dist s) (base_loss s))))).
        * apply req_opp_mult_l.
        * apply (req_opp_compat (mult (boltzmann_dist s)
                                      (mult (inv_pos D D_pos) (base_loss s)))
                                (mult (inv_pos D D_pos)
                                      (mult (boltzmann_dist s) (base_loss s)))).
          exact (req_trans (mult (boltzmann_dist s)
                                 (mult (inv_pos D D_pos) (base_loss s)))
                           (mult (mult (boltzmann_dist s) (inv_pos D D_pos))
                                 (base_loss s))
                           (mult (inv_pos D D_pos)
                                 (mult (boltzmann_dist s) (base_loss s)))
                           (mult_assoc (boltzmann_dist s) (inv_pos D D_pos) (base_loss s))
                           (req_trans (mult (mult (boltzmann_dist s) (inv_pos D D_pos))
                                            (base_loss s))
                                      (mult (mult (inv_pos D D_pos) (boltzmann_dist s))
                                            (base_loss s))
                                      (mult (inv_pos D D_pos)
                                            (mult (boltzmann_dist s) (base_loss s)))
                                      (req_mult_compat (mult (boltzmann_dist s) (inv_pos D D_pos))
                                                       (mult (inv_pos D D_pos) (boltzmann_dist s))
                                                       (base_loss s) (base_loss s)
                                                       (mult_comm (boltzmann_dist s) (inv_pos D D_pos))
                                                       (req_refl (base_loss s)))
                                      (req_sym (mult (inv_pos D D_pos)
                                                     (mult (boltzmann_dist s) (base_loss s)))
                                               (mult (mult (inv_pos D D_pos) (boltzmann_dist s))
                                                     (base_loss s))
                                               (mult_assoc (inv_pos D D_pos)
                                                           (boltzmann_dist s) (base_loss s))))).
  }
  (* 步骤 2：求和 Σ p_b·log p_b == -log Z - (1/D)·⟨E⟩ *)
  assert (Hsum :
    req A (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
  {
    apply (req_trans A
      (sumf (fun s => plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                           (opp (mult (inv_pos D D_pos)
                                      (mult (boltzmann_dist s) (base_loss s))))))
      (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
    - apply (fsum_ext (fun s => mult (boltzmann_dist s)
                                     (log (boltzmann_dist s) (req_boltzmann_positive s)))
                      (fun s => plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                                     (opp (mult (inv_pos D D_pos)
                                                (mult (boltzmann_dist s) (base_loss s)))))).
      exact Hpoint.
    - apply (req_trans (sumf (fun s => plus (mult (boltzmann_dist s) (opp (log Z Z_pos)))
                                            (opp (mult (inv_pos D D_pos)
                                                       (mult (boltzmann_dist s) (base_loss s))))))
                       (plus (sumf (fun s => mult (boltzmann_dist s) (opp (log Z Z_pos))))
                             (sumf (fun s => opp (mult (inv_pos D D_pos)
                                                       (mult (boltzmann_dist s) (base_loss s))))))
                       (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
      + apply fsum_add.
      + apply req_plus_compat.
        * (* Σ p_b·(-log Z) == -log Z：交换 → 线性 → 归一化 → 单位元 *)
          apply (req_trans (sumf (fun s => mult (boltzmann_dist s) (opp (log Z Z_pos))))
                           (sumf (fun s => mult (opp (log Z Z_pos)) (boltzmann_dist s)))
                           (opp (log Z Z_pos))).
          -- apply (fsum_ext (fun s => mult (boltzmann_dist s) (opp (log Z Z_pos)))
                             (fun s => mult (opp (log Z Z_pos)) (boltzmann_dist s))).
             intro s. apply mult_comm.
          -- apply (req_trans (sumf (fun s => mult (opp (log Z Z_pos)) (boltzmann_dist s)))
                              (mult (opp (log Z Z_pos)) (sumf boltzmann_dist))
                              (opp (log Z Z_pos))).
             ++ apply (fsum_linear (opp (log Z Z_pos)) boltzmann_dist).
             ++ apply (req_trans (mult (opp (log Z Z_pos)) (sumf boltzmann_dist))
                                 (mult (opp (log Z Z_pos)) one)
                                 (opp (log Z Z_pos))).
                ** exact (req_mult_compat (opp (log Z Z_pos)) (opp (log Z Z_pos))
                                          (sumf boltzmann_dist) one
                                          (req_refl (opp (log Z Z_pos)))
                                          req_boltzmann_normalized).
                ** apply (req_trans (mult (opp (log Z Z_pos)) one)
                                    (mult one (opp (log Z Z_pos)))
                                    (opp (log Z Z_pos))
                                    (mult_comm (opp (log Z Z_pos)) one)
                                    (req_mult_one_l (opp (log Z Z_pos)))).
        * (* Σ opp((1/D)·p_b·E) == opp((1/D)·⟨E⟩) *)
          apply (req_trans (sumf (fun s => opp (mult (inv_pos D D_pos)
                                                     (mult (boltzmann_dist s) (base_loss s)))))
                           (opp (sumf (fun s => mult (inv_pos D D_pos)
                                                      (mult (boltzmann_dist s) (base_loss s)))))
                           (opp (mult (inv_pos D D_pos) Eavg))).
          -- apply fsum_opp.
          -- exact (req_opp_compat (sumf (fun s => mult (inv_pos D D_pos)
                                                        (mult (boltzmann_dist s) (base_loss s))))
                                   (mult (inv_pos D D_pos) Eavg)
                                   (fsum_linear (inv_pos D D_pos)
                                                (fun s => mult (boltzmann_dist s) (base_loss s)))).
  }
  (* 步骤 3：D·(-log Z - (1/D)⟨E⟩) == -D·log Z - ⟨E⟩ *)
  assert (Hmd : req (mult D (plus (opp (log Z Z_pos))
                                  (opp (mult (inv_pos D D_pos) Eavg))))
                    (plus (opp (mult D (log Z Z_pos))) (opp Eavg))).
  {
    apply (req_trans (mult D (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) Eavg))))
                     (plus (mult D (opp (log Z Z_pos)))
                           (mult D (opp (mult (inv_pos D D_pos) Eavg))))
                     (plus (opp (mult D (log Z Z_pos))) (opp Eavg))).
    - apply distrib.
    - apply req_plus_compat.
      + apply req_opp_mult_l.
      + apply (req_trans (mult D (opp (mult (inv_pos D D_pos) Eavg)))
                         (opp (mult D (mult (inv_pos D D_pos) Eavg))) (opp Eavg)).
        * apply req_opp_mult_l.
        * apply (req_opp_compat (mult D (mult (inv_pos D D_pos) Eavg)) Eavg).
          exact (req_trans (mult D (mult (inv_pos D D_pos) Eavg))
                           (mult (mult D (inv_pos D D_pos)) Eavg) Eavg
                           (mult_assoc D (inv_pos D D_pos) Eavg)
                           (req_trans (mult (mult D (inv_pos D D_pos)) Eavg)
                                      (mult one Eavg) Eavg
                                      (req_mult_compat (mult D (inv_pos D D_pos)) one
                                                       Eavg Eavg
                                                       (inv_pos_correct D D_pos)
                                                       (req_refl Eavg))
                                      (req_trans (mult one Eavg) (mult Eavg one) Eavg
                                                 (mult_comm one Eavg) (mult_one Eavg)))).
  }
  (* 步骤 4：⟨E⟩ + (-D·log Z - ⟨E⟩) == -D·log Z（环坍缩） *)
  assert (Hfin : req (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                    (opp (mult D (log Z Z_pos)))).
  {
    apply (req_trans (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                     (plus (plus Eavg (opp (mult D (log Z Z_pos)))) (opp Eavg))
                     (opp (mult D (log Z Z_pos)))).
    - exact (plus_assoc Eavg (opp (mult D (log Z Z_pos))) (opp Eavg)).
    - apply (req_trans (plus (plus Eavg (opp (mult D (log Z Z_pos)))) (opp Eavg))
                       (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))
                       (opp (mult D (log Z Z_pos)))).
      + exact (req_plus_compat (plus Eavg (opp (mult D (log Z Z_pos))))
                               (plus (opp (mult D (log Z Z_pos))) Eavg)
                               (opp Eavg) (opp Eavg)
                               (plus_comm Eavg (opp (mult D (log Z Z_pos))))
                               (req_refl (opp Eavg))).
      + apply (req_trans (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))
                         (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                         (opp (mult D (log Z Z_pos)))).
        * apply (req_sym (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                         (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))).
          apply plus_assoc.
        * apply (req_trans (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                           (plus (opp (mult D (log Z Z_pos))) zero)
                           (opp (mult D (log Z Z_pos)))).
          -- exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                                    (opp (mult D (log Z Z_pos)))
                                    (plus Eavg (opp Eavg)) zero
                                    (req_refl (opp (mult D (log Z Z_pos))))
                                    (plus_opp Eavg)).
          -- apply plus_zero.
  }
  (* 总装：plus Eavg (D·A) →(Hsum 进 A)→ plus Eavg (D·(-logZ-(1/D)⟨E⟩))
            →(Hmd)→ plus Eavg (-D·logZ-⟨E⟩) →(Hfin)→ opp(D·logZ) →(opp_mult_r)→ (opp D)·logZ *)
  apply (req_trans (plus Eavg (mult D A))
                   (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                   (mult (opp D) (log Z Z_pos))).
  - apply (req_trans (plus Eavg (mult D A))
                     (plus Eavg (mult D (plus (opp (log Z Z_pos))
                                              (opp (mult (inv_pos D D_pos) Eavg)))))
                     (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))).
    + exact (req_plus_compat Eavg Eavg (mult D A)
                             (mult D (plus (opp (log Z Z_pos))
                                           (opp (mult (inv_pos D D_pos) Eavg))))
                             (req_refl Eavg)
                             (req_mult_compat D D A
                                              (plus (opp (log Z Z_pos))
                                                    (opp (mult (inv_pos D D_pos) Eavg)))
                                              (req_refl D) Hsum)).
    + exact (req_plus_compat Eavg Eavg
                             (mult D (plus (opp (log Z Z_pos))
                                           (opp (mult (inv_pos D D_pos) Eavg))))
                             (plus (opp (mult D (log Z Z_pos))) (opp Eavg))
                             (req_refl Eavg) Hmd).
  - exact (req_trans _ _ _ Hfin
                     (req_sym (mult (opp D) (log Z Z_pos))
                              (opp (mult D (log Z Z_pos)))
                              (req_opp_mult_r D (log Z Z_pos)))).
Qed.

(* Id p_times_energy_decomp @16198：p·E == -D·p·log p_b - D·p·log Z
   （能量期望的逐点分解；kl_decomp 的步骤 1 引理） *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s))
        (plus (opp (mult D (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))))
              (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  set (Lp := log (boltzmann_dist s) (req_boltzmann_positive s)).
  set (Lz := log Z Z_pos).
  set (E := base_loss s).
  set (ps := p s).
  assert (He : req E (opp (mult D (plus Lp Lz))))
    by exact (req_energy_in_log_boltzmann s).
  (* Hsw : ps·(D·(Lp+Lz)) == D·(ps·(Lp+Lz))（结合-交换-逆结合） *)
  assert (Hsw : req (mult ps (mult D (plus Lp Lz)))
                    (mult D (mult ps (plus Lp Lz)))).
  { apply (req_trans (mult ps (mult D (plus Lp Lz)))
                     (mult (mult ps D) (plus Lp Lz))
                     (mult D (mult ps (plus Lp Lz)))).
    - apply mult_assoc.
    - apply (req_trans (mult (mult ps D) (plus Lp Lz))
                       (mult (mult D ps) (plus Lp Lz))
                       (mult D (mult ps (plus Lp Lz)))).
      + exact (req_mult_compat (mult ps D) (mult D ps) (plus Lp Lz) (plus Lp Lz)
                               (mult_comm ps D) (req_refl (plus Lp Lz))).
      + apply (req_sym (mult D (mult ps (plus Lp Lz)))
                       (mult (mult D ps) (plus Lp Lz))). apply mult_assoc. }
  (* Hdi : D·(ps·(Lp+Lz)) == D·(ps·Lp) + D·(ps·Lz)（distrib 经 compat 运输） *)
  assert (Hdi : req (mult D (mult ps (plus Lp Lz)))
                    (plus (mult D (mult ps Lp)) (mult D (mult ps Lz)))).
  { exact (req_trans _ _ _ (req_mult_compat D D (mult ps (plus Lp Lz))
                                            (plus (mult ps Lp) (mult ps Lz))
                                            (req_refl D) (distrib ps Lp Lz))
                           (distrib D (mult ps Lp) (mult ps Lz))). }
  (* Hop : opp(ps·(D·(Lp+Lz))) == opp(D·(ps·Lp)) + opp(D·(ps·Lz)) *)
  assert (Hop : req (opp (mult ps (mult D (plus Lp Lz))))
                    (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
  { apply (req_trans (opp (mult ps (mult D (plus Lp Lz))))
                     (opp (plus (mult D (mult ps Lp)) (mult D (mult ps Lz))))
                     (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
    - apply (req_opp_compat (mult ps (mult D (plus Lp Lz)))
                            (plus (mult D (mult ps Lp)) (mult D (mult ps Lz)))).
      exact (req_trans _ _ _ Hsw Hdi).
    - apply req_opp_plus. }
  (* 总装：ps·E →(He 运输)→ ps·opp(D·(Lp+Lz)) →(opp_mult_l)→ opp(ps·(D·(Lp+Lz))) →(Hop)→ 目标 *)
  apply (req_trans (mult ps E)
                   (opp (mult ps (mult D (plus Lp Lz))))
                   (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
  - apply (req_trans (mult ps E)
                     (mult ps (opp (mult D (plus Lp Lz))))
                     (opp (mult ps (mult D (plus Lp Lz))))).
    + exact (req_mult_compat ps ps E (opp (mult D (plus Lp Lz))) (req_refl ps) He).
    + apply req_opp_mult_l.
  - exact Hop.
Qed.

(* ============================================================ *)
(* 训练-推理闭环皇冠定理：F[p] == F[p_b] + D·KL(p || p_b)        *)
(*   （Id free_energy_kl_decomp @16259；req 旗舰件——除节内      *)
(*   sumf 三性质与 log 前提化 positive_dist 参数外零新增假设）  *)
(* ============================================================ *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (free_energy p Hp)
        (plus (free_energy boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s => mult (p s)
                                           (req_minus (log (p s) (Hp s))
                                                      (log (boltzmann_dist s)
                                                             (req_boltzmann_positive s))))))).
Proof.
  intros p Hp Hnp.
  unfold free_energy.
  set (Eavg := sumf (fun s => mult (p s) (base_loss s))).
  set (A := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (B := sumf (fun s => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))).
  set (KL := sumf (fun s => mult (p s)
                                 (req_minus (log (p s) (Hp s))
                                            (log (boltzmann_dist s)
                                                   (req_boltzmann_positive s))))).
  (* 步骤 1：Σ p·E == -D·B - D·log Z（p_times_energy_decomp 逐点 + 求和机器） *)
  assert (Hse : req Eavg (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
  {
    apply (req_trans Eavg
      (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)
                                                            (req_boltzmann_positive s)))))
                           (opp (mult D (mult (p s) (log Z Z_pos))))))
      (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
    - apply (fsum_ext (fun s => mult (p s) (base_loss s))
                      (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                     (opp (mult D (mult (p s) (log Z Z_pos)))))).
      intro s. exact (req_p_times_energy_decomp p s).
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s)
                                                               (log (boltzmann_dist s)
                                                                       (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
      + apply fsum_add.
      + apply req_plus_compat.
        * apply (req_trans (sumf (fun s => opp (mult D (mult (p s)
                                                             (log (boltzmann_dist s)
                                                                     (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s)
                                                             (log (boltzmann_dist s)
                                                                     (req_boltzmann_positive s))))))
                           (opp (mult D B))).
          -- apply fsum_opp.
          -- exact (req_opp_compat (sumf (fun s => mult D (mult (p s)
                                                                (log (boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                   (mult D B)
                                   (fsum_linear D (fun s => mult (p s)
                                                                 (log (boltzmann_dist s)
                                                                         (req_boltzmann_positive s))))).
        * apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          -- apply fsum_opp.
          -- apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                              (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                              (opp (mult D (log Z Z_pos)))).
             ++ exact (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                      (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                      (fsum_linear D (fun s => mult (p s) (log Z Z_pos)))).
             ++ exact (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                      (mult D (log Z Z_pos))
                                      (req_mult_compat D D
                                                       (sumf (fun s => mult (p s) (log Z Z_pos)))
                                                       (log Z Z_pos) (req_refl D)
                                                       (fsum_norm_const p (log Z Z_pos) Hnp))).
  }
  (* 步骤 2：KL == A - B（逐点 req_mult_minus_distr_l + fsum_ext） *)
  assert (Hkl : req KL (req_minus A B)).
  {
    apply (req_trans KL
                     (sumf (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                               (mult (p s) (log (boltzmann_dist s)
                                                                (req_boltzmann_positive s)))))
                     (req_minus A B)).
    - apply (fsum_ext (fun s => mult (p s)
                                     (req_minus (log (p s) (Hp s))
                                                (log (boltzmann_dist s)
                                                       (req_boltzmann_positive s))))
                      (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (boltzmann_dist s)
                                                           (req_boltzmann_positive s))))).
      intro s. exact (req_mult_minus_distr_l (p s) (log (p s) (Hp s))
                                             (log (boltzmann_dist s)
                                                    (req_boltzmann_positive s))).
    - exact (fsum_minus (fun s => mult (p s) (log (p s) (Hp s)))
                        (fun s => mult (p s) (log (boltzmann_dist s)
                                                 (req_boltzmann_positive s)))).
  }
  (* 步骤 3 总装：
     Eavg + D·A →(Hse)→ (-D·B - D·logZ) + D·A →(交换重组)→ -D·logZ + (D·A - D·B)
     →(req_mult_minus_distr_l 逆向 + Hkl)→ -D·logZ + D·KL = (opp D·logZ 形) + D·KL。
     与 RHS plus F_b (D·KL)（F_b == opp(D·logZ)）对齐。 *)
  assert (HDkl : req (mult D KL)
                     (plus (mult D A) (opp (mult D B)))).
  { exact (req_trans _ _ _
           (req_mult_compat D D KL (req_minus A B) (req_refl D) Hkl)
           (req_mult_minus_distr_l D A B)). }
  assert (Hmain : req (plus Eavg (mult D A))
                      (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
  {
    apply (req_trans (plus Eavg (mult D A))
                     (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                           (mult D A))
                     (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
    - exact (req_plus_compat Eavg (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                             (mult D A) (mult D A) Hse (req_refl (mult D A))).
    - (* (x + y) + z == y + (z + x)：x := -D·B, y := -D·logZ, z := D·A *)
      apply (req_trans (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                             (mult D A))
                       (plus (opp (mult D (log Z Z_pos)))
                             (plus (mult D A) (opp (mult D B))))
                       (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
      + apply (req_trans (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                               (mult D A))
                         (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                               (mult D A))
                         (plus (opp (mult D (log Z Z_pos)))
                               (plus (mult D A) (opp (mult D B))))).
        * exact (req_plus_compat (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                                 (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                 (mult D A) (mult D A)
                                 (plus_comm (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                                 (req_refl (mult D A))).
        * apply (req_trans (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                 (mult D A))
                           (plus (opp (mult D (log Z Z_pos)))
                                 (plus (opp (mult D B)) (mult D A)))
                           (plus (opp (mult D (log Z Z_pos)))
                                 (plus (mult D A) (opp (mult D B))))).
          -- apply (req_sym (plus (opp (mult D (log Z Z_pos)))
                                  (plus (opp (mult D B)) (mult D A)))
                            (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                  (mult D A))).
             apply plus_assoc.
          -- exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                                    (opp (mult D (log Z Z_pos)))
                                    (plus (opp (mult D B)) (mult D A))
                                    (plus (mult D A) (opp (mult D B)))
                                    (req_refl (opp (mult D (log Z Z_pos))))
                                    (plus_comm (opp (mult D B)) (mult D A))).
      + exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                               (mult (opp D) (log Z Z_pos))
                               (plus (mult D A) (opp (mult D B))) (mult D KL)
                               (req_sym (mult (opp D) (log Z Z_pos))
                                        (opp (mult D (log Z Z_pos)))
                                        (req_opp_mult_r D (log Z Z_pos)))
                               (req_sym _ _ HDkl)).
  }
  exact (req_trans _ _ _ Hmain
           (req_plus_compat (mult (opp D) (log Z Z_pos))
                            (free_energy boltzmann_dist req_boltzmann_positive)
                            (mult D KL) (mult D KL)
                            (req_sym (free_energy boltzmann_dist req_boltzmann_positive)
                                     (mult (opp D) (log Z Z_pos))
                                     req_free_energy_boltzmann)
                            (req_refl (mult D KL)))).
Qed.
(* Id free_energy_kl_diff @16443：F[p] - F[p_b] == D·KL(p||p_b)（差形式） *)
Theorem req_free_energy_kl_diff :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (req_minus (free_energy p Hp)
                   (free_energy boltzmann_dist req_boltzmann_positive))
        (mult D (sumf (fun s => mult (p s)
                                     (req_minus (log (p s) (Hp s))
                                                (log (boltzmann_dist s)
                                                       (req_boltzmann_positive s)))))).
Proof.
  intros p Hp Hnp. unfold req_minus.
  assert (Hdec := req_free_energy_kl_decomp p Hp Hnp).
  apply (req_trans (plus (free_energy p Hp)
                         (opp (free_energy boltzmann_dist req_boltzmann_positive)))
                   (plus (plus (free_energy boltzmann_dist req_boltzmann_positive)
                               (mult D (sumf (fun s => mult (p s)
                                                            (req_minus (log (p s) (Hp s))
                                                                       (log (boltzmann_dist s)
                                                                              (req_boltzmann_positive s)))))))
                         (opp (free_energy boltzmann_dist req_boltzmann_positive)))
                   (mult D (sumf (fun s => mult (p s)
                                                (req_minus (log (p s) (Hp s))
                                                           (log (boltzmann_dist s)
                                                                  (req_boltzmann_positive s))))))).
  - exact (req_plus_compat (free_energy p Hp)
                           (plus (free_energy boltzmann_dist req_boltzmann_positive)
                                 (mult D (sumf (fun s => mult (p s)
                                                              (req_minus (log (p s) (Hp s))
                                                                         (log (boltzmann_dist s)
                                                                                (req_boltzmann_positive s)))))))
                           (opp (free_energy boltzmann_dist req_boltzmann_positive))
                           (opp (free_energy boltzmann_dist req_boltzmann_positive))
                           Hdec (req_refl (opp (free_energy boltzmann_dist
                                                            req_boltzmann_positive)))).
  - set (Fb := free_energy boltzmann_dist req_boltzmann_positive).
    set (KL := sumf (fun s => mult (p s)
                                   (req_minus (log (p s) (Hp s))
                                              (log (boltzmann_dist s)
                                                     (req_boltzmann_positive s))))).
    apply (req_trans (plus (plus Fb (mult D KL)) (opp Fb))
                     (plus Fb (plus (mult D KL) (opp Fb))) (mult D KL)).
    + apply (req_sym (plus Fb (plus (mult D KL) (opp Fb)))
                     (plus (plus Fb (mult D KL)) (opp Fb))).
      apply plus_assoc.
    + apply (req_trans (plus Fb (plus (mult D KL) (opp Fb)))
                       (plus (plus Fb (opp Fb)) (mult D KL))
                       (mult D KL)).
      * apply (req_trans (plus Fb (plus (mult D KL) (opp Fb)))
                         (plus Fb (plus (opp Fb) (mult D KL)))
                         (plus (plus Fb (opp Fb)) (mult D KL))).
        -- exact (req_plus_compat Fb Fb (plus (mult D KL) (opp Fb))
                                  (plus (opp Fb) (mult D KL))
                                  (req_refl Fb) (plus_comm (mult D KL) (opp Fb))).
        -- apply plus_assoc.
      * apply (req_trans (plus (plus Fb (opp Fb)) (mult D KL))
                         (plus zero (mult D KL)) (mult D KL)).
        -- exact (req_plus_compat (plus Fb (opp Fb)) zero (mult D KL) (mult D KL)
                                  (plus_opp Fb) (req_refl (mult D KL))).
        -- exact (req_trans (plus zero (mult D KL)) (plus (mult D KL) zero) (mult D KL)
                            (plus_comm zero (mult D KL)) (plus_zero (mult D KL))).
Qed.

(* Id free_energy_diff_kl @16489：F[p] - F[q] == D·(KL(p||p_b) - KL(q||p_b)) *)
Theorem req_free_energy_diff_kl :
  forall (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q),
    normalized p -> normalized q ->
    req (req_minus (free_energy p Hp) (free_energy q Hq))
        (mult D (req_minus
                   (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s))
                                                   (log (boltzmann_dist s)
                                                          (req_boltzmann_positive s)))))
                   (sumf (fun s => mult (q s)
                                        (req_minus (log (q s) (Hq s))
                                                   (log (boltzmann_dist s)
                                                          (req_boltzmann_positive s))))))).
Proof.
  intros p q Hp Hq Hnp Hnq.
  set (Fb := free_energy boltzmann_dist req_boltzmann_positive).
  set (KLp := sumf (fun s => mult (p s)
                                  (req_minus (log (p s) (Hp s))
                                             (log (boltzmann_dist s)
                                                    (req_boltzmann_positive s))))).
  set (KLq := sumf (fun s => mult (q s)
                                  (req_minus (log (q s) (Hq s))
                                             (log (boltzmann_dist s)
                                                    (req_boltzmann_positive s))))).
  apply (req_trans (req_minus (free_energy p Hp) (free_energy q Hq))
                   (req_minus (plus Fb (mult D KLp)) (plus Fb (mult D KLq)))
                   (mult D (req_minus KLp KLq))).
  - exact (reqd_minus_compat (free_energy p Hp) (plus Fb (mult D KLp))
                             (free_energy q Hq) (plus Fb (mult D KLq))
                             (req_free_energy_kl_decomp p Hp Hnp)
                             (req_free_energy_kl_decomp q Hq Hnq)).
  - apply (req_trans (req_minus (plus Fb (mult D KLp)) (plus Fb (mult D KLq)))
                     (req_minus (mult D KLp) (mult D KLq))
                     (mult D (req_minus KLp KLq))).
    + exact (req_minus_plus_congr_l Fb (mult D KLp) (mult D KLq)).
    + exact (req_sym _ _ (req_mult_minus_distr_l D KLp KLq)).
Qed.

(* Id relative_entropy_self_zero' @18483：KL(p||p) == 0（无条件件——旗舰演示：
   除节内 sumf 接口外零新增假设、零桥假设） *)
Lemma req_relative_entropy_self_zero :
  forall (p : S -> R) (Hp : positive_dist p),
    req (req_relative_entropy p p Hp Hp) zero.
Proof.
  intros p Hp. unfold req_relative_entropy.
  apply (req_trans (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s)) (log (p s) (Hp s)))))
                   (sumf (fun _ : S => zero)) zero).
  - apply (fsum_ext (fun s => mult (p s)
                                   (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                    (fun _ : S => zero)).
    intro s.
    apply (req_trans (mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                     (mult (p s) zero) zero).
    + exact (req_mult_compat (p s) (p s)
                             (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))) zero
                             (req_refl (p s))
                             (req_minus_self_zero (log (p s) (Hp s)) (log (p s) (Hp s))
                                                  (req_refl (log (p s) (Hp s))))).
    + apply mult_zero.
  - exact fsum_zero.
Qed.

(* Id entropy_neg_sum @16946：Σ p·log p == opp S[p]（熵的负和形式；无条件件） *)
Lemma req_entropy_neg_sum :
  forall (p : S -> R) (Hp : positive_dist p),
    req (sumf (fun s => mult (p s) (log (p s) (Hp s))))
        (opp (entropy_dist p Hp)).
Proof.
  intros p Hp. unfold entropy_dist.
  apply (req_trans (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                   (sumf (fun s => opp (mult (p s) (opp (log (p s) (Hp s))))))
                   (opp (sumf (fun s => mult (p s) (opp (log (p s) (Hp s))))))).
  - apply (fsum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                    (fun s => opp (mult (p s) (opp (log (p s) (Hp s)))))).
    intro s.
    apply (req_trans (mult (p s) (log (p s) (Hp s)))
                     (opp (opp (mult (p s) (log (p s) (Hp s)))))
                     (opp (mult (p s) (opp (log (p s) (Hp s)))))).
    + apply (req_sym (opp (opp (mult (p s) (log (p s) (Hp s)))))
                     (mult (p s) (log (p s) (Hp s)))).
      apply req_double_neg.
    + apply (req_opp_compat (opp (mult (p s) (log (p s) (Hp s))))
                            (mult (p s) (opp (log (p s) (Hp s))))).
      exact (req_sym (mult (p s) (opp (log (p s) (Hp s))))
                     (opp (mult (p s) (log (p s) (Hp s))))
                     (req_opp_mult_l (p s) (log (p s) (Hp s)))).
  - apply fsum_opp.
Qed.

(* Id free_energy_entropy @16976：F[p] == <E>_p - D·S[p]（无条件件） *)
Lemma req_free_energy_entropy :
  forall (p : S -> R) (Hp : positive_dist p),
    req (free_energy p Hp)
        (plus (energy_expectation p) (mult D (opp (entropy_dist p Hp)))).
Proof.
  intros p Hp.
  unfold free_energy, energy_expectation.
  exact (req_plus_compat (sumf (fun s => mult (p s) (base_loss s)))
                         (sumf (fun s => mult (p s) (base_loss s)))
                         (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult D (opp (entropy_dist p Hp)))
                         (req_refl (sumf (fun s => mult (p s) (base_loss s))))
                         (req_mult_compat D D
                                          (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                                          (opp (entropy_dist p Hp))
                                          (req_refl D) (req_entropy_neg_sum p Hp))).
Qed.
(* ---- Gibbs 簇公共辅件（R 层代数，导出给 equality 复用） ---- *)

(* x·(y·inv x) == y（分式约分） *)
Lemma reqd_p_times_ratio :
  forall (x y : R) (Hx : lt zero x), req (mult x (mult y (inv_pos x Hx))) y.
Proof.
  intros x y Hx.
  apply (req_trans (mult x (mult y (inv_pos x Hx)))
                   (mult y (mult x (inv_pos x Hx)))
                   y).
  - apply (req_trans (mult x (mult y (inv_pos x Hx)))
                     (mult (mult x y) (inv_pos x Hx))
                     (mult y (mult x (inv_pos x Hx)))).
    + exact (mult_assoc x y (inv_pos x Hx)).
    + apply (req_trans (mult (mult x y) (inv_pos x Hx))
                       (mult (mult y x) (inv_pos x Hx))
                       (mult y (mult x (inv_pos x Hx)))).
      * exact (req_mult_compat (mult x y) (mult y x)
                               (inv_pos x Hx) (inv_pos x Hx)
                               (mult_comm x y) (req_refl (inv_pos x Hx))).
      * exact (req_sym (mult y (mult x (inv_pos x Hx)))
                       (mult (mult y x) (inv_pos x Hx))
                       (mult_assoc y x (inv_pos x Hx))).
  - exact (req_trans (mult y (mult x (inv_pos x Hx)))
                     (mult y one) y
                     (req_mult_compat y y (mult x (inv_pos x Hx)) one
                                      (req_refl y) (inv_pos_correct x Hx))
                     (mult_one y)).
Qed.

(* x·(1 - y/x) == x - y（1 - 分式换形） *)
Lemma reqd_p_minus_ratio :
  forall (x y : R) (Hx : lt zero x),
    req (mult x (req_minus one (mult y (inv_pos x Hx)))) (req_minus x y).
Proof.
  intros x y Hx.
  apply (req_trans (mult x (req_minus one (mult y (inv_pos x Hx))))
                   (plus (mult x one) (mult x (opp (mult y (inv_pos x Hx)))))
                   (req_minus x y)).
  - exact (distrib x one (opp (mult y (inv_pos x Hx)))).
  - apply (req_trans (plus (mult x one) (mult x (opp (mult y (inv_pos x Hx)))))
                     (plus x (opp (mult x (mult y (inv_pos x Hx)))))
                     (req_minus x y)).
    + exact (req_plus_compat (mult x one) x
                             (mult x (opp (mult y (inv_pos x Hx))))
                             (opp (mult x (mult y (inv_pos x Hx))))
                             (mult_one x)
                             (req_opp_mult_l x (mult y (inv_pos x Hx)))).
    + apply (req_trans (plus x (opp (mult x (mult y (inv_pos x Hx)))))
                       (plus x (opp y))
                       (req_minus x y)).
      * exact (req_plus_compat x x
                               (opp (mult x (mult y (inv_pos x Hx))))
                               (opp y)
                               (req_refl x)
                               (req_opp_compat (mult x (mult y (inv_pos x Hx))) y
                                               (reqd_p_times_ratio x y Hx))).
      * apply req_refl.
Qed.

(* 1 - R == opp(R - 1)（切线等号点换形） *)
Lemma reqd_minus_one_flip :
  forall a : R, req (req_minus one a) (opp (req_minus a one)).
Proof.
  intro a.
  apply (req_trans (req_minus one a)
                   (plus (opp a) one)
                   (opp (req_minus a one))).
  - exact (req_trans (req_minus one a) (plus one (opp a)) (plus (opp a) one)
                     (req_refl (plus one (opp a))) (plus_comm one (opp a))).
  - exact (req_sym _ _ (req_opp_minus a one)).
Qed.

(* Id gibbs_pointwise @16538：p - q ≤ p·(log p - log q)（逐点分式约分；
   消费 dist_log_le_linear 桥 + reqd_log_div 组装） *)
Lemma req_gibbs_pointwise :
  forall (p q : S -> R) (s : S) (Hps : lt zero (p s)) (Hqs : lt zero (q s)),
    le (req_minus (p s) (q s))
       (mult (p s) (req_minus (log (p s) (Hps)) (log (q s) (Hqs)))).
Proof.
  intros p q s Hps Hqs.
  set (Rqp := mult (q s) (inv_pos (p s) Hps)).
  set (Hr := mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  assert (Hlin : le (log Rqp Hr) (req_minus Rqp one))
    by exact (dist_log_le_linear Rqp Hr).
  assert (Hopp : le (opp (req_minus Rqp one)) (opp (log Rqp Hr)))
    by exact (opp_le_compat (log Rqp Hr) (req_minus Rqp one) Hlin).
  (* Hjoin : log p - log q == opp(log(q/p))（log(p/q) == -log(q/p)） *)
  assert (Hjoin : req (req_minus (log (p s) Hps) (log (q s) Hqs))
                      (opp (log Rqp Hr))).
  { apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                     (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (opp (log Rqp Hr))).
    - apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                       (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                       (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))).
      + apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                         (plus (log (p s) Hps) (opp (log (q s) Hqs)))
                         (plus (opp (log (q s) Hqs)) (log (p s) Hps))).
        * exact (req_refl (plus (log (p s) Hps) (opp (log (q s) Hqs)))).
        * apply plus_comm.
      + exact (req_sym _ _ (req_opp_minus (log (q s) Hqs) (log (p s) Hps))).
    - exact (req_opp_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (log Rqp Hr)
                            (req_sym _ _ (reqd_log_div (q s) (p s) Hqs Hps))). }
  assert (Hlhsform : req (mult (p s) (req_minus one Rqp)) (req_minus (p s) (q s)))
    by exact (reqd_p_minus_ratio (p s) (q s) Hps).
  (* Hml : p·(1 - q/p) ≤ p·(-log(q/p))（p > 0 左乘保序） *)
  assert (Hml : le (mult (p s) (req_minus one Rqp)) (mult (p s) (opp (log Rqp Hr)))).
  { apply (le_id_l (mult (p s) (req_minus one Rqp))
                   (mult (p s) (opp (req_minus Rqp one)))
                   (mult (p s) (opp (log Rqp Hr)))).
    - exact (req_mult_compat (p s) (p s) (req_minus one Rqp) (opp (req_minus Rqp one))
                             (req_refl (p s)) (reqd_minus_one_flip Rqp)).
    - exact (req_le_mult_compat_r (p s) (opp (req_minus Rqp one)) (opp (log Rqp Hr))
                                  (lt_le_iff zero (p s) (inl Hps)) Hopp). }
  exact (le_id_l (req_minus (p s) (q s))
                 (mult (p s) (req_minus one Rqp))
                 (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs)))
                 (req_sym _ _ Hlhsform)
                 (le_id_r (mult (p s) (req_minus one Rqp))
                          (mult (p s) (opp (log Rqp Hr)))
                          (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs)))
                          (req_sym _ _ (req_mult_compat (p s) (p s)
                                                        (req_minus (log (p s) Hps) (log (q s) Hqs))
                                                        (opp (log Rqp Hr))
                                                        (req_refl (p s)) Hjoin))
                          Hml)).
Qed.

(* Id gibbs_inequality @16629：归一化正分布的 KL ≥ 0（Gibbs 不等式） *)
Theorem req_gibbs_inequality :
  forall (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q),
    normalized p -> normalized q ->
    le zero (req_relative_entropy p q Hp Hq).
Proof.
  intros p q Hp Hq Hnp Hnq. unfold req_relative_entropy.
  assert (Hpt : forall s : S,
                  le (req_minus (p s) (q s))
                     (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s; exact (req_gibbs_pointwise p q s (Hp s) (Hq s))).
  assert (Hle : le (sumf (fun s => req_minus (p s) (q s)))
                   (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (fsum_le _ _ Hpt).
  assert (Hsum0 : req (sumf (fun s => req_minus (p s) (q s))) zero).
  { exact (req_trans _ _ _ (fsum_minus p q)
                           (req_minus_self_zero (sumf p) (sumf q)
                                                (req_trans _ _ _ Hnp (req_sym _ _ Hnq)))). }
  exact (le_id_l zero (sumf (fun s => req_minus (p s) (q s)))
                    (sumf (fun s => mult (p s)
                                         (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                    (req_sym _ _ Hsum0) Hle).
Qed.

(* Id gibbs_equality @16678：KL(p||q) == 0 ⟹ p == q（逐点；
   等号条件经 dist_log_eq_linear 桥——log 严格凹的唯一缺字段） *)
Theorem req_gibbs_equality :
  forall (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q),
    normalized p -> normalized q ->
    req (req_relative_entropy p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl0 s0.
  unfold req_relative_entropy in Hkl0.
  set (KLsum := sumf (fun s => mult (p s)
                                    (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))).
  set (S2 := sumf (fun s => req_minus (p s) (q s))).
  assert (Hpq0 : req S2 zero).
  { exact (req_trans _ _ _ (fsum_minus p q)
                           (req_minus_self_zero (sumf p) (sumf q)
                                                (req_trans _ _ _ Hnp (req_sym _ _ Hnq)))). }
  (* 1) d(s) ≥ 0 逐点 *)
  assert (Hd_nonneg : forall s : S,
            le zero (req_minus (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                               (req_minus (p s) (q s)))).
  { intro s. apply req_le_minus_nonneg.
    exact (req_gibbs_pointwise p q s (Hp s) (Hq s)). }
  (* 2) Σ d == 0 *)
  assert (Hd_sum : req (sumf (fun s => req_minus
                                        (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                                        (req_minus (p s) (q s)))) zero).
  { apply (req_trans (sumf (fun s => req_minus
                                        (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                                        (req_minus (p s) (q s))))
                     (req_minus KLsum S2)
                     zero).
    - apply fsum_minus.
    - apply (req_trans (req_minus KLsum S2) (req_minus KLsum zero) zero).
      + exact (reqd_minus_compat KLsum KLsum S2 zero (req_refl KLsum) Hpq0).
      + exact (req_trans _ _ _ (reqd_minus_zero_r KLsum) Hkl0). }
  (* 3) fsum_zero_nonneg：d(s) == 0 逐点 *)
  assert (Hd0 : forall s : S,
            req (req_minus (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                           (req_minus (p s) (q s))) zero)
    by exact (fsum_zero_nonneg _ Hd_nonneg Hd_sum).
  (* 4) minus_eq_cancel：p·(log p - log q) == p - q *)
  assert (Hceq : forall s : S,
            req (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                (req_minus (p s) (q s)))
    by (intro s; exact (req_minus_eq_cancel _ _ (Hd0 s))).
  (* 5) p·(log p - log q) == p·(1 - q/p) ⟹ log p - log q == 1 - q/p（p > 0 消去） *)
  set (Hr := mult_positive (q s0) (inv_pos (p s0) (Hp s0)) (Hq s0)
                           (inv_pos_pos (p s0) (Hp s0))).
  assert (Hcancel_p : req (mult (p s0) (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                          (mult (p s0) (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0))))))
    by exact (req_trans _ _ _ (Hceq s0)
                             (req_sym _ _ (reqd_p_minus_ratio (p s0) (q s0) (Hp s0)))).
  assert (Hlm : req (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                    (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0)))))
    by exact (req_mult_cancel_l (p s0)
                                (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                                (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0))))
                                (Hp s0) Hcancel_p).
  assert (Hlmflip : req (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                        (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)))
    by exact (req_trans _ _ _ Hlm
                        (reqd_minus_one_flip (mult (q s0) (inv_pos (p s0) (Hp s0))))).
  (* 6) log(q/p) == opp(log p - log q)（reqd_log_div 双向） *)
  assert (Hlog_opplm : req (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                           (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
  { apply (req_trans (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                     (req_minus (log (q s0) (Hq s0)) (log (p s0) (Hp s0)))
                     (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
    - exact (reqd_log_div (q s0) (p s0) (Hq s0) (Hp s0)).
    - apply (req_trans (req_minus (log (q s0) (Hq s0)) (log (p s0) (Hp s0)))
                       (plus (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))
                       (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
      + exact (req_refl (plus (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))).
      + exact (req_trans _ _ _
                         (plus_comm (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))
                         (req_sym _ _ (req_opp_minus (log (p s0) (Hp s0))
                                                     (log (q s0) (Hq s0))))). }
  (* 7) log(q/p) == q/p - 1 ⟹ q/p == 1（dist_log_eq_linear 桥） *)
  assert (Hlog_eq : req (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                        (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
  { apply (req_trans (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                     (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                     (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
    - exact Hlog_opplm.
    - apply (req_trans (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                       (opp (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)))
                       (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
      + exact (req_opp_compat (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                              (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one))
                              Hlmflip).
      + apply req_double_neg. }
  assert (Hratio_one : req (mult (q s0) (inv_pos (p s0) (Hp s0))) one)
    by exact (dist_log_eq_linear (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr Hlog_eq).
  (* 8) q·inv p == p·inv p ⟹ q == p（inv p > 0 右消去） *)
  exact (req_sym _ _
           (req_mult_cancel_r (inv_pos (p s0) (Hp s0)) (q s0) (p s0)
                              (inv_pos_pos (p s0) (Hp s0))
                              (req_trans _ _ _ Hratio_one
                                         (req_sym _ _ (inv_pos_correct (p s0) (Hp s0)))))).
Qed.

(* Id boltzmann_dist_pos @16824（与节内 req_boltzmann_positive 同件；命名对齐台账） *)
Lemma req_boltzmann_dist_pos : forall s : S, lt zero (boltzmann_dist s).
Proof. exact req_boltzmann_positive. Qed.

(* ============================================================ *)
(* 自由能最小化 / 唯一性 / 熵-温度层收口（批 2 续建件）        *)
(*   Id 原件：min_free_energy_is_boltzmann@16838               *)
(*            free_energy_min_unique@16888                    *)
(*            entropy_deficit_kl@16993 max_entropy@17069      *)
(*            entropy_max_unique@17653 cross_entropy_decomp@18094 *)
(*            elbo 族@18359-18520 training_equivalence@18657  *)
(* ============================================================ *)

(* Id min_free_energy_is_boltzmann @16838：F[p_b] ≤ F[p]
   【旗舰 req 无条件形态】分解恒等式 + KL ≥ 0 + D>0 保序，零额外假设位 *)
Theorem req_min_free_energy_is_boltzmann :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    le (free_energy boltzmann_dist req_boltzmann_positive) (free_energy p Hp).
Proof.
  intros p Hp Hnp.
  set (K := req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive).
  set (FB := free_energy boltzmann_dist req_boltzmann_positive).
  (* 1. F[p] == F[p_b] + D·KL（req_relative_entropy 与 decomp 的 sumf 展开可转换） *)
  assert (Hdecomp : req (free_energy p Hp) (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  (* 2. KL ≥ 0（req_gibbs_inequality） *)
  assert (Hkl : le zero K)
    by exact (req_gibbs_inequality p boltzmann_dist Hp req_boltzmann_positive
                                Hnp req_boltzmann_normalized).
  (* 3. D > 0 ⟹ 0 ≤ D·KL *)
  assert (Hdkl : le zero (mult D K)).
  { apply (le_id_l zero (mult D zero) (mult D K)).
    - exact (req_sym _ _ (req_mult_zero_r D)).
    - apply (req_le_mult_compat_r D zero K).
      + exact (lt_le_iff zero D (inl D_pos)).
      + exact Hkl. }
  (* 4. F[p_b] ≤ F[p_b] + D·KL（le_plus_compat 保左，zero 项经 req 归位） *)
  assert (Hfin : le FB (plus FB (mult D K))).
  { apply (le_id_l FB (plus FB zero) (plus FB (mult D K))).
    - exact (req_sym _ _ (req_plus_zero_r FB)).
    - apply (le_plus_compat FB FB zero (mult D K)).
      + apply le_refl.
      + exact Hdkl. }
  (* 5. 右侧换形回 F[p] *)
  exact (le_id_r FB (plus FB (mult D K)) (free_energy p Hp)
                   (req_sym _ _ Hdecomp) Hfin).
Qed.

(* Id free_energy_min_unique @16888【旗舰唯一性 req 无条件形态】：
   F[p] == F[p_b] ⟹ p == p_b 逐点。链：decomp ⟹ D·KL==0（加法消去）
   ⟹ KL==0（D>0 乘法消去）⟹ gibbs_equality。 *)
Theorem req_free_energy_min_unique :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (free_energy p Hp) (free_energy boltzmann_dist req_boltzmann_positive) ->
    forall s : S, req (p s) (boltzmann_dist s).
Proof.
  intros p Hp Hnp Hfeq s.
  set (K := req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive).
  set (FB := free_energy boltzmann_dist req_boltzmann_positive).
  (* 1. F[p] == F[p_b] + D·KL *)
  assert (Hdecomp : req (free_energy p Hp) (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  (* 2. F[p_b] + D·KL == F[p_b] ⟹ D·KL == 0 *)
  assert (Hplus : req (plus FB (mult D K)) FB)
    by exact (req_trans _ _ _ (req_sym _ _ Hdecomp) Hfeq).
  assert (Hdkl0 : req (mult D K) zero)
    by exact (req_plus_cancel_zero FB (mult D K) Hplus).
  (* 3. D > 0 ⟹ KL == 0 *)
  assert (Hkl0 : req K zero).
  { apply (req_mult_cancel_l D K zero D_pos).
    exact (req_trans _ _ _ Hdkl0 (req_sym _ _ (req_mult_zero_r D))). }
  (* 4. gibbs_equality 收口 *)
  exact (req_gibbs_equality p boltzmann_dist Hp req_boltzmann_positive
                            Hnp req_boltzmann_normalized Hkl0 s).
Qed.

(* Id entropy_deficit_kl @16993：同能量约束下 S[p_b] − S[p] == KL(p‖p_b)。
   链：自由能恒等式（两端）+ 同能量消去（req_plus_cancel_l）+ 环消去（req_ring_d_cancel）。 *)
Theorem req_entropy_deficit_kl :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (energy_expectation p) (energy_expectation boltzmann_dist) ->
    req (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                   (entropy_dist p Hp))
       (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive).
Proof.
  intros p Hp Hnp Henergy.
  set (Sp := entropy_dist p Hp).
  set (Sb := entropy_dist boltzmann_dist req_boltzmann_positive).
  set (K := req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive).
  set (Ep := energy_expectation p).
  set (Eb := energy_expectation boltzmann_dist).
  set (FB0 := free_energy boltzmann_dist req_boltzmann_positive).
  (* 1. 三条自由能恒等式 *)
  assert (Hdecomp : req (free_energy p Hp) (plus FB0 (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  assert (Hfe_p : req (free_energy p Hp) (plus Ep (mult D (opp Sp))))
    by exact (req_free_energy_entropy p Hp).
  assert (Hfe_b : req FB0 (plus Eb (mult D (opp Sb))))
    by exact (req_free_energy_entropy boltzmann_dist req_boltzmann_positive).
  (* 2. ⟨E⟩_p − D·S[p] == (⟨E⟩_b − D·S[p_b]) + D·KL *)
  assert (Htot : req (plus Ep (mult D (opp Sp)))
                     (plus (plus Eb (mult D (opp Sb))) (mult D K))).
  { exact (req_trans (plus Ep (mult D (opp Sp)))
                     (plus FB0 (mult D K))
                     (plus (plus Eb (mult D (opp Sb))) (mult D K))
                     (req_trans _ _ _ (req_sym _ _ Hfe_p) Hdecomp)
                     (req_plus_compat FB0 (plus Eb (mult D (opp Sb))) (mult D K) (mult D K)
                        Hfe_b (req_refl (mult D K)))). }
  (* 3. 同能量换形 ⟨E⟩_p ↦ ⟨E⟩_b 后左消去 *)
  assert (Hcancel : req (mult D (opp Sp))
                        (plus (mult D (opp Sb)) (mult D K))).
  { apply (req_plus_cancel_l Eb (mult D (opp Sp)) (plus (mult D (opp Sb)) (mult D K))).
    apply (req_trans (plus Eb (mult D (opp Sp)))
                     (plus Ep (mult D (opp Sp)))
                     (plus Eb (plus (mult D (opp Sb)) (mult D K)))).
    - exact (req_plus_compat Eb Ep (mult D (opp Sp)) (mult D (opp Sp))
                             (req_sym _ _ Henergy) (req_refl (mult D (opp Sp)))).
    - exact (req_trans (plus Ep (mult D (opp Sp)))
                       (plus (plus Eb (mult D (opp Sb))) (mult D K))
                       (plus Eb (plus (mult D (opp Sb)) (mult D K)))
                       Htot
                       (req_sym _ _ (plus_assoc Eb (mult D (opp Sb)) (mult D K)))). }
  (* 4. 环消去（D > 0）：S[p_b] − S[p] == KL *)
  exact (req_ring_d_cancel D Sp Sb K D_pos Hcancel).
Qed.

(* Id max_entropy_is_boltzmann @17069：同能量 ⟹ S[p] ≤ S[p_b] *)
Theorem req_max_entropy_is_boltzmann :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (energy_expectation p) (energy_expectation boltzmann_dist) ->
    le (entropy_dist p Hp) (entropy_dist boltzmann_dist req_boltzmann_positive).
Proof.
  intros p Hp Hnp Henergy.
  assert (Hdef : req (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                (entropy_dist p Hp))
                     (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_entropy_deficit_kl p Hp Hnp Henergy).
  assert (Hkl : le zero (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_gibbs_inequality p boltzmann_dist Hp req_boltzmann_positive
                                   Hnp req_boltzmann_normalized).
  assert (Hnonneg : le zero (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                       (entropy_dist p Hp)))
    by exact (le_id_r zero (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive)
                       (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                  (entropy_dist p Hp))
                       (req_sym _ _ Hdef) Hkl).
  apply (le_id_r (entropy_dist p Hp)
                 (plus (entropy_dist p Hp)
                       (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                  (entropy_dist p Hp)))
                 (entropy_dist boltzmann_dist req_boltzmann_positive)).
  - exact (req_minus_plus_cancel (entropy_dist p Hp)
                                 (entropy_dist boltzmann_dist req_boltzmann_positive)).
  - exact (req_le_plus_nonneg_r (entropy_dist p Hp)
                                (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                           (entropy_dist p Hp))
                                Hnonneg).
Qed.

(* Id entropy_max_unique @17653：同能量且同熵 ⟹ p == p_b 逐点（唯一性 4 件之三） *)
Theorem req_entropy_max_unique :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (energy_expectation p) (energy_expectation boltzmann_dist) ->
    req (entropy_dist p Hp) (entropy_dist boltzmann_dist req_boltzmann_positive) ->
    forall s : S, req (p s) (boltzmann_dist s).
Proof.
  intros p Hp Hnp Henergy Hent s.
  assert (Hdef : req (req_minus (entropy_dist boltzmann_dist req_boltzmann_positive)
                                (entropy_dist p Hp))
                     (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_entropy_deficit_kl p Hp Hnp Henergy).
  assert (Hkl0 : req (req_relative_entropy p boltzmann_dist Hp req_boltzmann_positive) zero).
  { exact (req_trans _ _ _ (req_sym _ _ Hdef)
                           (req_minus_self_zero (entropy_dist boltzmann_dist req_boltzmann_positive)
                                                (entropy_dist p Hp)
                                                (req_sym _ _ Hent))). }
  exact (req_gibbs_equality p boltzmann_dist Hp req_boltzmann_positive
                            Hnp req_boltzmann_normalized Hkl0 s).
Qed.

(* Id cross_entropy_decomp @18094：H(p,q) == S[p] + KL(p‖q)。
   逐点 p·(−log q) == p·(−log p) + p·(log p − log q)（distrib+assoc+opp 抵消），
   fsum_ext + fsum_add 收口。 *)
Theorem req_cross_entropy_decomp :
  forall (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q),
    req (cross_entropy p q Hq)
        (plus (entropy_dist p Hp) (req_relative_entropy p q Hp Hq)).
Proof.
  intros p q Hp Hq. unfold cross_entropy, entropy_dist, req_relative_entropy.
  assert (Hpt : forall s : S,
            req (mult (p s) (opp (log (q s) (Hq s))))
                (plus (mult (p s) (opp (log (p s) (Hp s))))
                      (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))).
  { intro s.
    assert (Hz : req (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (mult (p s) (log (p s) (Hp s)))) zero)
      by exact (req_trans _ _ _
                  (req_plus_compat (mult (p s) (opp (log (p s) (Hp s))))
                                   (opp (mult (p s) (log (p s) (Hp s))))
                                   (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (log (p s) (Hp s)))
                                   (req_opp_mult_l (p s) (log (p s) (Hp s)))
                                   (req_refl (mult (p s) (log (p s) (Hp s)))))
                  (req_trans _ _ _
                    (plus_comm (opp (mult (p s) (log (p s) (Hp s))))
                               (mult (p s) (log (p s) (Hp s))))
                    (plus_opp (mult (p s) (log (p s) (Hp s)))))).
    apply (req_sym (plus (mult (p s) (opp (log (p s) (Hp s))))
                         (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                   (mult (p s) (opp (log (q s) (Hq s))))).
    apply (req_trans (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                     (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (plus (mult (p s) (log (p s) (Hp s)))
                                 (mult (p s) (opp (log (q s) (Hq s))))))
                     (mult (p s) (opp (log (q s) (Hq s))))).
    - exact (req_plus_compat (mult (p s) (opp (log (p s) (Hp s))))
                             (mult (p s) (opp (log (p s) (Hp s))))
                             (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                             (plus (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (opp (log (q s) (Hq s)))))
                             (req_refl (mult (p s) (opp (log (p s) (Hp s)))))
                             (distrib (p s) (log (p s) (Hp s)) (opp (log (q s) (Hq s))))).
    - apply (req_trans (plus (mult (p s) (opp (log (p s) (Hp s))))
                             (plus (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (opp (log (q s) (Hq s))))))
                       (plus (plus (mult (p s) (opp (log (p s) (Hp s))))
                                   (mult (p s) (log (p s) (Hp s))))
                             (mult (p s) (opp (log (q s) (Hq s)))))
                       (mult (p s) (opp (log (q s) (Hq s))))).
      + exact (plus_assoc (mult (p s) (opp (log (p s) (Hp s))))
                          (mult (p s) (log (p s) (Hp s)))
                          (mult (p s) (opp (log (q s) (Hq s))))).
      + apply (req_trans (plus (plus (mult (p s) (opp (log (p s) (Hp s))))
                                     (mult (p s) (log (p s) (Hp s))))
                               (mult (p s) (opp (log (q s) (Hq s)))))
                         (plus zero (mult (p s) (opp (log (q s) (Hq s)))))
                         (mult (p s) (opp (log (q s) (Hq s))))).
        * exact (req_plus_compat (plus (mult (p s) (opp (log (p s) (Hp s))))
                                       (mult (p s) (log (p s) (Hp s))))
                                 zero
                                 (mult (p s) (opp (log (q s) (Hq s))))
                                 (mult (p s) (opp (log (q s) (Hq s))))
                                 Hz
                                 (req_refl (mult (p s) (opp (log (q s) (Hq s)))))).
        * exact (req_trans (plus zero (mult (p s) (opp (log (q s) (Hq s)))))
                           (plus (mult (p s) (opp (log (q s) (Hq s)))) zero)
                           (mult (p s) (opp (log (q s) (Hq s))))
                           (plus_comm zero (mult (p s) (opp (log (q s) (Hq s)))))
                           (plus_zero (mult (p s) (opp (log (q s) (Hq s)))))).
  }
  apply (req_trans (sumf (fun s => mult (p s) (opp (log (q s) (Hq s)))))
                   (sumf (fun s => plus (mult (p s) (opp (log (p s) (Hp s))))
                                        (mult (p s) (req_minus (log (p s) (Hp s))
                                                               (log (q s) (Hq s))))))
                   (plus (sumf (fun s => mult (p s) (opp (log (p s) (Hp s)))))
                         (sumf (fun s => mult (p s)
                                              (req_minus (log (p s) (Hp s))
                                                         (log (q s) (Hq s))))))).
  - exact (fsum_ext _ _ Hpt).
  - exact (fsum_add _ _).
Qed.

(* 局部引理：共同被加项消去 minus (A+B) (A+C) == minus B C
   （Id minus_plus_common_local；req 系经 req_plus_swap_mid + req_opp_plus） *)
Lemma req_minus_plus_common_local : forall A B C : R,
  req (req_minus (plus A B) (plus A C)) (req_minus B C).
Proof.
  intros A B C. unfold req_minus.
  apply (req_trans (plus (plus A B) (opp (plus A C)))
                   (plus (plus A B) (plus (opp A) (opp C)))
                   (plus B (opp C))).
  - exact (req_plus_compat (plus A B) (plus A B)
                           (opp (plus A C)) (plus (opp A) (opp C))
                           (req_refl (plus A B)) (req_opp_plus A C)).
  - apply (req_trans (plus (plus A B) (plus (opp A) (opp C)))
                     (plus (plus A (opp A)) (plus B (opp C)))
                     (plus B (opp C))).
    + exact (req_plus_swap_mid A B (opp A) (opp C)).
    + apply (req_trans (plus (plus A (opp A)) (plus B (opp C)))
                       (plus zero (plus B (opp C)))
                       (plus B (opp C))).
      * exact (req_plus_compat (plus A (opp A)) zero
                               (plus B (opp C)) (plus B (opp C))
                               (plus_opp A) (req_refl (plus B (opp C)))).
      * exact (req_trans (plus zero (plus B (opp C)))
                         (plus (plus B (opp C)) zero)
                         (plus B (opp C))
                         (plus_comm zero (plus B (opp C)))
                         (req_plus_zero_r (plus B (opp C)))).
Qed.

(* Id cross_entropy_minus_self：H(p,q) − H(p,p) == KL(p‖q)（训练目标 KL 等价核心） *)
Theorem req_cross_entropy_minus_self :
  forall (p q : S -> R) (Hp : positive_dist p) (Hq : positive_dist q),
    req (req_minus (cross_entropy p q Hq) (cross_entropy p p Hp))
       (req_relative_entropy p q Hp Hq).
Proof.
  intros p q Hp Hq.
  assert (H1 : req (cross_entropy p q Hq)
                   (plus (entropy_dist p Hp) (req_relative_entropy p q Hp Hq)))
    by exact (req_cross_entropy_decomp p q Hp Hq).
  assert (H2 : req (cross_entropy p p Hp) (entropy_dist p Hp)).
  { apply (req_trans (cross_entropy p p Hp)
                     (plus (entropy_dist p Hp) (req_relative_entropy p p Hp Hp))
                     (entropy_dist p Hp)).
    - exact (req_cross_entropy_decomp p p Hp Hp).
    - apply (req_trans (plus (entropy_dist p Hp) (req_relative_entropy p p Hp Hp))
                       (plus (entropy_dist p Hp) zero)
                       (entropy_dist p Hp)).
      + exact (req_plus_compat _ _ _ _ (req_refl (entropy_dist p Hp))
                                      (req_relative_entropy_self_zero p Hp)).
      + exact (req_plus_zero_r (entropy_dist p Hp)). }
  apply (req_trans (req_minus (cross_entropy p q Hq) (cross_entropy p p Hp))
                   (req_minus (plus (entropy_dist p Hp)
                                    (req_relative_entropy p q Hp Hq))
                              (entropy_dist p Hp))
                   (req_relative_entropy p q Hp Hq)).
  - exact (reqd_minus_compat (cross_entropy p q Hq)
                             (plus (entropy_dist p Hp)
                                   (req_relative_entropy p q Hp Hq))
                             (cross_entropy p p Hp)
                             (entropy_dist p Hp)
                             H1 H2).
  - exact (req_minus_plus_cancel_r (entropy_dist p Hp)
                                   (req_relative_entropy p q Hp Hq)).
Qed.

(* Id training_equivalence @18657：交叉熵下降 ⟹ KL 下降（固定目标 p）
   【req 无条件形态】差分恒等式 + 共同项消去 + 非负差链。 *)
Theorem req_training_equivalence :
  forall (p q1 q2 : S -> R) (Hp : positive_dist p)
         (Hq1 : positive_dist q1) (Hq2 : positive_dist q2),
    le (cross_entropy p q2 Hq2) (cross_entropy p q1 Hq1) ->
    le (req_relative_entropy p q2 Hp Hq2) (req_relative_entropy p q1 Hp Hq1).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hce.
  assert (H1d : req (cross_entropy p q1 Hq1)
                    (plus (entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1)))
    by exact (req_cross_entropy_decomp p q1 Hp Hq1).
  assert (H2d : req (cross_entropy p q2 Hq2)
                    (plus (entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2)))
    by exact (req_cross_entropy_decomp p q2 Hp Hq2).
  (* 差分恒等：H2 − H1 == KL2 − KL1 *)
  assert (Hdiff : req (req_minus (cross_entropy p q2 Hq2) (cross_entropy p q1 Hq1))
                      (req_minus (req_relative_entropy p q2 Hp Hq2)
                                 (req_relative_entropy p q1 Hp Hq1))).
  { apply (req_trans (req_minus (cross_entropy p q2 Hq2) (cross_entropy p q1 Hq1))
                     (req_minus (plus (entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2))
                                (plus (entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1)))
                     (req_minus (req_relative_entropy p q2 Hp Hq2)
                                (req_relative_entropy p q1 Hp Hq1))).
    - exact (reqd_minus_compat _ _ _ _ H2d H1d).
    - exact (req_minus_plus_common_local (entropy_dist p Hp)
                                         (req_relative_entropy p q2 Hp Hq2)
                                         (req_relative_entropy p q1 Hp Hq1)). }
  (* 同型：H1 − H2 == KL1 − KL2 *)
  assert (Hdiff' : req (req_minus (cross_entropy p q1 Hq1) (cross_entropy p q2 Hq2))
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2))).
  { apply (req_trans (req_minus (cross_entropy p q1 Hq1) (cross_entropy p q2 Hq2))
                     (req_minus (plus (entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1))
                                (plus (entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2)))
                     (req_minus (req_relative_entropy p q1 Hp Hq1)
                                (req_relative_entropy p q2 Hp Hq2))).
    - exact (reqd_minus_compat _ _ _ _ H1d H2d).
    - exact (req_minus_plus_common_local (entropy_dist p Hp)
                                         (req_relative_entropy p q1 Hp Hq1)
                                         (req_relative_entropy p q2 Hp Hq2)). }
  assert (Hd : le zero (req_minus (cross_entropy p q1 Hq1) (cross_entropy p q2 Hq2)))
    by exact (req_le_minus_nonneg (cross_entropy p q2 Hq2) (cross_entropy p q1 Hq1) Hce).
  assert (Hd' : le zero (req_minus (req_relative_entropy p q1 Hp Hq1)
                                   (req_relative_entropy p q2 Hp Hq2)))
    by exact (le_id_r zero (req_minus (cross_entropy p q1 Hq1) (cross_entropy p q2 Hq2))
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2))
                       Hdiff' Hd).
  apply (le_id_r (req_relative_entropy p q2 Hp Hq2)
                 (plus (req_relative_entropy p q2 Hp Hq2)
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2)))
                 (req_relative_entropy p q1 Hp Hq1)).
  - exact (req_minus_plus_cancel (req_relative_entropy p q2 Hp Hq2)
                                 (req_relative_entropy p q1 Hp Hq1)).
  - exact (req_le_plus_nonneg_r (req_relative_entropy p q2 Hp Hq2)
                                (req_minus (req_relative_entropy p q1 Hp Hq1)
                                           (req_relative_entropy p q2 Hp Hq2))
                                Hd').
Qed.

(* ============================================================ *)
(* ELBO 族（Id elbo_lower_bound@18359 evidence_kl_decomp@18373 *)
(*          elbo_explicit@18428 elbo_tight@18520               *)
(*          evidence_gap_kl@18578）                            *)
(* ============================================================ *)

(* Id elbo_lower_bound @18359：ELBO(q) ≤ evidence（变分下界） *)
Theorem req_elbo_lower_bound :
  forall (q : S -> R) (Hq : positive_dist q), normalized q ->
    le (reqd_elbo q Hq) reqd_evidence.
Proof.
  intros q Hq Hnq. unfold reqd_elbo, reqd_evidence.
  apply (opp_le_compat (free_energy boltzmann_dist req_boltzmann_positive)
                       (free_energy q Hq)).
  exact (req_min_free_energy_is_boltzmann q Hq Hnq).
Qed.

(* Id evidence_kl_decomp @18373：evidence == ELBO(q) + D·KL(q‖p_b)
   （−F_b == −F_q + D·KL：opp 分配 + 抵消重组） *)
Theorem req_evidence_kl_decomp :
  forall (q : S -> R) (Hq : positive_dist q), normalized q ->
    req reqd_evidence
        (plus (reqd_elbo q Hq)
              (mult D (req_relative_entropy q boltzmann_dist Hq req_boltzmann_positive))).
Proof.
  intros q Hq Hnq.
  set (K := req_relative_entropy q boltzmann_dist Hq req_boltzmann_positive).
  set (Fq := free_energy q Hq).
  set (FB := free_energy boltzmann_dist req_boltzmann_positive).
  unfold reqd_evidence, reqd_elbo.
  assert (Hdecomp : req Fq (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp q Hq Hnq).
  apply (req_sym (plus (opp Fq) (mult D K)) (opp FB)).
  apply (req_trans (plus (opp Fq) (mult D K))
                   (plus (opp (plus FB (mult D K))) (mult D K))
                   (opp FB)).
  - exact (req_plus_compat (opp Fq) (opp (plus FB (mult D K)))
                           (mult D K) (mult D K)
                           (req_opp_compat Fq (plus FB (mult D K)) Hdecomp)
                           (req_refl (mult D K))).
  - apply (req_trans (plus (opp (plus FB (mult D K))) (mult D K))
                     (plus (plus (opp FB) (opp (mult D K))) (mult D K))
                     (opp FB)).
    + exact (req_plus_compat _ _ _ _ (req_opp_plus FB (mult D K)) (req_refl (mult D K))).
    + apply (req_trans (plus (plus (opp FB) (opp (mult D K))) (mult D K))
                       (plus (opp FB) (plus (opp (mult D K)) (mult D K)))
                       (opp FB)).
      * exact (req_sym _ _ (plus_assoc (opp FB) (opp (mult D K)) (mult D K))).
      * apply (req_trans (plus (opp FB) (plus (opp (mult D K)) (mult D K)))
                         (plus (opp FB) zero)
                         (opp FB)).
        -- exact (req_plus_compat (opp FB) (opp FB)
                                 (plus (opp (mult D K)) (mult D K)) zero
                                 (req_refl (opp FB))
                                 (req_trans (plus (opp (mult D K)) (mult D K))
                                            (plus (mult D K) (opp (mult D K)))
                                            zero
                                            (plus_comm (opp (mult D K)) (mult D K))
                                            (plus_opp (mult D K)))).
        -- exact (req_plus_zero_r (opp FB)).
Qed.

(* Id elbo_explicit @18428：−F[q] == −⟨E⟩_q + D·S[q] *)
Theorem req_elbo_explicit :
  forall (q : S -> R) (Hq : positive_dist q),
    req (reqd_elbo q Hq)
        (plus (opp (energy_expectation q)) (mult D (entropy_dist q Hq))).
Proof.
  intro q. intro Hq. unfold reqd_elbo, free_energy, energy_expectation.
  assert (Hml : req (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))
                    (opp (mult D (entropy_dist q Hq)))).
  { apply (req_trans (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))
                     (mult D (opp (entropy_dist q Hq)))
                     (opp (mult D (entropy_dist q Hq)))).
    - exact (req_mult_compat D D (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                             (opp (entropy_dist q Hq))
                             (req_refl D) (req_entropy_neg_sum q Hq)).
    - exact (req_opp_mult_l D (entropy_dist q Hq)). }
  apply (req_trans (opp (plus (sumf (fun s => mult (q s) (base_loss s)))
                              (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))))
                   (plus (opp (sumf (fun s => mult (q s) (base_loss s))))
                         (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))))
                   (plus (opp (sumf (fun s => mult (q s) (base_loss s))))
                         (mult D (entropy_dist q Hq)))).
  - exact (req_opp_plus (sumf (fun s => mult (q s) (base_loss s)))
                        (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - exact (req_plus_compat (opp (sumf (fun s => mult (q s) (base_loss s)))) (opp (sumf (fun s => mult (q s) (base_loss s)))) (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (mult D (entropy_dist q Hq))
                            (req_refl (opp (sumf (fun s => mult (q s) (base_loss s)))))
                            (req_trans (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (opp (opp (mult D (entropy_dist q Hq)))) (mult D (entropy_dist q Hq))
                                       (req_trans (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (opp (mult D (opp (entropy_dist q Hq)))) (opp (opp (mult D (entropy_dist q Hq))))
                                                  (req_opp_compat (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s))))) (mult D (opp (entropy_dist q Hq)))
                                                                  (req_mult_compat D D (sumf (fun s => mult (q s) (log (q s) (Hq s)))) (opp (entropy_dist q Hq)) (req_refl D)
                                                                                   (req_entropy_neg_sum q Hq)))
                                                  (req_opp_compat (mult D (opp (entropy_dist q Hq))) (opp (mult D (entropy_dist q Hq))) (req_opp_mult_l D (entropy_dist q Hq))))
                                       (req_double_neg (mult D (entropy_dist q Hq))))).
Qed.

(* Id elbo_tight @18520：ELBO[p_b] == evidence（零间隙态） *)
Theorem req_elbo_tight :
  req (reqd_elbo boltzmann_dist req_boltzmann_positive) reqd_evidence.
Proof.
  unfold reqd_elbo, reqd_evidence. apply req_refl.
Qed.
(* Id evidence_gap_kl @18578：evidence − ELBO(q) == D·KL(q‖p_b)（变分差距精确诊断） *)
Theorem req_evidence_gap_kl :
  forall (q : S -> R) (Hq : positive_dist q), normalized q ->
    req (req_minus reqd_evidence (reqd_elbo q Hq))
       (mult D (req_relative_entropy q boltzmann_dist Hq req_boltzmann_positive)).
Proof.
  intros q Hq Hnq.
  apply (req_trans (req_minus reqd_evidence (reqd_elbo q Hq))
                   (req_minus (plus (reqd_elbo q Hq)
                                    (mult D (req_relative_entropy q boltzmann_dist Hq
                                                                  req_boltzmann_positive)))
                              (reqd_elbo q Hq))
                   (mult D (req_relative_entropy q boltzmann_dist Hq req_boltzmann_positive))).
  - exact (reqd_minus_compat _ _ _ _
             (req_evidence_kl_decomp q Hq Hnq) (req_refl (reqd_elbo q Hq))).
  - exact (req_minus_plus_cancel_r (reqd_elbo q Hq)
                                   (mult D (req_relative_entropy q boltzmann_dist Hq
                                                                req_boltzmann_positive))).
Qed.


(* ============================================================ *)
(* KL 散度特化层（Id KLDivergence @24940-25010；q 固定特化；    *)
(*   P1 消解同 Id：kl_nonneg / kl_zero_iff_eq 由 Gibbs 定理特化） *)
(* ============================================================ *)
Section ReqKLDiv.
Variable qk : S -> R.
Hypothesis qk_pos : forall s : S, lt zero (qk s).
Hypothesis qk_norm : normalized qk.
Definition req_kl_divergence (p : S -> R) (Hp : positive_dist p) : R :=
  req_relative_entropy p qk Hp qk_pos.

(* Id kl_nonneg @24982 *)
Theorem req_kl_nonneg :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    le zero (req_kl_divergence p Hp).
Proof.
  intros p Hp Hnp. unfold req_kl_divergence.
  exact (req_gibbs_inequality p qk Hp qk_pos Hnp qk_norm).
Qed.

(* Id kl_zero_iff_eq @24992 *)
Theorem req_kl_zero_iff_eq :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    req (req_kl_divergence p Hp) zero -> forall s : S, req (p s) (qk s).
Proof.
  intros p Hp Hnp Hkl0 s. unfold req_kl_divergence in Hkl0.
  exact (req_gibbs_equality p qk Hp qk_pos Hnp qk_norm Hkl0 s).
Qed.
End ReqKLDiv.

(* ============================================================ *)
(* 温度层（Id T2.2 温度参数化 @17197-17810）：                  *)
(*   Z_temp 接口 + Boltzmann_temp 族 + log 分解 +               *)
(*   entropy_temp_explicit / relative_entropy_temp_decomp +     *)
(*   熵亏/最大熵/唯一性温度版（论文 2 最大熵对偶的构造收口）    *)
(* ============================================================ *)
Section ReqTemp.
Variable Z_temp : R -> R.
Hypothesis Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Lemma req_Z_temp_pos : forall (t : R) (Ht : lt zero t), lt zero (Z_temp t).
Proof.
  intros t Ht.
  apply (lt_id_r zero (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t)
                    (req_sym _ _ (Z_temp_spec t Ht))).
  exact (fsum_pos (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))
                  (fun s => exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Qed.

Definition reqd_boltzmann_dist_temp (t : R) (Ht : lt zero t) : S -> R :=
  fun s => mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Definition reqd_energy_exp_temp (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (reqd_boltzmann_dist_temp t Ht s) (base_loss s)).

Theorem reqd_boltzmann_dist_temp_normalized :
  forall (t : R) (Ht : lt zero t), normalized (reqd_boltzmann_dist_temp t Ht).
Proof.
  intros t Ht.
  apply (req_trans (sumf (fun s => mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                        (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                         (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   one).
  - exact (fsum_linear (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                       (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
  - apply (req_trans (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                           (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                     (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t))
                     one).
    + exact (req_mult_compat (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                             (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                             (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))))
                             (Z_temp t)
                             (req_refl (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                             (req_sym _ _ (Z_temp_spec t Ht))).
    + apply (req_trans (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t))
                       (mult (Z_temp t) (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                       one).
      * exact (mult_comm (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t)).
      * exact (inv_pos_correct (Z_temp t) (req_Z_temp_pos t Ht)).
Qed.

Lemma reqd_boltzmann_dist_temp_pos :
  forall (t : R) (Ht : lt zero t) (s : S), lt zero (reqd_boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht s. unfold reqd_boltzmann_dist_temp.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.

(* Id boltzmann_log_temp_decomp @17239：log p_t(s) == −log Z_t − β·e_s
   （经 dist_log_inv_one_inv + dist_log_exp_neg 接口桥——批 1 实测 setoid
   接口无 log_inv_one_inv/exp_neg 直场，故走桥；同 req_boltzmann_log_decomp 形） *)
Theorem reqd_boltzmann_log_temp_decomp :
  forall (t : R) (Ht : lt zero t) (s : S),
    req (log (reqd_boltzmann_dist_temp t Ht s) (reqd_boltzmann_dist_temp_pos t Ht s))
        (plus (opp (log (Z_temp t) (req_Z_temp_pos t Ht)))
              (opp (mult (inv_pos t Ht) (base_loss s)))).
Proof.
  intros t Ht s.
  unfold reqd_boltzmann_dist_temp, reqd_boltzmann_dist_temp_pos.
  assert (Hlm : req (log (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                        (mult_positive (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                       (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                                       (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                       (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))))
                    (plus (log (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (log (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))))).
  { apply log_mult. }
  apply (req_trans _ _ _ Hlm
         (req_plus_compat (log (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (opp (log (Z_temp t) (req_Z_temp_pos t Ht)))
                          (log (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))))
                          (opp (mult (inv_pos t Ht) (base_loss s)))
                          (dist_log_inv_one_inv (Z_temp t) (req_Z_temp_pos t Ht)
                                                (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (dist_log_exp_neg (mult (inv_pos t Ht) (base_loss s))))).
Qed.

End ReqTemp.

(* ============================================================ *)
(* 能量-交叉熵恒等式（Id energy_cross_entropy @CW219 L18162；    *)
(*   FEM 清单件，接管席 2026-09-08 夜续建）                       *)
(*   p 归一化 ⟹ E(p) == D·CE(p‖p_b) − D·log Z。                  *)
(*   逐点 req_energy_in_log_boltzmann 换形 + fsum 组装；          *)
(*   CE 侧 Σ p·log p_b == opp CE（opp_mult_l 换形 + fsum_opp）；   *)
(*   logZ 侧常数提取（fsum_linear + 归一化 + mult_one）。          *)
(* ============================================================ *)
Theorem req_energy_cross_entropy :
  forall p : S -> R,
    normalized p ->
    req (energy_expectation p)
        (plus (mult D (cross_entropy p boltzmann_dist req_boltzmann_positive))
              (opp (mult D (log Z Z_pos)))).
Proof.
  intros p Hnp.
  unfold energy_expectation, cross_entropy.
  (* 逐点：p·e == opp (D·(p·log p_b + p·logZ)) *)
  assert (Hpt : forall s : S,
    req (mult (p s) (base_loss s))
        (opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))
                           (mult (p s) (log Z Z_pos)))))).
  { intro s.
    apply (req_trans (mult (p s) (base_loss s))
                     (mult (p s) (opp (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                     (opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
    - exact (req_mult_compat (p s) (p s) (base_loss s)
               (opp (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
               (req_refl (p s)) (req_energy_in_log_boltzmann s)).
    - apply (req_trans (mult (p s) (opp (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                       (opp (mult (p s) (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                       (opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
      + exact (req_opp_mult_l (p s) (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
      + apply (req_opp_compat (mult (p s) (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                              (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))).
        apply (req_trans (mult (p s) (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                         (mult (mult D (p s)) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                         (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))).
        * apply (req_trans (mult (p s) (mult D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (mult (mult (p s) D) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                           (mult (mult D (p s)) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
          -- exact (mult_assoc (p s) D (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          -- exact (req_mult_compat (mult (p s) D) (mult D (p s))
                       (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                       (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                       (mult_comm (p s) D) (req_refl (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
        * exact (req_trans (mult (mult D (p s)) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                           (mult D (mult (p s) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                           (req_sym _ _ (mult_assoc D (p s) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (req_mult_compat D D
                              (mult (p s) (plus (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                              (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))
                              (req_refl D) (distrib (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  (* Σ 层：Σ p·e == opp (D·(Σ p·log p_b + Σ p·logZ)) *)
  assert (Hsum : req (sumf (fun s : S => mult (p s) (base_loss s)))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))))
                                        (sumf (fun s : S => mult (p s) (log Z Z_pos))))))).
  { apply (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                     (sumf (fun s : S => opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))).
    - apply (fsum_ext (fun s : S => mult (p s) (base_loss s))
                      (fun s : S => opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
      exact Hpt.
    - exact (req_trans (sumf (fun s : S => opp (mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                       (opp (sumf (fun s : S => mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                       (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))
                       (fsum_opp (fun s : S => mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                       (req_opp_compat (sumf (fun s : S => mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                       (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                       (req_trans (sumf (fun s : S => mult D (plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                                  (mult D (sumf (fun s : S => plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                                  (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                                  (fsum_linear D (fun s : S => plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                                                  (req_mult_compat D D
                                                     (sumf (fun s : S => plus (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                                                     (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))
                                                     (req_refl D)
                                                     (fsum_add (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))
                                                              (fun s : S => mult (p s) (log Z Z_pos))))))). }
  (* 预平衡 A：Σ p·log p_b == opp CE（opp_mult_l 换形 + fsum_opp + δ） *)
  assert (HA : req (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))))
                   (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))).
  { apply (req_trans (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))))
                     (sumf (fun s : S => opp (mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                     (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))).
    - apply (fsum_ext (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))
                      (fun s : S => opp (mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))).
      intro s.
      apply (req_trans (mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))
                       (mult (p s) (opp (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))
                       (opp (mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))).
      + exact (req_mult_compat (p s) (p s)
                 (log (boltzmann_dist s) (req_boltzmann_positive s))
                 (opp (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))
                 (req_refl (p s))
                 (req_sym _ _ (req_double_neg (log (boltzmann_dist s) (req_boltzmann_positive s))))).
      + exact (req_opp_mult_l (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))).
    - exact (fsum_opp (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))). }
  (* 预平衡 C：Σ p·logZ == logZ（常数提取 + 归一化） *)
  assert (HC : req (sumf (fun s : S => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
  { apply (req_trans (sumf (fun s : S => mult (p s) (log Z Z_pos)))
                     (sumf (fun s : S => mult (log Z Z_pos) (p s)))
                     (log Z Z_pos)).
    - apply (fsum_ext (fun s : S => mult (p s) (log Z Z_pos))
                      (fun s : S => mult (log Z Z_pos) (p s))).
      intro s. exact (mult_comm (p s) (log Z Z_pos)).
    - apply (req_trans (sumf (fun s : S => mult (log Z Z_pos) (p s)))
                       (mult (log Z Z_pos) (sumf p))
                       (log Z Z_pos)).
      + exact (fsum_linear (log Z Z_pos) p).
      + apply (req_trans (mult (log Z Z_pos) (sumf p))
                         (mult (log Z Z_pos) one)
                         (log Z Z_pos)).
        * exact (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one
                   (req_refl (log Z Z_pos)) Hnp).
        * exact (mult_one (log Z Z_pos)). }
  (* 收尾：opp (D·(opp CE + logZ)) == D·CE + opp (D·logZ) *)
  apply (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                   (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                                      (log Z Z_pos))))
                   (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                         (opp (mult D (log Z Z_pos))))).
  - exact (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))
                     (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))))
                     Hsum
                     (req_opp_compat (mult D (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                     (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                                     (req_mult_compat D D
                                        (plus (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))
                                        (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))
                                        (req_refl D)
                                        (req_plus_compat (sumf (fun s : S => mult (p s) (log (boltzmann_dist s) (req_boltzmann_positive s))))
                                                         (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                                                         (sumf (fun s : S => mult (p s) (log Z Z_pos)))
                                                         (log Z Z_pos)
                                                         HA
                                                         HC)))).
  - apply (req_trans (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                                        (log Z Z_pos))))
                     (opp (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                (mult D (log Z Z_pos))))
                     (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    + exact (req_opp_compat (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                            (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                  (mult D (log Z Z_pos)))
                            (req_trans (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                                       (plus (mult D (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (log Z Z_pos)))
                                       (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (log Z Z_pos)))
                                       (distrib D (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))
                                       (req_plus_compat (mult D (opp (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                                        (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                                        (mult D (log Z Z_pos))
                                                        (mult D (log Z Z_pos))
                                                        (req_opp_mult_l D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                                                        (req_refl (mult D (log Z Z_pos)))))).
    + exact (req_trans (opp (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                  (mult D (log Z Z_pos))))
                       (plus (opp (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))))
                             (opp (mult D (log Z Z_pos))))
                       (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))
                       (req_opp_plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                     (mult D (log Z Z_pos)))
                       (req_plus_compat (opp (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))))
                                        (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s))))))
                                        (opp (mult D (log Z Z_pos)))
                                        (opp (mult D (log Z Z_pos)))
                                        (req_double_neg (mult D (sumf (fun s : S => mult (p s) (opp (log (boltzmann_dist s) (req_boltzmann_positive s)))))))
                                        (req_refl (opp (mult D (log Z Z_pos)))))).
Qed.

End ReqFEP.

(* ============================================================ *)
(* 批 2 续建小节簇（稳态 / 概率分布 / 第二定律 / U2 辅件 /      *)
(*   平方根见证）——各自独立 Section，Require 锚 = 基座 + 批 1   *)
(* ============================================================ *)

(* ---- BoltzmannSteadyState（Id @15692；马尔可夫稳态） ---- *)
Section ReqSteadyState.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ssum_ext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ssum_linear : forall (a : R) (f : S -> R), req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Variable transition : S -> S -> R.
Hypothesis transition_normalization : forall s : S, req (sumf (fun s' => transition s s')) one.

Definition reqd_boltzmann_prob (s : S) : R :=
  mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).

Hypothesis detailed_balance :
  forall s s' : S,
    req (mult (reqd_boltzmann_prob s') (transition s' s))
        (mult (reqd_boltzmann_prob s) (transition s s')).

(* Id steady_state_boltzmann @15692：详细平衡 ⟹ 稳态 *)
Theorem req_steady_state_boltzmann :
  forall s : S,
    req (sumf (fun s' => mult (reqd_boltzmann_prob s') (transition s' s)))
        (reqd_boltzmann_prob s).
Proof.
  intro s.
  apply (req_trans (sumf (fun s' => mult (reqd_boltzmann_prob s') (transition s' s)))
                   (sumf (fun s' => mult (reqd_boltzmann_prob s) (transition s s')))
                   (reqd_boltzmann_prob s)).
  - exact (ssum_ext (fun s' => mult (reqd_boltzmann_prob s') (transition s' s))
                    (fun s' => mult (reqd_boltzmann_prob s) (transition s s'))
                    (fun s' => detailed_balance s s')).
  - apply (req_trans (sumf (fun s' => mult (reqd_boltzmann_prob s) (transition s s')))
                     (mult (reqd_boltzmann_prob s) (sumf (fun s' => transition s s')))
                     (reqd_boltzmann_prob s)).
    + exact (ssum_linear (reqd_boltzmann_prob s) (fun s' => transition s s')).
    + apply (req_trans (mult (reqd_boltzmann_prob s) (sumf (fun s' => transition s s')))
                       (mult (reqd_boltzmann_prob s) one)
                       (reqd_boltzmann_prob s)).
      * exact (req_mult_compat (reqd_boltzmann_prob s) (reqd_boltzmann_prob s)
                               (sumf (fun s' => transition s s')) one
                               (req_refl (reqd_boltzmann_prob s)) (transition_normalization s)).
      * exact (req_mult_one_r (reqd_boltzmann_prob s)).
Qed.
End ReqSteadyState.

(* ---- ProbDistProperties（Id @24896-24935） ---- *)
Section ReqProbDist.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis psum_linear : forall (a : R) (f : S -> R), req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis psum_add : forall f g : S -> R, req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Definition reqd_is_prob_dist (p : S -> R) : Set :=
  And (forall s : S, le zero (p s)) (req (sumf p) one).

(* Id prob_dist_sum_linear @24896 *)
Lemma req_prob_dist_sum_linear :
  forall (p : S -> R), reqd_is_prob_dist p ->
    forall a : R, req (sumf (fun s => mult a (p s))) a.
Proof.
  intros p Hp a. destruct Hp as [Hp_nonneg Hp_norm].
  apply (req_trans (sumf (fun s => mult a (p s))) (mult a (sumf p)) a).
  - exact (psum_linear a p).
  - exact (req_trans _ _ _ (req_mult_compat a a (sumf p) one (req_refl a) Hp_norm)
                           (req_mult_one_r a)).
Qed.

(* 修正注记（同 Id）：分布之和不再归一化（Σp+Σq = 2），正确的混合是
   归一化平均 inv_2·(p+q)。 *)
Theorem req_prob_dist_mix :
  forall p q : S -> R, reqd_is_prob_dist p -> reqd_is_prob_dist q ->
    reqd_is_prob_dist (fun s => mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))).
Proof.
  intros p q [Hp_nonneg Hp_norm] [Hq_nonneg Hq_norm]. unfold reqd_is_prob_dist.
  split.
  - intro s.
    assert (Hx : le zero (plus (p s) (q s))).
    { apply (le_id_l zero (plus zero zero) (plus (p s) (q s))).
      - exact (req_sym _ _ (req_plus_zero_r zero)).
      - exact (le_plus_compat zero (p s) zero (q s) (Hp_nonneg s) (Hq_nonneg s)). }
    apply (le_trans zero (mult zero (plus (p s) (q s)))
                        (mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s)))).
    + apply (le_id_l zero (mult zero (plus (p s) (q s))) (mult zero (plus (p s) (q s)))).
      * exact (req_sym _ _ (req_trans _ _ _ (mult_comm zero (plus (p s) (q s)))
                                               (mult_zero (plus (p s) (q s))))).
      * apply le_refl.
    + apply (le_mult_compat_weak zero (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))).
      * exact Hx.
      * exact (lt_le_iff zero (inv_pos (plus one one) req_two_pos)
                             (inl (inv_pos_pos (plus one one) req_two_pos))).
  - apply (req_trans (sumf (fun s => mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))))
                     (mult (inv_pos (plus one one) req_two_pos) (sumf (fun s => plus (p s) (q s))))
                     one).
    + exact (psum_linear (inv_pos (plus one one) req_two_pos) (fun s => plus (p s) (q s))).
    + apply (req_trans (mult (inv_pos (plus one one) req_two_pos) (sumf (fun s => plus (p s) (q s))))
                       (mult (inv_pos (plus one one) req_two_pos) (plus (sumf p) (sumf q)))
                       one).
      * exact (req_mult_compat (inv_pos (plus one one) req_two_pos)
                               (inv_pos (plus one one) req_two_pos)
                               (sumf (fun s => plus (p s) (q s))) (plus (sumf p) (sumf q))
                               (req_refl (inv_pos (plus one one) req_two_pos)) (psum_add p q)).
      * apply (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus (sumf p) (sumf q)))
                         (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                         one).
        -- exact (req_mult_compat (inv_pos (plus one one) req_two_pos)
                                 (inv_pos (plus one one) req_two_pos)
                                 (plus (sumf p) (sumf q)) (plus one one)
                                 (req_refl (inv_pos (plus one one) req_two_pos))
                                 (req_plus_compat (sumf p) one (sumf q) one Hp_norm Hq_norm)).
        -- exact (req_trans _ _ _ (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (inv_pos_correct (plus one one) req_two_pos)).
Qed.
End ReqProbDist.

(* ---- SecondLaw（Id @27796；签名变化：Not (Id ..) → Not (req ..)） ---- *)
Section ReqSecondLaw.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable entropy : R -> R.
Variable dynamics : R -> R.
Definition reqd_entropy_increases : Set :=
  forall x, le (entropy x) (entropy (dynamics x)).
Variable strict_entropy_increase :
  forall x, Not (req (dynamics x) x) -> lt (entropy x) (entropy (dynamics x)).
Theorem req_second_law_irreversible :
  forall x, Not (req (dynamics x) x) -> lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hneq. apply strict_entropy_increase. exact Hneq.
Qed.
End ReqSecondLaw.

(* ---- U2FixedPoint 辅件（Id @23337/23363；主体 7 件挂批 3 RLHF req 机器） ---- *)
Section ReqU2Aux.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
(* 辅助 A：两非负项之和为零 ⟹ 每项为零 *)
Lemma req_u2_nonneg_sum_zero : forall a b : R,
  le zero a -> le zero b -> req (plus a b) zero -> req a zero.
Proof.
  intros a b Ha Hb Habs.
  assert (H1 : le a (plus a b)) by exact (req_le_plus_nonneg_r a b Hb).
  assert (H2 : le a zero) by exact (le_id_r a (plus a b) zero Habs H1).
  exact (req_sym _ _ (le_antisym zero a Ha H2)).
Qed.

(* 辅助 C：(a − b) − a == −b（U2c 的 −ηA 提取） *)
Lemma req_u2_minus_minus : forall a b : R,
  req (req_minus (req_minus a b) a) (opp b).
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) (opp a))
                   (plus a (plus (opp b) (opp a)))
                   (opp b)).
  - exact (req_sym _ _ (plus_assoc a (opp b) (opp a))).
  - apply (req_trans (plus a (plus (opp b) (opp a)))
                     (plus a (plus (opp a) (opp b)))
                     (opp b)).
    + exact (req_plus_compat a a (plus (opp b) (opp a)) (plus (opp a) (opp b))
                             (req_refl a) (plus_comm (opp b) (opp a))).
    + apply (req_trans (plus a (plus (opp a) (opp b)))
                       (plus (plus a (opp a)) (opp b))
                       (opp b)).
      * exact (plus_assoc a (opp a) (opp b)).
      * apply (req_trans (plus (plus a (opp a)) (opp b))
                         (plus zero (opp b))
                         (opp b)).
        -- exact (req_plus_compat (plus a (opp a)) zero (opp b) (opp b)
                                  (plus_opp a) (req_refl (opp b))).
        -- exact (req_trans _ _ _ (plus_comm zero (opp b)) (plus_zero (opp b))).
Qed.
End ReqU2Aux.

(* ---- SqrtWitnessGeneral（Id @96548-96600；req 版自建 nat 嵌入） ---- *)
Section ReqSqrtWitness.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Fixpoint reqd_nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (reqd_nat_to_R n')
  end.

(* 加法同态 *)
Lemma reqd_nat_to_R_plus_hom : forall m n : nat,
  req (reqd_nat_to_R (m + n)%nat) (plus (reqd_nat_to_R m) (reqd_nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl. exact (req_sym _ _ (req_trans _ _ _ (plus_comm zero (reqd_nat_to_R n))
                                               (plus_zero (reqd_nat_to_R n)))).
  - simpl. exact (req_trans _ _ _ (req_plus_compat one one (reqd_nat_to_R (m + n)%nat)
                                                          (plus (reqd_nat_to_R m) (reqd_nat_to_R n))
                                                          (req_refl one) IH)
                                  (plus_assoc one (reqd_nat_to_R m) (reqd_nat_to_R n))).
Qed.

(* 乘法同态 *)
Lemma reqd_nat_to_R_mult_hom : forall m n : nat,
  req (reqd_nat_to_R (m * n)%nat) (mult (reqd_nat_to_R m) (reqd_nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl. exact (req_sym _ _ (req_trans _ _ _ (mult_comm zero (reqd_nat_to_R n))
                                               (mult_zero (reqd_nat_to_R n)))).
  - simpl.
    exact (req_trans _ _ _ (reqd_nat_to_R_plus_hom n (m * n)%nat)
           (req_trans _ _ _ (req_plus_compat (reqd_nat_to_R n) (reqd_nat_to_R n)
                                             (reqd_nat_to_R (m * n)%nat)
                                             (mult (reqd_nat_to_R m) (reqd_nat_to_R n))
                                             (req_refl (reqd_nat_to_R n)) IH)
           (req_trans _ _ _ (req_plus_compat (reqd_nat_to_R n) (mult (reqd_nat_to_R n) one)
                                             (mult (reqd_nat_to_R m) (reqd_nat_to_R n))
                                             (mult (reqd_nat_to_R n) (reqd_nat_to_R m))
                                             (req_sym _ _ (req_mult_one_r (reqd_nat_to_R n)))
                                             (mult_comm (reqd_nat_to_R m) (reqd_nat_to_R n)))
           (req_trans _ _ _ (req_sym _ _ (distrib (reqd_nat_to_R n) one (reqd_nat_to_R m)))
                            (mult_comm (reqd_nat_to_R n) (plus one (reqd_nat_to_R m))))))).
Qed.

(* 严格正性：k ≥ 1 ⟹ 0 < nat 嵌入 *)
Lemma reqd_nat_to_R_pos : forall k : nat, lt zero (reqd_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl. exact (lt_id_r zero one (plus one zero) (req_sym _ _ (req_plus_zero_r one)) one_pos).
  - simpl. exact (plus_positive one (reqd_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

Definition reqd_sqrt_witness (d r : R) : Set := req (mult r r) d.

(* 见证（字面形式）：d := r·r *)
Lemma reqd_sqrt_witness_sq : forall k : nat,
  reqd_sqrt_witness (mult (reqd_nat_to_R k) (reqd_nat_to_R k)) (reqd_nat_to_R k).
Proof. intro k. unfold reqd_sqrt_witness. apply req_refl. Qed.

(* 见证（非平凡形式）：d := nat (k·k) == nat k · nat k（乘法同态真见证） *)
Lemma reqd_sqrt_witness_nat_sq : forall k : nat,
  reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat) (reqd_nat_to_R k).
Proof. intro k. unfold reqd_sqrt_witness. exact (req_sym _ _ (reqd_nat_to_R_mult_hom k k)). Qed.
End ReqSqrtWitness.


(* ============================================================ *)
(* Section ReqAlgBridge2：批 2 余件续建（接管席 2026-09-08 夜）   *)
(*   (a) FEM 节内通用代数引理 4 件的 req 版（le 消去族/乘减右分配；*)
(*       Id 原件 @CW219 L17126/L17146/L17162/L17178——批 1 地基    *)
(*       无对应件（仅有 _l 版与正向 le_minus_nonneg），真证补齐）  *)
(*   (b) softmax 缩放-温度对偶 req 形（SqrtWitnessGeneral 余 2    *)
(*       件落位：req softmax 族定义 + 对偶 + 两实例；             *)
(*       Id 原件 scale_temp_duality@28590 scale_dual_sq_k@96603  *)
(*       scale_dual_nat_sq_k@96623）                             *)
(* ============================================================ *)
Section ReqAlgBridge2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- (a1) le 加法右消去（Id le_plus_cancel_l @17126） ---- *)
Lemma req_le_plus_cancel_l : forall a b c : R,
  le (plus a c) (plus b c) -> le a b.
Proof.
  intros a b c H.
  (* 恒等式：x == (x+c) + (opp c)（plus_zero_r + assoc + plus_opp 链） *)
  assert (Hdec : forall x : R, req x (plus (plus x c) (opp c))).
  { intro x.
    apply (req_trans x (plus x zero) (plus (plus x c) (opp c))).
    - exact (req_sym _ _ (req_plus_zero_r x)).
    - apply (req_trans (plus x zero) (plus x (plus c (opp c)))
                       (plus (plus x c) (opp c))).
      + exact (req_plus_compat x x zero (plus c (opp c)) (req_refl x)
                               (req_sym _ _ (plus_opp c))).
      + exact (plus_assoc x c (opp c)). }
  apply (le_id_l a (plus (plus a c) (opp c)) b (Hdec a)).
  apply (le_id_r (plus (plus a c) (opp c)) (plus (plus b c) (opp c)) b).
  - exact (req_sym _ _ (Hdec b)).
  - exact (le_plus_compat (plus a c) (plus b c) (opp c) (opp c) H
                          (le_refl (opp c))).
Qed.

(* ---- (a2) 减法非负的逆（Id le_minus_nonneg_rev @17146） ---- *)
Lemma req_le_minus_nonneg_rev : forall a b : R,
  le (req_minus a b) zero -> le a b.
Proof.
  intros a b H.
  (* a == (a−b) + b（req_minus δ 展开 + assoc + plus_opp_l 链） *)
  assert (Ha : req a (plus (req_minus a b) b)).
  { apply (req_trans a (plus a zero) (plus (req_minus a b) b)).
    - exact (req_sym _ _ (req_plus_zero_r a)).
    - apply (req_trans (plus a zero) (plus a (plus (opp b) b))
                       (plus (req_minus a b) b)).
      + exact (req_plus_compat a a zero (plus (opp b) b) (req_refl a)
                               (req_sym _ _ (req_plus_opp_l b))).
      + exact (plus_assoc a (opp b) b). }
  apply (le_id_l a (plus (req_minus a b) b) b Ha).
  apply (le_id_r (plus (req_minus a b) b) (plus zero b) b).
  - exact (req_trans (plus zero b) (plus b zero) b (plus_comm zero b)
                     (req_plus_zero_r b)).
  - exact (le_plus_compat (req_minus a b) zero b b H (le_refl b)).
Qed.

(* ---- (a3) 乘正数消去（Id le_mult_pos_cancel @17162） ---- *)
Lemma req_le_mult_pos_cancel : forall a c : R,
  lt zero c -> le (mult a c) zero -> le a zero.
Proof.
  intros a c Hc H.
  assert (Hic : le zero (inv_pos c Hc)).
  { apply (lt_le_iff zero (inv_pos c Hc)). left. exact (inv_pos_pos c Hc). }
  apply (le_id_l a (mult (mult a c) (inv_pos c Hc)) zero).
  - apply (req_trans a (mult a one) (mult (mult a c) (inv_pos c Hc))).
    + exact (req_sym _ _ (req_mult_one_r a)).
    + apply (req_trans (mult a one) (mult a (mult c (inv_pos c Hc)))
                       (mult (mult a c) (inv_pos c Hc))).
      * exact (req_mult_compat a a one (mult c (inv_pos c Hc)) (req_refl a)
                 (req_sym _ _ (inv_pos_correct c Hc))).
      * exact (mult_assoc a c (inv_pos c Hc)).
  - apply (le_id_r (mult (mult a c) (inv_pos c Hc))
                   (mult zero (inv_pos c Hc)) zero).
    + exact (req_trans (mult zero (inv_pos c Hc))
                       (mult (inv_pos c Hc) zero) zero
                       (mult_comm zero (inv_pos c Hc))
                       (mult_zero (inv_pos c Hc))).
    + exact (le_mult_compat_weak (mult a c) zero (inv_pos c Hc) Hic H).
Qed.

(* ---- (a4) 乘法对减法右分配（Id mult_minus_distr_r @17178；
            批 1 地基仅备 _l 版，右版真证补齐） ---- *)
Lemma req_mult_minus_distr_r : forall a b c : R,
  req (mult (req_minus a b) c) (req_minus (mult a c) (mult b c)).
Proof.
  intros a b c.
  unfold req_minus.
  apply (req_trans (mult (plus a (opp b)) c)
                   (mult c (plus a (opp b)))
                   (plus (mult a c) (opp (mult b c)))).
  - exact (mult_comm (plus a (opp b)) c).
  - apply (req_trans (mult c (plus a (opp b)))
                     (plus (mult c a) (mult c (opp b)))
                     (plus (mult a c) (opp (mult b c)))).
    + exact (distrib c a (opp b)).
    + apply (req_trans (plus (mult c a) (mult c (opp b)))
                       (plus (mult a c) (mult c (opp b)))
                       (plus (mult a c) (opp (mult b c)))).
      * exact (req_plus_compat (mult c a) (mult a c) (mult c (opp b))
                 (mult c (opp b)) (mult_comm c a) (req_refl (mult c (opp b)))).
      * exact (req_plus_compat (mult a c) (mult a c) (mult c (opp b))
                 (opp (mult b c)) (req_refl (mult a c))
                 (req_trans (mult c (opp b)) (opp (mult c b)) (opp (mult b c))
                            (req_opp_mult_l c b)
                            (req_opp_compat (mult c b) (mult b c)
                                            (mult_comm c b)))).
Qed.

(* ---- (b) softmax 缩放-温度对偶 req 形 ---- *)
(*   req softmax 族 = 基座 softmax_scaled@28455 / softmax_temp_param  *)
(*   @28511 的 setoid 重述（exp_neg 直接消费接口 exp 族；配分 =        *)
(*   Σ exp_neg(c·z)，正性证人 fsum_pos 构造内联）。                    *)
Section ReqSoftmaxDual.
(* R/RIS 继承外层 ReqAlgBridge2 Context（嵌套节禁止重名重声明） *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sumf_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sumf_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

Definition reqd_softmax_scaled (c : R) (z : S -> R) (s : S) : R :=
  mult (exp_neg (mult c (z s)))
       (inv_pos (sumf (fun s0 : S => exp_neg (mult c (z s0))))
                (sumf_pos (fun s0 : S => exp_neg (mult c (z s0)))
                          (fun s0 : S => exp_neg_pos (mult c (z s0))))).

Definition reqd_softmax_temp_param (t : R) (Ht : lt zero t) (z : S -> R) (s : S) : R :=
  mult (exp_neg (mult (inv_pos t Ht) (z s)))
       (inv_pos (sumf (fun s0 : S => exp_neg (mult (inv_pos t Ht) (z s0))))
                (sumf_pos (fun s0 : S => exp_neg (mult (inv_pos t Ht) (z s0)))
                          (fun s0 : S => exp_neg_pos (mult (inv_pos t Ht) (z s0))))).

(* 缩放-温度对偶（Id scale_temp_duality @28590）：1/t 缩放 logits 的
   softmax == 温度 t 的 softmax。req 语义下 δ 展开后两侧字面同一
   （req_refl 闭合）——与 Id 原件"unfold 后逐字相同"同阶非平凡性，
   本件验证定义性对偶在 req 语义下保持（幂等 δ 检查点）。 *)
Theorem reqd_scale_temp_duality :
  forall (t : R) (Ht : lt zero t) (z : S -> R) (s : S),
    req (reqd_softmax_scaled (inv_pos t Ht) z s)
        (reqd_softmax_temp_param t Ht z s).
Proof.
  intros t Ht z s. unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  apply req_refl.
Qed.

(* 实例 1（Id scale_dual_sq_k @96603）：d := r·r 平方见证路径；
   见证前提与 Id 原件同构（对偶本身无条件，见证仅记账）。 *)
Theorem reqd_scale_dual_sq_k :
  forall (k : nat) (z : S -> R) (s : S),
    reqd_sqrt_witness
      (mult (reqd_nat_to_R (Datatypes.S k)) (reqd_nat_to_R (Datatypes.S k)))
      (reqd_nat_to_R (Datatypes.S k)) ->
    req (reqd_softmax_scaled (inv_pos (reqd_nat_to_R (Datatypes.S k))
                                      (reqd_nat_to_R_pos k)) z s)
        (reqd_softmax_temp_param (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Proof.
  intros k z s Hw.
  exact (reqd_scale_temp_duality (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Qed.

(* 实例 2（Id scale_dual_nat_sq_k @96623）：d := nat(k·k) 非平凡见证
   路径——见证前提由 reqd_sqrt_witness_nat_sq（乘法同态真见证）满足。 *)
Theorem reqd_scale_dual_nat_sq_k :
  forall (k : nat) (z : S -> R) (s : S),
    reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat) (reqd_nat_to_R k) ->
    req (reqd_softmax_scaled (inv_pos (reqd_nat_to_R (Datatypes.S k))
                                      (reqd_nat_to_R_pos k)) z s)
        (reqd_softmax_temp_param (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Proof.
  intros k z s Hw.
  assert (Hwok : reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat)
                                   (reqd_nat_to_R k))
    by exact (reqd_sqrt_witness_nat_sq k).
  exact (reqd_scale_temp_duality (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Qed.

End ReqSoftmaxDual.
End ReqAlgBridge2.


(* ============================================================ *)
(* 批 2 清单逐条核销（接管席续建 2026-09-08 晚；接续前任席 52Qed） *)
(* -------------------------------------------------------------- *)
(* 【SumLayer+公共机器】reqd_le_of_req reqd_minus_compat reqd_inv_pos_cancel *)
(*   reqd_log_cancel reqd_le_mult_nonneg_t12 reqd_lt_mult_pos_cancel       *)
(*   reqd_plus_rot reqd_opp_zero reqd_minus_zero_r reqd_sum_opp            *)
(*   reqd_sum_minus reqd_sum_zero                                    [12]  *)
(* 【GRPO 15】req_list_sum_g_linear/add/ext/const/opp/minus                *)
(*   req_group_mean_def req_grpo_advantage_zero_mean req_grpo_square_expand*)
(*   req_grpo_variance_identity req_inv_G_absorb req_group_variance        *)
(*   req_group_variance_identity req_grpo_le_minus                         *)
(*   req_group_variance_le_raw_second_moment                          [15] *)
(* 【FEP 基座 26】req_boltzmann_positive(Defined) fsum_opp fsum_minus      *)
(*   req_boltzmann_normalized req_boltzmann_mix_normalized                 *)
(*   req_boltzmann_log_decomp reqd_log_div req_energy_in_log_boltzmann     *)
(*   fsum_pb_logZ fsum_zero fsum_norm_const req_free_energy_boltzmann      *)
(*   req_p_times_energy_decomp req_free_energy_kl_decomp                   *)
(*   req_free_energy_kl_diff req_free_energy_diff_kl                       *)
(*   req_relative_entropy_self_zero req_entropy_neg_sum                    *)
(*   req_free_energy_entropy reqd_p_times_ratio reqd_p_minus_ratio         *)
(*   reqd_minus_one_flip req_gibbs_pointwise req_gibbs_inequality          *)
(*   req_gibbs_equality req_boltzmann_dist_pos                        [26] *)
(* 【FEP 续建 13】req_min_free_energy_is_boltzmann【旗舰 req 无条件形态】   *)
(*   req_free_energy_min_unique【旗舰唯一性】 req_entropy_deficit_kl        *)
(*   req_max_entropy_is_boltzmann req_entropy_max_unique                   *)
(*   req_cross_entropy_decomp req_minus_plus_common_local                  *)
(*   req_cross_entropy_minus_self req_training_equivalence                 *)
(*   req_elbo_lower_bound req_evidence_kl_decomp req_elbo_explicit         *)
(*   req_elbo_tight(定义级) req_evidence_gap_kl                       [13] *)
(* 【KL 特化 2】req_kl_nonneg req_kl_zero_iff_eq（ReqKLDiv 节）        [2]  *)
(* 【温度层 4/9】req_Z_temp_pos reqd_boltzmann_dist_temp_normalized        *)
(*   reqd_boltzmann_dist_temp_pos(Defined) reqd_boltzmann_log_temp_decomp  *)
(*   （接口桥：dist_log_inv_one_inv + dist_log_exp_neg + log_mult 场） [4]  *)
(* 【稳态 1】req_steady_state_boltzmann（详细平衡+转移归一 req 形）    [1]  *)
(* 【概率分布 2】req_prob_dist_sum_linear req_prob_dist_mix（混合=归一平均  *)
(*   inv_2·(p+q)，同 Id 修正注记）                                    [2]  *)
(* 【第二定律 1】req_second_law_irreversible（Not(Id..)→Not(req..) 签名变化）*)
(*                                                                    [1]  *)
(* 【U2 辅件 2/3】req_u2_nonneg_sum_zero req_u2_minus_minus           [2]  *)
(* 【SqrtWitness 5/7】reqd_nat_to_R_plus_hom/mult_hom/pos                  *)
(*   reqd_sqrt_witness_sq reqd_sqrt_witness_nat_sq                    [5]  *)
(* -------------------------------------------------------------- *)
(* 【接管席三批续建 2026-09-08 夜（温度熵 5 件由并行席                     *)
(*   UpReqTempEntropy.v 承载并四关核销，本文件不重复建设）】                *)
(* 【ReqFEP 能量-交叉熵 1】req_energy_cross_entropy<-Id @18162        [1]  *)
(* 【ReqAlgBridge2 代数补件 4】req_le_plus_cancel_l<-Id @17126             *)
(*   req_le_minus_nonneg_rev<-Id @17146 req_le_mult_pos_cancel<-Id @17162  *)
(*   req_mult_minus_distr_r<-Id @17178（批 1 地基无对应件：仅有 _l 版与    *)
(*   正向 req_le_minus_nonneg，本批真证补齐；消费 Setoid 接口 req 形       *)
(*   le_id_l/le_id_r/le_plus_compat/le_mult_compat_weak 字段）        [4]  *)
(* 【ReqSoftmaxDual 对偶 3】reqd_softmax_scaled/reqd_softmax_temp_param    *)
(*   （req softmax 族定义）reqd_scale_temp_duality<-Id @28590              *)
(*   reqd_scale_dual_sq_k<-Id @96603 reqd_scale_dual_nat_sq_k<-Id @96623   *)
(*   （SqrtWitnessGeneral 余 2 件落位：幂等 δ 对偶 req_refl 闭合，         *)
(*   sq_k 见证记账 / nat_sq 见证经 reqd_sqrt_witness_nat_sq 真证）    [3]  *)
(* -------------------------------------------------------------- *)
(* 本文件合计：89 Qed + 2 Defined = 91 证明件（全部纯构造性）。            *)
(* 加上 UpReqTempEntropy.v（并行席 5 件）：批 2 簇 req 交付总量 96 件。     *)
(* 余件（精确缺口，交接批 3/批 4；对照 CW219 批 2 各节逐条 grep 实证）：    *)
(*  a) 温度严格层 5+1：variational_temp_bound(@17468) energy_exp_temp_mono *)
(*     (@17521) temp_strict_A_chain2(@17825) temp_strict_ident2(@17879)    *)
(*     energy_exp_temp_strict_mono(@18019) temp_energy_dual_closed(@17788  *)
(*     sigT 形)——组装路线：Require UpReqTempEntropy 后消费件 1（熵显式）   *)
(*     /件 2（KL 温度分解）+ 本文件 req_le_plus_cancel_l 移项链；因        *)
(*     UpReqDist 是其上游（循环依赖禁止），落位=UpReqTempEntropy 增量节    *)
(*     或批 3 文件。energy_exp_temp_mono/strict_mono 另需 inv_pos_lt_      *)
(*     compat 的 req 桥（基座 Id 件在，req 形待批 3 ReqLogBridge 扩展）。   *)
(*  b) req_u2_kl_arg2_ext：需 setoid log 兼容场（log_req_compat），基座     *)
(*     接口未提供，随批 3 ReqLogBridge 扩展落位（批 2 判词维持）。          *)
(*  c) U2 主体 7 件：依赖批 3 RLHF req 机器（pi_next/align_objective/      *)
(*     free_energy_ext），维持批 3 挂账。                                   *)
(* -------------------------------------------------------------- *)
