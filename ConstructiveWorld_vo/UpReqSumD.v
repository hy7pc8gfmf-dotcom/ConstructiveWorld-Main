(* ============================================================ *)
(* UpReqSumD.v *)
(* *)
(* 目的： B-求和族：sum_eq_list 钥匙桥实例化。 *)
(* 主件： sumd_sum_eq_list 钥匙桥与 sumd_list_sum_linear / sumd_sum_linear 线性族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： 原 Section 假设族在具体实例上全部收敛为无条件定理（纯接口字段推导，零新假设位）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqSumD.v —— B-求和族消解席 G1：sum_eq_list 钥匙桥实例化       *)
(*   + sum_ext/linear/add/opp/le/pos/zero_nonneg 一次性无条件消解    *)
(*                                                                *)
(* 钥匙：UpReqSampling.v L740 sum_eq_list（req 化，签名变化 7，      *)
(*   合规验证绿在盘）：Variable sum_eq_list : forall g, req (sumf g)     *)

(*   具体化为 enum 列表和（sumd_sumf，Definition），桥降为          *)
(*   req_refl 定义件（sumd_sum_eq_list，保底 1）；原 Section 假设族  *)
(*   sum_ext/sum_linear/sum_add/sum_pos/sum_le/sum_zero_nonneg 在    *)
(*   具体实例上全部收敛为无条件定理（纯接口字段推导，零新假设位）。  *)
(*                                                                *)

(*   接口层（R + RealInterfaceEnhancedSetoid）Set 值谓词 req/le/lt，  *)
(*   纯字段推导，不触及 real_le_b；具体 Real 实例 specialize 时接口   *)
(*   le 与 real_le_b 的同一性由 UpRealLeB real_le_to_le_b@78 单向桥   *)
(*   保证（本件零依赖）。落点 = req 层无条件定理（全接口泛函）。      *)
(*                                                                *)
(* 分级（逐件）：保底件 3：sumd_sum_eq_list / sumd_sum_ext /          *)
(*   sumd_sum_linear；主件 6：sumd_sum_add / sumd_sum_opp /           *)
(*   sumd_sum_le / sumd_sum_pos / sumd_list_sum_zero_nonneg_in /       *)
(*   sumd_sum_zero_nonneg_in（另附 head/tail 剥离腿两件）。诚实完成：   *)
(*   sum_pos 以列表头 witness 形（cons 形）+ 槽形（非空前提显式参）；    *)
(*   zero_nonneg 完成为 sumd_in s enum 诚实形（Set 层成员谓词；enum     *)
(*   无满射性数据，全称形不可证，见裁决注）。                          *)
(*                                                                *)
(* 消费面（全 Require 已认证 .vo，零改写上游）：                     *)
(*   CW_ConstructiveWorld_219：RealInterfaceEnhancedSetoid 字段       *)
(*   （req_plus_compat / distrib / le_plus_compat / lt_le_trans /      *)
(*   le_antisym / le_id_l / le_id_r / lt_le_iff / plus_zero 等）；     *)
(*   UpReqAlgebra：req_plus_exchange@1005（sum_add 换位腿）、          *)
(*   req_opp_plus@167（sum_opp 换轨腿）。                             *)
(*                                                                *)
(* 红线：Set 层语句（req/le/lt 均 Set 值谓词；非空前提之 Not 位与      *)
(*   UpReqSampling 签名变化 7 同形同阶，不放大主张）；纯项式组装       *)
(*   （req_trans 链 + compat 桥，零重写战术）；零外部未证假设，        *)
(*   尾部 Print Assumptions 新件全 Closed；既有文件零改；前缀 sumd_    *)
(*   全库防撞已核（grep 零命中）。                                    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
(* wb63 增量消费面：UpReqDist GRPO 节 req_list_sum_g_const/reqd_of_nat
   （同 Context 同语句，sum_const 换轨直连；导出名全 reqd_/req_/fsum_
   系，与本文件既有可见名零交，防撞已核）。 *)
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section SumDischarge：具体有限和实例（sumf := enum 列表和）      *)
(* ============================================================ *)
Section SumDischarge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable enum : list S.

(* 列表和机器（与 UpReqSampling bs_list_sum 同形自持，供本簇消费） *)
Fixpoint sumd_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (sumd_list_sum f t)
  end.

(* 具体有限和算子：sumf 的消解实例 *)
Definition sumd_sumf (f : S -> R) : R := sumd_list_sum f enum.

(* ============ 保底件 1：桥实例化定义件 ============ *)
(* UpReqSampling L740 桥在具体实例下降为 req_refl：sumf 定义性即列表和 *)
Lemma sumd_sum_eq_list : forall g : S -> R,
  req (sumd_sumf g) (sumd_list_sum g enum).
Proof. intro g. exact (req_refl (sumd_list_sum g enum)). Qed.

(* ============ 辅件家（消解件公共腿） ============ *)

(* lt 到 le 的单向提升（接口 lt_le_iff 的严格支；UpReqAlgebra L933 同款） *)
Lemma sumd_lt_le : forall a : R, lt zero a -> le zero a.
Proof. intros a H. exact (lt_le_iff zero a (inl H)). Qed.

(* 非负和：逐点非负则和非负（sum_pos 与 zero_nonneg 的公共腿） *)
Lemma sumd_list_sum_nonneg : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) -> le zero (sumd_list_sum f l).
Proof.
  intros f l H. induction l as [| x t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus (f x) (sumd_list_sum f t))
             (req_sym (plus zero zero) zero (plus_zero zero))
             (le_plus_compat zero (f x) zero (sumd_list_sum f t) (H x) IH)).
Qed.

(* ============ 保底件 2：sum_ext 类（普查 19 槽最大面） ============ *)
Lemma sumd_list_sum_ext : forall (f g : S -> R) (l : list S),
  (forall s : S, req (f s) (g s)) -> req (sumd_list_sum f l) (sumd_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

Lemma sumd_sum_ext : forall f g : S -> R,
  (forall s : S, req (f s) (g s)) -> req (sumd_sumf f) (sumd_sumf g).
Proof. intros f g H. exact (sumd_list_sum_ext f g enum H). Qed.

(* ============ 保底件 3：sum_linear 类（普查 17 槽） ============ *)
Lemma sumd_list_sum_linear : forall (a : R) (f : S -> R) (l : list S),
  req (sumd_list_sum (fun s : S => mult a (f s)) l) (mult a (sumd_list_sum f l)).
Proof.
  intros a f l. induction l as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x)) (sumd_list_sum (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
             (mult a (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
                (distrib a (f x) (sumd_list_sum f t)))).
Qed.

Lemma sumd_sum_linear : forall (a : R) (f : S -> R),
  req (sumd_sumf (fun s : S => mult a (f s))) (mult a (sumd_sumf f)).
Proof. intros a f. exact (sumd_list_sum_linear a f enum). Qed.

(* ============ 主件 1：sum_add 类（普查 18 槽） ============ *)
Lemma sumd_list_sum_add : forall (f g : S -> R) (l : list S),
  req (sumd_list_sum (fun s : S => plus (f s) (g s)) l)
      (plus (sumd_list_sum f l) (sumd_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                (plus (sumd_list_sum f t) (sumd_list_sum g t)))
             (plus (plus (f x) (sumd_list_sum f t))
                (plus (g x) (sumd_list_sum g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t)
                (plus (sumd_list_sum f t) (sumd_list_sum g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_plus_exchange (f x) (sumd_list_sum f t)
                (g x) (sumd_list_sum g t))).
Qed.

Lemma sumd_sum_add : forall f g : S -> R,
  req (sumd_sumf (fun s : S => plus (f s) (g s)))
      (plus (sumd_sumf f) (sumd_sumf g)).
Proof. intros f g. exact (sumd_list_sum_add f g enum). Qed.

(* ============ 主件 2：sum_opp 类（GRPO 区 opp/minus 前置） ============ *)
Lemma sumd_list_sum_opp : forall (f : S -> R) (l : list S),
  req (sumd_list_sum (fun s : S => opp (f s)) l) (opp (sumd_list_sum f l)).
Proof.
  intros f l. induction l as [| x t IH].
  - exact (req_sym (opp zero) zero
             (req_trans (opp zero) (plus zero (opp zero)) zero
                (req_sym (plus zero (opp zero)) (opp zero)
                   (req_plus_zero_l (opp zero)))
                (plus_opp zero))).
  - exact (req_trans
             (plus (opp (f x)) (sumd_list_sum (fun s : S => opp (f s)) t))
             (plus (opp (f x)) (opp (sumd_list_sum f t)))
             (opp (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (opp (f x)) (opp (f x))
                (sumd_list_sum (fun s : S => opp (f s)) t)
                (opp (sumd_list_sum f t))
                (req_refl (opp (f x))) IH)
             (req_sym (opp (plus (f x) (sumd_list_sum f t)))
                (plus (opp (f x)) (opp (sumd_list_sum f t)))
                (req_opp_plus (f x) (sumd_list_sum f t)))).
Qed.

Lemma sumd_sum_opp : forall f : S -> R,
  req (sumd_sumf (fun s : S => opp (f s))) (opp (sumd_sumf f)).
Proof. intros f. exact (sumd_list_sum_opp f enum). Qed.

(* ============ 主件 3：sum_le 类（普查 8 槽，12/16 近满） ============ *)
Lemma sumd_list_sum_le : forall (f g : S -> R) (l : list S),
  (forall s : S, le (f s) (g s)) -> le (sumd_list_sum f l) (sumd_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

Lemma sumd_sum_le : forall f g : S -> R,
  (forall s : S, le (f s) (g s)) -> le (sumd_sumf f) (sumd_sumf g).
Proof. intros f g H. exact (sumd_list_sum_le f g enum H). Qed.

(* ============ 主件 4：sum_pos 类（普查 12 槽；G3 配分函数族前置） ==== *)
(* cons 形：零 Prop，列表头 witness 直接供给（非空性的构造形态） *)
Lemma sumd_list_sum_pos_cons : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, lt zero (f s)) -> lt zero (sumd_list_sum f (x :: l)).
Proof.
  intros f x l H.
  exact (lt_le_trans zero (f x) (plus (f x) (sumd_list_sum f l)) (H x)
           (le_id_l (f x) (plus (f x) zero) (plus (f x) (sumd_list_sum f l))
              (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
              (le_plus_compat (f x) (f x) zero (sumd_list_sum f l)
                 (le_refl (f x))
                 (sumd_list_sum_nonneg f l
                    (fun s : S => sumd_lt_le (f s) (H s)))))).
Qed.

(* 槽形：非空前提显式参（与 UpReqSampling enum_nonempty 同位 datum；
   语句取 Stdlib 等词的否定位，签名变化 7 同形同阶） *)
Lemma sumd_list_sum_pos : forall (f : S -> R) (l : list S),
  Not (l = nil) -> (forall s : S, lt zero (f s)) -> lt zero (sumd_list_sum f l).
Proof.
  intros f l Hne H.
  destruct l as [| x t].
  - destruct (Hne eq_refl).
  - exact (sumd_list_sum_pos_cons f x t H).
Qed.

Lemma sumd_sum_pos : forall f : S -> R,
  Not (enum = nil) -> (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf f).
Proof. intros f Hne H. exact (sumd_list_sum_pos f enum Hne H). Qed.

(* ============ 主件 5：sum_zero_nonneg 类（普查 5 槽）诚实完成 ======== *)
(* 逐项零化：逐点非负 + 全和为零 + 成员位 ⇒ 该项为零。
   全称完成须 enum 满射（现有各节仅携带 enum_nonempty，无满射数据），
   故成员位诚实形为本实例可得的最大完成（阻塞裁决注见头注）。
   成员谓词取 Set 层自持（基座空型 + 和型），零 Prop 消去。 *)

(* Set 层成员谓词：nil 位取基座空型，cons 位取严格支/余段和型 *)
Fixpoint sumd_in (s : S) (l : list S) : Set :=
  match l with
  | nil => Empty_set
  | x :: t => (x = s) + (sumd_in s t)
  end.

(* 剥离腿 a（头项零化）：f x 非负、f x ≤ 和 = 0、0 ≤ f x ⇒ req (f x) zero *)
Lemma sumd_list_sum_zero_nonneg_head : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, le zero (f s)) -> req (sumd_list_sum f (x :: l)) zero ->
  req (f x) zero.
Proof.
  intros f x l Hnn H0.
  exact (le_antisym (f x) zero
           (le_trans (f x) (plus (f x) (sumd_list_sum f l)) zero
              (le_id_l (f x) (plus (f x) zero)
                 (plus (f x) (sumd_list_sum f l))
                 (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
                 (le_plus_compat (f x) (f x) zero (sumd_list_sum f l)
                    (le_refl (f x)) (sumd_list_sum_nonneg f l Hnn)))
              (le_id_r (plus (f x) (sumd_list_sum f l))
                 (plus (f x) (sumd_list_sum f l)) zero
                 H0 (le_refl (plus (f x) (sumd_list_sum f l)))))
           (Hnn x)).
Qed.

(* 剥离腿 b（尾段和零化）：全和为零 ⇒ 余段和为零（项位换轨后同法） *)
Lemma sumd_list_sum_zero_nonneg_tail : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, le zero (f s)) -> req (sumd_list_sum f (x :: l)) zero ->
  req (sumd_list_sum f l) zero.
Proof.
  intros f x l Hnn H0.
  exact (le_antisym (sumd_list_sum f l) zero
           (le_trans (sumd_list_sum f l) (plus (sumd_list_sum f l) (f x)) zero
              (le_id_l (sumd_list_sum f l) (plus (sumd_list_sum f l) zero)
                 (plus (sumd_list_sum f l) (f x))
                 (req_sym (plus (sumd_list_sum f l) zero)
                    (sumd_list_sum f l) (plus_zero (sumd_list_sum f l)))
                 (le_plus_compat (sumd_list_sum f l) (sumd_list_sum f l)
                    zero (f x)
                    (le_refl (sumd_list_sum f l)) (Hnn x)))
              (le_id_r (plus (sumd_list_sum f l) (f x))
                 (plus (sumd_list_sum f l) (f x)) zero
                 (req_trans (plus (sumd_list_sum f l) (f x))
                    (plus (f x) (sumd_list_sum f l)) zero
                    (plus_comm (sumd_list_sum f l) (f x)) H0)
                 (le_refl (plus (sumd_list_sum f l) (f x)))))
           (sumd_list_sum_nonneg f l Hnn)).
Qed.

(* 逐项零化主件（成员位诚实形） *)
Lemma sumd_list_sum_zero_nonneg_in : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) -> req (sumd_list_sum f l) zero ->
  forall s : S, sumd_in s l -> req (f s) zero.
Proof.
  intros f l Hnn H0.
  induction l as [| x t IH]; intros s Hs.
  - simpl in Hs. destruct Hs.
  - simpl in Hs. destruct Hs as [Heq | Ht].
    + exact (eq_rect x (fun v : S => req (f v) zero)
               (sumd_list_sum_zero_nonneg_head f x t Hnn H0) s Heq).
    + exact (IH (sumd_list_sum_zero_nonneg_tail f x t Hnn H0) s Ht).
Qed.

(* 具体有限和上的槽形完成（成员位诚实形） *)
Lemma sumd_sum_zero_nonneg_in : forall f : S -> R,
  (forall s : S, le zero (f s)) -> req (sumd_sumf f) zero ->
  forall s : S, sumd_in s enum -> req (f s) zero.
Proof.
  intros f Hnn H0 s Hs.
  exact (sumd_list_sum_zero_nonneg_in f enum Hnn H0 s Hs).
Qed.

(* ============================================================ *)

(*                                                                *)
(* ① 列表 Fubini（sum_swap/bs_swap/sum_swap_i 三槽同形一次消解）：  *)
(*   路线裁决=内层归纳，免 flatten/免配对展平——双侧展平产生同重集   *)
(*   异序清单，置换不变性须消去 Prop 型置换证据才能造 Set 值 req    *)
(*   项，Set 层不可行（E-探索结论 W1）；内层归纳 + add 分配两步即   *)
(*   闭合，零新增结构。                                            *)
(*                                                                *)
(* ② sum_const（Σc == of_nat(len)·c）：换轨实读裁决——              *)
(*   G06_BForm sumb_sum_const 系 Real 层（real_eq/real_list_sum/    *)
(*   real_mult/sumb_lenR），与本文件泛型接口层（R:Set）双名异型，    *)
(*   直连不可行（E387 判据），仅作证明结构模板；UpReqDist GRPO 节   *)
(*   req_list_sum_g_const 同 Context 同语句（reqd_of_nat 即         *)
(*   of_nat），且 reqd_list_sum_g 与 sumd_list_sum 定义性同构       *)
(*   （同 fold 形），1 步 exact 换轨直连。                          *)
(*                                                                *)
(* ③ zero_nonneg 全称形探索完成：无满射数据时全称形不可证（反模型：  *)
(*   enum=[a]、s∉enum、f s>0 且和为零——席57 结论维持）；本次结果    *)
(*   两件升格面：(a) 满射数据显式参形（消费方携带覆盖数据即得       *)
(*   全称形）；(b) 成员谓词单向桥 sumd_in→In（Set 沉降 Prop 合法    *)
(*   方向，反向 In→sumd_in 被 Prop 消去限制阻断，不主张）。         *)
(* ============================================================ *)

(* ---- ①·辅件：零函数列表和为零 ---- *)
Lemma sumd_list_sum_zero : forall l : list S,
  req (sumd_list_sum (fun _ : S => zero) l) zero.
Proof.
  intro l. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_trans (plus zero (sumd_list_sum (fun _ : S => zero) t))
                     (sumd_list_sum (fun _ : S => zero) t) zero
                     (req_plus_zero_l (sumd_list_sum (fun _ : S => zero) t)) IH).
Qed.

(* ---- ①·列表 Fubini 内层归纳主件（e 内层、l 外层全泛） ---- *)
Lemma sumd_list_sum_swap : forall (f : S -> S -> R) (e l : list S),
  req (sumd_list_sum (fun s : S => sumd_list_sum (f s) e) l)
      (sumd_list_sum (fun s' : S => sumd_list_sum (fun s : S => f s s') l) e).
Proof.
  intros f e l. induction e as [| y e' IH].
  - exact (req_trans (sumd_list_sum (fun s : S => sumd_list_sum (f s) nil) l)
                     zero
                     (sumd_list_sum (fun s' : S =>
                        sumd_list_sum (fun s : S => f s s') l) nil)
                     (sumd_list_sum_zero l)
                     (req_refl zero)).
  - exact (req_trans
             (sumd_list_sum (fun s : S =>
                plus (f s y) (sumd_list_sum (f s) e')) l)
             (plus (sumd_list_sum (fun s : S => f s y) l)
                   (sumd_list_sum (fun s : S => sumd_list_sum (f s) e') l))
             (plus (sumd_list_sum (fun s : S => f s y) l)
                   (sumd_list_sum (fun s' : S =>
                      sumd_list_sum (fun s : S => f s s') l) e'))
             (sumd_list_sum_add (fun s : S => f s y)
                                (fun s : S => sumd_list_sum (f s) e') l)
             (req_plus_compat (sumd_list_sum (fun s : S => f s y) l)
                (sumd_list_sum (fun s : S => f s y) l)
                (sumd_list_sum (fun s : S => sumd_list_sum (f s) e') l)
                (sumd_list_sum (fun s' : S =>
                   sumd_list_sum (fun s : S => f s s') l) e')
                (req_refl (sumd_list_sum (fun s : S => f s y) l))
                IH)).
Qed.

(* ---- ①·具体有限和槽形（bs_swap@Sampling727 / sum_swap_cc@125 /      *)
(*         sum_swap_i@AttnIter151 三槽同形一次消解） ---- *)
Lemma sumd_sum_swap : forall f : S -> S -> R,
  req (sumd_sumf (fun s : S => sumd_sumf (fun s' : S => f s s')))
      (sumd_sumf (fun s' : S => sumd_sumf (fun s : S => f s s'))).
Proof. intro f. exact (sumd_list_sum_swap f enum enum). Qed.

(* ---- ②·常数和坍缩（列表级）：Σc == of_nat(len)·c，换轨直连 ---- *)
Lemma sumd_sum_const : forall (c : R) (l : list S),
  req (sumd_list_sum (fun _ : S => c) l) (mult (reqd_of_nat (length l)) c).
Proof. intros c l. exact (req_list_sum_g_const S c l). Qed.

(* ---- ②·具体有限和槽形 ---- *)
Lemma sumd_sumf_const : forall c : R,
  req (sumd_sumf (fun _ : S => c)) (mult (reqd_of_nat (length enum)) c).
Proof. intro c. exact (sumd_sum_const c enum). Qed.

(* ---- ③·zero_nonneg 满射数据显式参形（全称形升格面） ---- *)
Lemma sumd_sum_zero_nonneg_surj : forall f : S -> R,
  (forall s : S, sumd_in s enum) ->
  (forall s : S, le zero (f s)) -> req (sumd_sumf f) zero ->
  forall s : S, req (f s) zero.
Proof.
  intros f Hsurj Hnn H0 s.
  exact (sumd_sum_zero_nonneg_in f Hnn H0 s (Hsurj s)).
Qed.

(* ---- ③·成员谓词单向桥（Set 沉降 Prop；反向不主张） ---- *)
Lemma sumd_in_to_In : forall (s : S) (l : list S), sumd_in s l -> In s l.
Proof.
  intros s l. induction l as [| x t IH]; intro H.
  - destruct H.
  - destruct H as [Heq | Ht].
    + left. exact Heq.
    + right. exact (IH Ht).
Qed.

End SumDischarge.

(* ============ G3 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions sumd_sum_eq_list.
Print Assumptions sumd_lt_le.
Print Assumptions sumd_list_sum_nonneg.
Print Assumptions sumd_list_sum_ext.
Print Assumptions sumd_sum_ext.
Print Assumptions sumd_list_sum_linear.
Print Assumptions sumd_sum_linear.
Print Assumptions sumd_list_sum_add.
Print Assumptions sumd_sum_add.
Print Assumptions sumd_list_sum_opp.
Print Assumptions sumd_sum_opp.
Print Assumptions sumd_list_sum_le.
Print Assumptions sumd_sum_le.
Print Assumptions sumd_list_sum_pos_cons.
Print Assumptions sumd_list_sum_pos.
Print Assumptions sumd_sum_pos.
Print Assumptions sumd_list_sum_zero_nonneg_head.
Print Assumptions sumd_list_sum_zero_nonneg_tail.
Print Assumptions sumd_list_sum_zero_nonneg_in.
Print Assumptions sumd_sum_zero_nonneg_in.
(* wb63 增量件（7） *)
Print Assumptions sumd_list_sum_zero.
Print Assumptions sumd_list_sum_swap.
Print Assumptions sumd_sum_swap.
Print Assumptions sumd_sum_const.
Print Assumptions sumd_sumf_const.
Print Assumptions sumd_sum_zero_nonneg_surj.
Print Assumptions sumd_in_to_In.
