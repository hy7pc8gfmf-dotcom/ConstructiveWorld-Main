(* ============================================================ *)
(* UpReqConcSoftmax.v —— SO 具体实例首切片（req 镜像系·柯西 Real 面）   *)
(*                                                              *)
(* 目的：论文7 §10.2 第 7 项的无条件合龙路线①切片：在柯西 Real 上        *)
(*   为 enum 列表折叠有限和机器 csm_sumf 无条件供给 8 项性质——          *)
(*   即 req 镜像链（UpReqSampling rsq_bounded_softmax_tv_iter 签名）     *)
(*   sumf 槽六件中的五件＋缺口核心件：                                   *)
(*   csm_abs_sum_le_eps（绝对值和三角的 Bishop 逐 eps 形）。             *)
(*                                                              *)
(* 实测注记：                                              *)
(*   ① plain 形 abs_sum_le（Or 编码 le）对混合号 f 无构造性路线——        *)
(*      real_le = Or (real_lt) (real_eq)（S02 L469），|Σf| 与 Σ|f| 既     *)
(*      无正间隙也非实等，Or 两支均不可达（真墙）。故本件供 Bishop        *)
(*      逐 eps 形（+eps 余量后 Or 的 inl 支可达，S07                     *)
(*      real_metric_triangle_eps 同款口径）；下游镜像消费槽若需 plain     *)
(*      形须改槽为 eps 形（本件直供）——余切片清单为待续工作。            *)
(*   ② Id 面 System A 实例墙实锤：S01 Id 为归纳内涵等价，req 面件        *)
(*      exact 进 Id 槽型错（实测核对）。                                 *)
(*                                                              *)
(* 素材（全部只读消费）：UpReqSumD.v sumd_ 系（有限和八性质无条件化      *)
(*   先例，逐槽委派）＋S07 real_metric_triangle_eps（三角逐 eps 认证机，  *)
(*   metric 代换法）＋S07 real_abs_zero_req＋UpReqAlgebra                *)
(*   req_plus_le_lt_pos（底件）。                                       *)
(*                                                              *)
(* 非平凡性分级：                                                      *)
(*   A 自证核心（本件增量）：csm_abs_pair_tri_eps（metric 代换＋req      *)
(*      缝合）、csm_abs_list_le_eps（列表归纳＋assoc 换形缝合）；        *)
(*   B 素材消费桥（委派 sumd_ 系，非重证）：ext/linear/add/le/           *)
(*      zero_nonneg 五槽；                                              *)
(*   C 定义级保底：csm_sum_eq_list（折叠处方即列表和，req_refl）。       *)
(*                                                              *)
(* 备注：公理面自审：全件语句 Set 值（req/le/lt 均 Set 值面）；前提位     *)
(*   全显式证书参数（eps 正性等），审计应 Closed；无未证断言；           *)
(*   无非构造捷径；主件 Defined 收束。                                  *)
(* ============================================================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Open Scope Q_scope.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.

(* ============ 折叠机器与五槽委派（柯西 Real 实数面） ============ *)

Section CsmSumOver.

Variable S : Set.
Variable enum : list S.

(* 具体有限和算子：enum 列表折叠（sumd_sumf 处方的同构自持） *)
Definition csm_sumf (f : S -> Real) : Real := sumd_list_sum S f enum.

(* C 档：钥匙桥（折叠处方定义性即列表和，req_refl 保底，sumd_sum_eq_list 同款） *)
Lemma csm_sum_eq_list : forall g : S -> Real,
  req (csm_sumf g) (sumd_list_sum S g enum).
Proof. intro g. exact (req_refl (sumd_list_sum S g enum)). Qed.

(* B 档：外延槽（sumd_sum_ext 委派；csm_sumf 折叠处方可转换） *)
Lemma csm_sum_ext : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (csm_sumf f) (csm_sumf g).
Proof. intros f g H. exact (sumd_sum_ext S enum f g H). Qed.

(* B 档：数乘线性槽（sumd_sum_linear 委派） *)
Lemma csm_sum_linear : forall (a : Real) (f : S -> Real),
  req (csm_sumf (fun s : S => mult a (f s))) (mult a (csm_sumf f)).
Proof. intros a f. exact (sumd_sum_linear S enum a f). Qed.

(* B 档：可加槽（sumd_sum_add 委派） *)
Lemma csm_sum_add : forall f g : S -> Real,
  req (csm_sumf (fun s : S => plus (f s) (g s)))
      (plus (csm_sumf f) (csm_sumf g)).
Proof. intros f g. exact (sumd_sum_add S enum f g). Qed.

(* B 档：单调槽（sumd_sum_le 委派） *)
Lemma csm_sum_le : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (csm_sumf f) (csm_sumf g).
Proof. intros f g H. exact (sumd_sum_le S enum f g H). Qed.

(* B 档：非负槽（sumd_list_sum_nonneg 直供折叠形） *)
Lemma csm_sum_zero_nonneg : forall f : S -> Real,
  (forall s : S, le zero (f s)) -> le zero (csm_sumf f).
Proof. intros f H. exact (sumd_list_sum_nonneg S f enum H). Qed.

(* ============ A 档：三角核心件（本件增量） ============ *)

(* —— Route A 逐点机（real_plus/real_abs/real_zero 全透明 repr 引理） —— *)

Lemma csm_repr_plus : forall (A B : Real) (n : nat),
  projT1 (real_plus A B) n == projT1 A n + projT1 B n.
Proof. intros A B n. destruct A as [u Hu]. destruct B as [v Hv]. reflexivity. Qed.

Lemma csm_repr_abs : forall (A : Real) (n : nat),
  projT1 (real_abs A) n == Qabs (projT1 A n).
Proof. intros A n. destruct A as [u Hu]. reflexivity. Qed.

Lemma csm_repr_zero : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intro n. reflexivity. Qed.

(* 逐点三角：Qabs(Σ f)(n) ≤ (Σ |f|)(n)（纯 Q 层，逐 n 全域成立） *)
Lemma csm_abs_pointwise : forall (l : list S) (f : S -> Real) (n : nat),
  Qle (Qabs (projT1 (sumd_list_sum S f l) n))
      (projT1 (sumd_list_sum S (fun s : S => real_abs (f s)) l) n).
Proof.
  intro l. induction l as [| x t IH]; intros f n.
  - change (Qle (Qabs (projT1 real_zero n)) (projT1 real_zero n)).
    rewrite csm_repr_zero.
    change (Qle 0%Q 0%Q).
    apply Qle_refl.
  - change (Qle (Qabs (projT1 (real_plus (f x) (sumd_list_sum S f t)) n))
                (projT1 (real_plus (real_abs (f x))
                            (sumd_list_sum S (fun s : S => real_abs (f s)) t))
                     n)).
    rewrite (csm_repr_plus (f x) (sumd_list_sum S f t) n).
    rewrite (csm_repr_plus (real_abs (f x))
              (sumd_list_sum S (fun s : S => real_abs (f s)) t) n).
    rewrite (csm_repr_abs (f x) n).
    eapply Qle_trans.
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (IH f n).
Qed.

(* 列表档：|Σ_l f| < (Σ_l |f|) + eps（0 < eps；real_lt 打包，逐点 eps 边际） *)
Lemma csm_abs_list_le_eps : forall (l : list S) (f : S -> Real) (eps : Real),
  lt zero eps ->
  le (abs (sumd_list_sum S f l))
     (plus (sumd_list_sum S (fun s : S => abs (f s)) l) eps).
Proof.
  intros l f eps Heps.
  change (real_lt real_zero eps) in Heps.
  destruct Heps as [e0 [He0 [N0 HN0]]].
  change (real_le (real_abs (sumd_list_sum S f l))
                  (real_plus (sumd_list_sum S (fun s => real_abs (f s)) l) eps)).
  apply inl.
  refine (existT _ e0 _).
  split.
  - exact He0.
  - refine (existT _ N0 _).
    intros n Hn.
    assert (Hpt := csm_abs_pointwise l f n).
    remember (sumd_list_sum S (fun s => real_abs (f s)) l) as wa eqn:Hwa_def.
    remember (sumd_list_sum S f l) as uf eqn:Huf.
    destruct wa as [wb Hwb].
    destruct uf as [u Hu].
    destruct eps as [we Hwe].
    change (Qle (Qabs (u n)) (wb n)) in Hpt.
    change (QltT e0 (wb n + we n - Qabs (u n))).
    assert (H0D : Qle 0 (wb n - Qabs (u n))).
    { exact (proj1 (Qle_minus_iff (Qabs (u n)) (wb n)) Hpt). }
    apply Qlt_to_QltT.
    assert (Hltw : e0 < we n - 0) by (apply QltT_to_Qlt; exact (HN0 n Hn)).
    remember (Qabs (u n)) as qa eqn:Hqa.
    assert (HR : wb n + we n - qa == (wb n - qa) + (we n - 0)).
    { ring. }
    rewrite HR.
    apply (Qlt_le_trans e0 (we n - 0)).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + assert (HT1 : we n - 0 <= 0 + (we n - 0)).
      { exact (proj1 (@Qle_comp (0 + (we n - 0)) (we n - 0)
                        (Qplus_0_l (we n - 0))
                        (0 + (we n - 0)) (0 + (we n - 0)) (Qeq_refl _))
               (Qle_refl (0 + (we n - 0)))). }
      exact (Qle_trans _ _ _ HT1
               (Qplus_le_compat 0%Q (wb n - qa) (we n - 0) (we n - 0)
                  H0D (Qle_refl (we n - 0)))).
Qed.

(* 逐对三角（Bishop 逐 eps 形）：|x+y| ≤ |x| + |y| + eps（0 < eps）
   metric 代换法：real_metric_triangle_eps (x+y) x zero eps 认证机直供
   le (|(x+y)−zero|) (|(x+y)−x| + |x−zero| + eps)，再将 metric 形
   逐槽 req 缝合到 abs 形（|a−zero|==|a|、|(x+y)−x|==|y|、加法重排）。 *)
Lemma csm_abs_pair_tri_eps : forall x y eps : Real,
  lt zero eps ->
  le (abs (plus x y)) (plus (abs x) (plus (abs y) eps)).
Proof.
  intros x y eps Heps.
  assert (HMT : le (real_metric (plus x y) zero)
                   (plus (plus (real_metric (plus x y) x)
                               (real_metric x zero))
                         eps)).
  { exact (RealSetoid.real_metric_triangle_eps (plus x y) x zero eps Heps). }
  assert (Hopp0 : req (opp zero) zero).
  { exact (req_trans (opp zero) (plus zero (opp zero)) zero
             (req_sym (plus zero (opp zero)) (opp zero)
               (req_plus_zero_l (opp zero)))
             (plus_opp zero)). }
  assert (Hmz : forall a : Real, req (real_metric a zero) (abs a)).
  { intro a. exact (req_abs_compat (plus a (opp zero)) a
             (req_trans (plus a (opp zero)) (plus a zero) a
               (req_plus_compat a a (opp zero) zero (req_refl a) Hopp0)
               (plus_zero a))). }
  assert (Hmy : req (real_metric (plus x y) x) (abs y)).
  { change (req (abs (plus (plus x y) (opp x))) (abs y)).
    apply (req_abs_compat (plus (plus x y) (opp x)) y).
    apply (req_trans _ (plus x (plus (opp x) y))).
    - apply (req_trans _ (plus x (plus y (opp x)))).
      + exact (req_sym (plus x (plus y (opp x))) (plus (plus x y) (opp x))
                 (plus_assoc x y (opp x))).
      + exact (req_plus_compat x x (plus y (opp x)) (plus (opp x) y)
                 (req_refl x) (plus_comm y (opp x))).
    - apply (req_trans _ (plus (plus x (opp x)) y)).
      + exact (plus_assoc x (opp x) y).
      + exact (req_trans (plus (plus x (opp x)) y) (plus zero y) y
                 (req_plus_compat (plus x (opp x)) zero y y
                   (plus_opp x) (req_refl y))
                 (req_plus_zero_l y)). }
  assert (Htail1 : req (plus (plus (real_metric (plus x y) x)
                                    (real_metric x zero))
                             eps)
                       (plus (plus (abs y) (abs x)) eps)).
  { exact (req_plus_compat (plus (real_metric (plus x y) x) (real_metric x zero))
             (plus (abs y) (abs x)) eps eps
             (req_plus_compat (real_metric (plus x y) x) (abs y)
                (real_metric x zero) (abs x) Hmy (Hmz x))
             (req_refl eps)). }
  assert (Htail3 : req (plus (abs y) (plus (abs x) eps))
                       (plus (abs x) (plus (abs y) eps))).
  { exact (req_trans (plus (abs y) (plus (abs x) eps))
             (plus (plus (abs y) (abs x)) eps)
             (plus (abs x) (plus (abs y) eps))
             (plus_assoc (abs y) (abs x) eps)
             (req_trans (plus (plus (abs y) (abs x)) eps)
               (plus (plus (abs x) (abs y)) eps)
               (plus (abs x) (plus (abs y) eps))
               (req_plus_compat (plus (abs y) (abs x)) (plus (abs x) (abs y))
                 eps eps (plus_comm (abs y) (abs x)) (req_refl eps))
               (req_sym (plus (abs x) (plus (abs y) eps))
                 (plus (plus (abs x) (abs y)) eps)
                 (plus_assoc (abs x) (abs y) eps)))). }
  apply (le_trans _ (real_metric (plus x y) zero)).
  - exact (le_id_r _ _ _ (req_sym _ _ (Hmz (plus x y)))
             (le_refl (abs (plus x y)))).
  - exact (le_trans _ _ _ HMT
             (le_id_l _ _ _ Htail1
               (le_id_l _ _ _
                 (req_sym (plus (abs y) (plus (abs x) eps))
                   (plus (plus (abs y) (abs x)) eps)
                   (plus_assoc (abs y) (abs x) eps))
                 (le_id_r _ _ _ Htail3
                    (le_refl (plus (abs y) (plus (abs x) eps))))))).
Qed.

(* 主件：csm_sumf 处方的逐 eps 三角（rsq 镜像 abs_sum_le 槽的 eps 形直供） *)
Definition csm_abs_sum_le_eps : forall (f : S -> Real) (eps : Real),
  lt zero eps ->
  le (abs (csm_sumf f)) (plus (csm_sumf (fun s : S => abs (f s))) eps)
  := fun f eps Heps => csm_abs_list_le_eps enum f eps Heps.

End CsmSumOver.

(* ============ 公理面证据：新件零外部未证假设（全 Closed，前提=显式参数） ============ *)
Print Assumptions csm_sum_eq_list.
Print Assumptions csm_sum_ext.
Print Assumptions csm_sum_linear.
Print Assumptions csm_sum_add.
Print Assumptions csm_sum_le.
Print Assumptions csm_sum_zero_nonneg.
Print Assumptions csm_abs_pair_tri_eps.
Print Assumptions csm_abs_list_le_eps.
Print Assumptions csm_abs_sum_le_eps.
