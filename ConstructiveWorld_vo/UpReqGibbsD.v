(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqGibbsD.v *)
(* *)
(* 目的： gibbs_inequality 槽的显式供给（UpReqDist 载体）。 *)
(* 主件： gibbsd_le_b_mult_pos_r / gibbsd_p_mult_ratio 等 ≤_B 引理族，供 gibbs_inequality 使用。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB。 *)
(* 备注： 使用链假设位 dist_log_le_linear 由 real_log_le_linear_B 显式应用（非公理面）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* ------------------------------------------------------------------ *)
(* 引擎形状核对结论（普查 §380 落点纪律执行记录）：                      *)
(*   引擎 real_log_le_linear_B @UpRealLeB:535 输出 Bishop 形序          *)
(*   real_le_b := forall eps>0, x < y+eps（Set 值）；req 层槽            *)
(*   dist_log_le_linear @UpReqDist:1029 输出接口序 le——                 *)
(*   RealEnhancedReal 实例的 le 字段 := real_le（Or 编码）。            *)
(*   桥核对：real_le_to_le_b@UpRealLeB:78 / latb_real_lt_to_le_b@       *)
(*   UpReqLatticeB:87 / real_lt_le_bridge@UpLogMono:16 均单向           *)
(*   （real_le / real_lt → real_le_b）；逆向 real_le_b → real_le 即     *)
(*   Or 形精确完成，构造性不可证（UpRealLeB 尾注登记表明示）。            *)
(*   结论：req 层槽不可由 B 形引擎无条件消解（序异向，缺逆向连接引理）；    *)
(*   按普查 §380 纪律落点升格为「Real 实例化定理」——本文件以            *)
(*   real_le_b 为序复演 req_gibbs_pointwise → req_gibbs_inequality      *)
(*   使用链，假设位 dist_log_le_linear 由 real_log_le_linear_B 显式应用。     *)
(*   模板：UpReqU2 log_req_compat_real（T2 模板 ②：显式实例显式应用）。     *)
(* ------------------------------------------------------------------ *)
(* 结果：                                                              *)
(*   [保底] gibbsd_gibbs_pointwise_B —— 逐点槽消解位：与                *)
(*     req_gibbs_pointwise 使用 dist_log_le_linear 逻辑同位，           *)
(*     real_log_le_linear_B 一次喂定；                                  *)
(*     gibbsd_gibbs_inequality —— KL ≥ 0 Bishop 形（与 E.13             *)
(*     real_gibbs_inequality_B 语句同形；E.13 走 real_gibbs_inequality_ *)

(*   [主件·级联首层] gibbsd_cross_entropy_decomp ——                    *)
(*     H(p,q) == S[p] + KL(p‖q) Real 实例化（req_cross_entropy_decomp   *)
(*     @UpReqDist:2431 对位），逐点恒等经 log 乘法分解向闭合，          *)
(*     同法使用本文件 Bishop 序机。                                     *)


(*   与之恒等需 log 逆消去（log(inv p) == −log p），未备该消去件、 *)
(*   real_eq_of_zero_diff 逐 n ring 形不适用——诚实边界，req 面同构记    *)
(*   δ 透明（UpReqDist 登记表 2「minus 非接口字段」同结论）。             *)
(* 红线：Set 层零 Prop（real_le_b / real_eq / real_lt 全 Set 值，      *)
(*   语句与证明零 Prop 泄露）；全 Qed 闭合；零公理；既有文件零改；      *)
(*   gibbsd_ 前缀全库防撞（建前 grep 实测零命中）。                     *)


(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A：Bishop 序代数基元（real_le_b 上的 opp / 数乘 / 换形）        *)
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
(* Part B：逐点槽消解前置（eq 层恒等）                                  *)
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
(* Part C：Bishop 和层机（real_list_sum 上的逐点→求和升格）             *)
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

(* 半分配：e·h + e·h == e（eps 预算对半拆分的恒等燃料） *)
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
(*   预算对半归纳：eps 拆 e/2 + e/2，nil 余量走 real_lt_plus_r_zero） *)
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
(* Part D：保底消解主体                                                 *)
(* ============================================================ *)

(* D0【槽消解位】：逐点 Gibbs 切线 p−q ≤_B p·(−log(q/p))。
   Hypothesis dist_log_le_linear（槽，10 下游）；此处显式应用
   real_log_le_linear_B（UpRealLeB:535）一次闭合，无条件。
   链：槽 log(q/p) ≤_B q/p−1 → opp 反向 → 1−q/p 换形 →
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
  (* —— 槽消解位：req 层 dist_log_le_linear 使用位，B 形引擎显式应用 —— *)
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

(* D1【保底主件】：Gibbs 不等式 Real 实例化——0 ≤_B Σ_s KL(p s‖q s)。
   req_gibbs_inequality（UpReqDist:2122，dist_log_le_linear 10 下游）
   的 Real 实例化消解：归一化前提位照抄 req 层（real_eq 形），求和层
   real_list_sum 机，序 real_le_b，假设位由 D0 逐点件填充。
   语句与 E.13 real_gibbs_inequality_B 同形：E.13 走
   real_gibbs_inequality_eps 完成路，本件走 log 切线槽消解复演路——双路互证。 *)
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
(* Part E：主件——级联首层 cross_entropy_decomp 同法消解                 *)
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
(*   （fsum_le / fsum_minus 的 Bishop 对位；预算对半归纳免除法）。      *)
(*   gibbsd_gibbs_pointwise_B —— 槽消解位（dist_log_le_linear 显式应用）。  *)

(*   gibbsd_cross_entropy_decomp —— 级联首层主件。                      *)
(*   E-GIBBSD-1：B 形引擎消解 req 层 Hypothesis 槽，序异向不可显式应用——    *)
(*   落点纪律 §380 fallback（Real 实例化定理）首次全链执行；缺口件=      *)
(*   Bishop 序代数基元 5 件 + Bishop 和单调 1 件（本文件 Part A/C      *)



(* ============================================================ *)
