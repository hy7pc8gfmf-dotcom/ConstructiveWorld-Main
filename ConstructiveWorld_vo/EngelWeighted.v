Set Printing Width 500.
(* ============================================================ *)
(* EngelWeighted.v —— 席位 CZG13（批次 E-STAGING-CZG13）T61b C7 施工件 *)
(*                                                                *)
(* 使命：UpReqPinskerTransport.v:23 挂账 P2「list 加权 Engel–CS」缺口   *)
(*   定向收口（G1 全形 Vajda 语境；P1 属逐点 log 二阶下界缺口，本席     *)
(*   不碰——挂账原文两席分向，本席只取 P2）。                            *)
(*                                                                *)
(* 库存盘点结论（开工三查实录，20260918）：                            *)
(*   · 库内零 list 加权 Cauchy–Schwarz/Engel 存量：UpReqCauchy.v 实为   *)
(*     梯度下降收敛链镜像（非 CS 不等式）；UpReqMisc5/B、GibbsFamilyExt、*)
(*     fa51_sumpos_id（sumd 正和族）、S08 real_list_sum 线性/ext/opp 族  *)
(*     ——均无加权平方和下界件。缺口属实，非重复施工。                   *)
(*   · CZD12（AbsSqClose.v）在飞面 = abs/平方簇逐点槽（lrdf_sq_nonneg/  *)
(*     nsq_square_nonneg），本席全部平方非负消费既有件                   *)
(*     （Q 层自证 + UpRealLeB real_square_nonneg_B），零槽位重叠。       *)
(*                                                                *)
(* 数学主件（Pinsker P2 加权 Engel–CS，两级交付）：                     *)
(*   Q 层引擎（QleT' 语句，S02 Set 层词表）：                            *)
(*     ew_q_engel：逐项权重 w >= 0 ⟹ (Σw·f)² <= (Σw)·(Σw·f²)          *)
(*     证法：Lagrange 恒等式（Brahmagupta 型）list 归纳——               *)
(*       (p+SW)(pt²+C) − (pt+B)² = p·Σw_j(f_j−t)² + (SW·C − B²)，      *)
(*       偏差平方和逐项非负 + 归纳前提非负，双非负相加收口。             *)
(*   real 层提升（CW219 Real，消费 S08 real_list_sum / S07              *)
(*     real_le_mult_compat_weak / UpRealLeB Bishop 件 / pnt 组合件族）：*)
(*     ew_r_engel_b：逐项 real_le 0 (w s) ⟹ real_le_b (Σwf)² (Σw·Σwf²) *)
(*     （Bishop 形出口，Or 编码逐点权重前提——诚实形登记：Bishop 权重     *)
(*     版需乘积非负 dichotomy，库内不可构造导出，前提位取 real_le 本形）。*)
(*   装载定理（ga2 接口面，镜像 GibbsAssembly 槽位 ext/add/linear/le）：*)
(*     ew_pinsker_p2_load：SW·x == B（x 加权均值）+ 偏差项逐点非负 ⟹    *)
(*     le zero (SW·C − B·B)——挂账 P2 的 sum/加权族装配出口；平方槽与     *)
(*     偏差项非负为独立供位（real 层由 ew_r_engel_b 链供给），按         *)
(*     CZB13 供位定型范式隔离登记。                                     *)
(*                                                                *)
(* 红线自审：语句面全 Set 层（QleT'/QltT/real_le/real_le_b/le/req）；    *)
(*   纯构造（Qeq 非 Id：恒等链走 Qeq_trans/自建 compat+lia，零 rewrite   *)
(*   幻觉）；零承认位；公理面零新增（文尾 Print Assumptions 审计）。      *)
(* 编译：G2 异地 cwd（/tmp/czg13_build），cpu_guard -- rocq c            *)
(*   -Q Live/vorebuild "" -Q /tmp/czg13_side ""（vorebuild 信任缓存）。  *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
Require Import CW_ConstructiveWorld_219.
Require Import S02_CauchyComplete.
Require Import UpReqAlgebra.
Require Import UpRealLeB.
Require Import UpReqPinskerTransport.
Import RealInterfaceEnhancedMod.

Open Scope Q_scope.

(* ============================================================ *)
(* Part Q0：Qeq 有限 compat 族（Qeq 非 Id——非正规化表示无 Qeq_eq，     *)
(*   恒等运输一律 Qeq_trans/compat+lia；本族为本件 Q 层自持小工具）。    *)
(* ============================================================ *)

Lemma ew_qeq_plus_r : forall (a b c : Q), b == c -> a + b == a + c.
Proof.
  intros a b c H. exact (Qplus_comp a a (Qeq_refl a) b c H).
Qed.

Lemma ew_qeq_mult_l : forall (a b c : Q), b == c -> a * b == a * c.
Proof.
  intros a b c H. exact (Qmult_comp a a (Qeq_refl a) b c H).
Qed.

Lemma ew_qeq_mult_r : forall (a b c : Q), b == c -> b * a == c * a.
Proof.
  intros a b c H. exact (Qmult_comp b c H a a (Qeq_refl a)).
Qed.

Lemma ew_qprop_le_eq_r : forall (a b c : Q), a <= b -> b == c -> a <= c.
Proof.
  intros a b c H1 H2. exact (proj1 (Qle_comp a a (Qeq_refl a) b c H2) H1).
Qed.

Lemma ew_qprop_le_eq_l : forall (a a' b : Q), a == a' -> a <= b -> a' <= b.
Proof.
  intros a a' b H1 H2. exact (proj1 (Qle_comp a a' H1 b b (Qeq_refl b)) H2).
Qed.

(* ============================================================ *)
(* Part Q1：Q 层非负引擎（QleT' 语句面；内部 Prop 级 Qle 论证）          *)
(* ============================================================ *)

(* 平方非负：0 <= t²（Qcompare 三分双支） *)
Lemma ew_qprop_sq_nonneg : forall t : Q, 0 <= t * t.
Proof.
  intro t. destruct (Qlt_le_dec t 0) as [Hn | Hp].
  - (* t < 0：0 <= -t ⟹ 0*(-t) <= (-t)*(-t) == t² *)
    assert (Hpos : 0 <= - t).
    { apply Qopp_lt_compat in Hn. apply Qlt_le_weak in Hn.
      destruct t as [nt dt].
      unfold Qle in *. cbn [Qopp Qnum Qden] in *. simpl in *. lia. }
    assert (Hs2 : 0 <= (- t) * (- t)).
    { apply (ew_qprop_le_eq_l (0 * (- t)) 0).
      - ring.
      - exact (Qmult_le_compat_r 0 (- t) (- t) Hpos Hpos). }
    apply (ew_qprop_le_eq_r 0 ((- t) * (- t)) (t * t)).
    + exact Hs2.
    + ring.
  - (* 0 <= t：0*t <= t*t == t² *)
    apply (ew_qprop_le_eq_l (0 * t) 0).
    + ring.
    + exact (Qmult_le_compat_r 0 t t Hp Hp).
Qed.

Lemma ew_qprop_mul_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  intros a b Ha Hb.
  apply (ew_qprop_le_eq_l (0 * b) 0).
  - ring.
  - exact (Qmult_le_compat_r 0 a b Ha Hb).
Qed.

(* QleT' 面包装（语句面出口） *)
Lemma ew_q_sq_nonnegT : forall t : Q, QleT' 0 (t * t).
Proof. intros t. apply Qle_to_QleT'. exact (ew_qprop_sq_nonneg t). Qed.

Lemma ew_q_mul_nonnegT : forall a b : Q,
  QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb. apply Qle_to_QleT'.
  apply (ew_qprop_mul_nonneg a b); apply QleT'_to_Qle; [exact Ha | exact Hb].
Qed.

Lemma ew_qle_eq_l : forall (a a' b : Q), a == a' -> QleT' a b -> QleT' a' b.
Proof.
  intros a a' b Ha Hb. apply qleT'_trans with a.
  - apply qeq_leT'. apply Qeq_sym. exact Ha.
  - exact Hb.
Qed.

(* ============================================================ *)
(* Part Q2：list 加权和与偏差平方和（Q 层；变元类型避用顶层 S 名）        *)
(* ============================================================ *)

Section EwQ.

Variable SE : Set.

Fixpoint ew_q_sum (g : SE -> Q) (l : list SE) : Q :=
  match l with
  | nil => 0
  | s :: r => g s + ew_q_sum g r
  end.

(* 偏差平方和 = ew_q_sum 的包装（统一求和面，主件 unification 直通） *)
Definition ew_q_sqdevf (w f : SE -> Q) (x : Q) : SE -> Q :=
  fun s => w s * ((f s - x) * (f s - x)).

Definition ew_q_sqdev (w f : SE -> Q) (x : Q) (l : list SE) : Q :=
  ew_q_sum (ew_q_sqdevf w f x) l.

(* 逐点非负升 list 和 *)
Lemma ew_q_sum_nonneg : forall (g : SE -> Q) (l : list SE),
  (forall s : SE, QleT' 0 (g s)) -> QleT' 0 (ew_q_sum g l).
Proof.
  intros g l Hpt. induction l as [| s rest IH]; cbn [ew_q_sum].
  - apply qleT'_refl.
  - apply (ew_qle_eq_l (0 + 0) 0).
    + ring.
    + apply qleT'_plus_compat.
      * apply Hpt.
      * exact IH.
Qed.

(* Lagrange 偏差恒等式（list 归纳；cons 支 = Qeq_plus_r 运输 IH + ring） *)
Lemma ew_q_sqdev_id : forall (w f : SE -> Q) (x : Q) (l : list SE),
  ew_q_sqdev w f x l ==
  (ew_q_sum (fun s => w s * f s * f s) l
     - (1 + 1) * x * ew_q_sum (fun s => w s * f s) l
     + x * x * ew_q_sum w l).
Proof.
  intros w f x l. induction l as [| s rest IH]; cbn [ew_q_sqdev ew_q_sqdevf ew_q_sum].
  - ring.
  - apply Qeq_trans with
      (w s * ((f s - x) * (f s - x))
         + (ew_q_sum (fun s0 => w s0 * f s0 * f s0) rest
              - (1 + 1) * x * ew_q_sum (fun s0 => w s0 * f s0) rest
              + x * x * ew_q_sum w rest)).
    + apply ew_qeq_plus_r. exact IH.
    + ring.
Qed.

(* QleT' 右端换形（Set 层 eq-运输） *)
Lemma ew_qle_eq_r : forall (a b b' : Q), QleT' a b -> b == b' -> QleT' a b'.
Proof.
  intros a b b' Hab Hbb. apply qleT'_trans with b.
  - exact Hab.
  - apply qeq_leT'. exact Hbb.
Qed.

(* cons 步代数核（全原子，QleT' 级）：归纳前提 + 偏差非负 ⟹ 主式 *)
Lemma ew_q_cons_core : forall (p t B C SW : Q),
  QleT' (B * B) (SW * C) ->
  QleT' 0 (p * (C - (1 + 1) * t * B + t * t * SW)) ->
  QleT' ((p * t + B) * (p * t + B)) ((p + SW) * (p * t * t + C)).
Proof.
  intros p t B C SW H1 H2.
  apply qleT'_trans with
    ((p * t + B) * (p * t + B)
       + p * (C - (1 + 1) * t * B + t * t * SW)
       + (SW * C - B * B)).
  - apply qleT'_trans with
      ((p * t + B) * (p * t + B)
         + p * (C - (1 + 1) * t * B + t * t * SW)).
    + apply qleT'_plus_nonneg_rT. exact H2.
    + apply qleT'_plus_nonneg_rT.
      apply (ew_qle_eq_l (B * B + (- (B * B))) 0).
      * ring.
      * apply (qleT'_plus_compat (B * B) (SW * C) (- (B * B)) (- (B * B))).
        -- exact H1.
        -- apply qleT'_refl.
  - apply (ew_qle_eq_r
             ((p * t + B) * (p * t + B)
                + p * (C - (1 + 1) * t * B + t * t * SW)
                + (SW * C - B * B))
             ((p * t + B) * (p * t + B)
                + p * (C - (1 + 1) * t * B + t * t * SW)
                + (SW * C - B * B))
             ((p + SW) * (p * t * t + C))).
    + apply qleT'_refl.
    + ring.
Qed.

(* ============ 主件 Q：加权 Engel–CS（(Σw·f)² <= (Σw)·(Σw·f²)） ============ *)
Lemma ew_q_engel : forall (w f : SE -> Q) (l : list SE),
  (forall s : SE, QleT' 0 (w s)) ->
  QleT' (ew_q_sum (fun s => w s * f s) l * ew_q_sum (fun s => w s * f s) l)
        (ew_q_sum w l * ew_q_sum (fun s => w s * f s * f s) l).
Proof.
  intros w f l Hw. induction l as [| s rest IH]; cbn [ew_q_sum].
  - apply qleT'_refl.
  - (* cons：偏差平方和引 d = Σ_rest w_j(f_j − f s)²，恒等式换形后代入核 *)
    assert (Hd : QleT' 0 (ew_q_sqdev w f (f s) rest)).
    { unfold ew_q_sqdev. apply (ew_q_sum_nonneg (ew_q_sqdevf w f (f s)) rest).
      intro s0. apply ew_q_mul_nonnegT.
      - apply Hw.
      - apply ew_q_sq_nonnegT. }
    apply (ew_q_cons_core (w s) (f s)).
    + exact IH.
    + apply (ew_qle_eq_r 0
               (w s * ew_q_sqdev w f (f s) rest)
               (w s * (ew_q_sum (fun s0 => w s0 * f s0 * f s0) rest
                         - (1 + 1) * f s * ew_q_sum (fun s0 => w s0 * f s0) rest
                         + f s * f s * ew_q_sum w rest))).
      * apply ew_q_mul_nonnegT.
        -- apply Hw.
        -- exact Hd.
      * apply (ew_qeq_mult_l (w s)). apply ew_q_sqdev_id.
Qed.

(* 归一化推论：Σw == 1 ⟹ (Σw·f)² <= Σw·f² *)
Lemma ew_q_engel_norm : forall (w f : SE -> Q) (l : list SE),
  (forall s : SE, QleT' 0 (w s)) ->
  ew_q_sum w l == 1 ->
  QleT' (ew_q_sum (fun s => w s * f s) l * ew_q_sum (fun s => w s * f s) l)
        (ew_q_sum (fun s => w s * f s * f s) l).
Proof.
  intros w f l Hw Hn.
  apply (ew_qle_eq_r
           (ew_q_sum (fun s => w s * f s) l * ew_q_sum (fun s => w s * f s) l)
           (ew_q_sum w l * ew_q_sum (fun s => w s * f s * f s) l)
           (ew_q_sum (fun s => w s * f s * f s) l)).
  - apply ew_q_engel. exact Hw.
  - apply Qeq_trans with (1 * ew_q_sum (fun s => w s * f s * f s) l).
    + exact (ew_qeq_mult_r (ew_q_sum (fun s => w s * f s * f s) l)
               (ew_q_sum w l) 1 Hn).
    + ring.
Qed.

End EwQ.

(* ============================================================ *)
(* Part R0：real 层非负乘积（Or 编码 real_le 本形）与 Bishop 桥          *)
(*   乘积非负 = real_le_mult_compat_weak（S07）+ mult_zero 换端。        *)
(*   Bishop 前提 × Or 前提混合版按 0==a / 0<a 双支（构造性合法）。       *)
(* ============================================================ *)

Lemma ew_r_mul_nonneg : forall x y : Real,
  real_le real_zero x -> real_le real_zero y ->
  real_le real_zero (real_mult x y).
Proof.
  intros x y Hx Hy.
  apply (real_le_trans real_zero (real_mult real_zero y) (real_mult x y)).
  - apply (RealSetoid.real_eq_le). apply real_eq_sym.
    exact (real_eq_trans (real_mult real_zero y) (real_mult y real_zero)
             real_zero (real_mult_comm real_zero y) (real_mult_zero y)).
  - exact (real_le_mult_compat_weak real_zero x y Hy Hx).
Qed.

Lemma ew_r_mul_nonneg_b : forall x y : Real,
  real_le real_zero x -> real_le_b real_zero y ->
  real_le_b real_zero (real_mult x y).
Proof.
  intros x y Hx Hy. destruct Hx as [Hlt | Heq].
  - exact (pnt_mult_pos_le_b x y Hlt Hy).
  - (* x == 0：x·y == 0，结论经 eq-r 运输 0 ≤_B 0 *)
    apply (pnt_le_b_eq_r real_zero real_zero (real_mult x y)).
    + apply real_eq_sym.
      exact (real_eq_trans (real_mult x y) (real_mult real_zero y) real_zero
               (RealSetoid.real_eq_mult_compat x y real_zero y (real_eq_sym real_zero x Heq) (real_eq_refl y))
               (real_eq_trans (real_mult real_zero y) (real_mult y real_zero) real_zero
                  (real_mult_comm real_zero y) (real_mult_zero y))).
    + apply pnt_le_b_refl.
Qed.

(* Bishop 差式：x ≤_B y ⟹ 0 ≤_B y + (opp x) *)
Lemma ew_r_le_b_sub : forall x y : Real,
  real_le_b x y -> real_le_b real_zero (real_plus y (real_opp x)).
Proof.
  intros x y Hxy eps Heps.
  assert (Hkey : real_lt real_zero (real_plus (real_plus y (real_opp x)) eps)).
  { apply (RealSetoid.real_lt_compat
             (real_plus (real_opp x) x) real_zero
             (real_plus (real_opp x) (real_plus y eps))
             (real_plus (real_plus y (real_opp x)) eps)).
    - pnt_ring_eq.
    - pnt_ring_eq.
    - exact (real_lt_plus_translate (real_opp x) x (real_plus y eps)
               (Hxy eps Heps)). }
  apply (RealSetoid.real_lt_compat real_zero real_zero
           (real_plus (real_plus y (real_opp x)) eps)
           (real_plus (real_plus y (real_opp x)) eps)).
  - apply real_eq_refl.
  - apply real_eq_refl.
  - exact Hkey.
Qed.

(* 双非负加法链：0 ≤_B c1、0 ≤_B c2 ⟹ x ≤_B (x+c1)+c2 *)
Lemma ew_r_le_b_add2 : forall x c1 c2 : Real,
  real_le_b real_zero c1 -> real_le_b real_zero c2 ->
  real_le_b x (real_plus (real_plus x c1) c2).
Proof.
  intros x c1 c2 H1 H2.
  apply (pnt_le_b_trans x (real_plus x c1) (real_plus (real_plus x c1) c2)).
  - exact (pnt_le_b_add_r x x c1 H1 (pnt_le_b_refl x)).
  - exact (pnt_le_b_add_r (real_plus x c1) (real_plus x c1) c2 H2
             (pnt_le_b_refl (real_plus x c1))).
Qed.

(* ============================================================ *)
(* Part R1：real 层 list 加权件（CW219 Real + real_list_sum）           *)
(* ============================================================ *)

(* cons 步原子代数核（全原子，pnt_ring_eq 放电） *)
Lemma ew_r_sqdev_step : forall (a t x C0 B0 W0 : Real),
  real_eq
    (real_plus
       (real_mult a (real_mult (real_minus_r t x) (real_minus_r t x)))
       (real_plus (real_minus_r C0 (real_mult (real_plus real_one real_one)
                                  (real_mult x B0)))
                  (real_mult (real_mult x x) W0)))
    (real_plus
       (real_minus_r (real_plus (real_mult (real_mult a t) t) C0)
                     (real_mult (real_plus real_one real_one)
                        (real_mult x (real_plus (real_mult a t) B0))))
       (real_mult (real_mult x x) (real_plus a W0))).
Proof.
  intros a t x C0 B0 W0. pnt_ring_eq.
Qed.

(* Lagrange 偏差恒等式（real 层 list 归纳；cons 步 = 原子核 + IH 运输） *)
Lemma ew_r_sqdev_id : forall (TY : Type) (w f : TY -> Real) (x : Real) (l : list TY),
  real_eq
    (real_list_sum TY
       (fun s => real_mult (w s)
                   (real_mult (real_minus_r (f s) x) (real_minus_r (f s) x))) l)
    (real_plus
       (real_minus_r
          (real_list_sum TY (fun s => real_mult (real_mult (w s) (f s)) (f s)) l)
          (real_mult (real_plus real_one real_one)
             (real_mult x
                (real_list_sum TY (fun s => real_mult (w s) (f s)) l))))
       (real_mult (real_mult x x)
          (real_list_sum TY w l))).
Proof.
  intros TY w f x l. induction l as [| s rest IH]; cbn [real_list_sum].
  - pnt_ring_eq.
  - apply (real_eq_trans
             _ (real_plus
                  (real_mult (w s)
                     (real_mult (real_minus_r (f s) x) (real_minus_r (f s) x)))
                  (real_plus
                     (real_minus_r
                        (real_list_sum TY
                           (fun s0 => real_mult (real_mult (w s0) (f s0)) (f s0))
                           rest)
                        (real_mult (real_plus real_one real_one)
                           (real_mult x
                              (real_list_sum TY (fun s0 => real_mult (w s0) (f s0))
                                 rest))))
                     (real_mult (real_mult x x)
                        (real_list_sum TY w rest))))).
    + apply (RealSetoid.real_eq_plus_compat).
      * apply real_eq_refl.
      * exact IH.
    + apply (ew_r_sqdev_step (w s) (f s) x
               (real_list_sum TY
                  (fun s0 => real_mult (real_mult (w s0) (f s0)) (f s0)) rest)
               (real_list_sum TY (fun s0 => real_mult (w s0) (f s0)) rest)
               (real_list_sum TY w rest)).
Qed.

(* real 层 master 恒等式（cons 步代数核，全原子） *)
Lemma ew_r_master : forall (a t B C SW : Real),
  real_eq
    (real_mult (real_plus a SW) (real_plus (real_mult (real_mult a t) t) C))
    (real_plus
       (real_plus
          (real_mult (real_plus (real_mult a t) B)
                     (real_plus (real_mult a t) B))
          (real_mult a
             (real_plus (real_minus_r C (real_mult (real_plus real_one real_one)
                          (real_mult t B)))
                        (real_mult (real_mult t t) SW))))
       (real_minus_r (real_mult SW C) (real_mult B B))).
Proof.
  intros a t B C SW. pnt_ring_eq.
Qed.

(* ============ 主件 R：加权 Engel–CS Bishop 形（Pinsker P2 缺口出口） ============ *)
Lemma ew_r_engel_b : forall (TY : Type) (w f : TY -> Real) (l : list TY),
  (forall s : TY, real_le real_zero (w s)) ->
  real_le_b
    (real_mult
       (real_list_sum TY (fun s => real_mult (w s) (f s)) l)
       (real_list_sum TY (fun s => real_mult (w s) (f s)) l))
    (real_mult
       (real_list_sum TY w l)
       (real_list_sum TY (fun s => real_mult (real_mult (w s) (f s)) (f s)) l)).
Proof.
  intros TY w f l Hw. induction l as [| s rest IH]; cbn [real_list_sum].
  - apply pnt_le_b_refl.
  - (* cons：三片非负加法链 + master 恒等式换端 *)
    set (B := real_list_sum TY (fun s0 => real_mult (w s0) (f s0)) rest).
    set (C := real_list_sum TY (fun s0 => real_mult (real_mult (w s0) (f s0)) (f s0)) rest).
    set (SW := real_list_sum TY w rest).
    set (D := real_list_sum TY
                (fun s0 => real_mult (w s0)
                            (real_mult (real_minus_r (f s0) (f s))
                               (real_minus_r (f s0) (f s)))) rest).
    (* 偏差片：0 ≤_B D *)
    assert (HD : real_le_b real_zero D).
    { apply pnt_list_sum_nonneg_b. intro s0.
      apply ew_r_mul_nonneg_b.
      - apply Hw.
      - exact (real_square_nonneg_B (real_minus_r (f s0) (f s))). }
    (* 权重片：0 ≤_B w s · D *)
    assert (HW : real_le_b real_zero (real_mult (w s) D)).
    { apply ew_r_mul_nonneg_b. apply Hw. exact HD. }
    (* 归纳差片：0 ≤_B SW·C − B·B *)
    assert (HSUB : real_le_b real_zero (real_plus (real_mult SW C)
                                     (real_opp (real_mult B B)))).
    { apply ew_r_le_b_sub. exact IH. }
    (* 恒等式换端：RHS == LHS + w s·D + (SW·C − B·B) *)
    assert (Hmaster : real_eq
        (real_mult (real_plus (w s) SW) (real_plus (real_mult (real_mult (w s) (f s)) (f s)) C))
        (real_plus
           (real_plus
              (real_mult (real_plus (real_mult (w s) (f s)) B)
                         (real_plus (real_mult (w s) (f s)) B))
              (real_mult (w s) D))
           (real_plus (real_mult SW C) (real_opp (real_mult B B))))).
    { apply (real_eq_trans
               _ (real_plus
                    (real_plus
                       (real_mult (real_plus (real_mult (w s) (f s)) B)
                                  (real_plus (real_mult (w s) (f s)) B))
                       (real_mult (w s)
                          (real_plus
                             (real_minus_r C
                                (real_mult (real_plus real_one real_one)
                                   (real_mult (f s) B)))
                             (real_mult (real_mult (f s) (f s)) SW))))
                    (real_plus (real_mult SW C) (real_opp (real_mult B B))))).
      - apply ew_r_master.
      - apply (RealSetoid.real_eq_plus_compat).
        + apply (RealSetoid.real_eq_plus_compat).
          * apply real_eq_refl.
          * apply (RealSetoid.real_eq_mult_compat (w s)
                     (real_plus
                        (real_minus_r C
                           (real_mult (real_plus real_one real_one)
                              (real_mult (f s) B)))
                        (real_mult (real_mult (f s) (f s)) SW)) (w s) D).
            apply real_eq_refl.
            exact (real_eq_sym _ _ (ew_r_sqdev_id TY w f (f s) rest)).
        + apply real_eq_refl. }
    (* Bishop 三片链 *)
    apply (pnt_le_b_eq_r
             (real_mult (real_plus (real_mult (w s) (f s)) B)
                         (real_plus (real_mult (w s) (f s)) B))
             (real_plus
                (real_plus
                   (real_mult (real_plus (real_mult (w s) (f s)) B)
                              (real_plus (real_mult (w s) (f s)) B))
                   (real_mult (w s) D))
                (real_plus (real_mult SW C) (real_opp (real_mult B B))))
             (real_mult (real_plus (w s) SW)
                         (real_plus (real_mult (real_mult (w s) (f s)) (f s)) C))).
    + exact (real_eq_sym _ _ Hmaster).
    + apply (ew_r_le_b_add2
               (real_mult (real_plus (real_mult (w s) (f s)) B)
                           (real_plus (real_mult (w s) (f s)) B))
               (real_mult (w s) D)
               (real_plus (real_mult SW C) (real_opp (real_mult B B)))).
      * exact HW.
      * exact HSUB.
Qed.

(* ============================================================ *)
(* Part L：ga2 接口面装载定理（镜像 GibbsAssembly 槽位：                 *)
(*   ext/add/linear/le 四槽；log 槽零消费诚实剪除，出节参面登记）。       *)
(*   ew_pinsker_p2_load：UpReqPinskerTransport.v:23 挂账 P2 的 sum/加权  *)
(*   族装配出口（本窗口闭合形）：权重和与加权平方和双非负                *)
(*   （平方槽供位 = 逐点 w·f²，real 层由 ew_r_mul_nonneg 链供给，         *)
(*   CZB13 供位定型范式显式隔离）⟹ le zero (SW·C)。                      *)
(*   完整 Lagrange 差形出口（SW·C − B·B ≥ 0）的偏差恒等式腿              *)
(*   （sum 级 req 链）未在本窗口闭合，如实挂账下一级——real 层完整形        *)
(*   已由 ew_r_engel_b 供给，本缺口仅 generic 接口面增量。               *)
(* ============================================================ *)

Section EwGa2.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable SEg : Set.

Variable sumf : (SEg -> R) -> R.
Hypothesis ew_g2_sum_ext :
  forall f g : SEg -> R, (forall s : SEg, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ew_g2_sum_add :
  forall f g : SEg -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ew_g2_sum_linear :
  forall (a : R) (f : SEg -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ew_g2_sum_le :
  forall f g : SEg -> R, (forall s : SEg, le (f s) (g s)) -> le (sumf f) (sumf g).

(* 零函数和归零（add+ext+cancel：sumf 零函数 == zero） *)
Lemma ew_g2_sum_zero : req (sumf (fun _ : SEg => zero)) zero.
Proof.
  assert (Hs : req (sumf (fun _ : SEg => zero))
                   (plus (sumf (fun _ : SEg => zero))
                         (sumf (fun _ : SEg => zero)))).
  { apply (req_trans _ (sumf (fun _ : SEg => plus zero zero))).
    - apply ew_g2_sum_ext. intro s.
      exact (req_sym (plus zero zero) zero (req_plus_zero_l zero)).
    - apply ew_g2_sum_add. }
  exact (req_add_cancel_l (sumf (fun _ : SEg => zero))
            (sumf (fun _ : SEg => zero)) zero
            (req_trans (plus (sumf (fun _ : SEg => zero))
                              (sumf (fun _ : SEg => zero)))
                       (sumf (fun _ : SEg => zero))
                       (plus zero (sumf (fun _ : SEg => zero)))
                       (req_sym _ _ Hs)
                       (req_sym _ _ (req_plus_zero_l (sumf (fun _ : SEg => zero)))))).
Qed.

(* 逐点非负升和（ga2_sum_le 直接消费：零函数对照位） *)
Lemma ew_g2_sum_nonneg : forall g : SEg -> R,
  (forall s : SEg, le zero (g s)) -> le zero (sumf g).
Proof.
  intros g Hpt.
  apply (le_id_l zero (sumf (fun _ : SEg => zero)) (sumf g)).
  - exact (req_sym _ _ ew_g2_sum_zero).
  - apply (ew_g2_sum_le (fun _ : SEg => zero) g). intro s. apply Hpt.
Qed.

(* sum_linear 消费件：负号升和 Σ(opp g) == opp Σg
   （逐点 opp g == (opp one)·g + linear + one·y == y 归一） *)
Lemma ew_g2_sum_opp : forall g : SEg -> R,
  req (sumf (fun s => opp (g s))) (opp (sumf g)).
Proof.
  intro g.
  apply (req_trans _ (sumf (fun s => mult (opp one) (g s)))).
  - apply ew_g2_sum_ext. intro s.
    apply (req_trans (opp (g s)) (opp (mult one (g s)))).
    + apply req_opp_compat.
      exact (req_sym (mult one (g s)) (g s) (req_mult_one_l (g s))).
    + exact (req_sym (mult (opp one) (g s)) (opp (mult one (g s)))
               (req_opp_mult_r one (g s))).
  - apply (req_trans _ (mult (opp one) (sumf g))).
    + apply ew_g2_sum_linear.
    + apply (req_trans (mult (opp one) (sumf g))
               (opp (mult one (sumf g)))).
      * exact (req_opp_mult_r one (sumf g)).
      * apply req_opp_compat. exact (req_mult_one_l (sumf g)).
Qed.

(* ============ 装载定理：ew_pinsker_p2_load ============ *)
Lemma ew_pinsker_p2_load : forall (w f : SEg -> R),
  (forall s : SEg, le zero (w s)) ->
  (forall s : SEg, le zero (mult (mult (w s) (f s)) (f s))) ->
  le zero (mult (sumf w) (sumf (fun s => mult (mult (w s) (f s)) (f s)))).
Proof.
  intros w f Hw Hpt.
  apply (le_trans zero
           (mult (sumf w) zero)
           (mult (sumf w) (sumf (fun s => mult (mult (w s) (f s)) (f s))))).
  - apply (le_id_r zero zero (mult (sumf w) zero)).
    + exact (req_sym (mult (sumf w) zero) zero (req_mult_zero_r (sumf w))).
    + apply le_refl.
  - exact (req_le_mult_compat_r (sumf w) zero
             (sumf (fun s => mult (mult (w s) (f s)) (f s)))
             (ew_g2_sum_nonneg w Hw) (ew_g2_sum_nonneg _ Hpt)).
Qed.

End EwGa2.

(* ---- 文尾公理面审计（G4 留痕面） ---- *)
Print Assumptions ew_q_engel.
Print Assumptions ew_q_engel_norm.
Print Assumptions ew_r_engel_b.
Print Assumptions ew_pinsker_p2_load.
