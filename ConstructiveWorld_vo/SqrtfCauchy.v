(* ============================================================ *)
(* SqrtfCauchy.v —— 本件形式化 Newton 迭代残差序列的柯西性质：            *)
(*   残差 sfc_t n = s(z_n) 满足逐 eps 柯西判据（主件 sfc_newton_cauchy，   *)
(*   Bishop 逐 eps 形；辅件 sfc_pick_K 与 sfc_geom_tail_t）。             *)
(*                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSqrtF；          *)
(*   位 sfc_square_nonneg 证书供给节另引 AbsSqClose（asc_sq_nonneg 锚）。  *)
(*                                                              *)
(* 构造性注记：Set 层承载/零承认/可提取；残差恒等式 t_{n+1} + t_n == z_n   *)
(*   与压缩比率恒等式 2·z_{n+1}·t_{n+1} == t_n² 联立得单步半衰减           *)
(*   t_{n+1} ≤ t_n/2，几何尾和 Σ ≤ 2·t_N 一步完成。                       *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流。                             *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSqrtF.
Require Import AbsSqClose.
From Stdlib Require Import Arith Lia.
Import RealInterfaceEnhancedMod.

Section SqrtfCauchy.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let sfc_two : R := plus one one.
Let sfc_half : R := inv_pos sfc_two req_two_pos.

(* ============ §0 阿基米德幂族（假设位3 引用形） ============ *)

Fixpoint sfc_pow_half (k : nat) : R :=
  match k with
  | Datatypes.O => one
  | Datatypes.S k' => mult (sfc_pow_half k') sfc_half
  end.

(* ============ 显式假设位（五枚，全部同位先例登记） ============ *)
(* 假设位1（§8 路线 (a) 永久假设位，M2 墙；为 §8 链提供前提 + 半衰减乘子步） *)
Hypothesis sfc_square_nonneg : forall t : R, le zero (mult t t).
(* 假设位2（metric_abs 桥接假设位，对照表 :703 缺位登记；UpReqCauchy:108 同位） *)
Variable sfc_metric_abs : forall a b : R, req (metric a b) (abs (req_minus a b)).
(* 假设位3（阿基米德同位假设位，S03 arch_decay :394 的 R 层同形；QltT→lt） *)
Variable sfc_arch_decay : forall (c eps : R), le zero c -> lt zero eps ->
  sigT (fun k : nat => lt (mult c (sfc_pow_half k)) eps).
(* 假设位4（abs 锐化 eps 形假设位；Real 证明 = Or 分解：lt 支 abs_pos / eq 支 abs_zero） *)
Variable sfc_abs_le_plus_eps : forall (t : R), le zero t -> forall (eps : R),
  lt zero eps -> le (abs t) (plus t eps).
(* 假设位5（1 < 2 严格档假设位。抽象接口无 le 分解/三分律字段，one_pos+
   lt_plus_compat 双严格形只达 0 < 2，混合平移不可导出（ReqStrictOrderBridge
   闭节后假设位不独立导出：沙箱检验 not found + UpReqAlgebra:1466 注释双证）；
   Firewall-TempEntMono / E347 区 Variable 诚实前置先例同位。Real 层经
   real_lt_plus_translate 消解，见 SqrtfCauchyDischarge §A3 sfcx_lt_one_two_slot。） *)
Hypothesis Hlt_one_two : lt one sfc_two.
(* 假设位6（严格加法混合保序 lt_le 形。接口仅双严格 lt_plus_compat，混合形
   不可内证（UpReqAlgebra:1466 注释 + 沙箱检验双证）；UpReqCauchy:123
   lt_plus_compat_lt_le 同位 Variable 先例，语句逐字。Real 层经
   real_lt_plus_translate + real_le Or 分解可消解。） *)
Variable sfc_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

(* ============ §0b 常量与基础 ============ *)

Lemma sfc_two_pos : lt zero sfc_two.
Proof. exact req_two_pos. Qed.

Lemma sfc_half_pos : lt zero sfc_half.
Proof. exact (inv_pos_pos sfc_two req_two_pos). Qed.

Lemma sfc_lt_le : forall a b : R, lt a b -> le a b.
Proof.
  intros a b H. exact (lt_le_iff a b (inl H)).
Qed.

Lemma sfc_le_of_req : forall u v : R, req u v -> le u v.
Proof.
  intros u v H.
  exact (req_le_compat v u v v (req_sym u v H) (req_refl v) (le_refl v)).
Qed.

Lemma sfc_le_plus_r : forall u v : R, le zero v -> le u (plus u v).
Proof.
  intros u v H.
  exact (req_le_compat (plus u zero) u (plus u v) (plus u v)
                       (plus_zero u) (req_refl (plus u v))
                       (le_plus_compat u u zero v (le_refl u) H)).
Qed.

Lemma sfc_le_mult_l : forall c a b : R, lt zero c -> le a b ->
  le (mult c a) (mult c b).
Proof.
  intros c a b Hc H.
  exact (req_le_compat (mult a c) (mult c a) (mult b c) (mult c b)
                       (mult_comm a c) (mult_comm b c) (le_mult_compat a b c Hc H)).
Qed.

Lemma sfc_lt_zero_two : lt zero sfc_two.
Proof.
  exact req_two_pos.
Qed.

Lemma sfc_lt_one_two : lt one sfc_two.
Proof. exact Hlt_one_two. Qed.

Lemma sfc_inv_one : req (inv_pos one one_pos) one.
Proof.
  apply (req_trans (inv_pos one one_pos)
                   (mult one (inv_pos one one_pos))
                   one).
  - exact (req_sym (mult one (inv_pos one one_pos))
                   (inv_pos one one_pos) (req_mult_one_l (inv_pos one one_pos))).
  - exact (inv_pos_correct one one_pos).
Qed.

Lemma sfc_half_le_one : le sfc_half one.
Proof.
  apply (req_le_compat sfc_half sfc_half (inv_pos one one_pos) one
           (req_refl sfc_half) (sfc_inv_one)).
  exact (inv_pos_le_compat one sfc_two one_pos req_two_pos
           (sfc_lt_le one sfc_two sfc_lt_one_two)).
Qed.

Definition sfc_qrt : R := mult sfc_half sfc_half.

Lemma sfc_qrt_pos : lt zero sfc_qrt.
Proof. exact (mult_positive sfc_half sfc_half sfc_half_pos sfc_half_pos). Qed.

Lemma sfc_qrt_lt_half : lt sfc_qrt sfc_half.
Proof.
  apply (req_lt_compat sfc_qrt sfc_qrt (mult one sfc_half) sfc_half
           (req_refl sfc_qrt) (req_mult_one_l sfc_half)).
  exact (lt_mult_compat sfc_half one sfc_half sfc_half_pos
           (req_lt_compat (mult one sfc_half) sfc_half
                          (mult sfc_two sfc_half) one
                          (req_mult_one_l sfc_half)
                          (inv_pos_correct sfc_two req_two_pos)
                          (lt_mult_compat one sfc_two sfc_half sfc_half_pos
                             sfc_lt_one_two))).
Qed.

(* 2·(half·X) == X *)
Lemma sfc_two_half_mult : forall X : R, req (mult sfc_two (mult sfc_half X)) X.
Proof.
  intro X.
  apply (req_trans (mult sfc_two (mult sfc_half X))
                   (mult (mult sfc_two sfc_half) X)
                   X).
  - exact (mult_assoc sfc_two sfc_half X).
  - apply (req_trans (mult (mult sfc_two sfc_half) X)
                     (mult one X)
                     X).
    + exact (req_mult_compat (mult sfc_two sfc_half) one X X
               (req_trans (mult sfc_two sfc_half) (mult sfc_half sfc_two) one
                          (mult_comm sfc_two sfc_half)
                          (req_trans (mult sfc_half sfc_two)
                                     (mult sfc_two sfc_half) one
                                     (mult_comm sfc_half sfc_two)
                                     (inv_pos_correct sfc_two req_two_pos)))
               (req_refl X)).
    + exact (req_mult_one_l X).
Qed.

(* 节内 half 面尾件：nsq_tail（UpReqSqrtF nsq_half 面）经 inv_pos_ext 桥
   运输到本节 sfc_half 面（nsq_two_pos 为 Qed 不透明件，与 req_two_pos
   不可 conv——F3 卡跨节 half 墙，桥配方同 E-STAGING-F3 L408 实证）。 *)
Lemma sfc_half_tail : forall X : R, req (mult sfc_half (plus X X)) X.
Proof.
  intro X.
  exact (req_trans (mult sfc_half (plus X X))
                   (mult nsq_half (plus X X)) X
                   (req_mult_compat sfc_half nsq_half (plus X X) (plus X X)
                      (inv_pos_ext sfc_two nsq_two req_two_pos nsq_two_pos
                         (req_refl (plus one one)))
                      (req_refl (plus X X)))
                   (nsq_tail X)).
Qed.

(* ============ §0c Set 层有限和 + 几何尾和机器 ============ *)

Fixpoint sfc_sumf (f : nat -> R) (n : nat) : R :=
  match n with
  | Datatypes.O => zero
  | Datatypes.S m => plus (sfc_sumf f m) (f m)
  end.

Lemma sfc_sumf_nonneg : forall (f : nat -> R),
  (forall j : nat, le zero (f j)) ->
  forall n : nat, le zero (sfc_sumf f n).
Proof.
  intros f Hf n. induction n as [| n IH].
  - exact (le_refl zero).
  - exact (req_le_compat (plus zero zero) zero
                         (sfc_sumf f (Datatypes.S n)) (sfc_sumf f (Datatypes.S n))
                         (plus_zero zero) (req_refl (sfc_sumf f (Datatypes.S n)))
                         (le_plus_compat zero (sfc_sumf f n) zero (f n)
                            IH (Hf n))).
Qed.

(* （语句面说明） 原语句对任意 f 断言 0 ≤ 2·f X，缺 f 逐点非负
   前提（假命题面）；按 B8/TempStrict 先例补显式前提 Hnn，逐位保留其余语句。 *)
Lemma sfc_sumf_nonneg_le_two : forall (f : nat -> R),
  (forall j : nat, le zero (f j)) ->
  forall X : nat, le zero (mult sfc_two (f X)).
Proof.
  intros f Hnn X.
  exact (req_le_compat (mult zero (f X)) zero
                       (mult sfc_two (f X)) (mult sfc_two (f X))
                       (req_trans (mult zero (f X)) (mult (f X) zero) zero (mult_comm zero (f X)) (mult_zero (f X)))
                       (req_refl (mult sfc_two (f X)))
                       (le_mult_compat_weak zero sfc_two (f X) (Hnn X)
                          (sfc_lt_le zero sfc_two sfc_lt_zero_two))).
Qed.

(* 不变量形几何尾和：Σ_{j≤J} f_j + 2·f_{J+1} ≤ 2·f_0 *)
Lemma sfc_geom_inv : forall (f : nat -> R),
  (forall j : nat, le zero (f j)) ->
  (forall j : nat, le (f (Datatypes.S j)) (mult sfc_half (f j))) ->
  forall J : nat,
    le (plus (sfc_sumf f (Datatypes.S J)) (mult sfc_two (f (Datatypes.S J))))
       (mult sfc_two (f Datatypes.O)).
Proof.
  intros f Hnn Hdec J. induction J as [| J IH].
  - (* f_0 + 2·f_1 ≤ f_0 + 2·half·f_0 = f_0 + f_0 = 2·f_0 *)
    apply (le_trans (plus (sfc_sumf f (Datatypes.S Datatypes.O))
                          (mult sfc_two (f (Datatypes.S Datatypes.O))))
                    (plus (f Datatypes.O) (mult sfc_two (mult sfc_half (f Datatypes.O))))
                    (mult sfc_two (f Datatypes.O))).
    + exact (le_plus_compat
                (sfc_sumf f (Datatypes.S Datatypes.O)) (f Datatypes.O)
                (mult sfc_two (f (Datatypes.S Datatypes.O)))
                (mult sfc_two (mult sfc_half (f Datatypes.O)))
                (sfc_le_of_req (sfc_sumf f (Datatypes.S Datatypes.O)) (f Datatypes.O)
                   (req_plus_zero_l (f Datatypes.O)))
                (sfc_le_mult_l sfc_two (f (Datatypes.S Datatypes.O))
                   (mult sfc_half (f Datatypes.O))
                   sfc_lt_zero_two (Hdec Datatypes.O))).
    + exact (sfc_le_of_req (plus (f Datatypes.O)
                                 (mult sfc_two (mult sfc_half (f Datatypes.O))))
                           (mult sfc_two (f Datatypes.O))
                           (req_trans (plus (f Datatypes.O)
                                            (mult sfc_two (mult sfc_half (f Datatypes.O))))
                                      (plus (f Datatypes.O) (f Datatypes.O))
                                      (mult sfc_two (f Datatypes.O))
                                      (req_plus_compat (f Datatypes.O) (f Datatypes.O)
                                                       (mult sfc_two (mult sfc_half (f Datatypes.O)))
                                                       (f Datatypes.O)
                                                       (req_refl (f Datatypes.O))
                                                       (sfc_two_half_mult (f Datatypes.O)))
                                      (req_sym (mult (plus one one) (f Datatypes.O))
                                               (plus (f Datatypes.O) (f Datatypes.O))
                                               (req_two_mult (f Datatypes.O))))).
  - (* (Σ_{j≤J} + f_{J+1}) + 2·f_{J+2}
       ≤ (Σ_{j≤J} + f_{J+1}) + 2·half·f_{J+1} = Σ_{j≤J} + 2·f_{J+1} ≤ 2·f_0 *)
    apply (le_trans (plus (sfc_sumf f (Datatypes.S (Datatypes.S J)))
                          (mult sfc_two (f (Datatypes.S (Datatypes.S J)))))
                    (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                          (mult sfc_two (mult sfc_half (f (Datatypes.S J)))))
                    (mult sfc_two (f Datatypes.O))).
    + exact (le_plus_compat
                (sfc_sumf f (Datatypes.S (Datatypes.S J)))
                (sfc_sumf f (Datatypes.S (Datatypes.S J)))
                (mult sfc_two (f (Datatypes.S (Datatypes.S J))))
                (mult sfc_two (mult sfc_half (f (Datatypes.S J))))
                (le_refl (sfc_sumf f (Datatypes.S (Datatypes.S J))))
                (sfc_le_mult_l sfc_two (f (Datatypes.S (Datatypes.S J)))
                   (mult sfc_half (f (Datatypes.S J)))
                   sfc_lt_zero_two (Hdec (Datatypes.S J)))).
    + apply (le_trans (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                            (mult sfc_two (mult sfc_half (f (Datatypes.S J)))))
                      (plus (sfc_sumf f (Datatypes.S J))
                            (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                      (mult sfc_two (f Datatypes.O))).
      * exact (le_id_l
                  (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                        (mult sfc_two (mult sfc_half (f (Datatypes.S J)))))
                  (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                        (f (Datatypes.S J)))
                  (plus (sfc_sumf f (Datatypes.S J))
                        (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                  (req_plus_compat (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                                   (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                                   (mult sfc_two (mult sfc_half (f (Datatypes.S J))))
                                   (f (Datatypes.S J))
                                   (req_refl (plus (sfc_sumf f (Datatypes.S J))
                                                   (f (Datatypes.S J))))
                                   (sfc_two_half_mult (f (Datatypes.S J))))
                  (sfc_le_of_req
                     (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                           (f (Datatypes.S J)))
                     (plus (sfc_sumf f (Datatypes.S J))
                           (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                     (req_sym (plus (sfc_sumf f (Datatypes.S J))
                                    (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                              (plus (plus (sfc_sumf f (Datatypes.S J)) (f (Datatypes.S J)))
                                    (f (Datatypes.S J)))
                              (plus_assoc (sfc_sumf f (Datatypes.S J))
                                          (f (Datatypes.S J))
                                          (f (Datatypes.S J)))))).
      * apply (le_trans (plus (sfc_sumf f (Datatypes.S J))
                              (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                        (plus (sfc_sumf f (Datatypes.S J))
                              (mult sfc_two (f (Datatypes.S J))))
                        (mult sfc_two (f Datatypes.O))).
        -- exact (sfc_le_of_req
                     (plus (sfc_sumf f (Datatypes.S J))
                           (plus (f (Datatypes.S J)) (f (Datatypes.S J))))
                     (plus (sfc_sumf f (Datatypes.S J))
                           (mult sfc_two (f (Datatypes.S J))))
                     (req_plus_compat (sfc_sumf f (Datatypes.S J))
                                      (sfc_sumf f (Datatypes.S J))
                                      (plus (f (Datatypes.S J)) (f (Datatypes.S J)))
                                      (mult sfc_two (f (Datatypes.S J)))
                                      (req_refl (sfc_sumf f (Datatypes.S J)))
                                      (req_sym (mult (plus one one) (f (Datatypes.S J)))
                                               (plus (f (Datatypes.S J)) (f (Datatypes.S J)))
                                               (req_two_mult (f (Datatypes.S J)))))).
        -- exact IH.
Qed.

Lemma sfc_geom_tail : forall (f : nat -> R),
  (forall j : nat, le zero (f j)) ->
  (forall j : nat, le (f (Datatypes.S j)) (mult sfc_half (f j))) ->
  forall J : nat,
    le (sfc_sumf f (Datatypes.S J)) (mult sfc_two (f Datatypes.O)).
Proof.
  intros f Hnn Hdec J.
  apply (le_trans (sfc_sumf f (Datatypes.S J))
                  (plus (sfc_sumf f (Datatypes.S J))
                        (mult sfc_two (f (Datatypes.S J))))
                  (mult sfc_two (f Datatypes.O))).
  - exact (sfc_le_plus_r (sfc_sumf f (Datatypes.S J))
                         (mult sfc_two (f (Datatypes.S J)))
                         (sfc_sumf_nonneg_le_two f Hnn (Datatypes.S J))).
  - exact (sfc_geom_inv f Hnn Hdec J).
Qed.

(* ============ §0d req_minus 辅件 ============ *)

Lemma sfc_minus_chain : forall u v w : R,
  req (req_minus u w) (plus (req_minus u v) (req_minus v w)).
Proof.
  intros u v w.
  apply (req_trans (plus u (opp w))
                   (plus u (plus zero (opp w)))
                   (plus (plus u (opp v)) (plus v (opp w)))).
  - exact (req_plus_compat u u (opp w) (plus zero (opp w))
             (req_refl u)
             (req_sym (plus zero (opp w)) (opp w) (req_plus_zero_l (opp w)))).
  - apply (req_trans (plus u (plus zero (opp w)))
                     (plus u (plus (plus (opp v) v) (opp w)))
                     (plus (plus u (opp v)) (plus v (opp w)))).
    + exact (req_plus_compat u u (plus zero (opp w))
                             (plus (plus (opp v) v) (opp w))
                             (req_refl u)
                             (req_sym (plus (plus (opp v) v) (opp w))
                                      (plus zero (opp w))
                                      (req_plus_compat (plus (opp v) v) zero (opp w) (opp w)
                                                       (req_trans (plus (opp v) v)
                                                                  (plus v (opp v))
                                                                  zero
                                                                  (plus_comm (opp v) v)
                                                                  (plus_opp v))
                                                       (req_refl (opp w))))).
    + apply (req_trans (plus u (plus (plus (opp v) v) (opp w)))
                       (plus u (plus (opp v) (plus v (opp w))))
                       (plus (plus u (opp v)) (plus v (opp w)))).
      * exact (req_plus_compat u u
                  (plus (plus (opp v) v) (opp w))
                  (plus (opp v) (plus v (opp w)))
                  (req_refl u)
                  (req_sym (plus (opp v) (plus v (opp w)))
                           (plus (plus (opp v) v) (opp w))
                           (plus_assoc (opp v) v (opp w)))).
      * exact (plus_assoc u (opp v) (plus v (opp w))).
Qed.

Lemma sfc_le_zero_minus : forall u v : R, le u v -> le zero (req_minus v u).
Proof.
  intros u v H.
  exact (req_le_compat (plus u (opp u)) zero (plus v (opp u)) (req_minus v u)
                       (plus_opp u) (req_refl (req_minus v u))
                       (le_plus_compat u v (opp u) (opp u) H (le_refl (opp u)))).
Qed.

Lemma sfc_le_minus_compat : forall w u v : R, le u v ->
  le (req_minus w v) (req_minus w u).
Proof.
  intros w u v H.
  exact (le_plus_compat w w (opp v) (opp u) (le_refl w) (opp_le_compat u v H)).
Qed.

Lemma sfc_req_minus_half : forall u : R,
  req (req_minus u (mult sfc_half u)) (mult sfc_half u).
Proof.
  intro u.
  apply (req_trans (plus u (opp (mult sfc_half u)))
                   (plus (mult sfc_half (plus u u)) (opp (mult sfc_half u)))
                   (mult sfc_half u)).
  - exact (req_plus_compat u (mult sfc_half (plus u u))
                           (opp (mult sfc_half u)) (opp (mult sfc_half u))
                           (req_sym (mult sfc_half (plus u u)) u (sfc_half_tail u))
                           (req_refl (opp (mult sfc_half u)))).
  - apply (req_trans (plus (mult sfc_half (plus u u)) (opp (mult sfc_half u)))
                     (plus (plus (mult sfc_half u) (mult sfc_half u))
                           (opp (mult sfc_half u)))
                     (mult sfc_half u)).
    + exact (req_plus_compat (mult sfc_half (plus u u))
                             (plus (mult sfc_half u) (mult sfc_half u))
                             (opp (mult sfc_half u)) (opp (mult sfc_half u))
                             (distrib sfc_half u u)
                             (req_refl (opp (mult sfc_half u)))).
    + apply (req_trans (plus (plus (mult sfc_half u) (mult sfc_half u))
                             (opp (mult sfc_half u)))
                       (plus (mult sfc_half u)
                             (plus (mult sfc_half u) (opp (mult sfc_half u))))
                       (mult sfc_half u)).
      * exact (req_sym (plus (mult sfc_half u)
                             (plus (mult sfc_half u) (opp (mult sfc_half u))))
                       (plus (plus (mult sfc_half u) (mult sfc_half u))
                             (opp (mult sfc_half u)))
                       (plus_assoc (mult sfc_half u) (mult sfc_half u)
                                   (opp (mult sfc_half u)))).
      * apply (req_trans (plus (mult sfc_half u)
                               (plus (mult sfc_half u) (opp (mult sfc_half u))))
                         (plus (mult sfc_half u) zero)
                         (mult sfc_half u)).
        -- exact (req_plus_compat (mult sfc_half u) (mult sfc_half u)
                                  (plus (mult sfc_half u) (opp (mult sfc_half u)))
                                  zero
                                  (req_refl (mult sfc_half u))
                                  (plus_opp (mult sfc_half u))).
        -- exact (plus_zero (mult sfc_half u)).
Qed.

(* ============ §1 残差链（内节：a、x 参量化） ============ *)

Section SqrtfCauchyCore.

Variable a x : R.
Hypothesis Ha : lt zero a.
Hypothesis Hx : lt zero x.

(* 残差：t_n := s(z_n) *)
Definition sfc_t (n : nat) : R :=
  sqrtf_slack a (sqrtf_newton a Ha x Hx n) Ha (sqrtf_newton_pos a Ha x Hx n).

Lemma sfc_step_eq : forall n : nat,
  req (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
      (sqrtf_newton a Ha x Hx n).
Proof.
  intro n.
  apply (req_trans (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
                   (plus (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                         (sqrtf_slack a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n)))
                   (sqrtf_newton a Ha x Hx n)).
  - exact (req_plus_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                              (sqrtf_newton_pos a Ha x Hx n))
                           (sfc_t n)
                           (sqrtf_slack a (sqrtf_newton a Ha x Hx n) Ha
                              (sqrtf_newton_pos a Ha x Hx n))
                           (sqrtf_newton_succ a Ha x Hx n)
                           (req_refl (sfc_t n))).
  - exact (nsq_step_plus_slack a (sqrtf_newton a Ha x Hx n) Ha
             (sqrtf_newton_pos a Ha x Hx n)).
Qed.

Lemma sfc_step_minus : forall n : nat,
  req (req_minus (sqrtf_newton a Ha x Hx n)
                 (sqrtf_newton a Ha x Hx (Datatypes.S n)))
      (sfc_t n).
Proof.
  intro n.
  apply (req_trans (req_minus (sqrtf_newton a Ha x Hx n)
                              (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                   (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
                         (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                   (sfc_t n)).
  - exact (req_plus_compat (sqrtf_newton a Ha x Hx n)
                           (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
                           (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                           (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                           (req_sym (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                          (sfc_t n))
                                    (sqrtf_newton a Ha x Hx n)
                                    (sfc_step_eq n))
                           (req_refl (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))).
  - apply (req_trans (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
                           (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                     (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (plus (sfc_t n)
                                 (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))))
                     (sfc_t n)).
    + exact (req_sym (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (plus (sfc_t n) (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))))
                     (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n))
                           (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                     (plus_assoc (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sfc_t n)
                                 (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))).
    + apply (req_trans (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                             (plus (sfc_t n) (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))))
                       (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                   (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                             (sfc_t n))
                       (sfc_t n)).
      * exact (req_trans (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                               (plus (sfc_t n) (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))))
                         (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                               (plus (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))) (sfc_t n)))
                         (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                     (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                               (sfc_t n))
                         (req_plus_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                          (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                          (plus (sfc_t n) (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                          (plus (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))) (sfc_t n))
                                          (req_refl (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                          (plus_comm (sfc_t n) (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))))
                         (plus_assoc (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                     (opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                     (sfc_t n))).
      * exact (req_trans (plus (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                     (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                               (sfc_t n))
                         (plus zero (sfc_t n))
                         (sfc_t n)
                         (req_plus_compat (plus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                (opp (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                          zero
                                          (sfc_t n) (sfc_t n)
                                          (plus_opp (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                          (req_refl (sfc_t n)))
                         (req_plus_zero_l (sfc_t n))).
Qed.

Lemma sfc_z_ge_half : forall n : nat,
  le (mult sfc_half (sqrtf_newton a Ha x Hx n))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intro n.
  apply (req_le_compat (mult sfc_half (sqrtf_newton a Ha x Hx n))
                       (mult sfc_half (sqrtf_newton a Ha x Hx n))
                       (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n))
                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (req_refl (mult sfc_half (sqrtf_newton a Ha x Hx n)))
                       (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                   (sqrtf_newton_pos a Ha x Hx n))
                                (sqrtf_newton_succ a Ha x Hx n))).
  exact (req_le_compat (mult sfc_half (sqrtf_newton a Ha x Hx n))
                       (mult sfc_half (sqrtf_newton a Ha x Hx n))
                       (mult sfc_half (plus (sqrtf_newton a Ha x Hx n)
                                            (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                             (sqrtf_newton_pos a Ha x Hx n)))))
                       (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n))
                       (req_refl (mult sfc_half (sqrtf_newton a Ha x Hx n)))
                       (req_trans (mult sfc_half (plus (sqrtf_newton a Ha x Hx n)
                                                       (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                                        (sqrtf_newton_pos a Ha x Hx n)))))
                                  (mult nsq_half (plus (sqrtf_newton a Ha x Hx n)
                                                       (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                                        (sqrtf_newton_pos a Ha x Hx n)))))
                                  (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                     (sqrtf_newton_pos a Ha x Hx n))
                                  (req_mult_compat sfc_half nsq_half
                                     (plus (sqrtf_newton a Ha x Hx n)
                                           (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                            (sqrtf_newton_pos a Ha x Hx n))))
                                     (plus (sqrtf_newton a Ha x Hx n)
                                           (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                            (sqrtf_newton_pos a Ha x Hx n))))
                                     (inv_pos_ext sfc_two nsq_two req_two_pos nsq_two_pos
                                        (req_refl (plus one one)))
                                     (req_refl (plus (sqrtf_newton a Ha x Hx n)
                                                     (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                                      (sqrtf_newton_pos a Ha x Hx n))))))
                                  (req_refl (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                               (sqrtf_newton_pos a Ha x Hx n))))
                       (sfc_le_mult_l sfc_half (sqrtf_newton a Ha x Hx n)
                          (plus (sqrtf_newton a Ha x Hx n)
                             (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                (sqrtf_newton_pos a Ha x Hx n))))
                          sfc_half_pos
                          (sfc_le_plus_r (sqrtf_newton a Ha x Hx n)
                             (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                (sqrtf_newton_pos a Ha x Hx n)))
                             (sfc_lt_le zero (mult a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                         (sqrtf_newton_pos a Ha x Hx n)))
                                (mult_positive a (inv_pos (sqrtf_newton a Ha x Hx n)
                                                          (sqrtf_newton_pos a Ha x Hx n))
                                   Ha (inv_pos_pos (sqrtf_newton a Ha x Hx n)
                                                   (sqrtf_newton_pos a Ha x Hx n))))))).
Qed.

Lemma sfc_two_z_ge : forall n : nat,
  le (sqrtf_newton a Ha x Hx n)
     (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))).
Proof.
  intro n.
  apply (req_le_compat (mult sfc_two (mult sfc_half (sqrtf_newton a Ha x Hx n)))
                       (sqrtf_newton a Ha x Hx n)
                       (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                       (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                       (sfc_two_half_mult (sqrtf_newton a Ha x Hx n))
                       (req_refl (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))).
  exact (sfc_le_mult_l sfc_two (mult sfc_half (sqrtf_newton a Ha x Hx n))
           (sqrtf_newton a Ha x Hx (Datatypes.S n))
           sfc_lt_zero_two (sfc_z_ge_half n)).
Qed.

Lemma sfc_az_le : forall n : nat,
  le (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intro n.
  exact (sqrtf_inv_le_self a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
           (sqrtf_iterate_sq_ge sfc_square_nonneg a Ha x Hx n)).
Qed.

Lemma sfc_t_nonneg : forall n : nat, le zero (sfc_t (Datatypes.S n)).
Proof.
  intro n.
  exact (req_le_compat
           (mult zero sfc_half) zero
           (mult (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                 sfc_half)
           (sfc_t (Datatypes.S n))
           (req_trans (mult zero sfc_half) (mult sfc_half zero) zero
                      (mult_comm zero sfc_half) (mult_zero sfc_half))
           (req_trans (mult (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                       (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                  (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                            sfc_half)
                      (mult sfc_half (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))))
                      (sfc_t (Datatypes.S n))
                      (mult_comm (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                            (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                                 sfc_half)
                      (req_trans (mult sfc_half (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                           (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))))
                                 (mult nsq_half (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                           (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))))
                                 (sfc_t (Datatypes.S n))
                                 (req_mult_compat sfc_half nsq_half
                                                  (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                             (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                        (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                                                  (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                             (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                        (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                                                  (inv_pos_ext sfc_two nsq_two req_two_pos nsq_two_pos
                                                               (req_refl (plus one one)))
                                                  (req_refl (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                       (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                                  (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))))
                                 (req_refl (sfc_t (Datatypes.S n)))))
           (le_mult_compat zero
              (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                         (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                    (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
              sfc_half
              sfc_half_pos
              (sfc_le_zero_minus
                 (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                 (sqrtf_newton a Ha x Hx (Datatypes.S n))
                 (sfc_az_le n)))).
Qed.

Lemma sfc_t_le_half_z : forall n : nat,
  le (sfc_t (Datatypes.S n))
     (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))).
Proof.
  intro n.
  apply (le_trans (sfc_t (Datatypes.S n))
                  (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                             (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                  (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))).
  - apply (le_trans (sfc_t (Datatypes.S n))
                    (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                               (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                    (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                               (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))).
    + exact (req_le_compat (sfc_t (Datatypes.S n))
                           (sfc_t (Datatypes.S n))
                           (sfc_t (Datatypes.S n))
                           (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                      (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                           (req_refl (sfc_t (Datatypes.S n)))
                           (req_sym (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                               (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                                    (sfc_t (Datatypes.S n))
                                    (sfc_step_minus (Datatypes.S n)))
                           (le_refl (sfc_t (Datatypes.S n)))).
    + exact (sfc_le_minus_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                (sfc_z_ge_half (Datatypes.S n))).
  - exact (sfc_le_of_req (req_minus (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                    (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                         (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                         (sfc_req_minus_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))).
Qed.

Lemma sfc_slack_ext : forall (u v : R) (Hu : lt zero u) (Hv : lt zero v),
  req u v -> req (sqrtf_slack a u Ha Hu) (sqrtf_slack a v Ha Hv).
Proof.
  intros u v Hu Hv H.
  apply (req_trans (sqrtf_slack a u Ha Hu)
                   (mult nsq_half (plus u (opp (mult a (inv_pos u Hu)))))
                   (sqrtf_slack a v Ha Hv)).
  - exact (req_refl (sqrtf_slack a u Ha Hu)).
  - apply (req_trans (mult nsq_half (plus u (opp (mult a (inv_pos u Hu)))))
                     (mult sfc_half (plus u (opp (mult a (inv_pos u Hu)))))
                     (sqrtf_slack a v Ha Hv)).
    + exact (req_mult_compat nsq_half sfc_half
               (plus u (opp (mult a (inv_pos u Hu))))
               (plus u (opp (mult a (inv_pos u Hu))))
               (inv_pos_ext nsq_two sfc_two nsq_two_pos req_two_pos
                  (req_refl (plus one one)))
               (req_refl (plus u (opp (mult a (inv_pos u Hu)))))).
    + apply (req_trans (mult sfc_half (plus u (opp (mult a (inv_pos u Hu)))))
                       (mult sfc_half (plus v (opp (mult a (inv_pos v Hv)))))
                       (sqrtf_slack a v Ha Hv)).
      * exact (req_mult_compat sfc_half sfc_half
                 (plus u (opp (mult a (inv_pos u Hu))))
                 (plus v (opp (mult a (inv_pos v Hv))))
                 (req_refl sfc_half)
                 (req_plus_compat u v (opp (mult a (inv_pos u Hu)))
                                    (opp (mult a (inv_pos v Hv)))
                                    H
                                    (req_opp_compat (mult a (inv_pos u Hu))
                                                    (mult a (inv_pos v Hv))
                                                    (req_mult_compat a a (inv_pos u Hu)
                                                       (inv_pos v Hv) (req_refl a)
                                                       (inv_pos_ext u v Hu Hv H))))).
      * apply (req_trans (mult sfc_half (plus v (opp (mult a (inv_pos v Hv)))))
                         (mult nsq_half (plus v (opp (mult a (inv_pos v Hv)))))
                         (sqrtf_slack a v Ha Hv)).
        -- exact (req_mult_compat sfc_half nsq_half
                    (plus v (opp (mult a (inv_pos v Hv))))
                    (plus v (opp (mult a (inv_pos v Hv))))
                    (inv_pos_ext sfc_two nsq_two req_two_pos nsq_two_pos
                       (req_refl (plus one one)))
                    (req_refl (plus v (opp (mult a (inv_pos v Hv)))))).
        -- exact (req_refl (sqrtf_slack a v Ha Hv)).
Qed.
Lemma sfc_t_rec : forall n : nat,
  req (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
            (sfc_t (Datatypes.S n)))
      (mult (sfc_t n) (sfc_t n)).
Proof.
  intro n.
  apply (req_trans (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                         (sfc_t (Datatypes.S n)))
                   (mult (mult sfc_two (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                            (sqrtf_newton_pos a Ha x Hx n)))
                         (sqrtf_slack a (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                            (sqrtf_newton_pos a Ha x Hx n))
                                    Ha (sqrtf_step_pos a (sqrtf_newton a Ha x Hx n) Ha
                                           (sqrtf_newton_pos a Ha x Hx n))))
                   (mult (sfc_t n) (sfc_t n))).
  - exact (req_sym (mult (mult sfc_two (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                            (sqrtf_newton_pos a Ha x Hx n)))
                         (sqrtf_slack a (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                            (sqrtf_newton_pos a Ha x Hx n))
                                    Ha (sqrtf_step_pos a (sqrtf_newton a Ha x Hx n) Ha
                                           (sqrtf_newton_pos a Ha x Hx n))))
                   (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                         (sfc_t (Datatypes.S n)))
                   (req_mult_compat (mult sfc_two (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                                      (sqrtf_newton_pos a Ha x Hx n)))
                                    (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                    (sqrtf_slack a (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                                       (sqrtf_newton_pos a Ha x Hx n))
                                              Ha (sqrtf_step_pos a (sqrtf_newton a Ha x Hx n) Ha
                                                     (sqrtf_newton_pos a Ha x Hx n)))
                                    (sfc_t (Datatypes.S n))
                                    (req_mult_compat sfc_two sfc_two
                                       (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                          (sqrtf_newton_pos a Ha x Hx n))
                                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                       (req_refl sfc_two)
                                       (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                                   (sqrtf_newton_pos a Ha x Hx n))
                                                (sqrtf_newton_succ a Ha x Hx n)))
                                    (sfc_slack_ext (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                                      (sqrtf_newton_pos a Ha x Hx n))
                                                   (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                   (sqrtf_step_pos a (sqrtf_newton a Ha x Hx n) Ha
                                                      (sqrtf_newton_pos a Ha x Hx n))
                                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
                                                   (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                            (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                                               (sqrtf_newton_pos a Ha x Hx n))
                                                            (sqrtf_newton_succ a Ha x Hx n))))).
  - exact (nsq_slack_contraction a (sqrtf_newton a Ha x Hx n) Ha
              (sqrtf_newton_pos a Ha x Hx n)).
Qed.

(* 残差闭式：t_{S n} == inv(2·z_{S n})·(t_n·t_n) *)
Lemma sfc_t_eq : forall n : nat,
  req (sfc_t (Datatypes.S n))
      (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                     (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                        (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
            (mult (sfc_t n) (sfc_t n))).
Proof.
  intro n.
  apply (req_trans (sfc_t (Datatypes.S n))
                   (mult (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                       (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                          (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                               (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                         (sfc_t (Datatypes.S n)))
                   (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                  (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                         (mult (sfc_t n) (sfc_t n)))).
  - apply (req_trans (sfc_t (Datatypes.S n))
                     (mult one (sfc_t (Datatypes.S n)))
                     (mult (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                         (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                 (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                           (sfc_t (Datatypes.S n)))).
    + exact (req_sym (mult one (sfc_t (Datatypes.S n))) (sfc_t (Datatypes.S n))
                     (req_mult_one_l (sfc_t (Datatypes.S n)))).
    + exact (req_sym (mult (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                        (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                               (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                         (sfc_t (Datatypes.S n)))
                     (mult one (sfc_t (Datatypes.S n)))
                     (req_mult_compat
                        (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                      (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                         (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                              (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                        one
                        (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))
                        (req_trans (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                  (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                         (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                   (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                         (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                  (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                                   one
                                   (mult_comm (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                       (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                                          (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                              (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                   (inv_pos_correct (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                    (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                        (req_refl (sfc_t (Datatypes.S n))))).
  - apply (req_trans (mult (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                        (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                              (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                        (sfc_t (Datatypes.S n)))
                     (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                   (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                           (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                 (sfc_t (Datatypes.S n))))
                     (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                   (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                           (mult (sfc_t n) (sfc_t n)))).
    + exact (req_sym (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                    (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                           (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                 (sfc_t (Datatypes.S n))))
                     (mult (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                       (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                          (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                               (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                          (sfc_t (Datatypes.S n)))
                     (mult_assoc (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                            (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                               (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                 (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                 (sfc_t (Datatypes.S n)))).
    + exact (req_mult_compat
                (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                         (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                         (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                (mult (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                      (sfc_t (Datatypes.S n)))
                (mult (sfc_t n) (sfc_t n))
                (req_refl (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                   (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S n)) req_two_pos
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                (sfc_t_rec n)).
Qed.

(* 单步半衰减：t_{S S n} ≤ half·t_{S n}（使用假设位1：t'·t' ≥ 0） *)
Lemma sfc_t_decay : forall n : nat,
  le (sfc_t (Datatypes.S (Datatypes.S n))) (mult sfc_half (sfc_t (Datatypes.S n))).
Proof.
  intro n.
  apply (le_trans (sfc_t (Datatypes.S (Datatypes.S n)))
                  (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                                 (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))) req_two_pos
                                    (sqrtf_newton_pos a Ha x Hx (Datatypes.S (Datatypes.S n)))))
                        (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))))
                  (mult sfc_half (sfc_t (Datatypes.S n)))).
  - exact (sfc_le_of_req _ _ (sfc_t_eq (Datatypes.S n))).
  - apply (le_trans (mult (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                                  (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))) req_two_pos
                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S (Datatypes.S n)))))
                         (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))))
                    (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                          (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))))
                    (mult sfc_half (sfc_t (Datatypes.S n)))).
    + exact (le_mult_compat_weak
                (inv_pos (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                         (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))) req_two_pos
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S (Datatypes.S n)))))
                (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                         (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n)))
                (sfc_square_nonneg (sfc_t (Datatypes.S n)))
                (inv_pos_le_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                   (mult sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))))
                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
                                   (mult_positive sfc_two (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n))) req_two_pos
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S (Datatypes.S n))))
                                   (sfc_two_z_ge (Datatypes.S n)))).
    + apply (le_trans (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                        (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                               (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))))
                       (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                             (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                   (sfc_t (Datatypes.S n))))
                       (mult sfc_half (sfc_t (Datatypes.S n)))).
      * exact (sfc_le_mult_l (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                (mult (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n)))
                (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                      (sfc_t (Datatypes.S n)))
                (inv_pos_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                (le_mult_compat_weak (sfc_t (Datatypes.S n))
                                     (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                     (sfc_t (Datatypes.S n))
                                     (sfc_t_nonneg n)
                                     (sfc_t_le_half_z n))).
      * apply (sfc_le_of_req (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                              (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                   (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                         (sfc_t (Datatypes.S n))))
                             (mult sfc_half (sfc_t (Datatypes.S n)))).
        -- apply (req_trans (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                              (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                   (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                         (sfc_t (Datatypes.S n))))
                            (mult (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                        (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                 (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                  (sfc_t (Datatypes.S n)))
                            (mult sfc_half (sfc_t (Datatypes.S n)))).
           ++ exact (req_trans (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                        (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                             (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                   (sfc_t (Datatypes.S n))))
                                       (mult (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                                       (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                              (sfc_t (Datatypes.S n)))
                                       (mult (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                   (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                             (sfc_t (Datatypes.S n)))
                                       (mult_assoc (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                                   (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                   (sfc_t (Datatypes.S n)))
                                       (req_mult_compat (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                          (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                                         (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                                        (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                                                              (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                                                        (sfc_t (Datatypes.S n)) (sfc_t (Datatypes.S n))
                                                        (mult_comm (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                                                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                                                                   (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))))
                                        (req_refl (sfc_t (Datatypes.S n))))).
           ++ exact (req_trans (mult (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))) (inv_pos
                       (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))) (sfc_t
                       (Datatypes.S n))) (mult (mult sfc_half one) (sfc_t (Datatypes.S n))) (mult sfc_half (sfc_t
                       (Datatypes.S n))) (req_mult_compat (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S
                       n))) (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S
                       n)))) (mult sfc_half one) (sfc_t (Datatypes.S n)) (sfc_t
                       (Datatypes.S n)) (req_trans (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                       (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S
                       n)))) (mult sfc_half (mult (sqrtf_newton a Ha x Hx (Datatypes.S n)) (inv_pos (sqrtf_newton a Ha
                       x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))) (mult sfc_half one)
                       (req_sym (mult sfc_half (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S
                       n))))) (mult (mult sfc_half (sqrtf_newton a Ha x Hx (Datatypes.S n))) (inv_pos (sqrtf_newton a
                       Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))) (mult_assoc sfc_half
                       (sqrtf_newton a Ha x Hx (Datatypes.S n)) (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))) (req_mult_compat sfc_half sfc_half (mult
                       (sqrtf_newton a Ha x Hx (Datatypes.S n)) (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))) one (req_refl sfc_half) (inv_pos_correct
                       (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))))
                       (req_refl (sfc_t (Datatypes.S n)))) (req_mult_compat (mult sfc_half one) sfc_half (sfc_t
                       (Datatypes.S n)) (sfc_t (Datatypes.S n)) (mult_one sfc_half) (req_refl (sfc_t (Datatypes.S
                       n))))).
Qed.


Lemma sfc_t_pow_decay : forall k : nat,
  le (sfc_t (Datatypes.S k))
     (mult (sfc_pow_half k) (sfc_t (Datatypes.S Datatypes.O))).
Proof.
  induction k as [| k IH].
  - exact (req_le_compat (sfc_t (Datatypes.S Datatypes.O))
                         (sfc_t (Datatypes.S Datatypes.O))
                         (sfc_t (Datatypes.S Datatypes.O))
                         (mult one (sfc_t (Datatypes.S Datatypes.O)))
                         (req_refl (sfc_t (Datatypes.S Datatypes.O)))
                         (req_sym (mult one (sfc_t (Datatypes.S Datatypes.O)))
                                  (sfc_t (Datatypes.S Datatypes.O))
                                  (req_mult_one_l (sfc_t (Datatypes.S Datatypes.O))))
                         (le_refl (sfc_t (Datatypes.S Datatypes.O)))).
  - apply (le_trans (sfc_t (Datatypes.S (Datatypes.S k)))
                    (mult sfc_half (sfc_t (Datatypes.S k)))
                    (mult (sfc_pow_half (Datatypes.S k))
                          (sfc_t (Datatypes.S Datatypes.O)))).
    + exact (sfc_t_decay k).
    + apply (req_le_compat (mult sfc_half (sfc_t (Datatypes.S k)))
                           (mult sfc_half (sfc_t (Datatypes.S k)))
                           (mult sfc_half (mult (sfc_pow_half k)
                                                (sfc_t (Datatypes.S Datatypes.O))))
                           (mult (sfc_pow_half (Datatypes.S k))
                                 (sfc_t (Datatypes.S Datatypes.O)))
                           (req_refl (mult sfc_half (sfc_t (Datatypes.S k))))).
      * exact (req_trans (mult sfc_half (mult (sfc_pow_half k)
                                              (sfc_t (Datatypes.S Datatypes.O))))
                         (mult (mult sfc_half (sfc_pow_half k))
                               (sfc_t (Datatypes.S Datatypes.O)))
                         (mult (sfc_pow_half (Datatypes.S k))
                               (sfc_t (Datatypes.S Datatypes.O)))
                         (mult_assoc sfc_half (sfc_pow_half k)
                                     (sfc_t (Datatypes.S Datatypes.O)))
                         (req_mult_compat (mult sfc_half (sfc_pow_half k))
                                          (mult (sfc_pow_half k) sfc_half)
                                          (sfc_t (Datatypes.S Datatypes.O))
                                          (sfc_t (Datatypes.S Datatypes.O))
                                          (mult_comm sfc_half (sfc_pow_half k))
                                          (req_refl (sfc_t (Datatypes.S Datatypes.O))))).
      * exact (sfc_le_mult_l sfc_half (sfc_t (Datatypes.S k))
                 (mult (sfc_pow_half k) (sfc_t (Datatypes.S Datatypes.O)))
                 sfc_half_pos IH).
Qed.

(* ===== 单调下降：t_{n+2} ≤ t_{n+1}（前席引用未定义，本席补装；
   指标同移一位——t 非负仅 n ≥ 1 有保证，sfc_t_nonneg 同界） ===== *)
Lemma sfc_t_mono : forall n : nat,
  le (sfc_t (Datatypes.S (Datatypes.S n))) (sfc_t (Datatypes.S n)).
Proof.
  intros n.
  apply (le_trans (sfc_t (Datatypes.S (Datatypes.S n)))
                  (mult sfc_half (sfc_t (Datatypes.S n)))
                  (sfc_t (Datatypes.S n))).
  + exact (sfc_t_decay n).
  + apply (le_trans (mult sfc_half (sfc_t (Datatypes.S n)))
                    (mult one (sfc_t (Datatypes.S n)))
                    (sfc_t (Datatypes.S n))).
    * exact (le_mult_compat_weak sfc_half one (sfc_t (Datatypes.S n))
                                (sfc_t_nonneg n) (sfc_half_le_one)).
    * exact (sfc_le_of_req (mult one (sfc_t (Datatypes.S n)))
                           (sfc_t (Datatypes.S n))
                           (req_mult_one_l (sfc_t (Datatypes.S n)))).
Qed.

Lemma sfc_t_mono_from : forall (k n : nat),
  le (sfc_t (Datatypes.S (n + k))) (sfc_t (Datatypes.S n)).
Proof.
  intros k n. induction k as [| k IH].
  - replace (n + Datatypes.O) with n by lia.
    exact (le_refl (sfc_t (Datatypes.S n))).
  - replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    apply (le_trans (sfc_t (Datatypes.S (Datatypes.S (n + k))))
                    (sfc_t (Datatypes.S (n + k)))
                    (sfc_t (Datatypes.S n))).
    + exact (sfc_t_mono (n + k)).
    + exact IH.
Qed.

(* ===== 尾和件②：Σ_{j<J} t_{m+j} ≤ 2·t_m（m ≥ 1） ===== *)
Lemma sfc_geom_tail_t : forall (m J : nat), (1 <= m)%nat ->
  le (sfc_sumf (fun j => sfc_t (m + j)) J) (mult sfc_two (sfc_t m)).
Proof.
  intros m J Hm.
  replace (sfc_t m) with (sfc_t (m + Datatypes.O)) by (f_equal; lia).
  destruct J as [| J'].
  - destruct m as [| m'']; [ lia | ].
    exact (sfc_sumf_nonneg_le_two (fun j => sfc_t (Datatypes.S m'' + j))
             (fun j => sfc_t_nonneg (m'' + j)) Datatypes.O).
  - apply (sfc_geom_tail (fun j => sfc_t (m + j))).
    + intros j.
      replace (m + j) with (Datatypes.S ((m - 1) + j)) by lia.
      exact (sfc_t_nonneg ((m - 1) + j)).
    + intros j.
      replace (m + Datatypes.S j) with (Datatypes.S (Datatypes.S ((m - 1) + j))) by lia.
      replace (m + j) with (Datatypes.S ((m - 1) + j)) by lia.
      exact (sfc_t_decay ((m - 1) + j)).
Qed.

(* ===== 望远镜：z_m − z_{m+J} == Σ_{j<J} t_{m+j} ===== *)
Lemma sfc_telescope : forall m J : nat,
  req (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx (m + J)))
      (sfc_sumf (fun j => sfc_t (m + j)) J).
Proof.
  intros m J. induction J as [| J IH].
  - replace (m + Datatypes.O) with m by lia.
    exact (req_trans (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx m))
                     zero zero
                     (plus_opp (sqrtf_newton a Ha x Hx m))
                     (req_refl zero)).
  - replace (m + Datatypes.S J) with (Datatypes.S (m + J)) by lia.
    apply (req_trans (req_minus (sqrtf_newton a Ha x Hx m)
                                (sqrtf_newton a Ha x Hx (Datatypes.S (m + J))))
                     (plus (req_minus (sqrtf_newton a Ha x Hx m)
                                      (sqrtf_newton a Ha x Hx (m + J)))
                           (req_minus (sqrtf_newton a Ha x Hx (m + J))
                                      (sqrtf_newton a Ha x Hx (Datatypes.S (m + J)))))
                     (sfc_sumf (fun j => sfc_t (m + j)) (Datatypes.S J))).
    + exact (sfc_minus_chain (sqrtf_newton a Ha x Hx m)
                             (sqrtf_newton a Ha x Hx (m + J))
                             (sqrtf_newton a Ha x Hx (Datatypes.S (m + J)))).
    + apply (req_trans (plus (req_minus (sqrtf_newton a Ha x Hx m)
                                        (sqrtf_newton a Ha x Hx (m + J)))
                             (req_minus (sqrtf_newton a Ha x Hx (m + J))
                                        (sqrtf_newton a Ha x Hx (Datatypes.S (m + J)))))
                       (plus (sfc_sumf (fun j => sfc_t (m + j)) J)
                             (sfc_t (m + J)))
                       (sfc_sumf (fun j => sfc_t (m + j)) (Datatypes.S J))).
      * exact (req_plus_compat (req_minus (sqrtf_newton a Ha x Hx m)
                                          (sqrtf_newton a Ha x Hx (m + J)))
                               (sfc_sumf (fun j => sfc_t (m + j)) J)
                               (req_minus (sqrtf_newton a Ha x Hx (m + J))
                                          (sqrtf_newton a Ha x Hx (Datatypes.S (m + J))))
                               (sfc_t (m + J))
                               IH
                               (sfc_step_minus (m + J))).
      * exact (req_refl (plus (sfc_sumf (fun j => sfc_t (m + j)) J) (sfc_t (m + J)))).
Qed.

(* ===== 取档步①：∃K, sfc_t K ≤ m0（阿基米德假设位直接应用） ===== *)
Lemma sfc_pick_K :
  sigT (fun K : nat =>
        le (sfc_t K)
           (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))).
Proof.
  destruct (sfc_arch_decay (sfc_t (Datatypes.S Datatypes.O))
              (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                               (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))
              (sfc_t_nonneg Datatypes.O)
              (mult_positive a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O)) (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))) Ha
                 (inv_pos_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                              (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O)))))
    as [k Hk].
  exists (Datatypes.S k).
  apply (le_trans (sfc_t (Datatypes.S k))
                  (mult (sfc_pow_half k) (sfc_t (Datatypes.S Datatypes.O)))
                  (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))).
  - exact (sfc_t_pow_decay k).
  - exact (sfc_lt_le (mult (sfc_pow_half k) (sfc_t (Datatypes.S Datatypes.O)))
                     (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))
                     (req_lt_compat (mult (sfc_t (Datatypes.S Datatypes.O)) (sfc_pow_half k))
                                    (mult (sfc_pow_half k) (sfc_t (Datatypes.S Datatypes.O)))
                                    (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))
                                    (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                                                     (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O))))
                                    (mult_comm (sfc_t (Datatypes.S Datatypes.O)) (sfc_pow_half k))
                                    (req_refl (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S Datatypes.O))
                                                               (sqrtf_newton_pos a Ha x Hx (Datatypes.S Datatypes.O)))))
                                    Hk)).
Qed.

(* ===== 对内 Cauchy 界：S K ≤ m ≤ n 的单侧链 ===== *)
Lemma sfc_cauchy_pair : forall (K : nat) (eps : R),
  lt zero eps ->
  lt (sfc_t (Datatypes.S K)) (mult sfc_qrt eps) ->
  forall m n : nat, (Datatypes.S K <= m)%nat -> (m <= n)%nat ->
  lt (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n)) eps.
Proof.
  intros K eps Heps HtN m n HKm Hmn.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (HJ : (m + (n - m))%nat = n) by lia.
  assert (Hsumnn : le zero (sfc_sumf (fun j => sfc_t (m + j)) (n - m))).
  { apply sfc_sumf_nonneg. intros j.
    replace (m + j) with (Datatypes.S ((m - 1) + j)) by lia.
    exact (sfc_t_nonneg ((m - 1) + j)). }
  assert (Hgeom : le (sfc_sumf (fun j => sfc_t (m + j)) (n - m))
                     (mult sfc_two (sfc_t m))) by exact (sfc_geom_tail_t m (n - m) Hm1).
  assert (Htm : le (sfc_t m) (sfc_t (Datatypes.S K))).
  { replace m with (Datatypes.S (K + (m - 1 - K))) by lia.
    exact (sfc_t_mono_from (m - 1 - K) K). }
  assert (Htmq : le (sfc_t m) (mult sfc_qrt eps))
    by exact (le_trans (sfc_t m) (sfc_t (Datatypes.S K)) (mult sfc_qrt eps)
           Htm (sfc_lt_le (sfc_t (Datatypes.S K)) (mult sfc_qrt eps) HtN)).
  assert (Htwo : le (mult sfc_two (sfc_t m)) (mult sfc_two (mult sfc_qrt eps)))
    by exact (sfc_le_mult_l sfc_two (sfc_t m) (mult sfc_qrt eps) sfc_lt_zero_two Htmq).
  (* 2·qrt·eps == half·eps *)
  assert (Eh : req (mult sfc_two (mult sfc_qrt eps)) (mult sfc_half eps)).
  { apply (req_trans (mult sfc_two (mult sfc_qrt eps))
                     (mult (mult sfc_two sfc_qrt) eps)
                     (mult sfc_half eps)).
    - exact (mult_assoc sfc_two sfc_qrt eps).
    - exact (req_mult_compat (mult sfc_two sfc_qrt) sfc_half eps eps
                (sfc_two_half_mult sfc_half) (req_refl eps)). }
  assert (Htel : req (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                     (sfc_sumf (fun j => sfc_t (m + j)) (n - m))).
  { pose proof (sfc_telescope m (n - m)) as Ht0. rewrite HJ in Ht0. exact Ht0. }
  assert (Hbound : le (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                      (plus (mult sfc_half eps) (mult sfc_qrt eps))).
  { apply (le_trans (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                    (plus (sfc_sumf (fun j => sfc_t (m + j)) (n - m)) (mult sfc_qrt eps))
                    (plus (mult sfc_half eps) (mult sfc_qrt eps))).
    - apply (le_trans (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                      (abs (sfc_sumf (fun j => sfc_t (m + j)) (n - m)))
                      (plus (sfc_sumf (fun j => sfc_t (m + j)) (n - m)) (mult sfc_qrt eps))).
      + apply (req_le_compat
                  (abs (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n)))
                  (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                  (abs (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n)))
                  (abs (sfc_sumf (fun j => sfc_t (m + j)) (n - m)))).
        * exact (req_sym (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                         (abs (req_minus (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n)))
                         (sfc_metric_abs (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))).
        * exact (req_abs_compat (req_minus (sqrtf_newton a Ha x Hx m)
                                           (sqrtf_newton a Ha x Hx n))
                                (sfc_sumf (fun j => sfc_t (m + j)) (n - m)) Htel).
        * exact (le_refl (abs (req_minus (sqrtf_newton a Ha x Hx m)
                                         (sqrtf_newton a Ha x Hx n)))).
      + exact (sfc_abs_le_plus_eps (sfc_sumf (fun j => sfc_t (m + j)) (n - m))
                  Hsumnn (mult sfc_qrt eps) (mult_positive sfc_qrt eps sfc_qrt_pos Heps)).
    - exact (le_plus_compat (sfc_sumf (fun j => sfc_t (m + j)) (n - m))
                            (mult sfc_half eps)
                            (mult sfc_qrt eps)
                            (mult sfc_qrt eps)
                (le_trans (sfc_sumf (fun j => sfc_t (m + j)) (n - m))
                          (mult sfc_two (sfc_t m))
                          (mult sfc_half eps)
                          Hgeom
                          (le_trans (mult sfc_two (sfc_t m))
                                    (mult sfc_two (mult sfc_qrt eps))
                                    (mult sfc_half eps)
                                    Htwo
(sfc_le_of_req (mult sfc_two (mult sfc_qrt eps)) (mult sfc_half eps) Eh)))
                (le_refl (mult sfc_qrt eps))). }
  (* 严格收尾：half·eps + qrt·eps < eps *)
  apply (le_lt_trans _ _ _ Hbound).
  apply (req_lt_compat (plus (mult sfc_qrt eps) (mult sfc_half eps))
                       (plus (mult sfc_half eps) (mult sfc_qrt eps))
                       (plus (mult sfc_half eps) (mult sfc_half eps))
                       eps
                       (plus_comm (mult sfc_qrt eps) (mult sfc_half eps))
                       (req_trans (plus (mult sfc_half eps) (mult sfc_half eps))
                                  (mult sfc_half (plus eps eps))
                                  eps
                                  (req_sym (mult sfc_half (plus eps eps))
                                           (plus (mult sfc_half eps) (mult sfc_half eps))
                                           (distrib sfc_half eps eps))
                                  (sfc_half_tail eps))).
  apply (sfc_lt_plus_compat_lt_le (mult sfc_qrt eps) (mult sfc_half eps)
           (mult sfc_half eps) (mult sfc_half eps)
           (lt_mult_compat sfc_qrt sfc_half eps Heps sfc_qrt_lt_half)
           (le_refl (mult sfc_half eps))).
Qed.

(* ===== 组装③：逐 eps Cauchy 证书（对照表 :644-648 同形） ===== *)
Lemma sfc_newton_cauchy : forall eps : R, lt zero eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    lt (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n)) eps).
Proof.
  intros eps Heps.
  destruct (sfc_arch_decay (sfc_t (Datatypes.S Datatypes.O)) (mult sfc_qrt eps)
              (sfc_t_nonneg Datatypes.O) (mult_positive sfc_qrt eps sfc_qrt_pos Heps)) as [k1 Hk1].
  assert (HtN : lt (sfc_t (Datatypes.S k1)) (mult sfc_qrt eps)).
  { apply (le_lt_trans (sfc_t (Datatypes.S k1))
                       (mult (sfc_pow_half k1) (sfc_t (Datatypes.S Datatypes.O)))
                       (mult sfc_qrt eps)
                       (sfc_t_pow_decay k1)
                       (req_lt_compat (mult (sfc_t (Datatypes.S Datatypes.O)) (sfc_pow_half k1))
                                      (mult (sfc_pow_half k1) (sfc_t (Datatypes.S Datatypes.O)))
                                      (mult sfc_qrt eps) (mult sfc_qrt eps)
                                      (mult_comm (sfc_t (Datatypes.S Datatypes.O)) (sfc_pow_half k1))
                                      (req_refl (mult sfc_qrt eps))
                                      Hk1)). }
  exists (Datatypes.S k1).
  intros m n Hm Hn.
  destruct (Nat.leb m n) eqn:Eb.
  - exact (sfc_cauchy_pair k1 eps Heps HtN m n
             (NatLe_drop (Datatypes.S k1) m Hm) (proj1 (Nat.leb_le m n) Eb)).
  - apply (req_lt_compat (metric (sqrtf_newton a Ha x Hx n) (sqrtf_newton a Ha x Hx m))
                         (metric (sqrtf_newton a Ha x Hx m) (sqrtf_newton a Ha x Hx n))
                         eps
                         eps
                         (metric_sym (sqrtf_newton a Ha x Hx n) (sqrtf_newton a Ha x Hx m))
                         (req_refl eps)).
    exact (sfc_cauchy_pair k1 eps Heps HtN n m
             (NatLe_drop (Datatypes.S k1) n Hn)
             (Nat.lt_le_incl _ _ (proj1 (Nat.leb_gt m n) Eb))).
Qed.

(* G4：封闭性核查（零公理面；四假设位为节参显式前提，非公理） *)
Print Assumptions sfc_newton_cauchy.
Print Assumptions sfc_pick_K.

End SqrtfCauchyCore.

End SqrtfCauchy.

(* ============================================================ *)
(* G3 提取（补记）：                                            *)
(* 参照 KLWallClosed.v 同式，Obj.magic 计数=0 为通过，产物 sfc_G3.ml。 *)
(* ============================================================ *)
Extraction "sfc_G3.ml" sfc_newton_cauchy sfc_pick_K sfc_geom_tail_t.
(* ============================================================ *)
(* 位 sfc_square_nonneg 的证书供给（载体代换：抽象 RIS 载体 → 锚件世界     *)
(* DO 可判定序增强载体）。                                               *)
(*                                                                     *)
(* 原位（Section SqrtfCauchy 假设位1，抽象 RIS 世界）为已登记的结构性     *)
(* 阻隔面——全称平方非负的 Or 编码数据形等价逐实数符号判定器，抽象世界内   *)
(* 不可供给（判定标注见 SqrtfCauchyDischarge §C）；锚件 AbsSqClose 在      *)
(* RealInterfaceEnhanced 与 DecidableOrder 双 Context 世界内对同语句给出  *)
(* 实证（asc_sq_nonneg，AbsSqClose:156，三分可判定序逐支构造）。本供给件   *)
(* 为锚语句的透明别名直引——语句形与原假设位逐字同型由锚语句自身携带，      *)
(* 投影世界（le/zero/mult 所属接口类）随锚解析，规避本文件 Import 面的     *)
(* RealInterfaceEnhancedSetoid 类投影错配。原假设位声明与既有定理签名      *)
(* 零改动。                                                              *)
(* ============================================================ *)
Definition sfc_square_nonneg_supply
  (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI) :=
  @asc_sq_nonneg RI DO.

Print Assumptions sfc_square_nonneg_supply.
