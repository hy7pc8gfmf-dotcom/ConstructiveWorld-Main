(* ============================================================ *)
(* UpDebtSqrtAbsReq.v *)
(* *)
(* 目的： 抽象载体的平方根见证存在引理（req 接口层）。 *)
(* 主件： req_sqrt_witness_exists_abstract 及其见证提取；req_sqrt_premise_le_intro 前提引入。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra。 *)
(* 备注： 抽象 R 载体配 RealInterfaceEnhancedSetoid；辅助元 two_abs / half_abs 自足构造，零外加假设。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpDebtSqrtAbsReq.v — 签名迁移批 4 第二席：G02_Debt 的     *)
(*   req 伴件（5 件 + 1 冻结扣除）                                *)
(*   冻结扣除：母件 sqrt_witness @L35 req 同位件批 2 已结果       *)
(*   （UpReqDist reqd_sqrt_witness），本件不重建。                *)
(* 非平凡性分级：件 4/5/6 = A（req 链三分支全构造）；件 3 = B。   *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

Section SqrtAbsReq.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let lt := @lt R RIS.
Let le := @le R RIS.
Let inv_pos := @inv_pos R RIS.
Let exp_neg := @exp_neg R RIS.

(* two := 1 + 1；two > 0（基座 req_two_pos 直引） *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : lt zero two_abs.
Proof. exact req_two_pos. Qed.

(* half := inv(two)；half + half == one（req 链：inv_pos_correct
   + distrib + mult_one + req_plus_compat 五步纯项） *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : req (plus half_abs half_abs) one.
Proof.
  assert (Hd : req (mult half_abs two_abs) one).
  { exact (req_trans (mult half_abs two_abs) (mult two_abs half_abs) one
             (mult_comm half_abs two_abs)
             (inv_pos_correct two_abs two_abs_pos)). }
  assert (Hsplit : req (mult half_abs two_abs) (plus half_abs half_abs)).
  { apply (req_trans
              (mult half_abs (plus one one))
              (plus (mult half_abs one) (mult half_abs one))
              (plus half_abs half_abs)).
    - exact (distrib half_abs one one).
    - exact (req_plus_compat (mult half_abs one) half_abs
                             (mult half_abs one) half_abs
                             (mult_one half_abs) (mult_one half_abs)). }
  exact (req_trans (plus half_abs half_abs) (mult half_abs two_abs) one
           (req_sym (mult half_abs two_abs) (plus half_abs half_abs) Hsplit)
           Hd).
Qed.

(* ===== 件 3：Or 前件即 le 的构造性内容 ===== *)
Lemma req_sqrt_premise_le_intro : forall d : R,
  Or (lt zero d) (req zero d) -> le zero d.
Proof.
  intros d H. apply lt_le_iff. exact H.
Qed.

(* ===== 件 4（旗舰）：抽象 req 层平方根见证 ===== *)
(* d > 0：r := e^{-(half·log_inv d)}，le 由 exp_neg_pos，
   r·r == d 由 exp_neg_plus(sym) + exp_neg_req_compat_setoid
   （消费 Hinner : half·L + half·L == L）+ exp_neg_log_inv 三链；
   d == 0：r := zero，mult zero zero == zero 由接口字段 mult_zero。 *)
Theorem req_sqrt_witness_exists_abstract :
  forall d : R,
  Or (lt zero d) (req zero d) ->
  sigT (fun r : R => And (le zero r) (req (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - exists (exp_neg (mult half_abs (log_inv d Hdlt))).
    split.
    + exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d Hdlt)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d Hdlt))))).
    + assert (Hinner : req (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt)))
                           (log_inv d Hdlt)).
      { apply (req_trans
                  (plus (mult half_abs (log_inv d Hdlt)) (mult half_abs (log_inv d Hdlt)))
                  (mult (plus half_abs half_abs) (log_inv d Hdlt))
                  (log_inv d Hdlt)).
        - exact (req_sym
                    (mult (plus half_abs half_abs) (log_inv d Hdlt))
                    (plus (mult half_abs (log_inv d Hdlt)) (mult half_abs (log_inv d Hdlt)))
                    (req_mult_plus_distr_r half_abs half_abs (log_inv d Hdlt))).
        - apply (req_trans
                    (mult (plus half_abs half_abs) (log_inv d Hdlt))
                    (mult one (log_inv d Hdlt))
                    (log_inv d Hdlt)).
          + exact (req_mult_compat (plus half_abs half_abs) one
                                   (log_inv d Hdlt) (log_inv d Hdlt)
                                   half_plus_half (req_refl (log_inv d Hdlt))).
          + exact (req_trans (mult one (log_inv d Hdlt))
                             (mult (log_inv d Hdlt) one)
                             (log_inv d Hdlt)
                             (mult_comm one (log_inv d Hdlt))
                             (mult_one (log_inv d Hdlt))). }
      exact (req_trans
              (mult (exp_neg (mult half_abs (log_inv d Hdlt)))
                    (exp_neg (mult half_abs (log_inv d Hdlt))))
              (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                             (mult half_abs (log_inv d Hdlt))))
              d
              (req_sym
                  (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt))))
                  (mult (exp_neg (mult half_abs (log_inv d Hdlt)))
                        (exp_neg (mult half_abs (log_inv d Hdlt))))
                  (exp_neg_plus (mult half_abs (log_inv d Hdlt))
                                (mult half_abs (log_inv d Hdlt))))
              (req_trans
                  (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt))))
                  (exp_neg (log_inv d Hdlt))
                  d
                  (exp_neg_req_compat_setoid
                      (plus (mult half_abs (log_inv d Hdlt))
                            (mult half_abs (log_inv d Hdlt)))
                      (log_inv d Hdlt) Hinner)
                  (exp_neg_log_inv d Hdlt))).
  - exists zero.
    split.
    + apply le_refl.
    + exact (req_trans (mult zero zero) zero d (mult_zero zero) Hdeq).
Qed.

(* ===== 件 5：见证形态重述（语义同件 4，供下游按名消费） ===== *)
Lemma req_sqrt_witness_exists_abstract_witness :
  forall d : R,
  Or (lt zero d) (req zero d) ->
  sigT (fun r : R => And (le zero r) (req (mult r r) d)).
Proof.
  intros d H.
  exact (req_sqrt_witness_exists_abstract d H).
Qed.

(* ===== 件 6：实例——1 的抽象平方根 ===== *)
Lemma req_sqrt_one_abstract :
  sigT (fun r : R => And (le zero r) (req (mult r r) one)).
Proof.
  exact (req_sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbsReq.
