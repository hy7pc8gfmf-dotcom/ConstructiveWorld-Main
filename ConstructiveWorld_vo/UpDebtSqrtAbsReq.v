(* ==========================================================================)
   UpDebtSqrtAbsReq.v — 抽象 req 层平方根见证件
   使命: Section SqrtAbsReq：req_sqrt_premise_le_intro（平方 ≥ a 前提的 le 引入形）与 req_sqrt_witness_exists_abstract（平方根见证存在性 sigT 形），two_abs/half_abs 支撑件；见证形态重述件 req_sqrt_witness_exists_abstract_witness/req_sqrt_one_abstract。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra。
   对标: 构造性分析中平方根存在性的抽象接口版本（Bishop 构造主义）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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

(* ===== 件 4（主定理）：抽象 req 层平方根见证 ===== *)
(* d > 0：r := e^{-(half·log_inv d)}，le 由 exp_neg_pos，
   r·r == d 由 exp_neg_plus(sym) + exp_neg_req_compat_setoid
   （使用 Hinner : half·L + half·L == L）+ exp_neg_log_inv 三链；
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

(* ===== 件 5：见证形态重述（语义同件 4，供下游按名使用） ===== *)
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
