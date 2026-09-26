(* ==========================================================================)
   ToyR_BeukersVariant.v — (1+t)^{n+1} 变体 Beukers 逼近的 Q 层级数定形
   使命: 变体积分 I′_n 的全正项级数展开、截断多项式 bv_carrier 的积分与级数部分和精确相等（QeqT）且单调恒正、定形主结论 ln2 − p_n/q̃_n == I′_n/q̃_n（真归一形）、Delannoy 恒等式 bv_delannoy_eq_qtilde 与数值锚组。
   依赖: QArith、List、Arith、ZArith、Lia；S01_BaseRing、S02_CauchyComplete、S03_QExp、PolyIntegral、PadeErrorIntegral、BeukersLists、PintMono。
   对标: Beukers 型 (1+t)^{n+1} 积分变体（ln2/Apéry 逼近论）。
   构造性: 主定理全 Qed、零承认词面（文末 Print Assumptions 复核）；主结论取 Q 层 Set 面（QeqT/QltT/QleT′）；支撑引理 Prop 面仅服务推理；可提取。
   编译配方: coqc 9.1 直调（无 -Q），cpu_guard 包裹，-o 输出临时目录，树内 .vo 不重写。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import PadeErrorIntegral BeukersLists PintMono.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 级数定形：级数项 bv_term = C(n+m,n)·B(n+2m+1, 2n+1) 与其正性        *)
(* ============================================================ *)

Definition bv_term (n m : nat) : Q :=
  ((Z.of_nat (bkC (n + m) n) # 1) *
     (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q.

(* bv_term n m == C(n+m,n)·∫₀¹ t^{n+2m}(1−t)^{2n+1} dt（由 pei_beta_value 归到 pint_integral） *)
Lemma bv_term_value : forall n m : nat,
  bv_term n m ==
  ((Z.of_nat (bkC (n + m) n) # 1) * pint_integral (pei_list (n + 2 * m) (2 * n + 1)))%Q.
Proof.
  intros n m. unfold bv_term.
  rewrite (pei_beta_value (n + 2 * m) (2 * n + 1)).
  replace ((n + 2 * m) + (2 * n + 1) + 1)%nat with (3 * n + 2 * m + 2)%nat by lia.
  reflexivity.
Qed.

(** bv_term_pos：级数项严格正——bkC ≥ 1 与 q_fact 正性相乘。 *)
Theorem bv_term_pos : forall n m : nat, QltT 0 (bv_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold bv_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : 1 <= bkC (n + m) n) by (apply bkC_pos; lia).
    assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* §B 截断承载：bv_pad（补两个零系数）与 bv_carrier（pei_eb_list 同型）   *)
(* ============================================================ *)

Definition bv_pad (p : list Q) : list Q := pei_ztail (pei_ztail p).

Lemma bv_pad_eval : forall (p : list Q) (x : Q),
  pint_eval (bv_pad p) x == pint_eval p x.
Proof.
  intros p x. unfold bv_pad.
  rewrite pei_eval_ztail, pei_eval_ztail. reflexivity.
Qed.

Lemma bv_pad_int : forall p : list Q,
  pint_integral (bv_pad p) == pint_integral p.
Proof.
  intro p. unfold bv_pad.
  rewrite pei_integral_ztail, pei_integral_ztail. reflexivity.
Qed.

Lemma bv_pad_length : forall p : list Q, length (bv_pad p) = (length p + 2)%nat.
Proof.
  intro p. unfold bv_pad, pei_ztail.
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

(* bv_carrier n M：部分和 Σ_{m≤M} C(n+m,n)·t^{n+2m}(1−t)^{2n+1} 的系数表（pei_eb_list 同型） *)
Fixpoint bv_carrier (n M : nat) : list Q :=
  match M with
  | 0 => pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                    (pei_list (n + 2 * 0) (2 * n + 1))
  | Datatypes.S m =>
      pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                           (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
               (bv_pad (bv_carrier n m))
  end.

Lemma bv_carrier_length : forall n M : nat,
  length (bv_carrier n M) = (3 * n + 2 * M + 2)%nat.
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    rewrite pei_scale_length, pei_list_length. lia.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite pei_scale_length, pei_list_length, bv_pad_length, IH. lia. }
    rewrite (pei_add_length _ _ HL).
    rewrite pei_scale_length, pei_list_length. lia.
Qed.

(** bv_carrier_eval：逐点值 == tⁿ(1−t)^{2n+1}·Σ_{m≤M} C(n+m,n)(t²)^m（负二项型截断）。 *)
Theorem bv_carrier_eval : forall (n M : nat) (t : Q),
  pint_eval (bv_carrier n M) t ==
  q_pow t n * q_pow (1 - t)%Q (2 * n + 1) *
    bk_psQ (fun m : nat => (Z.of_nat (bkC (n + m) n) # 1)%Q)
           (Datatypes.S M) (t * t)%Q.
Proof.
  intros n M. induction M as [| m IH]; intro t.
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                   (Datatypes.S 0) (t * t)%Q)
      with (0 + (Z.of_nat (bkC (n + 0) n) # 1) * 1)%Q.
    rewrite pei_eval_scale, pei_beta_eval.
    replace (n + 2 * 0)%nat with n%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    rewrite pei_eval_add, pei_eval_scale, pei_beta_eval, bv_pad_eval, IH.
    assert (HpsQ : bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S (Datatypes.S m)) (t * t)%Q
                   == bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S m) (t * t)%Q
                      + (Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q
                          * q_pow (t * t)%Q (Datatypes.S m))
      by reflexivity.
    rewrite HpsQ.
    rewrite (q_pow_add t n (2 * Datatypes.S m)).
    replace (2 * Datatypes.S m)%nat with (Datatypes.S m + Datatypes.S m)%nat by lia.
    rewrite (q_pow_add t (Datatypes.S m) (Datatypes.S m)).
    rewrite <- (bk_q_pow_mul t t (Datatypes.S m)).
    ring.
Qed.

(* ============================================================ *)
(* §C 截断积分：bv_carrier_value 精确值、bv_sum_mono 单调、bv_sum_pos 正性  *)
(* ============================================================ *)

Fixpoint bv_zeros (L : nat) : list Q :=
  match L with
  | 0 => nil
  | Datatypes.S m => 0%Q :: bv_zeros m
  end.

Lemma bv_zeros_length : forall L : nat, length (bv_zeros L) = L.
Proof.
  induction L as [| l IH].
  - reflexivity.
  - cbn [bv_zeros length]. rewrite IH. reflexivity.
Qed.

Lemma bv_zeros_int : forall (L k : nat), pint_integral_from (bv_zeros L) k == 0%Q.
Proof.
  induction L as [| l IH]; intros k.
  - reflexivity.
  - cbn [bv_zeros pint_integral_from]. unfold pint_monomial_int.
    rewrite pint_zero_div, Qplus_0_l. apply IH.
Qed.

Theorem bv_zeros_int0 : forall L : nat, pint_integral (bv_zeros L) == 0%Q.
Proof. intro L. unfold pint_integral. apply bv_zeros_int. Qed.

Lemma bv_c_pos_le : forall n m : nat, QleT' 0 ((Z.of_nat (bkC (n + m) n) # 1)%Q).
Proof.
  intros n m. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hb : 1 <= bkC (n + m) n) by (apply bkC_pos; lia).
  assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma bv_pos_cint : forall n m : nat,
  QleT' 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1))).
Proof.
  intros n m.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply pei_beta_pos.
Qed.

(** bv_carrier_value：截断积分 == 级数部分和 Σ_{m≤M} bv_term n m（精确 QeqT）。 *)
Theorem bv_carrier_value : forall n M : nat,
  pint_integral (bv_carrier n M) == sum_upto (Datatypes.S M) (fun m : nat => bv_term n m).
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                   (pei_list (n + 2 * 0) (2 * n + 1)))).
    rewrite pei_beta_value. unfold bv_term.
    replace (n + 2 * 0)%nat with n%nat by lia.
    replace (3 * n + 2 * 0 + 2)%nat with (n + (2 * n + 1) + 1)%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite bv_pad_int.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                   (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))).
    rewrite pei_beta_value, IH. unfold bv_term.
    replace ((n + 2 * Datatypes.S m) + (2 * n + 1) + 1)%nat
      with (3 * n + 2 * Datatypes.S m + 2)%nat by lia.
    ring.
Qed.

(** bv_sum_mono：截断积分对 M 单调（QleT'）；由 PintMono 的 pm_scale_mono、
   pm_add_mono 与同值替换 pm_qle_wd_l、pm_qle_wd_r 合成。 *)
Theorem bv_sum_mono : forall n M : nat,
  QleT' (pint_integral (bv_carrier n M))
        (pint_integral (bv_carrier n (Datatypes.S M))).
Proof.
  intros n M.
  change (pint_integral (bv_carrier n (Datatypes.S M)))
    with (pint_integral (pint_add
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)))).
  assert (Hlen : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n M))).
  { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
  assert (HId1 : Id (length (bv_zeros (3 * n + 2 * M + 2 + 2)))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite bv_zeros_length, bv_pad_length, bv_carrier_length. reflexivity. }
  assert (HId2 : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite <- Hlen. reflexivity. }
  (* 中间断言 HleX：0 ≤ C(n+M,n)·∫t^{n+2M}(1−t)^{2n+1}，经 bv_c_pos_le、bv_pos_cint 与 pm_scale_mono。 *)
  assert (HleX : QleT' 0 (pint_integral
                    (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))).
  { apply (pm_qle_wd_r
             (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
               pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
             (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
             0%Q).
    - apply Qeq_sym. apply qeqT_imp_qeq.
      apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
    - apply (pm_qle_wd_l
               (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                          (bv_zeros (3 * n + 2 * M + 2 + 2))))
               0%Q
               (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                 pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)).
      + transitivity (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                       pint_integral (bv_zeros (3 * n + 2 * M + 2 + 2)))%Q).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (bv_zeros (3 * n + 2 * M + 2 + 2))).
        * rewrite bv_zeros_int0. apply Qmult_0_r.
      + apply (pm_qle_wd_r
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                 (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                   pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (bv_zeros (3 * n + 2 * M + 2 + 2))))).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
        * apply (pm_scale_mono ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                   (bv_zeros (3 * n + 2 * M + 2 + 2))
                   (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
          -- apply bv_c_pos_le.
          -- apply (pm_qle_wd_l 0%Q _ _).
             ++ apply Qeq_sym. apply bv_zeros_int0.
             ++ apply bv_pos_cint. }
  (* 中间断言 Hmove：bv_zeros 与 bv_pad (bv_carrier n M) 之和的积分 == pint_integral (bv_carrier n M)。 *)
  assert (Hmove : pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                          (bv_pad (bv_carrier n M)))
                 == pint_integral (bv_carrier n M)).
  { assert (HLz : length (bv_zeros (3 * n + 2 * M + 2 + 2))
                  = length (bv_pad (bv_carrier n M)))
      by (rewrite bv_zeros_length, bv_pad_length, bv_carrier_length; reflexivity).
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HLz)).
    rewrite bv_zeros_int0, bv_pad_int. ring. }
  apply (pm_qle_wd_l
           (pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                    (bv_pad (bv_carrier n M))))
           (pint_integral (bv_carrier n M))
           (pint_integral (pint_add
                (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                (bv_pad (bv_carrier n M))))).
  - exact Hmove.
  - apply (pm_add_mono (bv_zeros (3 * n + 2 * M + 2 + 2))
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)) (bv_pad (bv_carrier n M))).
    + exact HId1.
    + exact HId2.
    + apply (pm_qle_wd_l 0%Q _ _).
      * apply Qeq_sym. apply bv_zeros_int0.
      * exact HleX.
    + apply qleT'_refl.
Qed.

(* bv_sum_upto_pos：部分和严格正（对 M 归纳；由 bv_term_pos 与 pei_lt_le_plus） *)
Lemma bv_sum_upto_pos : forall n M : nat,
  QltT 0 (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n. induction M as [| m IH].
  - change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    apply Qlt_to_QltT.
    apply (pei_qeq_lt (bv_term n 0) (0 + bv_term n 0)%Q 0%Q).
    + ring.
    + apply QltT_to_Qlt. apply bv_term_pos.
  - change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    apply Qlt_to_QltT. apply pei_lt_le_plus.
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply bv_term_pos.
Qed.

(** bv_sum_pos：截断积分严格正——由 bv_carrier_value 换为部分和，再用 bv_sum_upto_pos。 *)
Theorem bv_sum_pos : forall n M : nat,
  QltT 0 (pint_integral (bv_carrier n M)).
Proof.
  intros n M. apply Qlt_to_QltT.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m))
                    (pint_integral (bv_carrier n M)) 0%Q).
  - apply Qeq_sym. apply bv_carrier_value.
  - apply QltT_to_Qlt. apply bv_sum_upto_pos.
Qed.

(* ============================================================ *)
(* §D ln2 系数离散核：bv_delannoy_eq_qtilde（升幂 Delannoy 和 == q̃_n）    *)
(*   bv_D_asc n == Σ_{a≤n} C(n,a)²·2^a（经 bk_psd_ext、bk_Qn_sym 调整次序）；*)
(*   系数恒等式：[u^n](u−1)ⁿ(2−u)ⁿ = Σ_{a+b=n} C(n,a)C(n,b)2^{n−b}(−1)^{n−a+b}；*)
(*   取 b=n−a 时符号 (−1)^{2n−2a}=1，故 = Σ_a C(n,a)²2^a = D_n = q̃_n。   *)
(* ============================================================ *)

Definition bv_D_asc (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

Theorem bv_delannoy_eq_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bv_D_asc n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_D_asc.
  assert (H : bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n)
              = bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n)).
  { apply bk_psd_ext. intros k Hk.
    rewrite (bk_Qn_sym n k) by lia. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* ============================================================ *)
(* §E 分子闭式 bv_p（Laurent 系数符号和）与数值锚组                        *)
(*   p_n = −Σ_{j≠n, j≤2n} c_j·(2^{j−n}−1)/(j−n)（锚值 p: 0, 2, 9, 131/3）。*)
(* ============================================================ *)

Fixpoint bv_negpow (k : nat) : Q :=
  match k with
  | 0 => 1%Q
  | Datatypes.S k' => (- bv_negpow k')%Q
  end.

(* 2 的带符号幂（Z 指数） *)
Definition bv_q2 (k : Z) : Q :=
  match Z.leb 0 k with
  | true => q_pow (2 # 1)%Q (Z.to_nat k)
  | false => 1%Q / q_pow (2 # 1)%Q (Z.to_nat (Z.opp k))
  end.

(* Laurent 系数 c_j = (−1)^{n+j}·Σ_{a≤j, a≤n, j−a≤n} C(n,a)C(n,j−a)2^{n−(j−a)} *)
Definition bv_c (n j : nat) : Q :=
  bv_negpow (n + j) *
  bk_psQ (fun a : nat =>
            if andb (Nat.leb a n) (Nat.leb (j - a) n)
            then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                  q_pow (2 # 1)%Q (n - (j - a)))%Q
            else 0%Q)
         (Datatypes.S j) 1%Q.

(* bv_p：分子闭式（闭式见 §E；Laurent 系数符号和） *)
Definition bv_p (n : nat) : Q :=
  (- bk_psQ (fun j : nat =>
               if Nat.eqb j n then 0%Q
               else (bv_c n j *
                     ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))
            (Datatypes.S (2 * n)) 1%Q)%Q.

(* 真归一近似子 x_n := p_n/q̃_n（定形：无 2 幂） *)
Definition bv_x (n : nat) : Q := bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.

(* bv_x2pow：2 幂归一形 x''_n := p_n/(2^n·q̃_n)，与真归一形不相容（见 bv_x2pow_sep1） *)
Definition bv_x2pow (n : nat) : Q :=
  bv_p n / (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.

(* ---- 数值锚组（各锚由 vm_compute 精确判定）---- *)

Theorem bv_q1_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 1) # 1)%Q) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c11_anchor : QeqT (bv_c 1 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c22_anchor : QeqT (bv_c 2 2) (13 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c33_anchor : QeqT (bv_c 3 3) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p0_anchor : QeqT (bv_p 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p1_anchor : QeqT (bv_p 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p2_anchor : QeqT (bv_p 2) (9 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p3_anchor : QeqT (bv_p 3) (131 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x0_anchor : QeqT (bv_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x1_anchor : QeqT (bv_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x2_anchor : QeqT (bv_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 跨变体核对：bv_p 2 == 9，与原变体关系 r_2 == 2^{3}·p_2 == 72 一致。 *)
Theorem bv_cross2_anchor : QeqT ((bv_p 2 * (Z.of_nat 8 # 1))%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** bv_x2pow_sep1：分离见证——bv_x2pow 1 == 1/3 < 2/3 == bv_x 1（QltT，Set 层）。 *)
Theorem bv_x2pow_sep1 : QltT (bv_x2pow 1) (bv_x 1).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。        *)
(* ============================================================ *)

Print Assumptions bv_delannoy_eq_qtilde.
Print Assumptions bv_term_pos.
Print Assumptions bv_carrier_eval.
Print Assumptions bv_carrier_value.
Print Assumptions bv_sum_mono.
Print Assumptions bv_sum_pos.
Print Assumptions bv_p3_anchor.
Print Assumptions bv_x2pow_sep1.
