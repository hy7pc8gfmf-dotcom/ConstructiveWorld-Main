(* ============================================================ *)
(* ExpNegFinale.v                                                *)
(*                                                               *)
(* 目的：将 S03 的参数化下界双件（exp_partial_even_lower、         *)
(*       exp_partial_odd_lower）打包为 exp(−x) 的最终正性定理：    *)
(*       ∀ x ≥ 0, ∃ N, ∀ n ≥ N, 0 < exp_partial n (−x)。           *)
(* 主件：enpf_eventual_pos : forall x : Q, QleT' 0 x ->            *)
(*       sigT (fun N : nat => forall n : nat, NatLe N n ->         *)
(*         QltT 0 (exp_partial n (Qopp x)))。                      *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；               *)
(*       Stdlib QArith.QArith、QArith.Qabs、Arith.Arith、Setoid、    *)
(*       Lia。                                                    *)
(* 备注：材料强度经逐字核对 S03 原文：两 lower 件下界形为 1/C（偶档） *)
(*       与 1/(2C)（奇档），均严格正，无"1−x"型约束负担，故取        *)
(*       N := 2·m0+1 分偶奇组装即可，零附加前提。组装骨架仿         *)
(*       S03 cauchy_real_exp_pos 的固定 y = −x 简化：M := 1+x       *)
(*       （0 ≤ M 且 |−x| = x ≤ 1+x），C 由 exp_series_arch 给出     *)
(*       （1 ≤ C 且 ∀n, exp_series n M ≤ C），m0 由                 *)
(*       exp_partial_tail_small 给出。与 ExpNegPosUp.v（前缀 enpx_） *)
(*       互补不冲突：其主件是偶档切面（全 m 严格正、无 N 门限），     *)
(*       本件补齐奇档的最终门限；奇档逐点正性为假命题               *)
(*       （反例 S₁(−3) = −2 < 0），故须门限形。全件 Qed；无公理、     *)
(*       无承认式、无经典逻辑；语句面全 Set，存在见证走 sigT。       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Lia.

(* 辅件一：1/(2C) < 1/C（C ≥ 1）
   证法照抄样板 S03 cauchy_real_exp_pos 偶支首段
   （差 1/C − 1/(2C) == 1/(2C) 经 field + C ≠ 0；再 0 < Qinv(2C) ≤ 1·Qinv(2C)） *)
Lemma enpf_halfC_lt_invC : forall C : Q, QleT' 1 C -> Qlt (1 / (2 * C)) (1 / C).
Proof.
  intros C HC1.
  apply (Qlt_minus_iff (1 / (2 * C)) (1 / C)).
  unfold Qdiv.
  assert (Hf : 1 / C + - (1 / (2 * C)) == 1 / (2 * C)).
  { field.
    apply q_neq_of_lt.
    apply (Qlt_le_trans 0 1 C).
    - reflexivity.
    - exact (QleT'_to_Qle 1 C HC1). }
  setoid_rewrite Hf.
  apply (Qlt_le_trans _ (Qinv (2 * C)) _).
  - apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 2 C).
    + unfold Qlt; simpl; lia.
    + apply (Qlt_le_trans 0 1 C).
      * reflexivity.
      * exact (QleT'_to_Qle 1 C HC1).
  - apply qeq_le. apply Qeq_sym. apply (Qmult_1_l (Qinv (2 * C))).
Qed.

(* 辅件二：0 < 1/(2C) 的 QltT 形（qltT_div_pos + C ≥ 1 链） *)
Lemma enpf_halfC_posT : forall C : Q, QleT' 1 C -> QltT 0 (1 / (2 * C)).
Proof.
  intros C HC1.
  apply (qltT_div_pos 1 (2 * C)).
  - exact qltT_0_1.
  - apply (qmult_ltT_0_compat 2 C).
    + exact qltT_0_2.
    + apply (qltT_leT'_ltT 0 1 C).
      * exact qltT_0_1.
      * exact HC1.
Qed.

(* 偶奇拆分（Set 层 sigT 打包）：兼容性：9.1 下 Nat.Even_or_Odd 为 Prop 层
   or，向 Set 目标消除被禁；改用 stdlib div2/odd 判定的 Set 层拆分
   （商 m 与奇偶标记 b，恒等件 Nat.div2_odd）。 *)
Lemma enpf_split_even_odd : forall n : nat,
  sigT (fun m : nat => sigT (fun b : bool => n = 2 * m + (if b then 1 else 0))%nat).
Proof.
  intro n.
  exact (existT _ (Nat.div2 n)
           (existT _ (Nat.odd n) (Nat.div2_odd n))).
Qed.

(* 主件：exp(−x) 最终正性（∃N 形，材料 = S03 双 lower 参数化件） *)
Theorem enpf_eventual_pos : forall x : Q, QleT' 0 x ->
  sigT (fun N : nat => forall n : nat, NatLe N n -> QltT 0 (exp_partial n (Qopp x))).
Proof.
  intros x Hx.
  assert (Hxle : Qle 0 x) by (exact (QleT'_to_Qle 0 x Hx)).
  (* M := 1+x 的三条桥 *)
  assert (HM1 : Qle 1 (1 + x)) by (apply (Qle_plus_nonneg_r 1 x); exact Hxle).
  assert (HM0 : QleT' 0 (1 + x)).
  { (* 兼容性：目标壳 QleT'（S02 Qle_bool 反映形），Qlt_to_QltT 壳不符——
       走 Qle_to_QleT' + Qle 链 0 ≤ 1 ≤ 1+x *)
    apply Qle_to_QleT'.
    apply (Qle_trans 0 1 (1 + x)).
    - unfold Qle. simpl. lia.
    - exact HM1. }
  assert (HxM : Qle x (1 + x)).
  { apply (Qle_trans x (x + 1) (1 + x)).
    - apply (Qle_plus_nonneg_r x 1). unfold Qle. simpl. lia.
    - apply qeq_le. ring. }
  assert (Hneg : Qle (Qopp x) 0).
  { (* 兼容性：change-with 触发 setoid 自反关系回退报错；Qopp 0 为闭项可转换，直接 apply *)
    apply (Qopp_le_compat 0 x). exact Hxle. }
  assert (Habs : Qabs (Qopp x) == x).
  { rewrite (Qabs_neg (Qopp x) Hneg). apply Qopp_involutive. }
  assert (Hy : QleT' (Qabs (Qopp x)) (1 + x)).
  { apply Qle_to_QleT'. rewrite Habs. exact HxM. }
  (* C：级数指数上界证书（1≤C 且 ∀n, exp_series n M ≤ C） *)
  destruct (exp_series_arch (1 + x) HM0) as [C [HC1 HC]].
  (* m0：奇档尾项小项（∀k≥m0, M^(2k+1)/(2k+1)! < 1/(2C)） *)
  destruct (exp_partial_tail_small (1 + x) C HM0 HC1) as [m0 Hm0].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  pose proof (enpf_halfC_posT C HC1) as Hhalfpos.
  (* N := 2·m0+1（奇偶全覆盖） *)
  exists (2 * m0 + 1)%nat.
  intros n Hn.
  apply NatLe_drop in Hn.
  (* 偶奇拆分（Set 层 sigT，兼容性见 enpf_split_even_odd）；偶档先行，奇档居后 *)
  destruct (enpf_split_even_odd n) as [k [b Hkb]].
  destruct b; subst n.
  - (* n 奇（b = true：n = 2k+1）且 k ≥ m0；0 < 1/(2C) < exp_partial (2k+1) (−x) *)
    assert (Hk0 : (m0 <= k)%nat) by lia.
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k + 1) (Qopp x))).
    + exact Hhalfpos.
    + apply Qlt_to_QltT.
      exact (exp_partial_odd_lower (1 + x) C m0 k (Qopp x) HM0 HC1 HC Hm0 Hk0 Hy).
  - (* n 偶（b = false：n = 2k）；0 < 1/(2C) < 1/C ≤ exp_partial (2k) (−x) *)
    assert (Hkz : (2 * k + 0 = 2 * k)%nat) by lia.
    rewrite Hkz.
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k) (Qopp x))).
    + exact Hhalfpos.
    + apply Qlt_to_QltT.
      apply (Qlt_le_trans (1 / (2 * C)) (1 / C) (exp_partial (2 * k) (Qopp x))).
      * exact (enpf_halfC_lt_invC C HC1).
      * exact (exp_partial_even_lower (1 + x) C (Qopp x) k HM0 HC1 HC Hy).
Qed.

Print Assumptions enpf_eventual_pos.
