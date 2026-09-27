(* ==========================================================================)
   ExpOneEnvelope —— QltT'/QleT' 判定桥、eoe_fact_mono/eoe_term_pos/eoe_step_pos 单调正性族、eoe_abs_bound/；同域语句面
   使命：本件形式化QltT'/QleT' 判定桥、eoe_fact_mono/eoe_term_pos/eoe_step_pos 单调正性族、eoe_abs_bound/。
   本件并载：exp(−x) 偶奇分档最终正性定理（∃N 门限形）；exp(−x) 偶档部分和全 x ≥ 0 严格正性件；elv_exp_partial_ge_lin（1+x ≤ exp_partial n x）、elv_exp_partial_le_one（0≤x≤1 时。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, QArith.QArith, QArith.Qabs, Arith.Arith, Setoid, Lia
     S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5,
     S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, Morphisms, QArith.Qminmax, ExpNegPos。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §8 exp(−x) 偶奇分档最终正性定理（∃N 门限形） ============================ *)
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
    - exact Z.lt_0_1.
    - exact (QleT'_to_Qle 1 C HC1). }
  setoid_rewrite Hf.
  apply (Qlt_le_trans _ (Qinv (2 * C)) _).
  - apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 2 C).
    + exact (Z.lt_succ_diag_r 1).
    + apply (Qlt_le_trans 0 1 C).
      * exact Z.lt_0_1.
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

(* 偶奇拆分（Set 层 sigT 封装）：兼容性：9.1 下 Nat.Even_or_Odd 为 Prop 层
   or，向 Set 目标消除被禁；改用 stdlib div2/odd 判定的 Set 层拆分
   （商 m 与奇偶标记 b，恒等件 Nat.div2_odd）。 *)
Lemma enpf_split_even_odd : forall n : nat,
  sigT (fun m : nat => sigT (fun b : bool => n = 2 * m + (if b then 1 else 0))%nat).
Proof.
  intro n.
  refine (existT _ (Nat.div2 n) _).
  refine (existT _ (Nat.odd n) _).
  exact (Nat.div2_odd n).
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
    - exact Qle_0_1.
    - exact HM1. }
  assert (HxM : Qle x (1 + x)).
  { apply (Qle_trans x (x + 1) (1 + x)).
    - apply (Qle_plus_nonneg_r x 1). exact Qle_0_1.
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
    assert (Hk0 : (m0 <= k)%nat).
    { rewrite !Nat.add_1_r in Hn.
      apply (proj2 (Nat.mul_le_mono_pos_l m0 k 2 (Nat.lt_0_succ 1))).
      exact (proj2 (Nat.succ_le_mono (2 * m0) (2 * k)) Hn). }
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k + 1) (Qopp x))).
    + exact Hhalfpos.
    + apply Qlt_to_QltT.
      exact (exp_partial_odd_lower (1 + x) C m0 k (Qopp x) HM0 HC1 HC Hm0 Hk0 Hy).
  - (* n 偶（b = false：n = 2k）；0 < 1/(2C) < 1/C ≤ exp_partial (2k) (−x) *)
    assert (Hkz : (2 * k + 0 = 2 * k)%nat) by apply Nat.add_0_r.
    rewrite Hkz.
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k) (Qopp x))).
    + exact Hhalfpos.
    + apply Qlt_to_QltT.
      apply (Qlt_le_trans (1 / (2 * C)) (1 / C) (exp_partial (2 * k) (Qopp x))).
      * exact (enpf_halfC_lt_invC C HC1).
      * exact (exp_partial_even_lower (1 + x) C (Qopp x) k HM0 HC1 HC Hy).
Qed.

Print Assumptions enpf_eventual_pos.

(* ============================ §9 exp(−x) 偶档部分和全 x ≥ 0 严格正性件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* 主件：偶档全 x≥0 严格正（S03 exp_even_neg_pos 的 Set 层转译出口）
   证明：QleT' → Qle（S02 桥）喂 S03 偶档件，Qlt 经 Qlt_to_QltT 回 Set 面 *)
Theorem enpx_exp_partial_even_pos_all : forall (x : Q) (m : nat),
  QleT' 0 x -> QltT 0 (exp_partial (2 * m) (Qopp x)).
Proof.
  intros x m H0.
  exact (Qlt_to_QltT 0 (exp_partial (2 * m) (Qopp x))
    (exp_even_neg_pos x m (QleT'_to_Qle 0 x H0))).
Qed.

(* 伴件：偶档非负形（主件经 qltT_leT' 一步，供序链依存） *)
Theorem enpx_exp_partial_even_nonneg_all : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' 0 (exp_partial (2 * m) (Qopp x)).
Proof.
  intros x m H0.
  exact (qltT_leT' 0 (exp_partial (2 * m) (Qopp x))
    (enpx_exp_partial_even_pos_all x m H0)).
Qed.

(* 奇档假命题边界登记（诚实形态声明，非证明目标）：
   S₁(−3) = 1 − 3 = −2 < 0，故"奇档全 x≥0 正性"不在此列；
   最终正性（∀x≥0, ∃N, ∀n≥N, 0 < S_n）可依据 S03 的
   exp_partial_odd / exp_partial_even_lower 另行封装。 *)

Print Assumptions enpx_exp_partial_even_pos_all.
Print Assumptions enpx_exp_partial_even_nonneg_all.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* §0 Set 层出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 B4 §0） *)
(* ============================================================ *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. exact (QltT_to_Qlt x y H). Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  exact (Qle_to_QleT' a c (Qle_trans a b c H (qeq_le b c Hbc))).
Qed.

(* ============================================================ *)
(* §1 序/等小桥：Qeq 运输、乘左单调、倒数反序、除法单调             *)
(* ============================================================ *)

(* ---- Qeq 左端运输：x == y -> y < z -> x < z ---- *)
Lemma eoe_lt_eq_l : forall x y z : Q, x == y -> Qlt y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. exact (Qle_lt_trans x y z (qeq_le x y Hxy) Hyz).
Qed.

(* ---- Qeq 右端运输：x < y -> y == z -> x < z ---- *)
Lemma eoe_lt_eq_r : forall x y z : Q, Qlt x y -> y == z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz.
  exact (Qlt_le_trans x y z Hxy (qeq_le y z Hyz)).
Qed.

(* ---- 乘左单调（Qmult_le_compat_r 的项序桥：u*v ≤ u*w） ---- *)
Lemma eoe_mult_le_l : forall u v w : Q, Qle v w -> Qle 0 u -> Qle (u * v) (u * w).
Proof.
  intros u v w Hvw Hu.
  exact (Qle_trans (u * v) (v * u) (u * w)
           (qeq_le (u * v) (v * u) (Qmult_comm u v))
           (Qle_trans (v * u) (w * u) (u * w)
              (Qmult_le_compat_r v w u Hvw Hu)
              (qeq_le (w * u) (u * w) (Qmult_comm w u)))).
Qed.

(* ---- 倒数反序（Qle 形）：0 < x -> 0 < y -> y ≤ x -> /x ≤ /y ---- *)
Lemma eoe_qinv_le : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qle y x -> Qle (/ x) (/ y).
Proof.
  intros x y Hx Hy Hyx.
  destruct (Qle_lt_or_eq y x Hyx) as [Hlt | Heq].
  - exact (Qlt_le_weak (/ x) (/ y) (proj1 (Qinv_lt_contravar y x Hy Hx) Hlt)).
  - rewrite Heq. exact (Qle_refl (/ x)).
Qed.

(* ---- 除法单调（Qle 形）：同分子、正分母，大分母商更小 ---- *)
Lemma eoe_div_le : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qle z y -> Qle (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  exact (Qle_trans (a / y) (/ y * a) (a / z)
           (qeq_le (a / y) (/ y * a) (Qmult_comm a (/ y)))
           (Qle_trans (/ y * a) (/ z * a) (a / z)
              (Qmult_le_compat_r (/ y) (/ z) a (eoe_qinv_le y z Hy Hz Hzy)
                 (Qlt_le_weak 0 a Ha))
              (qeq_le (/ z * a) (a / z) (Qmult_comm (/ z) a)))).
Qed.

(* ---- 除法单调（Qlt 形）：严格版 ---- *)
Lemma eoe_div_lt : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qlt z y -> Qlt (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  exact (eoe_lt_eq_l (a / y) (/ y * a) (a / z)
           (Qmult_comm a (/ y))
           (eoe_lt_eq_r (/ y * a) (/ z * a) (a / z)
              (Qmult_lt_compat_r (/ y) (/ z) a Ha
                 (proj1 (Qinv_lt_contravar z y Hz Hy) Hzy))
              (Qmult_comm (/ z) a))).
Qed.

(* ============================================================ *)
(* §2 阶乘序结构（支撑件 1：n! 单调正，≥ max(1, n)）               *)
(* ============================================================ *)

Lemma eoe_fact_ge_one : forall k : nat, Qle (1%Q) (q_fact k).
Proof.
  induction k as [| k IH].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1))).
    + unfold Qle. simpl. lia.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * (1%Q))).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
        -- apply eoe_mult_le_l.
           ++ exact IH.
           ++ unfold Qle. simpl. lia.
        -- apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_ge_self : forall k : nat, Qle (Z.of_nat k # 1) (q_fact k).
Proof.
  intro k. destruct k as [| j].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * (1%Q))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      * apply eoe_mult_le_l.
        -- apply eoe_fact_ge_one.
        -- unfold Qle. simpl. lia.
      * apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_step_ge : forall k : nat, Qle (q_fact k) (q_fact (Datatypes.S k)).
Proof.
  intro k.
  apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
  - apply (Qle_trans _ (q_fact k * (Z.of_nat (Datatypes.S k) # 1))).
    + apply (Qle_trans _ (q_fact k * 1%Q)).
      * apply qeq_le. ring.
      * apply eoe_mult_le_l.
        -- unfold Qle. simpl. lia.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply q_fact_pos.
    + apply qeq_le. ring.
  - apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_mono_add : forall d a : nat, Qle (q_fact a) (q_fact (a + d)).
Proof.
  intros d a. induction d as [| d IH].
  - replace (a + 0)%nat with a by lia. apply Qle_refl.
  - replace (a + Datatypes.S d)%nat with (Datatypes.S (a + d)) by lia.
    apply (Qle_trans _ (q_fact (a + d))).
    + exact IH.
    + exact (eoe_fact_step_ge (a + d)).
Qed.

Lemma eoe_fact_mono : forall a b : nat, (a <= b)%nat -> Qle (q_fact a) (q_fact b).
Proof.
  intros a b Hab.
  replace b with (a + (b - a))%nat by lia.
  exact (eoe_fact_mono_add (b - a) a).
Qed.

(* ============================================================ *)
(* §3 部分和序结构（支撑件 2：正项 ⟹ 递增；2/n! 恒正）             *)
(* ============================================================ *)

Lemma eoe_q_pow_one : forall n : nat, q_pow 1 n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow 1 (Datatypes.S n)) with (1 * q_pow 1 n).
    rewrite IH. apply Qmult_1_l.
Qed.

Lemma eoe_two_fact_pos : forall n : nat, Qlt 0 ((1 + 1)%Q / q_fact n).
Proof.
  intro n.
  apply (eoe_lt_eq_l _ (0 * / q_fact n)).
  - rewrite Qmult_0_l. reflexivity.
  - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ q_fact n)).
    + apply Qinv_lt_0_compat. apply q_fact_pos.
    + unfold Qlt. simpl. lia.
Qed.

Lemma eoe_term_pos : forall n : nat,
  Qlt 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intro n. rewrite (eoe_q_pow_one (Datatypes.S n)).
  exact (eoe_lt_eq_r 0 (/ q_fact (Datatypes.S n)) (1 / q_fact (Datatypes.S n))
           (Qinv_lt_0_compat (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n)))
           (Qeq_sym (1 * / q_fact (Datatypes.S n)) (/ q_fact (Datatypes.S n))
              (Qmult_1_l (/ q_fact (Datatypes.S n))))).
Qed.

Lemma eoe_step_pos : forall n : nat,
  Qlt 0 (exp_partial (Datatypes.S n) 1 - exp_partial n 1).
Proof.
  intro n.
  assert (Hd : exp_partial (Datatypes.S n) 1 - exp_partial n 1 ==
               q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
  { simpl. ring. }
  exact (eoe_lt_eq_r 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n))
           (exp_partial (Datatypes.S n) 1 - exp_partial n 1)
           (eoe_term_pos n) (Qeq_sym _ _ Hd)).
Qed.

Lemma eoe_mono_add : forall d m : nat, Qle (exp_partial m 1) (exp_partial (m + d) 1).
Proof.
  intros d m. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    apply (Qle_trans _ (exp_partial (m + d) 1)).
    + exact IH.
    + apply (proj2 (Qle_minus_iff (exp_partial (m + d) 1)
                                  (exp_partial (Datatypes.S (m + d)) 1))).
      apply (Qlt_le_weak 0 (exp_partial (Datatypes.S (m + d)) 1 -
                            exp_partial (m + d) 1)).
      apply eoe_step_pos.
Qed.

Lemma eoe_mono : forall m n : nat, (m <= n)%nat -> Qle (exp_partial m 1) (exp_partial n 1).
Proof.
  intros m n Hmn.
  replace n with (m + (n - m))%nat by lia.
  exact (eoe_mono_add (n - m) m).
Qed.

(* ============================================================ *)
(* §4 尾界显式公式：m ≤ n ⟹ |S_n − S_m| ≤ 2/m!                    *)
(*   （引擎 exp_partial_diff_bound@S03:678，A := Qabs 1）          *)
(* ============================================================ *)

Lemma eoe_one_abs : Qabs 1 == 1.
Proof. apply Qabs_pos. unfold Qle. simpl. lia. Qed.

Lemma eoe_q_pow_one_abs : forall n : nat, q_pow (Qabs 1) n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow (Qabs 1) (Datatypes.S n)) with (Qabs 1 * q_pow (Qabs 1) n).
    rewrite eoe_one_abs. rewrite IH. reflexivity.
Qed.

Lemma eoe_diff_bound : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1))
      ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q).
Proof.
  intros m n H1m Hmn.
  apply (exp_partial_diff_bound 1 (Qabs 1) m n).
  - reflexivity.
  - rewrite eoe_one_abs. unfold Qle. simpl. lia.
  - intros t Hmt. unfold Qle. simpl. lia.
  - exact Hmn.
Qed.

Lemma eoe_tail_explicit : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1)) ((1 + 1)%Q / q_fact m).
Proof.
  intros m n H1m Hmn.
  apply (Qle_trans _ ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q)).
  - apply (exp_partial_diff_bound 1 (Qabs 1) m n).
    + reflexivity.
    + rewrite eoe_one_abs. unfold Qle. simpl. lia.
    + intros t Hmt. unfold Qle. simpl. lia.
    + exact Hmn.
  - apply qeq_le.
    rewrite (eoe_q_pow_one_abs m). unfold Qdiv. ring.
Qed.

(* ---- 对称化（出口主用形）：1 ≤ n ≤ m ⟹ |S_m − S_n| ≤ 2/n! ---- *)
Lemma eoe_abs_Qle : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  Qle (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (eoe_tail_explicit n m H1n Hnm).
Qed.

Theorem eoe_abs_bound : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (Qle_to_QleT' _ _ (eoe_abs_Qle m n H1n Hnm)).
Qed.

(* ============================================================ *)
(* §5 主件：e 的显式有理双区间（sigT 双端点 + 正隙宽 + 全后继夹逼） *)
(*   lo := S_n，hi := S_n + 2/n!，hi − lo == 2/n! > 0，           *)
(*   ∀ m ≥ n：lo ≤ S_m ≤ hi（即 S_n ≤ e 的任一后继近似 ≤ hi）。    *)
(* ============================================================ *)

Theorem eoe_two_sided : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      prod (QltT' 0 (hi - lo))
           (forall m : nat, NatLe n m ->
              prod (QleT' lo (exp_partial m 1))
                   (QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) (hi - lo))))).
Proof.
  intros n H1n.
  exists (exp_partial n 1).
  exists (exp_partial n 1 + (1 + 1)%Q / q_fact n).
  split.
  - (* 隙宽显式：hi − lo == 2/n! > 0 *)
    apply Qlt_to_QltT'.
    assert (Hgap : (exp_partial n 1 + (1 + 1)%Q / q_fact n) - exp_partial n 1 ==
                   (1 + 1)%Q / q_fact n) by ring.
    rewrite Hgap. apply eoe_two_fact_pos.
  - intros m Hnm.
    assert (Hnm' : (n <= m)%nat) by (apply NatLe_drop in Hnm; exact Hnm).
    split.
    + (* 下翼：S_n ≤ S_m（正项递增） *)
      apply Qle_to_QleT'.
      apply eoe_mono. exact Hnm'.
    + (* 上翼：|S_m − S_n| ≤ hi − lo == 2/n!（隙宽显式） *)
      apply (qleT'_weaken _ ((1 + 1)%Q / q_fact n) _).
      * apply eoe_abs_Qle; assumption.
      * ring.
Qed.

(* ============================================================ *)
(* §6 精度可计算支：N := S(ceil(2/eps)) 显式模量（B4 同款纪律）     *)
(* ============================================================ *)

Definition eoe_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling ((1 + 1)%Q / eps))).

Lemma eoe_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt ((1 + 1)%Q / q_fact (eoe_modulus eps)) eps.
Proof.
  intros eps Hlt.
  unfold eoe_modulus.
  assert (Hinv0 : Qlt 0 (/ eps)) by (apply Qinv_lt_0_compat; exact Hlt).
  assert (H2e : Qlt 0 ((1 + 1)%Q / eps)).
  { apply (eoe_lt_eq_l _ (0 * / eps)).
    - rewrite Qmult_0_l. reflexivity.
    - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ eps)).
      + exact Hinv0.
      + unfold Qlt. simpl. lia. }
  remember (Qceiling ((1 + 1)%Q / eps)) as c eqn:Hcdef.
  assert (Hle : Qle ((1 + 1)%Q / eps) (c # 1)) by (rewrite Hcdef; apply Qle_ceiling).
  assert (Hc1 : (1 <= c)%Z).
  { assert (Hlt1 : Qlt 0 (c # 1))
      by (apply (Qlt_le_trans 0 ((1 + 1)%Q / eps) (c # 1)); assumption).
    unfold Qlt in Hlt1. simpl in Hlt1. lia. }
  assert (Hk : Z.of_nat (Z.to_nat c) = c) by lia.
  assert (Hceil : Qle ((1 + 1)%Q / eps) ((Z.of_nat (Z.to_nat c)) # 1))
    by (rewrite Hk; exact Hle).
  (* 2/eps ≤ k#1 ≤ k! ⟹ 2 ≤ k!·eps *)
  assert (H2fact : Qle ((1 + 1)%Q / eps) (q_fact (Z.to_nat c))).
  { apply (Qle_trans _ ((Z.of_nat (Z.to_nat c)) # 1)).
    - exact Hceil.
    - apply eoe_fact_ge_self. }
  assert (Hmul : Qle ((1 + 1)%Q / eps * eps) (q_fact (Z.to_nat c) * eps)).
  { apply Qmult_le_compat_r.
    - exact H2fact.
    - apply (Qlt_le_weak 0 eps). exact Hlt. }
  assert (Hid : (1 + 1)%Q / eps * eps == (1 + 1)%Q).
  { field. intro Hzz. apply (Qlt_not_eq 0 eps Hlt). exact (Qeq_sym _ _ Hzz). }
  assert (H2 : Qle (1 + 1)%Q (q_fact (Z.to_nat c) * eps)).
  { apply (Qle_trans _ ((1 + 1)%Q / eps * eps)).
    - apply qeq_le. symmetry. exact Hid.
    - exact Hmul. }
  (* N = S k 的阶乘 = (k+1)·k! ≥ 2·k!，严格衰减压过 eps *)
  assert (HN2 : Qle (1 + 1)%Q ((Z.of_nat (Datatypes.S (Z.to_nat c))) # 1)).
  { unfold Qle. simpl. lia. }
  assert (Hden : Qle ((1 + 1)%Q * q_fact (Z.to_nat c))
                     (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Z.to_nat c)) # 1) * q_fact (Z.to_nat c))).
    - apply Qmult_le_compat_r.
      + exact HN2.
      + apply (Qlt_le_weak 0 (q_fact (Z.to_nat c))). apply q_fact_pos.
    - apply qeq_le. reflexivity. }
  assert (Hstrict : Qlt (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
  { apply (eoe_lt_eq_l _ (1 * q_fact (Z.to_nat c))).
    - symmetry. apply Qmult_1_l.
    - apply (Qmult_lt_compat_r 1 (1 + 1)%Q (q_fact (Z.to_nat c))).
      + apply q_fact_pos.
      + unfold Qlt. simpl. lia. }
  assert (HqN : Qlt (q_fact (Z.to_nat c)) (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qlt_le_trans (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
    - exact Hstrict.
    - exact Hden. }
  assert (Hdrop : Qlt ((1 + 1)%Q / q_fact (Datatypes.S (Z.to_nat c)))
                      ((1 + 1)%Q / q_fact (Z.to_nat c))).
  { apply (eoe_div_lt (1 + 1)%Q (q_fact (Datatypes.S (Z.to_nat c))) (q_fact (Z.to_nat c))).
    - unfold Qlt. simpl. lia.
    - apply q_fact_pos.
    - apply q_fact_pos.
    - exact HqN. }
  assert (H2inv : Qle ((1 + 1)%Q * / q_fact (Z.to_nat c))
                      ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
  { apply Qmult_le_compat_r.
    - exact H2.
    - apply (Qlt_le_weak 0 (/ q_fact (Z.to_nat c))).
      apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hid2 : (q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c) == eps).
  { field. intro Hzz. apply (q_neq_of_lt (q_fact (Z.to_nat c)) (q_fact_pos (Z.to_nat c))).
    exact Hzz. }
  assert (Hfinal : Qle ((1 + 1)%Q / q_fact (Z.to_nat c)) eps).
  { apply (Qle_trans _ ((1 + 1)%Q * / q_fact (Z.to_nat c))).
    - apply qeq_le. reflexivity.
    - apply (Qle_trans _ ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
      + exact H2inv.
      + apply qeq_le. exact Hid2. }
  apply (Qlt_le_trans _ ((1 + 1)%Q / q_fact (Z.to_nat c))).
  - exact Hdrop.
  - exact Hfinal.
Qed.

(* ---- 出口二：sigT 柯西模量（N 显式 = ceil(2/eps)+1，可抽取） ---- *)
Theorem eoe_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (exp_partial m 1 - exp_partial n 1)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (eoe_modulus eps).
  intros m n HNm HNn.
  apply NatLe_drop in HNm.
  apply NatLe_drop in HNn.
  apply Qlt_to_QltT'.
  assert (HN1 : (1 <= eoe_modulus eps)%nat) by (unfold eoe_modulus; lia).
  assert (H1m : (1 <= m)%nat) by lia.
  assert (H1n : (1 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n：|S_n − S_m| ≤ 2/m! ≤ 2/N! < eps *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact m)).
      * rewrite Qabs_Qminus. apply (eoe_tail_explicit m n); assumption.
      * apply (eoe_div_le (1 + 1)%Q (q_fact m) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNm.
    + apply eoe_modulus_bound. exact Hlt.
  - (* n < m：|S_m − S_n| ≤ 2/n! ≤ 2/N! < eps *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact n)).
      * apply (eoe_tail_explicit n m); lia.
      * apply (eoe_div_le (1 + 1)%Q (q_fact n) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNn.
    + apply eoe_modulus_bound. exact Hlt.
Qed.

(* ============================================================ *)
(* §7 假设留痕（红线④：Print Assumptions ≥ 1）                    *)
(* ============================================================ *)

Print Assumptions eoe_two_sided.
Print Assumptions eoe_abs_bound.
Print Assumptions eoe_cauchy_modulus.
Print Assumptions eoe_mono.

(* ============================ §10 elv_exp_partial_ge_lin（1+x ≤ exp_partial n x）、elv_exp_partial_le_one（0≤x≤1 时 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import ExpNegPos.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* 件 1（尾差展开件）：exp_partial 单步定义性展开                       *)
(*   （库版 enp_expSS 同款配方，普适 y 形）                            *)
(* ============================================================ *)

Lemma elv_exp_step_any : forall (n : nat) (y : Q),
  exp_partial (Datatypes.S n) y
  == exp_partial n y
     + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n).
Proof. intros n y. exact (Qeq_refl (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))). Qed.

(* 基座恒等：S_1(x) == 1 + x。
   Qinv (1 * 1) 系非环原子（Qdiv=Qmult x (Qinv y)，ring 不穿），须先桥
   为 1 再 ring（照库版 enp_odd_ge 基座配方）。 *)
Lemma elv_exp1 : forall x : Q, exp_partial 1 x == 1 + x.
Proof.
  intros x.
  replace (exp_partial 1 x)
    with (exp_partial 0 x + q_pow x 1 / q_fact 1) by reflexivity.
  replace (exp_partial 0 x) with 1%Q by reflexivity.
  unfold Qdiv.
  replace (q_pow x 1) with (x * 1) by reflexivity.
  replace (q_fact 1) with (1 * 1) by reflexivity.
  replace (Qinv (1 * 1)) with 1 by reflexivity.
  ring.
Qed.

(* ============================================================ *)
(* 件 2（Prop 内衬主面）：0 ≤ x, 1 ≤ n ⟹ 1 + x ≤ S_n(x)                *)
(*   S_n(x) − (1+x) = Σ_{k=2..n} x^k/k! 逐项非负。                     *)
(* ============================================================ *)

Lemma elv_lin_le_all : forall (x : Q) (n : nat),
  Qle 0 x -> (1 <= n)%nat -> Qle (1 + x) (exp_partial n x).
Proof.
  intros x n Hx0 Hn.
  revert Hn.
  induction n as [| n IH]; intros Hn.
  - (* n = 0 与 1 ≤ n 相斥（Prop 目标内 exfalso+lia 确定性闭） *)
    exfalso. lia.
  - destruct n as [| n'].
    + (* 基座 n = 1：S_1(x) == 1 + x *)
      apply (qeq_le (1 + x) (exp_partial 1 x)).
      apply Qeq_sym. apply elv_exp1.
    + (* 步进 n = S (S n')：尾差展开（Qeq 桥）+ 末项非负传递 *)
      assert (HIH : Qle (1 + x) (exp_partial (Datatypes.S n') x))
        by (apply IH; lia).
      assert (Hterm : Qle 0 (q_pow x (Datatypes.S (Datatypes.S n'))
                             / q_fact (Datatypes.S (Datatypes.S n'))))
        by (apply enp_term_nonneg; exact Hx0).
      apply (Qle_trans (1 + x) (exp_partial (Datatypes.S n') x)
                       (exp_partial (Datatypes.S (Datatypes.S n')) x)).
      * exact HIH.
      * apply (Qle_trans (exp_partial (Datatypes.S n') x)
                         (exp_partial (Datatypes.S n') x
                          + q_pow x (Datatypes.S (Datatypes.S n'))
                            / q_fact (Datatypes.S (Datatypes.S n')))).
        -- (* 原子 LHS 中转 E' + 0 归位（库版 AA21 修②同款，否则
              Qplus_le_compat 的 x+z 统一误 unfold） *)
           apply (Qle_trans (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)
                            (exp_partial (Datatypes.S n') x
                             + q_pow x (Datatypes.S (Datatypes.S n'))
                               / q_fact (Datatypes.S (Datatypes.S n')))).
           ++ apply (qeq_le (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)).
              ** ring.
           ++ apply Qplus_le_compat.
              ** apply Qle_refl.
              ** exact Hterm.
        -- (* 尾差展开同式（Qeq 桥：Qeq 重写不穿 Qle 面） *)
           apply qeq_le. apply Qeq_sym.
           apply (elv_exp_step_any (Datatypes.S n') x).
Qed.

(* ============================================================ *)
(* 件 3（主件·Set 出口）：0 ≤ x, 1 ≤ n ⟹ 1 + x ≤ S_n(x)                *)
(* ============================================================ *)

Theorem elv_exp_partial_ge_lin : forall (x : Q) (n : nat),
  QleT' 0 x -> (1 <= n)%nat -> QleT' (1 + x) (exp_partial n x).
Proof.
  intros x n H0 Hn.
  apply Qle_to_QleT'.
  apply elv_lin_le_all.
  - apply QleT'_to_Qle. exact H0.
  - exact Hn.
Qed.

(* ============================================================ *)
(* 件 4（升华支撑）：Qopp 穿除法 Qeq 桥 + 奇/偶次幂符号归一              *)
(* ============================================================ *)

(* ring 不穿除法：Qopp (u/v) == Qopp u / v（照库版 enp_two_step_odd 配方） *)
Lemma elv_qopp_div : forall u v : Q, Qopp (u / v) == Qopp u / v.
Proof. intros u v. unfold Qdiv. ring. Qed.

(* 奇次：(−x)^{S(2k)} == −x^{S(2k)}（q_pow_neg_odd 指数形 S(2k) 直接匹配） *)
Lemma elv_neg_pow_odd : forall (x : Q) (k : nat),
  q_pow (Qopp x) (Datatypes.S (2 * k))
  == Qopp (q_pow x (Datatypes.S (2 * k))).
Proof. intros x k. exact (q_pow_neg_odd x k). Qed.

(* 偶次：(−x)^{S(S(2k))} == x^{S(S(2k))}（指标归一 S(S 2k) == 2 * S k） *)
Lemma elv_neg_pow_even : forall (x : Q) (k : nat),
  q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * k)))
  == q_pow x (Datatypes.S (Datatypes.S (2 * k))).
Proof.
  intros x k.
  replace (Datatypes.S (Datatypes.S (2 * k)))
    with (2 * Datatypes.S k)%nat by lia.
  apply q_pow_neg_even.
Qed.

(* ============================================================ *)
(* 件 5（升华支撑·偶部归纳，Set 面）：0 ≤ x ≤ 1 ⟹ S_{2m}(−x) ≤ 1        *)
(*   两步尾差 = Qopp u + t2（u := x^{2m+1}/(2m+1)!，t2 ≤ u，            *)
(*   enp_decr）⟹ S_{2m+2} ≤ S_{2m+1} + u = S_{2m} − u + u ≤ 1。        *)
(* ============================================================ *)

Lemma elv_even_le_one : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial (2 * m) (Qopp x)) 1.
Proof.
  intros x m H0 H1.
  induction m as [| m IH].
  - (* 基座：S_0(−x) = 1 *)
    apply qeq_leT'. reflexivity.
  - (* 归纳步：2 * S m 归一 S(S(2m)) 后两步展开 *)
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    apply Qle_to_QleT'.
    (* E1 = S_{2m}(−x) + Qopp u（奇项负性桥，Qeq goal 内归一） *)
    assert (HE1 : exp_partial (Datatypes.S (2 * m)) (Qopp x)
                  == exp_partial (2 * m) (Qopp x)
                     + Qopp (q_pow x (Datatypes.S (2 * m))
                             / q_fact (Datatypes.S (2 * m)))).
    { rewrite (elv_exp_step_any (2 * m) (Qopp x)).
      rewrite (elv_neg_pow_odd x m).
      rewrite elv_qopp_div. reflexivity. }
    apply (Qle_trans
            (exp_partial (Datatypes.S (Datatypes.S (2 * m))) (Qopp x))
            (exp_partial (Datatypes.S (2 * m)) (Qopp x)
             + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
               / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
    + (* 尾差展开同式（Qeq 桥） *)
      apply qeq_le. apply Qeq_sym.
      apply (elv_exp_step_any (Datatypes.S (2 * m)) (Qopp x)).
    + (* 第二肢：LHS 为 Qopp 形，先偶负桥归 x 形，再 enp_decr 配对项差 *)
      apply (Qle_trans
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
      * (* 偶负桥：(−x)^{S(S(2m))} == x^{S(S(2m))}（Qeq 桥） *)
        apply qeq_le.
        rewrite (elv_neg_pow_even x m). reflexivity.
      * apply (Qle_trans
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                   / q_fact (Datatypes.S (Datatypes.S (2 * m))))
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (2 * m))
                   / q_fact (Datatypes.S (2 * m)))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (enp_decr x (Datatypes.S (2 * m))).
              ** apply QleT'_to_Qle. exact H0.
              ** apply QleT'_to_Qle. exact H1.
        -- (* S_{2m+1} + u = S_{2m} − u + u = S_{2m} ≤ 1 *)
           apply (Qle_trans
                   (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                    + q_pow x (Datatypes.S (2 * m))
                      / q_fact (Datatypes.S (2 * m)))
                   (exp_partial (2 * m) (Qopp x))).
           ++ apply qeq_le. rewrite HE1. ring.
           ++ apply QleT'_to_Qle. exact IH.
Qed.

(* ============================================================ *)
(* 件 6（升华·Prop 内衬）：0 ≤ x ≤ 1 ⟹ S_n(−x) ≤ 1                     *)
(*   偶部引用件 5；奇部 S_{2m+1} = S_{2m} − u ≤ S_{2m} ≤ 1              *)
(*   （奇项负性：enp_term_nonneg + Qopp_le_compat，Qopp 0 == 0 桥归）。  *)
(* ============================================================ *)

Lemma elv_exp_le_one_prop : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 -> Qle (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - (* 偶部：n = 2m *)
    subst n.
    apply QleT'_to_Qle.
    apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0) (Qle_to_QleT' _ _ H1)).
  - (* 奇部：n = 2m+1 归一 S(2m) 后单步展开 *)
    subst n.
    replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    apply (Qle_trans (exp_partial (Datatypes.S (2 * m)) (Qopp x))
                     (exp_partial (2 * m) (Qopp x)
                      + Qopp (q_pow x (Datatypes.S (2 * m))
                              / q_fact (Datatypes.S (2 * m))))).
    + (* S_{2m+1} == S_{2m} − u（尾差展开 + 奇负 + Qopp 穿除，Qeq goal 链） *)
      apply qeq_le.
      rewrite (elv_exp_step_any (2 * m) (Qopp x)).
      rewrite (elv_neg_pow_odd x m).
      rewrite elv_qopp_div. reflexivity.
    + (* S_{2m} − u ≤ S_{2m} + 0 ≤ S_{2m} ≤ 1 *)
      apply (Qle_trans (exp_partial (2 * m) (Qopp x)
                        + Qopp (q_pow x (Datatypes.S (2 * m))
                                / q_fact (Datatypes.S (2 * m))))
                       (exp_partial (2 * m) (Qopp x) + 0)).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qle_trans
                    (Qopp (q_pow x (Datatypes.S (2 * m))
                           / q_fact (Datatypes.S (2 * m))))
                    (Qopp 0) 0).
           ++ apply Qopp_le_compat. apply enp_term_nonneg. exact H0.
           ++ apply qeq_le. ring.
      * apply (Qle_trans (exp_partial (2 * m) (Qopp x) + 0)
                         (exp_partial (2 * m) (Qopp x))).
        -- apply qeq_le. ring.
        -- apply QleT'_to_Qle.
           apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0)
                                  (Qle_to_QleT' _ _ H1)).
Qed.

(* ============================================================ *)
(* 件 7（升华主件·Set 出口）：0 ≤ x ≤ 1 ⟹ S_n(−x) ≤ 1                  *)
(* ============================================================ *)

Theorem elv_exp_partial_le_one : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  apply Qle_to_QleT'.
  apply elv_exp_le_one_prop.
  - apply QleT'_to_Qle. exact H0.
  - apply QleT'_to_Qle. exact H1.
Qed.

(* ============================================================ *)
(* 出口公理面审查（G4 留痕）                                            *)
(* ============================================================ *)

Print Assumptions elv_exp_partial_ge_lin.
Print Assumptions elv_exp_partial_le_one.
