(* ============================================================ *)
(* ExpNegPosUp.v                                                 *)
(*                                                               *)
(* 目的：给出 exp(−x) 偶档部分和在全 x ≥ 0 上的严格正性出口件，     *)
(*       即 S03 的 exp_even_neg_pos 的 Set 层转译。                *)
(* 主件：enpx_exp_partial_even_pos_all :                          *)
(*       forall (x : Q) (m : nat), QleT' 0 x ->                   *)
(*       QltT 0 (exp_partial (2 * m) (Qopp x))；                   *)
(*       伴件 enpx_exp_partial_even_nonneg_all 给出非负形。         *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；               *)
(*       Stdlib QArith.QArith、Arith.Arith、Lia。                   *)
(* 备注：奇档情形存在反例 S₁(−3) = 1 − 3 = −2 < 0，故奇档部分和     *)
(*       的全 x ≥ 0 正性不在此列，本件仅陈述偶档 2 * m；            *)
(*       最终正性（∀ x ≥ 0, ∃ N, ∀ n ≥ N, 0 < S_n）可依据 S03 的    *)
(*       exp_partial_odd / exp_partial_even_lower 另行打包。        *)
(*       全件 Qed；无公理、无承认式、无经典逻辑；语句面             *)
(*       QleT' / QltT 全为 Set 层。                                *)
(* ============================================================ *)

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
  apply Qlt_to_QltT.
  exact (exp_even_neg_pos x m (QleT'_to_Qle 0 x H0)).
Qed.

(* 伴件：偶档非负形（主件经 qltT_leT' 一步，供序链消费） *)
Theorem enpx_exp_partial_even_nonneg_all : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' 0 (exp_partial (2 * m) (Qopp x)).
Proof.
  intros x m H0.
  apply qltT_leT'.
  exact (enpx_exp_partial_even_pos_all x m H0).
Qed.

(* 奇档假命题边界登记（诚实形态声明，非证明目标）：
   S₁(−3) = 1 − 3 = −2 < 0，故"奇档全 x≥0 正性"不在此列；
   最终正性（∀x≥0, ∃N, ∀n≥N, 0 < S_n）可依据 S03 的
   exp_partial_odd / exp_partial_even_lower 另行打包。 *)

Print Assumptions enpx_exp_partial_even_pos_all.
Print Assumptions enpx_exp_partial_even_nonneg_all.
