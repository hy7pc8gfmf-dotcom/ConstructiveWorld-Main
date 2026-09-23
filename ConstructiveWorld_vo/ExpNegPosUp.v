(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   enpx_exp_partial_even_nonneg_all（原 L37，3 句玩具证）               *)
(*   enpx_exp_partial_even_pos_all（原 L28，3 句玩具证）                  *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T329 恒等守恒更正注记】2026-09-22 包AV八 台账席（恒等头注更正全量第二批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T329 台账。                   *)
(* 附记：T277 判级全文恒等；包V 起批直推（第二批；承 T321 §五·1 批次滚动）                        *)
(* ============================================================ *)

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
(*       exp_partial_odd / exp_partial_even_lower 另行封装。        *)
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
