(* ============================================================ *)
(* ToyR 玩具证替换件 —— T263 台账席 战役包X（tier2 十四批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabT9_debt_ctxRIS_sqrt_witness（原 L27，2 句玩具证）                 *)
(*   uabT9_debt_ctxR_premise_le（原 L19，2 句玩具证）                     *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T337 恒等守恒更正注记】2026-09-22 包AW十三 台账席（恒等头注更正第三批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337 台账。 *)
(* 附记：T277 判级全文恒等；M-Z 域未及件（V 收尾＋X 整包＋Y 起步）第四批直推（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblT9_UpDebtSqrtAbsReq.v —— T9 批 Context 实例束·UpDebtSqrtAbsReq 辖区 *)
(* 被消融位（普查表 §2 UpDebtSqrtAbsReq 行）：                             *)
(*   位1 UpDebtSqrtAbsReq.v:24  Context {R : Set}                          *)
(*   位2 UpDebtSqrtAbsReq.v:25  Context {RIS : RealInterfaceEnhancedSetoid R} *)
(* 代表定理（Section SqrtAbsReq 内零数据槽、纯 Context 依赖件）：           *)
(*   位1 ←req_sqrt_premise_le_intro@:65                                    *)
(*   位2 ←req_sqrt_witness_exists_abstract@:76（旗舰出节件形态）            *)
(* 分级：两位全 N1（库内件直连，出节定理在具体实例位逐字材料化）。          *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、     *)
(*   UpDebtSqrtAbsReq。                                                    *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpDebtSqrtAbsReq.
Import RealInterfaceEnhancedMod.

(* 位1 ←:24（rep@:65；R 实例位材料化） *)
Theorem uabT9_debt_ctxR_premise_le :
  forall d : Real, Or (lt zero d) (req zero d) -> le zero d.
Proof.
  intro d.
  exact (@req_sqrt_premise_le_intro Real RealEnhancedReal d).
Qed.

(* 位2 ←:25（rep@:76 旗舰；RIS 实例位材料化） *)
Theorem uabT9_debt_ctxRIS_sqrt_witness :
  forall d : Real,
    Or (lt zero d) (req zero d) ->
    sigT (fun r : Real => And (le zero r) (req (mult r r) d)).
Proof.
  intro d.
  exact (@req_sqrt_witness_exists_abstract Real RealEnhancedReal d).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_debt_ctxR_premise_le.
Print Assumptions uabT9_debt_ctxRIS_sqrt_witness.
