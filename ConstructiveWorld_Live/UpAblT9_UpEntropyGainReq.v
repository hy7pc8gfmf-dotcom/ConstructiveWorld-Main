(* ============================================================ *)
(* ToyR 玩具证替换件 —— T263 台账席 战役包X（tier2 十四批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabT9_eg_ctxRIS_minus_plus_cancel（原 L27，2 句玩具证）              *)
(*   uabT9_eg_ctxR_minus_def（原 L19，2 句玩具证）                        *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T337 恒等守恒更正注记】2026-09-22 包AW十三 台账席（恒等头注更正第三批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 参数位＋恒等守恒 2 参数位；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337 台账。 *)
(* 附记：T277 判级全文恒等；M-Z 域未及件（V 收尾＋X 整包＋Y 起步）第四批直推（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblT9_UpEntropyGainReq.v —— T9 批 Context 实例束·UpEntropyGainReq 辖区 *)
(* 被消融位（普查表 §2 UpEntropyGainReq 行）：                             *)
(*   位1 UpEntropyGainReq.v:56  Context {R : Set}                          *)
(*   位2 UpEntropyGainReq.v:57  Context {RIS : RealInterfaceEnhancedSetoid R} *)
(* 代表定理（Section EntropyGainReq 内零数据参数位、纯 Context 依赖件）：       *)
(*   位1 ←req_eg_minus_def@:95                                             *)
(*   位2 ←req_eg_minus_plus_cancel@:102                                    *)
(* 分级：两位全 N1（库内件直连，出节定理在具体实例位逐字材料化）。          *)
(* 依赖（只读依存，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、     *)
(*   UpEntropyGainReq。                                                    *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpEntropyGainReq.
Import RealInterfaceEnhancedMod.

(* 位1 ←:56（rep@:95；R 实例位材料化） *)
Theorem uabT9_eg_ctxR_minus_def :
  forall a b : Real, req (req_minus a b) (plus a (opp b)).
Proof.
  intros a b.
  exact (@req_eg_minus_def Real RealEnhancedReal a b).
Qed.

(* 位2 ←:57（rep@:102；RIS 实例位材料化） *)
Theorem uabT9_eg_ctxRIS_minus_plus_cancel :
  forall a b : Real, req (plus (req_minus a b) b) a.
Proof.
  intros a b.
  exact (@req_eg_minus_plus_cancel Real RealEnhancedReal a b).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_eg_ctxR_minus_def.
Print Assumptions uabT9_eg_ctxRIS_minus_plus_cancel.
