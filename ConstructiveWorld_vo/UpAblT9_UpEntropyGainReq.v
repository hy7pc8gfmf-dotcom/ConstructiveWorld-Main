(* ============================================================ *)
(* UpAblT9_UpEntropyGainReq.v —— T9 批 Context 实例束·UpEntropyGainReq 辖区 *)
(* 被消融位（普查表 §2 UpEntropyGainReq 行）：                             *)
(*   位1 UpEntropyGainReq.v:56  Context {R : Set}                          *)
(*   位2 UpEntropyGainReq.v:57  Context {RIS : RealInterfaceEnhancedSetoid R} *)
(* 代表定理（Section EntropyGainReq 内零数据槽、纯 Context 依赖件）：       *)
(*   位1 ←req_eg_minus_def@:95                                             *)
(*   位2 ←req_eg_minus_plus_cancel@:102                                    *)
(* 分级：两位全 N1（库内件直连，出节定理在具体实例位逐字材料化）。          *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、     *)
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
