(* ==========================================================================)
   UpAblT9_UpEntropyGainReq.v — 实数减法定义与相消律（上下文重述）
   使命: uabT9_eg_ctxR_minus_def（req_minus == a + (−b)）与 uabT9_eg_ctxRIS_minus_plus_cancel（加相消）两件上下文实例。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpEntropyGainReq
   对标: 实数集oid减法的基本代数（定义展开与加法相消律）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)
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
