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
