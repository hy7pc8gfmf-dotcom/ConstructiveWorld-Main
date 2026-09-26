(* ==========================================================================)
   UpAblT9_UpDebtSqrtAbsReq.v — Context 实例束之 UpDebtSqrtAbsReq 辖区材料化件
   使命: Context {R}/{RIS} 两实例位在具体 Real 实例上的材料化——req_sqrt_premise_le_intro 与 req_sqrt_witness_exists_abstract 的逐字特化定理。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpDebtSqrtAbsReq。
   对标: 平方根见证存在性的具体实例层（无直接对应物）。
   构造性: 全 Qed 闭合、零承认词面；库内件直连，出节定理在具体实例位逐字材料化；只读依赖，原树零改。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)
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

(* 位2 ←:25（rep@:76 主定理；RIS 实例位材料化） *)
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
