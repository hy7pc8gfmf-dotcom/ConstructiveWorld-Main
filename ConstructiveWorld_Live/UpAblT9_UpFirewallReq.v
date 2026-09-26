(* ==========================================================================)
   UpAblT9_UpFirewallReq.v — Context 实例束之 UpFirewallReq 辖区材料化件
   使命: Context {R}/{RIS} 两实例位在具体 Real 实例上的材料化——fw_double_pos 与 req_fw_lt_double 的逐字特化定理；位 2 出节签名所携 lt_plus_compat 前提如实注记。
   依赖: CW_ConstructiveWorld_219、UpFirewallReq。
   对标: 温度 firewall 假设位的具体实例层（无直接对应物）。
   构造性: 全 Qed 闭合、零承认词面；库内件直连，出节定理在具体实例位逐字材料化；只读依赖，原树零改。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)
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
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* 位1 ←:62（rep@:175；R 实例位材料化） *)
Theorem uabT9_fw_ctxR_double_pos :
  forall t : Real, lt zero t -> lt zero (plus t t).
Proof.
  intros t Ht.
  exact (@fw_double_pos Real RealEnhancedReal t Ht).
Qed.

(* 位2 ←:63（rep@:182；RIS 实例位材料化；:103 位前提显式参，单参形同出节签名） *)
Theorem uabT9_fw_ctxRIS_lt_double :
  forall (lpc : forall (a b c d : Real),
            lt a b -> le c d -> lt (plus a c) (plus b d)),
    forall t : Real, lt zero t -> lt t (plus t t).
Proof.
  intros lpc t Ht.
  exact (@req_fw_lt_double Real RealEnhancedReal lpc t Ht).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_fw_ctxR_double_pos.
Print Assumptions uabT9_fw_ctxRIS_lt_double.
