(* ==========================================================================)
   UpAblP1_SqrtfCauchy_four_slots.v — 宿主 SqrtfCauchy 四假设位的逐字语句实例化件
   使命: metric_abs 桥接位、abs 锐化 eps 形位、1<1+1 严格档、严格加法混合保序位四位的实例化定理：证明体全部 exact 一行代入库内已证实例件，零新数学；附提取检验（Obj.magic=0）与假设闭包审计（Print Assumptions 全 Closed）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、SqrtfCauchyDischarge、UpReqRealLtShiftBridge、UpReqStrictBridgeD、Extraction。
   对标: 序谓词/等词桥面的逐字语句实例化（宿主声明行的 R:=Real 实例投影形）。
   构造性: 全 Set 层语句（req/le/lt 接口 Set 值谓词）；零新增假设声明形；全 Qed；宿主与只读树零改；前缀 uabp1_ 全库零撞名。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import SqrtfCauchyDischarge.
Require Import UpReqRealLtShiftBridge.
Require Import UpReqStrictBridgeD.
Import RealInterfaceEnhancedMod.

(* ============ 位2 重述：metric_abs 桥接位（宿主 :56 逐字） ============ *)
Theorem uabp1_sfc_metric_abs_slot :
  forall a b : Real,
  @req Real RealEnhancedReal (@metric Real RealEnhancedReal a b)
       (@abs Real RealEnhancedReal (@req_minus Real RealEnhancedReal a b)).
Proof. exact sfcx_metric_abs_slot. Qed.

(* ============ 位4 重述：abs 锐化 eps 形位（宿主 :61-62 逐字） ============ *)
Theorem uabp1_sfc_abs_le_plus_eps_slot :
  forall t : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) t ->
  forall eps : Real,
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  @le Real RealEnhancedReal (@abs Real RealEnhancedReal t)
      (@plus Real RealEnhancedReal t eps).
Proof. exact sfcx_abs_le_plus_eps_slot. Qed.

(* ============ 位5 重述：1 < 1+1 严格档（宿主 :68 逐字） ============ *)
Theorem uabp1_sfc_lt_one_two_slot :
  @lt Real RealEnhancedReal (@one Real RealEnhancedReal)
      (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
             (@one Real RealEnhancedReal)).
Proof. exact sfcx_lt_one_two_slot. Qed.

(* ============ 位6 重述：严格加法混合保序 lt_le 形（宿主 :73-74 逐字） ==== *)
Theorem uabp1_sfc_lt_plus_compat_lt_le_slot :
  forall a b c d : Real,
  @lt Real RealEnhancedReal a b ->
  @le Real RealEnhancedReal c d ->
  @lt Real RealEnhancedReal (@plus Real RealEnhancedReal a c)
      (@plus Real RealEnhancedReal b d).
Proof. exact sbd_req_lt_plus_compat_lt_le. Qed.

(* ============ 提取检验（Obj.magic 计数面） ============ *)
(* 位4/位2 两本体素颜件经同链复核提取（与上游 sfcx_G3 同判据，预判      *)
(* Obj.magic=0）；四位重述体为序谓词/等词桥面零计算内容，按               *)
(* UpReqRealLtShiftBridge/UpReqStrictBridgeD 先例以说明替代提取。         *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_four.ml" sfcx_abs_le_plus_eps_real
  sfcx_metric_abs_real.

(* ============ G4 检验：假设闭包审计（四位全 Closed 为过关判据） ============ *)
Print Assumptions uabp1_sfc_metric_abs_slot.
Print Assumptions uabp1_sfc_abs_le_plus_eps_slot.
Print Assumptions uabp1_sfc_lt_one_two_slot.
Print Assumptions uabp1_sfc_lt_plus_compat_lt_le_slot.
