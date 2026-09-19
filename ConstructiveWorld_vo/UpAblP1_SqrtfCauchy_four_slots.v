(* ============================================================ *)
(* UpAblP1_SqrtfCauchy_four_slots.v                              *)
(*                                                               *)
(* 席位：FA-P1S1 论文域消融施工席（三换装批·件一）｜日期：20260919    *)
(* 工单：attn/_tfap1_普查报告-20260919.md ④批1（SqrtfCauchy 四槽      *)
(*       换装打包，★★★）；方法论：E-STAGING-FA3 三分类卡（N1 直喂）。  *)
(* 目的：宿主 SqrtfCauchy 六假设位中位2/位4/位5/位6 四位换装——        *)
(*       位1＝SqWall 定义性永久墙位不动（五指针判定标注段见            *)
(*       SqrtfCauchyDischarge §C，W 账在普查③#1）；位3＝件二           *)
(*       UpAblP1_SqrtfCauchyArch_arch 独立承装。                       *)
(* 四位换装账（语句逐字＝宿主声明行的 R:=Real 实例投影形；              *)
(* 证明体全部 exact 一行喂库内放电件，零新数学，E752 喂参法）：         *)
(*   位2 sfc_metric_abs（宿主 :56，消费位 :1277）                       *)
(*       ← sfcx_metric_abs_slot@SqrtfCauchyDischarge:138               *)
(*       （本体 sfcx_metric_abs_real@:130，metric 与 abs(req_minus)    *)
(*       定义性重合，req_refl 一步；接口补装 ReqMetricAbs mixin:148     *)
(*       + 实例 ReqMetricAbsReal:152 随母本在库）。                    *)
(*   位4 sfc_abs_le_plus_eps（宿主 :61-62，消费位 :1283）               *)
(*       ← sfcx_abs_le_plus_eps_slot@SqrtfCauchyDischarge:115          *)
(*       （本体 :58；前提位 Or＝情形数据构造性分解：lt 支               *)
(*       real_abs_pos_req@S07:7280 / eq 支 real_abs_zero_req@:7257）。 *)
(*   位5 Hlt_one_two（宿主 :68，消费位 :115-117 sfc_lt_one_two）        *)
(*       ← sfcx_lt_one_two_slot@SqrtfCauchyDischarge:162               *)
(*       （SCFIX 20260916 件；sfc_two δ 展开＝plus one one 逐字）。     *)
(*   位6 sfc_lt_plus_compat_lt_le（宿主 :73-74，消费位 :1313）          *)
(*       ← sbd_req_lt_plus_compat_lt_le@UpReqStrictBridgeD:51          *)
(*       （实例面换装一步；种子 rlsb_lt_plus_compat_lt_le@              *)
(*       UpReqRealLtShiftBridge:119，两 translate+trans 处方、          *)
(*       Or 分解两支独立组装；与 SCFIX2 线协调＝消费点零改动，          *)
(*       本件独立伴生原树零改）。                                       *)
(* 分级：四位全 N1（普查总表 ④批1 逐位坐标即本件施工图）。              *)
(* 纪律：全 Set 层语句（req/le/lt 接口 Set 值谓词）；零新增挂账声明形；  *)
(*       全 Qed；宿主与只读树零改；前缀 uabp1_（全库实扫零撞名）。       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import SqrtfCauchyDischarge.
Require Import UpReqRealLtShiftBridge.
Require Import UpReqStrictBridgeD.
Import RealInterfaceEnhancedMod.

(* ============ 位2 换装：metric_abs 桥接位（宿主 :56 逐字） ============ *)
Theorem uabp1_sfc_metric_abs_slot :
  forall a b : Real,
  @req Real RealEnhancedReal (@metric Real RealEnhancedReal a b)
       (@abs Real RealEnhancedReal (@req_minus Real RealEnhancedReal a b)).
Proof. exact sfcx_metric_abs_slot. Qed.

(* ============ 位4 换装：abs 锐化 eps 形位（宿主 :61-62 逐字） ============ *)
Theorem uabp1_sfc_abs_le_plus_eps_slot :
  forall t : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) t ->
  forall eps : Real,
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  @le Real RealEnhancedReal (@abs Real RealEnhancedReal t)
      (@plus Real RealEnhancedReal t eps).
Proof. exact sfcx_abs_le_plus_eps_slot. Qed.

(* ============ 位5 换装：1 < 1+1 严格档（宿主 :68 逐字） ============ *)
Theorem uabp1_sfc_lt_one_two_slot :
  @lt Real RealEnhancedReal (@one Real RealEnhancedReal)
      (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
             (@one Real RealEnhancedReal)).
Proof. exact sfcx_lt_one_two_slot. Qed.

(* ============ 位6 换装：严格加法混合保序 lt_le 形（宿主 :73-74 逐字） ==== *)
Theorem uabp1_sfc_lt_plus_compat_lt_le_slot :
  forall a b c d : Real,
  @lt Real RealEnhancedReal a b ->
  @le Real RealEnhancedReal c d ->
  @lt Real RealEnhancedReal (@plus Real RealEnhancedReal a c)
      (@plus Real RealEnhancedReal b d).
Proof. exact sbd_req_lt_plus_compat_lt_le. Qed.

(* ============ G3 提取探针（一人一目录 _tp1s1_g3out） ============ *)
(* 位4/位2 两本体素颜件经本席链复验提取（与上游 sfcx_G3 同判据，预判      *)
(* Obj.magic=0）；四位换装体为序谓词/等词桥面零计算内容，按               *)
(* UpReqRealLtShiftBridge/UpReqStrictBridgeD 先例以说明替代提取。         *)
Set Extraction Output Directory "_tp1s1_g3out".
Extraction "uabp1s1_G3_four.ml" sfcx_abs_le_plus_eps_real
  sfcx_metric_abs_real.

(* ============ G4 探针：假设闭包审计（四位全 Closed 为过关判据） ============ *)
Print Assumptions uabp1_sfc_metric_abs_slot.
Print Assumptions uabp1_sfc_abs_le_plus_eps_slot.
Print Assumptions uabp1_sfc_lt_one_two_slot.
Print Assumptions uabp1_sfc_lt_plus_compat_lt_le_slot.
