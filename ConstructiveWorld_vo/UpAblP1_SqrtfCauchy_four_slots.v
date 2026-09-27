(* ==========================================================================)
   UpAblP1_SqrtfCauchy_four_slots.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：sbd_req_lt_plus_compat_lt_le、sbd_log_req_compat、sbd_log_inv_exp_neg_req、sbd_req_lt_plus_compat_le_lt、uabp1_sfc_metric_abs_slot、uabp1_sfc_abs_le_plus_eps_slot、uabp1_sfc_lt_one_two_slot、uabp1_sfc_lt_plus_compat_lt_le_slot。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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
Require Import UpReqRealLtShiftBridge.
Require Import UpReqAlgebra.
From Stdlib Require Import Extraction.
Require Import SqrtfCauchyDischarge.

(* ================= §1 sbd_req_lt_plus_compat_lt_le 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
Import RealInterfaceEnhancedMod.

(* ============ ① 槽1 实例化消解：严格序加法混合保序（lt_le 混合形） ============ *)
(* 参数位语句（UpReqAlgebra ，RealInterfaceEnhancedSetoid Real 字段面）：
   forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)。
   种子 rlsb_lt_plus_compat_lt_le（UpReqRealLtShiftBridge ③）语句逐字同构
   （lt:=real_lt、le:=real_le、plus:=real_plus，Instance RealEnhancedReal
   字段装配 S07:8577/8578/8573），δ 一步重述代入。 *)
Definition sbd_req_lt_plus_compat_lt_le :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d)
  := @rlsb_lt_plus_compat_lt_le.

(* ============ ② 槽2 实例化消解：log 参数 req 兼容 ============ *)
(* 参数位语句（UpReqAlgebra ）：forall x y (Hx : lt zero x) (Hy : lt zero y),
   req x y -> req (log x Hx) (log y Hy)。
   判定路线：real_log_wd（S08:1074，锚点法已验件）语句与槽语句在
   Real 实例面逐字同构（zero:=real_zero、log:=real_log、req:=real_eq），
   直接代入一步，零重述零组装。 *)
Definition sbd_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)
  := @real_log_wd.

(* ============ ③ 槽3 实例化消解：log 对 exp_neg 左逆 ============ *)
(* 参数位语句（UpReqAlgebra ）：forall x, req (log_inv (exp_neg x)
   (exp_neg_pos x)) x。字段装配（Instance RealEnhancedReal）：
   log_inv:=real_log_inv（S07:8656）、exp_neg:=real_exp_neg（S07:8646）、
   exp_neg_pos:=real_exp_neg_pos（S07:8647）。
   链：log_inv y == opp (log y)（real_log_inv_log，S07:7875）
       → opp 换形（RealSetoid.real_eq_opp_compat，S07:255）吃
         real_log_exp_neg（S08:1028：log(e^{-x}) == −x）
       → opp(opp x) == x（real_opp_opp，S08:106）闭合。 *)
Theorem sbd_log_inv_exp_neg_req : forall x : Real,
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  apply (real_eq_trans
           (real_log_inv (real_exp_neg x) (real_exp_neg_pos x))
           (real_opp (real_opp x))
           x).
  - apply (real_eq_trans
             (real_log_inv (real_exp_neg x) (real_exp_neg_pos x))
             (real_opp (real_log (real_exp_neg x) (real_exp_neg_pos x)))
             (real_opp (real_opp x))).
    + exact (real_log_inv_log (real_exp_neg x) (real_exp_neg_pos x)).
    + exact (RealSetoid.real_eq_opp_compat
               (real_log (real_exp_neg x) (real_exp_neg_pos x))
               (real_opp x) (real_log_exp_neg x)).
  - exact (real_opp_opp x).
Qed.

(* ============ ④ 家族闭合伴件：le_lt 形随槽1 实例化消解体闭合 ============ *)
(* UpReqAlgebra.req_lt_plus_compat_le_lt（）出节签名（检验捕获）：
   forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
     (forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
     forall a b c d, le a b -> lt c d -> lt (plus a c) (plus b d)。
   槽1 实例化消解体喂出节首参（discharged 首参位），le_lt 形在 Real 实例上
   无新假设闭合——ReqStrictOrderBridge 族两形式至此全闭。 *)
Definition sbd_req_lt_plus_compat_le_lt :
  forall a b c d : Real, le a b -> lt c d -> lt (plus a c) (plus b d)
  := @req_lt_plus_compat_le_lt Real RealEnhancedReal
       sbd_req_lt_plus_compat_lt_le.

(* ============ 关卡 G4：假设闭包检验（四件全 Closed 为过关判据） ============ *)
Print Assumptions sbd_req_lt_plus_compat_lt_le.
Print Assumptions sbd_log_req_compat.
Print Assumptions sbd_log_inv_exp_neg_req.
Print Assumptions sbd_req_lt_plus_compat_le_lt.
(* ================= §2 uabp1_sfc_metric_abs_slot 族 ================= *)
Import RealInterfaceEnhancedMod.

Theorem uabp1_sfc_metric_abs_slot :
  forall a b : Real,
  @req Real RealEnhancedReal (@metric Real RealEnhancedReal a b)
       (@abs Real RealEnhancedReal (@req_minus Real RealEnhancedReal a b)).
Proof. exact sfcx_metric_abs_slot. Qed.

Theorem uabp1_sfc_abs_le_plus_eps_slot :
  forall t : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) t ->
  forall eps : Real,
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  @le Real RealEnhancedReal (@abs Real RealEnhancedReal t)
      (@plus Real RealEnhancedReal t eps).
Proof. exact sfcx_abs_le_plus_eps_slot. Qed.

Theorem uabp1_sfc_lt_one_two_slot :
  @lt Real RealEnhancedReal (@one Real RealEnhancedReal)
      (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
             (@one Real RealEnhancedReal)).
Proof. exact sfcx_lt_one_two_slot. Qed.

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
