(* ==========================================================================)
   UpReqStrictBridgeD.v — 严格序桥的逐槽消解件
   使命: sbd_req_lt_plus_compat_lt_le/le_lt（严格序加法混合保序两形）、sbd_log_req_compat（log 参数 req 兼容）、sbd_log_inv_exp_neg_req（log-exp 左逆）四槽，附假设闭包审计节。
   依赖: CW_ConstructiveWorld_219、UpReqRealLtShiftBridge、UpReqAlgebra；Stdlib QArith。
   对标: 严格/非严格序的加法混合保序与对数-指数桥（实数序代数）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealLtShiftBridge.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* ============ ① 槽1 实例化消解：严格序加法混合保序（lt_le 混合形） ============ *)
(* 槽语句（UpReqAlgebra L1474，RealInterfaceEnhancedSetoid Real 字段面）：
   forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)。
   种子 rlsb_lt_plus_compat_lt_le（UpReqRealLtShiftBridge ③）语句逐字同构
   （lt:=real_lt、le:=real_le、plus:=real_plus，Instance RealEnhancedReal
   字段装配 S07:8577/8578/8573），δ 一步重述代入。 *)
Definition sbd_req_lt_plus_compat_lt_le :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d)
  := @rlsb_lt_plus_compat_lt_le.

(* ============ ② 槽2 实例化消解：log 参数 req 兼容 ============ *)
(* 槽语句（UpReqAlgebra L1498）：forall x y (Hx : lt zero x) (Hy : lt zero y),
   req x y -> req (log x Hx) (log y Hy)。
   判定路线：real_log_wd（S08:1074，锚点法已验件）语句与槽语句在
   Real 实例面逐字同构（zero:=real_zero、log:=real_log、req:=real_eq），
   直接代入一步，零重述零组装。 *)
Definition sbd_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)
  := @real_log_wd.

(* ============ ③ 槽3 实例化消解：log 对 exp_neg 左逆 ============ *)
(* 槽语句（UpReqAlgebra L1502）：forall x, req (log_inv (exp_neg x)
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
(* UpReqAlgebra.req_lt_plus_compat_le_lt（L1478）出节签名（检验捕获）：
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
