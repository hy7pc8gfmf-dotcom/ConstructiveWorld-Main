(* ============================================================ *)
(* UpReqStrictBridgeD.v                                          *)
(*                                                              *)
(* 目的： ReqStrictOrderBridge 族三槽放电件（DISCH2 席独立件，      *)
(*   执行 DISCH1 席 STG-B 审计的三张放电判决）。三槽均为 UpReqAlgebra *)
(*   节内假设位（B 类诚实槽位，节闭后非常量、Check 探针 not found），  *)
(*   本件将三槽在 Real 载体实例（RealInterfaceEnhancedSetoid Real，  *)
(*   即 Instance RealEnhancedReal，S07:8566）上逐槽闭合：            *)
(*   ①槽1 严格序加法混合保序槽（UpReqAlgebra L1474）：               *)
(*      lt a b -> le c d -> lt (plus a c) (plus b d)                *)
(*      消费 UpReqRealLtShiftBridge.rlsb_lt_plus_compat_lt_le        *)
(*      （语句逐字同构，real_* 面 → 实例字段面换装）。               *)
(*   ②槽2 log 参数 req 兼容槽（UpReqAlgebra L1498）：                *)
(*      req x y -> req (log x Hx) (log y Hy)                        *)
(*      E372 判决路线：real_log_wd（S08:1074）直喂——种子语句与槽     *)
(*      语句在 Real 实例面逐字同构，零换装一步喂定。                 *)
(*   ③槽3 log 对 exp_neg 左逆槽（UpReqAlgebra L1502）：              *)
(*      req (log_inv (exp_neg x) (exp_neg_pos x)) x                 *)
(*      DISCH1 判决路线（S07 组装注释自供）的 req 版落位：            *)
(*      log_inv_log 升形 + real_log_exp_neg（S08:1028）换形 +        *)
(*      opp 换形（RealSetoid.real_eq_opp_compat）+ real_opp_opp 收口。 *)
(*   ④家族闭合伴件：槽1 放电体喂 UpReqAlgebra.req_lt_plus_compat_le_lt *)
(*      出节首参（discharged 签名已探针捕获），le_lt 形随之闭合——      *)
(*      即 DISCH1「槽1 即可关 ReqStrictOrderBridge 族」判词的落盘。   *)
(* 依赖： CW_ConstructiveWorld_219（S07 实例面 + S08 log 种子）、     *)
(*   UpReqRealLtShiftBridge（槽1 种子）、UpReqAlgebra（出节家族件）。  *)
(*   不依赖 Sqrtf 三件与 SCFIX2/SK91 领地。                          *)
(* 消费面： 槽1/④ = Sqrtf 主件槽5 换装候选（SCFIX2 在飞，本件独立成文  *)
(*   供其后续换装，消费点零改动）；槽2/槽3 = ReqLogBridge 同位桥槽     *)
(*   的 Real 实例喂位（UpReqU2 线同位消解的独立复验）。               *)
(* 命名： 前缀 sbd_（Strict Bridge Discharge），全库 grep 防撞零占用。 *)
(* 关卡账：G1 七禁词扫描 0（本件纯 Definition/Theorem + 闭式证明，    *)
(*   无任何挂账声明形）；G2 全量编译绿（cpu_guard 包裹、rc 直捕）；    *)
(*   G3 本件全 Set/Prop 桥面零计算内容（四件均为序谓词/等词桥，       *)
(*   非计算函数），以本说明替代提取；G4 假设闭包探针 + coqchk 单件     *)
(*   （COQLIB 钉 9.1，防裸调吸 9.0 平台毒 .vo）。                    *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealLtShiftBridge.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* ============ ① 槽1 放电：严格序加法混合保序（lt_le 混合形） ============ *)
(* 槽语句（UpReqAlgebra L1474，RealInterfaceEnhancedSetoid Real 字段面）：
   forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)。
   种子 rlsb_lt_plus_compat_lt_le（UpReqRealLtShiftBridge ③）语句逐字同构
   （lt:=real_lt、le:=real_le、plus:=real_plus，Instance RealEnhancedReal
   字段装配 S07:8577/8578/8573），δ 换装一步喂定。 *)
Definition sbd_req_lt_plus_compat_lt_le :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d)
  := @rlsb_lt_plus_compat_lt_le.

(* ============ ② 槽2 放电：log 参数 req 兼容 ============ *)
(* 槽语句（UpReqAlgebra L1498）：forall x y (Hx : lt zero x) (Hy : lt zero y),
   req x y -> req (log x Hx) (log y Hy)。
   E372 判决路线：real_log_wd（S08:1074，锚点法已验件）语句与槽语句在
   Real 实例面逐字同构（zero:=real_zero、log:=real_log、req:=real_eq），
   直喂一步，零换装零组装。 *)
Definition sbd_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)
  := @real_log_wd.

(* ============ ③ 槽3 放电：log 对 exp_neg 左逆 ============ *)
(* 槽语句（UpReqAlgebra L1502）：forall x, req (log_inv (exp_neg x)
   (exp_neg_pos x)) x。字段装配（Instance RealEnhancedReal）：
   log_inv:=real_log_inv（S07:8656）、exp_neg:=real_exp_neg（S07:8646）、
   exp_neg_pos:=real_exp_neg_pos（S07:8647）。
   链：log_inv y == opp (log y)（real_log_inv_log，S07:7875）
       → opp 换形（RealSetoid.real_eq_opp_compat，S07:255）吃
         real_log_exp_neg（S08:1028：log(e^{-x}) == −x）
       → opp(opp x) == x（real_opp_opp，S08:106）收口。 *)
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

(* ============ ④ 家族闭合伴件：le_lt 形随槽1 放电体闭合 ============ *)
(* UpReqAlgebra.req_lt_plus_compat_le_lt（L1478）出节签名（探针捕获）：
   forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
     (forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
     forall a b c d, le a b -> lt c d -> lt (plus a c) (plus b d)。
   槽1 放电体喂出节首参（discharged 首参位），le_lt 形在 Real 实例上
   无新假设闭合——ReqStrictOrderBridge 族两形式至此全闭。 *)
Definition sbd_req_lt_plus_compat_le_lt :
  forall a b c d : Real, le a b -> lt c d -> lt (plus a c) (plus b d)
  := @req_lt_plus_compat_le_lt Real RealEnhancedReal
       sbd_req_lt_plus_compat_lt_le.

(* ============ 关卡 G4：假设闭包探针（四件全 Closed 为过关判据） ============ *)
Print Assumptions sbd_req_lt_plus_compat_lt_le.
Print Assumptions sbd_log_req_compat.
Print Assumptions sbd_log_inv_exp_neg_req.
Print Assumptions sbd_req_lt_plus_compat_le_lt.
