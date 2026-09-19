(* ============================================================ *)
(* UpAblT2a_UpReqPPO.v —— 假设消融战役 T2a 批（FA2 第 2 批·log 三面）       *)
(* 辖区：UpReqPPO.v ReqPPOAdvantage 节（L66 起）L82 rppo_log_req_compat          *)
(*   （相容面 1 位）。                                                          *)
(*   原位形态注记：宿主该位绑定变元已直书 Real 载体（宿主节内 sumf 面同形态），     *)
(*   故本件语句=R 换实例位后逐字；RIS 取 RealEnhancedReal。                      *)
(* 母本：logd_log_compat_real@G05_LogSmall（零前提 Real 层槽形；G05 头注 B1 族    *)
(*   明列 rppo_log_req_compat 本位；副路 hzlogd_log_req_compat_real@G08:799）。   *)
(* 实态取证：FA2 普查表（20260919）行号与现档逐位一致（底册行数 1253=现档          *)
(*   行数 1253，21 位语句逐字双检通过）。                                        *)
(* 分级：1 件 N1（库内放电件直连）。                                             *)
(* 备注：语句全集合层；公理面零新增；全 Qed；文尾逐件 Print Assumptions 收尾。     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←UpReqPPO.v L82 rppo_log_req_compat（ReqPPOAdvantage 节；逐字，载体已 Real） ---- *)
Theorem uabT2a_rppo_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_rppo_log_req_compat.
