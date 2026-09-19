(* ============================================================ *)
(* UpAblT2a_UpReqAlign.v —— 假设消融战役 T2a 批（FA2 第 2 批·log 三面）     *)
(* 辖区：UpReqAlign.v ReqAlignCore 节 L81 + ReqKLProjection 节 L704，          *)
(*   log 相容面假设位 2 位（同名 log_req_compat 两节同形位）。                  *)
(* 母本：logd_log_compat_real@G05_LogSmall（零前提 Real 层槽形；               *)
(*   副路：hzlogd_log_req_compat_real@G08_Gibbs:799，其证=                     *)
(*   real_log_wd@S08_RealMainlineDPO:1074 直取）。                             *)
(* 实态取证：FA2 普查表（20260919）行号与现档逐位一致（底册行数 1424=现档        *)
(*   行数 1424，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，        *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。         *)
(* 分级：2 件全 N1（库内放电件直连；G05 头注 B1 族本位在案）。                    *)
(* 备注：语句全集合层；公理面零新增；全 Qed；文尾逐件 Print Assumptions 收尾。    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←UpReqAlign.v L81 log_req_compat（ReqAlignCore 节；逐字，R:=Real） ---- *)
Theorem uabT2a_align_log_req_compat_core :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- 位2 ←UpReqAlign.v L704 log_req_compat（ReqKLProjection 节；逐字，R:=Real） ---- *)
Theorem uabT2a_align_log_req_compat_klproj :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_align_log_req_compat_core.
Print Assumptions uabT2a_align_log_req_compat_klproj.
