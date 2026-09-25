(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabT2a_align_log_req_compat_klproj（原 L29，2 句玩具证）             *)
(*   uabT2a_align_log_req_compat_core（原 L20，2 句玩具证）               *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

(* ============================================================ *)
(* 辖区：UpReqAlign.v ReqAlignCore 节 L81 + ReqKLProjection 节 L704，          *)
(*   log 相容面假设位 2 位（同名 log_req_compat 两节同形位）。                  *)
(* 母本：logd_log_compat_real@G05_LogSmall（零前提 Real 层参数形；               *)
(*   副路：hzlogd_log_req_compat_real@G08_Gibbs:799，其证=                     *)
(*   real_log_wd@S08_RealMainlineDPO:1074 直取）。                             *)
(*   行数 1424，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，        *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。         *)
(* 分级：2 件全 N1（库内实例化消解件直连；G05 头注 B1 族本位在案）。                    *)
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
