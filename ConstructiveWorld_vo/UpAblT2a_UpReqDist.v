(* ============================================================ *)
(* UpAblT2a_UpReqDist.v —— 假设消融战役 T2a 批（FA2 第 2 批·log 三面）      *)
(* 辖区：UpReqDist.v ReqFEP 节（L1001-1037）log 接口面假设位 2 位：              *)
(*   L1030 dist_log_inv_one_inv（倒数面）/ L1033 dist_log_exp_neg（负指面）。    *)
(*   （同文件 sumf 接口面 14 位已由 T1a 席 UpAblT1_UpReqDist.v 收割，本件零重叠。）*)
(* 母本：logd_log_inv_one_inv_real / logd_log_exp_neg_real@G05_LogSmall          *)
(*   （零前提 Real 层槽形；倒数面同形 kl_log_inv@UpStepKL:583；负指面根供给      *)
(*   real_log_exp_neg，CW 基座直取）。                                          *)
(* 实态取证：FA2 普查表（20260919）行号与现档逐位一致（底册行数 3576=现档         *)
(*   行数 3576，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，        *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。          *)
(* 分级：2 件全 N1（库内放电件直连；G05 头注 B3/B2 族本位在案）。                 *)
(* 备注：语句全集合层；公理面零新增；全 Qed；文尾逐件 Print Assumptions 收尾。    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←UpReqDist.v L1030 dist_log_inv_one_inv（逐字，R:=Real） ---- *)
Theorem uabT2a_dist_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Qed.

(* ---- 位2 ←UpReqDist.v L1033 dist_log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_dist_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_dist_log_inv_one_inv.
Print Assumptions uabT2a_dist_log_exp_neg.
