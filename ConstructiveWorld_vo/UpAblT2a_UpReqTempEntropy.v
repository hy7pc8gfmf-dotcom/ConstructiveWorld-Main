(* ============================================================ *)
(* UpAblT2a_UpReqTempEntropy.v —— 假设消融战役 T2a 批（FA2 第 2 批·log 三面） *)
(* 辖区：UpReqTempEntropy.v ReqTempEntropy 节（L42 起）log 接口面假设位 2 位：     *)
(*   L64 dist_log_inv_one_inv（倒数面）/ L67 dist_log_exp_neg（负指面）。          *)
(*   （同节 sumf 六面+L75 Z_temp_spec 系他批辖区，本件零重叠；                     *)
(*   L69/L71 dist_log_le_linear/dist_log_eq_linear 系 W 类墙位（普查 §3-W4），     *)
(*   不入件表，落墙登记。）                                                       *)
(* 母本：logd_log_inv_one_inv_real / logd_log_exp_neg_real@G05_LogSmall           *)
(*   （零前提 Real 层槽形；倒数面同形 kl_log_inv@UpStepKL:583；负指面根供给        *)
(*   real_log_exp_neg，CW 基座直取）。                                            *)
(* 实态取证：FA2 普查表（20260919）行号与现档逐位一致（底册行数 1574=现档           *)
(*   行数 1574，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，          *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。            *)
(* 分级：2 件全 N1（库内放电件直连；G05 头注 B3/B2 族本位在案）。                   *)
(* 备注：语句全集合层；公理面零新增；全 Qed；文尾逐件 Print Assumptions 收尾。      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←UpReqTempEntropy.v L64 dist_log_inv_one_inv（逐字，R:=Real） ---- *)
Theorem uabT2a_te_dist_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Qed.

(* ---- 位2 ←UpReqTempEntropy.v L67 dist_log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_te_dist_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_te_dist_log_inv_one_inv.
Print Assumptions uabT2a_te_dist_log_exp_neg.
