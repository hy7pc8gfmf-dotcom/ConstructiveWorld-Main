(* ============================================================ *)
(* UpAblT2a_UpSigMigrate2.v —— 假设消融战役 T2a 批（FA2 第 2 批·log 三面）  *)
(* 辖区：UpSigMigrate2.v ReqFECore 节（L92-121）+ ReqAlignCore 节（L872-921）   *)
(*   log 接口面假设位 4 位：L117 req_log_exp_neg / L120 req_log_compat /        *)
(*   L908 b_log_exp_neg / L910 b_log_compat。                                  *)
(* 母本（G05_LogSmall 三件组，零前提 Real 层槽形放电）：                         *)
(*   相容面←logd_log_compat_real（副路：hzlogd_log_req_compat_real@G08:799，     *)
(*     其证=real_log_wd@S08_RealMainlineDPO:1074 直取）                         *)
(*   负指面←logd_log_exp_neg_real（根供给 real_log_exp_neg，CW 基座直取）        *)
(*   倒数面←logd_log_inv_one_inv_real（本件未用位；同形 kl_log_inv@UpStepKL:583）*)
(* 实态取证：FA2 普查表（20260919）行号与现档逐位一致（底册行数 1731=现档        *)
(*   行数 1731，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，        *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。         *)
(* 分级：4 件全 N1（库内放电件直连：被消融位在库内已有零前提无条件形；            *)
(*   证明体非平凡内容在母本本体——G05_LogSmall Part0 接口代数件+CW 根基元，        *)
(*   本件直连不注水）。                                                         *)
(* 备注：语句全集合层（req/lt 均集合值谓词）；公理面零新增；全 Qed；              *)
(*   文尾逐件 Print Assumptions 收尾。四关留痕：Live_X/attn/logs/               *)
(*   g{1..4}-UpAblT2a_*.log。                                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←UpSigMigrate2.v L117 req_log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_sigm2_req_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Qed.

(* ---- 位2 ←UpSigMigrate2.v L120 req_log_compat（逐字，R:=Real） ---- *)
Theorem uabT2a_sigm2_req_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Qed.

(* ---- 位3 ←UpSigMigrate2.v L908 b_log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_sigm2_b_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Qed.

(* ---- 位4 ←UpSigMigrate2.v L910 b_log_compat（逐字，R:=Real） ---- *)
Theorem uabT2a_sigm2_b_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_sigm2_req_log_exp_neg.
Print Assumptions uabT2a_sigm2_req_log_compat.
Print Assumptions uabT2a_sigm2_b_log_exp_neg.
Print Assumptions uabT2a_sigm2_b_log_compat.
