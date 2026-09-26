(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* 辖区：UpReqFEPAttn.v 两节 log 三面满配 6 位：                                 *)
(*   ReqFEPAttn 节（L70-252）：L94 log_inv_one_inv / L97 log_exp_neg /           *)
(*     L106 log_req_compat；                                                     *)
(*   ReqFEPLogZ 节（L330-446）：L348 log_inv_one_inv / L351 log_exp_neg /         *)
(*     L353 log_req_compat。                                                     *)
(*   L99/L101 log_le_linear/log_eq_linear 系 W 类阈值位（普查 §3-W4），             *)
(*   不入件表，落墙登记。）                                                      *)
(* 源版本（G05_LogSmall 三件全用，零前提 Real 层槽形）：                            *)
(*   相容面←logd_log_compat_real；负指面←logd_log_exp_neg_real；                  *)
(*   倒数面←logd_log_inv_one_inv_real（同形 kl_log_inv@UpStepKL:583）。           *)
(*   行数 458，21 位语句逐字双检通过）；语句逐字抽取后仅 R 换实例位 Real，          *)
(*   RIS 取 RealEnhancedReal（hzlogd_discharge_real@G08:646 同形先例）。           *)
(* 分级：6 件全 N1（库内实例化消解件直连）。                                           *)
(* 备注：语句全集合层；公理面零新增；全 Qed；文尾逐件 Print Assumptions 收尾。     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ==== ReqFEPAttn 节 ==== *)

(* ---- 位1 ←UpReqFEPAttn.v L94 log_inv_one_inv（逐字，R:=Real） ---- *)
Theorem uabT2a_fep_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Qed.

(* ---- 位2 ←UpReqFEPAttn.v L97 log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_fep_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* ---- 位3 ←UpReqFEPAttn.v L106 log_req_compat（逐字，R:=Real） ---- *)
Theorem uabT2a_fep_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ==== ReqFEPLogZ 节（节内定义 lz_ 前缀位与本件无关） ==== *)

(* ---- 位4 ←UpReqFEPAttn.v L348 log_inv_one_inv（逐字，R:=Real） ---- *)
Theorem uabT2a_lz_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Qed.

(* ---- 位5 ←UpReqFEPAttn.v L351 log_exp_neg（逐字，R:=Real） ---- *)
Theorem uabT2a_lz_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* ---- 位6 ←UpReqFEPAttn.v L353 log_req_compat（逐字，R:=Real） ---- *)
Theorem uabT2a_lz_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_fep_log_inv_one_inv.
Print Assumptions uabT2a_fep_log_exp_neg.
Print Assumptions uabT2a_fep_log_req_compat.
Print Assumptions uabT2a_lz_log_inv_one_inv.
Print Assumptions uabT2a_lz_log_exp_neg.
Print Assumptions uabT2a_lz_log_req_compat.
