(* _z3_probe1.v — 席Z3 批 B 前置检验：钉死节闭签名（-Full 跑，-vos 吞打印） *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* T12 依赖模块节闭签名（批 B 槽2 主使用件） *)
About r2_policy_improvement_mono.
About r2_dpo_loss_step_le.
(* KL≥0 假设位（req2_gibbs_inequality 为节 Hypothesis，不预期有全局；失败即证） *)
About req2_gibbs_inequality.
(* T12 使用面别名（δ 目标面核对） *)
About KLE.
About JJ.
About NPX.
About npx_pos.
About nrm.
About pos3.
(* 序代数件（N4 geom_step 组装腿） *)
About req_plus_opp_le_zero.
About req_plusA_opp_cancel_le.
About opp_le_compat.
About le_id_r.
About le_id_l.
(* 批 A 件（本席文件，节闭形态核对） *)
About kcxr_req_backward_kl_identity.
About kcxr_pi_next_transport.
About kcxr_kl_witness_transport.
