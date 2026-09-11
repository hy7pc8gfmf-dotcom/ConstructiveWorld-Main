(* _z3_g3.v — 席Z3 批 B G3 证据探针（-Full 跑；-vos 吞打印） *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import G05_LogSmall.
Require Import UpReqAlign4.
Import RealInterfaceEnhancedMod.

(* 节闭签名实录（批 B 四件，About 钉死供台账） *)
About KlcxAlignBridgeB.kcxr_req_policy_improvement_mono.
About KlcxAlignBridgeB.kcxr_req_policy_iter_kl_geom_step.
About KlcxAlignBridgeB.kcxr_req_dpo_loss_iter_step_le.
About KlcxAlignBridgeB.kcxr_align_obj_transport.

(* Print Assumptions：批 B 四件 + 批 A 回归三件 *)
Print Assumptions KlcxAlignBridgeB.kcxr_req_policy_improvement_mono.
Print Assumptions KlcxAlignBridgeB.kcxr_req_policy_iter_kl_geom_step.
Print Assumptions KlcxAlignBridgeB.kcxr_req_dpo_loss_iter_step_le.
Print Assumptions KlcxAlignBridgeB.kcxr_align_obj_transport.
Print Assumptions kcxr_req_backward_kl_identity.
Print Assumptions kcxr_pi_next_transport.
Print Assumptions kcxr_kl_witness_transport.
