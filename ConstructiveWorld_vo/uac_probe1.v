Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpReqU2.
(*
   Check @log_req_witness_compat 报 reference not found——名字未进环境；
   补 Import 即绿（仅探针打表层，零证明面改动）。 *)
Import RealInterfaceEnhancedMod.

Check @req2_backward_kl_step.
Check @r2_policy_improvement_mono.
Check @req2_pi_next.
Check @req2_rel_ent.
Check @req2_dpo_loss.
Check @req_log_inv_one_inv.
Check @req_log_exp_neg.
Check @pi_next_req.
Check @pi_star_req.
Check @relative_entropy_req.
Check @req_pi_next_pos.
Check @req_pi_star_pos.
Check @pos_dist.
Check @norm_one.
Check @advantage_aug_req.
Check @Z_rel_req.
Check @req_Z_rel_pos.
Check @F_align_req.
Check @align_objective_req.
Check @inv_pos_ext.
Check @log_req_witness_compat.
