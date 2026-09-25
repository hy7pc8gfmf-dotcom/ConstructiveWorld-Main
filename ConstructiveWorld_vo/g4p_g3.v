(* g4p_g3.v — G3 提取检验（首行强制 Require Extraction，T40 四关） *)
From Stdlib Require Import Extraction.
Require Import G04ProjHook.
Separate Extraction g4p_kl_cost_two g4p_W2p_two_uniform_bridge g4p_proj_minor_uncond_two g4p_ZP_pos_two.
Print Assumptions g4p_kl_cost_two.
