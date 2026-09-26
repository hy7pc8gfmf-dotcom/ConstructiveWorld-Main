(* ipl_g3.v — G3 提取探针（首行强制 Require Extraction，T40 四关） *)
From Stdlib Require Import Extraction.
Require Import InvPosLtCompat.
Separate Extraction ipl_lt_mult_compat_l ipl_inv_pos_lt_compat ipl_upfirewall_102_shape.
Print Assumptions ipl_inv_pos_lt_compat.
