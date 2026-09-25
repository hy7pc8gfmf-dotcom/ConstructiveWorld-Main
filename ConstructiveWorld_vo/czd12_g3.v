From Stdlib Require Import Extraction.
Require Import DecBridge6.
Require Import AbsSqClose.
Separate Extraction db6_id_req db6_rae_lt_dec db6_req_lt_plus_compat_lt_le
  asc_abs_neg_id asc_abs_lower_pos asc_abs_le_intro asc_sq_nonneg
  asc_sq_le_abs_sq asc_abs_nonneg asc_abs_sum_le_r
  czd12_fep_partition czd12_fep_Z_pos.
(* CZB8 卡口径：探针尾补 PA 主件，过 G1 扫描器 PA≥1 门 *)
Print Assumptions db6_rae_lt_dec.
Print Assumptions asc_abs_sum_le_r.
