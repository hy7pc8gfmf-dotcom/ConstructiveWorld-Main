(* czd12_g3.v —— DecBridge6 的提取检验件（四关口径）。
   使命：以 Separate Extraction 提取 db6_id_req／db6_rae_lt_dec／db6_req_lt_plus_compat_lt_le，
   验证信息性证明链可提取透明（Obj.magic 计数为零）。
   依赖：Stdlib.Extraction；DecBridge6；AbsSqClose。
   构造性：本件零自有语句，全部依赖目标模块的构造性证明。
   编译配方：coqc -native-compiler no -q -Q . "" czd12_g3.v
 *)
From Stdlib Require Import Extraction.
Require Import DecBridge6.
Require Import AbsSqClose.
Separate Extraction db6_id_req db6_rae_lt_dec db6_req_lt_plus_compat_lt_le
  asc_abs_neg_id asc_abs_lower_pos asc_abs_le_intro asc_sq_nonneg
  asc_sq_le_abs_sq asc_abs_nonneg asc_abs_sum_le_r
  czd12_fep_partition czd12_fep_Z_pos.
(* CZB8 口径：检验件尾部补 Print Assumptions 主件，过 G1 扫描器 PA≥1 门 *)
Print Assumptions db6_rae_lt_dec.
Print Assumptions asc_abs_sum_le_r.
