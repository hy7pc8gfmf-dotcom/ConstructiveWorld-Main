(* fa53_compat_abs_g3.v — G3 提取探针（首行强制 Require Extraction，T40 四关） *)
From Stdlib Require Import Extraction.
Require Import fa53_compat_abs.
Separate Extraction fa53_lt_dec fa53_not_le_lt.
