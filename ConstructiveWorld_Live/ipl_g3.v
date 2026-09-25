(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ipl_g3.v — G3 提取检验（首行强制 Require Extraction， 四关） *)
From Stdlib Require Import Extraction.
Require Import InvPosLtCompat.
Separate Extraction ipl_lt_mult_compat_l ipl_inv_pos_lt_compat ipl_upfirewall_102_shape.
Print Assumptions ipl_inv_pos_lt_compat.
