(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* gfe_g3.v —— 位 P6C G3 提取检验（E-STAGING-P6C）
   纪律：文件式 Extraction 前置显式 Require Extraction；
   只提主定理（常量级主定理检验），不搞全量 Recursive Extraction。
   判定：gfe_g3_out.ml 中 Obj.magic 计数 = 0。 *)
From Stdlib Require Import Extraction.
Require Import GibbsFamilyExt.

Extraction "gfe_g3_out" gfe_gibbs_core_temp_eps gfe_gibbs_core_temp_B gfe_gibbs_inequality_temp_eps gfe_gibbs_inequality_temp_B gfe_gibbs_temp_gap_B gfe_jeffreys_sym_B gfe_jeffreys_sym_list_B.
