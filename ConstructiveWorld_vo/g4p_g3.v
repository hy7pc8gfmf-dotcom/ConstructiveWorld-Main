(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* g4p_g3.v — G3 提取检验（首行强制 Require Extraction， 四关） *)
From Stdlib Require Import Extraction.
Require Import G04ProjHook.
Separate Extraction g4p_kl_cost_two g4p_W2p_two_uniform_bridge g4p_proj_minor_uncond_two g4p_ZP_pos_two.
Print Assumptions g4p_kl_cost_two.
