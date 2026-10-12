(* ===================================================================== *)
(* 模块名：u5c_ext（提取驱动件，非库模块）                                *)
(* 使命：u5c_pr_bertrand_close 的公理审计与提取驱动——对主语句列            *)
(*   Print Assumptions，并对 u5c_bertrand_full 作 Separate Extraction。    *)
(* 依赖：u5c_pr_bertrand_close（只读 Require）。 *)
(* 构造性注记：本件零语句定义，仅审计与提取指令面。 *)
(* 编译配方：source Live/toolchain/env.sh 后于池目录 rocq c -native-compiler  *)
(*   no -q -Q . "" u5c_ext.v（依赖件 vo 经 -Q 映射挂源根）。 *)
(* ===================================================================== *)

Require Import u5c_pr_bertrand_close.
Print Assumptions u5c_cprime_gen.
Print Assumptions u5c_mid_master'.
Print Assumptions u5c_mid_lower.
Print Assumptions u5c_master_bound.
Separate Extraction u5c_bertrand_full.
