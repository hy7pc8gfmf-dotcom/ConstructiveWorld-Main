(* ===================================================================== *)
(* 模块名：zz_u5c_extract（提取驱动件，非库模块）                          *)
(* 使命：u5c_pr_mertens_nat 主语句 Separate Extraction，检验 Obj.magic 计数   *)
(*   （提取可执行性取证）。 *)
(* 依赖：u5c_pr_mertens_nat（只读 Require）；Stdlib Extraction。 *)
(* 构造性注记：本件零语句定义，仅提取指令面。 *)
(* 编译配方：source Live/toolchain/env.sh 后于池目录 rocq c -native-compiler  *)
(*   no -q -Q . "" zz_u5c_extract.v。 *)
(* ===================================================================== *)

From Stdlib Require Import Extraction.
Require Import u5c_pr_mertens_nat.
Separate Extraction pzs_prime_recip_diverge.
