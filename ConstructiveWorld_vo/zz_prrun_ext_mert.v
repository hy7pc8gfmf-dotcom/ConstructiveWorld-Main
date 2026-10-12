(* ===================================================================== *)
(* 模块名：zz_prrun_ext_mert（提取驱动件，RunAlive 取证用，非库模块）       *)
(* 使命：u5c_pr_mertens_nat 的 RunAlive 提取面——主语句 pzs_prime_recip_diverge *)
(*   （sigT+NatLebT 形）＋ pzs_rsum（A4 和函数）＋ pzs_B（下界常数）＋        *)
(*   abl_Pr_core_01.pr_prime_bool。 *)
(* 依赖：u5c_pr_mertens_nat（只读 Require）；Stdlib Extraction。 *)
(* 构造性注记：本件零语句定义，仅提取指令面；提取产物落 mmert/ 目录。 *)
(* 编译配方：source Live/toolchain/env.sh 后于池目录 rocq c -native-compiler  *)
(*   no -q -Q . "" zz_prrun_ext_mert.v。 *)
(* ===================================================================== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "mmert".
Require Import u5c_pr_mertens_nat.
Separate Extraction pzs_prime_recip_diverge
                    pzs_rsum
                    pzs_B
                    abl_Pr_core_01.pr_prime_bool.
