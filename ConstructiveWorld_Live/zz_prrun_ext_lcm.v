(* ===================================================================== *)
(* 模块名：zz_prrun_ext_lcm（提取驱动件，RunAlive 取证用，非库模块）        *)
(* 使命：u5c_pr_lcm_absorb 的 RunAlive 提取面——B' 可执行核 plw_maxpow ＋     *)
(*   HansonLcm.hl_binom（Pascal 机）＋ HansonLcm.hl_lcm_upto（折叠机）＋      *)
(*   abl_Pr_core_01.pr_prime_bool（前提布尔反射）。全部一阶 nat/bool，零 Prop  *)
(*   承载位。 *)
(* 依赖：HansonLcm、u5c_pr_lcm_absorb（只读 Require）；Stdlib Extraction。 *)
(* 构造性注记：本件零语句定义，仅提取指令面；提取产物落 mlcm/ 目录。 *)
(* 编译配方：source Live/toolchain/env.sh 后于池目录 rocq c -native-compiler  *)
(*   no -q -Q . "" zz_prrun_ext_lcm.v。 *)
(* ===================================================================== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "mlcm".
Require Import HansonLcm.
Require Import u5c_pr_lcm_absorb.
Separate Extraction plw_maxpow
                   HansonLcm.hl_binom
                   HansonLcm.hl_lcm_upto
                   abl_Pr_core_01.pr_prime_bool.
