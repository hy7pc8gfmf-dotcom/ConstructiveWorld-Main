(* mtc_g3.v —— MixTimeChain 的提取检验件（四关口径）。
   使命：以 Separate Extraction 提取 MixTimeChain 的耦合时间见证链，
   验证 sigT 步数见证链可提取透明（Obj.magic 计数为零）。
   依赖：Stdlib.Extraction；MixTimeChain。
   构造性：本件零自有语句，全部依赖目标模块的构造性证明。
   编译配方：coqc -native-compiler no -q -Q . "" mtc_g3.v
 *)
From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import MixTimeChain.

(* 提取面 1：接口腿 κ 前件包（抽象接口层，程序抹证留 nat 流水） *)
Separate Extraction mtc_kappa_package_if.

(* 提取面 2：主件提取——sigT 见证，projT1 给出返回步数 k 的程序 *)
Separate Extraction mtc_attention_mixing_time_local.

(* 提取面 3：柯西实例端到端闭环（expf 实例化消解后零接口前件的可执行形） *)
Separate Extraction mtc_mixing_time_cauchy_exp.

(* G1 min-PA 审计位 *)
Print Assumptions mtc_attention_mixing_time_local.
