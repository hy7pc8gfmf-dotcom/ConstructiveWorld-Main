(* ============================================================ *)
(* mtc_g3.v — MixTimeChain.v 的 G3 提取探针（席位P7E）             *)
(*   纪律：首行 From Stdlib Require Import Extraction.            *)
(*   目标：合龙主件（含柯西实例闭环推论）Separate Extraction，      *)
(*   验证 sigT 步数见证链透明可提取、Obj.magic 计数 = 0。          *)
(*   （本件为探针件，惯例不入库；实编在 /tmp/mtc_side 单根闭包     *)
(*   内执行以规避同名双根歧义，证据路径见交付报告。）              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import MixTimeChain.

(* 提取面 1：接口腿 κ 前件包（抽象接口层，程序抹证留 nat 流水） *)
Separate Extraction mtc_kappa_package_if.

(* 提取面 2：合龙主件——sigT 见证，projT1 给出返回步数 k 的程序 *)
Separate Extraction mtc_attention_mixing_time_local.

(* 提取面 3：柯西实例端到端闭环（expf 放电后零接口前件的可执行形） *)
Separate Extraction mtc_mixing_time_cauchy_exp.

(* G1 min-PA 审计位 *)
Print Assumptions mtc_attention_mixing_time_local.
