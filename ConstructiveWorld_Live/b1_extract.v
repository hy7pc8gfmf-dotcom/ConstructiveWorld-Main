(* ============================================================
   模块名: b1_extract
   数学使命: b1 spine 四件（kernel/trunc/carrier_beta/denom_control）
     九个常量的 Separate Extraction 驱动（零语句件），输出目录 extract/。
   依赖清单: b1_kernel_pointwise, b1_trunc_master, b1_carrier_beta,
     b1_denom_control; Stdlib Extraction。
   构造性注记: 本件无语句定义; 提取目标常量均出自已证 Set 承载件。
   编译配方: rocq c -native-compiler no -q -Q . "" b1_extract.v。
   ============================================================ *)

Require Import b1_kernel_pointwise.
Require Import b1_trunc_master.
Require Import b1_carrier_beta.
Require Import b1_denom_control.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "extract".

Separate Extraction b1_ps b1_pq b1_seg_poly b1_seg_signed b1_seg_beta
  b1_rho b1_dfact_odd b1_dfact_even b1_odd_div_dfact.
