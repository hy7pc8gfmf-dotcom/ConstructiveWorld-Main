Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Require Import fa56c_ext.
Require Import PhysPredAblation.

(* G3 探针（ppa 前缀）：取三槽主件 + 计算面装法代表件。
   ppa_dev_orbit 带 StateSpace 投影头（证明-only 面不出计算码），
   故探针取纯计算装法件 + 三主件的 @ 全参 witness。 *)

Definition ppa_g3_witness :=
  @ppa_physical_force_is_gradient.

Definition ppa_g3_witness2 :=
  @ppa_differentiation_attractor.

Definition ppa_g3_witness3 :=
  @ppa_macro_loss_monotone.

Definition ppa_g3_witness4 :=
  @ppa_potential_scaled_strict_mono.

Definition ppa_g3_witness5 :=
  @ppa_dev_dynamics_zero.

Definition ppa_g3_witness6 :=
  @ppa_iterate_macro_step.

Recursive Extraction ppa_g3_witness ppa_g3_witness2 ppa_g3_witness3
  ppa_g3_witness4 ppa_g3_witness5 ppa_g3_witness6.
