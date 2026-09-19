From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Require Import fa56c_ext.

Definition fa56c_g3_witness :=
  @fa56c_landauer_upper_bound.

Definition fa56c_g3_witness2 :=
  @fa56c_loss_structure_correlation.

Definition fa56c_g3_witness3 :=
  @fa56c_max_entropy_production.

Definition fa56c_g3_witness4 :=
  @fa56c_le_mult_compat_l.

Recursive Extraction fa56c_g3_witness fa56c_g3_witness2 fa56c_g3_witness3 fa56c_g3_witness4.
