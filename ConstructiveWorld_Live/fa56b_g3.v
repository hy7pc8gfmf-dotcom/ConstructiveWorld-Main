From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.

Definition fa56b_g3_witness :=
  @fa56b_boltzmann_stationary.

Definition fa56b_g3_witness2 :=
  @fa56b_sumd_swap_mult.

Definition fa56b_g3_witness3 :=
  @fa56b_cross_domain_scaling.

Definition fa56b_g3_witness4 :=
  @fa56b_id_transport.

Recursive Extraction fa56b_g3_witness fa56b_g3_witness2 fa56b_g3_witness3 fa56b_g3_witness4.
