From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.

Definition fa56_g3_witness :=
  @fa56_markov_kernel_normalized.

Definition fa56_g3_witness2 :=
  @fa56_prob_neg_entropy_lt_one.

Recursive Extraction fa56_g3_witness fa56_g3_witness2.
