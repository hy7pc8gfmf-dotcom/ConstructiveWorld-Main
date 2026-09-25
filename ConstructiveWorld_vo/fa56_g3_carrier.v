(* fa56_g3_carrier.v — fa56_id_carrier 提取检验件。
   使命: 验证 Markov 核归一与概率负熵小于一两结论的可提取性，零新数学内容。
   依赖: S01_BaseRing、fa51_sumpos_id、fa56_id_carrier。
   对标: fa56_markov_kernel_normalized、fa56_prob_neg_entropy_lt_one。
   构造性注记: 只含 Require/Definition/Recursive Extraction 语句，无证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/fa56_g3_carrier.v。 *)
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.

Definition fa56_g3_witness :=
  @fa56_markov_kernel_normalized.

Definition fa56_g3_witness2 :=
  @fa56_prob_neg_entropy_lt_one.

Recursive Extraction fa56_g3_witness fa56_g3_witness2.
