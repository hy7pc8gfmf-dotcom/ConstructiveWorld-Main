(* pa1_g3.v — Paper1Ablation 提取检验件。
   使命: 验证 GRPO 矩量、二阶矩分解、DPO 奖励相对精确与对合兼容四结论的可提取性，零新数学内容。
   依赖: Paper1Ablation。
   对标: pa1_grpo_unit_moment_pop、pa1_raw_second_moment_decomp、pa1_dpo_reward_relative_exact、pa1_opp_eq_compat。
   构造性注记: 只含 Require 与 Extraction 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/pa1_g3.v。 *)
From Stdlib Require Import Extraction.
Require Import Paper1Ablation.
Extraction "pa1_g3_out.v" pa1_grpo_unit_moment_pop pa1_raw_second_moment_decomp pa1_dpo_reward_relative_exact pa1_opp_eq_compat.
