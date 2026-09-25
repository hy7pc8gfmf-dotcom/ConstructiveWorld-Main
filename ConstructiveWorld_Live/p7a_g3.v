(* ============================================================ *)
(* p7a_g3.v —— Paper7Ablation 的 expf 接口可提取性检验件 *)
(* 使命：本件以 Separate Extraction 抽取 Paper7Ablation 的 expf 迷你 *)
(*   接口两定理——p7a_expf_wd（由 {expf_plus, expf_zero, expf_pos} 经 *)
(*   mult_cancel_l 消去链导出的同余性）与 p7a_expf_mono_le_do（由 *)
(*   mono_lt、三分律与同余性导出的 le 单调性）——验证该接口面可编译 *)
(*   为计算码。 *)
(* 依赖：Paper7Ablation；Stdlib Extraction。 *)
(* 对标行：Paper7Ablation（expf 字段面 6→5 压缩；AttnDoeblin:469 *)
(*   同型接口）。 *)
(* 构造性注记：本件零新增语句，仅提取命令；两定理均为全 Qed 构造证明。 *)
(* 编译配方：Rocq 9.1 coqc 直调，-native-compiler no -Q . ""， *)
(*   先 COQLIB/ROCQLIB 同源双 export。 *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Require Import Paper7Ablation.
Separate Extraction p7a_expf_wd p7a_expf_mono_le_do.
