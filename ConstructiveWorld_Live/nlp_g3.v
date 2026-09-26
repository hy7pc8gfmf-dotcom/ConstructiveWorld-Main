(* ============================================================ *)
(* nlp_g3.v —— NatLenPos 可提取性检验件 *)
(* 使命：本件以 Separate Extraction 抽取 NatLenPos 的三个见证—— *)
(*   nlp_ofnat_S_pos（of_nat 后继步严格正）、nlp_len_pos_cover（覆盖 *)
(*   见证下列表长度严格正）、nlp_g01_mean2（均值倒数装配锚）—— *)
(*   验证其可编译为计算码；并以 Print Assumptions 审计 *)
(*   nlp_len_pos_cover 的依赖面为空。 *)
(* 依赖：NatLenPos；Stdlib Extraction。 *)
(* 对标行：NatLenPos（长度正性覆盖面；均值件与 G01:287-289 逐字同构）。 *)
(* 构造性注记：本件零新增语句，仅提取与审计命令。 *)
(* 编译配方：Rocq 9.1 coqc 直调，-native-compiler no -Q . ""， *)
(*   先 COQLIB/ROCQLIB 同源双 export。 *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Require Import NatLenPos.
Separate Extraction nlp_ofnat_S_pos nlp_len_pos_cover nlp_g01_mean2.
Print Assumptions nlp_len_pos_cover.
