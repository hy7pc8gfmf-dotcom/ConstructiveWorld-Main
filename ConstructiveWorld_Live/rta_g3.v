(* rta_g3.v — RateTheoryAblation 提取检验件。
   使命: 验证迭代压缩不等式 rta_iter_contraction_wo_le_one 的可提取性与公理面纯净性，零新数学内容。
   依赖: RateTheoryAblation。
   对标: rta_iter_contraction_wo_le_one。
   构造性注记: 只含 Require/Recursive Extraction/Print Assumptions 语句，无新定义与证明，公理面应判定 Closed。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/rta_g3.v。 *)
From Stdlib Require Import Extraction.
Require Import RateTheoryAblation.
Recursive Extraction rta_iter_contraction_wo_le_one.
Print Assumptions rta_iter_contraction_wo_le_one.
