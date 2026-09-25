(* eum_g3.v — EntropyUnsatMark 提取检验件。
   使命: 验证 eum_premises_unsat_ref 的可提取性（提取输出落同名 .ml），零新数学内容。
   依赖: EntropyUnsatMark。
   对标: eum_premises_unsat_ref。
   构造性注记: 只含 Require 与 Extraction 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/eum_g3.v。 *)
From Stdlib Require Import Extraction.
Require Import EntropyUnsatMark.
Extraction "eum_g3_out" eum_premises_unsat_ref.
