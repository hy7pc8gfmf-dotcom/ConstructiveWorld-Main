(* ali_g3_absleid.v — AbsLeId 抽象主定理提取检验件。
   使命: 验证抽象主定理 ali_abs_ge_zero_id 的可提取性；编译标准输出中 Obj.magic 计数应为零。
   依赖: AbsLeId（文件式 Extraction 前置显式 Require Extraction）。
   对标: ali_abs_ge_zero_id。
   构造性注记: 只提取主定理单项，不做全量递归提取（依赖闭包过大）；零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/ali_g3_absleid.v。 *)
From Stdlib Require Import Extraction.
Require Import AbsLeId.

Recursive Extraction ali_abs_ge_zero_id.
