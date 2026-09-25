(* fic_g3.v — FepIdentClass 提取检验件。
   使命: 验证注意力 Gibbs 温度表示及其 Id 面结论的可提取性，零新数学内容。
   依赖: FepIdentClass。
   对标: fic_attention_is_gibbs_temp、fic_attention_is_gibbs_temp_id。
   构造性注记: 只含 Require 与 Extraction 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/fic_g3.v。 *)
From Stdlib Require Import Extraction.
Require Import FepIdentClass.
Extraction "fic_g3_out" fic_attention_is_gibbs_temp fic_attention_is_gibbs_temp_id.
