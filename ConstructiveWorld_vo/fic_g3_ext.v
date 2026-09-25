(* fic_g3_ext.v — FepIdentClass 提取检验件（Id 面变体）。
   使命: 验证 Id 面温度表示结论与 Fep 辨识实数实例的可提取性，零新数学内容。
   依赖: FepIdentClass。
   对标: fic_attention_is_gibbs_temp_via_id、FepIdentificationReal。
   构造性注记: 只含 Require 与 Extraction 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/fic_g3_ext.v。 *)
From Stdlib Require Import Extraction.
Require Import FepIdentClass.
Extraction "fic_g3_ext_out" fic_attention_is_gibbs_temp_via_id FepIdentificationReal.
