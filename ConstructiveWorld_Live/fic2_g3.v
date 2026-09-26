(* fic2_g3.v — FepIdConsume 纯面三定理提取检验件。
   使命: Separate Extraction 验证 S01 纯面三定理的可提取性；Obj.magic 计数目标为零。
   依赖: FepIdConsume。
   对标: fic2_identified_boltzmann_dual、fic2_fep_align_face_consume、fic2_rlhf_gap_identified_consume。
   构造性注记: 只含 Require 与 Separate Extraction 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/fic2_g3.v。 *)
From Stdlib Require Import Extraction.
Require Import FepIdConsume.
(* 主验证目标：Obj.magic 计数为零（提取面无魔术值）。 *)
Separate Extraction fic2_identified_boltzmann_dual.
Separate Extraction fic2_fep_align_face_consume.
Separate Extraction fic2_rlhf_gap_identified_consume.
