(* G3 提取探针 — 合并轨收口席续 20260910 · 跨模块常量 magic=0 口径 *)
Require Import CW_ConstructiveWorld_220.
From Stdlib Require Import Extraction.
Extraction "_mc2_close/g3_main.ml" sigm_boltzmann_dist qkb_dotp uab_Z_aud.
