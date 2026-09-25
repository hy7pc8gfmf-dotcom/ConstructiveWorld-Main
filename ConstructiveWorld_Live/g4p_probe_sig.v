(* g4p_probe_sig.v — G04_ProjFam 接口签名检验件。
   使命: 以类型检查核对实数等式、序、倒数与分配律接口签名在位，零新数学内容。
   依赖: CW_ConstructiveWorld_219、G04_ProjFam。
   对标: real_eq_lt_lt、real_inv_pos_correct、real_distrib 等 Check 具名行。
   构造性注记: 只含 Require 与 Check 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/g4p_probe_sig.v。 *)
Require Import CW_ConstructiveWorld_219.
Require Import G04_ProjFam.
Check real_eq_lt_lt.
Check real_lt_eq_lt.
Check real_lt_trans.
Check b4_one_mult.
Check real_inv_pos_correct.
Check real_inv_pos_pos.
Check real_distrib.
Check real_mult_one.
Check real_plus_zero.
Check real_mult_comm.
Check real_eq_refl.
Check real_eq_sym.
Check real_eq_trans.
Check RealSetoid.real_eq_plus_compat.
Check RealSetoid.real_eq_le.
Check real_mult_positive.
Check id_refl.
Check InT_here.
