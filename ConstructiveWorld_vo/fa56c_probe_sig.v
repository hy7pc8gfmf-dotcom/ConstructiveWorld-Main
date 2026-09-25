(* fa56c_probe_sig.v — fa56b_ext 接口签名检验件。
   使命: 以类型检查核对单点族、负熵与基础算术接口签名在位，零新数学内容。
   依赖: S01_BaseRing、fa56_id_carrier、fa56b_ext。
   对标: fa56b_singleton_nonempty、le_mult_compat、log_le_linear 等 Check 具名行。
   构造性注记: 只含 Require 与 Check 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/fa56c_probe_sig.v。 *)
Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Check fa56b_singleton_nonempty.
Check fa56b_cons_nil_id_contra.
Check fa56b_id_transport.
Check fa56_prob_neg_entropy.
Check fa56_prob_neg_entropy_pos.
Check le_mult_compat.
Check lt_mult_compat.
Check log_le_linear.
Check two_pos.
Check minus_plus_cancel_r.
Check le_id_l.
Check le_id_r.
Check mult_one.
Check mult_comm.
Check mult_positive.
Check le_refl.
Check ExistsT.
