(* ==========================================================================)
   UpAblT9_UpSigMigrate2.v — 配分条件 partition_condition 的 two_state 具体实例见证件
   使命: uabT9_sigm2_partition_two_state：D:=1、Z:=two_state_Z、base_loss 零常值、bsum 二态有限和实例下配分条件无条件成立。
   依赖: CW_ConstructiveWorld_219、UpSigMigrate2（只读使用，原树零改）。
   对标: 配分函数条件的具体实例层。
   构造性: 零承认词面（Qed 闭合，文末 Print Assumptions 审计）；Set 层承载；可提取。
   编译配方: coqc 9.1 直调无 -Q，cpu_guard 包裹，-o 临时目录（树内 .vo 不动）。
   ========================================================================== *)
Require Import CW_ConstructiveWorld_219.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* 即 c_partition@UpSigMigrate2:1589：配分条件于 two_state 实例成立 *)
Theorem uabT9_sigm2_partition_two_state :
  req two_state_Z
      (bsum (fun s : bool => exp_neg (mult two_state_inv_one real_zero))).
Proof.
  exact c_partition.
Qed.

(* 假设审计：Print Assumptions uabT9_sigm2_partition_two_state 应为空 *)
Print Assumptions uabT9_sigm2_partition_two_state.
