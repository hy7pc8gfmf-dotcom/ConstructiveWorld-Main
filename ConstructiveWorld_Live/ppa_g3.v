(* ============================================================ *)
(* ppa_g3.v —— PhysPredAblation 主定理可提取性检验件 *)
(* 使命：本件以 @ 全参见证固定隐式参数，取 PhysPredAblation 的六个 *)
(*   主定理值——ppa_physical_force_is_gradient（力场梯度性）、 *)
(*   ppa_differentiation_attractor（吸引子微分性）、 *)
(*   ppa_macro_loss_monotone（宏观损失单调性）、 *)
(*   ppa_potential_scaled_strict_mono（缩放势严格单调）、 *)
(*   ppa_dev_dynamics_zero（发展动力学零点）、 *)
(*   ppa_iterate_macro_step（迭代宏观步）——经 Recursive Extraction *)
(*   验证整链可编译为计算码。 *)
(* 依赖：S01_BaseRing、fa51_sumpos_id、fa56_id_carrier、fa56b_ext、 *)
(*   fa56c_ext、PhysPredAblation；Stdlib Extraction。 *)
(* 对标行：PhysPredAblation（ppa_ 前缀物理预测面：主定理与纯计算 *)
(*   装配代表件）。 *)
(* 构造性注记：见证以 @ 全参形式取定理值，零新增证明面； *)
(*   证明性参数不进入计算码。 *)
(* 编译配方：Rocq 9.1 coqc 直调，-native-compiler no -Q . ""， *)
(*   先 COQLIB/ROCQLIB 同源双 export。 *)
(* ============================================================ *)
Require Import Extraction.
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Require Import fa56c_ext.
Require Import PhysPredAblation.


Definition ppa_g3_witness :=
  @ppa_physical_force_is_gradient.

Definition ppa_g3_witness2 :=
  @ppa_differentiation_attractor.

Definition ppa_g3_witness3 :=
  @ppa_macro_loss_monotone.

Definition ppa_g3_witness4 :=
  @ppa_potential_scaled_strict_mono.

Definition ppa_g3_witness5 :=
  @ppa_dev_dynamics_zero.

Definition ppa_g3_witness6 :=
  @ppa_iterate_macro_step.

Recursive Extraction ppa_g3_witness ppa_g3_witness2 ppa_g3_witness3
  ppa_g3_witness4 ppa_g3_witness5 ppa_g3_witness6.
