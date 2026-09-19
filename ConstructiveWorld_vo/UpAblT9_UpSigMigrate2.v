(* ============================================================ *)
(* UpAblT9_UpSigMigrate2.v —— T9 批配分正性族·UpSigMigrate2 辖区            *)
(*   （sum 面=T6a、log 面=T2a 已毕，本件只收配分正性一位，零重叠）          *)
(* 被消融位（普查表 §2 UpSigMigrate2 行）：                                *)
(*   位1 UpSigMigrate2.v:112  partition_condition（ReqAlignCore 接口位）    *)
(* 母本（零施工直喂，同文件 two_state 具体实例段，行号现档直取）：           *)
(*   c_partition@UpSigMigrate2:1589（two_state 实例判例本体；D:=1、         *)
(*   Z:=two_state_Z=2、base_loss:=零常值，bsum 二态有限和）                *)
(* 分级：N1（普查判词 c_partition@:1589 逐字兑现——配分条件在 two_state      *)
(*   具体实例上无条件成立，语句逐字镜像）。                                 *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpSigMigrate2。    *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* 位1 ←:112（rep=c_partition@:1589 逐字镜像） *)
Theorem uabT9_sigm2_partition_two_state :
  req two_state_Z
      (bsum (fun s : bool => exp_neg (mult two_state_inv_one real_zero))).
Proof.
  exact c_partition.
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_sigm2_partition_two_state.
