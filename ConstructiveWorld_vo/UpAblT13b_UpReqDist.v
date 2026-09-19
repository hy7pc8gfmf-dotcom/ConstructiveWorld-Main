(* ============================================================ *)
(* UpAblT13b_UpReqDist.v —— 假设消融战役 T13b 承接席（批6 配分正性族一位）     *)
(* 辖区：UpReqDist.v 一位（T13a 移交单 §6 批6 行「等」2 待勘位之一，本席对       *)
(*   普查 17 位家族逐位清点认列；:1025 Z_pos 已由 T9a 收取，本席零重叠）：       *)
(*   位1 UpReqDist.v:1026  partition_condition（ReqFEP 配分条件槽）              *)
(* 被消融位语句（现档逐字，:1025-1026 同节）：                                   *)
(*   Hypothesis partition_condition :                                           *)
(*     req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).   *)
(* 放电母本：c_partition@UpSigMigrate2:1589 两状态具体实例判例直喂                *)
(*   （exp_neg_zero/req_plus_compat 实例代数已在其证明体；Z 取 two_state_Z、     *)
(*   sumf 取 bsum、D 取 real_one、base_loss 取 two_state_loss 具体实例）。        *)
(* 消融形（诚实登记）：具体实例供给（N3）——抽象载体上 Z 与 sumf 均为自由数据槽    *)
(*   不放电；两状态实例世界（实载体）上成立。                                     *)
(* 分级：N3（实例供给直喂）。                                                    *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpSigMigrate2。          *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                           *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* 位1 ←:1026（两状态实例装配；Z:=two_state_Z、sumf:=bsum、D:=real_one、          *)
(*   base_loss:=two_state_loss，配分条件实形=c_partition 语句转换同一） *)
Theorem uabT13b_dist_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_dist_partition_cond.
