(* ============================================================ *)
(* UpAblT9_UpSigMigrate.v —— T9 批配分正性族·UpSigMigrate 辖区。       *)
(* 使命：ReqGibbsPilot 数据证书位（配分函数温度版正性）供给件；分级    *)
(*   N1；T9 批零施工、直接代入；战役：头部规范化 T1 席 20260921。       *)
(* 供体：sumd_sum_pos@UpReqSumD（正和族，非空参数位显式参），sumf 取实例   *)
(*   sumd_sumf S enum；使用 sigm_partition_function_temp@:539；        *)
(*   被消融位 UpSigMigrate.v:542 partition_function_temp_pos。         *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219、UpReqSumD、    *)
(*   UpSigMigrate。                                                    *)
(* 红线自审：零承认（Qed 闭合，文末 Print Assumptions 审计）；Set 层    *)
(*   （Not/lt 仅显式参）；可提取。                                     *)
(* 编译配方：coqc 无 -Q 直编，-o 临时目录（树内 .vo 不动）。            *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
Require Import UpSigMigrate.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 位1 ←:542（sumf:=sumd_sumf 具体实例；正和族实例化消解） *)
Theorem uabT9_sigm_pft_pos :
  forall (S : Set) (enum : list S) (Hne : Not (enum = nil))
         (z : S -> Real) (T : Real) (T_pos : lt zero T),
    lt zero (@sigm_partition_function_temp Real RealEnhancedReal S
               (sumd_sumf S enum) T T_pos z).
Proof.
  intros S enum Hne z T T_pos.
  unfold sigm_partition_function_temp, sigm_exp_pos_fn.
  exact (sumd_sum_pos S enum _ Hne
           (fun s : S => exp_neg_pos (opp (mult (inv_pos T T_pos) (z s))))).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_sigm_pft_pos.
