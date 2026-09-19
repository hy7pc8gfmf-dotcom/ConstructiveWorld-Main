(* ============================================================ *)
(* UpAblT9_UpSigMigrate.v —— T9 批配分正性族·UpSigMigrate 辖区              *)
(* 被消融位（普查表 §2 UpSigMigrate 行）：                                 *)
(*   位1 UpSigMigrate.v:542  partition_function_temp_pos                   *)
(*       （ReqGibbsPilot 数据证书位；配分函数温度版正性）                   *)
(* 母本（零施工直喂，出节签名实测自 _tt9a_sig2 探针）：                     *)
(*   sumd_sum_pos@UpReqSumD:233（正和族；非空数据槽显式参）；               *)
(*   sumf 换实例位 sumd_sumf S enum；sigm_partition_function_temp@:539      *)
(*   出节签名 {R}{RIS} S sumf T T_pos z。                                  *)
(* 分级：N1（证书供给=具体配分实例上无条件正）。                            *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqSumD、        *)
(*   UpSigMigrate。                                                        *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
Require Import UpSigMigrate.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 位1 ←:542（sumf:=sumd_sumf 具体实例；正和族放电） *)
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
