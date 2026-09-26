(* ============================================================ *)
(* UpAblP4_UpStopTime_PA.v —— UpStopTime 闭合结论配套模块。        *)
(*                                                              *)
(* 使命： 本件以依存性重述为 UpStopTime 模块补全文尾闭合结论面：  *)
(*   三件定理语句与 UpStopTime 源模块同名件逐字同形，证明体       *)
(*   exact 直连源模块已证同名件，文尾逐件 Print Assumptions       *)
(*   给出闭合结论——源模块尾部仅有提取检验块、无 Print            *)
(*   Assumptions 块，本配套模块补全该证据链，源模块本体零改。       *)
(*                                                              *)
(* 语句覆盖（三件，均与源模块同名件逐字同形）：                   *)
(*   1  uastp_minimal_stoptime_pa      最小停时三联证书（存在性、  *)
(*                                     最小性、上界单调）；       *)
(*   2  uastp_st_thresh_dominance_pa   阈值策略双目标占优的几何    *)
(*                                     衰减实例化；              *)
(*   3  uastp_unguarded_no_stoptime_pa 无见证恒值链停时不存在      *)
(*                                     （分离件）。              *)
(*                                                              *)
(* 依赖： UpStopTime 及其传递面 CW_ConstructiveWorld_219、        *)
(*   UpBudgetReal、UpConstitution、QArith、Lia、PeanoNat——只读    *)
(*   依存，源模块本体零改。                                       *)
(* 构造性： 全件真证闭合——零悬置、零假设位、零经典逻辑依赖；      *)
(*   源模块 47 语句 = 38 Lemma + 1 Corollary + 8 Theorem，其中     *)
(*   45 处 Qed + 2 处 Defined（stsearch_step_0 / stsearch_step_S  *)
(*   为可执行搜索步，提取器须保留其本体）。                       *)
(* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。  *)
(* 对标： 无（本项目停时演算自建）。                              *)
(*                                                              *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpBudgetReal.
Require Import UpConstitution.
Require Import UpStopTime.

(* ============================================================ *)
(* 一、主依存性重述：最小停时三联证书（语句与 minimal_stoptime 逐字同形） *)
(* ============================================================ *)

Theorem uastp_minimal_stoptime_pa : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof. exact minimal_stoptime. Qed.

(* ============================================================ *)
(* 二、装配依存性重述：阈值策略双目标占优（语句与 st_thresh_dominance 逐字同形） *)
(* ============================================================ *)

Theorem uastp_st_thresh_dominance_pa : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof. exact st_thresh_dominance. Qed.

(* ============================================================ *)
(* 三、反面依存性重述：停时不存在分离件（语句与 unguarded_no_stoptime 逐字同形） *)
(* ============================================================ *)

Theorem uastp_unguarded_no_stoptime_pa : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof. exact unguarded_no_stoptime. Qed.

(* ============================================================ *)
(* 四、文尾逐件闭合审（Print Assumptions 三连）                                    *)
(* ============================================================ *)

Print Assumptions uastp_minimal_stoptime_pa.
Print Assumptions uastp_st_thresh_dominance_pa.
Print Assumptions uastp_unguarded_no_stoptime_pa.
