(* LW3Kills.v                                                          *)
(* 使命：环 6 kills 引理本体（Real 半边最后一环）。388 §5.2 草案落定形：      *)
(*      ∃M, 2|X| ≤ M+1 ∧ (|X|^M/M!)·2 < eps（sigT+And 数据形，X 泛型＝      *)
(*      390 界面点 1 家族无关铁据）。                                        *)
(* 路线：S03 谱系在件四件直连（388 缺供四项的在库升格——勘形补账）：          *)
(*      ①ceil 槽＝q_arch_geom（Set 层 sigT 形，stdlib Qarchimedean          *)
(*        {p|q<p#1} 构造 sigT 直连，零公理——390 第五证闭包已认证）；         *)
(*      ④前段定值×尾段比值积＝pow_fact_decay（A^b/b! ≤ front·(1/2)^{b-N0}）；*)
(*      ③几何 eps-实例化＝arch_decay（∃t 显式 sigT 形，C·(1/2)^{S t}<eps）； *)
(*      装配＝exp_tail_arch（b ≥ N0+S t 处 (A^b/b!)·2 < eps）。              *)
(* M 显式门槛算式：M := projT1(q_arch_geom |X|) + S(projT1(arch_decay front  *)
(*      eps …))——N0/t 全为 X,eps 的可计算函数（见证形态承 UpAblHalfPow      *)
(*      在档口径：Qarchimedean 的 Pos.to_nat p），非纯存在形。               *)
(* 对接：tlw398_carrier_discharge＝kills 填装 tlw383_eslot_carrier 的        *)
(*      kills 前提位（carrier 前提位减一、E-槽桥位零改动的机械兑现）。       *)
(* 构造性：语句面全 Set（QltT/QleT' Id-bool 形、sigT/And 数据组合）；        *)
(*      禁引六族零命中；Q 域洁净；终形 regex ^Theorem lw3_ 计 0＝诚实态。    *)
(* 编译配方：SW2 双 export COQLIB/ROCQLIB 全字面；coqc -q -Q . '""'          *)
(*      -Q Main_vo '""'；cpu_guard 包裹（390 配方承继）。                    *)
(* 依赖：Stdlib QArith/Lia/Arith/ZArith/List/QArith_base/QArith.Qabs/Extraction＋S01_BaseRing/S02_CauchyComplete/S03_QExp＋LW0QPoly/LW0FactGrowth/LW2Hermite＋LW3ESlot。 *)
(* 对标：kills 前提位机械兑现件（E-槽桥位零改动；carrier 第二前提位逐字对照）。 *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW3ESlot.

(* ===== 0. 链上引理可见性勘形（PROBEFIRST 判例件随件留存） ===== *)

Check q_arch_geom.
Check arch_decay.
Check exp_tail_arch.
Check q_pow_fact2_nonneg.
Check qabs_nonnegT.
Check QleT'_to_Qle.
Check Qle_to_QleT'.
Check QltT_to_Qlt.
Check qleT'_trans.
Check qeq_leT'.
Check NatLe_lift.
Check tlw383_geom_bound.
Check tlw383_eslot_carrier.
Print lw0_q_of_nat.

(* ===== 1. kills 主件：环 6 缺口的 eps-实例化闭合 ===== *)

(* M 显式门槛构造：N0 := 阿基米德 ceil 槽见证（q_arch_geom |X|），
   t := 几何 eps-实例化见证（arch_decay front eps），
   M := N0 + S t。三段语义：
   (a) N0 ≤ M+1 段：2|X| ≤ (u+1)#1 对一切 u ≥ N0（q_arch_geom 投影），
       取 u := M 即 2|X| ≤ M+1（(1+1)·A ≡ 2·A 环恒等收形）；
   (b) 前段定值：front := (|X|^{N0}/N0!)·2 ≥ 0（q_pow_fact2_nonneg）；
   (c) 尾段：t 使 front·(1/2)^{S t} < eps（arch_decay），b := M ≥ N0+S t
       处 exp_tail_arch 沿 pow_fact_decay 的比值积拆解压下 B_M < eps。 *)
Theorem tlw398_kills : forall (X eps : Q),
  QltT 0 eps ->
  sigT (fun M : nat =>
    And (QleT' (2 * Qabs X) (lw0_q_of_nat (M + 1)))
        (QltT (tlw383_geom_bound X M) eps)).
Proof.
  intros X eps Heps0.
  destruct (q_arch_geom (Qabs X)) as [N0 Hgeom].
  assert (HA : Qle 0 (Qabs X)).
  { apply QleT'_to_Qle. apply qabs_nonnegT. }
  assert (Hgq : forall u : nat, (N0 <= u)%nat ->
           Qle (Qmult (1 + 1)%Q (Qabs X)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply Hgeom. apply (NatLe_lift N0 u Hu). }
  assert (Hf0 : QleT' 0 ((q_pow (Qabs X) N0 / q_fact N0) * (1 + 1)%Q)).
  { apply Qle_to_QleT'. apply (q_pow_fact2_nonneg (Qabs X) N0 HA). }
  destruct (arch_decay ((q_pow (Qabs X) N0 / q_fact N0) * (1 + 1)%Q) eps
             Hf0 Heps0) as [t Hdec].
  exists ((N0 + Datatypes.S t)%nat). split.
  - apply (qleT'_trans (2 * Qabs X) (Qmult (1 + 1)%Q (Qabs X))
             (lw0_q_of_nat (((N0 + Datatypes.S t) + 1)%nat))).
    + apply qeq_leT'. ring.
    + unfold lw0_q_of_nat. apply Hgeom.
      apply NatLe_lift. lia.
  - unfold tlw383_geom_bound. apply Qlt_to_QltT.
    apply (exp_tail_arch (Qabs X) N0 t ((N0 + Datatypes.S t)%nat) eps HA Hgq).
    + exact (QltT_to_Qlt 0 eps Heps0).
    + exact (QltT_to_Qlt _ _ Hdec).
    + lia.
Qed.

(* 见证抽取数据形：M 门槛的显式可计算函数（X,eps ↦ nat；G3 提取并集） *)
Definition tlw398_kills_M (X eps : Q) (Heps0 : QltT 0 eps) : nat :=
  projT1 (tlw398_kills X eps Heps0).

(* ===== 2. 对接预验：kills 填装 tlw383_eslot_carrier 缺口位 ===== *)

(* carrier 前提位减一：原 carrier 取 (QltT 0 eps, kills 形) 两前提出
   real_lt 面结论；本件以 QltT 0 eps 单前提直接产出同款结论——
   tlw383_eslot_carrier 零改动（390 §6.2 消环记录的机械兑现，
   使用接口＝LW3Kills 逐字对照 carrier 第二前提位）。 *)
Theorem tlw398_carrier_discharge : forall (X eps : Q),
  QltT 0 eps ->
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const eps)).
Proof.
  intros X eps Heps0.
  exact (tlw383_eslot_carrier X eps Heps0 (tlw398_kills X eps Heps0)).
Qed.

(* ===== 3. 锚例钉：X := -node 2（|X|=2）、eps := 1 处 kills 产出实距 < 1 ===== *)

(* 与 tlw383_eslot_anchor 同款使用位：kills 在锚例上非vacuous——
   单前提 0 < 1 即产出 M 见证与实距离 < 1（对接件的实例化形态）。 *)
Theorem tlw398_anchor_discharge :
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (Datatypes.S O))) M)))
            (real_const (1 # 1)%Q)).
Proof.
  apply (tlw398_carrier_discharge
          (- lw2_node (Datatypes.S (Datatypes.S O))) (1 # 1)%Q).
  unfold QltT, Qlt_bool. vm_compute. reflexivity.
Qed.

(* ===== 4. 提取检核（G3 数据名并集：M 门槛可计算函数） ===== *)

From Stdlib Require Import Extraction.
Separate Extraction tlw398_kills_M.
