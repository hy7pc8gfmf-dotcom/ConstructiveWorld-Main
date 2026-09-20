(* ============================================================ *)
(* UpAblSlotB0Merge.v —— 槽② B≤0 退化支并轨供给件（P5 席·20260920）        *)
(*                                                                *)
(* 席位：P5（Qfloor 纵深槽② B≤0 退化支并轨席，N10 报告后续槽④）            *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   交付语句面全 Set 层值（QleT'＝S02 Id 形＋sigT 见证），                 *)
(*   语句面无裸命题；等式换形全部内联于证明内部（不上语句面）。             *)
(*                                                                *)
(* 槽②现场（N10 定谳表 2 号位，五同形）：                                   *)
(*   S10_KVQuantTrig.v :1675/1722/6424/11088/12009 ——                      *)
(*   destruct (q_arch_geom B) as [N0 HN0]，契约＝S03_QExp.v:383            *)
(*   q_arch_geom : forall A : Q, sigT (fun N : nat => forall t : nat,      *)
(*     NatLe N t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1))。    *)
(*   N10 定谳配方：非退化支（QltT 0 B）待 S02 层反演桥件后直配；             *)
(*   B≤0 退化支以 N:=0 平凡承接——本件即该退化支并轨供给位。                 *)
(*                                                                *)
(* 语句对齐申报（形态差显式）：                                             *)
(*   结论面与 S03:383 q_arch_geom 契约逐字同形（A:=B，含 NatLe 全称、      *)
(*   Qmult (1+1)%Q B 系数位与 Z.of_nat (t+1) # 1 槽形）；                   *)
(*   形态差仅一处——q_arch_geom 为无条件形（见证来自 Qarchimedean 抽象位），  *)
(*   本件为退化支条件形：增补退化侧假设 QleT' (Qmult (1+1)%Q B) 0           *)
(*   （2B ≤T 0，全 Set 层面），此时 2B ≤ 0 ≤ (t+1)#1 链即闭。              *)
(*                                                                *)
(* 并轨结构（两件，sb0_ 前缀）：                                            *)
(*   A 主件（N:=0 位）：sb0_arch_geom_degen——退化侧假设下 exists 0%nat，    *)
(*      2B ≤ 0 ≤ Z.of_nat (t+1) # 1 两段 Qle 链承接（Qle_of_nat 显式        *)
(*      实例收尾，nat 目标纯数论判定）；                                    *)
(*   B 槽②五槽并轨锚位：sb0_arch_geom_zero_merge——五槽现场环境假设          *)
(*      QleT' 0 B（非负界）之下，退化支即夹零支（QleT' 0 B＋QleT' B 0       *)
(*      ⟹ B=0），序对称桥收 B==0（内联），零乘桥入主件。                    *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全 Export 薄壳：QleT'/          *)
(*   Qle_to_QleT'/QleT'_to_Qle/NatLe/Qle_of_nat/qeq_le 皆在 namespaces）    *)
(*   ＋Stdlib QArith（Qle_trans/Qle_antisym/Qmult_0_r 标准件）＋Lia。       *)
(*   前置桥件 UpAblQeqBridge 未落盘——按令独立施工，零依赖之。               *)
(*   未入 order.txt/_CoqProject；S10/UpAblQeqBridge/既有文件零改动。        *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* Part 0 · 冻结现态打表（签名漂移即响亮失败）                              *)
(* ============================================================ *)

Check QleT'. Check QleT'_to_Qle. Check Qle_to_QleT'.
Check NatLe. Check NatLe_drop.
Check Qle_of_nat. Check qeq_le. Check Qle_trans.
Check Qle_antisym. Check Qmult_0_r.
Check q_arch_geom.

(* ============================================================ *)
(* Part A · 主件：B≤0 退化支 N:=0 平凡承接（槽②契约逐字同形）               *)
(* ============================================================ *)

(* A.1 主件（N:=0 位）：退化侧假设 2B ≤T 0 下，0 即合格基指标——
   2B ≤ 0 ≤ (t+1)#1 链：首段由假设直接承（QleT'_to_Qle 落 Qle），
   次段 Qle_of_nat 0 (t+1) 显式实例（Z.of_nat 0 # 1 与 0 定义性重合，
   应用即转换判定；nat 前提 (0 ≤ t+1)%nat 由 lia 闭）。 *)
Lemma sb0_arch_geom_degen : forall B : Q,
  QleT' (Qmult (1 + 1)%Q B) 0 ->
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intros B HB.
  exists 0%nat.
  intros t Ht.
  apply Qle_to_QleT'.
  apply (Qle_trans _ 0).
  - exact (QleT'_to_Qle _ _ HB).
  - apply (Qle_of_nat 0 (t + 1)). lia.
Qed.

(* ============================================================ *)
(* Part B · 槽②五槽并轨锚位：现场环境假设下的退化支承接                     *)
(* ============================================================ *)

(* B.1 五槽锚位：S10 五同形位现场假设 QleT' 0 B（非负界）之下，退化支
   即夹零支（0 ≤ B ≤ 0 ⟹ B=0）。序对称桥（Qle_antisym）内联收 B==0，
   零乘桥（Qmult_0_r）收 (1+1)%Q·0==0，入主件 A.1。 *)
Corollary sb0_arch_geom_zero_merge : forall B : Q,
  QleT' 0 B -> QleT' B 0 ->
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intros B HBpos HBneg.
  apply (sb0_arch_geom_degen B).
  apply Qle_to_QleT'.
  apply qeq_le.
  assert (HBeq : B == 0).
  { apply Qle_antisym.
    - exact (QleT'_to_Qle _ _ HBneg).
    - exact (QleT'_to_Qle _ _ HBpos). }
  rewrite HBeq.
  apply Qmult_0_r.
Qed.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions sb0_arch_geom_degen.
Print Assumptions sb0_arch_geom_zero_merge.
