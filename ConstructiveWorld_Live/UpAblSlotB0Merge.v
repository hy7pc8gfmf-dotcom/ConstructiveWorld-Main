(* ============================================================
   UpAblSlotB0Merge —— q_arch_geom 之 B≤0 退化支供给模块
(*                                                                *)
(* 使命：为 S10_KVQuantTrig 五处同形调用点 *)
(*   （destruct (q_arch_geom B) as [N0 HN0]）提供退化支供给。其目标形：   *)
(*   q_arch_geom : forall A : Q, sigT (fun N : nat => forall t : nat,    *)
(*     NatLe N t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1))。  *)
(*   非退化支（QltT 0 B）由 S02 层反演桥接引理另行供给；                  *)
(*   B≤0 退化支由 N:=0 平凡给出——本件即该退化支的供给模块。                *)
(*                                                                *)
(* 语句对齐注记（形态差显式）：                                          *)
(*   结论面与 S03_QExp 之 q_arch_geom 接口逐字同形（A:=B，含 NatLe 全称、 *)
(*   Qmult (1+1)%Q B 系数位与 Z.of_nat (t+1) # 1 目标形）；               *)
(*   形态差仅一处——q_arch_geom 为无条件形（见证来自 Qarchimedean          *)
(*   抽象构造），本件为退化支条件形：增补退化侧假设                        *)
(*   QleT' (Qmult (1+1)%Q B) 0（2B ≤T 0，全 Set 层面），                  *)
(*   此时 2B ≤ 0 ≤ (t+1)#1 链即闭。                                       *)
(*                                                                *)
(* 结构（两件，sb0_ 前缀）：                                              *)
(*   A 主件：sb0_arch_geom_degen——退化侧假设下 exists 0%nat，             *)
(*      2B ≤ 0 ≤ Z.of_nat (t+1) # 1 两段 Qle 链给出（Qle_of_nat 显式      *)
(*      实例收尾，nat 目标纯数论判定）；                                  *)
(*   B 合并件：sb0_arch_geom_zero_merge——调用点环境假设                   *)
(*      QleT' 0 B（非负界）之下，退化支即夹零支（QleT' 0 B＋QleT' B 0     *)
(*      ⟹ B=0），由序对称性（Qle_antisym）内联收 B==0，零乘               *)
(*      （Qmult_0_r）后入主件。                                           *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全部 Export：QleT'/            *)
(*   Qle_to_QleT'/QleT'_to_Qle/NatLe/Qle_of_nat/qeq_le 皆在 namespaces）  *)
(*   ＋Stdlib QArith（Qle_trans/Qle_antisym/Qmult_0_r 标准件）＋Lia。     *)
(*   前置引理 UpAblQeqBridge 另行供给，本件零依赖之。                     *)
(*                                                                *)
(* 对标：mathlib 置顶使命与声明注释惯例；stdlib 文档注释惯例。            *)
(*                                                                *)
(* 构造性注记：语句面全 Set 层值（QleT'＝S02 Id 形＋sigT 见证）；零承认；  *)
(*   证明全构造；等式换形全部内联于证明内部（不进入语句面）；Qed 闭合。    *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                  *)
(* ============================================================ *)

Check QleT'. Check QleT'_to_Qle. Check Qle_to_QleT'.
Check NatLe. Check NatLe_drop.
Check Qle_of_nat. Check qeq_le. Check Qle_trans.
Check Qle_antisym. Check Qmult_0_r.
Check q_arch_geom.

(* ============================================================ *)
(* §1 · 主件：B≤0 退化支 N:=0 平凡给出（目标形逐字同形）                   *)
(* ============================================================ *)

(* A.1 主件：退化侧假设 2B ≤T 0 下，N:=0 即为合格见证——
   2B ≤ 0 ≤ (t+1)#1 链：首段由假设直接承（QleT'_to_Qle 化为 Qle），
   次段 Qle_of_nat 0 (t+1) 显式实例（Z.of_nat 0 # 1 与 0 定义性重合，
   应用即转换判定；nat 前提 (0 ≤ t+1)%nat 由 le_S，le_n 归纳链闭）。 *)
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
  - apply (Qle_of_nat 0 (t + 1)). clear Ht. induction t as [| t IHt]. + apply le_S. apply le_n. + apply le_S. exact IHt.
Qed.

(* ============================================================ *)
(* §2 · 合并件：调用点环境假设下的退化支给出                                 *)
(* ============================================================ *)

(* B.1 合并件：S10 五处同形调用点的局部假设 QleT' 0 B（非负界）之下，退化支
   即夹零支（0 ≤ B ≤ 0 ⟹ B=0）。由序对称性（Qle_antisym）内联收 B==0，
   由零乘（Qmult_0_r）收 (1+1)%Q·0==0，而后入主件 A.1。 *)
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
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions sb0_arch_geom_degen.
Print Assumptions sb0_arch_geom_zero_merge.
