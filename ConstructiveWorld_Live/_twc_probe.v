(* ============================================================
   _twc_probe.v —— Q 层幂与阶乘引擎最小检验件。
   ── 使命：为 Padé 运输链提供 q_pow／q_fact 的最小可编译检验面：
   Fixpoint 定义＋样例恒等 q_pow s 8 / q_fact 8 · 2 == s⁸/20160
   的 field 判定（上游件 Require 冒烟入口）。
   ── 依赖：Stdlib QArith.Qring、QArith.QArith、Lqa、Lia。
   ── 构造性注记：纯构造性、零公理面；q_pow／q_fact 全 Defined
   可提取。
   ── 编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" _twc_probe.v。
   ============================================================ *)
From Stdlib Require Import QArith.Qring QArith.QArith Lqa Lia.
Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => x * q_pow x m
  end.
Fixpoint q_fact (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => (Z.of_nat (Datatypes.S m) # 1) * q_fact m
  end.
Goal forall s : Q, q_pow s 8 / q_fact 8 * (1+1) == s*s*s*s*s*s*s*s/20160.
intros s. cbn [q_pow q_fact]. field. Show.
Qed.
