(* ==========================================================================)
   UpAblArchGeomBatch.v — S10 尾界链四个同形指标位的批量供给引理
   使命: q_arch_geom 调和界语句形的四条引理（cos/cs_sq/add_sin/add_cos 使用位共用同一语句形与证明），指标 N 经 qbg_arch_geom_direct 具体化（调和反演在其中完成）。
   依赖: List、QArith、QArith.Qabs、QArith.Qring、Lia、Lqa、CW_ConstructiveWorld_219、UpAblAbsSumLeB2、UpAblQeqBridge。
   对标: 阿基米德性质的具体指标化（stdlib QArith 无直接对应物）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；四条交付语句面全 Set 层（sigT/NatLe/QleT′）；四件 Print Assumptions 全 Closed。
   编译配方: Rocq 9.1 coqc 直调与 cpu_guard 包裹，输出经 -o 临时目录，树内 .vo 不重写。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.
Require Import UpAblQeqBridge.

(* ============================================================ *)
(* §0 · 依赖签名核验（标识符漂移即编译期暴露） *)
(* ============================================================ *)

Check qbg_arch_geom_direct.
Check q_arch_geom.
Check sigT.
Check NatLe. Check NatLe_lift. Check NatLe_drop.
Check QleT'. Check Qle_to_QleT'.

(* ============================================================ *)
(* §A1 · 对应 sc_cos_partial_cauchy_bounded 使用位                          *)
(* ============================================================ *)

Corollary qag_arch_geom_cos_cauchy : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* ============================================================ *)
(* §A2 · 对应 sc_cs_sq_err_bound 使用位                                     *)
(* ============================================================ *)

Corollary qag_arch_geom_cs_sq : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* ============================================================ *)
(* §A3 · 对应 sc_add_sin_err_bound 使用位                                   *)
(* ============================================================ *)

Corollary qag_arch_geom_add_sin : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* ============================================================ *)
(* §A4 · 对应 sc_add_cos_err_bound 使用位                                   *)
(* ============================================================ *)

Corollary qag_arch_geom_add_cos : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* ============================================================ *)
(* 假设审计：四件 Print Assumptions 全 Closed                               *)
(* ============================================================ *)

Print Assumptions qag_arch_geom_cos_cauchy.
Print Assumptions qag_arch_geom_cs_sq.
Print Assumptions qag_arch_geom_add_sin.
Print Assumptions qag_arch_geom_add_cos.
