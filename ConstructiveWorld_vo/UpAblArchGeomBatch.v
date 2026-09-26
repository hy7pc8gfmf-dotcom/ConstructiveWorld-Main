(* ============================================================ *)
(* UpAblArchGeomBatch.v —— S10 q_arch_geom 调和界语句形的批量供给件       *)
(*   （四个使用位共用同一语句形与同一证明）                                *)
(*                                                                *)
(* 使命：S10 尾界链中五个同形指标位——destruct (q_arch_geom B) 后供给       *)
(*   sigT(N, forall t ≥ N, 2·B ≤ (t+1)#1)——中四位（对应                   *)
(*   sc_cos_partial_cauchy_bounded、sc_cs_sq_err_bound、                   *)
(*   sc_add_sin_err_bound、sc_add_cos_err_bound）由本件四引理覆盖；        *)
(*   指标 N 经 qbg_arch_geom_direct 具体化（取                             *)
(*   N := uabS4b_arch_N (Qinv 2B)，调和反演在其中完成）。                  *)
(*                                                                *)
(* 范围注记：样板位 sc_sin_partial_cauchy_bounded 已由 qbg_arch_geom_direct *)
(*   直接覆盖，本件不重复立件。                                            *)
(*                                                                *)
(* 四件同形同证（语句与证明逐件相同）：                                    *)
(*   qag_arch_geom_cos_cauchy（对应 sc_cos_partial_cauchy_bounded 使用位） *)
(*   qag_arch_geom_cs_sq（对应 sc_cs_sq_err_bound 使用位）                 *)
(*   qag_arch_geom_add_sin（对应 sc_add_sin_err_bound 使用位）             *)
(*   qag_arch_geom_add_cos（对应 sc_add_cos_err_bound 使用位）             *)
(*                                                                *)
(* 用法：对应 S10 使用位处改用本件引理，如                                 *)
(*   destruct (qag_arch_geom_cos_cauchy B) as [N0 HN0].；与原              *)
(*   destruct (q_arch_geom B) as [N0 HN0]. 语句面同形，下游对              *)
(*   HN0 的使用零改动。                                                    *)
(*                                                                *)
(* 构造性注记：全件 Qed 闭合、零承认词面、无经典逻辑；四条交付语句面全     *)
(*   Set 层（sigT/NatLe/QleT'）；四件 Print Assumptions 全 Closed。         *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219 ＋ UpAblAbsSumLeB2 ＋ UpAblQeqBridge。    *)
(* 对标：阿基米德性质的具体指标化（stdlib QArith 无直接对应物）。           *)
(* 编译配方：Rocq 9.1 coqc 直调＋cpu_guard 包裹，输出经 -o 临时目录，树内 .vo 不重写。 *)
(* ============================================================ *)

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
