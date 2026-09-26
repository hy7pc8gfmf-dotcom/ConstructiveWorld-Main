(* ============================================================ *)
(* UpAblHalfPowFeed.v —— hpw_arch_decay_instT 于 S10 五位的实例化供给      *)
(*                                                                *)
(* 使命：UpAblHalfPow 的 hpw_arch_decay_instT（与 arch_decay 语句同形：    *)
(*   sigT(t, QltT (C·(1/2)^{S t}) eps)）在 S10_KVQuantTrig 的五个使用位    *)
(*   （sc_sin_partial_cauchy_bounded、sc_cos_partial_cauchy_bounded、      *)
(*   sc_cs_sq_err_bound、sc_add_sin_err_bound、sc_add_cos_err_bound 的     *)
(*   destruct 上下文）中的逐位实例化，以五个 Corollary 交付。              *)
(*                                                                *)
(* 五位对应（每件复原该位 destruct 前的局部上下文——q_arch_geom／          *)
(*   exp_series_arch 展形、set C/P、非负性证明链——再以 hpw_arch_decay_instT  *)
(*   按原式实例化并 destruct，最后以 sigT 封装见证 (N0, t)）：             *)
(*   hpwf_slot1_sin_cauchy——对应 sc_sin_partial_cauchy_bounded 位；        *)
(*   hpwf_slot2_cos_cauchy——对应 sc_cos_partial_cauchy_bounded 位（同件1 形）； *)
(*   hpwf_slot3_cs_sq——对应 sc_cs_sq_err_bound 位；                        *)
(*   hpwf_slot4_add_sin——对应 sc_add_sin_err_bound 位（同件3 形）；        *)
(*   hpwf_slot5_add_cos——对应 sc_add_cos_err_bound 位（P 换 13 系数式：    *)
(*   13 = (1+1)·(1+1+1+1+1+1)+1，非负性经 q_pow_fact_nonneg 推得）。        *)
(*                                                                *)
(* 非平凡增量：各位的非负性证明链为新建——C 的 QleT' 0 C 与 P 的 Qle 0 P    *)
(*   分别经 q_pow_fact2_nonneg／q_pow_fact_nonneg 与 Qmult_le_0_compat     *)
(*   链推得；几何衰减见证 (N0, t) 本身由 hpw_arch_decay_instT 给出。        *)
(*                                                                *)
(* 构造性注记：全件 Qed 闭合、零承认词面、无经典逻辑；五语句面全 Set 层    *)
(*   值（sigT/QltT/QleT'/NatLe）；语句面无裸命题（Qle 非负前提均为证明内   *)
(*   assert，与 arch_decay 原位一致）；五件 Print Assumptions 全 Closed。   *)
(* 依赖：UpAblHalfPow（hpw_arch_decay_instT）＋CW_ConstructiveWorld_219    *)
(*   ＋stdlib QArith/ZArith/Arith/Setoid/Morphisms/Lia。                   *)
(* 对标：几何衰减级数的阿基米德尾界（stdlib 无直接对应物）。               *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard -LoadLimit 85 -CoreN 2 包裹，   *)
(*   输出经 -o 临时目录，树内 .vo 不重写。                                 *)
(* 范围注记：本件为独立新增件，只供上述五位语句形一致的实例化。            *)
(*                                                                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblHalfPow.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 · 依赖签名核验（标识符漂移即编译期暴露） *)
(* ============================================================ *)

Check q_pow.
Check q_fact.
Check exp_series.
Check q_arch_geom.
Check exp_series_arch.
Check q_pow_fact_nonneg.
Check q_pow_fact2_nonneg.
Check Q2_nonneg.
Check Qmult_le_0_compat.
Check Qle_to_QleT'.
Check QleT'_to_Qle.
Check QltT_to_Qlt.
Check NatLe_lift.
Check arch_decay.
Check hpw_arch_decay_instT.

(* 同形核验：hpw_arch_decay_instT 可置于 arch_decay 的语句型位置（类型注记） *)
Check (hpw_arch_decay_instT
  : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
      sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).

(* 上游假设核验：hpw_arch_decay_instT 的 Print Assumptions 应为 Closed *)
Print Assumptions hpw_arch_decay_instT.

(* ============================================================ *)
(* §1 · 件1（对应 sc_sin_partial_cauchy_bounded 位）                        *)
(*   上下文复原：q_arch_geom 展形→set N0'→set C→非负前提 HC（原位同式），   *)
(*   以 hpw_arch_decay_instT 按原式实例化并 destruct，                     *)
(*   封装 sigT(N0, sigT(t, QltT (C·(1/2)^{S t}) eps))。                    *)
(*   （HN0' 界为 destruct 后的下游推进所设，与本件交付无关。）              *)
(* ============================================================ *)

Corollary hpwf_slot1_sin_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT (((q_pow B (Datatypes.S (2 * N0)) / q_fact (Datatypes.S (2 * N0)))
             * (1 + 1)%Q)
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (N0' := Datatypes.S (2 * N0)).
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C)
    by (unfold C; apply Qle_to_QleT'; apply q_pow_fact2_nonneg;
        exact (QleT'_to_Qle _ _ HB)).
  destruct (hpw_arch_decay_instT C eps HC Hep) as [t Hdec].
  exists N0. exists t. exact Hdec.
Qed.

(* ============================================================ *)
(* §2 · 件2（对应 sc_cos_partial_cauchy_bounded 位）                        *)
(*   上下文与件1 同形（cos 位），实例化同式。                               *)
(* ============================================================ *)

Corollary hpwf_slot2_cos_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT (((q_pow B (Datatypes.S (2 * N0)) / q_fact (Datatypes.S (2 * N0)))
             * (1 + 1)%Q)
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (N0' := Datatypes.S (2 * N0)).
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C)
    by (unfold C; apply Qle_to_QleT'; apply q_pow_fact2_nonneg;
        exact (QleT'_to_Qle _ _ HB)).
  destruct (hpw_arch_decay_instT C eps HC Hep) as [t Hdec].
  exists N0. exists t. exact Hdec.
Qed.

(* ============================================================ *)
(* §3 · 件3（对应 sc_cs_sq_err_bound 位）                                   *)
(*   上下文复原：q_arch_geom＋exp_series_arch 展形→HC0/Htwo0/Hfour0→       *)
(*   set P→HP0 非负性证明链（原位同式），经 Qle_to_QleT' 实例化。           *)
(* ============================================================ *)

Corollary hpwf_slot3_cs_sq : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((1 + 1) * (1 + 1))
             * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _); [exact Qle_0_1 | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by apply Q2_nonneg.
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1)))
    by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + apply q_pow_fact2_nonneg. exact (QleT'_to_Qle _ _ HB). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* ============================================================ *)
(* §4 · 件4（对应 sc_add_sin_err_bound 位）                                 *)
(*   上下文与件3 同形（P 同式），实例化同式。                               *)
(* ============================================================ *)

Corollary hpwf_slot4_add_sin : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((1 + 1) * (1 + 1))
             * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _); [exact Qle_0_1 | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by apply Q2_nonneg.
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1)))
    by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + apply q_pow_fact2_nonneg. exact (QleT'_to_Qle _ _ HB). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* ============================================================ *)
(* §5 · 件5（对应 sc_add_cos_err_bound 位）                                 *)
(*   P 换 13 系数式（13 = (1+1)·(1+1+1+1+1+1)+1），HP0 链原位同式，         *)
(*   实例化同件3 形。                                                      *)
(* ============================================================ *)

Corollary hpwf_slot5_add_cos : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1)
              * (C * (q_pow B N0 / q_fact N0))))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _); [exact Qle_0_1 | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by apply Q2_nonneg.
  assert (Hsix0 : Qle 0 ((1 + 1) * (1 + 1 + 1))) by (unfold Qle; simpl; lia).
  set (P := (((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * (C * (q_pow B N0 / q_fact N0))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply (Qmult_le_0_compat _ _).
    - unfold Qle; simpl; lia.
    - apply (Qmult_le_0_compat C (q_pow B N0 / q_fact N0)).
      + exact HC0.
      + apply q_pow_fact_nonneg. exact (QleT'_to_Qle _ _ HB). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* ============================================================ *)
(* 假设审计：五件 Print Assumptions 全 Closed（零外部未证假设）              *)
(* ============================================================ *)

Print Assumptions hpwf_slot1_sin_cauchy.
Print Assumptions hpwf_slot2_cos_cauchy.
Print Assumptions hpwf_slot3_cs_sq.
Print Assumptions hpwf_slot4_add_sin.
Print Assumptions hpwf_slot5_add_cos.
