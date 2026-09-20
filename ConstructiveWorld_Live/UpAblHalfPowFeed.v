(* ============================================================ *)
(* UpAblHalfPowFeed.v —— S10 五槽位 hpw_arch_decay_instT 平替直配件        *)
(* （P4b 席·20260920，P4 席谱系件后续①：五槽位平替直配·零前置件）          *)
(*                                                                *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   五语句面全 Set 层值（sigT／QltT／QleT'／NatLe 皆 S01/S02 Id 形），     *)
(*   语句面无裸命题（槽内 Qle 非负证书全为 assert 内部位，与 S10 原位一致）。 *)
(*                                                                *)
(* 任务：消费 UpAblHalfPow.v 的 hpw_arch_decay_instT（与 S03:402 arch_decay *)
(*   语句逐字同形），对 S10_KVQuantTrig.v 五坐标（:1682/:1728/:6436/       *)
(*   :11100/:12022）逐位做 destruct 契约平替直配，新独立件交付。            *)
(*   禁碰 S10/UpAblHalfPow/任何既有文件；未入 order.txt/_CoqProject。       *)
(*                                                                *)
(* 五槽 destruct 契约对表（逐处实录）：                                    *)
(*   槽1 :1682 sc_sin_partial_cauchy_bounded                               *)
(*         destruct (arch_decay C eps HC Hep) as [t Hdec]，HC 直供；       *)
(*   槽2 :1728 sc_cos_partial_cauchy_bounded——同槽1 形；                   *)
(*   槽3 :6436 sc_cs_sq_err_bound                                         *)
(*         destruct (arch_decay P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht]；*)
(*   槽4 :11100 sc_add_sin_err_bound——同槽3 形（P 同式）；                 *)
(*   槽5 :12022 sc_add_cos_err_bound——同槽3 形（P 换 13 系数式）。          *)
(*   实形核验：五处消费面与供体语句形逐字同构（HC/HP0 非负证书五处          *)
(*   原位已在，Qle_to_QleT' 换形位同在），**无一坐标异构**，零 shim 成立。  *)
(*                                                                *)
(* 直配形态（逐位）：复原该槽 destruct 前的精确局部上下文                   *)
(*   （q_arch_geom／exp_series_arch 展形＋set C/P＋HC/HP0 证书链），        *)
(*   以 hpw_arch_decay_instT 按该槽原式实例化并 destruct，再按该槽消费方式  *)
(*   打包 sigT 见证。尾部 exact 为直配消费步（适配消费级，如实定性）；       *)
(*   非平凡增量＝各槽上下文证书链的真实现（q_pow_fact2_nonneg／             *)
(*   Qmult_le_0_compat 链）＋sigT 打包。                                  *)
(*                                                                *)
(* 定性申报（红线③）：本件为「适配消费级」直配件——供体 D 件已全款交付       *)
(*   可计算见证谱系，本件只证平替在各槽位可落地（五 Corollary 全 Closed）。  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblHalfPow.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0 · 体检（缺位即刻响亮失败）                                       *)
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

(* 契约对表核内验证：供体可处于 arch_decay 的语句型位置（转换性同形） *)
Check (hpw_arch_decay_instT
  : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
      sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).

(* 上游谱系闭合探针：非 Closed 则本席响亮失败 *)
Print Assumptions hpw_arch_decay_instT.

(* ============================================================ *)
(* Part 1 · 槽1 直配（S10:1682，sc_sin_partial_cauchy_bounded）            *)
(*   槽内上下文复原：q_arch_geom 展形→set N0'→set C→HC 证书（原位同式），   *)
(*   直配 destruct（原式 arch_decay C eps HC Hep 换供体），                *)
(*   打包 sigT(N0, sigT(t, QltT (C·(1/2)^{S t}) eps))。                   *)
(*   （槽内 HN0' 界为 destruct 后下游推进件，与直配无关，零影响。）          *)
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
(* Part 2 · 槽2 直配（S10:1728，sc_cos_partial_cauchy_bounded）            *)
(*   槽内上下文与槽1 逐字同形（cos 位），直配同式。                          *)
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
(* Part 3 · 槽3 直配（S10:6436，sc_cs_sq_err_bound）                       *)
(*   槽内上下文复原：q_arch_geom＋exp_series_arch 展形→HC0/Htwo0/Hfour0→    *)
(*   set P→HP0 证书（七行原位同式），直配 destruct（Qle_to_QleT' 换形位同在）。 *)
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
    by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
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
(* Part 4 · 槽4 直配（S10:11100，sc_add_sin_err_bound）                    *)
(*   槽内上下文与槽3 逐字同形（P 同式），直配同式。                          *)
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
    by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
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
(* Part 5 · 槽5 直配（S10:12022，sc_add_cos_err_bound）                    *)
(*   槽内上下文复原：P 换 13 系数式（13 = (1+1)(1+…+1)+1），HP0 原位同式，   *)
(*   直配 destruct 同槽3 形。                                             *)
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
    by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
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
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions hpwf_slot1_sin_cauchy.
Print Assumptions hpwf_slot2_cos_cauchy.
Print Assumptions hpwf_slot3_cs_sq.
Print Assumptions hpwf_slot4_add_sin.
Print Assumptions hpwf_slot5_add_cos.
