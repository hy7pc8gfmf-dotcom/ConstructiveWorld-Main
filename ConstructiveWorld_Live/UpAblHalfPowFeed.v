(* ==========================================================================)
   UpAblHalfPowFeed.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：hpw_half_step、hpw_half_pow_inv_le、hpw_half_pow_inv_pos、hpw_arch_decay_instT、hpwf_slot1_sin_cauchy、hpwf_slot2_cos_cauchy、hpwf_slot3_cs_sq、hpwf_slot4_add_sin、hpwf_slot5_add_cos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
From Stdlib Require Import Setoid Morphisms.

(* ================= §1 hpw_half_step 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* §0 · 库内符号核验（签名不符即编译失败）                                 *)

Check q_pow.
Check q_half_pow_le_inv.
Check Qle_refl.
Check QleT'_to_Qle.
Check Qle_to_QleT'.
Check QltT_to_Qlt.
Check Qlt_to_QltT.
Check Qle_lt_trans.
Check Qmult_le_compat_r.
Check Z.mul_le_mono_nonneg_r.
Check Z.mul_le_mono_nonneg_l.
Check Pos.of_succ_nat.

(* 上游谱系闭合核验：q_half_pow_le_inv 非 Closed 则需另行自证 *)
Print Assumptions q_half_pow_le_inv.

(* §A · 递归形（几何减半的定义性恒等式，QleT' 形）                        *)

Lemma hpw_half_step : forall n : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S n)) ((1 / 2)%Q * q_pow (1 / 2)%Q n).
Proof.
  intro n.
  exact (Qle_to_QleT' _ _
  (qeq_le _ _ (Qeq_refl ((1 / 2)%Q * q_pow (1 / 2)%Q n)))).
Qed.

(* §B · 单位分数桥接引理（使用 S03 (1/2)^n 谱系，S t 实例）                *)

Corollary hpw_half_pow_inv_le : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1)).
Proof.
  intro t.
  exact (Qle_to_QleT' _ _ (q_half_pow_le_inv (Datatypes.S t))).
Qed.


(* §C · Qfloor 形接口（1#Pos.of_succ_nat 形，S4B 谱系同形对接）            *)

Corollary hpw_half_pow_inv_pos : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1#(Pos.of_succ_nat (Datatypes.S t))).
Proof.
  intro t.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1))).
  - exact (q_half_pow_le_inv (Datatypes.S t)).
  - change (Z.of_nat (Datatypes.S t + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (t + 1)%nat)).
    replace (t + 1)%nat with (Datatypes.S t) by (symmetry; apply Nat.add_1_r).
    unfold Qle. cbn [Qdiv Qinv Qnum Qden Qmult]. apply Z.le_refl.
Qed.

(* §D · 目标语句供给（arch_decay 语句逐字同形，见证全具体）                *)
(*   见证：t0 := Z.to_nat(Z.max 0 (c·f) + 1)，c/f 为 C/eps 展形分量；      *)
(*   链：(1/2)^{S t0} ≤ 1/((S t0+1)#1)（经 §B 引理）⟹ C·(1/2)^{S t0} < eps， *)
(*   其中 c·f < e·d·q 的非线性步以 Z.mul 单调件显式供给（Hed1/Hmul），      *)
(*   线性部分由 lia 收尾。                                                *)

Corollary hpw_arch_decay_instT : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
  sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps).
Proof.
  intros C eps HC Hep.
  destruct C as [c d]. destruct eps as [e f].
  assert (Hepos : (0 < e)%Z).
  { pose proof (QltT_to_Qlt 0 (Qmake e f) Hep) as Hlt0.
    unfold Qlt in Hlt0. simpl in Hlt0.
    rewrite Z.mul_1_r in Hlt0. exact Hlt0. }
  assert (Hed1 : (1 <= e * Z.pos d)%Z).
  { assert (Hpd : (0 < Z.pos d)%Z) by exact (Pos2Z.is_pos d).
    assert (Hpd1 : (1 <= Z.pos d)%Z).
    { exact (proj2 (Z.le_succ_l 0 (Z.pos d)) Hpd). }
    assert (He1 : (1 <= e)%Z).
    { exact (proj2 (Z.le_succ_l 0 e) Hepos). }
    assert (Hstep : (Z.pos d <= e * Z.pos d)%Z).
    { pose proof (Z.mul_le_mono_nonneg_r 1 e (Z.pos d)
                     (Z.lt_le_incl 0 (Z.pos d) Hpd) He1) as Hm.
      rewrite Z.mul_1_l in Hm. exact Hm. }
    exact (Z.le_trans 1 (Z.pos d) (e * Z.pos d) Hpd1 Hstep). }
  exists (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)).
  assert (Hqv : (Z.max 0 (c * Z.pos f) + 1
                 <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))%Z).
  { change (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
      with (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    assert (Hge : (0 <= Z.max 0 (c * Z.pos f) + 1)%Z).
    { apply (Z.le_trans 0 (Z.max 0 (c * Z.pos f))
               (Z.succ (Z.max 0 (c * Z.pos f)))).
      - exact (Z.le_max_l 0 (c * Z.pos f)).
      - exact (Z.le_le_succ_r (Z.max 0 (c * Z.pos f)) (Z.max 0 (c * Z.pos f))
                 (Z.le_refl (Z.max 0 (c * Z.pos f)))). }
    rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add.
    rewrite (Z2Nat.id (Z.max 0 (c * Z.pos f) + 1) Hge).
    change (Z.of_nat 1) with 1%Z.
    apply (Z.le_trans (Z.max 0 (c * Z.pos f) + 1)
                      (Z.succ (Z.max 0 (c * Z.pos f) + 1))).
    - apply Z.le_succ_diag_r.
    - apply Z.le_succ_diag_r. }
  assert (Hmul : (Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * 1
                  <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))
                       * (e * Z.pos d))%Z).
  { apply (Z.mul_le_mono_nonneg_l 1 (e * Z.pos d)
             (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
    - exact (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)).
    - exact Hed1. }
  assert (Hpow : Qle (q_pow (1 / 2)%Q
                            (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)))
                      * (c # d))
                     ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))).
  { apply (Qmult_le_compat_r (q_pow (1 / 2)%Q
                             (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))))
                             (1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                             (c # d)).
    - exact (q_half_pow_le_inv (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)))).
    - apply QleT'_to_Qle. exact HC. }
  assert (Hmid : Qlt ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))
                     (e # f)).
  { change (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    unfold Qlt. cbn [Qdiv Qinv Qnum Qden Qmult].
    rewrite !Z.mul_1_l.
    assert (Hcf : Z.lt (c * Z.pos f)
                       (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
    { apply (Z.lt_le_trans (c * Z.pos f) (Z.succ (c * Z.pos f))
               (Z.pos (Pos.of_succ_nat
                    (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
      - apply Z.lt_succ_diag_r.
      - apply (Z.le_trans (Z.succ (c * Z.pos f))
                 (Z.succ (Z.max 0 (c * Z.pos f)))
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
        + apply (proj1 (Z.succ_le_mono (c * Z.pos f) (Z.max 0 (c * Z.pos f)))).
          exact (Z.le_max_r 0 (c * Z.pos f)).
        + exact Hqv. }
    assert (He1 : (1 <= e)%Z).
    { exact (proj2 (Z.le_succ_l 0 e) Hepos). }
    assert (Hd1 : (1 <= Z.pos d)%Z).
    { exact (proj2 (Z.le_succ_l 0 (Z.pos d)) (Pos2Z.is_pos d)). }
    assert (HP : Z.le (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                       (e * (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))
                             * Z.pos d))).
    { apply (Z.le_trans _ (e * Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))) _).
      - exact (Z.mul_le_mono_nonneg_r 1 e
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                 (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)) He1).
      - pose proof (Z.mul_le_mono_nonneg_l 1 (Z.pos d)
                       (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                       (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)) Hd1) as Hm2.
        rewrite Z.mul_1_r in Hm2.
        exact (Z.mul_le_mono_nonneg_l
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * Z.pos d)
                 e (Z.lt_le_incl 0 e Hepos) Hm2). }
    exact (Z.lt_le_trans (c * Z.pos f)
             (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
             (e * (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * Z.pos d))
             Hcf HP). }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
          (q_pow (1 / 2)%Q (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))) * (c # d)) _).
  - apply qeq_le. apply Qmult_comm.
  - exact (Qle_lt_trans _ _ _ Hpow Hmid).
Qed.

(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)

Print Assumptions hpw_half_step.
Print Assumptions hpw_half_pow_inv_le.
Print Assumptions hpw_half_pow_inv_pos.
Print Assumptions hpw_arch_decay_instT.
(* ================= §2 hpwf_slot1_sin_cauchy 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* §0 · 依赖签名核验（标识符漂移即编译期暴露） *)

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

(* §1 · 件1（对应 sc_sin_partial_cauchy_bounded 位）                        *)
(*   上下文复原：q_arch_geom 展形→set N0'→set C→非负前提 HC（原位同式），   *)
(*   以 hpw_arch_decay_instT 按原式实例化并 destruct，                     *)
(*   封装 sigT(N0, sigT(t, QltT (C·(1/2)^{S t}) eps))。                    *)
(*   （HN0' 界为 destruct 后的下游推进所设，与本件交付无关。）              *)

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

(* §2 · 件2（对应 sc_cos_partial_cauchy_bounded 位）                        *)
(*   上下文与件1 同形（cos 位），实例化同式。                               *)

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

(* §3 · 件3（对应 sc_cs_sq_err_bound 位）                                   *)
(*   上下文复原：q_arch_geom＋exp_series_arch 展形→HC0/Htwo0/Hfour0→       *)
(*   set P→HP0 非负性证明链（原位同式），经 Qle_to_QleT' 实例化。           *)

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

(* §4 · 件4（对应 sc_add_sin_err_bound 位）                                 *)
(*   上下文与件3 同形（P 同式），实例化同式。                               *)

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

(* §5 · 件5（对应 sc_add_cos_err_bound 位）                                 *)
(*   P 换 13 系数式（13 = (1+1)·(1+1+1+1+1+1)+1），HP0 链原位同式，         *)
(*   实例化同件3 形。                                                      *)

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

(* 假设审计：五件 Print Assumptions 全 Closed（零外部未证假设）              *)

Print Assumptions hpwf_slot1_sin_cauchy.
Print Assumptions hpwf_slot2_cos_cauchy.
Print Assumptions hpwf_slot3_cs_sq.
Print Assumptions hpwf_slot4_add_sin.
Print Assumptions hpwf_slot5_add_cos.
