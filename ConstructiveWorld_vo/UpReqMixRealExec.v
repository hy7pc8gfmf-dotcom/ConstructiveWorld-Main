(* ==========================================================================)
   UpReqMixRealExec.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：mix2_swap_ring、mix2_step_ring、mix2_bernoulli、mix2_budget_at、mix2_pow_budget、mix2_mult_one_l、mix2_k_select、mrx_arch_n、mrx_k_compute。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixingTime.

(* ================= §1 mix2_swap_ring 族 ================= *)
From Stdlib Require Import QArith.Qring.

Local Open Scope Q_scope.

(* 常量环式归一 tactic（承源模块 mix_rring 口径：实元解构+cbn+Q 环） *)
Ltac mix2_ring :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_const real_of_nat mix_scale tv_omd] in *;
  ring.

(* ============ 常量证书族（提取后 = fun _ _ _ _ => N=0，零成本） ============ *)

(* 乘换位：(w·q)·c == (w·c)·q —— 替代 mix_mult_swap（其 compat 是性能瓶颈根源） *)
Lemma mix2_swap_ring : forall w q c : Real,
  real_eq (real_mult (real_mult w q) c) (real_mult (real_mult w c) q).
Proof. intros w q c. mix2_ring. Qed.

(* 步进环式恒等式：κ·(1+((1−κ)+m)) == (1+m) − ((1−κ)+m)·(1−κ)
   （κ 形 Bernoulli 归纳步的收缩恒等式；替代 mix_ring_sc 的 κ 形用法） *)
Lemma mix2_step_ring : forall c m : Real,
  real_eq
    (real_mult c (real_plus real_one (real_plus (real_minus_r real_one c) m)))
    (real_minus_r (real_plus real_one m)
       (real_mult (real_plus (real_minus_r real_one c) m)
                  (real_minus_r real_one c))).
Proof. intros c m. mix2_ring. Qed.

(* ============ κ 形 Bernoulli 上形式（路线一核心件） ========================
   κ^k · (1 + k·(1−κ)) ≤ 1（0<κ<1；幂直接在 κ 上，零幂传递）               *)
Lemma mix2_bernoulli : forall (kappa : Real) (k : nat),
  real_le real_zero kappa -> real_lt real_zero kappa ->
  real_le kappa real_one -> real_lt kappa real_one ->
  real_le (real_mult (tv_rpow kappa k)
                     (real_plus real_one
                        (mix_scale k (real_minus_r real_one kappa))))
          real_one.
Proof.
  intros kappa k Hk0 Hkp Hk1 Hk2. induction k as [| k IH].
  - (* k = 0：1·(1+0) == 1 *)
    apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_mult real_one
                (real_plus real_one (mix_scale 0 (real_minus_r real_one kappa))))
             (real_mult real_one real_one)).
    + apply (RealSetoid.real_eq_mult_compat real_one
               (real_plus real_one (mix_scale 0 (real_minus_r real_one kappa)))
               real_one real_one
               (real_eq_refl real_one) (real_plus_zero real_one)).
    + exact (real_mult_one real_one).
  - (* 归纳步：环式恒等式 κ·(1+(S k)·w) == (1+k·w) − ((S k)·w)·w（w:=1−κ）；
       子 claim κ·(1+(S k)·w) ≤ 1+k·w；乘 κ^k 接 IH。全常量环式归一。 *)
    assert (Hbpos : real_lt real_zero (real_minus_r real_one kappa))
      by exact (tv_omd_pos_of_lt kappa Hk2).
    assert (HPk : real_lt real_zero (tv_rpow kappa k))
      by exact (mix_rpow_pos kappa k Hkp).
    assert (HC : real_lt real_zero
              (real_mult (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))
                         (real_minus_r real_one kappa)))
      by exact (real_mult_pos_compat
                  (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))
                  (real_minus_r real_one kappa)
                  (mix_scale_S_pos (real_minus_r real_one kappa) k Hbpos) Hbpos).
    assert (HeqSC : real_eq
              (real_mult kappa
                 (real_plus real_one
                    (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
              (real_minus_r (real_plus real_one
                                 (mix_scale k (real_minus_r real_one kappa)))
                 (real_mult (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))
                            (real_minus_r real_one kappa))))
      by exact (mix2_step_ring kappa (mix_scale k (real_minus_r real_one kappa))).
    assert (HSC : real_le
              (real_mult kappa
                 (real_plus real_one
                    (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
              (real_plus real_one (mix_scale k (real_minus_r real_one kappa)))).
    { apply (real_le_trans _
               (real_minus_r (real_plus real_one
                                 (mix_scale k (real_minus_r real_one kappa)))
                  (real_mult (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))
                             (real_minus_r real_one kappa)))).
      - apply (RealSetoid.real_eq_le). exact HeqSC.
      - apply (real_le_trans _
                 (real_plus (real_minus_r (real_plus real_one
                                    (mix_scale k (real_minus_r real_one kappa)))
                               (real_mult (mix_scale (Datatypes.S k)
                                             (real_minus_r real_one kappa))
                                          (real_minus_r real_one kappa)))
                            (real_mult (mix_scale (Datatypes.S k)
                                          (real_minus_r real_one kappa))
                                       (real_minus_r real_one kappa)))).
        + exact (igr_le_plus_r _ _ HC).
        + apply (RealSetoid.real_eq_le).
          exact (mix_ring_cancel _ _). }
    assert (HeqR : real_eq
              (real_mult (real_mult kappa (tv_rpow kappa k))
                         (real_plus real_one
                            (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
              (real_mult (real_mult kappa
                            (real_plus real_one
                               (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
                         (tv_rpow kappa k)))
      by exact (mix2_swap_ring kappa (tv_rpow kappa k)
                  (real_plus real_one
                     (mix_scale (Datatypes.S k) (real_minus_r real_one kappa)))).
    assert (IH' : real_le
              (real_mult (real_plus real_one
                            (mix_scale k (real_minus_r real_one kappa)))
                         (tv_rpow kappa k))
              real_one).
    { apply (real_le_trans _
               (real_mult (tv_rpow kappa k)
                          (real_plus real_one
                             (mix_scale k (real_minus_r real_one kappa))))).
      - apply (RealSetoid.real_eq_le). exact (real_mult_comm _ _).
      - exact IH. }
    apply (real_le_trans
             (real_mult (real_mult kappa (tv_rpow kappa k))
                   (real_plus real_one
                      (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
             (real_mult (real_plus real_one
                          (mix_scale k (real_minus_r real_one kappa)))
                (tv_rpow kappa k))
             real_one).
    + apply (real_le_trans _
               (real_mult (real_mult kappa
                             (real_plus real_one
                                (mix_scale (Datatypes.S k)
                                           (real_minus_r real_one kappa))))
                          (tv_rpow kappa k))).
      * apply (RealSetoid.real_eq_le). exact HeqR.
      * exact (real_le_mult_compat
                 (real_mult kappa
                    (real_plus real_one
                       (mix_scale (Datatypes.S k) (real_minus_r real_one kappa))))
                 (real_plus real_one
                    (mix_scale k (real_minus_r real_one kappa)))
                 (tv_rpow kappa k) HPk HSC).
    + exact IH'.
Qed.

(* ============ 路线二：逐层按需交付（k 由外部迭代器给定） ====================
   门证书 real_lt TV0 (budget·(1+k·(1−κ))) 由 OCaml 侧按层构造（全数据件）；  *)
(*   本件给出该层闭合定理：门真 ⟹ sigT k（κ^k·TV0 < budget）。               *)
Theorem mix2_budget_at : forall (kappa TV0 budget : Real) (k : nat),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  real_lt TV0 (real_mult budget
                 (real_plus real_one
                    (mix_scale k (real_minus_r real_one kappa)))) ->
  sigT (fun j : nat => real_lt (real_mult (tv_rpow kappa j) TV0) budget).
Proof.
  intros kappa TV0 budget k Hk1 Hk2 Ha Hbudget Hgate.
  assert (Hk0 : real_le real_zero kappa).
  { apply (RealSetoid.real_lt_le_iff_req real_zero kappa). left. exact Hk1. }
  assert (Hk1le : real_le kappa real_one).
  { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left. exact Hk2. }
  assert (Hbern : real_le
              (real_mult (tv_rpow kappa k)
                 (real_plus real_one
                    (mix_scale k (real_minus_r real_one kappa))))
              real_one)
    by exact (mix2_bernoulli kappa k Hk0 Hk1 Hk1le Hk2).
  assert (HPk : real_lt real_zero (tv_rpow kappa k))
    by exact (mix_rpow_pos kappa k Hk1).
  (* 预算分支：TV0·κ^k < (budget·boost)·κ^k —— lt 数据件 + 常量换位 *)
  assert (Hstep : real_lt (real_mult TV0 (tv_rpow kappa k))
                    (real_mult (real_mult budget
                                  (real_plus real_one
                                     (mix_scale k (real_minus_r real_one kappa))))
                               (tv_rpow kappa k)))
    by exact (real_mult_lt_compat TV0
                (real_mult budget
                   (real_plus real_one
                      (mix_scale k (real_minus_r real_one kappa))))
                (tv_rpow kappa k) Hgate HPk).
  assert (E1 : real_eq (real_mult (tv_rpow kappa k) TV0)
                       (real_mult TV0 (tv_rpow kappa k)))
    by exact (real_mult_comm _ _).
  assert (Hlt1 : real_lt (real_mult (tv_rpow kappa k) TV0)
                   (real_mult (real_mult budget
                                 (real_plus real_one
                                    (mix_scale k (real_minus_r real_one kappa))))
                              (tv_rpow kappa k)))
    by exact (real_eq_lt_lt _ _ _ E1 Hstep).
  assert (E2 : real_eq
           (real_mult (real_mult budget
                         (real_plus real_one
                            (mix_scale k (real_minus_r real_one kappa))))
                      (tv_rpow kappa k))
           (real_mult budget
              (real_mult (tv_rpow kappa k)
                 (real_plus real_one
                    (mix_scale k (real_minus_r real_one kappa))))))
    by exact (real_eq_trans _ _ _
                (mix2_swap_ring budget
                   (real_plus real_one
                      (mix_scale k (real_minus_r real_one kappa)))
                   (tv_rpow kappa k))
                (real_eq_sym _ _
                   (real_mult_assoc budget
                      (tv_rpow kappa k)
                      (real_plus real_one
                         (mix_scale k (real_minus_r real_one kappa)))))).
  assert (Hlt2 : real_lt (real_mult (tv_rpow kappa k) TV0)
                   (real_mult budget
                      (real_mult (tv_rpow kappa k)
                         (real_plus real_one
                            (mix_scale k (real_minus_r real_one kappa))))))
    by exact (real_lt_eq_lt _ _ _ Hlt1 E2).
  (* Bernoulli 分支：budget·(κ^k·boost) ≤ budget·1 ≤ budget —— 常量桥 *)
  assert (Hbern' : real_le
              (real_mult budget
                 (real_mult (tv_rpow kappa k)
                    (real_plus real_one
                       (mix_scale k (real_minus_r real_one kappa)))))
              (real_mult budget real_one)).
  { apply (real_le_trans _
             (real_mult (real_mult (tv_rpow kappa k)
                          (real_plus real_one
                             (mix_scale k (real_minus_r real_one kappa))))
                        budget)).
    - apply (RealSetoid.real_eq_le).
      exact (real_mult_comm budget
               (real_mult (tv_rpow kappa k)
                  (real_plus real_one
                     (mix_scale k (real_minus_r real_one kappa))))).
    - apply (real_le_trans _ (real_mult real_one budget)).
      + exact (real_le_mult_compat
                 (real_mult (tv_rpow kappa k)
                    (real_plus real_one
                       (mix_scale k (real_minus_r real_one kappa))))
                 real_one budget Hbudget Hbern).
      + apply (RealSetoid.real_eq_le).
        exact (real_mult_comm real_one budget). }
  assert (E3 : real_eq (real_mult budget real_one) budget)
    by exact (real_eq_trans _ _ _
                (real_mult_comm budget real_one) (mix_mult_one_l budget)).
  exists k.
  exact (real_lt_le_trans _ _ _
           Hlt2
           (real_le_trans _
              (real_mult budget real_one)
              budget
              Hbern'
              (RealSetoid.real_eq_le _ _ E3))).
Qed.

(* ============ 路线一主定理：mix2_pow_budget（arch 全自形态，同上游口径）
   与源模块同构，但主链换 κ 形 Bernoulli + 常量桥尾（去 eq-compat 幂爆炸）         *)
Theorem mix2_pow_budget : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  assert (hwp : real_lt real_zero (real_minus_r real_one kappa))
    by exact (tv_omd_pos_of_lt kappa Hk2).
  assert (Hwb : real_lt real_zero
              (real_mult (real_minus_r real_one kappa) budget))
    by exact (real_mult_pos_compat (real_minus_r real_one kappa) budget
                hwp Hbudget).
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                Hwb))) as [N [Hge2 HN]].
  destruct N as [| N'].
  - exfalso. exact (Nat.nle_succ_0 1%nat Hge2).
  - set (w := real_minus_r real_one kappa) in *.
    set (wb := real_mult w budget) in *.
    set (Ms := mix_scale (Datatypes.S N') w) in *.
    set (boost := real_plus real_one Ms) in *.
    set (mR := real_const (Z.of_nat (Datatypes.S N') # 1)).
    (* ---- 预算分支（承源模块，实测瞬时：全 O(N') 数据/常量件） ---- *)
    assert (Hstep : real_lt (real_mult (real_mult TV0
                                   (real_inv_pos wb Hwb)) wb)
                         (real_mult mR wb))
      by exact (real_mult_lt_compat _ _ _ HN Hwb).
    assert (HeqL : real_eq (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                         TV0).
    { apply (real_eq_trans _ (real_mult wb (real_mult TV0 (real_inv_pos wb Hwb)))).
      - exact (real_mult_comm _ _).
      - exact (real_mult_div wb TV0 Hwb). }
    assert (HeqR : real_eq (real_mult mR wb) (real_mult Ms budget)).
    { apply (real_eq_trans _ (mix_scale (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_eq_const (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_mult_distrib (Datatypes.S N') w budget)). }
    assert (Hb0 : real_lt TV0 (real_mult Ms budget)).
    { exact (real_lt_eq_lt TV0 (real_mult mR wb) (real_mult Ms budget)
               (real_eq_lt_lt TV0
                  (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                  (real_mult mR wb) (real_eq_sym _ _ HeqL) Hstep)
               HeqR). }
    assert (HeqBud : real_eq (real_mult budget boost)
                         (real_plus budget (real_mult Ms budget))).
    { apply (real_eq_trans _
               (real_plus (real_mult budget real_one)
                  (real_mult budget Ms))).
      - exact (real_distrib budget real_one Ms).
      - apply (RealSetoid.real_eq_plus_compat (real_mult budget real_one)
                 (real_mult budget Ms) budget (real_mult Ms budget)
                 (real_mult_one budget) (real_mult_comm budget Ms)). }
    assert (Hbud : real_lt TV0 (real_mult budget boost)).
    { apply (real_lt_eq_lt TV0 (real_plus (real_mult Ms budget) budget)
               (real_mult budget boost)).
      - exact (real_lt_le_trans TV0 (real_mult Ms budget)
                 (real_plus (real_mult Ms budget) budget) Hb0
                 (igr_le_plus_r (real_mult Ms budget) budget Hbudget)).
      - exact (real_eq_trans (real_plus (real_mult Ms budget) budget)
                 (real_plus budget (real_mult Ms budget))
                 (real_mult budget boost)
                 (real_plus_comm (real_mult Ms budget) budget)
                 (real_eq_sym _ _ HeqBud)). }
    exists (Datatypes.S N').
    (* ---- 主链（κ 形 Bernoulli + 常量桥尾，零幂传递零 compat 幂炸） ---- *)
    assert (Hk0 : real_le real_zero kappa).
    { apply (RealSetoid.real_lt_le_iff_req real_zero kappa). left. exact Hk1. }
    assert (Hk1le : real_le kappa real_one).
    { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left. exact Hk2. }
    assert (Hbern : real_le
              (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
              real_one)
      by exact (mix2_bernoulli kappa (Datatypes.S N') Hk0 Hk1 Hk1le Hk2).
    assert (HPk : real_lt real_zero (tv_rpow kappa (Datatypes.S N')))
      by exact (mix_rpow_pos kappa (Datatypes.S N') Hk1).
    assert (Hstep2 : real_lt (real_mult TV0 (tv_rpow kappa (Datatypes.S N')))
                       (real_mult (real_mult budget boost)
                                  (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_lt_compat TV0 (real_mult budget boost)
                  (tv_rpow kappa (Datatypes.S N')) Hbud HPk).
    assert (E1 : real_eq (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                         (real_mult TV0 (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_comm _ _).
    assert (Hlt1 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_eq_lt_lt _ _ _ E1 Hstep2).
    assert (E2 : real_eq (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N')))
                       (real_mult budget
                          (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_eq_trans _ _ _
                  (mix2_swap_ring budget boost
                     (tv_rpow kappa (Datatypes.S N')))
                  (real_eq_sym _ _
                     (real_mult_assoc budget
                        (tv_rpow kappa (Datatypes.S N')) boost))).
    assert (Hlt2 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult budget
                        (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_lt_eq_lt _ _ _ Hlt1 E2).
    assert (Hbern' : real_le (real_mult budget
                                (real_mult (tv_rpow kappa (Datatypes.S N')) boost))
                       (real_mult budget real_one)).
    { apply (real_le_trans _
               (real_mult (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                          budget)).
      - apply (RealSetoid.real_eq_le).
        exact (real_mult_comm budget
                 (real_mult (tv_rpow kappa (Datatypes.S N')) boost)).
      - apply (real_le_trans _ (real_mult real_one budget)).
        + exact (real_le_mult_compat
                   (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                   real_one budget Hbudget Hbern).
        + apply (RealSetoid.real_eq_le).
          exact (real_mult_comm real_one budget). }
    assert (E3 : real_eq (real_mult budget real_one) budget)
      by exact (real_eq_trans _ _ _
                  (real_mult_comm budget real_one) (mix_mult_one_l budget)).
    exact (real_lt_le_trans _ _ _
             Hlt2
             (real_le_trans _
                (real_mult budget real_one)
                budget
                Hbern'
                (RealSetoid.real_eq_le _ _ E3))).
Defined.

Lemma mix2_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  exact (real_eq_trans (real_mult real_one x) (real_mult x real_one) x
           (real_mult_comm real_one x) (real_mult_one x)).
Qed.

(* TV0 非负放宽形（同 master 口径） *)
Theorem mix2_k_select : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold real_le in Ha.
  destruct Ha as [Ha | Haq].
  - exact (mix2_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
  - exists 0%nat.
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                 real_one TV0 (real_eq_refl real_one) (real_eq_refl TV0)).
      * exact (real_eq_trans (real_mult real_one TV0) TV0 real_zero
                 (mix_mult_one_l TV0) (real_eq_sym _ _ Haq)).
    + exact Hbudget.
Defined.

(* ============ G4 审计口（全 Closed 预期） ============================ *)
Print Assumptions mix2_swap_ring.
Print Assumptions mix2_step_ring.
Print Assumptions mix2_bernoulli.
Print Assumptions mix2_budget_at.
Print Assumptions mix2_pow_budget.
Print Assumptions mix2_k_select.
(* ================= §2 mrx_arch_n 族 ================= *)
From Stdlib Require Import QArith.Qring.

Local Open Scope Q_scope.

(* Part 0：计算面（纯计算，提取后即 OCaml 侧 nat 函数）                    *)

(* Archimedean 见证 nat 面投影：real_arch 外层 sigT 第一分量。 *)
Definition mrx_arch_n (x : Real) : nat := projT1 (real_arch x).

(* k 计算器：与源文件 mix_pow_budget 同一 arch 锚站（保守上界口径）。
   N = 0 支不可达（real_arch 保 N ≥ 2），值面取 1 仅作全定义性占位，
   证明面 mrx_k_spec 中以 Hge2 排除。 *)
Definition mrx_k_compute (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget) : nat :=
  match mrx_arch_n (real_mult TV0
           (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
              (real_mult_pos_compat (real_minus_r real_one kappa) budget
                 (tv_omd_pos_of_lt kappa hk2) hb))) with
  | Datatypes.O => 1%nat
  | Datatypes.S m => Datatypes.S m
  end.

(* 非负 TV0 放宽形的 k 计算器（对齐源文件 mix_k_select 的 Or 逐支）：      *)
(*   左支（0 < TV0）走严格支计算器；右支（TV0 == 0）k := 0 一发闭合。     *)
Definition mrx_k_select_compute (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget) : nat :=
  match ha with
  | inl hlt => mrx_k_compute kappa TV0 budget hk1 hk2 hlt hb
  | inr _heq => 0%nat
  end.

(* Part 1：证明面（Qed 封闭；体承 mix2_pow_budget 已验证惰性化形）          *)

Lemma mrx_k_spec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa
            (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)) TV0) budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold mrx_k_compute, mrx_arch_n.
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                (real_mult_pos_compat (real_minus_r real_one kappa) budget
                   (tv_omd_pos_of_lt kappa Hk2) Hbudget)))) as [N [Hge2 HN]].
  cbn [projT1].
  destruct N as [| N'].
  - exfalso. exact (Nat.nle_succ_0 1 Hge2).
  - (* ---- 以下承 mix2_pow_budget 主链（κ 形 Bernoulli + 常量桥尾） ---- *)
    (* 证书统一面：real_inv_pos 证书 proof-relevant，全链只准使用同一
       证书应用——把 HN 内拼出的证书应用 remember 为唯一变量 Hwb。 *)
    set (w := real_minus_r real_one kappa) in *.
    set (wb := real_mult w budget) in *.
    remember (real_mult_pos_compat w budget
                (tv_omd_pos_of_lt kappa Hk2) Hbudget) as Hwb eqn:EHwb.
    set (Ms := mix_scale (Datatypes.S N') w) in *.
    set (boost := real_plus real_one Ms) in *.
    set (mR := real_const (Z.of_nat (Datatypes.S N') # 1)).
    (* ---- 预算支：TV0 < budget·boost（全 O(N') 数据/常量件） ---- *)
    assert (Hstep : real_lt (real_mult (real_mult TV0
                                   (real_inv_pos wb Hwb)) wb)
                         (real_mult mR wb))
      by exact (real_mult_lt_compat _ _ _ HN Hwb).
    assert (HeqL : real_eq (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                         TV0).
    { apply (real_eq_trans _ (real_mult wb (real_mult TV0 (real_inv_pos wb Hwb)))).
      - exact (real_mult_comm _ _).
      - exact (real_mult_div wb TV0 Hwb). }
    assert (HeqR : real_eq (real_mult mR wb) (real_mult Ms budget)).
    { apply (real_eq_trans _ (mix_scale (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_eq_const (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_mult_distrib (Datatypes.S N') w budget)). }
    assert (Hb0 : real_lt TV0 (real_mult Ms budget)).
    { exact (real_lt_eq_lt TV0 (real_mult mR wb) (real_mult Ms budget)
               (real_eq_lt_lt TV0
                  (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                  (real_mult mR wb) (real_eq_sym _ _ HeqL) Hstep)
               HeqR). }
    assert (HeqBud : real_eq (real_mult budget boost)
                         (real_plus budget (real_mult Ms budget))).
    { apply (real_eq_trans _
               (real_plus (real_mult budget real_one)
                  (real_mult budget Ms))).
      - exact (real_distrib budget real_one Ms).
      - apply (RealSetoid.real_eq_plus_compat (real_mult budget real_one)
                 (real_mult budget Ms) budget (real_mult Ms budget)
                 (real_mult_one budget) (real_mult_comm budget Ms)). }
    assert (Hbud : real_lt TV0 (real_mult budget boost)).
    { apply (real_lt_eq_lt TV0 (real_plus (real_mult Ms budget) budget)
               (real_mult budget boost)).
      - exact (real_lt_le_trans TV0 (real_mult Ms budget)
                 (real_plus (real_mult Ms budget) budget) Hb0
                 (igr_le_plus_r (real_mult Ms budget) budget Hbudget)).
      - exact (real_eq_trans (real_plus (real_mult Ms budget) budget)
                 (real_plus budget (real_mult Ms budget))
                 (real_mult budget boost)
                 (real_plus_comm (real_mult Ms budget) budget)
                 (real_eq_sym _ _ HeqBud)). }
    (* ---- 主链（κ 形 Bernoulli + 常量桥尾，零幂传递零 compat 幂炸） ---- *)
    assert (Hk0 : real_le real_zero kappa).
    { apply (RealSetoid.real_lt_le_iff_req real_zero kappa). left.
      exact Hk1. }
    assert (Hk1le : real_le kappa real_one).
    { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left.
      exact Hk2. }
    assert (Hbern : real_le
              (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
              real_one)
      by exact (mix2_bernoulli kappa (Datatypes.S N') Hk0 Hk1 Hk1le Hk2).
    assert (HPk : real_lt real_zero (tv_rpow kappa (Datatypes.S N')))
      by exact (mix_rpow_pos kappa (Datatypes.S N') Hk1).
    assert (Hstep2 : real_lt (real_mult TV0 (tv_rpow kappa (Datatypes.S N')))
                       (real_mult (real_mult budget boost)
                                  (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_lt_compat TV0 (real_mult budget boost)
                  (tv_rpow kappa (Datatypes.S N')) Hbud HPk).
    assert (E1 : real_eq (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                         (real_mult TV0 (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_comm _ _).
    assert (Hlt1 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_eq_lt_lt _ _ _ E1 Hstep2).
    assert (E2 : real_eq (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N')))
                       (real_mult budget
                          (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_eq_trans _ _ _
                  (mix2_swap_ring budget boost
                     (tv_rpow kappa (Datatypes.S N')))
                  (real_eq_sym _ _
                     (real_mult_assoc budget
                        (tv_rpow kappa (Datatypes.S N')) boost))).
    assert (Hlt2 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult budget
                        (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_lt_eq_lt _ _ _ Hlt1 E2).
    assert (Hbern' : real_le (real_mult budget
                                (real_mult (tv_rpow kappa (Datatypes.S N')) boost))
                       (real_mult budget real_one)).
    { apply (real_le_trans _
               (real_mult (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                          budget)).
      - apply (RealSetoid.real_eq_le).
        exact (real_mult_comm budget
                 (real_mult (tv_rpow kappa (Datatypes.S N')) boost)).
      - apply (real_le_trans _ (real_mult real_one budget)).
        + exact (real_le_mult_compat
                   (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                   real_one budget Hbudget Hbern).
        + apply (RealSetoid.real_eq_le).
          exact (real_mult_comm real_one budget). }
    assert (E3 : real_eq (real_mult budget real_one) budget)
      by exact (real_eq_trans _ _ _
                  (real_mult_comm budget real_one) (mix_mult_one_l budget)).
    exact (real_lt_le_trans _ _ _
             Hlt2
             (real_le_trans _
                (real_mult budget real_one)
                budget
                Hbern'
                (RealSetoid.real_eq_le _ _ E3))).
Qed.

(* 非负 TV0 放宽形的证明面（对齐源文件 mix_k_select 的 Or 逐支） *)
Lemma mrx_k_select_spec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa
            (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)) TV0) budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold mrx_k_select_compute. destruct Ha as [Hlt | Heq].
  - exact (mrx_k_spec kappa TV0 budget Hk1 Hk2 Hlt Hbudget).
  - (* TV0 == 0 支：k := 0 一发闭合（承源文件同构） *)
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                 real_one TV0 (real_eq_refl real_one) (real_eq_refl TV0)).
      * exact (real_eq_trans (real_mult real_one TV0) TV0 real_zero
                 (mix_mult_one_l TV0) (real_eq_sym _ _ Heq)).
    + exact Hbudget.
Qed.

(* Part 2：封装面（sigT 组装；计算面与证明面在 existT 下并置）              *)

Definition mrx_k_exec (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)
           (mrx_k_spec kappa TV0 budget hk1 hk2 ha hb).

Definition mrx_k_select_exec (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)
           (mrx_k_select_spec kappa TV0 budget hk1 hk2 ha hb).

(*   决定，与第二分量（Qed 封闭的证明面）无关——证明不透明不传染见证。      *)
Lemma mrx_projT1_exec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget),
  projT1 (mrx_k_exec kappa TV0 budget hk1 hk2 ha hb)
  = mrx_k_compute kappa TV0 budget hk1 hk2 ha hb.
Proof. intros.
  exact (@eq_refl nat (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)). Qed.

Lemma mrx_projT1_select_exec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget),
  projT1 (mrx_k_select_exec kappa TV0 budget hk1 hk2 ha hb)
  = mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb.
Proof. intros.
  exact (@eq_refl nat (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)). Qed.

(* 审计口（全 Closed 预期）                                              *)

Print Assumptions mrx_k_compute.
Print Assumptions mrx_k_spec.
Print Assumptions mrx_k_select_spec.
Print Assumptions mrx_k_exec.
Print Assumptions mrx_k_select_exec.
Print Assumptions mrx_projT1_exec.
Print Assumptions mrx_projT1_select_exec.
