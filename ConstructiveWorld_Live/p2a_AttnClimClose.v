(* ==========================================================================)
   p2a_AttnClimClose.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：one_minus_delta_pos_real、one_minus_delta_lt_one_real、r_arch_pow_attn_real、tv_iter_decay_real、attention_iterate_converges_real、p2a_geo_iter_le、p2a_attn_clim_zero、p2a_attn_tv_seq_clim_zero、p2a_attn_clim_budget。
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
Require Import UpBudgetReal.
From Stdlib Require Import Extraction.

(* ================= §1 one_minus_delta_pos_real 族 ================= *)
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ============ 1. 1−δ 的 Real 层序引理（κ := 1−δ 良定前提） ============ *)

(* 根文件 one_minus_kappa_pos 的 Real 层副本：δ < 1 ⟹ 0 < 1−δ *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd.
  exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* 根注意力区前提的对称支 Real 副本：0 < δ ⟹ 1−δ < 1
   （逐点差零 + real_lt_eq_lt：1−(1−δ) == δ 逐点 ring） *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    rewrite (real_plus_proj real_one
               (real_opp (real_plus real_one (real_opp delta))) n).
    rewrite (real_opp_proj (real_plus real_one (real_opp delta)) n).
    rewrite (real_plus_proj real_one (real_opp delta) n).
    rewrite (real_opp_proj delta n).
    cbn [projT1].
    ring.
Qed.

(* ============ 2. 件 1 主件：接口前提的 Real 层实例化 ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd2)           (one_minus_delta_lt_one_real delta Hd1)           a Ha eps Heps).
Qed.

(* ============ 3. 件 2 组装预演：TV 几何衰减链（Real 副本） ============ *)

(* 根文件 attention_tv_iter_contraction 结论的 Real 副本链：
   每步 tv_{n+1} ≤ (1−δ)·tv_n ⟹ tv_n ≤ (1−δ)^n·tv₀。
   （幂反单调的 Real 副本即 UpBudgetReal.real_pow_anti_mono，
     件 2 主定理直接复用，不重证。） *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* κ^0 ≡ one：1·tv₀ == tv₀ *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} ≤ κ·tv_n ≤ κ·(κ^n·tv₀) == κ^{n+1}·tv₀ *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. 件 2 主定理：迭代收敛的 sigT 显式预算见证 ============ *)

(* 根文件 attention_iterate_converges 的 Real 层副本组装：
   预算 N 由件 1（r_arch_pow_attn_real）构造；尾界 n ≥ N 由
   tv 衰减链（本文件件 2 前置）+ 幂反单调（real_pow_anti_mono）
   + 件 1 的 a·κ^N < eps 消解。
   覆盖面注记：tv_seq 即根语义对象 n ↦ TV(iterate attention_step n μ₀,
   boltzmann_dist_attn) 的 Real 承载；每步收缩 Hstep 对应根
   attention_tv_contraction 的结论形态。根抽象 Section 的完整
   Real 层实例化需整体消解 detailed_balance/minorization/
   sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等接口前提，
   工程量大，不属本件范围（主件 1 不受影响）。 *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n Hn).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. 提取检验（G3：零 Obj.magic） ============ *)
(* ================= §2 p2a_geo_iter_le 族 ================= *)
From Stdlib Require Import QArith.QArith.

(* ============ 几何迭代上界：u n ≤ κ^n·u 0 ============ *)

Theorem p2a_geo_iter_le : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  forall n : nat, real_le (u n) (real_mult (real_pow kappa n) (u 0%nat)).
Proof.
  intros u kappa Hk1 Hstep n.
  induction n as [| n IH].
  - apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_one_l.
  - apply (real_le_trans _ (real_mult kappa (u n))).
    + apply Hstep.
    + apply (real_le_trans _
               (real_mult kappa (real_mult (real_pow kappa n) (u 0%nat)))).
      * apply real_le_mult_compat_r.
        -- exact (real_lt_le_bridge real_zero kappa Hk1).
        -- exact IH.
      * apply real_eq_le_bridge. apply real_mult_assoc.
Qed.

(* ============ 引擎：几何收缩序列的 clim 收敛（收敛到零点） ============ *)

Theorem p2a_attn_clim_zero : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  real_lim u real_zero.
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 (u 0%nat) Hu0 (real_const eps)
              (real_const_pos eps Heps)) as [N HN].
  exists N. intros n Hn.
  split.
  - (* 上侧：u n ≤ κ^n·u0 ≤ κ^N·u0 < eps；再重述 0+eps 形 *)
    apply (real_lt_eq_lt (u n) (real_const eps)
             (real_plus real_zero (real_const eps))).
    + apply (real_le_lt_trans (u n)
               (real_mult (real_pow kappa N) (u 0%nat))).
      * apply (real_le_trans _
                 (real_mult (real_pow kappa n) (u 0%nat))).
        -- exact (p2a_geo_iter_le u kappa Hk1 Hstep n).
        -- apply real_le_mult_compat.
           ++ exact Hu0.
           ++ exact (real_pow_anti_mono kappa Hk1
                       (real_lt_le_bridge kappa real_one Hk2) N n Hn).
      * apply (real_eq_lt_lt
                 (real_mult (real_pow kappa N) (u 0%nat))
                 (real_mult (u 0%nat) (real_pow kappa N))).
        -- apply real_mult_comm.
        -- exact HN.
    + apply real_eq_sym.
      apply (real_eq_trans (real_plus real_zero (real_const eps))
                           (real_plus (real_const eps) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
  - (* 下侧：0 − eps < u n（非负性单边供给） *)
    apply (real_lt_le_trans (real_plus real_zero (real_opp (real_const eps))) real_zero).
    + apply (real_eq_lt_lt
               (real_plus real_zero (real_opp (real_const eps)))
               (real_opp (real_const eps)) real_zero).
      * apply (real_eq_trans
                 (real_plus real_zero (real_opp (real_const eps)))
                 (real_plus (real_opp (real_const eps)) real_zero)).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
      * exact (real_lt_zero_opp (real_const eps) (real_const_pos eps Heps)).
    + exact (Hnonneg n).
Qed.

(* ============ 注意力镜面：κ := 1−δ 特化形（论文2 §5.5/§9.4 口） ============ *)
(*   单步收缩前提 Hstep 对位 attention_tv_contraction 的 Real 对偶口         *)
(*   （S06 几何率 (1−δ) 的实例面；UpArchAttn 件2 同款显式前提纪律——          *)
(*   抽象 Section 世界的 TV/iterate 对象整体实例化属天级工程，不属本件）。     *)

Theorem p2a_attn_tv_seq_clim_zero :
  forall (tv_seq : nat -> Real) (delta : Real),
  real_lt real_zero delta -> real_lt delta real_one ->
  (forall n : nat,
     real_le (tv_seq (Datatypes.S n))
             (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  (forall n : nat, real_le real_zero (tv_seq n)) ->
  real_lt real_zero (tv_seq 0%nat) ->
  real_lim tv_seq real_zero.
Proof.
  intros tv_seq delta Hd0 Hd1 Hstep Hnonneg Hu0.
  exact (p2a_attn_clim_zero tv_seq (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd1)           (one_minus_delta_lt_one_real delta Hd0)           Hstep Hnonneg Hu0).
Qed.

(* ============ 预算伴件：clim 的单向 Q-eps 预算形 ============ *)

Theorem p2a_attn_clim_budget : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (u n) (real_plus real_zero (real_const eps))).
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (p2a_attn_clim_zero u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps)
    as [N HN].
  exists N. intros n Hn.
  destruct (HN n Hn) as [Hup _].
  exact Hup.
Qed.

(* ---- 四关备件：PA 口径 + G3 提取检验 ---- *)

Print Assumptions p2a_geo_iter_le.
Print Assumptions p2a_attn_clim_zero.
Print Assumptions p2a_attn_tv_seq_clim_zero.
Print Assumptions p2a_attn_clim_budget.

Set Extraction Output Directory ".".
Extraction "p2a_attnclimclose.ml" p2a_geo_iter_le p2a_attn_clim_budget.
