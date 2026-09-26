(* ==========================================================================)
   ToyR_RateTheoryAblation.v — 收缩率理论的消融件
   使命: rta_delta_le_one_of_minorization（Dobrushin 系数 ≤1）、rta_iter_contraction_wo_le_one（迭代收缩）、rta_strict_branch_real（严格支）与 rta_omd_powb_mono_b（TV 幂单调 ≤_B）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、G07_KLWall、KLWallClosed、UpTVDoeblin；Stdlib List、QArith
   对标: 马尔可夫链 Dobrushin 收缩与几何收敛率（遍历理论的消融面）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpTVDoeblin.

(* ============================================================ *)
(* §1 delta_le_one 前提消去：minorization + 两侧归一 ⟹ δ ≤ 1       *)
(*   （定理 4.1/4.2 接口中 delta_le_one 为冗余前提的第一刀）        *)
(* ============================================================ *)

Theorem rta_delta_le_one_of_minorization :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  (* 逐点 minorization（取 i := nil；K_row/Hmin 对任意 i 成立） *)
  pose proof (HKrow nil) as Hrow0.
  assert (Hpt : forall j : list Real,
           real_le (real_mult delta (u j)) (K nil j))
    by (intro j; apply Hmin).
  (* 逐点和单调：Σ(δ·u) ≤ Σ(K nil) *)
  assert (Hle : real_le
                  (real_list_sum (list Real)
                     (fun j : list Real => real_mult delta (u j)) states)
                  (real_list_sum (list Real) (K nil) states)).
  { exact (@real_list_sum_le (list Real)
             (fun j : list Real => real_mult delta (u j))
             (K nil) states Hpt). }
  (* LHS：Σ(δ·u) == δ·Σu == δ·1 == δ（数乘线性 + setoid 链） *)
  assert (Hlhs : real_eq
                   (real_list_sum (list Real)
                      (fun j : list Real => real_mult delta (u j)) states)
                   delta).
  { apply (real_eq_trans _
             (real_mult delta (real_list_sum (list Real) u states)) _).
    - exact (@real_list_sum_linear (list Real) delta u states).
    - apply (real_eq_trans _ (real_mult delta real_one) _).
      + apply (RealSetoid.real_eq_mult_compat delta
                 (real_list_sum (list Real) u states)
                 delta real_one (real_eq_refl delta) Hunorm).
      + exact (real_mult_one delta). }
  (* 组装：δ ≤ Σ(δ·u) ≤ Σ(K nil) == 1 *)
  apply (real_le_trans delta
           (real_list_sum (list Real)
              (fun j : list Real => real_mult delta (u j)) states)
           real_one).
  - apply (RealSetoid.real_eq_le _ _).
    exact (real_eq_sym _ _ Hlhs).
  - apply (real_le_trans _
             (real_list_sum (list Real) (K nil) states) _).
    + exact Hle.
    + apply (RealSetoid.real_eq_le _ _). exact Hrow0.
Qed.

(* ============================================================ *)
(* §2 定理 4.2 前提减薄实例形：无 delta_le_one（更无 delta_pos/     *)
(*   K_pos/n_pos）的 n 步迭代收缩——δ ≤ 1 由 §1 从 minorization      *)
(*   派生（依存出节后的 tv_doeblin_iter 全参形，接口位序实证坐标    *)
(*   UpTVDoeblin.v L1991）                                        *)
(* ============================================================ *)

Theorem rta_iter_contraction_wo_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  (forall f : list Real -> Real,
     real_le (real_abs (real_list_sum (list Real) f states))
             (real_list_sum (list Real)
                (fun w : list Real => real_abs (f w)) states)) ->
  forall (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin states
             (tv_titer states K n mu) (tv_titer states K n nu))
          (real_mult (tv_rpow (tv_omd delta) n)
                     (tv_doeblin states mu nu)).
Proof.
  intros states K u delta HKrow Hunorm Hmin Labs n mu nu Hmu Hnu.
  apply (tv_doeblin_iter states K HKrow u Hunorm delta           (rta_delta_le_one_of_minorization states K u delta              HKrow Hunorm Hmin)           Hmin Labs n mu nu Hmu Hnu).
Qed.

(* ============================================================ *)
(* §3 定理 4.4 的 Real 载体对应支：0 ≤ η < 1 ⟹ 正性证书 × Bishop    *)
(*   收缩 封装（klc_strict_branch 仅 Q 载体；本件 Real 载体，正性   *)
(*   证书由 real_lt 的平移链构造性取得——tv_omd_pos_of_lt 泛化形）   *)
(* ============================================================ *)

Theorem rta_strict_branch_real : forall (eta : Real) (t t1 : nat),
  real_le real_zero eta -> real_lt eta real_one -> NatLe t t1 ->
  prod (real_lt real_zero (real_plus real_one (real_opp eta)))
       (real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
                  (powb_pow (real_plus real_one (real_opp eta)) t)).
Proof.
  intros eta t t1 H0 Hlt Hle. split.
  - (* 0 < 1−η：η<1 平移 + η+(−η)==0 换形（tv_omd_pos_of_lt 同链） *)
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus eta (real_opp eta))
             (real_plus real_one (real_opp eta))).
    + exact (real_eq_sym (real_plus eta (real_opp eta)) real_zero
               (real_plus_opp eta)).
    + exact (real_lt_plus_compat_lt_le eta real_one (real_opp eta)
               (real_opp eta) Hlt (real_le_refl (real_opp eta))).
  - (* Bishop 收缩：klc_closed_powb_mono 依存 0 ≤ η ≤ 1 *)
    exact (klc_closed_powb_mono eta t t1 H0 (inl Hlt) Hle).
Qed.

(* ============================================================ *)
(* §4 率层桥：tv_rpow（§4.2 率载体，UpTVDoeblin L1552）与           *)
(*   powb_pow（§4.3 率代数载体，G07_KLWall L1025）逐点相等——        *)
(*   两个同构 Fixpoint 的 eq 证（率层 ⟷ 率代数层的接口翻译件）      *)
(* ============================================================ *)

Lemma rta_rpow_powb_eq : forall (a : Real) (n : nat),
  real_eq (tv_rpow a n) (powb_pow a n).
Proof.
  intros a n. induction n as [| n IH].
  - cbn [tv_rpow powb_pow]. apply real_eq_refl.
  - cbn [tv_rpow powb_pow].
    apply (RealSetoid.real_eq_mult_compat a (tv_rpow a n)
             a (powb_pow a n) (real_eq_refl a) IH).
Qed.

(* ============================================================ *)
(* §5 定理 4.3 在 tv_rpow 率层上的消耗形：Doeblin 残差率 (1−δ) 的    *)
(*   幂列 Bishop 单调——经 §4 桥把 klc_closed_powb_mono 运载到       *)
(*   率层（§4.1/4.2 的率代数与 §4.3 的退化端处置就此闭合）          *)
(* ============================================================ *)

Theorem rta_omd_powb_mono_b : forall (delta : Real) (n m : nat),
  real_le real_zero delta -> real_le delta real_one -> NatLe n m ->
  real_le_b (tv_rpow (tv_omd delta) m) (tv_rpow (tv_omd delta) n).
Proof.
  intros delta n m H0 H1 Hle.
  pose proof (klc_closed_powb_mono delta n m H0 H1 Hle) as Hklc.
  unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           (powb_pow (real_plus real_one (real_opp delta)) m)
           (tv_rpow (tv_omd delta) m)
           (real_plus (powb_pow (real_plus real_one (real_opp delta)) n) eps)
           (real_plus (tv_rpow (tv_omd delta) n) eps)).
  - exact (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) m).
  - apply (RealSetoid.real_eq_plus_compat
             (powb_pow (real_plus real_one (real_opp delta)) n) eps
             (tv_rpow (tv_omd delta) n) eps
             (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) n)
             (real_eq_refl eps)).
  - exact (Hklc eps Heps).
Qed.

(* ============================================================ *)
(* 审计口（G4：零公理 Closed；G1 min-pa 审计位）                    *)
(* ============================================================ *)
Print Assumptions rta_delta_le_one_of_minorization.
Print Assumptions rta_iter_contraction_wo_le_one.
Print Assumptions rta_strict_branch_real.
Print Assumptions rta_rpow_powb_eq.
Print Assumptions rta_omd_powb_mono_b.
