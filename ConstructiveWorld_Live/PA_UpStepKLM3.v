(* ==========================================================================)
   PA_UpStepKLM3.v — 策略链 KL 一步收缩与几何衰减
   使命: m3_states/m3_kl_list（KL 列表化）、m3_kappa（κ = 1−η）幂族与 m3_kappa_pos/m3_le_kappa_mul、real_iter_kl_step/real_iter_kl_geom/real_iter_step_geom_eps（一步 KL 收缩与几何-ε 衰减）与 real_interp_Z 正性桥。
   依赖: CW_ConstructiveWorld_219；Stdlib List、QArith
   对标: 策略迭代的 KL 信任域收缩（η-步长下单调几何衰减，TRPO 型论证的实数层化）。
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
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== M3.0 基础定义 ========== *)

(* 离散状态表：n 个状态 [0;1;...;n-1]（list 离散状态世界） *)
Definition m3_states (n : nat) : list nat := seq 0 n.

(* KL 的 list 版：逐项 real_kl_term 折叠求和 *)
Definition m3_kl_list (n : nat) (f g : nat -> Real)
    (Hf : forall i : nat, real_lt real_zero (f i))
    (Hg : forall i : nat, real_lt real_zero (g i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (f i) (g i) (Hf i) (Hg i))
    (m3_states n).

(* 几何率底 κ := 1−η *)
Definition m3_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* κ 的 t 次幂（nat 重复乘）※ S 遮蔽 Datatypes.S，须限定名 *)
Fixpoint m3_rpow (a : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S t' => real_mult a (m3_rpow a t')
  end.

(* t·x（nat 重复加；逐步误差 eps 的 t 步累积） *)
Fixpoint m3_nmul (k : nat) (x : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S k' => real_plus x (m3_nmul k' x)
  end.

(* 1+1 > 0（对半预算的分母） *)
Lemma m3_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)           (real_plus real_one real_one)           (real_eq_sym (real_plus real_zero real_zero) real_zero              kl_zero_plus_zero)           (real_lt_plus_compat real_zero real_one real_zero real_one              real_lt_zero_one real_lt_zero_one)).
Qed.

(* eps 对半：d := eps·inv(1+1)（M3.1 的双 eps 预算合一） *)
Definition m3_half (eps : Real) : Real :=
  real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos).

Lemma m3_half_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (m3_half eps).
Proof.
  intros eps Heps.
  unfold m3_half.
  exact (real_mult_positive eps           (real_inv_pos (real_plus real_one real_one) m3_two_pos)           Heps           (real_inv_pos_pos (real_plus real_one real_one) m3_two_pos)).
Qed.

Lemma m3_half_double_eq : forall eps : Real,
  real_eq (real_plus (m3_half eps) (m3_half eps)) eps.
Proof.
  intros eps. unfold m3_half.
  set (dd := real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos)).
  set (two := real_plus real_one real_one).
  apply (real_eq_trans (real_plus dd dd) (real_mult two dd)).
  - exact (real_eq_trans (real_plus dd dd)
             (real_plus (real_mult real_one dd) (real_mult real_one dd))
             (real_mult two dd)
             (RealSetoid.real_eq_plus_compat dd dd
                (real_mult real_one dd) (real_mult real_one dd)
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd))
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd)))
             (kl_sum_prod_r real_one real_one dd)).
  - exact (real_eq_trans (real_mult two dd)
             (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
             eps
             (kl_swap3 two eps (real_inv_pos two m3_two_pos))
             (real_eq_trans
                (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
                (real_mult eps real_one)
                eps
                (RealSetoid.real_eq_mult_compat eps
                   (real_mult two (real_inv_pos two m3_two_pos)) eps real_one
                   (real_eq_refl eps)
                   (real_inv_pos_correct two m3_two_pos))
                (real_mult_one eps))).
Qed.

(* ========== 环 / 序辅助 ========== *)

(* η + (1−η) == 1 *)
Lemma m3_ring_eta_kappa : forall eta : Real,
  real_eq (real_plus eta (m3_kappa eta)) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. unfold m3_kappa.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* η < 1 ⟹ 0 < 1−η *)
Lemma m3_kappa_pos : forall eta : Real,
  real_lt eta real_one -> real_lt real_zero (m3_kappa eta).
Proof.
  intros eta Hlt.
  unfold m3_kappa.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < η ⟹ 1−η ≤ 1 *)
Lemma m3_kappa_le_one : forall eta : Real,
  real_lt real_zero eta -> real_le (m3_kappa eta) real_one.
Proof.
  intros eta Hpos. unfold m3_kappa. apply kl_lt_le_bridge.
  set (X := real_plus real_one (real_opp eta)).
  assert (Hstep1 : real_lt (real_plus real_zero X) (real_plus eta X))
    by exact (real_lt_plus_compat_lt_le real_zero eta X X Hpos (real_le_refl X)).
  assert (Hstep2 : real_lt (real_plus real_zero X) real_one)
    by exact (real_lt_eq_lt (real_plus real_zero X) (real_plus eta X) real_one
                Hstep1 (m3_ring_eta_kappa eta)).
  exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus real_zero X) real_one
           (real_eq_trans (real_plus real_one (real_opp eta)) X (real_plus real_zero X)
              (real_eq_refl X)
              (real_eq_sym (real_plus real_zero X) X (kl_plus_zero_l X)))
           Hstep2).
Qed.

(* κ ≤ 1、0 ≤ y ⟹ κ·y ≤ y *)
Lemma m3_le_kappa_mul : forall kappa y : Real,
  real_le real_zero y -> real_le kappa real_one ->
  real_le (real_mult kappa y) y.
Proof.
  intros kappa y Hy0 Hk1.
  apply (kl_le_eq_r (real_mult kappa y) (real_mult real_one y) y).
  - exact (real_le_mult_compat_weak kappa real_one y Hy0 Hk1).
  - apply kl_mult_one_l.
Qed.

(* 0 ≤ c、a ≤ b ⟹ c·a ≤ c·b（左乘版） *)
Lemma m3_le_mult_compat_l : forall c a b : Real,
  real_le real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc Hab.
  apply (kl_le_eq_r (real_mult c a) (real_mult b c) (real_mult c b)).
  - apply (kl_le_eq_l (real_mult a c) (real_mult b c) (real_mult c a)).
    + exact (real_le_mult_compat_weak a b c Hc Hab).
    + apply real_mult_comm.
  - apply real_mult_comm.
Qed.

(* 环：a·(b+c) == a·b + a·c *)
Lemma m3_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环：a·(b·c) == (a·b)·c *)
Lemma m3_ring_reassoc2 : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < x ⟹ 0 ≤ t·x *)
Lemma m3_nmul_nonneg : forall (k : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (m3_nmul k x).
Proof.
  intros k x Hx. induction k as [| k IH].
  - apply real_le_refl.
  - exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus x (m3_nmul k x)) real_zero
             (real_le_plus_compat real_zero x real_zero (m3_nmul k x)
                (kl_lt_le_bridge real_zero x Hx) IH)
             kl_zero_plus_zero).
Qed.

(* n ≠ 0 ⟹ 状态表非空 *)
Lemma m3_seq_nonnil : forall n : nat, n <> 0 -> m3_states n <> nil.
Proof.
  intros n Hn Hnil. unfold m3_states in Hnil.
  destruct n as [| m].
  - exact (Hn eq_refl).
  - simpl in Hnil. discriminate Hnil.
Qed.

(* 逐项正项的 list 和为正（配分函数正性核） *)
Lemma m3_interp_Z_pos2 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k e : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero
    (real_list_sum nat
       (fun i : nat => real_mult
          (real_pow_pos (q i) k (Hq i)) (real_pow_pos (r i) e (Hr i)))
       (m3_states n)).
Proof.
  intros n Hn q r k e Hq Hr.
  apply (real_list_sum_pos nat).
  - intro i.
    exact (real_mult_positive (real_pow_pos (q i) k (Hq i))
             (real_pow_pos (r i) e (Hr i))
             (cauchy_real_exp_pos (real_mult k (cw_log (q i) (Hq i))))
             (cauchy_real_exp_pos (real_mult e (cw_log (r i) (Hr i))))).
  - exact (m3_seq_nonnil n Hn).
Qed.

(* 同上，结论取 real_interp_Z 原生形态（供 pkg 的 sigT 组件直接对型） *)
Lemma m3_interp_Z_pos3 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n q r k Hq Hr).
Proof.
  intros n Hn q r k Hq Hr.
  exact (m3_interp_Z_pos2 n Hn q r (real_plus real_one (real_opp k)) k Hq Hr).
Qed.

(* 单步更新逐点正性：π'(i) := (r(i)^{1−k}·p(i)^k)·inv Z > 0 *)
Definition m3_step_pos_pt (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp))
    (i : nat)
  : real_lt real_zero (real_step_next n r p k Hr Hp HZ i) :=
  real_mult_positive
    (real_mult (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
               (real_pow_pos (p i) k (Hp i)))
    (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
    (real_mult_positive
       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
       (real_pow_pos (p i) k (Hp i))
       (cauchy_real_exp_pos
          (real_mult (real_plus real_one (real_opp k)) (cw_log (r i) (Hr i))))
       (cauchy_real_exp_pos (real_mult k (cw_log (p i) (Hp i)))))
    (real_inv_pos_pos (real_interp_Z n r p k Hr Hp) HZ).

(* 单步更新归一化：Σ π' == inv Z·Z == 1（配分函数吸收） *)
Lemma m3_step_next_norm : forall (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp)),
  real_eq
    (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
    real_one.
Proof.
  intros n r p k Hr Hp HZ.
  exact (real_eq_trans           (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))           (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                      (real_list_sum nat                         (fun i : nat => real_mult                            (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                            (real_pow_pos (p i) k (Hp i)))                         (m3_states n)))           real_one           (real_list_sum_linear_r nat              (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)              (fun i : nat => real_mult                 (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                 (real_pow_pos (p i) k (Hp i)))              (m3_states n))           (real_eq_trans              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_list_sum nat                            (fun i : nat => real_mult                               (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                               (real_pow_pos (p i) k (Hp i)))                            (m3_states n)))              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_interp_Z n r p k Hr Hp))              real_one              (RealSetoid.real_eq_mult_compat                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_list_sum nat                    (fun i : nat => real_mult                       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                       (real_pow_pos (p i) k (Hp i)))                    (m3_states n))                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_interp_Z n r p k Hr Hp)                 (real_eq_refl (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 (real_eq_refl (real_interp_Z n r p k Hr Hp)))              (real_eq_trans                 (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                            (real_interp_Z n r p k Hr Hp))                 (real_mult (real_interp_Z n r p k Hr Hp)                            (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 real_one                 (real_mult_comm (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                                 (real_interp_Z n r p k Hr Hp))                 (real_inv_pos_correct (real_interp_Z n r p k Hr Hp) HZ)))).
Qed.

(* ========== 策略迭代序列（sigT 封装：策略+正性+配分函数正性+归一化） ========== *)

(* 迭代包类型：p := π_t 连同其逐点正性、下一步配分函数正性、归一化恒等 *)
Definition m3_pkg_type (n : nat) (r : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) : Type :=
  { p : nat -> Real &
    { Hp : forall i : nat, real_lt real_zero (p i) &
      { HZ : real_lt real_zero (real_interp_Z n r p (m3_kappa eta) Hr Hp) &
        real_eq (real_list_sum nat p (m3_states n)) real_one } } }.

(* π_{t+1}(i) := real_step_next n r π_t (1−η)：几何插值策略更新
   π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z_t。
   单 Fixpoint（对 t 结构递归），O 情形携带初值四元组，
   S 情形经 m3_step_pos_pt / m3_interp_Z_pos2 / m3_step_next_norm
   同步重建四元组。 *)
Fixpoint m3_pi_pkg (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) {struct t} : m3_pkg_type n r eta Hr :=
  match t with
  | Datatypes.O => existT _ p0 (existT _ Hp0 (existT _ HZ1 Hnorm0))
  | Datatypes.S t' =>
      let pkg := m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t' in
      let p := projT1 pkg in
      let Hp := projT1 (projT2 pkg) in
      let HZ := projT1 (projT2 (projT2 pkg)) in
      (existT _ (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
         (existT _ (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)
           (existT
              (fun HZ' : real_lt real_zero
                          (real_interp_Z n r
                             (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                             (m3_kappa eta) Hr
                             (fun i : nat =>
                                m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)) =>
                 real_eq
                   (real_list_sum nat
                      (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                      (m3_states n))
                   real_one)
              (m3_interp_Z_pos3 n Hn r
                 (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                 (m3_kappa eta) Hr
                 (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i))
              (m3_step_next_norm n r p (m3_kappa eta) Hr Hp HZ)))
       : m3_pkg_type n r eta Hr)
  end.

(* 四投影：迭代策略序列 / 逐点正性 / 配分函数正性 / 归一化 *)
Definition m3_pi_seq (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) : nat -> Real :=
  projT1 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t).

Definition m3_pi_seq_pos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  forall i : nat,
    real_lt real_zero (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t i) :=
  fun i : nat => projT1 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) i.

Definition m3_pi_seq_Zpos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_lt real_zero
    (real_interp_Z n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
       (m3_kappa eta) Hr (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) :=
  projT1 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

Definition m3_pi_seq_norm (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_eq
    (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) (m3_states n))
    real_one :=
  projT2 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

(* ========== M3.1 前置：M2 换向单步几何收缩（eps 化 geom_step） ========== *)

(* 单步真几何率（根内 policy_iter_kl_geom_step 的 eps 化副本）：
   KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + eps。
   即 UpStepKL 的 M2（real_step_kl_eta_bound_eps）在迭代序列第 t 步的
   直接实例化：p-槽 := r（π*），r-槽 := π_t，eta-槽 := κ := 1−η。 *)
Corollary real_iter_step_geom_eps :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       eps).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  exact (real_step_kl_eta_bound_eps n r           (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_kappa eta) Hr           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           Hnormr (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))           (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)           eps Heps).
Qed.

(* ========== M3.1：单步向后 KL 递推（backward_kl_step_le 的 eps 化副本） ========== *)
(* KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1}) + eps
   路线（对应根内 policy_iter_backward_kl_step_le 的「丢弃负项」）：
   M2 换向实例给 KL(π*‖π_{t+1}) ≤ (1−η)KL(π*‖π_t) + d（d := eps/2），
   Gibbs 下界给 0 ≤ KL(π_t‖π_{t+1}) + d，两式相加后对半预算吸收 eps。 *)
Theorem real_iter_kl_step :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       (real_plus
          (m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
          eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  assert (HnormP : forall s : nat,
            real_eq
              (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 s)
                 (m3_states n))
              real_one)
    by exact (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0).
  set (A := real_mult (m3_kappa eta)
              (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                 (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).
  set (B := m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))).
  set (d := m3_half eps).
  apply (real_le_trans
           (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
           (real_plus (real_plus A d) (real_plus B d))
           (real_plus A (real_plus B eps))).
  - apply (real_le_trans
             (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
                (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
             (real_plus A d)
             (real_plus (real_plus A d) (real_plus B d))).
    + (* M2 换向实例：KL(π*‖π_{t+1}) ≤ κ·KL(π*‖π_t) + d *)
      exact (real_step_kl_eta_bound_eps n r
               (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_kappa eta) Hr
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               Hnormr (HnormP t)
               (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
               (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
               d (m3_half_pos eps Heps)).
    + (* (A+d) ≤ (A+d) + (B+d)：Gibbs 下界 0 ≤ B + d *)
      exact (kl_le_eq_l (real_plus (real_plus A d) real_zero)
               (real_plus (real_plus A d) (real_plus B d))
               (real_plus A d)
               (real_le_plus_compat (real_plus A d) (real_plus A d)
                  real_zero (real_plus B d)
                  (real_le_refl (real_plus A d))
                  (real_gibbs_inequality_eps nat (m3_states n)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (HnormP t) (HnormP (Datatypes.S t)) d (m3_half_pos eps Heps)))
               (real_plus_zero (real_plus A d))).
  - (* eq 换形：(A+d)+(B+d) == A+(B+eps) *)
    exact (kl_eq_le_bridge (real_plus (real_plus A d) (real_plus B d))
             (real_plus A (real_plus B eps))
             (real_eq_trans (real_plus (real_plus A d) (real_plus B d))
             (real_plus (real_plus A B) (real_plus d d))
             (real_plus A (real_plus B eps))
             (real_plus_swap_mid A d B d)
             (real_eq_trans (real_plus (real_plus A B) (real_plus d d))
                (real_plus (real_plus A B) eps)
                (real_plus A (real_plus B eps))
                (RealSetoid.real_eq_plus_compat (real_plus A B) (real_plus d d)
                   (real_plus A B) eps
                   (real_eq_refl (real_plus A B))
                   (m3_half_double_eq eps))
                (real_eq_sym (real_plus A (real_plus B eps))
                   (real_plus (real_plus A B) eps)
                   (real_plus_assoc A B eps))))).
Qed.

(* ========== M3.2：真几何率迭代（geom_iter 的 eps 化副本） ========== *)
(* KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps
   （根内 policy_iter_kl_geom_iter 的 eps 化副本：单步收缩
     real_iter_step_geom_eps 对 t 归纳，误差按 t 步算术累积。） *)
Theorem real_iter_kl_geom :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))
    (real_plus
       (real_mult (m3_rpow (m3_kappa eta) t)
          (m3_kl_list n r p0 Hr Hp0))
       (m3_nmul t eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1
         t eps Heps.
  induction t as [| t IH].
  - (* t = 0：κ^0 == 1、0·eps == 0，KL ≤ 1·KL + 0 == KL *)
    cbn [m3_rpow m3_nmul].
    apply kl_eq_le_bridge.
    apply (real_eq_sym
             (real_plus
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero)
             (m3_kl_list n r p0 Hr Hp0)).
    exact (real_eq_trans
             (real_plus (real_mult real_one (m3_kl_list n r p0 Hr Hp0))
                        real_zero)
             (real_plus (m3_kl_list n r p0 Hr Hp0) real_zero)
             (m3_kl_list n r p0 Hr Hp0)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero
                (m3_kl_list n r p0 Hr Hp0) real_zero
                (kl_mult_one_l (m3_kl_list n r p0 Hr Hp0))
                (real_eq_refl real_zero))
             (real_plus_zero (m3_kl_list n r p0 Hr Hp0))).
  - (* t = S t：单步收缩 + IH 单调放大 + κ 系数重排 + 误差累积 *)
    cbn [m3_rpow m3_nmul].
    pose proof (real_iter_step_geom_eps n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                  Hnormr Heta_pos Heta_lt1 t eps Heps) as Hstep.
    set (KL0 := m3_kl_list n r p0 Hr Hp0).
    set (KLt := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)).
    set (KLs := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                  Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                     (Datatypes.S t))).
    set (Y := m3_nmul t eps).
    set (X := real_mult (m3_rpow (m3_kappa eta) t) KL0).
    (* κ·单调：0 ≤ κ、IH ⟹ κ·KL_t ≤ κ·(κ^t·KL0 + t·eps) *)
    assert (Hmono : real_le (real_mult (m3_kappa eta) KLt)
                            (real_mult (m3_kappa eta) (real_plus X Y))).
    { apply (m3_le_mult_compat_l (m3_kappa eta)).
      - exact (kl_lt_le_bridge real_zero (m3_kappa eta)
                 (m3_kappa_pos eta Heta_lt1)).
      - exact IH. }
    (* 单步链：KL_{t+1} ≤ κ·KL_t + eps ≤ κ·(κ^t·KL0 + Y) + eps *)
    assert (Hchain : real_le KLs
                       (real_plus (real_mult (m3_kappa eta) (real_plus X Y))
                          eps)).
    { apply (real_le_trans KLs (real_plus (real_mult (m3_kappa eta) KLt) eps)).
      - exact Hstep.
      - exact (real_le_plus_compat (real_mult (m3_kappa eta) KLt)
                  (real_mult (m3_kappa eta) (real_plus X Y)) eps eps
                  Hmono (real_le_refl eps)). }
    (* 终组装：κ·(X+Y)+eps ≤ (κ·κ^t)·KL0 + (Y+eps)（κ·Y ≤ Y） *)
    apply (real_le_trans KLs
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps))
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus eps Y))).
    + apply (kl_le_eq_r _ (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)).
      * exact Hchain.
      * exact (real_eq_trans
                 (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)
                 (real_plus (real_plus (real_mult (m3_kappa eta) X)
                              (real_mult (m3_kappa eta) Y)) eps)
                 (real_plus
                    (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                       KL0)
                    (real_plus (real_mult (m3_kappa eta) Y) eps))
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (m3_kappa eta) (real_plus X Y))
                    eps
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_mult (m3_kappa eta) Y))
                    eps
                    (m3_distrib_l (m3_kappa eta) X Y)
                    (real_eq_refl eps))
                 (real_eq_trans
                    (real_plus
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y)) eps)
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_plus
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_eq_sym
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_plus (real_mult (m3_kappa eta) Y) eps))
                       (real_plus
                          (real_plus (real_mult (m3_kappa eta) X)
                             (real_mult (m3_kappa eta) Y)) eps)
                       (real_plus_assoc (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y) eps))
                    (RealSetoid.real_eq_plus_compat
                       (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (m3_ring_reassoc2 (m3_kappa eta) (m3_rpow (m3_kappa eta) t) KL0)
                       (real_eq_refl (real_plus (real_mult (m3_kappa eta) Y) eps))))).
    + exact (real_le_plus_compat
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps)
                (real_plus eps Y)
                (real_le_refl
                   (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0))
                (kl_le_eq_r
                   (real_plus (real_mult (m3_kappa eta) Y) eps)
                   (real_plus Y eps)
                   (real_plus eps Y)
                   (real_le_plus_compat (real_mult (m3_kappa eta) Y) Y eps eps
                      (m3_le_kappa_mul (m3_kappa eta) Y
                         (m3_nmul_nonneg t eps Heps)
                         (m3_kappa_le_one eta Heta_pos))
                      (real_le_refl eps))
                   (real_plus_comm Y eps))).
Qed.

Print Assumptions real_iter_step_geom_eps.
Print Assumptions m3_step_next_norm.
Print Assumptions m3_interp_Z_pos3.
Print Assumptions m3_kappa_pos.
Print Assumptions m3_half_pos.
Print Assumptions m3_two_pos.
