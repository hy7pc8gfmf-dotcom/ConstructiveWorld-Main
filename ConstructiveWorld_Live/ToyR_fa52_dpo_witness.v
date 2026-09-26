(* ==========================================================================)
   ToyR_fa52_dpo_witness.v — DpoPairMain 节八项前提槽的显式见证件
   使命: S:=bool、reward 分档常值、beta:=1、pi_ref:=恒 1、Z_align:=1 的全显式见证；三处正性槽由 real_lt_zero_one 兑现；两件见证下闭合的全参特化定理（fa52_dpo_bounded_both_concrete 等）。
   依赖: S02_CauchyComplete、S07_RealSetoidExpLog、S08_RealMainlineDPO。
   对标: DPO 目标函数的有限状态实例化（强化学习对偶策略优化的极小模型）。
   构造性: 零承认词面；全显式见证构造、零剩余前提；非平凡（前提实例化与出节定理全参特化）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ---------- 具体见证 ---------- *)
Definition fa52_dpo_S : Type := bool.
Definition fa52_dpo_reward : bool -> Real :=
  fun s : bool => if s then real_plus real_one real_one else real_one.
Definition fa52_dpo_pi_ref : bool -> Real := fun _ : bool => real_one.
Definition fa52_dpo_pi_ref_pos : forall s : bool, real_lt real_zero (fa52_dpo_pi_ref s) :=
  fun _ : bool => real_lt_zero_one.

(* ---------- 1 < 2（0<1 复合 + 代数归位） ---------- *)
Lemma fa52_one_two_lt : real_lt real_one (real_plus real_one real_one).
Proof.
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus real_one real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
             real_lt_zero_one (real_le_refl real_one)). }
  exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) Hstep).
Qed.

Lemma fa52_dpo_reward_spread :
  real_lt (fa52_dpo_reward false) (fa52_dpo_reward true).
Proof.
  unfold fa52_dpo_reward.
  simpl.
  exact fa52_one_two_lt.
Qed.

(* ---------- 主件一：DPO 损失在 π* 处 (0, ln2) 有界——见证特化闭语句 ---------- *)
Theorem fa52_dpo_bounded_both_concrete :
  S01_BaseRing.And
    (real_lt real_zero
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false))
    (real_lt
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false)
       (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  exact (real_dpo_loss_pi_star_bounded_both bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one true false fa52_dpo_reward_spread).
Qed.

(* ---------- 主件二：闭式奖励复原——见证特化（β:=1, Z:=1 分离出 log1 修正项） ---------- *)
Theorem fa52_dpo_reward_recovery_concrete : forall s : bool,
  real_eq
    (real_dpo_reward_explicit bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
       (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref real_one real_lt_zero_one)
       (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
       s)
    (real_plus (fa52_dpo_reward s)
                (real_opp (real_mult real_one
                            (real_log real_one real_lt_zero_one)))).
Proof.
  intro s.
  exact (real_dpo_reward_recovers_up_to_baseline bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one s).
Qed.

Print Assumptions fa52_dpo_bounded_both_concrete.
Print Assumptions fa52_dpo_reward_recovery_concrete.
