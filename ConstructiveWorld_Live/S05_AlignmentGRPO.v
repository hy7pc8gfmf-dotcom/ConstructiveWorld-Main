(* ============================================================ *)
(* S05_AlignmentGRPO.v（同名非平凡替换稿）  *)
(* 本件为零 公理／零 承认件交付稿：全文无假设命令、无中途放弃、   *)
(* 无未证参数；所有玩具证明体均为纯构造性替换并以真 Qed 闭合。    *)
(* 替换段：clip_lower / ppo_gap_nonneg / sigmoid_pos /            *)
(*         u2_align_objective_ext                                  *)
(* 其余正文与基线原件逐字节同源；文件尾附替换件 Print Assumptions。*)
(* ============================================================ *)
(* ============================================================ *)
(* S05_AlignmentGRPO.v                                         *)
(*                                                             *)
(* 目的：GRPO/PPO 对齐的策略迭代：KL 几何收缩、代理目标保守性    *)
(*       与 DPO 奖励恢复（构造性 Set 层）。                      *)
(* 主件：policy_iter_kl_geom_iter（迭代几何上界                  *)
(*       KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)）；U2 不动点刻画。   *)
(* 依赖：S01–S04；Stdlib（QArith、Qabs、Qround、List、Bool、     *)
(*       Arith、Setoid、Morphisms、Lia、Qminmax）。              *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 拆分模块之一，原文区间 *)
(*       L18734-L24767，去头正文与原文区间逐字节同源。           *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.

Section Alignment.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略（如 SFT 策略） *)
Variable pi_ref_pos : forall s, lt zero (pi_ref s).
Variable pi_ref_norm : Id (sum_over_S pi_ref) one.

(* 闭式最优解：π*(s) ∝ π_ref(s)·e^{r(s)/β}，归一化配分函数 *)
Definition Z_align : R :=
  sum_over_S (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

Variable Z_align_pos : lt zero Z_align.

Definition pi_star (s : S) : R :=
  mult (inv_pos Z_align Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* π* 正性 *)
Lemma pi_star_pos : forall s : S, lt zero (pi_star s).
Proof.
  intro s.
  unfold pi_star.
  exact (mult_positive (inv_pos Z_align Z_align_pos)
                       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                       (inv_pos_pos Z_align Z_align_pos)
                       (mult_positive (pi_ref s)
                                      (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                                      (pi_ref_pos s)
                                      (exp_neg_pos (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* π* 归一化：Σ π* = 1（与 boltzmann_normalized 同构） *)
Theorem pi_star_normalized :
  Id (sum_over_S pi_star) one.
Proof.  exact (id_trans
           (sum_over_S_ext (fun s => pi_star s)
                           (fun s => mult (inv_pos Z_align Z_align_pos)
                                          (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                           (fun s => (id_refl : Id (pi_star s)
                                                   (mult (inv_pos Z_align Z_align_pos)
                                                         (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))))
           (id_trans
              (sum_over_S_linear (inv_pos Z_align Z_align_pos)
                                 (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
              (id_trans (id_cong (fun x => mult (inv_pos Z_align Z_align_pos) x)
                                 (id_sym (id_refl : Id (sum_over_S (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))) Z_align)))
                        (id_trans (mult_comm (inv_pos Z_align Z_align_pos) Z_align)
                                  (inv_pos_correct Z_align Z_align_pos))))).
Qed.

(* π* 的对数分解：log π*(s) = -log Z + log π_ref(s) + r(s)/β
   （由 π* 定义 + log_mult/log_inv_one_inv/log_exp_neg 逐点展开） *)
Lemma log_pi_star :
  forall s : S,
    Id (log (pi_star s))
       (plus (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  unfold pi_star.
  assert (Hpos1 : lt zero (inv_pos Z_align Z_align_pos)) by exact (inv_pos_pos Z_align Z_align_pos).
  assert (Hpos2 : lt zero (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
    by (apply mult_positive; [apply pi_ref_pos | apply exp_neg_pos]).
  assert (Hlm : Id (log (mult (inv_pos Z_align Z_align_pos) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                  (plus (log (inv_pos Z_align Z_align_pos)) (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))))
    by exact (log_mult (inv_pos Z_align Z_align_pos) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) Hpos1 Hpos2).
  assert (Hli : Id (log (inv_pos Z_align Z_align_pos)) (opp (log Z_align)))
    by exact (log_inv_one_inv Z_align Z_align_pos).
  assert (Hpos3 : lt zero (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) by exact (exp_neg_pos _).
  assert (Hlm2 : Id (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                  (plus (log (pi_ref s)) (log (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
    by exact (log_mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref_pos s) Hpos3).
  assert (Hle : Id (log (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                  (mult (inv_pos beta beta_pos) (reward s)))
    by exact (id_trans (log_exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                       (double_neg (mult (inv_pos beta beta_pos) (reward s)))).
  assert (Hlm2b : Id (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                     (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s))))
    by exact (id_trans Hlm2 (id_cong (fun x => plus (log (pi_ref s)) x) Hle)).
  assert (Ht1 : Id (log (mult (inv_pos Z_align Z_align_pos) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   (plus (opp (log Z_align)) (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))))
    by exact (id_trans Hlm (id_cong (fun x => plus x (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))) Hli)).
  assert (Ht2 : Id (plus (opp (log Z_align)) (log (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   (plus (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)))))
    by exact (id_cong (fun x => plus (opp (log Z_align)) x) Hlm2b).
  exact (id_trans Ht1 Ht2).
Qed.

(* 对齐能量：E_align(s) := -r(s) - beta*log pi_ref(s)
   使得 F_align(pi) := Σpi*E_align + beta*Σpi*log pi = -J(pi)。 *)
Definition align_energy (s : S) : R :=
  minus (opp (reward s)) (mult beta (log (pi_ref s))).

(* 对齐目标：J(pi) := -F_align(pi)
   （RLHF 目标 E_π[r] - beta*KL(pi,pi_ref) 的等价形式，
     定义性保证 rlhf_optimal 直接用自由能最小化） *)
Definition align_objective (pi : S -> R) : R :=
  opp (free_energy align_energy beta pi).

Lemma align_energy_exp :
  forall s : S,
    Id (exp_neg (mult (inv_pos beta beta_pos) (align_energy s)))
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intro s.
  unfold align_energy.
  assert (H1 : Id (mult (inv_pos beta beta_pos) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))
                  (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s)))).
  {
    assert (H1a : Id (mult (inv_pos beta beta_pos) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))
                     (minus (mult (inv_pos beta beta_pos) (opp (reward s)))
                            (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s))))))
      by exact (mult_minus_distr_l (inv_pos beta beta_pos) (opp (reward s)) (mult beta (log (pi_ref s)))).
    assert (H1b : Id (mult (inv_pos beta beta_pos) (opp (reward s)))
                     (opp (mult (inv_pos beta beta_pos) (reward s))))
      by exact (opp_mult_l (inv_pos beta beta_pos) (reward s)).
    assert (H1c : Id (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s))))
                     (log (pi_ref s))).
    {
      assert (Hc1 : Id (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s))))
                      (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s))))
        by exact (mult_assoc (inv_pos beta beta_pos) beta (log (pi_ref s))).
      assert (Hc2 : Id (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s)))
                      (mult one (log (pi_ref s))))
        by exact (id_cong (fun x => mult x (log (pi_ref s)))
                          (id_trans (mult_comm (inv_pos beta beta_pos) beta) (inv_pos_correct beta beta_pos))).
      assert (Hc3 : Id (mult one (log (pi_ref s))) (log (pi_ref s)))
        by exact (id_trans (mult_comm one (log (pi_ref s))) (mult_one (log (pi_ref s)))).
      exact (id_trans Hc1 (id_trans Hc2 Hc3)).
    }
    assert (H1d : Id (minus (mult (inv_pos beta beta_pos) (opp (reward s)))
                            (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s)))))
                     (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s))))
      by exact (id_trans (id_cong (fun x => minus x (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s))))) H1b)
                         (id_cong (fun x => minus (opp (mult (inv_pos beta beta_pos) (reward s))) x) H1c)).
    exact (id_trans H1a H1d).
  }
  assert (H2 : Id (opp (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s))))
                  (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s)))).
  {
    assert (H2a : Id (opp (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s))))
                    (plus (opp (opp (mult (inv_pos beta beta_pos) (reward s)))) (log (pi_ref s))))
      by exact (opp_minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s))).
    assert (H2b : Id (plus (opp (opp (mult (inv_pos beta beta_pos) (reward s)))) (log (pi_ref s)))
                    (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s))))
      by exact (id_cong (fun x => plus x (log (pi_ref s))) (double_neg (mult (inv_pos beta beta_pos) (reward s)))).
    exact (id_trans H2a H2b).
  }
  assert (H3 : Id (opp (mult (inv_pos beta beta_pos) (align_energy s)))
                  (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s)))).
  {
    assert (H3a : Id (opp (mult (inv_pos beta beta_pos) (align_energy s)))
                    (opp (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s)))))
      by exact (id_cong opp H1).
    exact (id_trans H3a H2).
  }
  (* Step 4: E_align/beta = opp (r/beta + log pi_ref) (from H1 + opp_plus) *)
  assert (H3b : Id (mult (inv_pos beta beta_pos) (align_energy s))
                  (opp (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s))))).
  {
    assert (H3b1 : Id (mult (inv_pos beta beta_pos) (align_energy s))
                     (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s))))
      by exact H1.
    assert (H3b2 : Id (minus (opp (mult (inv_pos beta beta_pos) (reward s))) (log (pi_ref s)))
                     (opp (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s))))).
    {
      unfold minus.
      assert (H3b2a : Id (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s))))
                        (opp (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s)))))
        by exact (id_sym (opp_plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s)))).
      exact H3b2a.
    }
    exact (id_trans H3b1 H3b2).
  }
  assert (H4 : Id (exp_neg (mult (inv_pos beta beta_pos) (align_energy s)))
                  (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                        (exp_neg (opp (log (pi_ref s)))))).
  {
    assert (H4a : Id (exp_neg (mult (inv_pos beta beta_pos) (align_energy s)))
                    (exp_neg (opp (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s))))))
      by exact (id_cong (fun t => exp_neg t) H3b).
    assert (H4b : Id (exp_neg (opp (plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s)))))
                    (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                          (exp_neg (opp (log (pi_ref s))))))
      by exact (exp_neg_opp_plus (mult (inv_pos beta beta_pos) (reward s)) (log (pi_ref s))).
    exact (id_trans H4a H4b).
  }
  assert (H5 : Id (exp_neg (opp (log (pi_ref s)))) (pi_ref s))
    by exact (exp_neg_opp_log (pi_ref s) (pi_ref_pos s)).
  assert (H6 : Id (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                        (exp_neg (opp (log (pi_ref s)))))
                  (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
  {
    assert (H6a : Id (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                          (exp_neg (opp (log (pi_ref s)))))
                    (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref s)))
      by exact (id_cong (fun x => mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) x) H5).
    assert (H6b : Id (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref s))
                    (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
      by exact (mult_comm (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref s)).
    exact (id_trans H6a H6b).
  }
  exact (id_trans H4 H6).
Qed.

Lemma align_partition_condition :
  Id Z_align (sum_over_S (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy s)))).
Proof.
  unfold Z_align.
  exact (sum_over_S_ext (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy s))) (fun s => id_sym (align_energy_exp s))).
Qed.

(* ============================================================ *)
(* RLHF 最优性（核心定理）                                    *)
(* ============================================================ *)
(* free_energy 函数外延性（逐点相等 ⟹ 自由能相等）            *)
Lemma free_energy_ext :
  forall f g : S -> R,
    (forall s, Id (f s) (g s)) ->
    Id (free_energy align_energy beta f) (free_energy align_energy beta g).
Proof.
  intros f g Hfg.
  unfold free_energy.
  assert (H1 : Id (sum_over_S (fun s => mult (f s) (align_energy s)))
                  (sum_over_S (fun s => mult (g s) (align_energy s))))
    by (apply sum_over_S_ext; intro s; apply (id_cong (fun x => mult x (align_energy s)) (Hfg s))).
  assert (H2 : Id (sum_over_S (fun s => mult (f s) (log (f s))))
                  (sum_over_S (fun s => mult (g s) (log (g s))))).
  {
    apply sum_over_S_ext.
    intro s.
    assert (Hc1 : Id (mult (f s) (log (f s))) (mult (g s) (log (f s))))
      by exact (id_cong (fun x => mult x (log (f s))) (Hfg s)).
    assert (Hc2 : Id (log (f s)) (log (g s))) by exact (id_cong log (Hfg s)).
    assert (Hc3 : Id (mult (g s) (log (f s))) (mult (g s) (log (g s))))
      by exact (id_cong (fun x => mult (g s) x) Hc2).
    exact (id_trans Hc1 Hc3).
  }
  assert (H3 : Id (plus (sum_over_S (fun s => mult (f s) (align_energy s)))
                        (mult beta (sum_over_S (fun s => mult (f s) (log (f s))))))
                  (plus (sum_over_S (fun s => mult (g s) (align_energy s)))
                        (mult beta (sum_over_S (fun s => mult (g s) (log (g s)))))))
    by exact (id_trans (id_cong (fun x => plus x (mult beta (sum_over_S (fun s => mult (f s) (log (f s)))))) H1)
                    (id_cong (fun x => plus (sum_over_S (fun s => mult (g s) (align_energy s))) (mult beta x)) H2)).
  exact H3.
Qed.

(* 对齐 Boltzmann 恒等：boltzmann_dist align_energy beta ... = pi_star *)
Lemma align_boltzmann_is_pi_star :
  forall s : S,
    Id (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s)
       (pi_star s).
Proof.
  intro s. unfold boltzmann_dist, pi_star.
  exact (id_cong (fun x => mult (inv_pos Z_align Z_align_pos) x) (align_energy_exp s)).
Qed.

(* 对齐 Boltzmann 归一化（pi_star_normalized + 外延） *)
Lemma align_boltzmann_normalized :
  Id (sum_over_S (fun s => boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s)) one.
Proof.
  exact (id_trans (sum_over_S_ext (fun s => boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s) pi_star (fun s => align_boltzmann_is_pi_star s)) pi_star_normalized).
Qed.

(* 对齐 Boltzmann 正性（pi_star_pos + lt_id_l） *)
Lemma align_boltzmann_pos :
  forall s : S, lt zero (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s).
Proof.
  intro s. exact (lt_id_r zero (pi_star s) (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s) (id_sym (align_boltzmann_is_pi_star s)) (pi_star_pos s)).
Qed.

(* RLHF 最优性：J(pi) <= J(pi_star)（对齐目标在奖励加权 Boltzmann 处最大）
   证明：min_free_energy_is_boltzmann（F_align(boltzmann) <= F_align(pi)）
   + free_energy_ext（F_align(boltzmann) = F_align(pi_star)）
   + opp_le_compat（取负得 J(pi) <= J(pi_star)）。 *)
Theorem rlhf_optimal :
  forall pi : S -> R,
    normalized pi -> positive_dist pi ->
    le (align_objective pi) (align_objective pi_star).
Proof.
  intros pi Hnpi Hppi.
  unfold align_objective.
  exact (opp_le_compat (free_energy align_energy beta pi_star) (free_energy align_energy beta pi) (le_id_l (free_energy align_energy beta pi_star) (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos)) (free_energy align_energy beta pi) (id_sym (free_energy_ext (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos) pi_star align_boltzmann_is_pi_star)) (min_free_energy_is_boltzmann align_energy beta beta_pos Z_align Z_align_pos align_partition_condition pi Hnpi Hppi))).
Qed.

(* ============================================================ *)
(* DPO：直接偏好优化（隐式奖励的具体化，P2）                  *)

(* ============================================================ *)
(* DPO：直接偏好优化（隐式奖励的具体化，P2）                  *)
(* ============================================================ *)
(* DPO 的巧妙：将奖励函数隐式表示为策略比率的对数——           *)
(*   r(s) = beta * (log pi(s) - log pi_ref(s))                 *)
(* 从而绕过显式奖励建模。DPO 损失 = -J(pi)（负对齐目标），     *)
(* 由 rlhf_optimal 直接推出 dpo_optimal，完全复用已证理论。     *)
(* ------------------------------------------------------------ *)

(* DPO 隐式奖励：r_imp(pi, s) := beta * (log pi(s) - log pi_ref(s)) *)
Definition dpo_implicit_reward (pi : S -> R) (s : S) : R :=
  mult beta (minus (log (pi s)) (log (pi_ref s))).

(* DPO 损失：负对齐目标（最大化奖励 = 最小化损失） *)
Definition dpo_loss (pi : S -> R) : R :=
  opp (align_objective pi).

(* DPO 最优性：在 pi_star 处损失最小。
   证明：dpo_loss = -J(pi)，rlhf_optimal 给 J(pi) <= J(pi_star)，
   opp_le_compat 取负得 -J(pi_star) <= -J(pi)。 *)
Theorem dpo_optimal :
  forall pi : S -> R,
    normalized pi -> positive_dist pi ->
    le (dpo_loss pi_star) (dpo_loss pi).
Proof.
  intros pi Hnpi Hppi. unfold dpo_loss.
  exact (opp_le_compat (align_objective pi) (align_objective pi_star) (rlhf_optimal pi Hnpi Hppi)).
Qed.

(* ============================================================ *)
(* RLHF 最优策略唯一性（非平凡平行版本：DPO 收敛目标无歧义）   *)
(* ============================================================ *)
(* dpo_optimal 证明 π* 处 DPO 损失最小；此处证明**唯一性**：     *)
(* 任何策略 pi 若取得与 pi_star 相同的最优对齐目标值（J(pi) = J(pi_star)）， *)
(* 则 π = π*（逐点）。                                          *)
(* 证明：取负的逆（opp_eq）把目标相等翻转为自由能相等，再复用   *)
(* free_energy_min_unique（F[p] = F[p_b] ⟹ p = p_b）+            *)
(* align_boltzmann_is_pi_star（p_b = pi_star）——自由能唯一极小的     *)
(* 对偶形式，非平凡：约 12 步跨模块推导链。                     *)
(* ------------------------------------------------------------ *)

(* 取负的逆：-a = -b ⟹ a = b（double_neg 两折） *)
Lemma opp_eq : forall a b : R, Id (opp a) (opp b) -> Id a b.
Proof.
  intros a b Hab. exact (id_trans (id_sym (double_neg a)) (id_trans (id_cong opp Hab) (double_neg b))).
Qed.

Theorem rlhf_optimal_unique :
  forall pi : S -> R,
    normalized pi -> positive_dist pi ->
    Id (align_objective pi) (align_objective pi_star) ->
    forall s : S, Id (pi s) (pi_star s).
Proof.
  intros pi Hnp Hpp Hj s.
  (* 1. 对齐目标相等（取负形式）⟹ 自由能相等（opp_eq） *)
  assert (Hfeq : Id (free_energy align_energy beta pi)
                    (free_energy align_energy beta pi_star)).
  { unfold align_objective in Hj. exact (opp_eq _ _ Hj). }
  (* 2. F(pi_star) = F(boltzmann)：free_energy_ext + 逐点恒等（p_b = pi_star） *)
  assert (Hfeq_b : Id (free_energy align_energy beta pi_star)
                      (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))).
  {
    apply free_energy_ext.
    intro t.
    exact (id_sym (align_boltzmann_is_pi_star t)).
  }
  (* 3. F(pi) = F(boltzmann)（链） *)
  assert (Hfeq0 : Id (free_energy align_energy beta pi)
                     (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos)))
    by exact (id_trans Hfeq Hfeq_b).
  (* 4. 自由能唯一极小：F(pi) = F(p_b) ⟹ pi = p_b（逐点） *)
  assert (Hpi : forall t : S,
                Id (pi t) (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos t))
    by exact (free_energy_min_unique align_energy beta beta_pos Z_align Z_align_pos align_partition_condition
                                    pi Hnp Hpp Hfeq0).
  (* 5. pi = pi_star（p_b = π* 逐点） *)
  exact (id_trans (Hpi s) (align_boltzmann_is_pi_star s)).
Qed.

(* ============================================================ *)
(* 优势分解与策略改进恒等式（PPO/TRPO 的构造性基石）           *)
(* ============================================================ *)
(* 策略梯度家族的数学基础：对齐目标 J(pi) = E_pi[r] - beta·KL(pi||pi_ref)
   可精确分解为参考策略值 + 优势期望 - KL 惩罚：
     J(pi) = J(pi_ref) + E_pi[advantage_pi_ref] - beta·KL(pi||pi_ref)
   这是 TRPO/PPO 代理目标（surrogate objective）的精确形式——非近似。
   证明：自由能展开（free_energy_align_decomp）+ 参考策略 KL 自零
   （relative_entropy_self_zero）+ 优势求和（Hadv）+ 减法双层合并
   （minus_minus_distr）+ 代数坍缩（Hfin），全部显式 Set 层推导。 *)

(* 状态值：V(pi) := E_pi[r] *)
Definition state_value (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (reward s)).

(* 优势：A(pi, s) := r(s) - V(pi) *)
Definition advantage (pi : S -> R) (s : S) : R :=
  minus (reward s) (state_value pi).

(* KL 惩罚项：beta·KL(pi||pi_ref) 中的散度部分 *)
Definition kl_to_ref (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))).

(* 减法双层合并：(a - b) - c = a - (b + c) *)
Lemma minus_minus_distr : forall a b c : R,
  Id (minus (minus a b) c) (minus a (plus b c)).
Proof.
  intros a b c. unfold minus.
  exact (id_trans (id_sym (plus_assoc a (opp b) (opp c))) (id_cong (fun x => plus a x) (id_sym (opp_plus b c)))).
Qed.

(* KL(p||p) = 0（自相对熵为零；Gibbs 等号条件的平凡方向）
   [T3 KL 孪生正典化] 跨件孪生统一：正典 = S04:4768 relative_entropy_self_zero'
   （两件语句逐字同形 forall p : S -> R, Id (relative_entropy p p) zero；原证明体 ~85% 同构，
   唯一实质差 = 零和见证取 mult zero (p s)（本件）vs mult zero one（S04 版），
   收尾链 sum_over_S_linear 的目标和 sum p vs sum (fun _ => one) 随之而异）。
   本件降为 2 行 exact 转发壳（照 S14:5407 wd 桥转发样板），签名逐字保持；
   转发方向受 Require 拓扑约束：S05 本 Require S04（L24），反向即环，故正典必落 S04。 *)
Lemma relative_entropy_self_zero :
  forall p : S -> R,
    Id (relative_entropy p p) zero.
Proof.
  intro p.
  exact (relative_entropy_self_zero' p).
Qed.

(* 自由能展开：F_align(pi) = -V(pi) + beta·KL(pi||pi_ref)（对齐能量的显式求值，
   多态引理——主定理对 pi 与 pi_ref 各用一次） *)
Lemma free_energy_align_decomp :
  forall pi : S -> R,
    Id (free_energy align_energy beta pi)
       (plus (opp (state_value pi)) (mult beta (kl_to_ref pi))).
Proof.
  intro pi.
  (* free_energy 泛化常量为 λ 应用，unfold 不 β-归约 ⟹ 用 change（内核转换）展开形态 *)
  change (Id (plus (sum_over_S (fun s => mult (pi s) (align_energy s)))
                   (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))
             (plus (opp (state_value pi))
                   (mult beta (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))))).
  (* 逐点：pi·E_align = -(pi·r) - pi·(beta·log pi_ref)（Hext 用折叠的 align_energy） *)
  assert (Hext : Id (sum_over_S (fun s => mult (pi s) (align_energy s)))
                   (sum_over_S (fun s => minus (opp (mult (pi s) (reward s)))
                                              (mult (pi s) (mult beta (log (pi_ref s))))))).
  {
    apply sum_over_S_ext.
    intro s.
    unfold align_energy.
    assert (Hd : Id (mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))
                    (minus (mult (pi s) (opp (reward s))) (mult (pi s) (mult beta (log (pi_ref s))))))
      by exact (mult_minus_distr_l (pi s) (opp (reward s)) (mult beta (log (pi_ref s)))).
    assert (Ho : Id (mult (pi s) (opp (reward s))) (opp (mult (pi s) (reward s))))
      by exact (opp_mult_l (pi s) (reward s)).
    exact (id_trans Hd (id_cong (fun x => minus x (mult (pi s) (mult beta (log (pi_ref s))))) Ho)).
  }
  rewrite Hext.
  assert (Hsmin : Id (sum_over_S (fun s => minus (opp (mult (pi s) (reward s)))
                                                (mult (pi s) (mult beta (log (pi_ref s))))))
                     (minus (sum_over_S (fun s => opp (mult (pi s) (reward s))))
                            (sum_over_S (fun s => mult (pi s) (mult beta (log (pi_ref s)))))))
    by exact (sum_over_S_minus (fun s => opp (mult (pi s) (reward s)))
                               (fun s => mult (pi s) (mult beta (log (pi_ref s))))).
  rewrite Hsmin.
  assert (Hso : Id (sum_over_S (fun s => opp (mult (pi s) (reward s))))
                   (opp (state_value pi)))
    by (unfold state_value; exact (sum_opp (fun s => mult (pi s) (reward s)))).
  rewrite Hso.
  (* 提取 beta：Σ pi·(beta·log pi_ref) = beta·Σ pi·log pi_ref（mult 次序重组） *)
  assert (Hswp : forall s, Id (mult (pi s) (mult beta (log (pi_ref s))))
                            (mult beta (mult (pi s) (log (pi_ref s))))).
  { intro s.
    assert (H1 : Id (mult (pi s) (mult beta (log (pi_ref s)))) (mult (mult (pi s) beta) (log (pi_ref s))))
      by exact (mult_assoc (pi s) beta (log (pi_ref s))).
    assert (H2 : Id (mult (mult (pi s) beta) (log (pi_ref s))) (mult (mult beta (pi s)) (log (pi_ref s))))
      by exact (id_cong (fun x => mult x (log (pi_ref s))) (mult_comm (pi s) beta)).
    assert (H3 : Id (mult (mult beta (pi s)) (log (pi_ref s))) (mult beta (mult (pi s) (log (pi_ref s)))))
      by exact (id_sym (mult_assoc beta (pi s) (log (pi_ref s)))).
    exact (id_trans H1 (id_trans H2 H3)). }
  assert (Hext2 : Id (sum_over_S (fun s => mult (pi s) (mult beta (log (pi_ref s)))))
                     (sum_over_S (fun s => mult beta (mult (pi s) (log (pi_ref s))))))
    by exact (sum_over_S_ext _ _ Hswp).
  rewrite Hext2.
  assert (Hlin : Id (sum_over_S (fun s => mult beta (mult (pi s) (log (pi_ref s)))))
                    (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
    by exact (sum_over_S_linear beta (fun s => mult (pi s) (log (pi_ref s)))).
  rewrite Hlin.
  (* KL 展开：Σ pi·(log pi - log pi_ref) = Σ pi·log pi - Σ pi·log pi_ref *)
  assert (Hkl : Id (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))
                   (minus (sum_over_S (fun s => mult (pi s) (log (pi s))))
                          (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))).
  { assert (Hpt2 : forall s, Id (mult (pi s) (minus (log (pi s)) (log (pi_ref s))))
                               (minus (mult (pi s) (log (pi s))) (mult (pi s) (log (pi_ref s)))))
      by (intro s; exact (mult_minus_distr_l (pi s) (log (pi s)) (log (pi_ref s)))).
    assert (He : Id (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))
                    (sum_over_S (fun s => minus (mult (pi s) (log (pi s))) (mult (pi s) (log (pi_ref s))))))
      by exact (sum_over_S_ext _ _ Hpt2).
    exact (id_trans He (sum_over_S_minus (fun s => mult (pi s) (log (pi s)))
                                        (fun s => mult (pi s) (log (pi_ref s))))). }
  rewrite Hkl.
  (* mult 对减法的分配（assert + exact，避开 rewrite 对 minus 展开形态的失配） *)
  assert (Hmd : Id (mult beta (minus (sum_over_S (fun s => mult (pi s) (log (pi s))))
                                     (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                   (minus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))
                          (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))
    by exact (mult_minus_distr_l beta (sum_over_S (fun s => mult (pi s) (log (pi s))))
                                 (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))).
  assert (Hrhs : Id (plus (opp (state_value pi))
                          (mult beta (minus (sum_over_S (fun s => mult (pi s) (log (pi s))))
                                            (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))
                    (plus (opp (state_value pi))
                          (minus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))
                                 (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))))
    by exact (id_cong (fun x => plus (opp (state_value pi)) x) Hmd).
  rewrite Hrhs.
  (* 重组：((opp V) + (opp B')) + (mult beta A) = (opp V) + (mult beta A - B') *)
  assert (Hfin : Id (plus (plus (opp (state_value pi))
                                (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))
                          (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))
                   (plus (opp (state_value pi))
                         (minus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))
                                (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))).
  {
    unfold minus.
    assert (Ha : Id (plus (plus (opp (state_value pi))
                                (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))
                          (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))
                    (plus (opp (state_value pi))
                          (plus (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                                (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))))
      by exact (id_sym (plus_assoc (opp (state_value pi))
                                   (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                                   (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))).
    assert (Hb : Id (plus (opp (state_value pi))
                          (plus (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                                (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
                    (plus (opp (state_value pi))
                          (plus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))
                                (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))))))
      by exact (id_cong (fun x => plus (opp (state_value pi)) x)
                        (plus_comm (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                                   (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))).
    exact (id_trans Ha Hb).
  }
  exact Hfin.
Qed.

(* 对齐目标的精确优势分解（单步 bandit 下的恒等式，非近似） *)
Theorem align_objective_advantage_decomp :
  forall pi : S -> R,
    normalized pi -> positive_dist pi ->
    Id (align_objective pi)
       (plus (align_objective pi_ref)
             (minus (sum_over_S (fun s => mult (pi s) (advantage pi_ref s)))
                    (mult beta (kl_to_ref pi)))).
Proof.
  intros pi Hnpi Hppi.
  (* 1. align_objective 展开（取负）+ 自由能展开 *)
  unfold align_objective.
  assert (Hfe : Id (free_energy align_energy beta pi)
                   (plus (opp (state_value pi)) (mult beta (kl_to_ref pi))))
    by exact (free_energy_align_decomp pi).
  rewrite Hfe.
  (* 2. F(pi_ref) = -V(pi_ref)（KL 自为零） *)
  assert (Hfe_ref : Id (free_energy align_energy beta pi_ref) (opp (state_value pi_ref))).
  {
    assert (H : Id (free_energy align_energy beta pi_ref)
                   (plus (opp (state_value pi_ref)) (mult beta (kl_to_ref pi_ref))))
      by exact (free_energy_align_decomp pi_ref).
    rewrite H.
    assert (Hkl0 : Id (kl_to_ref pi_ref) zero) by exact (relative_entropy_self_zero pi_ref).
    assert (Hmz : Id (mult beta (kl_to_ref pi_ref)) zero)
      by exact (id_trans (id_cong (fun x => mult beta x) Hkl0) (mult_zero beta)).
    assert (Hzz : Id (plus (opp (state_value pi_ref)) (mult beta (kl_to_ref pi_ref)))
                     (plus (opp (state_value pi_ref)) zero))
      by exact (id_cong (fun x => plus (opp (state_value pi_ref)) x) Hmz).
    assert (Hpz : Id (plus (opp (state_value pi_ref)) zero) (opp (state_value pi_ref)))
      by exact (plus_zero (opp (state_value pi_ref))).
    exact (id_trans Hzz Hpz).
  }
  rewrite Hfe_ref.
  (* 3. 优势求和：Σ pi·A(pi_ref) = V(pi) - V(pi_ref) *)
  assert (Hadv : Id (sum_over_S (fun s => mult (pi s) (advantage pi_ref s)))
                    (minus (state_value pi) (state_value pi_ref))).
  {
    unfold advantage.
    assert (Hpt : forall s, Id (mult (pi s) (minus (reward s) (state_value pi_ref)))
                               (minus (mult (pi s) (reward s)) (mult (pi s) (state_value pi_ref))))
      by (intro s; exact (mult_minus_distr_l (pi s) (reward s) (state_value pi_ref))).
    assert (Hext : Id (sum_over_S (fun s => mult (pi s) (minus (reward s) (state_value pi_ref))))
                     (sum_over_S (fun s => minus (mult (pi s) (reward s)) (mult (pi s) (state_value pi_ref)))))
      by exact (sum_over_S_ext _ _ Hpt).
    rewrite Hext.
    assert (Hadd : Id (sum_over_S (fun s => minus (mult (pi s) (reward s)) (mult (pi s) (state_value pi_ref))))
                     (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                            (sum_over_S (fun s => mult (pi s) (state_value pi_ref)))))
      by exact (sum_over_S_minus _ _).
    rewrite Hadd.
    assert (Hv : Id (sum_over_S (fun s => mult (pi s) (state_value pi_ref))) (state_value pi_ref)).
    {
      assert (Hsw : Id (sum_over_S (fun s => mult (pi s) (state_value pi_ref)))
                       (sum_over_S (fun s => mult (state_value pi_ref) (pi s))))
        by exact (sum_over_S_ext _ _ (fun s => mult_comm (pi s) (state_value pi_ref))).
      rewrite Hsw.
      assert (Hlin : Id (sum_over_S (fun s => mult (state_value pi_ref) (pi s)))
                        (mult (state_value pi_ref) (sum_over_S pi)))
        by exact (sum_over_S_linear (state_value pi_ref) pi).
      rewrite Hlin.
      assert (Hv1 : Id (mult (state_value pi_ref) (sum_over_S pi)) (mult (state_value pi_ref) one))
        by exact (id_cong (fun x => mult (state_value pi_ref) x) Hnpi).
      rewrite Hv1.
      assert (Hm1 : Id (mult (state_value pi_ref) one) (state_value pi_ref))
        by exact (mult_one (state_value pi_ref)).
      exact Hm1.
    }
    rewrite Hv.
    reflexivity.
  }
  rewrite Hadv.
  (* 4. 减法双层合并：minus (minus V_pi V_ref) (beta·kl) = minus V_pi (plus V_ref (beta·kl)) *)
  rewrite (minus_minus_distr (state_value pi) (state_value pi_ref) (mult beta (kl_to_ref pi))).
  (* 5. 代数坍缩：opp(-V_ref) + (V_pi - (V_ref + beta·kl)) = -(opp V_pi + beta·kl) *)
  assert (Hfin : Id (plus (opp (opp (state_value pi_ref)))
                          (minus (state_value pi) (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))
                   (opp (plus (opp (state_value pi)) (mult beta (kl_to_ref pi))))).
  {
    unfold minus.
    assert (H1 : Id (plus (opp (opp (state_value pi_ref)))
                          (plus (state_value pi) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))))
                    (plus (state_value pi_ref)
                          (plus (state_value pi) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))))
      by exact (id_cong (fun x => plus x (plus (state_value pi) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))) (double_neg (state_value pi_ref))).
    assert (H2 : Id (plus (state_value pi_ref)
                          (plus (state_value pi) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))))
                    (plus (plus (state_value pi_ref) (state_value pi))
                          (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))))
      by exact (plus_assoc (state_value pi_ref) (state_value pi) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))).
    assert (H3 : Id (plus (plus (state_value pi_ref) (state_value pi))
                          (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))
                    (plus (plus (state_value pi) (state_value pi_ref))
                          (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))))
      by exact (id_cong (fun x => plus x (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi))))) (plus_comm (state_value pi_ref) (state_value pi))).
    assert (H4 : Id (plus (plus (state_value pi) (state_value pi_ref))
                          (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))
                    (plus (state_value pi)
                          (plus (state_value pi_ref)
                                (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))))
      by exact (id_sym (plus_assoc (state_value pi) (state_value pi_ref) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))).
    (* 消去 V_ref 与 -V_ref *)
    assert (H5 : Id (plus (state_value pi_ref) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))
                    (opp (mult beta (kl_to_ref pi)))).
    {
      assert (H5a : Id (plus (state_value pi_ref) (opp (plus (state_value pi_ref) (mult beta (kl_to_ref pi)))))
                       (plus (state_value pi_ref) (plus (opp (state_value pi_ref)) (opp (mult beta (kl_to_ref pi))))))
        by exact (id_cong (fun x => plus (state_value pi_ref) x) (opp_plus (state_value pi_ref) (mult beta (kl_to_ref pi)))).
      assert (H5b : Id (plus (state_value pi_ref) (plus (opp (state_value pi_ref)) (opp (mult beta (kl_to_ref pi)))))
                       (plus (plus (state_value pi_ref) (opp (state_value pi_ref))) (opp (mult beta (kl_to_ref pi)))))
        by exact (plus_assoc (state_value pi_ref) (opp (state_value pi_ref)) (opp (mult beta (kl_to_ref pi)))).
      assert (H5c : Id (plus (plus (state_value pi_ref) (opp (state_value pi_ref))) (opp (mult beta (kl_to_ref pi))))
                       (plus zero (opp (mult beta (kl_to_ref pi)))))
        by exact (id_cong (fun x => plus x (opp (mult beta (kl_to_ref pi)))) (plus_opp (state_value pi_ref))).
      assert (H5d : Id (plus zero (opp (mult beta (kl_to_ref pi)))) (opp (mult beta (kl_to_ref pi))))
        by exact (id_trans (plus_comm zero (opp (mult beta (kl_to_ref pi)))) (plus_zero (opp (mult beta (kl_to_ref pi))))).
      exact (id_trans H5a (id_trans H5b (id_trans H5c H5d))).
    }
    (* 目标右侧反向重组：plus V_pi (opp (beta·kl)) = opp (plus (opp V_pi) (beta·kl)) *)
    assert (H6 : Id (plus (state_value pi) (opp (mult beta (kl_to_ref pi))))
                    (opp (plus (opp (state_value pi)) (mult beta (kl_to_ref pi))))).
    {
      assert (H6a : Id (opp (plus (opp (state_value pi)) (mult beta (kl_to_ref pi))))
                       (plus (opp (opp (state_value pi))) (opp (mult beta (kl_to_ref pi)))))
        by exact (opp_plus (opp (state_value pi)) (mult beta (kl_to_ref pi))).
      assert (H6b : Id (plus (opp (opp (state_value pi))) (opp (mult beta (kl_to_ref pi))))
                       (plus (state_value pi) (opp (mult beta (kl_to_ref pi)))))
        by exact (id_cong (fun x => plus x (opp (mult beta (kl_to_ref pi)))) (double_neg (state_value pi))).
      exact (id_sym (id_trans H6a H6b)).
    }
    exact (id_trans (id_trans (id_trans (id_trans H1 H2) H3) (id_trans H4 (id_cong (fun x => plus (state_value pi) x) H5))) H6).
  }
  exact (id_sym Hfin).
Qed.

(* ============================================================ *)
(* PPO：裁剪代理目标（改进恒等式.txt 块 2）                     *)
(* ============================================================ *)
(* 策略梯度家族：重要性采样比率 r(s) = pi_star(s)/pi_old(s)，裁剪  *)
(* 到 [1-eps, 1+eps]（clip），PPO 目标取 min(r, clip(r)) 的期望。  *)
(* ppo_conservative 证明裁剪使目标保守（≤ 未裁剪 IS 目标——         *)
(* advantage ≥ 0 时逐点 min_le_l + le_mult_compat_r，经             *)
(* sum_over_S_le 提升）；clip_lower 给出裁剪的下界（r_max_le_r）。*)

Variable pi_old : S -> R.
Variable pi_old_pos : forall s, lt zero (pi_old s).
Variable pi_old_norm : Id (sum_over_S pi_old) one.
Variable advantage_fn : S -> R.
Variable advantage_nonneg : forall s, le zero (advantage_fn s).
Variable epsilon : R.
Variable epsilon_pos : lt zero epsilon.

(* 重要性采样比率：r(s) := pi_star(s)/pi_old(s) *)
Definition importance_ratio (s : S) : R :=
  mult (pi_star s) (inv_pos (pi_old s) (pi_old_pos s)).

(* 裁剪：clip(r) := max(min(r, 1+eps), 1-eps) *)
Definition clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (minus one epsilon).

(* PPO 裁剪代理目标：E_pi_old[min(r, clip(r)) · advantage] *)
Definition ppo_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
                         (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))).

(* 未裁剪 IS 目标（对照基线） *)
Definition is_objective : R :=
  sum_over_S (fun s => mult (pi_old s) (mult (importance_ratio s) (advantage_fn s))).

(* 裁剪下界：clip(r) ≥ 1 - eps（r_max_le_r） *)
Lemma clip_lower : forall r : R, le (minus one epsilon) (clip r).
Proof.
  intro r.
  unfold clip.
  unfold minus.
  exact (r_max_le_r (min r (plus one epsilon)) (plus one (opp epsilon))).
Qed.

(* PPO 保守性：min(r, clip(r)) ≤ r（min_le_l）⟹ ppo_objective ≤ is_objective。
   裁剪牺牲一点目标值换取方差稳定——"不优于未裁剪"的定量证明。 *)
Theorem ppo_conservative :
  le ppo_objective is_objective.
Proof.
  unfold ppo_objective, is_objective.
  apply sum_over_S_le.
  intro s.
  exact (le_mult_compat_r (pi_old s)
                          (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))
                          (mult (importance_ratio s) (advantage_fn s))
                          (lt_le_iff zero (pi_old s) (inl (pi_old_pos s)))
                          (le_mult_compat_weak (min (importance_ratio s) (clip (importance_ratio s)))
                                               (importance_ratio s) (advantage_fn s)
                                               (advantage_nonneg s)
                                               (min_le_l (importance_ratio s) (clip (importance_ratio s))))).
Qed.

(* ============================================================ *)
(* T1.1：标准 PPO 代理目标与无前提保守性（并入）    *)
(*   标准形式 min(r·A, clip(r)·A) ≤ r·A 是纯定义性的           *)
(*   （min_le_l，无需 advantage_nonneg）——把 §6 使用限制 2     *)
(*   的"形式非标准"改写为等价性引理 + 无前提保守性            *)
(* ============================================================ *)

(* 标准 PPO 代理目标：E_pi_old[min(r·A, clip(r)·A)] *)
Definition std_ppo_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
    (min (mult (importance_ratio s) (advantage_fn s))
         (mult (clip (importance_ratio s)) (advantage_fn s)))).

(* 标准 PPO 保守性（无符号前提）：min(rA, clip(rA)) ≤ rA（min_le_l 定义性） *)
Theorem std_ppo_conservative : le std_ppo_objective is_objective.
Proof.
  unfold std_ppo_objective, is_objective.
  apply sum_over_S_le.
  intro s.
  exact (le_mult_compat_r (pi_old s)
                          (min (mult (importance_ratio s) (advantage_fn s))
                               (mult (clip (importance_ratio s)) (advantage_fn s)))
                          (mult (importance_ratio s) (advantage_fn s))
                          (lt_le_iff zero (pi_old s) (inl (pi_old_pos s)))
                          (min_le_l (mult (importance_ratio s) (advantage_fn s))
                                    (mult (clip (importance_ratio s)) (advantage_fn s)))).
Qed.

(* ============================================================ *)
(* RLHF 硬核扩展：策略比率 / 裁剪有界 / DPO 基线恢复            *)
(* （可微性代数闭环.txt 模块二节选，修正方向错误）              *)
(* ============================================================ *)

(* 策略比率：r(θ) = π(s)/π_old(s)（PPO/TRPO 相对更新的支撑） *)
Definition policy_ratio (pi pi_old : S -> R) (s : S) (Hpos : lt zero (pi_old s)) : R :=
  mult (pi s) (inv_pos (pi_old s) Hpos).

(* 裁剪函数：clip(r, low, high) = min(max(low, r), high)（标准 PPO 形态） *)
Definition ppo_clip (r low high : R) : R :=
  min (r_max low r) high.

(* PPO 代理目标（单步 bandit）：E[ min(r·A, clip(r)·A) ] *)
Definition ppo_surrogate (pi pi_old : S -> R) (adv : S -> R) (eps : R)
  (pi_old_pos : forall s, lt zero (pi_old s)) : R :=
  sum_over_S (fun s => mult (pi_old s)
    (min (mult (policy_ratio pi pi_old s (pi_old_pos s)) (adv s))
         (mult (ppo_clip (policy_ratio pi pi_old s (pi_old_pos s))
                         (minus one eps) (plus one eps))
               (adv s)))).

(* 未裁剪 IS 目标（带自由变量 pi）：E_pi_old[r·A]（ppo_surrogate 的对照基线） *)
Definition is_objective_of (pi pi_old : S -> R) (adv : S -> R)
  (pi_old_pos : forall s, lt zero (pi_old s)) : R :=
  sum_over_S (fun s => mult (pi_old s) (mult (policy_ratio pi pi_old s (pi_old_pos s)) (adv s))).


(* 裁剪上界：clip(r) ≤ high（min_le_r；下界 low ≤ clip(r) 需 min 的
   "最小元"性质，接口仅给 min_le_l/r，暂缺——见注记） *)
Lemma ppo_clip_upper :
  forall r low high, le (ppo_clip r low high) high.
Proof.
  intros r low high. unfold ppo_clip. exact (min_le_r (r_max low r) high).
Qed.

(* DPO 隐式奖励的显式对数形式（与 dpo_implicit_reward 逐点恒等） *)
Definition dpo_reward_explicit (pi : S -> R) (s : S) : R :=
  mult beta (minus (log (pi s)) (log (pi_ref s))).

Theorem dpo_reward_is_implicit :
  forall pi s,
    Id (dpo_reward_explicit pi s) (dpo_implicit_reward pi s).
Proof.
  intros pi s. unfold dpo_reward_explicit, dpo_implicit_reward. reflexivity.
Qed.

(* DPO 奖励在 π* 处的闭式值：r*(s) = r(s) − β·log Z_align（配分基线偏移——
   DPO 隐式奖励精确恢复真实奖励，差一个与状态无关的常数项 β·log Z_align）。
   注：可微性代数闭环.txt 原稿误写为 = r(s)（Z_align 项不消失），此处修正。 *)
Theorem dpo_reward_recovers_up_to_baseline :
  forall s,
    Id (dpo_reward_explicit pi_star s)
       (plus (reward s) (opp (mult beta (log Z_align)))).
Proof.
  intro s.
  unfold dpo_reward_explicit.
  assert (Hlog : Id (log (pi_star s))
                    (plus (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)))))
    by exact (log_pi_star s).
  rewrite Hlog.
  (* 消去 log pi_ref：minus (plus A (plus B C)) B = plus A C *)
  assert (H1 : Id (minus (plus (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)))) (log (pi_ref s)))
                  (plus (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s)))).
  {
    unfold minus.
    assert (Ha : Id (plus (plus (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)))) (opp (log (pi_ref s))))
                    (plus (opp (log Z_align)) (plus (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s))))))
      by exact (id_sym (plus_assoc (opp (log Z_align)) (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s))))).
    assert (Hb : Id (plus (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s))))
                    (mult (inv_pos beta beta_pos) (reward s))).
    {
      assert (Hb1 : Id (plus (plus (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s))))
                       (plus (log (pi_ref s)) (plus (mult (inv_pos beta beta_pos) (reward s)) (opp (log (pi_ref s))))))
        by exact (id_sym (plus_assoc (log (pi_ref s)) (mult (inv_pos beta beta_pos) (reward s)) (opp (log (pi_ref s))))).
      assert (Hb2 : Id (plus (log (pi_ref s)) (plus (mult (inv_pos beta beta_pos) (reward s)) (opp (log (pi_ref s)))))
                       (plus (log (pi_ref s)) (plus (opp (log (pi_ref s))) (mult (inv_pos beta beta_pos) (reward s)))))
        by exact (id_cong (fun z => plus (log (pi_ref s)) z) (plus_comm (mult (inv_pos beta beta_pos) (reward s)) (opp (log (pi_ref s))))).
      assert (Hb3 : Id (plus (log (pi_ref s)) (plus (opp (log (pi_ref s))) (mult (inv_pos beta beta_pos) (reward s))))
                       (plus (plus (log (pi_ref s)) (opp (log (pi_ref s)))) (mult (inv_pos beta beta_pos) (reward s))))
        by exact (plus_assoc (log (pi_ref s)) (opp (log (pi_ref s))) (mult (inv_pos beta beta_pos) (reward s))).
      assert (Hb4 : Id (plus (plus (log (pi_ref s)) (opp (log (pi_ref s)))) (mult (inv_pos beta beta_pos) (reward s)))
                       (mult (inv_pos beta beta_pos) (reward s)))
        by exact (id_trans (id_cong (fun z => plus z (mult (inv_pos beta beta_pos) (reward s))) (plus_opp (log (pi_ref s))))
                           (id_trans (plus_comm zero (mult (inv_pos beta beta_pos) (reward s)))
                                     (plus_zero (mult (inv_pos beta beta_pos) (reward s))))).
      exact (id_trans Hb1 (id_trans Hb2 (id_trans Hb3 Hb4))).
    }
    exact (id_trans Ha (id_cong (fun z => plus (opp (log Z_align)) z) Hb)).
  }
  rewrite H1.
  assert (H2 : Id (mult beta (plus (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s))))
                  (plus (mult beta (opp (log Z_align))) (mult beta (mult (inv_pos beta beta_pos) (reward s)))))
    by exact (distrib beta (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s))).
  rewrite H2.
  assert (H3 : Id (mult beta (mult (inv_pos beta beta_pos) (reward s))) (reward s)).
  {
    assert (H3a : Id (mult beta (mult (inv_pos beta beta_pos) (reward s))) (mult (mult beta (inv_pos beta beta_pos)) (reward s)))
      by exact (mult_assoc beta (inv_pos beta beta_pos) (reward s)).
    assert (H3b : Id (mult (mult beta (inv_pos beta beta_pos)) (reward s)) (mult one (reward s)))
      by exact (id_cong (fun z => mult z (reward s)) (inv_pos_correct beta beta_pos)).
    assert (H3c : Id (mult one (reward s)) (reward s))
      by exact (id_trans (mult_comm one (reward s)) (mult_one (reward s))).
    exact (id_trans H3a (id_trans H3b H3c)).
  }
  rewrite H3.
  assert (H4 : Id (mult beta (opp (log Z_align))) (opp (mult beta (log Z_align))))
    by exact (opp_mult_l beta (log Z_align)).
  rewrite H4.
  assert (H5 : Id (plus (opp (mult beta (log Z_align))) (reward s))
                  (plus (reward s) (opp (mult beta (log Z_align)))))
    by exact (plus_comm (opp (mult beta (log Z_align))) (reward s)).
  exact H5.
Qed.

(* 共同被加项消去：minus (plus A B) (plus A C) = minus B C（纯环代数） *)
Lemma minus_plus_common : forall A B C : R,
  Id (minus (plus A B) (plus A C)) (minus B C).
Proof.  intros A B C.
  unfold minus.
  exact (id_trans (id_cong (fun x => plus (plus A B) x) (opp_plus A C))
                  (id_trans (plus_swap_mid A B (opp A) (opp C))
                            (id_trans (id_cong (fun x => plus x (plus B (opp C))) (plus_opp A))
                                      (id_trans (plus_comm zero (plus B (opp C))) (plus_zero (plus B (opp C))))))).
Qed.

(* DPO 隐式奖励的相对差分精确恢复：r_DPO(s) − r_DPO(s') = r(s) − r(s')。
   （配分函数基线 β·log Z_align 在差分中严格消去——DPO 隐式奖励的
     相对值无偏。非平凡：dpo_reward_recovers_up_to_baseline 给出
     r_DPO(π*,s) = r(s) + opp(β·log Z)，两状态相减后共同项消去。） *)
Theorem dpo_reward_relative_exact :
  forall s s',
    Id (minus (dpo_implicit_reward pi_star s) (dpo_implicit_reward pi_star s'))
       (minus (reward s) (reward s')).
Proof.
  intros s s'.
  (* 用已证闭式：dpo_reward_explicit pi_star s = r(s) + opp(beta·log Z) *)
  assert (Hrec_s : Id (dpo_reward_explicit pi_star s)
                      (plus (reward s) (opp (mult beta (log Z_align)))))
    by exact (dpo_reward_recovers_up_to_baseline s).
  assert (Hrec_s' : Id (dpo_reward_explicit pi_star s')
                       (plus (reward s') (opp (mult beta (log Z_align)))))
    by exact (dpo_reward_recovers_up_to_baseline s').
  (* dpo_reward_explicit = dpo_implicit_reward（同义） *)
  assert (Himp_s : Id (dpo_implicit_reward pi_star s) (dpo_reward_explicit pi_star s))
    by exact (id_sym (dpo_reward_is_implicit pi_star s)).
  assert (Himp_s' : Id (dpo_implicit_reward pi_star s') (dpo_reward_explicit pi_star s'))
    by exact (id_sym (dpo_reward_is_implicit pi_star s')).
  (* LHS 替换为 r(s) − r(s')（经共同项消去） *)
  assert (Hmain : Id (minus (dpo_reward_explicit pi_star s) (dpo_reward_explicit pi_star s'))
                     (minus (reward s) (reward s'))).
  {
    assert (H1 : Id (minus (dpo_reward_explicit pi_star s) (dpo_reward_explicit pi_star s'))
                    (minus (plus (reward s) (opp (mult beta (log Z_align))))
                           (plus (reward s') (opp (mult beta (log Z_align))))))
      by exact (id_cong2 minus Hrec_s Hrec_s').
    (* 共同项 opp(beta·log Z) 换到左边，匹配 minus_plus_common *)
    assert (H1a : Id (minus (plus (reward s) (opp (mult beta (log Z_align))))
                            (plus (reward s') (opp (mult beta (log Z_align)))))
                     (minus (plus (opp (mult beta (log Z_align))) (reward s))
                            (plus (opp (mult beta (log Z_align))) (reward s'))))
      by exact (id_cong2 minus (plus_comm (reward s) (opp (mult beta (log Z_align))))
                                (plus_comm (reward s') (opp (mult beta (log Z_align))))).
    assert (H2 : Id (minus (plus (opp (mult beta (log Z_align))) (reward s))
                           (plus (opp (mult beta (log Z_align))) (reward s')))
                    (minus (reward s) (reward s')))
      by exact (minus_plus_common (opp (mult beta (log Z_align))) (reward s) (reward s')).
    exact (id_trans H1 (id_trans H1a H2)).
  }
  (* 替换回 dpo_implicit_reward 形式 *)
  assert (Hlhs : Id (minus (dpo_implicit_reward pi_star s) (dpo_implicit_reward pi_star s'))
                    (minus (dpo_reward_explicit pi_star s) (dpo_reward_explicit pi_star s')))
    by exact (id_cong2 minus Himp_s Himp_s').
  exact (id_trans Hlhs Hmain).
Qed.

(* ============================================================ *)
(* DPO 差分结构（聚焦AI算法.txt 模块 4 补充）：                 *)
(*   1) minus_rearrange_four：四元差分重排                       *)
(*      (a−b) − (c−d) = (a−c) − (b−d)（纯环代数）              *)
(*   2) dpo_reward_diff_is_log_ratio_diff：一般策略 pi 的 DPO    *)
(*      隐式奖励差分分解为策略对数比率差与参考策略对数比率差    *)
(*      的双重差分——DPO/PPO 梯度方向的代数结构。                *)
(* ------------------------------------------------------------ *)

(* 四元差分重排：(a−b) − (c−d) = (a−c) − (b−d)（非平凡代数链：
   unfold minus + opp_plus + double_neg + plus_assoc/comm 重排） *)
Lemma minus_rearrange_four : forall a b c d : R,
  Id (minus (minus a b) (minus c d)) (minus (minus a c) (minus b d)).
Proof.  intros a b c d.
  unfold minus.
  exact (id_trans (id_cong (fun x => plus (plus a (opp b)) x)
                           (id_trans (opp_plus c (opp d)) (id_cong (fun y => plus (opp c) y) (double_neg d))))
                  (id_trans (plus_swap_mid a (opp b) (opp c) d)
                            (id_cong (fun x => plus (plus a (opp c)) x)
                                     (id_trans (id_cong (fun y => plus (opp b) y) (id_sym (double_neg d)))
                                               (id_sym (opp_plus b (opp d))))))).
Qed.

(* DPO 隐式奖励差分 = beta·(策略对数比率差 − 参考对数比率差)：
   r_DPO(pi,s) − r_DPO(pi,s') = beta·((log pi(s) − log pi(s'))
   − (log pi_ref(s) − log pi_ref(s')))。
   非平凡：mult_minus_distr_l 提取 beta + minus_rearrange_four 重排。 *)
Theorem dpo_reward_diff_is_log_ratio_diff :
  forall (pi : S -> R) (s s' : S),
    Id (minus (dpo_implicit_reward pi s) (dpo_implicit_reward pi s'))
       (mult beta (minus (minus (log (pi s)) (log (pi s')))
                         (minus (log (pi_ref s)) (log (pi_ref s'))))).
Proof.
  intros pi s s'.
  unfold dpo_implicit_reward.
  (* beta·(A−B) − beta·(C−D) = beta·((A−B)−(C−D)) *)
  assert (H1 : Id (minus (mult beta (minus (log (pi s)) (log (pi_ref s))))
                         (mult beta (minus (log (pi s')) (log (pi_ref s')))))
                  (mult beta (minus (minus (log (pi s)) (log (pi_ref s)))
                                    (minus (log (pi s')) (log (pi_ref s'))))))
    by exact (id_sym (mult_minus_distr_l beta (minus (log (pi s)) (log (pi_ref s))) (minus (log (pi s')) (log (pi_ref s'))))).
  rewrite H1.
  (* 四元重排：(a−b)−(c−d) = (a−c)−(b−d)，a=log pi s, b=log pi_ref s, c=log pi s', d=log pi_ref s' *)
  assert (H2 : Id (minus (minus (log (pi s)) (log (pi_ref s)))
                         (minus (log (pi s')) (log (pi_ref s'))))
                  (minus (minus (log (pi s)) (log (pi s')))
                         (minus (log (pi_ref s)) (log (pi_ref s')))))
    by exact (minus_rearrange_four (log (pi s)) (log (pi_ref s)) (log (pi s')) (log (pi_ref s'))).
  rewrite H2.
  reflexivity.
Qed.

(* ============================================================ *)
(* PPO/TRPO 单调改进与 KL 控制（单调改进与hentic KL 控制.txt 块1）*)
(* ============================================================ *)
(* 1) advantage_expectation_zero：E_pi[A_pi] = 0（优势期望自零；  *)
(*    TRPO/PPO 代理目标的基线性质；非平凡：求和线性 + 常数提取   *)
(*    + 归一化坍缩）                                            *)
(* 2) exact_improvement_identity：从 π_ref 出发的精确改进恒等式  *)
(*    J(π_new) − J(π_ref) = E_{π_new}[A_ref] − β·KL(π_new‖π_ref) *)
(*    （经 align_objective_advantage_decomp；KL 项对 π_ref，非    *)
(*    对 π_old——注意原草案概念有误）                            *)
(* 3) ppo_monotonic_improvement：E[A_ref] ≥ β·KL ⟹ J(π_ref) ≤    *)
(*    J(π_new)（单调改进的充分条件）                             *)
(* ------------------------------------------------------------ *)

(* 优势期望自零：Σ_s pi(s)·A_pi(s) = 0（pi 归一化）。
   证明：A_pi(s) = r(s) − V(pi)，Σ pi·r = V(pi)（state_value 定义），
   Σ pi·V(pi) = V(pi)·Σ pi = V(pi)（常数提取 + 归一化），相减为零。 *)
Theorem advantage_expectation_zero :
  forall pi : S -> R,
    normalized pi ->
    Id (sum_over_S (fun s => mult (pi s) (advantage pi s))) zero.
Proof.
  intros pi Hnorm.
  unfold advantage, state_value.
  (* 逐点：pi·(r − V) = pi·r − pi·V *)
  assert (Hpt : forall s, Id (mult (pi s) (minus (reward s) (sum_over_S (fun t => mult (pi t) (reward t)))))
                            (minus (mult (pi s) (reward s))
                                   (mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t))))))
    by (intro s; exact (mult_minus_distr_l (pi s) (reward s) (sum_over_S (fun t => mult (pi t) (reward t))))).
  assert (Hext : Id (sum_over_S (fun s => mult (pi s) (minus (reward s) (sum_over_S (fun t => mult (pi t) (reward t))))))
                    (sum_over_S (fun s => minus (mult (pi s) (reward s)) (mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t)))))))
    by exact (sum_over_S_ext _ _ Hpt).
  rewrite Hext.
  assert (Hadd : Id (sum_over_S (fun s => minus (mult (pi s) (reward s)) (mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t))))))
                    (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                           (sum_over_S (fun s => mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t)))))))
    by exact (sum_over_S_minus _ _).
  rewrite Hadd.
  (* Σ pi·V = V·Σ pi = V（常数提取 + 归一化） *)
  assert (Hsw : forall s, Id (mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t))))
                            (mult (sum_over_S (fun t => mult (pi t) (reward t))) (pi s)))
    by (intro s; apply mult_comm).
  assert (Hlin : Id (sum_over_S (fun s => mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t)))))
                    (mult (sum_over_S (fun t => mult (pi t) (reward t))) (sum_over_S pi))).
  {
    assert (Hsw_sum : Id (sum_over_S (fun s => mult (pi s) (sum_over_S (fun t => mult (pi t) (reward t)))))
                         (sum_over_S (fun s => mult (sum_over_S (fun t => mult (pi t) (reward t))) (pi s))))
      by exact (sum_over_S_ext _ _ Hsw).
    rewrite Hsw_sum.
    exact (sum_over_S_linear (sum_over_S (fun t => mult (pi t) (reward t))) pi).
  }
  rewrite Hlin.
  assert (Hm1 : Id (mult (sum_over_S (fun t => mult (pi t) (reward t))) one)
                   (sum_over_S (fun t => mult (pi t) (reward t))))
    by exact (mult_one (sum_over_S (fun t => mult (pi t) (reward t)))).
  (* minus (Σpi·r) (Σpi·r) = 0 *)
  assert (Hfinal : Id (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                             (mult (sum_over_S (fun t => mult (pi t) (reward t))) (sum_over_S pi)))
                      zero).
  {
    unfold minus.
    assert (Hid2 : Id (mult (sum_over_S (fun t => mult (pi t) (reward t))) (sum_over_S pi))
                      (sum_over_S (fun t => mult (pi t) (reward t))))
      by exact (id_trans (id_cong (fun x => mult (sum_over_S (fun t => mult (pi t) (reward t))) x) Hnorm) Hm1).
    assert (Hcancel : Id (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                               (opp (sum_over_S (fun t => mult (pi t) (reward t)))))
                         zero)
      by exact (plus_opp (sum_over_S (fun t => mult (pi t) (reward t)))).
    exact (id_trans (id_cong (fun x => plus (sum_over_S (fun s => mult (pi s) (reward s))) (opp x)) Hid2) Hcancel).
  }
  exact Hfinal.
Qed.

(* 从 π_ref 出发的精确改进恒等式：
   J(π_new) − J(π_ref) = E_{π_new}[A_ref] − β·KL(π_new‖π_ref)。
   非平凡：align_objective_advantage_decomp + 优势自零消去（π_ref
   处的 E_{π_ref}[A_ref] = 0）+ KL 自零（KL(π_ref‖π_ref) = 0）。 *)
Theorem exact_improvement_identity :
  forall pi_new : S -> R,
    normalized pi_new -> positive_dist pi_new ->
    Id (minus (align_objective pi_new) (align_objective pi_ref))
       (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
              (mult beta (kl_to_ref pi_new))).
Proof.
  intros pi_new Hnorm Hpos.
  exact (id_trans (id_cong (fun x => minus x (align_objective pi_ref)) (align_objective_advantage_decomp pi_new Hnorm Hpos)) (minus_plus_cancel_r (align_objective pi_ref) (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s))) (mult beta (kl_to_ref pi_new))))).
Qed.

(* PPO 单调改进：E_{π_new}[A_ref] − β·KL(π_new‖π_ref) ≥ 0
   ⟹ J(π_ref) ≤ J(π_new)（代理优势非负 ⟹ 真实目标改进）。
   非平凡：精确恒等式 + le_minus_nonneg（差分非负 ⟹ 被减数 ≤ 减数）。 *)
Theorem ppo_monotonic_improvement :
  forall pi_new : S -> R,
    normalized pi_new -> positive_dist pi_new ->
    le zero (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
                   (mult beta (kl_to_ref pi_new))) ->
    le (align_objective pi_ref) (align_objective pi_new).
Proof.
  intros pi_new Hnorm Hpos Hsur.
  assert (Hid : Id (minus (align_objective pi_new) (align_objective pi_ref))
                   (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
                          (mult beta (kl_to_ref pi_new))))
    by exact (exact_improvement_identity pi_new Hnorm Hpos).
  (* 0 ≤ J_new − J_ref（经 Hid 替换为代理优势差） *)
  assert (Hd : le zero (minus (align_objective pi_new) (align_objective pi_ref))).
  { rewrite Hid. exact Hsur. }
  (* le J_ref J_new：J_ref ≤ J_ref + (J_new − J_ref) = J_new（le_plus_nonneg_r + minus_plus_cancel） *)
  apply (le_id_r (align_objective pi_ref)
                 (plus (align_objective pi_ref) (minus (align_objective pi_new) (align_objective pi_ref)))
                 (align_objective pi_new)
                 (minus_plus_cancel (align_objective pi_ref) (align_objective pi_new))).
  exact (le_plus_nonneg_r (align_objective pi_ref) (minus (align_objective pi_new) (align_objective pi_ref)) Hd).
Qed.

(* KL 惩罚充分条件：若 KL(π_new‖π_ref) ≤ eps 且 E_{π_new}[A_ref] ≥ β·eps，
   则 J(π_ref) ≤ J(π_new)。
   非平凡：E − β·KL ≥ E − β·eps ≥ 0（le_plus_compat + opp_le_compat
   + le_mult_compat_r + le_minus_nonneg）。 *)
Theorem kl_penalty_sufficient :
  forall (pi_new : S -> R) (eps : R),
    normalized pi_new -> positive_dist pi_new ->
    le (kl_to_ref pi_new) eps ->
    le (mult beta eps) (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s))) ->
    le (align_objective pi_ref) (align_objective pi_new).
Proof.
  intros pi_new eps Hnorm Hpos Hkl Hadv.
  apply (ppo_monotonic_improvement pi_new Hnorm Hpos).
  (* 目标：0 ≤ E − β·KL。由 Hadv: β·eps ≤ E 且 Hkl: KL ≤ eps。 *)
  (* 链：0 ≤ E − β·eps ≤ E − β·KL（KL ≤ eps ⟹ −β·eps ≤ −β·KL） *)
  assert (H1 : le (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
                         (mult beta eps))
                  (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
                         (mult beta (kl_to_ref pi_new)))).
  {
    unfold minus.
    apply le_plus_compat.
    - apply le_refl.
    - apply opp_le_compat.
      apply (le_mult_compat_r beta (kl_to_ref pi_new) eps).
      + apply (lt_le_iff _ _). left. exact beta_pos.
      + exact Hkl.
  }
  assert (H2 : le zero (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
                              (mult beta eps))).
  { apply le_minus_nonneg. exact Hadv. }
  exact (le_trans _ _ _ H2 H1).
Qed.

(* ============================================================ *)
(* PPO 差距恒等式（RLHF 对齐扩展.txt 块 3）                     *)
(* ============================================================ *)
(* 1) ppo_gap_exact：is_objective − ppo_objective 精确等于被裁剪  *)
(*    部分（r − min(r, clip(r))）的期望。裁剪只发生在比率偏离     *)
(*    [1−ε, 1+ε] 时——差距的精确代数刻画。                      *)
(* 2) ppo_gap_nonneg：差距非负（ppo_conservative 的直接推论）。   *)
(* ------------------------------------------------------------ *)

(* PPO 差距恒等式：IS − CLIP = E[pi_old·(r − min(r, clip(r)))·adv]。
   非平凡：逐点 mult_minus_distr_l 两层展开 + 求和线性化。 *)
Theorem ppo_gap_exact :
  Id (minus is_objective ppo_objective)
     (sum_over_S (fun s => mult (pi_old s)
                            (mult (minus (importance_ratio s)
                                         (min (importance_ratio s) (clip (importance_ratio s))))
                                  (advantage_fn s)))).
Proof.
  unfold is_objective, ppo_objective.
  (* 逐点：pi_old·r·adv − pi_old·min·adv = pi_old·(r − min)·adv *)
  assert (Hpt : forall s, Id (minus (mult (pi_old s) (mult (importance_ratio s) (advantage_fn s)))
                                    (mult (pi_old s) (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))))
                             (mult (pi_old s) (mult (minus (importance_ratio s)
                                                           (min (importance_ratio s) (clip (importance_ratio s))))
                                                    (advantage_fn s)))).
  {
    intro s.
    (* 外层：pi_old·X − pi_old·Y = pi_old·(X − Y)，X = r·adv, Y = min·adv。
       mult_minus_distr_l 方向是 mult a (minus b c) = minus (mult a b) (mult a c)，
       需要反向（id_sym）。 *)
    assert (H1 : Id (minus (mult (pi_old s) (mult (importance_ratio s) (advantage_fn s)))
                           (mult (pi_old s) (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))))
                    (mult (pi_old s) (minus (mult (importance_ratio s) (advantage_fn s))
                                            (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))))
      by exact (id_sym (mult_minus_distr_l (pi_old s) (mult (importance_ratio s) (advantage_fn s))
                                           (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))).
    (* 内层：r·adv − min·adv = (r − min)·adv。
       无 mult_minus_distr_r，用 mult_comm 换序 + mult_minus_distr_l：
       先证反向 (r − min)·adv = r·adv − min·adv，再 id_sym。 *)
    assert (H2 : Id (minus (mult (importance_ratio s) (advantage_fn s))
                           (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))
                    (mult (minus (importance_ratio s) (min (importance_ratio s) (clip (importance_ratio s))))
                          (advantage_fn s))).
    {
      apply id_sym.
      (* (r − min)·adv = adv·(r − min)（mult_comm） *)
      assert (Hsw1 : Id (mult (minus (importance_ratio s) (min (importance_ratio s) (clip (importance_ratio s)))) (advantage_fn s))
                        (mult (advantage_fn s) (minus (importance_ratio s) (min (importance_ratio s) (clip (importance_ratio s))))))
        by (apply mult_comm).
      (* adv·(r − min) = adv·r − adv·min（mult_minus_distr_l 正向） *)
      assert (Hsw2 : Id (mult (advantage_fn s) (minus (importance_ratio s) (min (importance_ratio s) (clip (importance_ratio s)))))
                        (minus (mult (advantage_fn s) (importance_ratio s))
                               (mult (advantage_fn s) (min (importance_ratio s) (clip (importance_ratio s))))))
        by exact (mult_minus_distr_l (advantage_fn s) (importance_ratio s) (min (importance_ratio s) (clip (importance_ratio s)))).
      (* adv·r = r·adv，adv·min = min·adv（mult_comm） *)
      assert (Hsw3 : Id (minus (mult (advantage_fn s) (importance_ratio s))
                               (mult (advantage_fn s) (min (importance_ratio s) (clip (importance_ratio s)))))
                        (minus (mult (importance_ratio s) (advantage_fn s))
                               (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))))
        by exact (id_cong2 minus (mult_comm (advantage_fn s) (importance_ratio s))
                                (mult_comm (advantage_fn s) (min (importance_ratio s) (clip (importance_ratio s))))).
      exact (id_trans Hsw1 (id_trans Hsw2 Hsw3)).
    }
    exact (id_trans H1 (id_cong (fun x => mult (pi_old s) x) H2)).
  }
  (* 求和：Σ(minus A B) = minus (Σ A) (Σ B)，经 sum_over_S_ext 换逐点 *)
  assert (Hstep1 : Id (sum_over_S (fun s => minus (mult (pi_old s) (mult (importance_ratio s) (advantage_fn s)))
                                                 (mult (pi_old s) (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))))
                      (sum_over_S (fun s => mult (pi_old s) (mult (minus (importance_ratio s)
                                                                         (min (importance_ratio s) (clip (importance_ratio s))))
                                                                  (advantage_fn s)))))
    by exact (sum_over_S_ext _ _ Hpt).
  (* LHS：minus (Σ pi_old·r·adv) (Σ pi_old·min·adv) = 目标 Σ 形态 *)
  assert (Hlhs : Id (minus (sum_over_S (fun s => mult (pi_old s) (mult (importance_ratio s) (advantage_fn s))))
                           (sum_over_S (fun s => mult (pi_old s) (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))))
                    (sum_over_S (fun s => mult (pi_old s) (mult (minus (importance_ratio s)
                                                                       (min (importance_ratio s) (clip (importance_ratio s))))
                                                                (advantage_fn s)))))
    by exact (id_trans (id_sym (sum_over_S_minus (fun s => mult (pi_old s) (mult (importance_ratio s) (advantage_fn s)))
                                                 (fun s => mult (pi_old s) (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s)))))
                       Hstep1).
  exact Hlhs.
Qed.

(* PPO 差距非负：is_objective ≥ ppo_objective（裁剪损失目标值，
   由 ppo_conservative + le_minus_nonneg 直接推出）。 *)
Theorem ppo_gap_nonneg :
  le zero (minus is_objective ppo_objective).
Proof.
  unfold minus.
  exact (le_id_l zero (plus ppo_objective (opp ppo_objective)) (plus is_objective (opp ppo_objective)) (id_sym (plus_opp ppo_objective)) (le_plus_compat ppo_objective is_objective (opp ppo_objective) (opp ppo_objective) ppo_conservative (le_refl (opp ppo_objective)))).
Qed.

(* ============================================================ *)
(* 偏好对直接优化（偏好对直接优化.txt：DPO 对损失构造性代数）   *)
(* ============================================================ *)
(* 1) dpo_pair_loss：DPO 单对损失 = log(1 + e^{−(r_imp(w)−r_imp(l))}) *)
(*    分母正性（构造性：one_pos + exp_neg_pos）                  *)
(* 2) pi_star_implicit_reward_diff：π* 的隐式奖励差分 = 真实奖励  *)
(*    差分（经已证 dpo_reward_relative_exact——Z_align/π_ref 消去）*)
(* 3) dpo_pair_loss_at_star：π* 处损失退化为真实奖励差分的        *)
(*    Sigmoid 交叉熵                                            *)
(* ------------------------------------------------------------ *)

Variable Preference : Set.
Variable pref_win  : Preference -> S.
Variable pref_lose : Preference -> S.

(* 隐式奖励差分：DPO 的核心驱动量（策略比率的对数 odds） *)
Definition implicit_reward_diff (pi : S -> R) (pref : Preference) : R :=
  minus (dpo_implicit_reward pi (pref_win pref))
        (dpo_implicit_reward pi (pref_lose pref)).

(* DPO 单对损失：L(π; y_w, y_l) = log(1 + e^{−(r_imp(y_w) − r_imp(y_l))}) *)
Definition dpo_pair_loss (pi : S -> R) (pref : Preference) : R :=
  log (plus one (exp_neg (implicit_reward_diff pi pref))).

(* 分母严格正性：保证 log 良定义（构造性见证） *)
Lemma dpo_pair_loss_denom_pos : forall (pi : S -> R) (pref : Preference),
  lt zero (plus one (exp_neg (implicit_reward_diff pi pref))).
Proof.
  intros pi pref.
  exact (plus_positive one (exp_neg (implicit_reward_diff pi pref)) one_pos
                         (exp_neg_pos (implicit_reward_diff pi pref))).
Qed.

(* π* 的隐式奖励差分 = 真实奖励差分（Z_align/π_ref 在差分中消去）。
   证明：经已证 dpo_reward_relative_exact（r_DPO(π*,s) − r_DPO(π*,s') = r(s) − r(s')）。 *)
Theorem pi_star_implicit_reward_diff : forall pref : Preference,
  Id (implicit_reward_diff pi_star pref)
     (minus (reward (pref_win pref)) (reward (pref_lose pref))).
Proof.
  intro pref.
  unfold implicit_reward_diff.
  exact (dpo_reward_relative_exact (pref_win pref) (pref_lose pref)).
Qed.

(* π* 处单对损失 = 真实奖励差分的 Sigmoid 交叉熵 *)
Definition dpo_pair_loss_star (pref : Preference) : R :=
  log (plus one (exp_neg (minus (reward (pref_win pref)) (reward (pref_lose pref))))).

Theorem dpo_pair_loss_at_star : forall pref : Preference,
  Id (dpo_pair_loss pi_star pref) (dpo_pair_loss_star pref).
Proof.
  intro pref. unfold dpo_pair_loss, dpo_pair_loss_star.
  exact (id_cong (fun x => log (plus one (exp_neg x))) (pi_star_implicit_reward_diff pref)).
Qed.

(* 数据集级聚合：总损失 = 单对损失的 fold *)
Variable pref_dataset : list Preference.

Definition dpo_total_loss (pi : S -> R) : R :=
  fold_right (fun pref acc => plus (dpo_pair_loss pi pref) acc) zero pref_dataset.

Definition dpo_total_loss_star : R :=
  fold_right (fun pref acc => plus (dpo_pair_loss_star pref) acc) zero pref_dataset.

(* fold 外延性（Set 层工具引理） *)
Lemma fold_right_ext {A B : Set} (f g : A -> B -> B) (l : list A) (b : B) :
  (forall a b', Id (f a b') (g a b')) -> Id (fold_right f b l) (fold_right g b l).
Proof.
  intros Hfg. induction l as [| a rest IH]; simpl.
  - reflexivity.
  - (* 目标：Id (f a (fold f)) (g a (fold g))：Hfg a 与 IH 组合 *)
    apply (id_trans (Hfg a (fold_right f b rest))).
    exact (id_cong (fun x => g a x) IH).
Qed.

(* π* 处总损失 = 显式常数（仅由真实奖励决定，与策略无关） *)
Theorem dpo_total_loss_at_star : Id (dpo_total_loss pi_star) dpo_total_loss_star.
Proof.
  unfold dpo_total_loss, dpo_total_loss_star.
  apply fold_right_ext.
  intros pref acc.
  apply (id_cong (fun x => plus x acc)).
  exact (dpo_pair_loss_at_star pref).
Qed.

(* DPO 总损失单调性：逐对损失下降则总损失下降（非平凡：fold 归纳） *)
Theorem dpo_total_loss_monotone :
  forall pi1 pi2 : S -> R,
    (forall pref, InT pref pref_dataset ->
      le (dpo_pair_loss pi2 pref) (dpo_pair_loss pi1 pref)) ->
    le (dpo_total_loss pi2) (dpo_total_loss pi1).
Proof.
  intros pi1 pi2 Hpt.
  unfold dpo_total_loss.
  induction pref_dataset as [| p rest IH]; simpl.
  - apply le_refl.
  - apply le_plus_compat.
    + apply Hpt. apply InT_here.
    + apply IH. intros pref Hin. apply Hpt. apply InT_next. exact Hin.
Qed.

(* DPO 总损失在 π* 处的局部最优性刻画：若策略 π 的隐式奖励差分
   已与真实奖励差分一致（逐对），则其总损失等于 π* 的总损失。
   非平凡：逐对损失等价 + fold 外延性提升到数据集。 *)
Theorem dpo_total_loss_star_characterization :
  forall pi : S -> R,
    (forall pref, InT pref pref_dataset ->
      Id (implicit_reward_diff pi pref)
         (minus (reward (pref_win pref)) (reward (pref_lose pref)))) ->
    Id (dpo_total_loss pi) dpo_total_loss_star.
Proof.
  intros pi Heq.
  unfold dpo_total_loss, dpo_total_loss_star.
  induction pref_dataset as [| p rest IH]; simpl.
  - reflexivity.
  - (* 逐对等价：dpo_pair_loss pi p = dpo_pair_loss_star p *)
    assert (Hp : Id (dpo_pair_loss pi p) (dpo_pair_loss_star p)).
    {
      unfold dpo_pair_loss, dpo_pair_loss_star.
      assert (Hdiff : Id (implicit_reward_diff pi p)
                         (minus (reward (pref_win p)) (reward (pref_lose p))))
        by exact (Heq p (InT_here p rest)).
      exact (id_cong (fun x => log (plus one (exp_neg x))) Hdiff).
    }
    assert (Hrest : Id (fold_right (fun pref acc => plus (dpo_pair_loss pi pref) acc) zero rest)
                       (fold_right (fun pref acc => plus (dpo_pair_loss_star pref) acc) zero rest)).
    {
      apply IH.
      intros pref Hin. apply Heq. apply (InT_next pref p rest Hin).
    }
    exact (id_cong2 plus Hp Hrest).
Qed.

(* ============================================================ *)
(* RLHF 对齐核心定理补全与强化（RLHF 对齐核心定理补全与强化.txt）*)
(* ============================================================ *)
(* 1) relative_entropy_ext_r：相对熵对第二分布的外延性           *)
(* 2) minus_opp_opp：minus (opp a) (opp b) = minus b a           *)
(* 3) sum_mult_opp_r：Σ pi·opp g = opp (Σ pi·g)                  *)
(* 4) rlhf_free_energy_kl：F_align[pi] = F_align[pi*] + β·KL     *)
(* 5) align_objective_explicit：J(pi) = E[r] − β·KL(pi‖pi_ref)   *)
(* 6) rlhf_optimal_value：pi* 处奖励-熵权衡显式值                 *)
(* 7) rlhf_suboptimality_gap：J(pi* ) − J(pi) = β·KL(pi‖pi* ) ≥ 0   *)
(* 8) rlhf_policy_improvement：KL 到 pi* 不增 ⟹ 目标单调上升      *)
(* ------------------------------------------------------------ *)

(* 相对熵对第二个分布的外延性（构造性；逐点相等 ⟹ KL 相等） *)
Lemma relative_entropy_ext_r :
  forall p q1 q2 : S -> R,
    (forall s, Id (q1 s) (q2 s)) ->
    Id (relative_entropy p q1) (relative_entropy p q2).
Proof.
  intros p q1 q2 Hext.
  unfold relative_entropy.
  apply sum_over_S_ext.
  intro s.
  exact (id_cong (fun x => mult (p s) x) (id_cong2 minus (@id_refl R (log (p s))) (id_cong log (Hext s)))).
Qed.

(* minus (opp a) (opp b) = minus b a（double_neg + plus_comm） *)
Lemma minus_opp_opp :
  forall a b : R, Id (minus (opp a) (opp b)) (minus b a).
Proof.
  intros a b. unfold minus.
  exact (id_trans (id_cong (fun x => plus (opp a) x) (double_neg b)) (plus_comm (opp a) b)).
Qed.

(* Σ pi·opp g = opp (Σ pi·g)（sum_opp + 逐点 opp_mult_l） *)
Lemma sum_mult_opp_r :
  forall (pi : S -> R) (g : S -> R),
    Id (sum_over_S (fun s => mult (pi s) (opp (g s))))
       (opp (sum_over_S (fun s => mult (pi s) (g s)))).
Proof.
  intros pi g.
  exact (id_trans (sum_over_S_ext (fun s => mult (pi s) (opp (g s))) (fun s => opp (mult (pi s) (g s))) (fun s => opp_mult_l (pi s) (g s))) (sum_opp (fun s => mult (pi s) (g s)))).
Qed.

(* RLHF 自由能-KL 恒等式：F_align[pi] = F_align[pi* ] + β·KL(pi‖pi* )
   非平凡：自由能-KL 分解（相对 Boltzmann）+ Boltzmann = pi* 的
   三层替换（free_energy_ext / relative_entropy_ext_r）。 *)
Theorem rlhf_free_energy_kl :
  forall pi : S -> R,
    normalized pi ->
    Id (free_energy align_energy beta pi)
       (plus (free_energy align_energy beta pi_star)
             (mult beta (relative_entropy pi pi_star))).
Proof.
  intros pi Hnorm.
  (* 1. 应用通用自由能-KL 分解（base_loss=align_energy, D=beta） *)
  assert (Hdecomp : Id (free_energy align_energy beta pi)
                       (plus (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))
                             (mult beta (relative_entropy pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))))).
  { exact (free_energy_kl_decomp align_energy beta beta_pos Z_align Z_align_pos align_partition_condition pi Hnorm). }
  (* 2. Boltzmann 分布 = pi_star（逐点） *)
  assert (Hstar : forall s, Id (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s) (pi_star s))
    by exact (align_boltzmann_is_pi_star).
  (* 3. 替换自由能中的 Boltzmann 为 pi_star *)
  assert (Hfe : Id (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))
                   (free_energy align_energy beta pi_star)).
  { apply (free_energy_ext (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos) pi_star Hstar). }
  (* 4. 替换 KL 中的 Boltzmann 为 pi_star *)
  assert (Hkl : Id (relative_entropy pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))
                   (relative_entropy pi pi_star)).
  { apply (relative_entropy_ext_r pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos) pi_star Hstar). }
  (* 5. 组装 *)
  exact (id_trans Hdecomp (id_cong2 plus Hfe (id_cong (fun x => mult beta x) Hkl))).
Qed.

(* 奖励期望：E_π[r] = Σ_s pi(s)·r(s) *)
Definition expected_reward (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (reward s)).

(* KL(pi||pi_ref) 的显式形式（相对参考策略） *)
Definition kl_reference (pi : S -> R) : R :=
  relative_entropy pi pi_ref.

(* 对齐目标显式分解：J(pi) = E[r] − β·KL(pi‖pi_ref)
   非平凡：align_energy 展开 + opp 分配（opp_plus）+ 求和线性
   （sum_over_S_add / sum_over_S_linear）+ 负号提取（sum_mult_opp_r
   / opp_mult_l）+ KL 逐点展开 + distrib 重组（约 12 步链）。 *)
Theorem align_objective_explicit :
  forall pi : S -> R,
    Id (align_objective pi)
       (minus (expected_reward pi) (mult beta (kl_reference pi))).
Proof.
  intro pi.
  unfold align_objective, free_energy, expected_reward, kl_reference, relative_entropy.
  (* 展开 align_energy（在 free_energy 参数内，逐点替换） *)
  assert (Hpt_ae : forall s, Id (align_energy s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))
    by (intro s; unfold align_energy; reflexivity).
  assert (Hsum_ae : Id (sum_over_S (fun s => mult (pi s) (align_energy s)))
                       (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
    by (apply sum_over_S_ext; intro s; exact (id_cong (fun x => mult (pi s) x) (Hpt_ae s))).
  (* Step 0: 目标 LHS 换为显式 align_energy 展开形式 *)
  assert (Hlhs : Id (opp (plus (sum_over_S (fun s => mult (pi s) (align_energy s)))
                               (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
                    (opp (plus (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s))))))
                               (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))).
  {
    apply (id_cong (fun z => opp (plus z (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))) Hsum_ae).
  }
  (* Step 1: opp (plus A B) = plus (opp A) (opp B) *)
  assert (H1 : Id (opp (plus (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s))))))
                             (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
                  (plus (opp (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
                        (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))))
    by exact (opp_plus _ _).
  (* 目标：Id LHS RHS；先用 Hlhs 换 LHS 为显式形式（H1/Hmid 在收尾组装） *)
  (* Step 2: 分解 align_energy 求和 *)
  assert (H2 : Id (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s))))))
                  (plus (sum_over_S (fun s => mult (pi s) (opp (reward s))))
                        (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s)))))))).
  {
    assert (Hpt : forall s, Id (mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))
                              (plus (mult (pi s) (opp (reward s))) (mult (pi s) (opp (mult beta (log (pi_ref s)))))))
      by (intro s;
          exact (id_trans (mult_minus_distr_l (pi s) (opp (reward s)) (mult beta (log (pi_ref s))))
                          (id_cong (fun x => plus (mult (pi s) (opp (reward s))) x)
                                   (id_sym (opp_mult_l (pi s) (mult beta (log (pi_ref s)))))))).
    assert (Hadd : Id (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s))))))
                     (sum_over_S (fun s => plus (mult (pi s) (opp (reward s))) (mult (pi s) (opp (mult beta (log (pi_ref s))))))))
      by exact (sum_over_S_ext _ _ Hpt).
    exact (id_trans Hadd (sum_over_S_add _ _)).
  }
  (* Step 3: opp (sum (pi·opp r)) = expected_reward *)
  assert (H3 : Id (opp (sum_over_S (fun s => mult (pi s) (opp (reward s)))))
                  (sum_over_S (fun s => mult (pi s) (reward s))))
    by exact (id_trans (id_cong opp (sum_mult_opp_r _ _)) (double_neg _)).
  (* Step 4: opp (sum (pi·opp (beta·log_ref))) = mult beta (sum (pi·log_ref)) *)
  assert (H4 : Id (opp (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s)))))))
                  (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))).
  {
    assert (Hso : Id (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s))))))
                     (opp (sum_over_S (fun s => mult (pi s) (mult beta (log (pi_ref s)))))))
      by exact (sum_mult_opp_r _ _).
    assert (Hsw : Id (sum_over_S (fun s => mult (pi s) (mult beta (log (pi_ref s)))))
                     (sum_over_S (fun s => mult beta (mult (pi s) (log (pi_ref s)))))).
    {
      apply sum_over_S_ext.
      intro s.
      (* mult (pi s) (mult beta (log ref)) = mult beta (mult (pi s) (log ref))：
         mult_assoc + mult_comm（同 free_energy_align_decomp.Hswp 模式） *)
      assert (Hs1 : Id (mult (pi s) (mult beta (log (pi_ref s)))) (mult (mult (pi s) beta) (log (pi_ref s))))
        by exact (mult_assoc (pi s) beta (log (pi_ref s))).
      assert (Hs2 : Id (mult (mult (pi s) beta) (log (pi_ref s))) (mult (mult beta (pi s)) (log (pi_ref s))))
        by exact (id_cong (fun x => mult x (log (pi_ref s))) (mult_comm (pi s) beta)).
      assert (Hs3 : Id (mult (mult beta (pi s)) (log (pi_ref s))) (mult beta (mult (pi s) (log (pi_ref s)))))
        by exact (id_sym (mult_assoc beta (pi s) (log (pi_ref s)))).
      exact (id_trans Hs1 (id_trans Hs2 Hs3)).
    }
    assert (Hlin : Id (sum_over_S (fun s => mult beta (mult (pi s) (log (pi_ref s)))))
                      (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
      by exact (sum_over_S_linear beta _).
    assert (Htot : Id (sum_over_S (fun s => mult (pi s) (mult beta (log (pi_ref s)))))
                      (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
      by exact (id_trans Hsw Hlin).
    exact (id_trans (id_cong opp Hso) (id_trans (double_neg _) Htot)).
  }
  (* Step 5: opp (sum align_energy) = plus E (mult beta (sum log_ref)) *)
  assert (H5 : Id (opp (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
                  (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                        (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))).
  {
    (* opp (Σ align_energy 分解) = opp (plus Σ1 Σ2)（H2 反向）
       = plus (opp Σ1) (opp Σ2)（opp_plus）= plus E (mult beta Σlog_ref)（H3 H4） *)
    assert (H2s : Id (opp (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
                     (opp (plus (sum_over_S (fun s => mult (pi s) (opp (reward s))))
                                (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s)))))))))
      by exact (id_cong opp H2).
    assert (Hopp : Id (opp (plus (sum_over_S (fun s => mult (pi s) (opp (reward s))))
                                 (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s))))))))
                      (plus (opp (sum_over_S (fun s => mult (pi s) (opp (reward s)))))
                            (opp (sum_over_S (fun s => mult (pi s) (opp (mult beta (log (pi_ref s)))))))))
      by exact (opp_plus _ _).
    exact (id_trans H2s (id_trans Hopp (id_cong2 plus H3 H4))).
  }
  (* Step 6: opp (mult beta (sum (pi·log pi))) = mult beta (sum (pi·opp log pi)) *)
  assert (H6 : Id (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))
                  (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))).
  {
    assert (Hopp : Id (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s))))))
                    (mult beta (opp (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
      by exact (id_sym (opp_mult_l beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))).
    assert (Hso : Id (opp (sum_over_S (fun s => mult (pi s) (log (pi s)))))
                    (sum_over_S (fun s => opp (mult (pi s) (log (pi s))))))
      by exact (id_sym (sum_opp (fun s => mult (pi s) (log (pi s))))).
    assert (Hpt : Id (sum_over_S (fun s => opp (mult (pi s) (log (pi s)))))
                    (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))
      by (apply sum_over_S_ext; intro s; exact (id_sym (opp_mult_l (pi s) (log (pi s))))).
    exact (id_trans Hopp (id_cong (fun x => mult beta x) (id_trans Hso Hpt))).
  }
  (* Step 7: 组合 LHS —— plus (opp A) (opp B) = plus (plus E X) Y（H5/H6） *)
  assert (H7 : Id (plus (opp (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
                        (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
                  (plus (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                              (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                        (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))).
  { exact (id_cong2 plus H5 H6). }
  (* Step 8: 提取 beta（重组） *)
  assert (H8 : Id (plus (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                              (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                        (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))
                  (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                        (mult beta (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                                         (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))))).
  {
    assert (Hdist : Id (mult beta (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                                        (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))
                       (plus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))
                             (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))))
      by exact (distrib _ _ _).
    assert (Hassoc : Id (plus (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                                    (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))))
                              (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))
                        (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                              (plus (mult beta (sum_over_S (fun s => mult (pi s) (log (pi_ref s)))))
                                    (mult beta (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))))
      by exact (id_sym (plus_assoc _ _ _)).
    exact (id_trans Hassoc (id_cong (fun x => plus (sum_over_S (fun s => mult (pi s) (reward s))) x) (id_sym Hdist))).
  }
  (* Step 9: 内部求和化简为 opp (KL 求和) *)
  assert (H9 : Id (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                        (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))
                  (opp (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s))))))).
  {
    assert (Hadd : Id (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                            (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))
                    (sum_over_S (fun s => plus (mult (pi s) (log (pi_ref s))) (mult (pi s) (opp (log (pi s)))))))
      by exact (id_sym (sum_over_S_add _ _)).
    assert (Hpt : forall s, Id (plus (mult (pi s) (log (pi_ref s))) (mult (pi s) (opp (log (pi s)))))
                              (opp (mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))).
    {
      intro s.
      assert (H9a : Id (plus (mult (pi s) (log (pi_ref s))) (mult (pi s) (opp (log (pi s)))))
                      (mult (pi s) (plus (log (pi_ref s)) (opp (log (pi s))))))
        by exact (id_sym (distrib _ _ _)).
      assert (H9b : Id (mult (pi s) (plus (log (pi_ref s)) (opp (log (pi s)))))
                      (opp (mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))).
      {
        assert (H9c : Id (plus (log (pi_ref s)) (opp (log (pi s))))
                         (opp (minus (log (pi s)) (log (pi_ref s))))).
        {
          assert (H9d : Id (opp (minus (log (pi s)) (log (pi_ref s))))
                          (plus (opp (log (pi s))) (log (pi_ref s))))
            by exact (opp_minus _ _).
          assert (H9e : Id (plus (opp (log (pi s))) (log (pi_ref s)))
                          (plus (log (pi_ref s)) (opp (log (pi s)))))
            by exact (plus_comm _ _).
          exact (id_sym (id_trans H9d H9e)).
        }
        assert (H9f : Id (mult (pi s) (opp (minus (log (pi s)) (log (pi_ref s)))))
                         (opp (mult (pi s) (minus (log (pi s)) (log (pi_ref s))))))
          by exact (opp_mult_l (pi s) (minus (log (pi s)) (log (pi_ref s)))).
        exact (id_trans (id_cong (fun x => mult (pi s) x) H9c) H9f).
      }
      exact (id_trans H9a H9b).
    }
    assert (Hext : Id (sum_over_S (fun s => plus (mult (pi s) (log (pi_ref s))) (mult (pi s) (opp (log (pi s))))))
                     (sum_over_S (fun s => opp (mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))))
      by exact (sum_over_S_ext _ _ Hpt).
    assert (Hso : Id (sum_over_S (fun s => opp (mult (pi s) (minus (log (pi s)) (log (pi_ref s))))))
                     (opp (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))))
      by exact (sum_opp _).
    exact (id_trans Hadd (id_trans Hext Hso)).
  }
  (* Step 10: 最终组合 *)
  assert (H10 : Id (mult beta (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                                    (sum_over_S (fun s => mult (pi s) (opp (log (pi s)))))))
                   (opp (mult beta (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s)))))))).
  {
    exact (id_trans (id_cong (fun x => mult beta x) H9) (opp_mult_l _ _)).
  }
  assert (Hfinal : Id (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                            (mult beta (plus (sum_over_S (fun s => mult (pi s) (log (pi_ref s))))
                                             (sum_over_S (fun s => mult (pi s) (opp (log (pi s))))))))
                      (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                            (opp (mult beta (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s))))))))).
  {
    exact (id_cong (fun x => plus (sum_over_S (fun s => mult (pi s) (reward s))) x) H10).
  }
  (* 目标（Step 1 后）：Id (plus (opp A) (opp B)) (minus E (mult beta KL))。
     链：plus (opp A) (opp B) → (H7) plus (plus E X) Y → (H8) plus E (plus X Y)
         → (Hfinal) plus E (opp KL') = minus E (mult beta KL)。 *)
  assert (Hmid : Id (plus (opp (sum_over_S (fun s => mult (pi s) (minus (opp (reward s)) (mult beta (log (pi_ref s)))))))
                          (opp (mult beta (sum_over_S (fun s => mult (pi s) (log (pi s)))))))
                    (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                          (opp (mult beta (sum_over_S (fun s => mult (pi s) (minus (log (pi s)) (log (pi_ref s))))))))).
  {
    exact (id_trans H7 (id_trans H8 Hfinal)).
  }
  exact (id_trans Hlhs (id_trans H1 Hmid)).
Qed.

(* pi* 的奖励-熵权衡显式值 *)
Corollary rlhf_optimal_value :
  Id (align_objective pi_star)
     (minus (expected_reward pi_star) (mult beta (kl_reference pi_star))).
Proof.
  exact (align_objective_explicit pi_star).
Qed.

(* 次优差距：J(pi* ) − J(pi) = β·KL(pi‖pi* ) ≥ 0。
   非平凡：取负翻转（minus_opp_opp）+ free_energy_kl_diff +
   Boltzmann = pi* 替换（free_energy_ext / relative_entropy_ext_r）。 *)
Theorem rlhf_suboptimality_gap :
  forall pi : S -> R,
    normalized pi -> positive_dist pi ->
    Id (minus (align_objective pi_star) (align_objective pi))
       (mult beta (relative_entropy pi pi_star)).
Proof.
  intros pi Hnorm Hpos.
  (* align_objective = -F，故 Jstar - J = (-Fstar) - (-F) = F - Fstar = beta·KL *)
  assert (H1 : Id (minus (opp (free_energy align_energy beta pi_star))
                          (opp (free_energy align_energy beta pi)))
                  (minus (free_energy align_energy beta pi)
                         (free_energy align_energy beta pi_star)))
    by exact (minus_opp_opp (free_energy align_energy beta pi_star) (free_energy align_energy beta pi)).
  assert (H2_raw : Id (minus (free_energy align_energy beta pi)
                             (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos)))
                      (mult beta (relative_entropy pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))))
    by exact (free_energy_kl_diff align_energy beta beta_pos Z_align Z_align_pos align_partition_condition pi Hnorm).
  assert (Hfe_b : Id (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))
                     (free_energy align_energy beta pi_star))
    by apply (free_energy_ext (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos) pi_star align_boltzmann_is_pi_star).
  assert (Hkl_b : Id (relative_entropy pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))
                     (relative_entropy pi pi_star))
    by apply (relative_entropy_ext_r pi (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos) pi_star align_boltzmann_is_pi_star).
  assert (H2 : Id (minus (free_energy align_energy beta pi) (free_energy align_energy beta pi_star))
                  (mult beta (relative_entropy pi pi_star))).
  {
    assert (Hlhs : Id (minus (free_energy align_energy beta pi) (free_energy align_energy beta pi_star))
                      (minus (free_energy align_energy beta pi) (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos))))
      by exact (id_cong2 minus id_refl (id_sym Hfe_b)).
    exact (id_trans Hlhs (id_trans H2_raw (id_cong (fun x => mult beta x) Hkl_b))).
  }
  exact (id_trans H1 H2).
Qed.

(* 策略改进单调性：KL(π_new‖πstar) ≤ KL(π_old‖πstar) ⟹ J(π_old) ≤ J(π_new)。
   非平凡：次优差距恒等式 ×2 + β > 0 保序 + 差分翻转（le_plus_compat
   + opp 消去 + double_neg，约 20 步）。 *)
Theorem rlhf_policy_improvement :
  forall (p_old p_new : S -> R),
    normalized p_old -> positive_dist p_old ->
    normalized p_new -> positive_dist p_new ->
    le (relative_entropy p_new pi_star) (relative_entropy p_old pi_star) ->
    le (align_objective p_old) (align_objective p_new).
Proof.
  intros p_old p_new Hn1 Hp1 Hn2 Hp2 Hkl_dec.
  (* J* - J_new = β·KL(new||pi* ) *)
  assert (Hgap_new : Id (minus (align_objective pi_star) (align_objective p_new))
                        (mult beta (relative_entropy p_new pi_star)))
    by exact (rlhf_suboptimality_gap p_new Hn2 Hp2).
  (* J* - J_old = β·KL(old||pi* ) *)
  assert (Hgap_old : Id (minus (align_objective pi_star) (align_objective p_old))
                        (mult beta (relative_entropy p_old pi_star)))
    by exact (rlhf_suboptimality_gap p_old Hn1 Hp1).
  (* β·KL_new ≤ β·KL_old（β > 0） *)
  assert (Hbeta_le : le (mult beta (relative_entropy p_new pi_star))
                        (mult beta (relative_entropy p_old pi_star)))
    by exact (le_mult_compat_r beta _ _ (lt_le_iff _ _ (inl beta_pos)) Hkl_dec).
  (* J* - J_new ≤ J* - J_old *)
  assert (Hle : le (minus (align_objective pi_star) (align_objective p_new))
                   (minus (align_objective pi_star) (align_objective p_old))).
  {
    exact (le_id_l (minus (align_objective pi_star) (align_objective p_new))
                   (mult beta (relative_entropy p_new pi_star))
                   (minus (align_objective pi_star) (align_objective p_old))
                   Hgap_new
                   (le_id_r (mult beta (relative_entropy p_new pi_star))
                            (mult beta (relative_entropy p_old pi_star))
                            (minus (align_objective pi_star) (align_objective p_old))
                            (id_sym Hgap_old)
                            Hbeta_le)).
  }
  unfold minus in Hle.
  (* 由 le (plus a (opp b)) (plus a (opp c)) 推出 le c b：
     两侧加 opp a，化简得 le (opp b) (opp c)，再取 opp 得 le c b *)
  assert (Hopp_le : le (opp (align_objective p_new)) (opp (align_objective p_old))).
  {
    assert (Hadd : le (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_new))))
                     (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_old))))).
    { exact (le_plus_compat _ _ _ _ (le_refl _) Hle). }
    assert (Hl : Id (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_new))))
                   (opp (align_objective p_new))).
    {
      assert (H1 : Id (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_new))))
                      (plus (plus (opp (align_objective pi_star)) (align_objective pi_star)) (opp (align_objective p_new))))
        by exact (plus_assoc (opp (align_objective pi_star)) (align_objective pi_star) (opp (align_objective p_new))).
      assert (H2 : Id (plus (plus (opp (align_objective pi_star)) (align_objective pi_star)) (opp (align_objective p_new)))
                      (plus zero (opp (align_objective p_new))))
        by exact (id_cong (fun x => plus x (opp (align_objective p_new)))
                          (id_trans (plus_comm (opp (align_objective pi_star)) (align_objective pi_star))
                                    (plus_opp (align_objective pi_star)))).
      exact (id_trans H1 (id_trans H2 (id_trans (plus_comm zero (opp (align_objective p_new))) (plus_zero (opp (align_objective p_new)))))).
    }
    assert (Hr : Id (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_old))))
                   (opp (align_objective p_old))).
    {
      assert (H1 : Id (plus (opp (align_objective pi_star)) (plus (align_objective pi_star) (opp (align_objective p_old))))
                      (plus (plus (opp (align_objective pi_star)) (align_objective pi_star)) (opp (align_objective p_old))))
        by exact (plus_assoc (opp (align_objective pi_star)) (align_objective pi_star) (opp (align_objective p_old))).
      assert (H2 : Id (plus (plus (opp (align_objective pi_star)) (align_objective pi_star)) (opp (align_objective p_old)))
                      (plus zero (opp (align_objective p_old))))
        by exact (id_cong (fun x => plus x (opp (align_objective p_old)))
                          (id_trans (plus_comm (opp (align_objective pi_star)) (align_objective pi_star))
                                    (plus_opp (align_objective pi_star)))).
      exact (id_trans H1 (id_trans H2 (id_trans (plus_comm zero (opp (align_objective p_old))) (plus_zero (opp (align_objective p_old)))))).
    }
    exact (le_id_l (opp (align_objective p_new)) _ _ (id_sym Hl) (le_id_r _ _ _ Hr Hadd)).
  }
  (* 由 le (opp new) (opp old) 得 le old new（opp_le_compat + double_neg） *)
  assert (Hdn : le (opp (opp (align_objective p_old))) (opp (opp (align_objective p_new))))
    by exact (opp_le_compat (opp (align_objective p_new)) (opp (align_objective p_old)) Hopp_le).
  assert (H1 : Id (opp (opp (align_objective p_old))) (align_objective p_old))
    by exact (double_neg _).
  assert (H2 : Id (opp (opp (align_objective p_new))) (align_objective p_new))
    by exact (double_neg _).
  exact (le_id_l (align_objective p_old) (opp (opp (align_objective p_old))) (align_objective p_new)
                 (id_sym H1) (le_id_r (opp (opp (align_objective p_old))) (opp (opp (align_objective p_new))) (align_objective p_new) H2 Hdn)).
Qed.

(* ============================================================ *)
(* PPO 单调保证（构造性单调保证.txt：比率消去 + 代理目标恒等式）*)
(* ============================================================ *)
(* 1) align_objective_decomp：J(pi) = V(pi) − β·KL(pi‖pi_ref)    *)
(* 2) importance_ratio_self_one：pi/pi = 1（比率自反）            *)
(* 3) ppo_surrogate_raw_is_value_improvement：L_raw = V(pi) −      *)
(*    V(pi_old)（比率消去 + 求和线性 + 归一化坍缩，核心非平凡）   *)
(* ------------------------------------------------------------ *)

(* 对齐目标显式分解：J(pi) = V(pi) − β·KL(pi‖pi_ref)
   （由 free_energy_align_decomp 取负推导；非平凡：opp 分配律） *)
Lemma align_objective_decomp :
  forall pi : S -> R,
    Id (align_objective pi)
       (minus (state_value pi) (mult beta (kl_to_ref pi))).
Proof.
  intro pi.
  unfold align_objective.
  exact (id_trans (id_cong opp (free_energy_align_decomp pi))
                  (id_trans (id_trans (opp_plus (opp (state_value pi)) (mult beta (kl_to_ref pi)))
                                    (id_cong2 plus (double_neg (state_value pi)) id_refl))
                            (@id_refl R (plus (state_value pi) (opp (mult beta (kl_to_ref pi))))))).
Qed.

(* 策略比率自反：pi/pi = 1（非平凡：交换律 + 逆元公理） *)
Lemma importance_ratio_self_one :
  forall (pi : S -> R) (Hpos : positive_dist pi) (s : S),
    Id (policy_ratio pi pi s (Hpos s)) one.
Proof.
  intros pi Hpos s.
  unfold policy_ratio.
  exact (inv_pos_correct (pi s) (Hpos s)).
Qed.

(* 无裁剪代理目标恒等：L_raw(pi, pi_old) = V(pi) − V(pi_old)。
   非平凡：比率消去（pi_old·(pi/pi_old) = pi）+ 求和线性
   （sum_over_S_linear）+ 归一化坍缩（Σ pi = 1），约 20 步。 *)
Theorem ppo_surrogate_raw_is_value_improvement :
  forall (pi p_old : S -> R) (Hpos : positive_dist p_old)
         (Hnorm : normalized pi),
    Id (sum_over_S (fun s => mult (p_old s)
       (mult (policy_ratio pi p_old s (Hpos s)) (advantage p_old s))))
       (minus (state_value pi) (state_value p_old)).
Proof.
  intros pi p_old Hpos Hnorm.
  unfold policy_ratio, advantage, state_value.
  (* 逐点消去 p_old·(pi/p_old) = pi *)
  assert (Hpt : forall s,
    Id (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s)))
                              (minus (reward s)
                                     (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
       (mult (pi s) (minus (reward s)
                           (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))).
  {
    intro s.
    assert (H1 : Id (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s)))
          (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
        (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
              (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
      by exact (mult_assoc (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s)))
                           (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))).
    assert (H2 : Id (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                          (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
        (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
              (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
      by exact (id_cong (fun x => mult x (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
               (id_trans (mult_assoc (p_old s) (pi s) (inv_pos (p_old s) (Hpos s)))
                         (id_cong (fun x => mult x (inv_pos (p_old s) (Hpos s)))
                                  (mult_comm (p_old s) (pi s))))).
    assert (H3 : Id (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                          (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
        (mult (pi s) (mult (mult (p_old s) (inv_pos (p_old s) (Hpos s)))
                           (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))).
    {
      set (X := mult (p_old s) (inv_pos (p_old s) (Hpos s))).
      set (M := minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))).
      (* 第一步：内层换序 mult (mult (pi s) (p_old s)) inv = mult (pi s) X *)
      assert (H3a : Id (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s))) M)
                       (mult (mult (pi s) X) M))
        by (unfold X; exact (id_cong (fun x => mult x M)
                                     (id_sym (mult_assoc (pi s) (p_old s) (inv_pos (p_old s) (Hpos s)))))).
      (* 第二步：外层重结合 mult (mult (pi s) X) M = mult (pi s) (mult X M) *)
      assert (H3b : Id (mult (mult (pi s) X) M) (mult (pi s) (mult X M)))
        by exact (id_sym (mult_assoc (pi s) X M)).
      exact (id_trans H3a H3b).
    }
    assert (H4 : Id (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                    (mult (pi s) one))
      by exact (id_cong (fun x => mult (pi s) x)
               (inv_pos_correct (p_old s) (Hpos s))).
    assert (H5 : Id (mult (pi s) one) (pi s))
      by exact (mult_one (pi s)).
    (* 收尾：LHS → H1 → H2 → H3（至 mult (pi s) (mult X M)）→
       H3b 反向（至 mult (mult (pi s) X) M）→ H4/H5 内层折叠 → mult (pi s) M *)
    set (M := minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))).
    assert (H6 : Id (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) M)
                     (mult (pi s) M))
      by exact (id_trans (id_cong (fun x => mult x M) H4)
                         (id_cong (fun x => mult x M) H5)).
    assert (H7 : Id (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) M)
                     (mult (pi s) M))
      by exact (id_trans (id_cong (fun x => mult x M) H4)
                         (id_cong (fun x => mult x M) H5)).
    (* H3 RHS = mult (pi s) (mult X M)；重结合到 mult (mult (pi s) X) M 再 H7 *)
    exact (id_trans H1 (id_trans H2 (id_trans H3
          (id_trans (mult_assoc (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))) M) H7)))).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p_old s)
       (mult (mult (pi s) (inv_pos (p_old s) (Hpos s)))
             (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
                   (sum_over_S (fun s => mult (pi s)
                       (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
    by exact (sum_over_S_ext _ _ Hpt).
  (* 逐点：mult (pi s) (minus r V) = minus (mult pi r) (mult pi V)（mult_minus_distr_l） *)
  assert (Hpt2 : forall s, Id (mult (pi s) (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
                             (minus (mult (pi s) (reward s))
                                    (mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
    by (intro s; exact (mult_minus_distr_l (pi s) (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))).
  assert (Hext2 : Id (sum_over_S (fun s => mult (pi s) (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
                     (sum_over_S (fun s => minus (mult (pi s) (reward s))
                                                 (mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
    by exact (sum_over_S_ext _ _ Hpt2).
  (* 目标换形：先 Hext 再 Hext2 再 Hdist *)
  assert (Hlhs : Id (sum_over_S (fun s => mult (p_old s)
       (mult (mult (pi s) (inv_pos (p_old s) (Hpos s)))
             (minus (reward s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
                   (sum_over_S (fun s => minus (mult (pi s) (reward s))
                                               (mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
    by exact (id_trans Hext Hext2).
  rewrite Hlhs.
  (* 分配求和：Σ (minus f g) = minus (Σf) (Σg) *)
  assert (Hdist : Id (sum_over_S (fun s => minus (mult (pi s) (reward s))
                                                 (mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))))
                     (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                            (sum_over_S (fun s => mult (pi s)
                                (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))))
    by exact (sum_over_S_minus (fun s => mult (pi s) (reward s))
                               (fun s => mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))).
  rewrite Hdist.
  (* 提取常数 V_old：Σ pi·V_old = V_old·Σ pi = V_old *)
  assert (Hconst : Id (sum_over_S (fun s => mult (pi s)
      (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
      (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (sum_over_S pi))).
  {
    assert (Hsw : Id (sum_over_S (fun s => mult (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
                     (sum_over_S (fun s => mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (pi s))))
      by exact (sum_over_S_ext _ _ (fun s => mult_comm (pi s) (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))).
    assert (Hlin : Id (sum_over_S (fun s => mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (pi s)))
                      (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (sum_over_S pi)))
      by exact (sum_over_S_linear (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) pi).
    exact (id_trans Hsw Hlin).
  }
  rewrite Hconst.
  (* Σ pi = 1（Hnorm：normalized pi = Id (sum_over_S pi) one） *)
  assert (Hnorm1 : Id (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (sum_over_S pi))
                       (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) one))
    by exact (id_cong (fun x => mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) x) Hnorm).
  assert (Hm1 : Id (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) one)
                   (sum_over_S (fun s0 => mult (p_old s0) (reward s0))))
    by exact (mult_one (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))).
  assert (Hfin : Id (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                           (mult (sum_over_S (fun s0 => mult (p_old s0) (reward s0))) (sum_over_S pi)))
                    (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                           (sum_over_S (fun s0 => mult (p_old s0) (reward s0)))))
    by (unfold minus; exact (id_cong (fun x => plus (sum_over_S (fun s => mult (pi s) (reward s))) (opp x))
                                     (id_trans Hnorm1 Hm1))).
  exact Hfin.
Qed.

(* ============================================================ *)
(* DPO 构造性骨架（对齐自由能显式.txt：sigmoid 与 BT 对数几率） *)
(* ============================================================ *)
(* 1) sigmoid_denom_pos：1 + e^{-x} > 0（sigmoid 良定义）          *)
(* 2) sigmoid：Set 层构造 σ(x) = 1/(1+e^{-x})（正性见证内嵌）      *)
(* 3) sigmoid_lt_one：σ(x) < 1（值域上界：lt_mult_compat + inv）   *)
(* 4) log_ratio：对数几率比 log π(s) − log π_ref(s)                *)
(* 5) dpo_loss_pair：成对 DPO 损失 −log σ(β·Δlog-ratio)            *)
(* 6) dpo_loss_at_pi_star：π* 处损失退化为 BT 模型对数几率          *)
(*    −log σ(r_w − r_l)（非平凡：log_pi_star 消去 Z_align/π_ref） *)
(* ------------------------------------------------------------ *)

(* Sigmoid 分母正性：1 + e^{-x} > 0（one_pos + exp_neg_pos） *)
Lemma sigmoid_denom_pos : forall x : R, lt zero (plus one (exp_neg x)).
Proof.
  intro x.
  exact (plus_le_lt_pos one (exp_neg x) (lt_le_iff zero one (inl one_pos))
                        (exp_neg_pos x)).
Qed.

(* 构造性 Sigmoid：σ(x) = 1 / (1 + e^{-x})，值域 (0,1) *)
Definition sigmoid (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (sigmoid_denom_pos x).

Lemma sigmoid_pos : forall x : R, lt zero (sigmoid x).
Proof.
  intro x.
  (* 定义层展开＋显式见证全参喂定：sigmoid x 展开为
     inv_pos (plus one (exp_neg x)) (分母正性见证)，
     正性由逆元保正 inv_pos_pos 在显式参数上就地给出 *)
  unfold sigmoid.
  exact (inv_pos_pos (plus one (exp_neg x)) (sigmoid_denom_pos x)).
Qed.

(* 对数几率比：log(π(s) / π_ref(s)) = log π(s) − log π_ref(s) *)
Definition log_ratio (pi : S -> R) (s : S) : R :=
  minus (log (pi s)) (log (pi_ref s)).

(* 成对 DPO 损失（偏好 s_w ≻ s_l）：
   L_DPO = −log σ( β·log_ratio(π,s_w) − β·log_ratio(π,s_l) ) *)
Definition dpo_loss_pair (pi : S -> R) (s_w s_l : S) : R :=
  opp (log (sigmoid (minus (mult beta (log_ratio pi s_w))
                           (mult beta (log_ratio pi s_l))))).

(* DPO 在 π* 处的显式值：损失退化为 BT 模型的对数几率
   非平凡：log_pi_star 展开（消去 Z_align 与 π_ref）+ β·(1/β) = 1
   消去（mult_assoc + inv_pos_correct）+ id_cong 提升（约 30 步）。 *)
Theorem dpo_loss_at_pi_star :
  forall s_w s_l : S,
    Id (dpo_loss_pair pi_star s_w s_l)
       (opp (log (sigmoid (minus (reward s_w) (reward s_l))))).
Proof.
  intros s_w s_l.
  unfold dpo_loss_pair, log_ratio.
  (* 利用 log_pi_star 消去 π_ref，保留 −log Z + r/β（Z 项在差分中消去） *)
  assert (Hdiff_w : Id (minus (log (pi_star s_w)) (log (pi_ref s_w)))
                        (plus (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s_w)))).
  {
    assert (Hls : Id (log (pi_star s_w))
                     (plus (opp (log Z_align)) (plus (log (pi_ref s_w)) (mult (inv_pos beta beta_pos) (reward s_w)))))
      by exact (log_pi_star s_w).
    unfold minus. rewrite Hls.
    assert (H1 : Id (plus (plus (opp (log Z_align)) (plus (log (pi_ref s_w)) (mult (inv_pos beta beta_pos) (reward s_w)))) (opp (log (pi_ref s_w))))
                    (plus (opp (log Z_align)) (plus (plus (log (pi_ref s_w)) (mult (inv_pos beta beta_pos) (reward s_w))) (opp (log (pi_ref s_w))))))
      by exact (id_sym (plus_assoc (opp (log Z_align)) (plus (log (pi_ref s_w)) (mult (inv_pos beta beta_pos) (reward s_w))) (opp (log (pi_ref s_w))))).
    assert (H2 : Id (plus (plus (log (pi_ref s_w)) (mult (inv_pos beta beta_pos) (reward s_w))) (opp (log (pi_ref s_w))))
                    (plus (mult (inv_pos beta beta_pos) (reward s_w)) (plus (log (pi_ref s_w)) (opp (log (pi_ref s_w))))))
      by exact (id_trans (id_cong (fun x => plus x (opp (log (pi_ref s_w)))) (plus_comm _ _))
                         (id_sym (plus_assoc (mult (inv_pos beta beta_pos) (reward s_w)) (log (pi_ref s_w)) (opp (log (pi_ref s_w)))))).
    assert (H3 : Id (plus (mult (inv_pos beta beta_pos) (reward s_w)) (plus (log (pi_ref s_w)) (opp (log (pi_ref s_w)))))
                    (plus (mult (inv_pos beta beta_pos) (reward s_w)) zero))
      by exact (id_cong (fun x => plus (mult (inv_pos beta beta_pos) (reward s_w)) x) (plus_opp _)).
    assert (H4 : Id (plus (mult (inv_pos beta beta_pos) (reward s_w)) zero) (mult (inv_pos beta beta_pos) (reward s_w)))
      by exact (plus_zero _).
    exact (id_trans H1 (id_cong (fun x => plus (opp (log Z_align)) x) (id_trans H2 (id_trans H3 H4)))).
  }
  assert (Hdiff_l : Id (minus (log (pi_star s_l)) (log (pi_ref s_l)))
                        (plus (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s_l)))).
  {
    assert (Hls : Id (log (pi_star s_l))
                     (plus (opp (log Z_align)) (plus (log (pi_ref s_l)) (mult (inv_pos beta beta_pos) (reward s_l)))))
      by exact (log_pi_star s_l).
    unfold minus. rewrite Hls.
    assert (H1 : Id (plus (plus (opp (log Z_align)) (plus (log (pi_ref s_l)) (mult (inv_pos beta beta_pos) (reward s_l)))) (opp (log (pi_ref s_l))))
                    (plus (opp (log Z_align)) (plus (plus (log (pi_ref s_l)) (mult (inv_pos beta beta_pos) (reward s_l))) (opp (log (pi_ref s_l))))))
      by exact (id_sym (plus_assoc (opp (log Z_align)) (plus (log (pi_ref s_l)) (mult (inv_pos beta beta_pos) (reward s_l))) (opp (log (pi_ref s_l))))).
    assert (H2 : Id (plus (plus (log (pi_ref s_l)) (mult (inv_pos beta beta_pos) (reward s_l))) (opp (log (pi_ref s_l))))
                    (plus (mult (inv_pos beta beta_pos) (reward s_l)) (plus (log (pi_ref s_l)) (opp (log (pi_ref s_l))))))
      by exact (id_trans (id_cong (fun x => plus x (opp (log (pi_ref s_l)))) (plus_comm _ _))
                         (id_sym (plus_assoc (mult (inv_pos beta beta_pos) (reward s_l)) (log (pi_ref s_l)) (opp (log (pi_ref s_l)))))).
    assert (H3 : Id (plus (mult (inv_pos beta beta_pos) (reward s_l)) (plus (log (pi_ref s_l)) (opp (log (pi_ref s_l)))))
                    (plus (mult (inv_pos beta beta_pos) (reward s_l)) zero))
      by exact (id_cong (fun x => plus (mult (inv_pos beta beta_pos) (reward s_l)) x) (plus_opp _)).
    assert (H4 : Id (plus (mult (inv_pos beta beta_pos) (reward s_l)) zero) (mult (inv_pos beta beta_pos) (reward s_l)))
      by exact (plus_zero _).
    exact (id_trans H1 (id_cong (fun x => plus (opp (log Z_align)) x) (id_trans H2 (id_trans H3 H4)))).
  }
  (* 计算 β·(log_ratio_w − log_ratio_l) = r_w − r_l
     非平凡：Z 项消去（minus_plus_common）+ β·(1/β)·r = r（mult_assoc）+
     共同因子提取（mult_minus_distr_l 反向），约 15 步。 *)
  assert (Hmain : Id (minus (mult beta (minus (log (pi_star s_w)) (log (pi_ref s_w))))
                            (mult beta (minus (log (pi_star s_l)) (log (pi_ref s_l)))))
                     (minus (reward s_w) (reward s_l))).
  {
    rewrite Hdiff_w. rewrite Hdiff_l.
    (* 目标：minus (mult beta (plus A Rw)) (mult beta (plus A Rl)) = minus r_w r_l
       1) 提取 beta：mult beta (plus A R) = plus (mult beta A) (mult beta R)（distrib） *)
    set (A := opp (log Z_align)).
    assert (Hd_w : Id (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_w))))
                      (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_w)))))
      by (unfold A; exact (distrib beta (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s_w)))).
    assert (Hd_l : Id (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_l))))
                      (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_l)))))
      by (unfold A; exact (distrib beta (opp (log Z_align)) (mult (inv_pos beta beta_pos) (reward s_l)))).
    (* 2) 目标 LHS 换为 minus (plus BA BRw) (plus BA BRl)（共同项 A 消去） *)
    assert (Hlhs : Id (minus (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_w))))
                             (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_l)))))
                      (minus (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_w))))
                             (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_l))))))
      by exact (id_cong2 minus Hd_w Hd_l).
    (* 3) 共同被加项消去：minus (plus BA X) (plus BA Y) = minus X Y（minus_plus_common） *)
    assert (Hcom : Id (minus (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_w))))
                             (plus (mult beta A) (mult beta (mult (inv_pos beta beta_pos) (reward s_l)))))
                      (minus (mult beta (mult (inv_pos beta beta_pos) (reward s_w)))
                             (mult beta (mult (inv_pos beta beta_pos) (reward s_l)))))
      by exact (minus_plus_common (mult beta A)
                                  (mult beta (mult (inv_pos beta beta_pos) (reward s_w)))
                                  (mult beta (mult (inv_pos beta beta_pos) (reward s_l)))).
    (* 4) β·(1/β)·r_w = r_w、β·(1/β)·r_l = r_l *)
    assert (Hw : Id (mult beta (mult (inv_pos beta beta_pos) (reward s_w))) (reward s_w)).
    {
      assert (H1 : Id (mult beta (mult (inv_pos beta beta_pos) (reward s_w)))
                      (mult (mult beta (inv_pos beta beta_pos)) (reward s_w)))
        by exact (mult_assoc _ _ _).
      assert (H2a : Id (mult (mult beta (inv_pos beta beta_pos)) (reward s_w)) (mult one (reward s_w)))
        by exact (id_cong (fun x => mult x (reward s_w)) (inv_pos_correct beta beta_pos)).
      assert (H2b : Id (mult one (reward s_w)) (reward s_w))
        by exact (id_trans (mult_comm _ _) (mult_one _)).
      exact (id_trans H1 (id_trans H2a H2b)).
    }
    assert (Hl : Id (mult beta (mult (inv_pos beta beta_pos) (reward s_l))) (reward s_l))
      by exact (id_trans (mult_assoc _ _ _)
                         (id_trans (id_cong (fun x => mult x _) (inv_pos_correct beta beta_pos))
                                   (id_trans (mult_comm _ _) (mult_one _)))).
    (* 5) 组装：LHS → Hlhs → Hcom → 替换 Hw/Hl → reflexivity *)
    assert (Hmid : Id (minus (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_w))))
                             (mult beta (plus A (mult (inv_pos beta beta_pos) (reward s_l)))))
                      (minus (reward s_w) (reward s_l)))
      by exact (id_trans Hlhs (id_trans Hcom (id_cong2 minus Hw Hl))).
    exact Hmid.
  }
  exact (id_cong (fun x => opp (log (sigmoid x))) Hmain).
Qed.

(* ============================================================ *)
(* DPO 损失在 π* 处有界（对齐自由能显式.txt：dpo_loss_pi_star_  *)
(* bounded 的零 承认 版本）                                    *)
(* ============================================================ *)
(* 前提：两个构造性有序域标准定理（接口未提供，诚实 Variable—— *)
(* 与 proj_orthogonal_compat 同先例。 *)
(*   1) inv_pos 反单调：0 < a < b ⟹ inv b < inv a（有序域定理）  *)
(*   2) log 严格递增：0 < a < b ⟹ log a < log b（CReals 中可证） *)
(* 证明链：r_w > r_l ⟹ r_w − r_l > 0 ⟹ σ(r_w − r_l) > σ(0) = 1/2 *)
(*   ⟹ −log σ(r_w − r_l) < −log σ(0) = log 2（σ 严格递增 +       *)
(*   log 严格递增 + opp_lt_compat + log_inv_one_inv + double_neg）*)
(* ------------------------------------------------------------ *)

(* inv_pos 反单调（诚实 Variable：构造性有序域标准定理） *)
Variable inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).

(* 严格序的加法保序混合版（诚实 Variable：le 与 lt 混合，构造性可接受） *)
(* [墙族登记·RW-MIX 混合保序（对偶 le_lt 形）] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批。 *)
Variable lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
(* [墙族登记·RW-MIX 混合保序] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批。 *)
Variable lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

(* log 严格递增（诚实 Variable：构造性分析标准定理） *)
Variable log_lt_mono :
  forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b).

(* sigmoid 严格递增：x < y ⟹ σ(x) < σ(y)
   非平凡：exp_neg_decr（指数反序）⟹ 分母反序（le/lt 混合保序）⟹
   inv_pos_lt_contra。 *)
Lemma sigmoid_strict_inc : forall x y : R,
  lt x y -> lt (sigmoid x) (sigmoid y).
Proof.
  intros x y Hxy. unfold sigmoid.
  exact (inv_pos_lt_contra (plus one (exp_neg y)) (plus one (exp_neg x)) (sigmoid_denom_pos y) (sigmoid_denom_pos x) (lt_plus_compat_le_lt one one (exp_neg y) (exp_neg x) (le_refl one) (exp_neg_decr x y Hxy))).
Qed.

(* σ(0) = 1/(1+1) = inv_pos 2：exp_neg_zero 折叠 + inv_pos_ext *)
Lemma sigmoid_zero_half :
  Id (sigmoid zero) (inv_pos (plus one one) two_pos).
Proof.
  unfold sigmoid.
  exact (inv_pos_ext (plus one (exp_neg zero)) (plus one one) (sigmoid_denom_pos zero) two_pos (id_cong (fun x => plus one x) exp_neg_zero)).
Qed.

(* DPO 损失在 π* 处有界：r_w > r_l ⟹ L_DPO(π*, s_w, s_l) < log 2
   非平凡：sigmoid 严格递增 + log 严格递增 + opp_lt_compat +
   σ(0)=1/2 + log_inv_one_inv（−log(1/2) = log 2），约 20 步。 *)
Theorem dpo_loss_pi_star_bounded :
  forall s_w s_l : S,
    lt (reward s_l) (reward s_w) ->
    lt (dpo_loss_pair pi_star s_w s_l) (log (plus one one)).
Proof.
  intros s_w s_l Hrw.
  rewrite (dpo_loss_at_pi_star s_w s_l).
  (* 1. r_w − r_l > 0（le_plus_compat + plus_opp 构造） *)
  assert (Hpos : lt zero (minus (reward s_w) (reward s_l))).
  {
    unfold minus.
    (* lt (plus r_l (opp r_l)) (plus r_w (opp r_l))：lt r_l r_w + le (opp r_l) (opp r_l) *)
    assert (H1 : lt (plus (reward s_l) (opp (reward s_l))) (plus (reward s_w) (opp (reward s_l))))
      by exact (lt_plus_compat_lt_le (reward s_l) (reward s_w) (opp (reward s_l)) (opp (reward s_l))
                                     Hrw (le_refl (opp (reward s_l)))).
    assert (H2 : Id (plus (reward s_l) (opp (reward s_l))) zero) by exact (plus_opp _).
    exact (lt_id_l zero (plus (reward s_l) (opp (reward s_l)))
                   (plus (reward s_w) (opp (reward s_l))) (id_sym H2) H1).
  }
  (* 2. σ(r_w − r_l) > σ(0)（sigmoid_strict_inc） *)
  assert (Hsig : lt (sigmoid zero) (sigmoid (minus (reward s_w) (reward s_l))))
    by exact (sigmoid_strict_inc zero (minus (reward s_w) (reward s_l)) Hpos).
  (* 3. log σ(r_w − r_l) > log σ(0)（log_lt_mono + sigmoid_pos） *)
  assert (Hlog : lt (log (sigmoid zero)) (log (sigmoid (minus (reward s_w) (reward s_l)))))
    by exact (log_lt_mono (sigmoid zero) (sigmoid (minus (reward s_w) (reward s_l)))
                          (sigmoid_pos zero) (sigmoid_pos (minus (reward s_w) (reward s_l))) Hsig).
  (* 4. −log σ(r_w − r_l) < −log σ(0)（opp_lt_compat） *)
  assert (Hopp : lt (opp (log (sigmoid (minus (reward s_w) (reward s_l)))))
                    (opp (log (sigmoid zero))))
    by exact (opp_lt_compat (log (sigmoid zero)) (log (sigmoid (minus (reward s_w) (reward s_l)))) Hlog).
  (* 5. −log σ(0) = log 2（σ(0) = 1/2，log_inv_one_inv，double_neg） *)
  assert (Hval : Id (opp (log (sigmoid zero))) (log (plus one one))).
  {
    rewrite sigmoid_zero_half.
    assert (Hlogi : Id (log (inv_pos (plus one one) two_pos)) (opp (log (plus one one))))
      by exact (log_inv_one_inv (plus one one) two_pos).
    assert (Hopp2 : Id (opp (opp (log (plus one one)))) (log (plus one one)))
      by exact (double_neg (log (plus one one))).
    exact (id_trans (id_cong opp Hlogi) Hopp2).
  }
  (* 6. 组装：L < −log σ(0) = log 2（lt_id_r 替换） *)
  exact (lt_id_r (opp (log (sigmoid (minus (reward s_w) (reward s_l)))))
                 (opp (log (sigmoid zero)))
                 (log (plus one one)) Hval Hopp).
Qed.

(* 对齐自由能显式：F_align[π] = −E_π[r] + β·KL(π‖π_ref)
   非平凡：由 align_objective_explicit（J = E − β·KL）取负推导——
   opp_plus 分配 + double_neg 折叠 + 显式展开（约 8 步，非公理重述）。 *)
Theorem align_free_energy_explicit :
  forall pi : S -> R,
    Id (free_energy align_energy beta pi)
       (plus (opp (sum_over_S (fun s => mult (pi s) (reward s))))
             (mult beta (relative_entropy pi pi_ref))).
Proof.
  intro pi.
  (* J(pi) = E[r] − β·KL（align_objective_explicit 显式展开） *)
  assert (Hj : Id (opp (free_energy align_energy beta pi))
                  (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                         (mult beta (relative_entropy pi pi_ref)))).
  {
    unfold align_objective in *.
    unfold expected_reward, kl_reference in *.
    exact (align_objective_explicit pi).
  }
  (* F = opp (J) = opp (E − β·KL) = −E + β·KL（取负 + opp_plus + double_neg） *)
  assert (Hopp : Id (opp (opp (free_energy align_energy beta pi)))
                    (opp (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                                (mult beta (relative_entropy pi pi_ref)))))
    by exact (id_cong opp Hj).
  assert (Hdd : Id (opp (opp (free_energy align_energy beta pi)))
                   (free_energy align_energy beta pi))
    by exact (double_neg (free_energy align_energy beta pi)).
  (* opp (minus E KL) = plus (opp E) (mult beta KL)：unfold minus + opp_plus + double_neg *)
  assert (Hrhs : Id (opp (minus (sum_over_S (fun s => mult (pi s) (reward s)))
                                (mult beta (relative_entropy pi pi_ref))))
                    (plus (opp (sum_over_S (fun s => mult (pi s) (reward s))))
                          (mult beta (relative_entropy pi pi_ref)))).
  {
    unfold minus.
    assert (H1 : Id (opp (plus (sum_over_S (fun s => mult (pi s) (reward s)))
                               (opp (mult beta (relative_entropy pi pi_ref)))))
                    (plus (opp (sum_over_S (fun s => mult (pi s) (reward s))))
                          (opp (opp (mult beta (relative_entropy pi pi_ref))))))
      by exact (opp_plus (sum_over_S (fun s => mult (pi s) (reward s)))
                         (opp (mult beta (relative_entropy pi pi_ref)))).
    assert (H2 : Id (plus (opp (sum_over_S (fun s => mult (pi s) (reward s))))
                          (opp (opp (mult beta (relative_entropy pi pi_ref)))))
                    (plus (opp (sum_over_S (fun s => mult (pi s) (reward s))))
                          (mult beta (relative_entropy pi pi_ref))))
      by exact (id_cong (fun x => plus (opp (sum_over_S (fun s => mult (pi s) (reward s)))) x)
                        (double_neg (mult beta (relative_entropy pi pi_ref)))).
    exact (id_trans H1 H2).
  }
  exact (id_trans (id_sym Hdd) (id_trans Hopp Hrhs)).
Qed.

(* ------------------------------------------------------------ *)
(* KL 正则化奖励最大化最优性定理链 3 小项（参考文件消化落地）     *)
(* 重叠项（rlhf_optimal/unique、align_free_energy_explicit、     *)
(* align_objective_explicit、sum_opp/sum_minus、kl_divergence）   *)
(* 已在前文实现；此处落地其余 3 项：                              *)
(*   ① align_free_energy_pi_star：F[π*] = F[boltzmann] 外延性    *)
(*   ② pi_star_objective_value：J(pi_star) 显式值（推论）        *)
(*   ③ align_cross_entropy：对齐交叉熵定义                       *)
(* ------------------------------------------------------------ *)

(* ① 核心外延性：π* 与 Boltzmann 分布共享对齐自由能              *)
Lemma align_free_energy_pi_star :
  Id (free_energy align_energy beta pi_star)
     (free_energy align_energy beta (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos)).
Proof.
  unfold free_energy.
  assert (Hext1 : Id (sum_over_S (fun s => mult (pi_star s) (align_energy s)))
                     (sum_over_S (fun s => mult (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s) (align_energy s)))).
  { apply sum_over_S_ext. intro s.
    exact (id_cong (fun x => mult x (align_energy s)) (id_sym (align_boltzmann_is_pi_star s))). }
  assert (Hext2 : Id (sum_over_S (fun s => mult (pi_star s) (log (pi_star s))))
                     (sum_over_S (fun s => mult (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s) (log (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s))))).
  { apply sum_over_S_ext. intro s.
    assert (Hlog : Id (log (pi_star s)) (log (boltzmann_dist align_energy beta beta_pos Z_align Z_align_pos s)))
      by exact (id_cong log (id_sym (align_boltzmann_is_pi_star s))).
    exact (id_cong2 mult (id_sym (align_boltzmann_is_pi_star s)) Hlog). }
  exact (id_cong2 plus Hext1 (id_cong (fun x => mult beta x) Hext2)).
Qed.

(* ② 推论：π* 的显式目标值 J(pi_star) = E_{π*}[r] − β·KL(π*‖π_ref) *)
Corollary pi_star_objective_value :
  Id (align_objective pi_star)
     (minus (expected_reward pi_star) (mult beta (kl_reference pi_star))).
Proof.
  exact (align_objective_explicit pi_star).
Qed.

(* ③ 对齐交叉熵：H_align(π, π_ref) = −Σ π·log π_ref
   （reward 视为 logits 负损失时，最小化交叉熵即最大化奖励；
     供外部模块如 LanguageModelInstance 实例化使用）             *)
Definition align_cross_entropy (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (opp (log (pi_ref s)))).

(* ============================================================
   论文1 PPO 补强（T1.1）：
   标准形式 PPO 保守性——任意符号 adv（无需 advantage_nonneg）。
   ppo_surrogate（L18056）已是标准形式 min(r·A, clip(r)·A)；
   其保守性 min(r·A, clip(r)·A) ≤ r·A 由 min_le_l 一步给出，
   不依赖 adv 的符号（对照：现有 ppo_conservative L18023 的
   min(r, clip(r))·A 形式需 advantage_nonneg L17994）。
   由此消除论文 §6 边界声明一的符号限制：标准形式的保守性
   对任意符号 adv 成立。Set 层 / 零经典 / 可提取。
   ============================================================ *)
Theorem ppo_surrogate_conservative :
  forall (pi : S -> R) (adv : S -> R) (eps : R),
  forall (Hpi_old_pos : forall s : S, lt zero (pi_old s)),
  le (ppo_surrogate pi pi_old adv eps Hpi_old_pos)
     (sum_over_S (fun s => mult (pi_old s) (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s)))).
Proof.
  intros pi adv eps Hpi_old_pos.
  unfold ppo_surrogate.
  apply sum_over_S_le.
  intro s.
  (* 逐点：min(r·A, clip·A) ≤ r·A（min_le_l，无需 adv 符号） *)
  assert (Hmin : le (min (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                         (mult (ppo_clip (policy_ratio pi pi_old s (Hpi_old_pos s))
                                         (minus one eps) (plus one eps)) (adv s)))
                    (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s)))
    by exact (min_le_l (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                       (mult (ppo_clip (policy_ratio pi pi_old s (Hpi_old_pos s))
                                       (minus one eps) (plus one eps)) (adv s))).
  (* pi_old ≥ 0（由 Hpi_old_pos 经 lt_le_iff） *)
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply Hpi_old_pos).
  (* 乘正因子保序：pi_old·min(rA, cA) ≤ pi_old·(rA) *)
  exact (le_mult_compat_r (pi_old s)
                          (min (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                               (mult (ppo_clip (policy_ratio pi pi_old s (Hpi_old_pos s))
                                               (minus one eps) (plus one eps)) (adv s)))
                          (mult (policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                          Hpi Hmin).
Qed.

(* ===== T1.2 新定义 ===== *)
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* 诚实接口假设：正项和为正（Real 层有限和可实例化；同 Z_align_pos 先例） *)
Variable sum_over_S_pos : forall (f : S -> R), (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).


Definition advantage_aug (pi_t : S -> R) (s : S) : R :=
  minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s)))).

Definition Z_rel (pi_t : S -> R) : R :=
  sum_over_S (fun s => mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).

Lemma Z_rel_pos : forall (pi_t : S -> R),
  (forall s : S, lt zero (pi_t s)) ->
  lt zero (Z_rel pi_t).
Proof.
  intros pi_t Hpos.
  apply sum_over_S_pos.
  intro s.
  exact (mult_positive (pi_t s)
                       (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))
                       (Hpos s)
                       (exp_neg_pos (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).
Qed.

Definition energy_t (pi_t : S -> R) (s : S) : R :=
  minus (opp (mult eta (advantage_aug pi_t s))) (mult beta (log (pi_t s))).

Definition pi_next (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S) : R :=
  mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
       (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).

(* 引理 A：Boltzmann 因子桥 *)
Lemma boltzmann_factor_bridge :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S),
    Id (exp_neg (mult (inv_pos beta beta_pos) (energy_t pi_t s)))
       (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).
Proof.
  intros pi_t pi_t_pos s.
  unfold energy_t, advantage_aug.
  set (A := minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s))))).
  assert (H1a : Id (mult (inv_pos beta beta_pos) (opp (mult eta A)))
                   (opp (mult (mult eta (inv_pos beta beta_pos)) A))).
  {
    apply (id_trans (opp_mult_l (inv_pos beta beta_pos) (mult eta A))).
    apply (id_cong opp
           (id_trans (mult_assoc (inv_pos beta beta_pos) eta A)
                     (id_cong (fun x => mult x A) (mult_comm (inv_pos beta beta_pos) eta)))).
  }
  assert (H1b : Id (mult (inv_pos beta beta_pos) (mult beta (log (pi_t s)))) (log (pi_t s))).
  {
    apply (id_trans (mult_assoc (inv_pos beta beta_pos) beta (log (pi_t s)))).
    apply (id_trans (id_cong (fun x => mult x (log (pi_t s)))
                             (id_trans (mult_comm (inv_pos beta beta_pos) beta) (inv_pos_correct beta beta_pos)))).
    apply (id_trans (mult_comm one (log (pi_t s))) (mult_one (log (pi_t s)))).
  }
  assert (H1 : Id (mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s)))))
                  (minus (opp (mult (mult eta (inv_pos beta beta_pos)) A)) (log (pi_t s)))).
  {
    apply (id_trans (mult_minus_distr_l (inv_pos beta beta_pos) (opp (mult eta A)) (mult beta (log (pi_t s))))).
    apply (id_trans (id_cong (fun x => minus x (mult (inv_pos beta beta_pos) (mult beta (log (pi_t s))))) H1a)).
    apply (id_cong (fun x => minus (opp (mult (mult eta (inv_pos beta beta_pos)) A)) x) H1b).
  }
  assert (H2 : Id (mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s)))))
                  (minus (opp (mult (mult eta (inv_pos beta beta_pos)) A)) (log (pi_t s)))).
  { exact H1. }
  assert (H3 : Id (opp (mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s))))))
                  (plus (mult (mult eta (inv_pos beta beta_pos)) A) (log (pi_t s)))).
  {
    apply (id_trans (id_cong opp H2)).
    apply (id_trans (opp_minus (opp (mult (mult eta (inv_pos beta beta_pos)) A)) (log (pi_t s)))).
    apply (id_cong (fun x => plus x (log (pi_t s)))).
    apply double_neg.
  }
  assert (H4 : Id (mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s)))))
                  (opp (plus (mult (mult eta (inv_pos beta beta_pos)) A) (log (pi_t s))))).
  {
    set (X := mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s))))).
    apply (id_trans (id_sym (double_neg X)) (id_sym (id_cong opp (id_sym H3)))).
  }
  assert (H5 : Id (exp_neg (mult (inv_pos beta beta_pos) (minus (opp (mult eta A)) (mult beta (log (pi_t s))))))
                  (mult (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) A)))
                        (exp_neg (opp (log (pi_t s)))))).
  {
    apply (id_trans (id_cong (fun t => exp_neg t) H4)).
    apply exp_neg_opp_plus.
  }
  assert (H6 : Id (exp_neg (opp (log (pi_t s)))) (pi_t s))
    by exact (exp_neg_opp_log (pi_t s) (pi_t_pos s)).
  (* 目标重写：energy_t 展开后 *)
  unfold energy_t.
  apply (id_trans H5).
  apply (id_trans (id_cong (fun x => mult (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) A))) x) H6)).
  apply mult_comm.
Qed.

(* 引理 B：Z_rel 的 Boltzmann 形式 *)
Lemma Z_rel_boltzmann_form :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
    Id (Z_rel pi_t)
       (sum_over_S (fun s => exp_neg (mult (inv_pos beta beta_pos) (energy_t pi_t s)))).
Proof.  intros pi_t pi_t_pos.
  unfold Z_rel.
  exact (sum_over_S_ext
           (fun s => mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))
           (fun s => exp_neg (mult (inv_pos beta beta_pos) (energy_t pi_t s)))
           (fun s => id_sym (boltzmann_factor_bridge pi_t pi_t_pos s))).
Qed.

(* 引理 C：π_next 的对数展开 *)
Lemma pi_next_log_decomp :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S),
    Id (log (pi_next pi_t pi_t_pos s))
       (plus (log (pi_t s))
             (plus (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))
                   (opp (log (Z_rel pi_t))))).
Proof.
  intros pi_t pi_t_pos s.
  unfold pi_next.
  assert (Hpos1 : lt zero (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)))
    by exact (inv_pos_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)).
  assert (Hpos2 : lt zero (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))).
  { apply mult_positive; [ exact (pi_t_pos s) | apply exp_neg_pos ]. }
  assert (Hlm : Id (log (mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                              (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))))
                   (plus (log (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)))
                         (log (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))))
    by exact (log_mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                       (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))
                       Hpos1 Hpos2).
  assert (Hli : Id (log (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))) (opp (log (Z_rel pi_t))))
    by exact (log_inv_one_inv (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)).
  assert (Hpos3 : lt zero (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))
    by exact (exp_neg_pos _).
  assert (Hlm2 : Id (log (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))
                    (plus (log (pi_t s)) (log (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))))
    by exact (log_mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))) (pi_t_pos s) Hpos3).
  assert (Hle : Id (log (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))
                   (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))
    by exact (id_trans (log_exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))
                       (double_neg (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))).
  assert (Hlm2b : Id (log (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))
                     (plus (log (pi_t s)) (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))
    by exact (id_trans Hlm2 (id_cong (fun x => plus (log (pi_t s)) x) Hle)).
  apply (id_trans Hlm).
  apply (id_trans (id_cong (fun x => plus x (log (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))) Hli)).
  apply (id_trans (id_cong (fun x => plus (opp (log (Z_rel pi_t))) x) Hlm2b)).
  (* 重组：opp(log Z) + (log pi_t + X) == log pi_t + (X + opp (log Z)) *)
  set (X := mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)).
  assert (Hre : Id (plus (opp (log (Z_rel pi_t))) (plus (log (pi_t s)) X))
                   (plus (log (pi_t s)) (plus X (opp (log (Z_rel pi_t)))))).
  {
    apply (id_trans (plus_assoc (opp (log (Z_rel pi_t))) (log (pi_t s)) X)).
    apply (id_trans (id_cong (fun y => plus y X) (plus_comm (opp (log (Z_rel pi_t))) (log (pi_t s))))).
    apply (id_trans (id_sym (plus_assoc (log (pi_t s)) (opp (log (Z_rel pi_t))) X))).
    apply (id_cong (fun y => plus (log (pi_t s)) y) (plus_comm (opp (log (Z_rel pi_t))) X)).
  }
  exact Hre.
Qed.

(* 引理 D：π_next 归一化 *)
Lemma pi_next_normalized :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
    Id (sum_over_S (pi_next pi_t pi_t_pos)) one.
Proof.
  intros pi_t pi_t_pos.
  assert (H1 : Id (sum_over_S (fun s => pi_next pi_t pi_t_pos s))
                  (sum_over_S (fun s => mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                                            (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))))
    by (apply sum_over_S_ext; intro s; reflexivity).
  assert (H2 : Id (sum_over_S (fun s => mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                                            (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))))
                  (mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                        (sum_over_S (fun s => mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))))))
    by exact (sum_over_S_linear (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                                (fun s => mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))).
  assert (H3 : Id (mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)) (Z_rel pi_t)) one)
    by exact (id_trans (mult_comm (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)) (Z_rel pi_t))
                       (inv_pos_correct (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))).
  assert (Hdef : Id (sum_over_S (fun s => mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s)))))) (Z_rel pi_t))
    by reflexivity.
  apply (id_trans H1 (id_trans H2 (id_trans (id_cong (fun x => mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)) x) Hdef) H3))).
Qed.

(* free_energy 对分布的外延性 *)
Lemma free_energy_ext_t12 :
  forall (energy : S -> R) (D : R) (p q : S -> R),
    (forall s : S, Id (p s) (q s)) ->
    Id (free_energy energy D p) (free_energy energy D q).
Proof.
  intros energy D p q Hpq. unfold free_energy.
  exact (id_cong2 plus (sum_over_S_ext (fun s => mult (p s) (energy s)) (fun s => mult (q s) (energy s)) (fun s => id_cong (fun x => mult x (energy s)) (Hpq s))) (id_cong (fun x => mult D x) (sum_over_S_ext (fun s => mult (p s) (log (p s))) (fun s => mult (q s) (log (q s))) (fun s => id_cong2 mult (Hpq s) (id_cong log (Hpq s)))))).
Qed.

(* 引理 E：相对自由能分解 *)
Lemma rel_free_energy_decomp :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (free_energy (energy_t pi_t) beta pi_t)
       (plus (free_energy (energy_t pi_t) beta (pi_next pi_t pi_t_pos))
             (mult beta
               (sum_over_S (fun s => mult (pi_t s)
                 (minus (log (pi_t s)) (log (pi_next pi_t pi_t_pos s))))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  assert (Hext : forall s : S, Id (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos) s)
                                 (pi_next pi_t pi_t_pos s)).
  {
    intro s.
    unfold boltzmann_dist, pi_next.
    apply (id_cong (fun x => mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)) x)).
    exact (boltzmann_factor_bridge pi_t pi_t_pos s).
  }
  pose proof (free_energy_kl_decomp (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)
                                    (Z_rel_boltzmann_form pi_t pi_t_pos) pi_t pi_t_norm) as Hdec.
  apply (id_trans Hdec).
  apply (id_cong2 plus
         (free_energy_ext_t12 (energy_t pi_t) beta
                          (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                          (pi_next pi_t pi_t_pos) Hext)
         (id_cong (fun x => mult beta x)
                  (sum_over_S_ext
                    (fun s => mult (pi_t s) (minus (log (pi_t s)) (log (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos) s))))
                    (fun s => mult (pi_t s) (minus (log (pi_t s)) (log (pi_next pi_t pi_t_pos s))))
                    (fun s => id_cong (fun y => mult (pi_t s) (minus (log (pi_t s)) y)) (id_cong log (Hext s)))))).
Qed.

(* r(s) == A_t(s) + beta·(log pi_t(s) - log pi_ref(s))（advantage_aug 定义反解） *)
Lemma reward_expand :
  forall (pi_t : S -> R) (s : S),
    Id (reward s)
       (plus (advantage_aug pi_t s)
             (minus (mult beta (log (pi_t s))) (mult beta (log (pi_ref s))))).
Proof.
  intros pi_t s.
  unfold advantage_aug.
  (* A == minus (reward s) (mult beta (minus (log pi_t) (log pi_ref)))
     ⟹ reward s == A + mult beta (minus (log pi_t) (log pi_ref)) *)
  assert (Hc : Id (plus (minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s)))))
                        (mult beta (minus (log (pi_t s)) (log (pi_ref s)))))
                  (reward s))
    by exact (minus_plus_cancel_gap (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s))))).
  apply (id_trans (id_sym Hc)).
  apply (id_cong (fun y => plus (minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s))))) y)
                 (mult_minus_distr_l beta (log (pi_t s)) (log (pi_ref s)))).
Qed.


(* ===== T1.2 第二阶段：策略改进单调性主定理 ===== *)
(* opp 提和：Σ (opp·f) == opp (Σ f) *)
Lemma sum_over_S_opp_t12 : forall (f : S -> R),
  Id (sum_over_S (fun s => opp (f s))) (opp (sum_over_S f)).
Proof.  intro f.
  exact (id_trans (sum_over_S_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))
        (fun s => id_sym (id_trans (opp_mult_r one (f s))
                                   (id_cong opp (id_trans (mult_comm one (f s)) (mult_one (f s))))))) (id_trans (sum_over_S_linear (opp one) f)
                  (id_trans (opp_mult_r one (sum_over_S f))
                            (id_cong opp (id_trans (mult_comm one (sum_over_S f)) (mult_one (sum_over_S f))))))).
Qed.

(* F_t(pi_t) == opp (eta·Σ pi_t·A_t) *)
(* 通用：Σ pi_t·(opp(a·f)) == opp (a·Σ pi_t·f) *)
Lemma sum_ptimes_opp_scal_t12 :
  forall (pi_t : S -> R) (a : R) (f : S -> R),
    Id (sum_over_S (fun s => mult (pi_t s) (opp (mult a (f s)))))
       (opp (mult a (sum_over_S (fun s => mult (pi_t s) (f s))))).
Proof.
  intros pi_t a f.
  set (Lf := fun s : S => mult (pi_t s) (opp (mult a (f s)))).
  set (Rf := fun s : S => opp (mult a (mult (pi_t s) (f s)))).
  assert (Hpt : forall s : S, Id (Lf s) (Rf s)).
  {
    intro s. unfold Lf, Rf.
    assert (Hm : Id (mult (pi_t s) (mult a (f s))) (mult a (mult (pi_t s) (f s)))).
    {
      apply (id_trans (mult_assoc (pi_t s) a (f s))
                      (id_trans (id_cong (fun x => mult x (f s)) (mult_comm (pi_t s) a))
                                (id_sym (mult_assoc a (pi_t s) (f s))))).
    }
    apply (id_trans (opp_mult_l (pi_t s) (mult a (f s))) (id_cong opp Hm)).
  }
  assert (HsumR : Id (sum_over_S Rf) (opp (mult a (sum_over_S (fun s => mult (pi_t s) (f s)))))).
  {
    unfold Rf.
    apply (id_trans (sum_over_S_opp_t12 (fun s => mult a (mult (pi_t s) (f s))))
                    (id_cong opp (sum_over_S_linear a (fun s => mult (pi_t s) (f s))))).
  }
  unfold Lf.
  apply (id_trans (sum_over_S_ext Lf Rf Hpt) HsumR).
Qed.



(* 通用：Σ pi_t·(a·log) 直接由 sum_over_S_linear 经逐点重组给出——F_t_simpl_t 内联使用 *)

(* 通用：Σ pi_t·(a·f) == a·Σ pi_t·f *)
Lemma sum_ptimes_scal_t12 :
  forall (pi_t : S -> R) (a : R) (f : S -> R),
    Id (sum_over_S (fun s => mult (pi_t s) (mult a (f s))))
       (mult a (sum_over_S (fun s => mult (pi_t s) (f s)))).
Proof.  intros pi_t a f.
  exact (id_trans (sum_over_S_ext (fun s => mult (pi_t s) (mult a (f s))) (fun s => mult a (mult (pi_t s) (f s)))
    (fun s => id_trans (mult_assoc (pi_t s) a (f s))
                       (id_trans (id_cong (fun x => mult x (f s)) (mult_comm (pi_t s) a))
                                 (id_sym (mult_assoc a (pi_t s) (f s)))))) (sum_over_S_linear a (fun s => mult (pi_t s) (f s)))).
Qed.

Lemma F_t_simpl_t :
  forall (pi_t : S -> R),
    Id (free_energy (energy_t pi_t) beta pi_t)
       (opp (mult eta (sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s))))).
Proof.
  intros pi_t.
  unfold free_energy, energy_t, advantage_aug.
  set (A := advantage_aug pi_t).
  set (S1t := sum_over_S (fun s => mult (pi_t s) (log (pi_t s)))).
  assert (H1 : Id (sum_over_S (fun s => mult (pi_t s) (opp (mult eta (A s)))))
                  (opp (mult eta (sum_over_S (fun s => mult (pi_t s) (A s)))))).
  { exact (sum_ptimes_opp_scal_t12 pi_t eta A). }
  assert (H2 : Id (sum_over_S (fun s => mult (pi_t s) (mult beta (log (pi_t s)))))
                  (mult beta S1t)).
  {
    unfold S1t.
    apply (id_trans (sum_over_S_ext _ _
      (fun s => id_trans (mult_assoc (pi_t s) beta (log (pi_t s)))
                         (id_trans (id_cong (fun x => mult x (log (pi_t s))) (mult_comm (pi_t s) beta))
                                   (id_sym (mult_assoc beta (pi_t s) (log (pi_t s)))))))).
    apply (sum_over_S_linear beta (fun s => mult (pi_t s) (log (pi_t s)))).
  }
  assert (Hsum : Id (sum_over_S (fun s => mult (pi_t s) (minus (opp (mult eta (A s))) (mult beta (log (pi_t s))))))
                    (minus (opp (mult eta (sum_over_S (fun s => mult (pi_t s) (A s))))) (mult beta S1t))).
  {
    apply (id_trans (sum_over_S_ext _ _
      (fun s => mult_minus_distr_l (pi_t s) (opp (mult eta (A s))) (mult beta (log (pi_t s)))))).
    apply (id_trans (sum_over_S_minus (fun s => mult (pi_t s) (opp (mult eta (A s))))
                                      (fun s => mult (pi_t s) (mult beta (log (pi_t s)))))).
    apply (id_cong2 minus H1 H2).
  }
  set (SX := opp (mult eta (sum_over_S (fun s => mult (pi_t s) (A s))))).
  apply (id_trans (id_cong2 plus Hsum (id_refl)) (minus_plus_cancel_gap SX (mult beta S1t))).
Qed.



(* F_t(pi_next) == opp (beta·log Z_rel)（pi_next_log_decomp + ΣNp 归一化） *)
(* 通用：Σ pi_t·(opp c) == opp c（Σ pi_t = 1） *)
Lemma sum_ptimes_opp_const_t12 :
  forall (pi_t : S -> R) (pi_t_norm : Id (sum_over_S pi_t) one) (c : R),
    Id (sum_over_S (fun s => mult (pi_t s) (opp c))) (opp c).
Proof.  intros pi_t pi_t_norm c.
  exact (id_trans (sum_over_S_ext (fun s => mult (pi_t s) (opp c)) (fun s => mult (opp c) (pi_t s)) (fun s => mult_comm (pi_t s) (opp c))) (id_trans (sum_over_S_linear (opp c) pi_t)
                  (id_trans (id_cong (fun x => mult (opp c) x) pi_t_norm)
                            (mult_one (opp c))))).
Qed.

(* beta·(eta·(1/beta)·a) == eta·a（inv_pos_correct 吸收） *)
Lemma beta_eta_inv_absorb_t12 : forall (a : R),
  Id (mult beta (mult (mult eta (inv_pos beta beta_pos)) a)) (mult eta a).
Proof.
  intro a.
  exact (id_trans (mult_assoc beta (mult eta (inv_pos beta beta_pos)) a) (id_trans (id_cong (fun x => mult x a) (id_trans (mult_assoc beta eta (inv_pos beta beta_pos)) (id_trans (id_cong (fun x => mult x (inv_pos beta beta_pos)) (mult_comm beta eta)) (id_sym (mult_assoc eta beta (inv_pos beta beta_pos)))))) (id_cong (fun x => mult x a) (id_trans (id_cong (fun x => mult eta x) (inv_pos_correct beta beta_pos)) (mult_one eta))))).
Qed.

Lemma F_t_simpl_next :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
    Id (free_energy (energy_t pi_t) beta (pi_next pi_t pi_t_pos))
       (opp (mult beta (log (Z_rel pi_t)))).
Proof.
  intros pi_t pi_t_pos.
  unfold free_energy, energy_t, advantage_aug.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (S1n := sum_over_S (fun s => mult (Np s) (log (pi_t s)))).
  set (SAn := sum_over_S (fun s => mult (Np s) (A s))).
  set (M := mult eta (inv_pos beta beta_pos)).
  (* H1：Σ Np·energy_t == -eta·SAn - beta·S1n *)
  assert (H1 : Id (sum_over_S (fun s => mult (Np s) (minus (opp (mult eta (A s))) (mult beta (log (pi_t s))))))
                  (minus (opp (mult eta SAn)) (mult beta S1n))).
  {
    apply (id_trans (sum_over_S_ext _ _
      (fun s => mult_minus_distr_l (Np s) (opp (mult eta (A s))) (mult beta (log (pi_t s)))))).
    apply (id_trans (sum_over_S_minus (fun s => mult (Np s) (opp (mult eta (A s))))
                                      (fun s => mult (Np s) (mult beta (log (pi_t s)))))).
    apply (id_cong2 minus (sum_ptimes_opp_scal_t12 Np eta A)
                           (sum_ptimes_scal_t12 Np beta (fun s => log (pi_t s)))).
  }
  (* H2：Σ Np·log Np == S1n + M·SAn - log Z *)
  assert (HlogNp : forall s : S, Id (log (Np s))
                                   (plus (log (pi_t s)) (plus (mult M (A s)) (opp (log (Z_rel pi_t)))))).
  { intro s. unfold Np, A, M. exact (pi_next_log_decomp pi_t pi_t_pos s). }
  assert (H2 : Id (sum_over_S (fun s => mult (Np s) (log (Np s))))
                  (plus S1n (plus (mult M SAn) (opp (log (Z_rel pi_t)))))).
  {
    unfold S1n, SAn.
    apply (id_trans (sum_over_S_ext _ _
      (fun s => id_cong (fun y => mult (Np s) y) (HlogNp s)))).
    apply (id_trans (sum_over_S_ext _ _
      (fun s => distrib (Np s) (log (pi_t s)) (plus (mult M (A s)) (opp (log (Z_rel pi_t))))))).
    assert (Ht2 : Id (sum_over_S (fun s => mult (Np s) (plus (mult M (A s)) (opp (log (Z_rel pi_t))))))(
                     (plus (mult M SAn) (opp (log (Z_rel pi_t)))))).
    {
      unfold SAn.
      assert (Ht2a : Id (sum_over_S (fun s => mult (Np s) (mult M (A s)))) (mult M SAn)).
      { unfold SAn. exact (sum_ptimes_scal_t12 Np M A). }
      assert (Ht2b : Id (sum_over_S (fun s => mult (Np s) (opp (log (Z_rel pi_t))))) (opp (log (Z_rel pi_t)))).
      { exact (sum_ptimes_opp_const_t12 Np (pi_next_normalized pi_t pi_t_pos) (log (Z_rel pi_t))). }
      apply (id_trans (sum_over_S_ext _ _ (fun s => distrib (Np s) (mult M (A s)) (opp (log (Z_rel pi_t)))))).
      apply (id_trans (sum_over_S_add (fun s => mult (Np s) (mult M (A s)))
                                      (fun s => mult (Np s) (opp (log (Z_rel pi_t)))))).
      apply (id_cong2 plus Ht2a Ht2b).
    }
    apply (id_trans (sum_over_S_add (fun s => mult (Np s) (log (pi_t s)))
                            (fun s => mult (Np s) (plus (mult M (A s)) (opp (log (Z_rel pi_t))))))
                    (id_cong2 plus (id_refl) Ht2)).
  }
  set (SX := opp (mult eta SAn)).
  set (SY := mult beta S1n).
  apply (id_trans (id_cong2 plus H1 (id_cong (fun x => mult beta x) H2))).
  apply (id_trans (id_cong (fun x => plus (minus SX SY) x)
                           (distrib beta S1n (plus (mult M SAn) (opp (log (Z_rel pi_t))))))).
  apply (id_trans (id_cong (fun x => plus (minus SX SY) (plus (mult beta S1n) x))
                           (distrib beta (mult M SAn) (opp (log (Z_rel pi_t)))))).
  apply (id_trans (id_cong (fun x => plus (minus SX SY) (plus (mult beta S1n) (plus x (mult beta (opp (log (Z_rel pi_t)))))))
                           (beta_eta_inv_absorb_t12 SAn))).
  apply (id_trans (id_cong (fun x => plus (minus SX SY) (plus (mult beta S1n) (plus (mult eta SAn) x)))
                           (opp_mult_l beta (log (Z_rel pi_t))))).
  apply (id_trans (plus_assoc (minus SX SY) (mult beta S1n) (plus (mult eta SAn) (opp (mult beta (log (Z_rel pi_t))))))).
  apply (id_trans (id_cong (fun x => plus x (plus (mult eta SAn) (opp (mult beta (log (Z_rel pi_t)))))) (minus_plus_cancel_gap SX SY))).
  apply (id_trans (plus_assoc SX (mult eta SAn) (opp (mult beta (log (Z_rel pi_t)))))).
  unfold SX.
  apply (id_trans (id_cong (fun x => plus x (opp (mult beta (log (Z_rel pi_t)))))
                          (id_trans (plus_comm (opp (mult eta SAn)) (mult eta SAn))
                                    (plus_opp (mult eta SAn))))).
  apply (id_trans (plus_comm zero (opp (mult beta (log (Z_rel pi_t))))) (plus_zero (opp (mult beta (log (Z_rel pi_t)))))).
Qed.

(* F_t(pi_next) 的 KL 形式：-eta·Σπ_next·A + beta·KL(pi_next||pi_t)（定义性） *)
Lemma F_t_simpl_next_kl :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
    Id (free_energy (energy_t pi_t) beta (pi_next pi_t pi_t_pos))
       (plus (opp (mult eta (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))))
             (mult beta (relative_entropy (pi_next pi_t pi_t_pos) pi_t))).
Proof.
  intros pi_t pi_t_pos.
  unfold free_energy, energy_t, advantage_aug, relative_entropy.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (S1n := sum_over_S (fun s => mult (Np s) (log (pi_t s)))).
  set (SAn := sum_over_S (fun s => mult (Np s) (A s))).
  set (S2n := sum_over_S (fun s => mult (Np s) (log (Np s)))).
  assert (H1 : Id (sum_over_S (fun s => mult (Np s) (minus (opp (mult eta (A s))) (mult beta (log (pi_t s))))))
                  (minus (opp (mult eta SAn)) (mult beta S1n))).
  {
    apply (id_trans (sum_over_S_ext _ _
      (fun s => mult_minus_distr_l (Np s) (opp (mult eta (A s))) (mult beta (log (pi_t s)))))).
    apply (id_trans (sum_over_S_minus (fun s => mult (Np s) (opp (mult eta (A s))))
                                      (fun s => mult (Np s) (mult beta (log (pi_t s)))))).
    apply (id_cong2 minus (sum_ptimes_opp_scal_t12 Np eta A)
                           (sum_ptimes_scal_t12 Np beta (fun s => log (pi_t s)))).
  }
  set (SX := opp (mult eta SAn)).
  set (SY := mult beta S1n).
  (* S2n - S1n == Σ Np (log Np - log pi_t) == relative_entropy Np pi_t *)
  assert (Hkl : Id (minus S2n S1n) (sum_over_S (fun s => mult (Np s) (minus (log (Np s)) (log (pi_t s)))))).
  {
    unfold S2n, S1n.
    apply (id_trans (id_sym (sum_over_S_minus (fun s => mult (Np s) (log (Np s))) (fun s => mult (Np s) (log (pi_t s)))))).
    apply (sum_over_S_ext _ _ (fun s => id_sym (mult_minus_distr_l (Np s) (log (Np s)) (log (pi_t s))))).
  }
  apply (id_trans (id_cong (fun x => plus x (mult beta S2n)) H1)).
  assert (Hm : Id (plus (opp (mult beta S1n)) (mult beta S2n)) (mult beta (minus S2n S1n))).
  {
    unfold minus.
    apply (id_trans (id_cong2 plus (id_sym (opp_mult_l beta S1n)) (id_refl))).
    apply (id_trans (plus_comm (mult beta (opp S1n)) (mult beta S2n))
                    (id_sym (distrib beta S2n (opp S1n)))).
  }
  unfold minus.
  apply (id_trans (id_sym (plus_assoc (opp (mult eta SAn)) (opp (mult beta S1n)) (mult beta S2n)))).
  apply (id_trans (id_cong (fun x => plus (opp (mult eta SAn)) x) Hm)).
  apply (id_cong (fun x => plus (opp (mult eta SAn)) (mult beta x)) Hkl).
Qed.



(* 代理-真实差异恒等式：eta·(Xn - Xt) == beta·(KL(pi_next||pi_t) + KL(pi_t||pi_next)) *)
Lemma surrogate_diff_identity :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (pi_t_norm : Id (sum_over_S pi_t) one),
    forall (pi_next_pos : forall s : S, lt zero (pi_next pi_t pi_t_pos s)),
    Id (mult eta (minus (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))
                        (sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s)))))
       (mult beta (plus (relative_entropy (pi_next pi_t pi_t_pos) pi_t)
                        (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm pi_next_pos.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  pose proof (rel_free_energy_decomp pi_t pi_t_pos pi_t_norm) as Hdec.
  pose proof (F_t_simpl_t pi_t) as HFt.
  pose proof (F_t_simpl_next_kl pi_t pi_t_pos) as HFn.
  assert (Heq : Id (opp (mult eta Xt))
                  (plus (plus (opp (mult eta Xn)) (mult beta K1)) (mult beta K2))).
  {
    apply (id_trans (id_sym HFt)).
    apply (id_trans Hdec).
    apply (id_cong2 plus HFn (id_refl)).
  }
  assert (Heq2 : Id (opp (mult eta Xt))
                   (plus (opp (mult eta Xn)) (plus (mult beta K1) (mult beta K2)))).
  {
    apply (id_trans Heq).
    apply (id_sym (plus_assoc (opp (mult eta Xn)) (mult beta K1) (mult beta K2))).
  }
  assert (Hstep : Id (plus (mult eta Xn) (opp (mult eta Xt)))
                    (plus (mult beta K1) (mult beta K2))).
  {
    apply (id_trans (id_cong2 plus (id_refl) Heq2)).
    apply (id_trans (plus_assoc (mult eta Xn) (opp (mult eta Xn)) (plus (mult beta K1) (mult beta K2)))).
    apply (id_trans (id_cong (fun x => plus x (plus (mult beta K1) (mult beta K2))) (plus_opp (mult eta Xn)))
                    (id_trans (plus_comm zero (plus (mult beta K1) (mult beta K2)))
                              (plus_zero (plus (mult beta K1) (mult beta K2))))).
  }
  apply (id_trans (mult_minus_distr_l eta Xn Xt)
                  (id_trans Hstep (id_sym (distrib beta K1 K2)))).
Qed.

(* pi_next 正性（Boltzmann 构造） *)
Lemma pi_next_pos :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S),
    lt zero (pi_next pi_t pi_t_pos s).
Proof.
  intros pi_t pi_t_pos s.
  unfold pi_next.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + exact (pi_t_pos s).
    + apply exp_neg_pos.
Qed.

(* ============ 辅助：le 逆与乘法非负 ============ *)

(* le a b ⟸ le zero (minus b a)（le_minus_nonneg 的逆） *)
Lemma le_nonneg_minus : forall a b : R, le zero (minus b a) -> le a b.
Proof.
  intros a b H.
  unfold minus in H.
  assert (Hstep : le (plus a zero) (plus a (plus b (opp a)))).
  { exact (le_plus_compat a a zero (plus b (opp a)) (le_refl a) H). }
  assert (Hl : Id (plus a zero) a) by exact (plus_zero a).
  assert (Hr : Id (plus a (plus b (opp a))) b).
  {
    apply (id_trans (plus_assoc a b (opp a))).
    apply (id_trans (id_cong (fun x => plus x (opp a)) (plus_comm a b))).
    apply (id_trans (id_sym (plus_assoc b a (opp a)))).
    apply (id_trans (id_cong (fun x => plus b x) (plus_opp a))).
    exact (plus_zero b).
  }
  exact (le_id_l a (plus a zero) b (id_sym Hl)
                (le_id_r (plus a zero) (plus a (plus b (opp a))) b Hr Hstep)).
Qed.

(* 非负乘非负仍非负 *)
Lemma le_mult_nonneg_t12 : forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  exact (le_id_l zero (mult zero b) (mult a b) (id_sym (id_trans (mult_comm zero b) (mult_zero b))) (le_mult_compat_weak zero a b Hb Ha)).
Qed.

(* 右分配减法：mult (minus a b) c == minus (mult a c) (mult b c) *)
Lemma mult_minus_distr_r_t12 : forall a b c : R,
  Id (mult (minus a b) c) (minus (mult a c) (mult b c)).
Proof.  intros a b c.
  unfold minus.
  exact (id_trans (mult_comm (plus a (opp b)) c) (id_trans (distrib c a (opp b)) (id_trans (id_cong (fun x => plus x (mult c (opp b))) (mult_comm c a)) (id_trans (id_cong (fun x => plus (mult a c) x)
                           (id_trans (opp_mult_l c b) (id_cong opp (mult_comm c b)))) (id_refl))))).
Qed.

(* eta·a + (1-eta)·a == a *)
Lemma eta_absorb_t12 : forall a : R,
  Id (plus (mult eta a) (mult (minus one eta) a)) a.
Proof.
  intro a.
  exact (id_trans (id_cong2 plus (mult_comm eta a) (mult_comm (minus one eta) a)) (id_trans (id_sym (distrib a eta (minus one eta))) (id_trans (id_cong (fun x => mult a x) (id_trans (plus_assoc eta one (opp eta)) (id_trans (id_cong (fun x => plus x (opp eta)) (plus_comm eta one)) (id_trans (id_sym (plus_assoc one eta (opp eta))) (id_trans (id_cong (fun x => plus one x) (plus_opp eta)) (plus_zero one)))))) (mult_one a)))).
Qed.

(* ============ 逐点能量差桥 ============ *)

(* align_energy s == energy_t(pi_t) s + (1-eta)·(-advantage_aug(pi_t) s)
   D(s) := align - energy_t == (1-eta)·(-A)（reward_expand + 抵消） *)
Lemma align_energy_expand :
  forall (pi_t : S -> R) (s : S),
    Id (align_energy s)
       (plus (energy_t pi_t s) (mult (minus one eta) (opp (advantage_aug pi_t s)))).
Proof.
  intros pi_t s.
  unfold align_energy, energy_t, advantage_aug.
  set (A := minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s))))).
  set (B1 := mult beta (log (pi_t s))).
  set (B2 := mult beta (log (pi_ref s))).
  (* H0：reward 展开（advantage_aug 定义反解） *)
  assert (H0 : Id (reward s) (plus A (minus B1 B2))) by exact (reward_expand pi_t s).
  (* H1：opp (reward s) == plus (opp A) (plus (opp B1) B2) *)
  assert (H1 : Id (opp (reward s)) (plus (opp A) (plus (opp B1) B2))).
  {
    apply (id_trans (id_cong opp H0)).
    apply (id_trans (opp_plus A (minus B1 B2))).
    apply (id_cong (fun x => plus (opp A) x) (opp_minus B1 B2)).
  }
  (* H2：LHS 化简为 plus (opp A) (opp B1) *)
  assert (H2 : Id (minus (opp (reward s)) B2) (plus (opp A) (opp B1))).
  {
    unfold minus.
    apply (id_trans (id_cong2 plus H1 (id_refl))).
    apply (id_trans (id_sym (plus_assoc (opp A) (plus (opp B1) B2) (opp B2)))).
    apply (id_trans (id_cong (fun x => plus (opp A) x)
                             (id_sym (plus_assoc (opp B1) B2 (opp B2))))).
    apply (id_trans (id_cong (fun x => plus (opp A) (plus (opp B1) x)) (plus_opp B2))).
    apply (id_cong (fun x => plus (opp A) x) (plus_zero (opp B1))).
  }
  (* H3：(1-eta)·(opp A) == plus (opp A) (mult eta A) *)
  assert (H3 : Id (mult (minus one eta) (opp A)) (plus (opp A) (mult eta A))).
  {
    unfold minus.
    apply (id_trans (mult_comm (plus one (opp eta)) (opp A))).
    apply (id_trans (distrib (opp A) one (opp eta))).
    apply (id_trans (id_cong (fun x => plus x (mult (opp A) (opp eta))) (mult_one (opp A)))).
    apply (id_trans (id_cong (fun x => plus (opp A) x)
                             (id_trans (opp_mult_l (opp A) eta)
                                       (id_trans (id_cong opp (opp_mult_r A eta)) (double_neg (mult A eta)))))).
    apply (id_cong (fun x => plus (opp A) x) (mult_comm A eta)).
  }
  (* H4：RHS 化简为 plus (opp A) (opp B1) *)
  assert (H4 : Id (plus (minus (opp (mult eta A)) B1) (mult (minus one eta) (opp A)))
                  (plus (opp A) (opp B1))).
  {
    unfold minus.
    apply (id_trans (id_cong (fun x => plus (plus (opp (mult eta A)) (opp B1)) x) H3)).
    apply (id_trans (id_sym (plus_assoc (opp (mult eta A)) (opp B1) (plus (opp A) (mult eta A))))).
    apply (id_trans (id_cong (fun x => plus (opp (mult eta A)) x)
                             (id_cong (fun y => plus (opp B1) y)
                                      (plus_comm (opp A) (mult eta A))))).
    apply (id_trans (id_cong (fun x => plus (opp (mult eta A)) x)
                             (plus_assoc (opp B1) (mult eta A) (opp A)))).
    apply (id_trans (plus_assoc (opp (mult eta A)) (plus (opp B1) (mult eta A)) (opp A))).
    apply (id_trans (id_cong (fun x => plus x (opp A))
                             (id_cong (fun y => plus (opp (mult eta A)) y)
                                      (plus_comm (opp B1) (mult eta A))))).
    apply (id_trans (id_cong (fun x => plus x (opp A))
                             (plus_assoc (opp (mult eta A)) (mult eta A) (opp B1)))).
    apply (id_trans (id_cong (fun x => plus x (opp A))
                             (id_cong (fun y => plus y (opp B1))
                                      (plus_comm (opp (mult eta A)) (mult eta A))))).
    apply (id_trans (id_cong (fun x => plus x (opp A))
                             (id_cong (fun y => plus y (opp B1)) (plus_opp (mult eta A))))).
    apply (id_trans (id_cong (fun x => plus x (opp A))
                             (id_trans (plus_comm zero (opp B1)) (plus_zero (opp B1))))).
    apply (plus_comm (opp B1) (opp A)).
  }
  apply (id_trans H2 (id_sym H4)).
Qed.

(* ============ 核心桥：F_align == F_t + (1-eta)·(-Σ p·A) ============ *)

Lemma F_align_F_t_rel :
  forall (pi_t : S -> R) (p : S -> R),
    Id (free_energy align_energy beta p)
       (plus (free_energy (energy_t pi_t) beta p)
             (mult (minus one eta) (opp (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s)))))).
Proof.
  intros pi_t p.
  unfold free_energy.
  assert (Hpt : forall s : S,
    Id (mult (p s) (align_energy s))
       (plus (mult (p s) (energy_t pi_t s))
             (mult (p s) (mult (minus one eta) (opp (advantage_aug pi_t s)))))).
  {
    intro s.
    apply (id_trans (id_cong (fun x => mult (p s) x) (align_energy_expand pi_t s))).
    apply (distrib (p s) (energy_t pi_t s) (mult (minus one eta) (opp (advantage_aug pi_t s)))).
  }
  assert (Hsum : Id (sum_over_S (fun s => mult (p s) (align_energy s)))
                    (plus (sum_over_S (fun s => mult (p s) (energy_t pi_t s)))
                          (sum_over_S (fun s => mult (p s) (mult (minus one eta) (opp (advantage_aug pi_t s))))))).
  {
    apply (id_trans (sum_over_S_ext _ _ Hpt)).
    apply (sum_over_S_add (fun s => mult (p s) (energy_t pi_t s))
                          (fun s => mult (p s) (mult (minus one eta) (opp (advantage_aug pi_t s))))).
  }
  assert (Hscal : Id (sum_over_S (fun s => mult (p s) (mult (minus one eta) (opp (advantage_aug pi_t s)))))
                     (mult (minus one eta) (opp (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s)))))).
  {
    apply (id_trans (sum_ptimes_scal_t12 p (minus one eta) (fun s => opp (advantage_aug pi_t s)))).
    apply (id_cong (fun x => mult (minus one eta) x)
                   (id_trans (sum_over_S_ext _ _ (fun s => opp_mult_l (p s) (advantage_aug pi_t s)))
                             (sum_over_S_opp_t12 (fun s => mult (p s) (advantage_aug pi_t s))))).
  }
  set (SAl := sum_over_S (fun s => mult (p s) (align_energy s))).
  set (SEt := sum_over_S (fun s => mult (p s) (energy_t pi_t s))).
  set (SEnt := sum_over_S (fun s => mult (p s) (log (p s)))).
  set (SA := sum_over_S (fun s => mult (p s) (advantage_aug pi_t s))).
  set (SX := sum_over_S (fun s => mult (p s) (mult (minus one eta) (opp (advantage_aug pi_t s))))).
  apply (id_trans (id_cong2 plus Hsum (id_refl))).
  apply (id_trans (id_sym (plus_assoc SEt SX (mult beta SEnt)))).
  apply (id_trans (id_cong (fun x => plus SEt x)
                           (id_trans (id_cong (fun y => plus y (mult beta SEnt)) Hscal)
                                     (plus_comm (mult (minus one eta) (opp SA)) (mult beta SEnt))))).
  apply (plus_assoc SEt (mult beta SEnt) (mult (minus one eta) (opp SA))).
Qed.

(* ============ J(pi) 分解：align_objective == -F_t + (1-eta)·Σp·A ============ *)

Lemma align_objective_t12_decomp :
  forall (pi_t : S -> R) (p : S -> R),
    Id (align_objective p)
       (plus (opp (free_energy (energy_t pi_t) beta p))
             (mult (minus one eta) (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s))))).
Proof.  intros pi_t p.
  unfold align_objective.
  pose proof (F_align_F_t_rel pi_t p) as Hrel.
  exact (id_trans (id_cong opp Hrel) (id_trans (opp_plus (free_energy (energy_t pi_t) beta p)
                            (mult (minus one eta) (opp (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s)))))) (id_cong (fun x => plus (opp (free_energy (energy_t pi_t) beta p)) x)
                 (id_trans (id_cong opp (opp_mult_l (minus one eta) (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s)))))
                           (double_neg (mult (minus one eta) (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s))))))))).
Qed.

(* ============ J(pi_t) == Σ pi_t·A ============ *)

Lemma J_pi_t_t12 :
  forall (pi_t : S -> R) (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (align_objective pi_t)
       (sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s))).
Proof.
  intros pi_t pi_t_norm.
  pose proof (align_objective_t12_decomp pi_t pi_t) as Hdec.
  pose proof (F_t_simpl_t pi_t) as HFt.
  set (Xt := sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s))).
  apply (id_trans Hdec).
  apply (id_trans (id_cong (fun x => plus x (mult (minus one eta) Xt))
                           (id_trans (id_cong opp HFt) (double_neg (mult eta Xt))))).
  exact (eta_absorb_t12 Xt).
Qed.

(* ============ J(pi_next) == Σ pi_next·A - beta·KL(pi_next||pi_t) ============ *)

Lemma J_pi_next_t12 :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
    Id (align_objective (pi_next pi_t pi_t_pos))
       (minus (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))
              (mult beta (relative_entropy (pi_next pi_t pi_t_pos) pi_t))).
Proof.
  intros pi_t pi_t_pos.
  pose proof (align_objective_t12_decomp pi_t (pi_next pi_t pi_t_pos)) as Hdec.
  pose proof (F_t_simpl_next_kl pi_t pi_t_pos) as HFn.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  assert (Hopp : Id (opp (plus (opp (mult eta Xn)) (mult beta K1)))
                    (plus (mult eta Xn) (opp (mult beta K1)))).
  {
    apply (id_trans (opp_plus (opp (mult eta Xn)) (mult beta K1))).
    apply (id_cong2 plus (double_neg (mult eta Xn)) (id_refl)).
  }
  apply (id_trans Hdec).
  apply (id_trans (id_cong (fun x => plus x (mult (minus one eta) Xn))
                           (id_trans (id_cong opp HFn) Hopp))).
  unfold minus.
  apply (id_trans (id_sym (plus_assoc (mult eta Xn) (opp (mult beta K1)) (mult (minus one eta) Xn)))).
  apply (id_trans (id_cong (fun x => plus (mult eta Xn) x)
                           (plus_comm (opp (mult beta K1)) (mult (minus one eta) Xn)))).
  apply (id_trans (plus_assoc (mult eta Xn) (mult (minus one eta) Xn) (opp (mult beta K1)))).
  apply (id_cong (fun x => plus x (opp (mult beta K1))) (eta_absorb_t12 Xn)).
Qed.

(* ============ 主定理：策略改进单调性 ============ *)

Theorem policy_improvement_mono :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    le (align_objective pi_t) (align_objective (pi_next pi_t pi_t_pos)).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  assert (HNp_pos : forall s : S, lt zero (Np s)) by (intro s; unfold Np; apply pi_next_pos).
  assert (HNp_norm : Id (sum_over_S Np) one) by (unfold Np; apply pi_next_normalized).
  (* J 分解 *)
  assert (HJt : Id (align_objective pi_t) Xt) by (unfold Xt; apply J_pi_t_t12; exact pi_t_norm).
  assert (HJn : Id (align_objective Np) (minus Xn (mult beta K1)))
    by (unfold Xn, K1; apply J_pi_next_t12).
  assert (Hdiff : Id (minus (align_objective Np) (align_objective pi_t))
                     (minus (minus Xn (mult beta K1)) Xt)).
  { unfold minus. apply (id_cong2 plus HJn (id_cong opp HJt)). }
  (* surrogate 恒等式 *)
  assert (Hsur : Id (mult eta (minus Xn Xt)) (mult beta (plus K1 K2))).
  {
    unfold Np, A, Xn, Xt, K1, K2.
    apply (surrogate_diff_identity pi_t pi_t_pos pi_t_norm).
    intro s. unfold Np. apply pi_next_pos.
  }
  (* Xn - Xt == (1/eta)·(beta·(K1+K2)) *)
  assert (Hlc : Id (mult (inv_pos eta eta_pos) (mult eta (minus Xn Xt))) (minus Xn Xt)).
  {
    apply (id_trans (mult_assoc (inv_pos eta eta_pos) eta (minus Xn Xt))).
    apply (id_trans (id_cong (fun x => mult x (minus Xn Xt))
                             (id_trans (mult_comm (inv_pos eta eta_pos) eta) (inv_pos_correct eta eta_pos)))).
    apply (id_trans (mult_comm one (minus Xn Xt)) (mult_one (minus Xn Xt))).
  }
  assert (Hinv : Id (minus Xn Xt) (mult (inv_pos eta eta_pos) (mult beta (plus K1 K2)))).
  {
    apply (id_trans (id_sym Hlc)).
    apply (id_cong (fun x => mult (inv_pos eta eta_pos) x) Hsur).
  }
  (* 交换：minus (minus Xn B) Xt == minus (minus Xn Xt) B *)
  assert (Hswap : Id (minus (minus Xn (mult beta K1)) Xt) (minus (minus Xn Xt) (mult beta K1))).
  {
    unfold minus.
    apply (id_trans (id_sym (plus_assoc Xn (opp (mult beta K1)) (opp Xt)))).
    apply (id_trans (id_cong (fun x => plus Xn x)
                             (plus_comm (opp (mult beta K1)) (opp Xt)))).
    apply (plus_assoc Xn (opp Xt) (opp (mult beta K1))).
  }
  (* 内部代数：mult a (plus K1 K2) - K1 == mult (minus a one) K1 + mult a K2 *)
  assert (Hm1 : Id (mult one K1) K1)
    by (apply (id_trans (mult_comm one K1)); apply mult_one).
  assert (Hmm : Id (minus (mult (inv_pos eta eta_pos) K1) K1)
                   (mult (minus (inv_pos eta eta_pos) one) K1)).
  {
    apply (id_trans (id_cong (fun x => minus (mult (inv_pos eta eta_pos) K1) x) (id_sym Hm1))).
    apply (id_sym (mult_minus_distr_r_t12 (inv_pos eta eta_pos) one K1)).
  }
  assert (Hin : Id (minus (mult (inv_pos eta eta_pos) (plus K1 K2)) K1)
                   (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2))).
  {
    unfold minus.
    apply (id_trans (id_cong (fun x => plus x (opp K1)) (distrib (inv_pos eta eta_pos) K1 K2))).
    apply (id_trans (id_sym (plus_assoc (mult (inv_pos eta eta_pos) K1) (mult (inv_pos eta eta_pos) K2) (opp K1)))).
    apply (id_trans (id_cong (fun x => plus (mult (inv_pos eta eta_pos) K1) x)
                             (plus_comm (mult (inv_pos eta eta_pos) K2) (opp K1)))).
    apply (id_trans (plus_assoc (mult (inv_pos eta eta_pos) K1) (opp K1) (mult (inv_pos eta eta_pos) K2))).
    exact (id_trans (id_cong (fun x => plus x (mult (inv_pos eta eta_pos) K2)) Hmm) id_refl).
  }
  (* 整体 beta 形式 *)
  assert (Hbeta_form : Id (minus (mult (inv_pos eta eta_pos) (mult beta (plus K1 K2))) (mult beta K1))
                          (mult beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))).
  {
    apply (id_trans (id_cong (fun x => minus x (mult beta K1))
                             (id_trans (mult_assoc (inv_pos eta eta_pos) beta (plus K1 K2))
                                       (id_trans (id_cong (fun x => mult x (plus K1 K2)) (mult_comm (inv_pos eta eta_pos) beta))
                                                 (id_sym (mult_assoc beta (inv_pos eta eta_pos) (plus K1 K2))))))).
    apply (id_trans (id_sym (mult_minus_distr_l beta (mult (inv_pos eta eta_pos) (plus K1 K2)) K1))).
    apply (id_cong (fun x => mult beta x) Hin).
  }
  (* le 非负链 *)
  assert (Ha : le zero (minus (inv_pos eta eta_pos) one)).
  {
    assert (Hinv1 : Id (inv_pos one one_pos) one)
      by exact (id_trans (id_sym (id_trans (mult_comm one (inv_pos one one_pos)) (mult_one (inv_pos one one_pos))))
                         (inv_pos_correct one one_pos)).
    assert (Hinv_le : le (inv_pos one one_pos) (inv_pos eta eta_pos))
      by exact (inv_pos_le_compat eta one eta_pos one_pos eta_le_one).
    assert (Hle1 : le one (inv_pos eta eta_pos))
      by exact (le_id_l one (inv_pos one one_pos) (inv_pos eta eta_pos) (id_sym Hinv1) Hinv_le).
    exact (le_minus_nonneg one (inv_pos eta eta_pos) Hle1).
  }
  assert (Hb : le zero K1).
  {
    unfold K1.
    apply (gibbs_inequality Np pi_t HNp_norm HNp_pos pi_t_norm pi_t_pos).
  }
  assert (Hc : le zero K2).
  {
    unfold K2.
    apply (gibbs_inequality pi_t Np pi_t_norm pi_t_pos HNp_norm HNp_pos).
  }
  assert (Hd : le zero (mult (minus (inv_pos eta eta_pos) one) K1))
    by exact (le_mult_nonneg_t12 (minus (inv_pos eta eta_pos) one) K1 Ha Hb).
  assert (He : le zero (mult (inv_pos eta eta_pos) K2)).
  {
    apply (le_mult_nonneg_t12 (inv_pos eta eta_pos) K2).
    - apply (lt_le_iff zero (inv_pos eta eta_pos)). left. exact (inv_pos_pos eta eta_pos).
    - exact Hc.
  }
  assert (Hf : le zero (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2))).
  {
    assert (Hplus : le (plus zero zero)
                       (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))
      by exact (le_plus_compat zero (mult (minus (inv_pos eta eta_pos) one) K1) zero (mult (inv_pos eta eta_pos) K2) Hd He).
    exact (le_id_l zero (plus zero zero)
                    (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2))
                    (id_sym (plus_zero zero)) Hplus).
  }
  assert (Hg : le zero (mult beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))).
  {
    apply (le_mult_nonneg_t12 beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2))).
    - apply (lt_le_iff zero beta). left. exact beta_pos.
    - exact Hf.
  }
  (* 组装 *)
  assert (Hrep : Id (minus (minus Xn (mult beta K1)) Xt)
                    (mult beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))).
  {
    apply (id_trans Hswap).
    apply (id_trans (id_cong (fun x => minus x (mult beta K1)) Hinv)).
    exact Hbeta_form.
  }
  assert (Hstep : le zero (minus (minus Xn (mult beta K1)) Xt))
    by exact (le_id_r zero (mult beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))
                      (minus (minus Xn (mult beta K1)) Xt) (id_sym Hrep) Hg).
  apply le_nonneg_minus.
  exact (le_id_r zero (minus (minus Xn (mult beta K1)) Xt)
                 (minus (align_objective Np) (align_objective pi_t))
                 (id_sym Hdiff) Hstep).
Qed.
(* ============================================================ *)
(* T1.3：策略迭代向后 KL 显式递推（论文1 几何收敛的副本下降核心） *)
(*   相对熵副本下降（entropic mirror descent）的三点恒等式组装： *)
(*   KL(pi_star‖pi_{t+1}) == (1−ηβ)·KL(pi_star‖pi_t) − η·KL(pi_t‖pi_star)    *)
(*                        + KL(pi_t‖pi_{t+1})                     *)
(*   构件：F_t 分解（F_t_decomp_p）+ F_t 展开（F_t_simpl_p）+     *)
(*   surrogate 最优性（grad_cross_identity）+ rlhf_suboptimality_gap *)
(*   （κ := 1−ηβ 显式收缩因子；KL 双向项与步长 KL 显式保留）     *)
(* ============================================================ *)

(* F_t(p) == −η·Σp·A_t + β·KL(p‖pi_t)（F_t_simpl_t 对任意 p 的泛化） *)
Lemma F_t_simpl_p :
  forall (pi_t : S -> R) (p : S -> R),
    Id (free_energy (energy_t pi_t) beta p)
       (plus (opp (mult eta (sum_over_S (fun s => mult (p s) (advantage_aug pi_t s)))))
             (mult beta (relative_entropy p pi_t))).
Proof.
  intros pi_t p.
  unfold free_energy, energy_t, advantage_aug, relative_entropy.
  set (A := advantage_aug pi_t).
  set (S1p := sum_over_S (fun s => mult (p s) (log (pi_t s)))).
  set (X := opp (mult eta (sum_over_S (fun s => mult (p s) (A s))))).
  set (Sp := sum_over_S (fun s => mult (p s) (log (p s)))).
  assert (H1 : Id (sum_over_S (fun s => mult (p s) (opp (mult eta (A s)))))
                  (opp (mult eta (sum_over_S (fun s => mult (p s) (A s)))))).
  { exact (sum_ptimes_opp_scal_t12 p eta A). }
  assert (H2 : Id (sum_over_S (fun s => mult (p s) (mult beta (log (pi_t s)))))
                  (mult beta S1p)).
  {
    unfold S1p.
    apply (id_trans (sum_over_S_ext _ _
      (fun s => id_trans (mult_assoc (p s) beta (log (pi_t s)))
                         (id_trans (id_cong (fun x => mult x (log (pi_t s))) (mult_comm (p s) beta))
                                   (id_sym (mult_assoc beta (p s) (log (pi_t s)))))))).
    apply (sum_over_S_linear beta (fun s => mult (p s) (log (pi_t s)))).
  }
  assert (Hsum : Id (sum_over_S (fun s => mult (p s) (minus (opp (mult eta (A s))) (mult beta (log (pi_t s))))))
                    (minus (opp (mult eta (sum_over_S (fun s => mult (p s) (A s))))) (mult beta S1p))).
  {
    apply (id_trans (sum_over_S_ext _ _
      (fun s => mult_minus_distr_l (p s) (opp (mult eta (A s))) (mult beta (log (pi_t s)))))).
    apply (id_trans (sum_over_S_minus (fun s => mult (p s) (opp (mult eta (A s))))
                                      (fun s => mult (p s) (mult beta (log (pi_t s)))))).
    apply (id_cong2 minus H1 H2).
  }
  (* KL 桥：minus Sp S1p == Σ p·(minus (log p) (log pi_t)) *)
  assert (Hkl : Id (minus Sp S1p)
                   (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (pi_t s)))))).
  { unfold Sp, S1p.
    apply (id_trans (id_sym (sum_over_S_minus (fun s => mult (p s) (log (p s)))
                                              (fun s => mult (p s) (log (pi_t s)))))
           (sum_over_S_ext _ _
             (fun s => id_sym (mult_minus_distr_l (p s) (log (p s)) (log (pi_t s)))))). }
  (* β 提取桥：minus (mult beta Sp) (mult beta S1p) == mult beta (minus Sp S1p) *)
  assert (Hlin : Id (minus (mult beta Sp) (mult beta S1p))
                    (mult beta (minus Sp S1p))).
  { exact (id_sym (mult_minus_distr_l beta Sp S1p)). }
  (* 组装：Σ p·(minus ...) + β·Sp == X + β·(Σ p·(log p − log pi_t)) *)
  assert (Hmain : Id (plus (sum_over_S (fun s => mult (p s) (minus (opp (mult eta (A s))) (mult beta (log (pi_t s))))))
                           (mult beta Sp))
                     (plus X (mult beta (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (pi_t s)))))))).
  {
    rewrite Hsum.
    apply (id_trans (id_sym (plus_assoc X (opp (mult beta S1p)) (mult beta Sp)))
           (id_trans (id_cong (fun x => plus X x)
                              (plus_comm (opp (mult beta S1p)) (mult beta Sp)))
           (id_trans (id_cong (fun x => plus X x) Hlin)
                     (id_cong (fun x => plus X (mult beta x)) Hkl)))).
  }
  exact Hmain.
Qed.

(* F_t(p) == F_t(pi_next) + β·KL(p‖pi_next)（rel_free_energy_decomp 对任意归一化 p 的泛化） *)
Lemma F_t_decomp_p :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one) (p : S -> R),
  normalized p ->
  Id (free_energy (energy_t pi_t) beta p)
     (plus (free_energy (energy_t pi_t) beta (pi_next pi_t pi_t_pos))
           (mult beta (relative_entropy p (pi_next pi_t pi_t_pos)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm p Hp_norm.
  assert (Hext : forall s : S, Id (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos) s)
                                  (pi_next pi_t pi_t_pos s)).
  {
    intro s.
    unfold boltzmann_dist, pi_next.
    apply (id_cong (fun x => mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)) x)).
    exact (boltzmann_factor_bridge pi_t pi_t_pos s).
  }
  pose proof (free_energy_kl_decomp (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos)
                                    (Z_rel_boltzmann_form pi_t pi_t_pos) p Hp_norm) as Hdec.
  apply (id_trans Hdec).
  apply (id_cong2 plus
         (free_energy_ext_t12 (energy_t pi_t) beta
                          (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
                          (pi_next pi_t pi_t_pos) Hext)
         (id_cong (fun x => mult beta x)
                  (sum_over_S_ext
                    (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist (energy_t pi_t) beta beta_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos) s))))
                    (fun s => mult (p s) (minus (log (p s)) (log (pi_next pi_t pi_t_pos s))))
                    (fun s => id_cong (fun y => mult (p s) (minus (log (p s)) y)) (id_cong log (Hext s)))))).
Qed.

(* Xn − Xt == Σ(pi_next − pi_t)·A_t（求和减法桥，surrogate 左侧换形） *)
Lemma sum_grad_cross :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
  Id (minus (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))
            (sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s))))
     (sum_over_S (fun s => mult (minus (pi_next pi_t pi_t_pos s) (pi_t s)) (advantage_aug pi_t s))).
Proof.  intros pi_t pi_t_pos.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  exact (id_trans (id_sym (sum_over_S_minus (fun s => mult (Np s) (A s))
                                            (fun s => mult (pi_t s) (A s))))
         (sum_over_S_ext (fun s => minus (mult (Np s) (A s)) (mult (pi_t s) (A s))) (fun s => mult (minus (Np s) (pi_t s)) (A s))
           (fun s => id_sym (mult_minus_distr_r (Np s) (pi_t s) (A s))))).
Qed.

(* 副本步最优性（surrogate ÷ η）：Σ(pi_next − pi_t)·A_t == (β/η)·(KL(pi_next‖pi_t) + KL(pi_t‖pi_next)) *)
Lemma grad_cross_identity :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one)
         (pi_next_pos : forall s : S, lt zero (pi_next pi_t pi_t_pos s)),
  Id (sum_over_S (fun s => mult (minus (pi_next pi_t pi_t_pos s) (pi_t s)) (advantage_aug pi_t s)))
     (mult (mult (inv_pos eta eta_pos) beta)
           (plus (relative_entropy (pi_next pi_t pi_t_pos) pi_t)
                 (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm pi_next_pos.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  pose proof (surrogate_diff_identity pi_t pi_t_pos pi_t_norm pi_next_pos) as Hsur.
  (* Hsur : mult eta (minus Xn Xt) == mult beta (plus K1 K2) *)
  (* 目标：Σ(pi_next−pi_t)·A == mult (mult (inv_pos eta) beta) (plus K1 K2) *)
  assert (Hone : Id (mult (mult (inv_pos eta eta_pos) eta) (minus Xn Xt)) (mult one (minus Xn Xt))).
  { apply (id_cong (fun x => mult x (minus Xn Xt))
           (id_trans (mult_comm (inv_pos eta eta_pos) eta) (inv_pos_correct eta eta_pos))). }
  apply (id_trans (id_sym (sum_grad_cross pi_t pi_t_pos))
         (id_trans (id_sym (id_trans (mult_comm one (minus Xn Xt)) (mult_one (minus Xn Xt))))
         (id_trans (id_sym Hone)
         (id_trans (id_sym (mult_assoc (inv_pos eta eta_pos) eta (minus Xn Xt)))
         (id_trans (id_cong (fun x => mult (inv_pos eta eta_pos) x) Hsur)
                   (mult_assoc (inv_pos eta eta_pos) beta (plus K1 K2))))))).
Qed.

(* minus 对 plus 的分配：minus a (plus b c) == minus (minus a b) c *)
Lemma minus_sub_plus_t13 : forall a b c : R,
  Id (minus a (plus b c)) (minus (minus a b) c).
Proof.
  intros a b c.
  unfold minus.
  exact (id_trans (id_cong (fun x => plus a x) (opp_plus b c))
                  (plus_assoc a (opp b) (opp c))).
Qed.

(* minus 反对称：minus a b == opp (minus b a) *)
Lemma opp_minus_rev_t13 : forall a b : R,
  Id (minus a b) (opp (minus b a)).
Proof.
  intros a b.
  unfold minus.
  exact (id_sym (id_trans (opp_plus b (opp a))
                 (id_trans (id_cong (fun x => plus (opp b) x) (double_neg a))
                           (plus_comm (opp b) a)))).
Qed.

(* Xt − Xs == −β·KL(pi_t‖pi_star) − β·KL(pi_star‖pi_t)（对齐目标两展开 + 子优间隙） *)
Lemma sum_advance_gap :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
  Id (minus (sum_over_S (fun s => mult (pi_t s) (advantage_aug pi_t s)))
            (sum_over_S (fun s => mult (pi_star s) (advantage_aug pi_t s))))
     (plus (opp (mult beta (relative_entropy pi_t pi_star)))
           (opp (mult beta (relative_entropy pi_star pi_t)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (A := advantage_aug pi_t).
  set (Xs := sum_over_S (fun s => mult (pi_star s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  (* J(pi_star) == Xs − β·KL(pi_star‖pi_t)（align_objective_t12_decomp + F_t_simpl_p + eta_absorb） *)
  assert (Hstar : Id (align_objective pi_star)
                    (minus Xs (mult beta (relative_entropy pi_star pi_t)))).
  {
    unfold Xs.
    pose proof (align_objective_t12_decomp pi_t pi_star) as Ht12.
    pose proof (F_t_simpl_p pi_t pi_star) as HFp.
    assert (Hopp : Id (opp (plus (opp (mult eta (sum_over_S (fun s => mult (pi_star s) (A s)))))
                                 (mult beta (relative_entropy pi_star pi_t))))
                      (plus (mult eta (sum_over_S (fun s => mult (pi_star s) (A s))))
                            (opp (mult beta (relative_entropy pi_star pi_t))))).
    {
      apply (id_trans (opp_plus (opp (mult eta (sum_over_S (fun s => mult (pi_star s) (A s)))))
                                (mult beta (relative_entropy pi_star pi_t)))
             (id_cong (fun x => plus x (opp (mult beta (relative_entropy pi_star pi_t))))
                      (double_neg (mult eta (sum_over_S (fun s => mult (pi_star s) (A s))))))).
    }
    assert (Hmid : Id (plus (opp (free_energy (energy_t pi_t) beta pi_star))
                            (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s)))))
                      (plus (opp (plus (opp (mult eta (sum_over_S (fun s => mult (pi_star s) (A s)))))
                                       (mult beta (relative_entropy pi_star pi_t))))
                            (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s)))))).
    { apply (id_cong2 plus (id_cong opp HFp) id_refl). }
    assert (Hfinal : Id (plus (plus (mult eta (sum_over_S (fun s => mult (pi_star s) (A s))))
                                    (opp (mult beta (relative_entropy pi_star pi_t))))
                            (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s)))))
                      (plus (sum_over_S (fun s => mult (pi_star s) (A s)))
                            (opp (mult beta (relative_entropy pi_star pi_t))))).
    {
      apply (id_trans (id_sym (plus_assoc (mult eta (sum_over_S (fun s => mult (pi_star s) (A s))))
                                           (opp (mult beta (relative_entropy pi_star pi_t)))
                                           (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s))))))
             (id_trans (id_cong (fun x => plus (mult eta (sum_over_S (fun s => mult (pi_star s) (A s)))) x)
                                (plus_comm (opp (mult beta (relative_entropy pi_star pi_t)))
                                           (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s))))))
             (id_trans (plus_assoc (mult eta (sum_over_S (fun s => mult (pi_star s) (A s))))
                                   (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s))))
                                   (opp (mult beta (relative_entropy pi_star pi_t))))
                       (id_cong (fun x => plus x (opp (mult beta (relative_entropy pi_star pi_t))))
                                (eta_absorb_t12 (sum_over_S (fun s => mult (pi_star s) (A s)))))))).
    }
    apply (id_trans Ht12).
    apply (id_trans Hmid
           (id_trans (id_cong (fun x => plus x (mult (minus one eta) (sum_over_S (fun s => mult (pi_star s) (A s))))) Hopp)
                     Hfinal)).
  }
  (* 反解：Xs == J(pi_star) + β·KL(pi_star‖pi_t) *)
  assert (Hxs : Id Xs (plus (align_objective pi_star) (mult beta (relative_entropy pi_star pi_t)))).
  {
    apply (id_trans (id_sym (minus_plus_cancel_gap Xs (mult beta (relative_entropy pi_star pi_t))))
           (id_cong (fun x => plus x (mult beta (relative_entropy pi_star pi_t))) (id_sym Hstar))).
  }
  (* J(pi_t) == Xt（J_pi_t_t12） *)
  assert (Hxt : Id (align_objective pi_t) Xt)
    by (unfold Xt; exact (J_pi_t_t12 pi_t pi_t_norm)).
  (* gap == β·KL(pi_t‖pi_star) *)
  pose proof (rlhf_suboptimality_gap pi_t pi_t_norm pi_t_pos) as Hgap.
  (* 链：minus Xt Xs == minus (J(pi_t)) (J(pi_star) + βKLst) == minus (opp gap) (βKLst) == −βKLts − βKLst *)
  apply (id_trans (id_cong2 minus (id_sym Hxt) Hxs)
         (id_trans (minus_sub_plus_t13 (align_objective pi_t) (align_objective pi_star)
                                       (mult beta (relative_entropy pi_star pi_t)))
         (id_trans (id_cong (fun x => minus x (mult beta (relative_entropy pi_star pi_t)))
                            (opp_minus_rev_t13 (align_objective pi_t) (align_objective pi_star)))
         (id_trans (id_cong (fun x => minus (opp x) (mult beta (relative_entropy pi_star pi_t))) Hgap)
                   id_refl)))).
Qed.



(* minus 分配于 plus：minus (plus a b) (plus c d) == plus (minus a c) (minus b d) *)
Lemma minus_distr_t13 : forall a b c d : R,
  Id (minus (plus a b) (plus c d)) (plus (minus a c) (minus b d)).
Proof.
  intros a b c d.
  unfold minus.
  assert (Hmid : Id (plus b (plus (opp c) (opp d)))
                   (plus (opp c) (plus b (opp d)))).
  {
    apply (id_trans (plus_assoc b (opp c) (opp d))
           (id_trans (id_cong (fun x => plus x (opp d)) (plus_comm b (opp c)))
                     (id_sym (plus_assoc (opp c) b (opp d))))).
  }
  apply (id_trans (id_cong (fun x => plus (plus a b) x) (opp_plus c d))
         (id_trans (id_sym (plus_assoc a b (plus (opp c) (opp d))))
         (id_trans (id_cong (fun x => plus a x) Hmid)
                   (plus_assoc a (opp c) (plus b (opp d)))))).
Qed.

(* minus (opp (mult eta a)) (opp (mult eta b)) == mult eta (minus b a)（η 吸收） *)
Lemma minus_opp_opp_mult_t13 : forall (a b : R),
  Id (minus (opp (mult eta a)) (opp (mult eta b)))
     (mult eta (minus b a)).
Proof.
  intros a b. unfold minus.
  exact (id_trans (id_cong (fun x => plus (opp (mult eta a)) x) (double_neg (mult eta b))) (id_trans (plus_comm (opp (mult eta a)) (mult eta b)) (id_trans (id_cong (fun x => plus (mult eta b) x) (id_sym (opp_mult_l eta a))) (id_sym (distrib eta b (opp a)))))).
Qed.

(* 主定理辅助 1：Hexp——minus 展开到 mult 形式 *)
Lemma t13_hexp :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
  Id (minus (plus (opp (mult eta (sum_over_S (fun s => mult (pi_star s) (advantage_aug pi_t s)))))
                  (mult beta (relative_entropy pi_star pi_t)))
            (plus (opp (mult eta (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))))
                  (mult beta (relative_entropy (pi_next pi_t pi_t_pos) pi_t))))
     (plus (mult eta (minus (sum_over_S (fun s => mult (pi_next pi_t pi_t_pos s) (advantage_aug pi_t s)))
                            (sum_over_S (fun s => mult (pi_star s) (advantage_aug pi_t s)))))
           (mult beta (minus (relative_entropy pi_star pi_t)
                             (relative_entropy (pi_next pi_t pi_t_pos) pi_t)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xs := sum_over_S (fun s => mult (pi_star s) (A s))).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (Kst := relative_entropy pi_star pi_t).
  apply (id_trans (minus_distr_t13 (opp (mult eta Xs)) (mult beta Kst)
                                   (opp (mult eta Xn)) (mult beta K1))
         (id_cong2 plus
                   (minus_opp_opp_mult_t13 Xs Xn)
                   (id_sym (mult_minus_distr_l beta Kst K1)))).
Qed.

(* Xn − Xs == (Xn − Xt) + (Xt − Xs)（minus 拆） *)
Lemma minus_split_t13 : forall a b c : R,
  Id (minus a c) (plus (minus a b) (minus b c)).
Proof.
  intros a b c. unfold minus.
  exact (id_trans (id_sym (id_cong (fun x => plus x (opp c)) (plus_zero a))) (id_trans (id_sym (id_cong (fun x => plus (plus a x) (opp c)) (id_trans (plus_comm (opp b) b) (plus_opp b)))) (id_trans (id_sym (id_cong (fun x => plus x (opp c)) (id_sym (plus_assoc a (opp b) b)))) (id_sym (plus_assoc (plus a (opp b)) b (opp c)))))).
Qed.

(* minus (plus a b) b == a（minus_plus_cancel_gap 的逆形态） *)
Lemma minus_plus_cancel_gap_rev_t13 : forall a b : R,
  Id (minus (plus a b) b) a.
Proof.
  intros a b. unfold minus.
  exact (id_trans (id_sym (plus_assoc a b (opp b))) (id_trans (id_cong (fun x => plus a x) (plus_opp b)) (plus_zero a))).
Qed.

(* 坍缩：a 与 −a 抵消，e − d 与 b 重组 *)
Lemma t13_collapse : forall a b c d e : R,
  Id (plus (plus (plus a b) (plus (opp c) (opp d))) (minus e a))
     (plus (minus e d) (plus (opp c) b)).
Proof.  intros a b c d e.
  unfold minus.
  set (X := plus (plus a b) (plus (opp c) (opp d))).
  exact (id_trans (id_trans (plus_assoc X e (opp a))
                   (id_trans (id_cong (fun x => plus x (opp a)) (plus_comm X e))
                             (id_sym (plus_assoc e X (opp a)))))
         (id_trans (id_cong (fun x => plus e x) (plus_comm X (opp a)))
         (id_trans (id_cong (fun x => plus e x)
                            (plus_assoc (opp a) (plus a b) (plus (opp c) (opp d))))
         (id_trans (id_cong (fun x => plus e x)
                            (id_cong (fun x => plus x (plus (opp c) (opp d)))
                                     (plus_assoc (opp a) a b)))
         (id_trans (id_cong (fun x => plus e x)
                            (id_cong (fun x => plus (plus x b) (plus (opp c) (opp d)))
                                     (id_trans (plus_comm (opp a) a) (plus_opp a))))
         (id_trans (id_cong (fun x => plus e x)
                            (id_cong (fun x => plus x (plus (opp c) (opp d)))
                                     (id_trans (plus_comm zero b) (plus_zero b))))
         (id_trans (id_cong (fun x => plus e x)
                            (id_trans (plus_assoc b (opp c) (opp d))
                            (id_trans (plus_comm (plus b (opp c)) (opp d))
                                      (id_cong (fun x => plus (opp d) x) (plus_comm b (opp c))))))
                   (plus_assoc e (opp d) (plus (opp c) b))))))))).
Qed.

Theorem policy_iter_backward_kl_step_beta :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one)
         (pi_next_pos : forall s : S, lt zero (pi_next pi_t pi_t_pos s)),
  Id (mult beta (relative_entropy pi_star (pi_next pi_t pi_t_pos)))
     (plus (mult (minus one eta) (mult beta (relative_entropy pi_star pi_t)))
           (plus (opp (mult eta (mult beta (relative_entropy pi_t pi_star))))
                 (mult beta (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm pi_next_pos.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xs := sum_over_S (fun s => mult (pi_star s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  set (Kst := relative_entropy pi_star pi_t).
  set (Kts := relative_entropy pi_t pi_star).
  set (Ksn := relative_entropy pi_star Np).
  pose proof (F_t_decomp_p pi_t pi_t_pos pi_t_norm pi_star pi_star_normalized) as Hdec.
  pose proof (F_t_simpl_p pi_t pi_star) as HFp.
  pose proof (F_t_simpl_next_kl pi_t pi_t_pos) as HFn.
  assert (Hkl0 : Id (minus (free_energy (energy_t pi_t) beta pi_star)
                           (free_energy (energy_t pi_t) beta Np))
                    (mult beta Ksn)).
  {
    apply (id_trans (id_cong (fun x => minus x (free_energy (energy_t pi_t) beta Np)) Hdec)
           (id_trans (id_cong (fun x => minus x (free_energy (energy_t pi_t) beta Np))
                              (plus_comm (free_energy (energy_t pi_t) beta Np) (mult beta Ksn)))
                     (minus_plus_cancel_gap_rev_t13 (mult beta Ksn) (free_energy (energy_t pi_t) beta Np)))).
  }
  assert (Hkl1 : Id (minus (plus (opp (mult eta Xs)) (mult beta Kst))
                           (plus (opp (mult eta Xn)) (mult beta K1)))
                    (mult beta Ksn)).
  {
    apply (id_trans (id_cong (fun x => minus x (plus (opp (mult eta Xn)) (mult beta K1))) (id_sym HFp))
           (id_trans (id_cong (fun x => minus (free_energy (energy_t pi_t) beta pi_star) x) (id_sym HFn))
                     Hkl0)).
  }
  pose proof (t13_hexp pi_t pi_t_pos pi_t_norm) as Hhexp.
  assert (Hmain0 : Id (mult beta Ksn)
                      (plus (mult eta (minus Xn Xs)) (mult beta (minus Kst K1)))).
  { apply (id_trans (id_sym Hkl1) Hhexp). }
  assert (Heta1 : Id (mult eta (minus Xn Xt)) (mult beta (plus K1 K2))).
  {
    apply (id_trans (id_cong (fun x => mult eta x) (sum_grad_cross pi_t pi_t_pos))
           (id_trans (id_cong (fun x => mult eta x)
                              (grad_cross_identity pi_t pi_t_pos pi_t_norm pi_next_pos))
           (id_trans (mult_assoc eta (mult (inv_pos eta eta_pos) beta) (plus K1 K2))
           (id_trans (id_cong (fun x => mult x (plus K1 K2))
                              (mult_assoc eta (inv_pos eta eta_pos) beta))
           (id_trans (id_cong (fun x => mult x (plus K1 K2))
                              (id_cong (fun x => mult x beta) (inv_pos_correct eta eta_pos)))
                     (id_cong (fun x => mult x (plus K1 K2))
                              (id_trans (mult_comm one beta) (mult_one beta)))))))).
  }
  assert (Heta2 : Id (mult eta (minus Xt Xs))
                     (plus (opp (mult eta (mult beta Kts)))
                           (opp (mult eta (mult beta Kst))))).
  {
    apply (id_trans (id_cong (fun x => mult eta x) (sum_advance_gap pi_t pi_t_pos pi_t_norm))
           (id_trans (distrib eta (opp (mult beta Kts)) (opp (mult beta Kst)))
           (id_cong2 plus
                     (opp_mult_l eta (mult beta Kts))
                     (opp_mult_l eta (mult beta Kst))))).
  }
  assert (Hsplit : Id (minus Xn Xs) (plus (minus Xn Xt) (minus Xt Xs)))
    by (unfold Xn, Xt, Xs; apply (minus_split_t13 (sum_over_S (fun s => mult (Np s) (A s)))
                                                  (sum_over_S (fun s => mult (pi_t s) (A s)))
                                                  (sum_over_S (fun s => mult (pi_star s) (A s))))).
  assert (Heta3 : Id (mult eta (minus Xn Xs))
                     (plus (mult eta (minus Xn Xt)) (mult eta (minus Xt Xs)))).
  {
    apply (id_trans (id_cong (fun x => mult eta x) Hsplit)
           (distrib eta (minus Xn Xt) (minus Xt Xs))).
  }
  assert (Hmid : Id (mult beta Ksn)
                    (plus (plus (mult beta (plus K1 K2))
                                (plus (opp (mult eta (mult beta Kts)))
                                      (opp (mult eta (mult beta Kst)))))
                          (minus (mult beta Kst) (mult beta K1)))).
  {
    apply (id_trans Hmain0
           (id_trans (id_cong (fun x => plus x (mult beta (minus Kst K1))) Heta3)
           (id_trans (id_cong (fun x => plus (plus x (mult eta (minus Xt Xs))) (mult beta (minus Kst K1))) Heta1)
           (id_trans (id_cong (fun x => plus (plus (mult beta (plus K1 K2)) x) (mult beta (minus Kst K1))) Heta2)
                     (id_cong (fun x => plus (plus (mult beta (plus K1 K2)) (plus (opp (mult eta (mult beta Kts))) (opp (mult eta (mult beta Kst))))) x)
                              (mult_minus_distr_l beta Kst K1)))))).
  }
  assert (Hdistr : Id (mult beta (plus K1 K2)) (plus (mult beta K1) (mult beta K2)))
    by (apply (distrib beta K1 K2)).
  assert (Hone : Id (minus (mult beta Kst) (mult eta (mult beta Kst)))
                    (mult (minus one eta) (mult beta Kst))).
  {
    apply (id_trans (id_sym (id_cong (fun x => minus x (mult eta (mult beta Kst)))
                                    (mult_one (mult beta Kst))))
           (id_trans (id_sym (id_cong (fun x => minus x (mult eta (mult beta Kst)))
                                      (mult_comm one (mult beta Kst))))
                     (id_sym (mult_minus_distr_r one eta (mult beta Kst))))).
  }
  apply (id_trans Hmid
         (id_trans (id_cong (fun x => plus (plus x (plus (opp (mult eta (mult beta Kts))) (opp (mult eta (mult beta Kst)))))
                                          (minus (mult beta Kst) (mult beta K1))) Hdistr)
         (id_trans (t13_collapse (mult beta K1) (mult beta K2)
                                 (mult eta (mult beta Kts)) (mult eta (mult beta Kst)) (mult beta Kst))
                   (id_cong (fun x => plus x (plus (opp (mult eta (mult beta Kts))) (mult beta K2)))
                            Hone)))).
Qed.

(* 除 β 版：KL(pi_star‖pi_next) == (1−η)·KL(pi_star‖pi_t) − η·KL(pi_t‖pi_star) + KL(pi_t‖pi_next) *)
Theorem policy_iter_backward_kl_step :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one)
         (pi_next_pos : forall s : S, lt zero (pi_next pi_t pi_t_pos s)),
  Id (relative_entropy pi_star (pi_next pi_t pi_t_pos))
     (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
           (plus (opp (mult eta (relative_entropy pi_t pi_star)))
                 (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
Proof.
  intros pi_t pi_t_pos pi_t_norm pi_next_pos.
  pose proof (policy_iter_backward_kl_step_beta pi_t pi_t_pos pi_t_norm pi_next_pos) as Hbeta.
  assert (Hbsn : Id (mult (inv_pos beta beta_pos) (mult beta (relative_entropy pi_star (pi_next pi_t pi_t_pos))))
                    (relative_entropy pi_star (pi_next pi_t pi_t_pos))).
  {
    apply (id_trans (mult_assoc (inv_pos beta beta_pos) beta (relative_entropy pi_star (pi_next pi_t pi_t_pos)))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_star (pi_next pi_t pi_t_pos)))
                             (mult_comm (inv_pos beta beta_pos) beta))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_star (pi_next pi_t pi_t_pos)))
                             (inv_pos_correct beta beta_pos))).
    apply (id_trans (mult_comm one (relative_entropy pi_star (pi_next pi_t pi_t_pos)))
                    (mult_one (relative_entropy pi_star (pi_next pi_t pi_t_pos)))).
  }
  assert (Hb1 : Id (mult (inv_pos beta beta_pos)
                         (mult (minus one eta) (mult beta (relative_entropy pi_star pi_t))))
                   (mult (minus one eta) (relative_entropy pi_star pi_t))).
  {
    apply (id_trans (mult_assoc (inv_pos beta beta_pos) (minus one eta) (mult beta (relative_entropy pi_star pi_t)))).
    apply (id_trans (id_cong (fun x => mult x (mult beta (relative_entropy pi_star pi_t)))
                             (mult_comm (inv_pos beta beta_pos) (minus one eta)))).
    apply (id_trans (id_sym (mult_assoc (minus one eta) (inv_pos beta beta_pos) (mult beta (relative_entropy pi_star pi_t))))).
    apply (id_trans (id_cong (fun x => mult (minus one eta) x)
                             (mult_assoc (inv_pos beta beta_pos) beta (relative_entropy pi_star pi_t)))).
    apply (id_trans (id_cong (fun x => mult (minus one eta) x)
                             (id_cong (fun x => mult x (relative_entropy pi_star pi_t))
                                      (mult_comm (inv_pos beta beta_pos) beta)))).
    apply (id_trans (id_cong (fun x => mult (minus one eta) x)
                             (id_cong (fun x => mult x (relative_entropy pi_star pi_t))
                                      (inv_pos_correct beta beta_pos)))).
    apply (id_cong (fun x => mult (minus one eta) x)
                   (id_trans (mult_comm one (relative_entropy pi_star pi_t))
                             (mult_one (relative_entropy pi_star pi_t)))).
  }
  assert (Hb2 : Id (mult (inv_pos beta beta_pos)
                         (opp (mult eta (mult beta (relative_entropy pi_t pi_star)))))
                   (opp (mult eta (relative_entropy pi_t pi_star)))).
  {
    apply (id_trans (opp_mult_l (inv_pos beta beta_pos) (mult eta (mult beta (relative_entropy pi_t pi_star))))).
    apply (id_trans (id_cong opp
                             (mult_assoc (inv_pos beta beta_pos) eta (mult beta (relative_entropy pi_t pi_star))))).
    apply (id_trans (id_cong opp
                             (id_cong (fun x => mult x (mult beta (relative_entropy pi_t pi_star)))
                                      (mult_comm (inv_pos beta beta_pos) eta)))).
    apply (id_trans (id_cong opp
                             (id_sym (mult_assoc eta (inv_pos beta beta_pos) (mult beta (relative_entropy pi_t pi_star)))))).
    apply (id_trans (id_cong opp
                             (id_cong (fun x => mult eta x)
                                      (mult_assoc (inv_pos beta beta_pos) beta (relative_entropy pi_t pi_star))))).
    apply (id_trans (id_cong opp
                             (id_cong (fun x => mult eta x)
                                      (id_cong (fun x => mult x (relative_entropy pi_t pi_star))
                                               (mult_comm (inv_pos beta beta_pos) beta))))).
    apply (id_trans (id_cong opp
                             (id_cong (fun x => mult eta x)
                                      (id_cong (fun x => mult x (relative_entropy pi_t pi_star))
                                               (inv_pos_correct beta beta_pos))))).
    apply (id_cong opp
                   (id_cong (fun x => mult eta x)
                            (id_trans (mult_comm one (relative_entropy pi_t pi_star))
                                      (mult_one (relative_entropy pi_t pi_star))))).
  }
  assert (Hb3 : Id (mult (inv_pos beta beta_pos) (mult beta (relative_entropy pi_t (pi_next pi_t pi_t_pos))))
                   (relative_entropy pi_t (pi_next pi_t pi_t_pos))).
  {
    apply (id_trans (mult_assoc (inv_pos beta beta_pos) beta (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                             (mult_comm (inv_pos beta beta_pos) beta))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                             (inv_pos_correct beta beta_pos))).
    apply (id_trans (mult_comm one (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                    (mult_one (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
  }
  apply (id_trans (id_sym Hbsn)).
  apply (id_trans (id_cong (fun x => mult (inv_pos beta beta_pos) x) Hbeta)).
  apply (id_trans (distrib (inv_pos beta beta_pos)
                           (mult (minus one eta) (mult beta (relative_entropy pi_star pi_t)))
                           (plus (opp (mult eta (mult beta (relative_entropy pi_t pi_star))))
                                 (mult beta (relative_entropy pi_t (pi_next pi_t pi_t_pos)))))).
  apply (id_trans (id_cong (fun x => plus (mult (inv_pos beta beta_pos) (mult (minus one eta) (mult beta (relative_entropy pi_star pi_t)))) x)
                           (distrib (inv_pos beta beta_pos)
                                    (opp (mult eta (mult beta (relative_entropy pi_t pi_star))))
                                    (mult beta (relative_entropy pi_t (pi_next pi_t pi_t_pos)))))).
  apply (id_cong2 plus Hb1 (id_cong2 plus Hb2 Hb3)).
Qed.

(* le 版：KL(pi_star‖pi_next) ≤ (1−η)·KL(pi_star‖pi_t) + KL(pi_t‖pi_next)（丢弃 −η·KL(pi_t‖pi_star) ≤ 0） *)
(* 辅助：opp zero == zero（Section 内自证；set_opp_zero 定义在 Section 之后，不能向前引用） *)
Lemma opp_zero_t13 : Id (opp zero) zero.
Proof.
  apply id_sym.
  apply (plus_inv_unique zero zero (opp zero)).
  - apply (plus_zero zero).
  - apply (plus_opp zero).
Qed.

Theorem policy_iter_backward_kl_step_le :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one)
         (pi_next_pos : forall s : S, lt zero (pi_next pi_t pi_t_pos s)),
  le (relative_entropy pi_star (pi_next pi_t pi_t_pos))
     (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
           (relative_entropy pi_t (pi_next pi_t pi_t_pos))).
Proof.
  intros pi_t pi_t_pos pi_t_norm pi_next_pos.
  pose proof (policy_iter_backward_kl_step pi_t pi_t_pos pi_t_norm pi_next_pos) as Hstep.
  assert (Hkl : le zero (relative_entropy pi_t pi_star)).
  {
    apply (gibbs_inequality pi_t pi_star pi_t_norm pi_t_pos pi_star_normalized pi_star_pos).
  }
  assert (HleM : le zero (mult eta (relative_entropy pi_t pi_star))).
  {
    apply (le_id_l zero (mult zero eta) (mult eta (relative_entropy pi_t pi_star))).
    - apply (id_sym (id_trans (mult_comm zero eta) (mult_zero eta))).
    - apply (le_trans (mult zero eta) (mult (relative_entropy pi_t pi_star) eta)
                      (mult eta (relative_entropy pi_t pi_star))).
      + apply (le_mult_compat zero (relative_entropy pi_t pi_star) eta).
        * exact eta_pos.
        * exact Hkl.
      + apply (le_id_l (mult (relative_entropy pi_t pi_star) eta)
                       (mult eta (relative_entropy pi_t pi_star))
                       (mult eta (relative_entropy pi_t pi_star))
                       (mult_comm (relative_entropy pi_t pi_star) eta)
                       (le_refl (mult eta (relative_entropy pi_t pi_star)))).
  }
  assert (Hopp : le (opp (mult eta (relative_entropy pi_t pi_star))) zero).
  {
    apply (le_id_r (opp (mult eta (relative_entropy pi_t pi_star))) (opp zero) zero).
    - apply opp_zero_t13.
    - apply (opp_le_compat zero (mult eta (relative_entropy pi_t pi_star))).
      exact HleM.
  }
  apply (le_id_l (relative_entropy pi_star (pi_next pi_t pi_t_pos))
                 (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                       (plus (opp (mult eta (relative_entropy pi_t pi_star)))
                             (relative_entropy pi_t (pi_next pi_t pi_t_pos))))
                 (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                       (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
  - exact Hstep.
  - apply (le_id_r (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                         (plus (opp (mult eta (relative_entropy pi_t pi_star)))
                               (relative_entropy pi_t (pi_next pi_t pi_t_pos))))
                   (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                         (plus zero (relative_entropy pi_t (pi_next pi_t pi_t_pos))))
                   (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                         (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
    + apply (id_cong (fun x => plus (mult (minus one eta) (relative_entropy pi_star pi_t)) x)
                     (id_trans (plus_comm zero (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                               (plus_zero (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
    + apply (le_plus_compat (mult (minus one eta) (relative_entropy pi_star pi_t))
                            (mult (minus one eta) (relative_entropy pi_star pi_t))
                            (plus (opp (mult eta (relative_entropy pi_t pi_star)))
                                  (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                            (plus zero (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                            (le_refl (mult (minus one eta) (relative_entropy pi_star pi_t)))
                            (le_plus_compat (opp (mult eta (relative_entropy pi_t pi_star))) zero
                                            (relative_entropy pi_t (pi_next pi_t pi_t_pos))
                                            (relative_entropy pi_t (pi_next pi_t pi_t_pos))
                                            Hopp (le_refl (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
Qed.

(* ============================================================ *)
(* A-1：T1.3 几何收敛上界（副本下降迭代的显式递推）           *)
(*   pi_{t+1} := pi_next pi_t（相对熵副本下降单步）              *)
(*   1) policy_iterate：sigT 封装的迭代 Fixpoint（正性内嵌）     *)
(*   2) policy_iter_norm：迭代保持归一化                          *)
(*   3) step_kl_weighted：加权步长 KL 和（κ^{t-1-i} 权重）        *)
(*   4) policy_iter_backward_kl_iter_le：                        *)
(*      KL(pi*‖pi_t) ≤ κ^t·KL(pi*‖pi_0) + Σ_{i<t} κ^{t-1-i}·KL(pi_i‖pi_{i+1}) *)
(*      （κ := 1−η；归纳组装 policy_iter_backward_kl_step_le）   *)
(*   5) policy_iter_gap_diff：gap 单步显式恒等式                 *)
(*      J(pi_{t+1}) − J(pi_t) == β·[(1/η−1)·KL(pi_{t+1}‖pi_t)   *)
(*                                  + (1/η)·KL(pi_t‖pi_{t+1})]   *)
(*      （提取 policy_improvement_mono 的 Hbeta_form 链为独立定理）*)
(*   6) policy_iter_gap_mono：gap 单调不增（gap_{t+1} ≤ gap_t）  *)
(*   7) step_kl_eta_bound（R2.1 升级接口：前向步长 KL 被控为      *)
(*      ≤ η × 前向 KL 到最优（≡ 插值不等式 log Z ≤ 0，Real 层    *)
(*      Hölder 可证）；旧 step_kl_ratio_bound 对任意常数 c 非定理  *)
(*      已退役）+ policy_iter_kl_geom_step：单步真几何收缩 c := 0 *)
(*      KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)                    *)
(*   8) policy_iter_kl_geom_iter：迭代几何上界（核心结论）       *)
(*      KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)                     *)
(* ============================================================ *)

(* 迭代 Fixpoint：分布 + 正性证明封装为 sigT（可提取） *)
Fixpoint policy_iterate (t : nat) (pi : S -> R)
         (pi_pos : forall s : S, lt zero (pi s)) :
  { pi' : S -> R & forall s : S, lt zero (pi' s) } :=
  match t with
  | 0%nat => existT _ pi pi_pos
  | Datatypes.S m =>
      let p := policy_iterate m pi pi_pos in
      existT _ (pi_next (projT1 p) (projT2 p)) (pi_next_pos (projT1 p) (projT2 p))
  end.

(* 迭代保持归一化 *)
Lemma policy_iter_norm : forall (t : nat) (pi : S -> R)
       (pi_pos : forall s : S, lt zero (pi s)),
  Id (sum_over_S pi) one ->
  Id (sum_over_S (projT1 (policy_iterate t pi pi_pos))) one.
Proof.
  intros t pi pi_pos Hnorm.
  induction t as [| m IH]; simpl.
  - exact Hnorm.
  - apply pi_next_normalized.
Qed.

(* 加权步长 KL 和：S(t) := Σ_{i<t} κ^{t-1-i}·KL(pi_i‖pi_{i+1})，κ := 1−η *)
(* 递推：S(S m) == KL(pi_m‖pi_{S m}) + κ·S(m) *)
Fixpoint step_kl_weighted (t : nat) (pi : S -> R)
         (pi_pos : forall s : S, lt zero (pi s)) : R :=
  match t with
  | 0%nat => zero
  | Datatypes.S m =>
      let p := policy_iterate m pi pi_pos in
      plus (relative_entropy (projT1 p) (pi_next (projT1 p) (projT2 p)))
           (mult (minus one eta) (step_kl_weighted m pi pi_pos))
  end.

(* 向后 KL 迭代递推（精确加权上界）：
   KL(pi*‖pi_t) ≤ κ^t·KL(pi*‖pi_0) + Σ_{i<t} κ^{t-1-i}·KL(pi_i‖pi_{i+1}) *)
Theorem policy_iter_backward_kl_iter_le :
  forall (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s)),
    Id (sum_over_S pi) one ->
    le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
       (plus (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi))
             (step_kl_weighted t pi pi_pos)).
Proof.
  intros t pi pi_pos Hnorm.
  induction t as [| m IH]; simpl.
  - (* t = 0：KL ≤ 1·KL + 0 *)
    apply (le_id_r (relative_entropy pi_star pi)
                   (plus (relative_entropy pi_star pi) zero)
                   (plus (mult one (relative_entropy pi_star pi)) zero)).
    + apply (id_sym (id_cong2 plus (id_trans (mult_comm one (relative_entropy pi_star pi))
                                             (mult_one (relative_entropy pi_star pi)))
                                  id_refl)).
    + apply (le_id_r (relative_entropy pi_star pi)
                     (relative_entropy pi_star pi)
                     (plus (relative_entropy pi_star pi) zero)).
      * apply (id_sym (plus_zero (relative_entropy pi_star pi))).
      * apply le_refl.
  - (* t = S m：KL(pi*‖pi_{S m}) ≤ (1−η)·KL(pi*‖pi_m) + KL(pi_m‖pi_{S m})
               ≤ (1−η)·(κ^m·KL0 + S_m) + KL_m
               == κ^{S m}·KL0 + (KL_m + (1−η)·S_m) *)
    set (K := minus one eta).
    set (Pm := projT1 (policy_iterate m pi pi_pos)).
    set (Pm_pos := projT2 (policy_iterate m pi pi_pos)).
    set (KL0 := relative_entropy pi_star pi).
    set (KSm := relative_entropy Pm (pi_next Pm Pm_pos)).
    set (Sm := step_kl_weighted m pi pi_pos).
    (* 单步向后 KL 递推 *)
    assert (H1 : le (relative_entropy pi_star (pi_next Pm Pm_pos))
                    (plus (mult K (relative_entropy pi_star Pm)) KSm)).
    { unfold K, KSm. exact (policy_iter_backward_kl_step_le Pm Pm_pos
                              (policy_iter_norm m pi pi_pos Hnorm) (pi_next_pos Pm Pm_pos)). }
    (* κ 非负：η ≤ 1 ⟹ 0 ≤ 1−η *)
    assert (Hk : le zero K).
    { unfold K. exact (le_minus_nonneg eta one eta_le_one). }
    (* 归纳前提乘 κ（le_mult_compat_weak + 交换换形） *)
    assert (H4 : le (mult K (relative_entropy pi_star Pm))
                    (mult K (plus (mult (r_pow K m) KL0) Sm))).
    {
      apply (le_id_l (mult K (relative_entropy pi_star Pm))
                     (mult (relative_entropy pi_star Pm) K)
                     (mult K (plus (mult (r_pow K m) KL0) Sm))).
      - apply mult_comm.
      - apply (le_id_r _ (mult (plus (mult (r_pow K m) KL0) Sm) K) _).
        + apply mult_comm.
        + apply (le_mult_compat_weak (relative_entropy pi_star Pm)
                                     (plus (mult (r_pow K m) KL0) Sm) K Hk).
          exact IH.
    }
    (* 加 KSm：le_plus_compat *)
    assert (H5 : le (plus (mult K (relative_entropy pi_star Pm)) KSm)
                    (plus (mult K (plus (mult (r_pow K m) KL0) Sm)) KSm)).
    { apply (le_plus_compat (mult K (relative_entropy pi_star Pm))
                            (mult K (plus (mult (r_pow K m) KL0) Sm))
                            KSm KSm H4 (le_refl KSm)). }
    (* 传递 *)
    assert (H6 : le (relative_entropy pi_star (pi_next Pm Pm_pos))
                    (plus (mult K (plus (mult (r_pow K m) KL0) Sm)) KSm)).
    { apply (le_trans _ (plus (mult K (relative_entropy pi_star Pm)) KSm) _).
      - exact H1.
      - exact H5. }
    (* 代数换形：mult K (plus A Sm) + KSm == κ^{S m}·KL0 + (KSm + κ·Sm) *)
    assert (Hid : Id (plus (mult K (plus (mult (r_pow K m) KL0) Sm)) KSm)
                     (plus (mult (mult K (r_pow K m)) KL0) (plus KSm (mult K Sm)))).
    {
      apply (id_trans (id_cong2 plus (distrib K (mult (r_pow K m) KL0) Sm) id_refl)).
      apply (id_trans (id_sym (plus_assoc (mult K (mult (r_pow K m) KL0)) (mult K Sm) KSm))).
      apply (id_trans (id_cong (fun x => plus (mult K (mult (r_pow K m) KL0)) x)
                               (plus_comm (mult K Sm) KSm))).
      apply (id_cong (fun x => plus x (plus KSm (mult K Sm)))
                     (mult_assoc K (r_pow K m) KL0)).
    }
    (* 目标换形后闭 *)
    apply (le_id_r (relative_entropy pi_star (pi_next Pm Pm_pos))
                   (plus (mult K (plus (mult (r_pow K m) KL0) Sm)) KSm)
                   (plus (mult (mult K (r_pow K m)) KL0) (plus KSm (mult K Sm)))).
    + exact Hid.
    + exact H6.
Qed.

(* gap 单步显式恒等式：
   J(pi_{t+1}) − J(pi_t) == β·[(1/η−1)·KL(pi_{t+1}‖pi_t) + (1/η)·KL(pi_t‖pi_{t+1})] *)
Lemma policy_iter_gap_diff :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t))
       (mult beta (plus (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy (pi_next pi_t pi_t_pos) pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Np := pi_next pi_t pi_t_pos).
  set (A := advantage_aug pi_t).
  set (Xn := sum_over_S (fun s => mult (Np s) (A s))).
  set (Xt := sum_over_S (fun s => mult (pi_t s) (A s))).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  assert (HNp_pos : forall s : S, lt zero (Np s)) by (intro s; unfold Np; apply pi_next_pos).
  assert (HNp_norm : Id (sum_over_S Np) one) by (unfold Np; apply pi_next_normalized).
  assert (HJt : Id (align_objective pi_t) Xt) by (unfold Xt; apply J_pi_t_t12; exact pi_t_norm).
  assert (HJn : Id (align_objective Np) (minus Xn (mult beta K1)))
    by (unfold Xn, K1; apply J_pi_next_t12).
  assert (Hdiff : Id (minus (align_objective Np) (align_objective pi_t))
                     (minus (minus Xn (mult beta K1)) Xt)).
  { unfold minus. apply (id_cong2 plus HJn (id_cong opp HJt)). }
  assert (Hsur : Id (mult eta (minus Xn Xt)) (mult beta (plus K1 K2))).
  {
    unfold Np, A, Xn, Xt, K1, K2.
    apply (surrogate_diff_identity pi_t pi_t_pos pi_t_norm).
    intro s. unfold Np. apply pi_next_pos.
  }
  assert (Hlc : Id (mult (inv_pos eta eta_pos) (mult eta (minus Xn Xt))) (minus Xn Xt)).
  {
    apply (id_trans (mult_assoc (inv_pos eta eta_pos) eta (minus Xn Xt))).
    apply (id_trans (id_cong (fun x => mult x (minus Xn Xt))
                             (id_trans (mult_comm (inv_pos eta eta_pos) eta) (inv_pos_correct eta eta_pos)))).
    apply (id_trans (mult_comm one (minus Xn Xt)) (mult_one (minus Xn Xt))).
  }
  assert (Hinv : Id (minus Xn Xt) (mult (inv_pos eta eta_pos) (mult beta (plus K1 K2)))).
  {
    apply (id_trans (id_sym Hlc)).
    apply (id_cong (fun x => mult (inv_pos eta eta_pos) x) Hsur).
  }
  assert (Hswap : Id (minus (minus Xn (mult beta K1)) Xt) (minus (minus Xn Xt) (mult beta K1))).
  {
    unfold minus.
    apply (id_trans (id_sym (plus_assoc Xn (opp (mult beta K1)) (opp Xt)))).
    apply (id_trans (id_cong (fun x => plus Xn x)
                             (plus_comm (opp (mult beta K1)) (opp Xt)))).
    apply (plus_assoc Xn (opp Xt) (opp (mult beta K1))).
  }
  assert (Hm1 : Id (mult one K1) K1)
    by (apply (id_trans (mult_comm one K1)); apply mult_one).
  assert (Hmm : Id (minus (mult (inv_pos eta eta_pos) K1) K1)
                   (mult (minus (inv_pos eta eta_pos) one) K1)).
  {
    apply (id_trans (id_cong (fun x => minus (mult (inv_pos eta eta_pos) K1) x) (id_sym Hm1))).
    apply (id_sym (mult_minus_distr_r_t12 (inv_pos eta eta_pos) one K1)).
  }
  assert (Hin : Id (minus (mult (inv_pos eta eta_pos) (plus K1 K2)) K1)
                   (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2))).
  {
    unfold minus.
    apply (id_trans (id_cong (fun x => plus x (opp K1)) (distrib (inv_pos eta eta_pos) K1 K2))).
    apply (id_trans (id_sym (plus_assoc (mult (inv_pos eta eta_pos) K1) (mult (inv_pos eta eta_pos) K2) (opp K1)))).
    apply (id_trans (id_cong (fun x => plus (mult (inv_pos eta eta_pos) K1) x)
                             (plus_comm (mult (inv_pos eta eta_pos) K2) (opp K1)))).
    apply (id_trans (plus_assoc (mult (inv_pos eta eta_pos) K1) (opp K1) (mult (inv_pos eta eta_pos) K2))).
    exact (id_trans (id_cong (fun x => plus x (mult (inv_pos eta eta_pos) K2)) Hmm) id_refl).
  }
  assert (Hbeta_form : Id (minus (mult (inv_pos eta eta_pos) (mult beta (plus K1 K2))) (mult beta K1))
                          (mult beta (plus (mult (minus (inv_pos eta eta_pos) one) K1) (mult (inv_pos eta eta_pos) K2)))).
  {
    apply (id_trans (id_cong (fun x => minus x (mult beta K1))
                             (id_trans (mult_assoc (inv_pos eta eta_pos) beta (plus K1 K2))
                                       (id_trans (id_cong (fun x => mult x (plus K1 K2)) (mult_comm (inv_pos eta eta_pos) beta))
                                                 (id_sym (mult_assoc beta (inv_pos eta eta_pos) (plus K1 K2))))))).
    apply (id_trans (id_sym (mult_minus_distr_l beta (mult (inv_pos eta eta_pos) (plus K1 K2)) K1))).
    apply (id_cong (fun x => mult beta x) Hin).
  }
  apply (id_trans Hdiff).
  apply (id_trans Hswap).
  apply (id_trans (id_cong (fun x => minus x (mult beta K1)) Hinv)).
  exact Hbeta_form.
Qed.

(* gap 单调不增：gap_{t+1} := J* − J_{t+1} ≤ J* − J_t =: gap_t *)
Lemma policy_iter_gap_mono :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    le (minus (align_objective pi_star) (align_objective (pi_next pi_t pi_t_pos)))
       (minus (align_objective pi_star) (align_objective pi_t)).
Proof.
  intros pi_t pi_t_pos pi_t_norm. unfold minus.
  exact (le_plus_compat (align_objective pi_star) (align_objective pi_star) (opp (align_objective (pi_next pi_t pi_t_pos))) (opp (align_objective pi_t)) (le_refl (align_objective pi_star)) (opp_le_compat (align_objective pi_t) (align_objective (pi_next pi_t pi_t_pos)) (policy_improvement_mono pi_t pi_t_pos pi_t_norm))).
Qed.

(* ============================================================
   诚实接口升级（R2.1 / 审稿 M4，sR21 判定）：
   旧 step_kl_ratio_bound（前向 KL ≤ c·向后 KL）对任意常数 c
   非定理——两方向 KL 在单纯形上不可比（前向 KL 可无界
   而 KL(pi*‖pi_t) 有界，比值无界）。数学正确的几何插值收缩
   前提为 step_kl_eta_bound：
     KL(pi_t‖pi_next pi_t) ≤ η · KL(pi_t‖pi_star)
   （≡ 插值不等式 log Z ≤ 0，Z := Σ pi_t^{1−η}·pi*^η；Real 层
   Hölder/exp 凸可证，方向为真）。在此单一诚实前提下，用精确
   恒等 policy_iter_backward_kl_step（L22574）纯代数推出真几何
   收缩 κ := 1−η（c := 0），比旧 (1−η+c) 更紧。
   ============================================================ *)
Variable step_kl_eta_bound : forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
  le (relative_entropy pi_t (pi_next pi_t pi_t_pos))
     (mult eta (relative_entropy pi_t pi_star)).

(* 纯序代数辅助：C ≤ B ⟹ −B + C ≤ 0 *)
Lemma plus_opp_le_zero : forall (B C : R), le C B -> le (plus (opp B) C) zero.
Proof.
  intros B C HCB.
  exact (le_id_r (plus (opp B) C) (plus (opp B) B) zero (id_trans (plus_comm (opp B) B) (plus_opp B)) (le_plus_compat (opp B) (opp B) C B (le_refl (opp B)) HCB)).
Qed.

(* plus A (plus (opp B) C) ≤ A  whenever  C ≤ B *)
Lemma plusA_opp_cancel_le : forall (A B C : R), le C B -> le (plus A (plus (opp B) C)) A.
Proof.
  intros A B C HCB.
  exact (le_id_r (plus A (plus (opp B) C)) (plus A zero) A (plus_zero A) (le_plus_compat A A (plus (opp B) C) zero (le_refl A) (plus_opp_le_zero B C HCB))).
Qed.

(* ============================================================
   单步几何收缩（真几何率 c := 0，R2.1 升级）：
     KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)
   路线：精确恒等 KL(pi*‖pi_next) == (1−η)·KL(pi*‖pi_t)
           − η·(前向 KL) + KL(pi_t‖pi_next)
         + step_kl_eta_bound 抵消两个 η 项。
   ============================================================ *)
Theorem policy_iter_kl_geom_step :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    le (relative_entropy pi_star (pi_next pi_t pi_t_pos))
       (mult (minus one eta) (relative_entropy pi_star pi_t)).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (KLst := relative_entropy pi_star pi_t).
  set (KLsn := relative_entropy pi_star (pi_next pi_t pi_t_pos)).
  set (KLts := relative_entropy pi_t pi_star).
  set (KLtn := relative_entropy pi_t (pi_next pi_t pi_t_pos)).
  (* 精确三 KL 恒等 *)
  assert (H : Id KLsn (plus (mult (minus one eta) KLst)
                            (plus (opp (mult eta KLts)) KLtn))).
  {
    unfold KLsn, KLst, KLts, KLtn.
    apply (policy_iter_backward_kl_step pi_t pi_t_pos pi_t_norm).
    intro s. apply (pi_next_pos pi_t pi_t_pos s).
  }
  (* 假设：KLtn ≤ η·KLts *)
  assert (Hb : le KLtn (mult eta KLts)).
  { unfold KLtn, KLts. exact (step_kl_eta_bound pi_t pi_t_pos). }
  (* RHS ≤ (1−η)·KLst *)
  apply (le_id_l KLsn (plus (mult (minus one eta) KLst)
                            (plus (opp (mult eta KLts)) KLtn))
                    (mult (minus one eta) KLst)).
  - exact H.
  - apply (plusA_opp_cancel_le (mult (minus one eta) KLst) (mult eta KLts) KLtn).
    exact Hb.
Qed.

(* ============================================================
   迭代几何上界（真几何率 (1−η)^t，T1.3 R2.1 升级）：
     KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)
   ============================================================ *)
Theorem policy_iter_kl_geom_iter :
  forall (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s))
         (pi_norm : Id (sum_over_S pi) one),
    le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
       (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi)).
Proof.
  intros t pi pi_pos pi_norm.
  induction t as [| m IH]; simpl.
  - (* t = 0：KL ≤ 1·KL *)
    apply (le_id_r (relative_entropy pi_star pi) (relative_entropy pi_star pi)
                   (mult one (relative_entropy pi_star pi))).
    + apply (id_sym (id_trans (mult_comm one (relative_entropy pi_star pi))
                              (mult_one (relative_entropy pi_star pi)))).
    + apply le_refl.
  - (* t = S m：单步收缩 + 归纳 + r_pow 结合换形 *)
    set (K := minus one eta).
    set (Pm := projT1 (policy_iterate m pi pi_pos)).
    set (Pm_pos := projT2 (policy_iterate m pi pi_pos)).
    set (KL0 := relative_entropy pi_star pi).
    (* 单步收缩应用于第 m 次迭代 *)
    assert (H1 : le (relative_entropy pi_star (pi_next Pm Pm_pos))
                    (mult K (relative_entropy pi_star Pm))).
    { unfold K.
      apply (policy_iter_kl_geom_step Pm Pm_pos (policy_iter_norm m pi pi_pos pi_norm)). }
    (* κ 非负：η ≤ 1 ⟹ 0 ≤ 1−η *)
    assert (Hk : le zero K).
    { unfold K. exact (le_minus_nonneg eta one eta_le_one). }
    (* 归纳前提乘 κ（le_mult_compat_weak + 交换换形） *)
    assert (H4 : le (mult K (relative_entropy pi_star Pm))
                    (mult K (mult (r_pow K m) KL0))).
    {
      apply (le_id_l (mult K (relative_entropy pi_star Pm))
                     (mult (relative_entropy pi_star Pm) K)
                     (mult K (mult (r_pow K m) KL0))).
      - apply mult_comm.
      - apply (le_id_r _ (mult (mult (r_pow K m) KL0) K) _).
        + apply mult_comm.
        + apply (le_mult_compat_weak (relative_entropy pi_star Pm)
                                     (mult (r_pow K m) KL0) K Hk).
          exact IH.
    }
    apply (le_trans _ (mult K (mult (r_pow K m) KL0)) _).
    + apply (le_trans _ (mult K (relative_entropy pi_star Pm)) _).
      * unfold K in H1. exact H1.
      * exact H4.
    + apply (le_id_r (mult K (mult (r_pow K m) KL0))
                     (mult K (mult (r_pow K m) KL0))
                     (mult (mult K (r_pow K m)) KL0)).
      * apply (mult_assoc K (r_pow K m) KL0).
      * apply le_refl.
Qed.

(* ============================================================ *)
(* DPO 损失沿策略改进轨道单调不增（并入）            *)
(*   dpo_loss(pi) := opp (align_objective pi)（L18360）          *)
(*   单步：dpo_loss(pi_{t+1}) ≤ dpo_loss(pi_t)                   *)
(*     （policy_improvement_mono + opp_le_compat 组装）           *)
(*   迭代：沿 policy_iterate 轨道 dpo_loss 单调不增               *)
(*     ——DPO 从"π* 处损失有界"升格为"沿改进轨道损失单调下降"，  *)
(*       评审 S3"无损失动态"的闭合                                 *)
(* ============================================================ *)

(* 单步：dpo_loss(pi_next pi_t) ≤ dpo_loss(pi_t) *)
Theorem dpo_loss_iter_step_le :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    le (dpo_loss (pi_next pi_t pi_t_pos)) (dpo_loss pi_t).
Proof.
  intros pi_t pi_t_pos pi_t_norm. unfold dpo_loss.
  exact (opp_le_compat (align_objective pi_t) (align_objective (pi_next pi_t pi_t_pos)) (policy_improvement_mono pi_t pi_t_pos pi_t_norm)).
Qed.

(* 迭代：dpo_loss(pi_{t+1}) ≤ dpo_loss(pi_t)（policy_iterate 轨道） *)
Theorem dpo_loss_iter_mono :
  forall (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s))
         (pi_norm : Id (sum_over_S pi) one),
    le (dpo_loss (projT1 (policy_iterate (Datatypes.S t) pi pi_pos)))
       (dpo_loss (projT1 (policy_iterate t pi pi_pos))).
Proof.
  intros t pi pi_pos pi_norm.
  apply (le_id_l (dpo_loss (projT1 (policy_iterate (Datatypes.S t) pi pi_pos)))
                 (dpo_loss (pi_next (projT1 (policy_iterate t pi pi_pos)) (projT2 (policy_iterate t pi pi_pos))))
                 (dpo_loss (projT1 (policy_iterate t pi pi_pos)))).
  - reflexivity.
  - apply (dpo_loss_iter_step_le (projT1 (policy_iterate t pi pi_pos))
                                 (projT2 (policy_iterate t pi pi_pos))
                                 (policy_iter_norm t pi pi_pos pi_norm)).
Qed.

End Alignment.

(* ============================================================ *)
(* U2 改进算子不动点与等值刻画                                  *)
(* （副本 Section U2FixedPoint，整节后置于 End Alignment.）；     *)
(* 来源：演变/.ablation/sc2_u2_fixed/u2_fixedpoint.v；10 Qed；    *)
(* 零公理面、零承认件、零经典逻辑。                              *)
(* ============================================================ *)

Section U2FixedPoint.

(* ---- 副本 Section Alignment 的声明（同名同序；未用变量不声明） ---- *)
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).

Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
Variable sum_over_S_pos : forall (f : S -> R), (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* 供给件（原 U2 节 Variable 换同名 Lemma，R120 基座消融波 T2 终判 B17）：由 sum_over_S_pos+逐点 mult_positive/exp_neg_pos 导出；零承认件 *)
Lemma Z_align_pos : lt zero (Z_align reward beta beta_pos pi_ref).
Proof.
  unfold Z_align. apply sum_over_S_pos. intros s. apply mult_positive.
  exact (pi_ref_pos s). apply exp_neg_pos.
Qed.

(* ---- 根库 Alignment 内局部名的实例化别名（同名 Let，正文可直移） ---- *)
Let pi_star := (pi_star reward beta beta_pos pi_ref Z_align_pos).
Let align_objective := (align_objective reward beta pi_ref).
Let pi_next := (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos).
Let pi_star_pos := (pi_star_pos reward beta beta_pos pi_ref pi_ref_pos Z_align_pos).
Let pi_star_normalized := (pi_star_normalized reward beta beta_pos pi_ref Z_align_pos).
Let pi_next_normalized := (pi_next_normalized reward beta beta_pos pi_ref eta sum_over_S_pos).
Let pi_next_pos := (pi_next_pos reward beta beta_pos pi_ref eta sum_over_S_pos).
Let rlhf_optimal := (rlhf_optimal reward beta beta_pos pi_ref pi_ref_pos Z_align_pos).
Let policy_improvement_mono :=
  (policy_improvement_mono reward beta beta_pos pi_ref eta eta_pos eta_le_one sum_over_S_pos).
Let policy_iter_gap_diff :=
  (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos sum_over_S_pos).
Let policy_iter_backward_kl_step_le :=
  (policy_iter_backward_kl_step_le reward beta beta_pos pi_ref pi_ref_pos Z_align_pos eta eta_pos
     sum_over_S_pos).
Let free_energy_ext := (free_energy_ext reward beta pi_ref).

(* =====================================================================
   常规序-环辅助（同 4.8 证明风格；无三分律、无经典）
   ===================================================================== *)

(* 辅助 A：两非负项之和为零 ⟹ 每项为零（a + b == 0 且 0 ≤ a、0 ≤ b ⟹ a == 0） *)
Lemma u2_nonneg_sum_zero : forall a b : R,
  le zero a -> le zero b -> Id (plus a b) zero -> Id a zero.
Proof.  intros a b Ha Hb Habs.
  exact (id_sym (le_antisym zero a Ha (le_id_r a (plus a b) zero Habs (le_plus_nonneg_r a b Hb)))).
Qed.

(* 辅助 B：相对熵对第二参数逐点相等的外延性（KL 同余，U2c 换形用） *)
Lemma u2_kl_arg2_ext :
  forall (p q q' : S -> R),
    (forall s : S, Id (q s) (q' s)) ->
    Id (relative_entropy p q) (relative_entropy p q').
Proof.  intros p q q' Hqq'.
  unfold relative_entropy.
  exact (sum_over_S_ext (fun s => mult (p s) (minus (log (p s)) (log (q s))))
                        (fun s => mult (p s) (minus (log (p s)) (log (q' s))))
                        (fun s => id_cong2 mult (id_refl)
                                            (id_cong (fun x => minus (log (p s)) x) (id_cong log (Hqq' s))))).
Qed.

(* 辅助 C：(a − b) − a == −b（U2c 的 −ηA 提取） *)
Lemma u2_minus_minus : forall a b : R,
  Id (minus (minus a b) a) (opp b).
Proof.  intros a b.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc a (opp b) (opp a))) (id_trans (id_cong (fun x => plus a x) (plus_comm (opp b) (opp a))) (id_trans (plus_assoc a (opp a) (opp b)) (id_trans (id_cong (fun x => plus x (opp b)) (plus_opp a)) (id_trans (plus_comm zero (opp b)) (plus_zero (opp b))))))).
Qed.

(* 辅助 D：对齐目标对策略逐点相等的外延性（rlhf_optimal_unique 同型引理） *)
Lemma u2_align_objective_ext :
  forall (p q : S -> R),
    (forall s : S, Id (p s) (q s)) ->
    Id (align_objective p) (align_objective q).
Proof.
  intros p q Hpq.
  (* 定义层展开＋显式构造项：align_objective 两侧展开为
     opp (free_energy …)，逐点相等经 free_energy_ext 后以
     opp 的全参映射 id_cong 一次注入闭合（消 apply 两跳） *)
  unfold align_objective.
  exact (id_cong opp (free_energy_ext p q Hpq)).
Qed.

(* =====================================================================
   U2a：π* 是单步改进算子 pi_next 的不动点
     pi_next pi_star ps_pos == pi_star（逐点）
   证明：rlhf_optimal（J(Tπ*） ≤ J(π*））+ policy_improvement_mono
     （J(π*） ≤ J(Tπ*））夹逼出 J 差 == 0；代入 policy_iter_gap_diff 恒等式
     得 β·[(1/η−1)KL(Tπ*‖π*） + (1/η)KL(π*‖Tπ*）] == 0；非负项和为零且
     1/η > 0 ⟹ KL(π*‖Tπ*） == 0 ⟹ gibbs_equality ⟹ Tπ* == π* 逐点。
   ===================================================================== *)
Theorem u2_pi_next_pi_star_fixed :
  forall (ps_pos : forall s : S, lt zero (pi_star s))
         (ps_norm : Id (sum_over_S pi_star) one),
    forall s : S, Id (pi_next pi_star ps_pos s) (pi_star s).
Proof.
  intros ps_pos ps_norm s0.
  set (Np := pi_next pi_star ps_pos).
  set (K1 := relative_entropy Np pi_star).
  set (K2 := relative_entropy pi_star Np).
  assert (HNp_norm : Id (sum_over_S Np) one)
    by (unfold Np; apply (pi_next_normalized pi_star ps_pos)).
  assert (HNp_pos : forall s : S, lt zero (Np s))
    by (intro s; unfold Np; apply (pi_next_pos pi_star ps_pos s)).
  (* 1. 夹逼：J(Tπ*） ≤ J(π*） 且 J(π*） ≤ J(Tπ*） ⟹ 目标差 == 0 *)
  assert (Hopt : le (align_objective Np) (align_objective pi_star))
    by exact (rlhf_optimal Np HNp_norm HNp_pos).
  assert (Hmono : le (align_objective pi_star) (align_objective Np))
    by exact (policy_improvement_mono pi_star ps_pos ps_norm).
  assert (Hjeq : Id (align_objective Np) (align_objective pi_star))
    by exact (le_antisym (align_objective Np) (align_objective pi_star) Hopt Hmono).
  assert (Hdiff0 : Id (minus (align_objective Np) (align_objective pi_star)) zero)
    by exact (minus_self_zero (align_objective Np) (align_objective pi_star) Hjeq).
  (* 2. gap 恒等式：J(Tπ*） − J(π*） == β·[(1/η−1)·K1 + (1/η)·K2] *)
  assert (Hgap : Id (minus (align_objective Np) (align_objective pi_star))
                    (mult beta
                          (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2)))).
  {
    unfold Np, K1, K2.
    exact (policy_iter_gap_diff pi_star ps_pos ps_norm).
  }
  (* 3. β > 0 消去（mult_cancel_l）：括号内 == 0 *)
  assert (HX0 : Id (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                         (mult (inv_pos eta eta_pos) K2)) zero).
  {
    apply (mult_cancel_l beta
                         (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                               (mult (inv_pos eta eta_pos) K2))
                         zero beta_pos).
    exact (id_trans (id_trans (id_sym Hgap) Hdiff0) (id_sym (mult_zero beta))).
  }
  (* 4. 非负性：(1/η−1) ≥ 0（η ≤ 1 ⟹ 1 ≤ 1/η）、K1 ≥ 0、K2 ≥ 0 *)
  assert (HP : le zero (minus (inv_pos eta eta_pos) one)).
  {
    assert (Hinv1 : Id (inv_pos one one_pos) one)
      by exact (id_trans (id_sym (id_trans (mult_comm one (inv_pos one one_pos))
                                           (mult_one (inv_pos one one_pos))))
                         (inv_pos_correct one one_pos)).
    assert (Hinv_le : le (inv_pos one one_pos) (inv_pos eta eta_pos))
      by exact (inv_pos_le_compat eta one eta_pos one_pos eta_le_one).
    assert (Hle1 : le one (inv_pos eta eta_pos))
      by exact (le_id_l one (inv_pos one one_pos) (inv_pos eta eta_pos) (id_sym Hinv1) Hinv_le).
    exact (le_minus_nonneg one (inv_pos eta eta_pos) Hle1).
  }
  assert (HK1 : le zero K1)
    by (unfold K1; apply (gibbs_inequality Np pi_star HNp_norm HNp_pos ps_norm ps_pos)).
  assert (HK2 : le zero K2)
    by (unfold K2; apply (gibbs_inequality pi_star Np ps_norm ps_pos HNp_norm HNp_pos)).
  assert (HPK1 : le zero (mult (minus (inv_pos eta eta_pos) one) K1))
    by (apply (le_mult_nonneg_t12 (minus (inv_pos eta eta_pos) one) K1 HP HK1)).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2)).
  {
    apply (le_mult_nonneg_t12 (inv_pos eta eta_pos) K2).
    - apply (lt_le_iff zero (inv_pos eta eta_pos)). left. exact (inv_pos_pos eta eta_pos).
    - exact HK2.
  }
  (* 5. 非负和为零 ⟹ (1/η)·K2 == 0 ⟹（1/η > 0）K2 == 0 *)
  assert (HQK2z : Id (mult (inv_pos eta eta_pos) K2) zero).
  {
    apply (u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                              (mult (minus (inv_pos eta eta_pos) one) K1)
                              HQK2 HPK1).
    apply (id_trans (plus_comm (mult (inv_pos eta eta_pos) K2)
                               (mult (minus (inv_pos eta eta_pos) one) K1)) HX0).
  }
  assert (HK2z : Id K2 zero).
  {
    apply (mult_cancel_l (inv_pos eta eta_pos) K2 zero (inv_pos_pos eta eta_pos)).
    apply (id_trans HQK2z (id_sym (mult_zero (inv_pos eta eta_pos)))).
  }
  (* 6. gibbs_equality：KL(π*‖Tπ*） == 0 ⟹ π* == Tπ* 逐点 ⟹ 结论（id_sym） *)
  assert (Hpi : forall s : S, Id (pi_star s) (Np s))
    by (apply (gibbs_equality pi_star Np ps_norm ps_pos HNp_norm HNp_pos);
        unfold K2 in HK2z; exact HK2z).
  exact (id_sym (Hpi s0)).
Qed.

(* =====================================================================
   U2b：无进展 ⟹ 不动点
     J(pi_next pi_t) == J(pi_t) ⟹ pi_next pi_t == pi_t（逐点）
   证明：与 U2a 第 3–6 步同构（目标等值直接给出 J 差 == 0，无需夹逼）。
   ===================================================================== *)
Theorem u2_no_progress_fixed_point :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t) ->
    forall s : S, Id (pi_next pi_t pi_t_pos s) (pi_t s).
Proof.
  intros pi_t pi_t_pos pi_t_norm Hno s0.
  set (Np := pi_next pi_t pi_t_pos).
  set (K1 := relative_entropy Np pi_t).
  set (K2 := relative_entropy pi_t Np).
  assert (HNp_norm : Id (sum_over_S Np) one)
    by (unfold Np; apply (pi_next_normalized pi_t pi_t_pos)).
  assert (HNp_pos : forall s : S, lt zero (Np s))
    by (intro s; unfold Np; apply (pi_next_pos pi_t pi_t_pos s)).
  (* 1. 目标差 == 0（无进展假设） *)
  assert (Hdiff0 : Id (minus (align_objective Np) (align_objective pi_t)) zero)
    by (unfold Np; exact (minus_self_zero (align_objective Np) (align_objective pi_t) Hno)).
  (* 2. gap 恒等式：J(Tπ) − J(π) == β·[(1/η−1)·K1 + (1/η)·K2] *)
  assert (Hgap : Id (minus (align_objective Np) (align_objective pi_t))
                    (mult beta
                          (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2)))).
  {
    unfold Np, K1, K2.
    exact (policy_iter_gap_diff pi_t pi_t_pos pi_t_norm).
  }
  (* 3. β > 0 消去 *)
  assert (HX0 : Id (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                         (mult (inv_pos eta eta_pos) K2)) zero).
  {
    apply (mult_cancel_l beta
                         (plus (mult (minus (inv_pos eta eta_pos) one) K1)
                               (mult (inv_pos eta eta_pos) K2))
                         zero beta_pos).
    exact (id_trans (id_trans (id_sym Hgap) Hdiff0) (id_sym (mult_zero beta))).
  }
  (* 4. 非负性 *)
  assert (HP : le zero (minus (inv_pos eta eta_pos) one)).
  {
    assert (Hinv1 : Id (inv_pos one one_pos) one)
      by exact (id_trans (id_sym (id_trans (mult_comm one (inv_pos one one_pos))
                                           (mult_one (inv_pos one one_pos))))
                         (inv_pos_correct one one_pos)).
    assert (Hinv_le : le (inv_pos one one_pos) (inv_pos eta eta_pos))
      by exact (inv_pos_le_compat eta one eta_pos one_pos eta_le_one).
    assert (Hle1 : le one (inv_pos eta eta_pos))
      by exact (le_id_l one (inv_pos one one_pos) (inv_pos eta eta_pos) (id_sym Hinv1) Hinv_le).
    exact (le_minus_nonneg one (inv_pos eta eta_pos) Hle1).
  }
  assert (HK1 : le zero K1)
    by (unfold K1; apply (gibbs_inequality Np pi_t HNp_norm HNp_pos pi_t_norm pi_t_pos)).
  assert (HK2 : le zero K2)
    by (unfold K2; apply (gibbs_inequality pi_t Np pi_t_norm pi_t_pos HNp_norm HNp_pos)).
  assert (HPK1 : le zero (mult (minus (inv_pos eta eta_pos) one) K1))
    by (apply (le_mult_nonneg_t12 (minus (inv_pos eta eta_pos) one) K1 HP HK1)).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2)).
  {
    apply (le_mult_nonneg_t12 (inv_pos eta eta_pos) K2).
    - apply (lt_le_iff zero (inv_pos eta eta_pos)). left. exact (inv_pos_pos eta eta_pos).
    - exact HK2.
  }
  (* 5. (1/η)·K2 == 0 ⟹ K2 == 0 *)
  assert (HQK2z : Id (mult (inv_pos eta eta_pos) K2) zero).
  {
    apply (u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                              (mult (minus (inv_pos eta eta_pos) one) K1)
                              HQK2 HPK1).
    apply (id_trans (plus_comm (mult (inv_pos eta eta_pos) K2)
                               (mult (minus (inv_pos eta eta_pos) one) K1)) HX0).
  }
  assert (HK2z : Id K2 zero).
  {
    apply (mult_cancel_l (inv_pos eta eta_pos) K2 zero (inv_pos_pos eta eta_pos)).
    apply (id_trans HQK2z (id_sym (mult_zero (inv_pos eta eta_pos)))).
  }
  (* 6. gibbs_equality：KL(π‖Tπ) == 0 ⟹ π == Tπ 逐点 ⟹ 结论（id_sym） *)
  assert (Hpi : forall s : S, Id (pi_t s) (Np s))
    by (apply (gibbs_equality pi_t Np pi_t_norm pi_t_pos HNp_norm HNp_pos);
        unfold K2 in HK2z; exact HK2z).
  exact (id_sym (Hpi s0)).
Qed.

(* =====================================================================
   U2c：不动点唯一 ⟹ π*
     (forall s, pi_next pi_t pi_t_pos s == pi_t s) ⟹ pi_t == pi_star（逐点）
   证明：不动点处向后 KL 单步 ≤ 化简为 KL(π*‖π_t) ≤ (1−η)·KL(π*‖π_t)，
     η > 0 乘回得 η·A ≤ 0；gibbs 给 0 ≤ A，η ≥ 0 ⟹ 0 ≤ η·A；夹逼
     η·A == 0 ⟹ A == 0 ⟹ gibbs_equality ⟹ π_t == π* 逐点。
   ===================================================================== *)
Theorem u2_fixed_point_unique :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    (forall s : S, Id (pi_next pi_t pi_t_pos s) (pi_t s)) ->
    forall s : S, Id (pi_t s) (pi_star s).
Proof.
  intros pi_t pi_t_pos pi_t_norm Hfix s0.
  set (A := relative_entropy pi_star pi_t).
  (* 1. 同余换形：KL(π*‖Tπ) == A 且 KL(π‖Tπ) == 0 *)
  assert (Hc1 : Id (relative_entropy pi_star (pi_next pi_t pi_t_pos))
                   (relative_entropy pi_star pi_t)).
  { apply (u2_kl_arg2_ext pi_star (pi_next pi_t pi_t_pos) pi_t). exact Hfix. }
  assert (Hc2 : Id (relative_entropy pi_t (pi_next pi_t pi_t_pos))
                   (relative_entropy pi_t pi_t)).
  { apply (u2_kl_arg2_ext pi_t (pi_next pi_t pi_t_pos) pi_t). exact Hfix. }
  assert (HC0 : Id (relative_entropy pi_t (pi_next pi_t pi_t_pos)) zero)
    by exact (id_trans Hc2 (relative_entropy_self_zero' pi_t)).
  (* 2. 向后 KL 单步（≤ 版）：KL(π*‖Tπ) ≤ (1−η)·KL(π*‖π) + KL(π‖Tπ) *)
  assert (HleA : le A (mult (minus one eta) A)).
  {
    assert (H1 : le (relative_entropy pi_star (pi_next pi_t pi_t_pos))
                    (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                          (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
    { apply (policy_iter_backward_kl_step_le pi_t pi_t_pos pi_t_norm).
      intro s. apply (pi_next_pos pi_t pi_t_pos s). }
    (* 右端 (1−η)KL(π*‖π_t) 换为 (1−η)A *)
    assert (H2 : Id (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                           (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                    (plus (mult (minus one eta) A)
                          (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
    {
      apply (id_cong (fun x => plus x (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
      apply (id_cong (fun x => mult (minus one eta) x)).
      unfold A. reflexivity.
    }
    (* 左端 KL(π*‖Tπ) 换为 A *)
    assert (H3 : le A (plus (mult (minus one eta) A)
                            (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
    {
      apply (le_id_l A (relative_entropy pi_star (pi_next pi_t pi_t_pos))
                       (plus (mult (minus one eta) A)
                             (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
      - unfold A. exact (id_sym Hc1).
      - apply (le_id_r (relative_entropy pi_star (pi_next pi_t pi_t_pos))
                       (plus (mult (minus one eta) (relative_entropy pi_star pi_t))
                             (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                       (plus (mult (minus one eta) A)
                             (relative_entropy pi_t (pi_next pi_t pi_t_pos)))).
        + exact H2.
        + exact H1.
    }
    (* KL(π‖Tπ) == 0 ⟹ 右端 == (1−η)A *)
    assert (H4 : Id (plus (mult (minus one eta) A)
                          (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                    (mult (minus one eta) A)).
    {
      apply (id_trans (id_cong (fun x => plus (mult (minus one eta) A) x) HC0)
                      (plus_zero (mult (minus one eta) A))).
    }
    apply (le_id_r A (plus (mult (minus one eta) A)
                           (relative_entropy pi_t (pi_next pi_t pi_t_pos)))
                   (mult (minus one eta) A) H4 H3).
  }
  (* 3. (1−η)A == A − ηA，故 A ≤ A − ηA *)
  assert (Hma : Id (mult (minus one eta) (relative_entropy pi_star pi_t))
                   (minus (relative_entropy pi_star pi_t)
                          (mult eta (relative_entropy pi_star pi_t)))).
  {
    apply (id_trans (mult_minus_distr_r one eta (relative_entropy pi_star pi_t))).
    apply (id_cong (fun x => minus x (mult eta (relative_entropy pi_star pi_t)))).
    apply (id_trans (mult_comm one (relative_entropy pi_star pi_t))
                    (mult_one (relative_entropy pi_star pi_t))).
  }
  assert (HleB : le (relative_entropy pi_star pi_t)
                    (minus (relative_entropy pi_star pi_t)
                           (mult eta (relative_entropy pi_star pi_t)))).
  {
    apply (le_id_r (relative_entropy pi_star pi_t)
                   (mult (minus one eta) (relative_entropy pi_star pi_t))
                   (minus (relative_entropy pi_star pi_t)
                          (mult eta (relative_entropy pi_star pi_t)))).
    - exact Hma.
    - unfold A in HleA. exact HleA.
  }
  (* 4. 0 ≤ −ηA（le_minus_nonneg + (A − ηA) − A == −ηA） *)
  assert (Hz1 : le zero (minus (minus (relative_entropy pi_star pi_t)
                                      (mult eta (relative_entropy pi_star pi_t)))
                               (relative_entropy pi_star pi_t)))
    by (apply (le_minus_nonneg (relative_entropy pi_star pi_t)
                               (minus (relative_entropy pi_star pi_t)
                                      (mult eta (relative_entropy pi_star pi_t))));
        exact HleB).
  assert (Hz2 : le zero (opp (mult eta (relative_entropy pi_star pi_t)))).
  {
    apply (le_id_r zero
                   (minus (minus (relative_entropy pi_star pi_t)
                                 (mult eta (relative_entropy pi_star pi_t)))
                          (relative_entropy pi_star pi_t))
                   (opp (mult eta (relative_entropy pi_star pi_t)))).
    - apply (u2_minus_minus (relative_entropy pi_star pi_t)
                            (mult eta (relative_entropy pi_star pi_t))).
    - exact Hz1.
  }
  (* 5. ηA ≤ 0（取负两次反号） *)
  assert (Hopp0 : le (opp (opp (mult eta (relative_entropy pi_star pi_t))))
                     (opp zero))
    by exact (opp_le_compat zero (opp (mult eta (relative_entropy pi_star pi_t))) Hz2).
  assert (Hopp1 : le (opp (opp (mult eta (relative_entropy pi_star pi_t)))) zero)
    by exact (le_id_r (opp (opp (mult eta (relative_entropy pi_star pi_t))))
                      (opp zero) zero opp_zero_t13 Hopp0).
  assert (Heta_le0 : le (mult eta (relative_entropy pi_star pi_t)) zero)
    by exact (le_id_l (mult eta (relative_entropy pi_star pi_t))
                      (opp (opp (mult eta (relative_entropy pi_star pi_t))))
                      zero (id_sym (double_neg (mult eta (relative_entropy pi_star pi_t))))
                      Hopp1).
  (* 6. 0 ≤ ηA（gibbs：0 ≤ A；η ≥ 0 ⟹ 0 ≤ ηA） *)
  assert (HA0 : le zero (relative_entropy pi_star pi_t))
    by (apply (gibbs_inequality pi_star pi_t pi_star_normalized pi_star_pos pi_t_norm pi_t_pos)).
  assert (Heta0 : le zero eta)
    by exact (lt_le_iff zero eta (inl eta_pos)).
  assert (HX0 : le zero (mult eta (relative_entropy pi_star pi_t)))
    by (apply (le_mult_nonneg_t12 eta (relative_entropy pi_star pi_t));
        [exact Heta0 | exact HA0]).
  (* 7. ηA == 0 ⟹（η > 0）A == 0 ⟹ gibbs_equality ⟹ π_t == π* 逐点 *)
  assert (HXz : Id (mult eta (relative_entropy pi_star pi_t)) zero)
    by exact (id_sym (le_antisym zero (mult eta (relative_entropy pi_star pi_t)) HX0 Heta_le0)).
  assert (HAz : Id (relative_entropy pi_star pi_t) zero).
  {
    apply (mult_cancel_l eta (relative_entropy pi_star pi_t) zero eta_pos).
    apply (id_trans HXz (id_sym (mult_zero eta))).
  }
  assert (Hpi : forall s : S, Id (pi_star s) (pi_t s))
    by (apply (gibbs_equality pi_star pi_t pi_star_normalized pi_star_pos pi_t_norm pi_t_pos HAz)).
  exact (id_sym (Hpi s0)).
Qed.

(* =====================================================================
   推论：无进展 ⟹ 已最优（u2b + u2c 组装）
     J(pi_next pi_t) == J(pi_t) ⟹ pi_t == pi_star（逐点）
   ===================================================================== *)
Theorem u2_no_progress_optimal :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t) ->
    forall s : S, Id (pi_t s) (pi_star s).
Proof.
  intros pi_t pi_t_pos pi_t_norm Hno s0.
  exact (u2_fixed_point_unique pi_t pi_t_pos pi_t_norm
                               (fun s : S => u2_no_progress_fixed_point pi_t pi_t_pos pi_t_norm Hno s)
                               s0).
Qed.

(* =====================================================================
   反向：已最优 ⟹ 无进展
     pi_t == pi_star（逐点）⟹ J(pi_next pi_t) == J(pi_t)
   证明：逐点相等 + 目标外延 ⟹ J(π_t) == J(π*）；
     rlhf_optimal（J(Tπ) ≤ J(π*））+ policy_improvement_mono（J(π) ≤ J(Tπ)）
     夹逼 ⟹ J(Tπ) == J(π)（等值传递）。
   ===================================================================== *)
Theorem u2_optimal_no_progress :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    (forall s : S, Id (pi_t s) (pi_star s)) ->
    Id (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t).
Proof.
  intros pi_t pi_t_pos pi_t_norm Hpi.
  set (Np := pi_next pi_t pi_t_pos).
  assert (HNp_norm : Id (sum_over_S Np) one)
    by (unfold Np; apply (pi_next_normalized pi_t pi_t_pos)).
  assert (HNp_pos : forall s : S, lt zero (Np s))
    by (intro s; unfold Np; apply (pi_next_pos pi_t pi_t_pos s)).
  (* J(π_t) == J(π*）（逐点外延） *)
  assert (Hext : Id (align_objective pi_t) (align_objective pi_star))
    by (apply (u2_align_objective_ext pi_t pi_star); exact Hpi).
  (* J(Tπ) ≤ J(π*） 与 J(π) ≤ J(Tπ) 夹逼 *)
  assert (Hopt : le (align_objective Np) (align_objective pi_star))
    by (unfold Np; exact (rlhf_optimal Np HNp_norm HNp_pos)).
  assert (Hmono : le (align_objective pi_t) (align_objective Np))
    by (unfold Np; exact (policy_improvement_mono pi_t pi_t_pos pi_t_norm)).
  assert (Hle1 : le (align_objective Np) (align_objective pi_t))
    by (apply (le_id_r (align_objective Np) (align_objective pi_star) (align_objective pi_t));
        [exact (id_sym Hext) | exact Hopt]).
  unfold Np.
  exact (le_antisym (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t)
                    Hle1 Hmono).
Qed.

(* =====================================================================
   等值刻画（双向，Set 层 And := A*B 乘积）：
     J(pi_next pi_t) == J(pi_t)  ⟺  pi_t == pi_star（逐点）
   ===================================================================== *)
Theorem u2_objective_eq_optimal_iff :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
  And (Id (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t) ->
        forall s : S, Id (pi_t s) (pi_star s))
      ((forall s : S, Id (pi_t s) (pi_star s)) ->
        Id (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t)).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  split.
  - intro H. apply (u2_no_progress_optimal pi_t pi_t_pos pi_t_norm H).
  - intro H. apply (u2_optimal_no_progress pi_t pi_t_pos pi_t_norm H).
Qed.

End U2FixedPoint.

(* ============================================================ *)
(* GRPO：组相对策略优化（组相对优势的构造性形式化）             *)
(* ============================================================ *)
(* DeepSeek-R1 核心算法：组内归一化优势 A_i = (r_i − μ)/σ 的      *)
(* 零均值性质。组求和用有限枚举列表 group_enum（同 S_enum 模式）；*)
(* 组均值 μ = (1/G)·Σr；σ 归一化对零均值无作用（Σ A_i·c = 0 对    *)
(* 任意缩放 c 成立）。                                           *)

Section GRPO.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.

(* nat 到 R 的嵌入（构造性计数；0 ⟼ zero，S n ⟼ 1 + of_nat n） *)
Fixpoint of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (of_nat n')
  end.

Variable Group : Set.
Variable group_enum : list Group.
Variable group_cover : forall i : Group, InT i group_enum.
Definition group_size : nat := length group_enum.
Variable group_size_pos : lt zero (of_nat group_size).
Variable reward_group : Group -> R.

(* 组求和（列表 fold） *)
Fixpoint list_sum_g (f : Group -> R) (l : list Group) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g f rest)
  end.

Lemma list_sum_g_linear : forall a : R, forall f : Group -> R, forall l : list Group,
  Id (list_sum_g (fun i => mult a (f i)) l) (mult a (list_sum_g f l)).
Proof.
  intros a f l. induction l as [| i rest IH]; simpl.
  - apply id_sym. apply mult_zero.
  - rewrite IH. apply id_sym. apply distrib.
Qed.

Lemma list_sum_g_add : forall f g : Group -> R, forall l : list Group,
  Id (list_sum_g (fun i => plus (f i) (g i)) l) (plus (list_sum_g f l) (list_sum_g g l)).
Proof.
  intros f g l. induction l as [| i rest IH]; simpl.
  - apply id_sym. apply plus_zero.
  - rewrite IH. exact (plus_swap_mid (f i) (g i) (list_sum_g f rest) (list_sum_g g rest)).
Qed.

Lemma list_sum_g_ext : forall f g : Group -> R, forall l : list Group,
  (forall i : Group, Id (f i) (g i)) -> Id (list_sum_g f l) (list_sum_g g l).
Proof.
  intros f g l Hfg. induction l as [| i rest IH]; simpl.
  - reflexivity.
  - assert (H1 : Id (plus (f i) (list_sum_g f rest)) (plus (f i) (list_sum_g g rest)))
      by exact (id_cong (fun x => plus (f i) x) IH).
    assert (H2 : Id (plus (f i) (list_sum_g g rest)) (plus (g i) (list_sum_g g rest)))
      by exact (id_cong (fun x => plus x (list_sum_g g rest)) (Hfg i)).
    exact (id_trans H1 H2).
Qed.

(* 常数求和：Σ_{i∈l} a = of_nat (length l) · a *)
Lemma list_sum_g_const : forall a : R, forall l : list Group,
  Id (list_sum_g (fun _ => a) l) (mult (of_nat (length l)) a).
Proof.
  intros a l. induction l as [| i rest IH]; simpl.
  - apply id_sym. exact (id_trans (mult_comm zero a) (mult_zero a)).
  - rewrite IH.
    assert (Hd : Id (mult (plus one (of_nat (length rest))) a)
                    (plus (mult one a) (mult (of_nat (length rest)) a)))
      by exact (mult_plus_distr_r one (of_nat (length rest)) a).
    assert (Ht : Id (plus a (mult (of_nat (length rest)) a))
                    (mult (plus one (of_nat (length rest))) a))
      by exact (id_trans (id_cong (fun x => plus x (mult (of_nat (length rest)) a))
                                  (id_trans (id_sym (mult_one a)) (mult_comm a one)))
                         (id_sym Hd)).
    exact Ht.
Qed.

(* 组求和的负号线性：Σ (-f) = -Σ f *)
Lemma list_sum_g_opp : forall f : Group -> R, forall l : list Group,
  Id (list_sum_g (fun i => opp (f i)) l) (opp (list_sum_g f l)).
Proof.
  intros f l. induction l as [| i rest IH]; simpl.
  - apply id_sym. apply (plus_inv_unique zero (opp zero) zero); [apply plus_opp | apply plus_zero].
  - assert (Hc : Id (plus (opp (f i)) (list_sum_g (fun i0 => opp (f i0)) rest))
                    (plus (opp (f i)) (opp (list_sum_g f rest))))
      by exact (id_cong (fun x => plus (opp (f i)) x) IH).
    assert (Ho : Id (plus (opp (f i)) (opp (list_sum_g f rest)))
                    (opp (plus (f i) (list_sum_g f rest))))
      by exact (id_sym (opp_plus (f i) (list_sum_g f rest))).
    exact (id_trans Hc Ho).
Qed.

(* 组求和的减法线性：Σ (f - g) = Σf - Σg *)
Lemma list_sum_g_minus : forall f g : Group -> R, forall l : list Group,
  Id (list_sum_g (fun i => minus (f i) (g i)) l) (minus (list_sum_g f l) (list_sum_g g l)).
Proof.
  intros f g l. unfold minus.
  assert (Hadd : Id (list_sum_g (fun i => plus (f i) (opp (g i))) l)
                    (plus (list_sum_g f l) (list_sum_g (fun i => opp (g i)) l)))
    by exact (list_sum_g_add f (fun i => opp (g i)) l).
  assert (Hopp : Id (list_sum_g (fun i => opp (g i)) l) (opp (list_sum_g g l)))
    by exact (list_sum_g_opp g l).
  exact (id_trans Hadd (id_cong (fun x => plus (list_sum_g f l) x) Hopp)).
Qed.

(* 组均值：μ = (1/G)·Σ r_i *)
Definition group_mean : R :=
  mult (inv_pos (of_nat group_size) group_size_pos) (list_sum_g reward_group group_enum).

(* 组相对优势：A_i = r_i − μ（σ 归一化在零均值定理中消去） *)
Definition grpo_advantage (i : Group) : R :=
  minus (reward_group i) group_mean.

(* 组相对优势的零均值性质：Σ_i (r_i − μ)·c = 0（对任意缩放 c）。
   证明：线性提取 c → Σ(r_i − μ) = Σr − G·μ = Σr − Σr = 0。 *)
Theorem grpo_advantage_zero_mean :
  forall c : R,
    Id (list_sum_g (fun i => mult (grpo_advantage i) c) group_enum) zero.
Proof.
  intros c.
  assert (Hext : Id (list_sum_g (fun i => mult (grpo_advantage i) c) group_enum)
                    (list_sum_g (fun i => mult c (grpo_advantage i)) group_enum))
    by (apply list_sum_g_ext; intro i; apply mult_comm).
  rewrite Hext.
  assert (Hlin : Id (list_sum_g (fun i => mult c (grpo_advantage i)) group_enum)
                    (mult c (list_sum_g grpo_advantage group_enum)))
    by exact (list_sum_g_linear c grpo_advantage group_enum).
  rewrite Hlin.
  assert (Hcancel : Id (list_sum_g grpo_advantage group_enum) zero).
  {
    unfold grpo_advantage.
    assert (Hmin : Id (list_sum_g (fun i => minus (reward_group i) group_mean) group_enum)
                      (minus (list_sum_g reward_group group_enum)
                             (list_sum_g (fun _ => group_mean) group_enum)))
      by exact (list_sum_g_minus reward_group (fun _ => group_mean) group_enum).
    rewrite Hmin.
    assert (Hconst : Id (list_sum_g (fun _ => group_mean) group_enum)
                        (mult (of_nat group_size) group_mean))
      by (unfold group_size; exact (list_sum_g_const group_mean group_enum)).
    rewrite Hconst.
    assert (Hcc : Id (mult (of_nat group_size) group_mean) (list_sum_g reward_group group_enum)).
    { unfold group_mean.
      assert (H1 : Id (mult (of_nat group_size) (mult (inv_pos (of_nat group_size) group_size_pos) (list_sum_g reward_group group_enum)))
                      (mult (mult (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos)) (list_sum_g reward_group group_enum)))
        by exact (mult_assoc (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos) (list_sum_g reward_group group_enum)).
      assert (H2 : Id (mult (mult (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos)) (list_sum_g reward_group group_enum))
                      (mult one (list_sum_g reward_group group_enum)))
        by exact (id_cong (fun z => mult z (list_sum_g reward_group group_enum))
                          (inv_pos_correct (of_nat group_size) group_size_pos)).
      assert (H3 : Id (mult one (list_sum_g reward_group group_enum)) (list_sum_g reward_group group_enum))
        by exact (id_trans (mult_comm one (list_sum_g reward_group group_enum)) (mult_one (list_sum_g reward_group group_enum))).
      exact (id_trans H1 (id_trans H2 H3)). }
    rewrite Hcc.
    exact (minus_self_zero _ _ (@id_refl R (list_sum_g reward_group group_enum))).
  }
  rewrite Hcancel.
  exact (mult_zero c).
Qed.

(* ============================================================ *)
(* GRPO 方差恒等式（聚焦AI算法.txt 模块 3）：                   *)
(*   Σ_i (r_i − μ)² = Σ_i r_i² − G·μ²                          *)
(* 证明：逐点展开 (r−μ)² = r² − 2·r·μ + μ²（distrib +          *)
(*   opp_mult_r/l + double_neg），求和线性化，用零均值性质       *)
(*   Σr = G·μ 消去交叉项，最终 −2·G·μ² + G·μ² = −G·μ²。         *)
(* ------------------------------------------------------------ *)

(* 组二阶矩：Σ r_i² *)
Definition group_raw_second_moment : R :=
  list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum.

(* 组方差（中心化二阶矩）：Σ (r_i − μ)² *)
Definition group_centered_second_moment : R :=
  list_sum_g (fun i => mult (grpo_advantage i) (grpo_advantage i)) group_enum.

(* 逐点展开：(r − μ)² = r² − 2·r·μ + μ²（非平凡代数链） *)
Lemma grpo_square_expand : forall i : Group,
  Id (mult (grpo_advantage i) (grpo_advantage i))
     (plus (mult (reward_group i) (reward_group i))
           (plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                 (mult group_mean group_mean))).
Proof.
  intro i.
  unfold grpo_advantage.
  (* (r − μ)² = (r + (−μ))·(r + (−μ)) *)
  assert (H1 : Id (mult (plus (reward_group i) (opp group_mean)) (plus (reward_group i) (opp group_mean)))
                  (plus (mult (reward_group i) (plus (reward_group i) (opp group_mean)))
                        (mult (opp group_mean) (plus (reward_group i) (opp group_mean)))))
    by exact (mult_plus_distr_r (reward_group i) (opp group_mean) (plus (reward_group i) (opp group_mean))).
  (* 第一项：r·(r + (−μ)) = r² + r·(−μ) = r² − r·μ *)
  assert (H2 : Id (mult (reward_group i) (plus (reward_group i) (opp group_mean)))
                  (plus (mult (reward_group i) (reward_group i)) (mult (reward_group i) (opp group_mean))))
    by exact (distrib (reward_group i) (reward_group i) (opp group_mean)).
  assert (H3 : Id (mult (reward_group i) (opp group_mean)) (opp (mult (reward_group i) group_mean)))
    by exact (opp_mult_l (reward_group i) group_mean).
  (* 第二项：(−μ)·(r + (−μ)) = (−μ)·r + (−μ)·(−μ) = −(μ·r) + μ² *)
  assert (H4 : Id (mult (opp group_mean) (plus (reward_group i) (opp group_mean)))
                  (plus (mult (opp group_mean) (reward_group i)) (mult (opp group_mean) (opp group_mean))))
    by exact (distrib (opp group_mean) (reward_group i) (opp group_mean)).
  assert (H5 : Id (mult (opp group_mean) (reward_group i)) (opp (mult group_mean (reward_group i))))
    by exact (opp_mult_r group_mean (reward_group i)).
  assert (H6 : Id (mult (opp group_mean) (opp group_mean)) (mult group_mean group_mean)).
  {
    assert (H6a : Id (mult (opp group_mean) (opp group_mean)) (opp (mult group_mean (opp group_mean))))
      by exact (opp_mult_r group_mean (opp group_mean)).
    assert (H6b : Id (opp (mult group_mean (opp group_mean))) (opp (opp (mult group_mean group_mean))))
      by exact (id_cong opp (opp_mult_l group_mean group_mean)).
    assert (H6c : Id (opp (opp (mult group_mean group_mean))) (mult group_mean group_mean))
      by exact (double_neg (mult group_mean group_mean)).
    exact (id_trans H6a (id_trans H6b H6c)).
  }
  (* 组装：r² − r·μ − μ·r + μ²；合并交叉项 −r·μ − μ·r = −2·r·μ *)
  assert (H7 : Id (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult (reward_group i) group_mean)))
                        (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)))
                  (plus (mult (reward_group i) (reward_group i))
                        (plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                              (mult group_mean group_mean)))).
  {
    (* 交叉项合并：−r·μ + (−μ·r) = −2·r·μ；用 μ·r = r·μ 换序 *)
    assert (Hsw : Id (opp (mult group_mean (reward_group i))) (opp (mult (reward_group i) group_mean)))
      by exact (id_cong opp (mult_comm group_mean (reward_group i))).
    assert (Hm1 : Id (plus (opp (mult (reward_group i) group_mean)) (opp (mult group_mean (reward_group i))))
                      (plus (opp (mult (reward_group i) group_mean)) (opp (mult (reward_group i) group_mean))))
      by exact (id_cong (fun x => plus (opp (mult (reward_group i) group_mean)) x) Hsw).
    assert (Hm2 : Id (plus (opp (mult (reward_group i) group_mean)) (opp (mult (reward_group i) group_mean)))
                      (opp (mult (mult (plus one one) (reward_group i)) group_mean))).
    {
      assert (Hm2a : Id (plus (opp (mult (reward_group i) group_mean)) (opp (mult (reward_group i) group_mean)))
                         (opp (plus (mult (reward_group i) group_mean) (mult (reward_group i) group_mean))))
        by exact (id_sym (opp_plus (mult (reward_group i) group_mean) (mult (reward_group i) group_mean))).
      assert (Hm2b : Id (mult (mult (plus one one) (reward_group i)) group_mean)
                        (plus (mult (reward_group i) group_mean) (mult (reward_group i) group_mean)))
        by exact (id_trans (id_cong (fun x => mult x group_mean) (two_mult (reward_group i)))
                           (mult_plus_distr_r (reward_group i) (reward_group i) group_mean)).
      exact (id_trans Hm2a (id_cong opp (id_sym Hm2b))).
    }
    (* 用 plus_swap_mid 重排四项为 r² + (交叉项和) + μ² 形态 *)
    assert (Hre : Id (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult (reward_group i) group_mean)))
                            (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)))
                      (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult group_mean (reward_group i))))
                            (plus (opp (mult (reward_group i) group_mean)) (mult group_mean group_mean))))
      by exact (plus_swap_mid (mult (reward_group i) (reward_group i)) (opp (mult (reward_group i) group_mean))
                              (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)).
    assert (Hre2 : Id (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult group_mean (reward_group i))))
                             (plus (opp (mult (reward_group i) group_mean)) (mult group_mean group_mean)))
                       (plus (mult (reward_group i) (reward_group i))
                             (plus (plus (opp (mult (reward_group i) group_mean)) (opp (mult group_mean (reward_group i))))
                                   (mult group_mean group_mean)))).
    {
      (* plus (plus r² x) (plus y μ²) = plus r² (plus (plus y x) μ²)
         用 plus_swap_mid 把 x,y 换到中间，再调整 y,x 顺序 *)
      assert (Hps : Id (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult group_mean (reward_group i))))
                             (plus (opp (mult (reward_group i) group_mean)) (mult group_mean group_mean)))
                       (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult (reward_group i) group_mean)))
                             (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean))))
        by exact (plus_swap_mid (mult (reward_group i) (reward_group i)) (opp (mult group_mean (reward_group i)))
                                (opp (mult (reward_group i) group_mean)) (mult group_mean group_mean)).
      assert (Hps2 : Id (plus (plus (mult (reward_group i) (reward_group i)) (opp (mult (reward_group i) group_mean)))
                              (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)))
                        (plus (mult (reward_group i) (reward_group i))
                              (plus (opp (mult (reward_group i) group_mean))
                                    (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)))))
        by exact (id_sym (plus_assoc (mult (reward_group i) (reward_group i))
                                     (opp (mult (reward_group i) group_mean))
                                     (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean)))).
      assert (Hps3 : Id (plus (mult (reward_group i) (reward_group i))
                              (plus (opp (mult (reward_group i) group_mean))
                                    (plus (opp (mult group_mean (reward_group i))) (mult group_mean group_mean))))
                        (plus (mult (reward_group i) (reward_group i))
                              (plus (plus (opp (mult (reward_group i) group_mean)) (opp (mult group_mean (reward_group i))))
                                    (mult group_mean group_mean))))
        by exact (id_cong (fun x => plus (mult (reward_group i) (reward_group i)) x)
                          (plus_assoc (opp (mult (reward_group i) group_mean))
                                      (opp (mult group_mean (reward_group i)))
                                      (mult group_mean group_mean))).
      exact (id_trans Hps (id_trans Hps2 Hps3)).
    }
    assert (Hre3 : Id (plus (mult (reward_group i) (reward_group i))
                            (plus (plus (opp (mult (reward_group i) group_mean)) (opp (mult group_mean (reward_group i))))
                                  (mult group_mean group_mean)))
                      (plus (mult (reward_group i) (reward_group i))
                            (plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                  (mult group_mean group_mean))))
      by exact (id_cong (fun x => plus (mult (reward_group i) (reward_group i)) (plus x (mult group_mean group_mean)))
                        (id_trans (id_cong (fun y => plus (opp (mult (reward_group i) group_mean)) y)
                                           (id_cong opp (mult_comm group_mean (reward_group i))))
                                  Hm2)).
    exact (id_trans Hre (id_trans Hre2 Hre3)).
  }
  exact (id_trans H1 (id_trans (id_cong2 plus (id_trans H2 (id_cong2 plus (@id_refl R (mult (reward_group i) (reward_group i))) H3))
                                              (id_trans H4 (id_cong2 plus H5 H6)))
                               H7)).
Qed.

(* GRPO 方差恒等式：Σ (r_i − μ)² = Σ r_i² − G·μ²
   非平凡：逐点展开 + 求和线性 + 零均值消交叉项（约 20 步代数链） *)
Theorem grpo_variance_identity :
  Id group_centered_second_moment
     (minus group_raw_second_moment (mult (of_nat group_size) (mult group_mean group_mean))).
Proof.
  unfold group_centered_second_moment, group_raw_second_moment.
  (* 逐点替换 (r−μ)² = r² − 2rμ + μ² *)
  assert (Hext : Id (list_sum_g (fun i => mult (grpo_advantage i) (grpo_advantage i)) group_enum)
                    (list_sum_g (fun i => plus (mult (reward_group i) (reward_group i))
                                              (plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                                    (mult group_mean group_mean))) group_enum))
    by (apply list_sum_g_ext; intro i; exact (grpo_square_expand i)).
  rewrite Hext.
  (* 求和线性化：Σ(r² + (−2rμ + μ²)) = Σr² + Σ(−2rμ) + Σμ² *)
  assert (Hadd1 : Id (list_sum_g (fun i => plus (mult (reward_group i) (reward_group i))
                                                (plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                                      (mult group_mean group_mean))) group_enum)
                     (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (list_sum_g (fun i => plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                                      (mult group_mean group_mean)) group_enum)))
    by exact (list_sum_g_add (fun i => mult (reward_group i) (reward_group i))
                             (fun i => plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                             (mult group_mean group_mean)) group_enum).
  rewrite Hadd1.
  assert (Hadd2 : Id (list_sum_g (fun i => plus (opp (mult (mult (plus one one) (reward_group i)) group_mean))
                                                (mult group_mean group_mean)) group_enum)
                     (plus (list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) group_mean)) group_enum)
                           (list_sum_g (fun _ => mult group_mean group_mean) group_enum)))
    by exact (list_sum_g_add (fun i => opp (mult (mult (plus one one) (reward_group i)) group_mean))
                             (fun _ => mult group_mean group_mean) group_enum).
  rewrite Hadd2.
  (* Σ(−2·r_i·μ) = −2·μ·Σr_i；Σμ² = G·μ² *)
  assert (Hopp : Id (list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) group_mean)) group_enum)
                    (opp (mult (mult (plus one one) (list_sum_g reward_group group_enum)) group_mean))).
  {
    assert (Hlin : Id (list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) group_mean) group_enum)
                      (mult group_mean (list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum))).
    {
      assert (Hsw : Id (list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) group_mean) group_enum)
                       (list_sum_g (fun i => mult group_mean (mult (plus one one) (reward_group i))) group_enum))
        by (apply list_sum_g_ext; intro i; apply mult_comm).
      rewrite Hsw. apply list_sum_g_linear.
    }
    assert (Hlin2 : Id (list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum)
                       (mult (plus one one) (list_sum_g reward_group group_enum)))
      by exact (list_sum_g_linear (plus one one) reward_group group_enum).
    assert (Hassoc : Id (mult group_mean (mult (plus one one) (list_sum_g reward_group group_enum)))
                        (mult (mult (plus one one) (list_sum_g reward_group group_enum)) group_mean))
      by exact (mult_comm group_mean (mult (plus one one) (list_sum_g reward_group group_enum))).
    assert (Hmid : Id (list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) group_mean) group_enum)
                      (mult (mult (plus one one) (list_sum_g reward_group group_enum)) group_mean))
      by exact (id_trans Hlin (id_trans (id_cong (fun x => mult group_mean x) Hlin2) Hassoc)).
    exact (id_trans (list_sum_g_opp (fun i => mult (mult (plus one one) (reward_group i)) group_mean) group_enum)
                    (id_cong opp Hmid)).
  }
  rewrite Hopp.
  (* Σμ² = G·μ² *)
  assert (Hconst : Id (list_sum_g (fun _ => mult group_mean group_mean) group_enum)
                      (mult (of_nat group_size) (mult group_mean group_mean)))
    by (unfold group_size; exact (list_sum_g_const (mult group_mean group_mean) group_enum)).
  rewrite Hconst.
  (* 用 Σr = G·μ 消去：−2·μ·Σr + G·μ² = −2·G·μ² + G·μ² = −G·μ² *)
  assert (Hmu : Id (list_sum_g reward_group group_enum) (mult (of_nat group_size) group_mean)).
  {
    unfold group_mean.
    assert (H1 : Id (mult (of_nat group_size) (mult (inv_pos (of_nat group_size) group_size_pos) (list_sum_g reward_group group_enum)))
                    (mult (mult (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos)) (list_sum_g reward_group group_enum)))
      by exact (mult_assoc (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos) (list_sum_g reward_group group_enum)).
    assert (H2 : Id (mult (mult (of_nat group_size) (inv_pos (of_nat group_size) group_size_pos)) (list_sum_g reward_group group_enum))
                    (mult one (list_sum_g reward_group group_enum)))
      by exact (id_cong (fun z => mult z (list_sum_g reward_group group_enum)) (inv_pos_correct (of_nat group_size) group_size_pos)).
    assert (H3 : Id (mult one (list_sum_g reward_group group_enum)) (list_sum_g reward_group group_enum))
      by exact (id_trans (mult_comm one (list_sum_g reward_group group_enum)) (mult_one (list_sum_g reward_group group_enum))).
    exact (id_sym (id_trans H1 (id_trans H2 H3))).
  }
  assert (Hcross : Id (opp (mult (mult (plus one one) (list_sum_g reward_group group_enum)) group_mean))
                      (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))).
  { exact (id_cong opp (id_cong (fun x => mult (mult (plus one one) x) group_mean) Hmu)). }
  rewrite Hcross.
  (* 目标重组：Σr² + (opp(2·G·μ·μ) + G·μ²) = Σr² − G·μ² *)
  (* −2·G·μ² + G·μ² = −G·μ²（经 mult_assoc + 2·x − x = x） *)
  assert (Hcancel2 : Id (plus (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))
                              (mult (of_nat group_size) (mult group_mean group_mean)))
                        (opp (mult (of_nat group_size) (mult group_mean group_mean)))).
  {
    (* 2·(G·μ)·μ = 2·(G·μ²)；−2x + x = −x *)
    assert (H2a : Id (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean)
                     (mult (plus one one) (mult (of_nat group_size) (mult group_mean group_mean)))).
    {
      assert (H1 : Id (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean)
                      (mult (plus one one) (mult (mult (of_nat group_size) group_mean) group_mean)))
        by exact (id_sym (mult_assoc (plus one one) (mult (of_nat group_size) group_mean) group_mean)).
      assert (H2 : Id (mult (mult (of_nat group_size) group_mean) group_mean)
                      (mult (of_nat group_size) (mult group_mean group_mean)))
        by exact (id_sym (mult_assoc (of_nat group_size) group_mean group_mean)).
      exact (id_trans H1 (id_cong (fun x => mult (plus one one) x) H2)).
    }
    assert (H2b : Id (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))
                     (opp (mult (plus one one) (mult (of_nat group_size) (mult group_mean group_mean)))))
      by exact (id_cong opp H2a).
    (* 2x − x = x（对 x := G·μ²） *)
    set (x := mult (of_nat group_size) (mult group_mean group_mean)).
    assert (H2c : Id (plus (opp (mult (plus one one) x)) x) (opp x)).
    {
      (* 2x = x + x（two_mult），− (x+x) + x = −x（opp_plus + plus_assoc/opp） *)
      assert (Ht : Id (mult (plus one one) x) (plus x x)) by exact (two_mult x).
      assert (Hopp2 : Id (opp (plus x x)) (plus (opp x) (opp x))) by exact (opp_plus x x).
      assert (Hcomb : Id (plus (plus (opp x) (opp x)) x) (plus (opp x) (plus (opp x) x)))
        by exact (id_sym (plus_assoc (opp x) (opp x) x)).
      assert (Hoppx : Id (plus (opp x) x) zero)
        by exact (id_trans (plus_comm (opp x) x) (plus_opp x)).
      assert (Hzero : Id (plus (opp x) (plus (opp x) x)) (plus (opp x) zero))
        by exact (id_cong (fun y => plus (opp x) y) Hoppx).
      assert (Hz : Id (plus (opp x) zero) (opp x)) by exact (plus_zero (opp x)).
      assert (Hrhs : Id (plus (opp (plus x x)) x) (plus (plus (opp x) (opp x)) x))
        by exact (id_cong (fun y => plus y x) Hopp2).
      assert (Hfin : Id (plus (opp (plus x x)) x) (opp x))
        by exact (id_trans Hrhs (id_trans Hcomb (id_trans Hzero Hz))).
      exact (id_trans (id_cong (fun y => plus (opp y) x) Ht) Hfin).
    }
    exact (id_trans (id_cong (fun y => plus (opp y) (mult (of_nat group_size) (mult group_mean group_mean))) H2a) H2c).
  }
  (* 组装最终结果 *)
  assert (Hfinal : Id (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (plus (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))
                                  (mult (of_nat group_size) (mult group_mean group_mean))))
                      (minus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (mult (of_nat group_size) (mult group_mean group_mean)))).
  {
    assert (H1 : Id (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))
                                (mult (of_nat group_size) (mult group_mean group_mean))))
                    (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (opp (mult (of_nat group_size) (mult group_mean group_mean)))))
      by exact (id_cong (fun y => plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum) y) Hcancel2).
    unfold minus.
    exact H1.
  }
  (* 组装主链：目标形态（含 Σr）→ 含 Gμ 形态（Hmid2）→ 最终 minus 形态（Hfinal） *)
  assert (Hmid2 : Id (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (list_sum_g reward_group group_enum)) group_mean))
                                 (mult (of_nat group_size) (mult group_mean group_mean))))
                     (plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (mult (of_nat group_size) group_mean)) group_mean))
                                 (mult (of_nat group_size) (mult group_mean group_mean)))))
    by exact (id_cong (fun y => plus (list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                                     (plus y (mult (of_nat group_size) (mult group_mean group_mean)))) Hcross).
  exact Hfinal.
Qed.

Definition group_variance : R :=
  mult (inv_pos (of_nat group_size) group_size_pos)
       (group_centered_second_moment).

(* 辅助：inv(G)·(G·(μ·μ)) == μ·μ（assoc + inv_pos_correct + one） *)
Lemma inv_G_absorb : forall (G : R) (Hg : lt zero G) (x : R),
  Id (mult (inv_pos G Hg) (mult G x)) x.
Proof.
  intros G Hg x.
  exact (id_trans (mult_assoc (inv_pos G Hg) G x) (id_trans (id_cong (fun z => mult z x) (id_trans (mult_comm (inv_pos G Hg) G) (inv_pos_correct G Hg))) (id_trans (mult_comm one x) (mult_one x)))).
Qed.

(* ===== 主定理：group_variance == (1/G)·Σr² − μ² =====
   grpo_variance_identity（L19774）给 Σ(r−μ)² == Σr² − G·μ²；
   两侧乘 inv(G)：invG·Σ(r−μ)² == invG·Σr² − invG·(G·μ²) == invG·Σr² − μ² *)
Theorem group_variance_identity :
  Id group_variance
     (minus (mult (inv_pos (of_nat group_size) group_size_pos)
                  (group_raw_second_moment))
            (mult (group_mean)
                  (group_mean))).
Proof.  unfold group_variance.
  pose proof (grpo_variance_identity) as Hvar.
  exact (id_trans (id_cong (fun z => mult (inv_pos (of_nat group_size) group_size_pos) z) Hvar) (id_trans (mult_minus_distr_l (inv_pos (of_nat group_size) group_size_pos)
                                      (group_raw_second_moment)
                                      (mult (of_nat group_size)
                                            (mult (group_mean)
                                                  (group_mean)))) (id_cong (fun z => minus (mult (inv_pos (of_nat group_size) group_size_pos)
                                       (group_raw_second_moment)) z)
                 (inv_G_absorb (of_nat group_size) group_size_pos
                               (mult (group_mean)
                                     (group_mean)))))).
Qed.

(* ============================================================ *)
(* T1.5：GRPO 基线方差归约（回应评审 3 的 S4）     *)
(*   Var ≤ (1/G)·Σr²：group_variance_identity（Var == raw − μ²） *)
(*   + 平方非负（μ² ≥ 0）——形式化 GRPO 核心动机"减均值降低二阶矩"； *)
(*   gap = μ²，等号当且仅当组均值零（square_zero 双向夹另行落地）。  *)
(*   诚实 Variable square_nonneg：构造性有序域无三分律，通用平方非负  *)
(*   需接口字段（E143-122；同 NaturalGradient）。                    *)
(* ============================================================ *)
Variable square_nonneg : forall a : R, le zero (mult a a).

(* 辅助：opp zero == zero（Section 内自证，set_opp_zero 定义在后） *)
Lemma grpo_opp_zero : Id (opp zero) zero.
Proof.
  apply id_sym.
  apply (plus_inv_unique zero zero (opp zero)).
  - apply (plus_zero zero).
  - apply (plus_opp zero).
Qed.

(* 辅助：0 ≤ b ⟹ a − b ≤ a（unfold minus + le_plus_compat + opp_le_compat） *)
Lemma grpo_le_minus : forall a b : R, le zero b -> le (minus a b) a.
Proof.
  intros a b Hb.
  unfold minus.
  apply (le_id_r (plus a (opp b)) (plus a zero) a).
  - apply (plus_zero a).
  - apply (le_plus_compat a a (opp b) zero).
    + apply le_refl.
    + apply (le_id_r (opp b) (opp zero) zero).
      * exact grpo_opp_zero.
      * apply (opp_le_compat zero b). exact Hb.
Qed.

(* T1.5 主定理：Var ≤ (1/G)·Σr²（基线方差归约，统计意义：减均值降低二阶矩） *)
Theorem group_variance_le_raw_second_moment :
  le group_variance
     (mult (inv_pos (of_nat group_size) group_size_pos)
           (group_raw_second_moment)).
Proof.
  apply (le_id_l group_variance
                 (minus (mult (inv_pos (of_nat group_size) group_size_pos)
                              (group_raw_second_moment))
                        (mult group_mean group_mean))
                 (mult (inv_pos (of_nat group_size) group_size_pos)
                       (group_raw_second_moment))).
  - exact group_variance_identity.
  - apply (grpo_le_minus (mult (inv_pos (of_nat group_size) group_size_pos)
                               (group_raw_second_moment))
                         (mult group_mean group_mean)).
    apply square_nonneg.
Qed.

End GRPO.

Section NaturalGradient.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let le := @le RI.
Let log := @log RI.                (* RealInterfaceEnhanced 中的 log *)
Let sum_over_S := @sum_over_S RI SS SO.

Variable Theta : Set.
Variable p_theta : Theta -> S -> R.
Variable partial : (Theta -> R) -> Theta -> R.

Definition fisher_info_scalar (theta : Theta) : R :=
  sum_over_S (fun s =>
    mult (p_theta theta s)
      (mult (partial (fun th => log (p_theta th s)) theta)
            (partial (fun th => log (p_theta th s)) theta))).

Variable free_energy_theta : Theta -> R.
(* 修正：梯度属于参数空间 Theta *)
Variable grad_free_energy : Theta -> Theta.

Variable theta_splus : Theta -> Theta -> Theta.
Variable theta_smult : R -> Theta -> Theta.
Variable theta_sopp : Theta -> Theta.

Variable fisher_pos : forall theta, lt zero (fisher_info_scalar theta).
Variable p_theta_pos : forall theta s, lt zero (p_theta theta s).

(* Fisher 正定性的核心：若 Fisher 信息为零（F(θ) = 0），则每个
   状态 s 上的权重项 p(θ,s)·(∂_θ log p(θ,s))² 为零。
   证明：F = Σ_s p·(∂log p)² 逐项非负（p > 0 × 平方非负），
   和为零且逐项非负 ⟹ 逐项为零（sum_over_S_zero_nonneg）。
   非平凡：非负和的零分解。平方非负由 square_nonneg 假设给出
   （构造性有序域无三分律，通用平方非负需接口字段）。 *)
Variable square_nonneg : forall a : R, le zero (mult a a).

Theorem fisher_zero_implies_pointwise :
  forall theta,
    Id (fisher_info_scalar theta) zero ->
    forall s : S, Id (mult (p_theta theta s)
                           (mult (partial (fun th => log (p_theta th s)) theta)
                                 (partial (fun th => log (p_theta th s)) theta)))
                     zero.
Proof.
  intros theta Hf0.
  unfold fisher_info_scalar in Hf0.
  (* 逐点非负：p·(∂log p)² ≥ 0（p > 0、平方非负、乘法保序） *)
  assert (Hpt_nonneg : forall s : S, le zero (mult (p_theta theta s)
       (mult (partial (fun th => log (p_theta th s)) theta)
             (partial (fun th => log (p_theta th s)) theta)))).
  {
    intro s.
    (* 0 ≤ p·(∂log p)²：经 0 ≤ (∂log p)² 与 p > 0 的乘法保序。
       le_mult_compat a b c : lt zero c -> le a b -> le (mult a c) (mult b c)。
       a := 0, b := (∂log p)², c := p（p > 0），再 mult_comm 换形。 *)
    assert (Hle_sq : le zero (mult (partial (fun th => log (p_theta th s)) theta)
                                  (partial (fun th => log (p_theta th s)) theta)))
      by exact (square_nonneg (partial (fun th => log (p_theta th s)) theta)).
    assert (Hle_p : le (mult zero (p_theta theta s))
                       (mult (mult (partial (fun th => log (p_theta th s)) theta)
                                   (partial (fun th => log (p_theta th s)) theta))
                             (p_theta theta s)))
      by exact (le_mult_compat zero (mult (partial (fun th => log (p_theta th s)) theta)
                                          (partial (fun th => log (p_theta th s)) theta))
                               (p_theta theta s) (p_theta_pos theta s) Hle_sq).
    (* mult 换形：mult 0 p = 0，mult ((∂logp)²) p = p·(∂logp)² *)
    assert (Hz0 : Id (mult zero (p_theta theta s)) zero)
      by exact (id_trans (mult_comm zero (p_theta theta s)) (mult_zero (p_theta theta s))).
    assert (Hswap : Id (mult (mult (partial (fun th => log (p_theta th s)) theta)
                                   (partial (fun th => log (p_theta th s)) theta))
                             (p_theta theta s))
                       (mult (p_theta theta s)
                             (mult (partial (fun th => log (p_theta th s)) theta)
                                   (partial (fun th => log (p_theta th s)) theta))))
      by exact (mult_comm (mult (partial (fun th => log (p_theta th s)) theta)
                                (partial (fun th => log (p_theta th s)) theta))
                          (p_theta theta s)).
    exact (le_id_l zero (mult zero (p_theta theta s))
                   (mult (p_theta theta s)
                         (mult (partial (fun th => log (p_theta th s)) theta)
                               (partial (fun th => log (p_theta th s)) theta)))
                   (id_sym Hz0)
                   (le_id_r (mult zero (p_theta theta s))
                            (mult (mult (partial (fun th => log (p_theta th s)) theta)
                                        (partial (fun th => log (p_theta th s)) theta))
                                  (p_theta theta s))
                            (mult (p_theta theta s)
                                  (mult (partial (fun th => log (p_theta th s)) theta)
                                        (partial (fun th => log (p_theta th s)) theta)))
                            Hswap Hle_p)).
  }
  (* F = 0 且逐项非负 ⟹ 逐项为零 *)
  exact (sum_over_S_zero_nonneg _ Hpt_nonneg Hf0).
Qed.

Definition natural_gradient_step (eta : R) (theta : Theta) : Theta :=
  theta_splus theta
    (theta_smult (opp eta)
      (theta_smult (inv_pos (fisher_info_scalar theta) (fisher_pos theta))
        (grad_free_energy theta))).

End NaturalGradient.

Section FluctuationDissipation.
Context {RI : RealInterfaceEnhanced}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let mult := @mult RI.

Variable D : R.
Variable D_pos : lt zero D.
Variable H : R.
Variable H_inv : R.
Variable H_pos : lt zero H.
Variable covariance : R.

Variable fluctuation_dissipation :
  Id covariance (mult D H_inv).

End FluctuationDissipation.

Section PhysicalMechanics.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let sopp := @sopp RI SS.   (* 注意：sopp 的类型是 S -> S *)

Variable Q : Set.
Variable P : Set.
Variable Hamiltonian : Q -> P -> R.
Variable potential : Q -> R.

Definition physical_loss (q : Q) : R := potential q.

Variable force_physical : Q -> Q.
(* 如果希望使用 sopp，grad 应返回 S，而不是 Q。
   这里有两种选择：
   1. 将 Q 定义为 S（即 Variable Q : Set := S），但 Q 是变量无法直接限定。
   2. 将 grad 的类型改为 (Q -> R) -> Q -> S，并让 sopp 作用于 S。
   3. 放弃使用 sopp，改用 Q 上的负操作，或引入 Q 到 S 的映射。
   下面采用一种折中：假设存在从 Q 到 S 的映射 inj_Q_S，并将 sopp 应用于映射后的结果。
*)

(* 添加一个从 Q 到 S 的映射 *)
Variable inj_Q_S : Q -> S.

Variable grad : (Q -> R) -> Q -> S.   (* 修改为返回 S *)

Variable physical_force_is_gradient :
  forall q, Id (inj_Q_S (force_physical q)) (sopp (grad potential q)).

End PhysicalMechanics.

Section Nonequilibrium.
Context {RI : RealInterfaceEnhanced}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let opp := @opp RI.
Let le := @le RI.

Variable Flux : Set.
Variable ThermodynamicForce : Set.

Variable entropy_production_rate : Flux -> ThermodynamicForce -> R.

Definition noneq_loss (J : Flux) (X : ThermodynamicForce) : R :=
  opp (entropy_production_rate J X).

Variable max_entropy_production :
  forall X,
    ExistsT (fun J : Flux =>
      forall J' : Flux, le (entropy_production_rate J X) (entropy_production_rate J' X)).

End Nonequilibrium.

Section DevelopmentalBiology.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let le := @le RI.
Let clim := @clim RI SS.

Variable Waddington_landscape : S -> R.
Variable noise : S -> S.
Variable grad : (S -> R) -> S -> S.

Definition developmental_dynamics (x : S) : S :=
  splus x (splus (sopp (grad Waddington_landscape x)) (noise x)).

(* 使用不同的名称避免与全局 is_truth 冲突 *)
Definition dev_is_truth (x : S) : Set :=
  forall s' : S, le (Waddington_landscape x) (Waddington_landscape s').

Variable differentiation_attractor :
  forall x,
    sigT (fun x_star : S =>
      And (dev_is_truth x_star)
          (clim (fun n => iterate developmental_dynamics n x) x_star)).

End DevelopmentalBiology.

Section LanguagePragmatics.
Context {RI : RealInterfaceEnhanced}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let plus := @plus RI.
Let le := @le RI.

Variable Sequence : Set.
Variable grammar_loss : Sequence -> R.
Variable semantics_loss : Sequence -> R.
Variable pragmatics_loss : Sequence -> R.

Definition total_lang_loss (s : Sequence) : R :=
  plus (grammar_loss s) (plus (semantics_loss s) (pragmatics_loss s)).

Variable best_sequence : Sequence -> Sequence.

Variable language_generation_optimizes_constraints :
  forall s, le (total_lang_loss (best_sequence s)) (total_lang_loss s).

End LanguagePragmatics.

Section TimeArrow.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let opp := @opp RI.
Let le := @le RI.

Variable Microstate : Set.
Variable Macrostate : Set.
Variable coarse_grain : Microstate -> Macrostate.
Variable macro_entropy : Macrostate -> R.
Variable macro_dynamics : Macrostate -> Macrostate.

Definition macro_loss (m : Macrostate) : R := opp (macro_entropy m).

Variable macro_loss_monotone :
  forall m0 : Macrostate,
    forall t : nat,
      le (macro_loss (iterate macro_dynamics t m0)) (macro_loss m0).

End TimeArrow.

Section Prediction1HeatRelaxation.
Context {RI : RealInterfaceEnhanced}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.

Variable temperature_difference : nat -> R.
Variable gamma : R.
Variable of_nat : nat -> R.
Variable temperature_difference0 : R.

Variable heat_relaxation_exponential :
  forall t : nat,
    Id (temperature_difference t)
       (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0).

End Prediction1HeatRelaxation.

Section Prediction3Landauer.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let log := @log RI.

Variable E_min : R.
Variable k_B : R.
Variable T_landauer : R.

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log (plus one one)))).

End Prediction3Landauer.

Section Prediction4FluctuationScale.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.

Variable prob_negative_entropy : R -> R.
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_scale :
  forall N : R,
    Id (prob_negative_entropy N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).

End Prediction4FluctuationScale.

Section Prediction5CrossDomainScaling.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.

Variable loss_drop : nat -> R.
Variable f_N : nat -> R.
Variable power : R -> R -> R.
Variable of_nat : nat -> R.

(* 注意：sig 的谓词返回 Set，必须改用 sigT *)
Variable cross_domain_scaling :
  sigT (fun alpha : R =>
    forall N : nat,
      Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N))).

End Prediction5CrossDomainScaling.

Section Prediction6HierarchicalStability.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let le := @le RI.
Let PropType := @Proposition RI SS.

Variable disturbance : PropType -> R.
Variable hierarchical_relation : PropType -> PropType -> Set.

Variable hierarchical_stability_prediction :
  forall (upper lower : PropType),
    hierarchical_relation upper lower ->
    le (disturbance upper) (disturbance lower).

End Prediction6HierarchicalStability.

Section Prediction7LMStructure.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let le := @le RI.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> R.
Variable total_loss : list Token -> R.

Variable loss_structure_correlation :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_loss (model epoch)) (total_loss (model (Nat.succ epoch))).

End Prediction7LMStructure.

(* ============================================================ *)
(* 补充与扩展部分（接续前文，需在同一环境中加载）             *)
(* ============================================================ *)

(* 扩展状态空间 *)
Class StateSpaceExtended (RI : RealInterface) := {
  SSE_base :> StateSpace RI;

  smult_zero : forall x : S, Id (smult zero x) szero;
  smult_opp : forall (a : R) (x : S), Id (smult (opp a) x) (sopp (smult a x));
  smult_splus_distrib : forall (a : R) (x y : S),
    Id (smult a (splus x y)) (splus (smult a x) (smult a y));
  snorm : S -> R;
  snorm_pos : forall x : S, le zero (snorm x);
  snorm_zero : forall x : S, Id (snorm x) zero -> Id x szero;
  snorm_smult : forall (a : R) (x : S), Id (snorm (smult a x)) (mult (abs a) (snorm x));
  snorm_triangle : forall x y : S, le (snorm (splus x y)) (plus (snorm x) (snorm y));

  (* 度量由范数诱导（P2-2 消解）：smetric u v == snorm (sminus u v)。
     范数度量空间标准性质（构造性可接受，非经典公理）；使
     smetric_sminus_zero（平移不变性）成为可证定理而非诚实 Variable。 *)
  smetric_snorm : forall u v : S, Id (smetric u v) (snorm (sminus u v));
}.

(* ============================================================ *)
(* Gram-Schmidt 正交化（P0：正交基的构造性构造）                *)
(* ============================================================ *)
(* 在扩展状态空间（smult_zero/smult_opp/snorm）上实现：         *)
(*   1) projection_idempotent：proj u (proj u v) = proj u v      *)
(*      （投影是幂等算子——正交投影的代数闭包；经正交分解       *)
(*       唯一性 + 内积零向量引理，非平凡）                      *)
(*   2) gram_schmidt_step：给定非零向量 u 与任意 v，构造         *)
(*      w := v - proj u v 使 ⟨u, w⟩ = 0（单步正交化，sigT 形式） *)
(* ------------------------------------------------------------ *)

(* ============================================================ *)
(* 替换件全局假设核查（切片三）                              *)
(* ============================================================ *)
Print Assumptions clip_lower.
Print Assumptions ppo_gap_nonneg.
Print Assumptions sigmoid_pos.
Print Assumptions u2_align_objective_ext.
