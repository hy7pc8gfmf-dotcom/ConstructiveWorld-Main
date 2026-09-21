(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   rppo_align_free_energy_pi_star（原 L1085，5 句玩具证）               *)
(*   rppo_pi_star_objective_value（原 L992，1 句玩具证）                  *)
(*   rppo_rlhf_optimal_value（原 L982，1 句玩具证）                       *)
(*   rppo_importance_ratio_self_one（原 L853，3 句玩具证）                *)
(*   rppo_dpo_reward_is_implicit（原 L277，3 句玩具证）                   *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPPO.v *)
(* *)
(* 目的： PPO 的 req 层基础面：优势、策略比与目标分解。 *)
(* 主件： rppo_advantage_expectation_zero / rppo_dpo_reward_is_implicit / rppo_align_objective_decomp。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign。 *)
(* 备注： 状态值、优势、KL 到参考策略为显式定义；求和接口三定律为前提。 *)
(* ============================================================ *)

(* UpReqPPO.v — 签名迁移批 3 收尾席：PPO/advantage 簇余件 + dpo_reward_is_implicit req 化
   上游：UpReqAlgebra.v（批 1 地基）+ UpReqAlign.v（批 3 主体：pos_dist/F_align_req/
     align_objective_req/relative_entropy_req/pi_star_req/req_pi_star_pos/
     req_align_energy_exp/req_le_of_minus_nonneg/rkl_opp_zero——全部只消费不重建）；
     纯 term-mode（req_trans 链 + compat 桥），零类型类重写层依赖；
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）。
   ----------------------------------------------------------------
   [区1 dpo_reward + advantage 期望簇]
     dpo_reward_is_implicit（L19616）→ rppo_dpo_reward_is_implicit（幂等δ对偶：
       定义级平移；对位注：RestA ralt_dir/ralt_log_ratio 为 dpo_implicit_reward req
     advantage_expectation_zero（L19844）→ rppo_advantage_expectation_zero（真证）。
     exact_improvement_identity（L19904）→ rppo_exact_improvement_identity
       rppo_advantage_sum_ref + rppo_KL_self_zero）。
     ppo_monotonic_improvement（L19940）→ rppo_ppo_monotonic_improvement（组装）。
     kl_penalty_sufficient（L19967）→ rppo_kl_penalty_sufficient（组装）。
   [区2 PPO gap / 目标分解 / 比率簇]
     ppo_gap_exact（L20008）→ rppo_ppo_gap_exact（真证；min/r_max 仅作符号载体
       零 le 消费——与冻结件 ppo_gap_nonneg（L20083）裁决边界逐位守住，不越界）。
     rlhf_optimal_value（L20544）→ rppo_rlhf_optimal_value（组装）。
       真证 ~15 步 req_trans 链；注：Id 显式假设件 align_objective_explicit（L20330）的
       req 内容与本件在 req 系逐定义可换（state_value_req==E_r、kl_to_ref_req==
     importance_ratio_self_one（L20708）→ rppo_importance_ratio_self_one（幂等δ对偶）。
     ppo_surrogate_raw_is_value_improvement（L20720）→
       rppo_ppo_surrogate_raw_is_value_improvement（真证：比率消去 + 求和线性 +
       归一化坍缩，~20 步）。
   [区3 FEP 显式 / Boltzmann / 外延簇]
     align_free_energy_explicit（L21108）→ rppo_align_free_energy_explicit（真证组装）。
     align_free_energy_pi_star（L21167）→ rppo_align_free_energy_pi_star（组装；
       UpReqAlign 基建独立落位，双向互证）。
     pi_star_objective_value（L21186）→ rppo_pi_star_objective_value（组装；Id 与
       rlhf_optimal_value L20544 双件同形，req 保持双件同位不合并）。
     free_energy_ext_t12（L21425）→ rppo_free_energy_ext_gen（真证；**对位结论**：
       真正 req 对位 = 本件（泛化能量/温度自由能外延），a_fe_ext 为其 align 固定
       能量特例）。
   [冻结 1 件] ppo_surrogate_conservative（L21209）→ **不建，冻结**。结论：req 接口
     min 字段 le 输出逐 eps 化（min_le_l : le (min a b) (plus a eps)），plain 形
     le (min a b) a 不可导出；与已冻结 4 兄弟件（clip_lower L19519/ppo_conservative
     L19526/std_ppo_conservative L19559/ppo_clip_upper L19606）及 ppo_gap_nonneg
     L20083 同因——批 5 min plain-le 裁决项，解冻路径在案。
   ----------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4）：
   1. log 前提化：dpo_reward_explicit/implicit_reward req 版携带 pos_dist pi 位；
     UpReqAlign ReqPPORatio 先例）。
   3. 桥假设位（诚实桥，Id 同位，不放大主张）：sum_ext/sum_add/sum_linear
     ReqLogBridge 同位）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* ReqPPOAdvantage：PPO/advantage 簇 req 主体                     *)
(*   （Id 原件：Alignment 节 L19616-21473；节参数逐位对齐）  *)
(* ============================================================ *)
Section ReqPPOAdvantage.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（UpReqAlign ReqAlignCore 同位） ---- *)
Variable sumf : (S -> Real) -> Real.
Hypothesis sum_ext :
  forall f g : S -> Real, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> Real,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : Real) (f : S -> Real),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).


Hypothesis rppo_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 节参数（Id Alignment 节 L18750-18768 同位） ---- *)
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.
Variable Zap : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).

(* ---- req 系节内定义（Id 同形） ---- *)
Definition state_value_req (p : S -> Real) : Real :=
  sumf (fun s => mult (p s) (reward s)).
Definition advantage_req (p : S -> Real) (s : S) : Real :=
  req_minus (reward s) (state_value_req p).
Definition kl_to_ref_req (p : S -> Real) (Hp : pos_dist S p) : Real :=
  relative_entropy_req S sumf p pi_ref Hp pi_ref_pos.
Definition rppo_pistar (s : S) : Real :=
  pi_star_req S sumf reward beta beta_pos pi_ref Zap s.
Definition rppo_pistar_pos (s : S) : lt zero (rppo_pistar s) :=
  req_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos Zap s.
Definition policy_ratio_req (pi p_old : S -> Real) (s : S) (Hpos : lt zero (p_old s)) : Real :=
  mult (pi s) (inv_pos (p_old s) Hpos).

(* ============ 求和机器（内机：rppo_sum_* 族） ============ *)

(* 内机 0：mult (opp 1)·x == opp x *)
Lemma rppo_opp_one_mult : forall x : Real, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  apply (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)).
  - exact (req_opp_mult_r one x).
  - apply (req_opp_compat (mult one x) x). apply req_mult_one_l.
Qed.

(* 内机 1：Σ opp f == opp Σ f *)
Lemma rppo_sum_opp :
  forall f : S -> Real, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s. apply (req_sym (mult (opp one) (f s)) (opp (f s))).
    exact (rppo_opp_one_mult (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + exact (rppo_opp_one_mult (sumf f)).
Qed.

(* 内机 2：Σ (f - g) == Σ f - Σ g *)
Lemma rppo_sum_minus :
  forall f g : S -> Real,
    req (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g.
  unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply sum_add.
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f)) (rppo_sum_opp g)).
Qed.

(* 内机 3：KL(p‖p) == 0（Id relative_entropy_self_zero L19207 req 版；真证：
   逐点 req_minus 自零 + 求和零坍缩） *)
Lemma rppo_KL_self_zero :
  forall (p : S -> Real) (Hp : pos_dist S p),
    req (relative_entropy_req S sumf p p Hp Hp) zero.
Proof.
  intros p Hp.
  apply (req_trans (relative_entropy_req S sumf p p Hp Hp)
                   (sumf (fun _ : S => zero)) zero).
  - apply (sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                   (fun _ : S => zero)).
    intro s.
    apply (req_trans (mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                     (mult (p s) zero) zero).
    + apply (req_mult_compat (p s) (p s)
                             (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))) zero
                             (req_refl (p s))).
      unfold req_minus. apply plus_opp.
    + apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => zero))
                     (sumf (fun s => mult zero (p s))) zero).
    + apply (sum_ext (fun _ : S => zero) (fun s => mult zero (p s))).
      intro s.
      exact (req_sym (mult zero (p s)) zero
                     (req_trans (mult zero (p s)) (mult (p s) zero) zero
                                (mult_comm zero (p s)) (mult_zero (p s)))).
    + apply (req_trans (sumf (fun s => mult zero (p s)))
                       (mult zero (sumf p)) zero).
      * apply (sum_linear zero p).
      * apply (req_trans (mult zero (sumf p)) (mult (sumf p) zero) zero).
        -- apply mult_comm.
        -- apply mult_zero.
Qed.

(* 内机 4：Σ p·c == c（常数提取 + 归一化坍缩；Id sum·collapse req 版） *)
Lemma rppo_constant_sum :
  forall (c : Real) (p : S -> Real),
    req (sumf p) one -> req (sumf (fun s => mult (p s) c)) c.
Proof.
  intros c p Hnorm.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (mult c (sumf p)) c).
  - apply (req_trans (sumf (fun s => mult (p s) c))
                     (sumf (fun s => mult c (p s)))
                     (mult c (sumf p))).
    + apply (sum_ext (fun s => mult (p s) c) (fun s => mult c (p s))).
      intro s. apply req_mult_comm_rewrite.
    + apply (sum_linear c (fun s => p s)).
  - apply (req_trans (mult c (sumf p)) (mult c one) c).
    + apply (req_mult_compat c c (sumf p) one (req_refl c) Hnorm).
    + apply req_mult_one_r.
Qed.

(* 内机 6：x + opp(y + x) == opp y（塌缩引擎；Id 内塌缩步 req 泛化） *)
Lemma rppo_plus_opp_plus_r : forall x y : Real,
  req (plus x (opp (plus y x))) (opp y).
Proof.
  intros x y.
  apply (req_trans (plus x (opp (plus y x)))
                   (plus x (plus (opp y) (opp x)))
                   (opp y)).
  - apply (req_plus_compat x x (opp (plus y x)) (plus (opp y) (opp x)) (req_refl x)).
    apply (req_opp_plus y x).
  - apply (req_trans (plus x (plus (opp y) (opp x)))
                     (plus (plus x (opp x)) (opp y))
                     (opp y)).
    + apply (req_trans (plus x (plus (opp y) (opp x)))
                       (plus x (plus (opp x) (opp y)))
                       (plus (plus x (opp x)) (opp y))).
      * apply (req_plus_compat x x (plus (opp y) (opp x)) (plus (opp x) (opp y))
                               (req_refl x) (plus_comm (opp y) (opp x))).
      * apply plus_assoc.
    + apply (req_trans (plus (plus x (opp x)) (opp y))
                       (plus zero (opp y))
                       (opp y)).
      * apply (req_plus_compat (plus x (opp x)) zero (opp y) (opp y)
                               (plus_opp x) (req_refl (opp y))).
      * apply (req_trans (plus zero (opp y)) (plus (opp y) zero) (opp y)).
        -- apply plus_comm.
        -- apply plus_zero.
Qed.

(* 内机 5：优势求和 Σ π·A_ref == V(π) − V(π_ref)（归一化位；真证） *)
Lemma rppo_advantage_sum_ref :
  forall (pi : S -> Real),
    req (sumf pi) one ->
    req (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
        (req_minus (state_value_req pi) (state_value_req pi_ref)).
Proof.
  intros pi Hnorm.
  apply (req_trans (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                   (sumf (fun s => req_minus (mult (pi s) (reward s))
                                             (mult (pi s) (state_value_req pi_ref))))
                   (req_minus (state_value_req pi) (state_value_req pi_ref))).
  - apply (sum_ext (fun s => mult (pi s) (advantage_req pi_ref s))
                   (fun s => req_minus (mult (pi s) (reward s))
                                       (mult (pi s) (state_value_req pi_ref)))).
    intro s. unfold advantage_req. apply req_mult_minus_distr_l.
  - apply (req_trans (sumf (fun s => req_minus (mult (pi s) (reward s))
                                               (mult (pi s) (state_value_req pi_ref))))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req pi_ref))))
                     (req_minus (state_value_req pi) (state_value_req pi_ref))).
    + apply rppo_sum_minus.
    + apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                             (opp (sumf (fun s => mult (pi s) (state_value_req pi_ref))))
                             (opp (state_value_req pi_ref))
                             (req_refl (state_value_req pi))).
      apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req pi_ref)))
                            (state_value_req pi_ref)).
      exact (rppo_constant_sum (state_value_req pi_ref) pi Hnorm).
Qed.

(* ============ 区1：dpo_reward + advantage 期望簇 ============ *)

(* ---- 件1 dpo_reward_is_implicit（基座 L19616；幂等δ对偶） ----
   Id 双定义同体；req 版双定义同体 + log 前提位（登记表 1）。
   对位注：RestA ralt_dir/ralt_log_ratio 为 dpo_implicit_reward req 同形。 *)
Definition dpo_reward_explicit_req (pi : S -> Real) (Hpi : pos_dist S pi) (s : S) : Real :=
  mult beta (req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s))).
Definition dpo_implicit_reward_req (pi : S -> Real) (Hpi : pos_dist S pi) (s : S) : Real :=
  mult beta (req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s))).

Lemma rppo_dpo_reward_is_implicit :
  forall (pi : S -> Real) (Hpi : pos_dist S pi) (s : S),
    req (dpo_reward_explicit_req pi Hpi s) (dpo_implicit_reward_req pi Hpi s).
Proof.
  intros pi Hpi s.
  unfold dpo_reward_explicit_req, dpo_implicit_reward_req.
  apply req_refl.
Qed.

(* ---- 件2 advantage_expectation_zero（基座 L19844；真证） ----
   Σ π·A_π == 0：逐点分配 + 求和线性 + 常数提取 + 归一化坍缩。 *)
Lemma rppo_advantage_expectation_zero :
  forall (pi : S -> Real),
    req (sumf pi) one ->
    req (sumf (fun s => mult (pi s) (advantage_req pi s))) zero.
Proof.
  intros pi Hnorm.
  apply (req_trans (sumf (fun s => mult (pi s) (advantage_req pi s)))
                   (sumf (fun s => req_minus (mult (pi s) (reward s))
                                             (mult (pi s) (state_value_req pi))))
                   zero).
  - apply (sum_ext (fun s => mult (pi s) (advantage_req pi s))
                   (fun s => req_minus (mult (pi s) (reward s))
                                       (mult (pi s) (state_value_req pi)))).
    intro s. unfold advantage_req. apply req_mult_minus_distr_l.
  - apply (req_trans (sumf (fun s => req_minus (mult (pi s) (reward s))
                                               (mult (pi s) (state_value_req pi))))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req pi))))
                     zero).
    + apply rppo_sum_minus.
    + apply (req_trans (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                  (sumf (fun s => mult (pi s) (state_value_req pi))))
                       (req_minus (state_value_req pi) (state_value_req pi))
                       zero).
      * apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                               (opp (sumf (fun s => mult (pi s) (state_value_req pi))))
                               (opp (state_value_req pi))
                               (req_refl (state_value_req pi))).
        apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req pi)))
                              (state_value_req pi)).
        exact (rppo_constant_sum (state_value_req pi) pi Hnorm).
      * unfold req_minus. apply plus_opp.
Qed.

(* ============ 区2 前置机器：align_objective 显式分解（件8 旗舰） ============ *)

(* ---- 件8 align_objective_decomp（基座 L20683；真证机器旗舰） ----
   J(p) == V(p) − β·KL(p‖π_ref)。
     → Σ p·log p = KL + Σ p·lgR → 内塌缩 opp(β·KL) → req_minus 形。 *)
Lemma rppo_align_objective_decomp :
  forall (p : S -> Real) (Hp : pos_dist S p),
    req (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
        (req_minus (state_value_req p)
                   (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))).
Proof.
  intros p Hp.
  (* 步A：Σ p·E_align == (Σ p·opp r) − (Σ p·β·lgR) *)
  assert (HA : req (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                   (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                              (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
  { apply (req_trans (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                     (sumf (fun s => req_minus (mult (p s) (opp (reward s)))
                                               (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                     (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
    - apply (sum_ext (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))
                     (fun s => req_minus (mult (p s) (opp (reward s)))
                                         (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))).
      intro s. exact (req_mult_minus_distr_l (p s) (opp (reward s))
                                             (mult beta (log (pi_ref s) (pi_ref_pos s)))).
    - apply rppo_sum_minus. }
  (* 步B：opp(Σ p·opp r) == V(p) *)
  assert (HB : req (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                   (state_value_req p)).
  { apply (req_trans (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                     (opp (sumf (fun s => opp (mult (p s) (reward s)))))
                     (state_value_req p)).
    - apply (req_opp_compat (sumf (fun s => mult (p s) (opp (reward s))))
                            (sumf (fun s => opp (mult (p s) (reward s))))).
      apply (sum_ext (fun s => mult (p s) (opp (reward s)))
                     (fun s => opp (mult (p s) (reward s)))).
      intro s. apply req_opp_mult_l.
    - apply (req_trans (opp (sumf (fun s => opp (mult (p s) (reward s)))))
                       (opp (opp (sumf (fun s => mult (p s) (reward s)))))
                       (state_value_req p)).
      + apply (req_opp_compat (sumf (fun s => opp (mult (p s) (reward s))))
                              (opp (sumf (fun s => mult (p s) (reward s))))).
        apply rppo_sum_opp.
      + apply req_double_neg. }
  (* 步C：opp(Σ p·E) == V(p) + Σ p·β·lgR *)
  assert (HC : req (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                   (plus (state_value_req p)
                         (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
  { apply (req_trans (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                     (opp (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                     (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))))
                     (plus (state_value_req p)
                           (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
    - apply (req_opp_compat (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                            (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
      exact HA.
    - apply (req_trans (opp (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))))
                       (plus (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                       (plus (state_value_req p)
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
      + exact (req_opp_minus (sumf (fun s => mult (p s) (opp (reward s))))
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))).
      + apply (req_plus_compat (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                               (state_value_req p)
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               HB (req_refl (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))). }
  (* 步D：Σ p·β·lgR == β·Σ p·lgR *)
  assert (HD : req (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                   (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
  { apply (req_trans (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                     (sumf (fun s => mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                     (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
    - apply (sum_ext (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))
                     (fun s => mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      intro s.
      apply (req_trans (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))
                       (mult (mult (p s) beta) (log (pi_ref s) (pi_ref_pos s)))
                       (mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      + apply mult_assoc.
      + apply (req_trans (mult (mult (p s) beta) (log (pi_ref s) (pi_ref_pos s)))
                         (mult (mult beta (p s)) (log (pi_ref s) (pi_ref_pos s)))
                         (mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
        * apply (req_mult_compat (mult (p s) beta) (mult beta (p s))
                                 (log (pi_ref s) (pi_ref_pos s)) (log (pi_ref s) (pi_ref_pos s))
                                 (mult_comm (p s) beta) (req_refl (log (pi_ref s) (pi_ref_pos s)))).
        * apply (req_sym _ _ (mult_assoc beta (p s) (log (pi_ref s) (pi_ref_pos s)))).
    - apply (sum_linear beta (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))). }
  
  assert (HE : req (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                   (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                         (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
  { apply (req_trans (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                     (sumf (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                     (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                           (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
    - apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                     (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                    (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      intro s.
      apply (req_trans (mult (p s) (log (p s) (Hp s)))
                       (plus (req_minus (mult (p s) (log (p s) (Hp s)))
                                        (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                             (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                       (plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                             (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      + apply (req_trans (mult (p s) (log (p s) (Hp s)))
                         (plus (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                         (plus (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
        * exact (req_sym _ _ (req_minus_plus_cancel (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                                                    (mult (p s) (log (p s) (Hp s))))).
        * apply plus_comm.
      + apply (req_plus_compat (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (req_sym _ _ (req_mult_minus_distr_l (p s) (log (p s) (Hp s))
                                                                    (log (pi_ref s) (pi_ref_pos s))))
                               (req_refl (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
    - apply (req_trans (sumf (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                            (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                       (plus (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s)))))
                             (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                       (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                             (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
      + apply sum_add.
      + apply (req_plus_compat (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s)))))
                               (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                               (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (req_refl (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                               (req_refl (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))). }
  (* 步F：总装配 *)
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                   (plus (plus (state_value_req p)
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                         (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                   (req_minus (state_value_req p)
                              (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
  - 
    apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                     (plus (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                     (plus (plus (state_value_req p)
                                 (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
    + (* align_objective_req δ= opp(F_align_req) = opp(plus ΣE βΣlogp) *)
      unfold align_objective_req, F_align_req.
      exact (req_opp_plus (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                          (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))).
    + apply (req_plus_compat (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                             (plus (state_value_req p)
                                   (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                             HC (req_refl (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
  - (* 内塌缩：W + opp(β·(KL + Lref)) == opp(β·KL)；收 req_minus 形 *)
    apply (req_trans (plus (plus (state_value_req p)
                                 (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                     (plus (state_value_req p)
                           (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                            (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))
                     (req_minus (state_value_req p)
                                (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
    + (* assoc 重排 + W 形变换（步D/步E） *)
      assert (HBeta : req (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                          (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))).
      { apply (req_trans (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                                          (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))
                         (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                               (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))).
        - apply (req_mult_compat beta beta
                                 (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                                 (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                                       (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (req_refl beta) HE).
        - exact (distrib beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                              (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))). }
      assert (Hinner : req (plus (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                           (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                            (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))))).
      { apply (req_plus_compat (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                               (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                               (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                          (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))
                               HD
                               (req_opp_compat (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                                               (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                                     (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))
                                               HBeta)). }
      apply (req_trans (plus (plus (state_value_req p)
                                   (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                       (plus (state_value_req p)
                             (plus (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))))
                       (plus (state_value_req p)
                             (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                              (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))).
      * apply (req_sym _ _ (plus_assoc (state_value_req p)
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                       (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
      * apply (req_plus_compat (state_value_req p) (state_value_req p) _ _
                               (req_refl (state_value_req p)) Hinner).
    + (* x + opp(y + x) == opp(y)，x := β·Lref, y := β·KL（消费内机 6） *)
      assert (Hcol : req (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                               (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                          (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))))
                          (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      { exact (rppo_plus_opp_plus_r
                 (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                 (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))). }
      apply (req_trans (plus (state_value_req p)
                             (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                              (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))
                       (plus (state_value_req p)
                             (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))))
                       (req_minus (state_value_req p)
                                  (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      * apply (req_plus_compat (state_value_req p) (state_value_req p) _ _ (req_refl (state_value_req p)) Hcol).
      * unfold req_minus. apply req_refl.
Qed.

(* ---- 件3 exact_improvement_identity（基座 L19904；真证组装） ---- *)
Lemma rppo_exact_improvement_identity :
  forall (pi_new : S -> Real) (Hnorm : req (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    req (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                   (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
        (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                   (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))).
Proof.
  intros pi_new Hnorm Hpos.
  (* 步1：J(π_ref) == V(π_ref)（KL 自零 + req_minus 零右消去） *)
  assert (Hr : req (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                   (state_value_req pi_ref)).
  { apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                     (req_minus (state_value_req pi_ref)
                                (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                     (state_value_req pi_ref)).
    - exact (rppo_align_objective_decomp pi_ref pi_ref_pos).
    - apply (req_trans (req_minus (state_value_req pi_ref)
                                  (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                       (req_minus (state_value_req pi_ref) zero)
                       (state_value_req pi_ref)).
      + apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                               (opp (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                               (opp zero)
                               (req_refl (state_value_req pi_ref))).
        apply (req_opp_compat (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)) zero).
        apply (req_trans (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos))
                         (mult beta zero) zero).
        * apply (req_mult_compat beta beta
                                 (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos) zero
                                 (req_refl beta) (rppo_KL_self_zero pi_ref pi_ref_pos)).
        * apply mult_zero.
      + apply (req_trans (req_minus (state_value_req pi_ref) zero)
                         (plus (state_value_req pi_ref) (opp zero))
                         (state_value_req pi_ref)).
        * unfold req_minus. apply req_refl.
        * apply (req_trans (plus (state_value_req pi_ref) (opp zero))
                           (plus (state_value_req pi_ref) zero)
                           (state_value_req pi_ref)).
          -- apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                                    (opp zero) zero (req_refl (state_value_req pi_ref))).
             exact (rkl_opp_zero).
          -- apply plus_zero. }
  (* 步2：J(new) − J(ref) → (V_n − βKL − V_r) → E_adv − βKL *)
  apply (req_trans (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                              (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
                   (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                              (state_value_req pi_ref))
                   (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                              (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
  - apply (req_plus_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                           (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
                           (opp (state_value_req pi_ref))
                           (req_refl (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos))
                           (req_opp_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                                           (state_value_req pi_ref) Hr)).
  - apply (req_trans (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                                (state_value_req pi_ref))
                     (req_minus (req_minus (state_value_req pi_new)
                                           (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                (state_value_req pi_ref))
                     (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
    + apply (req_plus_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                             (req_minus (state_value_req pi_new)
                                        (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                             (opp (state_value_req pi_ref)) (opp (state_value_req pi_ref))
                             (rppo_align_objective_decomp pi_new Hpos) (req_refl (opp (state_value_req pi_ref)))).
    + apply (req_trans (req_minus (req_minus (state_value_req pi_new)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                  (state_value_req pi_ref))
                       (req_minus (state_value_req pi_new)
                                  (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                        (state_value_req pi_ref)))
                       (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                  (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
      * exact (req_sym _ _ (req_minus_plus_r (state_value_req pi_new)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                             (state_value_req pi_ref))).
      * apply (req_trans (req_minus (state_value_req pi_new)
                                    (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                          (state_value_req pi_ref)))
                         (req_minus (state_value_req pi_new)
                                    (plus (state_value_req pi_ref)
                                          (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                         (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                    (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
        -- apply (req_plus_compat (state_value_req pi_new) (state_value_req pi_new)
                                  (opp (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                             (state_value_req pi_ref)))
                                  (opp (plus (state_value_req pi_ref)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                                  (req_refl (state_value_req pi_new))).
           apply (req_opp_compat (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                       (state_value_req pi_ref))
                                 (plus (state_value_req pi_ref)
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
           apply plus_comm.
        -- apply (req_trans (req_minus (state_value_req pi_new)
                                       (plus (state_value_req pi_ref)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                            (req_minus (req_minus (state_value_req pi_new) (state_value_req pi_ref))
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                            (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
           ++ apply req_minus_plus_r.
           ++ apply (req_plus_compat (req_minus (state_value_req pi_new) (state_value_req pi_ref))
                                     (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                     (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                     (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                     (req_sym _ _ (rppo_advantage_sum_ref pi_new Hnorm))
                                     (req_refl (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))).
Qed.

(* ---- 件4 ppo_monotonic_improvement（基座 L19940；组装） ---- *)
Lemma rppo_ppo_monotonic_improvement :
  forall (pi_new : S -> Real) (Hnorm : req (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    le zero (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))) ->
    le (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
       (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos).
Proof.
  intros pi_new Hnorm Hpos Hur.
  apply (req_le_of_minus_nonneg
           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)).
  apply (req_le_compat zero zero
           (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                      (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
           (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                      (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))).
  - apply req_refl.
  - apply (req_sym _ _).
    exact (rppo_exact_improvement_identity pi_new Hnorm Hpos).
  - exact Hur.
Qed.

(* ---- 件5 kl_penalty_sufficient（基座 L19967；组装） ---- *)
Lemma rppo_kl_penalty_sufficient :
  forall (pi_new : S -> Real) (eps : Real)
         (Hnorm : req (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    le (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos) eps ->
    le (mult beta eps) (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s))) ->
    le (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
       (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos).
Proof.
  intros pi_new eps Hnorm Hpos Hkl Hadv.
  apply (rppo_ppo_monotonic_improvement pi_new Hnorm Hpos).
  apply (req_le_minus_nonneg (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                             (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))).
  apply (le_trans (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                  (mult beta eps)
                  (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))).
  - apply (req_le_mult_compat_r beta
                                (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos) eps
                                (lt_le_iff zero beta (inl beta_pos)) Hkl).
  - exact Hadv.
Qed.

(* ============ 区2：PPO gap / 比率簇（基座 PPO 块 L19495-19520 同位） ============ *)

Variable pi_old : S -> Real.
Variable pi_old_pos : forall s : S, lt zero (pi_old s).
Variable advantage_fn : S -> Real.
Variable epsilon : Real.

(* 重要性采样比率（π*/π_old；Id importance_ratio L19502 req 同形） *)
Definition rppo_star_old_ratio (s : S) : Real :=
  mult (rppo_pistar s) (inv_pos (pi_old s) (pi_old_pos s)).
(* 裁剪（Id clip L19506 req 同形；min/r_max 仅符号载体） *)
Definition rppo_clip (r : Real) : Real :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).
(* PPO 裁剪代理目标（Id ppo_objective L19510 req 同形） *)
Definition rppo_ppo_objective : Real :=
  sumf (fun s => mult (pi_old s)
                      (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                            (advantage_fn s))).
(* 未裁剪 IS 目标（Id is_objective L19515 req 同形） *)
Definition rppo_is_objective : Real :=
  sumf (fun s => mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s))).

(* ---- 件6 ppo_gap_exact（基座 L20008；真证；min/r_max 零 le 消费） ---- *)
Lemma rppo_ppo_gap_exact :
  req (req_minus rppo_is_objective rppo_ppo_objective)
      (sumf (fun s => mult (pi_old s)
                           (mult (req_minus (rppo_star_old_ratio s)
                                            (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                 (advantage_fn s)))).
Proof.
  (* 逐点：p·(r·A) − p·(m·A) == p·((r−m)·A)（双层分配 + 换序） *)
  assert (Hpt : forall s : S,
    req (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                   (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                          (advantage_fn s))))
        (mult (pi_old s) (mult (req_minus (rppo_star_old_ratio s)
                                          (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                               (advantage_fn s)))).
  { intro s.
    (* 外层：p·X − p·Y == p·(X − Y)（req_mult_minus_distr_l 反向） *)
    assert (H1 : req (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                 (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s)))))
      by exact (req_sym _ _ (req_mult_minus_distr_l (pi_old s)
                                                    (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                    (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                          (advantage_fn s)))).
    (* 内层：(r·A) − (m·A) == (r − m)·A（comm + 分配反向 + comm 换回） *)
    assert (H2 : req (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                      (advantage_fn s)))
                     (mult (req_minus (rppo_star_old_ratio s)
                                      (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                           (advantage_fn s))).
    { apply (req_sym (mult (req_minus (rppo_star_old_ratio s)
                                      (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                           (advantage_fn s))
                     (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                      (advantage_fn s)))).
      apply (req_trans (mult (req_minus (rppo_star_old_ratio s)
                                        (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                             (advantage_fn s))
                       (mult (advantage_fn s) (req_minus (rppo_star_old_ratio s)
                                                         (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                       (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                  (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                        (advantage_fn s)))).
      - apply mult_comm.
      - apply (req_trans (mult (advantage_fn s) (req_minus (rppo_star_old_ratio s)
                                                           (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                         (req_minus (mult (advantage_fn s) (rppo_star_old_ratio s))
                                    (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                         (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                    (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                          (advantage_fn s)))).
        + exact (req_mult_minus_distr_l (advantage_fn s) (rppo_star_old_ratio s)
                                        (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))).
        + unfold req_minus.
          apply (req_plus_compat (mult (advantage_fn s) (rppo_star_old_ratio s))
                                 (mult (rppo_star_old_ratio s) (advantage_fn s))
                                 (opp (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                                 (opp (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                            (advantage_fn s)))
                                 (mult_comm (advantage_fn s) (rppo_star_old_ratio s))).
          apply (req_opp_compat (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))) (advantage_fn s))).
          apply mult_comm. }
    apply (req_trans (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                 (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (mult (req_minus (rppo_star_old_ratio s)
                                                       (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                            (advantage_fn s)))).
    - exact H1.
    - apply (req_mult_compat (pi_old s) (pi_old s) _ _ (req_refl (pi_old s)) H2). }
  (* 求和输运：Σ(f − g) == Σf − Σg（反向） + 逐点 *)
  apply (req_trans (req_minus rppo_is_objective rppo_ppo_objective)
                   (sumf (fun s => req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                             (mult (pi_old s)
                                                   (mult (min (rppo_star_old_ratio s)
                                                              (rppo_clip (rppo_star_old_ratio s)))
                                                         (advantage_fn s)))))
                   (sumf (fun s => mult (pi_old s)
                                        (mult (req_minus (rppo_star_old_ratio s)
                                                         (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                              (advantage_fn s))))).
  - apply (req_sym _ _ (rppo_sum_minus (fun s => mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                       (fun s => mult (pi_old s)
                                                      (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                            (advantage_fn s))))).
  - apply (sum_ext (fun s => req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                       (mult (pi_old s)
                                             (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                   (advantage_fn s))))
                   (fun s => mult (pi_old s)
                                  (mult (req_minus (rppo_star_old_ratio s)
                                                   (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                        (advantage_fn s)))).
    exact Hpt.
Qed.

(* ---- 件9 importance_ratio_self_one（基座 L20708；幂等δ对偶） ---- *)
Lemma rppo_importance_ratio_self_one :
  forall (p : S -> Real) (Hp : pos_dist S p) (s : S),
    req (policy_ratio_req p p s (Hp s)) one.
Proof.
  intros p Hp s.
  unfold policy_ratio_req.
  apply inv_pos_correct.
Qed.

(* ---- 件10 ppo_surrogate_raw_is_value_improvement（基座 L20720；真证） ---- *)
Lemma rppo_ppo_surrogate_raw_is_value_improvement :
  forall (pi p_old : S -> Real) (Hpos : forall s : S, lt zero (p_old s))
         (Hnorm : req (sumf pi) one),
    req (sumf (fun s => mult (p_old s)
                             (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s))))
        (req_minus (state_value_req pi) (state_value_req p_old)).
Proof.
  intros pi p_old Hpos Hnorm.
  (* 逐点比率消去：p·((π/p)·X) == π·X（~6 步 req 链） *)
  assert (Hpt : forall s : S,
    req (mult (p_old s) (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s)))
        (mult (pi s) (advantage_req p_old s))).
  { intro s.
    assert (H1 : req (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)))
                     (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s)))
      by exact (mult_assoc (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)).
    assert (H2 : req (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s))
                     (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                                (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (mult_assoc (p_old s) (pi s) (inv_pos (p_old s) (Hpos s)))
                                (req_refl (advantage_req p_old s))).
    assert (H3 : req (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s))
                     (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                                (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_compat (mult (p_old s) (pi s)) (mult (pi s) (p_old s))
                                                 (inv_pos (p_old s) (Hpos s))
                                                 (inv_pos (p_old s) (Hpos s))
                                                 (mult_comm (p_old s) (pi s))
                                                 (req_refl (inv_pos (p_old s) (Hpos s))))
                                (req_refl (advantage_req p_old s))).
    assert (H3b : req (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                            (advantage_req p_old s))
                     (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                                (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_sym _ _ (mult_assoc (pi s) (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (req_refl (advantage_req p_old s))).
    assert (H4 : req (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s))
                     (mult (mult (pi s) one) (advantage_req p_old s)))
      by exact (req_mult_compat (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (mult (pi s) one)
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_compat (pi s) (pi s)
                                                 (mult (p_old s) (inv_pos (p_old s) (Hpos s))) one
                                                 (req_refl (pi s)) (inv_pos_correct (p_old s) (Hpos s)))
                                (req_refl (advantage_req p_old s))).
    assert (H5 : req (mult (mult (pi s) one) (advantage_req p_old s))
                     (mult (pi s) (advantage_req p_old s)))
      by exact (req_mult_compat (mult (pi s) one) (pi s)
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_one_r (pi s)) (req_refl (advantage_req p_old s))).
    unfold policy_ratio_req.
    apply (req_trans (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)))
                     (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                     (mult (pi s) (advantage_req p_old s))).
    - exact H1.
    - apply (req_trans (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                       (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                       (mult (pi s) (advantage_req p_old s))).
      + exact H2.
      + apply (req_trans (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                         (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                         (mult (pi s) (advantage_req p_old s))).
        * exact H3.
        * apply (req_trans (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                           (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                           (mult (pi s) (advantage_req p_old s))).
          -- exact H3b.
          -- apply (req_trans (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                              (mult (mult (pi s) one) (advantage_req p_old s))
                              (mult (pi s) (advantage_req p_old s))).
             ++ exact H4.
              ++ exact H5. }
  apply (req_trans (sumf (fun s => mult (p_old s)
                                        (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s))))
                   (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                   (req_minus (state_value_req pi) (state_value_req p_old))).
  - apply (sum_ext (fun s => mult (p_old s)
                                  (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s)))
                   (fun s => mult (pi s) (advantage_req p_old s))).
    exact Hpt.
  - apply (req_trans (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req p_old))))
                     (req_minus (state_value_req pi) (state_value_req p_old))).
    + apply (req_trans (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                       (sumf (fun s => req_minus (mult (pi s) (reward s))
                                                 (mult (pi s) (state_value_req p_old))))
                       (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                  (sumf (fun s => mult (pi s) (state_value_req p_old))))).
      * apply (sum_ext (fun s => mult (pi s) (advantage_req p_old s))
                       (fun s => req_minus (mult (pi s) (reward s))
                                           (mult (pi s) (state_value_req p_old)))).
        intro s. unfold advantage_req. apply req_mult_minus_distr_l.
      * apply rppo_sum_minus.
    + apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                             (opp (sumf (fun s => mult (pi s) (state_value_req p_old))))
                             (opp (state_value_req p_old))
                             (req_refl (state_value_req pi))).
      apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req p_old)))
                            (state_value_req p_old)).
      exact (rppo_constant_sum (state_value_req p_old) pi Hnorm).
Qed.

(* ============ 区3：显式值 / FEP 显式 / Boltzmann / 外延簇 ============ *)

(* ---- 件7 rlhf_optimal_value（基座 L20544 Corollary；组装） ---- *)
Lemma rppo_rlhf_optimal_value :
  req (align_objective_req S sumf reward beta pi_ref pi_ref_pos rppo_pistar rppo_pistar_pos)
      (req_minus (state_value_req rppo_pistar)
                 (mult beta (relative_entropy_req S sumf rppo_pistar pi_ref rppo_pistar_pos pi_ref_pos))).
Proof.
  exact (rppo_align_objective_decomp rppo_pistar rppo_pistar_pos).
Qed.

(* ---- 件13 pi_star_objective_value（基座 L21186 Corollary；组装） ----
   Id 与件7 双件同形——req 保持双件同位（件数核对不合并）。 *)
Lemma rppo_pi_star_objective_value :
  req (align_objective_req S sumf reward beta pi_ref pi_ref_pos rppo_pistar rppo_pistar_pos)
      (req_minus (state_value_req rppo_pistar)
                 (mult beta (relative_entropy_req S sumf rppo_pistar pi_ref rppo_pistar_pos pi_ref_pos))).
Proof.
  exact (rppo_align_objective_decomp rppo_pistar rppo_pistar_pos).
Qed.

(* ---- 件11 align_free_energy_explicit（基座 L21108；真证组装） ---- *)
Lemma rppo_align_free_energy_explicit :
  forall (p : S -> Real) (Hp : pos_dist S p),
    req (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)
        (plus (opp (state_value_req p))
              (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))).
Proof.
  intros p Hp.
  apply (req_trans (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                   (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp))
                   (plus (opp (state_value_req p))
                         (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
  - apply (req_sym (opp (opp (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)))
                   (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)).
    exact (req_double_neg (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)).
  - apply (req_trans (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp))
                     (opp (req_minus (state_value_req p)
                                     (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))))
                     (plus (opp (state_value_req p))
                           (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
    + apply (req_opp_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                            (req_minus (state_value_req p)
                                       (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))
                            (rppo_align_objective_decomp p Hp)).
    + unfold req_minus.
      apply (req_trans (opp (plus (state_value_req p)
                                  (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))))
                       (plus (opp (state_value_req p))
                             (opp (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))))
                       (plus (opp (state_value_req p))
                             (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      * apply req_opp_plus.
      * apply (req_plus_compat (opp (state_value_req p)) (opp (state_value_req p)) _ _
                               (req_refl (opp (state_value_req p)))).
        apply req_double_neg.
Qed.

(* ---- 件15 free_energy_ext_t12（基座 L21425；真证；对位结论见头注） ----
   泛化能量/温度自由能外延（req log 前提位：Id 免费事实的诚实桥承接）。 *)
Definition F_gen_req (energy : S -> Real) (D : Real) (p : S -> Real) (Hp : pos_dist S p) : Real :=
  plus (sumf (fun s => mult (p s) (energy s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

Lemma rppo_free_energy_ext_gen :
  forall (energy : S -> Real) (D : Real) (p q : S -> Real)
         (Hp : pos_dist S p) (Hq : pos_dist S q),
    (forall s : S, req (p s) (q s)) ->
    req (F_gen_req energy D p Hp) (F_gen_req energy D q Hq).
Proof.
  intros energy D p q Hp Hq Hpq.
  unfold F_gen_req.
  apply (req_plus_compat (sumf (fun s => mult (p s) (energy s)))
                         (sumf (fun s => mult (q s) (energy s)))
                         (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - apply (sum_ext (fun s => mult (p s) (energy s)) (fun s => mult (q s) (energy s))).
    intro s.
    apply (req_mult_compat (p s) (q s) (energy s) (energy s) (Hpq s) (req_refl (energy s))).
  - apply (req_mult_compat D D (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                               (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                               (req_refl D)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (q s) (log (q s) (Hq s)))).
    intro s.
    apply (req_mult_compat (p s) (q s) (log (p s) (Hp s)) (log (q s) (Hq s)) (Hpq s)).
    apply (rppo_log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpq s)).
Qed.

(* Boltzmann req 同形（Id boltzmann_dist@align 实例 L15793 形）+ 正性 *)
Definition rppo_boltzmann (s : S) : Real :=
  mult (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)
       (exp_neg (mult (inv_pos beta beta_pos)
                      (align_energy_req S reward beta pi_ref pi_ref_pos s))).

Lemma rppo_boltzmann_pos : pos_dist S rppo_boltzmann.
Proof.
  intro s.
  unfold rppo_boltzmann.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ---- 件12 align_free_energy_pi_star（基座 L21167；组装） ----
   π* 与 Boltzmann 共享对齐自由能（F 外延 + 逐点闭式指数恒等）。 *)
Lemma rppo_align_free_energy_pi_star :
  req (F_gen_req (align_energy_req S reward beta pi_ref pi_ref_pos) beta
                 rppo_pistar rppo_pistar_pos)
      (F_gen_req (align_energy_req S reward beta pi_ref pi_ref_pos) beta
                 rppo_boltzmann rppo_boltzmann_pos).
Proof.
  apply (rppo_free_energy_ext_gen (align_energy_req S reward beta pi_ref pi_ref_pos) beta                                  rppo_pistar rppo_boltzmann                                  rppo_pistar_pos rppo_boltzmann_pos).
  intro s.
  apply (req_mult_compat (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)                         (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)                         (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))                         (exp_neg (mult (inv_pos beta beta_pos)                                        (align_energy_req S reward beta pi_ref pi_ref_pos s)))                         (req_refl (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap))).
  apply (req_sym _ _).
  exact (req_align_energy_exp S reward beta beta_pos pi_ref pi_ref_pos s).
Qed.


(* ---- 件16 align_objective_advantage_decomp（基座 L19350；真证组装） ----
   J(π) == J(π_ref) + (Σ π·A_ref − β·KL(π‖π_ref))（单步 bandit 精确恒等式，非近似）。
   Id 原文（L19349-19358，Alignment 节）：
     Theorem align_objective_advantage_decomp : forall pi : S -> R,
       normalized pi -> positive_dist pi ->
       Id (align_objective pi)
          (plus (align_objective pi_ref)
                (minus (sum_over_S (fun s => mult (pi s) (advantage pi_ref s)))
                       (mult beta (kl_to_ref pi)))).
   req 组装链（全部消费本文件既有件，零新建桥假设）：
     件8 rppo_align_objective_decomp（J = V − βKL，π 与 π_ref 双实例）
       + rppo_KL_self_zero（KL 对角自零 → J(π_ref) = V(π_ref)）
       + 内机5 rppo_advantage_sum_ref（Σ π·A_ref = V(π) − V(π_ref)，归一化位）
         三步 + plus_opp/plus_zero 归零）。
   命名对位：state_value_req==V、advantage_req==A、relative_entropy_req==kl_to_ref
     （kl_to_ref_req 同形 δ 可换，沿件3 语句惯例直用 relative_entropy_req）。
   封存改道（2026-09-09 终验席）：原节内双 assert（塌缩引理 / J(π_ref)==V(π_ref)）
     40min 无 .vo）；提级为独立件 rppo_b_collapse_minus（内机6）/
   根因修复（同席，定位探针二轮）：装配层尾腿原为 req_sym 内机5 裸喂
     req_plus_compat H2 槽——槽型 req (req_minus (req_minus Vπ Vref) KL)
     (req_minus A_sum KL) 与内机5 对称型 req (req_minus Vπ Vref) A_sum 差一层
     req_minus 双参同态运输，apply 进 δ 展开搜索死旋（glob 停在语句行即此；
     40min 内存爬升后 worker 静默亡=根源非封存非热载）；补 req_plus_compat
     双 opp-KL 腿 + req_refl 运输（req_minus δ 透明 plus a (opp b) 可转换）。 *)
(* 内机6（件16 提级伴件，2026-09-09 终验席封存改道）：塌缩引理
   b + ((a−b)−c) == a−c（Id 第4/5步 req 合并形）——原为件16 节内 assert，
   单件巨型封存在 .vo 期膨胀致死（四轮实证 EXIT=127 零输出），提级独立。 *)
Lemma rppo_b_collapse_minus :
  forall a b c : Real,
  req (plus b (req_minus (req_minus a b) c)) (req_minus a c).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus b (plus (plus a (opp b)) (opp c)))
                   (plus (plus b (plus a (opp b))) (opp c))
                   (plus a (opp c))).
  - apply plus_assoc.
  - apply (req_trans (plus (plus b (plus a (opp b))) (opp c))
                     (plus (plus a (plus b (opp b))) (opp c))
                     (plus a (opp c))).
    + apply (req_plus_compat (plus b (plus a (opp b)))
                             (plus a (plus b (opp b)))
                             (opp c) (opp c)
                             (req_trans (plus b (plus a (opp b)))
                                        (plus (plus b a) (opp b))
                                        (plus a (plus b (opp b)))
                                        (plus_assoc b a (opp b))
                                        (req_trans (plus (plus b a) (opp b))
                                                   (plus (plus a b) (opp b))
                                                   (plus a (plus b (opp b)))
                                                   (req_plus_compat (plus b a) (plus a b)
                                                                    (opp b) (opp b)
                                                                    (plus_comm b a)
                                                                    (req_refl (opp b)))
                                                   (req_sym _ _ (plus_assoc a b (opp b)))))
                             (req_refl (opp c))).
    + apply (req_trans (plus (plus a (plus b (opp b))) (opp c))
                       (plus (plus a zero) (opp c))
                       (plus a (opp c))).
      * apply (req_plus_compat (plus a (plus b (opp b)))
                               (plus a zero) (opp c) (opp c)
                               (req_plus_compat a a (plus b (opp b)) zero
                                                (req_refl a) (plus_opp b))
                               (req_refl (opp c))).
      * apply (req_plus_compat (plus a zero) a (opp c) (opp c)
                               (plus_zero a) (req_refl (opp c))).
Qed.

(* 内机7（件16 提级伴件，同上改道）：J(π_ref) == V(π_ref)
   （KL 对角自零 + 零右消去；件3 Hr 同位重建，纯 req 链） *)
Lemma rppo_J_ref_eq_value :
  req (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
      (state_value_req pi_ref).
Proof.
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                   (req_minus (state_value_req pi_ref)
                              (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                   (state_value_req pi_ref)).
  - exact (rppo_align_objective_decomp pi_ref pi_ref_pos).
  - apply (req_trans (req_minus (state_value_req pi_ref)
                                (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                     (req_minus (state_value_req pi_ref) zero)
                     (state_value_req pi_ref)).
    + apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                             (opp (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                             (opp zero)
                             (req_refl (state_value_req pi_ref))).
      apply (req_opp_compat (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)) zero).
      apply (req_trans (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos))
                       (mult beta zero) zero).
      * apply (req_mult_compat beta beta
                               (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos) zero
                               (req_refl beta) (rppo_KL_self_zero pi_ref pi_ref_pos)).
      * apply mult_zero.
    + apply (req_trans (req_minus (state_value_req pi_ref) zero)
                       (plus (state_value_req pi_ref) (opp zero))
                       (state_value_req pi_ref)).
      * unfold req_minus. apply req_refl.
      * apply (req_trans (plus (state_value_req pi_ref) (opp zero))
                         (plus (state_value_req pi_ref) zero)
                         (state_value_req pi_ref)).
        -- apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                                  (opp zero) zero (req_refl (state_value_req pi_ref))).
           exact (rkl_opp_zero).
        -- apply plus_zero.
Qed.


Lemma rppo_align_objective_advantage_decomp :
  forall (pi : S -> Real) (Hnorm : req (sumf pi) one) (Hpos : pos_dist S pi),
    req (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi Hpos)
        (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
              (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                         (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))).
Proof.
  intros pi Hnorm Hpos.
  (* 总装配：J(π) → Vπ−βKL → Vr+((Vπ−Vr)−βKL)[内机6 反向] → J(ref)+(ΣπA_ref−βKL) *)
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi Hpos)
                   (req_minus (state_value_req pi)
                              (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                   (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                         (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                    (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))).
  - exact (rppo_align_objective_decomp pi Hpos).
  - apply (req_trans (req_minus (state_value_req pi)
                                (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                     (plus (state_value_req pi_ref)
                           (req_minus (req_minus (state_value_req pi) (state_value_req pi_ref))
                                      (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))
                     (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                           (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                      (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))).
    + exact (req_sym _ _ (rppo_b_collapse_minus (state_value_req pi) (state_value_req pi_ref)
                           (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))).
    + apply (req_plus_compat (state_value_req pi_ref)
                             (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                             (req_minus (req_minus (state_value_req pi) (state_value_req pi_ref))
                                        (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                             (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                        (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                             (req_sym _ _ rppo_J_ref_eq_value)
                             (req_plus_compat (req_minus (state_value_req pi) (state_value_req pi_ref))
                                              (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                              (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                                              (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                                              (req_sym _ _ (rppo_advantage_sum_ref pi Hnorm))
                                              (req_refl (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))))).
Qed.
End ReqPPOAdvantage.
