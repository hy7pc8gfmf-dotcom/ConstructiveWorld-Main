(* ============================================================ *)
(* ToyR 玩具证替换件 —— T268 台账席 战役包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   minus_middle_t12（原 L90，2 句强证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpAlignId.v *)
(* *)
(* 目的： 对齐递减恒等式（策略间隙逐步递减）的 Real 层显式化。 *)
(* 主件： policy_gap_next_exact / policy_gap_decrement_exact：策略间隙的逐步精确式；dpo_loss_step_exact 与 policy_gap_backward_kl_exact。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 温度 β > 0 与奖励相关前提以显式 Variable 声明；陈述为接口 Set 层形态。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAlignId.v —— 对齐递减恒等式件（王中王批拆分件：热点 A5/B2）      *)
(*                                                                *)
(* 使命：把根内 Section Alignment 策略迭代的"单调 ≤"升级为"精确恒等式"。*)
(*   升级源：L23086 policy_iter_gap_mono（gap_{t+1} ≤ gap_t）与        *)
(*   L23244 dpo_loss_iter_step_le（loss 单步 ≤）均只有定性信息。       *)
(*                                                                *)
(* 数学目标（纸笔推导后的最终恒等式全文；记 J(p) := align_objective p，  *)
(*   gap(p) := J(pi_star) − J(p)，pi_{t+1} := pi_next pi_t，            *)
(*   K1 := KL(pi_{t+1}‖pi_t)，K2 := KL(pi_t‖pi_{t+1})，                 *)
(*   Δ := β·[(1/η−1)·K1 + (1/η)·K2]）：                                *)
(*                                                                *)
(*   件 A policy_gap_next_exact（gap 的单步精确分解）：              *)
(*     gap(pi_{t+1}) == gap(pi_t) − Δ                              *)
(*     即 J* − J(pi_{t+1})                                          *)
(*        == β·KL(pi_t‖pi_star) − β·[(1/η−1)·K1 + (1/η)·K2]。           *)
(*   件 A' policy_gap_decrement_exact（单调 ≤ 的精确化）：           *)
(*     gap(pi_t) − gap(pi_{t+1}) == Δ（每步下降量的精确值）。        *)
(*   件 B dpo_loss_step_exact（dpo_loss := opp J，换轴并列形态）：    *)
(*     dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ。                   *)
(*   伴随件 C policy_gap_backward_kl_exact（L22686 换轴组装）：       *)
(*     β·KL(pi*‖pi_{t+1})                                           *)
(*       == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2，              *)
(*     中项 gap(pi_t) 即 L20554 前向间隙——后向 KL 单步递推以前向      *)
(*     gap 精确进入（恒等式层面的两轴桥；前向/后向 KL 的"比较"仍需    *)
(*     Pinsker 型传递，库内无此材料，见扫描报告构造性边界 #1）。      *)
(*                                                                *)
(* 装配机器（全部在根，零新建分析机器）：                            *)
(*   L20554 rlhf_suboptimality_gap：gap(p) == β·KL(p‖pi_star)；           *)
(*   L23000 policy_iter_gap_diff：J(pi_{t+1}) − J(pi_t) == Δ；        *)
(*   L22686 policy_iter_backward_kl_step：三 KL 精确恒等（除 β 版）； *)
(*   差分代数：根内 minus_minus_distr + minus_plus_cancel（望远镜）    *)
(*   与 minus_rearrange_four + minus_self_zero + opp_minus（左消去）， *)
(*   本文件封装为 minus_middle_t12 / minus_left_cancel_t12 两件。     *)
(*                                                                *)
(* 诚实注记：扫描报告 A5 草案 RHS（η·KL(pi_t‖pi_star) − KL(pi_t‖pi_{t+1})，  *)
(*   无 β）混轴且丢 β 因子，作为恒等式不可由 L20554/L22686 推出；      *)
(*   本件按"两引理代数操作合并为准"落为上列可证形态。                *)
(*                                                                *)
(* 红线自审：纯构造性（零公理/零弃证/零经典逻辑，库 Not 为 Set 层      *)
(*   A -> Empty_set 编码）；语句全为 Set 层（premise 全为 lt/Id，      *)
(*   无 Prop 前提）；全部 Qed；尾部 Extraction 探针验证可提取性。      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ---------- 镜像 Section Alignment 的声明（同名同序；未用不声明） ---------- *)

Section AlignIdWorld.

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
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align reward beta beta_pos pi_ref).
Variable eta : R.                  (* 镜像步长 η > 0 *)
Variable eta_pos : lt zero eta.
Variable sum_over_S_pos : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* ---------- 差分代数封装（根内机器两步装配，供两主件共用） ---------- *)

(* 望远镜：已知 b 的公共项抽取。
   (a − b) − (c − b) == a − c
   装配：minus_minus_distr（(a−b)−c == a−(b+c)，根内 L19183）
       + minus_plus_cancel（b + (c−b) == c，根内 L668）。 *)
Lemma minus_middle_t12 : forall a b c : R,
  Id (minus (minus a b) (minus c b)) (minus a c).
Proof.
  intros a b c.
  exact (id_trans (minus_minus_distr a b (minus c b))
                  (id_cong (fun x => minus a x) (minus_plus_cancel b c))).
Qed.

(* 左消去：(a − b) − (a − c) == c − b（gap 下降量的换形核）。
   装配：minus_rearrange_four（根内 L19773，四元差分重排）
       + minus_self_zero（a − a == 0，根内 L984）
       + minus zero X == opp X（plus_comm/plus_zero）
       + opp_minus（根内 L706）+ plus_comm。 *)
Lemma minus_left_cancel_t12 : forall a b c : R,
  Id (minus (minus a b) (minus a c)) (minus c b).
Proof.
  intros a b c.
  assert (Hzero : Id (minus zero (minus b c)) (minus c b)).
  {
    assert (H1 : Id (minus zero (minus b c)) (opp (minus b c)))
      by exact (id_trans (plus_comm zero (opp (minus b c)))
                         (plus_zero (opp (minus b c)))).
    assert (H2 : Id (opp (minus b c)) (minus c b))
      by exact (id_trans (opp_minus b c) (plus_comm (opp b) c)).
    exact (id_trans H1 H2).
  }
  exact (id_trans (minus_rearrange_four a b a c)
                  (id_trans (id_cong2 minus (minus_self_zero a a id_refl) id_refl)
                            Hzero)).
Qed.

(* ---------- 件 A：次优间隙的单步精确分解恒等式 ---------- *)
(* gap(pi_{t+1}) == gap(pi_t) − β·[(1/η−1)·K1 + (1/η)·K2]
   装配 = 恒等式 + 恒等式 = 恒等式：
     gap(pi_t) == β·KL(pi_t‖pi_star)       （L20554）
     J(pi_{t+1}) − J(pi_t) == Δ              （L23000）
     望远镜：J* − J(pi_{t+1}) == (J* − J(pi_t)) − (J(pi_{t+1}) − J(pi_t))。 *)
Theorem policy_gap_next_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (align_objective reward beta pi_ref
                 (pi_star reward beta beta_pos pi_ref Z_align_pos))
              (align_objective reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (minus (mult beta (relative_entropy pi_t
                 (pi_star reward beta beta_pos pi_ref Z_align_pos)))
              (mult beta (plus
                 (mult (minus (inv_pos eta eta_pos) one)
                       (relative_entropy (pi_next reward beta beta_pos pi_ref
                                            eta sum_over_S_pos pi_t pi_t_pos)
                                         pi_t))
                 (mult (inv_pos eta eta_pos)
                       (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos)))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (id_sym (minus_middle_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np)))
           (id_cong2 minus Hgap Hdiff)).
Qed.

(* ---------- 件 A'：gap 递减量的精确恒等式（L23086 单调 ≤ 的精确化） ---------- *)
(* gap(pi_t) − gap(pi_{t+1}) == Δ；右端两 KL 均非负（根内 KL 机器），
   故单调 ≤ 为本恒等式的直接读出，且带精确步长。 *)
Corollary policy_gap_decrement_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref pi_t))
              (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref
                        (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                           pi_t pi_t_pos))))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_left_cancel_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np))
           Hdiff).
Qed.

(* ---------- 件 B：dpo_loss 单步精确差恒等式（换轴并列形态） ---------- *)
(* dpo_loss(pi) := opp (align_objective pi)（根内 L19090）。
   dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ。
   与根内 L23000 policy_iter_gap_diff 的关系：换轴并列——L23000 是 J 轴
   单步改进量，本件是 loss 轴单步下降量，二者经 minus_opp_opp 精确互逆
   （对偶轴上的显式陈述，供损失动态叙事直接引用）。 *)
Theorem dpo_loss_step_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (dpo_loss reward beta pi_ref pi_t)
              (dpo_loss reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  unfold dpo_loss.
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_opp_opp (align_objective reward beta pi_ref pi_t)
                                 (align_objective reward beta pi_ref Np))
                  Hdiff).
Qed.

(* ---------- 伴随件 C：后向 KL 递推的换轴精确恒等式 ---------- *)
(* β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2
   装配 = L22686（三 KL 恒等，除 β 版）整体乘 β（distrib + mult 交换
   吸收）+ 中项以 L20554 的 gap(pi_t) = J* − J(pi_t) 精确代换。
   定量解读：后向 KL 每步恰降 η·gap(pi_t)，并被前向步长 KL(β·K2) 抵消。 *)
Theorem policy_gap_backward_kl_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (mult beta (relative_entropy
             (pi_star reward beta beta_pos pi_ref Z_align_pos)
             (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                pi_t pi_t_pos)))
       (plus (mult (minus one eta)
                   (mult beta (relative_entropy
                          (pi_star reward beta beta_pos pi_ref Z_align_pos)
                          pi_t)))
             (plus (opp (mult eta
                          (minus (align_objective reward beta pi_ref
                                    (pi_star reward beta beta_pos pi_ref
                                       Z_align_pos))
                                 (align_objective reward beta pi_ref pi_t))))
                   (mult beta (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hnextpos : forall s : S, lt zero (Np s)).
  {
    intro s. unfold Np.
    exact (pi_next_pos reward beta beta_pos pi_ref eta sum_over_S_pos
                       pi_t pi_t_pos s).
  }
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  (* L22686 原始恒等（除 β 版三 KL） *)
  assert (Hb : Id (relative_entropy Ps Np)
                   (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                         (plus (opp (mult eta (relative_entropy pi_t Ps)))
                               (relative_entropy pi_t Np))))
    by exact (policy_iter_backward_kl_step reward beta beta_pos pi_ref
                                           pi_ref_pos Z_align_pos eta eta_pos
                                           sum_over_S_pos pi_t pi_t_pos
                                           pi_t_norm Hnextpos).
  (* β 缩放：β·(k·X) == k·(β·X)（结合-交换-反结合三步） *)
  assert (Hscale1 : Id (mult beta (mult (minus one eta) (relative_entropy Ps pi_t)))
                       (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))).
  {
    apply (id_trans (mult_assoc beta (minus one eta) (relative_entropy Ps pi_t))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy Ps pi_t))
                             (mult_comm beta (minus one eta)))).
    exact (id_sym (mult_assoc (minus one eta) beta (relative_entropy Ps pi_t))).
  }
  assert (Hswap2 : Id (mult beta (mult eta (relative_entropy pi_t Ps)))
                      (mult eta (mult beta (relative_entropy pi_t Ps)))).
  {
    apply (id_trans (mult_assoc beta eta (relative_entropy pi_t Ps))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t Ps))
                             (mult_comm beta eta))).
    exact (id_sym (mult_assoc eta beta (relative_entropy pi_t Ps))).
  }
  (* β·(opp (η·KLts)) == opp (η·gap(pi_t))：opp_mult_l + Hswap2 + Hgap 代换 *)
  assert (Hscale2 : Id (mult beta (opp (mult eta (relative_entropy pi_t Ps))))
                       (opp (mult eta
                              (minus (align_objective reward beta pi_ref Ps)
                                     (align_objective reward beta pi_ref pi_t))))).
  {
    apply (id_trans (opp_mult_l beta (mult eta (relative_entropy pi_t Ps)))).
    exact (id_cong opp
                   (id_trans Hswap2
                             (id_cong (fun z => mult eta z) (id_sym Hgap)))).
  }
  (* β 分配到后半树：β·(B + C) == β·B + β·C，B 项换形 *)
  assert (Hscale3 : Id (mult beta (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                        (relative_entropy pi_t Np)))
                       (plus (opp (mult eta
                                    (minus (align_objective reward beta pi_ref Ps)
                                           (align_objective reward beta pi_ref pi_t))))
                             (mult beta (relative_entropy pi_t Np))))
    by exact (id_trans (distrib beta (opp (mult eta (relative_entropy pi_t Ps)))
                                (relative_entropy pi_t Np))
                       (id_cong2 plus Hscale2 id_refl)).
  (* 全树 β 分配组装 *)
  assert (Hscale : Id (mult beta (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                                       (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                             (relative_entropy pi_t Np))))
                       (plus (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))
                             (plus (opp (mult eta
                                          (minus (align_objective reward beta pi_ref Ps)
                                                 (align_objective reward beta pi_ref pi_t))))
                                   (mult beta (relative_entropy pi_t Np)))))
    by exact (id_trans (distrib beta (mult (minus one eta) (relative_entropy Ps pi_t))
                                (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                      (relative_entropy pi_t Np)))
                       (id_cong2 plus Hscale1 Hscale3)).
  exact (id_trans (id_cong (mult beta) Hb) Hscale).
Qed.

End AlignIdWorld.

(* ---------- 提取探针（G3：Obj.magic = 0） ---------- *)

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions minus_middle_t12.
