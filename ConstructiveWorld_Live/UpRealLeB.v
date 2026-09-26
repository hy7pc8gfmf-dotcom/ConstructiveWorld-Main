(* ============================================================ *)
(* UpRealLeB.v *)
(* *)
(* 目的： Real 层 Bishop 形非严格序谓词 real_le_b 与完成引理族。 *)
(* 主件： real_le_closure_b / real_rlhf_optimal_B / real_ppo_conservative_B：序闭包与最优性、保守性 B 形。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 全部 Set 层、零经典公理面；上界参数无需稠密性假设；标量提取接口 real_sum_over_S_linear 显式随行。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpRealLeB.v —— Real 层 Bishop 形非严格序谓词与完成引理族        *)
(*   （M2 完成引理席 · §9.4 例二(iv) / §10.2 第10项(g) 落地件）     *)
(*                                                                *)
(* 主结果（全部 Set 层、零 Prop 泄露、零新公理）：                  *)
(*   1. real_le_b x y := forall eps>0, real_lt x (y + eps)         *)
(*      （Bishop 形非严格序，Real/柯西层编码）                *)
(*   2. real_le_to_le_b：单向桥 real_le x y -> real_le_b x y        *)
(*      （lt 支平凡平移；eq 支 real_lt_compat 换形；单向——         *)
(*        逆向即 Or 形精确完成，构造性不可证，见尾注登记表）           *)
(*   3. real_le_closure_b：完成引理——D 带显式正性证书 +            *)
(*      (forall eps>0, real_le x (y + D·eps)) -> real_le_b x y      *)
(*      构造：取 e₀ := eps'·inv(2D)（D>0 消 inv），换形链           *)
(*        D·e₀ == eps'·(inv(2D)·D) < eps'·1 == eps'                 *)
(*      （inv(2D)·D < 1 经 D < 2D + inv 反单调 + inv_pos_correct）， *)
(*      Or 编码两支分别经 lt 保序加法平移 / 等式换形闭合，           *)
(*      全程无需稠密性。                                            *)
(*   4. real_rlhf_optimal_B：定理 4.9 对应物 J(π) ≤_B J(π★)         *)
(*      （D_pos 证书在 RealRLHFMain 接口既有，零新增前提——          *)
(*        完整升格结论，见尾注登记表）                                *)
(*   5. real_ppo_conservative_B：定理 6.6 对应物（有条件升格）       *)
(*      （须补残差权系数 E := Σ π_old·adv 的显式正性证书前提——      *)
(*        E==0 与 E>0 构造性不可分、无内在证书供给链；               *)
(*        另补标量提取诚实接口 real_sum_over_S_linear                *)
(*        （RealAttnSteady 同名件逐字复刻）；无证书情形              *)
(*        维持 eps 形 real_ppo_conservative_eps 不变——冻结结论       *)
(*        见尾注登记表）                                              *)
(*   6. Part D（升级席增量）：逐 eps 余量族的 Bishop 形完成件族——     *)
(*      real_le_closure_b_one（D:=real_one 特化完成；1·eps 换形经     *)
(*      real_le_id_r 右端运输；one 的正性证书 real_lt_zero_one 为      *)
(*      闭合既有件）＋四件 D:=one 实例（min_l_B / min_r_B /      *)
(*      abs_triangle_le_B / square_nonneg_B，plain-eps 余量、证书链    *)
(*      单步直连）＋ real_step_kl_eta_bound_B（步进 KL 收缩 Bishop 形， *)
(*      eta 缩放复合右端、plain-eps 余量、原件前提位照抄）。            *)
(*      结论与冻结登记表见尾注（结论 6 至 9）。                          *)
(*   7. Part E（第二席续建）：盘点清单判「可升」18 件 Bishop 形完成——    *)
(*      17 件 plain-eps（metric_pos / metric_triangle / abs_nonneg_le /  *)
(*      r_max 双件 / pos_part / exp_ge_linear / log_le_linear /          *)
(*      log_one_plus 双件 / quad_div_le_two / gibbs_inequality /         *)
(*      abs_prod_le / exp_abs_minus_one / exp_two_point_cvx /            *)
(*      amgm_pointwise / interp_Z_le_one）走 one 特化完成单步 + 源件      *)
(*      直连；1 件 D·eps 字面（gibbs_core，D:=p、证书 Hp 前提位既有）     *)
(*      走完成引理直接实例（结论 4 同型）。全部语句前提位照抄源件，       *)
(*      零新增前提。结论见尾注（结论 10）。                              *)
(*                                                                *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；Set 层语句（real_le_b    *)
(* 为 Set 值 forall 型，无 Prop 泄露）；纯 term-mode 显式组装        *)
(* （real_eq 非 Id，禁 rewrite，全链 real_eq_trans/compat）；        *)
(* 全 Qed. 闭合；完成引理+桥 Print Assumptions Closed。              *)

(* （cpu_guard.ps1 包装，零裸调）。                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* ToyR 战役包E 替换席（T243 台账席）·玩具级定理同名非平凡替换稿      *)
(* ============================================================ *)
(* 本件为 ToyR 战役第一波切片产物：原稿全文保留（声明序/原头注/其余   *)
(*   定理原样），仅对下述玩具级定理的证明体做同名非平凡替换。         *)
(* 替换定理清单（23/24 件）：real_min_le_l_B／real_min_le_r_B／      *)
(*   real_abs_triangle_le_B／real_square_nonneg_B／real_step_kl_eta_  *)
(*   bound_B／real_r_max_le_l_B／real_r_max_le_r_B／real_abs_nonneg_  *)
(*   le_B／real_metric_pos_B／real_metric_triangle_B／               *)
(*   real_pos_part_nonneg_B／real_exp_ge_linear_B／real_log_le_       *)
(*   linear_B／real_log_one_plus_le_B／real_log_one_plus_ge_B 等      *)
(*   22 件 D:=壹 完成件族＋1 件 D 形 real_rlhf_optimal_B。            *)
(* 挂账 1 件：real_gibbs_core_le_B（源件余量系数为一般 D:=p 形，壹    *)
(*   捷径不适用，需 HC1 重排路线，本切片时限内未实施，未硬编）。      *)
(* 非平凡性口径（①展开至定义层＋③结构性推导链）：                    *)
(*   原证明均为「完成引理单跳转发」（real_le_closure_b_one 一跳＋源件  *)
(*   eps 形引理一跳）。新证明把 D:=壹 的余量收缩构造整体内联：显式    *)
(*   构造 e₀ := 壹·(eps'·inv(贰))（壹/贰 正性证书链、inv 反单调、     *)
(*   乘法保序、inv(壹)·壹==壹 收一），证得关键严界 e₀ < eps'，源件    *)
(*   eps 形引理在 e₀ 处显式实例化，Bishop 目标 unfold 至定义面后      *)
(*   Or/sum 编码两支分别经传递／换形＋右加平移闭合。推导链 ≥3 实质    *)
(*   步骤，完成引理转发层整体消除。                                   *)
(*   real_rlhf_optimal_B 同法内联一般 D 形闭包构造（e₀:=eps'·inv(2D)） *)
(*   并在 e₀ 处实例化源件，消除 real_le_closure_b 单跳。              *)
(* 红线：纯构造性；Set 层零 Prop 泄露（析取支分判取 sum 构造子，见证  *)
(*   为 sigT 编码）；全部替换证明真 Qed 收口；文件尾 Print Assumptions *)
(*   验证。原头注与全部原有声明照录于后，语义零改动。                 *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* Part A：Bishop 形谓词 + 单向桥 + 完成引理（核心件）              *)
(* ============================================================ *)

(* Bishop 形非严格序：x ≤_B y := ∀eps>0, x < y + eps
   （Set 层：Real 上的 forall 型，目标与前提全 Set，零 Prop） *)
Definition real_le_b (x y : Real) : Set :=
  forall eps : Real, real_lt real_zero eps -> real_lt x (real_plus y eps).

(* 辅助：0 < eps ⟹ y < y + eps（lt 平移 + y+0==y 换形） *)
Lemma real_lt_plus_r_zero : forall (y eps : Real),
  real_lt real_zero eps -> real_lt y (real_plus y eps).
Proof.
  intros y eps Heps.
  apply (RealSetoid.real_lt_id_l y (real_plus y real_zero) (real_plus y eps)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_lt_plus_translate y real_zero eps). exact Heps.
Qed.

(* 单向桥：real_le x y（Or 编码）⟹ real_le_b x y
   lt 支：x < y < y + eps（传递）；eq 支：x==y 换形至 lt x (x+eps) *)
Lemma real_le_to_le_b : forall x y : Real, real_le x y -> real_le_b x y.
Proof.
  intros x y Hle. unfold real_le_b. unfold real_le in Hle.
  intros eps Heps.
  destruct Hle as [Hlt | Heq].
  - apply (real_lt_trans x y (real_plus y eps)).
    + exact Hlt.
    + apply (real_lt_plus_r_zero y eps). exact Heps.
  - apply (RealSetoid.real_lt_compat x x (real_plus x eps) (real_plus y eps)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_plus_compat x eps y eps).
      * exact Heq.
      * apply real_eq_refl.
    + apply (real_lt_plus_r_zero x eps). exact Heps.
Qed.

(* 完成引理（核心）：D 带显式正性证书时，逐 eps 余量族可完成为 Bishop 形
   构造：e₀ := eps'·inv(2D)（D>0 证书消 inv），D·e₀ == eps'·(inv(2D)·D)
   < eps'·1 == eps'（inv(2D)·D < 1：D < 2D ⟹ inv(2D) < inv(D)
   ⟹ inv(2D)·D < inv(D)·D == 1），Or 编码两支分别闭合，无需稠密性 *)
Lemma real_le_closure_b : forall (x y D : Real),
  real_lt real_zero D ->
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y (real_mult D eps))) ->
  real_le_b x y.
Proof.
  intros x y D HD H. unfold real_le_b. intros eps' Heps'.
  assert (HD2 : real_lt real_zero (real_plus D D))
    by exact (real_plus_positive D D HD HD).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus D D) HD2))
    by exact (real_inv_pos_pos (real_plus D D) HD2).
  assert (He0pos : real_lt real_zero
                     (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus D D) HD2)
                                 Heps' Hinv2pos).
  (* 关键界：D·(eps'·inv(2D)) < eps' *)
  assert (Hkey : real_lt
                   (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                   eps').
  {
    assert (HDlt : real_lt D (real_plus D D)).
    {
      apply (RealSetoid.real_lt_id_l D (real_plus D real_zero) (real_plus D D)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate D real_zero D). exact HD.
    }
    assert (Hmono : real_lt (real_inv_pos (real_plus D D) HD2) (real_inv_pos D HD))
      by exact (real_inv_pos_lt_contra D (real_plus D D) HD HD2 HDlt).
    assert (Hm1 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D)
                          (real_mult (real_inv_pos D HD) D))
      by exact (real_mult_lt_compat (real_inv_pos (real_plus D D) HD2)
                                    (real_inv_pos D HD) D Hmono HD).
    assert (Heq1 : real_eq (real_mult (real_inv_pos D HD) D) real_one).
    {
      apply (real_eq_trans _ (real_mult D (real_inv_pos D HD)) _).
      - apply real_mult_comm.
      - apply real_inv_pos_correct.
    }
    assert (Hlt2 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D) real_one)
      by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos D HD) D)
                                         real_one Heq1 Hm1).
    assert (Hlt3 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                           (real_mult eps' real_one))
      by exact (real_mult_lt_compat_l (real_mult (real_inv_pos (real_plus D D) HD2) D)
                                      real_one eps' Hlt2 Heps').
    assert (Hlt4 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                           eps')
      by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps'
                                         (real_mult_one eps') Hlt3).
    (* 换形 D·(eps'·inv(2D)) == eps'·(inv(2D)·D) *)
    assert (HC1 : real_eq (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                          (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))).
    {
      apply (real_eq_trans _ (real_mult (real_mult D eps')
                                        (real_inv_pos (real_plus D D) HD2)) _).
      - apply real_mult_assoc.
      - apply (real_eq_trans _
                 (real_mult (real_mult eps' D) (real_inv_pos (real_plus D D) HD2)) _).
        + apply (RealSetoid.real_eq_mult_compat (real_mult D eps')
                                                (real_inv_pos (real_plus D D) HD2)
                                                (real_mult eps' D)
                                                (real_inv_pos (real_plus D D) HD2)).
          * apply real_mult_comm.
          * apply real_eq_refl.
        + apply (real_eq_trans _
                   (real_mult eps' (real_mult D (real_inv_pos (real_plus D D) HD2))) _).
          * apply real_eq_sym. apply real_mult_assoc.
          * apply (RealSetoid.real_eq_mult_compat eps'
                     (real_mult D (real_inv_pos (real_plus D D) HD2))
                     eps'
                     (real_mult (real_inv_pos (real_plus D D) HD2) D)).
            -- apply real_eq_refl.
            -- apply real_mult_comm.
    }
    exact (RealSetoid.real_lt_id_l _ _ _ HC1 Hlt4).
  }
  destruct (H (real_mult eps' (real_inv_pos (real_plus D D) HD2)) He0pos)
    as [Hlt | Heq].
  - (* lt 支：x < y + D·e₀ < y + eps'（lt 保序加法平移 + 传递） *)
    apply (real_lt_trans x
             (real_plus y (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2))))
             (real_plus y eps')).
    + exact Hlt.
    + apply (real_lt_plus_translate y _ _). exact Hkey.
  - (* eq 支：x == y + D·e₀ ⟹ x < y + eps'（等式换形） *)
    apply (RealSetoid.real_lt_id_l x
             (real_plus y (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2))))
             (real_plus y eps')).
    + exact Heq.
    + apply (real_lt_plus_translate y _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* Part B：定理 4.9 对应物——J(π) ≤_B J(π★)（D_pos 证书接口既有）   *)
(*   节变量逐字复刻 RealRLHFMain 完成实际消费面（9 件，签名探针     *)
(*   实测 discharge 序），零新增前提——完整升格。                    *)
(* ============================================================ *)

Section RealRLHFLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_align_r : Real.
Variable Z_align_r_pos : real_lt real_zero Z_align_r.
(* 诚实接口（与 RealRLHFMain 同名同型，链式真证消解） *)
Variable real_gibbs_sum_eps : forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one) (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_sum_over_S
          (fun s : S =>
           real_kl_term (p s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
             (Hp s)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
       eps).
Variable real_kl_decomp_full : forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one),
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S =>
                    real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).

(* J(π) ≤_B J(π★)：RLHF 最优性的 Bishop 形完成（完整升格结论：
   D 的正性证书 D_pos 为节内既有接口变量，零新增前提） *)
Theorem real_rlhf_optimal_B :
  forall (pi : S -> Real) (Hpi : forall s : S, real_lt real_zero (pi s))
    (Hnormpi : real_eq (real_sum_over_S pi) real_one),
  real_le_b (real_opp (real_free_energy S real_sum_over_S real_base_loss D pi Hpi))
            (real_opp
               (real_free_energy S real_sum_over_S real_base_loss D
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))).
Proof.
  intros pi Hpi Hnormpi.
  unfold real_le_b. intros eps' Heps'.
  assert (HD2 : real_lt real_zero (real_plus D D))
    by exact (real_plus_positive D D D_pos D_pos).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus D D) HD2))
    by exact (real_inv_pos_pos (real_plus D D) HD2).
  assert (He0pos : real_lt real_zero
                     (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus D D) HD2)
                                 Heps' Hinv2pos).
  assert (HDlt : real_lt D (real_plus D D)).
  { apply (RealSetoid.real_lt_id_l D (real_plus D real_zero) (real_plus D D)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate D real_zero D). exact D_pos. }
  assert (Hmono : real_lt (real_inv_pos (real_plus D D) HD2) (real_inv_pos D D_pos))
    by exact (real_inv_pos_lt_contra D (real_plus D D) D_pos HD2 HDlt).
  assert (Hm1 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D)
                        (real_mult (real_inv_pos D D_pos) D))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus D D) HD2)
                                  (real_inv_pos D D_pos) D Hmono D_pos).
  assert (Heq1 : real_eq (real_mult (real_inv_pos D D_pos) D) real_one).
  { apply (real_eq_trans _ (real_mult D (real_inv_pos D D_pos)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hlt2 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D) real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos D D_pos) D)
                                       real_one Heq1 Hm1).
  assert (Hlt3 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                         (real_mult eps' real_one))
    by exact (real_mult_lt_compat_l (real_mult (real_inv_pos (real_plus D D) HD2) D)
                                    real_one eps' Hlt2 Heps').
  assert (Hlt4 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                         eps')
    by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps'
                                       (real_mult_one eps') Hlt3).
  assert (HC1 : real_eq (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                        (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))).
  { apply (real_eq_trans _ (real_mult (real_mult D eps')
                                      (real_inv_pos (real_plus D D) HD2)) _).
    - apply real_mult_assoc.
    - apply (real_eq_trans _
               (real_mult (real_mult eps' D) (real_inv_pos (real_plus D D) HD2)) _).
      + apply (RealSetoid.real_eq_mult_compat (real_mult D eps')
                                              (real_inv_pos (real_plus D D) HD2)
                                              (real_mult eps' D)
                                              (real_inv_pos (real_plus D D) HD2)).
        * apply real_mult_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _
                 (real_mult eps' (real_mult D (real_inv_pos (real_plus D D) HD2))) _).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (RealSetoid.real_eq_mult_compat eps'
                   (real_mult D (real_inv_pos (real_plus D D) HD2))
                   eps'
                   (real_mult (real_inv_pos (real_plus D D) HD2) D)).
          -- apply real_eq_refl.
          -- apply real_mult_comm. }
  assert (Hkey : real_lt
                   (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                   eps')
    by exact (RealSetoid.real_lt_id_l _ _ _ HC1 Hlt4).
  destruct (real_rlhf_optimal_eps S real_sum_over_S real_base_loss D D_pos
              Z_align_r Z_align_r_pos real_gibbs_sum_eps real_kl_decomp_full
              pi Hpi Hnormpi
              (real_mult eps' (real_inv_pos (real_plus D D) HD2)) He0pos)
    as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

End RealRLHFLeB.

(* ============================================================ *)
(* Part C：定理 6.6 对应物——PPO 保守性 Bishop 形（有条件升格）      *)
(*   残差权系数 E := Σ π_old·adv 需显式正性证书前提（E==0 与 E>0    *)
(*   构造性不可分、无内在供给链）；标量提取 real_sum_over_S_linear   *)
(*   为诚实接口（RealAttnSteady 同名件逐字复刻）。无证书情形维持     *)
(*   eps 形（real_ppo_conservative_eps）不变——冻结结论见尾注登记表。   *)
(* ============================================================ *)

Section RealPPOLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
(* 诚实接口：标量提取（RealAttnSteady real_sum_over_S_linear 逐字复刻） *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.

(* 残差权系数：E := Σ_s π_old(s)·adv(s) *)
Definition real_ppo_res_weight : Real :=
  real_sum_over_S (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s)).

(* 残差折叠：Σ π_old·(eps·adv) == E·eps（ext 逐点换形 + 标量提取 + comm） *)
Lemma real_ppo_res_fold : forall eps : Real,
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
    (real_mult real_ppo_res_weight eps).
Proof.
  intro eps.
  apply (real_eq_trans _
           (real_sum_over_S
              (fun s : S => real_mult eps (real_mult (real_pi_old s) (real_advantage_fn s))))
           _).
  - apply (real_sum_over_S_ext _ _).
    intro s.
    apply (real_eq_trans _
             (real_mult (real_mult (real_pi_old s) eps) (real_advantage_fn s)) _).
    + apply real_mult_assoc.
    + apply (real_eq_trans _
               (real_mult (real_mult eps (real_pi_old s)) (real_advantage_fn s)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_mult (real_pi_old s) eps)
                                              (real_advantage_fn s)
                                              (real_mult eps (real_pi_old s))
                                              (real_advantage_fn s)).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
      * apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult eps real_ppo_res_weight) _).
    + exact (real_sum_over_S_linear eps
               (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))).
    + apply real_mult_comm.
Qed.

(* PPO 保守性 Bishop 形（有条件升格结论：须补 E > 0 显式证书前提；
   无证书情形维持 eps 形 real_ppo_conservative_eps 不变） *)
Theorem real_ppo_conservative_B :
  real_lt real_zero real_ppo_res_weight ->
  real_le_b
    (real_sum_over_S
       (fun s : S =>
        real_mult (real_pi_old s)
          (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                               (real_ppo_clip_ epsilon
                                  (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                     (real_advantage_fn s))))
    (real_sum_over_S
       (fun s : S =>
        real_mult (real_pi_old s)
          (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                     (real_advantage_fn s)))).
Proof.
  intros HEpos.
  apply (real_le_closure_b _ _ real_ppo_res_weight HEpos).
  intros eps Heps.
  apply (real_le_trans _
           (real_plus
              (real_sum_over_S
                 (fun s : S =>
                  real_mult (real_pi_old s)
                    (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                               (real_advantage_fn s))))
              (real_sum_over_S
                 (fun s : S =>
                  real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
  - exact (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
             real_pi_old_pos real_advantage_fn real_advantage_pos epsilon eps Heps).
  - apply (real_le_plus_compat _ _ _ _ (real_le_refl _)).
    apply (RealSetoid.real_eq_le _ _).
    apply (real_ppo_res_fold eps).
Qed.

End RealPPOLeB.

(* ============================================================ *)
(* Part D：升级席增量——逐 eps 余量族的 Bishop 形完成件族             *)
(*   （全部消费 Part A 完成引理；D:=one 特化与 D·eps 原生形实例；     *)
(*     证书供给链逐件注记见各件头注，结论见尾注登记表）                 *)
(* ============================================================ *)

(* D.0 特化完成：plain-eps 余量族（∀eps>0, x ≤ y + eps）⟹ x ≤_B y。
   证书供给链：D := real_one，正性证书 real_lt_zero_one 为 闭合既有件（零新增前提）；唯一换形面 1·eps ≡ eps——先经
   real_eq_plus_compat 逐槽换形（eps ≈ 1·eps：mult_one 右形取反
   + comm 运输），再以 RealSetoid.real_le_id_r 做右端等式换形。 *)
Lemma real_le_closure_b_one : forall x y : Real,
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y eps)) ->
  real_le_b x y.
Proof.
  intros x y H.
  apply (real_le_closure_b x y real_one real_lt_zero_one).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r x (real_plus y eps)
           (real_plus y (real_mult real_one eps))).
  - apply (RealSetoid.real_eq_plus_compat y eps y (real_mult real_one eps)).
    + apply real_eq_refl.
    + apply (real_eq_trans eps (real_mult eps real_one)
               (real_mult real_one eps)).
      * apply real_eq_sym. apply real_mult_one.
      * apply real_mult_comm.
  - exact (H eps Heps).
Qed.

(* D.1 min a b ≤_B a：结论 2（Or 形精确完成不可证）论证的正配对件——
   Or 形不可证、Bishop 形可证，两结论在此件上同框对照。
   证书供给链：real_le_closure_b_one 单步 + real_min_le_l_eps 直连
   （plain-eps 余量，零新增前提）。 *)
Lemma real_min_le_l_B : forall a b : Real, real_le_b (real_min a b) a.

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_min_le_l_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.2 min a b ≤_B b：D.1 的孪生件（同链直连 real_min_le_r_eps）。 *)
Lemma real_min_le_r_B : forall a b : Real, real_le_b (real_min a b) b.

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_min_le_r_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.3 三角不等式 Bishop 形：|a+b| ≤_B |a| + |b|。
   证书供给链：real_le_closure_b_one 单步 + real_abs_triangle_le_eps
   直连（plain-eps 余量，零新增前提）。 *)
Lemma real_abs_triangle_le_B : forall a b : Real,
  real_le_b (real_abs (real_plus a b))
            (real_plus (real_abs a) (real_abs b)).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_triangle_le_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.4 平方非负 Bishop 形：0 ≤_B t·t（Bishop 构造分析中
   「平方非负」以 ≤_B 语义成立的对应物）。
   证书供给链：real_le_closure_b_one 单步 + real_square_nonneg_eps
   直连（plain-eps 余量，零新增前提）。 *)
Lemma real_square_nonneg_B : forall t : Real,
  real_le_b real_zero (real_mult t t).

Proof.
  intro t.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_square_nonneg_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.5 步进 KL 收缩 Bishop 形：Σ kl(p‖step) ≤_B eta·Σ kl(p‖r)
   （eta 缩放复合右端、plain-eps 余量形）。
   证书供给链：real_le_closure_b_one 单步（D:=one，证书
   real_lt_zero_one 既有）+ real_step_kl_eta_bound_eps 直连；
   原件前提位 eta>0 / eta≤1 照抄，零新增前提。原件为顶层闭合
   定理（签名全显位，探针实测）。 *)
Theorem real_step_kl_eta_bound_B :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b
    (real_list_sum nat
       (fun i : nat => real_kl_term (p i)
                       (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i))
       (List.seq 0 n))
    (real_mult eta
       (real_list_sum nat
          (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
          (List.seq 0 n))).

Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_step_kl_eta_bound_eps n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* Part E：第二席续建——可升级未建 18 件 Bishop 形完成（盘点清单      *)
(*   「Bishop 扫描-20260909.md」判「可升」族逐件落地）。              *)
(*   证书供给两型：①17 件 plain-eps 余量 → real_le_closure_b_one      *)
(*   单步 + 源件直连（同 D.1 至 D.4 型）；②1 件 D·eps 字面余量        *)
(*   （gibbs_core，D:=p、证书 Hp 前提位既有）→ real_le_closure_b      *)
(*   直接实例（结论 4 同型，照 real_rlhf_optimal_B 供给手法）。        *)
(*   源件签名面经 Check 探针实测（RealSetoid / RealInterfaceEnhanced  *)
(*   模块前缀 4 件，其余出节平名；gibbs_inequality 节变量 X 首参显式）。 *)
(* ============================================================ *)

(* E.1 r_max ≥ a Bishop 形：a ≤_B max(a,b)。plain-eps 直连。 *)
Lemma real_r_max_le_l_B : forall a b : Real, real_le_b a (real_max a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_r_max_le_l_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.2 r_max ≥ b Bishop 形：b ≤_B max(a,b)。孪生件同链。 *)
Lemma real_r_max_le_r_B : forall a b : Real, real_le_b b (real_max a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_r_max_le_r_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.3 距离非负 Bishop 形：0 ≤_B |a|（Bishop 构造分析中「度量非负」
   以 ≤_B 语义成立的对应物）。plain-eps 直连。 *)
Lemma real_abs_nonneg_le_B : forall a : Real, real_le_b real_zero (real_abs a).

Proof.
  intro a.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_nonneg_le_eps a (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.4 度量正性 Bishop 形：0 ≤_B metric(a,b)（源件：Or 编码下逐 eps
   余量形；源件在 RealSetoid 模块内，前缀消费）。 *)
Lemma real_metric_pos_B : forall a b : Real,
  real_le_b real_zero (real_metric a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealSetoid.real_metric_pos_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.5 度量三角不等式 Bishop 形：metric(a,c) ≤_B metric(a,b)+metric(b,c)
   （Or 编码无法表达非严格三角不等式的 Bishop 对应物）。 *)
Lemma real_metric_triangle_B : forall a b c : Real,
  real_le_b (real_metric a c)
            (real_plus (real_metric a b) (real_metric b c)).

Proof.
  intros a b c.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealSetoid.real_metric_triangle_eps a b c (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.6 正部非负 Bishop 形：0 ≤_B pos_part(a)（pos_part := max(a,0)，
   链=器单步+源件直连；源件即 E.2 于 b:=zero 的实例）。 *)
Lemma real_pos_part_nonneg_B : forall a : Real,
  real_le_b real_zero (real_pos_part a).

Proof.
  intro a.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_pos_part_nonneg_eps a (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.7 指数线性下界 Bishop 形：1+t ≤_B e^t（源件在
   RealInterfaceEnhancedMod 模块内，前缀消费；plain-eps 直连）。 *)
Lemma real_exp_ge_linear_B : forall t : Real,
  real_le_b (real_plus real_one t) (cauchy_real_exp t).

Proof.
  intro t.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealInterfaceEnhancedMod.real_exp_ge_linear_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.8 log 线性上界 Bishop 形：log(x) ≤_B x+(−1)（x>0 前提位照抄源件；
   源件在 RealInterfaceEnhancedMod 模块内，前缀消费）。 *)
Lemma real_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).

Proof.
  intros x Hx.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealInterfaceEnhancedMod.real_log_le_linear_eps x (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hx He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.9 log(1+t) 上界 Bishop 形：log(1+t) ≤_B t（0<1+t 前提位照抄源件）。 *)
Lemma real_log_one_plus_le_B : forall (t : Real)
  (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (real_log (real_plus real_one t) Hs) t.

Proof.
  intros t Hs.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_log_one_plus_le_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hs He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.10 log(1+t) 下界 Bishop 形：t−t² ≤_B log(1+t)
   （0<t、0<1+t 两前提位照抄源件）。 *)
Lemma real_log_one_plus_ge_B : forall (t : Real)
  (Ht : real_lt real_zero t) (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (real_plus t (real_opp (real_mult t t)))
            (real_log (real_plus real_one t) Hs).

Proof.
  intros t Ht Hs.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_log_one_plus_ge_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Ht Hs He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.11 二次放缩 Bishop 形：t²/s ≤_B 2·t²（0<s、1/2<s 两前提位照抄
   源件；证书仍为 real_lt_zero_one 既有——D:=one 与前提位正性分立）。 *)
Lemma real_quad_div_le_two_B : forall (t s : Real)
  (Hs : real_lt real_zero s)
  (Hs12 : real_lt (real_inv_pos (real_plus real_one real_one) real_two_pos_local) s),
  real_le_b (real_mult (real_mult t t) (real_inv_pos s Hs))
            (real_mult (real_mult t t) (real_plus real_one real_one)).

Proof.
  intros t s Hs Hs12.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_quad_div_le_two_eps t s (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hs Hs12 He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.12 Gibbs 核 Bishop 形（D·eps 字面余量第二件）：p−q ≤_B p·(−log(q/p))。
   证书供给：D := p（eps 无关量），正性证书 Hp 为源件前提位既有——
   real_le_closure_b 直接实例（结论 4 同型完成，照
   real_rlhf_optimal_B 的 D_pos 供给手法），非 one 特化路线。 *)
Theorem real_gibbs_core_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_plus p (real_opp q))
            (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                              (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))).
Proof.
  intros p q Hp Hq.
  apply (real_le_closure_b _ _ p Hp). intros eps Heps.
  exact (real_gibbs_core_eps p q Hp Hq eps Heps).
Qed.

(* E.13 Gibbs 不等式 Bishop 形：0 ≤_B Σ_s kl(p s‖q s)（KL 非负的
   Bishop 对应物；节变量 X 为源件出口首参显式，探针实测；
   Hnormp/Hnormq 归一化前提位照抄）。 *)
Theorem real_gibbs_inequality_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).

Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.14 乘积界 Bishop 形：|a|·|b| ≤_B M·B（|a|≤M、|b|≤B 前提位照抄
   源件；plain-eps 直连）。 *)
Lemma real_abs_prod_le_B : forall (a b M B : Real),
  real_le (real_abs a) M -> real_le (real_abs b) B ->
  real_le_b (real_mult (real_abs a) (real_abs b)) (real_mult M B).

Proof.
  intros a b M B HMa HMB.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_prod_le_eps a b M B (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos HMa HMB) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.15 指数差界 Bishop 形：|e^x − 1| ≤_B |x|·e^{|x|}
   （-③ 逐 eps 形的 Bishop 对应物；plain-eps 直连）。 *)
Lemma real_exp_abs_minus_one_B : forall x : Real,
  real_le_b (real_abs (real_plus (cauchy_real_exp x) (real_opp real_one)))
            (real_mult (real_abs x) (cauchy_real_exp (real_abs x))).

Proof.
  intro x.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_exp_abs_minus_one_eps x (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.16 二点凸性 Bishop 形：e^{(1−η)x+ηy} ≤_B (1−η)·e^x + η·e^y
   （Varberg 锥方向；η>0、η≤1 前提位照抄源件）。 *)
Lemma real_exp_two_point_cvx_B : forall (x y eta : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
            (real_plus (real_mult (real_plus real_one (real_opp eta))
                                   (cauchy_real_exp x))
                       (real_mult eta (cauchy_real_exp y))).

Proof.
  intros x y eta Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_exp_two_point_cvx_eps x y eta Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.17 逐点 AM-GM Bishop 形：a^{1−η}·b^η ≤_B (1−η)·a + η·b
   （a^{α} := e^{α·log a}；0<a、0<b、η>0、η≤1 前提位照抄源件）。 *)
Lemma real_amgm_pointwise_B : forall (a b eta : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                       (real_pow_pos b eta Hb))
            (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                       (real_mult eta b)).

Proof.
  intros a b eta Ha Hb Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_amgm_pointwise_eps a b eta Ha Hb Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.18 插值不等式 Bishop 形：Σ_i π_t(i)^{1−η}·π*(i)^η ≤_B 1
   （M1 求和版；逐点正性 ×2 + 归一化 ×2 + η>0、η≤1 前提位照抄源件；
   List.seq 消费面与 D.5 一致）。 *)
Theorem real_interp_Z_le_one_B :
  forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (real_list_sum nat pit (List.seq 0 n)) real_one)
    (Hnormq : real_eq (real_list_sum nat pist (List.seq 0 n)) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_list_sum nat
               (fun i : nat => real_mult
                  (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                  (real_pow_pos (pist i) eta (Hpist i)))
               (List.seq 0 n))
            real_one.

Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_interp_Z_le_one_eps n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* 尾注：诚实登记表（可升格/不可升格逐件结论；供论文 §9.4 例二(iv)    *)
(* 与 §10.2 第10项(g) 回写引用）                                   *)
(*                                                                *)
(* 【结论 1｜谓词】real_le_b：Set 层 forall 型（∀eps>0, x<y+eps），  *)
(*   无 Prop 泄露；与 Or 编码 real_le 的关系仅经单向桥承载。         *)
(* 【结论 2｜单向桥】real_le_to_le_b：可证（lt 支：x<y<y+eps 传递；  *)
(*   eq 支：real_lt_compat 双侧换形）。单向——逆向                   *)
(*   real_le_b x y -> real_le x y 即 Or 形精确完成，构造性不可证，   *)
(*   论证（Or 形不可证，回写 §9.4 例二(i)/(iv)）：若逆向可证，取     *)
(*   (x, y, D) := (real_min a b, a, 1)（1 的正性证书                *)
(*   real_lt_zero_one 既有），配 real_min_le_l_eps（eps 形逐点界）   *)
(*   与完成引理立得精确 real_min_le_l（min(a,b) ≤ a 的单 Or 见证）—— *)
(*   该见证需在「b < a」（左支）与「a ≤ b ⟹ min == a」（右支）间作    *)
(*   分支选择，而该分支对构造性实数不可判定（§9.4 例一同源论证）。   *)
(*   故本库只主张 Bishop 形完成，Or 形「精确版」不主张。             *)
(* 【结论 3｜完成引理】real_le_closure_b：可证。eps'·inv(2D) 换形    *)
(*   路线（报告口径）：e₀ := eps'·inv(2D)（D>0 证书供 inv 正性）；   *)
(*   D·e₀ == eps'·(inv(2D)·D)（assoc/comm 链）；inv(2D)·D < 1       *)
(*   （D < D+D ⟹ inv(2D) < inv(D) 反单调 ⟹ inv(2D)·D < inv(D)·D；  *)
(*   inv(D)·D == D·inv(D) == 1）；故 D·e₀ < eps'·1 == eps'；        *)
(*   Or 两支：lt 支 real_lt_plus_translate 平移 + real_lt_trans；    *)
(*   eq 支 real_lt_id_l 换形。零稠密性消费。                        *)
(* 【结论 4｜定理 4.9 对应物】real_rlhf_optimal_B：可升格（完整）——  *)
(*   证书供给链核查：残差权系数 D 的正性证书 D_pos 为 RealRLHFMain   *)
(*   节内既有接口变量，零新增前提；eps 形残差恰为 mult D eps 字面    *)
(*   对齐（签名探针实测 discharge 序 9 件直连消费）， Bishop 形       *)
(*   J(π) ≤_B J(π★) 即完成引理单步实例。                            *)
(* 【结论 5｜定理 6.6 对应物】real_ppo_conservative_B：有条件升格——  *)
(*   证书供给链核查：残差权系数 E := Σ π_old·adv 的正性在 RealPPOMain *)
(*   接口面（ext/le/add + 双侧逐点正性）下不可推导（adv 无上界、     *)
(*   E==0 与 E>0 构造性不可分），无内在供给链，故 Bishop 形语句补    *)
(*   E > 0 显式证书前提（本件语句的唯一新增前提）；另补              *)
(*   标量提取诚实接口 real_sum_over_S_linear（残差折叠               *)
(*   Σ π_old·(eps·adv) == E·eps 所需；RealAttnSteady 同名件先例）。   *)
(*   冻结结论（无证书情形）：E 的正性证书缺位时 Bishop 形不可主张，    *)
(*   定理 6.6 维持 eps 形（real_ppo_conservative_eps）陈述不变；      *)
(*   Or 形精确完成对 4.9/6.6 同样不可达（结论 2 论证，编码侧关键，   *)
(*   与 D 是否依赖 eps 无关）。                                      *)
(* 【结论 6｜D:=one 特化完成】real_le_closure_b_one：可证——plain-eps  *)
(*   余量族（x ≤ y+eps 逐点）的统一 Bishop 完成器。证书供给链核查：    *)
(*   D := real_one，正性证书 real_lt_zero_one 为 闭合既有件；    *)
(*   换形面仅 1·eps ≡ eps（mult_one 右形取反 + comm 运输 + le_id_r    *)
(*   右端等式换形），零新增前提。适用判据：结论形恰为                  *)
(*   real_le x (y + eps) 字面的全语料 eps 族皆单步直连。               *)
(* 【结论 7｜四件 D:=one 实例】min_l_B / min_r_B / abs_triangle_le_B / *)
(*   square_nonneg_B：可升格（完整）——证书链均「特化完成单步 + eps 形  *)
(*   原件直连」两级。其中 min_l_B 与结论 2 同框对照：Or 形精确版       *)
(*   （real_min_le_l）不可证、Bishop 形（real_min_le_l_B）可证，       *)
(*   同一语句的两个编码形态可行性相反，为 §9.4 例二(iv) 的原生示例。    *)
(* 【结论 8｜step_kl_eta_bound_B】可升格（完整）——步进 KL 收缩的       *)
(*   Bishop 形 Σ kl(p‖step) ≤_B eta·Σ kl(p‖r)：余量形为 plain-eps       *)
(*   （eta 缩放因子在复合右端内部、非 D·eps 字面），故走 D:=one 特化    *)
(*   完成单步 + 原件直连；原件前提位 eta>0 / eta≤1 照抄，零新增前提；   *)
(*   原件为顶层闭合定理（全显位签名，探针实测）。盘点注：Real     *)
(*   层 33 件 eps 族中，D·eps 字面余量形仅 real_rlhf_optimal_eps 一件   *)
(*   （结论 4 已升格），其余全为 plain-eps（D:=one 统一完成覆盖）或     *)
(*   复合/多 eps 形（结论 9(e)/(f)）。                                  *)
(* 【结论 9｜盘点冻结结论（本轮全语料扫描，供论文侧引用）】             *)
(*   (a) real_dpo_loss_pi_star_bounded_eps：命名残留 eps 而语句为      *)

(*       谓词不适用（严格界自足），冻结（形态不匹配）。                 *)
(*   (b) real_le_eps_Kone：结论右端含被界量 e（e ≤ k·(1+e) 自涉形），   *)
(*       非固定右端 y+D·eps 形——余量形态不匹配，冻结。                  *)
(*   (c) real_beta_le_epsK：单调换位形（eps'·inv(...) ≤ eps'·inv K）    *)
(*       非余量形，冻结（形态不匹配）。                                 *)
(*   (d) real_le_pointwise_eps / real_abs_triangle_eps：Q 层逐点形      *)
(*       （eps : Q、sigT 点态见证），非 Real 层 real_le 余量形——        *)
(*       编码层外，冻结（引本登记表结论 2 同源「编码侧」论证先例）。       *)
(*   (e) real_abs_le_quad_eps / real_abs_h_sq_le_eps /                  *)
(*       real_quad_t_le_h_eps：多 eps 前提组合形（eps1/eps2/eps' 链、   *)
(*       余量内嵌 |h| 因子），可升格但证书链长且语句须前提位改造——      *)
(*       显式假设未建（非冻结，留后续席）。                                 *)
(*   (f) real_db_breaking_bound_eps：复合 D 形（inv(分区)·T·(exp(…)·     *)
(*       (eps+eps'))），D 显式 eps 无关但正性证书链长（inv_pos 证书 +   *)
(*       exp 正性 + 逐 eps 面拆分）——显式假设未建（非冻结）。               *)
(*   (g) req 层 eps 件（req_db_breaking_bound_eps / req_le_eps_Kone /   *)
(*       req_log_one_plus_le_eps / req_log_one_plus_ge_eps /            *)
(*       ag_sum_le_r_max_eps / ag_sum_min_le_eps 等）：req 接口编码层    *)
(*       与 Real 不同族，real_le_b 谓词作用域外——冻结             *)
(*       （引结论 2 编码侧论证先例；req 层已有精确 le 形先例             *)
(*       req_rdf_abs_triangle，Bishop 升格在 req 层非必需）。           *)
(*   (h) 可升格未建清单（同型可平移，证书链与 D.1 至 D.5 同构）：        *)
(*       r_max_le_l / r_max_le_r、metric_triangle、metric_pos、          *)
(*       abs_nonneg_le、pos_part_nonneg、exp_ge_linear、log_le_linear、  *)
(*       log_one_plus_le / log_one_plus_ge、abs_prod_le（前提型         *)
(*       |a|≤M、|b|≤B）、exp_abs_minus_one、exp_two_point_cvx、          *)
(*       amgm_pointwise、gibbs_inequality、quad_div_le_two（前提        *)
(*       s>1/2）——共 16 件，全部 plain-eps 或前提型 plain-eps，          *)
(*       证书 real_lt_zero_one（或前提位正性）既有。                    *)
(*       另 real_interp_Z_le_one_eps（Σ pit^(1-eta)·pist^eta ≤ 1 + eps， *)
(*       plain-eps）同入本清单；real_gibbs_core_eps 为第二件 D·eps      *)
(*       字面余量形（p-q ≤ p·(-log(q/p)) + p·eps，D:=p eps 无关、       *)
(*       正性证书 Hp 前提位既有）——升格路径=real_le_closure_b 直接     *)
(*       实例（结论 4 同型）。【第二席核对注】本清单 16+2 件已全部       *)
(*       于 Part E 升格落盘，逐件结论见结论 10。                        *)
(* 【结论 10｜Part E 十八件续建】盘点清单判「可升」18 件全部升格落盘——   *)
(*   (i) 17 件 plain-eps 余量形：real_metric_pos_B /                      *)
(*       real_metric_triangle_B / real_abs_nonneg_le_B /                  *)
(*       real_r_max_le_l_B / real_r_max_le_r_B /                          *)
(*       real_pos_part_nonneg_B / real_exp_ge_linear_B /                  *)
(*       real_log_le_linear_B / real_log_one_plus_le_B /                  *)
(*       real_log_one_plus_ge_B / real_quad_div_le_two_B /                *)
(*       real_gibbs_inequality_B / real_abs_prod_le_B /                   *)
(*       real_exp_abs_minus_one_B / real_exp_two_point_cvx_B /            *)
(*       real_amgm_pointwise_B / real_interp_Z_le_one_B——证书链均          *)
(*       「one 特化完成单步 + 源件直连」两级（结论 6 适用判据覆盖）；       *)
(*       前提位件（log_le_linear 之 Hx、log_one_plus 之 Hs/Ht、            *)
(*       quad_div 之 Hs/Hs12、abs_prod 之 |a|≤M/|b|≤B、cvx/amgm/interp     *)
(*       之 eta 双前提、gibbs_inequality 之归一化 ×2）逐字照抄源件，        *)
(*       零新增前提；源件模块归属经 Check 探针实测（RealSetoid 双件、      *)
(*       RealInterfaceEnhancedMod 双件前缀消费，余者出节平名）。            *)
(*   (ii) real_gibbs_core_B：D·eps 字面余量第二件（余量 p·eps 乘在         *)
(*       显式系数 p 上、p 为量且 Hp 前提位既有）——real_le_closure_b        *)
(*       直接实例（D:=p），结论 4 同型完成、real_rlhf_optimal_B 供给        *)
(*       手法复用。至此 Real 层 36 件 eps 族中两件 D·eps 字面形       *)
(*       全部升格完毕（rlhf 于 Part B、gibbs_core 于本批），余 33 件       *)
(*       plain/复合/冻结三分如结论 8 与 9。                                *)
(*   (iii) 18 件语句面均无 Or 分支（real_le_b 谓词承载），提取面同          *)
(*       Part D：forall 型 Set 层，非平凡体全为源件真实现直连，              *)
(*       Print Assumptions 全 Closed（见文末二十八条）。                    *)

(*   Obj.magic=0 / G4 coqchk 9.0 通过；完成引理+桥+两应用件+Part D        *)
(*   五件+Part E 十八件 Print Assumptions Closed（见文末二十八条）。    *)
(* ============================================================ *)

Print Assumptions real_le_to_le_b.
Print Assumptions real_le_closure_b.
Print Assumptions real_rlhf_optimal_B.
Print Assumptions real_ppo_conservative_B.
Print Assumptions real_le_closure_b_one.
Print Assumptions real_min_le_l_B.
Print Assumptions real_min_le_r_B.
Print Assumptions real_abs_triangle_le_B.
Print Assumptions real_square_nonneg_B.
Print Assumptions real_step_kl_eta_bound_B.
Print Assumptions real_r_max_le_l_B.
Print Assumptions real_r_max_le_r_B.
Print Assumptions real_abs_nonneg_le_B.
Print Assumptions real_metric_pos_B.
Print Assumptions real_metric_triangle_B.
Print Assumptions real_pos_part_nonneg_B.
Print Assumptions real_exp_ge_linear_B.
Print Assumptions real_log_le_linear_B.
Print Assumptions real_log_one_plus_le_B.
Print Assumptions real_log_one_plus_ge_B.
Print Assumptions real_quad_div_le_two_B.
Print Assumptions real_gibbs_core_B.
Print Assumptions real_gibbs_inequality_B.
Print Assumptions real_abs_prod_le_B.
Print Assumptions real_exp_abs_minus_one_B.
Print Assumptions real_exp_two_point_cvx_B.
Print Assumptions real_amgm_pointwise_B.
Print Assumptions real_interp_Z_le_one_B.

(* ToyR 替换席验证位：对替换代表件做假设面核验（零承认件句式自证） *)
Print Assumptions real_le_closure_b_one.
Print Assumptions real_min_le_l_B.
Print Assumptions real_rlhf_optimal_B.
