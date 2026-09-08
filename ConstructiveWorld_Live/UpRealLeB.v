(* ============================================================ *)
(* UpRealLeB.v —— Real 层 Bishop 形非严格序谓词与收口引理族        *)
(*   （M2 收口引理席 · §9.4 例二(iv) / §10.2 第10项(g) 落地件）     *)
(*                                                                *)
(* 主结果（全部 Set 层、零 Prop 泄露、零新公理）：                  *)
(*   1. real_le_b x y := forall eps>0, real_lt x (y + eps)         *)
(*      （Bishop 形非严格序，CW219 Real/柯西层编码）                *)
(*   2. real_le_to_le_b：单向桥 real_le x y -> real_le_b x y        *)
(*      （lt 支平凡平移；eq 支 real_lt_compat 换形；单向——         *)
(*        逆向即 Or 形精确收口，构造性不可证，见尾注台账）           *)
(*   3. real_le_closure_b：收口引理——D 带显式正性证书 +            *)
(*      (forall eps>0, real_le x (y + D·eps)) -> real_le_b x y      *)
(*      构造：取 e₀ := eps'·inv(2D)（D>0 消 inv），换形链           *)
(*        D·e₀ == eps'·(inv(2D)·D) < eps'·1 == eps'                 *)
(*      （inv(2D)·D < 1 经 D < 2D + inv 反单调 + inv_pos_correct）， *)
(*      Or 编码两支分别经 lt 保序加法平移 / 等式换形闭合，           *)
(*      全程无需稠密性。                                            *)
(*   4. real_rlhf_optimal_B：定理 4.9 对应物 J(π) ≤_B J(π★)         *)
(*      （D_pos 证书在 RealRLHFMain 接口既有，零新增前提——          *)
(*        完整升格判词，见尾注台账）                                *)
(*   5. real_ppo_conservative_B：定理 6.6 对应物（有条件升格）       *)
(*      （须补残差权系数 E := Σ π_old·adv 的显式正性证书前提——      *)
(*        E==0 与 E>0 构造性不可分、无内在证书供给链；               *)
(*        另补标量提取诚实接口 real_sum_over_S_linear                *)
(*        （RealAttnSteady 同名件逐字复刻）；无证书情形              *)
(*        维持 eps 形 real_ppo_conservative_eps 不变——冻结判词       *)
(*        见尾注台账）                                              *)
(*                                                                *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；Set 层语句（real_le_b    *)
(* 为 Set 值 forall 型，无 Prop 泄露）；纯 term-mode 显式组装        *)
(* （real_eq 非 Id，禁 rewrite，全链 real_eq_trans/compat）；        *)
(* 全 Qed. 闭合；收口引理+桥 Print Assumptions Closed。              *)
(* 编译配方：coqc -Q . "" -Q "..\001" "" UpRealLeB.v                *)
(* （cpu_guard.ps1 包装，零裸调）。                                  *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* Part A：Bishop 形谓词 + 单向桥 + 收口引理（核心件）              *)
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

(* 收口引理（核心）：D 带显式正性证书时，逐 eps 余量族可收口为 Bishop 形
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
(*   节变量逐字复刻 RealRLHFMain 收口实际消费面（9 件，签名探针     *)
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
(* 诚实接口（与 RealRLHFMain 同名同型，链式真证放电） *)
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

(* J(π) ≤_B J(π★)：RLHF 最优性的 Bishop 形收口（完整升格判词：
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
  apply (real_le_closure_b _ _ D D_pos).
  intros eps Heps.
  exact (real_rlhf_optimal_eps S real_sum_over_S real_base_loss D D_pos
           Z_align_r Z_align_r_pos real_gibbs_sum_eps real_kl_decomp_full
           pi Hpi Hnormpi eps Heps).
Qed.

End RealRLHFLeB.

(* ============================================================ *)
(* Part C：定理 6.6 对应物——PPO 保守性 Bishop 形（有条件升格）      *)
(*   残差权系数 E := Σ π_old·adv 需显式正性证书前提（E==0 与 E>0    *)
(*   构造性不可分、无内在供给链）；标量提取 real_sum_over_S_linear   *)
(*   为诚实接口（RealAttnSteady 同名件逐字复刻）。无证书情形维持     *)
(*   eps 形（real_ppo_conservative_eps）不变——冻结判词见尾注台账。   *)
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

(* PPO 保守性 Bishop 形（有条件升格判词：须补 E > 0 显式证书前提；
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
(* 尾注：诚实台账（可升格/不可升格逐件判词；供论文 §9.4 例二(iv)    *)
(* 与 §10.2 第10项(g) 回写引用）                                   *)
(*                                                                *)
(* 【判词 1｜谓词】real_le_b：Set 层 forall 型（∀eps>0, x<y+eps），  *)
(*   无 Prop 泄露；与 Or 编码 real_le 的关系仅经单向桥承载。         *)
(* 【判词 2｜单向桥】real_le_to_le_b：可证（lt 支：x<y<y+eps 传递；  *)
(*   eq 支：real_lt_compat 双侧换形）。单向——逆向                   *)
(*   real_le_b x y -> real_le x y 即 Or 形精确收口，构造性不可证，   *)
(*   论证（Or 形不可证，回写 §9.4 例二(i)/(iv)）：若逆向可证，取     *)
(*   (x, y, D) := (real_min a b, a, 1)（1 的正性证书                *)
(*   real_lt_zero_one 既有），配 real_min_le_l_eps（eps 形逐点界）   *)
(*   与收口引理立得精确 real_min_le_l（min(a,b) ≤ a 的单 Or 见证）—— *)
(*   该见证需在「b < a」（左支）与「a ≤ b ⟹ min == a」（右支）间作    *)
(*   分支选择，而该分支对构造性实数不可判定（§9.4 例一同源论证）。   *)
(*   故本库只主张 Bishop 形收口，Or 形「精确版」不主张。             *)
(* 【判词 3｜收口引理】real_le_closure_b：可证。eps'·inv(2D) 换形    *)
(*   路线（报告口径）：e₀ := eps'·inv(2D)（D>0 证书供 inv 正性）；   *)
(*   D·e₀ == eps'·(inv(2D)·D)（assoc/comm 链）；inv(2D)·D < 1       *)
(*   （D < D+D ⟹ inv(2D) < inv(D) 反单调 ⟹ inv(2D)·D < inv(D)·D；  *)
(*   inv(D)·D == D·inv(D) == 1）；故 D·e₀ < eps'·1 == eps'；        *)
(*   Or 两支：lt 支 real_lt_plus_translate 平移 + real_lt_trans；    *)
(*   eq 支 real_lt_id_l 换形。零稠密性消费。                        *)
(* 【判词 4｜定理 4.9 对应物】real_rlhf_optimal_B：可升格（完整）——  *)
(*   证书供给链核查：残差权系数 D 的正性证书 D_pos 为 RealRLHFMain   *)
(*   节内既有接口变量，零新增前提；eps 形残差恰为 mult D eps 字面    *)
(*   对齐（签名探针实测 discharge 序 9 件直连消费）， Bishop 形       *)
(*   J(π) ≤_B J(π★) 即收口引理单步实例。                            *)
(* 【判词 5｜定理 6.6 对应物】real_ppo_conservative_B：有条件升格——  *)
(*   证书供给链核查：残差权系数 E := Σ π_old·adv 的正性在 RealPPOMain *)
(*   接口面（ext/le/add + 双侧逐点正性）下不可推导（adv 无上界、     *)
(*   E==0 与 E>0 构造性不可分），无内在供给链，故 Bishop 形语句补    *)
(*   E > 0 显式证书前提（本件语句的唯一新增前提）；另补              *)
(*   标量提取诚实接口 real_sum_over_S_linear（残差折叠               *)
(*   Σ π_old·(eps·adv) == E·eps 所需；RealAttnSteady 同名件先例）。   *)
(*   冻结判词（无证书情形）：E 的正性证书缺位时 Bishop 形不可主张，    *)
(*   定理 6.6 维持 eps 形（real_ppo_conservative_eps）陈述不变；      *)
(*   Or 形精确收口对 4.9/6.6 同样不可达（判词 2 论证，编码侧关键，   *)
(*   与 D 是否依赖 eps 无关）。                                      *)
(* 【机器状态】四关卡：G1 禁词全零 / G2 EXIT=0 / G3 提取探针          *)
(*   Obj.magic=0 / G4 coqchk 9.0 通过；收口引理+桥+两应用件           *)
(*   Print Assumptions Closed（见文末四条）。                        *)
(* ============================================================ *)

Print Assumptions real_le_to_le_b.
Print Assumptions real_le_closure_b.
Print Assumptions real_rlhf_optimal_B.
Print Assumptions real_ppo_conservative_B.
