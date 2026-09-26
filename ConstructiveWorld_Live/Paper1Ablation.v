(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* Paper1Ablation.v —— 位 CZD11（组 E-STAGING-CZD11）        *)
(* 论文1《构造性ML对齐统一形式化》可消融 C 类槽施工              *)
(*                                                              *)
(* 前缀 pa1_（防撞 grep）；基座 ConstructiveWorld_vo_901（268）  *)
(*                                                              *)
(* 槽1 pa1_grpo_unit_moment_pop：论文 §10.2 第1项(c) 开口        *)
(*     「单位矩全装配 (1/G)·Σ(A_i/σ)² == 1」population 形。      *)
(*     库内 UpGRPO.real_grpo_standardized_unit_moment 为未归一形 *)
(*     Σ(A_i/σ)²==1；论文表2 自认 population 形未装配。本件装配： *)
(*     使用 real_list_sum_g_linear/ext、real_mult_exchange、     *)
(*     real_inv_pos_correct，零新增接口前提。                    *)
(* 槽2 pa1_dpo_reward_relative_exact：论文 §9.2 开口清单         *)
(*     「DPO 相对精确 5.5/5.6 尚未有 Real 层版本」之 5.6 对偶：   *)
(*     π★ 处隐式奖励差分 == 真实奖励差分。使用 S08 的 5.9 件     *)
(*     real_dpo_reward_recovers_up_to_baseline（已证 Closed）。  *)
(* 槽3 pa1_raw_second_moment_decomp：论文 §9.2 阻碍分析          *)
(*     「GRPO 方差族 7.4/7.5 尚未有 Real 层版本」之 7.4 恒等对偶：*)
(*     Σ r_i² == Σ A_i² + G·μ²（未归一中心二阶矩分解；A 为组内   *)
(*     中心化优势）。使用 S08 real_grpo_advantage_zero_mean +    *)
(*     real_list_sum_g_linear/add/const。                        *)
(*                                                              *)
(* 红线：纯构造性零公理、Set 层零 Prop 泄露、全 Qed 非平凡真证。 *)
(* 验收：G1 禁词0 / G2 EXIT=0 / Print Assumptions 全 Closed。    *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import S08_RealMainlineDPO S03_QExp S09_EntropyReal
               S07_RealSetoidExpLog S02_CauchyComplete S01_BaseRing.

(* ############ 第0件：opp 的等式兼容（槽2 装配基元） ############ *)
(* 库内缺 real_opp 等式兼容件（仅有序兼容 opp_le_compat）；        *)
(* 本件以 plus_opp/plus_zero/assoc 纯代数链自证，不触 Q 层逐点。   *)
Lemma pa1_opp_eq_compat : forall a b : Real,
  real_eq a b -> real_eq (real_opp a) (real_opp b).
Proof.
  intros a b Hab.
  apply (real_eq_trans _ (real_plus (real_opp a) (real_plus b (real_opp b))) _).
  - (* opp a == opp a + (b + opp b)：右端括号项 == 0 *)
    apply (real_eq_trans _ (real_plus (real_opp a) real_zero) _).
    + apply (real_eq_sym _ _ (real_plus_zero (real_opp a))).
    + apply (RealSetoid.real_eq_plus_compat (real_opp a) real_zero
               (real_opp a) (real_plus b (real_opp b))
               (real_eq_refl (real_opp a))
               (real_eq_sym _ _ (real_plus_opp b))).
  - (* opp a + (b + opp b) == opp b：(opp a + b) 项换 a、(opp a + a) 项归零 *)
    apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) (real_opp b)) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus (real_plus (real_opp a) a) (real_opp b)) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp a) b) (real_opp b)
                 (real_plus (real_opp a) a) (real_opp b)
                 (RealSetoid.real_eq_plus_compat (real_opp a) b (real_opp a) a
                    (real_eq_refl (real_opp a)) (real_eq_sym _ _ Hab))
                 (real_eq_refl (real_opp b))).
      * apply (real_eq_trans _ (real_plus real_zero (real_opp b)) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) a)
                    (real_opp b) real_zero (real_opp b)
                    (real_eq_trans _ (real_plus a (real_opp a)) _
                       (real_plus_comm (real_opp a) a) (real_plus_opp a))
                    (real_eq_refl (real_opp b))).
        -- apply (real_eq_trans _ (real_plus (real_opp b) real_zero) _).
           ++ apply real_plus_comm.
           ++ apply real_plus_zero.
Qed.

(* ############ 第0.5件：乘法四因子交换（自足内联，卸 UpGRPO 依赖） ############ *)
(* 与 UpGRPO.real_mult_exchange 同构；为使本稿只依赖 czc10 +2 件集，   *)
(* 以 monolith/S02 基元代数自证内联。 *)
Lemma pa1_mult_exchange : forall a b c d : Real,
  real_eq (real_mult (real_mult a c) (real_mult b d))
          (real_mult (real_mult a b) (real_mult c d)).
Proof.
  intros a b c d.
  apply (real_eq_trans _ (real_mult a (real_mult c (real_mult b d))) _).
  - apply (real_eq_sym (real_mult a (real_mult c (real_mult b d)))
                       (real_mult (real_mult a c) (real_mult b d))
                       (real_mult_assoc a c (real_mult b d))).
  - apply (real_eq_trans _ (real_mult a (real_mult (real_mult c b) d)) _
      (RealSetoid.real_eq_mult_compat a (real_mult c (real_mult b d))
         a (real_mult (real_mult c b) d)
         (real_eq_refl a) (real_mult_assoc c b d))).
    + apply (real_eq_trans _ (real_mult a (real_mult b (real_mult c d))) _
        (RealSetoid.real_eq_mult_compat a (real_mult (real_mult c b) d)
           a (real_mult b (real_mult c d))
           (real_eq_refl a)
           (real_eq_trans _ _ _
             (RealSetoid.real_eq_mult_compat (real_mult c b) d
                (real_mult b c) d
                (real_mult_comm c b) (real_eq_refl d))
             (real_eq_sym (real_mult b (real_mult c d))
                          (real_mult (real_mult b c) d)
                          (real_mult_assoc b c d))))
        (real_mult_assoc a b (real_mult c d))).
Qed.

(* ############ 槽1 + 槽3：GRPO population 单位矩 与 7.4 恒等对偶 ############ *)
Section PA1Grpo.

Variable Grp : Set.
Variable grp_enum : list Grp.
Variable real_size_pos : real_lt real_zero (real_of_nat (length grp_enum)).
Variable reward_grp : Grp -> Real.

Let sizeR : Real := real_of_nat (length grp_enum).
Let invG : Real := real_inv_pos sizeR real_size_pos.
Let mean : Real :=
  real_mult invG (real_list_sum_g Grp reward_grp grp_enum).
Let A (i : Grp) : Real := real_plus (reward_grp i) (real_opp mean).
Let Var : Real :=
  real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum.

(* ---------- 槽1 主定理：population 形单位矩 ---------- *)
(* 前提面诚实最小化：σ 与 σ²==invG·Var 显式给出（σ 的存在性由    *)
(* AttnSqrt real_sqrt_exists 一族另供给；此处只装配单位矩本身）。 *)
Theorem pa1_grpo_unit_moment_pop :
  forall (sig : Real) (Hsig : real_lt real_zero sig)
         (Hsq : real_eq (real_mult sig sig) (real_mult invG Var)),
    real_eq
      (real_mult invG
         (real_list_sum_g Grp
            (fun i : Grp =>
               real_mult (real_mult (A i) (real_inv_pos sig Hsig))
                         (real_mult (A i) (real_inv_pos sig Hsig)))
            grp_enum))
      real_one.
Proof.
  intros sig Hsig Hsq.
  set (u := real_inv_pos sig Hsig).
  (* 步A：和内逐项交换 + 线性提取，Σ((A·u)·(A·u)) == (u·u)·Var *)
  assert (Hsum : real_eq
           (real_list_sum_g Grp
              (fun i : Grp =>
                 real_mult (real_mult (A i) u) (real_mult (A i) u)) grp_enum)
           (real_mult (real_mult u u) Var)).
  { apply (real_eq_trans _
      (real_list_sum_g Grp
         (fun i : Grp =>
            real_mult (real_mult (A i) (A i)) (real_mult u u)) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply pa1_mult_exchange.
    - apply (real_eq_trans _
        (real_mult (real_mult u u)
                   (real_list_sum_g Grp
                      (fun i : Grp => real_mult (A i) (A i)) grp_enum)) _).
      + apply (real_eq_trans _
          (real_list_sum_g Grp
             (fun i : Grp =>
                real_mult (real_mult u u) (real_mult (A i) (A i))) grp_enum) _).
        * apply real_list_sum_g_ext.
          intro i. apply real_mult_comm.
        * apply real_list_sum_g_linear.
      + apply real_eq_refl. }
  (* 步B：标量恒等 invG·((u·u)·Var) == 1（Hsq 吸收 + inv 正确性） *)
  assert (Hscal : real_eq
           (real_mult invG (real_mult (real_mult u u) Var)) real_one).
  { apply (real_eq_trans _ (real_mult (real_mult (real_mult u u) invG) Var) _).
    - apply (real_eq_trans _ (real_mult (real_mult invG (real_mult u u)) Var) _).
      + apply real_mult_assoc.
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult invG (real_mult u u)) Var
                 (real_mult (real_mult u u) invG) Var
                 (real_mult_comm invG (real_mult u u)) (real_eq_refl Var)).
    - apply (real_eq_trans _ (real_mult (real_mult u u) (real_mult invG Var)) _).
      + apply (real_eq_sym _ _ (real_mult_assoc (real_mult u u) invG Var)).
      + apply (real_eq_trans _ (real_mult (real_mult u u) (real_mult sig sig)) _).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult u u) (real_mult invG Var)
                   (real_mult u u) (real_mult sig sig)
                   (real_eq_refl (real_mult u u)) (real_eq_sym _ _ Hsq)).
        * apply (real_eq_trans _ (real_mult (real_mult sig u) (real_mult sig u)) _).
          -- apply (real_eq_trans _ (real_mult (real_mult u sig) (real_mult u sig)) _).
             ++ apply pa1_mult_exchange.
             ++ apply (RealSetoid.real_eq_mult_compat
                         (real_mult u sig) (real_mult u sig)
                         (real_mult sig u) (real_mult sig u)
                         (real_mult_comm u sig) (real_mult_comm u sig)).
          -- apply (real_eq_trans _ (real_mult real_one real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat
                         (real_mult sig u) (real_mult sig u)
                         real_one real_one
                         (real_inv_pos_correct sig Hsig)
                         (real_inv_pos_correct sig Hsig)).
             ++ apply real_mult_one. }
  (* 主链：invG·Σ == invG·((u·u)·Var) == 1 *)
  apply (real_eq_trans _ (real_mult invG (real_mult (real_mult u u) Var)) _).
  - apply (RealSetoid.real_eq_mult_compat invG
             (real_list_sum_g Grp
                (fun i : Grp =>
                   real_mult (real_mult (A i) u) (real_mult (A i) u)) grp_enum)
             invG (real_mult (real_mult u u) Var)
             (real_eq_refl invG) Hsum).
  - exact Hscal.
Qed.

(* ---------- 槽3 主定理：7.4 恒等 Real 对偶（未归一形） ---------- *)
(* Σ r_i² == Σ A_i² + G·μ²；G := 组大小，μ := 组均值，A := r − μ。 *)
(* 装配：逐点平方展开（distrib_r + distrib）+ 求和三分 +          *)
(*       零均值（使用 S08 real_grpo_advantage_zero_mean）+ 常数和。 *)
Theorem pa1_raw_second_moment_decomp :
  real_eq
    (real_list_sum_g Grp
       (fun i : Grp => real_mult (reward_grp i) (reward_grp i)) grp_enum)
    (real_plus Var (real_mult sizeR (real_mult mean mean))).
Proof.
  (* 零均值：Σ A == 0（S08 主定理件 + mult_one 运送） *)
  assert (Hz : real_eq (real_list_sum_g Grp A grp_enum) real_zero).
  { pose proof (S08_RealMainlineDPO.real_grpo_advantage_zero_mean
                  Grp grp_enum real_size_pos reward_grp real_one) as Hz1.
    apply (real_eq_trans _
      (real_list_sum_g Grp (fun i : Grp => real_mult (A i) real_one) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply (real_eq_sym _ _ (real_mult_one (A i))).
    - exact Hz1. }
  (* 左标量缩放和：Σ(c·A) == c·ΣA == c·0 == 0 *)
  assert (Hzl : forall c : Real,
           real_eq
             (real_list_sum_g Grp
                (fun i : Grp => real_mult c (A i)) grp_enum) real_zero).
  { intro c.
    apply (real_eq_trans _ (real_mult c (real_list_sum_g Grp A grp_enum)) _).
    - apply real_list_sum_g_linear.
    - apply (real_eq_trans _ (real_mult c real_zero) _).
      + apply (RealSetoid.real_eq_mult_compat c (real_list_sum_g Grp A grp_enum)
                 c real_zero (real_eq_refl c) Hz).
      + apply real_mult_zero. }
  (* 右标量缩放和：Σ(A·c) == Σ(c·A) == 0 *)
  assert (Hzr : forall c : Real,
           real_eq
             (real_list_sum_g Grp
                (fun i : Grp => real_mult (A i) c) grp_enum) real_zero).
  { intro c.
    apply (real_eq_trans _
      (real_list_sum_g Grp (fun i : Grp => real_mult c (A i)) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply real_mult_comm.
    - apply Hzl. }
  (* 逐点：r·r == (A·A + A·mean) + (mean·A + mean·mean) *)
  assert (Hpt : forall i : Grp,
           real_eq (real_mult (reward_grp i) (reward_grp i))
                   (real_plus (real_plus (real_mult (A i) (A i))
                                          (real_mult (A i) mean))
                              (real_plus (real_mult mean (A i))
                                         (real_mult mean mean)))).
  { intro i.
    (* r == A + mean（中心化恒等：r == (r − mean) + mean） *)
    assert (Hra : real_eq (reward_grp i) (real_plus (A i) mean)).
    { apply (real_eq_trans _ (real_plus (reward_grp i) real_zero) _).
      - apply (real_eq_sym _ _ (real_plus_zero (reward_grp i))).
      - apply (real_eq_trans _
                 (real_plus (reward_grp i) (real_plus (real_opp mean) mean)) _).
        + apply (RealSetoid.real_eq_plus_compat (reward_grp i) real_zero
                   (reward_grp i) (real_plus (real_opp mean) mean)
                   (real_eq_refl (reward_grp i))).
          apply (real_eq_trans _ (real_plus mean (real_opp mean)) _).
          * apply (real_eq_sym _ _ (real_plus_opp mean)).
          * apply (real_plus_comm mean (real_opp mean)).
        + apply real_plus_assoc. }
    (* 平方展开：r·r == (A+mean)·(A+mean) == A·(A+mean) + mean·(A+mean) *)
    apply (real_eq_trans _
      (real_mult (real_plus (A i) mean) (real_plus (A i) mean)) _).
    - apply (RealSetoid.real_eq_mult_compat (reward_grp i) (reward_grp i)
               (real_plus (A i) mean) (real_plus (A i) mean) Hra Hra).
    - apply (real_eq_trans _
        (real_plus (real_mult (A i) (real_plus (A i) mean))
                   (real_mult mean (real_plus (A i) mean))) _).
      + apply (real_eq_sym _ _ (real_distrib_r (A i) mean (real_plus (A i) mean))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (A i) (real_plus (A i) mean))
                 (real_mult mean (real_plus (A i) mean))
                 (real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                 (real_plus (real_mult mean (A i)) (real_mult mean mean))
                 (real_distrib (A i) (A i) mean)
                 (real_distrib mean (A i) mean)). }
  (* 求和三分：Σ r² == (ΣX + ΣY) + (ΣZ + ΣW)，X=A² Y=A·mean Z=mean·A W=mean² *)
  apply (real_eq_trans _
    (real_list_sum_g Grp
       (fun i : Grp =>
          real_plus (real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                    (real_plus (real_mult mean (A i)) (real_mult mean mean)))
       grp_enum) _).
  - apply real_list_sum_g_ext.
    intro i. apply Hpt.
  - apply (real_eq_trans _
      (real_plus (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult (A i) mean) grp_enum))
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult mean (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult mean mean) grp_enum))) _).
    + exact
        (real_eq_trans _
           (real_plus (real_list_sum_g Grp
                         (fun i : Grp =>
                            real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                         grp_enum)
                      (real_list_sum_g Grp
                         (fun i : Grp =>
                            real_plus (real_mult mean (A i)) (real_mult mean mean))
                         grp_enum))
           _
           (real_list_sum_g_add Grp
              (fun i : Grp =>
                 real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
              (fun i : Grp =>
                 real_plus (real_mult mean (A i)) (real_mult mean mean))
              grp_enum)
           (RealSetoid.real_eq_plus_compat
              (real_list_sum_g Grp
                 (fun i : Grp =>
                    real_plus (real_mult (A i) (A i)) (real_mult (A i) mean)) grp_enum)
              (real_list_sum_g Grp
                 (fun i : Grp =>
                    real_plus (real_mult mean (A i)) (real_mult mean mean)) grp_enum)
              (real_plus (real_list_sum_g Grp
                            (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                         (real_list_sum_g Grp
                            (fun i : Grp => real_mult (A i) mean) grp_enum))
              (real_plus (real_list_sum_g Grp
                            (fun i : Grp => real_mult mean (A i)) grp_enum)
                         (real_list_sum_g Grp
                            (fun i : Grp => real_mult mean mean) grp_enum))
              (real_list_sum_g_add Grp
                 (fun i : Grp => real_mult (A i) (A i))
                 (fun i : Grp => real_mult (A i) mean) grp_enum)
              (real_list_sum_g_add Grp
                 (fun i : Grp => real_mult mean (A i))
                 (fun i : Grp => real_mult mean mean) grp_enum))).
    + (* 零项消去 + 常数项：== Var + G·mean² *)
      apply (real_eq_trans _
        (real_plus (real_plus Var real_zero)
                   (real_plus real_zero
                              (real_mult sizeR (real_mult mean mean)))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult (A i) mean) grp_enum))
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult mean (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult mean mean) grp_enum))
                 (real_plus Var real_zero)
                 (real_plus real_zero (real_mult sizeR (real_mult mean mean)))
                 (RealSetoid.real_eq_plus_compat
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult (A i) mean) grp_enum)
                    Var real_zero (real_eq_refl Var) (Hzr mean))
                 (RealSetoid.real_eq_plus_compat
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult mean (A i)) grp_enum)
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult mean mean) grp_enum)
                    real_zero (real_mult sizeR (real_mult mean mean))
                    (Hzl mean)
                    (real_list_sum_g_const Grp (real_mult mean mean) grp_enum))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus Var real_zero)
                 (real_plus real_zero (real_mult sizeR (real_mult mean mean)))
                 Var (real_mult sizeR (real_mult mean mean))
                 (real_plus_zero Var)
                 (real_eq_trans _
                    (real_plus (real_mult sizeR (real_mult mean mean)) real_zero) _
                    (real_plus_comm real_zero
                       (real_mult sizeR (real_mult mean mean)))
                    (real_plus_zero (real_mult sizeR (real_mult mean mean))))).
Qed.

End PA1Grpo.

(* ############ 槽2：DPO 相对精确 5.6 Real 对偶 ############ *)
Section PA1Dpo.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* 论文 5.6：π★ 处隐式奖励差分 == 真实奖励差分（基线 β·log Z 对消）。 *)
Theorem pa1_dpo_reward_relative_exact : forall s_w s_l : S,
  real_eq
    (real_plus
       (real_dpo_reward_explicit S beta pi_ref pi_ref_pos
          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
             Z_align Z_align_pos) s_w)
       (real_opp
          (real_dpo_reward_explicit S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                Z_align Z_align_pos) s_l)))
    (real_plus (reward s_w) (real_opp (reward s_l))).
Proof.
  intros s_w s_l.
  pose proof (S08_RealMainlineDPO.real_dpo_reward_recovers_up_to_baseline
                S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos
                s_w) as Hw.
  pose proof (S08_RealMainlineDPO.real_dpo_reward_recovers_up_to_baseline
                S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos
                s_l) as Hl.
  set (M := real_mult beta (real_log Z_align Z_align_pos)) in *.
  set (uw := real_dpo_reward_explicit S beta pi_ref pi_ref_pos
               (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
               (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                  Z_align Z_align_pos) s_w) in *.
  set (ul := real_dpo_reward_explicit S beta pi_ref pi_ref_pos
               (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
               (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                  Z_align Z_align_pos) s_l) in *.
  (* Hw : uw == r_w − M；Hl : ul == r_l − M *)
  apply (real_eq_trans _
    (real_plus (real_plus (reward s_w) (real_opp M))
               (real_opp (real_plus (reward s_l) (real_opp M)))) _).
  - apply (RealSetoid.real_eq_plus_compat uw
             (real_opp ul)
             (real_plus (reward s_w) (real_opp M))
             (real_opp (real_plus (reward s_l) (real_opp M)))
             Hw (pa1_opp_eq_compat ul
                   (real_plus (reward s_l) (real_opp M)) Hl)).
  - (* (r_w − M) + opp(r_l − M) == r_w − r_l：基线 M 对消 *)
    apply (real_eq_trans _
      (real_plus (real_plus (reward s_w) (real_opp M))
                 (real_plus (real_opp (reward s_l)) (real_opp (real_opp M)))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (reward s_w) (real_opp M))
               (real_opp (real_plus (reward s_l) (real_opp M)))
               (real_plus (reward s_w) (real_opp M))
               (real_plus (real_opp (reward s_l)) (real_opp (real_opp M)))
               (real_eq_refl (real_plus (reward s_w) (real_opp M)))
               (real_opp_plus (reward s_l) (real_opp M))).
    + apply (real_eq_trans _
        (real_plus (real_plus (real_plus (reward s_w) (real_opp M))
                              (real_opp (reward s_l)))
                   (real_opp (real_opp M))) _).
      * apply real_plus_assoc.
      * (* ((r_w − M) + opp r_l) + opp(opp M) == r_w + opp r_l *)
        apply (real_eq_trans _
          (real_plus (real_plus (reward s_w)
                                (real_plus (real_opp (reward s_l)) (real_opp M)))
                     (real_opp (real_opp M))) _).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_plus (real_plus (reward s_w) (real_opp M))
                               (real_opp (reward s_l)))
                    (real_opp (real_opp M))
                    (real_plus (reward s_w)
                               (real_plus (real_opp (reward s_l)) (real_opp M)))
                    (real_opp (real_opp M))
                    (real_eq_trans _
                       (real_plus (reward s_w)
                                  (real_plus (real_opp M) (real_opp (reward s_l)))) _
                       (real_eq_sym _ _
                          (real_plus_assoc (reward s_w) (real_opp M)
                             (real_opp (reward s_l))))
                       (RealSetoid.real_eq_plus_compat (reward s_w)
                          (real_plus (real_opp M) (real_opp (reward s_l)))
                          (reward s_w)
                          (real_plus (real_opp (reward s_l)) (real_opp M))
                          (real_eq_refl (reward s_w))
                          (real_plus_comm (real_opp M) (real_opp (reward s_l)))))
                    (real_eq_refl (real_opp (real_opp M)))).
        -- (* r_w + (opp r_l − M) + opp(opp M) == r_w + opp r_l *)
           apply (real_eq_trans _
             (real_plus (reward s_w)
                        (real_plus (real_opp (reward s_l))
                                   (real_plus (real_opp M)
                                              (real_opp (real_opp M))))) _).
           ++ apply (real_eq_trans _
                (real_plus (reward s_w)
                           (real_plus (real_plus (real_opp (reward s_l))
                                                 (real_opp M))
                                      (real_opp (real_opp M)))) _).
                ** apply (real_eq_sym _ _
                       (real_plus_assoc (reward s_w)
                          (real_plus (real_opp (reward s_l)) (real_opp M))
                          (real_opp (real_opp M)))).
                ** apply (RealSetoid.real_eq_plus_compat (reward s_w)
                             (real_plus (real_plus (real_opp (reward s_l))
                                                   (real_opp M))
                                        (real_opp (real_opp M)))
                             (reward s_w)
                             (real_plus (real_opp (reward s_l))
                                        (real_plus (real_opp M)
                                                   (real_opp (real_opp M))))
                             (real_eq_refl (reward s_w))
                             (real_eq_sym _ _
                                (real_plus_assoc (real_opp (reward s_l))
                                   (real_opp M) (real_opp (real_opp M))))).
           ++ apply (real_eq_trans _
                     (real_plus (real_plus (reward s_w) (real_opp (reward s_l)))
                                (real_plus (real_opp M) (real_opp (real_opp M)))) _).
                ** apply real_plus_assoc.
                ** apply (real_eq_trans _
                            (real_plus (real_plus (reward s_w) (real_opp (reward s_l)))
                                       real_zero) _
                            (RealSetoid.real_eq_plus_compat
                               (real_plus (reward s_w) (real_opp (reward s_l)))
                               (real_plus (real_opp M) (real_opp (real_opp M)))
                               (real_plus (reward s_w) (real_opp (reward s_l)))
                               real_zero
                               (real_eq_refl
                                  (real_plus (reward s_w) (real_opp (reward s_l))))
                               (real_plus_opp (real_opp M)))
                            (real_plus_zero
                               (real_plus (reward s_w) (real_opp (reward s_l))))).
Qed.

End PA1Dpo.

(* ############ 验收：Print Assumptions（G4 口径） ############ *)
Print Assumptions pa1_opp_eq_compat.
Print Assumptions pa1_grpo_unit_moment_pop.
Print Assumptions pa1_raw_second_moment_decomp.
Print Assumptions pa1_dpo_reward_relative_exact.
