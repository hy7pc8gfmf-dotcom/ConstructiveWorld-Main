(* ==========================================================================)
   UpReqMinUniqueTight.v —— FEP 规范分解、最小自由能 Boltzmann 刻画与自由能
   等式唯一性/紧性族
   使命：本件形式化三段。其一，FEP 规范形的 KL 分解恒等式：
     real_kl_decomp_full_canon 及其分划版本 real_kl_decomp_full_canon_partition
     （UpReqRealFEP 语境束在规范实例上的逐字材料化）。其二，定理 4.4
     min_free_energy 的 Real 层序档组装（逐 eps 档）：
     min_free_energy_is_boltzmann_eps 及其配分形
     min_free_energy_is_boltzmann_eps_partition、min_free_energy_close_eps
     （Boltzmann 分布最小化自由能的最强逐 eps 可达形态）。其三，自由能等式的
     唯一性与紧性：切点等式 t15_tangent_eq、t15_fe_eq_kl_zero、显式唯一性
     t15_fe_eq_unique_explicit / t15_fe_eq_unique_bool、严格肢
     t15_fe_strict_of_kl_pos、发散族 t15_fe_strict_divergence_le / _or / _bool
     与 t15_free_energy_min_unique。
   依赖：S01_BaseRing 至 S15_TailFEPUp 基座链（十五件顺序直调）、UpReqRealFEP、
     G07_KLWall、UpReqKLSTangent、G08_Gibbs；Stdlib List。
   对标：变分原理中自由能极小元的唯一性与 KL 紧性（Boltzmann 分布的极小性刻画）。
   构造性：全件 Qed 闭合、零承认词面、零公理；语句面以 Set 层承载（序谓词与
     等词为 Set 值，零 Prop 泄露）；逐 eps 档零新假设位。
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
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 主件：real_kl_decomp_full_canon                                   *)
(*   S08 参数 real_kl_decomp_full 的正典化消解形：结论面与 S08 参数位逐字    *)
(*   同构（real_eq (F p) (F p_b + D·Σ kl_term)）；节接口按消解后全参   *)
(*   显式升参（含 rfep 版诚实增量 linear），残留前提 Hnormb 照单升参。 *)
(*   证明 = rfep_real_kl_decomp_full 部分应用显式应用（一步 exact）。     *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos         p Hp Hnormp Hnormb.
  exact (rfep_real_kl_decomp_full           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos           p Hp Hnormp Hnormb).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：real_kl_decomp_full_canon_partition（前提消解小链版）        *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart                  *)
(*   （Σ exp(−e/D) ≡ Z，物理配分函数清单），经 rfep_boltzmann_        *)
(*   normalized_real 一步消解补齐 Hnormb，再显式应用 rfep 主件。           *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon_partition :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (fun s : S => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
          Z_align_r ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos         p Hp Hnormp Hpart.
  apply (rfep_real_kl_decomp_full           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos           p Hp Hnormp).
  exact (rfep_boltzmann_normalized_real           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_linear           real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart).
Qed.

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
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 件 0：定义件（ELBO/evidence 的 Real 层具名形）                       *)
(*   ELBO(q) := real_opp (F q)；evidence := real_opp (F p_b)。          *)
(*   对位 S04 L4563 elbo / L4565 evidence（Set 层 opp 自由能抽象）。     *)
(* ---------------------------------------------------------- *)

Definition real_elbo (S : Type) (real_sum_over_S : (S -> Real) -> Real)
  (real_base_loss : S -> Real) (D : Real)
  (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)) : Real :=
  real_opp (real_free_energy S real_sum_over_S real_base_loss D q Hq).

Definition real_evidence (S : Type) (real_sum_over_S : (S -> Real) -> Real)
  (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
  (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r) : Real :=
  real_opp
    (real_free_energy S real_sum_over_S real_base_loss D
       (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r
          Z_align_r_pos)).

(* 桥引理（reflexivity 级）：定义展开面，供下游对位 S04 Set 术语 *)
Lemma real_elbo_def :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real)
    (real_base_loss : S -> Real) (D : Real)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_opp (real_free_energy S real_sum_over_S real_base_loss D q Hq)).
Proof.
  intros S real_sum_over_S real_base_loss D q Hq.
  unfold real_elbo.
  exact (real_eq_refl
           (real_opp (real_free_energy S real_sum_over_S real_base_loss D q Hq))).
Qed.

Lemma real_evidence_def :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real)
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r),
  real_eq (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
          (real_opp
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r
                   Z_align_r_pos))).
Proof.
  intros S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos.
  unfold real_evidence.
  exact (real_eq_refl
           (real_opp
              (real_free_energy S real_sum_over_S real_base_loss D
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r
                    Z_align_r_pos)))).
Qed.

(* ---------------------------------------------------------- *)
(* 件 1：等值核 real_evidence_kl_decomp（S04 L4586 的 Real 对位）       *)
(*   evidence ≡ ELBO(q) + D·Σ kl_term(q, p_b)（real_eq 载体）。         *)
(*   组装：rfep_rlhf_free_energy_kl（任意 π* 版，π* := p_b 实例）给      *)
(*   F 形分解，取负代数链桥到 ELBO/evidence 术语。                       *)
(* ---------------------------------------------------------- *)

Lemma real_evidence_kl_decomp :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq
    (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
    (real_plus
       (real_elbo S real_sum_over_S real_base_loss D q Hq)
       (real_mult D
          (real_sum_over_S
             (fun s : S => real_kl_term (q s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hq s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (KLsum := real_sum_over_S (fun s : S => real_kl_term (q s) (pb s) (Hq s) (pbpos s))).
  set (Fq := real_free_energy S real_sum_over_S real_base_loss D q Hq).
  set (Fb := real_free_energy S real_sum_over_S real_base_loss D pb pbpos).
  (* 第 1 腿：rlhf 任意 π* 版分解件（π* := p_b 实例，对齐取逐点自反） *)
  assert (Hrlhf : real_eq Fq (real_plus Fb (real_mult D KLsum))).
  { exact (rfep_rlhf_free_energy_kl
             S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
             real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
             pb pbpos
             (fun s : S => real_eq_refl (pb s))
             q Hq Hnormq Hnormb). }
  (* 第 2 腿：取负代数链（F 形 ↝ ELBO/evidence 术语桥） *)
  unfold real_evidence, real_elbo.
  set (DK := real_mult D KLsum).
  (* 桥：opp Fq ≡ opp Fb + opp DK *)
  assert (Hbridge : real_eq (real_opp Fq) (real_plus (real_opp Fb) (real_opp DK))).
  { apply (real_eq_trans (real_opp Fq) (real_opp (real_plus Fb DK))
                         (real_plus (real_opp Fb) (real_opp DK))).
    - exact (RealSetoid.real_eq_opp_compat Fq (real_plus Fb DK) Hrlhf).
    - exact (real_opp_plus Fb DK). }
  (* 目标：opp Fb ≡ opp Fq + DK（四步环链） *)
  assert (Hdk0 : real_eq (real_plus (real_opp DK) DK) real_zero).
  { apply (real_eq_trans (real_plus (real_opp DK) DK)
                         (real_plus DK (real_opp DK)) real_zero).
    - exact (real_plus_comm (real_opp DK) DK).
    - exact (real_plus_opp DK). }
  apply (real_eq_trans (real_opp Fb)
                       (real_plus (real_opp Fb) (real_plus (real_opp DK) DK))
                       (real_plus (real_opp Fq) DK)).
  - (* opp Fb ≡ opp Fb + (opp DK + DK)：去零腿 + 兼容腿 *)
    apply (real_eq_trans (real_opp Fb) (real_plus (real_opp Fb) real_zero)
                         (real_plus (real_opp Fb) (real_plus (real_opp DK) DK))).
    + exact (real_eq_sym (real_plus (real_opp Fb) real_zero) (real_opp Fb)
                         (real_plus_zero (real_opp Fb))).
    + exact (RealSetoid.real_eq_plus_compat (real_opp Fb) real_zero
               (real_opp Fb) (real_plus (real_opp DK) DK)
               (real_eq_refl (real_opp Fb)) (real_eq_sym _ _ Hdk0)).
  - (* 结合重排后沿桥运输 *)
    apply (real_eq_trans (real_plus (real_opp Fb) (real_plus (real_opp DK) DK))
                         (real_plus (real_plus (real_opp Fb) (real_opp DK)) DK)
                         (real_plus (real_opp Fq) DK)).
    + exact (real_plus_assoc (real_opp Fb) (real_opp DK) DK).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus (real_opp Fb) (real_opp DK)) DK
               (real_opp Fq) DK
               (real_eq_sym _ _ Hbridge) (real_eq_refl DK)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2（通用逐 eps 完成机，组装链第 3+4 步，序代数纯拼装）              *)
(*   0 < D ∧ 0 < eps ∧ evidence ≡ ELBO + D·KL ∧ 0 ≤ KL + eps ⟹         *)
(*   ELBO ≤ evidence + D·eps。                                          *)
(*   证明：0 ≤ KL+eps 经 D>0 放缩得 0 ≤ D·KL + D·eps；再把              *)
(*   evidence+D·eps 沿等值核运输到 ELBO+D·(KL+eps)，加法保序后去零项。   *)
(* ---------------------------------------------------------- *)

Lemma elbo_lower_bound_close_eps :
  forall (D KLsum Elbo Evidence eps : Real),
  real_lt real_zero D ->
  real_lt real_zero eps ->
  real_eq Evidence (real_plus Elbo (real_mult D KLsum)) ->
  real_le real_zero (real_plus KLsum eps) ->
  real_le Elbo (real_plus Evidence (real_mult D eps)).
Proof.
  intros D KLsum Elbo Evidence eps D_pos Heps Hdec Hgibbs.
  (* 第 3 步：D>0 消去（lt 先过弱化桥，S09 real_r_pow_nonneg 同惯形） *)
  assert (Hdle : real_le real_zero D).
  { apply (RealSetoid.real_lt_le_iff_req real_zero D). left. exact D_pos. }
  assert (Hm0 : real_le (real_mult D real_zero)
                        (real_mult D (real_plus KLsum eps))).
  { exact (real_le_mult_compat_r D real_zero (real_plus KLsum eps)
             Hdle Hgibbs). }
  assert (Hm1 : real_le real_zero (real_mult D (real_plus KLsum eps))).
  { exact (RealSetoid.real_le_id_l real_zero (real_mult D real_zero)
             (real_mult D (real_plus KLsum eps))
             (real_eq_sym (real_mult D real_zero) real_zero
                (real_mult_zero D)) Hm0). }
  assert (Hscale : real_le real_zero
                     (real_plus (real_mult D KLsum) (real_mult D eps))).
  { exact (RealSetoid.real_le_id_r real_zero
             (real_mult D (real_plus KLsum eps))
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_distrib D KLsum eps) Hm1). }
  (* 第 4 步：逐 eps 完成 *)
  apply (RealSetoid.real_le_id_r Elbo
           (real_plus Elbo (real_plus (real_mult D KLsum) (real_mult D eps)))
           (real_plus Evidence (real_mult D eps))).
  - (* 等值面：ELBO+D·(KL+eps) ≡ evidence+D·eps（沿等值核两步运输） *)
    apply (real_eq_trans
             (real_plus Elbo (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_plus (real_plus Elbo (real_mult D KLsum)) (real_mult D eps))
             (real_plus Evidence (real_mult D eps))).
    + exact (real_plus_assoc Elbo (real_mult D KLsum) (real_mult D eps)).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus Elbo (real_mult D KLsum)) (real_mult D eps)
               Evidence (real_mult D eps)
               (real_eq_sym Evidence (real_plus Elbo (real_mult D KLsum)) Hdec)
               (real_eq_refl (real_mult D eps))).
  - (* 序面：ELBO ≤ ELBO+(D·KL+D·eps)（自反 + 加法保序 + 去零） *)
    apply (RealSetoid.real_le_id_l Elbo (real_plus Elbo real_zero)
             (real_plus Elbo (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_eq_sym (real_plus Elbo real_zero) Elbo
                (real_plus_zero Elbo))).
    exact (real_le_plus_compat Elbo Elbo real_zero
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_le_refl Elbo) Hscale).
Qed.

(* ---------------------------------------------------------- *)
(* 主件：real_elbo_lower_bound_eps（定理 4.7 Real 层第三档）             *)
(*   载体 = list X 具体状态空间（T7 同型实例化）；前提全显式：           *)
(*   Hnormq（Σq ≡ 1）+ Hnormb（Σp_b ≡ 1，由使用方或分件供给）。          *)
(*   组装：件 1 等值核（rlhf 件实例化）+ 件 2 非负腿（S08 L490）         *)
(*   + 件 3 完成机。                                                     *)
(* ---------------------------------------------------------- *)

Theorem real_elbo_lower_bound_eps :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q l) real_one ->
  real_eq
    (real_list_sum X
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       l) real_one ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_elbo X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D q Hq)
    (real_plus
       (real_evidence X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq
         Hnormb eps Heps.
  apply (elbo_lower_bound_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (q s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hq s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_elbo X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D q Hq)
           (real_evidence X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D D_pos Z_align_r Z_align_r_pos)
           eps D_pos Heps).
  - (* 件 1：等值核（rlhf 任意 π* 件实例化到 list 载体） *)
    exact (real_evidence_kl_decomp X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq
             Hnormq Hnormb).
  - (* 件 2：实 Gibbs 不等式逐 eps 形（S08 L490 在盘） *)
    exact (real_gibbs_inequality_eps X l q
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hq
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormq Hnormb eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：real_elbo_lower_bound_eps_partition（前提消解小链版）           *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart                    *)
(*   （Σ exp(−e/D) ≡ Z，物理配分函数记录项），经                           *)
(*   rfep_boltzmann_normalized_real（UpReqRealFEP L331）一步消解补齐     *)
(*   Hnormb，与 T7/X2 分件同型。                                         *)
(* ---------------------------------------------------------- *)

Theorem real_elbo_lower_bound_eps_partition :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q l) real_one ->
  real_eq
    (real_list_sum X
       (fun s : X =>
          real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
       l) Z_align_r ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_elbo X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D q Hq)
    (real_plus
       (real_evidence X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq
         Hpart eps Heps.
  assert (Hnormb : real_eq
                     (real_list_sum X
                        (real_boltzmann_dist_r X real_base_loss D D_pos
                           Z_align_r Z_align_r_pos) l) real_one).
  { exact (rfep_boltzmann_normalized_real X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart). }
  apply (elbo_lower_bound_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (q s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hq s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_elbo X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D q Hq)
           (real_evidence X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D D_pos Z_align_r Z_align_r_pos)
           eps D_pos Heps).
  - exact (real_evidence_kl_decomp X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq
             Hnormq Hnormb).
  - exact (real_gibbs_inequality_eps X l q
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hq
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormq Hnormb eps Heps).
Qed.

From Stdlib Require Import List.
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
Require Import UpReqRealFEP.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.
Import ListNotations.

(* ---------------------------------------------------------- *)
(* 件 0：切点式谓词（显式前提形的逐点结论面，Set 层）                    *)
(*   对位 G08 gibbe2_kl_zero_tangent_eq 的逐点结论：                    *)

(* ---------------------------------------------------------- *)

Definition t12_tangent_eq
  (S : Type) (real_base_loss : S -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (Z_align_r : Real)
  (Z_align_r_pos : real_lt real_zero Z_align_r)
  (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
  (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (q s) (Hq s)))
       (real_mult_positive
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos (q s) (Hq s))
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos_pos (q s) (Hq s))))
    (real_plus
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (q s) (Hq s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：紧致核——紧致假设 ⟹ KL ≡ 0（抽象载体）                          *)
(*   ⟹ ELBO ≡ ELBO + D·KL ⟹ 加法消去 ⟹ D·KL ≡ 0 ⟹ D>0 右因子消去      *)
(*   ⟹ KL ≡ 0。                                                         *)
(* ---------------------------------------------------------- *)

Lemma t12_tight_kl_zero :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  real_eq (real_sum_over_S
             (fun s : S => real_kl_term (q s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hq s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
          real_zero.
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htight.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (KLsum := real_sum_over_S (fun s : S => real_kl_term (q s) (pb s) (Hq s) (pbpos s))).
  assert (Hdec : real_eq (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))).
  { exact (real_evidence_kl_decomp S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb). }
  (* 第 2 步：紧致假设沿等值核运输：ELBO ≡ ELBO + D·KL *)
  assert (Hloop : real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                          (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                     (real_mult D KLsum))).
  { exact (real_eq_trans (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))
                         Htight Hdec). }
  (* 第 3 步：加法消去：D·KL ≡ 0（S08 real_eq_plus_cancel_l） *)
  assert (Hdk : real_eq (real_mult D KLsum) real_zero).
  { apply (real_eq_plus_cancel_l (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                 (real_mult D KLsum) real_zero).
    apply (real_eq_trans
             (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                        (real_mult D KLsum))
             (real_elbo S real_sum_over_S real_base_loss D q Hq)
             (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq) real_zero)).
    - exact (real_eq_sym (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq)
                                    (real_mult D KLsum))
                         Hloop).
    - exact (real_eq_sym (real_plus (real_elbo S real_sum_over_S real_base_loss D q Hq) real_zero)
                         (real_elbo S real_sum_over_S real_base_loss D q Hq)
                         (real_plus_zero (real_elbo S real_sum_over_S real_base_loss D q Hq))). }
  (* 第 4 步：D>0 消去：KL ≡ 0（comm 两次 + S08 右因子消去） *)
  apply (real_eq_mult_cancel_r KLsum real_zero D D_pos).
  apply (real_eq_trans (real_mult KLsum D) real_zero (real_mult real_zero D)).
  - apply (real_eq_trans (real_mult KLsum D) (real_mult D KLsum) real_zero).
    + exact (real_mult_comm KLsum D).
    + exact Hdk.
  - exact (real_eq_trans real_zero (real_mult D real_zero) (real_mult real_zero D)
             (real_eq_sym (real_mult D real_zero) real_zero (real_mult_zero D))
             (real_mult_comm D real_zero)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：正向半边（抽象载体，显式前提形）——定理 4.8 的 ⟹ 半边           *)
(*   紧致（ELBO ≡ evidence）+ 显式接口前提（KL≡0 ⟹ 逐点切点式）         *)
(*   ⟹ 逐点 q s ≡ p_b s。                                               *)
(*   逐点消去链：切点式 + t1_log_eq_linear_inject（切点⟹一，       *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去 ⟹ q s ≡ p_b s。        *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_forward :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (* 显式接口前提位（载体诚实接口）：KL ≡ 0 ⟹ 逐点切点式；
     bool 载体上由件 5 整链消解（整链件直达），零残留。 *)
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (q s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hq s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t12_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq s) ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  forall s : S,
    real_eq (q s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htan0 Htight s.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  (* 第 1 步：紧致核（件 1）：KL ≡ 0 *)
  assert (Hkl0 : real_eq (real_sum_over_S
                            (fun s0 : S => real_kl_term (q s0) (pb s0) (Hq s0) (pbpos s0)))
                         real_zero).
  { exact (t12_tight_kl_zero S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight). }
  (* 第 2 步：切点式 + 「切点⟹一」（无条件消解）⟹ 比值一 *)
  assert (Hu1 : real_eq (real_mult (pb s) (real_inv_pos (q s) (Hq s))) real_one).
  { apply (t1_log_eq_linear_inject (real_mult (pb s) (real_inv_pos (q s) (Hq s)))
             (real_mult_positive (pb s) (real_inv_pos (q s) (Hq s))
                (pbpos s) (real_inv_pos_pos (q s) (Hq s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ q s ≡ p_b s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (q s)
           (real_mult (q s) (real_mult (pb s) (real_inv_pos (q s) (Hq s))))
           (pb s)).
  - apply (real_eq_trans (q s) (real_mult (q s) real_one)
             (real_mult (q s) (real_mult (pb s) (real_inv_pos (q s) (Hq s))))).
    + exact (real_eq_sym (real_mult (q s) real_one) (q s) (real_mult_one (q s))).
    + exact (RealSetoid.real_eq_mult_compat (q s) real_one (q s)
               (real_mult (pb s) (real_inv_pos (q s) (Hq s)))
               (real_eq_refl (q s))
               (real_eq_sym (real_mult (pb s) (real_inv_pos (q s) (Hq s))) real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (q s) (pb s) (Hq s)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3：逆向半边（抽象载体，零接口前提）——定理 4.8 的 ⟸ 半边           *)
(*   逐点 q s ≡ p_b s ⟹ 自由能等（rfep_free_energy_ext_r，仅 ext 接口） *)
(*   ⟹ real_opp 兼容 ⟹ ELBO(q) ≡ evidence。                            *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_backward :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  (forall s : S,
     real_eq (q s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)) ->
  real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros S real_sum_over_S sumf_ext real_base_loss D D_pos Z_align_r Z_align_r_pos         q Hq Hpoint.
  unfold real_elbo, real_evidence.
  apply (RealSetoid.real_eq_opp_compat           (real_free_energy S real_sum_over_S real_base_loss D q Hq)           (real_free_energy S real_sum_over_S real_base_loss D              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))).
  exact (rfep_free_energy_ext_r S real_sum_over_S sumf_ext real_base_loss D q           (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hpoint).
Qed.

(* ---------------------------------------------------------- *)
(* 件 4：组装件（抽象载体，prod 双函数记录——Set 层 And 形，零 Prop）     *)
(*   (紧致 ⟹ 逐点 q≡p_b) × (逐点 q≡p_b ⟹ 紧致)。                       *)
(*   即定理 4.8「当且仅当」的 Real 层可达形（显式前提形）。              *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_eq (real_sum_over_S q) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (q s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hq s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t12_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq s) ->
  prod (real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)
        -> forall s : S,
             real_eq (q s)
                     (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : S,
           real_eq (q s)
                   (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        -> real_eq (real_elbo S real_sum_over_S real_base_loss D q Hq)
                   (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos)).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Htan0.
  split.
  - exact (t12_elbo_tight_forward S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htan0).
  - exact (t12_elbo_tight_backward S real_sum_over_S sumf_ext
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：bool 载体完成——显式接口前提整链消解的正向形                     *)
(*   显式前提位由t1_gibbe2_gibbs_equality_bool 整链消解             *)
(*   （KL≡0 ⟹ 逐点 q≡p_b 直达，注入位由 t1_log_eq_linear_inject          *)
(*   无条件供给）：bool 载体上正向半边零接口前提（除物理前提）。         *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_forward_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D q Hq)
          (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D D_pos Z_align_r Z_align_r_pos) ->
  forall s : bool,
    real_eq (q s)
            (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight s.
  apply (t1_gibbe2_gibbs_equality_bool q           (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq           (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hnormq Hnormb).
  exact (t12_tight_kl_zero bool           (fun f : bool -> Real => real_list_sum bool f [true; false])           (fun (f g : bool -> Real)                (Hfg : forall s : bool, real_eq (f s) (g s)) =>              real_list_sum_ext bool f g [true; false] Hfg)           (fun f g : bool -> Real => real_list_sum_add bool f g [true; false])           (fun (a : Real) (f : bool -> Real) =>              real_list_sum_linear bool a f [true; false])           real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Htight).
Qed.

(* ---------------------------------------------------------- *)
(* 件 6：bool 组装件（prod 双函数记录，零接口前提版）                    *)
(*   定理 4.8 在 gibbe2 样板载体上的全消解形：前提面仅剩                 *)
(*   「q 逐点正 + 双归一化」的显式物理前提。                              *)
(* ---------------------------------------------------------- *)

Theorem t12_elbo_tight_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  prod (real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                  real_base_loss D q Hq)
                (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D D_pos Z_align_r Z_align_r_pos)
        -> forall s : bool,
             real_eq (q s)
                     (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : bool,
           real_eq (q s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        -> real_eq (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D q Hq)
                   (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D D_pos Z_align_r Z_align_r_pos)).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb.
  split.
  - exact (t12_elbo_tight_forward_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             q Hq Hnormq Hnormb).
  - intros Hpoint.
    exact (t12_elbo_tight_backward bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             (fun (f g : bool -> Real)
                  (Hfg : forall s : bool, real_eq (f s) (g s)) =>
                real_list_sum_ext bool f g [true; false] Hfg)
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hpoint).
Qed.

From Stdlib Require Import List.
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
Require Import UpReqRealFEP.
Require Import G07_KLWall.
Import ListNotations.

(* ---------------------------------------------------------- *)
(* 件 1：取负换向跳——F[p_b] < F[q] ⟹ ELBO(q) < evidence                 *)
(*   ELBO(q) = −F[q]，evidence = −F[p_b]（定义展开面）；                 *)
(*   a<b ⟹ −b<−a（S07 real_opp_lt_compat，eps-N 直构）。                 *)
(* ---------------------------------------------------------- *)

Lemma t33_elbo_strict_of_fe_strict :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real)
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
  real_lt (real_free_energy S real_sum_over_S real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy S real_sum_over_S real_base_loss D q Hq) ->
  real_lt (real_elbo S real_sum_over_S real_base_loss D q Hq)
          (real_evidence S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros S real_sum_over_S real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hfs.
  unfold real_elbo, real_evidence.
  exact (real_opp_lt_compat           (real_free_energy S real_sum_over_S real_base_loss D              (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))           (real_free_energy S real_sum_over_S real_base_loss D q Hq)           Hfs).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：严格尾链（list 载体）——KL>0 ⟹ F[p_b] < F[q]                    *)
(*   同链同件重组（五步，D 因子逐字保留）： *)
(*   正典分解 F[q] ≡ F[p_b] + D·KL ⟹ D·KL > 0 ⟹ 加法平移 ⟹              *)
(*   零右端化简 ⟹ 沿分解运输。                                          *)
(* ---------------------------------------------------------- *)

Lemma t33_fe_strict_of_kl_pos :
  forall (X : Type) (L : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q L) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos) L)
          real_one ->
  real_lt real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (q s)
          (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (Hq s)
          (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       L) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D q Hq).
Proof.
  intros X L real_base_loss D D_pos Z_align_r Z_align_r_pos
         q Hq Hnormq Hnormb Hkl.
  set (pb := real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (sumf := fun f : X -> Real => real_list_sum X f L).
  set (KLsum := real_list_sum X (fun s : X => real_kl_term (q s) (pb s) (Hq s) (pbpos s)) L).
  set (Fq := real_free_energy X sumf real_base_loss D q Hq).
  set (Fb := real_free_energy X sumf real_base_loss D pb pbpos).
  (* 第 1 步：正典分解：F[q] ≡ F[p_b] + D·KL *)
  assert (Hdec : real_eq Fq (real_plus Fb (real_mult D KLsum))).
  { exact (real_kl_decomp_full_canon X sumf
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g L Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g L)
             (fun (a : Real) (f : X -> Real) => real_list_sum_linear X a f L)
             real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb). }
  (* 第 2 步：D·KL > 0（D>0 × KL>0） *)
  assert (HdK : real_lt real_zero (real_mult D KLsum)).
  { exact (real_mult_pos_compat D KLsum D_pos Hkl). }
  (* 第 3 步：加法平移：F[p_b] + 0 < F[p_b] + D·KL *)
  assert (Hshift : real_lt (real_plus Fb real_zero) (real_plus Fb (real_mult D KLsum))).
  { exact (real_lt_plus_translate Fb real_zero (real_mult D KLsum) HdK). }
  (* 第 4 步：零右端化简：F[p_b] < F[p_b] + D·KL *)
  assert (Hcore : real_lt Fb (real_plus Fb (real_mult D KLsum))).
  { exact (RealSetoid.real_lt_compat (real_plus Fb real_zero) Fb
             (real_plus Fb (real_mult D KLsum)) (real_plus Fb (real_mult D KLsum))
             (real_plus_zero Fb)
             (real_eq_refl (real_plus Fb (real_mult D KLsum)))
             Hshift). }
  (* 第 5 步：沿分解运输：F[p_b] < F[q] *)
  exact (RealSetoid.real_lt_compat Fb Fb
           (real_plus Fb (real_mult D KLsum)) Fq
           (real_eq_refl Fb)
           (real_eq_sym Fq (real_plus Fb (real_mult D KLsum)) Hdec)
           Hcore).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3：严格入 ELBO 口——KL>0 ⟹ ELBO(q) < evidence                      *)
(*   件 2（F 严格差）+ 件 1（取负换向一跳）。                            *)
(* ---------------------------------------------------------- *)

Lemma t33_elbo_strict_of_kl_pos :
  forall (X : Type) (L : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q L) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos) L)
          real_one ->
  real_lt real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (q s)
          (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (Hq s)
          (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       L) ->
  real_lt (real_elbo X (fun f : X -> Real => real_list_sum X f L) real_base_loss D q Hq)
          (real_evidence X (fun f : X -> Real => real_list_sum X f L) real_base_loss D
             D_pos Z_align_r Z_align_r_pos).
Proof.
  intros X L real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Hkl.
  apply (t33_elbo_strict_of_fe_strict X           (fun f : X -> Real => real_list_sum X f L) real_base_loss D D_pos           Z_align_r Z_align_r_pos q Hq).
  exact (t33_fe_strict_of_kl_pos X L real_base_loss D D_pos Z_align_r Z_align_r_pos           q Hq Hnormq Hnormb Hkl).
Qed.

(* ---------------------------------------------------------- *)
(* 件 4：单向可比版——逐项 q ≤ p_b（Set 层两支弱序）+ s₀ 严格分离         *)
(*   ⟹ G07 klst_kl_sum_strict（p := q 同向显式应用，不得 swap）⟹ 件 3。      *)
(* ---------------------------------------------------------- *)

Theorem t33_elbo_strict_divergence_le :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (forall s : X, real_le (q s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)) ->
  real_lt (q s₀)
    (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀) ->
  real_lt (real_elbo X (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂))
             real_base_loss D q Hq)
          (real_evidence X (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂))
             real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos         q Hq Hnormq Hnormb Hpq Hdiv.
  apply (t33_elbo_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos           Z_align_r Z_align_r_pos q Hq Hnormq Hnormb).
  exact (klst_kl_sum_strict X l₁ s₀ l₂ q           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hpq Hnormq Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：主件（双向 Or 见证版）——显式分歧见证的严格逆否肢                *)
(*   逐项双向可比（诚实接口位，Set 层 Or 承载）+ s₀ 处双向严格分离        *)
(*   Or 见证 ⟹ G07 klst_kl_energy_nonconst ⟹ KL(q‖p_b)>0 ⟹ 件 3         *)
(*   ⟹ ELBO(q) < evidence（严格）。                                      *)
(* ---------------------------------------------------------- *)

Theorem t33_elbo_strict_divergence :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : X -> Real) (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (* 逐项双向可比（诚实接口位：非直觉主义可证，显式见证输入） *)
  (forall s : X,
     Or (real_le (q s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (q s))) ->
  (* s₀ 处显式分歧见证（Set 层 Or 承载，任一方向） *)
  (Or (real_lt (q s₀)
               (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀))
      (real_lt (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀)
               (q s₀))) ->
  real_lt (real_elbo X (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂))
             real_base_loss D q Hq)
          (real_evidence X (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂))
             real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos         q Hq Hnormq Hnormb Hpq Hdiv.
  apply (t33_elbo_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos           Z_align_r Z_align_r_pos q Hq Hnormq Hnormb).
  exact (klst_kl_energy_nonconst X l₁ s₀ l₂ q           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hq           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)           Hpq Hnormq Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 6：bool 载体完成——件 5 在 [true; false] 载体的实例                 *)
(*   （s₀ := true，l₁ := []，l₂ := [false]）。                           *)
(* ---------------------------------------------------------- *)

Theorem t33_elbo_strict_divergence_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  (forall s : bool,
     Or (real_le (q s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (q s))) ->
  (Or (real_lt (q true)
               (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
      (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
               (q true))) ->
  real_lt (real_elbo bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D q Hq)
          (real_evidence bool (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D D_pos Z_align_r Z_align_r_pos).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Hpq Hdiv.
  exact (t33_elbo_strict_divergence bool [] true [false] real_base_loss D D_pos           Z_align_r Z_align_r_pos q Hq Hnormq Hnormb Hpq Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 7：边界组装件（bool 载体，prod 双函数记录——Set 层合取形，零 Prop）  *)
(*   定理 4.8 构造性边界两个合取肢：                                           *)
(*   (a) 肢 = 逐点 q ≡ p_b ⟹ 紧致（ 件 3 同链同件重组：自由能外延 +  *)
(*       real_opp 兼容一跳）；                                            *)

(*   两个合取肢以 prod 双函数记录承载（Set 层合取形，零 Prop 泄露）。          *)
(* ---------------------------------------------------------- *)

Theorem t33_elbo_boundary_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)),
  real_eq (real_list_sum bool q [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  prod ((forall s : bool,
           real_eq (q s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        -> real_eq (real_elbo bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D q Hq)
                   (real_evidence bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D D_pos Z_align_r Z_align_r_pos))
       ((forall s : bool,
           Or (real_le (q s)
                         (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
              (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                       (q s)))
        -> (Or (real_lt (q true)
                        (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
               (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
                        (q true)))
        -> real_lt (real_elbo bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D q Hq)
                   (real_evidence bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D D_pos Z_align_r Z_align_r_pos)).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos q Hq Hnormq Hnormb.
  split.
  - (* (a) 肢：逐点等 ⟹ 紧致（ 件 3 同链：ext + 取负兼容一跳） *)
    intros Hpoint.
    unfold real_elbo, real_evidence.
    apply (RealSetoid.real_eq_opp_compat
             (real_free_energy bool
                (fun f : bool -> Real => real_list_sum bool f [true; false])
                real_base_loss D q Hq)
             (real_free_energy bool
                (fun f : bool -> Real => real_list_sum bool f [true; false])
                real_base_loss D
                (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r
                   Z_align_r_pos))).
    exact (rfep_free_energy_ext_r bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             (fun (f g : bool -> Real)
                  (Hfg : forall s : bool, real_eq (f s) (g s)) =>
                real_list_sum_ext bool f g [true; false] Hfg)
             real_base_loss D q
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             Hq
             (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hpoint).
  - 
    exact (t33_elbo_strict_divergence_bool real_base_loss D D_pos
             Z_align_r Z_align_r_pos q Hq Hnormq Hnormb).
Qed.

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
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 第 0 步：通用逐 eps 完成机（组装链第 3+4 步，序代数纯拼装）          *)
(*   0 < eps ∧ F[p] ≡ F[p_b] + D·KL ∧ 0 ≤ KL + eps ⟹                  *)
(*   F[p_b] ≤ F[p] + D·eps。                                            *)
(*   证明：0 ≤ KL+eps 经 D>0 放缩得 0 ≤ D·KL + D·eps；再把 F[p]+D·eps   *)
(*   沿分解恒等式运输到 F[p_b]+D·(KL+eps)，加法保序后去零项。           *)
(* ---------------------------------------------------------- *)

Lemma min_free_energy_close_eps :
  forall (D KLsum Fp Fb eps : Real),
  real_lt real_zero D ->
  real_lt real_zero eps ->
  real_eq Fp (real_plus Fb (real_mult D KLsum)) ->
  real_le real_zero (real_plus KLsum eps) ->
  real_le Fb (real_plus Fp (real_mult D eps)).
Proof.
  intros D KLsum Fp Fb eps D_pos Heps Hdec Hgibbs.
  (* 第 3 步：D>0 消去（先 lt→le 弱化桥，S09 real_r_pow_nonneg 同惯形） *)
  assert (Hdle : real_le real_zero D).
  { apply (RealSetoid.real_lt_le_iff_req real_zero D). left. exact D_pos. }
  assert (Hm0 : real_le (real_mult D real_zero)
                        (real_mult D (real_plus KLsum eps))).
  { exact (real_le_mult_compat_r D real_zero (real_plus KLsum eps)
             Hdle Hgibbs). }
  assert (Hm1 : real_le real_zero (real_mult D (real_plus KLsum eps))).
  { exact (RealSetoid.real_le_id_l real_zero (real_mult D real_zero)
             (real_mult D (real_plus KLsum eps))
             (real_eq_sym (real_mult D real_zero) real_zero
                (real_mult_zero D)) Hm0). }
  assert (Hscale : real_le real_zero
                     (real_plus (real_mult D KLsum) (real_mult D eps))).
  { exact (RealSetoid.real_le_id_r real_zero
             (real_mult D (real_plus KLsum eps))
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_distrib D KLsum eps) Hm1). }
  (* 第 4 步：逐 eps 完成 *)
  apply (RealSetoid.real_le_id_r Fb
           (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
           (real_plus Fp (real_mult D eps))).
  - (* 等值面：F[p_b]+D·(KL+eps) ≡ F[p]+D·eps（沿分解恒等式两步运输） *)
    apply (real_eq_trans
             (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_plus (real_plus Fb (real_mult D KLsum)) (real_mult D eps))
             (real_plus Fp (real_mult D eps))).
    + exact (real_plus_assoc Fb (real_mult D KLsum) (real_mult D eps)).
    + exact (real_eq_sym (real_plus Fp (real_mult D eps))
               (real_plus (real_plus Fb (real_mult D KLsum))
                          (real_mult D eps))
               (RealSetoid.real_eq_plus_compat Fp (real_mult D eps)
                  (real_plus Fb (real_mult D KLsum)) (real_mult D eps)
                  Hdec (real_eq_refl (real_mult D eps)))).
  - (* 序面：F[p_b] ≤ F[p_b]+(D·KL+D·eps)（自反 + 加法保序 + 去零） *)
    apply (RealSetoid.real_le_id_l Fb (real_plus Fb real_zero)
             (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_eq_sym (real_plus Fb real_zero) Fb
                (real_plus_zero Fb))).
    exact (real_le_plus_compat Fb Fb real_zero
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_le_refl Fb) Hscale).
Qed.

(* ---------------------------------------------------------- *)
(* 主件：min_free_energy_is_boltzmann_eps（定理 4.4 Real 层第三档）      *)
(*   载体 = list X 具体状态空间；前提全显式：                           *)
(*     Hnormp（Σp ≡ 1）+ Hnormb（Σp_b ≡ 1，由使用方或分件供给）。        *)
(*   组装：第 1 步引入 real_kl_decomp_full_canon（X2 正典件，sumf 实例化 *)
(*   到 real_list_sum 求和引理组），第 2 步引入 real_gibbs_inequality_eps。 *)
(* ---------------------------------------------------------- *)

Theorem min_free_energy_is_boltzmann_eps :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p l) real_one ->
  real_eq
    (real_list_sum X
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       l) real_one ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
          Z_align_r_pos))
    (real_plus
       (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D p Hp)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp
         Hnormb eps Heps.
  apply (min_free_energy_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hp s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D p Hp)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D
              (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos)
              (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos))
           eps D_pos Heps).
  - (* 第 1 步：完整分解（X2 正典件实例化到 list 载体） *)
    exact (real_kl_decomp_full_canon X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp
             Hnormp Hnormb).
  - (* 第 2 步：实 Gibbs 不等式逐 eps 形（S08 L490 在盘） *)
    exact (real_gibbs_inequality_eps X l p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hp
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormp Hnormb eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：min_free_energy_is_boltzmann_eps_partition（前提消解小链版）    *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart（Σ exp(−e/D) ≡ Z） *)
(*   ——Hnormb 经 rfep_boltzmann_normalized_real（UpReqRealFEP L331）     *)
(*   一步消解，与 X2 分件同型；Gibbs 肢照常使用。                       *)
(* ---------------------------------------------------------- *)

Theorem min_free_energy_is_boltzmann_eps_partition :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p l) real_one ->
  real_eq
    (real_list_sum X
       (fun s : X =>
          real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
       l) Z_align_r ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
          Z_align_r_pos))
    (real_plus
       (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D p Hp)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp
         Hpart eps Heps.
  assert (Hnormb : real_eq
                     (real_list_sum X
                        (real_boltzmann_dist_r X real_base_loss D D_pos
                           Z_align_r Z_align_r_pos) l) real_one).
  { exact (rfep_boltzmann_normalized_real X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart). }
  apply (min_free_energy_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hp s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D p Hp)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D
              (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos)
              (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos))
           eps D_pos Heps).
  - exact (real_kl_decomp_full_canon_partition X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp
             Hnormp Hpart).
  - exact (real_gibbs_inequality_eps X l p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hp
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormp Hnormb eps Heps).
Qed.

From Stdlib Require Import List.
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
Require Import UpReqRealFEP.
Require Import G07_KLWall.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.
Import ListNotations.

(* ---------------------------------------------------------- *)
(* 件 0：切点式谓词（显式前提形的逐点结论面，Set 层）                    *)
(*   对位 G08 gibbe2 注入位的逐点结论：                                 *)

(* ---------------------------------------------------------- *)

Definition t15_tangent_eq
  (S : Type) (real_base_loss : S -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (Z_align_r : Real)
  (Z_align_r_pos : real_lt real_zero Z_align_r)
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (p s) (Hp s)))
       (real_mult_positive
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos (p s) (Hp s))
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos_pos (p s) (Hp s))))
    (real_plus
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (p s) (Hp s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：等值核——F[p] ≡ F[p_b] ⟹ KL ≡ 0（抽象载体）                    *)
(*   链：Feq 沿正典分解件运输 ⟹ F[p_b] ≡ F[p_b] + D·KL ⟹ 加法消去     *)
(*   ⟹ D·KL ≡ 0 ⟹ D>0 右因子消去 ⟹ KL ≡ 0。                           *)
(* ---------------------------------------------------------- *)

Lemma t15_fe_eq_kl_zero :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_free_energy S real_sum_over_S real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  real_eq (real_sum_over_S
             (fun s : S => real_kl_term (p s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
          real_zero.
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Feq.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (KLsum := real_sum_over_S (fun s : S => real_kl_term (p s) (pb s) (Hp s) (pbpos s))).
  set (Fp := real_free_energy S real_sum_over_S real_base_loss D p Hp).
  set (Fb := real_free_energy S real_sum_over_S real_base_loss D pb pbpos).
  (* 第 1 步：正典分解（X2 real_kl_decomp_full_canon）：F[p] ≡ F[p_b] + D·KL *)
  assert (Hdec : real_eq Fp (real_plus Fb (real_mult D KLsum))).
  { exact (real_kl_decomp_full_canon S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb). }
  (* 第 2 步：Feq 沿分解运输：F[p_b] ≡ F[p_b] + D·KL *)
  assert (Hloop : real_eq Fb (real_plus Fb (real_mult D KLsum))).
  { exact (real_eq_trans Fb Fp (real_plus Fb (real_mult D KLsum))
             (real_eq_sym Fp Fb Feq) Hdec). }
  (* 第 3 步：加法消去：D·KL ≡ 0（S08 real_eq_plus_cancel_l） *)
  assert (Hdk : real_eq (real_mult D KLsum) real_zero).
  { apply (real_eq_plus_cancel_l Fb (real_mult D KLsum) real_zero).
    apply (real_eq_trans (real_plus Fb (real_mult D KLsum)) Fb (real_plus Fb real_zero)).
    - exact (real_eq_sym Fb (real_plus Fb (real_mult D KLsum)) Hloop).
    - exact (real_eq_sym (real_plus Fb real_zero) Fb (real_plus_zero Fb)). }
  (* 第 4 步：D>0 消去：KL ≡ 0（comm 两跳 + S08 右因子消去） *)
  apply (real_eq_mult_cancel_r KLsum real_zero D D_pos).
  apply (real_eq_trans (real_mult KLsum D) real_zero (real_mult real_zero D)).
  - apply (real_eq_trans (real_mult KLsum D) (real_mult D KLsum) real_zero).
    + exact (real_mult_comm KLsum D).
    + exact Hdk.
  - exact (real_eq_trans real_zero (real_mult D real_zero) (real_mult real_zero D)
             (real_eq_sym (real_mult D real_zero) real_zero (real_mult_zero D))
             (real_mult_comm D real_zero)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：可达形 (a)——gibbe2 式显式前提形（抽象载体）                    *)
(*   F[p] ≡ F[p_b]（⟹ KL ≡ 0，件 1）+ 显式接口前提（KL≡0 ⟹ 逐点切点式）*)
(*   ⟹ 逐点 p s ≡ p_b s。                                               *)
(*   逐点消去链：切点式 + t1_log_eq_linear_inject（切点⟹一，       *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去 ⟹ p s ≡ p_b s。        *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_eq_unique_explicit :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (* 显式接口前提位（载体诚实接口）：KL ≡ 0 ⟹ 逐点切点式；
     bool 样板载体上由件 3 整链消解（整链件直达），零残留。 *)
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (p s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hp s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t15_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp s) ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_free_energy S real_sum_over_S real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  forall s : S,
    real_eq (p s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Htan0 Feq s.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  (* 第 1 步：等值核（件 1）：KL ≡ 0 *)
  assert (Hkl0 : real_eq (real_sum_over_S
                            (fun s0 : S => real_kl_term (p s0) (pb s0) (Hp s0) (pbpos s0)))
                         real_zero).
  { exact (t15_fe_eq_kl_zero S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq). }
  (* 第 2 步：切点式 + 「切点⟹一」（无条件消解）⟹ 比值一 *)
  assert (Hu1 : real_eq (real_mult (pb s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (t1_log_eq_linear_inject (real_mult (pb s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (pb s) (real_inv_pos (p s) (Hp s))
                (pbpos s) (real_inv_pos_pos (p s) (Hp s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ p s ≡ p_b s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (pb s) (real_inv_pos (p s) (Hp s))))
           (pb s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (pb s) (real_inv_pos (p s) (Hp s))))).
    + exact (real_eq_sym (real_mult (p s) real_one) (p s) (real_mult_one (p s))).
    + exact (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (pb s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (pb s) (real_inv_pos (p s) (Hp s))) real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (pb s) (Hp s)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3：可达形 (a) bool 完成——显式接口前提整链消解形                   *)
(*   显式前提位由t1_gibbe2_gibbs_equality_bool 整链消解            *)
(*   （KL≡0 ⟹ 逐点 p≡p_b 直达，注入位由 t1_log_eq_linear_inject        *)
(*   无条件供给）：gibbe2 样板载体上 (a) 形零接口前提（除物理前提）。    *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_eq_unique_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  real_eq (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D p Hp)
          (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  forall s : bool,
    real_eq (p s)
            (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq s.
  apply (t1_gibbe2_gibbs_equality_bool p
           (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hnormp Hnormb).
  exact (t15_fe_eq_kl_zero bool
           (fun f : bool -> Real => real_list_sum bool f [true; false])
           (fun (f g : bool -> Real)
                (Hfg : forall s : bool, real_eq (f s) (g s)) =>
              real_list_sum_ext bool f g [true; false] Hfg)
           (fun f g : bool -> Real => real_list_sum_add bool f g [true; false])
           (fun (a : Real) (f : bool -> Real) =>
              real_list_sum_linear bool a f [true; false])
           real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq).
Qed.

(* ---------------------------------------------------------- *)
(* 件 4：严格尾链——KL > 0 ⟹ F[p_b] < F[p]（list 载体，real_lt）         *)
(*   链：D·KL > 0（real_mult_pos_compat）⟹ 加法平移                    *)
(*   （real_lt_plus_translate）⟹ real_lt_compat 运输两跳 ⟹ 严格差。     *)
(*   F[p]−F[p_b] 核算由正典分解逐字保留（D 因子不吸收）。               *)
(* ---------------------------------------------------------- *)

Lemma t15_fe_strict_of_kl_pos :
  forall (X : Type) (L : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p L) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos) L)
          real_one ->
  real_lt real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s)
          (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (Hp s)
          (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       L) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D p Hp).
Proof.
  intros X L real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hkl.
  set (pb := real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (sumf := fun f : X -> Real => real_list_sum X f L).
  set (KLsum := real_list_sum X (fun s : X => real_kl_term (p s) (pb s) (Hp s) (pbpos s)) L).
  set (Fp := real_free_energy X sumf real_base_loss D p Hp).
  set (Fb := real_free_energy X sumf real_base_loss D pb pbpos).
  (* 第 1 步：正典分解：F[p] ≡ F[p_b] + D·KL *)
  assert (Hdec : real_eq Fp (real_plus Fb (real_mult D KLsum))).
  { exact (real_kl_decomp_full_canon X sumf
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g L Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g L)
             (fun (a : Real) (f : X -> Real) => real_list_sum_linear X a f L)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb). }
  (* 第 2 步：D·KL > 0（D>0 × KL>0） *)
  assert (HdK : real_lt real_zero (real_mult D KLsum)).
  { exact (real_mult_pos_compat D KLsum D_pos Hkl). }
  (* 第 3 步：加法平移：F[p_b] + 0 < F[p_b] + D·KL *)
  assert (Hshift : real_lt (real_plus Fb real_zero) (real_plus Fb (real_mult D KLsum))).
  { exact (real_lt_plus_translate Fb real_zero (real_mult D KLsum) HdK). }
  (* 第 4 步：零右端化简：F[p_b] < F[p_b] + D·KL *)
  assert (Hcore : real_lt Fb (real_plus Fb (real_mult D KLsum))).
  { exact (RealSetoid.real_lt_compat (real_plus Fb real_zero) Fb
             (real_plus Fb (real_mult D KLsum)) (real_plus Fb (real_mult D KLsum))
             (real_plus_zero Fb)
             (real_eq_refl (real_plus Fb (real_mult D KLsum)))
             Hshift). }
  (* 第 5 步：沿分解运输：F[p_b] < F[p] *)
  exact (RealSetoid.real_lt_compat Fb Fb
           (real_plus Fb (real_mult D KLsum)) Fp
           (real_eq_refl Fb)
           (real_eq_sym Fp (real_plus Fb (real_mult D KLsum)) Hdec)
           Hcore).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：可达形 (b) 单向可比版——逐项 p ≤ p_b + s₀ 处严格分离            *)
(*   ⟹ G07 klst_kl_sum_strict ⟹ KL > 0 ⟹ 件 4 ⟹ F 严格差。            *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_le :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (forall s : X, real_le (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)) ->
  real_lt (p s₀)
    (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D p Hp).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hpq Hdiv.
  apply (t15_fe_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb).
  exact (klst_kl_sum_strict X l₁ s₀ l₂ p
           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hpq Hnormp Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 6：可达形 (b) 双向见证版——逐项双向可比（Or 承载，诚实接口位）+     *)
(*   s₀ 处双向严格分离见证 ⟹ G07 klst_kl_energy_nonconst ⟹ KL>0        *)
(*   ⟹ 件 4 ⟹ F 严格差。                                               *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_or :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (* 逐项双向可比（诚实接口位：去除等价 LLPO 形，非直觉主义可证） *)
  (forall s : X,
     Or (real_le (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (p s))) ->
  (* s₀ 处显式分歧见证（Set 层 Or 承载，任一方向） *)
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀))
      (real_lt (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀)
               (p s₀))) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D p Hp).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hpq Hdiv.
  apply (t15_fe_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb).
  exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p
           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hpq Hnormp Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 7：可达形 (b) bool 完成——件 6 在 [true; false] 载体的实例          *)
(*   （s₀ := true，l₁ := []，l₂ := [false]）。                          *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  (forall s : bool,
     Or (real_le (p s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (p s))) ->
  (Or (real_lt (p true)
               (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
      (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
               (p true))) ->
  real_lt (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false]) real_base_loss D
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false]) real_base_loss D p Hp).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Hpq Hdiv.
  exact (t15_fe_strict_divergence_or bool [] true [false] real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Hpq Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 8：组装件（bool 载体，prod 双函数记录——Set 层 And 形，零 Prop）    *)
(*   定理 4.5 两可达形的合取载体：(a) 肢（F 等 ⟹ 逐点等，零接口）×      *)
(*   (b) 肢（逐项可比 + s₀ 分歧见证 ⟹ F 严格差）。                      *)
(* ---------------------------------------------------------- *)

Theorem t15_free_energy_min_unique :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  prod (real_eq (real_free_energy bool
                   (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D p Hp)
                (real_free_energy bool
                   (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
                   (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
        -> forall s : bool,
             real_eq (p s)
                     (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : bool,
           Or (real_le (p s)
                         (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
              (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                       (p s)))
        -> (Or (real_lt (p true)
                        (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
               (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
                        (p true)))
        -> real_lt (real_free_energy bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D
                      (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
                      (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
                   (real_free_energy bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D p Hp)).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb.
  split.
  - exact (t15_fe_eq_unique_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             p Hp Hnormp Hnormb).
  - exact (t15_fe_strict_divergence_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             p Hp Hnormp Hnormb).
Qed.
