(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   real_evidence_def（原 L104，2 句玩具证）                             *)
(*   real_elbo_def（原 L93，2 句玩具证）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqELBOEps.v *)
(* *)
(* 目的： 定理 4.7 elbo_lower_bound 的 Real 层序档组装（eps 档）。 *)
(* 主件： real_elbo_lower_bound_eps 及其配分形 real_elbo_lower_bound_eps_partition。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqRealFEP。 *)
(* 备注： 证据下界取逐 eps 档；ELBO 与证据为显式定义。 *)
(* ============================================================ *)

(* ============================================================ *)

(* ------------------------------------------------------------------ *)
(*   S04 L4570 Set 形 / req 层 UpReqDist.v L2645 已结果）的 Real 层     *)
(*   第三档逐 eps 形：                                                   *)
(*     ∀eps>0（q 正且归一），  ELBO(q) ≤ evidence + D·eps。             *)
(* ------------------------------------------------------------------ *)
(* 【术语映射表（论文/S04 Set 层 ↔ 本件 Real 层）】                     *)
(*   ELBO(q) := −F[q]        ↔ real_elbo（= real_opp 实自由能）          *)

(*   自由能 F[·]             ↔ real_free_energy（UpReqRealFEP 具名接口） *)
(*   后验/输出分布 p_output  ↔ real_boltzmann_dist_r（π* 锚闭式解实例）  *)
(*   KL(q‖p_output) 逐项和   ↔ real_sum_over_S (fun s => real_kl_term…) *)
(*   库内 RLHF 版术语对位：reward/π_ref 载体 = base_loss/p_b；            *)
(*   rlhf 自由能 F[π] ↔ −J(π)；F 形取负即 ELBO 术语（桥引理见件 2）。    *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（各步引用件名）】                                     *)
(*   件 0 定义件：real_elbo / real_evidence（real_opp 自由能抽象，       *)
(*     对位 S04 L4563/L4565 Set 定义；reflexivity 桥引理附）             *)
(*   件 1 等值核（real_eq）：evidence ≡ ELBO(q) + D·Σ kl_term(q,p_b)    *)
(*     = rfep_rlhf_free_energy_kl（UpReqRealFEP L1079，任意 π* 版；      *)
(*       π* := p_b 实例，Halign 取逐点自反）+ 取负代数链                 *)
(*       （real_eq_opp_compat / real_opp_plus / plus 环基元，           *)
(*       ——rlhf F 形到 ELBO/evidence 术语的桥引理，S04 L4586            *)
(*       evidence_kl_decomp 的 Real 对位）。                             *)
(*   件 2 非负腿（第三档逐 eps 形）：0 ≤ Σ kl_term + eps                 *)
(*     = S08_RealMainlineDPO.real_gibbs_inequality_eps（L490；          *)
(*       list 载体全链，Hnormq/Hnormb 双归一化前提）。                   *)
(*   件 3 通用逐 eps 完成机 elbo_lower_bound_close_eps（第 3+4 步）：    *)
(*     D>0 消去 = S09 real_le_mult_compat_r（弱 le 首前提，lt 先过       *)
(*       RealSetoid.real_lt_le_iff_req 弱化桥）+ real_mult_zero          *)
(*       / real_distrib（S02 代数基元）+ RealSetoid.real_le_id_l/id_r；  *)
(*     序完成 = S07 real_le_plus_compat（全局形）+ real_le_refl          *)
(*       + real_plus_assoc / real_plus_zero + RealSetoid 运输。          *)
(*   （件 1+2+3 由主件一次组装；主件载体实例化 sumf := list 形，          *)
(*   T7 同型；分件 Hnormb 经 rfep_boltzmann_normalized_real（L331）      *)
(*   消解为 partition 条件 Σ exp(−e/D) ≡ Z，与 T7/X2 分件同型。）        *)
(* ------------------------------------------------------------------ *)

(*   ①任意 π* 版自由能-KL 分解件（UpReqRealFEP L1079 在盘，正典件复用）  *)
(*   ②实 Gibbs 不等式逐 eps 形（S08 在盘）；③④纯序代数消去/完成        *)
(*   （S09/S07/S02 在盘）。本件增量 = ELBO/evidence 具名定义 + 取负      *)
(*   术语桥（rlhf F 形 ↝ 变分下界术语）+ 逐 eps 序档拼装。               *)
(*   前提全显式：q 逐点正 + 双归一化（或 partition 条件）+ eps 正。      *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_le/real_lt/real_eq 全 Set 值）；全 Qed   *)
(*   闭合；禁词条目零命中（头注以中文转述，不引英文原词）；real_eq 非    *)
(*   Id 禁改写，全链 real_eq_trans/RealSetoid 运输（E393 纪律）；        *)
(*   D 因子逐字保留（T7 同账）。                                         *)
(*   禁改红线：UpReqRealFEP.v / S08 模块全程只读（只使用 .vo）。         *)
(* 编译配方：_t10_run.ps1 单一入口（E355/X2/T7 先例）+ cpu_guard CoreN 2 *)

(*   前置 .vo 全在 D:/ComplexAnalysis/ConstructiveWorld-Main/           *)
(*   ConstructiveWorld_vo/（vo 树编译，上游件零重编）。                  *)
(* ============================================================ *)

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
