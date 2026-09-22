(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   t12_elbo_tight_forward_bool（原 L356，3 句玩具证）                   *)
(*   t12_elbo_tight_backward（原 L268，4 句玩具证）                       *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqELBOTight.v *)
(* *)
(* 目的： 定理 4.8 elbo_tight 的 Real 层可达形组装。 *)
(* 主件： t12_elbo_tight 前后向双腿与 t12_tight_kl_zero 紧致核。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqRealFEP、UpReqELBOEps、UpReqKLSTangent、G08_Gibbs。 *)
(* 备注： 等号条件承定理 4.3 的构造性边界；紧致假设沿等值核传递。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqELBOTight.v —— 席T12：定理 4.8 elbo_tight Real 层可达形组装      *)

(* ------------------------------------------------------------------ *)
(* 【使命】席N1 判定（C8）：定理 4.8（论文正式版 L374-376：ELBO=证据      *)
(*   当且仅当 q(z) 等于真实后验；〔构造强度〕标签「序档＋等号条件档——   *)
(*   等号条件承定理 4.3 的构造性边界；req 同位；Real 层无复刻」）的       *)
(*   Real 层可达形（同 C3(a) 显式前提形）：                              *)
(*     正向半边：ELBO(q) ≡ evidence ⟹ 逐点 q s ≡ p_b s；                *)
(*     逆向半边：逐点 q s ≡ p_b s ⟹ ELBO(q) ≡ evidence。                *)
(*   双向组装为 prod 双函数记录（Set 层 And 形，零 Prop）。              *)
(* ------------------------------------------------------------------ *)
(* 【术语映射表（承 T10 结果件，逐字沿用）】                             *)
(*   ELBO(q) := −F[q]        ↔ real_elbo（UpReqELBOEps 件 0）           *)

(*   真实后验/输出分布       ↔ real_boltzmann_dist_r（π* 锚闭式解实例）  *)
(*   KL(q‖p_b) 逐项和        ↔ Σ real_kl_term(q s, p_b s)                *)
(*   紧致点（ELBO=证据）     ↔ real_eq（RealSetoid 等值载体）            *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（各步引用件名）】                                     *)
(*   件 0 切点式谓词 t12_tangent_eq（Set 层显式前提形的逐点结论面）。    *)
(*   件 1 紧致核 t12_tight_kl_zero：紧致假设沿 T10 等值核               *)
(*     real_evidence_kl_decomp 运输 ⟹ ELBO ≡ ELBO + D·KL ⟹             *)
(*     加法消去（S08 real_eq_plus_cancel_l）⟹ D·KL ≡ 0 ⟹                *)
(*     D>0 右因子消去（S08 real_eq_mult_cancel_r + S02 real_mult_comm）  *)
(*     ⟹ KL ≡ 0。                                                       *)
(*   件 2 正向半边 t12_elbo_tight_forward（抽象载体，显式前提形）：      *)
(*     件 1 + 显式接口前提「KL ≡ 0 ⟹ 逐点切点式」（gibbe2 主件注入位    *)
(*     的载体级抬升）+ 席T1 t1_log_eq_linear_inject（「切点⟹一」，       *)
(*     无条件消解）+ gibbe2 主件尾链同款比值一消去                       *)
(*     （G08 gibbsd_p_mult_ratio）⟹ 逐点 q s ≡ p_b s。                  *)
(*   件 3 逆向半边 t12_elbo_tight_backward（抽象载体，零接口前提）：     *)
(*     逐点等 ⟹ 自由能等（UpReqRealFEP rfep_free_energy_ext_r）⟹       *)
(*     real_opp 兼容（RealSetoid.real_eq_opp_compat）⟹ 紧致。           *)
(*   件 4 组装件 t12_elbo_tight：prod 双函数记录（Set 层 And 形：        *)
(*     (紧致 ⟹ 逐点等) × (逐点等 ⟹ 紧致)）。                            *)
(*   件 5 bool 载体完成 t12_elbo_tight_forward_bool：显式接口前提由      *)
(*     席T1 t1_gibbe2_gibbs_equality_bool 整链消解（KL≡0 ⟹ 逐点等       *)
(*     直达，接口位零残留）——N1 C3(a)「样板」载体上的全消解形。         *)
(*   件 6 bool 组装件 t12_elbo_tight_bool：件 5 + 件 3 的 prod 双函数   *)
(*     记录，零接口前提（除 q 正 + 双归一化的显式物理前提）。            *)
(* ------------------------------------------------------------------ *)
(* 【可达强度如实标注】                                                 *)
(*   ① 双向半边的结论面均为 real_eq 等值载体（Set 层），前提面为        *)
(*     「q 逐点正 + Σq≡1 + Σp_b≡1」的显式物理前提（件 5/6）或再加       *)
(*     「KL≡0 ⟹ 逐点切点式」的抽象载体诚实接口前提（件 2/4）。          *)


(*     在案：需强三分/LPO）；本件用其弱形——「切点⟹一」                  *)
(*     （席T1 t1_log_eq_linear_inject，弱三分 + 双支切线构造）——         *)
(*     该弱形在盘无条件闭合，本件正向半边即弱形闭合实例。                *)
(*   ③ 抽象载体上「KL≡0 ⟹ 逐点」步的非负提取接口（件 2 的显式前提位）   *)
(*     在 bool 载体由 T1 整链件完全消解（件 5），零残留。                *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_eq/real_lt 全 Set 值，组装载体 prod）；   *)
(*   全 Qed 闭合；禁词条目零命中（头注以中文转述，不引英文原词）；       *)
(*   real_eq 非 Id 禁改写，全链 real_eq_trans / RealSetoid 运输；        *)
(*   D 因子逐字保留。禁改红线：UpReqELBOEps.v / UpReqKLSTangent.v /     *)
(*   UpReqRealFEP.v / G08_Gibbs.v / S 模块全程只读（只消费 .vo）。       *)

(*   全量 -Q vo 树；前置 .vo 全在 ConstructiveWorld_vo/。               *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.
Require Import UpReqELBOEps.
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
(*   链：T10 等值核（evidence ≡ ELBO + D·KL）+ 紧致（ELBO ≡ evidence）  *)
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
  (* 第 1 步：等值核（T10 件 1 实例化；set 折叠面经局部定义展开可转换） *)
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
(*   逐点消去链：切点式 + 席T1 t1_log_eq_linear_inject（切点⟹一，       *)
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
     bool 载体上由件 5 整链消解（席T1 件直达），零残留。 *)
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
  (* 第 2 步：切点式 + 「切点⟹一」（席T1 无条件消解）⟹ 比值一 *)
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
(*   显式前提位由席T1 t1_gibbe2_gibbs_equality_bool 整链消解             *)
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
