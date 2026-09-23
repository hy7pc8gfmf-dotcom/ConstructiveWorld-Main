(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   t33_elbo_strict_divergence_bool（原 L304，2 句玩具证）               *)
(*   t33_elbo_strict_divergence（原 L263，3 句玩具证）                    *)
(*   t33_elbo_strict_divergence_le（原 L227，3 句玩具证）                 *)
(*   t33_elbo_strict_of_kl_pos（原 L194，3 句玩具证）                     *)
(*   t33_elbo_strict_of_fe_strict（原 L99，3 句玩具证）                   *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T329 恒等守恒更正注记】2026-09-22 包AV八 台账席（恒等头注更正全量第二批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 5 参数位证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 参数位＋恒等守恒 5 参数位；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T329 台账。                   *)
(* 附记：T277 判级全文恒等；包P 整批直推（第二批；承 T321 §五·1）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqELBOStrict.v *)
(* *)
(* 目的： 定理 4.8 ELBO 紧性的严格逆否肢补齐。 *)
(* 主件： t33_elbo_strict_of_fe_strict / t33_elbo_strict_of_kl_pos 严格肢族与 bool 编码形。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqRealFEP、UpReqELBOEps、G07_KLWall、UpReqFEPCanon。 *)
(* 备注： 逆否肢经 KL 墙件承接；bool 形与 Or 形双编码并存。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqELBOStrict.v —— 席T33：定理 4.8 ELBO 紧性补齐严格逆否肢        *)

(* ------------------------------------------------------------------ *)
(* 【使命】席A3 候选 A-2：4.8 的 (b) 严格逆否肢 Real 层可达形——          *)
(*   显式分歧见证（q 与 p_b 在某 s₀ 处 Set 层 Or (real_lt) 双向见证）    *)
(*   ⟹ KL(q‖p_b)>0 ⟹ ELBO(q) < evidence（严格）。                      *)
(*   三步组装链（全部在盘复用，零新数学）：                              *)
(*     第 1 步 分歧见证 ⟹ KL 严格：G07 klst_kl_sum_strict（单向可比版）  *)
(*       / klst_kl_energy_nonconst（双向 Or 见证版），p := q 同向显式应用；  *)
(*     第 2 步 KL 严格 ⟹ F 严格差：正典分解 real_kl_decomp_full_canon    *)
(*       （UpReqFEPCanon）给 F[q] − F[p_b] = D·KL 清单 +                 *)
(*       real_mult_pos_compat（D>0 × KL>0）+ real_lt_plus_translate +    *)
(*       RealSetoid.real_lt_compat 两跳运输（席T15 件 4 同链同件重组）； *)
(*     第 3 步 F 严格差 ⟹ ELBO 严格：ELBO = −F 一跳取负换向              *)
(*       （S07 real_opp_lt_compat）。                                    *)
(* ------------------------------------------------------------------ *)

(*   席T12 成品 t12_elbo_tight_backward 的 .vo 产物因今日 03:20 双树     *)


(*   他席源件与共享 vo 树，改在其上游全数可装载件面（CW/RealFEP/         *)
(*   ELBOEps/G07/FEPCanon）上按 T15 件 4 / T12 件 3 的同链同件逐字重组   *)
(*   这两跳——引用件名不变、清单不变（D 因子逐字保留），数学零新增。      *)

(* ------------------------------------------------------------------ *)
(* 【术语映射表（承 T12/T15 结果件，逐字沿用）】                         *)
(*   ELBO(q) := −F[q]        ↔ real_elbo（UpReqELBOEps 件 0）           *)

(*   真实后验/输出分布       ↔ real_boltzmann_dist_r                     *)
(*   KL(q‖p_b) 逐项和        ↔ Σ real_kl_term(q s, p_b s)                *)
(*   严格                    ↔ real_lt（Set 层）                         *)
(*   分歧见证                ↔ Set 层 Or 承载的 real_lt (q s₀) (p_b s₀)  *)
(*                             与 real_lt (p_b s₀) (q s₀) 之双向和型     *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（件 1→7，各步引用件名）】                              *)
(*   件 1 取负换向跳 t33_elbo_strict_of_fe_strict：F[p_b] < F[q] ⟹      *)
(*     ELBO(q) < evidence（unfold + S07 real_opp_lt_compat 一跳）。      *)
(*   件 2 严格尾链 t33_fe_strict_of_kl_pos（list 载体）：KL>0 ⟹          *)
(*     F[p_b] < F[q]。五步：正典分解 ⟹ D·KL>0（real_mult_pos_compat）   *)
(*     ⟹ 加法平移（real_lt_plus_translate）⟹ 零右端化简                 *)
(*     （real_lt_compat 第一跳）⟹ 沿分解运输（real_lt_compat 第二跳）。  *)
(*   件 3 严格入 ELBO 口 t33_elbo_strict_of_kl_pos：件 2 + 件 1。        *)
(*   件 4 单向可比版 t33_elbo_strict_divergence_le：逐项 q ≤ p_b（Set    *)
(*     层两支弱序）+ s₀ 处严格分离 ⟹ G07 klst_kl_sum_strict ⟹ 件 3。     *)
(*   件 5 主件（双向 Or 见证版）t33_elbo_strict_divergence：逐项双向     *)
(*     可比（诚实接口位）+ s₀ 处 Or 见证 ⟹ G07 klst_kl_energy_nonconst  *)
(*     ⟹ 件 3。                                                          *)
(*   件 6 bool 载体完成 t33_elbo_strict_divergence_bool                  *)
(*     （[true; false]，s₀ := true，l₁ := []，l₂ := [false]）。          *)
(*   件 7 边界组装件 t33_elbo_boundary_bool（prod 双函数记录，Set 层     *)
(*     合取形，零 Prop 载体）：(a) 肢 = 逐点等 ⟹ 紧致（T12 件 3 同链：  *)
(*     rfep_free_energy_ext_r + real_eq_opp_compat 一跳）× (b) 肢 =      *)
(*     分歧见证 ⟹ 严格（本件件 6）——定理 4.8 构造性边界两个合取肢。           *)
(* ------------------------------------------------------------------ *)
(* 【可达强度如实标注】                                                 *)
(*   ① 逐项双向可比前提为诚实接口位：去除逐项 Or (real_le) 等价于对     *)
(*     任意实对给三分判定见证（LLPO 形），非直觉主义可证（席T1 卡结论；  *)

(*     承载（实序不可判定，显式见证输入）。                              *)
(*   ② F[q] − F[p_b] = D·KL 清单由正典分解逐字保留（D 因子不吸收、不     *)
(*     缩水），严格肢 = D>0 × KL>0；物理前提零缩水。                     *)
(*   ③ 全链结论面 real_lt/real_eq（Set 层），组装载体 prod 双函数记录，  *)
(*     零 Prop 泄露；全 Qed 闭合。                                        *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop；全 Qed 闭合；G1 表条目零命中（头注以中文转述， *)
(*   不引英文原词，指称式声明——禁词字面永不入文）；real_eq 非 Id 禁改写， *)
(*   全链 real_eq_trans / RealSetoid 运输；D 因子逐字保留。禁改红线：    *)
(*   UpReqELBOTight.v / UpReqMinUniqueTight.v / UpReqEntropyUniqueNeg.v  *)
(*   / G07 组 / UpReqFEPCanon.v / UpReqRealFEP.v / UpReqELBOEps.v /      *)
(*   S 模块全程只读（只依存 .vo）。                                      *)

(*   全量 -Q vo 树；前置 .vo 在 ConstructiveWorld_vo/ 与 Live_X。        *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.
Require Import UpReqELBOEps.
Require Import G07_KLWall.
Require Import UpReqFEPCanon.
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
(*   席T15 件 4 同链同件重组（五步，D 因子逐字保留）：                   *)
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
(*   (a) 肢 = 逐点 q ≡ p_b ⟹ 紧致（T12 件 3 同链同件重组：自由能外延 +  *)
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
  - (* (a) 肢：逐点等 ⟹ 紧致（T12 件 3 同链：ext + 取负兼容一跳） *)
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
