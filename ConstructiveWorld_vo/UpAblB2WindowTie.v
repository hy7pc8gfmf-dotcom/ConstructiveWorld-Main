(* ============================================================ *)
(* UpAblB2WindowTie.v —— (d) 窗定理退化端实例衔接件                                  *)
(* 使命：本件为 B2 退化端实例衔接件；原 B2 定位（装配路径验证，UpReqConcB2Time      *)
(*   §6.4 候）不变——本件零改原 B2 既有装配，只做「窗定理视角」的新增连接：              *)
(*   证明 B2 单点世界（S:=unit、enum:=[tt]、z:=cb2_z、Delta:=cb2_Delta、          *)
(*   核=rsq_bs_kernel 系）是 M4 泛型退化定理（UpAblMetaWindow）的实例。             *)
(* 两件升级内容：                                                                  *)
(*   (i) 前提分支：B2 核 cbt_kernel 满足 M4 退化前提——                          *)
(*       · 行随机：单点世界仅一行，行和 = 核值 = one（softmax 单点归一）；           *)
(*       · 核行全同：仅一行，平凡成立（ubt_rows_eq 由 unit 归纳平凡收束）；          *)
(*       · 点质量对：单点世界唯一归一分布即 tt 处点质量（ubt_mass_point）。          *)
(*   (ii) 具名实例：B2 世界一步退化 TV==0（与 cbt_tv 恒等式并读），                 *)
(*       且 M4 泛型退化分支被字面使用（ubt_b2_m4_collapse_instance：唯一行经          *)
(*       点质量嵌入 bool 载体为 (1,0)-常行，mwi_collapse_row_equal 直接代入）。        *)
(* 衔接语义诚实注记：M4 退化分支载体为 bool 载体（World3 两态），B2 世界为        *)
(*   unit 单点；字面使用经唯一态嵌入：B2 核唯一行（单条目 = one）映为                 *)
(*   ubt_Klift = 常行 (cbt_kernel tt tt, 0)——即 bool 上的 tt-点质量行。             *)
(*   该行满足 M4 两前提（行随机由 ubt_kernel_pt、行全同平凡），故泛型引理使用          *)
(*   合法；B2 自身指数（cbt_tv/cbt_titer）的一步退化另由 §3 直接链自证，              *)
(*   两读互证：泛型分支（嵌入像）＋本征分支（unit 原像）。                               *)
(* 依赖：S01_BaseRing、CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSampling、          *)
(*   UpReqConcSoftmax、UpAblMetaWorld3、UpAblMetaWindow、UpReqConcB2Time。             *)
(* 对标：mathlib 有限马尔可夫链退化端窗实例；stdlib 无同形。                            *)
(* 构造性注记：零承认件（语句面无承认式构造）；零经典逻辑；语句面全 Set 值            *)
(*   （req/lt/And 均基座 Set 层）；前提位全显式定理参数；全件 Defined 收束可提取；      *)
(*   零改任何既有件。                                                                  *)
(* 编译配方：9.1 bash 直调轨（vo 树内 -Q . "" 平面命名空间），信任缓存前置。         *)
(* ============================================================ *)

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
Require Import UpReqAlgebra.
Require Import UpReqSampling.
Require Import UpReqConcSoftmax.
Require Import UpAblMetaWorld3.
Require Import UpAblMetaWindow.
Require Import UpReqConcB2Time.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* §1 前提分支：B2 核行双档（M4 退化前提的单点世界形式）                             *)
(* ============================================================ *)

(* 1a. 行随机（核行和 = one）：rsq_bs_kernel_row 泛型分支全显实例直接代入 *)
Lemma ubt_row_sum_tt : req (cbt_sumf (fun s' : unit => cbt_kernel tt s')) one.
Proof.
  exact (@rsq_bs_kernel_row Real RealEnhancedReal unit cbt_sumf
           (csm_sum_ext unit [tt]) (csm_sum_linear unit [tt])
           [tt] cbt_enum_ne
           cbt_temp cbt_temp_pos cbt_Delta cbt_z cbt_z_lb cbt_sum_eq_list tt).
Defined.

(* 1b. 核值 = one（softmax 单点归一：单行和 = 唯一条目） *)
Lemma ubt_kernel_pt : req (cbt_kernel tt tt) one.
Proof.
  assert (B : req (plus (cbt_kernel tt tt) zero) one).
  { apply (req_trans (plus (cbt_kernel tt tt) zero)
             (cbt_sumf (fun s' : unit => cbt_kernel tt s'))).
    - exact (req_trans (plus (cbt_kernel tt tt) zero)
               (rsq_bs_list_sum unit (fun s' : unit => cbt_kernel tt s') [tt])
               (cbt_sumf (fun s' : unit => cbt_kernel tt s'))
               (req_refl _)
               (req_sym (cbt_sumf (fun s' : unit => cbt_kernel tt s'))
                  (rsq_bs_list_sum unit (fun s' : unit => cbt_kernel tt s') [tt])
                  (cbt_sum_eq_list (fun s' : unit => cbt_kernel tt s')))).
    - exact ubt_row_sum_tt. }
  exact (req_trans (cbt_kernel tt tt) (plus (cbt_kernel tt tt) zero) one
           (req_sym _ _ (plus_zero (cbt_kernel tt tt))) B).
Defined.

(* 1c. 核行全同（单点世界仅一行——平凡成立，unit 逐点归约） *)
Lemma ubt_rows_eq : forall s s' : unit, req (cbt_kernel s s') (cbt_kernel tt tt).
Proof.
  intros s s'. destruct s. destruct s'.
  exact (req_refl (cbt_kernel tt tt)).
Defined.

(* 1d. 行随机（逐行形） *)
Lemma ubt_row_stoch : forall s : unit, req (cbt_sumf (cbt_kernel s)) one.
Proof.
  intro s. destruct s.
  exact ubt_row_sum_tt.
Defined.

(* ============================================================ *)
(* §2 M4 泛型退化分支的字面使用：唯一行经点质量嵌入 bool 载体                        *)
(* ============================================================ *)

(* 嵌入核：B2 核唯一行（单条目 = one）映为 bool 上的 tt-点质量常行 *)
Definition ubt_Klift (s s' : bool) : Real := mult (cbt_kernel tt tt) (mtw_mu0 s').

Lemma ubt_Klift_row : forall s : bool,
  req (plus (ubt_Klift s true) (ubt_Klift s false)) one.
Proof.
  intro s.
  assert (Ht : req (ubt_Klift s true) (cbt_kernel tt tt)).
  { exact (mult_one (cbt_kernel tt tt)). }
  assert (Hf : req (ubt_Klift s false) zero).
  { exact (mult_zero (cbt_kernel tt tt)). }
  apply (req_trans (plus (ubt_Klift s true) (ubt_Klift s false))
                   (plus (cbt_kernel tt tt) zero)).
  - exact (req_plus_compat (ubt_Klift s true) (cbt_kernel tt tt)
                           (ubt_Klift s false) zero Ht Hf).
  - exact (req_trans (plus (cbt_kernel tt tt) zero) (cbt_kernel tt tt) one
             (plus_zero (cbt_kernel tt tt)) ubt_kernel_pt).
Defined.

Lemma ubt_Klift_rows_eq : forall s s' : bool,
  req (ubt_Klift s s') (ubt_Klift true s').
Proof.
  intros s s'. exact (req_refl (mult (cbt_kernel tt tt) (mtw_mu0 s'))).
Defined.

(* M4 泛型退化分支使用：B2 嵌入核的 TV 一步退化 == 0 *)
Theorem ubt_b2_m4_collapse_instance :
  req (mtw_tv (mwi_step ubt_Klift mtw_mu0) (mwi_step ubt_Klift mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal ubt_Klift ubt_Klift_row ubt_Klift_rows_eq).
Defined.

(* ============================================================ *)
(* §3 B2 本征分支：单点世界质量双档 + 一步退化 TV==0（与 cbt_tv 恒等式并读）               *)
(* ============================================================ *)

(* 1 元档折叠处方：sumf g = g tt + 0（cbt_sum_eq_list 桥 + iota） *)
Lemma ubt_sumf_of_point : forall g : unit -> Real,
  req (g tt) one -> req (cbt_sumf g) one.
Proof.
  intros g Hgt.
  apply (req_trans (cbt_sumf g) (plus (g tt) zero) one).
  - exact (req_trans (cbt_sumf g)
             (rsq_bs_list_sum unit g [tt]) (plus (g tt) zero)
             (cbt_sum_eq_list g) (req_refl _)).
  - exact (req_trans (plus (g tt) zero) (g tt) one (plus_zero (g tt)) Hgt).
Defined.

(* 1 元档质量消解：sumf mu = one -> mu tt = one（cbt_tv0 同轨逆向） *)
Lemma ubt_mass_point : forall mu : unit -> Real,
  req (cbt_sumf mu) one -> req (mu tt) one.
Proof.
  intros mu Hm.
  exact (req_trans (mu tt) (plus (mu tt) zero) one
           (req_sym _ _ (plus_zero (mu tt)))
           (req_trans (plus (mu tt) zero) (cbt_sumf mu) one
              (req_trans (plus (mu tt) zero)
                 (rsq_bs_list_sum unit mu [tt]) (cbt_sumf mu)
                 (req_refl _)
                 (req_sym _ _ (cbt_sum_eq_list mu)))
              Hm)).
Defined.

(* 一步演化在唯一态的值：titer 1 mu tt = mu tt · K(tt,tt)（k_step 出节形直算） *)
Lemma ubt_titer_one_tt : forall mu : unit -> Real,
  req (cbt_titer 1%nat mu tt) (mult (mu tt) (cbt_kernel tt tt)).
Proof.
  intro mu.
  change (cbt_titer 1%nat mu tt) with
    (cbt_sumf (fun s : unit => mult (mu s) (cbt_kernel s tt))).
  apply (req_trans (cbt_sumf (fun s : unit => mult (mu s) (cbt_kernel s tt)))
                   (plus (mult (mu tt) (cbt_kernel tt tt)) zero)).
  - exact (cbt_sum_eq_list (fun s : unit => mult (mu s) (cbt_kernel s tt))).
  - exact (plus_zero (mult (mu tt) (cbt_kernel tt tt))).
Defined.

(* 一步演化守质量：titer 1 mu tt = one（核值 = one 消解） *)
Lemma ubt_titer_one_mass : forall mu : unit -> Real,
  req (cbt_sumf mu) one -> req (cbt_titer 1%nat mu tt) one.
Proof.
  intros mu Hm.
  pose proof (ubt_titer_one_tt mu) as Hpt.
  assert (Hk1 : req (mult (mu tt) (cbt_kernel tt tt)) one).
  { exact (req_trans (mult (mu tt) (cbt_kernel tt tt))
                     (mult one (cbt_kernel tt tt)) one
             (req_mult_compat (mu tt) one (cbt_kernel tt tt) (cbt_kernel tt tt)
                (ubt_mass_point mu Hm) (req_refl (cbt_kernel tt tt)))
             (req_trans (mult one (cbt_kernel tt tt)) (cbt_kernel tt tt) one
                (req_mult_one_l (cbt_kernel tt tt))
                ubt_kernel_pt)). }
  exact (req_trans _ _ _ Hpt Hk1).
Defined.

(* 1 元档 TV 归零：唯一态差 = 0 ⟹ sumf|diff| = 0 ⟹ TV = inv_two·0 = 0 *)
Lemma ubt_tv_point_zero : forall mu nu : unit -> Real,
  req (mu tt) one -> req (nu tt) one -> req (cbt_tv mu nu) zero.
Proof.
  intros mu nu Hmu Hnu.
  assert (Hd : req (req_minus (mu tt) (nu tt)) zero).
  { exact (req_trans (req_minus (mu tt) (nu tt))
                     (plus one (opp one)) zero
                     (req_plus_compat (mu tt) one (opp (nu tt)) (opp one)
                        Hmu (req_opp_compat (nu tt) one Hnu))
                     (plus_opp one)). }
  assert (Hsum : req (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))) zero).
  { exact (req_trans
             (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s))))
             (plus (abs (req_minus (mu tt) (nu tt))) zero) zero
             (req_trans
                (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s))))
                (rsq_bs_list_sum unit
                   (fun s : unit => abs (req_minus (mu s) (nu s))) [tt])
                (plus (abs (req_minus (mu tt) (nu tt))) zero)
                (cbt_sum_eq_list (fun s : unit => abs (req_minus (mu s) (nu s))))
                (req_refl _))
             (req_trans (plus (abs (req_minus (mu tt) (nu tt))) zero)
                (abs (req_minus (mu tt) (nu tt))) zero
                (plus_zero (abs (req_minus (mu tt) (nu tt))))
                (req_trans (abs (req_minus (mu tt) (nu tt))) (abs zero) zero
                   (req_abs_compat (req_minus (mu tt) (nu tt)) zero Hd)
                   abs_zero))). }
  unfold cbt_tv.
  exact (req_trans
           (mult cbt_inv_two
              (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))))
           (mult cbt_inv_two zero) zero
           (req_mult_compat cbt_inv_two cbt_inv_two
              (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))) zero
              (req_refl cbt_inv_two) Hsum)
           (mult_zero cbt_inv_two)).
Defined.

(* 具名实例（本征分支）：B2 世界一步退化 TV==0 *)
Theorem ubt_b2_one_step_collapse :
  forall mu nu : unit -> Real,
    req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
    req (cbt_tv (cbt_titer 1%nat mu) (cbt_titer 1%nat nu)) zero.
Proof.
  intros mu nu Hmu Hnu.
  apply ubt_tv_point_zero.
  - exact (ubt_titer_one_mass mu Hmu).
  - exact (ubt_titer_one_mass nu Hnu).
Defined.

(* 单点世界 TV ≡ 0（零步亦零；与论文 §6.4「装配路径验证」定位并读不变） *)
Theorem ubt_b2_tv0_zero :
  forall mu nu : unit -> Real,
    req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
    req (cbt_tv mu nu) zero.
Proof.
  intros mu nu Hmu Hnu.
  apply ubt_tv_point_zero.
  - exact (ubt_mass_point mu Hmu).
  - exact (ubt_mass_point nu Hnu).
Defined.

(* 退化端窗（Set 层合取：本征零步支 + 本征一步支） *)
Theorem ubt_b2_window_degenerate :
  And (forall mu nu : unit -> Real,
         req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
         req (cbt_tv mu nu) zero)
      (forall mu nu : unit -> Real,
         req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
         req (cbt_tv (cbt_titer 1%nat mu) (cbt_titer 1%nat nu)) zero).
Proof.
  split.
  - exact ubt_b2_tv0_zero.
  - exact ubt_b2_one_step_collapse.
Defined.

(* ============================================================ *)
(* G4 证据：衔接件闭包机器判据（全 Closed = 零新假设）                               *)
(* ============================================================ *)

Print Assumptions ubt_row_sum_tt.
Print Assumptions ubt_kernel_pt.
Print Assumptions ubt_rows_eq.
Print Assumptions ubt_row_stoch.
Print Assumptions ubt_Klift_row.
Print Assumptions ubt_Klift_rows_eq.
Print Assumptions ubt_b2_m4_collapse_instance.
Print Assumptions ubt_b2_one_step_collapse.
Print Assumptions ubt_b2_tv0_zero.
Print Assumptions ubt_b2_window_degenerate.
