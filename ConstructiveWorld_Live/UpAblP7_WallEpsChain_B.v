(* ==========================================================================)
   UpAblP7_WallEpsChain_B —— 论文7 收缩链链身逐 eps 化件：边界见证与迭代副本；同域语句面
   使命：本件形式化论文7 收缩链链身逐 eps 化件：边界见证与迭代副本。
   本件并载：uabp7an_abs_nonneg_uncond（le zero a -> req (abs a) a）：接口字段 abs_pos（仅严格正前提）的弱；lo/hi 桥接引理组：二分之一抽象形 half:=inv_pos (plus one one) two_pos 的有界性与序关系事实；P7BoundedSoftmaxDeep 出节定理的实例化、 独立重证与求和交换恒等三形；Paper7Ablation 出节定理的全称副本、构造性；p7a_expf_wd / p7a_expf_mono_le_do 的柯西实数实例件（S1inst）；ConcB2 的 +1 松弛常数 Δ 与中心 z 的实例双侧界与严格形否定。
   依赖：QArith.QArith, QArith.Qabs, Lia, QArith.Qminmax, S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv
     S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF,
     S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpReqAlgebra, AttnDoeblin, P7BoundedSoftmaxDeep, List, Paper7Ablation,
     Setoid, Morphisms, UpReqSumD, UpReqConcSoftmax, UpReqSampling, UpReqConcMixSel, UpReqConcFin2, UpReqConcB2。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §5 uabp7an_abs_nonneg_uncond（le zero a -> req (abs a) a）：接口字段 abs_pos（仅严格正前提）的弱 ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
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
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 Q 层辅件（半量与四分量的序关系、Qabs 下界引理；零经典逻辑）         *)
(* ============================================================ *)

(* 负零恒等：(- 0)%Q == 0%Q（多处复用） *)
Lemma uabp7an_qneg0 : (- 0)%Q == 0%Q.
Proof. ring. Qed.

(* e/2 严格正（0 < e）（由 Qlt_le_dec 的可判定二分与 Qplus_le_compat） *)
Lemma uabp7an_qlt_half : forall e : Q, 0 < e -> 0 < e / 2.
Proof.
  intros e He.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  destruct (Qlt_le_dec 0 (e / 2)) as [Hc | Hc].
  - exact Hc.
  - exfalso.
    assert (Hle : e / 2 + e / 2 <= 0 + 0)
      by (apply (Qplus_le_compat (e / 2) 0 (e / 2) 0); [exact Hc | exact Hc]).
    assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
    rewrite Hz1 in Hle.
    rewrite Hsum in Hle.
    exact (Qlt_not_le 0 e He Hle).
Qed.

(* 半加恒等：e/2 + e/2 == e *)
Lemma uabp7an_half_add : forall e : Q, e / 2 + e / 2 == e.
Proof. intro e. field. Qed.

(* 半小于：e/2 < e（0 < e） *)
Lemma uabp7an_half_lt : forall e : Q, 0 < e -> e / 2 < e.
Proof.
  intros e He.
  assert (Hh : 0 < e / 2) by (apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2))); exact Hh).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* 半小于负零形：e/2 < e - 0（0 < e）——配合柯西表示的投影目标形 *)
Lemma uabp7an_half_lt_m0 : forall e : Q, 0 < e -> e / 2 < e - 0.
Proof.
  intros e He.
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2)));
        apply uabp7an_qlt_half; exact He).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e - 0) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* 半不大于：e/2 <= e（0 < e） *)
Lemma uabp7an_half_le : forall e : Q, 0 < e -> e / 2 <= e.
Proof.
  intros e He.
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2)));
        apply uabp7an_qlt_half; exact He).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  apply Qlt_le_weak. exact H1.
Qed.

(* 四分之一小于二分之一：e/4 < e/2（0 < e） *)
Lemma uabp7an_q4_lt_q2 : forall e : Q, 0 < e -> e / 4 < e / 2.
Proof.
  intros e He.
  assert (Hq4 : 0 < e / 4) by (apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 4 + 0 < e / 4 + e / 4)
    by (apply (proj2 (Qplus_lt_r 0 (e / 4) (e / 4))); exact Hq4).
  assert (Hz0 : (e / 4 + 0)%Q == (e / 4)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 4 + e / 4 == e / 2) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* Qabs 下界翻转：|x| < e（0 < e）⟹ -e < x（Qlt_le_dec 分段 + Qopp_lt_compat） *)
Lemma uabp7an_abs_lb : forall x e : Q, 0 < e -> Qabs x < e -> - e < x.
Proof.
  intros x e He Hb.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx') in Hb.
    rewrite <- (Qopp_involutive x).
    exact (Qopp_lt_compat (- x) e Hb).
  - assert (H0 : (- e) < (- 0)) by (apply (Qopp_lt_compat 0 e He)).
    rewrite uabp7an_qneg0 in H0.
    exact (Qlt_le_trans (- e) 0 x H0 Hx).
Qed.

(* 逐点收尾辅件：-x < eps/2（0 < eps）⟹ QltT (Qabs (Qabs x - x)) eps。
   证明：Qlt_le_dec 符号分段，以 Qabs_pos/Qabs_neg 定位绝对值后
   归结为「弱非负（逐 eps 下界）到 |a|==a」的 Q 层核心步骤。 *)
Lemma uabp7an_pt_tail : forall x eps : Q,
  0 < eps -> - x < eps / 2 -> QltT (Qabs (Qabs x - x)) eps.
Proof.
  intros x eps Heps Hneg.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - (* x < 0：|x| == -x，目标 |-2x| == -2x < eps *)
    assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx').
    assert (Hsp : (- x - x)%Q == (- (2 * x))%Q) by ring.
    rewrite Hsp.
    assert (H2xpos : 0 < - (2 * x)).
    { assert (Hlt2 : x + x < 0 + 0)
        by (apply (Qplus_lt_compat x 0 x 0); exact Hx).
      assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
      rewrite Hz1 in Hlt2.
      assert (Hz2 : (x + x)%Q == (2 * x)%Q) by ring.
      rewrite Hz2 in Hlt2.
      assert (H0 : (- 0)%Q < (- (2 * x)))
        by (apply (Qopp_lt_compat (2 * x) 0); exact Hlt2).
      rewrite uabp7an_qneg0 in H0.
      exact H0. }
    rewrite (Qabs_pos (- (2 * x)) (Qlt_le_weak _ _ H2xpos)).
    assert (Hz3 : (- (2 * x))%Q == ((- x) + (- x))%Q) by ring.
    rewrite Hz3.
    assert (Hfin : (- x) + (- x) < eps / 2 + eps / 2)
      by (apply (Qplus_lt_compat (- x) (eps / 2) (- x) (eps / 2)); exact Hneg).
    assert (HsumE : eps / 2 + eps / 2 == eps) by field.
    rewrite HsumE in Hfin.
    exact Hfin.
  - (* x ≥ 0：|x| == x，差归零 *)
    rewrite (Qabs_pos x Hx).
    assert (Hzd : (x - x)%Q == 0%Q) by ring.
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    rewrite uabp7an_qneg0.
    exact Heps.
Qed.

(* ============================================================ *)
(* §2 主件：具体层无条件 abs 非负件（除语句前提外零假设位）               *)
(* ============================================================ *)

Lemma uabp7an_core : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. destruct a as [u Hu]. destruct H as [Hlt | Heq].
  - (* 严格正支：e 见证逐点定位 Qabs_pos，差归零 *)
    destruct Hlt as [e [He [N HN]]].
    unfold real_eq. intros eps Heps. exists N. intros n Hn.
    specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HeQ : 0 < e) by (apply QltT_to_Qlt; exact He).
    assert (HNQ : e < u n - 0) by (apply QltT_to_Qlt; exact HN).
    assert (Hzq : (u n - 0)%Q == u n) by ring.
    rewrite Hzq in HNQ.
    assert (Hpos : 0 < u n) by exact (Qlt_trans 0 e (u n) HeQ HNQ).
    assert (Habs : Qabs (u n) == u n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    apply Qlt_to_QltT.
    assert (Hzd : (Qabs (u n) - u n)%Q == 0%Q) by (rewrite Habs; ring).
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    rewrite uabp7an_qneg0.
    apply QltT_to_Qlt. exact Heps.
  - (* 弱支 real_eq：对半 eps + Qabs_triangle 双倍放行 *)
    unfold real_eq. intros eps Heps.
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply Qlt_to_QltT; apply uabp7an_qlt_half; apply QltT_to_Qlt; exact Heps).
    destruct (Heq (eps / 2)%Q Hhalf) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HNQ : Qabs (0 - u n) < eps / 2) by (apply QltT_to_Qlt; exact HN).
    assert (Hzm : (0 - u n)%Q == (- u n)%Q) by ring.
    rewrite Hzm in HNQ.
    rewrite (Qabs_opp (u n)) in HNQ.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (u n) + Qabs (u n)) _).
    + assert (Hsp : (Qabs (u n) - u n)%Q
                    == (Qabs (u n) + (- u n))%Q) by ring.
      rewrite Hsp.
      apply (Qle_trans _ (Qabs (Qabs (u n)) + Qabs (- u n))).
      * apply Qabs_triangle.
      * rewrite (Qabs_pos (Qabs (u n)) (Qabs_nonneg (u n))).
        rewrite (Qabs_opp (u n)).
        apply Qle_refl.
    + rewrite <- (uabp7an_half_add eps).
      exact (Qplus_lt_compat (Qabs (u n)) (eps / 2)
                             (Qabs (u n)) (eps / 2) HNQ HNQ).
Qed.

(* 接口字段语句形（le/abs/req 取 Instance RealEnhancedReal 字段）：                 *)
(* 无条件「le zero a -> req (abs a) a」全称件——接口字段 abs_pos 仅覆盖              *)
(* 严格正前提 lt zero a，本件将其前提减弱为 le zero a。                            *)
Lemma uabp7an_abs_nonneg_uncond : forall a : Real,
  le zero a -> req (abs a) a.
Proof. intros a H. exact (uabp7an_core a H). Qed.

(* ============================================================ *)
(* §3 桥①（抽象接口层）：无条件件 ⟹ 接口 eps 形 abs_nonneg（带 le zero a 前提）      *)
(*   任意载体 R 通用；由 req_plus_le_lt_pos 与接口 lt_le_iff/le_id_r 推得。           *)
(* ============================================================ *)

Section Uabp7anUncondToEps.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Lemma uabp7an_uncond_to_eps : forall a : R,
  le zero a -> req (abs a) a ->
  forall eps : R, lt zero eps -> le zero (plus (abs a) eps).
Proof.
  intros a Hle Heq eps Heps.
  apply (lt_le_iff zero (plus (abs a) eps)). left.
  apply (req_plus_le_lt_pos (abs a) eps).
  - apply (le_id_r zero a (abs a) (req_sym (abs a) a Heq) Hle).
  - exact Heps.
Qed.

End Uabp7anUncondToEps.

(* ============================================================ *)
(* §4 桥②（具体层）：Bishop 逐 eps 非负形 ⟹ 无条件件（逆向桥）                       *)
(*   前提形状=接口 abs_nonneg 字段用于 a 本身（forall eps>0, le zero (a+eps)）。        *)
(*   路线：取四分之一常值见证，经 real_le 的 Or 两支分别提取逐点下界                     *)
(*   （-a_n < eps/2），再由 uabp7an_pt_tail 符号分段收束；Q 层序可判定，零经典逻辑。     *)
(* ============================================================ *)

Lemma uabp7an_eps_to_uncond : forall a : Real,
  (forall eps : Real, lt zero eps -> le zero (plus a eps)) ->
  req (abs a) a.
Proof.
  intros a Hbis. destruct a as [u Hu].
  assert (Hcore : real_eq (real_abs (existT (fun u : nat -> Q => cauchy u) u Hu)) (existT (fun u : nat -> Q => cauchy u) u Hu)).
  { intros eps Heps.
    assert (HepsQ : 0 < eps) by (apply QltT_to_Qlt; exact Heps).
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply Qlt_to_QltT; apply uabp7an_qlt_half; exact HepsQ).
    assert (Hq2 : 0 < eps / 2) by (apply uabp7an_qlt_half; exact HepsQ).
    assert (Hq4 : 0 < eps / 4).
    { assert (Hz : eps / 4 == eps / 2 / 2) by field.
      rewrite Hz.
      apply uabp7an_qlt_half. exact Hq2. }
    assert (Hq4T : QltT 0 (eps / 4)) by (apply Qlt_to_QltT; exact Hq4).
    assert (Hq42 : eps / 4 < eps / 2) by (apply uabp7an_q4_lt_q2; exact HepsQ).
    (* 四分之一常值实数的严格正见证（real_lt 构造，取 eps/4 之半） *)
    assert (Hltc : lt zero (real_const (eps / 4))).
    { assert (Hltc2 : real_lt real_zero (real_const (eps / 4))).
      { unfold real_lt. exists (eps / 4 / 2)%Q. split.
        - apply Qlt_to_QltT. apply uabp7an_qlt_half. exact Hq4.
        - exists 0%nat. intros n _.
          apply Qlt_to_QltT. apply uabp7an_half_lt_m0. exact Hq4. }
      exact Hltc2. }
    destruct (Hbis (real_const (eps / 4)) Hltc) as [Hb | Hb].
    - (* inl 严格支：e1 < a_n + eps/4 ⟹ -a_n < eps/2 *)
      unfold real_le in Hb. destruct Hb as [e1 [He1 [N1 HN1]]].
      exists N1. intros n Hn. specialize (HN1 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN1Q : e1 < u n + eps / 4 - 0) by (apply QltT_to_Qlt; exact HN1).
      assert (Hzq : (u n + eps / 4 - 0)%Q
                    == (u n + eps / 4)%Q) by ring.
      rewrite Hzq in HN1Q.
      apply QltT_to_Qlt in He1.
      assert (Hpos2 : 0 < u n + eps / 4)
        by exact (Qlt_trans 0 e1 (u n + eps / 4) He1 HN1Q).
      assert (Hneg0 : - (u n + eps / 4) < 0).
      { assert (H0 : - (u n + eps / 4) < (- 0))
          by (apply (Qopp_lt_compat 0 (u n + eps / 4)); exact Hpos2).
        rewrite uabp7an_qneg0 in H0. exact H0. }
      assert (Hs : eps / 4 + -(u n + eps / 4) < eps / 4 + 0)
        by (apply (proj2 (Qplus_lt_r (- (u n + eps / 4)) 0 (eps / 4)));
            exact Hneg0).
      assert (Hzs : (eps / 4 + -(u n + eps / 4))%Q
                    == (- u n)%Q) by ring.
      rewrite Hzs in Hs.
      assert (Hzs2 : (eps / 4 + 0)%Q == (eps / 4)%Q) by ring.
      rewrite Hzs2 in Hs.
      assert (Hneg : - u n < eps / 2)
        by exact (Qlt_trans (- u n) (eps / 4) (eps / 2) Hs Hq42).
      apply (uabp7an_pt_tail (u n) eps HepsQ Hneg).
    - (* inr 相等支：|a_n + eps/4| < eps/4 ⟹ 下界翻转 ⟹ -a_n < eps/2 *)
      unfold real_eq in Hb.
      destruct (Hb (eps / 4)%Q Hq4T) as [N2 HN2].
      exists N2. intros n Hn. specialize (HN2 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN2Q : Qabs (0 - (u n + eps / 4)) < eps / 4)
        by (apply QltT_to_Qlt; exact HN2).
      assert (Hsp0 : (0 - (u n + eps / 4))%Q
                     == (-(u n + eps / 4))%Q) by ring.
      rewrite Hsp0 in HN2Q.
      rewrite (Qabs_opp (u n + eps / 4)) in HN2Q.
      pose proof (uabp7an_abs_lb (u n + eps / 4) (eps / 4) Hq4 HN2Q) as Hlb.
      assert (Hs : -(eps / 4) + -(eps / 4) < -(eps / 4) + (u n + eps / 4))
        by (apply (proj2 (Qplus_lt_r (- (eps / 4)) (u n + eps / 4) (- (eps / 4))));
            exact Hlb).
      assert (Hs1 : (-(eps / 4) + -(eps / 4))%Q == (-(eps / 2))%Q) by field.
      rewrite Hs1 in Hs.
      assert (Hs2 : (-(eps / 4) + (u n + eps / 4))%Q
                    == u n) by ring.
      rewrite Hs2 in Hs.
      assert (Hneg : - u n < eps / 2).
      { assert (H0 : - u n < - (-(eps / 2)))
          by (apply (Qopp_lt_compat (-(eps / 2)) (u n)); exact Hs).
        rewrite Qopp_involutive in H0.
        exact H0. }
      apply (uabp7an_pt_tail (u n) eps HepsQ Hneg). }
  exact Hcore.
Qed.

(* ============================================================ *)
(* §5 假设闭包核验（Print Assumptions，各件应为空）                      *)
(* ============================================================ *)

Print Assumptions uabp7an_qneg0.
Print Assumptions uabp7an_qlt_half.
Print Assumptions uabp7an_half_add.
Print Assumptions uabp7an_half_lt.
Print Assumptions uabp7an_half_le.
Print Assumptions uabp7an_q4_lt_q2.
Print Assumptions uabp7an_half_lt_m0.
Print Assumptions uabp7an_abs_lb.
Print Assumptions uabp7an_pt_tail.
Print Assumptions uabp7an_core.
Print Assumptions uabp7an_abs_nonneg_uncond.
Print Assumptions uabp7an_uncond_to_eps.
Print Assumptions uabp7an_eps_to_uncond.

(* ============================ §6 lo/hi 桥接引理组：二分之一抽象形 half:=inv_pos (plus one one) two_pos 的有界性与序关系事实 ============================ *)
Require Import S01_BaseRing.

(* ############ 段一：uahlb_le_neq_lt —— Or 编码 le＋neq⟹lt ############### *)
(* 约定：本库序 le 取 Or(lt,Id) 编码（S01_BaseRing 实数层；UpTVDoeblin 中     *)
(* tvd_abs_le_id 同此编码）。Or 编码 le 逐支分情形：lt 支直取；eq 支与 neq    *)
(* 前提矛盾消去（Empty_set 归谬，构造性，无经典逻辑）。                       *)

Section UahlbBridgeOr.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Theorem uahlb_le_neq_lt : forall a b : R,
  Or (lt a b) (Id a b) -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hle Hneq.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - destruct (Hneq Heq).
Qed.

End UahlbBridgeOr.

(* ############ 段二：uahlb_le_abs_neq_lt —— 抽象 le＋neq⟹lt ############## *)
(* 抽象 le 无逐支分解字段，经 DecidableOrder 的 ord_le_dec 在 (b,a) 位分情形：*)
(* le b a 支与 le a b 由 le_antisym 得 Id a b，与 neq 前提矛盾消去；非 le 支  *)
(* 经 not_le_lt 直接推得 lt a b。构造性分情形，无经典逻辑。                   *)

Section UahlbBridgeLe.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 投影别名定式：match Build_DecidableOrder 逐字段取用，防字段名遮蔽        *)
Definition uahlb_ord_dec : forall a b : R, Or (le a b) (Not (le a b)) :=
  match DO with
  | Build_DecidableOrder _ old _ _ _ _ => old
  end.

Definition uahlb_not_le_lt : forall a b : R, Not (le a b) -> lt b a :=
  match DO with
  | Build_DecidableOrder _ _ _ _ nll _ => nll
  end.

Theorem uahlb_le_abs_neq_lt : forall a b : R,
  le a b -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hle Hneq.
  destruct (uahlb_ord_dec b a) as [Hle' | Hnle'].
  - destruct (Hneq (le_antisym a b Hle Hle')).
  - exact (uahlb_not_le_lt b a Hnle').
Qed.

End UahlbBridgeLe.

(* ############ 段三：uahlb_delta_star_bounded_half —— δ*∈(0,1) 全前提形 ### *)
(* half:=inv_pos (plus one one) two_pos（two_pos/inv_pos_pos 提供正性）；      *)
(* half2:=mult half half（δ*=lo² 定义位的抽象形）。先证 uahlb_half2_le_one     *)
(* 与 uahlb_half2_neq_one，再经 uahlb_eq_dec 等辅助件合成全件。               *)

Section UahlbHalfStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* eq_dec 投影别名（同 uahlb_ord_dec 的 match 投影定式） *)
Definition uahlb_eq_dec : forall a b : R, Or (Id a b) (Not (Id a b)) :=
  match DO with
  | Build_DecidableOrder _ _ _ ed _ _ => ed
  end.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 证明素材（半的加倍恒等式组）：                                             *)
(*   0<half（inv_pos_pos 于 two_pos）；0<half2（mult_positive）；              *)
(*   half2+half2=half（half_twice half）；half+half=1（mult_one 与            *)
(*   half_twice one）；1=(half2+half2)+(half2+half2)（恒等重排）。             *)
(*   下列 uahlb_half2_le_one 与 uahlb_half2_neq_one 直接使用这组恒等式。       *)

Lemma uahlb_half2_le_one : le half2 one.
Proof.
  assert (Lh : le zero half2).
  { exact (lt_le_iff zero half2
             (@inl (lt zero half2) (Id zero half2)
                (mult_positive half half
                   (inv_pos_pos (plus one one) two_pos)
                   (inv_pos_pos (plus one one) two_pos)))). }
  assert (L1 : le half2 (plus half2 half2)).
  { exact (le_plus_nonneg_r half2 half2 Lh). }
  assert (L2 : le half2 half).
  { exact (le_id_r half2 (plus half2 half2) half (half_twice half) L1). }
  assert (Lh2 : le zero half).
  { exact (lt_le_iff zero half
             (@inl (lt zero half) (Id zero half)
                (inv_pos_pos (plus one one) two_pos))). }
  assert (L3 : le half (plus half half)).
  { exact (le_plus_nonneg_r half half Lh2). }
  exact (le_trans half2 half one L2
           (le_id_r half (plus half half) one
              (id_trans (id_cong (fun x => plus x x)
                          (id_sym (mult_one half)))
                 (half_twice one))
              L3)).
Qed.

Lemma uahlb_half2_neq_one : Not (Id half2 one).
Proof.
  intro Hid.
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_trans (id_cong (fun x => plus x x)
                          (id_sym (mult_one half)))
                        (half_twice one)))
             (id_sym (id_cong (fun x => plus x x) (half_twice half)))). }
  assert (Hfour : Id one (plus (plus one one) (plus one one))).
  { exact (id_trans Hone2
             (id_cong (fun x => plus (plus x x) (plus x x)) Hid)). }
  assert (Hstep3 : Id zero
             (plus (plus (plus one one) (plus one one)) (opp one))).
  { exact (id_trans (id_sym (plus_opp one))
             (id_cong (fun x => plus x (opp one)) Hfour)). }
  assert (Hinner : Id (plus (plus one one) (opp one)) one).
  { exact (id_trans (id_sym (plus_assoc one one (opp one)))
             (id_trans (id_cong (fun w => plus one w) (plus_opp one))
                (plus_zero one))). }
  assert (Hthree : Id zero (plus (plus one one) one)).
  { exact (id_trans Hstep3
             (id_trans
                (id_sym (plus_assoc (plus one one) (plus one one)
                          (opp one)))
                (id_cong (fun w => plus (plus one one) w) Hinner))). }
  exact (lt_irrefl zero
           (lt_id_r zero (plus (plus one one) one) zero (id_sym Hthree)
              (plus_positive (plus one one) one two_pos one_pos))).
Qed.

(* uahlb_delta_star_bounded_half：合取 0<half2 且 half2<1 的完整前提形。      *)
(* half2<1 支：eq_dec 分情形重建 Or 编码 le——Id 支直取（inr）；neq 支经       *)
(* uahlb_le_abs_neq_lt 升为 lt 直取（inl）；再由 uahlb_le_neq_lt 推得：lt 支   *)
(* 直取、Id 支与 uahlb_half2_neq_one 前提矛盾消去。0<half2 支：mult_positive。 *)
Theorem uahlb_delta_star_bounded_half :
  And (lt zero half2) (lt half2 one).
Proof.
  assert (Hneq : Not (Id half2 one)).
  { exact uahlb_half2_neq_one. }
  assert (Hle1 : le half2 one).
  { exact uahlb_half2_le_one. }
  assert (O : Or (lt half2 one) (Id half2 one)).
  { destruct (uahlb_eq_dec half2 one) as [Hid | Hneq'].
    - exact (@inr (lt half2 one) (Id half2 one) Hid).
    - exact (@inl (lt half2 one) (Id half2 one)
               (uahlb_le_abs_neq_lt half2 one Hle1 Hneq')). }
  split.
  - exact (mult_positive half half
             (inv_pos_pos (plus one one) two_pos)
             (inv_pos_pos (plus one one) two_pos)).
  - exact (uahlb_le_neq_lt half2 one O Hneq).
Qed.

End UahlbHalfStar.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahlb_le_neq_lt.
Print Assumptions uahlb_le_abs_neq_lt.
Print Assumptions uahlb_half2_le_one.
Print Assumptions uahlb_half2_neq_one.
Print Assumptions uahlb_delta_star_bounded_half.

(* ============================ §7 P7BoundedSoftmaxDeep 出节定理的实例化、 独立重证与求和交换恒等三形 ============================ *)
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
Require Import AttnDoeblin.
Require Import P7BoundedSoftmaxDeep.
From Stdlib Require Import List.

(* ################ 段一：展幅 1≤hi² 与因子-倒数（九参前提节） ################ *)

Section UaftScale.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* uaft_one_le_hi_sq_one：p7d_one_le_hi_sq @ 温度:=1、利差:=1 的实例形       *)
(*   （温度与利差均取 one，one_pos 供两处正性位，invT:=inv_pos one one_pos；  *)
(*   指数族保持抽象——全库无具体实数实例） *)
Theorem uaft_one_le_hi_sq_one :
  forall (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos one one_pos) one))
               (expf (mult (inv_pos one one_pos) one))).
Proof.
  intros expf expf_pos expf_zero expf_plus expf_mono_lt.
  exact (p7d_one_le_hi_sq one one_pos one one_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* uaft_one_le_hi_sq_indep：与 p7d_one_le_hi_sq 同结论的独立重证——先由      *)
(*   恒等链得 lo·hi=one（expf_plus、distrib、plus_comm、plus_opp、mult_zero、 *)
(*   expf_zero），再经 lo<hi 单调链（lt_mult_compat、mult_comm、lt_id_l）     *)
(*   与 le_mult_compat_r 推出 1≤hi·hi；不使用源模块 bs_lo_hi_eq／bs_lo_lt_hi。 *)
Theorem uaft_one_le_hi_sq_indep :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) Delta))).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus expf_mono_lt.
  assert (Hlhi : Id (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))) one).
  { exact (id_trans (id_sym (expf_plus (mult (inv_pos temp temp_pos) (opp Delta))
                                       (mult (inv_pos temp temp_pos) Delta)))
             (id_trans (id_cong expf (id_sym (distrib (inv_pos temp temp_pos)
                                                     (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_comm (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_opp Delta)))
                       (id_trans (id_cong expf (mult_zero (inv_pos temp temp_pos)))
                                 expf_zero))))). }
  assert (Hopplt : lt (opp Delta) Delta).
  { exact (le_lt_trans (opp Delta) zero Delta
             (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                (opp_le_compat zero Delta (lt_le_iff zero Delta (inl Delta_pos))))
             Delta_pos). }
  assert (Hlohi : lt (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                     (expf (mult (inv_pos temp temp_pos) Delta))).
  { apply (expf_mono_lt (mult (inv_pos temp temp_pos) (opp Delta))
                        (mult (inv_pos temp temp_pos) Delta)).
    exact (lt_id_l (mult (inv_pos temp temp_pos) (opp Delta))
                   (mult (opp Delta) (inv_pos temp temp_pos))
                   (mult (inv_pos temp temp_pos) Delta)
                   (mult_comm (inv_pos temp temp_pos) (opp Delta))
                   (lt_id_r (mult (opp Delta) (inv_pos temp temp_pos))
                            (mult Delta (inv_pos temp temp_pos))
                            (mult (inv_pos temp temp_pos) Delta)
                            (mult_comm Delta (inv_pos temp temp_pos))
                            (lt_mult_compat (opp Delta) Delta
                               (inv_pos temp temp_pos)
                               (inv_pos_pos temp temp_pos) Hopplt))). }
  apply (le_trans _ (mult (expf (mult (inv_pos temp temp_pos) Delta))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))).
  - exact (le_id_l one (mult (expf (mult (inv_pos temp temp_pos) Delta))
                             (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (mult (expf (mult (inv_pos temp temp_pos) Delta))
                   (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (id_sym (id_trans (mult_comm (expf (mult (inv_pos temp temp_pos) Delta))
                                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))
                               Hlhi))
             (le_refl (mult (expf (mult (inv_pos temp temp_pos) Delta))
                            (expf (mult (inv_pos temp temp_pos) (opp Delta)))))).
  - exact (le_mult_compat_r (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) (opp Delta)))
               (expf (mult (inv_pos temp temp_pos) Delta))
               (lt_le_iff zero (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl (expf_pos (mult (inv_pos temp temp_pos) Delta))))
               (lt_le_iff (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl Hlohi))).
Qed.

(* uaft_factor_over_hi_one：p7d_factor_over_hi @ 温度:=1 的实例形——         *)
(*   因子-倒数恒等式 e^{a/T}·(e^{Δ/T})⁻¹ = e^{(a−Δ)/T} 的具体温度形；        *)
(*   hi 正性前提由 bs_hi_pos @ one/one 供给。 *)
Theorem uaft_factor_over_hi_one :
  forall (a b : R) (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult (inv_pos one one_pos) a))
           (inv_pos (expf (mult (inv_pos one one_pos) one))
                    (AttnDoeblin.bs_hi_pos one one_pos one expf expf_pos)))
     (expf (mult (inv_pos one one_pos) (plus a (opp one)))).
Proof.
  intros a b expf expf_pos expf_zero expf_plus.
  exact (p7d_factor_over_hi one one_pos one a b expf expf_pos expf_zero expf_plus).
Qed.

End UaftScale.

(* ################ 段二：单例非空两向互证（nR>0 与 enum 非空） ############## *)
(* 源模块出节面中反向件 p7d_nR_pos_gives_enum_nonempty 不需求和实例，正向件     *)
(*   p7d_enum_nonempty_gives_nR_pos 须 sel 全称位；本件以单例计算位补具体形。  *)

Section UaftTail.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* uaft_singleton_nR_pos：单例载体 nat_to_R>0——length (s::nil) 定义性归约    *)
(*   为 S (length nil)，与 AttnDoeblin.nat_to_R_pos 全称形直接合一。 *)
Theorem uaft_singleton_nR_pos : forall s : S,
  lt zero (AttnDoeblin.nat_to_R (length (s :: nil))).
Proof.
  intro s.
  exact (AttnDoeblin.nat_to_R_pos (length (nil : list S))).
Qed.

(* uaft_singleton_nonempty_hand：独立重证——由 Id (s::nil) nil 经长度映射     *)
(*   得 Id one zero，与 one_pos 矛盾（经 lt_id_l，收于 lt_irrefl）。 *)
Theorem uaft_singleton_nonempty_hand : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intros s H.
  assert (Hone0 : Id one zero).
  { exact (id_trans (id_sym (plus_zero one))
             (id_cong (fun l : list S => AttnDoeblin.nat_to_R (length l)) H)). }
  exact (lt_irrefl one (lt_id_l one zero one Hone0 one_pos)).
Qed.

(* uaft_singleton_nonempty_via_mother：同命题经                              *)
(*   p7d_nR_pos_gives_enum_nonempty @ 单例载体——与 uaft_singleton_nonempty_hand 互为独立证明。 *)
Theorem uaft_singleton_nonempty_via_mother : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intro s.
  exact (p7d_nR_pos_gives_enum_nonempty (s :: nil)
           (AttnDoeblin.nat_to_R_pos (length (nil : list S)))).
Qed.

End UaftTail.

(* ################ 段三：求和交换恒等三形（显式全称/载体恒等/单例） ######### *)
(* 背景：SumOver 八字段实例构造不可行（zero_nonneg 全称位须 enum 满射数据）；  *)
(*   故对本件交换恒等分三形论证：显式全称／载体恒等／单例计算。               *)

Section UaftCarrier.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* uaft_swap_of_sum_eq_list_explicit：源模块 p7d_swap_of_sum_eq_list 的全称形  *)
(*   ——求和实例 SO、enum 与 sum_eq_list 证书由节内 Variable 升为 forall      *)
(*   显式前提，对任意 f 成立。 *)
Theorem uaft_swap_of_sum_eq_list_explicit :
  forall (SO : SumOver RI SS) (enum : list S)
         (sum_eq_list : forall g : S -> R,
            Id (@sum_over_S RI SS SO g) (AttnDoeblin.bs_list_sum g enum))
         (f : S -> S -> R),
  Id (@sum_over_S RI SS SO (fun s : S => @sum_over_S RI SS SO (fun s' : S => f s s')))
     (@sum_over_S RI SS SO (fun s' : S => @sum_over_S RI SS SO (fun s : S => f s s'))).
Proof.
  intros SO enum sum_eq_list f.
  exact (p7d_swap_of_sum_eq_list enum sum_eq_list f).
Qed.

(* uaft_swap_list_carrier_id：以 bs_list_sum 折叠为求和载体——交换恒等即     *)
(*   双重列表和的 Fubini 恒等式（经 p7d_lsum_fubini_gen），无需 SumOver 实例。 *)
Theorem uaft_swap_list_carrier_id :
  forall (enum : list S) (f : S -> S -> R),
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum)
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum).
Proof.
  intros enum f.
  exact (p7d_lsum_fubini_gen f enum enum).
Qed.

(* uaft_swap_singleton_carrier：enum:=(szero::nil)——内外两折叠在单例载体上   *)
(*   定义性归约为同一形（id_refl，不经引理）。 *)
Theorem uaft_swap_singleton_carrier :
  forall f : S -> S -> R,
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') (szero :: nil))
        (szero :: nil))
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') (szero :: nil))
        (szero :: nil)).
Proof.
  intro f.
  exact id_refl.
Qed.

End UaftCarrier.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uaft_one_le_hi_sq_one.
Print Assumptions uaft_one_le_hi_sq_indep.
Print Assumptions uaft_factor_over_hi_one.
Print Assumptions uaft_singleton_nR_pos.
Print Assumptions uaft_singleton_nonempty_hand.
Print Assumptions uaft_singleton_nonempty_via_mother.
Print Assumptions uaft_swap_of_sum_eq_list_explicit.
Print Assumptions uaft_swap_list_carrier_id.
Print Assumptions uaft_swap_singleton_carrier.

(* ============================ §8 Paper7Ablation 出节定理的全称副本、构造性 ============================ *)
Require Import S01_BaseRing.
Require Import Paper7Ablation.

(* ################ κ 选择器供给副本（δ* 面 + 1−δ* 面） ################ *)
(* 节前导与上游 P7aKappa/P7aExpf 节一致（隐参上下文＋基类实例声明）。       *)
Section P7aMirrorKappa.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* uabp7_delta_star_pos_mirror：p7a_delta_star_pos 的全称副本（出口无序可判定参数） *)
Theorem uabp7_delta_star_pos_mirror :
  forall lo : R, lt zero lo -> lt zero (mult lo lo).
Proof.
  intros lo Hlo.
  exact (mult_positive lo lo Hlo Hlo).
Qed.

(* uabp7_delta_star_pos_half：p7a_delta_star_pos @ lo:=二分之一（构造性实例） *)
Theorem uabp7_delta_star_pos_half :
  lt zero (mult (inv_pos (plus one one) two_pos)
                (inv_pos (plus one one) two_pos)).
Proof.
  exact (mult_positive (inv_pos (plus one one) two_pos)
           (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* uabp7_omd_pos_mirror：p7a_omd_pos 的全称副本（上游证明不使用 lo_pos，      *)
(*   出节无该前提；出口带可判定序参数，以 @ 全参显式应用）               *)
Theorem uabp7_omd_pos_mirror :
  forall lo : R, lt (mult lo lo) one ->
    lt zero (minus one (mult lo lo)).
Proof.
  intros lo Hds.
  exact (@p7a_omd_pos RI DO lo Hds).
Qed.

(* uabp7_omd_lt_one_mirror：p7a_omd_lt_one 的全称副本 *)
Theorem uabp7_omd_lt_one_mirror :
  forall lo : R, lt zero lo -> lt (minus one (mult lo lo)) one.
Proof.
  intros lo Hlo.
  exact (@p7a_omd_lt_one RI DO lo Hlo).
Qed.

(* uabp7_omd_lt_one_half：p7a_omd_lt_one @ 二分之一（构造性实例；κ=3/4 上界） *)
Theorem uabp7_omd_lt_one_half :
  lt (minus one (mult (inv_pos (plus one one) two_pos)
                      (inv_pos (plus one one) two_pos))) one.
Proof.
  exact (@p7a_omd_lt_one RI DO (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* uabp7_expf_wd_mirror：p7a_expf_wd 的接口副本（同余性无需独立假设） *)
Theorem uabp7_expf_wd_mirror :
  forall (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R,
                        Id (expf (plus a b)) (mult (expf a) (expf b)))
         (a b : R), Id a b -> Id (expf a) (expf b).
Proof.
  intros expf expf_pos expf_zero expf_plus a b Hab.
  assert (He := expf_pos (opp b)).
  assert (Ha1 : Id (mult (expf a) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus a (opp b)))).
    apply (id_trans (id_cong expf
             (id_trans (id_cong (fun x => plus x (opp b)) Hab)
                       (plus_opp b)))).
    exact expf_zero. }
  assert (Hb1 : Id (mult (expf b) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus b (opp b)))).
    apply (id_trans (id_cong expf (plus_opp b)) expf_zero). }
  apply (mult_cancel_l (expf (opp b)) (expf a) (expf b) He).
  apply (id_trans (id_trans (mult_comm (expf (opp b)) (expf a)) Ha1)
                  (id_sym (id_trans (mult_comm (expf (opp b)) (expf b)) Hb1))).
Qed.

End P7aMirrorKappa.

(* ============================================================ *)
(* 节二：κ:=1−δ*∈(0,1) 前提装配（对应论文 §6.3 引用面）                       *)
(*   变量面：invT:=inv_pos temp temp_pos、lo:=expf(invT·oppΔ)、               *)
(*   hi:=expf(invT·Δ)、δ*:=lo·lo，与 AttnDoeblin 中 BoundedSoftmax 的          *)
(*   别名面同构。路线：先独立证明六件基础事实                                  *)
(*   （uabp7_kappa_lo_pos/hi_pos/opp_lt/lo_lt_hi/lo_hi_eq/ds_lt_one，          *)
(*   对应上游 bs_lo_pos/bs_opp_lt/bs_lo_lt_hi/bs_lo_hi_eq 的实例形），         *)
(*   再以 @ 全参显式应用对接上游 p7a_omd_pos/p7a_omd_lt_one（两件），          *)
(*   以 Set 层 And 收束为前提合取 Corollary uabp7_kappa_in01_package           *)
(*   （语句即「0 < 1−δ* ∧ 1−δ* < 1」）。                                      *)
(*   替代注记一：lt_id_r_loc 与 lt_id_r 同形，一律用后者；                    *)
(*   替代注记二：uabp7_kappa_opp_lt 不走 opp_le_compat 加 opp 零恒等的路线，   *)
(*   改走 lt_zero_opp + lt_le_iff + le_lt_trans 的两步路线；                  *)
(*   两处替代皆免增 Require。                                                *)
(* ============================================================ *)
(* ------------------------------------------------------------ *)
(* 节二假设面申报（如实登记，未消解为定理）：节内 Variable 九位——               *)
(*   temp/temp_pos/Delta/Delta_pos（数据与正性证书四位）与 expf/expf_pos/       *)
(*   expf_zero/expf_plus/expf_mono_lt（指数接口五位），系上游 P7aKappa/          *)
(*   P7aExpf 节的接口面对应位，全部被本节定理证明项真实使用，非冗余位。          *)
(*   消解受阻双证：①树内具体柯西指数（S07）不在本件依赖面                        *)
(*  （S01_BaseRing＋Paper7Ablation），增补依赖撞零新增红线；                      *)
(*   ②uabp7_kappa_omd_pos_inst/omd_lt_one_inst 使用上游 p7a_omd_pos/             *)
(*   p7a_omd_lt_one，需 DecidableOrder 实例，而全库无 Real 的                    *)
(*   DecidableOrder 具体实例（序可判定缺位，受限 LPO 族门槛）——                  *)
(*   皆为显式前提义务，如实保留，不作硬证。                                      *)
(* ------------------------------------------------------------ *)
Section P7aKappaPackage.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* 别名面：与 AttnDoeblin 中 BoundedSoftmax 的别名面同构 *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* uabp7_kappa_lo_pos：0<lo（即 bs_lo_pos 的实例形，由 expf_pos 一步） *)
Theorem uabp7_kappa_lo_pos : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* uabp7_kappa_hi_pos：0<hi（即 bs_hi_pos 的实例形） *)
Theorem uabp7_kappa_hi_pos : lt zero hi.
Proof.
  exact (expf_pos (mult invT Delta)).
Qed.

(* uabp7_kappa_opp_lt：oppΔ < Δ（即 bs_opp_lt 的实例形；lt_zero_opp +
   lt_le_iff + le_lt_trans 两步路线，不依赖 opp 零恒等） *)
Theorem uabp7_kappa_opp_lt : lt (opp Delta) Delta.
Proof.
  exact (le_lt_trans (opp Delta) zero Delta
           (lt_le_iff (opp Delta) zero (inl (lt_zero_opp Delta Delta_pos)))
           Delta_pos).
Qed.

(* uabp7_kappa_lo_lt_hi：lo<hi（即 bs_lo_lt_hi 的实例形；四步链：
   expf_mono_lt + lt_id_l + lt_id_r + lt_mult_compat，inv_pos_pos 供 invT 正性） *)
Theorem uabp7_kappa_lo_lt_hi : lt lo hi.
Proof.
  apply (expf_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (lt_id_r _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT (inv_pos_pos temp temp_pos)
           uabp7_kappa_opp_lt).
Qed.

(* uabp7_kappa_lo_hi_eq：lo·hi=one（即 bs_lo_hi_eq 的实例形；expf 加法同态核心） *)
Theorem uabp7_kappa_lo_hi_eq : Id (mult lo hi) one.
Proof.
  apply (id_trans (id_sym (expf_plus (mult invT (opp Delta)) (mult invT Delta)))).
  apply (id_trans (id_cong expf (id_sym (distrib invT (opp Delta) Delta)))).
  apply (id_trans (id_cong expf (id_cong (fun w => mult invT w)
                 (id_trans (plus_comm (opp Delta) Delta) (plus_opp Delta))))).
  exact (id_trans (id_cong expf (mult_zero invT)) expf_zero).
Qed.

(* uabp7_kappa_ds_lt_one：δ*:=lo·lo < 1（即 bs_delta_star_lt_one 的实例形） *)
Theorem uabp7_kappa_ds_lt_one : lt delta_star one.
Proof.
  apply (lt_id_r _ _ _ uabp7_kappa_lo_hi_eq).
  apply (lt_id_r _ _ _ (mult_comm hi lo)).
  exact (lt_mult_compat lo hi lo uabp7_kappa_lo_pos uabp7_kappa_lo_lt_hi).
Qed.

(* uabp7_kappa_omd_pos_inst：p7a_omd_pos @ 全参显式，以 δ*<1 为前提（0<1−δ*） *)
Theorem uabp7_kappa_omd_pos_inst : lt zero (minus one delta_star).
Proof.
  exact (@p7a_omd_pos RI DO lo uabp7_kappa_ds_lt_one).
Qed.

(* uabp7_kappa_omd_lt_one_inst：p7a_omd_lt_one @ 全参显式，以 0<lo 为前提（1−δ*<1） *)
Theorem uabp7_kappa_omd_lt_one_inst : lt (minus one delta_star) one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo uabp7_kappa_lo_pos).
Qed.

(* uabp7_kappa_in01_package（收束）：κ := 1−δ* ∈ (0,1) 的前提合取。
   语句即「0 < 1−δ* ∧ 1−δ* < 1」（Set 层 And）。 *)
Corollary uabp7_kappa_in01_package :
  And (lt zero (minus one delta_star)) (lt (minus one delta_star) one).
Proof.
  exact (pair uabp7_kappa_omd_pos_inst uabp7_kappa_omd_lt_one_inst).
Qed.

End P7aKappaPackage.

(* ============================================================ *)
(* 节三：有界 softmax 上界件 p7a_lo_lt_one 于 temp:=one、Delta:=one 的        *)
(*   具体实例（对应上游 P7aSoftBound 的形）。                                 *)
(*   链路：one_pos + inv_pos_pos + lt_zero_opp。三件：                        *)
(*   uabp7_sb_one_lo_lt_one 为 one/one 处全称 invT 副本                       *)
(*   （出节次序 Delta→Delta_pos→expf→expf_zero→expf_mono_lt→invT→Hin，        *)
(*   temp 未被上游本位使用故无该参）；uabp7_sb_one_lo_lt_one_instant 为       *)
(*   invT:=inv_pos one one_pos 处的实例形；uabp7_sb_one_lo_lt_one_chain       *)
(*   为独立四步链重证（零上游使用，对齐上游 p7a_lo_lt_one 的证明结构）。       *)
(* ============================================================ *)
(* ------------------------------------------------------------ *)
(* 节三假设面申报：expf/expf_zero/expf_mono_lt 三位为指数接口字段               *)
(*   （与上游对应节同形），被本节三定理真实使用；树内具体柯西指数               *)
(*   不在本件依赖面，消解受阻，如实保留为显式前提义务。                          *)
(* ------------------------------------------------------------ *)
Section P7aSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable expf : R -> R.
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* uabp7_sb_one_lo_lt_one：p7a_lo_lt_one @ temp:=one、Delta:=one 的实例副本 *)
Theorem uabp7_sb_one_lo_lt_one : forall invT : R,
  lt zero invT -> lt (expf (mult invT (opp one))) one.
Proof.
  intros invT Hin.
  assert (Hond := lt_zero_opp one one_pos).
  assert (Hm : lt (mult (opp one) invT) zero).
  { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
             (id_trans (mult_comm zero invT) (mult_zero invT))).
    exact (lt_mult_compat (opp one) zero invT Hin Hond). }
  apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
  apply (expf_mono_lt (mult invT (opp one)) zero).
  apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
                   (mult_comm invT (opp one))).
  exact Hm.
Qed.

(* uabp7_sb_one_lo_lt_one_instant：p7a_lo_lt_one_instant @ one/one
   （one_pos 供两处正性，invT:=inv_pos one one_pos） *)
Theorem uabp7_sb_one_lo_lt_one_instant :
  lt (expf (mult (inv_pos one one_pos) (opp one))) one.
Proof.
  exact (p7a_lo_lt_one_instant one one_pos one one_pos
           expf expf_zero expf_mono_lt).
Qed.

(* uabp7_sb_one_lo_lt_one_chain（独立四步链重证，零上游使用）：
   lt_zero_opp + lt_mult_compat + expf_mono_lt + expf_zero *)
Theorem uabp7_sb_one_lo_lt_one_chain :
  lt (expf (mult (inv_pos one one_pos) (opp one))) one.
Proof.
  assert (Hond := lt_zero_opp one one_pos).
  assert (Hm : lt (mult (opp one) (inv_pos one one_pos)) zero).
  { apply (lt_id_r (mult (opp one) (inv_pos one one_pos))
             (mult zero (inv_pos one one_pos)) zero
             (id_trans (mult_comm zero (inv_pos one one_pos))
                       (mult_zero (inv_pos one one_pos)))).
    exact (lt_mult_compat (opp one) zero (inv_pos one one_pos)
             (inv_pos_pos one one_pos) Hond). }
  apply (lt_id_r (expf (mult (inv_pos one one_pos) (opp one)))
           (expf zero) one expf_zero).
  apply (expf_mono_lt (mult (inv_pos one one_pos) (opp one)) zero).
  apply (lt_id_l (mult (inv_pos one one_pos) (opp one))
           (mult (opp one) (inv_pos one one_pos)) zero
           (mult_comm (inv_pos one one_pos) (opp one))).
  exact Hm.
Qed.

End P7aSbInst.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uabp7_delta_star_pos_mirror.
Print Assumptions uabp7_delta_star_pos_half.
Print Assumptions uabp7_omd_pos_mirror.
Print Assumptions uabp7_omd_lt_one_mirror.
Print Assumptions uabp7_omd_lt_one_half.
Print Assumptions uabp7_expf_wd_mirror.
Print Assumptions uabp7_kappa_lo_pos.
Print Assumptions uabp7_kappa_hi_pos.
Print Assumptions uabp7_kappa_opp_lt.
Print Assumptions uabp7_kappa_lo_lt_hi.
Print Assumptions uabp7_kappa_lo_hi_eq.
Print Assumptions uabp7_kappa_ds_lt_one.
Print Assumptions uabp7_kappa_omd_pos_inst.
Print Assumptions uabp7_kappa_omd_lt_one_inst.
Print Assumptions uabp7_kappa_in01_package.
Print Assumptions uabp7_sb_one_lo_lt_one.
Print Assumptions uabp7_sb_one_lo_lt_one_instant.
Print Assumptions uabp7_sb_one_lo_lt_one_chain.

(* ============================ §9 p7a_expf_wd / p7a_expf_mono_le_do 的柯西实数实例件（S1inst） ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ############ 子件一：e 在零点连续（装配链同余步补足） ########### *)
(* x == 0 ⟹ e^x == 1。自 S03 原语自证，不使用 cauchy_real_exp_wd。 *)
Lemma s1inst_exp_cong_zero : forall x : Real,
  real_eq x real_zero -> real_eq (cauchy_real_exp x) real_one.
Proof.
  intros x Hx. destruct x as [u Hu].
  unfold real_eq in Hx |- *.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu))
    as [M [HMpos HM]].
  assert (HMnonnegT : QleT' 0 M) by (apply qltT_leT'; exact HMpos).
  destruct (exp_series_arch M HMnonnegT) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  assert (HCpos : Qlt 0 C) by (apply QltT_to_Qlt; exact HCposT).
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  assert (HepsC : QltT 0 (eps / (2 * C))).
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  destruct (Hx (eps / (2 * C))%Q HepsC) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1.
  simpl.
  (* 目标：QltT (Qabs (exp_partial n (u n) - 1)) eps *)
  assert (Hshape : Qabs (exp_partial n (u n) - exp_partial n 0)
                   == Qabs (exp_partial n (u n) - 1)).
  { rewrite (exp_partial_zero n). reflexivity. }
  apply (qltT_eq_compat_l (Qabs (exp_partial n (u n) - exp_partial n 0))
                          (Qabs (exp_partial n (u n) - 1))
                          eps Hshape).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - 0) * C) _).
  - apply (Qle_trans _ (Qabs (u n - 0) * exp_series n M) _).
    + exact (exp_partial_lipschitz (u n) 0 M n HMnonnegT (HM n) HMnonnegT).
    + apply (Qmult_le_compat_nonneg (Qabs (u n - 0)) (Qabs (u n - 0))
                                    (exp_series n M) C).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- apply (exp_series_nonneg n M HMnonnegT).
        -- apply QleT'_to_Qle. apply (HC n).
  - apply (Qle_lt_trans _ ((eps / (2 * C)) * C) _).
    + apply (Qmult_le_compat_r (Qabs (u n - 0)) (eps / (2 * C)) C).
      * apply (Qlt_le_weak (Qabs (u n - 0)) (eps / (2 * C))).
        apply QltT_to_Qlt. exact (HN1 n Hn).
      * exact HCnonneg.
    + apply (Qle_lt_trans _ (eps / 2) _).
      * apply qeq_le.
        assert (Hc : (eps / (2 * C)) * C == eps / 2).
        { unfold Qdiv. field.
          all: try (apply q_neq_of_lt; apply (Qmult_lt_0_compat 2 C)).
          all: try (unfold Qlt; simpl; lia).
          all: try (exact HCpos).
          all: try (apply q_neq_of_lt; exact HCpos). }
        exact Hc.
      * apply (q_half_lt_self eps). apply QltT_to_Qlt. exact Heps.
Qed.

(* ############ 子件二：实层乘法左消去（仿 S01 mult_cancel_l） ##### *)
Lemma s1inst_real_mult_cancel_l : forall a b c : Real,
  real_lt real_zero a ->
  real_eq (real_mult a b) (real_mult a c) -> real_eq b c.
Proof.
  intros a b c Ha Habc.
  assert (H1 : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b))
                       (real_mult (real_inv_pos a Ha) (real_mult a c))).
  { apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) (real_mult a b)
             (real_inv_pos a Ha) (real_mult a c)).
    - apply real_eq_refl.
    - exact Habc. }
  assert (Hinv : real_eq (real_mult (real_inv_pos a Ha) a) real_one).
  { apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
    - apply real_mult_comm.
    - exact (real_inv_pos_correct a Ha). }
  assert (Honeb : real_eq (real_mult real_one b) b).
  { apply (real_eq_trans _ (real_mult b real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one b). }
  assert (Honec : real_eq (real_mult real_one c) c).
  { apply (real_eq_trans _ (real_mult c real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one c). }
  assert (Hlb : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b)) b).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) b) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a b).
    - apply (real_eq_trans _ (real_mult real_one b) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) b real_one b).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honeb. }
  assert (Hrc : real_eq (real_mult (real_inv_pos a Ha) (real_mult a c)) c).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) c) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a c).
    - apply (real_eq_trans _ (real_mult real_one c) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) c real_one c).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honec. }
  apply (real_eq_trans b (real_mult (real_inv_pos a Ha) (real_mult a b)) c).
  - apply real_eq_sym. exact Hlb.
  - exact (real_eq_trans _ _ _ H1 Hrc).
Qed.

(* ############ 装配形：三字段 {plus, zero, pos} 消去链输入参数位 ######## *)
(* p7a_expf_wd 的实例化语句：柯西实数 e 的 real_eq 同余性，由      *)
(* cauchy_real_exp_plus / cauchy_real_exp_zero / cauchy_real_exp_pos *)
(* 三字段件与子件一/二重演 p7a_expf_wd 的乘逆消去链，不使用直证形。 *)
Theorem s1inst_p7a_expf_wd : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  assert (Ha1 : real_eq (real_mult (cauchy_real_exp a)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus a (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus a (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus a (real_opp b))).
      apply (real_eq_trans (real_plus a (real_opp b))
             (real_plus b (real_opp b)) real_zero).
      + exact (RealSetoid.real_eq_plus_compat a (real_opp b) b (real_opp b)
                 Hab (real_eq_refl (real_opp b))).
      + exact (real_plus_opp b). }
  assert (Hb1 : real_eq (real_mult (cauchy_real_exp b)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus b (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus b (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus b (real_opp b))).
      exact (real_plus_opp b). }
  apply (s1inst_real_mult_cancel_l (cauchy_real_exp (real_opp b))
           (cauchy_real_exp a) (cauchy_real_exp b)
           (cauchy_real_exp_pos (real_opp b))).
  apply (real_eq_trans
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp a))
           real_one
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp b))).
  - apply (real_eq_trans _ (real_mult (cauchy_real_exp a)
                     (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Ha1.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (cauchy_real_exp b)
                      (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Hb1.
Qed.

(* ############ 直证形：直接使用 cauchy_real_exp_wd（双覆盖之一） ### *)
Theorem s1inst_p7a_expf_wd_direct : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact cauchy_real_exp_wd.
Qed.

(* ############ 互证：抽象消融语句与柯西实例语句对照合取 ############ *)
(* 类型注记：抽象支为 Type 层 forall（接口量化），And 为 Set×Set      *)
(* 装不下，故以 sigT 封装——首支=抽象消融语句的证明（p7a_expf_wd      *)
(* 全参形，Paper7Ablation 实际使用），尾支=柯西实例语句的装配∧直证双覆盖。*)
Corollary s1inst_dual_cover :
  sigT
    (fun _ : forall {RI : S01_BaseRing.RealInterfaceEnhanced}
                    (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI),
       (forall x : @S01_BaseRing.R RI,
          @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x)) ->
       S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                       (@S01_BaseRing.one RI) ->
       (forall a b : @S01_BaseRing.R RI,
          S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                          (@S01_BaseRing.mult RI (expf a) (expf b))) ->
       forall a b : @S01_BaseRing.R RI,
         S01_BaseRing.Id a b -> S01_BaseRing.Id (expf a) (expf b) =>
     And
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))).
Proof.
  (* 抽象消融支：裸引 p7a_expf_wd 会触发 ?RI 急切实例化而与带 RI
     首量化的期望型失配，故以 λ 全参显式应用（@ 全参形）。 *)
  exists (fun (RI : S01_BaseRing.RealInterfaceEnhanced)
             (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
             (expf_pos : forall x : @S01_BaseRing.R RI,
                 @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x))
             (expf_zero : S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                            (@S01_BaseRing.one RI))
             (expf_plus : forall a b : @S01_BaseRing.R RI,
                 S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                                 (@S01_BaseRing.mult RI (expf a) (expf b))) =>
           @p7a_expf_wd RI expf expf_pos expf_zero expf_plus).
  split.
  - exact s1inst_p7a_expf_wd.
  - exact s1inst_p7a_expf_wd_direct.
Qed.

(* ############ mono_le 实例形：mono_lt + Or 分解 + wd 路径 ######## *)
(* real_le := Or (real_lt) (real_eq)（S02_CauchyComplete）：lt 支走参数5 严格单调 *)
(* cauchy_real_exp_mono，eq 支走装配形 wd——DO 三分在柯西实例不可   *)
(* 满足（强三分 LPO 不可证），Or 编码即其模型级对应形。             *)
Theorem s1inst_p7a_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  unfold real_le in Hab |- *.
  destruct Hab as [Hlt | Heq].
  - (* lt 支：参数5 严格单调直给 *)
    left. exact (cauchy_real_exp_mono a b Hlt).
  - (* eq 支：装配形 wd 路径（三字段消去链） *)
    right. exact (s1inst_p7a_expf_wd a b Heq).
Qed.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions s1inst_exp_cong_zero.
Print Assumptions s1inst_real_mult_cancel_l.
Print Assumptions s1inst_p7a_expf_wd.
Print Assumptions s1inst_p7a_expf_wd_direct.
Print Assumptions s1inst_dual_cover.
Print Assumptions s1inst_p7a_expf_mono_le.

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
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Import RealInterfaceEnhancedMod.

(* ============ §1 混合加法保序证书件（cmk 选择器首参接口参数闭证书） ============ *)

(* lt a b -> le c d -> lt (a+c) (b+d)。
   依存申报：S07:6118 real_lt_plus_compat_lt_le 具体层成品直闭
   （ConcMixSelFeed.v:112 同款实例化；接口 lt/le 经 RealEnhancedReal 实例
   与 real_lt/real_le 同源同解析）。此位在库内为诚实证书位
   （UpReqAlgebra ReqStrictOrderBridge：抽象层不可由接口字段导出），
   本件在具体层将其闭合，零承认。 *)
Theorem ubw_b_lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact real_lt_plus_compat_lt_le.
Qed.

(* ============ §2 小机器（req 链辅件与载体） ============ *)

(* 两点混合号载体：正支 true 点 = a（正），负支 false 点 = −b——
   plain 不可证结果注记（UpReqConcSoftmax.v:11-16 已证结论）中的混合号形状 *)
Definition ubw_b_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 左分配律辅件：接口 distrib 字段为右分配形，左形经交换律衔接（req 链四段） *)
Lemma ubw_b_mult_plus_distr_l : forall a b c : Real,
  req (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  exact (req_trans (mult (plus a b) c) (mult c (plus a b))
           (plus (mult a c) (mult b c))
           (mult_comm (plus a b) c)
           (req_trans (mult c (plus a b))
              (plus (mult c a) (mult c b))
              (plus (mult a c) (mult b c))
              (distrib c a b)
              (req_plus_compat (mult c a) (mult a c) (mult c b) (mult b c)
                 (mult_comm c a) (mult_comm c b)))).
Qed.

(* 同右端加项的非严格加法保序：le a b ⟹ le (a+c) (b+c)。
   Or 两支分案（le 定义性 = Or lt req，检验实测双向零摩擦）：
   lt 支走 §1 闭证书，req 支走 plus 同余换形。 *)
Lemma ubw_b_le_plus_r : forall a b c : Real,
  le a b -> le (plus a c) (plus b c).
Proof.
  intros a b c Hle.
  destruct Hle as [Hlt | Heq].
  - apply lt_le_iff. apply inl.
    exact (ubw_b_lt_plus_compat_lt_le a b c c Hlt (le_refl c)).
  - exact (le_id_r (plus a c) (plus a c) (plus b c)
             (req_plus_compat a b c c Heq (req_refl c))
             (le_refl (plus a c))).
Qed.

(* req 升格引理：req a b ⟹ le a b（lt_le_iff inr 支直连，绕行件） *)
Lemma ubw_b_req_le : forall a b : Real,
  req a b -> le a b.
Proof.
  intros a b Hreq.
  exact (lt_le_iff a b (inr Hreq)).
Qed.

(* ============ §3 链身 eps 化边界诚实件组 ============ *)

(* 3a 升级方向边界引理：plain 链结论 ⟹ 逐 eps 链结论（可构造方向）。
   与 3b 否定性见证构成边界两侧：升级方向免费，余量消除论证方向=不可证结果。 *)
Lemma ubw_b_plain_upgrade_eps : forall X Y eps : Real,
  le X Y -> lt zero eps -> le X (plus Y eps).
Proof.
  intros X Y eps Hle Heps.
  exact (le_trans X (plus X zero) (plus Y eps)
           (req_le_plus_nonneg_r X zero (le_refl zero))
           (le_plus_compat X Y zero eps Hle (lt_le_iff zero eps (inl Heps)))).
Qed.

(* 余量消除论证原理（边界对象，仅以类型位出现，本件零假设它成立）：
   逐 eps 上界族闭合到 plain 上界。 *)
Definition ubw_b_deslack_principle : Set :=
  forall X Y : Real,
    (forall eps : Real, lt zero eps -> le X (plus Y eps)) -> le X Y.

(* 3b 否定性见证一般形：余量消除论证原理 ⟹ plain 不可证结果。
   csm 逐 eps 三角（免费档）正是不可证结果 plain 形的逐 eps 逼近像：
   余量消除论证买下的恰是不可证结果本体——链身 eps 化的完成度边界=不可证结果。 *)
Lemma ubw_b_deslack_wall : forall (S : Set) (enum : list S) (f : S -> Real),
  ubw_b_deslack_principle ->
  le (abs (csm_sumf S enum f))
     (csm_sumf S enum (fun s : S => abs (f s))).
Proof.
  intros S enum f Hdeslack.
  apply Hdeslack.
  intros eps Heps.
  exact (csm_abs_sum_le_eps S enum f eps Heps).
Qed.

(* 3c 混合号锚：两点载体上正负支逐点已证结论（sigT 封装防宇宙坑——
   Set 值面合取走依存对，依存对封装同族形） *)
Lemma ubw_b_twopt_mixed_sign : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT (fun _ : lt zero (ubw_b_mixed_f a b true) =>
        lt (ubw_b_mixed_f a b false) zero).
Proof.
  intros a b Ha Hb.
  exact (existT _
           Ha
           (req_lt_id_r_loc (opp b) (opp zero) zero
              (req_trans (opp zero) (plus zero (opp zero)) zero
                 (req_sym (plus zero (opp zero)) (opp zero)
                    (req_plus_zero_l (opp zero)))
                 (plus_opp zero))
              (opp_lt_compat zero b Hb))).
Qed.

(* 3d 否定性见证封装件（cb2w_death_certificate 同范式）：
   「余量消除论证原理在混合号载体上买下 plain 不可证结果实例」×「载体确为混合号」
   双证 sigT 封装——链身 eps 化完成度边界的定理化固化。 *)
Theorem ubw_b_death_certificate : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT
    (fun _ : ubw_b_deslack_principle ->
        le (abs (csm_sumf bool (true :: false :: nil) (ubw_b_mixed_f a b)))
           (csm_sumf bool (true :: false :: nil)
              (fun s : bool => abs (ubw_b_mixed_f a b s))) =>
     sigT (fun _ : lt zero (ubw_b_mixed_f a b true) =>
           lt (ubw_b_mixed_f a b false) zero)).
Proof.
  intros a b Ha Hb.
  exact (existT _
           (fun Hdeslack =>
              ubw_b_deslack_wall bool (true :: false :: nil)
                (ubw_b_mixed_f a b) Hdeslack)
           (existT _ Ha
              (req_lt_id_r_loc (opp b) (opp zero) zero
                 (req_trans (opp zero) (plus zero (opp zero)) zero
                    (req_sym (plus zero (opp zero)) (opp zero)
                       (req_plus_zero_l (opp zero)))
                    (plus_opp zero))
                 (opp_lt_compat zero b Hb)))).
Qed.

(* ============ §4 链身 eps 迭代副本件 + cmk 末端依存定理逐 eps 副本 ============ *)

Section ChainEpsBody.

(* 链身体：步算子 + TV 泛函抽象位（库内同位 = rsq/k_step 核迭代 +
   tv_req；链身单步收缩的逐 eps 形为诚实证书参数位，见文件头申报） *)
Variable S : Set.
Variable tvr : (S -> Real) -> (S -> Real) -> Real.
Variable tstep : (S -> Real) -> (S -> Real).
Variable omd : Real.
Variable eps0 : Real.

Hypothesis Homd_pos : lt zero omd.
Hypothesis Homd_lt_one : lt omd one.

(* 链身 eps 收缩参数位：tv_contraction 链身层的逐 eps 形——
   接口参数假设面与库内 cmk_* 依存 rsq_bounded_softmax_tv_iter 的假设位同构 *)
Hypothesis Hstep_eps : forall mu nu : S -> Real,
  le (tvr (tstep mu) (tstep nu)) (plus (mult omd (tvr mu nu)) eps0).

(* 余量系数：c_0 = 0，c_{n+1} = 1 + omd·c_n——递推精确闭合，
   无几何级数 bounding 冒充 *)
Fixpoint ubw_b_cslack (n : nat) : Real :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus one (mult omd (ubw_b_cslack m))
  end.

(* 链步迭代（rsq_u_titer / k_titer / cmk_titer 同形） *)
Fixpoint ubw_b_titer (n : nat) (mu : S -> Real) : S -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => tstep (ubw_b_titer m mu)
  end.

(* 4a 链身 eps 迭代副本件：n 步后 TV ≤ omd^n·TV₀ + c_n·eps₀（精确余量递推）。
   底 case req 数乘单位换轨；递归步 = 接口参数一次 + IH 经 omd 数乘抬升
   （req_le_mult_compat_r）+ 同右端加项保序（ubw_b_le_plus_r）+
   分配/结合/交换 req 链闭合 c_{n+1} 递推形。 *)
Theorem ubw_b_chain_eps_iter : forall (n : nat) (mu nu : S -> Real),
  le (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))
     (plus (mult (req_r_pow omd n) (tvr mu nu))
           (mult (ubw_b_cslack n) eps0)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu.
  - (* 底：omd^0 ≡ one、c_0 ≡ zero，req 链归一回 TV₀ 本体 *)
    exact (le_trans (tvr mu nu) (mult one (tvr mu nu))
             (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                   (mult (ubw_b_cslack 0%nat) eps0))
             (le_id_r (tvr mu nu) (tvr mu nu) (mult one (tvr mu nu))
                (req_sym (mult one (tvr mu nu)) (tvr mu nu)
                   (req_mult_one_l (tvr mu nu)))
                (le_refl (tvr mu nu)))
             (le_id_r (mult one (tvr mu nu))
                (plus (mult one (tvr mu nu)) zero)
                (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                      (mult (ubw_b_cslack 0%nat) eps0))
                (req_trans (plus (mult one (tvr mu nu)) zero)
                   (plus (mult one (tvr mu nu)) (mult zero eps0))
                   (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                         (mult (ubw_b_cslack 0%nat) eps0))
                   (req_plus_compat (mult one (tvr mu nu))
                      (mult one (tvr mu nu))
                      zero (mult zero eps0)
                      (req_refl (mult one (tvr mu nu)))
                      (req_sym (mult zero eps0) zero
                         (req_trans (mult zero eps0) (mult eps0 zero) zero
                            (mult_comm zero eps0) (mult_zero eps0))))
                   (req_refl (plus (mult (req_r_pow omd 0%nat) (tvr mu nu))
                              (mult (ubw_b_cslack 0%nat) eps0))))
                (req_le_plus_nonneg_r (mult one (tvr mu nu)) zero
                   (le_refl zero)))).
  - (* 递归步 *)
    assert (Homd_le0 : le zero omd) by exact (lt_le_iff zero omd (inl Homd_pos)).
    apply (le_trans
             (tvr (ubw_b_titer (Datatypes.S n) mu)
                  (ubw_b_titer (Datatypes.S n) nu))
             (plus (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))) eps0)
             (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                   (mult (ubw_b_cslack (Datatypes.S n)) eps0))).
    + (* 接口参数一次（链身单步 eps 收缩） *)
      exact (Hstep_eps (ubw_b_titer n mu) (ubw_b_titer n nu)).
    + (* omd 数乘抬升 IH，再同右端加 eps0 *)
      apply (le_trans
               (plus (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))) eps0)
               (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                              (mult (ubw_b_cslack n) eps0)))
                     eps0)
               (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                     (mult (ubw_b_cslack (Datatypes.S n)) eps0))).
      * exact (ubw_b_le_plus_r
                 (mult omd (tvr (ubw_b_titer n mu) (ubw_b_titer n nu)))
                 (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                 (mult (ubw_b_cslack n) eps0)))
                 eps0
                 (req_le_mult_compat_r omd
                    (tvr (ubw_b_titer n mu) (ubw_b_titer n nu))
                    (plus (mult (req_r_pow omd n) (tvr mu nu))
                          (mult (ubw_b_cslack n) eps0))
                    Homd_le0 (IH mu nu))).
      * (* req 链（平化三段）：MID2 →(distrib)→ (A+T)+eps0 →(assoc 对称)→
              A+(T+eps0) →(mult_assoc+尾链)→ RHS；le_id_r+le_refl 升格为 le *)
        exact (ubw_b_req_le
                 (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                (mult (ubw_b_cslack n) eps0)))
                       eps0)
                 (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                       (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                 (req_trans
                    (plus (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                   (mult (ubw_b_cslack n) eps0)))
                          eps0)
                    (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                           (mult omd (mult (ubw_b_cslack n) eps0)))
                          eps0)
                    (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                          (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                    (req_plus_compat
                       (mult omd (plus (mult (req_r_pow omd n) (tvr mu nu))
                                (mult (ubw_b_cslack n) eps0)))
                       (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (mult omd (mult (ubw_b_cslack n) eps0)))
                       eps0 eps0
                       (distrib omd (mult (req_r_pow omd n) (tvr mu nu))
                          (mult (ubw_b_cslack n) eps0))
                       (req_refl eps0))
                    (req_trans
                       (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                              (mult omd (mult (ubw_b_cslack n) eps0)))
                             eps0)
                       (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                       (plus (mult (req_r_pow omd (Datatypes.S n)) (tvr mu nu))
                             (mult (ubw_b_cslack (Datatypes.S n)) eps0))
                       (req_sym
                          (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                             (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                          (plus (plus (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                                   (mult omd (mult (ubw_b_cslack n) eps0)))
                                eps0)
                          (plus_assoc (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                             (mult omd (mult (ubw_b_cslack n) eps0)) eps0))
                       (req_plus_compat
                          (mult omd (mult (req_r_pow omd n) (tvr mu nu)))
                          (mult (mult omd (req_r_pow omd n)) (tvr mu nu))
                          (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                          (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                          (mult_assoc omd (req_r_pow omd n) (tvr mu nu))
                          (req_trans
                             (plus (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                             (plus eps0 (mult omd (mult (ubw_b_cslack n) eps0)))
                             (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                             (plus_comm (mult omd (mult (ubw_b_cslack n) eps0)) eps0)
                             (req_trans
                                (plus eps0 (mult omd (mult (ubw_b_cslack n) eps0)))
                                (plus (mult one eps0)
                                   (mult (mult omd (ubw_b_cslack n)) eps0))
                                (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                                (req_plus_compat eps0 (mult one eps0)
                                   (mult omd (mult (ubw_b_cslack n) eps0))
                                   (mult (mult omd (ubw_b_cslack n)) eps0)
                                   (req_sym (mult one eps0) eps0
                                      (req_trans (mult one eps0)
                                         (mult eps0 one) eps0
                                         (mult_comm one eps0)
                                         (mult_one eps0)))
                                   (mult_assoc omd (ubw_b_cslack n) eps0))
                                (req_sym (mult (ubw_b_cslack (Datatypes.S n)) eps0)
                                   (plus (mult one eps0)
                                      (mult (mult omd (ubw_b_cslack n)) eps0))
                                   (ubw_b_mult_plus_distr_l one
                                      (mult omd (ubw_b_cslack n)) eps0))))))
        )).
Qed.

(* 4b cmk 末端依存定理逐 eps 副本·严格版。
   装配结构与 cmk_attention_mixing_time（UpReqConcMixSel.v:856-884）逐位
   同形：k 选择依存库件 cmk_k_select（构造核心直连，首参证书=§1 闭证书），
   req_r_pow/cmk_r_pow 换形副本源模块 :871-878 的同款 req 链
   （cmk_r_pow_req_r_pow + req_mult_compat + lt_id_r）；链身依存取逐 eps 形
   （4a），结论右端携诚实余量 c_k·eps0（le_lt_trans + 同右端加项严格化）。 *)
Theorem ubw_b_cmk_eps_mirror : forall mu nu : S -> Real,
  forall budget : Real,
  lt zero budget ->
  le zero (tvr mu nu) ->
  (forall x : Real, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    lt (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
       (plus budget (mult (ubw_b_cslack k) eps0))).
Proof.
  intros mu nu budget Hbudget Htv0 Harch.
  destruct (cmk_k_select ubw_b_lt_plus_compat_lt_le omd (tvr mu nu) budget
             Homd_pos Homd_lt_one Htv0 Hbudget Harch) as [k Hk].
  assert (Hk2 : lt (mult (req_r_pow omd k) (tvr mu nu)) budget).
  { exact (lt_id_l (mult (req_r_pow omd k) (tvr mu nu))
                   (mult (cmk_r_pow omd k) (tvr mu nu)) budget
                   (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                      (tvr mu nu) (tvr mu nu)
                      (req_sym (cmk_r_pow omd k) (req_r_pow omd k)
                         (cmk_r_pow_req_r_pow omd k))
                      (req_refl (tvr mu nu)))
                   Hk). }
  exists k.
  apply (le_lt_trans
           (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
           (plus (mult (req_r_pow omd k) (tvr mu nu))
                 (mult (ubw_b_cslack k) eps0))
           (plus budget (mult (ubw_b_cslack k) eps0))).
  - exact (ubw_b_chain_eps_iter k mu nu).
  - exact (ubw_b_lt_plus_compat_lt_le
             (mult (req_r_pow omd k) (tvr mu nu)) budget
             (mult (ubw_b_cslack k) eps0) (mult (ubw_b_cslack k) eps0)
             Hk2 (le_refl (mult (ubw_b_cslack k) eps0))).
Qed.

(* 4c cmk 末端依存定理逐 eps 副本·非严格版（cmk_attention_mixing_time_le
   :887-915 同形；依存 cmk_k_select_le，k 选择换形走 le_id_l 副本）。 *)
Theorem ubw_b_cmk_eps_mirror_le : forall mu nu : S -> Real,
  forall budget : Real,
  lt zero budget ->
  le zero (tvr mu nu) ->
  (forall x : Real, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    le (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
       (plus budget (mult (ubw_b_cslack k) eps0))).
Proof.
  intros mu nu budget Hbudget Htv0 Harch.
  destruct (cmk_k_select_le ubw_b_lt_plus_compat_lt_le omd (tvr mu nu) budget
             Homd_pos Homd_lt_one Htv0 Hbudget Harch) as [k Hk].
  assert (Hk2 : le (mult (req_r_pow omd k) (tvr mu nu)) budget).
  { exact (le_id_l (mult (req_r_pow omd k) (tvr mu nu))
                   (mult (cmk_r_pow omd k) (tvr mu nu)) budget
                   (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                      (tvr mu nu) (tvr mu nu)
                      (req_sym (cmk_r_pow omd k) (req_r_pow omd k)
                         (cmk_r_pow_req_r_pow omd k))
                      (req_refl (tvr mu nu)))
                   Hk). }
  exists k.
  apply (le_trans
           (tvr (ubw_b_titer k mu) (ubw_b_titer k nu))
           (plus (mult (req_r_pow omd k) (tvr mu nu))
                 (mult (ubw_b_cslack k) eps0))
           (plus budget (mult (ubw_b_cslack k) eps0))).
  - exact (ubw_b_chain_eps_iter k mu nu).
  - exact (ubw_b_le_plus_r (mult (req_r_pow omd k) (tvr mu nu)) budget
             (mult (ubw_b_cslack k) eps0) Hk2).
Qed.

End ChainEpsBody.

(* ============ 审计收尾段（逐件封闭判读，节外全显） ============ *)
Print Assumptions ubw_b_lt_plus_compat_lt_le.
Print Assumptions ubw_b_mult_plus_distr_l.
Print Assumptions ubw_b_le_plus_r.
Print Assumptions ubw_b_plain_upgrade_eps.
Print Assumptions ubw_b_deslack_wall.
Print Assumptions ubw_b_twopt_mixed_sign.
Print Assumptions ubw_b_death_certificate.
Print Assumptions ubw_b_chain_eps_iter.
Print Assumptions ubw_b_cmk_eps_mirror.
Print Assumptions ubw_b_cmk_eps_mirror_le.
Print Assumptions ubw_b_req_le.

(* ============================================================ *)
(* 供给段（签名保持式消解，b3 §2.2.1；原节声明与三假设声明零改）：                *)
(*   链身三证书位在 cf2 实例（UpReqConcFin2 两点有界 softmax 具体层）上供给：      *)
(*   Homd_pos 位引 cf2_omd_pos；Homd_lt_one 位由 cf2_aux_ds_omd 与 cf2_ds_pos     *)
(*   经严格加法保序及右端 req 换形链导出；Hstep_eps 位引 cf2_tv_contraction_eps    *)
(*   （带两侧分布归一前提的逐 eps 单步收缩，余量参数全称量化，强于固定余量的      *)
(*   原假设形）。抽象层三位保持假设身份，本段为具体实例上的消解证书，              *)
(*   并以 sigT 封装成组供下游整取。                                              *)
(* ============================================================ *)
Require Import UpReqConcFin2.

Theorem ubw_b_omd_pos_supply : lt zero cf2_omd.
Proof.
  exact cf2_omd_pos.
Qed.

Theorem ubw_b_omd_lt_one_supply : lt cf2_omd one.
Proof.
  exact (lt_id_r cf2_omd (plus cf2_delta_star cf2_omd) one
           cf2_aux_ds_omd
           (lt_id_l cf2_omd (plus zero cf2_omd)
              (plus cf2_delta_star cf2_omd)
              (req_sym (plus zero cf2_omd) cf2_omd (req_plus_zero_l cf2_omd))
              (ubw_b_lt_plus_compat_lt_le zero cf2_delta_star cf2_omd cf2_omd
                 cf2_ds_pos (le_refl cf2_omd)))).
Qed.

Theorem ubw_b_step_eps_supply :
  forall (mu nu : bool -> Real) (eps : Real),
    req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> lt zero eps ->
    le (cf2_tv (cf2_k_step mu) (cf2_k_step nu))
       (plus (mult cf2_omd (cf2_tv mu nu)) eps).
Proof.
  exact cf2_tv_contraction_eps.
Qed.

Theorem ubw_b_cf2_certs :
  sigT (fun _ : lt zero cf2_omd =>
        sigT (fun _ : lt cf2_omd one =>
              forall (mu nu : bool -> Real) (eps : Real),
                req (cf2_sumf mu) one -> req (cf2_sumf nu) one ->
                lt zero eps ->
                le (cf2_tv (cf2_k_step mu) (cf2_k_step nu))
                   (plus (mult cf2_omd (cf2_tv mu nu)) eps))).
Proof.
  exact (existT _ ubw_b_omd_pos_supply
           (existT _ ubw_b_omd_lt_one_supply ubw_b_step_eps_supply)).
Qed.

(* ---- 供给段假设审计（四连 Print Assumptions） ---- *)
Print Assumptions ubw_b_omd_pos_supply.
Print Assumptions ubw_b_omd_lt_one_supply.
Print Assumptions ubw_b_step_eps_supply.
Print Assumptions ubw_b_cf2_certs.

(* ============================ §10 ConcB2 的 +1 松弛常数 Δ 与中心 z 的实例双侧界与严格形否定 ============================ *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
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
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.
Import ListNotations.
Require Import UpReqConcB2.

(* ============================================================ *)
(* §1 实例数据面（a 组：非退化实例；b 组复用源模块 cb2_smoke_* 全零面）       *)
(* ============================================================ *)

Definition cb2w_q : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_k : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_lmax : list (list Real * list Real) :=
  (real_one :: nil, real_one :: nil) :: nil.

(* 完备性证明（lmax 含唯一 pair，由 in_eq 一步给出） *)
Lemma cb2w_complete : forall s s' : unit, In (cb2w_q s, cb2w_k s') cb2w_lmax.
Proof. intros s s'. apply in_eq. Qed.

(* 非退化数值锚：z ≡ 1、Delta ≡ 2（与全零退化实例 z ≡ 0、core ≡ 0 形成对照） *)
Lemma cb2w_z_pw_one : forall n : nat,
  projT1 (cb2_z unit cb2w_q cb2w_k real_one tt tt) n == 1%Q.
Proof.
  intro n.
  (* 刀：实例壳层（cb2w_q/cb2w_k 常量体）＋源模块核层（cb2_z = temp·dot）逐层
     unfold 显式化，转换闭合替代裸反射单跳吞层。 *)
  unfold cb2_z, cb2w_q, cb2w_k.
  reflexivity.
Qed.

Lemma cb2w_Delta_pw_two : forall n : nat,
  projT1 (cb2_Delta real_one cb2w_lmax) n == 2%Q.
Proof.
  intro n.
  (* 刀：装配面（cb2_Delta = core + one）与封顶核（cb2_Delta_core = temp·maxabs）
     及实例清单 cb2w_lmax 三层 unfold 显式化后转换闭合。 *)
  unfold cb2_Delta, cb2_Delta_core, cb2w_lmax.
  reflexivity.
Qed.

(* ============================================================ *)
(* §2 非退化实例上的严格形（eps:=1#2 具体值）                                     *)
(*   证明结构与源模块 UpReqConcB2 的证明链（cb2_Delta_pos/cb2_z_lb/cb2_z_ub）        *)
(*   逐行同构，实例化 temp:=real_one、lmax:=cb2w_lmax，逐点不等式全用源模块          *)
(*   已证引理（cb2_maxabs_nonneg/cb2_dot_le_max/cb2_qplus_one_gap/cb2_qminus_gap）， *)
(*   即 cb2_Delta_core 的实例化重建本体。                                        *)
(* ============================================================ *)

(* a-2：Delta 正性的实例化重建（同构于源模块 cb2_Delta_pos 的严格支） *)
Theorem cb2w_Delta_pos_half : real_lt real_zero (cb2_Delta real_one cb2w_lmax).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (HM0 : Qle 0 (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_maxabs_nonneg cb2w_lmax n).
    assert (HX : Qle 0 (projT1 real_one n
                         * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by (apply cb2_qmul_nonneg; assumption).
    apply Qlt_to_QltT.
    unfold cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    change (projT1 real_zero n) with 0%Q.
    assert (HX1 : Qle 0 (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1. exact HX. }
    assert (Hzg : Qeq (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                      (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n
                       + 1 - 0)) by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
             (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1 - 0)
             (Qlt_le_trans (1#2)%Q 1%Q
                (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) HX1))
             Hzg).
Qed.

(* a-3：z 上界严格形的实例化重建（同构于源模块 cb2_z_ub 的 inl 支，语句强化为 real_lt 本体） *)
Theorem cb2w_z_ub_lt :
  real_lt (cb2_z unit cb2w_q cb2w_k real_one tt tt)
          (cb2_Delta real_one cb2w_lmax).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                      (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_dot_le_max cb2w_lmax (cb2w_q tt) (cb2w_k tt) n
                  (cb2w_complete tt tt)).
    assert (Huv : Qle (projT1 real_one n * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                      (projT1 real_one n
                        * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { apply cb2_qmul_nonneg_r.
      - exact Htn0.
      - apply (Qle_trans (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                         (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))).
        + apply cb2_qabs_ge.
        + exact Hbd. }
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    assert (Huv1 : Qle (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                       (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1. exact Huv. }
    exact (Qlt_le_trans (1#2)%Q 1%Q
             (Qminus (Qplus (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) 1)
                     (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
             cb2_qhalf_lt_one
             (cb2_qminus_gap
                (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                Huv1)).
Qed.

(* a-4：z 下界严格形的实例化重建（同构于源模块 cb2_z_lb 的 inl 支，语句强化为 real_lt 本体） *)
Theorem cb2w_z_lb_lt :
  real_lt (real_opp (cb2_Delta real_one cb2w_lmax))
          (cb2_z unit cb2w_q cb2w_k real_one tt tt).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                      (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_dot_le_max cb2w_lmax (cb2w_q tt) (cb2w_k tt) n
                  (cb2w_complete tt tt)).
    assert (Hdn_ge : Qle (Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                         (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
      by exact (cb2_qopp_abs_le (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)).
    assert (Hu : Qle (projT1 real_one n
                       * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                     (projT1 real_one n
                       * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
      by (apply cb2_qmul_nonneg_r; [exact Htn0 | exact Hdn_ge]).
    assert (Hw : Qle 0 (projT1 real_one n
                         * Qminus (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                             (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))))
      by (apply cb2_qmul_nonneg; [exact Htn0 | exact (cb2_qle_minus _ _ Hbd)]).
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_opp_proj. rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    assert (Hw1 : Qle 0 (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                          + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1.
      assert (Hzr : Qeq (projT1 real_one n
                          * Qminus (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                              (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                        (projT1 real_one n
                          * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                         + projT1 real_one n
                          * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)) by ring.
      rewrite <- Hzr. exact Hw. }
    assert (Htot1 : Qle 0 (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                           + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)).
    { apply (Qle_trans 0
               (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
               (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
      - exact Hw1.
      - apply Qplus_le_compat.
        + assert (Hu1 : Qle (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                            (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)).
          { rewrite <- H1. exact Hu. }
          exact Hu1.
        + apply Qle_refl. }
    assert (Hzg : Qeq (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                       + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                      (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                       - Qopp (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)))
      by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
              + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
             (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
              - Qopp (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1))
             (Qlt_le_trans (1#2)%Q 1%Q
                (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                 + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                    + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) Htot1))
             Hzg).
Qed.

(* a-5：库内全参一般引理的直接应用（cb2_z_lb_all / cb2_z_ub_all，实参 temp_pos:=one_pos、lmax_complete:=cb2w_complete） *)
Theorem cb2w_export_pack :
  real_le (real_opp (cb2_Delta real_one cb2w_lmax))
          (cb2_z unit cb2w_q cb2w_k real_one tt tt)
  * real_le (cb2_z unit cb2w_q cb2w_k real_one tt tt)
            (cb2_Delta real_one cb2w_lmax).
Proof.
  split.
  - exact (cb2_z_lb_all unit cb2w_q cb2w_k real_one one_pos
             cb2w_lmax cb2w_complete tt tt).
  - exact (cb2_z_ub_all unit cb2w_q cb2w_k real_one one_pos
             cb2w_lmax cb2w_complete tt tt).
Qed.

(* ============================================================ *)
(* §3 全零退化对照件（源模块 UpReqConcB2 头注如实记载的局限的定理化）：              *)
(*   uniform eventual gap 形的严格见证遇上点态恒零 gap 即自相矛盾                  *)
(*   （0<eps 且 eps<0，由 Qlt 传递性与非自反性导出矛盾，零经典逻辑）。             *)
(* ============================================================ *)

(* b-1 一般否定引理：点态 gap 恒零的二元组上 real_lt 见证不存在（构造性否定） *)
Lemma cb2w_gap_zero_no_lt : forall x y : Real,
  (forall n : nat, projT1 y n - projT1 x n == 0%Q) -> real_lt x y -> False.
Proof.
  intros x y Hgap [eps [Heps [N0 HN]]].
  assert (HNn : QltT eps (projT1 y N0 - projT1 x N0)).
  { apply HN. exact (NatLe_lift N0 N0 (le_n N0)). }
  apply QltT_to_Qlt in HNn.
  rewrite (Hgap N0) in HNn.
  apply QltT_to_Qlt in Heps.
  assert (Hbad : Qlt 0 0%Q) by exact (Qlt_trans 0 eps 0%Q Heps HNn).
  exact (Qlt_irrefl 0%Q Hbad).
Qed.

(* b-2 全零退化实例的逐点面：cb2_Delta_core ≡ 0（cb2_smoke_lmax 面上逐点计算归零） *)
Lemma cb2w_core_zero_pw : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n == 0%Q.
Proof.
  intro n.
  (* 刀：封顶核 cb2_Delta_core 与全零实例 cb2_smoke_lmax 两层 unfold 显式化
     （temp·maxabs 在零清单上逐点归零）后转换闭合。 *)
  unfold cb2_Delta_core, cb2_smoke_lmax.
  reflexivity.
Qed.

(* b-3 否定性见证：全零退化下 cb2_Delta_core 的严格正性见证不存在 *)
Theorem cb2w_core_pos_death :
  real_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax)
           (fun n => cb2w_core_zero_pw n)).
Qed.

(* b-4 z 上界严格见证的否定：gap ≡ 0，由 cb2w_gap_zero_no_lt 直接导出矛盾 *)
Lemma cb2w_core_gap_zero : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n
  - projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) n == 0%Q.
Proof.
  intro n.
  (* 刀：封顶核与核值两源模块定义（cb2_Delta_core/cb2_z）连同 b 组实例三常量
     （cb2_smoke_lmax/cb2_smoke_q/cb2_smoke_k）五层 unfold 显式化，gap 逐点
     差在零核与零核值上转换归零闭合。 *)
  unfold cb2_Delta_core, cb2_smoke_lmax, cb2_z, cb2_smoke_q, cb2_smoke_k.
  reflexivity.
Qed.

Theorem cb2w_z_ub_core_death :
  real_lt (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
          (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt
           (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
           (cb2_Delta_core real_one cb2_smoke_lmax)
           cb2w_core_gap_zero).
Qed.

(* b-5 否定性见证的合取封装：逐点恒零面 × 两个严格见证不存在 *)
Theorem cb2w_death_certificate :
  (forall n : nat, projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n == 0%Q)
  * ((real_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax) -> False)
      * (real_lt (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
                 (cb2_Delta_core real_one cb2_smoke_lmax) -> False)).
Proof.
  split.
  - exact cb2w_core_zero_pw.
  - split.
    + exact (fun H => cb2w_core_pos_death H).
    + exact (fun H => cb2w_z_ub_core_death H).
Qed.

(* ============================================================ *)
(* 假设审计（对逐件 Print Assumptions） *)
(* ============================================================ *)

Print Assumptions cb2w_complete.
Print Assumptions cb2w_z_pw_one.
Print Assumptions cb2w_Delta_pw_two.
Print Assumptions cb2w_Delta_pos_half.
Print Assumptions cb2w_z_ub_lt.
Print Assumptions cb2w_z_lb_lt.
Print Assumptions cb2w_export_pack.
Print Assumptions cb2w_gap_zero_no_lt.
Print Assumptions cb2w_core_zero_pw.
Print Assumptions cb2w_core_pos_death.
Print Assumptions cb2w_core_gap_zero.
Print Assumptions cb2w_z_ub_core_death.
Print Assumptions cb2w_death_certificate.
