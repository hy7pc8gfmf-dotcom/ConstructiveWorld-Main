(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   rwl_s14_pointwise_to_tail（原 L382，4 句玩具证）                     *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqResidWallEquiv.v *)
(* *)
(* 目的： GEO1 残墙三段定理化收束——G07 逐项可比墙 / S14 逐点界墙 /        *)
(*        AlignIdUnclosed 参序钉定账，沿「B→Or 提升器 ⟺ rLPO」等价类范式。 *)
(* 主件： rwl_resid_walls_lpo（残墙收束四参数位账）。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqLpoEquiv、UpReqSquareWallEquiv。 *)
(* 备注： 零公理、零假设负载；段一可比墙单向归约 rLPO（符号类强于判定     *)
(*        基座，双向不开），与 snw/g05w 双向类分野如实入账。 *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                              *)
(* 公理面：本件零公理、零假设负载。语句面全 Set 层（real_le/real_lt/    *)
(*   real_eq/Or(sigT)/QleT'/NatLe 均 Set 值；Or = S01:67 A+B 真数据   *)
(*   和型）；墙语句作蕴含前提参数化，全程零经典逻辑；证明体内部 Prop    *)
(*   仅现于 Q 层归谬 assert（KLWallClosed 先例：Prop 不外泄语句面；    *)
(*   Set 目标经 False_rect 出——AA15「不证墙为假」口径仅指不以          *)
(*   False 结尾的语句面，证明体内归谬不在禁域）。                      *)
(*                                                              *)
(* 三段残墙实读定形与分类（WALL-1 结构性分野口径）：                    *)
(*                                                              *)
(*  段一 G07_KLWall.v:627（判定 2/3 负支链）：判定 2 所记「四项交错     *)
(*    部分和下界」单引理缺口已由 判例 在盘闭合（klst_ep_four_terms /    *)
(*    klst_exp_tangent_neg / klst_gibbs_core_strict_neg 全链，G07 内    *)
(*    UpReqKLEnergy 成员；UpReqKLSTangent 头注核验在案）。残余墙 =      *)
(*    「逐项可比前提」：KL 严格和无条件化需逐点 Or (p s ≤ q s) (q s ≤   *)
(*    p s) 的全称供给——其载体核（S := unit、常值函数实例化）即任意      *)
(*    两实数可比性。定形 rwl_g07_cmp_wall。分类：符号类（比较判定，    *)
(*    （四支 Or-in-Or 逐支供隙/供零见证，rwl_g07_cmp_to_rlpo）；反向    *)
(*    （rLPO ⟹ 可比）不开（零-间隙二分不及符号，如实账）。故 G07 残    *)
(*    结论，与 WALL-2「七 S 参数位类外」结论同型互补。                      *)
(*                                                              *)
(*  段二 S14_B5BatchBlock.v:6849（δ-D ⑤ S 上界）：逐点全 n 界不可证    *)
(*    （log_seq/approx_root 逐点墙，δB-3 降级实证 item7 §2）⟹ 工程降    *)
(*    级改尾形 M 前提 + 尾证书 b5?_S_ub_tail_q。分类：工程实证降级型   *)
(*    （非 B/Or 序隙、非逻辑强度墙——降级依据是逐点估计实证失败，非     *)
(*    判定不可供给）。定理化面：自由向（逐点 ⟹ 尾形，M := 0）+ 诚实    *)
(*    重建通道（尾形 + 有限头段证书 ⟹ 逐点，即 b5dE 尾证书与 S(0)==1    *)
(*    透明件拼链的接口账）：rwl_s14_pointwise_to_tail /                 *)
(*    rwl_s14_tail_plus_head。                                          *)
(*                                                              *)
(*  段三 AlignIdUnclosed.v（文件名「未闭合」自述其上游件 6）：核验判定   *)
(*    ② 参序倒置——件 6 前提/结论 LHS 为 NPX-先序（KLE (NPX…) PSTR），   *)
(*    与已证桥 req2_backward_kl_step（PSTR-先序）反向；KL 数层面非对    *)
(*    称（KLE p q 与 KLE q p 不同函数），构造性下两向不可互推。分类：   *)
(*    （AlignIdUnclosed.v:157，Qed+Closed 三连打在案）闭合，残余        *)
(*    rwl_aiu_swap_slot（二元泛形；依 AA15 先例「不证墙为假」——不供     *)
(*    Swap 失败见证，只定形 + 分类账）。                                *)
(*                                                              *)
(* G3 加餐（GEO1 插值缝 #8，min/max 序劈裂对偶——Or 劈裂形全库 0 件，    *)
(*   G06_BForm:642「不主张 real_le (real_max a b) c 精确形（分支选择    *)
(*   面）」在案注记即其库内见证）：定形 rwl_max_split_wall，并证       *)
(*   cmp_wall ⟹ 劈裂缝（rwl_cmp_to_max_split：分支选择面由逐点可比供   *)
(*   给，S07 real_r_max_l_iff/real_r_max_r_iff 两支收缩件免费复合）；   *)
(*   严格 Or 劈裂的 free 向（real_lt 支无前提可证：x < a ⟹ x < max）    *)
(*   同源检验结论：#8 劈裂缝 ≤ 可比墙（LLPO 级），亦不在 rLPO 双向类   *)
(*   内——GEO1 #8 与 WALL-1/2 序隙轴的分野在此已证结论。                     *)
(*                                                              *)
(* 主件 rwl_resid_walls_lpo（四参数位账）：cmp_wall ⟹ rLPO × cmp_wall ⟹    *)
(*   snw_wall（段一与 WALL-1 类的衔接：可比强于平方墙——负支 t·t<0 与   *)
(*   q_sq_nonneg 逐点矛盾、eq 支 real_eq_sym 直换）× cmp_wall ⟹        *)
(*   max_split（#8 缝归约）× 段二自由向+重建通道对。                    *)
(*                                                              *)
(*   q_sq_nonneg/q_abs_neg_eq/q_abs_congr）⟶ WALL-1（UpReqSquareWall   *)
(*   Equiv 的 snw_wall——盘上 .vo 摘要不一致，按 WALL-2 退回方案本地    *)
(*   （UpReqG05WallClass 全基桥，未 Require——可比轴不在其等价类内，    *)
(*   头注核验替代依存）⟶ 本件（残墙三段清账）。                         *)
(* ------------------------------------------------------------ *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
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
Require Import UpReqLpoEquiv.
Import RealInterfaceEnhancedMod.
Local Open Scope Q_scope.

(*
   对 UpReqLpoEquiv 摘要不一致（Require 报 inconsistent assumptions）——
   按零触碰他件产物纪律，不重编他件 .vo，改直挂 UpReqLpoEquiv + 本地
   内联同构面：rwl_snw_wall_face 与 snw_wall（UpReqSquareWallEquiv:70）
   定义性同形（同一 CW219/S02 Real 层）。 *)
Definition rwl_snw_wall_face : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

(* ============================================================ *)
(* Part 1：Q 层助件（零名自查：全 rwl_ 前缀）                        *)
(* ============================================================ *)

(* 供隙位移：b−a > e 且 |b−c| < d < e ⟹ c−a > e−d。
   正支（a<c）三角形直链；负支（c≤a）给 |b−c| = b−c ≥ b−a > e > d > |b−c| 矛盾。
   纪律：Qeq 改写只进目标侧与 QltT/Id 型假设（UpReqLpoEquiv 先例），
   不做 Qle/Qlt 假设内改写（库 delta 展开坑，vos 虚假通过后全量首测实测）。 *)
Lemma rwl_q_gap_shift : forall a b c e d : Q,
  Qlt 0 d -> Qlt d e -> Qlt e (b - a) -> Qlt (Qabs (b - c)) d ->
  Qlt (e - d) (c - a).
Proof.
  intros a b c e d Hd0 Hde Hea Hbc.
  assert (Hba0 : 0 <= b - a).
  { apply Qlt_le_weak.
    apply (Qlt_trans 0 e (b - a)).
    - apply (Qlt_trans 0 d e); [exact Hd0 | exact Hde].
    - exact Hea. }
  assert (Heqba : Qabs (b - a) == (b - a)) by (apply Qabs_pos; exact Hba0).
  destruct (Qlt_le_dec a c) as [Hac | Hca].
  - (* 正支：|c−a| = c−a，c−a ≥ (b−a) − |b−c| > e − d *)
    apply (Qlt_le_trans (e - d) (b - a + (- Qabs (b - c))) (c - a)).
    + assert (Hr1 : (e - d)%Q == (e + (- d))%Q) by ring.
      rewrite Hr1.
      apply Qplus_lt_compat.
      * exact Hea.
      * apply Qopp_lt_compat. exact Hbc.
    + apply (Qle_trans (b - a + (- Qabs (b - c)))
                       ((Qabs (b - c) + (c - a)) + (- Qabs (b - c)))
                       (c - a)).
      * apply Qplus_le_compat;
          [apply (Qle_trans (b - a) (Qabs (b - a))
                            (Qabs (b - c) + (c - a))) | apply Qle_refl].
        -- rewrite Heqba. apply Qle_refl.
        -- apply (Qle_trans (Qabs (b - a)) (Qabs (b - c) + Qabs (c - a))
                            (Qabs (b - c) + (c - a))).
           ++ pose proof (Qabs_triangle (b - c) (c - a)) as Htri2.
              assert (Hr6 : ((b - c) + (c - a))%Q == (b - a)%Q) by ring.
              rewrite <- Hr6.
              exact Htri2.
           ++ assert (Hca0 : Qlt 0 (c - a)).
              { pose proof (proj2 (Qplus_lt_l a c (- a)) Hac) as H1.
                assert (Hr7 : (0%Q) == (a + - a)%Q) by ring.
                assert (Hr8 : (c - a)%Q == (c + - a)%Q) by ring.
                rewrite Hr7. rewrite Hr8.
                exact H1. }
              apply Qplus_le_compat; [apply Qle_refl |
                rewrite (Qabs_pos (c - a) (Qlt_le_weak 0 (c - a) Hca0));
                apply Qle_refl].
      * assert (Hr2 : ((Qabs (b - c) + (c - a)) + (- Qabs (b - c)))%Q
                      == (c - a)%Q) by ring.
        rewrite Hr2. apply Qle_refl.
  - (* 负支：c ≤ a ⟹ b−a ≤ b−c 且 |b−c| = b−c ⟹ b−c < d < e < b−a ≤ b−c 爆 *)
    exfalso.
    assert (Hbac : b - a <= b - c).
    { pose proof (Qopp_le_compat c a Hca) as Ho.
      pose proof (Qplus_le_compat (- a) (- c) b b Ho (Qle_refl b)) as Hq2.
      assert (Hr4 : (b - a)%Q == (- a + b)%Q) by ring.
      assert (Hr5 : (b - c)%Q == (- c + b)%Q) by ring.
      rewrite Hr4. rewrite Hr5.
      exact Hq2. }
    assert (Hbc0 : 0 <= b - c).
    { apply Qlt_le_weak.
      apply (Qlt_trans 0 e (b - c)).
      - apply (Qlt_trans 0 d e); [exact Hd0 | exact Hde].
      - exact (Qlt_le_trans e (b - a) (b - c) Hea Hbac). }
    apply (Qlt_irrefl (b - c)).
    apply (Qlt_le_trans (b - c) (b - a) (b - c)).
    + apply (Qlt_trans (b - c) e (b - a)).
      * apply (Qlt_trans (b - c) d e).
        -- apply (Qle_lt_trans (b - c) (Qabs (b - c)) d).
           ++ rewrite (Qabs_pos (b - c) Hbc0). apply Qle_refl.
           ++ exact Hbc.
        -- exact Hde.
      * exact Hea.
    + exact Hbac.
Qed.

(* ============================================================ *)
(* Part 2：实层换形助件（序沿等距的右迁移）                          *)
(* ============================================================ *)

(* real_le x y + real_eq y z ⟹ real_le x z（real_lt 支经 rwl_q_gap_shift
   供半隙；real_eq 支 real_eq_trans 直连） *)
Lemma rwl_le_eq_transfer_r : forall x y z : Real,
  real_le x y -> real_eq y z -> real_le x z.
Proof.
  intros x y z H Hq.
  destruct H as [Hlt | Heq].
  - apply inl.
    destruct Hlt as [eps [Heps [N HN]]].
    assert (Hh : QltT 0 (eps / 2)).
    { apply Qlt_to_QltT. apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    destruct (Hq (eps / 2) Hh) as [N2 HN2].
    assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    assert (Hde2 : Qlt (eps / 2) eps).
    { destruct (Qlt_le_dec (eps / 2) eps) as [Hgood | Hbad].
      - exact Hgood.
      - exfalso.
        pose proof (Qmult_le_compat_r eps (eps / 2) 2 Hbad
                      (Qlt_le_weak 0 2 (proj2 (Qlt_alt 0 2) eq_refl))) as Hm.
        assert (Hm2 : (2 * eps <= eps)%Q).
        { assert (Hr1a : (2 * eps)%Q == (eps * 2)%Q) by ring.
          assert (Hr2a : eps%Q == ((eps / 2) * 2)%Q) by field.
          rewrite Hr1a. rewrite Hr2a at 2.
          exact Hm. }
        assert (Hm3 : (eps <= 0)%Q).
        { pose proof (Qplus_le_compat (2 * eps) eps (- eps) (- eps) Hm2
                        (Qle_refl (- eps))) as Hm4.
          assert (Hr6 : eps%Q == (2 * eps + - eps)%Q) by field.
          assert (Hr7 : 0%Q == (eps + - eps)%Q) by ring.
          rewrite Hr6. rewrite Hr7.
          exact Hm4. }
        apply (Qlt_irrefl 0).
        exact (Qlt_le_trans 0 eps 0 HepsQ Hm3). }
    exists (eps / 2). split.
    + exact Hh.
    + exists (Nat.max N N2). intros n Hn.
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (HnN2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      specialize (HN n HnN). specialize (HN2 n HnN2).
      apply QltT_to_Qlt in HN. apply QltT_to_Qlt in HN2.
      apply Qlt_to_QltT.
      assert (Hring : (eps - eps / 2)%Q == (eps / 2)%Q) by field.
      rewrite <- Hring.
      exact (rwl_q_gap_shift (projT1 x n) (projT1 y n) (projT1 z n)
               eps (eps / 2)
               (QltT_to_Qlt 0 (eps / 2) Hh) Hde2 HN HN2).
  - apply inr. exact (real_eq_trans x y z Heq Hq).
Qed.

(* ============================================================ *)
(* Part 3：段一定形与归约——G07 逐项可比墙 ⟹ rLPO                     *)
(* ============================================================ *)

(* 段一墙语（载体核）：任意两实数可比性。G07 KL 严格和链「逐项可比前提」
   的 S := unit 常值实例化即此形。 *)
Definition rwl_g07_cmp_wall : Set :=
  forall p q : Real, Or (real_le p q) (real_le q p).

(* 归约定理：可比墙 ⟹ 受限 LPO。四支 Or-in-Or 逐支：
   x<0 支 |x_n| = −x_n > eps；x==0 支直供零见证；0<x 支 |x_n| = x_n > eps；
   0==x 支经 |0−x_n| = |x_n| 换形。反向不开（符号不归零二分所及）。 *)
Theorem rwl_g07_cmp_to_rlpo : rwl_g07_cmp_wall -> rLPO.
Proof.
  intros Hcmp x.
  destruct (Hcmp x real_zero) as [H | H].
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      apply inl. exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn). apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz in HN.
        assert (Hr : (0 - projT1 x n)%Q == (- projT1 x n)%Q) by ring.
        rewrite Hr in HN.
        assert (Hneg : (projT1 x n < 0)%Q).
        { assert (Hrn : (projT1 x n)%Q == (- (- projT1 x n))%Q) by ring.
          rewrite Hrn.
          apply (Qopp_lt_compat 0 (- projT1 x n)).
          apply (Qlt_trans 0 eps (- projT1 x n)).
          - exact (QltT_to_Qlt 0 eps Heps).
          - exact HN. }
        assert (Hle0 : (projT1 x n <= 0)%Q) by (apply (Qlt_le_weak _ _ Hneg)).
        rewrite (q_abs_neg_eq (projT1 x n) Hle0).
        exact HN.
    + apply inr. intros eps Heps.
      destruct (Heq eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      assert (Hr : (projT1 x n - projT1 real_zero n)%Q == (projT1 x n)%Q).
      { assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz. ring. }
      rewrite (q_abs_congr _ _ Hr) in HN.
      apply Qlt_to_QltT. exact HN.
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      apply inl. exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn). apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz in HN.
        assert (Hr : (projT1 x n - 0)%Q == (projT1 x n)%Q) by ring.
        rewrite Hr in HN.
        assert (Hxn0 : Qlt 0 (projT1 x n)).
        { apply (Qlt_trans 0 eps (projT1 x n)).
          - exact (QltT_to_Qlt 0 eps Heps).
          - exact HN. }
        rewrite (Qabs_pos (projT1 x n) (Qlt_le_weak _ _ Hxn0)).
        exact HN.
    + apply inr. intros eps Heps.
      destruct (Heq eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      assert (Hr : (projT1 real_zero n - projT1 x n)%Q
                   == (- projT1 x n)%Q).
      { assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz. ring. }
      rewrite (q_abs_congr _ _ Hr) in HN.
      rewrite (Qabs_opp (projT1 x n)) in HN.
      apply Qlt_to_QltT. exact HN.
Qed.

(* 段一 ⟷ WALL-1 类衔接：可比墙 ⟹ 素颜平方墙。
   左支直供；右支（t·t ≤ 0）的 lt 子支与 q_sq_nonneg 逐点矛盾
   （Prop 归谬 False_rect 出 Set 目标），eq 子支 real_eq_sym 直换。 *)
Theorem rwl_cmp_to_snw_wall : rwl_g07_cmp_wall -> rwl_snw_wall_face.
Proof.
  intros Hcmp t.
  destruct (Hcmp real_zero (real_mult t t)) as [H | H].
  - exact H.
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      assert (Habs : False).
      { specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
        apply QltT_to_Qlt in HN.
        assert (Hz : projT1 real_zero N == 0) by reflexivity.
        rewrite Hz in HN.
        rewrite (real_mult_proj t t N) in HN.
        assert (Hr : (0 - projT1 t N * projT1 t N)%Q
                     == (- (projT1 t N * projT1 t N))%Q) by ring.
        rewrite Hr in HN.
        apply QltT_to_Qlt in Heps.
        assert (Hle0 : (- (projT1 t N * projT1 t N) <= 0)%Q).
        { apply (Qopp_le_compat 0 (projT1 t N * projT1 t N)).
          apply q_sq_nonneg. }
        apply (Qlt_irrefl 0).
        exact (Qlt_le_trans 0 (- (projT1 t N * projT1 t N)) 0
                 (Qlt_trans 0 eps (- (projT1 t N * projT1 t N)) Heps HN)
                 Hle0). }
      exact (False_rect _ Habs).
    + apply inr. exact (real_eq_sym (real_mult t t) real_zero Heq).
Qed.

(* ============================================================ *)
(* Part 4：G3 加餐——GEO1 #8 min/max 序劈裂缝（Or 劈裂形定形与归约）   *)
(* ============================================================ *)

(* #8 劈裂缝本体：x ≤ max(a,b) ⟹ x ≤ a ∨ x ≤ b。
   Or 劈裂形全库 0 件；G06_BForm:642「不主张 real_le (real_max a b) c
   精确形（分支选择面）」注记即其库内见证。 *)
Definition rwl_max_split_wall : Set :=
  forall x a b : Real,
    real_le x (real_max a b) -> Or (real_le x a) (real_le x b).

(* 归约定理：可比墙 ⟹ 劈裂缝。分支选择面由逐点可比供给：
   a ≤ b 支 max 收缩到 b（real_r_max_r_iff），b ≤ a 支收缩到 a
   （real_r_max_l_iff），序沿收缩等距右迁移（rwl_le_eq_transfer_r）。 *)
Theorem rwl_cmp_to_max_split : rwl_g07_cmp_wall -> rwl_max_split_wall.
Proof.
  intros Hcmp x a b Hx.
  destruct (Hcmp a b) as [Hab | Hba].
  - apply inr. apply (rwl_le_eq_transfer_r x (real_max a b) b Hx).
    exact (real_r_max_r_iff a b Hab).
  - apply inl. apply (rwl_le_eq_transfer_r x (real_max a b) a Hx).
    exact (real_r_max_l_iff a b Hba).
Qed.

(* ============================================================ *)
(* Part 5：段二定形与账——S14 逐点界墙的尾形接口（QleT'/NatLe 面）      *)
(* ============================================================ *)

(* 段二被降级面：逐点全 n 界（δB-3 实证不可证：log_seq/approx_root
   逐点墙）。 *)
Definition rwl_s14_ptw_wall (Sq : nat -> Q) (ub : Q) : Set :=
  forall n : nat, QleT' (Sq n) ub.

(* 段二诚实接口：尾形 M 前提 + 尾证书（b5?_S_ub_tail_q 的语句形）。 *)
Definition rwl_s14_tail_cert (Sq : nat -> Q) (ub : Q) : Set :=
  sigT (fun M : nat => forall n : nat, NatLe M n -> QleT' (Sq n) ub).

(* 自由向：逐点 ⟹ 尾形（M := 0，零厚度）。 *)
Theorem rwl_s14_pointwise_to_tail : forall (Sq : nat -> Q) (ub : Q),
  rwl_s14_ptw_wall Sq ub -> rwl_s14_tail_cert Sq ub.
Proof.
  intros Sq ub H.
  exists 0%nat.
  intros n _.
  exact (H n).
Qed.

(* 重建通道：尾形 + 有限头段证书 ⟹ 逐点（b5dE 尾证书 × S(0)==1 透明件
   拼链的接口账；头段分支走 NatLe n M，尾段分支走 NatLe M n）。 *)
Theorem rwl_s14_tail_plus_head : forall (Sq : nat -> Q) (ub : Q) (M : nat),
  (forall n : nat, NatLe M n -> QleT' (Sq n) ub) ->
  (forall n : nat, NatLe n M -> QleT' (Sq n) ub) ->
  rwl_s14_ptw_wall Sq ub.
Proof.
  intros Sq ub M Htail Hhead n.
  destruct (Nat.leb n M) eqn:E.
  - apply Hhead. unfold NatLe. rewrite E. apply id_refl.
  - apply Htail. apply NatLe_lift.
    apply Nat.lt_le_incl.
    exact (proj1 (Nat.leb_gt n M) E).
Qed.

(* ============================================================ *)
(* Part 6：段三定形——AlignIdUnclosed 参序面（钉定账，无归约）          *)
(* ============================================================ *)

(* 件 6 参序面（二元泛形；F 的 KLE 实例 = req2_rel_ent 参数序）。
   钉定：KL 数层面非对称（KLE p q ≠ KLE q p 一般成立），构造性下
   swap 参数位两向不可互推；修正序闭合件 aiu_backward_kl_exact_uncond
   （AlignIdUnclosed.v:157）已在盘。依 AA15 先例不证为假——只定形。 *)
Definition rwl_aiu_swap_slot (F : Real -> Real -> Real) : Set :=
  forall p q : Real, real_eq (F p q) (F q p).

(* ============================================================ *)
(* Part 7：主件闭合——rwl_resid_walls_lpo（残墙收束四参数位账）            *)
(* ============================================================ *)

Definition rwl_resid_walls_lpo :
  And (rwl_g07_cmp_wall -> rLPO)
      (And (rwl_g07_cmp_wall -> rwl_snw_wall_face)
           (And (rwl_g07_cmp_wall -> rwl_max_split_wall)
                (And (forall Sq ub, rwl_s14_ptw_wall Sq ub ->
                                    rwl_s14_tail_cert Sq ub)
                     (forall (Sq : nat -> Q) (ub : Q) (M : nat),
                        (forall n : nat, NatLe M n -> QleT' (Sq n) ub) ->
                        (forall n : nat, NatLe n M -> QleT' (Sq n) ub) ->
                        rwl_s14_ptw_wall Sq ub)))) :=
  (rwl_g07_cmp_to_rlpo,
   (rwl_cmp_to_snw_wall,
    (rwl_cmp_to_max_split,
     (rwl_s14_pointwise_to_tail, rwl_s14_tail_plus_head)))).

(* ============================================================ *)
(* 提取检验与假设审计面                                             *)
(* ============================================================ *)

(* 提取检验：四件素颜 real_* 语句面全量提取（段二件为 QleT'/NatLe 面
   同为 Set 值 Id/sigT，亦入面；段三定形件非定理不进面）。
   全部证明体为纯组合子复合 + Q 层算术链，实证 Obj.magic 计数=0。 *)
Extraction "_thv3twall3.ml" rwl_g07_cmp_to_rlpo rwl_cmp_to_snw_wall
  rwl_cmp_to_max_split rwl_le_eq_transfer_r
  rwl_s14_pointwise_to_tail rwl_s14_tail_plus_head.

Print Assumptions rwl_q_gap_shift.
Print Assumptions rwl_le_eq_transfer_r.
Print Assumptions rwl_g07_cmp_to_rlpo.
Print Assumptions rwl_cmp_to_snw_wall.
Print Assumptions rwl_cmp_to_max_split.
Print Assumptions rwl_s14_pointwise_to_tail.
Print Assumptions rwl_s14_tail_plus_head.
Print Assumptions rwl_resid_walls_lpo.
