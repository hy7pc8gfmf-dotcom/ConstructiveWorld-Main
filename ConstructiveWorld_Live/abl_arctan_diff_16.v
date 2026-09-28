(* ==========================================================================)
   abl_arctan_diff_16.v — arctan 差公式件首片（9a-乙）
   使命: arctan 差公式 9a-乙 的首片（1h 上限内的可达部分）：
     件 1 内点导数封装 abl9_atan_deriv_interior——b3rr_real_arctan_deriv_linear
     （S11:L5521）于收缩内界 0≤ρ<1 的实例化（结论配形=φ 复合的 u-侧增量
     供给；系薄实例化，非平凡主体在件 2 与未竟登记）；件 2 和差规则骨架
     abl9_atan_diff_sum_rule——eps-线性近似形态（HasIncr f x a，配形与
     b3rr 结论逐字同构）的和差规则真构造（eps/2·eps/3 预算分割＋
     real_min δ 合成＋real_abs 三角＋real_le_plus_compat 装配＋逐点环律
     闭合），系 S06 differentiable_plus 同构定理在 S02 cauchy 实数层的
     独立自建供给。
   目标全句（本片未闭合，不书全句）：real_eq (arctan(x+h) − arctan x)
     (arctan' 型增量项)，应用域 1+x(x+h) ≥ 3/4 严格正；闭合缺口见未竟登记。
   实文勘正（对源计划判据3）：「微积分机器全带空缺」系按名 grep 盲区——
     S06:L258-1588 Section DifferentiableLemmas 存在完整抽象序域可微层：
     differentiable_plus（L352）/mult（L426）/affine（L747）/opp（L805）/
     minus（L850）/power_nat（L885）/compose（L1016，链式规则已实现）。
     真空缺勘定为三项：①常值判据（F'=0⟹F 常值）全带确无；②S06 抽象基座
     RealInterfaceEnhanced 的 S02 Real 实例可用性未验（S07:L8596 系 setoid
     版非同接口）；③arctan 逐点域证书形态与全局型 Differentiable 不合，
     区域相对化重构为真缺口。
   依赖: S01_BaseRing–S11_TP3B5；Stdlib QArith、List、Setoid、Lia、Extraction。
   构造性: 纯构造性（全链 Qed 真构造，零承认式语句）；Set 层零 Prop 泄露
     （HasIncr 全由 real_lt/real_le/sigT/And 组装）；非平凡（件 2 真构造
     五步；件 1 薄实例化已申明）；可提取（尾 Print Assumptions +
     Recursive Extraction，判据 Closed + Obj.magic 0）。
   编译配方: source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x16pool "" abl_arctan_diff_16.v
     （隔离池 /tmp/x16pool=真拷 x15pool 现势链，S01–S11 .vo 在链。）
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 骨架谓词：eps-线性近似（斜率 a 于点 x），LHS 配形与            *)
(* b3rr_real_arctan_deriv_linear 结论逐字同构。全 Set 层。        *)
(* ============================================================ *)
Definition HasIncr (f : Real -> Real) (x a : Real) : Set :=
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (f (real_plus x h))
                     (real_opp (real_plus (f x) (real_mult h a)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* 辅件：Q 常数正因子 × 正 eps 保正（eps 预算分割用）              *)
(* ============================================================ *)
Lemma abl9_qscale_pos : forall (c : Q) (eps : Real),
  Qlt 0 c -> real_lt real_zero eps ->
  real_lt real_zero (real_mult (real_const c) eps).
Proof.
  intros c eps Hc Heps.
  destruct Heps as [e0 [He0 [N0 HN0]]].
  exists (c * e0)%Q.
  split.
  - assert (Hlt : Qlt 0 (c * e0)%Q).
    { apply (Qmult_lt_0_compat c e0).
      - exact Hc.
      - apply QltT_to_Qlt. exact He0. }
    unfold QltT, Qlt_bool.
    assert (Hcmp : Qcompare 0 (c * e0)%Q = Lt) by (apply Qlt_alt; exact Hlt).
    rewrite Hcmp. reflexivity.
  - exists N0. intros n Hn.
    assert (H2 : Qlt (e0 * c)%Q
                   ((projT1 eps n - projT1 real_zero n) * c)%Q).
    { apply (Qmult_lt_compat_r e0 (projT1 eps n - projT1 real_zero n)%Q c).
      - exact Hc.
      - apply QltT_to_Qlt. exact (HN0 n Hn). }
    assert (Hmid : (projT1 (real_mult (real_const c) eps) n
                    - projT1 real_zero n ==
                    c * (projT1 eps n - projT1 real_zero n))%Q).
    { rewrite (real_mult_proj (real_const c) eps n).
      rewrite (real_const_proj c n).
      simpl. ring. }
    assert (Hc2 : Qcompare (c * e0)%Q
                    (projT1 (real_mult (real_const c) eps) n
                     - projT1 real_zero n)%Q
                  = Qcompare (c * e0)%Q
                    (c * (projT1 eps n - projT1 real_zero n))%Q)
      by (apply (Qcompare_comp (c * e0) (c * e0) (Qeq_refl (c * e0))
                   (projT1 (real_mult (real_const c) eps) n
                    - projT1 real_zero n)%Q
                   (c * (projT1 eps n - projT1 real_zero n))%Q Hmid)).
    assert (Ha : (c * e0 == e0 * c)%Q) by ring.
    assert (Hb : (c * (projT1 eps n - projT1 real_zero n) ==
                  (projT1 eps n - projT1 real_zero n) * c)%Q) by ring.
    assert (Hce : Qcompare (c * e0)%Q
                    (c * (projT1 eps n - projT1 real_zero n))%Q
                  = Qcompare (e0 * c)%Q
                    ((projT1 eps n - projT1 real_zero n) * c)%Q)
      by (apply (Qcompare_comp (c * e0) (e0 * c) Ha
                   (c * (projT1 eps n - projT1 real_zero n))
                   ((projT1 eps n - projT1 real_zero n) * c) Hb)).
    unfold QltT, Qlt_bool.
    rewrite Hc2. rewrite Hce.
    assert (Hcmp : Qcompare (e0 * c)%Q
                     ((projT1 eps n - projT1 real_zero n) * c)%Q = Lt)
      by (apply Qlt_alt; exact H2).
    rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(* 辅件：Qmin 下界两件（Qle=Z 层定义，Qcompare 分支直构；            *)
(* 本 Stdlib 面无 Qmin_le_l/r 实名件，实编译勘定自建）。              *)
(* ============================================================ *)
Lemma abl9_Qmin_le_l : forall x y : Q, Qle (Qmin x y) x.
Proof.
  intros x y.
  unfold Qmin, gmin.
  destruct (Qcompare x y) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - assert (Hyx : (y ?= x) = Lt).
    { rewrite <- Qcompare_antisym. rewrite E. reflexivity. }
    apply Qlt_le_weak. apply Qlt_alt. exact Hyx.
Qed.

Lemma abl9_Qmin_le_r : forall x y : Q, Qle (Qmin x y) y.
Proof.
  intros x y.
  assert (Hgen : forall c : comparison,
           Qcompare x y = c ->
           Qle (match c with Gt => y | _ => x end) y).
  { intros c Hc. destruct c.
    - apply qeq_le. apply Qeq_alt. exact Hc.
    - apply Qlt_le_weak. apply Qlt_alt. exact Hc.
    - apply Qle_refl. }
  unfold Qmin, gmin.
  apply (Hgen (Qcompare x y)). reflexivity.
Qed.

(* ============================================================ *)
(* 辅件：δmin 解包（骨架件）——|s| < min δf δg ⟹ |s| < δf 与        *)
(* |s| < δg（逐点 Qmin 链 + qeq_le/Qle_trans 中继），供和差规则 δ 合成。 *)
(* ============================================================ *)
Lemma abl9_min_lt_l : forall (a b s : Real),
  real_lt s (real_min a b) -> real_lt s a.
Proof.
  intros a b s Hs.
  destruct Hs as [e0 [He0 [N0 HN0]]].
  exists e0. split.
  - exact He0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0
             (projT1 (real_min a b) n - projT1 s n)%Q
             (projT1 a n - projT1 s n)%Q).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + unfold Qminus.
      apply (Qle_trans (projT1 (real_min a b) n + Qopp (projT1 s n))
                       (Qmin (projT1 a n) (projT1 b n) + Qopp (projT1 s n))
                       (projT1 a n + Qopp (projT1 s n))).
      * apply (Qplus_le_compat (projT1 (real_min a b) n)
                 (Qmin (projT1 a n) (projT1 b n))
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply qeq_le. apply real_min_proj.
        -- apply Qle_refl.
      * apply (Qplus_le_compat (Qmin (projT1 a n) (projT1 b n))
                 (projT1 a n)
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply abl9_Qmin_le_l.
        -- apply Qle_refl.
Qed.

Lemma abl9_min_lt_r : forall (a b s : Real),
  real_lt s (real_min a b) -> real_lt s b.
Proof.
  intros a b s Hs.
  destruct Hs as [e0 [He0 [N0 HN0]]].
  exists e0. split.
  - exact He0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0
             (projT1 (real_min a b) n - projT1 s n)%Q
             (projT1 b n - projT1 s n)%Q).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + unfold Qminus.
      apply (Qle_trans (projT1 (real_min a b) n + Qopp (projT1 s n))
                       (Qmin (projT1 a n) (projT1 b n) + Qopp (projT1 s n))
                       (projT1 b n + Qopp (projT1 s n))).
      * apply (Qplus_le_compat (projT1 (real_min a b) n)
                 (Qmin (projT1 a n) (projT1 b n))
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply qeq_le. apply real_min_proj.
        -- apply Qle_refl.
      * apply (Qplus_le_compat (Qmin (projT1 a n) (projT1 b n))
                 (projT1 b n)
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply abl9_Qmin_le_r.
        -- apply Qle_refl.
Qed.

(* ============================================================ *)
(* 件 2：三元组骨架·和差规则（本项目 Real 层自建，S06 抽象层同构）  *)
(*   HasIncr f x a -> HasIncr g x b ->                            *)
(*   HasIncr (fun y => f y + g y) x (a + b)                       *)
(* 预算：内层各取 eps/2、eps'/3；δ := real_min δf δg。             *)
(* ============================================================ *)
Lemma abl9_atan_diff_sum_rule :
  forall (f g : Real -> Real) (x a b : Real),
  HasIncr f x a -> HasIncr g x b ->
  HasIncr (fun y : Real => real_plus (f y) (g y)) x (real_plus a b).
Proof.
  intros f g x a b Hf Hg eps Heps.
  unfold HasIncr in Hf, Hg.
  set (e1 := real_mult (real_const (1 # 2)) eps).
  assert (He1 : real_lt real_zero e1).
  { apply abl9_qscale_pos.
    - unfold Qlt. simpl. lia.
    - exact Heps. }
  destruct (Hf e1 He1) as [df [Hdfp Hdfstep]].
  destruct (Hg e1 He1) as [dg [Hdgp Hdgstep]].
  exists (real_min df dg). split.
  - apply real_min_pos.
    + exact Hdfp.
    + exact Hdgp.
  - intros h Hh eps' Heps'.
    set (e2 := real_mult (real_const (1 # 3)) eps').
    assert (He2 : real_lt real_zero e2).
    { apply abl9_qscale_pos.
      - unfold Qlt. simpl. lia.
      - exact Heps'. }
    (* —— δmin 逐点拆解：|h| < min δf δg ⟹ |h| < δf 且 |h| < δg —— *)
    assert (Hhdf : real_lt (real_abs h) df)
      by (apply (abl9_min_lt_l df dg (real_abs h)); exact Hh).
    assert (Hhdg : real_lt (real_abs h) dg)
      by (apply (abl9_min_lt_r df dg (real_abs h)); exact Hh).
    assert (HA := Hdfstep h Hhdf e2 He2).
    assert (HB := Hdgstep h Hhdg e2 He2).
    (* —— 1. LHS 实值重组（逐点环律）：                              *)
    (*   |(f+g)(x+h) − ((f+g)(x) + h(a+b))|                          *)
    (*    = |(f(x+h) − (f(x)+ha)) + (g(x+h) − (g(x)+hb))|            *)
    assert (Hrearr : real_eq
      (real_abs (real_plus
        (real_plus (f (real_plus x h)) (g (real_plus x h)))
        (real_opp (real_plus (real_plus (f x) (g x))
                             (real_mult h (real_plus a b))))))
      (real_abs (real_plus
        (real_plus (f (real_plus x h))
                   (real_opp (real_plus (f x) (real_mult h a))))
        (real_plus (g (real_plus x h))
                   (real_opp (real_plus (g x) (real_mult h b))))))).
    { apply real_abs_eq_compat. apply real_eq_of_zero_diff. intro n.
      (* 自顶向下单发 proj 重写（X15 工法；! 重写走 setoid 路径不可用） *)
      rewrite (real_plus_proj (real_plus (f (real_plus x h)) (g (real_plus x h)))
                 (real_opp (real_plus (real_plus (f x) (g x))
                             (real_mult h (real_plus a b)))) n).
      rewrite (real_plus_proj (real_plus (f (real_plus x h))
                                 (real_opp (real_plus (f x) (real_mult h a))))
                 (real_plus (g (real_plus x h))
                            (real_opp (real_plus (g x) (real_mult h b)))) n).
      rewrite (real_plus_proj (f (real_plus x h)) (g (real_plus x h)) n).
      rewrite (real_opp_proj (real_plus (real_plus (f x) (g x))
                                 (real_mult h (real_plus a b))) n).
      rewrite (real_plus_proj (real_plus (f x) (g x))
                 (real_mult h (real_plus a b)) n).
      rewrite (real_mult_proj h (real_plus a b) n).
      rewrite (real_plus_proj a b n).
      rewrite (real_plus_proj (f x) (g x) n).
      rewrite (real_plus_proj (f (real_plus x h))
                 (real_opp (real_plus (f x) (real_mult h a))) n).
      rewrite (real_opp_proj (real_plus (f x) (real_mult h a)) n).
      rewrite (real_plus_proj (f x) (real_mult h a) n).
      rewrite (real_mult_proj h a n).
      rewrite (real_plus_proj (g (real_plus x h))
                 (real_opp (real_plus (g x) (real_mult h b))) n).
      rewrite (real_opp_proj (real_plus (g x) (real_mult h b)) n).
      rewrite (real_plus_proj (g x) (real_mult h b) n).
      rewrite (real_mult_proj h b n).
      ring. }
    (* —— 2. eps 三角 —— *)
    assert (Htri : real_le
      (real_abs (real_plus
        (real_plus (f (real_plus x h))
                   (real_opp (real_plus (f x) (real_mult h a))))
        (real_plus (g (real_plus x h))
                   (real_opp (real_plus (g x) (real_mult h b))))))
      (real_plus
        (real_plus (real_abs (real_plus (f (real_plus x h))
                              (real_opp (real_plus (f x) (real_mult h a)))))
                   (real_abs (real_plus (g (real_plus x h))
                              (real_opp (real_plus (g x) (real_mult h b))))))
        e2))
      by (apply (real_abs_triangle_le_eps
                   (real_plus (f (real_plus x h))
                              (real_opp (real_plus (f x) (real_mult h a))))
                   (real_plus (g (real_plus x h))
                              (real_opp (real_plus (g x) (real_mult h b))))
                   e2 He2)).
    (* —— 3. 弱-弱加法装配 —— *)
    assert (HT1 : real_le
      (real_plus (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                 (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
      (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                 (real_plus (real_mult e1 (real_abs h)) e2)))
      by (apply real_le_plus_compat; [exact HA | exact HB]).
    assert (HT2 : real_le
      (real_plus
        (real_plus (real_abs (real_plus (f (real_plus x h))
                                  (real_opp (real_plus (f x) (real_mult h a)))))
                   (real_abs (real_plus (g (real_plus x h))
                                  (real_opp (real_plus (g x) (real_mult h b))))))
        e2)
      (real_plus
        (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                   (real_plus (real_mult e1 (real_abs h)) e2))
        e2))
      by (apply real_le_plus_compat; [exact HT1 | apply real_le_refl]).
    (* —— 4. 链式闭合：|BIG| ≤ |A|+|B|+e2 ≤ 装配式 ≤ eps|h|+eps'（全显式项直构） —— *)
    assert (Hmid : real_eq
      (real_plus
        (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                   (real_plus (real_mult e1 (real_abs h)) e2))
        e2)
      (real_plus (real_mult eps (real_abs h)) eps')).
    { apply real_eq_of_zero_diff. intro n.
      rewrite (real_plus_proj (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                                 (real_plus (real_mult e1 (real_abs h)) e2))
                 e2 n).
      rewrite (real_plus_proj (real_plus (real_mult e1 (real_abs h)) e2)
                 (real_plus (real_mult e1 (real_abs h)) e2) n).
      rewrite (real_plus_proj (real_mult e1 (real_abs h)) e2 n).
      rewrite (real_mult_proj e1 (real_abs h) n).
      rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
      rewrite (real_mult_proj eps (real_abs h) n).
      unfold e1, e2.
      rewrite (real_mult_proj (real_const (1 # 2)) eps n).
      rewrite (real_const_proj (1 # 2) n).
      rewrite (real_mult_proj (real_const (1 # 3)) eps' n).
      rewrite (real_const_proj (1 # 3) n).
      ring. }
    exact (real_le_trans
             (real_abs (real_plus
               (real_plus (f (real_plus x h)) (g (real_plus x h)))
               (real_opp (real_plus (real_plus (f x) (g x))
                                    (real_mult h (real_plus a b))))))
             (real_plus
               (real_plus
                  (real_abs (real_plus (f (real_plus x h))
                             (real_opp (real_plus (f x) (real_mult h a)))))
                  (real_abs (real_plus (g (real_plus x h))
                             (real_opp (real_plus (g x) (real_mult h b))))))
               e2)
             (real_plus (real_mult eps (real_abs h)) eps')
             (real_le_eq_l
                (real_abs (real_plus
                  (real_plus (f (real_plus x h)) (g (real_plus x h)))
                  (real_opp (real_plus (real_plus (f x) (g x))
                                       (real_mult h (real_plus a b))))))
                (real_abs (real_plus
                  (real_plus (f (real_plus x h))
                             (real_opp (real_plus (f x) (real_mult h a))))
                  (real_plus (g (real_plus x h))
                             (real_opp (real_plus (g x) (real_mult h b))))))
                (real_plus
                  (real_plus
                     (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                     (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
                  e2)
                Hrearr Htri)
             (real_le_trans
                (real_plus
                  (real_plus
                     (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                     (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
                  e2)
                (real_plus
                  (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                             (real_plus (real_mult e1 (real_abs h)) e2))
                  e2)
                (real_plus (real_mult eps (real_abs h)) eps')
                HT2
                 (RealSetoid.real_eq_le
                    (real_plus
                      (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                                 (real_plus (real_mult e1 (real_abs h)) e2))
                      e2)
                    (real_plus (real_mult eps (real_abs h)) eps')
                    Hmid))).
Qed.

(* ============================================================ *)
(* 件 1：内点导数封装（b3rr 于收缩内界 0≤ρ<1 的实例化）             *)
(*   结论配形 = φ 复合的 u-侧增量供给（9a-乙 首片指定内容）。        *)
(*   红线3 诚实申明：薄实例化（转发级），见头注。                   *)
(* ============================================================ *)
Lemma abl9_atan_deriv_interior :
  forall (rho : Q) (Hrho0 : Qle 0 rho) (Hrho1 : Qlt rho 1),
  forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) rho),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (Huh : forall n : nat,
                    QleT' (Qabs (projT1 (real_plus u h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u rho Hu Hrho1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros rho Hrho0 Hrho1 u Hu eps Heps.
  exact (b3rr_real_arctan_deriv_linear rho Hrho0 Hrho1 u Hu eps Heps).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                        *)
(*   对账三联：定理名清单 2 = Qed 计数 2 = PA 语句 2，零差。        *)
(* ============================================================ *)
Print Assumptions abl9_atan_diff_sum_rule.
Print Assumptions abl9_atan_deriv_interior.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_atan_diff_sum_rule abl9_atan_deriv_interior.
