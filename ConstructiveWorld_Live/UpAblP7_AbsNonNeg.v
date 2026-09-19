(* ============================================================ *)
(* UpAblP7_AbsNonNeg.v —— 论文7 专项消融战役席 PA7-22                            *)
(*   abs_nonneg 具体层无条件化（T154/PA7-11 余切片申报件）                          *)
(*                                                              *)
(* 母本坐标（union 根现行版实测）                                                 *)
(*   UpReqAlgebra.v:919-922 定谳注记：setoid 接口 abs_nonneg 仅 Bishop 逐 eps 形     *)
(*     （Class RealInterfaceEnhancedSetoid @S07:8004），plain 形不可由 eps 形导出      *)
(*     （无序消去）；接口同位字段 abs_pos @S07:8010 仅严格正前提 lt zero a。           *)
(*   本件目标（申报原文）：无条件「le zero a -> req (abs a) a」——弱非负前提版，          *)
(*     全库无件，本席在具体柯西层（Real，S02/S03 编码）建成。                          *)
(*   S03_QExp.v:6510 real_abs：逐点 Qabs 抬升（Q 层 max/If 面，非 Or 分歧面）          *)
(*   S02_CauchyComplete.v:469 real_le := Or real_lt real_eq（Or 仅在假设侧）          *)
(*                                                              *)
(* 定性结论（T165 台账）：非墙。abs 走 Q 层逐点面，real_le 的 Or 分歧在假设侧可              *)
(*   构造消去（Q 层可判定 Qlt_le_dec，零经典逻辑），两支均有构造路线：                     *)
(*     inl real_lt 支：e 见证逐点定位 Qabs_pos（|a_n|==a_n），差归零；                    *)
(*     inr real_eq 支：对半 eps + Qabs_triangle 双倍放行。                              *)
(*   抽象接口层（forall R RIS）确属墙（接口无 le 消去面），故主件落具体层，                *)
(*   语句面经 Instance RealEnhancedReal @S07:8566 与 UpReqAlgebra 同源（裸名直连，         *)
(*   探针 _probe_pa722.v 实测 exact 双向直连）。                                     *)
(*                                                              *)
(* 工具链实况（实测入坑卡）：本环境 lia 不支持 Q 序目标（最小测件 Cannot find witness）；    *)
(*   Q 上 replace-by-ring/field 侧目标不被 ring/field 认领（同报错）——Q 层代数              *)
(*   变形一律走「assert Qeq by ring/field + rewrite (in)」范式，序链手推。                *)
(*                                                              *)
(* 分级申报：N2 已证导出（Q 层辅件七件，库件 Qabs_pos/Qabs_neg/Qabs_triangle/Qabs_opp     *)
(*   + S02 QltT 桥直连）；N3 实例供给（具体层 Real 载体全构造，零退化）。                  *)
(* 依赖清单：CW_ConstructiveWorld_219（real_lt/real_le/QltT 面）+ UpReqAlgebra           *)
(*   （req_plus_le_lt_pos/lt_le_iff 桥件）——只读消费，原树零改，在飞席零接触。              *)
(* 红线自审：全中文表述；全件真证收口；零假设位（主件除语句前提 le zero a 外零证书）；         *)
(*   文尾 Print Assumptions 逐件全闭合；编译产物只落 /tmp（vo_9.1/Live 只读）。            *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 一、Q 层辅件（除法正性走可判定反证，序链手推，零经典逻辑）                        *)
(* ============================================================ *)

(* 负零恒等（多次复用的变形种子） *)
Lemma uabp7an_qneg0 : (- 0)%Q == 0%Q.
Proof. ring. Qed.

(* e/2 严格正（Qlt_le_dec 可判定反证 + field 换形） *)
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

(* 半加恒等 *)
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

(* 半小于负零形：e/2 < e - 0（0 < e）——供 projT1 投影目标的 conversion 直连 *)
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
   非平凡：Qlt_le_dec 符号分段 + Qabs_pos/Qabs_neg 定位 + 严格放行。
   这是「弱非负（逐 eps 下界）到 |a|==a」的 Q 层核心机。 *)
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
(* 二、主件：具体层无条件 abs 非负件（真 Qed，除语句前提外零假设位）                  *)
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

(* 任务点名语句面（Instance 裸名直连，探针实测 exact 双向）：                       *)
(* 无条件「le zero a -> req (abs a) a」全称件——abs_pos（接口字段，仅 lt zero a）        *)
(* 的弱前提强化版，库内首件。                                                      *)
Lemma uabp7an_abs_nonneg_uncond : forall a : Real,
  le zero a -> req (abs a) a.
Proof. intros a H. exact (uabp7an_core a H). Qed.

(* ============================================================ *)
(* 三、桥①（抽象接口层）：无条件件 ⟹ 接口 eps 形 abs_nonneg（带 le zero a 前提位）     *)
(*   任意载体 R 通用；消费 UpReqAlgebra.req_plus_le_lt_pos + 接口 lt_le_iff/le_id_r。   *)
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
(* 四、桥②（具体层）：Bishop 逐 eps 非负形 ⟹ 无条件件（逆向，构造性非墙）              *)
(*   前提形状=接口 abs_nonneg 字段用在 a 本身（forall eps>0, le zero (a+eps)）。        *)
(*   路线：取四分之一常值见证经 Or 两支提取逐点下界（-a_n < eps/2），                       *)
(*   再由 uabp7an_pt_tail 符号分段收口——Q 层可判定，零经典逻辑。                         *)
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
(* 五、文尾逐件闭合审（Print Assumptions）                                       *)
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
