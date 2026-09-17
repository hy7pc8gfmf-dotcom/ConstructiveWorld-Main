(* ============================================================ *)
(* UpReqLogZWallEquiv.v *)
(* *)
(* 目的： log Z ≤ 0 精确形墙（第四面墙）与受限 LPO 的归约定理化。 *)
(* 主件： lgz_log_z_wall_lpo（泛型槽段正向）与 lgz_lpo_zle（具体反向）。 *)
(* 依赖： S01_BaseRing、S02_CauchyComplete、CW_ConstructiveWorld_219、 *)
(*        UpRealLeB、UpReqGeomD、UpReqLpoEquiv。 *)
(* 备注： 零公理、零假设负载；不证墙命题为假，证其归约强度边界（构造性边界）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqLogZWallEquiv.v —— 席EXPL2：C1 LogZWall 第四面墙定理化        *)
(*                    （LogZ 墙 ⟶ 受限 LPO 归约谱系件）               *)
(*                                                              *)
(* 公理面：本件零公理、零假设负载。墙坐标在案：UpGeomB.v:17-21——      *)
(*   「Or-序编码下 step_kl_eta_bound 的『log Z ≤ 0 精确形』不可证       *)
(*   （等号分支提取需排中）」。上下文 = 几何迭代链：Z := 插值配分       *)
(*   Σ π_t^{1−η}·π*^η，精确 Or 形 KL(π_t‖π_{t+1}) ≤ η·KL(π_t‖π★)      *)
(*   需要 log Z ≤ 0 的精确支，而 Z<1 与 Z==1 的分支不可构造判定。       *)
(*   本件把该「证不了」升级为机器检验的归约边界（新数学·负形定理）：     *)
(*                                                              *)
(*   lgz_LogZWall : Set := 插值数据（正性×2 + 归一化×2 + η∈(0,1]）     *)
(*     全体的 real_le Z real_one 精确判定形（mission 许可语句面；       *)
(*     log 形经 log 单调互为镜像，见尾注「log 形注记」）。              *)
(*                                                              *)
(*   lgz_log_z_wall_lpo（主件·AA22 GibbMechanism 范式）：任一配分函数族  *)
(*     ZWf 带两槽——槽A 族内逐点正（配分语义）+ 槽B 载体编码（任意 x 的   *)
(*     1−x² 形可经某落位点 real_eq 编码进 ZWf 值域）——则其 plain-le 形   *)
(*     给出 SqWall，经 lpn_forward 升为受限 LPO。解码双侧透明：         *)
(*     eq 支经 |1−x²−1| 链 ⟹ x² 逐点归零（Q 环 + 容差半分）；lt 支取     *)
(*     δ:=ε/2 经载体 real_eq 兼容（供隙 ε、余量 ε/2 拼接）⟹ x² 有隙。   *)
(*   lgz_lpo_zle（具体反向·全证）：rLPO ⟹ lgz_LogZWall。决策器施于     *)
(*     y := 1−Z：归零支 ⟹ Z==1（右支）；|1−Z| 隙支 + 弱严格上界          *)
(*     lgz_zle_weak_lt（∀eps>0, real_lt Z (1+eps)——经 real_interp_Z_    *)
(*     le_one_eps 的 Or 两支各通：lt 支直递、eq 支经 real_eq_le +        *)
(*     le-lt 拼接）+ Q 层两分（Z_n<1 / ≥1，后者经 half<5/8 界消去）      *)
(*     ⟹ real_lt Z 1。                                                 *)
(*   对角双槽（具体内容位）：lgz_diag_one（r:=p ⟹ Z==1，exp 加法性      *)
(*     cauchy_real_exp_plus + exp-wd + 分布律环链）与 lgz_diag_no_gap    *)
(*     （对角位 lt 支灭绝：real_lt_not_eq 直驳）——AA22 gwe_diag_zero/   *)
(*     gwe_diag_no_gap 的 LogZ 镜像：墙的全部判据内容活在非对角位的      *)
(*     Z<1-vs-Z==1 二分上。                                             *)
(*                                                              *)
(*   诚实障碍账（具体正向）：lgz_LogZWall ⟹ rLPO 的具体归约需载体编码槽   *)
(*     在真插值族上的实例——编码 x 进严格正归一 r₀,r₁（如 e^x/(1+e^x)     *)
(*     形）后 Z 值域为 Hellinger 型 [1/√2,1]，Z==1 ⟺ x==0 的解码链需     *)
(*     exp 投影不透明层的量化 log/exp 代数（exp 单调 + 左右逆 + 间隙      *)
(*     搬运），非本席窗口可封；故具体正向以泛型槽段条件形承载（AA22       *)
(*     「泛型段只做正向」先例同格），具体反向全证。两向合账：LogZWall     *)
(*     与 rLPO 的精确归约强度双向均未封口，本件交付该边界的机器检验      *)
(*     部分。                                                          *)
(*                                                              *)
(*   同族注记（C15·G05_LogSmall.v:893 判定表）：log 等号桥墙（log_eq_   *)
(*     linear 族 X 阻塞位「需强三分/受限 LPO」）与本件同属 LPO 归约      *)
(*     家族，但其等号凹性机制与本件的 Z-二分机制归约未同构在案，         *)
(*     不并类，留未归约注记（如实）。                                  *)
(*   消费面：S05_AlignmentGRPO.v:4404 step_kl_eta_bound 接口的精确形      *)
(*     依赖本墙——本件即该接口「不可消解性」的证书（与在飞席 GEOM-A      *)
(*     的 eps 形实例化件 UpReqStepKLEtaInst.v 互补：彼证 eps 可达形，    *)
(*     此证精确形归约强度）。                                          *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、语句面全 Type/sigT/自定义 And/Or/QltT，       *)
(*       零 Prop 泄露、零硬凑；墙语句为假设形参数化，全程零经典逻辑。    *)
(* 依赖：S01_BaseRing（And/Or/NatLe）+ S02_CauchyComplete（Real/序）     *)
(*       + CW/UpRealLeB/UpReqGeomD（interp-Z 求和面）+ UpReqLpoEquiv     *)
(*       （rLPO/lpn_forward/Q 层桥）。                                 *)
(* ------------------------------------------------------------ *)
(* EXPL2（20260916）：新建。前缀 lgz_（grep 全库零撞名实测）。          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqGeomD.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：Q 层小桥（Qlt_alt 破形 + 位移 helper + Qabs 界）          *)
(* ============================================================ *)

Lemma lgz_q_pos_half : Qlt 0 (1#2).
Proof.
  apply (proj2 (Qlt_alt 0 (1#2))).
  reflexivity.
Qed.

Lemma lgz_q_pos_quarter : Qlt 0 (1#4).
Proof.
  apply (proj2 (Qlt_alt 0 (1#4))).
  reflexivity.
Qed.

Lemma lgz_q_pos_quarterT : QltT 0 (1#4).
Proof.
  apply Qlt_to_QltT.
  exact lgz_q_pos_quarter.
Qed.

(* 位移三件与 Qabs 界拆分（lra 封口；非线性单项式按原子抽象） *)
Lemma lgz_q_lt_add_l : forall a b c : Q, a + b < c -> a < c - b.
Proof.
  intros a b c H.
  lra.
Qed.

Lemma lgz_q_lt_add_r : forall a b c : Q, a + b < c -> b < c - a.
Proof.
  intros a b c H.
  lra.
Qed.

Lemma lgz_q_plus_lt_r : forall u v w : Q, u < v -> u + w < v + w.
Proof.
  intros u v w H.
  lra.
Qed.

Lemma lgz_q_plus_lt_l : forall u v w : Q, u < v -> w + u < w + v.
Proof.
  intros u v w H.
  lra.
Qed.

(* Qabs 界拆分：0 < b ∧ |a| < b ⟹ a < b（上界）/ −b < a（下界） *)
Lemma lgz_q_abs_lt_bounds_ub : forall a b : Q,
  0 < b -> Qabs a < b -> a < b.
Proof.
  intros a b Hb0 H.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in H.
    exact H.
  - rewrite (Qabs_neg a Hneg) in H.
    lra.
Qed.

Lemma lgz_q_abs_lt_bounds_lb : forall a b : Q,
  0 < b -> Qabs a < b -> - b < a.
Proof.
  intros a b Hb0 H.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in H.
    lra.
  - rewrite (Qabs_neg a Hneg) in H.
    lra.
Qed.

(* Qeq 位移四件：Qlt/Qabs 位换形（q_eq_le/q_abs_congr 桥）——
   Qeq 集合重写只在 Qeq-目标内可用（AA22 先例），Qlt/Id 位经此四件搬运 *)
Lemma lgz_qlt_shift : forall u u' w : Q, u == u' -> Qlt u w -> Qlt u' w.
Proof.
  intros u u' w Huu H.
  apply (Qle_lt_trans u' u w).
  - apply q_eq_le.
    apply Qeq_sym.
    exact Huu.
  - exact H.
Qed.

Lemma lgz_qlt_shift2_r : forall w u u' : Q, u == u' -> Qlt w u -> Qlt w u'.
Proof.
  intros w u u' Huu H.
  apply (Qlt_le_trans w u u').
  - exact H.
  - apply q_eq_le.
    exact Huu.
Qed.

Lemma lgz_qlt_abs_shift : forall a a' w : Q,
  a == a' -> Qlt (Qabs a) w -> Qlt (Qabs a') w.
Proof.
  intros a a' w Haa H.
  apply (Qle_lt_trans (Qabs a') (Qabs a) w).
  - apply q_eq_le.
    apply q_abs_congr.
    apply Qeq_sym.
    exact Haa.
  - exact H.
Qed.

Lemma lgz_qlt_shift_r : forall w u u' : Q,
  u == u' -> Qlt w (Qabs u) -> Qlt w (Qabs u').
Proof.
  intros w u u' Huu H.
  apply (Qlt_le_trans w (Qabs u) (Qabs u')).
  - exact H.
  - apply q_eq_le.
    apply q_abs_congr.
    exact Huu.
Qed.

(* 解码封口（lt 支）：ε>0 ∧ ε < 1−a ∧ |a−(1−b)| < ε/2 ⟹ ε/2 < b *)
Lemma lgz_q_decode_lt : forall eps a b : Q,
  0 < eps -> Qlt eps (1 - a) ->
  Qlt (Qabs (a - (1 - b))) (eps * (1#2)) ->
  Qlt (eps * (1#2)) b.
Proof.
  intros eps a b Heps H1 H2.
  destruct (Qlt_le_dec 0 (a - (1 - b))) as [Hp | Hn].
  - rewrite (Qabs_pos _ (Qlt_le_weak _ _ Hp)) in H2.
    lra.
  - rewrite (Qabs_neg _ Hn) in H2.
    lra.
Qed.

(* 解码封口（eq 支）：|a−(1−b)| < δ/2 ∧ |a−1| < δ/2 ⟹ |0−b| < δ *)
Lemma lgz_q_decode_eq : forall del a b : Q,
  Qlt (Qabs (a - (1 - b))) (del * (1#2)) ->
  Qlt (Qabs (a - 1)) (del * (1#2)) ->
  Qlt (Qabs (0 - b)) del.
Proof.
  intros del a b H1 H2.
  apply (lgz_qlt_abs_shift (((1 - b) + (- a)) + (a - 1)) (0 - b) del).
  - ring.
  - apply (Qle_lt_trans (Qabs (((1 - b) + (- a)) + (a - 1)))
             (Qabs ((1 - b) + (- a)) + Qabs (a - 1)) del).
    + apply Qabs_triangle.
    + assert (H1' : Qlt (Qabs ((1 - b) + (- a))) (del * (1#2))).
      { apply (Qle_lt_trans (Qabs ((1 - b) + (- a)))
                 (Qabs (a - (1 - b))) (del * (1#2))).
        - apply q_eq_le.
          rewrite <- (Qabs_opp (a - (1 - b))).
          apply q_abs_congr.
          ring.
        - exact H1. }
      lra.
Qed.

(* ============================================================ *)
(* Part 2：Real 层小桥 + 半量机 lgz_half                             *)
(* ============================================================ *)

(* le + lt 拼接（geod_b_le_lt_trans 同体） *)
Lemma lgz_le_lt_trans : forall x y z : Real,
  real_le x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt.
  destruct Hle as [Hlt' | Heq].
  - exact (real_lt_trans x y z Hlt' Hlt).
  - exact (real_eq_lt_lt x y z Heq Hlt).
Qed.

(* 半量：inv2 := 1/(1+1)（正性证书内嵌） *)
Definition lgz_half : Real :=
  real_inv_pos (real_plus real_one real_one)
    (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).

Lemma lgz_half_eq :
  real_eq (real_mult (real_plus real_one real_one) lgz_half) real_one.
Proof.
  exact (real_inv_pos_correct (real_plus real_one real_one)
           (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one)).
Qed.

(* half < 1：隙 3/8 *)
Lemma lgz_half_lt_one : real_lt lgz_half real_one.
Proof.
  exists (3#8). split.
  - apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt 0 (3#8))).
    reflexivity.
  - destruct (lgz_half_eq (1#4) lgz_q_pos_quarterT) as [N HN].
    exists N. intros m Hm.
    pose proof (HN m Hm) as HNb.
    apply QltT_to_Qlt in HNb.
    assert (Hpj : projT1 (real_mult (real_plus real_one real_one) lgz_half) m
                  == (1 + 1) * projT1 lgz_half m).
    { rewrite (real_mult_proj (real_plus real_one real_one) lgz_half m).
      reflexivity. }
    rewrite Hpj in HNb.
    assert (Hone : projT1 real_one m == 1) by reflexivity.
    rewrite Hone in HNb.
    pose proof (lgz_q_abs_lt_bounds_ub ((1 + 1) * projT1 lgz_half m - 1)
                  (1#4) lgz_q_pos_quarter HNb) as Hub.
    assert (Hb2 : (1 + 1) * projT1 lgz_half m < (5#4)) by lra.
    assert (Hb3 : projT1 lgz_half m < (5#8)).
    { assert (Hm1 : ((1 + 1) * projT1 lgz_half m) * (1#2) < (5#4) * (1#2))
        by (apply (Qmult_lt_compat_r _ _ (1#2));
            [apply (proj2 (Qlt_alt 0 (1#2))); reflexivity | exact Hb2]).
      assert (Hm2 : ((1 + 1) * projT1 lgz_half m) * (1#2)
                    == projT1 lgz_half m) by ring.
      rewrite Hm2 in Hm1.
      assert (Hm3 : (5#4) * (1#2) == (5#8)) by ring.
      rewrite Hm3 in Hm1.
      exact Hm1. }
    apply Qlt_to_QltT.
    apply (lgz_qlt_shift2_r (3#8) (1 - projT1 lgz_half m)
             (projT1 real_one m - projT1 lgz_half m)).
    + rewrite Hone.
      ring.
    + apply (lgz_q_lt_add_l (3#8) (projT1 lgz_half m) 1).
      assert (Hg : (3#8) + projT1 lgz_half m < (3#8) + (5#8))
        by (apply (lgz_q_plus_lt_l _ _ (3#8)); exact Hb3).
      assert (Hg2 : (3#8) + (5#8) == 1) by ring.
      rewrite Hg2 in Hg.
      exact Hg.
Qed.

(* half 投影的一致 5/8 上界（事件形，供反向解码） *)
Lemma lgz_half_eventual_ub :
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    Qlt (projT1 lgz_half m) (5#8)).
Proof.
  destruct (lgz_half_eq (1#4) lgz_q_pos_quarterT) as [Nv HNv].
  exists Nv. intros m Hm.
  pose proof (HNv m Hm) as Hb.
  apply QltT_to_Qlt in Hb.
  assert (Hpj : projT1 (real_mult (real_plus real_one real_one) lgz_half) m
                == (1 + 1) * projT1 lgz_half m).
  { rewrite (real_mult_proj (real_plus real_one real_one) lgz_half m).
    reflexivity. }
  rewrite Hpj in Hb.
  assert (Hone : projT1 real_one m == 1) by reflexivity.
  rewrite Hone in Hb.
  pose proof (lgz_q_abs_lt_bounds_ub ((1 + 1) * projT1 lgz_half m - 1)
                (1#4) lgz_q_pos_quarter Hb) as Hub.
  assert (H1 : (1 + 1) * projT1 lgz_half m < (5#4)) by lra.
  assert (H1b : ((1 + 1) * projT1 lgz_half m) * (1#2) < (5#4) * (1#2)).
  { apply (Qmult_lt_compat_r ((1 + 1) * projT1 lgz_half m) (5#4) (1#2)).
    - apply (proj2 (Qlt_alt 0 (1#2))).
      reflexivity.
    - exact H1. }
  assert (H2 : ((1 + 1) * projT1 lgz_half m) * (1#2)
               == projT1 lgz_half m) by ring.
  rewrite H2 in H1b.
  assert (H3 : (5#4) * (1#2) == (5#8)) by ring.
  rewrite H3 in H1b.
  exact H1b.
Qed.

(* ε/2 < ε（严格，ε>0） *)
Lemma lgz_half_lt_eps : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult eps lgz_half) eps.
Proof.
  intros eps Heps.
  apply (real_lt_eq_lt (real_mult eps lgz_half) (real_mult eps real_one) eps).
  - exact (real_mult_lt_compat_l lgz_half real_one eps lgz_half_lt_one Heps).
  - exact (real_mult_one eps).
Qed.

(* (1 + ε/2) < (1 + ε) *)
Lemma lgz_one_half_lt_one : forall eps : Real,
  real_lt real_zero eps ->
  real_lt (real_plus real_one (real_mult eps lgz_half)) (real_plus real_one eps).
Proof.
  intros eps Heps.
  apply (real_eq_lt_lt _ (real_plus (real_mult eps lgz_half) real_one)
           (real_plus real_one eps)).
  - exact (real_eq_sym _ _ (real_plus_comm (real_mult eps lgz_half) real_one)).
  - apply (real_lt_eq_lt _ (real_plus eps real_one) _).
    + exact (real_lt_plus_compat_lt_le (real_mult eps lgz_half) eps real_one
               real_one (lgz_half_lt_eps eps Heps) (real_le_refl real_one)).
    + exact (real_plus_comm eps real_one).
Qed.

(* ============================================================ *)
(* Part 3：具体墙语句面（Z ≤ 1 精确判定形）                          *)
(* ============================================================ *)

Definition lgz_LogZWall : Set :=
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le (real_interp_Z n p r eta Hp Hr) real_one.

(* ============================================================ *)
(* Part 4：泛型槽段（AA22 GibbMechanism 范式）——主件                 *)
(* ============================================================ *)

Section LogZMechanism.

Variable ZWf : Real -> Real.

(* 槽：载体编码——任意 x 的 1−x² 形可编码进 ZWf 值域。
   注：族内逐点正（配分语义位）在 Z-形正向中不被消费（log 形接口才需要），
   故不入段（段封闭会丢弃未消费槽），如实移除。 *)
Hypothesis lgmech_carr : forall x : Real,
  sigT (fun xi : Real =>
    real_eq (ZWf xi) (real_plus real_one (real_opp (real_mult x x)))).

(* 泛型墙 plain-le 形 ⟹ SqWall（解码双侧透明） *)
Theorem lgmech_wall_zle :
  (forall x : Real, real_le (ZWf x) real_one) -> SqWall.
Proof.
  intros Hwall x.
  destruct (lgmech_carr x) as [xi Heq].
  destruct (Hwall xi) as [Hlt | Heq1].
  - (* 左支：ZWf ξ < 1 带隙 ε ⟹ x·x 有隙（δ := ε/2） *)
    apply inl.
    destruct Hlt as [eps [Heps [N HN]]].
    assert (Hq2 : QltT 0 (eps * (1#2))).
    { apply Qlt_to_QltT.
      assert (H0 : 0 * (1#2) < eps * (1#2))
        by (apply Qmult_lt_compat_r;
            [exact lgz_q_pos_half | apply QltT_to_Qlt; exact Heps]).
      rewrite Qmult_0_l in H0.
      exact H0. }
    destruct (Heq (eps * (1#2)) Hq2) as [N2 HN2].
    exists (eps * (1#2)). split.
    + exact Hq2.
    + exists (Nat.max N N2). intros n Hn.
      assert (Hmn : NatLe N n).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hn) as Hdn.
        lia. }
      assert (Hmn2 : NatLe N2 n).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hn) as Hdn.
        lia. }
      assert (Hone : projT1 real_one n == 1) by reflexivity.
      (* H1 换形：eps < 1 − a（Qeq 位移桥） *)
      assert (H1 : Qlt eps (1 - projT1 (ZWf xi) n)).
      { pose proof (HN n Hmn) as HNn.
        pose proof (QltT_to_Qlt eps
                      (projT1 real_one n - projT1 (ZWf xi) n) HNn) as HNn'.
        apply (lgz_qlt_shift2_r eps (projT1 real_one n - projT1 (ZWf xi) n)
                 (1 - projT1 (ZWf xi) n)).
        - rewrite Hone.
          ring.
        - exact HNn'. }
      (* H2 换形：|a − (1−b)| < ε/2（Qeq 位移桥） *)
      assert (H2 : Qlt (Qabs (projT1 (ZWf xi) n
                                - (1 - projT1 x n * projT1 x n)))
                       (eps * (1#2))).
      { pose proof (HN2 n Hmn2) as HN2n.
        pose proof (QltT_to_Qlt
                      (Qabs
                         (projT1 (ZWf xi) n
                            - (projT1 (real_plus real_one
                                         (real_opp (real_mult x x))) n)))
                      (eps * (1#2)) HN2n) as HN2n'.
        apply (lgz_qlt_abs_shift
                 (projT1 (ZWf xi) n
                    - (projT1 (real_plus real_one
                                 (real_opp (real_mult x x))) n))
                 (projT1 (ZWf xi) n
                    - (1 - projT1 x n * projT1 x n))
                 (eps * (1#2))).
        - rewrite (real_plus_proj real_one (real_opp (real_mult x x)) n).
          rewrite (real_opp_proj (real_mult x x) n).
          rewrite (real_mult_proj x x n).
          rewrite Hone.
          ring.
        - exact HN2n'. }
      assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      assert (Hfin : Qlt (eps * (1#2)) (projT1 x n * projT1 x n))
        by (apply (lgz_q_decode_lt eps (projT1 (ZWf xi) n)
                     (projT1 x n * projT1 x n) HepsQ H1 H2)).
      (* 终局搬运：目标位 projT1 (real_mult x x) n − projT1 real_zero n *)
      apply Qlt_to_QltT.
      apply (lgz_qlt_shift2_r (eps * (1#2))
               (projT1 x n * projT1 x n)
               (projT1 (real_mult x x) n - projT1 real_zero n)).
      * rewrite (real_mult_proj x x n).
        assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz0.
        ring.
      * exact Hfin.
  - (* 右支：ZWf ξ == 1 ⟹ x·x 逐点归零（容差半分 + 三角不等式） *)
    apply inr.
    intros del Hdel.
    assert (Hq2 : QltT 0 (del * (1#2))).
    { apply Qlt_to_QltT.
      assert (H0 : 0 * (1#2) < del * (1#2))
        by (apply Qmult_lt_compat_r;
            [exact lgz_q_pos_half | apply QltT_to_Qlt; exact Hdel]).
      rewrite Qmult_0_l in H0.
      exact H0. }
    destruct (Heq (del * (1#2)) Hq2) as [N1 HN1].
    destruct (Heq1 (del * (1#2)) Hq2) as [N2 HN2].
    exists (Nat.max N1 N2). intros n Hn.
    assert (Hmn1 : NatLe N1 n).
    { apply NatLe_lift.
      pose proof (NatLe_drop _ _ Hn) as Hdn.
      lia. }
    assert (Hmn2 : NatLe N2 n).
    { apply NatLe_lift.
      pose proof (NatLe_drop _ _ Hn) as Hdn.
      lia. }
    assert (Hone : projT1 real_one n == 1) by reflexivity.
    (* H1r 换形：|a − (1−b)| < δ/2 *)
    assert (H1r : Qlt (Qabs (projT1 (ZWf xi) n
                                - (1 - projT1 x n * projT1 x n)))
                       (del * (1#2))).
    { pose proof (HN1 n Hmn1) as HN1n.
      pose proof (QltT_to_Qlt
                    (Qabs
                       (projT1 (ZWf xi) n
                          - (projT1 (real_plus real_one
                                       (real_opp (real_mult x x))) n)))
                    (del * (1#2)) HN1n) as HN1n'.
      apply (lgz_qlt_abs_shift
               (projT1 (ZWf xi) n
                  - (projT1 (real_plus real_one
                               (real_opp (real_mult x x))) n))
               (projT1 (ZWf xi) n
                  - (1 - projT1 x n * projT1 x n))
               (del * (1#2))).
      - rewrite (real_plus_proj real_one (real_opp (real_mult x x)) n).
        rewrite (real_opp_proj (real_mult x x) n).
        rewrite (real_mult_proj x x n).
        rewrite Hone.
        ring.
      - exact HN1n'. }
    (* H2r 换形：|a − 1| < δ/2 *)
    assert (H2r : Qlt (Qabs (projT1 (ZWf xi) n - 1)) (del * (1#2))).
    { pose proof (HN2 n Hmn2) as HN2n.
      pose proof (QltT_to_Qlt
                    (Qabs (projT1 (ZWf xi) n - projT1 real_one n))
                    (del * (1#2)) HN2n) as HN2n'.
      apply (lgz_qlt_abs_shift
               (projT1 (ZWf xi) n - projT1 real_one n)
               (projT1 (ZWf xi) n - 1)
               (del * (1#2))).
      - rewrite Hone.
        ring.
      - exact HN2n'. }
    (* 终局搬运 *)
    apply Qlt_to_QltT.
    apply (lgz_qlt_abs_shift (0 - projT1 x n * projT1 x n)
             (projT1 real_zero n - projT1 (real_mult x x) n) del).
    * rewrite (real_mult_proj x x n).
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      ring.
    * exact (lgz_q_decode_eq del (projT1 (ZWf xi) n)
               (projT1 x n * projT1 x n) H1r H2r).
Qed.

(* 主件：泛型墙 plain-le 形 ⟹ 受限 LPO（lpn_forward 升维） *)
Theorem lgz_log_z_wall_lpo :
  (forall x : Real, real_le (ZWf x) real_one) -> rLPO.
Proof.
  intros Hwall.
  exact (lpn_forward (lgmech_wall_zle Hwall)).
Qed.

End LogZMechanism.

(* ============================================================ *)
(* Part 5：对角双槽（具体内容位）——r := p ⟹ Z == 1 与左支灭绝         *)
(* ============================================================ *)

(* 逐点幂拆：p^{1−η}·p^η == p（exp 加法性 + exp-wd + 分布律环链） *)
Lemma lgz_pow_split : forall (y : Real) (Hy : real_lt real_zero y) (eta : Real),
  real_eq (real_mult (real_pow_pos y (real_plus real_one (real_opp eta)) Hy)
                     (real_pow_pos y eta Hy))
            y.
Proof.
  intros y Hy eta.
  unfold real_pow_pos.
  apply (real_eq_trans
           (real_mult (cauchy_real_exp
                          (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy)))
                      (cauchy_real_exp (real_mult eta (cw_log y Hy))))
           (cauchy_real_exp
              (real_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                 (real_mult eta (cw_log y Hy))))
           y).
  - apply real_eq_sym.
    exact (cauchy_real_exp_plus
             (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
             (real_mult eta (cw_log y Hy))).
  - apply (real_eq_trans
             (cauchy_real_exp
                (real_plus
                   (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                   (real_mult eta (cw_log y Hy))))
             (cauchy_real_exp
                (real_mult (cw_log y Hy)
                   (real_plus (real_plus real_one (real_opp eta)) eta)))
             y).
    + apply cauchy_real_exp_wd.
      apply (real_eq_trans
               (real_plus
                  (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                  (real_mult eta (cw_log y Hy)))
               (real_plus
                  (real_mult (cw_log y Hy) (real_plus real_one (real_opp eta)))
                  (real_mult (cw_log y Hy) eta))
               (real_mult (cw_log y Hy)
                  (real_plus (real_plus real_one (real_opp eta)) eta))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log y Hy))
                 (real_mult eta (cw_log y Hy))
                 (real_mult (cw_log y Hy) (real_plus real_one (real_opp eta)))
                 (real_mult (cw_log y Hy) eta)).
        -- exact (real_mult_comm (real_plus real_one (real_opp eta)) (cw_log y Hy)).
        -- exact (real_mult_comm eta (cw_log y Hy)).
      * exact (real_eq_sym _ _ (real_distrib (cw_log y Hy)
                    (real_plus real_one (real_opp eta)) eta)).
+ apply (real_eq_trans
               (cauchy_real_exp
                  (real_mult (cw_log y Hy)
                     (real_plus (real_plus real_one (real_opp eta)) eta)))
               (cauchy_real_exp (cw_log y Hy))
               y).
  * apply cauchy_real_exp_wd.
    apply (real_eq_trans
             (real_mult (cw_log y Hy)
                (real_plus (real_plus real_one (real_opp eta)) eta))
             (real_mult (cw_log y Hy) real_one)
             (cw_log y Hy)).
    -- apply (RealSetoid.real_eq_mult_compat
               (cw_log y Hy)
               (real_plus (real_plus real_one (real_opp eta)) eta)
               (cw_log y Hy) real_one).
      ++ exact (real_eq_refl (cw_log y Hy)).
      ++ destruct eta as [e He].
         apply real_eq_of_zero_diff.
         intro k.
         simpl.
         ring.
    -- exact (real_mult_one (cw_log y Hy)).
  * exact (cw_log_exp_right y Hy).
Qed.

(* 对角单位槽：r := p ⟹ Z == 1（AA22 gwe_diag_zero 的 LogZ 镜像） *)
Lemma lgz_diag_one : forall (n : nat) (p : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one),
  real_eq (real_interp_Z n p p eta Hp Hp) real_one.
Proof.
  intros n p eta Hp Hnp.
  unfold real_interp_Z.
  apply (real_eq_trans
           (real_list_sum nat
              (fun i : nat => real_mult
                 (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                 (real_pow_pos (p i) eta (Hp i)))
              (List.seq 0 n))
           (real_list_sum nat p (List.seq 0 n))
           real_one).
  - apply real_list_sum_ext.
    intro i.
    exact (lgz_pow_split (p i) (Hp i) eta).
  - exact Hnp.
Qed.

(* 对角左支灭绝：r := p 时 real_lt Z 1 驳斥（AA22 gwe_diag_no_gap 镜像） *)
Lemma lgz_diag_no_gap : forall (n : nat) (p : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one),
  real_lt (real_interp_Z n p p eta Hp Hp) real_one -> forall A : Set, A.
Proof.
  intros n p eta Hp Hnp Hlt A.
  destruct (real_lt_not_eq (real_interp_Z n p p eta Hp Hp) real_one
              Hlt (lgz_diag_one n p eta Hp Hnp)).
Qed.

(* ============================================================ *)
(* Part 6：弱严格上界 + 具体反向（rLPO ⟹ 墙）                        *)
(* ============================================================ *)

(* 弱严格上界：∀eps>0, Z < 1+eps（real_interp_Z_le_one_eps 的 Or 两支各通） *)
Lemma lgz_zle_weak_lt :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one)
    (eps : Real), real_lt real_zero eps ->
  real_lt (real_interp_Z n p r eta Hp Hr) (real_plus real_one eps).
Proof.
  intros n p r eta Hp Hr Hnp Hnr Heta Hetale eps Heps.
  assert (Hstep : real_lt (real_plus real_one (real_mult eps lgz_half))
                          (real_plus real_one eps))
    by (apply (lgz_one_half_lt_one eps Heps)).
  destruct (real_interp_Z_le_one_eps n p r eta Hp Hr Hnp Hnr Heta Hetale
              (real_mult eps lgz_half)
              (real_mult_positive eps lgz_half Heps
                 (real_inv_pos_pos (real_plus real_one real_one)
                    (real_plus_positive real_one real_one
                       real_lt_zero_one real_lt_zero_one)))) as [Hlt | Heq].
  - exact (real_lt_trans (real_interp_Z n p r eta Hp Hr)
             (real_plus real_one (real_mult eps lgz_half))
             (real_plus real_one eps) Hlt Hstep).
  - exact (lgz_le_lt_trans (real_interp_Z n p r eta Hp Hr)
             (real_plus real_one (real_mult eps lgz_half))
             (real_plus real_one eps) (RealSetoid.real_eq_le _ _ Heq) Hstep).
Qed.

(* 具体反向：受限 LPO ⟹ LogZ 墙（Z ≤ 1 精确判定形） *)
Theorem lgz_lpo_zle : rLPO -> lgz_LogZWall.
Proof.
  intros Hdec n p r eta Hp Hr Hnp Hnr Heta Hetale.
  assert (Hhalfpos : real_lt real_zero lgz_half)
    by exact (real_inv_pos_pos (real_plus real_one real_one)
                (real_plus_positive real_one real_one
                   real_lt_zero_one real_lt_zero_one)).
  destruct (lgz_half_eventual_ub) as [Nv HNv].
  destruct (Hdec (real_plus real_one
                    (real_opp (real_interp_Z n p r eta Hp Hr))))
    as [[c [Hc [N HN]]] | Hz].
  - (* |1−Z| ≥ c ⟹ Z < 1（Q 层两分消去 ≥1 支） *)
    apply inl.
    assert (Hcpos : Qlt 0 c) by (apply QltT_to_Qlt; exact Hc).
    assert (Hcp : real_lt real_zero (real_const c)).
    { unfold real_lt.
      exists (c * (1#2)). split.
      - apply Qlt_to_QltT.
        assert (H0 : 0 * (1#2) < c * (1#2))
          by (apply (Qmult_lt_compat_r 0 c (1#2));
              [exact lgz_q_pos_half | exact Hcpos]).
        rewrite Qmult_0_l in H0.
        exact H0.
      - exists O. intros n0 _. apply Qlt_to_QltT.
        assert (Hcz : projT1 (real_const c) n0 == c) by reflexivity.
        rewrite Hcz.
        assert (Hz0 : projT1 real_zero n0 == 0) by reflexivity.
        rewrite Hz0.
        lra. }
    destruct (lgz_zle_weak_lt n p r eta Hp Hr Hnp Hnr Heta Hetale
                (real_mult (real_const c) lgz_half)
                (real_mult_positive (real_const c) lgz_half Hcp Hhalfpos))
      as [eps2 [Heps2 [N2 HN2]]].
    exists c. split.
    + exact Hc.
    + exists (Nat.max N (Nat.max N2 Nv)). intros m Hm.
      assert (HmN : NatLe N m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (HmN2 : NatLe N2 m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (HmNv : NatLe Nv m).
      { apply NatLe_lift.
        pose proof (NatLe_drop _ _ Hm) as Hdn.
        lia. }
      assert (Hone : projT1 real_one m == 1) by reflexivity.
      assert (Hcz : projT1 (real_const c) m == c) by reflexivity.
      set (Zm := projT1 (real_interp_Z n p r eta Hp Hr) m) in *.
      (* HN 换形：c < |1 − Zm|（Qeq 位移桥） *)
      assert (Habs1 : Qlt c (Qabs (1 - Zm))).
      { pose proof (HN m HmN) as HNn.
        pose proof (QltT_to_Qlt c
                      (Qabs
                         (projT1 (real_plus real_one
                                    (real_opp (real_interp_Z n p r eta Hp Hr))) m)) HNn) as HNn'.
        apply (lgz_qlt_shift_r c
                 (projT1 (real_plus real_one
                            (real_opp (real_interp_Z n p r eta Hp Hr))) m)
                 (1 - Zm)).
        - unfold Zm.
          rewrite (real_plus_proj real_one
                     (real_opp (real_interp_Z n p r eta Hp Hr)) m).
          rewrite (real_opp_proj (real_interp_Z n p r eta Hp Hr) m).
          lra.
        - exact HNn'. }
      pose proof (HN2 m HmN2) as H2r.
      pose proof (HNv m HmNv) as H58.
      (* H2r 换形：eps2 < 1 + c·half_m − Zm *)
      assert (H2r' : Qlt eps2 (1 + c * projT1 lgz_half m - Zm)).
      { pose proof (QltT_to_Qlt eps2
                      (projT1 (real_plus real_one
                                 (real_mult (real_const c) lgz_half)) m -
                       projT1 (real_interp_Z n p r eta Hp Hr) m) H2r) as H2r'.
        apply (lgz_qlt_shift2_r eps2
                 (projT1 (real_plus real_one
                            (real_mult (real_const c) lgz_half)) m -
                  projT1 (real_interp_Z n p r eta Hp Hr) m)
                 (1 + c * projT1 lgz_half m - Zm)).
        - unfold Zm.
          rewrite (real_plus_proj real_one
                     (real_mult (real_const c) lgz_half) m).
          rewrite (real_mult_proj (real_const c) lgz_half m).
          rewrite Hcz.
          rewrite Hone.
          lra.
        - exact H2r'. }
      (* 半量桥：c·half_m < c *)
      assert (Hchc : Qlt (c * projT1 lgz_half m) c).
      { assert (H1 : Qlt (projT1 lgz_half m * c) ((5#8) * c))
          by (apply (Qmult_lt_compat_r (projT1 lgz_half m) (5#8) c);
              [exact Hcpos | exact H58]).
        assert (H2 : Qlt ((5#8) * c) (1 * c))
          by (apply (Qmult_lt_compat_r (5#8) 1 c);
              [exact Hcpos | apply (proj2 (Qlt_alt (5#8) 1)); reflexivity]).
        assert (H3 : 1 * c == c) by ring.
        rewrite H3 in H2.
        assert (Hr4 : projT1 lgz_half m * c == c * projT1 lgz_half m) by ring.
        apply (lgz_qlt_shift (projT1 lgz_half m * c)
                 (c * projT1 lgz_half m) c).
        - exact Hr4.
        - exact (Qlt_trans _ _ _ H1 H2). }
      (* Zm < 1 + c·half_m（弱严格上界的直接读出） *)
      assert (Hs1 : Qlt Zm (1 + c * projT1 lgz_half m)).
      { assert (Hpos2 : Qlt 0 eps2) by (apply QltT_to_Qlt; exact Heps2).
        lra. }
      assert (Hs3 : Qlt Zm (1 + c)).
      { apply (Qlt_trans Zm (1 + c * projT1 lgz_half m) (1 + c)).
        - exact Hs1.
        - apply (lgz_q_plus_lt_l (c * projT1 lgz_half m) c 1).
          exact Hchc. }
      destruct (Qlt_le_dec Zm 1) as [Hlt1 | Hge1].
      { (* Z_m < 1：c < 1 − Z_m 直得 *)
        apply Qlt_to_QltT.
        assert (Habsp : Qabs (1 - Zm) == 1 - Zm)
          by (apply Qabs_pos; lra).
        apply (lgz_qlt_shift2_r c (1 - Zm) (projT1 real_one m - Zm)).
        { rewrite Hone.
          ring. }
        { exact (lgz_qlt_shift2_r c (Qabs (1 - Zm)) (1 - Zm) Habsp Habs1). } }
      { (* Z_m ≥ 1：与 HN 矛盾，消去 *)
        exfalso.
        assert (Hle : Qle (1 - Zm) 0) by lra.
        assert (Habsp : Qabs (1 - Zm) == - (1 - Zm))
          by (apply q_abs_neg_eq; exact Hle).
        assert (HN2c : Qlt c (- (1 - Zm)))
          by (apply (lgz_qlt_shift2_r c (Qabs (1 - Zm)) (- (1 - Zm)));
              [ exact Habsp | exact Habs1 ]).
        apply (Qlt_irrefl c).
        apply (Qlt_le_trans c (Zm - 1) c).
        { apply (lgz_qlt_shift2_r c (- (1 - Zm)) (Zm - 1)).
          - ring.
          - exact HN2c. }
        { lra. } }
  - (* 1−Z 逐点归零 ⟹ Z == 1（右支） *)
    apply inr.
    intros del Hdel.
    destruct (Hz del Hdel) as [N HN].
    exists N. intros m Hm.
    assert (Hone : projT1 real_one m == 1) by reflexivity.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (projT1 (real_interp_Z n p r eta Hp Hr) m - projT1 real_one m))
             (Qabs (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m)) del).
    + apply q_eq_le.
      rewrite <- (Qabs_opp (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m)).
      apply q_abs_congr.
      ring.
    + pose proof (HN m Hm) as HNn.
      pose proof (QltT_to_Qlt
                    (Qabs
                       (projT1 (real_plus real_one
                                  (real_opp (real_interp_Z n p r eta Hp Hr))) m)) del HNn) as HNn'.
      apply (lgz_qlt_abs_shift
               (projT1 (real_plus real_one
                          (real_opp (real_interp_Z n p r eta Hp Hr))) m)
               (projT1 real_one m - projT1 (real_interp_Z n p r eta Hp Hr) m) del).
      { rewrite (real_plus_proj real_one
                   (real_opp (real_interp_Z n p r eta Hp Hr)) m).
        rewrite (real_opp_proj (real_interp_Z n p r eta Hp Hr) m).
        rewrite Hone.
        ring. }
      { exact HNn'. }
Qed.

(* ============================================================ *)
(* Part 7：判定件——合账（泛型正向 + 具体反向）                        *)
(* ============================================================ *)

Definition lgz_equivalence :
  And (forall (ZWf : Real -> Real),
         (forall x : Real,
             sigT (fun xi : Real =>
               real_eq (ZWf xi)
                 (real_plus real_one (real_opp (real_mult x x))))) ->
         (forall x : Real, real_le (ZWf x) real_one) -> rLPO)
      (rLPO -> lgz_LogZWall) :=
  (lgz_log_z_wall_lpo, lgz_lpo_zle).

(* ============================================================ *)
(* 判定打印                                                         *)
(* ============================================================ *)

Print Assumptions lgz_log_z_wall_lpo.
Print Assumptions lgz_lpo_zle.
Print Assumptions lgz_equivalence.
Print Assumptions lgz_diag_one.
Print Assumptions lgz_diag_no_gap.
