(* ============================================================ *)
(* UpReqLatticeB.v —— B 形格组合面前段（T4a）：strict-lt 新基元 + max 侧 *)
(*   （B 形扩展建造队列 T4 拆分前段席 · §9.4 格特征强扩展）           *)
(*                                                                *)
(* 立项：侦察席「B形扩展建造队列-20260910」目标 4 前段。min 侧与格      *)
(* 组合律留 T4b 后席；本库只做 strict-lt 基元、两连接件、max 侧三件。   *)
(* 上游消费：UpRealLeB3（运输三件 eq_r/plus_nonneg_r/refl，T1 交付，   *)
(* .v/.vo 双证新鲜）+ UpRealLeB（收口器 D 置 one 特化 + 单向桥）+      *)
(* CW219 锚点（real_max_proj@L39803 Q 层点态投影通道、real_max         *)
(* 逐点 Qmax 编码@L39763、real_lt sigT 见证型@L3517、stdlib 泛型格     *)
(* 严格形 Q.max_lub_lt 与 Q.min_dec、Qopp_le_compat、Qlt_minus_iff）。 *)
(*                                                                *)
(* 勘误一则（对侦察单 T4 草图）：逐点 Qmax 上界严格形无需 witness 全     *)
(* 重排——stdlib 泛型格库 Q.max_lub_lt（n<p ⟹ m<p ⟹ max n m<p）       *)
(* 在案可直连，逐点归约后一步闭合；新基元工作量减半，min 对偶           *)
(*（Q.min_glb_lt 同库在案）可由 T4b 同法平移。                         *)
(*                                                                *)
(* 六件清单：1 latb_lt_b 严格序基元（∃δ>0，x ≤_B y−δ；sigT+And 形       *)
(*     沿 real_lt 同构，Set 层零 Prop 出面）/ 2 latb_lt_b_to_le_b      *)
(*     严格形 ⟹ ≤_B 连接件（边界右加成对消去）/ 3 latb_real_lt_to_le_b *)
(*     CW219 严格序 ⟹ ≤_B（Or 左支单步）/ 4 latb_lt_max_intro 严格     *)
(*     上界引入基元（Q 层通道：min 见证 + max_lub_lt 逐点直连）/        *)
(*   5 latb_max_le_b max 上界格主件（a≤_B c ∧ b≤_B c ⟹ max≤_B c；      *)
(*     同一 d 取 c+eps，左支入 Or 后 one 收口器单步）/ 6 latb_max_le_r  *)
(*     吸收律实例（a≤_B b ⟹ max a b ≤_B b）。                          *)
(*                                                                *)
(* 红线自检口径：                                                      *)
(*   —— 语句面全 Set 层：latb_lt_b 为 sigT 见证型（And 分量系           *)
(*      real_lt 既有同构用法），结论全 real_le_b / real_lt；            *)
(*   —— 零 Or 形不可证面越界：不主张 real_le (real_max a b) c 精确形    *)
(*      （判词 2 同源分支选择面），严格面只走 real_lt 见证；             *)
(*   —— 前提位零新增（正性证书全既有件）；全件真证闭合无降级；           *)
(*   —— 提取探针 Obj.magic=0（独立小探针，验后删）；                    *)
(*   —— Print Assumptions 全件 Closed（文末六连打，证据在编译日志）。   *)
(* 编译配方：cpu_guard 包装零裸调（9.0 同轨）：                         *)
(*   coqc -Q . "" -Q "..\001" "" UpReqLatticeB.v                       *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qminmax.
From Stdlib Require Import Arith.PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 一、strict-lt 新基元与 ≤_B 连接件                                   *)
(* ============================================================ *)

(* 件 1：Bishop 严格序基元：x <ᴮ y := ∃δ>0，x ≤_B y+(−δ)。
   sigT+And 形沿 real_lt 同构（CW219 L3517 同款 Set 层封装）；
   边距子句经 real_le_b 表出（零 Prop 出面）。 *)
Definition latb_lt_b (x y : Real) : Set :=
  sigT (fun d : Real => And (real_lt real_zero d)
                            (real_le_b x (real_plus y (real_opp d)))).

(* 件 2：连接件（严格形 ⟹ ≤_B）：x ≤_B y−δ 且 δ>0
   ⟹ x ≤_B (y−δ)+δ == y。右端加正量 δ（nonneg 右加运输件），
   再结合+对消+零元恒等链换形。 *)
Lemma latb_lt_b_to_le_b : forall x y : Real, latb_lt_b x y -> real_le_b x y.
Proof.
  intros x y Hd. destruct Hd as [d [Hdpos Hle]].
  apply (leb3_le_b_eq_r x (real_plus (real_plus y (real_opp d)) d) y).
  - apply (leb3_le_b_plus_nonneg_r x (real_plus y (real_opp d)) d Hle).
    unfold real_le. left. exact Hdpos.
  - assert (Hz : real_eq (real_plus (real_opp d) d) real_zero).
    { apply (real_eq_trans (real_plus (real_opp d) d)
               (real_plus d (real_opp d)) real_zero).
      - apply real_plus_comm.
      - apply real_plus_opp. }
    apply (real_eq_trans (real_plus (real_plus y (real_opp d)) d)
             (real_plus y (real_plus (real_opp d) d)) y).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans (real_plus y (real_plus (real_opp d) d))
               (real_plus y real_zero) y).
      * apply (RealSetoid.real_eq_plus_compat y
                 (real_plus (real_opp d) d) y real_zero).
        -- apply real_eq_refl.
        -- exact Hz.
      * apply real_plus_zero.
Qed.

(* 件 3：连接件（CW219 严格序 ⟹ ≤_B）：real_lt 即 Or 形左支，
   单向桥单步。 *)
Lemma latb_real_lt_to_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y H. apply real_le_to_le_b. unfold real_le. left. exact H.
Qed.

(* ============================================================ *)
(* 二、max 侧组合件（经 real_max_proj Q 层通道）                        *)
(* ============================================================ *)

(* 件 4：严格上界引入基元：a<d 且 b<d ⟹ max a b<d。
   见证 eps 置 Qmin ea eb（正性经 Q.min_dec 分支）、N 置 max Na Nb；
   逐点归约（real_max_proj 通道）后：aₙ<dₙ−Qmin≤dₙ−ea 侧与 bₙ 侧
   分别经 Qopp_le_compat+Qplus_le_compat 换形，Q.max_lub_lt 一步
   闭合 Qmax，末段 Qlt_minus_iff+ring 恒等换形。 *)
Lemma latb_lt_max_intro : forall a b d : Real,
  real_lt a d -> real_lt b d -> real_lt (real_max a b) d.
Proof.
  intros a b d Ha Hb.
  destruct Ha as [ea [Hea [Na HNa]]].
  destruct Hb as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_max_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 严格界对翻：ea<dₙ−aₙ ⟹ aₙ<dₙ−ea（Qlt_minus_iff + ring 恒等） *)
    assert (Q1r : projT1 a n < projT1 d n - ea).
    { apply (proj2 (Qlt_minus_iff (projT1 a n) (projT1 d n - ea))).
      assert (Hj1 : (projT1 d n - ea - projT1 a n ==
                     projT1 d n - projT1 a n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 d n - projT1 a n))).
      exact Q1. }
    assert (Q2r : projT1 b n < projT1 d n - eb).
    { apply (proj2 (Qlt_minus_iff (projT1 b n) (projT1 d n - eb))).
      assert (Hj2 : (projT1 d n - eb - projT1 b n ==
                     projT1 d n - projT1 b n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 d n - projT1 b n))).
      exact Q2. }
    assert (Qa : projT1 a n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - ea) _ Q1r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Ml. }
    assert (Qb : projT1 b n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - eb) _ Q2r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Mr. }
    assert (Hmax : Qmax (projT1 a n) (projT1 b n)
                     < projT1 d n - Qmin ea eb)
      by (apply Q.max_lub_lt; assumption).
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (projT1 d n - Qmax (projT1 a n) (projT1 b n)))).
    assert (Hj : (projT1 d n - Qmax (projT1 a n) (projT1 b n)
                    + - Qmin ea eb ==
                  projT1 d n - Qmin ea eb
                    + - Qmax (projT1 a n) (projT1 b n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmax (projT1 a n) (projT1 b n))
                   (projT1 d n - Qmin ea eb))).
    exact Hmax.
Qed.

(* 件 5（主件）：max 上界格特征：a ≤_B c 且 b ≤_B c ⟹ max a b ≤_B c。
   给 eps>0：两前提同取 d:=c+eps，件 4 一步得 max a b<c+eps（严格），
   Or 左支单步入精确面，one 收口器单步收口——构造性分支选择难题
   （判词 2 同源）在严格见证面不存在，故无需 eps/2 拆分。 *)
Lemma latb_max_le_b : forall a b c : Real,
  real_le_b a c -> real_le_b b c -> real_le_b (real_max a b) c.
Proof.
  intros a b c Ha Hb.
  apply real_le_closure_b_one.
  intros eps Heps. unfold real_le. left.
  apply latb_lt_max_intro.
  - exact (Ha eps Heps).
  - exact (Hb eps Heps).
Qed.

(* 件 6：吸收律实例：a ≤_B b ⟹ max a b ≤_B b（件 5 + ≤_B 自反）。 *)
Lemma latb_max_le_r : forall a b : Real,
  real_le_b a b -> real_le_b (real_max a b) b.
Proof.
  intros a b H. apply (latb_max_le_b a b b H).
  apply leb3_le_b_refl.
Qed.

(* ============================================================ *)
(* 三、假设审计（全件 Closed，证据在编译日志）                           *)
(* ============================================================ *)

Print Assumptions latb_lt_b.
Print Assumptions latb_lt_b_to_le_b.
Print Assumptions latb_real_lt_to_le_b.
Print Assumptions latb_lt_max_intro.
Print Assumptions latb_max_le_b.
Print Assumptions latb_max_le_r.

(* ============================================================ *)
(* 四、min 侧组合件（T4b 后段席追加节）：对偶基元 + 下界格律 + glb 主件 *)
(*                                                                *)
(* 五件清单：7 latb_min_glb 严格下界引入基元（Q 层通道：Qmin 见证 +   *)
(*     Q.min_glb_lt 逐点直连；严格界 e+pₙ<aₙ 平移经 Qle_lt_trans +    *)
(*     Qplus_le_compat；回程余量对翻沿 Qlt_minus_iff 定式）/          *)
(*   8 latb_min_le_b min 下界格主件（c ≤_B a ∧ c ≤_B b ⟹ c ≤_B        *)
(*     min a b；与 max 侧主件不对称——eps 余量挂在 min 外侧，one       *)
(*     收口器单步不可达（max 侧 eps 恰在 latb_lt_max_intro 结论槽     *)
(*     内），走完整逐点证：real_plus_proj 换形 + Qmin 下界平移 +      *)
(*     Q.min_dec 分支收口）/ 9 latb_min_le_l 下界格律左（免费件实    *)
(*     证：real_min_le_l_B @UpRealLeB L396 直连）/ 10 latb_min_le_r  *)
(*     下界格律右（real_min_le_r_B @UpRealLeB L403 直连）/            *)
(*   11 latb_min_le_le trans 组装件（real_le_b_trans @UpRealLeB2     *)
(*     F.2 + 件 9 两步：min a b ≤_B a ≤_B c ⟹ min a b ≤_B c）。       *)
(*                                                                *)
(* 红线沿 T4a 口径：语句面全 Set 层（real_lt sigT 见证形 + real_le_b  *)
(* forall 型，零 Prop 出面）；前提位零新增；全件真证闭合无降级。      *)
(* ============================================================ *)

(* 件 7：严格下界引入基元：p<a 且 p<b ⟹ p<min a b。
   见证 e 置 Qmin ea eb（正性经 Q.min_dec 分支）、N 置 max Na Nb；
   逐点归约（real_min_proj 通道）后：ea<aₙ−pₙ 对翻至 ea+pₙ<aₙ，
   e+pₙ ≤ ea+pₙ 平移（Qle_lt_trans 两步）得 e+pₙ<aₙ 与 e+pₙ<bₙ，
   Q.min_glb_lt 一步闭合 Qmin，末段 Qlt_minus_iff+ring 恒等对翻回
   real_lt 见证形 e<Qmin−pₙ。 *)
Lemma latb_min_glb : forall p a b : Real,
  real_lt p a -> real_lt p b -> real_lt p (real_min a b).
Proof.
  intros p a b Hp Ha.
  destruct Hp as [ea [Hea [Na HNa]]].
  destruct Ha as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_min_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 严格界对翻：ea<aₙ−pₙ ⟹ ea+pₙ<aₙ（Qlt_minus_iff + ring 恒等） *)
    assert (Q1r : ea + projT1 p n < projT1 a n).
    { apply (proj2 (Qlt_minus_iff (ea + projT1 p n) (projT1 a n))).
      assert (Hj1 : (projT1 a n - (ea + projT1 p n) ==
                     projT1 a n - projT1 p n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 a n - projT1 p n))).
      exact Q1. }
    assert (Q2r : eb + projT1 p n < projT1 b n).
    { apply (proj2 (Qlt_minus_iff (eb + projT1 p n) (projT1 b n))).
      assert (Hj2 : (projT1 b n - (eb + projT1 p n) ==
                     projT1 b n - projT1 p n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 b n - projT1 p n))).
      exact Q2. }
    (* 下界平移：e+pₙ ≤ ea+pₙ < aₙ 与 e+pₙ ≤ eb+pₙ < bₙ
       （Qle_lt_trans 中项全显式喂参 + Qplus_le_compat 双前提形） *)
    assert (Qa : Qmin ea eb + projT1 p n < projT1 a n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (ea + projT1 p n) (projT1 a n)).
      - apply Qplus_le_compat.
        + exact Ml.
        + apply Qle_refl.
      - exact Q1r. }
    assert (Qb : Qmin ea eb + projT1 p n < projT1 b n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (eb + projT1 p n) (projT1 b n)).
      - apply Qplus_le_compat.
        + exact Mr.
        + apply Qle_refl.
      - exact Q2r. }
    assert (Hmin : Qmin ea eb + projT1 p n
                     < Qmin (projT1 a n) (projT1 b n))
      by (apply Q.min_glb_lt; assumption).
    (* 对翻回见证形：e<Qmin−pₙ ⟺ 0<Qmin−pₙ−e ⟺ 0<Qmin−(e+pₙ) *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) - projT1 p n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) - projT1 p n
                    - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n)
                    - (Qmin ea eb + projT1 p n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmin ea eb + projT1 p n)
                   (Qmin (projT1 a n) (projT1 b n)))).
    exact Hmin.
Qed.

(* 件 8（主件）：min 下界格特征：c ≤_B a 且 c ≤_B b ⟹ c ≤_B min a b。
   与件 5 不对称处：eps 余量挂在 min 外侧（目标 c<min a b+eps），
   件 7 结论槽无 eps 位，one 收口器单步不可达——走完整逐点证：
   两前提各取同一 eps，real_plus_proj 换形至 aₙ+epsₙ 侧，Qmin 下界
   平移（Qopp_le_compat）后 Q.min_dec 分支收口（分支后目标恰为
   左/右支现成严格界）。 *)
Lemma latb_min_le_b : forall c a b : Real,
  real_le_b c a -> real_le_b c b -> real_le_b c (real_min a b).
Proof.
  intros c a b Hca Hcb.
  unfold real_le_b. intros eps Heps.
  pose proof (Hca eps Heps) as L1.
  pose proof (Hcb eps Heps) as L2.
  destruct L1 as [ea [Hea [Na HNa]]].
  destruct L2 as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj (real_min a b) eps n).
    rewrite (real_min_proj a b n).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    (* 严格界对翻：ea<(a+eps)ₙ−cₙ ⟹ cₙ<(a+eps)ₙ−ea（Qlt_minus_iff+ring） *)
    assert (Q1 : projT1 c n < projT1 a n + projT1 eps n - ea).
    { rewrite <- (real_plus_proj a eps n).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus a eps) n - ea))).
      assert (Hj1 : (projT1 (real_plus a eps) n - ea - projT1 c n ==
                     projT1 (real_plus a eps) n - projT1 c n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea
                (projT1 (real_plus a eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNa n Han). }
    assert (Q2 : projT1 c n < projT1 b n + projT1 eps n - eb).
    { rewrite <- (real_plus_proj b eps n).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus b eps) n - eb))).
      assert (Hj2 : (projT1 (real_plus b eps) n - eb - projT1 c n ==
                     projT1 (real_plus b eps) n - projT1 c n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb
                (projT1 (real_plus b eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNb n Hbn). }
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* 对翻回 cₙ 左位形：e<X−cₙ ⟺ 0<X−cₙ−e ⟺ 0<X−e−cₙ ⟺ cₙ<X−e *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - projT1 c n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - projT1 c n - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - Qmin ea eb - projT1 c n)%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (projT1 c n)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - Qmin ea eb))).
    destruct (Q.min_dec (projT1 a n) (projT1 b n)) as [EM | EM].
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 a n + projT1 eps n - ea) _ Q1).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Ml.
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 b n + projT1 eps n - eb) _ Q2).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Mr.
Qed.

(* 件 9：下界格律左：min a b ≤_B a（免费件——交接注记 D.1 实证在案：
   real_min_le_l_B @UpRealLeB L396，签名 forall a b, real_le_b
   (real_min a b) a，逐字同形直连）。 *)
Lemma latb_min_le_l : forall a b : Real, real_le_b (real_min a b) a.
Proof. intros a b. exact (real_min_le_l_B a b). Qed.

(* 件 10：下界格律右：min a b ≤_B b（免费件——D.2 实证在案：
   real_min_le_r_B @UpRealLeB L403 直连）。 *)
Lemma latb_min_le_r : forall a b : Real, real_le_b (real_min a b) b.
Proof. intros a b. exact (real_min_le_r_B a b). Qed.

(* 件 11：trans 组装件：a ≤_B c ⟹ min a b ≤_B c。
   real_le_b_trans @UpRealLeB2 F.2（签名 forall x y z, real_le_b x y
   -> real_le_b y z -> real_le_b x z，.vo 新鲜实证）+ 件 9 两步组装。 *)
Lemma latb_min_le_le : forall a b c : Real,
  real_le_b a c -> real_le_b (real_min a b) c.
Proof.
  intros a b c H. apply (real_le_b_trans (real_min a b) a c).
  - apply real_min_le_l_B.
  - exact H.
Qed.

(* ============================================================ *)
(* 五、T4b 假设审计（全件 Closed，证据在编译日志）                      *)
(* ============================================================ *)

Print Assumptions latb_min_glb.
Print Assumptions latb_min_le_b.
Print Assumptions latb_min_le_l.
Print Assumptions latb_min_le_r.
Print Assumptions latb_min_le_le.

(* ============================================================ *)
(* 六、与基座严格序的互连（槽放电战役波1 #8：T4 决策项复活）          *)
(*     （T4b 交接注记「节五：latb_lt_b ⟵ real_lt 互连」实装）        *)
(*                                                                *)
(* 目标语句（T4b 交接注记原文）：real_lt x y ⟹ latb_lt_b x y——        *)
(* 把 CW219 基座严格序（real_lt@L3517，Cauchy 追赶型：∃eps>0，∃N，    *)
(* ∀n≥N，eps<yₙ−xₙ）接入 latb_lt_b（∃δ>0，x ≤_B y+(−δ)）。方向单研：  *)
(* 反向（latb_lt_b ⟹ real_lt）不在范围。                            *)
(*                                                                *)
(* 证法（T4b 卡 §七+勘误③路线）：real_lt 见证 (eps,N) 即"最终分离"    *)
(* 窗口；正性 Real δ 置 real_const eps（正性见证 eps·(1/2)，常值序列  *)
(* 窗口 N:=0；正性半量恒等式 eps−eps·(1/2)==eps·(1−1/2) 走 ring      *)
(* 多项式形+闭式 1−1/2==1/2 计算收口——Q 的「/」系 Qdiv 独立算子，    *)
(* ring 视为不可抽象函数符，含变量的除法式须先化乘法形）；主部对任意  *)
(* 正性 e 取其 sigT 首分量 e0 为余量（正性免新造），窗口相交          *)
(* N:=max N N0：分离窗口经 Qlt_minus_iff 对翻 0<yₙ−xₙ+(−eps)，        *)
(* 追赶窗口给 e0<eₙ（real_zero 逐点化简），Qplus_lt_compat 合流       *)
(* 0+e0<(yₙ−xₙ+(−eps))+eₙ，ring 恒等换形回 real_lt 见证槽            *)
(* （real_plus_proj/real_opp_proj/real_const_proj 逐点展开）。       *)
(* ============================================================ *)

Lemma latb_real_lt_interconnect : forall x y : Real,
  real_lt x y -> latb_lt_b x y.
Proof.
  intros x y H.
  destruct H as [eps [Heps0 [N HN]]].
  pose proof (QltT_to_Qlt _ _ Heps0) as HepsQ.
  assert (Hhalf : Qlt 0 (1 / 2)).
  { vm_compute. reflexivity. }
  assert (Hhalf_eps : Qlt 0 (eps * (1 / 2))).
  { assert (Hz2 : (0 * (1 / 2) == 0)%Q) by (unfold Qminus; ring).
    rewrite <- Hz2.
    exact (proj2 (Qmult_lt_r 0 eps (1 / 2) Hhalf) HepsQ). }
  exists (real_const eps). split.
  - (* δ 正性：见证 eps·(1/2)，常值序列窗口 N:=0 *)
    exists (eps * (1 / 2)). split.
    + apply Qlt_to_QltT. exact Hhalf_eps.
    + exists O. intros n Hn.
      apply Qlt_to_QltT.
      rewrite (real_const_proj eps n).
      assert (Hzp : projT1 real_zero n == 0) by reflexivity.
      rewrite Hzp.
      assert (Hj : (eps - 0 == eps)%Q) by (unfold Qminus; ring).
      rewrite Hj.
      apply (proj2 (Qlt_minus_iff (eps * (1 / 2)) eps)).
      assert (Hj2 : (eps + - (eps * (1 / 2)) == eps * (1 - (1 / 2)))%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      assert (Hc : (1 - (1 / 2) == 1 / 2)%Q) by (vm_compute; reflexivity).
      rewrite Hc.
      exact Hhalf_eps.
  - (* 主部：x ≤_B y+(−δ) 逐 eps 收口 *)
    unfold real_le_b. intros e He.
    destruct He as [e0 [He0pos [N0 HN0]]].
    exists e0. split.
    + exact He0pos.
    + exists (Nat.max N N0). intros n Hn.
      apply Qlt_to_QltT.
      rewrite (real_plus_proj (real_plus y (real_opp (real_const eps))) e n).
      rewrite (real_plus_proj y (real_opp (real_const eps)) n).
      rewrite (real_opp_proj (real_const eps) n).
      rewrite (real_const_proj eps n).
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_l.
        - exact (NatLe_drop _ _ Hn). }
      assert (HnN0 : NatLe N0 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_r.
        - exact (NatLe_drop _ _ Hn). }
      assert (Hzn : projT1 real_zero n == 0) by reflexivity.
      pose proof (QltT_to_Qlt _ _ (HN0 n HnN0)) as HB.
      rewrite Hzn in HB.
      assert (Hj3 : (projT1 e n - 0 == projT1 e n)%Q) by (unfold Qminus; ring).
      rewrite Hj3 in HB.
      pose proof (QltT_to_Qlt _ _ (HN n HnN)) as Q1.
      assert (HP : 0 < projT1 y n - projT1 x n + - eps).
      { apply (proj1 (Qlt_minus_iff eps (projT1 y n - projT1 x n))).
        exact Q1. }
      assert (Hfin : 0 + e0 < projT1 y n - projT1 x n + - eps + projT1 e n).
      { apply Qplus_lt_compat.
        - exact HP.
        - exact HB. }
      assert (Hj1 : (0 + e0 == e0)%Q) by (apply Qplus_0_l).
      rewrite Hj1 in Hfin.
      assert (Hj4 : (projT1 y n - projT1 x n + - eps + projT1 e n ==
                     projT1 y n + - eps + projT1 e n - projT1 x n)%Q)
        by (unfold Qminus; ring).
      rewrite Hj4 in Hfin.
      exact Hfin.
Qed.

Print Assumptions latb_real_lt_interconnect.
