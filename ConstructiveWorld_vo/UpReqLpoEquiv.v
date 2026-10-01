(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体替换为玩具证          *)
(*   （非平凡三口径：定义层受控展开/显式见证直取/结构性重演），声明面与引用面     *)
(*   零改动、零新增 Require、纯构造性闭合；清单：q_0_lt_1（原 L69，2 句玩具证）。  *)
(* ============================================================ *)
(* UpReqLpoEquiv.v *)
(* 目的： 平方非负全称命题与受限 LPO 的双向归约。 *)
(* 主件： rLPO 与 SqWall 的 lpn_equivalence 双向肢（q_sq_nonneg 全称形为墙面）。 *)
(* 依赖： S01_BaseRing、S02_CauchyComplete。 *)
(* 备注： 零公理、零假设负载；不证墙命题为假，证其与受限 LPO 等价（构造性边界）。 *)
(* ============================================================ *)
(* AA15：平方非负全称 ⟺ 受限 LPO 双向归约定理。公理面：本件零公理、零假设负载——    *)
(*   S02:802 real_square_not_negative 自注「信息性 real_le 的全称形式不可证（需判定  *)
(*   a 的符号）」；本件把该「证不了」升级为机器检验的双向归约：SqWall : Set :=       *)
(*   forall x:Real, real_le real_zero (x·x)——墙的全称数据形（库内 real_le = S01      *)
(*   自定义 Set 层 Or，真数据和，故 SqWall 的 inhabitant 本质上是「逐实数的符号       *)
(*   判定器」，构造性不可供给——这正是墙）；rLPO : Set := forall x:Real,              *)
(*   {|x| 一致正下界间隙} + {∀eps>0, ∃N, ∀n≥N, |x_n| < eps}——受限 LPO：柯西实数       *)
(*   「零问题」决策形；lpn_forward : SqWall -> rLPO（全称正性见证的数据内容给出       *)
(*   逐点判据；非线性支点 |a|≤1 ⟹ a·a ≤ |a| + 无平方根归零桥）；                       *)
(*   lpn_backward : rLPO -> SqWall（决策器两支分别供 real_lt 间隙与 real_eq 逐点      *)
(*   归零见证）；lpn_equivalence : And (SqWall -> rLPO) (rLPO -> SqWall)。注意：本件   *)
(*   不证 SqWall 假，证 SqWall 与 rLPO 等价——「不可证性」以条件定理（若墙则受限      *)
(*   LPO）承载。纪律：纯构造性 Set 层、语句面全 Type/sigT/自定义 And/Or，零 Prop      *)
(*   泄露、零强造；两面均为机器检验的完整证明。实形适配：real_mult 对变量 x 卡        *)
(*   match 处改 real_mult_proj 命题式提供实参；real_eq 实形差序为首元−尾元（S02:387）， *)
(*   minus0 桥取 0−a 形；正向右支供隙改 δ := eps·eps；SUSPEND 之 q_lt_minus0/          *)
(*   q_abs_minus0_le 收敛为 q_eq_le + q_abs_congr 双桥；Part 1 八引理与 lpn_forward    *)
(*   左支逐字续用。                                                                  *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

Local Open Scope Q_scope.

(* ============================================================ *)
(*         以 Qabs_pos + Qabs_opp 符号两支自证）                  *)
(* ============================================================ *)

Lemma q_0_lt_1 : Qlt 0 1.
Proof.
  apply (proj2 (Qlt_alt 0 1)).
  reflexivity.
Qed.

(* 负支：a ≤ 0 ⟹ |a| == −a（经 Qabs (−a) 迁移） *)
Lemma q_abs_neg_eq : forall a : Q, a <= 0 -> Qabs a == - a.
Proof.
  intros a Ha.
  assert (Hpos : 0 <= - a).
  { apply (Qopp_le_compat a 0). exact Ha. }
  rewrite <- (Qabs_opp a).
  apply Qabs_pos.
  exact Hpos.
Qed.

(* |a| ≥ 0 *)
Lemma q_abs_nonneg : forall a : Q, 0 <= Qabs a.
Proof.
  intros a.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    apply Qlt_le_weak.
    exact Hpos.
  - rewrite (q_abs_neg_eq a Hneg).
    apply (Qopp_le_compat a 0).
    exact Hneg.
Qed.

(* a·a ≥ 0（符号两支 + 乘法单调） *)
Lemma q_sq_nonneg : forall a : Q, 0 <= a * a.
Proof.
  intros a.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - assert (H0 : 0 * a <= a * a) by (apply Qmult_le_compat_r; apply Qlt_le_weak; exact Hpos).
    rewrite Qmult_0_l in H0.
    exact H0.
  - assert (Habs : Qabs a == - a) by (apply q_abs_neg_eq; exact Hneg).
    assert (Ha : a * a == (- a) * (- a)) by ring.
    rewrite Ha.
    assert (Hnn : 0 <= - a) by (apply (Qopp_le_compat a 0); exact Hneg).
    assert (H0 : 0 * (- a) <= (- a) * (- a)) by (apply Qmult_le_compat_r; assumption).
    rewrite Qmult_0_l in H0.
    exact H0.
Qed.

(* |a·a| == |a|·|a|（Qabs_square 替身） *)
Lemma qabs_sq : forall a : Q, Qabs (a * a) == Qabs a * Qabs a.
Proof.
  intros a.
  assert (Hnn : 0 <= a * a) by (apply q_sq_nonneg).
  rewrite (Qabs_pos (a * a) Hnn).
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    reflexivity.
  - rewrite (q_abs_neg_eq a Hneg).
    ring.
Qed.

(* 非线性支点：|a| ≤ 1 ⟹ a·a ≤ |a|（1·|a| 桥） *)
Lemma q_sq_le_abs : forall a : Q, Qabs a <= 1 -> a * a <= Qabs a.
Proof.
  intros a Hab.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in Hab.
    assert (H1 : a * a <= 1 * a) by (apply Qmult_le_compat_r; [exact Hab | apply Qlt_le_weak; exact Hpos]).
    rewrite Qmult_1_l in H1.
    exact H1.
  - assert (Habs : Qabs a == - a) by (apply q_abs_neg_eq; exact Hneg).
    rewrite Habs in Hab.
    rewrite Habs.
    assert (Hrepl : (- a) * (- a) == a * a) by ring.
    setoid_rewrite <- Hrepl.
    assert (H1 : (- a) * (- a) <= 1 * (- a)) by (apply Qmult_le_compat_r; [exact Hab | apply (Qopp_le_compat a 0); exact Hneg]).
    rewrite Qmult_1_l in H1.
    exact H1.
Qed.

(* 严格乘法桥：c < |a| ∧ 0 < c ⟹ c·c < a·a（正向供隙用） *)
Lemma q_sq_lt_sq : forall c a : Q, 0 < c -> c < Qabs a -> c * c < a * a.
Proof.
  intros c a Hc0 Hca.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - assert (Habs : Qabs a == a) by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    rewrite Habs in Hca.
    assert (H1 : c * c < a * c) by (apply Qmult_lt_compat_r; assumption).
    assert (H2 : c * a < a * a) by (apply Qmult_lt_compat_r; [exact Hpos | exact Hca]).
    rewrite (Qmult_comm a c) in H1.
    apply Qlt_trans with (c * a); [exact H1 | exact H2].
  - assert (Habs : Qabs a == - a) by (apply q_abs_neg_eq; exact Hneg).
    rewrite Habs in Hca.
    assert (Hrepl : (- a) * (- a) == a * a) by ring.
    setoid_rewrite <- Hrepl.
    assert (H1 : c * c < (- a) * c) by (apply Qmult_lt_compat_r; [exact Hc0 | exact Hca]).
    assert (Hca0 : 0 < (- a)) by (apply Qlt_le_trans with c; [exact Hc0 | apply Qlt_le_weak; exact Hca]).
    assert (H2 : c * (- a) < (- a) * (- a)) by (apply Qmult_lt_compat_r; [exact Hca0 | exact Hca]).
    rewrite (Qmult_comm (- a) c) in H1.
    apply Qlt_trans with (c * (- a)); [exact H1 | exact H2].
Qed.

(* 无平方根归零桥：|a·a| < e·e ∧ 0 < e ⟹ |a| < e（反支 e ≤ |a| 给 e² ≤ |a|² 矛盾） *)
Lemma q_sq_abs_lt : forall a e : Q, 0 < e -> Qabs (a * a) < e * e -> Qabs a < e.
Proof.
  intros a e He0 Hlt.
  destruct (Qlt_le_dec (Qabs a) e) as [Hlt2 | Hge].
  - exact Hlt2.
  - exfalso.
    assert (Hge0 : 0 <= e) by (apply Qlt_le_weak; exact He0).
    assert (H1a : e * e <= Qabs a * e) by (apply (Qmult_le_compat_r e (Qabs a) e); assumption).
    assert (H1b : e * Qabs a <= Qabs a * Qabs a)
      by (apply (Qmult_le_compat_r e (Qabs a) (Qabs a)); [exact Hge | apply q_abs_nonneg]).
    rewrite (Qmult_comm e (Qabs a)) in H1b.
    rewrite <- qabs_sq in H1b.
    apply (Qlt_irrefl (e * e)).
    apply Qle_lt_trans with (Qabs (a * a)).
    + exact (Qle_trans (e * e) (Qabs a * e) (Qabs (a * a)) H1a H1b).
    + exact Hlt.
Qed.

(* ============================================================ *)

(*   故一切换形走「顶面 Qabs 原子」+ 自证同构引理，零实例依赖。     *)
(* ============================================================ *)

(* Qeq 到 Qle 顶面迁移（Qlt_le_dec 两分 + Qlt_irrefl 归谬） *)
Lemma q_eq_le : forall a b : Q, a == b -> a <= b.
Proof.
  intros a b H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    apply (Qlt_irrefl b).
    rewrite H in Hlt.
    exact Hlt.
  - exact Hle.
Qed.

(* Qabs 同构：x == y ⟹ |x| == |y|（检验 _taa15r_probe2 全量真验版） *)
Lemma q_abs_congr : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros x y H.
  destruct (Qlt_le_dec 0 x) as [Hx | Hx].
  - (* 0 < x：迁移 0 ≤ y 后两面 Qabs_pos 完成 *)
    assert (Hxle : 0 <= x) by (apply Qlt_le_weak; exact Hx).
    pose proof Hxle as Hy.
    rewrite H in Hy.
    rewrite (Qabs_pos x Hxle).
    rewrite (Qabs_pos y Hy).
    exact H.
  - (* x ≤ 0：两面 q_abs_neg_eq 后负向同构（Qopp_le_compat×2 + Qle_antisym） *)
    rewrite (q_abs_neg_eq x Hx).
    rewrite H in Hx.
    rewrite (q_abs_neg_eq y Hx).
    apply (Qle_antisym (- x) (- y)).
    + apply (Qopp_le_compat y x).
      apply q_eq_le.
      rewrite H.
      reflexivity.
    + apply (Qopp_le_compat x y).
      apply q_eq_le.
      exact H.
Qed.

(* ============================================================ *)
(* Part 2：两面语句                                              *)
(* ============================================================ *)

(* 墙的全称数据形（S02:802 墙注的对象升级为 Type 面） *)
Definition SqWall : Set :=
  forall x : Real, real_le real_zero (real_mult x x).

(* 受限 LPO：柯西实数零问题决策形（|x| 一致正下界 vs 逐点归零） *)
Definition rLPO : Set :=
  forall x : Real,
    Or
      (sigT (fun c : Q =>
        And (QltT 0 c)
            (sigT (fun N : nat => forall n : nat, NatLe N n ->
              QltT c (Qabs (projT1 x n))))))
      (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT (Qabs (projT1 x n)) eps)).

(* ============================================================ *)
(* Part 3：正向——墙 ⟹ 受限 LPO（见证数据内容给出判据）           *)
(* ============================================================ *)

Theorem lpn_forward : SqWall -> rLPO.
Proof.
  intros Hwall x.
  destruct (Hwall x) as [Hlt | Heq].
  - (* 左支：0 < x·x 带一致间隙 eps ⟹ |x| 有一致正下界 *)
    destruct Hlt as [eps [Heps [N HN]]].
    destruct (Qlt_le_dec 1 eps) as [Hbig | Hsmall].
    + (* eps > 1：取 c := 1；若某点 |x_n| ≤ 1 则 x_n² ≤ |x_n| ≤ 1 < eps 矛盾 *)
      apply inl.
      exists 1. split.
      * apply Qlt_to_QltT.
        exact q_0_lt_1.
      * exists N. intros n Hn.
        specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        (* eps < projT1 (x·x) n = x_n·x_n（投影桥） *)
        assert (Hp : eps < projT1 x n * projT1 x n).
        { assert (Hz : projT1 real_zero n == 0) by reflexivity.
          rewrite Hz in HN.
          assert (Hm : projT1 (real_mult x x) n - 0 == projT1 (real_mult x x) n) by ring.
          rewrite Hm in HN.
          rewrite <- (real_mult_proj x x n).
          exact HN. }
        destruct (Qlt_le_dec 1 (Qabs (projT1 x n))) as [Hbig' | Hsmall'].
        -- exact Hbig'.
        -- exfalso.
           assert (Hle : projT1 x n * projT1 x n <= Qabs (projT1 x n))
             by (apply q_sq_le_abs; exact Hsmall').
           assert (Hlt1 : eps < 1).
           { apply Qlt_le_trans with (projT1 x n * projT1 x n).
             exact Hp.
             exact (Qle_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) 1 Hle Hsmall'). }
           apply (Qlt_irrefl 1).
           apply Qlt_trans with eps; [exact Hbig | exact Hlt1].
    + (* eps ≤ 1：取 c := eps；分 |x_n| ≥ 1 / ≤ 1 两支 *)
      apply inl.
      exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hp : eps < projT1 x n * projT1 x n).
        { assert (Hz : projT1 real_zero n == 0) by reflexivity.
          rewrite Hz in HN.
          assert (Hm : projT1 (real_mult x x) n - 0 == projT1 (real_mult x x) n) by ring.
          rewrite Hm in HN.
          rewrite <- (real_mult_proj x x n).
          exact HN. }
        destruct (Qlt_le_dec 1 (Qabs (projT1 x n))) as [Hbig' | Hsmall'].
        -- (* |x_n| ≥ 1：eps ≤ 1 < |x_n|（Hsmall + Hbig' 直链） *)
           exact (Qle_lt_trans eps 1 (Qabs (projT1 x n)) Hsmall Hbig').
        -- (* |x_n| ≤ 1：eps < x_n·x_n ≤ |x_n|（q_sq_le_abs 支点） *)
           apply Qlt_le_trans with (projT1 x n * projT1 x n).
           ++ exact Hp.
           ++ apply q_sq_le_abs.
              exact Hsmall'.
  - (* 右支：x·x == 0 逐点归零 ⟹ x 逐点归零（无平方根桥）                              *)
    (* AA15R：real_eq 实形差序为首元−尾元（S02:387），逐点项 = Qabs (0 − x_n·x_n)；      *)
    (*   real_mult 对变量卡 match（probe P1 实证），以 real_mult_proj 命题式提供实参         *)
    (*   + q_abs_congr 顶面换形完成；供隙 δ := eps·eps，经 q_sq_abs_lt（e := eps）出。    *)
    apply inr.
    intros eps Heps.
    pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
    assert (Hee : 0 < eps * eps).
    { assert (H0 : 0 * eps < eps * eps) by (apply Qmult_lt_compat_r; assumption).
      rewrite Qmult_0_l in H0.
      exact H0. }
    assert (HeeT : QltT 0 (eps * eps)) by (apply Qlt_to_QltT; exact Hee).
    destruct (Heq (eps * eps) HeeT) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    (* HN : Qabs (projT1 real_zero n − projT1 (real_mult x x) n) < eps·eps *)
    assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                  == 0 - projT1 x n * projT1 x n).
    { rewrite (real_mult_proj x x n).
      assert (Hz : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz.
      reflexivity. }
    rewrite (q_abs_congr _ _ Hdz) in HN.
    assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
    rewrite (q_abs_congr _ _ Hm) in HN.
    rewrite (Qabs_opp (projT1 x n * projT1 x n)) in HN.
    apply (q_sq_abs_lt (projT1 x n) eps HepsQ HN).
Qed.

(* ============================================================ *)
(* Part 4：反向——受限 LPO ⟹ 墙（决策器给出逐点见证）             *)
(* ============================================================ *)

Theorem lpn_backward : rLPO -> SqWall.
Proof.
  intros Hdec x.
  destruct (Hdec x) as [[c [Hc [N HN]]] | Hzr].
  - (* 间隙支 ⟹ real_lt 0 (x·x)：隙常量取 c·c（防 |x_n|<1 收缩） *)
    apply QltT_to_Qlt in Hc.
    apply inl.
    exists (c * c). split.
    + apply Qlt_to_QltT.
      assert (Hcc : 0 * c < c * c) by (apply Qmult_lt_compat_r; assumption).
      rewrite Qmult_0_l in Hcc.
      exact Hcc.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      (* goal : c·c < projT1 (x·x) n − projT1 0 n（real_lt 实形差序） *)
      assert (Hd : projT1 (real_mult x x) n - projT1 real_zero n
                   == projT1 x n * projT1 x n - 0).
      { rewrite (real_mult_proj x x n).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        ring. }
      rewrite Hd.
      assert (Hm : projT1 x n * projT1 x n - 0 == projT1 x n * projT1 x n) by ring.
      rewrite Hm.
      apply q_sq_lt_sq; assumption.
  - (* 归零支 ⟹ real_eq 0 (x·x)：δ 两支（1 < eps 取 1，否则取 eps），             *)
    (*   界内平方支点 q_sq_le_abs（|x_n| ≤ 1 ⟹ x_n² ≤ |x_n|）+ q_abs_congr 顶面链 *)
    apply inr.
    intros eps Heps.
    pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
    destruct (Qlt_le_dec 1 eps) as [Hbig | Hsmall].
    + (* δ := 1：|x_n| < 1 ⟹ x_n·x_n ≤ |x_n| < 1 ≤ eps *)
      assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; exact q_0_lt_1).
      destruct (Hzr 1 H1T) as [N HN].
      exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      (* goal : Qabs (projT1 0 n − projT1 (x·x) n) < eps *)
      assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                    == 0 - projT1 x n * projT1 x n).
      { rewrite (real_mult_proj x x n).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        reflexivity. }
      rewrite (q_abs_congr _ _ Hdz).
      assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
      rewrite (q_abs_congr _ _ Hm).
      rewrite (Qabs_opp (projT1 x n * projT1 x n)).
      assert (Hnn : 0 <= projT1 x n * projT1 x n) by (apply q_sq_nonneg).
      rewrite (Qabs_pos (projT1 x n * projT1 x n) Hnn).
      assert (Hab : Qabs (projT1 x n) <= 1) by (apply Qlt_le_weak; exact HN).
      assert (Hsq : projT1 x n * projT1 x n <= Qabs (projT1 x n))
        by (apply q_sq_le_abs; exact Hab).
      apply (Qle_lt_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) eps Hsq
                          (Qlt_le_trans (Qabs (projT1 x n)) 1 eps HN (Qlt_le_weak 1 eps Hbig))).
    + (* δ := eps：|x_n| < eps ≤ 1，同链 *)
      destruct (Hzr eps Heps) as [N HN].
      exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                    == 0 - projT1 x n * projT1 x n).
      { rewrite (real_mult_proj x x n).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        reflexivity. }
      rewrite (q_abs_congr _ _ Hdz).
      assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
      rewrite (q_abs_congr _ _ Hm).
      rewrite (Qabs_opp (projT1 x n * projT1 x n)).
      assert (Hnn : 0 <= projT1 x n * projT1 x n) by (apply q_sq_nonneg).
      rewrite (Qabs_pos (projT1 x n * projT1 x n) Hnn).
      assert (Hab : Qabs (projT1 x n) <= 1)
        by (apply Qlt_le_weak; apply Qlt_le_trans with eps; [exact HN | exact Hsmall]).
      assert (Hsq : projT1 x n * projT1 x n <= Qabs (projT1 x n))
        by (apply q_sq_le_abs; exact Hab).
      apply (Qle_lt_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) eps Hsq HN).
Qed.

(* ============================================================ *)
(* Part 5：判定件——双向归约                                      *)
(* ============================================================ *)

Definition lpn_equivalence : And (SqWall -> rLPO) (rLPO -> SqWall) :=
  (lpn_forward, lpn_backward).

Print Assumptions lpn_forward.
Print Assumptions lpn_backward.
Print Assumptions lpn_equivalence.

Print Assumptions q_0_lt_1.
