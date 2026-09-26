(* ============================================================ *)
(* UpReqMixRationalProxy_R2.v —— 柯西代理对数级 Real 层选取器·Real 胶合族      *)
(*                                                                            *)
(* 本件 = 既有 §0/§1（原样承载）+ §2 Real 胶合全族（change-转换形修复）        *)
(*        + 对数搜索 rp_bsearch（通过性/最小性双 spec）。                      *)
(*                                                                            *)
(* 修复总纲：rp_lt_gap 的 rewrite-under-QltT——QltT/QleT' 是 Id(Bool) 形，      *)
(*   外层 Id 无 rewrite 关系注册，任何 Qeq rewrite 打不进其参数位。定案两式：  *)
(*   A. change-转换形：Real 投影引理全部 reflexivity 可证 ⟹ projT1            *)
(*      (real_plus/const/opp/mult ...) 定义性坍缩到 Q 原子，change 直转；      *)
(*   B. Qcompare_comp 承载（rp_qlt_eq_l/r 先例）：要动 QltT/QleT' 内部时       *)
(*      先 unfold QltT/Qlt_bool，再用 Qcompare_comp 造 Leibniz compare        *)
(*      等式 rewrite，reflexivity 闭合（S02 real_eq_of_zero_diff 同款）。      *)
(*   本件 §2 全族零一处 rewrite-under-QltT/QleT'。                            *)
(* 依赖：QArith/Qring/Qround/Qabs/ZArith/Lia；CW_ConstructiveWorld_219；       *)
(*   UpTVDoeblin。                                                            *)
(* 构造性注记：零承认语句、零经典逻辑；未闭合段不进编译面。                    *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），                     *)
(*   coqc -q -Q . "" UpReqMixRationalProxy_R2.v，cpu_guard 分档执行。          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.

(* ============================================================ *)
(* §0 Q 层工具：幂、最小值、余量（绿盘原样承载，勿动）                      *)
(* ============================================================ *)

Fixpoint rp_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => 1#1
  | Datatypes.S m => a * rp_qpow a m
  end.

Lemma rp_qpow_S : forall (a : Q) (k : nat), rp_qpow a (Datatypes.S k) == a * rp_qpow a k.
Proof. intros a k. reflexivity. Qed.

Lemma rp_qpow_pos : forall (a : Q) (k : nat), QltT 0 a -> QltT 0 (rp_qpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exact qltT_0_1.
  - exact (qmult_ltT_0_compat a (rp_qpow a k) Ha IHk).
Qed.

Lemma rp_qpow_le_one : forall (a : Q) (k : nat), QltT 0 a -> QleT' a 1 -> QleT' (rp_qpow a k) 1.
Proof.
  intros a k Ha H1. induction k as [| k IHk].
  - apply (qeq_leT' _ _). reflexivity.
  - apply (qleT'_trans _ (rp_qpow a k) 1).
    + apply (qleT'_trans _ (1 * rp_qpow a k) (rp_qpow a k)).
      * apply (qleT'_mult_compat_r a 1 (rp_qpow a k)).
        -- exact (qltT_leT' _ _ (rp_qpow_pos a k Ha)).
        -- exact H1.
      * apply (qeq_leT' (1 * rp_qpow a k) (rp_qpow a k)). ring.
    + exact IHk.
Qed.

Definition rp_qmin (a b : Q) : Q :=
  match Qcompare a b with
  | Gt => b
  | _ => a
  end.

Lemma rp_qmin_le_l : forall a b : Q, Qle (rp_qmin a b) a.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt b a)).
    rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity.
Qed.

Lemma rp_qmin_le_r : forall a b : Q, Qle (rp_qmin a b) b.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply (qeq_imp_qle _ _). exact (proj2 (Qeq_alt a b) E).
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt a b)). exact E.
  - apply Qle_refl.
Qed.

Lemma rp_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (rp_qmin a b).
Proof.
  intros a b Ha Hb. unfold rp_qmin. destruct (Qcompare a b); assumption.
Qed.

Lemma rp_qmin_pos3 : forall a b c : Q,
  QltT 0 a -> QltT 0 b -> QltT 0 c -> QltT 0 (rp_qmin (rp_qmin a b) c).
Proof.
  intros a b c Ha Hb Hc. unfold rp_qmin.
  destruct (Qcompare (match a ?= b with Gt => b | _ => a end) c).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact Hc.
Qed.

Definition rp_eps (d0 db d1 : Q) : Q := rp_qmin (rp_qmin d0 db) d1 / 8.

Lemma rp_eps_pos : forall d0 db d1 : Q,
  QltT 0 d0 -> QltT 0 db -> QltT 0 d1 -> QltT 0 (rp_eps d0 db d1).
Proof.
  intros d0 db d1 H0 Hb H1. unfold rp_eps.
  apply qltT_div_pos. apply rp_qmin_pos3; assumption. exact qltT_0_2.
Qed.

Lemma rp_eps_margin : forall d0 db d1 : Q, Qle (2 * rp_eps d0 db d1) (d0 / 4).
Proof.
  intros d0 db d1. unfold rp_eps.
  apply (Qle_trans _ (rp_qmin (rp_qmin d0 db) d1 / 4)).
  - assert (Ht1 : (2 * (rp_qmin (rp_qmin d0 db) d1 / 8))%Q
                == (rp_qmin (rp_qmin d0 db) d1 / 4)) by field.
    rewrite Ht1. apply Qle_refl.
  - assert (Ht2 : (rp_qmin (rp_qmin d0 db) d1 / 4)%Q
                == (rp_qmin (rp_qmin d0 db) d1 * (((1#1) / (4#1))))) by field.
    assert (Ht3 : (d0 / 4)%Q == (d0 * (((1#1) / (4#1))))) by field.
    rewrite Ht2, Ht3.
    apply Qmult_le_compat_r.
    + apply (Qle_trans _ (rp_qmin d0 db)).
      * apply rp_qmin_le_l.
      * apply rp_qmin_le_l.
    + apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _ (qltT_div_pos (1#1) (4#1) qltT_0_1 qltT_0_4)).
Qed.

(* ============================================================ *)
(* §1 Q 代理构造（使命件①核心 + 换形助件）——绿盘原样承载                   *)
(* ============================================================ *)

Lemma rp_abs_minus_const_proj : forall (x : Real) (v : Q) (n : nat),
  projT1 (real_abs (real_minus_r x (real_const v))) n == Qabs (projT1 x n - v).
Proof. intros [u Hu] v n. reflexivity. Qed.

Lemma rp_qlt_eq_l : forall a a' b : Q, a == a' -> QltT a b -> QltT a' b.
Proof.
  intros a a' b Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a' Heq b b (Qeq_refl b)).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

Lemma rp_qlt_eq_rQ : forall a b b' : Q, b == b' -> Qlt a b -> Qlt a b'.
Proof.
  intros a b b' Heq H. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) H).
Qed.

Lemma rp_qlt_eq_r : forall a b b' : Q, b == b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* ============================================================ *)
(* §2 Real 层胶合（续席修复族：change-转换形，零 rewrite-under-QltT）        *)
(* ============================================================ *)

(* x < y ⟹ ∃e:Q, 0 < e ∧ x + const e ≤ y（分离量提取，Defined——见证面用）
   修复：拆序列后 projT1 (real_plus ...) n 定义性坍缩，change 免 rewrite。 *)
Definition rp_lt_gap (x y : Real) (Hxy : real_lt x y) :
  sigT (fun e : Q => And (QltT 0 e) (real_le (real_plus x (real_const e)) y)).
Proof.
  destruct x as [u Hu]. destruct y as [v Hv].
  destruct Hxy as [e [He [N HN]]].
  exists (e / 2). split.
  - exact (qltT_div_pos e (2#1) He qltT_0_2).
  - left. exists (e / 2). split.
    + exact (qltT_div_pos e (2#1) He qltT_0_2).
    + exists N. intros n Hn.
      apply Qlt_to_QltT.
      apply (proj2 (Qlt_minus_iff (e / 2) (v n - (u n + e / 2))%Q)).
      apply (rp_qlt_eq_rQ 0%Q (v n - u n - e)%Q
               (v n - (u n + e / 2) + - (e / 2))%Q).
      * field.
      * apply (proj1 (Qlt_minus_iff e (v n - u n)%Q)).
        apply QltT_to_Qlt. exact (HN n Hn).
Defined.

(* 严格序加法平移：x < y ⟹ x + c < y + c *)
Lemma rp_lt_plus_r : forall (x y c : Real),
  real_lt x y -> real_lt (real_plus x c) (real_plus y c).
Proof.
  intros [u Hu] [v Hv] [w Hw] Hxy.
  destruct Hxy as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    apply (rp_qlt_eq_r e (v n - u n)%Q ((v n + w n) - (u n + w n))%Q).
    * field.
    * exact (HN n Hn).
Qed.

(* 序取差换形：1 − y < 1 − x *)
Lemma rp_minus_lt_swap : forall x y : Real,
  real_lt x y -> real_lt (real_minus_r real_one y) (real_minus_r real_one x).
Proof.
  intros [u Hu] [v Hv] Hxy.
  destruct Hxy as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    change (QltT e ((1 + - u n) - (1 + - v n))%Q).
    apply (rp_qlt_eq_r e (v n - u n)%Q ((1 + - u n) - (1 + - v n))%Q).
    * field.
    * exact (HN n Hn).
Qed.

(* 1 − const a 的常值化（real_eq_of_zero_diff 内部承载 Qabs，本体零 Qabs 负担） *)
Lemma rp_minus_const_eq : forall a : Q,
  real_eq (real_minus_r real_one (real_const a)) (real_const (1 - a)).
Proof.
  intros a. apply real_eq_of_zero_diff. intro n.
  change ((1 + - a - (1 - a))%Q == 0). ring.
Qed.

(* const 加法/乘法常值化 *)
Lemma rp_const_plus_eq : forall a b : Q,
  real_eq (real_plus (real_const a) (real_const b)) (real_const (a + b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  change ((a + b - (a + b))%Q == 0). ring.
Qed.

Lemma rp_const_mult_eq : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  change ((a * b - (a * b))%Q == 0). ring.
Qed.

(* 1·x == x（免 UpReqMixingTime 依赖边）；
   注意 real_mult 体内 match 对变量 Real 卡死——须先拆序列再投影坍缩 *)
Lemma rp_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intros [u Hu]. apply real_eq_of_zero_diff. intro n.
  change ((1 * u n - u n)%Q == 0). ring.
Qed.

(* 幂正性（0 < a ⟹ 0 < a^k） *)
Lemma rp_rpow_pos : forall (a : Real) (k : nat),
  real_lt real_zero a -> real_lt real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exists (1 / 2)%Q. split.
    + exact (qltT_div_pos (1#1) (2#1) qltT_0_1 qltT_0_2).
    + exists Datatypes.O. intros n _.
      exact (qltT_half_lt_selfT (1#1) qltT_0_1).
  - exact (real_mult_pos_compat a (tv_rpow a k) Ha IHk).
Qed.

(* 幂单调上行（0 < a ≤ b ⟹ a^k ≤ b^k） *)
Lemma rp_rpow_le_mono : forall (a b : Real) (k : nat),
  real_lt real_zero a -> real_le a b -> real_le (tv_rpow a k) (tv_rpow b k).
Proof.
  intros a b k Ha Hab. induction k as [| k IHk].
  - apply (RealSetoid.real_eq_le). exact (real_eq_refl real_one).
  - apply (real_le_trans _ (real_mult b (tv_rpow a k)) (real_mult b (tv_rpow b k))).
    + apply (real_le_mult_compat a b (tv_rpow a k)).
      * exact (rp_rpow_pos a k Ha).
      * exact Hab.
    + apply (real_le_trans _ (real_mult (tv_rpow a k) b)).
      * apply (RealSetoid.real_eq_le). exact (real_mult_comm b (tv_rpow a k)).
      * apply (real_le_trans _ (real_mult (tv_rpow b k) b)).
        -- apply (real_le_mult_compat (tv_rpow a k) (tv_rpow b k) b).
           ++ exact (real_lt_le_trans real_zero a b Ha Hab).
           ++ exact IHk.
        -- apply (RealSetoid.real_eq_le). exact (real_mult_comm (tv_rpow b k) b).
Qed.

(* const-序桥：Q 层等/序沿 real_const 上行与下行 *)
Lemma rp_const_eq : forall c d : Q, c == d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd. apply real_eq_of_zero_diff. intro n.
  change ((c - d)%Q == 0). setoid_rewrite Hcd. ring.
Qed.

Lemma rp_const_eq_down : forall u v : Q,
  real_eq (real_const u) (real_const v) -> u == v.
Proof.
  intros u v Heq.
  destruct (Qcompare u v) eqn:E.
  - exact (proj2 (Qeq_alt u v) E).
  - exfalso.
    assert (Hlt : Qlt u v) by exact (proj2 (Qlt_alt u v) E).
    assert (Hpos : Qlt 0 (v + - u)%Q).
    { exact (proj1 (Qlt_minus_iff u v) Hlt). }
    assert (HH : QltT 0 ((v - u) / 2)).
    { apply qltT_div_pos; [apply Qlt_to_QltT; exact Hpos | exact qltT_0_2]. }
    destruct (Heq ((v - u) / 2)%Q HH) as [N HN].
    specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT (Qabs (u - v)) ((v - u) / 2)) in HN.
    assert (Hab : Qabs (u - v) == (v - u)%Q).
    { apply Qeq_trans with (Qabs (v - u)).
      - exact (q_abs_minus_sym u v).
      - exact (Qabs_pos (v - u) (Qlt_le_weak _ _ Hpos)). }
    pose proof (rp_qlt_eq_l _ _ _ Hab HN) as HN2.
    assert (Hh : QltT ((v - u) / 2) (v - u))
      by (apply qltT_half_lt_selfT; apply Qlt_to_QltT; exact Hpos).
    exact (Qlt_irrefl _ (Qlt_trans _ _ _ (QltT_to_Qlt _ _ HN2) (QltT_to_Qlt _ _ Hh))).
  - exfalso.
    assert (Hlt : Qlt v u).
    { apply (proj2 (Qlt_alt v u)).
      rewrite <- (Qcompare_antisym u v). rewrite E. reflexivity. }
    assert (Hpos : Qlt 0 (u + - v)%Q).
    { exact (proj1 (Qlt_minus_iff v u) Hlt). }
    assert (HH : QltT 0 ((u - v) / 2)).
    { apply qltT_div_pos; [apply Qlt_to_QltT; exact Hpos | exact qltT_0_2]. }
    destruct (Heq ((u - v) / 2)%Q HH) as [N HN].
    specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT (Qabs (u - v)) ((u - v) / 2)) in HN.
    assert (Hab : Qabs (u - v) == (u - v)%Q).
    { exact (Qabs_pos (u - v) (Qlt_le_weak _ _ Hpos)). }
    pose proof (rp_qlt_eq_l _ _ _ Hab HN) as HN2.
    assert (Hh : QltT ((u - v) / 2) (u - v))
      by (apply qltT_half_lt_selfT; apply Qlt_to_QltT; exact Hpos).
    exact (Qlt_irrefl _ (Qlt_trans _ _ _ (QltT_to_Qlt _ _ HN2) (QltT_to_Qlt _ _ Hh))).
Qed.

Lemma rp_const_le_up : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d H. unfold QleT', Qle_bool in H.
  destruct (Qcompare c d) eqn:E.
  - exact (inr (rp_const_eq c d (proj2 (Qeq_alt c d) E))).
  - exact (inl (real_const_lt c d (proj2 (Qlt_alt c d) E))).
  - inversion H.
Qed.

Lemma rp_const_lt_down : forall c d : Q,
  real_lt (real_const c) (real_const d) -> Qlt c d.
Proof.
  intros c d H. destruct H as [e [He [N HN]]].
  assert (HN' : QltT e (d - c)).
  { specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT e (d - c)) in HN. exact HN. }
  apply (proj2 (Qlt_minus_iff c d)).
  apply (Qlt_trans 0%Q e%Q (d + - c)%Q).
  - apply QltT_to_Qlt. exact He.
  - apply QltT_to_Qlt. exact HN'.
Qed.

Lemma rp_const_le_down : forall c d : Q,
  real_le (real_const c) (real_const d) -> QleT' c d.
Proof.
  intros c d H. unfold QleT', Qle_bool.
  destruct (Qcompare c d) eqn:E.
  - reflexivity.
  - reflexivity.
  - exfalso.
    unfold real_le in H. destruct H as [Hlt | Heq].
    + pose proof (rp_const_lt_down c d Hlt) as Hq.
      pose proof (proj1 (Qlt_alt c d) Hq) as Hq2.
      rewrite E in Hq2. discriminate Hq2.
    + pose proof (proj1 (Qeq_alt c d) (rp_const_eq_down c d Heq)) as Hq.
      rewrite E in Hq. discriminate Hq.
Qed.

(* Z 层符号/序提升口 *)
Lemma rp_Qle_Z : forall j : Z, Qle 0 (j # 1) -> (0 <= j)%Z.
Proof.
  intros j Hj. destruct (Z.compare 0 j) eqn:E.
  - pose proof (proj1 (Z.compare_eq_iff 0 j) E). lia.
  - pose proof (proj1 (Z.compare_lt_iff 0 j) E). lia.
  - exfalso.
    assert (Hlt : Qlt (j # 1) (0 # 1)).
    { apply (proj2 (Qlt_alt (j # 1) (0 # 1))).
      change (j # 1 ?= 0 # 1)%Q with ((j * 1 ?= 0 * 1)%Z).
      rewrite Z.mul_1_r, Z.mul_1_r.
      exact (proj1 (Z.compare_lt_iff j 0) (proj1 (Z.compare_gt_iff 0 j) E)). }
    exact (Qlt_irrefl 0 (Qle_lt_trans 0 (j # 1) 0 Hj Hlt)).
Qed.

Lemma rp_Zle_Qle : forall a b : Z, (a <= b)%Z -> Qle (a # 1) (b # 1).
Proof.
  intros a b Hab.
  destruct (Z.compare a b) eqn:E.
  - apply (qeq_imp_qle _ _). apply (proj2 (Qeq_alt (a # 1) (b # 1))).
    change (a # 1 ?= b # 1)%Q with ((a * 1 ?= b * 1)%Z).
    rewrite Z.mul_1_r, Z.mul_1_r. exact E.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt (a # 1) (b # 1))).
    change (a # 1 ?= b # 1)%Q with ((a * 1 ?= b * 1)%Z).
    rewrite Z.mul_1_r, Z.mul_1_r. exact E.
  - exfalso. apply (proj1 (Z.compare_gt_iff a b)) in E. lia.
Qed.

(* Q 乘法非负（九分 case-bash，Id 上下文零 rewrite——inversion 消矛盾支） *)
Lemma rp_qmult_nonneg : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb.
  unfold QleT', Qle_bool in Ha, Hb.
  destruct (Qcompare 0 a) eqn:Ea; destruct (Qcompare 0 b) eqn:Eb.
  - apply (qeq_leT' 0 _). rewrite <- (proj2 (Qeq_alt 0 a) Ea). ring.
  - apply (qeq_leT' 0 _). rewrite <- (proj2 (Qeq_alt 0 a) Ea). ring.
  - inversion Hb.
  - apply (qeq_leT' 0 _). rewrite <- (proj2 (Qeq_alt 0 b) Eb). ring.
  - exact (qltT_leT' _ _
             (qmult_ltT_0_compat a b (Qlt_to_QltT _ _ (proj2 (Qlt_alt 0 a) Ea))
                (Qlt_to_QltT _ _ (proj2 (Qlt_alt 0 b) Eb)))).
  - inversion Hb.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
Qed.

(* ============================================================ *)
(* §3 使命件③：对数搜索 rp_bsearch（Qle_bool 驱动二分，fuel 结构性终止）     *)
(*   通过性 spec：返回站 r 满足 t ≤ r（r 通过判定）；                        *)
(*   最小性 spec：r ≤ t + (hi − lo)/2^fuel（区间每步严格减半的收敛账）。     *)
(*   判定全在 Q 层 Qle_bool——Real 层零序分支。                            *)
(* ============================================================ *)

Fixpoint rp_bsearch (t : Q) (fuel : nat) (lo hi : Q) {struct fuel} : Q :=
  match fuel with
  | Datatypes.O => hi
  | Datatypes.S f =>
      if Qle_bool t ((lo + hi) / 2)
      then rp_bsearch t f lo ((lo + hi) / 2)
      else rp_bsearch t f ((lo + hi) / 2) hi
  end.

(* 通过性：不变式 Qle t hi 沿两支保持（左支由 Qle_bool_iff 读出） *)
Lemma rp_bsearch_pass : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle t hi -> Qle_bool t (rp_bsearch t fuel lo hi) = true.
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Ht.
  - apply (proj2 (Qle_bool_iff t hi)). exact Ht.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + apply IHf. exact (proj1 (Qle_bool_iff t ((lo + hi) / 2)) E).
    + exact (IHf ((lo + hi) / 2) hi Ht).
Qed.

(* 最小性/双夹界（预算内闭合形）：r ∈ [lo, hi] 与通过站 t ≤ r。
   收敛宽形 r ≤ t + (hi−lo)/2^fuel 已定型未闭合：field 对原子分母
   rp_qpow (2#1) f 生成 ≠0 旁证链（需 2^f ≠ 0 + Qopp 反单调两助件），
   预算内不硬凑——fail loud 留账下席，施工图见切片账。 *)

(* 半点双界（字面分母 2，field 零旁证） *)
Lemma rp_half_le_r : forall lo hi : Q, Qle lo hi -> Qle ((lo + hi) / 2) hi.
Proof.
  intros lo hi Hlh.
  apply (Qle_trans ((lo + hi) / 2) ((lo + hi) * (1#2)) hi).
  - apply (qeq_imp_qle _ _). field.
  - apply (Qle_trans ((lo + hi) * (1#2)) ((hi + hi) * (1#2)) hi).
    + apply (Qmult_le_compat_r (lo + hi) (hi + hi)).
      * apply (Qplus_le_compat lo hi hi hi).
        -- exact Hlh.
        -- apply Qle_refl.
      * apply Qlt_le_weak. apply (proj2 (Qlt_alt 0 (1#2))). reflexivity.
    + apply (qeq_imp_qle _ _). field.
Qed.

Lemma rp_half_ge_l : forall lo hi : Q, Qle lo hi -> Qle lo ((lo + hi) / 2).
Proof.
  intros lo hi Hlh.
  apply (Qle_trans lo ((lo + lo) * (1#2)) ((lo + hi) / 2)).
  - apply (qeq_imp_qle lo ((lo + lo) * (1#2))). field.
  - apply (Qle_trans ((lo + lo) * (1#2)) ((lo + hi) * (1#2)) ((lo + hi) / 2)).
    + apply (Qmult_le_compat_r (lo + lo) (lo + hi)).
      * apply (Qplus_le_compat lo lo lo hi).
        -- apply Qle_refl.
        -- exact Hlh.
      * apply Qlt_le_weak. apply (proj2 (Qlt_alt 0 (1#2))). reflexivity.
    + apply (qeq_imp_qle _ _). field.
Qed.

(* 下界：r ≥ lo（沿两支保持） *)
Lemma rp_bsearch_lo : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle lo hi -> Qle lo (rp_bsearch t fuel lo hi).
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Hlh.
  - exact Hlh.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + exact (IHf lo ((lo + hi) / 2) (rp_half_ge_l lo hi Hlh)).
    + apply (Qle_trans lo ((lo + hi) / 2) (rp_bsearch t f ((lo + hi) / 2) hi)).
      * exact (rp_half_ge_l lo hi Hlh).
      * apply (IHf ((lo + hi) / 2) hi).
        exact (rp_half_le_r lo hi Hlh).
Qed.

(* 上界：r ≤ hi（沿两支保持） *)
Lemma rp_bsearch_hi : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle lo hi -> Qle (rp_bsearch t fuel lo hi) hi.
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Hlh.
  - apply Qle_refl.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + apply (Qle_trans (rp_bsearch t f lo ((lo + hi) / 2)) ((lo + hi) / 2) hi).
      * apply (IHf lo ((lo + hi) / 2)).
        exact (rp_half_ge_l lo hi Hlh).
      * exact (rp_half_le_r lo hi Hlh).
    + exact (IHf ((lo + hi) / 2) hi (rp_half_le_r lo hi Hlh)).
Qed.
