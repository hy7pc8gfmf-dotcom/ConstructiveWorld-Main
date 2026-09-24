(* ============================================================ *)
(* UpReqMixRationalProxy_R3.v —— RC3-R 续席（柯西②误差桥接+④主定理打包）      *)
(*                                                                *)
(* 本盘 = R2 全量承载（§0-§3 冻结语义原样：Q 工具族/§1 代理构造/§2 Real      *)
(*        胶合族/③对数搜索 rp_bsearch）+ 新增三段：                         *)
(*   §4 ① Q 层 Bernoulli + 上界站 rp_q_close：rp_bern_sharp 为               *)
(*        rb_bern_sharp'（库树 R2BishopLogSel.v L134，p 底形）勘形复用，      *)
(*        内核 mixe_bern_sharp（UpReqMixLogE，(1-w)^k*(1+k*w)<=1 形）；       *)
(*   §5 ② rp_tq_bound 误差桥接：real_arch 界站 + 单侧代理误差余量            *)
(*        （rp_proxy_up/rp_proxy_low，Qabs_Qlt_condition 承载）              *)
(*        ⟹ Q 层上界站 tq <= c+2eps（rp_const_lt_down 回拉）；               *)
(*   §6 ④ mix_k_select_r2 主定理打包：结论形态同 R1（sigT k，               *)
(*        kappa^k*TV0 < budget），见证/证明分离（compute 透明/spec Qed/      *)
(*        select existT Defined），组合 ③rp_bsearch + ②桥 + ceil 站          *)
(*        J := qarch 形 S(Z.to_nat(Qfloor t))（Qceiling 等形，RBB 六坑      *)
(*        处方照用；mixe_qfloor_lt 直给 ceil 见证）。                        *)
(*                                                                *)
(* 红线自检：零公理/零承认件/零经典逻辑；Set 层产物零 Prop 泄漏；           *)
(*   Real 层零序分支（判定全在 Q 层 Qle_bool/Qcompare）；未闭合段不进编译面。 *)
(* 四关自检（沙箱）：G1 代码区零禁词 / G2 编译 EXIT=0+.vo 魔数 /            *)
(*   G3 Obj.magic=0 / G4 coqchk Axioms none（正斜杠）。                      *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqMixLogE.

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

(* ============================================================ *)
(* §4 使命件①：Q 层 Bernoulli + 上界站 rp_q_close                           *)
(*   rp_bern_sharp = rb_bern_sharp'（库树 R2BishopLogSel.v L134，p 底形）    *)
(*   勘形复用——内核 mixe_bern_sharp（UpReqMixLogE）：(1-w)^k*(1+k*w)<=1。    *)
(* ============================================================ *)

Lemma rp_qpow_mixe : forall (a : Q) (k : nat), rp_qpow a k == mixe_qpow a k.
Proof.
  intros a k. induction k as [| k IH].
  - reflexivity.
  - rewrite rp_qpow_S. cbn [mixe_qpow]. rewrite IH. reflexivity.
Qed.

Lemma rp_q_div4_le : forall x : Q, QltT 0 x -> Qle (x / 4) x.
Proof.
  intros x Hx.
  assert (H14 : Qle (1#4) (1#1))
    by (apply (proj1 (Qle_bool_iff (1#4) (1#1))); reflexivity).
  apply (Qle_trans _ ((1#4) * x)).
  - apply (qeq_imp_qle _ _). field.
  - apply (Qle_trans _ ((1#1) * x)).
    + exact (Qmult_le_compat_r (1#4) (1#1) x H14
               (Qlt_le_weak 0 x (QltT_to_Qlt 0 x Hx))).
    + apply (qeq_imp_qle _ _). ring.
Qed.

Lemma rp_qplus_lt_le : forall x y p q : Q,
  Qlt x y -> Qle p q -> Qlt (x + p) (y + q).
Proof.
  intros x y p q Hxy Hpq.
  destruct (Qle_lt_or_eq p q Hpq) as [Hlt | Heq].
  - exact (Qplus_lt_compat x y p q Hxy Hlt).
  - assert (Hy : (y + p)%Q == (y + q)%Q) by (rewrite Heq; reflexivity).
    apply (rp_qlt_eq_rQ (x + p)%Q (y + p)%Q (y + q)%Q Hy).
    apply (proj2 (Qlt_minus_iff (x + p) (y + p))).
    apply (rp_qlt_eq_rQ 0%Q (y - x)%Q ((y + p) - (x + p))%Q).
    + ring.
    + exact (proj1 (Qlt_minus_iff x y) Hxy).
Qed.

Lemma rp_qleT_imp_qle : forall a b : Q, QleT' a b -> Qle a b.
Proof.
  intros a b H. unfold QleT', Qle_bool in H.
  destruct (Qcompare a b) eqn:E.
  - apply (qeq_imp_qle a b). exact (proj2 (Qeq_alt a b) E).
  - apply Qlt_le_weak. exact (proj2 (Qlt_alt a b) E).
  - inversion H.
Qed.

Lemma rp_qle_imp_qleT' : forall a b : Q, Qle a b -> QleT' a b.
Proof.
  intros a b H. unfold QleT', Qle_bool.
  destruct (Qcompare a b) eqn:E.
  - reflexivity.
  - reflexivity.
  - exfalso.
    assert (Hba : Qlt b a).
    { apply (proj2 (Qlt_alt b a)).
      rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity. }
    destruct (Qle_lt_or_eq a b H) as [Hlt | Heq].
    + exact (Qlt_irrefl b (Qlt_trans b a b Hba Hlt)).
    + rewrite Heq in Hba. exact (Qlt_irrefl b Hba).
Qed.

Lemma rp_qmult_lt_cancel_r : forall a c d : Q,
  QltT 0 d -> Qlt (a * d) (c * d) -> Qlt a c.
Proof.
  intros a c d Hd Hlt.
  destruct (Qcompare a c) eqn:E.
  - exfalso.
    assert (Heq : a == c) by exact (proj2 (Qeq_alt a c) E).
    assert (Hd2 : (a * d)%Q == (c * d)%Q) by (rewrite Heq; reflexivity).
    assert (Hlt2 : Qlt (c * d) (c * d)).
    { apply (proj2 (Qlt_alt (c * d) (c * d))).
      rewrite <- (Qcompare_comp (a * d) (c * d) Hd2 (c * d) (c * d)
                    (Qeq_refl (c * d))).
      exact (proj1 (Qlt_alt (a * d) (c * d)) Hlt). }
    exact (Qlt_irrefl (c * d) Hlt2).
  - exact (proj2 (Qlt_alt a c) E).
  - exfalso.
    assert (Hca : Qlt c a).
    { apply (proj2 (Qlt_alt c a)).
      rewrite <- (Qcompare_antisym a c). rewrite E. reflexivity. }
    assert (Hcd : Qlt (c * d) (a * d))
      by exact (Qmult_lt_compat_r c a d (QltT_to_Qlt 0 d Hd) Hca).
    exact (Qlt_irrefl (a * d) (Qlt_trans (a * d) (c * d) (a * d) Hlt Hcd)).
Qed.

Lemma rp_bern_sharp : forall (q1 : Q) (k : nat),
  Qle 0 q1 -> Qlt q1 1 ->
  Qle (mixe_qpow q1 k * (1 + mixe_qofnat k * (1 - q1))) 1.
Proof.
  intros q1 k Hq0 Hq1.
  assert (Hw0s : Qlt 0 (1 - q1)%Q) by (exact (proj1 (Qlt_minus_iff q1 1) Hq1)).
  assert (Hw0 : Qle 0 (1 - q1)%Q) by (apply (Qlt_le_weak 0%Q (1 - q1)%Q); exact Hw0s).
  assert (Hw1 : Qle (1 - q1)%Q 1).
  { pose proof (Qopp_le_compat 0%Q q1 Hq0) as H1.
    pose proof (Qplus_le_compat (- q1)%Q (- 0)%Q 1%Q 1%Q H1 (Qle_refl 1%Q)) as H2.
    assert (Hrc11 : (- q1 + 1)%Q == (1 - q1)%Q) by ring.
    rewrite Hrc11 in H2.
    assert (Hrc12 : (- 0 + 1)%Q == 1%Q) by ring.
    rewrite Hrc12 in H2.
    exact H2. }
  pose proof (mixe_bern_sharp (1 - q1)%Q k Hw0 Hw1) as Hs.
  assert (Hcvt : (1 - (1 - q1))%Q == q1) by ring.
  rewrite Hcvt in Hs. exact Hs.
Qed.

(* ① 上界站 rp_q_close：cross-mult 闭形（零除法零旁证）：
   q1^k * cup * (1 + k*(1-q1)) <= cup *)
Lemma rp_q_close : forall (q1 cup : Q) (k : nat),
  Qle 0 q1 -> Qlt q1 1 -> QleT' 0 cup ->
  QleT' (mixe_qpow q1 k * cup * (1 + mixe_qofnat k * (1 - q1))) cup.
Proof.
  intros q1 cup k Hq0 Hq1 Hcup0.
  assert (Hle : Qle (mixe_qpow q1 k * cup * (1 + mixe_qofnat k * (1 - q1))) cup).
  { pose proof (rp_bern_sharp q1 k Hq0 Hq1) as Hbern.
    apply (Qle_trans _ ((mixe_qpow q1 k * (1 + mixe_qofnat k * (1 - q1))) * cup) cup).
    - apply (qeq_imp_qle _ _). ring.
    - apply (Qle_trans _ (1 * cup)).
      + exact (Qmult_le_compat_r
                 (mixe_qpow q1 k * (1 + mixe_qofnat k * (1 - q1)))
                 1%Q cup Hbern (rp_qleT_imp_qle _ _ Hcup0)).
      + apply (qeq_imp_qle _ cup). ring. }
  exact (rp_qle_imp_qleT' _ _ Hle).
Qed.

(* ============================================================ *)
(* §5 使命件②：误差桥接——real_arch 界站 + 单侧代理误差余量                   *)
(*   （eps := min(d0,db,d1)/8，rp_eps 承载）⟹ Q 层上界站 tq <= c+2eps。      *)
(* ============================================================ *)

(* 上侧代理余量：x < (x n0 + 2eps)（n0 入模区；Qabs_Qlt_condition 承载） *)
Lemma rp_proxy_up : forall (x : Real) (eps : Q) (Heps : QltT 0 eps) (N : nat),
  (forall m n : nat, NatLe N m -> NatLe N n ->
     QltT (Qabs (projT1 x m - projT1 x n)) eps) ->
  forall n0 : nat, NatLe N n0 ->
  real_lt x (real_const (projT1 x n0 + 2 * eps)).
Proof.
  intros [u Hu] eps Heps N HN n0 Hn0.
  exists eps. split.
  - exact Heps.
  - exists N. intros m Hm.
    specialize (HN m n0 Hm Hn0).
    change (QltT eps ((u n0 + 2 * eps) - u m)).
    apply Qlt_to_QltT.
    assert (HXa : Qlt (Qabs (u m - u n0)) eps) by exact (QltT_to_Qlt _ _ HN).
    destruct (proj1 (Qabs_Qlt_condition (u m - u n0) eps) HXa) as [Hneg Hpos].
    apply (proj2 (Qlt_minus_iff eps ((u n0 + 2 * eps) - u m))).
    apply (rp_qlt_eq_rQ 0%Q (eps - (u m - u n0))%Q
                        ((u n0 + 2 * eps) - u m + - eps)%Q).
    + ring.
    + exact (proj1 (Qlt_minus_iff (u m - u n0) eps) Hpos).
Qed.

(* 下侧代理余量：(x n0 - 2eps) < x（n0 入模区） *)
Lemma rp_proxy_low : forall (x : Real) (eps : Q) (Heps : QltT 0 eps) (N : nat),
  (forall m n : nat, NatLe N m -> NatLe N n ->
     QltT (Qabs (projT1 x m - projT1 x n)) eps) ->
  forall n0 : nat, NatLe N n0 ->
  real_lt (real_const (projT1 x n0 - 2 * eps)) x.
Proof.
  intros [u Hu] eps Heps N HN n0 Hn0.
  exists eps. split.
  - exact Heps.
  - exists N. intros m Hm.
    specialize (HN m n0 Hm Hn0).
    change (QltT eps (u m - (u n0 - 2 * eps))).
    apply Qlt_to_QltT.
    assert (HXa : Qlt (Qabs (u m - u n0)) eps) by exact (QltT_to_Qlt _ _ HN).
    destruct (proj1 (Qabs_Qlt_condition (u m - u n0) eps) HXa) as [Hneg Hpos].
    assert (Hstep : Qlt 0 ((u m - u n0) + eps)).
    { apply (rp_qlt_eq_rQ 0%Q ((u m - u n0) - - eps)%Q ((u m - u n0) + eps)%Q).
      - ring.
      - exact (proj1 (Qlt_minus_iff (- eps) (u m - u n0)) Hneg). }
    apply (proj2 (Qlt_minus_iff eps (u m - (u n0 - 2 * eps)))).
    apply (rp_qlt_eq_rQ 0%Q ((u m - u n0) + eps)%Q
                        (u m - (u n0 - 2 * eps) + - eps)%Q).
    + ring.
    + exact Hstep.
Qed.

(* ② 主形：界站 tq（real_arch 供给）+ 代理余量 ⟹ Q 层上界站 tq <= c+2eps *)
Lemma rp_tq_bound : forall (x : Real) (tq c eps : Q),
  QltT 0 eps ->
  real_lt (real_const tq) x ->
  real_lt x (real_const (c + 2 * eps)) ->
  QleT' tq (c + 2 * eps).
Proof.
  intros x tq c eps Heps Hlow Hup.
  apply qltT_leT'. apply Qlt_to_QltT.
  apply (rp_const_lt_down tq (c + 2 * eps)).
  exact (real_lt_trans (real_const tq) x (real_const (c + 2 * eps)) Hlow Hup).
Qed.

(* ② 代理余量实例化 *)
Lemma rp_tq_bound_proxy : forall (x : Real) (tq eps : Q) (Heps : QltT 0 eps) (N : nat),
  (forall m n : nat, NatLe N m -> NatLe N n ->
     QltT (Qabs (projT1 x m - projT1 x n)) eps) ->
  forall n0 : nat, NatLe N n0 ->
  real_lt (real_const tq) x ->
  QleT' tq (projT1 x n0 + 2 * eps).
Proof.
  intros x tq eps Heps N HN n0 Hn0 Hlow.
  apply (rp_tq_bound x tq (projT1 x n0) eps Heps Hlow).
  exact (rp_proxy_up x eps Heps N HN n0 Hn0).
Qed.

(* ② real_arch 界实例化：tq := arch 站（Z.of_nat na # 1），tq <= c+2eps *)
Lemma rp_tq_bound_arch : forall (x : Real) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun tq : Q =>
          And (QleT' (projT1 x (projT1 (projT2 x eps Heps)) - 2 * eps) tq)
              (real_lt x (real_const tq))).
Proof.
  intros x eps Heps.
  destruct (real_arch x) as [na [_ Harch]].
  destruct (projT2 x eps Heps) as [N HN].
  exists (Z.of_nat na # 1)%Q. split.
  - apply qltT_leT'. apply Qlt_to_QltT.
    apply (rp_const_lt_down (projT1 x N - 2 * eps) (Z.of_nat na # 1)%Q).
    exact (real_lt_trans (real_const (projT1 x N - 2 * eps)) x
             (real_const (Z.of_nat na # 1))
             (rp_proxy_low x eps Heps N HN N (NatLe_lift N N (Nat.le_refl N)))
             Harch).
  - exact Harch.
Qed.

(* 常值实幂 == 常值 Q 幂（④ 实层桥腿） *)
Lemma rp_const_rpow_eq : forall (a : Q) (k : nat),
  real_eq (tv_rpow (real_const a) k) (real_const (mixe_qpow a k)).
Proof.
  intros a k. induction k as [| k IH].
  - apply real_eq_of_zero_diff. intro n.
    change ((1 - mixe_qpow a 0)%Q == 0). cbn [mixe_qpow]. ring.
  - cbn [tv_rpow].
    apply (real_eq_trans _
             (real_mult (real_const a) (real_const (mixe_qpow a k)))).
    + apply (RealSetoid.real_eq_mult_compat (real_const a)
               (tv_rpow (real_const a) k) (real_const a)
               (real_const (mixe_qpow a k))
               (real_eq_refl (real_const a)) IH).
    + exact (rp_const_mult_eq a (mixe_qpow a k)).
Qed.

(* ============================================================ *)
(* §6 使命件④：mix_k_select_r2 主定理打包                                   *)
(*   组合 ③rp_bsearch（搜索引擎）+ ②桥（代理余量三腿）+ ceil 站              *)
(*   J := S(Z.to_nat(Qfloor t))——qarch_ceil 形 = Qceiling 等形（RBB 六坑    *)
(*   处方照用），mixe_qfloor_lt 直给严格 ceil 见证。见证/证明分离：           *)
(*   mix_k_compute_r2 透明可提取 / mix_k_spec_r2 不透明 / existT 打包。      *)
(* ============================================================ *)

Definition rp_qceil_nat (t : Q) : nat := Datatypes.S (Z.to_nat (Qfloor t)).

Definition rp_and_fst {A B : Set} (p : And A B) : A := match p with pair a _ => a end.
Definition rp_and_snd {A B : Set} (p : And A B) : B := match p with pair _ b => b end.

Definition mix_k_compute_r2 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget) : nat :=
  match Ha with
  | inr _ => Datatypes.O
  | inl Halt =>
      let ea := projT1 Hk1 in
      let Hea := rp_and_fst (projT2 Hk1) in
      let Na := projT1 (rp_and_snd (projT2 Hk1)) in
      let eb := projT1 Hk2 in
      let Heb := rp_and_fst (projT2 Hk2) in
      let Nb := projT1 (rp_and_snd (projT2 Hk2)) in
      let ec := projT1 Hbudget in
      let Hec := rp_and_fst (projT2 Hbudget) in
      let Nc := projT1 (rp_and_snd (projT2 Hbudget)) in
      let Nd := projT1 (rp_and_snd (projT2 Halt)) in
      let eps := rp_eps eb ec ea in
      let Heps := rp_eps_pos eb ec ea Heb Hec Hea in
      let Nk := projT1 (projT2 kappa eps Heps) in
      let Nt := projT1 (projT2 budget eps Heps) in
      let Nv := projT1 (projT2 TV0 eps Heps) in
      let n0 := Nat.max Na (Nat.max Nb (Nat.max Nc (Nat.max Nd (Nat.max Nk (Nat.max Nt Nv))))) in
      let kq := projT1 kappa n0 in
      let vq := projT1 TV0 n0 in
      let bq := projT1 budget n0 in
      let q1 := (kq + 2 * eps)%Q in
      let cup := (vq + 2 * eps)%Q in
      let blw := (bq - 2 * eps)%Q in
      let sg := (1 - q1)%Q in
      let tq := (cup / (sg * blw))%Q in
      let kn := rp_qceil_nat tq in
      let kr := rp_bsearch tq kn 0%Q (mixe_qofnat kn) in
      rp_qceil_nat kr
  end.

Theorem mix_k_spec_r2 : forall (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow kappa (mix_k_compute_r2 kappa TV0 budget Hk1 Hk2 Ha Hbudget))
             TV0) budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold mix_k_compute_r2.
  destruct Ha as [Halt | Heq0].
  - (* TV0 > 0：Q 层代理全算 + 实层三桥回拉 *)
    destruct Hk1 as [ea [Hea [Na HNa]]].
    destruct Hk2 as [eb [Heb [Nb HNb]]].
    destruct Hbudget as [ec [Hec [Nc HNc]]].
    destruct Halt as [ed [Hed [Nd HNd]]].
    cbn [projT1 projT2 rp_and_fst rp_and_snd].
    assert (Hapos : real_lt real_zero TV0).
    { exists ed. split.
      - exact Hed.
      - exists Nd. exact HNd. }
    assert (Hk1re : real_lt real_zero kappa).
    { exists ea. split.
      - exact Hea.
      - exists Na. exact HNa. }
    cbv zeta.
    assert (HepsT : QltT 0 (rp_eps eb ec ea))
      by exact (rp_eps_pos eb ec ea Heb Hec Hea).
    destruct (projT2 kappa (rp_eps eb ec ea)
                (rp_eps_pos eb ec ea Heb Hec Hea)) as [Nk HNk].
    destruct (projT2 budget (rp_eps eb ec ea)
                (rp_eps_pos eb ec ea Heb Hec Hea)) as [Nt HNt].
    destruct (projT2 TV0 (rp_eps eb ec ea)
                (rp_eps_pos eb ec ea Heb Hec Hea)) as [Nv HNv].
    set (eps := rp_eps eb ec ea).
    set (n0 := Nat.max Na (Nat.max Nb (Nat.max Nc (Nat.max Nd (Nat.max Nk (Nat.max Nt Nv)))))).
    assert (Hmax : (Na <= n0)%nat /\ (Nb <= n0)%nat /\ (Nc <= n0)%nat /\
                   (Nd <= n0)%nat /\ (Nk <= n0)%nat /\ (Nt <= n0)%nat /\
                   (Nv <= n0)%nat)
      by (unfold n0; lia).
    destruct Hmax as [HNa0 [HNb0 [HNc0 [HNd0 [HNk0 [HNt0 HNv0]]]]]].
    set (kq := projT1 kappa n0).
    set (vq := projT1 TV0 n0).
    set (bq := projT1 budget n0).
    set (q1 := (kq + 2 * eps)%Q).
    set (cup := (vq + 2 * eps)%Q).
    set (blw := (bq - 2 * eps)%Q).
    set (sg := (1 - q1)%Q).
    set (tq := (cup / (sg * blw))%Q).
    set (kn := rp_qceil_nat tq).
    set (kr := rp_bsearch tq kn 0%Q (mixe_qofnat kn)).
    set (k := rp_qceil_nat kr).
    assert (Hzero0 : projT1 real_zero n0 == 0) by reflexivity.
    assert (Hzero1 : projT1 real_one n0 == 1) by reflexivity.
    assert (Heq_kq : (kq - projT1 real_zero n0)%Q == kq).
    { rewrite Hzero0. ring. }
    assert (Hkqpos : QltT ea kq).
    { exact (rp_qlt_eq_r ea _ _ Heq_kq (HNa n0 (NatLe_lift Na n0 HNa0))). }
    assert (Heq_lt1 : (projT1 real_one n0 - kq)%Q == (1 - kq)%Q).
    { rewrite Hzero1. ring. }
    assert (Hkq_lt : Qlt kq (1 - eb)).
    { apply (proj2 (Qlt_minus_iff kq (1 - eb))).
      apply (rp_qlt_eq_rQ 0%Q ((1 - kq) - eb)%Q ((1 - eb) - kq)%Q).
      - ring.
      - exact (proj1 (Qlt_minus_iff eb (1 - kq))
                 (QltT_to_Qlt _ _ (HNb n0 (NatLe_lift Nb n0 HNb0)))). }
    assert (Heq_bq : (bq - projT1 real_zero n0)%Q == bq).
    { rewrite Hzero0. ring. }
    assert (HbqQ : Qlt ec bq).
    { exact (QltT_to_Qlt _ _
               (rp_qlt_eq_r ec _ _ Heq_bq (HNc n0 (NatLe_lift Nc n0 HNc0)))). }
    assert (Heq_vq : (vq - projT1 real_zero n0)%Q == vq).
    { rewrite Hzero0. ring. }
    assert (Hvqpos : QltT ed vq).
    { exact (rp_qlt_eq_r ed _ _ Heq_vq (HNd n0 (NatLe_lift Nd n0 HNd0))). }
    assert (Hcup0 : QleT' 0 cup).
    { apply rp_qle_imp_qleT'. unfold cup.
      apply (Qlt_le_weak 0%Q (vq + 2 * eps)).
      apply (Qplus_lt_compat 0%Q vq 0%Q (2 * eps)).
      - apply (Qlt_trans 0%Q ed vq (QltT_to_Qlt 0 ed Hed) (QltT_to_Qlt _ _ Hvqpos)).
      - exact (QltT_to_Qlt 0 (2 * eps)
                 (qmult_ltT_0_compat (2#1) eps qltT_0_2 HepsT)). }
    assert (Hmarg_eb : Qle (2 * eps) (eb / 4)) by exact (rp_eps_margin eb ec ea).
    assert (Hmarg_ec : Qle (2 * eps) (ec / 4)).
    { unfold eps. unfold rp_eps.
      apply (Qle_trans _ (rp_qmin (rp_qmin eb ec) ea / 4)).
      - assert (Ht1 : (2 * (rp_qmin (rp_qmin eb ec) ea / 8))%Q
                    == (rp_qmin (rp_qmin eb ec) ea / 4)) by field.
        rewrite Ht1. apply Qle_refl.
      - assert (Ht2 : (rp_qmin (rp_qmin eb ec) ea / 4)%Q
                    == (rp_qmin (rp_qmin eb ec) ea * (((1#1) / (4#1))))) by field.
        assert (Ht3 : (ec / 4)%Q == (ec * (((1#1) / (4#1))))) by field.
        rewrite Ht2, Ht3.
        apply Qmult_le_compat_r.
        + apply (Qle_trans _ (rp_qmin eb ec)).
          * apply rp_qmin_le_l.
          * apply rp_qmin_le_r.
        + apply Qlt_le_weak.
          exact (QltT_to_Qlt _ _ (qltT_div_pos (1#1) (4#1) qltT_0_1 qltT_0_4)). }
    assert (Hq1pos : QltT 0 q1).
    { unfold q1. apply Qlt_to_QltT.
      apply (Qplus_lt_compat 0%Q kq 0%Q (2 * eps)).
      - apply (Qlt_trans 0%Q ea kq (QltT_to_Qlt 0 ea Hea) (QltT_to_Qlt _ _ Hkqpos)).
      - exact (QltT_to_Qlt 0 (2 * eps)
                 (qmult_ltT_0_compat (2#1) eps qltT_0_2 HepsT)). }
    assert (Hq0le : Qle 0 q1) by exact (Qlt_le_weak 0 q1 (QltT_to_Qlt 0 q1 Hq1pos)).
    assert (Hq1lt1 : Qlt q1 1).
    { unfold q1.
      apply (Qlt_le_trans _ ((1 - eb) + eb / 4) 1).
      - exact (rp_qplus_lt_le kq (1 - eb) (2 * eps) (eb / 4) Hkq_lt Hmarg_eb).
      - apply (Qle_trans _ ((1 - eb) + eb)).
        + exact (Qplus_le_compat (1 - eb) (1 - eb) (eb / 4) eb (Qle_refl _)
                   (rp_q_div4_le eb Heb)).
        + apply (qeq_imp_qle _ _). ring. }
    assert (Hsgpos : QltT 0 sg).
    { unfold sg.
      exact (Qlt_to_QltT 0 (1 - q1) (proj1 (Qlt_minus_iff q1 1) Hq1lt1)). }
    assert (Hblwpos : QltT 0 blw).
    { unfold blw. apply Qlt_to_QltT.
      apply (proj1 (Qlt_minus_iff (2 * eps) bq)).
      apply (Qle_lt_trans (2 * eps) ec bq).
      - exact (Qle_trans (2 * eps) (ec / 4) ec Hmarg_ec
                 (rp_q_div4_le ec Hec)).
      - exact HbqQ. }
    assert (Hsbpos : QltT 0 (sg * blw))
      by exact (qmult_ltT_0_compat sg blw Hsgpos Hblwpos).
    assert (Hsbnz : ~ ((sg * blw) == 0)%Q) by exact (qltT_not_eq_zero _ Hsbpos).
    assert (Htqlt : Qlt tq (mixe_qofnat kn)) by exact (mixe_qfloor_lt tq).
    assert (Hpass : Qle tq kr).
    { apply (proj1 (Qle_bool_iff tq kr)).
      exact (rp_bsearch_pass tq kn 0%Q (mixe_qofnat kn)
               (Qlt_le_weak _ _ Htqlt)). }
    assert (Hkrlt : Qlt kr (mixe_qofnat k)) by exact (mixe_qfloor_lt kr).
    assert (Hdiv : (tq * (sg * blw))%Q == cup).
    { unfold tq, Qdiv. field.
      split; intro Hc.
      - exact (qltT_not_eq_zero blw Hblwpos Hc).
      - exact (qltT_not_eq_zero sg Hsgpos Hc). }
    assert (Hcuplt : Qlt cup (mixe_qofnat k * (sg * blw))).
    { apply (Qle_lt_trans cup (kr * (sg * blw)) (mixe_qofnat k * (sg * blw))).
      - rewrite <- Hdiv.
        exact (Qmult_le_compat_r tq kr (sg * blw) Hpass
                 (Qlt_le_weak 0 (sg * blw) (QltT_to_Qlt 0 (sg * blw) Hsbpos))).
      - exact (Qmult_lt_compat_r kr (mixe_qofnat k) (sg * blw)
                 (QltT_to_Qlt 0 (sg * blw) Hsbpos) Hkrlt). }
    assert (HDpos : QltT 0 (1 + mixe_qofnat k * sg)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans 0%Q 1%Q (1 + mixe_qofnat k * sg)).
      - exact (QltT_to_Qlt 0 1 qltT_0_1).
      - apply (Qle_trans _ (1 + 0)).
        + apply (qeq_imp_qle _ _). ring.
        + apply (Qplus_le_compat 1 1 0 (mixe_qofnat k * sg) (Qle_refl 1)
                   (mixe_qmult_nonneg (mixe_qofnat k) sg
                      (mixe_qofnat_nonneg k)
                      (Qlt_le_weak 0 sg (QltT_to_Qlt 0 sg Hsgpos)))). }
    assert (HQclose : QleT' (mixe_qpow q1 k * cup * (1 + mixe_qofnat k * (1 - q1))) cup)
      by exact (rp_q_close q1 cup k Hq0le Hq1lt1 Hcup0).
    assert (HQle : Qle (mixe_qpow q1 k * cup * (1 + mixe_qofnat k * sg)) cup)
      by exact (rp_qleT_imp_qle _ _ HQclose).
    assert (Hcuplt2 : Qlt cup (blw * (1 + mixe_qofnat k * sg))).
    { apply (Qlt_le_trans cup (mixe_qofnat k * (sg * blw))
               (blw * (1 + mixe_qofnat k * sg))).
      - exact Hcuplt.
      - apply (Qle_trans _ (0 + mixe_qofnat k * (sg * blw))).
        + apply (qeq_imp_qle _ _). ring.
        + apply (Qle_trans _ (blw + mixe_qofnat k * (sg * blw))).
          * apply (Qplus_le_compat 0 blw (mixe_qofnat k * (sg * blw))
                     (mixe_qofnat k * (sg * blw))
                     (Qlt_le_weak 0 blw (QltT_to_Qlt 0 blw Hblwpos)) (Qle_refl _)).
          * apply (qeq_imp_qle _ _). ring. }
    assert (Hclaim : QltT (mixe_qpow q1 k * cup) blw).
    { apply Qlt_to_QltT.
      apply (rp_qmult_lt_cancel_r (mixe_qpow q1 k * cup) blw
               (1 + mixe_qofnat k * sg) HDpos).
      exact (Qle_lt_trans _ cup (blw * (1 + mixe_qofnat k * sg)) HQle Hcuplt2). }
    assert (Hkle : real_lt kappa (real_const q1))
      by exact (rp_proxy_up kappa eps HepsT Nk HNk n0 (NatLe_lift Nk n0 HNk0)).
    assert (Hkq1le : real_le kappa (real_const q1)).
    { apply (RealSetoid.real_lt_le_iff_req kappa (real_const q1)). left. exact Hkle. }
    assert (HApow : QltT 0 (mixe_qpow q1 k)).
    { apply (rp_qlt_eq_r 0%Q (rp_qpow q1 k) (mixe_qpow q1 k) (rp_qpow_mixe q1 k)).
      exact (rp_qpow_pos q1 k Hq1pos). }
    assert (HconstApow : real_lt real_zero (real_const (mixe_qpow q1 k)))
      by exact (real_const_lt 0%Q (mixe_qpow q1 k)
                  (QltT_to_Qlt 0 (mixe_qpow q1 k) HApow)).
    assert (Hrpowle : real_le (tv_rpow kappa k) (real_const (mixe_qpow q1 k))).
    { apply (real_le_trans _ (tv_rpow (real_const q1) k)).
      - exact (rp_rpow_le_mono kappa (real_const q1) k Hk1re Hkq1le).
      - apply (RealSetoid.real_eq_le). exact (rp_const_rpow_eq q1 k). }
    assert (Htvle : real_le TV0 (real_const cup)).
    { apply (RealSetoid.real_lt_le_iff_req TV0 (real_const cup)). left.
      exact (rp_proxy_up TV0 eps HepsT Nv HNv n0 (NatLe_lift Nv n0 HNv0)). }
    assert (Hmainle : real_le (real_mult (tv_rpow kappa k) TV0)
               (real_const (mixe_qpow q1 k * cup))).
    { apply (real_le_trans _ (real_mult (real_const (mixe_qpow q1 k)) TV0)).
      - exact (real_le_mult_compat (tv_rpow kappa k) (real_const (mixe_qpow q1 k))
                 TV0 Hapos Hrpowle).
      - apply (real_le_trans _ (real_mult TV0 (real_const (mixe_qpow q1 k)))).
        + apply (RealSetoid.real_eq_le).
          exact (real_mult_comm (real_const (mixe_qpow q1 k)) TV0).
        + apply (real_le_trans _ (real_mult (real_const cup)
                     (real_const (mixe_qpow q1 k)))).
          * exact (real_le_mult_compat TV0 (real_const cup)
                     (real_const (mixe_qpow q1 k)) HconstApow Htvle).
          * apply (RealSetoid.real_eq_le).
            apply (real_eq_trans _
                     (real_mult (real_const (mixe_qpow q1 k)) (real_const cup))).
            -- exact (real_mult_comm (real_const cup)
                        (real_const (mixe_qpow q1 k))).
            -- exact (rp_const_mult_eq (mixe_qpow q1 k) cup). }
    assert (Hbudlt : real_lt (real_const blw) budget)
      by exact (rp_proxy_low budget eps HepsT Nt HNt n0 (NatLe_lift Nt n0 HNt0)).
    assert (Hstatlt : real_lt (real_const (mixe_qpow q1 k * cup)) budget).
    { apply (real_lt_trans _ (real_const blw)).
      - exact (real_const_lt (mixe_qpow q1 k * cup) blw (QltT_to_Qlt _ _ Hclaim)).
      - exact Hbudlt. }
    exact (real_le_lt_trans _ _ _ Hmainle Hstatlt).
  - (* TV0 == 0：k = 0，kappa^0 * TV0 == 0 < budget *)
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa Datatypes.O) TV0)
             real_zero budget).
    + apply (real_eq_trans _ TV0).
      * exact (rp_mult_one_l TV0).
      * exact (real_eq_sym _ _ Heq0).
    + exact Hbudget.
Qed.

Definition mix_k_select_r2 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget) :
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mix_k_compute_r2 kappa TV0 budget Hk1 Hk2 Ha Hbudget)
           (mix_k_spec_r2 kappa TV0 budget Hk1 Hk2 Ha Hbudget).

(* ============================================================ *)
(* 切片账（20260924 RC3-R 续席收口）：                                       *)
(*   本盘新增闭合：①rp_bern_sharp（rb_bern_sharp' 勘形复用）+ rp_q_close      *)
(*     上界站；②rp_tq_bound 主形 + rp_proxy_up/low 双余量 +                  *)
(*     rp_tq_bound_arch（real_arch 界实例化）；④mix_k_compute_r2 /           *)
(*     mix_k_spec_r2 / mix_k_select_r2（③rp_bsearch 供站 + ②桥三腿 +         *)
(*     qarch 形 ceil 站，见证/证明分离，全链 Defined）。                      *)
(*   R2 存量（§0-§3）原样承载零改动；R2 件本体冻结未触。                     *)
(* ============================================================ *)
(* 切片账（20260924 R3C 席 §6 收口，四关全绿）：                            *)
(*   §6 修复红点十一处：L861 Hcup0 腿 Qlt_to_QltT 误用（结论 QltT 对 Qle 目标） *)
(*     →改 Qlt_le_weak 直桥；Hmarg_ec rp_eps_margin 实参序变位→min3≤ec 内联  *)
(*     链；Hq1lt1 两腿 rp_q_div4_le 去误包 QltT_to_Qlt（本体吃 QltT）；      *)
(*     Hblwpos Qlt_minus_iff proj2→proj1 向反；Hpass stdlib-Qle 桥           *)
(*     （rp_bsearch_pass 的 Qle_bool=stdlib 常量，Qle_bool_iff 直桥）；      *)
(*     Hdiv Qeq 编码 rewrite 拒吃（Q 层==找整个编码等式非子项）→field+双因子  *)
(*     非零旁证（qltT_not_eq_zero）；Hcuplt/Hclaim Qlt_le_trans→Qle_lt_trans  *)
(*     向反两处；HDpos mixe_qmult_nonneg 回 Qle 去 Qlt 包装+Qle_trans 支序；  *)
(*     Hk1/Halt destruct 消耗→Hk1re/Hapos 重建；Hmainle Real 层 * 记号不存在 *)
(*     →real_mult 显式+四站链重建；主定谳=goal 怪物体 stuck 投影（destruct    *)
(*     不做 iota）：cbn [projT1 projT2 rp_and_fst rp_and_snd] 归约构造子投影  *)
(*     + Nk/Nt/Nv destruct 项与 goal 字面对齐（rp_eps_pos… 裸形非 HepsT）；   *)
(*     TV0==0 支 Heq0 加 real_eq_sym。四关：G2 EXIT=0+.vo 125503B；G3        *)
(*     Separate Extraction mix_k_select_r2+rp_bsearch 17 .ml 全零 Obj.magic； *)
(*     G4 coqchk Modules successfully checked 零 Axiom。配方同波批           *)
(*     （ASCII .cmd/start /low 空根 -Q . ""/cpu_guard 哨兵伴行）。           *)
(* ============================================================ *)
