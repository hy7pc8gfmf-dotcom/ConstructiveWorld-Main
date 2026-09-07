(* ============================================================ *)
(* UpQKBound.v —— 方案一 QKᵀ 管线收尾：界转化件 + QKᵀ 绑定 +       *)
(*   Δ 显式 sigT 打包（下游消费 UpCS 的 dotp/sql/Q 层核）          *)
(*                                                              *)
(* 数学目标（Real 层，list 向量世界，CW_ConstructiveWorld_219）：   *)
(*   向量 = list Real；维数 d := 向量长度；                       *)
(*   root_of d := projT1 (real_sqrt_exists d Hd)（sqrt 见证：      *)
(*   And (r ≥ 0) (r·r == d)；root 记号只出现在前提与 Δ 定义，      *)
(*   不进恒等链——恒等链全部走 real_eq 迁移 + 逐点尾界）。          *)
(*                                                              *)
(* 件 1（内积/范数桥）inner_sq_norm：                             *)
(*   ⟨q,q⟩ == Σq²（real_eq；UpCS 的 sql 即 Σq²——命名桥）。        *)
(*   根有界前提形态（正确原语，Or 编码下 A² ≤ Q² 推不出 A ≤ Q）：   *)
(*   Hqn : real_le (root_of (sql q) Hqq) Q——件 2/件 3 前提照此。   *)
(*                                                              *)
(* 件 2（界转化·主件）real_logit_bound_of_norm_bounds：            *)
(*   根有界前提（root⟨q,q⟩ ≤ Q、root⟨k,k⟩ ≤ K，Q,K > 0）⟹         *)
(*   real_le |⟨q,k⟩| (Q·K·√d + eps)（eps 版；证明走 inl 严格支）。  *)
(*   装配：C-S 严格版（eps 簿记显式：C-S 的 eps := (h/2)²，经       *)
(*   abs 转化件（abs_le_add_of_sq_lt）转化为 |⟨q,k⟩| < 根积 + h，   *)
(*   再正数乘单调（根积 ≤ Q·K）+ 1 ≤ √d（k=1 时相等、k≥2 时严格    *)
(*   ——k 分支）合并入最终 +eps。                                  *)
(*                                                              *)
(* 件 3（QKᵀ 绑定 + Δ 打包·旗舰）qk_logits_bounded：               *)
(*   attn_logit q k d s s' := dotp(q s, k s')·inv(√d)             *)
(*   （inv 形态：real_inv_pos root_d (root_d_pos d)——正性证书      *)
(*   构造性携带）。前提全 s s' 根有界一致。Δ := (Q·K)·inv(√d)+1，   *)
(*   sigT 打包：Δ > 0 ∧ ∀s s' |logit| ≤ Δ。                        *)
(*   +1 余量代数（eps 透传吸收，零 eps 版）：                      *)
(*     |dotp| < 根积 + 1/2 （件 2 机制，h := 1/2）                 *)
(*     ⟹ |logit| = |dotp|·inv(√d) < (根积 + 1/2)·inv(√d)           *)
(*        = 根积·inv(√d) + (1/2)·inv(√d) ≤ Q·K·inv(√d) + 1/2       *)
(*        （inv(√d) ≤ 1：√d ≥ 1 ⟹ inv 反序）                       *)
(*        < Q·K·inv(√d) + 1 = Δ。+1 精确吸收 (1/2)·inv(√d) ≤ 1/2。  *)
(*                                                              *)
(* 件 4（接缝注记，非定理）：下游接缝——本件 Δ 界供给               *)
(*   bs_minorization 的双界前提（−Δ ≤ z ≤ Δ 由 |z| ≤ Δ 给出）⟹      *)
(*   softmax 核逐点 ≥ δ⋆·U，δ⋆ = e^{−2Δ/T} ⟹ (1−δ⋆)ⁿ 收缩率        *)
(*   （该下游件属 bs_minorization Real 化范围，不在本文件）。        *)
(*                                                              *)
(* 关键构造性事实（设计发现）：                                   *)
(*   real_eq 的柯西语义只约束尾段（∀δ>0 ∃N ∀n≥N |x_n−y_n|<δ），     *)
(*   不给出任何固定下标的逐点相等——故 sqrt 见证 r·r == d 的消费     *)
(*   一律取尾界形式（固定 δ 截断），所有结论为 real_lt（尾段严格    *)
(*   分离），零逐点相等提取、零经典逻辑。                          *)
(*                                                              *)
(* 红线：纯构造性；Set 层语句（Set 层 And/Or/sigT，无 Prop 泄露）；  *)
(*   全 Qed 闭合；可提取零魔法。                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpCS.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.
From Stdlib Require Import Lia Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ################ 第 0 部分：Q 层辅助（可判定序 + 平方桥） ###### *)

Lemma Qle_or_lt : forall x y : Q, {x <= y} + {y < x}.
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - assert (Hxy : x == y) by (apply (proj2 (Qeq_alt x y)); exact E).
    left. rewrite Hxy. apply Qle_refl.
  - left. apply Qlt_le_weak. apply (proj2 (Qlt_alt x y)). exact E.
  - right. apply (proj2 (Qlt_alt y x)).
    rewrite <- (Qcompare_antisym x y). rewrite E. reflexivity.
Qed.

Lemma Qlt_0_half : Qlt 0 (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_half_one : Qlt (1#2) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_le_one : Qle 0 1.
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qle_0_sq_Q : forall x : Q, Qle 0 (x * x).
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)).
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
    + ring.
Qed.

Lemma Qle_0_of_sq_0 : forall a : Q, Qle 0 a -> a * a == 0 -> a == 0.
Proof.
  intros a Ha Hsq.
  destruct (Qeq_dec a 0) as [Heq | Hne]; [exact Heq |].
  exfalso.
  assert (Hlt : 0 < a).
  { destruct (Qle_or_lt a 0) as [Hle | Hgt].
    - exfalso. apply Hne. apply (Qle_antisym a 0); [exact Hle | exact Ha].
    - exact Hgt. }
  assert (H1 : 0 * a < a * a) by (apply (Qmult_lt_compat_r 0 a a); assumption).
  assert (H2 : 0 * a == 0) by ring.
  rewrite H2 in H1. rewrite Hsq in H1.
  exact (Qlt_irrefl 0 H1).
Qed.

(* 平方非负 + 平方界的单调核：0 ≤ a、0 ≤ y、a² ≤ y² ⟹ a ≤ y *)
Lemma QH1core : forall a y : Q,
  Qle 0 a -> Qle 0 y -> Qle (a * a) (y * y) -> Qle a y.
Proof.
  intros a y Ha Hy Hsq.
  destruct (Qle_or_lt a y) as [Hle | Hlt]; [exact Hle |].
  exfalso.
  destruct (Qeq_dec y 0) as [Hy0 | Hny0].
  - rewrite Hy0 in Hsq.
    assert (Haa : a * a == 0).
    { apply (Qle_antisym (a * a) 0).
      - simpl in Hsq. exact Hsq.
      - apply (Qle_0_sq_Q a). }
    assert (Ha0 : a == 0) by (apply (Qle_0_of_sq_0 a Ha Haa)).
    rewrite Hy0, Ha0 in Hlt. exact (Qlt_irrefl 0 Hlt).
  - assert (Hpy : 0 < y).
    { destruct (Qle_or_lt y 0) as [Hle | Hgt].
      - exfalso. apply Hny0. apply (Qle_antisym y 0); [exact Hle | exact Hy].
      - exact Hgt. }
    assert (Hpa : 0 < a) by (apply (Qlt_trans 0 y a Hpy Hlt)).
    assert (H1 : y * y < a * y) by (apply (Qmult_lt_compat_r y a y); assumption).
    assert (H2 : a * y < a * a).
    { setoid_replace (a * y) with (y * a) by ring.
      apply (Qmult_lt_compat_r y a a); assumption. }
    assert (H3 : y * y < a * a) by (apply (Qlt_trans (y * y) (a * y) (a * a) H1 H2)).
    exact (Qlt_irrefl (y * y) (Qlt_le_trans (y * y) (a * a) (y * y) H3 Hsq)).
Qed.

(* 严格版：0 ≤ d、0 < h、d² < h² ⟹ d < h *)
Lemma Qlt_of_sq_lt : forall d h : Q,
  Qle 0 d -> Qle 0 h -> Qlt (d * d) (h * h) -> Qlt d h.
Proof.
  intros d h Hd Hh Hlt.
  destruct (Qle_or_lt h d) as [Hle | Hlt'].
  - exfalso.
    assert (Hmono : h * h <= d * d).
    { apply (Qle_trans (h * h) (d * h) (d * d)).
      - apply (Qmult_le_compat_r h d h); [exact Hle | exact Hh].
      - setoid_replace (d * h) with (h * d) by ring.
        apply (Qmult_le_compat_r h d d); [exact Hle | exact Hd]. }
    exact (Qlt_irrefl (d * d) (Qlt_le_trans (d * d) (h * h) (d * d) Hlt Hmono)).
  - exact Hlt'.
Qed.

(* 绝对值版：0 ≤ y、x² ≤ y² ⟹ |x| ≤ y *)
Lemma Qle_abs_le_sq : forall x y : Q,
  Qle 0 y -> Qle (x * x) (y * y) -> Qle (Qabs x) y.
Proof.
  intros x y Hy Hsq.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos x Hpos).
    apply (QH1core x y); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
    rewrite Habsx.
    apply (QH1core (- x) y).
    + exact (Qopp_le_compat x 0 Hle).
    + exact Hy.
    + setoid_replace ((- x) * (- x)) with (x * x) by ring. exact Hsq.
Qed.

(* 平方相等 + 双非负 ⟹ 相等 *)
Lemma Qeq_of_sq_eq : forall a b : Q,
  Qle 0 a -> Qle 0 b -> a * a == b * b -> a == b.
Proof.
  intros a b Ha Hb Hsq.
  apply (Qle_antisym a b).
  - apply (QH1core a b); [exact Ha | exact Hb | apply qeq_le; exact Hsq].
  - apply (QH1core b a); [exact Hb | exact Ha | apply qeq_le; rewrite Hsq; reflexivity].
Qed.

(* |x·x| == |x|² *)
Lemma Qabs_sq : forall x : Q, Qabs (x * x) == Qabs x * Qabs x.
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos (x * x)).
    + rewrite (Qabs_pos x Hpos). reflexivity.
    + apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)) by ring.
    rewrite (Qabs_pos ((- x) * (- x))).
    + assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
      rewrite Habsx. reflexivity.
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
Qed.

(* x² == |x|·|x| *)
Lemma Qsq_abs_eq : forall x : Q, x * x == Qabs x * Qabs x.
Proof.
  intro x. rewrite <- (Qabs_sq x).
  apply Qeq_sym. apply Qabs_pos. apply Qle_0_sq_Q.
Qed.

(* 绝对值乘法性：|a·b| == |a|·|b| *)
Lemma Qabs_mult_gen : forall a b : Q, Qabs (a * b) == Qabs a * Qabs b.
Proof.
  intros a b.
  apply (Qeq_of_sq_eq (Qabs (a * b)) (Qabs a * Qabs b)).
  - apply Qabs_nonneg.
  - apply (Qmult_le_0_compat (Qabs a) (Qabs b)); apply Qabs_nonneg.
  - setoid_replace (Qabs a * Qabs b * (Qabs a * Qabs b))
      with (Qabs a * Qabs a * (Qabs b * Qabs b)) by ring.
    rewrite <- (Qabs_sq a). rewrite <- (Qabs_sq b).
    rewrite (Qabs_pos (a * a) (Qle_0_sq_Q a)).
    rewrite (Qabs_pos (b * b) (Qle_0_sq_Q b)).
    rewrite <- (Qabs_sq (a * b)).
    rewrite (Qabs_pos ((a * b) * (a * b)) (Qle_0_sq_Q (a * b))).
    ring.
Qed.

(* 双非负单调乘 *)
Lemma Qmult_le_mono2 : forall a b c d : Q,
  Qle 0 a -> Qle 0 b -> Qle a c -> Qle b d -> Qle (a * b) (c * d).
Proof.
  intros a b c d Ha Hb Hac Hbd.
  assert (Hc0 : 0 <= c) by (apply (Qle_trans 0 a c); assumption).
  apply (Qle_trans (a * b) (c * b) (c * d)).
  - apply (Qmult_le_compat_r a c b); assumption.
  - setoid_replace (c * b) with (b * c) by ring.
    setoid_replace (c * d) with (d * c) by ring.
    apply (Qmult_le_compat_r b d c); [exact Hbd | exact Hc0].
Qed.

(* 1 ≤ x² + 0 ≤ x ⟹ 1 ≤ x（√d ≥ 1 的逐点内核） *)
Lemma Qle_1_of_sq : forall x : Q, Qle 0 x -> Qle 1 (x * x) -> Qle 1 x.
Proof.
  intros x H0 Hsq.
  assert (H : Qle (1 * 1) (x * x)).
  { setoid_replace (1 * 1) with 1 by ring. exact Hsq. }
  apply (QH1core 1 x); [exact zero_le_one | exact H0 | exact H].
Qed.

(* UpCS 的 sqlQ/dotpQ 命名桥：dotpQ u u == sqlQ u *)
Lemma dotpQ_sqlQ : forall u : list Q, dotpQ u u == sqlQ u.
Proof.
  induction u as [| x xs IH].
  - reflexivity.
  - cbn [dotpQ sqlQ]. rewrite IH. ring.
Qed.

(* ################ 第 2 部分：向量世界 + Real 尾段消费件 ########## *)
(* 本文件自带 dotp/sql（CW219 Real 版；UpCS 的同名件锚定扫描版     *)
(* Real，不可跨用；UpCS 的纯 Q 层 cs_Q/dotpQ/sqlQ 照常消费）。      *)

Fixpoint dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (dotp xs ys)
  | _, _ => real_zero
  end.

Fixpoint sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (sql rest)
  end.

(* ---- Q 层补充 ---- *)

Lemma Qlt_0_two : Qlt 0 2.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_eight : Qlt 0 8.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_one : Qlt 0 1.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_sixteen : Qlt 0 16.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_32 : Qlt 0 32.
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_0_three_quarters : Qle 0 (3#4).
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qlt_0_7_16 : Qlt 0 (7#16).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_quarter : Qlt 0 (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_add_pos_r : forall a e : Q, Qle 0 e -> Qle a (a + e).
Proof.
  intros a e He.
  apply (Qle_trans a (a + 0) (a + e)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat a a 0 e); [apply Qle_refl | exact He].
Qed.

Lemma Qabs_lt_l : forall x c : Q, Qlt (Qabs x) c -> Qlt x c.
Proof.
  intros x c H.
  destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0) in H. exact H.
  - apply (Qlt_trans x 0 c H0).
    apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H).
Qed.

Lemma Qabs_lt_low : forall x c : Q, Qlt (Qabs x) c -> Qlt (- c) x.
Proof.
  intros x c H.
  destruct (Qle_or_lt x (- c)) as [Hle | Hgt].
  - exfalso.
    assert (Hc0 : 0 < c) by (apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H)).
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; lra).
    rewrite Habs in H.
    assert (Hge0 : - (- c) <= - x) by exact (Qopp_le_compat x (- c) Hle).
    assert (Hcc : c == - (- c)) by ring.
    rewrite Hcc in Hge0.
    lra.
  - exact Hgt.
Qed.

(* ---- real_le 尾段消费（eq 支带 eps 松弛；lt 支精确） ---- *)

Lemma real_lt_pt_le : forall x y : Real,
  real_lt x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n)).
Proof.
  intros x y H. destruct H as [e [Hp [N HN]]].
  exists N. intros n Hn.
  assert (Hp0 : Qlt 0 e) by (apply QltT_to_Qlt; exact Hp).
  assert (Hq : Qlt e (projT1 y n - projT1 x n)).
  { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
  lra.
Qed.

Lemma real_le_pt_ev_plus : forall (x y : Real) (e : Q),
  Qlt 0 e -> real_le x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n + e)).
Proof.
  intros x y e He H. destruct H as [Hlt | Heq].
  - destruct (real_lt_pt_le x y Hlt) as [N HN]. exists N. intros n Hn.
    apply (Qle_trans (projT1 x n) (projT1 y n) (projT1 y n + e));
      [exact (HN n Hn) | apply Qle_add_pos_r; apply Qlt_le_weak; exact He].
  - destruct (Heq e (Qlt_to_QltT 0 e He)) as [N HN].
    exists N. intros n Hn.
    assert (Hab : Qlt (Qabs (projT1 x n - projT1 y n)) e).
    { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
    assert (Hl := Qabs_lt_l _ _ Hab).
    lra.
Qed.

(* ---- real_const 桥 ---- *)

Lemma real_const_pos : forall c : Q, Qlt 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  exists ((1#2) * c). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1#2) c); [exact Qlt_0_half | exact Hc].
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite real_const_proj.
    setoid_replace (c - 0) with c by ring.
    lra.
Qed.

Lemma real_const_eq_of_Qeq : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n.
  rewrite !real_const_proj. rewrite H. ring.
Qed.

Lemma real_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. apply real_eq_of_zero_diff. intro n.
  rewrite ?real_plus_proj. rewrite ?real_mult_proj.
  rewrite ?real_plus_proj. rewrite ?real_mult_proj.
  ring.
Qed.

(* ################ 第 3 部分：nat 嵌入 + 构造性平方根绑定 ######## *)

(* Q 侧自然数常数（避免 Q.of_nat/Z 换算） *)
Fixpoint natQ (k : nat) : Q :=
  match k with
  | 0%nat => 0%Q
  | Datatypes.S m => 1 + natQ m
  end.

Lemma natQ_pos : forall k : nat, Qle 0 (natQ k).
Proof.
  induction k as [| k IH].
  - apply Qle_refl.
  - cbn [natQ]. apply (Qle_trans 0 (0 + natQ k) (1 + natQ k)).
    + rewrite Qplus_0_l. exact IH.
    + apply (Qplus_le_compat 0 1 (natQ k) (natQ k));
        [exact zero_le_one | apply Qle_refl].
Qed.

Lemma natQ_Sk_ge_one : forall k : nat, Qle 1 (natQ (Datatypes.S k)).
Proof.
  intro k. cbn [natQ].
  apply (Qle_trans 1 (1%Q + 0%Q) (1%Q + natQ k)).
  - apply qeq_le. ring.
  - setoid_replace (1%Q + 0%Q) with (0%Q + 1%Q) by ring.
    setoid_replace (1%Q + natQ k) with (natQ k + 1%Q) by ring.
    apply (Qplus_le_compat 0 (natQ k) 1 1); [apply natQ_pos | apply Qle_refl].
Qed.

(* Real 侧嵌入 *)
Fixpoint nat_to_R (k : nat) : Real :=
  match k with
  | 0%nat => real_zero
  | Datatypes.S m => real_plus real_one (nat_to_R m)
  end.

Lemma nat_to_R_proj : forall (k : nat) (n : nat),
  projT1 (nat_to_R k) n == natQ k.
Proof.
  induction k as [| k IH]; intro n.
  - reflexivity.
  - cbn [nat_to_R]. rewrite real_plus_proj.
    change (projT1 real_one n) with 1%Q.
    rewrite IH. reflexivity.
Qed.

Lemma nat_to_R_pos : forall k : nat, real_lt real_zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k.
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite (nat_to_R_proj (Datatypes.S k) n).
    cbn [natQ].
    setoid_replace (1 + natQ k - 0) with (1%Q + natQ k) by ring.
    assert (H1 : Qle 0 (natQ k)) by apply natQ_pos.
    lra.
Qed.

(* 平方根的界转化原语：root_of 只出现在前提与 Δ 定义，不进恒等链 *)
Definition root_of (d : Real) (Hd : real_le real_zero d) : Real :=
  projT1 (real_sqrt_exists d Hd).

Definition root_d (k : nat) : Real :=
  root_of (nat_to_R (Datatypes.S k)) (inl (nat_to_R_pos k)).

Lemma root_d_sq : forall k : nat,
  real_eq (real_mult (root_d k) (root_d k)) (nat_to_R (Datatypes.S k)).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (nat_to_R (Datatypes.S k)) (inl (nat_to_R_pos k)))
    as [r [Hr0 Hrsq]].
  exact Hrsq.
Qed.

(* sqrt 见证的尾下界：r² == natQ(S k)（尾段）+ S k ≥ 1 ⟹ r_n² > 9/16（尾段） *)
Lemma sq_bound_from_eq : forall (k : nat) (r : Real),
  real_eq (real_mult r r) (nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (9#16) (projT1 r n * projT1 r n)).
Proof.
  intros k r Hrsq. destruct r as [u Hu].
  destruct (Hrsq (7#16) (Qlt_to_QltT 0 (7#16) Qlt_0_7_16)) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1 |- *.
  assert (Hlow2 : Qlt (- (7#16)) (u n * u n - natQ (Datatypes.S k))).
  { assert (Ht := HN1 n (NatLe_lift N1 n Hn)).
    apply QltT_to_Qlt in Ht.
    assert (Hlow := Qabs_lt_low _ _ Ht).
    rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
    exact Hlow. }
  assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
  remember (u n * u n) as t eqn:Et.
  remember (natQ (Datatypes.S k)) as q eqn:Eq.
  lra.
Qed.

(* 根的下界：S k ≥ 1 ⟹ 根 ≥ 3/4（尾段） *)
Lemma sqrt_dim_ge_quarter : forall (k : nat) (r : Real),
  real_le real_zero r ->
  real_eq (real_mult r r) (nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (3#4) (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq. destruct r as [u Hu].
  destruct (sq_bound_from_eq k (existT (fun s : Qseq => cauchy s) u Hu) Hrsq)
    as [N1 HN1].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat).
    { apply (Nat.le_trans N0 (Nat.max N0 N1) n); [apply Nat.le_max_l | exact Hn]. }
    assert (Hn1 : (N1 <= n)%nat).
    { apply (Nat.le_trans N1 (Nat.max N0 N1) n); [apply Nat.le_max_r | exact Hn]. }
    assert (Hge : Qle 0 (u n)).
    { assert (Hpos : Qlt 0 e0) by (apply QltT_to_Qlt; exact Hpos0).
      assert (Hq : Qlt e0 (u n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    apply (QH1core (3#4) (u n)).
    + exact Qle_0_three_quarters.
    + exact Hge.
    + setoid_replace ((3#4) * (3#4)) with (9#16) by ring.
      apply Qlt_le_weak. exact (HN1 n Hn1).
  - exfalso.
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (Hn1 : (N1 <= Nat.max N1 N2)%nat) by apply Nat.le_max_l.
    assert (Hn2 : (N2 <= Nat.max N1 N2)%nat) by apply Nat.le_max_r.
    assert (H9 : Qlt (9#16) (u (Nat.max N1 N2) * u (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) Hn1).
    assert (Hsmall0 := HN2 (Nat.max N1 N2) (NatLe_lift N2 (Nat.max N1 N2) Hn2)).
    apply QltT_to_Qlt in Hsmall0.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hsmall0.
    setoid_replace (0 - u (Nat.max N1 N2))
      with (- u (Nat.max N1 N2)) in Hsmall0 by ring.
    rewrite Qabs_opp in Hsmall0.
    assert (Hsq : u (Nat.max N1 N2) * u (Nat.max N1 N2)
                  == Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos (u (Nat.max N1 N2) * u (Nat.max N1 N2))
                    (Qle_0_sq_Q (u (Nat.max N1 N2)))). apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hq4 : (1#4) * (1#4) == (1#16)) by ring.
    assert (Hqabs0 : Qle 0 (Qabs (u (Nat.max N1 N2)))) by apply Qabs_nonneg.
    assert (Hstep : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#4) * (1#4)).
    { assert (Hq4p : Qlt 0 ((1#4) * (1#4))).
      { apply (Qmult_lt_0_compat (1#4) (1#4)); exact Qlt_0_quarter. }
      nra. }
    assert (Hmono : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#16)).
    { rewrite <- Hq4. exact Hstep. }
    assert (Hg : Qlt (1#16) (9#16)) by (vm_compute; reflexivity).
    lra.
Qed.

Lemma root_zero_of : forall (d : Real) (Hd : real_le real_zero d),
  real_le real_zero (root_of d Hd).
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_sq_of : forall (d : Real) (Hd : real_le real_zero d),
  real_eq (real_mult (root_of d Hd) (root_of d Hd)) d.
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hrsq.
Qed.

Lemma root_d_ge_zero : forall k : nat, real_le real_zero (root_d k).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (nat_to_R (Datatypes.S k)) (inl (nat_to_R_pos k)))
    as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_d_pos : forall k : nat, real_lt real_zero (root_d k).
Proof.
  intro k.
  unfold root_d, root_of.
  destruct (real_sqrt_exists (nat_to_R (Datatypes.S k)) (inl (nat_to_R_pos k)))
    as [r [Hr0 Hrdsq]].
  destruct (sqrt_dim_ge_quarter k r Hr0 Hrdsq) as [N HN].
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    setoid_replace (projT1 r n - 0) with (projT1 r n) by ring.
    apply (Qlt_le_trans (1#2) (3#4) (projT1 r n));
      [exact Qlt_half_one | exact (HN n Hn)].
Qed.

(* real_inv_pos 的逐点形式（Defined 体展开 + leb 分支） *)
Lemma real_inv_pos_pt :
  forall (u : Qseq) (Hu : cauchy u) (eps0 : Q) (Heps0 : QltT 0 eps0)
         (N0 : nat) (HN0 : forall n : nat, NatLe N0 n -> QltT eps0 (u n - projT1 real_zero n))
         (n : nat), (N0 <= n)%nat ->
  projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) u Hu)
             (existT _ eps0 (Heps0, existT _ N0 HN0))) n == Qinv (u n).
Proof.
  intros u Hu eps0 Heps0 N0 HN0 n Hn.
  unfold real_inv_pos. cbn [projT1].
  destruct (Nat.leb N0 n) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hlt : (n < N0)%nat) by (apply (proj1 (Nat.leb_gt N0 n) E)).
    exact (Nat.lt_irrefl n (Nat.lt_le_trans n N0 n Hlt Hn)).
Qed.

(* ################ 第 4 部分：abs 界转化件（B'）与 eps 透传 ######## *)

(* 核心 abs 转化件：x² < y² + h² ⟹ |x| < |y| + 2h（无符号前提，Qabs 形式） *)
Lemma abs_le_add_abs_of_sq_lt : forall (x y : Real) (h : Q),
  Qlt 0 h ->
  real_lt (real_mult x x) (real_plus (real_mult y y) (real_const (h * h))) ->
  real_lt (real_abs x) (real_plus (real_abs y) (real_const (2 * h))).
Proof.
  intros x y h Hh Hlt. destruct Hlt as [e1 [Hpos1 [N1 HN1]]].
  exists h. split.
  - apply Qlt_to_QltT. exact Hh.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
  rewrite real_plus_proj. rewrite real_const_proj.
  rewrite !real_abs_proj.
  assert (Hpt : Qlt e1 (projT1 y n * projT1 y n + h * h - projT1 x n * projT1 x n)).
  { pose proof (HN1 n Hn) as Hp.
    apply QltT_to_Qlt in Hp.
    rewrite real_plus_proj in Hp. rewrite !real_mult_proj in Hp.
    rewrite real_const_proj in Hp.
    exact Hp. }
  assert (Hax : projT1 x n * projT1 x n == Qabs (projT1 x n) * Qabs (projT1 x n))
    by apply Qsq_abs_eq.
  assert (Hay : projT1 y n * projT1 y n == Qabs (projT1 y n) * Qabs (projT1 y n))
    by apply Qsq_abs_eq.
  assert (Hax0 : Qle 0 (Qabs (projT1 x n))) by apply Qabs_nonneg.
  assert (Hay0 : Qle 0 (Qabs (projT1 y n))) by apply Qabs_nonneg.
  assert (Hpos1q : Qlt 0 e1) by (apply QltT_to_Qlt; exact Hpos1).
  destruct (Qle_or_lt (Qabs (projT1 x n)) (Qabs (projT1 y n))) as [Hle | Hgt];
    nra.
Defined.
(* |x·y| ≤ |x|·y + eps（y > 0 尾段；eps 直接透传） *)
Lemma abs_mult_pos_eps : forall (x y : Real) (eps : Real),
  real_lt real_zero y -> real_lt real_zero eps ->
  real_lt (real_abs (real_mult x y))
          (real_plus (real_mult (real_abs x) y) eps).
Proof.
  intros x y eps Hy Heps.
  destruct Hy as [ey [Hpey [Ny HNy]]].
  destruct Heps as [ee [Hpee [Ne HNe]]].
  exists ee. split; [exact Hpee | exists (Nat.max Ny Ne); intros n Hn].
  assert (Hny : (Ny <= n)%nat).
  { apply (Nat.le_trans Ny (Nat.max Ny Ne) n);
      [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  assert (Hne : (Ne <= n)%nat).
  { apply (Nat.le_trans Ne (Nat.max Ny Ne) n);
      [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  apply Qlt_to_QltT.
  rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_abs_proj.
  rewrite ?real_mult_proj. rewrite ?real_plus_proj. rewrite ?real_abs_proj.
  assert (Hy0 : Qle 0 (projT1 y n)).
  { assert (Hq : Qlt ey (projT1 y n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNy n (NatLe_lift Ny n Hny)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 y n - 0) with (projT1 y n) in Hq by ring.
    apply (Qle_trans 0 ey (projT1 y n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpey.
    - apply Qlt_le_weak. exact Hq. }
  rewrite (Qabs_mult_gen (projT1 x n) (projT1 y n)).
  rewrite (Qabs_pos (projT1 y n) Hy0).
  assert (Hep : Qlt ee (projT1 eps n - projT1 real_zero n)).
  { apply QltT_to_Qlt. exact (HNe n (NatLe_lift Ne n Hne)). }
  change (projT1 real_zero n) with 0%Q in Hep.
  lra.
Qed.

(* ################ 第 5 部分：本地投影 + 严格 C-S（CW219.Real 版） ## *)

Lemma sql_proj_l : forall (a : list Real) (k : nat),
  projT1 (sql a) k == sqlQ (map (fun x : Real => projT1 x k) a).
Proof.
  induction a as [| x xs IH]; intro k.
  - reflexivity.
  - cbn [sql]. rewrite real_plus_proj. rewrite real_mult_proj. rewrite IH.
    reflexivity.
Qed.

Lemma dotp_proj_l : forall (a b : list Real) (k : nat),
  projT1 (dotp a b) k
    == dotpQ (map (fun x : Real => projT1 x k) a)
             (map (fun y : Real => projT1 y k) b).
Proof.
  induction a as [| x xs IH]; intros b k.
  - reflexivity.
  - destruct b as [| y ys].
    + reflexivity.
    + cbn [dotp]. rewrite real_plus_proj. rewrite real_mult_proj. rewrite IH.
      reflexivity.
Qed.

(* 有限和 Cauchy–Schwarz（严格版，实层；UpCS cs_Q 的点对点提升） *)
Theorem cs_real_lt : forall (a b : list Real) (eps : Real),
  real_lt real_zero eps ->
  real_lt (real_mult (dotp a b) (dotp a b))
          (real_plus (real_mult (sql a) (sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    rewrite (sql_proj_l a n). rewrite (sql_proj_l b n). rewrite (dotp_proj_l a b n).
    set (A := sqlQ (map (fun x : Real => projT1 x n) a)).
    set (B := sqlQ (map (fun x : Real => projT1 x n) b)).
    set (C := dotpQ (map (fun x : Real => projT1 x n) a)
                    (map (fun y : Real => projT1 y n) b)).
    assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
    assert (Hep : Qlt e1 (projT1 eps n)).
    { pose proof (HN1 n Hn) as Ht.
      apply QltT_to_Qlt in Ht.
      assert (Hzr : projT1 eps n - projT1 real_zero n == projT1 eps n).
      { rewrite Hz0. ring. }
      rewrite Hzr in Ht. exact Ht. }
    assert (Hgap : Qle 0 (A * B - C * C)).
    { apply (Qle_trans _ (C * C - C * C)).
      - apply qeq_le. ring.
      - assert (Hcs := cs_Q (map (fun x : Real => projT1 x n) a)
                            (map (fun y : Real => projT1 y n) b)).
        unfold Qminus.
        exact (Qplus_le_compat (C * C) (A * B) (-(C * C)) (-(C * C))
                 Hcs (Qle_refl _)). }
    apply (Qlt_le_trans e1 (projT1 eps n)).
    + exact Hep.
    + apply (Qle_trans _ (0 + projT1 eps n)).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((A * B - C * C) + projT1 eps n)).
        -- exact (Qplus_le_compat 0 (A * B - C * C) (projT1 eps n) (projT1 eps n)
                    Hgap (Qle_refl _)).
        -- apply qeq_le. ring.
Qed.


Lemma Qle_add_pos_l : forall b a : Q, Qle 0 a -> Qle b (b + a).
Proof.
  intros b a Ha.
  apply (Qle_trans b (b + 0) (b + a)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat b b 0 a); [apply Qle_refl | exact Ha].
Qed.

Lemma Qle_abs_self : forall x : Q, Qle x (Qabs x).
Proof.
  intro x. destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0). apply Qle_refl.
  - rewrite (Qabs_neg x (Qlt_le_weak x 0 H0)). lra.
Qed.

(* 根的绝对值尾界（统一形式，lt/eq 两支内部消化）：
   0 在 lt 支给精确界（|rq_n| = rq_n ≤ Q_n），eq 支给 |rq_n| ≤ d。 *)
Lemma root_abs_tail : forall (rq Q2 : Real) (d : Q),
  Qlt 0 d -> real_lt real_zero Q2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)).
Proof.
  intros rq Q2 d Hd HQ Hr0 Hrq.
  destruct (real_le_pt_ev_plus rq Q2 d Hd Hrq) as [Nq HNq].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [er [Hper [Nr HNr]]].
    exists (Nat.max Nr (Nat.max Nq NQ)). intros n Hn.
    assert (Hnr : (Nr <= n)%nat) by lia.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hper' : Qlt 0 er) by (apply QltT_to_Qlt; exact Hper).
    assert (Hge : Qle 0 (projT1 rq n)).
    { assert (Hq : Qlt er (projT1 rq n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNr n (NatLe_lift Nr n Hnr)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    rewrite (Qabs_pos (projT1 rq n) Hge).
    exact (HNq n Hnq).
  - destruct (Heq0 d (Qlt_to_QltT 0 d Hd)) as [Ne HNe].
    exists (Nat.max Nq (Nat.max Ne NQ)). intros n Hn.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (Hne : (Ne <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hab : Qlt (Qabs (projT1 rq n)) d).
    { assert (Ht := HNe n (NatLe_lift Ne n Hne)).
      apply QltT_to_Qlt in Ht.
      change (projT1 real_zero n) with 0%Q in Ht.
      setoid_replace (0 - projT1 rq n) with (- projT1 rq n) in Ht by ring.
      rewrite Qabs_opp in Ht. exact Ht. }
    apply (Qle_trans (Qabs (projT1 rq n)) d (projT1 Q2 n + d)).
    { apply Qlt_le_weak. exact Hab. }
    { setoid_replace (projT1 Q2 n + d) with (d + projT1 Q2 n) by ring.
      apply (Qle_add_pos_l d (projT1 Q2 n) HQ0). }
Qed.

(* 根积尾界（统一形式）：|rq·rk| ≤ Q·K + d·(MQ+MK) + d²，其中
   MQ/MK 为 Q/K 的全局界（real_norm_bounded），d 为内部 eq 支截断粒度 *)
Lemma prod_tail_bound : forall (rq rk Q2 K2 : Real) (MQ MK : Q) (d : Q),
  Qlt 0 d ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  real_le real_zero rk -> real_le rk K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (real_mult rq rk) n))
        (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
Proof.
  intros rq rk Q2 K2 MQ MK d Hd HQ HK Hr0 Hrq Hk0 Hrk HMQ HMK.
  destruct (root_abs_tail rq Q2 d Hd HQ Hr0 Hrq) as [Nq HNq].
  destruct (root_abs_tail rk K2 d Hd HK Hk0 Hrk) as [Nk HNk].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max Nq (Nat.max Nk (Nat.max NQ NK))).
  intros n Hn.
  assert (Hnq : (Nq <= n)%nat) by lia.
  assert (Hnk : (Nk <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  rewrite real_mult_proj. rewrite Qabs_mult_gen.
  assert (Hbq : Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)) by exact (HNq n Hnq).
  assert (Hbk : Qle (Qabs (projT1 rk n)) (projT1 K2 n + d)) by exact (HNk n Hnk).
  assert (Haq : Qle 0 (Qabs (projT1 rq n))) by apply Qabs_nonneg.
  assert (Hak : Qle 0 (Qabs (projT1 rk n))) by apply Qabs_nonneg.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
    lra. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    assert (HpeK' : Qlt 0 eK) by (apply QltT_to_Qlt; exact HpeK).
    lra. }
  assert (HQm : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    { apply Qle_abs_self. }
    { exact (HMQ n). } }
  assert (HKm : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    { apply Qle_abs_self. }
    { exact (HMK n). } }
  apply (Qle_trans (Qabs (projT1 rq n) * Qabs (projT1 rk n))
                   ((projT1 Q2 n + d) * (projT1 K2 n + d))
                   (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
  - apply (Qmult_le_mono2 _ _ _ _ Haq Hak Hbq Hbk).
  - nra.
Qed.


(* ################ 第 6 部分：件 1 内积/范数桥 #################### *)

(* 件 1：⟨q,q⟩ == Σq²（UpCS 的 sql 即 Σq²——命名桥）。 *)
Theorem inner_sq_norm : forall q : list Real, real_eq (dotp q q) (sql q).
Proof.
  intro q. apply real_eq_of_zero_diff. intros n.
  rewrite (dotp_proj_l q q n). rewrite (sql_proj_l q n).
  rewrite dotpQ_sqlQ. ring.
Qed.

(* ################ 第 7 部分：件 2 界转化主件 #################### *)

(* 配对界：根有界前提 ⟹ |⟨a,b⟩| < Q·K + h（inl 严格支； witness h/4） *)
Lemma qk_pair_bound : forall (a b : list Real) (Q2 K2 : Real) (MQ MK : Q) (h : Q)
  (Ha : real_le real_zero (sql a)) (Hb : real_le real_zero (sql b)),
  Qlt 0 h -> Qlt 0 MQ -> Qlt 0 MK ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le (root_of (sql a) Ha) Q2 -> real_le (root_of (sql b) Hb) K2 ->
  real_lt (real_abs (dotp a b)) (real_plus (real_mult Q2 K2) (real_const h)).
Proof.
  intros a b Q2 K2 MQ MK h Ha Hb Hh HMQp HMKp HQ HK HMQ HMK Hqa Hkb.
  set (ra := root_of (sql a) Ha).
  set (rb := root_of (sql b) Hb).
  assert (Hrasq : real_eq (real_mult ra ra) (sql a)) by apply (root_sq_of (sql a) Ha).
  assert (Hrbsq : real_eq (real_mult rb rb) (sql b)) by apply (root_sq_of (sql b) Hb).
  assert (Hra0 : real_le real_zero ra) by apply (root_zero_of (sql a) Ha).
  assert (Hrb0 : real_le real_zero rb) by apply (root_zero_of (sql b) Hb).
  (* C-S 严格版，eps := ((1#4)*h)² *)
  assert (Hcs : real_lt (real_mult (dotp a b) (dotp a b))
                  (real_plus (real_mult (sql a) (sql b))
                              (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply cs_real_lt. apply real_const_pos.
    apply (Qmult_lt_0_compat ((1#4) * h) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh]. }
  (* 换元到 (ra·rb)² *)
  assert (E12 : real_eq (real_mult (sql a) (sql b))
                        (real_mult (real_mult ra rb) (real_mult ra rb))).
  { apply (real_eq_trans (real_mult (sql a) (sql b))
                         (real_mult (real_mult ra ra) (real_mult rb rb)) _).
    - apply (RealSetoid.real_eq_mult_compat (sql a) (sql b)
                                 (real_mult ra ra) (real_mult rb rb)
                                 (real_eq_sym (real_mult ra ra) (sql a) Hrasq)
                                 (real_eq_sym (real_mult rb rb) (sql b) Hrbsq)).
    - apply real_eq_of_zero_diff. intro n.
      rewrite !real_mult_proj. ring. }
  assert (H3 : real_lt (real_mult (dotp a b) (dotp a b))
                (real_plus (real_mult (real_mult ra rb) (real_mult ra rb))
                           (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply (real_lt_le_trans _ (real_plus (real_mult (sql a) (sql b))
                                          (real_const (((1#4) * h) * ((1#4) * h)))) _ Hcs).
    apply (real_le_plus_compat (real_mult (sql a) (sql b))
                               (real_mult (real_mult ra rb) (real_mult ra rb))
                               (real_const (((1#4) * h) * ((1#4) * h)))
                               (real_const (((1#4) * h) * ((1#4) * h)))).
    + apply (RealSetoid.real_eq_le (real_mult (sql a) (sql b))
                                   (real_mult (real_mult ra rb) (real_mult ra rb))
                                   E12).
    + apply (real_le_refl (real_const (((1#4) * h) * ((1#4) * h)))). }
  (* B'：|AB| < |ra·rb| + 2·((1#4)*h) = |ra·rb| + (1#2)*h *)
  assert (H4 : real_lt (real_abs (dotp a b))
                (real_plus (real_abs (real_mult ra rb))
                           (real_const (2 * ((1#4) * h))))).
  { apply (abs_le_add_abs_of_sq_lt (dotp a b) (real_mult ra rb) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - exact H3. }
  (* B' 的点对点尾事实（不破坏 witness 值）：
     per n ≥ N4: |AB|_n ≤ |ra_n·rb_n| + (1#2)*h  —— 由 real_lt 的严格差与 eps4 > 0 *)
  destruct H4 as [eps4 [Hpos4 [N4 HN4]]].
  set (d := h / (32 * (1 + MQ + MK + h))).
  assert (Hgt : Qlt 0 (1 + MQ + MK + h)) by lra.
  assert (HX1 : Qle 1 (1 + MQ + MK + h)) by lra.
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply (Qmult_lt_0_compat h (/ (32 * (1 + MQ + MK + h)))).
    - exact Hh.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + MQ + MK + h)).
      + exact Qlt_0_32.
      + exact Hgt. }
  assert (Hd1 : d * (32 * (1 + MQ + MK + h)) == h).
  { unfold d. field.
    intro Hz. lra. }
  assert (Hd2 : Qle (16 * (d * (MQ + MK) + d * d)) h).
  { assert (Hdh : Qle d h) by nra.
    nra. }
  destruct (prod_tail_bound ra rb Q2 K2 MQ MK d Hd0 HQ HK
              Hra0 Hqa Hrb0 Hkb
              HMQ HMK) as [Np HNp].
  exists ((1#4) * h). split.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
  - exists (Nat.max N4 Np). intros n Hn.
    assert (Hn4 : (N4 <= n)%nat).
    { apply (Nat.le_trans N4 (Nat.max N4 Np) n);
        [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    assert (Hnp : (Np <= n)%nat).
    { apply (Nat.le_trans Np (Nat.max N4 Np) n);
        [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite !real_mult_proj. rewrite real_const_proj.
    rewrite !real_abs_proj.
    assert (Hf1 : Qle (Qabs (projT1 (dotp a b) n))
                      (Qabs (projT1 ra n) * Qabs (projT1 rb n) + (1#2) * h)).
    { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
      apply QltT_to_Qlt in Hq.
      assert (Hpe4 : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      rewrite real_plus_proj in Hq. rewrite real_const_proj in Hq.
      rewrite !real_abs_proj in Hq.
      rewrite real_mult_proj in Hq.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hq.
      lra. }
    assert (Hf2 : Qle (Qabs (projT1 ra n) * Qabs (projT1 rb n))
                      (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
    { pose proof (HNp n Hnp) as Hp.
      rewrite real_mult_proj in Hp.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hp.
      exact Hp. }
    nra.
Qed.
(* ################ 第 8 部分：件 2 rd-loss 链 + 主定理 ############ *)

(* rd ≥ 0 尾段（inl 支精确；inr 支 rd≈0 与 rd²≈S k≥1 矛盾） *)
Lemma rd_pos_tail : forall (k : nat) (r : Real),
  real_le real_zero r -> real_eq (real_mult r r) (nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle 0 (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq.
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists N0. intros n Hn0.
    assert (Hq : Qlt e0 (projT1 r n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 r n - 0) with (projT1 r n) in Hq by ring.
    apply (Qle_trans 0 e0 (projT1 r n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact Hpos0
      | apply Qlt_le_weak; exact Hq].
  - exfalso.
    destruct (sq_bound_from_eq k r Hrsq) as [N1 HN1].
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (H9 : Qlt (9#16)
                   (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)).
    assert (Hs := HN2 (Nat.max N1 N2)
                    (NatLe_lift N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2))).
    apply QltT_to_Qlt in Hs.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hs.
    setoid_replace (0 - projT1 r (Nat.max N1 N2))
      with (- projT1 r (Nat.max N1 N2)) in Hs by ring.
    rewrite Qabs_opp in Hs.
    assert (Hsq : projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)
                  == Qabs (projT1 r (Nat.max N1 N2))
                     * Qabs (projT1 r (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos
                    (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2))
                    (Qle_0_sq_Q (projT1 r (Nat.max N1 N2)))).
      apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hmono : Qabs (projT1 r (Nat.max N1 N2))
                      * Qabs (projT1 r (Nat.max N1 N2)) < (1#16)).
    { assert (Ha0 : Qle 0 (Qabs (projT1 r (Nat.max N1 N2))))
        by apply Qabs_nonneg.
      nra. }
    lra.
Qed.

(* rd ≥ 1 − dq 尾段（dq ≤ 1 前提下） *)
Lemma rd_ge_one_minus_delta : forall (k : nat) (r : Real) (dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_le real_zero r -> real_eq (real_mult r r) (nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (1 - dq) (projT1 r n)).
Proof.
  intros k r dq Hdq0 Hdq1 Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (Qle_or_lt 1 dq) as [Hge | Hlt].
  - exists N0. intros n Hn. pose proof (HN0 n Hn) as Hge0. lra.
  - assert (Hpos : Qlt 0 (1 - dq)) by lra.
    assert (Heps : Qlt 0 (1 - (1 - dq) * (1 - dq))) by nra.
    destruct (Hrsq (1 - (1 - dq) * (1 - dq))
                   (Qlt_to_QltT 0 (1 - (1 - dq) * (1 - dq)) Heps)) as [N1 HN1].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    apply (QH1core (1 - dq) (projT1 r n)).
    + assert (Hd1 : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
      lra.
    + exact (HN0 n Hn0).
    + (* rd² ≈ S k 尾段 ⟹ rd_n² > S k − (1−(1−dq)²) ≥ (1−dq)² *)
      assert (Hs := HN1 n (NatLe_lift N1 n Hn1)).
      apply QltT_to_Qlt in Hs.
      assert (Hlow := Qabs_lt_low _ _ Hs).
      rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
      rewrite real_mult_proj in Hlow.
      assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
      nra.
Qed.

(* 件 2：rd-loss 后的最终界——Q·K ≤ Q·K·rd + MQ·MK·dq（尾段） *)
Lemma qk_rd_loss : forall (k : nat) (Q2 K2 r : Real) (MQ MK dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le real_zero r -> real_eq (real_mult r r) (nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (projT1 Q2 n * projT1 K2 n)
        (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
Proof.
  intros k Q2 K2 r MQ MK dq Hdq0 Hdq1 HQ HK HMQ HMK Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (rd_ge_one_minus_delta k r dq Hdq0 Hdq1 Hr0 Hrsq) as [N1 HN1].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max N0 (Nat.max N1 (Nat.max NQ NK))). intros n Hn.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 Q2 n - 0) with (projT1 Q2 n) in Hq by ring.
    apply (Qle_trans 0 eQ (projT1 Q2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeQ
      | apply Qlt_le_weak; exact Hq]. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    setoid_replace (projT1 K2 n - 0) with (projT1 K2 n) in Hk by ring.
    apply (Qle_trans 0 eK (projT1 K2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeK
      | apply Qlt_le_weak; exact Hk]. }
  assert (HQb : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    - apply Qle_abs_self.
    - exact (HMQ n). }
  assert (HKb : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    - apply Qle_abs_self.
    - exact (HMK n). }
  assert (Hrdn : Qle (1 - dq) (projT1 r n)) by (exact (HN1 n Hn1)).
  assert (Hsum : Qle 1 (projT1 r n + dq)) by lra.
  assert (Hdq0le : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
  assert (Hd : Qle (projT1 Q2 n * projT1 K2 n) (MQ * MK)).
  { apply (Qmult_le_mono2 (projT1 Q2 n) (projT1 K2 n) MQ MK);
      [exact HQ0 | exact HK0 | exact HQb | exact HKb]. }
  assert (Hqk20 : Qle 0 (projT1 Q2 n * projT1 K2 n)).
  { apply (Qmult_le_0_compat (projT1 Q2 n) (projT1 K2 n)); assumption. }
  assert (Hscale : Qle (projT1 Q2 n * projT1 K2 n)
                       (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
  { apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                     (projT1 Q2 n * projT1 K2 n * 1)
                     (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
    - apply qeq_le. ring.
    - apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) 1
                            (projT1 Q2 n * projT1 K2 n) (projT1 r n + dq));
        [exact Hqk20 | exact zero_le_one | apply Qle_refl | exact Hsum]. }
  assert (Hdqle : Qle (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq)).
  { apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) dq (MQ * MK) dq);
      [exact Hqk20 | exact Hdq0le | exact Hd | apply Qle_refl]. }
  assert (Hsplit : Qle (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                       (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
  { setoid_replace (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
      with (projT1 Q2 n * projT1 K2 n * projT1 r n
            + projT1 Q2 n * projT1 K2 n * dq) by ring.
    apply (Qplus_le_compat (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq));
      [apply Qle_refl | exact Hdqle]. }
  apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                   (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                   (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq));
    [exact Hscale | exact Hsplit].
Qed.

(* ################ 第 9 部分：件 2 主定理（rd-loss 链装配） ######## *)

(* 件 2：根有界前提 ⟹ |⟨a,b⟩| ≤ Q·K·√d + eps（eps 版；inl 严格支）。
   装配：qk_pair_bound（h := eps/2，witness eps/8 严格）+ rd-loss 链
   （QK ≤ QK·rd + QK·dq，dq := eps/(32(1+QK))；dq ≤ 1 支用 qk_rd_loss，
   dq > 1 支 eps 本身已大、只需 rd ≥ 0 尾段），eps/4 余量 witness。 *)
Theorem real_logit_bound_of_norm_bounds :
  forall (a b : list Real) (Qb Kb : Q) (k : nat) (eps : Q)
    (Ha : real_le real_zero (sql a)) (Hb : real_le real_zero (sql b)),
    Qlt 0 eps -> Qlt 0 Qb -> Qlt 0 Kb ->
    real_le (root_of (sql a) Ha) (real_const Qb) ->
    real_le (root_of (sql b) Hb) (real_const Kb) ->
    real_le (real_abs (dotp a b))
      (real_plus (real_mult (real_mult (real_const Qb) (real_const Kb)) (root_d k))
                 (real_const eps)).
Proof.
  intros a b Qb Kb k eps Ha Hb Heps HQ HK Hqa Hkb.
  assert (HQK0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
  assert (Hgt1 : Qlt 0 (1 + Qb * Kb)) by lra.
  set (dq := eps / (32 * (1 + Qb * Kb))).
  assert (Hdq0 : Qlt 0 dq).
  { unfold dq. apply (Qmult_lt_0_compat eps (/ (32 * (1 + Qb * Kb)))).
    - exact Heps.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + Qb * Kb)).
      + exact Qlt_0_32.
      + exact Hgt1. }
  assert (Hdqe : dq * (32 * (1 + Qb * Kb)) == eps).
  { unfold dq. field.
    intro Hz. lra. }
  assert (Hdqk : Qle (Qb * Kb * dq) ((1#32) * eps)).
  { rewrite <- Hdqe.
    setoid_replace ((1#32) * (dq * (32 * (1 + Qb * Kb))))
      with (dq + dq * (Qb * Kb)) by ring.
    setoid_replace (Qb * Kb * dq) with (0 + dq * (Qb * Kb)) by ring.
    apply (Qplus_le_compat 0%Q dq (dq * (Qb * Kb)) (dq * (Qb * Kb))).
    - apply Qlt_le_weak. exact Hdq0.
    - apply Qle_refl. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  destruct (qk_pair_bound a b (real_const Qb) (real_const Kb) Qb Kb ((1#2) * eps)
              Ha Hb
              (Qmult_lt_0_compat (1#2) eps Qlt_0_half Heps) HQ HK HcQpos HcKpos
              HQbnd HKbnd Hqa Hkb) as [eps4 [Hpos4 [N4 HN4]]].
  destruct (Qle_or_lt dq 1) as [Hdq1 | Hdqbig].
  - (* dq ≤ 1：rd-loss 链 QK ≤ QK·rd + QK·dq *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (qk_rd_loss k (real_const Qb) (real_const Kb) (root_d k) Qb Kb dq
                Hdq0 Hdq1 HcQpos HcKpos HQbnd HKbnd Hrd0 (root_d_sq k))
      as [N2 HN2].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N2). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N2) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      assert (Hn2 : (N2 <= n)%nat).
      { apply (Nat.le_trans N2 (Nat.max N4 N2) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj.
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Hbr : Qle (Qb * Kb) (Qb * Kb * projT1 (root_d k) n + Qb * Kb * dq)).
      { pose proof (HN2 n Hn2) as Hq.
        rewrite !real_const_proj in Hq. exact Hq. }
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      remember (Mq * dq) as Z eqn:HZ in *.
      clear HQ HK Hgt1 HQK0 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN2 Hrd0.
      assert (Hbr2 : Qle (Mq - (1#32) * eps) W).
      { assert (H1 : Qle (Mq - Z) W) by lra.
        apply (Qle_trans (Mq - (1#32) * eps) (Mq - Z) W).
        - lra.
        - exact H1. }
      clear HW HZ Hbr Hdqk Hdq0 Hdq1.
      lra.
  - (* dq > 1：eps > 32(1+QK)，QK 本身 < eps/32，只需 rd ≥ 0 尾段 *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (rd_pos_tail k (root_d k) Hrd0 (root_d_sq k)) as [N0 HN0].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N0). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N0) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      assert (Hn0 : (N0 <= n)%nat).
      { apply (Nat.le_trans N0 (Nat.max N4 N0) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj.
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Hrn : Qle 0 (projT1 (root_d k) n)) by (exact (HN0 n Hn0)).
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      clear HQ HK Hgt1 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN0 Hdq0.
      assert (Hmlt : Qlt Mq (Mq * dq)).
      { pose proof (Qmult_lt_compat_r 1 dq Mq HQK0 Hdqbig) as Hm2.
        setoid_replace (1 * Mq) with Mq in Hm2 by ring.
        setoid_replace (dq * Mq) with (Mq * dq) in Hm2 by ring.
        exact Hm2. }
      assert (Hm32 : Qle Mq ((1#32) * eps)).
      { apply (Qle_trans Mq (Mq * dq) ((1#32) * eps));
          [apply Qlt_le_weak; exact Hmlt | exact Hdqk]. }
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      assert (Hw0 : Qle 0 W).
      { subst W. apply (Qmult_le_0_compat Mq (projT1 (root_d k) n)).
        - apply Qlt_le_weak. exact HQK0.
        - exact Hrn. }
      clear Hmlt Hdqbig Hdqk HQK0 HW Hrn.
      lra.
Qed.

(* ################ 第 10 部分：件 3 QKᵀ 绑定 + Δ 打包（Section 旗舰） ## *)

Section QKLogitSection.

Variable kdim : nat.
Variable Qc Kc : Q.

(* 逆根：real_inv_pos 构造性携带正性证书（root_d_pos） *)
Definition w_root : Real := real_inv_pos (root_d kdim) (root_d_pos kdim).

(* Δ := Q·K·inv(√d) + 1（+1 余量精确吸收 (1/2)·w ≤ 2/3 < 1） *)
Definition Delta : Real :=
  real_plus (real_mult (real_mult (real_const Qc) (real_const Kc)) w_root)
            (real_const 1).

(* attn_logit：⟨q,k⟩·inv(√d) *)
Definition attn_logit (a b : list Real) : Real :=
  real_mult (dotp a b) w_root.

End QKLogitSection.

(* w_root 尾段数据：正性（real_inv_pos_pos 尾段）+ 乘法核对
   （real_inv_pos_correct 尾段，固定 δ := 1#4 截断：3/4 < Wn·Rn < 5/4）。
   下界系数 5/3 由 rd ≥ 3/4 吸收：Wn ≤ 5/3，(3/8)·Wn ≤ 5/8 < 1，
   Δ 的 +1 余量照常吸收（per-pair witness 仍为 1/4）。 *)
Theorem qk_logits_bounded :
  forall (k : nat) (Qb Kb : Q) (vq vk : nat -> list Real)
    (Hvsq : forall s : nat, real_le real_zero (sql (vq s)))
    (Hksq : forall s : nat, real_le real_zero (sql (vk s))),
    Qlt 0 Qb -> Qlt 0 Kb ->
    (forall s : nat, real_le (root_of (sql (vq s)) (Hvsq s)) (real_const Qb)) ->
    (forall s : nat, real_le (root_of (sql (vk s)) (Hksq s)) (real_const Kb)) ->
    And (real_lt real_zero (Delta k Qb Kb))
        (forall s s' : nat,
           real_le (real_abs (attn_logit k (vq s) (vk s'))) (Delta k Qb Kb)).
Proof.
  intros k Qb Kb vq vk Hvsq Hksq HQ HK Hvb Hkb.
  assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
  destruct (sqrt_dim_ge_quarter k (root_d k) Hrd0 (root_d_sq k)) as [Ns HNs].
  assert (Hwlt : real_lt real_zero (w_root k))
    by (apply (real_inv_pos_pos (root_d k) (root_d_pos k))).
  destruct Hwlt as [ew [Hpew [Nwp HNwp]]].
  assert (Hcorrect : real_eq (real_mult (root_d k) (w_root k)) real_one)
    by (apply (real_inv_pos_correct (root_d k) (root_d_pos k))).
  assert (Hqt : Qlt 0 (1#8)) by lra.
  destruct (Hcorrect (1#8) (Qlt_to_QltT 0 (1#8) Hqt)) as [Nc HNc].
  set (Nw := Nat.max Ns (Nat.max Nwp Nc)).
  assert (Hwp' : forall n : nat, (Nw <= n)%nat -> Qlt 0 (projT1 (w_root k) n)).
  { intros n Hnn.
    assert (Hnwp : (Nwp <= n)%nat).
    { apply (Nat.le_trans Nwp Nw n).
      - apply (Nat.le_trans Nwp (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_l.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hq : Qlt ew (projT1 (w_root k) n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNwp n (NatLe_lift Nwp n Hnwp)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 (w_root k) n - 0) with (projT1 (w_root k) n) in Hq by ring.
    apply (Qle_lt_trans 0 ew (projT1 (w_root k) n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpew.
    - exact Hq. }
  assert (Hwub : forall n : nat, (Nw <= n)%nat ->
            Qlt (projT1 (w_root k) n) (3#2)).
  { intros n Hnn.
    assert (Hnc : (Nc <= n)%nat).
    { apply (Nat.le_trans Nc Nw n).
      - apply (Nat.le_trans Nc (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_r.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hc' : Qlt (Qabs (projT1 (root_d k) n * projT1 (w_root k) n - 1)) (1#8)).
    { pose proof (HNc n (NatLe_lift Nc n Hnc)) as Hq.
      apply QltT_to_Qlt in Hq.
      rewrite real_mult_proj in Hq.
      change (projT1 real_one n) with 1%Q in Hq.
      exact Hq. }
    assert (Hrl : Qlt (3#4) (projT1 (root_d k) n * projT1 (w_root k) n)).
    { assert (Hl := Qabs_lt_low _ _ Hc'). lra. }
    assert (Hru : Qlt (projT1 (root_d k) n * projT1 (w_root k) n) (9#8)).
    { assert (Hu := Qabs_lt_l _ _ Hc'). lra. }
    assert (Hwpn : Qlt 0 (projT1 (w_root k) n)) by (apply (Hwp' n Hnn)).
    assert (Hns : (Ns <= n)%nat).
    { apply (Nat.le_trans Ns Nw n).
      - apply Nat.le_max_l.
      - exact Hnn. }
    assert (Hs1 : Qle ((3#4) * projT1 (w_root k) n)
                      (projT1 (root_d k) n * projT1 (w_root k) n)).
    { apply (Qmult_le_compat_r (3#4) (projT1 (root_d k) n) (projT1 (w_root k) n));
        [exact (HNs n Hns) | apply Qlt_le_weak; exact Hwpn]. }
    assert (Hw43b : Qle (projT1 (w_root k) n)
                      ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
    { apply (Qle_trans (projT1 (w_root k) n)
                       ((4#3) * ((3#4) * projT1 (w_root k) n))
                       ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
      - apply qeq_le. ring.
      - setoid_replace ((4#3) * ((3#4) * projT1 (w_root k) n))
          with (((3#4) * projT1 (w_root k) n) * (4#3)) by ring.
        setoid_replace ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))
          with ((projT1 (root_d k) n * projT1 (w_root k) n) * (4#3)) by ring.
        apply (Qmult_le_compat_r ((3#4) * projT1 (w_root k) n)
                                  (projT1 (root_d k) n * projT1 (w_root k) n) (4#3)).
        + exact Hs1.
        + apply Qlt_le_weak. lra. }
    clear - Hw43b Hru Hwpn. lra. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  assert (Hpair : forall s s' : nat,
           real_lt (real_abs (dotp (vq s) (vk s')))
                   (real_plus (real_mult (real_const Qb) (real_const Kb))
                              (real_const (1#2)))).
  { intros s s'.
    apply (qk_pair_bound (vq s) (vk s') (real_const Qb) (real_const Kb) Qb Kb (1#2)
             (Hvsq s) (Hksq s') Qlt_0_half HQ HK HcQpos HcKpos HQbnd HKbnd
             (Hvb s) (Hkb s')). }
  split.
  - (* Δ > 0（witness 1/2）：QK > 0 且 Wn > 0（尾段） *)
    exists (1#2). split.
    + apply Qlt_to_QltT. exact Qlt_0_half.
    + exists Nw. intros n Hn.
      unfold Delta.
      apply Qlt_to_QltT.
      change (projT1 real_zero n) with 0%Q.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      setoid_replace (Qb * Kb * projT1 (w_root k) n + 1 - 0)
        with (Qb * Kb * projT1 (w_root k) n + 1) by ring.
      assert (Hnn : (Nw <= n)%nat) by (apply (NatLe_drop Nw n Hn)).
      pose proof (Hwp' n Hnn) as Hwp.
      assert (Hqk0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
      assert (Hqw : Qlt 0 (Qb * Kb * projT1 (w_root k) n)).
      { apply (Qmult_lt_0_compat (Qb * Kb) (projT1 (w_root k) n));
          [exact Hqk0 | exact Hwp]. }
      setoid_replace ((1#2)%Q) with (0 + (1#2)) by ring.
      apply (Qplus_lt_compat 0 (Qb * Kb * projT1 (w_root k) n) (1#2) 1);
        [exact Hqw | exact Qlt_half_one].
  - (* 逐对 |logit| ≤ Δ（inl 严格支，witness 1/4） *)
    intros s s'.
    destruct (Hpair s s') as [epsp [Hpsep [Np HNp]]].
    left.
    exists (1#4). split.
    + apply Qlt_to_QltT. exact Qlt_0_quarter.
    + exists (Nat.max Nw Np). intros n Hn.
      assert (Hnn : (Nw <= n)%nat).
      { apply (Nat.le_trans Nw (Nat.max Nw Np) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      assert (Hnp : (Np <= n)%nat).
      { apply (Nat.le_trans Np (Nat.max Nw Np) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      unfold attn_logit, Delta.
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj. rewrite ?real_mult_proj.
      rewrite (Qabs_mult_gen (projT1 (dotp (vq s) (vk s')) n)
                             (projT1 (w_root k) n)).
      rewrite (Qabs_pos (projT1 (w_root k) n) (Qlt_le_weak 0 (projT1 (w_root k) n) (Hwp' n Hnn))).
      assert (Hpp : Qlt epsp
                        (Qb * Kb + (1#2)
                           - Qabs (projT1 (dotp (vq s) (vk s')) n))).
      { pose proof (HNp n (NatLe_lift Np n Hnp)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Heps' : Qlt 0 epsp) by (apply QltT_to_Qlt; exact Hpsep).
      remember (Qabs (projT1 (dotp (vq s) (vk s')) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq2 eqn:HM2 in *.
      clear - Hpp Heps' Hwp' Hwub Hnn.
      assert (Hpp2 : Qle Aq (Mq2 + (1#2))) by lra.
      remember (Aq * projT1 (w_root k) n) as XW eqn:HXX in *.
      remember (Mq2 * projT1 (w_root k) n) as QW eqn:HQW in *.
      clear - Hpp2 Hwp' Hwub HXX HQW Hnn Hpp Heps'.
      assert (Hxw' : Qlt XW (QW + (3#4))).
      { rewrite HQW.
        apply (Qle_lt_trans XW (Aq * projT1 (w_root k) n)
                            (Mq2 * projT1 (w_root k) n + (3#4))).
        - apply qeq_le. rewrite <- HXX. reflexivity.
        - apply (Qle_lt_trans (Aq * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (3#4))).
          + setoid_replace (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
              with ((Mq2 + (1#2)) * projT1 (w_root k) n) by ring.
            apply (Qmult_le_compat_r Aq (Mq2 + (1#2)) (projT1 (w_root k) n));
              [exact Hpp2 | apply Qlt_le_weak; exact (Hwp' n Hnn)].
          + apply (proj2 (Qplus_lt_r ((1#2) * projT1 (w_root k) n) (3#4)
                                     (Mq2 * projT1 (w_root k) n))).
            setoid_replace (3#4) with ((3#2) * (1#2)) by ring.
            setoid_replace ((1#2) * projT1 (w_root k) n)
              with (projT1 (w_root k) n * (1#2)) by ring.
            apply (Qmult_lt_compat_r (projT1 (w_root k) n) (3#2) (1#2));
              [lra | exact (Hwub n Hnn)]. }
      clear - Hxw'. lra.
Qed.
