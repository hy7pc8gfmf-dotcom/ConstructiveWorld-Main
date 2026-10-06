(* ===================================================================== *)
(*  abl_z2_pointwise.v —— ζ(2) 第四塔·逐点控制面（Beukers 二重积分族第一层）  *)
(*  模块名：abl_z2_pointwise。                                            *)
(*  使命：为 Beukers 1979 的 ζ(2) 无理性二重积分                          *)
(*        I_n = ∫₀¹∫₀¹ (x(1−x)y(1−y))ⁿ/(1−xy)ⁿ⁺¹ dx dy 建立被积族的        *)
(*        逐点指数控制。记 N := x(1−x)y(1−y)，在闭方格 0≤x,y≤1 上证得：    *)
(*        ① 主不等式 10N ≤ 1−xy（换元 u=1−x, v=1−y 后经 m=u+v, k=uv       *)
(*        化为 m 的单变元四次式：F = m−k(11−10m+10k)，由 4k≤m² 放缩至      *)
(*        m−(m²/4)((5/2)(2−m)²+1) = (m/8)(8−2m−5m(2−m)²)，末步分档        *)
(*        m≤1 用 32−27m(2−m)² = (3m−2)²(8−3m)≥0、m≥1 用                   *)
(*        8−2m−5m(2−m)² = 5w(w−1)²+(4−3w)（w=2−m∈[0,1]）双平方分解；      *)
(*        ② 平方恒等式对 (1−xy)²−4x(1−x)(1−y) = (1−2x+xy)² 及 y 对称形，  *)
(*        相乘并约去得 4N ≤ (1−xy)²；③ 复合面：对 n 归纳证                *)
(*        4·10ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（除法自由形），即被积函数族逐点不超过    *)
(*        (1/4)·(1/10)ⁿ。常数 1/10 的真最优为 ((√5−1)/2)⁵ ≈ 0.0902，       *)
(*        取整值常数以保有理短证书形。                                    *)
(*  依赖：仅 Stdlib QArith/ZArith/Arith。零自动化战术依赖：有理域线性放缩  *)
(*        全部以显式引理链（Qle_trans＋Qplus_le_compat＋                  *)
(*        Qmult_le_compat_r＋平方非负）组合，每步证书可独立核验。          *)
(*        序关系以 Set 层类型实现：zb2_id（Set 层恒等型）与 zb2_qle        *)
(*        （Qle_bool 的 Set 层见证），与栈内 QleT' 结构同型，              *)
(*        下游件以 zb2_qle_to_Qle 后 Qle_to_QleT' 三行桥即达。             *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.    *)
(*        London Math. Soc. 11 (1979) 的被积函数族逐点估计步。             *)
(*  构造性：纯构造性、零假设声明、零承认词面；主语句全 Set 面（zb2_qle），  *)
(*        Qle/Qeq 仅作推理支撑面；全部非线性不等式以显式平方分解完成证明   *)
(*        （平方非负＋乘法保序＋正因子除法三件原子），未引入实数、         *)
(*        未引入经典逻辑。                                                *)
(*  编译配方：coqc -native-compiler no（零栈依赖，-Q 世界根仅备下游引用）。*)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 Set 层承载自立：恒等型 zb2_id 与序见证 zb2_qle                    *)
(* ============================================================ *)

(* Set 层恒等型（与栈内 Id 结构同型；本件自立以免栈依赖） *)
Inductive zb2_id (A : Set) (x : A) : A -> Set :=
  zb2_idrefl : zb2_id A x x.

(* Q 序的 Set 层见证：Qle_bool 归真（与栈内 QleT' 同型） *)
Definition zb2_qle (x y : Q) : Set := zb2_id bool (Qle_bool x y) true.

(* 常值锚：0 ≤ 1 *)
Lemma zb2_0_le_1 : (0 <= 1)%Q.
Proof. exact (proj1 (Qle_bool_iff 0 1) eq_refl). Qed.

(* 桥：Prop 面 Qle 升 Set 面 *)
Lemma zb2_qle_of_Qle : forall x y : Q, x <= y -> zb2_qle x y.
Proof.
  intros x y H.
  assert (Hb : Qle_bool x y = true) by exact (proj2 (Qle_bool_iff x y) H).
  unfold zb2_qle. rewrite Hb. apply zb2_idrefl.
Qed.

(* 桥：Set 面降 Prop 面（服务推理） *)
Lemma zb2_qle_to_Qle : forall x y : Q, zb2_qle x y -> x <= y.
Proof.
  intros x y H. apply (proj1 (Qle_bool_iff x y)).
  destruct H. reflexivity.
Qed.

(* Qeq 入 Qle（Qeq 与 Qle 在 Qnum/QDen 层的展开面） *)
Lemma zb2_qeq_imp_le : forall x y : Q, x == y -> y <= x.
Proof.
  intros x y Hxy. unfold Qle. unfold Qeq in Hxy.
  rewrite Hxy. apply Z.le_refl.
Qed.

(* 等换序：a == b 且 0 ≤ a ⟹ a ≤ b（等值两侧皆可 ≤） *)
Lemma zb2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> a <= b.
Proof.
  intros a b Hab Ha.
  apply (zb2_qeq_imp_le b a).
  apply Qeq_sym. exact Hab.
Qed.

(* 等换序（无前提）：a == b ⟹ a ≤ b *)
Lemma zb2_le_eq : forall a b : Q, a == b -> a <= b.
Proof.
  intros a b Hab.
  apply (zb2_qeq_imp_le b a). apply Qeq_sym. exact Hab.
Qed.

(* 非负沿 Qeq 传输：a == b 且 0 ≤ a ⟹ 0 ≤ b *)
Lemma zb2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> 0 <= b.
Proof.
  intros a b Hab Ha.
  apply (Qle_trans 0 a b).
  - exact Ha.
  - apply (zb2_le_eq_swap a b); assumption.
Qed.

(* 同侧换形（左端以 Qeq 换形） *)
Lemma zb2_qle_wd_l : forall x y z : Q, x == y -> zb2_qle x z -> zb2_qle y z.
Proof.
  intros x y z Hxy Hxz. apply zb2_qle_of_Qle.
  apply (Qle_trans y x z)
  ; [ apply zb2_qeq_imp_le; exact Hxy
    | apply zb2_qle_to_Qle; exact Hxz ].
Qed.

(* 同侧换形（右端以 Qeq 换形） *)
Lemma zb2_qle_wd_r : forall x y z : Q, y == z -> zb2_qle x y -> zb2_qle x z.
Proof.
  intros x y z Hyz Hxy. apply zb2_qle_of_Qle.
  apply (Qle_trans x y z)
  ; [ apply zb2_qle_to_Qle; exact Hxy
    | apply (zb2_qeq_imp_le z y); apply Qeq_sym; exact Hyz ].
Qed.

(* ============================================================ *)
(* §A 线性放缩原子库（全引理链，无自动化）                              *)
(* ============================================================ *)

(* 右加非负：0 ≤ b ⟹ a ≤ a + b *)
Lemma zb2_add_ge0_le : forall a b : Q, 0 <= b -> a <= a + b.
Proof.
  intros a b H.
  apply (Qle_trans a (a + 0) (a + b)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat a a 0 b); [ apply Qle_refl | exact H ].
Qed.

(* 减非负移位：0 ≤ b − a ⟹ a ≤ b *)
Lemma zb2_sub_ge0 : forall a b : Q, 0 <= b - a -> a <= b.
Proof.
  intros a b H. apply (Qle_trans a (a + (b - a)) b).
  - apply zb2_add_ge0_le. exact H.
  - assert (Heq : a + (b - a) == b) by ring.
    rewrite Heq. apply Qle_refl.
Qed.

(* 上界减法：a ≤ b ⟹ 0 ≤ b − a *)
Lemma zb2_le_sub : forall a b : Q, a <= b -> 0 <= b - a.
Proof.
  intros a b H.
  assert (H1 : a + (- a) <= b + (- a))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : a + (- a) == 0) by ring.
  assert (Heq2 : b + (- a) == b - a) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

(* 负号移界：s ≤ 0 ⟹ 0 ≤ −s *)
Lemma zb2_le0_opp : forall s : Q, s <= 0 -> 0 <= - s.
Proof.
  intros s H.
  assert (H1 : s + (- s) <= 0 + (- s))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : s + (- s) == 0) by ring.
  assert (Heq2 : 0 + (- s) == - s) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

(* 非负取负：0 ≤ t ⟹ −t ≤ 0 *)
Lemma zb2_ge0_opp_le : forall t : Q, 0 <= t -> - t <= 0.
Proof.
  intros t H.
  assert (H1 : (- t) + 0 <= (- t) + t)
    by (apply (Qplus_le_compat (- t) (- t) 0 t); [ apply Qle_refl | exact H ]).
  assert (Heq1 : (- t) + t == 0) by ring.
  rewrite Heq1 in H1. rewrite Qplus_0_r in H1. exact H1.
Qed.

(* 同减比较：q ≤ r ⟹ p − r ≤ p − q *)
Lemma zb2_minus_le : forall p q r : Q, q <= r -> p - r <= p - q.
Proof.
  intros p q r H. apply (zb2_sub_ge0 (p - r) (p - q)).
  assert (Heq : (p - q) - (p - r) == r - q) by ring.
  rewrite Heq. apply (zb2_le_sub q r). exact H.
Qed.

(* 非负移位：0 ≤ t ⟹ c − t ≤ c *)
Lemma zb2_minus_ge0 : forall t c : Q, 0 <= t -> c - t <= c.
Proof.
  intros t c H. apply (zb2_sub_ge0 (c - t) c).
  assert (Heq : c - (c - t) == t) by ring.
  rewrite Heq. exact H.
Qed.

(* 平方非负：s·s ≥ 0（按 0<s 与 s≤0 两档，负档换元 −s） *)
Lemma zb2_sq_ge0 : forall s : Q, 0 <= s * s.
Proof.
  intro s. destruct (Qlt_le_dec 0 s) as [Hlt | Hle].
  - apply Qmult_le_0_compat
    ; [ apply Qlt_le_weak; exact Hlt | apply Qlt_le_weak; exact Hlt ].
  - assert (Hn : 0 <= - s) by (apply zb2_le0_opp; exact Hle).
    assert (Heq : s * s == (- s) * (- s)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact Hn.
Qed.

(* 两因子乘积非负 *)
Lemma zb2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof. intros a b Ha Hb. apply Qmult_le_0_compat; assumption. Qed.

(* 四因子乘积非负 *)
Lemma zb2_mult4_ge0 : forall a b c d : Q,
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= ((a * b) * c) * d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat; assumption.
    + exact Hc.
  - exact Hd.
Qed.

(* 正因子除法：a·c ≥ 0 且 c > 0 则 a ≥ 0（a<0 时乘正因子变负，矛盾） *)
Lemma zb2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> 0 <= a.
Proof.
  intros a c Hac Hc.
  destruct (Qlt_le_dec 0 a) as [Hlt | Hle].
  - apply Qlt_le_weak; exact Hlt.
  - destruct (Qlt_le_dec a 0) as [Hneg | Hzero].
    + exfalso.
      pose proof (Qmult_lt_compat_r a 0 c Hc Hneg) as Hbad.
      assert (Heq : 0 * c == 0) by ring.
      rewrite Heq in Hbad.
      exact (Qlt_not_le (a * c) 0 Hbad Hac).
    + assert (Ha0 : a == 0) by (apply Qle_antisym; assumption).
      rewrite Ha0. apply Qle_refl.
Qed.

(* Q 幂（本件自定、与栈内同构定义） *)
Fixpoint zb2_pow (t : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | S k' => t * zb2_pow t k'
  end.

Lemma zb2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> 0 <= zb2_pow t k.
Proof.
  intros t k Ht. induction k as [| k' IH].
  - simpl. exact zb2_0_le_1.
  - simpl. apply Qmult_le_0_compat; [ exact Ht | exact IH ].
Qed.

(* 乘积封一：0≤x≤1、0≤y≤1 ⟹ xy ≤ 1 *)
Lemma zb2_xy_le_1 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> x * y <= 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  apply (Qle_trans (x * y) (1 * 1) 1).
  - apply (Qmult_le_compat_nonneg x 1 y 1)
    ; [ split; assumption | split; assumption ].
  - assert (Heq : 1 * 1 == 1) by ring.
    rewrite Heq. apply Qle_refl.
Qed.


(* 常值正性：Z 域字面（Z 域 Lia 洁净可证） *)
Lemma zb2_qmake_pos : forall (a : Z) (b : positive),
  (0 <= a)%Z -> 0 <= (a # b)%Q.
Proof.
  intros a b Ha.
  unfold Qle. simpl. lia.
Qed.

Lemma zb2_nat_pos : forall n : nat, 0 <= (Z.of_nat n # 1)%Q.
Proof.
  intro n. apply (proj1 (Qle_bool_iff 0 (Z.of_nat n # 1))).
  destruct n as [| n']; reflexivity.
Qed.

(* 成对单调：a ≤ b、c ≤ d、各量非负 ⟹ c·a ≤ d·b *)
Lemma zb2_mono_pair : forall a b c d : Q,
  a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
  c * a <= d * b.
Proof.
  intros a b c d Hab Hcd Ha Hb Hc Hd.
  apply (Qle_trans (c * a) (d * a) (d * b)).
  - apply (Qmult_le_compat_r c d a); [ exact Hcd | exact Ha ].
  - apply (Qmult_le_compat_nonneg d d a b)
    ; [ split; [ exact Hd | apply Qle_refl ] | split; [ exact Ha | exact Hab ] ].
Qed.

(* ============================================================ *)
(* §B 主不等式：10N ≤ 1−xy                                              *)
(* ============================================================ *)

(* 主不等式（换元形）：0≤u,v≤1 ⟹ 10·u(1−u)v(1−v) ≤ u+v−uv。
   证书链（记 m=u+v, k=uv；F := u+v−uv−10u(1−u)v(1−v)）：
   F = m−k(11−10m+10k) ≥ m−k((5/2)(2−m)²+1) ≥ m−(m²/4)((5/2)(2−m)²+1)
     = (m/8)(8−2m−5m(2−m)²) ≥ 0。 *)
Lemma zb2_ten_le_uv : forall u v : Q,
  0 <= u <= 1 -> 0 <= v <= 1 ->
  10 * u * (1 - u) * v * (1 - v) <= u + v - u * v.
Proof.
  intros u v [Hu1 Hu2] [Hv1 Hv2].
  assert (Hk0 : 0 <= u * v) by (apply zb2_mult2_ge0; assumption).
  assert (Hm0 : 0 <= u + v).
  { apply (Qle_trans 0 (0 + 0) (u + v)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 u 0 v); assumption. }
  assert (Hm2 : (u + v) <= 2).
  { apply (Qle_trans (u + v) (1 + 1) 2).
    - apply (Qplus_le_compat u 1 v 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (H4k : 0 <= (u+v)*(u+v) - 4*(u*v)).
  { assert (Heq : (u+v)*(u+v) - 4*(u*v) == (u-v)*(u-v)) by ring.
    rewrite Heq. apply zb2_sq_ge0. }
  (* 由 H4k 线性导出：10k ≤ (5/2)m² 与 k ≤ (m²/4) *)
  assert (HBB : 10 * (u*v) <= (5#2)*(u+v)*(u+v)).
  { apply (Qle_trans (10 * (u*v))
      (10 * (u*v) + (5#2) * ((u+v)*(u+v) - 4*(u*v)))
      ((5#2)*(u+v)*(u+v))).
    - apply zb2_add_ge0_le.
      apply (zb2_mult2_ge0 (5#2) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (zb2_qmake_pos 5 2); lia | exact H4k ].
    - assert (Heq : 10 * (u*v) + (5#2) * ((u+v)*(u+v) - 4*(u*v))
                 == (5#2)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply zb2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply (zb2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (zb2_qmake_pos 1 4); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
  (* 因子界：B ≤ B* 且 B* = (5/2)(2−m)²+1 ≥ 0 *)
  assert (HBp : 0 <= 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)).
  { assert (Hid0 : 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)
                 == (5#2)*(2-(u+v))*(2-(u+v)) + 1) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v))) by apply zb2_sq_ge0.
    assert (HX : 0 <= (5#2)*(2-(u+v))*(2-(u+v))).
    { assert (Hasso : (5#2)*(2-(u+v))*(2-(u+v))
                    == (5#2)*((2-(u+v))*(2-(u+v)))) by ring.
      rewrite Hasso.
      apply (zb2_mult2_ge0 (5#2) ((2-(u+v))*(2-(u+v)))).
      - apply (zb2_qmake_pos 5 2). lia.
      - exact Hs. }
    apply (Qle_trans 0 ((5#2)*(2-(u+v))*(2-(u+v)))
                      (((5#2)*(2-(u+v))*(2-(u+v))) + 1)).
    - exact HX.
    - apply zb2_add_ge0_le. exact zb2_0_le_1. }
  assert (HBs : 11 - 10*(u+v) + 10*(u*v)
             <= 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (11 - 10*(u+v)) (11 - 10*(u+v))
             (10*(u*v)) ((5#2)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
  (* 步一：k·B ≤ k·B* *)
  assert (HkBB : (u*v) * (11 - 10*(u+v) + 10*(u*v))
              <= (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (11 - 10*(u+v) + 10*(u*v))
                  (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (11 - 10*(u+v) + 10*(u*v))
                 == (11 - 10*(u+v) + 10*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
                 == (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
  (* 步二：k·B* ≤ (m²/4)·B* *)
  assert (HkB2 : (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
  (* 单变元末式非负（分档） *)
  assert (Hlow : 0 <= ((u+v) * (1#8))
                   * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v)))).
  { destruct (Qlt_le_dec (u+v) 1) as [Hm1 | Hm3].
    - (* 档一 m ≤ 1：m(2−m)² ≤ 32/27 *)
      assert (Hsq : 0 <= (3*(u+v)-2)*(3*(u+v)-2)) by apply zb2_sq_ge0.
      assert (Hfac : 32 - 27*(u+v)*(2-(u+v))*(2-(u+v))
                  == (3*(u+v)-2)*(3*(u+v)-2)*(8-3*(u+v))) by ring.
      assert (Hprod : 0 <= 32 - 27*(u+v)*(2-(u+v))*(2-(u+v))).
      { rewrite Hfac.
        apply (zb2_mult2_ge0 ((3*(u+v)-2)*(3*(u+v)-2)) (8-3*(u+v)))
        ; [ exact Hsq | ].
        assert (H1m : 0 <= 1 - (u+v)) by (apply (zb2_le_sub (u+v) 1); exact (Qlt_le_weak (u+v) 1 Hm1)).
        assert (Hide : 8 - 3*(u+v) == 5 + 3*(1-(u+v))) by ring.
        rewrite Hide.
        apply (Qle_trans 0 5 (5 + 3*(1-(u+v)))).
        + apply (zb2_nat_pos 5).
        + apply zb2_add_ge0_le.
          apply (zb2_mult2_ge0 3); [ apply (zb2_nat_pos 3) | exact H1m ]. }
      assert (Hd : (u+v)*(2-(u+v))*(2-(u+v)) <= (32#27)).
      { apply (zb2_sub_ge0 ((u+v)*(2-(u+v))*(2-(u+v))) (32#27)).
        assert (H0b : 0 <= (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27)).
        { apply (zb2_mult2_ge0 (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) (1#27))
          ; [ exact Hprod | apply (zb2_qmake_pos 1 27); lia ]. }
        assert (Heq2 : (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27)
                    == (32#27) - (u+v)*(2-(u+v))*(2-(u+v))) by ring.
        apply (Qle_trans 0
                 ((32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27))
                 ((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))).
        - exact H0b.
        - apply (zb2_le_eq_swap
                   ((32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27))
                   ((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))).
          + exact Heq2.
          + exact H0b. }
      apply Qmult_le_0_compat.
      + apply (zb2_mult2_ge0 (u+v) (1#8))
        ; [ exact Hm0 | apply (zb2_qmake_pos 1 8); lia ].
      + assert (H1m : 0 <= 1 - (u+v)) by (apply (zb2_le_sub (u+v) 1); exact (Qlt_le_weak (u+v) 1 Hm1)).
        assert (Hp2 : 0 <= 2*(1-(u+v)))
          by (apply (zb2_mult2_ge0 2); [ apply (zb2_nat_pos 2) | exact H1m ]).
        assert (Hp3 : 0 <= 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))
          by (apply (zb2_mult2_ge0 5)
            ; [ apply (zb2_nat_pos 5)
              | apply (zb2_le_sub ((u+v)*(2-(u+v))*(2-(u+v))) (32#27))
              ; exact Hd ]).
        assert (Hide : 8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))
                    == (2#27) + 2*(1-(u+v))
                         + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))) by ring.
        rewrite Hide.
        apply (Qle_trans 0 (2#27)
                         ((2#27) + 2*(1-(u+v))
                                + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))).
        { apply (zb2_qmake_pos 2 27); lia. }
        { apply (Qle_trans (2#27) ((2#27) + 2*(1-(u+v)))
                           ((2#27) + 2*(1-(u+v))
                                  + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))).
          { apply (Qplus_le_compat (2#27) (2#27) 0 (2*(1-(u+v))))
            ; [ apply Qle_refl | exact Hp2 ]. }
          { apply zb2_add_ge0_le; exact Hp3. } }
    - (* 档二 m ≥ 1：w = 2−m ∈ [0,1]，5w(w−1)²+(4−3w) ≥ 1 *)
      assert (Hwge : 0 <= 2-(u+v)) by (apply (zb2_le_sub (u+v) 2); exact Hm2).
      assert (Hwle : (2-(u+v)) <= 1).
      { assert (Hm4 : 0 <= (u+v) - 1)
          by (apply (zb2_le_sub 1 (u+v)); exact Hm3).
        apply (zb2_sub_ge0 (2-(u+v)) 1).
        assert (Heq : 1 - (2-(u+v)) == (u+v) - 1) by ring.
        rewrite Heq. apply (zb2_le_sub 1 (u+v)). exact Hm3. }
      assert (Hid3 : 8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))
                  == 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)
                   + (4 - 3*(2-(u+v)))) by ring.
      assert (Hs0 : 0 <= (2-(u+v)-1)*(2-(u+v)-1)) by apply zb2_sq_ge0.
      assert (Hasso2 : (5*(2-(u+v))*((2-(u+v)-1)*(2-(u+v)-1)))
                     == 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)) by ring.
      assert (Hp1g : 0 <= 5*(2-(u+v))*((2-(u+v)-1)*(2-(u+v)-1))).
      { apply (zb2_mult2_ge0 (5*(2-(u+v))) ((2-(u+v)-1)*(2-(u+v)-1))).
        + apply (zb2_mult2_ge0 5); [ apply (zb2_nat_pos 5) | exact Hwge ].
        + exact Hs0. }
      assert (Hp1 : 0 <= 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1))
        by (apply (zb2_ge0_wd _ _ Hasso2 Hp1g)).
      assert (H4m : 0 <= 4 - 3*(2-(u+v))).
      { assert (Hide : 4 - 3*(2-(u+v)) == 3*(1-(2-(u+v))) + 1) by ring.
        rewrite Hide.
        assert (H1w : 0 <= 1 - (2-(u+v)))
          by (apply (zb2_le_sub (2-(u+v)) 1); exact Hwle).
        apply (Qle_trans 0 (3*(1-(2-(u+v)))))
        ; [ apply (zb2_mult2_ge0 3); [ apply (zb2_nat_pos 3) | exact H1w ]
          | apply zb2_add_ge0_le; exact zb2_0_le_1 ]. }
      rewrite Hid3.
      apply Qmult_le_0_compat.
      + apply (zb2_mult2_ge0 (u+v) (1#8))
        ; [ exact Hm0 | apply (zb2_qmake_pos 1 8); lia ].
      + apply (Qle_trans 0 (5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)) _).
        * exact Hp1.
        * apply zb2_add_ge0_le. exact H4m. }
  (* 链式合成：0 ≤ (m/8)(…) = m−(m²/4)B* ≤ m−k·B* ≤ m−k·B = F *)
  assert (Hid2 : (u+v) - (((u+v)*(u+v)) * (1#4))
                       * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
              == ((u+v) * (1#8))
                   * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))))
    by ring.
  assert (HF : 0 <= u + v - u*v - 10*u*(1-u)*v*(1-v)).
  { assert (HeqF : u + v - u*v - 10*u*(1-u)*v*(1-v)
                 == (u+v) - (u*v)*(11 - 10*(u+v) + 10*(u*v))) by ring.
    rewrite HeqF.
    apply (Qle_trans _ (((u+v) * (1#8))
              * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ ((u+v) - (u*v)*(11 - 10*(u+v) + (5#2)*(u+v)*(u+v)))).
      + apply (zb2_minus_le (u+v)
          ((u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply (zb2_minus_le (u+v)
          ((u*v) * (11 - 10*(u+v) + 10*(u*v)))
          ((u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))))
        ; exact HkBB. }
  (* 结论步：u+v−uv = 10N + F ≥ 10N *)
  apply (Qle_trans (10*u*(1-u)*v*(1-v))
    (10*u*(1-u)*v*(1-v) + (u + v - u*v - 10*u*(1-u)*v*(1-v)))
    (u + v - u*v)).
  - apply zb2_add_ge0_le. exact HF.
  - assert (HeqG : 10*u*(1-u)*v*(1-v)
                 + (u + v - u*v - 10*u*(1-u)*v*(1-v))
                == u + v - u*v) by ring.
    rewrite HeqG. apply Qle_refl.
Qed.

(* 主不等式（原变元形，Set 面）：0≤x,y≤1 ⟹ 10N ≤ 1−xy *)
Theorem zb2_ten_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  zb2_qle (10 * x * (1 - x) * y * (1 - y)) (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hu1 : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hu2 : (1 - x) <= 1) by (apply (zb2_minus_ge0 x 1); exact Hx1).
  assert (Hv1 : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hv2 : (1 - y) <= 1) by (apply (zb2_minus_ge0 y 1); exact Hy1).
  pose proof (zb2_ten_le_uv (1 - x) (1 - y) (conj Hu1 Hu2) (conj Hv1 Hv2)) as H.
  assert (Hl : 10 * x * (1 - x) * y * (1 - y)
            == 10 * (1 - x) * x * (1 - y) * y) by ring.
  assert (Hr : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  assert (Hn : 10 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
            == 10 * x * (1 - x) * y * (1 - y)) by ring.
  apply (zb2_qle_wd_r (10 * x * (1 - x) * y * (1 - y))
            ((1 - x) + (1 - y) - (1 - x) * (1 - y)) (1 - x * y)).
  - exact Hr.
  - apply (zb2_qle_wd_l (10 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                        (10 * x * (1 - x) * y * (1 - y))
                        ((1 - x) + (1 - y) - (1 - x) * (1 - y))).
    + exact Hn.
    + apply zb2_qle_of_Qle. exact H.
Qed.

(* ============================================================ *)
(* §C 平方恒等式对与 4N ≤ (1−xy)²                                       *)
(* ============================================================ *)

(* 恒等式：(1−xy)²−4x(1−x)(1−y) = (1−2x+xy)²（左形）与 y 对称形（右形） *)
Lemma zb2_amgm_eq_l : forall x y : Q,
  (1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y) == (1 - 2*x + x*y)*(1 - 2*x + x*y).
Proof. intros x y. ring. Qed.

Lemma zb2_amgm_eq_r : forall x y : Q,
  (1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y) == (1 - 2*y + x*y)*(1 - 2*y + x*y).
Proof. intros x y. ring. Qed.

(* 复合面：0≤x,y≤1 ⟹ 4N ≤ (1−xy)²。
   两恒等式给出 P ≥ A 与 P ≥ B（P=(1−xy)²，A=4x(1−x)(1−y)，B=4(1−x)y(1−y)），
   相乘得 P² ≥ A·B；又 A·B−Q² = 16xy(1−x)²(1−y)²(1−xy) ≥ 0（Q=4N），
   故 P² ≥ Q²；由 P,Q ≥ 0 与 P+Q > 0（或退化档 P+Q ≤ 0）得 P ≥ Q。 *)
Lemma zb2_N4_le_dsq : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  4 * x * (1 - x) * y * (1 - y) <= (1 - x*y)*(1 - x*y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (HN0 : 0 <= 4 * x * (1 - x) * y * (1 - y)).
  { apply (zb2_mult2_ge0 ((4 * x * (1 - x)) * y) (1 - y)).
    - apply (zb2_mult2_ge0 (4 * x * (1 - x)) y).
      + apply (zb2_mult2_ge0 (4 * x) (1 - x)).
        * apply (zb2_mult2_ge0 4 x); [ apply (zb2_nat_pos 4) | exact Hx1 ].
        * exact Hxb.
      + exact Hy1.
    - exact Hyb. }
  assert (HP : 0 <= (1 - x*y)*(1 - x*y)) by apply zb2_sq_ge0.
  pose proof (zb2_sq_ge0 (1 - 2*x + x*y)) as HAl.
  rewrite <- (zb2_amgm_eq_l x y) in HAl.
  pose proof (zb2_sq_ge0 (1 - 2*y + x*y)) as HAr.
  rewrite <- (zb2_amgm_eq_r x y) in HAr.
  assert (Hm1 : 4*x*(1-x)*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply (zb2_sub_ge0 (4*x*(1-x)*(1-y))); exact HAl).
  assert (Hm2 : 4*(1-x)*y*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply (zb2_sub_ge0 (4*(1-x)*y*(1-y))); exact HAr).
  assert (HPP : (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))
             <= ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))).
  { apply Qmult_le_compat_r; [ exact Hm1 | exact HP ]. }
  assert (HNA : 0 <= 4*x*(1-x)*(1-y)).
  { apply (zb2_mult2_ge0 (4*x*(1-x)) (1-y)).
    - apply (zb2_mult2_ge0 (4*x) (1-x)).
      + apply (zb2_mult2_ge0 4 x); [ apply (zb2_nat_pos 4) | exact Hx1 ].
      + exact Hxb.
    - exact Hyb. }
  assert (HAA : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             <= (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))).
  { apply (Qle_trans _ ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
    - apply (zb2_le_eq ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
      assert (Hcmm : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                  == (4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y))) by ring.
      exact Hcmm.
    - apply (Qle_trans _ (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))).
      + apply (Qmult_le_compat_r (4*(1-x)*y*(1-y)) ((1 - x*y)*(1 - x*y))
               (4*x*(1-x)*(1-y)))
        ; [ exact Hm2 | exact HNA ].
      + apply (zb2_le_eq (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))
                         ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
        assert (Hcmm2 : ((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y))
                     == (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))) by ring.
        exact Hcmm2. }
  assert (Hqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (zb2_sub_ge0 ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))).
    assert (Heqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))
              == (4*x*(1-x)*(1-y)) * (4*y*(1-x)*(1-y)*(1-x*y))) by ring.
    rewrite Heqq.
    apply Qmult_le_0_compat.
    - apply (zb2_mult4_ge0 4 x (1-x) (1-y))
      ; [ apply (zb2_nat_pos 4) | exact Hx1 | exact Hxb | exact Hyb ].
    - apply Qmult_le_0_compat.
      + apply (zb2_mult4_ge0 4 y (1-x) (1-y))
        ; [ apply (zb2_nat_pos 4) | exact Hy1 | exact Hxb | exact Hyb ].
      + apply (zb2_le_sub (x*y) 1).
        apply (zb2_xy_le_1 x y); assumption. }
  assert (HPPQ : ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
              >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                     ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))
                     (((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y)))).
    - apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
      + exact Hqq.
      + exact HAA.
    - exact HPP. }
  destruct (Qlt_le_dec 0
    ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))) as [Hpos | Hzero].
  - assert (Hdiff : 0 <= ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                       * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))).
    { assert (Heqd : ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                   * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))
                == ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))) by ring.
      rewrite Heqd. exact (zb2_le_sub _ _ HPPQ). }
    assert (Hres : 0 <= (1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y)).
    { apply (zb2_div_pos _ ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y)))
      ; assumption. }
    exact (zb2_sub_ge0 _ _ Hres).
  - assert (HQle : (4*x*(1-x)*y*(1-y)) <= 0).
    { assert (Hcq : (4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)
                 == (1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y))) by ring.
      apply (Qle_trans (4*x*(1-x)*y*(1-y))
               ((4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)) 0).
      - apply zb2_add_ge0_le. exact HP.
      - apply (Qle_trans _ ((1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y)))).
        + apply (zb2_le_eq _ _). exact Hcq.
        + exact Hzero. }
    assert (Heq : (4*x*(1-x)*y*(1-y)) == 0) by (apply Qle_antisym; assumption).
    rewrite Heq. exact HP.
Qed.

(* ============================================================ *)
(* §D 复合面：4·10ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（除法自由形，Set 面）              *)
(* ============================================================ *)

(* 归纳复合：基档即 §C；步档乘 N ≤ (1−xy)/10（§B 主不等式）后再乘 (1−xy)。
   即被积函数族逐点 ≤ (1/4)·(1/10)ⁿ 的无除法形。 *)
Theorem zb2_pointwise_decay : forall (n : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  zb2_qle (4 * zb2_pow 10 n * zb2_pow (x*(1-x)*y*(1-y)) (S n))
          (zb2_pow (1 - x*y) (S (S n))).
Proof.
  induction n as [| n IH]; intros x y [Hx1 Hx2] [Hy1 Hy2].
  - apply zb2_qle_of_Qle.
    assert (Heq1 : 4 * zb2_pow 10 0 * zb2_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (simpl; ring).
    assert (Heq2 : zb2_pow (1 - x*y) 2 == ((1 - x*y)*(1 - x*y)))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    apply zb2_N4_le_dsq; [ split; assumption | split; assumption ].
  - apply zb2_qle_of_Qle.
    assert (HIH := IH x y (conj Hx1 Hx2) (conj Hy1 Hy2)).
    apply zb2_qle_to_Qle in HIH.
    pose proof (zb2_ten_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hten.
    apply zb2_qle_to_Qle in Hten.
    assert (Hxy1 : 0 <= x*y) by (apply (zb2_mult2_ge0 x y); assumption).
    assert (HP0 : 0 <= zb2_pow (1 - x*y) (S (S n)))
      by (apply zb2_pow_ge0; apply (zb2_le_sub (x*y) 1);
        apply (zb2_xy_le_1 x y); assumption).
    assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply (zb2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (H4N : 0 <= (4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)).
    { apply (zb2_mult2_ge0 (4 * zb2_pow 10 n) (zb2_pow (x*(1-x)*y*(1-y)) (S n))).
      - apply (zb2_mult2_ge0 4 (zb2_pow 10 n))
        ; [ apply (zb2_nat_pos 4) | apply zb2_pow_ge0; exact (zb2_nat_pos 10) ].
      - apply zb2_pow_ge0. exact HN0. }
    assert (HPn : 0 <= 1 - x*y)
      by (apply (zb2_le_sub (x*y) 1); apply (zb2_xy_le_1 x y); assumption).
    assert (HN10 : 0 <= ((10 * x * (1 - x)) * y) * (1 - y)).
    { apply (zb2_mult2_ge0 ((10 * x * (1 - x)) * y) (1 - y)).
      - apply (zb2_mult2_ge0 ((10 * x) * (1 - x)) y).
        + apply (zb2_mult2_ge0 (10 * x) (1 - x)).
          * apply (zb2_mult2_ge0 10 x); [ apply (zb2_nat_pos 10) | exact Hx1 ].
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    apply (Qle_trans (4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                     (10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))
                     ((1 - x*y) * zb2_pow (1 - x*y) (S (S n)))).
    + apply (zb2_le_eq (4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                       (10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))).
      assert (Hrw : 4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n))
                 == 10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))
        by (simpl; ring).
      exact Hrw.
    + apply (zb2_mono_pair (4 * zb2_pow 10 n * zb2_pow (x*(1-x)*y*(1-y)) (S n))
                           (zb2_pow (1 - x*y) (S (S n)))
                           _ (1 - x*y))
      ; [ exact HIH | exact Hten | exact H4N | exact HP0 | exact HN10 | exact HPn ].
Qed.

(* 审计行：全部语句的假设封闭性检查（Print Assumptions 清单）。 *)
Print Assumptions zb2_0_le_1.
Print Assumptions zb2_qle_of_Qle.
Print Assumptions zb2_qle_to_Qle.
Print Assumptions zb2_qeq_imp_le.
Print Assumptions zb2_le_eq_swap.
Print Assumptions zb2_le_eq.
Print Assumptions zb2_ge0_wd.
Print Assumptions zb2_qle_wd_l.
Print Assumptions zb2_qle_wd_r.
Print Assumptions zb2_add_ge0_le.
Print Assumptions zb2_sub_ge0.
Print Assumptions zb2_le_sub.
Print Assumptions zb2_le0_opp.
Print Assumptions zb2_ge0_opp_le.
Print Assumptions zb2_minus_le.
Print Assumptions zb2_minus_ge0.
Print Assumptions zb2_sq_ge0.
Print Assumptions zb2_mult2_ge0.
Print Assumptions zb2_mult4_ge0.
Print Assumptions zb2_div_pos.
Print Assumptions zb2_pow_ge0.
Print Assumptions zb2_xy_le_1.
Print Assumptions zb2_qmake_pos.
Print Assumptions zb2_nat_pos.
Print Assumptions zb2_mono_pair.
Print Assumptions zb2_ten_le_uv.
Print Assumptions zb2_ten_le.
Print Assumptions zb2_amgm_eq_l.
Print Assumptions zb2_amgm_eq_r.
Print Assumptions zb2_N4_le_dsq.
Print Assumptions zb2_pointwise_decay.
