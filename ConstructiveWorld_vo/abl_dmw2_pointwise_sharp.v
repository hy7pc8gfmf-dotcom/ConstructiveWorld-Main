(* ===================================================================== *)
(*  abl_dmw2_pointwise_sharp.v —— ζ(2) 第四塔·逐点控制面锐化重铸            *)
(*  模块名：abl_dmw2_pointwise_sharp。                                    *)
(*  使命：将 Beukers 1979 ζ(2) 二重积分被积族 N := x(1−x)y(1−y) 的         *)
(*        逐点线性控制常数自 10（θ=1/10）锐化至 11（θ=1/11≈0.0909，        *)
(*        逼近真最优 ((√5−1)/2)⁵ ≈ 0.09017）。证得：                      *)
(*        ① 锐化主不等式 11N ≤ 1−xy（换元 u=1−x, v=1−y 后经 m=u+v, k=uv    *)
(*        化为 F = m−k(12−11m+11k) 与单变元末式 (m/16)·H(m)，              *)
(*        H(m)=16−48m+44m²−11m³ = 16−4m−11m(2−m)²；分档收束：              *)
(*        m ≤ 4/5 档 z=4/5−m 化 H = 16/125−(32/25)z+(88/5)z²+11z³，        *)
(*        弃 11z³≥0 后二次式 = (8/125)(275(z−2/55)²+18/11) > 0；           *)
(*        m ≥ 4/5 档 s=m−4/5∈[0,6/5] 化 H = 16/125+s(32/25+11s(8/5−s))     *)
(*        ≥ 16/125 > 0；                                                  *)
(*        ② 平方恒等式对 4N ≤ (1−xy)²（与 abl_z2_pointwise 同构重铸）；     *)
(*        ③ 复合面 4·11ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（Set 面），即被积函数族逐点       *)
(*        不超过 (1/4)·(1/11)ⁿ。                                          *)
(*  量化距离注记（如实申报）：族界供下游竞争判定                          *)
(*        (9/4)(9/11)^m < 1 于 m ≥ 5（源面 1/10 档为 m ≥ 8）；库隐含        *)
(*        测度档 μ_lib 自 ≈21.85 降至 ≈11.95，真最优档极限 ≈11.52；         *)
(*        Rhin–Viola 型界本体＝组结构置换群双积分法（其面尚未建库），       *)
(*        本件为该方向逐点层前置锐化，不作「首例/更强于」表述。            *)
(*  依赖：仅 Stdlib QArith/ZArith/Arith/Lia。有理域线性放缩以显式引理链     *)
(*        组合，非线性末式以显式平方分解收束；未引入实数、未引入经典逻辑。   *)
(*  对标：Beukers 1979（Bull. London Math. Soc. 11）逐点估计步常数锐化；    *)
(*        Rhin–Viola 组结构法（在册经典）。                               *)
(*  构造性：纯构造性、零假设声明、零承认词面；主语句全 Set 面（dmw2_qle）。 *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no 本件      *)
(*        （零栈依赖；-Q 缓存根仅备下游件使用）。                          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 Set 层承载自立：恒等型 dmw2_id 与序见证 dmw2_qle                  *)
(* ============================================================ *)

Inductive dmw2_id (A : Set) (x : A) : A -> Set :=
  dmw2_idrefl : dmw2_id A x x.

Definition dmw2_qle (x y : Q) : Set := dmw2_id bool (Qle_bool x y) true.

Lemma dmw2_0_le_1 : (0 <= 1)%Q.
Proof. exact (proj1 (Qle_bool_iff 0 1) eq_refl). Qed.

Lemma dmw2_qle_of_Qle : forall x y : Q, x <= y -> dmw2_qle x y.
Proof.
  intros x y H.
  assert (Hb : Qle_bool x y = true) by exact (proj2 (Qle_bool_iff x y) H).
  unfold dmw2_qle. rewrite Hb. apply dmw2_idrefl.
Qed.

Lemma dmw2_qle_to_Qle : forall x y : Q, dmw2_qle x y -> x <= y.
Proof.
  intros x y H. apply (proj1 (Qle_bool_iff x y)).
  destruct H. reflexivity.
Qed.

Lemma dmw2_qeq_imp_le : forall x y : Q, x == y -> y <= x.
Proof.
  intros x y Hxy. unfold Qle. unfold Qeq in Hxy.
  rewrite Hxy. apply Z.le_refl.
Qed.

Lemma dmw2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> a <= b.
Proof.
  intros a b Hab Ha.
  apply (dmw2_qeq_imp_le b a).
  apply Qeq_sym. exact Hab.
Qed.

Lemma dmw2_le_eq : forall a b : Q, a == b -> a <= b.
Proof.
  intros a b Hab.
  apply (dmw2_qeq_imp_le b a). apply Qeq_sym. exact Hab.
Qed.

Lemma dmw2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> 0 <= b.
Proof.
  intros a b Hab Ha.
  apply (Qle_trans 0 a b).
  - exact Ha.
  - apply (dmw2_le_eq_swap a b); assumption.
Qed.

Lemma dmw2_qle_wd_l : forall x y z : Q, x == y -> dmw2_qle x z -> dmw2_qle y z.
Proof.
  intros x y z Hxy Hxz. apply dmw2_qle_of_Qle.
  apply (Qle_trans y x z)
  ; [ apply dmw2_qeq_imp_le; exact Hxy
    | apply dmw2_qle_to_Qle; exact Hxz ].
Qed.

Lemma dmw2_qle_wd_r : forall x y z : Q, y == z -> dmw2_qle x y -> dmw2_qle x z.
Proof.
  intros x y z Hyz Hxy. apply dmw2_qle_of_Qle.
  apply (Qle_trans x y z)
  ; [ apply dmw2_qle_to_Qle; exact Hxy
    | apply (dmw2_qeq_imp_le z y); apply Qeq_sym; exact Hyz ].
Qed.

(* ============================================================ *)
(* §A 线性放缩原子库（全引理链，无自动化）                              *)
(* ============================================================ *)

Lemma dmw2_add_ge0_le : forall a b : Q, 0 <= b -> a <= a + b.
Proof.
  intros a b H.
  apply (Qle_trans a (a + 0) (a + b)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat a a 0 b); [ apply Qle_refl | exact H ].
Qed.

Lemma dmw2_sub_ge0 : forall a b : Q, 0 <= b - a -> a <= b.
Proof.
  intros a b H. apply (Qle_trans a (a + (b - a)) b).
  - apply dmw2_add_ge0_le. exact H.
  - assert (Heq : a + (b - a) == b) by ring.
    rewrite Heq. apply Qle_refl.
Qed.

Lemma dmw2_le_sub : forall a b : Q, a <= b -> 0 <= b - a.
Proof.
  intros a b H.
  assert (H1 : a + (- a) <= b + (- a))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : a + (- a) == 0) by ring.
  assert (Heq2 : b + (- a) == b - a) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

Lemma dmw2_minus_ge0 : forall t c : Q, 0 <= t -> c - t <= c.
Proof.
  intros t c H. apply (dmw2_sub_ge0 (c - t) c).
  assert (Heq : c - (c - t) == t) by ring.
  rewrite Heq. exact H.
Qed.

Lemma dmw2_le0_opp : forall s : Q, s <= 0 -> 0 <= - s.
Proof.
  intros s H.
  assert (H1 : s + (- s) <= 0 + (- s))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : s + (- s) == 0) by ring.
  assert (Heq2 : 0 + (- s) == - s) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

Lemma dmw2_minus_le : forall p q r : Q, q <= r -> p - r <= p - q.
Proof.
  intros p q r H. apply (dmw2_sub_ge0 (p - r) (p - q)).
  assert (Heq : (p - q) - (p - r) == r - q) by ring.
  rewrite Heq. apply (dmw2_le_sub q r). exact H.
Qed.

Lemma dmw2_sq_ge0 : forall s : Q, 0 <= s * s.
Proof.
  intro s. destruct (Qlt_le_dec 0 s) as [Hlt | Hle].
  - apply Qmult_le_0_compat
    ; [ apply Qlt_le_weak; exact Hlt | apply Qlt_le_weak; exact Hlt ].
  - assert (Hn : 0 <= - s) by (apply dmw2_le0_opp; exact Hle).
    assert (Heq : s * s == (- s) * (- s)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact Hn.
Qed.

Lemma dmw2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof. intros a b Ha Hb. apply Qmult_le_0_compat; assumption. Qed.

Lemma dmw2_mult4_ge0 : forall a b c d : Q,
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= ((a * b) * c) * d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat; assumption.
    + exact Hc.
  - exact Hd.
Qed.

Lemma dmw2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> 0 <= a.
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

Fixpoint dmw2_pow (t : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | S k' => t * dmw2_pow t k'
  end.

Lemma dmw2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> 0 <= dmw2_pow t k.
Proof.
  intros t k Ht. induction k as [| k' IH].
  - simpl. exact dmw2_0_le_1.
  - simpl. apply Qmult_le_0_compat; [ exact Ht | exact IH ].
Qed.

Lemma dmw2_xy_le_1 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> x * y <= 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  apply (Qle_trans (x * y) (1 * 1) 1).
  - apply (Qmult_le_compat_nonneg x 1 y 1)
    ; [ split; assumption | split; assumption ].
  - assert (Heq : 1 * 1 == 1) by ring.
    rewrite Heq. apply Qle_refl.
Qed.

Lemma dmw2_qmake_pos : forall (a : Z) (b : positive),
  (0 <= a)%Z -> 0 <= (a # b)%Q.
Proof.
  intros a b Ha.
  unfold Qle. simpl. lia.
Qed.

Lemma dmw2_nat_pos : forall n : nat, 0 <= (Z.of_nat n # 1)%Q.
Proof.
  intro n. apply (proj1 (Qle_bool_iff 0 (Z.of_nat n # 1))).
  destruct n as [| n']; reflexivity.
Qed.

Lemma dmw2_mono_pair : forall a b c d : Q,
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
(* §B 锐化主不等式：11N ≤ 1−xy                                          *)
(* ============================================================ *)

(* 锐化主不等式（换元形）：0≤u,v≤1 ⟹ 11·u(1−u)v(1−v) ≤ u+v−uv。
   证书链（m := u+v, k := uv；F := m − k(12−11m+11k)）：
   F ≥ m − k(12−11m+(11/4)m²) ≥ m − (m²/4)(12−11m+(11/4)m²)
     = (m/16)·H(m) ≥ 0，
   其中 B* = 12−11m+(11/4)m² = 1+(11/4)(m−2)² ≥ 1（正定·判别式 −11），
   H(m) = 16−48m+44m²−11m³ = 16−4m−11m(2−m)²，分档：
   m ≤ 4/5 档：z := 4/5−m，H = 16/125−(32/25)z+(88/5)z²+11z³，
     弃 11z³ ≥ 0，二次式 = (8/125)(275(z−2/55)²+18/11) ≥ 144/1375 > 0；
   m ≥ 4/5 档：s := m−4/5 ∈ [0,6/5]，H = 16/125+s(32/25+11s(8/5−s))，
     括号 ≥ 32/25 > 0（s ≤ 6/5 < 8/5），故 H ≥ 16/125 > 0。 *)
Lemma dmw2_eleven_le_uv : forall u v : Q,
  0 <= u <= 1 -> 0 <= v <= 1 ->
  11 * u * (1 - u) * v * (1 - v) <= u + v - u * v.
Proof.
  intros u v [Hu1 Hu2] [Hv1 Hv2].
  assert (Hk0 : 0 <= u * v) by (apply dmw2_mult2_ge0; assumption).
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
    rewrite Heq. apply dmw2_sq_ge0. }
  (* 由 H4k 线性导出：11k ≤ (11/4)m² 与 k ≤ m²/4 *)
  assert (HBB : 11 * (u*v) <= (11#4)*(u+v)*(u+v)).
  { apply (Qle_trans (11 * (u*v))
      (11 * (u*v) + (11#4) * ((u+v)*(u+v) - 4*(u*v)))
      ((11#4)*(u+v)*(u+v))).
    - apply dmw2_add_ge0_le.
      apply (dmw2_mult2_ge0 (11#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (dmw2_qmake_pos 11 4); lia | exact H4k ].
    - assert (Heq : 11 * (u*v) + (11#4) * ((u+v)*(u+v) - 4*(u*v))
                 == (11#4)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply dmw2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply (dmw2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (dmw2_qmake_pos 1 4); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
  (* 因子界：B* = 12−11m+(11/4)m² = 1+(11/4)(m−2)² ≥ 1 > 0 *)
  assert (HBp : 0 <= 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)).
  { assert (Hid0 : 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)
                == (11#4)*((2-(u+v))*(2-(u+v))) + 1) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v))) by apply dmw2_sq_ge0.
    assert (HX : 0 <= (11#4)*((2-(u+v))*(2-(u+v)))).
    { apply (dmw2_mult2_ge0 (11#4) ((2-(u+v))*(2-(u+v))))
      ; [ apply (dmw2_qmake_pos 11 4); lia | exact Hs ]. }
    apply (Qle_trans 0 ((11#4)*((2-(u+v))*(2-(u+v))))
                      ((11#4)*((2-(u+v))*(2-(u+v))) + 1)).
    - exact HX.
    - apply dmw2_add_ge0_le. exact dmw2_0_le_1. }
  assert (HBs : 12 - 11*(u+v) + 11*(u*v)
             <= 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (12 - 11*(u+v)) (12 - 11*(u+v))
             (11*(u*v)) ((11#4)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
  (* 步一：k·B ≤ k·B* *)
  assert (HkBB : (u*v) * (12 - 11*(u+v) + 11*(u*v))
              <= (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (12 - 11*(u+v) + 11*(u*v))
                  (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (12 - 11*(u+v) + 11*(u*v))
                == (12 - 11*(u+v) + 11*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
                == (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
  (* 步二：k·B* ≤ (m²/4)·B* *)
  assert (HkB2 : (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
  (* 单变元末式非负（分档 m ≤ 4/5 ／ m ≥ 4/5） *)
  assert (Hlow : 0 <= ((u+v) * (1#16))
                   * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v))).
  { destruct (Qlt_le_dec (u+v) (4#5)) as [Hm45 | Hm45].
    - (* 档一 m ≤ 4/5：z = 4/5−m，H = 16/125−(32/25)z+(88/5)z²+11z³ *)
      assert (Hz0 : 0 <= (4#5) - (u+v))
        by (apply (dmw2_le_sub (u+v) (4#5)); exact (Qlt_le_weak _ _ Hm45)).
      assert (HidB : 16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)
                  == (16#125) - (32#25)*((4#5)-(u+v))
                     + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                     + 11*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v))))
        by ring.
      assert (Hcube0 : 0 <= (((4#5)-(u+v))*((4#5)-(u+v)))*((4#5)-(u+v))).
      { apply Qmult_le_0_compat.
        - apply dmw2_sq_ge0.
        - exact Hz0. }
      assert (Hcube : 0 <= 11*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v)))).
      { apply (dmw2_mult2_ge0 11); [ apply (dmw2_nat_pos 11) | exact Hcube0 ]. }
      assert (Hsq : 0 <= (((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55)))
        by apply dmw2_sq_ge0.
      assert (Hin : 0 <= (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))).
      { assert (Hasso : (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))
                     == (275)*((((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))))
          by ring.
        rewrite Hasso.
        apply (dmw2_mult2_ge0 (275) ((((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))))
        ; [ apply (dmw2_nat_pos 275) | exact Hsq ]. }
      assert (Hin2 : 0 <= (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))
                          + (18#11)).
      { apply (Qle_trans 0
                 ((275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))) _).
        - exact Hin.
        - apply (dmw2_add_ge0_le
                   ((275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55)))
                   (18#11)).
          apply (dmw2_qmake_pos 18 11); lia. }
      assert (Hquad : 0 <= (16#125) - (32#25)*((4#5)-(u+v))
                           + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))).
      { assert (Hsos : (16#125) - (32#25)*((4#5)-(u+v))
                           + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                    == (8#125)*((275)*(((4#5)-(u+v))-(2#55))
                                          *(((4#5)-(u+v))-(2#55)) + (18#11)))
          by ring.
        rewrite Hsos.
        apply Qmult_le_0_compat.
        - apply (dmw2_qmake_pos 8 125); lia.
        - exact Hin2. }
      assert (HH : 0 <= 16 - 48*(u+v) + 44*(u+v)*(u+v)
                        - 11*(u+v)*(u+v)*(u+v)).
      { rewrite HidB.
        apply (Qle_trans _ ((16#125) - (32#25)*((4#5)-(u+v))
                 + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v))))).
        - exact Hquad.
        - apply dmw2_add_ge0_le. exact Hcube. }
      apply Qmult_le_0_compat.
      + apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH.
    - (* 档二 m ≥ 4/5：s = m−4/5 ∈ [0,6/5]，
         H = 16/125 + s(32/25 + 11s(8/5−s)) ≥ 16/125 > 0 *)
      assert (Hs0 : 0 <= (u+v) - (4#5))
        by (apply (dmw2_le_sub (4#5) (u+v)); exact Hm45).
      assert (Hs2 : (u+v) - (4#5) <= (6#5)).
      { apply (dmw2_sub_ge0 ((u+v)-(4#5)) (6#5)).
        assert (Heq : (6#5) - ((u+v)-(4#5)) == 2 - (u+v)) by ring.
        rewrite Heq. apply (dmw2_le_sub (u+v) 2). exact Hm2. }
      assert (Hs8 : (u+v) - (4#5) <= (8#5))
        by (apply (Qle_trans _ (6#5)); [ exact Hs2
          | unfold Qle; simpl; lia ]).
      assert (Hbr : 0 <= (8#5) - ((u+v)-(4#5)))
        by (apply (dmw2_le_sub ((u+v)-(4#5)) (8#5)); exact Hs8).
      assert (Hbrk : 0 <= (32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))).
      { apply (Qle_trans 0 (32#25) _).
        - apply (dmw2_qmake_pos 32 25); lia.
        - apply dmw2_add_ge0_le.
          assert (Hasso : 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))
                       == 11*(((u+v)-(4#5))*((8#5)-((u+v)-(4#5))))) by ring.
          rewrite Hasso.
          apply (dmw2_mult2_ge0 11).
          + apply (dmw2_nat_pos 11).
          + apply (dmw2_mult2_ge0 ((u+v)-(4#5)) ((8#5)-((u+v)-(4#5))))
            ; [ exact Hs0 | exact Hbr ]. }
      assert (HidA : 16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)
                  == (16#125) + ((u+v)-(4#5))
                       *((32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))))
        by ring.
      assert (Hterm : 0 <= ((u+v)-(4#5))
                       *((32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5))))).
      { apply (dmw2_mult2_ge0 ((u+v)-(4#5)))
        ; [ exact Hs0 | exact Hbrk ]. }
      assert (HH : 0 <= 16 - 48*(u+v) + 44*(u+v)*(u+v)
                        - 11*(u+v)*(u+v)*(u+v)).
      { rewrite HidA.
        apply (Qle_trans 0 (16#125) _).
        - apply (dmw2_qmake_pos 16 125); lia.
        - apply dmw2_add_ge0_le. exact Hterm. }
      apply Qmult_le_0_compat.
      + apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH. }
  (* 链式合成：0 ≤ (m/16)H = m−(m²/4)B* ≤ m−k·B* ≤ m−k·B = F *)
  assert (Hid2 : (u+v) - (((u+v)*(u+v)) * (1#4))
                       * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
              == ((u+v) * (1#16))
                   * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)))
    by ring.
  assert (HF : 0 <= u + v - u*v - 11*u*(1-u)*v*(1-v)).
  { assert (HeqF : u + v - u*v - 11*u*(1-u)*v*(1-v)
                == (u+v) - (u*v)*(12 - 11*(u+v) + 11*(u*v))) by ring.
    rewrite HeqF.
    apply (Qle_trans _ (((u+v) * (1#16))
              * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ ((u+v) - (u*v)*(12 - 11*(u+v) + (11#4)*(u+v)*(u+v)))).
      + apply (dmw2_minus_le (u+v)
          ((u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply (dmw2_minus_le (u+v)
          ((u*v) * (12 - 11*(u+v) + 11*(u*v)))
          ((u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))))
        ; exact HkBB. }
  (* 结论：u+v−uv = 11N + F ≥ 11N *)
  apply (Qle_trans (11*u*(1-u)*v*(1-v))
    (11*u*(1-u)*v*(1-v) + (u + v - u*v - 11*u*(1-u)*v*(1-v)))
    (u + v - u*v)).
  - apply dmw2_add_ge0_le. exact HF.
  - assert (HeqG : 11*u*(1-u)*v*(1-v)
                 + (u + v - u*v - 11*u*(1-u)*v*(1-v))
                == u + v - u*v) by ring.
    rewrite HeqG. apply Qle_refl.
Qed.

(* 锐化主不等式（原变元形，Set 面）：0≤x,y≤1 ⟹ 11N ≤ 1−xy *)
Theorem dmw2_eleven_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  dmw2_qle (11 * x * (1 - x) * y * (1 - y)) (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hu1 : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hu2 : (1 - x) <= 1) by (apply (dmw2_minus_ge0 x 1); exact Hx1).
  assert (Hv1 : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hv2 : (1 - y) <= 1) by (apply (dmw2_minus_ge0 y 1); exact Hy1).
  pose proof (dmw2_eleven_le_uv (1 - x) (1 - y) (conj Hu1 Hu2) (conj Hv1 Hv2)) as H.
  assert (Hl : 11 * x * (1 - x) * y * (1 - y)
            == 11 * (1 - x) * x * (1 - y) * y) by ring.
  assert (Hr : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  assert (Hn : 11 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
            == 11 * x * (1 - x) * y * (1 - y)) by ring.
  apply (dmw2_qle_wd_r (11 * x * (1 - x) * y * (1 - y))
            ((1 - x) + (1 - y) - (1 - x) * (1 - y)) (1 - x * y)).
  - exact Hr.
  - apply (dmw2_qle_wd_l (11 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                        (11 * x * (1 - x) * y * (1 - y))
                        ((1 - x) + (1 - y) - (1 - x) * (1 - y))).
    + exact Hn.
    + apply dmw2_qle_of_Qle. exact H.
Qed.

(* 数值锚一：u = v = 1/2 档 11N = 11/16 *)
Lemma dmw2_anchor_main_uv :
  11 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)) == (11#16).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §C 平方恒等式对与 4N ≤ (1−xy)²（常数无关·与源面同构重铸）              *)
(* ============================================================ *)

Lemma dmw2_amgm_eq_l : forall x y : Q,
  (1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y) == (1 - 2*x + x*y)*(1 - 2*x + x*y).
Proof. intros x y. ring. Qed.

Lemma dmw2_amgm_eq_r : forall x y : Q,
  (1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y) == (1 - 2*y + x*y)*(1 - 2*y + x*y).
Proof. intros x y. ring. Qed.

(* 复合面：0≤x,y≤1 ⟹ 4N ≤ (1−xy)²。
   两恒等式给出 P ≥ A 与 P ≥ B（P=(1−xy)²，A=4x(1−x)(1−y)，B=4(1−x)y(1−y)），
   相乘得 P² ≥ A·B；又 A·B−Q² = 16xy(1−x)²(1−y)²(1−xy) ≥ 0（Q=4N），
   故 P² ≥ Q²；由 P,Q ≥ 0 与 P+Q > 0（或退化档 P+Q ≤ 0）得 P ≥ Q。 *)
Lemma dmw2_N4_le_dsq : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  4 * x * (1 - x) * y * (1 - y) <= (1 - x*y)*(1 - x*y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (HN0 : 0 <= 4 * x * (1 - x) * y * (1 - y)).
  { apply (dmw2_mult2_ge0 ((4 * x * (1 - x)) * y) (1 - y)).
    - apply (dmw2_mult2_ge0 (4 * x * (1 - x)) y).
      + apply (dmw2_mult2_ge0 (4 * x) (1 - x)).
        * apply (dmw2_mult2_ge0 4 x); [ apply (dmw2_nat_pos 4) | exact Hx1 ].
        * exact Hxb.
      + exact Hy1.
    - exact Hyb. }
  assert (HP : 0 <= (1 - x*y)*(1 - x*y)) by apply dmw2_sq_ge0.
  pose proof (dmw2_sq_ge0 (1 - 2*x + x*y)) as HAl.
  rewrite <- (dmw2_amgm_eq_l x y) in HAl.
  pose proof (dmw2_sq_ge0 (1 - 2*y + x*y)) as HAr.
  rewrite <- (dmw2_amgm_eq_r x y) in HAr.
  assert (Hm1 : 4*x*(1-x)*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply (dmw2_sub_ge0 (4*x*(1-x)*(1-y))); exact HAl).
  assert (Hm2 : 4*(1-x)*y*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply (dmw2_sub_ge0 (4*(1-x)*y*(1-y))); exact HAr).
  assert (HPP : (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))
             <= ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))).
  { apply Qmult_le_compat_r; [ exact Hm1 | exact HP ]. }
  assert (HNA : 0 <= 4*x*(1-x)*(1-y)).
  { apply (dmw2_mult2_ge0 (4*x*(1-x)) (1-y)).
    - apply (dmw2_mult2_ge0 (4*x) (1-x)).
      + apply (dmw2_mult2_ge0 4 x); [ apply (dmw2_nat_pos 4) | exact Hx1 ].
      + exact Hxb.
    - exact Hyb. }
  assert (HAA : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             <= (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))).
  { apply (Qle_trans _ ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
    - apply (dmw2_le_eq ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
      assert (Hcmm : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                  == (4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y))) by ring.
      exact Hcmm.
    - apply (Qle_trans _ (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))).
      + apply (Qmult_le_compat_r (4*(1-x)*y*(1-y)) ((1 - x*y)*(1 - x*y))
               (4*x*(1-x)*(1-y)))
        ; [ exact Hm2 | exact HNA ].
      + apply (dmw2_le_eq (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))
                         ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
        assert (Hcmm2 : ((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y))
                     == (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))) by ring.
        exact Hcmm2. }
  assert (Hqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (dmw2_sub_ge0 ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))).
    assert (Heqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))
              == (4*x*(1-x)*(1-y)) * (4*y*(1-x)*(1-y)*(1-x*y))) by ring.
    rewrite Heqq.
    apply Qmult_le_0_compat.
    - apply (dmw2_mult4_ge0 4 x (1-x) (1-y))
      ; [ apply (dmw2_nat_pos 4) | exact Hx1 | exact Hxb | exact Hyb ].
    - apply Qmult_le_0_compat.
      + apply (dmw2_mult4_ge0 4 y (1-x) (1-y))
        ; [ apply (dmw2_nat_pos 4) | exact Hy1 | exact Hxb | exact Hyb ].
      + apply (dmw2_le_sub (x*y) 1).
        apply (dmw2_xy_le_1 x y); assumption. }
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
      rewrite Heqd. exact (dmw2_le_sub _ _ HPPQ). }
    assert (Hres : 0 <= (1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y)).
    { apply (dmw2_div_pos _ ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y)))
      ; assumption. }
    exact (dmw2_sub_ge0 _ _ Hres).
  - assert (HQle : (4*x*(1-x)*y*(1-y)) <= 0).
    { assert (Hcq : (4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)
                 == (1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y))) by ring.
      apply (Qle_trans (4*x*(1-x)*y*(1-y))
               ((4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)) 0).
      - apply dmw2_add_ge0_le. exact HP.
      - apply (Qle_trans _ ((1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y)))).
        + apply (dmw2_le_eq _ _). exact Hcq.
        + exact Hzero. }
    assert (Heq : (4*x*(1-x)*y*(1-y)) == 0) by (apply Qle_antisym; assumption).
    rewrite Heq. exact HP.
Qed.

(* ============================================================ *)
(* §D 复合面：4·11ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（除法自由形，Set 面）               *)
(* ============================================================ *)

(* 归纳复合：基档即 §C；步档乘 N ≤ (1−xy)/11（§B 锐化主不等式）后再乘 (1−xy)。
   即被积函数族逐点 ≤ (1/4)·(1/11)ⁿ 的无除法形（源面 1/10 档的锐化重铸）。 *)
Theorem dmw2_pointwise_decay : forall (n : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  dmw2_qle (4 * dmw2_pow 11 n * dmw2_pow (x*(1-x)*y*(1-y)) (S n))
          (dmw2_pow (1 - x*y) (S (S n))).
Proof.
  induction n as [| n IH]; intros x y [Hx1 Hx2] [Hy1 Hy2].
  - apply dmw2_qle_of_Qle.
    assert (Heq1 : 4 * dmw2_pow 11 0 * dmw2_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (simpl; ring).
    assert (Heq2 : dmw2_pow (1 - x*y) 2 == ((1 - x*y)*(1 - x*y)))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    apply dmw2_N4_le_dsq; [ split; assumption | split; assumption ].
  - apply dmw2_qle_of_Qle.
    assert (HIH := IH x y (conj Hx1 Hx2) (conj Hy1 Hy2)).
    apply dmw2_qle_to_Qle in HIH.
    pose proof (dmw2_eleven_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hten.
    apply dmw2_qle_to_Qle in Hten.
    assert (Hxy1 : 0 <= x*y) by (apply dmw2_mult2_ge0; assumption).
    assert (HP0 : 0 <= dmw2_pow (1 - x*y) (S (S n)))
      by (apply dmw2_pow_ge0; apply (dmw2_le_sub (x*y) 1);
        apply (dmw2_xy_le_1 x y); assumption).
    assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply (dmw2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (H4N : 0 <= (4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (S n)).
    { apply (dmw2_mult2_ge0 (4 * dmw2_pow 11 n) (dmw2_pow (x*(1-x)*y*(1-y)) (S n))).
      - apply (dmw2_mult2_ge0 4 (dmw2_pow 11 n))
        ; [ apply (dmw2_nat_pos 4) | apply dmw2_pow_ge0; exact (dmw2_nat_pos 11) ].
      - apply dmw2_pow_ge0. exact HN0. }
    assert (HPn : 0 <= 1 - x*y)
      by (apply (dmw2_le_sub (x*y) 1); apply (dmw2_xy_le_1 x y); assumption).
    assert (HN11 : 0 <= ((11 * x * (1 - x)) * y) * (1 - y)).
    { apply (dmw2_mult2_ge0 ((11 * x * (1 - x)) * y) (1 - y)).
      - apply (dmw2_mult2_ge0 ((11 * x) * (1 - x)) y).
        + apply (dmw2_mult2_ge0 (11 * x) (1 - x)).
          * apply (dmw2_mult2_ge0 11 x); [ apply (dmw2_nat_pos 11) | exact Hx1 ].
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    apply (Qle_trans (4 * dmw2_pow 11 (S n) * dmw2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                     (11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (S n)))
                     ((1 - x*y) * dmw2_pow (1 - x*y) (S (S n)))).
    + apply (dmw2_le_eq (4 * dmw2_pow 11 (S n) * dmw2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                       (11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (S n)))).
      assert (Hrw : 4 * dmw2_pow 11 (S n) * dmw2_pow (x*(1-x)*y*(1-y)) (S (S n))
                 == 11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (S n)))
        by (simpl; ring).
      exact Hrw.
    + apply (dmw2_mono_pair (4 * dmw2_pow 11 n * dmw2_pow (x*(1-x)*y*(1-y)) (S n))
                           (dmw2_pow (1 - x*y) (S (S n)))
                           _ (1 - x*y))
      ; [ exact HIH | exact Hten | exact H4N | exact HP0 | exact HN11 | exact HPn ].
Qed.

(* 数值锚二：n=1、x=y=1/2 档复合左端 4·11·N² = 44/256 *)
Lemma dmw2_anchor_decay_n1 :
  4 * dmw2_pow 11 1 * dmw2_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2 == (44#256).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §E 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions dmw2_eleven_le_uv.
Print Assumptions dmw2_eleven_le.
Print Assumptions dmw2_N4_le_dsq.
Print Assumptions dmw2_pointwise_decay.
Print Assumptions dmw2_anchor_main_uv.
Print Assumptions dmw2_anchor_decay_n1.
