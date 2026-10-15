(* ===================================================================== *)
(*  d519a2_cert.v —— 1/14 精确逐点证书 Coq 化 born-in place（DM-519A2）      *)
(*  模块名：d519a2_cert。                                                  *)
(*  使命：承 519A 计算实验判定（_mirror_519a.py §3.4·30 PASS/EXIT=0 在卷），  *)
(*        铸【56N ≤ 3+s−2p 逐点改进证书】——θ(3)=1/14 精确档（Ψ₃=3+s−2p      *)
(*        纯轨道正组合·σ=7/8·非循环），GCL 1/12 档（gcl_sup_avg）之上       *)
(*        的 genuine 逐点改进。                                            *)
(*  构造性注记：零 Axiom／零 Admitted／零承认式收尾；证明面全 algebra 链    *)
(*        （无微积分、无归纳、无经典逻辑），分支判定以 Qcompare 布尔反映形   *)
(*        就地分析；零重做。                                              *)
(*  数学核（对照 _mirror_519a2.py 17/17 全 PASS 在卷·Fractions 精确）：      *)
(*    · 四基 a=x(1−y), b=y(1−x), c=(1−x)(1−y), d=xy：a+b+c+d=1·ab=cd=N·    *)
(*      a+b=σ:=s−2p·c+d=τ, σ+τ=1；                                          *)
(*    · AM-GM×2：4ab ≤ σ²、4cd ≤ τ²（平方差闭式 (a−b)²/(c−d)² ≥ 0）；       *)
(*    · σ ≤ 1/2 支：56N=56ab ≤ 14σ² ≤ 3+σ（末式闭式分解                     *)
(*      3+σ−14σ² == (1−2σ)(7σ+3) ≥ 0，两因子于 σ∈[0,1/2] 域正）；           *)
(*    · σ > 1/2 支：3+σ == 4−τ 且 56N=56cd ≤ 14τ² ≤ 4−τ（闭式分解           *)
(*      4−τ−14τ² == (1−2τ)(7τ+4) ≥ 0，两因子于 τ∈[0,1/2] 域正）；           *)
(*    · 等号唯 τ-不动点 (1/2,1/2)：56·(1/16) == 3+(1−1/2) == 7/2（锚在卷·   *)
(*      dense 201² min slack=0 唯中心·对照 §3.3）。                          *)
(*  u 对角层（519A 移交账施工图逐句翻译·常数经精确复核判定）：                   *)
(*    · 分解式 3+2u−56u² == 56(1/4−u)(u+3/14)（u∈[0,1/4] 域正）；            *)
(*      【519A 移交账写「u+3/28」为转抄滑——精确复算 3/28 形 == 3/2+8u−56u²    *)
(*      ≠ 原式（对照 §2.2 反证在卷），正确常数 3/14，Coq ring 同式收束】；    *)
(*    · 对角 v∈[0,1]：u := v(1−v) ≤ 1/4（AM-GM (2v−1)² ≥ 0）⟹ 56u² ≤ 3+2u。 *)
(*  归一链形：14N ≤ Ψ₃·(1/4)（⟺ 56N ≤ Ψ₃·maxΨ̂⁻¹ 归一 Ψ̂₃=Ψ₃/4，             *)
(*  max Ψ̂₃ = 1 于中心）＋ Ψ₃ ≤ 4（4−Ψ₃ == (1−x)(1−y)+xy ≥ 0）——             *)
(*  供下游 famv_le_weight 末步更换（N^(m+1) ≤ ((1/14)·Ψ̂₃)^(m+1)）之插槽。    *)
(*  σ-权衡律见证（519A §3.3b）：θ·σ == 1/16 于 u=3（σ=7/8）：(1/14)(7/8)=1/16。*)
(*  依赖：Stdlib（QArith/ZArith/Lia）；GCL 世界继承件 S02_CauchyComplete     *)
(*        （QleT'/QeqT Set 承载正典形＋双向桥）、abl_dmw2_pointwise_sharp    *)
(*        （dmw2 基础不等式六件·GCL 冻结件同款使用）。零 Admitted。           *)
(*  诚实边界：Ψ₃ 的轨道表示 (5/3)(T+T̄)+(2/3)(T3+T4)（对照 §3.5·系数全正      *)
(*        总权 14/3 非凸）为计算域判定，本件不铸（T/T̄/T3/T4 轨道面属        *)
(*        gcl_coefficient 冻结域）；famv/sep 下游更换与 μ_lib 传导不在本件。  *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&       *)
(*        ulimit -s 65532 && cd 本池 && cpu_guard 包裹 rocq c               *)
(*        -native-compiler no -q -Q ../GCL/_world "" d519a2_cert.v          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Lia.
From Stdlib Require Import Extraction.
Require Import S02_CauchyComplete abl_dmw2_pointwise_sharp.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 语句面：Ψ₃ 定义与正典形桥                                                   *)
(* ============================================================ *)

(* Ψ₃ := 3+s−2p（519A Class B u=3 纯轨道正组合的 s−2p 形；Set 承载 Defined） *)
Definition d519_psi3 (x y : Q) : Q := 3 + x + y - 2 * x * y.

Lemma d519_psi3_eq : forall x y : Q,
  d519_psi3 x y == 3 + x + y - 2 * x * y.
Proof.
  intros x y. unfold d519_psi3. reflexivity.
Qed.

(* ============================================================ *)
(* §1 u 对角层：分解式＋u 域正＋对角化归件                                          *)
(* ============================================================ *)

(* 闭式分解（对照 §2.1 全网格·正确常数 3/14——移交账 3/28 转抄滑经复核判定） *)
Lemma d519_u_fact : forall u : Q,
  3 + 2 * u - 56 * u * u == 56 * ((1#4) - u) * (u + (3#14)).
Proof.
  intro u. ring.
Qed.

(* u 域正收束：u ∈ [0,1/4] ⟹ 56u² ≤ 3+2u *)
Theorem d519_u_le_14 : forall u : Q,
  0 <= u -> u <= (1#4) -> QleT' (56 * u * u) (3 + 2 * u).
Proof.
  intros u Hu0 Hu1.
  apply Qle_to_QleT'.
  apply (dmw2_sub_ge0 (56 * u * u) (3 + 2 * u)).
  rewrite (d519_u_fact u).
  apply Qmult_le_0_compat.
  - apply (dmw2_mult2_ge0 56 ((1#4) - u)).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply (dmw2_le_sub u (1#4)). exact Hu1.
  - apply (Qle_trans 0 u (u + (3#14))).
    + exact Hu0.
    + apply (dmw2_add_ge0_le u (3#14)). unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* AM-GM 对角特化：v(1−v) ≤ 1/4（(2v−1)² ≥ 0） *)
Lemma d519_v1v_le_quarter : forall v : Q, v * (1 - v) <= (1#4).
Proof.
  intro v.
  apply (dmw2_sub_ge0 (v * (1 - v)) (1#4)).
  assert (E : (1#4) - v * (1 - v) == (2 * v - 1) * (2 * v - 1) * (1#4)) by ring.
  rewrite E. apply Qmult_le_0_compat.
  - apply dmw2_sq_ge0.
  - unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 对角化归件（519A 施工图「最坏 p=s²/4 对角」的代数特化形）：
   v ∈ [0,1] ⟹ 56·(v(1−v))² ≤ 3+2v(1−v) *)
Theorem d519_diag_N_le_14 : forall v : Q,
  0 <= v <= 1 ->
  QleT' (56 * v * (1 - v) * (v * (1 - v))) (3 + v + v - 2 * v * v).
Proof.
  intro v. intros [Hv0 Hv1].
  assert (Hvb : 0 <= 1 - v) by (apply (dmw2_le_sub v 1); exact Hv1).
  assert (Hu0 : 0 <= v * (1 - v))
    by (apply Qmult_le_0_compat; [ exact Hv0 | exact Hvb ]).
  pose proof (d519_u_le_14 (v * (1 - v)) Hu0 (d519_v1v_le_quarter v)) as H.
  apply Qle_to_QleT'.
  assert (E1 : 56 * v * (1 - v) * (v * (1 - v))
            == 56 * (v * (1 - v)) * (v * (1 - v))) by ring.
  assert (E2 : 3 + v + v - 2 * v * v == 3 + 2 * (v * (1 - v))) by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle. exact H.
Qed.

(* ============================================================ *)
(* §2 主语句：56N ≤ 3+s−2p（四基代数路线·双分支）                                     *)
(* ============================================================ *)

Theorem d519_N_le_14 : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (56 * x * (1 - x) * y * (1 - y)) (3 + x + y - 2 * x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  (* 四基非负 *)
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (Ha : 0 <= x * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hb : 0 <= y * (1 - x)) by (apply Qmult_le_0_compat; assumption).
  assert (Hc : 0 <= (1 - x) * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hd : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hs0 : 0 <= x * (1 - y) + y * (1 - x)).
  { apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
    - exact Ha.
    - apply (dmw2_add_ge0_le (x * (1 - y)) (y * (1 - x))). exact Hb. }
  assert (Ht0 : 0 <= (1 - x) * (1 - y) + x * y).
  { apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
    - exact Hc.
    - apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)). exact Hd. }
  (* 四基恒等式（对照 §1.1-1.3） *)
  assert (HNab : x * (1 - x) * y * (1 - y) == (x * (1 - y)) * (y * (1 - x))) by ring.
  assert (HNcd : x * (1 - x) * y * (1 - y) == ((1 - x) * (1 - y)) * (x * y)) by ring.
  assert (Hsym : x * (1 - y) + y * (1 - x) + ((1 - x) * (1 - y) + x * y) == 1) by ring.
  (* AM-GM×2（平方差闭式·对照 §1.6） *)
  assert (Hgm1 : 4 * ((x * (1 - y)) * (y * (1 - x)))
              <= (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))).
  { apply (dmw2_sub_ge0 (4 * ((x * (1 - y)) * (y * (1 - x))))
             ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)))).
    assert (E : (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))
                - 4 * ((x * (1 - y)) * (y * (1 - x)))
             == ((x * (1 - y)) - (y * (1 - x)))
                * ((x * (1 - y)) - (y * (1 - x)))) by ring.
    rewrite E. apply dmw2_sq_ge0. }
  assert (Hgm2 : 4 * (((1 - x) * (1 - y)) * (x * y))
              <= ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)).
  { apply (dmw2_sub_ge0 (4 * (((1 - x) * (1 - y)) * (x * y)))
             (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y))).
    assert (E : ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)
                - 4 * (((1 - x) * (1 - y)) * (x * y))
             == (((1 - x) * (1 - y)) - (x * y))
                * (((1 - x) * (1 - y)) - (x * y))) by ring.
    rewrite E. apply dmw2_sq_ge0. }
  (* 分支判定：σ := a+b 与 1/2 的 Qcompare 布尔反映形就地分析 *)
  destruct (Qle_bool (x * (1 - y) + y * (1 - x)) (1#2)) eqn:Hbs.
  - (* σ ≤ 1/2 支：56N = 56ab ≤ 14σ² ≤ 3+σ *)
    assert (Hhalf : x * (1 - y) + y * (1 - x) <= (1#2)).
    { apply QleT'_to_Qle. unfold QleT'. rewrite Hbs. reflexivity. }
    assert (H72 : 0 <= 1 - 2 * (x * (1 - y) + y * (1 - x))).
    { assert (E : 1 - 2 * (x * (1 - y) + y * (1 - x))
               == 2 * ((1#2) - (x * (1 - y) + y * (1 - x)))) by ring.
      rewrite E. apply Qmult_le_0_compat.
      - unfold Qle. cbn [Qnum Qden]. lia.
      - apply (dmw2_le_sub (x * (1 - y) + y * (1 - x)) (1#2)). exact Hhalf. }
    assert (H73 : 0 <= 7 * (x * (1 - y) + y * (1 - x)) + 3).
    { assert (H7s : 0 <= 7 * (x * (1 - y) + y * (1 - x)))
        by (apply (dmw2_mult2_ge0 7 (x * (1 - y) + y * (1 - x)))
            ; [ unfold Qle; cbn [Qnum Qden]; lia | exact Hs0 ]).
      apply (Qle_trans 0 (7 * (x * (1 - y) + y * (1 - x)))
                        (7 * (x * (1 - y) + y * (1 - x)) + 3)).
      - exact H7s.
      - apply (dmw2_add_ge0_le (7 * (x * (1 - y) + y * (1 - x))) 3)
        ; unfold Qle; cbn [Qnum Qden]; lia. }
    assert (HQ1 : (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14
               <= 3 + (x * (1 - y) + y * (1 - x))).
    { apply (dmw2_sub_ge0
               ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14)
               (3 + (x * (1 - y) + y * (1 - x)))).
      assert (E : 3 + (x * (1 - y) + y * (1 - x))
                  - (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14
               == (1 - 2 * (x * (1 - y) + y * (1 - x)))
                  * (7 * (x * (1 - y) + y * (1 - x)) + 3)) by ring.
      rewrite E. apply Qmult_le_0_compat; assumption. }
    assert (HQ2 : 56 * ((x * (1 - y)) * (y * (1 - x)))
               <= (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14).
    { assert (H14 : 0 <= 14) by (unfold Qle; cbn [Qnum Qden]; lia).
      pose proof (Qmult_le_compat_r (4 * ((x * (1 - y)) * (y * (1 - x))))
                    ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))) 14
                    Hgm1 H14) as Hm.
      assert (E : (4 * ((x * (1 - y)) * (y * (1 - x)))) * 14
               == 56 * ((x * (1 - y)) * (y * (1 - x)))) by ring.
      rewrite E in Hm. exact Hm. }
    apply Qle_to_QleT'.
    assert (E1 : 56 * x * (1 - x) * y * (1 - y)
              == 56 * ((x * (1 - y)) * (y * (1 - x)))) by ring.
    assert (E2 : 3 + x + y - 2 * x * y
              == 3 + (x * (1 - y) + y * (1 - x))) by ring.
    rewrite E1, E2.
    apply (Qle_trans
             (56 * ((x * (1 - y)) * (y * (1 - x))))
             ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14)
             (3 + (x * (1 - y) + y * (1 - x)))).
    + exact HQ2.
    + exact HQ1.
  - (* σ > 1/2 支：τ := c+d ≤ 1/2，56N = 56cd ≤ 14τ² ≤ 4−τ = 3+σ *)
    assert (Hnle : ~ (x * (1 - y) + y * (1 - x) <= (1#2))).
    { intro Hcc.
      assert (HcT : QleT' (x * (1 - y) + y * (1 - x)) (1#2))
        by (apply Qle_to_QleT'; exact Hcc).
      unfold QleT' in HcT. rewrite Hbs in HcT. inversion HcT. }
    assert (Hgt : (1#2) < x * (1 - y) + y * (1 - x)).
    { apply (Qnot_le_lt (x * (1 - y) + y * (1 - x)) (1#2)). exact Hnle. }
    assert (Hs1 : x * (1 - y) + y * (1 - x) <= 1).
    { pose proof (Qplus_le_compat (x * (1 - y) + y * (1 - x))
                                  (x * (1 - y) + y * (1 - x)) 0
                                  ((1 - x) * (1 - y) + x * y)
                                  (Qle_refl (x * (1 - y) + y * (1 - x))) Ht0) as Hs.
      assert (Ez : x * (1 - y) + y * (1 - x) + 0
                == x * (1 - y) + y * (1 - x)) by ring.
      rewrite Ez in Hs. rewrite Hsym in Hs. exact Hs. }
    assert (Ht2 : 0 <= 1 - 2 * ((1 - x) * (1 - y) + x * y)).
    { assert (E : 1 - 2 * ((1 - x) * (1 - y) + x * y)
               == 2 * ((x * (1 - y) + y * (1 - x)) - (1#2))) by ring.
      rewrite E. apply Qmult_le_0_compat.
      - unfold Qle. cbn [Qnum Qden]. lia.
      - apply (dmw2_le_sub (1#2) (x * (1 - y) + y * (1 - x)))
        ; apply Qlt_le_weak; exact Hgt. }
    assert (Ht4 : 0 <= 7 * ((1 - x) * (1 - y) + x * y) + 4).
    { assert (H7t : 0 <= 7 * ((1 - x) * (1 - y) + x * y))
        by (apply (dmw2_mult2_ge0 7 ((1 - x) * (1 - y) + x * y))
            ; [ unfold Qle; cbn [Qnum Qden]; lia | exact Ht0 ]).
      apply (Qle_trans 0 (7 * ((1 - x) * (1 - y) + x * y))
                        (7 * ((1 - x) * (1 - y) + x * y) + 4)).
      - exact H7t.
      - apply (dmw2_add_ge0_le (7 * ((1 - x) * (1 - y) + x * y)) 4)
        ; unfold Qle; cbn [Qnum Qden]; lia. }
    assert (HQ1 : ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14
               <= 4 - ((1 - x) * (1 - y) + x * y)).
    { apply (dmw2_sub_ge0
               (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14)
               (4 - ((1 - x) * (1 - y) + x * y))).
      assert (E : 4 - ((1 - x) * (1 - y) + x * y)
                  - ((1 - x) * (1 - y) + x * y)
                    * ((1 - x) * (1 - y) + x * y) * 14
               == (1 - 2 * ((1 - x) * (1 - y) + x * y))
                  * (7 * ((1 - x) * (1 - y) + x * y) + 4)) by ring.
      rewrite E. apply Qmult_le_0_compat; assumption. }
    assert (HQ2 : 56 * (((1 - x) * (1 - y)) * (x * y))
               <= ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14).
    { assert (H14 : 0 <= 14) by (unfold Qle; cbn [Qnum Qden]; lia).
      pose proof (Qmult_le_compat_r (4 * (((1 - x) * (1 - y)) * (x * y)))
                    (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)) 14
                    Hgm2 H14) as Hm.
      assert (E : (4 * (((1 - x) * (1 - y)) * (x * y))) * 14
               == 56 * (((1 - x) * (1 - y)) * (x * y))) by ring.
      rewrite E in Hm. exact Hm. }
    apply Qle_to_QleT'.
    assert (E1 : 56 * x * (1 - x) * y * (1 - y)
              == 56 * (((1 - x) * (1 - y)) * (x * y))) by ring.
    assert (E2 : 3 + x + y - 2 * x * y
              == 4 - ((1 - x) * (1 - y) + x * y)) by ring.
    rewrite E1, E2.
    apply (Qle_trans
             (56 * (((1 - x) * (1 - y)) * (x * y)))
             (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14)
             (4 - ((1 - x) * (1 - y) + x * y))).
    + exact HQ2.
    + exact HQ1.
Qed.

(* ============================================================ *)
(* §3 归一链形＋Ψ₃ ≤ 4＋验收锚（照 _mirror_519a.py §3.4 精确值逐行）                   *)
(* ============================================================ *)

(* 归一链形（famv 末步更换插槽）：14N ≤ Ψ₃·(1/4) ⟺ N ≤ (1/14)·Ψ̂₃ *)
Theorem d519_N_le_14_psihat : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (14 * x * (1 - x) * y * (1 - y)) ((3 + x + y - 2 * x * y) * (1#4)).
Proof.
  intros x y Hx Hy.
  pose proof (QleT'_to_Qle _ _ (d519_N_le_14 x y Hx Hy)) as H.
  assert (Hq : 0 <= (1#4)) by (unfold Qle; cbn [Qnum Qden]; lia).
  pose proof (Qmult_le_compat_r (56 * x * (1 - x) * y * (1 - y))
                (3 + x + y - 2 * x * y) (1#4) H Hq) as Hm.
  assert (E : (56 * x * (1 - x) * y * (1 - y)) * (1#4)
           == 14 * x * (1 - x) * y * (1 - y)) by ring.
  rewrite E in Hm.
  apply Qle_to_QleT'. exact Hm.
Qed.

(* Ψ₃ ≤ 4（4−Ψ₃ == (1−x)(1−y)+xy ≥ 0·max Ψ̂₃ = 1 的分子侧） *)
Theorem d519_psi3_le_4 : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> QleT' (3 + x + y - 2 * x * y) 4.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  apply Qle_to_QleT'.
  apply (dmw2_sub_ge0 (3 + x + y - 2 * x * y) 4).
  assert (E : 4 - (3 + x + y - 2 * x * y) == (1 - x) * (1 - y) + x * y) by ring.
  rewrite E.
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (H1 : 0 <= (1 - x) * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (H2 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
  - exact H1.
  - apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)). exact H2.
Qed.

(* 验收锚（等号唯 τ-不动点）：56·N(1/2,1/2) == 3+Q0(1/2,1/2) == 7/2
   ——照 _mirror_519a.py §3.4 精确值逐行（非「14≤3」转抄形） *)
Lemma d519_anchor_tight : QeqT
  (56 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)))
  (3 + (1#2) + (1#2) - 2 * (1#2) * (1#2)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* θ(3) == 4/56 == 1/14（§3.3c 闭式 θ(u)=(u+1)/(16(u+1/2)) 于 u=3 归一值） *)
Lemma d519_theta14 : QeqT ((4#56)) ((1#14)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* σ-权衡律见证（519A §3.3b）：θ·σ == 1/16 于 u=3（σ = Ψ₃(中心)/maxΨ = (7/2)/4 = 7/8） *)
Lemma d519_sigma_trade : QeqT ((1#14) * (7#8)) ((1#16)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §4 提取与假设审计                                                              *)
(* ============================================================ *)

Print Assumptions d519_u_le_14.
Print Assumptions d519_diag_N_le_14.
Print Assumptions d519_N_le_14.
Print Assumptions d519_N_le_14_psihat.
Print Assumptions d519_psi3_le_4.
Print Assumptions d519_anchor_tight.
Print Assumptions d519_theta14.
Print Assumptions d519_sigma_trade.

Separate Extraction d519_psi3 d519_u_le_14 d519_diag_N_le_14 d519_N_le_14
  d519_N_le_14_psihat d519_psi3_le_4 d519_anchor_tight d519_theta14
  d519_sigma_trade.
