(* ============================================================
   UpEntropyGain.v —— 榜 A2：second_law_irreversible（根 L27796）
   从"假设搬运型平凡"升级为带定量增量的真定理。

   件 1  entropy_step_gain_lower：
     一步梯度上升 x' := x + η·g(x) 的熵增量定量下界
       entropy(x') − entropy(x) ≥ η·(1 − L·η)·g(x)²     （g(x) > 0）
   件 2  entropy_gain_positive：
     0 < η、0 < L、ηL < 1、g(x) > 0 ⟹ 0 < entropy(x') − entropy(x)
   件 3  second_law_quant（对照注记）：
     同条件下严格熵增 lt (entropy x) (entropy (dynamics x))——
     以"充分条件版定理"取代根 SecondLaw 区的
     Variable strict_entropy_increase 假设重述（旧件可退役）。

   纸笔推导（tangent 接口 + Lipschitz 实际形态）：
     (i)   切线（凹景观上界）在 x' 处取 y := x：
           e ≤ e' + g'·(x − x')，而 x − x' = −η·g
           ⟹ e' − e ≥ η·g·g'。
     (ii)  下界 g' ≥ (1 − Lη)·g 来自 Lipschitz 单边提取：
           g − g' ≤ |g − g'| ≤ L|x − x'| = Lη·g（g > 0 时 |x−x'| = ηg）。
           注意 strong_concavity(μ) 只给 g' ≤ (1−ημ)·g（上界），
           无法控制步长过大时的回落——曲率修正项的常数只能是 L。
     (iii) g > 0 两侧乘 (1−Lη)g ≥ g' 得 g·g' ≥ (1−Lη)g²
           ⟹ 增量 ≥ η(1−Lη)g²。
     数值 sanity（f = log, x = 2, η = 0.4, L = 2）：
           真增量 log(1.2) ≈ 0.182 ≥ 下界 0.4·(1−0.8)·0.25 = 0.02 ✓。
     正性条件是 ηL < 1 而非草案的 ημ < 1：μ ≤ L（Lipschitz 与强凹
           相容时）⟹ 1/L ≤ 1/μ，ημ < 1 控制不住过冲，诚实常数取 1/L。
     g(x) < 0 负支同界（|g| 收缩对称），但其提取需符号三分判定，
           构造性 Set 层不可达——如实降级为 g(x) > 0 单侧版。

   纪律：纯构造性 / Set 层 / 零未证缺口 / 零经典 / 语句零 Prop
        （lt/le 均接口 Set 字段；无 Not/Or 前提）/ 可提取 OCaml。
   诚实接口：entropy_tangent / gradient_lipschitz /
        dynamics_gradient_step 复刻根 ConvergenceCauchy 区同名
        Variable；abs_ge_value（le a (abs a)，与根 abs_ge_zero_id_cc
        同族的构造性有序域标准性质，Real 层可证）与
        lt_plus_compat_lt_le（根区同名 Variable 先例）为本区新增。
   ============================================================ *)
Require Import CW_ConstructiveWorld_219.

Section EntropyGainQuant.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段（同根 ConvergenceCauchy 先例） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)，定义性展开） *)

(* ===== 诚实接口（Variable 复刻根 ConvergenceCauchy 区） ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz : forall x y : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (minus x y))).
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).
(* 新增诚实接口：|·| 的单边提取（le a (abs a)；根 abs_ge_zero_id_cc
   同族——le zero a -> |a| == a 的姊妹形态；构造性有序域标准性质，
   柯西实数模型可证，抽象层声明为接口字段，非经典公理） *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== 基础代数（Root 全局层无此三件的手工链） ===== *)

(* 减法定义（minus 透明，定义性相等） *)
Lemma eg_minus_def : forall a b : R, Id (minus a b) (plus a (opp b)).
Proof. intros a b. apply id_refl. Qed.

(* 减法可逆：(a − b) + b == a *)
Lemma eg_minus_plus_cancel : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* K0 单步展开（差形式）：x' − x == η·g(x) *)
Lemma eg_step_diff : forall x : R,
  Id (minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_gradient_step x))).
  apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
  apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x)))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
  apply (plus_zero (mult eta (entropy_gradient x))).
Qed.

(* K0' 反向差：x − x' == −(η·g(x)) *)
Lemma eg_step_neg_diff : forall x : R,
  Id (minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus x z)
                           (id_cong opp (dynamics_gradient_step x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (opp_plus x (mult eta (entropy_gradient x))))).
  apply (id_trans (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x))))).
  apply (id_trans (id_cong (fun z => plus z (opp (mult eta (entropy_gradient x))))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (opp (mult eta (entropy_gradient x))))).
  apply (plus_zero (opp (mult eta (entropy_gradient x)))).
Qed.

(* 辅助：严格减正 a < b ⟹ 0 < b − a（根 ConvergenceCauchy 区 minus_pos 同构） *)
Lemma eg_minus_pos : forall u v : R, lt u v -> lt zero (minus v u).
Proof.
  intros u v Huv. unfold minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u)) (id_sym (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== 件 1 核 A：切线在 x' 处反向使用 ⟹ 增量 ≥ η·g(x)·g(x') =====
   切线（上界控制）在 x' 处取 y := x：
     e ≤ e' + g'·(x − x') = e' − g'·(η·g) ⟹ e' − e ≥ g'·(η·g) *)
Lemma eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* Ht 换形：minus x x' == −(η·g)；g'·(−η·g) == −(g'·(η·g)) *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r _ (plus (entropy (dynamics x))
                           (mult (entropy_gradient (dynamics x))
                                 (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => plus (entropy (dynamics x)) z)
                     (id_trans (id_cong (fun z => mult (entropy_gradient (dynamics x)) z)
                                        (eg_step_neg_diff x))
                               (opp_mult_l (entropy_gradient (dynamics x))
                                           (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* 两边加 W := g'·(η·g) 移项：le e (e' − W) ⟹ le (e + W) e'
     链：le_plus_compat Ht1 (le_refl W) 得 le (e + W) ((e' − W) + W)，
     右端 == e'（assoc + plus_opp + plus_zero），le_id_r 直接收口 *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat (entropy x)
                               (plus (entropy (dynamics x))
                                     (opp (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               Ht1 (le_refl (mult (entropy_gradient (dynamics x))
                                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (id_trans (id_sym (plus_assoc (entropy (dynamics x))
                                          (opp (mult (entropy_gradient (dynamics x))
                                                     (mult eta (entropy_gradient x))))
                                          (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                      (id_trans (id_cong (fun z => plus (entropy (dynamics x)) z)
                                         (id_trans (plus_comm (opp (mult (entropy_gradient (dynamics x))
                                                                            (mult eta (entropy_gradient x))))
                                                              (mult (entropy_gradient (dynamics x))
                                                                    (mult eta (entropy_gradient x))))
                                                   (plus_opp (mult (entropy_gradient (dynamics x))
                                                                   (mult eta (entropy_gradient x))))))
                                (plus_zero (entropy (dynamics x))))).
    - exact Hadd. }
  (* 两边加 opp e 提取：le (e + W) e' ⟹ le W (e' − e) == minus e' e *)
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))).
  - exact (id_trans (id_trans (id_sym (plus_zero (mult (entropy_gradient (dynamics x))
                                                      (mult eta (entropy_gradient x)))))
                              (id_cong (fun z => plus (mult (entropy_gradient (dynamics x))
                                                             (mult eta (entropy_gradient x))) z)
                                       (id_sym (plus_opp (entropy x)))))
                    (id_trans (plus_assoc (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))
                                          (entropy x) (opp (entropy x)))
                              (id_cong (fun z => plus z (opp (entropy x)))
                                       (plus_comm (mult (entropy_gradient (dynamics x))
                                                        (mult eta (entropy_gradient x)))
                                                  (entropy x))))).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== 件 1 核 B：Lipschitz 单边提取 ⟹ g' ≥ (1 − L·η)·g ===== *)
Lemma eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' − x| == η·g(x)（η>0、g>0：abs_pos + abs_mult + abs_opp） *)
  assert (Hstep : Id (minus (dynamics x) x) (mult eta (entropy_gradient x)))
    by exact (eg_step_diff x).
  assert (Hha : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) eta_pos Hgx).
  assert (Habsstep : Id (abs (minus (dynamics x) x))
                        (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs Hstep)).
    apply (id_trans (abs_mult eta (entropy_gradient x))).
    exact (id_cong2 (fun u v => mult u v) (abs_pos eta eta_pos) (abs_pos _ Hgx)). }
  assert (Habsneg : Id (abs (minus x (dynamics x)))
                       (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs (eg_step_neg_diff x))).
    apply (id_trans (abs_opp (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong abs (id_sym Hstep))).
    exact Habsstep. }
  (* (ii) Lipschitz 在 (x, x') 处：|g − g'| ≤ L·η·g *)
  assert (Hlip : le (abs (minus (entropy_gradient x) (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r _ (mult L (abs (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => mult L z) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) 单边提取：g − g' ≤ |g − g'| ≤ L·η·g（abs_ge_value） *)
  assert (Hone : le (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans _ (abs (minus (entropy_gradient x)
                                  (entropy_gradient (dynamics x)))) _).
    - exact (abs_ge_value (minus (entropy_gradient x)
                                 (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) 移项：g − (Lη)g ≤ g'，即 (1 − Lη)·g ≤ g'
        链：加 g' 得 le g ((Lη)g + g')；加 opp((Lη)g) 得 le (g − (Lη)g) g' *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (minus (entropy_gradient x)
                                (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))).
    - exact (id_sym (eg_minus_plus_cancel (entropy_gradient x)
                                          (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)) (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r _ (plus (plus (mult L (mult eta (entropy_gradient x)))
                                 (entropy_gradient (dynamics x)))
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (entropy_gradient (dynamics x))).
    - exact (id_trans (id_cong (fun z => plus z (opp (mult L (mult eta (entropy_gradient x)))))
                               (plus_comm (mult L (mult eta (entropy_gradient x)))
                                          (entropy_gradient (dynamics x))))
                      (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                                    (mult L (mult eta (entropy_gradient x)))
                                                    (opp (mult L (mult eta (entropy_gradient x))))))
                                (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                                                   (plus_opp (mult L (mult eta (entropy_gradient x)))))
                                          (plus_zero (entropy_gradient (dynamics x)))))).
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (v) 换形：g + opp((Lη)g) == (1 − Lη)·g
        链：opp((Lη)g) == opp((L·η)g) == (opp(Lη))·g；再
        g + (opp(Lη))·g == 1·g + (opp(Lη))·g == (1 + opp(Lη))·g *)
  apply (le_id_l (mult (minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (id_sym
             (id_trans (id_cong (fun z => plus (entropy_gradient x) z)
                                (id_trans (id_cong opp (mult_assoc L eta (entropy_gradient x)))
                                          (id_sym (opp_mult_r (mult L eta) (entropy_gradient x)))))
                       (id_trans (id_cong (fun z => plus z (mult (opp (mult L eta))
                                                                 (entropy_gradient x)))
                                          (id_trans (id_sym (mult_one (entropy_gradient x)))
                                                    (mult_comm (entropy_gradient x) one)))
                                 (id_sym (mult_plus_distr_r one (opp (mult L eta))
                                                            (entropy_gradient x)))))).
  - exact H2.
Qed.

(* ============================================================
   件 1（交付）：entropy_step_gain_lower —— 一步熵增定量下界
     g(x) > 0 ⟹
     η(1 − L·η)·g(x)² ≤ entropy(dynamics x) − entropy(x)
   组装：核 B 乘 g > 0 再乘 η > 0，与核 A 级联。
   ============================================================ *)
Theorem entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (eg_grad_lower x Hgx) as Hlow.
  (* 乘 g > 0（le_mult_compat）：(c₁·g)·g ≤ g'·g，左换形 assoc *)
  pose proof (le_mult_compat (mult (minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l _ (mult (mult (minus one (mult L eta)) (entropy_gradient x))
                           (entropy_gradient x)) _).
    - exact (mult_assoc (minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  (* 乘 η > 0（le_mult_compat_r，左乘）：η·((1−Lη)·g²) ≤ η·(g'·g) *)
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (le_mult_compat_r eta
                             (mult (minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x)))
                             (mult (entropy_gradient (dynamics x)) (entropy_gradient x))
                             Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l _ (mult eta (mult (minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x)))) _).
    - exact (id_sym (mult_assoc eta (minus one (mult L eta))
                                (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r _ (mult eta (mult (entropy_gradient (dynamics x))
                                       (entropy_gradient x))) _).
      + exact (id_trans (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                        (id_trans (id_cong (fun z => mult z (entropy_gradient x))
                                           (mult_comm eta (entropy_gradient (dynamics x))))
                                  (id_sym (mult_assoc (entropy_gradient (dynamics x))
                                                      eta (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans _ _ _ Hm2' (eg_tangent_shift x)).
Qed.

(* ============================================================
   件 2（交付）：entropy_gain_positive —— 增量正性充分条件版
     0 < η、0 < L、ηL < 1、g(x) > 0 ⟹ 0 < entropy(x') − entropy(x)
   （正性条件取 ηL < 1 而非草案 ημ < 1：μ 只控制上界不控制过冲，
     见文件头推导注记；负支 g < 0 需符号三分判定，构造性降级单侧版。）
   ============================================================ *)
Theorem entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (minus one (mult L eta)))
    by exact (eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (minus one (mult L eta))))
    by exact (mult_positive eta (minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero _ _ HA Hlow).
Qed.

(* ============================================================
   件 3（对照注记 + 交付推论）：second_law_quant
   根 L27778–27803 SecondLaw 区：strict_entropy_increase 是接口假设
   （Variable），second_law_irreversible = `apply strict_entropy_increase`
   （T2 假设搬运，探针实证导出形态两处同现同一前提）。本件以具体熵梯度
   动力学 + 诚实充分条件（ηL < 1、g(x) > 0）产出同一结论
   lt (entropy x) (entropy (dynamics x))——旧件可作退役注记：
   其接口前提在本件条件下由 entropy_gain_positive 构造性供给。
   ============================================================ *)
Theorem second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (id_trans (id_sym (plus_zero (entropy x)))
                      (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero (minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainQuant.
