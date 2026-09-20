(* ============================================================ *)
(* BetaLower.v —— P5 载体下界：c·σ^n 型下界的 Beta 闭式构造         *)
(*                                                               *)
(* 使命：对 ln2 逼近载体 lne_B n = (n!)²/(2n+1)!（Beta 闭式，见       *)
(*   lne_B_closed），构造并证明 c·σ^n 型下界。三种参数：              *)
(*   · 规格参数 (c, σ) = (1/2, 3/16)；                              *)
(*   · 族最优参数 (c, σ) = (98/135, 3/14)，在 n=2 与 n=3 同时        *)
(*     取等号，该意义下不可改进；                                   *)
(*   · (1+t) 侧变体偏移 (1/4)·(3/32)^n。                            *)
(*   本件范围仅下界；恒等式不在本件。                                *)
(*                                                               *)
(* 数学背景：真恒等式 ln2 − x'_n = I_n/(2^{n+1}·q̃_n)，其中            *)
(*   I_n = ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt（分母无平方）。             *)
(*   (1−t/2)^{−(n+1)} ≥ 1 逐点（因 2−t ≤ 2），且具正系数二项级数，    *)
(*   故 I_n ≥ lne_B n。I_n 本体（有理被积函数的积分）不在库内，       *)
(*   也不在 PolyIntegral 的 pint_ 多项式面（Ln2Escape 头注同判）；    *)
(*   该不等式最后一步需全段逐点机制，故本件只断言以 lne_B n 为       *)
(*   载体的可证下界形；至于 I_n 本体的精确下界，本件不虚称、          *)
(*   不覆盖。                                                       *)
(*                                                               *)
(* 数值事实：lne_B 0..3 = 1, 1/6, 1/30, 1/140；                      *)
(*   步比 (n+1)/(2(2n+3)) 在 n=2 处取尾最小值 3/14，                 *)
(*   故族最优 σ = 3/14。                                            *)
(*                                                               *)
(* 证明结构：bl_half_pow 与 bl_opt_pow 将左侧常数幂化为单一分式，     *)
(*   lne_B_closed 展开右端，经 bl_div_le 归约到纯 nat 阶乘不等式      *)
(*   bl_nat_core16 / bl_nat_core14（线性证书，免高阶证书）；          *)
(*   Q 分式与 nat 阶乘的转换由 sif_qfact_Z 承担。                    *)
(*                                                               *)
(* 数值锚：§5 提供 n=0..3 的 vm_compute 实例（bl_spec_anchor0..3、   *)
(*   bl_opt_anchor0..3、bl_var_anchor3）与 lne_B 值见证 ×3           *)
(*   （bl_value1/2/3）。                                            *)
(*                                                               *)
(* 依赖（本库）：S02_CauchyComplete、S03_QExp、SumInvFactEscape、     *)
(*   PolyIntegral、Ln2Escape；stdlib：Arith.Factorial 等。           *)
(*                                                               *)
(* 对标：stdlib Arith.Factorial（阶乘载体）；Beta 闭式配方同          *)
(*   Ln2Escape 的 lne_beta_value（两参数 Beta 归纳的对角特化）。      *)
(*                                                               *)
(* 构造性注记：语句面全 Set（QleT'/QeqT），零承认、零经典逻辑，        *)
(*   语句位置不用 Prop；提取面 Obj.magic = 0                           *)
(*   （§6 Separate Extraction 与 Print Assumptions 自审）。           *)
(*                                                               *)
(* 编译配方：Rocq 9.1 直调，unset COQLIB/ROCQLIB，                   *)
(*   cpu_guard 包裹（LoadLimit 85，CoreN 2）。                       *)
(*                                                               *)
(* 诚实未竟项：I_n ≥ lne_B n 的精确偏移与全段逐点机制不在本件，       *)
(*   见 bl_variant_shift 注。                                       *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Arith.Factorial.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import PolyIntegral.
Require Import Ln2Escape.

(* ============================================================ *)
(* §1 Q 层支撑引理                                                   *)
(* ============================================================ *)

(* 正底幂的非零下界：1 ≤ k ⟹ 1 ≤ k^n（为 Qlt 前提提供正下界） *)
Lemma bl_mul_ge1 : forall k n : nat, (1 <= k)%nat -> (1 <= k ^ n)%nat.
Proof.
  intros k n Hk. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Qmake 层乘法桥接引理：(a#1)·(b#1) == (a·b#1)，展开 Qmult 后为定义级计算 *)
Lemma bl_qmake_mul : forall a b : Z, (a # 1) * (b # 1) == (a * b # 1)%Q.
Proof.
  intros a b. unfold Qmult. cbn [Pos.mul]. reflexivity.
Qed.

(* Qinv 对乘积分配：x、y 均非零 ⟹ Qinv (x*y) == Qinv x * Qinv y（bl_pow_div 使用） *)
Lemma bl_qinv_mult : forall x y : Q,
  ~ (x == 0%Q) -> ~ (y == 0%Q) -> Qinv (x * y) == Qinv x * Qinv y.
Proof.
  intros x y Hx Hy.
  apply (lne_mult_canc (Qinv (x * y)) (Qinv x * Qinv y) (x * y)).
  - transitivity (1%Q).
    + rewrite (Qmult_comm (Qinv (x * y)) (x * y)).
      apply Qmult_inv_r.
      intro E. apply Hx. apply (lne_mult_canc x 0%Q y).
      * rewrite Qmult_0_l. exact E.
      * exact Hy.
    + assert (E1 : (Qinv x * Qinv y) * (x * y) == (x * Qinv x) * (y * Qinv y)) by ring.
      rewrite E1.
      rewrite (Qmult_inv_r x Hx). rewrite (Qmult_inv_r y Hy). ring.
  - apply (lne_mult_nz x y Hx Hy).
Qed.

(* 正底幂非零：~ (q_pow y n == 0)，对 n 归纳：情形 n=0 归约即得，归纳步由 lne_mult_nz 传递非零性 *)
Lemma bl_qpow_nz : forall (y : Q) (n : nat), ~ (y == 0%Q) -> ~ (q_pow y n == 0%Q).
Proof.
  intros y n Hy. induction n as [| n IH].
  - intro E. vm_compute in E. lia.
  - apply (lne_mult_nz y (q_pow y n)).
    + exact Hy.
    + apply IH.
Qed.

(* 幂的除法分配：q_pow (x/y) n == q_pow x n / q_pow y n *)
Lemma bl_pow_div : forall (x y : Q) (n : nat),
  ~ (y == 0%Q) -> q_pow (x / y) n == q_pow x n / q_pow y n.
Proof.
  intros x y n Hy. induction n as [| n IH].
  - reflexivity.
  - assert (Hzn : ~ (q_pow y n == 0%Q)) by (apply bl_qpow_nz; exact Hy).
    rewrite (q_pow_succ (x / y) n), (q_pow_succ x n), (q_pow_succ y n), IH.
    unfold Qdiv.
    rewrite (bl_qinv_mult y (q_pow y n) Hy Hzn).
    ring.
Qed.

(* 乘除结合桥接引理：x·(y/z) == (x·y)/z（Qdiv 的定义即乘 Qinv，展开后为结合律） *)
Lemma bl_mult_div_assoc : forall x y z : Q, x * (y / z) == (x * y) / z.
Proof. intros x y z. unfold Qdiv. ring. Qed.

(* 整数 cast 幂桥接引理：q_pow (Z.of_nat k # 1) n == (Z.of_nat (k ^ n) # 1) *)
Lemma bl_pZ : forall k n : nat, q_pow (Z.of_nat k # 1) n == (Z.of_nat (k ^ n) # 1)%Q.
Proof.
  intros k n. induction n as [| n IH].
  - reflexivity.
  - rewrite q_pow_succ, IH, Nat.pow_succ_r'.
    unfold Qmult. cbn [Pos.mul]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 同幂相乘桥接引理：q_pow x n · q_pow y n == q_pow (x·y) n（bl_variant_shift 使用） *)
Lemma bl_qpow_mul : forall (x y : Q) (n : nat), q_pow x n * q_pow y n == q_pow (x * y) n.
Proof.
  intros x y n. induction n as [| n IH].
  - reflexivity.
  - rewrite (q_pow_succ x n), (q_pow_succ y n), (q_pow_succ (x * y) n).
    transitivity ((x * y) * (q_pow x n * q_pow y n)).
    + ring.
    + rewrite IH. ring.
Qed.

(* 左乘保序：x ≤ y、0 ≤ z ⟹ z·x ≤ z·y（Qmult_le_compat_r 经交换重排直得） *)
Lemma bl_mlc : forall x y z : Q, Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H Hz.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  exact (Qmult_le_compat_r x y z H Hz).
Qed.

(* 除法下界比较器（lne_div_le_inv 的对应形式）：0 < y、z·y ≤ x ⟹ z ≤ x/y *)
Lemma bl_div_ge : forall x y z : Q, Qlt 0 y -> Qle (z * y) x -> Qle z (x / y).
Proof.
  intros x y z Hy Hzy. unfold Qdiv.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ E). }
  assert (Ey : (y * Qinv y)%Q == 1%Q) by (apply Qmult_inv_r; exact Hy0).
  assert (H1 : Qle ((z * y) * Qinv y) (x * Qinv y)).
  { apply (Qmult_le_compat_r (z * y) x).
    - exact Hzy.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy. }
  rewrite <- (Qmult_assoc z y (Qinv y)) in H1.
  rewrite Ey in H1. rewrite Qmult_1_r in H1.
  exact H1.
Qed.

(* 右消元器：0 < s、a·s ≤ b·s ⟹ a ≤ b（内部走 bl_div_ge） *)
Lemma bl_cancel_r : forall a b s : Q, Qlt 0 s -> Qle (a * s) (b * s) -> Qle a b.
Proof.
  intros a b s Hs H.
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (H1 : Qle a ((b * s) / s)) by (apply (bl_div_ge (b * s) s a Hs H)).
  assert (E : (b * s) / s == b).
  { unfold Qdiv.
    assert (E0 : (b * s) * Qinv s == b * (s * Qinv s)) by ring.
    rewrite E0, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
  rewrite E in H1. exact H1.
Qed.

(* 除法比较器（lne_div_eq 的不等式版）：0<y、0<s、x·s ≤ y·r ⟹ x/y ≤ r/s *)
Lemma bl_div_le : forall x y r s : Q,
  Qlt 0 y -> Qlt 0 s -> Qle (x * s) (y * r) -> Qle (x / y) (r / s).
Proof.
  intros x y r s Hy Hs Hc.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ Ee). }
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (E : x / y == (x * s) / (y * s)).
  { apply (lne_div_eq x y (x * s) (y * s)).
    - exact Hy.
    - apply Qmult_lt_0_compat; assumption.
    - ring. }
  rewrite E. unfold Qdiv.
  rewrite (bl_qinv_mult y s Hy0 Hs0).
  assert (E2 : (x * s) * (Qinv y * Qinv s) == (x * Qinv y) * (s * Qinv s)) by ring.
  rewrite E2.
  apply (Qle_trans _ (x * Qinv y)).
  - apply qeq_imp_qle.
    assert (HT : (s * Qinv s)%Q == 1) by (apply Qmult_inv_r; exact Hs0).
    rewrite HT, Qmult_1_r. reflexivity.
  - apply (bl_cancel_r (x * Qinv y) (r * Qinv s) s Hs).
    assert (E3 : (x * Qinv y) * s == (x * s) * Qinv y) by ring.
    rewrite E3.
    assert (E5 : (r * Qinv s) * s == r).
    { assert (E6 : (r * Qinv s) * s == r * (s * Qinv s)) by ring.
      rewrite E6, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
    rewrite E5.
    apply (Qle_trans _ ((y * r) * Qinv y)).
    + apply (Qmult_le_compat_r (x * s) (y * r) (Qinv y)).
      * exact Hc.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy.
    + assert (E4 : (y * r) * Qinv y == r).
      { assert (E7 : (y * r) * Qinv y == r * (y * Qinv y)) by ring.
        rewrite E7, (Qmult_inv_r y Hy0), Qmult_1_r. reflexivity. }
      rewrite E4. apply Qle_refl.
Qed.

(* ============================================================ *)
(* §2 纯 nat 阶乘不等式核                                            *)
(* ============================================================ *)

(* 主核：3^n·8·(2n+1)! ≤ 16^n·16·(n!)²
   （⟺ (1/2)(3/16)^n ≤ (n!)²/(2n+1)!；与 Ln2Escape 的 lne_nat_core 同型；
     归纳步经线性证书 3(2n+3) ≤ 8(n+1)（n≥1）比较步乘子，全程线性 lia） *)
Lemma bl_nat_core16 : forall n : nat,
  (3 ^ n * 8 * fact (2 * n + 1) <= 16 ^ n * 16 * fact n * fact n)%nat.
Proof.
(* 对 n 归纳，归纳步：由 n 到 S n。 *)  induction n as [| n IH].
  - (* 情形 n=0：两侧归约后线性。 *)cbn. lia.
  - (* 情形分析：先处理 S n = 1，再处理 S n ≥ 2。 *)destruct n as [| m].
    + (* 情形 n=0：即 S n = 1，归约后线性。 *)cbn. lia.
    + (* 情形 n=S m：展开阶乘的两层新因子，公共步乘子为
         3(2m+5)(2m+4)；线性证书 H1: 3(2m+5) ≤ 8(m+2) 乘以 (2m+4)
         得 H2，再与 2m+4 ≤ 2(m+2) 合取得步乘子 ≤ 16(m+2)²（HAB）。 *)replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (16 ^ Datatypes.S (Datatypes.S m))%nat with (16 * 16 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 8 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 8 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (8 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * (* 左侧 = S m 处的核 × 步乘子；核的不等式即归纳假设 IH。 *)replace ((3 * 3 ^ Datatypes.S m) * 8
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * (2 * Datatypes.S (Datatypes.S m) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 8 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        match goal with |- ?g => idtac "G16:" g end.
        apply Nat.mul_le_mono_r. exact IH.
      * (* 右侧 = S m 处的核 × 16(m+2)²；步乘子 ≤ 16(m+2)² 即 HAB。 *)replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((16 * 16 ^ Datatypes.S m) * 16
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB.

Qed.

(* 族最优核：3^n·98·(2n+1)! ≤ 14^n·135·(n!)²
   （⟺ (98/135)(3/14)^n ≤ (n!)²/(2n+1)!；归纳步经线性证书
     3(2n+3) ≤ 7(n+1)（n≥2）；n=2 处两侧同为 105840，即取等情形） *)
Lemma bl_nat_core14 : forall n : nat,
  (3 ^ n * 98 * fact (2 * n + 1) <= 14 ^ n * 135 * fact n * fact n)%nat.
Proof.
(* 对 n 归纳，归纳步：由 n 到 S n。 *)  induction n as [| n IH].
  - (* 情形 n=0：归约后线性。 *)cbn. lia.
  - (* 情形分析：先处理 S n = 1，再处理 S n ≥ 2。 *)destruct n as [| m].
    + (* 情形 n=0：即 S n = 1，归约后线性。 *)cbn. lia.
    + (* 对 m 分段：m=0 即 S n=2（取等情形），m≥1 走与 bl_nat_core16
         相同的展开链，线性证书为 3(2m+5) ≤ 7(m+2)。 *)destruct (Nat.eq_dec m 0) as [Hm0 | Hmpos].
      { (* 情形 m=0：即 S n = 2，线性证书取等（3·7 = 7·3）。 *)subst m. cbn. lia. }
      { replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (14 ^ Datatypes.S (Datatypes.S m))%nat with (14 * 14 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 7 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 7 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (7 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * (* 左侧 = S m 处的核 × 步乘子；核的不等式即归纳假设 IH。 *)replace ((3 * 3 ^ Datatypes.S m) * 98
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * (2 * Datatypes.S (Datatypes.S m) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 98 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * (* 右侧 = S m 处的核 × 14(m+2)²；步乘子 ≤ 14(m+2)² 即 HAB。 *)replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((14 * 14 ^ Datatypes.S m) * 135
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB. }

Qed.

(* ============================================================ *)
(* §3 Q 层桥接引理：目标常数幂化为单一分式                             *)
(* ============================================================ *)

(* (1/2)·(3/16)^n == (3^n·8 # 1)/(16^n·16 # 1)
   （(1/2)(3/16)^n = 3^n/(2·16^n) = (8·3^n)/(16·16^n)） *)
Lemma bl_half_pow : forall n : nat,
  (1 # 2) * q_pow (3 # 16) n
  == (Z.of_nat (3 ^ n * 8) # 1) / (Z.of_nat (16 ^ n * 16) # 1)%Q.
Proof.
(* 策略：3/16 拆为 3/1 ÷ 16/1 后由 bl_pow_div 分配幂，bl_pZ 换算
     cast，bl_mult_div_assoc 与 bl_qmake_mul 合并因子，lne_div_eq 收束。 *)  intro n.
  replace (3 # 16)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 16 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 16 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 16) ltac:(lia)). lia. }
  rewrite (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 16 # 1) n Hnz),
          (bl_pZ 3 n), (bl_pZ 16 n).
  assert (E1 : (Z.of_nat (3 ^ n * 8))%Z = (8 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (16 ^ n * 16))%Z = (16 * Z.of_nat (16 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (bl_mult_div_assoc (1 # 2)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (16 ^ n) # 1)).
  rewrite <- (bl_qmake_mul 8%Z (Z.of_nat (3 ^ n))).
  rewrite <- (bl_qmake_mul 16%Z (Z.of_nat (16 ^ n))).
  apply lne_div_eq.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (bl_mul_ge1 16 n ltac:(lia)).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (bl_mul_ge1 16 n ltac:(lia)).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* (98/135)·(3/14)^n == (3^n·98 # 1)/(14^n·135 # 1) *)
Lemma bl_opt_pow : forall n : nat,
  (98 # 135) * q_pow (3 # 14) n
  == (Z.of_nat (3 ^ n * 98) # 1) / (Z.of_nat (14 ^ n * 135) # 1)%Q.
Proof.
(* 策略与 bl_half_pow 相同：bl_pow_div 分配幂后合并为单一分式，
     经 bl_mult_div_assoc、bl_qmake_mul 与 lne_div_eq 收束。 *)  intro n.
  replace (3 # 14)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 14 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 14 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 14) ltac:(lia)). lia. }
  rewrite (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 14 # 1) n Hnz),
          (bl_pZ 3 n), (bl_pZ 14 n).
  assert (E1 : (Z.of_nat (3 ^ n * 98))%Z = (98 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (14 ^ n * 135))%Z = (135 * Z.of_nat (14 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (bl_mult_div_assoc (98 # 135)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (14 ^ n) # 1)).
  rewrite <- (bl_qmake_mul 98%Z (Z.of_nat (3 ^ n))).
  rewrite <- (bl_qmake_mul 135%Z (Z.of_nat (14 ^ n))).
  apply lne_div_eq.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (bl_mul_ge1 14 n ltac:(lia)).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (bl_mul_ge1 14 n ltac:(lia)).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* ============================================================ *)
(* §4 主定理                                                         *)
(* ============================================================ *)

(* 主定理（规格参数）：(1/2)·(3/16)^n ≤ lne_B n，QleT' 语句、Set 层 *)
Theorem bl_beta_lower : forall n : nat, QleT' ((1 # 2) * q_pow (3 # 16) n) (lne_B n).
Proof.
(* 策略：bl_half_pow 化左侧为单一分式，lne_B_closed 展开右侧，
     bl_div_le 归约到 bl_nat_core16 的纯 nat 阶乘不等式。 *)  intro n. apply Qle_to_QleT'.
  rewrite bl_half_pow, lne_B_closed.
  apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 16 n ltac:(lia)). lia.
  - apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (bl_nat_core16 n) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 族最优：(98/135)·(3/14)^n ≤ lne_B n，n=2/3 同时取等且步比尾最小 3/14 使其不可改进 *)
Theorem bl_beta_lower_opt : forall n : nat, QleT' ((98 # 135) * q_pow (3 # 14) n) (lne_B n).
Proof.
(* 策略与 bl_beta_lower 相同：bl_opt_pow 与 lne_B_closed 化为分式，
     bl_div_le 归约到 bl_nat_core14。 *)  intro n. apply Qle_to_QleT'.
  rewrite bl_opt_pow, lne_B_closed.
  apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 14 n ltac:(lia)). lia.
  - apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (bl_nat_core14 n) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 变体偏移（(1+t) 侧）：(1/4)·(3/32)^n ≤ 2^{−(n+1)}·lne_B n。
   注：右端 2^{−(n+1)}·lne_B n 是变体积分 I'_n 的可证载体下界形
   （I'_n 本体的下界需全段逐点机制，不在本件范围）；
   (1/4)(3/32)^n = 2^{−(n+2)}(3/16)^n，即由主定理直接倍半推得。 *)
Theorem bl_variant_shift : forall n : nat,
  QleT' ((1 # 4) * q_pow (3 # 32) n) (q_pow (1 # 2) (Datatypes.S n) * lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (1 # 2) (Datatypes.S n) * ((1 # 2) * q_pow (3 # 16) n))).
  - (* 恒等式：(1/2)^{S n}·((1/2)(3/16)^n) = (1/4)·((1/2)^n(3/16)^n)
       = (1/4)(3/32)^n，幂的合并经 bl_qpow_mul。 *)apply qeq_imp_qle.
    rewrite q_pow_succ.
    assert (E3 : ((1 # 2) * q_pow (1 # 2) n * ((1 # 2) * q_pow (3 # 16) n))%Q
                 == (((1 # 2) * (1 # 2)) * (q_pow (1 # 2) n * q_pow (3 # 16) n))%Q) by ring.
    rewrite E3.
    assert (E2 : ((1 # 2) * (1 # 2))%Q == (1 # 4)) by reflexivity.
    rewrite E2.
    rewrite <- (bl_qpow_mul (1 # 2) (3 # 16) n).
    reflexivity.
  - (* 两侧乘非负因子 q_pow (1 # 2) (S n) 保序（bl_mlc），再用主定理
       bl_beta_lower 与非零性 q_pow_nonneg。 *)apply (bl_mlc _ _ (q_pow (1 # 2) (Datatypes.S n))).
    + apply QleT'_to_Qle. apply bl_beta_lower.
    + apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* §5 数值锚（n=0..3 的 vm_compute 实例与 lne_B 值见证）               *)
(* ============================================================ *)

Lemma bl_spec_anchor0 : QleT' ((1 # 2) * q_pow (3 # 16) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor1 : QleT' ((1 # 2) * q_pow (3 # 16) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor2 : QleT' ((1 # 2) * q_pow (3 # 16) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor3 : QleT' ((1 # 2) * q_pow (3 # 16) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor0 : QleT' ((98 # 135) * q_pow (3 # 14) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor1 : QleT' ((98 # 135) * q_pow (3 # 14) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor2 : QleT' ((98 # 135) * q_pow (3 # 14) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor3 : QleT' ((98 # 135) * q_pow (3 # 14) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* 变体偏移在 n=3 的数值锚：左端 (1/4)(3/32)³ = 27/131072，右端 2^{−3}·(1/140) = 1/1120 *)
Lemma bl_var_anchor3 : QleT' ((1 # 4) * q_pow (3 # 32) 3) (q_pow (1 # 2) 3 * lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* lne_B 数值见证（经 lne_B_closed）：lne_B 1 = 1/6, 2 → 1/30, 3 → 1/140 *)
Lemma bl_value1 : QeqT (lne_B 1) (1 # 6).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value2 : QeqT (lne_B 2) (1 # 30).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value3 : QeqT (lne_B 3) (1 # 140).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

(* ============================================================ *)
(* §6 提取与假设审计                                                  *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bl_beta_lower bl_beta_lower_opt bl_variant_shift
  bl_spec_anchor3 bl_var_anchor3 lne_B q_pow.

Print Assumptions bl_beta_lower.
Print Assumptions bl_beta_lower_opt.
Print Assumptions bl_variant_shift.
