(* ============================================================ *)
(* BetaLower.v — 席位切片代理M（批次 E-STAGING-D025r，20260918）    *)
(*                                                               *)
(* 使命：P5 载体下界首攻切片（T122 派席④；T124 §三 改判后即可开工）。 *)
(*   P1b「段上逐点正⟹积分正」路线经 T124 死亡证书注销，本席按        *)
(*   T124 §二(a)+(b) 合流改走：系数级/Beta 闭式 + 纯阶乘不等式，     *)
(*   零段上逐点化。与在飞变体切片划清接口：只交下界，不碰恒等式。     *)
(*                                                               *)
(* 承载形定向（按 T118 勘误后真恒等式）：                            *)
(*   I_n = ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt 与 lne_B n 的关系：        *)
(*   真恒等式 ln2 − x'_n = I_n/(2^{n+1}·q̃_n)（分母无平方，T118 §0）； *)
(*   (1−t/2)^{−(n+1)} ≥ 1 逐点（2−t ≤ 2）且具正系数二项级数，        *)
(*   故 I_n ≥ lne_B n = (n!)²/(2n+1)!（Beta 闭式，lne_B_closed）。  *)
(*   I_n 本体（有理被积函数）超出一期 pint_ 多项式面（Ln2Escape 头注  *)
(*   同判），其积分对象不在库内——本席交付以 lne_B 为承载的           *)
(*   c·σ^n 下界，即 I_n 下界的可证承载形；I_n ≥ lne_B n 的最后一步   *)
(*   需全段逐点机（T124 §二(c) 真命题残面）或正系数级数机，精确        *)
(*   偏移如实登记于 T125 报告，不虚报。                              *)
(*                                                               *)
(* 数值锚定（n=0..3，vm_compute 哨兵见 §5）：                        *)
(*   lne_B: 1, 1/6, 1/30, 1/140；步比 (n+1)/(2(2n+3))：             *)
(*   1/6, 1/5, 3/14, 2/9, 5/22（尾min=3/14 在 n=2）。               *)
(*   ① 规格档 c=1/2, σ=3/16（T97 §4-P5 原目标）：n=0..3 全过。       *)
(*   ② 族最优档 c=98/135, σ=3/14：n=2、n=3 双缚等号                 *)
(*      （98/135·(3/14)² = 1/30 = lne_B 2；×(3/14) = 1/140 =         *)
(*      lne_B 3）——任何 c·σ^n 下界族中 σ ≤ min_{n≥2} 步比 = 3/14，    *)
(*      故此对在「n≥2 缚」意义下不可改进（精确最优化记录）。          *)
(*   ③ 变体偏移件（(1+t) 面）：2^{−(n+1)}·lne_B n ≥ (1/4)(3/32)^n    *)
(*      = 2^{−(n+2)}·(3/16)^n，与 T97 §三 Λ_n 下界需求 2^{−(n+2)}     *)
(*      (3/16)^n 精确匹配。                                          *)
(*                                                               *)
(* 交付件（bl_ 前缀，语句面全 Set：QleT'/QeqT；Q 层 Prop 仅内件        *)
(* 脚手架，UpReq 系/Ln2Escape 同款纪律）：                            *)
(*   主件  bl_beta_lower      : (1/2)·(3/16)^n ≤ lne_B n（QleT'）    *)
(*   最优  bl_beta_lower_opt  : (98/135)·(3/14)^n ≤ lne_B n（QleT'） *)
(*   变体  bl_variant_shift   : (1/4)·(3/32)^n ≤ 2^{−(n+1)}·lne_B n  *)
(*   锚哨  §5 n=0..3 vm_compute 实例 ×9 + 值见证 ×3                 *)
(* 证明路线：Beta 闭式（lne_B_closed，两参数 Beta 归纳的对角特化，     *)
(*   配方溯沿 PadeErrorIntegral pei_beta 族/Ln2Escape lne_beta_value） *)
(*   → sif_qfact_Z 桥 → 纯 nat 阶乘不等式归纳（bl_nat_core16/14，     *)
(*   核证书 3(2n+3) ≤ 8(n+1) / ≤ 7(n+1) 线性 lia，免 Psatz）→        *)
(*   除法比较器 bl_div_le（lne_div_eq 同构配 bl_div_ge 镜像）。       *)
(* 依赖：S02_CauchyComplete（QleT'/QltT 桥）、S03_QExp（q_pow/q_fact）、*)
(*   SumInvFactEscape（sif_qfact_Z）、Ln2Escape（lne_B 三件套承载，    *)
(*   side 根现编）。PadeErrorIntegral 原件因信任根缺链不直接消费       *)
(*   （Ln2Escape 头注同判），Beta 闭式走其移植面。                   *)
(* 红线：零公理声明词、零认授收口、零经典逻辑、零 Prop 语句位；         *)
(*   提取探针 Obj.magic=0。                                          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Arith.Factorial.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import PolyIntegral.
Require Import Ln2Escape.

(* ============================================================ *)
(* §1 Q 层支撑件（内件，Prop 面仅脚手架）                              *)
(* ============================================================ *)

(* k^n ≥ 1（正底幂非零下界；喂 Qlt cast 腿用） *)
Lemma bl_mul_ge1 : forall k n : nat, (1 <= k)%nat -> (1 <= k ^ n)%nat.
Proof.
  intros k n Hk. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Qmake 乘法桥：(a#1)·(b#1) == (a·b#1)（定义级） *)
Lemma bl_qmake_mul : forall a b : Z, (a # 1) * (b # 1) == (a * b # 1)%Q.
Proof.
  intros a b. unfold Qmult. cbn [Pos.mul]. reflexivity.
Qed.

(* Qinv 对乘积分配（双非零前提；bl_pow_div/桥件用） *)
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

(* 正底幂非零：~ (q_pow y n == 0) *)
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

(* 整数 cast 幂桥：q_pow (k#1) n == (k^n # 1) *)
Lemma bl_pZ : forall k n : nat, q_pow (Z.of_nat k # 1) n == (Z.of_nat (k ^ n) # 1)%Q.
Proof.
  intros k n. induction n as [| n IH].
  - reflexivity.
  - rewrite q_pow_succ, IH, Nat.pow_succ_r'.
    unfold Qmult. cbn [Pos.mul]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 左乘保序：x ≤ y、0 ≤ z ⟹ z·x ≤ z·y（Qmult_le_compat_r 的左乘封装） *)
Lemma bl_mlc : forall x y z : Q, Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H Hz.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  exact (Qmult_le_compat_r x y z H Hz).
Qed.

(* 除法下界比较器（lne_div_le_inv 镜像）：0 < y、z·y ≤ x ⟹ z ≤ x/y *)
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
(* §2 纯 nat 阶乘不等式核（lne_nat_core 同型；核证书线性 lia）          *)
(* ============================================================ *)

(* 主件核：3^n·8·(2n+1)! ≤ 16^n·16·(n!)²
   （⟺ (1/2)(3/16)^n ≤ (n!)²/(2n+1)!；步乘子 3(2n+3)(2n+2) ≤ 16(n+1)²
     经线性证书 3(2n+3) ≤ 8(n+1)（n≥1）×(2n+2) 达成） *)
Lemma bl_nat_core16 : forall n : nat,
  (3 ^ n * 8 * fact (2 * n + 1) <= 16 ^ n * 16 * fact n * fact n)%nat.
Proof.
  induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
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
      * replace ((3 * 3 ^ Datatypes.S m) * 8
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * (2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1)))%nat
          with ((3 ^ Datatypes.S m * 8 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        match goal with |- ?g => idtac "G16:" g end.
        apply Nat.mul_le_mono_r. exact IH.
      * replace ((16 * 16 ^ Datatypes.S m) * 16
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_r. exact HAB.

Qed.

(* 最优档核：3^n·98·(2n+1)! ≤ 14^n·135·(n!)²
   （⟺ (98/135)(3/14)^n ≤ (n!)²/(2n+1)!；步乘子 3(2n+3)(2n+2) ≤ 14(n+1)²
     经线性证书 3(2n+3) ≤ 7(n+1)（n≥2）×(2n+2) 达成；n=2 等号 105840） *)
Lemma bl_nat_core14 : forall n : nat,
  (3 ^ n * 98 * fact (2 * n + 1) <= 14 ^ n * 135 * fact n * fact n)%nat.
Proof.
  induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
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
      * replace ((3 * 3 ^ Datatypes.S m) * 98
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * (2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1)))%nat
          with ((3 ^ Datatypes.S m * 98 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * replace ((14 * 14 ^ Datatypes.S m) * 135
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_r. exact HAB.

Qed.

(* ============================================================ *)
(* §3 Q 桥：目标常数幂 → 单除法 Z cast 形                               *)
(* ============================================================ *)

(* (1/2)·(3/16)^n == (3^n·8 # 1)/(16^n·16 # 1)
   （(1/2)(3/16)^n = 3^n/(2·16^n) = (8·3^n)/(16·16^n)） *)
Lemma bl_half_pow : forall n : nat,
  (1 # 2) * q_pow (3 # 16) n
  == (Z.of_nat (3 ^ n * 8) # 1) / (Z.of_nat (16 ^ n * 16) # 1)%Q.
Proof.
  intro n.
  rewrite bl_pow_div, (bl_pZ 3 n), (bl_pZ 16 n).
  assert (E1 : (Z.of_nat (3 ^ n * 8))%Z == (8 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (16 ^ n * 16))%Z == (16 * Z.of_nat (16 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  apply lne_div_eq.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 16 n ltac:(lia)). lia.
    + unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 16 n ltac:(lia)). lia.
  - rewrite <- (bl_qmake_mul 16%Z (Z.of_nat (16 ^ n))).
    rewrite <- (bl_qmake_mul 8%Z (Z.of_nat (3 ^ n))).
    assert (E16 : (16 # 1) == ((8 # 1) * (2 # 1))%Q)
      by (unfold Qeq; cbn [Qnum Qden Qmult Pos.mul]; lia).
    rewrite E16.
    unfold Qdiv. ring.
Qed.

(* (98/135)·(3/14)^n == (3^n·98 # 1)/(14^n·135 # 1) *)
Lemma bl_opt_pow : forall n : nat,
  (98 # 135) * q_pow (3 # 14) n
  == (Z.of_nat (3 ^ n * 98) # 1) / (Z.of_nat (14 ^ n * 135) # 1)%Q.
Proof.
  intro n.
  rewrite bl_pow_div, (bl_pZ 3 n), (bl_pZ 14 n).
  assert (E1 : (Z.of_nat (3 ^ n * 98))%Z == (98 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (14 ^ n * 135))%Z == (135 * Z.of_nat (14 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  apply lne_div_eq.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 14 n ltac:(lia)). lia.
    + unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 14 n ltac:(lia)). lia.
  - rewrite <- (bl_qmake_mul 135%Z (Z.of_nat (14 ^ n))).
    rewrite <- (bl_qmake_mul 98%Z (Z.of_nat (3 ^ n))).
    assert (E3 : ((98 # 135) * ((Z.of_nat (3 ^ n) # 1) * Qinv (Z.of_nat (14 ^ n) # 1))
                    * ((135 # 1) * (Z.of_nat (14 ^ n) # 1)))%Q
                 == (((98 # 135) * (135 # 1))
                       * ((Z.of_nat (3 ^ n) # 1) * (Z.of_nat (14 ^ n) # 1)
                            * Qinv (Z.of_nat (14 ^ n) # 1)))%Q) by ring.
    rewrite E3.
    assert (E135 : (98 # 135) * (135 # 1) == (98 # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qmult Pos.mul]; lia).
    rewrite E135.
    unfold Qdiv. ring.
Qed.

(* ============================================================ *)
(* §4 主件（Set 面）                                                   *)
(* ============================================================ *)

(* 主件（T97 §4-P5 规格档）：(1/2)·(3/16)^n ≤ lne_B n *)
Theorem bl_beta_lower : forall n : nat, QleT' ((1 # 2) * q_pow (3 # 16) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite bl_half_pow, lne_B_closed.
  apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 16 n ltac:(lia)). lia.
  - apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (bl_nat_core16 n) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 最优档（族最优对，n=2/3 双缚等号）：(98/135)·(3/14)^n ≤ lne_B n *)
Theorem bl_beta_lower_opt : forall n : nat, QleT' ((98 # 135) * q_pow (3 # 14) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite bl_opt_pow, lne_B_closed.
  apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden]. pose proof (bl_mul_ge1 14 n ltac:(lia)). lia.
  - apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (bl_nat_core14 n) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 变体偏移件（(1+t) 面）：(1/4)·(3/32)^n ≤ 2^{−(n+1)}·lne_B n。
   注：右端 2^{−(n+1)}·lne_B n 是 (1+t)^{n+1} 变体积分 I'_n 的可证折叠
   承载（I'_n ≥ 2^{−(n+1)}·lne_B n 需全段逐点机，精确偏移登记 T125）；
   (1/4)(3/32)^n = 2^{−(n+2)}(3/16)^n 与 T97 §三 Λ_n 需求精确匹配。 *)
Theorem bl_variant_shift : forall n : nat,
  QleT' ((1 # 4) * q_pow (3 # 32) n) (q_pow (1 # 2) (Datatypes.S n) * lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (1 # 2) (Datatypes.S n) * ((1 # 2) * q_pow (3 # 16) n))).
  - apply (bl_mlc _ _ (q_pow (1 # 2) (Datatypes.S n))).
    + apply QleT'_to_Qle. apply bl_beta_lower.
    + apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
  - apply qeq_imp_qle.
    rewrite q_pow_succ.
    assert (E3 : ((1 # 2) * q_pow (1 # 2) n * ((1 # 2) * q_pow (3 # 16) n))%Q
                 == (((1 # 2) * (1 # 2)) * (q_pow (1 # 2) n * q_pow (3 # 16) n))%Q) by ring.
    rewrite E3.
    assert (E2 : ((1 # 2) * (1 # 2))%Q == (1 # 4)) by reflexivity.
    rewrite E2.
    rewrite <- (bl_qpow_mul (1 # 2) (3 # 16) n).
    reflexivity.
Qed.

(* ============================================================ *)
(* §5 数值锚哨（n=0..3 vm_compute 实例 + 载体值见证）                    *)
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

(* 变体折叠 n=3 锚：2^{-4}·(1/140) = 1/2240 ≥ 27/131072 *)
Lemma bl_var_anchor3 : QleT' ((1 # 4) * q_pow (3 # 32) 3) (q_pow (1 # 2) 3 * lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* 载体值见证（Beta 闭式数值面）：1, 1/6, 1/30, 1/140 *)
Lemma bl_value1 : QeqT (lne_B 1) (1 # 6).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value2 : QeqT (lne_B 2) (1 # 30).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value3 : QeqT (lne_B 3) (1 # 140).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

(* ============================================================ *)
(* §6 提取探针 + 公理面自审                                             *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bl_beta_lower bl_beta_lower_opt bl_variant_shift
  bl_spec_anchor3 bl_var_anchor3 lne_B q_pow.

Print Assumptions bl_beta_lower.
Print Assumptions bl_beta_lower_opt.
Print Assumptions bl_variant_shift.
