(* 模块：b1_carrier_beta.v —— arctan 截断积分的段载体（单积分版）。
   使命：把截断被积式 xⁿ(1−x)ⁿ·A(n,M,−x²)（件② b1_ps 的核积）落成
   [0,1] 单积分段载体：第 m 段 = 系数 C(n+m,n)·(−1)^m × 因子表
   t^{n+2m}(1−t)ⁿ，施加一次 pint_integral 得 Beta 闭式精确值。
   zb2 双积分载体（abl_z2_itg_carrier，段=系数×双因子表·两次 pint_integral）
   的单积分同位再铸：一次复合（Beukers-arctan 核只一维），免交换积分次序。
   面：①段精确值（Beta 闭式）；②带号段（(−1)^m 因子）；③段正性
   （pei_beta_pos）；④Beta ≤ 1 衰减肢（沿 pei_fact_le）；⑤段列与
   ρ(n,M) 部分和承载（聚合单表面沿 zb2 先例如实不含）。
   依赖：S01/S02/S03、BeukersLists（bkC/bk_psQ）、PolyIntegral（pint_*）、
   PadeErrorIntegral（pei_list/pei_beta_value/pei_beta_pos/pei_fact_le/q_fact）、
   b1_trunc_master（b1_ps）。
   构造性：语句面全 Set（QeqT/QltT/Qle）；证明体线性性与 Beta 闭式直链，
   零公理、零经典逻辑。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" b1_carrier_beta.v。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield Lia Lists.List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import BeukersLists.
Require Import PolyIntegral.
Require Import PadeErrorIntegral.
Require Import b1_kernel_pointwise.
Require Import b1_trunc_master.

Open Scope Q_scope.
Open Scope list_scope.

(* ========== §1 段载体定义 ========== *)

(* 第 m 段（正核）：系数 C(n+m,n) × 因子表 t^{n+2m}(1−t)ⁿ
   （= xⁿ(1−x)ⁿ·x^{2m} 的 [0,1] 系数表） *)
Definition b1_seg_poly (n m : nat) : list Q :=
  pint_scale ((Z.of_nat (bkC (n + m) n) # 1)) (pei_list (n + 2 * m) n).

(* 第 m 段（带号）：再乘 (−1)^m（A(n,M,−x²) 展开的交错符） *)
Definition b1_seg_signed (n m : nat) : list Q :=
  pint_scale (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m))
             (pei_list (n + 2 * m) n).

(* 段的 Beta 闭式精确值（统一引用形） *)
Definition b1_seg_beta (n m : nat) : Q :=
  (q_fact (n + 2 * m) * q_fact n) / q_fact (Datatypes.S (n + 2 * m + n)).

(* ========== §2 段精确值（单积分 Beta 闭式） ========== *)

(* 正核段值（Qeq 核）：∫₀¹ C·t^{n+2m}(1−t)ⁿ = C·(n+2m)!·n!/(2n+2m+1)! *)
Lemma b1_seg_val_eq : forall n m : nat,
  pint_integral (b1_seg_poly n m) ==
  ((Z.of_nat (bkC (n + m) n) # 1) * b1_seg_beta n m)%Q.
Proof.
  intros n m. unfold b1_seg_poly, b1_seg_beta.
  assert (Hsc := qeqT_imp_qeq _ _
    (pint_integral_scale ((Z.of_nat (bkC (n + m) n) # 1))
       (pei_list (n + 2 * m) n))).
  rewrite Hsc.
  rewrite (pei_beta_value (n + 2 * m) n).
  replace (n + 2 * m + n + 1)%nat with (Datatypes.S (n + 2 * m + n))%nat by lia.
  reflexivity.
Qed.

(* 正核段值（Set 证书形） *)
Theorem b1_seg_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_poly n m))
       (((Z.of_nat (bkC (n + m) n) # 1) * b1_seg_beta n m)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_seg_val_eq n m).
Qed.

(* 带号段值：乘 (−1)^m 因子 *)
Lemma b1_seg_signed_val_eq : forall n m : nat,
  pint_integral (b1_seg_signed n m) ==
  (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m) * b1_seg_beta n m)%Q.
Proof.
  intros n m. unfold b1_seg_signed.
  assert (Hsc := qeqT_imp_qeq _ _
    (pint_integral_scale (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m))
       (pei_list (n + 2 * m) n))).
  rewrite Hsc.
  rewrite (pei_beta_value (n + 2 * m) n).
  replace (n + 2 * m + n + 1)%nat with (Datatypes.S (n + 2 * m + n))%nat by lia.
  reflexivity.
Qed.

Theorem b1_seg_signed_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_signed n m))
       (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m * b1_seg_beta n m)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_seg_signed_val_eq n m).
Qed.

(* ========== §3 段正性与 Beta 衰减肢 ========== *)

(* 段严格正（核正性：[0,1] 上 t^{a}(1−t)^b > 0 的积分） *)
Theorem b1_seg_pos : forall a b : nat,
  QltT 0 (pint_integral (pei_list a b)).
Proof.
  intros a b. exact (Qlt_to_QltT 0 _ (pei_beta_pos a b)).
Qed.

(* Beta ≤ 1 衰减肢：n!·(n+2m)! ≤ (2n+2m+1)!（沿 pei_fact_le） *)
Theorem b1_seg_beta_le1 : forall n m : nat,
  Qle (b1_seg_beta n m) 1.
Proof.
  intros n m. unfold b1_seg_beta.
  apply pei_div_le_1.
  - apply q_fact_pos.
  - rewrite (Qmult_comm (q_fact (n + 2 * m)) (q_fact n)).
    replace (n + 2 * m + n)%nat with (2 * n + 2 * m)%nat by lia.
    apply pei_fact_le.
Qed.

(* ========== §4 段列与部分和承载 ρ(n,M) ========== *)

(* 带号段值的有理和 ρ(n,M) = Σ_{m<S M} (−1)^m·C(n+m,n)·Beta(n,m)
   （截断多项部分 [0,1] 积分值的承载；聚合单系数表面沿 zb2_itg_carrier
   头注先例如实不含——逐项相加错位 Horner 位） *)
Fixpoint b1_rho (n M : nat) : Q :=
  match M with
  | Datatypes.O => (Z.of_nat (bkC (n + 0) n) # 1) * b1_seg_beta n 0
  | Datatypes.S M' => b1_rho n M'
                      + ((Z.of_nat (bkC (n + Datatypes.S M') n) # 1)
                         * q_pow (- 1)%Q (Datatypes.S M') * b1_seg_beta n (Datatypes.S M'))%Q
  end.

(* 末项剥离（定义性） *)
Lemma b1_rho_unfold : forall n M : nat,
  b1_rho n (Datatypes.S M)
  == (b1_rho n M
      + ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
         * q_pow (- 1)%Q (Datatypes.S M) * b1_seg_beta n (Datatypes.S M))%Q).
Proof. intros n M. reflexivity. Qed.

(* 段列（头为 m = M，降序至 m = 0）——zb2_segl 单积分同位 *)
Fixpoint b1_segl (n M : nat) : list (Q * list Q) :=
  match M with
  | Datatypes.O =>
      (((Z.of_nat (bkC (n + 0) n) # 1) * q_pow (- 1)%Q 0,
        pei_list (n + 2 * 0) n) :: nil)%list
  | Datatypes.S M' =>
      (((Z.of_nat (bkC (n + Datatypes.S M') n) # 1)
        * q_pow (- 1)%Q (Datatypes.S M'),
        pei_list (n + 2 * Datatypes.S M') n) :: b1_segl n M')%list
  end.

(* 段列逐点求值 = 系数 × Horner 值 *)
Definition b1_seg_pt (seg : (Q * list Q)) (x : Q) : Q :=
  (fst seg) * pint_eval (snd seg) x.

(* 段积分值与段系数×Beta 值一致（逐段） *)
Lemma b1_segl_val_eq : forall n m : nat,
  pint_integral (b1_seg_signed n m) ==
  ((fst (hd (0%Q, nil)%list (b1_segl n m))) * b1_seg_beta n m)%Q.
Proof.
  intros n m. destruct m as [| m'].
  - unfold b1_seg_signed.
    assert (Hhd : fst (hd (0%Q, nil)%list (b1_segl n 0))
                  == ((Z.of_nat (bkC (n + 0) n) # 1) * q_pow (- 1)%Q 0)%Q)
      by reflexivity.
    rewrite Hhd.
    exact (b1_seg_signed_val_eq n 0).
  - unfold b1_seg_signed.
    assert (Hhd : fst (hd (0%Q, nil)%list (b1_segl n (Datatypes.S m')))
                  == ((Z.of_nat (bkC (n + Datatypes.S m') n) # 1)
                      * q_pow (- 1)%Q (Datatypes.S m'))%Q)
      by reflexivity.
    rewrite Hhd.
    exact (b1_seg_signed_val_eq n (Datatypes.S m')).
Qed.

Theorem b1_segl_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_signed n m))
       ((fst (hd (0%Q, nil)%list (b1_segl n m))) * b1_seg_beta n m)%Q.
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_segl_val_eq n m).
Qed.

(* ========== §5 数值锚（独立复算比对点） ========== *)

(* 锚一：n=1, m=0：C(1,1)·B(2,2) = 1·(1!·1!/3!) = 1/6 *)
Lemma b1_seg_anchor_10 :
  QeqT (pint_integral (b1_seg_poly 1 0)) (1 # 6).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚二：n=1, m=1：C(2,1)·(−1)¹·B(4,2) = 2·(−1)·(3!·1!/5!) = −1/10 *)
Lemma b1_seg_anchor_11 :
  QeqT (pint_integral (b1_seg_signed 1 1)) (-(1 # 10)).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚三：ρ(1,1) = 1/6 − 1/10 = 1/15 *)
Lemma b1_rho_anchor_11 :
  QeqT (b1_rho 1 1) (1 # 15).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚四：Beta ≤ 1 实例：B(4,2) = 1/20 ≤ 1 *)
Lemma b1_seg_beta_anchor :
  QeqT (b1_seg_beta 1 1) (1 # 20).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* ========== §6 在件检验与假设审计 ========== *)

Check b1_seg_val.
Check b1_seg_signed_val.
Check b1_seg_pos.
Check b1_seg_beta_le1.
Check b1_rho_unfold.
Check b1_segl_val.

Print Assumptions b1_seg_val.
Print Assumptions b1_seg_signed_val.
Print Assumptions b1_seg_pos.
Print Assumptions b1_seg_beta_le1.
Print Assumptions b1_segl_val.
