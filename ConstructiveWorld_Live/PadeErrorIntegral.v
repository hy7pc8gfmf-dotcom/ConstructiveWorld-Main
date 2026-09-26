(* ============================================================ *)
(* PadeErrorIntegral.v —— 使命：Padé [n/n] 误差余项积分表示四件构造性落地  *)
(*   （UpReqPadeExp.v:193 显式假设四件 + PadeDenPosA.v:26 遗留 c 的       *)
(*   消解）。原阻塞 = 构造性积分基建缺位；现 PolyIntegral.v 已在册        *)
(*   （[0,1] 多项式 Q 系数构造性定积分），阻塞解除。                     *)
(* 语句形判定：被积函数 tⁿ(1−t)ⁿ·e^{tx} 中 e^{tx} 非多项式，库内构造性    *)
(*   载体为 exp_partial M (x·t) = Σ_{k≤M} (x·t)^k/k!（S03:39 在册）。     *)
(*   故四件落地为「截断指数被积函数」构造性有限核：                       *)
(*   pei_eb_list n x M := Σ_{k=0}^{M} (x^k/k!)·list(t^{n+k}(1−t)ⁿ)       *)
(*   ——其逐点语义恰为 tⁿ(1−t)ⁿ·exp_partial M (x·t)。                    *)
(*   ① pei_integral_pos：0 ≤ x ⟹ ∫₀¹ > 0（k=0 项 Beta 严格正接续）；    *)
(*   ② pei_eb_value：∫ 闭式 = Σ x^k/k!·Beta(n+k+1,n+1)——余项积分表示    *)
(*      的构造性泰勒系数对接件（精确全形 e^x−P/Q=… 需极限交换，          *)
(*      B4TwoStage 已判 LPO 墙，显式假设维持，本件交付其有限核）；        *)
(*   ③ pei_error_mag_pos + pei_error_lead_integral：符号 =(−1)^n 的      *)
(*      模长正性 + 首项因式分解（(−1)^n·x^{2n+1}/(2n)!·∫ 形）；         *)
(*   ④ pei_eb_le：显式界 ∫ ≤ exp_partial M x（exp 截断一致控制）。      *)
(* 数学核心：Beta 族闭式 ∫₀¹ t^a(1−t)^b dt == a!·b!/(a+b+1)!，          *)
(*   经 (1−t)^{b+1} = (1−t)^b − t·(1−t)^b 的系数列表递归                 *)
(*   pei_list a (S b) = ztail(L a b) ⊕ (−1)·L (S a) b（等长垫零）        *)
(*   两参数归纳直取，无 Pascal/二项式系数需求。                          *)
(* 依赖：Stdlib QArith/Lists/Arith/ZArith/Lia Setoid；S01_BaseRing        *)
(*   S02_CauchyComplete S03_QExp PolyIntegral UpReqB4TwoStage。           *)
(* 构造性注记：① 零承认面（全件 Qed 真证，依赖全为在册 Closed 件）；     *)
(*   ② 语句面 Set（主件 Qeq/QltT/QleT'；Qle/Qlt 仅支撑件内面）；         *)
(*   ③ 非平凡（Beta 闭式两参数归纳 + 有理域交叉相消引擎）；               *)
(*   ④ 可提取（G3 检验独立文件实测）。前缀 pei_ 全库防撞 grep=0。         *)
(* 编译配方：coqc 9.1 直调（vo 树内 -Q . "" 平面命名空间），信任缓存前置。 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import UpReqB4TwoStage.

(* ============================================================ *)
(* §A 有理域引擎（非零/交叉相消/除法面）                                *)
(* ============================================================ *)

Lemma pei_mult_canc : forall a b c : Q, a * c == b * c -> ~ (c == 0%Q) -> a == b.
Proof.
  intros a b c H Hc0.
  apply (proj1 (Qmult_inj_r a b c Hc0) H).
Qed.

Lemma pei_mult_nz : forall x y : Q, ~ (x == 0%Q) -> ~ (y == 0%Q) -> ~ (x * y == 0%Q).
Proof.
  intros x y Hx Hy Heq. apply Hx.
  apply (pei_mult_canc x 0%Q y).
  - rewrite Qmult_0_l. exact Heq.
  - exact Hy.
Qed.

Lemma pei_div_eq : forall p q r s : Q,
  Qlt 0 q -> Qlt 0 s -> p * s == q * r -> p / q == r / s.
Proof.
  intros p q r s Hq Hs H.
  assert (Hqz : ~ (q == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q q Hq). exact (Qeq_sym _ _ E). }
  assert (Hsz : ~ (s == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ E). }
  assert (Hqsz : ~ (q * s == 0%Q)) by (apply (pei_mult_nz q s Hqz Hsz)).
  apply (pei_mult_canc (p / q) (r / s) (q * s)).
  - unfold Qdiv.
    assert (E1 : (p * Qinv q) * (q * s) == (p * Qinv q * q) * s) by ring.
    rewrite E1.
    assert (E2 : (p * Qinv q * q) * s == p * s).
    { rewrite <- (Qmult_assoc p (Qinv q) q). rewrite (Qmult_comm (Qinv q) q).
      rewrite (Qmult_inv_r q Hqz). ring. }
    rewrite E2.
    assert (E3 : (r * Qinv s) * (q * s) == (r * Qinv s * s) * q) by ring.
    rewrite E3.
    assert (E4 : (r * Qinv s * s) * q == q * r).
    { rewrite <- (Qmult_assoc r (Qinv s) s). rewrite (Qmult_comm (Qinv s) s).
      rewrite (Qmult_inv_r s Hsz). ring. }
    rewrite E4. exact H.
  - exact Hqsz.
Qed.

Lemma pei_div_sub : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> a / b - c / d == (a * d - c * b) / (b * d).
Proof.
  intros a b c d Hb Hd.
  assert (Hbz : ~ (b == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q b Hb). exact (Qeq_sym _ _ E). }
  assert (Hdz : ~ (d == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q d Hd). exact (Qeq_sym _ _ E). }
  assert (Hbdz : ~ (b * d == 0%Q)) by (apply (pei_mult_nz b d Hbz Hdz)).
  assert (Hbd1 : (b * d) * Qinv (b * d) == 1%Q) by (apply Qmult_inv_r; exact Hbdz).
  apply (pei_mult_canc (a / b - c / d) ((a * d - c * b) / (b * d)) (b * d)).
  - unfold Qdiv.
    assert (E1 : (a * Qinv b - c * Qinv d) * (b * d)
                 == a * (Qinv b * b) * d - c * (Qinv d * d) * b) by ring.
    rewrite E1.
    rewrite <- (Qmult_assoc (a * d - c * b) (Qinv (b * d)) (b * d)).
    rewrite (Qmult_comm (Qinv (b * d)) (b * d)). rewrite Hbd1.
    rewrite (Qmult_comm (Qinv b) b).
    assert (Hb1 : b * Qinv b == 1%Q) by (apply Qmult_inv_r; exact Hbz).
    rewrite Hb1.
    rewrite (Qmult_comm (Qinv d) d).
    assert (Hd1 : d * Qinv d == 1%Q) by (apply Qmult_inv_r; exact Hdz).
    rewrite Hd1.
    ring.
  - exact Hbdz.
Qed.

Lemma pei_div_le_1 : forall a c : Q, Qlt 0 c -> Qle a c -> Qle (a / c) 1%Q.
Proof.
  intros a c Hc0 Hac. unfold Qdiv.
  apply (Qle_trans _ (c * Qinv c) 1%Q).
  - apply (Qmult_le_compat_r a c).
    + exact Hac.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hc0.
  - apply qeq_le. apply Qmult_inv_r.
    intro E. apply (Qlt_not_eq 0%Q c Hc0). exact (Qeq_sym _ _ E).
Qed.

Lemma pei_qeq_lt : forall a b c : Q, a == b -> Qlt c a -> Qlt c b.
Proof.
  intros a b c Hab Hca. apply (Qlt_le_trans c a b).
  - exact Hca.
  - apply qeq_le. exact Hab.
Qed.

(* REV-R1 新增：除法-乘法换位（Qdiv 为 ring 原子，跨原子恒等
   须显式归位——pei_eb_eval 步项两侧 /-原子形不同时所需）。 *)
Lemma pei_div_mul_shift : forall X Y Z : Q, X * Z / Y == (X / Y) * Z.
Proof.
  intros X Y Z. unfold Qdiv. ring.
Qed.

Lemma pei_lt_le_plus : forall a b : Q, Qlt 0 a -> Qle 0 b -> Qlt 0 (a + b).
Proof.
  intros a b Ha Hb.
  apply (Qlt_le_trans 0%Q a (a + b)).
  - exact Ha.
  - apply (Qle_trans a (a + 0) (a + b)).
    + apply qeq_le. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hb.
Qed.

Lemma pei_ZS1_nz : forall k : nat, ~ ((Z.of_nat (Datatypes.S k) # 1)%Q == 0%Q).
Proof.
  intro k. intro E. unfold Qeq in E. cbn [Qnum Qden Qmult Pos.mul] in E.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma pei_qfact_nz : forall k : nat, ~ (q_fact k == 0%Q).
Proof.
  intro k. intro E. apply (Qlt_not_eq 0%Q (q_fact k)).
  apply q_fact_pos. exact (Qeq_sym _ _ E).
Qed.

Lemma pei_sum_shift : forall (M : nat) (f : nat -> Q),
  sum_upto (Datatypes.S M) f == f 0%nat + sum_upto M (fun k => f (Datatypes.S k)).
Proof.
  intros M f. induction M as [| m IH].
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

Lemma pei_q_pow_mul : forall (x y : Q) (k : nat),
  q_pow (x * y) k == q_pow x k * q_pow y k.
Proof.
  intros x y k. induction k as [| m IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma pei_q_pow_pos_sq : forall (n : nat) (y : Q),
  Qlt 0 y -> Qlt 0 (q_pow y n).
Proof.
  intros n y Hy. induction n as [| m IH].
  - cbn [q_pow]. unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat; [exact Hy | exact IH].
Qed.

Lemma pei_q_pow_odd_pos : forall (n : nat) (x : Q),
  Qlt 0 x -> Qlt 0 (q_pow x (Datatypes.S (2 * n))).
Proof.
  intros n x Hx.
  replace (Datatypes.S (2 * n))%nat with (Datatypes.S (n + n))%nat by lia.
  rewrite q_pow_succ.
  apply (Qmult_lt_0_compat x (q_pow x (n + n))).
  - exact Hx.
  - rewrite (q_pow_add x n n).
    rewrite <- (pei_q_pow_mul x x n).
    apply (pei_q_pow_pos_sq n (x * x)).
    apply Qmult_lt_0_compat; exact Hx.
Qed.

(* ============================================================ *)
(* §B Beta 族：系数列表 t^a(1−t)^b 的构造、求值语义与闭式                *)
(* ============================================================ *)

(* 尾垫零：多项式列表尾部接一个 0（值与积分皆不变；等长用） *)
Definition pei_ztail (p : list Q) : list Q := p ++ (0%Q :: nil).

Lemma pei_eval_ztail : forall (p : list Q) (x : Q),
  pint_eval (pei_ztail p) x == pint_eval p x.
Proof.
  intros p x. unfold pei_ztail. induction p as [| a p' IH].
  - cbn [app pint_eval]. ring.
  - cbn [app pint_eval]. rewrite IH. ring.
Qed.

Lemma pei_integral_ztail : forall p : list Q,
  pint_integral (pei_ztail p) == pint_integral p.
Proof.
  intro p. unfold pint_integral, pei_ztail. generalize 0%nat.
  induction p as [| a p' IH]; intro k.
  - cbn [app pint_integral_from]. unfold pint_monomial_int.
    rewrite pint_zero_div. ring.
  - cbn [app pint_integral_from]. rewrite IH. ring.
Qed.

(* t^a(1−t)^b 的规范系数列表（头为常数项；长度 a+b+1）：
   (1−t)^{b+1} = (1−t)^b − t·(1−t)^b 的列表级递归，首操作数垫零保等长 *)
Fixpoint pei_list (a b : nat) : list Q :=
  match b with
  | 0%nat => pint_pow_poly a
  | Datatypes.S b' =>
      pint_add (pei_ztail (pei_list a b'))
               (pint_scale (- 1)%Q (pei_list (Datatypes.S a) b'))
  end.

Lemma pei_scale_length : forall (a : Q) (p : list Q),
  length (pint_scale a p) = length p.
Proof.
  intros a p. induction p as [| c p' IH].
  - reflexivity.
  - cbn [pint_scale length]. rewrite IH. reflexivity.
Qed.

Lemma pei_add_length : forall p q : list Q,
  length p = length q -> length (pint_add p q) = length p.
Proof.
  intros p. induction p as [| a p' IH]; intros q Hlen.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_add length]. injection Hlen as Hlen'.
      rewrite (IH q' Hlen'). reflexivity.
Qed.

Lemma pei_list_length : forall a b : nat,
  length (pei_list a b) = Datatypes.S (a + b)%nat.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a.
  - cbn [pei_list]. replace (Datatypes.S (a + 0))%nat with (Datatypes.S a)%nat by lia.
    induction a as [| a' IHa].
    + reflexivity.
    + cbn [pint_pow_poly length] in IHa. cbn [pint_pow_poly length].
      rewrite IHa. reflexivity.
  - cbn [pei_list].
    rewrite pei_add_length.
    + unfold pei_ztail. rewrite app_length, IH. cbn [length]. lia.
    + unfold pei_ztail. rewrite app_length, IH, pei_scale_length,
        (IH (Datatypes.S a)). cbn [length]. lia.
Qed.

(* 求值线性性（无长度前提——零垫语义自洽） *)
Lemma pei_eval_add : forall (p q : list Q) (x : Q),
  pint_eval (pint_add p q) x == pint_eval p x + pint_eval q x.
Proof.
  intros p. induction p as [| a p' IH]; intros q x.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval]. ring.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval]. rewrite IH. ring.
Qed.

Lemma pei_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  pint_eval (pint_scale a p) x == a * pint_eval p x.
Proof.
  intros a p. induction p as [| c p' IH]; intro x.
  - cbn [pint_scale pint_eval]. ring.
  - cbn [pint_scale pint_eval]. rewrite IH. ring.
Qed.

(* 语义锚：pei_list a b 逐点 == t^a·(1−t)^b *)
Lemma pei_beta_eval : forall (a b : nat) (t : Q),
  pint_eval (pei_list a b) t == q_pow t a * q_pow (1 - t) b.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a t.
  - cbn [pei_list]. cbn [q_pow].
    rewrite <- (qeqT_imp_qeq _ _ (pint_eval_pow_poly a t)).
    ring.
  - cbn [pei_list].
    rewrite pei_eval_add, pei_eval_ztail, pei_eval_scale.
    rewrite (IH (Datatypes.S a) t). rewrite (IH a t).
    rewrite (q_pow_succ t a).
    rewrite (q_pow_succ (1 - t)%Q b'). ring.
Qed.

(* Beta 闭式：∫₀¹ t^a(1−t)^b dt == a!·b!/(a+b+1)!。
   两参数归纳于 b：步 = 线性拆分 + 除法合并（pei_div_sub/pei_div_eq）。 *)
Theorem pei_beta_value : forall a b : nat,
  pint_integral (pei_list a b) ==
  q_fact a * q_fact b / q_fact (a + b + 1)%nat.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a.
  - cbn [pei_list].
    assert (H := qeqT_imp_qeq _ _ (pint_integral_pow_poly a)).
    rewrite H.
    replace (a + 0 + 1)%nat with (Datatypes.S a)%nat by lia.
    cbn [q_fact].
    apply pei_div_eq.
    + unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
    + apply Qmult_lt_0_compat.
      * unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
      * apply q_fact_pos.
    + ring.
  - cbn [pei_list].
    assert (HL : length (pei_ztail (pei_list a b'))
                 = length (pint_scale (- 1)%Q (pei_list (Datatypes.S a) b'))).
    { unfold pei_ztail. rewrite app_length, pei_list_length.
      rewrite pei_scale_length, pei_list_length. simpl. lia. }
    assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite Hadd, pei_integral_ztail.
    assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (- 1)%Q (pei_list (Datatypes.S a) b'))).
    rewrite Hsc.
    rewrite (IH a), (IH (Datatypes.S a)).
    rewrite (q_fact_succ b').
    rewrite (q_fact_succ a).
    replace (a + Datatypes.S b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    replace (Datatypes.S a + b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    rewrite (q_fact_succ (a + b' + 1)%nat).
    assert (EJ : (Z.of_nat (Datatypes.S (a + b' + 1)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S a) # 1)
                       + (Z.of_nat (Datatypes.S b') # 1))%Q).
    { unfold Qeq, Qplus. cbn [Qnum Qden Qmult Pos.mul].
      replace (Z.of_nat (Datatypes.S (a + b' + 1)))
        with ((Z.of_nat (Datatypes.S a) + Z.of_nat (Datatypes.S b'))%Z) by lia.
      lia. }
    rewrite EJ.
    transitivity (q_fact a * q_fact b' / q_fact (a + b' + 1)
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a * q_fact b')
                       / (((Z.of_nat (Datatypes.S a) # 1)
                             + (Z.of_nat (Datatypes.S b') # 1))
                            * q_fact (a + b' + 1)))).
    + ring.
    + rewrite (pei_div_sub (q_fact a * q_fact b') (q_fact (a + b' + 1))
               (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
               (((Z.of_nat (Datatypes.S a) # 1)
                   + (Z.of_nat (Datatypes.S b') # 1))
                  * q_fact (a + b' + 1))).
      * apply (pei_div_eq
                 ((q_fact a * q_fact b')
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1))
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
                      * q_fact (a + b' + 1))
                 (q_fact (a + b' + 1)
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1)))
                 (q_fact a * ((Z.of_nat (Datatypes.S b') # 1) * q_fact b'))
                 (((Z.of_nat (Datatypes.S a) # 1)
                     + (Z.of_nat (Datatypes.S b') # 1))
                    * q_fact (a + b' + 1))).
        -- apply Qmult_lt_0_compat.
           ++ apply q_fact_pos.
           ++ apply Qmult_lt_0_compat.
              ** unfold Qlt. cbn [Qnum Qden Qplus]. lia.
              ** apply q_fact_pos.
        (* REV-R1：原块系块 1 复制，但 s 因子次序相反
           （(S a#1 + S b'#1) 在前、q_fact 在后），apply q_fact_pos
           打在加和项上失配（TRI-V1 L374 首错，实测环境 b'/IH 即此处）。
           REV-R1 定点手术：加和项 lia 支、q_fact 支换序。 *)
        -- apply Qmult_lt_0_compat.
           ++ unfold Qlt. cbn [Qnum Qden Qplus]. lia.
           ++ apply q_fact_pos.
        -- ring.
      * apply q_fact_pos.
      * apply Qmult_lt_0_compat.
        -- unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
        -- apply q_fact_pos.
Qed.

(* ============================================================ *)
(* §C Beta 正性与上界（阶乘不等式引擎）                                  *)
(* ============================================================ *)

Lemma pei_beta_pos : forall a b : nat,
  Qlt 0 (pint_integral (pei_list a b)).
Proof.
  intros a b. rewrite pei_beta_value. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

Corollary pei_beta_integral_pos : forall n : nat,
  QltT 0 (pint_integral (pei_list n n)).
Proof.
  intro n. exact (Qlt_to_QltT 0 (pint_integral (pei_list n n))
    (pei_beta_pos n n)).
Qed.

(* 阶乘不等式核：n!·(n+k)! ≤ (2n+k+1)!（Beta_k ≤ 1 的载体） *)
Lemma pei_fact_le : forall n k : nat,
  Qle (q_fact n * q_fact (n + k)) (q_fact (Datatypes.S (2 * n + k))).
Proof.
  intros n k. induction n as [| m IH].
  - replace (0 + k)%nat with k%nat by lia.
    rewrite (q_fact_succ k). cbn [q_fact].
    (* REV-R1：原 apply (Qmult_le_compat_l 1 (Z.of_nat (S k) # 1)
       (q_fact k)) 死名（9.1 stdlib 无 _l/Qmult_le_compat）。实测目标
       （q_fact 0 cbn 后）= 1*q_fact k <= (S k#1)*q_fact k，恰为
       Qmult_le_compat_r 1 (S k#1) (q_fact k) 结论形，单步直合。 *)
    apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S k) # 1)%Q (q_fact k)).
    + unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
    + apply Qlt_le_weak. apply q_fact_pos.
  - assert (Esm : q_fact (Datatypes.S m)
                  == (Z.of_nat (Datatypes.S m) # 1) * q_fact m) by apply q_fact_succ.
    assert (Esmk : q_fact (Datatypes.S m + k)
                   == (Z.of_nat (Datatypes.S (m + k)) # 1) * q_fact (m + k)).
    { replace (Datatypes.S m + k)%nat with (Datatypes.S (m + k))%nat by lia.
      apply q_fact_succ. }
    assert (Ej1 : q_fact (Datatypes.S (2 * m + k))
                  == (Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))
      by apply q_fact_succ.
    (* REV-R1：原 replace 多敲一层 S（S(S(S(2m+k)))=2m+k+3 ≠
       2*S m+k=2m+k+2，lia "Cannot find witness"）；下方 q_fact_succ
       重写链与 Qle_trans 链均按 S(S(2m+k)) 两层形书写——按链形已证结论改回
       两层 S。 *)
    replace (2 * Datatypes.S m + k)%nat
      with (Datatypes.S (Datatypes.S (2 * m + k)))%nat by lia.
    rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * m + k)))).
    rewrite (q_fact_succ (Datatypes.S (2 * m + k))).
    rewrite Esm, Esmk, Ej1.
    (* REV-R1 重写归纳步链（原链三重真伤：①replace 多一层 S；
       ②A # 1 * B # 1 同级左结合被 Qmake 吞参——positive 型错；
       ③qeq_le+ring 误用于真不等式 P*A ≤ q_fact(S(2m+k))*A——非恒等式）。
       本构四步右嵌套：
       h1 恒等归位（ring）；h2 IH 右乘 A（_r，IH+0≤A）；
       h3 旋转后 _r：A ≤ (2m+k+3)(2m+k+2)（nia）右乘 q_fact(S(2m+k))；
       h4 Ej1 恒等归位（ring）。 *)
    apply (Qle_trans
      ((Z.of_nat (Datatypes.S m) # 1) * q_fact m
         * ((Z.of_nat (Datatypes.S (m + k)) # 1) * q_fact (m + k)))
      ((q_fact m * q_fact (m + k))
         * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
      ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
         * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
              * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
    + apply qeq_le. ring.
    + apply (Qle_trans
        ((q_fact m * q_fact (m + k))
           * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
        (q_fact (Datatypes.S (2 * m + k))
           * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
        ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
           * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
      * apply (Qmult_le_compat_r (q_fact m * q_fact (m + k))
                  (q_fact (Datatypes.S (2 * m + k)))
                  ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))).
        -- exact IH.
        -- apply Qmult_le_0_compat; unfold Qle; cbn [Qnum Qden Qplus Qmult Qinv q_fact]; lia.
      * apply (Qle_trans
          (q_fact (Datatypes.S (2 * m + k))
             * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
          (((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
             * q_fact (Datatypes.S (2 * m + k)))
          ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
             * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                  * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
        -- apply qeq_le. ring.
        -- apply (Qle_trans
              (((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
                 * q_fact (Datatypes.S (2 * m + k)))
              (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1))
                 * q_fact (Datatypes.S (2 * m + k)))
              ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                 * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                      * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
           ++ apply (Qmult_le_compat_r
                  ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
                  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                     * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1))
                  (q_fact (Datatypes.S (2 * m + k)))).
              ** unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. nia.
              ** apply Qlt_le_weak. apply q_fact_pos.
           ++ apply qeq_le. rewrite Ej1. ring.
Qed.

(* ============================================================ *)
(* §D 截断指数被积函数 pei_eb_list（主件载体）                            *)
(*   pei_eb_list n x M = Σ_{k=0}^{M} (x^k/k!)·list(t^{n+k}(1−t)ⁿ)        *)
(*   逐点语义 == tⁿ(1−t)ⁿ·exp_partial M (x·t)                           *)
(* ============================================================ *)

Fixpoint pei_eb_list (n : nat) (x : Q) (M : nat) : list Q :=
  match M with
  | 0%nat => pei_list n n
  | Datatypes.S m =>
      pint_add (pint_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                           (pei_list (n + Datatypes.S m) n))
               (pei_ztail (pei_eb_list n x m))
  end.

Lemma pei_eb_length : forall (n : nat) (x : Q) (M : nat),
  length (pei_eb_list n x M) = (2 * n + M + 1)%nat.
Proof.
  intros n x M. induction M as [| m IH].
  - cbn [pei_eb_list]. rewrite pei_list_length. lia.
  - cbn [pei_eb_list].
    rewrite pei_add_length.
    + rewrite pei_scale_length, pei_list_length. simpl. lia.
    + unfold pei_ztail. rewrite app_length, IH, pei_scale_length,
        pei_list_length. simpl. lia.
Qed.

(* 步分解：∫(S m) == c_m·Beta(n+S m, n) + ∫(m) *)
Lemma pei_eb_step : forall (n : nat) (x : Q) (m : nat),
  pint_integral (pei_eb_list n x (Datatypes.S m)) ==
  q_pow x (Datatypes.S m) / q_fact (Datatypes.S m) *
    (q_fact (n + Datatypes.S m) * q_fact n
       / q_fact (Datatypes.S (n + Datatypes.S m + n)))
  + pint_integral (pei_eb_list n x m).
Proof.
  intros n x m. cbn [pei_eb_list].
  assert (HL : length (pint_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                                  (pei_list (n + Datatypes.S m) n))
               = length (pei_ztail (pei_eb_list n x m))).
  { rewrite pei_scale_length, pei_list_length. unfold pei_ztail.
    rewrite app_length, pei_eb_length. simpl. lia. }
  assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
  rewrite Hadd, pei_integral_ztail.
  assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)) (pei_list (n + Datatypes.S m) n))).
  rewrite Hsc.
  assert (Hbv := pei_beta_value (n + Datatypes.S m) n).
  replace (n + Datatypes.S m + n + 1)%nat
    with (Datatypes.S (n + Datatypes.S m + n))%nat in Hbv by lia.
  rewrite Hbv. ring.
Qed.

Lemma pei_eb_value0 : forall (n : nat) (x : Q),
  pint_integral (pei_eb_list n x 0) ==
  q_fact n * q_fact n / q_fact (Datatypes.S (2 * n))%nat.
Proof.
  intros n x. cbn [pei_eb_list].
  rewrite pei_beta_value.
  replace (n + n + 1)%nat with (Datatypes.S (2 * n))%nat by lia.
  reflexivity.
Qed.

(* 闭式：∫ == Σ_{k≤M} x^k/k!·Beta(n+k+1,n+1)——余项积分表示的
   构造性泰勒系数对接件（②的有限核） *)
Theorem pei_eb_value : forall (n : nat) (x : Q) (M : nat),
  pint_integral (pei_eb_list n x M) ==
  sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))).
Proof.
  intros n x M. induction M as [| m IH].
  - rewrite pei_eb_value0. cbn [sum_upto].
    replace (n + 0)%nat with n%nat by lia.
    replace (2 * n + 0)%nat with (2 * n)%nat by lia.
    change (q_pow x 0%nat) with 1%Q.
    change (q_fact 0%nat) with 1%Q.
    assert (Hone : 1%Q / 1%Q == 1%Q).
    { unfold Qdiv. apply Qmult_inv_r.
      intro E. unfold Qeq in E. cbn [Qnum Qden Qmult Pos.mul] in E. lia. }
    rewrite Hone. rewrite Qmult_1_l. ring.
  - rewrite pei_eb_step, IH. cbn [sum_upto].
    replace (2 * n + Datatypes.S m)%nat with (n + Datatypes.S m + n)%nat by lia.
    ring.
Qed.

(* 语义锚：pei_eb_list 逐点 == tⁿ(1−t)ⁿ·exp_partial M (x·t)
   ——截断指数被积函数恰为 e^{tx} 的构造性 M 截断 *)
Theorem pei_eb_eval : forall (n : nat) (x : Q) (M : nat) (t : Q),
  pint_eval (pei_eb_list n x M) t
  == q_pow t n * q_pow (1 - t) n * exp_partial M (x * t).
Proof.
  intros n x M. induction M as [| m IH]; intro t.
  - cbn [pei_eb_list]. rewrite pei_beta_eval. cbn [exp_partial]. ring.
  - cbn [pei_eb_list].
    rewrite pei_eval_add, pei_eval_ztail, pei_eval_scale.
    rewrite IH. rewrite pei_beta_eval.
    cbn [exp_partial].
    rewrite (pei_q_pow_mul x t (Datatypes.S m)).
    rewrite pei_div_mul_shift.
    rewrite (q_pow_add t n (Datatypes.S m)).
    ring.
Qed.

(* 项非负：x ≥ 0 时每个泰勒项非负（幂非负 × 1/k! 正 × Beta 正） *)
Lemma pei_term_nonneg : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x ->
  Qle 0 (q_pow x k / q_fact k
           * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))).
Proof.
  intros n x k Hx. unfold Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. apply q_fact_pos.
  - apply Qlt_le_weak. apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* §E 主件一（pade_integral_pos 对应）：积分严格正                        *)
(* ============================================================ *)

Theorem pei_integral_pos : forall (n : nat) (x : Q) (M : nat),
  QleT' 0 x -> QltT 0 (pint_integral (pei_eb_list n x M)).
Proof.
  intros n x M Hx.
  assert (Hval := pei_eb_value n x M).
  assert (Hshift := pei_sum_shift M (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k))))).
  rewrite Hshift in Hval.
  assert (Hrest : Qle 0 (sum_upto M (fun k : nat =>
    q_pow x (Datatypes.S k) / q_fact (Datatypes.S k)
      * (q_fact (n + Datatypes.S k) * q_fact n
           / q_fact (Datatypes.S (2 * n + Datatypes.S k)))))).
  { apply (bts_sum_nonneg_bounded M (fun k : nat =>
      q_pow x (Datatypes.S k) / q_fact (Datatypes.S k)
        * (q_fact (n + Datatypes.S k) * q_fact n
             / q_fact (Datatypes.S (2 * n + Datatypes.S k))))).
    intro k. intro Hbnd. apply pei_term_nonneg. exact Hx. }
  assert (Hf0 : Qlt 0 (q_pow x 0%nat / q_fact 0%nat
    * (q_fact (n + 0)%nat * q_fact n
         / q_fact (Datatypes.S (2 * n + 0)%nat)))).
  { replace (n + 0)%nat with n%nat by lia.
    replace (2 * n + 0)%nat with (2 * n)%nat by lia.
    change (q_pow x 0%nat) with 1%Q.
    change (q_fact 0%nat) with 1%Q.
    assert (Hone : 1%Q / 1%Q == 1%Q).
    { unfold Qdiv. apply Qmult_inv_r.
      intro E. unfold Qeq in E. cbn [Qnum Qden Qmult Pos.mul] in E. lia. }
    rewrite Hone, Qmult_1_l.
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hsum : Qlt 0 (sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))))).
  { rewrite Hshift. apply pei_lt_le_plus; assumption. }
  apply Qlt_to_QltT.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))))
    (pint_integral (pei_eb_list n x M)) 0%Q).
  - rewrite Hshift. apply Qeq_sym. exact Hval.
  - exact Hsum.
Qed.

(* ============================================================ *)
(* §F 主件二（pade_error_bound 对应）：显式上界                           *)
(* ============================================================ *)

Theorem pei_eb_le : forall (n : nat) (x : Q) (M : nat),
  QleT' 0 x -> QleT' (pint_integral (pei_eb_list n x M)) (exp_partial M x).
Proof.
  intros n x M Hx. induction M as [| m IH].
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (q_fact n * q_fact n / q_fact (Datatypes.S (2 * n))) 1%Q).
    + apply qeq_le. apply pei_eb_value0.
    + apply pei_div_le_1.
      * apply q_fact_pos.
      * assert (Hle := pei_fact_le n 0%nat).
        replace (n + 0)%nat with n%nat in Hle by lia.
        replace (2 * n + 0)%nat with (2 * n)%nat in Hle by lia.
        exact Hle.
  - apply Qle_to_QleT'.
    assert (Hstep := pei_eb_step n x m).
    assert (Hf2 := pei_fact_le n (Datatypes.S m)).
    replace (2 * n + Datatypes.S m)%nat
      with (n + Datatypes.S m + n)%nat in Hf2 by lia.
    assert (Hf3 : Qle (q_fact (n + Datatypes.S m) * q_fact n)
                      (q_fact (Datatypes.S (n + Datatypes.S m + n)))).
    { apply (Qle_trans _ (q_fact n * q_fact (n + Datatypes.S m)) _).
      - apply qeq_le. ring.
      - exact Hf2. }
    (* REV-R1：原步项链三处错序——①外链中间点误写 exp_partial m x
       （应为 Hstep 右侧的 pint_integral (pei_eb_list n x m) 项）；
       ②两条 + bullet 顺序颠倒（Hstep 传输须先于 Qplus_le_compat 拆分）；
       ③内层中点 c*1 应为 1*c（Qmult_le_compat_r 结论形 x*z ≤ y*z）。
       本构：pint(Sm) ≤(Hstep) c*Beta+pint m ≤(Qplus_le_compat) c*1+exp m
       ==(cbn+ring) exp(S m)。 *)
    apply (Qle_trans _
      (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)
         * (q_fact (n + Datatypes.S m) * q_fact n
              / q_fact (Datatypes.S (n + Datatypes.S m + n)))
       + pint_integral (pei_eb_list n x m)) _).
    + apply qeq_le. exact Hstep.
    + apply (Qle_trans _
        (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m) * 1%Q
           + exp_partial m x) _).
      * apply Qplus_le_compat.
        -- apply (Qle_trans _
              ((q_fact (n + Datatypes.S m) * q_fact n
                  / q_fact (Datatypes.S (n + Datatypes.S m + n)))
                 * (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))) _).
           ++ apply qeq_le. ring.
           ++ apply (Qle_trans _
                 (1%Q * (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))) _).
              ** apply (Qmult_le_compat_r
                    (q_fact (n + Datatypes.S m) * q_fact n
                       / q_fact (Datatypes.S (n + Datatypes.S m + n))) 1%Q
                    (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))).
                 --- apply pei_div_le_1.
                     +++ apply q_fact_pos.
                     +++ exact Hf3.
                 --- unfold Qdiv. apply Qmult_le_0_compat.
                     *** apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx.
                     *** apply Qlt_le_weak. apply Qinv_lt_0_compat.
                         apply q_fact_pos.
              ** apply qeq_le. ring.
        -- apply QleT'_to_Qle. apply IH.
      * apply qeq_le. cbn [exp_partial]. ring.
Qed.

(* ============================================================ *)
(* §G 主件三（pade_error_sign 对应）：符号 =(−1)^n 的模长正性              *)
(*   + 主件四（pade_error_integral 对应）：首项因式分解                    *)
(* ============================================================ *)

Theorem pei_error_mag_pos : forall (n : nat) (x : Q),
  QltT 0 x ->
  QltT 0 (q_fact n * q_fact n * q_pow x (Datatypes.S (2 * n))
            / (q_fact (2 * n) * q_fact (Datatypes.S (2 * n)))).
Proof.
  intros n x Hx. apply Qlt_to_QltT. unfold Qdiv.
  apply (Qmult_lt_0_compat
           (q_fact n * q_fact n * q_pow x (Datatypes.S (2 * n)))
           (Qinv (q_fact (2 * n) * q_fact (Datatypes.S (2 * n))))).
  - apply (Qmult_lt_0_compat (q_fact n * q_fact n)
             (q_pow x (Datatypes.S (2 * n)))).
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply pei_q_pow_odd_pos. apply QltT_to_Qlt. exact Hx.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* 首项恒等式（M=0 截断的余项积分表示）：
   (−1)^n·x^{2n+1}/(2n)!·∫₀¹ tⁿ(1−t)ⁿ·[e^{tx} 的 k=0 项] dt
   == (−1)^n·x^{2n+1}/(2n)!·n!²/(2n+1)!——经典误差首项 *)
Corollary pei_error_lead_integral : forall (n : nat) (x : Q),
  q_pow (- 1)%Q n
    * (q_pow x (Datatypes.S (2 * n)) / q_fact (2 * n)
         * pint_integral (pei_eb_list n x 0)) ==
  q_pow (- 1)%Q n
    * (q_pow x (Datatypes.S (2 * n)) / q_fact (2 * n)
         * (q_fact n * q_fact n / q_fact (Datatypes.S (2 * n)))).
Proof.
  intros n x.
  exact (Qmult_comp _ _ (Qeq_refl _) _ _
           (Qmult_comp _ _ (Qeq_refl _) _ _ (pei_eb_value0 n x))).
Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（编译期 stdout，verify 复核）          *)
(* ============================================================ *)

Print Assumptions pei_beta_eval.
Print Assumptions pei_beta_value.
Print Assumptions pei_beta_pos.
Print Assumptions pei_beta_integral_pos.
Print Assumptions pei_fact_le.
Print Assumptions pei_eb_eval.
Print Assumptions pei_eb_value.
Print Assumptions pei_integral_pos.
Print Assumptions pei_eb_le.
Print Assumptions pei_error_lead_integral.
Print Assumptions pei_error_mag_pos.
