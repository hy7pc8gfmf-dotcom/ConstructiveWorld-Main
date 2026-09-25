(* ============================================================ *)
(*                                                               *)
(*   积分面路线不可达——库内 pint_ 机器只覆盖多项式被积函数，           *)
(*   有理型 t^n(1−t)^n/(1+t)^{n+1} 超出一期面；逐点界               *)
(*   (t(1−t))^n ≤ 4^{-n} 需「逐点单调⟹积分单调」机器，              *)
(*   【离散化/多项式系数序列路线】：载体取 Padé 积分分子多项式          *)
(*   t^n(1−t)^n 的系数列表积分（Beta 载体）：                        *)
(*     lne_B n := ∫₀¹ t^n(1−t)^n dt = (n!)^2/(2n+1)!               *)
(*   三件套交付（正性+指数上界+整性）：                               *)
(*   ① 正性 lne_B_posT：QltT 0 (lne_B n)（闭式两正因子）；            *)
(*   ② 上界 lne_B_le_p4：lne_B n ≤ 4^{-n}（核 = (2n+1)!≥(n!)^2·4^n，  *)
(*      纯 nat 归纳 lne_nat_core；4^{-n} 与判定窗 2^{-n} 匹配：        *)
(*      lne_B_lt_p2 给 n≥1 的严格窗内 containment）；                 *)
(*   ③ 整性 lne_B_int：lne_B n·(2n+1)! = (n!)^2 ∈ Z（sif_qfact_Z 桥，  *)
(*      sigT 见证形）。                                              *)
(* 配方来源（诚实溯源）：lne_list/lne_beta_value 及 §A 引擎移植自        *)
(*   消融50/PadeErrorIntegral.v（CYE10 交付件，pei_ 前缀）同构换名，     *)
(*   因其 Require 链（UpReqB4TwoStage⟵219 壳⟵UpReqPadeExp）在          *)
(*   vo_901 信任根缺 .vo 无法本地消费，按配方移植免 Psatz 装环境。       *)
(* 消费装配：UpReqLn2Irrational 条件形母定理消费，零旁路：              *)
(*   lne_ln2_irrational_cond : ln2i_escape_spec -> forall q, ...       *)
(*   （exact ln2i_irrational_criterion_cond 真走母定理）；             *)
(*   lne_B_in_window：载体严格落入 ln2 判定窗 ln2i_e n = 2^{-n} 内。     *)
(* 残面诚实登记（对照 GEOM-B 先例）：                                  *)
(*   escape 需对每个 q 找 n 使 2^{-n} < |q − x_n|；n!·2^n 整递推        *)
(*   「窗放不进」）；Beta 载体三件套 + 窗匹配件是 Padé 路线的首步          *)
(*   承重面，d_n^2 档间隙步（Hermite 机制：载体×分母方幂与 ln2 级数        *)
(*   部分和的耦合）留续作，首步路线=以 lne_B 整性面 × 递推 d_n 做          *)
(*   窗内/窗外二分。本件全部Qed/Defined，零公理声明词、零认授。           *)
(* 语句面纪律：装配/消费面全 Set（QltT/QleT'/QeqT/sigT/S01.And:=A*B）；  *)
(*   支撑引理 nat/Z/Q 层 Prop 面仅作推理脚手架（UpReq 系先例同构）。     *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、PolyIntegral、      *)
(*   SumInvFactEscape（sif_qfact_Z）、UpReqLn2Irrational（母件消费）；    *)
(*   前 5 件 vo_901 信任根在册，UpReqLn2Irrational 按 CZE13 配方         *)
(*   side 根现编（源=ConstructiveWorld_Live 只读原件）。                 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PolyIntegral.
Require Import SumInvFactEscape.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
  ZArith.ZArith.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §A 有理域引擎（PadeErrorIntegral §A 同构移植，lne_ 换名）           *)
(* ============================================================ *)

Lemma lne_mult_canc : forall a b c : Q, a * c == b * c -> ~ (c == 0%Q) -> a == b.
Proof.
  intros a b c H Hc0.
  apply (proj1 (Qmult_inj_r a b c Hc0) H).
Qed.

Lemma lne_mult_nz : forall x y : Q, ~ (x == 0%Q) -> ~ (y == 0%Q) -> ~ (x * y == 0%Q).
Proof.
  intros x y Hx Hy Heq. apply Hx.
  apply (lne_mult_canc x 0%Q y).
  - rewrite Qmult_0_l. exact Heq.
  - exact Hy.
Qed.

Lemma lne_div_eq : forall p q r s : Q,
  Qlt 0 q -> Qlt 0 s -> p * s == q * r -> p / q == r / s.
Proof.
  intros p q r s Hq Hs H.
  assert (Hqz : ~ (q == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q q Hq). exact (Qeq_sym _ _ E). }
  assert (Hsz : ~ (s == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ E). }
  assert (Hqsz : ~ (q * s == 0%Q)) by (apply (lne_mult_nz q s Hqz Hsz)).
  apply (lne_mult_canc (p / q) (r / s) (q * s)).
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

Lemma lne_div_sub : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> a / b - c / d == (a * d - c * b) / (b * d).
Proof.
  intros a b c d Hb Hd.
  assert (Hbz : ~ (b == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q b Hb). exact (Qeq_sym _ _ E). }
  assert (Hdz : ~ (d == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q d Hd). exact (Qeq_sym _ _ E). }
  assert (Hbdz : ~ (b * d == 0%Q)) by (apply (lne_mult_nz b d Hbz Hdz)).
  assert (Hbd1 : (b * d) * Qinv (b * d) == 1%Q) by (apply Qmult_inv_r; exact Hbdz).
  apply (lne_mult_canc (a / b - c / d) ((a * d - c * b) / (b * d)) (b * d)).
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

Lemma lne_qfact_nz : forall k : nat, ~ (q_fact k == 0%Q).
Proof.
  intro k. intro E. apply (Qlt_not_eq 0%Q (q_fact k)).
  apply q_fact_pos. exact (Qeq_sym _ _ E).
Qed.

(* 阶乘 ≥ 1（nat 层，供 Z 传递腿） *)
Lemma lne_fact_ge1 : forall k : nat, (1 <= fact k)%nat.
Proof.
  induction k as [| k IH].
  - cbn [fact]. lia.
  - cbn [fact]. lia.
Qed.

(* ============================================================ *)
(* §B Beta 载体：系数列表 t^a(1−t)^b 的构造与闭式                       *)
(*    （PadeErrorIntegral §B 同构移植；积分语义=PolyIntegral pint_ 面）  *)
(* ============================================================ *)

(* 尾垫零：列表尾部接一个 0（值与积分皆不变；等长用） *)
Definition lne_ztail (p : list Q) : list Q := p ++ (0%Q :: nil).

Lemma lne_eval_ztail : forall (p : list Q) (x : Q),
  pint_eval (lne_ztail p) x == pint_eval p x.
Proof.
  intros p x. unfold lne_ztail. induction p as [| a p' IH].
  - cbn [app pint_eval]. ring.
  - cbn [app pint_eval]. rewrite IH. ring.
Qed.

Lemma lne_integral_ztail : forall p : list Q,
  pint_integral (lne_ztail p) == pint_integral p.
Proof.
  intro p. unfold pint_integral, lne_ztail. generalize 0%nat.
  induction p as [| a p' IH]; intro k.
  - cbn [app pint_integral_from]. unfold pint_monomial_int.
    rewrite pint_zero_div. ring.
  - cbn [app pint_integral_from]. rewrite IH. ring.
Qed.

(* t^a(1−t)^b 的规范系数列表（头为常数项；长度 a+b+1）：
   (1−t)^{b+1} = (1−t)^b − t·(1−t)^b 的列表级递归，首操作数垫零保等长 *)
Fixpoint lne_list (a b : nat) : list Q :=
  match b with
  | 0%nat => pint_pow_poly a
  | Datatypes.S b' =>
      pint_add (lne_ztail (lne_list a b'))
               (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))
  end.

Lemma lne_scale_length : forall (a : Q) (p : list Q),
  length (pint_scale a p) = length p.
Proof.
  intros a p. induction p as [| c p' IH].
  - reflexivity.
  - cbn [pint_scale length]. rewrite IH. reflexivity.
Qed.

Lemma lne_add_length : forall p q : list Q,
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

Lemma lne_list_length : forall a b : nat,
  length (lne_list a b) = Datatypes.S (a + b)%nat.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a.
  - cbn [lne_list]. replace (Datatypes.S (a + 0))%nat with (Datatypes.S a)%nat by lia.
    induction a as [| a' IHa].
    + reflexivity.
    + cbn [pint_pow_poly length] in IHa. cbn [pint_pow_poly length].
      rewrite IHa. reflexivity.
  - cbn [lne_list].
    rewrite lne_add_length.
    + unfold lne_ztail. rewrite app_length, IH. cbn [length]. lia.
    + unfold lne_ztail. rewrite app_length, IH, lne_scale_length,
        (IH (Datatypes.S a)). cbn [length]. lia.
Qed.

(* 求值线性性（无长度前提——零垫语义自洽） *)
Lemma lne_eval_add : forall (p q : list Q) (x : Q),
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

Lemma lne_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  pint_eval (pint_scale a p) x == a * pint_eval p x.
Proof.
  intros a p. induction p as [| c p' IH]; intro x.
  - cbn [pint_scale pint_eval]. ring.
  - cbn [pint_scale pint_eval]. rewrite IH. ring.
Qed.

(* 语义锚：lne_list a b 逐点 == t^a·(1−t)^b *)
Lemma lne_beta_eval : forall (a b : nat) (t : Q),
  pint_eval (lne_list a b) t == q_pow t a * q_pow (1 - t) b.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a t.
  - cbn [lne_list]. cbn [q_pow].
    rewrite <- (qeqT_imp_qeq _ _ (pint_eval_pow_poly a t)).
    ring.
  - cbn [lne_list].
    rewrite lne_eval_add, lne_eval_ztail, lne_eval_scale.
    rewrite (IH (Datatypes.S a) t). rewrite (IH a t).
    rewrite (q_pow_succ t a).
    rewrite (q_pow_succ (1 - t)%Q b'). ring.
Qed.

(* Beta 闭式：∫₀¹ t^a(1−t)^b dt == a!·b!/(a+b+1)!。
   两参数归纳于 b：步 = 线性拆分 + 除法合并（lne_div_sub/lne_div_eq）。 *)
Theorem lne_beta_value : forall a b : nat,
  pint_integral (lne_list a b) ==
  q_fact a * q_fact b / q_fact (a + b + 1)%nat.
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a.
  - cbn [lne_list].
    assert (H := qeqT_imp_qeq _ _ (pint_integral_pow_poly a)).
    rewrite H.
    replace (a + 0 + 1)%nat with (Datatypes.S a)%nat by lia.
    cbn [q_fact].
    apply lne_div_eq.
    + unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
    + apply Qmult_lt_0_compat.
      * unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
      * apply q_fact_pos.
    + ring.
  - cbn [lne_list].
    assert (HL : length (lne_ztail (lne_list a b'))
                 = length (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))).
    { unfold lne_ztail. rewrite app_length, lne_list_length.
      rewrite lne_scale_length, lne_list_length. simpl. lia. }
    assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite Hadd, lne_integral_ztail.
    assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (- 1)%Q (lne_list (Datatypes.S a) b'))).
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
    + rewrite (lne_div_sub (q_fact a * q_fact b') (q_fact (a + b' + 1))
               (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
               (((Z.of_nat (Datatypes.S a) # 1)
                   + (Z.of_nat (Datatypes.S b') # 1))
                  * q_fact (a + b' + 1))).
      * apply (lne_div_eq
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
        -- apply Qmult_lt_0_compat.
           ++ unfold Qlt. cbn [Qnum Qden Qplus]. lia.
           ++ apply q_fact_pos.
        -- ring.
      * apply q_fact_pos.
      * apply Qmult_lt_0_compat.
        -- unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
        -- apply q_fact_pos.
Qed.

(* 主载体：lne_B n := ∫₀¹ t^n(1−t)^n dt（Padé 积分分子的离散承载） *)
Definition lne_B (n : nat) : Q := pint_integral (lne_list n n).

(* 载体闭式（对角特化）：lne_B n == (n!)^2/(2n+1)! *)
Lemma lne_B_closed : forall n : nat,
  lne_B n == q_fact n * q_fact n / q_fact (Datatypes.S (n + n))%nat.
Proof.
  intro n. unfold lne_B. rewrite (lne_beta_value n n).
  replace (n + n + 1)%nat with (Datatypes.S (n + n))%nat by lia.
  reflexivity.
Qed.

(* ============================================================ *)
(* §C 指数级上界件：lne_B n ≤ 4^{-n}（核：nat 阶乘不等式归纳）           *)
(* ============================================================ *)

Lemma lne_pow4 : forall n : nat, (4 ^ n = 2 ^ (2 * n))%nat.
Proof.
  induction n as [| n IH].
  - cbn [Nat.mul Nat.pow]. reflexivity.
  - rewrite Nat.pow_succ_r'. rewrite IH.
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite !Nat.pow_succ_r'. lia.
Qed.

(* 核心不等式：(n!)^2·4^n ≤ (2n+1)!（即 (2n+1)·C(2n,n) ≥ 4^n 的整形式）
   归纳步：4(n+1)^2 ≤ (2n+2)(2n+3) 乘 IH 即得（nia 证书） *)
Lemma lne_nat_core : forall n : nat,
  (fact n * fact n * 2 ^ (2 * n) <= fact (2 * n + 1))%nat.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - cbn [fact].
    replace (2 * Datatypes.S n + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * n + 1)))%nat by lia.
    cbn [fact].
    replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite !Nat.pow_succ_r'.
    assert (H4 : (4 * Datatypes.S n * Datatypes.S n
                  <= Datatypes.S (Datatypes.S (2 * n + 1))
                       * Datatypes.S (2 * n + 1))%nat) by lia.
    assert (H5 : (fact n * fact n * 2 ^ (2 * n)
                    * (4 * Datatypes.S n * Datatypes.S n)
                  <= fact (2 * n + 1) * (4 * Datatypes.S n * Datatypes.S n))%nat)
      by (apply Nat.mul_le_mono_r; exact IH).
    transitivity (fact (2 * n + 1) * (4 * Datatypes.S n * Datatypes.S n))%nat.
    + replace ((Datatypes.S n * fact n) * (Datatypes.S n * fact n)
                 * (2 * (2 * 2 ^ (2 * n)))%nat)%nat
        with ((fact n * fact n * 2 ^ (2 * n))%nat
                * (4 * Datatypes.S n * Datatypes.S n)%nat)%nat
        by ring.
      exact H5.
    + assert (H6 : ((4 * Datatypes.S n * Datatypes.S n) * fact (2 * n + 1)
                     <= (Datatypes.S (Datatypes.S (2 * n + 1))
                          * Datatypes.S (2 * n + 1)) * fact (2 * n + 1))%nat)
        by (apply Nat.mul_le_mono_r; exact H4).
      lia.
Qed.

Lemma lne_pow_ge1 : forall n : nat, (1 <= 4 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* 4^n 的 Q 承载与正性 *)
Fixpoint lne_p4 (n : nat) : Q :=
  match n with
  | O => (1 # 1)
  | Datatypes.S m => (4 # 1) * lne_p4 m
  end.

Lemma lne_p4_Z : forall n : nat, lne_p4 n == ((Z.of_nat (4 ^ n)) # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [lne_p4]. rewrite IH. rewrite Nat.pow_succ_r'.
    rewrite Nat2Z.inj_mul. cbn [Z.of_nat].
    unfold Qmult. cbn [Qnum Qden Pos.mul]. reflexivity.
Qed.

Lemma lne_p4_pos : forall n : nat, Qlt 0 (lne_p4 n).
Proof.
  induction n as [| n IH].
  - unfold Qlt. cbn [Qnum Qden lne_p4]. lia.
  - cbn [lne_p4]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* 除法右乘逆比较器：0<y, 0<w, x·w ≤ y ⟹ x/y ≤ 1/w（全 Q 层，免展开簿记） *)
Lemma lne_div_le_inv : forall x y w : Q,
  Qlt 0 y -> Qlt 0 w -> Qle (x * w) y -> Qle (x / y) (Qinv w).
Proof.
  intros x y w Hy Hw Hxy. unfold Qdiv.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ E). }
  assert (Hw0 : ~ (w == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q w Hw). exact (Qeq_sym _ _ E). }
  assert (Eyw : (w * Qinv w)%Q == 1%Q) by (apply Qmult_inv_r; exact Hw0).
  assert (Eyy : (y * Qinv y)%Q == 1%Q) by (apply Qmult_inv_r; exact Hy0).
  assert (H1 : Qle ((x * w) * Qinv y) (y * Qinv y)).
  { apply (Qmult_le_compat_r (x * w) y).
    - exact Hxy.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy. }
  rewrite Eyy in H1.
  assert (H2 : Qle (((x * w) * Qinv y) * Qinv w) (1%Q * Qinv w)).
  { apply (Qmult_le_compat_r ((x * w) * Qinv y) (1%Q)).
    - exact H1.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hw. }
  rewrite Qmult_1_l in H2.
  assert (E3 : (((x * w) * Qinv y) * Qinv w)%Q
               == (x * (w * Qinv w) * Qinv y)%Q) by ring.
  rewrite E3 in H2. rewrite Eyw in H2. rewrite Qmult_1_r in H2.
  exact H2.
Qed.

(* 上界主件（Set 面）：lne_B n ≤ 4^{-n} *)
Theorem lne_B_le_p4 : forall n : nat, QleT' (lne_B n) (Qinv (lne_p4 n)).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite lne_B_closed.
  rewrite (sif_qfact_Z n). rewrite (sif_qfact_Z (Datatypes.S (n + n))).
  rewrite lne_p4_Z.
  apply (lne_div_le_inv ((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
          ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))
          ((Z.of_nat (4 ^ n) # 1))).
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (lne_fact_ge1 (Datatypes.S (n + n))) as Hg. lia.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (lne_pow_ge1 n) as Hg. lia.
  - rewrite lne_pow4.
    pose proof (lne_nat_core n) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    lia.
Qed.

(* ============================================================ *)
(* §D 整性件：lne_B n·(2n+1)! = (n!)^2 ∈ Z（sigT 见证形）               *)
(* ============================================================ *)

Theorem lne_B_int : forall n : nat,
  sigT (fun m : Z => QeqT (lne_B n * q_fact (Datatypes.S (n + n))%nat)
                           (m # 1)).
Proof.
  intro n. exists (Z.of_nat (fact n * fact n))%Z. apply qeq_imp_qeqT.
  rewrite lne_B_closed.
  rewrite (sif_qfact_Z n). rewrite (sif_qfact_Z (Datatypes.S (n + n))).
  unfold Qdiv.
  transitivity (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))%Q).
  - assert (E1 : ((((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
                     * Qinv ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)))
                    * (Z.of_nat (fact (Datatypes.S (n + n))) # 1))%Q
                 == (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
                       * ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)
                            * Qinv ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))))%Q)
      by ring.
    rewrite E1.
    rewrite (Qmult_inv_r
      ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)%Q)).
    + ring.
    + intro E. apply (Qlt_not_eq 0%Q
          ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))%Q).
      * unfold Qlt. cbn [Qnum Qden].
        pose proof (lne_fact_ge1 (Datatypes.S (n + n))) as Hg. lia.
      * exact (Qeq_sym _ _ E).
  - rewrite Nat2Z.inj_mul.
    unfold Qmult. cbn [Qnum Qden Pos.mul]. reflexivity.
Qed.

(* 正性件（Set 面）：0 < lne_B n 严格 *)
Theorem lne_B_posT : forall n : nat, QltT 0 (lne_B n).
Proof.
  intro n. apply Qlt_to_QltT. rewrite lne_B_closed. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* §E 三件套 Set 规格与窗匹配件                                          *)
(* ============================================================ *)

(* 正性 + 指数上界 + 整性 三件套合一 Set 规格 *)
Definition lne_three_spec : Set :=
  sigT (fun n : nat =>
    And (QltT 0 (lne_B n))
      (And (QleT' (lne_B n) (Qinv (lne_p4 n)))
           (sigT (fun m : Z =>
             QeqT (lne_B n * q_fact (Datatypes.S (n + n))%nat)
                    (m # 1))))).

Definition lne_three_spec_holds : forall n : nat, lne_three_spec :=
  fun n => existT _ n
    ((lne_B_posT n, (lne_B_le_p4 n, lne_B_int n))).

(* 窗匹配件：lne_B n 严格落入判定窗 2^{-n}（n ≥ 1；4^{-n} < 2^{-n} 链） *)
Lemma lne_B_lt_p2 : forall n : nat, (1 <= n)%nat ->
  QltT (lne_B n) (Qinv (ln2i_p2 n)).
Proof.
  intros n Hn. apply Qlt_to_QltT.
  apply (Qle_lt_trans (lne_B n) (Qinv (lne_p4 n)) (Qinv (ln2i_p2 n))).
  - apply QleT'_to_Qle. apply lne_B_le_p4.
  - assert (Huv : Qlt (ln2i_p2 n) (lne_p4 n)).
    { rewrite ln2i_p2_Z. rewrite lne_p4_Z. rewrite lne_pow4.
      pose proof (Nat.pow_lt_mono_r 2 n (2 * n) ltac:(lia) ltac:(lia)) as Hp.
      unfold Qlt. cbn [Qnum Qden]. lia. }
    pose proof (lne_p4_pos n) as Hp4.
    assert (Hu0 : Qlt 0 (ln2i_p2 n)) by apply ln2i_p2_pos.
    exact (proj1 (Qinv_lt_contravar (ln2i_p2 n) (lne_p4 n) Hu0 Hp4) Huv).
Qed.

(* 消费件：载体严格落入 UpReqLn2Irrational 判定窗 ln2i_e n = 2^{-n} *)
Theorem lne_B_in_window : forall n : nat, (1 <= n)%nat ->
  QltT (lne_B n) (ln2i_e n).
Proof.
  intros n Hn. unfold ln2i_e. apply lne_B_lt_p2. exact Hn.
Qed.

(* ============================================================ *)
(* §F 条件形收口消费（真走母定理，零旁路）                                *)
(* ============================================================ *)

Theorem lne_ln2_irrational_cond : forall (Hesc : ln2i_escape_spec) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hesc q.
  exact (ln2i_irrational_criterion_cond Hesc q).
Qed.

(* ============================================================ *)
(* §G 提取探针 + 公理面自审                                              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction lne_three_spec_holds lne_B_int lne_B_lt_p2
  lne_B_in_window lne_ln2_irrational_cond lne_B lne_p4.

Print Assumptions lne_three_spec_holds.
Print Assumptions lne_B_le_p4.
Print Assumptions lne_B_int.
Print Assumptions lne_B_in_window.
Print Assumptions lne_ln2_irrational_cond.
