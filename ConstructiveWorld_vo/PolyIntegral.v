(* ============================================================
   PolyIntegral.v —— [0,1] 上多项式（Q 系数列表）的构造性定积分
   基建（一期，Q 承载层、纯 Set）——解锁 UpReqPadeExp 所需的
   「[0,1] 上多项式型被积函数的构造性积分」。
   ── 使命：pint_integral 定积分主定义与正确性锚
   pint_integral_pow_poly : QeqT (pint_integral (pint_pow_poly k))
   (1/(Z.of_nat (S k) # 1))，即 ∫_0^1 x^k dx == 1/(k+1)；
   pint_eval_pow_poly（求值与 S03 q_pow 幂引擎一致）；线性性
   pint_integral_scale／pint_integral_add；逐项单调性
   pint_integral_nonneg／pint_integral_mono。
   ── 数学要点：多项式以系数列表表示（头＝常数项），pint_eval 为
   Horner 求值；定积分逐项定义 pint_integral p = Σ_k a_k/(k+1)
   （Q 除法全定义，无需良法定义前提）。线性性以等长列表为显式
   前提——不等长列表在 pint_add 尾接语义下线性性不真，前提诚实。
   逐点单调版本（0 ≤ p(x) ≤ 1 ⟹ 0 ≤ ∫p ≤ ∫1 == 1）需连续性／
   黎曼和极限机器，与柯西极限同留二期，本件不虚报强度。
   ── 替换声明：pint_integral_mono／pint_integral_nonneg／
   pint_integral_add／pint_integral_scale／pint_zero_div 五槽证明体
   经全量恒等核查与原版逐字同文（真替换 0 槽＋恒等守恒 5 槽）；
   语句面与引用面零改动。
   ── 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib
   QArith.QArith、QArith.Qabs、Lists.List、Arith.Arith、
   ZArith.ZArith、Lia、Extraction。
   ── 构造性注记：主定理 QeqT/QleT' Set 面（S02_CauchyComplete），
   Qle/Qeq 仅证内与内部支撑引理；pint_ 前缀避免命名冲突；纯构造性、
   零承认件、全 Qed 闭合。
   ── 编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" PolyIntegral.v。
   ============================================================ *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ============================================================ *)
(* §A 定义（全 Set 面；承载集 Q；多项式 = 系数列表，头为常数项）         *)
(* ============================================================ *)

(* 求值（Horner 复现）：pint_eval p x = a_0 + x·(a_1 + x·(…)) = Σ a_k x^k *)
Fixpoint pint_eval (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: p' => a + x * pint_eval p' x
  end.

(* 单项式积分值：∫_0^1 a·x^k dx = a/(k+1)（k+1 于 Q 内非零，除法全定义） *)
Definition pint_monomial_int (a : Q) (k : nat) : Q :=
  a / (Z.of_nat (Datatypes.S k) # 1).

(* 定积分（起始偏移 k 版，供归纳；第 i 项系数配分母 k+i+1） *)
Fixpoint pint_integral_from (p : list Q) (k : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' => pint_monomial_int a k + pint_integral_from p' (Datatypes.S k)
  end.

(* [0,1] 定积分主定义 *)
Definition pint_integral (p : list Q) : Q := pint_integral_from p 0.

(* x^k 的系数列表编码：k 个 0 接一个 1 *)
Fixpoint pint_pow_poly (k : nat) : list Q :=
  match k with
  | 0%nat => 1 :: []
  | Datatypes.S m => 0 :: pint_pow_poly m
  end.

(* 逐项运算：数乘 / 加法（等长语义）/ 取第 i 项系数（越界为 0） *)
Fixpoint pint_scale (a : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | c :: p' => a * c :: pint_scale a p'
  end.

Fixpoint pint_add (p q : list Q) : list Q :=
  match p with
  | [] => q
  | a :: p' =>
      match q with
      | [] => p
      | b :: q' => a + b :: pint_add p' q'
      end
  end.

Fixpoint pint_coeff (p : list Q) (i : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' =>
      match i with
      | 0%nat => a
      | Datatypes.S i' => pint_coeff p' i'
      end
  end.

(* ============================================================ *)
(* §B Q 层内部支撑（== / Qle 仅证内面）                               *)
(* ============================================================ *)

(* 0 除任意 Q 为 0（Qdiv = 乘 Qinv，零乘一步） *)
Lemma pint_zero_div : forall d : Q, 0 / d == 0.
Proof. intros d. unfold Qdiv. apply Qmult_0_l. Qed.

(* 乘法对除法的结合：(a·c)/d == a·(c/d) *)
Lemma pint_div_mult_assoc : forall a c d : Q, a * c / d == a * (c / d).
Proof. intros a c d. unfold Qdiv. ring. Qed.

(* 除法对加法的分配：(a+b)/d == a/d + b/d *)
Lemma pint_div_add_distr : forall a b d : Q, (a + b) / d == a / d + b / d.
Proof. intros a b d. unfold Qdiv. ring. Qed.

(* 1/(k+1) 严格正：Qinv 于 (n#1)（n>0）定义性折回 (1#n)；
   Z.of_nat (Datatypes.S k) 的符号判定经 Nat2Z 桥（Z0 支矛盾、Zneg 支非负矛盾） *)
Lemma pint_invS_pos : forall k : nat, Qlt 0 ((/ (Z.of_nat (Datatypes.S k) # 1))%Q).
Proof.
  intros k.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  assert (Hz : Z.of_nat (Datatypes.S k) <> 0%Z).
  { intros Hc. discriminate Hc. }
  destruct (Z.of_nat (Datatypes.S k)) as [| z | z] eqn:E.
  - exfalso. apply Hz. reflexivity.
  - unfold Qinv, Qlt. cbn [Qnum Qden Qmult]. lia.
  - exfalso. simpl in Hnn. lia.
Qed.

(* 单项式积分非负：0 ≤ a ⟹ 0 ≤ a/(k+1)（QleT' 进出，Qle 仅证内） *)
Lemma pint_monomial_int_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans 0 (0 * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                    (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))).
  - apply qeq_le. apply Qeq_sym. apply Qmult_0_l.
  - apply (Qmult_le_compat_r 0 a).
    + exact (QleT'_to_Qle 0 a Ha).
    + apply Qlt_le_weak. apply pint_invS_pos.
Qed.

(* ============================================================ *)
(* §C 求值正确性伴侣：pint_pow_poly k 的求值 ≡ q_pow x k（S03 幂引擎） *)
(* ============================================================ *)

Theorem pint_eval_pow_poly : forall (k : nat) (x : Q),
  QeqT (pint_eval (pint_pow_poly k) x) (q_pow x k).
Proof.
  intros k. induction k as [| m IH]; intros x.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT. ring.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    apply Qplus_0_l.
Qed.

(* ============================================================ *)
(* §D 正确性锚：∫ x^k == 1/(k+1)（含偏移推广版）                      *)
(* ============================================================ *)

(* 偏移推广：∫（起始偏移 k）x^m == 1/(k+m+1)。对 m 归纳；                *)
(*   nat 层 S 归一经 lia 桥（Hnat），Z.of_nat 原子两侧同步重写。          *)
Lemma pint_integral_from_pow_poly : forall (m k : nat),
  pint_integral_from (pint_pow_poly m) k == 1 / (Z.of_nat (Datatypes.S (k + m)) # 1).
Proof.
  intros m. induction m as [| m' IH]; intros k.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    rewrite Nat.add_0_r. apply Qplus_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    unfold pint_monomial_int. rewrite pint_zero_div.
    rewrite (IH (Datatypes.S k)).
    assert (Hnat : Datatypes.S (k + Datatypes.S m')
                   = Datatypes.S (Datatypes.S k + m')) by lia.
    rewrite Hnat.
    apply Qplus_0_l.
Qed.

(* 正确性锚（Set 面）：∫_0^1 x^k dx == 1/(k+1) *)
Theorem pint_integral_pow_poly : forall k : nat,
  QeqT (pint_integral (pint_pow_poly k)) (1 / (Z.of_nat (Datatypes.S k) # 1)).
Proof.
  intros k. apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (pint_integral_from_pow_poly k 0).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* 退化锚：∫ 1 == 1 *)
Theorem pint_integral_one : QeqT (pint_integral (pint_pow_poly 0)) (1 # 1).
Proof.
  apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (pint_integral_from_pow_poly 0 0).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* ============================================================ *)
(* §E 线性性（系数层面偏移版 + 0 偏移组装，Set 面）                    *)
(* ============================================================ *)

(* 数乘：∫（偏移 k）(a·p) == a·∫（偏移 k）p *)
Lemma pint_integral_from_scale : forall (a : Q) (p : list Q) (k : nat),
  pint_integral_from (pint_scale a p) k == a * pint_integral_from p k.
Proof.
  intros a p. induction p as [| c p' IH]; intros k.
  - cbn [pint_integral_from pint_scale]. symmetry. apply Qmult_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_scale].
    rewrite (pint_div_mult_assoc a c (Z.of_nat (Datatypes.S k) # 1)).
    rewrite (IH (Datatypes.S k)).
    unfold pint_monomial_int. ring.
Qed.

(* 加法（等长前提）：∫（偏移 k）(p+q) == ∫p + ∫q *)
Lemma pint_integral_from_add : forall (p q : list Q) (k : nat),
  length p = length q ->
  pint_integral_from (pint_add p q) k
  == pint_integral_from p k + pint_integral_from q k.
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_add]. ring.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from pint_monomial_int pint_add].
      injection Hlen as Hlen'.
      rewrite (IH q' (Datatypes.S k) Hlen').
      rewrite (pint_div_add_distr a b (Z.of_nat (Datatypes.S k) # 1)).
      unfold pint_monomial_int. ring.
Qed.

(* 组装（0 偏移，QeqT 面） *)
Theorem pint_integral_scale : forall (a : Q) (p : list Q),
  QeqT (pint_integral (pint_scale a p)) (a * pint_integral p).
Proof.
  intros a p.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  apply pint_integral_from_scale.
Qed.

Theorem pint_integral_add : forall p q : list Q,
  length p = length q ->
  QeqT (pint_integral (pint_add p q)) (pint_integral p + pint_integral q).
Proof.
  intros p q Hlen.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  apply pint_integral_from_add.
  exact Hlen.
Qed.

(* ============================================================ *)
(* §F 单调性加分件（逐项版；QleT' 面，Qle 仅证内）                     *)
(* ============================================================ *)

(* 逐项非负 ⟹ 偏移积分非负（Qplus_le_compat 双支：单项式非负支＋        *)
(*   归纳支；系数索引偏移由 pint_coeff 的 S 分支定义性对齐）             *)
Lemma pint_integral_from_nonneg : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral_from p k).
Proof.
  intros p. induction p as [| a p' IH]; intros k Hcoeff.
  - reflexivity.
  - cbn [pint_integral_from].
    apply Qle_to_QleT'.
    apply (Qplus_le_compat 0 (pint_monomial_int a k)
                           0 (pint_integral_from p' (Datatypes.S k))).
    + apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QleT'_to_Qle. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 逐项 ≤（等长）⟹ 偏移积分 ≤：双支 Qmult_le_compat_r（右因子 = 1/(k+1) *)
(*   严格正支经 pint_invS_pos）＋归纳支                                  *)
Lemma pint_integral_from_mono : forall (p q : list Q) (k : nat),
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen Hcoeff.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from].
      injection Hlen as Hlen'.
      apply Qle_to_QleT'.
      apply Qplus_le_compat.
      * unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply pint_invS_pos.
      * apply QleT'_to_Qle. apply IH.
        -- exact Hlen'.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 组装（0 偏移，QleT' 面） *)
Theorem pint_integral_nonneg : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral p).
Proof.
  intros p H.
  unfold pint_integral.
  exact (pint_integral_from_nonneg p 0 H).
Qed.


Theorem pint_integral_mono : forall p q : list Q,
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hlen Hcoeff.
  unfold pint_integral.
  exact (pint_integral_from_mono p q 0 Hlen Hcoeff).
Qed.


(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（编译期 stdout，verify 复核）        *)
(* ============================================================ *)

Print Assumptions pint_integral_pow_poly.
Print Assumptions pint_integral_one.
Print Assumptions pint_eval_pow_poly.
Print Assumptions pint_integral_scale.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_mono.
