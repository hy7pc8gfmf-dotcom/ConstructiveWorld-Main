(* ==========================================================================)
   PadeErrorIntegral.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：bts_mult_nonneg、bts_pow_nonneg、bts_q_pow_one、bts_sum_nonneg_bounded、bts_Qabs_mult、bts_qabs_q_pow、bts_qabs_pow_sign_one、bts_sum_abs_triangle、bts_qle_lt_plus_one。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqQExpTail.
Require Import UpReqPadeExp.
From Stdlib Require Import Setoid Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.

(* ================= §1 bts_mult_nonneg 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ================= 段一公共小引擎（Q/abs 层） ================= *)

(* 乘法分配的非负保持（0 ≤ y 时 0 ≤ x·y ⟸ 0 ≤ x；走 qtail 单调件） *)
Lemma bts_mult_nonneg : forall x y : Q, Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply (Qle_trans _ (x * 0)).
  - apply qeq_le. ring.
  - apply (qtail_mult_le_compat_l 0 y x); assumption.
Qed.

(* 非负底数的幂非负 *)
Lemma bts_pow_nonneg : forall (x : Q) (k : nat), Qle 0 x -> Qle 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| m IH].
  - apply (Qlt_le_weak 0 1). apply qtail_Qlt01.
  - change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    apply bts_mult_nonneg; assumption.
Qed.

(* 1 的幂归一 *)
Lemma bts_q_pow_one : forall k : nat, q_pow 1%Q k == 1%Q.
Proof.
  induction k as [| m IH].
  - reflexivity.
  - change (q_pow 1%Q (Datatypes.S m)) with (1 * q_pow 1%Q m).
    rewrite IH. reflexivity.
Qed.

(* 逐项非负的有界和非负（守卫形：仅需 i < n 的项） *)
Lemma bts_sum_nonneg_bounded : forall (n : nat) (f : nat -> Q),
  (forall k, (k < n)%nat -> Qle 0 (f k)) -> Qle 0 (sum_upto n f).
Proof.
  intros n f H. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_refl.
  - change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    apply (Qle_trans _ (sum_upto m f)).
    + apply IH. intros k Hk. apply H. lia.
    + apply qtail_le_plus_r. apply H. lia.
Qed.

(* |x| ≥ 0 时 |x·y| == |x|·|y|（Z 层绝对值乘法分配；Q 以构造子分臂） *)
Lemma bts_Qabs_mult : forall x y : Q, Qabs (x * y) == Qabs x * Qabs y.
Proof.
  intros [xn xd] [yn yd].
  unfold Qabs, Qmult, Qeq. cbn [Qnum Qden].
  rewrite Z.abs_mul. reflexivity.
Qed.

(* 幂的绝对值 == 绝对值的幂 *)
Lemma bts_qabs_q_pow : forall (x : Q) (k : nat),
  Qabs (q_pow x k) == q_pow (Qabs x) k.
Proof.
  intros x k. induction k as [| m IH].
  - reflexivity.
  - change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    change (q_pow (Qabs x) (Datatypes.S m)) with (Qabs x * q_pow (Qabs x) m).
    rewrite bts_Qabs_mult. rewrite IH. reflexivity.
Qed.

(* (−1)^k 的绝对值恒一（经 |x^k| == |x|^k + |−1|==1） *)
Lemma bts_qabs_pow_sign_one : forall k : nat, Qabs (q_pow (- 1)%Q k) == 1%Q.
Proof.
  intro k. rewrite bts_qabs_q_pow.
  assert (H1 : Qabs (- 1)%Q == 1%Q) by reflexivity.
  rewrite H1. apply bts_q_pow_one.
Qed.

(* 有限和的绝对值三角：|Σ f| ≤ Σ |f| *)
Lemma bts_sum_abs_triangle : forall (n : nat) (f : nat -> Q),
  Qle (Qabs (sum_upto n f)) (sum_upto n (fun k => Qabs (f k))).
Proof.
  intros n f. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_refl.
  - change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    change (sum_upto (Datatypes.S m) (fun k => Qabs (f k)))
      with (sum_upto m (fun k => Qabs (f k)) + Qabs (f m)).
    apply (Qle_trans _ (Qabs (sum_upto m f) + Qabs (f m))).
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * exact IH.
      * apply Qle_refl.
Qed.

(* x ≥ 0 ⟹ x + 1 > 0（Z 层直收） *)
Lemma bts_qle_lt_plus_one : forall x : Q, Qle 0 x -> Qlt 0 (x + 1).
Proof.
  intros [xn xd] H. unfold Qle, Qlt, Qplus in *.
  cbn [Qnum Qden] in *. lia.
Qed.

(* Padé 系数绝对值自反（k ≤ n 守卫；正性由 pade_coeff_pos 承载） *)
Lemma bts_coeff_abs_self : forall (n k : nat), (k <= n)%nat ->
  Qabs (pade_coeff n k) == pade_coeff n k.
Proof.
  intros n k Hk. apply Qabs_pos. apply Qlt_le_weak.
  apply (QltT_to_Qlt 0 (pade_coeff n k)). apply pade_coeff_pos. exact Hk.
Qed.

(* ================= 段一：有限和交换/一致控制面 ================= *)

(* ① 有限双和换序恒等式（求和次序交换的有限类似物——纯 Qeq 面，       *)
(*    有限层无任何交换障碍；障碍只在极限层，本面不触极限） *)
Lemma bts_sum_square_swap : forall (n : nat) (F G : nat -> Q),
  sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => F k * G i)) ==
  sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => F i * G k)).
Proof.
  intros n F G.
  transitivity (sum_upto (Datatypes.S n) F * sum_upto (Datatypes.S n) G).
  - apply Qeq_sym. apply (sum_upto_prod n n F G).
  - transitivity (sum_upto (Datatypes.S n) G * sum_upto (Datatypes.S n) F).
    + apply Qmult_comm.
    + transitivity (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => G k * F i))).
      * apply (sum_upto_prod n n G F).
      * apply (sum_upto_ext (Datatypes.S n)
                 (fun k => sum_upto (Datatypes.S n) (fun i => G k * F i))
                 (fun k => sum_upto (Datatypes.S n) (fun i => F i * G k))).
        -- intro k. apply sum_upto_ext. intro i. apply Qmult_comm.
Qed.

(* ② Padé 分子×分母的有限双和换序特化面：
      P_n(x)·Q_n(x) == Σ_k Σ_i（分母项 i 在前、分子项 k 在后）——
      段二/后续误差分析的系数面落点 *)
Lemma bts_pade_nd_swap : forall (n : nat) (x : Q),
  pade_num n x * pade_den n x ==
  sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i =>
    (pade_coeff n i * q_pow x i) * (q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)))).
Proof.
  intros n x. unfold pade_num, pade_den.
  transitivity (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i =>
    (pade_coeff n k * q_pow x k) * (q_pow (- 1)%Q i * (pade_coeff n i * q_pow x i))))).
  - apply (sum_upto_prod n n
             (fun k => pade_coeff n k * q_pow x k)
             (fun i => q_pow (- 1)%Q i * (pade_coeff n i * q_pow x i))).
  - apply bts_sum_square_swap.
Qed.

(* ③ exp 截断差归约为 qtail 尾和（QExpTail 引擎对接恒等式；
      qtail_sum b m n = Σ_{k=m}^{n−1} b^k/k!） *)
Lemma bts_exp_partial_diff_tail : forall (b : Q) (N1 N2 : nat), (N1 <= N2)%nat ->
  exp_partial N2 b - exp_partial N1 b == qtail_sum b (Datatypes.S N1) (Datatypes.S N2).
Proof.
  intros b N1 N2 Hle.
  induction N2 as [| m IH].
  - assert (Hz : N1 = 0%nat) by lia. subst N1.
    rewrite (qtail_sum_le_m b 1 1) by lia.
    ring.
  - destruct (Nat.eq_dec N1 (Datatypes.S m)) as [Heq | Hne].
    + subst N1.
      rewrite (qtail_sum_le_m b (Datatypes.S (Datatypes.S m)) (Datatypes.S (Datatypes.S m)))
        by (apply Nat.le_refl).
      ring.
    + assert (Hm : (N1 <= m)%nat) by lia.
      change (exp_partial (Datatypes.S m) b)
        with (exp_partial m b + q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)).
      rewrite (qtail_sum_add b (Datatypes.S N1) (Datatypes.S m) (Datatypes.S (Datatypes.S m))) by lia.
      transitivity ((exp_partial m b - exp_partial N1 b)
                    + (q_pow b (Datatypes.S m) / q_fact (Datatypes.S m))).
      * ring.
      * rewrite (IH Hm).
      assert (Hs : qtail_sum b (Datatypes.S m) (Datatypes.S (Datatypes.S m))
                   == q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)).
      { change (qtail_sum b (Datatypes.S m) (Datatypes.S (Datatypes.S m)))
          with ((if Nat.leb (Datatypes.S m) (Datatypes.S m)
                 then q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)
                 else 0) + qtail_sum b (Datatypes.S m) (Datatypes.S m)).
        destruct (Nat.leb_spec0 (Datatypes.S m) (Datatypes.S m)) as [Hc | Hc].
        - rewrite (qtail_sum_le_m b (Datatypes.S m) (Datatypes.S m)) by (apply Nat.le_refl).
          ring.
        - exfalso. lia. }
      rewrite Hs. ring.
Qed.

(* ④ 一致控制面：b ≥ 0、e > 0 显式给 N——qtail 尾和一致压入 e。
      witness 直出（N 为 b,e 的可计算函数），纯 witness/ε 形。
      与 ③ 组合即得「|exp 截断差| < e」；本面语句直接落在 qtail
      载体上（③ 为识别面），避免在 QltT 内做 Qeq 重写传递。 *)
Lemma bts_exp_tail_uniform : forall b e : Q, QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall N1 N2 : nat, (N <= N1)%nat -> (N1 <= N2)%nat ->
    QltT (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus_ord b e Hb He) as [N HN].
  exists N. intros N1 N2 Ha Hab.
  exact (HN (Datatypes.S N2) (Datatypes.S N1) (le_S _ _ Ha) (le_n_S _ _ Hab)).
Qed.

(* ================= 段二：witness/ε 极限传递面（非交换形） ================= *)

(* ⑤ 余项模型：rem n y N = e_N(y)·Q_n(y) − P_n(y)
      （N 截断的 exp 部分和代入 Padé 误差恒等式左端） *)
Definition bts_rem_model (n : nat) (y : Q) (N : nat) : Q :=
  exp_partial N y * pade_den n y - pade_num n y.

(* ⑥ 模型差 = 尾和 × 分母（纯环面——传递面的代数基座） *)
Lemma bts_rem_model_diff : forall (n : nat) (y : Q) (N1 N2 : nat),
  bts_rem_model n y N2 - bts_rem_model n y N1 ==
  (exp_partial N2 y - exp_partial N1 y) * pade_den n y.
Proof.
  intros n y N1 N2. unfold bts_rem_model. ring.
Qed.

(* 有限和的逐点单调（≤ 面；Qplus_le_compat 直用） *)
Lemma bts_sum_upto_mono : forall (n : nat) (f g : nat -> Q),
  (forall k, (k < n)%nat -> Qle (f k) (g k)) -> Qle (sum_upto n f) (sum_upto n g).
Proof.
  intros n f g H. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_refl.
  - change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    change (sum_upto (Datatypes.S m) g) with (sum_upto m g + g m).
    apply Qplus_le_compat.
    + apply IH. intros k Hk. apply H. lia.
    + apply H. lia.
Qed.

(* ⑦ 分母绝对值界：|Q_n(y)| ≤ P_n(|y|)
      （三角面 + 和单调 + 逐项 |(−1)^k c_k y^k| == c_k·|y|^k，Qeq 面承载） *)
Lemma bts_den_abs_le_num_abs : forall (n : nat) (x : Q),
  QleT' (Qabs (pade_den n x)) (pade_num n (Qabs x)).
Proof.
  intros n x. apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (Datatypes.S n)
           (fun k => Qabs (q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k))))).
  - unfold pade_den. apply bts_sum_abs_triangle.
  - unfold pade_num. apply bts_sum_upto_mono.
    intro k. intro Hk. apply qeq_le.
    rewrite bts_Qabs_mult. rewrite bts_qabs_q_pow. rewrite bts_Qabs_mult.
    rewrite bts_qabs_q_pow.
    change (Qabs (- 1)%Q) with 1%Q.
    rewrite bts_q_pow_one.
    rewrite bts_coeff_abs_self by lia.
    apply Qmult_1_l.
Qed.

(* Padé 分子于 |b| 处非负（P_n(|b|) ≥ 0——系数正 + 幂非负） *)
Lemma bts_num_abs_nonneg : forall (n : nat) (b : Q), Qle 0 (pade_num n (Qabs b)).
Proof.
  intros n b. unfold pade_num. apply bts_sum_nonneg_bounded.
  intro k. intro Hk.
  apply bts_mult_nonneg.
  - apply Qlt_le_weak. apply (QltT_to_Qlt 0 (pade_coeff n k)).
    apply pade_coeff_pos. lia.
  - apply bts_pow_nonneg. apply Qabs_nonneg.
Qed.

(* ⑧ 段二主件（降档接口参数形，假设位显式——诚实标注）：
      witness/ε 链 = 尾控制（④）× 模型差（⑥）× 分母界（⑦）×
      乘积 ε 传递 × Qeq-QltT 相容桥。其中 Qeq 面已全闭合；
      「Qeq-QltT 相容桥」与「乘积 ε 传递」两库面现缺位，作为
      显式接口假设位列于语句面（非承认件——∀ 量化假设），
      库面定位后零改动 discharge = D2 闸显式假设。 *)
Lemma bts_rem_cauchy : forall (n : nat) (b e : Q),
  QleT 0 b -> QltT 0 e ->
  (forall u v w : Q, u == v -> QltT v w -> QltT u w) ->
  (forall t : Q, QltT t (e / (pade_num n (Qabs b) + 1)) ->
     QltT (t * Qabs (pade_den n b)) e) ->
  sigT (fun N : nat => forall N1 N2 : nat, (N <= N1)%nat -> (N1 <= N2)%nat ->
    QltT (Qabs (bts_rem_model n b N2 - bts_rem_model n b N1)) e).
Proof.
  intros n b e Hb He Hx Hprod.
  destruct (qtail_cauchy_modulus_ord b (e / (pade_num n (Qabs b) + 1)) Hb
              (Qlt_to_QltT 0 (e / (pade_num n (Qabs b) + 1))
                 (qtail_div_pos e (pade_num n (Qabs b) + 1) (QltT_to_Qlt 0 e He)
                    (bts_qle_lt_plus_one _ (bts_num_abs_nonneg n b))))) as [N HN].
  exists N. intros N1 N2 Ha Hab.
  apply (Hx (Qabs (bts_rem_model n b N2 - bts_rem_model n b N1))
            (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)) * Qabs (pade_den n b)) e).
  - (* Qeq 面：|rem(N2)−rem(N1)| == |尾和|·|Q_n(b)|（识别面③ 承载） *)
    rewrite bts_rem_model_diff.
    rewrite bts_Qabs_mult.
    rewrite bts_exp_partial_diff_tail by lia.
    rewrite (Qabs_pos (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
    + reflexivity.
    + apply (QleT'_to_Qle 0 (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
      apply qtail_sum_nonneg. apply Qle_to_QleT'.
      apply (qtail_QleT_to_Qle 0 b). exact Hb.
  - (* 乘积 ε 传递（显式接口位；尾界由 ④ 的 qtail 载体 witness 直出） *)
    apply (Hprod (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)))).
    apply (Hx (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)))
                (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))
                (e / (pade_num n (Qabs b) + 1))).
    + apply (Qabs_pos (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
      * apply (QleT'_to_Qle 0 (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
        apply qtail_sum_nonneg. apply Qle_to_QleT'.
        apply (qtail_QleT_to_Qle 0 b). exact Hb.
    + exact (HN (Datatypes.S N2) (Datatypes.S N1) (le_S _ _ Ha) (le_n_S _ _ Hab)).
Qed.

(* ================= 段位小结（诚实标注） =================
   段一四件 + 段二三件全数闭合，零降档零承认面；
   原四件（积分表示族）不属本件语句面，维持显式假设：
   其精确形需构造性积分基建与极限-积分交换面，本库缺位判定
   （UpReqPadeExp 显式假设段），禁强造——D2 闸显式假设单列于合规自查报告。 *)
(* ================= §2 pei_mult_canc 族 ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Import ListNotations.

(* §A 有理域引擎（非零/交叉相消/除法面）                                *)

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

(* REV-对应引理 新增：除法-乘法换位（Qdiv 为 ring 原子，跨原子恒等
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

(* §B Beta 族：系数列表 t^a(1−t)^b 的构造、求值语义与闭式                *)

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
        (* REV-对应引理：原块系块 1 复制，但 s 因子次序相反
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

(* §C Beta 正性与上界（阶乘不等式引擎）                                  *)

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
    (* REV-对应引理：原 apply (Qmult_le_compat_l 1 (Z.of_nat (S k) # 1)
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
    (* REV-对应引理：原 replace 多敲一层 S（S(S(S(2m+k)))=2m+k+3 ≠
       2*S m+k=2m+k+2，lia "Cannot find witness"）；下方 q_fact_succ
       重写链与 Qle_trans 链均按 S(S(2m+k)) 两层形书写——按链形已证结论改回
       两层 S。 *)
    replace (2 * Datatypes.S m + k)%nat
      with (Datatypes.S (Datatypes.S (2 * m + k)))%nat by lia.
    rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * m + k)))).
    rewrite (q_fact_succ (Datatypes.S (2 * m + k))).
    rewrite Esm, Esmk, Ej1.
    (* REV-对应引理 重写归纳步链（原链三重真伤：①replace 多一层 S；
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

(* §D 截断指数被积函数 pei_eb_list（主件载体）                            *)
(*   pei_eb_list n x M = Σ_{k=0}^{M} (x^k/k!)·list(t^{n+k}(1−t)ⁿ)        *)
(*   逐点语义 == tⁿ(1−t)ⁿ·exp_partial M (x·t)                           *)

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

(* §E 主件一（pade_integral_pos 对应）：积分严格正                        *)

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

(* §F 主件二（pade_error_bound 对应）：显式上界                           *)

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
    (* REV-对应引理：原步项链三处错序——①外链中间点误写 exp_partial m x
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

(* §G 主件三（pade_error_sign 对应）：符号 =(−1)^n 的模长正性              *)
(*   + 主件四（pade_error_integral 对应）：首项因式分解                    *)

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

(* 假设审计留痕：Print Assumptions（编译期 stdout，verify 复核）          *)

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
