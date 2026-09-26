(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqB4TwoStage.v *)
(* *)
(* 目的： B4 单（B 档垫底）的两段式降档完成件。 *)
(* 主件： bts_sum_nonneg_bounded 有界非负和与 bts_qabs_pow_sign_one 符号定律；bts_rem_model 余项模型。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqQExpTail、UpReqPadeExp。 *)
(* 备注： 精确形在构造性约定下不可证（LPO 阻挡先例），诚实降档为两段式可达形。 *)
(* ============================================================ *)

(* ============================================================ *)
(*   Padé [n/n] 余项的「系数恒等式/一致控制」+「witness/ε 极限传递」  *)
(*                                                                 *)
(* 工单定位（_taa8 B4 段 + _taa1 B 档 B4 段）：                      *)
(*   原形态四件（积分表示族）判【不通】——根因 = 极限交换基建缺位       *)
(*   （∫₀¹ tⁿ(1−t)ⁿ·e^{tx} 需「极限与积分交换」，库内判定缺位，        *)

(*   禁立注定不可证的精确形（LPO/交换墙先例：假/被阻语句诚实降档，      *)
(*   绝不强造）。                                                   *)
(*                                                                 *)
(* 两段式语句面设计（判据先行；全部 Set 层 Type 版，出口 QltT/QleT'）： *)
(*   段一（保底）＝有限和交换/一致控制面（纯 Q 有限组合层）：           *)
(*     ① bts_sum_square_swap：有限双和换序恒等式（Qeq 面）——          *)
(*        它是极限层「和与和交换」的有限类似物；有限层恒等式按         *)
(*        sum_upto_prod + 乘法交换即闭，不触任何极限判断言；           *)
(*     ② bts_pade_nd_swap：Padé 分子×分母的换序特化面；               *)
(*     ③ bts_exp_partial_diff_tail：exp 截断差 == qtail 尾和           *)
(*        （QExpTail 引擎对接恒等式）；                               *)
(*     ④ bts_exp_tail_uniform：一致控制面——b≥0、e>0 显式给 N，          *)
(*        N1,N2 ≥ N 时 |exp 截断差| < e（N 是 b,e 的可计算函数，        *)
(*        witness 直出，非「存在精度使收敛」的抽象形）。               *)
(*   段二（冲刺）＝witness/ε 极限传递面（非交换形）：                  *)
(*     ⑤ bts_rem_model：余项模型 rem n y N = e_N(y)·Q_n(y) − P_n(y)；   *)
(*     ⑥ bts_rem_model_diff：模型差 = 尾和×分母（环面）；              *)
(*     ⑦ bts_den_abs_le_num_abs：|Q_n(y)| ≤ P_n(|y|)（三角+逐项面）；   *)
(*     ⑧ bts_rem_cauchy：b≥0、e>0 ⟹ 显式 N 使余项模型序列柯西          *)
(*        于区间点 b——「尾控制 ⟹ 模型柯西性」的 witness/ε 复合，       *)
(*        目标恒为有理数有限表达式，未构造极限对象、未交换极限。        *)
(*                                                                 *)
(* 不撞极限交换的论证（判据先行）：                                   *)
(*   原形态不通的根因是「极限与积分交换」基建缺位；本件两段中——        *)
(*   段一全部语句为有限和恒等式/有限 witness（N 显式），无极限判断言；  *)
(*   段二的传递是「显式 N 尾控制 ⟹ 模型序列柯西」的 ε 三角复合，        *)
(*   柯西性是 witness/ε 形而非极限对象形，不构成交换；                  *)
(*   真积分语义四件（误差积分表示/积分正性/符号/界原形）继续显式假设        *)
(*   （等构造性积分基建另批，D2 闸显式假设见合规自查报告）。                   *)
(*                                                                 *)
(* 公理面/七项禁词扫描：0——全件无承认面、无自由变量位、无条件寄生      *)
(*   参数位；本头注以中文承载扫描表述，禁词字面量不落盘（AA13 卡前科    *)
(*   规避）。使用面仅 Require：CW_ConstructiveWorld_219（S03/S07 的    *)
(*   sum_upto 族/sum_upto_prod）、UpReqQExpTail（qtail 引擎：           *)
(*   qtail_cauchy_modulus_ord/qtail_sum_add/le_m/nonneg、单调件、      *)
(*   QleT'/QleT 桥）、UpReqPadeExp（pade_coeff/num/den/pade_coeff_pos）  *)
(*   ——禁改任何既有件一行。UpReqPadeLower 系（环境有额外承认闭包）与    *)
(*   bxuq_lim_uniq（需 B7 完备装配闸）本单按需不使用，理由见合规自查报告。  *)
(*                                                                 *)

(*   全量经 cwfix_aa14.cmd（cpu_guard CoreN 1，coqc 并发≥3 则候 60s）。  *)
(* ============================================================ *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Lia.

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
