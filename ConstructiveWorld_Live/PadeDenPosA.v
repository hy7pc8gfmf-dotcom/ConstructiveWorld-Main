(* ============================================================ *)
(* PadeDenPosA.v — Padé 分母正性严格正版（挂账 a 攻坚）               *)
(* 席位 CWE（批次 E-STAGING-CWE），2026-09-14                       *)
(* ============================================================ *)
(* 使命：UpReqPadeDenPos.v 挂账 a 的严格正版——0 ≤ x < 2 处            *)
(*   QltT 0 (pade_den n x)（对一切 n；非负版 pdp_den_pos 只给         *)
(*   QleT' 0 且前提 x ≤ 1）。真零点排除注记：n=1 分母 1−x/2 在 x=2    *)
(*   恰为零，故严格版前提取 x < 2（半开区间 [0,2) 天然排除真零点）。    *)
(*                                                                 *)
(* 数学路线（挂账 a 的「首对严格 + 逐对配比细化」路线走通）：            *)
(*   系数比 c_k/c_{k+1} = (2n−k)(k+1)/(n−k) 的逐 k 下界从 1 细化到 2   *)
(*   （pdpa_R_ge_2：2(n−k) ≤ (2n−k)(k+1) ⟺ k(2n+1−k) ≥ 0，nia），      *)
(*   于是衰减 t_{k+1} ≤ t_k 对 x ≤ 2 全段成立（比式消元：               *)
(*   c_{k+1}·(x·x^k) ≤ c_{k+1}·(R·x^k) == (c_{k+1}·R)·x^k == c_k·x^k，  *)
(*   其中 c_k == c_{k+1}·R 由既有 pdp_coeff_ratio 直供）；首对严格       *)
(*   t_1 = c_1·x < c_1·2 == c_0 == t_0 由 qltT_mult_ltT_compat_r        *)
(*   （0 < c_1）+ c_1·2 == c_0（pdpa_c1_2_c0，经 R n 0 == 2 与          *)
(*   pdp_coeff_ratio n 0 组装）闭合。引擎 altsum_pos_strict             *)
(*   （首对严格 + 全指标非负递减 + n ≥ 2）放电；n=0 特例由              *)
(*   pade_den 0 x == 1 直接收口。                                       *)
(*                                                                 *)
(* 对位台账：UpReqPadeDenPos.v 头注挂账 a（「严格正版 QltT 0：引擎出口   *)
(*   altsum_pos_strict 需首对严格 t_1 < t_0……本轮不攻」）——本席以       *)
(*   配比下界 1→2 细化攻下；挂账 b（x∈(1,2] 段递减装配需比式消元）——    *)
(*   本席比式消元即 pdp_coeff_ratio 改写步，一并清偿；挂账 c（误差积分   *)
(*   表示）维持挂账。CWA 报告注记「x<2 时 altsum_pos_strict 路线已可探」 *)
(*   在此兑现。                                                        *)
(*                                                                 *)
(* 交付件（pdpa_ 前缀，全库防撞 grep=0）：                             *)
(*   pdpa_c0_nz          c_0 ≠ 0（pdp_coeff_pos_any 折叠面直供）        *)
(*   pdpa_c0_one         pade_coeff n 0 == 1（阶乘分子分母对消）         *)
(*   pdpa_R0_two         pdp_R n 0 == 2（首对比值精确值）                *)
(*   pdpa_c1_2_c0        c_1·2 == c_0（首对严格性的代数核）              *)
(*   pdpa_R_ge_2         0 ≤ k < n ⟹ 2 ≤ pdp_R n k（配比下界 1→2 细化）  *)
(*   pdpa_term_decay     k < n、0 ≤ x < 2 ⟹ t_{k+1} ≤ t_k（x ≤ 2 全段）  *)
(*   pdpa_g1_lt_g0       1 ≤ n、x < 2 ⟹ t_1 <T t_0（首对严格）           *)
(*   pdpa_den0_one       pade_den 0 x == 1（n=0 特例）                   *)
(*   pdpa_den_pos_strict 主定理：0 ≤ x < 2 ⟹ QltT 0 (pade_den n x)      *)
(*   pdpa_den_pos_strict_lt1  挂账 a 原形桥：0 ≤ x < 1 ⟹ 同结论         *)
(*                                                                 *)
(* 红线自审：① 零承认件（依赖全为库内 Closed 件：S01–S03 薄壳 +        *)
(*   UpReqPadeExp/UpReqAltSumPos/UpReqPadeDenPos）；② 语句面全 Set      *)
(*   （QltT/QleT/QleT' bool·Or 反映形；Prop 序仅证内转译——Qle/Qeq      *)
(*   中间件全部 assert 消化，不留语句面前提位）；③ 全件 Qed 真证        *)
(*   （nia 比式 + Qmult_comp 项式组装 + qeq 链），无降级占位；④ 可提取  *)
(*   （G3 探针独立文件实测 Obj.magic=0）。                              *)
(* 编译配方：source Live/toolchain/env.sh && cd Live/build &&          *)
(*   rocq c -Q . '' PadeDenPosA.v（cpu_guard 包裹，-j2 上限）。          *)
(* 依赖：CW_ConstructiveWorld_219；UpReqPadeExp（pade_den/pade_coeff/  *)
(*   q_pow/q_fact/sum_upto 定义面）；UpReqAltSumPos（altsum 引擎出口    *)
(*   altsum_pos_strict 与 qeq/qltT 运输件）；UpReqPadeDenPos（pdp_g/    *)
(*   pdp_R/pdp_coeff_ratio/pdp_den_altsum/pdp_g_nonneg/                 *)
(*   pdp_g_decay_hi 非负版机器）。                                     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Psatz.

(* ============================================================ *)
(* Part 0：系数特殊值（c_0 == 1、首对比值 R n 0 == 2、c_1·2 == c_0）     *)
(* ============================================================ *)

(* c_0 ≠ 0（Qeq 形否定；折叠面直供：pdp_coeff_pos_any 对一切 k 无条件正） *)
Lemma pdpa_c0_nz : forall n : nat, ~ (pade_coeff n 0%nat == 0%Q).
Proof.
  intros n Heq. apply (Qlt_not_eq 0%Q (pade_coeff n 0%nat)).
  - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
  - apply Qeq_sym. exact Heq.
Qed.

(* c_0 == 1：pade_coeff n 0 = (2n)!·n!/((2n)!·(0!·n!))——Qmult_comp
   项式组装 + Qmult_inv_r 收口（q_fact 0 == 1 由转换消解，免改写） *)
Lemma pdpa_c0_one : forall n : nat, pade_coeff n 0%nat == 1%Q.
Proof.
  intro n. unfold pade_coeff, Qdiv.
  replace (2 * n - 0)%nat with (2 * n)%nat by lia.
  replace (n - 0)%nat with n%nat by lia.
  apply (Qeq_trans
    (q_fact (2 * n) * q_fact n *
     Qinv (q_fact (2 * n) * (q_fact 0 * q_fact n)))
    (q_fact (2 * n) * (q_fact 0 * q_fact n) *
     Qinv (q_fact (2 * n) * (q_fact 0 * q_fact n)))).
  - apply (Qmult_comp (q_fact (2 * n) * q_fact n)
             (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    + apply (Qmult_comp (q_fact (2 * n)) (q_fact (2 * n))
               (Qeq_refl (q_fact (2 * n))) (q_fact n) (q_fact 0 * q_fact n)).
      * apply Qeq_sym.
        apply (Qeq_trans (q_fact 0 * q_fact n) (1%Q * q_fact n) (q_fact n)).
        -- apply (Qmult_comp (q_fact 0) 1%Q (Qeq_refl (q_fact 0))
                    (q_fact n) (q_fact n) (Qeq_refl (q_fact n))).
        -- apply Qmult_1_l.
    + apply Qeq_refl.
  - apply (Qmult_inv_r (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    intro Heq. apply (Qlt_not_eq 0%Q (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    + apply (Qmult_lt_0_compat (q_fact (2 * n)) (q_fact 0 * q_fact n)).
      * apply q_fact_pos.
      * apply (Qmult_lt_0_compat (q_fact 0) (q_fact n)); apply q_fact_pos.
    + apply Qeq_sym. exact Heq.
Qed.

(* 首对比值精确值：pdp_R n 0 == 2（(2n)·1/n == 2——Z 层 S(2n−1)==2·S(n−1)
   lia 定值 + Qmult_inv_r 尾收口） *)
Lemma pdpa_R0_two : forall n : nat, (1 <= n)%nat -> pdp_R n 0%nat == 2%Q.
Proof.
  intros n Hn. unfold pdp_R.
  assert (EA : (Z.of_nat (Datatypes.S (2 * n - Datatypes.S 0)) # 1)%Q ==
               ((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q).
  { unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. lia. }
  rewrite EA.
  replace (Z.of_nat (Datatypes.S 0) # 1)%Q with 1%Q by reflexivity.
  apply (Qeq_trans
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q * 1%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q)
    (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
            Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q))).
  - ring.
  - apply (Qeq_trans
      (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
              Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q))
      (2%Q * 1%Q) 2%Q).
    + apply (Qmult_comp 2%Q 2%Q (Qeq_refl 2%Q)
               ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
                Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q)
               1%Q
               (Qmult_inv_r (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q
                            (pdp_ZS1_nz (n - Datatypes.S 0)))).
    + ring.
Qed.

(* 首对严格性的代数核：c_1·2 == c_0（pdp_coeff_ratio n 0 的 Qeq 换向
   + pdpa_R0_two 换元，Qmult_comp 项式组装） *)
Lemma pdpa_c1_2_c0 : forall n : nat, (1 <= n)%nat ->
  pade_coeff n 1%nat * 2%Q == pade_coeff n 0%nat.
Proof.
  intros n Hn.
  apply (Qeq_trans (pade_coeff n 1%nat * 2%Q)
                   (pade_coeff n 1%nat * pdp_R n 0%nat)
                   (pade_coeff n 0%nat)).
  - apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) 2%Q (pdp_R n 0%nat)
             (Qeq_sym (pdp_R n 0%nat) 2%Q (pdpa_R0_two n Hn))).
  - apply Qeq_sym. apply pdp_coeff_ratio. lia.
Qed.

(* ============================================================ *)
(* Part 1：配比下界 1→2 细化 + x ≤ 2 全段衰减                           *)
(* ============================================================ *)

(* 配比下界细化：0 ≤ k < n ⟹ 2 ≤ pdp_R n k
   （pdpa_R_ge_1 的 1 下界细化到 2：2(n−k) ≤ (2n−k)(k+1)
   ⟺ k(2n+1−k) ≥ 0，k ≥ 0 且 k ≤ n−1 时恒真，nia 收口） *)
Lemma pdpa_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2%Q (pdp_R n k).
Proof.
  intros n k Hk. unfold pdp_R.
  assert (Hdinv : QleT' 0
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Hlit : QleT'
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    ((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1)%Q *
     (Z.of_nat (Datatypes.S k) # 1)%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul]. nia. }
  apply (qleT'_trans 2%Q
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    ((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1)%Q *
     (Z.of_nat (Datatypes.S k) # 1)%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
  - apply qeq_leT'.
    apply (Qeq_trans 2%Q
      (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
              Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q))
      (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
    + apply (Qeq_trans 2%Q (2%Q * 1%Q)
               (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q))).
      * ring.
      * apply (Qmult_comp 2%Q 2%Q (Qeq_refl 2%Q) 1%Q
                 ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                  Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
                 (Qeq_sym ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                           Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
                          1%Q
                          (Qmult_inv_r (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q
                                       (pdp_ZS1_nz (n - Datatypes.S k))))).
    + ring.
  - apply (pdp_qmult_le_compat_r _ _
             (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
    + exact Hlit.
    + exact Hdinv.
Qed.

(* 项衰减（x ≤ 2 全段）：k < n、0 ≤ x < 2 ⟹ t_{k+1} ≤ t_k。
   比式消元（挂账 b 的清偿步）：t_{k+1} = c_{k+1}·(x·x^k)
   ≤ c_{k+1}·(R·x^k)（qleT'_mult 两次：x ≤ 2 ≤ R）
   == (c_{k+1}·R)·x^k == c_k·x^k（pdp_coeff_ratio 换写）。 *)
Lemma pdpa_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QltT x 2 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true) by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  assert (Hxq : QleT' 0 (q_pow x k))
    by (apply Qle_to_QleT'; apply q_pow_nonneg; apply QleT'_to_Qle; exact Hx).
  assert (HxR : QleT' x (pdp_R n k)).
  { apply (qleT'_trans x 2%Q (pdp_R n k)).
    - apply qltT_leT'. exact Hx2.
    - apply pdpa_R_ge_2. exact Hk. }
  apply (qleT'_trans
    (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
    (pade_coeff n (Datatypes.S k) * (pdp_R n k * q_pow x k))
    (pade_coeff n k * q_pow x k)).
  - apply (qleT'_mult_compat_l (x * q_pow x k) (pdp_R n k * q_pow x k)
             (pade_coeff n (Datatypes.S k))).
    + apply qltT_leT'. apply pdp_coeff_pos_any.
    + apply (qleT'_mult_compat_r x (pdp_R n k) (q_pow x k) Hxq HxR).
  - apply qeq_leT'.
    apply (Qeq_trans (pade_coeff n (Datatypes.S k) * (pdp_R n k * q_pow x k))
                     ((pade_coeff n (Datatypes.S k) * pdp_R n k) * q_pow x k)
                     (pade_coeff n k * q_pow x k)).
    + ring.
    + apply (Qmult_comp (pade_coeff n (Datatypes.S k) * pdp_R n k)
               (pade_coeff n k)
               (Qeq_sym (pade_coeff n k)
                        (pade_coeff n (Datatypes.S k) * pdp_R n k)
                        (pdp_coeff_ratio n k Hk))
               (q_pow x k) (q_pow x k) (Qeq_refl (q_pow x k))).
Qed.

(* 首对严格：1 ≤ n、x < 2 ⟹ t_1 <T t_0。
   c_1·x <T c_1·2（qltT_mult_ltT_compat_r，0 < c_1）
   ==（两端 Qmult_comm/qltT_eq_compat 运输）c_1·x <T c_0，
   再经 pdp_g 展开换形（q_pow x 1 == x、q_pow x 0 == 1）。 *)
Lemma pdpa_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT x 2 -> QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hx2.
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E0 : (0 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (Hp0 : q_pow x 0%nat == 1%Q) by apply Qeq_refl.
  assert (Hp1 : q_pow x 1%nat == x).
  { apply (Qeq_trans (q_pow x 1%nat) (x * q_pow x 0%nat) x).
    - apply q_pow_succ.
    - apply (Qeq_trans (x * q_pow x 0%nat) (x * 1%Q) x).
      + apply (Qmult_comp x x (Qeq_refl x) (q_pow x 0%nat) 1%Q Hp0).
      + ring. }
  assert (Eg1 : pdp_g n x 1%nat == pade_coeff n 1%nat * x).
  { unfold pdp_g. rewrite E1.
    apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) (q_pow x 1%nat) x Hp1). }
  assert (Eg0 : pdp_g n x 0%nat == pade_coeff n 0%nat).
  { unfold pdp_g. rewrite E0.
    apply (Qeq_trans (pade_coeff n 0%nat * q_pow x 0%nat)
                     (pade_coeff n 0%nat * 1%Q) (pade_coeff n 0%nat)).
    - apply (Qmult_comp (pade_coeff n 0%nat) (pade_coeff n 0%nat)
               (Qeq_refl (pade_coeff n 0%nat)) (q_pow x 0%nat) 1%Q Hp0).
    - ring. }
  assert (Hm1 : pade_coeff n 1%nat * q_pow x 1%nat == pade_coeff n 1%nat * x).
  { apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) (q_pow x 1%nat) x Hp1). }
  assert (Hstep : QltT (x * pade_coeff n 1%nat) (2%Q * pade_coeff n 1%nat))
    by (apply (qltT_mult_ltT_compat_r x 2%Q (pade_coeff n 1%nat));
        [apply pdp_coeff_pos_any | exact Hx2]).
  assert (Hr1 : QltT (x * pade_coeff n 1%nat) (pade_coeff n 1%nat * 2%Q))
    by (apply (qltT_eq_compat_r (pade_coeff n 1%nat * 2%Q)
                 (2%Q * pade_coeff n 1%nat) (x * pade_coeff n 1%nat));
        [apply Qmult_comm | exact Hstep]).
  assert (Hr2 : QltT (x * pade_coeff n 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_r (pade_coeff n 0%nat)
                 (pade_coeff n 1%nat * 2%Q) (x * pade_coeff n 1%nat));
        [apply Qeq_sym; apply pdpa_c1_2_c0; exact Hn | exact Hr1]).
  assert (Hl1 : QltT (pade_coeff n 1%nat * x) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (x * pade_coeff n 1%nat)
                 (pade_coeff n 1%nat * x) (pade_coeff n 0%nat));
        [apply Qmult_comm | exact Hr2]).
  assert (Hl2 : QltT (pade_coeff n 1%nat * q_pow x 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (pade_coeff n 1%nat * x)
                 (pade_coeff n 1%nat * q_pow x 1%nat) (pade_coeff n 0%nat));
        [apply Qeq_sym; exact Hm1 | exact Hl1]).
  assert (Hm1r : pade_coeff n 1%nat * q_pow x 1%nat == pdp_g n x 1%nat).
  { apply (Qeq_trans (pade_coeff n 1%nat * q_pow x 1%nat)
             (pade_coeff n 1%nat * x) (pdp_g n x 1%nat)).
    - exact Hm1.
    - apply Qeq_sym. exact Eg1. }
  assert (Hl3 : QltT (pdp_g n x 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (pade_coeff n 1%nat * q_pow x 1%nat)
                 (pdp_g n x 1%nat) (pade_coeff n 0%nat));
        [exact Hm1r | exact Hl2]).
  apply (qltT_eq_compat_r (pdp_g n x 0%nat) (pade_coeff n 0%nat)
            (pdp_g n x 1%nat) Eg0 Hl3).
Qed.

(* ============================================================ *)
(* Part 2：n=0 特例 + 主定理                                            *)
(* ============================================================ *)

(* pade_den 0 x == 1（sum_upto 1 单项：q_pow (−1) 0 == 1、
   q_pow x 0 == 1、c_0 == 1 三换形后 ring） *)
Lemma pdpa_den0_one : forall x : Q, pade_den 0 x == 1%Q.
Proof.
  intro x. unfold pade_den.
  cbn [sum_upto q_pow].
  rewrite pdpa_c0_one.
  ring.
Qed.

(* 主定理：0 ≤ x < 2 ⟹ 0 <T 分母（一切 n）。
   n=0：den == 1 直接收口；n ≥ 1：altsum_pos_strict 放电——
   全指标非负（pdp_g_nonneg）、全指标递减（k < n 走 pdpa_term_decay、
   k ≥ n 走 pdp_g_decay_hi 清零段）、首对严格（pdpa_g1_lt_g0）、
   2 ≤ S n；pade_den 桥（pdp_den_altsum）回原形。 *)
Theorem pdpa_den_pos_strict : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 2 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx2.
  destruct n as [| m].
  - apply (qeq_ltT 1%Q (pade_den 0%nat x)).
    + apply Qeq_sym. apply pdpa_den0_one.
    + apply qltT_0_1.
  - assert (Hxa : QleT' 0 x) by (apply altsum_QleT_to_QleT'; exact Hx0).
    assert (Hb : pade_den (Datatypes.S m) x ==
                 altsum (pdp_g (Datatypes.S m) x)
                        (Datatypes.S (Datatypes.S m)))
      by apply pdp_den_altsum.
    apply (qeq_ltT (altsum (pdp_g (Datatypes.S m) x)
                            (Datatypes.S (Datatypes.S m)))
                   (pade_den (Datatypes.S m) x)).
    + apply Qeq_sym. exact Hb.
    + apply (altsum_pos_strict (pdp_g (Datatypes.S m) x)
                 (Datatypes.S (Datatypes.S m))).
      * intro k. apply pdp_g_nonneg. exact Hxa.
      * intro k. destruct (Nat.leb (Datatypes.S k) (Datatypes.S m)) eqn:E.
        -- apply (pdpa_term_decay (Datatypes.S m) k x).
           ++ apply Nat.leb_le in E. lia.
           ++ exact Hxa.
           ++ exact Hx2.
        -- apply (pdp_g_decay_hi (Datatypes.S m) x k).
           ++ exact Hxa.
           ++ apply Nat.leb_gt in E. lia.
      * apply (pdpa_g1_lt_g0 (Datatypes.S m) x).
        -- lia.
        -- exact Hx2.
      * lia.
Qed.

(* 挂账 a 原形桥：0 ≤ x < 1 ⟹ 同结论（x < 1 ≤ 2 上界传递） *)
Corollary pdpa_den_pos_strict_lt1 : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 1 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx1.
  apply pdpa_den_pos_strict.
  - exact Hx0.
  - assert (H12 : QleT' 1%Q 2%Q).
    { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. }
    exact (qltT_leT'_ltT x 1%Q 2%Q Hx1 H12).
Qed.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设                                          *)
(* ============================================================ *)
Print Assumptions pdpa_c0_nz.
Print Assumptions pdpa_c0_one.
Print Assumptions pdpa_R0_two.
Print Assumptions pdpa_c1_2_c0.
Print Assumptions pdpa_R_ge_2.
Print Assumptions pdpa_term_decay.
Print Assumptions pdpa_g1_lt_g0.
Print Assumptions pdpa_den0_one.
Print Assumptions pdpa_den_pos_strict.
Print Assumptions pdpa_den_pos_strict_lt1.
