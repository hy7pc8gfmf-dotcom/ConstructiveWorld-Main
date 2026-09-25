(* ============================================================ *)
(* UpAblMetaDivQ.v —— Q 层 Bernoulli 幂下界与 Doeblin 界无界性件      *)
(*                                                              *)
(* 使命：本件形式化两件 Q 层独立结论：                                *)
(*   件① mqd_bernoulli_lower：Bernoulli 幂下界                        *)
(*        (1−x)^N ≥ 1−N·x（0≤x≤1，QleT' 出口，N 归纳一次成型）——      *)
(*        库内 mixe_bern_lower（(1+w)^k ≥ 1+k·w）与 mixe_bern_sharp    *)
(*        均为上/配对方向，下界方向自建；配套 mqd_bern_complement      *)
(*        以 mixe_bern_sharp 供给 (1−w)^k·(1+k·w) ≤ 1 的 QleT' 形；    *)
(*   件② mqd_q_doeblin_bound_unbounded：Q 层 Doeblin 界无界性          *)
(*        （QltT 见证形）：forall N lo0 r, 0<lo0, 0<r, r<1 →           *)
(*        sigT (fun lo => And (0<lo) (And (lo<lo0) (r < (1−lo²)^N)))， *)
(*        见证 lo := Qmin (lo0/2) ((1−r)·inv(S N))（除法以倒数积        *)
(*        承载）；两态链口径：偏移 w := lo²/2 时收缩因子 1−lo²，        *)
(*        TV₀=1、TV(n) = (1−lo²)ⁿ——本件承载其 Q 层纯代数因子面。      *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、UpReqMixLogE；              *)
(*        stdlib QArith.QArith、QArith.Qminmax、ZArith.ZArith、        *)
(*        Arith.Arith、Lia、micromega.Lqa。                            *)
(* 对标：mathlib bernoulli_inequality（幂下界形）；stdlib QArith       *)
(*        序引理族（Qmult_lt_compat_r、Q.min_glb_lt 等）。              *)
(* 构造性注记：语句面全 Set 层出口（QltT/QleT'，S01.And:=A*B 合取，    *)
(*        sigT 见证），前件显式正性证书，无 Prop 泄露；零假设位、       *)
(*        零承认、可提取；分式序接口引理以显式 Z 序引理链构造           *)
(*        （逐位显式归约与正性见证，不经一键算术自动战术）；            *)
(*        定理 A 以 Defined 收束（见证 lo 可提取可计算）。              *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 护航，信任缓存 vo 树 -Q 映射。    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqMixLogE.
From Stdlib Require Import QArith.QArith QArith.Qminmax ZArith.ZArith
               Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import micromega.Lqa.

Open Scope Q_scope.

(* ============================================================ *)
(* 第 0 层：幂载体与 (S n) 倒数数字面                                *)
(* ============================================================ *)

(* 幂载体（本件自备 Fixpoint：形状同 mixe_qpow/qpow，库内各件自备      *)
(* 同形件为惯例；定理 A 语句面用本件载体，保持 mqd_ 前缀自洽）         *)
Fixpoint mqd_pow (w : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | Datatypes.S m => w * mqd_pow w m
  end.

(* (S n) 的 Q 倒数：1/(S N)，除法以倒数积承载（规格书见证 min 项）      *)
Definition mqd_invSN (n : nat) : Q := (1 # Pos.of_nat (Datatypes.S n))%Q.

Lemma mqd_znat_le_posS : forall n : nat,
  (Z.of_nat n <= Z.pos (Pos.of_nat (Datatypes.S n)))%Z.
Proof.
  intro n. induction n as [| m IH].
  - change (Z.of_nat 0) with 0%Z.
    apply Z.lt_le_incl. apply Pos2Z.pos_is_pos.
  - rewrite Nat2Z.inj_succ.
    replace (Z.pos (Pos.of_nat (Datatypes.S (Datatypes.S m))))
      with (Z.pos (Pos.succ (Pos.of_nat (Datatypes.S m)))) by reflexivity.
    rewrite Pos2Z.inj_succ. lia.
Qed.

Lemma mqd_invSN_pos : forall n : nat, Qlt 0 (mqd_invSN n).
Proof.
  intro n. unfold mqd_invSN, Qlt. cbn [Qnum Qden].
  (* 目标即 Z 严格序 0·den lo < 1·den 0：以 Z.mul_0_l/Z.mul_1_l 显式    *)
  (* 归约两侧乘法，余下 0 < 1 由零侧分母位正数 1 的正性见证             *)
  (* Pos2Z.is_pos 构造                                                  *)
  rewrite Z.mul_0_l, Z.mul_1_l.
  exact (Pos2Z.is_pos 1%positive).
Qed.

Lemma mqd_invSN_le1 : forall n : nat, Qle (mqd_invSN n) 1.
Proof.
  intro n. unfold mqd_invSN, Qle. cbn [Qnum Qden].
  (* 目标即 Z 序 1·1 ≤ 1·den：两侧乘法以 Z.mul_1_l 归约，               *)
  (* 1 ≤ Z.pos den 经 Z.le_succ_l（1 与 Z.succ 0 可转换）化为           *)
  (* 0 < Z.pos den，由分母位 Pos.of_nat (S n) 的正性见证构造             *)
  rewrite !Z.mul_1_l.
  apply (proj2 (Z.le_succ_l 0 (Z.pos (Pos.of_nat (Datatypes.S n))))).
  apply Pos2Z.is_pos.
Qed.

Lemma mqd_kQ_inv_le : forall n : nat,
  Qle (mixe_qofnat n * mqd_invSN n) 1.
Proof.
  intro n. unfold mqd_invSN, Qle, Qmult, mixe_qofnat. cbn [Qnum Qden].
  rewrite Pos.mul_1_l.
  (* 目标即 Z 序 Z.of_nat n·1·1 ≤ 1·den：正数位积以 Pos.mul_1_l 归约，  *)
  (* 两侧乘法单位元以 Z.mul_1_r/Z.mul_1_l 逐步归约，                    *)
  (* 余下 Z 序结论即既有构造性引理 mqd_znat_le_posS n                   *)
  rewrite !Z.mul_1_r, Z.mul_1_l.
  exact (mqd_znat_le_posS n).
Qed.

(* ============================================================ *)
(* 件①：规格书缺口 G1——Bernoulli 幂下界 (1−x)^N ≥ 1−N·x（0≤x≤1）    *)
(* ============================================================ *)

Lemma mqd_bernoulli_lower : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (1 - mixe_qofnat n * x) (mqd_pow (1 - x) n).
Proof.
  intros x n Hx0 Hx1.
  assert (Hmx : Qle 0 (1 - x)) by exact (mixe_sub_nonneg x Hx1).
  induction n as [| n IH].
  - apply (mixe_qle_eq_l (1 - mixe_qofnat 0 * x) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mqd_pow].
    assert (Hk0 : Qle 0 (mixe_qofnat n)) by exact (mixe_qofnat_nonneg n).
    assert (Hxx : Qle 0 (mixe_qofnat n * x * x))
      by exact (mixe_qmult_nonneg (mixe_qofnat n * x) x
                  (mixe_qmult_nonneg (mixe_qofnat n) x Hk0 Hx0) Hx0).
    (* 链：A ≤ A + k·x² == (1−x)·(1−k·x) ≤ (1−x)·(1−x)^n *)
    assert (Hstep1 : Qle (1 - (1 + mixe_qofnat n) * x)
                         ((1 - (1 + mixe_qofnat n) * x)
                            + mixe_qofnat n * x * x))
      by lra.
    assert (Hstep2 : ((1 - (1 + mixe_qofnat n) * x)
                        + mixe_qofnat n * x * x)
                     == ((1 - x) * (1 - mixe_qofnat n * x))) by ring.
    assert (HBD : Qle (1 - (1 + mixe_qofnat n) * x)
                      ((1 - x) * (1 - mixe_qofnat n * x)))
      by exact (mixe_qle_eq_r _ _ _ Hstep1 Hstep2).
    assert (Hstep3 : Qle ((1 - x) * (1 - mixe_qofnat n * x))
                          ((1 - x) * mqd_pow (1 - x) n))
      by exact (mixe_qmult_le_l (1 - x) (1 - mixe_qofnat n * x)
                  (mqd_pow (1 - x) n) Hmx IH).
    apply (mixe_qle_eq_l (1 - mixe_qofnat (Datatypes.S n) * x)
             (1 - (1 + mixe_qofnat n) * x)
             ((1 - x) * mqd_pow (1 - x) n)).
    + rewrite (mixe_qofnat_S n). ring.
    + exact (Qle_trans _ _ _ HBD Hstep3).
Qed.

(* G1 出口：QleT' 面（Set 层判定证书） *)
Lemma mqd_bernoulli_lowerT : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' (1 - mixe_qofnat n * x) (mqd_pow (1 - x) n).
Proof.
  intros x n Hx0 Hx1. apply Qle_to_QleT'.
  exact (mqd_bernoulli_lower x n
           (QleT'_to_Qle 0 x Hx0) (QleT'_to_Qle x 1 Hx1)).
Qed.

(* 使用+桥接件：任务说明 (1−w)^k·(1+k·w) ≤ 1 形——直接使用库内            *)
(* mixe_bern_sharp（UpReqMixLogE F1 锐化 Bernoulli 上形），T 化出口     *)
Lemma mqd_bern_complement : forall (w : Q) (k : nat),
  QleT' 0 w -> QleT' w 1 ->
  QleT' (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1.
Proof.
  intros w k Hw0 Hw1. apply Qle_to_QleT'.
  exact (mixe_bern_sharp w k
           (QleT'_to_Qle 0 w Hw0) (QleT'_to_Qle w 1 Hw1)).
Qed.

(* ============================================================ *)
(* 件② 支撑：见证的界与收缩关键式                                    *)
(* ============================================================ *)

(* 见证收缩关键式：lo ≤ (1−r)·inv(S N) ∧ 0<lo<1 ⟹ N·lo² < 1−r         *)
Lemma mqd_shrink_key : forall (N : nat) (lo r : Q),
  Qlt 0 lo -> Qlt lo 1 -> Qlt 0 (1 - r) ->
  Qle lo ((1 - r) * mqd_invSN N) ->
  Qlt (mixe_qofnat N * (lo * lo)) (1 - r).
Proof.
  intros N lo r Hlo Hlo1 Hrp Hle.
  assert (Hlp : Qle 0 lo) by exact (Qlt_le_weak 0 lo Hlo).
  assert (Hu : Qlt 0 ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_l 0 (0 * mqd_invSN N) ((1 - r) * mqd_invSN N)).
    - ring.
    - exact (Qmult_lt_compat_r 0 (1 - r) (mqd_invSN N)
               (mqd_invSN_pos N) Hrp). }
  assert (Hs1 : Qle (lo * lo) (lo * ((1 - r) * mqd_invSN N)))
    by exact (mixe_qmult_le_l lo lo ((1 - r) * mqd_invSN N) Hlp Hle).
  assert (Hs2 : Qlt (lo * ((1 - r) * mqd_invSN N))
                    ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_r (1 * ((1 - r) * mqd_invSN N))
             ((1 - r) * mqd_invSN N) (lo * ((1 - r) * mqd_invSN N))).
    - ring.
    - exact (Qmult_lt_compat_r lo 1 ((1 - r) * mqd_invSN N) Hu Hlo1). }
  assert (Hs3 : Qlt (lo * lo) ((1 - r) * mqd_invSN N))
    by exact (Qle_lt_trans _ _ _ Hs1 Hs2).
  destruct N as [| m].
  - apply (mixe_qlt_eq_l (mixe_qofnat 0 * (lo * lo)) 0 (1 - r)).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + exact Hrp.
  - assert (HkQpos : Qlt 0 (mixe_qofnat (Datatypes.S m))).
    { pose proof (mixe_qofnat_nonneg m) as Hmn.
      apply (mixe_qlt_eq_r (1 + mixe_qofnat m)
               (mixe_qofnat (Datatypes.S m)) 0).
      - exact (Qeq_sym (mixe_qofnat (Datatypes.S m))
                 (1 + mixe_qofnat m) (mixe_qofnat_S m)).
      - lra. }
    assert (Hs4 : Qle (mixe_qofnat (Datatypes.S m)
                         * ((1 - r) * mqd_invSN (Datatypes.S m)))
                      (1 - r)).
    { apply (mixe_qle_eq_l
               (mixe_qofnat (Datatypes.S m)
                  * ((1 - r) * mqd_invSN (Datatypes.S m)))
               (mixe_qofnat (Datatypes.S m)
                  * mqd_invSN (Datatypes.S m) * (1 - r))
               (1 - r)).
      - ring.
      - apply (mixe_qle_eq_r
                 (mixe_qofnat (Datatypes.S m)
                    * mqd_invSN (Datatypes.S m) * (1 - r))
                 (1 * (1 - r)) (1 - r)).
        + exact (Qmult_le_compat_r (mixe_qofnat (Datatypes.S m)
                        * mqd_invSN (Datatypes.S m)) 1 (1 - r)
                        (mqd_kQ_inv_le (Datatypes.S m))
                        (Qlt_le_weak 0 (1 - r) Hrp)).
        + ring. }
    assert (Hs5 : Qlt (mixe_qofnat (Datatypes.S m) * (lo * lo))
                      (mixe_qofnat (Datatypes.S m)
                         * ((1 - r) * mqd_invSN (Datatypes.S m)))).
    { apply (mixe_qlt_eq_l
               (mixe_qofnat (Datatypes.S m) * (lo * lo))
               ((lo * lo) * mixe_qofnat (Datatypes.S m))
               (mixe_qofnat (Datatypes.S m)
                  * ((1 - r) * mqd_invSN (Datatypes.S m)))).
      - ring.
      - apply (mixe_qlt_eq_r
                 (((1 - r) * mqd_invSN (Datatypes.S m))
                    * mixe_qofnat (Datatypes.S m))
                 (mixe_qofnat (Datatypes.S m)
                    * ((1 - r) * mqd_invSN (Datatypes.S m)))
                 ((lo * lo) * mixe_qofnat (Datatypes.S m))).
        + ring.
        + exact (Qmult_lt_compat_r (lo * lo)
                   ((1 - r) * mqd_invSN (Datatypes.S m))
                   (mixe_qofnat (Datatypes.S m)) HkQpos Hs3). }
    exact (Qlt_le_trans _ _ _ Hs5 Hs4).
Qed.

(* 见证三界：0 < lo < lo0 ∧ lo < 1（lo := Qmin (lo0/2) ((1−r)·inv)）   *)
Lemma mqd_witness_bounds : forall (N : nat) (lo0 r : Q),
  Qlt 0 lo0 -> Qlt 0 r -> Qlt r 1 ->
  Qlt 0 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
  /\ Qlt (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) lo0
  /\ Qlt (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1.
Proof.
  intros N lo0 r Hlo0 Hr0 Hr1.
  assert (Hrp : Qlt 0 (1 - r)) by lra.
  assert (Hhalf : Qlt 0 (1 # 2)%Q) by lra.
  assert (Hr1l : Qlt (1 - r) 1) by lra.
  assert (Ha : Qlt 0 (lo0 * (1 # 2)%Q)).
  { apply (mixe_qlt_eq_l 0 (0 * (1 # 2)%Q) (lo0 * (1 # 2)%Q)).
    - ring.
    - exact (Qmult_lt_compat_r 0 lo0 (1 # 2)%Q Hhalf Hlo0). }
  assert (Hu : Qlt 0 ((1 - r) * mqd_invSN N)).
  { apply (mixe_qlt_eq_l 0 (0 * mqd_invSN N) ((1 - r) * mqd_invSN N)).
    - ring.
    - exact (Qmult_lt_compat_r 0 (1 - r) (mqd_invSN N)
               (mqd_invSN_pos N) Hrp). }
  split; [exact (Q.min_glb_lt _ _ _ Ha Hu) | split].
  - assert (Hminle : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                         (lo0 * (1 # 2)%Q))
      by exact (Q.le_min_l (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)).
    assert (Halo : Qlt (lo0 * (1 # 2)%Q) lo0).
    { apply (mixe_qlt_eq_l (lo0 * (1 # 2)%Q) ((1 # 2)%Q * lo0) lo0).
      - ring.
      - apply (mixe_qlt_eq_r (1 * lo0) lo0 ((1 # 2)%Q * lo0)).
        + ring.
        + exact (Qmult_lt_compat_r (1 # 2)%Q 1 lo0 Hlo0 Hhalf). }
    exact (Qle_lt_trans _ _ _ Hminle Halo).
  - assert (Hminle : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                         ((1 - r) * mqd_invSN N))
      by exact (Q.le_min_r (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)).
    assert (Hule : Qle ((1 - r) * mqd_invSN N) (1 - r)).
    { apply (mixe_qle_eq_l ((1 - r) * mqd_invSN N)
               (mqd_invSN N * (1 - r)) (1 - r)).
      - ring.
      - apply (mixe_qle_eq_r (mqd_invSN N * (1 - r)) (1 * (1 - r)) (1 - r)).
        + exact (Qmult_le_compat_r (mqd_invSN N) 1 (1 - r)
                    (mqd_invSN_le1 N) (Qlt_le_weak 0 (1 - r) Hrp)).
        + ring. }
    exact (Qle_lt_trans _ _ _ (Qle_trans _ _ _ Hminle Hule) Hr1l).
Qed.

(* ============================================================ *)
(* 件②：定理 A——Q 层 Doeblin 界无界性（QltT 见证形，规格书 §1.2）      *)
(*   语句与规格书 §1.2 逐点对应：0<lo0/0<r/r<1 以 QltT 证书面承载，      *)
(*   合取以 S01.And（Set 积型）承载；结论第三支即 QltT r ((1−lo²)^N)。  *)
(* ============================================================ *)

Theorem mqd_q_doeblin_bound_unbounded :
  forall (N : nat) (lo0 r : Q),
    QltT 0 lo0 -> QltT 0 r -> QltT r 1 ->
    sigT (fun lo : Q =>
      And (QltT 0 lo)
        (And (QltT lo lo0)
           (QltT r (mqd_pow (1 - lo * lo) N)))).
Proof.
  intros N lo0 r Hlo0T Hr0T Hr1T.
  assert (Hlo0 : Qlt 0 lo0) by exact (QltT_to_Qlt 0 lo0 Hlo0T).
  assert (Hr0 : Qlt 0 r) by exact (QltT_to_Qlt 0 r Hr0T).
  assert (Hr1 : Qlt r 1) by exact (QltT_to_Qlt r 1 Hr1T).
  refine (existT (fun lo : Q =>
             And (QltT 0 lo)
               (And (QltT lo lo0)
                  (QltT r (mqd_pow (1 - lo * lo) N))))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) _).
  destruct (mqd_witness_bounds N lo0 r Hlo0 Hr0 Hr1) as [W1 [W2 W3]].
  (* 收缩关键式：N·lo² < 1−r *)
  assert (Hshr : Qlt (mixe_qofnat N *
                       (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)))
                  (1 - r)).
  { apply (mqd_shrink_key N
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) r).
    - exact W1.
    - exact W3.
    - lra.
    - exact (Q.le_min_r (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)). }
  (* Bernoulli 装配：r < 1 − N·lo² ≤ (1−lo²)^N *)
  assert (Hx0 : Qle 0 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                            Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))).
  { exact (mixe_qmult_nonneg (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qlt_le_weak 0 _ W1) (Qlt_le_weak 0 _ W1)). }
  assert (Hx1 : Qle (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                      Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1).
  { apply (Qle_trans
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
              Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
             (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1).
    - apply (mixe_qle_eq_r
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) * 1)
               (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))).
      + exact (mixe_qmult_le_l
                 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N))
                 (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) 1
                 (Qlt_le_weak 0 _ W1) (Qlt_le_weak _ 1 W3)).
      + ring.
    - exact (Qlt_le_weak _ 1 W3). }
  pose proof (mqd_bernoulli_lower
                (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                 Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N
                Hx0 Hx1) as HB.
  assert (HK : Qlt r (mqd_pow
                (1 - Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N)).
  { apply (Qlt_le_trans r
             (1 - mixe_qofnat N *
                (Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                 Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)))
             (mqd_pow
                (1 - Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N) *
                        Qmin (lo0 * (1 # 2)%Q) ((1 - r) * mqd_invSN N)) N)).
    - lra.
    - exact HB. }
  split; [exact (Qlt_to_QltT 0 _ W1) | split].
  - exact (Qlt_to_QltT _ lo0 W2).
  - exact (Qlt_to_QltT r _ HK).
Defined.

(* ============================================================ *)
(* 证人注册面（G2/G5 口径：全件 Print Assumptions）                    *)
(* ============================================================ *)

Print Assumptions mqd_pow.
Print Assumptions mqd_invSN.
Print Assumptions mqd_znat_le_posS.
Print Assumptions mqd_invSN_pos.
Print Assumptions mqd_invSN_le1.
Print Assumptions mqd_kQ_inv_le.
Print Assumptions mqd_bernoulli_lower.
Print Assumptions mqd_bernoulli_lowerT.
Print Assumptions mqd_bern_complement.
Print Assumptions mqd_shrink_key.
Print Assumptions mqd_witness_bounds.
Print Assumptions mqd_q_doeblin_bound_unbounded.
