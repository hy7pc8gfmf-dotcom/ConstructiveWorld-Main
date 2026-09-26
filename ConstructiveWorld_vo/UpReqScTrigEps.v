(* ============================================================ *)
(* UpReqScTrigEps.v                                             *)
(*                                                             *)
(* 目的：S10_KVQuantTrig.v 的 sc_cos/sc_sin 族（全库最大重整化山，  *)
(*       GEO1 插值缝 #4，实测 124 处命中）的 eps-Bishop 补脸——     *)
(*       把「Or-le 精确形 + Id 恒等式在库、eps 形缺位」的首段       *)
(*       粗粒化收割为可消费的逐 eps 余量/Bishop 形。               *)
(*                                                             *)
(* 主件（全部纯构造性、Set 层语句、零新公理）：                     *)
(*   Part A（母件）：sce_real_le_eps_face——族母桥：                *)
(*       Or 编码 real_le ⟹ plain-eps 余量面                       *)
(*       (∀eps>0, real_le lhs (rhs+eps))；上游 real_le_to_le_b      *)
(*       （UpRealLeB Part A 单向桥）+ real_lt sigT 拆装，零稠密性。  *)
(*   Part B（G1 首段四件升格）：S10 Real 层四大主力夹逼              *)
(*       （real_sin_le_x / real_x_minus_cube_le_sin /              *)
(*       real_cos_le_one / real_one_minus_half_le_cos——            *)
(*       0 ≤ X ≤ 1 定义域照抄源件，零新增前提）的 eps 形四件          *)
(*       （sce_real_*_eps）与 Bishop 形四件（sce_real_*_B，          *)
(*       经 real_le_closure_b_one 特化完成器），全链                 *)
(*       Or ⟹ eps ⟹ ≤_B 三面同族可消费。                           *)
(*   Part C（G2 尾部余项 eps 件）：sc_cos/sc_sin 部分和截断尾的        *)
(*       构造性量化——Q 层尾界 sce_cos_partial_tail_le /             *)
(*       sce_sin_partial_tail_le（sc_cos/sc_sin_diff_bound2 于      *)
(*       B:=1 直连，尾形 T_n(q):=q^{S(2n)}/(S(2n))!·2）与 Real 层     *)
(*       Bishop 尾件 sce_cos_real_tail_B / sce_sin_real_tail_B：     *)
(*       |cauchy_real_cos(real_const q) − S_n(q)| ≤_B 3·T_n(q)      *)
(*       （real_lt 证书 δ:=T_n/2；q==0 支走 real_eq 精确闭合——       *)
(*       0<q 与 q==0 经 Qle_lt_or_eq 构造可分，无不可达精确形）。     *)
(*                                                             *)
(* 公理面：零新公理、零 承认、零经典；上游依赖 CW219（S01–S15       *)
(*       闭合）与 UpRealLeB（同零公理面）。文末主件                  *)
(*       Print Assumptions 全 Closed。                              *)
(* 红线：纯构造性 / Set 层语句（real_le_b 与 real_lt 皆 Set 值；      *)
(*       Qle 前提位沿 S10 族内先例）/ 非平凡真实现 / Obj.magic=0。   *)
(* 领地：新件零撞名（sce_ 前缀开工 grep 零撞）；S10 本体只读。        *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.

(* ============================================================ *)
(* Part A：母件——Or-le 形 ⟹ plain-eps 余量面（族母桥）              *)
(* ============================================================ *)

(* 母桥：Or 编码 real_le lhs rhs ⟹ ∀eps>0, real_le lhs (rhs+eps)。
   构造：real_le_to_le_b（UpRealLeB 单向桥）给 Bishop 面，拆
   real_lt 的 sigT 证书（δ>0 + 最终指数 N + 逐点间隔），以
   real_le = Or(lt,eq) 的 inl 支重组为 plain-eps 面。
   意义：Or 精确形的构造性多撞判定墙被单向平移消解——下游组装
   免分支（§9.4 可填充目标序）；逆向（eps⟹Or）不主张（构造性
   不可证，UpRealLeB 尾注结论 2 先例）。 *)
Lemma sce_real_le_eps_face : forall lhs rhs : Real,
  real_le lhs rhs ->
  forall eps : Real, real_lt real_zero eps ->
  real_le lhs (real_plus rhs eps).
Proof.
  intros lhs rhs Hle eps Heps.
  destruct (real_le_to_le_b lhs rhs Hle eps Heps) as [d [Hd [N HN]]].
  apply RealSetoid.real_lt_le_iff_req. apply inl.
  exists d. split.
  - exact Hd.
  - exists N. intros n Hn. exact (HN n Hn).
Qed.

(* ============================================================ *)
(* Part B：G1 首段四件——S10 Real 层主力夹逼的 eps/Bishop 升格       *)
(*   定义域与前提位照抄源件（0 ≤ X ≤ 1 双 real_le），零新增前提。     *)
(* ============================================================ *)

(* B.1 sin X ≤_eps X（源件 real_sin_le_x） *)
Lemma sce_real_sin_le_x_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_sin X) (real_plus X eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face (cauchy_real_sin X) X (real_sin_le_x X H0 H1)
           eps Heps).
Qed.

(* B.2 X − X³/6 ≤_eps sin X（源件 real_x_minus_cube_le_sin） *)
Lemma sce_real_x_minus_cube_le_sin_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                            (real_const (1 / 6)))))
          (real_plus (cauchy_real_sin X) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face
           (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                             (real_const (1 / 6)))))
           (cauchy_real_sin X)
           (real_x_minus_cube_le_sin X H0 H1) eps Heps).
Qed.

(* B.3 cos X ≤_eps 1（源件 real_cos_le_one） *)
Lemma sce_real_cos_le_one_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_cos X) (real_plus (real_const 1) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face (cauchy_real_cos X) (real_const 1)
           (real_cos_le_one X H0 H1) eps Heps).
Qed.

(* B.4 1 − X²/2 ≤_eps cos X（源件 real_one_minus_half_le_cos） *)
Lemma sce_real_one_minus_half_le_cos_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_plus (real_const 1)
                     (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
          (real_plus (cauchy_real_cos X) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face
           (real_plus (real_const 1)
                      (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
           (cauchy_real_cos X)
           (real_one_minus_half_le_cos X H0 H1) eps Heps).
Qed.

(* B.5 至 B.8：Bishop 完成四件（real_le_closure_b_one 特化完成器
   + B.1 至 B.4 直连；证书 D:=real_one、real_lt_zero_one 既有） *)
Lemma sce_real_sin_le_x_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (cauchy_real_sin X) X.
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_sin_le_x_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_x_minus_cube_le_sin_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                              (real_const (1 / 6)))))
            (cauchy_real_sin X).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_x_minus_cube_le_sin_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_cos_le_one_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (cauchy_real_cos X) (real_const 1).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_cos_le_one_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_one_minus_half_le_cos_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (real_plus (real_const 1)
                       (real_opp (real_mult (real_mult X X)
                                            (real_const (1 / 2)))))
            (cauchy_real_cos X).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_one_minus_half_le_cos_eps X H0 H1 eps Heps).
Qed.

(* ============================================================ *)
(* Part C：G2 尾部余项 eps 件——部分和截断尾的构造性量化              *)
(* ============================================================ *)

(* C.0 尾量：T_n(q) := q^{S(2n)}/(S(2n))!（首弃项绝对值；
   sc_sin/sc_cos_diff_bound2 的界指数同为 S(2n)，sin/cos 共用） *)
Definition sce_cos_tail (q : Q) (n : nat) : Q :=
  q_pow q (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n)).

(* C.0a 辅助：0 < 1/2（Q 字面量直算） *)
Lemma sce_half_pos : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. lia. Qed.

(* C.1 辅助：2 ≤ (t+1)#1（t ≥ 1；sc_*_diff_bound2 的 B:=1 几何前提） *)
Lemma sce_two_le_nat_q : forall t : nat, (1 <= t)%nat ->
  Qle (1 + 1)%Q (Z.of_nat (t + 1) # 1).
Proof.
  intros t Ht.
  assert (H1 : (1 + 1)%Q == 2) by reflexivity.
  rewrite H1.
  unfold Qle. simpl. lia.
Qed.

(* C.2 辅助：0 < q ⟹ 0 < q^k（q_pow 严格正；归纳 + Qmult_lt_compat_r） *)
Lemma sce_q_pow_pos : forall (q : Q) (k : nat), Qlt 0 q -> Qlt 0 (q_pow q k).
Proof.
  intros q k Hq. induction k as [| k IH].
  - simpl. unfold Qlt. simpl. lia.
  - rewrite q_pow_succ.
    assert (Hpre : Qlt (0 * q_pow q k) (q * q_pow q k))
      by (apply (Qmult_lt_compat_r 0 q (q_pow q k)); assumption).
    rewrite Qmult_0_l in Hpre. exact Hpre.
Qed.

(* C.3 辅助：0 < q ⟹ 0 < T_n(q)（q^…>0 × 1/(2n+2)!>0 乘法闭合） *)
Lemma sce_cos_tail_pos : forall (q : Q) (n : nat), Qlt 0 q ->
  Qlt 0 (sce_cos_tail q n).
Proof.
  intros q n Hq. unfold sce_cos_tail. unfold Qdiv.
  assert (Hinv : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * n)))))
    by (apply Qinv_lt_0_compat; apply q_fact_pos).
  assert (Hpre : Qlt (0 * Qinv (q_fact (Datatypes.S (2 * n))))
                     (q_pow q (Datatypes.S (2 * n))
                      * Qinv (q_fact (Datatypes.S (2 * n)))))
    by (apply (Qmult_lt_compat_r 0 (q_pow q (Datatypes.S (2 * n)))
                                  (Qinv (q_fact (Datatypes.S (2 * n)))));
        [exact Hinv | apply (sce_q_pow_pos q); exact Hq]).
  rewrite Qmult_0_l in Hpre. exact Hpre.
Qed.


(* C.3a 零点求值三件：q == 0 时的部分和与尾量（q_pow_wd 供形——
   q 位于 q_pow/cos_partial/sin_partial 等非态函数位，Qeq 重写不可达，
   统一以「wedge 供形 + 可计算求值」在引理内闭合） *)
Lemma sce_cos_tail_at_zero : forall (q : Q) (n : nat), q == 0 -> sce_cos_tail q n == 0.
Proof.
  intros q n Hz. unfold sce_cos_tail, Qdiv.
  assert (Hqp : q_pow q (Datatypes.S (2 * n)) == q_pow 0 (Datatypes.S (2 * n)))
    by exact (q_pow_wd q 0 (Datatypes.S (2 * n)) Hz).
  rewrite Hqp.
  assert (Hq0 : q_pow 0 (Datatypes.S (2 * n)) == 0) by reflexivity.
  rewrite Hq0. apply Qmult_0_l.
Qed.

Lemma sce_cos_partial_at_zero : forall (q : Q) (n : nat), q == 0 -> cos_partial n q == 1.
Proof.
  intros q n Hz. induction n as [| n IH].
  - reflexivity.
  - change (cos_partial (Datatypes.S n) q)
      with (cos_partial n q + cos_term (Datatypes.S n) q)%Q.
    rewrite IH.
    assert (Hterm : cos_term (Datatypes.S n) q == 0).
    { unfold cos_term, Qdiv.
      assert (Hqp : q_pow q (2 * Datatypes.S n) == q_pow 0 (2 * Datatypes.S n))
        by exact (q_pow_wd q 0 (2 * Datatypes.S n) Hz).
      rewrite Hqp.
      assert (Hq0 : q_pow 0 (2 * Datatypes.S n) == 0) by reflexivity.
      rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r. }
    rewrite Hterm. reflexivity.
Qed.

Lemma sce_sin_partial_at_zero : forall (q : Q) (n : nat), q == 0 -> sin_partial n q == 0.
Proof.
  intros q n Hz. induction n as [| n IH].
  - simpl. unfold sin_term, Qdiv.
    assert (Hqp : q_pow q 1 == q_pow 0 1) by exact (q_pow_wd q 0 1 Hz).
    rewrite Hqp.
    assert (Hq0 : q_pow 0 1 == 0) by reflexivity.
    rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r.
  - change (sin_partial (Datatypes.S n) q)
      with (sin_partial n q + sin_term (Datatypes.S n) q)%Q.
    rewrite IH.
    assert (Hterm : sin_term (Datatypes.S n) q == 0).
    { unfold sin_term, Qdiv.
      assert (Hqp : q_pow q (Datatypes.S (2 * Datatypes.S n)) == q_pow 0 (Datatypes.S (2 * Datatypes.S n)))
        by exact (q_pow_wd q 0 (Datatypes.S (2 * Datatypes.S n)) Hz).
      rewrite Hqp.
      assert (Hq0 : q_pow 0 (Datatypes.S (2 * Datatypes.S n)) == 0) by reflexivity.
      rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r. }
    rewrite Hterm. reflexivity.
Qed.

(* C.4 Q 层 cos 尾界：0 ≤ q ≤ 1、n ≤ k ⟹
      |cos_partial k q − cos_partial n q| ≤ 2·T_n(q)
      （sc_cos_diff_bound2 于 B:=q 直连；几何前提 2q ≤ 2 ≤ t+1
      由 q ≤ 1 与 t ≥ S(2n) ≥ 1 闭合） *)
Lemma sce_cos_partial_tail_le : forall (q : Q) (n k : nat),
  Qle 0 q -> Qle q 1 -> (n <= k)%nat ->
  Qle (Qabs (cos_partial k q - cos_partial n q))
      (sce_cos_tail q n * (1 + 1)%Q).
Proof.
  intros q n k Hq0 Hq1 Hnk.
  apply (sc_cos_diff_bound2 q q n k).
  - exact Hq0.
  - rewrite (Qabs_pos q Hq0). apply Qle_refl.
  - intros t Ht.
    assert (Hz : Qle 0 ((1 + 1)%Q)) by (unfold Qle; simpl; lia).
    apply (Qle_trans _ (q * (1 + 1))).
    + rewrite (Qmult_comm (1 + 1) q). apply Qle_refl.
    + apply (Qle_trans _ ((1 + 1) * 1)%Q).
      * assert (Hr : (1 + 1) * 1 == 1 * (1 + 1)) by ring.
        rewrite Hr.
        apply (Qmult_le_compat_r q 1 (1 + 1)).
        -- exact Hq1.
        -- exact Hz.
      * assert (Heq : (1 + 1) * 1 == 1 + 1) by ring.
        rewrite Heq. apply (sce_two_le_nat_q t). lia.
  - exact Hnk.
Qed.

(* C.5 Q 层 sin 尾界（sc_sin_diff_bound2 于 B:=1 直连；界指数与
   cos 同为 S(2n)，源件即此形） *)
Lemma sce_sin_partial_tail_le : forall (q : Q) (n k : nat),
  Qle 0 q -> Qle q 1 -> (n <= k)%nat ->
  Qle (Qabs (sin_partial k q - sin_partial n q))
      (sce_cos_tail q n * (1 + 1)%Q).
Proof.
  intros q n k Hq0 Hq1 Hnk.
  apply (sc_sin_diff_bound2 q q n k).
  - exact Hq0.
  - rewrite (Qabs_pos q Hq0). apply Qle_refl.
  - intros t Ht.
    assert (Hz : Qle 0 ((1 + 1)%Q)) by (unfold Qle; simpl; lia).
    apply (Qle_trans _ (q * (1 + 1))).
    + rewrite (Qmult_comm (1 + 1) q). apply Qle_refl.
    + apply (Qle_trans _ ((1 + 1) * 1)%Q).
      * assert (Hr : (1 + 1) * 1 == 1 * (1 + 1)) by ring.
        rewrite Hr.
        apply (Qmult_le_compat_r q 1 (1 + 1)).
        -- exact Hq1.
        -- exact Hz.
      * assert (Heq : (1 + 1) * 1 == 1 + 1) by ring.
        rewrite Heq. apply (sce_two_le_nat_q t). lia.
  - exact Hnk.
Qed.

(* C.6 核心算术：|diff| ≤ 2T、0 < T ⟹ T/2 < 3T − |diff|
   （Qlt 证书 = real_lt 的分离量 δ := T/2 的供给面） *)
Lemma sce_gap_arith : forall (T diff : Q),
  Qlt 0 T -> Qle (Qabs diff) (T * (1 + 1)%Q) ->
  Qlt (T * (1 # 2)) (3 * T - Qabs diff).
Proof.
  intros T diff HT Hb.
  assert (Hb2 : T * (1 + 1) == 2 * T) by ring.
  rewrite Hb2 in Hb.
  (* 半量正：T/2 > 0 *)
  assert (Hhalf : Qlt 0 (T * (1 # 2))).
  { assert (Hpre : Qlt (0 * (1 # 2)) (T * (1 # 2)))
      by (apply (Qmult_lt_compat_r 0 T (1 # 2));
          [exact sce_half_pos | exact HT]).
    rewrite Qmult_0_l in Hpre. exact Hpre. }
  (* T/2 < T：T/2 + 0 < T/2 + T/2 == T *)
  assert (Hsplit : T * (1 # 2) + T * (1 # 2) == T) by ring.
  assert (Hlt : Qlt (T * (1 # 2)) T).
  { assert (Hstep : T * (1 # 2) + 0 < T * (1 # 2) + T * (1 # 2))
      by exact (proj2 (Qplus_lt_r 0 (T * (1 # 2)) (T * (1 # 2))) Hhalf).
    rewrite Hsplit in Hstep. rewrite Qplus_0_r in Hstep. exact Hstep. }
  (* T ≤ 3T − |diff|：|diff| ≤ 2T ⟹ T + |diff| ≤ T + 2T == 3T，
     目标左端换形 T == (T + |diff|) − |diff| 后传递 *)
  assert (Hle2 : Qle (T + Qabs diff) (T + 2 * T))
    by exact (proj2 (Qplus_le_r (Qabs diff) (2 * T) T) Hb).
  assert (Hle3 : Qle (T + Qabs diff) (3 * T)).
  { assert (Heq : T + 2 * T == 3 * T) by ring.
    apply (Qle_trans _ (T + 2 * T)).
    - exact Hle2.
    - rewrite Heq. apply Qle_refl. }
  apply (Qlt_le_trans (T * (1 # 2)) T (3 * T - Qabs diff)).
  - exact Hlt.
  - assert (Hid : T == T + Qabs diff - Qabs diff) by ring.
    rewrite Hid at 1.
    exact (proj2 (Qplus_le_l (T + Qabs diff) (3 * T) (- Qabs diff)) Hle3).
Qed.

(* C.7 G2 旗舰：cos Real 尾件 Bishop 形——
   |cauchy_real_cos(real_const q) − S_n(q)| ≤_B 3·T_n(q)，q ∈ [0,1]。
   构造：q==0 支 real_eq 精确闭合（cos_partial k 0 == 1 恒等）；
   0<q 支 real_lt 证书 δ := T_n/2（C.6），最终指数 N := n，
   逐点界走 C.4；右端 +eps 经 real_lt_plus_r_zero 平移。 *)
Theorem sce_cos_real_tail_B : forall (q : Q) (n : nat),
  Qle 0 q -> Qle q 1 ->
  real_le_b (real_abs (real_plus (cauchy_real_cos (real_const q))
                                 (real_opp (real_const (cos_partial n q)))))
            (real_const (3 * sce_cos_tail q n)).
Proof.
  intros q n Hq0 Hq1. apply real_le_closure_b_one. intros eps Heps.
  destruct (Qlt_bool 0 q) eqn:Hb.
  - (* Qlt_bool 0 q = true ⟹ 0 < q：real_lt 证书 δ := T_n/2（inl 支） *)
    assert (Hpz : Qlt 0 q).
    { unfold Qlt_bool in Hb.
      destruct (Qcompare 0 q) eqn:E; try discriminate Hb.
      apply Qlt_alt. exact E. }
    assert (HT : Qlt 0 (sce_cos_tail q n)) by (apply sce_cos_tail_pos; exact Hpz).
    assert (Hhalf : Qlt 0 (sce_cos_tail q n * (1 # 2))).
    { assert (Hpre : Qlt (0 * (1 # 2)) (sce_cos_tail q n * (1 # 2)))
        by (apply (Qmult_lt_compat_r 0 (sce_cos_tail q n) (1 # 2));
            [exact sce_half_pos | exact HT]).
      rewrite Qmult_0_l in Hpre. exact Hpre. }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (real_lt_trans
             (real_abs (real_plus (cauchy_real_cos (real_const q))
                                  (real_opp (real_const (cos_partial n q)))))
             (real_const (3 * sce_cos_tail q n))
             (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + unfold real_lt.
      exists (sce_cos_tail q n * (1 # 2)). split.
      * apply Qlt_to_QltT. exact Hhalf.
      * exists n. intros k Hk.
        apply Qlt_to_QltT.
        rewrite real_const_proj.
        rewrite real_abs_proj. rewrite (real_plus_proj _ _ k).
        rewrite (real_opp_proj _ k).
        rewrite real_cos_proj. rewrite (real_const_proj q k).
        rewrite (real_const_proj (cos_partial n q) k).
        apply (sce_gap_arith (sce_cos_tail q n)
                             (cos_partial k q - cos_partial n q)).
        -- exact HT.
        -- apply (sce_cos_partial_tail_le q n k Hq0 Hq1).
           apply NatLe_drop. exact Hk.
    + apply real_lt_plus_r_zero. exact Heps.
  - (* Qlt_bool 0 q = false：¬(0<q) 配 0 ≤ q ⟹ q == 0；差投影恒 0，real_eq 精确闭合（inr 支） *)
    assert (Hz : q == 0).
    { destruct (Qle_lt_or_eq 0 q Hq0) as [Hlt0 | Hc].
      - exfalso.
        unfold Qlt_bool, Qcompare in Hb.
        rewrite (proj2 (Qlt_alt 0 q) Hlt0) in Hb.
        simpl in Hb. discriminate Hb.
      - exact (Qeq_sym 0 q Hc). }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (RealSetoid.real_lt_id_l
             (real_abs (real_plus (cauchy_real_cos (real_const q))
                                  (real_opp (real_const (cos_partial n q)))))
             real_zero (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + (* |差| == 0 == real_zero（q==0 恒等式闭合） *)
      apply real_eq_of_zero_diff. intro k.
      rewrite real_abs_proj. rewrite (real_plus_proj _ _ k). rewrite (real_opp_proj _ k).
      rewrite real_cos_proj. rewrite (real_const_proj q k).
      rewrite (real_const_proj (cos_partial n q) k).
      rewrite (sce_cos_partial_at_zero q k Hz).
      rewrite (sce_cos_partial_at_zero q n Hz).
      assert (Hrz : projT1 real_zero k == 0) by reflexivity.
      rewrite Hrz. simpl. reflexivity.
    + (* real_lt real_zero (real_const c + eps)：右端换形 + real_lt_plus_r_zero *)
      apply (RealSetoid.real_lt_id_r real_zero
               (real_plus real_zero eps)
               (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
      * apply (RealSetoid.real_eq_plus_compat real_zero eps
                 (real_const (3 * sce_cos_tail q n)) eps).
        -- apply real_eq_of_zero_diff. intro k.
           rewrite (real_const_proj (3 * sce_cos_tail q n) k).
           assert (Hrz : projT1 real_zero k == 0) by reflexivity.
           rewrite Hrz. rewrite (sce_cos_tail_at_zero q n Hz).
           reflexivity.
        -- apply real_eq_refl.
      * exact (real_lt_plus_r_zero real_zero eps Heps).
Qed.

(* C.8 G2 孪生：sin Real 尾件 Bishop 形（C.7 同型，源件换
   real_sin_proj / sc_sin_diff_bound2 / sc_sin_partial_zero） *)
Theorem sce_sin_real_tail_B : forall (q : Q) (n : nat),
  Qle 0 q -> Qle q 1 ->
  real_le_b (real_abs (real_plus (cauchy_real_sin (real_const q))
                                 (real_opp (real_const (sin_partial n q)))))
            (real_const (3 * sce_cos_tail q n)).
Proof.
  intros q n Hq0 Hq1. apply real_le_closure_b_one. intros eps Heps.
  destruct (Qlt_bool 0 q) eqn:Hb.
  - (* Qlt_bool 0 q = true ⟹ 0 < q：real_lt 证书 δ := T_n/2（inl 支） *)
    assert (Hpz : Qlt 0 q).
    { unfold Qlt_bool in Hb.
      destruct (Qcompare 0 q) eqn:E; try discriminate Hb.
      apply Qlt_alt. exact E. }
    assert (HT : Qlt 0 (sce_cos_tail q n)) by (apply sce_cos_tail_pos; exact Hpz).
    assert (Hhalf : Qlt 0 (sce_cos_tail q n * (1 # 2))).
    { assert (Hpre : Qlt (0 * (1 # 2)) (sce_cos_tail q n * (1 # 2)))
        by (apply (Qmult_lt_compat_r 0 (sce_cos_tail q n) (1 # 2));
            [exact sce_half_pos | exact HT]).
      rewrite Qmult_0_l in Hpre. exact Hpre. }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (real_lt_trans
             (real_abs (real_plus (cauchy_real_sin (real_const q))
                                  (real_opp (real_const (sin_partial n q)))))
             (real_const (3 * sce_cos_tail q n))
             (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + unfold real_lt.
      exists (sce_cos_tail q n * (1 # 2)). split.
      * apply Qlt_to_QltT. exact Hhalf.
      * exists n. intros k Hk.
        apply Qlt_to_QltT.
        rewrite real_const_proj.
        rewrite real_abs_proj. rewrite (real_plus_proj _ _ k).
        rewrite (real_opp_proj _ k).
        rewrite real_sin_proj. rewrite (real_const_proj q k).
        rewrite (real_const_proj (sin_partial n q) k).
        apply (sce_gap_arith (sce_cos_tail q n)
                             (sin_partial k q - sin_partial n q)).
        -- exact HT.
        -- apply (sce_sin_partial_tail_le q n k Hq0 Hq1).
           apply NatLe_drop. exact Hk.
    + apply real_lt_plus_r_zero. exact Heps.
  - (* Qlt_bool 0 q = false：¬(0<q) 配 0 ≤ q ⟹ q == 0；差投影恒 0，real_eq 精确闭合（inr 支） *)
    assert (Hz : q == 0).
    { destruct (Qle_lt_or_eq 0 q Hq0) as [Hlt0 | Hc].
      - exfalso.
        unfold Qlt_bool, Qcompare in Hb.
        rewrite (proj2 (Qlt_alt 0 q) Hlt0) in Hb.
        simpl in Hb. discriminate Hb.
      - exact (Qeq_sym 0 q Hc). }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (RealSetoid.real_lt_id_l
             (real_abs (real_plus (cauchy_real_sin (real_const q))
                                  (real_opp (real_const (sin_partial n q)))))
             real_zero (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + (* |差| == 0 == real_zero（q==0 恒等式闭合） *)
      apply real_eq_of_zero_diff. intro k.
      rewrite real_abs_proj. rewrite (real_plus_proj _ _ k). rewrite (real_opp_proj _ k).
      rewrite real_sin_proj. rewrite (real_const_proj q k).
      rewrite (real_const_proj (sin_partial n q) k).
      rewrite (sce_sin_partial_at_zero q k Hz).
      rewrite (sce_sin_partial_at_zero q n Hz).
      assert (Hrz : projT1 real_zero k == 0) by reflexivity.
      rewrite Hrz. simpl. reflexivity.
    + (* real_lt real_zero (real_const c + eps)：右端换形 + real_lt_plus_r_zero *)
      apply (RealSetoid.real_lt_id_r real_zero
               (real_plus real_zero eps)
               (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
      * apply (RealSetoid.real_eq_plus_compat real_zero eps
                 (real_const (3 * sce_cos_tail q n)) eps).
        -- apply real_eq_of_zero_diff. intro k.
           rewrite (real_const_proj (3 * sce_cos_tail q n) k).
           assert (Hrz : projT1 real_zero k == 0) by reflexivity.
           rewrite Hrz. rewrite (sce_cos_tail_at_zero q n Hz).
           reflexivity.
        -- apply real_eq_refl.
      * exact (real_lt_plus_r_zero real_zero eps Heps).
Qed.

(* ============================================================ *)
(* 公理面拍：主件 Print Assumptions（应全 Closed——零新公理）        *)
(* ============================================================ *)
Print Assumptions sce_real_le_eps_face.
Print Assumptions sce_real_sin_le_x_eps.
Print Assumptions sce_real_cos_le_one_eps.
Print Assumptions sce_real_x_minus_cube_le_sin_eps.
Print Assumptions sce_real_one_minus_half_le_cos_eps.
Print Assumptions sce_real_sin_le_x_B.
Print Assumptions sce_real_cos_le_one_B.
Print Assumptions sce_real_x_minus_cube_le_sin_B.
Print Assumptions sce_real_one_minus_half_le_cos_B.
Print Assumptions sce_cos_partial_tail_le.
Print Assumptions sce_sin_partial_tail_le.
Print Assumptions sce_cos_real_tail_B.
Print Assumptions sce_sin_real_tail_B.
