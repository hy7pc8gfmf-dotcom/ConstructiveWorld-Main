(* ============================================================
   DTPT_EntFam2.v — 多熵函数族缺席成员三件套（collide / maxfreq / H_min_q·H_max_q）
   职责：补多熵族缺席三成员的 Q 域有理代理面并证其序链——
         collide（Rényi 阶 2 碰撞熵内积面核 Σp_v²）、maxfreq（最大
         频率归一化，序链旗舰）、H_max_q = 1 − maxfreq、H_min_q = 1 −
         collide（任务书指定形）；Rényi 阶梯 1/n≤collide≤maxfreq≤1
         （非空 l，三成员一次入链）+ H_freq 相干桥 + 置换不变全套。
   依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、
         DTPT、DTPT_Entropy2。
   归并记录：无（原生成模块；席 DTPT-U9 新建件，禁碰既有件）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；Set 层零公理面、全程 Qed。
   附注：选形声明（详见 DTPT_EntFam2_升级报告_U9.md）——
         1. collide l = qn (sqsum l) / (qn n · qn n)，复用 S6 泛求和
            路线（sqsum 免 dedup、天然置换不变）；
         2. maxfreq l = qn (maxcount l) / qn n，空表取 0；
         3. 对照口径：−log max p 文献常记 H_min、−log Σp² 为 Rényi₂/
            碰撞熵；Q 域无 log，取「熵补 1−x」有理代理，与 −log x
            同为减函数 ⟹ 单调同向，序性质全部保真；命名遵任务书，
            语义以「补形单调同向代理」自洽；
         4. 旗舰序链 1/qn n <= collide l <= maxfreq l <= 1
            （Σp² >= 1/n 即 Cauchy-Schwarz 离散形；Σp² <= max p · Σ p
            经典不等式的 nat 层归纳实现，nat 侧收口后 Q 层除法桥接）；
         5. H_freq l == 1 − collide l（非空 l；S6 件直推——H_freq 即
            1 − collide 的别名面）。
         原典对照（数字全域—熵相三元论·基座）：L22 裁决表·熵行
         「采用多熵函数族 ℋ，不强行选单一熵」；L148-152 成员清单
         H_alg/H_Sh/H_vN/H_str + 可扩展 H_Rényi/H_min/H_max/H_top/
         H_cond；盘面在册状态（B1 定谳）：H_devsum（占位件）+
         H_cond + H_freq（S6，算半个 H_Rényi₂ 面）——九成员仅 2.5 个
         在册，本件补三成员。语义面：collide/maxfreq ∈ [1/n, 1]
         （非空）、空表取 0；H_max_q/H_min_q ∈ [0, 1]；全同值面
         maxfreq 取 1（熵补取 0）；置换不变全套。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Require DTPT.
Require DTPT_Entropy2.
Import DTPT.DTPT.
Import DTPT_Entropy2.DTPT_Entropy2.

Module DTPT_EntFam2.

(* ========== §1 Q 序/除法工具（stdlib 形变自建层） ========== *)

(* Qeq 可直接改写进 Qle 目标（S6 已实证） *)
Lemma qeq_le_l : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. rewrite H. apply Qle_refl.
Qed.

(* qn n >= 1（n >= 1；经 qadd_le，S6 qn_S_pos 同款配方） *)
Lemma qn_ge1 : forall n : nat, (1 <= n)%nat -> (1:Q) <= qn n.
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - simpl.
    pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1) (qn_nonneg k)) as HH.
    simpl in HH. exact HH.
Qed.

(* qn 乘积正性（nat 侧非负乘法 + qn 单调，绕开 stdlib 严格乘法名赌博） *)
Lemma qn_mul_pos : forall a b : nat, (0 < a)%nat -> (0 < b)%nat -> 0 < qn a * qn b.
Proof.
  intros a b Ha Hb.
  apply (Qlt_le_trans 0 (qn a) (qn a * qn b)).
  - apply qn_pos. exact Ha.
  - assert (Hab : (a <= a * b)%nat).
    { apply (Nat.le_trans a (a * 1) (a * b)).
      - lia.
      - apply Nat.mul_le_mono_l. lia. }
    rewrite <- (qn_mul a b). apply qn_le. exact Hab.
Qed.

(* 非空表长度正性（纯 nat 侧，simpl 只在 nat 目标上做——Q 目标 simpl
   会把 Qlt 展成 Qnum/Qden 编码形致 apply 失配） *)
Lemma qlen_pos : forall (x : Q) (l : list Q), (0 < length (x :: l))%nat.
Proof.
  intros x l. simpl. apply Nat.lt_0_succ.
Qed.

(* 非空表长度嵌入的乘积正性（序链 Q 侧统一入口） *)
Lemma qlen_mul_pos : forall (x : Q) (l : list Q),
  0 < qn (length (x :: l)) * qn (length (x :: l)).
Proof.
  intros x l. apply qn_mul_pos; apply qlen_pos.
Qed.

(* 同分母除法对分子单调（分母为正；Qmult_le_compat_r 带非负前提，
   逆元正性经 Qinv_lt_0_compat——本 9.0 stdlib 无 Qmult_le_compat_l） *)
Lemma qdiv_ge_num : forall A C B : Q, 0 < B -> C <= A -> C / B <= A / B.
Proof.
  intros A C B HB Hle. unfold Qdiv.
  apply Qmult_le_compat_r.
  - exact Hle.
  - apply (Qlt_le_weak 0 (/ B)). apply (Qinv_lt_0_compat B HB).
Qed.

(* 分子不超分母则商不超 1（Qmult_inv_r 是乘出 1 的特化形，S6 卡在案） *)
Lemma qdiv_le_1 : forall A B : Q, A <= B -> 0 < B -> A / B <= 1.
Proof.
  intros A B Hle HB. unfold Qdiv.
  assert (Hpos : 0 <= / B)
    by (apply (Qlt_le_weak 0 (/ B)); apply (Qinv_lt_0_compat B HB)).
  assert (Hm : A * / B <= B * / B) by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (A * / B) (B * / B) 1 Hm).
  apply qeq_le_l. apply Qmult_inv_r. exact (qpos_neq0 B HB).
Qed.

(* 归一化：1/P == P/(P·P)（field 除法侧条件为 Qeq 形，由上下文假设放电） *)
Lemma qdiv_norm : forall P : Q, ~ (P == 0) -> ~ (P * P == 0) -> 1 / P == P / (P * P).
Proof.
  intros P HP1 HP2. field; assumption.
Qed.

(* 减法保序反变（z 固定；Qminus 先展开再 qadd_le，避开 apply 单化病） *)
Lemma qsub_le : forall x y z : Q, x <= y -> z - y <= z - x.
Proof.
  intros x y z H. unfold Qminus.
  apply (qadd_le z z (- y) (- x)).
  - apply Qle_refl.
  - exact (Qopp_le_compat x y H).
Qed.

(* ========== §2 nmax：Q 索引 nat 泛取大（与 S6 nsum 同构） ========== *)

Fixpoint nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (nmax f ys)
  end.

Lemma nmax_bound : forall (f : Q -> nat) (l : list Q) (y : Q),
  In y l -> (f y <= nmax f l)%nat.
Proof.
  intros f l. induction l as [| z zs IH]; simpl; intros y Hy.
  - destruct Hy.
  - destruct Hy as [Hz | Hy].
    + subst z. apply Nat.le_max_l.
    + apply (Nat.le_trans (f y) (nmax f zs) (Nat.max (f z) (nmax f zs))).
      * apply IH. exact Hy.
      * apply Nat.le_max_r.
Qed.

Lemma nmax_le_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> (nmax f l <= B)%nat.
Proof.
  intros f l B. induction l as [| z zs IH]; simpl; intros H.
  - lia.
  - assert (Hz : (f z <= B)%nat) by (apply H; left; reflexivity).
    assert (Hzs : (nmax f zs <= B)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

Lemma nmax_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> nmax f l = nmax g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* 泛取大置换不变（perm_swap 分支 lia 收 Nat.max 交换） *)
Lemma nmax_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> nmax f l = nmax f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* ========== §3 频数补充件（保底件 nat 侧承重） ========== *)

(* 成员频率至少 1（Qeq_bool 假分支经 S6 qeqb_false_neq 矛盾收口） *)
Lemma freq_q_ge1 : forall (x : Q) (l : list Q), In x l -> (1 <= freq_q x l)%nat.
Proof.
  intros x l. induction l as [| y ys IH]; intros Hin; simpl.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst y. destruct (Qeq_bool x x) eqn:Exx.
      * lia.
      * exfalso. apply (qeqb_false_neq x x Exx). reflexivity.
    + destruct (Qeq_bool x y) eqn:Exy.
      * lia.
      * apply IH. exact Hin.
Qed.

(* 泛求和下界（nsum_bound 的对偶） *)
Lemma nsum_ge_const : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (B <= f x)%nat) -> (length l * B <= nsum f l)%nat.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H.
  - lia.
  - assert (Hy : (B <= f y)%nat) by (apply H; left; reflexivity).
    assert (Hys : (length ys * B <= nsum f ys)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* 保底件 nat 侧核心：sqsum >= length（逐点 freq >= 1，Cauchy-Schwarz 下界入口） *)
Lemma sqsum_ge_length : forall l : list Q, (length l <= sqsum l)%nat.
Proof.
  intros l. unfold sqsum.
  pose proof (nsum_ge_const (fun x => freq_q x l) l 1
                (fun x Hx => freq_q_ge1 x l Hx)) as Hge.
  rewrite Nat.mul_1_r in Hge. exact Hge.
Qed.

(* ========== §4 collide：Rényi₂/碰撞熵核 Σp² 与界定理（保底件） ========== *)

(* collide l = Σ_{x∈l} (freq_q x l / n)² = qn (sqsum l) / (qn n · qn n) *)
Definition collide (l : list Q) : Q :=
  qn (sqsum l) / (qn (length l) * qn (length l)).

Lemma collide_zero : collide [] == 0.
Proof.
  unfold collide. apply qdiv_zero_num. reflexivity.
Qed.

(* 上界：collide <= 1（全表；sqsum <= n² 经 S6 sqsum_le） *)
Theorem collide_upper : forall l : list Q, collide l <= 1.
Proof.
  intros l. destruct l as [| x xs].
  - rewrite collide_zero. apply (Qlt_le_weak 0 1). reflexivity.
  - unfold collide. apply qdiv_le_1.
    + assert (Hle : qn (sqsum (x :: xs))
                    <= qn (length (x :: xs)) * qn (length (x :: xs))).
      { rewrite <- (qn_mul (length (x :: xs)) (length (x :: xs))).
        apply qn_le. apply sqsum_le. }
      exact Hle.
    + apply qlen_mul_pos.
Qed.

(* 下界：1/n <= collide（非空；1/n == n/n² 经 qdiv_norm，分子经 sqsum_ge_length） *)
Theorem collide_lower : forall l : list Q,
  (0 < length l)%nat -> 1 / qn (length l) <= collide l.
Proof.
  intros l Hl. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold collide.
    pose proof (qlen_mul_pos x xs) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { apply qpos_neq0. apply qn_pos. apply qlen_pos. }
    assert (Hge : (length (x :: xs) <= sqsum (x :: xs))%nat)
      by apply sqsum_ge_length.
    assert (Hnum : qn (length (x :: xs)) <= qn (sqsum (x :: xs)))
      by (apply qn_le; exact Hge).
    rewrite (qdiv_norm (qn (length (x :: xs))) HP1 HP2).
    apply qdiv_ge_num.
    + exact HPP.
    + exact Hnum.
Qed.

(* 置换不变（sqsum_perm + Permutation_length 两步，S6 同款） *)
Theorem collide_perm : forall l p : list Q,
  Permutation l p -> collide l == collide p.
Proof.
  intros l p H. unfold collide.
  rewrite (sqsum_perm l p H). rewrite (Permutation_length H). reflexivity.
Qed.

(* ========== §5 maxfreq：最大频率归一化与序链闭环（旗舰） ========== *)

Definition maxcount (l : list Q) : nat := nmax (fun x => freq_q x l) l.

Definition maxfreq (l : list Q) : Q := qn (maxcount l) / qn (length l).

(* 【旗舰序链】collide <= maxfreq：
   nat 侧 sqsum <= n · maxcount（S6 nsum_bound + nmax_bound 逐点），
   Q 侧同分母单调 + 场内归一（field 侧条件由上下文放电） *)
Theorem collide_le_maxfreq : forall l : list Q, collide l <= maxfreq l.
Proof.
  intros l. destruct l as [| x xs].
  - rewrite collide_zero.
    assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qdiv_zero_num; reflexivity).
    rewrite Hz. apply Qle_refl.
  - unfold collide, maxfreq.
    pose proof (qlen_mul_pos x xs) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { apply qpos_neq0. apply qn_pos. apply qlen_pos. }
    assert (Hnat : (sqsum (x :: xs)
                    <= length (x :: xs) * maxcount (x :: xs))%nat).
    { unfold sqsum, maxcount. apply nsum_bound.
      intros x0 Hx0.
      exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x0 Hx0). }
    assert (HQ : qn (sqsum (x :: xs))
                 <= qn (length (x :: xs)) * qn (maxcount (x :: xs))).
    { rewrite <- (qn_mul (length (x :: xs)) (maxcount (x :: xs))).
      apply qn_le. exact Hnat. }
    assert (HA : qn (sqsum (x :: xs)) / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 <= (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                    / (qn (length (x :: xs)) * qn (length (x :: xs)))).
    { apply qdiv_ge_num.
      - exact HPP.
      - exact HQ. }
    assert (HB : (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                 / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 == qn (maxcount (x :: xs)) / qn (length (x :: xs))).
    { field; assumption. }
    apply (Qle_trans _ _ _ HA (qeq_le_l _ _ HB)).
Qed.

(* 下界：1/n <= maxfreq（非空；maxcount >= 1 经逐点成员频率 >= 1） *)
Theorem maxfreq_lower : forall l : list Q,
  (0 < length l)%nat -> 1 / qn (length l) <= maxfreq l.
Proof.
  intros l Hl. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hge : (1 <= maxcount (x :: xs))%nat).
    { pose proof (freq_q_ge1 x (x :: xs) (or_introl eq_refl)) as H1.
      assert (Hb : (freq_q x (x :: xs) <= maxcount (x :: xs))%nat).
      { unfold maxcount.
        exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                 (or_introl eq_refl)). }
      lia. }
    apply qdiv_ge_num.
    + apply qn_pos. apply qlen_pos.
    + assert (Hq1 : qn 1 == (1:Q)) by reflexivity.
      rewrite <- Hq1. apply qn_le. exact Hge.
Qed.

(* 上界：maxfreq <= 1（全表；maxcount <= length 经 nmax_le_bound 逐点） *)
Theorem maxfreq_upper : forall l : list Q, maxfreq l <= 1.
Proof.
  intros l. destruct l as [| x xs].
  - assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qdiv_zero_num; reflexivity).
    rewrite Hz. apply (Qlt_le_weak 0 1). reflexivity.
  - unfold maxfreq. apply qdiv_le_1.
    + apply qn_le. unfold maxcount. apply nmax_le_bound.
      intros y Hy. apply freq_q_le_length.
    + apply qn_pos. apply qlen_pos.
Qed.

(* 简并面：全同值 ⟹ maxfreq 取 1（maxcount == length 双向夹） *)
Theorem maxfreq_all_same_one : forall l : list Q,
  all_same l -> (0 < length l)%nat -> maxfreq l == 1.
Proof.
  intros l Hs Hl. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hmc : (maxcount (x :: xs) = length (x :: xs))%nat).
    { unfold maxcount. apply Nat.le_antisymm.
      - apply nmax_le_bound. intros y Hy. apply freq_q_le_length.
      - apply (Nat.le_trans (length (x :: xs)) (freq_q x (x :: xs))
                 (nmax (fun x0 => freq_q x0 (x :: xs)) (x :: xs))).
        + rewrite <- (freq_q_eq_all x (x :: xs)
                        (fun z Hz => Hs z x Hz (or_introl eq_refl))).
          apply Nat.le_refl.
        + exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                   (or_introl eq_refl)). }
    rewrite Hmc.
    assert (HPne : ~ (qn (length (x :: xs)) == 0)).
    { apply qpos_neq0. apply qn_pos. apply qlen_pos. }
    field; assumption.
Qed.

(* maxcount 置换不变（nmax_ext_in 点点相等桥 + nmax_perm，sqsum_perm 同款） *)
Theorem maxcount_perm : forall l p : list Q,
  Permutation l p -> maxcount l = maxcount p.
Proof.
  intros l p H. unfold maxcount.
  rewrite (nmax_ext_in (fun x => freq_q x l) (fun x => freq_q x p) l
             (fun x _ => freq_q_perm x l p H)).
  exact (nmax_perm (fun x => freq_q x p) l p H).
Qed.

(* maxfreq 置换不变 *)
Theorem maxfreq_perm : forall l p : list Q,
  Permutation l p -> maxfreq l == maxfreq p.
Proof.
  intros l p H. unfold maxfreq.
  rewrite (maxcount_perm l p H). rewrite (Permutation_length H). reflexivity.
Qed.

(* 【序链合读】非空 l：1/n <= collide <= maxfreq <= 1 三成员一次入链 *)
Theorem H_chain : forall l : list Q, (0 < length l)%nat ->
  1 / qn (length l) <= collide l /\ collide l <= maxfreq l /\ maxfreq l <= 1.
Proof.
  intros l Hl. split.
  - apply collide_lower. exact Hl.
  - split.
    + apply collide_le_maxfreq.
    + apply maxfreq_upper.
Qed.

(* ========== §6 H_max_q / H_min_q：多熵族补形有理代理面（主件） ========== *)

Definition H_max_q (l : list Q) : Q := 1 - maxfreq l.

Definition H_min_q (l : list Q) : Q := 1 - collide l.

(* 单调面：maxfreq 越大 H_max_q 越小（经 qsub_le 反变桥） *)
Theorem H_max_q_anti : forall l p : list Q,
  maxfreq l <= maxfreq p -> H_max_q p <= H_max_q l.
Proof.
  intros l p H. unfold H_max_q. apply qsub_le. exact H.
Qed.

Theorem H_max_q_nonneg : forall l : list Q, 0 <= H_max_q l.
Proof.
  intros l. unfold H_max_q.
  apply (proj1 (Qle_0_sub' (maxfreq l) 1)). apply maxfreq_upper.
Qed.

Theorem H_max_q_le_one : forall l : list Q, H_max_q l <= 1.
Proof.
  intros l. unfold H_max_q.
  assert (H0 : 0 <= maxfreq l).
  { destruct l as [| x xs].
    - assert (Hz : maxfreq [] == 0)
        by (unfold maxfreq; apply qdiv_zero_num; reflexivity).
      rewrite Hz. apply Qle_refl.
    - unfold maxfreq. apply qdiv_nonneg.
      + apply qn_nonneg.
      + apply qn_pos. apply qlen_pos. }
  apply (Qle_trans (1 - maxfreq l) (1 - 0) 1).
  - apply qsub_le. exact H0.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* 与下界的耦合：H_max_q l <= 1 - 1/n（非空） *)
Theorem H_max_q_le_inv : forall l : list Q, (0 < length l)%nat ->
  H_max_q l <= 1 - 1 / qn (length l).
Proof.
  intros l Hl. unfold H_max_q. apply qsub_le. apply maxfreq_lower. exact Hl.
Qed.

Theorem H_min_q_nonneg : forall l : list Q, 0 <= H_min_q l.
Proof.
  intros l. unfold H_min_q.
  apply (proj1 (Qle_0_sub' (collide l) 1)). apply collide_upper.
Qed.

Theorem H_min_q_le_one : forall l : list Q, H_min_q l <= 1.
Proof.
  intros l. unfold H_min_q.
  assert (Hc : 0 <= collide l).
  { destruct l as [| x xs].
    - rewrite collide_zero. apply Qle_refl.
    - unfold collide. apply qdiv_nonneg.
      + apply qn_nonneg.
      + apply qlen_mul_pos. }
  apply (Qle_trans (1 - collide l) (1 - 0) 1).
  - apply qsub_le. exact Hc.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* 熵族内部相干桥：H_freq == 1 − collide（非空；S6 件定义直推，field 收口） *)
Theorem H_freq_eq_bridge : forall l : list Q,
  (0 < length l)%nat -> H_freq l == H_min_q l.
Proof.
  intros l Hl. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold H_freq, H_min_q, collide.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { apply qpos_neq0. apply qn_pos. apply qlen_pos. }
    pose proof (qlen_mul_pos x xs) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    field; assumption.
Qed.

(* 简并面：全同值 ⟹ H_max_q 取 0（与 S6 H_freq_all_same_zero 对偶） *)
Theorem H_max_q_all_same_zero : forall l : list Q,
  all_same l -> (0 < length l)%nat -> H_max_q l == 0.
Proof.
  intros l Hs Hl. unfold H_max_q.
  assert (H1 : maxfreq l == 1) by (apply maxfreq_all_same_one; assumption).
  rewrite H1. reflexivity.
Qed.

(* ========== §7 置换不变收尾（加分项） ========== *)

Theorem H_min_q_perm : forall l p : list Q,
  Permutation l p -> H_min_q l == H_min_q p.
Proof.
  intros l p H. unfold H_min_q. rewrite (collide_perm l p H). reflexivity.
Qed.

Theorem H_max_q_perm : forall l p : list Q,
  Permutation l p -> H_max_q l == H_max_q p.
Proof.
  intros l p H. unfold H_max_q. rewrite (maxfreq_perm l p H). reflexivity.
Qed.

End DTPT_EntFam2.
Import DTPT_EntFam2.

(* ========== 审计：零公理面实证 ========== *)

Print Assumptions collide_lower.
Print Assumptions collide_upper.
Print Assumptions collide_le_maxfreq.
Print Assumptions maxfreq_lower.
Print Assumptions maxfreq_upper.
Print Assumptions H_freq_eq_bridge.
Print Assumptions H_max_q_anti.
Print Assumptions H_chain.
Print Assumptions maxfreq_perm.
Print Assumptions collide_perm.
Print Assumptions H_max_q_perm.
Print Assumptions H_min_q_perm.
