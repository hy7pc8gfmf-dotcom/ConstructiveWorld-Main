(* ============================================================
   DTPT_Entropy2.v — 真频率香农熵、置换不变定理族与数据处理不等式
                     （M3 归并版）
   ------------------------------------------------------------
   【职责】
   · 真频率香农熵（Q 域有理替代形）自包含定义面：qn（nat→Q 嵌入）、
     freq_q（Qeq_bool 判等频数）、nsum（泛求和）、sqsum（免 dedup
     碰撞和）、H_freq = 1 − Σ_v p_v² 及其定理族（置换不变
     H_freq_perm / 非负 / 简并双向刻画）。背景：旧 H_devsum 实为
     质心偏移和、置换不变性为假（反例见 DTPT_Entropy.v），本件为
     其诚实替代——H_freq ∈ [0,1)，全同值/length≤1 取 0。
   · 数据处理不等式族（M3 并入段 §7-§12）：粗粒化观测 map f 不增熵
     ——计数形 freq_q_map、逐点支配 freq_q_map_ge（Qeq 形态假设
     进场）、碰撞和单调 sqsum_map_ge、补形反号 hfreq_core_anti、
     旗舰 H_freq_dpi、端点双例与迭代不衰减链。
   【依赖】stdlib（QArith / Qabs / List / Arith / Lia / Permutation）
     + 底座 DTPT（qopp_le / Qeq 环境等）。无其它外部依赖。
   【归并记录】M3（2026-09-14）：U17 席「H_freq 数据处理不等式」件
     整体并入本文件尾（其对本文件的 Require 行随之删除，变同文件
     直引，对 DTPT 的 Require 保留）；撞名预检 15 个并入顶层名
     全 0 撞（dpi_ 系命名天然区分，未加前缀）；全工作区无下游
     Require 该退役件，源已删、.retired_M3 快照留存；拓扑无新增
     依赖。
   【认证】文尾审计 15 件 Print Assumptions 全 "Closed under the
     global context"（零公理）；.vo 于 M3 归并后重编全绿。
   【纪律】Set 层零公理、零承认、零中途放弃，全程 Qed 收口；
     nat 全显式 %nat；仅 Require DTPT 与 stdlib，禁 Require 在飞件。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Require DTPT.
Import DTPT.DTPT.

Module DTPT_Entropy2.

(* ========== §1 qn：nat → Q 嵌入（自包含，免 Z.of_nat 依赖面） ========== *)

Fixpoint qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + qn k)%Q
  end.

Lemma qn_nonneg : forall n : nat, 0 <= qn n.
Proof.
  induction n as [| k IH].
  - apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + exact IH.
Qed.

Lemma qn_S_pos : forall k : nat, 0 < qn (S k).
Proof.
  intros k. simpl. apply (Qlt_le_trans 0 1 (1 + qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1) (qn_nonneg k)) as HH.
    simpl in HH. exact HH.
Qed.

Lemma qn_pos : forall n : nat, (0 < n)%nat -> 0 < qn n.
Proof.
  intros n Hn. destruct n as [| m].
  - exfalso. lia.
  - apply qn_S_pos.
Qed.

Lemma qn_add : forall a b : nat, qn (a + b)%nat == qn a + qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. rewrite Qplus_0_l. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma qn_mul : forall a b : nat, qn (a * b)%nat == qn a * qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite qn_add. rewrite IH. ring.
Qed.

Lemma qn_le : forall a b : nat, (a <= b)%nat -> qn a <= qn b.
Proof.
  induction a as [| a IH]; intros b Hle.
  - apply qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply (qadd_le 1 1 (qn a) (qn b')).
      * apply Qle_refl.
      * apply IH. apply (le_S_n _ _ Hle).
Qed.

Lemma qn_inj : forall a b : nat, qn a == qn b -> a = b.
Proof.
  induction a as [| a IH]; intros b Heq.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (qn_S_pos b') as HP. simpl in HP.
      rewrite <- Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (qn_S_pos a) as HP. simpl in HP.
      rewrite Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (qn a)) in Heq.
      rewrite (Qplus_comm 1 (qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (qn a) (qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. rewrite Hab. reflexivity.
Qed.

(* ========== §2 Q 除法/减号工具（Qminus 先展开再 ring；零除法前提漏洞） ========== *)

Lemma qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

Lemma qpos_neq0 : forall y : Q, 0 < y -> ~ (y == 0).
Proof.
  intros y Hpy Heq. apply (Qlt_not_eq 0 y Hpy). apply (Qeq_sym y 0).
  exact Heq.
Qed.

(* 本平台 9.0 stdlib 的 Qmult_inv_r 是 x * /x == 1 形而非消去形，
   自建消去引理（field 的除法侧条件恰为 Qeq 形 ~ (B == 0)） *)
Lemma qmult_inv_cancel_r : forall A B : Q, ~ (B == 0) -> A * / B * B == A.
Proof.
  intros A B HB. field. exact HB.
Qed.

Lemma qsub_eq0 : forall a b : Q, a - b == 0 -> a == b.
Proof.
  intros a b H.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* 分子为零（含零分母的平凡情形）则商为零：0/0 == 0 亦被覆盖 *)
Lemma qdiv_zero_num : forall A B : Q, A == 0 -> A / B == 0.
Proof.
  intros A B H. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

Lemma qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> A == 0.
Proof.
  intros A B HB H. unfold Qdiv in H.
  pose proof (qmult_inv_cancel_r A B (qpos_neq0 B HB)) as Hcancel.
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

Lemma qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> 0 <= A / B.
Proof.
  intros A B HA HB. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

Lemma qnum_zero : forall n s : nat, qn (n * n) == qn s -> qn n * qn n - qn s == 0.
Proof.
  intros n s H. rewrite <- (qn_mul n n). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

Lemma qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* ========== §3 freq_q：自包含频数计数（Qeq_bool 判等） ========== *)

Fixpoint freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (freq_q x ys) else freq_q x ys
  end.

Lemma freq_q_le_length : forall (x : Q) (l : list Q),
  (freq_q x l <= length l)%nat.
Proof.
  intros x. induction l as [| y ys IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

(* 保底件：拼接频数可加 *)
Theorem freq_q_app : forall (x : Q) (l p : list Q),
  freq_q x (l ++ p) = (freq_q x l + freq_q x p)%nat.
Proof.
  intros x l p. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* 旗舰前置：频数置换不变（对 Permutation 构造子归纳；perm_swap
   分支因计数同一 x0 而只需四分支字面重排，无需 Qeq_bool 对称性） *)
Theorem freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> freq_q x l = freq_q x p.
Proof.
  intros x l p H.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

Lemma freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> freq_q x l = length l.
Proof.
  intros x l. induction l as [| y ys IH]; intros H.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal. apply IH. intros z Hz. apply H.
    right. exact Hz.
Qed.

Lemma freq_q_full_count : forall (x : Q) (l : list Q),
  freq_q x l = length l -> forall y, In y l -> y == x.
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (freq_q_le_length x l) as HL. lia.
    + apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (freq_q_le_length x l) as HL. lia.
      * exact Hy0.
Qed.

(* ========== §4 nsum：Q 索引 nat 泛求和 ========== *)

Fixpoint nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + nsum f ys)%nat
  end.

Lemma nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> nsum f l = nsum g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

Lemma nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> nsum f l = nsum f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

Lemma nsum_const : forall (n : nat) (l : list Q),
  nsum (fun _ => n) l = (length l * n)%nat.
Proof.
  intros n l. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> (nsum f l <= length l * B)%nat.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : (nsum f ys <= length ys * B)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

Lemma nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  nsum f l = (length l * B)%nat ->
  forall x, In x l -> f x = B.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : (nsum f ys <= length ys * B)%nat)
      by (apply (nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    assert (Hfy : f y = B) by lia.
    assert (HysEq : nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + apply IH.
      * intros z Hz. apply Hsat. right. exact Hz.
      * exact HysEq.
      * exact Hx0.
Qed.

(* ========== §5 sqsum：Σ_{x∈l} freq_q x l = Σ_v c_v²（免 dedup） ========== *)

Definition sqsum (l : list Q) : nat := nsum (fun x => freq_q x l) l.

Definition all_same (l : list Q) : Prop :=
  forall a b, In a l -> In b l -> a == b.

Theorem sqsum_perm : forall l p : list Q,
  Permutation l p -> sqsum l = sqsum p.
Proof.
  intros l p H. unfold sqsum.
  rewrite (nsum_ext_in (fun x => freq_q x l) (fun x => freq_q x p) l
             (fun x _ => freq_q_perm x l p H)).
  exact (nsum_perm (fun x => freq_q x p) l p H).
Qed.

Lemma sqsum_le : forall l : list Q, (sqsum l <= length l * length l)%nat.
Proof.
  intros l. unfold sqsum.
  apply (nsum_bound (fun x => freq_q x l) l (length l)).
  intros x _. apply freq_q_le_length.
Qed.

Lemma freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> all_same l -> freq_q x l = length l.
Proof.
  intros x l Hin Hs. apply freq_q_eq_all. intros z Hz. apply Hs.
  - exact Hz.
  - exact Hin.
Qed.

Lemma sqsum_all_same : forall l : list Q,
  all_same l -> sqsum l = (length l * length l)%nat.
Proof.
  intros l Hs. unfold sqsum.
  rewrite (nsum_ext_in (fun x => freq_q x l) (fun _ : Q => length l) l
             (fun x Hx => freq_q_all_same x l Hx Hs)).
  apply nsum_const.
Qed.

Lemma sqsum_eq_all_same : forall l : list Q,
  sqsum l = (length l * length l)%nat -> all_same l.
Proof.
  intros l Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - unfold sqsum in Heq.
    pose proof (nsum_bound_eq (fun x0 => freq_q x0 (x :: xs)) (x :: xs)
                  (length (x :: xs))
                  (fun x0 _ => freq_q_le_length x0 (x :: xs))
                  Heq x (or_introl eq_refl)) as Hfx.
    pose proof (freq_q_full_count x (x :: xs) Hfx) as Hall.
    intros a b Ha Hb. apply (Qeq_trans a x b).
    + apply Hall. exact Ha.
    + apply (Qeq_sym b x). apply Hall. exact Hb.
Qed.

(* ========== §6 H_freq：真频率香农熵的有理替代形与旗舰定理 ========== *)

(* H_freq l = 1 − Σ_v p_v² = (n² − Σ_v c_v²)/n²（Q 域；n=0 时取 0） *)
Definition H_freq (l : list Q) : Q :=
  (qn (length l) * qn (length l) - qn (sqsum l))
    / (qn (length l) * qn (length l)).

(* 【旗舰】置换不变——旧 H_devsum 因质心偏移形而造不出的定理 *)
Theorem H_freq_perm : forall l p : list Q,
  Permutation l p -> H_freq l == H_freq p.
Proof.
  intros l p Hp. unfold H_freq.
  rewrite (sqsum_perm l p Hp).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* 非负（按所选形：n² ≥ Σc_v² 且除正保号；空表分子分母同零取 0） *)
Theorem H_freq_nonneg : forall l : list Q, 0 <= H_freq l.
Proof.
  intros l. destruct l as [| x xs].
  - assert (Hz : H_freq [] == 0).
    { unfold H_freq. apply qdiv_zero_num. apply qnum_zero. reflexivity. }
    rewrite Hz. apply Qle_refl.
  - unfold H_freq. apply qdiv_nonneg.
    + apply (proj1 (Qle_0_sub' (qn (sqsum (x :: xs)))
                 (qn (length (x :: xs)) * qn (length (x :: xs))))).
      rewrite <- (qn_mul (length (x :: xs)) (length (x :: xs))).
      apply qn_le. apply sqsum_le.
    + rewrite <- (qn_mul (length (x :: xs)) (length (x :: xs))).
      apply qn_pos. simpl. apply Nat.lt_0_succ.
Qed.

(* 简并刻画（正向）：全同值面 ⟹ H_freq 取 0 *)
Theorem H_freq_all_same_zero : forall l : list Q,
  all_same l -> H_freq l == 0.
Proof.
  intros l Hs. unfold H_freq. apply qdiv_zero_num. apply qnum_zero.
  rewrite (sqsum_all_same l Hs). reflexivity.
Qed.

Theorem H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> H_freq l == 0.
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply H_freq_all_same_zero. intros a b Ha Hb. destruct Ha.
  - simpl in Hl. destruct xs as [| y ys].
    + apply H_freq_all_same_zero. intros a b Ha Hb.
      destruct Ha as [Ha | Ha].
      * subst a. destruct Hb as [Hb | Hb].
        -- subst b. apply Qeq_refl.
        -- destruct Hb.
      * destruct Ha.
    + simpl in Hl. exfalso. lia.
Qed.

(* 简并刻画（反向）：H_freq 取 0 ⟹ 全同值面（双向闭合） *)
Theorem H_freq_eq0_all_same : forall l : list Q,
  H_freq l == 0 -> all_same l.
Proof.
  intros l Heq. unfold H_freq in Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - assert (HB : 0 < qn (length (x :: xs)) * qn (length (x :: xs))).
    { rewrite <- (qn_mul (length (x :: xs)) (length (x :: xs))).
      apply qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : qn (length (x :: xs)) * qn (length (x :: xs))
                   - qn (sqsum (x :: xs)) == 0)
      by (apply (qdiv_eq0_num _ _ HB Heq)).
    pose proof (qsub_eq0 (qn (length (x :: xs)) * qn (length (x :: xs)))
                  (qn (sqsum (x :: xs))) Hnum) as Hab.
    rewrite <- (qn_mul (length (x :: xs)) (length (x :: xs))) in Hab.
    pose proof (qn_inj (length (x :: xs) * length (x :: xs))
                  (sqsum (x :: xs)) Hab) as Heqnat.
    apply sqsum_eq_all_same. symmetry. exact Heqnat.
Qed.

(* ############################################################
   M3 归并段【U17 件 · H_freq 数据处理不等式族】（§7-§12）
   原独立文件整体并入：内容零改动，仅删其 Require 行（变同文件
   直引）、节号顺延 §7-§12、审计并档文尾。
   ############################################################ *)

(* ========== §7 列表/求和搬运工具 ========== *)

(* map 保长（stdlib 9.0 length_map 改名风险规避，自建） *)
Lemma length_map_self : forall (f : Q -> Q) (l : list Q),
  length (map f l) = length l.
Proof.
  intros f. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 泛求和逐点单调 *)
Lemma nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> (nsum g l <= nsum h l)%nat.
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : (nsum g l <= nsum h l)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* 求和过 map = 复合求和（nsum 与 map 的交换桥） *)
Lemma nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q),
  nsum g (map f l) = nsum (fun x => g (f x)) l.
Proof.
  intros g f l. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ========== §8 保底件：推前计数引理与逐点支配 ========== *)

(* 【保底件·推前引理·计数形】map 后 y 的频数 = 原表中命中 f x == y 的票数
   （Fixpoint 直接形；报告声明：任务书之 Σ freq_q l x 形重计票，弃用） *)
Theorem freq_q_map : forall (f : Q -> Q) (y : Q) (l : list Q),
  freq_q y (map f l) = nsum (fun x : Q => if Qeq_bool y (f x) then 1%nat else 0%nat) l.
Proof.
  intros f y. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool y (f a)); rewrite IH; reflexivity.
Qed.

(* 【Qeq 形态桥】逐点支配：x 在原表中的票数 <= f x 在像表中的票数。
   真票（x == a）在 f 作用下仍命中（形态假设保命中），且像表可能
   额外并票（他值同像），故只增不减——这是 DPI 的微观机理。 *)
Lemma freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q), (freq_q x l <= freq_q (f x) (map f l))%nat.
Proof.
  intros f Hf x. induction l as [| a l IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x a) eqn:H1.
    + assert (H2 : Qeq_bool (f x) (f a) = true).
      { apply (proj2 (Qeq_bool_iff (f x) (f a))). apply Hf.
        apply (proj1 (Qeq_bool_iff x a)). exact H1. }
      rewrite H2. lia.
    + destruct (Qeq_bool (f x) (f a)); lia.
Qed.

(* 【质量合并单调】碰撞和面：sqsum (map f l) >= sqsum l。
   求和过 map（nsum_map）+ 逐点支配（freq_q_map_ge）两步归堆。 *)
Theorem sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, (sqsum l <= sqsum (map f l))%nat.
Proof.
  intros f Hf l. unfold sqsum.
  rewrite (nsum_map (fun y => freq_q y (map f l)) f l).
  apply nsum_le. intros x _. apply freq_q_map_ge. exact Hf.
Qed.

(* ========== §9 Q 除法/减号单调工具（DPI 的补形反号机件） ========== *)

(* 同分母商的减法分配（Qminus、Qdiv 先 unfold 再 ring，Qinv 为原子） *)
Lemma qdiv_sub_distr : forall A B D : Q, A / D - B / D == (A - B) / D.
Proof.
  intros A B D. unfold Qminus, Qdiv. ring.
Qed.

(* 减法右单调：A <= B 则 D - B <= D - A（补形单调反号的内核） *)
Lemma qsub_mono_r : forall D A B : Q, A <= B -> D - B <= D - A.
Proof.
  intros D A B H. unfold Qminus.
  apply (qadd_le D D (- B) (- A)).
  - apply Qle_refl.
  - apply qopp_le. exact H.
Qed.

(* 核形：N >= 1 时碰撞和在 [0, N²] 内单调反号穿过补形商。
   （qdiv_sub_distr 把商之差归并为单商，qdiv_nonneg 保号；
   N = 0 时 A = B = 0 两侧字面相同。） *)
Lemma hfreq_core_anti : forall (N A B : nat), (A <= B)%nat -> (B <= N * N)%nat ->
  (qn N * qn N - qn B) / (qn N * qn N) <= (qn N * qn N - qn A) / (qn N * qn N).
Proof.
  intros N A B HAB HBN.
  destruct N as [| m].
  - assert (HA : A = 0%nat) by lia.
    assert (HB : B = 0%nat) by lia.
    subst. apply Qle_refl.
  - assert (HD : 0 < qn (S m) * qn (S m)).
    { rewrite <- (qn_mul (S m) (S m)). apply qn_pos. simpl. apply Nat.lt_0_succ. }
    pose proof (qpos_neq0 (qn (S m) * qn (S m)) HD) as HDneq.
    apply (proj2 (Qle_0_sub'
              ((qn (S m) * qn (S m) - qn B) / (qn (S m) * qn (S m)))
              ((qn (S m) * qn (S m) - qn A) / (qn (S m) * qn (S m))))).
    rewrite (qdiv_sub_distr (qn (S m) * qn (S m) - qn A)
                            (qn (S m) * qn (S m) - qn B)
                            (qn (S m) * qn (S m))).
    apply qdiv_nonneg.
    + apply (proj1 (Qle_0_sub' (qn (S m) * qn (S m) - qn B)
                               (qn (S m) * qn (S m) - qn A))).
      apply qsub_mono_r. apply qn_le. exact HAB.
    + exact HD.
Qed.

(* ========== §10 【旗舰】数据处理不等式 DPI ========== *)

(* 观测（粗粒化合并质量）不增 H_freq：H_freq (map f l) <= H_freq l。
   形态假设 = 等价类合并语义的 Qeq 诚实守恒（对任意裸函数 f 该命题
   为假——裸函数可观测 Q 的 Record 表示，如取分子；反例
   l = [1/2; 2/4]，H_freq l = 0 而 H_freq (map (取分子) l) = 1/2。
   故旗舰带形态假设 (forall x y : Q, x == y -> f x == f y)。 *)
Theorem H_freq_dpi : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, H_freq (map f l) <= H_freq l.
Proof.
  intros f Hf l.
  assert (Hlen : length (map f l) = length l) by (apply length_map_self).
  destruct l as [| x xs].
  - replace (map f (@nil Q)) with (@nil Q) by reflexivity.
    apply Qle_refl.
  - unfold H_freq. rewrite Hlen.
    apply (hfreq_core_anti (length (x :: xs))
                           (sqsum (x :: xs)) (sqsum (map f (x :: xs)))).
    + apply sqsum_map_ge. exact Hf.
    + pose proof (sqsum_le (map f (x :: xs))) as Hs.
      rewrite Hlen in Hs. exact Hs.
Qed.

(* ========== §11 端点双例：DPI 两端的行为钉死 ========== *)

(* 端点一【恒等不衰减】：恒等映射（最细观测）零损耗——列表面
   Leibniz 相等直接桥接，无需形态假设。 *)
Theorem H_freq_map_id : forall l : list Q,
  H_freq (map (fun x : Q => x) l) == H_freq l.
Proof.
  intros l.
  assert (Hid : map (fun x : Q => x) l = l).
  { induction l as [| a l IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite Hid. apply Qeq_refl.
Qed.

(* 常数映射的像全同值（列表面 Leibniz） *)
Lemma in_map_const : forall (c : Q) (l : list Q) (a : Q),
  In a (map (fun _ : Q => c) l) -> a == c.
Proof.
  intros c l. induction l as [| b l IH]; simpl; intros a H.
  - destruct H.
  - destruct H as [H | H].
    + subst a. apply Qeq_refl.
    + apply IH. exact H.
Qed.

(* 端点二【常数全塌缩】：最粗观测（全部并成一桶）H_freq 取 0
   （简并面；对空表亦真，空表 H_freq 本为 0）。 *)
Theorem H_freq_map_const : forall (c : Q) (l : list Q),
  H_freq (map (fun _ : Q => c) l) == 0.
Proof.
  intros c l. apply H_freq_all_same_zero.
  intros a b Ha Hb.
  apply (Qeq_trans a c b).
  - exact (in_map_const c l a Ha).
  - apply (Qeq_sym b c). exact (in_map_const c l b Hb).
Qed.

(* ========== §12 加分：迭代不衰减链 ========== *)

(* 两步复合直推：第二次观测仍不增（需 g 亦为形态） *)
Theorem H_freq_map_twice : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, H_freq (map g (map f l)) <= H_freq (map f l).
Proof.
  intros f g Hf Hg l. apply (H_freq_dpi g Hg (map f l)).
Qed.

(* 链式：H_freq (map g (map f l)) <= H_freq (map f l) <= H_freq l *)
Theorem H_freq_map_chain : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, H_freq (map g (map f l)) <= H_freq l.
Proof.
  intros f g Hf Hg l.
  apply (Qle_trans (H_freq (map g (map f l))) (H_freq (map f l)) (H_freq l)).
  - apply (H_freq_dpi g Hg (map f l)).
  - apply (H_freq_dpi f Hf l).
Qed.

End DTPT_Entropy2.
Import DTPT_Entropy2.

(* ========== 审计：零公理实证（M3 归并后 15 件并档） ========== *)

Print Assumptions freq_q_app.
Print Assumptions freq_q_perm.
Print Assumptions H_freq_perm.
Print Assumptions H_freq_nonneg.
Print Assumptions H_freq_all_same_zero.
Print Assumptions H_freq_len_le_1.
Print Assumptions H_freq_eq0_all_same.
Print Assumptions freq_q_map.
Print Assumptions freq_q_map_ge.
Print Assumptions sqsum_map_ge.
Print Assumptions H_freq_dpi.
Print Assumptions H_freq_map_id.
Print Assumptions H_freq_map_const.
Print Assumptions H_freq_map_twice.
Print Assumptions H_freq_map_chain.
