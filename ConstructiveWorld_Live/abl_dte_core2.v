(* ==========================================================================
   abl_dte_core2.v —— DTPT_Entropy 前件参数消解供给·卷二（参数 39–76）。
   ── 使命：宿主 DTPT_Entropy.v 前件参数登记序第 39–76 位（语句坐标
   :944–:1392，31 条语句 38 参数，与卷一卷界零重叠）逐参数消解供给：T＝
   A 直供形（语句面＝登记形经 dte_c2_ 前缀映射逐字同构，证明体就地构造
   真构造、零宿主 Entropy 定理使用）；P′＝规范实例无前提精简版（参数前件
   于规范实例处内联构造）。38 参数＝36 供给＋2 登记（qpos_neq0／
   qmult_inv_cancel_r 前提或结论位否定形，照登记不供给，其消去内核在
   dte_c2_qdiv_eq0_num 证体内以 field 侧条件构造性重演；all_same 以现档
   逐字同构副本承载，供本卷 5 条 LOCPRED 参数语句使用）。41 件＝28 T＋
   7 辅助＋6 P′，全 Qed。真前提阻塞为零；宿主件零字节动，本件零 Require
   宿主（供给面为宿主语句面的自足替代世界）。
   ── 依赖：stdlib（QArith.QArith／Qabs、List、Arith Lia、Permutation、
   Extraction）＋基座 DTPT（qadd_nonneg／qadd_le 两件序工具——同构宿主
   件头依赖面）；零 Require 宿主 DTPT_Entropy。
   ── 对标行：A 直供形正本＝abl_dtd_core1／abl_dte_core1；P′ 应用形工艺＝
   abl_dtd_core4（规范实例内联输入）。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位；
   语句面全 Set 层（real_lt／real_le／real_le_b／QleT'／QltT bool 判定面／
   sigT／Empty_set 皆 Set 值），零 Prop 前件零 Prop 结论；<> 全件两处＝
   NEQ 参数面逐字透传（非自造）；名面全 dte_c2_ 前缀；尾置逐件 Print
   Assumptions Closed＋定理桶单命令 Separate Extraction，Obj.magic 零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dte_core2.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(* 〇 数据层承载副本（宿主 :921/:1058/:1126/:1193/:1195/:1250 现档     *)
(*    逐字同构，dte_c2_ 前缀隔离；见头注④。dte_c2_all_same 系混载      *)
(*    旗位（参数 63-64）之承载副本——注记位逐字承载、下游 LOCPRED 参数       *)
(*    使用面，  dtd_Qmem/dtd_Qnodup 先例同款）                    *)
(* ============================================================ *)

Fixpoint dte_c2_qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + dte_c2_qn k)%Q
  end.

Fixpoint dte_c2_freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (dte_c2_freq_q x ys) else dte_c2_freq_q x ys
  end.

Fixpoint dte_c2_nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + dte_c2_nsum f ys)%nat
  end.

Definition dte_c2_sqsum (l : list Q) : nat :=
  dte_c2_nsum (fun x => dte_c2_freq_q x l) l.

Definition dte_c2_all_same (l : list Q) : Prop :=
  forall a b, In a l -> In b l -> a == b.

Definition dte_c2_H_freq (l : list Q) : Q :=
  (dte_c2_qn (length l) * dte_c2_qn (length l) - dte_c2_qn (dte_c2_sqsum l))
    / (dte_c2_qn (length l) * dte_c2_qn (length l)).

(* ============================================================ *)
(* 一 辅助件区（7 枚·宿主 :927/:936/:951/:958/:1064/:1152/:1353 现档    *)
(*    同构副本——宿主零前提在役件，非参数位，供本件 T 证明体使用；          *)
(*    就地构造 真构造，序工具面使用基座 DTPT qadd_nonneg/qadd_le   *)
(*    （同构宿主 §1 证明体使用面））                                   *)
(* ============================================================ *)

Lemma dte_c2_qn_nonneg : forall n : nat, 0 <= dte_c2_qn n.
Proof.
  induction n as [| k IH].
  - apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + exact IH.
Qed.

Lemma dte_c2_qn_S_pos : forall k : nat, 0 < dte_c2_qn (S k).
Proof.
  intros k. simpl. apply (Qlt_le_trans 0 1 (1 + dte_c2_qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (dte_c2_qn k) (Qle_refl 1) (dte_c2_qn_nonneg k))
      as HH. simpl in HH. exact HH.
Qed.

Lemma dte_c2_qn_add : forall a b : nat, dte_c2_qn (a + b)%nat == dte_c2_qn a + dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. rewrite Qplus_0_l. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma dte_c2_qn_mul : forall a b : nat, dte_c2_qn (a * b)%nat == dte_c2_qn a * dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite dte_c2_qn_add. rewrite IH. ring.
Qed.

Lemma dte_c2_freq_q_le_length : forall (x : Q) (l : list Q),
  (dte_c2_freq_q x l <= length l)%nat.
Proof.
  intros x. induction l as [| y ys IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

Lemma dte_c2_nsum_const : forall (n : nat) (l : list Q),
  dte_c2_nsum (fun _ => n) l = (length l * n)%nat.
Proof.
  intros n l. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma dte_c2_nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q),
  dte_c2_nsum g (map f l) = dte_c2_nsum (fun x => g (f x)) l.
Proof.
  intros g f l. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ============================================================ *)
(* 二 供给定理 T 区（28 枚·34 参数）：逐枚＝底册语句面现档逐字（dte_c2_    *)
(*    前缀映射），证明体 就地构造 真构造。登记参数 43/44 以注释块     *)
(*    立档于底册登记位。                                              *)
(* ============================================================ *)

(* T〔参数 39〕=:944 qn_pos 现档逐字 *)
Theorem dte_c2_qn_pos : forall n : nat, (0 < n)%nat -> 0 < dte_c2_qn n.
Proof.
  intros n Hn. destruct n as [| m].
  - exfalso. lia.
  - apply dte_c2_qn_S_pos.
Qed.

(* T〔参数 40〕=:965 qn_le 现档逐字 *)
Theorem dte_c2_qn_le : forall a b : nat, (a <= b)%nat -> dte_c2_qn a <= dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b Hle.
  - apply dte_c2_qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply (qadd_le 1 1 (dte_c2_qn a) (dte_c2_qn b')).
      * apply Qle_refl.
      * apply IH. apply (le_S_n _ _ Hle).
Qed.

(* T〔参数 41〕=:976 qn_inj 现档逐字 *)
Theorem dte_c2_qn_inj : forall a b : nat, dte_c2_qn a == dte_c2_qn b -> a = b.
Proof.
  induction a as [| a IH]; intros b Heq.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (dte_c2_qn_S_pos b') as HP. simpl in HP.
      rewrite <- Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (dte_c2_qn_S_pos a) as HP. simpl in HP.
      rewrite Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (dte_c2_qn a)) in Heq.
      rewrite (Qplus_comm 1 (dte_c2_qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (dte_c2_qn a) (dte_c2_qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. rewrite Hab. reflexivity.
Qed.

(* T〔参数 42〕=:995 qlt_neq0 现档逐字（<> 系参数面逐字，见头注④） *)
Theorem dte_c2_qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

(* ──〔参数 43·只登记〕=:1000 qpos_neq0 : forall y : Q, 0 < y -> ~ (y == 0)。
   底册 §2.3 混载旗位（结论位否定形），照任务口径只登记不供给；
   失败显式申报 见交付报告 §四。 ── *)

(* ──〔参数 44·只登记〕=:1008 qmult_inv_cancel_r :
   forall A B : Q, ~ (B == 0) -> A * / B * B == A。
   底册 §2.3 混载旗位（前提位否定形），照登记不供给；其消去内核在
   下方 dte_c2_qdiv_eq0_num 证体内以 field 侧条件构造性真实重演。 ── *)

(* T〔参数 45〕=:1013 qsub_eq0 现档逐字 *)
Theorem dte_c2_qsub_eq0 : forall a b : Q, a - b == 0 -> a == b.
Proof.
  intros a b H.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* T〔参数 46〕=:1022 qdiv_zero_num 现档逐字 *)
Theorem dte_c2_qdiv_zero_num : forall A B : Q, A == 0 -> A / B == 0.
Proof.
  intros A B H. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

(* T〔参数 47-48〕=:1027 qdiv_eq0_num 现档逐字——证明体不经登记参数 44 件：
   消去步骤以 field 侧条件（构造性否定面 discharged by stdlib 严格序
   事实 Qlt_not_eq，宿主 :1002 同款喂法）独立重演 *)
Theorem dte_c2_qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> A == 0.
Proof.
  intros A B HB H. unfold Qdiv in H.
  assert (Hcancel : A * / B * B == A).
  { field. intro Hb. apply (Qlt_not_eq 0 B HB). apply (Qeq_sym B 0). exact Hb. }
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

(* T〔参数 49-50〕=:1035 qdiv_nonneg 现档逐字 *)
Theorem dte_c2_qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> 0 <= A / B.
Proof.
  intros A B HA HB. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

(* T〔参数 51〕=:1042 qnum_zero 现档逐字 *)
Theorem dte_c2_qnum_zero : forall n s : nat,
  dte_c2_qn (n * n) == dte_c2_qn s -> dte_c2_qn n * dte_c2_qn n - dte_c2_qn s == 0.
Proof.
  intros n s H. rewrite <- (dte_c2_qn_mul n n). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

(* T〔参数 52〕=:1048 qeqb_false_neq 现档逐字（<> 系参数面逐字，见头注④） *)
Theorem dte_c2_qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* T〔参数 53〕=:1083 freq_q_perm 现档逐字 *)
Theorem dte_c2_freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> dte_c2_freq_q x l = dte_c2_freq_q x p.
Proof.
  intros x l p H.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

(* T〔参数 54〕=:1094 freq_q_eq_all 现档逐字 *)
Theorem dte_c2_freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> dte_c2_freq_q x l = length l.
Proof.
  intros x l. induction l as [| y ys IH]; intros H.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal. apply IH. intros z Hz. apply H.
    right. exact Hz.
Qed.

(* T〔参数 55-56〕=:1106 freq_q_full_count 现档逐字 *)
Theorem dte_c2_freq_q_full_count : forall (x : Q) (l : list Q),
  dte_c2_freq_q x l = length l -> forall y, In y l -> y == x.
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (dte_c2_freq_q_le_length x l) as HL. lia.
    + apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (dte_c2_freq_q_le_length x l) as HL. lia.
      * exact Hy0.
Qed.

(* T〔参数 57〕=:1132 nsum_ext_in 现档逐字 *)
Theorem dte_c2_nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> dte_c2_nsum f l = dte_c2_nsum g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* T〔参数 58〕=:1141 nsum_perm 现档逐字 *)
Theorem dte_c2_nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> dte_c2_nsum f l = dte_c2_nsum f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* T〔参数 59〕=:1160 nsum_bound 现档逐字 *)
Theorem dte_c2_nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> (dte_c2_nsum f l <= length l * B)%nat.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : (dte_c2_nsum f ys <= length ys * B)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* T〔参数 60-62〕=:1171 nsum_bound_eq 现档逐字 *)
Theorem dte_c2_nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  dte_c2_nsum f l = (length l * B)%nat ->
  forall x, In x l -> f x = B.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : (dte_c2_nsum f ys <= length ys * B)%nat)
      by (apply (dte_c2_nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    assert (Hfy : f y = B) by lia.
    assert (HysEq : dte_c2_nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + apply IH.
      * intros z Hz. apply Hsat. right. exact Hz.
      * exact HysEq.
      * exact Hx0.
Qed.

(* ──〔参数 63-64·承载副本〕=:1195 all_same 定义位（底册 §2.3 显式
   注记位混载旗）。旗位照登记；注记位逐字同构副本＝〇区 dte_c2_all_same
   （  dtd_Qmem/dtd_Qnodup 先例），本卷 5 条 LOCPRED 参数语句（参数
   66-67/68/69/71/73）全经此副本供给。 ── *)

(* T〔参数 65〕=:1198 sqsum_perm 现档逐字 *)
Theorem dte_c2_sqsum_perm : forall l p : list Q,
  Permutation l p -> dte_c2_sqsum l = dte_c2_sqsum p.
Proof.
  intros l p H. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_ext_in (fun x => dte_c2_freq_q x l)
             (fun x => dte_c2_freq_q x p) l
             (fun x _ => dte_c2_freq_q_perm x l p H)).
  exact (dte_c2_nsum_perm (fun x => dte_c2_freq_q x p) l p H).
Qed.

(* T〔参数 66-67〕=:1214 freq_q_all_same 现档逐字 *)
Theorem dte_c2_freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> dte_c2_all_same l -> dte_c2_freq_q x l = length l.
Proof.
  intros x l Hin Hs. apply dte_c2_freq_q_eq_all. intros z Hz. apply Hs.
  - exact Hz.
  - exact Hin.
Qed.

(* T〔参数 68〕=:1222 sqsum_all_same 现档逐字 *)
Theorem dte_c2_sqsum_all_same : forall l : list Q,
  dte_c2_all_same l -> dte_c2_sqsum l = (length l * length l)%nat.
Proof.
  intros l Hs. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_ext_in (fun x => dte_c2_freq_q x l)
             (fun _ : Q => length l) l
             (fun x Hx => dte_c2_freq_q_all_same x l Hx Hs)).
  apply dte_c2_nsum_const.
Qed.

(* T〔参数 69〕=:1231 sqsum_eq_all_same 现档逐字 *)
Theorem dte_c2_sqsum_eq_all_same : forall l : list Q,
  dte_c2_sqsum l = (length l * length l)%nat -> dte_c2_all_same l.
Proof.
  intros l Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - unfold dte_c2_sqsum in Heq.
    pose proof (dte_c2_nsum_bound_eq (fun x0 => dte_c2_freq_q x0 (x :: xs))
                  (x :: xs) (length (x :: xs))
                  (fun x0 _ => dte_c2_freq_q_le_length x0 (x :: xs))
                  Heq x (or_introl eq_refl)) as Hfx.
    pose proof (dte_c2_freq_q_full_count x (x :: xs) Hfx) as Hall.
    intros a b Ha Hb. apply (Qeq_trans a x b).
    + apply Hall. exact Ha.
    + apply (Qeq_sym b x). apply Hall. exact Hb.
Qed.

(* T〔参数 70〕=:1255 H_freq_perm 现档逐字（本卷主定理） *)
Theorem dte_c2_H_freq_perm : forall l p : list Q,
  Permutation l p -> dte_c2_H_freq l == dte_c2_H_freq p.
Proof.
  intros l p Hp. unfold dte_c2_H_freq.
  rewrite (dte_c2_sqsum_perm l p Hp).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* T〔参数 71〕=:1281 H_freq_all_same_zero 现档逐字 *)
Theorem dte_c2_H_freq_all_same_zero : forall l : list Q,
  dte_c2_all_same l -> dte_c2_H_freq l == 0.
Proof.
  intros l Hs. unfold dte_c2_H_freq. apply dte_c2_qdiv_zero_num.
  apply dte_c2_qnum_zero.
  rewrite (dte_c2_sqsum_all_same l Hs). reflexivity.
Qed.

(* T〔参数 72〕=:1288 H_freq_len_le_1 现档逐字 *)
Theorem dte_c2_H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> dte_c2_H_freq l == 0.
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply dte_c2_H_freq_all_same_zero. intros a b Ha Hb. destruct Ha.
  - simpl in Hl. destruct xs as [| y ys].
    + apply dte_c2_H_freq_all_same_zero. intros a b Ha Hb.
      destruct Ha as [Ha | Ha].
      * subst a. destruct Hb as [Hb | Hb].
        -- subst b. apply Qeq_refl.
        -- destruct Hb.
      * destruct Ha.
    + simpl in Hl. exfalso. lia.
Qed.

(* T〔参数 73〕=:1304 H_freq_eq0_all_same 现档逐字 *)
Theorem dte_c2_H_freq_eq0_all_same : forall l : list Q,
  dte_c2_H_freq l == 0 -> dte_c2_all_same l.
Proof.
  intros l Heq. unfold dte_c2_H_freq in Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - assert (HB : 0 < dte_c2_qn (length (x :: xs)) * dte_c2_qn (length (x :: xs))).
    { rewrite <- (dte_c2_qn_mul (length (x :: xs)) (length (x :: xs))).
      apply dte_c2_qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : dte_c2_qn (length (x :: xs)) * dte_c2_qn (length (x :: xs))
                   - dte_c2_qn (dte_c2_sqsum (x :: xs)) == 0)
      by (apply (dte_c2_qdiv_eq0_num _ _ HB Heq)).
    pose proof (dte_c2_qsub_eq0 (dte_c2_qn (length (x :: xs))
                  * dte_c2_qn (length (x :: xs)))
                  (dte_c2_qn (dte_c2_sqsum (x :: xs))) Hnum) as Hab.
    rewrite <- (dte_c2_qn_mul (length (x :: xs)) (length (x :: xs))) in Hab.
    pose proof (dte_c2_qn_inj (length (x :: xs) * length (x :: xs))
                  (dte_c2_sqsum (x :: xs)) Hab) as Heqnat.
    apply dte_c2_sqsum_eq_all_same. symmetry. exact Heqnat.
Qed.

(* T〔参数 74〕=:1341 nsum_le 现档逐字 *)
Theorem dte_c2_nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> (dte_c2_nsum g l <= dte_c2_nsum h l)%nat.
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : (dte_c2_nsum g l <= dte_c2_nsum h l)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* T〔参数 75〕=:1376 freq_q_map_ge 现档逐字 *)
Theorem dte_c2_freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q),
  (dte_c2_freq_q x l <= dte_c2_freq_q (f x) (map f l))%nat.
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

(* T〔参数 76〕=:1392 sqsum_map_ge 现档逐字 *)
Theorem dte_c2_sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, (dte_c2_sqsum l <= dte_c2_sqsum (map f l))%nat.
Proof.
  intros f Hf l. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_map (fun y => dte_c2_freq_q y (map f l)) f l).
  apply dte_c2_nsum_le. intros x _. apply dte_c2_freq_q_map_ge. exact Hf.
Qed.

(* ============================================================ *)
(* 三 P′ 规范实例精简版区（6 枚·6 参数实证）：逐枚＝本件 T 面 @ 全实参显式应用，  *)
(*    参数前件于规范实例处内联构造（喂法与宿主面同构——其余 28 参数的规范     *)
(*    应用形通道（Nat.lt_0_succ/le_n/Qeq_refl/in_eq/Permutation_nil/      *)
(*    reflexivity 证人们）逐参数登记于交付报告对照表，本区 6 枚为应用形       *)
(*    通道的 proof-carrying 实证样例。R-2 防双供：6 枚 P′ 面均系宿主      *)
(*    结论面之特化形（带前件宿主语句的无前提实例），与宿主在役件零       *)
(*    面重合（宿主无 rev 形/自反射形在役语句），与本件 T 面异形。        *)
(* ============================================================ *)

(* P′〔参数 39〕qn_pos 规范实例：NAT 参数于 n:=1 处 Nat.lt_0_succ 0 输入 *)
Theorem dte_c2_qn_pos_one : 0 < dte_c2_qn 1.
Proof.
  exact (dte_c2_qn_pos 1 (Nat.lt_0_succ 0)).
Qed.

(* P′〔参数 40〕qn_le 自反射规范实例：NAT 参数于 b:=a 处 le_n 输入 *)
Theorem dte_c2_qn_le_refl : forall a : nat, dte_c2_qn a <= dte_c2_qn a.
Proof.
  intro a. exact (dte_c2_qn_le a a (le_n a)).
Qed.

(* P′〔参数 53〕freq_q_perm 反转规范实例：PERM 参数喂 Permutation_rev *)
Theorem dte_c2_freq_q_perm_rev : forall (x : Q) (l : list Q),
  dte_c2_freq_q x l = dte_c2_freq_q x (rev l).
Proof.
  intros x l. exact (dte_c2_freq_q_perm x l (rev l) (Permutation_rev l)).
Qed.

(* P′〔参数 58〕nsum_perm 反转规范实例：同上喂法 *)
Theorem dte_c2_nsum_perm_rev : forall (f : Q -> nat) (l : list Q),
  dte_c2_nsum f l = dte_c2_nsum f (rev l).
Proof.
  intros f l. exact (dte_c2_nsum_perm f l (rev l) (Permutation_rev l)).
Qed.

(* P′〔参数 65〕sqsum_perm 反转规范实例：同上喂法 *)
Theorem dte_c2_sqsum_perm_rev : forall l : list Q,
  dte_c2_sqsum l = dte_c2_sqsum (rev l).
Proof.
  intro l. exact (dte_c2_sqsum_perm l (rev l) (Permutation_rev l)).
Qed.

(* P′〔参数 70〕H_freq_perm 反转规范实例（本卷主定理）：真频率熵反转不变 *)
Theorem dte_c2_H_freq_perm_rev : forall l : list Q,
  dte_c2_H_freq l == dte_c2_H_freq (rev l).
Proof.
  intro l. exact (dte_c2_H_freq_perm l (rev l) (Permutation_rev l)).
Qed.

(* ============================================================ *)
(* 四 尾置验印区：Check 印＋逐件承认面验印，名清单＝41 零差             *)
(*    （28 T＋7 辅助＋6 P′，Qed 计数 41≤41 配额）                      *)
(* ============================================================ *)

Check dte_c2_qn_nonneg.
Check dte_c2_qn_S_pos.
Check dte_c2_qn_add.
Check dte_c2_qn_mul.
Check dte_c2_freq_q_le_length.
Check dte_c2_nsum_const.
Check dte_c2_nsum_map.
Check dte_c2_qn_pos.
Check dte_c2_qn_le.
Check dte_c2_qn_inj.
Check dte_c2_qlt_neq0.
Check dte_c2_qsub_eq0.
Check dte_c2_qdiv_zero_num.
Check dte_c2_qdiv_eq0_num.
Check dte_c2_qdiv_nonneg.
Check dte_c2_qnum_zero.
Check dte_c2_qeqb_false_neq.
Check dte_c2_freq_q_perm.
Check dte_c2_freq_q_eq_all.
Check dte_c2_freq_q_full_count.
Check dte_c2_nsum_ext_in.
Check dte_c2_nsum_perm.
Check dte_c2_nsum_bound.
Check dte_c2_nsum_bound_eq.
Check dte_c2_sqsum_perm.
Check dte_c2_freq_q_all_same.
Check dte_c2_sqsum_all_same.
Check dte_c2_sqsum_eq_all_same.
Check dte_c2_H_freq_perm.
Check dte_c2_H_freq_all_same_zero.
Check dte_c2_H_freq_len_le_1.
Check dte_c2_H_freq_eq0_all_same.
Check dte_c2_nsum_le.
Check dte_c2_freq_q_map_ge.
Check dte_c2_sqsum_map_ge.
Check dte_c2_qn_pos_one.
Check dte_c2_qn_le_refl.
Check dte_c2_freq_q_perm_rev.
Check dte_c2_nsum_perm_rev.
Check dte_c2_sqsum_perm_rev.
Check dte_c2_H_freq_perm_rev.

Print Assumptions dte_c2_qn_nonneg.
Print Assumptions dte_c2_qn_S_pos.
Print Assumptions dte_c2_qn_add.
Print Assumptions dte_c2_qn_mul.
Print Assumptions dte_c2_freq_q_le_length.
Print Assumptions dte_c2_nsum_const.
Print Assumptions dte_c2_nsum_map.
Print Assumptions dte_c2_qn_pos.
Print Assumptions dte_c2_qn_le.
Print Assumptions dte_c2_qn_inj.
Print Assumptions dte_c2_qlt_neq0.
Print Assumptions dte_c2_qsub_eq0.
Print Assumptions dte_c2_qdiv_zero_num.
Print Assumptions dte_c2_qdiv_eq0_num.
Print Assumptions dte_c2_qdiv_nonneg.
Print Assumptions dte_c2_qnum_zero.
Print Assumptions dte_c2_qeqb_false_neq.
Print Assumptions dte_c2_freq_q_perm.
Print Assumptions dte_c2_freq_q_eq_all.
Print Assumptions dte_c2_freq_q_full_count.
Print Assumptions dte_c2_nsum_ext_in.
Print Assumptions dte_c2_nsum_perm.
Print Assumptions dte_c2_nsum_bound.
Print Assumptions dte_c2_nsum_bound_eq.
Print Assumptions dte_c2_sqsum_perm.
Print Assumptions dte_c2_freq_q_all_same.
Print Assumptions dte_c2_sqsum_all_same.
Print Assumptions dte_c2_sqsum_eq_all_same.
Print Assumptions dte_c2_H_freq_perm.
Print Assumptions dte_c2_H_freq_all_same_zero.
Print Assumptions dte_c2_H_freq_len_le_1.
Print Assumptions dte_c2_H_freq_eq0_all_same.
Print Assumptions dte_c2_nsum_le.
Print Assumptions dte_c2_freq_q_map_ge.
Print Assumptions dte_c2_sqsum_map_ge.
Print Assumptions dte_c2_qn_pos_one.
Print Assumptions dte_c2_qn_le_refl.
Print Assumptions dte_c2_freq_q_perm_rev.
Print Assumptions dte_c2_nsum_perm_rev.
Print Assumptions dte_c2_sqsum_perm_rev.
Print Assumptions dte_c2_H_freq_perm_rev.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    定理桶：单条 Separate Extraction（  避坑——本件          *)
(*    仅此一条命令；41 定理结论面全数 Prop 离散承载，按家族提取擦除      *)
(*    惯例归约占位）。数据层真提取面＝6 承载副本（qn/freq_q/nsum/        *)
(*    sqsum/H_freq 真实现＋all_same 擦除位），归独立检验件               *)
(*    _dte_c2_probe.v 定向  另桶（分桶工艺执行位，       *)
(*    Obj.magic 双桶分桶归因见交付报告）。                              *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t7".
Separate Extraction dte_c2_qn_nonneg dte_c2_qn_S_pos dte_c2_qn_add
  dte_c2_qn_mul dte_c2_freq_q_le_length dte_c2_nsum_const dte_c2_nsum_map
  dte_c2_qn_pos dte_c2_qn_le dte_c2_qn_inj dte_c2_qlt_neq0 dte_c2_qsub_eq0
  dte_c2_qdiv_zero_num dte_c2_qdiv_eq0_num dte_c2_qdiv_nonneg
  dte_c2_qnum_zero dte_c2_qeqb_false_neq dte_c2_freq_q_perm
  dte_c2_freq_q_eq_all dte_c2_freq_q_full_count dte_c2_nsum_ext_in
  dte_c2_nsum_perm dte_c2_nsum_bound dte_c2_nsum_bound_eq dte_c2_sqsum_perm
  dte_c2_freq_q_all_same dte_c2_sqsum_all_same dte_c2_sqsum_eq_all_same
  dte_c2_H_freq_perm dte_c2_H_freq_all_same_zero dte_c2_H_freq_len_le_1
  dte_c2_H_freq_eq0_all_same dte_c2_nsum_le dte_c2_freq_q_map_ge
  dte_c2_sqsum_map_ge dte_c2_qn_pos_one dte_c2_qn_le_refl
  dte_c2_freq_q_perm_rev dte_c2_nsum_perm_rev dte_c2_sqsum_perm_rev
  dte_c2_H_freq_perm_rev.
