(* ==========================================================================)
   UpReqMinPKLChain.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：um_lt_le、um_eq_le、um_le_add_l、um_add_nonneg、um_le_add_r、um_mult_one_l、um_Emptyset_false、um_nreal、um_nreal_pos。
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
From Stdlib Require Import List Arith Lia.
Require Import UpAuditBridge.

(* ================= §1 um_lt_le 族 ================= *)
(* 0. 通用桥（Real 层，Section 外，全局可复用）                  *)

(* lt ⟹ le（real_le 的 Or 编码左支） *)
Lemma um_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* eq ⟹ le（Or 编码右支） *)
Lemma um_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  exact RealSetoid.real_eq_le.
Qed.

(* 0 ≤ y ⟹ x ≤ x + y（加非负数） *)
Lemma um_le_add_l : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus x y).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus x real_zero) (real_plus x y)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + exact Hy.
Qed.

(* 0 ≤ a、0 ≤ b ⟹ 0 ≤ a + b *)
Lemma um_add_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b ->
  real_le real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + exact Ha.
    + exact Hb.
Qed.

(* 0 ≤ y ⟹ x ≤ y + x（加非负数于左） *)
Lemma um_le_add_r : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus y x).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus real_zero x) (real_plus y x)).
  - apply (real_eq_trans x (real_plus x real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_plus_comm.
  - apply real_le_plus_compat.
    + exact Hy.
    + apply real_le_refl.
Qed.

(* 1·x == x（左单位；real_mult_one 是右单位版） *)
Lemma um_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* Empty_set → False 桥：扫描库把 Not 定义为 Set 层（A → Empty_set），
   归谬项须跨入 Prop 的 False（仅证明内部使用，语句层无 Prop） *)
Lemma um_Emptyset_false : Empty_set -> False.
Proof.
  intro e. exact (match e with end).
Qed.

(* 1. 索引表求和（seq 形态）：nreal / 位移 / nth 桥 / 常值        *)

(* nreal：nat → Real 嵌入（表长 N 的 Real 化） *)
Fixpoint um_nreal (n : nat) : Real :=
  match n with
  | Datatypes.O => real_zero
  | Datatypes.S k => real_plus real_one (um_nreal k)
  end.

Lemma um_nreal_pos : forall n : nat,
  real_lt real_zero (um_nreal (Datatypes.S n)).
Proof.
  induction n as [| k IH].
  - apply (real_lt_eq_lt real_zero real_one
                         (real_plus real_one (um_nreal Datatypes.O))).
    + apply real_lt_zero_one.
    + apply real_eq_sym. apply real_plus_zero.
  - apply real_plus_positive.
    + apply real_lt_zero_one.
    + exact IH.
Qed.

(* 由下标界给 nreal 正性：NatLt i n ⟹ n = S m ⟹ nreal n > 0 *)
Lemma um_nreal_pos_of_lt : forall (n i : nat),
  NatLt i n -> real_lt real_zero (um_nreal n).
Proof.
  intros n i Hi. destruct n as [| m].
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - exact (um_nreal_pos m).
Qed.

(* 求和位移：Σ_{seq (S s) n} f == Σ_{seq s n} (fun i => f (S i)) *)
Lemma um_seq_shift : forall (f : nat -> Real) (n s : nat),
  real_eq (real_list_sum nat f (seq (Datatypes.S s) n))
          (real_list_sum nat (fun i : nat => f (Datatypes.S i)) (seq s n)).
Proof.
  intros f n. induction n as [| n IH]; intro s.
  - cbn [seq real_list_sum]. apply real_eq_refl.
  - cbn [seq real_list_sum].
    apply (RealSetoid.real_eq_plus_compat (f (Datatypes.S s))
             (real_list_sum nat f (seq (Datatypes.S (Datatypes.S s)) n))
             (f (Datatypes.S s))
             (real_list_sum nat (fun i : nat => f (Datatypes.S i))
                                   (seq (Datatypes.S s) n))).
    + apply real_eq_refl.
    + exact (IH (Datatypes.S s)).
Qed.

(* skipn 求和步进：nth k rest 0 + Σ (skipn (S k) rest)
                    == Σ (skipn k rest) *)
Lemma um_skipn_sum_step : forall (k : nat) (rest : list Real),
  real_eq (real_plus (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest)))
          (real_list_sum Real (fun x : Real => x) (skipn k rest)).
Proof.
  induction k as [| k IH]; intro rest.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat q
               (real_list_sum Real (fun x : Real => x) rest2)
               q (real_list_sum Real (fun x : Real => x) rest2)).
      * apply real_eq_refl.
      * apply real_eq_refl.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      exact (IH rest2).
Qed.

(* nth 桥（主引理）：Σ_{seq s (length l)} nth i l 0 == Σ (skipn s l) *)
Lemma um_seq_nth_sum : forall (l : list Real) (s : nat),
  real_eq (real_list_sum nat (fun i : nat => nth i l real_zero)
                             (seq s (length l)))
          (real_list_sum Real (fun x : Real => x) (skipn s l)).
Proof.
  induction l as [| p rest IH]; intro s.
  - destruct s as [| k].
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
  - destruct s as [| k].
    + (* s = 0：p + Σ_{seq 1 n} nth i (p::rest) 0 == p + Σ rest *)
      cbn [seq length skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat
                (nth Datatypes.O (p :: rest) real_zero)
                (real_list_sum nat
                   (fun i : nat => nth i (p :: rest) real_zero)
                   (seq 1%nat (length rest)))
                p
                (real_list_sum Real (fun x : Real => x) rest)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (seq 1%nat (length rest)))
                 (real_list_sum nat
                    (fun i : nat => nth i rest real_zero)
                    (seq 0%nat (length rest)))).
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) 0%nat).
        -- exact (IH 0%nat).
    + (* s = S k：位移 + IH(rest, S k) + 步进引理三段拼合 *)
      cbn [seq length real_list_sum].
      apply (real_eq_trans
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i (p :: rest) real_zero)
                             (seq (Datatypes.S (Datatypes.S k))
                                  (length rest))))
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i rest real_zero)
                             (seq (Datatypes.S k) (length rest))))).
      * apply (RealSetoid.real_eq_plus_compat
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i (p :: rest) real_zero)
                     (seq (Datatypes.S (Datatypes.S k)) (length rest)))
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i rest real_zero)
                     (seq (Datatypes.S k) (length rest)))).
        -- apply real_eq_refl.
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) (Datatypes.S k)).
      * apply (real_eq_trans
                 (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                            (real_list_sum nat
                               (fun i : nat => nth i rest real_zero)
                               (seq (Datatypes.S k) (length rest))))
                 (real_plus (nth k rest real_zero)
                            (real_list_sum Real (fun x : Real => x)
                                          (skipn (Datatypes.S k) rest)))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (nth (Datatypes.S k) (p :: rest) real_zero)
                     (real_list_sum nat
                        (fun i : nat => nth i rest real_zero)
                        (seq (Datatypes.S k) (length rest)))
                     (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest))).
           ++ apply real_eq_refl.
           ++ exact (IH (Datatypes.S k)).
        -- exact (um_skipn_sum_step k rest).
Qed.

(* 常值表：Σ_{seq 0 n} c == nreal(n)·c *)
Lemma um_seq_const : forall (n : nat) (c : Real),
  real_eq (real_list_sum nat (fun _ : nat => c) (seq 0%nat n))
          (real_mult (um_nreal n) c).
Proof.
  induction n as [| n IH]; intro c.
  - cbn [seq um_nreal real_list_sum].
    apply real_eq_sym.
    apply (real_eq_trans (real_mult real_zero c)
             (real_mult c real_zero) real_zero).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - cbn [seq um_nreal real_list_sum].
    (* c + Σ_{seq 1 n} c == c + nreal n·c == (1 + nreal n)·c *)
    apply (real_eq_trans
             (real_plus c
                        (real_list_sum nat (fun _ : nat => c)
                                       (seq (Datatypes.S 0%nat) n)))
             (real_plus c (real_mult (um_nreal n) c))).
    + apply (RealSetoid.real_eq_plus_compat c
                (real_list_sum nat (fun _ : nat => c) (seq 1%nat n))
                c (real_mult (um_nreal n) c)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat (fun _ : nat => c) (seq 1%nat n))
                 (real_list_sum nat (fun _ : nat => c) (seq 0%nat n))).
        -- exact (um_seq_shift (fun _ : nat => c) n 0%nat).
        -- exact (IH c).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_plus real_one (um_nreal n)) c)
               (real_mult c (real_plus real_one (um_nreal n)))).
      * apply real_mult_comm.
      * apply (real_eq_trans
                 (real_mult c (real_plus real_one (um_nreal n)))
                 (real_plus (real_mult c real_one)
                            (real_mult c (um_nreal n)))).
        -- exact (real_distrib c real_one (um_nreal n)).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult c real_one) (real_mult c (um_nreal n))
                     c (real_mult (um_nreal n) c)).
           ++ apply real_mult_one.
           ++ apply real_mult_comm.
Qed.




Definition um_ent_term (p : Real) (Hp : real_lt real_zero p) : Real :=
  real_mult p (real_opp (cw_log p Hp)).

(* log 单调（≤ 版：由严格版 + real_log_wd 的 Or 分解拼合） *)
Lemma um_log_le_mono : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hle. destruct Hle as [Hlt | Heq].
  - apply um_lt_le. exact (real_log_lt_mono a b Ha Hb Hlt).
  - exact (um_eq_le _ _ (real_log_wd a b Ha Hb Heq)).
Qed.

(* 逐项熵项下界：p ≤ M ⟹ p·(−log M) ≤ p·(−log p)
   （log 反单调 + 乘非负权重 p） *)
Lemma um_ent_term_le : forall (p M : Real)
    (Hp : real_lt real_zero p) (HM : real_lt real_zero M),
  real_le p M ->
  real_le (real_mult p (real_opp (cw_log M HM)))
          (real_mult p (real_opp (cw_log p Hp))).
Proof.
  intros p M Hp HM Hle.
  assert (Hlog : real_le (real_opp (cw_log M HM)) (real_opp (cw_log p Hp))).
  { apply real_opp_le_compat.
    apply um_log_le_mono. exact Hle. }
  apply (RealSetoid.real_le_id_l
           (real_mult p (real_opp (cw_log M HM)))
           (real_mult (real_opp (cw_log M HM)) p)
           (real_mult p (real_opp (cw_log p Hp)))).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_opp (cw_log M HM)) p)
             (real_mult (real_opp (cw_log p Hp)) p)
             (real_mult p (real_opp (cw_log p Hp)))).
    + apply real_mult_comm.
    + exact (real_le_mult_compat_weak (real_opp (cw_log M HM))
                                      (real_opp (cw_log p Hp)) p
               (um_lt_le real_zero p Hp) Hlog).
Qed.

(* 3. NatLt 下标制的索引和引理（逐点假设函数，无 Prop 解构）      *)
(*    NatLt i n := Id (i <? n) true（扫描库 Set 层界编码）；      *)
(*    关键转换：NatLt (S i) (S n) ≡ NatLt i n（ltb/leb iota）。   *)

(* 索引和的逐点 ≤ *)
Lemma um_rls_le_N : forall (f g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le (f j) (g j)) ->
  real_le (real_list_sum nat f (seq 0%nat n))
          (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros f g n. revert f g. induction n as [| n IH]; intros f g Hpt.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    apply real_le_plus_compat.
    + exact (Hpt 0%nat id_refl).
    + apply (RealSetoid.real_le_compat
                (real_list_sum nat (fun j : nat => f (Datatypes.S j))
                                   (seq 0%nat n))
                (real_list_sum nat f (seq 1%nat n))
                (real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                   (seq 0%nat n))
                (real_list_sum nat g (seq 1%nat n))).
      * exact (real_eq_sym _ _ (um_seq_shift f n 0%nat)).
      * exact (real_eq_sym _ _ (um_seq_shift g n 0%nat)).
      * apply (IH (fun j : nat => f (Datatypes.S j))
                  (fun j : nat => g (Datatypes.S j))).
        intros j Hj. exact (Hpt (Datatypes.S j) Hj).
Qed.

(* 索引和的非负 *)
Lemma um_rls_nonneg_N : forall (g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le real_zero (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g Hnn.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    assert (Htail : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0%nat n))).
    { apply (IH (fun j : nat => g (Datatypes.S j))).
      intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
    assert (Hstep : real_le (real_plus real_zero real_zero)
                       (real_plus (g 0%nat)
                                  (real_list_sum nat
                                     (fun j : nat => g (Datatypes.S j))
                                     (seq 0%nat n)))).
    { apply real_le_plus_compat.
      - exact (Hnn 0%nat id_refl).
      - exact Htail. }
    exact (RealSetoid.real_le_compat
              (real_plus real_zero real_zero)
              real_zero
              (real_plus (g 0%nat)
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0%nat n)))
              (real_plus (g 0%nat) (real_list_sum nat g (seq 1%nat n)))
              (real_plus_zero real_zero)
              (RealSetoid.real_eq_plus_compat (g 0%nat)
                 (real_list_sum nat
                    (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                 (g 0%nat)
                 (real_list_sum nat g (seq 1%nat n))
                 (real_eq_refl (g 0%nat))
                 (real_eq_sym _ _ (um_seq_shift g n 0%nat)))
              Hstep).
    (* 尾段 le 已由 Hstep 的 d 分量直接给出 *)
Qed.

(* 单成员 ≤ 全和：NatLt i n ⟹ g i ≤ Σ_{seq 0 n} g（权重逐点非负） *)
Lemma um_rls_single_le_N : forall (g : nat -> Real) (n i : nat),
  NatLt i n ->
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le (g i) (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g i Hi Hnn.
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - cbn [seq real_list_sum]. destruct i as [| i'].
    + (* i = 0：头项即目标项；尾段非负经位移换形 *)
      assert (Ht0 : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0%nat n))).
      { apply (um_rls_nonneg_N (fun j : nat => g (Datatypes.S j)) n).
        intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
      apply um_le_add_l.
      exact (RealSetoid.real_le_compat real_zero real_zero
                (real_list_sum nat
                   (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                (real_list_sum nat g (seq 1%nat n))
                (real_eq_refl real_zero)
                (real_eq_sym _ _ (um_seq_shift g n 0%nat))
                Ht0).
    + (* i = S i'：IH 于 S i'（NatLt (S i') n ≡ NatLt i' n），
         再沿 um_seq_shift 的 eq 换形到 Σ_{seq 1 n} g，加非负头项 *)
      assert (Htail : real_le (g (Datatypes.S i'))
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0%nat n))).
      { apply (IH (fun j : nat => g (Datatypes.S j)) i'
                  Hi (fun j Hj => Hnn (Datatypes.S j) Hj)). }
      apply real_le_trans with
        (y := real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                (seq 0%nat n)).
      * exact Htail.
      * apply (real_le_trans
                 (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                 (real_list_sum nat g (seq 1%nat n))
                 (real_plus (g 0%nat) (real_list_sum nat g (seq 1%nat n)))).
        -- apply (RealSetoid.real_le_compat
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat g (seq 1%nat n))
                     (real_eq_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n)))
                     (real_eq_sym _ _ (um_seq_shift g n 0%nat))
                     (real_le_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n)))).
        -- apply (um_le_add_r (real_list_sum nat g (seq 1%nat n)) (g 0%nat)).
           exact (Hnn 0%nat id_refl).
Qed.

(* 4. 世界段：tokens / ratio + 三分判定元（对偶 ord_le_dec）      *)

Section UpMinPWorld.

(* 三分判定元：a ≤ b ∨ b < a（Real 层 le/lt 的构造性判定假设） *)
Variable um_trich_probe : forall a b : Real, Or (real_le a b) (real_lt b a).

(* 最大值：fold real_max（nil ↦ 0） *)
Fixpoint um_fmax (l : list Real) : Real :=
  match l with
  | nil => real_zero
  | p :: rest => real_max p (um_fmax rest)
  end.

(* 逐点上界（下标版）：NatLt i (length l) ⟹ nth i l 0 ≤ fold_max l *)
Lemma um_fmax_ge_nth : forall (l : list Real) (i : nat),
  NatLt i (length l) -> real_le (nth i l real_zero) (um_fmax l).
Proof.
  induction l as [| p rest IH]; intros i Hi.
  - (* NatLt i 0 ≡ Id false true *)
    destruct (um_Emptyset_false (id_false_true Hi)).
  - cbn [length um_fmax]. destruct i as [| i'].
    + (* 头元素：p ≤ max p M；NatLt 0 (S n) ≡ id_refl *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r p (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact Hle.
      * apply (RealSetoid.real_le_id_r p p
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply real_le_refl.
    + (* 尾元素：nth i' rest 0 ≤ max p M；NatLt (S i') (S n) ≡ NatLt i' n *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact (IH i' Hi).
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          p (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply um_lt_le.
           exact (real_le_lt_trans (nth i' rest real_zero)
                     (um_fmax rest) p (IH i' Hi) Hlt).
Qed.

(* 可达性（下标版）：非空见证 + 逐项正 ⟹ 最大值在表中取到 *)
Lemma um_fmax_mem_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  sigT (fun i : nat =>
          prod (NatLt i (length l))
               (real_eq (nth i l real_zero) (um_fmax l))).
Proof.
  induction l as [| p rest IH]; intros [i0 Hi0] Hpos.
  - destruct (um_Emptyset_false (id_false_true Hi0)).
  - destruct rest as [| q rest2].
    + (* 单元素表：um_fmax [p] = real_max p real_zero *)
      destruct (um_trich_probe p real_zero) as [Hle | Hlt].
      * (* p ≤ 0 与 p > 0 矛盾 *)
        destruct (um_Emptyset_false
                    (real_lt_irrefl real_zero
                       (real_lt_eq_lt real_zero p real_zero
                          (Hpos Datatypes.O id_refl)
                          (real_eq_sym real_zero p
                             (real_le_antisym real_zero p
                                (um_lt_le real_zero p
                                   (Hpos Datatypes.O id_refl))
                                Hle))))).
      * (* 0 < p：max p 0 == p（左支胜），见证 i = 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p real_zero) p
                          (real_r_max_l_iff p real_zero
                             (um_lt_le real_zero p Hlt))))).
    + (* 尾表非空（构造性见证 0）：可达性传给 IH，max p M 按三分取支 *)
      assert (Hrestnn : sigT (fun i : nat => NatLt i (length (q :: rest2)))).
      { exact (existT _ Datatypes.O id_refl). }
      assert (Hposr : forall i : nat,
                NatLt i (length (q :: rest2)) ->
                real_lt real_zero (nth i (q :: rest2) real_zero)).
      { intros i Hi.
        apply (Hpos (Datatypes.S i)).
        (* NatLt (S i) (S (S m)) ≡ NatLt i (S m)（ltb/leb iota） *)
        exact Hi. }
      specialize (IH Hrestnn Hposr).
      destruct IH as [j [Hjlen Hjeq]].
      destruct (um_trich_probe p (um_fmax (q :: rest2))) as [Hle | Hlt].
      * (* max p M == M ∈ 尾表（右支胜）：见证 S j；
           NatLt (S j) (S (S m)) ≡ NatLt j (S m) ≡ Hjlen *)
        exact (existT _ (Datatypes.S j)
                 (pair Hjlen
                       (real_eq_trans
                          (nth (Datatypes.S j) (p :: q :: rest2) real_zero)
                          (nth j (q :: rest2) real_zero)
                          (real_max p (um_fmax (q :: rest2)))
                          (real_eq_refl (nth j (q :: rest2) real_zero))
                          (real_eq_trans
                             (nth j (q :: rest2) real_zero)
                             (um_fmax (q :: rest2))
                             (real_max p (um_fmax (q :: rest2)))
                             Hjeq
                             (real_eq_sym _ _
                                (RealInterfaceEnhancedMod.real_r_max_r_iff p
                                   (um_fmax (q :: rest2)) Hle)))))).
      * (* M < p：max p M == p（左支胜）：见证 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p (um_fmax (q :: rest2))) p
                          (real_r_max_l_iff p (um_fmax (q :: rest2))
                             (um_lt_le (um_fmax (q :: rest2)) p Hlt))))).
Qed.

(* 最大值为正：非空见证 + 逐项正 *)
Lemma um_fmax_pos_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  real_lt real_zero (um_fmax l).
Proof.
  intros l Hne Hpos.
  destruct (um_fmax_mem_nth l Hne Hpos) as [i [Hi Heq]].
  exact (RealSetoid.real_lt_compat real_zero real_zero
           (nth i l real_zero) (um_fmax l)
           (real_eq_refl real_zero) Heq (Hpos i Hi)).
Qed.

(* 5. Min-P 截断世界（tokens + ratio）                           *)

Section MinPEntropy.

(* 概率表：非空见证、逐项正（下标有界）、和 = 1 *)
Variable tokens : list Real.
Variable tokens_ne : sigT (fun i : nat => NatLt i (length tokens)).
Variable tokens_pos : forall i : nat,
  real_lt real_zero (nth i tokens real_zero).
Hypothesis tokens_sum :
  real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one.

(* Min-P 阈值比例：0 < ratio ≤ 1 *)
Variable ratio : Real.
Hypothesis ratio_pos : real_lt real_zero ratio.
Hypothesis ratio_le_one : real_le ratio real_one.

(* ---- 核心对象 ---- *)
Definition um_N : nat := length tokens.

Definition um_pmax : Real := um_fmax tokens.

Definition um_Hpmax : real_lt real_zero um_pmax :=
  um_fmax_pos_nth tokens tokens_ne (fun i _ => tokens_pos i).

(* 逐点 k ≤ p_max（下标化） *)
Lemma um_le_pmax : forall i : nat,
  NatLt i um_N -> real_le (nth i tokens real_zero) um_pmax.
Proof.
  intros i Hi. exact (um_fmax_ge_nth tokens i Hi).
Qed.

(* S：源分布的 Shannon 熵（list 离散、下标求和版） *)
Definition um_entropy : Real :=
  real_list_sum nat
    (fun i : nat => um_ent_term (nth i tokens real_zero) (tokens_pos i))
    (seq 0%nat um_N).

(* Min-P 阈值与保留指示：thr = ratio·p_max；保留者取 k，淘汰者取 0 *)
Definition um_thr : Real := real_mult ratio um_pmax.

Definition um_keepF (p : Real) : Real :=
  match um_trich_probe um_thr p with
  | inl _ => p
  | inr _ => real_zero
  end.

(* 保留质量 / 截断质量：kept = Σ keepF，dropped = 1 − kept（定义性） *)
Definition um_kept : Real :=
  real_list_sum nat (fun i : nat => um_keepF (nth i tokens real_zero))
                (seq 0%nat um_N).

Lemma um_keepF_nonneg_nth : forall (x : Real) (Hx : real_lt real_zero x),
  real_le real_zero (um_keepF x).
Proof.
  intros x Hx.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hkeep | Hdrop].
  - apply um_lt_le. exact Hx.
  - apply real_le_refl.
Qed.

(* 保留权重的逐点非负（下标全域版，供索引和引理使用） *)
Definition um_keepF_nonneg : forall i : nat,
  real_le real_zero (um_keepF (nth i tokens real_zero)) :=
  fun i => um_keepF_nonneg_nth (nth i tokens real_zero) (tokens_pos i).

Definition um_dropped : Real :=
  real_plus real_one (real_opp um_kept).

(* ---- keepF 的代数性质 ---- *)
Lemma um_keepF_congr : forall x y : Real,
  real_eq x y -> real_eq (um_keepF x) (um_keepF y).
Proof.
  intros x y Heq.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hx | Hx];
    destruct (um_trich_probe um_thr y) as [Hy | Hy].
  - (* x、y 均保留：keepF x == x == y == keepF y *)
    apply Heq.
  - (* x 保留、y 淘汰：y < thr ⟹ x < thr（换形）与 thr ≤ x 矛盾 *)
    destruct (um_Emptyset_false (real_lt_irrefl x
                (real_lt_le_trans x um_thr x
                   (RealSetoid.real_lt_compat y x um_thr um_thr
                      (real_eq_sym x y Heq) (real_eq_refl um_thr) Hy)
                   Hx))).
  - (* x 淘汰、y 保留：thr ≤ y ⟹ thr ≤ x（换形）与 x < thr 矛盾 *)
    destruct (um_Emptyset_false (real_lt_irrefl um_thr
                (real_le_lt_trans um_thr x um_thr
                   (RealSetoid.real_le_compat um_thr um_thr y x
                      (real_eq_refl um_thr) (real_eq_sym x y Heq) Hy)
                   Hx))).
  - (* 均淘汰：0 == 0 *)
    apply real_eq_refl.
Qed.


(* thr ≤ p_max：ratio·p_max ≤ 1·p_max == p_max *)
Lemma um_thr_le_pmax : real_le um_thr um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_mult ratio um_pmax)
                                 (real_mult real_one um_pmax) um_pmax).
  - apply um_mult_one_l.
  - exact (real_le_mult_compat_weak ratio real_one um_pmax
             (um_lt_le real_zero um_pmax um_Hpmax) ratio_le_one).
Qed.

(* 件 1：S ≥ −log(p_max)                                        *)

Theorem entropy_ge_neg_log_p_max :
  real_le (real_opp (cw_log um_pmax um_Hpmax)) um_entropy.
Proof.
  apply real_le_trans with
    (y := real_list_sum nat
            (fun i : nat =>
               real_mult (nth i tokens real_zero)
                         (real_opp (cw_log um_pmax um_Hpmax)))
            (seq 0%nat um_N)).
  - (* (−log p_max) == (−log p_max)·Σ nth == (−log p_max)·1
       （反向即 Σ nth·(−log p_max)） *)
    apply um_eq_le.
    apply (real_eq_trans
             (real_opp (cw_log um_pmax um_Hpmax))
             (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                        (real_list_sum nat
                           (fun i : nat => nth i tokens real_zero)
                           (seq 0%nat um_N)))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                          (real_list_sum nat
                             (fun i : nat => nth i tokens real_zero)
                             (seq 0%nat um_N)))
               (real_mult (real_opp (cw_log um_pmax um_Hpmax)) real_one)).
      * apply (RealSetoid.real_eq_mult_compat
                  (real_opp (cw_log um_pmax um_Hpmax))
                  (real_list_sum nat
                     (fun i : nat => nth i tokens real_zero)
                     (seq 0%nat um_N))
                  (real_opp (cw_log um_pmax um_Hpmax)) real_one).
        -- apply real_eq_refl.
        -- (* Σ_{seq 0 N} nth i tokens 0 == 1 *)
           apply (real_eq_trans
                    (real_list_sum nat
                       (fun i : nat => nth i tokens real_zero)
                       (seq 0%nat (length tokens)))
                    (real_list_sum Real (fun x : Real => x) tokens)).
           ++ exact (um_seq_nth_sum tokens 0%nat).
           ++ exact tokens_sum.
      * apply real_mult_one.
    + apply real_eq_sym.
      exact (real_list_sum_linear_r nat
               (real_opp (cw_log um_pmax um_Hpmax))
               (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N)).
  - (* 逐项：nth i tokens 0 ≤ p_max ⟹ nth·(−log p_max) ≤ 熵项 *)
    apply (um_rls_le_N
              (fun i : nat =>
                 real_mult (nth i tokens real_zero)
                           (real_opp (cw_log um_pmax um_Hpmax)))
              (fun i : nat =>
                 um_ent_term (nth i tokens real_zero) (tokens_pos i))
              um_N).
    intros j Hj.
    exact (um_ent_term_le (nth j tokens real_zero) um_pmax
              (tokens_pos j) um_Hpmax (um_le_pmax j Hj)).
Qed.

(* pick_max 必被保留：kept ≥ p_max *)
Lemma um_kept_ge_pmax : real_le um_pmax um_kept.
Proof.
  destruct (um_fmax_mem_nth tokens tokens_ne (fun i _ => tokens_pos i))
    as [istar [Hiistar Heqstar]].
  apply (RealSetoid.real_le_id_l um_pmax
            (um_keepF (nth istar tokens real_zero)) um_kept).
  - (* eq um_pmax (keepF (nth istar))：p_max 被保留 ⟹ keepF um_pmax == um_pmax，
       再沿 congruence 换形到 keepF (nth istar) *)
    apply (real_eq_trans um_pmax (um_keepF um_pmax)
             (um_keepF (nth istar tokens real_zero))).
    + unfold um_keepF.
      destruct (um_trich_probe um_thr um_pmax) as [Hkeep | Hdrop].
      * apply real_eq_refl.
      * exact (False_rect _
                 (um_Emptyset_false
                    (real_lt_irrefl um_pmax
                       (real_lt_le_trans um_pmax um_thr um_pmax Hdrop
                                          um_thr_le_pmax)))).
    + exact (um_keepF_congr um_pmax (nth istar tokens real_zero)
               (real_eq_sym _ _ Heqstar)).
  - (* 单成员 ≤ 全和：keepF (nth istar) ≤ Σ keepF *)
    exact (um_rls_single_le_N
              (fun i : nat => um_keepF (nth i tokens real_zero))
              um_N istar Hiistar (fun j _ => um_keepF_nonneg j)).
Qed.

(* e^{−S} ≤ p_max：S ≥ −log p_max ⟹ exp antitone ⟹
   e^{−S} ≤ e^{−(−log p_max)} == e^{log p_max} == p_max *)
Lemma um_exp_neg_S_le_pmax :
  real_le (real_exp_neg um_entropy) um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_exp_neg um_entropy)
            (real_exp_neg (real_opp (cw_log um_pmax um_Hpmax))) um_pmax).
  - 
    exact (real_exp_neg_log_inv um_pmax um_Hpmax).
  - apply real_exp_neg_le_decr.
    exact entropy_ge_neg_log_p_max.
Qed.

(* 件 2：dropped ≤ 1 − e^{−S}                                   *)

Theorem dropped_le_one_minus_exp_neg_S :
  real_le um_dropped
          (real_plus real_one (real_opp (real_exp_neg um_entropy))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_exp_neg_S_le_pmax.
    + exact um_kept_ge_pmax.
Qed.

(* 件 3：dropped ≤ 1 − 1/N（N = |tokens|；均匀特例）             *)

Definition um_Npos : real_lt real_zero (um_nreal um_N).
Proof.
  destruct tokens_ne as [i Hi].
  exact (um_nreal_pos_of_lt um_N i Hi).
Defined.

(* p_max ≥ 1/N：Σk = 1 ≤ N·p_max ⟹ inv N ≤ p_max
   （反证：p_max < inv N ⟹ N·p_max < N·inv N == 1，矛盾） *)
Lemma um_pmax_ge_inv_n :
  real_le (real_inv_pos (um_nreal um_N) um_Npos) um_pmax.
Proof.
  assert (H1 : real_le real_one
                 (real_mult (um_nreal um_N) um_pmax)).
  { (* 1 == Σnth ≤ Σ(const p_max) == N·p_max *)
    apply real_le_trans with
      (y := real_list_sum nat
              (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N)).
    - apply um_eq_le.
      apply (real_eq_trans real_one
               (real_list_sum Real (fun x : Real => x) tokens)
               (real_list_sum nat
                  (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N))).
      * exact (real_eq_sym _ _ tokens_sum).
      * exact (real_eq_sym _ _ (um_seq_nth_sum tokens 0%nat)).
    - apply real_le_trans with
        (y := real_list_sum nat (fun _ : nat => um_pmax) (seq 0%nat um_N)).
      + apply (um_rls_le_N (fun i : nat => nth i tokens real_zero)
                 (fun _ : nat => um_pmax) um_N).
        intros j Hj. apply um_le_pmax. exact Hj.
      + apply um_eq_le. exact (um_seq_const um_N um_pmax). }
  destruct (um_trich_probe (real_inv_pos (um_nreal um_N) um_Npos)
                           um_pmax) as [Hle | Hlt].
  - exact Hle.
  - destruct (um_Emptyset_false
                (real_lt_irrefl real_one
                   (real_le_lt_trans real_one
                      (real_mult (um_nreal um_N) um_pmax) real_one H1
                      (real_lt_eq_lt
                         (real_mult (um_nreal um_N) um_pmax)
                         (real_mult (um_nreal um_N)
                                    (real_inv_pos (um_nreal um_N) um_Npos))
                         real_one
                         (real_lt_mult_compat um_pmax
                            (real_inv_pos (um_nreal um_N) um_Npos)
                            (um_nreal um_N) um_Npos Hlt)
                         (real_inv_pos_correct (um_nreal um_N) um_Npos))))).
Qed.

Theorem dropped_le_one_minus_inv_n :
  real_le um_dropped
          (real_plus real_one
                (real_opp (real_inv_pos (um_nreal um_N) um_Npos))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_pmax_ge_inv_n.
    + exact um_kept_ge_pmax.
Qed.

End MinPEntropy.

End UpMinPWorld.
(* ================= §2 x1_plus_opp_cancel 族 ================= *)
From Stdlib Require Import QArith.Qring.

Section X1MinPKLChain.

(* ---- 概率表世界（对齐 UpMinP.MinPEntropy 出口剖面） ---- *)
Variable trich : forall a b : Real, Or (real_le a b) (real_lt b a).
Variable tokens : list Real.
Variable tokens_ne : sigT (fun i : nat => NatLt i (length tokens)).
Variable tokens_pos : forall i : nat,
  real_lt real_zero (ListDef.nth i tokens real_zero).
Hypothesis tokens_sum :
  real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one.
Variable ratio : Real.
Hypothesis ratio_pos : real_lt real_zero ratio.
Hypothesis ratio_le_one : real_le ratio real_one.

Notation N := (um_N tokens).
Notation S := (um_entropy tokens tokens_pos).
Notation K := (um_kept trich tokens ratio).
Notation D := (um_dropped trich tokens ratio).
Notation thr := (um_thr tokens ratio).
Notation pmax := (um_pmax tokens).

(* 0. 通用小桥（本文件自建）                                     *)

(* 1 − (1 − x) == x（kept 与 dropped 互补恒等核） *)
Lemma x1_plus_opp_cancel : forall x : Real,
  real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp x)))) x.
Proof.
  intro x.
  apply (real_eq_trans _
           (real_plus real_one (real_plus (real_opp real_one) x))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_plus (real_opp real_one) (real_opp (real_opp x)))).
      * apply real_opp_plus.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- apply real_opp_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus real_one (real_opp real_one)) x)).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero x)).
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply (real_eq_trans _ (real_plus x real_zero)).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
Qed.

(* seq 平移：Σ_{seq (S s) n} h == Σ_{seq s n} (h ∘ S) *)
Lemma x1_seq_shift : forall (n s : nat) (h : nat -> Real),
  real_eq (real_list_sum nat h (ListDef.seq (Datatypes.S s) n))
          (real_list_sum nat (fun i => h (Datatypes.S i)) (ListDef.seq s n)).
Proof.
  induction n as [| n IH]; intro s; intro h.
  - cbn [seq real_list_sum]. apply real_eq_refl.
  - cbn [seq real_list_sum].
    apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + exact (IH (Datatypes.S s) h).
Qed.

(* nth 位移：nth (S i) (p::rest) == nth i rest *)
Lemma x1_nth_S_cons : forall (i : nat) (p : Real) (rest : list Real),
  real_eq (ListDef.nth (Datatypes.S i) (p :: rest) real_zero)
          (ListDef.nth i rest real_zero).
Proof.
  intros i p rest. destruct i as [| i'].
  - cbn [ListDef.nth]. apply real_eq_refl.
  - cbn [ListDef.nth]. apply real_eq_refl.
Qed.

(* 通用输运：list 和 == seq 下标和（任意 f；um_seq_nth_sum 的泛化版， *)
(*   nth 全程保符号，仅经 x1_seq_shift 位移——对应 UpMinP 纪律）      *)
Lemma x1_sum_list_seq : forall (l : list Real) (f : Real -> Real),
  real_eq (real_list_sum Real f l)
          (real_list_sum nat (fun i => f (ListDef.nth i l real_zero))
                         (ListDef.seq 0%nat (length l))).
Proof.
  intros l f. induction l as [| p rest IH].
  - cbn [length seq real_list_sum]. apply real_eq_refl.
  - cbn [length seq real_list_sum].
    apply (real_eq_trans _
             (real_plus (f (ListDef.nth Datatypes.O (p :: rest) real_zero))
                (real_list_sum nat (fun i => f (ListDef.nth i rest real_zero))
                                (ListDef.seq 0%nat (length rest))))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * exact IH.
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * apply real_eq_sym.
        exact (x1_seq_shift (length rest) 0%nat
                  (fun i => f (ListDef.nth i (p :: rest) real_zero))).
Qed.

(* seq 限点外延：逐点（i < n）相等 ⟹ seq 和相等 *)
Lemma x1_seq_ext : forall (n : nat) (f g : nat -> Real),
  (forall i : nat, NatLt i n -> real_eq (f i) (g i)) ->
  real_eq (real_list_sum nat f (ListDef.seq 0%nat n))
          (real_list_sum nat g (ListDef.seq 0%nat n)).
Proof.
  intros n f g H.
  apply (real_le_antisym
           (real_list_sum nat f (ListDef.seq 0%nat n))
           (real_list_sum nat g (ListDef.seq 0%nat n))).
  - apply (um_rls_le_N f g n).
    intros j Hjn. apply um_eq_le. exact (H j Hjn).
  - apply (um_rls_le_N g f n).
    intros j Hjn. apply um_eq_le.
    apply real_eq_sym. exact (H j Hjn).
Qed.

(* 逆元运输：x == x' ⟹ inv x == inv x' *)
Lemma x1_inv_compat : forall (x x' : Real) (Hx : real_lt real_zero x)
    (Hx' : real_lt real_zero x'),
  real_eq x x' -> real_eq (real_inv_pos x Hx) (real_inv_pos x' Hx').
Proof.
  intros x x' Hx Hx' Heq.
  apply (real_inv_unique x' (real_inv_pos x Hx) (real_inv_pos x' Hx')).
  - apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_sym. exact Heq.
      * apply real_eq_refl.
    + apply real_inv_pos_correct.
  - apply real_inv_pos_correct.
Qed.

(* 乘法对加法右分配（root real_opp_mult 同模式） *)
Lemma x1_mult_plus_distr : forall x a b : Real,
  real_eq (real_mult x (real_plus a b))
          (real_plus (real_mult x a) (real_mult x b)).
Proof.
  intros x a b.
  apply real_eq_of_zero_diff.
  intro n.
  destruct x as [ux Hx]. destruct a as [ua Ha]. destruct b as [ub Hb].
  simpl. ring.
Qed.


Lemma x1_log_inv_eq_opp_log : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (cw_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (cw_log x Hx)).
Proof.
  intros x Hx.
  assert (H0 : real_eq (real_plus (cw_log (real_inv_pos x Hx)
                                     (real_inv_pos_pos x Hx))
                          (cw_log x Hx))
                       real_zero).
  { apply (real_eq_trans _
             (cw_log (real_mult (real_inv_pos x Hx) x)
                (real_mult_positive (real_inv_pos x Hx) x
                   (real_inv_pos_pos x Hx) Hx))).
    - apply real_eq_sym. apply real_log_mult.
    - apply (real_eq_trans _ (cw_log real_one real_lt_zero_one)).
      + apply (real_eq_trans _
                 (cw_log (real_mult (real_inv_pos x Hx) x)
                    (real_mult_positive (real_inv_pos x Hx) x
                       (real_inv_pos_pos x Hx) Hx))).
        * (* X1b 对应引理：该 trans 两端本就同一项——refl 直接闭合
               语法头，evars 挡住 delta 展开） *)
          apply real_eq_refl.
        * apply (real_log_wd
                   (real_mult (real_inv_pos x Hx) x) real_one
                   (real_mult_positive (real_inv_pos x Hx) x
                      (real_inv_pos_pos x Hx) Hx)
                   real_lt_zero_one).
          -- apply (real_eq_trans _
                       (real_mult x (real_inv_pos x Hx))).
             ++ apply real_mult_comm.
             ++ apply real_inv_pos_correct.
          (* X1b：原第二发 `-- apply real_eq_refl.` 为多余子弹——real_log_wd
             全显应用后仅剩单目标，已由上一 `--` 链闭合，此处按 + 推进 *)
      + apply real_log_one. }
  apply (real_eq_trans _
           (real_plus (real_plus (cw_log (real_inv_pos x Hx)
                                     (real_inv_pos_pos x Hx))
                          (cw_log x Hx))
                      (real_opp (cw_log x Hx)))).
  - apply (real_eq_trans _
             (real_plus (cw_log (real_inv_pos x Hx)
                                    (real_inv_pos_pos x Hx))
                           (real_plus (cw_log x Hx)
                              (real_opp (cw_log x Hx))))).
    + (* X1b：子弹1目标实为 `A == A+(B+−B)`（非 assoc 形），经 A+0 完成 *)
      apply (real_eq_trans _
                 (real_plus (cw_log (real_inv_pos x Hx)
                                        (real_inv_pos_pos x Hx))
                               real_zero)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- (* X1b：此位目标是 `0 == B+−B`（compat 第二位反向），sym 后消解 *)
           apply real_eq_sym. apply real_plus_opp.
    + (* X1b：assoc 本朝向即 `x+(y+z) == (x+y)+z`（S02 ），直放即可 *)
      apply real_plus_assoc.
  - apply (real_eq_trans _
             (real_plus real_zero (real_opp (cw_log x Hx)))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact H0.
      * apply real_eq_refl.
    + apply (real_eq_trans _
               (real_plus (real_opp (cw_log x Hx)) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Qed.

(* 1. 审计桥实例（UpAuditBridge 在概率表世界上消解）              *)

(* 温度因子安全包装：正元恒等，非正元取 1（保证全局正性） *)
Definition x1_tf (x : Real) : Real :=
  match trich x real_zero with
  | inl _ => real_one
  | inr _ => x
  end.

Lemma x1_tf_pos : forall x : Real, real_lt real_zero (x1_tf x).
Proof.
  intro x. unfold x1_tf.
  destruct (trich x real_zero) as [Hle | Hlt].
  - exact real_lt_zero_one.
  - exact Hlt.
Qed.

Lemma x1_tf_id : forall x : Real,
  real_lt real_zero x -> real_eq (x1_tf x) x.
Proof.
  intros x Hx. unfold x1_tf.
  destruct (trich x real_zero) as [Hle | Hlt].
  - exact (False_rect _ (um_Emptyset_false (real_lt_irrefl real_zero
              (real_lt_le_trans real_zero x real_zero Hx Hle)))).
  - apply real_eq_refl.
Qed.

(* Min-P 保留判定（阈值 thr = ratio·p_max；与 um_keepF 同一判定项） *)
Definition x1_keep (_ : list Real) (x : Real) : Set :=
  match trich thr x with
  | inl _ => unit
  | inr _ => Empty_set
  end.

Definition x1_keep_dec : forall (_ : list Real) (x : Real),
  Or (x1_keep nil x) (Not (x1_keep nil x)).
Proof.
  intros _ x. unfold x1_keep.
  destruct (trich thr x) as [Hk | Hd].
  - exact (inl tt).  (* X1b：unit 构造子是 tt（I 是 Prop 层 True 的构造子） *)
  - (* X1b：Not 是 Set 层定义（S01），内层 match 不被 simpl 归约——
       显式给 a 标注 Empty_set，与 Not(match …) 经 delta+iota 可转换 *)
    exact (inr (fun a : Empty_set => match a with end)).
Defined.

(* 0 < thr（ratio·p_max，双正相乘） *)
Lemma x1_thr_pos : real_lt real_zero thr.
Proof.
  unfold thr, um_thr.
  exact (real_mult_positive ratio pmax ratio_pos
           (um_Hpmax trich tokens tokens_ne tokens_pos)).
Qed.

(* 完整配分 Z_full == 1 *)
Lemma x1_Zfull_eq_one : real_eq (Z_full Real tokens x1_tf) real_one.
Proof.
  unfold Z_full.
  apply (real_eq_trans _
           (real_list_sum nat (fun i => x1_tf (ListDef.nth i tokens real_zero))
                          (ListDef.seq 0%nat (length tokens)))).
  - apply x1_sum_list_seq.
  - apply (real_eq_trans _
             (real_list_sum nat (fun i => ListDef.nth i tokens real_zero)
                             (ListDef.seq 0%nat (length tokens)))).
    + apply (x1_seq_ext (length tokens)
               (fun i => x1_tf (ListDef.nth i tokens real_zero))
               (fun i => ListDef.nth i tokens real_zero)).
      intro i. intro Hj. apply x1_tf_id. apply tokens_pos.
    + apply (real_eq_trans _
               (real_list_sum Real (fun x : Real => x) tokens)).
      * apply um_seq_nth_sum.
      * exact tokens_sum.
Qed.

Lemma x1_Zfull_pos : real_lt real_zero (Z_full Real tokens x1_tf).
Proof.
  (* X1b：lt_compat 剖面 x1 x2 y1 y2 + 三证据；0<1 与 Z_full==1 重述为 0<Z_full *)
  apply (RealSetoid.real_lt_compat real_zero real_zero real_one
           (Z_full Real tokens x1_tf)
           (real_eq_refl real_zero)
           (real_eq_sym (Z_full Real tokens x1_tf) real_one x1_Zfull_eq_one)
           real_lt_zero_one).
Qed.

(* inv(Z_full) == 1 *)
Lemma x1_inv_of_Zfull :
  real_eq (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos) real_one.
Proof.
  apply (real_inv_unique (Z_full Real tokens x1_tf)
           (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos) real_one).
  - apply real_inv_pos_correct.
  - apply (real_eq_trans _ (Z_full Real tokens x1_tf)).
    + apply real_mult_one.
    + exact x1_Zfull_eq_one.
Qed.

(* 截断质量正性（uab_temp_sum_pos 的实例：argmax 必被保留） *)
Lemma x1_temp_sum_pos_inst : forall _ : list Real,
  real_lt real_zero
    (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil).
Proof.
  intro Hj.
  assert (Hsum : real_eq
    (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil)
    (real_list_sum nat
       (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                 | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                 | inr _ => real_zero
                 end)
       (ListDef.seq 0%nat (length tokens)))).
  { unfold uab_temp_sum, real_minp_temp_sum. apply x1_sum_list_seq. }
  destruct (um_fmax_mem_nth trich tokens tokens_ne
              (fun (i : nat) (_ : NatLt i (length tokens)) => tokens_pos i))
    as [istar [Histar Heqstar]].
  assert (Hthle : real_le thr (ListDef.nth istar tokens real_zero)).
  { apply (RealSetoid.real_le_id_r thr pmax
             (ListDef.nth istar tokens real_zero)
             (real_eq_sym _ _ Heqstar)
             (um_thr_le_pmax trich tokens tokens_ne
                (fun i => tokens_pos i) ratio ratio_le_one)). }
  assert (Hnn : forall j : nat, NatLt j (length tokens) ->
    real_le real_zero
      (match x1_keep_dec nil (ListDef.nth j tokens real_zero) with
       | inl _ => x1_tf (ListDef.nth j tokens real_zero)
       | inr _ => real_zero
       end)).
  { intros j _. unfold x1_keep_dec, x1_keep.
    destruct (trich thr (ListDef.nth j tokens real_zero)) as [Hk | Hd].
    - apply um_lt_le. apply x1_tf_pos.
    - apply real_le_refl. }
  assert (Hstar : real_lt real_zero
    (match x1_keep_dec nil (ListDef.nth istar tokens real_zero) with
     | inl _ => x1_tf (ListDef.nth istar tokens real_zero)
     | inr _ => real_zero
     end)).
  { unfold x1_keep_dec, x1_keep.
    destruct (trich thr (ListDef.nth istar tokens real_zero)) as [Hk | Hd].
    - apply x1_tf_pos.
    - exact (False_rect _ (um_Emptyset_false
                (real_lt_irrefl (ListDef.nth istar tokens real_zero)
                (real_lt_le_trans (ListDef.nth istar tokens real_zero) thr
                   (ListDef.nth istar tokens real_zero) Hd Hthle)))). }
  (* X1b：先证 seq 和版正性（single_le 完成），再经 lt_compat 运输回 uab_temp_sum。
     原稿 compat 假设位错位（x2 误占 real_one 且 eq 证据顺序颠倒） *)
  assert (HM : real_lt real_zero
    (real_list_sum nat
       (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                 | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                 | inr _ => real_zero
                 end)
       (ListDef.seq 0%nat (length tokens)))).
  { apply (real_lt_le_trans real_zero
             (match x1_keep_dec nil (ListDef.nth istar tokens real_zero) with
              | inl _ => x1_tf (ListDef.nth istar tokens real_zero)
              | inr _ => real_zero
              end)).
    - exact Hstar.
    - exact (um_rls_single_le_N
               (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                         | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                         | inr _ => real_zero
                         end)
               (length tokens) istar Histar Hnn). }
  apply (RealSetoid.real_lt_compat real_zero real_zero
           (real_list_sum nat
              (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                        | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                        | inr _ => real_zero
                        end)
              (ListDef.seq 0%nat (length tokens)))
           (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil)
           (real_eq_refl real_zero)
           (real_eq_sym _ _ Hsum)
           HM).
Qed.

(* 桥：Z_aud == um_kept（kept） *)
Definition x1_Zaud : Real :=
  uab_Z_aud Real tokens x1_tf x1_keep x1_keep_dec x1_Zfull_pos nil.

Theorem x1_Zaud_eq_kept : real_eq x1_Zaud K.
Proof.
  unfold x1_Zaud.
  apply (real_eq_trans _
           (real_list_sum Real
              (fun w : Real =>
                 match x1_keep_dec nil w with
                 | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos nil w
                 | inr _ => real_zero
                 end) tokens)).
  - exact (real_Z_aud_is_kept_mass Real tokens x1_tf x1_keep x1_keep_dec
             x1_Zfull_pos nil).
  - apply (real_eq_trans _
             (real_list_sum nat
                (fun i =>
                   match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                   | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos
                                nil (ListDef.nth i tokens real_zero)
                   | inr _ => real_zero
                   end)
                (ListDef.seq 0%nat (length tokens)))).
    + apply x1_sum_list_seq.
    + apply (x1_seq_ext (length tokens)
               (fun i =>
                  match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                  | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos
                               nil (ListDef.nth i tokens real_zero)
                  | inr _ => real_zero
                  end)
               (fun i => um_keepF trich tokens ratio
                           (ListDef.nth i tokens real_zero))).
      intro i. intro Hj.
      (* X1b：trich 藏在 x1_keep_dec 的依赖 Or 体下，直接 destruct trich 会触发
         「ill-formed elimination predicate」抽象失败。改走三段：
         (1) 先 destruct keep_dec（目标无语法 trich，抽象平凡合法）；
         (2) kernel 运输后 unfold x1_keep/um_keepF，再 destruct trich
             （此时载体 Kk:match o0 with unit|Empty 为非嵌套谓词，抽象合法）；
         (3) 混合支用载体空/居头矛盾完成。 *)
      destruct (x1_keep_dec nil (ListDef.nth i tokens real_zero)) as [Kk | Kd].
      * (* dec 判 keep：LHS iota 归到 kernel(w)，再与 um_keepF(w) 对齐 *)
        apply (real_eq_trans _
                 (real_markov_kernel Real tokens x1_tf x1_Zfull_pos nil
                    (ListDef.nth i tokens real_zero))).
        -- apply real_eq_refl.
        -- unfold x1_keep in Kk. unfold um_keepF.
           destruct (trich thr (ListDef.nth i tokens real_zero)) as [H2 | H2].
           ++ (* kernel ≡ tf(w)·inv(Z) == w·inv(Z) == w·1 == w *)
              apply (real_eq_trans _
                       (real_mult (ListDef.nth i tokens real_zero)
                          (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos))).
              ** apply RealSetoid.real_eq_mult_compat.
                 --- apply x1_tf_id. apply tokens_pos.
                 --- apply real_eq_refl.
              ** apply (real_eq_trans _
                           (real_mult (ListDef.nth i tokens real_zero) real_one)).
                 --- apply RealSetoid.real_eq_mult_compat.
                     +++ apply real_eq_refl.
                     +++ exact x1_inv_of_Zfull.
                 --- apply real_mult_one.
           ++ (* trich 判 drop 而 dec 判 keep：载体 Kk 必空 *)
              destruct Kk.
      * (* dec 判 drop：LHS iota 归到 0 *)
        apply (real_eq_trans _ real_zero).
        -- apply real_eq_refl.
        -- unfold x1_keep in Kd. unfold um_keepF.
           destruct (trich thr (ListDef.nth i tokens real_zero)) as [H2 | H2].
           ++ (* trich 判 keep 而 dec 判 drop：Not 载体 Kd 作用于 tt 得 Empty *)
              destruct (Kd tt).
           ++ exact (real_eq_refl real_zero).
Qed.

(* 2. 主件一：KL(minp‖full) ≤ S                                 *)

Definition x1_minp_kernel : Real -> Real :=
  uab_minp_kernel Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst nil.

Definition x1_minp_keep_pos :
  forall w : Real, x1_keep nil w -> real_lt real_zero (x1_minp_kernel w) :=
  uab_minp_keep_pos Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst x1_tf_pos nil.

Definition x1_Zaud_pos_cert : real_lt real_zero x1_Zaud :=
  uab_Z_aud_pos_cert Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst x1_Zfull_pos nil.

Definition x1_KL : Real :=
  real_list_sum Real
    (uab_kl_q_full Real tokens x1_tf x1_keep x1_keep_dec
       x1_tf_pos x1_Zfull_pos nil x1_minp_kernel x1_minp_keep_pos) tokens.

(* 互补恒等（论文形态）：x1_KL == −log(1 − dropped）                          *)
(* X1b 迁移注记：本定理依赖 0 < K 证书（x1_K_pos，源自 x1_exp_neg_S_le_kept）， *)
(*   故整体后移至 x1_exp_neg_S_le_kept / x1_K_pos 之后；内联 5 处              *)

(* e^−S ≤ kept（由 dropped ≤ 1 − e^−S 与互补恒等） *)
Theorem x1_exp_neg_S_le_kept : real_le (real_exp_neg S) K.
Proof.
  pose proof (dropped_le_one_minus_exp_neg_S trich tokens tokens_ne
                tokens_pos tokens_sum ratio ratio_le_one) as H4.
  apply (RealSetoid.real_le_id_l (real_exp_neg S)
           (real_plus real_one
              (real_opp (real_plus real_one (real_opp (real_exp_neg S)))))).  - apply real_eq_sym. apply x1_plus_opp_cancel.
  - (* X1b：real_le_id_r 子弹序 = 先 eq 位后 le 位（原稿反序） *)
    apply (RealSetoid.real_le_id_r
             (real_plus real_one
                (real_opp (real_plus real_one (real_opp (real_exp_neg S)))))
             (real_plus real_one (real_opp D))).
    + exact (x1_plus_opp_cancel K).
    + apply real_le_plus_compat.
      * apply real_le_refl.
      * apply real_opp_le_compat. exact H4.
Qed.

(* 0 < K（kept 正性：0 < e^−S ≤ K；X1b 新增，供互补恒等与 wd 假设位消解） *)
Lemma x1_K_pos : real_lt real_zero K.
Proof.
  exact (real_lt_le_trans real_zero (real_exp_neg S) K
           (real_exp_neg_pos S) x1_exp_neg_S_le_kept).
Qed.

(* 互补恒等（论文形态）：x1_KL == −log(1 − dropped)
   （X1b 自「主件一」定义区后移至此：依赖 x1_K_pos；
     原 5 处内联 lt_le_trans 证书收缩为 x1_K_pos —— R5 收缩） *)
(* K ≤ 1−D：D ≡ 1−K（定义性，UpMinP L684），故本式经 x1_plus_opp_cancel 归于 K≤K *)
Definition x1_K_le_one_minus_D :
  real_le K (real_plus real_one (real_opp D)) :=
  RealSetoid.real_le_id_r K K (real_plus real_one (real_opp D))
    (real_eq_sym _ _ (x1_plus_opp_cancel K)) (real_le_refl K).

(* 互补恒等（论文形态）：x1_KL == −log(1 − dropped)
   （X1b 自「主件一」定义区后移至此：依赖 x1_K_pos；
     原 5 处内联 lt_le_trans 证书收缩为 x1_K_pos —— R5 收缩） *)
Theorem x1_kl_eq_opp_log_one_minus_dropped :
  real_eq x1_KL
    (real_opp (real_log (real_plus real_one (real_opp D))
                 (real_lt_le_trans real_zero K
                    (real_plus real_one (real_opp D))
                    x1_K_pos x1_K_le_one_minus_D))).
Proof.
  apply (real_eq_trans x1_KL
           (real_opp (real_log K x1_K_pos))).
  - apply (real_eq_trans _
             (real_opp (real_log x1_Zaud x1_Zaud_pos_cert))).
    + exact (real_minp_kl_cost Real tokens x1_tf x1_keep x1_keep_dec
               x1_temp_sum_pos_inst x1_tf_pos x1_Zfull_pos nil).
    + apply RealSetoid.real_eq_opp_compat.
      (* X1b：a/b/Ha/Hb 皆可由目标合一，apply 后仅剩 Heq 一目标 *)
      apply real_log_wd.
      exact x1_Zaud_eq_kept.
  - apply RealSetoid.real_eq_opp_compat.
    apply real_log_wd.
    exact (real_eq_sym _ _ (x1_plus_opp_cancel K)).
Qed.

(* [4] 主件一：KL(minp‖full) ≤ S *)
Theorem x1_kl_le_entropy : real_le x1_KL S.
Proof.
  pose proof (real_minp_kl_cost Real tokens x1_tf x1_keep x1_keep_dec
                x1_temp_sum_pos_inst x1_tf_pos x1_Zfull_pos nil) as Hkl.
  pose proof x1_exp_neg_S_le_kept as Hexp.
  assert (Hlogpos : real_lt real_zero K).
  { exact (real_lt_le_trans real_zero (real_exp_neg S) K
             (real_exp_neg_pos S) Hexp). }
  pose proof (um_log_le_mono (real_exp_neg S) K
                (real_exp_neg_pos S) Hlogpos Hexp) as Hmono.
  assert (H2 : real_le (real_opp S) (real_log K Hlogpos)).
  { apply (RealSetoid.real_le_id_l (real_opp S)
             (cw_log (real_exp_neg S) (real_exp_neg_pos S))
             (real_log K Hlogpos)).
    - (* X1b：−S == log(e^−S)：log_inv 消解给 cauchy 形，正性证明经
         real_log_wd 重述为 real_exp_neg_pos S（不透明常量须语法同形） *)
      apply (real_eq_trans _
                 (cw_log (cauchy_real_exp (real_opp S))
                    (cauchy_real_exp_pos (real_opp S)))).
      + apply real_eq_sym.
        exact (log_inv_exp_neg_thm (real_opp S)
                 (cauchy_real_exp_pos (real_opp S))).
      + apply real_log_wd.
        exact (real_eq_refl (cauchy_real_exp (real_opp S))).
    - exact Hmono. }
  apply (RealSetoid.real_le_id_l x1_KL
           (real_opp (real_log K Hlogpos)) S).
  - apply (real_eq_trans _
             (real_opp (real_log x1_Zaud x1_Zaud_pos_cert))).
    + exact Hkl.
    + apply RealSetoid.real_eq_opp_compat.
      (* X1b：Ha/Hb 可由目标合一，apply real_log_wd 后仅剩 Heq *)
      apply real_log_wd.
      exact x1_Zaud_eq_kept.
  - (* X1b：opp_le_compat 给 −log K ≤ −(−S)，再经 real_opp_opp 运输到 ≤ S *)
    apply (RealSetoid.real_le_id_r
             (real_opp (real_log K Hlogpos))
             (real_opp (real_opp S)) S).
    + exact (real_opp_opp S).
    + apply real_opp_le_compat. exact H2.
Qed.

(* 3. 主件二：S ≤ log|S|（Gibbs 于均匀 + 逐 eps 余量）            *)

Lemma x1_N_pos : real_lt real_zero (um_nreal N).
Proof.
  (* X1b：um_Npos（UpMinP ，语句仅依赖 tokens）直接消解——
     原稿 destruct/rewrite 组合在 Rocq9 下「length tokens」语法面已被
     destruct 代换，rewrite 必空转 *)
  exact (um_Npos tokens tokens_ne).
Qed.

Notation LN := (cw_log (um_nreal N) x1_N_pos).
Notation U := (real_inv_pos (um_nreal N) x1_N_pos).
Notation HqU := (real_inv_pos_pos (um_nreal N) x1_N_pos).

Lemma x1_log_U_eq_opp_LN : real_eq (cw_log U HqU) (real_opp LN).
Proof. exact (x1_log_inv_eq_opp_log (um_nreal N) x1_N_pos). Qed.


Lemma x1_kl_term_expand : forall (k : Real) (Hk : real_lt real_zero k),
  real_eq (real_kl_term k U Hk HqU)
          (real_plus (real_mult k LN)
                     (real_opp (real_mult k (real_opp (cw_log k Hk))))).
Proof.
  intros k Hk. unfold real_kl_term.
  (* X1b 重构：k·(−log(U·inv k)) == k·(−((−LN)+(−log k))) == k·(LN+log k)
     原稿 4 处 `k` 误占正性证明位（应为 Hk），且 opp_plus 朝向与
     两段 trans 中项错位，此版按直推链重排。 *)
  apply (real_eq_trans _
           (real_mult k
              (real_opp (real_plus (real_opp LN) (real_opp (cw_log k Hk)))))).
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_opp_compat.
      apply (real_eq_trans _
                 (real_plus (cw_log U HqU)
                            (cw_log (real_inv_pos k Hk)
                                    (real_inv_pos_pos k Hk)))).
      * apply real_log_mult.
      * apply RealSetoid.real_eq_plus_compat.
        -- exact x1_log_U_eq_opp_LN.
        -- exact (x1_log_inv_eq_opp_log k Hk).
  - 
    apply (real_eq_trans _
               (real_mult k (real_plus LN (cw_log k Hk)))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply (real_eq_trans _
                   (real_plus (real_opp (real_opp LN))
                              (real_opp (real_opp (cw_log k Hk))))).
        -- (* X1b：real_opp_plus 本朝向即 −(a+b) == (−a)+(−b)，直放 *)
           apply real_opp_plus.
        -- apply RealSetoid.real_eq_plus_compat.
           ++ apply real_opp_opp.
           ++ apply real_opp_opp.
    + apply (real_eq_trans _
               (real_plus (real_mult k LN) (real_mult k (cw_log k Hk)))).
      * apply x1_mult_plus_distr.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- apply real_eq_sym.
           apply (real_eq_trans _
                      (real_opp (real_opp (real_mult k (cw_log k Hk))))).
           ++ (* X1b：子弹序随子目标序；opp_mult 朝向 −(a·b)==a·(−b) 取对称 *)
              apply RealSetoid.real_eq_opp_compat.
              apply real_eq_sym. apply real_opp_mult.
           ++ apply real_opp_opp.
Qed.

(* kl 项在权重上的运输（包装 ⟹ 原表项） *)
Lemma x1_kl_term_compat_p : forall (p p' : Real)
    (Hp : real_lt real_zero p) (Hp' : real_lt real_zero p'),
  real_eq p p' ->
  real_eq (real_kl_term p U Hp HqU) (real_kl_term p' U Hp' HqU).
Proof.
  intros p p' Hp Hp' Heq. unfold real_kl_term.
  apply RealSetoid.real_eq_mult_compat.
  - exact Heq.
  - apply RealSetoid.real_eq_opp_compat.
    (* X1b：a/b/Ha/Hb 可由目标合一，apply real_log_wd 后仅剩 Heq 位 *)
    apply real_log_wd.
    apply RealSetoid.real_eq_mult_compat.
    * apply real_eq_refl.
    * (* X1b：x/x'/Hx/Hx' 皆由目标合一，仅剩 Heq 位 *)
      apply x1_inv_compat.
      exact Heq.
Qed.

(* [5] 逐 eps 形：S ≤ log N + eps *)
Theorem x1_entropy_le_log_N_eps : forall eps : Real,
  real_lt real_zero eps -> real_le S (real_plus LN eps).
Proof.
  intros eps Heps.
  assert (Hnormp : real_eq (real_list_sum nat
      (fun i => x1_tf (ListDef.nth i tokens real_zero))
      (ListDef.seq 0%nat N)) real_one).
  { apply (real_eq_trans _
             (real_list_sum nat (fun i => ListDef.nth i tokens real_zero)
                             (ListDef.seq 0%nat N))).
    - apply (x1_seq_ext N (fun i => x1_tf (ListDef.nth i tokens real_zero))
               (fun i => ListDef.nth i tokens real_zero)).
      intro i. intro Hj. apply x1_tf_id. apply tokens_pos.
    - apply (real_eq_trans _
               (real_list_sum Real (fun x : Real => x) tokens)).
      * apply um_seq_nth_sum.
      * exact tokens_sum. }
  assert (Hnormq : real_eq (real_list_sum nat (fun _ : nat => U)
                               (ListDef.seq 0%nat N)) real_one).
  { apply (real_eq_trans _ (real_mult (um_nreal N) U)).
    - apply um_seq_const.
    - apply real_inv_pos_correct. }
  pose proof (real_gibbs_inequality_eps nat (ListDef.seq 0%nat N)
                (fun i => x1_tf (ListDef.nth i tokens real_zero))
                (fun _ : nat => U)
                (fun i => x1_tf_pos (ListDef.nth i tokens real_zero))
                (fun _ : nat => HqU) Hnormp Hnormq eps Heps) as Hg.
  assert (Hpt : forall i : nat, NatLt i N ->
    real_eq (real_kl_term (x1_tf (ListDef.nth i tokens real_zero)) U
               (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
            (real_plus (real_mult (ListDef.nth i tokens real_zero) LN)
                       (real_opp (um_ent_term
                          (ListDef.nth i tokens real_zero) (tokens_pos i))))).
  { intros i Hi.
    apply (real_eq_trans _
             (real_kl_term (ListDef.nth i tokens real_zero) U
                (tokens_pos i) HqU)).
    - (* X1b：p/p'/Hp/Hp' 皆由目标合一，仅剩 Heq（tf 包装逐点恒等） *)
      apply x1_kl_term_compat_p.
      apply x1_tf_id. apply tokens_pos.
    - exact (x1_kl_term_expand (ListDef.nth i tokens real_zero)
               (tokens_pos i)). }
  assert (Hstep : real_eq (real_list_sum nat
      (fun i => real_kl_term (x1_tf (ListDef.nth i tokens real_zero)) U
                 (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
      (ListDef.seq 0%nat N))
    (real_plus LN (real_opp S))).
  { apply (real_eq_trans _
             (real_list_sum nat
                (fun i => real_plus
                            (real_mult (ListDef.nth i tokens real_zero) LN)
                            (real_opp (um_ent_term
                                         (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))))
                (ListDef.seq 0%nat N))).
    - apply (x1_seq_ext N
               (fun i => real_kl_term
                           (x1_tf (ListDef.nth i tokens real_zero)) U
                           (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
               (fun i => real_plus
                            (real_mult (ListDef.nth i tokens real_zero) LN)
                            (real_opp (um_ent_term
                                         (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))))).
      intro i. intro Hj. apply Hpt. exact Hj.
    - apply (real_eq_trans _
               (real_plus
                  (real_list_sum nat
                     (fun i => real_mult (ListDef.nth i tokens real_zero) LN)
                     (ListDef.seq 0%nat N))
                  (real_list_sum nat
                     (fun i => real_opp (um_ent_term
                                          (ListDef.nth i tokens real_zero)
                                          (tokens_pos i)))
                     (ListDef.seq 0%nat N)))).
      + apply real_list_sum_add.
      + apply (real_eq_trans _
                 (real_plus LN
                    (real_opp (real_list_sum nat
                       (fun i => um_ent_term
                                   (ListDef.nth i tokens real_zero)
                                   (tokens_pos i))
                       (ListDef.seq 0%nat N))))).
        * apply RealSetoid.real_eq_plus_compat.
          -- apply (real_eq_trans _
                       (real_mult LN (real_list_sum nat
                          (fun i => ListDef.nth i tokens real_zero)
                          (ListDef.seq 0%nat N)))).
             ++ apply real_list_sum_linear_r.
             ++ apply (real_eq_trans _ (real_mult LN real_one)).
                ** apply RealSetoid.real_eq_mult_compat.
                   --- apply real_eq_refl.
                   --- (* X1b：此位须 Σ nth==1（非 tf 版 Hnormp）；经 um_seq_nth_sum
                          与 tokens_sum 现场重造 *)
                      apply (real_eq_trans _
                                 (real_list_sum Real
                                    (fun x : Real => x) tokens)).
                      ++++ apply um_seq_nth_sum.
                      ++++ exact tokens_sum.
                ** apply real_mult_one.
        -- exact (real_list_sum_opp nat
                   (fun i => um_ent_term (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))
                   (ListDef.seq 0%nat N)).
        * (* X1b：(b2) M2 == LN+opp(S)：um_entropy 定义性展开下反射闭合 *)
          apply real_eq_refl. }
  assert (Hg2 : real_le real_zero
                  (real_plus (real_plus LN (real_opp S)) eps)).
  { apply (RealSetoid.real_le_id_r real_zero
             (real_plus (real_list_sum nat
                (fun i => real_kl_term
                            (x1_tf (ListDef.nth i tokens real_zero)) U
                            (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
                (ListDef.seq 0%nat N)) eps)
             (real_plus (real_plus LN (real_opp S)) eps)).
    - (* X1b：id_r 位序 = 先 eq 后 le（原稿反序） *)
      apply RealSetoid.real_eq_plus_compat.
      + exact Hstep.
      + apply real_eq_refl.
    - exact Hg. }
  (* X1b：(LN−S)+S == LN（assoc + comm + plus_opp 三步；eq 位消 S 的核） *)
  assert (HSL : real_eq (real_plus (real_plus LN (real_opp S)) S) LN).
  { apply (real_eq_trans _ (real_plus LN (real_plus (real_opp S) S))).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus LN real_zero)).
      + apply RealSetoid.real_eq_plus_compat.
        * apply real_eq_refl.
        * apply (real_eq_trans _ (real_plus S (real_opp S))).
          -- apply real_plus_comm.
          -- apply real_plus_opp.
      + apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l S (real_plus real_zero S)
           (real_plus LN eps)).
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus S real_zero)).
    + apply real_plus_comm.
    + apply real_plus_zero.
  - apply (RealSetoid.real_le_id_r (real_plus real_zero S)
             (real_plus (real_plus (real_plus LN (real_opp S)) eps) S)
             (real_plus LN eps)).
    + (* X1b：id_r 位序 = 先 eq 后 le；eq 位把 S 搬入内层经 HSL 消去 *)
      apply (real_eq_trans _
               (real_plus (real_plus LN (real_opp S)) (real_plus eps S))).
      * apply real_eq_sym. apply real_plus_assoc.
      * apply (real_eq_trans _
               (real_plus (real_plus LN (real_opp S)) (real_plus S eps))).
        -- apply RealSetoid.real_eq_plus_compat.
           ++ apply real_eq_refl.
           ++ apply real_plus_comm.
        -- apply (real_eq_trans _
                     (real_plus (real_plus (real_plus LN (real_opp S)) S) eps)).
           ++ apply real_plus_assoc.
           ++ apply RealSetoid.real_eq_plus_compat.
              ** exact HSL.
              ** apply real_eq_refl.
    + apply real_le_plus_compat.
      * exact Hg2.
      * apply real_le_refl.
Qed.

(*   消解剖面：0<d（d:=S+(−LN)）→ inv2<1（real_inv_pos_lt_contra）  *)
(*     → d·inv2<d（real_lt_mult_compat）→ LN+d·inv2<LN+d            *)
(*     （real_lt_plus_compat_le_lt）→ real_lt_trans（S02 L463）完成  *)

(* [6] 闭形：S ≤ log N（逐 eps 形经三分判定器 + 半隙完成） *)
Theorem x1_entropy_le_log_N : real_le S LN.
Proof.
  destruct (trich S LN) as [Hle | Hgt].
  - (* inl 支：S ≤ LN 即结论 *)
    exact Hle.
  - (* inr 支：LN < S 导矛盾（d := S+(−LN)，eps := d·inv 2） *)
    assert (H2pos : real_lt real_zero (real_plus real_one real_one)).
    { (* (0+0) < (1+1) 重述为 0 < 1+1 *)
      apply (RealSetoid.real_lt_compat (real_plus real_zero real_zero) real_zero
               (real_plus real_one real_one) (real_plus real_one real_one)).
      - apply real_plus_zero.
      - apply real_eq_refl.
      - (* (0+0) < (1+1)：两跳（0+0 < 0+1 < 1+1） *)
        apply (real_lt_trans (real_plus real_zero real_zero)
                 (real_plus real_zero real_one) (real_plus real_one real_one)).
        + exact (real_lt_plus_translate real_zero real_zero real_one
                   real_lt_zero_one).
        + exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
                   real_lt_zero_one (real_le_refl real_one)). }
    assert (Hinv2pos : real_lt real_zero
             (real_inv_pos (real_plus real_one real_one) H2pos)).
    { exact (real_inv_pos_pos (real_plus real_one real_one) H2pos). }
    assert (Hd : real_lt real_zero (real_plus S (real_opp LN))).
    { (* −S < −LN ⟹ (−S)+S < (−LN)+S ⟹ 重述 0 < S+(−LN) *)
      apply (RealSetoid.real_lt_compat (real_plus (real_opp S) S) real_zero
               (real_plus (real_opp LN) S) (real_plus S (real_opp LN))).
      - apply (real_eq_trans _ (real_plus S (real_opp S))).
        + apply real_plus_comm.
        + apply real_plus_opp.
      - apply real_plus_comm.
      - exact (real_lt_plus_compat_lt_le (real_opp S) (real_opp LN) S S
                 (real_opp_lt_compat LN S Hgt) (real_le_refl S)). }
    assert (H12 : real_lt real_one (real_plus real_one real_one)).
    { (* (0+1) < (1+1) 经 real_lt_compat 重述 0+1→1 *)
      apply (RealSetoid.real_lt_compat (real_plus real_zero real_one) real_one
               (real_plus real_one real_one) (real_plus real_one real_one)).
      - apply (real_eq_trans _ (real_plus real_one real_zero)).
        + apply real_plus_comm.
        + apply real_plus_zero.
      - apply real_eq_refl.
      - exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
                 real_lt_zero_one (real_le_refl real_one)). }
    assert (Hinv2lt1 : real_lt
             (real_inv_pos (real_plus real_one real_one) H2pos) real_one).
    { (* inv 2 < inv 1（real_inv_pos_lt_contra）经 inv1==1 重述 *)
      apply (RealSetoid.real_lt_compat
               (real_inv_pos (real_plus real_one real_one) H2pos)
               (real_inv_pos (real_plus real_one real_one) H2pos)
               (real_inv_pos real_one real_lt_zero_one) real_one).
      - apply real_eq_refl.
      - exact real_inv_one.
      - exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one)
                 real_lt_zero_one H2pos H12). }
    assert (Hdlt : real_lt
             (real_mult (real_plus S (real_opp LN))
                (real_inv_pos (real_plus real_one real_one) H2pos))
             (real_plus S (real_opp LN))).
    { (* d·inv2 < d·1（real_lt_mult_compat）经 d·1==d 重述 *)
      apply (RealSetoid.real_lt_compat
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_mult (real_plus S (real_opp LN)) real_one)
               (real_plus S (real_opp LN))).
      - apply real_eq_refl.
      - apply real_mult_one.
      - exact (real_lt_mult_compat
                 (real_inv_pos (real_plus real_one real_one) H2pos) real_one
                 (real_plus S (real_opp LN)) Hd Hinv2lt1). }
    assert (HLTN : real_lt
             (real_plus LN
                (real_mult (real_plus S (real_opp LN))
                   (real_inv_pos (real_plus real_one real_one) H2pos)))
             (real_plus LN (real_plus S (real_opp LN)))).
    { exact (real_lt_plus_compat_le_lt LN LN
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_plus S (real_opp LN))
               (real_le_refl LN) Hdlt). }
    assert (HdS : real_eq (real_plus LN (real_plus S (real_opp LN))) S).
    { (* LN+(S+(−LN)) == S：assoc/comm/plus_opp/plus_zero（同 HSL 手法） *)
      apply (real_eq_trans _ (real_plus (real_plus LN S) (real_opp LN))).
      - apply real_plus_assoc.
      - apply (real_eq_trans _ (real_plus (real_plus S LN) (real_opp LN))).
        + apply RealSetoid.real_eq_plus_compat.
          * apply real_plus_comm.
          * apply real_eq_refl.
        + apply (real_eq_trans _ (real_plus S (real_plus LN (real_opp LN)))).
          * apply real_eq_sym. apply real_plus_assoc.
          * apply (real_eq_trans _ (real_plus S real_zero)).
            -- apply RealSetoid.real_eq_plus_compat.
               ++ apply real_eq_refl.
               ++ apply real_plus_opp.
            -- apply real_plus_zero. }
    assert (HLTS : real_lt
             (real_plus LN
                (real_mult (real_plus S (real_opp LN))
                   (real_inv_pos (real_plus real_one real_one) H2pos))) S).
    { apply (RealSetoid.real_lt_compat
               (real_plus LN
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)))
               (real_plus LN
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)))
               (real_plus LN (real_plus S (real_opp LN))) S).
      - apply real_eq_refl.
      - exact HdS.
      - exact HLTN. }
    pose proof (x1_entropy_le_log_N_eps
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos))
                  (real_mult_positive (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)
                     Hd Hinv2pos)) as Hle2.
    unfold real_le in Hle2.
    destruct Hle2 as [Hlt2 | Heq2].
    + (* lt 支：S < LN+d·inv2 < S ⟹ S < S ⟹ 完成 *)
      assert (HSS : real_lt S S).
      { exact (real_lt_trans S
                 (real_plus LN
                    (real_mult (real_plus S (real_opp LN))
                       (real_inv_pos (real_plus real_one real_one) H2pos)))
                 S Hlt2 HLTS). }
      destruct (real_lt_irrefl S HSS).
    + (* eq 支：S == LN+d·inv2 < S ⟹ S < S ⟹ 完成 *)
      assert (HSS : real_lt S S).
      { exact (real_eq_lt_lt S
                 (real_plus LN
                    (real_mult (real_plus S (real_opp LN))
                       (real_inv_pos (real_plus real_one real_one) H2pos)))
                 S Heq2 HLTS). }
      destruct (real_lt_irrefl S HSS).
Qed.

(* [7] 复合件一：KL ≤ log N（KL ≤ S 与 S ≤ log N 直连） *)
Theorem x1_kl_le_log_N : real_le x1_KL LN.
Proof.
  exact (real_le_trans x1_KL S LN x1_kl_le_entropy x1_entropy_le_log_N).
Qed.

(* [7] 复合件二：复合熵链合取形（S01 And := A*B，Set 层） *)
Definition x1_composite_chain :
  And (real_le x1_KL S) (real_le S LN) :=
  (x1_kl_le_entropy, x1_entropy_le_log_N).

End X1MinPKLChain.
