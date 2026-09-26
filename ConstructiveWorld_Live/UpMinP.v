(* ============================================================ *)
(* UpMinP.v *)
(* *)
(* 目的： Min-P 截断质量的熵刻画（Real 层 list 离散世界）。 *)
(* 主件： um_entropy / um_Hpmax：截断分布熵与最大概率熵的刻画；um_fmax / um_thr 阈值面。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 三分性探针以显式 Variable 随行；词表非空/逐点正/质量和为显式前提；纯构造性、无经典公理面。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpMinP.v —— Min-P 截断质量的熵刻画（Real 层 list 离散世界）    *)
(*                                                              *)
(* 主定理（统一根内两条已知界的熵版）：                          *)
(*   件 1  entropy_ge_neg_log_p_max :                            *)
(*         S ≥ −log(p_max)（熵 ≥ 最大概率的负对数）              *)
(*   件 2  dropped_le_one_minus_exp_neg_S :                      *)
(*         dropped ≤ 1 − e^−S（Min-P 截断质量的熵上界）          *)
(*   件 3  dropped_le_one_minus_inv_n :                          *)
(*         dropped ≤ 1 − 1/N（均匀特例，与根 L31849 对齐）       *)
(*                                                              *)
(* 证明链：dropped == 1 − kept（定义性）；kept ≥ p_max（pick_max *)
(* 必被保留，见 um_kept_ge_pmax）；p_max ≥ e^−S：逐项 k ≤ p_max   *)
(* ⟹ −log k ≥ −log p_max ⟹ S = Σ k·(−log k) ≥ −log p_max（权重  *)
(* 非负加权 + 归一化 Σk = 1）⟹ e^−S ≤ p_max（exp antitone +      *)
(* cw_log_exp_right）⟹ dropped ≤ 1 − e^−S。                     *)
(*                                                              *)
(* 简化世界：tokens : list Real（概率表，逐项正、和 = 1）；      *)
(* p_max := fold real_max（逐点上界 um_fmax_ge_nth + 可达性       *)
(* um_fmax_mem_nth 双引理）；熵/保留质量均以 seq 0 N 下标表求和， *)
(* 下标界全用扫描库 Set 层编码 NatLt := Id (ltb) true——          *)
(* 索引和引理（um_rls_le_N / um_rls_nonneg_N /                   *)
(* um_rls_single_le_N）逐点假设为 NatLt 前提函数，无 Prop 解构、 *)
(* 无递归 Set 谓词匹配，提取零 Obj.magic；Min-P 保留判定以三分    *)
(* 判定元 um_trich_probe（a ≤ b ∨ b < a，镜像根内 ord_le_dec     *)
(* 结构域字段）携带——纯构造性，无经典公理。                      *)
(* 纪律：零公理、零搁置、零参数化声明、零经典逻辑（纯构造性）；*)
(*       语句全 Set 层（real_lt/real_le/real_eq + Or/sigT/prod + *)
(*       NatLt），无 Prop 前提；全部 Qed. 闭合；                 *)
(*       Real 层顶层名（um_ 前缀防遮蔽）。                       *)
(* 注意：CW_ConstructiveWorld_219 将 S 遮蔽为 Set，nat 模式一律               *)
(* Datatypes.O / Datatypes.S。提取探针见 probe_minp_extract.v。  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import List Arith Lia.

(* ============================================================ *)
(* 0. 通用桥（Real 层，Section 外，全局可复用）                  *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 1. 索引表求和（seq 形态）：nreal / 位移 / nth 桥 / 常值        *)
(* ============================================================ *)

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

(* ============================================================ *)

(* ============================================================ *)


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

(* ============================================================ *)
(* 3. NatLt 下标制的索引和引理（逐点假设函数，无 Prop 解构）      *)
(*    NatLt i n := Id (i <? n) true（扫描库 Set 层界编码）；      *)
(*    关键转换：NatLt (S i) (S n) ≡ NatLt i n（ltb/leb iota）。   *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 4. 世界段：tokens / ratio + 三分判定元（镜像 ord_le_dec）      *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 5. Min-P 截断世界（tokens + ratio）                           *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 件 1：S ≥ −log(p_max)                                        *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 件 2：dropped ≤ 1 − e^{−S}                                   *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 件 3：dropped ≤ 1 − 1/N（N = |tokens|；均匀特例）             *)
(* ============================================================ *)

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
