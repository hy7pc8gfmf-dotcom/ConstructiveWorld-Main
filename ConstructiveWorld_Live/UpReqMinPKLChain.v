(* UpReqMinPKLChain.v *)
(* 使命： 复合熵链的一步拼装（Min-P KL 链）。 *)
(* 主件： x1_KL 与 x1_minp_kernel / x1_Zaud_pos_cert：KL 链的显式组装件。 *)
(* 依赖： CW_ConstructiveWorld_219、UpMinP。 *)
(* 备注： 三分性判定器显式随行；零公理面、零经典逻辑（纯构造）。 *)
(* 构造性注记：Set 层承载、零承认、可提取。 *)
(* 编译配方：rocq 9.1 直调 + cpu_guard。 *)
(* UpReqMinPKLChain.v —— 复合熵链一步拼装 *)
(*   KL(minp‖full) ≤ S ≤ log|S|   （论文 2 正式版 §10.2 第 6 项）  *)
(* 拼装件（全在盘，只读使用）：                                   *)
(*                   real_Z_aud_is_kept_mass（Z_aud == 保留质量）  *)
(*   UpMinP        : dropped_le_one_minus_exp_neg_S（dropped ≤ 1−e^−S）*)
(*                   um_log_le_mono / um_fmax 族 / um_rls 族 / um_seq 族 *)
(*   根   : real_gibbs_inequality_eps（Gibbs ≥ 0 逐 eps） *)
(*                   real_log_mult / real_inv_unique / real_le_antisym *)
(* 链结构（各步引用件名）：                                       *)
(*   [2] real_Z_aud_is_kept_mass + x1_sum_list_seq + x1_seq_ext   *)
(*       + x1_inv_of_Zfull ⟹ Z_aud == um_kept                    *)
(*   [3] dropped_le_one_minus_exp_neg_S + x1_plus_opp_cancel      *)
(*       ⟹ e^−S ≤ kept（kept == 1 − dropped 互补恒等）            *)
(*   [4] um_log_le_mono + log_inv_exp_neg_thm ⟹ KL ≤ S            *)
(*       ⟹ S ≤ log N + eps（逐 eps 形）                           *)
(*   [6] 三分判定器 + 半隙完成 ⟹ S ≤ log N（闭形）                  *)
(*   [7] real_le_trans ⟹ KL ≤ log N 与合取形复合链                 *)
(* 世界：UpMinP 概率表世界（tokens : list Real，逐项正、和 == 1，   *)
(* ratio ∈ (0,1]，三分判定器 trich 随行）；UpAuditBridge 抽象 Min-P   *)
(* 机器在 (Real, tokens, x1_tf, x1_keep, x1_keep_dec) 上实例化。    *)
(* 纪律：零公理、零搁置、零经典（纯构造，三分判定器显式随行）；        *)
(*       语句全 Set 层；全 Qed 闭合；um_/x1_ 前缀防遮蔽。           *)

Require Import CW_ConstructiveWorld_219.
Require Import UpMinP UpAuditBridge.
From Stdlib Require Import List Arith Lia.
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

(* ============================================================ *)
(* 0. 通用小桥（本文件自建）                                     *)
(* ============================================================ *)

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
        * (* X1b R1：该 trans 两端本就同一项——refl 直接闭合
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
    + (* X1b：assoc 本朝向即 `x+(y+z) == (x+y)+z`（S02 L2333），直放即可 *)
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

(* ============================================================ *)
(* 1. 审计桥实例（UpAuditBridge 在概率表世界上消解）              *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 2. 主件一：KL(minp‖full) ≤ S                                 *)
(* ============================================================ *)

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
(*   lt_le_trans 证书收敛为 x1_K_pos（R5 收缩）。                              *)

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

(* ============================================================ *)
(* 3. 主件二：S ≤ log|S|（Gibbs 于均匀 + 逐 eps 余量）            *)
(* ============================================================ *)

Lemma x1_N_pos : real_lt real_zero (um_nreal N).
Proof.
  (* X1b：um_Npos（UpMinP L847，语句仅依赖 tokens）直接消解——
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

(* ============================================================ *)
(* R4：闭形 + 复合件                                                    *)
(*   消解剖面：0<d（d:=S+(−LN)）→ inv2<1（real_inv_pos_lt_contra）  *)
(*     → d·inv2<d（real_lt_mult_compat）→ LN+d·inv2<LN+d            *)
(*     （real_lt_plus_compat_le_lt）→ real_lt_trans（S02 L463）完成  *)
(* ============================================================ *)

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
