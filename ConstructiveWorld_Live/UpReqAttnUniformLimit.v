(* ============================================================ *)
(* UpReqAttnUniformLimit.v —— 本件形式化并列最大值注意力温度极限的        *)
(*   L1 收敛性质：对任意 eps>0 存在 T₀>0，使任意 T(0<T<T₀) 满足           *)
(*   L1(w_T, u) ≤ eps，其中 u 为副本上的均匀分布。                       *)
(*                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219（伞壳）、AttnHardLimit218。         *)
(*                                                              *)
(* 构造性注记：Set 层承载/零承认/可提取；Q 层并列间隙证书、副本均匀       *)
(*   目标分布与 m-开关求和恒等式全构造性；词表非空位与 token 可判定       *)
(*   相等位的 Set 重述与具体层供给见文尾节。                             *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流。                             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import AttnHardLimit218.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import QArith.QArith QArith.Qring.
Import ListNotations.

(* ============================================================ *)
(* Part 1：Q 层并列间隙证书（可判定枚举，全构造性）            *)
(* ============================================================ *)

(* 非空表极大值：以首元为累加基，避免 0-基在负值表上的假极大 *)
(* 本安装无 Qorder/Qle_dec：以 Qle_bool 为可判定比较基座，自建双桥 *)
Lemma alm_qleb_true : forall a b : Q, Qle_bool a b = true -> Qle a b.
Proof.
  intros a b H. apply Qle_bool_iff. exact H.
Qed.

Lemma alm_qleb_false : forall a b : Q, Qle_bool a b = false -> Qlt b a.
Proof.
  intros a b H. apply Qnot_le_lt.
  destruct (Qle_bool_iff a b) as [_ Hb]. intro Hle.
  apply Hb in Hle. rewrite H in Hle. discriminate Hle.
Qed.

(* 实测核对：本安装 Qorder 缺席——Qplus_lt_compat_r/Qeq_lt/Qlt_refl
   全无；以 Qplus_le_l（iff 形右消去）+Qlt_irrefl+Qlt_le_trans 自建
   单侧严格单调桥，兼作 Qeq_lt 替代面（ witness 严格支用）。 *)
Lemma alm_qlt_compat_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros x y z Hxy.
  apply (Qnot_le_lt (y + z)%Q (x + z)%Q).
  intro Hle.
  assert (Hyx : Qle y x) by exact (proj1 (Qplus_le_l y x z) Hle).
  exact (Qlt_irrefl x (Qlt_le_trans x y x Hxy Hyx)).
Qed.

Fixpoint alm_max_ne (q : Q) (tab : list Q) : Q :=
  match tab with
  | nil => q
  | y :: r =>
      match Qle_bool q (alm_max_ne y r) with
      | true => alm_max_ne y r
      | false => q
      end
  end.

Lemma alm_max_ne_ub : forall (tab : list Q) (q x : Q),
  In x (q :: tab) -> Qle x (alm_max_ne q tab).
Proof.
  intros tab. induction tab as [| y rest IH]; intros q x Hin.
  - destruct Hin as [Heq | Hin'].
    + subst. apply Qle_refl.
    + destruct Hin'.
  - cbn [alm_max_ne].
    destruct (Qle_bool q (alm_max_ne y rest)) eqn:Hd.
    + inversion Hin as [Heq | Hin']; subst.
      * exact (alm_qleb_true _ _ Hd).
      * exact (IH y x Hin').
    + inversion Hin as [Heq | Hin'].
      * rewrite <- Heq. apply Qle_refl.
      * apply Qlt_le_weak.
        apply (Qle_lt_trans x (alm_max_ne y rest) q).
        -- exact (IH y x Hin').
        -- exact (alm_qleb_false _ _ Hd).
Qed.

Lemma alm_max_ne_in : forall (tab : list Q) (q : Q),
  In (alm_max_ne q tab) (q :: tab).
Proof.
  intros tab. induction tab as [| y rest IH]; intro q.
  - apply in_eq.
  - cbn [alm_max_ne].
    destruct (Qle_bool q (alm_max_ne y rest)).
    + apply in_cons. exact (IH y).
    + apply in_eq.
Qed.

Lemma alm_qeqb_false : forall a b : Q, Qeq_bool a b = false -> ~ (a == b).
Proof.
  intros a b H Heq.
  destruct (Qeq_bool_iff a b) as [_ Hb].
  specialize (Hb Heq). rewrite Hb in H. discriminate H.
Qed.

(* 下滤极大值：表中与 qmax 不同的元素之极大（option 型，零 filter 依赖） *)
Fixpoint alm_below_max (qmax : Q) (tab : list Q) : option Q :=
  match tab with
  | nil => None
  | y :: r =>
      match Qeq_bool y qmax with
      | true => alm_below_max qmax r
      | false =>
          match alm_below_max qmax r with
          | None => Some y
          | Some m => if Qle_bool y m then Some m else Some y
          end
      end
  end.

(* P2：下滤极大为 None ⟹ 全表同值 *)
Lemma alm_below_max_none : forall tab qmax q,
  In q tab -> alm_below_max qmax tab = None -> q == qmax.
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax q Hin H.
  - exact (match Hin with end).
  - revert H. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy; simpl.
    + inversion Hin as [Heq | Hin']; subst.
      * intro H. apply Qeq_bool_eq. exact Hy.
      * intro H. exact (IH qmax q Hin' H).
    + intro H. destruct (alm_below_max qmax rest) as [m' |].
      * destruct (Qle_bool y m'); discriminate H.
      * discriminate H.
Qed.

(* P1a：下滤极大 = Some m ⟹ m 在表中且 m ≠ qmax *)
Lemma alm_below_max_in : forall tab qmax m,
  alm_below_max qmax tab = Some m ->
  And (In m tab) (~ (m == qmax)).
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax m H.
  - discriminate H.
  - revert H. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy; simpl.
    + intros H. destruct (IH qmax m H) as [Hin Hne].
      split.
      * apply in_cons. exact Hin.
      * exact Hne.
    + destruct (alm_below_max qmax rest) as [m' |] eqn:Hr.
      * destruct (Qle_bool y m') eqn:Hyle.
        -- simpl. intros H. inversion H. subst.
           destruct (IH qmax m Hr) as [Hinm Hne].
           split.
           ++ apply in_cons. exact Hinm.
           ++ exact Hne.
        -- simpl. intros H. inversion H. subst.
           split.
           ++ apply in_eq.
           ++ exact (alm_qeqb_false _ _ Hy).
      * intros H. inversion H. subst.
        split.
        ++ apply in_eq.
        ++ exact (alm_qeqb_false _ _ Hy).
Qed.

(* P1b：下滤极大 = Some m ⟹ 表中任一非 qmax 元素 ≤ m *)
Lemma alm_below_max_ub : forall tab qmax m q,
  In q tab -> alm_below_max qmax tab = Some m ->
  ~ (q == qmax) -> Qle q m.
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax m q Hin H Hne.
  - exact (match Hin with end).
  - revert Hin H Hne. revert q. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy.
    + simpl. intros q Hin H Hne.
      inversion Hin as [Heq | Hin']; subst.
      * exact (match Hne (Qeq_bool_eq _ _ Hy) with end).
      * exact (IH qmax m q Hin' H Hne).
    + simpl. destruct (alm_below_max qmax rest) as [m' |] eqn:Hr.
      * assert (IH' : forall q : Q,
            In q rest -> alm_below_max qmax rest = Some m' ->
            ~ (q == qmax) -> Qle q m')
          by exact (IH qmax m').
        destruct (Qle_bool y m') eqn:Hyle.
        -- simpl. intros q Hin H Hne. inversion H. subst.
           destruct Hin as [Heq | Hin']; subst.
           ++ exact (alm_qleb_true _ _ Hyle).
           ++ exact (IH' q Hin' Hr Hne).
        -- simpl. intros q Hin H Hne. inversion H. subst.
           destruct Hin as [Heq | Hin']; subst.
           ++ apply Qle_refl.
           ++ apply (Qle_trans q m' m).
              ** exact (IH' q Hin' Hr Hne).
              ** apply Qlt_le_weak. exact (alm_qleb_false _ _ Hyle).
      * simpl. intros q Hin H Hne. inversion H. subst.
        destruct Hin as [Heq | Hin']; subst.
        ++ apply Qle_refl.
        ++ exact (match Hne (alm_below_max_none _ _ _ Hin' Hr) with end).
Qed.


(* 主件：并列间隙证书（Q 层可判定枚举，全构造性） *)
Theorem alm_gap_witness : forall (q0 : Q) (rest : list Q),
  sigT (fun qmax => sigT (fun k => sigT (fun g =>
    And (In qmax (q0 :: rest))
    (And ((1 <= k)%nat)
    (And (forall q : Q, In q (q0 :: rest) -> Qle q qmax)
         (sum (forall q : Q, In q (q0 :: rest) -> q == qmax)
              (And (Qlt 0%Q g)
                   (forall q : Q, In q (q0 :: rest) ->
                     Or (q == qmax) (Qle (q + g) qmax))))))))).
Proof.
  intros q0 rest.
  assert (Hqmaxin : In (alm_max_ne q0 rest) (q0 :: rest))
    by exact (alm_max_ne_in rest q0).
  assert (Hqmaxub : forall q : Q, In q (q0 :: rest) -> Qle q (alm_max_ne q0 rest))
    by exact (alm_max_ne_ub rest q0).
  destruct (alm_below_max (alm_max_ne q0 rest) (q0 :: rest)) as [mb |] eqn:Hbm.
  + (* 并列间隙支：g := qmax −（下滤极大） *)
    destruct (alm_below_max_in _ _ _ Hbm) as [Hmbin Hmbne].
    assert (Hltmb : Qlt mb (alm_max_ne q0 rest)).
    { destruct (Qle_lt_or_eq _ _ (Hqmaxub _ Hmbin)) as [Hlt | Heqq].
      - exact Hlt.
      - exfalso. apply Hmbne. exact Heqq. }
    exists (alm_max_ne q0 rest).
    exists (Datatypes.S (length (q0 :: rest))).
    exists (alm_max_ne q0 rest - mb)%Q.
    split; [exact Hqmaxin | ].
    split; [apply le_n_S; apply Nat.le_0_l | ].
    split; [exact Hqmaxub | ].
    right. split.
    * rewrite <- (Qplus_opp_r mb) at 1.
      apply (alm_qlt_compat_r mb (alm_max_ne q0 rest) (- mb)%Q).
      exact Hltmb.
    * intros q Hin. destruct (Qeq_dec q (alm_max_ne q0 rest)) as [Heqq | Hneqq].
      -- left. exact Heqq.
      -- right.
         assert (Hqle : Qle q mb)
           by exact (alm_below_max_ub _ _ _ q Hin Hbm Hneqq).
         unfold Qminus. lra.
  + (* 全表同值支（均匀退化档） *)
    exists (alm_max_ne q0 rest).
    exists (Datatypes.S (length (q0 :: rest))).
    exists 0%Q.
    split; [exact Hqmaxin | ].
    split; [apply le_n_S; apply Nat.le_0_l | ].
    split; [exact Hqmaxub | ].
    left. intros q Hin.
    exact (alm_below_max_none _ _ _ Hin Hbm).
Qed.

(* ============================================================ *)
(* Part 2：Real 层并列副本均匀极限——定义面与计算核             *)
(* ============================================================ *)

Section AlmUniform.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.

(* argmax 证物（不要求唯一：并列副本显式入模） *)
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* 副本多重数：m 在 vocab 中的出现次数（任意 ≥1，不再要求 ==1） *)
Definition alm_k : nat := count_token Token token_eq_dec m vocab.

Lemma alm_count_ge_one_aux : forall (t : Token) (l : list Token),
  InT t l -> (1 <= count_token Token token_eq_dec t l)%nat.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hin.
  - exact (match Hin with end).
  - cbn [count_token].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + apply le_n_S. apply Nat.le_0_l.
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact (match Hnyt id_refl with end).
      * exact (IH Hin2).
Qed.

Lemma alm_k_ge_one : (1 <= alm_k)%nat.
Proof.
  unfold alm_k. exact (alm_count_ge_one_aux m vocab m_in_vocab).
Qed.

Lemma alm_k_pos : real_lt real_zero (real_of_nat alm_k).
Proof.
  destruct alm_k as [| j] eqn:Hk.
  - exfalso.
    assert (Hc := alm_k_ge_one). rewrite Hk in Hc. inversion Hc.
  - apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat j))
             (real_of_nat (Datatypes.S j))).
    + apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat j))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* 每副本份：1/k *)
Definition alm_invk : Real :=
  real_inv_pos (real_of_nat alm_k) alm_k_pos.

(* 副本均匀目标：u(m)=1/k，u(非 m)=0 *)
Definition alm_uniform (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => alm_invk
  | inr _ => real_zero
  end.

(* m-开关函数：副本支 c1，非副本支 c2（求和恒等式的辅助引理） *)
Definition alm_switch (c1 c2 : Real) (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => c1
  | inr _ => c2
  end.

(* m-开关求和恒等式（极限定理的核心组合学，蓝图见头注）：
   Σ_vocab switch(c,g) = k·c + Σ_vocab switch(0,g)。
   证明：对 vocab 归纳，副本支用 real_distrib + of_nat(S)定义折叠，
   非副本支用 plus 交换/结合。——蓝图已由下列 swg_ 两件落成。 *)

(* —— 补编：m-开关求和恒等式蓝图落成（下两件 swg_）—— *)
(* 头注所述待续部分自本节起由下列 swg_ 两件给出。 *)
(* 对显式表 vl 归纳（不归纳 Section Variable：vocab 被 m_in_vocab 等钉死）。 *)
(* 基座核对（全数对上零漂移）：real_list_sum/
   real_of_nat（S08，O↦0、S n↦1+of_nat n 定义折叠）、real_eq_refl/sym/trans、
   real_plus_comm/assoc/zero、real_mult_zero/one、real_distrib（S02）、
   real_distrib_r（S09）、RealSetoid.real_eq_plus_compat（S07）。 *)
(* real_eq 为 Set 层等词（基库 :3448），两件语句面零 Prop 前提，红线②安全。 *)

Lemma swg_switch_sum_gen : forall (c g : Real) (vl : list Token),
  real_eq (real_list_sum Token (alm_switch c g) vl)
    (real_plus
       (real_mult (real_of_nat (count_token Token token_eq_dec m vl)) c)
       (real_list_sum Token (alm_switch real_zero g) vl)).
Proof.
  intros c g vl. induction vl as [| y rest IH].
  - (* 空表：0 == 0·c + 0（real_of_nat O ≡ real_zero 定义折叠） *)
    cbn [real_list_sum count_token alm_switch real_of_nat].
    apply (real_eq_trans _ (real_plus real_zero real_zero) _).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero real_zero
               (real_mult real_zero c) real_zero).
      * apply (real_eq_trans _ (real_mult c real_zero) _).
        -- apply (real_eq_sym (real_mult c real_zero) real_zero).
           apply (real_mult_zero c).
        -- apply (real_mult_comm c real_zero).
      * apply real_eq_refl.
  - cbn [real_list_sum count_token]. unfold alm_switch.
    destruct (token_eq_dec y m) as [Hym | Hnym].
    + (* 副本支：of_nat(S k) ≡ 1 + of_nat k 定义折叠；
         核 = (1+a)·c == c + a·c（右分配 + 左幺元经交换桥） *)
      cbn [real_of_nat].
      assert (Hcore : real_eq
                (real_mult (real_plus real_one
                              (real_of_nat
                                 (count_token Token token_eq_dec m rest))) c)
                (real_plus c
                   (real_mult (real_of_nat
                                 (count_token Token token_eq_dec m rest)) c))).
      { apply (real_eq_trans _
            (real_plus (real_mult real_one c)
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)) _).
        - apply (real_eq_sym
              (real_plus (real_mult real_one c)
                         (real_mult
                            (real_of_nat
                               (count_token Token token_eq_dec m rest)) c))
              (real_mult (real_plus real_one
                            (real_of_nat
                               (count_token Token token_eq_dec m rest))) c)).
          apply (real_distrib_r real_one
                   (real_of_nat (count_token Token token_eq_dec m rest)) c).
        - apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)
                   c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)).
          + apply (real_eq_trans _ (real_mult c real_one) _).
            * apply (real_mult_comm real_one c).
            * apply (real_mult_one c).
          + apply real_eq_refl. }
      apply (real_eq_trans _
        (real_plus c
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alm_switch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_list_sum Token (alm_switch c g) rest) c
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus c
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alm_switch real_zero g) rest)) _).
        -- apply (real_plus_assoc c
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c))
                (real_plus real_zero
                   (real_list_sum Token (alm_switch real_zero g) rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alm_switch real_zero g) rest)
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym
                         (real_plus real_zero
                            (real_list_sum Token (alm_switch real_zero g)
                               rest))
                         (real_list_sum Token (alm_switch real_zero g)
                            rest)).
                 apply (real_eq_trans _
                           (real_plus
                              (real_list_sum Token (alm_switch real_zero g)
                                 rest) real_zero) _).
                 apply (real_plus_comm real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
                 apply (real_plus_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))
                       (real_mult
                          (real_plus real_one
                             (real_of_nat
                                (count_token Token token_eq_dec m rest))) c)
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))).
              ** apply (real_eq_sym
                          (real_mult
                             (real_plus real_one
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest)))
                             c)
                          (real_plus c
                             (real_mult
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest))
                                c))).
                 exact Hcore.
              ** apply real_eq_refl.
    + (* 非副本支：IH + assoc + comm 拼中项交换 *)
      apply (real_eq_trans _
        (real_plus g
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alm_switch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat g
                 (real_list_sum Token (alm_switch c g) rest) g
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus g
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alm_switch real_zero g) rest)) _).
        -- apply (real_plus_assoc g
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c) g)
                (real_list_sum Token (alm_switch real_zero g) rest)) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus g
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alm_switch real_zero g) rest)
                       (real_plus
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          g)
                       (real_list_sum Token (alm_switch real_zero g) rest)).
              ** apply (real_plus_comm g
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)).
              ** apply real_eq_refl.
           ++ apply (real_eq_sym
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_plus g
                       (real_list_sum Token (alm_switch real_zero g)
                          rest)))
                 (real_plus
                    (real_plus
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c) g)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
              ** apply (real_plus_assoc
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          g
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
Qed.

(* 闭合引理：以 vocab 实例化（alm_k 即 count_token m vocab） *)
Lemma swg_switch_sum : forall c g : Real,
  real_eq (real_list_sum Token (alm_switch c g) vocab)
    (real_plus (real_mult (real_of_nat alm_k) c)
               (real_list_sum Token (alm_switch real_zero g) vocab)).
Proof.
  intros c g. unfold alm_k.
  apply (swg_switch_sum_gen c g vocab).
Qed.

End AlmUniform.

Section AluChain.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* 硬注意力权重缩写（post-End w_T 五参直引，delta 透明） *)
Definition alu_w (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  w_T Token vocab vocab_nonempty z T Ht x.

(* 函数形 m-开关：副本支取常量 c，非副本支取 g x（c : Real 常量参数位 +  *)
(* g : Token -> Real 函数参数位——上游 alm_switch 双常量参数位的函数形补全） *)
Definition alu_mswitch (c : Real) (g : Token -> Real) (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => c
  | inr _ => g x
  end.

(* 非 m 副本质量 M：switch(0, w_T) 的 vocab 和（上游蓝图 §1 的 M） *)
Definition alu_M (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Token (alu_mswitch real_zero (alu_w T Ht)) vocab.

(* ---------- 函数形 m-开关求和恒等式（上游原证明骨架逐行转录） ---------- *)
(* Σ alu_mswitch c g == count(m)·c + Σ alu_mswitch 0 g（对显式表 vl 归纳： *)
(* 空表零元代数 / 副本支 of_nat(S) 定义折叠+右分配+左幺元交换桥 /          *)
(* 非副本支中项交换。g 为函数形（对上游常量 g 版的形参补全）。         *)

Lemma alu_switch_sum_fun : forall (c : Real) (g : Token -> Real) (vl : list Token),
  real_eq (real_list_sum Token (alu_mswitch c g) vl)
    (real_plus
       (real_mult (real_of_nat (count_token Token token_eq_dec m vl)) c)
       (real_list_sum Token (alu_mswitch real_zero g) vl)).
Proof.
  intros c g vl. induction vl as [| y rest IH].
  - (* 空表：0 == 0·c + 0（real_of_nat O ≡ real_zero 定义折叠） *)
    cbn [real_list_sum count_token real_of_nat].
    apply (real_eq_trans _ (real_plus real_zero real_zero) _).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero real_zero
               (real_mult real_zero c) real_zero).
      * apply (real_eq_trans _ (real_mult c real_zero) _).
        -- apply (real_eq_sym (real_mult c real_zero) real_zero).
           apply (real_mult_zero c).
        -- apply (real_mult_comm c real_zero).
      * apply real_eq_refl.
  - cbn [real_list_sum count_token]. unfold alu_mswitch.
    destruct (token_eq_dec y m) as [Hym | Hnym].
    + (* 副本支：of_nat(S k) ≡ 1 + of_nat k 定义折叠；
         核 = (1+a)·c == c + a·c（右分配 + 左幺元经交换桥） *)
      cbn [real_of_nat].
      assert (Hcore : real_eq
                (real_mult (real_plus real_one
                              (real_of_nat
                                 (count_token Token token_eq_dec m rest))) c)
                (real_plus c
                   (real_mult (real_of_nat
                                 (count_token Token token_eq_dec m rest)) c))).
      { apply (real_eq_trans _
            (real_plus (real_mult real_one c)
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)) _).
        - apply (real_eq_sym
              (real_plus (real_mult real_one c)
                         (real_mult
                            (real_of_nat
                               (count_token Token token_eq_dec m rest)) c))
              (real_mult (real_plus real_one
                            (real_of_nat
                               (count_token Token token_eq_dec m rest))) c)).
          apply (real_distrib_r real_one
                   (real_of_nat (count_token Token token_eq_dec m rest)) c).
        - apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)
                   c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)).
          + apply (real_eq_trans _ (real_mult c real_one) _).
            * apply (real_mult_comm real_one c).
            * apply (real_mult_one c).
          + apply real_eq_refl. }
      apply (real_eq_trans _
        (real_plus c
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alu_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_list_sum Token (alu_mswitch c g) rest) c
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus c
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc c
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c))
                (real_plus real_zero
                   (real_list_sum Token (alu_mswitch real_zero g)
                      rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym
                         (real_plus real_zero
                            (real_list_sum Token (alu_mswitch real_zero g)
                               rest))
                         (real_list_sum Token (alu_mswitch real_zero g)
                            rest)).
                 apply (real_eq_trans _
                           (real_plus
                              (real_list_sum Token (alu_mswitch real_zero g)
                                 rest) real_zero) _).
                 apply (real_plus_comm real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
                 apply (real_plus_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))
                       (real_mult
                          (real_plus real_one
                             (real_of_nat
                                (count_token Token token_eq_dec m rest))) c)
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))).
              ** apply (real_eq_sym
                          (real_mult
                             (real_plus real_one
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest)))
                             c)
                          (real_plus c
                             (real_mult
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest))
                                c))).
                 exact Hcore.
              ** apply real_eq_refl.
    + (* 非副本支：IH + assoc + comm 拼中项交换 *)
      apply (real_eq_trans _
        (real_plus (g y)
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alu_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat (g y)
                 (real_list_sum Token (alu_mswitch c g) rest) (g y)
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus (g y)
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc (g y)
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c) (g y))
                (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)
                       (real_plus
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)).
              ** apply (real_plus_comm (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)).
              ** apply real_eq_refl.
           ++ apply (real_eq_sym
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_plus (g y)
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)))
                 (real_plus
                    (real_plus
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)
                       (g y))
                    (real_list_sum Token (alu_mswitch real_zero g)
                       rest))).
              ** apply (real_plus_assoc
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y)
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
Qed.

(* ---------- 内部件 0：开关自逐点等值（mass_split 的 pointwise 面） ---------- *)

Lemma alu_switch_self_eq : forall (f : Token -> Real) (x : Token),
  real_eq (alu_mswitch (f m) f x) (f x).
Proof.
  intros f x. unfold alu_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* Id 非 setoid：id_cong + id_sym + aid_real_eq 桥（基库惯用法） *)
    exact (aid_real_eq (f m) (f x) (id_sym (id_cong f Hxm))).
  - apply real_eq_refl.
Qed.

Lemma alu_sum_switch_self : forall f : Token -> Real,
  real_eq (real_list_sum Token (alu_mswitch (f m) f) vocab)
          (real_list_sum Token f vocab).
Proof.
  intro f. apply real_list_sum_ext. intro w.
  exact (alu_switch_self_eq f w).
Qed.

(* ---------- 内部件 1：minus_r 右消还原：(a − b) + b == a ---------- *)

Lemma alu_minus_r_plus : forall a b : Real,
  real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b. unfold real_minus_r.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) b)) _).
  - (* (a + −b) + b == a + (−b + b)：右嵌形 = assoc 的对称 *)
    apply (real_eq_sym (real_plus a (real_plus (real_opp b) b))
                       (real_plus (real_plus a (real_opp b)) b)).
    apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus b (real_opp b))) _).
    + apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) b) a (real_plus b (real_opp b))).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply (real_eq_trans _ (real_plus a real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat a
                 (real_plus b (real_opp b)) a real_zero).
        -- apply real_eq_refl.
        -- apply real_plus_opp.
      * apply real_plus_zero.
Qed.

(* ---------- 内部件 2：Real 层加法右消去（上游蓝图预留件） ----------
   c + a == c + b ⟹ a == b。构造路线：两侧加 −c（compat），assoc/comm
   折叠 (−c + c) → 0 → 0 + d == d。零序判定依赖，纯 eq 代数。       *)

Lemma alu_plus_reg_r : forall a b c : Real,
  real_eq (real_plus c a) (real_plus c b) -> real_eq a b.
Proof.
  intros a b c H.
  assert (Hshift : forall d : Real,
    real_eq (real_plus (real_opp c) (real_plus c d)) d).
  { intro d.
    apply (real_eq_trans _ (real_plus (real_plus (real_opp c) c) d) _).
    - apply (real_plus_assoc (real_opp c) c d).
    - apply (real_eq_trans _ (real_plus (real_plus c (real_opp c)) d) _).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp c) c) d
                 (real_plus c (real_opp c)) d).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus real_zero d) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_plus c (real_opp c)) d real_zero d).
          -- apply real_plus_opp.
          -- apply real_eq_refl.
        * apply (real_eq_trans _ (real_plus d real_zero) _).
          -- apply real_plus_comm.
          -- apply real_plus_zero. }
  apply (real_eq_trans a (real_plus (real_opp c) (real_plus c a)) b).
  - exact (real_eq_sym _ _ (Hshift a)).
  - apply (real_eq_trans (real_plus (real_opp c) (real_plus c a))
             (real_plus (real_opp c) (real_plus c b)) b).
    + apply (RealSetoid.real_eq_plus_compat (real_opp c) (real_plus c a)
               (real_opp c) (real_plus c b)).
      * apply real_eq_refl.
      * exact H.
    + exact (Hshift b).
Qed.

(* ---------- 内部件 3：M ≥ 0（switch 保非负 + sum_nonneg） ---------- *)

Lemma alu_M_nonneg : forall (T : Real) (Ht : real_lt real_zero T),
  real_le real_zero (alu_M T Ht).
Proof.
  intros T Ht. unfold alu_M.
  apply (sum_nonneg_aux Token (alu_mswitch real_zero (alu_w T Ht)) vocab).
  intro y. unfold alu_mswitch.
  destruct (token_eq_dec y m) as [Hym | Hnym].
  - apply real_le_refl.
  - apply real_le_from_lt_aux.
    exact (w_T_pos Token vocab vocab_nonempty z T Ht y).
Qed.

(* ---------- 内部件 4：w_T(m) ≤ 1/k（wm_le_invk） ----------
   链：k·w(m) + M == Σw == 1 且 M ≥ 0 ⟹ k·w(m) ≤ 1 == k·(1/k)；
   右乘 1/k（正数保序）后 eq_mult_inv_absorb 两侧换序收尾——
   上游蓝图 alm_w_m_le_invk 的免消去引理实现。                   *)

Lemma alu_wm_le_invk : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (alu_w T Ht m) (alm_invk Token vocab token_eq_dec m m_in_vocab).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* 步 1：k·w(m) ≤ 1 *)
  assert (Hle1 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (alu_w T Ht m))
                         real_one).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (alu_w T Ht m))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (alu_M T Ht))
             real_one).
    - apply (real_eq_trans
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (alu_w T Ht m))
                          (alu_M T Ht))
               (real_list_sum Token (alu_w T Ht) vocab) real_one).
      + apply (real_eq_trans
                 (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                       (alu_w T Ht m))
                            (alu_M T Ht))
                 (real_list_sum Token
                    (alu_mswitch (alu_w T Ht m) (alu_w T Ht)) vocab) _).
        * exact (real_eq_sym _ _
                   (alu_switch_sum_fun (alu_w T Ht m) (alu_w T Ht) vocab)).
        * exact (alu_sum_switch_self (alu_w T Ht)).
      + exact (w_T_sum_one Token vocab vocab_nonempty z T Ht).
    - apply (real_le_plus_nonneg_r_aux _ _ (alu_M_nonneg T Ht)). }
  (* 步 2：k·w(m) ≤ k·(1/k)（eq 1 == k·(1/k) 适配 + 步 1） *)
  assert (Hle2 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (alu_w T Ht m))
                         (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (alu_w T Ht m))
             real_one
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))).
    - exact (real_eq_sym _ _ Hk1).
    - exact Hle1. }
  (* 步 3：右乘 1/k（正数）保序 *)
  assert (Hle4 : real_le (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (alu_w T Ht m))
                                     (alm_invk Token vocab token_eq_dec m m_in_vocab))
                         (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (alm_invk Token vocab token_eq_dec m m_in_vocab))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (real_le_mult_compat _ _
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    - exact (real_inv_pos_pos (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
    - exact Hle2. }
  (* 步 4：eq_mult_inv_absorb 两侧换序 + le 适配收尾 *)
  apply (RealSetoid.real_le_id_l (alu_w T Ht m)
           (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (alu_w T Ht m))
                      (alm_invk Token vocab token_eq_dec m m_in_vocab))
           (alm_invk Token vocab token_eq_dec m m_in_vocab)).
  - apply (real_eq_sym _ _ (eq_mult_inv_absorb
              (real_of_nat (alm_k Token vocab token_eq_dec m))
              (alu_w T Ht m)
              (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1)).
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alu_w T Ht m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    + exact (eq_mult_inv_absorb
               (real_of_nat (alm_k Token vocab token_eq_dec m))
               (alm_invk Token vocab token_eq_dec m m_in_vocab)
               (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1).
    + exact Hle4.
Qed.

(* ============================================================ *)
(* 链件 ①：alu_mass_split —— vocab 质量分裂引理                     *)
(*   Σ_vocab w_T == k·w_T(m) + M（上游原申报形；自逐点等值 +          *)
(*   alu_switch_sum_fun 直接使用）。                                 *)
(* ============================================================ *)

Theorem alu_mass_split : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (alu_w T Ht) vocab)
          (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                (alu_w T Ht m))
                     (alu_M T Ht)).
Proof.
  intros T Ht.
  apply (real_eq_trans
           (real_list_sum Token (alu_w T Ht) vocab)
           (real_list_sum Token
              (alu_mswitch (alu_w T Ht m) (alu_w T Ht)) vocab) _).
  - apply (real_eq_sym _ _ (alu_sum_switch_self (alu_w T Ht))).
  - exact (alu_switch_sum_fun (alu_w T Ht m) (alu_w T Ht) vocab).
Qed.

(* ============================================================ *)
(* 链件 ②：alu_deficit_eq —— 亏量恒等式                             *)
(*   k·(1/k − w_T(m)) == M（亏差=溢出；上游原申报形）。              *)
(*   链：D + w(m) == 1/k（minus_r 右消）⟹ k·(D + w(m)) == k·(1/k)    *)
(*   == 1 == k·w(m) + M（①+Σw==1）⟹ 交换后 alu_plus_reg_r 消去。   *)
(* ============================================================ *)

Theorem alu_deficit_eq : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                   (alu_w T Ht m)))
          (alu_M T Ht).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* k·w(m) + M == 1（①+Σw==1） *)
  assert (Hsum1 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m))
                                      (alu_M T Ht))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (alu_M T Ht))
             (real_list_sum Token (alu_w T Ht) vocab) _).
    - exact (real_eq_sym _ _ (alu_mass_split T Ht)).
    - exact (w_T_sum_one Token vocab vocab_nonempty z T Ht). }
  (* D + w(m) == 1/k（D := 1/k − w(m) 的右消还原） *)
  assert (Hcan : real_eq (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))
                                    (alu_w T Ht m))
                         (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (alu_minus_r_plus _ _).
  (* k·(D + w(m)) == k·D + k·w(m)（分配，左因子参数位） *)
  assert (Hdist : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (real_plus (real_minus_r
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                            (alu_w T Ht m))
                                         (alu_w T Ht m)))
                  (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (real_minus_r
                                           (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                           (alu_w T Ht m)))
                             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (alu_w T Ht m))))
    by exact (real_distrib _ _ _).
  (* k·D + k·w(m) == k·(D + w(m)) == k·(1/k) == 1 *)
  assert (Hone2 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (alu_w T Ht m)))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m)))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m)))
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))
                                   (alu_w T Ht m))) _).
    - exact (real_eq_sym _ _ Hdist).
    - apply (real_eq_trans
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (real_plus (real_minus_r
                                        (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                        (alu_w T Ht m))
                                     (alu_w T Ht m)))
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (real_plus (real_minus_r
                               (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                            (alu_w T Ht m))
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (alm_invk Token vocab token_eq_dec m m_in_vocab)).
        * apply real_eq_refl.
        * exact Hcan.
      + exact Hk1. }
  (* 交换 + 过 1 + 右消去 ⟹ k·D == M *)
  assert (Hswap : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (alu_w T Ht m))))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))) _).
    - apply real_plus_comm.
    - exact Hone2. }
  exact (alu_plus_reg_r _ _ _
           (real_eq_trans _ _ _ Hswap (real_eq_sym _ _ Hsum1))).
Qed.

(* ============================================================ *)
(* 链件 ③：alu_mass_rest_le —— 其余部分质量上界                     *)
(*   M ≤ n·e^{−γ/T}（上游原申报形；逐点：副本支 0 ≤ decay（exp 恒    *)
(*   正），非副本支 core_decay_bound 复用；求和步 sum_nonneg_le_     *)
(*   const_aux（n = length vocab）。                                 *)
(* ============================================================ *)

Theorem alu_mass_rest_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (alu_M T Ht)
          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)).
Proof.
  intros T Ht. unfold alu_M.
  apply (sum_nonneg_le_const_aux Token
           (alu_mswitch real_zero (alu_w T Ht))
           (decay_T gamma T Ht) vocab).
  intros x Hin. unfold alu_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* 副本支：0 ≤ decay_T，exp 恒正 *)
    apply real_le_from_lt_aux. unfold decay_T. apply cauchy_real_exp_pos.
  - (* 非副本支：w_T(x) ≤ decay_T（免 m_count_one 的衰减界） *)
    exact (core_decay_bound Token vocab vocab_nonempty z m m_in_vocab
              gamma gap_le T Ht x Hnxm).
Qed.

(* ---------- 内部件 5：逐点 |u − w| == switch(D, w) ----------
   u = alm_uniform；副本支 D := 1/k − w(m) ≥ 0（wm_le_invk 入件）
   经 real_abs_minus_r_nonneg_aux 折叠 abs；非副本支 |0 − w(x)| ==
   w(x)（w ≥ 0）。unfold 双件在前、destruct 在后（上游件同款处置）。   *)

Lemma alu_abs_pointwise : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_eq (real_abs (real_minus_r (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                  (alu_w T Ht x)))
          (alu_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht m))
                       (alu_w T Ht) x).
Proof.
  intros T Ht x.
  assert (Hwmle : real_le (alu_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (alu_wm_le_invk T Ht).
  unfold alu_mswitch, alm_uniform.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* 副本支：x==m 的 Id 传输（id_cong 链）后 |D| == D（D ≥ 0 折叠） *)
    assert (HTx : real_eq (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (alu_w T Ht x))
                          (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (alu_w T Ht m)))
      by exact (aid_real_eq _ _
                  (id_cong (fun t =>
                              real_minus_r
                                (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                t)
                     (id_cong (alu_w T Ht) Hxm))).
    apply (real_eq_trans
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht x)))
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht m))) _).
    + exact (real_abs_eq_compat _ _ HTx).
    + (* |1/k − w(m)| == |−(w(m) − 1/k)| == |w(m) − 1/k| == 1/k − w(m) *)
      apply (real_eq_trans
               (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                       (alu_w T Ht m)))
               (real_abs (real_opp (real_minus_r (alu_w T Ht m)
                                                 (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
      * (* 1/k − w(m) == −(w(m) − 1/k)：comm + opp_opp + opp_plus 翻转 *)
        apply real_abs_eq_compat.
        apply (real_eq_trans
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                 (real_plus (real_opp (alu_w T Ht m))
                            (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
        -- apply real_plus_comm.
        -- apply (real_eq_trans
                    (real_plus (real_opp (alu_w T Ht m))
                               (alm_invk Token vocab token_eq_dec m m_in_vocab))
                    (real_plus (real_opp (alu_w T Ht m))
                               (real_opp (real_opp
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_opp (alu_w T Ht m))
                       (alm_invk Token vocab token_eq_dec m m_in_vocab)
                       (real_opp (alu_w T Ht m))
                       (real_opp (real_opp
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym _ _
                       (real_opp_opp
                          (alm_invk Token vocab token_eq_dec m m_in_vocab))).
           ++ apply (real_eq_sym _ _ (real_opp_plus (alu_w T Ht m)
                        (real_opp (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
      * (* |−(w(m) − 1/k)| == |w(m) − 1/k| == 1/k − w(m)（wm_le_invk 入件） *)
        apply (real_eq_trans
                 (real_abs (real_opp (real_minus_r (alu_w T Ht m)
                                                   (alm_invk Token vocab token_eq_dec m m_in_vocab))))
                 (real_abs (real_minus_r (alu_w T Ht m)
                                         (alm_invk Token vocab token_eq_dec m m_in_vocab))) _).
        -- exact (real_abs_opp (real_minus_r (alu_w T Ht m)
                              (alm_invk Token vocab token_eq_dec m m_in_vocab))).
        -- exact (real_abs_minus_r_nonneg_aux (alu_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab) Hwmle).
  - (* 非副本支：|0 − w(x)| == |−w(x)| == w(x)（w ≥ 0） *)
    apply (real_eq_trans
             (real_abs (real_minus_r real_zero (alu_w T Ht x)))
             (real_abs (real_opp (alu_w T Ht x))) _).
    + apply real_abs_eq_compat.
      apply (real_eq_trans
               (real_minus_r real_zero (alu_w T Ht x))
               (real_plus (real_opp (alu_w T Ht x)) real_zero) _).
      * apply real_plus_comm.
      * apply real_plus_zero.
    + apply (real_eq_trans (real_abs (real_opp (alu_w T Ht x)))
               (real_abs (alu_w T Ht x)) (alu_w T Ht x)).
      * apply real_abs_opp.
      * apply (real_abs_pos_req (alu_w T Ht x)
                  (w_T_pos Token vocab vocab_nonempty z T Ht x)).
Qed.

(* ============================================================ *)
(* 链件 ④：alu_l1_le —— L1 距离上界闭合                             *)
(*   L1(w_T, u) = Σ|u − w| == 2M ≤ 2·(n·decay)（上游原申报形；       *)
(*   2n·decay 写成 n·decay + n·decay 直写形）。链式组装：逐点 abs    *)
(*   折叠（部件 5）+ alu_switch_sum_fun（①同款）+ ②（k·D == M）+ ③。 *)
(* ============================================================ *)

Theorem alu_l1_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token
             (fun x : Token => real_abs (real_minus_r
                            (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                            (alu_w T Ht x))) vocab)
          (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                     (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))).
Proof.
  intros T Ht.
  (* L1 == k·D + M（逐点折叠 + 函数形开关求和恒等式）⟹ == M+M ⟹ ≤ n·d+n·d *)
  apply (real_le_trans
           (real_list_sum Token
              (fun x : Token => real_abs (real_minus_r
                             (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                             (alu_w T Ht x))) vocab)
           (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                               (alu_w T Ht m)))
                      (alu_M T Ht))
           (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                      (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
  - (* L1 ≤ k·D + M：eq-链后 le_refl 适配 *)
    apply (RealSetoid.real_le_id_l
             (real_list_sum Token
                (fun x : Token => real_abs (real_minus_r
                               (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                               (alu_w T Ht x))) vocab)
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))).
    + apply (real_eq_trans
               (real_list_sum Token
                  (fun x : Token => real_abs (real_minus_r
                                 (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                 (alu_w T Ht x))) vocab)
               (real_list_sum Token
                  (alu_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                             (alu_w T Ht m))
                               (alu_w T Ht)) vocab)
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (alu_w T Ht m)))
                          (alu_M T Ht))).
      * apply real_list_sum_ext. intro w.
        exact (alu_abs_pointwise T Ht w).
      * exact (alu_switch_sum_fun
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                 (alu_w T Ht) vocab).
    + apply real_le_refl.
  - (* k·D + M == M + M（②）⟹ M+M ≤ n·d + n·d（③×2） *)
    apply (real_le_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))
             (real_plus (alu_M T Ht) (alu_M T Ht))
             (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                        (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
    + apply (RealSetoid.real_le_id_l
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (alu_w T Ht m)))
                          (alu_M T Ht))
               (real_plus (alu_M T Ht) (alu_M T Ht))
               (real_plus (alu_M T Ht) (alu_M T Ht))).
      * exact (RealSetoid.real_eq_plus_compat
                 (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                            (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                          (alu_w T Ht m)))
                 (alu_M T Ht) (alu_M T Ht) (alu_M T Ht)
                 (alu_deficit_eq T Ht) (real_eq_refl (alu_M T Ht))).
      * apply real_le_refl.
    + apply (real_le_trans
               (real_plus (alu_M T Ht) (alu_M T Ht))
               (real_plus (alu_M T Ht)
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))
               (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- exact (alu_mass_rest_le T Ht).
      * apply real_le_plus_compat.
        -- exact (alu_mass_rest_le T Ht).
        -- apply real_le_refl.
Qed.

End AluChain.

(* ============================================================ *)
(* Part 2.9：本体闭合——alm_uniform_limit                        *)
(*   陈述（冻结形）：∀eps>0, sigT T₀(>0) ∧ ∀T(0<T<T₀),        *)
(*   L1(w_T,u) ≤ eps。装配路线：质量分裂链（Part 2.5 alu_ 链自承    *)
(*   转录，因 MassSplit 为下游使用方不可反向 Require）给出          *)
(*   L1 ≤ n·d + n·d（d = e^{−γ/T}）；间隙证书/副本计数/均匀目标/     *)
(*   开关核为 Part 1-2 之 alm_ 件。阈值 T₀ := γ·δ、                 *)
(*   δ := (eps·½)·(1/n)：cw_log 缺席下的无 log 扁形替代——            *)
(*   real_exp_ge_linear（e^t > 1+t）+ exp 单调 + δ·e^{γ/T} ≥        *)
(*   δ·inv δ == 1 闭合，零嵌套 inv、零经典逻辑。                    *)
(* ============================================================ *)

Theorem alm_uniform_limit :
  forall (Token : Set) (vocab : list Token)
    (vocab_nonempty : Not (Id vocab nil))
    (token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)))
    (z : Token -> Real)
    (m : Token) (m_in_vocab : InT m vocab)
    (gamma : Real) (gamma_pos : real_lt real_zero gamma)
    (gap_le : forall x : Token, Not (Id x m) ->
      real_le (real_plus (z x) gamma) (z m))
    (eps : Real),
    real_lt real_zero eps ->
    sigT (fun T0 =>
      And (real_lt real_zero T0)
        (forall (T : Real) (Ht : real_lt real_zero T),
          real_lt T T0 ->
          real_le
            (real_list_sum Token
               (fun x : Token =>
                  real_abs (real_minus_r
                    (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                    (w_T Token vocab vocab_nonempty z T Ht x)))
               vocab)
            eps)).
Proof.
  intros Token vocab vocab_nonempty token_eq_dec z m m_in_vocab gamma
    gamma_pos gap_le eps Heps.
  (* ---------- 阈值材料：½、δ := (eps·½)·(1/n)、T₀ := γ·δ ---------- *)
  assert (H2lt0 : real_lt real_zero (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
             (real_plus real_one real_one)).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - apply (real_lt_plus_compat_lt_le real_zero real_one
               real_zero real_one real_lt_zero_one).
      apply (real_le_from_lt_aux real_zero real_one real_lt_zero_one). }
  assert (Hnatpos : forall n : nat, (1 <= n)%nat ->
    real_lt real_zero (real_of_nat n)).
  { intros n Hn. destruct n as [| j].
    - lia.
    - apply (real_lt_eq_lt real_zero
               (real_plus real_one (real_of_nat j))
               (real_of_nat (Datatypes.S j))).
      + apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus real_one (real_of_nat j))).
        * apply real_eq_sym. apply real_plus_zero.
        * apply real_lt_plus_compat_lt_le.
          -- apply real_lt_zero_one.
          -- apply real_of_nat_nonneg_aux.
      + apply real_eq_refl. }
  assert (Hn1 : (1 <= length vocab)%nat).
  { destruct vocab as [| y rest].
    - exact (match vocab_nonempty id_refl with end).
    - cbn [length]. lia. }
  assert (Hnpos : real_lt real_zero (real_of_nat (length vocab)))
    by exact (Hnatpos (length vocab) Hn1).
  set (h2 := real_inv_pos (real_plus real_one real_one) H2lt0).
  assert (Hh2 : real_lt real_zero h2)
    by exact (real_inv_pos_pos (real_plus real_one real_one) H2lt0).
  set (HALF := real_mult eps h2).
  assert (HHALF : real_lt real_zero HALF)
    by exact (real_mult_pos_compat eps h2 Heps Hh2).
  set (invn := real_inv_pos (real_of_nat (length vocab)) Hnpos).
  assert (Hinvn : real_lt real_zero invn)
    by exact (real_inv_pos_pos (real_of_nat (length vocab)) Hnpos).
  set (delta := real_mult HALF invn).
  assert (Hdelta : real_lt real_zero delta)
    by exact (real_mult_pos_compat HALF invn HHALF Hinvn).
  exists (real_mult gamma delta).
  split.
  - exact (real_mult_pos_compat gamma delta gamma_pos Hdelta).
  - intros T Ht HTl.
    set (invT := real_inv_pos T Ht).
    assert (HinvT : real_lt real_zero invT)
      by exact (real_inv_pos_pos T Ht).
    set (u := real_mult invT gamma).
    assert (Hu : real_lt real_zero u)
      by exact (real_mult_pos_compat invT gamma HinvT gamma_pos).
    set (invd := real_inv_pos delta Hdelta).
    assert (Hinvd : real_lt real_zero invd)
      by exact (real_inv_pos_pos delta Hdelta).
    (* 步1：T·invδ ≤ γ（T < γδ 右乘 invδ + δ·invδ == 1 折叠） *)
    assert (Hs1 : real_le (real_mult T invd) gamma).
    { apply (real_le_trans (real_mult T invd)
               (real_mult (real_mult gamma delta) invd) gamma).
      - apply (real_le_mult_compat T (real_mult gamma delta) invd Hinvd).
        exact (real_le_from_lt_aux T (real_mult gamma delta) HTl).
      - apply (RealSetoid.real_eq_le _ _).
        apply (real_eq_trans (real_mult (real_mult gamma delta) invd)
                 (real_mult gamma (real_mult delta invd)) gamma).
        + apply (real_eq_sym _ _ (real_mult_assoc gamma delta invd)).
        + apply (real_eq_trans
                   (real_mult gamma (real_mult delta invd))
                   (real_mult gamma real_one) gamma).
          * apply (RealSetoid.real_eq_mult_compat gamma
                     (real_mult delta invd) gamma real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct delta Hdelta).
          * exact (real_mult_one gamma). }
    (* 步2：invδ ≤ u := invT·γ（步1 右乘 invT + invT·T == 1 折叠） *)
    assert (Hs2 : real_le invd u).
    { apply (RealSetoid.real_le_id_l invd
               (real_mult invT (real_mult T invd)) u).
      - apply (real_eq_sym _ _).
        apply (real_eq_trans
                 (real_mult invT (real_mult T invd))
                 (real_mult real_one invd) invd).
        + apply (real_eq_trans
                   (real_mult invT (real_mult T invd))
                   (real_mult (real_mult invT T) invd)
                   (real_mult real_one invd)).
          * apply real_mult_assoc.
          * apply (RealSetoid.real_eq_mult_compat
                     (real_mult invT T) invd real_one invd).
            -- apply (real_eq_trans (real_mult invT T)
                       (real_mult T invT) real_one).
               ++ apply real_mult_comm.
               ++ exact (real_inv_pos_correct T Ht).
            -- apply real_eq_refl.
        + apply (real_eq_trans (real_mult real_one invd)
                   (real_mult invd real_one) invd).
          * apply real_mult_comm.
          * exact (real_mult_one invd).
      - exact (real_le_mult_compat_l_aux (real_mult T invd) gamma invT
                 HinvT Hs1). }
    (* 步3：invδ ≤ e^u（invδ ≤ 1+invδ ≤ e^{invδ} ≤ e^u：ge_linear + 单调） *)
    assert (Hs3 : real_le invd (cauchy_real_exp u)).
    { assert (Hmid : real_le (real_plus real_one invd)
                       (cauchy_real_exp invd)).
      { exact (real_le_from_lt_aux (real_plus real_one invd)
                 (cauchy_real_exp invd) (real_exp_ge_linear invd Hinvd)). }
      apply (real_le_trans invd (cauchy_real_exp invd) (cauchy_real_exp u)).
      - apply (real_le_trans invd (real_plus real_one invd)
                 (cauchy_real_exp invd)).
        + apply (RealSetoid.real_le_id_l invd
                   (real_plus real_zero invd) (real_plus real_one invd)).
          * exact (real_eq_trans invd (real_plus invd real_zero)
                     (real_plus real_zero invd)
                     (real_eq_sym (real_plus invd real_zero) invd
                        (real_plus_zero invd))
                     (real_plus_comm invd real_zero)).
          * apply (real_le_plus_compat real_zero real_one invd invd).
            -- exact (real_le_from_lt_aux real_zero real_one
                        real_lt_zero_one).
            -- apply real_le_refl.
        + exact Hmid.
      - apply real_exp_le_mono. exact Hs2. }
    (* 步4：1 ≤ δ·e^u（步3 左乘 δ + δ·invδ == 1） *)
    assert (Hs4 : real_le real_one (real_mult delta (cauchy_real_exp u))).
    { apply (RealSetoid.real_le_id_l real_one
               (real_mult delta invd) (real_mult delta (cauchy_real_exp u))).
      - exact (real_eq_sym (real_mult delta invd) real_one
                 (real_inv_pos_correct delta Hdelta)).
      - exact (real_le_mult_compat_l_aux invd (cauchy_real_exp u) delta
                 Hdelta Hs3). }
    (* 步5：d ≤ δ（d·e^u == 1（exp_mult_opp_l）+ 步4 + 右乘 inv(e^u) 消去） *)
    assert (Hs5 : real_le (decay_T gamma T Ht) delta).
    { set (E := cauchy_real_exp u).
      assert (HE : real_lt real_zero E) by exact (cauchy_real_exp_pos u).
      set (invE := real_inv_pos E HE).
      assert (HinvE : real_lt real_zero invE)
        by exact (real_inv_pos_pos E HE).
      assert (Hcancel : real_le (real_mult (decay_T gamma T Ht) E)
                                (real_mult delta E)).
      { apply (real_le_trans (real_mult (decay_T gamma T Ht) E)
                 real_one (real_mult delta E)).
        - apply (RealSetoid.real_eq_le _ _).
          exact (exp_mult_opp_l_aux u).
        - exact Hs4. }
      assert (Hrhs : real_eq (real_mult (real_mult delta E) invE) delta).
      { apply (real_eq_trans
                 (real_mult (real_mult delta E) invE)
                 (real_mult delta (real_mult E invE)) delta).
        - apply (real_eq_sym _ _ (real_mult_assoc delta E invE)).
        - apply (real_eq_trans _
                   (real_mult delta real_one) _).
          + apply (RealSetoid.real_eq_mult_compat delta
                     (real_mult E invE) delta real_one).
            * apply real_eq_refl.
            * exact (real_inv_pos_correct E HE).
          + exact (real_mult_one delta). }
      apply (RealSetoid.real_le_id_l (decay_T gamma T Ht)
               (real_mult (real_mult (decay_T gamma T Ht) E) invE) delta).
      - apply (real_eq_sym _ _).
        apply (real_eq_trans
                 (real_mult (real_mult (decay_T gamma T Ht) E) invE)
                 (real_mult (decay_T gamma T Ht) (real_mult E invE))
                 (decay_T gamma T Ht)).
        + apply (real_eq_sym _ _
                   (real_mult_assoc (decay_T gamma T Ht) E invE)).
        + apply (real_eq_trans _
                   (real_mult (decay_T gamma T Ht) real_one) _).
          * apply (RealSetoid.real_eq_mult_compat (decay_T gamma T Ht)
                     (real_mult E invE) (decay_T gamma T Ht) real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct E HE).
          * exact (real_mult_one (decay_T gamma T Ht)).
      - apply (RealSetoid.real_le_id_r
                 (real_mult (real_mult (decay_T gamma T Ht) E) invE)
                 (real_mult (real_mult delta E) invE) delta).
        + exact Hrhs.
        + apply (real_le_mult_compat (real_mult (decay_T gamma T Ht) E)
                   (real_mult delta E) invE HinvE Hcancel). }
    (* 步6-7：L1 ≤ n·d + n·d ≤ n·δ + n·δ == eps（链闭合） *)
    apply (real_le_trans
             (real_list_sum Token
                (fun x : Token => real_abs (real_minus_r
                   (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                   (alu_w Token vocab vocab_nonempty z T Ht x))) vocab)
             (real_plus (real_mult (real_of_nat (length vocab)) delta)
                        (real_mult (real_of_nat (length vocab)) delta))
             eps).
    + apply (real_le_trans
               (real_list_sum Token
                  (fun x : Token => real_abs (real_minus_r
                     (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                     (alu_w Token vocab vocab_nonempty z T Ht x))) vocab)
               (real_plus
                  (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                  (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht)))
               (real_plus (real_mult (real_of_nat (length vocab)) delta)
                          (real_mult (real_of_nat (length vocab)) delta))).
      * exact (alu_l1_le Token vocab vocab_nonempty token_eq_dec z
                 m m_in_vocab gamma gap_le T Ht).
      * apply (real_le_plus_compat
                 (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                 (real_mult (real_of_nat (length vocab)) delta)).
        -- apply (RealSetoid.real_le_id_l
                    (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                    (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                    (real_mult (real_of_nat (length vocab)) delta)).
           ++ apply real_mult_comm.
           ++ apply (RealSetoid.real_le_id_r
                       (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                       (real_mult delta (real_of_nat (length vocab)))
                       (real_mult (real_of_nat (length vocab)) delta)).
              ** apply real_mult_comm.
              ** exact (real_le_mult_compat (decay_T gamma T Ht) delta
                          (real_of_nat (length vocab)) Hnpos Hs5).
        -- apply (RealSetoid.real_le_id_l
                    (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                    (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                    (real_mult (real_of_nat (length vocab)) delta)).
           ++ apply real_mult_comm.
           ++ apply (RealSetoid.real_le_id_r
                       (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                       (real_mult delta (real_of_nat (length vocab)))
                       (real_mult (real_of_nat (length vocab)) delta)).
              ** apply real_mult_comm.
              ** exact (real_le_mult_compat (decay_T gamma T Ht) delta
                          (real_of_nat (length vocab)) Hnpos Hs5).
    + apply (RealSetoid.real_eq_le _ _).
      assert (Hnd : real_eq
                 (real_mult (real_of_nat (length vocab)) delta) HALF).
      { apply (real_eq_trans
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult HALF
                    (real_mult (real_of_nat (length vocab)) invn)) HALF).
        - apply (real_eq_trans _
                   (real_mult (real_mult HALF (real_of_nat (length vocab)))
                      invn) _).
          * apply (real_eq_trans _
                     (real_mult (real_mult (real_of_nat (length vocab)) HALF)
                        invn) _).
            -- apply real_mult_assoc.
            -- apply (RealSetoid.real_eq_mult_compat
                       (real_mult (real_of_nat (length vocab)) HALF) invn
                       (real_mult HALF (real_of_nat (length vocab))) invn).
               ++ apply (real_mult_comm (real_of_nat (length vocab)) HALF).
               ++ apply real_eq_refl.
          * apply (real_eq_sym _ _ (real_mult_assoc HALF
                       (real_of_nat (length vocab)) invn)).
        - apply (real_eq_trans
                   (real_mult HALF (real_mult (real_of_nat (length vocab)) invn))
                   (real_mult HALF real_one) HALF).
          * apply (RealSetoid.real_eq_mult_compat HALF
                     (real_mult (real_of_nat (length vocab)) invn)
                     HALF real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct (real_of_nat (length vocab)) Hnpos).
          * exact (real_mult_one HALF). }
      apply (real_eq_trans
               (real_plus (real_mult (real_of_nat (length vocab)) delta)
                  (real_mult (real_of_nat (length vocab)) delta))
               (real_plus HALF HALF) eps).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult (real_of_nat (length vocab)) delta)
                 HALF HALF Hnd Hnd).
      * apply (real_eq_trans (real_plus HALF HALF)
                 (real_mult eps (real_plus h2 h2)) eps).
        -- apply (real_eq_sym _ _ (real_distrib eps h2 h2)).
        -- apply (real_eq_trans _
                     (real_mult eps
                        (real_mult (real_plus real_one real_one) h2)) _).
           ++ apply (RealSetoid.real_eq_mult_compat eps (real_plus h2 h2)
                      eps (real_mult (real_plus real_one real_one) h2)).
              ** apply real_eq_refl.
              ** apply (real_eq_trans
                          (real_plus h2 h2)
                          (real_plus (real_mult real_one h2)
                             (real_mult real_one h2))
                          (real_mult (real_plus real_one real_one) h2)).
                 --- apply (RealSetoid.real_eq_plus_compat h2 h2
                              (real_mult real_one h2)
                              (real_mult real_one h2)).
                     +++ exact (real_eq_trans h2
                                  (real_mult h2 real_one)
                                  (real_mult real_one h2)
                                  (real_eq_sym (real_mult h2 real_one) h2
                                     (real_mult_one h2))
                                  (real_mult_comm h2 real_one)).
                     +++ exact (real_eq_trans h2
                                  (real_mult h2 real_one)
                                  (real_mult real_one h2)
                                  (real_eq_sym (real_mult h2 real_one) h2
                                     (real_mult_one h2))
                                  (real_mult_comm h2 real_one)).
                 --- exact (real_distrib_r real_one real_one h2).
           ++ apply (real_eq_trans
                       (real_mult eps
                          (real_mult (real_plus real_one real_one) h2))
                       (real_mult eps real_one) eps).
              ** apply (RealSetoid.real_eq_mult_compat eps
                          (real_mult (real_plus real_one real_one) h2)
                          eps real_one).
                 --- apply real_eq_refl.
                 --- exact (real_inv_pos_correct
                              (real_plus real_one real_one) H2lt0).
              ** exact (real_mult_one eps).
Qed.

Print Assumptions alm_uniform_limit.
(* ============================================================ *)
(* Part 3：提取口与公理面审计                                 *)
(* ============================================================ *)

(* 计算核提取出口（对齐现件 attn_hardlimit218.ml 出口形态） *)
From Stdlib Require Import Extraction.
Extraction "attn_uniformlimit_q18.ml"
  alm_max_ne alm_count_ge_one_aux alm_k alm_uniform alm_switch count_token.

Print Assumptions alm_gap_witness.
Print Assumptions alm_k_pos.
Print Assumptions alm_uniform.

(* 新增主件审计口：m-开关求和恒等式两件（swg_switch_sum_gen/swg_switch_sum） *)
Print Assumptions swg_switch_sum_gen.
Print Assumptions swg_switch_sum.
(* ============================================================ *)
(* 词表非空位 vocab_nonempty 与 token 可判定相等位 token_eq_dec 的        *)
(* Set 重述位与具体层供给                                                *)
(*                                                                     *)
(* 原两位为 Prop 形（Not (Id vocab nil) 与 forall a b, Or (Id a b)        *)
(* (Not (Id a b))）；本节将其重述为 Set 层形并给出具体层供给：非空取      *)
(* sigT 见证形 sigT (fun t => InT t vocab)（见证更强：可提取出具体元素），  *)
(* 可判定相等取 sigT bool 形——正支给出 Id 相等见证，负支给出              *)
(* Id a b -> Empty_set 函数（Set 层否定见证，可提取）。二点清单（bool      *)
(* 载体）上，非空见证由 InT_here 构造子直接给出，可判定相等由构造子四分    *)
(* 逐一给出（正支 id_refl，负支构造子分裂消去）。原 Prop 形假设位声明与    *)
(* 既有定理签名零改动。                                                  *)
(* ============================================================ *)
Definition alm_vocab_nonempty_set (X : Set) (vocab : list X) : Set :=
  sigT (fun t : X => InT t vocab).
Definition alm_token_eq_dec_set (X : Set) : Set :=
  forall a b : X,
    sigT (fun d : bool =>
      match d with
      | true => Id a b
      | false => Id a b -> Empty_set
      end).

Theorem alm_vocab_nonempty_supply :
  alm_vocab_nonempty_set bool (cons true (cons false nil)).
Proof. exact (existT _ true (@InT_here bool true (cons false nil))). Qed.

Theorem alm_token_eq_dec_supply : alm_token_eq_dec_set bool.
Proof.
  intros a b.
  destruct a; destruct b.
  - exact (existT _ true (@id_refl bool true)).
  - refine (existT _ false _).
    intro H.
    (* 构造子分裂：Id true false 无构造元，J 形索引匹配消去 *)
    exact (match H in Id _ y return
             match y with true => unit | false => Empty_set end with
           id_refl => tt end).
  - refine (existT _ false _).
    intro H.
    exact (match H in Id _ y return
             match y with false => unit | true => Empty_set end with
           id_refl => tt end).
  - exact (existT _ true (@id_refl bool false)).
Qed.

Print Assumptions alm_vocab_nonempty_supply.
Print Assumptions alm_token_eq_dec_supply.
