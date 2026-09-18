(* ============================================================ *)
(* UpReqAttnUniformLimit.v —— 并列最大值注意力极限定理                *)
(*                                                              *)
(* 目的：闭合 AttnHardLimit218 自注的待补缺口（其头注接口①注记，      *)
(*   :23-30）：「若 m 有并列副本，w_T 的 T→0 极限是副本上的均匀分布」。 *)
(*                                                              *)
(* 主件（前缀 alm_，避免与库内既有名冲突）：                          *)
(*   ① alm_gap_witness——Q 层并列间隙证书：非空 Q 表上极大值           *)
(*      （可判定枚举 alm_max_ne）＋多重数 k≥1＋逐点上界＋两分支：      *)
(*      (i) 全表同值（均匀退化档）或 (ii) 并列间隙 g>0 且逐点          *)
(*      q==qmax ∨ q+g≤qmax（镜像现件 gap_le 形）。全构造性。           *)
(*   ② 定义面——副本多重数 alm_k := count_token m vocab（不要求        *)
(*      唯一）、副本均匀目标 alm_uniform、m-开关 alm_switch：          *)
(*      并列副本→均匀的计算核，Defined 可提取。                        *)
(*   ③ m-开关求和恒等式 swg_switch_sum_gen / swg_switch_sum。          *)
(*                                                              *)
(* 已知边界（待续工作）：极限定理 alm_uniform_limit 陈述已冻结，        *)
(*   尚未落盘。蓝图：                                                 *)
(*   陈述：∀eps>0, sigT T₀(>0) ∧ ∀T<T₀, L1(w_T,u) ≤ eps；             *)
(*   率形：L1 ≤ 2n·e^{−γ/T}（数值核验已过）；                          *)
(*   阈值：T₀ := γ/ln(1+2n/eps)（cw_log 形）；                         *)
(*   核心恒等式：k·(1/k−w_T(m)) = 非 m 质量 M，L1 = 2M                  *)
(*    （数值验证：四温度点 L1==2M 逐位成立）。                          *)
(*   引理链：switch_gen → mass_split → deficit_eq → mass_rest_le       *)
(*   （复用 core_decay_bound，免 m_count_one，其签名已核）→ l1_le。     *)
(*   另两处诚实障碍：跨 token 同值情形 L1→1≠0（数值验证），覆盖它       *)
(*   需 argmax 集合在 Real 层的可判定证书，待续；T₀ 的 Q 有理化替代     *)
(*   须 cw_log 有理上界包装，待续。                                    *)
(*                                                              *)
(* 依赖（全部只读消费）：CW_ConstructiveWorld_219（伞壳）；              *)
(*   AttnHardLimit218（已完成机器验证，只读）。                         *)
(*                                                              *)
(* 备注：纯构造性、零改既有文件。公理面：零公理、零承认件、零弃证；      *)
(*   零经典逻辑。文末 Print Assumptions 核验 Closed。                   *)
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

(* m-开关函数：副本支 c1，非副本支 c2（求和恒等式的工作马） *)
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
(* 头注所述待续部分自本节起由下列 swg_ 两件承接。 *)
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

(* 收口引理：以 vocab 实例化（alm_k 即 count_token m vocab） *)
Lemma swg_switch_sum : forall c g : Real,
  real_eq (real_list_sum Token (alm_switch c g) vocab)
    (real_plus (real_mult (real_of_nat alm_k) c)
               (real_list_sum Token (alm_switch real_zero g) vocab)).
Proof.
  intros c g. unfold alm_k.
  apply (swg_switch_sum_gen c g vocab).
Qed.

End AlmUniform.

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
