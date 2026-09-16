(* ============================================================ *)
(* ExpLinearLower.v —— C11 席：exp 线性下界 Q 层种子（A3 后链榜 F4）  *)
(* （20260916；施工席位 C11）                                        *)
(* ============================================================ *)
(* 使命：主件 elv_exp_partial_ge_lin —— 0 ≤ x, 1 ≤ n ⟹ 1+x ≤          *)
(*   exp_partial n x。证法：S_n(x) − (1+x) = Σ_{k=2..n} x^k/k! 逐项    *)
(*   非负（x ≥ 0 直接适用库版 ExpNegPos.v 的 enp_term_nonneg）。       *)
(* 支撑 ≥2：尾差展开件 elv_exp_step_any（exp_partial 单步定义性展开，  *)
(*   库版 enp_expSS 同款配方）；逐项正性传递 = 内衬步进                 *)
(*   （enp_term_nonneg + Qplus_le_compat 加非负末项）。                *)
(* 可选升华：elv_exp_partial_le_one（0 ≤ x ≤ 1 ⟹ S_n(−x) ≤ 1，        *)
(*   偶部归纳配 enp_decr 配对项差 + enp_term_nonneg 奇项负性）。        *)
(*                                                                *)
(* 架构（照库版 ExpNegPos.v 件 2/件 3 分工）：Prop 内衬主面（Qle，     *)
(*   容纳 le/Even_or_Odd 的 Prop 消解）→ QleT' Set 出口薄壳。          *)
(*   实测坑①：le/Even_or_Odd 属 Prop，不得 destruct 进 Set 语句目标。  *)
(*   实测坑②：Qeq 集合 rewrite 只能在 Qeq goal 内动；Qle 面一律        *)
(*   Qle_trans 分腿 + qeq_le 桥（库版同款纪律）。                      *)
(*                                                                *)
(* 依赖侧编实况：库版 ConstructiveWorld_Live/ExpNegPos.v（347 行，    *)
(*   非 Live/build 十六稿同名件；不在 order.txt，vorebuild 无其 .vo）。*)
(*   侧编配方（本席实测通过）：                                       *)
(*     mkdir -p /tmp/expneg_side &&                                   *)
(*     cp -p ConstructiveWorld_Live/ExpNegPos.v /tmp/expneg_side/ &&  *)
(*     cd /tmp/expneg_side && rocq c -Q <vorebuild绝对路径> ""        *)
(*        -Q . "" ExpNegPos.v                                         *)
(*   库版件名清单（grep 实测）：enp_one_le_succ / enp_decr /           *)
(*   enp_term_nonneg（Qle 0 x -> Qle 0 (q_pow x k / q_fact k)）/       *)
(*   enp_expSS / enp_two_step_odd / enp_odd_step / enp_odd_ge /       *)
(*   enp_even_ge_odd / enp_ge_all / enp_exp_partial_ge /              *)
(*   enp_exp_partial_nonneg / enp_exp_partial_pos / 两数值例。         *)
(*   其 Print Assumptions ×3 全 Closed（零公理面）。                   *)
(*                                                                *)
(* 红线自审：出口语句面全 QleT'（Qle 仅证内/内衬件，恒等件照库版       *)
(*   enp_expSS 先例用 Qeq 同式可逆恒等）；禁词八项零命中；全件 Qed     *)
(*   真证；文末 Print Assumptions ≥1。                                *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import ExpNegPos.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* 件 1（尾差展开件）：exp_partial 单步定义性展开                       *)
(*   （库版 enp_expSS 同款配方，普适 y 形）                            *)
(* ============================================================ *)

Lemma elv_exp_step_any : forall (n : nat) (y : Q),
  exp_partial (Datatypes.S n) y
  == exp_partial n y
     + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n).
Proof. intros n y. reflexivity. Qed.

(* 基座恒等：S_1(x) == 1 + x。
   Qinv (1 * 1) 系非环原子（Qdiv=Qmult x (Qinv y)，ring 不穿），须先桥
   为 1 再 ring（照库版 enp_odd_ge 基座配方）。 *)
Lemma elv_exp1 : forall x : Q, exp_partial 1 x == 1 + x.
Proof.
  intros x.
  replace (exp_partial 1 x)
    with (exp_partial 0 x + q_pow x 1 / q_fact 1) by reflexivity.
  replace (exp_partial 0 x) with 1%Q by reflexivity.
  unfold Qdiv.
  replace (q_pow x 1) with (x * 1) by reflexivity.
  replace (q_fact 1) with (1 * 1) by reflexivity.
  replace (Qinv (1 * 1)) with 1 by reflexivity.
  ring.
Qed.

(* ============================================================ *)
(* 件 2（Prop 内衬主面）：0 ≤ x, 1 ≤ n ⟹ 1 + x ≤ S_n(x)                *)
(*   S_n(x) − (1+x) = Σ_{k=2..n} x^k/k! 逐项非负。                     *)
(* ============================================================ *)

Lemma elv_lin_le_all : forall (x : Q) (n : nat),
  Qle 0 x -> (1 <= n)%nat -> Qle (1 + x) (exp_partial n x).
Proof.
  intros x n Hx0 Hn.
  revert Hn.
  induction n as [| n IH]; intros Hn.
  - (* n = 0 与 1 ≤ n 相斥（Prop 目标内 exfalso+lia 确定性闭） *)
    exfalso. lia.
  - destruct n as [| n'].
    + (* 基座 n = 1：S_1(x) == 1 + x *)
      apply (qeq_le (1 + x) (exp_partial 1 x)).
      apply Qeq_sym. apply elv_exp1.
    + (* 步进 n = S (S n')：尾差展开（Qeq 桥）+ 末项非负传递 *)
      assert (HIH : Qle (1 + x) (exp_partial (Datatypes.S n') x))
        by (apply IH; lia).
      assert (Hterm : Qle 0 (q_pow x (Datatypes.S (Datatypes.S n'))
                             / q_fact (Datatypes.S (Datatypes.S n'))))
        by (apply enp_term_nonneg; exact Hx0).
      apply (Qle_trans (1 + x) (exp_partial (Datatypes.S n') x)
                       (exp_partial (Datatypes.S (Datatypes.S n')) x)).
      * exact HIH.
      * apply (Qle_trans (exp_partial (Datatypes.S n') x)
                         (exp_partial (Datatypes.S n') x
                          + q_pow x (Datatypes.S (Datatypes.S n'))
                            / q_fact (Datatypes.S (Datatypes.S n')))).
        -- (* 原子 LHS 中转 E' + 0 归位（库版 AA21 修②同款，否则
              Qplus_le_compat 的 x+z 统一误 unfold） *)
           apply (Qle_trans (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)
                            (exp_partial (Datatypes.S n') x
                             + q_pow x (Datatypes.S (Datatypes.S n'))
                               / q_fact (Datatypes.S (Datatypes.S n')))).
           ++ apply (qeq_le (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)).
              ** ring.
           ++ apply Qplus_le_compat.
              ** apply Qle_refl.
              ** exact Hterm.
        -- (* 尾差展开同式（Qeq 桥：Qeq 重写不穿 Qle 面） *)
           apply qeq_le. apply Qeq_sym.
           apply (elv_exp_step_any (Datatypes.S n') x).
Qed.

(* ============================================================ *)
(* 件 3（主件·Set 出口）：0 ≤ x, 1 ≤ n ⟹ 1 + x ≤ S_n(x)                *)
(* ============================================================ *)

Theorem elv_exp_partial_ge_lin : forall (x : Q) (n : nat),
  QleT' 0 x -> (1 <= n)%nat -> QleT' (1 + x) (exp_partial n x).
Proof.
  intros x n H0 Hn.
  apply Qle_to_QleT'.
  apply elv_lin_le_all.
  - apply QleT'_to_Qle. exact H0.
  - exact Hn.
Qed.

(* ============================================================ *)
(* 件 4（升华支撑）：Qopp 穿除法 Qeq 桥 + 奇/偶次幂符号归一              *)
(* ============================================================ *)

(* ring 不穿除法：Qopp (u/v) == Qopp u / v（照库版 enp_two_step_odd 配方） *)
Lemma elv_qopp_div : forall u v : Q, Qopp (u / v) == Qopp u / v.
Proof. intros u v. unfold Qdiv. ring. Qed.

(* 奇次：(−x)^{S(2k)} == −x^{S(2k)}（q_pow_neg_odd 指数形 S(2k) 直配） *)
Lemma elv_neg_pow_odd : forall (x : Q) (k : nat),
  q_pow (Qopp x) (Datatypes.S (2 * k))
  == Qopp (q_pow x (Datatypes.S (2 * k))).
Proof. intros x k. apply q_pow_neg_odd. Qed.

(* 偶次：(−x)^{S(S(2k))} == x^{S(S(2k))}（指标归一 S(S 2k) == 2 * S k） *)
Lemma elv_neg_pow_even : forall (x : Q) (k : nat),
  q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * k)))
  == q_pow x (Datatypes.S (Datatypes.S (2 * k))).
Proof.
  intros x k.
  replace (Datatypes.S (Datatypes.S (2 * k)))
    with (2 * Datatypes.S k)%nat by lia.
  apply q_pow_neg_even.
Qed.

(* ============================================================ *)
(* 件 5（升华支撑·偶部归纳，Set 面）：0 ≤ x ≤ 1 ⟹ S_{2m}(−x) ≤ 1        *)
(*   两步尾差 = Qopp u + t2（u := x^{2m+1}/(2m+1)!，t2 ≤ u，            *)
(*   enp_decr）⟹ S_{2m+2} ≤ S_{2m+1} + u = S_{2m} − u + u ≤ 1。        *)
(* ============================================================ *)

Lemma elv_even_le_one : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial (2 * m) (Qopp x)) 1.
Proof.
  intros x m H0 H1.
  induction m as [| m IH].
  - (* 基座：S_0(−x) = 1 *)
    apply qeq_leT'. reflexivity.
  - (* 归纳步：2 * S m 归一 S(S(2m)) 后两步展开 *)
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    apply Qle_to_QleT'.
    (* E1 = S_{2m}(−x) + Qopp u（奇项负性桥，Qeq goal 内归一） *)
    assert (HE1 : exp_partial (Datatypes.S (2 * m)) (Qopp x)
                  == exp_partial (2 * m) (Qopp x)
                     + Qopp (q_pow x (Datatypes.S (2 * m))
                             / q_fact (Datatypes.S (2 * m)))).
    { rewrite (elv_exp_step_any (2 * m) (Qopp x)).
      rewrite (elv_neg_pow_odd x m).
      rewrite elv_qopp_div. reflexivity. }
    apply (Qle_trans
            (exp_partial (Datatypes.S (Datatypes.S (2 * m))) (Qopp x))
            (exp_partial (Datatypes.S (2 * m)) (Qopp x)
             + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
               / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
    + (* 尾差展开同式（Qeq 桥） *)
      apply qeq_le. apply Qeq_sym.
      apply (elv_exp_step_any (Datatypes.S (2 * m)) (Qopp x)).
    + (* 第二腿：LHS 为 Qopp 形，先偶负桥归 x 形，再 enp_decr 配对项差 *)
      apply (Qle_trans
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
      * (* 偶负桥：(−x)^{S(S(2m))} == x^{S(S(2m))}（Qeq 桥） *)
        apply qeq_le.
        rewrite (elv_neg_pow_even x m). reflexivity.
      * apply (Qle_trans
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                   / q_fact (Datatypes.S (Datatypes.S (2 * m))))
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (2 * m))
                   / q_fact (Datatypes.S (2 * m)))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (enp_decr x (Datatypes.S (2 * m))).
              ** apply QleT'_to_Qle. exact H0.
              ** apply QleT'_to_Qle. exact H1.
        -- (* S_{2m+1} + u = S_{2m} − u + u = S_{2m} ≤ 1 *)
           apply (Qle_trans
                   (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                    + q_pow x (Datatypes.S (2 * m))
                      / q_fact (Datatypes.S (2 * m)))
                   (exp_partial (2 * m) (Qopp x))).
           ++ apply qeq_le. rewrite HE1. ring.
           ++ apply QleT'_to_Qle. exact IH.
Qed.

(* ============================================================ *)
(* 件 6（升华·Prop 内衬）：0 ≤ x ≤ 1 ⟹ S_n(−x) ≤ 1                     *)
(*   偶部引用件 5；奇部 S_{2m+1} = S_{2m} − u ≤ S_{2m} ≤ 1              *)
(*   （奇项负性：enp_term_nonneg + Qopp_le_compat，Qopp 0 == 0 桥归）。  *)
(* ============================================================ *)

Lemma elv_exp_le_one_prop : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 -> Qle (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - (* 偶部：n = 2m *)
    subst n.
    apply QleT'_to_Qle.
    apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0) (Qle_to_QleT' _ _ H1)).
  - (* 奇部：n = 2m+1 归一 S(2m) 后单步展开 *)
    subst n.
    replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    apply (Qle_trans (exp_partial (Datatypes.S (2 * m)) (Qopp x))
                     (exp_partial (2 * m) (Qopp x)
                      + Qopp (q_pow x (Datatypes.S (2 * m))
                              / q_fact (Datatypes.S (2 * m))))).
    + (* S_{2m+1} == S_{2m} − u（尾差展开 + 奇负 + Qopp 穿除，Qeq goal 链） *)
      apply qeq_le.
      rewrite (elv_exp_step_any (2 * m) (Qopp x)).
      rewrite (elv_neg_pow_odd x m).
      rewrite elv_qopp_div. reflexivity.
    + (* S_{2m} − u ≤ S_{2m} + 0 ≤ S_{2m} ≤ 1 *)
      apply (Qle_trans (exp_partial (2 * m) (Qopp x)
                        + Qopp (q_pow x (Datatypes.S (2 * m))
                                / q_fact (Datatypes.S (2 * m))))
                       (exp_partial (2 * m) (Qopp x) + 0)).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qle_trans
                    (Qopp (q_pow x (Datatypes.S (2 * m))
                           / q_fact (Datatypes.S (2 * m))))
                    (Qopp 0) 0).
           ++ apply Qopp_le_compat. apply enp_term_nonneg. exact H0.
           ++ apply qeq_le. ring.
      * apply (Qle_trans (exp_partial (2 * m) (Qopp x) + 0)
                         (exp_partial (2 * m) (Qopp x))).
        -- apply qeq_le. ring.
        -- apply QleT'_to_Qle.
           apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0)
                                  (Qle_to_QleT' _ _ H1)).
Qed.

(* ============================================================ *)
(* 件 7（升华主件·Set 出口）：0 ≤ x ≤ 1 ⟹ S_n(−x) ≤ 1                  *)
(* ============================================================ *)

Theorem elv_exp_partial_le_one : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  apply Qle_to_QleT'.
  apply elv_exp_le_one_prop.
  - apply QleT'_to_Qle. exact H0.
  - apply QleT'_to_Qle. exact H1.
Qed.

(* ============================================================ *)
(* 出口公理面审查（G4 留痕）                                            *)
(* ============================================================ *)

Print Assumptions elv_exp_partial_ge_lin.
Print Assumptions elv_exp_partial_le_one.
