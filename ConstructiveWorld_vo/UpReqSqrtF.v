(* ==========================================================================)
   UpReqSqrtF.v — req 接口上的函数式平方根
   使命: sqrtf_sqrt（Newton 迭代平方根，sigT 组装值与正性见证）、sqrtf_fixed_point_correct、收敛链件（sqrtf_sq_ge_a/iterate_sq_ge/step_contract/iterate_mono/lower/slack_contraction）与假设位诚实注记。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra。
   对标: 构造性平方根迭代（Bishop 构造主义的接口化版本）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

Section SqrtF.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let opp := @opp R RIS.
Let lt := @lt R RIS.
Let le := @le R RIS.
Let inv_pos := @inv_pos R RIS.

(* ============================================================ *)
(* §1 Newton 常数：two := 1+1、half := inv(two)                  *)
(*    （UpDebtSqrtAbsReq 同款本地重建，nsq_ 前缀防撞）            *)
(* ============================================================ *)

Definition nsq_two : R := plus one one.

Lemma nsq_two_pos : lt zero nsq_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition nsq_half : R := inv_pos nsq_two nsq_two_pos.

Lemma nsq_half_pos : lt zero nsq_half.
Proof. exact (inv_pos_pos nsq_two nsq_two_pos). Qed.

(* two·half == one（inv_pos_correct 直引——half 的定义性内核） *)
Lemma nsq_half_two_correct : req (mult nsq_two nsq_half) one.
Proof. exact (inv_pos_correct nsq_two nsq_two_pos). Qed.

(* ============================================================ *)
(* §2 Newton 单步：g(y) := half·(y + a·(1/y))                    *)
(*    正性：half > 0 且 y > 0 且 a·(1/y) > 0 ⟹ 和 > 0 ⟹ 积 > 0  *)
(* ============================================================ *)

Definition sqrtf_step (a y : R) (Ha : lt zero a) (Hy : lt zero y) : R :=
  mult nsq_half (plus y (mult a (inv_pos y Hy))).

Lemma sqrtf_step_pos : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  lt zero (sqrtf_step a y Ha Hy).
Proof.
  intros a y Ha Hy. unfold sqrtf_step.
  apply mult_positive.
  - exact nsq_half_pos.
  - apply plus_positive.
    + exact Hy.
    + apply mult_positive.
      * exact Ha.
      * apply inv_pos_pos.
Qed.

(* ============================================================ *)
(* §3 函数式 Newton 迭代（证明携带型依赖 Fixpoint）               *)
(*   sigT 组合（值, 正性见证），递归逐步产出——正性不变量与       *)
(*   函数本体同构生成，Set 层零 Prop 出面。                       *)
(* ============================================================ *)

Fixpoint sqrtf_newton_dep (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
         (n : nat) {struct n} : sigT (fun y : R => lt zero y) :=
  match n with
  | Datatypes.O => existT _ x Hx
  | Datatypes.S m =>
      match sqrtf_newton_dep a Ha x Hx m with
      | existT _ y Hy =>
          existT _ (sqrtf_step a y Ha Hy) (sqrtf_step_pos a y Ha Hy)
      end
  end.

(* 函数本体：n 步 Newton 迭代（n 为迭代精度控制参量） *)
Definition sqrtf_newton (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
           (n : nat) : R :=
  projT1 (sqrtf_newton_dep a Ha x Hx n).

(* 正性不变量：任意步迭代严格正（依赖 Fixpoint 第二分量直引）。
   透明 Definition 而非引理：正性见证进入迭代值位（inv_pos 的
   见证位是值位，proof-relevant——既有先例），规范见证必须
   delta 可导以与 Fixpoint 体内 witnesses conversion 对齐。 *)
Definition sqrtf_newton_pos (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
           (n : nat) : lt zero (sqrtf_newton a Ha x Hx n) :=
  projT2 (sqrtf_newton_dep a Ha x Hx n).

(* 迭代展开（健全性两件）：0 步返回初值；S n 步 = 单步作用于 n 步 *)
Lemma sqrtf_newton_zero : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x),
  req (sqrtf_newton a Ha x Hx 0) x.
Proof.
  intros a Ha x Hx. unfold sqrtf_newton.
  exact (req_refl x).
Qed.

Lemma sqrtf_newton_succ : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                 (n : nat),
  req (sqrtf_newton a Ha x Hx (Datatypes.S n))
      (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                   (sqrtf_newton_pos a Ha x Hx n)).
Proof.
  intros a Ha x Hx n.
  unfold sqrtf_newton, sqrtf_newton_pos.
  cbn [sqrtf_newton_dep projT1].
  destruct (sqrtf_newton_dep a Ha x Hx n) as [y Hy] eqn:E.
  exact (req_refl (sqrtf_step a y Ha Hy)).
Qed.

(* ============================================================ *)
(* §4 Newton 代数引擎（纯项式环代数，req 载体）                    *)
(*   核心恒等式：g(y)·g(y) == s(y)·s(y) + a，                     *)
(*   其中 s(y) := half·(y − a/y)（残差方幕：Newton 单步输出的      *)
(*   平方恰为 a 加一个完全方幕——有限步近似正确性的代数形态）。      *)
(* ============================================================ *)

(* 尾件：half·(X+X) == X（2·half == one 的直接推论） *)
Lemma nsq_tail : forall X : R, req (mult nsq_half (plus X X)) X.
Proof.
  intro X.
  apply (req_trans (mult nsq_half (plus X X))
                   (mult (mult nsq_half nsq_two) X)
                   X).
  - apply (req_trans (mult nsq_half (plus X X))
                     (mult nsq_half (mult nsq_two X))
                     (mult (mult nsq_half nsq_two) X)).
    + exact (req_mult_compat nsq_half nsq_half (plus X X) (mult nsq_two X)
               (req_refl nsq_half)
               (req_sym (mult nsq_two X) (plus X X) (req_two_mult X))).
    + exact (mult_assoc nsq_half nsq_two X).
  - apply (req_trans (mult (mult nsq_half nsq_two) X)
                     (mult one X)
                     X).
    + exact (req_mult_compat (mult nsq_half nsq_two) one X X
               (req_trans (mult nsq_half nsq_two) (mult nsq_two nsq_half) one
                          (mult_comm nsq_half nsq_two)
                          nsq_half_two_correct)
               (req_refl X)).
    + exact (req_trans (mult one X) (mult X one) X
                       (mult_comm one X) (mult_one X)).
Qed.

(* 广义单步差：(h·(p+q)) − (h·(p−q)) == h·(q+q)（req_minus 载体） *)
Lemma nsq_h_minus : forall h p q : R,
  req (req_minus (mult h (plus p q)) (mult h (plus p (opp q))))
      (mult h (plus q q)).
Proof.
  intros h p q. unfold req_minus.
  apply (req_trans (plus (mult h (plus p q)) (opp (mult h (plus p (opp q)))))
                   (mult h (plus (plus p q) (opp (plus p (opp q)))))
                   (mult h (plus q q))).
  - apply (req_trans (plus (mult h (plus p q)) (opp (mult h (plus p (opp q)))))
                     (plus (mult h (plus p q))
                           (mult h (opp (plus p (opp q)))))
                     (mult h (plus (plus p q) (opp (plus p (opp q)))))).
    + exact (req_plus_compat (mult h (plus p q)) (mult h (plus p q))
                             (opp (mult h (plus p (opp q))))
                             (mult h (opp (plus p (opp q))))
                             (req_refl (mult h (plus p q)))
                             (req_sym (mult h (opp (plus p (opp q))))
                                      (opp (mult h (plus p (opp q))))
                                      (req_opp_mult_l h (plus p (opp q))))).
    + exact (req_sym (mult h (plus (plus p q) (opp (plus p (opp q)))))
                     (plus (mult h (plus p q))
                           (mult h (opp (plus p (opp q)))))
                     (distrib h (plus p q) (opp (plus p (opp q))))).
  - exact (req_mult_compat h h
             (plus (plus p q) (opp (plus p (opp q)))) (plus q q)
             (req_refl h)
             (req_trans (plus (plus p q) (opp (plus p (opp q))))
                        (plus q (opp (opp q)))
                        (plus q q)
                        (req_minus_plus_congr p q (opp q))
                        (req_plus_compat q q (opp (opp q)) q
                           (req_refl q) (req_double_neg q)))).
Qed.

(* 广义单步和：(h·(p+q)) + (h·(p−q)) == h·(p+p) *)
Lemma nsq_h_plus : forall h p q : R,
  req (plus (mult h (plus p q)) (mult h (plus p (opp q))))
      (mult h (plus p p)).
Proof.
  intros h p q. unfold req_minus.
  apply (req_trans (plus (mult h (plus p q)) (mult h (plus p (opp q))))
                   (mult h (plus (plus p q) (plus p (opp q))))
                   (mult h (plus p p))).
  - exact (req_sym (mult h (plus (plus p q) (plus p (opp q))))
                   (plus (mult h (plus p q)) (mult h (plus p (opp q))))
                   (distrib h (plus p q) (plus p (opp q)))).
  - exact (req_mult_compat h h
             (plus (plus p q) (plus p (opp q))) (plus p p)
             (req_refl h)
             (req_trans (plus (plus p q) (plus p (opp q)))
                        (plus (plus p p) (plus q (opp q)))
                        (plus p p)
                        (req_plus_swap_mid p q p (opp q))
                        (req_trans (plus (plus p p) (plus q (opp q)))
                                   (plus (plus p p) zero)
                                   (plus p p)
                                   (req_plus_compat (plus p p) (plus p p)
                                      (plus q (opp q)) zero
                                      (req_refl (plus p p)) (plus_opp q))
                                   (plus_zero (plus p p))))).
Qed.

(* 广义极化恒等式：p·p == (p−q)·(p+q) + q·q（差平方分解） *)
Lemma nsq_polarization : forall p q : R,
  req (mult p p)
      (plus (mult (req_minus p q) (plus p q)) (mult q q)).
Proof.
  intros p q. unfold req_minus.
  assert (Hd : req (mult (plus p (opp q)) (plus p q))
                   (plus (mult p p) (opp (mult q q)))).
  { apply (req_trans
             (mult (plus p (opp q)) (plus p q))
             (plus (mult (plus p (opp q)) p) (mult (plus p (opp q)) q))
             (plus (mult p p) (opp (mult q q)))).
    - exact (distrib (plus p (opp q)) p q).
    - apply (req_trans
               (plus (mult (plus p (opp q)) p) (mult (plus p (opp q)) q))
               (plus (plus (mult p p) (opp (mult p q)))
                     (plus (mult q p) (opp (mult q q))))
               (plus (mult p p) (opp (mult q q)))).
      + apply (req_plus_compat
                 (mult (plus p (opp q)) p)
                 (plus (mult p p) (opp (mult p q)))
                 (mult (plus p (opp q)) q)
                 (plus (mult q p) (opp (mult q q)))
                 (req_trans (mult (plus p (opp q)) p)
                            (mult p (plus p (opp q)))
                            (plus (mult p p) (opp (mult p q)))
                            (mult_comm (plus p (opp q)) p)
                            (req_trans (mult p (plus p (opp q)))
                                       (plus (mult p p) (mult p (opp q)))
                                       (plus (mult p p) (opp (mult p q)))
                                       (distrib p p (opp q))
                                       (req_plus_compat (mult p p) (mult p p)
                                          (mult p (opp q)) (opp (mult p q))
                                          (req_refl (mult p p))
                                          (req_opp_mult_l p q))))
                 (req_trans (mult (plus p (opp q)) q)
                            (mult q (plus p (opp q)))
                            (plus (mult q p) (opp (mult q q)))
                            (mult_comm (plus p (opp q)) q)
                            (req_trans (mult q (plus p (opp q)))
                                       (plus (mult q p) (mult q (opp q)))
                                       (plus (mult q p) (opp (mult q q)))
                                       (distrib q p (opp q))
                                       (req_plus_compat (mult q p) (mult q p)
                                          (mult q (opp q)) (opp (mult q q))
                                          (req_refl (mult q p))
                                          (req_opp_mult_l q q))))).
      + apply (req_trans
                 (plus (plus (mult p p) (opp (mult p q)))
                       (plus (mult q p) (opp (mult q q))))
                 (plus (mult p p)
                       (plus (plus (opp (mult p q)) (mult q p))
                             (opp (mult q q))))
                 (plus (mult p p) (opp (mult q q)))).
        * exact (req_trans
                   (plus (plus (mult p p) (opp (mult p q)))
                         (plus (mult q p) (opp (mult q q))))
                   (plus (mult p p)
                         (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q)))))
                   (plus (mult p p)
                         (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q))))
                   (req_sym (plus (mult p p)
                                  (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q)))))
                            (plus (plus (mult p p) (opp (mult p q)))
                                  (plus (mult q p) (opp (mult q q))))
                            (plus_assoc (mult p p) (opp (mult p q))
                                        (plus (mult q p) (opp (mult q q)))))
                   (req_plus_compat (mult p p) (mult p p)
                      (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q))))
                      (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q)))
                      (req_refl (mult p p))
                      (plus_assoc (opp (mult p q)) (mult q p) (opp (mult q q))))).
        * apply (req_trans
                   (plus (mult p p)
                         (plus (plus (opp (mult p q)) (mult q p))
                               (opp (mult q q))))
                   (plus (mult p p) (plus zero (opp (mult q q))))
                   (plus (mult p p) (opp (mult q q)))).
          -- exact (req_plus_compat (mult p p) (mult p p)
                      (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q)))
                      (plus zero (opp (mult q q)))
                      (req_refl (mult p p))
                      (req_plus_compat (plus (opp (mult p q)) (mult q p)) zero
                         (opp (mult q q)) (opp (mult q q))
                         (req_trans (plus (opp (mult p q)) (mult q p))
                                    (plus (opp (mult p q)) (mult p q))
                                    zero
                                    (req_plus_compat (opp (mult p q)) (opp (mult p q))
                                       (mult q p) (mult p q)
                                       (req_refl (opp (mult p q)))
                                       (mult_comm q p))
                                    (req_trans (plus (opp (mult p q)) (mult p q))
                                               (plus (mult p q) (opp (mult p q)))
                                               zero
                                               (plus_comm (opp (mult p q)) (mult p q))
                                               (plus_opp (mult p q))))
                         (req_refl (opp (mult q q))))).
          -- exact (req_plus_compat (mult p p) (mult p p)
                       (plus zero (opp (mult q q))) (opp (mult q q))
                       (req_refl (mult p p))
                       (req_trans (plus zero (opp (mult q q)))
                                  (plus (opp (mult q q)) zero)
                                  (opp (mult q q))
                                  (plus_comm zero (opp (mult q q)))
                                  (plus_zero (opp (mult q q))))). }
  exact (req_sym
           (plus (mult (plus p (opp q)) (plus p q)) (mult q q))
           (mult p p)
           (req_trans (plus (mult (plus p (opp q)) (plus p q)) (mult q q))
                      (plus (plus (mult p p) (opp (mult q q))) (mult q q))
                      (mult p p)
                      (req_plus_compat (mult (plus p (opp q)) (plus p q))
                                       (plus (mult p p) (opp (mult q q)))
                                       (mult q q) (mult q q)
                                       Hd (req_refl (mult q q)))
                      (req_trans (plus (plus (mult p p) (opp (mult q q))) (mult q q))
                                 (plus (mult p p) (plus (opp (mult q q)) (mult q q)))
                                 (mult p p)
                                 (req_sym (plus (mult p p)
                                                (plus (opp (mult q q)) (mult q q)))
                                          (plus (plus (mult p p) (opp (mult q q)))
                                                (mult q q))
                                          (plus_assoc (mult p p) (opp (mult q q))
                                                      (mult q q)))
                                 (req_trans (plus (mult p p)
                                                  (plus (opp (mult q q)) (mult q q)))
                                            (plus (mult p p) zero)
                                            (mult p p)
                                            (req_plus_compat (mult p p) (mult p p)
                                               (plus (opp (mult q q)) (mult q q)) zero
                                               (req_refl (mult p p))
                                               (req_trans (plus (opp (mult q q)) (mult q q))
                                                          (plus (mult q q) (opp (mult q q)))
                                                          zero
                                                          (plus_comm (opp (mult q q)) (mult q q))
                                                          (plus_opp (mult q q))))
                                            (plus_zero (mult p p)))))).
Qed.

(* 交叉项：(a·(1/y))·y == a（inv_pos_correct 的换序使用） *)
Lemma nsq_u_mult_y : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  req (mult (mult a (inv_pos y Hy)) y) a.
Proof.
  intros a y Ha Hy.
  apply (req_trans (mult (mult a (inv_pos y Hy)) y)
                   (mult a (mult (inv_pos y Hy) y))
                   a).
  - exact (req_sym (mult a (mult (inv_pos y Hy) y))
                   (mult (mult a (inv_pos y Hy)) y)
                   (mult_assoc a (inv_pos y Hy) y)).
  - apply (req_trans (mult a (mult (inv_pos y Hy) y))
                     (mult a (mult y (inv_pos y Hy)))
                     a).
    + exact (req_mult_compat a a (mult (inv_pos y Hy) y) (mult y (inv_pos y Hy))
               (req_refl a) (mult_comm (inv_pos y Hy) y)).
    + apply (req_trans (mult a (mult y (inv_pos y Hy)))
                       (mult a one)
                       a).
      * exact (req_mult_compat a a (mult y (inv_pos y Hy)) one
                 (req_refl a) (inv_pos_correct y Hy)).
      * exact (req_trans (mult a one) (mult one a) a
                         (mult_comm a one)
                         (req_trans (mult one a) (mult a one) a
                                    (mult_comm one a) (mult_one a))).
Qed.

(* ============================================================ *)
(* §5 有限步近似正确性件                                          *)
(* ============================================================ *)

(* 残差项：s(y) := half·(y − a/y)（与 g(y) 配对的 slack 载体） *)
Definition sqrtf_slack (a y : R) (Ha : lt zero a) (Hy : lt zero y) : R :=
  mult nsq_half (plus y (opp (mult a (inv_pos y Hy)))).

(* 单步差：g(y) − s(y) == a/y *)
Lemma nsq_step_minus_slack : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  req (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
      (mult a (inv_pos y Hy)).
Proof.
  intros a y Ha Hy.
  exact (req_trans (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                   (mult nsq_half (plus (mult a (inv_pos y Hy)) (mult a (inv_pos y Hy))))
                   (mult a (inv_pos y Hy))
                   (nsq_h_minus nsq_half y (mult a (inv_pos y Hy)))
                   (nsq_tail (mult a (inv_pos y Hy)))).
Qed.

(* 单步和：g(y) + s(y) == y *)
Lemma nsq_step_plus_slack : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  req (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)) y.
Proof.
  intros a y Ha Hy.
  exact (req_trans (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                   (mult nsq_half (plus y y))
                   y
                   (nsq_h_plus nsq_half y (mult a (inv_pos y Hy)))
                   (nsq_tail y)).
Qed.

(* ============================================================ *)
(* §5 有限步近似正确性件（残差方幕恒等式）                         *)
(*   g(y)·g(y) == s(y)·s(y) + a：输出平方 = a + 完全方幕。         *)
(*   分解：p·p == (p−q)(p+q) + q·q（极化）⟹ 代入 p := g(y)、       *)
(*   q := s(y)，交叉项 (g−s)(g+s) == (a/y)·y == a。               *)
(* ============================================================ *)

Lemma sqrtf_step_residual : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  sigT (fun s : R =>
        req (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
            (plus (mult s s) a)).
Proof.
  intros a y Ha Hy.
  exists (sqrtf_slack a y Ha Hy).
  apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                               (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                         (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
  - exact (nsq_polarization (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)).
  - apply (req_trans
             (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                         (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (mult a (inv_pos y Hy)) y)
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
    + exact (req_plus_compat
               (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                     (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (mult (mult a (inv_pos y Hy)) y)
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (req_mult_compat
                  (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  (mult a (inv_pos y Hy))
                  (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  y
                  (nsq_step_minus_slack a y Ha Hy)
                  (nsq_step_plus_slack a y Ha Hy))
               (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + apply (req_trans
               (plus (mult (mult a (inv_pos y Hy)) y)
                     (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
      * exact (req_plus_compat (mult (mult a (inv_pos y Hy)) y) a
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (nsq_u_mult_y a y Ha Hy)
                 (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * exact (req_sym (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                       (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
Qed.

(* ============================================================ *)
(* §6 迭代统一证书 + 函数式平方根（主定理）                          *)
(* ============================================================ *)

(* 全步统一证书：第 S n 步迭代 z 满足 z·z == t·t + a（t 为残差项）。
   —— 有限步近似正确性：任意精度档位（n 越大残差越小，见段2骨架
   注记）下输出都带显式方幕型余量估计。 *)
Lemma sqrtf_newton_cert : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                (n : nat),
  sigT (fun t : R =>
        req (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                  (sqrtf_newton a Ha x Hx (Datatypes.S n)))
            (plus (mult t t) a)).
Proof.
  intros a Ha x Hx n.
  destruct (sqrtf_step_residual a (sqrtf_newton a Ha x Hx n) Ha
              (sqrtf_newton_pos a Ha x Hx n)) as [t Ht].
  exists t.
  apply (req_trans (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                         (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                   (mult (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n))
                         (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n)))
                   (plus (mult t t) a)).
  - exact (req_mult_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                           (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                           (sqrtf_newton_succ a Ha x Hx n)
                           (sqrtf_newton_succ a Ha x Hx n)).
  - exact Ht.
Qed.

(* 主定理（函数式平方根，U3 轴对位陈述）：给定 a > 0、初值 x > 0 与
   精度档 n，sqrtf_sqrt 产出三元组（值 r、正性见证、残差项 t），
   满足 r·r == t·t + a——与见证式 sqrt_witness（给定 r 验证 r·r == d）
   的对位：r 由 Fixpoint 构造性地算出，余量显式入账。
   嵌套 sigT 承载（正性位升第一见证位， 先例）。 *)
Definition sqrtf_sqrt (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x) (n : nat)
  : sigT (fun r : R =>
          sigT (fun _ : lt zero r =>
                sigT (fun t : R =>
                      req (mult r r) (plus (mult t t) a)))) :=
  existT _ (sqrtf_newton a Ha x Hx (Datatypes.S n))
    (existT _ (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
              (sqrtf_newton_cert a Ha x Hx n)).

(* 主定理自初值特化：x := a（a > 0 自充正性初值，签名收窄到 (a, Ha, n)） *)
Lemma sqrtf_sqrt_self_init : forall (a : R) (Ha : lt zero a) (n : nat),
  sigT (fun r : R =>
        sigT (fun _ : lt zero r =>
              sigT (fun t : R =>
                    req (mult r r) (plus (mult t t) a)))).
Proof.
  intros a Ha n.
  exact (existT _ (sqrtf_newton a Ha a Ha (Datatypes.S n))
           (existT _ (sqrtf_newton_pos a Ha a Ha (Datatypes.S n))
                     (sqrtf_newton_cert a Ha a Ha n))).
Qed.

(* ============================================================ *)
(* §7 段2：极限正确件 + 收敛证书骨架（阻塞裁决）                   *)
(* ============================================================ *)

(* 极限正确件：Newton 单步的不动点恰为平方根。
   z == g(z) ⟹ z·z == a——收敛证书一旦补全（z_n 的 Cauchy 性 + 极限
   传递），本件立即把极限值升格为真平方根，即 1/√d 绑定所缺的函数式
   半边。纯项式环代数（不动点方程两端乘 2 化简 + 乘消）。 *)
Lemma sqrtf_fixed_point_correct : forall (a z : R) (Ha : lt zero a) (Hz : lt zero z),
  req z (sqrtf_step a z Ha Hz) -> req (mult z z) a.
Proof.
  intros a z Ha Hz H.
  (* 第一步：不动点方程 ⟹ two·z == z + a·(1/z) *)
  assert (H2 : req (mult nsq_two z) (plus z (mult a (inv_pos z Hz)))).
  { apply (req_trans (mult nsq_two z)
                     (mult (mult nsq_two nsq_half)
                           (plus z (mult a (inv_pos z Hz))))
                     (plus z (mult a (inv_pos z Hz)))).
    - apply (req_trans (mult nsq_two z)
                       (mult nsq_two (sqrtf_step a z Ha Hz))
                       (mult (mult nsq_two nsq_half)
                             (plus z (mult a (inv_pos z Hz))))).
      + exact (req_mult_compat nsq_two nsq_two z (sqrtf_step a z Ha Hz)
                 (req_refl nsq_two) H).
      + exact (mult_assoc nsq_two nsq_half (plus z (mult a (inv_pos z Hz)))).
    - apply (req_trans (mult (mult nsq_two nsq_half) (plus z (mult a (inv_pos z Hz))))
                       (mult one (plus z (mult a (inv_pos z Hz))))
                       (plus z (mult a (inv_pos z Hz)))).
      + exact (req_mult_compat (mult nsq_two nsq_half) one
                 (plus z (mult a (inv_pos z Hz))) (plus z (mult a (inv_pos z Hz)))
                 (req_trans (mult nsq_two nsq_half) (mult nsq_half nsq_two) one
                            (mult_comm nsq_two nsq_half)
                            (req_trans (mult nsq_half nsq_two)
                                       (mult nsq_two nsq_half) one
                                       (mult_comm nsq_half nsq_two)
                                       nsq_half_two_correct))
                 (req_refl (plus z (mult a (inv_pos z Hz))))).
      + exact (req_trans (mult one (plus z (mult a (inv_pos z Hz))))
                         (mult (plus z (mult a (inv_pos z Hz))) one)
                         (plus z (mult a (inv_pos z Hz)))
                         (mult_comm one (plus z (mult a (inv_pos z Hz))))
                         (mult_one (plus z (mult a (inv_pos z Hz))))). }
  (* 第二步：z + z == z + a/z ⟹ z == a/z（req_plus_cancel_l） *)
  assert (Hzu : req z (mult a (inv_pos z Hz))).
  { apply (req_plus_cancel_l z z (mult a (inv_pos z Hz))).
    apply (req_trans (plus z z) (mult nsq_two z)
                     (plus z (mult a (inv_pos z Hz)))).
    - exact (req_sym (mult nsq_two z) (plus z z) (req_two_mult z)).
    - exact H2. }
  (* 第三步：z·z == z·(a/z) == a·(z·(1/z)) == a·one == a *)
  apply (req_trans (mult z z) (mult z (mult a (inv_pos z Hz))) a).
  - exact (req_mult_compat z z z (mult a (inv_pos z Hz))
             (req_refl z) Hzu).
  - apply (req_trans (mult z (mult a (inv_pos z Hz)))
                     (mult a (mult z (inv_pos z Hz)))
                     a).
    + apply (req_trans (mult z (mult a (inv_pos z Hz)))
                       (mult (mult z a) (inv_pos z Hz))
                       (mult a (mult z (inv_pos z Hz)))).
      * exact (mult_assoc z a (inv_pos z Hz)).
      * apply (req_trans (mult (mult z a) (inv_pos z Hz))
                         (mult (mult a z) (inv_pos z Hz))
                         (mult a (mult z (inv_pos z Hz)))).
        -- exact (req_mult_compat (mult z a) (mult a z) (inv_pos z Hz) (inv_pos z Hz)
                    (mult_comm z a) (req_refl (inv_pos z Hz))).
        -- exact (req_sym (mult a (mult z (inv_pos z Hz)))
                          (mult (mult a z) (inv_pos z Hz))
                          (mult_assoc a z (inv_pos z Hz))).
    + apply (req_trans (mult a (mult z (inv_pos z Hz)))
                       (mult a one)
                       a).
      * exact (req_mult_compat a a (mult z (inv_pos z Hz)) one
                 (req_refl a) (inv_pos_correct z Hz)).
      * exact (req_trans (mult a one) (mult one a) a
                         (mult_comm a one)
                         (req_trans (mult one a) (mult a one) a
                                    (mult_comm one a) (mult_one a))).
Qed.

(* ============================================================ *)
(* 【段2 骨架与阻塞裁决——收敛证书（未完成，诚实显式假设）】            *)
(*                                                              *)
(* 目标语句（接口原生 Bishop 逐 eps 形，与 cauchy_complete 前提   *)
(* 同构，供后续完成后直接喂完备性字段）：                         *)
(*   Lemma sqrtf_newton_cauchy : forall (a : R) (Ha : lt zero a)   *)
(*     (x : R) (Hx : lt zero x) (eps : R), lt zero eps ->          *)
(*     sigT (fun N : nat => forall m n : nat, NatLe N m ->         *)
(*       NatLe N n -> lt (metric (sqrtf_newton a Ha x Hx m)        *)
(*                                (sqrtf_newton a Ha x Hx n)) eps).*)
(*                                                              *)
(* 证明计划（三步）：                                             *)
(*  (1) 残差方幕链：本件 §5 恒等式给出 z_{n+1}·z_{n+1} == a +      *)
(*      t_n·t_n，t_n := s(z_n) := half·(z_n − a/z_n)；且           *)
(*      t_{n+1} == t_n·t_n / (2·z_{n+1})（同极化分解的比率形式）。  *)
(*  (2) 压缩界：z_{n} ≥ m > 0（正性不变量 + 下界槽）⟹              *)
(*      |t_{n+1}| ≤ |t_n|²/(2m) ⟹ 几何收敛 ⟹ 逐 eps Cauchy。       *)
(*  (3) 极限升格：Cauchy + cauchy_complete 出极限 l，              *)
(*      sqrtf_fixed_point_correct（本件 §7）经 req 兼容传递得       *)
(*      l·l == a——函数式平方根闭环。                              *)
(*                                                              *)
(* 阻塞裁决：第 (2) 步的「残差非负/方幕保序」在本接口层不可构造——    *)
(*   le zero (mult t t)（平方非负）不是接口定理：库内 GRPO *)
(*   square_nonneg 同位先例保持显式假设位（UpReqDist 头注登记表第 6   *)
(*   条），接口无 le↔Or 分解字段亦无 lt 三分（经典公理已移除，      *)
(*   L173-176 自述）。两条消解路线留后续工作：               *)
(*   (a) 假设位路线：节内立诚实 Hypothesis nsq_square_nonneg       *)
(*       （le zero (mult t t)），Real 实例可消解；                  *)
(*   (b) 具体层路线：real_abs 族（L13473 逐点 Qabs + 柯西）   *)
(*       具体层证 |x|·|x| == x·x 且 abs ≥ 0，经实例化特化消解。     *)
(* 本件已就位的段2 资产：sqrtf_fixed_point_correct（极限正确件，    *)
(*   已完成）+ §5 残差方幕恒等式（压缩链代数核心，已完成）          *)
(*   + §8 收敛链件（残差非负使用/平方下界/单调/一致下界/压缩比率     *)
(*   恒等式——假设位诚实形，见 §8 头注修正补注）。                    *)
(* ============================================================ *)

(* ============================================================ *)
(* §8 段2 收敛链（增量完成）——路线 (a) 诚实槽 + 压缩比率恒等式      *)
(*                                                              *)
(* 件清单：                                                       *)
(*  - nsq_square_nonneg：诚实槽（路线 (a)，GRPO square_nonneg  *)
(*    同位先例 UpReqDist 登记表 6；节内立槽泛化为引理显式前提位，      *)
(*    Print Assumptions 仍 Closed 零公理面）；                      *)
(*  - sqrtf_sq_ge_a：残差非负使用件（槽 + §5 恒等式 ⟹ g(y)^2 ≥ a，  *)

(*  - sqrtf_iterate_sq_ge：全迭代平方下界 z_{S n}^2 ≥ a；           *)
(*  - sqrtf_inv_le_self：平方下界换倒数上界 a·(1/z) ≤ z；           *)
(*  - sqrtf_step_contract：单步 le 压缩 g(y) ≤ y；                  *)
(*  - sqrtf_iterate_mono_step / _from1：迭代自 z_1 起单调不增；      *)
(*  - sqrtf_iterate_lower：一致下界 m0 := a·(1/z_1) ≤ z_n（n ≥ 1）；*)
(*  - nsq_two_slack + nsq_slack_contraction：压缩比率恒等式          *)
(*    2·g(y)·s(g(y)) == s(y)·s(y)（证明计划步 (1) 比率形式完成）。   *)
(*                                                              *)
(* 假设位裁决修正补注：plain 形 le zero (mult t t) 在 Real 层亦不可    *)
(* 消解——RealEnhancedReal 的 le := real_le 为 Or (real_lt)          *)
(* (real_eq) 编码（实例段），t_n^2 无一致正尾部时两支皆假      *)
(* （t := 1/n 序列形反例）；接口 abs 族字段亦不敷用（|t|·|t| 与      *)
(* t·t 无 req 桥：符号不可判定且接口无分解字段）。故该槽是收敛链     *)
(* 的不可消去诚实前提位；路线 (b) 可行残形=具体层逐点重造（Q 层      *)
(* Qsquare_nonneg 同位，L44850 real_square_nonneg_eps 即       *)
(* Bishop eps 形同类件），留后续工作。                              *)
(*                                                              *)
(* 尾程显式假设（精确余量）：Cauchy 证书全件 = 压缩比率恒等式（本节       *)
(* 已完成）+「存在 K: |s(z_K)| ≤ m0」（取档步，需阿基米德同位槽）     *)
(* + 几何尾和逐 eps 上界（metric 尾和三角迭代，metric_abs 桥槽）     *)
(* 三段组装；余段留待后续。                                        *)
(* ============================================================ *)

Hypothesis nsq_square_nonneg : forall t : R, le zero (mult t t).

(* 残差非负使用件：s(y)^2 ≥ 0（槽）经 §5 恒等式 ⟹ g(y)^2 ≥ a。
   le_plus_compat（槽注入 a 侧）+ req 运输（plus zero a ~ a、
   g·g ~ s^2 + a）三项式组装。 *)
Lemma sqrtf_sq_ge_a : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  le a (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)).
Proof.
  intros a y Ha Hy.
  destruct (sqrtf_step_residual a y Ha Hy) as [s Hs].
  exact (req_le_compat (plus zero a) a
                       (plus (mult s s) a)
                       (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                       (req_plus_zero_l a)
                       (req_sym (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                (plus (mult s s) a)
                                Hs)
                       (le_plus_compat zero (mult s s) a a
                          (nsq_square_nonneg s) (le_refl a))).
Qed.

(* 全迭代平方下界：z_{S n}^2 ≥ a（succ 展开 req 运输 + 上件） *)
Lemma sqrtf_iterate_sq_ge : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                  (n : nat),
  le a (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
             (sqrtf_newton a Ha x Hx (Datatypes.S n))).
Proof.
  intros a Ha x Hx n.
  apply (req_le_compat a a
           (mult (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                 (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                             (sqrtf_newton_pos a Ha x Hx n)))
           (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                 (sqrtf_newton a Ha x Hx (Datatypes.S n)))
           (req_refl a)
           (req_mult_compat (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                          (sqrtf_newton_pos a Ha x Hx n))
                            (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                         (sqrtf_newton_pos a Ha x Hx n))
                            (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha (sqrtf_newton_pos a Ha x Hx n)) (sqrtf_newton_succ a Ha x Hx n))
                            (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha (sqrtf_newton_pos a Ha x Hx n)) (sqrtf_newton_succ a Ha x Hx n)))).
  exact (sqrtf_sq_ge_a a (sqrtf_newton a Ha x Hx n) Ha
           (sqrtf_newton_pos a Ha x Hx n)).
Qed.

(* 平方下界换倒数上界：a ≤ z·z ⟹ a·(1/z) ≤ z
   （左乘 1/z > 0 + inv_pos_correct 收尾：1/z·(z·z) ~ (1/z·z)·z ~ 1·z ~ z） *)
Lemma sqrtf_inv_le_self : forall (a z : R) (Ha : lt zero a) (Hz : lt zero z),
  le a (mult z z) -> le (mult a (inv_pos z Hz)) z.
Proof.
  intros a z Ha Hz H.
  apply (le_trans (mult a (inv_pos z Hz))
                  (mult (mult z z) (inv_pos z Hz))
                  z).
  - exact (le_mult_compat a (mult z z) (inv_pos z Hz) (inv_pos_pos z Hz) H).
  - exact (req_le_compat (mult (mult z z) (inv_pos z Hz))
                         (mult (mult z z) (inv_pos z Hz))
                         (mult (mult z z) (inv_pos z Hz))
                         z
           (req_refl (mult (mult z z) (inv_pos z Hz)))
           (req_trans (mult (mult z z) (inv_pos z Hz))
                      (mult z (mult z (inv_pos z Hz)))
                      z
                      (req_sym (mult z (mult z (inv_pos z Hz)))
                               (mult (mult z z) (inv_pos z Hz))
                               (mult_assoc z z (inv_pos z Hz)))
                      (req_trans (mult z (mult z (inv_pos z Hz)))
                                 (mult z one)
                                 z
                                 (req_mult_compat z z (mult z (inv_pos z Hz)) one
                                    (req_refl z)
                                    (inv_pos_correct z Hz))
                                 (mult_one z)))
           (le_refl (mult (mult z z) (inv_pos z Hz)))).
Qed.

(* 单步 le 压缩：a ≤ y·y ⟹ g(y) ≤ y
   （g(y) = half·(y + a/y) ≤ half·(y + y) == y，末步 nsq_tail） *)
Lemma sqrtf_step_contract : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  le a (mult y y) -> le (sqrtf_step a y Ha Hy) y.
Proof.
  intros a y Ha Hy H.
  apply (le_trans (sqrtf_step a y Ha Hy)
                  (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                  y).
  - exact (le_refl (sqrtf_step a y Ha Hy)).
  - apply (le_trans (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                    (mult nsq_half (plus y y))
                    y).
    + exact (req_le_compat (mult (plus y (mult a (inv_pos y Hy))) nsq_half)
                           (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                           (mult (plus y y) nsq_half)
                           (mult nsq_half (plus y y))
             (mult_comm (plus y (mult a (inv_pos y Hy))) nsq_half)
             (mult_comm (plus y y) nsq_half)
             (le_mult_compat (plus y (mult a (inv_pos y Hy))) (plus y y) nsq_half
                nsq_half_pos
                (le_plus_compat y y (mult a (inv_pos y Hy)) y
                   (le_refl y) (sqrtf_inv_le_self a y Ha Hy H)))).
    + exact (req_le_compat (mult nsq_half (plus y y))
                           (mult nsq_half (plus y y))
                           (mult nsq_half (plus y y))
                           y
               (req_refl (mult nsq_half (plus y y)))
               (nsq_tail y)
               (le_refl (mult nsq_half (plus y y)))).
Qed.

(* 迭代单调（单步）：z_{S (S n)} ≤ z_{S n}（使用 z_{S n}^2 ≥ a） *)
Lemma sqrtf_iterate_mono_step : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                       (n : nat),
  le (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intros a Ha x Hx n.
  apply (req_le_compat (sqrtf_step a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
                                    (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                       (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
           (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                    (sqrtf_step a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
                                 (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                    (sqrtf_newton_succ a Ha x Hx (Datatypes.S n)))
           (req_refl (sqrtf_newton a Ha x Hx (Datatypes.S n)))).
  exact (sqrtf_step_contract a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
           (sqrtf_iterate_sq_ge a Ha x Hx n)).
Qed.

(* 迭代单调（自 z_1 起一致）：z_{S n} ≤ z_1（归纳 + 单步传递） *)
Lemma sqrtf_iterate_mono_from1 : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                        (n : nat),
  le (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton a Ha x Hx 1).
Proof.
  intros a Ha x Hx n. induction n as [| n IH].
  - exact (le_refl (sqrtf_newton a Ha x Hx 1)).
  - apply (le_trans (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                    (sqrtf_newton a Ha x Hx (Datatypes.S n))
                    (sqrtf_newton a Ha x Hx 1)).
    + exact (sqrtf_iterate_mono_step a Ha x Hx n).
    + exact IH.
Qed.

(* 一致下界：m0 := a·(1/z_1) ≤ z_n 对一切 n ≥ 1
   （z_n ≤ z_1 ⟹ 1/z_1 ≤ 1/z_n（inv 反序）⟹ a/z_1 ≤ a/z_n ≤ z_n
     （末步 = 平方下界换倒数上界）） *)
Lemma sqrtf_iterate_lower : forall (a : R) (Ha : lt zero a) (x : R) (Hx : lt zero x)
                                   (n : nat),
  le (mult a (inv_pos (sqrtf_newton a Ha x Hx 1)
                      (sqrtf_newton_pos a Ha x Hx 1)))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intros a Ha x Hx n.
  apply (le_trans (mult a (inv_pos (sqrtf_newton a Ha x Hx 1)
                                   (sqrtf_newton_pos a Ha x Hx 1)))
                  (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                  (sqrtf_newton a Ha x Hx (Datatypes.S n))).
  - apply (req_le_compat
             (mult (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1)) a)
             (mult a (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1)))
             (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))) a)
             (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                              (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
             (mult_comm (inv_pos (sqrtf_newton a Ha x Hx 1)
                                 (sqrtf_newton_pos a Ha x Hx 1)) a)
             (mult_comm (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                 (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))) a)).
    exact (le_mult_compat
             (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1))
             (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
             a Ha
             (inv_pos_le_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                (sqrtf_newton a Ha x Hx 1)
                                (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
                                (sqrtf_newton_pos a Ha x Hx 1)
                                (sqrtf_iterate_mono_from1 a Ha x Hx n))).
  - exact (sqrtf_inv_le_self a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
             (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
             (sqrtf_iterate_sq_ge a Ha x Hx n)).
Qed.

(* 尾件：nsq_two·s(u) == u − a/u（2·half == one 的 slack 形直推，
   2·(half·w) ~ (2·half)·w ~ 1·w ~ w，delta 使用 sqrtf_slack 定义形） *)
Lemma nsq_two_slack : forall (a u : R) (Ha : lt zero a) (Hu : lt zero u),
  req (mult nsq_two (sqrtf_slack a u Ha Hu))
      (plus u (opp (mult a (inv_pos u Hu)))).
Proof.
  intros a u Ha Hu.
  apply (req_trans (mult nsq_two (sqrtf_slack a u Ha Hu))
                   (mult (mult nsq_two nsq_half)
                         (plus u (opp (mult a (inv_pos u Hu)))))
                   (plus u (opp (mult a (inv_pos u Hu))))).
  - exact (mult_assoc nsq_two nsq_half (plus u (opp (mult a (inv_pos u Hu))))).
  - apply (req_trans (mult (mult nsq_two nsq_half)
                           (plus u (opp (mult a (inv_pos u Hu)))))
                     (mult one (plus u (opp (mult a (inv_pos u Hu)))))
                     (plus u (opp (mult a (inv_pos u Hu))))).
    + exact (req_mult_compat (mult nsq_two nsq_half) one
               (plus u (opp (mult a (inv_pos u Hu))))
               (plus u (opp (mult a (inv_pos u Hu))))
               (req_trans (mult nsq_two nsq_half) (mult nsq_half nsq_two) one
                          (mult_comm nsq_two nsq_half)
                          (req_trans (mult nsq_half nsq_two)
                                     (mult nsq_two nsq_half)
                                     one
                                     (mult_comm nsq_half nsq_two)
                                     nsq_half_two_correct))
               (req_refl (plus u (opp (mult a (inv_pos u Hu)))))).
    + exact (req_mult_one_l (plus u (opp (mult a (inv_pos u Hu))))).
Qed.

(* §5 恒等式的非 sigT 直述形（见证= sqrtf_slack 内联，供收敛链使用；
   §5 原件的 req 链逐字副本） *)
Lemma nsq_step_residual_req : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  req (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
      (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a).
Proof.
  intros a y Ha Hy.
  apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                               (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                         (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
  - exact (nsq_polarization (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)).
  - apply (req_trans
             (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                         (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (mult a (inv_pos y Hy)) y)
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
    + exact (req_plus_compat
               (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                     (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (mult (mult a (inv_pos y Hy)) y)
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (req_mult_compat
                  (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  (mult a (inv_pos y Hy))
                  (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  y
                  (nsq_step_minus_slack a y Ha Hy)
                  (nsq_step_plus_slack a y Ha Hy))
               (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + apply (req_trans
               (plus (mult (mult a (inv_pos y Hy)) y)
                     (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
      * exact (req_plus_compat (mult (mult a (inv_pos y Hy)) y) a
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (nsq_u_mult_y a y Ha Hy)
                 (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * exact (req_sym (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                       (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
Qed.

(* 压缩比率恒等式（收敛链核心件，证明计划步 (1) 的比率形式）：
   2·g(y)·s(g(y)) == s(y)·s(y)。
   代数：2·u·s(u) == u·(u − a/u) == u·u + opp a（交叉项 u·(a/u) == a，
   nsq_u_mult_y 换序使用）⟹ 2·u·s(u) + a == u·u == s(y)^2 + a
   （§5 恒等式）⟹ 加 a 抵消（req_plus_cancel_l）。 *)
Lemma nsq_slack_contraction : forall (a y : R) (Ha : lt zero a) (Hy : lt zero y),
  req (mult (mult nsq_two (sqrtf_step a y Ha Hy))
            (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha (sqrtf_step_pos a y Ha Hy)))
      (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)).
Proof.
  intros a y Ha Hy.
  pose proof (nsq_step_residual_req a y Ha Hy) as Hres.
  set (Hu := sqrtf_step_pos a y Ha Hy) in *.
  (* 支路 A：2·u·s_u == u·u + opp a *)
  assert (HA : req (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                         (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                   (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                         (opp a))).
  { apply (req_trans
             (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                   (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
             (mult (sqrtf_step a y Ha Hy)
                   (plus (sqrtf_step a y Ha Hy)
                         (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
             (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (opp a))).
    - apply (req_trans
               (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                     (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
               (mult (sqrtf_step a y Ha Hy)
                     (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
               (mult (sqrtf_step a y Ha Hy)
                     (plus (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))).
      + apply (req_trans
                 (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                       (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (mult (mult (sqrtf_step a y Ha Hy) nsq_two)
                       (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (mult (sqrtf_step a y Ha Hy)
                       (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))).
        * exact (req_mult_compat (mult nsq_two (sqrtf_step a y Ha Hy))
                    (mult (sqrtf_step a y Ha Hy) nsq_two)
                    (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)
                    (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)
                    (mult_comm nsq_two (sqrtf_step a y Ha Hy))
                    (req_refl (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
        * exact (req_sym (mult (sqrtf_step a y Ha Hy)
                               (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
                         (mult (mult (sqrtf_step a y Ha Hy) nsq_two)
                               (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                         (mult_assoc (sqrtf_step a y Ha Hy) nsq_two
                                     (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
      + exact (req_mult_compat (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)
                 (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (plus (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                 (req_refl (sqrtf_step a y Ha Hy))
                 (nsq_two_slack a (sqrtf_step a y Ha Hy) Ha Hu)).
    - apply (req_trans
               (mult (sqrtf_step a y Ha Hy)
                     (plus (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
               (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                     (mult (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
               (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                     (opp a))).
      + exact (distrib (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))).
      + exact (req_plus_compat (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                 (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                 (mult (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                 (opp a)
                 (req_refl (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)))
                 (req_trans (mult (sqrtf_step a y Ha Hy)
                                  (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                            (opp (mult (sqrtf_step a y Ha Hy)
                                       (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                            (opp a)
                            (req_opp_mult_l (sqrtf_step a y Ha Hy)
                                            (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                            (req_opp_compat (mult (sqrtf_step a y Ha Hy)
                                                  (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                            a
                                            (req_trans (mult (sqrtf_step a y Ha Hy)
                                                             (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                                       (mult (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))
                                                             (sqrtf_step a y Ha Hy))
                                                       a
                                                       (mult_comm (sqrtf_step a y Ha Hy)
                                                                  (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                                       (nsq_u_mult_y a (sqrtf_step a y Ha Hy) Ha Hu))))) . }
  (* 汇合：a + 2us == a + u·u == a + s(y)²（req_plus_cancel_l 抵消左侧 a） *)
  apply (req_plus_cancel_l a
           (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
           (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))).
  apply (req_trans (plus a (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
                   (plus (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                               (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)) a)
                   (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
  - exact (plus_comm a (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                             (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
  - apply (req_trans (plus (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)) a)
                     (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                     (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + exact (req_plus_compat (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                   (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                             (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a))
                             a a HA (req_refl a)).
    + apply (req_trans (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                       (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * apply (req_trans (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                         (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (plus (opp a) a))
                         (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
        -- exact (req_sym (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                (plus (opp a) a))
                          (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                          (plus_assoc (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                      (opp a) a)).
        -- apply (req_trans (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                  (plus (opp a) a))
                            (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) zero)
                            (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
           ++ exact (req_plus_compat (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                        (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                        (plus (opp a) a) zero
                                        (req_refl (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)))
                                        (req_plus_opp_l a)).
           ++ exact (plus_zero (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
      * apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                         (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                         (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
        -- exact Hres.
        -- exact (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a).
Qed.

End SqrtF.

(* （ToyR 增补·非原件改动）假设面闭合申报节：玩具面逐件申报，
    全 Closed 为结论标识；基准对照件以同文申报节同法试编比对。 *)
Print Assumptions nsq_two_pos.
Print Assumptions nsq_half_pos.
Print Assumptions nsq_half_two_correct.
Print Assumptions sqrtf_newton_zero.
Print Assumptions nsq_step_minus_slack.
Print Assumptions nsq_step_plus_slack.
Print Assumptions sqrtf_sqrt_self_init.
Print Assumptions sqrtf_iterate_sq_ge.
Print Assumptions sqrtf_inv_le_self.
Print Assumptions sqrtf_step_contract.
Print Assumptions sqrtf_iterate_mono_step.