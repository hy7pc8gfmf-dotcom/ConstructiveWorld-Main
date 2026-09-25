(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpGeomB.v *)
(* *)
(* 目的： 策略迭代几何收缩的 Bishop 形无条件版（定理 4.8 对应物）。 *)
(* 主件： geod_b_iterate 迭代族与 geod_b_kappa_lt_one；geod_b_interp_Z_pos 插值正性。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpReqGeomD。 *)
(* 备注： real_le 的 Or 形前提仅被构造性消耗（两支皆有见证）；无条件指无额外 eps 假设位。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpGeomB.v —— 定理 4.8 策略迭代几何收缩的 Bishop     *)
(*   （广义主定理链·评审 07 点名「最能提升的单一改动」落盘件）           *)
(* ---------------------------------------------------------------- *)
(* 数学目标：策略迭代几何收缩的无条件 Bishop 形（le_b 序语言）：        *)
(*   KL(π*‖π_{t+1}) ≤_B (1−η)·KL(π*‖π_t)        （主件1·单步）        *)
(*   KL(π*‖π_t)   ≤_B (1−η)^t·KL(π*‖π_0)       （主件2·迭代·主定理）    *)
(* 关键：Or-序编码下 step_kl_eta_bound 的「log Z ≤ 0 精确形」不可证    *)
(*   （等号分支提取需排中）——Bishop 形绕开：逐 eps 余量替代精确       *)
(*   不等式，严格 lt 见证替代 eq 分支。全文件零 Or 形精确完成目标，     *)
(*   前提位 Or 假设（real_le）仅被构造性消耗（destruct 两支皆有 witness   *)
(*   路线），与 UpRealLeB.real_le_to_le_b 单向桥同纪律。              *)
(* ---------------------------------------------------------------- *)
(* 本文件结果（前缀 geod_b_，grep 全库零撞名实测）：                   *)
(*   [P-A 序/环辅件] geod_b_le_lt_trans（le+lt 拼接）/                 *)
(*     geod_b_kappa_lt_one（η>0 ⟹ 1−η<1 严格）/ geod_b_ring_mlcr /    *)
(*     geod_b_scale_reshape（零名依赖 ring 换形）/                     *)
(*     geod_b_half_double（(1+1)·i==1 ⟹ e·i+e·i==e——eps 半量机）。     *)
(*   [P-B 主定理 geod_b_eta_pow] geod_b_pow（(1−η)^t 幂载体 Fixpoint）+  *)
(*     geod_b_pow_pos（正性保持）+ geod_b_pow_mono_decr（单调递减      *)
(*     的 Bishop 序版：0<x≤1 ⟹ x^{t+1} ≤_B x^t）。                     *)
(*   [P-C 语义件] geod_b_kl_sum（KL 和载体）/ geod_b_interp_Z_pos /    *)
(*     geod_b_step_next_pos / geod_b_step_next_norm（下一步策略三证书： *)
(*     正性/归一化——迭代轨道自足供给）/ geod_b_iterate（sigT 封装      *)
(*     迭代 Fixpoint，正性+归一化内嵌，policy_iterate 同构）。          *)
(*   [P-D 保底件] geod_b_step_kl_eps——单步 KL 收缩 Bishop 形          *)
(*     KL(π_t‖π_{t+1}) ≤_B η·KL(π_t‖π★)——55 引擎                    *)
(*     real_step_kl_eta_bound_B 一次喂定（核验后 Require 使用）。      *)
(*   [P-E 主件1] geod_b_policy_iter_step_margin（逐 eps 严格余量       *)
(*     辅助引理：三 KL 恒等式的逐点对偶 kl(r,q)==(1−η)·kl(r,p)+r·log Z   *)

(*     geod_b_policy_iter_step（Bishop 完成：KL(π*‖π_{t+1}) ≤_B        *)
(*     (1−η)·KL(π*‖π_t)，real_le_closure_b_one 一步）。                *)
(*   [P-F 主件2·主定理] geod_b_policy_iter_iter——t 步几何收缩 Bishop 形： *)
(*     KL(π*‖π_t) ≤_B (1−η)^t·KL(π*‖π_0)（le_b 归纳；eps 累积=         *)
(*     逐 eps 半量分配 h+（1−η)h < 2h == eps，免 1/n 拆分——SumD        *)
(*     先例同款）。                                                    *)
(* ---------------------------------------------------------------- *)

(*   real_eq_mult_compat 未前缀），当前盘上 UpReqGeomD.v 已是前缀修     *)
(*   正版且 .vo/.glob 同刻新——非阻塞，仅日志未刷新。                   *)
(* 红线：Set 层语句（real_le_b/real_lt 均 Set 值；nat 层 0<n 前提为    *)
(*   Prop——real_list_sum_pos 先例同格）；全 Qed 闭合；既有文件零改；   *)
(*   纯 term-mode 组装（real_eq 非 Id，禁 rewrite 主链）。             *)

(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqGeomD.

(* ============================================================ *)
(* P-A 序/环辅件                                                      *)
(* ============================================================ *)

(* le + lt 拼接：x ≤ y < z ⟹ x < z（Or 编码前提两支各取 witness 路线） *)
Lemma geod_b_le_lt_trans : forall x y z : Real,
  real_le x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt. unfold real_le in Hle.
  destruct Hle as [Hlt' | Heq].
  - exact (real_lt_trans x y z Hlt' Hlt).
  - exact (real_eq_lt_lt x y z Heq Hlt).
Qed.

(* η > 0 ⟹ 1−η < 1（严格；geod_kappa_le_one 的严格孪生） *)
Lemma geod_b_kappa_lt_one : forall eta : Real,
  real_lt real_zero eta ->
  real_lt (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
  (* m == m+0 < m+eta == eta+m == 1 *)
  apply (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus (real_plus real_one (real_opp eta)) real_zero) real_one).
  - exact (real_eq_sym _ _
             (real_plus_zero (real_plus real_one (real_opp eta)))).
  - apply (real_lt_eq_lt
             (real_plus (real_plus real_one (real_opp eta)) real_zero)
             (real_plus (real_plus real_one (real_opp eta)) eta) real_one).
    + exact (real_lt_plus_translate (real_plus real_one (real_opp eta))
                real_zero eta Hpos).
    + exact (real_eq_trans
               (real_plus (real_plus real_one (real_opp eta)) eta)
               (real_plus eta (real_plus real_one (real_opp eta))) real_one
               (real_plus_comm (real_plus real_one (real_opp eta)) eta)
               (geod_eta_plus_kappa eta)).
Qed.

(* 环辅件：kl_ring_neg4 的换向对偶（m := 1−η 内嵌）：
   −((m·lp + η·lr) + (−LZ + −lr)) == m·(lr − lp) + LZ *)
Lemma geod_b_ring_neg4_b : forall eta lp lr LZ : Real,
  real_eq (real_opp (real_plus
                       (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                  (real_mult eta lr))
                       (real_plus (real_opp LZ) (real_opp lr))))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                                (real_plus lr (real_opp lp))) LZ).
Proof.
  intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

(* 环辅件：关联重排（换向对偶，kk 任意实——终点为 −lr 而非 −lp）：
   kk·lp + (η·lr + (−LZ + −lr)) == (kk·lp + η·lr) + (−LZ + −lr) *)
Lemma geod_b_ring_log4_b : forall kk eta lp lr LZ : Real,
  real_eq (real_plus (real_mult kk lp)
                     (real_plus (real_mult eta lr)
                                (real_plus (real_opp LZ) (real_opp lr))))
          (real_plus (real_plus (real_mult kk lp) (real_mult eta lr))
                     (real_plus (real_opp LZ) (real_opp lr))).
Proof.
  intros kk eta lp lr LZ. destruct kk as [a Ha]. destruct eta as [e He].
  destruct lp as [u Hu]. destruct lr as [v Hv]. destruct LZ as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环辅件：乘积重排 i·(e·X) == X·(i·e)（零名依赖，pointwise ring） *)
Lemma geod_b_ring_mlcr : forall i e X : Real,
  real_eq (real_mult i (real_mult e X)) (real_mult X (real_mult i e)).
Proof.
  intros i e X. destruct i as [fi Hi]. destruct e as [fe He].
  destruct X as [fx Hx]. apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环辅件：单步缩放换形 m·(X·KL + h) == (m·X)·KL + m·h *)
Lemma geod_b_scale_reshape : forall m X KL0 h : Real,
  real_eq (real_mult m (real_plus (real_mult X KL0) h))
          (real_plus (real_mult (real_mult m X) KL0) (real_mult m h)).
Proof.
  intros m X KL0 h. destruct m as [fm Hm]. destruct X as [fx Hx].
  destruct KL0 as [fk Hk]. destruct h as [fh Hh].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 半量机：(1+1)·i == 1 ⟹ e·i + e·i == e（eps 半量分配的环核；
   real_inv_pos 为柯西倒数、逐点非恒等，故走 real-eq 代数链非 pointwise） *)
Lemma geod_b_half_double : forall e i : Real,
  real_eq (real_mult (real_plus real_one real_one) i) real_one ->
  real_eq (real_plus (real_mult e i) (real_mult e i)) e.
Proof.
  intros e i H.
  apply (real_eq_trans
           (real_plus (real_mult e i) (real_mult e i))
           (real_mult i (real_plus e e)) e).
  - apply (real_eq_trans
             (real_plus (real_mult e i) (real_mult e i))
             (real_plus (real_mult i e) (real_mult i e))
             (real_mult i (real_plus e e))).
    + exact (RealSetoid.real_eq_plus_compat (real_mult e i) (real_mult e i)
               (real_mult i e) (real_mult i e)
               (real_mult_comm e i) (real_mult_comm e i)).
    + exact (real_eq_sym _ _ (real_distrib i e e)).
  - apply (real_eq_trans
             (real_mult i (real_plus e e))
             (real_mult i (real_mult e (real_plus real_one real_one))) e).
    + exact (RealSetoid.real_eq_mult_compat i (real_plus e e) i
               (real_mult e (real_plus real_one real_one))
               (real_eq_refl i)
               (real_eq_trans (real_plus e e)
                  (real_plus (real_mult e real_one) (real_mult e real_one))
                  (real_mult e (real_plus real_one real_one))
                  (RealSetoid.real_eq_plus_compat e e
                     (real_mult e real_one) (real_mult e real_one)
                     (real_eq_sym _ _ (real_mult_one e))
                     (real_eq_sym _ _ (real_mult_one e)))
                  (real_eq_sym _ _ (real_distrib e real_one real_one)))).
    + apply (real_eq_trans
               (real_mult i (real_mult e (real_plus real_one real_one)))
               (real_mult (real_plus real_one real_one) (real_mult i e)) e).
      * exact (geod_b_ring_mlcr i e (real_plus real_one real_one)).
      * apply (real_eq_trans
                 (real_mult (real_plus real_one real_one) (real_mult i e))
                 (real_mult (real_mult (real_plus real_one real_one) i) e) e).
      -- exact (real_mult_assoc (real_plus real_one real_one) i e).
      -- apply (real_eq_trans
                   (real_mult (real_mult (real_plus real_one real_one) i) e)
                   (real_mult real_one e) e).
         ++ exact (RealSetoid.real_eq_mult_compat
                     (real_mult (real_plus real_one real_one) i)
                     e real_one e H (real_eq_refl e)).
         ++ exact (real_eq_trans (real_mult real_one e)
                     (real_mult e real_one) e
                     (real_mult_comm real_one e) (real_mult_one e)).
Qed.

(* ============================================================ *)
(* P-B 主定理：geod_b_eta_pow —— (1−η)^t 的 Bishop 序幂件族              *)
(* ============================================================ *)

(* 幂载体：x^t := x·x^{t−1}（klcx_r_pow/req_r_pow 逐位同体 Fixpoint） *)
Fixpoint geod_b_pow (x : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S k => real_mult x (geod_b_pow x k)
  end.

(* 正性保持：0 < x ⟹ 0 < x^t *)
Lemma geod_b_pow_pos : forall (x : Real) (t : nat),
  real_lt real_zero x -> real_lt real_zero (geod_b_pow x t).
Proof.
  intros x t Hx. induction t as [| k IH].
  - exact real_lt_zero_one.
  - exact (real_mult_positive x (geod_b_pow x k) Hx IH).
Qed.

(* 单调递减（Bishop 序版）：0 < x ≤ 1 ⟹ x^{t+1} ≤_B x^t。
   路线：x·x^t ≤ 1·x^t（正因子右乘保序，Or 形——前提位本为 Or 假设，        *)
(*   构造性消耗合法）+ 1·x^t == x^t 换形，real_le_to_le_b 单向桥完成。       *)
Lemma geod_b_pow_mono_decr : forall (x : Real) (t : nat),
  real_lt real_zero x -> real_le x real_one ->
  real_le_b (geod_b_pow x (Datatypes.S t)) (geod_b_pow x t).
Proof.
  intros x t Hx Hx1. apply real_le_to_le_b.
  apply (real_le_trans (real_mult x (geod_b_pow x t))
           (real_mult real_one (geod_b_pow x t)) (geod_b_pow x t)).
  - exact (real_le_mult_compat x real_one (geod_b_pow x t)
             (geod_b_pow_pos x t Hx) Hx1).
  - apply (RealSetoid.real_eq_le _ _).
    exact (real_eq_trans (real_mult real_one (geod_b_pow x t))
             (real_mult (geod_b_pow x t) real_one) (geod_b_pow x t)
             (real_mult_comm real_one (geod_b_pow x t))
             (real_mult_one (geod_b_pow x t))).
Qed.

(* ============================================================ *)
(* P-C 语义件：KL 和载体 + 下一步策略三证书 + 迭代轨道                  *)
(* ============================================================ *)

(* KL 和载体：Σ_i kl(a_i‖b_i)（证书显式参——real_kl_term 依赖型直承） *)
Definition geod_b_kl_sum (n : nat) (a b : nat -> Real)
  (Ha : forall i : nat, real_lt real_zero (a i))
  (Hb : forall i : nat, real_lt real_zero (b i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (a i) (b i) (Ha i) (Hb i))
    (List.seq 0 n).

(* 插值配分 Z := Σ p^{1−η}·r^η > 0（n 非空 + 逐点正；exp 全域正，      *)
(*   零 η 前提——cauchy_real_exp_pos 免费供给） *)
Lemma geod_b_interp_Z_pos : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hn : (0 < n)%nat)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n p r eta Hp Hr).
Proof.
  intros n p r eta Hn Hp Hr. unfold real_interp_Z.
  apply (real_list_sum_pos nat
           (fun i : nat => real_mult
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i)))
           (List.seq 0 n)).
  - intro i.
    exact (real_mult_positive
             (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
             (real_pow_pos (r i) eta (Hr i))
             (cauchy_real_exp_pos
                (real_mult (real_plus real_one (real_opp eta))
                           (cw_log (p i) (Hp i))))
             (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i))))).
  - intro Heq. destruct n as [| k].
    + lia.
    + discriminate Heq.
Qed.

(* 下一步策略逐点正：q_i = p_i^{1−η}·r_i^η/Z > 0 *)
Lemma geod_b_step_next_pos : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)) (i : nat),
  real_lt real_zero (real_step_next n p r eta Hp Hr HZ i).
Proof.
  intros n p r eta Hp Hr HZ i. unfold real_step_next.
  exact (real_mult_positive
           (real_mult
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i)))
           (real_inv_pos (real_interp_Z n p r eta Hp Hr) HZ)
           (real_mult_positive
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i))
              (cauchy_real_exp_pos
                 (real_mult (real_plus real_one (real_opp eta))
                            (cw_log (p i) (Hp i))))
              (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))))
           (real_inv_pos_pos (real_interp_Z n p r eta Hp Hr) HZ)).
Qed.

(* 下一步策略保持归一化：Σ q == (Σ p^{1−η}r^η)/Z == Z/Z == 1
   （线性律 + 逆元吸收；零前提——Z 定义即该和） *)
Lemma geod_b_step_next_norm : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)),
  real_eq (geod_lsum n (real_step_next n p r eta Hp Hr HZ)) real_one.
Proof.
  intros n p r eta Hp Hr HZ.
  unfold geod_lsum, real_step_next.
  set (Z := real_interp_Z n p r eta Hp Hr).
  apply (real_eq_trans
           (real_list_sum nat
              (fun i : nat => real_mult
                 (real_mult
                    (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                    (real_pow_pos (r i) eta (Hr i)))
                 (real_inv_pos Z HZ))
              (List.seq 0 n))
           (real_mult (real_inv_pos Z HZ)
                      (real_list_sum nat
                         (fun i : nat => real_mult
                            (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                            (real_pow_pos (r i) eta (Hr i)))
                         (List.seq 0 n)))
           real_one).
  - exact (real_list_sum_linear_r nat (real_inv_pos Z HZ)
             (fun i : nat => real_mult
                (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                (real_pow_pos (r i) eta (Hr i)))
             (List.seq 0 n)).
  - exact (real_eq_trans (real_mult (real_inv_pos Z HZ) Z)
             (real_mult Z (real_inv_pos Z HZ)) real_one
             (real_mult_comm (real_inv_pos Z HZ) Z)
             (real_inv_pos_correct Z HZ)).
Qed.

(* 迭代轨道：π_{t+1} := real_step_next(π_t, r)（sigT 封装逐点正 + 归一化；
   policy_iterate 同构，正性/归一化内嵌自足供给——零新增前提） *)
Fixpoint geod_b_iterate (n : nat) (Hn : (0 < n)%nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real) (t : nat)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    {struct t}
  : { q : nat -> Real &
      prod (forall i : nat, real_lt real_zero (q i))
           (real_eq (geod_lsum n q) real_one) } :=
  match t with
  | Datatypes.O => existT _ p (Hp, Hnormp)
  | Datatypes.S k =>
      let q := projT1 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp) in
      let Hqp := fst (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in
      let Hqn := snd (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in
      let HZq := geod_b_interp_Z_pos n q r eta Hn Hqp Hr in
      existT _ (real_step_next n q r eta Hqp Hr HZq)
               (geod_b_step_next_pos n q r eta Hqp Hr HZq,
                geod_b_step_next_norm n q r eta Hqp Hr HZq)
  end.

(* ============================================================ *)
(* P-D 保底件：单步 KL 收缩 Bishop 形（Require 55 引擎）          *)
(* ============================================================ *)

(* KL(π_t‖π_{t+1}) ≤_B η·KL(π_t‖π★)：
   real_step_kl_eta_bound_B（UpRealLeB D.5，合规验证绿在盘）一次喂定。 *)
Theorem geod_b_step_kl_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le_b (geod_b_kl_sum n p (real_step_next n p r eta Hp Hr HZ) Hp Hqv)
            (real_mult eta (geod_b_kl_sum n p r Hp Hr)).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  exact (real_step_kl_eta_bound_B n p r eta Hp Hr Hnormp Hnormr HZ Hqv
           Heta Hetale).
Qed.

(* ============================================================ *)
(* P-E 主件1：单步真几何收缩 Bishop 形（三 KL 恒等式的 le_b 形）        *)
(*   辅助引理：逐 eps 严格余量 KL(r‖q) < (1−η)·KL(r‖p) + eps——           *)
(*   逐点恒等 kl(r_i,q_i) == (1−η)·kl(r_i,p_i) + r_i·log Z（M2 对偶）   *)

(* ============================================================ *)

Theorem geod_b_policy_iter_step_margin :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  forall eps : Real, real_lt real_zero eps ->
  real_lt (geod_b_kl_sum n r (real_step_next n p r eta Hp Hr HZ) Hr Hqv)
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                        (geod_b_kl_sum n r p Hr Hp))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale eps Heps.
  unfold geod_b_kl_sum.
  set (m := real_plus real_one (real_opp eta)).
  set (Z := real_interp_Z n p r eta Hp Hr).
  set (q := real_step_next n p r eta Hp Hr HZ).
  set (LZ := cw_log Z HZ).
  set (Rsum := real_list_sum nat
                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                 (List.seq 0 n)).
  (* ---- 逐点 KL 恒等（精确 eq）：kl(r_i,q_i) == m·kl(r_i,p_i) + r_i·LZ ---- *)
  assert (Hpi : forall i : nat,
    real_eq (real_kl_term (r i) (q i) (Hr i) (Hqv i))
            (real_plus (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                       (real_mult (r i) LZ))).
  { intro i.
    set (irr := real_inv_pos (r i) (Hr i)).
    set (izz := real_inv_pos Z HZ).
    set (pA := real_pow_pos (p i) m (Hp i)).
    set (pB := real_pow_pos (r i) eta (Hr i)).
    set (lr := cw_log (r i) (Hr i)).
    set (lp := cw_log (p i) (Hp i)).
    assert (HIR : real_lt real_zero irr) by exact (real_inv_pos_pos (r i) (Hr i)).
    assert (HIZ : real_lt real_zero izz) by exact (real_inv_pos_pos Z HZ).
    assert (HpA : real_lt real_zero pA)
      by exact (cauchy_real_exp_pos (real_mult m (cw_log (p i) (Hp i)))).
    assert (HpB : real_lt real_zero pB)
      by exact (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))).
    set (Hrqlog := real_mult_positive (q i) (real_inv_pos (r i) (Hr i)) (Hqv i)
                     (real_inv_pos_pos (r i) (Hr i))).
    set (Hprlog := real_mult_positive (p i) (real_inv_pos (r i) (Hr i)) (Hp i)
                     (real_inv_pos_pos (r i) (Hr i))).
    
    assert (HlA : real_eq (cw_log pA HpA) (real_mult m lp))
      by exact (log_inv_exp_neg_thm (real_mult m (cw_log (p i) (Hp i))) HpA).
    assert (HlB : real_eq (cw_log pB HpB) (real_mult eta lr))
      by exact (log_inv_exp_neg_thm (real_mult eta (cw_log (r i) (Hr i))) HpB).
    assert (HlZ : real_eq (cw_log izz HIZ) (real_opp LZ))
      by exact (kl_log_inv Z HZ HIZ).
    assert (HlR : real_eq (cw_log irr HIR) (real_opp lr))
      by exact (kl_log_inv (r i) (Hr i) HIR).
    
    assert (Hlogpr : real_eq (cw_log (real_mult (p i) irr) Hprlog)
                             (real_plus lp (real_opp lr))).
    { exact (real_eq_trans (cw_log (real_mult (p i) irr) Hprlog)
               (real_plus (cw_log (p i) (Hp i)) (cw_log irr HIR))
               (real_plus lp (real_opp lr))
               (log_inv_mult_thm (p i) irr (Hp i) HIR Hprlog)
               (RealSetoid.real_eq_plus_compat (cw_log (p i) (Hp i))
                  (cw_log irr HIR) (cw_log (p i) (Hp i)) (real_opp lr)
                  (real_eq_refl (cw_log (p i) (Hp i))) HlR)). }
    (* q·inv r 环重排（纯环） *)
    assert (Hring1 : real_eq (real_mult (q i) irr)
                             (real_mult pA (real_mult pB (real_mult izz irr))))
      by exact (kl_ring_reassoc pA pB izz irr).
    assert (Hpos3 : real_lt real_zero (real_mult izz irr))
      by exact (real_mult_positive izz irr HIZ HIR).
    assert (Hpos2 : real_lt real_zero (real_mult pB (real_mult izz irr)))
      by exact (real_mult_positive pB (real_mult izz irr) HpB Hpos3).
    assert (HAB4 : real_lt real_zero (real_mult pA (real_mult pB (real_mult izz irr))))
      by exact (real_mult_positive pA (real_mult pB (real_mult izz irr)) HpA Hpos2).
    
    assert (Hlog4 : real_eq (cw_log (real_mult (q i) irr) Hrqlog)
                       (real_plus (cw_log pA HpA)
                          (real_plus (cw_log pB HpB)
                             (real_plus (cw_log izz HIZ) (cw_log irr HIR))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) irr) Hrqlog)
               (cw_log (real_mult pA (real_mult pB (real_mult izz irr))) HAB4)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz HIZ) (cw_log irr HIR))))).
      - exact (real_log_wd (real_mult (q i) irr)
                 (real_mult pA (real_mult pB (real_mult izz irr))) Hrqlog HAB4 Hring1).
      - exact (real_eq_trans
                  (cw_log (real_mult pA (real_mult pB (real_mult izz irr))) HAB4)
                  (real_plus (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz irr)) Hpos2))
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
                  (log_inv_mult_thm pA (real_mult pB (real_mult izz irr)) HpA Hpos2 HAB4)
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz irr)) Hpos2)
                     (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                     (real_eq_refl (cw_log pA HpA))
                     (real_eq_trans
                        (cw_log (real_mult pB (real_mult izz irr)) Hpos2)
                        (real_plus (cw_log pB HpB) (cw_log (real_mult izz irr) Hpos3))
                        (real_plus (cw_log pB HpB)
                           (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                        (log_inv_mult_thm pB (real_mult izz irr) HpB Hpos3 Hpos2)
                        (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                           (cw_log (real_mult izz irr) Hpos3)
                           (cw_log pB HpB)
                           (real_plus (cw_log izz HIZ) (cw_log irr HIR))
                           (real_eq_refl (cw_log pB HpB))
                           (log_inv_mult_thm izz irr HIZ HIR Hpos3))))). }
    
    assert (Hlog4' : real_eq (cw_log (real_mult (q i) irr) Hrqlog)
                       (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                                  (real_plus (real_opp LZ) (real_opp lr)))).
    { apply (real_eq_trans (cw_log (real_mult (q i) irr) Hrqlog)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
               (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                          (real_plus (real_opp LZ) (real_opp lr)))).
      - exact Hlog4.
      - exact (real_eq_trans
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
                  (real_plus (real_mult m lp)
                     (real_plus (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr))))
                  (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                             (real_plus (real_opp LZ) (real_opp lr)))
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                     (real_mult m lp)
                     (real_plus (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr)))
                     HlA
                     (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))
                        (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr))
                        HlB
                        (RealSetoid.real_eq_plus_compat (cw_log izz HIZ)
                           (cw_log irr HIR) (real_opp LZ) (real_opp lr)
                           HlZ HlR)))
                  (geod_b_ring_log4_b m eta lp lr LZ)). }
    
    assert (Hneg : real_eq (real_opp (cw_log (real_mult (q i) irr) Hrqlog))
                       (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)).
    { exact (real_eq_trans
               (real_opp (cw_log (real_mult (q i) irr) Hrqlog))
               (real_opp (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                                    (real_plus (real_opp LZ) (real_opp lr))))
               (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)
               (RealSetoid.real_eq_opp_compat
                  (cw_log (real_mult (q i) irr) Hrqlog)
                  (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                             (real_plus (real_opp LZ) (real_opp lr)))
                  Hlog4')
               (geod_b_ring_neg4_b eta lp lr LZ)). }
    
    assert (HnegP : real_eq (real_plus lr (real_opp lp))
                            (real_opp (cw_log (real_mult (p i) irr) Hprlog))).
    { exact (real_eq_trans (real_plus lr (real_opp lp))
               (real_opp (real_plus lp (real_opp lr)))
               (real_opp (cw_log (real_mult (p i) irr) Hprlog))
               (real_eq_sym
                  (real_opp (real_plus lp (real_opp lr)))
                  (real_plus lr (real_opp lp))
                  (kl_ring_opp_swap lp lr))
               (real_eq_sym
                  (real_opp (cw_log (real_mult (p i) irr) Hprlog))
                  (real_opp (real_plus lp (real_opp lr)))
                  (RealSetoid.real_eq_opp_compat
                     (cw_log (real_mult (p i) irr) Hprlog)
                     (real_plus lp (real_opp lr)) Hlogpr))). }
    (* 终装配：kl(r,q) == m·kl(r,p) + r·LZ *)
    exact (real_eq_trans
              (real_mult (r i) (real_opp (cw_log (real_mult (q i) irr) Hrqlog)))
              (real_plus
                 (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                 (real_mult (r i) LZ))
              (real_plus (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                         (real_mult (r i) LZ))
              (real_eq_trans
                 (real_mult (r i) (real_opp (cw_log (real_mult (q i) irr) Hrqlog)))
                 (real_mult (r i)
                    (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ))
                 (real_plus
                    (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                    (real_mult (r i) LZ))
                 (RealSetoid.real_eq_mult_compat (r i)
                    (real_opp (cw_log (real_mult (q i) irr) Hrqlog)) (r i)
                    (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)
                    (real_eq_refl (r i)) Hneg)
                 (kl_ring_kl_split m (r i) (real_plus lr (real_opp lp)) LZ))
              (RealSetoid.real_eq_plus_compat
                 (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                 (real_mult (r i) LZ)
                 (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                 (real_mult (r i) LZ)
                 (RealSetoid.real_eq_mult_compat m
                    (real_mult (r i) (real_plus lr (real_opp lp)))
                    m (real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (real_eq_refl m)
                    (real_eq_trans
                       (real_mult (r i) (real_plus lr (real_opp lp)))
                       (real_mult (r i)
                          (real_opp (cw_log (real_mult (p i) irr) Hprlog)))
                       (real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (RealSetoid.real_eq_mult_compat (r i)
                          (real_plus lr (real_opp lp)) (r i)
                          (real_opp (cw_log (real_mult (p i) irr) Hprlog))
                          (real_eq_refl (r i)) HnegP)
                       (real_eq_refl (real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                 (real_eq_refl (real_mult (r i) LZ)))). }
  (* ---- 求和层：Σ kl(r,q) == m·Σ kl(r,p) + LZ（归一化吸收 Σr == 1） ---- *)
  assert (Hsum : real_eq
      (real_list_sum nat
         (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i)) (List.seq 0 n))
      (real_plus (real_mult m Rsum) LZ)).
  { apply (real_eq_trans
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i))
                (List.seq 0 n))
             (real_list_sum nat
                (fun i : nat => real_plus
                                   (real_mult m
                                      (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                                   (real_mult (r i) LZ))
                (List.seq 0 n))
             (real_plus (real_mult m Rsum) LZ)).
    - exact (real_list_sum_ext nat _ _ (List.seq 0 n) Hpi).
    - apply (real_eq_trans
                (real_list_sum nat
                   (fun i : nat => real_plus
                                      (real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                                      (real_mult (r i) LZ))
                   (List.seq 0 n))
                (real_plus
                   (real_list_sum nat
                      (fun i : nat => real_mult m
                                       (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                      (List.seq 0 n))
                   (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                      (List.seq 0 n)))
                (real_plus (real_mult m Rsum) LZ)).
      + exact (real_list_sum_add nat _ _ (List.seq 0 n)).
      + exact (real_eq_trans
                  (real_plus
                     (real_list_sum nat
                        (fun i : nat => real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (List.seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                        (List.seq 0 n)))
                  (real_plus (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n))))
                  (real_plus (real_mult m Rsum) LZ)
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum nat
                        (fun i : nat => real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (List.seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                        (List.seq 0 n))
                     (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                     (real_list_sum_linear nat m
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n))
                     (real_list_sum_linear_r nat LZ r (List.seq 0 n)))
                  (RealSetoid.real_eq_plus_compat (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                     (real_mult m Rsum) LZ
                     (real_eq_refl (real_mult m Rsum))
                     (real_eq_trans (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                        (real_mult LZ real_one) LZ
                        (RealSetoid.real_eq_mult_compat LZ
                           (real_list_sum nat r (List.seq 0 n)) LZ real_one
                           (real_eq_refl LZ) Hnormr)
                        (real_mult_one LZ)))). }
  
  assert (HLZ : real_lt LZ eps).
  { assert (HZle : real_le Z (real_plus real_one eps))
      by exact (real_interp_Z_le_one_eps n p r eta Hp Hr Hnormp Hnormr
                  Heta Hetale eps Heps).
    assert (Honep : real_lt real_zero (real_plus real_one eps))
      by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one eps) kl_zero_plus_zero
                  (real_lt_plus_compat real_zero real_one real_zero eps
                     real_lt_zero_one Heps)).
    assert (Hlogle : real_le LZ (cw_log (real_plus real_one eps) Honep))
      by exact (kl_log_le_mono Z (real_plus real_one eps) HZ Honep HZle).
    assert (Hloglt : real_lt (cw_log (real_plus real_one eps) Honep) eps).
    { apply (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
               (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps).
      - exact (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                  Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps)).
      - exact (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)). }
    exact (geod_b_le_lt_trans LZ (cw_log (real_plus real_one eps) Honep) eps
             Hlogle Hloglt). }
  (* ---- 终局：KL(r,q) == m·KL(r,p) + LZ < m·KL(r,p) + eps ---- *)
  exact (real_eq_lt_lt
           (real_list_sum nat
              (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i))
              (List.seq 0 n))
           (real_plus (real_mult m Rsum) LZ)
           (real_plus (real_mult m Rsum) eps)
           Hsum
           (real_lt_eq_lt
              (real_plus (real_mult m Rsum) LZ)
              (real_plus eps (real_mult m Rsum))
              (real_plus (real_mult m Rsum) eps)
              (real_eq_lt_lt
                 (real_plus (real_mult m Rsum) LZ)
                 (real_plus LZ (real_mult m Rsum))
                 (real_plus eps (real_mult m Rsum))
                 (real_plus_comm (real_mult m Rsum) LZ)
                 (real_lt_plus_compat_lt_le LZ eps (real_mult m Rsum)
                    (real_mult m Rsum) HLZ
                    (real_le_refl (real_mult m Rsum))))
              (real_plus_comm eps (real_mult m Rsum)))).
Qed.

(* 主件1（Bishop 完成）：KL(π*‖π_{t+1}) ≤_B (1−η)·KL(π*‖π_t)。
   证书链：geod_b_policy_iter_step_margin（任意 eps 严格余量）
   + real_le_closure_b_one 一步完成（证书 real_lt_zero_one 既有）。 *)
Theorem geod_b_policy_iter_step :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le_b (geod_b_kl_sum n r (real_step_next n p r eta Hp Hr HZ) Hr Hqv)
            (real_mult (real_plus real_one (real_opp eta))
                       (geod_b_kl_sum n r p Hr Hp)).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  apply real_le_closure_b_one. intros eps Heps.
  exact (inl (geod_b_policy_iter_step_margin n p r eta Hp Hr Hnormp Hnormr
                  HZ Hqv Heta Hetale eps Heps)).
Qed.

(* ============================================================ *)
(* P-F 主件2（主定理）：t 步几何收缩 Bishop 形                            *)
(*   KL(π*‖π_t) ≤_B (1−η)^t·KL(π*‖π_0)——le_b 归纳；eps 累积 =          *)
(*   逐 eps 半量分配（每步取 h := eps/2，余 (1−η)·h < h，合 2h == eps；  *)
(*   免 1/n 拆分——SumD 先例同款）。                                    *)
(* ============================================================ *)

Theorem geod_b_policy_iter_iter :
  forall (n : nat) (Hn : (0 < n)%nat) (r p : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one) (t : nat),
  real_le_b
    (geod_b_kl_sum n r
       (projT1 (geod_b_iterate n Hn r Hr eta t p Hp Hnormp))
       Hr
       (fst (projT2 (geod_b_iterate n Hn r Hr eta t p Hp Hnormp))))
    (real_mult (geod_b_pow (real_plus real_one (real_opp eta)) t)
               (geod_b_kl_sum n r p Hr Hp)).
Proof.
  intros n Hn r p eta Hr Hp Hnormr Hnormp Heta Hlt1 t.
  unfold real_le_b.
  set (m := real_plus real_one (real_opp eta)).
  set (KL0 := geod_b_kl_sum n r p Hr Hp).
  assert (Hmpos : real_lt real_zero m) by exact (geod_kappa_pos eta Hlt1).
  assert (Hmlt1 : real_lt m real_one) by exact (geod_b_kappa_lt_one eta Heta).
  assert (Hetale : real_le eta real_one) by exact (inl Hlt1).
  induction t as [| k IH].
  - (* t = 0：KL(π*‖π_0) < 1·KL(π*‖π_0) + eps（1·KL0 == KL0 换形） *)
    intros eps Heps.
    apply (real_lt_eq_lt KL0 (real_plus KL0 eps)
             (real_plus (real_mult (geod_b_pow m 0) KL0) eps)).
    + exact (real_lt_plus_r_zero KL0 eps Heps).
    + apply (RealSetoid.real_eq_plus_compat KL0 eps
               (real_mult (geod_b_pow m 0) KL0) eps).
      * exact (real_eq_sym _ _ (real_eq_trans (real_mult (geod_b_pow m 0) KL0)
                 (real_mult real_one KL0) KL0
                 (RealSetoid.real_eq_mult_compat (geod_b_pow m 0) KL0
                    real_one KL0
                    (real_eq_refl real_one) (real_eq_refl KL0))
                 (real_eq_trans (real_mult real_one KL0)
                    (real_mult KL0 real_one) KL0
                    (real_mult_comm real_one KL0) (real_mult_one KL0)))).
      * exact (real_eq_refl eps).
  - (* t = S k：严格单步 + 归纳 + 缩放 + 半量 eps 分配 *)
    intros eps Heps.
    set (Pk := projT1 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in *.
    set (Pkp := fst (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp))) in *.
    set (Hkn := snd (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp))) in *.
    set (HZk := geod_b_interp_Z_pos n Pk r eta Hn Pkp Hr).
    set (PSk := real_step_next n Pk r eta Pkp Hr HZk).
    set (HPSkpos := geod_b_step_next_pos n Pk r eta Pkp Hr HZk).
    (* 半量 h := eps/2 *)
    set (inv2 := real_inv_pos (real_plus real_one real_one)
                   (real_plus_positive real_one real_one
                      real_lt_zero_one real_lt_zero_one)).
    set (h := real_mult eps inv2).
    assert (Hh : real_lt real_zero h)
      by exact (real_mult_positive eps inv2 Heps
                  (real_inv_pos_pos (real_plus real_one real_one)
                     (real_plus_positive real_one real_one
                        real_lt_zero_one real_lt_zero_one))).
    assert (Hhh : real_eq (real_plus h h) eps)
      by exact (geod_b_half_double eps inv2
                  (real_inv_pos_correct (real_plus real_one real_one)
                     (real_plus_positive real_one real_one
                        real_lt_zero_one real_lt_zero_one))).
    (* 归纳前提 specializes 到 h *)
    specialize (IH h Hh).
    (* 严格单步收缩（主件1 margin） *)
    assert (Hstep : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                            (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h))
      by exact (geod_b_policy_iter_step_margin n Pk r eta Pkp Hr Hkn Hnormr
                  HZk HPSkpos Heta Hetale h Hh).
    (* 归纳前提正缩放：m·KL_k < m·(κ^k·KL0 + h) == κ^{Sk}·KL0 + m·h *)
    assert (Hscale : real_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                             (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h)))
      by exact (real_mult_lt_compat_l (geod_b_kl_sum n r Pk Hr Pkp)
                  (real_plus (real_mult (geod_b_pow m k) KL0) h) m IH Hmpos).
    assert (Hresh : real_eq (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h))
                            (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                       (real_mult m h)))
      by exact (geod_b_scale_reshape m (geod_b_pow m k) KL0 h).
    assert (HA : real_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                         (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                    (real_mult m h)))
      by exact (real_lt_eq_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                  (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_mult m h))
                  Hscale Hresh).
    (* m·h < h（m < 1 严格） *)
    assert (Hmh : real_lt (real_mult m h) h)
      by exact (real_eq_lt_lt (real_mult m h) (real_mult h m) h
                  (real_mult_comm m h)
                  (real_lt_eq_lt (real_mult h m) (real_mult h real_one) h
                     (real_mult_lt_compat_l m real_one h Hmlt1 Hh)
                     (real_mult_one h))).
    (* 合拢：KL_{Sk} ≤ m·KL_k + h < (κ^{Sk}KL0 + m·h) + h < κ^{Sk}KL0 + 2h == κ^{Sk}KL0 + eps *)
    assert (Hmerge : real_lt (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h)
                             (real_plus
                                (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                           (real_mult m h))
                                h))
      by exact (real_lt_plus_compat_lt_le
                  (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_mult m h))
                  h h HA (real_le_refl h)).
    assert (Hstep2 : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                             (real_plus
                                (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                           (real_mult m h))
                                h))
      by exact (geod_b_le_lt_trans (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h)
                  (real_plus
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_mult m h))
                     h)
                  (inl Hstep) Hmerge).
    assert (Hassoc : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                        (real_plus (real_mult m h) h)))
      by exact (real_lt_eq_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_mult m h))
                     h)
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_plus (real_mult m h) h))
                  Hstep2
                  (real_eq_sym
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_plus (real_mult m h) h))
                     (real_plus
                        (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                   (real_mult m h))
                        h)
                     (real_plus_assoc (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                        (real_mult m h) h))).
    assert (Hinner : real_lt (real_plus (real_mult m h) h) (real_plus h h))
      by exact (real_lt_plus_compat_lt_le (real_mult m h) h h h Hmh
                  (real_le_refl h)).
    assert (Hfin : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos) (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus h h)))
      by exact (real_lt_eq_lt
                  (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus h h))
                  (real_lt_trans (geod_b_kl_sum n r PSk Hr HPSkpos) (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h)) (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0)) Hassoc (real_eq_lt_lt
                      (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h))
                      (real_plus (real_plus (real_mult m h) h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                      (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                      (real_plus_comm (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h))
                      (real_lt_plus_compat_lt_le (real_plus (real_mult m h) h) (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_mult (geod_b_pow m (Datatypes.S k)) KL0) Hinner (real_le_refl (real_mult (geod_b_pow m (Datatypes.S k)) KL0)))))
                  (real_plus_comm (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))).
    exact (real_lt_eq_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                        (real_plus h h))
             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) eps)
             Hfin
             (RealSetoid.real_eq_plus_compat
                (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                (real_plus h h)
                (real_mult (geod_b_pow m (Datatypes.S k)) KL0) eps
                (real_eq_refl (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                Hhh)).
Qed.

(* ============================================================ *)

(* ============================================================ *)

Print Assumptions geod_b_le_lt_trans.
Print Assumptions geod_b_kappa_lt_one.
Print Assumptions geod_b_half_double.
Print Assumptions geod_b_pow_pos.
Print Assumptions geod_b_pow_mono_decr.
Print Assumptions geod_b_interp_Z_pos.
Print Assumptions geod_b_step_next_pos.
Print Assumptions geod_b_step_next_norm.
Print Assumptions geod_b_iterate.
Print Assumptions geod_b_step_kl_eps.
Print Assumptions geod_b_policy_iter_step_margin.
Print Assumptions geod_b_policy_iter_step.
Print Assumptions geod_b_policy_iter_iter.
