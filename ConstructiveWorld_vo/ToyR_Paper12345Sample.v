(* ==========================================================================)
   ToyR_Paper12345Sample.v — 参数化展开恒等式（三次余项形）
   使命: p12_s（(1−v)^(−k) − 1）、p12_param_general_k（s_k(v) = k·v + b_k·v^2 + v^3·w 的存在分解）、p12_param_k1 特例与 p12_coef 指纹系数件。
   依赖: Stdlib QArith_base、Qring
   对标: 几何级数余项的参数化展开（三次余项存在形；论文样例件）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import QArith_base Qring.

(* ---- 自足定义（与 UpReqEngineCeiling.v 逐位对照） ---- *)

Fixpoint p12_qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m => p12_qpow x m * x
  end.

(* R6 族核：s = 1/(1-v)^k - 1 *)
Definition p12_s (k : nat) (v : Q) : Q := (1 # 1) / p12_qpow (1 - v) k - (1 # 1).

(* 族参数 b = k(k+1)/2 *)
Definition p12_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).

(* 指纹系数 (k+1)/(2k) *)
Definition p12_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

(* ---- 支撑引理（Q 层除法消去，自足） ---- *)

Lemma p12_mul_neq0 : forall a b : Q, a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  (*
     语句面 <> 是表示级 eq（记录 Leibniz），证明体弃 Qeq(==) 面 tactic，
     改纯 Z 层：destruct 拆 Qmake → injection 分量等式 → positive 单位
     9 情形 discriminate 收敛 ad=bd=1 → Z.mul_eq_0 闭合。 *)
  intros a b Ha Hb Hab.
  destruct a as [an ad]; destruct b as [bn bd]; simpl in *.
  injection Hab as H1 H2.
  destruct ad; destruct bd; simpl in *; try discriminate.
  assert (Han : an <> 0%Z) by (intro Hz; apply Ha; rewrite Hz; reflexivity).
  assert (Hbn : bn <> 0%Z) by (intro Hz; apply Hb; rewrite Hz; reflexivity).
  apply Z.mul_eq_0 in H1.
  destruct H1 as [H1 | H1].
  - apply Ha. rewrite H1. reflexivity.
  - apply Hb. rewrite H1. reflexivity.
Qed.

(*
   为【假命题】：反例 a := Qmake 0 2 满足 Leibniz 非 0，但 Qeq 面为零，
   此时 /a == 0，左端 a * (x / a) == 0 ≠ x。故本引理原形不可证非 tactic
   之过，最小维修 = 前提重述 Qeq 面 `~ a == 0`（真前提，语义恰所需，
   非改弱）。另 :85 原报错（组 定格：Found no subterm matching
   "(Qnum (?M * (?M * ?M)) * QDen (?M * ?M * ?M))%Z"）双因：
   ① Qmult_assoc 实形 `n * (m * p) == n * m * p` LHS 右结合，
     目标 (x*a)*/a 左结合无匹配（即该 Z 展开模式）；
   ② Qmult_inv_r 9.1 实形为单参 `forall x, ~ x == 0 -> x * / x == 1`，
     原双参引用形 + Leibniz 前提 `exact Ha` 两处皆不匹配。 *)
Lemma p12_div_cancel : forall a x : Q, ~ a == 0 -> a * (x / a) == x.
Proof.
  intros a x Ha. unfold Qdiv.
  transitivity (x * (a * / a)).
  - ring.
  - rewrite Qmult_inv_r by exact Ha. apply Qmult_1_r.
Qed.

(* CZD13 新增支撑：v == 0（Qeq 面）时 (1-v)^k == 1——主件零支用。
   证面全在 Proper 参数位 setoid rewrite（Qmult/Qminus 位实测可用）。 *)
Lemma p12_qpow_zero_r : forall (k : nat) (v : Q),
  v == 0 -> p12_qpow (1 - v) k == 1.
Proof.
  intros k. induction k as [| k IH]; intros v Hv.
  - reflexivity.
  - simpl. rewrite (IH v Hv). rewrite Hv. reflexivity.
Qed.

(* ---- 主件：一般 k 无条件参数化（销论文5 §9 边界 3 的第一格） ---- *)

Theorem p12_param_general_k : forall (k : nat) (v : Q),
  (1 <= k)%nat -> v <> 0 ->
  exists w : Q,
    p12_s k v == (Z.of_nat k # 1) * v + p12_bcoef k * v * v + v * v * v * w.
Proof.
  (*
     而 Leibniz 前提 v <> 0 推不出它（Qmake 0 2 反例同源）——非 tactic
     缺陷而是覆盖面缺口。按 Qeq_dec v 0 双分支闭合：
     零支（Qeq 为 0，含非正规形）p12_s == 0，取 w := 0；
     非零支走除法消去真支 + ring。定理语句面零改动；Hk 在本证面
     天然冗余（两支均不用），保留以维持语句面原貌。 *)
  intros k v Hk Hv.
  destruct (Qeq_dec v 0) as [Hv0 | Hvn].
  - exists 0%Q.
    assert (Hs : p12_s k v == 0).
    { unfold p12_s. rewrite (p12_qpow_zero_r k v Hv0). reflexivity. }
    rewrite Hs. rewrite Hv0. ring.
  - exists ((p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v)
            / (v * v * v)).
    assert (Hv3 : ~ v * v * v == 0).
    { intros Hz. apply Hvn.
      apply Qmult_integral in Hz. destruct Hz as [H1 | H1].
      - apply Qmult_integral in H1. destruct H1 as [H2 | H2]; exact H2.
      - exact H1. }
    rewrite (p12_div_cancel (v * v * v)
              (p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v) Hv3).
    ring.
Qed.

(* k=1 特化：与库内无条件件 cec_r6_param_k1 同位对照 *)
Corollary p12_param_k1 : forall v : Q,
  v <> 0 ->
  exists w : Q,
    p12_s 1%nat v == (Z.of_nat 1 # 1) * v + p12_bcoef 1%nat * v * v
            + v * v * v * w.
Proof.
  intros v Hv.
  apply (p12_param_general_k 1%nat v); [ apply le_n | exact Hv ].
Qed.

(* 角点指纹（k=1 系数 > 1/2，无条件；cec_coef_fingerprint 的 k=1 角点） *)
Lemma p12_coef_fingerprint_one : Qlt (1 # 2) (p12_coef 1%nat).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions p12_param_general_k.
