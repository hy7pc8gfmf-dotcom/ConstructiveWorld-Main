(* ============================================================ *)
(* UpAblHalfPow.v —— arch_decay 几何衰减谱系供给件                       *)
(*                                                                *)
(* 使命：为 arch_decay 衰减语句提供可计算见证的几何衰减谱系。             *)
(*                                                                *)
(* 谱系定位：S03_QExp 的 arch_decay 给出衰减语句                          *)
(*   sigT(t, QltT (C*(1/2)^{S t}) eps)，但其见证走 Qarchimedean(C/eps)    *)
(*   不透明定义（阿基米德实例化，指标不可计算）；S10 的五处使用点          *)
(*   （sc_sin/sc_cos 柯西模与 exp_tail 链三处）继承同一不透明见证。        *)
(*   本件供给几何衰减形的可计算指标谱系：见证 t :=                        *)
(*   Z.to_nat(Z.max 0 (c·f)+1)（c、f 为 C、eps 的 Qnum/QDen 展形），      *)
(*   全链零 Qarchimedean 位、零除法位。                                   *)
(*                                                                *)
(* 谱系结构（四件，hpw_ 前缀）：                                           *)
(*   A 递归形：hpw_half_step——q_pow 半步的定义性恒等式（QleT' 形）：      *)
(*      (1/2)^{S n} ≡ (1/2)·(1/2)^n（几何减半递归，q_pow 的 S 支由        *)
(*      iota 直接化简）；                                                 *)
(*   B 单位分数桥接引理：hpw_half_pow_inv_le——(1/2)^{S t} ≤ 1/((t+2)#1)， *)
(*      使用 S03 q_half_pow_le_inv 既有 (1/2)^n 谱系（S t 实例）；         *)
(*   C Qfloor 形接口：hpw_half_pow_inv_pos——右端换形为                    *)
(*      1#(Pos.of_succ_nat (S t))，与 S4B 谱系件 uabS4b_null_lt 的        *)
(*      1#(Pos.of_succ_nat k) 同形对接（两谱系可自由组合）；换形走        *)
(*      Zpos 头 iota（Qinv 在 Zpos 头上定义性归约；Zneg 分支的三支        *)
(*      match 会阻断定义性换形，本件只取正头）。                          *)
(*   D 目标语句供给：hpw_arch_decay_instT——arch_decay 语句逐字同形       *)
(*      （sigT(t, QltT (C*q_pow (1/2)%Q (Datatypes.S t)) eps)，前提      *)
(*      QleT' 0 C/QltT 0 eps 一字不差），见证全具体（Z 指标构造，         *)
(*      c·f 与 e·d 的线性推理用 Z.mul 单调件配对供给，非线性步不赖 lia）。 *)
(*                                                                *)
(* 形态差注记：语句面形态差＝0（D 件与五处调用点 destruct 接口逐字        *)
(*   同形）；见证形态差＝Qarchimedean(C/eps) 的 Pos.to_nat p（不透明）    *)
(*   换为 Z.to_nat(Z.max 0 (c·f)+1)（可计算具体指标）；下游以             *)
(*   destruct (hpw_arch_decay_instT C eps HC Hep) 替换                    *)
(*   destruct (arch_decay C eps HC Hep)，其后推进零改动。                 *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全部 Export；                  *)
(*   q_pow/q_half_pow_le_inv/Qlt 桥接引理皆在）＋Stdlib Z 单调件。        *)
(*                                                                *)
(* 对标：mathlib 置顶使命与声明注释惯例；stdlib 文档注释惯例。            *)
(* 构造性注记：语句面全 Set 层值（QltT/QleT'＝S02 Id 形＋sigT 见证）；    *)
(*   语句面无裸命题；Qeq/Z 换形全部内联于证明内部；零承认；Qed 闭合。     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                 *)
(* ============================================================ *)

Check q_pow.
Check q_half_pow_le_inv.
Check Qle_refl.
Check QleT'_to_Qle.
Check Qle_to_QleT'.
Check QltT_to_Qlt.
Check Qlt_to_QltT.
Check Qle_lt_trans.
Check Qmult_le_compat_r.
Check Z.mul_le_mono_nonneg_r.
Check Z.mul_le_mono_nonneg_l.
Check Pos.of_succ_nat.

(* 上游谱系闭合核验：q_half_pow_le_inv 非 Closed 则需另行自证 *)
Print Assumptions q_half_pow_le_inv.

(* ============================================================ *)
(* §A · 递归形（几何减半的定义性恒等式，QleT' 形）                        *)
(* ============================================================ *)

Lemma hpw_half_step : forall n : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S n)) ((1 / 2)%Q * q_pow (1 / 2)%Q n).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply qeq_le. reflexivity.
Qed.

(* ============================================================ *)
(* §B · 单位分数桥接引理（使用 S03 (1/2)^n 谱系，S t 实例）                *)
(* ============================================================ *)

Corollary hpw_half_pow_inv_le : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1)).
Proof.
  intro t.
  apply Qle_to_QleT'.
  exact (q_half_pow_le_inv (Datatypes.S t)).
Qed.

(* ============================================================ *)
(* §C · Qfloor 形接口（1#Pos.of_succ_nat 形，S4B 谱系同形对接）            *)
(* ============================================================ *)

Corollary hpw_half_pow_inv_pos : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1#(Pos.of_succ_nat (Datatypes.S t))).
Proof.
  intro t.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1))).
  - exact (q_half_pow_le_inv (Datatypes.S t)).
  - change (Z.of_nat (Datatypes.S t + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (t + 1)%nat)).
    replace (t + 1)%nat with (Datatypes.S t) by lia.
    unfold Qle. cbn [Qdiv Qinv Qnum Qden Qmult]. lia.
Qed.

(* ============================================================ *)
(* §D · 目标语句供给（arch_decay 语句逐字同形，见证全具体）                *)
(*   见证：t0 := Z.to_nat(Z.max 0 (c·f) + 1)，c/f 为 C/eps 展形分量；      *)
(*   链：(1/2)^{S t0} ≤ 1/((S t0+1)#1)（经 §B 引理）⟹ C·(1/2)^{S t0} < eps， *)
(*   其中 c·f < e·d·q 的非线性步以 Z.mul 单调件显式供给（Hed1/Hmul），      *)
(*   线性部分由 lia 收尾。                                                *)
(* ============================================================ *)

Corollary hpw_arch_decay_instT : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
  sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps).
Proof.
  intros C eps HC Hep.
  destruct C as [c d]. destruct eps as [e f].
  assert (Hepos : (0 < e)%Z).
  { pose proof (QltT_to_Qlt 0 (Qmake e f) Hep) as Hlt0.
    unfold Qlt in Hlt0. simpl in Hlt0. lia. }
  assert (Hed1 : (1 <= e * Z.pos d)%Z).
  { assert (Hstep : (1 * Z.pos d <= e * Z.pos d)%Z)
      by (apply (Z.mul_le_mono_nonneg_r 1 e (Z.pos d)); lia).
    lia. }
  exists (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)).
  assert (Hqv : (Z.max 0 (c * Z.pos f) + 1
                 <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))%Z).
  { change (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
      with (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    lia. }
  assert (Hmul : (Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * 1
                  <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))
                       * (e * Z.pos d))%Z).
  { apply (Z.mul_le_mono_nonneg_l 1 (e * Z.pos d)
             (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
    - lia.
    - exact Hed1. }
  assert (Hpow : Qle (q_pow (1 / 2)%Q
                            (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)))
                      * (c # d))
                     ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))).
  { apply (Qmult_le_compat_r (q_pow (1 / 2)%Q
                             (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))))
                             (1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                             (c # d)).
    - exact (q_half_pow_le_inv (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)))).
    - apply QleT'_to_Qle. exact HC. }
  assert (Hmid : Qlt ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))
                     (e # f)).
  { change (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    unfold Qlt. cbn [Qdiv Qinv Qnum Qden Qmult]. lia. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
          (q_pow (1 / 2)%Q (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))) * (c # d)) _).
  - apply qeq_le. apply Qmult_comm.
  - exact (Qle_lt_trans _ _ _ Hpow Hmid).
Qed.

(* ============================================================ *)
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions hpw_half_step.
Print Assumptions hpw_half_pow_inv_le.
Print Assumptions hpw_half_pow_inv_pos.
Print Assumptions hpw_arch_decay_instT.
