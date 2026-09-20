(* ============================================================ *)
(* UpAblHalfPow.v —— arch_decay 几何衰减谱系供体件（P4 席·20260920）      *)
(*                                                                *)
(* 席位：P4（arch_decay 几何衰减谱系供体席，N10 报告后续槽③实办）。       *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   交付语句面全 Set 层值（QltT/QleT'＝S02 Id 形＋sigT 见证），           *)
(*   语句面无裸命题；Qeq/Z 换形全部内联于证明内部（不上语句面）。           *)
(*                                                                *)
(* 谱系定位：S03_QExp.v arch_decay（:402）给出衰减契约                     *)
(*   sigT(t, QltT (C*(1/2)^{S t}) eps)，但其见证走 Qarchimedean(C/eps)      *)
(*   不透明位（阿基米德实例化，指标不可计算）；S10 五个消费位               *)
(*   （:1682/1728/6436/11100/12022，sc_sin/sc_cos 柯西模位与               *)
(*   exp_tail 链三处）inherit 同一不透明见证。本件供给几何衰减形的          *)
(*   具体指标谱系：见证 t := Z.to_nat(Z.max 0 (c·f)+1)（c、f 为 C、eps      *)
(*   的 Qnum/QDen 展形），全链零 Qarchimedean 位、零除法位。               *)
(*                                                                *)
(* 谱系结构（四件，hpw_ 前缀）：                                           *)
(*   A 递归形登记：hpw_half_step——q_pow 半步 ι-定义性恒等（QleT' 面登记）， *)
(*      (1/2)^{S n} ≡ (1/2)·(1/2)^n（几何减半递归，q_pow S 支 iota 直出）； *)
(*   B 单位分数桥：hpw_half_pow_inv_le——(1/2)^{S t} ≤ 1/((t+2)#1)，        *)
(*      消费 S03 q_half_pow_le_inv 既有 (1/2)^n 谱系（S t 实例）；          *)
(*   C Qfloor 形接口：hpw_half_pow_inv_pos——右端换形为                     *)
(*      1#(Pos.of_succ_nat (S t))，与 S4B Qfloor 谱系件                    *)
(*      uabS4b_null_lt 的 1#(Pos.of_succ_nat k) 同形对接（后续席可自由      *)
(*      组合两谱系）；换形走 Zpos 头 iota（Qinv 在 Zpos 头上定义性归约，    *)
(*      绕开 N10 墙卡「Zneg 三支 match 阻断定义性换形」——本件只取正头）。   *)
(*   D 槽契约直配：hpw_arch_decay_instT——arch_decay 语句逐字同形          *)
(*      （sigT(t, QltT (C*q_pow (1/2)%Q (Datatypes.S t)) eps)，前件        *)
(*      QleT' 0 C/QltT 0 eps 一字不差），见证全具体（Z 指标构造，           *)
(*      c·f 与 e·d 的线性推理用 Z.mul 单调件配对供给，非线性步不赖 lia）。  *)
(*                                                                *)
(* 形态差申报（对 N10 定谳表 3 号位档案）：                                 *)
(*   语句面形态差＝0（D 件与五槽位 destruct 契约逐字同形）；                *)
(*   见证形态差＝Qarchimedean(C/eps) 的 Pos.to_nat p（不透明）              *)
(*     换为 Z.to_nat(Z.max 0 (c·f)+1)（可计算具体指标）；后续席在五槽位     *)
(*     以 destruct (hpw_arch_decay_instT C eps HC Hep) 平替                *)
(*     destruct (arch_decay C eps HC Hep)，其后推进零改动。                *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全 Export 薄壳；                 *)
(*   q_pow/q_half_pow_le_inv/Qlt 桥件皆在）＋Stdlib Z 单调件。             *)
(*   本件未入 order.txt/_CoqProject；禁触 S10/任何既有文件。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0 · 体检（缺位即刻响亮失败；上游谱系闭合探针）                     *)
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

(* 上游谱系闭合探针：非 Closed 则本席改道自证（响亮失败制） *)
Print Assumptions q_half_pow_le_inv.

(* ============================================================ *)
(* Part A · 递归形登记（几何减半的 ι-定义性内容，QleT' 面登记）            *)
(* ============================================================ *)

Lemma hpw_half_step : forall n : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S n)) ((1 / 2)%Q * q_pow (1 / 2)%Q n).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply qeq_le. reflexivity.
Qed.

(* ============================================================ *)
(* Part B · 单位分数桥（消费 S03 (1/2)^n 谱系，S t 实例）                  *)
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
(* Part C · Qfloor 形接口（1#Pos.of_succ_nat 形，S4B 谱系同形对接）        *)
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
(* Part D · 槽契约直配（arch_decay 语句逐字同形，见证全具体）              *)
(*   见证：t0 := Z.to_nat(Z.max 0 (c·f) + 1)，c/f 为 C/eps 展形分量；      *)
(*   链：(1/2)^{S t0} ≤ 1/((S t0+1)#1)（B 桥）⟹ C·(1/2)^{S t0} < eps，     *)
(*   其中 c·f < e·d·q 的非线性步以 Z.mul 单调件显式供给（Hed1/Hmul），      *)
(*   线性壳 lia 收口。                                                    *)
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
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions hpw_half_step.
Print Assumptions hpw_half_pow_inv_le.
Print Assumptions hpw_half_pow_inv_pos.
Print Assumptions hpw_arch_decay_instT.
