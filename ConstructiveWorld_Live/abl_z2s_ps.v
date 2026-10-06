(* ===================================================================== *)
(*  abl_z2s_ps.v —— ζ(2) 级数部分和承载件（值面恒等式砖）                    *)
(*  模块名：abl_z2s_ps。                                                 *)
(*  使命：为 ζ(2) := Σ_{k≥1} 1/k² 建立部分和族 z2s_ps M = Σ_{k<M} 1/(k+1)²  *)
(*        的有理算术表述与值面恒等式面：级数项 1/(k+1)² 严格正（QltT）、     *)
(*        部分和递归展开、严格正与单调（QleT'）；零权 Beta 恒等面           *)
(*        z2s_term k == zb2_term 0 k 与部分和 == 闭式项和                   *)
(*        z2s_ps (S M) == zb2_Isum 0 M；截断展开恒等式 (1−t)^{n+1}A +       *)
(*        t^{M+1}P = 1 的 ζ(2) 侧双变量实例（t := xy 档）与余项分离序面      *)
(*        (1−xy)^{n+1}A ≤ 1；有理数值锚 z2s_ps 3 == 49/36。后续装配入口：    *)
(*        部分和的极限面与 ζ(2)=π²/6 评估桥自此件语句面起装。                *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；S01_BaseRing、          *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists、PolyIntegral、        *)
(*        PadeErrorIntegral（pei_div_eq 交义乘除法等式）；abl_z2_truncfam    *)
(*        （zb2_master/zb2_ps_bound）、abl_z2_itg_carrier（zb2_term/        *)
(*        zb2_Isum）。零外部证书器、零实数层、零经典逻辑。                   *)
(*  构造性：纯构造性、零假设声明、零承认式语句、零悬置假设；级数承载语句面    *)
(*        全部零前提（Qeq 传输面与 Set 层序见证）；双变量实例按              *)
(*        abl_z2_truncfam 同族形；除法恒等步以交义乘除法等式闭合，           *)
(*        未引入任何有序域决策程序。                                       *)
(*  编译配方：coqc -native-compiler no -q -Q <本件目录> ""                  *)
(*        -Q <认证 vo 世界根> "" abl_z2s_ps.v（COQLIB/ROCQLIB 全字面        *)
(*        指向 9.1 平台库）。                                              *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.    *)
(*        London Math. Soc. 11 (1979) 中 I_0 的级数表示步；ζ(2) 级数部分和  *)
(*        的经典有理逼近面。                                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam abl_z2_itg_carrier.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 承载定义（接口面，签名定死）                                      *)
(* ============================================================ *)

(* ζ(2) 级数第 k 项：1/(k+1)²（正整数平方倒数，Z 像分母形） *)
Definition z2s_term (k : nat) : Q :=
  1 / ((Z.of_nat (Datatypes.S k) # 1) * (Z.of_nat (Datatypes.S k) # 1))%Q.

(* ζ(2) 部分和：Σ_{k<M} 1/(k+1)²（M 项截断） *)
Fixpoint z2s_ps (M : nat) : Q :=
  match M with
  | O => 0
  | Datatypes.S M' => z2s_ps M' + z2s_term M'
  end.

(* 正整数 Z 像的严格正性（除法恒等步的正性证书） *)
Lemma z2s_pos_image : forall k : nat, Qlt 0 (Z.of_nat (Datatypes.S k) # 1).
Proof.
  intro k. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* §1 级数面：项正性、递归展开、和的正性与单调                            *)
(* ============================================================ *)

(* 级数项严格正：分子 1 > 0、分母为两个正因子之积 *)
Lemma z2s_term_pos : forall k : nat, QltT 0 (z2s_term k).
Proof.
  intro k. apply Qlt_to_QltT. unfold z2s_term, Qdiv.
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      apply z2s_pos_image.
Qed.

(* 级数项非负（Set 层见证；单调步用） *)
Lemma z2s_term_nonneg : forall k : nat, QleT' 0 (z2s_term k).
Proof.
  intro k. apply Qle_to_QleT'. apply Qlt_le_weak.
  apply QltT_to_Qlt. apply z2s_term_pos.
Qed.

(* 部分和递归展开（定义性） *)
Lemma z2s_ps_unfold : forall M : nat,
  z2s_ps (Datatypes.S M) == (z2s_ps M + z2s_term M)%Q.
Proof.
  intro M. cbn [z2s_ps]. reflexivity.
Qed.

(* Qeq 右端换形的严格正传输：a == b、0 < a ⟹ 0 < b（Set 层见证） *)
Lemma z2s_qeq_lt_r : forall a b : Q, a == b -> QltT 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha. apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 a b (QltT_to_Qlt _ _ Ha)).
  apply qeq_imp_qle. exact Hab.
Qed.

(* 部分和严格正：首项严格正，逐项累加非负项保持严格正 *)
Lemma z2s_ps_pos : forall M : nat, QltT 0 (z2s_ps (Datatypes.S M)).
Proof.
  induction M as [| M IH].
  - cbn [z2s_ps]. apply (z2s_qeq_lt_r (0 + z2s_term 0) (z2s_term 0)).
    + ring.
    + apply z2s_term_pos.
  - cbn [z2s_ps].
    apply Qlt_to_QltT.
    apply (pei_lt_le_plus (z2s_ps (Datatypes.S M))
                          (z2s_term (Datatypes.S M))).
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply z2s_term_pos.
Qed.

(* 部分和单调：z2s_ps M ≤ z2s_ps (S M)（Set 层见证） *)
Lemma z2s_ps_mono : forall M : nat, QleT' (z2s_ps M) (z2s_ps (Datatypes.S M)).
Proof.
  intro M.
  apply (zb2_qleT'_wd_r (z2s_ps M + z2s_term M)
                        (z2s_ps (Datatypes.S M)) (z2s_ps M)).
  - exact (Qeq_sym _ _ (z2s_ps_unfold M)).
  - apply qleT'_plus_nonneg_rT. apply z2s_term_nonneg.
Qed.

(* ============================================================ *)
(* §2 零权 Beta 恒等面：ζ(2) 级数项与部分和的闭式换算                     *)
(* ============================================================ *)

(* 零权比值恒等式：q_fact k / q_fact (S k) == 1/(S k)。
   由 q_fact_succ 换形后按交义乘除法等式（pei_div_eq）闭合。 *)
Lemma z2s_beta0_ratio : forall k : nat,
  (q_fact k / q_fact (Datatypes.S k))%Q
  == 1 / (Z.of_nat (Datatypes.S k) # 1)%Q.
Proof.
  intros k. apply pei_div_eq.
  - apply q_fact_pos.
  - apply z2s_pos_image.
  - rewrite (q_fact_succ k). ring.
Qed.

(* 零权 Beta 恒等面：ζ(2) 级数项 == Beukers 族零权重闭式项。
   zb2_term 0 k = C(k,0)·(k!·0!/(k+1)!)² = (k!/(k+1)!)²，与级数项相等。 *)
Lemma z2s_term_bridge : forall k : nat, z2s_term k == zb2_term 0 k.
Proof.
  intro k. unfold z2s_term, zb2_term. cbn [Nat.add].
  rewrite zb2_bkC_zero.
  replace (k + 0 + 1)%nat with (Datatypes.S k)%nat by lia.
  cbn [q_fact Z.of_nat]. rewrite Qmult_1_r.
  transitivity ((q_fact k / q_fact (Datatypes.S k)
                 * (q_fact k / q_fact (Datatypes.S k)))%Q).
  - rewrite (z2s_beta0_ratio k).
    unfold Qdiv. rewrite Qinv_mult_distr. rewrite !Qmult_1_l. reflexivity.
  - rewrite Qmult_1_l. reflexivity.
Qed.

(* 部分和 = 闭式项和：z2s_ps (S M) == zb2_Isum 0 M。
   ζ(2) 值面的代数换算面：M 项部分和与零权重二重积分族闭式项和逐项相等。 *)
Corollary z2s_Isum_bridge : forall M : nat,
  z2s_ps (Datatypes.S M) == zb2_Isum 0 M.
Proof.
  induction M as [| M IH].
  - cbn [z2s_ps zb2_Isum]. rewrite (z2s_term_bridge 0). ring.
  - cbn [z2s_ps zb2_Isum]. rewrite IH. rewrite (z2s_term_bridge (Datatypes.S M)).
    ring.
Qed.

(* 部分和严格正的闭式项和读法：zb2_Isum 0 M 严格正的直接传输 *)
Corollary z2s_ps_pos_via_Isum : forall M : nat, QltT 0 (zb2_Isum 0 M).
Proof.
  intro M. apply (z2s_qeq_lt_r (z2s_ps (Datatypes.S M)) (zb2_Isum 0 M)).
  - exact (z2s_Isum_bridge M).
  - apply z2s_ps_pos.
Qed.

(* ============================================================ *)
(* §3 截断展开恒等式的 ζ(2) 侧双变量实例（t := xy 档）                     *)
(* ============================================================ *)

(* 值域乘积复合件：0 ≤ x ≤ 1、0 ≤ y ≤ 1 ⟹ 0 ≤ xy ≤ 1 *)
Lemma z2s_range_mul : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= x * y <= 1.
Proof.
  intros x y Hx Hy. destruct Hx as [Hx0 Hx1]. destruct Hy as [Hy0 Hy1].
  split.
  - apply Qmult_le_0_compat; assumption.
  - assert (E : (1 * y)%Q == y) by apply Qmult_1_l.
    apply (Qle_trans (x * y) (1 * y) 1).
    + apply Qmult_le_compat_r; assumption.
    + apply (Qle_trans (1 * y) y 1).
      * apply qeq_imp_qle. exact E.
      * exact Hy1.
Qed.

(* 截断展开恒等式双变量实例（t := xy 档；同族参数化）：
   在 0 ≤ xy ≤ 1 上 (1−xy)^{n+1}·A(n,M,xy) + (xy)^{M+1}·P(n,M,xy) = 1。 *)
Lemma z2s_master_xy : forall (n M : nat) (x y : Q), 0 <= x * y <= 1 ->
  q_pow (1 - x * y) (Datatypes.S n) * zb2_ps n M (x * y)
  + q_pow (x * y) (Datatypes.S M) * zb2_pq n M (x * y) == 1.
Proof.
  intros n M x y Hxy. exact (zb2_master n M (x * y) Hxy).
Qed.

(* 余项显式分离序面（双变量实例）：(1−xy)^{n+1}·A(n,M,xy) ≤ 1。
   代数读法：1 − (1−xy)^{n+1}·A = (xy)^{M+1}·P ≥ 0（右端两因子非负）。 *)
Lemma z2s_master_rim : forall (n M : nat) (x y : Q), 0 <= x * y <= 1 ->
  QleT' (q_pow (1 - x * y) (Datatypes.S n) * zb2_ps n M (x * y)) 1.
Proof.
  intros n M x y Hxy. exact (zb2_ps_bound n M (x * y) Hxy).
Qed.

(* ============================================================ *)
(* §4 数值锚                                                            *)
(* ============================================================ *)

(* 有理数值锚：1 + 1/4 = 5/4 *)
Lemma z2s_ps_anchor2 : z2s_ps 2 == (5 # 4).
Proof. vm_compute. reflexivity. Qed.

(* 有理数值锚：1 + 1/4 + 1/9 = 49/36 *)
Lemma z2s_ps_anchor3 : z2s_ps 3 == (49 # 36).
Proof. vm_compute. reflexivity. Qed.

(* 桥面数值锚：零权重闭式项和与部分和在 M = 2 处同为 49/36 *)
Lemma z2s_Isum_bridge_anchor : zb2_Isum 0 2 == (49 # 36).
Proof.
  rewrite <- (z2s_Isum_bridge 2). exact z2s_ps_anchor3.
Qed.

(* ============================================================ *)
(* §5 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions z2s_term_pos.
Print Assumptions z2s_ps_unfold.
Print Assumptions z2s_ps_pos.
Print Assumptions z2s_ps_mono.
Print Assumptions z2s_beta0_ratio.
Print Assumptions z2s_term_bridge.
Print Assumptions z2s_Isum_bridge.
Print Assumptions z2s_range_mul.
Print Assumptions z2s_master_xy.
Print Assumptions z2s_master_rim.
Print Assumptions z2s_ps_anchor3.
Print Assumptions z2s_Isum_bridge_anchor.
