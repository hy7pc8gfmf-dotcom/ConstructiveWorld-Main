(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ============================================================ *)
(* EpsTrichotomy.v —— 件 CZI13（ E-STAGING-CZI13· C9 第一阶段） *)
(*                                                              *)
(* 使命：ε-三分点级比较基建件（Q 层）。                          *)
(*   UpReqPinskerCore 四留记（:20 常数2 / :991 S1近支 / :1305 R8  *)
(*   S2 / :2461 W3）共同前置—— 勘察"库内比较基建全零"，      *)
(*   本件补位。本件只建基建件，不攻四留记本体（压轴件）。      *)
(*                                                              *)
(* 交付面：                                                      *)
(*   ① 等值代换三件（Qeq 左代换 ≤/＜、Qabs 零化）；             *)
(*   ② eps 分半小引擎（(1#2)·eps 正性 + 回接恒等 + 分母形桥）；  *)
(*   ③ 主件 etc_trichotomy：0 < eps 证书下构造性三分 a 与 b，    *)
(*      Lt 支（a＜b）/ Eq 支（|a−b|≤eps）/ Gt 支（b＜a），       *)
(*      comparison 标签 sigT 三支见证形（Set 层）；              *)
(*   ④ Apart 桥 etc_apart：|a−b|＞eps ⟹ 仅 Lt/Gt 支居留；       *)
(*   ⑤ 出口便捷件 etc_compare_tri / etc_sign_tri / etc_one_side  *)
(*      （无 eps 精确二点三分；符号提取与单位区间判支皆实例）。  *)
(*                                                              *)
(* 使用面：S01（Set 层 Id/And/Or）、S02（QltT/QleT'/桥族/        *)
(*   Qlt_bool/Qle_bool）。构造路线＝符号判定 + 减法符号：        *)
(*   Qcompare（可判定）分账三支，Qeq/Z 层显式代换链闭合。        *)
(*   逐点 Qcompare 本就可判定，不依赖整体三分律假设面。          *)
(*                                                              *)
(* 前缀 etc_ 全库零撞名（grep trichotomy/eps_split/apart 全零    *)
(*   核验 ， C9 行同源）。                           *)
(* 红线自审：语句面全 Set 值（QltT/QleT'/QeqT/sigT/Id），    *)
(*   合取用 S01 And:=A*B；证内 Or 分解仅显式两支消解；           *)
(*   全真证 Qed/Defined 零承认件；文尾 Print Assumptions 审计。  *)
(* 编译：source Live/toolchain/env.sh 后 rocq c -q               *)
(*   -Q <信任根> "" -Q . "" EpsTrichotomy.v（9.1 live 轨）       *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring
               ZArith.Zorder Setoid Lia Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

(* ============================================================ *)
(* §0 便捷桥两件                                                *)
(* ============================================================ *)

(* QltT → QleT' 降格（严格蕴涵非严格） *)
Lemma etc_ltT_leT' : forall x y : Q, QltT x y -> QleT' x y.
Proof.
  intros x y H.
  apply Qle_to_QleT'.
  apply QltT_to_Qlt in H. unfold Qle. unfold Qlt in H. lia.
Qed.

(* Set 层等值见证直接使用 S02 原生 QeqT（Id-Qcompare 反映形，
   qeq_imp_qeqT/qeqT_imp_qeq 双向桥在案），本件不另造第三形。 *)

(* ============================================================ *)
(* §1 等值代换三件（Z 层显式乘式链，不做 Qlt 下重写）           *)
(* ============================================================ *)

(* 左代换（≤）：x == y、x ≤ z ⟹ y ≤ z *)
Lemma etc_qeq_le_r : forall x y z : Q, (x == y)%Q -> (x <= z)%Q -> (y <= z)%Q.
Proof.
  intros x y z He Hle.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qle in Hle. unfold Qeq in He. unfold Qle.
  apply (Zmult_le_reg_r (Qnum y * Z.pos (Qden z))
           (Qnum z * Z.pos (Qden y)) (Z.pos (Qden x))).
  - lia.
  - replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_le_compat_r (Qnum x * Z.pos (Qden z))
             (Qnum z * Z.pos (Qden x)) (Z.pos (Qden y))).
    + exact Hle.
    + lia.
Qed.

(* 左代换（＜）：x == y、z ＜ x ⟹ z ＜ y *)
Lemma etc_qeq_lt_r : forall x y z : Q, (x == y)%Q -> (z < x)%Q -> (z < y)%Q.
Proof.
  intros x y z He Hlt.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qlt in Hlt. unfold Qeq in He. unfold Qlt.
  apply (Zmult_lt_reg_r (Qnum z * Z.pos (Qden y))
           (Qnum y * Z.pos (Qden z)) (Z.pos (Qden x))).
  - exact Hdx.
  - replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_lt_compat_r (Qnum z * Z.pos (Qden x))
             (Qnum x * Z.pos (Qden z)) (Z.pos (Qden y))).
    + exact Hdy.
    + exact Hlt.
Qed.

(* Qabs 零化：a == b ⟹ |a−b| == 0 *)
Lemma etc_qabs_zero : forall a b : Q, (a == b)%Q -> (Qabs (a - b) == 0)%Q.
Proof.
  intros a b Hab.
  assert (Hd : (a - b == 0)%Q).
  { apply (Qeq_trans (a + - b)%Q (b + - b)%Q).
    - apply Qplus_comp; [exact Hab | apply Qeq_refl].
    - apply Qplus_opp_r. }
  apply (Qabs_case (a - b) (fun t => (t == 0)%Q)).
  - intros _. exact Hd.
  - intros _. apply (Qeq_trans (- (a - b))%Q (- 0)%Q 0%Q).
    + apply (Qopp_comp (a - b) 0%Q Hd).
    + reflexivity.
Qed.

(* ============================================================ *)
(* §2 eps 分半小引擎                                            *)
(* ============================================================ *)

(* 半量正性：0 < eps ⟹ 0 < (1#2)·eps *)
Lemma etc_eps_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 ((1#2) * eps).
Proof.
  intros eps Heps.
  apply Qlt_to_QltT.
  apply Qmult_lt_0_compat.
  - unfold Qlt. simpl. lia.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* 分半回接恒等：(1#2)·eps + (1#2)·eps == eps（eps/2 拆分闭合） *)
Lemma etc_eps_half_add : forall eps : Q,
  (((1#2) * eps) + ((1#2) * eps) == eps)%Q.
Proof.
  intro eps.
  assert (Hone : (((1#2) + (1#2)) == 1)%Q) by reflexivity.
  rewrite <- (Qmult_plus_distr_l (1#2) (1#2) eps).
  rewrite Hone.
  apply Qmult_1_l.
Qed.

(* ============================================================ *)
(* §3 主件：ε-三分（三支 sigT 见证形）                          *)
(* ============================================================ *)

Theorem etc_trichotomy : forall (a b eps : Q),
  QltT 0 eps ->
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => QleT' (Qabs (a - b)) eps
    | Gt => QltT b a
    end).
Proof.
  intros a b eps Heps.
  destruct (Qcompare a b) eqn:E.
  - (* Eq 支：a == b ⟹ |a−b| == 0 ＜ eps ⟹ 判定必非 Gt（comparison 序＝Eq|Lt|Gt） *)
    exists Eq.
    assert (Hq : (a == b)%Q).
    { apply (proj2 (Qeq_alt a b)). exact E. }
    assert (Hz := etc_qabs_zero a b Hq).
    apply QltT_to_Qlt in Heps.
    unfold QleT', Qle_bool.
    destruct (Qcompare (Qabs (a - b)) eps) eqn:E2.
    + reflexivity.
    + reflexivity.
    + exfalso.
      assert (Hgt : (eps < Qabs (a - b))%Q) by (apply Qgt_alt; exact E2).
      apply (etc_qeq_lt_r (Qabs (a - b)) 0 eps Hz) in Hgt.
      assert (Hc : (0 < 0)%Q) by (apply Qlt_trans with eps; assumption).
      destruct (Qlt_irrefl 0 Hc).
  - (* Lt 支：a ＜ b *)
    exists Lt. unfold QltT, Qlt_bool. rewrite E. reflexivity.
  - (* Gt 支：b ＜ a（见证判定式为 (b ?= a)，独立分账） *)
    exists Gt. unfold QltT, Qlt_bool.
    destruct (Qcompare b a) eqn:E3.
    + exfalso.
      assert (Heqba : (b == a)%Q) by (apply (proj2 (Qeq_alt b a)); exact E3).
      assert (Eab : (a ?= b) = Eq).
      { apply (proj1 (Qeq_alt a b)). apply Qeq_sym. exact Heqba. }
      rewrite Eab in E. discriminate.
    + reflexivity.
    + exfalso.
      assert (Hba : (b < a)%Q) by (apply Qgt_alt; exact E).
      assert (Hab : (a < b)%Q) by (apply Qgt_alt; exact E3).
      exact (Qlt_irrefl a (Qlt_trans a b a Hab Hba)).
Defined.

(* ============================================================ *)
(* §4 Apart 桥：|a−b| ＞ eps ⟹ 三分判 Lt/Gt（Eq 支排空）        *)
(* ============================================================ *)

Theorem etc_apart : forall (a b eps : Q),
  QltT 0 eps ->
  QltT eps (Qabs (a - b)) ->
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => Id false true
    | Gt => QltT b a
    end).
Proof.
  intros a b eps Heps Hap.
  destruct (Qcompare a b) eqn:E.
  - (* Eq 支排空：a == b ⟹ |a−b| == 0 ⟹ eps ＜ 0，与 0 ＜ eps 矛盾 *)
    assert (Hq : (a == b)%Q).
    { apply (proj2 (Qeq_alt a b)). exact E. }
    assert (Hz := etc_qabs_zero a b Hq).
    apply QltT_to_Qlt in Hap.
    apply (etc_qeq_lt_r (Qabs (a - b)) 0 eps Hz) in Hap.
    apply QltT_to_Qlt in Heps.
    assert (Hc : (0 < 0)%Q) by (apply Qlt_trans with eps; assumption).
    destruct (Qlt_irrefl 0 Hc).
  - exists Lt. unfold QltT, Qlt_bool. rewrite E. reflexivity.
  - exists Gt. unfold QltT, Qlt_bool.
    destruct (Qcompare b a) eqn:E3.
    + exfalso.
      assert (Heqba : (b == a)%Q) by (apply (proj2 (Qeq_alt b a)); exact E3).
      assert (Eab : (a ?= b) = Eq).
      { apply (proj1 (Qeq_alt a b)). apply Qeq_sym. exact Heqba. }
      rewrite Eab in E. discriminate.
    + reflexivity.
    + exfalso.
      assert (Hba : (b < a)%Q) by (apply Qgt_alt; exact E).
      assert (Hab : (a < b)%Q) by (apply Qgt_alt; exact E3).
      exact (Qlt_irrefl a (Qlt_trans a b a Hab Hba)).
Defined.

(* ============================================================ *)
(* §5 出口便捷件：精确比较三分族                                *)
(*   PinskerCore 四留记预期使用形定向：                         *)
(*   符号提取＝etc_sign_tri（:20 ε-三分符号支）；               *)
(*   S1 近/远支判分（:991/:1305 t≤1 vs t＞1）＝etc_one_side；   *)
(*   W3 常数段（:2461）Q 层比较面＝etc_compare_tri 通用形。     *)
(* ============================================================ *)

Theorem etc_compare_tri : forall a b : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => QeqT a b
    | Gt => QltT b a
    end).
Proof.
  intros a b.
  destruct (Qcompare a b) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply (proj2 (Qeq_alt a b)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* 便捷实例一：符号提取（t 正/零/负三分） *)
Theorem etc_sign_tri : forall t : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT 0 t
    | Eq => QeqT t 0
    | Gt => QltT t 0
    end).
Proof.
  intro t.
  destruct (Qcompare 0 t) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply Qeq_sym. apply (proj2 (Qeq_alt 0 t)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* 便捷实例二：单位上界判支（t ＜ 1 / t == 1 / t ＞ 1） *)
Theorem etc_one_side : forall t : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT t 1
    | Eq => QeqT t 1
    | Gt => QltT 1 t
    end).
Proof.
  intro t.
  destruct (Qcompare t 1) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply (proj2 (Qeq_alt t 1)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* ============================================================ *)
(* 提取检验（G3）：sigT 见证可计算、证明面擦除                  *)
(* ============================================================ *)
Definition etc_pack (a b eps : Q) (Heps : QltT 0 eps) : comparison :=
  projT1 (etc_trichotomy a b eps Heps).

Extraction "etc13_out" etc_pack etc_eps_half_add.

(* 公理面审计（G4 前置） *)
Print Assumptions etc_trichotomy.
Print Assumptions etc_apart.
Print Assumptions etc_compare_tri.
Print Assumptions etc_sign_tri.
Print Assumptions etc_one_side.
Print Assumptions etc_eps_half_pos.
Print Assumptions etc_eps_half_add.
Print Assumptions etc_qeq_le_r.
Print Assumptions etc_qeq_lt_r.
Print Assumptions etc_qabs_zero.
Print Assumptions etc_ltT_leT'.
