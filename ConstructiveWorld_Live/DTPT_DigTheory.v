(* ============================================================
   DTPT_DigTheory.v — 数字全域塔（Dig）本体理论 + H_alg 有穷深度代理
   ①职责：
     · 本体理论段（S7，分层交付）：
       §1 构造子单射性（7 构造子 + dCode 逐点形）    【保底件】
       §2 跨构造子互斥性（C(7,2)=21 对判别面）        【保底件】
       §3 塔尺寸理论 dig_size/dig_lsize：方程组+正性+下界【主件】
       §4 数值投影 dig_Q：dQ 槽取值/默认零/往返面      【主件】
       §5 数字域判定 is_num：特征定理（Prop 形+sigT 构造形）
          与 dig_Q/dig_size 组合面                    【加分项】
     · H 代理段（U13R，M4 并入）：h_alg := (Z.of_nat (dig_size d) # 1)
       有穷 dCode 深度代理（非负/正性/可加性族/子项严格单调）、
       dig_eqb 尺寸可传匹配近似、sub_dig 结构真子项判定与
       sub_dig_size_mono/lt 灵魂件、is_num × h_alg 联合刻画。
   ②依赖：Require Import QArith.QArith QArith.Qabs / List / Arith Lia
          / DTPT；H 代理段追加 Require Import Bool ZArith
          （Z.of_nat / Nat2Z / Z.add_1_r 面）。
   ③归并记录：2026-09-14 DTPT-M4 席将 DTPT_HAlg.v（U13R 席）全量
          并入本文件尾部：删其 Require Import 中的 DTPT_DigTheory
          （并入后同文件直引），保留 Require Import DTPT 与其
          stdlib Require（Bool/ZArith 为本件新增面）；Qed 面零改动。
          撞名预检：h_alg/sub_dig/dig_eqb/qZ1_eq/qZ3_eq 系对本体段
          既有名 grep 零撞（U13R 开席全库零命中在册）。源件退役为
          DTPT_HAlg.v.retired_M4（全工作区 grep 无下游 Require）。
   ④认证：81 件全 Qed（本体段 58 + H 代理段 23）；两段各 6 件
          Print Assumptions 公理闭包审计（应全 Closed）。
          四关：G1 禁词 grep=0 / G2 .vo 新于 .v / G3 Qed 对账 /
          G4 stderr 无 Anomaly/Error。
   ⑤纪律：零承认零公理（头注不用禁词字面）；全程收口 Qed；
          Q_scope 自 DTPT 传导为开，nat 层一律 %nat 全显式；
          全部编译走 cpu_guard（LoadLimit 60 / CoolSec 10）。
   ⑥边界诚实注记（两段合并陈列）：
     a) dCode 的内容函数 f : nat -> Dig 之像无法在结构递归内求和
        （f k 非递归参的子项，同块守卫拒绝；dSeq 表内子件可用
        嵌套 match 经 dSeq l 的 l 下钻故不受限），故 dCode 槽取
        槽位计数 S n；内容求和留待良基递归（挂账，见报告）。
     b) dig_size d = 1 不刻画 is_num d = true（反例 dSeq []），
        只证正向 is_num d = true -> dig_size d = 1。
     c) dig_Q 非单射（默认零碰撞 dQ 0 与 dModel (dQ 0)），
        以定义性见证定理落面；往返定理只取 d = dQ x 方向。
     d) 全相等可判定（decidable equality）不可证：dCode 载函数
        相等不可判定，故互斥性按 21 对逐对判别落面，不造决策器。
     e) H 代理段（U13R）：真 H_alg（层级算法熵）的泛型递归结构
        无法在结构递归内完全刻画，h_alg 只取 dCode 深度代理面，
        不承担真 H_alg 语义（无编码内容熵、无极限过程）；
        sub_dig 对 dCode 支保守 false（其 f i 子项对结构判定
        不可见）；dig_eqb true 保尺寸可传不保 Leibniz 相等
        （Q 叶用 Qeq_bool 值相等）；is_num × h_alg 只取可证
        受限形（反向 dSeq [] 见证不成立，沿边界 b 固化）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Bool ZArith.
Require DTPT.
Import ListNotations.
Open Scope Q_scope.
Import DTPT.DTPT.

Module DTPT_DigTheory.

(* ========== §1 构造子单射性【保底件】 ========== *)

Lemma dig_inj_dQ : forall x y : Q, dQ x = dQ y -> x = y.
Proof. intros x y H. injection H as Hxy. exact Hxy. Qed.

Lemma dig_inj_dPair : forall a b c d : Dig,
  dPair a b = dPair c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

Lemma dig_inj_dSeq : forall l1 l2 : list Dig,
  dSeq l1 = dSeq l2 -> l1 = l2.
Proof. intros l1 l2 H. injection H as Hl. exact Hl. Qed.

Lemma dig_inj_dCode : forall (n m : nat) (f g : nat -> Dig),
  dCode n f = dCode m g -> n = m /\ f = g.
Proof. intros n m f g H. split; congruence. Qed.

Lemma dig_inj_dCode_pointwise : forall (n m : nat) (f g : nat -> Dig),
  dCode n f = dCode m g -> n = m /\ (forall i : nat, f i = g i).
Proof.
  intros n m f g H. destruct (dig_inj_dCode n m f g H) as [Hn Hf].
  split; [exact Hn | intros i; rewrite Hf; reflexivity].
Qed.

Lemma dig_inj_dJudge : forall a b c d : Dig,
  dJudge a b = dJudge c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

Lemma dig_inj_dModel : forall a b : Dig,
  dModel a = dModel b -> a = b.
Proof. intros a b H. injection H as Hab. exact Hab. Qed.

Lemma dig_inj_dProofT : forall a b c d : Dig,
  dProofT a b = dProofT c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

(* ========== §2 跨构造子互斥性（21 对）【保底件】 ========== *)
(* 逐对 discriminate；反向由等式对称性免费获得，不重复落面。 *)

Lemma dig_ne_dQ_dPair : forall (x : Q) (a b : Dig), dQ x <> dPair a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dSeq : forall (x : Q) (l : list Dig), dQ x <> dSeq l.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dCode : forall (x : Q) (n : nat) (f : nat -> Dig),
  dQ x <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dJudge : forall (x : Q) (a b : Dig), dQ x <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dModel : forall (x : Q) (a : Dig), dQ x <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dProofT : forall (x : Q) (a b : Dig), dQ x <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dSeq : forall (a b : Dig) (l : list Dig),
  dPair a b <> dSeq l.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dCode : forall (a b : Dig) (n : nat) (f : nat -> Dig),
  dPair a b <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dJudge : forall (a b : Dig) (c d : Dig),
  dPair a b <> dJudge c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dModel : forall (a b : Dig) (c : Dig),
  dPair a b <> dModel c.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dProofT : forall (a b : Dig) (c d : Dig),
  dPair a b <> dProofT c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dCode : forall (l : list Dig) (n : nat) (f : nat -> Dig),
  dSeq l <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dJudge : forall (l : list Dig) (a b : Dig),
  dSeq l <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dModel : forall (l : list Dig) (a : Dig),
  dSeq l <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dProofT : forall (l : list Dig) (a b : Dig),
  dSeq l <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dJudge : forall (n : nat) (f : nat -> Dig) (a b : Dig),
  dCode n f <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dModel : forall (n : nat) (f : nat -> Dig) (a : Dig),
  dCode n f <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dProofT : forall (n : nat) (f : nat -> Dig) (a b : Dig),
  dCode n f <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dJudge_dModel : forall (a b : Dig) (c : Dig),
  dJudge a b <> dModel c.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dJudge_dProofT : forall (a b : Dig) (c d : Dig),
  dJudge a b <> dProofT c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dModel_dProofT : forall (a : Dig) (b c : Dig),
  dModel a <> dProofT b c.
Proof. intros; discriminate. Qed.

(* ========== §3 塔尺寸理论【主件】 ========== *)
(* dig_size：按构造子结构递归，二叉节点取子件尺寸求和加一，
   序列节点取表内子件尺寸求和加一，dCode 取槽位计数（见头注 a)。
   实现注记：mutual Fixpoint 方案被守卫拒绝（dig_lsize 对表头的
   dig_size x 调用，x 非尾参 xs 的子项）——改用 dSeq 分支内嵌
   匿名 fix：y 经 d ⊳ l ⊳ m ⊳ y 三层 match 嵌套仍是 d 的子项，
   守卫通过；dig_lsize 随后独立定义，方程组 face 经转换性成立。 *)

Fixpoint dig_size (d : Dig) : nat :=
  match d with
  | dQ _ => 1%nat
  | dPair a b => S (dig_size a + dig_size b)%nat
  | dSeq l =>
      S ((fix dig_lsz (m : list Dig) : nat :=
            match m with
            | [] => 0%nat
            | y :: ys => (dig_size y + dig_lsz ys)%nat
            end) l)
  | dCode n _ => S n%nat
  | dJudge a b => S (dig_size a + dig_size b)%nat
  | dModel a => S (dig_size a)
  | dProofT a b => S (dig_size a + dig_size b)%nat
  end.

(* 独立表尺寸函数（与 dig_size 的 dSeq 内嵌 fix 同体，转换相等） *)
Fixpoint dig_lsize (l : list Dig) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => (dig_size x + dig_lsize xs)%nat
  end.

(* --- 构造子方程组（全部定义性成立） --- *)

Theorem dig_size_eq_dQ : forall x : Q, dig_size (dQ x) = 1%nat.
Proof. intros x. reflexivity. Qed.

Theorem dig_size_eq_dPair : forall a b : Dig,
  dig_size (dPair a b) = S (dig_size a + dig_size b)%nat.
Proof. intros a b. reflexivity. Qed.

Theorem dig_size_eq_dSeq : forall l : list Dig,
  dig_size (dSeq l) = S (dig_lsize l).
Proof. intros l. reflexivity. Qed.

Theorem dig_size_eq_dCode : forall (n : nat) (f : nat -> Dig),
  dig_size (dCode n f) = S n.
Proof. intros n f. reflexivity. Qed.

Theorem dig_size_eq_dJudge : forall a b : Dig,
  dig_size (dJudge a b) = S (dig_size a + dig_size b)%nat.
Proof. intros a b. reflexivity. Qed.

Theorem dig_size_eq_dModel : forall a : Dig,
  dig_size (dModel a) = S (dig_size a).
Proof. intros a. reflexivity. Qed.

Theorem dig_size_eq_dProofT : forall a b : Dig,
  dig_size (dProofT a b) = S (dig_size a + dig_size b)%nat.
Proof. intros a b. reflexivity. Qed.

Theorem dig_lsize_eq_nil : dig_lsize [] = 0%nat.
Proof. reflexivity. Qed.

Theorem dig_lsize_eq_cons : forall (x : Dig) (l : list Dig),
  dig_lsize (x :: l) = (dig_size x + dig_lsize l)%nat.
Proof. intros x l. reflexivity. Qed.

(* --- 正性与下界面 --- *)

Theorem dig_size_pos : forall d : Dig, (0 < dig_size d)%nat.
Proof. intros d. destruct d; simpl; lia. Qed.

Theorem dig_size_ge1 : forall d : Dig, (1 <= dig_size d)%nat.
Proof. intros d. pose proof (dig_size_pos d). lia. Qed.

Theorem dig_lsize_cons_pos : forall (x : Dig) (l : list Dig),
  (0 < dig_lsize (x :: l))%nat.
Proof. intros x l. simpl. pose proof (dig_size_pos x). lia. Qed.

Theorem dig_lsize_pos : forall l : list Dig,
  l <> [] -> (0 < dig_lsize l)%nat.
Proof.
  intros l Hne. destruct l as [| y ys].
  - exfalso. apply Hne. reflexivity.
  - apply dig_lsize_cons_pos.
Qed.

Theorem dig_lsize_app : forall l1 l2 : list Dig,
  dig_lsize (l1 ++ l2) = (dig_lsize l1 + dig_lsize l2)%nat.
Proof.
  intros l1 l2. induction l1 as [| y ys IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(* 分支节点尺寸至少为 2（需子件正性前提——子件尺寸是不透明原子，
   裸 lia 会以 X=Y=0 反例拒证：自设子目标先验真再证的活教材） *)

Theorem dig_size_dPair_ge2 : forall a b : Dig,
  (2 <= dig_size (dPair a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dPair.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dJudge_ge2 : forall a b : Dig,
  (2 <= dig_size (dJudge a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dJudge.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dProofT_ge2 : forall a b : Dig,
  (2 <= dig_size (dProofT a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dProofT.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dModel_ge2 : forall a : Dig,
  (2 <= dig_size (dModel a))%nat.
Proof.
  intros a. rewrite dig_size_eq_dModel.
  pose proof (dig_size_ge1 a). lia.
Qed.

(* ========== §4 数值投影 dig_Q【主件】 ========== *)
(* 全函数：dQ 槽取原值，其余构造子取默认 0（头注 c：非单射）。 *)

Definition dig_Q (d : Dig) : Q :=
  match d with
  | dQ x => x
  | _ => 0%Q
  end.

Theorem dig_Q_eq_dQ : forall x : Q, dig_Q (dQ x) = x.
Proof. intros x. reflexivity. Qed.

Theorem dig_Q_roundtrip : forall (d : Dig) (x : Q),
  d = dQ x -> dig_Q d = x.
Proof. intros d x H. subst. reflexivity. Qed.

Theorem dig_Q_not_injective_witness :
  dig_Q (dModel (dQ 0)) = dig_Q (dQ 0).
Proof. reflexivity. Qed.

(* ========== §5 数字域判定 is_num 与组合面【加分项】 ========== *)

Definition is_num (d : Dig) : bool :=
  match d with
  | dQ _ => true
  | _ => false
  end.

Theorem is_num_eq_dQ : forall x : Q, is_num (dQ x) = true.
Proof. intros x. reflexivity. Qed.

(* 特征定理·弱形（Prop 存在） *)
Theorem is_num_inv : forall d : Dig,
  is_num d = true -> exists x : Q, d = dQ x.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  exists x. reflexivity.
Qed.

(* 特征定理·构造形（sigT，可提取见证） *)
Theorem is_num_inv_sigT : forall d : Dig,
  is_num d = true -> { x : Q & d = dQ x }.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  exact (existT _ x (eq_refl (dQ x))).
Qed.

Theorem is_num_false_not_dQ : forall (d : Dig) (x : Q),
  is_num d = false -> d <> dQ x.
Proof.
  intros d x H Heq. rewrite Heq in H. rewrite is_num_eq_dQ in H.
  discriminate.
Qed.

(* 组合面一：非数字域节点的投影恒落默认零 *)
Theorem dig_Q_default0 : forall d : Dig,
  is_num d = false -> dig_Q d = 0%Q.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate; reflexivity.
Qed.

(* 组合面二：数字域节点的尺寸恒为 1（只证正向，头注 b） *)
Theorem is_num_size1 : forall d : Dig,
  is_num d = true -> dig_size d = 1%nat.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  reflexivity.
Qed.

(* 组合面三：dQ 探针三重一致（投影往返 + 尺寸 + 判定）——旗舰 *)
Theorem dQ_probe_roundtrip : forall x : Q,
  dig_Q (dQ x) = x /\ dig_size (dQ x) = 1%nat /\ is_num (dQ x) = true.
Proof. intros x. split; [reflexivity | split; reflexivity]. Qed.

(* 诚实边界：尺寸 1 不等价于数字域（dSeq [] 反例，定义性见证） *)
Theorem dig_size_one_not_only_num :
  dig_size (dSeq []) = 1%nat /\ is_num (dSeq []) = false.
Proof. split; reflexivity. Qed.

(* ========== 终验：公理闭包审计 ========== *)

Print Assumptions dQ_probe_roundtrip.
Print Assumptions dig_size_pos.
Print Assumptions is_num_inv_sigT.
Print Assumptions dig_Q_default0.
Print Assumptions dig_ne_dQ_dPair.
Print Assumptions dig_inj_dCode_pointwise.

(* ============================================================
   H 代理段（M4 归并：原件 DTPT_HAlg.v，席 DTPT-U13R；
   2026-09-14 全量并入，上方既有语句零改动，Qed 面零改动）
   防撞检索：h_alg / sub_dig / dig_eqb 在全库 .v 零命中（U13R 开席
   grep 实证，原席 U13 热宕机无遗存，本段以本文件为唯一事实源）。
   温控纪律：全部编译走 cpu_guard（LoadLimit 60 / CoolSec 10），
   编译前 coqc/coqchk 串行化检查，每件落盘即快照。
   ============================================================ *)

Import ListNotations.
Open Scope Q_scope.

(* ========== §1 保底件：h_alg 定义 + 非负 / 正性 + 最小码面 ========== *)

Definition h_alg (d : Dig) : Q := ((Z.of_nat (dig_size d)) # 1)%Q.

Theorem h_alg_dQ : forall x : Q, h_alg (dQ x) == 1.
Proof. intros x. unfold h_alg. reflexivity. Qed.

Theorem h_alg_pos : forall d : Dig, 0 < h_alg d.
Proof.
  intros d. pose proof (dig_size_pos d) as Hp. unfold h_alg.
  destruct (dig_size d) as [| k].
  - lia.
  - unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r. reflexivity.
Qed.

Theorem h_alg_nonneg : forall d : Dig, 0 <= h_alg d.
Proof. intros d. apply Qlt_le_weak. apply h_alg_pos. Qed.

(* ========== §2 主件·子项序：sub_dig + 尺寸严格单调（本席灵魂件） ========== *)
(* dig_eqb：Dig 上尺寸单调的匹配近似（头注 c）。dSeq 分支按 S7 守卫墙
   定式走 dSeq l1 的直接子项 l1 内嵌匿名 fix（双层表扫描），独立方程
   面经转换性成立。 *)

Fixpoint dig_eqb (a b : Dig) {struct a} : bool :=
  match a, b with
  | dQ x, dQ y => Qeq_bool x y
  | dPair a1 a2, dPair b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | dSeq l1, dSeq l2 =>
      (fix eq_l (m1 m2 : list Dig) {struct m1} : bool :=
         match m1, m2 with
         | [], [] => true
         | x :: xs, y :: ys => (dig_eqb x y && eq_l xs ys)
         | _, _ => false
         end) l1 l2
  | dJudge a1 a2, dJudge b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | dModel a1, dModel b1 => dig_eqb a1 b1
  | dProofT a1 a2, dProofT b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | _, _ => false
  end.

(* dSeq 面方程（转换性直取，供归纳消费） *)
Theorem dig_eqb_dSeq_cons : forall (x : Dig) (xs : list Dig) (y : Dig) (ys : list Dig),
  dig_eqb (dSeq (x :: xs)) (dSeq (y :: ys)) =
  (dig_eqb x y && dig_eqb (dSeq xs) (dSeq ys)).
Proof. intros x xs y ys. reflexivity. Qed.

(* dig_eqb 尺寸可传（有界归纳；dSeq 面经内层表归纳 + 逐元 IH 供量） *)
Lemma dig_eqb_size_bound : forall (n : nat) (a b : Dig),
  (dig_size a <= n)%nat -> dig_eqb a b = true -> (dig_size a <= dig_size b)%nat.
Proof.
  intros n. induction n as [| n IHn]; intros a b Hd Hb.
  - pose proof (dig_size_pos a). lia.
  - destruct a as [x | a1 a2 | l1 | n0 f | a1 a2 | a1 | a1 a2];
      destruct b as [y | b1 b2 | l2 | m g | b1 b2 | b1 | b1 b2];
      simpl in Hb; try discriminate.
    + (* dQ *) simpl. lia.
    + (* dPair *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
    + (* dSeq *)
      assert (Hcase : forall (m1 m2 : list Dig), (dig_lsize m1 <= n)%nat ->
        dig_eqb (dSeq m1) (dSeq m2) = true ->
        (dig_lsize m1 <= dig_lsize m2)%nat).
      { intros m1. induction m1 as [| x xs IHl]; intros m2 Hm Hs.
        - destruct m2 as [| y ys].
          + simpl. lia.
          + simpl in Hs. discriminate.
        - destruct m2 as [| y ys].
          + simpl in Hs. discriminate.
          + rewrite dig_eqb_dSeq_cons in Hs.
            apply andb_true_iff in Hs as [H1 H2].
            assert (Hx : (dig_size x <= n)%nat) by (simpl in Hm; lia).
            assert (Hxs : (dig_lsize xs <= n)%nat) by (simpl in Hm; lia).
            pose proof (IHn x y Hx H1). pose proof (IHl ys Hxs H2).
            simpl. lia. }
      assert (Hl : (dig_lsize l1 <= n)%nat).
      { rewrite dig_size_eq_dSeq in Hd. lia. }
      pose proof (Hcase l1 l2 Hl Hb).
      rewrite !dig_size_eq_dSeq. lia.
    + (* dJudge *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
    + (* dModel *)
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 Hb). simpl. lia.
    + (* dProofT *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
Qed.

(* sub_dig：结构真子项判定（七构造子递归；dQ 无真子项；dCode 支保守
   false，头注 b）。dSeq 分支同 S7 守卫定式：表扫描内嵌匿名 fix，
   尾参 m 上递归，元素 y 经 d ⊳ l ⊳ m ⊳ y 保持子项证据链。 *)
Fixpoint sub_dig (a d : Dig) {struct d} : bool :=
  match d with
  | dQ _ => false
  | dPair b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  | dSeq l =>
      (fix sub_l (a0 : Dig) (m : list Dig) {struct m} : bool :=
         match m with
         | [] => false
         | y :: ys => ((dig_eqb a0 y || sub_dig a0 y) || sub_l a0 ys)
         end) a l
  | dCode _ _ => false
  | dJudge b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  | dModel b => (dig_eqb a b || sub_dig a b)
  | dProofT b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  end.

(* dSeq 面方程（转换性直取）与定义性见证 *)
Theorem sub_dig_dSeq_nil : forall a : Dig, sub_dig a (dSeq []) = false.
Proof. intros a. reflexivity. Qed.

Theorem sub_dig_dSeq_cons : forall (a y : Dig) (ys : list Dig),
  sub_dig a (dSeq (y :: ys)) =
  ((dig_eqb a y || sub_dig a y) || sub_dig a (dSeq ys)).
Proof. intros a y ys. reflexivity. Qed.

Theorem sub_dig_witness : sub_dig (dQ 0) (dPair (dQ 0) (dQ 0)) = true.
Proof. reflexivity. Qed.

Theorem sub_dig_witness_neg : sub_dig (dQ 0) (dQ 0) = false.
Proof. reflexivity. Qed.

(* 灵魂件：子项序 → 尺寸严格单调（有界归纳；dSeq 面内层表归纳） *)
Lemma sub_dig_size_bound : forall (n : nat) (d a : Dig),
  (dig_size d <= n)%nat -> sub_dig a d = true -> (dig_size a < dig_size d)%nat.
Proof.
  intros n. induction n as [| n IHn]; intros d a Hd H.
  - pose proof (dig_size_pos d). lia.
  - destruct d as [x | b c | l | n0 f | b c | b | b c]; simpl in H;
      try discriminate.
    + (* dPair *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
    + (* dSeq *)
      assert (Hcase : forall m : list Dig, (dig_lsize m <= n)%nat ->
        sub_dig a (dSeq m) = true -> (dig_size a < S (dig_lsize m))%nat).
      { intros m. induction m as [| y ys IHl]; intros Hm Hs.
        - rewrite sub_dig_dSeq_nil in Hs. discriminate.
        - rewrite sub_dig_dSeq_cons in Hs. simpl in Hm. simpl.
          assert (Hy : (dig_size y <= n)%nat) by lia.
          pose proof (dig_size_pos y) as Hpy.
          apply orb_true_iff in Hs. destruct Hs as [Hs | Hs].
          + apply orb_true_iff in Hs. destruct Hs as [Hs | Hs].
            * pose proof (dig_eqb_size_bound (dig_size a) a y
                           (le_n (dig_size a)) Hs). lia.
            * pose proof (IHn y a Hy Hs). lia.
          + assert (Hys : (dig_lsize ys <= n)%nat) by lia.
            pose proof (IHl Hys Hs). lia. }
      assert (Hl : (dig_lsize l <= n)%nat).
      { rewrite dig_size_eq_dSeq in Hd. lia. }
      pose proof (Hcase l Hl H).
      rewrite dig_size_eq_dSeq. lia.
    + (* dJudge *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
    + (* dModel *)
      apply orb_true_iff in H. destruct H as [H | H].
      * pose proof (dig_eqb_size_bound (dig_size a) a b (le_n (dig_size a)) H).
        simpl. lia.
      * assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn b a Hb H). simpl. lia.
    + (* dProofT *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
Qed.

(* 单调定理（任务书原陈述 ≤ 形）与严格形 *)
Theorem sub_dig_size_mono : forall (d a : Dig),
  sub_dig a d = true -> (dig_size a <= dig_size d)%nat.
Proof.
  intros d a H. apply Nat.lt_le_incl.
  apply (sub_dig_size_bound (dig_size d) d a (le_n (dig_size d)) H).
Qed.

Theorem sub_dig_size_lt : forall (d a : Dig),
  sub_dig a d = true -> (dig_size a < dig_size d)%nat.
Proof.
  intros d a H. apply (sub_dig_size_bound (dig_size d) d a (le_n (dig_size d)) H).
Qed.

(* ========== §3 主件·可加性族：构造子方程组直推 ========== *)
(* 整值 Q 面：n # 1 形的加法单位吸收（ring 面一次成型） *)
Lemma qZ1_eq : forall p : Z, (((p + 1) # 1) == (((p # 1) + 1))%Q).
Proof. intros p. unfold Qeq, Qplus. cbn. ring. Qed.

Lemma qZ3_eq : forall p q : Z,
  (((p + q + 1) # 1) == (((p # 1) + (q # 1)) + 1)%Q).
Proof. intros p q. unfold Qeq, Qplus. cbn. ring. Qed.

Theorem h_alg_dPair : forall a b : Dig,
  h_alg (dPair a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dPair, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dJudge : forall a b : Dig,
  h_alg (dJudge a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dJudge, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dProofT : forall a b : Dig,
  h_alg (dProofT a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dProofT, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dModel : forall a : Dig, h_alg (dModel a) == (h_alg a + 1)%Q.
Proof.
  intros a. unfold h_alg.
  rewrite dig_size_eq_dModel, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

Theorem h_alg_dSeq : forall l : list Dig,
  h_alg (dSeq l) == ((Z.of_nat (dig_lsize l) # 1) + 1)%Q.
Proof.
  intros l. unfold h_alg.
  rewrite dig_size_eq_dSeq, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

Theorem h_alg_dCode : forall (n : nat) (f : nat -> Dig),
  h_alg (dCode n f) == ((Z.of_nat n # 1) + 1)%Q.
Proof.
  intros n f. unfold h_alg.
  rewrite dig_size_eq_dCode, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

(* ========== §4 加分件：is_num × h_alg 联合刻画（可证受限形） ========== *)

Theorem is_num_h_alg1 : forall d : Dig, is_num d = true -> h_alg d == 1.
Proof.
  intros d H. apply is_num_inv in H. destruct H as [x Hx].
  rewrite Hx. apply h_alg_dQ.
Qed.

(* dQ 探针三重一致：最小码面 + 判定 + 正性 *)
Theorem h_alg_dQ_probe : forall x : Q,
  h_alg (dQ x) == 1 /\ is_num (dQ x) = true /\ 0 < h_alg (dQ x).
Proof.
  intros x. split; [apply h_alg_dQ | split; [reflexivity | apply h_alg_pos]].
Qed.

(* 诚实边界 d)：码面 1 不等价于数字域（dSeq [] 反例，定义性见证） *)
Theorem h_alg_one_not_only_num :
  h_alg (dSeq []) == 1 /\ is_num (dSeq []) = false.
Proof. split; reflexivity. Qed.

End DTPT_DigTheory.
Import DTPT_DigTheory.

(* ========== 终验：公理闭包审计 ========== *)

Print Assumptions sub_dig_size_mono.
Print Assumptions sub_dig_size_lt.
Print Assumptions h_alg_pos.
Print Assumptions h_alg_nonneg.
Print Assumptions h_alg_dPair.
Print Assumptions is_num_h_alg1.
