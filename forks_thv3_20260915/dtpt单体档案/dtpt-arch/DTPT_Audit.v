(* ============================================================
   DTPT_Audit.v — X2-4 组合审查器 + 双副本相干桥 + 零消费名救活
   职责：§1 零消费名救活——level_le_total / trLevel_geq_trans /
           chain_ok 传递链（消费 level_le_trans）/ ev_append 精确
           加性（常数 k=1，由定义实形归纳推得，非拍脑袋）；
         §2 双副本相干桥——DTPT.Evidence 与 DTPT_Truth.Evidence
           逐构造同形，转换函数 cv_ev 即恒等映射形态，但往返保构
           与尺寸守恒定理一律实归纳证明（非平凡载荷）；Level 侧
           cv_lv 保序（全序性/反对称性经桥运输）；TrNode 四投影
           保构 + Tex 纤维铸造；
         §3 组合审查器——audit_node（层判 × 证据非空 bool 化）行为
           双向定理 + 换更高层节点审查不降 + 桥上审查相干 +
           门槛单调与层判的组合审查定理（消费 llm_gate_pass_mono_thr）。
   依赖：QArith（QArith/Qabs）、Bool、Arith、Lia；DTPT / DTPT_Truth /
         DTPT_LLM 三底座（均限名引用防遮蔽，本文件对三底座只
         Require 不 Import）。
   归并记录：无（原生成模块；席 DTPT-U6，2026-09-13）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；nat 层一律显式
         Datatypes.S / O / Nat.add / Nat.leb（防 Q_scope 劫持）；
         Q 语句一律 %Q 标注。
   ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Bool Arith Lia.
Require DTPT DTPT_Truth DTPT_LLM.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Truth.DTPT_Truth.
Import DTPT_LLM.DTPT_LLM.

Module DTPT_Audit.

(* ========== §1 零消费名救活 ========== *)

(* 1.0 全序性：level_le 判定器双向往复（X2-4 清单件，救活 level_le） *)
Theorem level_le_total : forall a b : DTPT_Truth.DTPT_Truth.Level,
  DTPT_Truth.DTPT_Truth.level_le a b = true \/ DTPT_Truth.DTPT_Truth.level_le b a = true.
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Qed.

(* 1.1 层升检查的传递形：节点对要求层 a 过审（a ≤ 节点层）且要求
   不升（b ≤ a）时对 b 过审——消费 level_le_trans 的第一下游。
   （方向注记：trLevel_geq t lv 语义是 lv ≤ trLevel t，故传递律的
   合法形是"要求递降"，反向陈述为假命题，a=Lv0,b=Lv2,t=Lv0 反例） *)
Theorem trLevel_geq_trans : forall (t : DTPT_Truth.DTPT_Truth.TrNode)
    (a b : DTPT_Truth.DTPT_Truth.Level),
  DTPT_Truth.DTPT_Truth.trLevel_geq t a = true ->
  DTPT_Truth.DTPT_Truth.level_le b a = true ->
  DTPT_Truth.DTPT_Truth.trLevel_geq t b = true.
Proof.
  intros t a b Ha Hb.
  unfold DTPT_Truth.DTPT_Truth.trLevel_geq in *.
  apply (DTPT_Truth.DTPT_Truth.level_le_trans b a (DTPT_Truth.DTPT_Truth.trLevel t)); assumption.
Qed.

(* 1.2 传递链审查器：chain_ok 三节点链式判定（消费 level_le_trans） *)
Definition chain_ok (l1 l2 l3 : DTPT_Truth.DTPT_Truth.Level) : bool :=
  andb (DTPT_Truth.DTPT_Truth.level_le l1 l2) (DTPT_Truth.DTPT_Truth.level_le l2 l3).

Theorem chain_ok_iff : forall l1 l2 l3 : DTPT_Truth.DTPT_Truth.Level,
  chain_ok l1 l2 l3 = true <->
  DTPT_Truth.DTPT_Truth.level_le l1 l2 = true /\ DTPT_Truth.DTPT_Truth.level_le l2 l3 = true.
Proof.
  intros l1 l2 l3. unfold chain_ok. split.
  - intro H. apply andb_prop in H. destruct H as [ H1 H2 ].
    split; assumption.
  - intros [ H1 H2 ]. apply andb_true_intro. split; assumption.
Qed.

Theorem chain_ok_trans : forall l1 l2 l3 : DTPT_Truth.DTPT_Truth.Level,
  chain_ok l1 l2 l3 = true -> DTPT_Truth.DTPT_Truth.level_le l1 l3 = true.
Proof.
  intros l1 l2 l3 H.
  destruct (proj1 (chain_ok_iff l1 l2 l3) H) as [H1 H2].
  apply (DTPT_Truth.DTPT_Truth.level_le_trans l1 l2 l3); assumption.
Qed.

(* 1.3 ev_append 精确加性：k=1（压平化每丧失一个 Pair 包装恰补 1）。
   证法：对 a 归纳（b 先泛化）。基例 evNum/evSeq：结果为
   evPair 头 + b，尺寸 = 1 + (1 + |b|)；归纳例 evPair：双递归展开
   后两条归纳假设相接，常数方程 2k = 1 + k 逼出 k = 1。 *)
Theorem audit_ev_append_size_exact : forall a b : DTPT_Truth.DTPT_Truth.Evidence,
  DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.ev_append a b)
  = Nat.add (Nat.add (DTPT_Truth.DTPT_Truth.ev_size a) (DTPT_Truth.DTPT_Truth.ev_size b))
            (Datatypes.S Datatypes.O).
Proof.
  intros a. induction a as [ q | l | a1 IH1 a2 IH2 ]; intros b; simpl.
  - lia.
  - lia.
  - rewrite (IH1 (DTPT_Truth.DTPT_Truth.ev_append a2 b)). rewrite (IH2 b). lia.
Qed.

(* 1.4 拼接单调：右参证据在拼接下尺寸不减（精确加性的推论） *)
Theorem audit_ev_append_size_mono : forall a b : DTPT_Truth.DTPT_Truth.Evidence,
  le (DTPT_Truth.DTPT_Truth.ev_size b)
               (DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.ev_append a b)).
Proof.
  intros a b. rewrite audit_ev_append_size_exact. lia.
Qed.

(* ========== §2 双副本相干桥 ========== *)

(* 2.1 证据层转换：DTPT.DTPT.Evidence → DTPT_Truth.DTPT_Truth.Evidence（恒等形态） *)
Fixpoint cv_ev (e : DTPT.DTPT.Evidence) : DTPT_Truth.DTPT_Truth.Evidence :=
  match e with
  | DTPT.DTPT.evNum q    => DTPT_Truth.DTPT_Truth.evNum q
  | DTPT.DTPT.evSeq l    => DTPT_Truth.DTPT_Truth.evSeq l
  | DTPT.DTPT.evPair a b => DTPT_Truth.DTPT_Truth.evPair (cv_ev a) (cv_ev b)
  end.

(* 2.2 逆转换：DTPT_Truth.DTPT_Truth.Evidence → DTPT.DTPT.Evidence *)
Fixpoint cv_ev_inv (e : DTPT_Truth.DTPT_Truth.Evidence) : DTPT.DTPT.Evidence :=
  match e with
  | DTPT_Truth.DTPT_Truth.evNum q    => DTPT.DTPT.evNum q
  | DTPT_Truth.DTPT_Truth.evSeq l    => DTPT.DTPT.evSeq l
  | DTPT_Truth.DTPT_Truth.evPair a b => DTPT.DTPT.evPair (cv_ev_inv a) (cv_ev_inv b)
  end.

(* 2.3 往返保构（实归纳，非平凡载荷） *)
Lemma cv_ev_round_trip_fwd : forall e : DTPT.DTPT.Evidence,
  cv_ev_inv (cv_ev e) = e.
Proof.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

Lemma cv_ev_round_trip_bwd : forall e : DTPT_Truth.DTPT_Truth.Evidence,
  cv_ev (cv_ev_inv e) = e.
Proof.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.4 尺寸守恒（正方向）：Truth 侧证据过桥往返后尺寸不变 *)
Theorem cv_size_preservation_T : forall e : DTPT_Truth.DTPT_Truth.Evidence,
  DTPT_Truth.DTPT_Truth.ev_size (cv_ev (cv_ev_inv e)) = DTPT_Truth.DTPT_Truth.ev_size e.
Proof.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.5 DTPT 侧尺寸测度：经桥取 Truth 侧 ev_size（桥传输的测度） *)
Definition dt_ev_size (e : DTPT.DTPT.Evidence) : nat :=
  DTPT_Truth.DTPT_Truth.ev_size (cv_ev e).

(* 2.6 尺寸守恒（反方向）：DTPT 侧证据全往返后桥测度不变（实归纳） *)
Theorem cv_size_preservation_D : forall e : DTPT.DTPT.Evidence,
  dt_ev_size (cv_ev_inv (cv_ev e)) = dt_ev_size e.
Proof.
  intros e. unfold dt_ev_size.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.7 层转换与逆转换 *)
Definition cv_lv (l : DTPT.DTPT.Level) : DTPT_Truth.DTPT_Truth.Level :=
  match l with
  | DTPT.DTPT.Lv0 => DTPT_Truth.DTPT_Truth.Lv0
  | DTPT.DTPT.Lv1 => DTPT_Truth.DTPT_Truth.Lv1
  | DTPT.DTPT.Lv2 => DTPT_Truth.DTPT_Truth.Lv2
  end.

Definition cv_lv_inv (l : DTPT_Truth.DTPT_Truth.Level) : DTPT.DTPT.Level :=
  match l with
  | DTPT_Truth.DTPT_Truth.Lv0 => DTPT.DTPT.Lv0
  | DTPT_Truth.DTPT_Truth.Lv1 => DTPT.DTPT.Lv1
  | DTPT_Truth.DTPT_Truth.Lv2 => DTPT.DTPT.Lv2
  end.

Lemma cv_lv_round : forall l : DTPT.DTPT.Level, cv_lv_inv (cv_lv l) = l.
Proof. intros l. destruct l; reflexivity. Qed.

Lemma cv_lv_round_inv : forall l : DTPT_Truth.DTPT_Truth.Level,
  cv_lv (cv_lv_inv l) = l.
Proof. intros l. destruct l; reflexivity. Qed.

(* 2.8 层转换单射（经往返引理） *)
Lemma cv_lv_inj : forall a b : DTPT.DTPT.Level, cv_lv a = cv_lv b -> a = b.
Proof.
  intros a b H.
  assert (H1 : cv_lv_inv (cv_lv a) = cv_lv_inv (cv_lv b))
    by (rewrite H; reflexivity).
  rewrite cv_lv_round in H1. rewrite cv_lv_round in H1. exact H1.
Qed.

(* 2.9 保序·反对称性运输：level_le 反对称律经桥回运到 DTPT 侧
   （消费 level_le_antisym + cv_lv_inj） *)
Theorem cv_lv_antisym_transport : forall a b : DTPT.DTPT.Level,
  DTPT_Truth.DTPT_Truth.level_le (cv_lv a) (cv_lv b) = true ->
  DTPT_Truth.DTPT_Truth.level_le (cv_lv b) (cv_lv a) = true -> a = b.
Proof.
  intros a b H1 H2. apply cv_lv_inj.
  apply DTPT_Truth.DTPT_Truth.level_le_antisym; assumption.
Qed.

(* 2.10 保序·全序性运输：桥像上的全序判定双向往复 *)
Theorem cv_lv_total_transport : forall a b : DTPT.DTPT.Level,
  DTPT_Truth.DTPT_Truth.level_le (cv_lv a) (cv_lv b) = true \/
  DTPT_Truth.DTPT_Truth.level_le (cv_lv b) (cv_lv a) = true.
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Qed.

(* 2.11 节点桥：DTPT.DTPT.TrNode → DTPT_Truth.DTPT_Truth.TrNode 四投影搬运 *)
Definition cv_node (t : DTPT.DTPT.TrNode) : DTPT_Truth.DTPT_Truth.TrNode :=
  DTPT_Truth.DTPT_Truth.mkTrNode (cv_lv (DTPT.DTPT.trLevel t))
                      (DTPT.DTPT.trPhi t) (DTPT.DTPT.trModel t)
                      (cv_ev (DTPT.DTPT.trValue t)).

Definition cv_node_inv (t : DTPT_Truth.DTPT_Truth.TrNode) : DTPT.DTPT.TrNode :=
  DTPT.DTPT.mkTrNode (cv_lv_inv (DTPT_Truth.DTPT_Truth.trLevel t))
                (DTPT_Truth.DTPT_Truth.trPhi t) (DTPT_Truth.DTPT_Truth.trModel t)
                (cv_ev_inv (DTPT_Truth.DTPT_Truth.trValue t)).

(* 2.12 节点桥四投影保构（封死漂移风险；首投影另立单引理供改写） *)
Lemma cv_node_level : forall t : DTPT.DTPT.TrNode,
  DTPT_Truth.DTPT_Truth.trLevel (cv_node t) = cv_lv (DTPT.DTPT.trLevel t).
Proof. reflexivity. Qed.

Theorem cv_node_pres : forall t : DTPT.DTPT.TrNode,
  DTPT_Truth.DTPT_Truth.trLevel (cv_node t) = cv_lv (DTPT.DTPT.trLevel t)
  /\ DTPT_Truth.DTPT_Truth.trPhi (cv_node t) = DTPT.DTPT.trPhi t
  /\ DTPT_Truth.DTPT_Truth.trModel (cv_node t) = DTPT.DTPT.trModel t
  /\ DTPT_Truth.DTPT_Truth.trValue (cv_node t) = cv_ev (DTPT.DTPT.trValue t).
Proof.
  intros t. repeat split; reflexivity.
Qed.

(* 2.13 节点桥往返（核心引理纯可逆 + f_equal 分解，绕开 simpl 折形） *)
Lemma cv_node_round_core : forall (lv : DTPT.DTPT.Level) (p m : DTPT.DTPT.Dig)
    (v : DTPT.DTPT.Evidence),
  cv_node_inv (cv_node (DTPT.DTPT.mkTrNode lv p m v))
  = DTPT.DTPT.mkTrNode (cv_lv_inv (cv_lv lv)) p m (cv_ev_inv (cv_ev v)).
Proof. reflexivity. Qed.

Lemma cv_node_round : forall t : DTPT.DTPT.TrNode, cv_node_inv (cv_node t) = t.
Proof.
  intros [ lv p m v ]. rewrite cv_node_round_core. f_equal.
  - destruct lv; reflexivity.
  - apply cv_ev_round_trip_fwd.
Qed.

(* 2.14 Tex 纤维铸造：trPhi 对齐的 DTPT 节点升格为 Truth 侧 Tex 见证 *)
Theorem Tex_fiber_cast : forall (phi : DTPT.DTPT.Dig) (t : DTPT.DTPT.TrNode),
  DTPT.DTPT.trPhi t = phi ->
  exists T : DTPT_Truth.DTPT_Truth.Tex phi, projT1 T = cv_node t.
Proof.
  intros phi t H. exists (existT _ (cv_node t) H). reflexivity.
Qed.

(* ========== §3 组合审查器 ========== *)

(* 3.0 审查器：层判（不低于 Lv1）× 层内证据非空（尺寸 ≥ 1 的
   bool 化）两支合取 *)
Definition audit_node (t : DTPT_Truth.DTPT_Truth.TrNode) : bool :=
  andb (DTPT_Truth.DTPT_Truth.trLevel_geq t DTPT_Truth.DTPT_Truth.Lv1)
       (Nat.leb (Datatypes.S Datatypes.O)
                (DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.trValue t))).

(* 3.1 行为定理（双向）：审查通过 ⟺ 两分支各自通过（拆解到分支级） *)
Theorem audit_node_iff : forall t : DTPT_Truth.DTPT_Truth.TrNode,
  audit_node t = true <->
  DTPT_Truth.DTPT_Truth.trLevel_geq t DTPT_Truth.DTPT_Truth.Lv1 = true
  /\ le (Datatypes.S Datatypes.O)
                  (DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.trValue t)).
Proof.
  intros t. unfold audit_node. split.
  - intro Ha.
    destruct (proj1 (Bool.andb_true_iff _ _) Ha) as [H1 H2].
    split; [ exact H1 | exact (proj1 (Nat.leb_le _ _) H2) ].
  - intros [ H1 H2 ].
    apply (proj2 (Bool.andb_true_iff _ _)).
    split; [ exact H1 | exact (proj2 (Nat.leb_le _ _) H2) ].
Qed.

(* 3.2 行为定理（构造子级拆解）：对 mkTrNode 逐分支反射 *)
Theorem audit_node_branch_iff : forall (lv : DTPT_Truth.DTPT_Truth.Level)
    (p m : DTPT.DTPT.Dig) (v : DTPT_Truth.DTPT_Truth.Evidence),
  audit_node (DTPT_Truth.DTPT_Truth.mkTrNode lv p m v) = true <->
  DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv1 lv = true
  /\ Nat.leb (Datatypes.S Datatypes.O) (DTPT_Truth.DTPT_Truth.ev_size v) = true.
Proof.
  intros lv p m v.
  unfold audit_node, DTPT_Truth.DTPT_Truth.trLevel_geq. simpl. split.
  - intro H. apply andb_prop in H. destruct H as [ H1 H2 ].
    split; assumption.
  - intros [ H1 H2 ]. apply andb_true_intro. split; assumption.
Qed.

(* 3.3 尺寸支恒真引理（消费零消费名 ev_size_pos）：审查器退化为层判 *)
Theorem audit_node_eq_trLevel : forall t : DTPT_Truth.DTPT_Truth.TrNode,
  audit_node t = DTPT_Truth.DTPT_Truth.trLevel_geq t DTPT_Truth.DTPT_Truth.Lv1.
Proof.
  intros t. unfold audit_node.
  assert (Hb : Nat.leb (Datatypes.S Datatypes.O)
                 (DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.trValue t)) = true).
  { apply (proj2 (Nat.leb_le _ _)). apply DTPT_Truth.DTPT_Truth.ev_size_pos. }
  rewrite Hb. apply Bool.andb_true_r.
Qed.

(* 3.4 替换稳定：同层同值换节点审查不降 *)
Theorem audit_node_mono : forall t t' : DTPT_Truth.DTPT_Truth.TrNode,
  DTPT_Truth.DTPT_Truth.trLevel t' = DTPT_Truth.DTPT_Truth.trLevel t ->
  DTPT_Truth.DTPT_Truth.trValue t' = DTPT_Truth.DTPT_Truth.trValue t ->
  audit_node t = true -> audit_node t' = true.
Proof.
  intros t t' Hlv Hval Ht.
  destruct t as [ lv p m v ]. destruct t' as [ lv' p' m' v' ].
  simpl in Hlv, Hval. subst lv'. subst v'.
  unfold audit_node in Ht |- *. simpl in Ht |- *. exact Ht.
Qed.

(* 3.5 换更高层节点（Lv2）审查不降：任何 Lv2 节点必过审 *)
Theorem audit_node_lv2 : forall (p m : DTPT.DTPT.Dig) (v : DTPT_Truth.DTPT_Truth.Evidence),
  audit_node (DTPT_Truth.DTPT_Truth.mkTrNode DTPT_Truth.DTPT_Truth.Lv2 p m v) = true.
Proof.
  intros p m v. unfold audit_node.
  apply andb_true_intro. split.
  - reflexivity.
  - apply (proj2 (Nat.leb_le _ _)). apply DTPT_Truth.DTPT_Truth.ev_size_pos.
Qed.

(* 3.6 桥上审查的定义级相干：铸造节点与对应 Truth 节点同审计值 *)
Theorem audit_node_cast : forall (lv : DTPT.DTPT.Level) (p m : DTPT.DTPT.Dig)
    (v : DTPT.DTPT.Evidence),
  audit_node (cv_node (DTPT.DTPT.mkTrNode lv p m v))
  = audit_node (DTPT_Truth.DTPT_Truth.mkTrNode (cv_lv lv) p m (cv_ev v)).
Proof. reflexivity. Qed.

(* 3.7 桥上审查的语义相干：DTPT 侧节点过桥过审 ⟺ 层判经桥保序
   （消费 audit_node_eq_trLevel + 节点桥投影） *)
Theorem audit_bridge_iff : forall t : DTPT.DTPT.TrNode,
  audit_node (cv_node t) = true <->
  DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv1 (cv_lv (DTPT.DTPT.trLevel t)) = true.
Proof.
  intros t. rewrite audit_node_eq_trLevel.
  unfold DTPT_Truth.DTPT_Truth.trLevel_geq. rewrite cv_node_level. reflexivity.
Qed.

(* 3.8 组合审查定理：门槛单调（llm_gate_pass_mono_thr）× 层判传递
   （trLevel_geq_trans）双通道合流——两通道均为"放宽不降"语义 *)
Theorem audit_gate_level_combo : forall (t : DTPT_Truth.DTPT_Truth.TrNode)
    (a b : DTPT_Truth.DTPT_Truth.Level) (thr1 thr2 H : Q),
  (thr1 <= thr2)%Q ->
  DTPT_Truth.DTPT_Truth.trLevel_geq t a = true ->
  DTPT_Truth.DTPT_Truth.level_le b a = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  DTPT_Truth.DTPT_Truth.trLevel_geq t b = true
  /\ DTPT.DTPT.gate_pass thr2 H = true.
Proof.
  intros t a b thr1 thr2 H Hthr Ha Hab Hgate.
  split.
  - apply (trLevel_geq_trans t a b); assumption.
  - exact (DTPT_LLM.DTPT_LLM.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hgate).
Qed.

(* 3.9 收官：审查器升级（值提升至 Lv2 节点必过审）× 门槛单调合流 *)
Theorem audit_node_chain_combo : forall (t : DTPT_Truth.DTPT_Truth.TrNode)
    (thr1 thr2 H : Q) (p m : DTPT.DTPT.Dig),
  (thr1 <= thr2)%Q ->
  audit_node t = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  audit_node
    (DTPT_Truth.DTPT_Truth.mkTrNode DTPT_Truth.DTPT_Truth.Lv2 p m (DTPT_Truth.DTPT_Truth.trValue t)) = true
  /\ DTPT.DTPT.gate_pass thr2 H = true.
Proof.
  intros t thr1 thr2 H p m Hthr Ha Hg. split.
  - apply audit_node_lv2.
  - exact (DTPT_LLM.DTPT_LLM.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hg).
Qed.

End DTPT_Audit.
Import DTPT_Audit.

(* ========== 四关取证：旗舰假设闭包打印 ========== *)
Print Assumptions cv_size_preservation_T.
Print Assumptions cv_size_preservation_D.
Print Assumptions cv_ev_round_trip_fwd.
Print Assumptions cv_lv_antisym_transport.
Print Assumptions audit_gate_level_combo.
Print Assumptions audit_bridge_iff.
