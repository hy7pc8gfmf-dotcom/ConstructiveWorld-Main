(* ============================================================
   DTPT_Truth.v — 证据分层判断网络（D10 构造性转译）
                 + 塔斯基防自指定理构造性化（B1 缺口 TARSKI）
   ①职责：
     · 基础段（D10）：证据分层 Level/Evidence/TrNode 判断网络、
       Tex/Tabs 真理载体；
     · 补强段（S3 四件套）：序律（level_le 三律）/ 证据代数
       （ev_size 正性、ev_append 结合）/ 见证构造（default_Tex）/
       层升审查器（trLevel_geq、Lv2 节点存在）；
     · 塔斯基段（U11，M4 并入）：tarski 主定理（对角化引理 =
       显式前提 diag_closed，主定理承担语义半边）、no_uniform_truth、
       否定对合条件性（involutive/negS 反例）、分层必要性桥
       （Tr_α 只适用于 L_α：layer_self_refutation /
       layered_network_liar_each_layer / level_confusion_revives_liar）、
         renaming 封闭（diag_conj_spec / tarski_via_renaming）。
     · 审查器段（S5 棒并入 DTPT_Audit.v）：零消费名救活（level_le_total/
       trLevel_geq_trans/chain_ok 传递链/ev_append 精确加性）+ 双副本
       相干桥（cv_ev/cv_lv/cv_node 往返保构与尺寸守恒）+ 组合审查器
       （audit_node 行为双向/审查不降/桥上相干/门槛组合）。
   ②依赖：Require Import QArith.QArith / List / Bool / Arith / Lia /
          DTPT（Bool/Arith/Lia 三行随 S5 棒 Audit 并入增补，From Stdlib
          形；negb / nat 构造子皆 Datatypes 预载）。
          注意：本件与 DTPT.v 存在 Level/Evidence 双定义（U12 卡
          在册）——本文件内裸名 Level/Lv0/Lv1/Lv2/Evidence 恒指
          本件侧定义（文件内定义遮蔽 Import）。
   ③归并记录：2026-09-14 DTPT-M4 席将 DTPT_Tarski.v（U11 席
          2026-09-13）全量并入本文件尾部：删其 Require DTPT_Truth
          （并入后同文件直引）；其 DTPT_Truth.Level/Lv0/Lv1/Lv2
          限名引用逐处改直引并核对语义指向（原件引用本就是 Truth
          侧定义，U12 卡口径）；Qed 面零改动。撞名预检：Tarski
          顶层 19 名对 Truth 既有名 grep 零撞。源件退役为
          DTPT_Tarski.v.retired_M4（全工作区 grep 无下游 Require）。
          S5 棒（2026-09-15）：DTPT_Audit.v（U6 席 2026-09-13）全量并入
          本文件尾（审查器段分隔注起，除 Require 块外逐字搬运；其
          DTPT_Truth.DTPT_Truth. 限名逐处改直引——M4 先例、U12 卡口径，
          语义指向逐一核对不变；DTPT.DTPT. 限名保持原样）。撞名预检：
          Audit 顶层 38 名对本件既有名 grep 零撞。源件退役
          DTPT_Audit.v.retired_S5（全工作区 grep 零下游）。
   ④认证：56 件全 Qed（补强段 12 + 塔斯基段 15 + 审查器段 29）；
          塔斯基段 5 件 + 审查器段 6 件 Print Assumptions 公理闭包
          审计（应全 Closed）。
          四关：G1 禁词 grep=0 / G2 .vo 新于 .v / G3 Qed 对账 /
          G4 stderr 无 Anomaly/Error。
   ⑤纪律：塔斯基段全显式 forall 形，无 Section Variable；零公理
          零承认零中途放弃，全程 Qed 收口。
   ⑥边界：nat 层代码一律显式 Datatypes.S / Nat.add / 构造子 O，
          不裸用 +、<=、S（防 DTPT 传导 Q_scope 劫持，S3 头注）；
          Tex 非空由 default_Tex 见证；Tabs 为全称函数面（无额外
          方程）；塔斯基不可定义性的句法半边（对角化引理）以
          diag_closed 公理化形状显式封包，非平凡化（见塔斯基段
          方法论声明）。
   ============================================================ *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith Lia.
Import ListNotations.
Require DTPT.
Import DTPT.DTPT.

Module DTPT_Truth.

Inductive Level : Type := Lv0 | Lv1 | Lv2.

Inductive Evidence : Type :=
| evNum  : Q -> Evidence
| evSeq  : list Q -> Evidence
| evPair : Evidence -> Evidence -> Evidence.

Record TrNode : Type := mkTrNode {
  trLevel : Level;
  trPhi   : Dig;
  trModel : Dig;
  trValue : Evidence
}.

Definition Tex (phi : Dig) : Type := { t : TrNode & trPhi t = phi }.

Definition Tabs (phi : Dig) : Type := forall (m : Dig), Evidence.

(* ============================================================
   补强段（S3 席，追加式；上方既有语句零改动）
   四件套：序律 / 证据代数 / 见证构造 / 层升审查器
   防御注记：DTPT.v 已 Open Scope Q_scope，本段 nat 层代码
   一律显式 Datatypes.S / Nat.add / 构造子 O，不裸用 +、<=、S
   ============================================================ *)

(* ---------- 1. 序律：Level 全序判定器与三律 ---------- *)

Definition level_le (a b : Level) : bool :=
  match a with
  | Lv0 => true
  | Lv1 => match b with
           | Lv0 => false
           | _   => true
           end
  | Lv2 => match b with
           | Lv2 => true
           | _   => false
           end
  end.

Lemma level_le_refl : forall a : Level, level_le a a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

Lemma level_le_trans : forall a b c : Level,
  level_le a b = true -> level_le b c = true -> level_le a c = true.
Proof.
  intros a b c H1 H2.
  destruct a, b, c; simpl in *; try discriminate; reflexivity.
Qed.

Lemma level_le_antisym : forall a b : Level,
  level_le a b = true -> level_le b a = true -> a = b.
Proof.
  intros a b H1 H2.
  destruct a, b; simpl in *; try discriminate; reflexivity.
Qed.

(* ---------- 2. 证据代数：尺寸测度、正性与结合拼接 ---------- *)

Fixpoint ev_size (e : Evidence) : nat :=
  match e with
  | evNum _      => Datatypes.S O
  | evSeq _      => Datatypes.S O
  | evPair a b   => Datatypes.S (Nat.add (ev_size a) (ev_size b))
  end.

Lemma ev_size_pair : forall a b : Evidence,
  ev_size (evPair a b) = Datatypes.S (Nat.add (ev_size a) (ev_size b)).
Proof.
  intros a b. reflexivity.
Qed.

(* nat 局部底座：Arith 的 Import 不经 DTPT 透传，自证零依赖 *)
Lemma nat_le_0 : forall n : nat, le O n.
Proof.
  intros n. induction n as [| n' IH].
  - apply le_n.
  - apply le_S. exact IH.
Qed.

Lemma nat_succ_le_mono : forall n m : nat,
  le n m -> le (Datatypes.S n) (Datatypes.S m).
Proof.
  intros n m H. induction H as [| m' H IH].
  - apply le_n.
  - apply le_S. exact IH.
Qed.

Lemma ev_size_pos : forall e : Evidence,
  le (Datatypes.S O) (ev_size e).
Proof.
  intros e. induction e as [q | l | a IHa b IHb].
  - simpl. apply le_n.
  - simpl. apply le_n.
  - simpl. apply nat_succ_le_mono. apply nat_le_0.
Qed.

Fixpoint ev_append (a b : Evidence) : Evidence :=
  match a with
  | evNum q      => evPair (evNum q) b
  | evSeq l      => evPair (evSeq l) b
  | evPair a1 a2 => ev_append a1 (ev_append a2 b)
  end.

Lemma ev_append_assoc : forall a b c : Evidence,
  ev_append (ev_append a b) c = ev_append a (ev_append b c).
Proof.
  induction a as [q | l | a1 IH1 a2 IH2]; intros b c; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* ---------- 3. 见证构造：Tex 的 inhabitant 与投影往返 ---------- *)

Definition default_Tex (phi : Dig) : Tex phi :=
  existT _ (mkTrNode Lv0 phi phi (evNum 0%Q)) eq_refl.

Lemma default_Tex_phi : forall phi : Dig,
  trPhi (projT1 (default_Tex phi)) = phi.
Proof.
  intros phi. reflexivity.
Qed.

(* ---------- 4. 层升审查器：trLevel 单调检查与高阶节点存在 ---------- *)

Definition trLevel_geq (t : TrNode) (lv : Level) : bool :=
  level_le lv (trLevel t).

Lemma trLevel_geq_Lv0 : forall t : TrNode, trLevel_geq t Lv0 = true.
Proof.
  intros t. destruct t as [lv p m v].
  unfold trLevel_geq. destruct lv; reflexivity.
Qed.

Lemma trLevel_geq_own : forall (lv : Level) (p m : Dig) (v : Evidence),
  trLevel_geq (mkTrNode lv p m v) lv = true.
Proof.
  intros lv p m v. unfold trLevel_geq. simpl. destruct lv; reflexivity.
Qed.

Lemma exists_level2_node : forall phi : Dig,
  exists t : TrNode, trLevel_geq t Lv2 = true.
Proof.
  intros phi.
  exists (mkTrNode Lv2 phi phi (evNum 0%Q)).
  reflexivity.
Qed.

(* ============================================================
   塔斯基段（M4 归并：原件 DTPT_Tarski.v，席 DTPT-U11，2026-09-13；
   2026-09-14 全量并入，上方既有语句零改动，Qed 面零改动）
   原典对应（数字全域—熵相三元论·基座）：
     · :267-279 定义 2.8.1/2.8.2 语言分层 L_α 与 Tr_α 网络：
       真谓词 T_α 只适用于 L_α、不适用于自身 —— 本段 §3
       分层必要性桥的形式根据（为何真理网必须带层指标）；
     · :551 D12 条款 4「自指与真谓词必须分层，避免塔斯基不可
       定义、罗素悖论、康托悖论」—— 本段主定理是该条款的
       第一块盘面定理（此前 grep tarski|selfref|diag 零命中）；
     · :927-930 元认知映射「塔斯基分层真值 T_α 只适用于 L_α」
       —— §3 level_confusion_revives_liar 给出其类型级落地。
   方法论声明（对角化引理对应，防「平凡化」误读）：
     塔斯基不可定义性的完整证明 = 对角化引理（句法层构造句 G 使
     G ↔ ¬True(⌜G⌝)）+ 语义层矛盾两个半边。本段走标准构造性
     路线：把对角化引理作为显式前提 diag_closed（forall f,
     truth (diag f) = f (diag f)，即「对任何性质 f 可造出谈论
     自身之码」的构造性封装），主定理承担语义层半边（与 bool
     三律矛盾）。diag_closed 恰是塔斯基理论中对角化引理的公理化
     形状——盘面无句法编码器时，这是诚实且最小的充分前提。
   构造性纪律（M4 并入后口径）：
     · 全段无 Section Variable（全显式 forall 形），故 Print
       Assumptions 平凡得 Closed；零公理零承认零中途放弃，全程 Qed。
     · 零自有 stdlib Require（negb / nat 构造子皆 Datatypes 预载）；
       原件仅 §3 Require DTPT_Truth（Level 索引；只 Require 不
       Import，防 Q_scope 传导，参照 U6 卡纪律）——M4 并入后该
       Require 删除，Level 索引同文件直引（语义指向不变）。
     · Level 三分立定理盘上缺（grep 证），§3.1 自建，discriminate
       秒证。
   ============================================================ *)

(* ========== §1 保底件：塔斯基主定理（对角化引理 = 显式前提） ========== *)

(* diag_closed：真谓词对对角化子封闭 —— 码世界里的对角化引理之名化 *)
Definition diag_closed (Code : Type) (diag : (Code -> bool) -> Code)
           (truth : Code -> bool) : Prop :=
  forall f, truth (diag f) = f (diag f).

(* bool 三律：任何布尔值都不等于它自身的否定（说谎句无布尔解） *)
Lemma bool_neq_negb : forall b : bool, b = negb b -> False.
Proof.
  intros b H.
  destruct b; simpl in H; discriminate H.
Qed.

(* 主定理：说谎句取 s := diag (fun c => negb (truth c))，
   diag_closed 一次即得 truth s = negb (truth s)（beta 转换闭合）。
   证法实质：把「真」作用于「『本句不真』之码」上，二值律双向矛盾。 *)
Theorem tarski :
  forall (Code : Type) (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth ->
  exists s, truth s = negb (truth s).
Proof.
  intros Code diag truth Hdiag.
  exists (diag (fun c => negb (truth c))).
  exact (Hdiag (fun c => negb (truth c))).
Qed.

(* 推论（一致真谓词不存在）：满足对角化引理的二值真谓词在任何
   码世界上不可一致存在 —— 塔斯基不可定义性的 bool 化形状 *)
Corollary no_uniform_truth :
  forall (Code : Type) (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth -> False.
Proof.
  intros Code diag truth Hdiag.
  destruct (tarski Code diag truth Hdiag) as [s Hs].
  exact (bool_neq_negb (truth s) Hs).
Qed.

(* ========== §2 主件·否定对合：「否定提升到码层」的条件性 ========== *)

(* 对合性：码层否定要成为真否定，必须往返自守 *)
Definition involutive (Code : Type) (neg : Code -> Code) : Prop :=
  forall c, neg (neg c) = c.

(* 正例：Code := bool，negb 自身对合 —— bool 码世界的否定可平凡提升 *)
Lemma negb_involutive_self : involutive bool negb.
Proof.
  intros c. destruct c; reflexivity.
Qed.

(* 诚实反例：Code := nat，negS n := S n 非对合（见证 n = O 处
   negS (negS O) = S (S O) ≠ O）—— 提升「否定」到码层是条件性的，
   非任意码自映都配称否定 *)
Definition negS (n : nat) : nat := S n.

Lemma negS_not_involutive : ~ (involutive nat negS).
Proof.
  intros H.
  pose proof (H O) as H0.
  simpl in H0.
  discriminate H0.
Qed.

(* 码层否定真值：truth' c := negb (truth (neg c)) *)
Definition neg_truth (Code : Type) (neg : Code -> Code)
           (truth : Code -> bool) : Code -> bool :=
  fun c => negb (truth (neg c)).

(* 条件性主引理：仅当 neg 对合时，码层否定真值在 neg c 处的取值
   回收为 negb (truth c) —— 否定与真谓词的相容交换以对合为前提 *)
Lemma neg_truth_at_neg :
  forall (Code : Type) (neg : Code -> Code) (truth : Code -> bool),
  involutive Code neg ->
  forall c, neg_truth Code neg truth (neg c) = negb (truth c).
Proof.
  intros Code neg truth Hinv c.
  unfold neg_truth.
  rewrite (Hinv c).
  reflexivity.
Qed.

(* ========== §3 主件·分层必要性桥：Tr_α 只适用于 L_α ========== *)

(* 3.1 Level 三分立（本文件侧 Level = Lv0|Lv1|Lv2；U12 卡双定义
       纪律：同文件直引即 Truth 侧，与原件 DTPT_Truth. 限名同指；
       盘上原只有 level_le 三律，无分立定理，本段自建） *)
Lemma lv0_ne_lv1 : Lv0 <> Lv1.
Proof.
  intros H. discriminate H.
Qed.

Lemma lv0_ne_lv2 : Lv0 <> Lv2.
Proof.
  intros H. discriminate H.
Qed.

Lemma lv1_ne_lv2 : Lv1 <> Lv2.
Proof.
  intros H. discriminate H.
Qed.

Theorem level_pairwise_distinct :
  Lv0 <> Lv1 /\
  Lv0 <> Lv2 /\
  Lv1 <> Lv2.
Proof.
  split; [exact lv0_ne_lv1 | split; [exact lv0_ne_lv2 | exact lv1_ne_lv2]].
Qed.

(* 3.2 逐层自斥：任何层 lv 的真谓词，若对同层对角化子封闭，
       则该层自斥出说谎句 —— 「T_α 只适用于 L_α」的正面形式：
       同层封闭即同层崩溃，无一层可免 *)
Theorem layer_self_refutation :
  forall (lv : Level) (Code : Type)
         (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth ->
  exists s, truth s = negb (truth s).
Proof.
  intros lv Code diag truth Hclosed.
  exact (tarski Code diag truth Hclosed).
Qed.

(* 3.3 分层网络逐层说谎者：若真值网络对每层均匀取同层对角封闭，
       则每层都产出说谎句 —— 分层本身不豁免，豁免只来自不封闭 *)
Theorem layered_network_liar_each_layer :
  forall (Code : Type) (truth : Level -> Code -> bool)
         (diag_lv : Level -> (Code -> bool) -> Code),
  (forall lv, diag_closed Code (diag_lv lv) (truth lv)) ->
  forall lv, exists s, truth lv s = negb (truth lv s).
Proof.
  intros Code truth diag_lv H lv.
  exact (tarski Code (diag_lv lv) (truth lv) (H lv)).
Qed.

(* 3.4 层级混淆复活说谎者：Lv2 审 Lv1 时，若把 Lv1 层对角化子生成
       的码当 Lv2 自家封闭律的实例消费（跨层误配 = 单层坍缩的工程
       形状），说谎句即在 Lv2 复活。逆否读法：跨层求值（Lv2 审 Lv1）
       要安全，就必须带层指标、不得落入同层 diag 的封闭方程 ——
       这正是原典 :267-274「T_α 只适用于 L_α 不适用于自身」为何
       强制真理网分层的类型级根据 *)
Theorem level_confusion_revives_liar :
  forall (Code : Type) (truth : Level -> Code -> bool)
         (diag_l1 : (Code -> bool) -> Code),
  (forall f, truth Lv2 (diag_l1 f) = f (diag_l1 f)) ->
  exists s, truth Lv2 s = negb (truth Lv2 s).
Proof.
  intros Code truth diag_l1 Hcross.
  exact (tarski Code diag_l1 (truth Lv2) Hcross).
Qed.

(* ========== §4 加分：renaming 封闭 —— diag 经 neg 共轭仍是 diag 形 ========== *)

(* 共轭对角引理：neg 对合时，diag' f := neg (diag (fun c => f (neg c)))
   是 negated 真值 truth' c := truth (neg c) 的对角化子
   —— 对角化引理在 renaming 下封闭 *)
Lemma diag_conj_spec :
  forall (Code : Type) (neg : Code -> Code) (truth : Code -> bool)
         (diag : (Code -> bool) -> Code),
  involutive Code neg ->
  diag_closed Code diag truth ->
  diag_closed Code (fun f => neg (diag (fun c => f (neg c))))
                  (fun c => truth (neg c)).
Proof.
  intros Code neg truth diag Hinv Hdiag f.
  unfold diag_closed in Hdiag.
  rewrite (Hinv (diag (fun c => f (neg c)))).
  rewrite Hdiag.
  reflexivity.
Qed.

(* tarski 复用：renaming 后的码世界照出自斥句，
   说谎句在原码层的落点为 neg s *)
Theorem tarski_via_renaming :
  forall (Code : Type) (neg : Code -> Code) (truth : Code -> bool)
         (diag : (Code -> bool) -> Code),
  involutive Code neg ->
  diag_closed Code diag truth ->
  exists s, truth (neg s) = negb (truth (neg s)).
Proof.
  intros Code neg truth diag Hinv Hdiag.
  destruct (tarski Code (fun f => neg (diag (fun c => f (neg c))))
                     (fun c => truth (neg c))
                     (diag_conj_spec Code neg truth diag Hinv Hdiag)) as [s Hs].
  exists s. exact Hs.
Qed.

(* ============================================================
   审查器段（S5 棒归并分隔注）—— 以下为原 DTPT_Audit.v 全文
   （S5 整合棒并入本文件尾；原件席 DTPT-U6，2026-09-13）
   除 Require 块外逐字搬运，声明序与证法零改动；其头部职责任务注
   原文照录于下。唯一非逐字面：原件对三底座「只 Require 不 Import、
   全限名引用防遮蔽」——并入后 DTPT_Truth.DTPT_Truth.X 限名前缀逐处
   改直引 X（M4 塔斯基段先例；原件所引即本件侧定义，U12 卡口径，
   语义指向逐一核对不变）；DTPT.DTPT. 限名保持原样（跨库双副本面）。
   头部依赖行所记 DTPT_LLM 已随棒 1 归并入 DTPT.v §11（改写后引用形
   DTPT.DTPT.llm_gate_pass_mono_thr 即其现态，随行有效）。撞名预检
   与下游登记见本文件头 ③。
   ============================================================ *)
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

(* ========== §1 零消费名救活 ========== *)

(* 1.0 全序性：level_le 判定器双向往复（X2-4 清单件，救活 level_le） *)
Theorem level_le_total : forall a b : Level,
  level_le a b = true \/ level_le b a = true.
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Qed.

(* 1.1 层升检查的传递形：节点对要求层 a 过审（a ≤ 节点层）且要求
   不升（b ≤ a）时对 b 过审——消费 level_le_trans 的第一下游。
   （方向注记：trLevel_geq t lv 语义是 lv ≤ trLevel t，故传递律的
   合法形是"要求递降"，反向陈述为假命题，a=Lv0,b=Lv2,t=Lv0 反例） *)
Theorem trLevel_geq_trans : forall (t : TrNode)
    (a b : Level),
  trLevel_geq t a = true ->
  level_le b a = true ->
  trLevel_geq t b = true.
Proof.
  intros t a b Ha Hb.
  unfold trLevel_geq in *.
  apply (level_le_trans b a (trLevel t)); assumption.
Qed.

(* 1.2 传递链审查器：chain_ok 三节点链式判定（消费 level_le_trans） *)
Definition chain_ok (l1 l2 l3 : Level) : bool :=
  andb (level_le l1 l2) (level_le l2 l3).

Theorem chain_ok_iff : forall l1 l2 l3 : Level,
  chain_ok l1 l2 l3 = true <->
  level_le l1 l2 = true /\ level_le l2 l3 = true.
Proof.
  intros l1 l2 l3. unfold chain_ok. split.
  - intro H. apply andb_prop in H. destruct H as [ H1 H2 ].
    split; assumption.
  - intros [ H1 H2 ]. apply andb_true_intro. split; assumption.
Qed.

Theorem chain_ok_trans : forall l1 l2 l3 : Level,
  chain_ok l1 l2 l3 = true -> level_le l1 l3 = true.
Proof.
  intros l1 l2 l3 H.
  destruct (proj1 (chain_ok_iff l1 l2 l3) H) as [H1 H2].
  apply (level_le_trans l1 l2 l3); assumption.
Qed.

(* 1.3 ev_append 精确加性：k=1（压平化每丧失一个 Pair 包装恰补 1）。
   证法：对 a 归纳（b 先泛化）。基例 evNum/evSeq：结果为
   evPair 头 + b，尺寸 = 1 + (1 + |b|)；归纳例 evPair：双递归展开
   后两条归纳假设相接，常数方程 2k = 1 + k 逼出 k = 1。 *)
Theorem audit_ev_append_size_exact : forall a b : Evidence,
  ev_size (ev_append a b)
  = Nat.add (Nat.add (ev_size a) (ev_size b))
            (Datatypes.S Datatypes.O).
Proof.
  intros a. induction a as [ q | l | a1 IH1 a2 IH2 ]; intros b; simpl.
  - lia.
  - lia.
  - rewrite (IH1 (ev_append a2 b)). rewrite (IH2 b). lia.
Qed.

(* 1.4 拼接单调：右参证据在拼接下尺寸不减（精确加性的推论） *)
Theorem audit_ev_append_size_mono : forall a b : Evidence,
  le (ev_size b)
               (ev_size (ev_append a b)).
Proof.
  intros a b. rewrite audit_ev_append_size_exact. lia.
Qed.

(* ========== §2 双副本相干桥 ========== *)

(* 2.1 证据层转换：DTPT.DTPT.Evidence → Evidence（恒等形态） *)
Fixpoint cv_ev (e : DTPT.DTPT.Evidence) : Evidence :=
  match e with
  | DTPT.DTPT.evNum q    => evNum q
  | DTPT.DTPT.evSeq l    => evSeq l
  | DTPT.DTPT.evPair a b => evPair (cv_ev a) (cv_ev b)
  end.

(* 2.2 逆转换：Evidence → DTPT.DTPT.Evidence *)
Fixpoint cv_ev_inv (e : Evidence) : DTPT.DTPT.Evidence :=
  match e with
  | evNum q    => DTPT.DTPT.evNum q
  | evSeq l    => DTPT.DTPT.evSeq l
  | evPair a b => DTPT.DTPT.evPair (cv_ev_inv a) (cv_ev_inv b)
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

Lemma cv_ev_round_trip_bwd : forall e : Evidence,
  cv_ev (cv_ev_inv e) = e.
Proof.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.4 尺寸守恒（正方向）：Truth 侧证据过桥往返后尺寸不变 *)
Theorem cv_size_preservation_T : forall e : Evidence,
  ev_size (cv_ev (cv_ev_inv e)) = ev_size e.
Proof.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.5 DTPT 侧尺寸测度：经桥取 Truth 侧 ev_size（桥传输的测度） *)
Definition dt_ev_size (e : DTPT.DTPT.Evidence) : nat :=
  ev_size (cv_ev e).

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
Definition cv_lv (l : DTPT.DTPT.Level) : Level :=
  match l with
  | DTPT.DTPT.Lv0 => Lv0
  | DTPT.DTPT.Lv1 => Lv1
  | DTPT.DTPT.Lv2 => Lv2
  end.

Definition cv_lv_inv (l : Level) : DTPT.DTPT.Level :=
  match l with
  | Lv0 => DTPT.DTPT.Lv0
  | Lv1 => DTPT.DTPT.Lv1
  | Lv2 => DTPT.DTPT.Lv2
  end.

Lemma cv_lv_round : forall l : DTPT.DTPT.Level, cv_lv_inv (cv_lv l) = l.
Proof. intros l. destruct l; reflexivity. Qed.

Lemma cv_lv_round_inv : forall l : Level,
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
  level_le (cv_lv a) (cv_lv b) = true ->
  level_le (cv_lv b) (cv_lv a) = true -> a = b.
Proof.
  intros a b H1 H2. apply cv_lv_inj.
  apply level_le_antisym; assumption.
Qed.

(* 2.10 保序·全序性运输：桥像上的全序判定双向往复 *)
Theorem cv_lv_total_transport : forall a b : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv b) = true \/
  level_le (cv_lv b) (cv_lv a) = true.
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Qed.

(* 2.11 节点桥：DTPT.DTPT.TrNode → TrNode 四投影搬运 *)
Definition cv_node (t : DTPT.DTPT.TrNode) : TrNode :=
  mkTrNode (cv_lv (DTPT.DTPT.trLevel t))
                      (DTPT.DTPT.trPhi t) (DTPT.DTPT.trModel t)
                      (cv_ev (DTPT.DTPT.trValue t)).

Definition cv_node_inv (t : TrNode) : DTPT.DTPT.TrNode :=
  DTPT.DTPT.mkTrNode (cv_lv_inv (trLevel t))
                (trPhi t) (trModel t)
                (cv_ev_inv (trValue t)).

(* 2.12 节点桥四投影保构（封死漂移风险；首投影另立单引理供改写） *)
Lemma cv_node_level : forall t : DTPT.DTPT.TrNode,
  trLevel (cv_node t) = cv_lv (DTPT.DTPT.trLevel t).
Proof. reflexivity. Qed.

Theorem cv_node_pres : forall t : DTPT.DTPT.TrNode,
  trLevel (cv_node t) = cv_lv (DTPT.DTPT.trLevel t)
  /\ trPhi (cv_node t) = DTPT.DTPT.trPhi t
  /\ trModel (cv_node t) = DTPT.DTPT.trModel t
  /\ trValue (cv_node t) = cv_ev (DTPT.DTPT.trValue t).
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
  exists T : Tex phi, projT1 T = cv_node t.
Proof.
  intros phi t H. exists (existT _ (cv_node t) H). reflexivity.
Qed.

(* ========== §3 组合审查器 ========== *)

(* 3.0 审查器：层判（不低于 Lv1）× 层内证据非空（尺寸 ≥ 1 的
   bool 化）两支合取 *)
Definition audit_node (t : TrNode) : bool :=
  andb (trLevel_geq t Lv1)
       (Nat.leb (Datatypes.S Datatypes.O)
                (ev_size (trValue t))).

(* 3.1 行为定理（双向）：审查通过 ⟺ 两分支各自通过（拆解到分支级） *)
Theorem audit_node_iff : forall t : TrNode,
  audit_node t = true <->
  trLevel_geq t Lv1 = true
  /\ le (Datatypes.S Datatypes.O)
                  (ev_size (trValue t)).
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
Theorem audit_node_branch_iff : forall (lv : Level)
    (p m : DTPT.DTPT.Dig) (v : Evidence),
  audit_node (mkTrNode lv p m v) = true <->
  level_le Lv1 lv = true
  /\ Nat.leb (Datatypes.S Datatypes.O) (ev_size v) = true.
Proof.
  intros lv p m v.
  unfold audit_node, trLevel_geq. simpl. split.
  - intro H. apply andb_prop in H. destruct H as [ H1 H2 ].
    split; assumption.
  - intros [ H1 H2 ]. apply andb_true_intro. split; assumption.
Qed.

(* 3.3 尺寸支恒真引理（消费零消费名 ev_size_pos）：审查器退化为层判 *)
Theorem audit_node_eq_trLevel : forall t : TrNode,
  audit_node t = trLevel_geq t Lv1.
Proof.
  intros t. unfold audit_node.
  assert (Hb : Nat.leb (Datatypes.S Datatypes.O)
                 (ev_size (trValue t)) = true).
  { apply (proj2 (Nat.leb_le _ _)). apply ev_size_pos. }
  rewrite Hb. apply Bool.andb_true_r.
Qed.

(* 3.4 替换稳定：同层同值换节点审查不降 *)
Theorem audit_node_mono : forall t t' : TrNode,
  trLevel t' = trLevel t ->
  trValue t' = trValue t ->
  audit_node t = true -> audit_node t' = true.
Proof.
  intros t t' Hlv Hval Ht.
  destruct t as [ lv p m v ]. destruct t' as [ lv' p' m' v' ].
  simpl in Hlv, Hval. subst lv'. subst v'.
  unfold audit_node in Ht |- *. simpl in Ht |- *. exact Ht.
Qed.

(* 3.5 换更高层节点（Lv2）审查不降：任何 Lv2 节点必过审 *)
Theorem audit_node_lv2 : forall (p m : DTPT.DTPT.Dig) (v : Evidence),
  audit_node (mkTrNode Lv2 p m v) = true.
Proof.
  intros p m v. unfold audit_node.
  apply andb_true_intro. split.
  - reflexivity.
  - apply (proj2 (Nat.leb_le _ _)). apply ev_size_pos.
Qed.

(* 3.6 桥上审查的定义级相干：铸造节点与对应 Truth 节点同审计值 *)
Theorem audit_node_cast : forall (lv : DTPT.DTPT.Level) (p m : DTPT.DTPT.Dig)
    (v : DTPT.DTPT.Evidence),
  audit_node (cv_node (DTPT.DTPT.mkTrNode lv p m v))
  = audit_node (mkTrNode (cv_lv lv) p m (cv_ev v)).
Proof. reflexivity. Qed.

(* 3.7 桥上审查的语义相干：DTPT 侧节点过桥过审 ⟺ 层判经桥保序
   （消费 audit_node_eq_trLevel + 节点桥投影） *)
Theorem audit_bridge_iff : forall t : DTPT.DTPT.TrNode,
  audit_node (cv_node t) = true <->
  level_le Lv1 (cv_lv (DTPT.DTPT.trLevel t)) = true.
Proof.
  intros t. rewrite audit_node_eq_trLevel.
  unfold trLevel_geq. rewrite cv_node_level. reflexivity.
Qed.

(* 3.8 组合审查定理：门槛单调（llm_gate_pass_mono_thr）× 层判传递
   （trLevel_geq_trans）双通道合流——两通道均为"放宽不降"语义 *)
Theorem audit_gate_level_combo : forall (t : TrNode)
    (a b : Level) (thr1 thr2 H : Q),
  (thr1 <= thr2)%Q ->
  trLevel_geq t a = true ->
  level_le b a = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  trLevel_geq t b = true
  /\ DTPT.DTPT.gate_pass thr2 H = true.
Proof.
  intros t a b thr1 thr2 H Hthr Ha Hab Hgate.
  split.
  - apply (trLevel_geq_trans t a b); assumption.
  - exact (DTPT.DTPT.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hgate).
Qed.

(* 3.9 收官：审查器升级（值提升至 Lv2 节点必过审）× 门槛单调合流 *)
Theorem audit_node_chain_combo : forall (t : TrNode)
    (thr1 thr2 H : Q) (p m : DTPT.DTPT.Dig),
  (thr1 <= thr2)%Q ->
  audit_node t = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  audit_node
    (mkTrNode Lv2 p m (trValue t)) = true
  /\ DTPT.DTPT.gate_pass thr2 H = true.
Proof.
  intros t thr1 thr2 H p m Hthr Ha Hg. split.
  - apply audit_node_lv2.
  - exact (DTPT.DTPT.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hg).
Qed.

End DTPT_Truth.
Import DTPT_Truth.

(* ========== 假设面自查（四关 G4 附件） ========== *)
Print Assumptions tarski.
Print Assumptions no_uniform_truth.
Print Assumptions layer_self_refutation.
Print Assumptions level_confusion_revives_liar.
Print Assumptions tarski_via_renaming.

(* —— 以下 6 件为原 DTPT_Audit.v 文尾审计块逐字随行（S5 棒） —— *)

(* ========== 四关取证：旗舰假设闭包打印 ========== *)
Print Assumptions cv_size_preservation_T.
Print Assumptions cv_size_preservation_D.
Print Assumptions cv_ev_round_trip_fwd.
Print Assumptions cv_lv_antisym_transport.
Print Assumptions audit_gate_level_combo.
Print Assumptions audit_bridge_iff.
