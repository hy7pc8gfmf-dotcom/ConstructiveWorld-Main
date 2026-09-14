(* ============================================================
   DTPT_Bridge.v — P3 桥接层首件（席 P3-B1，2026-09-14）
   职责：DTPT 冻结旗舰的 Set 层信息性桥接——
         §1 信息性比较类型族 Type 版（QleT/QltT/QeqT，单构造子
            携 Prop 证明参数＝提取擦除惯例）+ Qle 双向桥 + 传播引理
         §2 主库惯例镜像件（And := A*B、ExistsT := sigT 本地同构
            Type 版；DTPT 隔离区不 Require 主库）
         §3 旗舰桥三件：C_sorted_min_adj_set / C_gen_set /
            H_devsum_nonneg_set（陈述 QleT 面，证明＝Prop 版直构包装）
         §4 Extraction 探针：对桥件本身提取，验收 Obj.magic=0 实测
   依赖：DTPT（冻结旗舰，只读 Require）、DTPT_Entropy（H_devsum
         所在件，只读消费——ADJ-1 改名点 L42、非负件
         H_shannon_q_nonneg L116；只读 Require 先例＝DTPT_Extract.v
         L33）、stdlib（QArith/List/Permutation/Extraction）。
   主库惯例对应（详见 DTPT_P3B1_桥接报告.md）：
         ConstructiveWorld_Live 不 Require（DTPT 隔离区纪律），本地
         同名同构 Type 版——
         S02 L26 QltT := Id (Qlt_bool x y) true
         S02 L27 QleT := Or (QltT x y) (Id x y)
         S02 L77 QleT' := Id (Qle_bool x y) true
         S01 L68 And (A B : Set) := A * B
         S01 L73 ExistsT P := sigT P
         本件比较族改取「单构造子归纳＋Prop 证明参数」形（任务书
         指定）：信息角色与提取行为同构（Prop 参提取即擦除），
         并避开主库 Or/Id 形在隔离区缺 Id 底座的依赖。
   命名：沿用任务书指定名；模块 DTPT_Bridge 限名隔离防撞。
   认证目标：零承认零公理；Error=0 Warning=0；Obj.magic=0 实测。
   纪律：温控协议 v2（coqc 全机 ≤3 先查后编）；禁碰既有 .v；
         H_freq/Entropy 族桥留待后续棒（Entropy 置换不变命题经
         DTPT_Entropy.v L125 在案核查为假命题，禁桥假命题）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* 归纳参数在构造子上自动隐式（主库 conj 风格：qleT_intro H 直构） *)
Set Implicit Arguments.

Require DTPT.
Require DTPT_Entropy.
(* P3-B3 追加：真理网/审查器冻结终态（835 行）只读消费；
   只 Require 不 Import（Import 置于 §7 内，防对 B1/B2 段遮蔽）。
   注：Module 内 Require 实测触发 require-in-module fragile 警告，
   破零警告关，故置文件头——B1/B2 段零改动，仅此一行插入。 *)
Require DTPT_Truth.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Bridge.

(* ========== §1 信息性比较类型族（Type 版，主库 S02 同构镜像） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Inductive QltT (x y : Q) : Type :=
| qltT_intro : (x < y)%Q -> QltT x y.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

(* Qle 双向桥：直构入桥 / 模式匹配抽取 *)
Definition QleT_of_Qle {x y : Q} (H : (x <= y)%Q) : QleT x y :=
  qleT_intro H.

Definition QleT_to_Qle {x y : Q} (Hq : QleT x y) : (x <= y)%Q :=
  match Hq with qleT_intro Hp => Hp end.

(* Qlt/Qeq 同族双向桥（同构镜像同形） *)
Definition QltT_of_Qlt {x y : Q} (H : (x < y)%Q) : QltT x y :=
  qltT_intro H.

Definition QltT_to_Qlt {x y : Q} (Hq : QltT x y) : (x < y)%Q :=
  match Hq with qltT_intro Hp => Hp end.

Definition QeqT_of_Qeq {x y : Q} (H : (x == y)%Q) : QeqT x y :=
  qeqT_intro H.

Definition QeqT_to_Qeq {x y : Q} (Hq : QeqT x y) : (x == y)%Q :=
  match Hq with qeqT_intro Hp => Hp end.

(* 传播引理：QltT 传 QleT——stdlib QArith 本环境无 Qlt_le（CS1 卡
   第 4 条实测口径），按在案处方 unfold Qlt/Qle 后 lia 收口 *)
Definition QltT_QleT {x y : Q} (Hq : QltT x y) : QleT x y.
Proof.
  destruct Hq as [Hlt]. apply qleT_intro. unfold Qle. unfold Qlt in Hlt. lia.
Defined.

(* ========== §2 主库惯例镜像件（S01 本地同构 Type 版） ========== *)

Definition And (A B : Type) : Type := A * B.
Definition ExistsT {A : Type} (P : A -> Type) : Type := sigT P.

(* ========== §3 旗舰桥三件（陈述 QleT 面，证明＝Prop 版包装；
     提取面消费件故取 Defined——避免 opaque-accessed 提取警告） ========== *)

(* 旗舰一：排序最小化——DTPT.v L729 C_sorted_min_adj 的 Set 形重述 *)
Theorem C_sorted_min_adj_set : forall l : list Q,
  QleT (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply qleT_intro. exact (C_sorted_min_adj l).
Defined.

(* 旗舰二：置换泛化——DTPT.v L968 C_gen（M1 并入件）的 Set 形重述 *)
Theorem C_gen_set : forall l p : list Q,
  Permutation l p -> QleT (H_adj (P0 l)) (H_adj p).
Proof.
  intros l p Hp. apply qleT_intro. exact (C_gen l p Hp).
Defined.

(* 旗舰三：H_devsum 非负——ADJ-1 改名现名（DTPT_Entropy.v L42 定义点），
   Prop 版＝DTPT_Entropy.v L116 H_shannon_q_nonneg 的 Set 形重述 *)
Theorem H_devsum_nonneg_set : forall l : list Q,
  QleT 0 (H_devsum l).
Proof.
  intro l. apply qleT_intro. exact (H_shannon_q_nonneg l).
Defined.

(* ========== §4 Extraction 探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

(* 产物落工作区显式化（消 extraction-default-directory 警告） *)
Set Extraction Output Directory ".".

Extraction "b1_QleT_ext.ml" QleT.
Extraction "b1_QltT_ext.ml" QltT.
Extraction "b1_QeqT_ext.ml" QeqT.
Extraction "b1_QleT_of_Qle_ext.ml" QleT_of_Qle.
Extraction "b1_C_sorted_min_adj_set_ext.ml" C_sorted_min_adj_set.
Extraction "b1_C_gen_set_ext.ml" C_gen_set.
Extraction "b1_H_devsum_nonneg_set_ext.ml" H_devsum_nonneg_set.

(* ========== §5 P3-B2 追加：熵族旗舰 Set 形桥接（2026-09-14） ==========
   前置核查裁决（详见 DTPT_P3B2_桥接报告.md §1）：
   DTPT_Entropy.v L125 注记所指命题＝「H_devsum 置换不变」（质心偏移
   占位形；盘上 H_shannon_q_perm_inv_counterex 已构造性证伪，反例
   [3;1;2] vs [2;1;3] 机检在案），与 §A2 H_freq_perm（真频率形
   1−Σp_v²，真）为不同载体、不同命题——裁决＝②不同命题且确为假
   （B1 标记无误，注记零改动）。本节桥 H_freq 面不触碰 H_devsum
   置换面，无假命题入桥。
   消费盘上已证件（全部只读）：
     H_freq_perm（DTPT_Entropy.v L1239）；collide_lower L1757 /
     collide_le_maxfreq L1794 / maxfreq_upper L1849（即 H_chain
     L1903 三成员）；H_shannon_q_zero_iff_sorted L2484 与 stdlib
     Qeq_bool_iff；freq_perm（DTPT.v L1974）；
     mu_total_mass（DTPT.v L2094）。
   类型注记：任务书草式「1 # Z.of_nat (length l)」的 # 分母须
   positive 实参（Measure 卡同族坑：# 不可吃 Z），盘上类型正确形
   ＝ 1 / qn (length l)（collide_lower / maxfreq_lower 同面），
   从盘面。 *)

(* 保底件：H_freq 置换不变 Set 形（消费 DTPT_Entropy.v L1239 旗舰） *)
Theorem H_freq_perm_set : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeqT_intro. exact (H_freq_perm l p Hp).
Defined.

(* 旗舰：Rényi 阶梯 Set 形——非空表 1/n <= collide <= maxfreq <= 1
   一次入链（合取用 B1 §2 基建 And := A*B 信息性 Type 版） *)
Theorem H_chain_set : forall l : list Q, (0 < length l)%nat ->
  And (QleT (1 / qn (length l)) (collide l))
      (And (QleT (collide l) (maxfreq l)) (QleT (maxfreq l) 1)).
Proof.
  intros l Hl. unfold And. split.
  - apply qleT_intro. exact (collide_lower l Hl).
  - split.
    + apply qleT_intro. exact (collide_le_maxfreq l).
    + apply qleT_intro. exact (maxfreq_upper l).
Defined.

(* 主件：H_devsum 零点对照 Set 面——Qeq_bool 判定零点，经盘上
   iff 定理给出升序性的信息性载体（sumbool 形；判真支消费 iff
   正向，判假支经 qeqb_false_neq 反证非升序） *)
Definition H_devsum_zero_iff_sorted_set (l : list Q) :
  {SortedQ l} + {~ SortedQ l}.
Proof.
  destruct (Qeq_bool (H_devsum l) 0) eqn:Eb.
  - left. exact (proj1 (H_shannon_q_zero_iff_sorted l)
                   (proj1 (Qeq_bool_iff (H_devsum l) 0) Eb)).
  - right. intro Hs.
    assert (Hc : Qeq_bool (H_devsum l) 0 = true).
    { apply (proj2 (Qeq_bool_iff (H_devsum l) 0)).
      exact (proj2 (H_shannon_q_zero_iff_sorted l) Hs). }
    congruence.
Defined.

(* 加分一：freq 置换不变 Set 形——freq 为 nat 值，Q 域信息载体取
   mu l x 的分子面 (Z.of_nat (freq l x) # 1)%Q（# 须 positive 实参，
   故 # 1 归一，同 DTPT.v §12 mu 定义面）；消费 DTPT.v L1974 *)
Theorem freq_perm_set : forall (l p : list Q) (x : Q),
  Permutation l p ->
  QeqT ((Z.of_nat (freq l x) # 1)%Q) ((Z.of_nat (freq p x) # 1)%Q).
Proof.
  intros l p x Hp. apply qeqT_intro.
  rewrite (freq_perm l p x Hp). apply Qeq_refl.
Defined.

(* 加分二：均匀测度总质量一 Set 形（消费 DTPT.v L2094） *)
Theorem mu_total_mass_set : forall l : list Q, l <> [] ->
  QeqT (qsum (map (mu l) (dedup l))) 1.
Proof.
  intro l. intro Hne. apply qeqT_intro. exact (mu_total_mass l Hne).
Defined.

(* ========== §6 P3-B2 提取探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b2_H_freq_perm_set_ext.ml" H_freq_perm_set.
Extraction "b2_H_chain_set_ext.ml" H_chain_set.
Extraction "b2_H_devsum_zero_iff_sorted_set_ext.ml" H_devsum_zero_iff_sorted_set.
Extraction "b2_freq_perm_set_ext.ml" freq_perm_set.
Extraction "b2_mu_total_mass_set_ext.ml" mu_total_mass_set.

(* ========== §7 P3-B3 追加：真理网/审查器旗舰 Set 形桥接（2026-09-15） ==========
   消费盘上已证件（DTPT_Truth.v 835 行冻结终态，全部只读）：
     level_le L89 / level_le_total L468 / trLevel_geq_trans L480 /
     audit_node L700 / diag_closed L247（对角化引理＝显式前提，
     参数形照盘上现役陈述 diag_closed Code diag truth 三参显式）/
     bool_neq_negb L252 / layered_network_liar_each_layer L368 /
     cv_size_preservation_T L574 / cv_size_preservation_D L588 /
     cv_lv L599 / dt_ev_size L584。
   基建：沿用 B1 §1 QleT/QeqT 族与 §2 And/sigT 信息性 Type 惯例；
     全部 Defined（提取消费件惯例，B1 坑④）；sumbool/sigT 直构。
   Tarski 语义边界声明（随行）：对角化引理＝显式前提 diag_closed
     ——与盘上塔斯基段同口径，本棒不证对角化引理本身（盘面无句法
     编码器，diag_closed 恰是其公理化形状）；tarski_set 的升级点＝
     盘上 tarski（L261）Prop 形 exists 的 Set 形重述，说谎句见证以
     sigT 信息性携带（见证码可计算交付，真值方程证明为 Prop 参随
     提取擦除）。liar_diag 为可执行码面对角构造器，其「闭包」语义
     由 diag_closed 前提承担（本棒不证 liar_diag closed——对任意
     具体闭包对角子 no_uniform_truth 即假，故诚实立场是不证）；
     liar_diag_point 为反面互补＝bool 三律下无码点满足对角方程
     （Prop 面，不提取）。
   层网面（§7.4）：码世界固定为 Dig、层索引为 Truth 侧 Level
     （盘上 layered_network_liar_each_layer 的 Code 一般形在本件
     取 Dig 实例，与 liar_diag 码面同世界）。
   ============================================================ *)

Import DTPT_Truth.DTPT_Truth.

(* ---------- 7.1 保底件：审查器可执行 Set 面 ---------- *)

(* 判定器完整性：audit_node 对任意节点可执行判定（sumbool 直构，
   bool 计算分支即判定；盘上双向行为定理 audit_node_iff L706 的
   判定面底座） *)
Theorem audit_node_spec_set : forall t : TrNode,
  {audit_node t = true} + {audit_node t = false}.
Proof.
  intro t. destruct (audit_node t).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* 层判 Set 面判定器：trLevel_geq 对任意节点/层可执行判定 *)
Theorem trLevel_geq_spec_set : forall (t : TrNode) (lv : Level),
  {trLevel_geq t lv = true} + {trLevel_geq t lv = false}.
Proof.
  intros t lv. destruct (trLevel_geq t lv).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* 层升单调 Set 形：节点对 a 层过审时对不升要求 b 的判定转移——
   左支消费盘上 trLevel_geq_trans（L480），右支以 bool 判定见证
   「要求未降」（level_le b a = false，level_le L89 计算面） *)
Theorem trLevel_geq_mono_set : forall (t : TrNode) (a b : Level),
  trLevel_geq t a = true ->
  {trLevel_geq t b = true} + {level_le b a = false}.
Proof.
  intros t a b Ha. destruct (level_le b a) eqn:E.
  - left. exact (trLevel_geq_trans t a b Ha E).
  - right. reflexivity.
Defined.

(* 全序 Set 面：level_le 判定器双向往复的信息性形——与盘上
   level_le_total（L468）同真值面；Prop \/ 不可消除入 Set，本件
   为 Level 三层九格穷举直构（判定器计算面，诚实声明非 Prop 消费） *)
Theorem level_le_total_set : forall a b : Level,
  {level_le a b = true} + {level_le b a = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.2 旗舰：塔斯基可判定面（sigT 信息性说谎句见证） ---------- *)

(* 对角构造器（可执行码面）：把码 c 与其自身真值的 negb 反射打包为
   说谎码——truth c = true 时码内嵌 0、false 时内嵌 1（Q 编码走
   if 计算面）。闭包语义由 diag_closed 前提承担（边界声明见 §7 头注） *)
Definition liar_diag (truth : Dig -> bool) (c : Dig) : Dig :=
  dPair c (dQ (if negb (truth c) then 1%Q else 0%Q)).

(* 旗舰·塔斯基 Set 形：diag_closed 照盘上现役三参陈述，见证
   s := diag (fun c => negb (truth c)) 以 sigT 信息性携带——对照盘上
   tarski（L261）Prop 形 exists，Set 形升级点＝说谎句见证可计算交付 *)
Theorem tarski_set : forall (truth : Dig -> bool)
    (diag : (Dig -> bool) -> Dig),
  diag_closed Dig diag truth ->
  {s : Dig & truth s = negb (truth s)}.
Proof.
  intros truth diag Hcl.
  exact (existT _ (diag (fun c => negb (truth c)))
                  (Hcl (fun c => negb (truth c)))).
Defined.

(* 对角方程的 bool 三律互补面：无任何码点满足对角方程（消费盘上
   bool_neq_negb L252）——与 tarski_set 合读即 no_uniform_truth
   的两面：闭包前提造见证，三律封死解。Prop 面，不提取 *)
Theorem liar_diag_point : forall (truth : Dig -> bool) (c : Dig),
  truth (liar_diag truth c) = negb (truth (liar_diag truth c)) -> False.
Proof.
  intros truth c H.
  exact (bool_neq_negb (truth (liar_diag truth c)) H).
Defined.

(* ---------- 7.3 主件：双副本相干桥 Set 形（守恒值见证携带） ---------- *)

(* T 侧守恒的信息性面：桥往返后尺寸守恒值 ev_size e 作为 nat 见证
   信息性携带（消费盘上 cv_size_preservation_T L574；方程证明为
   sigT 第二分量证明参，提取擦除） *)
Theorem cv_size_preservation_T_set : forall e : Evidence,
  {n : nat & ev_size (cv_ev (cv_ev_inv e)) = n}.
Proof.
  intro e. exact (existT _ (ev_size e) (cv_size_preservation_T e)).
Defined.

(* D 侧守恒的信息性面：桥测度 dt_ev_size 守恒值作为见证（消费盘上
   cv_size_preservation_D L588） *)
Theorem cv_size_preservation_D_set : forall e : DTPT.DTPT.Evidence,
  {n : nat & dt_ev_size (cv_ev_inv (cv_ev e)) = n}.
Proof.
  intro e. exact (existT _ (dt_ev_size e) (cv_size_preservation_D e)).
Defined.

(* 层桥全序 Set 面：桥像上的层比较双向往复可判定（与盘上
   cv_lv_total_transport L640 同真值面；DTPT.Level 九格穷举直构） *)
Theorem cv_lv_total_set : forall a b : DTPT.DTPT.Level,
  {level_le (cv_lv a) (cv_lv b) = true} +
  {level_le (cv_lv b) (cv_lv a) = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.4 加分：层网说谎句每层复活 Set 面 ---------- *)

(* 盘上 layered_network_liar_each_layer（L368）的 Set 形重述：
   每层闭包下每层产出说谎句见证（逐层实例化 tarski_set 同款直构，
   见证 sigT 信息性携带——与旗舰同一升级点） *)
Theorem layered_network_liar_set : forall
    (truth : Level -> Dig -> bool)
    (diag_lv : Level -> (Dig -> bool) -> Dig),
  (forall lv, diag_closed Dig (diag_lv lv) (truth lv)) ->
  forall lv, {s : Dig & truth lv s = negb (truth lv s)}.
Proof.
  intros truth diag_lv Hcl lv.
  exact (existT _ (diag_lv lv (fun c => negb (truth lv c)))
                  (Hcl lv (fun c => negb (truth lv c)))).
Defined.

(* ========== §8 P3-B3 提取探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除；liar_diag_point 为
     Prop/False 面不提取，随行声明） ========== *)

Extraction "b3_audit_node_spec_set_ext.ml" audit_node_spec_set.
Extraction "b3_trLevel_geq_spec_set_ext.ml" trLevel_geq_spec_set.
Extraction "b3_trLevel_geq_mono_set_ext.ml" trLevel_geq_mono_set.
Extraction "b3_level_le_total_set_ext.ml" level_le_total_set.
Extraction "b3_liar_diag_ext.ml" liar_diag.
Extraction "b3_tarski_set_ext.ml" tarski_set.
Extraction "b3_cv_size_preservation_T_set_ext.ml" cv_size_preservation_T_set.
Extraction "b3_cv_size_preservation_D_set_ext.ml" cv_size_preservation_D_set.
Extraction "b3_cv_lv_total_set_ext.ml" cv_lv_total_set.
Extraction "b3_layered_network_liar_set_ext.ml" layered_network_liar_set.

(* ========== §9 P3-B5 追加：熵族剩余旗舰 Set 形桥接（2026-09-15） ==========
   消费盘面现役名 grep 实测表（DTPT_Entropy.v 2,708 行冻结终态，
   全部只读；棒 6a 在飞 Cyc/RotSpec/Lam 无交叠——DTPT_Lam.v 未
   Require 未消费，H_lam_anti_mono 禁消费在飞件照办）：
     collide_upper        L1743  forall l, collide l <= 1
     collide_lower        L1757  forall l, (0 < length l)%nat ->
                                   1 / qn (length l) <= collide l
     H_shannon_q_count_ub L664   forall l, H_devsum l <= H_adj l *
                                   (Z.of_nat (length l) # 1)
                                   （盘面现名实测＝原名未改，桥件名按
                                   B1 H_devsum 载体命名惯例取
                                   H_devsum_count_ub_set）
     H_max_q_anti         L1920  forall l p, maxfreq l <= maxfreq p ->
                                   H_max_q p <= H_max_q l
     H_max_q_nonneg       L1926  forall l, 0 <= H_max_q l
     H_min_q_nonneg       L1956  forall l, 0 <= H_min_q l
   主件二择一裁决：取 H_max_q_anti 反变单调面（QleT 前提经 §1
     QleT_to_Qle 抽取、结论经 qleT_intro 包装——双向桥同件串接，
     消费深度高于 collide_perm 直构形）；collide_perm 实测在册
     （L1778，EntFam2 归并区），按任务书二择一让位，如实记账。
   H_lam 面声明：H_lam_mono（L94）现役但不在本棒任务清单，让位
     后续棒；H_lam_anti_mono 在 DTPT_Lam.v 棒 6a 归并中，禁消费。
   惯例：全部 Defined（B1 坑④提取消费件惯例）；# 分母 positive
     实参形照盘面（B2 坑②）；非空卫哨 (0 < length l)%nat 照
     collide_lower 原面（B2 H_chain_set 同款）。 *)
(* ============================================================ *)

(* ---------- 9.1 保底件：collide 界双 Set 形 ---------- *)

(* collide 上界 Set 形：Σp² <= 1 全表无卫哨（消费 L1743 collide_upper） *)
Theorem collide_upper_set : forall l : list Q,
  QleT (collide l) 1.
Proof.
  intro l. apply qleT_intro. exact (collide_upper l).
Defined.

(* collide 下界 Set 形：1/n <= collide，非空信息性卫哨形（消费
   L1757 collide_lower；卫哨照原面 nat 侧 (0 < length l)%nat） *)
Theorem collide_lower_set : forall l : list Q,
  (0 < length l)%nat -> QleT (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply qleT_intro. exact (collide_lower l Hl).
Defined.

(* ---------- 9.2 旗舰：H_devsum 计数上界 Set 形 ---------- *)

(* 计数上界 QleT 面：H_devsum l <= H_adj l × 长度系数（消费
   L664 H_shannon_q_count_ub，盘面现名 grep 实测；桥件名按 B1
   H_devsum 载体命名惯例——对照 H_shannon_q_nonneg→
   H_devsum_nonneg_set 同款） *)
Theorem H_devsum_count_ub_set : forall l : list Q,
  QleT (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. apply qleT_intro. exact (H_shannon_q_count_ub l).
Defined.

(* ---------- 9.3 主件：H_max_q 反变单调 Set 形（二择一裁决件） ---------- *)

(* 反变单调：maxfreq l <= maxfreq p 导出 H_max_q p <= H_max_q l——
   前提 QleT 经 QleT_to_Qle 抽取为 Prop、结论经 qleT_intro 包装
   回 QleT（§1 双向桥串接；消费 L1920 H_max_q_anti） *)
Theorem H_max_q_anti_set : forall l p : list Q,
  QleT (maxfreq l) (maxfreq p) -> QleT (H_max_q p) (H_max_q l).
Proof.
  intros l p Hq. apply qleT_intro. apply H_max_q_anti.
  exact (QleT_to_Qle Hq).
Defined.

(* ---------- 9.4 加分：H_min_q/H_max_q 界面 Set 形各一件 ---------- *)

(* H_max_q 非负界面 Set 形（消费 L1926 H_max_q_nonneg） *)
Theorem H_max_q_nonneg_set : forall l : list Q,
  QleT 0 (H_max_q l).
Proof.
  intro l. apply qleT_intro. exact (H_max_q_nonneg l).
Defined.

(* H_min_q 非负界面 Set 形（消费 L1956 H_min_q_nonneg） *)
Theorem H_min_q_nonneg_set : forall l : list Q,
  QleT 0 (H_min_q l).
Proof.
  intro l. apply qleT_intro. exact (H_min_q_nonneg l).
Defined.

(* ========== §10 P3-B5 提取探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b5_collide_upper_set_ext.ml" collide_upper_set.
Extraction "b5_collide_lower_set_ext.ml" collide_lower_set.
Extraction "b5_H_devsum_count_ub_set_ext.ml" H_devsum_count_ub_set.
Extraction "b5_H_max_q_anti_set_ext.ml" H_max_q_anti_set.
Extraction "b5_H_max_q_nonneg_set_ext.ml" H_max_q_nonneg_set.
Extraction "b5_H_min_q_nonneg_set_ext.ml" H_min_q_nonneg_set.

End DTPT_Bridge.
