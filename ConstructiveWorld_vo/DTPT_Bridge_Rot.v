(* ============================================================
   DTPT_Bridge_Rot.v — P3 桥接层第六棒（席 P3-B6，2026-09-15）
   续棒：P3-B7（2026-09-15）尾部追加 §8——Rotation §S8 新定理
         桥接（FRUIT-1 席 §S8 冻结新件的 Set 形面，12 件）
   续棒：P3-B12（2026-09-15）尾部追加 §9——Rotation §S9 新定理
         桥接（FRUIT-3 席 §S9 冻结新件 H_lam_pmid 三相互补熵族的
         Set 形面，9 件：端点双件 + 双旗舰 + 分离见证 sigT + 加分
         端点旧件桥/常值面 + vm_compute 锚双件）
   职责：旋转族旗舰 Set 形桥接——底座 DTPT_Rotation.v
         （棒 6b 改名件：原 DTPT_Cyc.v 全量 2,005 行，名不变只变
         限定路径；本棒消费其改名后形态）的 Prop 证件升级为
         信息性 Type/Set 面。
     §1 本地信息性类型族 QleT/QeqT（构造子携 Prop 证明参＝提取
        擦除惯例 B1 同款；以 Arguments 显式声明取代全局
        Set Implicit Arguments——B3 坑3 根除，B4 同款）
     §2 保底件：H_rotc_separates_set——非退化分离见证的
        sigT 信息性形（Prop exists 不可消除入 Type，按 B3
        tarski_set 同款直构包装：见证 [0;1;2] 转 1 格照盘照录）
     §3 旗舰件：rotc_class_sharp_ub_set——2·spread 锐化上界的
        QleT 面（盘上 rotc_class_sharp_ub 为 Qle ≤ 面，逐字对齐）
     §4 旗舰副件：rotc_spectrum_bound_set——谱有限性的 sigT
        信息性形（Prop 版二分为 cyc_nat_le_gt_cases 的 or 面，
        不可消除；此处换 stdlib 可计算二分 le_lt_dec 同款直构，
        两支见证与界逐字照盘）
     §5 主件：偏差判别器 phase_dev 可执行面三件——sumbool
        判定器 / 稳定面 QeqT 证书（消费盘上 phase_dev_stable）/
        sigT 偏差见证（消费盘上 phase_dev_witness 直构）
     §6 加分件：H_lam_cyc 端点双件 QeqT 面（消费盘上
        H_lam_cyc_lam1 / H_lam_cyc_lam0）
     §7 提取探针：逐件独立提取，验收 Obj.magic 计数 0
     §8 Rotation §S8 新定理桥接（P3-B7 追加段）：保底双件
        （H_adj_Pmid_seam_set QeqT 面 / Pmid_sorted_collapse_set
        sumbool 可执行表等判定面）+ 旗舰四件（精确坍缩 QeqT 面
        H_adj_Pmid_sorted_exact_set + 1·spread 精确值信息性携带
        spread 面 + 上界双件 ub2/gen QleT）+ 主件
        phase_classify_ne_PMid_set（死支定理可执行 sumbool 面
        {=PhP0}+{=PhPinf}）+ 加分端点三件（k0/klen QeqT +
        sorted 端点对 Type 积面）+ vm_compute 锚见证双件
   归并记录：§1–§7 = P3-B6 首棒（旋转族旗舰 Set 形桥接，稳定段
        零改）；§8 = P3-B7 追加（任务书「§2 = S8 新定理桥接」
        号段；沿文内既有 §2–§7 编号顺延为 §8，B6 段保持原样）；
        §9 = P3-B12 追加（任务书「§4 = §S9 三相互补桥接」号段；
        沿文内既有 §2–§8 编号顺延为 §9，B6/B7 段保持原样）；
        提取产物 b7_ / b12_ 前缀（B6 段 b6_ 不变）。
   依赖（全部冻结只读）：DTPT / DTPT_Entropy / DTPT_Rotation
         （棒 6b 改名件；其下游 ROTC/Entropy2 已退役，本文件
         与退役件零接触）。本文件不 Require DTPT_Bridge /
         DTPT_Bridge_Dig（并发席位文件，防竞态；QleT/QeqT 族
         本地镜像，惯例同构 B1 §1 / B4 §1 同款形——依赖链
         DTPT/DTPT_Entropy/DTPT_Rotation 全链 grep 该族名零
         命中，零撞名实测在案）。
   命名：桥件名沿任务书指定（H_rotc_separates_set 等 8 件，
         _set 后缀 B1-B5 惯例）；提取产物 b6_ 前缀；模块
         DTPT_Bridge_Rot 限名隔离。
   认证目标：零承认零公理；Error=0 Warning=0；Obj.magic=0 实测。
   纪律：温控协议 v2（coqc 全机 ≤3 先查后编）；禁碰一切既有 .v
         （本席独占本新建件）；禁 git；nat 字面量全显式 %nat；
         Q_scope 自开。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

Module DTPT_Bridge_Rot.

(* ========== §1 本地信息性类型族（QleT/QeqT 惯例镜像） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Arguments qleT_intro {x y} _.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

Arguments qeqT_intro {x y} _.

(* ========== §2 保底件：非退化分离见证的信息性形 ========== *)

(* 盘上 H_rotc_separates（DTPT_Rotation.v §S5 段）：Prop exists 形
   exists l n, H_adj (rotc n l) <> H_adj l，见证 [0;1;2] 转 1 格
   （H_adj 2 -> 3）。Prop exists 不可消除入 Type，故 sigT 信息性
   形按 B3 tarski_set 同款直构：见证值照盘照录，闭包证明同款
   （vm_compute 一发 + discriminate）。 <> 分量为 Prop 证明参，
   随提取擦除惯例留 __（B1 §G1 同款声明）。 *)
Theorem H_rotc_separates_set :
  {l : list Q & {n : nat & H_adj (rotc n l) <> H_adj l}}.
Proof.
  exists [0;1;2]. exists 1%nat.
  intro Hc. vm_compute in Hc. discriminate Hc.
Defined.

(* ========== §3 旗舰件：2·spread 锐化上界的 QleT 面 ========== *)

(* 盘上 rotc_class_sharp_ub（DTPT_Rotation.v §S6 段）为 Qle ≤ 面：
   forall l k, SortedQ l -> (H_adj (rotc k l) <= 2 * (lastq l - hd 0 l))%Q.
   桥面逐字对齐（任务书草式即此形），qleT_intro 一跳包装。 *)
Theorem rotc_class_sharp_ub_set : forall (l : list Q) (k : nat),
  SortedQ l -> QleT (H_adj (rotc k l)) (2 * (lastq l - hd 0 l)).
Proof.
  intros l k HS. apply qleT_intro.
  exact (rotc_class_sharp_ub l k HS).
Defined.

(* ========== §4 旗舰副件：谱有限性的 sigT 信息性形 ========== *)

(* 盘上 rotc_spectrum_bound（DTPT_Rotation.v §M5-1 段）：
   exists k', (k' <= length l - 1)%nat /\ rotc k l = rotc k' l
   （Leibniz 表等）。其证之二分为 Prop or 面（cyc_nat_le_gt_cases）
   不可消除入 Type；此处换 stdlib 可计算二分 le_lt_dec 同款直构：
   两支见证（k >= 表长取 k' = k；越界冻结回 k' = 0）与界逐字照盘，
   rotc_ge_len_id / rotc_0 消费面不变。 *)
Theorem rotc_spectrum_bound_set : forall (k : nat) (l : list Q),
  {k' : nat & (k' <= length l - 1)%nat /\ rotc k l = rotc k' l}.
Proof.
  intros k l. destruct (le_lt_dec (S k) (length l)) as [Hlt | Hge].
  - exists k. split.
    + lia.
    + reflexivity.
  - assert (Hge' : (length l <= k)%nat) by lia.
    exists 0%nat. split.
    + lia.
    + rewrite (rotc_ge_len_id k l Hge'). rewrite rotc_0. reflexivity.
Defined.

(* ========== §5 主件：偏差判别器 phase_dev 可执行面 ========== *)

(* 盘上 phase_dev（DTPT_Rotation.v §S6 段）本为 bool 值可执行定义：
   negb (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l)))。
   ① sumbool 判定器：bool 二分直构（分支目标被 destruct 抽象为
   计算形——B3 坑1 在案，处方 reflexivity 收口）。 *)
Theorem phase_dev_spec_set : forall (l : list Q) (k : nat),
  {phase_dev l k = true} + {phase_dev l k = false}.
Proof.
  intros l k. destruct (phase_dev l k).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* ② 稳定面 QeqT 证书：不偏差时两侧数值相等（消费盘上
   phase_dev_stable：phase_dev l k = false -> H_adj (rotc k l)
   == H_adj (P0 l)），qeqT_intro 一跳包装。 *)
Theorem phase_dev_stable_set : forall (l : list Q) (k : nat),
  phase_dev l k = false -> QeqT (H_adj (rotc k l)) (H_adj (P0 l)).
Proof.
  intros l k H. apply qeqT_intro. apply phase_dev_stable. exact H.
Defined.

(* ③ 偏差见证 sigT 信息性形：Prop exists（盘上 phase_dev_witness）
   不可消除，直构同款见证 [0;1;2] 转 1 格（vm_compute 闭式）。 *)
Theorem phase_dev_witness_set : {l : list Q & {k : nat & phase_dev l k = true}}.
Proof.
  exists [0;1;2]. exists 1%nat. vm_compute. reflexivity.
Defined.

(* ========== §6 加分件：H_lam_cyc 端点双件 QeqT 面 ========== *)

(* 盘上 H_lam_cyc_lam1 / H_lam_cyc_lam0（DTPT_Rotation.v §S7 段）：
   λ=1 全落排序相 P0、λ=0 全落 k 格真旋转相。QeqT 一跳包装。 *)
Theorem H_lam_cyc_lam1_set : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 1) (H_adj (P0 l)).
Proof.
  intros l k. apply qeqT_intro. apply H_lam_cyc_lam1.
Defined.

Theorem H_lam_cyc_lam0_set : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 0) (H_adj (rotc k l)).
Proof.
  intros l k. apply qeqT_intro. apply H_lam_cyc_lam0.
Defined.

(* ========== §7 提取探针（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Set Extraction Output Directory ".".
Extraction "b6_H_rotc_separates_set_ext.ml" H_rotc_separates_set.
Extraction "b6_rotc_class_sharp_ub_set_ext.ml" rotc_class_sharp_ub_set.
Extraction "b6_rotc_spectrum_bound_set_ext.ml" rotc_spectrum_bound_set.
Extraction "b6_phase_dev_spec_set_ext.ml" phase_dev_spec_set.
Extraction "b6_phase_dev_stable_set_ext.ml" phase_dev_stable_set.
Extraction "b6_phase_dev_witness_set_ext.ml" phase_dev_witness_set.
Extraction "b6_H_lam_cyc_lam1_set_ext.ml" H_lam_cyc_lam1_set.
Extraction "b6_H_lam_cyc_lam0_set_ext.ml" H_lam_cyc_lam0_set.

(* ========== 终验：公理闭包审计 ========== *)

Print Assumptions H_rotc_separates_set.
Print Assumptions rotc_class_sharp_ub_set.
Print Assumptions rotc_spectrum_bound_set.
Print Assumptions phase_dev_spec_set.
Print Assumptions phase_dev_stable_set.
Print Assumptions phase_dev_witness_set.
Print Assumptions H_lam_cyc_lam1_set.
Print Assumptions H_lam_cyc_lam0_set.

(* ========== §8 Rotation §S8 新定理桥接（P3-B7 追加段） ========== *)

(* 消费对象＝DTPT_Rotation.v §S8 冻结新件（FRUIT-1 席产，只读；
   行号实测：.v 2026-09-15 06:12:51 / .vo 2026-09-15 06:28:58 新于
   .v）：L1994 H_adj_Pmid_seam、L2019 H_adj_Pmid_decomp、L2039
   sorted_abs_le_spread、L2056 Pmid_sorted_collapse、L2068
   H_adj_Pmid_sorted_exact、L2079 H_adj_Pmid_sorted_ub2、L2099
   H_adj_Pmid_ub_gen、L2141/L2150/L2158 端点三件、L2175
   phase_classify_ne_PMid、L2193/L2197 vm_compute 锚双件。
   H_devsum/垫片/弃用注记零消费零触碰（弃用件 Pinf_eq_l 沿 FRUIT-1
   同款绕行，仅经 Pinf_true_id 面）。 *)

(* ---------- §8.1 保底件：中相分解 Set 面 ---------- *)

(* ① 消费 L1994 H_adj_Pmid_seam（Qeq == 面，seam 定向 hd 在前）：
   qeqT_intro 一跳包装，QeqT 面逐字对齐，接缝项保持盘面原定向。 *)
Theorem H_adj_Pmid_seam_set : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  QeqT (H_adj (Pmid l s k))
       (H_adj (firstn k (P0 l)) + H_adj (skipn k l)
        + Qabs (hd 0 (skipn k l) - lastq (firstn k (P0 l)))).
Proof.
  intros l s k Hk Hlt. apply qeqT_intro.
  apply H_adj_Pmid_seam; [ exact Hk | exact Hlt ].
Defined.

(* ② 消费 L2056 Pmid_sorted_collapse（list 级 Leibniz 直等面）：
   盘上结论为 Prop eq，信息性化取 sumbool 可执行表等判定面——
   本地可计算判定底 list_qeqb（Qeq 逐点口径，Module 内限定名，
   全链 grep 零撞名实测）。soundness：true 支由盘面坍缩件直供；
   false 支经 list_qeqb_refl（list_qeqb a a = true）与坍缩件矛盾
   排除——无 Prop 消除入 Type，无硬凑。SortedQ 前提为 Prop 整参
   （提取擦除惯例，B6 rotc_class_sharp_ub_set 同款诚实声明）。 *)
Fixpoint list_qeqb (a b : list Q) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if Qeq_bool x y then list_qeqb a' b' else false
  | _, _ => false
  end.

Lemma list_qeqb_refl : forall a : list Q, list_qeqb a a = true.
Proof.
  induction a as [| x a IH]; simpl.
  - reflexivity.
  - rewrite Qeq_bool_refl. exact IH.
Defined.

Theorem Pmid_sorted_collapse_set : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> {Pmid l s k = l} + {Pmid l s k <> l}.
Proof.
  intros l s k HS.
  destruct (list_qeqb (Pmid l s k) l) eqn:E.
  - left. exact (Pmid_sorted_collapse l s k HS).
  - right. intro Heq. rewrite Heq in E.
    rewrite list_qeqb_refl in E. discriminate E.
Defined.

(* ---------- §8.2 旗舰件：精确坍缩 Set 面 + 上界双件 ---------- *)

(* ③ 消费 L2068 H_adj_Pmid_sorted_exact（sorted 卫哨 Qeq 面）：
   QeqT 证书面——sorted 下中相熵 == H_adj l，QeqT 载体即把
   「1·spread 精确值」信息性携带为可提取证书（非 mere ≤ 界）。 *)
Theorem H_adj_Pmid_sorted_exact_set : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QeqT (H_adj (Pmid l s k)) (H_adj l).
Proof.
  intros l s k HS. apply qeqT_intro.
  apply H_adj_Pmid_sorted_exact. exact HS.
Defined.

(* ④ 1·spread 精确值的信息性携带面：sorted 下中相熵逐字等于
   lastq l - hd 0 l（精确面 + DTPT_Entropy xq_telescope 一跳，
   xq_telescope : forall l, SortedQ l -> H_adj l == lastq l - hd 0 l，
   DTPT_Entropy.v L362 实测）——见证值显式出现于桥面陈述。 *)
Theorem H_adj_Pmid_sorted_spread_set : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QeqT (H_adj (Pmid l s k)) (lastq l - hd 0 l).
Proof.
  intros l s k HS. apply qeqT_intro.
  rewrite <- (xq_telescope l HS).
  apply H_adj_Pmid_sorted_exact. exact HS.
Defined.

(* ⑤ 消费 L2079 H_adj_Pmid_sorted_ub2（2·spread 上界，P0 面
   spread 口径）：qleT_intro 一跳包装，QleT 面逐字对齐。 *)
Theorem H_adj_Pmid_sorted_ub2_set : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QleT (H_adj (Pmid l s k)) (2 * (lastq (P0 l) - hd 0 (P0 l))).
Proof.
  intros l s k HS. apply qleT_intro.
  apply H_adj_Pmid_sorted_ub2. exact HS.
Defined.

(* ⑥ 消费 L2099 H_adj_Pmid_ub_gen（无排序诚实界，尾段如实分项——
   FRUIT-1 诚实障碍声明随行：无排序时尾段 H_adj (skipn k l) 不可
   吞入 2·spread，见证 [0;1;0;1] k=1 在案）：QleT 面逐字对齐。 *)
Theorem H_adj_Pmid_ub_gen_set : forall (l : list Q) (s : nat) (k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  QleT (H_adj (Pmid l s k))
       (2 * (lastq (P0 l) - hd 0 (P0 l)) + H_adj (skipn k l)).
Proof.
  intros l s k Hk Hlt. apply qleT_intro.
  apply H_adj_Pmid_ub_gen; [ exact Hk | exact Hlt ].
Defined.

(* ---------- §8.3 主件：死支定理 Set 面 ---------- *)

(* ⑦ 消费 L2175 phase_classify_ne_PMid + DTPT.v L2846/L2848 实测
   （PhaseTag : Type := PhP0 | PhMid | PhPinf；phase_classify 为
   Qeq_bool 双测试判定树：第一测试 h0=hm → PhP0，第二测试 hm=hi →
   PhPinf，否则 PhMid）。盘上死支定理（PhMid 构造子不可达）的
   可执行判定面＝sumbool {=PhP0} + {=PhPinf}：判定器沿
   phase_classify 自身决策树分派，PhMid 支按盘面同款配方排除
   （Pmid l s 0 ≡ Pinf l s 定义性 → Hid reflexivity →
   Qeq_bool_refl → discriminate）。提取面为可执行相判定器，
   sumbool 两支 Prop 证书参擦除（B6 phase_dev_spec_set 同级件）。 *)
Theorem phase_classify_ne_PMid_set : forall (l : list Q) (s : nat),
  {phase_classify l s = PhP0} + {phase_classify l s = PhPinf}.
Proof.
  intros l s. unfold phase_classify. cbv zeta.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0%nat))) eqn:E1.
  - left. reflexivity.
  - destruct (Qeq_bool (H_adj (Pmid l s 0%nat)) (H_adj (Pinf l s)))
      eqn:E2.
    + right. reflexivity.
    + assert (Hid : H_adj (Pmid l s 0%nat) == H_adj (Pinf l s))
        by reflexivity.
      rewrite Hid in E2. rewrite Qeq_bool_refl in E2. discriminate E2.
Defined.

(* ---------- §8.4 加分件：端点三件 Set 面（对账 U2 端点族） ---------- *)

(* ⑧ 消费 L2141 H_adj_Pmid_k0（k=0 端点＝P∞ 相，原始全体）：
   QeqT 一跳包装。 *)
Theorem H_adj_Pmid_k0_set : forall (l : list Q) (s : nat),
  QeqT (H_adj (Pmid l s 0%nat)) (H_adj l).
Proof.
  intros l s. apply qeqT_intro. apply H_adj_Pmid_k0.
Defined.

(* ⑨ 消费 L2150 H_adj_Pmid_klen（k=length 端点＝P0 相，排序全体）：
   QeqT 一跳包装。 *)
Theorem H_adj_Pmid_klen_set : forall (l : list Q) (s : nat),
  QeqT (H_adj (Pmid l s (length l))) (H_adj (P0 l)).
Proof.
  intros l s. apply qeqT_intro. apply H_adj_Pmid_klen.
Defined.

(* ⑩ 消费 L2158 H_adj_Pmid_endpoints_sorted（sorted 下两端点熵皆
   == lastq l - hd 0 l）：Set 面取 QeqT 双证书的 Type 积（prod）——
   分量经盘面 conj 的 proj1/proj2 取得（仅 Prop→Prop 投影，无
   Prop 消除入 Type），两证书信息性并存。 *)
Theorem H_adj_Pmid_endpoints_sorted_set : forall (l : list Q) (s : nat),
  SortedQ l ->
  QeqT (H_adj (Pmid l s 0%nat)) (lastq l - hd 0 l)
  * QeqT (H_adj (Pmid l s (length l))) (lastq l - hd 0 l).
Proof.
  intros l s HS. split.
  - apply qeqT_intro. exact (proj1 (H_adj_Pmid_endpoints_sorted l s HS)).
  - apply qeqT_intro. exact (proj2 (H_adj_Pmid_endpoints_sorted l s HS)).
Defined.

(* ---------- §8.5 vm_compute 锚见证件（G4 实测面） ---------- *)

(* ⑪ 消费 L2193 Pmid_sorted_collapse_wit_012：见证列 [0;1;2]
   （sorted）上中相整体坍缩的 sigT 信息性形——坍缩结果表
   [0;1;2] 作为见证信息性携带，vm_compute 一步闭项照盘。 *)
Theorem Pmid_collapse_wit_set : {l : list Q & Pmid [0; 1; 2] 0%nat 1%nat = l}.
Proof.
  exists [0; 1; 2]. vm_compute. reflexivity.
Defined.

(* ⑫ 消费 L2197 H_adj_Pmid_decomp_wit_012：接缝分解恒等式数值锚
   的 sigT 信息性形——熵见证值（盘面 RHS 逐字照录）经 QeqT 载体
   信息性携带，vm_compute 一步闭项照盘。 *)
Theorem H_adj_Pmid_wit_set :
  {v : Q & QeqT (H_adj (Pmid [0; 1; 2] 0%nat 1%nat)) v}.
Proof.
  exists (H_adj [0] + Qabs (lastq [0] - hd 0 [1; 2]) + H_adj [1; 2]).
  apply qeqT_intro. vm_compute. reflexivity.
Defined.

(* ========== §8.6 提取探针（B7 追加；b7_ 前缀，U12 配方：
     逐件独立提取，验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Set Extraction Output Directory ".".
Extraction "b7_H_adj_Pmid_seam_set_ext.ml" H_adj_Pmid_seam_set.
Extraction "b7_Pmid_sorted_collapse_set_ext.ml" Pmid_sorted_collapse_set.
Extraction "b7_H_adj_Pmid_sorted_exact_set_ext.ml" H_adj_Pmid_sorted_exact_set.
Extraction "b7_H_adj_Pmid_sorted_spread_set_ext.ml" H_adj_Pmid_sorted_spread_set.
Extraction "b7_H_adj_Pmid_sorted_ub2_set_ext.ml" H_adj_Pmid_sorted_ub2_set.
Extraction "b7_H_adj_Pmid_ub_gen_set_ext.ml" H_adj_Pmid_ub_gen_set.
Extraction "b7_phase_classify_ne_PMid_set_ext.ml" phase_classify_ne_PMid_set.
Extraction "b7_H_adj_Pmid_k0_set_ext.ml" H_adj_Pmid_k0_set.
Extraction "b7_H_adj_Pmid_klen_set_ext.ml" H_adj_Pmid_klen_set.
Extraction "b7_H_adj_Pmid_endpoints_sorted_set_ext.ml" H_adj_Pmid_endpoints_sorted_set.
Extraction "b7_Pmid_collapse_wit_set_ext.ml" Pmid_collapse_wit_set.
Extraction "b7_H_adj_Pmid_wit_set_ext.ml" H_adj_Pmid_wit_set.

(* ========== §8.7 终验：公理闭包审计（B7 追加 12 件，
     期望全 Closed） ========== *)

Print Assumptions H_adj_Pmid_seam_set.
Print Assumptions Pmid_sorted_collapse_set.
Print Assumptions H_adj_Pmid_sorted_exact_set.
Print Assumptions H_adj_Pmid_sorted_spread_set.
Print Assumptions H_adj_Pmid_sorted_ub2_set.
Print Assumptions H_adj_Pmid_ub_gen_set.
Print Assumptions phase_classify_ne_PMid_set.
Print Assumptions H_adj_Pmid_k0_set.
Print Assumptions H_adj_Pmid_klen_set.
Print Assumptions H_adj_Pmid_endpoints_sorted_set.
Print Assumptions Pmid_collapse_wit_set.
Print Assumptions H_adj_Pmid_wit_set.

(* ========== §9 Rotation §S9 新定理桥接（P3-B12 追加段） ========== *)

(* 消费对象＝DTPT_Rotation.v §S9 冻结新件（FRUIT-3 席产，只读；
   行号实测：.v 2026-09-15 07:38:09 / .vo 2026-09-15 07:40:58 新于
   .v）：L2244 H_lam_pmid（Definition）、L2248 H_lam_pmid_lam1、
   L2257 H_lam_pmid_lam0、L2271 H_lam_pmid_diff、L2298
   H_lam_pmid_sorted_consistency、L2333 H_lam_pmid_k0_oldface、
   L2343 H_lam_pmid_klen_const、L2357 H_lam_pmid_H_lam_separates、
   L2368 H_lam_pmid_wit_201、L2372 H_lam_pmid_wit_201_ends。
   H_devsum/垫片/弃用注记零消费零触碰（弃用件 Pinf_eq_l 沿 FRUIT-3
   同款绕行，仅经 Pinf_true_id 面，DTPT_Rotation.v L417 实测）。 *)

(* ---------- §9.1 保底件：端点双件 QeqT 面 ---------- *)

(* ① 消费 L2248 H_lam_pmid_lam1（λ=1 端点，s、k 解耦）：qeqT_intro
   一跳包装，QeqT 面逐字对齐（B6 §6 H_lam_cyc_lam1_set 同款）。 *)
Theorem H_lam_pmid_lam1_set : forall (l : list Q) (s : nat) (k : nat),
  QeqT (H_lam_pmid l s k 1) (H_adj (P0 l)).
Proof.
  intros l s k. apply qeqT_intro. apply H_lam_pmid_lam1.
Defined.

(* ② 消费 L2257 H_lam_pmid_lam0（λ=0 端点＝真中相 Pmid）：QeqT
   一跳包装。 *)
Theorem H_lam_pmid_lam0_set : forall (l : list Q) (s : nat) (k : nat),
  QeqT (H_lam_pmid l s k 0) (H_adj (Pmid l s k)).
Proof.
  intros l s k. apply qeqT_intro. apply H_lam_pmid_lam0.
Defined.

(* ---------- §9.2 旗舰件：仿射差分 + 排序一致性 QeqT 面 ---------- *)

(* ③ 消费 L2271 H_lam_pmid_diff（仿射差分恒等式：插值两端之差 =
   (λ1-λ2)·(排序相熵 - 中相熵)，§S7 泛形 lam_affine_diff_sub 的
   真中相实形）：Prop 消费 + QeqT 包装——差分恒等式升为信息性
   证书，右端全计算面（B7 §8.2 件③④同款配方）。 *)
Theorem H_lam_pmid_diff_set : forall (l : list Q) (s : nat) (k : nat)
    (lam1 lam2 : Q),
  QeqT (H_lam_pmid l s k lam1 - H_lam_pmid l s k lam2)
       ((lam1 - lam2) * (H_adj (P0 l) - H_adj (Pmid l s k))).
Proof.
  intros l s k lam1 lam2. apply qeqT_intro. apply H_lam_pmid_diff.
Defined.

(* ④ 消费 L2298 H_lam_pmid_sorted_consistency（排序一致性全 λ 面：
   SortedQ l -> H_lam_pmid l s k lam == H_lam l s lam）——三相互补
   熵与经典序列熵相容性的 QeqT 证书面：sorted 卫哨下第三块 λ-插值
   与 H_lam 逐点重合，相容性面定理化后升为可提取信息性载体。
   SortedQ 前提为 Prop 整参（提取擦除惯例，B6
   rotc_class_sharp_ub_set 同款诚实声明）。 *)
Theorem H_lam_pmid_sorted_consistency_set :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  SortedQ l -> QeqT (H_lam_pmid l s k lam) (H_lam l s lam).
Proof.
  intros l s k lam HS. apply qeqT_intro.
  apply H_lam_pmid_sorted_consistency. exact HS.
Defined.

(* ---------- §9.3 主件：分离见证 sigT 信息性形 ---------- *)

(* ⑤ 消费 L2357 H_lam_pmid_H_lam_separates（Prop exists 形：
   exists l k s lam, H_lam_pmid l s k lam <> H_lam l s lam）。Prop
   exists 不可消除入 Type，sigT 信息性形按 B3 tarski_set 同款直构
   （B6 §2 H_rotc_separates_set 同款）：见证 [2;0;1]（未排序）、
   k=1、s=0、lam=1/2 照盘照录，闭包证明同盘配方（Pinf_true_id
   重写 + vm_compute + discriminate）。 <> 分量为 Prop 证明参，
   随提取擦除惯例留 __（B1 §G1 同款声明）。 *)
Theorem H_lam_pmid_separates_set :
  {l : list Q & {k : nat & {s : nat &
    {lam : Q & H_lam_pmid l s k lam <> H_lam l s lam}}}}.
Proof.
  exists [2; 0; 1]. exists 1%nat. exists 0%nat. exists (1#2)%Q.
  intro Hc. unfold H_lam_pmid, H_lam in Hc.
  rewrite (Pinf_true_id [2; 0; 1] 0%nat) in Hc.
  vm_compute in Hc. discriminate Hc.
Defined.

(* ---------- §9.4 加分件：端点旧件桥/常值面 + vm_compute 锚双件 ---------- *)

(* ⑥ 消费 L2333 H_lam_pmid_k0_oldface（k=0 端点与旧件 H_lam 逐点
   重合，迁移零丢旧信息）：QeqT 一跳包装。 *)
Theorem H_lam_pmid_k0_oldface_set : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_pmid l s 0%nat lam) (H_lam l s lam).
Proof.
  intros l s lam. apply qeqT_intro. apply H_lam_pmid_k0_oldface.
Defined.

(* ⑦ 消费 L2343 H_lam_pmid_klen_const（k=length 两端重合，λ 失效
   常值面）：QeqT 一跳包装。 *)
Theorem H_lam_pmid_klen_const_set : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_pmid l s (length l) lam) (H_adj (P0 l)).
Proof.
  intros l s lam. apply qeqT_intro. apply H_lam_pmid_klen_const.
Defined.

(* ⑧ 消费 L2368 H_lam_pmid_wit_201：数值锚的 sigT 信息性形——
   见证列 [2;0;1] 上插值值（盘面 RHS (3#2)%Q 逐字）经 QeqT 载体
   信息性携带，vm_compute 一步闭项照盘（B7 §8.5 件⑫同款）。 *)
Theorem H_lam_pmid_wit_201_set :
  {v : Q & QeqT (H_lam_pmid [2; 0; 1] 0%nat 1%nat (1#2)%Q) v}.
Proof.
  exists (3#2)%Q. apply qeqT_intro. vm_compute. reflexivity.
Defined.

(* ⑨ 消费 L2372 H_lam_pmid_wit_201_ends（分离根因双值面：排序相端
   2、中相端 1）：sigT over Q*Q——双端见证值信息性携带（fst/snd
   显式入证书），两分量各经 QeqT 载体 vm_compute 一步闭项（B7
   §8.4 件⑩ Prop 合取→Type 证书配方 × §8.5 锚配方的复合）。 *)
Theorem H_lam_pmid_ends_wit_set :
  {p : Q * Q &
    (QeqT (H_adj (P0 [2; 0; 1])) (fst p)
     * QeqT (H_adj (Pmid [2; 0; 1] 0%nat 1%nat)) (snd p))%type}.
Proof.
  exists (2%Q, 1%Q). split.
  - apply qeqT_intro. vm_compute. reflexivity.
  - apply qeqT_intro. vm_compute. reflexivity.
Defined.

(* ---------- §9.5 提取探针（B12 追加；b12_ 前缀，U12 配方：
     逐件独立提取，验收指标＝Obj.magic 计数 0，验后产物清除） ---------- *)

Set Extraction Output Directory ".".
Extraction "b12_H_lam_pmid_lam1_set_ext.ml" H_lam_pmid_lam1_set.
Extraction "b12_H_lam_pmid_lam0_set_ext.ml" H_lam_pmid_lam0_set.
Extraction "b12_H_lam_pmid_diff_set_ext.ml" H_lam_pmid_diff_set.
Extraction "b12_H_lam_pmid_sorted_consistency_set_ext.ml" H_lam_pmid_sorted_consistency_set.
Extraction "b12_H_lam_pmid_separates_set_ext.ml" H_lam_pmid_separates_set.
Extraction "b12_H_lam_pmid_k0_oldface_set_ext.ml" H_lam_pmid_k0_oldface_set.
Extraction "b12_H_lam_pmid_klen_const_set_ext.ml" H_lam_pmid_klen_const_set.
Extraction "b12_H_lam_pmid_wit_201_set_ext.ml" H_lam_pmid_wit_201_set.
Extraction "b12_H_lam_pmid_ends_wit_set_ext.ml" H_lam_pmid_ends_wit_set.

(* ---------- §9.6 终验：公理闭包审计（B12 追加 9 件，
     期望全 Closed） ---------- *)

Print Assumptions H_lam_pmid_lam1_set.
Print Assumptions H_lam_pmid_lam0_set.
Print Assumptions H_lam_pmid_diff_set.
Print Assumptions H_lam_pmid_sorted_consistency_set.
Print Assumptions H_lam_pmid_separates_set.
Print Assumptions H_lam_pmid_k0_oldface_set.
Print Assumptions H_lam_pmid_klen_const_set.
Print Assumptions H_lam_pmid_wit_201_set.
Print Assumptions H_lam_pmid_ends_wit_set.

End DTPT_Bridge_Rot.
