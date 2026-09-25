(* ============================================================
   DTPT_Bridge_Dep.v —— 恒等簇处置的 Set 形证书层
   【独立新建件】与 Bridge/Bridge_Dig/Bridge_Rot 分离——处置面
   独立成件。
   使命：DTPT_Rotation.v §S10（llm_rot_id 恒等簇 + 8 件弃用注记件
         逐件映射闭合段）的 Prop 证件升级为信息性 Type/Set 面。
   依赖（全部冻结只读）：DTPT / DTPT_Entropy / DTPT_Rotation
         （§S10 行号 L2427-L2676；vo 时序新鲜对表在案）。本文件不
         Require DTPT_Bridge / DTPT_Bridge_Dig / DTPT_Bridge_Rot /
         DTPT_Bridge_All / DTPT_Truth / DTPT_Extract（QleT/QeqT 族
         本地副本，B1 §1 / B4 §1 / B6 §1 惯例同构——依赖链 grep
         该族名零命中）。
   命名：桥接引理名沿桥接层惯例（rotc_supersedes_rot_id_set 等
         _set 后缀）；提取产物 b14_ 前缀；模块 DTPT_Bridge_Dep
         限名隔离（八件映射定理原名的 Set 形变体 = 原名去 map 加
         _set 或 dep_ 前缀，全链 grep 零撞名）。
   构造性注记：零承认、公理面为空；语句面全 Type/sigT（QleT/QeqT/
         sumbool/sigT 形）；全部 Defined（信息性入证书）。
   对标：已弃用定义的语义迁移证书（deprecated remap）惯例形。
   编译配方：Rocq 9.1 直调 rocq c -Q . "" DTPT_Bridge_Dep.v，
         cpu_guard 包装；nat 字面量全显式 %nat（Q_scope 全开传导）。
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

Module DTPT_Bridge_Dep.

(* ========== §1 本地信息性类型族（QleT/QeqT 惯例副本） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Arguments qleT_intro {x y} _.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

Arguments qeqT_intro {x y} _.

(* ========== §2 保底件：supersession 信息性双/三件 ==========
   盘面（DTPT_Rotation.v §S10，只读依存）：
   - L2445 rotc_supersedes_rot_id : forall n l, rot n l = l
     （firstn_skipn 直证，不依存弃用件 llm_rot_id）；
   - L2456 llm_rot_id_superseded : forall n l P, P l <-> P (rot n l)
     （P 面迁移零损失）。 *)

(* ① 依存 L2445：rot n l = l 的 list 级直等 sumbool 判定面。
   恒等处置已证结论 ⇒ 判定恒归 Left（这就是处置的实质：旧 rot 名下
   恒等重写依存无条件由真化基础模块承接）；left 构造子携 Prop 证明参
   ＝提取擦除惯例，无 Prop 消除入 Type。 *)
Theorem rotc_supersedes_rot_id_set : forall (n : nat) (l : list Q),
  {rot n l = l} + {rot n l <> l}.
Proof.
  intros n l.
  exact (left (rotc_supersedes_rot_id n l)).
Defined.

(* ② 依存 L2445：list 级直等的 sigT 见证面——重构列表信息性入证书
   （w := l，逐字即处置定理的等式右端），非退化旋转下 rot n l 的
   实际表值可提取。 *)
Theorem rotc_supersedes_rot_wit_set : forall (n : nat) (l : list Q),
  {w : list Q & rot n l = w}.
Proof.
  intros n l.
  exact (@existT (list Q) (fun w : list Q => rot n l = w) l
             (rotc_supersedes_rot_id n l)).
Defined.

(* ③ 依存 L2456 llm_rot_id_superseded（P 面 P↔P∘rot 迁移零损失）
   在熵实例 P := fun m => H_adj m == H_adj l 的 QeqT 面：迁移定理
   proj1（P l -> P (rot n l)）吃 Qeq_refl 一步——恒等重写在熵面
   零损失的信息性证书（P 面择熵面＝恒等簇依存主力，QeqT 面
   授权）。 *)
Theorem llm_rot_id_superseded_set : forall (n : nat) (l : list Q),
  QeqT (H_adj (rot n l)) (H_adj l).
Proof.
  intros n l.
  exact (qeqT_intro (proj1 (llm_rot_id_superseded n l
             (fun m : list Q => (H_adj m == H_adj l)%Q))
             (Qeq_refl (H_adj l)))).
Defined.

(* ========== §3 主件：八件映射逐件抽样 Set 面（3 件代表作：
   映射④ Hsup_mono / 映射⑦ H_adj_cross_phase_lb /
   映射⑧ u12_phase_side_always_zero 各一） ==========
   共同纪律：旧面性质经真化层重述，依存 §S10 映射定理 + 真化层
   现役件，禁重证。 *)

(* ④ 依存 L2559 deprecated_consumers_map_Hsup_mono（映射④：
   旧面 Hsup l n <= Hsup l (S n) 经 helper Hsup_oldface_const
   （L2502 旧 Hsup 面恒常值 = H_adj l，X1 结论定理化）+ 真化面
   Hsup_cyc_mono 同形在册的双覆盖）旧面分量的 QleT 信息性面。 *)
Theorem deprecated_Hsup_mono_set : forall (l : list Q) (n : nat),
  QleT (Hsup l n) (Hsup l (S n)).
Proof.
  intros l n.
  exact (qleT_intro (proj1 (deprecated_consumers_map_Hsup_mono l n))).
Defined.

(* ⑤ 依存 L2605 deprecated_consumers_map_H_adj_cross_phase_lb
   （映射⑦：旧跨相下界 H_adj (P0 l) <= H_adj (Pinf l s) 经
   Pinf_true_id + H_adj_P0_min（Entropy:428 现役）重推；真化面
   phcyc_min_perm + rotc_perm 覆盖任意 k 含 Pinf_c——同时是 §S7
   两处重定向的基础模块）三分量的 QleT Type 积面（旧面 + 任意 k 真旋转
   面 + Pinf_c 面，逐件照盘三分信息性无损迁移）。 *)
Theorem deprecated_H_adj_cross_phase_lb_set :
  forall (l : list Q) (s k : nat),
  (QleT (H_adj (P0 l)) (H_adj (Pinf l s)) *
   (QleT (H_adj (P0 l)) (H_adj (rotc k l)) *
   QleT (H_adj (P0 l)) (H_adj (Pinf_c l s))))%type.
Proof.
  intros l s k.
  exact (pair (qleT_intro
             (proj1 (deprecated_consumers_map_H_adj_cross_phase_lb l s k)))
             (pair (qleT_intro (proj1 (proj2
               (deprecated_consumers_map_H_adj_cross_phase_lb l s k))))
                   (qleT_intro (proj2 (proj2
               (deprecated_consumers_map_H_adj_cross_phase_lb l s k)))))).
Defined.

(* ⑥ 依存 L2625 deprecated_consumers_map_u12_phase_side_always_zero
   （映射⑧：旧判别器 phase_side l s = 0%nat 经定义展开 + Pinf_true_id
   + xq_Qle_bool_true + H_adj_P0_min 绕行弃用名重推；真化面
   phase_side_cyc_side_zero 在册）的信息性双证书面：判别值 sigT
   见证（v := 0，判别器输出信息性入证书）+ rotc 口径判别支路
   QleT（H_adj (P0 l) <= H_adj (rotc s l)，支路取 0 分支的信息性
   根由——依存映射⑦任意 k 面在 k := s 的实例）。 *)
Theorem deprecated_u12_phase_side_set : forall (l : list Q) (s : nat),
  ({v : nat & phase_side l s = v} *
   QleT (H_adj (P0 l)) (H_adj (rotc s l)))%type.
Proof.
  intros l s.
  exact (pair (@existT nat (fun v : nat => phase_side l s = v) 0%nat
             (proj1 (deprecated_consumers_map_u12_phase_side_always_zero l s)))
            (qleT_intro (proj1 (proj2
              (deprecated_consumers_map_H_adj_cross_phase_lb l s s))))).
Defined.

(* ========== §4 主件：处置完备性（八件映射联合覆盖证书） ==========
   deprecated_cluster_fully_covered：真化层对恒等簇全部依存场景的
   覆盖证书——八件映射逐件 Set 形分量联合配对（信息性合取）。
   覆盖核验（弃用件 → 本证书分量）：
   ① D5_Pinf_perm（L2515）→ 分量1+2：内容等式面强于置换面
     （Pinf l s = w 且 w = l ⇒ Permutation 经 rotc_supersedes… 基础模块
     平凡成立；Pinf_c 面同理由分量2 等式承接，Permutation l
     (Pinf_c l s) 由映射⑥第三分量在册）；
   ② llm_Pmid_zero（L2529）→ 分量3：内容面（Pmid l s 0 = l）+
     熵面 QeqT 双证书；
   ③ P0_absorbs_Pmid（L2547）→ 分量4：全 k 吸收见证面（sorted
     显式前提照录，§S8 结论在案）；
   ④ Hsup_mono（L2559）→ 分量5（= 主④）；
   ⑤ Hsup_bounded（L2572）→ 分量6+7：旧面 len#1·B·2 界（经
     H_adj_bound 同一基础模块绕行弃用名）+ 真化面 3·spread 界（诚实
     显式前提 SortedQ + l <> [] 随行）；
   ⑥ Pinf_eq_l（L2587）→ 分量1+2（旧名陈述由现役同形件零损失
     承接面 = Pinf l s = l；真化内容 Pinf_c l s = rotc (S s) l
     信息性携带具体旋转表）；
   ⑦ H_adj_cross_phase_lb（L2605）→ 分量8（= 主⑤ 三面全体）；
   ⑧ u12_phase_side_always_zero（L2625）→ 分量9（= 主⑥ 双证书）。
   8/8 全覆盖，零豁免。 *)

(* 逐件 helper（分量3 的独立可用形）：映射② 的内容+熵双证书。 *)
Theorem dep_map_llm_Pmid_zero_set : forall (l : list Q) (s : nat),
  ({w : list Q & Pmid l s 0%nat = w} *
   QeqT (H_adj (Pmid l s 0%nat)) (H_adj l))%type.
Proof.
  intros l s.
  exact (pair (@existT (list Q) (fun w : list Q => Pmid l s 0%nat = w) l
             (proj1 (deprecated_consumers_map_llm_Pmid_zero l s)))
            (qeqT_intro (proj2 (deprecated_consumers_map_llm_Pmid_zero l s)))).
Defined.

(* 联合覆盖定理（九分量 Type 积；显式前提照映射③⑤原样随行）。 *)
Theorem deprecated_cluster_fully_covered :
  forall (l : list Q) (s k n : nat) (B : Q),
  (forall x : Q, In x l -> Qabs x <= B) -> SortedQ l -> l <> [] ->
  ({w : list Q & Pinf l s = w} *
  {w : list Q & Pinf_c l s = w} *
  ({w : list Q & Pmid l s 0%nat = w} *
   QeqT (H_adj (Pmid l s 0%nat)) (H_adj l)) *
  {w : list Q & P0 (Pmid l s k) = w} *
  QleT (Hsup l n) (Hsup l (S n)) *
  QleT (Hsup l n) (((Z.of_nat (length l) # 1)%Q * B * 2)%Q) *
  QleT (Hsup_cyc l n) ((3 * (lastq l - hd 0 l))%Q) *
  (QleT (H_adj (P0 l)) (H_adj (Pinf l s)) *
  (QleT (H_adj (P0 l)) (H_adj (rotc k l)) *
  QleT (H_adj (P0 l)) (H_adj (Pinf_c l s)))) *
  ({v : nat & phase_side l s = v} *
   QleT (H_adj (P0 l)) (H_adj (rotc s l))))%type.
Proof.
  intros l s k n B HB HS Hne.
  exact ((existT _ l (proj1 (deprecated_consumers_map_Pinf_eq_l l s)),
  existT _ (rotc (S s) l)
    (proj1 (proj2 (deprecated_consumers_map_Pinf_eq_l l s))),
  dep_map_llm_Pmid_zero_set l s,
  existT _ (P0 l)
    (deprecated_consumers_map_P0_absorbs_Pmid l s k HS),
  deprecated_Hsup_mono_set l n,
  qleT_intro (proj1 (deprecated_consumers_map_Hsup_bounded
                       l n B HB HS Hne)),
  qleT_intro (proj2 (deprecated_consumers_map_Hsup_bounded
                       l n B HB HS Hne)),
  deprecated_H_adj_cross_phase_lb_set l s k,
  deprecated_u12_phase_side_set l s)%type).
Defined.

(* ========== §5 加分件：§S10 依存面重定向示范双件的 Set 面 ========== *)

(* ⑦ 依存 L2644 H_lam_anti_mono_real（§S7 L1615 主同陈述重定向
   变体：斜率非正装配处经 Pinf_true_id + H_adj_P0_min 真化层核验引用，
   弃用名零出现）的 QleT 面：λ-反单调性信息性证书。 *)
Theorem H_lam_anti_mono_real_set :
  forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> QleT (H_lam l s lam2) (H_lam l s lam1).
Proof.
  intros l s lam1 lam2 Hlam.
  exact (qleT_intro (H_lam_anti_mono_real l s lam1 lam2 Hlam)).
Defined.

(* ⑧ 依存 L2669 lam_opt_cross_phase_real（§S7 L1749 显式前提同陈述
   变体：跨相下界经真化层核验引用两步装配）的 QeqT 面：对齐选择器跨相
   恒取 1 的信息性证书。 *)
Theorem lam_opt_cross_phase_real_set : forall (l : list Q) (s : nat),
  QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) 1%Q.
Proof.
  intros l s.
  exact (eq_rect 1%Q (fun z => QeqT z 1%Q) (qeqT_intro (Qeq_refl 1%Q))
             (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
             (eq_sym (lam_opt_cross_phase_real l s))).
Defined.

(* ⑨ 同依存点的 sigT 见证面：选择器输出值信息性入证书
   （v := 1%Q）。Q 型 sigT 体的等式载体沿 B12 ⑧ 配方用 QeqT
   （Q 型 sigT 体裸 `=` 会被 Q_scope 侧解释吞成 Qeq，实测踩坑；
   QeqT 载体同时是双信息性层：见证值 + Qeq 证书）。 *)
Theorem lam_opt_cross_phase_wit_set : forall (l : list Q) (s : nat),
  {v : Q & QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) v}.
Proof.
  intros l s.
  exact (@existT Q (fun v : Q => QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) v) 1%Q
             (eq_rect (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) (fun z => QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) z)
              (qeqT_intro (Qeq_refl (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))) 1%Q
              (lam_opt_cross_phase_real l s))).
Defined.

(* ---------- §6 提取检验（b14_ 前缀逐件独立提取，
     Obj.magic 计数 0） ---------- *)

Set Extraction Output Directory ".".
Extraction "b14_rotc_supersedes_rot_id_set_ext.ml" rotc_supersedes_rot_id_set.
Extraction "b14_rotc_supersedes_rot_wit_set_ext.ml" rotc_supersedes_rot_wit_set.
Extraction "b14_llm_rot_id_superseded_set_ext.ml" llm_rot_id_superseded_set.
Extraction "b14_deprecated_Hsup_mono_set_ext.ml" deprecated_Hsup_mono_set.
Extraction "b14_deprecated_H_adj_cross_phase_lb_set_ext.ml" deprecated_H_adj_cross_phase_lb_set.
Extraction "b14_deprecated_u12_phase_side_set_ext.ml" deprecated_u12_phase_side_set.
Extraction "b14_dep_map_llm_Pmid_zero_set_ext.ml" dep_map_llm_Pmid_zero_set.
Extraction "b14_deprecated_cluster_fully_covered_ext.ml" deprecated_cluster_fully_covered.
Extraction "b14_H_lam_anti_mono_real_set_ext.ml" H_lam_anti_mono_real_set.
Extraction "b14_lam_opt_cross_phase_real_set_ext.ml" lam_opt_cross_phase_real_set.
Extraction "b14_lam_opt_cross_phase_wit_set_ext.ml" lam_opt_cross_phase_wit_set.

(* ---------- §7 公理闭包审计（本件 11 件，期望全 Closed） ---------- *)

Print Assumptions rotc_supersedes_rot_id_set.
Print Assumptions rotc_supersedes_rot_wit_set.
Print Assumptions llm_rot_id_superseded_set.
Print Assumptions deprecated_Hsup_mono_set.
Print Assumptions deprecated_H_adj_cross_phase_lb_set.
Print Assumptions deprecated_u12_phase_side_set.
Print Assumptions dep_map_llm_Pmid_zero_set.
Print Assumptions deprecated_cluster_fully_covered.
Print Assumptions H_lam_anti_mono_real_set.
Print Assumptions lam_opt_cross_phase_real_set.
Print Assumptions lam_opt_cross_phase_wit_set.

End DTPT_Bridge_Dep.
