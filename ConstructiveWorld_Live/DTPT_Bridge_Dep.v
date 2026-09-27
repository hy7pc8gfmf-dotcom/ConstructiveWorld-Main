(* ==========================================================================)
   DTPT_Bridge_Dep —— 恒等簇处置的 Set 形证书层；同域语句面
   使命：本件形式化恒等簇处置的 Set 形证书层。
   本件并载：八簇使用面抽验（桥接件重述式 re-Port，覆盖 QleT/QeqT/sumbool/sigT 四形）、八件闭式数值锚、全部使用件逐件 Extract。
   依赖：QArith.QArith, QArith.Qabs, List, Arith, Lia, Extraction, DTPT, DTPT_Entropy
     DTPT_Rotation, Bool, ZArith, Permutation, DTPT_DigTheory, DTPT_Extract, DTPT_Truth, DTPT_Bridge,
     DTPT_Bridge_Dig, DTPT_Bridge_Rot。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
   恒等重写依存无条件由真化基础模块承担）；left 构造子携 Prop 证明参
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
     平凡成立；Pinf_c 面同理由分量2 等式承担，Permutation l
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
     承担面 = Pinf l s = l；真化内容 Pinf_c l s = rotc (S s) l
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
   （v := 1%Q）。Q 型 sigT 体的等式载体沿同族桥接件配方用 QeqT
   （Q 型 sigT 体裸 `=` 会被 Q_scope 侧解释吞成 Qeq，实测在案；
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

(* ============================ §8 八簇使用面抽验（桥接件重述式 re-Port，覆盖 QleT/QeqT/sumbool/sigT 四形）、八件闭式数值锚、全部使用件逐件 Extract ============================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Bool ZArith.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Require DTPT_DigTheory.
Require DTPT_Extract.
Require DTPT_Truth.
Require DTPT_Bridge.
Require DTPT_Bridge_Dig.
Require DTPT_Bridge_Rot.

(* 计算件名面 Import：与三桥各文件生效环境同序（相对次序保持，
   名解析逐簇同构）；DTPT_Truth 置末＝B3 §7 生效遮蔽序的复刻。 *)
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Extract.DTPT_Extract.
Import DTPT_Truth.DTPT_Truth.

(* ========== §B0 桥接件缩记（纯 Notation 缩写，零语义新增） ========== *)

Notation QleTB := DTPT_Bridge.DTPT_Bridge.QleT.
Notation QeqTB := DTPT_Bridge.DTPT_Bridge.QeqT.
Notation AndB := DTPT_Bridge.DTPT_Bridge.And.
Notation dQleTB := DTPT_Bridge_Dig.DTPT_Bridge_Dig.dQleT.
Notation dQeqTB := DTPT_Bridge_Dig.DTPT_Bridge_Dig.dQeqT.
Notation QleTR := DTPT_Bridge_Rot.DTPT_Bridge_Rot.QleT.
Notation QeqTR := DTPT_Bridge_Rot.DTPT_Bridge_Rot.QeqT.

(* ========== §B 使用面抽验（八簇 × 每簇 2–3 件，全部直接别名
     使用＝重述式 re-Port，每件 <=5 行，零重证） ==========
   簇 × 形覆盖矩阵：
     簇  | 桥接件(形)                                   | 基础件
     B1  | C_sorted_min_adj_set(QleT)                 | DTPT L729
         | qeqT_intro/QeqT_to_Qeq(QeqT 双向桥)        | 基建 §1
     B2  | H_freq_perm_set(QeqT)                      | Entropy L1239
         | H_chain_set(QleT×And 积)                   | Entropy L1757/1794/1849
         | H_devsum_zero_iff_sorted_set(sumbool)      | Entropy L2484
     B3  | tarski_set(sigT)                           | Truth L261
         | audit_node_spec_set(sumbool)               | Truth L700
     B4  | is_num_spec(sumbool)                       | DigTheory L329
         | u12_gate_chain_QleT(dQleT×prod)            | Extract L139
         | dig_Q_roundtrip_set(dQeqT)                 | DigTheory L319
     B5  | H_devsum_count_ub_set(QleT)                | Entropy L664
         | H_max_q_anti_set(QleT 反变)                | Entropy L1920
     B6  | phase_dev_stable_set(QeqT)                 | Rotation S6
         | phase_dev_spec_set(sumbool)                | Rotation S6
         | H_rotc_separates_set(sigT)                 | Rotation S5
     B7  | H_adj_Pmid_seam_set(QeqT)                  | Rotation L1994
         | H_adj_Pmid_sorted_ub2_set(QleT)            | Rotation L2079
         | Pmid_collapse_wit_set(sigT)                | Rotation L2193
     B8  | H_freq_dpi_set(QleT)                       | Entropy L1439
         | H_min_q_anti_set(QleT 反变)                | Entropy L1637/1920
         | H_freq_eq0_all_same_set(sumbool)           | Entropy L1291/1268
   四形覆盖：QleT＝B1/B2/B5/B7/B8；QeqT＝B1/B2/B6/B7；
     sumbool＝B2/B3/B4/B6/B8；sigT＝B3/B6/B7（另 dQleT/dQeqT＝B4）。
   ============================================================ *)

(* ---------- 簇 B1（DTPT_Bridge §1/§3，） ---------- *)

Definition all_B1_C_sorted_min_adj_set :
  forall l : list Q, QleTB (H_adj (P0 l)) (H_adj l) :=
  DTPT_Bridge.DTPT_Bridge.C_sorted_min_adj_set.

Definition all_B1_QeqT_of_Qeq : forall x y : Q, (x == y)%Q ->
  QeqTB x y := @DTPT_Bridge.DTPT_Bridge.qeqT_intro.

Definition all_B1_QeqT_to_Qeq : forall x y : Q,
  QeqTB x y -> (x == y)%Q := @DTPT_Bridge.DTPT_Bridge.QeqT_to_Qeq.

(* ---------- 簇 B2（DTPT_Bridge §5，） ---------- *)

Definition all_B2_H_freq_perm_set : forall l p : list Q, Permutation l p ->
  QeqTB (H_freq l) (H_freq p) := DTPT_Bridge.DTPT_Bridge.H_freq_perm_set.

Definition all_B2_H_chain_set : forall l : list Q, (0 < length l)%nat ->
  AndB (QleTB (1 / qn (length l)) (collide l))
       (AndB (QleTB (collide l) (maxfreq l)) (QleTB (maxfreq l) 1)) :=
  DTPT_Bridge.DTPT_Bridge.H_chain_set.

Definition all_B2_H_devsum_zero_iff_sorted_set (l : list Q) :
  {SortedQ l} + {~ SortedQ l} :=
  DTPT_Bridge.DTPT_Bridge.H_devsum_zero_iff_sorted_set l.

(* ---------- 簇 B3（DTPT_Bridge §7，） ---------- *)

Definition all_B3_tarski_set : forall (truth : Dig -> bool)
    (diag : (Dig -> bool) -> Dig),
  diag_closed Dig diag truth -> {s : Dig & truth s = negb (truth s)} :=
  DTPT_Bridge.DTPT_Bridge.tarski_set.

Definition all_B3_audit_node_spec_set : forall t : TrNode,
  {audit_node t = true} + {audit_node t = false} :=
  DTPT_Bridge.DTPT_Bridge.audit_node_spec_set.

(* ---------- 簇 B4（DTPT_Bridge_Dig，） ---------- *)

Definition all_B4_is_num_spec : forall d : Dig,
  {is_num d = true} + {is_num d = false} :=
  DTPT_Bridge_Dig.DTPT_Bridge_Dig.is_num_spec.

Definition all_B4_u12_gate_chain_QleT : forall (l : list Q) (t : Q),
  u12_gate_chain l t = true ->
  prod (dQleTB (H_adj l) t) (dQleTB (H_adj (P0 l)) (H_adj (Pinf l 0%nat))) :=
  DTPT_Bridge_Dig.DTPT_Bridge_Dig.u12_gate_chain_QleT.

Definition all_B4_dig_Q_roundtrip_set : forall (d : Dig) (x : Q),
  d = dQ x -> dQeqTB (dig_Q d) x :=
  DTPT_Bridge_Dig.DTPT_Bridge_Dig.dig_Q_roundtrip_set.

(* ---------- 簇 B5（DTPT_Bridge §9，） ---------- *)

Definition all_B5_H_devsum_count_ub_set : forall l : list Q,
  QleTB (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)) :=
  DTPT_Bridge.DTPT_Bridge.H_devsum_count_ub_set.

Definition all_B5_H_max_q_anti_set : forall l p : list Q,
  QleTB (maxfreq l) (maxfreq p) -> QleTB (H_max_q p) (H_max_q l) :=
  DTPT_Bridge.DTPT_Bridge.H_max_q_anti_set.

(* ---------- 簇 B6（DTPT_Bridge_Rot §2–§6，） ---------- *)

Definition all_B6_phase_dev_stable_set : forall (l : list Q) (k : nat),
  phase_dev l k = false -> QeqTR (H_adj (rotc k l)) (H_adj (P0 l)) :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.phase_dev_stable_set.

Definition all_B6_phase_dev_spec_set : forall (l : list Q) (k : nat),
  {phase_dev l k = true} + {phase_dev l k = false} :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.phase_dev_spec_set.

Definition all_B6_H_rotc_separates_set :
  {l : list Q & {n : nat & H_adj (rotc n l) <> H_adj l}} :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.H_rotc_separates_set.

(* ---------- 簇 B7（DTPT_Bridge_Rot §8，） ---------- *)

Definition all_B7_H_adj_Pmid_seam_set : forall (l : list Q) (s k : nat),
  k <> 0%nat -> (k < length l)%nat ->
  QeqTR (H_adj (Pmid l s k))
        (H_adj (firstn k (P0 l)) + H_adj (skipn k l) + Qabs (hd 0 (skipn k l) - lastq (firstn k (P0 l)))) :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.H_adj_Pmid_seam_set.

Definition all_B7_H_adj_Pmid_sorted_ub2_set : forall (l : list Q) (s k : nat),
  SortedQ l -> QleTR (H_adj (Pmid l s k)) (2 * (lastq (P0 l) - hd 0 (P0 l))) :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.H_adj_Pmid_sorted_ub2_set.

Definition all_B7_Pmid_collapse_wit_set :
  {l : list Q & Pmid [0; 1; 2] 0%nat 1%nat = l} :=
  DTPT_Bridge_Rot.DTPT_Bridge_Rot.Pmid_collapse_wit_set.

(* ---------- 簇 B8（DTPT_Bridge §11，） ---------- *)

Definition all_B8_H_freq_dpi_set : forall f : Q -> Q,
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleTB (H_freq (map f l)) (H_freq l) :=
  DTPT_Bridge.DTPT_Bridge.H_freq_dpi_set.

Definition all_B8_H_min_q_anti_set : forall l p : list Q,
  QleTB (collide l) (collide p) -> QleTB (H_min_q p) (H_min_q l) :=
  DTPT_Bridge.DTPT_Bridge.H_min_q_anti_set.

Definition all_B8_H_freq_eq0_all_same_set (l : list Q) :
  {all_same l} + {~ all_same l} :=
  DTPT_Bridge.DTPT_Bridge.H_freq_eq0_all_same_set l.

(* ========== §C 金标准数值锚（闭式数值等式 8 件；
     证明＝核内换形显式项直取，右端为显式见证值） ========== *)

Definition all_anchor_gate_pass_hi : gate_pass 1 0 = true.
Proof. exact (@eq_refl bool true). Defined.

Definition all_anchor_phase_dev_true : phase_dev [0; 1; 2] 1 = true.
Proof. exact (@eq_refl bool true). Defined.

Definition all_anchor_phase_dev_false : phase_dev [0; 1; 2] 0 = false.
Proof. exact (@eq_refl bool false). Defined.

Definition all_anchor_collide_012 : collide [0; 1; 2] = 3 # 9.
Proof. exact (@eq_refl Q (3 # 9)). Defined.

Definition all_anchor_mu_012 : mu [0; 1; 2] 0 = 1 # 3.
Proof. exact (@eq_refl Q (1 # 3)). Defined.

(* H_freq 零点判定：全同值表零点（简并态） *)
Definition all_anchor_H_freq_zero : Qeq_bool (H_freq [5; 5; 5]) 0 = true.
Proof. exact (@eq_refl bool true). Defined.

(* H_freq 值面：互异三值表 1 - 3#9 = 2#3 *)
Definition all_anchor_H_freq_value : Qeq_bool (H_freq [0; 1; 2]) (2 # 3) = true.
Proof. exact (@eq_refl bool true). Defined.

(* H_adj 样例：升序三值表 spread = 2 *)
Definition all_anchor_H_adj_012 : Qeq_bool (H_adj [0; 1; 2]) 2 = true.
Proof. exact (@eq_refl bool true). Defined.

(* ========== §D 统一提取面（全部使用件逐件 Extraction，
     b10_ 前缀；Obj.magic 全量 grep 计数 0） ========== *)

Set Extraction Output Directory ".".

Extraction "b10_all_B1_C_sorted_min_adj_set.ml" all_B1_C_sorted_min_adj_set.
Extraction "b10_all_B1_QeqT_of_Qeq.ml" all_B1_QeqT_of_Qeq.
Extraction "b10_all_B1_QeqT_to_Qeq.ml" all_B1_QeqT_to_Qeq.
Extraction "b10_all_B2_H_freq_perm_set.ml" all_B2_H_freq_perm_set.
Extraction "b10_all_B2_H_chain_set.ml" all_B2_H_chain_set.
Extraction "b10_all_B2_H_devsum_zero_iff_sorted_set.ml" all_B2_H_devsum_zero_iff_sorted_set.
Extraction "b10_all_B3_tarski_set.ml" all_B3_tarski_set.
Extraction "b10_all_B3_audit_node_spec_set.ml" all_B3_audit_node_spec_set.
Extraction "b10_all_B4_is_num_spec.ml" all_B4_is_num_spec.
Extraction "b10_all_B4_u12_gate_chain_QleT.ml" all_B4_u12_gate_chain_QleT.
Extraction "b10_all_B4_dig_Q_roundtrip_set.ml" all_B4_dig_Q_roundtrip_set.
Extraction "b10_all_B5_H_devsum_count_ub_set.ml" all_B5_H_devsum_count_ub_set.
Extraction "b10_all_B5_H_max_q_anti_set.ml" all_B5_H_max_q_anti_set.
Extraction "b10_all_B6_phase_dev_stable_set.ml" all_B6_phase_dev_stable_set.
Extraction "b10_all_B6_phase_dev_spec_set.ml" all_B6_phase_dev_spec_set.
Extraction "b10_all_B6_H_rotc_separates_set.ml" all_B6_H_rotc_separates_set.
Extraction "b10_all_B7_H_adj_Pmid_seam_set.ml" all_B7_H_adj_Pmid_seam_set.
Extraction "b10_all_B7_H_adj_Pmid_sorted_ub2_set.ml" all_B7_H_adj_Pmid_sorted_ub2_set.
Extraction "b10_all_B7_Pmid_collapse_wit_set.ml" all_B7_Pmid_collapse_wit_set.
Extraction "b10_all_B8_H_freq_dpi_set.ml" all_B8_H_freq_dpi_set.
Extraction "b10_all_B8_H_min_q_anti_set.ml" all_B8_H_min_q_anti_set.
Extraction "b10_all_B8_H_freq_eq0_all_same_set.ml" all_B8_H_freq_eq0_all_same_set.
Extraction "b10_all_anchor_gate_pass_hi.ml" all_anchor_gate_pass_hi.
Extraction "b10_all_anchor_phase_dev_true.ml" all_anchor_phase_dev_true.
Extraction "b10_all_anchor_phase_dev_false.ml" all_anchor_phase_dev_false.
Extraction "b10_all_anchor_collide_012.ml" all_anchor_collide_012.
Extraction "b10_all_anchor_mu_012.ml" all_anchor_mu_012.
Extraction "b10_all_anchor_H_freq_zero.ml" all_anchor_H_freq_zero.
Extraction "b10_all_anchor_H_freq_value.ml" all_anchor_H_freq_value.
Extraction "b10_all_anchor_H_adj_012.ml" all_anchor_H_adj_012.

(* ========== §E 公理闭包审计（全部使用件，期望全 Closed） ========== *)

Print Assumptions all_B1_C_sorted_min_adj_set.
Print Assumptions all_B1_QeqT_of_Qeq.
Print Assumptions all_B1_QeqT_to_Qeq.
Print Assumptions all_B2_H_freq_perm_set.
Print Assumptions all_B2_H_chain_set.
Print Assumptions all_B2_H_devsum_zero_iff_sorted_set.
Print Assumptions all_B3_tarski_set.
Print Assumptions all_B3_audit_node_spec_set.
Print Assumptions all_B4_is_num_spec.
Print Assumptions all_B4_u12_gate_chain_QleT.
Print Assumptions all_B4_dig_Q_roundtrip_set.
Print Assumptions all_B5_H_devsum_count_ub_set.
Print Assumptions all_B5_H_max_q_anti_set.
Print Assumptions all_B6_phase_dev_stable_set.
Print Assumptions all_B6_phase_dev_spec_set.
Print Assumptions all_B6_H_rotc_separates_set.
Print Assumptions all_B7_H_adj_Pmid_seam_set.
Print Assumptions all_B7_H_adj_Pmid_sorted_ub2_set.
Print Assumptions all_B7_Pmid_collapse_wit_set.
Print Assumptions all_B8_H_freq_dpi_set.
Print Assumptions all_B8_H_min_q_anti_set.
Print Assumptions all_B8_H_freq_eq0_all_same_set.
Print Assumptions all_anchor_gate_pass_hi.
Print Assumptions all_anchor_phase_dev_true.
Print Assumptions all_anchor_phase_dev_false.
Print Assumptions all_anchor_collide_012.
Print Assumptions all_anchor_mu_012.
Print Assumptions all_anchor_H_freq_zero.
Print Assumptions all_anchor_H_freq_value.
Print Assumptions all_anchor_H_adj_012.
