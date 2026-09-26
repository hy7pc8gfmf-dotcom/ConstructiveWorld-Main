(* ============================================================
   DTPT_Bridge_All.v —— 八棒桥接件 + 计算件的统一提取回归套件
   使命：桥接层全部使用件的统一回归面——
     §A 基建：Require 三桥（DTPT_Bridge / DTPT_Bridge_Dig /
        DTPT_Bridge_Rot）+ 计算件 DTPT / DTPT_Entropy（传递依赖
        DTPT_Rotation / DTPT_Truth / DTPT_DigTheory / DTPT_Extract）。
        注记：原任务面 Require「DTPT_Measure」实测偏差：该件已 S1
        归并退役（盘面 DTPT_Measure.v / .vo 均带 .retired_S1 后缀，
        Require 无现役 .vo 可解析），其测度面现役落点＝
        DTPT.v（qsum L2054 / mu L2062）与 DTPT_Entropy.v（collide
        L1737）——Require DTPT + DTPT_Entropy 已全数覆盖使用面；
        本件按盘面现役态执行，退役件零触碰零改动。
     §B 使用面抽验：八簇（B1–B8）每簇 2–3 件代表桥件的重述式
        re-Port——陈述面照抄被使用桥件，证明＝直接别名使用
        （零重证、零新证明思想）；QleT / QeqT / sumbool / sigT
        四形各至少一件（覆盖矩阵见 §B 头注），另含 B4 dQleT /
        dQeqT 对偶形、B2 And(Type) 积形、B4 prod 证书形。
     §C 金标准数值锚 8 件：gate_pass / phase_dev 双向 / collide /
        mu / H_freq 零点判定 + 值面 / H_adj 样例，全部闭式数值等式
        （证明＝核内换形显式项直取，右端为显式见证值；各值实算
        核对在案：gate_pass 1 0 = true、phase_dev [0;1;2] 1 = true /
        0 = false、collide [0;1;2] = 3#9、mu [0;1;2] 0 = 1#3、
        Qeq_bool (H_freq [5;5;5]) 0 = true、Qeq_bool (H_freq
        [0;1;2]) (2#3) = true、Qeq_bool (H_adj [0;1;2]) 2 = true）。
     §D 统一提取面：全部使用件（22 抽验 + 8 数值锚）逐件 Extraction
        （b10_ 前缀），Obj.magic 全量 grep 计数 0。
     §E 公理闭包审计：全部使用件 Print Assumptions，期望全 Closed。
   依赖：DTPT、DTPT_Entropy、DTPT_Rotation、DTPT_DigTheory、
     DTPT_Extract、DTPT_Truth、DTPT_Bridge、DTPT_Bridge_Dig、
     DTPT_Bridge_Rot；Stdlib QArith、List、Bool、ZArith、
     Permutation、Lia、Extraction。
   限定名纪律：三桥模块零 Import（QleT/QeqT 在 DTPT_Bridge 与
     DTPT_Bridge_Rot 双处定义、dQleT/dQeqT 在 Bridge_Dig——限名
     隔离防撞），使用面一律全限定名或 §B0 缩记；计算件名面按三桥
     各文件生效 Import 序复刻（相对次序保持；DTPT_Truth 置末＝
     B3 §7 生效遮蔽序复刻，Level/Evidence 取 Truth 侧与其一致）。
   构造性注记：零承认、公理面为空；Error=0；Obj.magic=0；
     语句面全 Set（QleT/QeqT/sumbool/sigT）。
   对标：桥接/重述层（type synonym re-export）惯例。
   编译配方：Rocq 9.1 直调 rocq c -Q . "" DTPT_Bridge_All.v，
     cpu_guard 包装；提取产物定向本目录（Set Extraction Output
     Directory "."）。
   ============================================================ *)


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

(* ========== §B0 桥件缩记（纯 Notation 缩写，零语义新增） ========== *)

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
     簇  | 桥件(形)                                   | 基础件
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
