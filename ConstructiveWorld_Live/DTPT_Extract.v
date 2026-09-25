(* ==========================================================================)
   DTPT_Extract.v — 提取面门控套件
   使命: §1 提取检验（核心件 Extraction，Obj.magic=0 验收）；§2 计算行为锚（vm_compute 级数值正确性回归面）；§3 可执行审查链（gate_chain bool 面 + phase 判定 bool 化等值 + 行为定理）；§4 质量回归与 phase_side 退化可执行化（u12_ 前缀全套）。
   依赖: DTPT、DTPT_Entropy、DTPT_Truth；Stdlib QArith、List、Arith、Permutation、Extraction。
   对标: 可提取性验收与计算行为回归（形式化软件工程方法层）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Require DTPT.
Require DTPT_Entropy.
Require DTPT_Truth.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Truth.DTPT_Truth.

Module DTPT_Extract.

(* ========== §1 提取检验（保底件） ========== *)

(* 每件单独提取为「名_ext.ml」，防撞产物名；验收后删除产物。
   逐件独立提取使 Obj.magic 计数可定位到具体计算件。 *)

Set Extraction Output Directory ".".
Extraction "gate_pass_ext.ml" gate_pass.
Extraction "H_adj_ext.ml" H_adj.
Extraction "freq_ext.ml" freq.
Extraction "mu_ext.ml" mu.
Extraction "level_le_ext.ml" DTPT_Truth.DTPT_Truth.level_le.
Extraction "ev_size_ext.ml" DTPT_Truth.DTPT_Truth.ev_size.
Extraction "trLevel_geq_ext.ml" DTPT_Truth.DTPT_Truth.trLevel_geq.
Extraction "phase_side_ext.ml" phase_side.

(* ========== §2 计算行为钉死（主定理·金标准回归面） ========== *)

(* gate_pass 样例表：阈值 1/2 下 0/1/2 的三行真值（六格逐格钉死）。
   注意 gate_pass 形参序为 (threshold H)，阈值在前。 *)
Theorem u12_gate_pass_t1_h0 : gate_pass 1 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t1_h1 : gate_pass 1 1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t1_h2 : gate_pass 1 2 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h0 : gate_pass 2 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h1 : gate_pass 2 1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h2 : gate_pass 2 2 = true.
Proof. vm_compute. reflexivity. Qed.

(* freq 具体列计数：[1;2;2;3] 中 2 出现 2 次 *)
Theorem u12_freq_1223_2 : freq [1;2;2;3] 2 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ev_size 具体证据树尺寸：evPair(evNum 1)(evSeq [1;2]) = 1+1+1 = 3 *)
Theorem u12_ev_size_pair_num_seq :
  DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.evPair (DTPT_Truth.DTPT_Truth.evNum 1)
                                       (DTPT_Truth.DTPT_Truth.evSeq [1;2])) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* level_le 全序判定器样例：Lv1<=Lv2 真、Lv2<=Lv1 假 *)
Theorem u12_level_le_12 : DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv1 DTPT_Truth.DTPT_Truth.Lv2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_level_le_21 : DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv2 DTPT_Truth.DTPT_Truth.Lv1 = false.
Proof. vm_compute. reflexivity. Qed.

(* trLevel_geq 具体节点判定：Lv1 节点过 Lv0 门真、过 Lv2 门假 *)
Definition u12_trn1 : DTPT_Truth.DTPT_Truth.TrNode :=
  DTPT_Truth.DTPT_Truth.mkTrNode DTPT_Truth.DTPT_Truth.Lv1 (dQ 1) (dQ 1) (DTPT_Truth.DTPT_Truth.evNum 1).

Theorem u12_trLevel_geq_lv0 : DTPT_Truth.DTPT_Truth.trLevel_geq u12_trn1 DTPT_Truth.DTPT_Truth.Lv0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_trLevel_geq_lv2 : DTPT_Truth.DTPT_Truth.trLevel_geq u12_trn1 DTPT_Truth.DTPT_Truth.Lv2 = false.
Proof. vm_compute. reflexivity. Qed.

(* phase_side 具体列判定（X2-1 退化实证可执行化：基座 rot 为恒等退化，
   Pinf = l，故相位判定恒落 0 侧；三实例钉死） *)
Theorem u12_phase_side_301_s0 : phase_side [3;0;1] 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_phase_side_301_s2 : phase_side [3;0;1] 2 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_phase_side_nil : phase_side [] 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* H_adj 具体列数值：乱序 4、有序 3（Qeq 面） *)
Theorem u12_H_adj_301 : H_adj [3;0;1] == 4%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_H_adj_013 : H_adj [0;1;3] == 3%Q.
Proof. vm_compute. reflexivity. Qed.

(* ========== §3 可执行审查链（主件） ========== *)

(* 相位判定 bool 化：与 phase_side 同一 Qle_bool 判据，零 Prop 前提 *)
Definition u12_phase_side_bool (l : list Q) (s : nat) : bool :=
  Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)).

(* bool 化件与原 nat 判定件的逐点等值桥 *)
Theorem u12_phase_side_bool_spec : forall (l : list Q) (s : nat),
  phase_side l s = if u12_phase_side_bool l s then 0%nat else 1%nat.
Proof.
  intros l s. unfold phase_side, u12_phase_side_bool.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))); reflexivity.
Qed.

(* 可提取审查链：门控 = 阈值过 H_adj 门 且 相位落 P0 侧（s=0 取样） *)
Definition u12_gate_chain (l : list Q) (threshold : Q) : bool :=
  gate_pass threshold (H_adj l) && u12_phase_side_bool l 0%nat.

(* 链上新定义亦可提取（与基座件同链，Obj.magic 面一并验收） *)
Extraction "gate_chain_ext.ml" u12_gate_chain u12_phase_side_bool.

(* 行为定理两件：拒真（阈值截断）与放行（双门同开）各一 *)
Theorem u12_gate_chain_301_t1 : u12_gate_chain [3;0;1] 1 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_301_t5 : u12_gate_chain [3;0;1] 5 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_013_t3 : u12_gate_chain [0;1;3] 3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_nil_t0 : u12_gate_chain [] 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ========== §4 加分件 ========== *)

(* mu 均匀测度数值回归：mu [1;1;2] 1 = 2/3（Qeq 面与 bool 面双钉） *)
Theorem u12_mu_112_1 : mu [1;1;2] 1 == (2 # 3)%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_mu_112_1_bool : Qeq_bool (mu [1;1;2] 1) (2 # 3)%Q = true.
Proof. vm_compute. reflexivity. Qed.

(* freq 空表与零频回归 *)
Theorem u12_freq_nil : freq [] 1 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_freq_1223_5 : freq [1;2;2;3] 5 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* phase_side 退化实证的可执行全称化：基座 rot = firstn ++ skipn 恒等，
   Pinf l s = l，判定归约为 C_sorted_min_adj（P0 侧 H_adj 恒不增）。
   本件为 Prop 面文档件，不进提取链；具体值行为已由 §2 三实例钉死。 *)
(* 【弃用注记】本件在 rot=firstn++skipn 恒等基座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem u12_phase_side_always_zero : forall (l : list Q) (s : nat),
  phase_side l s = 0%nat.
Proof.
  intros l s. unfold phase_side, Pinf, rot.
  rewrite firstn_skipn.
  rewrite (xq_Qle_bool_true _ _ (C_sorted_min_adj l)).
  reflexivity.
Qed.

End DTPT_Extract.

(* ========== 尾注 ==========
   提取产物清单（验收 Obj.magic = 0 后清除，本报告数字存升级报告）：
     gate_pass_ext.ml / H_adj_ext.ml / freq_ext.ml / mu_ext.ml /
     level_le_ext.ml / ev_size_ext.ml / trLevel_geq_ext.ml /
     phase_side_ext.ml / gate_chain_ext.ml
   金标准回归面 = §2 + §3 全部 vm_compute 闭式定理：
     基座任何改动若使这些定理变红，即为行为漂移报警。 *)
