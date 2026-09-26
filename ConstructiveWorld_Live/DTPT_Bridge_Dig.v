(* ==========================================================================)
   DTPT_Bridge_Dig.v — DTPT 判码理论的桥接与门链套件
   使命: is_num_spec/is_num_size1_set（数值见证）、尺寸单调可判定（sub_dig_size_mono_set/dig_eqb_size_dec_true）、dig_Q 投影往返、门链 u12_gate_chain_spec 与 QleT 证书（gate_pass_QleT）、判定器 dig_dec_sound/shape/size。
   依赖: DTPT、DTPT_DigTheory、DTPT_Extract；Stdlib QArith、List、Bool、ZArith、Arith、Lia、Extraction。
   对标: 数字编码树的尺寸单调性与可判定桥（组合编码理论）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Bool ZArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Require DTPT.
Require DTPT_DigTheory.
Require DTPT_Extract.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Extract.DTPT_Extract.

Module DTPT_Bridge_Dig.

(* ========== §1 本地信息性类型族（QleT/QeqT 惯例 d 前缀对应副本） ========== *)

Inductive dQleT (x y : Q) : Type :=
| dqleT_intro : (x <= y)%Q -> dQleT x y.

Arguments dqleT_intro {x y} _.

Inductive dQeqT (x y : Q) : Type :=
| dqeqT_intro : (x == y)%Q -> dQeqT x y.

Arguments dqeqT_intro {x y} _.

(* ========== §2 保底件：is_num 可执行判定桥 ========== *)

(* 判定器完整性：is_num 对任意码可执行判定（sumbool 直构，
   bool 计算分支即判定；七构造子穷举分派） *)
Theorem is_num_spec : forall d : Dig,
  {is_num d = true} + {is_num d = false}.
Proof.
  intro d. destruct d as [x | a b | l | n f | a b | a | a b];
    [left | right | right | right | right | right | right]; reflexivity.
Defined.

(* 特征定理使用面：is_num=true 时尺寸见证 1（sigT 信息性携带；
   使用盘上 is_num_size1 L372 正向形——头注 b：尺寸 1 不反演
   is_num=true，dSeq [] 反例盘上 dig_size_one_not_only_num 在案，
   本件不桥反向假命题） *)
Theorem is_num_size1_set : forall d : Dig,
  is_num d = true ->
  {n : nat & (n = 1%nat /\ dig_size d = n)}.
Proof.
  intros d H. exists 1%nat. split; [reflexivity | exact (is_num_size1 d H)].
Defined.

(* ========== §3 主定理件：塔尺寸单调的信息性面 ========== *)

(* 可执行尺寸比较器：对任意两码，Nat.leb 计算面分派 sumbool *)
Definition dig_size_le_dec (a d : Dig) :
  {Nat.leb (dig_size a) (dig_size d) = true} +
  {Nat.leb (dig_size a) (dig_size d) = false}.
Proof.
  destruct (Nat.leb (dig_size a) (dig_size d));
    [left | right]; reflexivity.
Defined.

(* 使用桥·sub_dig 尺寸单调（HAlg 并入件 sub_dig_size_mono L616 的
   信息性面）：sub_dig a d = true 时比较器必落左支——右支改载
   「d 尺寸严格小于 a」的 nat 判定见证（leb false 的等值换算面，
   B3 trLevel_geq_mono_set 同款定式：右支计算面直构，零
   False_rect 入提取位）。以盘面现役陈述为准择可证形。 *)
Theorem sub_dig_size_mono_set : forall d a : Dig,
  sub_dig a d = true ->
  {Nat.leb (dig_size a) (dig_size d) = true} +
  {(dig_size d < dig_size a)%nat}.
Proof.
  intros d a Hsub.
  destruct (Nat.leb (dig_size a) (dig_size d)) eqn:E.
  - left. reflexivity.
  - right. apply Nat.leb_gt. exact E.
Defined.

(* 使用桥·相干面（Prop，不提取）：sub_dig 前提下比较器恒左支
   ——直接使用盘上 sub_dig_size_mono L616 *)
Theorem sub_dig_size_dec_true : forall d a : Dig,
  sub_dig a d = true -> Nat.leb (dig_size a) (dig_size d) = true.
Proof.
  intros d a Hsub.
  exact (proj2 (Nat.leb_le (dig_size a) (dig_size d))
                (sub_dig_size_mono d a Hsub)).
Qed.

(* 使用桥·dig_eqb 尺寸可传（盘上 dig_eqb_size_bound L458 的判定面
   ——n := dig_size a 自实例） *)
Theorem dig_eqb_size_dec_true : forall a b : Dig,
  dig_eqb a b = true -> Nat.leb (dig_size a) (dig_size b) = true.
Proof.
  intros a b Hab.
  exact (proj2 (Nat.leb_le (dig_size a) (dig_size b))
                (dig_eqb_size_bound (dig_size a) a b
                                    (le_n (dig_size a)) Hab)).
Qed.

(* 使用桥·dig_Q 投影往返信息性面（盘上 dig_Q_roundtrip L319 的
   QeqT 面——头注 c：dig_Q 非单射（默认零碰撞），往返只取
   d = dQ x 方向，禁桥反向假命题） *)
Theorem dig_Q_roundtrip_set : forall (d : Dig) (x : Q),
  d = dQ x -> dQeqT (dig_Q d) x.
Proof.
  intros d x H. subst d. apply dqeqT_intro.
  exact (Qeq_refl (dig_Q (dQ x))).
Defined.

(* ========== §4 主件：提取门控全链 Set 面 ========== *)

(* 全链判定器：u12_gate_chain（gate_pass ∧ phase bool，
   DTPT_Extract.v L139 组装）对任意列/阈值可执行判定 *)
Theorem u12_gate_chain_spec : forall (l : list Q) (t : Q),
  {u12_gate_chain l t = true} + {u12_gate_chain l t = false}.
Proof.
  intros l t. destruct (u12_gate_chain l t);
    [left | right]; reflexivity.
Defined.

(* 双门分解对：审查链的信息性拆解——阈值门 gate_pass（DTPT.v
   L865）与相位门 u12_phase_side_bool（DTPT_Extract.v L127）各交
   独立 sumbool 判定（B1 §2 And 惯例的 prod 直构） *)
Definition u12_gate_chain_gates (l : list Q) (t : Q) :
  prod ({gate_pass t (H_adj l) = true} + {gate_pass t (H_adj l) = false})
       ({u12_phase_side_bool l 0%nat = true} +
        {u12_phase_side_bool l 0%nat = false}).
Proof.
  split.
  - destruct (gate_pass t (H_adj l)); [left | right]; reflexivity.
  - destruct (u12_phase_side_bool l 0%nat); [left | right]; reflexivity.
Defined.

(* 阈值门的 QleT 证书：gate_pass t h = true 经定义面
   （if Qle_bool h t then true else false，DTPT.v L866）换算出
   Qle_bool h t = true——证书 h <= t 以 dQleT 信息性携带 *)
Theorem gate_pass_QleT : forall t h : Q,
  gate_pass t h = true -> dQleT h t.
Proof.
  intros t h H. unfold gate_pass in H.
  destruct (Qle_bool h t) eqn:E; [| discriminate H].
  apply dqleT_intro. unfold Qle, Qle_bool in E |- *.
  apply Z.leb_le. exact E.
Defined.

(* 主定理·全链 QleT 证书：u12_gate_chain l t = true 时双门各交
   QleT 证书——阈值门 H_adj l <= t（门语义：H 不超阈值，金标准
   gate_pass 1 0 = true 同向）、相位门 H_adj (P0 l) <=
   H_adj (Pinf l 0)（证书 Type 值交付，bool 前提 Prop 擦除；
   与判定器/分解对合读即门控全链 QleT/sumbool 信息性链） *)
Theorem u12_gate_chain_QleT : forall (l : list Q) (t : Q),
  u12_gate_chain l t = true ->
  prod (dQleT (H_adj l) t)
       (dQleT (H_adj (P0 l)) (H_adj (Pinf l 0%nat))).
Proof.
  intros l t Hc. unfold u12_gate_chain in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hg Hp].
  split.
  - exact (gate_pass_QleT _ _ Hg).
  - unfold u12_phase_side_bool in Hp.
    apply dqleT_intro. unfold Qle, Qle_bool in Hp |- *.
    apply Z.leb_le. exact Hp.
Defined.

(* ========== §5 加分件：dig_dec 形状+尺寸双判（可判定子面） ========== *)
(* S7 边界 d 沿用：Dig 全相等可判定不可证（dCode 载函数相等不可
   判定，盘上互斥性按 21 对判别落面不造决策器），本件不越界——
   dig_dec 只做「构造子形状 + 塔尺寸」双判的可判定子面，是
   Leibniz 相等的可靠下近似：
     可靠性 a = b -> dig_dec a b = true（dig_dec_sound）；
     完备性不成立（反例见证 dig_dec_not_eq_witness 在案：
     dPair (dQ 0) (dQ 0) 与 dPair (dQ 1) (dQ 0) 同形同尺寸而不等）；
     更细的计算近似＝盘上 dig_eqb（Q 叶 Qeq_bool 值相等面，
     头注 e：true 保尺寸可传不保 Leibniz 相等，本件 §3 已桥其
     尺寸可传面）。 *)

Definition dig_tag (d : Dig) : nat :=
  match d with
  | dQ _ => 0%nat
  | dPair _ _ => 1%nat
  | dSeq _ => 2%nat
  | dCode _ _ => 3%nat
  | dJudge _ _ => 4%nat
  | dModel _ => 5%nat
  | dProofT _ _ => 6%nat
  end.

Definition dig_dec (a b : Dig) : bool :=
  andb (Nat.eqb (dig_tag a) (dig_tag b))
       (Nat.eqb (dig_size a) (dig_size b)).

Theorem dig_dec_sound : forall a b : Dig, a = b -> dig_dec a b = true.
Proof.
  intros a b Heq. rewrite Heq. unfold dig_dec.
  apply andb_true_iff. split; apply Nat.eqb_refl.
Qed.

Theorem dig_dec_shape : forall a b : Dig,
  dig_dec a b = true -> dig_tag a = dig_tag b.
Proof.
  intros a b H. unfold dig_dec in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply Nat.eqb_eq. exact H1.
Qed.

Theorem dig_dec_size : forall a b : Dig,
  dig_dec a b = true -> dig_size a = dig_size b.
Proof.
  intros a b H. unfold dig_dec in H.
  apply andb_true_iff in H. destruct H as [_ H2].
  apply Nat.eqb_eq. exact H2.
Qed.

(* 边界见证（定义性双钉）：同形同尺寸判真而两码 Leibniz 不等
   ——完备性反例（不等侧经 dPair/dQ/Qmake 三层构造子注入到
   Z0 vs Zpos 1 构造子判别闭合） *)
Theorem dig_dec_not_eq_witness :
  dig_dec (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0)) = true /\
  dPair (dQ 0) (dQ 0) <> dPair (dQ 1) (dQ 0).
Proof.
  split; [reflexivity | intros H; congruence].
Qed.

(* ========== §6 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Set Extraction Output Directory ".".
Extraction "b4_is_num_spec_ext.ml" is_num_spec.
Extraction "b4_is_num_size1_set_ext.ml" is_num_size1_set.
Extraction "b4_dig_size_le_dec_ext.ml" dig_size_le_dec.
Extraction "b4_sub_dig_size_mono_set_ext.ml" sub_dig_size_mono_set.
Extraction "b4_dig_Q_roundtrip_set_ext.ml" dig_Q_roundtrip_set.
Extraction "b4_u12_gate_chain_spec_ext.ml" u12_gate_chain_spec.
Extraction "b4_u12_gate_chain_gates_ext.ml" u12_gate_chain_gates.
Extraction "b4_gate_pass_QleT_ext.ml" gate_pass_QleT.
Extraction "b4_u12_gate_chain_QleT_ext.ml" u12_gate_chain_QleT.
Extraction "b4_dig_dec_ext.ml" dig_dec.

(* ========== 终验：公理闭包审计 ========== *)

Print Assumptions is_num_spec.
Print Assumptions is_num_size1_set.
Print Assumptions sub_dig_size_mono_set.
Print Assumptions u12_gate_chain_QleT.
Print Assumptions dig_dec.
Print Assumptions dig_dec_not_eq_witness.

End DTPT_Bridge_Dig.
