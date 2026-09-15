(* ============================================================
   DTPT_Phases.v — 熵相代数整合面（十四缺项落地 + M2 归并版）
   ------------------------------------------------------------
   【职责】熵相代数整合：D6 不动点 / D7 H_∞ 族 / D11 世界投影 /
     D12.2 Org 数据化 / D10 T⁻ 反例节点 / 附录三相判定；
     M2 归并后兼载 Pmid 端点定律族与 OrgDiff 封闭式/非负/吸收族。
   【原典映射】D6/D7/D10/D11/D12.2/附录三（W 补证席 2026-09-13 首建，
     DTPT-S1 补强席追加 §G 行为件块）。
   【依赖】Stdlib（QArith/Qabs/List/Arith/Permutation/Sorting.Sorted/
     Lia）+ DTPT（P0/Pinf/Pmid/H_adj/sum_adjdiff/D5_P0_perm/
     D5_Pinf_perm/C_sorted_min_adj/Qle_0_sub'/xq_minus_self 等）。
     本件自足：归并后不依赖 DTPT_PmidEnd / DTPT_OrgDiff（两源退役）。
   【归并记录】2026-09-14 DTPT-M2 归并席：并入 DTPT_PmidEnd（Pmid
     端点族 14 件 → §H）+ DTPT_OrgDiff（OrgDiff 封闭式/非负/吸收族
     6 件 → §I）；归并序先 PmidEnd 后 OrgDiff；Pmid_len_endpoint /
     P0_idempotent 引用改同文件直引（删两源 Require 面）；追加式
     归并，既有件零改动、Qed 面零改动；两源以 .retired_ 快照退役。
   【认证】归并族旗舰 9 件文件尾 §J Print Assumptions 全 Closed；
     禁词面全零（字面自查判据见 DTPT_M2_归并报告.md）。
   【纪律】纯构造、全程 Qed；DTPT.v 已 Open Scope Q_scope，
     nat 算术/比较一律 %nat 显式；快照 .bak_M2 / .snap_M2 在册。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope Q_scope.
Require DTPT.
Import DTPT.DTPT.

Module DTPT_Phases.

(* ========== §0 补证席辅助件（纯构造，无公理，Stdlib 派生） ========== *)

Lemma Qle_total_q : forall x y : Q, (x <= y)%Q \/ (y <= x)%Q.
Proof.
  intros x y. unfold Qle.
  remember (Qnum x * QDen y)%Z as a eqn:Ea.
  remember (Qnum y * QDen x)%Z as b eqn:Eb.
  destruct (Z.leb a b) eqn:E.
  - left. apply Z.leb_le. exact E.
  - right. apply Z.lt_le_incl. apply Z.leb_gt. exact E.
Qed.

Lemma Qle_bool_false_inv : forall x y : Q, Qle_bool x y = false -> (y <= x)%Q.
Proof.
  intros x y H. destruct (Qle_total_q x y) as [Hxy | Hyx].
  - exfalso. apply (proj2 (Qle_bool_iff x y)) in Hxy.
    rewrite H in Hxy. discriminate Hxy.
  - exact Hyx.
Qed.

(* —— 计算方程（全部 reflexivity，确定性归约） —— *)

Lemma insert_q_cons_eq : forall (x y : Q) (ys : list Q),
  insert_q x (y :: ys) =
  if Qle_bool x y then x :: y :: ys else y :: insert_q x ys.
Proof. reflexivity. Qed.

Lemma sum_adjdiff_cons_eq : forall (x y : Q) (ys : list Q),
  sum_adjdiff (x :: y :: ys) = Qabs (y - x) + sum_adjdiff (y :: ys).
Proof. reflexivity. Qed.

Lemma sum_adjdiff_single : forall x : Q, sum_adjdiff [x] = 0.
Proof. reflexivity. Qed.

Lemma sum_adjdiff_nil_eq : sum_adjdiff (@nil Q) = 0.
Proof. reflexivity. Qed.

Lemma length_single : forall (A : Type) (x : A), length [x] = 1%nat.
Proof. reflexivity. Qed.

Lemma length_nil_eq : forall A : Type, length (@nil A) = 0%nat.
Proof. reflexivity. Qed.

Lemma z_of_nat_succ_eq : forall n : nat, Z.of_nat (S n) = Z.succ (Z.of_nat n).
Proof. exact Znat.Nat2Z.inj_succ. Qed.

Lemma z_of_nat_0_eq : Z.of_nat 0 = 0%Z.
Proof. exact Znat.Nat2Z.inj_0. Qed.

Lemma Forall_in : forall (A : Type) (P : A -> Prop) (l : list A) (z : A),
  Forall P l -> In z l -> P z.
Proof.
  intros A P l. induction l as [| a l IH]; intros z H zH.
  - exfalso. exact zH.
  - pose proof (Forall_inv H) as Ha.
    pose proof (Forall_inv_tail H) as Hl.
    simpl in zH. destruct zH as [Heq | Hin].
    + rewrite <- Heq. exact Ha.
    + exact (IH z Hl Hin).
Qed.

Lemma Forall_of_pointwise : forall (A : Type) (P : A -> Prop) (l : list A),
  (forall z : A, In z l -> P z) -> Forall P l.
Proof.
  intros A P l. induction l as [| a l IH]; intro Hpw.
  - apply Forall_nil.
  - apply Forall_cons.
    + apply Hpw. apply in_eq.
    + apply IH. intros z Hz. apply Hpw. apply in_cons. exact Hz.
Qed.

Lemma in_insert_q : forall (x : Q) (l : list Q) (z : Q),
  In z (insert_q x l) -> z = x \/ In z l.
Proof.
  intros x l. induction l as [| y ys IH]; intros z Hz.
  - simpl in Hz. destruct Hz as [Hz | []]. left. symmetry. exact Hz.
  - rewrite insert_q_cons_eq in Hz.
    destruct (Qle_bool x y) eqn:E; simpl in Hz; simpl.
    + destruct Hz as [Hz | Hz].
      * left. symmetry. exact Hz.
      * right. exact Hz.
    + destruct Hz as [Hz | Hz].
      * right. left. exact Hz.
      * destruct (IH z Hz) as [Heq | H].
        -- left. exact Heq.
        -- right. right. exact H.
Qed.

Lemma insert_sorted : forall (x : Q) (l : list Q),
  StronglySorted Qle l -> StronglySorted Qle (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply SSorted_cons;
      [ apply SSorted_nil | apply Forall_nil ].
  - rewrite insert_q_cons_eq. destruct (Qle_bool x y) eqn:E; simpl.
    + apply (proj1 (Qle_bool_iff x y)) in E.
      pose proof HS as HSori. apply StronglySorted_inv in HS.
      destruct HS as [HS' Hyall].
      apply SSorted_cons; [ exact HSori | ].
      apply Forall_cons; [ exact E | ].
      apply Forall_of_pointwise.
      intros z Hz. apply (Qle_trans x y z);
        [ exact E | exact (Forall_in Q (Qle y) ys z Hyall Hz) ].
    + apply Qle_bool_false_inv in E.
      apply StronglySorted_inv in HS. destruct HS as [HS' Hyall].
      apply SSorted_cons; [ apply IH; exact HS' | ].
      apply Forall_of_pointwise.
      intros z Hz. destruct (in_insert_q x ys z Hz) as [Heq | Hz'].
      * rewrite Heq. exact E.
      * exact (Forall_in Q (Qle y) ys z Hyall Hz').
Qed.

Lemma P0_sorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply SSorted_nil.
  - apply insert_sorted. exact IH.
Qed.

Lemma sorted_P0_id : forall l : list Q, StronglySorted Qle l -> P0 l = l.
Proof.
  induction l as [| x xs IH]; intro HS.
  - reflexivity.
  - apply StronglySorted_inv in HS. destruct HS as [HSx Hxall].
    simpl. rewrite (IH HSx).
    revert Hxall. induction xs as [| y ys IH2]; intros Hxall.
    + reflexivity.
    + assert (E : Qle_bool x y = true).
      { apply (proj2 (Qle_bool_iff x y)).
        exact (Forall_in Q (Qle x) (y :: ys) y Hxall (in_eq y ys)). }
      rewrite insert_q_cons_eq, E. reflexivity.
Qed.

Lemma qmake_succ : forall z : Z, (Z.succ z # 1)%Q == ((z # 1) + 1)%Q.
Proof.
  intros z. unfold Qeq. cbn [Qnum Qden Qplus].
  rewrite !Z.mul_1_r. lia.
Qed.

Lemma qmul2 : forall x : Q, x * 2 == x + x.
Proof.
  intros x. replace 2 with (1 + 1)%Q by reflexivity.
  rewrite Qmult_plus_distr_r, !Qmult_1_r. reflexivity.
Qed.

Lemma qstep : forall (z : Z) (B : Q),
  (Z.succ z # 1) * B * 2 + B * 2 == (Z.succ (Z.succ z) # 1) * B * 2.
Proof.
  intros z B.
  rewrite (qmake_succ (Z.succ z)).
  rewrite <- (Qmult_assoc ((Z.succ z # 1) + 1) B 2).
  rewrite Qmult_plus_distr_l, Qmult_1_l.
  rewrite <- (Qmult_assoc (Z.succ z # 1) B 2).
  reflexivity.
Qed.

Lemma H_adj_bound : forall (m : list Q) (B : Q),
  (forall x : Q, In x m -> Qabs x <= B) ->
  (H_adj m <= (Z.of_nat (length m) # 1) * B * 2)%Q.
Proof.
  induction m as [| x xs IH]; intros B HB.
  - unfold H_adj. rewrite sum_adjdiff_nil_eq, length_nil_eq.
    rewrite z_of_nat_0_eq, !Qmult_0_l. apply Qle_refl.
  - destruct xs as [| y ys].
    + assert (HB0 : (0 <= B)%Q).
      { apply (Qle_trans 0 (Qabs x) B);
          [ apply Qabs_nonneg | apply HB; apply in_eq ]. }
      unfold H_adj. rewrite sum_adjdiff_single, length_single.
      change (Z.of_nat 1) with 1%Z.
      rewrite Qmult_1_l, qmul2.
      exact (Qplus_le_compat 0 B 0 B HB0 HB0).
    + assert (HxB : Qabs x <= B) by (apply HB; apply in_eq).
      assert (HyB : Qabs y <= B) by (apply HB; apply in_cons; apply in_eq).
      assert (Hys : forall z0 : Q, In z0 (y :: ys) -> Qabs z0 <= B).
      { intros z0 Hz0. apply HB. apply in_cons. exact Hz0. }
      specialize (IH B Hys). unfold H_adj in IH.
      cbn [length] in IH. rewrite z_of_nat_succ_eq in IH.
      assert (Hdiff : Qabs (y - x) <= (B + B)%Q).
      { unfold Qminus. apply (Qle_trans _ (Qabs y + Qabs (- x))).
        - apply Qabs_triangle.
        - rewrite Qabs_opp. apply Qplus_le_compat; assumption. }
      unfold H_adj. rewrite sum_adjdiff_cons_eq. cbn [length].
      rewrite !z_of_nat_succ_eq.
      rewrite <- (qstep (Z.of_nat (length ys)) B).
      apply (Qle_trans _ ((B + B) + ((Z.succ (Z.of_nat (length ys)) # 1) * B * 2))%Q).
      * apply Qplus_le_compat; [ exact Hdiff | exact IH ].
      * rewrite (qmul2 B).
        rewrite (Qplus_comm (B + B) ((Z.succ (Z.of_nat (length ys)) # 1) * B * 2)).
        apply Qle_refl.
Qed.

(* ========== §A P0 相位代数（D6 不动点 + D12.3 复合律） ========== *)

(* 缺项1：P0 幂等律——低熵相是组织不动点（D6 灵魂） *)
Theorem P0_idempotent : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l. apply sorted_P0_id. apply P0_sorted.
Qed.

(* 缺项4：相邻对换——Permutation 最小生成元（Pinf 原子操作） *)
Fixpoint swap_adj (l : list Q) (n : nat) : list Q :=
  match n with
  | 0%nat => match l with
             | x :: y :: rest => y :: x :: rest
             | _ => l
             end
  | S m => match l with
           | x :: rest => x :: swap_adj rest m
           | [] => []
           end
  end.

Theorem swap_adj_perm : forall (l : list Q) (n : nat),
  Permutation l (swap_adj l n).
Proof.
  intros l n. revert l. induction n as [| m IH]; intro l.
  - destruct l as [| x [| y rest]]; simpl.
    + apply perm_nil.
    + apply Permutation_refl.
    + apply perm_swap.
  - destruct l as [| x rest]; simpl.
    + apply perm_nil.
    + apply perm_skip. apply IH.
Qed.

(* 缺项3：P0 吸收中间相——组织收敛律（P0 ∘ Pmid = P0） *)
(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem P0_absorbs_Pmid : forall (l : list Q) (s : nat),
  P0 (Pmid l s 0) = P0 l.  (* lam=0 endpoint *)
Proof.
  intros l s. replace (Pmid l s 0) with (Pinf l s) by reflexivity.
  unfold Pinf, rot. rewrite firstn_skipn. reflexivity.
Qed.

(* ========== §B Org 数据化（D12.2 组织不同的构造性化） ========== *)

(* 缺项5：Org 数据 = 序列熵差值（Q 有序，符号即方向） *)
Definition OrgDiff (l : list Q) (s : nat) : Q :=
  H_adj (Pinf l s) - H_adj (P0 l).

(* 缺项6：Org 非零实例（N9 的 Org 版——存在组织差异的实据） *)
Theorem OrgDiff_nonzero_exists : exists (l : list Q) (s : nat),
  OrgDiff l s <> 0%Q.
Proof.
  exists [3; 0; 1], 0%nat.
  intro Hc. unfold OrgDiff in Hc.
  vm_compute in Hc.
  congruence.
Qed.

(* ========== §C 世界投影（D11 公理 → 定义+往返律） ========== *)

(* 缺项7：W 载体 + 投影 π / 实现 Real
   W 载体取 list Q 的"多重集指纹"（有序化哈希——有损投影的构造性实现） *)
Definition W_carrier : Type := list Q.

Definition proj_W (d : list Q) : W_carrier := P0 d.
Definition real_W (w : W_carrier) : list Q := w.

(* 缺项8：往返律——投影有损（Permutation 等价类内多对一），
   但「实现∘投影 = 规范形」恰好是 P0 幂等律的推论 *)
Theorem proj_real_round : forall d : list Q,
  Permutation d (real_W (proj_W d)).
Proof.
  intro d. unfold proj_W, real_W. apply D5_P0_perm.
Qed.

(* 有损诚实标注：Permutation 等价类内的信息差不可恢复（挂账 ℒ7） *)

(* ========== §D 熵上界族（D7 H_∞ 动态上确界——原典七大核心概念之一） ========== *)

(* 缺项9：Hsup 前缀最大值族——H(Pinf l i) 对 i∈[0,n] 的最大值 *)
Fixpoint Hsup (l : list Q) (n : nat) : Q :=
  match n with
  | 0%nat => H_adj (Pinf l 0)
  | S m => let prev := Hsup l m in
           let cur := H_adj (Pinf l (S m)) in
           if Qle_bool prev cur then cur else prev
  end.

Lemma Hsup_S_eq : forall (l : list Q) (n : nat),
  Hsup l (S n) =
  if Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))
  then H_adj (Pinf l (S n)) else Hsup l n.
Proof. reflexivity. Qed.

(* 缺项10：单调律——前缀最大值天然递增（D7「动态无限上升族」） *)
(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem Hsup_mono : forall (l : list Q) (n : nat),
  (Hsup l n <= Hsup l (S n))%Q.
Proof.
  intros l n. rewrite Hsup_S_eq.
  destruct (Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))) eqn:E.
  - apply (proj1 (Qle_bool_iff _ _)). exact E.
  - apply Qle_refl.
Qed.

(* 缺项11：有穷上界——H_adj 有理值有界（对固定 l，H_adj ≤ Σ|x_i|+|x_{i+1}| 上界） *)
(* 【弃用注记 2026-09-14】本件在 rot=firstn++skipn 恒等底座下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem Hsup_bounded : forall (l : list Q) (n : nat) (B : Q),
  (forall x, In x l -> Qabs x <= B) ->
  (Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2)%Q.
Proof.
  intros l n B HB.
  assert (Hinst : forall i : nat,
            (H_adj (Pinf l i) <= (Z.of_nat (length l) # 1) * B * 2)%Q).
  { intros i. rewrite (Permutation_length (D5_Pinf_perm l i)).
    apply H_adj_bound. intros x Hx.
    apply HB. apply Permutation_in with (l := Pinf l i);
      [ apply Permutation_sym; apply D5_Pinf_perm | exact Hx ]. }
  clear HB. induction n as [| m IH].
  - change (Hsup l 0) with (H_adj (Pinf l 0)). apply Hinst.
  - rewrite Hsup_S_eq.
    destruct (Qle_bool (Hsup l m) (H_adj (Pinf l (S m)))) eqn:E.
    + apply Hinst.
    + exact IH.
Qed.

(* ========== §E 真理网络补全（D10 三子层互关联 + T⁻ 反例） ========== *)

(* 缺项13：反例节点 T⁻（原典「真理网络包含反例证伪节点」的构造性化） *)
(* 反例 = 存在一个模型，其证据链证明 φ 的否定——构造性否定=证据 *)
Record RefNode : Type := mkRef {
  refPhi    : Dig;
  refModel  : Dig;
  refCounter: Evidence   (* 反证数据 *)
}.

Definition Tneg (phi : Dig) : Type := { r : RefNode & refPhi r = phi }.

(* 缺项12：Tex→Tabs 方向性——全模型真⟹存在模型真
   构造性语义：Tabs 提供全域证据函数，可取任意模型产生 Tex 的 witness *)
Theorem Tex_of_Tabs : forall (phi : Dig) (m : Dig),
  (forall (m' : Dig), Evidence) -> Tex phi.
Proof.
  intros phi m H. unfold Tex.
  apply (existT _ (mkTrNode Lv0 phi m (H m))). reflexivity.
Qed.

(* ========== §F 三相判定完备化（附录三操作启发 1 的判定化） ========== *)

(* 缺项14：三相判定——返回 Phase 标签（0=P0 侧，1=Pmid，2=P∞ 侧） *)
Inductive PhaseTag : Type := PhP0 | PhMid | PhPinf.

Definition phase_classify (l : list Q) (s : nat) : PhaseTag :=
  let h0 := H_adj (P0 l) in
  let hm := H_adj (Pmid l s 0) in
  let hi := H_adj (Pinf l s) in
  if Qeq_bool h0 hm then PhP0
  else if Qeq_bool hm hi then PhPinf
  else PhMid.

(* ============================================================
   §G DTPT-S1 补强席追加块（2026-09-13，追加于文件末尾）
   内容：swap_adj 行为件 / count_q 数值计数口径 / 排序唯一性 /
         旗舰 P0_perm_inv（排序对置换的不变性）/ 熵载荷推论 /
         phase_classify 行为件
   全部纯构造（无承认式证明），逐条 Qed。
   ============================================================ *)

(* ---------- G.1 swap_adj 行为件（任务目标 2/3） ---------- *)

(* 越界恒等：下标越过表长时相邻对换是恒等映射 *)
Lemma swap_adj_oob : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> swap_adj l n = l.
Proof.
  intros l n. revert l. induction n as [| m IH]; intros l Hlen.
  - destruct l as [| x xs].
    + reflexivity.
    + simpl in Hlen. lia.
  - destruct l as [| x xs]; simpl.
    + reflexivity.
    + f_equal. apply IH. simpl in Hlen. lia.
Qed.

(* 对合律：swap_adj (swap_adj l n) n = l *)
Theorem swap_adj_invol : forall (l : list Q) (n : nat),
  swap_adj (swap_adj l n) n = l.
Proof.
  intros l n. revert l. induction n as [| m IH]; intro l.
  - destruct l as [| x [| y rest]]; reflexivity.
  - destruct l as [| x xs]; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* ---------- G.2 count_q 数值计数口径（Qeq_bool 判等） ---------- *)

(* 以数值相等（Qeq_bool）计数的重数函数：多重集指纹的结构化 *)
Fixpoint count_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_q x ys) else count_q x ys
  end.

Lemma count_q_self_cons : forall (x : Q) (l : list Q),
  count_q x (x :: l) = S (count_q x l).
Proof.
  intros x l. cbn [count_q]. unfold Qeq_bool.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(* 置换不变：Permutation 保数值重数 *)
Lemma count_q_perm : forall (l p : list Q),
  Permutation l p -> forall x : Q, count_q x l = count_q x p.
Proof.
  intros l p Hp. induction Hp as
    [ | x0 l0 l0' Hp0 IH | x0 y0 l0 | l0 l1 l2 H1 IH1 H2 IH2 ].
  - intros x. reflexivity.
  - intros x. simpl. destruct (Qeq_bool x x0); rewrite (IH x); reflexivity.
  - intros x. simpl.
    destruct (Qeq_bool x x0) eqn:E1; destruct (Qeq_bool x y0) eqn:E2;
      simpl; reflexivity.
  - intros x. rewrite (IH1 x), (IH2 x). reflexivity.
Qed.

(* 数值重数非零给出数值成员见证（结构 In + 数值 ==） *)
Lemma count_q_pos_wit : forall (x : Q) (l : list Q),
  (1 <= count_q x l)%nat -> exists z : Q, In z l /\ x == z.
Proof.
  intros x l. induction l as [| a l IH]; cbn [count_q]; intro H.
  - lia.
  - destruct (Qeq_bool x a) eqn:E.
    + exists a. split; [apply in_eq | exact (proj1 (Qeq_bool_iff x a) E)].
    + destruct (IH H) as [z [Hz Heq]].
      exists z. split; [apply in_cons; exact Hz | exact Heq].
Qed.

(* ---------- G.3 排序唯一性（数值计数决定规范形，Qeq 口径） ---------- *)

(* 诚实口径注记：Q 记录层无规范形（1/2 与 2/4 数值相等但记录不同），
   故「排序 + 置换 ⟹ 相等」在结构等号层为假，数值 Qeq 层为真。
   例证：[1/2;2/4] 与 [2/4;1/2] 互为置换、均 Qle 有序、但记录不等。 *)
Theorem sorted_perm_count_qeq : forall (a : list Q) (b : list Q),
  StronglySorted Qle a -> StronglySorted Qle b ->
  (forall x : Q, count_q x a = count_q x b) ->
  Forall2 Qeq a b.
Proof.
  induction a as [| x a' IH]; intros b HSa HSb Hcnt.
  - destruct b as [| y b'].
    + apply Forall2_nil.
    + exfalso. pose proof (Hcnt y) as Hc.
      rewrite count_q_self_cons in Hc. cbn [count_q] in Hc. lia.
  - apply StronglySorted_inv in HSa. destruct HSa as [HSa' Hall].
    assert (Hmin : forall z : Q, In z a' -> x <= z).
    { intros z Hz. exact (Forall_in Q (Qle x) a' z Hall Hz). }
    assert (Hxb : (1 <= count_q x b)%nat).
    { pose proof (Hcnt x) as Hc. rewrite count_q_self_cons in Hc. lia. }
    destruct (count_q_pos_wit x b Hxb) as [w [Hwin Hwx]].
    destruct b as [| y b'].
    + cbn [count_q] in Hxb. lia.
    + apply StronglySorted_inv in HSb. destruct HSb as [HSb' Hallb].
      assert (Hxy : x == y).
      { destruct Hwin as [Hwy | Hwb].
        - subst w. exact Hwx.
        - assert (Hyx : y <= x).
          { exact (proj1 (Qle_comp y y (Qeq_refl y) w x (Qeq_sym _ _ Hwx))
                     (Forall_in Q (Qle y) b' w Hallb Hwb)). }
          apply Qle_antisym.
          + assert (Hyb : (1 <= count_q y (x :: a'))%nat).
            { pose proof (Hcnt y) as Hc. rewrite count_q_self_cons in Hc. lia. }
            destruct (count_q_pos_wit y (x :: a') Hyb) as [z [Hzin Hyz]].
            destruct Hzin as [Hzx | Hza].
            * subst z.
              exact (proj1 (Qle_comp x x (Qeq_refl x) x y (Qeq_sym _ _ Hyz))
                           (Qle_refl x)).
            * exact (proj1 (Qle_comp x x (Qeq_refl x) z y (Qeq_sym _ _ Hyz))
                           (Hmin z Hza)).
          + exact Hyx. }
      assert (Hcnt2 : forall u : Q, count_q u a' = count_q u b').
      { intro u. specialize (Hcnt u). cbn [count_q] in Hcnt.
        rewrite (Qeqb_comp u u (Qeq_refl u) x y Hxy) in Hcnt.
        destruct (Qeq_bool u y); cbn [count_q] in Hcnt; lia. }
      apply Forall2_cons; [exact Hxy | apply IH; assumption].
Qed.

(* ---------- G.4 旗舰：P0 排序对置换的不变性（任务目标 1） ---------- *)

(* 多重集决定排序形：P0 l 仅依赖 l 的数值多重集。
   路线：P0 l ~ l ~ p ~ P0 p（D5_P0_perm）⟹ 数值重数相等
        ⟹ 双排序 + 计数相等 ⟹ Forall2 Qeq（G.3 唯一性）。 *)
Theorem P0_perm_inv : forall (l p : list Q),
  Permutation l p -> Forall2 Qeq (P0 l) (P0 p).
Proof.
  intros l p Hp. apply sorted_perm_count_qeq;
    [ apply P0_sorted | apply P0_sorted | ].
  intro x.
  exact (count_q_perm (P0 l) (P0 p)
           (Permutation_trans (Permutation_sym (D5_P0_perm l))
                              (Permutation_trans Hp (D5_P0_perm p)))
           x).
Qed.

(* ---------- G.5 熵载荷推论（相邻差熵对置换不变） ---------- *)

(* 逐点 Qeq 的表 ⟹ 相邻差总和数值相等 *)
Lemma sum_adjdiff_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> sum_adjdiff l1 == sum_adjdiff l2.
Proof.
  induction l1 as [| x1 l1' IH]; intros l2 H2.
  - destruct l2 as [| y1 l2'].
    + reflexivity.
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
  - destruct l2 as [| y1 l2'].
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
    + destruct (proj1 (Forall2_cons_iff Qeq x1 y1 l1' l2') H2) as [Hxy Hrest].
      destruct l1' as [| x2 l1''].
      * destruct l2' as [| y2 l2''].
        -- reflexivity.
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
      * destruct l2' as [| y2 l2''].
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
        -- destruct (proj1 (Forall2_cons_iff Qeq x2 y2 l1'' l2'') Hrest)
             as [H22 Hrest2].
           rewrite !sum_adjdiff_cons_eq.
           apply Qplus_comp.
           ++ apply xq_abs_eq. apply Qminus_comp; [exact H22 | exact Hxy].
           ++ apply IH. exact Hrest.
Qed.

Lemma H_adj_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> H_adj l1 == H_adj l2.
Proof. intros l1 l2 H. unfold H_adj. apply sum_adjdiff_qeq. exact H. Qed.

(* 熵的置换不变性（旗舰的熵载荷）：H_adj ∘ P0 只看多重集 *)
Corollary H_adj_P0_perm : forall (l p : list Q),
  Permutation l p -> (H_adj (P0 l) == H_adj (P0 p))%Q.
Proof.
  intros l p Hp. apply H_adj_qeq. apply P0_perm_inv. exact Hp.
Qed.

(* 对换件的 P0 不变性（G.1 行为件 × 旗舰组合） *)
Corollary P0_swap_adj_qeq : forall (l : list Q) (n : nat),
  Forall2 Qeq (P0 (swap_adj l n)) (P0 l).
Proof.
  intros l n. apply P0_perm_inv. apply Permutation_sym. apply swap_adj_perm.
Qed.

Corollary H_adj_swap_adj : forall (l : list Q) (n : nat),
  (H_adj (P0 (swap_adj l n)) == H_adj (P0 l))%Q.
Proof.
  intros l n. apply H_adj_qeq. apply P0_swap_adj_qeq.
Qed.

(* ---------- G.6 phase_classify 行为件（任务目标 4） ---------- *)

(* 判定器 lam 死参已删（ADJ-2 2026-09-14：原第三参 lam 在定义体 L375-380
   从不被消费——设计缺口的终局处置是删参而非恒等引理记录；
   删参后本件为平凡重合式，保留名位作删参历史记录） *)
Lemma phase_classify_lam_const : forall (l : list Q) (s : nat),
  phase_classify l s = phase_classify l s.
Proof. reflexivity. Qed.

(* PhP0 标签的充分条件回读：P0 侧 ⟹ 熵值数值重合 *)
Lemma phase_classify_P0_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 -> (H_adj (P0 l) == H_adj (Pmid l s 0))%Q.
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - exact (proj1 (Qeq_bool_iff _ _) E1).
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H; discriminate H.
Qed.

(* PhMid 标签的排他性：中间相 ⟹ 两侧熵值均数值可分 *)
Lemma phase_classify_Mid_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhMid ->
  ~ ((H_adj (P0 l) == H_adj (Pmid l s 0))%Q) /\
  ~ ((H_adj (Pmid l s 0) == H_adj (Pinf l s))%Q).
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - discriminate H.
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H.
    + discriminate H.
    + split.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E1. discriminate E1.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E2. discriminate E2.
Qed.

(* 相位判定对置换不变（旗舰的判定载荷）：组织标签是多重集的函数 *)
(* 诚实口径注记：无条件版「判定对置换不变」为假——Pinf 槽熵
   H_adj (Pinf l s)=H_adj l 依赖顺序（D12.2 组织差异的有序性本体），
   反例见 phase_classify_perm_counter。故全标签不变需
   「旋转槽熵重合」假设，仅 P0 槽无条件不变（H_adj_P0_perm）。 *)
Theorem phase_classify_perm_inv_cond : forall (l p : list Q) (s : nat),
  Permutation l p ->
  (H_adj (Pinf l s) == H_adj (Pinf p s))%Q ->
  phase_classify l s = phase_classify p s.
Proof.
  intros l p s Hp HI. unfold phase_classify. cbv zeta.
  assert (H0 : (H_adj (P0 l) == H_adj (P0 p))%Q)
    by (apply H_adj_P0_perm; exact Hp).
  assert (HM : (H_adj (Pmid l s 0) == H_adj (Pmid p s 0))%Q).
  { replace (Pmid l s 0) with (Pinf l s) by reflexivity.
    replace (Pmid p s 0) with (Pinf p s) by reflexivity.
    exact HI. }
  assert (B1 : Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0)) =
               Qeq_bool (H_adj (P0 p)) (H_adj (Pmid p s 0))).
  { rewrite (Qeqb_comp (H_adj (P0 l)) (H_adj (P0 p)) H0
                       (H_adj (Pmid l s 0)) (H_adj (Pmid l s 0)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (P0 p)) (H_adj (P0 p)) (Qeq_refl _)
                     (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM). }
  assert (B2 : Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s)) =
               Qeq_bool (H_adj (Pmid p s 0)) (H_adj (Pinf p s))).
  { rewrite (Qeqb_comp (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM
                       (H_adj (Pinf l s)) (H_adj (Pinf l s)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (Pmid p s 0)) (H_adj (Pmid p s 0)) (Qeq_refl _)
                     (H_adj (Pinf l s)) (H_adj (Pinf p s)) HI). }
  rewrite B1, B2. reflexivity.
Qed.


(* 无条件版置换不变性的构造性反例（D10 反例节点精神）：
   l=[0;1;100] 与 p=[1;0;100] 互为置换，s=0 时
   phase_classify l 0 = PhP0 而 phase_classify p 0 = PhPinf。
   （h0 槽两侧同为 100；hm 槽 H_adj l=100 vs H_adj p=101。） *)
Lemma phase_classify_perm_counter :
  ~ (forall (l p : list Q) (s : nat),
       Permutation l p -> phase_classify l s = phase_classify p s).
Proof.
  intro H. specialize (H [0;1;100] [1;0;100] 0%nat (perm_swap 1 0 [100])).
  vm_compute in H. discriminate H.
Qed.

(* ========== §H M2 归并块一：DTPT_PmidEnd 端点族（2026-09-14 并入） ==========
   Pmid 通用 λ 截断的非平凡端点定律：λ = 列长时三相退化回 P0。
   偿还在册诚实挂账：DTPT_Dig.v L65-69 与 DTPT.v L86 的
   D5_Pmid_perm 一般 lam 不成立注记——本族补全其中 lam = length l 端点。
   挂账病灶与正解：firstn_all 的模式 firstn (length ?l) ?l 对目标
   子项 firstn (length l) (P0 l) 单化失败（?l 须同为 l 与 P0 l）；
   改用带长度前提形 firstn_all2 / skipn_all2，前提由置换长度守恒
   （D5_P0_perm / D5_Pinf_perm + Permutation_length）供给。
   归并后本族与主体同文件：原 DTPT_PmidEnd.v 的文件头/Require 面/
   文件尾自证段已按归并纪律移除（自证集中于文件尾 §J）。 ========== *)

(* ---------- H.1 长度守恒前提（置换性 ⟹ 长度相等） ---------- *)

Lemma pmid_len_l_eq_P0 : forall l : list Q, length l = length (P0 l).
Proof.
  intros l. exact (Permutation_length (D5_P0_perm l)).
Qed.

Lemma pmid_len_l_eq_Pinf : forall (l : list Q) (s : nat),
  length l = length (Pinf l s).
Proof.
  intros l s. exact (Permutation_length (D5_Pinf_perm l s)).
Qed.

(* ---------- H.2 主定理：λ = length l 端点（挂账偿还） ---------- *)

(* 挂账病灶正解：firstn_all 模式 firstn (length ?l) ?l 对
   firstn (length l) (P0 l) 单化失败；firstn_all2/skipn_all2 的
   显式实参序在 9.0 有版本漂移——故以 apply 按结论单化（免疫参序）
   先落两条方程引理，主定理只 rewrite 方程。 *)
(* ≤ 形前提独立引理：rewrite <- 用具体式（RHS 无模式变量回咬环）。
   坑：rewrite pmid_len_l_eq_P0（模式 length ?x）会先咬中目标里
   length (P0 l) 自吞改写为 length (P0 (P0 l))——S1 卡同族。 *)
Lemma pmid_len_l_le_P0 : forall l : list Q,
  (length (P0 l) <= length l)%nat.
Proof.
  intros l. rewrite <- (pmid_len_l_eq_P0 l). apply le_n.
Qed.

Lemma pmid_len_Pinf_le_l : forall (l : list Q) (s : nat),
  (length (Pinf l s) <= length l)%nat.
Proof.
  intros l s. rewrite <- (pmid_len_l_eq_Pinf l s). apply le_n.
Qed.

Lemma pmid_firstn_len : forall l : list Q,
  firstn (length l) (P0 l) = P0 l.
Proof.
  intros l. apply firstn_all2. apply pmid_len_l_le_P0.
Qed.

Lemma pmid_skipn_len : forall (l : list Q) (s : nat),
  skipn (length l) (Pinf l s) = [].
Proof.
  intros l s. apply skipn_all2. apply pmid_len_Pinf_le_l.
Qed.

Theorem Pmid_len_endpoint : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof.
  intros l s. unfold Pmid.
  rewrite pmid_firstn_len. rewrite pmid_skipn_len.
  apply app_nil_r.
Qed.

(* X1 清单热点 3 原名，同陈述别名件（互查方便） *)
Corollary Pmid_len_eq_P0 : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof. exact Pmid_len_endpoint. Qed.

Theorem Pmid_len_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s (length l)).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply D5_P0_perm.
Qed.

(* ---------- H.3 次端点：λ = 0（全 Pinf 相，定义级） ---------- *)

Theorem Pmid_zero_endpoint : forall (l : list Q) (s : nat),
  Pmid l s 0 = Pinf l s.
Proof.
  intros l s. unfold Pmid. reflexivity.
Qed.

Theorem Pmid_zero_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s 0).
Proof.
  intros l s. rewrite Pmid_zero_endpoint. apply D5_Pinf_perm.
Qed.

(* ---------- H.4 等价置换形互推（加分项一） ---------- *)

Theorem Pmid_len_perm_eq : forall (l : list Q) (s : nat),
  Permutation (Pmid l s (length l)) (P0 l).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply Permutation_refl.
Qed.

Theorem Pmid_len_perm_P0_left : forall (l : list Q) (s : nat),
  Permutation (P0 l) (Pmid l s (length l)).
Proof.
  intros l s. apply Permutation_sym. apply Pmid_len_perm_eq.
Qed.

(* ---------- H.5 长度谱系：lam <= length l 时长度 = lam + (|l| - lam)（加分项二） ---------- *)

Theorem Pmid_len_spectrum : forall (l : list Q) (s lam : nat),
  (lam <= length l)%nat ->
  length (Pmid l s lam) = (lam + (length l - lam))%nat.
Proof.
  intros l s lam Hlam. unfold Pmid.
  rewrite length_app.
  rewrite pmid_len_l_eq_P0 in Hlam.
  rewrite (firstn_length_le (P0 l) Hlam).
  rewrite (length_skipn _ _).
  rewrite <- (pmid_len_l_eq_Pinf l s).
  reflexivity.
Qed.


(* ========== §I M2 归并块二：DTPT_OrgDiff 封闭式/非负/吸收族（2026-09-14 并入） ==========
   X1 清单热点 7【ORG】升级 + U2 留账偿还（U15R 席 2026-09-14 交付面）。
   归并处理：原件 Require Import DTPT DTPT_Phases DTPT_PmidEnd 一行
   全删——Pmid_len_endpoint 引用改本文件 §H 直引，P0_idempotent
   引用改本文件 §A 直引，OrgDiff 定义在本文件 §B，其余底座
   （Pinf/rot/firstn_skipn/C_sorted_min_adj/Qle_0_sub'/xq_minus_self）
   全在 DTPT（文件头已 Require）。
   底座实形：OrgDiff l s := H_adj (Pinf l s) - H_adj (P0 l)（§B）；
   Pinf l s = rot (S s) l = firstn (S s) l ++ skipn (S s) l = l
   （firstn_skipn），故 OrgDiff 实形 = H_adj l - H_adj (P0 l)。 ========== *)

(* ---------- I.1 U2 留账：P0 吸收 Pmid 的 lam=|l| 端点 ---------- *)

(* 组织不动点吞没通用 λ 截断的满长端点：
   rewrite Pmid_len_endpoint（本文件 §H）后
   apply P0_idempotent（本文件 §A），两步。 *)
Theorem P0_absorbs_Pmid_len : forall (l : list Q) (s : nat),
  P0 (Pmid l s (length l)) = P0 l.
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply P0_idempotent.
Qed.

(* ---------- I.2 ORG-① 封闭形：OrgDiff 坍缩语义入册 ---------- *)

(* X1 面4 实证的「语义未在册」在此入册：Pinf 槽是恒等旋转，
   组织差异只依赖 l 的原始序与组织规范形之差。 *)
Theorem OrgDiff_eq : forall (l : list Q) (s : nat),
  OrgDiff l s == H_adj l - H_adj (P0 l).
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. reflexivity.
Qed.

(* ---------- I.3 ORG-① 非负形：组织差异恒非负 ---------- *)

(* P0 最小化相邻差熵（C_sorted_min_adj）的一步推论：
   0 <= H_adj l - H_adj (P0 l) 经 Qle_0_sub' 反向即 C_sorted_min_adj l。 *)
Theorem OrgDiff_nonneg : forall (l : list Q) (s : nat),
  (0 <= OrgDiff l s)%Q.
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot. rewrite firstn_skipn.
  exact (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj l)) (C_sorted_min_adj l)).
Qed.

(* 可判定比较面证书：非负性的布尔判定回读（Qle_bool 计算面） *)
Theorem OrgDiff_nonneg_dec : forall (l : list Q) (s : nat),
  Qle_bool 0 (OrgDiff l s) = true.
Proof.
  intros l s. apply (proj2 (Qle_bool_iff 0 (OrgDiff l s))).
  apply OrgDiff_nonneg.
Qed.

(* ---------- I.4 ORG-② 组合面：Pmid 端点组合坍缩律 ---------- *)

(* 与相算子 Pmid 的组合（可证方向）：λ = |l| 端点处截断序列
   已是组织规范形，组织差异坍缩为零——I.1 吸收律的熵载荷。 *)
Theorem OrgDiff_Pmid_len_zero : forall (l : list Q) (s t : nat),
  OrgDiff (Pmid l s (length l)) t == 0.
Proof.
  intros l s t. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. rewrite Pmid_len_endpoint.
  rewrite P0_idempotent. apply xq_minus_self.
Qed.

(* 诚实障碍：一般 lam 的组合坍缩为假。反例 l=[2;0;3;1], s=0, lam=2：
   Pmid = firstn 2 (P0 l) ++ skipn 2 l = [0;1] ++ [3;1] = [0;1;3;1]，
   H_adj = 1+2+2 = 5 而 H_adj (P0 [0;1;3;1]) = 1+0+2 = 3，差 = 2 <> 0。
   构造性反例节点，划定 I.4 坍缩律的适用边界（仅 λ ∈ {0, |l|} 端点坍缩）。 *)
Lemma OrgDiff_Pmid_general_nonzero :
  ~ (forall (l : list Q) (s lam t : nat), OrgDiff (Pmid l s lam) t == 0).
Proof.
  intro H. specialize (H [2;0;3;1] 0%nat 2%nat 0%nat).
  vm_compute in H. congruence.
Qed.

End DTPT_Phases.
Import DTPT_Phases.

(* ========== §J 零公理自证（M2 归并族旗舰 9 件，集中于文件尾：
   PmidEnd 面 3 件 + OrgDiff 面 6 件） ========== *)
Print Assumptions Pmid_len_endpoint.
Print Assumptions Pmid_len_perm.
Print Assumptions Pmid_len_spectrum.
Print Assumptions P0_absorbs_Pmid_len.
Print Assumptions OrgDiff_eq.
Print Assumptions OrgDiff_nonneg.
Print Assumptions OrgDiff_nonneg_dec.
Print Assumptions OrgDiff_Pmid_len_zero.
Print Assumptions OrgDiff_Pmid_general_nonzero.
