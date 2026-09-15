(* ============================================================
   DTPT_ZeroLocus.v — 零点刻画席 U4（热点升级单 X2-2，X2 扫描 Top-2）
   职责：占位「质心偏移」香农偏差熵 H_devsum（DTPT_Entropy.v，
         逐项 |x - 后缀 P0 最小| 之和）的零点集结构刻画：
         零点 ⟺ 升序表（SortedQ）；内容分级：
         旗舰  H_shannon_q_zero_iff_sorted（正向 = 盘上
               xq_H_shannon_sortQ；反向本席新证：和零 + 双项非负
               ⟹ 逐项零 ⟹ 首元 == 后缀 P0 最小 ⟹ 升序 cons，
               配 hd 最小性新引理 xqz_sorted_hd_min）
         主件A H_ms1_all_eq / H_ms1_iff_const（H_ms == 1 全同值
               刻画；诚实口径：空表 H_ms [] == 0 而「全成员同值」
               空真，故 iff 右侧带 l <> [] 守卫——对 X2-2 草式的
               必要修正）
         主件B H_cond_nonneg_iff / H_cond_abs_bound / H_cond_zero_iff
               （绝对值界：|H_cond| <= H_devsum l + H_devsum ctx）
         加分  H_shannon_q_perm_inv_if_sorted（反例①的 restricted
               正形：双侧升序时置换不变成立）、zero_locus_joint
               （反例③的正面孪生：双零点 ⟺ 非空常值表）、
               zero_locus_contrast_sorted_not_const（[1;2] 对照锚）
   依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、
         DTPT（D5_P0_perm / dedup 系 / Qmem 系 / qadd_le /
         Qle_0_sub' / Qeqb_true_of）、DTPT_Entropy（xq_H_shannon_sortQ、
         xq_Zlen_inj1、xq_len1_el、xq_dedup1_all_eq、
         H_shannon_q_const_zero、H_shannon_q_nonneg）。
   归并记录：无（原生成模块）。
   认证：零承认零公理；全树 coqchk EXIT=0（2026-09-14）。
   纪律：纯构造性；四关收割；温控协议；新名一律 xqz_ 前缀防撞名；
         nat 全显式 %nat；Qeq 口径显式搬运（Qeq_trans/Qeq_sym
         值参显式位）；全部声明以 Qed 封口。
   附注：与 S6 真频率熵的对照定位——占位熵 H_devsum 零点可含
         相异值（[1;2] 是零点但非常值），真频率熵 H_freq 零点必为
         常值表；对照锚 zero_locus_contrast_sorted_not_const 给出
         可执行见证，S6 落盘后可经 Require 直接拼装双向对照引理
         （首期不做）；本件不定义任何频率/对数对象，S5 测度面零接触。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.
Require DTPT.
Require DTPT_Entropy.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_ZeroLocus.

(* ========== §1 工具：绝对值零点、减法零点、非负和零分解 ========== *)

(* Qabs x == 0 -> x == 0（对 Qnum 三分直解，stdlib 无 Qeq 形现成件） *)
Lemma xqz_abs0_eq : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* x - y == 0 -> x == y（Qle_0_sub' 双向 + 反对称，零 setoid 重写） *)
Lemma xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> x == y.
Proof.
  intros x y H.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by apply xq_minus_opp.
    rewrite Hmo, H. reflexivity. }
  apply (xq_Qle_antisym x y).
  - apply (proj2 (Qle_0_sub' x y)).
    apply xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply (proj2 (Qle_0_sub' y x)).
    apply xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* 非负两项和为零 ⟹ 首项为零（a <= a+b == 0 与 0 <= a 夹挤） *)
Lemma xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0.
Proof.
  intros a b Hab Ha Hb.
  assert (Hle : (a + 0 <= a + b)%Q)
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  rewrite Qplus_0_r in Hle. rewrite Hab in Hle.
  apply (xq_Qle_antisym a 0 Hle Ha).
Qed.

(* 非负两项和为零 ⟹ 两项皆零（交换后复用） *)
Lemma xqz_plus_eq0 : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0 /\ b == 0.
Proof.
  intros a b Hab Ha Hb. split.
  - apply (xqz_plus_eq0_le a b Hab Ha Hb).
  - rewrite Qplus_comm in Hab.
    apply (xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* ========== §2 旗舰：H_devsum 零点集 = 升序表 ========== *)

(* hd 最小性：升序表的首元不超过表内任何成员 *)
Lemma xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> (hd 0 l <= z)%Q.
Proof.
  intros [| a rest] z HS Hin.
  - destruct Hin.
  - inversion HS as [| c1 c2 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (hd 0 (a :: rest)) with a.
    destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + apply HFa. exact Hin.
Qed.

(* P0 规范形的首元是全表下界（经置换搬运成员性） *)
Lemma xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> (hd 0 (P0 l) <= z)%Q.
Proof.
  intros l z Hin.
  apply (xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* 旗舰反向：占位熵零 ⟹ 升序（逐层剥 |首差| + 归纳） *)
Theorem H_shannon_q_zero_sorted : forall l : list Q,
  H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [H_devsum] in H.
    destruct (xqz_plus_eq0
                (Qabs (x - hd 0 (P0 (x :: xs)))) (H_devsum xs) H
                (abs_nonneg (x - hd 0 (P0 (x :: xs))))
                (H_shannon_q_nonneg xs)) as [Ha Hs].
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply xqz_sub_eq0. apply xqz_abs0_eq. exact Ha. }
    apply sortQ_cons.
    + apply IH. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply xq_Qeq_le. exact Hxm.
      * apply xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* 旗舰：占位香农偏差熵的零点集 = 升序表
   （正向 = 盘上 xq_H_shannon_sortQ；对照 S6 真频率熵零点 = 常值表） *)
Theorem H_shannon_q_zero_iff_sorted : forall l : list Q,
  H_devsum l == 0 <-> SortedQ l.
Proof.
  intro l. split.
  - apply H_shannon_q_zero_sorted.
  - apply xq_H_shannon_sortQ.
Qed.

(* 对照锚（可执行）：[1;2] 升序且是占位熵零点，但非常值表
   ——「占位熵零点 ≠ 真香农零点」的构造性见证（S6 对照面） *)
Theorem zero_locus_contrast_sorted_not_const :
  SortedQ [1; 2] /\ H_devsum [1; 2] == 0
  /\ ~ (exists a : Q, Forall (fun z => z == a) [1; 2]).
Proof.
  split.
  - apply (sortQ_cons 1 [2]).
    + apply (sortQ_cons 2 []).
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_cons; [ unfold Qle; simpl; lia | apply Forall_nil ].
  - split.
    + vm_compute. reflexivity.
    + intros [a Hfa].
      inversion Hfa as [| z1 zs1 Hz1 Hf1]; subst.
      inversion Hf1 as [| z2 zs2 Hz2 Hf2]; subst.
      assert (H12 : (1 == 2)%Q)
        by (apply (Qeq_trans 1 a 2 Hz1 (Qeq_sym 2 a Hz2))).
      vm_compute in H12. discriminate H12.
Qed.

(* ========== §3 主件A：H_ms == 1 的全同值刻画 ========== *)

(* dedup_aux 消元：成员全同值于 x 时收空（Qmem 口径，不经 In） *)
Lemma xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> dedup_aux x m = [].
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall.
  - reflexivity.
  - cbn [dedup_aux].
    assert (Hxy : Qeq_bool x y = true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    rewrite Hxy. apply IH.
    intros z Hz. apply Hall. rewrite Qmem_cons. right. exact Hz.
Qed.

(* 全等刻画：H_ms l == 1 ⟹ 任意两成员 Qeq 同值
   （dedup 长度 1 + dedup_Qmem_r 结构，零 In 依赖） *)
Theorem H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> a == b.
Proof.
  intro l. intro H. unfold H_ms in H.
  apply xq_Zlen_inj1 in H.
  destruct (xq_len1_el (dedup l) H) as [c Hc].
  intros a b Ha Hb.
  assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
  assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
  rewrite Hc in Qa. rewrite Hc in Qb.
  rewrite Qmem_cons in Qa. rewrite Qmem_cons in Qb.
  destruct Qa as [Qa | Qa]; [ | unfold Qmem in Qa; simpl in Qa;
                             discriminate Qa ].
  destruct Qb as [Qb | Qb]; [ | unfold Qmem in Qb; simpl in Qb;
                             discriminate Qb ].
  rewrite (Qeqb_sym b c) in Qb.
  apply Qeq_bool_eq. apply (Qeqb_trans a c b Qa Qb).
Qed.

(* 主件A：H_ms == 1 ⟺ 非空且全成员 Qeq 同值（exists-Forall 形） *)
Theorem H_ms1_iff_const : forall l : list Q,
  (H_ms l == 1)%Q <-> (l <> [] /\ exists a : Q, Forall (fun z => z == a) l).
Proof.
  intro l. split.
  - intro H.
    assert (Hlen : length (dedup l) = 1%nat)
      by (unfold H_ms in H; apply xq_Zlen_inj1; exact H).
    destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
    split.
    + intro He. rewrite He in Hc. simpl in Hc. discriminate Hc.
    + exists c. apply (xq_dedup1_all_eq l c Hc).
  - intros [Hne [a Hfa]].
    destruct l as [| x xs]; [ exfalso; apply Hne; reflexivity | ].
    inversion Hfa as [| z0 zs Hzx Hfxs]; subst.
    assert (Hd : dedup_aux x (dedup xs) = []).
    { rewrite Forall_forall in Hfxs.
      apply xqz_dedup_aux_nil. intros z Hz.
      assert (Qxs : Qmem z xs) by (apply (dedup_Qmem_l xs z); exact Hz).
      unfold Qmem in Qxs. apply existsb_exists in Qxs.
      destruct Qxs as [w [Hw Hzw]].
      apply (Qeq_trans x a z Hzx).
      apply (Qeq_sym z a).
      apply (Qeq_trans z w a (Qeq_bool_eq z w Hzw) (Hfxs w Hw)). }
    unfold H_ms. cbn [dedup]. rewrite Hd. reflexivity.
Qed.

(* ========== §4 主件B：H_cond 面（非负 iff + 绝对值界 + 零点 iff） ========== *)

(* 反例②（无条件非负为假）的精确 iff 化：缺失前提恰为
   H_devsum ctx <= H_devsum l（盘上 H_cond_nonneg_guarded 的
   双向强化） *)
Theorem H_cond_nonneg_iff : forall l ctx : list Q,
  (0 <= H_cond l ctx)%Q <-> (H_devsum ctx <= H_devsum l)%Q.
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply (proj2 (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
  - intro H. apply (proj1 (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
Qed.

(* 绝对值界（Qabs_triangle）：|H_cond l ctx| <= H_devsum l + H_devsum ctx
   （两熵皆非负，三角和即保守上界；按 H_cond 定义实形选形，无生造） *)
Theorem H_cond_abs_bound : forall l ctx : list Q,
  Qabs (H_cond l ctx) <= (H_devsum l + H_devsum ctx)%Q.
Proof.
  intros l ctx. unfold H_cond, Qminus.
  apply (Qle_trans _ (Qabs (H_devsum l) + Qabs (- H_devsum ctx))).
  - apply Qabs_triangle.
  - rewrite (xq_abs_id (H_devsum l) (H_shannon_q_nonneg l)).
    rewrite (xq_abs_opp (H_devsum ctx)).
    rewrite (xq_abs_id (H_devsum ctx) (H_shannon_q_nonneg ctx)).
    apply Qle_refl.
Qed.

(* 条件熵零点：H_cond l ctx == 0 ⟺ 两占位熵相等 *)
Theorem H_cond_zero_iff : forall l ctx : list Q,
  H_cond l ctx == 0 <-> (H_devsum l == H_devsum ctx)%Q.
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply xqz_sub_eq0. exact H.
  - intro H. rewrite H. apply xq_minus_self.
Qed.

(* ========== §5 加分：反例正化收尾 ========== *)

(* 反例①的 restricted 正形：置换不变在「双侧升序」前提恰成立
   （反例 [3;1;2] vs [2;1;3] 的病根 = 置换破坏升序性） *)
Theorem H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> H_devsum l == H_devsum p.
Proof.
  intros l p _Hp Hl Hpp.
  rewrite (xq_H_shannon_sortQ l Hl).
  rewrite (xq_H_shannon_sortQ p Hpp).
  reflexivity.
Qed.

(* 反例③的正面孪生：双零点（占位熵零 ∧ 多重集熵 1）⟺ 非空常值表
   （联合零点；⟸ 向组装 H_shannon_q_const_zero + H_ms1_iff_const） *)
Theorem zero_locus_joint : forall l : list Q,
  (H_devsum l == 0 /\ H_ms l == 1)%Q
  <-> (l <> [] /\ exists a : Q, Forall (fun z => z == a) l).
Proof.
  intro l. split.
  - intros [Hh Hm]. exact (proj1 (H_ms1_iff_const l) Hm).
  - intros [Hne [a Hfa]]. split.
    + apply (H_shannon_q_const_zero a l Hfa).
    + apply (proj2 (H_ms1_iff_const l)). split.
      * exact Hne.
      * exists a. exact Hfa.
Qed.

End DTPT_ZeroLocus.
Import DTPT_ZeroLocus.

(* ========== 零承认核验（G4：编译日志应为 Closed under the global context） ========== *)

Print Assumptions H_shannon_q_zero_iff_sorted.
Print Assumptions H_ms1_iff_const.
Print Assumptions H_cond_abs_bound.
Print Assumptions zero_locus_joint.
