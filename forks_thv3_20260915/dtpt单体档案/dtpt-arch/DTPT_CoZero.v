(* ============================================================
   DTPT_CoZero.v — 余零理想 ℐ 计数化（席 DTPT-U10 · 缺口单 COZIDEAL）
   原典对照：数字全域—熵相三元论·基座.txt §2.5 定义 2.5.3（行 219-226）：
     「若无法定义测度，则用余零理想 ℐ 表达：P_0, P_∞ ∈ ℐ, P_mid ∉ ℐ，
       其中 ℐ 可理解为『在适当意义下可忽略的边界集合』。」
   计数化口径（全 Set 层有限世界 w : list Q）：
     · 区域   = w 的子表（保序抽取，重数忠实）；
     · 可观测量 = φ : Q -> Q，以 Qeq_bool 判零；
     · 零点区域 fiber φ w = filter (fun x => Qeq_bool (φ x) 0) w；
     · 理想 ℐ_w = { fiber φ w : φ 为可观测量 }，即「可忽略集」的计数化。
   理想公理面（本件定理对应）：
     · 空区域 ∈ ℐ（fiber 常一）；全域 ∈ ℐ（fiber 常零）；
     · 并封闭（旗舰）：fiber (φ·ψ) 与 fiber φ ∪ fiber ψ 元素一致
       ——承重件 = Q 无零因子（a·b == 0 ⟺ a == 0 ∨ b == 0，Z 层直解）；
     · 交封闭（主件）：fiber (φ²+ψ²) 与 fiber φ ∩ fiber ψ 元素一致
       ——承重件 = Q 平方非负（Z 层三分直解）+ 平方和零序夹挤；
     · 子集封闭（主件）：w 的任一子表经指示零函数直构入 ℐ。
   余零面（加分）：cozero φ w = filter (negb (Qeq_bool (φ x) 0)) w，
     与 fiber 构成元素级互补（长度和 = 表长、互斥、覆盖）。
   成员口径声明：区域成员一律取记录级 In（stdlib List）。
     值级 Qeq 口径对任意 φ 不保零点（非外延 φ 反例：φ 读 Qnum 低位），
     故 fiber 成员刻画必须用 In——这正合 filter_In 的语义，非降档。
   依赖：DTPT（qadd_le / Qle_0_sub' 系 + Open Q_scope）；stdlib QArith/List。
   纪律：零公理零承认；nat 全显式 %nat；全程 Qed 收口。
   ============================================================ *)

Require DTPT.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
Import ListNotations.
Import DTPT.DTPT.

Module DTPT_CoZero.

(* ========== §1 Q 代数承重件：零因子 / 平方 / 平方和 ========== *)

(* Qeq→Qle 桥（stdlib 9.0 无 Qeq_le：Qeq 展开后两侧即 Qle 展开的同项） *)
Lemma qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* Q 无零因子·正向分解（Z 层 Z.mul_eq_0 两段收口） *)
Lemma qmul_eq0_fwd : forall a b : Q, (a * b == 0)%Q -> a == 0 \/ b == 0.
Proof.
  intros [an ad] [bn bd] H.
  unfold Qmult, Qeq in H; simpl in H.
  repeat rewrite Z.mul_1_r in H.
  apply Z.mul_eq_0 in H.
  destruct H as [H|H]; [left|right]; unfold Qeq; simpl; lia.
Qed.

(* 零因子进入（左/右） *)
Lemma qmul_eq0_intro_l : forall a b : Q, a == 0 -> (a * b == 0)%Q.
Proof.
  intros [an ad] b Hab. unfold Qeq in Hab; simpl in Hab.
  assert (Han : (an = 0)%Z) by lia.
  destruct b as [bn bd]. unfold Qmult, Qeq; simpl.
  rewrite Han. reflexivity.
Qed.

Lemma qmul_eq0_intro_r : forall a b : Q, b == 0 -> (a * b == 0)%Q.
Proof.
  intros a [bn bd] Hbb. unfold Qeq in Hbb; simpl in Hbb.
  assert (Hbn : (bn = 0)%Z) by lia.
  destruct a as [an ad]. unfold Qmult, Qeq; simpl.
  rewrite Hbn. lia.
Qed.

(* 零因子刻画（并封闭的承重件） *)
Lemma qmul_eq0_iff : forall a b : Q, (a * b == 0)%Q <-> (a == 0 \/ b == 0).
Proof.
  intros a b. split.
  - apply qmul_eq0_fwd.
  - intros [H|H]; [apply qmul_eq0_intro_l | apply qmul_eq0_intro_r]; exact H.
Qed.

(* Q 平方非负（Z 层 Znum 三分：Z0/Zpos/Zneg 皆平方非负） *)
Lemma qsq_nonneg : forall x : Q, (0 <= x * x)%Q.
Proof.
  intros [xn xd]. unfold Qmult, Qle. simpl.
  destruct xn as [| p | p]; simpl; lia.
Qed.

(* 平方零 ⟹ 因子零 *)
Lemma qsq_eq0 : forall x : Q, (x * x == 0)%Q -> x == 0.
Proof.
  intros x H. destruct (qmul_eq0_fwd x x H) as [Hx|Hx]; exact Hx.
Qed.

(* 平方和零 ⟹ 两因子零（序夹挤：0 <= a² <= a²+b² == 0，反对称收口） *)
Lemma qsum_sq_zero : forall a b : Q, (a * a + b * b == 0)%Q -> a == 0 /\ b == 0.
Proof.
  intros a b Hsum.
  assert (Hs1 : (a * a <= a * a + b * b)%Q).
  { assert (Hs0 : (a * a + 0 <= a * a + b * b)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle1 : (a * a <= 0)%Q)
    by (apply (Qle_trans (a * a) (a * a + b * b) 0);
        [exact Hs1 | apply qeq_le; exact Hsum]).
  assert (Hs2 : (b * b <= b * b + a * a)%Q).
  { assert (Hs0 : (b * b + 0 <= b * b + a * a)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle2 : (b * b <= 0)%Q)
    by (apply (Qle_trans (b * b) (b * b + a * a) 0);
        [exact Hs2 | apply qeq_le; apply Qeq_trans with (a * a + b * b);
         [apply Qplus_comm | exact Hsum]]).
  assert (Hz1 : (a * a == 0)%Q) by (apply Qle_antisym; [exact Hle1 | apply qsq_nonneg]).
  assert (Hz2 : (b * b == 0)%Q) by (apply Qle_antisym; [exact Hle2 | apply qsq_nonneg]).
  split.
  - apply qsq_eq0; exact Hz1.
  - apply qsq_eq0; exact Hz2.
Qed.

(* 反向构造：两因子零 ⟹ 平方和零 *)
Lemma qsum_sq_zero_intro : forall a b : Q,
  a == 0 -> b == 0 -> (a * a + b * b == 0)%Q.
Proof.
  intros a b Ha Hb.
  assert (Haa : (a * a == 0)%Q) by (apply qmul_eq0_intro_l; exact Ha).
  assert (Hbb : (b * b == 0)%Q) by (apply qmul_eq0_intro_l; exact Hb).
  destruct a as [an ad]; destruct b as [bn bd].
  unfold Qeq in Haa, Hbb; simpl in Haa, Hbb.
  assert (Han : (an = 0)%Z) by lia.
  assert (Hbn : (bn = 0)%Z) by lia.
  unfold Qmult, Qplus, Qeq; simpl.
  rewrite Han, Hbn. reflexivity.
Qed.

(* 判零布尔面：乘积可观测量归零 ⟺ 有一因子归零（并封闭键） *)
Lemma qmul_fiber_key : forall p q : Q,
  Qeq_bool (p * q) 0 = true <-> (Qeq_bool p 0 = true \/ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qmul_eq0_iff in Hb.
    destruct Hb as [H|H]; [left|right]; apply Qeqb_true_of; exact H.
  - intros [Hb|Hb]; apply Qeq_bool_iff; apply qmul_eq0_iff;
      [left|right]; apply Qeq_bool_iff; exact Hb.
Qed.

(* 判零布尔面：平方和可观测量归零 ⟺ 两因子各归零（交封闭键） *)
Lemma qsum_sq_fiber_key : forall p q : Q,
  Qeq_bool (p * p + q * q) 0 = true <-> (Qeq_bool p 0 = true /\ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qsum_sq_zero in Hb.
    destruct Hb as [H1 H2]; split; apply Qeqb_true_of; assumption.
  - intros [Hp Hq]. apply Qeq_bool_iff. apply qsum_sq_zero_intro.
    + apply Qeq_bool_iff; exact Hp.
    + apply Qeq_bool_iff; exact Hq.
Qed.

(* ========== §2 零点区域 fiber 与余零区域 cozero ========== *)

(* 零点区域：w 中使可观测量归零的元素之保序子表 *)
Definition fiber (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => Qeq_bool (f x) 0) w.

(* 余零区域：w 中使可观测量非零的元素之保序子表（fiber 的补面） *)
Definition cozero (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => negb (Qeq_bool (f x) 0)) w.

(* 成员刻画（记录级 In 口径，经 filter_In 显式项收口——HO-unify 免疫） *)
Lemma fiber_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) <-> (In x w /\ Qeq_bool (f x) 0 = true).
Proof.
  intros f w x. unfold fiber.
  exact (filter_In (fun y : Q => Qeq_bool (f y) 0) x w).
Qed.

Lemma cozero_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (cozero f w) <-> (In x w /\ Qeq_bool (f x) 0 = false).
Proof.
  intros f w x. unfold cozero.
  rewrite (filter_In (fun y : Q => negb (Qeq_bool (f y) 0)) x w).
  split.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
Qed.

(* ========== §3 旗舰·并封闭：乘积可观测量分解为零因子之并 ========== *)

(* 原典语义：可忽略集对有限并封闭——零点语言下即
   fiber (φ·ψ) w = fiber φ w ∪ fiber ψ w（元素级一致），
   承重件 = Q 无零因子 qmul_eq0_iff。 *)
Theorem fiber_mul_union : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * g y) w) <-> (In x (fiber f w) \/ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qmul_fiber_key in Hb.
    destruct Hb as [H|H]; [left|right]; split; assumption.
  - intros [Hp|Hp].
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. left. exact (proj2 Hp).
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. right. exact (proj2 Hp).
Qed.

(* ========== §4 主件·交封闭：平方和可观测量分解为零因子之交 ========== *)

(* 原典语义：可忽略集对有限交封闭——零点语言下即
   fiber (φ²+ψ²) w = fiber φ w ∩ fiber g ψ w（元素级一致），
   承重件 = Q 平方非负 + 平方和零序夹挤 qsum_sq_zero。 *)
Theorem fiber_sumsq_inter : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * f y + g y * g y) w)
  <-> (In x (fiber f w) /\ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qsum_sq_fiber_key in Hb.
    destruct Hb as [H1 H2]; split; split; assumption.
  - intros [[Hin H1] [_ H2]]. split; [exact Hin|].
    apply qsum_sq_fiber_key. split; assumption.
Qed.

(* ========== §5 理想公理面：空域 / 全域 / 子集封闭 ========== *)

(* 空区域 ∈ ℐ：常一可观测量处处非零，零点区域为空 *)
Theorem fiber_one_empty : forall w : list Q,
  fiber (fun _ : Q => 1) w = [].
Proof.
  induction w as [| a t IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* 全域 ∈ ℐ：常零可观测量处处归零，零点区域为全表
   （ℐ 吞全域的退化面；理想之为「真理想」的排除项见原典 P_mid ∉ ℐ） *)
Theorem fiber_zero_full : forall w : list Q,
  fiber (fun _ : Q => 0) w = w.
Proof.
  induction w as [| a t IH].
  - reflexivity.
  - unfold fiber in *. simpl in *. rewrite IH. reflexivity.
Qed.

(* Q 的 Leibniz 判等器：Q 是 Z×positive 记录，in_dec 需 Leibniz 形判等
   （stdlib Qeq_dec 是 Qeq 形，喂 in_dec 类型不通；Qeq 布尔成员判又与
   记录级 In 不合——0#1 ≠ 0#2 项级——故自建直构，零公理） *)
Definition Q_dec : forall x y : Q, {x = y} + {x <> y}.
Proof.
  intros [an ad] [bn bd].
  destruct (Z.eq_dec an bn) as [Hn|Hn]; destruct (positive_eq_dec ad bd) as [Hd|Hd].
  - left. rewrite Hn, Hd. reflexivity.
  - right. intros He. apply Hd. congruence.
  - right. intros He. apply Hn. congruence.
  - right. intros He. apply Hd. congruence.
Defined.

(* 指示函数点态刻画：χ_l x = 0 ⟺ x ∈ l（Leibniz 记录级口径） *)
Lemma chi_spec : forall (l : list Q) (x : Q),
  Qeq_bool (if in_dec Q_dec x l then 0 else 1) 0 = true <-> In x l.
Proof.
  intros l x. destruct (in_dec Q_dec x l) as [Hi|Hni].
  - split; [intros _; exact Hi | intros _; reflexivity].
  - split.
    + intro Hb. vm_compute in Hb. discriminate.
    + intro Hi. exfalso. apply Hni. exact Hi.
Qed.

(* 指示零函数：w 的任一子表 l 经 χ_l := 「y ∈ l 则 0 否则 1」直构为 fiber，
   ——子集封闭的直构面（成员级，记录级 In 双向） *)
Lemma fiber_indicator : forall (l w : list Q) (x : Q),
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w)
  <-> (In x w /\ In x l).
Proof.
  intros l w x. rewrite fiber_in. cbv beta. rewrite chi_spec.
  split; intros H; exact H.
Qed.

(* 子集封闭（理想第二公理）：l ⊆ fiber φ w ⟹ l 经指示零函数入 ℐ
   ——原典 P_0, P_∞ ∈ ℐ 的承载面：任一边界相区域皆某可观测量的零点子区域 *)
Theorem ideal_sub_closed : forall (l : list Q) (f : Q -> Q) (w : list Q) (x : Q),
  (forall y : Q, In y l -> In y (fiber f w)) ->
  In x l ->
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w).
Proof.
  intros l f w x Hsub Hxl. apply fiber_indicator. split.
  - exact (proj1 (proj1 (fiber_in f w x) (Hsub x Hxl))).
  - exact Hxl.
Qed.

(* ========== §6 余零面：cozero 与 fiber 的元素级互补 ========== *)

(* 长度和 = 表长（重数忠实二分） *)
Theorem fiber_cozero_length : forall (f : Q -> Q) (w : list Q),
  (length (fiber f w) + length (cozero f w))%nat = length w.
Proof.
  intros f w. unfold fiber, cozero.
  induction w as [| a t IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool (f a) 0); simpl; lia.
Qed.

(* 互斥：零点区域与余零区域无公共元素 *)
Theorem fiber_cozero_disjoint : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> ~ In x (cozero f w).
Proof.
  intros f w x H1 H2.
  apply fiber_in in H1. apply cozero_in in H2.
  destruct H1 as [_ Hb1]. destruct H2 as [_ Hb2].
  rewrite Hb1 in Hb2. discriminate.
Qed.

(* 覆盖：世界内任一元素必居两侧之一 *)
Theorem fiber_cozero_cover : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) \/ In x (cozero f w)).
Proof.
  intros f w x Hw.
  destruct (Qeq_bool (f x) 0) eqn:Ef.
  - left. apply fiber_in. split; assumption.
  - right. apply cozero_in. split; assumption.
Qed.

(* 补面刻画：世界内 x 落零点区域 ⟺ 不落余零区域（元素级二分） *)
Theorem fiber_cozero_compl : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) <-> ~ In x (cozero f w)).
Proof.
  intros f w x Hw. split.
  - intros H1 Hc. exact (fiber_cozero_disjoint f w x H1 Hc).
  - intros Hn. apply (fiber_cozero_cover f w x) in Hw.
    destruct Hw as [H|H]; [exact H | exfalso; apply Hn; exact H].
Qed.

End DTPT_CoZero.
Import DTPT_CoZero.

(* ========== §7 终验：Print Assumptions（G4 关） ========== *)

Print Assumptions fiber_mul_union.
Print Assumptions fiber_sumsq_inter.
Print Assumptions ideal_sub_closed.
Print Assumptions fiber_cozero_compl.
Print Assumptions fiber_cozero_length.
