(* ===================================================================== *)
(*  u5c_ln2_theta_slot.v —— ln2 供给链 ⑥θⁿ 上界内容位（θ:=4/5 规范预算桥）   *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_theta_slot。                                          *)
(*  使命：铸造装配件 u5c_ln2_assembly 第六节肢（θⁿ 上界位）的内容件——       *)
(*    「线对象 |A_n·X − B_n| ≤ (4/5)ⁿ」的实数面不等式族。数学核：           *)
(*    · 内容定义面——线面义务形 u5c_ln2_theta_slot（定义性复用乙件           *)
(*      u5c_ln2b_line_upper，θ 取装配规范值 u5c_lna_theta_mod=4/5）与       *)
(*      真族载体面义务形 u5c_ln2_theta_slot_face（与装配残面第六节肢         *)
(*      语句逐字同形）；                                                   *)
(*    · θ<1 带宽常数的 Q 层构造性承载——预算折叠恒等式                       *)
(*      4ⁿ·(7/40)ⁿ == (7/10)ⁿ 与带宽比较 (7/10)ⁿ ≤ (4/5)ⁿ 的自足证明       *)
(*      （幂乘法则＋幂底单调＋有理数乘法保序，纯 Q 零假设）；                *)
(*    · 预算桥义务定理——若线对象已被实数面预算 4ⁿ·(7/40)ⁿ 约束             *)
(*      （有理预算面供给），则经实数常值序提升与传递即得 4/5 带宽上界，      *)
(*      线面桥 u5c_ln2_theta_slot_of_budget 与真族载体面桥                  *)
(*      u5c_ln2_theta_slot_face_of_budget（后者沿 real_eq 缝迁移，          *)
(*      为装配第六节肢的直接代入入口）。                                    *)
(*  实现注记：实数常值序提升经 Qlt_le_dec 可判定劈分（严格面走 eps:=(b−a)/2  *)
(*    显式配方，相等面走常值实数相等）；Qle 沿 Qeq 的左/右迁移走 Prop 面     *)
(*    传递桥，免 setoid。                                                   *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                      *)
(*    u5c_ln2_gap2_bridge（线对象/上界义务面/real_eq 缝迁移件）、            *)
(*    u5c_ln2_assembly（θ 规范值 u5c_lna_theta_mod）；                      *)
(*    Stdlib：QArith/Qabs/ZArith/Arith/Lia。                                *)
(*  对标：abl_ln2_assembly2.v:370 lnb3_theta_slot（本件内容的规格原型）；    *)
(*    abl_ln2_theta_rehook.v §② lnr2_rem_upper_of_budget（预算面接入桥的    *)
(*    同构原型）；abl_ln2_theta_upper.v lnt2_theta_budget（(7/10)ⁿ ≤ (4/5)ⁿ  *)
(*    预算的原型；本件 Q 层承载自足重证，不依赖树件）。                      *)
(*  构造性注记：语句面全 Set 层（sigT/And/Or/real_lt/real_le/real_eq/        *)
(*    QeqT/QleT'/QltT）；幂定律与预算比较为归纳＋有理乘法保序的实质推导链；   *)
(*    θ<1 带宽常数 4/5<1 已由装配件取定为规范值。零承认、零公理；             *)
(*    文尾 Separate Extraction 与 Print Assumptions 全列。                   *)
(*  诚实边界：义务定理的前提——「线对象 ≤ 4ⁿ·(7/40)ⁿ 的实数面预算供给」——     *)
(*    即本位显式前提（GAPASUME-⑥）：∀n, real_le (u5c_ln2b_line X A B n)     *)
(*    (real_const (q_pow (4#1) n * q_pow (7#40) n))。其内容=「规范线对象     *)
(*    等于归一化积分常数倍」这一恒等式的实数面供给（S6 恒等式肢到货形），     *)
(*    依赖卷积恒等式内容位（真族级数和与规范线对象的实数相等，                *)
(*    即 abl_ln2_assembly2.v:347 lnb3_conv_slot 同层内容）与树内 Q 层        *)
(*    二次衰减核链（abl_ln2_theta_upper lnt2_hquad：h(t) ≤ 7/40，池外        *)
(*    不可 Require）。本件不冒领该供给：前提以 Set 形显式参数位承载           *)
(*    （非全局假设，Print Assumptions 仍全 Closed），到货即闭合。             *)
(*    消解路径注记：真族载体面桥的缝前提由装配件 u5c_ln2_weld_cascade        *)
(*    两道接合供给；预算供给到货后，装配第六节肢的代入                        *)
(*    = u5c_ln2_theta_slot_face_of_budget 一次应用。                         *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_theta_slot.v     *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_assembly.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 内容定义面（⑥位义务形：线面/真族载体面两形，θ 取装配规范值）           *)
(* ============================================================ *)

(* 线面义务形：|A_n·X − B_n| ≤ (4/5)ⁿ（定义性复用乙件上界义务面，
   θ 取装配规范值 u5c_lna_theta_mod = 4/5——lnb3_theta_slot 的同构重铸面） *)
Definition u5c_ln2_theta_slot (X : Real) (A B : nat -> Z) : Set :=
  u5c_ln2b_line_upper X A B u5c_lna_theta_mod.

(* 真族载体面义务形：I_n ≤ (4/5)ⁿ（与装配件 u5c_ln2_assembly_slot
   第六节肢语句逐字同形——装配残面的直接填充位） *)
Definition u5c_ln2_theta_slot_face (X : Real) (A B : nat -> Z)
  (I : nat -> Real) : Set :=
  forall n : nat, real_le (I n) (real_const (q_pow u5c_lna_theta_mod n)).

(* ============================================================ *)
(* §1 Q 层小件（幂乘法则/幂底合同/预算折叠/序迁移）                          *)
(* ============================================================ *)

(* 幂乘法则：aⁿ·bⁿ == (a·b)ⁿ（归纳＋q_pow_succ＋Qmult 兼容性，纯项模式链） *)
Lemma u5c_qpow_mul_qeq : forall (a b : Q) (n : nat),
  (q_pow a n * q_pow b n)%Q == (q_pow (a * b) n)%Q.
Proof.
  intros a b n. induction n as [| m IH].
  - reflexivity.
  - pose proof (q_pow_succ a m) as E1.
    pose proof (q_pow_succ b m) as E2.
    pose proof (q_pow_succ (a * b) m) as E3.
    apply (Qeq_trans _ ((a * q_pow a m) * (b * q_pow b m))%Q).
    + exact (@Qmult_comp _ _ E1 _ _ E2).
    + apply (Qeq_trans _ ((a * b) * (q_pow a m * q_pow b m))%Q).
      * ring.
      * apply (Qeq_trans _ ((a * b) * q_pow (a * b) m)%Q).
        -- exact (@Qmult_comp _ _ (Qeq_refl (a * b)%Q) _ _ IH).
        -- apply Qeq_sym. exact E3.
Qed.

(* 幂底合同：a == b ⟹ aⁿ == bⁿ *)
Lemma u5c_qpow_eq_base : forall (a b : Q) (n : nat),
  a == b -> (q_pow a n)%Q == (q_pow b n)%Q.
Proof.
  intros a b n Hab. induction n as [| m IH].
  - reflexivity.
  - pose proof (q_pow_succ a m) as E1.
    pose proof (q_pow_succ b m) as E2.
    apply (Qeq_trans _ (a * q_pow a m)%Q).
    + exact E1.
    + apply (Qeq_trans _ (b * q_pow b m)%Q).
      * exact (@Qmult_comp _ _ Hab _ _ IH).
      * apply Qeq_sym. exact E2.
Qed.

(* 幂乘法则的 QeqT 形（乙件传递件的可使用形） *)
Lemma u5c_qpow_mul : forall (a b : Q) (n : nat),
  QeqT (q_pow a n * q_pow b n)%Q (q_pow (a * b) n)%Q.
Proof. intros a b n. apply qeq_imp_qeqT. apply u5c_qpow_mul_qeq. Qed.

(* 预算折叠恒等式：4ⁿ·(7/40)ⁿ == (7/10)ⁿ
   （底折叠 4·(7/40) == 7/10 为定义性有理判定，幂层走幂乘法则＋幂底合同） *)
Theorem u5c_theta_budget_fold : forall n : nat,
  QeqT (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow (7 # 10)%Q n)%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  apply (Qeq_trans _ (q_pow ((4 # 1)%Q * (7 # 40)%Q) n)%Q).
  - exact (u5c_qpow_mul_qeq (4 # 1)%Q (7 # 40)%Q n).
  - apply u5c_qpow_eq_base. reflexivity.
Qed.

(* 数值锚：底折叠 4·(7/40) == 7/10（28/40 与 7/10 的交叉乘定义性判定） *)
Theorem u5c_theta_budget_fold_anchor : QeqT ((4 # 1)%Q * (7 # 40)%Q) (7 # 10)%Q.
Proof. reflexivity. Qed.

(* QleT' 沿 Qeq 的左/右侧迁移（走 Qle Prop 桥，不触碰 Id 内核） *)
Lemma u5c_leT'_eq_l : forall a c b : Q, a == c -> QleT' a b -> QleT' c b.
Proof.
  intros a c b Hac H. apply Qle_to_QleT'. apply (Qle_trans c a b).
  - apply qeq_le. apply Qeq_sym. exact Hac.
  - apply QleT'_to_Qle. exact H.
Qed.

Lemma u5c_leT'_eq_r : forall a b c : Q, b == c -> QleT' a b -> QleT' a c.
Proof.
  intros a b c Hbc H. apply Qle_to_QleT'. apply (Qle_trans a b c).
  - apply QleT'_to_Qle. exact H.
  - apply qeq_le. exact Hbc.
Qed.

(* Qle 沿 Qeq 的左/右迁移（Qle Prop 面传递桥，免 setoid） *)
Lemma u5c_qle_eq_l : forall a c b : Q, a == c -> Qle a b -> Qle c b.
Proof.
  intros a c b Hac H. apply (Qle_trans c a b).
  - apply qeq_le. apply Qeq_sym. exact Hac.
  - exact H.
Qed.

Lemma u5c_qle_eq_r : forall a b c : Q, b == c -> Qle a b -> Qle a c.
Proof.
  intros a b c Hbc H. apply (Qle_trans a b c).
  - exact H.
  - apply qeq_le. exact Hbc.
Qed.

(* 带宽比较主归纳：(7/10)ⁿ ≤ (4/5)ⁿ
   （步进：(7/10)·(7/10)ⁿ ≤ (4/5)·(7/10)ⁿ ≤ (4/5)·(4/5)ⁿ，
   两步各为有理乘法保序，7/10 ≤ 4/5 与幂非负为纯 Q 判定） *)
Lemma u5c_qpow_budget_core : forall n : nat,
  QleT' (q_pow (7 # 10)%Q n) (q_pow (4 # 5)%Q n).
Proof.
  intro n. induction n as [| m IH].
  - apply qeq_leT'. reflexivity.
  - apply Qle_to_QleT'.
    pose proof (q_pow_succ (7 # 10)%Q m) as E1.
    pose proof (q_pow_succ (4 # 5)%Q m) as E2.
    apply (u5c_qle_eq_r _ _ _ E2).
    apply (u5c_qle_eq_l _ _ _ E1).
    apply (Qle_trans _ ((4 # 5)%Q * q_pow (7 # 10)%Q m)%Q).
    + apply Qmult_le_compat_r.
      * apply Qlt_le_weak. unfold Qlt. cbn [Qnum Qden]. lia.
      * apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
    + apply (u5c_qle_eq_l _ _ _ (Qmult_comm (q_pow (7 # 10)%Q m) (4 # 5)%Q)).
      apply (u5c_qle_eq_r _ _ _ (Qmult_comm (q_pow (4 # 5)%Q m) (4 # 5)%Q)).
      apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. exact IH.
      * unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* θ 预算带宽承载（本件 Q 层主内容）：4ⁿ·(7/40)ⁿ ≤ (4/5)ⁿ
   ＝折叠恒等式（§1）＋带宽比较（归纳）的合成 *)
Theorem u5c_theta_budget : forall n : nat,
  QleT' (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow (4 # 5)%Q n)%Q.
Proof.
  intro n.
  apply (u5c_leT'_eq_l (q_pow (7 # 10)%Q n)
           (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow (4 # 5)%Q n)
           (Qeq_sym _ _ (qeqT_imp_qeq _ _ (u5c_theta_budget_fold n)))).
  apply u5c_qpow_budget_core.
Qed.

(* 数值锚：n=3 带宽比较实例 (7/10)³ ≤ (4/5)³（0.343 ≤ 0.512） *)
Theorem u5c_qpow_budget_anchor : QleT' (q_pow (7 # 10)%Q 3) (q_pow (4 # 5)%Q 3).
Proof. apply u5c_qpow_budget_core. Qed.

(* ============================================================ *)
(* §2 实数常值序提升（Q 层序 ⟹ 常值实数序；Or 编码按可判定劈分）             *)
(* ============================================================ *)

(* 常值实数相等：a == b ⟹ real_eq (real_const a) (real_const b)
   （N:=0，逐点读数定义性为常值；|a−b|==0 沿 QeqT 迁移到 eps 判定） *)
Lemma u5c_const_eq : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H eps Heps. exists 0%nat. intros n Hn.
  change (projT1 (real_const a) n) with a.
  change (projT1 (real_const b) n) with b.
  apply (qltT_eq_compat_l 0%Q (Qabs (a - b))%Q eps).
  - apply Qeq_sym.
    apply (Qeq_trans (Qabs (a - b))%Q (Qabs 0%Q) 0%Q).
    + apply Qabs_wd. setoid_rewrite H. ring.
    + reflexivity.
  - exact Heps.
Qed.

(* 常值实数严格序：Qlt a b ⟹ real_lt (real_const a) (real_const b)
   （eps := (1/2)·(b−a) 的显式配方，N:=0：(1/2)·(b−a) < b−a 沿 (1/2)<1
   乘法保序；0 < b−a 由 Qlt 定义面逐分量有理判定） *)
Lemma u5c_const_lt : forall a b : Q, Qlt a b -> real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (H0 : QltT 0 ((b - a)%Q)).
  { apply Qlt_to_QltT.
    destruct a as [an ad]. destruct b as [bn bd].
    unfold Qlt in Hab. cbn [Qnum Qden] in Hab.
    unfold Qlt. cbn [Qnum Qden Qminus Qplus Qopp]. lia. }
  assert (Hhalf : QltT 0 (1 # 2)%Q).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Heps : QltT 0 ((1 # 2) * (b - a))%Q)
    by (apply (qmult_ltT_0_compat (1 # 2)%Q (b - a)%Q); assumption).
  assert (Hpt : QltT ((1 # 2) * (b - a))%Q (b - a)%Q).
  { apply (qltT_eq_compat_r (b - a)%Q (1 * (b - a))%Q ((1 # 2) * (b - a))%Q).
    - ring.
    - apply (qltT_mult_ltT_compat_r (1 # 2)%Q 1%Q (b - a)%Q).
      + exact H0.
      + apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  exists ((1 # 2) * (b - a))%Q. split.
  - exact Heps.
  - exists 0%nat. intros n Hn.
    change (projT1 (real_const b) n) with b.
    change (projT1 (real_const a) n) with a.
    exact Hpt.
Qed.

(* 常值实数序：Qle a b ⟹ real_le (real_const a) (real_const b)
   （real_le 的 Or 编码按 Qlt_le_dec 可判定劈分：严格走 lt、互走 eq） *)
Lemma u5c_const_le : forall a b : Q, Qle a b -> real_le (real_const a) (real_const b).
Proof.
  intros a b Hab.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - exact (inl (u5c_const_lt a b Hlt)).
  - exact (inr (u5c_const_eq a b (Qle_antisym a b Hab Hge))).
Qed.

(* ============================================================ *)
(* §3 预算桥义务定理（⑥位内容：有理预算面供给 ⟹ 4/5 带宽上界）              *)
(* ============================================================ *)

(* 线面点态桥：预算实供给 ⟹ 线对象 ≤ (4/5)ⁿ
   （实数序传递＋预算带宽承载的实数常值序提升） *)
Theorem u5c_ln2_theta_slot_line : forall (X : Real) (A B : nat -> Z),
  (forall n : nat, real_le (u5c_ln2b_line X A B n)
                     (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  forall n : nat,
    real_le (u5c_ln2b_line X A B n) (real_const (q_pow u5c_lna_theta_mod n)).
Proof.
  intros X A B Hb n.
  apply (real_le_trans (u5c_ln2b_line X A B n)
          (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))
          (real_const (q_pow u5c_lna_theta_mod n))).
  - apply Hb.
  - apply u5c_const_le. apply QleT'_to_Qle. apply u5c_theta_budget.
Qed.

(* 义务定理一（线面）：预算实供给 ⟹ 线面义务形 inhabited
   （u5c_ln2_theta_slot 定义性展开即点态桥，与 lnb3_theta_slot 同构面） *)
Theorem u5c_ln2_theta_slot_of_budget : forall (X : Real) (A B : nat -> Z),
  (forall n : nat, real_le (u5c_ln2b_line X A B n)
                     (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  u5c_ln2_theta_slot X A B.
Proof. intros X A B Hb. exact (u5c_ln2_theta_slot_line X A B Hb). Qed.

(* 义务定理二（真族载体面·装配第六节肢直接代入入口）：
   缝（I 与线对象逐点实数相等）＋预算实供给 ⟹ 载体面义务形
   （沿 real_eq 的 real_le 右迁移＝乙件 gap2_le_eq_l 的直接使用） *)
Theorem u5c_ln2_theta_slot_face_of_budget :
  forall (X : Real) (A B : nat -> Z) (I : nat -> Real),
  (forall n : nat, real_eq (I n) (u5c_ln2b_line X A B n)) ->
  (forall n : nat, real_le (u5c_ln2b_line X A B n)
                     (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  u5c_ln2_theta_slot_face X A B I.
Proof.
  intros X A B I Hseam Hb n. unfold u5c_ln2_theta_slot_face.
  apply (gap2_le_eq_l (u5c_ln2b_line X A B n)
          (real_const (q_pow u5c_lna_theta_mod n)) (I n)).
  - exact (u5c_ln2_theta_slot_line X A B Hb n).
  - apply real_eq_sym. apply Hseam.
Qed.

(* ============================================================ *)
(* §4 提取与假设审计（零承认复核）                                           *)
(* ============================================================ *)

Separate Extraction u5c_theta_budget u5c_ln2_theta_slot_of_budget
  u5c_ln2_theta_slot_face_of_budget u5c_const_le u5c_const_lt u5c_const_eq.

Print Assumptions u5c_qpow_mul_qeq.
Print Assumptions u5c_qpow_eq_base.
Print Assumptions u5c_qle_eq_l.
Print Assumptions u5c_qle_eq_r.
Print Assumptions u5c_qpow_mul.
Print Assumptions u5c_theta_budget_fold.
Print Assumptions u5c_theta_budget_fold_anchor.
Print Assumptions u5c_leT'_eq_l.
Print Assumptions u5c_leT'_eq_r.
Print Assumptions u5c_qpow_budget_core.
Print Assumptions u5c_qpow_budget_anchor.
Print Assumptions u5c_theta_budget.
Print Assumptions u5c_const_eq.
Print Assumptions u5c_const_lt.
Print Assumptions u5c_const_le.
Print Assumptions u5c_ln2_theta_slot_line.
Print Assumptions u5c_ln2_theta_slot_of_budget.
Print Assumptions u5c_ln2_theta_slot_face_of_budget.
