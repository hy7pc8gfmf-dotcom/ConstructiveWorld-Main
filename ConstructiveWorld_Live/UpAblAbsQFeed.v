(* ==========================================================================)
   UpAblAbsQFeed.v — 绝对值三角不等式的 Q 层推论件
   使命: uaq_abs_triangle_plus/minus（± 形三角）、uaq_abs_triangle_reverse_leT（反向形）、uaq_abs_abs_diff_le/ltT（双重绝对值差）、uaq_qfloor_abs_margin、uaq_abs_nonneg。
   依赖: CW_ConstructiveWorld_219、UpAblAbsSumLeB2；Stdlib List、QArith、Lia、Lqa。
   对标: 绝对值三角不等式及其反向形（初等分析）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* Part 0 · 签名核验（依赖签名漂移即编译报错）                              *)
(* ============================================================ *)

Check QltT. Check QleT'.
Check Qle_to_QleT'. Check QleT'_to_Qle. Check qeq_le.
Check qltT_eq_compat_l. Check qleT'_ltT_ltT. Check qabs_nonnegT.
Check Qabs_triangle. Check Qabs_triangle_reverse. Check Qabs_pos.
Check Qabs_opp. Check Qabs_wd. Check Qabs_Qle_condition.
Check Qopp_comp. Check Qopp_le_compat. Check Qeq_sym.
Check Qle_trans. Check Qminus.
Check uabS4b_arch_N. Check uabS4b_null_lt. Check uabS4b_null_nonneg.

(* ============================================================ *)
(* Part A · S10 六点供给：＋形三角语句族                                   *)
(* ============================================================ *)

(* A.1 ＋形三角语句形（S10_KVQuantTrig 四处使用面逐字同形）。
   由 stdlib 引理 Qabs_triangle 经 Qle_to_QleT' 转换直接推得，无附加
   证明步骤；本件价值在以 Set 层语句形常备（Q 世界语句面供给位）。 *)
Corollary uaq_abs_triangle_plus : forall a b : Q,
  QleT' (Qabs (a + b)) (Qabs a + Qabs b).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* A.2 减法形直接供给（S10_KVQuantTrig 两处使用面原以环归一化到＋形
   后应用三角不等式——本件直接给出减法形，使用处免归一步）。 *)
Corollary uaq_abs_triangle_minus : forall a b : Q,
  QleT' (Qabs (a - b)) (Qabs a + Qabs b).
Proof.
  intros a b. apply Qle_to_QleT'.
  assert (Hm : a - b == a + Qopp b) by (unfold Qminus; ring).
  assert (Ho : Qabs (Qopp b) == Qabs b) by apply Qabs_opp.
  apply (Qle_trans _ (Qabs (a + Qopp b)) _).
  - apply qeq_le. apply Qabs_wd. exact Hm.
  - apply (Qle_trans _ (Qabs a + Qabs (Qopp b)) _).
    + apply Qabs_triangle.
    + apply qeq_le. rewrite Ho. reflexivity.
Qed.

(* A.3 reverse 裸形（S08 使用点双支的直接构件，stdlib 语句面逐字同形）。 *)
Corollary uaq_abs_triangle_reverse_leT : forall a b : Q,
  QleT' (Qabs a - Qabs b) (Qabs (a - b)).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle_reverse.
Qed.

(* ============================================================ *)
(* Part B · S08 双层差语句供给                                             *)
(* ============================================================ *)

(* B.1 双层差整件：|Qabs a − Qabs b| ≤ Qabs (a − b)。
   对应 S08_RealMainlineDPO 的双层差语句（原使用处以
   Qabs_Qle_condition 双支内联展开，此处收束为单件供给）。证明：Qopp 支经
   Qabs_opp 换形＋Qopp_le_compat 反向接续＋Qminus 环归一；正向支由 Qabs_triangle_reverse 直接给出。 *)
Theorem uaq_abs_abs_diff_le : forall a b : Q,
  QleT' (Qabs (Qabs a - Qabs b)) (Qabs (a - b)).
Proof.
  intros a b. apply Qle_to_QleT'.
  assert (Hrev : Qabs b - Qabs a <= Qabs (b - a)) by apply Qabs_triangle_reverse.
  assert (Heq : Qabs (b - a) == Qabs (a - b)).
  { apply (Qeq_trans (Qabs (b - a)) (Qabs (Qopp (a - b))) (Qabs (a - b))).
    - apply Qabs_wd. unfold Qminus. ring.
    - apply Qabs_opp. }
  apply (proj2 (Qabs_Qle_condition (Qabs a - Qabs b) (Qabs (a - b)))).
  split.
  - (* Qopp 支：−|a−b| ≤ |a|−|b|：先由 Heq 把 Hrev 右端换形为 Qabs (a − b)，
       再经 Qopp_le_compat 反号保序，差形恒等式 −(x − y) == y − x
       于 Qminus 展开后收尾 *)
    rewrite Heq in Hrev.
    apply (Qle_trans _ (Qopp (Qabs b - Qabs a))).
    + apply Qopp_le_compat. exact Hrev.
    + apply qeq_le. unfold Qminus. ring.
  - (* 正向支：|a|−|b| ≤ |a−b| *)
    exact (Qabs_triangle_reverse a b).
Qed.

(* B.2 严格余量版（经转换层）：Qabs 尾界 ε 直接传递到双层差——
   S10_KVQuantTrig 局部差链与 S08 尾界使用处的 QltT 面语句形。
   纯 Set 层序推理：经 qleT'_ltT_ltT（左 QleT' 右 QltT）转换。 *)
Corollary uaq_abs_abs_diff_ltT : forall a b e : Q,
  QltT (Qabs (a - b)) e -> QltT (Qabs (Qabs a - Qabs b)) e.
Proof.
  intros a b e Hab.
  exact (qleT'_ltT_ltT _ _ _ (uaq_abs_abs_diff_le a b) Hab).
Qed.

(* ============================================================ *)
(* Part C · Qfloor 谱系衔接：S4B 单位分数证书过 Qabs 门                     *)
(* ============================================================ *)

(* C.1 Qabs 形尾界余量证书：S4B 阿基米德指标 uabS4b_arch_N 的单位分数
   1/(N(e)+1) 过 Qabs 门——Q 世界柯西链以 Qabs 尾界陈述时的余量供给源
   （谱系件 UpAblAbsSumLeB2 的直接应用）。 *)
Theorem uaq_qfloor_abs_margin : forall e : Q, QltT 0 e ->
  QltT (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e)))) e.
Proof.
  intros e He.
  assert (Hpos : Qle 0 (1#(Pos.of_succ_nat (uabS4b_arch_N e))))
    by apply uabS4b_null_nonneg.
  assert (Habs : Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e)))
                 == 1#(Pos.of_succ_nat (uabS4b_arch_N e)))
    by (apply Qabs_pos; exact Hpos).
  apply (qltT_eq_compat_l (1#(Pos.of_succ_nat (uabS4b_arch_N e)))
                          (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e))))
                          e (Qeq_sym _ _ Habs)).
  exact (uabS4b_null_lt e He).
Qed.

(* C.2 非负性形式：0 ≤ Qabs x 的 Set 层形（S10_KVQuantTrig 使用面；
   S02 的 qabs_nonnegT 同形常备）。 *)
Corollary uaq_abs_nonneg : forall x : Q, QleT' 0 (Qabs x).
Proof. intros x. apply qabs_nonnegT. Qed.

(* ============================================================ *)
(* 假设审计：全件 Closed（零外部未证假设）                                  *)
(* ============================================================ *)

Print Assumptions uaq_abs_triangle_plus.
Print Assumptions uaq_abs_triangle_minus.
Print Assumptions uaq_abs_triangle_reverse_leT.
Print Assumptions uaq_abs_abs_diff_le.
Print Assumptions uaq_abs_abs_diff_ltT.
Print Assumptions uaq_qfloor_abs_margin.
Print Assumptions uaq_abs_nonneg.
