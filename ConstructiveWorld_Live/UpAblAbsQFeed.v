(* ============================================================ *)
(* UpAblAbsQFeed.v —— Q 世界 Qabs 槽直配供给件（N4R 席·20260920）          *)
(*                                                                *)
(* 席位：N4R（Q 世界 Qabs 槽×9 直配席，M3 普查 #8）｜包装协议 v2 内嵌执行  *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   全部交付语句 Set 层值（QleT'/QltT＝S02 Id(Qle_bool/Qlt_bool,true) 形），*)
(*   语句面无裸命题；证明全构造（「命题层面」仅 stdlib 序引理消费）。        *)
(*                                                                *)
(* 槽位来源（M3 普查表 #8，逐处 grep 定谳）：                              *)
(*   S10_KVQuantTrig.v Qabs_triangle 消费×6（:1411 sin 尾、:1426 cos 尾、   *)
(*     :2015 sin 差项、:2074 cos 差项、:2265 sin 局部差链、:2350 cos 局部    *)
(*     差链）——语句面全为＋形三角 Qabs(a+b) ≤ Qabs a + Qabs b（其中        *)
(*     2015/2074 先 ring 归一到＋形再 apply）；                            *)
(*   S08_RealMainlineDPO.v :5121-5166 双层差槽——语句面                     *)
(*     |Qabs x − Qabs y| ≤ Qabs (x − y)（Qabs_Qle_condition 双支＋          *)
(*     Qabs_triangle_reverse 双向，槽内 25 行内联）。                       *)
(* 逐槽定谳：9/9 均 Q 层自足（stdlib QArith.Qabs 序面，无 Real 桥依赖）；    *)
(*   其中 S08 两点为 Real 层引理的逐点 Q 子语句（子语句面仍 Q 自足）。      *)
(*                                                                *)
(* 供给结构：                                                              *)
(*   A S10 六槽供给：＋形三角（stdlib 直喂＋Set 层升格，适配消费级如实      *)
(*     定性）＋减法形直供（免 ring 归一）＋reverse 裸形；                   *)
(*   B S08 槽全款包：双层差整包单件＋严格余量版（QleT'→QltT 转换层装配）；  *)
(*   C Qfloor 谱系消费：S4B uabS4b_arch_N 阿基米德指标单位分数证书过        *)
(*     Qabs 门（柯西链 Qabs 形尾界余量供体）＋非负门桥。                    *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（Export S02 转换层）＋                    *)
(*   UpAblAbsSumLeB2（S4B Qfloor 谱系件，.vo 在盘）。                       *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* Part 0 · 冻结现态打表（签名漂移即响亮失败）                              *)
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
(* Part A · S10 六槽供给：＋形三角槽族                                     *)
(* ============================================================ *)

(* A.1 ＋形三角槽形（S10:1411/1426/2265/2350 四处消费面逐字同形）。
   诚实定性：适配消费级——stdlib Qabs_triangle 直喂＋QleT' 升格，
   证明增量零；本席价值在 Set 层槽形常备（Q 世界语句面直配位）。 *)
Corollary uaq_abs_triangle_plus : forall a b : Q,
  QleT' (Qabs (a + b)) (Qabs a + Qabs b).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* A.2 减法形直供（S10:2015/2074 消费面先 ring 归一到＋形再 apply——
   本件直供减法形，消费免归一步）。 *)
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

(* A.3 reverse 裸形（S08 槽位双支的直接构件，stdlib 语句面逐字同形）。 *)
Corollary uaq_abs_triangle_reverse_leT : forall a b : Q,
  QleT' (Qabs a - Qabs b) (Qabs (a - b)).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle_reverse.
Qed.

(* ============================================================ *)
(* Part B · S08 双层差槽全款包                                             *)
(* ============================================================ *)

(* B.1 双层差整包：|Qabs a − Qabs b| ≤ Qabs (a − b)。
   S08:5121-5166 槽位语句整包（槽内 Qabs_Qle_condition 双支 25 行内联
   收束为单件供给）。真实现：Qopp 支经 Qabs_opp 换形＋Qopp_le_compat
   反向承接＋Qminus 环归一；正向支 reverse 直喂。 *)
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
  - (* Qopp 支：−|a−b| ≤ |a|−|b|（lra 线性收束：Heq Qeq 桥＋Hrev reverse） *)
    lra.
  - (* 正向支：|a|−|b| ≤ |a−b| *)
    exact (Qabs_triangle_reverse a b).
Qed.

(* B.2 严格余量版（转换层装配）：Qabs 尾界 ε 直传双层差——
   S10:2265/2350 局部差链与 S08 尾界消费的 QltT 面槽形。
   纯 Set 层序推理装配：qleT'_ltT_ltT（S02:148）左 QleT' 右 QltT。 *)
Corollary uaq_abs_abs_diff_ltT : forall a b e : Q,
  QltT (Qabs (a - b)) e -> QltT (Qabs (Qabs a - Qabs b)) e.
Proof.
  intros a b e Hab.
  exact (qleT'_ltT_ltT _ _ _ (uaq_abs_abs_diff_le a b) Hab).
Qed.

(* ============================================================ *)
(* Part C · Qfloor 谱系消费：S4B 单位分数证书过 Qabs 门                     *)
(* ============================================================ *)

(* C.1 Qabs 形尾界余量证书：S4B 阿基米德指标 uabS4b_arch_N 的单位分数
   1/(N(e)+1) 过 Qabs 门——Q 世界柯西链以 Qabs 尾界陈述时的余量供体
   （Qfloor 谱系件 UpAblAbsSumLeB2 直配消费）。 *)
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

(* C.2 非负门桥：0 ≤ Qabs x 的 Set 层形（S10:1634 消费面直配；
   S02 qabs_nonnegT 同形常备——适配消费级如实定性）。 *)
Corollary uaq_abs_nonneg : forall x : Q, QleT' 0 (Qabs x).
Proof. intros x. apply qabs_nonnegT. Qed.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions uaq_abs_triangle_plus.
Print Assumptions uaq_abs_triangle_minus.
Print Assumptions uaq_abs_triangle_reverse_leT.
Print Assumptions uaq_abs_abs_diff_le.
Print Assumptions uaq_abs_abs_diff_ltT.
Print Assumptions uaq_qfloor_abs_margin.
Print Assumptions uaq_abs_nonneg.
