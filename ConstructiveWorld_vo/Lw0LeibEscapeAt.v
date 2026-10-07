(* 五字段指针｜模块：Lw0LeibEscapeAt。使命：LW0LeibSeparation §4 内侧支分区
   S5 随件三（案三 lic 接口形）的落地面——对每一有理数 a/b 给出显式逃逸阶见证：
   存在 n >= 1 使窗距 lw0m_e n 严格小于点距 |a/b - xL n|（lic 窗型接口形，
   LW0LicAdapt lw0m_escape_at_cond 去前提版的 Lw0 系对齐形）。本件为
   leibsep_q_kernel（LW0LeibSeparation 内侧支 Q 内核无条件形）的一步机械转写：
   由内核的正距离 c 与窗距消失面 lw0m_vanish_pi 在 N1 := max N (max N0 1) 处
   合流（窗距 e N1 < c/8 < c < |xL N1 - a/b|，Qabs 对称一步换岸）。
  依赖：S01_BaseRing（And/NatLe/NatLe_lift）、S02_CauchyComplete（QltT/
   QltT_to_Qlt/Qlt_to_QltT）、LW0MLicBridge（lw0m_e/lw0m_xL/lw0m_vanish_pi）、
   LW0LeibSeparation（leibsep_q_kernel）。
  对标行：LW0LeibSeparation.v :391-436（§4 内侧支分区·S5 随件三冻结语句面，
   本件即其落地面）；LW0LeibSeparation.v :5452（leibsep_q_kernel 上游源）；
   LW0LicAdapt.v :58/:98（下游两定点适配件：本件就位后删 Hp 实参一行即升
   无条件形）；UpReqIrrationalCriterion.v :242（lic_escape_window 窗型）。
  构造性注记：零公理声明、零承认式（件尾 Print Assumptions 应 Closed）；
   语句面全 Set 层零 Prop 泄露（sigT/And/QltT 均 Set 值，(1 <= n)%nat 箭头位
   为认证先例形）；证内 Prop（Qlt）仅脚手架，出口位一律 Qlt_to_QltT 回 Set；
   见证 n 由 max 真算非空转。诚实边界：本件结论以 leibsep_q_kernel 已闭合为
   前提面（其内核证内的 Niven 多项式机械不在本件重复）。
  编译配方：coqc -native-compiler no -q -Q "<本件目录>" "" -Q
   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0MLicBridge.
Require Import Local.LW0LeibSeparation.

Lemma leibsep_escape_window_at :
  forall a b : Q,
    QltT 0 (Qabs b) ->
    sigT (fun n : nat => And ((1 <= n)%nat)
            (QltT (lw0m_e n) (Qabs ((a / b - lw0m_xL n)%Q)))).
Proof.
  intros a b Hb.
  destruct (leibsep_q_kernel (a / b)%Q) as [c [Hc0 [N HN]]].
  pose proof (QltT_to_Qlt _ _ Hc0) as Hc0'.
  assert (Hc8 : QltT 0 (c * (1 # 8))%Q) by (apply Qlt_to_QltT; lra).
  destruct (lw0m_vanish_pi (c * (1 # 8))%Q Hc8) as [N0 HN0].
  set (N1 := Nat.max N (Nat.max N0 1)).
  assert (HN01 : (1 <= N1)%nat)
    by (apply (Nat.le_trans 1 (Nat.max N0 1) N1);
          [apply Nat.le_max_r | apply Nat.le_max_r]).
  assert (HN0N1 : QltT (lw0m_e N1) (c * (1 # 8))%Q).
  { apply (HN0 N1). apply (Nat.max_lub_l N0 1). apply Nat.le_max_r. }
  pose proof (QltT_to_Qlt _ _ HN0N1) as HN0N1'.
  pose proof (QltT_to_Qlt _ _
    (HN N1 (NatLe_lift _ _ (Nat.le_max_l N (Nat.max N0 1))))) as HkN1.
  exists N1.
  split.
  - exact HN01.
  - assert (Hs1 : (a / b - lw0m_xL N1)%Q == (-(lw0m_xL N1 - a / b)%Q)) by ring.
    assert (Hsym : Qabs ((a / b - lw0m_xL N1)%Q)
                   == Qabs ((lw0m_xL N1 - a / b)%Q)).
    { rewrite Hs1. apply Qabs_opp. }
    apply Qlt_to_QltT. rewrite Hsym. lra.
Qed.

Print Assumptions leibsep_escape_window_at.

Separate Extraction leibsep_escape_window_at.
