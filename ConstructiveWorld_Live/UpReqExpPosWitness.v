(* UpReqExpPosWitness.v *)
(* 目的： 路径 A：指数正性的显式见证提取。 *)
(* 主件： upreq_exp_pos_witness 与 upreq_exp_partial_even_lower_witness。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 见证提取件：为正性主链供给 sigT 见证；零假设位。           *)
(* 对标：stdlib QArith 幂级数偶/奇截断下界构造。                     *)
(* 构造性注记：Set 层承载（QltT/QleT' 均集合层值）；零承认、公理面为空； *)
(*   可提取（Separate Extraction 检验 Obj.magic=0）。                 *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 温控包装，-Q 单根。             *)
(* UpReqExpPosWitness.v —— 路径 A 显式见证提取件 *)
(* 使命（路径 A：算法见证显式化）：0 < e^x 的 ε 见证不再埋在  *)
(* 证明项里，而是以显式 sigT 函数结果（第一见证位 eps 浮出为有理数    *)
(* 输出），再经 Separate Extraction 检验为真实可计算程序——      *)
(* 见证函数体可溯源到 S03 幂级数 ε-构造（一致界 C、偶截断 >= 1/C、   *)
(* 奇截断 >= 1/(2C)、eps := 1/(2C)、N := 2*m0+1）。                 *)
(* 语句面实形依据（照源码实形书写）：               *)
(*   QltT (x y : Q) : Set := Id (Qlt_bool x y) true   （S02:26）    *)
(*   QleT' (x y : Q) : Set := Id (Qle_bool x y) true  （S02:77）    *)
(*   And  (A B : Set) : Set := A * B                  （S01:68）    *)
(*   real_lt x y := sigT (fun eps : Q => And (QltT 0 eps)           *)
(*     (sigT (fun N : nat => forall n, NatLe N n ->                 *)
(*       QltT eps (projT1 y n - projT1 x n))))        （S02:456）    *)
(* 若把第二分量误写为 QltT q (real_exp_neg ...) 会把 Real 层项混入 Q  *)
(* 层谓词（QltT : Q -> Q -> Set），类型不通；本件第二分量照 real_lt   *)
(* 实形写（N 界 + 逐点分离），与 real_lt 逐位对齐。                  *)
(* 改动边界：只新建本件；基座 UpReqExpPos.v 零改动；       *)
(* 前缀 upreq_exp_pos_witness / upreq_exp_partial 全库防撞已核。      *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* 件 1（S1 主件）：0 < e^x 的显式 ε-见证                             *)
(*   将 real_exp_neg_pos（S07:7766，其 ε 由 S03:6412 cauchy_real_    *)
(*   exp_pos 的幂级数构造给出）的 sigT 拆包重组：第一见证位 eps 直接   *)
(*   浮出为本函数的显式有理数输出，第二分量（N 界 + 逐点分离）原位     *)
(*   转译。整个定理体是一个可提取的函数项：输入 x，输出 (q, 正性, 界)。 *)
(* ============================================================ *)
Theorem upreq_exp_pos_witness :
  forall x : Real,
    sigT (fun q : Q =>
            And (QltT 0%Q q)
                (sigT (fun N : nat =>
                          forall n : nat, NatLe N n ->
                            QltT q ((projT1 (real_exp_neg (real_opp x)) n
                                     - projT1 real_zero n)%Q)))).
Proof.
  intro x.
  destruct (real_exp_neg_pos (real_opp x)) as [q [Hq [N HN]]].
  exists q.
  split.
  - exact Hq.
  - exists N. exact HN.
Qed.

(* ============================================================ *)
(* 件 2（A.3.1 形）：偶截断显式有理下界的见证形        *)
(*   S03 exp_partial_even_lower（6172：|y| <= M ⟹ 1/C <= exp_partial *)
(*   (2m) y；由 exp_even_mul_eq(5937) + corr_nonneg(1636) + 上界引擎   *)
(*   exp_series_arch(1094) 组装）结论是 Qle（Prop 面）；本件重铸为     *)
(*   sigT 见证形：显式有理下界 q := 1/C 作为函数输出浮出，正性位        *)
(*   QltT 0 q 独立结果。Qle 到 QleT' 换桥用库件 Qle_to_QleT'          *)
(*   （S02:93，经 Qle_bool 可判定性的构造换桥）。上界引擎库内现名为    *)
(*   exp_series_arch（exp_series_bounded 库内无此名）。 *)
(* ============================================================ *)
Theorem upreq_exp_partial_even_lower_witness :
  forall (M C y : Q) (m : nat),
    QleT' 0%Q M -> QleT' 1%Q C ->
    (forall n : nat, QleT' (exp_series n M) C) ->
    QleT' (Qabs y) M ->
    sigT (fun q : Q =>
            And (QltT 0%Q q) (QleT' q (exp_partial (2 * m)%nat y))).
Proof.
  intros M C y m HM HC HCser Hy.
  exists (1 / C)%Q.
  split.
  - apply (qltT_div_pos 1%Q C).
    + exact qltT_0_1.
    + apply (qltT_leT'_ltT 0%Q 1%Q C).
      * exact qltT_0_1.
      * exact HC.
  - apply Qle_to_QleT'.
    exact (exp_partial_even_lower M C y m HM HC HCser Hy).
Qed.

Print Assumptions upreq_exp_pos_witness.
Print Assumptions upreq_exp_partial_even_lower_witness.
