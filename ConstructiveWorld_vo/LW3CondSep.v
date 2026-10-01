(* LW3CondSep.v                                                          *)
(* 使命：M3 案丙分层形余下两层落地——其一 C2 条件定理（|λ|<1 线）：未缩放    *)
(*       侧增长量低于一即整数泛函值的绝对值低于一（391 未缩放上界经谱桥与   *)
(*       严格比较合成）；其二 C4 合成组装件：零点前件、E-槽间隙承载位与      *)
(*       增长量门槛三前件下，分离见证经 379 承载形与本件 C2 及矛盾出口      *)
(*       三段装配产出（394 材料包 §案丙 C2/C4 行语句面草案逐字承袭，        *)
(*       tlw399_ 前缀避占终形名位）。另附锚例增长量值钉（2452， documenting *)
(*       门槛前件在锚例处的可判定间隙）。                                   *)
(* 依赖：LW3ETranscendental（只读正本）及其闭包 S01/S02/S03/LW0/LW1/LW2 系； *)
(*       LW3P2Prod（端点泛函求值式桥，379 链只读使用）；               *)
(*       _tlw381_famscale/_tlw384_fill/_tlw384_vtsum/_tlw387_dual（391 谱系  *)
(*       vo 只读使用）；LW3P2Carrier（C1 承载形，vo 67909526 系）；     *)
(*       _tlw391_genfill（C3 填装族，vo a7ef9241 系）。                     *)
(* 对标：E-STAGING-LW0-GAPASUME（检索索引 L1842：C4 的 E-槽间隙前件为显式    *)
(*       承载位，缺口即后续段目标形，kills/识别桥落地后零改动升形——照       *)
(*       E-槽桥判例）；E-STAGING-LW0-NOEVALIFT（检索索引 L1860：装配全走     *)
(*       在件引理与数据桥，零 eval 级拼装）；attn\_tlw394 跨线合成裁决材料   *)
(*       包 §案丙分层形（本件使命源）；attn\_tlw391 记录 §六尾款（装配桥    *)
(*       候令状态供料账）。                                                 *)
(* 构造性：语句面全 Set——前提位 lw3_nz 枚举形、real_eq 数据形、lw3_qnz      *)
(*       布尔见证形、QltT Id-bool 形；结论面 sigT＋And＋QltT（394 案甲′     *)
(*       同面）；零 Axiom、零假设承载位、零新增命题语句；等词面仅证明体内   *)
(*       （正本 step1 同款口径）；提取并集仅数据名（锚例多项式与指数，      *)
(*       值钉不入提取并集——391 同款工艺，match 型见证经擦除必生魔数）。     *)
(* 编译配方：SW2 双 export COQLIB/ROCQLIB="C:/Rocq-Platform~9.1~2026.01/    *)
(*       lib/coq" 全字面；coqc -q -Q . "" -Q "D:\ComplexAnalysis\           *)
(*       ConstructiveWorld-Main\ConstructiveWorld_vo" ""；cpu_guard 包裹。  *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.
Require Import LW3P2Prod.
Require Import LW3DualBridge.
Require Import LW3JointFill.
Require Import LW3VarTSumBound.
Require Import LW3FamScale.
Require Import LW3P2Carrier.
Require Import LW3GenFill.
(* LW1ZPoly opens Z_scope at file level and the open leaks through the      *)
(* Require chain, so the bare numeral default would land on Z; reopen the   *)
(* rational scope for this file.  Every nat/Z occurrence carries an explicit *)
(* scope annotation, so no reading changes.                                 *)
Local Open Scope Q_scope.

(* ===== C2.  The conditional below-one theorem on the unscaled line. ===== *)

(* The growth threshold transfers to the integer functional value: once    *)
(* the unscaled growth quantity falls below one, the absolute value of the *)
(* lambda functional does too, and the spectral bridge then moves the      *)
(* strict comparison onto the integer functional value with its unit       *)
(* denominator.                                                            *)
Theorem tlw399_c2_lambda_lt1_cond :
  forall (p : zpoly) (N : nat),
    QltT (lw391_wsum_unscaled p N) (1 # 1)%Q ->
    QltT (Qabs ((lw3_Kinst p N) # 1)%Q) (1 # 1)%Q.
Proof.
  intros p N Hlt.
  assert (Hlam : lw2_lambda (lw3_nodecount p N)
                   (lw3_fbuild p (lw3_deg p) N)
                 == ((lw3_Kinst p N) # 1)%Q)
    by exact (lw3_Kinst_spec p N).
  exact (qltT_eq_compat_l
           (Qabs (lw2_lambda (lw3_nodecount p N)
                   (lw3_fbuild p (lw3_deg p) N)))
           (Qabs ((lw3_Kinst p N) # 1)%Q)
           (1 # 1)%Q
           (lw3_Qabs_congr _ _ Hlam)
           (qleT'_ltT_ltT _ _ _
              (lw391_lambda_upper_unscaled p N) Hlt)).
Qed.

(* ===== C4.  The conditional assembly theorem (the Case-A-prime face). ==== *)

(* The full conditional form: the nonzero polynomial witness, the          *)
(* vanishing of the polynomial evaluation at the constructive constant e,  *)
(* the explicit standing premise holding the E-slot analytic half, and the *)
(* growth threshold together produce the separation witness.  The chain    *)
(* rides the C1 carrier for the K nonzero witness, the C2 theorem for the  *)
(* strict below-one comparison, and the contradiction exit for the         *)
(* witness; all premises are Set-sorted and the main statement stays       *)
(* untouched.                                                              *)
Theorem tlw399_c4_full_cond1 :
  forall (p : zpoly) (N : nat),
    lw3_nz p ->
    real_eq (lw3_evalr p lw3_e) real_zero ->
    lw3_qnz (lw2_exp_L (1 # 1)%Q
              (length (lw3_fbuild p (lw3_deg p) N))
              (lw3_fbuild p (lw3_deg p) N)
              (lw2_node (Datatypes.S (lw3_nodecount p N)))) ->
    QltT (lw391_wsum_unscaled p N) (1 # 1)%Q ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (lw3_evalr p lw3_e) real_zero))).
Proof.
  intros p N Hnz Hpzero Hgap Hlt.
  assert (HP2 : lw3_qnz ((lw3_Kinst p N) # 1)%Q)
    by exact (tlw379_p2carrier p N Hnz Hpzero Hgap).
  assert (HK : lw3_Kinst p N <> 0%Z).
  { intro Hz. unfold lw3_qnz in HP2.
    rewrite Hz in HP2. rewrite Qeq_bool_refl in HP2.
    cbn in HP2. destruct HP2. }
  exact (lw3_e_trans_exit p N HK (tlw399_c2_lambda_lt1_cond p N Hlt)).
Qed.

(* ===== The anchor growth datum. ===== *)

(* The growth quantity at the anchor polynomial and first exponent equals  *)
(* 2452: the threshold premise is decidable at the anchor and its gap to   *)
(* one is exactly 2451, which records why the conditional premises of the  *)
(* two theorems above are not discharged there (the discharge belongs to   *)
(* the continuation orders: the kills line and the identification bridge). *)
Definition tlw399_anchor_B_p381 :
  match Qeq_bool (lw391_wsum_unscaled p381 N1_381) (2452 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Print Assumptions tlw399_c2_lambda_lt1_cond.
Print Assumptions tlw399_c4_full_cond1.
Print Assumptions tlw399_anchor_B_p381.

From Stdlib Require Import Extraction.
Separate Extraction p381 N1_381.
