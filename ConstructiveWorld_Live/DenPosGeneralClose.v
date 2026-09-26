(* ===================================================================== *)
(* DenPosGeneralClose.v —— pade 分母非负/严格档的四来源覆盖证书件。        *)
(* 形态：声明件——注记＋引用性定理（全 exact/实例化转发，零新数学内容）；        *)
(*   dpc_ 前缀全库防撞；宿主 UpReqPadeSign.v 零改动。                      *)
(*   使命：汇总 pade_den 非负档与严格档的库内现成来源，兑现旧注记      *)
(*   留记的依赖缺口（相邻递减比式件等已全部建成，旧注记陈旧）。          *)
(*   覆盖表（语句面×结论域×严格度）：                                        *)
(*    ① PadeDenPosB12（pdpb_）：pdpb_den_pos_le2@141 [0,2] 全段非负，        *)
(*      为留记「0<=x 段非负档」的严格超集；② UpReqPadeDenPos12（pdq_）：      *)
(*      pdq_den_pos_12@157 (1,2) 段；③ UpReqPadeDenPos（pdp_）：               *)
(*      pdp_den_pos@493 0≤x≤1 精确同域；④ PadeDenPosA（pdpa_）：             *)
(*      pdpa_den_pos_strict@318 一般 n 全体 [0,2) 严格档（含 n=0 特例        *)
(*      pdpa_den0_one@305）——留记「首对严格升 QltT」路线的通用 n 闭合。        *)
(*      比式/递减件：pdpb_R_ge_2@50 / pdq_R_ge_2@69 / pdpa_R_ge_2@153 /    *)
(*      pdpa_term_decay@201；引擎出口 altsum_nonneg@475 /                    *)
(*      altsum_nonneg_leT@UpReqAltSumPos.v:464 / altsum_pos_strict@599。       *)
(*      旧留记「库内尚无现成件」的依赖缺口已全部建成。                          *)
(*    汇总：非负档 0≤x≤1←③:493；(1,2]/(1,2)←①:172/②:157；[0,2]←①:141。      *)
(*      严格档 [0,2)←④:318；(1,2)←②:249。x=2 端点严格档不可证系数学        *)
(*      必然（n=1 分母 1−x/2 在 x=2 为零），两档语句面在端点分岔非缺口。      *)
(*   依赖：上述四来源件＋UpReqPadeExp/UpReqAltSumPos（全部只读引用）。        *)
(*   对标：den(x) := altsum (fun k => pade_coeff n k * q_pow x k) (n+1)。        *)
(*   构造性：引用性转发全 exact/实例化；零新公理面。                          *)
(*   编译配方：coqc -native-compiler no -q -Q . ""。                              *)
(* ===================================================================== *)

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
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
Require Import PadeDenPosA DenPosGeneral.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* 引用性主件：严格档统一闭合形——语句面与 pdpa_den_pos_strict 逐字同构，  *)
(* 全参 exact 转发，零新证（来源④坐标的定理面落章）。                    *)
Theorem dpc_den_pos_close : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof. exact pdpa_den_pos_strict. Qed.

(* 引用性互证件：同一语句面经补充源⑤（dpg_，n=0 走 pdpa_den0_one）      *)
(* 独立可达——严格档库内双路线实证。                                      *)
Theorem dpc_den_pos_close_alt : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx H2.
  destruct n as [| m].
  - apply (qeq_ltT 1%Q (pade_den 0%nat x)).
    + apply Qeq_sym. apply pdpa_den0_one.
    + apply qltT_0_1.
  - apply (dpg_den_pos_strict_T (Datatypes.S m) x).
    + lia.
    + exact Hx.
    + exact H2.
Qed.

(* 留记标记核对件：宿主 n=1 手工实例 pds_den1_pos@UpReqPadeSign.v:106    *)
(* 语句面（QltT 0 x -> QltT x 2 -> QltT 0 (pade_den 1 x)）由通用严格档    *)
(* 直接实例——通用件回场核对标记，条款兑现。                              *)
Theorem dpc_pds_den1_pos_sentinel : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1%nat x).
Proof.
  intros x H0 H2.
  apply (dpc_den_pos_close 1%nat x).
  - left. exact H0.
  - exact H2.
Qed.

(* ===== G1 证据：引用链全库内 Closed 件 ===== *)
Print Assumptions dpc_den_pos_close.
Print Assumptions dpc_den_pos_close_alt.
Print Assumptions dpc_pds_den1_pos_sentinel.
