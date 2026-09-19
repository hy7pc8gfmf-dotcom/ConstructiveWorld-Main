(* ============================================================ *)
(* UpAblD1S3_sum_pos_TempSoftmaxInstantiation.v —— FA-D1S3 批 D1-⑤    *)
(*   sum_pos 收官批·件12                                                *)
(*   槽位：TempSoftmaxInstantiation.v L239（Hsum_pos，RI 面，语句逐字）  *)
(*     forall f : Token -> R, (forall w : Token, lt zero (f w)) ->       *)
(*     lt zero (sumf f)                                                  *)
(*   放电母本（普查表钦定）：fa57_sum_carrier_realizes@fa57_ext.v:63     *)
(*     （E389/E703 sum_pos 槽收官 sigT 打包件）；本槽原世界即 RI 面      *)
(*     （Context {RI}），与母本同面——零降级直喂：sumf 槽取母本          *)
(*     sigT 打包件 projT1 投影，槽语句由母本 pos 组件（And 首字段        *)
(*     fst）逐字直喂。                                                   *)
(*   本件语境注记：宿主件为 T2b 件1 槽11 已引用装配桥（UpReqAlgebra:1474 *)
(*     载体实例供给形，T2b 报告五.5）；本件为其供给面 sum_pos 槽的        *)
(*     母本直喂形，Token 取任意 Set 载体 X、enum0 非空显式承载。          *)
(*   防重认领（20260919 实测）：Live_X 无 UpAblD1S1_*/UpAblD1S2_*/       *)
(*     UpAblP3S1_* 认领件；本槽 Live_X 无既有同槽放电件。               *)
(*   纪律：零 git、原树零改、前缀 uabd1s3_ 全树零撞名；                  *)
(*     文尾 Print Assumptions 收尾；G3 提取探针内嵌一人一目录            *)
(*     _tuabd1s3_g3out（验后判读）。四关留痕 attn/logs/g1..4-UpAblD1S3_* *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import S01_BaseRing.
Require Import fa57_ext.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_tempsoftmaxinst_carrier (RI0 : RealInterfaceEnhanced)
  (Tok : Set) (enum0 : list Tok) (Hne : Not (Id enum0 nil))
  : (Tok -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes Tok enum0 Hne).

Theorem uabd1s3_tempsoftmaxinst_Hsum_pos :
  forall (RI0 : RealInterfaceEnhanced) (Tok : Set) (enum0 : list Tok)
         (Hne : Not (Id enum0 nil)) (f : Tok -> @S01_BaseRing.R RI0),
    (forall w : Tok, @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f w)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_tempsoftmaxinst_carrier RI0 Tok enum0 Hne f).
Proof.
  intros RI0 Tok enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes Tok enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_tempsoftmaxinst_carrier.ml" uabd1s3_tempsoftmaxinst_carrier.

Print Assumptions uabd1s3_tempsoftmaxinst_Hsum_pos.
