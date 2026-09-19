(* ============================================================ *)
(* UpAblD1S3_sum_pos_UpReqAlignClose.v —— FA-D1S3 批 D1-⑤ sum_pos 收官批      *)
(*   槽位：UpReqAlignClose.v L42（sum_pos，req 载体层，语句逐字）          *)
(*     forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f) *)
(*   放电母本（普查表钦定）：fa57_sum_carrier_realizes@fa57_ext.v:63    *)
(*     （E389/E703 sum_pos 槽收官 sigT 打包件，pos/ext/linear 三组件）  *)
(*   消融形态：聚合引用形（扩槽不重立）——载体实例供给形：               *)
(*     R 取典范载体、RIS 取装配桥 tsi_rie_setoid（req 取 S01 集合层幺等， *)
(*     lt/zero 逐字段同源）、sumf 取母本 sigT 打包件 projT1 投影；       *)
(*     槽语句经装配桥逐位可转换，由母本 pos 组件（And 首字段 fst）直喂。 *)
(*   诚实降级登记（T2b 五.5 同款）：抽象 R/RIS/sumf 接口内不消解，       *)
(*     典范载体上成立；E751-A 口径逐槽登记。                            *)
(*   防重认领（20260919 实测）：Live_X 无 UpAblD1S1_*/UpAblD1S2_*/       *)
(*     UpAblP3S1_* 认领件；本槽 Live_X 无既有同槽放电件。               *)
(*   纪律：零 git、原树零改、前缀 uabd1s3_ 全树零撞名；                  *)
(*     文尾 Print Assumptions 收尾；G3 提取探针内嵌一人一目录            *)
(*     _tuabd1s3_g3out（验后判读）。四关留痕 attn/logs/g1..4-UpAblD1S3_* *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import S01_BaseRing.
Require Import fa57_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_upreqalignclose_carrier (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (Hne : Not (Id enum0 nil))
  : (X -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes X enum0 Hne).

Theorem uabd1s3_upreqalignclose_sum_pos :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (Hne : Not (Id enum0 nil)) (f : X -> @S01_BaseRing.R RI0),
    (forall s : X,
       @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
         (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
         (@RealInterfaceEnhancedMod.zero (@S01_BaseRing.R RI0)
            (TempSoftmaxInstantiation.tsi_rie_setoid RI0)) (f s)) ->
    @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI0)
      (TempSoftmaxInstantiation.tsi_rie_setoid RI0)
      (@RealInterfaceEnhancedMod.zero (@S01_BaseRing.R RI0)
         (TempSoftmaxInstantiation.tsi_rie_setoid RI0))
      (uabd1s3_upreqalignclose_carrier RI0 X enum0 Hne f).
Proof.
  intros RI0 X enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes X enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqalignclose_carrier.ml" uabd1s3_upreqalignclose_carrier.

Print Assumptions uabd1s3_upreqalignclose_sum_pos.
