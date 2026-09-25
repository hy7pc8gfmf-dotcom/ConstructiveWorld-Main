(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程包AA（tier2 十七批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabd1s3_tempsoftmaxinst_Hsum_pos（原 L33，2 句玩具证）               *)
(* ============================================================ *)
(* ============================================================ *)
(* 【 恒等守恒修订注记】 包AW十 （恒等头注修订全量第三批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 （包AL）全量恒等核查已证结论、（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此修订。                                        *)
(* 修订口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；记录册承载见  附录／ 修正块／ 评估册／／ 记录册。                   *)
(* 附记： 判级全文恒等；包AA A-L 包域（AA/AB/AC/AD）第三批整批直推（ 六·1 方案①）         *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblD1S3_sum_pos_TempSoftmaxInstantiation.v —— FA-D1S3 批 D1-⑤    *)
(*   sum_pos 完成批·件12                                                *)
(*   接口参数：TempSoftmaxInstantiation.v L239（Hsum_pos，RI 面，语句逐字）  *)
(*     forall f : Token -> R, (forall w : Token, lt zero (f w)) ->       *)
(*     lt zero (sumf f)                                                  *)
(*   实例化消解源文件（普查表钦定）：fa57_sum_carrier_realizes@fa57_ext.v:63     *)
(*     （E389/E703 sum_pos 槽完成 sigT 封装件）；本槽原世界即 RI 面      *)
(*     （Context {RI}），与源文件同面——零降级直接代入：sumf 槽取源文件          *)
(*     sigT 封装件 projT1 投影，槽语句由源文件 pos 组件（And 首字段        *)
(*     fst）逐字直接代入。                                                   *)
(*   本件语境注记：宿主件为 T2b 件1 槽11 已引用装配桥（UpReqAlgebra:1474 *)
(*     载体实例供给形，T2b 报告五.5）；本件为其供给面 sum_pos 槽的        *)
(*     源文件直接代入形，Token 取任意 Set 载体 X、enum0 非空显式承载。          *)
(*   防重认领（ 实测）：Live_X 无 UpAblD1S1_*/UpAblD1S2_*/       *)
(*     UpAblP3S1_* 认领件；本槽 Live_X 无既有同槽实例化消解件。               *)
(*   纪律：零 git、原树零改、前缀 uabd1s3_ 全树零撞名；                  *)
(*     文尾 Print Assumptions 收尾；G3 提取检验内嵌一人一目录            *)
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
