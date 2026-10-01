(* ==========================================================================)
   abl_tail_sum_pos_bridge.v — G1 sum_pos 类槽统一桥族·槽形传入延伸件
   ── 使命：64 件 tsp_sumd_sum_pos_of_enum_witness 已立「sigT 非空见证→sumd 载体槽形」
      泛型桥引擎；本件做其槽形传入延伸（非重复），四定理四面：（一）抽象算子传入形
      （RIS 面）：任意与 sumd 列表和逐点 req 同一的求和算子，持 sigT InT 非空见证即
      满足 tmw_sum_pos（PA_TempMonoW2Mark :50）／frd_sum_pos（Arch_PA_02 :898）／
      sum_pos（Arch_PA_04 :1354）三槽之逐字槽命题（sumd 实例闭形＝64 件在役，零重述）；
      （三）EMS 槽形传入＝real_sum_pos_preserved（ToyR_EntropyMonoSplitInst :121 与
      UpAblP6_EntropyMonoSplit_C :52 逐字双落）之 csm_sumf 读法 sigT 泛枚举形；
      （四）TSI 槽形传入＝Hsum_pos（PA_TempSoftmaxInstantiation :220）RI 桥面 sigT
      泛枚举形；（五）slc 槽形传入＝sumpos（PA_ToyR_SecondLawConsume :117 与
      Arch_ToyR_04 :79 逐字双落）real_list_sum 载体 sigT 泛枚举形。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqSumD（sumd 列表和机与 InT 成员
      承载）、UpReqConcSoftmax（csm_sumf 载体）、PA_TempSoftmaxInstantiation
      （tsi_rie_setoid RI 桥实例）、Stdlib List 与 Extraction——全部只读引用；目标件
      零字节不动、零级联；不 Require 批件。
   ── 对标行：泛型桥引擎＝tsp_sumd_sum_pos_of_enum_witness@abl_tail_supply_64.v:55-67；
      sigT 见证传入先例＝usrq_bs_sum_pos_supply@UpReqSamplingFeed.v:174-177；头尾分解根
      ＝sumd_list_sum_pos_cons@UpReqSumD.v:306-317；req 运输字段＝
      lt_id_r@S07_RealSetoidExpLog.v:7988；Real 列表和根＝real_list_sum_pos@
      S08_RealMainlineDPO.v:464；RI→RIS 桥＝tsi_rie_setoid@PA_TempSoftmaxInstantiation.v:52-67。
   ── 构造性注记：全件零承认式声明、零悬置前提、零经典逻辑；语句面承载位全 Set 形
      （sigT/InT 承载非空性，lt/req/real_lt 皆 Set 值谓词）；空表支由 InT 空归纳型
      构造性关闭（match 空支，照 64 件先例）；全部结论 Qed 真构造闭合；Print Assumptions
      全 Closed 判据；提取检验取库层转写与本件引入分开计数如实登记（G3 对照实验口径）。
   ── 编译配方：单道 nice -19 rocq c -native-compiler no -Q <统一缓存根> "" abl_tail_sum_pos_bridge.v；
      绿判：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v。
   ========================================================================== *)

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
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import PA_TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 条款照办）：                        *)
(*   sumd 载体 sigT 泛形＝tsp_sumd_sum_pos_of_enum_witness（64 件）在役，  *)
(*   本件零重述其语句；Not 非空形＝uabT1_rte_fsum_pos（UpAblT1）在役；     *)
(*   bool 二点具体实例＝uabp6c_sum_pos_supply（EMS_C 供给段 :455）在役；   *)
(*   cons 头见证形＝tsp_tsi_sum_pos_cons／tsp_slc_sum_pos_cons（65 件）    *)
(*   在役；Id 面 sigT 三性质封装＝fa57_sum_carrier_realizes（Arch_PA_02    *)
(*   :70）在役（Arch_Up_01 :481/:786 两槽已供，禁拆单重供）。本件四语句   *)
(*   （抽象算子传入形＋三面 sigT 泛枚举形）全库无同语句。                  *)
(* ============================================================ *)

(* ============================================================ *)
(* 一、泛型桥·抽象算子传入形（RIS 面）                                *)
(*    服务 tmw_sum_pos（PA_TempMonoW2Mark :50-51）／frd_sum_pos        *)
(*    （Arch_PA_02 :898-899）／sum_pos（Arch_PA_04 :1354）三槽：槽面    *)
(*    求和算子为节内抽象 Variable，使用面只需（a）sigT InT 非空见证，  *)
(*    （b）其算子与 sumd 列表和逐点 req 同一（取 sumd 实例时为自反），  *)
(*    即得槽命题逐字同形。非空支取头见证加 sumd_list_sum_pos_cons      *)
(*    头尾分解（usrq 先例配方），空表支由 InT 空归纳型构造性关闭。      *)
(* ============================================================ *)

Theorem tspb_sum_pos_slot_of_carrier_agree :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
    (sumf : (S -> R) -> R) (en : list S),
    sigT (fun t : S => InT t en) ->
    (forall f : S -> R, req (sumf f) (sumd_sumf S en f)) ->
    forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Proof.
  intros R RIS S sumf en W Hagree f Hpt.
  destruct W as [x Hx].
  destruct en as [| y t].
  - exact (match Hx with end).
  - apply (lt_id_r zero (sumd_sumf S (y :: t) f) (sumf f)).
    + exact (req_sym (sumf f) (sumd_sumf S (y :: t) f) (Hagree f)).
    + unfold sumd_sumf.
      exact (@sumd_list_sum_pos_cons R RIS S f y t Hpt).
Qed.

(* ============================================================ *)
(* 三、EMS 槽形传入（real_sum_pos_preserved 双落：                     *)
(*     ToyR_EntropyMonoSplitInst.v:121-123 ↔ UpAblP6_EntropyMonoSplit_C *)
(*     .v:52-54 逐字同面）                                            *)
(*    S 节参降格申报（Set 承载；Type 槽使用面取 Set 实例无碍），载体取  *)
(*    csm_sumf（与 63 件 EMS 四槽同载体同读法），结论面＝槽面 real_lt   *)
(*    real_zero 逐字形；非空性以 sigT InT 见证显式前提显状（二审卡 10  *)
(*    裁决「改写申报后可消解」之落地语句形）。                          *)
(* ============================================================ *)

Theorem tspb_ems_sum_pos_preserved_witness :
  forall (S : Set) (en : list S),
    sigT (fun t : S => InT t en) ->
    forall f : S -> Real,
      (forall s : S, real_lt real_zero (f s)) ->
      real_lt real_zero (csm_sumf S en f).
Proof.
  intros S en W f Hpt.
  destruct W as [x Hx].
  destruct en as [| y t].
  - exact (match Hx with end).
  - unfold csm_sumf.
    exact (@sumd_list_sum_pos_cons Real RealEnhancedReal S f y t Hpt).
Qed.

(* ============================================================ *)
(* 四、TSI 槽形传入（Hsum_pos：PA_TempSoftmaxInstantiation.v:220-221）  *)
(*    RI 桥面（类字段经 tsi_rie_setoid 实例解析，lt/zero 字段定义性直  *)
(*    引 @lt RI／@zero RI），逐点绑定名 w 照槽面；65 件 cons 头见证形   *)
(*    之 sigT 泛枚举延伸（任意非空 en，不限 w::rest）。                 *)
(* ============================================================ *)

Section TspbTsiPosSlotFeed.

Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable en : list Token.

Theorem tspb_tsi_Hsum_pos_witness :
  sigT (fun t : Token => InT t en) ->
  forall f : Token -> @S01_BaseRing.R RI,
    (forall w : Token, lt zero (f w)) -> lt zero (sumd_sumf Token en f).
Proof.
  intros W f Hpt.
  destruct W as [x Hx].
  destruct en as [| y t].
  - exact (match Hx with end).
  - unfold sumd_sumf.
    exact (@sumd_list_sum_pos_cons (@S01_BaseRing.R RI) (tsi_rie_setoid RI)
             Token f y t Hpt).
Qed.

End TspbTsiPosSlotFeed.

(* ============================================================ *)
(* 五、slc 槽形传入（sumpos 双落：PA_ToyR_SecondLawConsume.v:117-119 ↔  *)
(*     Arch_ToyR_04.v:79-81 逐字同面）                                 *)
(*    Real 层 real_list_sum 载体（S08 折叠和机），结论面＝槽面         *)
(*    real_lt real_zero 逐字形；S 节参降格申报（InT 承载位需 Set 承载， *)
(*    Type 槽使用面取 Set 实例无碍）；65 件 cons 形之 sigT 泛枚举延伸，  *)
(*    空否定支由 real_list_sum_pos 之 l 否定空前提位接入，InT 见证      *)
(*    构造性关闭之。                                                   *)
(* ============================================================ *)

Theorem tspb_slc_sumpos_witness :
  forall (S : Set) (en : list S),
    sigT (fun t : S => InT t en) ->
    forall f : S -> Real,
      (forall s : S, real_lt real_zero (f s)) ->
      real_lt real_zero (real_list_sum S f en).
Proof.
  intros S en W f Hpt.
  destruct W as [x Hx].
  apply (real_list_sum_pos S f en Hpt).
  intro Heq.
  rewrite Heq in Hx.
  exact (match Hx with end).
Qed.

(* ============================================================ *)
(* 六、PA 审计段（对照 Check 读面＋逐件 Closed 判读）                   *)
(* ============================================================ *)

(* 对照 Check：根件语句面读出（面型保真对照留痕） *)
Check sumd_sumf.
Check csm_sumf.
Check real_list_sum.
Check tsi_rie_setoid.
Check lt_id_r.
Check sumd_list_sum_pos_cons.

(* 前提面审计（逐件全 Closed 判据；名清单＝Qed 计数＝4，零差） *)
Print Assumptions tspb_sum_pos_slot_of_carrier_agree.
Print Assumptions tspb_ems_sum_pos_preserved_witness.
Print Assumptions tspb_tsi_Hsum_pos_witness.
Print Assumptions tspb_slc_sumpos_witness.

(* ============================================================ *)
(* 七、提取检验区（判据＝Obj.magic 库层转写与本件引入分开计数如实登记；  *)
(*   输出目录为本池检验区；对照实验＝树外检验件单抽 csm_sumf 库件，     *)
(*   同段 magic 复现即闭包固有，检验件与本件同名带 ctrl 后缀非交付件）  *)
(* ============================================================ *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspb_ems_sum_pos_preserved_witness
  tspb_slc_sumpos_witness.
