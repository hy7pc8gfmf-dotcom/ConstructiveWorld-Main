(* ==========================================================================)
   abl_tail_sum_readbridge.v — 批 5-1 施工席（基座区第五批·求和读法桥分件）
   ── 使命：基座区 12 宿主 46 槽（求和四性质 44 槽＋逐项零化 2 槽）之
      csm_sumf 实现化读法统一供给桥（下编册 §三批 5-1 施工令；卡 1 求和
      四槽族＋卡 2 逐项零化槽）。件内三段：
      （一）求和通用读法节 req/le 面四供给（tspbr_sum_ext／linear／add／
        le，exact 直引 cms_sum_ext／linear／add／le@ConcMixSelFeed）——
        服务 req/le 面八宿主 30 槽（SqrtfCauchyDischarge 四槽：46/:48/:51/
        :56、TempUnimodalMax 四槽：45/:47/:50/:55、TempSoftmaxInstantiation
        三槽：296/:299/:302、Arch_GibbsA_01 四槽：303/:305/:308/:311、
        EngelWeighted 四槽：536/:538/:541/:544、UpReqAlignClose 三槽：57/
        :59/:62、UpAblT1c_UpFirewallReq 四槽：90/:92/:95/:98、
        UpReqConcMixSel 四槽：714/:716/:719/:722）；
      （二）同读法节 real_eq/real_le 面四供给（tspbr_real_sum_ext／le／
        linear／add）——服务 real_eq 面宿主 10 槽（RealKLCorrMark 三槽：
        120/:122/:125、SecondLawQuantified 三槽：56/:58/:60、
        EntropyMonoSplitInst 四槽：63/:65/:67/:70）；UpReqEntropyMonoSplit
        四槽（135/:137/:139/:142）在件已供（urems_sum_* 同件 :757-790
        在役），本件零新增；
      （三）逐项零化槽 bool 二点枚举装配二件（tspbr_bool_two_enum_in_
        witness 满射前置直给＋tspbr_sum_zero_nonneg_bool 装配，exact 直引
        uabT1_rte_fsum_zero_nonneg@UpAblT1_UpReqTempEntropy）——服务
        SqrtfCauchyDischarge:58-60／TempUnimodalMax:57-59 逐字槽面
        （非负和归零⟹逐项归零形）之 bool 载体读法闭形。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqSumD（sumd_in
      成员谓词）、UpReqConcSoftmax（csm_sumf 载体）、ConcMixSelFeed
      （cms 四供给根件）、UpAblT1_UpReqTempEntropy（零化泛型件）、
      Stdlib List、Stdlib Extraction——全部只读引用；既有件零字节不动、
      零级联；12 宿主目标件本件零 Require（通用桥出节全参形，消费面
      下游读法接线经 Require 本件即取）。
   ── 对标行：读法配方正本＝BBDBridgeSupply.v:58-90（节参 :60-61＋
      Let sumf :64＋bbridge_sum_ext/linear/add_supply :69-90）；cms 四根件
      ＝ConcMixSelFeed.v:79-88（cms_sum_ext）／:90-117（cms_sum_linear）／
      :119-148（cms_sum_add）／:150-161（cms_sum_le）；零化泛型件＝
      UpAblT1_UpReqTempEntropy.v:108-117（uabT1_rte_fsum_zero_nonneg），
      根件＝sumd_sum_zero_nonneg_surj@UpReqSumD.v:520-525、成员谓词
      sumd_in@UpReqSumD.v:353-357；槽面现档＝下编册卡 1 十二宿主逐槽行号
      （本席 20261001 逐件复测零漂移）。
   ── 查重登记块（禁重复供给声明，R1 先例照办；开工前分工先勘实测）：
      在役重叠件四组逐条列坐标——①BBDBridgeSupply.v:69-90 bbridge_sum_
      ext/linear/add_supply（req 面 ext/linear/add 三件泛型在役，无 le）；
      ②UpReqSamplingFeed.v:83-89 usrq_sum_le_supply（le 面节内泛型在役）；
      ③abl_tail_supply_63.v 批二段／abl_tail_bridge_assembly.v 段一
      tsp_ems_sum_ext/le/linear/add（real_eq/real_le 面四件泛型在役）；
      ④abl_tail_bridge_assembly.v 段二 :213-227 tsp_bool_enum_sumd_in_
      witness＋tsp_sumd_sum_zero_nonneg_full_bool（零化 sumd 算子面全形
      在役）。本件为批 5-1 施工令所建十二宿主统一读法桥正体：req/le 面
      四件全齐（le 件为库内首件泛型全件之一）＋real 面四件全齐＋零化
      csm_sumf 读法槽面装配（④件为 sumd 算子面，本件按卡 2 配方取
      csm_sumf 槽面，两载体定义性同一：csm_sumf S en f 与 sumd_sumf S en
      f 均展开为 sumd_list_sum S f en）——重叠面逐条登记如上，下游消费
      面亦可直引在役件；非重复立项申报：施工令明文令建本批统一桥＋
      le/零化装配/real 面全齐为净新增，四步复核与蓝估 ~10 Qed 一致。
   ── 构造性注记：全件零承认式声明、零悬置前提、零经典逻辑；语句面承载
      位全 Set 形（req/le/real_eq/real_le 皆 Set 值谓词，零 Prop 泄露）；
      供给定理只消费在役已证根件，零接口外新前提；分级申报＝十件全 N1
      （库内实例化消解件直连：证明体非平凡内容在 cms 四件／uabT1 零化
      泛型件本体——列表归纳链与逐项零化链，本件直连不注水）；逐件
      Print Assumptions 取全 Closed 判据（名清单＝Qed 计数＝语句数，零
      差）；提取探针取库层转写与本件引入分开计数如实登记（对照实验口径）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532；道闸核 rocq 进程数 ≤1 方起编；单道顺序；
      nice -19 rocq c -native-compiler no -Q <统一缓存根> ""
      abl_tail_sum_readbridge.v（统一缓存只读指向，输出 .vo 落本池 cwd）；
      绿判四件套：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／
      vo 新于 v；rocqchk -o 环境摘要公理位 <none> 第五证。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前
      提、零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

(* ── Require 面：基座链库序＋本件直接消费件并集（去重；顺序＝依赖序） *)
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
Require Import ConcMixSelFeed.
Require Import UpAblT1_UpReqTempEntropy.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 段一＋段二：求和通用读法节（配方照抄 BBDBridgeSupply.v:60-64）     *)
(*   节参 S0:Set＋en:list S0，抽象求和槽取 csm_sumf S0 en 读法；        *)
(*   出节后十定理呈全参喂形（S0/en 显式参位，sumf 读法体内替换）。    *)
(* ============================================================ *)
Section TspbrSumReadBridge.

Variable S0 : Set.
Variable en : list S0.

(* 求和实现化读法：抽象 sumf 取 ConcMixSelFeed 列表折叠和 *)
Let sumf : (S0 -> Real) -> Real := csm_sumf S0 en.

(* ---- 段一：req/le 面四供给（req/le 面八宿主 30 槽逐字同形，binder      *)
(*      f g a 逐同名；exact 直引 cms 四根件） ---------------------------- *)

(* 供给一：求和外延（宿主槽形 forall f g, (forall s, req (f s) (g s)) ->   *)
(*   req (sumf f) (sumf g)；cms_sum_ext@ConcMixSelFeed.v:79-88 直引） *)
Theorem tspbr_sum_ext : forall f g : S0 -> Real,
  (forall s : S0, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* 供给二：求和左线性（cms_sum_linear@ConcMixSelFeed.v:90-117 直引） *)
Theorem tspbr_sum_linear : forall (a : Real) (f : S0 -> Real),
  req (sumf (fun s : S0 => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* 供给三：求和加法分解（cms_sum_add@ConcMixSelFeed.v:119-148 直引） *)
Theorem tspbr_sum_add : forall f g : S0 -> Real,
  req (sumf (fun s : S0 => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S0 en f g).
Qed.

(* 供给四：求和保序（cms_sum_le@ConcMixSelFeed.v:150-161 直引） *)
Theorem tspbr_sum_le : forall f g : S0 -> Real,
  (forall s : S0, le (f s) (g s)) -> le (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_le S0 en f g H).
Qed.

(* ---- 段二：real_eq/real_le 面四供给（RealKLCorrMark／                 *)
(*      SecondLawQuantified／EntropyMonoSplitInst 宿主面逐字同形；        *)
(*      证明体同 cms 四根件，req≡real_eq／le≡real_le 为                   *)
(*      RealEnhancedReal 实例字段投影的定义性归约） --------------------- *)

(* 供给五：real 面求和外延（RKC:120／SLQ:56／EMSI:63 槽面逐字同形） *)
Theorem tspbr_real_sum_ext : forall f g : S0 -> Real,
  (forall s : S0, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* 供给六：real 面求和保序（EMSI:65 槽面逐字同形） *)
Theorem tspbr_real_sum_le : forall f g : S0 -> Real,
  (forall s : S0, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_le S0 en f g H).
Qed.

(* 供给七：real 面求和左线性（RKC:125／SLQ:58／EMSI:67 槽面逐字同形） *)
Theorem tspbr_real_sum_linear : forall (a : Real) (f : S0 -> Real),
  real_eq (sumf (fun s : S0 => real_mult a (f s)))
          (real_mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* 供给八：real 面求和加法分解（RKC:122／SLQ:60／EMSI:70 槽面逐字同形） *)
Theorem tspbr_real_sum_add : forall f g : S0 -> Real,
  real_eq (sumf (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S0 en f g).
Qed.

End TspbrSumReadBridge.

(* ============================================================ *)
(* 段三：逐项零化槽 bool 二点枚举装配（卡 2 配方：满射前置直给＋        *)
(*       uabT1_rte_fsum_zero_nonneg 直引；槽面＝SCD:58-60／TUM:57-59     *)
(*       逐字（sumf 取 csm_sumf bool 二点枚举读法）                    *)
(* ============================================================ *)

(* 满射前置：bool 二点枚举（true :: false :: nil）的成员谓词直给
   （sumd_in 二支：头项 inl eq_refl／次项 inr (inl eq_refl)） *)
Lemma tspbr_bool_two_enum_in_witness : forall s : bool,
  sumd_in bool s (true :: false :: nil).
Proof.
  intro s.
  destruct s as [|].
  - exact (inl eq_refl).
  - exact (inr (inl eq_refl)).
Qed.

(* 逐项零化槽装配：逐点非负＋全和为零 ⟹ 逐项为零（SCD:58-60／
   TUM:57-59 槽面逐字，sumf := csm_sumf bool (true :: false :: nil)；
   exact 直引 uabT1_rte_fsum_zero_nonneg@UpAblT1_UpReqTempEntropy.v:
   108-117，csm_sumf 与 sumd_sumf 两载体定义性同一） *)
Theorem tspbr_sum_zero_nonneg_bool :
  forall f : bool -> Real,
    (forall s : bool, le zero (f s)) ->
    req (csm_sumf bool (true :: false :: nil) f) zero ->
    forall s : bool, req (f s) zero.
Proof.
  intros f Hnn H0 s.
  exact (@uabT1_rte_fsum_zero_nonneg Real RealEnhancedReal bool
           (true :: false :: nil)
           tspbr_bool_two_enum_in_witness f Hnn H0 s).
Qed.

(* ============================================================ *)
(* PA 收尾段（逐件 Closed 判读；名清单＝Qed 计数＝10＝语句数，零差）   *)
(* ============================================================ *)
Print Assumptions tspbr_sum_ext.
Print Assumptions tspbr_sum_linear.
Print Assumptions tspbr_sum_add.
Print Assumptions tspbr_sum_le.
Print Assumptions tspbr_real_sum_ext.
Print Assumptions tspbr_real_sum_le.
Print Assumptions tspbr_real_sum_linear.
Print Assumptions tspbr_real_sum_add.
Print Assumptions tspbr_bool_two_enum_in_witness.
Print Assumptions tspbr_sum_zero_nonneg_bool.

(* ============================================================ *)
(* 终段提取检验区（判据＝输出 Obj.magic 分段归桶如实登记；输出目录为    *)
(*   本池检验区；对照实验＝树外探针件单抽 cms_sum_ext 库件，库层转写    *)
(*   段同源复现即闭包固有，本件引入段分开计数）                        *)
(* ============================================================ *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspbr_sum_ext tspbr_sum_le
  tspbr_sum_zero_nonneg_bool.
