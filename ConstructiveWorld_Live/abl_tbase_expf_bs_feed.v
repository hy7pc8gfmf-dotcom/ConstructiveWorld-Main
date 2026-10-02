(* ==========================================================================)
   abl_tbase_expf_bs_feed.v — 基座区下编批 5-3 施工组（expf B 型输入＋RSQ bs
   三槽 cms 直引＋T1b sum_eq_list 桥，11 Qed）
   ── 使命：基座区存疑二审与施工说明（attn/_tbase100_存疑二审与施工说明.md
      §二 施工说明 5-3）逐行施工。段一 expf 组 7 件：Paper7Ablation §1（:43
      expf_pos／:46 expf_mono_lt）＋§2（:97 expf_mono_lt）、MixTimeChain §1
      （:76 expf_pos／:79 expf_mono_lt）、MixTimeChainIface（:67 expf_pos／
      :70 expf_mono_lt）七槽的 Real 特化闭形 B 型输入（层位注记沿上编卡 2
      定论口径：七宿主槽为 RI 类字段抽象位，消解形＝R:=Real 全参喂，使用位
      以实例充任接口字段，AMT amtr 形 :229-262 同款先例）；W 排除 6 位
      （P7A:44/:45/:96、MTC:77/:78、MTI:68/:69 的 Id 面 expf zero/plus 槽）
      零输入零触碰。段二 RSQ bs 组 3 件：UpReqConcMixSel ReqRowView 前节
      （:704-743，节自持 enum+enum_nonempty :729-730）的 bs_swap（:738-740）／
      bs_abs（:741）／sum_eq_list（:743）三槽，读法 sumf := csm_sumf S en
      （下编卡 1 同款），ConcMixSelFeed cms_ 系三根 exact 直引。段三 T1b
      sum_eq_list 组 1 件施工：UpAblT1b_AttnDoeblin AblSwap 节（:115-123）
      sum_eq_list 槽，idt_slot_attdoeblin 一步直引（SO 实例读法＝
      sum_over_S := idt_sumf enum，使用侧 idt 读法装载）；UpAblT1b_S13 同槽
      在件已供（ablq_sum_eq_list@UpAblT1b_S13_NLiveAudit.v:195-200），对接
      申报零新增。AMT 在件已供 4 位（amtr_expf_pos／amtr_expf_mono_lt／
      amtr_expf_mono_le／amtr_bs_swap）对接申报零新增。合计 11 Qed。
   ── 锚复拍登记（ 本文件 Live 现档实拍，施工说明行号零漂移零勘正）：
      P7A:43/:46/:97、MTC:76/:79、MTI:67/:70、UpReqConcMixSel:729-730/
      :738-740/:741/:743、UpAblT1b_AttnDoeblin:121-123、UpAblT1b_S13:111-112
      ＋ablq_sum_eq_list:195-200；根件锚＝uabd1x_expf@UpAblD1_expf_pack.v:28／
      uabd1x_expf_pos:48-49／uabd1x_expf_mono_lt:61-63、cms_sum_eq_list@
      ConcMixSelFeed.v:180-190／cms_bs_swap:194-197／cms_bs_abs:255-267、
      idt_slot_attdoeblin@IdSlotTranslate.v:156（语句 :156-158）。
   ── 依赖：S01_BaseRing、S02_CauchyComplete、S07_RealSetoidExpLog（勘正
      增补：RealInterfaceEnhancedMod 模块宿主件@:7934，Import 位必需；首编
      红判「Cannot find module」就地勘正留痕）、UpReqConcSoftmax（勘正增补：
      csm_sumf 定义宿主@:41，段二语句面必需；二编红判「reference not found」
      就地勘正留痕——Require Import 非传递，内层名不外浮）、UpReqSampling
      （勘正增补：rsq_bs_list_sum 定义宿主@:708，段二 2.3 语句面必需）、
      UpAblD1_expf_pack、ConcMixSelFeed、IdSlotTranslate、AttnDoeblin（全部
      在役只读；不 Require 任何池批件）；Import RealInterfaceEnhancedMod
      （req 面 bare 名解析，段二语句面与 cms_ 根同面）。七宿主目标件
      （Paper7Ablation／MixTimeChain／MixTimeChainIface／UpReqConcMixSel／
      UpAblT1b_AttnDoeblin／UpAblT1b_S13_NLiveAudit）零 Require、零字节不动、
      零级联。
   ── 对标行：模板＝本池 abl_tail_supply_67.v（段〇换名不换形＋exact 一击
      工艺＋PA/提取收尾段式）；Id 面全限定坑 5 处方与 @S RI SS 出节形＝
      本池 abl_tail_supply_68.v:85-94/:111-113；段三同槽既供先例＝
      ablq_sum_eq_list@UpAblT1b_S13_NLiveAudit.v:195-200（Live 在件）；
      查重登记（R1 条款）：四已供件（abls_/abla_/tspps_/tspbr_）与本件
      tspex_/tspbs_ 前缀全池 grep 零重叠（本文件实测），tspbl_（批 5-2 log 桥）
      与 abl_tbase_logbridge（上编批 2 log 桥）辖区＝log 域零交叠。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑；
      语句面承载位全 Set 形（real_lt/real_le/req/le/Id 皆 Set 值，零 Prop
      泄露；W 排除 6 位 Id 面槽零输入）；供给定理只使用已编在役内容
      （exact 直引），零接口外新前提；11 件 Print Assumptions 全 Closed
      判据；文件尾提取探查件三代表件取 Obj.magic 计 0 判据＋对照命令并排
      提取比对（G3 口径，如实登记禁虚报；若触提取器硬错，照池内豁免先例
      处置并逐条登记）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532 && cd 沙箱/现役/abl_tail_supply_pool；道闸核 rocq 进程
      ≤2 方起编；单道顺序；先写后编；
      nice -19 rocq c -native-compiler no -Q /Users/apple/Desktop/
      ConstructiveWorld/vo_local_world_unified_0930 "" abl_tbase_expf_bs_feed.v
      （统一缓存只读指向，输出 .vo 落本池 cwd；绿判四要素：EXIT=0／日志真
      错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v；rocqchk 第五证）。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpAblD1_expf_pack.
Require Import ConcMixSelFeed.
Require Import IdSlotTranslate.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 段〇 前置：函数实例（模板 67 换名不换形；                          *)
(*   uabd1x_expf@UpAblD1_expf_pack:28 定义性转写）                   *)
(* ============================================================ *)
Definition tspex_fn : Real -> Real := uabd1x_expf.

(* ============================================================ *)
(* 段一 expf 组（7 行，B 型 Real 特化闭形；每行 exact 一击直引         *)
(*   拆包件 uabd1x_expf_pos@:48-49／uabd1x_expf_mono_lt@:61-63）      *)
(* ============================================================ *)

(* ---- 1.1 Paper7Ablation §1（:38-46 节）expf_pos 槽（:43） ---- *)
Theorem tspex_p7a1_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 1.2 Paper7Ablation §1 expf_mono_lt 槽（:46） ---- *)
Theorem tspex_p7a1_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 1.3 Paper7Ablation §2（:92-97 节）expf_mono_lt 槽（:97） ---- *)
Theorem tspex_p7a2_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 1.4 MixTimeChain §1（:71-79 节）expf_pos 槽（:76） ---- *)
Theorem tspex_mtc_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 1.5 MixTimeChain §1 expf_mono_lt 槽（:79） ---- *)
Theorem tspex_mtc_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 1.6 MixTimeChainIface（:60-70 节）expf_pos 槽（:67） ---- *)
Theorem tspex_mti_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 1.7 MixTimeChainIface expf_mono_lt 槽（:70） ---- *)
Theorem tspex_mti_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ============================================================ *)
(* 段二 RSQ bs 组（3 行，B 型 cms 读法；读法＝sumf := csm_sumf S en，   *)
(*   下编卡 1 同款；宿主＝UpReqConcMixSel ReqRowView 前节 :704-743，   *)
(*   节自持 enum+enum_nonempty :729-730（bs 三槽使用面本持非空 datum，  *)
(*   喂形零额外前提——勘 D）；三根＝ConcMixSelFeed cms_ 系 exact 直引） *)
(* ============================================================ *)

(* ---- 2.1 UpReqConcMixSel bs_swap 槽（:738-740）；根＝cms_bs_swap ---- *)
(* ----    @ConcMixSelFeed.v:194-197（双列表泛型换序归纳）          ---- *)
Theorem tspbs_rsq_bs_swap :
  forall (S0 : Set) (en : list S0) (f : S0 -> S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => csm_sumf S0 en (fun s' : S0 => f s s')))
        (csm_sumf S0 en (fun s' : S0 => csm_sumf S0 en (fun s : S0 => f s s'))).
Proof. exact cms_bs_swap. Qed.

(* ---- 2.2 UpReqConcMixSel bs_abs 槽（:741）；根＝cms_bs_abs ---- *)
(* ----    @ConcMixSelFeed.v:255-267（real_lt 支 abs 正形＋req 支换面） ---- *)
Theorem tspbs_rsq_bs_abs : forall a : Real, le zero a -> req (abs a) a.
Proof. exact cms_bs_abs. Qed.

(* ---- 2.3 UpReqConcMixSel sum_eq_list 槽（:743）；根＝cms_sum_eq_list ---- *)
(* ----    @ConcMixSelFeed.v:180-190（两折叠机器同构归纳件；宿主      ---- *)
(* ----    rsq_bs_list_sum@UpReqSampling.v:708 与 csm_sumf 折叠同构） ---- *)
Theorem tspbs_rsq_sum_eq_list :
  forall (S0 : Set) (en : list S0) (g : S0 -> Real),
    req (csm_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof. exact cms_sum_eq_list. Qed.

(* ============================================================ *)
(* 段三 T1b sum_eq_list 组（1 行施工＋1 行对接申报）                  *)
(*   3.1 施工件：UpAblT1b_AttnDoeblin AblSwap 节（:115-123）          *)
(*   sum_eq_list 槽——槽语句面 forall g, Id (sum_over_S g)             *)
(*   (AttnDoeblin.bs_list_sum g enum)，SO 实例读法＝                  *)
(*   sum_over_S := idt_sumf enum（使用侧 idt 读法装载）；本件取       *)
(*   enum 升格显式全称的更强诚实形（IdSlotTranslate :150-155 件内     *)
(*   用法注记同款），idt_slot_attdoeblin（:156-162）一步直引。        *)
(*   3.2 对接申报（零新增 Qed）：UpAblT1b_S13_NLiveAudit 同槽         *)
(*   已在件自供 ablq_sum_eq_list（:195-200，语句同形，                *)
(*   exact (idt_slot_attdoeblin enum g) 一步），使用对接即清。        *)
(*   Id 面全限定＝坑 5 处方（abl_tail_supply_68.v:85-94 先例）。      *)
(* ============================================================ *)
Theorem tspbs_t1b_sum_eq_list :
  forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI}
         (enum : list (@S RI SS)) (g : @S RI SS -> @R RI),
    S01_BaseRing.Id (@idt_sumf RI SS enum g)
                    (@AttnDoeblin.bs_list_sum RI SS g enum).
Proof.
  intros RI SS enum g.
  exact (idt_slot_attdoeblin enum g).
Qed.

(* ============================================================ *)
(* 段四 收尾一：11 件前提面审计（全 Closed 判据；名清单＝Qed 计数＝    *)
(*   PA 语句数 11，零差）                                            *)
(* ============================================================ *)
Print Assumptions tspex_p7a1_expf_pos.
Print Assumptions tspex_p7a1_expf_mono_lt.
Print Assumptions tspex_p7a2_expf_mono_lt.
Print Assumptions tspex_mtc_expf_pos.
Print Assumptions tspex_mtc_expf_mono_lt.
Print Assumptions tspex_mti_expf_pos.
Print Assumptions tspex_mti_expf_mono_lt.
Print Assumptions tspbs_rsq_bs_swap.
Print Assumptions tspbs_rsq_bs_abs.
Print Assumptions tspbs_rsq_sum_eq_list.
Print Assumptions tspbs_t1b_sum_eq_list.

(* ============================================================ *)
(* 段四 收尾二：提取检验区（三代表件：expf 直引／bs_swap 直引／       *)
(*   t1b Id 桥；判据＝Obj.magic 计 0；对照命令＝三根原身并排提取，    *)
(*   计数比对＝本件零新增口径，G3 对照实验口径如实登记禁虚报；        *)
(*   若触提取器硬错，照池内豁免先例处置并逐条登记）                   *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Recursive Extraction tspex_fn.
Recursive Extraction tspbs_rsq_bs_swap.
Recursive Extraction tspbs_t1b_sum_eq_list.
Recursive Extraction uabd1x_expf_pos cms_bs_swap idt_slot_attdoeblin.

(* 终验实测登记（ 本文件如实登记禁虚报）：
   编译 EXIT=0；日志真错行计 0（禁词锚 ^Error|Error: 计 0）；11 件 Print
   Assumptions 全 Closed（计 11＝Qed 计数零差）；.vo 头 8 字节
   436f7121 00015ff4 在案；rocqchk 第五证 EXIT=0。
   提取 Obj.magic 分解归桶（G3 对照实验口径，§4）：全日志计 142 处，分段
   ＝探查件一 tspex_fn（cauchy 闭包）0 处＋探查件二 tspbs_rsq_bs_swap（swap
   闭包）71 处＋探查件三 tspbs_t1b_sum_eq_list（idt 闭包）0 处＋对照命令
   （三根复提）71 处；独立对照探查件 probe_b53_g3ctrl（roots-only 三根原身
   单抽）实测 71 处，与池内在役判例数（cms_sum_ext 提取复现 71 处）精确
   同数——71 处＝在役根闭包（swap 证明体 Q/regularize 机器）固有位点，
   本日志 142＝该 71 位点经四条提取命令对同闭包两轮重复印刷，零新增位点；
   本件三代表件提取体均为指针别名（tspex_fn＝uabd1x_expf／
   tspbs_rsq_bs_swap＝cms_bs_swap／tspbs_t1b_sum_eq_list＝idt_slot_attdoeblin），
   本件语句面新增 Obj.magic＝0、新增 cast/见证转写＝0。豁免登记三要件
   （对照实验实证＋PA Closed 双证＋本条如实登记）齐备。
   提取器按旁路不透明设定访问了依赖闭包内既证定理体（标准告警
   extraction-opaque-accessed，池内 67 号件同形），仅告警面、非承认面。 *)
