(* ==========================================================================)
   abl_tbase_tempsum.v — 基座区上编假设消解战役·上编批 5 施工席（UB5）
   （Real 面抽象求和接口族喂形供给件·温度族首攻＋同形宿主顺带）
   ── 使命：上编三态定谳册（20261001，attn/_tbase100_ 系）§二卡 1 F1
      sumf 六性质族「可消解」槽之 Real 面余段（覆盖图 §增补·第五批 ④
      余量算式「上编余 133（F1 余 64…）」辖区），抽象求和载体
      real_sum_over_S 取 S08_RealListSumMain 节 real_list_sum X f l
      （X : Type 逐字同面，Fixpoint fold real_plus，nil→real_zero）
      定义性实例化读法，四性质桥（ext/add/linear/le）＋pos cons 头
      见证喂形共 5 件，闭十文件十三节 48 槽：
      〔温度族六件八节〕UpReqTempDefs.v RealTempDefs（pos:95/ext:98/
        linear:100/add:102）、UpReqEntropyDeficitTemp.v
        RealEntropyDeficitTemp（:171/:174/:176/:179）、
        UpReqEntropyMaxTemp.v RealEntropyMaxTemp（pos:136/ext:139/
        le:143/linear:145/add:148）、UpReqTempDual.v RealTempDual
        （:36/:39/:41/:44）、UpReqEntropyUniqueNeg.v 双节
        RealEntropyUniqueTemp（:105/:108/:110/:113）＋
        RealEntropyUniqueNeg（:901/:904/:906/:909）、UpReqTopKTVChain.v
        双节 RealTopKTVChain（ext:112/add:115/le:118）＋
        RealTopKTVFinish（ext:385/add:388/linear:391）；
      〔同形宿主顺带五节〕G06_BForm.v RealPPOLeBFull（ext:53/le:55/
        add:57/linear:61；pos 槽已退场件内注 :64，本件零触碰）、
        G02_Debt.v RealScaleDual（pos:220/ext:223/linear:225）＋
        RealAttnGibbsTemp（pos:545/ext:548/linear:550）、UpRealLeB.v
        RealPPOLeB（ext:382/le:384/add:386/linear:389）、
        UpReqRealFEP.v RFEPMain（ext:121/add:123/linear:127）。
      零新增登记三件（在役/在件已供，本件零重复）：UpReqTempEntropy.v
      fsum 六槽＝uabT1_rte_fsum_*@UpAblT1_UpReqTempEntropy.v:56-113 在
      役；UpReqSteadyThermo.v ext/linear＝sts_sum_*_supply@:123-141 在
      件；G13 系/BoltzmannBridgeDischarge req 面三槽组＝uabT1 泛型同形
      在役覆盖。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、S08_RealListSumMain
      节 real_list_sum 五根（ext:296/add:341/linear:363/le:433/
      pos:464）、Stdlib List/Extraction——全部只读引用；十三宿主目标
      件零 Require、零字节不动、零级联（基座冻结域外置供给零级联合
      法；W 槽/存疑槽/冻结件语义位零触碰）。
   ── 对标行：供给根＝real_list_sum_ext@S08_RealMainlineDPO.v:296／
      real_list_sum_add@:341／real_list_sum_linear@:363／
      real_list_sum_le@:433／real_list_sum_pos@:464（X : Type 载体
      与温度宿主 S : Type 逐字同面，Set 降格问题不发生）；读法先例＝
      G06_BForm.v:129-160（件内自证「载体勘定：RealListSumMain 节
      real_list_sum」＋:146 直接消费 real_list_sum_pos）＋
      UpReqRealFEP.v:126（宿主件内自证「real_list_sum_linear（在案），
      具体实例可显式应用」）；载体代换喂形先例＝UpReqSteadyThermo.v
      SteadyThermoSumSlotsSupply:118-141（「语句与原假设位逐字同型
      （载体代换 real_sum_over_S := csm_sumf S0 enum）」件内注记在
      档，本件同款流程改取 X : Type 同面根）；cons 头见证申报位先例＝
      tspps_uralign_sum_pos_cons@abl_tail_pos_supply_sum.v:146-154；
      查重登记＝池内 tspps_（req 面 UpReqAlign/UpReqDist/UpFirewall/
      AlignRestA 七段）/tspbr_（req+real 面 SCD/TUM/TSI/GA2/EW/UAC/
      T1C/URCM/RKC/SLQ/EMSI 十二宿主）/tblb_/tspbl_/tblr_/tbex_ 系全
      语句名清单 20261002 实拍对表零交集（real_list_sum X 读法位与
      csm_sumf S0 读法位宿主面不相交）；配方细节＝沙箱/现役/
      abl_tail_supply_pool/_log/供给件配方笔记-20260930.md。
   ── 构造性注记：全件 Qed 真构造（S08 五根为列表归纳真证，本件
      exact 直引零注水）；语句面承载位全 Set 形（real_eq/real_le/
      real_lt 为 Real 接口 Set 值谓词，列表 cons 数据形承载，全文件
      零 Prop 位——real_list_sum_pos 之 l <> nil 前提仅在证明体内以
      cons 头见证消解，语句面零 Prop，申报位见 pos 段注记）；宿主
      pos 槽无前提位：非空见证以枚举 w::rest 数据形承载（申报位，
      非静默增补）；F13 Type 载体位照现档 `S : Type` 逐字抄（二审
      册①条款：供给定理按现档逐字，施工不受阻）；逐件 Print
      Assumptions 取全 Closed 判据；段内提取探针取 Obj.magic 分段归
      位如实登记口径（库层转写与本件引入分开计数）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532；道闸 rocq 进程数 ≤2 方起编（主会话 rocqchk
      全树在飞时 sleep 60 等窗），单道顺序；
      nice -19 rocq c -native-compiler no -Q <统一缓存根> ""
      abl_tbase_tempsum.v（统一缓存只读指向，输出 .vo 落本池 cwd）；
      绿判四件套：EXIT=0／日志真错行 0（锚 `^Error|Error:`，坑 1
      口径）／vo 头 8 字节 436f7121 00015ff4／vo 新于 v；rocqchk
      环境摘要公理位 <none> 第五证。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬
      置前提、零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

(* ── Require 面：基座链库序（顺序＝依赖序）。十三宿主目标件零
   Require（槽级供给定理只对表槽语句面，不经宿主模块——目标件零字节
   不动承诺的直接实现）。 *)
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
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 分级申报（全件六件同一判词）：N1——库内实例化消解件直连            *)
(* （real_list_sum 五根@S08_RealListSumMain 在役，本件逐桥具名喂位，  *)
(* exact 一步直引）；逐桥语句面＝宿主槽现档逐字抽取（含参序／命名／   *)
(* 隐式位；G02 两节 `fun s =>` 省略注记与宿主他节 `fun s : S =>` 为   *)
(* 解析糖同项，坑 4 三面对拍在案），real_sum_over_S 位取              *)
(* real_list_sum S en 实例化读法（X : Type 与宿主 S : Type 逐字同面，  *)
(* 载体代换先例＝UpReqSteadyThermo SteadyThermoSumSlotsSupply）。      *)
(* ============================================================ *)

(* ---- 桥一：求和外延（宿主槽 real_sum_over_S_ext 逐字；                *)
(*      TempDefs:98/EDT:174/EMT:139/TempDual:39/EUTemp:108/EUNeg:904/   *)
(*      TKTV:112/TKTVF:385/G06:53/G02:223/:548/UpRealLeB:382/RFEP:121   *)
(*      十三节同形；根 real_list_sum_ext@S08:296 直引） ---- *)
Theorem tspt_rsum_ext :
  forall (S : Type) (en : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f en) (real_list_sum S g en).
Proof.
  intros S en f g H.
  exact (real_list_sum_ext S f g en H).
Qed.

(* ---- 桥二：求和加法分解（宿主槽 real_sum_over_S_add 逐字；            *)
(*      TempDefs:102/EDT:179/EMT:148/TempDual:44/EUTemp:113/EUNeg:909/  *)
(*      TKTV:115/TKTVF:388/G06:57/UpRealLeB:386/RFEP:123 十一节同形；   *)
(*      根 real_list_sum_add@S08:341 直引） ---- *)
Theorem tspt_rsum_add :
  forall (S : Type) (en : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) en)
            (real_plus (real_list_sum S f en) (real_list_sum S g en)).
Proof.
  intros S en f g.
  exact (real_list_sum_add S f g en).
Qed.

(* ---- 桥三：求和左线性（宿主槽 real_sum_over_S_linear 逐字；           *)
(*      TempDefs:100/EDT:176/EMT:145/TempDual:41/EUTemp:110/EUNeg:906/  *)
(*      TKTVF:391/G06:61/G02:225/:550/UpRealLeB:389/RFEP:127 十二节     *)
(*      同形；根 real_list_sum_linear@S08:363 直引） ---- *)
Theorem tspt_rsum_linear :
  forall (S : Type) (en : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) en)
            (real_mult a (real_list_sum S f en)).
Proof.
  intros S en a f.
  exact (real_list_sum_linear S a f en).
Qed.

(* ---- 桥四：求和保序（宿主槽 real_sum_over_S_le 逐字；                 *)
(*      EMT:143/TKTV:118/G06:55/UpRealLeB:384 四节同形；                 *)
(*      根 real_list_sum_le@S08:433 直引） ---- *)
Theorem tspt_rsum_le :
  forall (S : Type) (en : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f en) (real_list_sum S g en).
Proof.
  intros S en f g H.
  exact (real_list_sum_le S f g en H).
Qed.

(* ---- 桥五：求和正性 cons 头见证喂形（宿主槽 real_sum_pos_preserved    *)
(*      逐字＋申报位：宿主槽无前提位，非空见证以枚举 w::rest 数据形      *)
(*      承载，w::rest 即见证本身，语句面零 Prop；根                      *)
(*      real_list_sum_pos@S08:464 之 l <> nil 前提在证明体内以 cons      *)
(*      头数据消解（:: 对 [] 构造子冲突 discriminate 一击）；八节同形    *)
(*      ＝TempDefs:95/EDT:171/EMT:136/TempDual:36/EUTemp:105/EUNeg:901/  *)
(*      G02:220/:545）                                                   *)
Theorem tspt_rsum_pos_cons :
  forall (S : Type) (f : S -> Real) (w : S) (rest : list S),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S f w rest H.
  apply (real_list_sum_pos S f (w :: rest) H).
  intro Hn.
  discriminate Hn.
Qed.

(* ============================================================ *)
(* PA 审计段（逐件全 Closed 判据；名清单＝Qed 计数＝5，零差）          *)
(* ============================================================ *)
Print Assumptions tspt_rsum_ext.
Print Assumptions tspt_rsum_add.
Print Assumptions tspt_rsum_linear.
Print Assumptions tspt_rsum_le.
Print Assumptions tspt_rsum_pos_cons.

(* ============================================================ *)
(* 提取检验区（判据＝Obj.magic 库层转写与本件引入分开计数如实登记；     *)
(*   三代表桥覆盖三种语句族：ext 直引／linear 逐项形／pos cons 形；     *)
(*   若触提取器硬错或记录层转写非零，照池内 63/68 先例对照实验口径      *)
(*   处置并逐条登记，禁虚报通过）                                       *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspt_rsum_ext tspt_rsum_linear tspt_rsum_pos_cons.
