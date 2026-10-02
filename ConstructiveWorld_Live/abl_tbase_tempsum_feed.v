(* ==========================================================================)
   abl_tbase_tempsum_feed.v — 基座区上编假设消解战役·上编批 6 施工席（UB6）
   （F1 温度族 Real 面 per-宿主具名喂形供给件：UpReqTempDefs／
     UpReqEntropyDeficitTemp／UpReqEntropyMaxTemp／UpReqTempDual 四宿主
     pos/ext/linear/add（＋EMT le 扩槽）共 17 槽）
   ── 使命：UB1 交付报告（_log/UB1_批1交付报告-20261001.md）勘 5＋§五未及
      项候续批清单逐落位具名施工——温度族八件 Real 面槽组「泛型根全在役、
      per-宿主具名喂形件未立」，本件补立其前四宿主段（EUN 双节／TopKTVChain
      双节／G02 双节留余量，见交付报告 §五）。B 型喂形：宿主节内抽象
      real_sum_over_S 取 real_list_sum S l 读法（S08 RealListSumMain
      X : Type 全型泛型列表折叠和——温度族宿主 S : Type 载体逐字匹配，
      uabt4 同款载体、X:Set→S:Type 升档），槽语句面以现档源码逐字实拍。
   ── 锚复拍登记（20261002 UB6 席 Live 现档 sed/grep 实拍，禁转抄）：
      （一）UpReqTempDefs.v Section RealTempDefs（:90）四槽：
        real_sum_pos_preserved :95-97／real_sum_over_S_ext :98-99／
        real_sum_over_S_linear :100-101／real_sum_over_S_add :102-104；
      （二）UpReqEntropyDeficitTemp.v Section RealEntropyDeficitTemp（:167）
        四槽：pos :171-173／ext :174-175／linear :176-178／add :179-181；
      （三）UpReqEntropyMaxTemp.v Section RealEntropyMaxTemp（:132）五槽：
        pos :135-137／ext :138-139／le（扩槽，件内自证「real_list_sum_le，
        S08 L421 在库」:140-141 实拍）:142-143／linear :144-146／add :147-149；
      （四）UpReqTempDual.v Section RealTempDual（:32）四槽：
        pos :36-38／ext :39-40／linear :41-43／add :44-46。
      四宿主四形槽面逐字同构（本席并排 diff 实拍）；根件锚＝
      real_list_sum@S08_RealMainlineDPO.v:291（Section RealListSumMain
      :287，Variable X : Type :288）／real_list_sum_ext :295 区／
      real_list_sum_add :334 区／real_list_sum_linear :363 区／
      real_list_sum_le :432 区／real_list_sum_pos :464-468（非空前提
      「l <> nil」形）。本席 grep 复拍零漂移零勘正。
   ── W/存疑排除登记（零触碰）：F13 Type 载体位按现档 : Type 逐字抄
      （定谳册卡 F13 行「施工不受阻」条款；Set 降格＝治理波 C3 硬前置，
      本件零涉）；四宿主 T/T_pos/energy/Z 套＝真-数据证书位（卡 9/卡 16）
      零触碰；Gibbs/le_linear 墙形槽本件零发件；UpRealLeB/UpRealLeB2
      勘槽＝UB1 §五「待二审席面分拣」位零触碰。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、S08_RealMainlineDPO
      （RealListSumMain 六根）、Stdlib List/Extraction（段内）——全部只读
      引用；四宿主目标件零 Require、零字节不动、零级联（基座冻结域外置
      供给零级联合法）。
   ── 对标行：uabt4_sum_carrier4_realized@UpAblT4_SumCarrier.v:55-77
      （同一载体 real_list_sum 的 sigT 兑现包先例，X : Set；其非空前提
      基座 Not/Id→in-tree <> 消去桥 :62-65 本件逐字承袭）；uabT1_rte_
      fsum_*@UpAblT1_UpReqTempEntropy.v:56-117（req 面 per-宿主具名喂形
      体例正本）；tsp_slc 系@abl_tail_sum_family.v:423-463（S:Type Real
      面泛型根，勘 5 在役）；查重登记＝UB1 勘 5（温度族 Real 面泛型根
      le/ext/add/pos 已在役，per-宿主具名喂形件未立＝本件唯一新增面）＋
      防重复审计-20261002（温度族 Real 面在役辖区零交叠）——本件四宿主
      per-宿主具名落位均不在上列在役辖区，零重复立项。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典
      逻辑；语句面承载位全 Set 形（real_eq/real_lt/real_le 为 S02/S07
      Set 值谓词；非空前提＝基座 Set 面 Not (Id l nil)，fa51:145／
      abls 域内先例同形）；pos 槽宿主无前提位：非空见证前提为数学必需
      （空枚举和＝real_zero，real_lt real_zero real_zero 构造性不可证）
      ——增补前提申报位（禁静默增补，SumDCarrierFeed:106-109 判词同源），
      消费位按 cons 头见证或 bool 二点枚举装载即合；供给定理只消费供给
      根件已导出内容，零接口外新前提。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532；道闸 rocq 进程数 ≤2 方起编、单道顺序；
      nice -19 rocq c -native-compiler no -Q <统一缓存根> ""
      abl_tbase_tempsum_feed.v（统一缓存只读指向，输出 .vo 落本池 cwd）；
      绿判四件套：EXIT=0／日志真错行 grep -Eq '^Error|Error:' 计 0／
      vo 头 8 字节 436f7121 00015ff4／vo 新于 v；rocqchk 第五证。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置
      前提、零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

(* ── Require 面：基座链库序（顺序＝依赖序）。四宿主目标件零 Require
   （槽级供给定理只对表槽语句面，不经宿主模块——目标件零字节不动承诺的
   直接实现）。 *)
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
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 分级申报（段级，全件 17 槽同一判词）：N1——库内实例化消解件直连     *)
(* （real_list_sum_* 六根@S08 RealListSumMain 在役，本件逐落位具名喂位，  *)
(* 证明体 exact 一步直引＋pos 位非空桥一步，零注水）；pos 非空前提增补   *)
(* 申报位见头注构造性注记。逐槽语句面＝四宿主现档逐字抽取（含参序／      *)
(* 命名／隐式位），real_sum_over_S 位取 real_list_sum S l 实例化读法。   *)
(* ============================================================ *)

(* ============================================================ *)
(* 段一：UpReqTempDefs.v Section RealTempDefs 四槽（现档 :90-104 实拍：  *)
(*   载体位 real_sum_over_S :94；pos :95／ext :98／linear :100／add :102） *)
(* ============================================================ *)

(* ---- 槽 real_sum_pos_preserved（:95-97 逐字：forall (f : S -> Real),
        (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero
        (real_sum_over_S f)；sumf 位＝real_list_sum S (w::rest) 读法；
        非空性以 cons 头见证数据承载（tspps cons 形先例：S : Type 载体
        下基座 Not (Id l nil) 不合型——Id 载体位 Set 约束，本席探针
        probe 实证——故取零 Prop 位数据形，增补申报位） ---- *)
Theorem tbtf_tdefs_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

(* ---- 槽 real_sum_over_S_ext（:98-99 逐字） ---- *)
Theorem tbtf_tdefs_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

(* ---- 槽 real_sum_over_S_linear（:100-101 逐字） ---- *)
Theorem tbtf_tdefs_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

(* ---- 槽 real_sum_over_S_add（:102-104 逐字） ---- *)
Theorem tbtf_tdefs_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* ============================================================ *)
(* 段二：UpReqEntropyDeficitTemp.v Section RealEntropyDeficitTemp 四槽   *)
(* （现档 :167-181 实拍：载体位 :170；pos :171／ext :174／linear :176／  *)
(*  add :179；四形槽面与段一逐字同构——本席并排实拍）                   *)
(* ============================================================ *)

Theorem tbtf_edt_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_edt_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

Theorem tbtf_edt_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_edt_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* ============================================================ *)
(* 段三：UpReqEntropyMaxTemp.v Section RealEntropyMaxTemp 五槽（现档      *)
(*  :132-149 实拍：载体位 :134；pos :135／ext :138／le 扩槽 :142（件内    *)
(*  自证「具体载体实例……real_list_sum_le，S08 L421 在库」:140-141）／    *)
(*  linear :144／add :147）                                            *)
(* ============================================================ *)

Theorem tbtf_emt_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_emt_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

(* ---- 扩槽 real_sum_over_S_le（:142-143 逐字；根件件内自证位） ---- *)
Theorem tbtf_emt_sum_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_le S f g l H).
Qed.

Theorem tbtf_emt_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_emt_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* ============================================================ *)
(* 段四：UpReqTempDual.v Section RealTempDual 四槽（现档 :32-46 实拍：    *)
(*  载体位 :35；pos :36／ext :39／linear :41／add :44；四形槽面与段一     *)
(*  逐字同构——本席并排实拍）                                           *)
(* ============================================================ *)

Theorem tbtf_tdu_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_tdu_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

Theorem tbtf_tdu_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_tdu_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* ============================================================ *)
(* PA 收尾段（逐件 Closed 判读，十七件）                                *)
(* ============================================================ *)
Print Assumptions tbtf_tdefs_sum_pos.
Print Assumptions tbtf_tdefs_sum_ext.
Print Assumptions tbtf_tdefs_sum_linear.
Print Assumptions tbtf_tdefs_sum_add.
Print Assumptions tbtf_edt_sum_pos.
Print Assumptions tbtf_edt_sum_ext.
Print Assumptions tbtf_edt_sum_linear.
Print Assumptions tbtf_edt_sum_add.
Print Assumptions tbtf_emt_sum_pos.
Print Assumptions tbtf_emt_sum_ext.
Print Assumptions tbtf_emt_sum_le.
Print Assumptions tbtf_emt_sum_linear.
Print Assumptions tbtf_emt_sum_add.
Print Assumptions tbtf_tdu_sum_pos.
Print Assumptions tbtf_tdu_sum_ext.
Print Assumptions tbtf_tdu_sum_linear.
Print Assumptions tbtf_tdu_sum_add.

(* ============================================================ *)
(* G3 提取探针段：本件二代表件＋根件一件（对照锚）分件提取，             *)
(* Obj.magic 计数分解归桶（本件引入 vs 库层转写）——口径见交付报告 G3 节。 *)
(* ============================================================ *)
Extraction "_tbtf_g3_probe.ml" tbtf_tdefs_sum_pos tbtf_tdefs_sum_ext.
Extraction "_tbtf_g3_ctrl_root.ml" real_list_sum_ext.
