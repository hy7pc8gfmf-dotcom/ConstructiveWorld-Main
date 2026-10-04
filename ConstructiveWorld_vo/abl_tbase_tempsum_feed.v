(* ==========================================================================
   abl_tbase_tempsum_feed.v —— 温度族四宿主 Real 面具名应用形供给（17 参数）。
   ── 使命：UpReqTempDefs／UpReqEntropyDeficitTemp／UpReqEntropyMaxTemp／
   UpReqTempDual 四宿主 Section 内 pos／ext／linear／add（＋EMT le 扩参数）
   共 17 参数的 per-宿主具名应用形供给（B 型应用形：宿主节内抽象
   real_sum_over_S 取 real_list_sum S l 读法——S08_RealMainlineDPO
   Section RealListSumMain 之 Variable X : Type 全型泛型列表折叠和，与温度
   族宿主 S : Type 逐字匹配）。四宿主四形参数面逐字同构；根件出处＝
   real_list_sum@S08 及其 ext／add／linear／le／pos 伴随族。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、S08_RealMainlineDPO
   （RealListSumMain 六根）、Stdlib List／Extraction——全部只读引用；四宿主
   目标件零 Require、零字节动零级联。
   ── 对标行：uabt4_sum_carrier4_realized@UpAblT4_SumCarrier.v（同一
   real_list_sum 的 sigT 兑现包先例）；uabT1_rte_fsum_*@
   UpAblT1_UpReqTempEntropy.v（req 面 per-宿主具名应用形体例正本）。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑；
   语句面承载位全 Set 形（real_eq／real_lt／real_le 为 S02/S07 Set 值谓词，
   非空前提＝基座 Set 面 Not (Id l nil)）；pos 参数宿主无前提位：非空见证
   前提为数学必需（空枚举和＝real_zero 构造性不可证），增补前提如实申报，
   使用位按 cons 头见证或 bool 二点枚举装载；供给定理只使用根件已导出内容。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no -Q <统一缓存根> "" abl_tbase_tempsum_feed.v
   （统一缓存只读指向，输出 .vo 落本池 cwd）；绿判＝EXIT=0／日志零 Error／
   vo 头 8 字节 436f7121 00015ff4／vo 新于 v；第五证 rocqchk。
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
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 分级申报（段级，全件 17 参数同一结论）：N1——库内实例化消解件直连     *)
(* （real_list_sum_* 六根@S08 RealListSumMain 在役，本件逐安置具名喂位，  *)
(* 证明体 exact 一步直引＋pos 位非空桥一步，零注水）；pos 非空前提增补   *)
(* 申报位见头注构造性注记。逐参数语句面＝四宿主现档逐字抽取（含参序／      *)
(* 命名／隐式位），real_sum_over_S 位取 real_list_sum S l 实例化读法。   *)
(* ============================================================ *)

(* ============================================================ *)
(* 段一：UpReqTempDefs.v Section RealTempDefs 四参数（现档 :90-104 实拍：  *)
(*   承载位 real_sum_over_S :94；pos :95／ext :98／linear :100／add :102） *)
(* ============================================================ *)

(* ---- 参数 real_sum_pos_preserved（:95-97 逐字：forall (f : S -> Real),
        (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero
        (real_sum_over_S f)；sumf 位＝real_list_sum S (w::rest) 读法；
        非空性以 cons 头见证数据承载（tspps cons 形先例：S : Type 承载
        下基座 Not (Id l nil) 不合型——Id 承载位 Set 约束，检验
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

(* ---- 参数 real_sum_over_S_ext（:98-99 逐字） ---- *)
Theorem tbtf_tdefs_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

(* ---- 参数 real_sum_over_S_linear（:100-101 逐字） ---- *)
Theorem tbtf_tdefs_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

(* ---- 参数 real_sum_over_S_add（:102-104 逐字） ---- *)
Theorem tbtf_tdefs_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* ============================================================ *)
(* 段二：UpReqEntropyDeficitTemp.v Section RealEntropyDeficitTemp 四参数   *)
(* （现档 :167-181 实拍：承载位 :170；pos :171／ext :174／linear :176／  *)
(*  add :179；四形参数面与段一逐字同构——并排实拍）                   *)
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
(* 段三：UpReqEntropyMaxTemp.v Section RealEntropyMaxTemp 五参数（现档      *)
(*  :132-149 实拍：承载位 :134；pos :135／ext :138／le 扩参数 :142（件内    *)
(*  自证「具体承载实例……real_list_sum_le，S08 L421 在库」:140-141）／    *)
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

(* ---- 扩参数 real_sum_over_S_le（:142-143 逐字；根件件内自证位） ---- *)
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
(* 段四：UpReqTempDual.v Section RealTempDual 四参数（现档 :32-46 实拍：    *)
(*  承载位 :35；pos :36／ext :39／linear :41／add :44；四形参数面与段一     *)
(*  逐字同构——并排实拍）                                           *)
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
(* G3 提取检验段：本件二代表件＋根件一件（对照锚）分件提取，             *)
(* Obj.magic 计数分解归桶（本件引入 vs 库层转写）——口径见交付报告 G3 节。 *)
(* ============================================================ *)
Extraction "_tbtf_g3_probe.ml" tbtf_tdefs_sum_pos tbtf_tdefs_sum_ext.
Extraction "_tbtf_g3_ctrl_root.ml" real_list_sum_ext.
