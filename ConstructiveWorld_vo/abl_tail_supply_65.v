(* ==========================================================================)
   abl_tail_supply_65.v — 尾百供给施工组（第二批·批 1：tsp_sum6 求和六性质件）
   ── 使命：F1 求和六性质 28 槽实例闭形（六性质供给定理＋使用件槽输入形）
      ＋F9 inv_one_inv 双槽＋F12 fold 两方程＋PA 审计段。受益六件：
      PA_TempMonoW2Mark（tmw 六槽 :42-57）、Arch_PA_02（frd 六槽 :890-905，
      与 tmw 逐字双落）、PA_TempSoftmaxInstantiation（tsi 四槽 :211-221）、
      PA_ToyR_SecondLawConsume 与 Arch_ToyR_04（slc 双件四槽 :117-126 ↔
      :79-88 逐字双落）、Arch_PA_04（sum_ext/add/linear :871-878＋sum_pos
      :1354）、UpAblAbsSumLeB2（sumL 两方程 :350-352）。
      覆盖结构（查重后如实分工，禁重复供给）：tmw/frd/PA_04 十六槽之实例
      闭形在役已备——UpAblT1_UpReqTempEntropy.v:56-113 fsum 六件（RIS 泛型
      sumd_sumf 面）＋UpAblP6_EntropyMonoSplit_C.v:453-503 uabp6c 五件
      （bool 载体）＋abl_tail_supply_64.v sigT 正性衔接形与 bool 零化全形；
      本件不再复写该十六槽面，新增供给＝（一）tsi 四槽输入形（RI 桥面，
      sumf := sumd_sumf，库内无此面）；（二）slc 双件八槽输入形（Real 层
      S:Type，sumf := real_list_sum，库内仅有件内联名直接传入无独立供给定理）；
      （三）F9 inv_one_inv Real 特化一击（一件服务 tmw/frd 双槽）；（四）
      F12 fold 两方程（sumL := real_list_sum 实例，nil/cons 定义性）；
      （五）PA 审计段（Check 对照＋Print Assumptions 逐件＋提取探查件）。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqSumD（sumd 列表和
      机）、受益六件 PA_TempMonoW2Mark／Arch_PA_02／PA_TempSoftmaxInstantiation
      ／PA_ToyR_SecondLawConsume／Arch_ToyR_04／Arch_PA_04／UpAblAbsSumLeB2、
      Stdlib List——全部只读引用；受益件零字节不动、零级联（其 Require 面
      经由各自编译件自动装载；本件 Require 六件中除 tsi（用其 RI→RIS 桥
      实例）外为名义性签名保持引，据件 53 先例登记备查）。
   ── 对标行：供给型 A 接口假设直供形＝UpAblMetaEngine.v zpd_Z_align_pos_slot；
      签名保持式供给段正本＝UpAblP6_EntropyMonoSplit_C.v:445-505（uabp6c
      五件）与 UpAblT1_UpReqTempEntropy.v:56-113（fsum 六件）；cons 形非空
      头见证＝sumd_list_sum_pos_cons@UpReqSumD.v:306；Real 层列表和机＝
      real_list_sum@S08_RealMainlineDPO.v:289（ext:296/add:341/
      linear:363/pos:464）；inv_one_inv 根＝
      real_log_inv_one_inv@S08_RealMainlineDPO.v:999（tmw/frd 槽 Real 特化
      逐字同语句；甄别册上编卡 7 所引 S07:7905 real_log_inv_log 为 log_inv 面
      邻接根，本件现档复核改引 S08 直根——登记订正）；RIS 类面＝
      RealInterfaceEnhancedSetoid@S07_RealSetoidExpLog.v:7945，Real 实例
      装配＝RealEnhancedReal@:8596（req:=real_eq/lt:=real_lt/log:=real_log/
      inv_pos:=real_inv_pos）；tsi RI→RIS 桥实例＝tsi_rie_setoid@
      PA_TempSoftmaxInstantiation.v（req:=Id，字段定义性直引 S01）；配方
      细节＝沙箱/现役/abl_tail_supply_pool/_log/供给文件配方笔记.md。
   ── 构造性注记：全件零承认式声明、零悬置前提、零经典逻辑；语句面承载位
      全 Set 形（req/lt/le/real_eq/real_lt/real_le 皆 Set 值谓词）；非空性
      数据参取 cons 头见证形（Not 形不入语句面，证明体内 discriminate 一
      步为证明位非承载位）；供给定理只使用在役已证根件，零接口外新前提；
      全部结论 Qed 真构造闭合；Print Assumptions 全 Closed 判据；提取探查件
      取库层转写与本件引入分开计数如实登记口径（G3 对照实验）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532 && cd 本池；道闸核 rocq 进程数 ≤1 后单道执行
      nice -19 rocq c -native-compiler no -Q <统一缓存根> "" abl_tail_supply_65.v；
      绿判四要素：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／
      vo 新于 v。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑，全部结论 Qed 真构造闭合。
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
Require Import PA_TempMonoW2Mark.
Require Import Arch_PA_02.
Require Import PA_TempSoftmaxInstantiation.
Require Import PA_ToyR_SecondLawConsume.
Require Import Arch_ToyR_04.
Require Import Arch_PA_04.
Require Import UpAblAbsSumLeB2.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   tmw 六槽（PA_TempMonoW2Mark.v:42-57）与 frd 六槽（Arch_PA_02.v:   *)
(*   890-905）与 PA_04 sum_ext/add/linear（:871-878）＋sum_pos（:1354）  *)
(*   之实例闭形＝UpAblT1_UpReqTempEntropy.v:56-113 fsum 六件在役同语句  *)
(*   （sumd_sumf 面，RIS 泛型）；bool 载体 Real 层五件＝uabp6c 系       *)
(*   （UpAblP6_EntropyMonoSplit_C.v:453-503）；sigT 正性衔接形与 bool   *)
(*   零化全形＝abl_tail_supply_64.v。以上十六槽本件零新增语句，使用面   *)
(*   经 Require 引在役件即取。                                          *)
(* ============================================================ *)

(* ============================================================ *)
(* 一、tsi 四槽输入形（PA_TempSoftmaxInstantiation Section TsiMains    *)
(*     槽面 :211-221；RI 桥读法下 sumf := sumd_sumf，req/lt/zero/      *)
(*     mult/plus 经 tsi_rie_setoid 实例解析，定义性直引 S01 字段）。   *)
(* ============================================================ *)

Section TspTsiSumFeed.

Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable en : list Token.

(* 求和实现化读法：tsi 抽象求和槽取 sumd 列表和（RIS 取 tsi RI 桥实例） *)
Let sumf : (Token -> @S01_BaseRing.R RI) -> @S01_BaseRing.R RI :=
  sumd_sumf Token en.

(* ---- 供给一：求和外延（tsi Hsum_ext 槽 :211-213 逐字同形，N1：      *)
(*      sumd_sum_ext@UpReqSumD.v:141 直引） ---- *)
Theorem tsp_tsi_sum_ext : forall f g : Token -> @S01_BaseRing.R RI,
  (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (sumd_sum_ext Token en f g H).
Qed.

(* ---- 供给二：求和左线性（tsi Hsum_linear 槽 :214-216 逐字同形，     *)
(*      N1：sumd_sum_linear@UpReqSumD.v:171 直引） ---- *)
Theorem tsp_tsi_sum_linear : forall (a : @S01_BaseRing.R RI)
    (f : Token -> @S01_BaseRing.R RI),
  req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (sumd_sum_linear Token en a f).
Qed.

(* ---- 供给三：求和加法分解（tsi Hsum_add 槽 :217-219 逐字同形，      *)
(*      N1：sumd_sum_add@UpReqSumD.v:213 直引） ---- *)
Theorem tsp_tsi_sum_add : forall f g : Token -> @S01_BaseRing.R RI,
  req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (sumd_sum_add Token en f g).
Qed.

End TspTsiSumFeed.

(* ---- 供给四：求和正性 cons 头见证形（tsi Hsum_pos 槽 :220-221 输入  *)
(*      形；枚举呈 w::rest 数据形承载非空，N2：                        *)
(*      sumd_list_sum_pos_cons@UpReqSumD.v:306 头尾分解直引） ---- *)
Theorem tsp_tsi_sum_pos_cons : forall (RI : RealInterfaceEnhanced)
    (Token : Set) (f : Token -> @S01_BaseRing.R RI) (w : Token)
    (rest : list Token),
  (forall s : Token, lt zero (f s)) ->
  lt zero (sumd_sumf Token (w :: rest) f).
Proof.
  intros RI Token f w rest H.
  exact (sumd_list_sum_pos_cons Token f w rest H).
Qed.

(* ============================================================ *)
(* 二、slc 双件八槽输入形（PA_ToyR_SecondLawConsume.v:117-126 ↔        *)
(*     Arch_ToyR_04.v:79-88 逐字双落；Real 层 S:Type，sumf :=          *)
(*     real_list_sum；Arch_ToyR_04.v:228-281 件内联名直接传入之独立供给    *)
(*     定理化，库内无独立面）。                                        *)
(* ============================================================ *)

Section TspSlcSumFeed.

Variable S : Type.
Variable en : list S.

(* 求和实现化读法：slc 抽象求和槽取 S08 real_list_sum 折叠和 *)
Let sumf : (S -> Real) -> Real := fun g : S -> Real => real_list_sum S g en.

(* ---- 供给五：求和外延（slc sumext 槽 :120-121/:82-83 逐字同形，     *)
(*      N1：real_list_sum_ext@S08_RealMainlineDPO.v:296 直引） ---- *)
Theorem tsp_slc_sum_ext : forall f g : S -> Real,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (real_list_sum_ext S f g en H).
Qed.

(* ---- 供给六：求和左线性（slc sumlinear 槽 :122-123/:84-85 逐字同形，*)
(*      N1：real_list_sum_linear@S08_RealMainlineDPO.v:363 直引） ---- *)
Theorem tsp_slc_sum_linear : forall (a : Real) (f : S -> Real),
  real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)).
Proof.
  intros a f.
  exact (real_list_sum_linear S a f en).
Qed.

(* ---- 供给七：求和加法分解（slc sumadd 槽 :124-126/:86-88 逐字同形， *)
(*      N1：real_list_sum_add@S08_RealMainlineDPO.v:341 直引） ---- *)
Theorem tsp_slc_sum_add : forall f g : S -> Real,
  real_eq (sumf (fun s : S => real_plus (f s) (g s)))
          (real_plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (real_list_sum_add S f g en).
Qed.

End TspSlcSumFeed.

(* ---- 供给八：求和正性 cons 头见证形（slc sumpos 槽 :117-119/:79-81  *)
(*      输入形；枚举呈 w::rest 数据形承载非空，N2：                    *)
(*      real_list_sum_pos@S08_RealMainlineDPO.v:464 直引＋证明体内      *)
(*      discriminate 关非空支） ---- *)
Theorem tsp_slc_sum_pos_cons : forall (S : Type) (f : S -> Real)
    (w : S) (rest : list S),
  (forall s : S, real_lt real_zero (f s)) ->
  real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S f w rest H.
  apply (real_list_sum_pos S f (w :: rest) H).
  discriminate.
Qed.

(* ============================================================ *)
(* 三、F9 inv_one_inv（tmw 槽 :62-64 ↔ frd 槽 :909-911 逐字双落，       *)
(*     一件服务双槽；Real 特化一击——R:=Real 时类面字段 req/lt/zero/    *)
(*     inv_pos/log/opp 经 RealEnhancedReal 装配定义性落 real_eq/       *)
(*     real_lt/real_zero/real_inv_pos/real_log/real_opp，槽面即        *)
(*     real_log_inv_one_inv@S08_RealMainlineDPO.v:999 逐字同语句）。   *)
(* ============================================================ *)

Theorem tsp_log_inv_one_inv_real :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (real_log_inv_one_inv x Hx Hi).
Qed.

(* ============================================================ *)
(* 四、F12 fold 两方程（UpAblAbsSumLeB2.v:350-352 槽面逐字同形；       *)
(*     sumL := real_list_sum X 实例——nil 肢折叠定义性落 real_zero，    *)
(*     cons 肢折叠定义性落头尾分解，real_eq_refl 一击；X:Type 与槽同    *)
(*     Universe，零特化代价）。                                        *)
(* ============================================================ *)

Theorem tsp_sumL_nil_eq : forall (X : Type) (f : X -> Real),
  real_eq (real_list_sum X f nil) real_zero.
Proof.
  intros X f.
  exact (real_eq_refl (real_list_sum X f nil)).
Qed.

Theorem tsp_sumL_cons_eq : forall (X : Type) (f : X -> Real) (w : X)
    (rest : list X),
  real_eq (real_list_sum X f (w :: rest))
          (real_plus (f w) (real_list_sum X f rest)).
Proof.
  intros X f w rest.
  exact (real_eq_refl (real_list_sum X f (w :: rest))).
Qed.

(* ============================================================ *)
(* 五、PA 审计段（对照 Check 读面＋逐件 Closed 判读）                   *)
(* ============================================================ *)

(* 对照 Check：根件语句面读出（面型保真对照留痕） *)
Check sumd_sumf.
Check real_list_sum.
Check real_log_inv_one_inv.
Check tsi_rie_setoid.
Check RealEnhancedReal.

(* 前提面审计（逐件全 Closed 判据；名清单＝Qed 计数＝11，零差） *)
Print Assumptions tsp_tsi_sum_ext.
Print Assumptions tsp_tsi_sum_linear.
Print Assumptions tsp_tsi_sum_add.
Print Assumptions tsp_tsi_sum_pos_cons.
Print Assumptions tsp_slc_sum_ext.
Print Assumptions tsp_slc_sum_linear.
Print Assumptions tsp_slc_sum_add.
Print Assumptions tsp_slc_sum_pos_cons.
Print Assumptions tsp_log_inv_one_inv_real.
Print Assumptions tsp_sumL_nil_eq.
Print Assumptions tsp_sumL_cons_eq.

(* ============================================================ *)
(* 六、提取检验区（判据＝Obj.magic 库层转写与本件引入分开计数如实登记；  *)
(*   输出目录为本池检验区）                                            *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tsp_sumL_nil_eq tsp_sumL_cons_eq tsp_slc_sum_ext
  tsp_tsi_sum_ext tsp_log_inv_one_inv_real.

(* 终验实测登记（ 实测补录，禁虚报）：
   ① 提取命令 EXIT=0 绿、零硬错（bypass opacity 提示为库层不透明体披露
     警告面，非错误）；提取对象五件。
   ② Obj.magic 计 50，分段归因（对照实验口径）：
     库层转写段 49 处，本件语句面零引入——
     (a) S01 realInterfaceEnhanced 模块 r_if/r_if_true/r_if_false 转写段
         3 处（提取输出 :682-694）；
     (b) tsi_rie_setoid 桥实例转写段 46 处（:2968-3117；实例本体声明于
         PA_TempSoftmaxInstantiation 库件，Id 同义转换与逐 eps 桥字段，
         因提取闭包携入，非本件引入）；
     本件引入段 1 处——tsp_log_inv_one_inv_real 体内 req↔real_eq 型别
     同义转换 cast（供给语句面取 tmw/frd 槽面 req 形〔逐字铁律对象＝
     槽面〕、证明体 exact 直引 Real 层根件 real_log_inv_one_inv〔全参
     直引铁律〕，两铁律联合强制的提取器型别转写，非悬置前提引入；
     前提面审计该件 Closed 为独立证据）。与 abl_tail_supply_63 批二段
     登记同类（彼件 4 处）。
   ③ PA 审计十一件全 Closed（Closed under the global context 计 11＝
     Qed 计数 11，零差）；G4 rocqchk -o EXIT=0，CONTEXT SUMMARY 全位空：
     公理 <none>／type-in-type <none>／unsafe fixpoints <none>／
     positivity assumed <none>。 *)
