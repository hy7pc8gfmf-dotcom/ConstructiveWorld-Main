(* ==========================================================================)
   abl_tail_pos_supply_sum.v — 基座区上编假设消解第五批·上编批 1 施工席
   （F1 sum 族六性质槽组喂形供给件·SumDCarrierFeed 槽组延线）
   ── 使命：上编三态判定册（20261001，attn/_tbase100_ 系）§三批 1 行
      （槽组延线，卡 1 F1 sumf 六性质族）七宿主槽组逐落位具名供给，
      sumf := sumd_sumf S enum 定义性实例化路线（SumDCarrierFeed 同款
      流程），共 26 槽：
      （一）UpReqAlign.v ReqAlignCore 节六槽（sum_ext/sum_add/sum_linear/
        sum_le/sum_pos/sum_zero_nonneg，现档 :90-103）——段一；
      （二）UpReqDist.v ReqSumLayer 节六槽（现档 :251-267）——段二；
      （三）UpReqDist.v ReqFEP 节六槽（fsum_*，现档 :1053-1069）——段三；
      （四）UpReqDist.v ReqSteadyState 节双槽（ssum_ext/ssum_linear，
        现档 :3147-3149）——段四；
      （五）UpReqDist.v ReqSoftmaxDual 节双槽（sumf_ext/sumf_pos，
        现档 :3501-3504）——段五；
      （六）UpFirewallReq.v FirewallReq 节余三槽（ssum_ext/ssum_linear/
        ssum_pos，现档 :89-104；ssum_add/ssum_le 两槽已由 SumDCarrierFeed
        feed_ssum_add/feed_ssum_le 在役供给，本件零重复）——段六；
      （七）UpReqAlignRestA.v ReqRestACore 节余一槽（ralt_sum_pos，
        现档 :107-115；ralt_sum_ext 已由 feed_ralt_sum_ext 在役供给，
        本件零重复）——段七。
      A 直供形四性质（ext/add/linear/le）＝@sumd_* 直引逐字同形；B 全参
      喂形两性质：pos＝cons 头见证数据形（非空性以枚举 w::rest 数据承载，
      零 Prop 位；非空显式形根在役＝uabT1_rte_fsum_pos，消费按需取用，
      本件不重述）；zero_nonneg＝满射数据显式参形（成员谓词 sumd_in 为
      Set 层自持，申报位见段内注记）。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqSumD（sumd 列表
      和机械）、Stdlib List、Stdlib Extraction（段内）——全部只读引用；
      七宿主目标件零 Require、零字节不动、零级联（基座冻结域外置供给
      零级联合法）。
   ── 对标行：供给根＝sumd_sum_ext@UpReqSumD.v:141／sumd_sum_linear@:171／
      sumd_sum_add@:213／sumd_sum_le@:293／sumd_list_sum_pos_cons@:306／
      sumd_sum_zero_nonneg_surj@:519；全参泛型先例＝uabT1_rte_fsum_*
      @UpAblT1_UpReqTempEntropy.v:56-113（辖区＝ReqTempEntropy 节）；槽组
      逐宿主喂形先例＝SumDCarrierFeed.v:47-139（feed_ 系槽组一至五）；
      cons 头见证形在役先例＝tsp_tsi_sum_pos_cons／tsp_slc_sum_pos_cons@
      abl_tail_sum_family.v:396-404／:455-463；查重登记＝abl_tail_sum_
      pos_bridge.v:76-79（泛型 sigT 形／Not 形／bool 二点形／cons 形四路
      在役）＋UpAblT4_SumCarrier.v:82-105（Real 面泛型 le/ext/add 在役）
      ——本件七宿主落位均不在上列在役辖区，零重复立项；配方细节＝
      沙箱/现役/abl_tail_supply_pool/_log/供给件配方笔记-20260930.md。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典
      逻辑；语句面承载位全 Set 形（req/le/lt 为 S01 接口 Set 值谓词，
      成员谓词 sumd_in 为 Set 层自持，非空性以列表 cons 数据形承载，
      全文件零 Prop 位）；供给定理只消费供给根件已导出内容，零接口外
      新前提；满射显式参为 sumd_sum_zero_nonneg_surj 槽形同位（全称形
      无满射数据不可证，UpReqSumD 头注裁决注在案），非静默增补；逐件
      Print Assumptions 取全 Closed 判据；段内提取探针取 Obj.magic 分段
      归位如实登记口径（库层转写与本件引入分开计数）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532；道闸 rocq 进程数 ≤1 单道顺序；
      nice -19 rocq c -native-compiler no -Q <统一缓存根> ""
      abl_tail_pos_supply_sum.v（统一缓存只读指向，输出 .vo 落本池 cwd）；
      绿判四件套：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／
      vo 新于 v；rocqchk -o 环境摘要公理位 <none> 第五证。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置
      前提、零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

(* ── Require 面：基座链库序＋供给根件（顺序＝依赖序）。七宿主目标件
   零 Require（槽级供给定理只对表槽语句面，不经宿主模块——目标件零字节
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 分级申报（段级，全件 26 槽同一判词）：N1——库内实例化消解件      *)
(* 直连（sumd_* 供给根@UpReqSumD 在役，本件逐落位具名喂位，证明体    *)
(* exact 一步直引，零注水）；逐槽语句面＝宿主槽现档逐字抽取（含参序／  *)
(* 命名／隐式位），sumf 位取 sumd_sumf S enum 实例化读法。           *)
(* ============================================================ *)

(* ============================================================ *)
(* 段一：UpReqAlign.v ReqAlignCore 节六槽（现档 :90-103 实拍：        *)
(*   求和载体位 sumf :90；sum_ext :91／sum_add :93／sum_linear :96／     *)
(*   sum_pos :99／sum_le :101／sum_zero_nonneg :103）。A 直供形四件＋   *)
(*   B 喂形两件。pos 槽宿主无前提位：本件以 cons 头见证数据形喂入       *)
(*   （非空见证＝w::rest 数据承载，申报位，非静默增补）；zero_nonneg    *)
(*   槽同法以满射数据显式参喂入（sumd_in 成员谓词 Set 层自持，申报位）。 *)
(* ============================================================ *)

(* ---- 槽 sum_ext（:91-92 逐字：forall f g : S -> R, (forall s : S,
        req (f s) (g s)) -> req (sumf f) (sumf g)） ---- *)
Theorem tspps_uralign_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* ---- 槽 sum_add（:93-95 逐字） ---- *)
Theorem tspps_uralign_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* ---- 槽 sum_linear（:96-98 逐字） ---- *)
Theorem tspps_uralign_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* ---- 槽 sum_le（:101-102 逐字） ---- *)
Theorem tspps_uralign_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, le (f s) (g s)) ->
    le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* ---- 槽 sum_pos（:99-100）cons 头见证喂形（申报位：宿主槽无前提位，
        非空见证以枚举 cons 数据形承载，w::rest 即见证本身；非空显式
        形根在役＝uabT1_rte_fsum_pos，本件不重述） ---- *)
Theorem tspps_uralign_sum_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* ---- 槽 sum_zero_nonneg（:103 逐字＋满射显式参申报位：宿主槽为全称
        形，UpReqSumD 头注裁决注＝无满射数据不可证（反模型在案），喂入
        形取 sumd_sum_zero_nonneg_surj 槽形同位，sumd_in 成员谓词为
        Set 层自持（基座空型＋和型），零 Prop 位） ---- *)
Theorem tspps_uralign_sum_zero_nonneg_surj :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) ->
      req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros R RIS S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============================================================ *)
(* 段二：UpReqDist.v ReqSumLayer 节六槽（现档 :251-267 实拍：         *)
(*   求和载体位 sumf :251；sum_ext :252／sum_add :254／sum_linear :257／  *)
(*   sum_pos :260／sum_le :262／sum_zero_nonneg :264）。六槽语句面与    *)
(*   段一逐字同形（req 面六性质槽组同款），逐落位分别具名。            *)
(* ============================================================ *)

Theorem tspps_udist_rsl_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rsl_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

Theorem tspps_udist_rsl_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

Theorem tspps_udist_rsl_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, le (f s) (g s)) ->
    le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* sum_pos 槽（:260）cons 头见证喂形（申报位同段一） *)
Theorem tspps_udist_rsl_sum_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* sum_zero_nonneg 槽（:264）满射显式参喂形（申报位同段一） *)
Theorem tspps_udist_rsl_sum_zero_nonneg_surj :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) ->
      req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros R RIS S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============================================================ *)
(* 段三：UpReqDist.v ReqFEP 节六槽（现档 :1053-1069 实拍：            *)
(*   求和载体位 sumf :1053；fsum_ext :1054／fsum_add :1056／fsum_linear   *)
(*   :1059／fsum_pos :1062／fsum_le :1064／fsum_zero_nonneg :1066）。    *)
(* ============================================================ *)

Theorem tspps_udist_rfep_fsum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rfep_fsum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

Theorem tspps_udist_rfep_fsum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

Theorem tspps_udist_rfep_fsum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, le (f s) (g s)) ->
    le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* fsum_pos 槽（:1062）cons 头见证喂形（申报位同段一） *)
Theorem tspps_udist_rfep_fsum_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* fsum_zero_nonneg 槽（:1066）满射显式参喂形（申报位同段一） *)
Theorem tspps_udist_rfep_fsum_zero_nonneg_surj :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) ->
      req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros R RIS S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============================================================ *)
(* 段四：UpReqDist.v ReqSteadyState 节双槽（现档 :3147-3149 实拍：     *)
(*   求和载体位 sumf :3147；ssum_ext :3148／ssum_linear :3149）。         *)
(* ============================================================ *)

Theorem tspps_udist_rss_ssum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rss_ssum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* ============================================================ *)
(* 段五：UpReqDist.v ReqSoftmaxDual 节双槽（现档 :3501-3504 实拍：     *)
(*   求和载体位 sumf :3501；sumf_ext :3502／sumf_pos :3504）。            *)
(* ============================================================ *)

Theorem tspps_udist_rsd_sumf_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* sumf_pos 槽（:3504）cons 头见证喂形（申报位同段一） *)
Theorem tspps_udist_rsd_sumf_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* ============================================================ *)
(* 段六：UpFirewallReq.v FirewallReq 节余三槽（现档 :89-104 实拍：     *)
(*   求和载体位 sumf :89；ssum_ext :90／ssum_add :92／ssum_linear :95／   *)
(*   ssum_le :98／ssum_pos :100。ssum_add/ssum_le 两槽已由              *)
(*   SumDCarrierFeed feed_ssum_add/feed_ssum_le（:118-126）在役供给，   *)
(*   本件只做余三槽，零重复。判定册卡 1 记四槽，现档实拍五槽（勘误      *)
(*   留痕见交付报告）。                                                *)
(* ============================================================ *)

Theorem tspps_ufw_ssum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_ufw_ssum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* ssum_pos 槽（:100）cons 头见证喂形（申报位同段一） *)
Theorem tspps_ufw_ssum_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* ============================================================ *)
(* 段七：UpReqAlignRestA.v ReqRestACore 节余一槽（现档 :107-115 实拍： *)
(*   求和载体位 sumf :107；ralt_sum_ext :108（已由 SumDCarrierFeed        *)
(*   feed_ralt_sum_ext :128-130 在役，零重复）；ralt_sum_pos :113）。    *)
(* ============================================================ *)

(* ralt_sum_pos 槽（:113）cons 头见证喂形（申报位同段一） *)
Theorem tspps_uralta_ralt_sum_pos_cons :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros R RIS S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* ============================================================ *)
(* PA 审计段（逐件全 Closed 判据；名清单＝Qed 计数＝26，零差）          *)
(* ============================================================ *)
Print Assumptions tspps_uralign_sum_ext.
Print Assumptions tspps_uralign_sum_add.
Print Assumptions tspps_uralign_sum_linear.
Print Assumptions tspps_uralign_sum_le.
Print Assumptions tspps_uralign_sum_pos_cons.
Print Assumptions tspps_uralign_sum_zero_nonneg_surj.
Print Assumptions tspps_udist_rsl_sum_ext.
Print Assumptions tspps_udist_rsl_sum_add.
Print Assumptions tspps_udist_rsl_sum_linear.
Print Assumptions tspps_udist_rsl_sum_le.
Print Assumptions tspps_udist_rsl_sum_pos_cons.
Print Assumptions tspps_udist_rsl_sum_zero_nonneg_surj.
Print Assumptions tspps_udist_rfep_fsum_ext.
Print Assumptions tspps_udist_rfep_fsum_add.
Print Assumptions tspps_udist_rfep_fsum_linear.
Print Assumptions tspps_udist_rfep_fsum_le.
Print Assumptions tspps_udist_rfep_fsum_pos_cons.
Print Assumptions tspps_udist_rfep_fsum_zero_nonneg_surj.
Print Assumptions tspps_udist_rss_ssum_ext.
Print Assumptions tspps_udist_rss_ssum_linear.
Print Assumptions tspps_udist_rsd_sumf_ext.
Print Assumptions tspps_udist_rsd_sumf_pos_cons.
Print Assumptions tspps_ufw_ssum_ext.
Print Assumptions tspps_ufw_ssum_linear.
Print Assumptions tspps_ufw_ssum_pos_cons.
Print Assumptions tspps_uralta_ralt_sum_pos_cons.

(* ============================================================ *)
(* 提取检验区（判据＝Obj.magic 库层转写与本件引入分开计数如实登记；     *)
(*   输出目录为本池检验区；三代表件覆盖三种证明体族：ext 直引／         *)
(*   pos cons 形／zero_nonneg 满射参形；若触提取器硬错或记录层转写      *)
(*   非零，照池内 63/68 先例对照实验口径处置并逐条登记，禁虚报通过）    *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspps_uralign_sum_ext
  tspps_uralign_sum_pos_cons tspps_uralign_sum_zero_nonneg_surj.

(* 终验实测登记（20261001 本席实跑回填，禁虚报）：
   ① 编译四件套全绿：EXIT=0／日志真错行计 0／vo 头 8 字节
     436f7121 00015ff4／vo 新于 v；日志＝_log/
     abl_tail_pos_supply_sum-compile-20261001.log。
   ② PA 审计 26 件全 Closed under the global context（名清单＝Qed
     计数＝26，零差；非 Closed 位计 0）。
   ③ 提取命令 EXIT=0 绿、零硬错；提取对象三代表件（ext 直引／pos
     cons 形／zero_nonneg 满射参形各一）；Obj.magic 行计 1，分段归因
     （对照实验口径，探针＝probe_tspps_g3ctl 同位复现，日志＝_log/
     probe_tspps_g3ctl-20261001.log）：库层闭包携入 1——
     sumd_sum_zero_nonneg_in@UpReqSumD 体内 sumd_in Set 层和型之
     match 转写（对照探针仅提取在役根件同位复现同一行）；本件引入
     段 0——三代表件提取体均为裸 let 薄绑定直引根件（日志尾段
     let tspps_uralign_sum_ext = sumd_sum_ext 等在案）。
   ④ G4 第五证：rocq check -Q <统一缓存根> "" -o
     abl_tail_pos_supply_sum EXIT=0；环境摘要公理〈none〉／
     type-in-type <none>／unsafe fixpoints <none>／positivity
     assumed <none>／Set is predicative（日志＝_log/
     abl_tail_pos_supply_sum-coqchk-20261001.log）。 *)
