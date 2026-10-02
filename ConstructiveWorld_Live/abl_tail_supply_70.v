(* ==========================================================================)
   abl_tail_supply_70.v — 尾百供给施工席（尾百模块假设消解批量供给件·批四段：
   Arch_Up_01 Z_align_pos 槽换名喂入＋sum_over_S_pos 实例闭形×2）
   ── 使命：对 Arch_Up_01 上编槽位三处给出供给定理。三处槽位现档＝
      AlignIdWorld 节 :478（Variable Z_align_pos : lt zero (Z_align reward
      beta beta_pos pi_ref)）、同节 :481-482 与 FirewallLoop 节 :786-787
      （sum_over_S_pos 两槽逐字同形）。供给构造三段：
      （一）换名 conv 件＋Z_align_pos 槽喂入——tsp_up01_zalign_slot_body_conv
        （S05 出节常量 Z_align 与 UpAblZpos 消解体 zab_Z_align 展开后为
        同一项的恒等换名核验，zpd_slot_body_conv_zabr@UpAblMetaEngine.v:
        63-74 先例照抄形）＋tsp_up01_Z_align_pos_slot（显式前提 Hsum_pos
        即 :481-482 槽逐字同形，喂入 zab_Z_align_pos@UpAblZpos.v:82 条件形
        即闭合，结论面经换名件与槽面逐字同形）；
      （二）sum_over_S_pos 实例闭形×2——在库内既有最小 SumOver 实例世界
        （uab_ssUnit＋uab_soUnit@UpAblT13c_G13，单点状态空间）上取共用
        本体 tsp_up01_sum_pos_unit（求和投影按记录定义性展开为逐点函数值，
        逐项正前提实例于唯一元素即闭合），两槽位分别具名
        tsp_up01_align_sum_over_S_pos（:481-482）／
        tsp_up01_fwloop_sum_over_S_pos（:786-787），一次构造两槽受益；
      （三）出节全参闭形——tsp_up01_Z_align_pos_unit_world：单点世界读法下
        Z_align_pos 槽无条件闭合（（一）槽喂入件以（二）具名件入位；
        消费面读法＝目标节以 SS := uab_ssUnit、SO := uab_soUnit 实例化）。
      施工形修正登记（如实申报）：批草案批四行原含 lt_plus_compat_lt_le×2
      喂入段并依赖批三件（DO-free bs_abs／bs_lpc）；批三件
      abl_tail_supply_69 现档核验改判该族属抽象接口层不可成证（le 前件
      分解在纯字段内不可导，机判探针与在役供给面普查在案），Arch_Up_01
      :797-798／:1175-1176 两槽随判保持假设身份、不发供给件，本件依赖
      随之解除、零 Require 批三件，全量一次编绿交付。另 :1867-1868 槽
      （实数层不透明自由参数裸正性证书）同不发供给件，坐标与判读登记于
      池内交付报告。
   ── 依赖：S01_BaseRing（接口类、Set 层恒等型与字段来源）、
      S05_AlignmentGRPO（Z_align 出节常量）、UpAblZpos（zab_Z_align 定义
      与 zab_Z_align_pos 条件形）、UpAblT13c_G13（uab_ssUnit／
      uab_ssUnit_elem／uab_soUnit 实例来源）、Stdlib Extraction——全部
      只读引用；既有件零字节不动、零级联。
   ── 对标行：槽位现档＝Arch_Up_01.v:478／:481-482／:786-787；换名通路
      机器先例＝zpd_slot_body_conv_zabr@UpAblMetaEngine.v:63-74（前提面
      自检 :131 全 Closed）＋zpd_Z_align_pos_slot :93；条件形＝
      zab_Z_align_pos@UpAblZpos.v:82-93；实数层无条件形＝
      zabr_Z_align_pos@UpAblZposReal.v:75；Z_align 定义体＝
      S05_AlignmentGRPO.v:60-61；实例来源＝uab_ssUnit@UpAblT13c_G13.v:
      72-94／uab_ssUnit_elem :96-100／uab_soUnit :102-113；SumOver 类＝
      S01_BaseRing.v:1273-1306；两槽位分别具名先例＝本池
      abl_tail_supply_68.v；配方细节＝本池 _log/供给件配方笔记-20260930.md。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑；
      语句面承载位全 Set 形（Id 型为 S01:73 Set 层恒等型，lt/le 皆 Set 值，
      零 Prop 泄露）；供给定理只消费目标件已导出内容与在役实例，零接口外
      新前提；逐件 Print Assumptions 取全 Closed 判据；文件尾提取检验区取
      Obj.magic 计 0 判据（若触提取器硬错或记录层转写非零，照池内 63/64/68
      豁免与如实登记先例处置，禁虚报通过）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      cd 沙箱/现役/abl_tail_supply_pool；道闸核 rocq 进程数 ≤1 方起编；
      单道顺序；ulimit -s 65532；
      nice -19 rocq c -native-compiler no -Q /Users/apple/Desktop/
      ConstructiveWorld/vo_local_world_unified_0930 "" abl_tail_supply_70.v
      （统一缓存只读指向，输出 .vo 落本池 cwd；绿判四件套：EXIT=0／
      日志真错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v）。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

(* ── Require 面：接口基座＋Z_align 常量来源＋条件形消解件＋实例来源件
   （顺序＝依赖序；既有件零改动。本件零 Require 批三件
   abl_tail_supply_69——该件两定理为抽象层非严边界形，与本件供给面无
   消费关系，见头注施工形修正登记） *)
Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import UpAblZpos.
Require Import UpAblT13c_G13.

(* ============================================================ *)
(* 一、Z_align_pos 槽换名喂入段（Arch_Up_01 AlignIdWorld 节 :478）   *)
(*    节环境照抄槽位所在节（Arch_Up_01.v:455-477 同序同形），         *)
(*    语句面取槽位逐字同形。                                        *)
(* ============================================================ *)

Section TspUp01AlignSupply.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).

(* ---- 构造件一：换名 conv 件 ----
   S05 主节出节常量 Z_align（体＝参考策略逐项乘 exp_neg 的 sum_over_S
   和，S05_AlignmentGRPO.v:60-61）与 UpAblZpos 消解体 zab_Z_align
   （UpAblZpos.v:60-63 同构定义）展开后为同一项：恒等构造子经转换内导
   即闭合——此即「逐字同构」的机器验证。 *)
Theorem tsp_up01_zalign_slot_body_conv :
  Id (Z_align reward beta beta_pos pi_ref)
     (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  exact id_refl.
Qed.

(* ---- 构造件二：Z_align_pos 槽喂入（条件形） ----
   显式前提 Hsum_pos 即槽位节内 sum_over_S_pos 假设（:481-482）逐字
   同形；喂入 zab_Z_align_pos（UpAblZpos.v:82-93，同前提条件形）即
   闭合，结论面经构造件一换名与槽面逐字同形。 *)
Theorem tsp_up01_Z_align_pos_slot :
  forall Hsum_pos : forall f : S -> R,
              (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f),
    lt zero (Z_align reward beta beta_pos pi_ref).
Proof.
  intro Hsum_pos.
  exact (zab_Z_align_pos reward beta beta_pos pi_ref pi_ref_pos Hsum_pos).
Qed.

End TspUp01AlignSupply.

(* ============================================================ *)
(* 二、sum_over_S_pos 实例闭形段（:481-482／:786-787 两槽位）        *)
(*    最小 SumOver 实例世界（uab_ssUnit＋uab_soUnit@UpAblT13c_G13，  *)
(*    单点状态空间）：求和投影按记录定义性展开为逐点函数值，逐项正    *)
(*    前提实例于唯一元素即闭合。抽象位两槽保持假设身份，本段闭形      *)
(*    供下游充任接口字段。                                          *)
(* ============================================================ *)

(* ---- 共用本体：sum_over_S_pos 槽逐字闭形（单点世界读法） ---- *)
Theorem tsp_up01_sum_pos_unit :
  forall {RI : RealInterfaceEnhanced} (f : @S RI uab_ssUnit -> @R RI),
    (forall s : @S RI uab_ssUnit, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (@sum_over_S RI uab_ssUnit uab_soUnit f).
Proof.
  intros RI f H.
  exact (H uab_ssUnit_elem).
Qed.

(* ---- :481-482 槽位具名（AlignIdWorld 节） ---- *)
Theorem tsp_up01_align_sum_over_S_pos :
  forall {RI : RealInterfaceEnhanced} (f : @S RI uab_ssUnit -> @R RI),
    (forall s : @S RI uab_ssUnit, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (@sum_over_S RI uab_ssUnit uab_soUnit f).
Proof.
  intros RI f H.
  exact (@tsp_up01_sum_pos_unit RI f H).
Qed.

(* ---- :786-787 槽位具名（FirewallLoop 节） ---- *)
Theorem tsp_up01_fwloop_sum_over_S_pos :
  forall {RI : RealInterfaceEnhanced} (f : @S RI uab_ssUnit -> @R RI),
    (forall s : @S RI uab_ssUnit, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (@sum_over_S RI uab_ssUnit uab_soUnit f).
Proof.
  intros RI f H.
  exact (@tsp_up01_sum_pos_unit RI f H).
Qed.

(* ---- 出节全参闭形：单点世界读法下 Z_align_pos 槽无条件闭合 ----
   消费面读法：目标节以 SS := uab_ssUnit、SO := uab_soUnit 实例化后，
   Z_align_pos 槽位以本件入位；构造件二以 :481-482 具名件入位 Hsum_pos。 *)
Theorem tsp_up01_Z_align_pos_unit_world :
  forall {RI : RealInterfaceEnhanced}
         (reward : @S RI uab_ssUnit -> @R RI) (beta : @R RI)
         (beta_pos : @lt RI (@zero RI) beta)
         (pi_ref : @S RI uab_ssUnit -> @R RI)
         (pi_ref_pos : forall s : @S RI uab_ssUnit,
                         @lt RI (@zero RI) (pi_ref s)),
    @lt RI (@zero RI)
      (@Z_align RI uab_ssUnit uab_soUnit reward beta beta_pos pi_ref).
Proof.
  intros RI reward beta beta_pos pi_ref pi_ref_pos.
  exact (@tsp_up01_Z_align_pos_slot RI uab_ssUnit uab_soUnit
           reward beta beta_pos pi_ref pi_ref_pos
           (@tsp_up01_align_sum_over_S_pos RI)).
Qed.

(* ============================================================ *)
(* 三、逐件前提面审计（全 Closed 判据；名清单=Qed 计数=语句数，零差） *)
(* ============================================================ *)
Print Assumptions tsp_up01_zalign_slot_body_conv.
Print Assumptions tsp_up01_Z_align_pos_slot.
Print Assumptions tsp_up01_sum_pos_unit.
Print Assumptions tsp_up01_align_sum_over_S_pos.
Print Assumptions tsp_up01_fwloop_sum_over_S_pos.
Print Assumptions tsp_up01_Z_align_pos_unit_world.

(* ============================================================ *)
(* 四、提取检验区（判据＝输出 Obj.magic 计 0；输出目录为本池检验区；   *)
(*    若触提取器硬错或记录层转写非零，照池内 63/64/68 先例处置并逐条   *)
(*    如实登记，禁虚报通过）                                        *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tsp_up01_zalign_slot_body_conv
  tsp_up01_Z_align_pos_slot tsp_up01_sum_pos_unit
  tsp_up01_align_sum_over_S_pos tsp_up01_fwloop_sum_over_S_pos
  tsp_up01_Z_align_pos_unit_world.
