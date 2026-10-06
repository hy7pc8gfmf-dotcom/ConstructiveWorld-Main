(* ==========================================================================)
   abl_dtpt_rot_bridge_supply.v — DTPT 扩容批卷三供给卷
   ── DTPT_Bridge_Rot.v 本体 12 前件槽：普查底册
      §2.5/§3（§S8/§S9 焦普查）登记序：本卷 12 槽全做（底册初判全 🟢）。
      红线遵守：W-DTPTTRUTH-DIAG-01 七槽（diag_closed 形，Truth 域）绝对禁碰
      （本域零此形，零触碰实录）；宿主/桥面禁重计铁律（X §1.1/§4.3-4）：§S8/§S9
      宿主面槽（DTPT_Rotation.v :1952 系，dtr_ Rotation 106 槽版图内已闭合）
      零触碰零重做，本卷仅供桥面卫哨 12 槽；Truth 🟡 五槽（存疑-②）候二审
      不做；Bridge_Dep 4 槽（残差 tbd_，先与 abl_dtr_ 系对拍）本卷不做。
   ① 模块名+使命：abl_dtpt_rot_bridge_supply——逐槽一条供给定理（tbr_ 前缀），
      陈述形＝「库内既有组合 ⟹ DTPT_Bridge_Rot X 槽前件」：SortedQ 族七槽走
      P0 排序计算律通路（吃宿主既有件 xq_P0_sorted 直供，X §4.3-2 判定通路）；
      NAT 界四槽 born-in-place（ discriminate＋算术闭判定）；BOOL 判定面一槽
      vm_compute 计算律（X §2.5 槽 2 初判通路）；推导只吃已导出内容（Require
      库件三件：DTPT＋DTPT_Entropy＋DTPT_Rotation；桥面槽前件零 Bridge_Rot
      本体名依赖，第三 Require 供 phase_dev 判定器名；AQ 坑卡① 照办：透传
      Require 不导出短名，本件自 Require 全链并显式 Import，Import 序照宿主
      桥接件原序 DTPT→DTPT_Entropy→DTPT_Rotation，SortedQ 短名解析位同宿主）。
      供给形三类分布：计算律形 8 条（SortedQ 七槽＝P0 排序律＋BOOL 一槽＝
      phase_dev 计算判定）＋NAT 界闭判定 4 条（discriminate/lia born-in-place）。
      【参数位对照总表（12 槽＝底册 §2.5 登记号）】
        槽 1  →tbr_rotc_class_sharp_ub_set_h1（:77，SortedQ＝P0 排序律）
        槽 2  →tbr_phase_dev_stable_set_h1（:122，BOOL phase_dev 计算判定，
                实例 []×0 落 false）
        槽 3  →tbr_H_adj_Pmid_seam_set_h1（:201，NAT k=1 <> 0）
        槽 4  →tbr_H_adj_Pmid_seam_set_h2（:202，NAT 1 < length [0;1;2]）
        槽 5  →tbr_Pmid_sorted_collapse_set_h1（:238，SortedQ＝P0 排序律）
        槽 6  →tbr_H_adj_Pmid_sorted_exact_set_h1（:253，SortedQ＝P0 排序律）
        槽 7  →tbr_H_adj_Pmid_sorted_spread_set_h1（:264，SortedQ＝P0 排序律）
        槽 8  →tbr_H_adj_Pmid_sorted_ub2_set_h1（:274，SortedQ＝P0 排序律）
        槽 9  →tbr_H_adj_Pmid_ub_gen_set_h1（:284，NAT k=2 <> 0）
        槽 10 →tbr_H_adj_Pmid_ub_gen_set_h2（:285，NAT 2 < length [0;1;2;3]）
        槽 11 →tbr_H_adj_Pmid_endpoints_sorted_set_h1（:344，SortedQ＝P0 排序律）
        槽 12 →tbr_H_lam_pmid_sorted_consistency_set_h1（:457，SortedQ＝P0 排序律）
      【应用演示（底册 §4.2 A 直供形使用面）】
        rotc_class_sharp_ub_set (P0 w) k (tbr_rotc_class_sharp_ub_set_h1 w)
          ⟹ QleT (H_adj (rotc k (P0 w))) (2 * (lastq (P0 w) - hd 0 (P0 w)))
          ——2·spread 锐化上界 QleT 证书随应用落地；
        phase_dev_stable_set [] 0%nat (tbr_phase_dev_stable_set_h1)
          ⟹ QeqT (H_adj (rotc 0%nat [])) (H_adj (P0 []))；
        H_adj_Pmid_seam_set l s 1%nat (tbr_H_adj_Pmid_seam_set_h1)
          (tbr_H_adj_Pmid_seam_set_h2 于 l:=[0;1;2] 实例域)
          ⟹ 中相接缝分解 QeqT 证书；§8⑥ ub_gen 双卫哨同法（h9/h10）；
          §8②③④⑤⑩/§9④ 六 SortedQ 槽各随宿主陈述喂 P0 排序律落地（§8②坍缩
          sumbool 判定面于 P0 域恒左支——xq_sortQ_P0_id 在档可推）。
      【降档口径】供给定理取「槽前件的可满足实例/计算律提供形」：宿主槽前件
        为全称变元上的卫哨假设（SortedQ l／phase_dev l k = false／k <> 0%nat／
        (k < length l)%nat），无条件泛形多不恒真（phase_dev l k = false 于偏差
        对落假——宿主 phase_dev_witness_set [0;1;2]×1 落 true 反例在档；
        k < length l 于超界 k 落假），故供给＝给出现档可判定通路：SortedQ 七槽
        全取 P0 排序计算律全称形（∀l, SortedQ (P0 l)，宿主既有件直供，闭实例
        见证列 [0;0;2]/[0;1;2] 均为 P0 像——sorted_wit_002（Rotation :1233）与
        xq_sortQ_P0_id（Entropy :314）在档互证，X §4.3-2 通路）；NAT 界取具体
        数值实例域；BOOL 取 vm_compute 闭式实例。宿主结论方向不桥假命题
        （phase_dev_stable 只取 false 向，本件同向不越界）。
   ② 依赖清单：Stdlib（QArith.QArith/List/Bool/Arith/Lia）＋库件 DTPT、
      DTPT_Entropy、DTPT_Rotation（统一缓存 vo_local_world_unified_0930 在册
      .vo 只读依赖，零重编零级联；本件 Require 顺序＝先 stdlib 后库序，禁逆向；
      SortedQ/xq_P0_sorted/xq_sortQ_P0_id 在 DTPT_Entropy.DTPT_Entropy，
      phase_dev 在 DTPT_Rotation.DTPT_Rotation，P0/H_adj/lastq/hd 在 DTPT.DTPT
      经依赖链在档；本件零 Require DTPT_Bridge_Rot——桥面 12 槽前件名面
      （SortedQ/phase_dev/nat 序）全宿主依赖链既有，零桥本体名依赖实录）。
   ③ 对标行：同族卷二另半（abl_dtpt_bridge_dig_supply.v）工艺＝
      A 直供形/头注五字段/查重登记块/绿判四件套/应用演示入头注，同族工艺
      直接复用；设计依据＝普查底册 §2.5（Bridge_Rot
      12 槽全 🟢）＋§3（§S8/§S9 焦普查，桥面/宿主面分账）／§4.1（卷3 tbr_
      计划，件名照设计 abl_dtpt_rot_bridge_supply）；坑卡预读：AQ（无 Not
      大写名——本件零 Not 大写位；`<>` 记法本件两处（槽 3/9）＝宿主 k <> 0%nat
      槽前件逐字形状，宿主桥接件同记法在档编译绿；grep -c 零命中退码 1 断链
      ——道闸与绿判各步分号独立跑）/AL（语句面零 Or 形出口——宿主 §8②
      sumbool 支面为宿主既有件，本件陈述零使用）/AS（trans 三实参——本件零
      trans 引用）/AO（Q 值序列世界甄别：本件 list Q 面与宿主同域，零混载）。
   ④ 构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set/Prop 离散
      卫哨载体（Q/nat/bool/list Q 全宿主既有，本件零新增数据载体、零
      Definition/Fixpoint/Inductive）；语句面零混载（零析取/零存在/零经典
      逻辑）；供给对象全为可判定离散卫哨（排序 Prop 面/nat 序/bool 判定面），
      可提取性由被引宿主件既有提取锚承载（宿主桥接件 §7/§8.6/§9.5 b6_/b7_/
      b12_ 提取块在册——其 SortedQ 前提＝Prop 整参提取擦除惯例，本件供给
      前件同法擦除，零 Obj.magic 新增面）；nat 层显式 %nat、Q 字面一律 %Q
      （防 Q_scope 劫持）；lia 用面＝nat 界两参数位（宿主桥接件 §4 rotc_spectrum_
      bound_set 同款在库），构造性由 Print Assumptions 全 Closed 实证。
   ⑤ 编译配方（池 cwd＝沙箱/现役/abl_tmine04_pool/dtpt_v2b，路径绝对化）：
      source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_rot_bridge_supply.v
      （道闸：起编前 ps -axo comm|grep -ci rocq 独立跑、禁入 && 链；绿判
      四件套：EXIT=0 无管道真取／日志真错行计 0＋逐条 Print Assumptions 全
      Closed／.vo 头 8 字节与宿主 DTPT_Bridge_Rot.vo 同款／.vo 新于 .v；
      第五证 rocq check 分号独立跑。）
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑、零节变量声明位，全部供给定理 Qed 闭合；12 供给定理逐条
      Print Assumptions 全 Closed；DTPT_Bridge_Rot.v 宿主零字节不动（零重编）。
   ========================================================================== *)

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）名面：本件全部顶层名 12 枚全 tbr_ 新前缀（tbr_＝卷三专用       *)
(*   prefix，X §4.1 计划名），Live 全树＋统一缓存 vo_local_world_unified_  *)
(*   0930 全量 grep 零命中（施工前复检实录）；与已占 dtd_/  *)
(*   dte_/dtr_/dtb_ 四前缀及卷一 tdt_、卷二 tdg_、同族卷另半     *)
(*   tdbg_ 专prefix 零撞零别名转发；件名 abl_dtpt_rot_bridge_supply.v    *)
(*   全树零命中（X 设计件名照录）。                                      *)
(*   （二）槽面：本卷 12 槽＝底册 §2.5 登记号逐位对表（①总表），坐标      *)
(*   12 位（:77/:122/:201/:202/:238/:253/:264/:274/:284/:285/:344/:457）  *)
(*   与底册现档核验逐位吻合，零漂移；零双供零漏账（12＝Bridge_Rot   *)
(*   桥面槽总数，对账平）；同形槽（1↔5↔6↔7↔8↔11↔12 七槽 SortedQ 前件）    *)
(*   逐位各立一条（逐槽一条铁律），供给语句同形系槽前件同形所致，非重复    *)
(*   计数；宿主/桥面禁重计：§S8/§S9 宿主面槽（dtr_ Rotation 版图内）零     *)
(*   触碰零重做，本卷槽账对宿主面零交集。                                *)
(*   （三）宿主界：DTPT_Bridge_Rot.v 本体零字节不动、零重编；两档 diff    *)
(*   逐字同档实测；本件 Require 统一缓存只读在册 .vo，宿主重编  *)
(*   零级联于本件，本件重编零级联于宿主。                                *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith Lia.
Import ListNotations.

Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

Open Scope Q_scope.

(* ========== 批一：§3/§5 主件卫哨族两槽（#1-2） ========== *)

(* 槽 1（DTPT_Bridge_Rot.v:77 rotc_class_sharp_ub_set 槽1）：SortedQ l ——
   P0 排序计算律全称形：宿主既有件 xq_P0_sorted（DTPT_Entropy.v:300）直供。
   应用后 rotc_class_sharp_ub_set 于 P0 域给出 2·spread 锐化上界 QleT 证书
   （头注①演示；X §4.3-2 判定通路）。 *)
Theorem tbr_rotc_class_sharp_ub_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 2（:122 phase_dev_stable_set 槽1）：phase_dev l k = false —— bool
   判定面计算律实例（空表零偏差域：P0 []＝rotc 0 []＝[]，两侧 H_adj 皆零，
   Qeq_bool 落真、negb 落假）：vm_compute 一步闭项。应用后
   phase_dev_stable_set 给出 QeqT (H_adj (rotc 0%nat [])) (H_adj (P0 []))。
   反例面：phase_dev [0;1;2] 1 = true（宿主 phase_dev_witness_set 在档），
   故实例域供给为唯一诚实形。 *)
Theorem tbr_phase_dev_stable_set_h1 : phase_dev [] 0%nat = false.
Proof.
  vm_compute. reflexivity.
Qed.

(* ========== 批二：§8 桥面卫哨族九槽（#3-11） ========== *)

(* 槽 3（:201 H_adj_Pmid_seam_set 槽1）：k <> 0%nat —— 正值实例域 k=1：
    构造子互斥 discriminate。应用（连同槽 4）后 H_adj_Pmid_seam_set 给出
   中相接缝分解 QeqT 证书。语句含 <> 位＝宿主槽前件逐字形状。 *)
Theorem tbr_H_adj_Pmid_seam_set_h1 : 1%nat <> 0%nat.
Proof.
  intros H. discriminate H.
Qed.

(* 槽 4（:202 H_adj_Pmid_seam_set 槽2）：(k < length l)%nat —— 实例域
   k=1、l=[0;1;2]（长 3）：nat 闭判定 lia（宿主桥接件 §4 同款在库）。 *)
Theorem tbr_H_adj_Pmid_seam_set_h2 : (1 < length [0%Q; 1%Q; 2%Q])%nat.
Proof.
  cbn. lia.
Qed.

(* 槽 5（:238 Pmid_sorted_collapse_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条（同吃 xq_P0_sorted）。应用后 Pmid_sorted_collapse_set 于 P0 域
   落坍缩左支（xq_sortQ_P0_id：P0 l 排序即恒等，坍缩件直供）。 *)
Theorem tbr_Pmid_sorted_collapse_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 6（:253 H_adj_Pmid_sorted_exact_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条。应用后给出中相熵 == H_adj l 精确值 QeqT 证书。 *)
Theorem tbr_H_adj_Pmid_sorted_exact_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 7（:264 H_adj_Pmid_sorted_spread_set 槽1）：SortedQ l —— P0 排序
   计算律逐槽一条。应用后给出 1·spread 精确值 QeqT 证书。 *)
Theorem tbr_H_adj_Pmid_sorted_spread_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 8（:274 H_adj_Pmid_sorted_ub2_set 槽1）：SortedQ l —— P0 排序计算律
   逐槽一条。应用后给出 2·spread 上界 QleT 证书（§8 桥面 all_B7 使用链
   供给需求位，底册 §3 判）。 *)
Theorem tbr_H_adj_Pmid_sorted_ub2_set_h1 : forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* 槽 9（:284 H_adj_Pmid_ub_gen_set 槽1）：k <> 0%nat —— 正值实例域 k=2
   （与槽 3 异值逐槽一条）：discriminate。 *)
Theorem tbr_H_adj_Pmid_ub_gen_set_h1 : 2%nat <> 0%nat.
Proof.
  intros H. discriminate H.
Qed.

(* 槽 10（:285 H_adj_Pmid_ub_gen_set 槽2）：(k < length l)%nat —— 实例域
   k=2、l=[0;1;2;3]（长 4，与槽 4 异值逐槽一条）：nat 闭判定 lia。 *)
Theorem tbr_H_adj_Pmid_ub_gen_set_h2 : (2 < length [0%Q; 1%Q; 2%Q; 3%Q])%nat.
Proof.
  cbn. lia.
Qed.

(* 槽 11（:344 H_adj_Pmid_endpoints_sorted_set 槽1）：SortedQ l —— P0 排序
   计算律逐槽一条。应用后给出两端点熵 QeqT 双证书 Type 积。 *)
Theorem tbr_H_adj_Pmid_endpoints_sorted_set_h1 :
  forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* ========== 批三：§9 桥面卫哨一槽（#12） ========== *)

(* 槽 12（:457 H_lam_pmid_sorted_consistency_set 槽1）：SortedQ l —— P0
   排序计算律逐槽一条。应用后给出 λ-插值与 H_lam 相容性 QeqT 证书
   （§9 桥面完备性闭合位，底册 §3 判使用面开放候选）。 *)
Theorem tbr_H_lam_pmid_sorted_consistency_set_h1 :
  forall l : list Q, SortedQ (P0 l).
Proof.
  exact xq_P0_sorted.
Qed.

(* ========== 假设面自查（公理面自审附件，12 供给定理逐条打印） ========== *)
Print Assumptions tbr_rotc_class_sharp_ub_set_h1.
Print Assumptions tbr_phase_dev_stable_set_h1.
Print Assumptions tbr_H_adj_Pmid_seam_set_h1.
Print Assumptions tbr_H_adj_Pmid_seam_set_h2.
Print Assumptions tbr_Pmid_sorted_collapse_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_exact_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_spread_set_h1.
Print Assumptions tbr_H_adj_Pmid_sorted_ub2_set_h1.
Print Assumptions tbr_H_adj_Pmid_ub_gen_set_h1.
Print Assumptions tbr_H_adj_Pmid_ub_gen_set_h2.
Print Assumptions tbr_H_adj_Pmid_endpoints_sorted_set_h1.
Print Assumptions tbr_H_lam_pmid_sorted_consistency_set_h1.
