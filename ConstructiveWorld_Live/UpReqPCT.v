(* UpReqPCT.v — 签名迁移批 5 波 4 桥席 C3：reqRealSelfSS（req StateSpace 迷你类，
   clim:=lim 实例化）+ reqPCTDefs（PCT 定义层）+ PCTRealBridge 2 件 req 平移。
   工作单：attn\批5基建层处置清单-20260909.md 波4/(c) 桥C3（§0.3 / §7.4 / §8 / §9.2）。
   母本：CW_ConstructiveWorld_219：
     Class StateSpace（收敛面 3 字段）        L1160-1187（clim L1183 / clim_unique L1184 /
                                              cauchy_complete_S L1186-1187）
     Definition RealSelfSS（clim:=lim 桥本体）L1219-1247（收敛面实例化 L1242-1244）
     Module PCC is_truth / is_attractor      L1581-1585
     Section PCTRealBridge（Let SS_R 消费形） L1710-1780（2 件 L1742 / L1757）
   上游：CW219 基座（setoid 接口自带 lim/lim_unique/cauchy_complete 字段
   L40589-40596——清单 §0.3 桥C3 判词的落位依据）；UpReqAlgebra 按需未消费故未
   Require；在飞 5 件零 Require（工作单红线）。
   ----------------------------------------------------------------
   桥设计（逐字段对账）：
   1. reqRealSelfSS 迷你记录 = Id StateSpace（L1160-1187，21 字段）的**收敛面
      3 字段** req 镜像（清单 §8 行 C3「req StateSpace 迷你类（clim:=lim）」——
      PCT 定义层消费面恰为收敛面；代数/度量面 18 字段属清单 §8 行 4
      reqStateSpace+reqHilbertSpace 桥（抽象类转写，他席交付），本席不越界不撞名）：
        clim              L1183 → rself_clim
        clim_unique       L1184 → rself_clim_unique（结论位 Id→req）
        cauchy_complete_S L1186 → rself_cauchy_complete（语句逐字同形，
                                     metric/lt/NatLe 全基座字段原样）
   2. reqRealSelfSS_inst = Id RealSelfSS（L1219-1247）收敛面实例化的 req 镜像：
        rself_clim := lim / rself_clim_unique := lim_unique /
        rself_cauchy_complete := cauchy_complete——即清单「clim:=lim 实例化」
        桥本体（Id L1242-1244 注记逐位对应）。
   3. reqPCTDefs 定义层：
        reqPCT_is_truth     ← Id is_truth     L1581-1582（语句逐字同形，le 直引）
        reqPCT_is_attractor ← Id is_attractor L1584-1585（clim 位 = rself_clim；
              Id 桥 dynamics Variable 以 fun _ => dyn 闭名消费 L1738 区——req 形
              把该 dynamics 位前移为显式参 dyn，签名差异注记：dyn 已代 dynamics）
   4. iterate 直接复用：CW219 L1394 多态纯 nat Fixpoint（零 Id 内容；nat 层不
      迁移口径同清单 §7.12 grpo_count_one 消费 count 机先例）。
   ----------------------------------------------------------------
   交付对账（清单 §7.4 (c) 2 件）：
     req_pct_attractor_is_lim    ← pct_attractor_is_lim    L1742（语句同构，
                                    双向 exact——清单 L276「桥后证明 exact h
                                    定义级平凡」判词兑现：rself_clim RSS_R 经
                                    reqRealSelfSS_inst 定义链 delta/iota 级
                                    化简为 lim）
     req_pct_truth_is_global_min ← pct_truth_is_global_min L1757（同上）
   纪律：纯构造性；Set 层语句（le/req/乘积积全基座 Set 形）；纯 term-mode
   （split/intro/exact）；核心件 Qed。G3 提取探针独立文件（验后删）。 *)

Require Import CW_ConstructiveWorld_219.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 桥 C3 本体 1：reqRealSelfSS——Id StateSpace 收敛面 3 字段的       *)
(*   req 迷你镜像（清单「迷你类」口径；全 Set 层）                  *)
(* ============================================================ *)
Record reqRealSelfSS (R : Set) (RIS : RealInterfaceEnhancedSetoid R) := {
  rself_clim : (nat -> R) -> R -> Set;
  rself_clim_unique : forall (u : nat -> R) (l1 l2 : R),
    rself_clim u l1 -> rself_clim u l2 -> req l1 l2;
  rself_cauchy_complete :
    forall u : nat -> R,
      (forall eps : R, lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : R => rself_clim u l)
}.

(* ============================================================ *)
(* 桥 C3 本体 2：reqRealSelfSS_inst——clim:=lim 实例化（Id           *)
(*   RealSelfSS L1242-1244 收敛面字段逐位对应；桥本体）             *)
(* ============================================================ *)
Section ReqRealSelfSSInst.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Definition reqRealSelfSS_inst : reqRealSelfSS R RIS :=
  {| rself_clim := lim;
     rself_clim_unique := lim_unique;
     rself_cauchy_complete := cauchy_complete |}.
End ReqRealSelfSSInst.

(* ============================================================ *)
(* reqPCTDefs 定义层 + 2 件（Id PCTRealBridge L1710-1780 同构：      *)
(*   Let RSS_R := 实例 的消费形）                                   *)
(* ============================================================ *)
Section ReqPCTBridge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
(* Id L1737 Let SS_R : StateSpace RI := @RealSelfSS (@RI_base RI) 同位 *)
Let RSS_R : reqRealSelfSS R RIS := reqRealSelfSS_inst.

(* Id PCC is_truth L1581-1582 同构（le = setoid 接口 le 字段，语句逐字同形） *)
Definition reqPCT_is_truth (L : R -> R) (s : R) : Set :=
  forall s' : R, le (L s) (L s').

(* Id PCC is_attractor L1584-1585 同构：clim 位 = rself_clim；Id 桥以
   dynamics := fun _ => dyn 闭名消费，req 形把 dynamics 位前移为显式 dyn
   （签名差异注记：dyn 已代 dynamics，见头注 3）。 *)
Definition reqPCT_is_attractor (dyn : R -> R) (s : R) : Set :=
  forall s0 : R, @rself_clim R RIS RSS_R (fun n => iterate dyn n s0) s.

(* 基座 pct_attractor_is_lim L1742（件 1）：is_attractor（clim:=lim 实例化）
   与 lim 收敛语句的双向定义级桥——双向 exact（rself_clim RSS_R 经
   reqRealSelfSS_inst 定义链化简为 lim，转换级闭合）。 *)
Theorem req_pct_attractor_is_lim :
  forall (dyn : R -> R) (L : R -> R) (s : R),
    (reqPCT_is_attractor dyn s ->
     forall s0 : R, lim (fun n => iterate dyn n s0) s) *
    ((forall s0 : R, lim (fun n => iterate dyn n s0) s) ->
     reqPCT_is_attractor dyn s).
Proof.
  intros dyn L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

(* 基座 pct_truth_is_global_min L1757（件 2）：is_truth 与全局最小点语句的
   双向定义级桥（reqPCT_is_truth 定义即语句本体，双向 exact）。 *)
Theorem req_pct_truth_is_global_min :
  forall (L : R -> R) (s : R),
    (reqPCT_is_truth L s -> forall s' : R, le (L s) (L s')) *
    ((forall s' : R, le (L s) (L s')) -> reqPCT_is_truth L s).
Proof.
  intros L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

End ReqPCTBridge.
