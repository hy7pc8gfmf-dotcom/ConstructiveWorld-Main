(* ============================================================ *)
(* LoHiSqueeze.v —— 席位P7D（批次 E-STAGING-P7D）合璧包装定理     *)
(*                                                                *)
(* 使命：论文7《率即算法》夹逼包装——P7A 已证 lo=e^{−Δ/T}<1        *)
(*   （Paper7Ablation.p7a_lo_lt_one），P7C 已证对偶 hi=e^{Δ/T}>1  *)
(*   （P7BoundedSoftmaxDeep.p7d_hi_gt_one）。本件把两件合璧为单    *)
(*   件陈述 lt lo one ∧ lt one hi（Set 层 And = prod，S01:66），   *)
(*   再以 lt_trans 一步导出夹逼推论 lt lo hi，最终消费             *)
(*   p7a_delta_star_pos（δ*=lo²>0）导出 δ* ∈ (0,1) 完整包装，     *)
(*   并以 p7a_omd_pos＋p7a_omd_lt_one 合龙 κ:=1−δ*∈(0,1) 前件包   *)
(*   （P7A 卡所记论文 §6.3「开放工作第1项」的收口件）。            *)
(*                                                                *)
(* 侦查对账（两组前提兼容性，探针 Check 实测定谳）：               *)
(*   p7a_lo_lt_one 出节形（Section P7aSoftBound；Rocq 9 出节剪枝  *)
(*   未用变量 temp/temp_pos——语句与证明体均不消费它们）：          *)
(*     forall Delta (Delta_pos : lt zero Delta) expf expf_zero    *)
(*            expf_mono_lt invT, lt zero invT ->                 *)
(*            lt (expf (mult invT (opp Delta))) one  (RI 隐式)    *)
(*     ——通用 invT 形，invT := inv_pos temp temp_pos 处经          *)
(*     inv_pos_pos temp temp_pos 放电；                            *)
(*   p7d_hi_gt_one 全称形（无 Section，8 参齐不剪枝）：            *)
(*     forall temp temp_pos Delta Delta_pos expf expf_pos          *)
(*            expf_zero expf_mono_lt,                             *)
(*            lt one (expf (mult (inv_pos temp temp_pos) Delta)). *)
(*   并集 = 8 变量 {temp,temp_pos,Delta,Delta_pos,expf,expf_pos,  *)
(*   expf_zero,expf_mono_lt}，零冲突零冗余——同一 softmax 实例     *)
(*   上下文同时放电两件，兼容 ✔。剪枝差异（p7a 少 temp 面、       *)
(*   p7d 少 invT 自由度）在包装层互相补齐，正合璧之趣。            *)
(*                                                                *)
(* δ*<1 支的出处：任务书所指 p7a_omd_lt_one 实为 1−δ*<1（κ<1，    *)
(*   不含 δ*<1 信息，探针签名核实在案）；δ*<1 在件 c 从合璧件左支  *)
(*   lo<1 与 lo>0 经 lt_mult_compat＋lt_id_r＋lt_trans 新导（语句  *)
(*   与基座 AttnDoeblin.bs_delta_star_lt_one:584 对齐，进路更短——  *)
(*   不经 lo·hi=1 恒等式，纯序论三步）。κ 件（段二）消费            *)
(*   p7a_omd_pos（δ*<1 ⟹ 0<κ）＋p7a_omd_lt_one（lo_pos ⟹ κ<1），  *)
(*   出节携带 Context {DO : DecidableOrder RI}（fa53 消费链所致，  *)
(*   隐式不可反推，@ 全参形喂参——P7A 卡消费法先例）。             *)
(*                                                                *)
(* 编译根：基座 ConstructiveWorld_vo_901/ 内 fa53_compat_abs.vo   *)
(*   （Sep17 05:04）、AttnDoeblin/CW_219 vo（Sep17 03:16）对       *)
(*   S01_BaseRing.vo（Sep18 04:50 重编）digest 漂移——基座原生      *)
(*   Paper7Ablation.vo 单根加载同样报 inconsistent assumptions    *)
(*   （探针实证），故按 CYA7b/CZC10 处置定式走复制盘 /tmp/p7droot  *)
(*   单根：以 /tmp/czc10_base 一致层（S01/AttnDoeblin/CW_219 探针  *)
(*   全 OK）覆盖基座骨架，fa53/Paper7Ablation/P7BoundedSoftmaxDeep *)
(*   单源对齐重编（各 EXIT=0、PA 全 Closed）。vo_901 正本零碰；    *)
(*   消融50/ 的 fa53 编译副产物已移 /tmp/p7d_stale 隔离（防        *)
(*   CYA7b 双根撞名墙姊妹坑）。                                    *)
(*                                                                *)
(* 红线自审：语句面全 Set 层（合取用 S01 And=prod，零 Prop 泄露）； *)
(*   五禁词零出现；非平凡性＝两席异构出口（含剪枝形）的合璧规范化  *)
(*   ＋序论链新导；原 vo_901 正本零改；前缀 lhs_ 全库防撞           *)
(*   （grep 零命中）。                                             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ################ 段一：合璧包装、夹逼推论、δ*∈(0,1)（无 DO） #### *)
(* 对照 AttnDoeblin.v L544-548：lo := expf(invT·oppΔ)、hi := expf(invT·Δ)。 *)

Section LhsPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* 件 a：合璧包装——lt lo one ∧ lt one hi（Set 层 And = prod）。
   左支消费 p7a_lo_lt_one（剪枝形：Delta/Delta_pos/expf/expf_zero/
   expf_mono_lt 五参＋invT；inv_pos_pos 放电 lt zero invT）；
   右支消费 p7d_hi_gt_one（全称 8 参形，temp 面齐全）。 *)
Theorem lhs_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* 件 b：夹逼推论——lt lo hi（lt_trans 一步，两支皆出自合璧件）。
   语句与基座 AttnDoeblin.bs_lo_lt_hi:565 对齐，前提面同（B 类证书）。 *)
Theorem lhs_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst lhs_lo_lt_one_hi) (snd lhs_lo_lt_one_hi)).
Qed.

(* 件 c：0 < δ* < 1 完整包装（Set 层 And）。
   左支：p7a_delta_star_pos（探针签名 forall lo, lt zero lo -> …；
   DO/temp 面均已被出节剪枝，lo_pos := expf_pos(invT·oppΔ) 直喂）。
   右支（δ*<1 新导）：lo<1（合璧件左支）＋lo>0 ⟹ lo·lo < lo·1
   （lt_mult_compat 右乘 lo 保严格序）＝lo（mult_one 右单位律经
   lt_id_r 降形）<1（再消费 lo<1）——lt_trans 合龙。 *)
Theorem lhs_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End LhsPair.

(* ############ 段二：κ := 1−δ* ∈ (0,1) 前件包合龙（DO 节） ######## *)
(* p7a_omd_pos/p7a_omd_lt_one 出节保留 DO（fa53 消费链），其隐式参
   不可由结论反推，须 @ RI DO 全参形喂参（P7A 卡消费法先例）。 *)

Section LhsStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* 件 d：0 < 1−δ* < 1 完整包装（论文 §6.3 的 κ∈(0,1) 前件包）。
   左支：p7a_omd_pos 消费件 c 右支（δ*<1 ⟹ 0<κ）；
   右支：p7a_omd_lt_one 消费 lo_pos（0<δ* ⟹ κ<1）。
   两支出节前件（δ*<1 前件／lo_pos 前件）分别由段一件 c 与
   expf_pos 字段证书放电。 *)
Theorem lhs_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End LhsStar.

(* ---- PA 自检段（G1 min-pa 与 G4 审查留痕面；全出节全局名） ---- *)
Print Assumptions lhs_lo_lt_one_hi.
Print Assumptions lhs_lo_lt_hi.
Print Assumptions lhs_delta_star_bounded.
Print Assumptions lhs_omd_bounded.
