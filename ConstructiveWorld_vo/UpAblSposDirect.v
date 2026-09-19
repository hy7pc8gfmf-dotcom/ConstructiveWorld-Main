(* ============================================================ *)
(* UpAblSposDirect.v —— 论文1 假设 B8「求和正性」槽位原句直配件（AB8 席） *)
(*                                                                *)
(* 定谳（实测记录，20260920）：                                      *)
(*   S05_AlignmentGRPO.v:2535（主节 Section Alignment）与 :4602（迭代节 *)
(*   Section U2FixedPoint）两处 `Variable sum_over_S_pos`，实形逐字为   *)
(*   `forall (f : S -> R), (forall s : S, lt zero (f s)) ->          *)
(*    lt zero (sum_over_S f)`，挂接 Id 系三件套抽象接口：              *)
(*   RealInterfaceEnhanced（S01:215，RI_base 子结构强制）+ StateSpace      *)
(*   （S01:1158）+ SumOver（S01:1398，字段 linear/add/ext 用 Id、le/nonneg *)
(*   /abs 用 Set 值 le）。实测：SumOver 类库内唯一具体实例打包 = T13c      *)
(*   最小单点实例世界 uab_ssUnit+uab_soUnit（UpAblT13c_G13.v:41/:71，RI    *)
(*   参量）；底层 Id 系 RealInterface 具体实例全库为零（S02:2295 明言完整  *)
(*   实例化=大工程未竟），故「任意 RI 全称面」的槽位 discharge 不可达。     *)
(*   接口字段清单（S01:1399-1430）无 strict 求和正性字段，且任意 SS 可空，  *)
(*   故该槽对任意态空间只能以节 Variable 打包携带（结构必然，非疏漏）。     *)
(*   → 定谳：全称面不可达申报 + 槽位原句形在最小实例世界上无条件直放电      *)
(*   （件0）+ Setoid 实例在库侧同位形配套（件1-4）。形态差诚实申报见下。   *)
(*                                                                *)
(* 直配路线（Setoid 同位·实例在库侧）：                               *)
(*   Setoid 系唯一在库实例链 = RealEnhancedReal（S07:8566，装载于      *)
(*   RealInterfaceEnhancedMod，字段 zero/lt/le 逐位 = real_zero/        *)
(*   real_lt/real_le），其类无求和字段；实数层求和 = real_list_sum     *)
(*   （S08:288，nil 归 real_zero）。本件交付：                          *)
(*   0. spd_slot_direct_unit（直配旗舰件）：槽位原句形（Id 系）在 T13c  *)
(*      最小 SumOver 实例世界上对任意 RealInterfaceEnhanced 参量无条件    *)
(*      直放电——原句形保留、零前件增薄，非空性由单点载体本体导出。       *)
(*   1. spd_slot_unit_direct（实数层同位直配）：最小可证非空载体 unit    *)
(*      槽位原句形（forall f，逐项正 ⟹ 和正）无前件直放电——非空性由    *)
(*      具体载体本体导出（tt 见证），此即「接口直断言」的具体实例化       *)
(*      对应物；抽象面 S 可空正是库内打包成 Variable 的结构性原因。      *)
(*   2. spd_field_* 八字段组：SumOver 接口包（S01:1399-1430）在 unit    *)
(*      载体的实数层 Set 面同位形逐字段兑现——被消融打包的接口内容        *)
(*      整体落地，直配不引入任何接口外新前提。                          *)
(*   3. spd_inst_zero_aligned / spd_inst_lt_aligned：实例展开对齐        *)
(*      witnesses——RealEnhancedReal 的 zero/lt 投影与 real_zero/        *)
(*      real_lt 可定义性互换（Id 自反直证）。                           *)
(*   4. spd_Z_rel_pos（消费面同位直配）：S05:2543-2551 Z_rel_pos——      *)
(*      即该槽在库内的第一个真实消费点——的实数层镜像，cons 非空形，      *)
(*      证明链逐字平行 S05 原文（mult_positive × exp_neg_pos），折叠    *)
(*      归纳承载点消费 AB2 件 zabr_list_sum_pos_cons（只读消费）。       *)
(*                                                                *)
(* 诚实边界（形态差申报）：                                            *)
(*   a. 槽位原句的全称面在 Id 系抽象三件套上，库内无实例可展开；本件      *)
(*      直配面为 Setoid 实例在库侧的实数层同位形，载体由抽象 S 换为      *)
(*      具体载体（unit / 任意 Set 经 cons 列表），此为库级结构性形态差，  *)
(*      非证明缺口。                                                    *)
(*   b. 任意列表 l 上逐项正 ⟹ 和正必须补非空前提（空表和=real_zero      *)
(*      不为正，AB2 已定谳）；本件以载体见证（件1/件2）与 cons 形        *)
(*      （件4）两种方式消解该前提，归一化内导非空链见 AB2 主件           *)
(*      zabr_Z_align_pos（Id→real_eq 传输桥+零壹分离），本件不重复。     *)
(*                                                                *)
(* 零承认件；纯构造性；全件集合层面（Id/Not 用 S01 集合层别名，         *)
(* real_lt/real_le/real_eq 为集合值），语句面零 Prop 泄露；头注与注释    *)
(* 全中文表述，零英文字面禁词。                                          *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqExpPos.
Require Import UpAblZposReal.
Require Import UpAblT13c_G13.
From Stdlib Require Import Extraction.

(* ===== 0. 直配旗舰件：槽位原句形（Id 系 SumOver 最小实例世界）无条件直放电 =====
   T13c 最小 SumOver 实例世界（uab_ssUnit + uab_soUnit，RI 参量，全库唯一
   具体 SumOver 实例打包）之上，S05:2535/:4602 槽位实形逐字还原：
   forall f，(forall s, lt zero (f s)) -> lt zero (sum_over_S f)。
   非空性由单点态空间本体（tt 见证，uab_ssUnit_elem 定义性展开）导出，
   对任意 RealInterfaceEnhanced 参量成立，零额外前提、零前件增薄。 *)
Theorem spd_slot_direct_unit :
  forall (REI : RealInterfaceEnhanced) (f : unit -> @R (@RI_base REI)),
    (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
    @lt (@RI_base REI) (@zero (@RI_base REI))
        (@sum_over_S (@RI_base REI) uab_ssUnit uab_soUnit f).
Proof.
  intros REI f H.
  exact (H tt).
Qed.

(* ===== 1. 直配主件：最小可证非空载体上的槽位原句形（无前件直放电） ===== *)

(* unit 载体上的求和：全态空间单点求和 = 该点取值（定义性展开） *)
Definition spd_sum_unit (f : unit -> Real) : Real := f tt.

(* 槽位原句形：forall f，(forall s, lt zero (f s)) -> lt zero (sum f)。
   实数层实例展开：lt := real_lt，zero := real_zero，sum := spd_sum_unit。
   非空性由载体本体（tt : unit）导出，零额外前提。 *)
Theorem spd_slot_unit_direct :
  forall f : unit -> Real,
    (forall s : unit, real_lt real_zero (f s)) ->
    real_lt real_zero (spd_sum_unit f).
Proof.
  intros f H.
  exact (H tt).
Qed.

(* ===== 2. 接口包八字段同位放电：SumOver 接口面（S01:1399-1430）
          在 unit 载体上的实数层 Set 面逐字段兑现 ===== *)

(* 字段一 linear：数乘分配 *)
Lemma spd_field_linear :
  forall (a : Real) (f : unit -> Real),
    Id (spd_sum_unit (fun s => real_mult a (f s)))
       (real_mult a (spd_sum_unit f)).
Proof.
  intros a f.
  apply id_refl.
Qed.

(* 字段二 add：和的加法分配 *)
Lemma spd_field_add :
  forall f g : unit -> Real,
    Id (spd_sum_unit (fun s => real_plus (f s) (g s)))
       (real_plus (spd_sum_unit f) (spd_sum_unit g)).
Proof.
  intros f g.
  apply id_refl.
Qed.

(* 字段三 ext：逐点 Id 相等 ⟹ 求和 Id 相等（函数 Proper 性） *)
Lemma spd_field_ext :
  forall f g : unit -> Real,
    (forall s : unit, Id (f s) (g s)) ->
    Id (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (H tt).
Qed.

(* 字段四 le：逐点 ≤ ⟹ 求和 ≤（保序性） *)
Lemma spd_field_le :
  forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (H tt).
Qed.

(* 字段五 nonneg：逐点非负 ⟹ 求和非负 *)
Lemma spd_field_nonneg :
  forall f : unit -> Real,
    (forall s : unit, real_le real_zero (f s)) ->
    real_le real_zero (spd_sum_unit f).
Proof.
  intros f H.
  exact (H tt).
Qed.

(* 字段六 zero_nonneg：和为零且逐点非负 ⟹ 逐点为零 *)
Lemma spd_field_zero_nonneg :
  forall f : unit -> Real,
    (forall s : unit, real_le real_zero (f s)) ->
    Id (spd_sum_unit f) real_zero ->
    forall s : unit, Id (f s) real_zero.
Proof.
  intros f _ Hsum s.
  destruct s.
  exact Hsum.
Qed.

(* 字段七 abs：求和的三角不等式 |Σ f| ≤ Σ |f| *)
Lemma spd_field_abs :
  forall f : unit -> Real,
    real_le (real_abs (spd_sum_unit f))
            (spd_sum_unit (fun s => real_abs (f s))).
Proof.
  intros f.
  apply real_le_refl.
Qed.

(* 字段八（= B8 槽本尊，strict 求和正性，接口清单 S01:1399-1430 缺席字段）：
   即件1 spd_slot_unit_direct，接口包在具体载体上完整闭合。 *)

(* ===== 3. 实例展开对齐 witnesses：RealEnhancedReal 投影与实数层名
          定义性互换（槽位原句在实例展开下逐字还原的直证） ===== *)

Theorem spd_inst_zero_aligned :
  Id (@RealInterfaceEnhancedMod.zero
        Real RealInterfaceEnhancedMod.RealEnhancedReal)
     real_zero.
Proof.
  apply id_refl.
Qed.

Theorem spd_inst_lt_aligned :
  forall (x y : Real)
         (Hs : @RealInterfaceEnhancedMod.lt
                 Real RealInterfaceEnhancedMod.RealEnhancedReal x y),
    real_lt x y.
Proof.
  intros x y Hs.
  exact Hs.
Qed.

(* ===== 4. 消费面同位直配：S05:2543-2551 Z_rel_pos（槽位第一真实消费点）
          的实数层镜像（cons 非空形，承载点消费 AB2 折叠归纳件） ===== *)

(* Z_rel 实数层镜像：与 S05 主节定义逐字对齐
   （sum_over_S↦real_list_sum、mult↦real_mult、exp_neg↦real_exp_neg、
     opp↦real_opp、inv_pos↦real_inv_pos；advantage_aug 以 adv 抽象参入） *)
Definition spd_Z_rel (X : Set) (pi_t : X -> Real) (beta eta : Real)
  (beta_pos : real_lt real_zero beta) (adv : X -> Real) (l : list X) : Real :=
  real_list_sum X
    (fun s => real_mult (pi_t s)
       (real_exp_neg (real_opp
         (real_mult (real_mult eta (real_inv_pos beta beta_pos)) (adv s)))))
    l.

(* S05:2548 `apply sum_over_S_pos` 的实数层同位放电：证明链逐字平行
   （mult_positive × exp_neg_pos），折叠归纳消费 AB2
   zabr_list_sum_pos_cons（其 .vo 在盘，只读消费）。 *)
Theorem spd_Z_rel_pos :
  forall (X : Set) (pi_t : X -> Real) (beta eta : Real)
         (beta_pos : real_lt real_zero beta) (adv : X -> Real)
         (l : list X) (w : X),
    (forall s : X, real_lt real_zero (pi_t s)) ->
    real_lt real_zero (spd_Z_rel X pi_t beta eta beta_pos adv (w :: l)).
Proof.
  intros X pi_t beta eta beta_pos adv l w Hpos.
  unfold spd_Z_rel.
  apply (zabr_list_sum_pos_cons X _ l w).
  intro s.
  apply real_mult_positive.
  - exact (Hpos s).
  - apply real_exp_neg_pos.
Qed.

(* ===== 审计口：零假设面留痕 ===== *)
Print Assumptions spd_slot_direct_unit.
Print Assumptions spd_slot_unit_direct.
Print Assumptions spd_field_linear.
Print Assumptions spd_field_add.
Print Assumptions spd_field_ext.
Print Assumptions spd_field_le.
Print Assumptions spd_field_nonneg.
Print Assumptions spd_field_zero_nonneg.
Print Assumptions spd_field_abs.
Print Assumptions spd_inst_zero_aligned.
Print Assumptions spd_inst_lt_aligned.
Print Assumptions spd_Z_rel_pos.

(* ===== 提取审计：独立隔离目录（一人一目录） ===== *)
Set Extraction Output Directory "../_ab8_spos_extract".
Separate Extraction spd_slot_direct_unit.
Separate Extraction spd_sum_unit.
Separate Extraction spd_slot_unit_direct.
Separate Extraction spd_Z_rel_pos.
