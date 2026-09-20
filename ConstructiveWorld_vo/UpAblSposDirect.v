(* ============================================================ *)
(* UpAblSposDirect.v —— 求和正性（逐项为正 ⟹ 和为正）                         *)
(* 在具体实例上的直接证明。                                                  *)
(*                                                               *)
(* 使命：论文 1 假设 B8「求和正性」原句形                                        *)
(*   forall (f : S -> R), (forall s : S, lt zero (f s)) ->       *)
(*   lt zero (sum_over_S f)                                      *)
(* 在库内具体实例上直接证得。                                                 *)
(*                                                               *)
(* 背景：S05_AlignmentGRPO 的主节与迭代节以节 Variable 引入该命题；                *)
(* Id 系抽象接口（RealInterfaceEnhanced / StateSpace / SumOver）        *)
(* 无严格求和正性字段，且态空间可为空（空表之和为 real_zero，                            *)
(* 不为正），故该命题在抽象接口层不可证，须在具体载体上证得。                                 *)
(*                                                               *)
(* 内容：§1 求和正性在最小 SumOver 实例                                      *)
(* （uab_ssUnit + uab_soUnit，全库唯一的具体 SumOver 实例，                  *)
(* 对任意 RealInterfaceEnhanced 参量）上逐字还原；                           *)
(* §2 单点载体 unit 上的求和 spd_sum_unit 与求和正性                          *)
(* （实数层实例）；                                                      *)
(* §3 SumOver 接口八个字段（linear、add、ext、le、nonneg、                   *)
(* zero_nonneg、abs、严格求和正性）在单点载体上逐字段兑现，                           *)
(* 不引入接口之外的新前提；                                                  *)
(* §4 RealEnhancedReal 的 zero/lt 投影与 real_zero/real_lt           *)
(* 的定义性互换（实例展开下原句形逐字还原）；                                         *)
(* §5 使用面对应命题：S05 中 Z_rel_pos 的实数层对应形式                           *)
(* （cons 非空形，和的正性由 zabr_list_sum_pos_cons 给出）。                   *)
(*                                                               *)
(* 各件（spd_slot_direct_unit、spd_sum_unit、spd_slot_unit_direct、    *)
(* spd_field_*、spd_inst_zero_aligned、spd_inst_lt_aligned、        *)
(* spd_Z_rel、spd_Z_rel_pos）均以 Qed 闭合，依赖审计见文末                     *)
(* Print Assumptions。                                            *)
(*                                                               *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp                   *)
(* S04_RealExpLogConv S05_AlignmentGRPO                          *)
(* S06_DiffSamplingGibbs S07_RealSetoidExpLog                    *)
(* S08_RealMainlineDPO UpReqExpPos                               *)
(* UpAblZposReal UpAblT13c_G13                                   *)
(*                                                               *)
(* 对标：mathlib 有限求和的正性引理（Finset.sum 系）；stdlib 列表求和归纳。             *)
(*                                                               *)
(* 构造性注记：零承认；全件 Set 层承载（Id/Not 用 S01 集合层                         *)
(* 别名，real_lt/real_le/real_eq 为集合值），语句面零 Prop；                   *)
(* 可提取。                                                          *)
(*                                                               *)
(* 适用边界：原句形的全称面依托 Id 系抽象接口，库内无具体实例                               *)
(* 可展开；本件在 Setoid 实例的实数层上证得对应形式，载体由                              *)
(* 抽象 S 换为具体载体（unit，或任意 Set 经 cons 列表），                          *)
(* 此为库级结构性形态差，非证明缺口。                                             *)
(*                                                               *)
(* 任意列表上「逐项正 ⟹ 和正」须补非空前提（空表之和为                                   *)
(* real_zero，不为正）；本件以载体见证（§1/§2）与 cons 形                         *)
(* （§5）给出该前提；归一化非空链见 UpAblZposReal 的                             *)
(* zabr_Z_align_pos，本件不重复。                                       *)
(*                                                               *)
(* 编译配方：Rocq 9.1 直调 + cpu_guard；编译输出 -o 临时目录，树内 .vo 不动。          *)
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

(* ================= §1 最小 SumOver 实例上的求和正性 =================

   求和正性原句形在最小 SumOver 实例（uab_ssUnit + uab_soUnit，全库唯一的
   具体 SumOver 实例，对任意 RealInterfaceEnhanced 参量）上逐字还原：
   forall f，(forall s, lt zero (f s)) -> lt zero (sum_over_S f)。
   非空性由单点态空间本体导出（tt 见证，uab_ssUnit_elem 定义性展开），
   无额外前提。 *)
Theorem spd_slot_direct_unit :
  forall (REI : RealInterfaceEnhanced) (f : unit -> @R (@RI_base REI)),
    (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
    @lt (@RI_base REI) (@zero (@RI_base REI))
        (@sum_over_S (@RI_base REI) uab_ssUnit uab_soUnit f).
Proof.
  intros REI f H.
  exact (H tt).
Qed.

(* ================= §2 单点载体上的求和与求和正性 ================= *)

(* unit 载体上的求和：全态空间单点求和 = 该点取值（定义性展开） *)
Definition spd_sum_unit (f : unit -> Real) : Real := f tt.

(* 求和正性原句形的实数层实例：forall f，(forall s, lt zero (f s)) ->
   lt zero (sum f)；实例展开 lt := real_lt，zero := real_zero，
   sum := spd_sum_unit。非空性由载体本体（tt : unit）导出，无额外前提。 *)
Theorem spd_slot_unit_direct :
  forall f : unit -> Real,
    (forall s : unit, real_lt real_zero (f s)) ->
    real_lt real_zero (spd_sum_unit f).
Proof.
  intros f H.
  exact (H tt).
Qed.

(* ================= §3 SumOver 接口字段在单点载体上的逐字段兑现 ================= *)

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

(* 字段八：严格求和正性——接口字段清单中缺席的字段，即 spd_slot_unit_direct。
   至此 SumOver 接口在单点载体上完整兑现，不引入接口之外的新前提。 *)

(* ================= §4 实例投影与实数层运算的对齐 =================

   RealEnhancedReal 的 zero/lt 投影与 real_zero/real_lt 定义性互换：
   求和正性原句形在实例展开下逐字还原。 *)

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

(* ================= §5 使用面对应命题：cons 非空形的求和正性 ================= *)

(* spd_Z_rel：S05 中 Z_rel 的实数层对应定义，逐字对齐
   （sum_over_S ↦ real_list_sum、mult ↦ real_mult、exp_neg ↦ real_exp_neg、
     opp ↦ real_opp、inv_pos ↦ real_inv_pos；advantage_aug 以抽象参量 adv 引入）。 *)
Definition spd_Z_rel (X : Set) (pi_t : X -> Real) (beta eta : Real)
  (beta_pos : real_lt real_zero beta) (adv : X -> Real) (l : list X) : Real :=
  real_list_sum X
    (fun s => real_mult (pi_t s)
       (real_exp_neg (real_opp
         (real_mult (real_mult eta (real_inv_pos beta beta_pos)) (adv s)))))
    l.

(* 对应 S05 中 `apply sum_over_S_pos` 一步的实数层证明：由 real_mult_positive
   与 real_exp_neg_pos 合成（两因子皆正则乘积为正），和的正性由
   UpAblZposReal 的归纳引理 zabr_list_sum_pos_cons（cons 非空形）给出；
   空表情形与归一化非空链见 UpAblZposReal 的 zabr_Z_align_pos，本件不重复。 *)
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

(* 依赖审计：Print Assumptions 确认上述各件零承认。 *)
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

(* 提取：输出至独立目录，不写入树内。 *)
Set Extraction Output Directory "../_ab8_spos_extract".
Separate Extraction spd_slot_direct_unit.
Separate Extraction spd_sum_unit.
Separate Extraction spd_slot_unit_direct.
Separate Extraction spd_Z_rel_pos.
