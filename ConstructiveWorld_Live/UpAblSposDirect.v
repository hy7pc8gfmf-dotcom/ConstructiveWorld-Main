(* ==========================================================================)
   UpAblSposDirect.v — 严格求和正性的逐字段直供件
   使命: spd_slot_direct_unit/spd_slot_unit_direct（严格求和正性槽的直接供给）、spd_field_ 线性/加法/外延/序/非负/绝对值七字段直推与 spd_inst_zero/lt_aligned、spd_Z_rel_pos。
   依赖: S01_BaseRing 至 S08_RealMainlineDPO、UpReqExpPos、UpAblZposReal 及 UpAbl 系 Z 正性伴件；Stdlib Extraction。
   对标: 求和算子正性字段的直接实例供给（接口字段完备性层）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)
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
  pose proof (H (uab_ssUnit_elem (RI := @RI_base REI))) as Hw.
  exact Hw.
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
  unfold spd_sum_unit.
  pose proof (H tt) as Hs.
  exact Hs.
Qed.

(* ================= §3 SumOver 接口字段在单点载体上的逐字段兑现 ================= *)

(* 字段一 linear：数乘分配 *)
Lemma spd_field_linear :
  forall (a : Real) (f : unit -> Real),
    Id (spd_sum_unit (fun s => real_mult a (f s)))
       (real_mult a (spd_sum_unit f)).
Proof.
  intros a f.
  unfold spd_sum_unit.
  exact (id_cong (fun x => real_mult a x) (@id_refl _ (f tt))).
Qed.

(* 字段二 add：和的加法分配 *)
Lemma spd_field_add :
  forall f g : unit -> Real,
    Id (spd_sum_unit (fun s => real_plus (f s) (g s)))
       (real_plus (spd_sum_unit f) (spd_sum_unit g)).
Proof.
  intros f g.
  unfold spd_sum_unit.
  apply (id_trans
           (id_cong (fun x => real_plus x (g tt)) (@id_refl _ (f tt)))
           (id_cong (fun y => real_plus (f tt) y) (@id_refl _ (g tt)))).
Qed.

(* 字段三 ext：逐点 Id 相等 ⟹ 求和 Id 相等（函数 Proper 性） *)
Lemma spd_field_ext :
  forall f g : unit -> Real,
    (forall s : unit, Id (f s) (g s)) ->
    Id (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  pose proof (H tt) as Htt.
  exact Htt.
Qed.

(* 字段四 le：逐点 ≤ ⟹ 求和 ≤（保序性） *)
Lemma spd_field_le :
  forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  pose proof (H tt) as Hle.
  exact Hle.
Qed.

(* 字段五 nonneg：逐点非负 ⟹ 求和非负 *)
Lemma spd_field_nonneg :
  forall f : unit -> Real,
    (forall s : unit, real_le real_zero (f s)) ->
    real_le real_zero (spd_sum_unit f).
Proof.
  intros f H.
  unfold spd_sum_unit.
  pose proof (H tt) as Hnn.
  exact Hnn.
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
  unfold spd_sum_unit.
  apply real_le_refl.
Qed.

(* 字段八：严格求和正性——接口字段清单中缺失的字段，即 spd_slot_unit_direct。
   至此 SumOver 接口在单点载体上完整兑现，不引入接口之外的新前提。 *)

(* ================= §4 实例投影与实数层运算的对齐 =================

   RealEnhancedReal 的 zero/lt 投影与 real_zero/real_lt 定义性互换：
   求和正性原句形在实例展开下逐字还原。 *)

Theorem spd_inst_zero_aligned :
  Id (@RealInterfaceEnhancedMod.zero
        Real RealInterfaceEnhancedMod.RealEnhancedReal)
     real_zero.
Proof.
  unfold RealInterfaceEnhancedMod.RealEnhancedReal.
  apply id_refl.
Qed.

Theorem spd_inst_lt_aligned :
  forall (x y : Real)
         (Hs : @RealInterfaceEnhancedMod.lt
                 Real RealInterfaceEnhancedMod.RealEnhancedReal x y),
    real_lt x y.
Proof.
  intros x y Hs.
  unfold RealInterfaceEnhancedMod.RealEnhancedReal in Hs.
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
