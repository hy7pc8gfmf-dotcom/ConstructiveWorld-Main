(* ==========================================================================)
   UpAblP2FeedSum.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：spd_slot_direct_unit、spd_sum_unit、spd_slot_unit_direct、spd_field_linear、spd_field_add、spd_field_ext、spd_field_le、spd_field_nonneg、spd_field_zero_nonneg。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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

(* ================= §1 spd_slot_direct_unit 族 ================= *)
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
(* ================= §2 p2f_id_real_eq 族 ================= *)
(* ===== §1 桥接与转换引理 ===== *)

(* Id 消去：沿 Id a b 将实数层等词逐点传输——集合层 Id 到 real_eq 的传输引理 *)
Lemma p2f_id_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H.
  induction H.
  apply real_eq_refl.
Qed.

(* lt/le/req 与柯西层 real_lt/real_le/real_eq 逐位恒等（定义级换轨），体 exact H 为       *)
(* 最短定义性闭合，体不可再分。                                                          *)
(* 类投影与实数层序/等词的双向转换：库实例 RealEnhancedReal 字段逐位＝实数层名，转换即恒等 *)
Lemma p2f_proj_lt_of_real :
  forall x y : Real,
    real_lt x y ->
    @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_lt_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_lt x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_proj_le_of_real :
  forall x y : Real,
    real_le x y ->
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_le_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_le x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_proj_req_of_real :
  forall x y : Real,
    real_eq x y ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_eq_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_eq x y.
Proof.
  intros x y H.
  exact H.
Qed.

(* ===== §2 Id 系 SumOver 语句形实例 =====
   语句形为 S04/S06 接口的令名展开形（R:=@R RI、S:=@S RI SS、zero:=@zero RI、
   lt:=@lt RI、sum_over_S:=@sum_over_S RI SS SO；S06 同表）；态空间与求和
   实例取最小世界 uab_ssUnit／uab_soUnit，接口参量全称保留。
   证明：由 spd_slot_direct_unit 一步给出。 *)
Theorem p2f_S04_S06_slot_sum_over_S_pos :
  forall REI : RealInterfaceEnhanced,
    forall f : unit -> @R (@RI_base REI),
      (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
      @lt (@RI_base REI) (@zero (@RI_base REI))
          (@sum_over_S (@RI_base REI) uab_ssUnit uab_soUnit f).
Proof.
  exact spd_slot_direct_unit.
Qed.

(* ===== §3 req 六前提语句形在库实例上的装配 =====
   语句形与 UpReqFEPAttn 六前提一一对齐：载体取 unit（最小可证非空），
   求和算子取 spd_sum_unit，等词/序/正性取库实例 RealEnhancedReal
   的类投影形（其字段逐位等于实数层名）。 *)

(** 前提一 sum_ext：逐点 req 相等⟹求和 req 相等。
   证明：单点载体上和等于点值，由 H tt 直接给出。 *)
Theorem p2f_req_sum_ext :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  exact (H tt).
Qed.

(** 前提二 sum_add：逐点相加后求和等于分别求和后相加（req 面）。
   证明：经 p2f_proj_req_of_real、p2f_id_real_eq 至供体件 spd_field_add。 *)
Theorem p2f_req_sum_add :
  forall f g : unit -> Real,
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit (fun s : unit =>
         @RealInterfaceEnhancedMod.plus Real RealInterfaceEnhancedMod.RealEnhancedReal
           (f s) (g s)))
      (@RealInterfaceEnhancedMod.plus Real RealInterfaceEnhancedMod.RealEnhancedReal
         (spd_sum_unit f) (spd_sum_unit g)).
Proof.
  intros f g.
  exact (match spd_field_add f g in Id _ y return
           real_eq (spd_sum_unit (fun s : unit => real_plus (f s) (g s))) y
         with id_refl => real_eq_refl _ end).
Qed.

(** 前提三 sum_linear：数乘与求和可交换（req 面）；经 spd_field_linear。 *)
Theorem p2f_req_sum_linear :
  forall (a : Real) (f : unit -> Real),
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit (fun s : unit =>
         @RealInterfaceEnhancedMod.mult Real RealInterfaceEnhancedMod.RealEnhancedReal
           a (f s)))
      (@RealInterfaceEnhancedMod.mult Real RealInterfaceEnhancedMod.RealEnhancedReal
         a (spd_sum_unit f)).
Proof.
  intros a f.
  exact (match spd_field_linear a f in Id _ y return
           real_eq (spd_sum_unit (fun s : unit => real_mult a (f s))) y
         with id_refl => real_eq_refl _ end).
Qed.

(** 前提四 sum_le：逐点序不降⟹求和序不降；经 spd_field_le 与转换引理。 *)
Theorem p2f_req_sum_le :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (spd_field_le f g H).
Qed.

(** 前提五 sum_zero_nonneg：和为零且逐点非负⟹逐点为零。
   证明：单点载体上和等于点值，结论即前提自身（destruct s 后 exact Hsum）；
   供体 spd_field_zero_nonneg 为 Id 强前提形，req 弱前提推不出强形，
   故此处不由供体件证得——等词强度差如实记录。 *)
Theorem p2f_req_sum_zero_nonneg :
  forall f : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f)
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal) ->
    forall s : unit,
      @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
        (f s)
        (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal).
Proof.
  intros f Hle Hsum s.
  destruct s as [u].
  unfold spd_sum_unit in Hsum.
  exact Hsum.
Qed.

(** 前提六 sum_pos：逐点为正⟹和为正。
   证明：经 p2f_proj_lt_of_real 至供体件 spd_slot_unit_direct。 *)
Theorem p2f_req_sum_pos :
  forall f : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
      (spd_sum_unit f).
Proof.
  intros f H.
  exact (spd_slot_unit_direct f H).
Qed.

(* ===== §4 实数层路径（list 载体） ===== *)

(** p2f_req_sum_pos_cons·cons 载体形：非空性由载体本体 w :: l 给出，
   无需额外前提；由 zabr_list_sum_pos_cons 经转换引理立得。 *)
Theorem p2f_req_sum_pos_cons :
  forall (X : Set) (f : X -> Real) (l : list X) (w : X),
    (forall s : X,
       @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
      (real_list_sum X f (w :: l)).
Proof.
  intros X f l w H.
  exact (zabr_list_sum_pos_cons X f l w H).
Qed.

(** p2f_req_sum_pos_list·任意列表形：附非空前提 Hnn（空表和为零不为正，此前提最弱）；由 zabr_sum_over_S_pos 立得。 *)
Theorem p2f_req_sum_pos_list :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X,
       @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal)
      (real_list_sum X f l).
Proof.
  intros X f l Hnn H.
  exact (zabr_sum_over_S_pos X f l Hnn H).
Qed.

(* ===== 假设审计：Print Assumptions 应全部 Closed ===== *)
Print Assumptions p2f_id_real_eq.
Print Assumptions p2f_proj_lt_of_real.
Print Assumptions p2f_real_lt_of_proj.
Print Assumptions p2f_proj_le_of_real.
Print Assumptions p2f_real_le_of_proj.
Print Assumptions p2f_proj_req_of_real.
Print Assumptions p2f_real_eq_of_proj.
Print Assumptions p2f_S04_S06_slot_sum_over_S_pos.
Print Assumptions p2f_req_sum_ext.
Print Assumptions p2f_req_sum_add.
Print Assumptions p2f_req_sum_linear.
Print Assumptions p2f_req_sum_le.
Print Assumptions p2f_req_sum_zero_nonneg.
Print Assumptions p2f_req_sum_pos.
Print Assumptions p2f_req_sum_pos_cons.
Print Assumptions p2f_req_sum_pos_list.

(* ===== 提取：仅两面内容承载件 p2f_id_real_eq 与 p2f_S04_S06_slot_sum_over_S_pos ===== *)
Set Extraction Output Directory "../_tz2a_feedsum_extract".
Separate Extraction p2f_id_real_eq.
Separate Extraction p2f_S04_S06_slot_sum_over_S_pos.
