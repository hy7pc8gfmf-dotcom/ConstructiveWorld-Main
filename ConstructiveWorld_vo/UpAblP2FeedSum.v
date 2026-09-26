(* ============================================================ *)
(* UpAblP2FeedSum.v —— 论文2 消融件的求和正性供给件（实数层与接口层双路）：  *)
(*   以已证件 spd_ 系（UpAblSposDirect）与 zabr 系（UpAblZposReal）为       *)
(*   实参来源，为三处求和正性接口供给显式实例。全件分四组。                 *)
(*                                                                        *)
(* 依赖接口三处（均为已注册件中的既有语句形）：                             *)
(*   其一 S04_RealExpLogConv 的 sum_over_S_pos（Section 自由能最小化节，     *)
(*       接口三件套上下文；令名展开后为 Id 系 SumOver 抽象语句形）；         *)
(*   其二 S06_DiffSamplingGibbs 的 sum_pos_preserved（Section 注意力        *)
(*       吉布斯桥节，与其一展开后同形）；                                   *)
(*   其三 UpReqFEPAttn 的 req 求和六前提语句形（Section ReqFEPAttn：         *)
(*       sum_ext/sum_add/sum_linear/sum_le/sum_zero_nonneg/sum_pos）。       *)
(*                                                                        *)
(* 一、桥接适配层（本件实质转换内容）：                                     *)
(*   p2f_id_real_eq——集合层 Id 到实数层等词 real_eq 的传输引理；            *)
(*   p2f_proj_lt_of_real／p2f_real_lt_of_proj／p2f_proj_le_of_real／        *)
(*   p2f_real_le_of_proj／p2f_proj_req_of_real／p2f_real_eq_of_proj——       *)
(*   库实例 RealEnhancedReal 类投影与实数层序/等词的双向转换见证             *)
(*   （该实例字段逐位等于实数层名，转换即恒等）。                            *)
(*                                                                        *)
(* 二、Id 系 SumOver 语句形实例 p2f_S04_S06_slot_sum_over_S_pos：在         *)
(*   T13c 最小世界（uab_ssUnit／uab_soUnit）上实例化，态空间取 unit          *)
(*   （最小可证非空），接口参量全称保留。                                    *)
(*                                                                        *)
(* 三、req 六前提语句形在库实例上的装配：p2f_req_sum_ext／add／linear／      *)
(*   le／zero_nonneg／pos，求和算子取 spd_sum_unit（unit 载体）。            *)
(*                                                                        *)
(* 四、实数层 list 载体路径：p2f_req_sum_pos_cons（cons 载体，非空性         *)
(*   由载体本体导出）与 p2f_req_sum_pos_list（任意列表，附非空前提           *)
(*   Hnn：Not (Id l nil)——空表和为零不为正，此前提最弱）。                   *)
(*                                                                        *)
(* 【形态差与诚实边界】                                                     *)
(*   甲、其一/其二的抽象全称形（任意态空间）不可无条件成立：态空间可空        *)
(*       为库级结构必然；本件在最小可证非空世界（unit）上实例化。            *)
(*   乙、其三的抽象求和算子全称形在本件装配为 unit 具体载体——库级           *)
(*       形态差，非证明缺口。                                                *)
(*   丙、p2f_req_sum_ext 与 p2f_req_sum_zero_nonneg 在单点载体上本体         *)
(*       直证（和等于点值）；更强前提形的相应件并列在库，如实记录。          *)
(*   丁、p2f_req_sum_zero_nonneg 的前提为 req 弱等词形，spd_field_zero_nonneg *)
(*       为 Id 强等词形；弱前提推不出强形，该件在此不可用，                  *)
(*       结论改由载体本体直证。                                              *)
(*                                                                        *)
(* 【依赖】S01_BaseRing；S02_CauchyComplete；S03_QExp；                      *)
(*   S04_RealExpLogConv；S05_AlignmentGRPO；S06_DiffSamplingGibbs；          *)
(*   S07_RealSetoidExpLog；S08_RealMainlineDPO；UpAblZposReal；              *)
(*   UpAblT13c_G13（uab_ssUnit／uab_soUnit）；UpAblSposDirect（spd_ 系）。    *)
(*                                                                        *)
(* 【对标】无直接对应物；声明注释体例对齐 stdlib 可提取文档注释。            *)
(*                                                                        *)
(* 【构造性注记】零承认、纯构造性（零经典逻辑）；全件集合层承载，            *)
(*   语句面无命题层泄露；全 Qed 闭合；末段 Print Assumptions 审计            *)
(*   应全部 Closed；提取集仅两面内容承载件 p2f_id_real_eq 与                 *)
(*   p2f_S04_S06_slot_sum_over_S_pos；提取输出中投影桥处提取器插入的         *)
(*   记号与库实例记录字面量为机械产物，非承认项，完备性以假设审计承担。      *)
(*                                                                        *)
(* 【编译配方】coqc 9.1 直调，cpu_guard 包裹（-LoadLimit 85 -CoreN 2），      *)
(*   编译输出经 -o 写临时目录，树内 .vo 一律不动。                           *)
(*                                                                        *)
(*                                                                        *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpAblZposReal.
Require Import UpAblT13c_G13.
Require Import UpAblSposDirect.
From Stdlib Require Import Extraction.

(* ===== §1 桥接与转换引理 ===== *)

(* Id 消去：沿 Id a b 将实数层等词逐点传输——集合层 Id 到 real_eq 的传输引理 *)
Lemma p2f_id_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H.
  induction H.
  apply real_eq_refl.
Qed.

(* 【批量登记·甲】接口投影直通六件（本件至 p2f_real_eq_of_proj）：RealEnhancedReal 字段   *)
(* lt/le/req 与柯西层 real_lt/real_le/real_eq 逐位恒等（定义级换轨），体 exact H 为       *)
(* 最短定义性收口，体不可再分。                                                          *)
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
   实例取 T13c 最小世界 uab_ssUnit／uab_soUnit，接口参量全称保留。
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
