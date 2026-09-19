(* ============================================================ *)
(* UpAblP2FeedSum.v —— 论文2 求和面供体直配对接声明件（Z2a 席）        *)
(*                                                                    *)
(* 使命（P2B 基准报告交集行 11「求和面」＋其⑤-5 直配清单前半）：          *)
(*   把论文1 收官供体——AB8 槽位原句直配件 spd_ 系（UpAblSposDirect）     *)
(*   与 AB2 实数层等价形 zabr 系（UpAblZposReal）——对接论文2 求和面     *)
(*   三处槽位（坐标均为现盘实测）：                                    *)
(*   槽甲 S04_RealExpLogConv.v:3339 sum_over_S_pos（Section 自由能      *)
(*       最小化节，接口三件套上下文，令名展开后＝Id 系 SumOver 抽象面）； *)
(*   槽乙 S06_DiffSamplingGibbs.v:3216 sum_pos_preserved（Section 注意  *)
(*       力吉布斯桥节，与槽甲展开同形，逐字同一语句面）；                *)
(*   槽丙 UpReqFEPAttn.v:76-106 req 求和六前件面（Section ReqFEPAttn，   *)
(*       类上下文 R＋实数集oid增强接口，sum_pos 槽在 :90；六前件＝       *)
(*       sum_ext/add/linear/le/zero_nonneg/pos）。                     *)
(* 供体侧（各自 .vo 均在盘，只读消费，零改动零重述）：                    *)
(*   spd_slot_direct_unit（Id 系槽位原句形，在 T13c 最小 SumOver 实例    *)
(*       世界 uab_ssUnit＋uab_soUnit 上无条件直放电）；                  *)
(*   spd_sum_unit＋spd_slot_unit_direct（unit 载体实数层直配）；         *)
(*   spd_field_ext/add/linear/le/zero_nonneg（接口包字段实数层兑现）；   *)
(*   spd_inst_lt_aligned（实例投影对齐见证）；                          *)
(*   zabr_list_sum_pos_cons／zabr_sum_over_S_pos（实数层 list 载体      *)
(*       正性求和：cons 载体无条件形／任意列表非空前提最弱补全形）。      *)
(* 对接定理三面：                                                      *)
(*   面一（槽甲/槽乙共形）：p2f_S04_S06_slot_sum_over_S_pos——槽位原句    *)
(*       形在最小实例世界上对任意接口参量直放电；                       *)
(*   面二（槽丙六前件）：p2f_req_sum_ext/add/linear/le/zero_nonneg/pos   *)
(*       ——req 类投影形逐字，装配在库实例 RealEnhancedReal（S07:8566，   *)
(*       字段逐位＝实数层名）的 unit 载体 spd_sum_unit 上全闭合；        *)
(*   面三（实数层路径）：p2f_req_sum_pos_cons（cons 载体无条件形）＋      *)
(*       p2f_req_sum_pos_list（任意列表非空前提最弱补全形）。            *)
(* 桥接适配层（实质转换内容）：                                        *)
(*   p2f_id_real_eq——集合层 Id 到实数层等词的传输桥（AB2 主件匹配式      *)
(*       同款）；p2f_proj_lt_of_real／p2f_real_lt_of_proj／             *)
(*       p2f_proj_le_of_real／p2f_real_le_of_proj／                     *)
(*       p2f_proj_req_of_real／p2f_real_eq_of_proj——类投影与实数层名     *)
(*       的双向转换见证（补齐供体仅有的单侧 lt 对齐件）。               *)
(* 形态差申报（诚实边界，照 AB2/AB8 先例）：                            *)
(*   甲. 槽甲/乙的抽象全称面（任意态空间）不可无条件放电——态空间可空      *)
(*       是库级结构必然（AB8 定谳一）；本件直配面为最小可证非空实例世界，  *)
(*       语句面保留槽位原句逐字形。                                   *)
(*   乙. 槽丙在库实例装配于 unit/list 具体载体——抽象 sumf 全称面同为      *)
(*       打包结构（库级形态差，非证明缺口）。                          *)
(*   丙. 面三任意列表形增薄非空前提——实数层空表和归零不为正（AB2 定谳     *)
(*       最弱补全）；cons 载体形零增薄。                               *)
(*   丁. p2f_req_sum_ext 系单点载体本体直证（和＝点值，逐点外延即求和     *)
(*       外延），供体强形（Id 前件 spd_field_ext）并列在库，如实定性；    *)
(*   戊. p2f_S04_S06_slot_sum_over_S_pos 系供体旗舰逐字直喂（适配消费级，  *)
(*       零新增证明内容，如实定性）。                                  *)
(*   己. p2f_req_sum_zero_nonneg 同为载体本体直证——槽丙前件面系 req 等词   *)
(*       弱形，供体 spd_field_zero_nonneg 系 Id 强前件形，弱前件不可反向   *)
(*       喂入强形（等词强度差），供体在该槽不可消费，如实记录。          *)
(*   庚. 提取审计口径：入选提取集＝两面内容承载件（面一旗舰＋传输桥）。    *)
(*       其余面不入选，两类伪影如实登记——(1)投影桥三条系提取器对定义性    *)
(*       互换类型别名插入的搬运记号（实测 2 处，非承认）；(2)面二/面三闭包  *)
(*       必然物化库自带实例记录字面量（S07 实例侧 71 处既有库级伪影，非    *)
(*       本件引入）；语句面完备性由零假设留痕（全 Closed）与全量核验       *)
(*       （无承认项）承担。                                             *)
(* 零承认件；纯构造性；全件集合层面；语句面零命题泄露；头注与注释全      *)
(* 中文表述。                                                        *)
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

(* ===== 0. 桥接适配层 ===== *)

(* (甲) 集合层 Id 到实数层等词传输桥（AB2 主件匹配式同款） *)
Lemma p2f_id_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H.
  exact (match H in Id _ y return real_eq a y with id_refl => real_eq_refl a end).
Qed.

(* (乙) 类投影与实数层名双向转换见证（在库实例字段逐位＝实数层名） *)
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

(* ===== 面一：槽甲/槽乙（Id 系 SumOver 槽位原句形）直配 =====
   槽位令名展开逐字形（S04 令名表：R:=@R RI、S:=@S RI SS、zero:=@zero RI、
   lt:=@lt RI、sum_over_S:=@sum_over_S RI SS SO；S06 同表），态空间/求和
   实例装配 T13c 最小世界（uab_ssUnit/uab_soUnit），接口参量全称保留。
   定性：供体旗舰 spd_slot_direct_unit 逐字直喂（适配消费级，形态差申报戊）。 *)
Theorem p2f_S04_S06_slot_sum_over_S_pos :
  forall REI : RealInterfaceEnhanced,
    forall f : unit -> @R (@RI_base REI),
      (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
      @lt (@RI_base REI) (@zero (@RI_base REI))
          (@sum_over_S (@RI_base REI) uab_ssUnit uab_soUnit f).
Proof.
  exact spd_slot_direct_unit.
Qed.

(* ===== 面二：槽丙（req 求和六前件面）在库实例装配直配 =====
   语句形与 UpReqFEPAttn.v:76-106 六前件逐字对齐：载体 S:=unit（最小可证
   非空），sumf:=spd_sum_unit（供体载体），等词/序/正性取在库实例
   RealEnhancedReal 的类投影形（其字段逐位＝实数层名）。 *)

(* 前件一 sum_ext（:76）：逐点等词⟹求和等词。
   定性：单点载体本体直证（和＝点值）；供体强形（Id 前件）并列，见形态差丁。 *)
Theorem p2f_req_sum_ext :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (H tt).
Qed.

(* 前件二 sum_add（:78）：求和加法分配（等词面）。桥接：投影等词←实数层等词←
   集合层 Id←供体字段件。 *)
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
  apply p2f_proj_req_of_real.
  exact (p2f_id_real_eq _ _ (spd_field_add f g)).
Qed.

(* 前件三 sum_linear（:81）：数乘分配（等词面）。 *)
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
  apply p2f_proj_req_of_real.
  exact (p2f_id_real_eq _ _ (spd_field_linear a f)).
Qed.

(* 前件四 sum_le（:84）：逐点序⟹求和序。 *)
Theorem p2f_req_sum_le :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (p2f_proj_le_of_real _ _
    (spd_field_le f g (fun s => p2f_real_le_of_proj _ _ (H s)))).
Qed.

(* 前件五 sum_zero_nonneg（:86）：和为零且逐点非负⟹逐点为零。
   定性：单点载体本体直证（和＝点值，结论即前件自身）；供体强形
   spd_field_zero_nonneg 系 Id 前件面，req 弱前件不可反向喂入（等词强度
   差，形态差申报己），如实记录。 *)
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
  destruct s.
  exact Hsum.
Qed.

(* 前件六 sum_pos（:90，槽丙本尊）：逐点正⟹和正。
   桥接：投影正←实数层正←供体直配主件 spd_slot_unit_direct。 *)
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
  exact (p2f_proj_lt_of_real _ _
    (spd_slot_unit_direct f (fun s => p2f_real_lt_of_proj _ _ (H s)))).
Qed.

(* ===== 面三：实数层路径（list 载体）直配 ===== *)

(* cons 载体无条件形：零增薄（非空性由载体本体 w::l 导出）。
   承载点消费供体 zabr_list_sum_pos_cons。 *)
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
  exact (p2f_proj_lt_of_real _ _
    (zabr_list_sum_pos_cons X f l w (fun s => p2f_real_lt_of_proj _ _ (H s)))).
Qed.

(* 任意列表形：非空前提最弱补全（AB2 定谳，形态差申报丙）。 *)
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
  exact (p2f_proj_lt_of_real _ _
    (zabr_sum_over_S_pos X f l Hnn (fun s => p2f_real_lt_of_proj _ _ (H s)))).
Qed.

(* ===== 审计口：零假设面留痕 ===== *)
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

(* ===== 提取审计：独立隔离目录（一人一目录，伪影登记见头注庚） ===== *)
Set Extraction Output Directory "../_tz2a_feedsum_extract".
Separate Extraction p2f_id_real_eq.
Separate Extraction p2f_S04_S06_slot_sum_over_S_pos.
