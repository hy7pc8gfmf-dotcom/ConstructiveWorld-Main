(* G 组：G12_ZPosFam — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpReqZPosD + UpReqZPosI + UpReqZPosI2 + UpReqZAuto + UpReqZPosFinal（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G12_ZPosFam 成员件：UpReqZPosD（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqZPosD.v —— 配分函数正性放电席 G3：Z_pos 族无条件化          *)
(*   消费 G1 钥匙 UpReqSumD（sumd_sum_pos 直供）+ 根 exp 正性引擎    *)
(*   CW219 增强接口字段 exp_neg_pos。                              *)
(*                                                                *)
(* 数学核：Z == sum_s exp_neg(beta·e_s) > 0 <-- 逐项 exp_neg_pos     *)
(*   + sumd_sum_pos（G1 主件 4，enum 非空前提 datum 形）。放电后     *)
(*   Z 不再是 Variable，而是 sumd_sumf 的 Definition；槽语句对       *)
(*   （Z_pos : lt zero Z，partition_condition : req Z (sumf ...)）   *)
(*   降为「enum 非空 datum + beta_pos」，严格弱前提诚实降级。        *)
(*                                                                *)
(* 分级（逐件）：保底 1：zposd_Z_pos（lt zero Z 放电形，本席锚）；    *)
(*   辅件 1：zposd_boltz_factor_pos（逐项 exp 腿）；主件 5：          *)
(*   zposd_Z_pos_of_partition（抽象 Z + partition_condition 槽的      *)
(*   通用放电键，lt_id_r 换轨沿 UpReqDist L2806 req_Z_temp_pos       *)
(*   同法）/ zposd_boltzmann_dist_pos（Id boltzmann_dist_pos         *)
(*   @16824 族；UpReqDist L1059 req_boltzmann_positive 与 L2249      *)
(*   req_boltzmann_dist_pos 的无条件形）/ zposd_Z_temp_pos（槽       *)
(*   Z_temp_spec@2800 放电 -> UpReqDist L2803 req_Z_temp_pos 的      *)
(*   无条件形）/ zposd_boltzmann_dist_temp_pos（UpReqDist L2847      *)
(*   reqd_boltzmann_dist_temp_pos 无条件形）/ zposd_partition        *)
(*   （partition_condition 槽（UpReqDist L1020/UpSigMigrate L41/     *)
(*   UpSigMigrate2 L112）的 E354 装法 Definition 件：Z 定义性即       *)
(*   sumd_sumf 有限和，槽降 req_refl 定义件）。                      *)
(*                                                                *)
(* 签名变化台账（诚实降级）：上游槽 Z_pos+partition_condition 双位    *)
(*   -> 本席单 datum 位 Not (enum = nil)（基座 Set 版 Not，与        *)
(*   UpReqSampling 签名变化 7 同形同阶，不放大主张）；boltzmann_dist  *)
(*   的 Z_pos 位换为 zposd_Z_pos Hne 供给。                          *)
(*                                                                *)
(* 阻塞裁决（兜底，普查 §G3 余量如实报）：                          *)
(*   1. 纯抽象 Z 无 spec 者（普查已归 N：rZ/rpartition_function_t/    *)
(*      Z_align_r/real_temp_factor；另 UpReqDist ReqSteadyState      *)
(*      L3079 Z 无 partition_condition）无放电路，本席不越权；        *)
(*   2. uab_* 槽（UpAuditBridge L56/L65、UpRealLeB2 L474）为 Id 系    *)
(*      real 载体（real_lt real_zero 形），非本席 req 接口层——       *)
(*      enum/接口载体不匹配，留 real 镜像席；                        *)
(*   3. 含 log 下游族（req_boltzmann_log_decomp /                    *)
(*      reqd_boltzmann_log_temp_decomp 等）前置 G5 log 基元，不在     *)
(*      本席首批直接消费面；                                        *)
(*   4. 抽象 sumf 槽形对接本席具体和须沿 E354 装法（sumf :=           *)
(*      sumd_sumf 喂参 + sumd_sum_eq_list 桥），本席零重写战术。      *)
(*                                                                *)
(* 红线：Set 层语句（lt/req 均 Set 值谓词；零 Prop 泄露）；纯项式     *)
(*   组装（exact 供给项，零 rewrite 战术）；零外部未证假设，尾部      *)
(*   Print Assumptions 新件全 Closed；既有文件零改；前缀 zposd_       *)
(*   全库防撞已核（grep 零命中）。                                   *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ZPosDischarge：配分函数正性实例（sumf := G1 sumd_sumf）  *)
(* ============================================================ *)
Section ZPosDischarge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable enum : list S.
Variable base_loss : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.

(* ============ 辅件 1：Boltzmann 因子逐项正性（exp 引擎换形腿） ===== *)
Lemma zposd_boltz_factor_pos : forall s : S,
  lt zero (exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).
Proof.
  intro s. exact (exp_neg_pos (mult (inv_pos beta beta_pos) (base_loss s))).
Qed.

(* 具体配分函数：放电后 Z 的 Definition 形（G1 sumd_sumf 实例） *)
Definition zposd_Z : R :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).

(* ============ 保底件 1：Z 正性放电形（槽语句 lt zero Z） ============ *)
Lemma zposd_Z_pos : Not (enum = nil) -> lt zero zposd_Z.
Proof.
  intro Hne.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))
           Hne zposd_boltz_factor_pos).
Qed.

(* ============ 主件 1：抽象 Z + partition_condition 槽通用放电键 ===== *)
(* 槽形：任给 Z 带规范条件 req Z (有限和)，Z 正性无条件直推。
   换轨腿 = lt_id_r（req 先 lt 后，UpReqDist L2806 同法）。 *)
Lemma zposd_Z_pos_of_partition : forall Z : R,
  req Z (sumd_sumf S enum
          (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))) ->
  Not (enum = nil) -> lt zero Z.
Proof.
  intros Z Hcond Hne.
  exact (lt_id_r zero
           (sumd_sumf S enum
              (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s))))
           Z
           (req_sym Z
              (sumd_sumf S enum
                 (fun s : S =>
                    exp_neg (mult (inv_pos beta beta_pos) (base_loss s))))
              Hcond)
           (zposd_Z_pos Hne)).
Qed.

(* ============ 主件 2：boltzmann_dist_pos 族（@16824）无条件形 ======= *)
(* 上游 boltzmann_dist 的 Z_pos 位换为 zposd_Z_pos Hne（签名台账）。 *)
Definition zposd_boltzmann_dist (Hne : Not (enum = nil)) (s : S) : R :=
  mult (inv_pos zposd_Z (zposd_Z_pos Hne))
       (exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).

Lemma zposd_boltzmann_dist_pos : forall (Hne : Not (enum = nil)) (s : S),
  lt zero (zposd_boltzmann_dist Hne s).
Proof.
  intros Hne s. unfold zposd_boltzmann_dist.
  exact (mult_positive (inv_pos zposd_Z (zposd_Z_pos Hne))
           (exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))
           (inv_pos_pos zposd_Z (zposd_Z_pos Hne))
           (zposd_boltz_factor_pos s)).
Qed.

(* ============ 主件 3：Z_temp 族（Z_temp_spec@2800 槽放电） ========== *)
(* 温度形：逐温 t，beta := inv_pos t Ht；Z_temp 定义性即有限和，
   槽 Z_temp_spec 的 req 方程降为定义性（zposd_partition 同判词）。 *)
Definition zposd_Z_temp (t : R) (Ht : lt zero t) : R :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s))).

Lemma zposd_Z_temp_pos : forall (t : R) (Ht : lt zero t),
  Not (enum = nil) -> lt zero (zposd_Z_temp t Ht).
Proof.
  intros t Ht Hne.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))
           Hne
           (fun s : S => exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Qed.

(* ============ 主件 4：boltzmann_dist_temp_pos 族（@2847）无条件形 ==== *)
Definition zposd_boltzmann_dist_temp (t : R) (Ht : lt zero t)
           (Hne : Not (enum = nil)) (s : S) : R :=
  mult (inv_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
       (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Lemma zposd_boltzmann_dist_temp_pos :
  forall (t : R) (Ht : lt zero t) (Hne : Not (enum = nil)) (s : S),
  lt zero (zposd_boltzmann_dist_temp t Ht Hne s).
Proof.
  intros t Ht Hne s. unfold zposd_boltzmann_dist_temp.
  exact (mult_positive (inv_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
           (exp_neg (mult (inv_pos t Ht) (base_loss s)))
           (inv_pos_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
           (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Qed.

(* ============ 主件 5：partition_condition 槽放电 Definition 件 ====== *)
(* E354 装法：Z 定义性即 sumd_sumf 有限和，槽语句降 req_refl 定义件
   （G1 sumd_sum_eq_list 同法；透明 Definition 供下游喂参直连）。 *)
Definition zposd_partition :
  req zposd_Z (sumd_sumf S enum
                 (fun s : S =>
                    exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))) :=
  req_refl (sumd_sumf S enum
             (fun s : S =>
                exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))).

End ZPosDischarge.

(* ============ G3 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions zposd_boltz_factor_pos.
Print Assumptions zposd_Z_pos.
Print Assumptions zposd_Z_pos_of_partition.
Print Assumptions zposd_boltzmann_dist_pos.
Print Assumptions zposd_Z_temp_pos.
Print Assumptions zposd_boltzmann_dist_temp_pos.
Print Assumptions zposd_partition.

(* ======== G12_ZPosFam 成员件：UpReqZPosI（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqZPosI.v —— G3 同形直装席：Z_pos 族无条件实例化放电件        *)
(*   消费席60 通用键 UpReqZPosD（zposd_Z_pos / zposd_partition /     *)
(*   zposd_Z_temp_pos），为三个同形面产出 T2 模板② 形态的具体实例：   *)
(*   槽被放电键填充，非空前提 Not (enum = nil) 显式携带（诚实降级）。 *)
(*                                                                *)
(* 三面对表（sed 实读勘误以现值为准）：                             *)
(*   面1 UpSigMigrate.v L40/41：Z_pos : lt zero Z +                *)
(*     partition_condition : req Z (sumf (fun s => exp_neg          *)
(*       (mult (inv_pos D D_pos) (base_loss s))))（sumf 抽象位，     *)
(*     温度参数名 D）；槽消费件 req_boltzmann_positive@L56。         *)
(*   面2 UpSigMigrate2.v L111/112：同形双槽（m2 系名）；槽消费件     *)
(*     req_boltzmann_positive@L352（positive_dist_m2 形）。         *)
(*   面3a UpReqTempEntropy.v L66：Z_temp_spec : forall t Ht,        *)
(*     req (Z_temp t) (sumf ...)；槽消费件 tZpos@L74（fsum_pos      *)
(*     无条件正性槽位）。                                           *)
(*   面3b UpFirewallReq.v L87：req_Z_temp_spec 同形；槽消费件        *)
(*     fw_bt_pos（ssum_pos 槽位，正性分布形）。                     *)
(*                                                                *)
(* 勘误（对表所出，以现值为准）：                                   *)
(*   1. 面内 sumf 均为抽象 Section Variable（sumd_sumf 喂参沿 E354   *)
(*      装法），面1/2 温度参数名 D 非 beta——实例件照面现值命名；     *)
(*   2. zposd_boltzmann_dist 喂参实为 curried 形 (S->R) -> forall    *)
(*      beta, lt zero beta -> Not (enum = nil) -> S -> R（探针       *)
(*      Check 实证），与 D 文件节内书写顺序无冲突；                 *)
(*   3. 面1/2 面常数 R/RIS 为非极大隐式位（Check 显示省略不等于可省  *)
(*      略应用），直装喂定一律 @ 全参形（平铺应用曾落 S : Set 位错）； *)
(*   4. 面3 Z_temp 槽位为 R -> R 形（不带 Ht），与席60 zposd_Z_temp   *)
(*      族 forall t, lt zero t -> R 类型失配（product vs R 编译实证）， *)
(*      直装沿面常数不可行——面3 实例件改沿 zposd_Z_temp_pos /        *)
(*      zposd_boltzmann_dist_temp_pos 直放电，签名台账记「Z_temp 位   *)
(*      Ht 化」诚实降级（不放大主张）。                              *)
(*                                                                *)
(* 直装法（T2 模板②）：面1/2 槽消费常数（req_boltzmann_positive 族）   *)
(*   @ 全喂定（E354 装法：Definition 槽名 : 槽语句 := @zposd_* …）；    *)
(*   面3 因勘误 4 改结论形直放电。全文件零重写战术、纯项式组装。      *)
(*                                                                *)
(* 分级：保底 = 面1 + 面2（各 4 件：E354 槽装配件 2 + 实例放电件 2）； *)
(*   主件 = + 面3 两文件（各 2 件：E354 槽装配件 1 + 实例放电件 1）。 *)
(*   共 11 件。三面原文件零改（双形并存，本席只交付实例件）。         *)
(*                                                                *)
(* 红线：Set 层语句（零 Prop 泄露）；纯项式组装（exact 供给项，零     *)
(*   rewrite 战术）；零外部未证假设，尾部 Print Assumptions 新件全   *)
(*   Closed；前缀 zpi_ 全库防撞已核（grep 零命中）。                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.

Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 面1 UpSigMigrate.v：Z_pos@L40 + partition_condition@L41 双槽实例  *)
(* ============================================================ *)

(* E354 装配件 1：partition_condition 槽放电（Z := zposd_Z，sumf :=
   sumd_sumf 喂参；zposd_partition 直供，定义性 req_refl 同判词）。 *)
Definition zpi1_partition_condition
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (D : R) (D_pos : lt zero D) :
  req (@zposd_Z R RIS S enum base_loss D D_pos)
      (@sumd_sumf R RIS S enum
         (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) :=
  @zposd_partition R RIS S enum base_loss D D_pos.

(* 实例放电件 1：Z_pos 槽实例形（非空前提显式携带）。 *)
Lemma zpi1_Z_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) :
  lt zero (@zposd_Z R RIS S enum base_loss D D_pos).
Proof.
  exact (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne).
Qed.

(* E354 装配件 2：sigm_boltzmann_dist@L46 实例形（Z_pos 位由放电键供给）。 *)
Definition zpi1_boltzmann_dist
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) : S -> R :=
  @zposd_boltzmann_dist R RIS S enum base_loss D D_pos Hne.

(* 实例放电件 2：req_boltzmann_positive@L56 直装形——面1 常数在放电
   槽位处的实例（T2 模板②），零重证、槽位一次喂定。 *)
Lemma zpi1_req_boltzmann_positive
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) :
  (@UpSigMigrate.sigm_positive_dist R RIS S
     (@UpSigMigrate.sigm_boltzmann_dist R RIS S base_loss D D_pos
        (@zposd_Z R RIS S enum base_loss D D_pos)
        (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne))).
Proof.
  exact (@UpSigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos
           (@zposd_Z R RIS S enum base_loss D D_pos)
           (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne)).
Qed.

(* ============================================================ *)
(* 面2 UpSigMigrate2.v：Z_pos@L111 + partition_condition@L112 双槽实例 *)
(*   （与面1 同形；m2 系名，槽消费件 req_boltzmann_positive@L352）。   *)
(* ============================================================ *)

(* E354 装配件 3：partition_condition 槽放电（面2 同形直装）。 *)
Definition zpi2_partition_condition
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (D : R) (D_pos : lt zero D) :
  req (@zposd_Z R RIS S enum base_loss D D_pos)
      (@sumd_sumf R RIS S enum
         (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) :=
  @zposd_partition R RIS S enum base_loss D D_pos.

(* 实例放电件 3：Z_pos 槽实例形（非空前提显式携带）。 *)
Lemma zpi2_Z_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) :
  lt zero (@zposd_Z R RIS S enum base_loss D D_pos).
Proof.
  exact (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne).
Qed.

(* E354 装配件 4：boltzmann_dist_m2@L128 实例形。 *)
Definition zpi2_boltzmann_dist_m2
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) : S -> R :=
  @zposd_boltzmann_dist R RIS S enum base_loss D D_pos Hne.

(* 实例放电件 4：req_boltzmann_positive@L352 直装形（m2 形）。 *)
Lemma zpi2_req_boltzmann_positive
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (D : R) (D_pos : lt zero D) (Hne : Not (enum = nil)) :
  (@UpSigMigrate2.positive_dist_m2 R RIS S
     (@UpSigMigrate2.boltzmann_dist_m2 R RIS S base_loss D D_pos
        (@zposd_Z R RIS S enum base_loss D D_pos)
        (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne))).
Proof.
  exact (@UpSigMigrate2.req_boltzmann_positive R RIS S base_loss D D_pos
           (@zposd_Z R RIS S enum base_loss D D_pos)
           (@zposd_Z_pos R RIS S enum base_loss D D_pos Hne)).
Qed.

(* ============================================================ *)
(* 面3a UpReqTempEntropy.v：Z_temp_spec@L66 槽实例（tZpos@L74 直装）  *)
(* ============================================================ *)

(* E354 装配件 5：Z_temp_spec 槽放电——zposd_Z_temp t Ht 定义性即
   sumd_sumf 有限和，槽语句降 req_refl 定义件（zposd_partition 同法）。 *)
Definition zpi3_Z_temp_spec
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (t : R) (Ht : lt zero t) :
  req (@zposd_Z_temp R RIS S enum base_loss t Ht)
      (@sumd_sumf R RIS S enum
         (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))) :=
  req_refl (@sumd_sumf R RIS S enum
              (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* 实例放电件 5：tZpos@L74 结论实例形（Z_temp 位 Ht 化诚实降级——
   勘误：面3 槽位 Z_temp : R -> R 与席60 zposd_Z_temp 族
   forall t, lt zero t -> R 类型失配（product vs R，编译实证），
   直装沿面常数不可行；本件改沿席60 主件3 zposd_Z_temp_pos
   （= UpReqDist req_Z_temp_pos 的无条件形）直放电，签名台账记
   「Z_temp 位 Ht 化」，非空前提显式携带。 *)
Lemma zpi3_tZpos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (t : R) (Ht : lt zero t) (Hne : Not (enum = nil)) :
  lt zero (@zposd_Z_temp R RIS S enum base_loss t Ht).
Proof.
  exact (@zposd_Z_temp_pos R RIS S enum base_loss t Ht Hne).
Qed.

(* ============================================================ *)
(* 面3b UpFirewallReq.v：req_Z_temp_spec@L87 槽实例（fw_bt_pos 直装） *)
(* ============================================================ *)

(* E354 装配件 6：req_Z_temp_spec 槽放电（面3b 同形直装）。 *)
Definition zpi_fw_req_Z_temp_spec
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S) (base_loss : S -> R)
           (t : R) (Ht : lt zero t) :
  req (@zposd_Z_temp R RIS S enum base_loss t Ht)
      (@sumd_sumf R RIS S enum
         (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))) :=
  req_refl (@sumd_sumf R RIS S enum
              (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* 实例放电件 6：fw_bt_pos@L93 结论实例形（正性分布）——同面3a 勘误
   （Z_temp 槽 R -> R 形与席60 Ht 化族失配，直装沿面常数不可行），
   本件取其结论形在放电槽位的实例：fw_bt 的 zposd 同构 = 席60 主件4
   zposd_boltzmann_dist_temp，正性沿 zposd_boltzmann_dist_temp_pos
   直供，非空前提显式携带。 *)
Lemma zpi_fw_bt_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S) (base_loss : S -> R)
      (t : R) (Ht : lt zero t) (Hne : Not (enum = nil)) (s : S) :
  lt zero (@zposd_boltzmann_dist_temp R RIS S enum base_loss t Ht Hne s).
Proof.
  exact (@zposd_boltzmann_dist_temp_pos R RIS S enum base_loss t Ht Hne s).
Qed.

(* ============ G2 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions zpi1_partition_condition.
Print Assumptions zpi1_Z_pos.
Print Assumptions zpi1_boltzmann_dist.
Print Assumptions zpi1_req_boltzmann_positive.
Print Assumptions zpi2_partition_condition.
Print Assumptions zpi2_Z_pos.
Print Assumptions zpi2_boltzmann_dist_m2.
Print Assumptions zpi2_req_boltzmann_positive.
Print Assumptions zpi3_Z_temp_spec.
Print Assumptions zpi3_tZpos.
Print Assumptions zpi_fw_req_Z_temp_spec.
Print Assumptions zpi_fw_bt_pos.

(* ======== G12_ZPosFam 成员件：UpReqZPosI2（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqZPosI2.v —— G3 Definition-Z 面直装席：Z_pos 族余量逐槽实例化  *)
(*   消费席60 通用键 UpReqZPosD（zposd_Z_pos 主键）+ G1 钥匙          *)
(*   UpReqSumD（sumd_sum_pos 根引擎）+ CW219 exp/mult 正性引擎，      *)
(*   为普查 §G3 Definition-Z 余量面产出 T2 模板② 形态逐槽放电件：    *)
(*   槽类型在 E354 填位（sumf := sumd_sumf 喂参）的实例语句，非空     *)
(*   前提 Not (enum = nil) 显式携带（诚实降级）。                    *)
(*                                                                *)
(* 前缀台账：前缀 zpi2_ 在席64 UpReqZPosI.v 面2 已有 4 名             *)
(*   （zpi2_partition_condition / zpi2_Z_pos / zpi2_boltzmann_dist_m2 / *)
(*   zpi2_req_boltzmann_positive）；本席逐名 grep 全库零重名，文件名    *)
(*   UpReqZPosI2.v 与 UpReqZPosI.v 无冲突（双形并存，零既有文件改动）。 *)
(*                                                                *)
(* 逐槽清偿表（sed 实读行号；键填充/根引擎/阻塞三分级）：             *)
(*  保底 4：                                                      *)
(*   ① UpReqAlign.v:94   Z_align_pos : lt zero Z_align_req          *)
(*      （Z_align_req@92 := sumf 逐项 mult (pi_ref s) 乘 exp_neg     *)
(*      （opp 翻转指数）——见勘误 1）                               *)
(*   ② UpReqAlign2.v:104  Z_align_pos : lt zero req2_Z_align         *)
(*      （req2_Z_align@102 同形体）                                *)
(*   ③ UpReqAlignRestA.v:75 Z_align_pos : lt zero (Z_align_req …)    *)
(*   ④ UpReqDpoLoss.v:58  Z_align_pos : lt zero (Z_align_req …)      *)
(*  主件 11：                                                     *)
(*   ⑤ UpReqAlign3.v:114  ZAL_pos : lt zero ZAL（ZAL := req2_Z_align） *)
(*   ⑥ UpReqU2.v:343      ZAL_pos 同形                             *)
(*   ⑦ UpAlignIdReq.v:163 ZAL_pos 同形                             *)
(*   ⑧ UpReqPPOPlain.v:115 Zap : lt zero (Z_align_req S sumf …)      *)
(*   ⑨ UpReqPPO.v:95      Zap 同形（节载体名 Real，语句同型）        *)
(*   ⑩ UpSigMigrate.v:540 Z_thermo_pos : lt zero Z_thermo           *)
(*      （键填充：zposd_Z_pos 直供，base_loss := energy，β := D）    *)
(*   ⑪ G13_EvictFam.v:88  Z_thermo_pos 同形（键填充）               *)
(*   ⑫ UpReqAttnIter.v:129 Z_thermo_i_pos（键填充）                 *)
(*   ⑬ UpReqAttnGibbs.v:543 Z_thermo_r_pos（键填充）                *)
(*   ⑭ UpSigMigrate2.v:891 Z_align_a_pos : lt zero Z_align_a_sum     *)
(*   ⑮ UpSigMigrate.v:533 partition_function_temp_pos                *)
(*      （sigm_exp_pos_fn := exp_neg∘opp 换形，根引擎逐项 exp 正性）      *)
(*                                                                *)
(* 阻塞裁决（兜底，逐槽如实报；本席零越权）：                         *)
(*   B1 UpReqAlign.v:709 HZ : lt zero Z_aud_req——Z_aud_req :=        *)
(*      sumf (fun s => if post_aud s then p s else zero)：零腿分支和  *)
(*      （非 posting 态项为 zero），非全正项和；sumd_sum_pos 全正前提 *)
(*      在零腿不可满足，posting 非空信息缺失，阻塞归 N。             *)
(*   B2 G13_EvictFam.v:117 evicted_partition_pos——evq_evicted_partition  *)
(*      := sumf (fun s => if keep_dec s then boltzmann_factor s      *)
(*      else zero)：同零腿分支和（keep 分支），kept 非空信息缺失，    *)
(*      阻塞归 N。                                                  *)
(*   B3 UpReqAttnGibbs.v:697 evicted_partition_r_pos——同 B2 零腿形，  *)
(*      阻塞归 N。                                                  *)
(*   B4 UpReqAlignRestB.v:1755 req_evicted_partition_pos——求和载体为  *)
(*      sum_over_S 且节载体 S : Type（Check 实证），与 enum 列表键     *)
(*      载体不匹配 + 零腿 match keep_dec 分支，双重不适配，阻塞归 N。  *)
(*                                                                *)
(* 勘误（对表所出，以 sed/Check 现值为准）：                          *)
(*   1. 键形失配类：zposd 四键的指数形为 exp_neg (mult (inv_pos β β⁻¹) *)
(*      (base_loss s))；Align 族（①②③④⑤⑥⑦⑧⑨⑭）逐项实为          *)
(*      mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos)   *)
(*      (reward s))))——pi_ref 外乘 + 指数 opp 翻转，键形不可对接      *)
(*      （ convertible 实证否），改沿 G1 根引擎 sumd_sum_pos +         *)
(*      mult_positive/exp_neg_pos 纯项式直装（即席60 zposd_Z_pos      *)
(*      内部同链），台账记「键形失配→根引擎直装」，不放大主张；        *)
(*   2. ⑮ sigm_exp_pos_fn 为透明 Definition（exp_neg∘opp），delta 换形后    *)
(*      根引擎逐项 exp_neg_pos 直供，同上登记；                       *)
(*   3. ⑨ UpReqPPO 节载体绑定名 Real（语句与 R 实例同型，绑定名差异    *)
(*      不改语句）；                                                 *)
(*   4. 面常数 R/RIS 为非极大隐式位，直装喂定一律 @ 全参形（席64       *)
(*      勘误3 同法）；feed 形 sumf := @sumd_sumf R RIS S enum（部分    *)
(*      应用即 (S->R)->R 载体，E354 装法）。                          *)
(*                                                                *)
(* 红线：Set 层语句（lt/req 均 Set 值谓词，零泄露）；纯项式组装        *)
(*   （exact 供给项，零重写战术）；零外部未证假设，尾部 Print          *)
(*   Assumptions 新件全 Closed；既有文件零改；零 git。                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.

Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Require Import G13_EvictFam.
Require Import UpReqAttnIter.
Require Import UpReqAttnGibbs.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 保底 ①：UpReqAlign.v:94 槽实例（Z_align_req@92 E354 填位）        *)
(* ============================================================ *)
Lemma zpi2_align1_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ②：UpReqAlign2.v:104 槽实例（req2_Z_align@102 E354 填位）     *)
(* ============================================================ *)
Lemma zpi2_align2_req2_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ③：UpReqAlignRestA.v:75 槽实例（全局 Z_align_req E354 填位）  *)
(* ============================================================ *)
Lemma zpi2_resta_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ④：UpReqDpoLoss.v:58 槽实例（全局 Z_align_req E354 填位）     *)
(* ============================================================ *)
Lemma zpi2_dpo_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑤：UpReqAlign3.v:114 ZAL_pos 槽实例（ZAL := req2_Z_align）    *)
(* ============================================================ *)
Lemma zpi2_align3_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑥：UpReqU2.v:343 ZAL_pos 槽实例（同形）                      *)
(* ============================================================ *)
Lemma zpi2_u2_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑦：UpAlignIdReq.v:163 ZAL_pos 槽实例（同形）                  *)
(* ============================================================ *)
Lemma zpi2_alignidreq_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑧：UpReqPPOPlain.v:115 Zap 槽实例（全局 Z_align_req 填位）    *)
(* ============================================================ *)
Lemma zpi2_ppoplain_Zap
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑨：UpReqPPO.v:95 Zap 槽实例（节载体绑定名 Real，语句同型；    *)
(*         勘误 3）                                                  *)
(* ============================================================ *)
Lemma zpi2_ppo_Zap
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑩：UpSigMigrate.v:540 Z_thermo_pos 槽实例——键填充：           *)
(*   Z_thermo@539 := sumf boltzmann_factor，boltzmann_factor@536 :=   *)
(*   exp_neg (mult (inv_pos D D_pos) (energy s))，E354 填位后与        *)
(*   zposd_Z（base_loss := energy，β := D）定义性重合，zposd_Z_pos    *)
(*   一次喂定。                                                      *)
(* ============================================================ *)
Lemma zpi2_sigmig_Z_thermo_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate.sigm_Z_thermo R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑪：G13_EvictFam.v:88 Z_thermo_pos 槽实例（键填充，同⑩形）     *)
(* ============================================================ *)
Lemma zpi2_evict_Z_thermo_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@G13_EvictFam.evq_Z_thermo R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑫：UpReqAttnIter.v:129 Z_thermo_i_pos 槽实例（键填充）        *)
(* ============================================================ *)
Lemma zpi2_iter_Z_thermo_i_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAttnIter.Z_thermo_i R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑬：UpReqAttnGibbs.v:543 Z_thermo_r_pos 槽实例（键填充）       *)
(* ============================================================ *)
Lemma zpi2_gibbs_Z_thermo_r_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAttnGibbs.Z_thermo_r R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑭：UpSigMigrate2.v:891 Z_align_a_pos 槽实例                   *)
(*   （Z_align_a_sum@889 Align 同形体；勘误 1 根引擎直装）             *)
(* ============================================================ *)
Lemma zpi2_sigmig2_Z_align_a_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate2.Z_align_a_sum R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑮：UpSigMigrate.v:533 partition_function_temp_pos 槽实例      *)
(*   （sigm_partition_function_temp@531 := sumf (fun s => sigm_exp_pos_fn       *)
(*   (mult (inv_pos T T_pos) (z s)))，sigm_exp_pos_fn := exp_neg∘opp 透明   *)
(*   换形（勘误 2），根引擎逐项 exp 正性直供）                        *)
(* ============================================================ *)
Lemma zpi2_sigmig_partition_function_temp_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (T : R) (T_pos : lt zero T) (z : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate.sigm_partition_function_temp R RIS S
             (@sumd_sumf R RIS S enum) T T_pos z).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
           Hne
           (fun s : S =>
              @exp_neg_pos R RIS (opp (mult (inv_pos T T_pos) (z s))))).
Qed.

(* ============ 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions zpi2_align1_Z_align_pos.
Print Assumptions zpi2_align2_req2_Z_align_pos.
Print Assumptions zpi2_resta_Z_align_pos.
Print Assumptions zpi2_dpo_Z_align_pos.
Print Assumptions zpi2_align3_ZAL_pos.
Print Assumptions zpi2_u2_ZAL_pos.
Print Assumptions zpi2_alignidreq_ZAL_pos.
Print Assumptions zpi2_ppoplain_Zap.
Print Assumptions zpi2_ppo_Zap.
Print Assumptions zpi2_sigmig_Z_thermo_pos.
Print Assumptions zpi2_evict_Z_thermo_pos.
Print Assumptions zpi2_iter_Z_thermo_i_pos.
Print Assumptions zpi2_gibbs_Z_thermo_r_pos.
Print Assumptions zpi2_sigmig2_Z_align_a_pos.
Print Assumptions zpi2_sigmig_partition_function_temp_pos.

(* ======== G12_ZPosFam 成员件：UpReqZAuto（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqZAuto.v —— Z_auto 引理席：配分相等前提「Z == partition」     *)
(*   的定义性消去（评审08 §3.3.1 点名弱点清偿）。                  *)
(*                                                                *)
(* 目标：把「Z_thermo == partition_function」从配分函数定理的前提    *)
(*   降为可自动消去的引理（Z_auto）：两分布在                       *)
(*   「energy == -z 逐点 + inv D == 1/T」下由定义性相等直接可导，    *)
(*   无需把它单列为前提。                                          *)
(*                                                                *)
(* 原件定位（sed 实读）：                                          *)
(*   · 原件 1：CW219 attention_is_gibbs_setoid（L66294），前提形：    *)
(*       req (inv_pos D D_pos) one ->                              *)
(*       (forall s, req (energy s) (opp (z s))) ->                  *)
(*       req (Z_thermo_setoid …) (partition_function_setoid z) ->   *)
(*       forall s, req (softmax_setoid z s) (boltzmann_dist_attn … s) *)
(*   · 原件 2：CW220 SigMigrate.req_attention_is_gibbs_temp          *)
(*       （L1954），前提 3 = req Z_thermo cwe_partition_function_temp。  *)
(*   两处求和载体均无 req 外延可消费（原件 1 的 sum_req_over_S_ext    *)
(*   Variable 未被定理消费故出节即弃；原件 2 节内只有 sum_pos）——     *)
(*   「前提可消而未消」的机制根因。本席把外延引擎显式接入，           *)
(*   Z_auto 即成立。                                               *)
(*                                                                *)
(* 外延引擎（实测签名）：                                          *)
(*   · Id 形：CW219 SumOver 字段                                    *)
(*       sum_over_S_ext : forall f g, (forall s, Id (f s) (g s)) -> *)
(*         Id (sum_over_S f) (sum_over_S g)                         *)
(*   · req 形：本文件各 Z_auto 件以显式参数 sum_req_ext / sumf_req_ext *)
(*     接入（诚实接口：对任何具体求和载体构造性满足，非分布层假设）。 *)
(*                                                                *)
(* exp 关系（实测）：exp_pos 即 exp_neg ∘ opp——两处上游均为透明       *)
(*   Definition（CW220 SigMigrate.cwe_exp_pos_fn / CW219 exp_pos_fn_setoid）， *)
(*   delta 换形后逐点镜像件直接以 exp_neg 收口；exp 的 req 兼容由     *)
(*   CW219 已证件 exp_neg_req_compat_setoid（L66223）免费供给，        *)
(*   不再立新假设（CW220 原件 2 节内同形 Hypothesis 桥由此被证明件替代）。 *)
(*                                                                *)
(* 交付清单（8 件，双形并存）：                                     *)
(*  形 A（req 形·CW219 AttentionGibbsBridgeSetoid 载体，S : Type）：  *)
(*   A1 zauto_mirror_point_setoid      保底·逐点镜像件               *)
(*       （inv D == one + energy == -z 逐点                          *)
(*         ⟹ exp_neg(inv D·energy s) == exp_pos(z s) 逐点）          *)
(*   A2 zauto_Z_eq_setoid              主件·Z_auto 引理              *)
(*       （partition_function_setoid == Z_thermo_setoid）            *)
(*   A3 zauto_attention_is_gibbs_noZ_setoid  主件2·前提消去示范件     *)
(*       （原件 1 同结论、少前提 3——配分相等前提由 A2 供替）          *)
(*  形 B（req 形·CW220 SigMigrate 温度参数载体，S : Set）：           *)
(*   B1 zauto_mirror_point_temp        保底·逐点镜像件（温度参数形）  *)
(*   B2 zauto_Z_eq_temp                主件·Z_auto 引理（温度参数形） *)
(*   B3 zauto_attention_is_gibbs_temp_noZ   主件2·前提消去示范件      *)
(*       （原件 2 同结论、少前提 3——配分相等前提由 B2 供替）          *)
(*  形 C（Id 形·Set 层零 Prop，CW219 RealInterfaceEnhanced+SumOver）： *)
(*   C1 zauto_id_mirror                保底·逐点镜像件（Id 形）       *)
(*   C2 zauto_id_Z_eq                  主件·Z_auto 引理（Id 形）      *)
(*                                                                *)
(* 诚实账目：A3/B3 相对原件少一实质前提（配分相等），多一求和载体      *)
(*   外延参数（sum_req_ext / sumf_req_ext）——该参数是载体接口性质，    *)
(*   任何具体求和（有限和/列表和）构造性满足，非对分布的新增假设；     *)
(*   A2/B2/C2 的 Z_auto 本体即「premise 可由（镜像前提+外延）自动供替」  *)
(*   的定理形态。                                                   *)
(*                                                                *)
(* 红线：Set 层语句零 Prop（req/lt/Id 均 Set 值谓词）；全 Qed 闭合；    *)
(*   尾部 Print Assumptions 新件全 Closed；既有文件零改；零 git。      *)
(* 前缀台账：zauto_ 前缀全库 grep 零重名（本席首用）。                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import CW220_Extensions.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 形 A（req 形）：CW219 AttentionGibbsBridgeSetoid 载体             *)
(*   出口签名实测：Z_thermo_setoid R RI S sum D D_pos energy；       *)
(*   partition_function_setoid R RI S sum z；                       *)
(*   attention_is_gibbs_setoid 前提序 = HD、Henergy、HZ。             *)
(* ============================================================ *)

(* A1 保底·逐点镜像件：inv D == one + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_pos(z s)（即 exp_neg(opp(z s))）逐点。 *)
Lemma zauto_mirror_point_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (D : R) (D_pos : lt zero D) (energy z : S -> R),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@boltzmann_factor_setoid R RIS S D D_pos energy s)
      (@exp_pos_fn_setoid R RIS (z s)).
Proof.
  intros R RIS S D D_pos energy z HD Henergy s.
  exact (@exp_neg_req_compat_setoid R RIS
           (mult (inv_pos D D_pos) (energy s)) (opp (z s))
           (@req_trans R RIS (mult (inv_pos D D_pos) (energy s)) (energy s) (opp (z s))
              (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                             (mult one (energy s)) (energy s)
                 (@req_mult_compat R RIS (inv_pos D D_pos) one (energy s) (energy s)
                    HD (@req_refl R RIS (energy s)))
                 (@req_trans R RIS (mult one (energy s)) (mult (energy s) one) (energy s)
                    (@mult_comm R RIS one (energy s))
                    (@mult_one R RIS (energy s))))
              (Henergy s))).
Qed.

(* A2 主件·Z_auto 引理：partition_function_setoid == Z_thermo_setoid。
   逐点镜像（A1）+ 求和外延（sum_req_ext）组装；配分相等前提不出现。 *)
Lemma zauto_Z_eq_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (sum_req_over_S : (S -> R) -> R)
         (sum_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sum_req_over_S f) (sum_req_over_S g))
         (D : R) (D_pos : lt zero D) (energy z : S -> R),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req (@partition_function_setoid R RIS S sum_req_over_S z)
      (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy).
Proof.
  intros R RIS S sum_req_over_S sum_req_ext D D_pos energy z HD Henergy.
  exact (sum_req_ext (fun s : S => exp_neg (opp (z s)))
                     (fun s : S => exp_neg (mult (inv_pos D D_pos) (energy s)))
                     (fun s : S =>
                        @req_sym R RIS (exp_neg (mult (inv_pos D D_pos) (energy s)))
                          (exp_neg (opp (z s)))
                          (zauto_mirror_point_setoid R RIS S D D_pos energy z
                                                     HD Henergy s))).
Qed.

(* A3 主件2·前提消去示范件：原件 1 attention_is_gibbs_setoid 同结论，
   配分相等前提（req Z_thermo_setoid (partition_function_setoid z)）
   不再出现——由 A2 供替（req_sym 换向后喂入）。 *)
Lemma zauto_attention_is_gibbs_noZ_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (sum_req_over_S : (S -> R) -> R)
         (sum_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sum_req_over_S f) (sum_req_over_S g))
         (sum_pos_preserved_req : forall f : S -> R,
            (forall s : S, lt zero (f s)) -> lt zero (sum_req_over_S f))
         (D : R) (D_pos : lt zero D) (energy z : S -> R)
         (Z_thermo_pos : lt zero (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy)),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@softmax_setoid R RIS S sum_req_over_S sum_pos_preserved_req z s)
      (@boltzmann_dist_attn_setoid R RIS S sum_req_over_S D D_pos energy
                                   Z_thermo_pos s).
Proof.
  intros R RIS S sum_req_over_S sum_req_ext sum_pos_preserved_req
         D D_pos energy z Z_thermo_pos HD Henergy s.
  exact (@attention_is_gibbs_setoid R RIS S sum_req_over_S sum_pos_preserved_req
           D D_pos energy z Z_thermo_pos HD Henergy
           (@req_sym R RIS (@partition_function_setoid R RIS S sum_req_over_S z)
                     (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy)
                     (zauto_Z_eq_setoid R RIS S sum_req_over_S sum_req_ext
                                        D D_pos energy z HD Henergy)) s).
Qed.

(* ============================================================ *)
(* 形 B（req 形）：CW220 SigMigrate.ReqGibbsPilot 温度参数载体        *)
(*   出口签名实测（@ 全参形）：                                      *)
(*   Z_thermo R RIS S sumf D D_pos energy；                          *)
(*   cwe_partition_function_temp R RIS S sumf T T_pos z；                *)
(*   req_attention_is_gibbs_temp 前提序 = HD（inv T == inv D）、       *)
(*   Henergy、HZ（req Z_thermo cwe_partition_function_temp）。            *)
(* ============================================================ *)

(* B1 保底·逐点镜像件（温度参数形）：inv T == inv D + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_neg(opp(inv T·z s)) 逐点
   （RHS 即 cwe_partition_function_temp 第 s 项，cwe_exp_pos_fn delta 换形后）。 *)
Lemma zauto_mirror_point_temp :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@SigMigrate.boltzmann_factor R RIS S D D_pos energy s)
      (exp_neg (opp (mult (inv_pos T T_pos) (z s)))).
Proof.
  intros R RIS S T T_pos D D_pos energy z HD Henergy s.
  exact (@exp_neg_req_compat_setoid R RIS
           (mult (inv_pos D D_pos) (energy s)) (opp (mult (inv_pos T T_pos) (z s)))
           (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                       (opp (mult (inv_pos D D_pos) (z s)))
                       (opp (mult (inv_pos T T_pos) (z s)))
              (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                          (mult (inv_pos D D_pos) (opp (z s)))
                          (opp (mult (inv_pos D D_pos) (z s)))
                 (@req_mult_compat R RIS (inv_pos D D_pos) (inv_pos D D_pos)
                                   (energy s) (opp (z s))
                    (@req_refl R RIS (inv_pos D D_pos)) (Henergy s))
                 (@SigMigrate.req_mult_opp_l R RIS (inv_pos D D_pos) (z s)))
              (@req_opp_compat R RIS (mult (inv_pos D D_pos) (z s))
                               (mult (inv_pos T T_pos) (z s))
                 (@req_mult_compat R RIS (inv_pos D D_pos) (inv_pos T T_pos)
                                   (z s) (z s)
                    (@req_sym R RIS (inv_pos T T_pos) (inv_pos D D_pos) HD)
                    (@req_refl R RIS (z s)))))).
Qed.

(* B2 主件·Z_auto 引理（温度参数形）：cwe_partition_function_temp == Z_thermo。
   逐点镜像（B1）+ 求和外延（sumf_req_ext，诚实接口：任何具体求和
   构造性满足）组装；配分相等前提不出现。 *)
Lemma zauto_Z_eq_temp :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (sumf : (S -> R) -> R)
         (sumf_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req (@SigMigrate.cwe_partition_function_temp R RIS S sumf T T_pos z)
      (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy).
Proof.
  intros R RIS S sumf sumf_req_ext T T_pos D D_pos energy z HD Henergy.
  exact (sumf_req_ext (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                      (fun s : S => exp_neg (mult (inv_pos D D_pos) (energy s)))
                      (fun s : S =>
                         @req_sym R RIS (exp_neg (mult (inv_pos D D_pos) (energy s)))
                           (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                           (zauto_mirror_point_temp R RIS S T T_pos D D_pos energy z
                                                    HD Henergy s))).
Qed.

(* B3 主件2·前提消去示范件（温度参数形）：原件 2 req_attention_is_gibbs_temp
   同结论，前提 3（req Z_thermo cwe_partition_function_temp）不再出现——
   由 B2 供替；原节内 exp 兼容 Hypothesis 桥位由已证件
   exp_neg_req_compat_setoid 填充（该假设也被消去）。 *)
Lemma zauto_attention_is_gibbs_temp_noZ :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (sumf : (S -> R) -> R)
         (sumf_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R)
         (partition_function_temp_pos :
            lt zero (@SigMigrate.cwe_partition_function_temp R RIS S sumf T T_pos z))
         (Z_thermo_pos : lt zero (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy)),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@SigMigrate.cwe_softmax_temp R RIS S sumf T T_pos z
                                partition_function_temp_pos s)
      (@SigMigrate.boltzmann_dist_attn R RIS S sumf D D_pos energy Z_thermo_pos s).
Proof.
  intros R RIS S sumf sumf_req_ext T T_pos D D_pos energy z
         partition_function_temp_pos Z_thermo_pos HD Henergy s.
  exact (@SigMigrate.req_attention_is_gibbs_temp R RIS S sumf
           (@exp_neg_req_compat_setoid R RIS)
           T T_pos D D_pos energy z partition_function_temp_pos Z_thermo_pos
           HD Henergy
           (@req_sym R RIS (@SigMigrate.cwe_partition_function_temp R RIS S sumf T T_pos z)
                     (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy)
                     (zauto_Z_eq_temp R RIS S sumf sumf_req_ext T T_pos D D_pos
                                      energy z HD Henergy)) s).
Qed.

(* ============================================================ *)
(* 形 C（Id 形·Set 层零 Prop）：CW219 RealInterfaceEnhanced + SumOver。 *)
(*   外延引擎 = SumOver 字段 sum_over_S_ext（Id 形，实测 L1411）。      *)
(* ============================================================ *)

Section ZAutoId.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let lt := @lt RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition zauto_id_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition zauto_id_Z_thermo : R :=
  sum_over_S zauto_id_boltzmann_factor.

Definition zauto_id_exp_pos (x : R) : R := exp_neg (opp x).

Definition zauto_id_partition : R :=
  sum_over_S (fun s : S => zauto_id_exp_pos (z s)).

(* C1 保底·逐点镜像件（Id 形）：inv D == one + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_pos(z s) 逐点（Id 收口，零 Prop）。 *)
Lemma zauto_id_mirror :
  Id (inv_pos D D_pos) one ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  forall s : S,
  Id (zauto_id_boltzmann_factor s) (zauto_id_exp_pos (z s)).
Proof.
  intros HD Henergy s.
  exact (id_cong (fun x : R => exp_neg x)
           (id_trans
              (id_trans (id_cong (fun x : R => mult x (energy s)) HD)
                        (id_trans (@mult_comm RI one (energy s))
                                  (@mult_one RI (energy s))))
              (Henergy s))).
Qed.

(* C2 主件·Z_auto 引理（Id 形）：zauto_id_partition == zauto_id_Z_thermo。
   逐点镜像（C1）+ SumOver 外延字段组装；Id 层语句，零 Prop。 *)
Lemma zauto_id_Z_eq :
  Id (inv_pos D D_pos) one ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id zauto_id_partition zauto_id_Z_thermo.
Proof.
  intros HD Henergy.
  exact (@sum_over_S_ext RI SS SO (fun s : S => zauto_id_exp_pos (z s))
                         zauto_id_boltzmann_factor
                         (fun s : S => id_sym (zauto_id_mirror HD Henergy s))).
Qed.

End ZAutoId.

(* ============================================================ *)
(* 尾验：新件零假设（Closed）——8 件全数打表                          *)
(* ============================================================ *)
Print Assumptions zauto_mirror_point_setoid.
Print Assumptions zauto_Z_eq_setoid.
Print Assumptions zauto_attention_is_gibbs_noZ_setoid.
Print Assumptions zauto_mirror_point_temp.
Print Assumptions zauto_Z_eq_temp.
Print Assumptions zauto_attention_is_gibbs_temp_noZ.
Print Assumptions zauto_id_mirror.
Print Assumptions zauto_id_Z_eq.

(* ======== G12_ZPosFam 成员件：UpReqZPosFinal（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqZPosFinal.v —— Z_align_pos 四站点前提消去席（终装）          *)
(*   消费席60 通用键 UpReqZPosD（zposd_Z_pos_of_partition 主键）+    *)
(*   G1 钥匙 UpReqSumD（sumd_sum_ext / sumd_sum_linear 喂定）+       *)
(*   UpReqAlign.req_align_partition_condition（配分条件桥）。        *)
(*                                                                *)
(* 使命（战役工卡）：T2① 普查 G3 族 Z_align_pos 槽 ×4 站点            *)
(*   （UpReqAlign.v:94 / UpReqAlign2.v:104 / UpReqAlignRestA.v:75 /  *)
(*   UpReqDpoLoss.v:58）的消费定理面前提消去：槽位 Z_align_pos 被     *)
(*   zposd 键替换，其余前提原样；产出件名 = 原定理名_zpfinal_站点号。  *)
(*                                                                *)
(* 消去路线（本席升级，超出席72 保底件）：                            *)
(*   席72（UpReqZPosI2.v 保底①②③④）判「键形失配→根引擎直装」：      *)
(*   其保底件只交付槽值 lt zero Z_align（E354 sumd 喂位），且因        *)
(*   Z_align 逐项含 pi_ref 外乘而绕开 zposd 键。本席发现站点1 的      *)
(*   配分条件规格 req_align_partition_condition@UpReqAlign.v:210      *)
(*     req Z_align_req (sumf (exp_neg (mult iv (align_energy_req))))  *)
(*   经 E354（sumf := sumd_sumf）后与 zposd_Z_pos_of_partition 的      *)
(*   槽形逐位重合（base_loss := align_energy_req），故站点1/3/4        *)
(*   （3/4 消费的正是站点1 的 Z_align_req 常数）走真 zposd 键路线；    *)
(*   站点2（req2_Z_align）无配分条件件，但其体与 Z_align_req δ 等价    *)
(*   （convertible），键喂定 exact 换轨直通（本席勘误 2）。           *)
(*                                                                *)
(* 逐站消去台账（消去前假设集 vs 消去后假设集；载体位=sumf 装定位）：  *)
(*  站1 UpReqAlign.v:94（消费面=pi_star_req@95 / req_pi_star_pos /    *)
(*     req_pi_star_normalized@222；普查 L518 记 2 件，本席 Check      *)
(*     实证 req_pi_star_pos 亦携槽位=3 件，勘误 1）：                 *)
(*     · pi_star_req_zpfinal_1（定义件）                              *)
(*       前 6 位{sumf,reward,beta,beta_pos,pi_ref,Z_align_pos}        *)
(*       后 7 位{enum,reward,beta,beta_pos,pi_ref,pi_ref_pos,Hne}     *)
(*       数学位 Z_align_pos 消去→datum 位 Hne；载体锁定 sumd_sumf。   *)
(*     · req_pi_star_pos_zpfinal_1：前 7 位（含 Z_align_pos）→        *)
(*       后 7 位（Z_align_pos→Hne）；数位降级同上。                   *)
(*     · req_pi_star_normalized_zpfinal_1：                           *)
(*       前 7 位{sumf,sum_linear,reward,beta,beta_pos,pi_ref,         *)
(*       Z_align_pos}→后 7 位{enum,reward,beta,beta_pos,pi_ref,       *)
(*       pi_ref_pos,Hne}；Z_align_pos 消去 + sum_linear 桥定义性      *)
(*       喂定消去（sumd_sum_linear 同型直供），未证数学/桥位净 -2。    *)
(*  站2 UpReqAlign2.v:104（消费面=req2_pi_star@105 /                  *)
(*     req2_pi_star_normalized@387；普查 L551 记 2 件）：             *)
(*     · req2_pi_star_zpfinal_2：前 6 位→后 7 位（同站1 定义件）。    *)
(*     · req2_pi_star_normalized_zpfinal_2：前 7 位→后 7 位；         *)
(*       Z_align_pos 消去 + sum_linear 喂定消去，净 -2。              *)
(*  站3 UpReqAlignRestA.v:75（消费面=ralt_pistar@201 /                *)
(*     ralt_pistar_pos@196 / ralt_log_pi_star@207 /                   *)
(*     ralt_dpo_reward_recovers@260 / ralt_dpo_reward_relative_exact  *)
(*     @343 / ralt_dpo_loss_at_pi_star@509；普查 L568 记 7 处）：      *)
(*     6 件 *_zpfinal_3：每件 Z_align_pos 消去→Hne；log 双桥位        *)
(*     （ralt_log_req_compat / ralt_log_inv_exp_neg_req）原样保留     *)
(*     （接口缺口桥，非本席消去面）。DPO 簇 4 定理假设集全部缩减。     *)
(*  站4 UpReqDpoLoss.v:58（消费面=rdl_pistar@87 / rdl_pistar_pos@90 /  *)
(*     rdl_dpo_total_loss_at_star@164；普查 L793）：                  *)
(*     3 件 *_zpfinal_4：同站3 法；批5 解冻主件 dpo_total_loss_at_star *)
(*     的槽位随之消去。                                               *)
(*                                                                *)
(* 下游影响清单（假设集因此缩减的面）：                                *)
(*   - 旗舰链入端：req_pi_star_pos / req_pi_star_normalized（站1）     *)
(*     与 req2_pi_star_normalized（站2）—— π* 正性/归一化两腿；       *)
(*   - DPO 奖励簇：ralt_log_pi_star → ralt_dpo_reward_recovers →      *)
(*     ralt_dpo_reward_relative_exact（基线消去）→                    *)
(*     ralt_dpo_loss_at_pi_star（π* 处损失闭式）；                    *)
(*   - 批5 解冻主件：rdl_dpo_total_loss_at_star；                     *)
(*   - 普查 L125「7/21 传递消费定理面」：上述件的一切下游消费件        *)
(*     经换件即继承缩减后假设集（Z_pos 数学位 → datum 非空位）。       *)
(*                                                                *)
(* 红线：Set 层语句（lt/req 均 Set 值谓词；槽放电新增前提仅 datum 位   *)
(*   Not (enum = nil)，沿 ZPosD 签名台账先例）；纯项式组装（exact      *)
(*   供给项，零 rewrite 战术）；零外部未证假设，尾部 Print Assumptions *)
(*   新件全 Closed；既有文件零改；前缀 zpfinal_ 全库防撞 grep 零命中；  *)
(*   零 git。                                                        *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.

Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlignRestA.
Require Import UpReqDpoLoss.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 键喂定件 1（站1/3/4 共用）：Z_align_pos 槽的 zposd 键放电形         *)
(*   zposd_Z_pos_of_partition（席60 主件1）+ 配分条件桥               *)
(*   req_align_partition_condition（E354：sumf := sumd_sumf，        *)
(*   sum_ext := sumd_sum_ext 定义性喂定）+ datum 非空位。             *)
(* ============================================================ *)
Definition zpfinal1_Z_align_pos_key
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref) :=
  @zposd_Z_pos_of_partition R RIS S enum
    (@UpReqAlign.align_energy_req R RIS S reward beta pi_ref pi_ref_pos)
    beta beta_pos
    (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
       reward beta beta_pos pi_ref)
    (@UpReqAlign.req_align_partition_condition R RIS S
       (@sumd_sumf R RIS S enum)
       (@sumd_sum_ext R RIS S enum)
       reward beta beta_pos pi_ref pi_ref_pos)
    Hne.

(* ============================================================ *)
(* 键喂定件 2（站2）：req2_Z_align 体与 Z_align_req δ 等价             *)
(*   （同体 sumf 逐项形，convertible），键喂定 exact 换轨直通。        *)
(* ============================================================ *)
Lemma zpfinal2_req2_Z_align_pos_key
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
           pi_ref_pos Hne).
Qed.

(* ============================================================ *)
(* 站1 UpReqAlign.v:94 消去件（槽消费面 3 件）                        *)
(* ============================================================ *)

(* 定义件：pi_star_req@95 槽放电实例形 *)
Definition pi_star_req_zpfinal_1
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) : S -> R :=
  @UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref
    (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne).

(* 消去件 1a：req_pi_star_pos（π* 逐点正性）
   消去前 7 位{sumf,reward,beta,beta_pos,pi_ref,pi_ref_pos,Z_align_pos}
   消去后 7 位{enum,reward,beta,beta_pos,pi_ref,pi_ref_pos,Hne} *)
Lemma req_pi_star_pos_zpfinal_1
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  @UpReqAlign.pos_dist R RIS S
    (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
       reward beta beta_pos pi_ref
       (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne)).
Proof.
  exact (@UpReqAlign.req_pi_star_pos R RIS S (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)).
Qed.

(* 消去件 1b：req_pi_star_normalized（π* 归一化）
   消去前 7 位{sumf,sum_linear,reward,beta,beta_pos,pi_ref,Z_align_pos}
   消去后 7 位{enum,reward,beta,beta_pos,pi_ref,pi_ref_pos,Hne}
   （Z_align_pos 消去 + sum_linear 定义性喂定消去，净 -2） *)
Lemma req_pi_star_normalized_zpfinal_1
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  req
    (@sumd_sumf R RIS S enum
       (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
          reward beta beta_pos pi_ref
          (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
             pi_ref_pos Hne)))
    one.
Proof.
  exact (@UpReqAlign.req_pi_star_normalized R RIS S
           (@sumd_sumf R RIS S enum)
           (@sumd_sum_linear R RIS S enum)
           reward beta beta_pos pi_ref
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)).
Qed.

(* ============================================================ *)
(* 站2 UpReqAlign2.v:104 消去件（槽消费面 2 件）                      *)
(* ============================================================ *)

(* 定义件：req2_pi_star@105 槽放电实例形 *)
Definition req2_pi_star_zpfinal_2
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) : S -> R :=
  @UpReqAlign2.req2_pi_star R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref
    (zpfinal2_req2_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne).

(* 消去件 2a：req2_pi_star_normalized
   消去前 7 位{sumf,sum_linear,reward,beta,beta_pos,pi_ref,Z_align_pos}
   消去后 7 位{enum,reward,beta,beta_pos,pi_ref,pi_ref_pos,Hne}
   （Z_align_pos 消去 + sum_linear 定义性喂定消去，净 -2） *)
Lemma req2_pi_star_normalized_zpfinal_2
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  req
    (@sumd_sumf R RIS S enum
       (@UpReqAlign2.req2_pi_star R RIS S (@sumd_sumf R RIS S enum)
          reward beta beta_pos pi_ref
          (zpfinal2_req2_Z_align_pos_key R RIS S enum reward beta beta_pos
             pi_ref pi_ref_pos Hne)))
    one.
Proof.
  exact (@UpReqAlign2.req2_pi_star_normalized R RIS S
           (@sumd_sumf R RIS S enum)
           (@sumd_sum_linear R RIS S enum)
           reward beta beta_pos pi_ref
           (zpfinal2_req2_Z_align_pos_key R RIS S enum reward beta beta_pos
              pi_ref pi_ref_pos Hne)).
Qed.

(* ============================================================ *)
(* 站3 UpReqAlignRestA.v:75 消去件（槽消费面 6 件；log 双桥原样）      *)
(* ============================================================ *)

(* 定义件：ralt_pistar@201 槽放电实例形 *)
Definition ralt_pistar_zpfinal_3
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) : S -> R :=
  @UpReqAlignRestA.ralt_pistar R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref
    (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne).

(* 消去件 3a：ralt_pistar_pos（π* 逐点正性见证）
   消去前 8 位{sumf,reward,beta,beta_pos,pi_ref,pi_ref_pos,Z_align_pos,s}
   消去后 8 位（Z_align_pos→Hne，载体锁定）
   （透明 Definition 形：下游 3b-3e 语句引用其 δ 展开直连） *)
Definition ralt_pistar_pos_zpfinal_3
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) (s : S) :
  lt zero
    (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
       reward beta beta_pos pi_ref
       (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne) s) :=
  @UpReqAlignRestA.ralt_pistar_pos R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref pi_ref_pos
    (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne) s.

(* 消去件 3b：ralt_log_pi_star（log π* 闭式）
   消去前 9 位{sumf,reward,beta,beta_pos,pi_ref,pi_ref_pos,Z_align_pos,
   log双桥2}→消去后 9 位（Z_align_pos→Hne；log 双桥原样保留） *)
Lemma ralt_log_pi_star_zpfinal_3
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil))
      (Hlog : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
                req x y -> req (log x Hx) (log y Hy))
      (Hlie : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) :
  forall s : S,
  req
    (log
       (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
          reward beta beta_pos pi_ref
          (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
             pi_ref_pos Hne) s)
       (ralt_pistar_pos_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne s))
    (plus
       (opp
          (log
             (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
                reward beta beta_pos pi_ref)
             (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos
                pi_ref pi_ref_pos Hne)))
       (plus (log (pi_ref s) (pi_ref_pos s))
             (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  exact (@UpReqAlignRestA.ralt_log_pi_star R RIS S (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)
           Hlog Hlie).
Qed.

(* 消去件 3c：ralt_dpo_reward_recovers（DPO 奖励基线偏移闭式）
   消去前后假设集同 3b（Z_align_pos→Hne，log 双桥原样） *)
Lemma ralt_dpo_reward_recovers_zpfinal_3
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil))
      (Hlog : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
                req x y -> req (log x Hx) (log y Hy))
      (Hlie : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) :
  forall s : S,
  req
    (@UpReqAlignRestA.ralt_dir R RIS S beta pi_ref pi_ref_pos
       (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
          reward beta beta_pos pi_ref
          (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
             pi_ref_pos Hne))
       (ralt_pistar_pos_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne)
       s)
    (plus (reward s)
          (opp
             (mult beta
                (log
                   (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
                      reward beta beta_pos pi_ref)
                   (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos
                      pi_ref pi_ref_pos Hne))))).
Proof.
  exact (@UpReqAlignRestA.ralt_dpo_reward_recovers R RIS S
           (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)
           Hlog Hlie).
Qed.

(* 消去件 3d：ralt_dpo_reward_relative_exact（基线严格消去）
   消去前后假设集同 3b *)
Lemma ralt_dpo_reward_relative_exact_zpfinal_3
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil))
      (Hlog : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
                req x y -> req (log x Hx) (log y Hy))
      (Hlie : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) :
  forall s s' : S,
  req
    (req_minus
       (@UpReqAlignRestA.ralt_dir R RIS S beta pi_ref pi_ref_pos
          (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref
             (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos
                pi_ref pi_ref_pos Hne))
          (ralt_pistar_pos_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
             pi_ref_pos Hne)
          s)
       (@UpReqAlignRestA.ralt_dir R RIS S beta pi_ref pi_ref_pos
          (@UpReqAlign.pi_star_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref
             (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos
                pi_ref pi_ref_pos Hne))
          (ralt_pistar_pos_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
             pi_ref_pos Hne)
          s'))
    (req_minus (reward s) (reward s')).
Proof.
  exact (@UpReqAlignRestA.ralt_dpo_reward_relative_exact R RIS S
           (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)
           Hlog Hlie).
Qed.

(* 消去件 3e：ralt_dpo_loss_at_pi_star（π* 处 DPO 损失闭式）
   消去前后假设集同 3b *)
Lemma ralt_dpo_loss_at_pi_star_zpfinal_3
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil))
      (Hlog : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
                req x y -> req (log x Hx) (log y Hy))
      (Hlie : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) :
  forall s_w s_l : S,
  req
    (@UpReqAlignRestA.ralt_dpo_loss_pair R RIS S beta pi_ref pi_ref_pos
       (ralt_pistar_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne)
       (ralt_pistar_pos_zpfinal_3 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne)
       s_w s_l)
    (opp
       (log (sigmoid_req (req_minus (reward s_w) (reward s_l)))
          (req_sigmoid_pos (req_minus (reward s_w) (reward s_l))))).
Proof.
  exact (@UpReqAlignRestA.ralt_dpo_loss_at_pi_star R RIS S
           (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)
           Hlog Hlie).
Qed.

(* ============================================================ *)
(* 站4 UpReqDpoLoss.v:58 消去件（槽消费面 3 件；log 双桥原样）         *)
(* ============================================================ *)

(* 定义件：rdl_pistar@87 槽放电实例形 *)
Definition rdl_pistar_zpfinal_4
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) : S -> R :=
  @UpReqDpoLoss.rdl_pistar R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref
    (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne).

(* 消去件 4a：rdl_pistar_pos
   消去前 8 位{sumf,reward,beta,beta_pos,pi_ref,pi_ref_pos,Z_align_pos,s}
   消去后 8 位（Z_align_pos→Hne）
   （透明 Definition 形：4b 语句引用其 δ 展开直连） *)
Definition rdl_pistar_pos_zpfinal_4
           (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (enum : list S)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Hne : Not (enum = nil)) (s : S) :
  lt zero
    (@UpReqDpoLoss.rdl_pistar R RIS S (@sumd_sumf R RIS S enum)
       reward beta beta_pos pi_ref
       (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne) s) :=
  @UpReqDpoLoss.rdl_pistar_pos R RIS S (@sumd_sumf R RIS S enum)
    reward beta beta_pos pi_ref pi_ref_pos
    (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
       pi_ref_pos Hne) s.

(* 消去件 4b：rdl_dpo_total_loss_at_star（批5 解冻主件）
   消去前 12 位{sumf,reward,beta,beta_pos,pi_ref,pi_ref_pos,Z_align_pos,
   log双桥2,Preference,pref_win,pref_lose,pref_dataset}
   消去后 12 位（Z_align_pos→Hne；log 双桥原样；preference 三参原样） *)
Lemma rdl_dpo_total_loss_at_star_zpfinal_4
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil))
      (Hlog : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
                req x y -> req (log x Hx) (log y Hy))
      (Hlie : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x)
      (Preference : Set) (pref_win pref_lose : Preference -> S)
      (pref_dataset : list Preference) :
  req
    (@UpReqDpoLoss.rdl_dpo_total_loss R RIS S beta pi_ref pi_ref_pos
       Preference pref_win pref_lose pref_dataset
       (rdl_pistar_zpfinal_4 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne)
       (rdl_pistar_pos_zpfinal_4 R RIS S enum reward beta beta_pos pi_ref
          pi_ref_pos Hne))
    (@UpReqDpoLoss.rdl_dpo_total_loss_star R RIS S reward Preference
       pref_win pref_lose pref_dataset).
Proof.
  exact (@UpReqDpoLoss.rdl_dpo_total_loss_at_star R RIS S
           (@sumd_sumf R RIS S enum)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal1_Z_align_pos_key R RIS S enum reward beta beta_pos pi_ref
              pi_ref_pos Hne)
           Hlog Hlie Preference pref_win pref_lose pref_dataset).
Qed.

(* ============ 终装证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions zpfinal1_Z_align_pos_key.
Print Assumptions zpfinal2_req2_Z_align_pos_key.
Print Assumptions pi_star_req_zpfinal_1.
Print Assumptions req_pi_star_pos_zpfinal_1.
Print Assumptions req_pi_star_normalized_zpfinal_1.
Print Assumptions req2_pi_star_zpfinal_2.
Print Assumptions req2_pi_star_normalized_zpfinal_2.
Print Assumptions ralt_pistar_zpfinal_3.
Print Assumptions ralt_pistar_pos_zpfinal_3.
Print Assumptions ralt_log_pi_star_zpfinal_3.
Print Assumptions ralt_dpo_reward_recovers_zpfinal_3.
Print Assumptions ralt_dpo_reward_relative_exact_zpfinal_3.
Print Assumptions ralt_dpo_loss_at_pi_star_zpfinal_3.
Print Assumptions rdl_pistar_zpfinal_4.
Print Assumptions rdl_pistar_pos_zpfinal_4.
Print Assumptions rdl_dpo_total_loss_at_star_zpfinal_4.

(* ============ G3 证据：提取面（Obj.magic 扫描用） ============ *)
Extraction "_zpfinal_extract.ml" zpfinal1_Z_align_pos_key
  zpfinal2_req2_Z_align_pos_key pi_star_req_zpfinal_1
  req_pi_star_pos_zpfinal_1 req_pi_star_normalized_zpfinal_1
  req2_pi_star_zpfinal_2 req2_pi_star_normalized_zpfinal_2
  ralt_pistar_zpfinal_3 ralt_pistar_pos_zpfinal_3
  ralt_log_pi_star_zpfinal_3 ralt_dpo_reward_recovers_zpfinal_3
  ralt_dpo_reward_relative_exact_zpfinal_3
  ralt_dpo_loss_at_pi_star_zpfinal_3 rdl_pistar_zpfinal_4
  rdl_pistar_pos_zpfinal_4 rdl_dpo_total_loss_at_star_zpfinal_4.
