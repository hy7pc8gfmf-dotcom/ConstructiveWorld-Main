(* ==========================================================================)
   abl_tail_def_instance.v — 配分定义性实例化件族统一件＋可达槽具名闭形
   ── 使命：对配分/温度配分接口假设族的定义性实例化路线给出统一件族。四件构造：
      （一）泛 sumf 统一装配与自反闭合——tspd_g5_partition_Z（配分函数装配：
      Z := sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))，
      R/S/sumf/base_loss/D/D_pos 全参，不绑任何具体求和实现）＋
      tspd_g5_partition_condition_req_refl（req_refl 一击，对任意 sumf 面闭合
      partition_condition 型槽语句）；（二）温度配分带证书参面统一件——
      tspd_g5_Z_temp_of＋tspd_g5_Z_temp_spec_ht_carry；（三）可达槽逐槽具名闭形——
      tspd_g5_pa04_partition_condition（Arch_PA_04.v:886-887 槽面节环境同构，抽象 sumf）
      与 tspd_g5_bbd_partition_condition（BBDBridgeSupply.v:98，sumf := csm_sumf S enum
      实化读法）。逐槽判读（如实申报）：Z_temp_spec 泛 t 裸槽面（不带证书参）定义性
      装配路线不可达——逆算子 inv_pos 之值计算依赖证书参（real_inv_pos 定义体拆用
      证书参取 eps0/N0，S03_QExp.v:6681-6686），本件对其不发供给定理，判读登记于
      池内交付报告；带证书参面可达，由（二）闭合。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqConcSoftmax（csm_sumf 实化读法）；
      Stdlib List。全部只读引用，既有件零字节不动、零级联。
   ── 对标行：目标命题位现档＝BBDBridgeSupply.v:98／Arch_PA_04.v:886-887／
      PA_TempMonoW2Mark.v:74-76／Arch_PA_02.v:921-923；req_refl 配方先例＝
      csm_sum_eq_list@UpReqConcSoftmax.v:44-46、sumd_sum_eq_list@UpReqSumD.v:108-111、
      zpi3_Z_temp_spec@G12_ZPosFam.v:836-850；装配先例＝zposd_Z@G12_ZPosFam.v:125-128；
      逐槽具名先例＝abl_tail_supply_70.v:145-162。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑；语句面
      承载位全 Set 形（req/lt 皆 Set 值，零 Prop 泄露）；定义性自反闭合件承
      csm_sum_eq_list/sumd_sum_eq_list 先例款；本件非平凡面在泛 sumf 统一形与带证书参
      统一形；逐件 Print Assumptions 取全 Closed 判据；文件尾提取检验区取 Obj.magic
      计 0 判据（若触提取器硬错或记录层转写非零，照池内先例处置并逐条如实登记，禁虚报）。
   ── 编译配方：单道 nice -19 rocq c -native-compiler no -Q <统一缓存根> "" abl_tail_def_instance.v；
      绿判：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v。
   ========================================================================== *)

From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqConcSoftmax.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 一、泛 sumf 统一装配与自反闭合                                  *)
(*    装配 Z 不绑任何具体求和实现：任意接口 sumf（含抽象 sumf 假设  *)
(*    位与 csm_sumf 实化读法）皆可入位；配分等式 req_refl 一步闭合。 *)
(* ============================================================ *)

Definition tspd_g5_partition_Z
    (R : Set) {RIS : RealInterfaceEnhancedSetoid R}
    (S : Set) (sumf : (S -> R) -> R)
    (base_loss : S -> R) (D : R) (D_pos : lt zero D) : R :=
  sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))).

Theorem tspd_g5_partition_condition_req_refl :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
    (sumf : (S -> R) -> R) (base_loss : S -> R) (D : R) (D_pos : lt zero D),
    req (tspd_g5_partition_Z R S sumf base_loss D D_pos)
        (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intros R RIS S sumf base_loss D D_pos.
  exact (req_refl
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
Qed.

(* ============================================================ *)
(* 二、温度配分带证书参面统一件                                    *)
(*    Z_temp_spec 槽语句的可装配面：温度 t 与正性证书 Ht 同参的算子  *)
(*    （目标命题位 Z_temp : R -> R 裸函数面不携带证书参，其定义性装配路线  *)
(*    阻塞，判读见头注与池内交付报告；本面为该族的可达装配面）。    *)
(* ============================================================ *)

Definition tspd_g5_Z_temp_of
    (R : Set) {RIS : RealInterfaceEnhancedSetoid R}
    (S : Set) (sumf : (S -> R) -> R) (base_loss : S -> R)
    (t : R) (Ht : lt zero t) : R :=
  sumf (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s))).

Theorem tspd_g5_Z_temp_spec_ht_carry :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set)
    (sumf : (S -> R) -> R) (base_loss : S -> R) (t : R) (Ht : lt zero t),
    req (tspd_g5_Z_temp_of R S sumf base_loss t Ht)
        (sumf (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
Proof.
  intros R RIS S sumf base_loss t Ht.
  exact (req_refl
           (sumf (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s))))).
Qed.

(* ============================================================ *)
(* 三、可达槽逐槽具名闭形                                          *)
(*    槽面节环境同构（Arch_PA_04.v:865-887／BBDBridgeSupply.v:58-98  *)
(*    同序同形），语句面取目标命题位逐字同形、Z 位以装配定义入位。  *)
(* ============================================================ *)

(* ---- Arch_PA_04.v:886-887 槽面（抽象 sumf 节） ---- *)
Section TspG5Pa04Slot.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

Theorem tspd_g5_pa04_partition_condition :
  req (tspd_g5_partition_Z R S sumf base_loss D D_pos)
      (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
Qed.

End TspG5Pa04Slot.

(* ---- BBDBridgeSupply.v:98 槽面（csm_sumf 实化读法节） ---- *)
Section TspG5BbdSlot.

Variable S : Set.
Variable enum : list S.
Let sumf : (S -> Real) -> Real := csm_sumf S enum.
Variable base_loss : S -> Real.
Variable D : Real.
Variable D_pos : lt zero D.

Theorem tspd_g5_bbd_partition_condition :
  req (@tspd_g5_partition_Z Real RealEnhancedReal S sumf base_loss D D_pos)
      (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
Qed.

End TspG5BbdSlot.

(* ============================================================ *)
(* 四、逐件前提面审计（全 Closed 判据；名清单=Qed 计数=语句数，零差） *)
(* ============================================================ *)
Print Assumptions tspd_g5_partition_condition_req_refl.
Print Assumptions tspd_g5_Z_temp_spec_ht_carry.
Print Assumptions tspd_g5_pa04_partition_condition.
Print Assumptions tspd_g5_bbd_partition_condition.

(* ============================================================ *)
(* 五、提取检验区（判据＝输出 Obj.magic 计 0；输出目录为本池检验区；  *)
(*    若触提取器硬错或记录层转写非零，照池内 63/64/68 先例处置并逐条  *)
(*    如实登记，禁虚报通过）                                        *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspd_g5_partition_Z tspd_g5_partition_condition_req_refl
  tspd_g5_Z_temp_of tspd_g5_Z_temp_spec_ht_carry
  tspd_g5_pa04_partition_condition tspd_g5_bbd_partition_condition.
