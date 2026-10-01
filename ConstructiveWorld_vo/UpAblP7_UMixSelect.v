(* ============================================================ *)
(* 近一击位甄别处置件：原件全文逐字保留，仅将三位定理（各二处）证明体内的常数      *)
(*   Q 比较 lia 位替换为定义性显式构造（eq_refl）：uabm_half_pos/uabm_half_lt_one/  *)
(*   uabm_one_pos；另涉 uabm_k_select_half（原 L172）/uabm_ums_pow_budget_slot_     *)
(*   freeze（原 L69）。语句面与引用面零改动，零新增 Require，纯构造性闭合。         *)
(* ============================================================ *)
(* UpAblP7_UMixSelect.v —— UpReqUMixSelect.v 的使用面重建件：ums_pow_budget 的      *)
(*   具名使用形与 κ:=1/2 具体实例。使命：基件 UpReqUMixSelect.v 以                   *)
(*   lt_plus_compat_lt_le（lt＋le 相加保序）为唯一声明假设（接口层不可内证；omd 与    *)
(*   κ<1 两处使用点的 le_refl 参数位构造性不可升级消去）；本件把其出节主定理          *)
(*   ums_pow_budget 的「代入该前提即得结论」形固定为具名定理                          *)
(*   uabm_ums_pow_budget_slot_freeze，并在 req 面（RealEnhancedReal，S07）给          *)
(*   κ:=real_const(1/2)、TV0:=budget:=one 的具体实例 uabm_k_select_half：见证存在 k    *)
(*   使 (1/2)^k·1 < 1。使用面（上游出口真名）：ums_pow_budget（UpReqUMixSelect）；      *)
(*   cmk_pow_budget/cmk_scale/cmk_r_pow（UpReqConcMixSel 的 CmkMixSelect 节）；        *)
(*   real_lt_plus_compat_lt_le（S07）；real_arch（nat-尺度 Arch 上界）、                *)
(*   mix_scale_eq_const（UpReqMixingTime）、real_mult_one（S02）、                     *)
(*   RealSetoid.real_lt_id_r（S07）。新构造 uabm_arch_scale——nat-尺度 Arch 桥接引理     *)
(*   （树内此前缺失）：real_arch 的 const 形上界（forall B，存在 n≥2，B < const(n#1)）   *)
(*   经 mix_scale_eq_const 与 real_mult_one 转换为 cmk_scale (S N) one 形。节序注记     *)
(*   （技术性）：§A（Id 面）须前置于 Import RealInterfaceEnhancedMod——该模块裸名遮蔽    *)
(*   Id 面访问器（S01_BaseRing.R：Arguments {RealInterface}；遮蔽下裸 @R RI 误解析），   *)
(*   故 Id 面节先落、req 面裸名后启用。依赖清单：CW_ConstructiveWorld_219＋             *)
(*   UpReqConcMixSel＋UpReqMixingTime＋S01_BaseRing＋S04_RealExpLogConv＋               *)
(*   UpReqUMixSelect——只读引用。对标：mathlib pow_lt_one 的倒数衰减步数见证之构造性      *)
(*   对应。构造性注记：全件真证、零承认（声明前提仅经基件出节形引入）；语句面全 Set      *)
(*   层。编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。                     *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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
Require Import UpReqConcMixSel.
Require Import UpReqMixingTime.
Require Import UpReqUMixSelect.

(* ============================================================ *)
(* §A Id 面：主定理声明前提的具名使用形（节前导与基件一致；                    *)
(*   本节必须先于 RealInterfaceEnhancedMod 裸名导入，见头部节序注记）        *)
(*   ums_pow_budget 出节首参即声明前提 lt_plus_compat_lt_le；本件把          *)
(*   「代入该前提即得主定理结论」的出节形固定为具名可用定理                  *)
(*   uabm_ums_pow_budget_slot_freeze，供直接调用。                          *)
(* ============================================================ *)

Section UabmIface.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt   := @lt RI.
Let le   := @le RI.

Theorem uabm_ums_pow_budget_slot_freeze :
  (forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
  forall kappa TV0 budget : R,
    lt zero kappa -> lt kappa one -> lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros Hwall.
  exact (ums_pow_budget Hwall).
Defined.

End UabmIface.

(* 自此启用 req 面裸名（Real 层语句面用）： *)
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 κ:=1/2 实例面（逐点构造，eps:=1/4 Q 计算闭合）                        *)
(* ============================================================ *)

Definition uabm_half : Real := real_const (1#2)%Q.

(* 0 < 1/2：real_lt 见证构造（eps:=1/4，const 列逐点常值） *)
Theorem uabm_half_pos : real_lt real_zero uabm_half.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 uabm_half n - projT1 real_zero n)).
    change (projT1 uabm_half n) with (1#2)%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Qed.

(* 1/2 < 1：同形（eps:=1/4，差 1−1/2=1/2） *)
Theorem uabm_half_lt_one : real_lt uabm_half real_one.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 real_one n - projT1 uabm_half n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 uabm_half n) with (1#2)%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Qed.

(* 0 < 1（实例件 TV0/budget 前件用） *)
Theorem uabm_one_pos : real_lt real_zero real_one.
Proof.
  unfold real_lt. exists (1#2)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#2)%Q (projT1 real_one n - projT1 real_zero n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Qed.

(* ============================================================ *)
(* §2 声明前提的 req 面实例与 nat-尺度 Arch 桥接引理（新构造）               *)
(* ============================================================ *)

(* 声明前提 lt_plus_compat_lt_le 的 req 面实例：real_lt_plus_compat_lt_le（与 ConcMixSelFeed 的 cms_bs_lpc 同件） *)
Definition uabm_wall :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d) :=
  real_lt_plus_compat_lt_le.

(* uabm_arch_scale（树内此前缺失的桥接引理）：
   real_arch 给出 const 形上界（forall B，存在 n≥2，B < const(n#1)），
   经 mix_scale_eq_const（mix_scale k w == const(k#1)·w）与
   real_mult_one（x·1 == x）转换为 cmk_scale (S N) one 形。
   三步：cmk_scale 与 mix_scale 同一折叠（实例字段相同，转换性等价）、
   const·one 消去、RealSetoid.real_lt_id_r 右端等式改写。 *)
Lemma uabm_arch_scale : forall x : Real,
  lt zero x ->
  sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) real_one)).
Proof.
  intros x Hx.
  destruct (real_arch x) as [n [H2n Hlt]].
  destruct n as [| m].
  - exfalso. inversion H2n.
  - exists m.
    apply (RealSetoid.real_lt_id_r x
             (real_const (Z.of_nat (Datatypes.S m) # 1))
             (cmk_scale (Datatypes.S m) real_one)).
    + apply real_eq_sym.
      apply (real_eq_trans
               (cmk_scale (Datatypes.S m) real_one)
               (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) real_one)
               (real_const (Z.of_nat (Datatypes.S m) # 1))).
      * exact (mix_scale_eq_const (Datatypes.S m) real_one).
      * exact (real_mult_one (real_const (Z.of_nat (Datatypes.S m) # 1))).
    + exact Hlt.
Qed.

(* ============================================================ *)
(* §3 主件：主定理的具体实例装配（声明前提取 uabm_wall + κ:=1/2）      *)
(*   @cmk_pow_budget Real RealEnhancedReal —— ums_pow_budget 的 req 面副本，  *)
(*   声明前提位代入 uabm_wall，Arch 前提位代入 uabm_arch_scale，                 *)
(*   得 κ=1/2 的具体步数见证：sigT k, (1/2)^k·1 < 1。全件闭合。             *)
(* ============================================================ *)

Theorem uabm_k_select_half :
  sigT (fun k : nat => lt (mult (cmk_r_pow uabm_half k) real_one) real_one).
Proof.
  exact (@cmk_pow_budget Real RealEnhancedReal uabm_wall           uabm_half real_one real_one           uabm_half_pos uabm_half_lt_one uabm_one_pos uabm_one_pos           uabm_arch_scale).
Defined.

(* ============================================================ *)
(* 收尾段：逐件 Print Assumptions 核验零承认                                *)
(* ============================================================ *)

Print Assumptions uabm_ums_pow_budget_slot_freeze.
Print Assumptions uabm_half_pos.
Print Assumptions uabm_half_lt_one.
Print Assumptions uabm_one_pos.
Print Assumptions uabm_arch_scale.
Print Assumptions uabm_k_select_half.
