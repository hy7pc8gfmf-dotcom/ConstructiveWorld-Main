(* ============================================================ *)
(* UpAblP7_UMixSelect.v —— 论文7 专项消融战役席 PA7-15（目标④            *)
(*   UpReqUMixSelect.v 清盘：墙位 lt_plus_compat_lt_le 的消费面重建件）    *)
(*                                                              *)
(* 母本坐标（ConstructiveWorld_Live/UpReqUMixSelect.v，四树零差）：         *)
(*   :67   墙槽 Variable lt_plus_compat_lt_le（唯一声明假设）              *)
(*         → 定谳 W（接口层不可内证；E-STAGING-Firewall-TempEntMono；      *)
(*           本席四消费点复核：omd/κ<1 两腿 le_refl 槽构造性不可升级）      *)
(*         → 本件不做 Id 面内证（诚实 W），走 W7 族出口先例（T143:57）：    *)
(*           实例化可放电替身=req 面（RealEnhancedReal@S07:8566）消费面重建 *)
(*   :559 ums_pow_budget（lt 前件+lt 形 Arch 旗舰）                        *)
(*         → 件六 Id 面墙槽具名冻结消费形（出节首参喂槽直击装配）           *)
(*   req 面镜像坐标：UpReqConcMixSel.v CmkMixSelect 节（ums_ 系逐件镜像，   *)
(*   :79 墙同位 Variable）——cmk_pow_budget 为 ums_pow_budget 同构镜像      *)
(*   ：墙放电供体=real_lt_plus_compat_lt_le@S07:6118（ConcMixSelFeed:198   *)
(*   cms_bs_lpc 同件同喂先例）。                                           *)
(* 节序注记：§A（Id 面）须前置于 Import RealInterfaceEnhancedMod——该模块    *)
(*   裸名遮蔽 Id 面访问器（S01_BaseRing.R 实测 : RealInterface -> Set，    *)
(*   Arguments {RealInterface}；遮蔽下裸 @R RI 误解析，_probe_pa715c 实证   *)
(*   无遮蔽作用域母件同款前导完好），故 Id 面节先落、req 面裸名后启用。      *)
(* 分级申报：N1 库内放电件直连（real_lt_plus_compat_lt_le / real_arch /     *)
(*   mix_scale_eq_const@UpReqMixingTime:140 / real_mult_one@S02:2372 /     *)
(*   RealSetoid.real_lt_id_r@S07:456 / cmk_pow_budget）；N3 实例供给        *)
(*   （κ:=real_const(1/2)，eps:=1/4 逐点 Q 计算正性/上界；TV0:=budget:=one）。*)
(* 新构造（非平凡本体）：uabm_arch_scale——nat-尺度 Arch 放电桥，            *)
(*   real_arch 的 const 形（S07:2772）经 mix_scale_eq_const 双向桥换装为    *)
(*   cmk_scale (S N) one 形，树内无同形独立件（UpReqConcMixSel 头注自报      *)
(*   「本件不消费 real_arch，Arch 前件保持 nat-尺度形」=本桥即其放电缺口）。 *)
(* 依赖清单：CW_ConstructiveWorld_219（伞壳）+ UpReqConcMixSel（req 镜像）   *)
(*   + UpReqMixingTime（scale 桥）+ S01/S04 + UpReqUMixSelect（Id 面旗舰）  *)
(*   ——只读消费，原树零改，在飞席件零接触。                                 *)
(* 红线自审：全中文表述；零 公理/承认件/参数/猜想/弃证字面；全件真证收口；    *)
(*   文尾 Print Assumptions 逐件闭合判读；编译产物只落 /tmp（vo_9.1/Live     *)
(*   只读）；零 git。                                                      *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqConcMixSel.
Require Import UpReqMixingTime.
Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.
Require Import UpReqUMixSelect.

(* ============================================================ *)
(* §A Id 面：目标件旗舰墙槽具名冻结消费形（节前导逐字镜像母件；               *)
(*   本节必须先于 RealInterfaceEnhancedMod 裸名导入，见头注节序注记）        *)
(*   ums_pow_budget 出节首参=墙槽（CZE13 出节实形勘误同源），本件把          *)
(*   「喂槽即得旗舰」的 discharged 形冻结为具名可消费件（T155 槽位直喂       *)
(*   打包先例），UMixSelect 出节签名由此具名定格。                          *)
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
(* §1 半件实例面（κ:=1/2 逐点构造，eps:=1/4 Q 计算收口）                    *)
(* ============================================================ *)

Definition uabm_half : Real := real_const (1#2)%Q.

(* 0 < 1/2：real_lt 证书形拆装（eps:=1/4，const 列逐点常值） *)
Theorem uabm_half_pos : real_lt real_zero uabm_half.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. lia.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 uabm_half n - projT1 real_zero n)).
    change (projT1 uabm_half n) with (1#2)%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. lia.
Qed.

(* 1/2 < 1：同形（eps:=1/4，差 1−1/2=1/2） *)
Theorem uabm_half_lt_one : real_lt uabm_half real_one.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. lia.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 real_one n - projT1 uabm_half n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 uabm_half n) with (1#2)%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. lia.
Qed.

(* 0 < 1（实例件 TV0/budget 前件用） *)
Theorem uabm_one_pos : real_lt real_zero real_one.
Proof.
  unfold real_lt. exists (1#2)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. lia.
  - exists 0%nat. intros n Hn.
    change (QltT (1#2)%Q (projT1 real_one n - projT1 real_zero n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. lia.
Qed.

(* ============================================================ *)
(* §2 墙放电直连（N1）与 nat-尺度 Arch 放电桥（新构造本体）                  *)
(* ============================================================ *)

(* 墙槽 req 面放电件：同 ConcMixSelFeed cms_bs_lpc 面（S07:6118 直连） *)
Definition uabm_wall :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d) :=
  real_lt_plus_compat_lt_le.

(* nat-尺度 Arch 放电桥（树内缺口件）：
   real_arch 出 const 形上界（forall B, 存 n≥2，B < const(n#1)），
   经 mix_scale_eq_const（mix_scale k w == const(k#1)·w）与
   real_mult_one（x·1 == x）换装为 cmk_scale (S N) one 形。
   换形三腿：cmk_scale 与 mix_scale 同折（实例字段零差，转换性同件）、
   const·one 消去、real_lt_id_r 右端等式换形（S07:456）。 *)
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
(* §3 主件：旗舰消费定理的具体实例装配（墙喂放电件 + κ:=1/2）                *)
(*   @cmk_pow_budget Real RealEnhancedReal —— ums_pow_budget req 镜像     *)
(*   旗舰的墙槽喂 uabm_wall（S07:6118 放电），Arch 槽喂 uabm_arch_scale，   *)
(*   得 κ=1/2 的具体步数见证：sigT k, (1/2)^k·1 < 1。全件闭合。             *)
(* ============================================================ *)

Theorem uabm_k_select_half :
  sigT (fun k : nat => lt (mult (cmk_r_pow uabm_half k) real_one) real_one).
Proof.
  exact (@cmk_pow_budget Real RealEnhancedReal uabm_wall
           uabm_half real_one real_one
           uabm_half_pos uabm_half_lt_one uabm_one_pos uabm_one_pos
           uabm_arch_scale).
Defined.

(* ============================================================ *)
(* PA 收尾段（逐件闭合判读留痕）                                            *)
(* ============================================================ *)

Print Assumptions uabm_ums_pow_budget_slot_freeze.
Print Assumptions uabm_half_pos.
Print Assumptions uabm_half_lt_one.
Print Assumptions uabm_one_pos.
Print Assumptions uabm_arch_scale.
Print Assumptions uabm_k_select_half.
