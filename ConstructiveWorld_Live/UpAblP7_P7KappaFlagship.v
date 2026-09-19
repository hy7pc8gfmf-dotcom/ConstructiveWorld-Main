(* ============================================================ *)
(* UpAblP7_P7KappaFlagship.v —— 论文7 专项消融战役 PA7-09 席甲腿件           *)
(*   （κ∈(0,1) 前件包 × P7BoundedSoftmaxDeep 旗舰五件·合龙实例化：甲腿半）     *)
(* 零承认件句式：本件为独立伴生真件，全件 Theorem/Corollary 级真 Qed，        *)
(*   零 公理／零 承认件／零 参数声明／零 猜想／零 弃证（禁词中文化，令五交付口径） *)
(*   零经典逻辑引设；语句面全 Set 层（合取用 S01 And=prod、析取用 Or=sum，    *)
(*   零 Prop 泄露）；公理面零新增。                                         *)
(* 甲乙两腿分工（同一假设任务两席接力，写区互斥）：                           *)
(*   甲腿=本席 PA7-09：供给面三件——件a 供给桥自证（real_le=Or(lt,eq)         *)
(*     见证形＋Neq 矛盾消去）、件b δ*<1 姊妹镜像（lo:=1/2 抽象形，a 桥＋      *)
(*     half_twice 加倍还原链＋DecidableOrder 三分派发合成 0<δ*<1 全前件）、   *)
(*     件c 旗舰① p7d_hi_gt_one 的 κ 包合龙实例形（κ 包＋expf 链同槽装配）；  *)
(*   乙腿=姊妹席 PA7-10（UpAblP7_P7FlagshipTail.v，前缀 uaft_）：旗舰        *)
(*     ②③④⑤四件（p7d_one_le_hi_sq／swap_of_sum_eq_list／双向件／           *)
(*     factor_over_hi）。乙腿不装设本件（在飞依赖隔离），本件末尾台账段      *)
(*     留供给面接口清单供主会话合龙时消费。                                  *)
(* 母本（全部只读消费，原树零改）：Paper7Ablation.v、LoHiSqueeze.v、          *)
(*   P7BoundedSoftmaxDeep.v、UpAblP7_Paper7Ablation.v（κ 包源件）、          *)
(*   UpAblP7_LoHiSqueeze.v。                                                *)
(* 消费面（出口签名实测自姊妹席探针打表 2026-09-19 23:46）：                  *)
(*   位1 uabp7_kappa_in01_package（UpAblP7_Paper7Ablation.v:195）——          *)
(*       κ:=1−δ*∈(0,1) 前件包（S01 Set 层 And 合取形，{RI}{DO} 隐参＋        *)
(*       温度/利差/指数族九槽出节形），件c 第一合龙支；                       *)
(*   位2 p7d_hi_gt_one（P7BoundedSoftmaxDeep.v:247）——1<hi 全称八参形，      *)
(*       件c 第二合龙支（hi:=expf(invT·Delta) 实例装配位）；                  *)
(*   位3 half_twice（S01:503）、two_pos（S01:487）、inv_pos_pos（S01:237）、  *)
(*       le_plus_nonneg_r（S01:560）、plus_cancel_l（S01:1018）、            *)
(*       lt_le_iff（S01:160）、lt_dec／le_lt_trans／lt_irrefl／              *)
(*       lt_plus 族类字段——件b 加倍还原链与矛盾消去全链供给。                *)
(* Require 面勘定：按任务令四路齐装（Paper7Ablation＋LoHiSqueeze＋           *)
(*   UpAblP7_Paper7Ablation＋UpAblP7_LoHiSqueeze，另加 P7BoundedSoftmaxDeep  *)
(*   供 p7d 位直呼）；编译 -Q 链=/tmp/pa7_work（工作根放前，防双根同名        *)
(*   歧义）、/tmp/czn14_union_full、/tmp/pa7_side 依需。LoHiSqueeze 双根     *)
(*   同名（并集根与 side 根各一份 .vo，两根 .v 逐字节同）以工作根序取并集根   *)
(*   版；若摘要漂移报装设假设不一致，以实编判词为准录台账（见 T152 坑卡）。    *)
(* 定理面（甲腿四件，全 Qed，前缀 uapk7_ 本件内防撞）：                       *)
(*   件a uapk7_le_neq_to_lt——供给桥自证：构造性实数 le 的见证形即            *)
(*       Or(lt,eq)（S01:160 lt_le_iff 的前提形），桥件把它细化成严格序：      *)
(*       lt 支直取、eq 支与 Neq 前提矛盾消去（Empty_set 消去，构造性真）。    *)
(*   件b-0 uapk7_lt_x_plus_x——严格加倍种子：0<x ⟹ x<x+x（DecidableOrder     *)
(*       lt_dec 三分派发：lt 支直取；eq 支 plus_cancel_l 消零与 0<x 矛盾；    *)
(*       gt 支与 le_plus_nonneg_r 非严格链合流成 x+x<x+x 矛盾）。抽象接口    *)
(*       无 le+≠⟹lt 原语，本件即该缺口的三分构造补件（非平凡实现）。         *)
(*   件b uapk7_delta_star_bounded_half——δ*<1 姊妹镜像（lo:=1/2 形）：        *)
(*       δ*:=half·half（half:=inv_pos (plus one one) two_pos，二分之一       *)
(*       抽象形）；左支 mult_positive 直击；右支以 a 桥＋加倍还原链合成：      *)
(*       half_twice half（ quarter 加倍还原）＋half_twice one（half 加倍      *)
(*       还原）供恒等面，uapk7_lt_x_plus_x 供严格面，half2=one 的反证经      *)
(*       half=2⟹4=1⟹2<1 与 1≤2 合流 2<2 矛盾放电，DO 三分派发收口            *)
(*       （eq 支走 a 桥主消费位，gt 支与加倍链 le 矛盾）。                    *)
(*   件c uapk7_flagship_hi_kappa——旗舰① 合龙实例形：κ∈(0,1) 前件包          *)
(*       （@uabp7_kappa_in01_package 全显喂参）∧ 1<hi                        *)
(*       （p7d_hi_gt_one 同槽直呼）三支合璧，别名面与 AttnDoeblin:547-552    *)
(*       逐字同构（invT/lo/hi/δ*）。                                          *)
(* 红线自审：语句面全 Set 层；公理面零新增；独立伴生件不并入原模块；           *)
(*   全中文零承认件写法（头注与注释同口径）。                                 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import LoHiSqueeze.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_Paper7Ablation.
Require Import UpAblP7_LoHiSqueeze.

(* ################ 段一：供给桥自证（real_le=Or(lt,eq) 细化面） ############## *)
(* 桥件只吃基类槽（零 DO 依赖）：见证 Or 全 Set 层，消去即构造。               *)

Section Uapk7Bridge.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 件a ←任务令甲腿a：lt 支直取、eq 支与 Neq 矛盾消去 *)
Theorem uapk7_le_neq_to_lt :
  forall a b : R, Or (lt a b) (Id a b) -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hwit Hne.
  destruct Hwit as [Hlt | Heq].
  - exact Hlt.
  - elim (Hne Heq).
Qed.

End Uapk7Bridge.

(* ################ 段二：δ*<1 姊妹镜像（lo:=二分之一抽象形） ################# *)
(* 节前导带 DO（件b-0 三分派发与收口派发皆消费 lt_dec）。别名面 half/half2    *)
(* 与 UpAblP7_LoHiSqueeze 件七同构（lo:=inv_pos (plus one one) two_pos）。    *)

Section Uapk7Half.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 件b-0（严格加倍种子）：0<x ⟹ x<x+x。抽象接口无「加正仍严格」原语，         *)
(* 本件以 DO 三分派发构造补位：eq 支 plus_cancel_l 消去首项得 0=x 与 0<x 矛盾；*)
(* gt 支 x+x<x 与 le_plus_nonneg_r 的 x≤x+x 合流成自反矛盾。 *)
Theorem uapk7_lt_x_plus_x :
  forall x : R, lt zero x -> lt x (plus x x).
Proof.
  intros x Hx.
  destruct (lt_dec x (plus x x)) as [Hlt | [Heq | Hgt]].
  - exact Hlt.
  - assert (Hxz : Id (plus x zero) (plus x x))
      by exact (id_trans (plus_zero x) Heq).
    assert (H0x : Id zero x) by exact (plus_cancel_l x zero x Hxz).
    elim (lt_irrefl zero (lt_id_r zero x zero (id_sym H0x) Hx)).
  - assert (Hlexx : le x (plus x x))
      by exact (le_plus_nonneg_r x x (lt_le_iff zero x (inl Hx))).
    elim (lt_irrefl (plus x x)
            (lt_le_trans (plus x x) x (plus x x) Hgt Hlexx)).
Qed.

(* 件b ←任务令甲腿b：0<δ*<1 全前件 @ lo:=1/2（a 桥＋加倍还原链合成） *)
Theorem uapk7_delta_star_bounded_half :
  And (lt zero half2) (lt half2 one).
Proof.
  assert (Hhp : lt zero half) by exact (inv_pos_pos (plus one one) two_pos).
  assert (Hh2p : lt zero half2) by exact (mult_positive half half Hhp Hhp).
  (* 加倍还原链（half_twice S01:503 面）：1/4+1/4=1/2、1/2+1/2=1、1=4·(1/4) *)
  assert (Hq : Id (plus half2 half2) half) by exact (half_twice half).
  assert (Hone : Id (plus half half) one)
    by exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                       (half_twice one)).
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2)))
    by exact (id_trans (id_sym Hone)
                       (id_sym (id_cong (fun x => plus x x) Hq))).
  split.
  - exact Hh2p.
  - (* 严格面：half2<half2+half2（件b-0）＝re Hq⟹ half2<half；half<half+half *)
    (* ＝re Hone⟹half<one；两跳 lt_trans 备反证用。 *)
    assert (Hlt1 : lt half2 (plus half2 half2)) by exact (uapk7_lt_x_plus_x half2 Hh2p).
    assert (Hlt2 : lt half2 half) by exact (lt_id_r half2 (plus half2 half2) half Hq Hlt1).
    assert (Hlt3 : lt half (plus half half)) by exact (uapk7_lt_x_plus_x half Hhp).
    assert (Hlt4 : lt half one) by exact (lt_id_r half (plus half half) one Hone Hlt3).
    assert (Hchain : lt half2 one) by exact (lt_trans half2 half one Hlt2 Hlt4).
    (* Neq 反证：half2=one ⟹ half=2 ⟹ 4=1 ⟹ 2<4 洗成 2<1，与 1≤2 合流 2<2 *)
    assert (Hne : Not (Id half2 one)).
    { intro Heq.
      assert (H2 : Id half (plus one one))
        by exact (id_trans (id_sym Hq) (id_cong (fun w => plus w w) Heq)).
      assert (H41 : Id (plus (plus one one) (plus one one)) one)
        by exact (id_trans (id_cong (fun w => plus w w) (id_sym H2)) Hone).
      assert (H24 : lt (plus one one) (plus (plus one one) (plus one one)))
        by exact (uapk7_lt_x_plus_x (plus one one) two_pos).
      assert (H21 : lt (plus one one) one) by exact (lt_id_r (plus one one) (plus (plus one one) (plus one one)) one H41 H24).
      assert (Hle12 : le one (plus one one))
        by exact (le_plus_nonneg_r one one (lt_le_iff zero one (inl one_pos))).
      exact (lt_irrefl (plus one one)
               (lt_le_trans (plus one one) one (plus one one) H21 Hle12)). }
    (* 非严格面（加倍链 le 版）：1/4≤1/2≤1/4+1/4=1，le_id_r 收口 *)
    assert (Hle0 : le zero half2) by exact (lt_le_iff zero half2 (inl Hh2p)).
    assert (Hle0' : le zero (plus half2 half2))
      by exact (lt_le_iff zero (plus half2 half2)
                  (inl (plus_positive half2 half2 Hh2p Hh2p))).
    assert (Hle : le half2 one)
      by exact (le_id_r half2 (plus (plus half2 half2) (plus half2 half2)) one
                  (id_sym Hone2)
                  (le_trans half2 (plus half2 half2)
                     (plus (plus half2 half2) (plus half2 half2))
                     (le_plus_nonneg_r half2 half2 Hle0)
                     (le_plus_nonneg_r (plus half2 half2) (plus half2 half2) Hle0'))).
    (* DO 三分派发收口：lt 支直取；eq 支经 a 桥与 Neq 矛盾消去（主消费位）； *)
    (* gt 支 one<half2 与加倍链 le half2≤one 合流 one<one 矛盾。 *)
    destruct (lt_dec half2 one) as [Hlt | [Heq | Hgt]].
    + exact Hlt.
    + exact (uapk7_le_neq_to_lt half2 one (inr Heq) Hne).
    + elim (lt_irrefl one (lt_le_trans one half2 one Hgt Hle)).
Qed.

End Uapk7Half.

(* ################ 段三：旗舰① 合龙实例形（κ 包 × p7d_hi_gt_one 同槽装配） ### *)
(* 节前导九槽逐字复刻 AttnDoeblin BoundedSoftmax/UpAblP7_Paper7Ablation 包节； *)
(* 别名面 invT/lo/hi/δ* 与母本 :547-:552 逐字同构。 *)

Section Uapk7Flagship.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* 件c ←任务令甲腿c：κ∈(0,1) 前件包（κ 包合龙支一：@ 全显喂参）∧ 1<hi        *)
(*   （旗舰① p7d_hi_gt_one 实例支：hi:=expf(invT·Delta) 同槽直呼）。 *)
Theorem uapk7_flagship_hi_kappa :
  And (And (lt zero (minus one delta_star)) (lt (minus one delta_star) one))
      (lt one hi).
Proof.
  split.
  - exact (@uabp7_kappa_in01_package RI DO temp temp_pos Delta Delta_pos
             expf expf_pos expf_zero expf_plus expf_mono_lt).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

End Uapk7Flagship.

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uapk7_le_neq_to_lt.
Print Assumptions uapk7_lt_x_plus_x.
Print Assumptions uapk7_delta_star_bounded_half.
Print Assumptions uapk7_flagship_hi_kappa.
