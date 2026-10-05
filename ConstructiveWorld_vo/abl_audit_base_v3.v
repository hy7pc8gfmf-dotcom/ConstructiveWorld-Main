(* ==========================================================================)
   abl_audit_base_v3.v — S02 基座八顶层定理直审卷第三件（余七位）
   使命：S02_CauchyComplete 顶层 Theorem 恰 8 条，v1 已直审 real_cauchy_complete
      （1/8），本件审余 7 位：四主位 real_lim_unique／real_lim_plus／real_lim_scal／
      real_lim_mult 各出一条 Set 层轻量实例定理（abc_ 前缀；以具体实例化／双定理
      链行使主定理本体，非单纯转发）；三负型位 real_square_not_negative／
      step_not_unif_pointwise／step_not_lim_zero 语句面为 Not（Prop 面），按零
      Prop 语句红线不出行使件、以尾舱 qualified 直审覆盖（如实登记，非缺口）。
      尾舱 11 条 Print Assumptions＝余 7 位直审（8/8 总账与 v1 汇合）＋本件四
      实例自审。
   依赖清单：S01_BaseRing、S02_CauchyComplete（-Q 预编译树 vo_local_world_
      unified_0930 只读引用）＋Stdlib QArith（2%Q 记号面）＋Stdlib Extraction
      （尾段 Separate Extraction）。
   对标行：审计直审卷族体例（v1 起五字段头注）；S02 顶层 Theorem 坐标＝
      :812/:1035/:1545/:1647/:3084/:3365/:3425/:3855。
   构造性注记：全件 Qed 闭合、零承认词面、无经典逻辑；语句面全 Set 层
      （real_lim／real_eq／real_lt 皆 S02 : Set 定义，sigT 实现），零 Prop 泄露；
      证明体全 exact 显式项直交，无 tactic 猜测面；real_eq 为 Set 型逐 eps sigT
      面（S02:399），unique 实例结论落在 Set 层；S02 常量全为无类参裸顶层形
      （Section+Context 钉类参的已知病形于本件不适用——本件语句不触
      RealInterface 面参数）。
   编译配方（独占编译池 audit_base_v3/，池内并发≤1，单件无池内链序）：source
      Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 &&
      nice -19 rocq c -native-compiler no -Q vo_local_world_unified_0930 ""
      abl_audit_base_v3.v；验证＝EXIT=0＋日志零真错＋逐条 Print Assumptions
      全 Closed＋.vo 新于 .v，rocq check 复核。
   查重登记：顶层名 4 枚全 abc_ 新前缀（lim_square_via_plus／lim_twice_via_scal／
      lim_square_via_mult／lim_unique_double），与 v1/v2 及库内既有顶层名零撞
      零别名转发；11 条 Print Assumptions 只读直审，宿主零字节不动。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith.

(* ============================================================ *)
(* §1 实例语句舱·四主位轻量真行使（每条主定理各一，全 Set 层）     *)
(*    各实例均为新语句：以具体实例化／双定理链行使主定理本体，     *)
(*    非单纯转发。                                                 *)
(* ============================================================ *)

(* 主位 plus：倍列收敛。real_lim_plus 以 u:=v:=u、l1:=l2:=l 实例化，   *)
(*   倍列 (fun n => u n + u n) 收敛到 l+l——具体倍增实例，非泛转发。 *)
Theorem abc_lim_square_via_plus :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n))
      (S02_CauchyComplete.real_plus l l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_plus u u l l H H).
Qed.

(* 主位 scal：二倍数乘列收敛。real_lim_scal 以 c:=2%Q 具体实例化，    *)
(*   数乘列收敛到 2·l——_scal 内部 eps/(2(|c|+1)) 机器在具体尺度行使。 *)
Theorem abc_lim_twice_via_scal :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat =>
         S02_CauchyComplete.real_mult (S02_CauchyComplete.real_const 2%Q) (u n))
      (S02_CauchyComplete.real_mult (S02_CauchyComplete.real_const 2%Q) l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_scal u l 2%Q H).
Qed.

(* 主位 mult：平方列收敛。real_lim_mult 以 u:=v:=u、l1:=l2:=l 实例化， *)
(*   平方列收敛到 l·l——具体平方实例。                                *)
Theorem abc_lim_square_via_mult :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_mult (u n) (u n))
      (S02_CauchyComplete.real_mult l l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_mult u u l l H H).
Qed.

(* 主位 unique：双定理链实例。倍列之极限唯一且等于原极限之倍——        *)
(*   real_lim_plus 先给出倍列的规范极限，real_lim_unique 随即判同；    *)
(*   两主位在同一定理中成链行使，结论 real_eq 落 Set 层。             *)
Theorem abc_lim_unique_double :
  forall (u : nat -> S02_CauchyComplete.Real)
         (l1 l2 : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n)) l1 ->
    S02_CauchyComplete.real_lim u l2 ->
    S02_CauchyComplete.real_eq l1 (S02_CauchyComplete.real_plus l2 l2).
Proof.
  intros u l1 l2 Hd H.
  exact (S02_CauchyComplete.real_lim_unique
           (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n))
           l1 (S02_CauchyComplete.real_plus l2 l2) Hd
           (S02_CauchyComplete.real_lim_plus u u l2 l2 H H)).
Qed.

(* ============================================================ *)
(* §2 尾舱·假设审计（余 7 位跨件 qualified 直审＋本件四实例自审）   *)
(*    判读判据：11 条全输出 Closed under the global context。        *)
(*    前七条=S02 余 7 位直审（与本件头注总账一一对应：四主位在前、   *)
(*    三负型位在后；8/8 总账与 v1 之 real_cauchy_complete 汇合）；    *)
(*    后四条=本件实例自审（PA≥1 下限之上）。                        *)
(* ============================================================ *)

Print Assumptions S02_CauchyComplete.real_lim_unique.
Print Assumptions S02_CauchyComplete.real_lim_plus.
Print Assumptions S02_CauchyComplete.real_lim_scal.
Print Assumptions S02_CauchyComplete.real_lim_mult.
Print Assumptions S02_CauchyComplete.real_square_not_negative.
Print Assumptions S02_CauchyComplete.step_not_unif_pointwise.
Print Assumptions S02_CauchyComplete.step_not_lim_zero.
Print Assumptions abc_lim_square_via_plus.
Print Assumptions abc_lim_twice_via_scal.
Print Assumptions abc_lim_square_via_mult.
Print Assumptions abc_lim_unique_double.

(* ============================================================ *)
(* §3 出口舱：实例定理兼任提取端口（提取面零魔数）。               *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abc_lim_square_via_plus abc_lim_twice_via_scal
                    abc_lim_square_via_mult abc_lim_unique_double.
