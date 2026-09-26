(* ============================================================ *)
(* UpAblD1S17_UpReqAttnGibbs.v —— 源模块 UpReqAttnGibbs.v 的单点实例供给件 *)
(*   数学使命：热力学和式接口的典范载体实例与指数几何衰减的见证构造。   *)
(* ============================================================ *)
(* 【使命】源模块 UpReqAttnGibbs 的 Section ReqAttnGibbs 以全体接口语句为  *)
(*   节内前提；本件将这些前提在单点态空间上逐一给出见证，并装配为记录    *)
(*   uabd1s17_gib_pack18，共十九项字段：                                *)
(*   R/RIS 实数载体、S 态空间载体、sumf 求和算子、                      *)
(*   sum_ext（逐点相等⟹和相等）、sum_linear（线性）、sum_add（可加性）、  *)
(*   T/T_pos（正温度）、D/D_pos（正分辨率）、energy（能量函数）、         *)
(*   Z_thermo_r_pos（热力学配分和正性）、transition（转移核）、           *)
(*   keep/keep_dec（保持集及其可判定前提）、sum_le（和的单调性）、        *)
(*   abs_sum_le_r（绝对值不等式）、evicted_partition_r_pos（逐出分区正    *)
(*   性）、exp_neg_geo_break（指数几何衰减：∀d>0, ∀eps>0, ∃N,           *)
(*   exp_neg(N·(1+1)·d) ≤ eps）。                                        *)
(* 【实例选择】R:=Real；RIS:=RealEnhancedReal（具名为 uabd1s17_ren，      *)
(*   限定名引用 RealInterfaceEnhancedMod.RealEnhancedReal）；             *)
(*   S:=unit（单点态空间）；sumf:=fun f => f tt；                        *)
(*   sum_ext/sum_le 由单点上的逐点前提直接给出（对 tt 求值即得）；        *)
(*   sum_linear/sum_add 由 req_refl 直接给出；                           *)
(*   T:=D:=one，正性由 one_pos 给出；energy:=零函数；                     *)
(*   transition:=零二元函数；keep:=unit（恒非空）；keep_dec:=inl tt       *)
(*   （保持性的直接见证）；Z_thermo_r_pos/evicted_partition_r_pos 由       *)
(*   exp_neg_pos 给出——节内定义 Z_thermo_r/evicted_partition_r 经        *)
(*   δ+iota 归约后与本实例的定义体逐字同体；exp_neg_geo_break 由          *)
(*   uabd1s17_gib_geobreak 供给（转引库中引理 klcx_exp_neg_geo_break_     *)
(*   iface）。                                                           *)
(* 【依赖】CW_ConstructiveWorld_219／UpReqCauchy（req_r_pow 即出节后的    *)
(*   全局同名引理）／G07_KLWall（klcx_exp_neg_geo_break_iface 供给源）。   *)
(*   不 Require 源模块 UpReqAttnGibbs.v 本体。                              *)
(* 【对标】数学原型：单点态空间上热力学配分和与逐出分区的正性、指数尾     *)
(*   衰减的构造性见证；mathlib/stdlib 无直接构造对应物。                  *)
(* 【构造性注记】语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑。 *)
(*   keep_dec 的前提为排除律 ∀s:S, keep s ∨ ¬ keep s，在单点态空间上      *)
(*   以 inl tt 显式见证。文末对两条主结论逐一 Print Assumptions，         *)
(*   以全部 Closed 为零外部未证假设的判据。                               *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹   *)
(*   限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。       *)
(* 【结构总览】§1 典范载体实例：uabd1s17_ren 的具名定义。                 *)
(*   §2 接口封装记录 uabd1s17_gib_pack18：十九项字段的类型对应源模块        *)
(*   Section ReqAttnGibbs 的节内声明（逐字相同）；字段序＝源模块声明序。     *)
(*   sum_pos、req_lt_plus_compat_lt_le_h、detailed_balance_r 三项节内     *)
(*   语句不在本记录中，其供给分别由 UpAblD1S3_sum_pos_UpReqAttnGibbs、    *)
(*   UpAblD1_fa53_lpc_broadcast、UpAblD1S3_fep_UpReqAttnGibbs 承担。      *)
(*   Z_thermo_r/evicted_partition_r 系源模块节内 Definition，本记录相应     *)
(*   字段按其定义体经 δ 归约后逐字展开（与源模块定义可互换）。              *)
(*   §3 几何衰减供给：uabd1s17_gib_geobreak——由库中引理                   *)
(*   klcx_exp_neg_geo_break_iface 直接推得。记录字段 req_r_pow 取         *)
(*   UpReqCauchy 出节后的全局同名引理（与源模块节内同名同源）；             *)
(*   以下标识符在定义展开后同体，可互换使用：                             *)
(*   exp_neg≡real_exp_neg／req_r_pow≡klcx_r_pow／                         *)
(*   plus one one≡real_plus real_one real_one。                           *)
(*   §4 供给定理 uabd1s17_gib_pack18_supplied：以 §1 载体实例与 §3 供给    *)
(*   一次性给出记录 uabd1s17_gib_pack18 全部字段的见证。                  *)
(*   §5 假设审计区：对 uabd1s17_gib_geobreak 与                            *)
(*   uabd1s17_gib_pack18_supplied 逐一 Print Assumptions。                 *)
(* 【边界注记】本件为源模块接口的载体实例供给件：一切数学内容由源模块节内     *)
(*   前提与所引库件承载，本件的贡献在于给出全部前提的具体见证；           *)
(*   单点态空间上的和式等式与不等式均退化为对唯一元素 tt 的逐点判断。      *)
(*   载体的一般化（任意态空间上的和式）属后续工作。                       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqCauchy.
Require Import G07_KLWall.
Import RealInterfaceEnhancedMod.

(* ============ 典范载体实例具名 ============ *)

Definition uabd1s17_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ 接口封装记录：对应源模块 Section ReqAttnGibbs 的节内声明 ============ *)
(* 字段序＝源模块声明序；sum_pos、req_lt_plus_compat_lt_le_h、              *)
(* detailed_balance_r 三项不在本记录中（供给由上述专件承担）。            *)
(* Z_thermo_r/evicted_partition_r 系源模块节内 Definition，本记录相应       *)
(* 字段按其定义体经 δ 归约后逐字展开（与源模块定义可互换）。                *)

Inductive uabd1s17_gib_pack18 : Type :=
| uabd1s17_gib_pack18_intro :
    forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (sumf : (S -> R) -> R)
           (sum_ext : forall f g : S -> R,
                      (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
           (sum_linear : forall (a : R) (f : S -> R),
                         req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
           (sum_add : forall f g : S -> R,
                      req (sumf (fun s : S => plus (f s) (g s)))
                          (plus (sumf f) (sumf g)))
           (T : R) (T_pos : lt zero T)
           (D : R) (D_pos : lt zero D) (energy : S -> R)
           (Z_thermo_r_pos :
              lt zero (sumf (fun s : S =>
                        exp_neg (mult (inv_pos D D_pos) (energy s)))))
           (transition : S -> S -> R) (keep : S -> Set)
           (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
           (sum_le : forall f g : S -> R,
                     (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
           (abs_sum_le_r : forall f : S -> R,
                           le (abs (sumf f)) (sumf (fun s : S => abs (f s))))
           (evicted_partition_r_pos :
              lt zero (sumf (fun s : S =>
                        if keep_dec s
                        then exp_neg (mult (inv_pos D D_pos) (energy s))
                        else zero)))
           (exp_neg_geo_break :
              forall d : R, lt zero d ->
                forall eps : R, lt zero eps ->
                  sigT (fun N : nat =>
                    le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps)),
      uabd1s17_gib_pack18.

(* ============ exp_neg_geo_break 的供给（转引库中引理） ============ *)
(* 记录字段 req_r_pow 取 UpReqCauchy 出节后的全局同名引理（与源模块         *)
(*   Section 内同名同源）。以下标识符在定义展开后同体，可互换使用：       *)
(*   exp_neg≡real_exp_neg／req_r_pow≡klcx_r_pow／plus one one≡          *)
(*   real_plus real_one real_one。                                       *)

Theorem uabd1s17_gib_geobreak :
  forall d : Real, lt zero d ->
    forall eps : Real, lt zero eps ->
      sigT (fun N : nat =>
        le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps).
Proof.
  intros d Hd eps Heps.
  exact (klcx_exp_neg_geo_break_iface d eps Hd Heps).
Qed.

(* ============ 供给定理：以单点实例给出记录的全部字段 ============ *)

Theorem uabd1s17_gib_pack18_supplied : uabd1s17_gib_pack18.
Proof.
  exact (uabd1s17_gib_pack18_intro
           Real uabd1s17_ren
           unit (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, req (f s) (g s)) => H tt)
           (fun (a : Real) (f : unit -> Real) =>
              @req_refl Real uabd1s17_ren (mult a (f tt)))
           (fun (f g : unit -> Real) =>
              @req_refl Real uabd1s17_ren (plus (f tt) (g tt)))
           one (@one_pos Real uabd1s17_ren)
           one (@one_pos Real uabd1s17_ren)
           (fun _ : unit => zero)
           (@exp_neg_pos Real uabd1s17_ren
              (mult (inv_pos one (@one_pos Real uabd1s17_ren)) zero))
           (fun (_ _ : unit) => zero)
           (fun _ : unit => unit)
           (fun _ : unit => @inl unit (Not unit) tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, le (f s) (g s)) => H tt)
           (fun f : unit -> Real =>
              @le_refl Real uabd1s17_ren (abs (f tt)))
           (@exp_neg_pos Real uabd1s17_ren
              (mult (inv_pos one (@one_pos Real uabd1s17_ren)) zero))
           uabd1s17_gib_geobreak).
Qed.

(* ============ 假设审计 ============ *)

Print Assumptions uabd1s17_gib_geobreak.
Print Assumptions uabd1s17_gib_pack18_supplied.
