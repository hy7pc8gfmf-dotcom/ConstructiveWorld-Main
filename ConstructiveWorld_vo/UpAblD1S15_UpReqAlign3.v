(* ==========================================================================)
   UpAblD1S15_UpReqAlign3.v — UpReqAlign3 接口十六项的单点典范载体供给引理
   使命: R/RIS 载体、单点求和、sum_ext/add/linear、reward/beta/pi_ref 等八项数据与前提、ZAL_pos 正性证书、req2_gibbs_inequality 以全称前提显式接续的供给引理；不 Require 源模块本体。
   依赖: CW_ConstructiveWorld_219、UpReqAlign2（req2_Z_align/req2_pos_dist/req2_rel_ent 定义件）。
   对标: 策略评估比对中的相对熵非负性（Gibbs 型不等式）接口之实例化。
   构造性: 语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑；文末对两条结论逐一 Print Assumptions 全 Closed。
   编译配方: Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹限载；输出一律 -o 临时目录，树内 .vo 不重写。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.

(* ============ 典范载体实例具名 ============ *)

Definition uabd1s15_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ ZAL_pos 供给证书（三字段直接推得） ===== *)
(* 源模块 ZAL := @req2_Z_align R RIS S sumf reward beta beta_pos pi_ref；  *)
(*   单点供给下逐字化为 mult one (exp_neg (opp (mult (inv_pos one        *)
(*   one_pos) zero)))——由 mult_positive 直接推得。 *)

Lemma uabd1s15_a3_zal_pos :
  lt zero (@req2_Z_align Real uabd1s15_ren unit
            (fun f : unit -> Real => f tt)
            (fun _ : unit => zero)
            one
            (@one_pos Real uabd1s15_ren)
            (fun _ : unit => one)).
Proof.
  exact (@mult_positive Real uabd1s15_ren
           one
           (@exp_neg Real uabd1s15_ren
              (@opp Real uabd1s15_ren
                 (@mult Real uabd1s15_ren
                    (@inv_pos Real uabd1s15_ren one (@one_pos Real uabd1s15_ren))
                    zero)))
           (@one_pos Real uabd1s15_ren)
           (@exp_neg_pos Real uabd1s15_ren
              (@opp Real uabd1s15_ren
                 (@mult Real uabd1s15_ren
                    (@inv_pos Real uabd1s15_ren one (@one_pos Real uabd1s15_ren))
                    zero)))).
Qed.

(* ============ 接口封装：对应对源模块节级接口语句（依源模块语句序） ====== *)
(* 语句序＝源模块语句序；sum_pos、log 相容性两条已由                     *)
(* UpAblD1S3_sum_pos_UpReqAlign3.v 与 UpAblD1S2_reqlog_UpReqAlign3.v 供给，pi_ref_norm 为基础模块剪除位置，均不入本封装。 *)

Inductive uabd1s15_a3_pack16 : Type :=
| uabd1s15_a3_pack16_intro :
    forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
      forall (S : Set) (sumf : (S -> R) -> R),
        forall (sum_ext : forall f g : S -> R,
                   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)),
          forall (sum_add : forall f g : S -> R,
                     req (sumf (fun s : S => plus (f s) (g s)))
                         (plus (sumf f) (sumf g))),
            forall (sum_linear : forall (a : R) (f : S -> R),
                       req (sumf (fun s : S => mult a (f s)))
                           (mult a (sumf f))),
              forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta),
                forall (pi_ref : S -> R)
                       (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
                  forall (eta : R) (eta_pos : lt zero eta)
                         (eta_le_one : le eta one),
                    forall (ZAL_pos : lt zero (@req2_Z_align R RIS S sumf
                                                 reward beta beta_pos pi_ref)),
                      forall (req2_gibbs : forall (p q : S -> R)
                                                 (Hp : @req2_pos_dist R RIS S p)
                                                 (Hq : @req2_pos_dist R RIS S q),
                                        le zero (@req2_rel_ent R RIS S sumf
                                                   p q Hp Hq)),
                        uabd1s15_a3_pack16.

(* ============ 供给引理：单点实例一次给定 15 项＋req2_gibbs 全称前提接续 ==== *)

Theorem uabd1s15_a3_pack16_supplied :
  forall (GIBBS : forall (p q : unit -> Real)
                    (Hp : @req2_pos_dist Real uabd1s15_ren unit p)
                    (Hq : @req2_pos_dist Real uabd1s15_ren unit q),
              le zero (@req2_rel_ent Real uabd1s15_ren unit
                        (fun f : unit -> Real => f tt) p q Hp Hq)),
    uabd1s15_a3_pack16.
Proof.
  intro GIBBS.
  exact (uabd1s15_a3_pack16_intro
           Real uabd1s15_ren
           unit (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, req (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) =>
              @req_refl Real uabd1s15_ren (plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              @req_refl Real uabd1s15_ren (mult a (f tt)))
           (fun _ : unit => zero)
           one
           (@one_pos Real uabd1s15_ren)
           (fun _ : unit => one)
           (fun _ : unit => @one_pos Real uabd1s15_ren)
           one
           (@one_pos Real uabd1s15_ren)
           (@le_refl Real uabd1s15_ren one)
           uabd1s15_a3_zal_pos
           GIBBS).
Qed.

(* ============ 假设审计（Print Assumptions 全 Closed 为判据） ============ *)

Print Assumptions uabd1s15_a3_zal_pos.
Print Assumptions uabd1s15_a3_pack16_supplied.
