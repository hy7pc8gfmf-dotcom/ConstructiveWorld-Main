(* ============================================================ *)
(* UpAblD1S15_UpReqAlign3.v —— 源模块 UpReqAlign3.v 接口语句的实例供给件   *)
(*   数学使命：Req3AlignCore 节十六项接口/语句的单点典范载体供给。       *)
(* ============================================================ *)
(* 【使命】为源模块 UpReqAlign3.v 之 Section Req3AlignCore 的十六项接口与  *)
(*   语句供给具体实例：R/RIS 载体、S 载体与求和 sumf、sum_ext/sum_add/   *)
(*   sum_linear 三条求和性质、reward/beta/beta_pos/pi_ref/pi_ref_pos/    *)
(*   eta/eta_pos/eta_le_one 八项数据与前提、ZAL_pos（对齐函数正性）、     *)
(*   req2_gibbs_inequality（KL 非负的 plain-le 形态）。三项排除：        *)
(*   sum_pos 已由 UpAblD1S3_sum_pos_UpReqAlign3.v 供给；log 相容性两条    *)
(*   已由 UpAblD1S2_reqlog_UpReqAlign3.v 供给；pi_ref_norm 为基础模块剪除位置 *)
(*   （零消费），均不在本件重复供给。                                    *)
(* 【依赖】CW_ConstructiveWorld_219 / UpReqAlign2（req2_Z_align/         *)
(*   req2_pos_dist/req2_rel_ent 定义件）。不 Require 源模块本体。           *)
(* 【对标】数学原型：策略评估比对中的相对熵非负性（Gibbs 型不等式）       *)
(*   接口之实例化；mathlib/stdlib 无直接构造对应物。                      *)
(* 【实例供给】R:=Real、RIS:=RealEnhancedReal、S:=unit（单点态空间）、    *)
(*   sumf:=fun f => f tt；sum_ext 由单点前提直接应用，sum_add/sum_linear  *)
(*   为单点重合的 req_refl；reward:=零函数；beta:=eta:=one；              *)
(*   beta_pos/eta_pos/pi_ref_pos 取 one_pos 字段；pi_ref:=常函数 one；    *)
(*   eta_le_one:=le_refl one；ZAL_pos 由 uabd1s15_a3_zal_pos 证书供给     *)
(*   （unfold 后为 mult_positive 与 one_pos、exp_neg_pos 三字段之组合）。 *)
(* 【构造性边界注记】req2_gibbs_inequality 的结论为 plain-le 形态的序     *)
(*   谓词，无法由逐 eps 形态消去导出（源模块头注自述「序无消去」）；本件    *)
(*   将其作为全称前提显式承载于供给件 uabd1s15_a3_pack16_supplied，       *)
(*   如实申报为条件承接而非无条件供给。                                   *)
(* 【构造性注记】语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑； *)
(*   文末对两条结论逐一 Print Assumptions，以全部 Closed 为零外部未证     *)
(*   假设的判据。                                                         *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard       *)
(*   包裹限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。   *)
(* 【结构总览】§1 典范载体实例具名（uabd1s15_ren：                       *)
(*   RealInterfaceEnhancedMod.RealEnhancedReal 的具名别名）；             *)
(*   §2 ZAL_pos 供给证书 uabd1s15_a3_zal_pos——对齐函数                   *)
(*   req2_Z_align 在单点实例下化归为 mult one (exp_neg ...) 形，          *)
(*   由 mult_positive 直接推得；§3 接口封装 uabd1s15_a3_pack16            *)
(*   （十六项接口/前提的合取封装，依源模块语句序）；§4 供给件               *)
(*   uabd1s15_a3_pack16_supplied（单点实例一次给定十五项，                *)
(*   req2_gibbs 以全称前提 GIBBS 显式承接）；假设审计区。                 *)
(* ============================================================ *)

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

(* ============ 供给件：单点实例一次给定 15 项＋req2_gibbs 全称前提承接 ==== *)

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
