(* UpAblD1S13_AlignIdUnclosed.v —— AiuBackwardKL 节数据供给模块（件②）   *)
(* 使命：AiuBackwardKL 节余量 14 参数位的实例供给（辖区见下）。 *)
(* 构造性注记：零承认语句，纯构造证明，供给级无条件机械供给。 *)
(* 编译配方：coqc -q -Q . "" UpAblD1S13_AlignIdUnclosed.v（9.1 工具链）。 *)
(* 独立模块  *)
(* ·原树零改                                                      *)
(* 辖区：AlignIdUnclosed.v 节 AiuBackwardKL 余量 14 槽：              *)
(*   L74(R)｜L75(RIS)｜L76(S)｜L78(sumf)｜L79-80(sum_ext)｜           *)
(*   L81-83(sum_add)｜L84-86(sum_linear)｜L95(reward)｜L96(beta)｜    *)
(*   L97(beta_pos)｜L98(pi_ref)｜L99(pi_ref_pos)｜L100(eta)｜         *)
(*   L118(ZAL_pos，ZAL 定义 L116-117 δ 内联同体——同族件 Z 位同款)。   *)
(* 排除位（扩位不重立，零触碰）：L87-88 sum_pos 已由                                          *)
(*   UpAblD1S3_sum_pos_AlignIdUnclosed.v 供给；L89-93 log_req_compat 与                       *)
(*   log_inv_exp_neg_req 已由 UpAblD1S2_reqlog_AlignIdUnclosed.v 供给。                       *)
(*   合计 14＋1＋2＝17，模块完备。                                                           *)
(* 形态：供给记录型（参数位语句逐字入件）＋实例供给申报形；与同族件                           *)
(*   同构（无 eta_pos/eta_le_one 位——源文件节头注自述「pi_ref_norm/eta_le_one               *)
(*   未进 discharge 集，节内不设」）                                                         *)
(* 实例供给：R:=Real｜RIS:=RealEnhancedReal（S07:8566 限定名引用）｜    *)
(*   S:=unit｜sumf:=fun f => f tt｜sum_ext＝使用位直取 H tt｜           *)
(*   sum_add/linear＝单点重合 req_refl 一行｜reward:=零函数｜beta:=     *)
(*   eta:=one｜beta_pos/pi_ref_pos:=one_pos 字段直接匹配｜pi_ref:=常函数 one ｜ *)
(*   ZAL_pos＝uabd1s13_aiu_zal_pos 证书（unfold req2_Z_align 后        *)
(*   mult_positive×one_pos×exp_neg_pos 三字段直接匹配）。                  *)
(* 供给级：14 参数位均为数据/接口供给级（无条件机械供给），按模块合并申报。                     *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219／UpReqAlign2    *)
(*   （req2_Z_align 定义件）。零 Require 上游源件。                     *)
(* 纪律：零注册面增量；fail-loud。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.

Definition uabd1s13_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ ZAL_pos 供给证书（ZAL＝req2_Z_align 单点实例，三字段直接匹配） ============ *)

Lemma uabd1s13_aiu_zal_pos :
  lt zero (@req2_Z_align Real uabd1s13_ren unit
            (fun f : unit -> Real => f tt)
            (fun _ : unit => zero)
            one
            (@one_pos Real uabd1s13_ren)
            (fun _ : unit => one)).
Proof.
  exact (@mult_positive Real uabd1s13_ren
           one
           (@exp_neg Real uabd1s13_ren
              (@opp Real uabd1s13_ren
                 (@mult Real uabd1s13_ren
                    (@inv_pos Real uabd1s13_ren one (@one_pos Real uabd1s13_ren))
                    zero)))
           (@one_pos Real uabd1s13_ren)
           (@exp_neg_pos Real uabd1s13_ren
              (@opp Real uabd1s13_ren
                 (@mult Real uabd1s13_ren
                    (@inv_pos Real uabd1s13_ren one (@one_pos Real uabd1s13_ren))
                    zero)))).
Qed.

(* ============ 供给记录型：对照源文件 L74-118（参数位语句逐字入件） ============ *)
(* 参数位序＝供给序；sum_pos(L87)/log 两位(L89-93) 已由同族件供给不入件（见件头排除位）。 *)

Inductive uabd1s13_aiu_pack14 : Type :=
| uabd1s13_aiu_pack14_intro :
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
                  forall (eta : R),
                    forall (ZAL_pos :
                              lt zero (@req2_Z_align R RIS S sumf reward beta
                                         beta_pos pi_ref)),
                      uabd1s13_aiu_pack14.

(* ============ 实例供给：单点实例一次喂定 14 槽 ============ *)

Theorem uabd1s13_aiu_pack14_supplied :
  uabd1s13_aiu_pack14.
Proof.
  exact (uabd1s13_aiu_pack14_intro
           Real uabd1s13_ren
           unit (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, req (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) =>
              @req_refl Real uabd1s13_ren (plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              @req_refl Real uabd1s13_ren (mult a (f tt)))
           (fun _ : unit => zero)
           one
           (@one_pos Real uabd1s13_ren)
           (fun _ : unit => one)
           (fun _ : unit => @one_pos Real uabd1s13_ren)
           one
           uabd1s13_aiu_zal_pos).
Qed.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions uabd1s13_aiu_zal_pos.
Print Assumptions uabd1s13_aiu_pack14_supplied.
