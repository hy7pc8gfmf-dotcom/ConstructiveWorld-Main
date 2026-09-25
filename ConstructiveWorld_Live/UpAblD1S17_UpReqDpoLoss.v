(* ============================================================ *)
(* UpAblD1S17_UpReqDpoLoss.v —— 源模块 UpReqDpoLoss.v 的单点实例依赖模块 *)
(*   数学使命：直接偏好优化损失接口的典范载体实例与对齐正性证书。   *)
(* ============================================================ *)
(* 【使命】源模块 UpReqDpoLoss 的 Section ReqDpoLossCore 以全体接口语句为 *)
(*   节内前提；本件将这些前提在单点态空间上逐一给出见证，并装配为记录    *)
(*   uabd1s17_dpo_pack13，共十三项字段：                                *)
(*   R/RIS 实数载体、S 态空间载体、sumf 求和算子、reward（奖励函数）、    *)
(*   beta/beta_pos（逆温度及其正性）、                                   *)
(*   pi_ref/pi_ref_pos（参考策略及其逐点正性）、Z_align_pos（对齐配分    *)
(*   和正性）、Preference（偏好类型）、pref_win/pref_lose（胜负偏好      *)
(*   映射）、pref_dataset（偏好数据集）。                                *)
(* 【实例选择】R:=Real；RIS:=RealEnhancedReal（具名 uabd1s17_ren，        *)
(*   限定名引用 RealInterfaceEnhancedMod.RealEnhancedReal）；             *)
(*   S:=unit（单点态空间）；sumf:=fun f => f tt；reward:=零函数；         *)
(*   beta:=one，正性由 one_pos 给出；pi_ref:=常函数 one，逐点正性由       *)
(*   one_pos 全称实例给出；Z_align_pos:=uabd1s17_dpo_zap_pos；            *)
(*   Preference:=unit；pref_win/pref_lose:=fun _ => tt；                  *)
(*   pref_dataset:=cons tt nil（单元素数据集）。                          *)
(* 【依赖】CW_ConstructiveWorld_219／UpReqAlign（Z_align_req 定义件）；    *)
(*   不 Require 源模块 UpReqDpoLoss.v 本体。mathlib/stdlib 无直接对应物。   *)
(* 【构造性注记】语句面全 Set 层；全件 Qed 闭合、零承认词面、无经典逻辑；  *)
(*   文末两条主结论逐一 Print Assumptions，以全部 Closed 为零外部未证判据。 *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹   *)
(*   限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。       *)
(* 【结构总览】§1 典范载体实例：uabd1s17_ren 的具名定义。§2 对齐正性证书  *)
(*   uabd1s17_dpo_zap_pos：Z_align_req 展开后为逐点和                      *)
(*   Σ_s pi_ref(s)·exp_neg(−inv_pos(beta)·reward(s))，单点实例上化为一项， *)
(*   正性由 mult_positive 连同 one_pos 与 exp_neg_pos 直接给出。§3 接口    *)
(*   封装记录 uabd1s17_dpo_pack13：十三项字段对应源模块 Section ReqDpoLossCore *)
(*   的节内声明（逐字相同）；rdl_log_req_compat 与 rdl_log_inv_exp_neg_req *)
(*   两项不在本记录中（供给见 UpAblD1S2_reqlog_UpReqDpoLoss）。§4 供给定理 *)
(*   uabd1s17_dpo_pack13_supplied 一次性给出全部字段；§5 假设审计区。      *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============ 典范载体实例具名 ============ *)

Definition uabd1s17_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ Z_align_pos 供给证书 ============ *)
(* 实例代入：S:=unit、sumf:=单点求和、reward:=零函数、beta:=one、         *)
(*   pi_ref:=常函数 one；Z_align_req 在此实例下经 δ/ι 归约为乘积          *)
(*   one·exp_neg(−inv_pos(one)·零)，两端正性各由 one_pos 与 exp_neg_pos 给出。 *)

Lemma uabd1s17_dpo_zap_pos :
  lt zero (@Z_align_req Real uabd1s17_ren unit
            (fun f : unit -> Real => f tt)
            (fun _ : unit => zero)
            one
            (@one_pos Real uabd1s17_ren)
            (fun _ : unit => one)).
Proof.
  exact (@mult_positive Real uabd1s17_ren
           one
           (@exp_neg Real uabd1s17_ren
              (@opp Real uabd1s17_ren
                 (@mult Real uabd1s17_ren
                    (@inv_pos Real uabd1s17_ren one (@one_pos Real uabd1s17_ren))
                    zero)))
           (@one_pos Real uabd1s17_ren)
           (@exp_neg_pos Real uabd1s17_ren
              (@opp Real uabd1s17_ren
                 (@mult Real uabd1s17_ren
                    (@inv_pos Real uabd1s17_ren one (@one_pos Real uabd1s17_ren))
                    zero)))).
Qed.

(* ============ 接口封装记录：对应源模块 Section ReqDpoLossCore 的节内声明 ============ *)
(* 字段序＝源模块声明序；两个 log 相容性语句不在本记录中（件头已注明）。    *)

Inductive uabd1s17_dpo_pack13 : Type :=
| uabd1s17_dpo_pack13_intro :
    forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
           (S : Set) (sumf : (S -> R) -> R)
           (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (Z_align_pos :
              lt zero (@Z_align_req R RIS S sumf reward beta beta_pos pi_ref))
           (Preference : Set)
           (pref_win : Preference -> S) (pref_lose : Preference -> S)
           (pref_dataset : list Preference),
      uabd1s17_dpo_pack13.

(* ============ 供给定理：以单点实例给出记录的全部字段 ============ *)

Theorem uabd1s17_dpo_pack13_supplied : uabd1s17_dpo_pack13.
Proof.
  exact (uabd1s17_dpo_pack13_intro
           Real uabd1s17_ren
           unit (fun f : unit -> Real => f tt)
           (fun _ : unit => zero)
           one
           (@one_pos Real uabd1s17_ren)
           (fun _ : unit => one)
           (fun _ : unit => @one_pos Real uabd1s17_ren)
           uabd1s17_dpo_zap_pos
           unit
           (fun _ : unit => tt)
           (fun _ : unit => tt)
           (cons tt nil)).
Qed.

(* ============ 假设审计 ============ *)

Print Assumptions uabd1s17_dpo_zap_pos.
Print Assumptions uabd1s17_dpo_pack13_supplied.
