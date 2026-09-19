(* ============================================================ *)
(* UpAblDistLogEq.v                                                            *)
(*                                                                             *)
(* 目的： UpReqDist.v:1037「dist_log_eq_linear」槽的具体 Regular-Real 载体      *)
(*       实例供给（族E eq 侧闭合件；B2 定谳 T13c-2「log-eq 槽具体载体非墙」    *)
(*       的兑现件）。                                                          *)
(* 主件： ydle_dist_log_eq_linear —— 槽位语句逐字对齐的具体实例                 *)
(*       （R:=Real、RIS:=RealEnhancedReal；显式 forall 前件）。                 *)
(* 伴件： ydle_dist_log_eq_linear_short —— 不经 t1/t34 成品件、由 S07 弱三分    *)
(*       + G07 双支切线本源骨架重证的短链（供给的骨架独立性复核）。             *)
(*       ydle_dist_log_eq_linear_ex —— 全显式实例参放电形（UpReqDist           *)
(*       Section ReqFEP 出节位按位喂入用）。                                    *)
(* 孪生： ydle_dist_log_eq_linear_real / _short_real —— 同内容的具体层          *)
(*       （real_lt/real_eq）证书二件，担提取见证面（见形态差申报）。             *)
(* 依赖： CW_ConstructiveWorld_219、G07_KLWall、UpReqKLSTangent、UpReqAlgebra。 *)
(* 备注： 槽位实形（UpReqDist.v:1037-1039，Section ReqFEP）：                   *)
(*         Hypothesis dist_log_eq_linear :                                     *)
(*           forall (x : R) (Hx : lt zero x),                                  *)
(*             req (log x Hx) (req_minus x one) -> req x one.                  *)
(*       槽仅依赖节境 {R : Set}{RIS : RealInterfaceEnhancedSetoid R}——          *)
(*       无 S/sumf/分布参数自由度，故具体载体实例即全位覆盖。                   *)
(*       t34 同构度对表（t34_log_eq_linear_weak @ UpReqCEqDispersion.v:80）：   *)
(*         · 载体参数：t34 面向 Real 直陈；本槽经 {R}{RIS} 节境泛化，            *)
(*           实例化 R:=Real/RIS:=RealEnhancedReal 后同一；                      *)
(*         · 前件组：两者均零额外前件（同吃 x/Hx/切点前提三元）；               *)
(*         · eq 形态：两者均 req 系 setoid 等号（Id 系 L304 接口形不在本槽）。   *)
(*       结论：零形态差、零新增自由度，t34 形直接换装即合槽。                   *)
(* 提取面形态差申报：接口形三件（主件/短链/放电形）是槽位放电面，Coq 层经        *)
(*       exact 转换判定与具体层互通；但接口投影型与具体层 real_* 型在 Caml 提取  *)
(*       层为两个型缩写，接口形直提取在交界生成魔数残留（UpReqCEqDispersion      *)
(*       头注 T26「运行型转换残留」同现象、B2 magic=3 按族登记先例；实测          *)
(*       Extraction Inline 投影/实例常量两路均无效——提取层不做投影 over 常量     *)
(*       实例的归约）。故抽取位只列具体层孪生证书二件（Part D，t1 同构形）作     *)
(*       提取见证，G3 全树魔数=0；接口形不 ship 提取（T26「自段口径不 ship」     *)
(*       同款处置）。                                                           *)
(* 红线自查：本件为零承认件（无承认性收尾、无新增假设声明位、无经典逻辑导入、    *)
(*       无抽取魔数）；语句面全 req/lt 接口 Set 值，Set 层零 Prop 泄露           *)
(*       （Prop 仅经 real_weak_trich 库内 Not 形在证明体内消费，不上语句面）；   *)
(*       全 Qed 闭合；既有文件零改；新名 ydle_ 前缀（全库检索零冲突）。          *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G07_KLWall.
Require Import UpReqKLSTangent.
Require Import UpReqAlgebra.

Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part A：重证短链——S07/G07 本源骨架（不经 t1/t34 成品件）                      *)
(*   证明骨架 = t34 先例同款：                                                  *)
(*     real_weak_trich（S07:5719 双否形弱三分，直觉主义有效不触 LPO）           *)
(*     + klst_log_tangent_neg（0<x<1 支，G07:2568）                             *)
(*     + klst_log_tangent_pos（1<x 支，G07:173）                                *)
(*     + RealSetoid.real_lt_compat（切点前提沿 req 的传输，成对形）             *)
(*     + real_lt_irrefl（S02:2391）收紧。                                       *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_short : forall (x : Real) (Hx : lt zero x),
  req (log x Hx) (req_minus x one) -> req x one.
Proof.
  intros x Hx Heqlin.
  (* δ 换装：接口投影 req/lt/log/req_minus 在 RealEnhancedReal 实例上与          *)
  (* 具体层 real_eq/real_lt/real_log/plus-opp δ 互通（t34 先例同款转换判定）。    *)
  assert (Heq : real_eq (real_log x Hx) (real_plus x (real_opp real_one)))
    by exact Heqlin.
  apply (real_weak_trich x real_one).
  - (* 支 1：排除 x < 1。负支切线 + 恒等代换 ⟹ x−1 < x−1，irrefl 收紧。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_neg x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
  - (* 支 2：排除 1 < x。正支切线 + 同款收紧。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_pos x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
Qed.

(* ============================================================ *)
(* Part B：主件——B2 定谳（T13c-2）兑现：t34 骨架换装直供槽位                    *)
(*   经 UpReqKLSTangent.t1_log_eq_linear_inject（G07/S07 链成品）零假设喂入；    *)
(*   与 Part A 互为独立复核（主件走成品链，短链走本源骨架）。                   *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear : forall (x : Real) (Hx : lt zero x),
  req (log x Hx) (req_minus x one) -> req x one.
Proof.
  intros x Hx Heqlin.
  exact (t1_log_eq_linear_inject x Hx Heqlin).
Qed.

(* ============================================================ *)
(* Part C：全显式实例参放电形——UpReqDist Section ReqFEP 出节位实装用            *)
(*   出节后槽位实参形 = @lt/@req/@log/@req_minus 全带实例参；                   *)
(*   本件全显式重述主件，消费面按位喂入免推参。                                 *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_ex :
  forall (x : Real)
         (Hx : @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) x),
    @req Real RealEnhancedReal
         (@log Real RealEnhancedReal x Hx)
         (@req_minus Real RealEnhancedReal x (@one Real RealEnhancedReal)) ->
    @req Real RealEnhancedReal x (@one Real RealEnhancedReal).
Proof.
  intros x Hx Heqlin.
  exact (ydle_dist_log_eq_linear x Hx Heqlin).
Qed.

(* ============================================================ *)
(* Part D：具体层孪生证书——提取见证面                                           *)
(*   语句形 = t1_log_eq_linear_inject 同构（real_lt/real_eq 直陈），            *)
(*   与接口形主件/短链同内容（两层在 RealEnhancedReal 上 δ 互通）。             *)
(*   实测：该形提取零残留（对照 UpReqKLSTangent.ml 的 t1 提取体）。              *)
(* ============================================================ *)

Lemma ydle_dist_log_eq_linear_real : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log x Hx) (real_plus x (real_opp real_one)) -> real_eq x real_one.
Proof.
  intros x Hx Heq.
  exact (t1_log_eq_linear_inject x Hx Heq).
Qed.

Lemma ydle_dist_log_eq_linear_short_real : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log x Hx) (real_plus x (real_opp real_one)) -> real_eq x real_one.
Proof.
  intros x Hx Heq.
  apply (real_weak_trich x real_one).
  - (* 支 1：排除 x < 1。负支切线 + 恒等代换 ⟹ x−1 < x−1，irrefl 收紧。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_neg x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
  - (* 支 2：排除 1 < x。正支切线 + 同款收紧。 *)
    intro Hlt.
    assert (Htan : real_lt (real_log x Hx) (real_plus x (real_opp real_one)))
      by exact (klst_log_tangent_pos x Hx Hlt).
    exact (real_lt_irrefl (real_plus x (real_opp real_one))
             (RealSetoid.real_lt_compat (real_log x Hx)
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             (real_plus x (real_opp real_one))
                             Heq
                             (real_eq_refl (real_plus x (real_opp real_one)))
                             Htan)).
Qed.

(* ============================================================ *)
(* 抽取验证位：单条合并命令列全部常量（AB7 卡坑 1：多条抽取命令互相冲写 .ml，    *)
(* 一律单命令 + let 计数对账）。只列具体层孪生二件——接口形不 ship 提取          *)
(* （形态差申报见头注）。                                                       *)
(* ============================================================ *)

Separate Extraction ydle_dist_log_eq_linear_real
                    ydle_dist_log_eq_linear_short_real.
