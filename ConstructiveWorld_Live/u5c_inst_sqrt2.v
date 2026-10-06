(* 五字段指针｜使命：√2（Newton 序列 X = lim x(n)，x(0)=2、
   x(n+1) = (x(n) + 2/x(n))/2）的无理性分离定理——逃逸点显式装配版。
   对任意有理数 q，取逃逸窗见证 ir2_escape q 的显式逃逸点 n0
   （e(n0) < |q − x(n0)|，e(n) = (x(n)² − 2)/2），由通用分离引理
   u5c_escape_to_dist 得 Q 层正分离常数 c := (|q − x(n0)| − e(n0))/2 使
   real_const c < |√2 − q|。与在树 ir2_sqrt2_irrational_criterion 结论形
   一致，差异仅在装配路线：本件经显式逃逸点引理，检验该入口对二次无理
   实例适用；闭式常元路线（c(q) = 1/(b(|a|+2b))）为后续深化方向。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_bridge；Stdlib QArith、Qabs、ZArith、Arith、Bool。
   对标行：UpReqSqrt3Irrational.v ir2_escape、ir2_sqrt2_irrational_criterion。
   构造性注记：语句面全 Set 层，零 Prop 前提位；见证解构与引理装配全构造。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <ConstructiveWorld_vo 树> ""。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

Theorem u5c_sqrt2_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                            (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
       (real_const q)))).
Proof.
  intro q.
  destruct (ir2_escape q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist ir2_x ir2_e ir2_tail ir2_vanish q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt2_criterion_escape_pt.

Print Assumptions u5c_sqrt2_criterion_escape_pt.
