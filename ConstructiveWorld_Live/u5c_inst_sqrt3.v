(* 五字段指针｜使命：√3（Newton 序列 X = lim x(n)，x(0)=2、
   x(n+1) = (x(n) + 3/x(n))/2）的无理性分离定理——逃逸点显式装配版。
   对任意有理数 q，取逃逸窗见证 is3_escape q 的显式逃逸点 n0
   （e(n0) < |q − x(n0)|，e(n) = (x(n)² − 3)/2），由通用分离引理
   u5c_escape_to_dist 得 Q 层正分离常数 c := (|q − x(n0)| − e(n0))/2 使
   real_const c < |√3 − q|。与在树 is3_sqrt3_irrational_criterion 结论形
   一致，差异仅在装配路线：本件经显式逃逸点引理，检验该入口对二次无理
   实例适用。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_bridge；Stdlib QArith、Qabs、ZArith、Arith、Bool。
   对标行：UpReqSqrt3Irrational.v is3_escape、is3_sqrt3_irrational_criterion。
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

Theorem u5c_sqrt3_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                            (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
       (real_const q)))).
Proof.
  intro q.
  destruct (is3_escape q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist is3_x is3_e is3_tail is3_vanish q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt3_criterion_escape_pt.

Print Assumptions u5c_sqrt3_criterion_escape_pt.
