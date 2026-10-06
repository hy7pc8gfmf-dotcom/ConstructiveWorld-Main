(* 五字段指针｜使命：e（自然指数级数和 X = lim Σ_{j≤n} 1/j!）的无理性
   分离定理——逃逸点显式装配版。对任意有理数 q，取逃逸窗见证
   lic_witness_e q 的显式逃逸点 n0（1/n! < |q − x(n0)|），由通用分离引理
   u5c_escape_to_dist 得 Q 层正分离常数 c := (|q − x(n0)| − 1/n0!)/2 使
   real_const c < |X − q|。与在树 lic_e_irrational_criterion 结论形一致，
   差异仅在装配路线：本件经显式逃逸点引理，检验该入口对指数型实例适用。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、u5c_bridge；Stdlib 同 u5c_bridge。
   对标行：UpReqIrrationalCriterion.v lic_witness_e、lic_e_irrational_criterion。
   构造性注记：语句面全 Set 层，零 Prop 前提位；见证解构与引理装配全构造。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <ConstructiveWorld_vo 树> ""。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

Theorem u5c_e_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            (fun n => exp_series n 1)
                            (lic_seq_cauchy (fun n => exp_series n 1)
                                            (fun n => 1%Q / q_fact n)
                                            lic_tail_e lic_vanish_e))
       (real_const q)))).
Proof.
  intro q.
  destruct (lic_witness_e q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist (fun n => exp_series n 1) (fun n => 1%Q / q_fact n)
           lic_tail_e lic_vanish_e q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_e_criterion_escape_pt.

Print Assumptions u5c_e_criterion_escape_pt.
