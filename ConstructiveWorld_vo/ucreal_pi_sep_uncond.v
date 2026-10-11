(* 五字段指针｜模块：ucreal_pi_sep_uncond.v。
   数学使命：标准库构造性柯西实数中的无条件 π 无理性分离。对每有理数 a 与每非零
   有理数 b，存在正有理数 c，其严格低于 π 的几何值于距离 |π − a/b| 处（当
   a/b < π 时即 c < π − a/b）。本件将库定理 leibsep_pi_rational_unconditional
   （库构造实数 Real := sigT (fun u : Qseq => cauchy u) 上的语句）转述为 Rocq
   标准库类型 ConstructiveCauchyReals.CReal 上的语句：点 c 经 ucreal_of_real
   传递，严格序语句经 ucreal_lt_compat 传递。
   依赖：Stdlib QArith、QArith.Qabs、QArith.Qminmax、ConstructiveCauchyReals；
   库内 S01_BaseRing、S02_CauchyComplete、S03_QExp、S10_KVQuantTrig、
   Local.LW0LeibSeparation、ucreal_bridge；验证检验段另用 Stdlib Extraction。
   对标：Stdlib.Reals.Cauchy.ConstructiveCauchyReals。
   构造性：语句面全 Set 层（sigT/And/CRealLt）；零全局假设、零证明放弃、零经典
   逻辑；见证 c 及其正性取自库定理，严格序经 ucreal_lt_compat 传递。
   编译配方：coqc -native-compiler no -q -Q . "" -Q "<vo树>/Local" ""
   -Q "<vo树>" "" ucreal_pi_sep_uncond.v，工作目录库树根；COQLIB 与 ROCQLIB
   环境变量同值指向 Rocq 9.1 库根。
*)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import Local.LW0LeibSeparation.
Require Import ucreal_bridge.

(* ================================================================== *)
(* Unconditional pi irrational separation in CReal form.             *)
(* ================================================================== *)

Theorem ucreal_pi_sep_unconditional :
  forall a b : Q,
    QltT 0 (Qabs b) ->
    sigT (fun c : Q => And (QltT 0 c)
            (CRealLt (ucreal_of_real (real_const c))
                     (ucreal_of_real (real_metric real_pi_geom
                        (real_const (a / b)))))).
Proof.
  intros a b Hb.
  destruct (leibsep_pi_rational_unconditional a b Hb)
    as [c [Hpos Hlt]].
  exists c. split.
  - exact Hpos.
  - apply (ucreal_lt_compat _ _ Hlt).
Qed.

(* ================================================================== *)
(* Verification probes.                                              *)
(* ================================================================== *)

From Stdlib Require Import Extraction.
Extraction "ucreal_pi_sep_uncond_extract.ml" ucreal_pi_sep_unconditional.

Print Assumptions ucreal_pi_sep_unconditional.
