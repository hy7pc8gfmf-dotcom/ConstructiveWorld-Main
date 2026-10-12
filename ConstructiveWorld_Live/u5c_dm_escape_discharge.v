(* 五字段指针｜使命：u5c_dm_escape_to_dist_any 消解件——为已绿源件构建供给定理 T×2：
   dmec_escape_to_dist_any_ir2（√2 牛顿列）/ dmec_escape_to_dist_any_is3（√3 牛顿列）。
   消解依据：主语句的 Ht : lic_tail_bounded x e 与 Hv : lic_vanish e 两接口前提
   在使用实例可由库内已绿件消解——UpReqSqrt3Irrational 的 ir2_tail/ir2_vanish
   （√2）与 is3_tail/is3_vanish（√3）皆为非平凡定义面（尾控逐窗验证/消失逐 eps
   显式 N），本件以其实例装配，Ht/Hv 零前提化。证体＝dmec_escape_to_dist_any
   ir2_x ir2_e ir2_tail ir2_vanish（/is3 同构）的全参显式应用装配（使用先例：
   u5c_sqrt2_closed_measure.v 同形 pose proof）。实质申报：装配平凡性属辅助装配位，
   非平凡性全居实例供给（四实例皆已绿实质定义面），显式申报如上。
   margin 前提 QleT' (c+c) (|q−x(n0)|−e(n0))、正性 QltT 0 c 与逃逸前提
   QltT (e n0) |q−x(n0)| 系引理本质，保留（使用方按例供给，先例：
   u5c_sqrt2_closed_measure 的 dmcm_margin_closed + dmew_escape_closed_window 链）。
   依赖：在册库件链至 UpReqSqrt3Irrational＋已绿 u5c_dm_escape_to_dist_any（只读 Require）。
   构造性注记：证体＝已绿定义面的全参显式应用装配（实质申报如上）；主语句供给定理面
   零前提化；零承认、零经典、零全局假设。
   编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh
   后于池目录 rocq c -native-compiler no -q -Q . "" u5c_dm_escape_discharge.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Setoid Morphisms Qfield.

(* ============================================================ *)
(* T-1：√2 牛顿列实例（ir2_tail/ir2_vanish 消解 Ht/Hv）                  *)
(* ============================================================ *)

Lemma dmec_escape_to_dist_any_ir2 :
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (ir2_e n0) (Qabs ((q - ir2_x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)%Q) ->
    sigT (fun c' : Q => And (QltT 0 c')
      (real_lt (real_const c')
         (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                          (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                      (real_const q)))).
Proof.
  intros q n0 Hn01 Hesc c Hc0 Hmarg.
  exact (dmec_escape_to_dist_any ir2_x ir2_e ir2_tail ir2_vanish
           q n0 Hn01 Hesc c Hc0 Hmarg).
(* 沿源件修复方案（源定理同款一词改）：sigT 见证透明以支撑下游 Qeq 确定装配 *)
Defined.

(* ============================================================ *)
(* T-2：√3 牛顿列实例（is3_tail/is3_vanish 消解 Ht/Hv），与 T-1 同构      *)
(* ============================================================ *)

Lemma dmec_escape_to_dist_any_is3 :
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (is3_e n0) (Qabs ((q - is3_x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - is3_x n0)%Q) - is3_e n0)%Q) ->
    sigT (fun c' : Q => And (QltT 0 c')
      (real_lt (real_const c')
         (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                          (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
                      (real_const q)))).
Proof.
  intros q n0 Hn01 Hesc c Hc0 Hmarg.
  exact (dmec_escape_to_dist_any is3_x is3_e is3_tail is3_vanish
           q n0 Hn01 Hesc c Hc0 Hmarg).
(* 同 T-1：Defined 透明 *)
Defined.

Print Assumptions dmec_escape_to_dist_any_ir2.
Print Assumptions dmec_escape_to_dist_any_is3.
