(* UpAblCauchyMod.v —— S10 cauchy_real_sin/cos 输入柯西模的依赖模块        *) (* 使命：为 S10_KVQuantTrig 的 cauchy_real_sin 与 cauchy_real_cos        *)
(*   之输入柯西模提供供给；柯西模＝柯西见证 N1 的存在性。                 *)
(* 目标形（两处同形）：                                                  *)
(*   sin 侧 cauchy_real_sin 与 cos 侧 cauchy_real_cos 均含               *)
(*   destruct (Hu (eps / (2 * C))%Q) as [N1 HN1]，                       *)
(*   即 S02 之 cauchy u 在切口 eps/(2*C) 的实例；                        *)
(*   Hu 由输入 x : Real（sigT(u, cauchy u) 形）解构供给；                 *)
(*   （N1 只依赖 u 与切口，两处输入项形状不同不影响本件。）               *)
(* 范围注记：对任意输入 x 的全称供给不可达——N1 即输入柯西证书之内容，     *)
(*   无法对任意 u 独立构造；但具体输入上的供给可以完成——输入侧           *)
(*   柯西证书已在库且全部具体：real_zero（见证 N:=O）、real_const c      *)
(*   （见证 N:=O）皆 Defined 透明（零不透明定义）；real_sin_zero、       *)
(*   real_cos_one 及其 real_const 族使用处之输入证书全部走此二形，       *)
(*   本件即在二具体输入面上完成四件供给。                                 *)
(* 供给结构（四件，ucm_ 前缀）：                                          *)
(*   A/B 输入柯西模：ucm_input_slot_zero / ucm_input_slot_const          *)
(*      ——切口 eps/(2*C) 的同形实例，见证 N1 := O 具体给出（C 为任意     *)
(*      正值的全称变元，切口正性由 eps>0 与 C>0 双前提给出，零不透明）；  *)
(*   C/D 具体输入证书：ucm_sin_zero_cauchy / ucm_cos_zero_cauchy         *)
(*      ——real_zero 输入下 sin/cos 部分和序列的柯西证书，见证 N := O，   *)
(*      经 sc_sin_partial_zero / sc_cos_partial_one 具体化，             *)
(*      不经 cauchy_real_sin / cauchy_real_cos 之 Defined 体，           *)
(*      供给链零中转。                                                   *)
(* 依赖：CW_ConstructiveWorld_219＋Stdlib List/QArith.QArith/Qabs/Qring＋ *)
(*   Stdlib Lia/Lqa。                                                     *)
(* 对标：mathlib 置顶使命与声明注释惯例；stdlib 文档注释惯例。            *)
(* 构造性注记：语句面全 Set 层值（QltT/QleT'＝S02 Id 形＋sigT 见证、      *)
(*   NatLe＝S01 Id 形）；Prop 面换形（Qlt/Qeq）全内联于证明内部；         *)
(*   零承认；全件 Qed 闭合。                                              *)
(* 编译配方：Rocq 9.1 coqc 直调＋cpu_guard 包裹，输出经 -o 临时目录，树内 .vo 不重写。 *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

(* real_zero 的底层序列（与 S02 中 real_zero 之底层序列同形，独立具名以便引用） *)
Definition ucm_zero_seq : Qseq := fun _ : nat => 0%Q.

(* A. 输入柯西模（零序列输入面）：
   cauchy u 在切口 eps/(2*C) 的实例，见证 N1 := O。 *)
Corollary ucm_input_slot_zero : forall (eps C : Q),
  QltT 0 eps -> QltT 0 C ->
  sigT (fun N1 : nat => forall m n : nat, NatLe N1 m -> NatLe N1 n ->
    QltT (Qabs (ucm_zero_seq m - ucm_zero_seq n)) (eps / (2 * C))).
Proof.
  intros eps C Heps HC.
  exists O.
  intros m n Hm Hn.
  unfold ucm_zero_seq.
  simpl.
  apply (qltT_div_pos eps (2 * C)).
  - exact Heps.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat 2 C).
    + unfold Qlt. simpl. lia.
    + apply QltT_to_Qlt. exact HC.
Qed.

(* B. 输入柯西模（常值序列输入面，覆盖 real_const c 族使用处）：
   cauchy (fun _ => c) 在切口 eps/(2*C) 的实例，见证 N1 := O。 *)
Corollary ucm_input_slot_const : forall (c eps C : Q),
  QltT 0 eps -> QltT 0 C ->
  sigT (fun N1 : nat => forall m n : nat, NatLe N1 m -> NatLe N1 n ->
    QltT (Qabs (c - c)) (eps / (2 * C))).
Proof.
  intros c eps C Heps HC.
  exists O.
  intros m n Hm Hn.
  apply (qltT_eq_compat_l 0 (Qabs (c - c))).
  - apply Qeq_sym. apply q_abs_self_zero.
  - apply (qltT_div_pos eps (2 * C)).
    + exact Heps.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 C).
      * unfold Qlt. simpl. lia.
      * apply QltT_to_Qlt. exact HC.
Qed.

(* C. 具体输入证书：real_zero 输入下 sin 部分和序列的柯西证书，
   见证 N := O（cauchy_real_sin 之 N1 在此输入面具体为 O）。 *)
Corollary ucm_sin_zero_cauchy :
  cauchy (fun n : nat => sin_partial n (projT1 real_zero n)).
Proof.
  intros eps Heps.
  exists O.
  intros m n Hm Hn.
  change (sin_partial m (projT1 real_zero m)) with (sin_partial m 0).
  change (sin_partial n (projT1 real_zero n)) with (sin_partial n 0).
  assert (H1 : sin_partial m 0 - sin_partial n 0 == 0).
  { rewrite (sc_sin_partial_zero m). rewrite (sc_sin_partial_zero n). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply qeq_le.
    apply (Qabs_wd (sin_partial m 0 - sin_partial n 0) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* D. 具体输入证书：real_zero 输入下 cos 部分和序列的柯西证书，
   见证 N := O（cauchy_real_cos 之 N1 在此输入面具体为 O）。 *)
Corollary ucm_cos_zero_cauchy :
  cauchy (fun n : nat => cos_partial n (projT1 real_zero n)).
Proof.
  intros eps Heps.
  exists O.
  intros m n Hm Hn.
  change (cos_partial m (projT1 real_zero m)) with (cos_partial m 0).
  change (cos_partial n (projT1 real_zero n)) with (cos_partial n 0).
  assert (H1 : cos_partial m 0 - cos_partial n 0 == 0).
  { rewrite (sc_cos_partial_one m). rewrite (sc_cos_partial_one n). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply qeq_le.
    apply (Qabs_wd (cos_partial m 0 - cos_partial n 0) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* 假设审计：以下四件 Print Assumptions 均为 Closed（零外部未证假设） *)
Print Assumptions ucm_input_slot_zero.
Print Assumptions ucm_input_slot_const.
Print Assumptions ucm_sin_zero_cauchy.
Print Assumptions ucm_cos_zero_cauchy.
