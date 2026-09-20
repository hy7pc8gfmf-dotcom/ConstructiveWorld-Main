(* ============================================================ *)
(* UpAblCauchyMod.v —— S10 cauchy_real_sin/cos 输入柯西模位直配件        *)
(*   （P6 席·20260920）                                                *)
(*                                                                *)
(* 席位：P6（输入柯西模位侦察＋直配尝试席，N10 报告槽③后续）。             *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   交付语句面全 Set 层值（QltT/QleT'＝S02 Id 形＋sigT 见证、            *)
(*   NatLe＝S01 Id 形）；Prop 面换形（Qlt/Qeq）全内联于证明内部。           *)
(*                                                                *)
(* 槽位来源（P6 席侦察定谳，逐处核坐标与语句实形）：                        *)
(*   槽甲 S10_KVQuantTrig.v:2236 cauchy_real_sin 输入柯西模位——           *)
(*      destruct (Hu (eps / (2 * C))%Q) as [N1 HN1]，                     *)
(*      契约＝S02:389 cauchy u 在切口 eps/(2*C) 的实例位，                 *)
(*      Hu 由输入 x : Real（S02:394 sigT(u, cauchy u)）解构供给。          *)
(*   槽乙 S10_KVQuantTrig.v:2321 cauchy_real_cos 输入柯西模位——           *)
(*      同形 destruct (Hu (eps / (2 * C))%Q) as [N1 HN1]，                 *)
(*      同一契约（输入项形状不同不触及本位：N1 只依赖 u 与切口）。          *)
(*      （N10 报告载槽乙于 2318，现盘实形 2321，漂移已核。）               *)
(*                                                                *)
(* 定谳：全称位本体（任意 x）＝内容性墙域——N1 即输入证书之内容，           *)
(*   对任意 u 无独立构造面（N10 原判成立）；                                *)
(*   但具体输入消费面＝上游已备可直配——输入侧柯西模证书群在盘且           *)
(*   全款具体：real_zero（S02:457，见证 N:=O）、real_const c               *)
(*   （S02:858，见证 N:=O）皆 Defined 透明零不透明；两槽在盘消费点         *)
(*   real_sin_zero（S10:2422）/real_cos_one（S10:2437）及其 real_const    *)
(*   族消费点（:2530/:2644/:2660/:3128/:3264/:3280/:4850/:4875/:4909 等） *)
(*   之输入证书全部走此二件。本件即在二具体输入面上落直配四款。            *)
(*                                                                *)
(* 供给结构（四件，ucm_ 前缀）：                                          *)
(*   A/B 输入槽契约位直配：ucm_input_slot_zero / ucm_input_slot_const      *)
(*      ——切口 eps/(2*C) 同形契约，见证 N1 := O 全款具体（C 为任意正值的   *)
(*      全称变元，切口的正性由 eps>0 与 C>0 双假设承接，零 opaque 位）；   *)
(*   C/D 两槽消费面全款：ucm_sin_zero_cauchy / ucm_cos_zero_cauchy         *)
(*      ——real_zero 输入下槽甲/槽乙全链条柯西证书，见证 N := O，           *)
(*      经 sc_sin_partial_zero（S10:2104）/sc_cos_partial_one（S10:2132）  *)
(*      具体化，不经 cauchy_real_sin/cos 之 Defined 体（零穿堂）。         *)
(*                                                                *)
(* 上游全只读零改动；未入 order.txt/_CoqProject。                          *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.

(* real_zero 的底层序列（与 S02:457 同形，独立具名以便直配引用） *)
Definition ucm_zero_seq : Qseq := fun _ : nat => 0%Q.

(* A. 槽甲/槽乙输入契约位直配（零序列输入面）：
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

(* B. 槽甲/槽乙输入契约位直配（常值序列输入面，覆盖 real_const c 族消费点）：
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

(* C. 槽甲消费面全款：real_zero 输入下 sin 部分和序列的柯西证书，
   见证 N := O（S10:2236 之 N1 位在此输入面＝O 全款具体）。 *)
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

(* D. 槽乙消费面全款：real_zero 输入下 cos 部分和序列的柯西证书，
   见证 N := O（S10:2321 之 N1 位在此输入面＝O 全款具体）。 *)
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

(* 假设面自检：四件全 Closed（编译日志留痕） *)
Print Assumptions ucm_input_slot_zero.
Print Assumptions ucm_input_slot_const.
Print Assumptions ucm_sin_zero_cauchy.
Print Assumptions ucm_cos_zero_cauchy.
