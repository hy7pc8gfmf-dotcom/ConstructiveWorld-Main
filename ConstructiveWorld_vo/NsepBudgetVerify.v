(* ========================================================================= *)
(* Module   : NsepBudgetVerify                                              *)
(* Mission  : verification block split out of NsepBudgetExhaustion so the   *)
(*            host file is born in minutes: the instance anchor             *)
(*            q0 := 22/7, the two computed pins (budget lw5n_bnd q0 = 34    *)
(*            and endpoint window lw5n_inwin q0 34 = true) relocated        *)
(*            unchanged from the host, and the all-levels window lemma      *)
(*            lw5n_inwin_q0_all constantized per the B-piece surgery: no    *)
(*            lw5n_shape_mono materialization; it goes through the          *)
(*            analytic window nesting lemma lw5n_win_nested plus two        *)
(*            level-34 comparison pins Qle (lw5n_lo 34) q0 and              *)
(*            Qle q0 (lw5n_hi 34), bool-evaluated at the endpoint level.    *)
(* Dependencies: LW0LeibWindow (leiblw_Id/leiblw_id_eq/leiblw_Qleb),        *)
(*            S01_BaseRing, NsepFindGeneric, LW5SepComplexity (lw5n_lo/hi,  *)
(*            lw5n_inwin, lw5n_bnd, lw5n_nsep, lw5n_win_nested :228,        *)
(*            lw5n_Qle_Qleb_true :606); Stdlib QArith/ZArith/Arith/Bool/Lia.*)
(* Constructivity: conclusion faces fully Set-carried (leiblw_Id); zero     *)
(*            axioms, zero classical logic, zero admits. The two endpoint   *)
(*            comparison pins carry the Qle face of lw5n_win_nested :228    *)
(*            (library precedent); the two relocated eq-face pins           *)
(*            lw5n_bnd_q0/lw5n_inwin_q0_bnd are moved verbatim from the     *)
(*            host, not new Prop faces; none enters an extraction unit;     *)
(*            vm_compute confined to the pins; endpoint Q-order pins        *)
(*            reduce to a concrete Z constructor mismatch discharged by     *)
(*            discriminate (Rocq 9.1 Z.le := ?= <> Gt, declared here).      *)
(* Build    : coqc -native-compiler no -q -Q <tree root> ""                 *)
(*            NsepBudgetVerify.v (single shot, this directory as workdir);  *)
(*            host NsepBudgetExhaustion.v Requires this module with the     *)
(*            sandbox dir as an additional -Q root ahead of the tree root.  *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.

(* ============================================================ *)
(* §V0 实例锚点与两枚计算钉（自主件 §2 原样迁入）                       *)
(* ============================================================ *)

Definition q0 : Q := (22 # 7)%Q.

Lemma lw5n_bnd_q0 : lw5n_bnd q0 = 34%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma lw5n_inwin_q0_bnd : lw5n_inwin q0 34 = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §V1 端点两侧比较钉（第 34 级 lo/hi 对 q0 的 Q 序，字面量级计算）      *)
(* ============================================================ *)

Lemma lw5n_lo34_le_q0 : Qle (lw5n_lo 34) q0.
Proof. vm_compute. discriminate. Qed.

Lemma lw5n_q0_le_hi34 : Qle q0 (lw5n_hi 34).
Proof. vm_compute. discriminate. Qed.

(* ============================================================ *)
(* §V2 全阶窗内引理——常量化：不走 lw5n_shape_mono 全量物化，改走        *)
(*    lw5n_win_nested 解析嵌套（LW5SepComplexity :228）＋§V1 两钉，       *)
(*    经 lw5n_Qle_Qleb_true（:606）Qle→bool 桥逐侧下传。                *)
(* ============================================================ *)

Lemma lw5n_inwin_q0_all :
  forall n : nat, (n <= 34)%nat -> leiblw_Id (lw5n_inwin q0 n) true.
Proof.
  intros n Hn.
  destruct (lw5n_win_nested n 34 Hn) as [Hlo Hhi].
  apply leiblw_id_eq. unfold lw5n_inwin.
  rewrite (lw5n_Qle_Qleb_true (lw5n_lo n) q0
             (Qle_trans (lw5n_lo n) (lw5n_lo 34) q0 Hlo lw5n_lo34_le_q0)).
  rewrite (lw5n_Qle_Qleb_true q0 (lw5n_hi n)
             (Qle_trans q0 (lw5n_hi 34) (lw5n_hi n) lw5n_q0_le_hi34 Hhi)).
  reflexivity.
Qed.

(* ============================================================ *)
(* §V3 计算抽查（自主件 §5 迁入）                                       *)
(* ============================================================ *)

Eval vm_compute in (lw5n_nsep q0).
Eval vm_compute in (lw5n_inwin q0 (lw5n_bnd q0)).

(* ============================================================ *)
(* §V4 假设审计（本件三定理）                                           *)
(* ============================================================ *)

Print Assumptions lw5n_bnd_q0.
Print Assumptions lw5n_inwin_q0_bnd.
Print Assumptions lw5n_inwin_q0_all.
