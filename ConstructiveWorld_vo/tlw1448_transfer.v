(* ================================================================== *)
(* TLW1448Transfer —— 分离距离 kernel 到逐点距离证书的语句面换形          *)
(*                                                                    *)
(* 数学使命：leibsep_q_kernel 对任意 q 无条件给出显式见证 (c, N)：        *)
(*   0 < c 且尾段逐点 c < |xL k − q|；lw1m_dist_pt q d 是同一逐点尾段    *)
(*   性质的证书封装（QltT/QltT' 一字之差，两定义体同为 Id (Qlt_bool ..)  *)
(*   true）。本模块给出两者的换形定理、kernel 见证的定义化提取           *)
(*   ck q := projT1 (leibsep_q_kernel q)，以及闭合定理所需的显式预算     *)
(*   基 Bexp q := S(pie_modulus(ck q / 2))。换形零数学内容：逐字同构。   *)
(*                                                                    *)
(* 依赖清单：Stdlib QArith/List/Bool/Arith/Setoid/Morphisms/Lia/Qminmax；*)
(*   S01_BaseRing S02_CauchyComplete S03_QExp PiEnvelope LW0MLicBridge  *)
(*   LW0LeibWindow S10_KVQuantTrig S11_TP3B5 LW5SepComplexity           *)
(*   Local.LW0LeibSeparation LW0PiIrrational LW1PiMeasure               *)
(*                                                                    *)
(* 对标行：LW0LeibSeparation :5452（leibsep_q_kernel 语句面）；           *)
(*   LW1PiMeasure :174（lw1m_dist_pt 定义）；S02 :48 与 PiEnvelope :56   *)
(*   （QltT/QltT' 同体定义）；LW1PiMeasure §五装配图 L1 换形位。          *)
(*                                                                    *)
(* 构造性注记：全 Set/Type 层；零 Axiom/Admitted；零 Prop 泄露；ck 为     *)
(*   projT1 直取的定义项（QltT 到 QltT' 转换经 convertible 直用）。       *)
(*                                                                    *)
(* 编译配方：coqc -native-compiler no -q -Q . "" tlw1448_transfer.v      *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW0LeibWindow.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import LW5SepComplexity.
Require Import Local.LW0LeibSeparation.
Require Import LW0PiIrrational.
Require Import LW1PiMeasure.

(* QltT 与 QltT' 定义体同为 Id (Qlt_bool x y) true（S02 与 PiEnvelope），
   convertible 直换；立名便于审读。 *)
Lemma tlw1448_qltT_to_qltT' : forall x y : Q, QltT x y -> QltT' x y.
Proof. intros x y H. exact H. Qed.

(* margin_transfer：kernel 存在形 ⟹ 逐点距离证书形（语句面逐字同构换形） *)
Theorem tlw1448_margin_transfer : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c) (lw1m_dist_pt q c)).
Proof.
  intros q. destruct (leibsep_q_kernel q) as [c [Hc [N HN]]].
  exists c. split.
  - exact Hc.
  - exists N. intros k Hk. exact (HN k Hk).
Qed.

(* kernel margin 的定义化提取：ck q := kernel 见证的第一分量（Q 项） *)
Definition tlw1448_ck (q : Q) : Q := projT1 (leibsep_q_kernel q).

(* 闭合定理的目标预算基：Bexp q := S(pie_modulus(ck q / 2)) *)
Definition tlw1448_Bexp (q : Q) : nat :=
  Datatypes.S (pie_modulus ((tlw1448_ck q) / 2)%Q).

(* 换形指向形：kernel 见经 projT1 提取后仍携带正性与逐点尾段证书 *)
Theorem tlw1448_kernel_dist_ck : forall q : Q,
  And (QltT 0 (tlw1448_ck q)) (lw1m_dist_pt q (tlw1448_ck q)).
Proof.
  intros q. unfold tlw1448_ck.
  destruct (leibsep_q_kernel q) as [c [Hc [N HN]]].
  split.
  - exact Hc.
  - exists N. intros k Hk. exact (HN k Hk).
Qed.

(* ---- 假设审计（应全 Closed）---- *)
Print Assumptions tlw1448_margin_transfer.
Print Assumptions tlw1448_kernel_dist_ck.
Print Assumptions tlw1448_Bexp.

(* ---- 提取检验（Obj.magic 计数如实登记）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1448_transfer_ext.ml" tlw1448_ck tlw1448_Bexp.
