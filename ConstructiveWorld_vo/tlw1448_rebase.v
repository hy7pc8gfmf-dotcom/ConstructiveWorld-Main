(* ================================================================== *)
(* TLW1448Rebase —— 有界线性搜索的显式预算重置族                          *)
(*                                                                    *)
(* 数学使命：lw5n_nsep 的预算焊定于 lw5n_bnd（包络列在 1/(分母+1) 处的    *)
(*   阶），该预算对分离见证不足用（22/7 实测反例在卷）。本模块把预算      *)
(*   重置为任一显式 Q 函数 ck : Q -> Q 生成的界 B(q) := S(pie_modulus   *)
(*   (ck q / 2))，并复用 lw5n_find 机件给出换基后的上界、命中、不越      *)
(*   三定理；ck 取分离距离 kernel 的显式见证时即得增长律闭合所需的       *)
(*   预算基（对偶定理另件）。                                           *)
(*                                                                    *)
(* 依赖清单：Stdlib QArith/List/Bool/Arith/Setoid/Morphisms/Lia/Qminmax；*)
(*   S01_BaseRing S02_CauchyComplete S03_QExp PiEnvelope LW0MLicBridge  *)
(*   LW0LeibWindow S10_KVQuantTrig S11_TP3B5 LW5SepComplexity           *)
(*                                                                    *)
(* 对标行：LW5SepComplexity §3（lw5n_find/_ub/_hit 机件与 lw5n_nsep      *)
(*   预算位）；LW1PiMeasure §1（lw1m_nsep 自有窗阶＝共享搜索机件×显式    *)
(*   预算的同构先例）。                                                 *)
(*                                                                    *)
(* 构造性注记：全 Set/Type 层；零 Axiom/Admitted；零 Prop 泄露；预算界    *)
(*   不设正性前提（上界与命中定理对任意预算参数成立）。                   *)
(*                                                                    *)
(* 编译配方：coqc -native-compiler no -q -Q . "" tlw1448_rebase.v        *)
(*   （沙箱内含认证 vo 播种闭包；同目录 Local/ 供 Local 前缀件）          *)
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

(* 显式预算基：B(q) := S(pie_modulus(ck q / 2))，ck 为 q 上显式 Q 函数。
   增长律闭合取 ck 为分离距离 kernel 的显式见证函数；本模块对任意 ck 成立。 *)
Definition tlw1448_bexp (ck : Q -> Q) (q : Q) : nat :=
  Datatypes.S (pie_modulus ((ck q) / 2)%Q).

(* 换基搜索器：共享搜索机件 lw5n_find × 显式预算基（lw1m_nsep 同构形） *)
Definition tlw1448_nsep_rebase (ck : Q -> Q) (q : Q) : nat :=
  lw5n_find q 0 (tlw1448_bexp ck q).

(* 换基上界：搜索不越显式预算基（lw5n_find_ub 直取） *)
Theorem tlw1448_nsep_rebase_bound : forall (ck : Q -> Q) (q : Q),
  (tlw1448_nsep_rebase ck q <= tlw1448_bexp ck q)%nat.
Proof.
  intros ck q. unfold tlw1448_nsep_rebase.
  pose proof (lw5n_find_ub q (tlw1448_bexp ck q) 0) as H. lia.
Qed.

(* 换基命中：预算基内存在分离阶则搜索停在分离阶（lw5n_find_hit 直取） *)
Theorem tlw1448_nsep_rebase_hit : forall (ck : Q -> Q) (q : Q) (n0 : nat),
  (n0 <= tlw1448_bexp ck q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  leiblw_Id (lw5n_sep_dec q (tlw1448_nsep_rebase ck q)) true.
Proof.
  intros ck q n0 Hb Hhit. unfold tlw1448_nsep_rebase.
  destruct (lw5n_find_hit q (tlw1448_bexp ck q) 0 n0 (Nat.le_0_l n0) Hb Hhit)
    as [H _].
  exact H.
Qed.

(* 换基不越：搜索不越过预算基内任一分离阶（lw5n_find_hit 第二分量） *)
Theorem tlw1448_nsep_rebase_least : forall (ck : Q -> Q) (q : Q) (n0 : nat),
  (n0 <= tlw1448_bexp ck q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  (tlw1448_nsep_rebase ck q <= n0)%nat.
Proof.
  intros ck q n0 Hb Hhit.
  apply Nat.leb_le. apply leiblw_id_inv.
  unfold tlw1448_nsep_rebase.
  destruct (lw5n_find_hit q (tlw1448_bexp ck q) 0 n0 (Nat.le_0_l n0) Hb Hhit)
    as [_ H].
  exact H.
Qed.

(* ---- 假设审计（应全 Closed）---- *)
Print Assumptions tlw1448_nsep_rebase_bound.
Print Assumptions tlw1448_nsep_rebase_hit.
Print Assumptions tlw1448_nsep_rebase_least.

(* ---- 提取探针（Obj.magic 应为 0）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1448_rebase_ext.ml" tlw1448_bexp tlw1448_nsep_rebase.
