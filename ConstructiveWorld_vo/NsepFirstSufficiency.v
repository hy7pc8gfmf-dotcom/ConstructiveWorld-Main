(* ============================================================ *)
(* NsepFirstSufficiency.v —— 预算足用性一般定理：预算化最小分离索引     *)
(*   搜索 nsep_first 的输出与实际首中步数的足用关系（判定器参数化一般   *)
(*   形，对任意 bool 判定器 dec 与任意预算 b 成立）。                    *)
(*   数学使命：NsepFindGeneric 四推论刻画预算足用（[0,b] 内存在命中     *)
(*   阶）时的输出行为；本件补足双向完整刻画——§1 精确停点：r 为         *)
(*   [n,n+fuel] 内首中阶（r 处命中且之下逐阶非命中）则搜索逐字停于 r；  *)
(*   §2 足用合成：预算内存在命中阶则输出为命中且之下逐阶非命中，即      *)
(*   输出恰为实际首中步数；§3 足用预算无关性：任两足用预算输出逐字      *)
(*   相等；§4 非足用特征：输出非命中则搜索耗尽——输出为预算端点且       *)
(*   区间内全程无命中；§5 pi 侧实例接口：LW5SepComplexity 硬编码机      *)
(*   lw5n_find 与通用机 nsep_find 函身同构（固定判定器 lw5n_sep_dec     *)
(*   代参量 dec），归纳过渡后通用机在实例预算 lw5n_bnd 下与 lw5n_nsep  *)
(*   逐字相等，足用合成定理对 pi 实例直接特化。lw5n_bnd 自身足用性      *)
(*   （对每 q 存在命中阶不超过它，即窗宽衰减与点误差的竞争不等式）      *)
(*   属实例方职责，本件不主张，闭证属后续工作。                         *)
(*   依赖：LW0LeibWindow（leiblw_Id/leiblw_id_eq/leiblw_id_inv）、      *)
(*   S01_BaseRing（And := A*B 的 Set 面合取）、NsepFindGeneric          *)
(*   （nsep_find/nsep_first 及特征定理）、LW5SepComplexity（§5 接口）； *)
(*   Stdlib：QArith/ZArith/Arith/Bool/Lia/Extraction。                  *)
(*   对标：NsepFindGeneric.v nsep_find_hit/nsep_find_min/nsep_first_*   *)
(*   （足用刻画与之衔接）；LW5SepComplexity.v lw5n_find :416（函身同    *)
(*   构）/lw5n_bnd/lw5n_nsep :427-429；增长律闭证属后续工作（其头注）。 *)
(*   构造性：零公理/零承认式/零经典逻辑；主结论面全 Set（leiblw_Id 与   *)
(*   And := prod）；nat 序仅前提位置与端点等词位；结构归纳＋bool 分情   *)
(*   形证明；提取面 Obj.magic = 0；文末 Print Assumptions 全 Closed。   *)
(*   编译配方：coqc.exe -native-compiler no -q -Q <沙箱目录> "" -Q      *)
(*   "D:/ComplexAnalysis/新算法实践/Live_X" "" NsepFirstSufficiency.v  *)
(*   （双 export COQLIB/ROCQLIB 至 9.1 lib/coq，温控包裹下单发）。      *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.

(* ============================================================ *)
(* §0 等词接口补充：leiblw_Id 的 false 面与一般等词面提取。             *)
(*    库内 leiblw_id_eq/leiblw_id_inv 仅覆盖 bool 的 =true 面；非足用   *)
(*    特征定理的前提以 leiblw_Id b false 面承载，此处按 leiblw_Id 的    *)
(*    归纳定义补足其等词提取（对任意类型的一般提取面亦然）。            *)
(* ============================================================ *)

Lemma leiblw_id_eqv : forall (A : Type) (x y : A), leiblw_Id x y -> x = y.
Proof.
  intros A x y H. inversion H. reflexivity.
Qed.

Lemma leiblw_id_false_inv : forall b : bool, leiblw_Id b false -> b = false.
Proof.
  intros b H. destruct b as [|].
  - inversion H.
  - reflexivity.
Qed.

(* ============================================================ *)
(* §1 精确停点定理：首中阶 r 落在搜索窗内则有界搜索逐字停于 r。         *)
(* ============================================================ *)

Lemma nsep_find_exact :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n r : nat),
  (n <= r)%nat -> (r <= n + fuel)%nat ->
  leiblw_Id (dec q r) true ->
  (forall m : nat, (n <= m)%nat -> (m < r)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_find dec q n fuel) r.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n r Hn1 Hn2 Hhit Hmin.
  - simpl. assert (Heq : r = n) by lia. subst r. apply leiblw_id_intro.
  - simpl. destruct (Nat.eq_dec n r) as [Heq|Hne].
    + subst r. destruct (dec q n) as [|] eqn:E.
      * apply leiblw_id_intro.
      * inversion Hhit.
    + destruct (dec q n) as [|] eqn:E.
      * assert (Hlt : (n < r)%nat) by lia.
        specialize (Hmin n (Nat.le_refl n) Hlt).
        simpl in Hmin. rewrite E in Hmin. inversion Hmin.
      * apply (IH (Datatypes.S n) r).
        -- lia.
        -- lia.
        -- exact Hhit.
        -- intros m Hm1 Hm2. apply Hmin; lia.
Qed.

(* ============================================================ *)
(* §2 预算足用下输出逐字等于首中步数（n=0 特化）。                      *)
(* ============================================================ *)

Theorem nsep_first_exact :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q) (r : nat),
  (r <= b)%nat ->
  leiblw_Id (dec q r) true ->
  (forall m : nat, (m < r)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_first dec b q) r.
Proof.
  intros dec b q r Hb Hhit Hmin. unfold nsep_first.
  apply (nsep_find_exact dec q b 0 r).
  - apply Nat.le_0_l.
  - lia.
  - exact Hhit.
  - intros m Hm1 Hm2. apply Hmin. exact Hm2.
Qed.

(* ============================================================ *)
(* §3 足用合成：预算足用则输出为命中且输出之下逐阶非命中。              *)
(* ============================================================ *)

Theorem nsep_first_sufficient :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q) (n0 : nat),
  (n0 <= b)%nat -> leiblw_Id (dec q n0) true ->
  And (leiblw_Id (dec q (nsep_first dec b q)) true)
      (forall m : nat, (m < nsep_first dec b q)%nat ->
                       leiblw_Id (dec q m) false).
Proof.
  intros dec b q n0 Hb Hhit. split.
  - exact (nsep_first_hit dec b q n0 Hb Hhit).
  - intros m Hlt. exact (nsep_find_min dec q b 0 m (Nat.le_0_l m) Hlt).
Qed.

(* ============================================================ *)
(* §4 足用预算无关性：首中步数不依赖足用预算的具体取值。                *)
(* ============================================================ *)

Theorem nsep_first_budget_indep :
  forall (dec : Q -> nat -> bool) (q : Q) (b1 b2 : nat) (n0 : nat),
  (n0 <= b1)%nat -> (b1 <= b2)%nat ->
  leiblw_Id (dec q n0) true ->
  leiblw_Id (nsep_first dec b2 q) (nsep_first dec b1 q).
Proof.
  intros dec q b1 b2 n0 H1 H2 Hhit.
  apply (nsep_first_exact dec b2 q (nsep_first dec b1 q)).
  - pose proof (nsep_first_least dec b1 q n0 H1 Hhit) as Hle. lia.
  - exact (nsep_first_hit dec b1 q n0 H1 Hhit).
  - intros m Hlt. exact (nsep_find_min dec q b1 0 m (Nat.le_0_l m) Hlt).
Qed.

(* ============================================================ *)
(* §5 非足用特征：输出非命中则搜索耗尽——输出为预算端点且区间内        *)
(*    全程无命中。等价逆否：预算端点可达搜索（输出非端点）或区间有     *)
(*    命中，则输出为命中阶。                                           *)
(* ============================================================ *)

Lemma nsep_find_false_stop :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  leiblw_Id (dec q (nsep_find dec q n fuel)) false ->
  leiblw_Id (nsep_find dec q n fuel) (n + fuel)%nat.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n H.
  - simpl. replace (n + 0)%nat with n by lia. apply leiblw_id_intro.
  - simpl in H |- *. destruct (dec q n) as [|] eqn:E.
    + simpl in H. rewrite E in H. inversion H.
    + replace (n + Datatypes.S f)%nat with (Datatypes.S n + f)%nat by lia.
      apply (IH (Datatypes.S n)). exact H.
Qed.

Theorem nsep_first_exhausted :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q),
  leiblw_Id (dec q (nsep_first dec b q)) false ->
  And (leiblw_Id (nsep_first dec b q) b)
      (forall n0 : nat, (n0 <= b)%nat -> leiblw_Id (dec q n0) false).
Proof.
  intros dec b q H. unfold nsep_first in H |- *.
  assert (Hstop : leiblw_Id (nsep_find dec q 0 b) (0 + b)%nat)
    by (apply (nsep_find_false_stop dec q b 0); exact H).
  split.
  - apply (leiblw_id_eqv nat) in Hstop. rewrite Hstop.
    replace (0 + b)%nat with b by lia. apply leiblw_id_intro.
  - intros n0 Hn0. destruct (dec q n0) as [|] eqn:E.
    + exfalso.
      assert (Ht : leiblw_Id (dec q n0) true) by (apply leiblw_id_eq; exact E).
      pose proof (nsep_first_hit dec b q n0 Hn0 Ht) as HH.
      unfold nsep_first in HH.
      apply leiblw_id_inv in HH. apply leiblw_id_false_inv in H.
      rewrite HH in H. discriminate H.
    + apply leiblw_id_intro.
Qed.

(* ============================================================ *)
(* §6 pi 侧实例接口：硬编码机与通用机的同构过渡与逐字相等，及足用       *)
(*    合成定理对 pi 实例的直接特化。                                    *)
(* ============================================================ *)

Lemma lw5n_find_nsep_find :
  forall (q : Q) (fuel n : nat),
  leiblw_Id (lw5n_find q n fuel) (nsep_find lw5n_sep_dec q n fuel).
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n.
  - simpl. apply leiblw_id_intro.
  - simpl. destruct (lw5n_sep_dec q n) as [|] eqn:E.
    + apply leiblw_id_intro.
    + apply (IH (Datatypes.S n)).
Qed.

Theorem lw5n_nsep_generic_agree :
  forall q : Q,
  leiblw_Id (nsep_first lw5n_sep_dec (lw5n_bnd q) q) (lw5n_nsep q).
Proof.
  intros q. unfold nsep_first, lw5n_nsep.
  pose proof (lw5n_find_nsep_find q (lw5n_bnd q) 0) as H.
  apply (leiblw_id_eqv nat) in H. rewrite H. apply leiblw_id_intro.
Qed.

Theorem lw5n_first_sufficient :
  forall (q : Q) (b : nat) (n0 : nat),
  (n0 <= b)%nat -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And (leiblw_Id (lw5n_sep_dec q (nsep_first lw5n_sep_dec b q)) true)
      (forall m : nat, (m < nsep_first lw5n_sep_dec b q)%nat ->
                       leiblw_Id (lw5n_sep_dec q m) false).
Proof.
  intros q b n0 Hb Hhit.
  exact (nsep_first_sufficient lw5n_sep_dec b q n0 Hb Hhit).
Qed.

(* ============================================================ *)
(* §7 计算抽查：sqrt(2) Newton 实例（NsepFindGeneric §3 判定器）上     *)
(*    足用、非足用与预算无关三态。q = 3/2 的首中阶为 2（x_2 = 17/12，  *)
(*    e_2 = 1/288，|3/2 - 17/12| = 1/12 > 1/288 出窗）；预算 3 足用得   *)
(*    2，预算 1 内无命中耗尽得端点 1，预算 10 与预算 3 同得 2。         *)
(* ============================================================ *)

Eval vm_compute in (nsep_first ir2_sep_dec 3 (3 # 2)).
Eval vm_compute in (nsep_first ir2_sep_dec 1 (3 # 2)).
Eval vm_compute in (nsep_first ir2_sep_dec 10 (3 # 2)).

(* ============================================================ *)
(* §8 提取核查与假设审计。                                              *)
(* ============================================================ *)

Separate Extraction nsep_find nsep_first.

Print Assumptions leiblw_id_eqv.
Print Assumptions leiblw_id_false_inv.
Print Assumptions nsep_find_exact.
Print Assumptions nsep_first_exact.
Print Assumptions nsep_first_sufficient.
Print Assumptions nsep_first_budget_indep.
Print Assumptions nsep_find_false_stop.
Print Assumptions nsep_first_exhausted.
Print Assumptions lw5n_find_nsep_find.
Print Assumptions lw5n_nsep_generic_agree.
Print Assumptions lw5n_first_sufficient.
