(* ============================================================ *)
(* UpReqCauchyLogBound.v —— R2-RCL 席：柯西侧显式对数返回界               *)
(* （fuel 结构递归二分搜索本体的对数界显式化）2026-09-24                  *)
(* ============================================================ *)
(* RBC 对账席定谳：Bishop 路线的对数返回界已闭合                          *)
(*   （R2BishopLogSel.rb_log_return_bound: S j0 <= 2^(log2 j0 + 2)），     *)
(*   而柯西侧的"对数性寄存于二分 Fixpoint 本体"=设计形未显式化。          *)
(*   本件补缺口：自带 cl_bsearch（Q 区间 [lo,hi] 上 Qle_bool 驱动的       *)
(*   fuel 结构递归二分：区间每步折半、fuel 每步减一、结构性终止），        *)
(*   主定理 cl_bsearch_log_bound 把对数性显式绑回搜索本体：               *)
(*     fuel = log2 j0 + 2 的搜索在 [0,j0] 上给出双账                      *)
(*     （通过+最小 或 诚实无解报告）且 S j0 <= 2^(log2 j0 + 2)。          *)
(*                                                              *)
(* 对标表（与 R2BishopLogSel.v / UpReqMixLogA.v）：                       *)
(*   mixa_bsearch         ~ cl_bsearch      （二分核自带，零库内 Require） *)
(*   rb_bishop_search     ~ cl_bsearch_log  （fuel j0 的 [0,j0] 搜索）     *)
(*   rb_cond/rb_cond_mono ~ cl_cond/cl_cond_mono（Qle_bool 驱动+单调）     *)
(*   rb_fuel_ge           ~ cl_fuel_ge_pos （0<j0 燃料充分性）              *)
(*   rb_log_return_bound  ~ cl_log_return_bound（同形逐字对标）            *)
(*   rb_bishop_search_ok  ~ cl_bsearch_ok   （通过+最小账）                *)
(*   （Bishop 侧无）      ~ cl_bsearch_dual （新增：通过+最小 或 诚实无解） *)
(*                                                              *)
(* 依赖：仅 Stdlib（PeanoNat/QArith/Qring/Lia/Extraction）。              *)
(*   二分核自带；在建件零 Require（并行代理 B 的 WIP 零触碰）。           *)
(*                                                              *)
(* 红线自检：全文零公理承认参数猜想中止；经典逻辑零引入；                 *)
(*   搜索判定全在 Q 层（Qle_bool）；fuel 结构性递归；                     *)
(*   提取探针 Obj.magic = 0（G3 实测）。                                  *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.

(* nat 记号优先（QArith 泄漏 Q_scope；Q 侧算式期望类型驱动或 %Q 标注） *)
Open Scope nat_scope.

(* ============================================================ *)
(* §0 Q 层搜索谓词内核：幂 + Qle_bool 桥 + 单调                          *)
(* ============================================================ *)

(* Q 幂（nat 指数，透明可计算——搜索谓词的计算内核，本席自带） *)
Fixpoint cl_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => (1#1)
  | Datatypes.S m => a * cl_qpow a m
  end.

Lemma cl_qpow_nonneg : forall (q : Q), Qle 0 q ->
  forall m : nat, Qle 0 (cl_qpow q m).
Proof.
  intros q H0 m. induction m as [| m IH].
  - cbn [cl_qpow]. unfold Qle. cbn. lia.
  - cbn [cl_qpow].
    assert (Hs : Qle (0 * cl_qpow q m)%Q (q * cl_qpow q m)%Q)
      by (apply (Qmult_le_compat_r 0 q (cl_qpow q m) H0 IH)).
    assert (E0 : (0 * cl_qpow q m)%Q == 0%Q) by ring.
    rewrite <- E0. exact Hs.
Qed.

(* Qeq -> Qle（stdlib 换形，免基座名） *)
Lemma cl_qeq_le : forall x y : Q, x == y -> Qle x y.
Proof. intros x y H. rewrite H. apply Qle_refl. Qed.

(* 左乘保序（Qmult_le_compat_r 经交换换形装配，显式 args） *)
Lemma cl_qmult_le_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H H0.
  apply (Qle_trans (z * x) (x * z) (z * y)).
  - apply cl_qeq_le. apply Qmult_comm.
  - apply (Qle_trans (x * z) (y * z) (z * y)).
    + exact (Qmult_le_compat_r x y z H H0).
    + apply cl_qeq_le. apply Qmult_comm.
Qed.

(* Qle_bool 双桥（本版 Qle_bool 终形 = Z 层 Qnum/QDen <=?，实测定谳；
   Z.leb_le / Z.leb_gt 直桥，零内部形赌运气） *)
Lemma cl_qle_bool_true : forall x y : Q, Qle_bool x y = true -> Qle x y.
Proof.
  intros x y H. unfold Qle_bool in H. simpl in H.
  unfold Qle. apply Z.leb_le. exact H.
Qed.

Lemma cl_qle_bool_false : forall x y : Q, Qle_bool x y = false -> Qlt y x.
Proof.
  intros x y H. unfold Qle_bool in H. simpl in H.
  unfold Qlt. apply Z.leb_gt. exact H.
Qed.

(* 正向桥：Qle -> Qle_bool true（Z.leb 双向 + lia 收矛盾） *)
Lemma cl_qle_bool_of_qle : forall x y : Q, Qle x y -> Qle_bool x y = true.
Proof.
  intros x y H. unfold Qle in H. unfold Qle_bool.
  destruct (Z.leb (Qnum x * QDen y) (Qnum y * QDen x)) eqn:E.
  - reflexivity.
  - exfalso. apply Z.leb_gt in E. lia.
Qed.

(* 幂列指数递减：m <= m' 时 q^m' <= q^m（0<=q<=1；沿 le 归纳） *)
Lemma cl_qpow_decr : forall (q : Q), Qle 0 q -> Qle q 1 ->
  forall m m' : nat, Nat.le m m' -> Qle (cl_qpow q m') (cl_qpow q m).
Proof.
  intros q H0 H1 m m' Hle. induction Hle as [| m' Hle IH].
  - apply Qle_refl.
  - cbn [cl_qpow].
    apply (Qle_trans (q * cl_qpow q m') (q * cl_qpow q m) (cl_qpow q m)).
    + exact (cl_qmult_le_l (cl_qpow q m') (cl_qpow q m) q IH H0).
    + apply (Qle_trans (q * cl_qpow q m) (1 * cl_qpow q m) (cl_qpow q m)).
      * exact (Qmult_le_compat_r q 1 (cl_qpow q m) H1
                 (cl_qpow_nonneg q H0 m)).
      * rewrite Qmult_1_l. apply Qle_refl.
Qed.

(* 柯西设计形搜索谓词：站 j 通过 ⟺ q1^j·M <= T。判定全在 Q 层。 *)
Definition cl_cond (q1 M T : Q) (j : nat) : bool :=
  Qle_bool (cl_qpow q1 j * M) T.

(* 代理谓词单调（通过站向上闭合） *)
Lemma cl_cond_mono : forall (q1 M T : Q),
  Qle 0 q1 -> Qle q1 1 -> Qle 0 M ->
  forall j j' : nat, Nat.le j j' ->
  cl_cond q1 M T j = true -> cl_cond q1 M T j' = true.
Proof.
  intros q1 M T Hq0 Hq1 HM0 j j' Hjj Hj.
  unfold cl_cond in Hj |- *.
  apply cl_qle_bool_of_qle.
  apply (Qle_trans (cl_qpow q1 j' * M) (cl_qpow q1 j * M) T).
  - apply (Qmult_le_compat_r (cl_qpow q1 j') (cl_qpow q1 j) M).
    + apply (cl_qpow_decr q1 Hq0 Hq1 j j' Hjj).
    + exact HM0.
  - apply cl_qle_bool_true in Hj. exact Hj.
Qed.

(* ============================================================ *)
(* §1 二分核（自带）：fuel 结构递归 + 区间折半 + 双账 spec               *)
(* ============================================================ *)

(* 二分核：fuel 每步减一（结构性终止），区间每步折半（mid 取中）。     *)
(*   f=0 或 lo=hi 直接回 lo；否则测 mid：通过收左 [lo,mid]，           *)
(*   失败收右 [S mid,hi]。判定谓词 cond 由 Q 层实例（§0/§3）供给。      *)
Fixpoint cl_bsearch (cond : nat -> bool) (f lo hi : nat) {struct f} : nat :=
  match f with
  | Datatypes.O => lo
  | Datatypes.S f' =>
      if Nat.eqb lo hi then lo
      else if cond (Nat.div2 (Nat.add lo hi))
        then cl_bsearch cond f' lo (Nat.div2 (Nat.add lo hi))
        else cl_bsearch cond f' (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi
  end.

(* 双账 spec（柯西设计形显式化：找到最小通过站，或诚实报告区间无解）。 *)
(*   fuel 不变式 S (hi - lo) <= 2^f：区间每步折半，2^f 步必解决。        *)
Theorem cl_bsearch_dual : forall (cond : nat -> bool) (f : nat),
  (forall a b : nat, Nat.le a b -> cond a = true -> cond b = true) ->
  forall lo hi : nat,
  Nat.le lo hi ->
  Nat.le (Datatypes.S (Nat.sub hi lo)) (Nat.pow 2 f) ->
  (cond hi = true /\
   cond (cl_bsearch cond f lo hi) = true /\
   (forall j : nat, Nat.le lo j ->
      Nat.lt j (cl_bsearch cond f lo hi) -> cond j = false))
  \/ (cond hi = false /\
      cond (cl_bsearch cond f lo hi) = false /\
      (forall j : nat, Nat.le lo j -> Nat.le j hi -> cond j = false)).
Proof.
  intros cond f Hmono.
  induction f as [| f IH]; intros lo hi Hlo Hfuel.
  - (* f = 0：燃料界逼 hi = lo，直接回 lo *)
    simpl in Hfuel. assert (Elo : lo = hi) by lia.
    rewrite Elo. cbn [cl_bsearch].
    destruct (cond hi) eqn:Hc.
    + left. split; [reflexivity | split].
      * reflexivity.
      * intros j Hjl Hjlt. exfalso. lia.
    + right. split; [reflexivity | split].
      * reflexivity.
      * intros j Hjl Hjh. assert (Hjeq : j = hi) by lia.
        rewrite Hjeq. exact Hc.
  - cbn [cl_bsearch]. destruct (Nat.eqb lo hi) eqn:Eeq.
    + (* lo = hi：单点区间，双账按该点真伪分流 *)
      apply Nat.eqb_eq in Eeq. rewrite Eeq.
      destruct (cond hi) eqn:Hc.
      * left. split; [reflexivity | split].
        -- reflexivity.
        -- intros j Hjl Hjlt. exfalso. lia.
      * right. split; [reflexivity | split].
        -- reflexivity.
        -- intros j Hjl Hjh. assert (Hjeq : j = hi) by lia.
           rewrite Hjeq. exact Hc.
    + (* lo < hi：取中折半 *)
      apply Nat.eqb_neq in Eeq.
      assert (Hlt : Nat.lt lo hi) by lia.
      assert (Hd2 : Nat.div2 (Nat.add lo hi) = Nat.div (Nat.add lo hi) 2)
        by apply Nat.div2_div.
      rewrite Hd2.
      pose proof (Nat.mod_upper_bound (Nat.add lo hi) 2 ltac:(lia)) as Hmod.
      pose proof (Nat.div_mod (Nat.add lo hi) 2 ltac:(lia)) as Hdm.
      assert (Hmod0 : Nat.le 0 (Nat.modulo (Nat.add lo hi) 2))
        by (apply Nat.le_0_l).
      assert (Hmlo : Nat.le lo (Nat.div (Nat.add lo hi) 2)) by lia.
      assert (Hmhi : Nat.lt (Nat.div (Nat.add lo hi) 2) hi) by lia.
      rewrite Nat.pow_succ_r' in Hfuel.
      destruct (cond (Nat.div (Nat.add lo hi) 2)) eqn:Ht.
      * (* mid 通过：单调推 hi 通过，收左区间，双账落左支 *)
        assert (Hhit : cond hi = true).
        { apply (Hmono (Nat.div (Nat.add lo hi) 2) hi
                    (Nat.lt_le_incl _ _ Hmhi) Ht). }
        assert (Hf1 : Nat.le (Datatypes.S
                          (Nat.sub (Nat.div (Nat.add lo hi) 2) lo))
                        (Nat.pow 2 f)) by lia.
        destruct (IH lo (Nat.div (Nat.add lo hi) 2) Hmlo Hf1)
          as [[Htop [Hok Hmin]] | [Hf1' [Hf2' Hf3']]];
          [| exfalso; congruence].
        left. split; [exact Hhit | split; [exact Hok | exact Hmin]].
      * (* mid 失败：收右区间；below-mid 全败账先行 *)
        assert (Hbl : forall j : nat, Nat.le lo j ->
                   Nat.lt j (Datatypes.S (Nat.div (Nat.add lo hi) 2)) ->
                   cond j = false).
        { intros j Hjl Hjlt.
          destruct (Nat.lt_ge_cases j (Nat.div (Nat.add lo hi) 2))
            as [Hltj | Hgej].
          - destruct (cond j) eqn:Htj; [| reflexivity].
            assert (Htm2 : cond (Nat.div (Nat.add lo hi) 2) = true)
              by (apply (Hmono j (Nat.div (Nat.add lo hi) 2));
                    [lia | exact Htj]).
            rewrite Ht in Htm2. discriminate Htm2.
          - assert (Heq : j = Nat.div (Nat.add lo hi) 2) by lia.
            rewrite Heq. exact Ht. }
        assert (Hf2 : Nat.le (Datatypes.S (Nat.sub hi
                          (Datatypes.S (Nat.div (Nat.add lo hi) 2))))
                        (Nat.pow 2 f)) by lia.
        destruct (cond hi) eqn:Hc.
        -- (* hi 通过：右区间递归回左支；below 账与 IH 最小账缝合 *)
           destruct (IH (Datatypes.S (Nat.div (Nat.add lo hi) 2)) hi
                       ltac:(lia) Hf2)
             as [[Htop [Hok Hmin]] | [Hg1 [Hg2 Hg3]]];
             [| exfalso; congruence].
           left. split; [reflexivity | split; [exact Hok |]].
           intros j Hjl Hjlt.
           destruct (Nat.lt_ge_cases j
                       (Datatypes.S (Nat.div (Nat.add lo hi) 2)))
             as [Hltj | Hgej].
           ++ apply Hbl; [exact Hjl | exact Hltj].
           ++ apply Hmin; [lia | exact Hjlt].
        -- (* hi 失败：诚实无解账（区间内无通过站） *)
           destruct (IH (Datatypes.S (Nat.div (Nat.add lo hi) 2)) hi
                       ltac:(lia) Hf2)
             as [[Hh1 [Hh2 Hh3]] | [Hh1 [Hh2 Hh3]]].
           ++ exfalso. rewrite Hc in Hh1. discriminate Hh1.
           ++ right. split; [reflexivity | split; [exact Hh2 |]].
              intros j Hjl Hjh.
              destruct (Nat.lt_ge_cases j
                          (Datatypes.S (Nat.div (Nat.add lo hi) 2)))
                as [Hltj | Hgej].
              ** apply Hbl; [exact Hjl | exact Hltj].
              ** apply Hh3; [lia | exact Hjh].
Qed.

(* ============================================================ *)
(* §2 对数返回界显式化（对标 rb_fuel_ge / rb_log_return_bound）          *)
(* ============================================================ *)

(* 燃料充分性（0 < j0）：S j0 <= 2^(log2 j0 + 2)，纯 nat 算术链        *)
(*   （与 rb_fuel_ge 同构：log2_spec 上下界夹逼 + pow_add_r 摊平）       *)
Lemma cl_fuel_ge_pos : forall j0 : nat,
  0 < j0 -> Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0 Hj0.
  destruct (Nat.log2_spec j0 Hj0) as [Hlo Hhi].
  replace (Nat.log2 j0 + 2) with (Nat.log2 j0 + 1 + 1) by lia.
  rewrite Nat.pow_add_r. rewrite Nat.pow_add_r.
  cbn [Nat.pow].
  replace (Datatypes.S (Nat.log2 j0)) with (Nat.log2 j0 + 1) in Hhi by lia.
  rewrite Nat.pow_add_r in Hhi. cbn [Nat.pow] in Hhi.
  lia.
Qed.

(* 对标 rb_log_return_bound（signature 逐字同形，j0=0 含） *)
Theorem cl_log_return_bound : forall j0 : nat,
  Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0. destruct j0 as [| j0'].
  - replace (Nat.log2 0 + 2) with 2 by (cbn; lia).
    cbn [Nat.pow]. lia.
  - apply (cl_fuel_ge_pos (Datatypes.S j0') (Nat.lt_0_succ j0')).
Qed.

(* [0, j0] 区间燃料条件换形（sub 0 消去） *)
Lemma cl_fuel_sub : forall j0 : nat,
  Nat.le (Datatypes.S (Nat.sub j0 0)) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof. intros j0. rewrite Nat.sub_0_r. apply cl_log_return_bound. Qed.

(* fuel = log2 j0 + 2 的 [0, j0] 搜索（对标 rb_bishop_search 装配位） *)
Definition cl_bsearch_log (cond : nat -> bool) (j0 : nat) : nat :=
  cl_bsearch cond (Nat.log2 j0 + 2) 0 j0.

(* 通过 + 最小账（对标 rb_bishop_search_ok：顶站为真时搜索给最小通过站） *)
Theorem cl_bsearch_ok : forall (cond : nat -> bool) (j0 : nat),
  (forall a b : nat, Nat.le a b -> cond a = true -> cond b = true) ->
  cond j0 = true ->
  cond (cl_bsearch cond (Nat.log2 j0 + 2) 0 j0) = true /\
  (forall j : nat, Nat.lt j (cl_bsearch cond (Nat.log2 j0 + 2) 0 j0) ->
     cond j = false).
Proof.
  intros cond j0 Hmono Hhi.
  destruct (cl_bsearch_dual cond (Nat.log2 j0 + 2) Hmono 0 j0
              (Nat.le_0_l j0) (cl_fuel_sub j0))
    as [[H1 [H2 H3]] | [H1 [H2 H3]]].
  - split; [exact H2 |].
    intros j Hj. apply (H3 j (Nat.le_0_l j) Hj).
  - exfalso. rewrite Hhi in H1. discriminate H1.
Qed.

(* ============================================================ *)
(* 主定理：对数性显式寄存于二分本体                                      *)
(*   第一账 = 双账 spec（通过+最小 或 诚实无解，柯西设计形）；           *)
(*   第二账 = 显式对数返回界 S j0 <= 2^(log2 j0 + 2)（对标 Bishop）。    *)
(* ============================================================ *)
Theorem cl_bsearch_log_bound : forall (cond : nat -> bool) (j0 : nat),
  (forall a b : nat, Nat.le a b -> cond a = true -> cond b = true) ->
  ((cond j0 = true /\
    cond (cl_bsearch_log cond j0) = true /\
    (forall j : nat, Nat.lt j (cl_bsearch_log cond j0) -> cond j = false))
   \/ (cond j0 = false /\
       cond (cl_bsearch_log cond j0) = false /\
       (forall j : nat, Nat.le j j0 -> cond j = false)))
  /\ Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros cond j0 Hmono. split.
  - unfold cl_bsearch_log.
    destruct (cl_bsearch_dual cond (Nat.log2 j0 + 2) Hmono 0 j0
                (Nat.le_0_l j0) (cl_fuel_sub j0))
      as [[H1 [H2 H3]] | [H1 [H2 H3]]].
    + left. split; [exact H1 | split; [exact H2 |]].
      intros j Hj. apply (H3 j (Nat.le_0_l j) Hj).
    + right. split; [exact H1 | split; [exact H2 |]].
      intros j Hj. apply (H3 j (Nat.le_0_l j) Hj).
  - apply cl_log_return_bound.
Qed.

(* ============================================================ *)
(* §3 柯西设计形实例：Qle_bool 幂余量谓词的装配                          *)
(* ============================================================ *)

Definition cl_find_qpow (q1 M T : Q) (j0 : nat) : nat :=
  cl_bsearch_log (cl_cond q1 M T) j0.

Theorem cl_find_qpow_spec : forall (q1 M T : Q) (j0 : nat),
  Qle 0 q1 -> Qle q1 1 -> Qle 0 M ->
  ((cl_cond q1 M T j0 = true /\
    cl_cond q1 M T (cl_find_qpow q1 M T j0) = true /\
    (forall j : nat, Nat.lt j (cl_find_qpow q1 M T j0) ->
       cl_cond q1 M T j = false))
   \/ (cl_cond q1 M T j0 = false /\
       cl_cond q1 M T (cl_find_qpow q1 M T j0) = false /\
       (forall j : nat, Nat.le j j0 -> cl_cond q1 M T j = false)))
  /\ Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros q1 M T j0 Hq0 Hq1 HM0.
  exact (cl_bsearch_log_bound (cl_cond q1 M T) j0
           (cl_cond_mono q1 M T Hq0 Hq1 HM0)).
Qed.

(* ============================================================ *)
(* 探针审计：提取 Obj.magic 计数应为 0 + 语句假设闭包                     *)
(* ============================================================ *)

Separate Extraction cl_qpow cl_cond cl_bsearch cl_bsearch_log cl_find_qpow.

Print Assumptions cl_bsearch_dual.
Print Assumptions cl_bsearch_ok.
Print Assumptions cl_bsearch_log_bound.
Print Assumptions cl_find_qpow_spec.
Print Assumptions cl_log_return_bound.
