(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(*                                                               *)
(* 目的：PolyIntegral 一期（Q 系数列表线性泛函 pint_integral）之上  *)
(*       的 P1 积分二期机——单调/正性双机，供候选一 Beukers 主线    *)
(* 四要素逐件声明（语句面 / 前提面 / 证明面 / 提取面）：            *)
(*  §1 pm_qleT'_mult_r / pm_qle_wd_l / pm_qle_wd_r：               *)
(*     语句面 QleT'（Set）；前提面 QleT' 与 Qeq（内部支撑件，       *)
(*     Qeq 仅证内）；证明面 Q 层单调 + Qeq 重写；提取面纯函数。      *)
(*  §2 pm_eval_ge0 / pm_eval_le0 / pm_pointwise_le_eval：           *)
(*     语句面全 QleT'（Set）；前提面逐系数 QleT' 全称 + QleT' 0 x，  *)
(*     零 Prop；证明面列表归纳 + 乘法右保序；提取面 eval 型纯函数。  *)
(*  §3 pm_monomial_int_nonpos / pm_integral_from_nonpos /           *)
(*     pm_pointwise_le_integral：语句面 QleT'（Set）；免等长前提     *)
(*     （越界系数 0 语义下四分支归纳，强于一期等长版）；证明面       *)
(*     Qplus_le_compat 双肢；提取面积分型纯函数。                   *)
(*  §4 pm_monomial_int_pos / pm_integral_from_pos_strict /          *)
(*     pm_integral_pos_strict / pm_integral_from_pos /              *)
(*     pm_integral_pos：语句面 QltT（Set）；严格性见证 sigT         *)
(*     （Set）承载，零 Prop；证明面 Qplus_lt_compat /               *)
(*     Qplus_lt_le_compat + sigT 索引三分（0/S/空反证灭）；          *)
(*     提取面积分型纯函数。                                         *)
(*  §5 pm_scale_mono / pm_add_mono：语句面 QleT'（Set）；前提面     *)
(*     QleT' + Id (length p) (length q)（Id:Set，S01，非 Prop eq）； *)
(*     证明面一期 pint_integral_scale / pint_integral_add 线性性    *)
(*     QeqT 换形 + Qmult_le_compat_r / qleT'_plus_compat；          *)
(*     提取面积分型纯函数。                                        *)
(* 红线：假设审计全空（六件主定理 Closed under the global          *)
(*       context，见文件尾 Print Assumptions 留痕）；无假公理位、    *)
(*       无未证闭合、无经典逻辑依赖。语句面零 Prop（Qeq/Qle 仅证内）；*)
(*       一期刊物 pint_integral_* 全部只使用不重编。诚实边界：真      *)
(*       「段上逐点正而系数任意」面需网格/Sturm 机器，超本期窗口，    *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.

(* ============================================================ *)
(* §1 QleT' 运算支撑小件（内部 Q 层，仅证内）                         *)
(* ============================================================ *)

(* QleT' 乘法右保序：a ≤ b、0 ≤ c ⟹ a·c ≤ b·c *)
Lemma pm_qleT'_mult_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  apply (Qmult_le_compat_r a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hc.
Qed.

(* QleT' 乘法左保序：a ≤ b、0 ≤ c ⟹ c·a ≤ c·b（经 Qmult_comm 桥） *)
Lemma pm_qleT'_mult_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  rewrite (Qmult_comm c a).
  rewrite (Qmult_comm c b).
  apply (Qmult_le_compat_r a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hc.
Qed.

(* QleT' 左端 Qeq 换形：x == y、QleT' x z ⟹ QleT' y z（内部件） *)
Lemma pm_qle_wd_l : forall x y z : Q, x == y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z Hxy Hxz. apply Qle_to_QleT'.
  rewrite <- Hxy. apply QleT'_to_Qle. exact Hxz.
Qed.

(* QleT' 右端 Qeq 换形：x == y、QleT' z x ⟹ QleT' z y（内部件） *)
Lemma pm_qle_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hzx. apply Qle_to_QleT'.
  rewrite <- Hxy. apply QleT'_to_Qle. exact Hzx.
Qed.

(* 乘法换形三件（wd 桥 + Qmult_comm 组装，绕开 Z 层 rewrite 匹配） *)
Lemma pm_mult_r0_le : forall b c : Q,
  QleT' 0 b -> QleT' 0 c -> QleT' 0 (c * b).
Proof.
  intros b c Hb Hc.
  apply (pm_qle_wd_l (0 * c) 0 (c * b)).
  - apply Qmult_0_l.
  - apply (pm_qle_wd_r (b * c) (c * b)).
    + apply Qmult_comm.
    + apply (pm_qleT'_mult_r 0 b c).
      * exact Hb.
      * exact Hc.
Qed.

Lemma pm_mult_r0_le0 : forall a c : Q,
  QleT' a 0 -> QleT' 0 c -> QleT' (c * a) 0.
Proof.
  intros a c Ha Hc.
  apply (pm_qle_wd_l (a * c) (c * a) 0).
  - apply Qmult_comm.
  - apply (pm_qle_wd_r (0 * c) 0).
    + apply Qmult_0_l.
    + apply (pm_qleT'_mult_r a 0 c).
      * exact Ha.
      * exact Hc.
Qed.

Lemma pm_qleT'_comm_l : forall a b c : Q,
  QleT' (a * c) (b * c) -> QleT' (c * a) (c * b).
Proof.
  intros a b c H. apply (pm_qle_wd_l (a * c) (c * a) (c * b)).
  - apply Qmult_comm.
  - apply (pm_qle_wd_r (b * c) (c * b)).
    + apply Qmult_comm.
    + exact H.
Qed.

(* Id (nat) 桥到 Prop eq（前提面 Set 化的唯一通道；仅证内） *)
Lemma pm_id_nat_eq : forall n m : nat, Id n m -> n = m.
Proof.
  intros n m H. case H. reflexivity.
Qed.

(* ============================================================ *)
(* §2 逐点求值面：系数级符号 ⟹ eval 符号（[0,1] 左端点非负即可）       *)
(* ============================================================ *)

(* 正系数 ⟹ eval ≥ 0（0 ≤ x） *)
Theorem pm_eval_ge0 : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  forall x : Q, QleT' 0 x -> QleT' 0 (pint_eval p x).
Proof.
  induction p as [| a p' IH]; intros Hcoeff x Hx.
  - apply qleT'_refl.
  - cbn [pint_eval pint_coeff].
    apply (qleT'_plus_compat 0 a 0 (x * pint_eval p' x)).
    + specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply pm_mult_r0_le.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- exact Hx.
      * exact Hx.
Qed.

(* 负系数（全 ≤ 0）⟹ eval ≤ 0（0 ≤ x） *)
Theorem pm_eval_le0 : forall p : list Q,
  (forall i : nat, QleT' (pint_coeff p i) 0) ->
  forall x : Q, QleT' 0 x -> QleT' (pint_eval p x) 0.
Proof.
  induction p as [| a p' IH]; intros Hcoeff x Hx.
  - apply qleT'_refl.
  - cbn [pint_eval pint_coeff].
    apply (qleT'_plus_compat a 0 (x * pint_eval p' x) 0).
    + specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply pm_mult_r0_le0.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- exact Hx.
      * exact Hx.
Qed.

(* 单调主件（逐点面）：逐系数 ≤ ⟹ ∀0≤x，eval p x ≤ eval q x。
   免等长前提：越界系数 0 语义下四分支归纳（强于一期等长版）。 *)
Theorem pm_pointwise_le_eval : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  forall x : Q, QleT' 0 x -> QleT' (pint_eval p x) (pint_eval q x).
Proof.
  induction p as [| a p' IH]; intros q Hcoeff x Hx.
  - destruct q as [| b q'].
    + apply qleT'_refl.
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat 0 b 0 (x * pint_eval q' x)).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_mult_r0_le.
        -- apply pm_eval_ge0.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
  - destruct q as [| b q'].
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat a 0 (x * pint_eval p' x) 0).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_mult_r0_le0.
        -- apply pm_eval_le0.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat a b (x * pint_eval p' x) (x * pint_eval q' x)).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_qleT'_comm_l.
        apply (pm_qleT'_mult_r (pint_eval p' x) (pint_eval q' x) x).
        -- apply IH.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
Qed.

(* ============================================================ *)
(* §3 积分单调面（免等长增强版）：逐系数 ≤ ⟹ ∫p ≤ ∫q                   *)
(* ============================================================ *)

(* 单项式非正：a ≤ 0 ⟹ a/(k+1) ≤ 0（同构一期 pint_monomial_int_nonneg） *)
Lemma pm_monomial_int_nonpos : forall (a : Q) (k : nat),
  QleT' a 0 -> QleT' (pint_monomial_int a k) 0.
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                   (0 * (1 / (Z.of_nat (Datatypes.S k) # 1))) 0).
  - apply (Qmult_le_compat_r a 0).
    + apply QleT'_to_Qle. exact Ha.
    + apply Qlt_le_weak. apply pint_invS_pos.
  - rewrite Qmult_0_l. apply Qle_refl.
Qed.

(* 全系数 ≤ 0 ⟹ 偏移积分 ≤ 0（归纳双肢） *)
Lemma pm_integral_from_nonpos : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' (pint_coeff p i) 0) ->
  QleT' (pint_integral_from p k) 0.
Proof.
  induction p as [| a p' IH]; intros k Hcoeff.
  - apply qleT'_refl.
  - cbn [pint_integral_from].
    apply (qleT'_plus_compat (pint_monomial_int a k) 0
                             (pint_integral_from p' (Datatypes.S k)) 0).
    + apply pm_monomial_int_nonpos.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 积分单调主件：逐系数 ≤（免等长，四分支）⟹ 偏移积分 ≤ *)
Lemma pm_integral_from_mono_gen : forall (p q : list Q) (k : nat),
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  induction p as [| a p' IH]; intros q k Hcoeff.
  - destruct q as [| b q'].
    + apply qleT'_refl.
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat 0 (pint_monomial_int b k)
                               0 (pint_integral_from q' (Datatypes.S k))).
      * apply pint_monomial_int_nonneg.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pint_integral_from_nonneg.
        intros i. specialize (Hcoeff (Datatypes.S i)).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat (pint_monomial_int a k) 0
                               (pint_integral_from p' (Datatypes.S k)) 0).
      * apply pm_monomial_int_nonpos.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_integral_from_nonpos.
        intros i. specialize (Hcoeff (Datatypes.S i)).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat (pint_monomial_int a k) (pint_monomial_int b k)
                             (pint_integral_from p' (Datatypes.S k))
                             (pint_integral_from q' (Datatypes.S k))).
      * apply Qle_to_QleT'.
        unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply pint_invS_pos.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 组装（0 偏移）：
   【pm_pointwise_le 主件】逐系数 ≤ ⟹ pint_integral p ≤ pint_integral q *)
Theorem pm_pointwise_le_integral : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hcoeff. unfold pint_integral.
  exact (pm_integral_from_mono_gen p q 0 Hcoeff).
Qed.


(* ============================================================ *)
(* §4 严格正机（QltT 面；见证 sigT 承载，零 Prop）                     *)
(* ============================================================ *)

(* 单项式严格正：0 < a ⟹ 0 < a/(k+1)（Qmult_lt_compat_r + Qmult_0_l 换左端） *)
Lemma pm_monomial_int_pos : forall (a : Q) (k : nat),
  QltT 0 a -> QltT 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qlt_to_QltT.
  unfold pint_monomial_int, Qdiv.
  assert (H0 : 0 * (1 / (Z.of_nat (Datatypes.S k) # 1))
               < a * (1 / (Z.of_nat (Datatypes.S k) # 1))).
  { apply (Qmult_lt_compat_r 0 a (1 / (Z.of_nat (Datatypes.S k) # 1))).
    - apply pint_invS_pos.
    - apply QltT_to_Qlt. exact Ha. }
  rewrite Qmult_0_l in H0. exact H0.
Qed.

(* 全系数严格正 ⟹ 偏移积分严格正（归纳；空列表前提 QltT 0 0 型无人居，
   同型恒等闭合——前提假设即结论型，非爆炸） *)
Lemma pm_integral_from_pos_strict : forall (p : list Q) (k : nat),
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral_from p k).
Proof.
  induction p as [| a p' IH]; intros k Hcoeff.
  - cbn [pint_integral_from]. specialize (Hcoeff 0%nat).
    cbn [pint_coeff] in Hcoeff. exact Hcoeff.
  - cbn [pint_integral_from].
    apply Qlt_to_QltT. apply (Qplus_lt_compat
      (0) (pint_monomial_int a k)
      (0) (pint_integral_from p' (Datatypes.S k))).
    + apply QltT_to_Qlt. apply pm_monomial_int_pos.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QltT_to_Qlt. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 组装：全系数严格正 ⟹ ∫p 严格正 *)
Theorem pm_integral_pos_strict : forall p : list Q,
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral p).
Proof.
  intros p H. unfold pint_integral.
  exact (pm_integral_from_pos_strict p 0 H).
Qed.


(* 严格正见证的偏移归纳主件：全系数非负 + sigT 见证（某系数严格正）
   ⟹ 偏移积分严格正。sigT 索引三分（0 ⟹ 头严格；S i' ⟹ 尾归纳；
   空表 ⟹ 见证型不可满足灭）。 *)
Lemma pm_integral_from_pos : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  sigT (fun i => QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral_from p k).
Proof.
  induction p as [| a p' IH]; intros k Hcoeff Hwit.
  - destruct Hwit as [i Hi].
    cbn [pint_integral_from]. cbn [pint_coeff] in Hi. exact Hi.
  - destruct Hwit as [i Hi]. destruct i as [| i].
    + (* 头严格 + 尾非负 *)
      cbn [pint_coeff] in Hi. cbn [pint_integral_from].
      apply Qlt_to_QltT.
      apply (Qplus_lt_le_compat 0 (pint_monomial_int a k)
                               0 (pint_integral_from p' (Datatypes.S k))).
      * apply QltT_to_Qlt. apply pm_monomial_int_pos. exact Hi.
      * apply QleT'_to_Qle. apply pint_integral_from_nonneg.
        intros i'. specialize (Hcoeff (Datatypes.S i')).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + (* 头非负 + 尾严格正：Qplus_le_lt 型经 Qplus_comm 重写链落到
         Qplus_lt_le_compat（stdlib 无 le_lt 版，右端项序固定所致） *)
      cbn [pint_coeff] in Hi. cbn [pint_integral_from].
      assert (Htail : QltT 0 (pint_integral_from p' (Datatypes.S k))).
      { apply IH.
        - intros i'. specialize (Hcoeff (Datatypes.S i')).
          cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        - exact (existT (fun j => QltT 0 (pint_coeff p' j)) i Hi). }
      apply Qlt_to_QltT.
      rewrite <- (Qplus_0_l 0).
      rewrite (Qplus_comm (pint_monomial_int a k)
                          (pint_integral_from p' (Datatypes.S k))).
      apply (Qplus_lt_le_compat 0 (pint_integral_from p' (Datatypes.S k))
                               0 (pint_monomial_int a k)).
      * apply QltT_to_Qlt. exact Htail.
      * apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 组装：【pm_pointwise_pos 主件】全系数非负 + 某系数严格正（sigT 见证）
   ⟹ ∫p 严格正。
   与 §4 strict 件合构「非负 + 某点严格正」分解的系数级可达面；
   候选一被积函数 (1−t/2)^{−(n+1)} 的 Taylor 截断为全正系数形，
   strict 件直接适用；任意位见证由本件 sigT 面承担。 *)
Theorem pm_integral_pos : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  sigT (fun i => QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral p).
Proof.
  intros p Hcoeff Hwit. unfold pint_integral.
  exact (pm_integral_from_pos p 0 Hcoeff Hwit).
Qed.


(* ============================================================ *)
(* §5 线性两件（Beukers 恒等式链用；一期线性性只使用不重编）            *)
(* ============================================================ *)

(* 数乘单调：0 ≤ a、∫p ≤ ∫q ⟹ ∫(a·p) ≤ ∫(a·q)
   （pint_integral_scale QeqT 双端换形 + Qmult_le_compat_r） *)
Theorem pm_scale_mono : forall (a : Q) (p q : list Q),
  QleT' 0 a ->
  QleT' (pint_integral p) (pint_integral q) ->
  QleT' (pint_integral (pint_scale a p)) (pint_integral (pint_scale a q)).
Proof.
  intros a p q Ha Hipq.
  apply (pm_qle_wd_l (a * pint_integral p) (pint_integral (pint_scale a p))).
  - apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_scale.
  - apply (pm_qle_wd_r (a * pint_integral q) (pint_integral (pint_scale a q))).
    + apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_scale.
    + apply pm_qleT'_mult_l.
      * exact Hipq.
      * exact Ha.
Qed.

(* 加法单调：add 内部等长（Id:Set 面，p~r 与 q~s 配对）+ ∫p ≤ ∫q、
   ∫r ≤ ∫s ⟹ ∫(p+r) ≤ ∫(q+s)
   （pint_integral_add QeqT 双端换形 + qleT'_plus_compat） *)
Theorem pm_add_mono : forall p q r s : list Q,
  Id (length p) (length r) -> Id (length q) (length s) ->
  QleT' (pint_integral p) (pint_integral q) ->
  QleT' (pint_integral r) (pint_integral s) ->
  QleT' (pint_integral (pint_add p r)) (pint_integral (pint_add q s)).
Proof.
  intros p q r s Hpr Hqs Hipq Hirs.
  apply (pm_qle_wd_l (pint_integral p + pint_integral r)
                     (pint_integral (pint_add p r))).
  - apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_add.
    apply pm_id_nat_eq. exact Hpr.
  - apply (pm_qle_wd_r (pint_integral q + pint_integral s)
                       (pint_integral (pint_add q s))).
    + apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_add.
      apply pm_id_nat_eq. exact Hqs.
    + apply (qleT'_plus_compat (pint_integral p) (pint_integral q)
                             (pint_integral r) (pint_integral s)).
      * exact Hipq.
      * exact Hirs.
Qed.

(* ============================================================ *)
(* 提取检验 + 假设审计留痕（编译期 stdout，verify 复核）               *)
(* ============================================================ *)

Extraction "pintmono_extract.ml"
  pm_eval_ge0 pm_eval_le0 pm_pointwise_le_eval
  pm_pointwise_le_integral pm_integral_pos_strict pm_integral_pos
  pm_scale_mono pm_add_mono.

Print Assumptions pm_pointwise_le_eval.
Print Assumptions pm_pointwise_le_integral.
Print Assumptions pm_integral_pos_strict.
Print Assumptions pm_integral_pos.
Print Assumptions pm_scale_mono.
Print Assumptions pm_add_mono.
