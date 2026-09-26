(* ============================================================ *)
(* UpReqBanachExpAddEq.v —— 席EXPADD2：S3 exp_add 等式形总装       *)
(* (20260913，路径 B；闸门 UNQ+CBR 双开 04:26 确认后直接总装)        *)
(* ============================================================ *)
(* 使命主件：bxae_exp_add                                         *)
(*   bae (bxdef_emul (bxdef_exp a) (bxdef_exp b))                *)
(*       (bxdef_exp (a+b))    （hab 交换面；零假设形见尾注）        *)
(* 六环接线：                                                     *)
(*   ① bnh_esp_term_binom（BanachNoHyp，(a+b)^k 项二项式形零假设）  *)
(*   ② esp_as_bsum/bpa_bsum_mult_r（方块行形，UpReqBanachProd/Add） *)
(*   ③ bxcb_term_split_binom（UpReqBanachBinomBridge 系数桥）      *)
(*   ④ esp_diff_le_tail（UpReqBanachExp 尾界）+ 块和→0（本席新建）  *)
(*   ⑤ bxadd_esp_prod_blim（UpReqBanachExpAdd 部分积序列极限）      *)
(*   ⑥ bxuq_lim_uniq（UpReqBanachLimUniq 极限唯一性）              *)
(* 工艺：行形三角 bxae_tri_row（自建归纳，免 bd2 转置）+ 差=块和     *)
(*   分解 bxae_diff_block + 分窗 Q 记账 bxae_qblock_small。         *)
(* 红线自审：纯构造性（无公理/承认件/弃证面/经典逻辑）；语句面 Set   *)
(*   层（bae/blim/sigT），Q 层 Prop 仅引擎内衬；禁词条口径含注释——   *)
(*   本头注已用「公理/承认件/弃证面」字面。                          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachAdd.
Require Import UpReqBanachProd.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
Require Import UpReqBanachBinomBridge.
Require Import UpReqNormConv.
Require Import BanachNoHyp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Lia.

(* ============================================================ *)
(* S0：bxdef_emul——exp 元素乘法（主件左元接线位；普查全树无先名）    *)
(* ============================================================ *)

Definition bxdef_emul (B : BanachAlg) (x y : (@BA B)) : (@BA B) :=
  @bmult B x y.

(* ============================================================ *)
(* S1：Q 层工具件（Prop 引擎内衬，零 lia）                          *)
(* ============================================================ *)

Lemma bxae_1p1_neq_0 : ~ ((1 + 1)%Q == 0)%Q.
Proof. intros Hz. vm_compute in Hz. discriminate. Qed.

Lemma bxae_qlt_0_1 : Qlt 0 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qlt_0_2 : Qlt 0 (1 + 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qltT_0_1 : QltT 0 1%Q.
Proof. apply Qlt_to_QltT. exact bxae_qlt_0_1. Qed.

(* x ≤ x + y（0 ≤ y） *)
Lemma bxae_Qle_add_r : forall x y : Q, Qle 0 y -> Qle x (x + y)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (x + y)%Q).
  - apply qeq_imp_qle. ring.
  - apply (Qle_trans (0 + x)%Q (y + x)%Q (x + y)%Q).
    + apply (Qplus_le_compat 0%Q y x x).
      * exact Hy.
      * apply Qle_refl.
    + apply qeq_imp_qle. ring.
Qed.

(* x ≤ y + x（0 ≤ y） *)
Lemma bxae_Qle_add_l : forall x y : Q, Qle 0 y -> Qle x (y + x)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (y + x)%Q).
  - apply qeq_imp_qle. ring.
  - apply (Qplus_le_compat 0%Q y x x).
    + exact Hy.
    + apply Qle_refl.
Qed.

(* 1 ≤ 2 *)
Lemma bxae_Qle_1_2 : Qle 1%Q (1 + 1)%Q.
Proof. apply bxae_Qle_add_r. apply Qle_0_1. Qed.

(* 右乘严格单调（Qmult_lt_r iff 面） *)
Lemma bxae_mult_lt_r : forall x y z : Q,
  Qlt x y -> Qlt 0 z -> Qlt (x * z) (y * z)%Q.
Proof.
  intros x y z Hxy Hz.
  exact (proj2 (Qmult_lt_r x y z Hz) Hxy).
Qed.

(* 域律消去：e·/(y·x)·x == e·/y *)
Lemma bxae_cancel_mul : forall e x y : Q,
  ~ (y == 0) -> ~ (y * x == 0) -> (e * / (y * x)) * x == e * / y.
Proof.
  intros e x y Hy Hyx.
  assert (Hx0 : ~ (x == 0)).
  { intros Hx. apply Hyx. rewrite Hx. ring. }
  field. split; assumption.
Qed.

(* 半和合并：e·/2 + e·/2 == e *)
Lemma bxae_half_add : forall e : Q, (e * / (1 + 1) + e * / (1 + 1))%Q == e%Q.
Proof. intros e. field. Qed.

(* 级数项非负：0 ≤ X^k/k! *)
Lemma bxae_term_nonneg : forall (X : Q) (k : nat),
  Qle 0 X -> Qle 0 (q_pow X k / q_fact k)%Q.
Proof.
  intros X k HX. unfold Qdiv.
  assert (Hinv : Qlt 0 (Qinv (q_fact k)))
    by (apply Qinv_lt_0_compat; apply q_fact_pos).
  apply (Qle_trans 0%Q (0 * Qinv (q_fact k))%Q
                   (q_pow X k * Qinv (q_fact k))%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (proj2 (Qmult_le_r 0 (q_pow X k) (Qinv (q_fact k)) Hinv)).
    apply (q_pow_nonneg X k HX).
Qed.

(* 尾和非负 *)
Lemma bxae_etab_nonneg : forall (X : Q) (m n : nat),
  Qle 0 X -> Qle 0 (exp_tail_abs m n X).
Proof.
  intros X m n HX. induction n as [| n' IH].
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m (Datatypes.S n') X)
      with (exp_tail_abs m n' X
            + (if Nat.leb m n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m n').
    + apply (Qplus_le_compat 0%Q (exp_tail_abs m n' X) 0%Q
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      * exact IH.
      * exact (bxae_term_nonneg X (Datatypes.S n') HX).
    + apply (Qle_trans 0%Q (exp_tail_abs m n' X) (exp_tail_abs m n' X + 0)%Q).
      * exact IH.
      * apply qeq_imp_qle. symmetry. apply Qplus_0_r.
Qed.


(* 尾和对起点反单调：m1 ≤ m2 ⟹ tail(m2..n) ≤ tail(m1..n) *)
Lemma bxae_etab_mono_start : forall (X : Q) (m1 m2 n : nat),
  Qle 0 X -> (m1 <= m2)%nat -> Qle (exp_tail_abs m2 n X) (exp_tail_abs m1 n X).
Proof.
  intros X m1 m2 n HX Hm. revert m1 m2 Hm.
  induction n as [| n' IH]; intros m1 m2 Hm.
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m1 (Datatypes.S n') X)
      with (exp_tail_abs m1 n' X
            + (if Nat.leb m1 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    change (exp_tail_abs m2 (Datatypes.S n') X)
      with (exp_tail_abs m2 n' X
            + (if Nat.leb m2 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m2 n') eqn:Em2.
    { assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      apply (Qplus_le_compat (exp_tail_abs m2 n' X) (exp_tail_abs m1 n' X)
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      - exact (IH m1 m2 Hm).
      - apply (Qle_refl (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))). }
    { assert (E0 : (exp_tail_abs m2 n' X + 0)%Q == exp_tail_abs m2 n' X) by ring.
      apply (Qle_trans _ (exp_tail_abs m1 n' X)).
      - apply (Qle_trans _ (exp_tail_abs m2 n' X)).
        + exact (qeq_imp_qle _ _ E0).
        + exact (IH m1 m2 Hm).
      - apply bxae_Qle_add_r. destruct (Nat.leb m1 n').
        + exact (bxae_term_nonneg X (Datatypes.S n') HX).
        + apply Qle_refl. }
Qed.
(* 尾和分裂可加：tail(m1..n) == tail(m1..m2) + tail(m2..n) *)
Lemma bxae_etab_split : forall (X : Q) (m1 m2 n : nat),
  (m1 <= m2)%nat -> (m2 <= n)%nat ->
  exp_tail_abs m1 n X == (exp_tail_abs m1 m2 X + exp_tail_abs m2 n X)%Q.
Proof.
  intros X m1 m2 n Hm12 Hm2n. revert m1 m2 Hm12 Hm2n.
  induction n as [| n' IH]; intros m1 m2 Hm12 Hm2n.
  - assert (Hm20 : m2 = 0%nat) by lia. subst m2.
    assert (Hm10 : m1 = 0%nat) by lia. subst m1.
    simpl. ring.
  - destruct (Nat.leb m2 n') eqn:Em2.
    + assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      change (exp_tail_abs m1 (Datatypes.S n') X)
        with (exp_tail_abs m1 n' X
              + (if Nat.leb m1 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      change (exp_tail_abs m2 (Datatypes.S n') X)
        with (exp_tail_abs m2 n' X
              + (if Nat.leb m2 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      rewrite (IH m1 m2 Hm12 Hm2n').
      rewrite Em2.
      set (T := (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
      ring.
    + assert (Hlt : (n' < m2)%nat) by (apply Nat.leb_gt; exact Em2).
      assert (Hm2 : m2 = Datatypes.S n') by lia. subst m2.
      rewrite (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n') X
                 (Nat.le_refl _)).
      ring.
Qed.

(* 尾和任意小：∃N，m ≥ N ⟹ tail(m..n) < e（任意 n） *)
Lemma bxae_etab_small : forall (X e : Q),
  Qle 0 X -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat ->
    Qlt (exp_tail_abs m n X) e).
Proof.
  intros X e HX Heps.
  destruct (q_arch_geom X) as [N0 HN0].
  assert (Harch : forall u : nat, (N0 <= u)%nat ->
            Qle (Qmult (1 + 1)%Q X) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (H0C : QleT' 0 ((q_pow X N0 / q_fact N0) * (1 + 1))%Q).
  { apply Qle_to_QleT'. apply (q_pow_fact2_nonneg X N0 HX). }
  destruct (arch_decay ((q_pow X N0 / q_fact N0) * (1 + 1)%Q) e H0C Heps)
    as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm.
  destruct (Nat.leb m n) eqn:Emn.
  - apply Nat.leb_le in Emn.
    apply (Qle_lt_trans _ ((q_pow X m / q_fact m) * (1 + 1)%Q) e).
    + exact (exp_tail_abs_geom2 X m n HX (fun t0 Ht => Harch t0 (Nat.le_trans N0 m t0 ltac:(lia) Ht)) Emn).
    + apply (exp_tail_arch X N0 t m e HX Harch (QltT_to_Qlt 0 e Heps)
               (QltT_to_Qlt _ _ Hdec)).
      lia.
  - apply Nat.leb_gt in Emn.
    assert (Hnm : (n <= m)%nat) by lia.
    rewrite (exp_tail_abs_le_m m n X Hnm).
    exact (QltT_to_Qlt 0 e Heps).
Qed.

(* α 部分和 == 1 + 尾（α_k := X^k/k!） *)
Lemma bxae_ncvsum_alpha : forall (X : Q) (n : nat),
  ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n)
  == (1 + exp_tail_abs 0 n X)%Q.
Proof.
  intros X n. induction n as [| n' IH].
  - simpl. unfold Qdiv. vm_compute. reflexivity.
  - change (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
              (Datatypes.S (Datatypes.S n')))
      with (ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n')
            + (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
    rewrite IH.
    change (exp_tail_abs 0 (Datatypes.S n') X)
      with (exp_tail_abs 0 n' X
            + (if Nat.leb 0 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    assert (H0b : Nat.leb 0 n' = true) by (apply Nat.leb_le; lia).
    rewrite H0b.
    ring.
Qed.

(* qsum 分裂（前窗 + 位移窗） *)
Lemma bxae_ncvsum_split_eq : forall (f : nat -> Q) (n1 d : nat),
  ncv_qsum f (Datatypes.S (n1 + d))%nat
  == (ncv_qsum f (Datatypes.S n1)
      + ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d)%Q.
Proof.
  intros f n1 d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) 0%nat)
      with 0%Q.
    ring.
  - replace ((n1 + Datatypes.S d')%nat) with (Datatypes.S (n1 + d')) by lia.
    change (ncv_qsum f (Datatypes.S (Datatypes.S (n1 + d'))))
      with (ncv_qsum f (Datatypes.S (n1 + d'))
            + f (Datatypes.S (n1 + d')))%Q.
    rewrite IH.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d'
            + f (Datatypes.S (n1 + d'))%Q).
    ring.
Qed.

(* 窗内逐点控制（range 限定前提，前窗点态界用） *)
Lemma bxae_ncvsum_le_ranged : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, (k < n)%nat -> QleT' (f k) (g k)) ->
  QleT' (ncv_qsum f n) (ncv_qsum g n).
Proof.
  intros f g n Hle. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. change (ncv_qsum g 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    change (ncv_qsum g (Datatypes.S m)) with (ncv_qsum g m + g m)%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + apply IH. intros k Hk. apply Hle. lia.
    + apply Hle. lia.
Qed.

(* 位移 α 窗和 == 尾和 *)
Lemma bxae_ncvsum_alpha_shift : forall (X : Q) (m d : nat),
  ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d
  == exp_tail_abs m (m + d)%nat X.
Proof.
  intros X m d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) 0%nat)
      with 0%Q.
    apply Qeq_sym. apply (exp_tail_abs_le_m m m X (Nat.le_refl _)).
  - replace ((m + Datatypes.S d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d'
            + (q_pow X (Datatypes.S m + d') / q_fact (Datatypes.S m + d'))%Q).
    change (exp_tail_abs m (Datatypes.S (m + d'))%nat X)
      with (exp_tail_abs m (m + d')%nat X
            + (if Nat.leb m (m + d')%nat
               then q_pow X (Datatypes.S (m + d'))%nat / q_fact (Datatypes.S (m + d'))%nat
               else 0)%Q).
    assert (Hleb : Nat.leb m (m + d')%nat = true)
      by (apply Nat.leb_le; lia).
    rewrite Hleb.
    replace ((Datatypes.S m + d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    rewrite IH. ring.
Qed.

(* 主 Q 件：块和任意小（Mertens 型分窗） *)
Lemma bxae_qblock_small : forall (X Y eps : Q),
  Qle 0 X -> Qle 0 Y -> QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (ncv_qsum (fun i : nat =>
           q_pow X i / q_fact i * exp_tail_abs (Nat.sub n i) n Y)
         (Datatypes.S n)) eps).
Proof.
  intros X Y eps HX HY He.
  (* Y 尾 < 1 阈 ⟹ 全局 β 和界 Bb *)
  destruct (bxae_etab_small Y 1%Q HY bxae_qltT_0_1) as [Ny Hy].
  assert (Hb : forall n : nat,
           Qle (1 + exp_tail_abs 0 n Y)%Q ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
  { intro n. destruct (Nat.leb_spec n Ny) as [Hle | Hgt].
    - assert (Hsp : exp_tail_abs 0 Ny Y
                    == (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)%Q)
        by (apply bxae_etab_split with (m2 := n); lia).
      rewrite Hsp.
      apply (Qplus_le_compat 1%Q (1 + 1)%Q
               (exp_tail_abs 0 n Y)
               (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)).
      + exact bxae_Qle_1_2.
      + apply bxae_Qle_add_r.
        exact (bxae_etab_nonneg Y n Ny HY).
    - assert (Hsp : exp_tail_abs 0 n Y
                    == (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y)%Q)
        by (apply bxae_etab_split with (m2 := Ny); lia).
      rewrite Hsp.
      assert (E1a : (1 + (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y))%Q
                    == ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q) by ring.
      apply (Qle_trans _ ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q).
      + exact (qeq_imp_qle _ _ E1a).
      + apply (Qplus_le_compat (1 + exp_tail_abs Ny n Y)%Q (1 + 1)%Q
                 (exp_tail_abs 0 Ny Y) (exp_tail_abs 0 Ny Y)).
        * apply (Qplus_le_compat 1%Q 1%Q (exp_tail_abs Ny n Y) 1%Q).
          -- apply Qle_refl.
          -- apply Qlt_le_weak. exact (Hy Ny n (Nat.le_refl Ny)).
        * apply Qle_refl. }
  (* β 全局界 Bb 及其正性/抵消恒等（HP2 缩放链用） *)
  set (Bb := ((1 + 1)%Q + exp_tail_abs 0 Ny Y)%Q).
  assert (HBb : Qlt 0 Bb).
  { unfold Bb.
    setoid_rewrite (Qplus_comm (1 + 1)%Q (exp_tail_abs 0 Ny Y)).
    apply (Qle_lt_trans 0%Q (exp_tail_abs 0 Ny Y + 0)%Q
             (exp_tail_abs 0 Ny Y + (1 + 1)%Q)).
    - rewrite Qplus_0_r. exact (bxae_etab_nonneg Y 0 Ny HY).
    - apply (proj2 (Qplus_lt_r 0%Q (1 + 1)%Q (exp_tail_abs 0 Ny Y))).
      exact bxae_qlt_0_2. }
  assert (HtwoBb : Qlt 0 ((1 + 1) * Bb)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) Bb); [exact bxae_qlt_0_2 | exact HBb]).
  assert (HcanBb : ((eps * / ((1 + 1) * Bb)) * Bb == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - apply q_neq_of_lt. exact HtwoBb. }
  (* X 侧窗阈值（eps·/(2·Bb) 缩放额） *)
  assert (HltE : Qlt 0 (eps * / (1 + 1))%Q).
  { apply (ncv_qmult_lt0 eps (Qinv (1 + 1))).
    - exact (QltT_to_Qlt 0 eps He).
    - apply Qinv_lt_0_compat. exact bxae_qlt_0_2. }
  destruct (bxae_etab_small X (eps * / ((1 + 1) * Bb))%Q HX
              (Qlt_to_QltT _ _
                (ncv_qmult_lt0 eps (Qinv ((1 + 1) * Bb))
                   (QltT_to_Qlt 0 eps He)
                   (Qinv_lt_0_compat _ HtwoBb)))) as [Na Ha].
  set (SN := (1 + exp_tail_abs 0 Na X)%Q).
  assert (HposSN : Qlt 0 SN).
  { unfold SN. apply (Qlt_le_trans 0%Q 1%Q SN).
    - exact bxae_qlt_0_1.
    - apply bxae_Qle_add_r. exact (bxae_etab_nonneg X 0 Na HX). }
  assert (HtwoSN : Qlt 0 ((1 + 1) * SN)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) SN); [exact bxae_qlt_0_2 | exact HposSN]).
  destruct (bxae_etab_small Y (eps * / ((1 + 1) * SN))%Q HY
              (Qlt_to_QltT _ _
        (ncv_qmult_lt0 eps (Qinv ((1 + 1) * SN))
                   (QltT_to_Qlt 0 eps He)
                   (Qinv_lt_0_compat _ HtwoSN)))) as [Ny1 Hy1].
  exists (Na + Ny1)%nat. intros n Hn.
  assert (Hnd : n = (Na + (n - Na))%nat) by lia.
  set (d := (n - Na)%nat).
  assert (HcanSN : ((eps * / ((1 + 1) * SN)) * SN == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - apply q_neq_of_lt. exact HtwoSN. }
  (* 分窗 *)
  set (F := fun i : nat =>
              (q_pow X i / q_fact i) * exp_tail_abs (Nat.sub n i) n Y).
  replace (ncv_qsum F (Datatypes.S n)) with (ncv_qsum F (Datatypes.S (Na + d)))%nat
    by (f_equal; lia).
  rewrite bxae_ncvsum_split_eq.
  (* 前窗：i ≤ Na *)
  assert (HP1 : Qlt (ncv_qsum F (Datatypes.S Na)) (eps * / (1 + 1))%Q).
  { assert (Hlt1 : Qlt (exp_tail_abs (Nat.sub n Na) n Y * SN)
                       ((eps * / ((1 + 1) * SN)) * SN)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs (Nat.sub n Na) n Y)
        (eps * / ((1 + 1) * SN)) SN).
      - apply (Hy1 (Nat.sub n Na) n). lia.
      - exact HposSN. }
    rewrite HcanSN in Hlt1.
    assert (Hpt : forall i : nat, (i <= Na)%nat ->
              QleT' (F i) (exp_tail_abs (Nat.sub n Na) n Y
                           * (q_pow X i / q_fact i))%Q).
    { intros i Hi. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               (exp_tail_abs (Nat.sub n i) n Y
                * (q_pow X i / q_fact i))%Q).
      - apply qeq_imp_qle. ring.
      - apply (Qmult_le_compat_r _ _ (q_pow X i / q_fact i)).
        + apply (bxae_etab_mono_start Y (Nat.sub n Na) (Nat.sub n i) n HY).
          lia.
        + apply (bxae_term_nonneg X i HX). }
    assert (Hle1 : QleT' (ncv_qsum F (Datatypes.S Na))
                   (ncv_qsum (fun i : nat =>
                      exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                      (Datatypes.S Na)))
      by (apply bxae_ncvsum_le_ranged; intros k Hk; apply Hpt; lia).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na)
                 == (exp_tail_abs (Nat.sub n Na) n Y
                     * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))%Q)
      by apply ncv_qsum_scalar_l.
    apply (Qle_lt_trans _ (exp_tail_abs (Nat.sub n Na) n Y * SN)%Q).
    - apply (Qle_trans _ (ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na))%Q).
      + exact (QleT'_to_Qle _ _ Hle1).
      + apply (Qle_trans _ (exp_tail_abs (Nat.sub n Na) n Y
                 * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                   (Datatypes.S Na))%Q).
        * exact (qeq_imp_qle _ _ Hsc).
        * rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y)
                    (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))).
          rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y) SN).
          apply (Qmult_le_compat_r _ _ (exp_tail_abs (Nat.sub n Na) n Y)).
          -- apply qeq_imp_qle. unfold SN. exact (bxae_ncvsum_alpha X Na).
          -- exact (bxae_etab_nonneg Y (Nat.sub n Na) n HY).
    - exact Hlt1. }
  (* 后窗：i > Na（位移窗） *)
  assert (HP2 : Qlt (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                    (eps * / (1 + 1))%Q).
  { assert (Hpt : forall i : nat,
              QleT' (F ((Datatypes.S Na + i)%nat))
                (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)))%Q).
    { intros i. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               ((q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                * ((1 + 1)%Q + exp_tail_abs 0 Ny Y))%Q).
      - rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  (exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)).
        rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
        apply (Qmult_le_compat_r _ _
                 (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))).
        + (* tail(n−j, n) ≤ 1 + tail(0, n) ≤ Bb *)
          apply (Qle_trans _ (1 + exp_tail_abs 0 n Y)%Q).
          * assert (Hsp2 : exp_tail_abs 0 n Y
                           == (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                               + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q)
              by (apply bxae_etab_split with (m2 := Nat.sub n ((Datatypes.S Na + i)%nat)); lia).
            assert (Ht1 : exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y
                          <= exp_tail_abs 0 n Y).
            { apply (Qle_trans _
                       (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                        + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q).
              - apply bxae_Qle_add_l.
                exact (bxae_etab_nonneg Y 0%nat (Nat.sub n ((Datatypes.S Na + i)%nat)) HY).
              - apply qeq_imp_qle. symmetry. exact Hsp2. }
            apply (Qle_trans _ (exp_tail_abs 0 n Y)).
            -- exact Ht1.
            -- apply bxae_Qle_add_l. apply Qle_0_1.
          * apply Hb.
        + apply (bxae_term_nonneg X ((Datatypes.S Na + i)%nat) HX).
      - apply qeq_imp_qle. apply Qmult_comm. }
    assert (Hle2 : QleT' (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                   (ncv_qsum (fun i : nat =>
                      ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                      * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d))
      by (apply ncv_qsum_le; exact Hpt).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d
                 == (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                     * ncv_qsum (fun i : nat =>
                          q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)) d)%Q)
      by apply ncv_qsum_scalar_l.
    pose proof Hle2 as Hle3.
    apply QleT'_to_Qle in Hle3.
    rewrite Hsc in Hle3.
    rewrite (bxae_ncvsum_alpha_shift X Na d) in Hle3.
    replace (Na + d)%nat with n in Hle3 by lia.
    assert (Hlt2 : Qlt (exp_tail_abs Na n X * Bb)
                       ((eps * / ((1 + 1) * Bb)) * Bb)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs Na n X)
              (eps * / ((1 + 1) * Bb)) Bb).
      - exact (Ha Na n (Nat.le_refl Na)).
      - exact HBb. }
    setoid_rewrite HcanBb in Hlt2.
    setoid_rewrite (Qmult_comm (exp_tail_abs Na n X) Bb) in Hlt2.
    apply (Qle_lt_trans _ (Bb * exp_tail_abs Na n X)%Q).
    - exact Hle3.
    - exact Hlt2. }
  (* 合流：P1 < e/2，P2 < e/2 ⟹ P1 + P2 < e *)
  apply (Qle_lt_trans _
           (eps * / (1 + 1) + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)%Q).
  - apply (Qplus_le_compat _ _ _ _).
    + apply Qlt_le_weak. exact HP1.
    + apply Qle_refl.
  - apply (Qlt_le_trans
             (eps * / (1 + 1)
              + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
             (eps * / (1 + 1) + eps * / (1 + 1))%Q eps).
    + apply (proj2 (Qplus_lt_r (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                       (eps * / (1 + 1)) (eps * / (1 + 1)))).
      exact HP2.
    + apply qeq_imp_qle. apply bxae_half_add.
Qed.

(* ============================================================ *)
(* S2：Banach 层（行形三角 + 块分解 + 范数界 + 极限移位 + 主件）      *)
(* ============================================================ *)

(* QleT' 乘法双单调（0 ≤ x2 与 0 ≤ y1 显式前提，免 stdlib compat_l 缺位） *)
Lemma bxae_qleT'_mul_le : forall x1 y1 x2 y2 : Q,
  Qle x1 y1 -> Qle x2 y2 -> Qle 0 x2 -> Qle 0 y1 -> QleT' (x1 * x2) (y1 * y2)%Q.
Proof.
  intros x1 y1 x2 y2 H1 H2 H3a H3b.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (y1 * x2)%Q).
  - apply (Qmult_le_compat_r x1 y1 x2); assumption.
  - rewrite (Qmult_comm y1 x2). rewrite (Qmult_comm y1 y2).
    apply (Qmult_le_compat_r x2 y2 y1); assumption.
Qed.

(* bsum 与 ncv_sum 同形桥 *)
Lemma bxae_bsum_ncvsum : forall (B : BanachAlg) (x : nat -> (@BA B)) (n : nat),
  @bae B (bsum B n x) (ncv_sum B x n).
Proof.
  intros B x n. induction n as [| m IH].
  - apply (@bae_refl B).
  - change (bsum B (Datatypes.S m) x)
      with (@bplus B (bsum B m x) (x m)).
    change (ncv_sum B x (Datatypes.S m))
      with (@bplus B (ncv_sum B x m) (x m)).
    apply (@bplus_wd B).
    + exact IH.
    + apply (@bae_refl B).
Qed.

(* 零次幂项即单位：bpow x 0·(1/0!) == bone *)
Lemma bxae_B0_one : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B (bpow B x 0%nat) (@bcoef B (/ q_fact 0%nat))) (@bone B).
Proof.
  intros B x.
  assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
  rewrite Hq0.
  change (bpow B x 0%nat) with (@bone B).
  eapply bae_trans with (b := @bcoef B 1%Q).
  - exact (@bmult_one_l B (@bcoef B 1%Q)).
  - exact (@bcoef_one B).
Qed.

(* 项重排：coef c·(a^j·b^i) == (a^j·coef x)·(b^i·coef y)（c == x·y） *)
Lemma bxae_term_reassoc : forall (B : BanachAlg) (a b : (@BA B)) (j i : nat)
                                 (x y c : Q),
  c == (x * y)%Q ->
  @bae B (@bmult B (@bcoef B c) (@bmult B (bpow B a j) (bpow B b i)))
         (@bmult B (@bmult B (bpow B a j) (@bcoef B x))
                   (@bmult B (bpow B b i) (@bcoef B y))).
Proof.
  intros B a b j i x y c Hc.
  assert (Hswap : @bae B (@bmult B (@bmult B (bpow B b i) (@bcoef B x))
                                    (@bcoef B y))
                         (@bmult B (@bcoef B x)
                                   (@bmult B (bpow B b i) (@bcoef B y)))).
  { eapply bae_trans with
      (b := @bmult B (@bmult B (@bcoef B x) (bpow B b i)) (@bcoef B y)).
    - apply (@bmult_wd B).
      + exact (@bcoef_comm B x (bpow B b i)).
      + apply (@bae_refl B).
    - apply (@bae_sym B).
      exact (@bmult_assoc B (@bcoef B x) (bpow B b i) (@bcoef B y)). }
  eapply bae_trans with
    (b := @bmult B (@bmult B (bpow B a j) (bpow B b i))
                    (@bcoef B (x * y)%Q)).
  - eapply bae_trans with
      (b := @bmult B (@bmult B (bpow B a j) (bpow B b i)) (@bcoef B c)).
    + apply (@bae_sym B).
      exact (@bcoef_comm B c (@bmult B (bpow B a j) (bpow B b i))).
    + apply (@bmult_wd B).
      * apply (@bae_refl B).
        * apply (@bcoef_wd B). exact Hc.
  - eapply bae_trans with
      (b := @bmult B (bpow B a j)
                      (@bmult B (bpow B b i) (@bcoef B (x * y)%Q))).
    + apply (@bae_sym B).
      exact (@bmult_assoc B (bpow B a j) (bpow B b i)
                             (@bcoef B (x * y)%Q)).
    + eapply bae_trans with
        (b := @bmult B (bpow B a j)
                        (@bmult B (bpow B b i)
                                 (@bmult B (@bcoef B x) (@bcoef B y)))).
      * apply (@bmult_wd B).
        -- apply (@bae_refl B).
        -- apply (@bmult_wd B).
           ++ apply (@bae_refl B).
           ++ exact (@bcoef_mult B x y).
      * eapply bae_trans with
          (b := @bmult B (bpow B a j)
                          (@bmult B (@bmult B (bpow B b i) (@bcoef B x))
                                    (@bcoef B y))).
        -- apply (@bmult_wd B).
           ++ apply (@bae_refl B).
           ++ exact (@bmult_assoc B (bpow B b i) (@bcoef B x)
                                  (@bcoef B y)).
        -- eapply bae_trans with
             (b := @bmult B (bpow B a j)
                             (@bmult B (@bcoef B x)
                                       (@bmult B (bpow B b i)
                                                  (@bcoef B y)))).
           ++ apply (@bmult_wd B).
              ** apply (@bae_refl B).
              ** exact Hswap.
           ++ exact (@bmult_assoc B (bpow B a j) (@bcoef B x)
                                  (@bmult B (bpow B b i) (@bcoef B y))).
Qed.
(* ①③ 对接：(a+b)^k/k! == Σ_{j≤k} A j·B (k−j)（行形，CBR 桥供系数） *)
Lemma bxae_binom_row : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall k : nat,
    @bae B (@bmult B (bpow B (@bplus B a b) k) (@bcoef B (/ q_fact k)))
           (bsum B (Datatypes.S k)
              (fun j : nat =>
                 @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                          (@bmult B (bpow B b (Nat.sub k j))
                                   (@bcoef B (/ q_fact (Nat.sub k j)))))).
Proof.
  intros B a b hab k.
  eapply bae_trans.
  - exact (bnh_esp_term_binom B a b hab k).
  - apply (bsum_ext B (Datatypes.S k)
             (fun j : nat =>
                @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                         (@bmult B (bpow B a j)
                                  (bpow B b (Nat.sub k j))))
             (fun j : nat =>
                @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                         (@bmult B (bpow B b (Nat.sub k j))
                                  (@bcoef B (/ q_fact (Nat.sub k j)))))).
    intros j Hj.
    apply (bxae_term_reassoc B a b j (Nat.sub k j)
               (/ q_fact j) (/ q_fact (Nat.sub k j))
               (bpa_binom k j * / q_fact k)%Q).
    + exact (bxcb_term_split_binom k j ltac:(lia)).
Qed.

(* ② 方块行形：esp a n·esp b n == Σ_{i≤n} A i·esp b n *)
Lemma bxae_prod_row : forall (B : BanachAlg) (a b : (@BA B)) (n : nat),
  @bae B (@bmult B (exp_series_partial B a n) (exp_series_partial B b n))
         (bsum B (Datatypes.S n)
            (fun i : nat =>
               @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                        (exp_series_partial B b n))).
Proof.
  intros B a b n.
  eapply bae_trans.
  - apply (@bmult_wd B).
    + exact (esp_as_bsum B a n).
    + apply (@bae_refl B).
  - apply (@bae_sym B).
    exact (bpa_bsum_mult_r B (Datatypes.S n) (exp_series_partial B b n)
             (fun i : nat =>
                @bmult B (bpow B a i) (@bcoef B (/ q_fact i)))).
Qed.

(* ④ 行形三角（自建归纳，免 bd2 转置）：
   esp (a+b) n == Σ_{i≤n} A i·esp b (n−i) *)
Lemma bxae_tri_row : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall n : nat,
    @bae B (exp_series_partial B (@bplus B a b) n)
           (bsum B (Datatypes.S n)
              (fun i : nat =>
                 @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                          (exp_series_partial B b (Nat.sub n i)))).
Proof.
  intros B a b hab n.
  induction n as [| n' IH].
  - (* 基例：bone == bzero + A 0·esp b 0 *)
    assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
    change (exp_series_partial B (@bplus B a b) 0%nat) with (@bone B).
    change (bsum B (Datatypes.S 0%nat)
              (fun i : nat =>
                 @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                          (exp_series_partial B b (Nat.sub 0 i))))
      with (@bplus B (@bzero B)
              (@bmult B (@bmult B (bpow B a 0%nat) (@bcoef B (/ q_fact 0%nat)))
                       (exp_series_partial B b (Nat.sub 0 0)))).
    rewrite Hq0.
    change (bpow B a 0%nat) with (@bone B).
    change (exp_series_partial B b (Nat.sub 0 0)) with (@bone B).
    eapply bae_trans with
      (b := @bmult B (@bmult B (@bone B) (@bcoef B 1%Q)) (@bone B)).
    + eapply bae_trans with (b := @bmult B (@bcoef B 1%Q) (@bone B)).
      * eapply bae_trans with (b := @bcoef B 1%Q).
        -- apply (@bae_sym B). exact (@bcoef_one B).
        -- apply (@bae_sym B). exact (@bmult_one_r B (@bcoef B 1%Q)).
      * apply (@bmult_wd B).
        -- apply (@bae_sym B). exact (@bmult_one_l B (@bcoef B 1%Q)).
        -- apply (@bae_refl B).
    + apply (@bae_sym B).
      exact (@bplus_zero_l B (@bmult B (@bmult B (@bone B) (@bcoef B 1%Q)) (@bone B))).
  - (* 归纳步：set 命名短项结构 *)
    assert (Esub : Nat.sub (Datatypes.S n') (Datatypes.S n') = 0%nat) by lia.
    set (Ai := fun i : nat => @bmult B (bpow B a i) (@bcoef B (/ q_fact i))).
    set (Bj := fun j : nat => @bmult B (bpow B b j) (@bcoef B (/ q_fact j))).
    set (Hrow := fun i : nat =>
                   @bmult B (Ai i) (exp_series_partial B b (Nat.sub n' i))).
    set (Fj := fun j : nat =>
                 @bmult B (Ai j) (Bj (Nat.sub (Datatypes.S n') j))).
    set (Tl := @bmult B (Ai (Datatypes.S n')) (Bj 0%nat)).
    set (R := fun i : nat =>
                @bmult B (Ai i)
                    (exp_series_partial B b (Nat.sub (Datatypes.S n') i))).
    (* LHS 前置 change：esp(S n') == esp n' + C，RHS bsum 剥末项 *)
    change (exp_series_partial B (@bplus B a b) (Datatypes.S n'))
      with (@bplus B (exp_series_partial B (@bplus B a b) n')
                (@bmult B (bpow B (@bplus B a b) (Datatypes.S n'))
                          (@bcoef B (/ q_fact (Datatypes.S n'))))).
    change (bsum B (Datatypes.S (Datatypes.S n')) R)
      with (@bplus B (bsum B (Datatypes.S n') R) (R (Datatypes.S n'))).
    (* R (S n') ≡ Tl（B0↔esp b 0） *)
    assert (HRtl : @bae B Tl (R (Datatypes.S n'))).
    { unfold Tl, R, Ai, Bj. rewrite Esub.
      change (exp_series_partial B b 0%nat) with (@bone B).
      apply (@bmult_wd B); [apply (@bae_refl B) | exact (bxae_B0_one B b)]. }
    (* C 行形 *)
    assert (HC : @bae B (@bmult B (bpow B (@bplus B a b) (Datatypes.S n'))
                                  (@bcoef B (/ q_fact (Datatypes.S n'))))
                         (bsum B (Datatypes.S (Datatypes.S n')) Fj)).
    { unfold Fj. exact (bxae_binom_row B a b hab (Datatypes.S n')). }
    (* 剥末项：bsum (S (S n')) Fj == bsum (S n') Fj + Tl *)
    assert (Hpeel : @bae B (bsum B (Datatypes.S (Datatypes.S n')) Fj)
                           (@bplus B (bsum B (Datatypes.S n') Fj) Tl)).
    { unfold Fj, Tl, Ai, Bj.
      change (bsum B (Datatypes.S (Datatypes.S n'))
                (fun j : nat =>
                   @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                            (@bmult B (bpow B b (Nat.sub (Datatypes.S n') j))
                                     (@bcoef B (/ q_fact (Nat.sub (Datatypes.S n') j))))))
        with (@bplus B (bsum B (Datatypes.S n')
                          (fun j : nat =>
                             @bmult B (@bmult B (bpow B a j)
                                                  (@bcoef B (/ q_fact j)))
                                      (@bmult B (bpow B b
                                                   (Nat.sub (Datatypes.S n') j))
                                               (@bcoef B
                                                  (/ q_fact (Nat.sub (Datatypes.S n') j))))))
                  (@bmult B (@bmult B (bpow B a (Datatypes.S n'))
                                      (@bcoef B (/ q_fact (Datatypes.S n'))))
                           (@bmult B (bpow B b
                                        (Nat.sub (Datatypes.S n') (Datatypes.S n')))
                                    (@bcoef B
                                       (/ q_fact (Nat.sub (Datatypes.S n') (Datatypes.S n'))))))).
      rewrite Esub. apply (@bae_refl B). }
    (* 逐项合并：Hrow i + Fj i == R i（i < S n'） *)
    assert (HR : forall i : nat, (i < Datatypes.S n')%nat ->
                   @bae B (@bplus B (Hrow i) (Fj i)) (R i)).
    { intros i Hi. unfold Hrow, Fj, R, Ai, Bj.
      assert (E2 : Nat.sub (Datatypes.S n') i
                   = Datatypes.S (Nat.sub n' i)) by lia.
      rewrite E2.
      change (exp_series_partial B b (Datatypes.S (Nat.sub n' i)))
        with (@bplus B (exp_series_partial B b (Nat.sub n' i))
                  (@bmult B (bpow B b (Datatypes.S (Nat.sub n' i)))
                           (@bcoef B (/ q_fact (Datatypes.S (Nat.sub n' i)))))).
      apply (@bae_sym B). apply (@bdistrib_l B). }
    (* 总链（EXPADD5 重排）：esp+C → esp+ΣFj → esp+(ΣFj'+Tl) → 重结合
       → (ΣHrow+ΣFj)+Tl → +R(S n') → Σ(Hrow+Fj)+R(S n') → 目标 *)
    eapply bae_trans with
      (b := @bplus B (exp_series_partial B (@bplus B a b) n')
                      (bsum B (Datatypes.S (Datatypes.S n')) Fj)).
    { apply (@bplus_wd_r B). exact HC. }
    eapply bae_trans with
      (b := @bplus B (exp_series_partial B (@bplus B a b) n')
                      (@bplus B (bsum B (Datatypes.S n') Fj) Tl)).
    { apply (@bplus_wd_r B). exact Hpeel. }
    eapply bae_trans with
      (b := @bplus B (@bplus B (exp_series_partial B (@bplus B a b) n')
                            (bsum B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_assoc B). }
    eapply bae_trans with
      (b := @bplus B (@bplus B (bsum B (Datatypes.S n') Hrow)
                            (bsum B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_wd_l B). apply (@bplus_wd_l B). exact IH. }
    eapply bae_trans with
      (b := @bplus B (@bplus B (bsum B (Datatypes.S n') Hrow)
                            (bsum B (Datatypes.S n') Fj)) (R (Datatypes.S n'))).
    { apply (@bplus_wd_r B). exact HRtl. }
    apply (@bplus_wd_l B).
    eapply bae_trans with
      (b := bsum B (Datatypes.S n') (fun i : nat => @bplus B (Hrow i) (Fj i))).
    { apply (@bae_sym B). exact (bsum_plus B (Datatypes.S n') Hrow Fj). }
    { apply (bsum_ext B (Datatypes.S n')
                (fun i : nat => @bplus B (Hrow i) (Fj i)) R).
      intros i Hi. exact (HR i Hi). }
Qed.
(* 差=块和：esp a n·esp b n − esp (a+b) n == Σ_{i≤n} A i·(esp b n − esp b (n−i)) *)
Lemma bxae_diff_block : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall (n : nat),
  @bae B (@bplus B (@bmult B (exp_series_partial B a n)
                             (exp_series_partial B b n))
                   (@bopp B (exp_series_partial B (@bplus B a b) n)))
         (bsum B (Datatypes.S n)
            (fun i : nat =>
               @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                        (@bplus B (exp_series_partial B b n)
                                 (@bopp B (exp_series_partial B b
                                              (Nat.sub n i)))))).
Proof.
  intros B a b hab n.
  set (Ai := fun i : nat => @bmult B (bpow B a i) (@bcoef B (/ q_fact i))).
  set (Hrow := fun i : nat =>
                 @bmult B (Ai i) (exp_series_partial B b (Nat.sub n i))).
  set (Kf := fun i : nat =>
               @bmult B (Ai i)
                        (@bplus B (exp_series_partial B b n)
                                 (@bopp B (exp_series_partial B b
                                            (Nat.sub n i))))).
  (* 逐项：A i·esp b n == Hrow i + Kf i *)
  assert (Hpt : forall i : nat,
             @bae B (@bmult B (Ai i) (exp_series_partial B b n))
                    (@bplus B (Hrow i) (Kf i))).
  { intros i. unfold Hrow, Kf.
    (* A·u == A·(v+(u+−v)) == A·v + A·(u+−v)（分配反演+群律消去） *)
    eapply bae_trans with
      (b := @bmult B (Ai i)
                      (@bplus B (exp_series_partial B b (Nat.sub n i))
                               (@bplus B (exp_series_partial B b n)
                                        (@bopp B (exp_series_partial B b
                                                   (Nat.sub n i)))))).
    - apply (@bmult_wd B).
      + apply (@bae_refl B).
      + apply (@bae_sym B).
        eapply bae_trans with
          (b := @bplus B (@bplus B (exp_series_partial B b (Nat.sub n i))
                                  (exp_series_partial B b n))
                         (@bopp B (exp_series_partial B b
                                    (Nat.sub n i)))).
        * apply (@bplus_assoc B).
        * eapply bae_trans with
            (b := @bplus B (@bplus B (exp_series_partial B b n)
                                    (exp_series_partial B b (Nat.sub n i)))
                           (@bopp B (exp_series_partial B b
                                      (Nat.sub n i)))).
          -- apply (@bplus_wd_l B). apply (@bplus_comm B).
          -- eapply bae_trans with
               (b := @bplus B (exp_series_partial B b n)
                              (@bplus B (exp_series_partial B b (Nat.sub n i))
                                       (@bopp B (exp_series_partial B b
                                                  (Nat.sub n i))))).
             ++ apply (@bae_sym B). apply (@bplus_assoc B).
             ++ eapply bae_trans with
                  (b := @bplus B (exp_series_partial B b n) (@bzero B)).
                ** apply (@bplus_wd_r B).
                   exact (@bplus_opp B (exp_series_partial B b (Nat.sub n i))).
                ** apply (@bplus_zero B (exp_series_partial B b n)).
    - apply (@bdistrib_l B). }
  assert (H1 : @bae B (@bplus B (@bmult B (exp_series_partial B a n)
                                         (exp_series_partial B b n))
                              (@bopp B (exp_series_partial B
                                          (@bplus B a b) n)))
                     (@bplus B (bsum B (Datatypes.S n)
                                  (fun i : nat =>
                                     @bmult B (Ai i)
                                         (exp_series_partial B b n)))
                              (@bopp B (bsum B (Datatypes.S n) Hrow)))).
  { apply (@bplus_wd B).
    - exact (bxae_prod_row B a b n).
    - apply (@bopp_wd B).
      destruct n as [| n'].
      + exact (bxae_tri_row B a b hab 0%nat).
      + exact (bxae_tri_row B a b hab (Datatypes.S n')). }
  assert (H2 : @bae B (bsum B (Datatypes.S n)
                         (fun i : nat =>
                            @bmult B (Ai i) (exp_series_partial B b n)))
                     (@bplus B (bsum B (Datatypes.S n) Hrow)
                              (bsum B (Datatypes.S n) Kf))).
  { eapply bae_trans with
      (b := bsum B (Datatypes.S n)
               (fun i : nat => @bplus B (Hrow i) (Kf i))).
    - apply (bsum_ext B (Datatypes.S n)
                (fun i : nat => @bmult B (Ai i) (exp_series_partial B b n))
                (fun i : nat => @bplus B (Hrow i) (Kf i))).
      intros k _. exact (Hpt k).
    - exact (bsum_plus B (Datatypes.S n) Hrow Kf). }
  assert (H3 : @bae B (@bplus B (@bplus B (bsum B (Datatypes.S n) Hrow)
                                        (bsum B (Datatypes.S n) Kf))
                              (@bopp B (bsum B (Datatypes.S n) Hrow)))
                     (bsum B (Datatypes.S n) Kf)).
  { apply (@bae_sym B).
    eapply bae_trans with
      (b := @bplus B (bsum B (Datatypes.S n) Kf)
                   (@bplus B (bsum B (Datatypes.S n) Hrow)
                            (@bopp B (bsum B (Datatypes.S n) Hrow)))).
    - (* bsum Kf == bsum Kf + (bsum Hrow + -bsum Hrow)：先 == 自身+0，再 wd_r *)
      eapply bae_trans with
        (b := @bplus B (bsum B (Datatypes.S n) Kf) (@bzero B)).
      + apply (@bae_sym B).
        exact (@bplus_zero B (bsum B (Datatypes.S n) Kf)).
      + apply (@bplus_wd_r B). apply (@bae_sym B).
        exact (@bplus_opp B (bsum B (Datatypes.S n) Hrow)).
    - (* bsum Kf + (bsum Hrow + -bsum Hrow) == (bsum Hrow + bsum Kf) + -bsum Hrow *)
      eapply bae_trans with
        (b := @bplus B (@bplus B (bsum B (Datatypes.S n) Kf)
                                (bsum B (Datatypes.S n) Hrow))
                       (@bopp B (bsum B (Datatypes.S n) Hrow))).
      + apply (@bplus_assoc B _ _ _).
      + apply (@bplus_wd_l B).
        exact (@bplus_comm B (bsum B (Datatypes.S n) Kf)
                             (bsum B (Datatypes.S n) Hrow)). }
  eapply bae_trans with
    (b := @bplus B (bsum B (Datatypes.S n)
                       (fun i : nat =>
                          @bmult B (Ai i) (exp_series_partial B b n)))
                  (@bopp B (bsum B (Datatypes.S n) Hrow))).
  - exact H1.
  - eapply bae_trans with
      (b := @bplus B (@bplus B (bsum B (Datatypes.S n) Hrow)
                              (bsum B (Datatypes.S n) Kf))
                     (@bopp B (bsum B (Datatypes.S n) Hrow))).
    + apply (@bplus_wd_l B). exact H2.
    + exact H3.
Qed.
(* ④ 块和范数界：‖块 n‖ ≤T Σ_{i≤n} ‖a‖^i/i!·tail(‖b‖; n−i..n) *)
Lemma bxae_block_norm_le : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall n : nat,
    QleT' (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                            (exp_series_partial B b n))
                              (@bopp B (exp_series_partial B
                                          (@bplus B a b) n))))
          (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm B b))
               (Datatypes.S n)).
Proof.
  intros B a b hab n.
  eapply (QeqT_Qle_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd B _ _
               (bxae_diff_block B a b hab n)))).
  eapply qleT'_trans.
  - eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd B _ _
               (bxae_bsum_ncvsum B
                  (fun i : nat =>
                     @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                              (@bplus B (exp_series_partial B b n)
                                       (@bopp B (exp_series_partial B b
                                                  (Nat.sub n i)))))
                  (Datatypes.S n))))).
    exact (ncv_norm_sum_le B
             (fun i : nat =>
                @bmult B (@bmult B (bpow B a i) (@bcoef B (/ q_fact i)))
                         (@bplus B (exp_series_partial B b n)
                                  (@bopp B (exp_series_partial B b
                                               (Nat.sub n i)))))
             (Datatypes.S n)).
  - apply ncv_qsum_le. intros i. destruct i as [| i'].
    + (* i = 0：‖A 0‖ == 1（经 bcoef 1） *)
      assert (Hn0 : (Nat.sub n 0 <= n)%nat) by lia.
      assert (HA0 : @bae B (@bmult B (bpow B a 0%nat)
                                  (@bcoef B (/ q_fact 0%nat)))
                           (@bcoef B 1%Q)).
      { assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
        rewrite Hq0.
        change (bpow B a 0%nat) with (@bone B).
        exact (@bmult_one_l B (@bcoef B 1%Q)). }
      eapply qleT'_trans.
      * exact (@bnorm_mult B (@bmult B (bpow B a 0%nat)
                                      (@bcoef B (/ q_fact 0%nat)))
                             (@bplus B (exp_series_partial B b n)
                                      (@bopp B (exp_series_partial B b
                                                  (Nat.sub n 0))))).
      * eapply qleT'_trans.
        { eapply (qleT'_mult_compat_r).
          { apply (@bnorm_pos B). }
          { eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_wd B _ _ HA0))).
            eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_coef B 1%Q))).
            apply qleT'_refl. } }
        { apply (bxae_qleT'_mul_le (Qabs 1%Q)
                   (q_pow (@bnorm B a) 0%nat / q_fact 0%nat)%Q).
          -- apply Qle_refl.
          -- apply QleT'_to_Qle.
             exact (esp_diff_le_tail B b (Nat.sub n 0) n Hn0).
          -- apply QleT'_to_Qle. apply (@bnorm_pos B).
          -- exact (Qle_0_1). }
    + (* i = S i'：bnorm_esp_term × esp_diff_le_tail *)
      assert (HnS : (Nat.sub n (Datatypes.S i') <= n)%nat) by lia.
      eapply qleT'_trans.
      * exact (@bnorm_mult B (@bmult B (bpow B a (Datatypes.S i'))
                                       (@bcoef B (/ q_fact (Datatypes.S i'))))
                             (@bplus B (exp_series_partial B b n)
                                      (@bopp B (exp_series_partial B b
                                                  (Nat.sub n (Datatypes.S i')))))).
      * apply (bxae_qleT'_mul_le).
        -- apply QleT'_to_Qle. apply (bnorm_esp_term B a i').
        -- apply QleT'_to_Qle.
           exact (esp_diff_le_tail B b (Nat.sub n (Datatypes.S i')) n HnS).
        -- apply QleT'_to_Qle. apply (@bnorm_pos B).
        -- apply (bxae_term_nonneg (@bnorm B a) (Datatypes.S i')).
           apply QleT'_to_Qle. exact (@bnorm_pos B a).
Qed.

(* ④ 差小：∀eps>0 ∃N，n≥N ⟹ ‖esp a n·esp b n − esp (a+b) n‖ < eps *)
Lemma bxae_diff_small : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                            (exp_series_partial B b n))
                              (@bopp B (exp_series_partial B
                                          (@bplus B a b) n)))) eps).
Proof.
  intros B a b hab eps Heps.
  destruct (bxae_qblock_small (@bnorm B a) (@bnorm B b) eps
              (QleT'_to_Qle 0 (@bnorm B a) (@bnorm_pos B a))
              (QleT'_to_Qle 0 (@bnorm B b) (@bnorm_pos B b))
              Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm B b))
               (Datatypes.S n)) eps).
  - exact (QleT'_to_Qle _ _
             (bxae_block_norm_le B a b hab n)).
  - exact (HN n Hn).
Qed.

(* 极限移位：v→l 且 ‖u n − v n‖→0 ⟹ u→l *)
Lemma bxae_lim_shift : forall (B : BanachAlg) (u v : nat -> (@BA B)) (l : (@BA B)),
  blim B v l ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall n : nat, NatLe N n ->
       QltT (@bnorm B (@bplus B (u n) (@bopp B (v n)))) eps)) ->
  blim B u l.
Proof.
  intros B u v l Hv Hdiff eps Heps.
  assert (Hh : QltT 0 (eps / 2)%Q) by (apply bxuq_half_pos; exact Heps).
  destruct (Hdiff (eps / 2)%Q Hh) as [N1 HN1].
  destruct (Hv (eps / 2)%Q Hh) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  eapply (QeqT_Qlt_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd B _ _
               (bxuq_diff_split B (u n) (v n) l)))).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           ((@bnorm B (@bplus B (u n) (@bopp B (v n)))) +
            (@bnorm B (@bplus B (v n) (@bopp B l))))%Q eps).
  - exact (QleT'_to_Qle _ _
             (@bnorm_plus B (@bplus B (u n) (@bopp B (v n)))
                           (@bplus B (v n) (@bopp B l)))).
  - apply (bxuq_sum_half_lt
             (@bnorm B (@bplus B (u n) (@bopp B (v n))))
             (@bnorm B (@bplus B (v n) (@bopp B l)))).
    + assert (Hle1 : (N1 <= n)%nat).
      * apply (Nat.le_trans N1 (Nat.max N1 N2) n).
        -- apply Nat.le_max_l.
        -- exact (NatLe_drop _ _ Hn).
      * exact (QltT_to_Qlt _ _ (HN1 n (NatLe_lift _ _ Hle1))).
    + assert (Hle2 : (N2 <= n)%nat).
      * apply (Nat.le_trans N2 (Nat.max N1 N2) n).
        -- apply Nat.le_max_r.
        -- exact (NatLe_drop _ _ Hn).
      * exact (QltT_to_Qlt _ _ (HN2 n (NatLe_lift _ _ Hle2))).
Qed.

(* ============================================================ *)
(* 主件：e^a·e^b == e^(a+b)（hab 交换面；20260915 席AA18 起零假设）  *)
(* 六环总装：⑤ 左极限 + ④ 差小移位 + ⑥ 唯一性                      *)
(* 迁移史注：bxae_ 族七件（term_reassoc/binom_row/tri_row/           *)
(* diff_block/block_norm_le/diff_small/exp_add）签名收窄至零假设，   *)
(* bnh_esp_term_binom 同位供给，hplus/hwd 形参全摘。                 *)
(* ============================================================ *)

Theorem bxae_exp_add : forall (E : BanachAlgExt) (a b : (@BA (@bxce_base E))),
  @bae (@bxce_base E) (@bmult (@bxce_base E) a b) (@bmult (@bxce_base E) b a) ->
  @bae (@bxce_base E)
       (@bxdef_emul (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                    (bxdef_exp (@bxce_base E) b))
       (bxdef_exp (@bxce_base E) (@bplus (@bxce_base E) a b)).
Proof.
  intros E a b hab.
  unfold bxdef_emul.
  apply (bxuq_lim_uniq E
           (fun n : nat =>
              @bmult (@bxce_base E) (exp_series_partial (@bxce_base E) a n)
                                    (exp_series_partial (@bxce_base E) b n))).
  - exact (bxadd_esp_prod_blim (@bxce_base E) a b).
  - apply (bxae_lim_shift (@bxce_base E)
             (fun n : nat =>
                @bmult (@bxce_base E) (exp_series_partial (@bxce_base E) a n)
                                      (exp_series_partial (@bxce_base E) b n))
             (exp_series_partial (@bxce_base E) (@bplus (@bxce_base E) a b))
             (bxdef_exp (@bxce_base E) (@bplus (@bxce_base E) a b))).
    + exact (bxdef_exp_spec (@bxce_base E)
                (@bplus (@bxce_base E) a b)).
    + intros eps Heps.
      destruct (bxae_diff_small (@bxce_base E) a b hab eps Heps)
        as [N HN].
      exists N. intros n Hn.
      apply HN. exact (NatLe_drop _ _ Hn).
Qed.
