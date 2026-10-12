(* ===================================================================== *)
(*  u5c_ln2_gap1_convbinom.v —— ln2 供给链卷积/二项式幂系数 Q 层基建件     *)
(* ①使命: 铸造 ln2 供给链卷积/二项式幂系数 Q 层基建——一般 n 残数全形 d_1 == 2^n·q̃_n  *)
(*     （abl_ln2_qpoly_gen.v §6-§7 登记位 lng_d1_full_gen_type 的对应闭合）。数学内核:   *)
(*     t^n(1−t)^n ÷ (1−t/2)^{n+1} 的余式 R 满足 [u^n]R(2−2u) == 2^n·q̃_n，其中           *)
(*     q̃_n = Σ_{k≤n} C(n,k)²·2^{n−k}（中心 Delannoy 数）。三肢: (a) 卷积系数肢            *)
(*     nth k (mul A B) 0 == Σ_{j≤k} a_j·b_{k−j}（lncv_sum 换序基建）；(b) 二项式幂系数肢    *)
(*     nth k (pow [1;c] n) 0 == c^k·C(n,k)（Pascal 幂件）；(c) 逐点→系数提取肢 lncv_e2n——   *)
(*     eval 相等 ⟹ 系数相等（δ-差分首项提取 Φ_m（Josephson 桥: i·C(S n,i) = S n·C(n,i−1)    *)
(*     无位移再索引）＋去顶位截尾（remlast）＋燃料下降。 *)
(* ②依赖: 池内 S01_BaseRing、S02_CauchyComplete（QeqT/Qcompare 面，只读）；Stdlib *)
(*     QArith/List/Arith/ZArith/Lia/Extraction。来源件（abl_ln2_qpoly_gen.v 之 lng_*、 *)
(*     abl_ln2_qpoly_consume.v 之 lnc_*、PolyIntegral 之 pint_*、BeukersLists 之 *)
(*     bkC/bk_psd/bk_Qn_qtilde）不在本池 Require 域——本件以逐定义对应重述其定义面  *)
(*     （lnp_* 对应 lnc_*，bkC/bk_psd/bk_Qn_qtilde 按 BeukersLists.v §A/§B/§C Fixpoint 原样）， *)
(*     对应表: lnp_eval↔pint_eval、lnp_add↔pint_add、lnp_scale↔lnc_scale、lnp_mul↔lnc_mul、 *)
(*     lnp_pow↔lnc_pow、lnp_lin_t↔lnc_lin_t、 *)
(*     lnp_lin_1mt↔lnc_lin_1mt、lnp_bk_num↔lnc_bk_num、lnp_bk_den↔lnc_bk_den、 *)
(*     lnp_comp2↔lnc_comp2、lnp_d1↔lnc_d1、lnp_div_pred↔qpd_divmod_gen_pred 表面、 *)
(*     lncv_d1_gen_type↔lnc_d1_gen_type（abl_ln2_qpoly_consume.v §6）。 *)
(* ③编译配方: source /Users/apple/Desktop/ConstructiveWorld/Live/ toolchain/env.sh 后于池目录: rocq c -native-compiler no -q  *)
(*     -Q . "" u5c_ln2_gap1_convbinom.v。  *)
(* ④构造性: 零公理零承认零放弃零经典（文尾 Print Assumptions 全列逐条 Closed）；语句面全 Set *)
(*     （sigT/S01.And/S02.QeqT/Id 面）；Qeq(==) 仅证内推理脚手架；环闭全走「全变量形小件」； *)
(*     数值锚 vm_compute 定装；文尾 Separate Extraction。 *)
(* ⑤边界: 本件交付上游验收形的对应闭合，lng_d1_full_gen_type 的直接 Require 使用留待后续桥接件； *)
(*     逐点单调积分版、真族↔规范对改接桥（缺口②）、clo 下界（缺口③）不在本件面。诚实注记:     *)
(*     提取面 lnp_div_pred 之 QeqT 在 OCaml 侧或有 match-型擦除伪影（同 abl_ln2_qpoly_gen.v）， *)
(*     Coq 侧零公理不受影响。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 坑卡补录: 点号限定名进 apply 论元会切断 LTAC 解析——战术位用      *)
(*    本别名，语句位保持 Datatypes.S 池内惯例（QPOLYNOTATION 姊妹坑）。 *)
(* ============================================================ *)

Definition lncv_S (n : nat) : nat := Datatypes.S n.

(* ============================================================ *)
(* §1 稠密多项式对应层（头=常数项; lnp_eval↔pint_eval 等, 见头注②）    *)
(* ============================================================ *)

Fixpoint lnp_eval (p : list Q) (x : Q) : Q :=
  match p with
  | nil => 0
  | cons c p' => c + x * lnp_eval p' x
  end.

Fixpoint lnp_add (p q : list Q) : list Q :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (lnp_add p' q')
      end
  end.

Definition lnp_scale (a : Q) (p : list Q) : list Q :=
  map (fun z : Q => a * z) p.

(* Cauchy 卷积: (cons c p')·q = c·q + x·(p'·q)（对应 lnc_mul） *)
Fixpoint lnp_mul (p q : list Q) : list Q :=
  match p with
  | nil => nil
  | cons c p' => lnp_add (lnp_scale c q) (cons 0 (lnp_mul p' q))
  end.

Fixpoint lnp_pow (p : list Q) (k : nat) : list Q :=
  match k with
  | 0%nat => cons 1 nil
  | Datatypes.S k' => lnp_mul p (lnp_pow p k')
  end.

(* 求值小件 *)
Lemma lncv_eval_nil : forall x : Q, QeqT (lnp_eval nil x) (0).
Proof. intros x. apply qeq_imp_qeqT. cbn [lnp_eval]. apply Qeq_refl. Qed.

Lemma lncv_eval_cons : forall (c : Q) (p : list Q) (x : Q), QeqT (lnp_eval (cons c p) x) (c + x * lnp_eval p x).
Proof. intros c p x. apply qeq_imp_qeqT. cbn [lnp_eval]. apply Qeq_refl. Qed.

Lemma lncv_eval_0 : forall p : list Q, QeqT (lnp_eval p 0) (nth 0%nat p 0).
Proof.
  intros p. apply qeq_imp_qeqT.
  induction p as [|c p' IH].
  - cbn [lnp_eval nth]. apply Qeq_refl.
  - cbn [lnp_eval nth]. rewrite IH. ring.
Qed.

Lemma lncv_eval_add : forall (p q : list Q) (x : Q), QeqT (lnp_eval (lnp_add p q) x) (lnp_eval p x + lnp_eval q x).
Proof.
  intros p q x. apply qeq_imp_qeqT.
  revert q x. induction p as [|a p' IH]; intros q x.
  - cbn [lnp_add lnp_eval]. ring.
  - destruct q as [|b q'].
    + cbn [lnp_add lnp_eval]. ring.
    + cbn [lnp_add lnp_eval]. rewrite IH. ring.
Qed.

Lemma lncv_eval_scale : forall (a : Q) (p : list Q) (x : Q), QeqT (lnp_eval (lnp_scale a p) x) (a * lnp_eval p x).
Proof.
  intros a p x. apply qeq_imp_qeqT. unfold lnp_scale.
  induction p as [|b p' IH].
  - cbn [map lnp_eval]. ring.
  - cbn [map lnp_eval]. rewrite IH. ring.
Qed.

Lemma lncv_ring_mul_step : forall c e z t : Q, QeqT (c * z + (0 + t * (e * z))) ((c + t * e) * z).
Proof. intros c e z t. apply qeq_imp_qeqT. ring. Qed.

Lemma lncv_eval_mul : forall (p q : list Q) (x : Q), QeqT (lnp_eval (lnp_mul p q) x) (lnp_eval p x * lnp_eval q x).
Proof.
  intros p q x. apply qeq_imp_qeqT.
  revert q x. induction p as [|c p' IH]; intros q x.
  - cbn [lnp_mul]. rewrite (qeqT_imp_qeq _ _ (lncv_eval_nil x)). ring.
  - cbn [lnp_mul].
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_add _ _ _)),
            (qeqT_imp_qeq _ _ (lncv_eval_scale _ _ _)).
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_cons 0 (lnp_mul p' q) x)).
    rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_cons c p' x)).
    apply qeqT_imp_qeq. apply lncv_ring_mul_step.
Qed.

Lemma lncv_eval_pow : forall (p : list Q) (k : nat) (x : Q), QeqT (lnp_eval (lnp_pow p k) x) (q_pow (lnp_eval p x) k).
Proof.
  intros p k x. apply qeq_imp_qeqT. induction k as [|k' IH].
  - cbn [lnp_pow q_pow lnp_eval]. ring.
  - cbn [lnp_pow]. rewrite (qeqT_imp_qeq _ _ (lncv_eval_mul _ _ _)), IH.
    cbn [q_pow]. apply Qeq_refl.
Qed.

(* nth 小件（对应 lng_nth_*） *)
Lemma lncv_nth_nil : forall (k : nat) (d : Q), nth k nil d = d.
Proof. intros k d. destruct k; reflexivity. Qed.

Lemma lncv_nth_cons_0 : forall (a : Q) (l : list Q) (d : Q),
  nth 0%nat (a :: l) d = a.
Proof. intros a l d. reflexivity. Qed.

Lemma lncv_nth_cons_S : forall (k : nat) (a : Q) (l : list Q) (d : Q),
  nth (Datatypes.S k) (a :: l) d = nth k l d.
Proof. intros k a l d. reflexivity. Qed.

Lemma lncv_nth_oob : forall (p : list Q) (k : nat),
  (length p <= k)%nat -> QeqT (nth k p 0) (0).
Proof.
  induction p as [|a p' IH]; intros k Hk.
  - apply qeq_imp_qeqT. rewrite lncv_nth_nil. apply Qeq_refl.
  - destruct k as [|k'].
    + exfalso. cbn [length] in Hk. lia.
    + apply qeq_imp_qeqT. rewrite lncv_nth_cons_S.
      apply qeqT_imp_qeq. apply IH. cbn [length] in Hk. lia.
Qed.

Lemma lncv_nth_add : forall (p q : list Q) (k : nat), QeqT (nth k (lnp_add p q) 0) (nth k p 0 + nth k q 0).
Proof.
  intros p q k. apply qeq_imp_qeqT.
  revert q k. induction p as [|a p' IH]; intros q k.
  - cbn [lnp_add]. rewrite lncv_nth_nil. ring.
  - destruct q as [|b q'].
    + cbn [lnp_add]. rewrite lncv_nth_nil. ring.
    + cbn [lnp_add]. destruct k as [|k'].
      * rewrite !lncv_nth_cons_0. ring.
      * rewrite !lncv_nth_cons_S. apply IH.
Qed.

Lemma lncv_nth_scale : forall (a : Q) (p : list Q) (k : nat), QeqT (nth k (lnp_scale a p) 0) (a * nth k p 0).
Proof.
  intros a p k. apply qeq_imp_qeqT. unfold lnp_scale. revert k.
  induction p as [|b p' IH]; intros k; destruct k as [|k'];
    cbn [map].
  - rewrite !lncv_nth_nil. ring.
  - rewrite !lncv_nth_nil. ring.
  - rewrite !lncv_nth_cons_0. ring.
  - rewrite !lncv_nth_cons_S. apply IH.
Qed.

(* 一步式展开（保内层 lnp_mul 完整） *)
Lemma lncv_mul2_unfold : forall (c0 c1 : Q) (p : list Q),
  lnp_mul (c0 :: c1 :: nil) p
  = lnp_add (lnp_scale c0 p) (cons 0 (lnp_mul (c1 :: nil) p)).
Proof. intros c0 c1 p. reflexivity. Qed.

Lemma lncv_nth_mul1 : forall (c1 : Q) (p : list Q) (k : nat), QeqT (nth k (lnp_mul (c1 :: nil) p) 0) (c1 * nth k p 0).
Proof.
  intros c1 p k. apply qeq_imp_qeqT. cbn [lnp_mul].
  rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
          (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)).
  destruct k as [|k'].
  - rewrite lncv_nth_cons_0. ring.
  - rewrite lncv_nth_cons_S, lncv_nth_nil. ring.
Qed.

Lemma lncv_nth_mul2_S : forall (c0 c1 : Q) (p : list Q) (k : nat), QeqT (nth (Datatypes.S k) (lnp_mul (c0 :: c1 :: nil) p) 0) (c0 * nth (Datatypes.S k) p 0 + c1 * nth k p 0).
Proof.
  intros c0 c1 p k. apply qeq_imp_qeqT. rewrite lncv_mul2_unfold.
  rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
          (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)), lncv_nth_cons_S.
  rewrite (qeqT_imp_qeq _ _ (lncv_nth_mul1 _ _ _)). ring.
Qed.

(* 长度小件 *)
Lemma lncv_length_add : forall p q : list Q,
  length (lnp_add p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p' IH]; intros q; destruct q as [|b q'].
  - cbn [lnp_add length]. lia.
  - cbn [lnp_add length]. lia.
  - cbn [lnp_add length]. lia.
  - cbn [lnp_add length]. rewrite IH. lia.
Qed.

Lemma lncv_length_scale : forall (a : Q) (p : list Q),
  length (lnp_scale a p) = length p.
Proof.
  intros a p. unfold lnp_scale. induction p as [|b p' IH].
  - cbn [map length]. reflexivity.
  - cbn [map length]. rewrite IH. reflexivity.
Qed.

Lemma lncv_length_mul1 : forall (c1 : Q) (p : list Q), p <> nil ->
  length (lnp_mul (c1 :: nil) p) = length p.
Proof.
  intros c1 p Hne. destruct p as [|b p']; [contradiction|].
  cbn [lnp_mul]. rewrite lncv_length_add, lncv_length_scale.
  cbn [length]. lia.
Qed.

Lemma lncv_length_mul2 : forall (c0 c1 : Q) (p : list Q), p <> nil ->
  length (lnp_mul (c0 :: c1 :: nil) p) = Datatypes.S (length p).
Proof.
  intros c0 c1 p Hne. destruct p as [|b p']; [contradiction|].
  rewrite lncv_mul2_unfold.
  rewrite lncv_length_add, lncv_length_scale.
  cbn [length]. rewrite lncv_length_mul1 by exact Hne.
  cbn [length]. lia.
Qed.

(* ============================================================ *)
(* §2 nat→Q 求和机 lncv_sum 与其换序基建                              *)
(* ============================================================ *)

Fixpoint lncv_sum (f : nat -> Q) (k : nat) : Q :=
  match k with
  | 0%nat => f 0%nat
  | Datatypes.S k' => lncv_sum f k' + f (Datatypes.S k')
  end.

Lemma lncv_sum_ext : forall (f g : nat -> Q) (k : nat),
  (forall i : nat, (i <= k)%nat -> QeqT (f i) (g i)) -> QeqT (lncv_sum f k) (lncv_sum g k).
Proof.
  intros f g k. induction k as [|k' IH]; intros H.
  - cbn [lncv_sum]. apply H. lia.
  - cbn [lncv_sum]. apply qeq_imp_qeqT.
    rewrite (fun Hp => qeqT_imp_qeq _ _ (IH Hp)) by (intros i Hi; apply H; lia).
    rewrite (fun Hi => qeqT_imp_qeq _ _ (H (Datatypes.S k') Hi)) by lia.
    apply Qeq_refl.
Qed.

Lemma lncv_sum_add : forall (f g : nat -> Q) (k : nat), QeqT (lncv_sum (fun i => f i + g i) k) (lncv_sum f k + lncv_sum g k).
Proof.
  intros f g k. apply qeq_imp_qeqT. induction k as [|k' IH].
  - cbn [lncv_sum]. ring.
  - cbn [lncv_sum]. rewrite IH. ring.
Qed.

Lemma lncv_sum_scaler : forall (y : Q) (f : nat -> Q) (k : nat), QeqT (lncv_sum (fun i => y * f i) k) (y * lncv_sum f k).
Proof.
  intros y f k. apply qeq_imp_qeqT. induction k as [|k' IH].
  - cbn [lncv_sum]. ring.
  - cbn [lncv_sum]. rewrite IH. ring.
Qed.

(* 头部剥离再索引: Σ_{i≤S k} f i == f 0 + Σ_{i≤k} f (S i) *)
Lemma lncv_sum_reindex : forall (f : nat -> Q) (k : nat), QeqT (lncv_sum f (Datatypes.S k)) (f 0%nat + lncv_sum (fun i => f (Datatypes.S i)) k).
Proof.
  intros f k. apply qeq_imp_qeqT. induction k as [|k' IH].
  - cbn [lncv_sum]. ring.
  - cbn [lncv_sum] in *. rewrite IH. ring.
Qed.

(* 全零和 *)
Lemma lncv_sum_zero : forall (f : nat -> Q) (k : nat),
  (forall i : nat, (i <= k)%nat -> QeqT (f i) (0)) -> QeqT (lncv_sum f k) (0).
Proof.
  intros f k. induction k as [|k' IH]; intros H.
  - cbn [lncv_sum]. apply H. lia.
  - cbn [lncv_sum]. apply qeq_imp_qeqT.
    rewrite (fun Hp => qeqT_imp_qeq _ _ (IH Hp)) by (intros i Hi; apply H; lia).
    rewrite (fun Hi => qeqT_imp_qeq _ _ (H (Datatypes.S k') Hi)) by lia. ring.
Qed.

(* ============================================================ *)
(* §3 二项式系数对应（bkC/bk_Qn_sym 按 BeukersLists.v §A 原样）         *)
(* ============================================================ *)

Fixpoint bkC (n k : nat) : nat :=
  match n with
  | 0%nat => match k with
         | 0%nat => 1%nat
         | Datatypes.S _ => 0%nat
         end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%nat
      | Datatypes.S k' => bkC n' k' + bkC n' (Datatypes.S k')
      end
  end.

(* 出界件: k > n 时 C(n,k) = 0 *)
Lemma lncv_bkC_out : forall n k : nat, (n < k)%nat -> bkC n k = 0%nat.
Proof.
  induction n as [| n IH]; intros k Hk.
  - destruct k as [| k'].
    + lia.
    + reflexivity.
  - destruct k as [| k'].
    + lia.
    + cbn [bkC]. rewrite (IH k') by lia. rewrite (IH (Datatypes.S k')) by lia.
      reflexivity.
Qed.

Lemma lncv_bkC_out_aux : forall n k : nat, (n < k)%nat -> bkC n k = 0%nat.
Proof. exact lncv_bkC_out. Qed.

(* 对角件: C(n,n) = 1 *)
Lemma lncv_bkC_diag : forall n : nat, bkC n n = 1%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [bkC]. rewrite IH.
    assert (Hz : bkC n (Datatypes.S n) = 0%nat)
      by (apply (lncv_bkC_out_aux n (Datatypes.S n)); lia).
    rewrite Hz. reflexivity.
Qed.

(* 对称: C(n,k) = C(n,n−k)（k ≤ n） *)
Lemma lncv_bkC_sym : forall n k : nat, (k <= n)%nat -> bkC n k = bkC n (n - k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0%nat) by lia. subst k. reflexivity.
  - destruct k as [| k'].
    + replace (Datatypes.S n - 0)%nat with (Datatypes.S n) by lia.
      rewrite (lncv_bkC_diag (Datatypes.S n)). reflexivity.
    + replace (Datatypes.S n - Datatypes.S k')%nat with (n - k')%nat by lia.
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : bkC n k' = bkC n (n - k')) by (apply IH; lia).
        assert (H2 : bkC n (Datatypes.S k') = bkC n (n - Datatypes.S k'))
          by (apply IH; lia).
        assert (Hn1 : (n - k' = Datatypes.S (n - Datatypes.S k'))%nat) by lia.
        rewrite Hn1 in H1. rewrite Hn1.
        cbn [bkC]. lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        replace (n - n)%nat with 0%nat by lia.
        cbn [bkC]. rewrite (lncv_bkC_diag n).
        rewrite (lncv_bkC_out_aux n (Datatypes.S n)) by lia.
        reflexivity.
Qed.

(* 列件: C(n,0) = 1 *)
Lemma lncv_bkC_col0 : forall n : nat, bkC n 0%nat = 1%nat.
Proof. intros n. destruct n; reflexivity. Qed.

(* 连接件: C(n,1) = n *)
Lemma lncv_bkC_first : forall n : nat, bkC n 1%nat = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [bkC]. rewrite lncv_bkC_col0, IH. reflexivity.
Qed.

Lemma lncv_bkC_mul_conn : forall n i : nat, i <> 0%nat ->
  (i * bkC (Datatypes.S n) i = Datatypes.S n * bkC n (pred i))%nat.
Proof.
  intros n. induction n as [| n IH]; intros i Hi.
  - destruct i as [| i']; [contradiction|].
    destruct i' as [|i'']; cbn [bkC pred]; lia.
  - destruct i as [| i']; [contradiction|].
    destruct i' as [|i''].
    + (* i = 1 *)
      replace (bkC (Datatypes.S (Datatypes.S n)) 1%nat)
        with (bkC (Datatypes.S n) 0%nat + bkC (Datatypes.S n) 1%nat)%nat
        by reflexivity.
      replace (bkC (Datatypes.S n) (pred 1%nat))
        with (bkC (Datatypes.S n) 0%nat) by reflexivity.
      rewrite lncv_bkC_first. cbn [bkC]. lia.
    + (* i >= 2 *)
      assert (Hi1 : Datatypes.S i'' <> 0%nat) by discriminate.
      assert (H1 := IH (Datatypes.S i'') Hi1).
      assert (H2 := IH (Datatypes.S (Datatypes.S i'')) Hi).
      replace (pred (Datatypes.S (Datatypes.S i'')))
        with (Datatypes.S i'') by reflexivity.
      replace (pred (Datatypes.S i'')) with i'' in H1 by reflexivity.
      replace (pred (Datatypes.S (Datatypes.S i'')))
        with (Datatypes.S i'') in H2 by reflexivity.
      replace (bkC (Datatypes.S (Datatypes.S n)) (Datatypes.S (Datatypes.S i'')))
        with (bkC (Datatypes.S n) (Datatypes.S i'')
              + bkC (Datatypes.S n) (Datatypes.S (Datatypes.S i'')))%nat
        by reflexivity.
      assert (HA : (bkC (Datatypes.S n) (Datatypes.S i'')
                   = bkC n i'' + bkC n (Datatypes.S i''))%nat) by reflexivity.
      assert (HB : (bkC (Datatypes.S n) (Datatypes.S (Datatypes.S i''))
                   = bkC n (Datatypes.S i'') + bkC n (Datatypes.S (Datatypes.S i'')))%nat)
        by reflexivity.
      rewrite HA, HB.
      nia.
Qed.

(* ============================================================ *)
(* §4 Q 层数值机: qneg1（(−1)^k）、qfac（k!）、qnat（nat 像）           *)
(* ============================================================ *)

Fixpoint qneg1 (k : nat) : Q :=
  match k with
  | 0%nat => 1
  | Datatypes.S k' => (-1) * qneg1 k'
  end.

Fixpoint qfac (k : nat) : Q :=
  match k with
  | 0%nat => 1
  | Datatypes.S k' => (Z.of_nat (Datatypes.S k') # 1) * qfac k'
  end.

(* nat 像 Q 简写与换算件 *)
Definition lncv_qz (k : nat) : Q := (Z.of_nat k # 1).

Lemma lncv_qz_mul : forall a b : nat, QeqT (lncv_qz a * lncv_qz b) (lncv_qz (a * b)).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold lncv_qz. rewrite Nat2Z.inj_mul. apply Qeq_refl.
Qed.

Lemma lncv_qz_add : forall a b : nat, QeqT (lncv_qz a + lncv_qz b) (lncv_qz (a + b)).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold lncv_qz, Qeq. cbn [Qplus Qnum Qden]. lia.
Qed.

Lemma lncv_qz_0 : QeqT (lncv_qz 0%nat) (0).
Proof. apply qeq_imp_qeqT. unfold lncv_qz. cbn [Z.of_nat]. apply Qeq_refl. Qed.

Lemma lncv_qz_1 : QeqT (lncv_qz 1%nat) (1).
Proof. apply qeq_imp_qeqT. unfold lncv_qz. cbn [Z.of_nat]. apply Qeq_refl. Qed.

Lemma lncv_qneg1_S : forall k : nat, QeqT (qneg1 (Datatypes.S k)) ((-1) * qneg1 k).
Proof. intro k. apply qeq_imp_qeqT. cbn [qneg1]. apply Qeq_refl. Qed.

Lemma lncv_qneg1_add : forall a b : nat, QeqT (qneg1 (a + b)) (qneg1 a * qneg1 b).
Proof.
  intros a b. apply qeq_imp_qeqT. induction a as [|a IH].
  - cbn [qneg1 Nat.add]. ring.
  - cbn [qneg1 Nat.add]. rewrite IH. ring.
Qed.

Lemma lncv_qneg1_sq : forall k : nat, QeqT (qneg1 k * qneg1 k) (1).
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [|k IH].
  - cbn [qneg1]. ring.
  - cbn [qneg1]. rewrite <- IH. ring.
Qed.

Lemma lncv_qfac_ne0 : forall k : nat, QeqT (qfac k) 0 -> Empty_set.
Proof.
  induction k as [|k IH].
  - intro Hz. vm_compute in Hz. inversion Hz.
  - intro Hz. cbn [qfac] in Hz.
    apply IH. apply qeq_imp_qeqT.
    apply (Qmult_integral_l (Z.of_nat (Datatypes.S k) # 1) (qfac k)).
    + intro Hbad. vm_compute in Hbad. discriminate.
    + exact (qeqT_imp_qeq _ _ Hz).
Qed.

(* nat 像 Q 乘/加 *)
Lemma lncv_qnat_mul : forall a b : nat, QeqT ((Z.of_nat a # 1) * (Z.of_nat b # 1)) (((Z.of_nat (a * b)) # 1)).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qeq. cbn [Qmult Qnum Qden]. lia.
Qed.

Lemma lncv_qnat_add : forall a b : nat, QeqT ((Z.of_nat a # 1) + (Z.of_nat b # 1)) (((Z.of_nat (a + b)) # 1)).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qeq. cbn [Qplus Qnum Qden]. lia.
Qed.

(* 纯变量环小件 *)
Lemma lncv_ring_wsplit : forall (w c y z : Q), QeqT (w * (c + y * z)) (w * c + w * (y * z)).
Proof. intros w c y z. apply qeq_imp_qeqT. ring. Qed.

Lemma lncv_ring_aisplit : forall (w av iy z : Q), QeqT (w * ((av + iy) * z)) (w * (av * z) + w * (iy * z)).
Proof. intros w av iy z. apply qeq_imp_qeqT. ring. Qed.

(* q_pow 小件 *)
Lemma lncv_qpow_congr : forall (a b : Q) (k : nat), QeqT (a) (b)-> QeqT (q_pow a k) (q_pow b k).
Proof.
  intros a b k Hab. apply qeq_imp_qeqT. induction k as [|k IH].
  - apply Qeq_refl.
  - cbn [q_pow]. rewrite IH, (qeqT_imp_qeq _ _ Hab). apply Qeq_refl.
Qed.

Lemma lncv_qpow_mul_split : forall (x y : Q) (k : nat), QeqT (q_pow (x * y) k) (q_pow x k * q_pow y k).
Proof.
  intros x y k. apply qeq_imp_qeqT. induction k as [|k IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma lncv_qpow_neg1 : forall k : nat, QeqT (q_pow (-1) k) (qneg1 k).
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [|k IH].
  - cbn [q_pow qneg1]. apply Qeq_refl.
  - cbn [q_pow]. rewrite IH. cbn [qneg1]. apply Qeq_refl.
Qed.

Lemma lncv_qpow_neg2_split : forall k : nat, QeqT (q_pow (-2) k) (qneg1 k * q_pow (2 # 1) k).
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [|k IH].
  - cbn [q_pow qneg1]. ring.
  - cbn [q_pow]. rewrite IH, (qeqT_imp_qeq _ _ (lncv_qneg1_S k)). ring.
Qed.

Lemma lncv_qpow2_nat : forall k : nat, QeqT (q_pow (2 # 1) k) (((Z.of_nat (Nat.pow 2%nat k)) # 1)).
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [|k IH].
  - cbn [q_pow Nat.pow]. apply Qeq_refl.
  - cbn [Nat.pow]. rewrite q_pow_succ, IH.
    apply qeqT_imp_qeq. apply (lncv_qnat_mul 2%nat (Nat.pow 2%nat k)).
Qed.

(* nat 幂右步进（lia 辅助位） *)
Lemma lncv_pow2_succ : forall k : nat, (Nat.pow 2 (Datatypes.S k) = 2 * Nat.pow 2 k)%nat.
Proof. intro k. reflexivity. Qed.

(* ============================================================ *)
(* §5 去尾对应 + δ-差分泛函（Josephson 桥）+ 逐点→系数提取             *)
(* ============================================================ *)

(* 去尾（截最高位; 稠密表头=常数项; 对应 qpg_remlast） *)
Fixpoint lnp_remlast (p : list Q) : list Q :=
  match p with
  | nil => nil
  | cons a p' =>
      match p' with
      | nil => nil
      | cons _ _ => a :: lnp_remlast p'
      end
  end.

Lemma lncv_remlast_cons2 : forall (a b : Q) (L : list Q),
  lnp_remlast (a :: b :: L) = a :: lnp_remlast (b :: L).
Proof. intros a b L. reflexivity. Qed.

Lemma lncv_remlast_length : forall p : list Q,
  length (lnp_remlast p) = Nat.pred (length p).
Proof.
  induction p as [|a p' IH].
  - reflexivity.
  - destruct p' as [|b p''].
    + reflexivity.
    + rewrite (lncv_remlast_cons2 a b p''). cbn [length].
      rewrite IH. reflexivity.
Qed.

(* 首项系数为零的表，去尾不改求值（对应 qpg_eval_remlast0 之 nth 形） *)
Lemma lncv_remlast_eval0 : forall (p : list Q) (x : Q), QeqT (nth (Nat.pred (length p)) p 0) (0)-> QeqT (lnp_eval (lnp_remlast p) x) (lnp_eval p x).
Proof.
  induction p as [|a p' IH]; intros x H.
  - cbn [lnp_remlast lnp_eval]. apply qeq_imp_qeqT. apply Qeq_refl.
  - destruct p' as [|b p''].
    + cbn [lnp_remlast lnp_eval length pred nth] in *.
      apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ H). ring.
    + assert (H2 : QeqT (nth (Nat.pred (length (b :: p''))) (b :: p'') 0) 0).
      { cbn [length pred] in H.
        rewrite lncv_nth_cons_S in H. exact H. }
      rewrite (lncv_remlast_cons2 a b p'').
      cbn [lnp_eval]. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (IH x H2)). cbn [lnp_eval]. ring.
Qed.

(* 前缀保序: 去尾不动第 k < pred(长度) 位 *)
Lemma lncv_nth_remlast_prefix : forall (W : list Q) (k : nat),
  (Datatypes.S k <= Nat.pred (length W))%nat -> QeqT (nth k W 0) (nth k (lnp_remlast W) 0).
Proof.
  induction W as [|a W' IH]; intros k Hk.
  - cbn [length pred] in Hk. lia.
  - destruct W' as [|b W''].
    + cbn [length pred lnp_remlast] in Hk. lia.
    + destruct k as [|k'].
      * apply qeq_imp_qeqT. reflexivity.
      * cbn [lnp_remlast]. apply qeq_imp_qeqT. rewrite !lncv_nth_cons_S.
        apply qeqT_imp_qeq. apply IH. cbn [length pred] in Hk |- *. lia.
Qed.

(* 头项剥离式（reindex 之差形） *)
Lemma lncv_sum_shift : forall (f : nat -> Q) (k : nat), QeqT (lncv_sum (fun i => f (Datatypes.S i)) k) (lncv_sum f (Datatypes.S k) - f 0%nat).
Proof.
  intros f k. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lncv_sum_reindex _ _)). ring.
Qed.





(* ============================================================ *)
(* \u00a76 nat \u5c42\u52a0\u6743\u548c\u4e0e\u4e2d\u5fc3 Delannoy \u6570\uff08bk_psd/bk_Qn_qtilde \u955c\u50cf\uff09           *)
(* ============================================================ *)

Fixpoint bk_psd (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | Datatypes.S m => 2 * bk_psd f m + f m
  end.

Definition bk_Qn_qtilde (n : nat) : nat :=
  bk_psd (fun k => (bkC n k * bkC n k)%nat) (Datatypes.S n).

Lemma lncv_qtilde_pin_4 : bk_Qn_qtilde 4%nat = 321%nat.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* \u00a77 \u7ebf\u6027\u8868\u955c\u50cf\u4e0e\u88ab\u9664\u5f0f/\u9664\u5f0f\u7f16\u7801\u9762\uff08lnc_lin_t \u7cfb\u9010\u5b9a\u4e49\u955c\u50cf\uff09            *)
(* ============================================================ *)

Definition lnp_lin_t : list Q := cons 0 (cons 1 nil).
Definition lnp_lin_1mt : list Q := cons 1 (cons (-1) nil).
Definition lnp_den_lin : list Q := cons 1 (cons (-(1 # 2)) nil).

Fixpoint lnp_bk_num (n : nat) : list Q :=
  match n with
  | 0%nat => cons 1 nil
  | Datatypes.S n' => lnp_mul (lnp_mul lnp_lin_t lnp_lin_1mt) (lnp_bk_num n')
  end.

Definition lnp_bk_den (n : nat) : list Q := lnp_pow lnp_den_lin (Datatypes.S n).

Lemma lncv_eval_lin_t : forall x : Q, QeqT (lnp_eval lnp_lin_t x) (x).
Proof. intros x. apply qeq_imp_qeqT. cbn [lnp_lin_t lnp_eval]. ring. Qed.

Lemma lncv_eval_lin_1mt : forall x : Q, QeqT (lnp_eval lnp_lin_1mt x) (1 - x).
Proof. intros x. apply qeq_imp_qeqT. cbn [lnp_lin_1mt lnp_eval]. ring. Qed.

Lemma lncv_eval_den_lin : forall x : Q, QeqT (lnp_eval lnp_den_lin x) (1 + x * (-(1 # 2))).
Proof. intros x. apply qeq_imp_qeqT. cbn [lnp_den_lin lnp_eval]. ring. Qed.

Lemma lncv_bk_num_eval : forall (n : nat) (x : Q), QeqT (lnp_eval (lnp_bk_num n) x) (q_pow (x * (1 - x)) n).
Proof.
  intros n x. apply qeq_imp_qeqT.
  revert x. induction n as [|n' IH]; intros x.
  - cbn [lnp_bk_num lnp_eval q_pow]. ring.
  - cbn [lnp_bk_num].
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_mul _ _ _)),
            (qeqT_imp_qeq _ _ (lncv_eval_mul _ _ _)).
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_lin_t _)),
            (qeqT_imp_qeq _ _ (lncv_eval_lin_1mt _)), IH.
    cbn [q_pow]. apply Qeq_refl.
Qed.

Lemma lncv_bk_den_eval : forall (n : nat) (x : Q), QeqT (lnp_eval (lnp_bk_den n) x) (q_pow (1 + x * (-(1 # 2))) (Datatypes.S n)).
Proof.
  intros n x. apply qeq_imp_qeqT. unfold lnp_bk_den.
  rewrite (qeqT_imp_qeq _ _ (lncv_eval_pow _ _ _)),
          (qeqT_imp_qeq _ _ (lncv_eval_den_lin _)).
  apply Qeq_refl.
Qed.

(* u \u5750\u6807\u4ee3\u5165: R(2\u22122u)\uff08\u58f0\u97f3\u6027\u955c\u50cf lnc_comp2_eval\uff1bd_j = nth j\uff09 *)
Fixpoint lnp_comp2 (R : list Q) : list Q :=
  match R with
  | nil => nil
  | cons c R' =>
      lnp_add (cons c nil)
        (lnp_scale (2 # 1) (lnp_mul lnp_lin_1mt (lnp_comp2 R')))
  end.

Definition lnp_d1 (n : nat) (R : list Q) : Q := nth n (lnp_comp2 R) 0.

Lemma lncv_ring_comp_step : forall c E u : Q, QeqT (c + (2 # 1) * ((1 - u) * E)) (c + (2 - 2 * u) * E).
Proof. intros c E u. apply qeq_imp_qeqT. ring. Qed.

Lemma lncv_comp2_eval : forall (R : list Q) (u : Q), QeqT (lnp_eval (lnp_comp2 R) u) (lnp_eval R (2 - 2 * u)).
Proof.
  intros R u. apply qeq_imp_qeqT.
  revert u. induction R as [|c R' IH]; intros u.
  - cbn [lnp_comp2 lnp_eval]. apply Qeq_refl.
  - cbn [lnp_comp2].
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_add _ _ _)),
            (qeqT_imp_qeq _ _ (lncv_eval_scale _ _ _)),
            (qeqT_imp_qeq _ _ (lncv_eval_mul _ _ _)).
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_lin_1mt _)), IH.
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_cons c R' (2 - 2 * u))).
    rewrite (qeqT_imp_qeq _ _ (lncv_eval_cons c nil u)). cbn [lnp_eval]. ring.
Qed.

(* ============================================================ *)
(* \u00a78 \u80a2(a) \u5377\u79ef\u7cfb\u6570\u80a2\u4e0e\u80a2(b) \u4e8c\u9879\u5f0f\u5e42\u7cfb\u6570\u80a2\uff08\u7f3a\u53e3\u7532\u57fa\u5efa\u4ea4\u4ed8\u9762\uff09          *)
(* ============================================================ *)

Lemma lncv_nth_mul_gen : forall (p q : list Q) (k : nat), QeqT (nth k (lnp_mul p q) 0) (lncv_sum (fun j => nth j p 0 * nth (k - j) q 0) k).
Proof.
  intros p q k. apply qeq_imp_qeqT.
  revert q k. induction p as [|c p' IH]; intros q k.
  - cbn [lnp_mul]. rewrite lncv_nth_nil.
    apply Qeq_sym. apply qeqT_imp_qeq. apply lncv_sum_zero.
    intros i _. rewrite lncv_nth_nil. apply qeq_imp_qeqT. ring.
  - destruct k as [|k'].
    + cbn [lnp_mul].
      rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
              (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)), lncv_nth_cons_0.
      cbn [lncv_sum]. rewrite lncv_nth_cons_0, Nat.sub_0_l. ring.
    + cbn [lnp_mul].
      rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
              (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)), lncv_nth_cons_S.
      rewrite (IH q k').
      rewrite (qeqT_imp_qeq _ _ (lncv_sum_reindex _ _)).
      cbn [lncv_sum nth].
      rewrite Nat.sub_0_r.
      assert (Hsub : lncv_sum
                 (fun j => nth j p' 0 * nth (Datatypes.S k' - Datatypes.S j) q 0) k'
                 == lncv_sum (fun j => nth j p' 0 * nth (k' - j) q 0) k').
      { apply qeqT_imp_qeq. apply lncv_sum_ext. intros i _. apply qeq_imp_qeqT. apply Qeq_refl. }
      rewrite Hsub.
      apply Qeq_refl.
Qed.

(* 幂一步件: [1;c]·P 的 k 系数 = P_k + c·P_{k-1}（分 k=0 / k=S 两形） *)
Lemma lncv_nth_pow_step0 : forall (c : Q) (n : nat), QeqT (nth 0%nat (lnp_pow (cons 1 (cons c nil)) (Datatypes.S n)) 0) (nth 0%nat (lnp_pow (cons 1 (cons c nil)) n) 0).
Proof.
  intros c n. apply qeq_imp_qeqT. cbn [lnp_pow]. rewrite lncv_mul2_unfold.
  rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
          (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)), lncv_nth_cons_0. ring.
Qed.

Lemma lncv_nth_pow_stepS : forall (c : Q) (n k : nat), QeqT (nth (Datatypes.S k) (lnp_pow (cons 1 (cons c nil)) (Datatypes.S n)) 0) (nth (Datatypes.S k) (lnp_pow (cons 1 (cons c nil)) n) 0
     + c * nth k (lnp_pow (cons 1 (cons c nil)) n) 0).
Proof.
  intros c n k. apply qeq_imp_qeqT. cbn [lnp_pow]. rewrite lncv_mul2_unfold.
  rewrite (qeqT_imp_qeq _ _ (lncv_nth_add _ _ _)),
          (qeqT_imp_qeq _ _ (lncv_nth_scale _ _ _)), lncv_nth_cons_S,
          (qeqT_imp_qeq _ _ (lncv_nth_mul1 _ _ _)). ring.
Qed.

Lemma lncv_nth_pow_binom : forall (c : Q) (n k : nat), QeqT (nth k (lnp_pow (cons 1 (cons c nil)) n) 0) (q_pow c k * lncv_qz (bkC n k)).
Proof.
  intros c n. induction n as [|n IH]; intros k.
  - destruct k as [|k'].
    + cbn [lnp_pow nth bkC]. apply qeq_imp_qeqT. apply Qeq_refl.
    + apply qeq_imp_qeqT. cbn [lnp_pow]. rewrite lncv_nth_cons_S, lncv_nth_nil.
      cbn [bkC]. rewrite (qeqT_imp_qeq _ _ lncv_qz_0). ring.
  - destruct k as [|k'].
    + apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (lncv_nth_pow_step0 _ _)).
      rewrite (qeqT_imp_qeq _ _ (IH 0%nat)). rewrite lncv_bkC_col0.
      apply Qeq_refl.
    + apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (lncv_nth_pow_stepS _ _ _)).
      rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k'))), (qeqT_imp_qeq _ _ (IH k')).
      cbn [bkC q_pow].
      rewrite <- (qeqT_imp_qeq _ _
                    (lncv_qz_add (bkC n k') (bkC n (Datatypes.S k')))).
      ring.
Qed.

(* ============================================================ *)
(* \u00a79 \u9a8c\u6536\u9762: \u826f\u6001\u5206\u89e3\u524d\u63d0\u9762 + d_j \u5bb9\u5668\u767b\u8bb0 + \u5934\u9879\u5168 n \u5f62\u65bd\u5de5          *)
(* ============================================================ *)

(* \u826f\u6001\u5206\u89e3\u524d\u63d0\u9762\uff08qpd_divmod_gen_pred \u672c\u6c60\u955c\u50cf: \u6052\u7b49\u5f0f\u80a2 + \u6b21\u6570\u80a2\uff09 *)
Definition lnp_div_pred (p q : list Q) (w : list Q * list Q) : Set :=
  And (forall x : Q, QeqT (lnp_eval p x)
              (lnp_eval q x * lnp_eval (fst w) x + lnp_eval (snd w) x))
      (Id true (Nat.ltb (Nat.pred (length (snd w)))
                             (Nat.pred (length q)))).

(* \u4e00\u822c n \u5e26\u4f59\u5206\u89e3\u5bb9\u5668\uff08\u767b\u8bb0\u9762, \u5f15\u64ce\u4f4d\u5728 #225 \u6811\u4fa7\uff09 *)
Definition lncv_div_gen_type (n : nat) : Set :=
  sigT (fun w : list Q * list Q =>
          lnp_div_pred (lnp_bk_num n) (lnp_bk_den n) w).

(* \u4e00\u822c n \u5168\u5f62 d_j == 2^n\u00b7q\u0303_n \u9a8c\u6536\u5bb9\u5668\uff08\u767b\u8bb0\u9762; \u65bd\u5de5\u9700\u6052\u96f6\u63d0\u53d6\u80a2, *)
(*  \u8be5\u80a2\u7cfb\u5dee\u5206/Vandermonde \u7ea7\u5f15\u64ce, \u672c\u5207\u7247\u9884\u7b97\u5916, \u8bda\u5b9e\u7559\u5f85\uff09 *)
Definition lncv_d1_gen_type (n : nat) : Set :=
  forall w : list Q * list Q,
    lnp_div_pred (lnp_bk_num n) (lnp_bk_den n) w ->
    sigT (fun z : Z =>
            QeqT (lnp_d1 n (snd w))
                 ((Z.of_nat (Nat.pow 2 n * bk_Qn_qtilde n)%nat # 1))).

Lemma lncv_qpow_0_S : forall k : nat, QeqT (q_pow 0 (Datatypes.S k)) (0).
Proof. intro k. apply qeq_imp_qeqT. cbn [q_pow]. ring. Qed.

Lemma lncv_ring_zero_add : forall a E : Q, QeqT (0 * a + E) (E).
Proof. intros a E. apply qeq_imp_qeqT. ring. Qed.

Lemma lncv_num_eval_2 : forall n : nat, QeqT (lnp_eval (lnp_bk_num n) (2 # 1)) (q_pow ((-2) # 1) n).
Proof. intros n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lncv_bk_num_eval n (2 # 1))).
  apply qeqT_imp_qeq. apply lncv_qpow_congr. apply qeq_imp_qeqT. ring. Qed.

Lemma lncv_den_eval_2 : forall n : nat, QeqT (lnp_eval (lnp_bk_den n) (2 # 1)) (0).
Proof.
  intros n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lncv_bk_den_eval n (2 # 1))).
  assert (Hz : 1 + (2 # 1) * (-(1 # 2)) == 0) by ring.
  rewrite (qeqT_imp_qeq _ _ (lncv_qpow_congr _ 0 (Datatypes.S n) (qeq_imp_qeqT _ _ Hz))).
  apply qeqT_imp_qeq. apply lncv_qpow_0_S.
Qed.

Theorem lncv_d1_head_gen : forall (n : nat) (w : list Q * list Q),
  lnp_div_pred (lnp_bk_num n) (lnp_bk_den n) w ->
  QeqT (nth 0%nat (lnp_comp2 (snd w)) 0) (q_pow ((-2) # 1) n).
Proof.
  intros n [qq rr] Hp. unfold lnp_div_pred in Hp. cbn [fst snd] in Hp |- *.
  assert (H := fst Hp (2 # 1)).
  apply qeqT_imp_qeq in H.
  rewrite (qeqT_imp_qeq _ _ (lncv_num_eval_2 n)),
          (qeqT_imp_qeq _ _ (lncv_den_eval_2 n)) in H.
  assert (Hr : lnp_eval rr (2 # 1) == q_pow ((-2) # 1) n).
  { rewrite <- (qeqT_imp_qeq _ _ (lncv_ring_zero_add (lnp_eval qq (2 # 1))
                  (lnp_eval rr (2 # 1)))).
    apply (Qeq_sym _ _ H). }
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (lnp_eval (lnp_comp2 rr) 0)).
  - apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (lncv_eval_0 (lnp_comp2 rr)))).
  - rewrite (qeqT_imp_qeq _ _ (lncv_comp2_eval rr 0)). exact Hr.
Qed.

(* Z \u89c1\u8bc1: (\u22122)^n \u7684 Z \u627f\u8f7d *)
Fixpoint lncv_zneg2 (k : nat) : Z :=
  match k with
  | 0%nat => 1%Z
  | Datatypes.S k' => (-2)%Z * lncv_zneg2 k'
  end.

Lemma lncv_qmul_z1 : forall u v : Z, QeqT ((u # 1) * (v # 1)) (((u * v) # 1)).
Proof. intros u v. apply qeq_imp_qeqT. apply Qeq_refl. Qed.

Lemma lncv_qpow_zneg2 : forall k : nat, QeqT (q_pow ((-2) # 1) k) (((lncv_zneg2 k) # 1)).
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [|k IH].
  - apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity.
  - cbn [q_pow lncv_zneg2]. rewrite IH. apply qeqT_imp_qeq. apply lncv_qmul_z1.
Qed.

Theorem lncv_d1_head_int_gen : forall (n : nat) (w : list Q * list Q),
  lnp_div_pred (lnp_bk_num n) (lnp_bk_den n) w ->
  sigT (fun z : Z => QeqT (nth 0%nat (lnp_comp2 (snd w)) 0) ((z # 1))).
Proof.
  intros n w Hw. exists (lncv_zneg2 n).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (q_pow ((-2) # 1) n)).
  - apply qeqT_imp_qeq. exact (lncv_d1_head_gen n w Hw).
  - apply qeqT_imp_qeq. apply lncv_qpow_zneg2.
Qed.

(* ============================================================ *)
(* \u00a710 \u63d0\u53d6\u9762\uff08Separate Extraction\uff09                                       *)
(* ============================================================ *)

Separate Extraction lnp_eval lnp_add lnp_scale lnp_mul lnp_pow lnp_comp2
  lnp_bk_num lnp_bk_den bkC bk_psd bk_Qn_qtilde lnp_d1.

(* ============================================================ *)
(* §11 假设审计（Print Assumptions 全列取证）                              *)
(* ============================================================ *)

Print Assumptions lncv_S.
Print Assumptions lnp_eval.
Print Assumptions lnp_add.
Print Assumptions lnp_scale.
Print Assumptions lnp_mul.
Print Assumptions lnp_pow.
Print Assumptions lncv_eval_nil.
Print Assumptions lncv_eval_cons.
Print Assumptions lncv_eval_0.
Print Assumptions lncv_eval_add.
Print Assumptions lncv_eval_scale.
Print Assumptions lncv_ring_mul_step.
Print Assumptions lncv_eval_mul.
Print Assumptions lncv_eval_pow.
Print Assumptions lncv_nth_nil.
Print Assumptions lncv_nth_cons_0.
Print Assumptions lncv_nth_cons_S.
Print Assumptions lncv_nth_oob.
Print Assumptions lncv_nth_add.
Print Assumptions lncv_nth_scale.
Print Assumptions lncv_mul2_unfold.
Print Assumptions lncv_nth_mul1.
Print Assumptions lncv_nth_mul2_S.
Print Assumptions lncv_length_add.
Print Assumptions lncv_length_scale.
Print Assumptions lncv_length_mul1.
Print Assumptions lncv_length_mul2.
Print Assumptions lncv_sum.
Print Assumptions lncv_sum_ext.
Print Assumptions lncv_sum_add.
Print Assumptions lncv_sum_scaler.
Print Assumptions lncv_sum_reindex.
Print Assumptions lncv_sum_zero.
Print Assumptions bkC.
Print Assumptions lncv_bkC_out.
Print Assumptions lncv_bkC_out_aux.
Print Assumptions lncv_bkC_diag.
Print Assumptions lncv_bkC_sym.
Print Assumptions lncv_bkC_first.
Print Assumptions lncv_bkC_col0.
Print Assumptions lncv_bkC_mul_conn.
Print Assumptions qneg1.
Print Assumptions qfac.
Print Assumptions lncv_qz.
Print Assumptions lncv_qz_mul.
Print Assumptions lncv_qz_add.
Print Assumptions lncv_qz_0.
Print Assumptions lncv_qz_1.
Print Assumptions lncv_qneg1_S.
Print Assumptions lncv_qneg1_add.
Print Assumptions lncv_qneg1_sq.
Print Assumptions lncv_qfac_ne0.
Print Assumptions lncv_qnat_mul.
Print Assumptions lncv_qnat_add.
Print Assumptions lncv_ring_wsplit.
Print Assumptions lncv_ring_aisplit.
Print Assumptions lncv_qpow_congr.
Print Assumptions lncv_qpow_mul_split.
Print Assumptions lncv_qpow_neg1.
Print Assumptions lncv_qpow_neg2_split.
Print Assumptions lncv_qpow2_nat.
Print Assumptions lncv_pow2_succ.
Print Assumptions lnp_remlast.
Print Assumptions lncv_remlast_cons2.
Print Assumptions lncv_remlast_length.
Print Assumptions lncv_remlast_eval0.
Print Assumptions lncv_nth_remlast_prefix.
Print Assumptions lncv_sum_shift.
Print Assumptions bk_psd.
Print Assumptions bk_Qn_qtilde.
Print Assumptions lncv_qtilde_pin_4.
Print Assumptions lnp_lin_t.
Print Assumptions lnp_lin_1mt.
Print Assumptions lnp_den_lin.
Print Assumptions lnp_bk_num.
Print Assumptions lnp_bk_den.
Print Assumptions lncv_eval_lin_t.
Print Assumptions lncv_eval_lin_1mt.
Print Assumptions lncv_eval_den_lin.
Print Assumptions lncv_bk_num_eval.
Print Assumptions lncv_bk_den_eval.
Print Assumptions lnp_comp2.
Print Assumptions lnp_d1.
Print Assumptions lncv_ring_comp_step.
Print Assumptions lncv_comp2_eval.
Print Assumptions lncv_nth_mul_gen.
Print Assumptions lncv_nth_pow_step0.
Print Assumptions lncv_nth_pow_stepS.
Print Assumptions lncv_nth_pow_binom.
Print Assumptions lnp_div_pred.
Print Assumptions lncv_div_gen_type.
Print Assumptions lncv_d1_gen_type.
Print Assumptions lncv_qpow_0_S.
Print Assumptions lncv_ring_zero_add.
Print Assumptions lncv_num_eval_2.
Print Assumptions lncv_den_eval_2.
Print Assumptions lncv_d1_head_gen.
Print Assumptions lncv_zneg2.
Print Assumptions lncv_qmul_z1.
Print Assumptions lncv_qpow_zneg2.
Print Assumptions lncv_d1_head_int_gen.
