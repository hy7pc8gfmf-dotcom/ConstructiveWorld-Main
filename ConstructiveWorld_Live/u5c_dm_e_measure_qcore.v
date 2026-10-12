(* 五字段指针｜使命：e（自然指数级数和 X = lim Σ_{k≥0} 1/k!）的无理性测度闭式件——
   对任意有理数 q = a/b，输出只依赖分母 b 的显式分离常数 c := 1/(4·b·(b+7)!)，
   使部分和序列自第 b+7 项起与 q 的距离恒大于 c（纯 Q 核心 dmeq_e_qcore），
   并装配为实层分离 real_const c < |X − q|（u5c_e_closed_measure）。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion；Stdlib QArith、Qabs、ZArith、
   Arith、Bool、Arith.Factorial、Lia、Setoid、Morphisms、Qfield、Extraction。
   对标行：u5c_inst_e.v u5c_e_criterion_escape_pt（枚举逃逸点路线，常元非闭式）；
   u5c_dm_escape_to_dist_any.v dmec_escape_to_dist_any（边距参数化桥，本件未引——
   其窗口逃逸前提与闭式常元路线不匹配，实层装配改走 Q 核直引 + lic_metric_proj 直链）；
   SumInvFactEscape.v sif_*（n! 整数化与分式桥）；
   UpReqIrrationalCriterion.v lic_tail_e / lic_vanish_e / lic_exp_diff / lic_rsum_*。
   构造性注记：语句面全 Set 层（sigT/prod/QltT/Id），零 Prop 前提位；分情形由
   Q_dec 三分和型（Set 层 sumbool）产出；量化隙 dmeq_gap（整隙 1 ≤ |分子| 配
   sif_abs_frac 分式桥）、尾控闭式 dmeq_tail_lt（几何级数归纳，尾 < 1/(n·n!)）、
   逃逸比条件 n0 − b ≥ 1 三件套全构造；零承认、零经典逻辑、零全局假设。
   设计确定（对预研基线的修正，响亮申报）：基线逃逸步「3/(n0+1)! < 1/(2b·n0!)」
   等价 5b < 7，仅 b=1 成立，b≥2 失效；本件改尾控锐化为 e−s(n0) < 1/(n0·n0!)
   （n0 := b+6，几何级数和 < (n+1)/n 自建），并取统一闭式 c := 1/(4·b·(b+7)!)：
   CaseA（q ≠ s(n0)）隙−尾 = (n0−b)/(b·n0·n0!) ≥ c ⟸ 24(n0+1) ≥ n0 恒真；
   CaseB（q = s(n0)）尾 ≥ 1/(n0+1)! ≥ c ⟸ 4b ≥ 1 恒真——单式通吃两分支，
   无需 Qmin 取小，也无需双常元和式。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_dm_e_measure_qcore.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：Q 层算术微件（消去/单调/倒数/减法，全自建 dmeq_ 前缀）          *)
(* ============================================================ *)

Lemma dmeq_mult_0_r : forall x : Q, QeqT (x * 0)%Q 0%Q.
Proof.
  intro x. apply qeq_imp_qeqT.
  unfold Qmult, Qeq. cbn [Qnum Qden Qmult]. first [ring | nia | lia].
Qed.

Lemma dmeq_mult_0_l : forall x : Q, QeqT (0 * x)%Q 0%Q.
Proof.
  intro x. apply qeq_imp_qeqT. destruct x as [x1 x2].
  unfold Qmult, Qeq. cbn [Qnum Qden Qmult].
  first [ring | nia | lia].
Qed.

Lemma dmeq_minus_plus_cancel : forall x y : Q, QeqT x ((x - y) + y)%Q.
Proof.
  intros x y. apply qeq_imp_qeqT. apply Qeq_sym. apply lic_qlt_minus_add_r.
Qed.

Lemma dmeq_sub_split : forall x y z : Q, QeqT (x - y)%Q ((x - z) + (z - y))%Q.
Proof.
  intros x y z. apply qeq_imp_qeqT. apply lic_qlt_tri_decomp.
Qed.

Lemma dmeq_plus_minus_r : forall b e : Q, QeqT ((b + e) - e)%Q b.
Proof.
  intros b e. apply qeq_imp_qeqT. destruct b as [b1 b2]. destruct e as [e1 e2].
  unfold Qminus, Qeq. cbn [Qnum Qden Qplus Qopp Qmult].
  first [ring | nia | lia].
Qed.

Lemma dmeq_le_add_r : forall x z : Q, QleT' 0%Q z -> QleT' x ((x + z)%Q).
Proof.
  intros x z Hz.
  pose proof (Qplus_le_compat x x 0%Q z (Qle_refl x) (QleT'_to_Qle _ _ Hz)) as H.
  rewrite Qplus_0_r in H. apply Qle_to_QleT'. exact H.
Qed.

Lemma dmeq_lt_add_r : forall x t : Q, QltT 0%Q t -> QltT x ((x + t)%Q).
Proof.
  intros x t Ht. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Ht) as Ht'.
  destruct x as [x1 x2]. destruct t as [t1 t2].
  unfold Qlt, Qplus in *. cbn [Qnum Qden Qmult] in *.
  assert (H2 : (0 < Z.pos x2)%Z) by apply sif_posZ.
  assert (H3 : (0 < Z.pos t2)%Z) by apply sif_posZ.
  nia.
Qed.

Lemma dmeq_0_lt_sub : forall z b : Q, QltT z b -> QltT 0%Q ((b - z)%Q).
Proof.
  intros z b Hlt. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hlt) as Hlt'.
  destruct z as [z1 z2]. destruct b as [b1 b2].
  unfold Qlt, Qminus, Qplus, Qopp in *. cbn [Qnum Qden Qmult] in *.
  assert (H2 : (0 < Z.pos z2)%Z) by apply sif_posZ.
  assert (H3 : (0 < Z.pos b2)%Z) by apply sif_posZ.
  nia.
Qed.

Lemma dmeq_le_mono_sub_r : forall x y z : Q,
  QleT' x y -> QleT' ((x - z)%Q) ((y - z)%Q).
Proof.
  intros x y z H. apply Qle_to_QleT'.
  exact (Qplus_le_compat x y (- z) (- z) (QleT'_to_Qle _ _ H) (Qle_refl (- z))).
Qed.

Lemma dmeq_le_sub_reg : forall a b e : Q,
  QleT' a ((b + e)%Q) -> QleT' ((a - e)%Q) b.
Proof.
  intros a b e H.
  pose proof (dmeq_le_mono_sub_r a (b + e) e H) as H1.
  apply QleT'_to_Qle in H1.
  rewrite (qeqT_imp_qeq _ _ (dmeq_plus_minus_r b e)) in H1.
  exact (Qle_to_QleT' _ _ H1).
Qed.

Lemma dmeq_sub_lt_mono_r : forall a z b : Q,
  QltT z b -> QltT ((a - b)%Q) ((a - z)%Q).
Proof.
  intros a z b Hlt. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hlt) as Hlt'.
  destruct a as [a1 a2]. destruct z as [z1 z2]. destruct b as [b1 b2].
  unfold Qlt, Qminus, Qplus, Qopp in *. cbn [Qnum Qden Qmult] in *.
  assert (Ha : (0 < Z.pos a2)%Z) by apply sif_posZ.
  assert (Hz : (0 < Z.pos z2)%Z) by apply sif_posZ.
  assert (Hb : (0 < Z.pos b2)%Z) by apply sif_posZ.
  nia.
Qed.

Lemma dmeq_mult_le_compat_r : forall x y z : Q,
  QleT' 0%Q z -> QleT' x y -> QleT' (x * z)%Q (y * z)%Q.
Proof.
  intros x y z Hz Hxy.
  pose proof (QleT'_to_Qle _ _ Hz) as Hz'.
  pose proof (QleT'_to_Qle _ _ Hxy) as Hxy'.
  apply Qle_to_QleT'.
  destruct (Qle_lt_or_eq 0%Q z Hz') as [Hzlt | Hzeq].
  - destruct (Qle_lt_or_eq x y Hxy') as [Hlt | Heq].
    + apply Qlt_le_weak. exact (Qmult_lt_compat_r x y z Hzlt Hlt).
    + rewrite Heq. apply Qle_refl.
  - rewrite <- Hzeq. rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_r x)).
    rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_r y)).
    apply Qle_refl.
Qed.

Lemma dmeq_mult_le_compat_l : forall x y z : Q,
  QleT' 0%Q x -> QleT' y z -> QleT' (x * y)%Q (x * z)%Q.
Proof.
  intros x y z Hx Hyz.
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hyz) as Hyz'.
  apply Qle_to_QleT'.
  destruct (Qle_lt_or_eq 0%Q x Hx') as [Hxlt | Hxeq].
  - destruct (Qle_lt_or_eq y z Hyz') as [Hlt | Heq].
    + apply Qlt_le_weak.
      pose proof (Qmult_lt_compat_r y z x Hxlt Hlt) as H.
      rewrite (Qmult_comm y x) in H. rewrite (Qmult_comm z x) in H. exact H.
    + rewrite Heq. apply Qle_refl.
  - rewrite <- Hxeq. rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_l y)).
    rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_l z)).
    apply Qle_refl.
Qed.

Lemma dmeq_mul_ge0 : forall x y : Q,
  QleT' 0%Q x -> QleT' 0%Q y -> QleT' 0%Q (x * y)%Q.
Proof.
  intros x y Hx Hy. destruct x as [x1 x2]. destruct y as [y1 y2].
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hy) as Hy'.
  apply Qle_to_QleT'.
  unfold Qle, Qmult in *. cbn [Qnum Qden Qmult] in *.
  assert (H2 : (0 < Z.pos x2)%Z) by apply sif_posZ.
  assert (H3 : (0 < Z.pos y2)%Z) by apply sif_posZ.
  nia.
Qed.

Lemma dmeq_inv_le_mono : forall u v : Q,
  QltT 0%Q u -> QleT' u v -> QleT' (Qinv v) (Qinv u).
Proof.
  intros u v Hu Huv.
  pose proof (QltT_to_Qlt _ _ Hu) as Hu'.
  pose proof (QleT'_to_Qle _ _ Huv) as Huv'.
  apply Qle_to_QleT'.
  destruct (Qle_lt_or_eq u v Huv') as [Hlt | Heq].
  - assert (Hv : Qlt 0%Q v)
      by (apply (Qlt_le_trans 0%Q u v Hu'); exact (Qlt_le_weak _ _ Hlt)).
    apply Qlt_le_weak. exact (proj1 (Qinv_lt_contravar u v Hu' Hv) Hlt).
  - rewrite Heq. apply Qle_refl.
Qed.

Lemma dmeq_div_split : forall A B : Q,
  ~ (A == 0%Q) -> ~ (B == 0%Q) ->
  QeqT (1%Q / (A * B))%Q ((1%Q / B) * (1%Q / A))%Q.
Proof.
  intros A B HA HB. apply qeq_imp_qeqT.
  assert (HAB : ~ ((A * B) == 0%Q)).
  { intro Hc.
    assert (H1 : ((1%Q / A) * (A * B))%Q == ((1%Q / A) * 0%Q)%Q)
      by (apply sif_mult_comp_r; exact Hc).
    rewrite Qmult_assoc in H1.
    rewrite (Qmult_comm (1%Q / A) A) in H1.
    rewrite (bno_mul_div_self A HA) in H1.
    rewrite Qmult_1_l in H1.
    rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_r (1%Q / A))) in H1.
    exact (HB H1). }
  assert (HY : ((A * B) * ((1%Q / B) * (1%Q / A)))%Q == 1%Q).
  { rewrite <- (Qmult_assoc A B ((1%Q / B) * (1%Q / A))%Q).
    rewrite (Qmult_assoc B (1%Q / B) (1%Q / A)).
    rewrite (bno_mul_div_self B HB).
    rewrite Qmult_1_l.
    rewrite (bno_mul_div_self A HA).
    apply Qeq_refl. }
  assert (HL : ((1%Q / (A * B)) * ((A * B) * ((1%Q / B) * (1%Q / A))))%Q
               == ((1%Q / B) * (1%Q / A))%Q).
  { rewrite Qmult_assoc.
    rewrite (Qmult_comm (1%Q / (A * B)) (A * B)).
    rewrite (bno_mul_div_self (A * B) HAB).
    rewrite Qmult_1_l.
    apply Qeq_refl. }
  assert (HR : ((1%Q / (A * B)) * ((A * B) * ((1%Q / B) * (1%Q / A))))%Q
               == (1%Q / (A * B))%Q).
  { apply (Qeq_trans _ ((1%Q / (A * B)) * 1%Q)%Q).
    - apply sif_mult_comp_r. exact HY.
    - apply Qmult_1_r. }
  apply Qeq_sym.
  apply (Qeq_trans _ ((1%Q / (A * B)) * ((A * B) * ((1%Q / B) * (1%Q / A))))%Q).
  - apply Qeq_sym. exact HL.
  - exact HR.
Qed.

Lemma dmeq_Zfact_pos : forall n : nat, (0 < Z.of_nat (fact n))%Z.
Proof.
  intro n.
  assert (Hf : (1 <= fact n)%nat).
  { destruct n as [| m].
    - cbn [fact]. lia.
    - assert (Hs : (Datatypes.S m <= fact (Datatypes.S m))%nat)
        by (apply lic_fact_ge_self; lia).
      lia. }
  lia.
Qed.

(* zify 无「n=0 ↔ Z.of_nat n=0」链（diag5 案例实证）：变量 n 的
   Z0 支消解专用微件——destruct n 后 cbn 收尾。 *)
Lemma dmeq_Zofnat_eq0 : forall n : nat, Z.of_nat n = 0%Z -> (n = 0)%nat.
Proof.
  intro n. destruct n as [| m].
  - intro H0. reflexivity.
  - intro H. cbn in H. discriminate H.
Qed.

(* Zneg 支消解微件：Zneg p 对 micromega 是无符号信息原子，lia 无 witness
   （实测证实）——Z.of_nat 的像恒非 Zneg，constructor 层 discriminate 收尾。 *)
Lemma dmeq_Zofnat_neqneg : forall (n : nat) (p : positive),
  Z.of_nat n <> Zneg p.
Proof.
  intros n p. destruct n as [| m].
  - intro H. change (Z0 = Zneg p) in H. discriminate H.
  - intro H. change (Z.pos (Pos.of_succ_nat m) = Zneg p) in H. discriminate H.
Qed.

(* ============================================================ *)
(* S1：尾控闭式（几何级数和 + 逐项比较 ⟹ 尾和 < 1/(n·n!)，n ≥ 1）     *)
(* ============================================================ *)

Definition dmeq_rp (n : nat) : Q := 1%Q / ((Z.of_nat (Datatypes.S n) # 1)%Q).

Fixpoint dmeq_gpow (n j : nat) : Q :=
  match j with
  | O => 1%Q
  | Datatypes.S i => dmeq_rp n * dmeq_gpow n i
  end.

Fixpoint dmeq_gsum (n K : nat) : Q :=
  match K with
  | O => 1%Q
  | Datatypes.S k => dmeq_gsum n k + dmeq_gpow n (Datatypes.S k)
  end.

Lemma dmeq_gpow_succ : forall n j : nat,
  QeqT (dmeq_gpow n (Datatypes.S j)) (dmeq_rp n * dmeq_gpow n j)%Q.
Proof. intros n j. apply qeq_imp_qeqT. cbn [dmeq_gpow]. apply Qeq_refl. Qed.

Lemma dmeq_rp_pos : forall n : nat, QltT 0%Q (dmeq_rp n).
Proof.
  intro n. apply Qlt_to_QltT. unfold dmeq_rp.
  pose proof (Qinv_lt_0_compat ((Z.of_nat (Datatypes.S n)) # 1)%Q
                ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia)) as Hi.
  rewrite <- (Qmult_1_l (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q)) in Hi.
  unfold Qdiv. exact Hi.
Qed.

Lemma dmeq_gpow_ge0 : forall n j : nat, QleT' 0%Q (dmeq_gpow n j).
Proof.
  intros n j. induction j as [| j IH].
  - apply Qle_to_QleT'. unfold Qle. cbn [dmeq_gpow Qnum Qden]. lia.
  - cbn [dmeq_gpow]. apply dmeq_mul_ge0.
    + exact (Qle_to_QleT' _ _
                (Qlt_le_weak 0%Q _ (QltT_to_Qlt _ _ (dmeq_rp_pos n)))).
    + exact IH.
Qed.

Lemma dmeq_rp_G' : forall n : nat, (1 <= n)%nat ->
  QeqT (dmeq_rp n * (((Z.of_nat (Datatypes.S n)) # 1)%Q
                * (1%Q / ((Z.of_nat n) # 1)%Q)))%Q
    (1%Q / ((Z.of_nat n) # 1)%Q)%Q.
Proof.
  intros n Hn. apply qeq_imp_qeqT. unfold dmeq_rp.
  assert (HY0 : ~ (((Z.of_nat (Datatypes.S n)) # 1)%Q == 0%Q))
    by (intro Hc; unfold Qeq in Hc; cbn [Qnum Qden Qmult] in Hc; lia).
  rewrite (Qmult_assoc (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q)
                       ((Z.of_nat (Datatypes.S n)) # 1)%Q
                       (1%Q / ((Z.of_nat n) # 1)%Q)).
  rewrite (Qmult_comm (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q)
                      ((Z.of_nat (Datatypes.S n)) # 1)%Q).
  rewrite (bno_mul_div_self ((Z.of_nat (Datatypes.S n)) # 1)%Q HY0).
  rewrite Qmult_1_l.
  apply Qeq_refl.
Qed.

Lemma dmeq_gsum_split : forall n k : nat,
  QeqT (dmeq_gsum n k + dmeq_gpow n (Datatypes.S k))%Q
    (1%Q + dmeq_rp n * dmeq_gsum n k)%Q.
Proof.
  intros n k. apply qeq_imp_qeqT. induction k as [| k IH].
  - cbn [dmeq_gsum dmeq_gpow]. apply Qeq_refl.
  - cbn [dmeq_gsum]. rewrite (qeqT_imp_qeq _ _ (dmeq_gpow_succ n (Datatypes.S k))).
    apply (Qeq_trans _ (((1%Q + dmeq_rp n * dmeq_gsum n k)%Q
                         + dmeq_rp n * dmeq_gpow n (Datatypes.S k))%Q)).
    + apply sif_plus_comp.
      * exact IH.
      * apply Qeq_refl.
    + rewrite Qmult_plus_distr_r.
      unfold Qplus, Qeq. cbn [Qnum Qden Qmult]. first [ring | nia | lia].
Qed.

Lemma dmeq_gsum_lt : forall n K : nat, (1 <= n)%nat ->
  QltT (dmeq_gsum n K)
       (((Z.of_nat (Datatypes.S n)) # 1)%Q * (1%Q / ((Z.of_nat n) # 1)%Q))%Q.
Proof.
  intros n K Hn. destruct n as [| n'].
  - exfalso. lia.
  - apply Qlt_to_QltT.
    assert (Hbase : Qlt 1%Q (((Z.of_nat (Datatypes.S (Datatypes.S n'))) # 1)%Q
                             * (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q))%Q).
    { unfold Qeq, Qlt, Qmult, Qdiv, Qinv.
      destruct (Z.of_nat (Datatypes.S (Datatypes.S n'))) as [| Np | Np] eqn:HN.
      - lia.
      - destruct (Z.of_nat (Datatypes.S n')) as [| Nq | Nq] eqn:HN2.
        + lia.
        + cbn [Qnum Qden Qmult]. nia.
        + exfalso. exact (dmeq_Zofnat_neqneg _ _ HN2).
      - exfalso. exact (dmeq_Zofnat_neqneg _ _ HN). }
    assert (H3 : (1%Q + (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q))%Q
                 == (((Z.of_nat (Datatypes.S (Datatypes.S n'))) # 1)%Q
                     * (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q))%Q).
    { unfold Qeq, Qplus, Qmult, Qdiv, Qinv.
      destruct (Z.of_nat (Datatypes.S (Datatypes.S n'))) as [| Np | Np] eqn:HN.
      - lia.
      - destruct (Z.of_nat (Datatypes.S n')) as [| Nq | Nq] eqn:HN2.
        + lia.
        + cbn [Qnum Qden Qmult]. nia.
        + exfalso. exact (dmeq_Zofnat_neqneg _ _ HN2).
      - exfalso. exact (dmeq_Zofnat_neqneg _ _ HN). }
    induction K as [| k IH].
    + cbn [dmeq_gsum]. exact Hbase.
    + cbn [dmeq_gsum dmeq_gpow]. rewrite (qeqT_imp_qeq _ _ (dmeq_gsum_split _ _)).
      pose proof (QltT_to_Qlt _ _ (dmeq_rp_pos (Datatypes.S n'))) as Hrp.
      assert (H1 : Qlt (dmeq_rp (Datatypes.S n') * dmeq_gsum (Datatypes.S n') k)%Q
                       (dmeq_rp (Datatypes.S n')
                        * (((Z.of_nat (Datatypes.S (Datatypes.S n'))) # 1)%Q
                           * (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q)))%Q).
      { pose proof (Qmult_lt_compat_r _ _ _ Hrp IH) as HH.
        rewrite (Qmult_comm (dmeq_gsum (Datatypes.S n') k)
                            (dmeq_rp (Datatypes.S n'))) in HH.
        rewrite (Qmult_comm (((Z.of_nat (Datatypes.S (Datatypes.S n'))) # 1)%Q
                             * (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q))
                            (dmeq_rp (Datatypes.S n'))) in HH.
        exact HH. }
      pose proof (lic_qlt_add_l 1%Q
                    (dmeq_rp (Datatypes.S n') * dmeq_gsum (Datatypes.S n') k)%Q
                    (dmeq_rp (Datatypes.S n')
                     * ((((Z.of_nat (Datatypes.S (Datatypes.S n')))) # 1)%Q
                        * (1%Q / ((Z.of_nat (Datatypes.S n')) # 1)%Q)))%Q H1) as H2.
      rewrite (qeqT_imp_qeq _ _ (dmeq_rp_G' (Datatypes.S n') ltac:(lia))) in H2.
      rewrite H3 in H2. exact H2.
Qed.

Lemma dmeq_qf_succ : forall m : nat,
  QeqT (q_fact (Datatypes.S m)) ((Z.of_nat (Datatypes.S m) # 1) * q_fact m)%Q.
Proof. intro m. apply qeq_imp_qeqT. cbn [q_fact]. apply Qeq_refl. Qed.

Lemma dmeq_term_le : forall n j : nat, (1 <= n)%nat ->
  QleT' (1%Q / q_fact (n + Datatypes.S j))%Q
        (((1%Q / q_fact (Datatypes.S n)) * dmeq_gpow n j)%Q).
Proof.
  intros n j Hn. apply Qle_to_QleT'. induction j as [| j IH].
  - rewrite Nat.add_1_r. cbn [dmeq_gpow]. rewrite Qmult_1_r. apply Qle_refl.
  - rewrite Nat.add_succ_r.
    rewrite (qeqT_imp_qeq _ _ (dmeq_qf_succ (n + Datatypes.S j))).
    assert (HA' : ~ (((Z.of_nat (Datatypes.S (n + Datatypes.S j)) # 1)%Q) == 0%Q))
      by (intro Hc; unfold Qeq in Hc; cbn [Qnum Qden Qmult] in Hc; lia).
    assert (HB' : ~ ((q_fact (n + Datatypes.S j)) == 0%Q))
      by (intro Hc;
          exact (Qlt_not_eq 0%Q _ (q_fact_pos (n + Datatypes.S j))
                   (Qeq_sym _ _ Hc))).
    rewrite (qeqT_imp_qeq _ _
               (dmeq_div_split ((Z.of_nat (Datatypes.S (n + Datatypes.S j)) # 1)%Q)
                               (q_fact (n + Datatypes.S j)) HA' HB')).
    assert (HposX : Qlt 0%Q (1%Q / q_fact (Datatypes.S n))).
    { pose proof (Qinv_lt_0_compat (q_fact (Datatypes.S n))
                    (q_fact_pos (Datatypes.S n))) as Hi.
      rewrite <- (Qmult_1_l (Qinv (q_fact (Datatypes.S n)))) in Hi.
      unfold Qdiv. exact Hi. }
    assert (Hdelta : Qlt 0%Q (1%Q / ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q)).
    { pose proof (Qinv_lt_0_compat ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q
                    ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia)) as Hi.
      rewrite <- (Qmult_1_l
                    (Qinv ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q)) in Hi.
      unfold Qdiv. exact Hi. }
    assert (Hle2 : Qle (1%Q / ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q)
                       (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q)).
    { unfold Qdiv.
      rewrite (Qmult_1_l (Qinv ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q)).
      rewrite (Qmult_1_l (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q)).
      apply QleT'_to_Qle. apply dmeq_inv_le_mono.
      - apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Qmult]. lia.
      - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult]. lia. }
    assert (Hstep3 : Qle (((1%Q / q_fact (Datatypes.S n)) * dmeq_gpow n j)%Q
                          * (1%Q / ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q))%Q
                         (((1%Q / q_fact (Datatypes.S n)) * dmeq_gpow n j)%Q
                          * (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q))%Q).
    { apply QleT'_to_Qle. apply dmeq_mult_le_compat_l.
      - apply dmeq_mul_ge0.
        + exact (Qle_to_QleT' _ _ (Qlt_le_weak 0%Q _ HposX)).
        + apply dmeq_gpow_ge0.
      - exact (Qle_to_QleT' _ _ Hle2). }
    assert (Hrew : (((1%Q / q_fact (Datatypes.S n)) * dmeq_gpow n j)%Q
                    * (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q))%Q
                   == ((1%Q / q_fact (Datatypes.S n)) * dmeq_gpow n (Datatypes.S j))%Q).
    { unfold dmeq_gpow, dmeq_rp.
      rewrite (Qmult_comm (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q)
                          (dmeq_gpow n j)).
      rewrite (Qmult_assoc (1%Q / q_fact (Datatypes.S n)) (dmeq_gpow n j)
                 (1%Q / ((Z.of_nat (Datatypes.S n)) # 1)%Q)).
      apply Qeq_refl. }
    rewrite <- Hrew.
    exact (Qle_trans _ _ _
             (QleT'_to_Qle _ _
                (dmeq_mult_le_compat_r _ _ _
                   (Qle_to_QleT' _ _ (Qlt_le_weak 0%Q _ Hdelta))
                   (Qle_to_QleT' _ _ IH)))
             Hstep3).
Qed.

Lemma dmeq_rsum_le : forall n K : nat, (1 <= n)%nat ->
  QleT' (lic_rsum n K) (((1%Q / q_fact (Datatypes.S n)) * dmeq_gsum n K)%Q).
Proof.
  intros n K Hn. apply Qle_to_QleT'.
  assert (Hposq : Qlt 0%Q (1%Q / q_fact (Datatypes.S n))).
  { pose proof (Qinv_lt_0_compat (q_fact (Datatypes.S n))
                  (q_fact_pos (Datatypes.S n))) as Hi.
    rewrite <- (Qmult_1_l (Qinv (q_fact (Datatypes.S n)))) in Hi.
    unfold Qdiv. exact Hi. }
  (* 平移不变式：lic_rsum n (S k) ≤ (1/(S n)!)*gsum n k（增量 1/(n+S(S k))! 恰配
     dmeq_term_le n (S k) 的 gpow n (S k) 上界——原冻结归纳按 gpow n k 计数，
     索引错位不可闭合，此为重写点） *)
  assert (Haux : forall k : nat,
           Qle (lic_rsum n (Datatypes.S k))
               (((1%Q / q_fact (Datatypes.S n)) * dmeq_gsum n k)%Q)).
  { intro k. induction k as [| k IH].
    - cbn [lic_rsum dmeq_gsum]. rewrite Nat.add_1_r.
      rewrite Qplus_0_l, Qmult_1_r. apply Qle_refl.
    - assert (Hrec : lic_rsum n (Datatypes.S (Datatypes.S k))
                     == (lic_rsum n (Datatypes.S k)
                         + 1%Q / q_fact (n + Datatypes.S (Datatypes.S k)))%Q)
        by apply Qeq_refl.
      cbn [dmeq_gsum].
      apply (Qle_trans _ (((1%Q / q_fact (Datatypes.S n)) * dmeq_gsum n k
                           + (1%Q / q_fact (Datatypes.S n))
                             * dmeq_gpow n (Datatypes.S k))%Q)).
      + rewrite Hrec. apply Qplus_le_compat.
        * exact IH.
        * exact (QleT'_to_Qle _ _ (dmeq_term_le n (Datatypes.S k) Hn)).
      + apply qeq_le. apply Qeq_sym. cbn [dmeq_gsum]. apply Qmult_plus_distr_r. }
  destruct K as [| k].
  - cbn [lic_rsum]. apply QleT'_to_Qle. apply dmeq_mul_ge0.
    + apply Qle_to_QleT'. apply Qlt_le_weak. exact Hposq.
    + apply Qle_to_QleT'. cbn [dmeq_gsum]. unfold Qle. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1%Q / q_fact (Datatypes.S n)) * dmeq_gsum n k)%Q)).
    + exact (Haux k).
    + apply QleT'_to_Qle. apply dmeq_mult_le_compat_l.
      * apply Qle_to_QleT'. apply Qlt_le_weak. exact Hposq.
      * cbn [dmeq_gsum]. apply dmeq_le_add_r. apply dmeq_gpow_ge0.
Qed.

Lemma dmeq_rsum_mono : forall n K : nat,
  QleT' (lic_rsum n K) (lic_rsum n (Datatypes.S K)).
Proof.
  intros n K. cbn [lic_rsum]. apply dmeq_le_add_r.
  pose proof (Qinv_lt_0_compat (q_fact (n + Datatypes.S K))
                (q_fact_pos (n + Datatypes.S K))) as Hi.
  rewrite <- (Qmult_1_l (Qinv (q_fact (n + Datatypes.S K)))) in Hi.
  unfold Qdiv. apply Qle_to_QleT'. apply Qlt_le_weak. exact Hi.
Qed.

Lemma dmeq_rsum_mono_K : forall n j K : nat, (j <= K)%nat ->
  QleT' (lic_rsum n j) (lic_rsum n K).
Proof.
  intros n j K H. apply Qle_to_QleT'. induction H as [| K Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (lic_rsum n K)); [exact IH | apply QleT'_to_Qle;
      apply dmeq_rsum_mono].
Qed.

Lemma dmeq_rsum_geo : forall n K : nat, (1 <= n)%nat ->
  QltT (lic_rsum n K)
       ((1%Q / ((Z.of_nat n) # 1)%Q) * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q.
Proof.
  intros n K Hn. apply Qlt_to_QltT.
  assert (Hposq : Qlt 0%Q (1%Q / q_fact (Datatypes.S n))).
  { pose proof (Qinv_lt_0_compat (q_fact (Datatypes.S n))
                  (q_fact_pos (Datatypes.S n))) as Hi.
    rewrite <- (Qmult_1_l (Qinv (q_fact (Datatypes.S n)))) in Hi.
    unfold Qdiv. exact Hi. }
  assert (H1 : Qlt (lic_rsum n K)
                   (((1%Q / ((Z.of_nat (fact (Datatypes.S n))) # 1)%Q)
                     * (((Z.of_nat (Datatypes.S n)) # 1)%Q
                        * (1%Q / ((Z.of_nat n) # 1)%Q)))%Q)).
  { pose proof (QleT'_to_Qle _ _ (dmeq_rsum_le n K Hn)) as Hle.
    pose proof (Qmult_lt_compat_r _ _ _ Hposq
                  (QltT_to_Qlt _ _ (dmeq_gsum_lt n K Hn))) as Hlt.
    rewrite (Qmult_comm (dmeq_gsum n K) (1%Q / q_fact (Datatypes.S n))) in Hlt.
    rewrite (Qmult_comm (((Z.of_nat (Datatypes.S n)) # 1)%Q
                         * (1%Q / ((Z.of_nat n) # 1)%Q))
                        (1%Q / q_fact (Datatypes.S n))) in Hlt.
    rewrite (sif_qfact_Z (Datatypes.S n)) in Hle.
    rewrite (sif_qfact_Z (Datatypes.S n)) in Hlt.
    exact (Qle_lt_trans _ _ _ Hle Hlt). }
  assert (HF7p : (0 < Z.of_nat (fact (Datatypes.S n)))%Z) by apply dmeq_Zfact_pos.
  assert (HFp : (0 < Z.of_nat (fact n))%Z) by apply dmeq_Zfact_pos.
  assert (HP : ((1%Q / ((Z.of_nat (fact (Datatypes.S n))) # 1)%Q)
                * (((Z.of_nat (Datatypes.S n)) # 1)%Q
                   * (1%Q / ((Z.of_nat n) # 1)%Q)))%Q
               == ((1%Q / ((Z.of_nat n) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q).
  { unfold Qeq, Qmult, Qdiv, Qinv.
    destruct (Z.of_nat (fact (Datatypes.S n))) as [| Fp | Fp] eqn:HF7.
    - lia.
    - destruct (Z.of_nat n) as [| Np | Np] eqn:HN.
      + pose proof (dmeq_Zofnat_eq0 _ HN). lia.
      + destruct (Z.of_nat (fact n)) as [| Gp | Gp] eqn:HFa.
        * lia.
        * assert (HF7' : Zpos Fp = (Z.of_nat (Datatypes.S n) * Z.of_nat (fact n))%Z)
            by (rewrite <- HF7; cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
          cbn [Qnum Qden Qmult]. nia.
        * exfalso. exact (dmeq_Zofnat_neqneg _ _ HFa).
      + exfalso. exact (dmeq_Zofnat_neqneg _ _ HN).
    - exfalso. exact (dmeq_Zofnat_neqneg _ _ HF7). }
  rewrite HP in H1. exact H1.
Qed.

Lemma dmeq_tail_lt : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  QltT ((exp_series k 1%Q - exp_series n 1%Q)%Q)
       ((1%Q / ((Z.of_nat n) # 1)%Q) * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q.
Proof.
  intros n k Hn Hnk. apply Qlt_to_QltT. remember (k - n)%nat as K eqn:HK.
  assert (Hk : k = (n + K)%nat) by (rewrite HK; lia).
  rewrite Hk. rewrite lic_exp_diff. apply QltT_to_Qlt.
  apply dmeq_rsum_geo. exact Hn.
Qed.

(* ============================================================ *)
(* S2：量化隙（q ≠ 部分和 ⟹ 1/(b·n!) ≤ |q − s(n)|）                   *)
(* ============================================================ *)

Lemma dmeq_gap : forall q : Q, forall n : nat,
  ~ ((q == exp_series n 1)%Q) ->
  QleT' ((1%Q / ((Z.pos (Qden q)) # 1)%Q) * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q
        (Qabs ((q - exp_series n 1)%Q)).
Proof.
  intros q n Hne. apply Qle_to_QleT'.
  pose proof (sif_frac_prod q n) as HF.
  pose proof (sif_abs_frac q n) as HA.
  pose proof (q_fact_pos n) as Hqp.
  assert (Hqf0 : ~ (q_fact n == 0%Q)).
  { intro Hc. exact (Qlt_not_eq 0%Q _ Hqp (Qeq_sym _ _ Hc)). }
  assert (Hd0 : sif_d q n <> 0%Z).
  { intro Hd.
    assert (Hz : ((sif_d q n) # (Qden q))%Q == 0%Q)
      by (rewrite Hd; unfold Qeq; cbn [Qnum Qden Qmult]; lia).
    rewrite Hz in HF.
    assert (H1 : ((1%Q / q_fact n) * (q_fact n * (q - exp_series n 1)%Q))%Q
                 == ((1%Q / q_fact n) * 0%Q)%Q)
      by (apply sif_mult_comp_r; exact HF).
    rewrite Qmult_assoc in H1.
    rewrite (Qmult_comm (1%Q / q_fact n) (q_fact n)) in H1.
    rewrite (bno_mul_div_self (q_fact n) Hqf0) in H1.
    rewrite Qmult_1_l in H1.
    rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_r (1%Q / q_fact n))) in H1.
    assert (H2 : q == ((q - exp_series n 1) + exp_series n 1)%Q)
      by (apply qeqT_imp_qeq; apply dmeq_minus_plus_cancel).
    rewrite H1 in H2. rewrite Qplus_0_l in H2.
    exact (Hne H2). }
  assert (Habs1 : (1 <= Z.abs (sif_d q n))%Z).
  { destruct (sif_d q n) as [| zz | zz]; cbn [Z.abs].
    - lia.
    - assert (0 < Z.pos zz)%Z by apply sif_posZ. lia.
    - assert (0 < Z.pos zz)%Z by apply sif_posZ. lia. }
  assert (HC : Qabs (q_fact n) == q_fact n).
  { apply Qabs_pos. exact (Qlt_le_weak 0%Q _ Hqp). }
  rewrite (Qabs_Qmult (q_fact n) ((q - exp_series n 1)%Q)) in HA.
  rewrite HC in HA.
  assert (H2 : ((1%Q / q_fact n) * (q_fact n * Qabs ((q - exp_series n 1)%Q)))%Q
               == ((1%Q / q_fact n) * ((Z.abs (sif_d q n)) # (Qden q))%Q)%Q)
    by (apply sif_mult_comp_r; exact HA).
  rewrite Qmult_assoc in H2.
  rewrite (Qmult_comm (1%Q / q_fact n) (q_fact n)) in H2.
  rewrite (bno_mul_div_self (q_fact n) Hqf0) in H2.
  rewrite Qmult_1_l in H2.
  rewrite (sif_qfact_Z n) in H2.
  assert (HF0 : (0 < Z.of_nat (fact n))%Z) by apply dmeq_Zfact_pos.
  assert (Hb0 : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
  assert (H3 : ((1%Q / ((Z.of_nat (fact n)) # 1)%Q)
                * ((Z.abs (sif_d q n)) # (Qden q))%Q)%Q
               == (((Z.abs (sif_d q n)) # (Qden q))%Q
                   * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q).
  { symmetry. apply Qmult_comm. }
  rewrite H3 in H2.
  rewrite H2.
  destruct (Z.of_nat (fact n)) as [| Fq | Fq] eqn:HFq.
  - lia.
  - unfold Qle, Qdiv, Qinv. cbn [Qnum Qden Qmult]. nia.
  - exfalso. exact (dmeq_Zofnat_neqneg _ _ HFq).
Qed.

(* ============================================================ *)
(* S3：主件——CaseA/CaseB 分支与统一闭式 c := 1/(4·b·(b+7)!)           *)
(* ============================================================ *)

(* q 形统一闭式常元非负性（caseA/caseB 冻结语句面派生用） *)
Lemma dmeq_constq_pos : forall (q : Q) (n0 : nat),
  QleT' 0%Q ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
           * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q.
Proof.
  intros q n0.
  assert (Hb : Qlt 0%Q (1%Q / ((Z.pos (Qden q)) # 1)%Q)).
  { pose proof (Qinv_lt_0_compat ((Z.pos (Qden q)) # 1)%Q
                  ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia)) as Hi.
    rewrite <- (Qmult_1_l (Qinv ((Z.pos (Qden q)) # 1)%Q)) in Hi.
    unfold Qdiv. exact Hi. }
  assert (HF : Qlt 0%Q (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)).
  { pose proof (Qinv_lt_0_compat ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q
                  ltac:(pose proof (dmeq_Zfact_pos (Datatypes.S n0));
                        unfold Qlt; cbn [Qnum Qden Qmult]; lia)) as Hi.
    rewrite <- (Qmult_1_l (Qinv ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)) in Hi.
    unfold Qdiv. exact Hi. }
  apply dmeq_mul_ge0.
  - apply dmeq_mul_ge0.
    + apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qle_to_QleT'. apply Qlt_le_weak. exact Hb.
  - apply Qle_to_QleT'. apply Qlt_le_weak. exact HF.
Qed.

(* CaseA margin 形（real_lt 逐点义务 eps < d − eps 所需的 2 倍余量版）：
   隙−尾 ≥ c 且 c ≥ 0 ⟹ c + c ≤ 隙−尾 < |q − s(k)| ⟹ c < |q − s(k)| − c。 *)
Lemma dmeq_qcore_caseA2 : forall q : Q, forall n0 k : nat,
  (1 <= n0)%nat -> (Datatypes.S n0 <= k)%nat ->
  (1 <= Z.of_nat n0 - Z.pos (Qden q))%Z ->
  ~ ((q == exp_series n0 1)%Q) ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
       ((Qabs ((q - exp_series k 1)%Q)
         - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
Proof.
  intros q n0 k Hn01 HkN Hratio Hne.
  assert (Hb0 : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
  assert (HF0 : (0 < Z.of_nat (fact n0))%Z) by apply dmeq_Zfact_pos.
  assert (HF7p : (0 < Z.of_nat (fact (Datatypes.S n0)))%Z) by apply dmeq_Zfact_pos.
  pose proof (dmeq_gap q n0 Hne) as Hgap.
  assert (Hle : (n0 <= k)%nat) by lia.
  pose proof (QltT_to_Qlt _ _ (dmeq_tail_lt n0 k Hn01 Hle)) as Htail0.
  remember (k - n0)%nat as K eqn:HK.
  assert (Hk2 : k = (n0 + K)%nat) by (rewrite HK; lia).
  assert (Hid : (exp_series k 1%Q - exp_series n0 1%Q)%Q == lic_rsum n0 K).
  { rewrite Hk2. rewrite lic_exp_diff. apply Qeq_refl. }
  assert (Hge0 : Qle 0%Q ((exp_series k 1%Q - exp_series n0 1%Q)%Q)).
  { apply (Qle_trans _ (lic_rsum n0 K)).
    - exact (lic_rsum_ge0 n0 K).
    - apply qeq_le. apply Qeq_sym. exact Hid. }
  assert (HabsE : Qabs ((exp_series k 1%Q - exp_series n0 1%Q)%Q)
                  == (exp_series k 1%Q - exp_series n0 1%Q)%Q)
    by (apply Qabs_pos; exact Hge0).
  rewrite <- HabsE in Htail0.
  pose proof (lic_qlt_tri_decomp q (exp_series n0 1%Q) (exp_series k 1%Q)) as Htri0.
  assert (Htri : Qle (Qabs ((q - exp_series n0 1%Q)%Q))
                     ((Qabs ((q - exp_series k 1%Q)%Q)
                       + Qabs ((exp_series k 1%Q - exp_series n0 1%Q)%Q))%Q)).
  { apply (Qle_trans _ (Qabs (((q - exp_series k 1%Q)
                               + (exp_series k 1%Q - exp_series n0 1%Q))%Q))).
    - apply qeq_le. setoid_rewrite Htri0. apply Qeq_refl.
    - exact (Qabs_triangle ((q - exp_series k 1%Q)%Q)
                            ((exp_series k 1%Q - exp_series n0 1%Q)%Q)). }
  assert (H4 : Qlt (((1%Q / ((Z.pos (Qden q)) # 1)%Q)
                     * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q
                    - ((1%Q / ((Z.of_nat n0) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q)%Q
                   (Qabs ((q - exp_series k 1)%Q))).
  { exact (Qlt_le_trans _ _ _
             (QltT_to_Qlt _ _
                (dmeq_sub_lt_mono_r _ _ _ (Qlt_to_QltT _ _ Htail0)))
             (Qle_trans _ _ _
                (QleT'_to_Qle _ _
                   (dmeq_le_mono_sub_r _ _
                      (Qabs ((exp_series k 1%Q - exp_series n0 1%Q)%Q)) Hgap))
                (QleT'_to_Qle _ _
                   (dmeq_le_sub_reg _ _ _ (Qle_to_QleT' _ _ Htri))))). }
  assert (H6 : (((1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q
                - ((1%Q / ((Z.of_nat n0) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q)%Q
               == ((((Z.of_nat n0 - Z.pos (Qden q)) # 1)%Q
                    * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                    * (1%Q / ((Z.of_nat n0) # 1)%Q)
                    * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q)).
  { unfold Qminus, Qplus, Qopp, Qeq, Qmult, Qdiv, Qinv.
    destruct (Z.of_nat n0) as [| Nn | Nn] eqn:HNn.
    - pose proof (dmeq_Zofnat_eq0 _ HNn). lia.
    - destruct (Z.of_nat (fact n0)) as [| Gq | Gq] eqn:HFq.
      + lia.
      + cbn [Qnum Qden Qmult]. nia.
      + exfalso. exact (dmeq_Zofnat_neqneg _ _ HFq).
    - exfalso. exact (dmeq_Zofnat_neqneg _ _ HNn). }
  rewrite H6 in H4.
  assert (H5x : Qle ((2 # 1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q
                    ((((Z.of_nat n0 - Z.pos (Qden q)) # 1)%Q
                      * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                      * (1%Q / ((Z.of_nat n0) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact n0)) # 1)%Q))%Q)).
  { assert (HF7 : Z.of_nat (fact (Datatypes.S n0))
                  = (Z.of_nat (Datatypes.S n0) * Z.of_nat (fact n0))%Z)
      by (cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
    assert (Hkey : (Z.of_nat n0
                    <= (Z.of_nat n0 - Z.pos (Qden q)) * 4
                       * Z.of_nat (Datatypes.S n0))%Z) by nia.
    destruct (Z.of_nat n0) as [| Nn | Nn] eqn:HNn.
    - pose proof (dmeq_Zofnat_eq0 _ HNn). lia.
    - destruct (Z.of_nat (fact n0)) as [| Gq | Gq] eqn:HFq.
      + lia.
      + destruct (Z.of_nat (fact (Datatypes.S n0))) as [| F7 | F7] eqn:HF7d.
        * lia.
        * unfold Qle, Qdiv, Qinv. cbn [Qnum Qden Qmult]. nia.
        * exfalso. exact (dmeq_Zofnat_neqneg _ _ HF7d).
      + exfalso. exact (dmeq_Zofnat_neqneg _ _ HFq).
    - exfalso. exact (dmeq_Zofnat_neqneg _ _ HNn). }
  assert (Hcc : (((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                 + ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
                == ((2 # 1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q).
  { unfold Qeq, Qplus, Qmult. cbn [Qnum Qden Qmult]. nia. }
  pose proof (Qle_lt_trans _ _ _ H5x H4) as Hltc.
  rewrite <- Hcc in Hltc.
  assert (Hfin : Qlt ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                     ((Qabs ((q - exp_series k 1)%Q)
                       - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                          * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)).
  { apply (lic_qlt_add_r_cancel_r
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
             ((Qabs ((q - exp_series k 1)%Q)
               - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    rewrite (lic_qlt_minus_add_r (Qabs ((q - exp_series k 1)%Q))
               ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    exact Hltc. }
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* 冻结语句面（任务指令 §三）：c < |q − s(k)|，由 margin 形派生。 *)
Lemma dmeq_qcore_caseA : forall q : Q, forall n0 k : nat,
  (1 <= n0)%nat -> (Datatypes.S n0 <= k)%nat ->
  (1 <= Z.of_nat n0 - Z.pos (Qden q))%Z ->
  ~ ((q == exp_series n0 1)%Q) ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
       (Qabs ((q - exp_series k 1)%Q)).
Proof.
  intros q n0 k Hn01 HkN Hratio Hne.
  pose proof (dmeq_qcore_caseA2 q n0 k Hn01 HkN Hratio Hne) as H2c.
  pose proof (QltT_to_Qlt _ _ H2c) as Hlt0.
  pose proof (lic_qlt_add_l
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((Qabs ((q - exp_series k 1)%Q)
                  - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                     * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)
                Hlt0) as Hlt1.
  rewrite (Qplus_comm ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                       * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                      ((Qabs ((q - exp_series k 1)%Q)
                        - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                           * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)) in Hlt1.
  rewrite (lic_qlt_minus_add_r (Qabs ((q - exp_series k 1)%Q))
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q) in Hlt1.
  pose proof (dmeq_le_add_r
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                (dmeq_constq_pos q n0)) as Hle.
  apply Qlt_to_QltT. exact (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ Hle) Hlt1).
Qed.

(* CaseB margin 形：2c < 1/(n0+1)! ≤ e_k − q（⟸ 2 < 4b 恒真）⟹ c < |e_k − q| − c。 *)
Lemma dmeq_qcore_caseB2 : forall q : Q, forall n0 k : nat,
  (1 <= n0)%nat -> (Datatypes.S n0 <= k)%nat ->
  (q == exp_series n0 1)%Q ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
       ((Qabs ((q - exp_series k 1)%Q)
         - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
Proof.
  intros q n0 k Hn01 HkN Heq.
  remember (k - n0)%nat as K eqn:HK.
  assert (Hk2 : k = (n0 + K)%nat) by (rewrite HK; lia).
  assert (HK1 : (1 <= K)%nat) by lia.
  assert (HE : (exp_series k 1%Q - q)%Q == lic_rsum n0 K).
  { rewrite Hk2. rewrite Heq. rewrite lic_exp_diff. apply Qeq_refl. }
  assert (Hge0 : Qle 0%Q (exp_series k 1%Q - q)%Q)
    by (rewrite HE; apply lic_rsum_ge0).
  assert (Habs : Qabs ((exp_series k 1%Q - q)%Q)
                 == (exp_series k 1%Q - q)%Q)
    by (apply Qabs_pos; exact Hge0).
  assert (Hmono : Qle (lic_rsum n0 1%nat) (lic_rsum n0 K))
    by (apply QleT'_to_Qle; apply (dmeq_rsum_mono_K n0 1 K); exact HK1).
  assert (H1 : lic_rsum n0 1%nat == (1%Q / q_fact (Datatypes.S n0))%Q).
  { cbn [lic_rsum]. rewrite Nat.add_1_r. rewrite Qplus_0_l. apply Qeq_refl. }
  assert (Hchain : Qle (1%Q / q_fact (Datatypes.S n0))
                       (exp_series k 1%Q - q)%Q).
  { rewrite HE. rewrite <- H1. exact Hmono. }
  assert (Hc2 : Qlt ((2 # 1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q
                   (1%Q / q_fact (Datatypes.S n0))).
  { rewrite (sif_qfact_Z (Datatypes.S n0)).
    assert (HF7 : (0 < Z.of_nat (fact (Datatypes.S n0)))%Z)
      by apply dmeq_Zfact_pos.
    assert (Hb0 : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
    unfold Qlt, Qdiv, Qinv.
    destruct (Z.of_nat (fact (Datatypes.S n0))) as [| Fp | Fp] eqn:HF7c.
    + lia.
    + cbn [Qnum Qden Qmult]. nia.
    + exfalso. exact (dmeq_Zofnat_neqneg _ _ HF7c). }
  assert (Hcc : (((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                 + ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
                == ((2 # 1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q).
  { unfold Qeq, Qplus, Qmult. cbn [Qnum Qden Qmult]. nia. }
  pose proof (Qlt_le_trans _ _ _ Hc2 Hchain) as Hltc.
  rewrite <- Hcc in Hltc.
  assert (Hfin : Qlt ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                     ((exp_series k 1%Q - q)%Q
                      - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                         * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
  { apply (lic_qlt_add_r_cancel_r
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
             ((exp_series k 1%Q - q)%Q
              - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    rewrite (lic_qlt_minus_add_r (exp_series k 1%Q - q)%Q
               ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    exact Hltc. }
  assert (Hbr : ((exp_series k 1%Q - q)%Q
                 - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                    * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
                == ((Qabs ((q - exp_series k 1)%Q))
                    - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                       * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
  { assert (Habs2 : Qabs ((q - exp_series k 1)%Q)
                    == Qabs ((exp_series k 1%Q - q)%Q)).
    { rewrite (Qabs_Qminus q (exp_series k 1%Q)). apply Qeq_refl. }
    apply (sif_plus_comp
             ((exp_series k 1%Q - q)%Q)
             (- ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q
             ((Qabs ((q - exp_series k 1)%Q)))
             (- ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q).
    - apply (Qeq_trans _ (Qabs ((exp_series k 1%Q - q)%Q))).
      + apply Qeq_sym. exact Habs.
      + apply Qeq_sym. exact Habs2.
    - apply Qeq_refl. }
  apply (lic_qltt_comp_r
            ((exp_series k 1%Q - q)%Q
             - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
            ((Qabs ((q - exp_series k 1)%Q))
             - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
            ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
             * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
  - exact Hbr.
  - apply Qlt_to_QltT. exact Hfin.
Qed.

(* 冻结语句面（任务指令 §三）：c < |q − s(k)|，由 margin 形派生。 *)
Lemma dmeq_qcore_caseB : forall q : Q, forall n0 k : nat,
  (1 <= n0)%nat -> (Datatypes.S n0 <= k)%nat ->
  (q == exp_series n0 1)%Q ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
       (Qabs ((q - exp_series k 1)%Q)).
Proof.
  intros q n0 k Hn01 HkN Heq.
  pose proof (dmeq_qcore_caseB2 q n0 k Hn01 HkN Heq) as H2c.
  pose proof (QltT_to_Qlt _ _ H2c) as Hlt0.
  pose proof (lic_qlt_add_l
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((Qabs ((q - exp_series k 1)%Q)
                  - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                     * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)
                Hlt0) as Hlt1.
  rewrite (Qplus_comm ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                       * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                      ((Qabs ((q - exp_series k 1)%Q)
                        - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                           * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q)) in Hlt1.
  rewrite (lic_qlt_minus_add_r (Qabs ((q - exp_series k 1)%Q))
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q) in Hlt1.
  pose proof (dmeq_le_add_r
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                (dmeq_constq_pos q n0)) as Hle.
  apply Qlt_to_QltT. exact (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ Hle) Hlt1).
Qed.

Lemma dmeq_const_pos : forall (a : Z) (bb : positive),
  QltT 0%Q ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
Proof.
  intros a bb.
  assert (HF : (0 < Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7)))%Z)
    by apply dmeq_Zfact_pos.
  destruct (Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) as [| Fp | Fp] eqn:HFc.
  - lia.
  - apply Qlt_to_QltT. unfold Qlt, Qdiv, Qinv. cbn [Qnum Qden Qmult]. nia.
  - exfalso. exact (dmeq_Zofnat_neqneg _ _ HFc).
Qed.

Theorem dmeq_e_qcore2 : forall (a : Z) (bb : positive) (k : nat),
  ((Z.to_nat (Z.pos bb) + 7)%nat <= k)%nat ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
       ((Qabs (((a # bb)%Q - exp_series k 1)%Q)
         - ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)%Q).
Proof.
  intros a bb k Hk7.
  assert (Hratio : (1 <= Z.of_nat (Z.to_nat (Z.pos bb) + 6) - Z.pos bb)%Z).
  { rewrite Nat2Z.inj_add. rewrite (Z2Nat.id (Z.pos bb) (Z.lt_le_incl 0%Z (Z.pos bb) (sif_posZ bb))). lia. }
  assert (Hn01 : (1 <= (Z.to_nat (Z.pos bb) + 6))%nat) by lia.
  assert (HkN : (Datatypes.S (Z.to_nat (Z.pos bb) + 6) <= k)%nat) by lia.
  assert (H7 : (Z.to_nat (Z.pos bb) + 7)%nat
               = Datatypes.S (Z.to_nat (Z.pos bb) + 6))
    by (rewrite Nat.add_succ_r; reflexivity).
  rewrite H7.
  destruct (Q_dec ((a # bb)%Q)
                  (exp_series (Z.to_nat (Z.pos bb) + 6) 1%Q))
    as [Hlt | Hrest].
  - destruct Hlt as [Hlt1 | Hlt2].
    + exact (dmeq_qcore_caseA2 ((a # bb)%Q) (Z.to_nat (Z.pos bb) + 6) k
               Hn01 HkN Hratio (Qlt_not_eq _ _ Hlt1)).
    + exact (dmeq_qcore_caseA2 ((a # bb)%Q) (Z.to_nat (Z.pos bb) + 6) k
               Hn01 HkN Hratio (not_eq_sym (Qlt_not_eq _ _ Hlt2))).
  - exact (dmeq_qcore_caseB2 ((a # bb)%Q) (Z.to_nat (Z.pos bb) + 6) k
             Hn01 HkN Hrest).
Qed.

(* 冻结语句面（任务指令 §三）：c < |q − s(k)|，由 margin 形派生。 *)
Theorem dmeq_e_qcore : forall (a : Z) (bb : positive) (k : nat),
  ((Z.to_nat (Z.pos bb) + 7)%nat <= k)%nat ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
       (Qabs (((a # bb)%Q - exp_series k 1)%Q)).
Proof.
  intros a bb k Hk7.
  pose proof (dmeq_e_qcore2 a bb k Hk7) as H2c.
  pose proof (QltT_to_Qlt _ _ H2c) as Hlt0.
  pose proof (lic_qlt_add_l
                ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
                ((Qabs (((a # bb)%Q - exp_series k 1)%Q)
                  - ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                     * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)%Q)
                Hlt0) as Hlt1.
  rewrite (Qplus_comm ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                       * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
                      ((Qabs (((a # bb)%Q - exp_series k 1)%Q)
                        - ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                           * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)%Q)) in Hlt1.
  rewrite (lic_qlt_minus_add_r (Qabs (((a # bb)%Q - exp_series k 1)%Q))
             ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q) in Hlt1.
  pose proof (dmeq_le_add_r
                ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
                ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
                (Qle_to_QleT' _ _
                   (Qlt_le_weak 0%Q _ (QltT_to_Qlt _ _ (dmeq_const_pos a bb))))) as Hle.
  apply Qlt_to_QltT. exact (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ Hle) Hlt1).
Qed.

Theorem u5c_e_closed_measure : forall (a : Z) (bb : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u)
                                 (fun n => exp_series n 1)
                                 (lic_seq_cauchy (fun n => exp_series n 1)
                                                 (fun n => 1%Q / q_fact n)
                                                 lic_tail_e lic_vanish_e))
               (real_const ((a # bb)%Q)))))).
Proof.
  intros a bb.
  exists ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
          * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
  split.
  - exact (dmeq_const_pos a bb).
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + unfold real_lt.
      exists ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
      split.
      * exact (dmeq_const_pos a bb).
      * exists (Z.to_nat (Z.pos bb) + 7)%nat.
        intros k HkN. apply NatLe_drop in HkN.
        assert (HPr : projT1 (real_metric (existT (fun u : Qseq => cauchy u)
                                    (fun n => exp_series n 1)
                                    (lic_seq_cauchy (fun n => exp_series n 1)
                                                    (fun n => 1%Q / q_fact n)
                                                    lic_tail_e lic_vanish_e))
                             (real_const ((a # bb)%Q))) k
                    == Qabs ((exp_series k 1%Q - (a # bb)%Q)%Q))
          by apply lic_metric_proj.
        apply (lic_qltt_comp_r
                  ((Qabs (((a # bb)%Q - exp_series k 1)%Q))
                   - ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)%Q
                  (projT1 (real_metric (existT (fun u : Qseq => cauchy u)
                                          (fun n => exp_series n 1)
                                          (lic_seq_cauchy (fun n => exp_series n 1)
                                                          (fun n => 1%Q / q_fact n)
                                                          lic_tail_e lic_vanish_e))
                           (real_const ((a # bb)%Q))) k
                   - projT1 (real_const ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                                         * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q) k)
                  ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q).
        -- rewrite real_const_proj. rewrite HPr.
           rewrite (Qabs_Qminus ((a # bb)%Q) (exp_series k 1%Q)). reflexivity.
        -- apply dmeq_e_qcore2. exact HkN.
Qed.

(* ============================================================ *)
(* S4：提取检验 + 假设面自审                                          *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction dmeq_e_qcore u5c_e_closed_measure dmeq_qcore_caseA
  dmeq_qcore_caseB dmeq_qcore_caseA2 dmeq_qcore_caseB2 dmeq_e_qcore2
  dmeq_gap dmeq_tail_lt dmeq_rsum_geo dmeq_rsum_le
  dmeq_term_le dmeq_gsum_lt dmeq_rsum_mono dmeq_rsum_mono_K dmeq_le_add_r
  dmeq_mult_le_compat_r dmeq_mult_le_compat_l dmeq_inv_le_mono
  dmeq_le_mono_sub_r dmeq_le_sub_reg dmeq_sub_lt_mono_r dmeq_lt_add_r
  dmeq_0_lt_sub dmeq_plus_minus_r dmeq_sub_split dmeq_minus_plus_cancel
  dmeq_div_split dmeq_mul_ge0 dmeq_gpow_ge0 dmeq_Zfact_pos dmeq_const_pos
  dmeq_constq_pos dmeq_Zofnat_eq0
  dmeq_qf_succ dmeq_rp dmeq_gpow dmeq_gsum dmeq_gpow_succ dmeq_gsum_split
  dmeq_rp_pos dmeq_mult_0_r.

Print Assumptions dmeq_e_qcore.
Print Assumptions dmeq_e_qcore2.
Print Assumptions u5c_e_closed_measure.
Print Assumptions dmeq_gap.
Print Assumptions dmeq_tail_lt.
