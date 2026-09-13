(* ============================================================ *)
(* UpReqNormConv.v —— 席BNC：路径 B 范数卷积收敛引擎（20260912） *)
(* ============================================================ *)
(* 评审003 路径 B S3（交换函数方程）收敛侧引擎：                  *)
(*   Mertens 型引理 —— 若 Σa 与 Σb 的范数尾界受控                *)
(*   （一切前缀部分和 Σ‖a‖≤Ba / Σ‖b‖≤Bb），则两级数项式积的      *)
(*   卷积块范差有显式界：                                        *)
(*     ‖C(m2,n2) − C(m1,n1)‖ ≤ Ba·(b 尾 n1..n2) + Bb·(a 尾 m1..m2) *)
(*   （C(m,n) = Σ_{k<m} Σ_{j<n} a_k·b_j 矩形部分和）。           *)
(* 分层交付：                                                    *)
(*   S1 = ncv_qsum/ncv_qtail/ncv_sum/ncv_row/ncv_conv 定义面；    *)
(*   S2 = ncv_norm_sum_le 范数三角引擎（次可加字段归纳）；        *)
(*   S3 = ncv_mertens 主件（QleT 面，显式界）；                   *)
(*   S4 = ncv_conv_rect_cauchy + ncv_conv_diag_cauchy（柯西组装）。*)
(* 总装挂账：与 exp_add 的代数恒等面（BanachProd 卷积极性）归     *)
(* B3Sv2 线，本席只做收敛面，两件文件互不相碰。                  *)
(*                                                               *)
(* 红线自审：语句面全 Set 层——QleT'/QltT/sigT/NatLe（S02 桥件    *)
(* 同款）；证内 Prop 层 Qle/Qlt 仅作引擎内衬。                   *)
(* 工程注（承 PB/PBR 卡）：Rocq 9 类投影实例参为隐式，类字段/     *)
(* 字段引理一律 @显式喂实例；自定 Fixpoint/Lemma 常规显式参。     *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1：定义面 —— Q 值有限和/尾和 + BA 值行和/卷积矩形部分和       *)
(* ============================================================ *)

(* Q 值有限和 Σ_{k<n} f k *)
Fixpoint ncv_qsum (f : nat -> Q) (n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S m => (ncv_qsum f m + f m)%Q
  end.

(* Q 值尾和 Σ_{m≤k<n} f k（leb 守卫形，n<m 空和=0 防 nat 减法截断；
   与 S03 exp_tail_abs 同族守卫配方） *)
Fixpoint ncv_qtail (f : nat -> Q) (m n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S n' => (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q
  end.

(* BA 值有限和 Σ_{k<n} x k *)
Fixpoint ncv_sum (B : BanachAlg) (x : nat -> (@BA B)) (n : nat) : (@BA B) :=
  match n with
  | 0%nat => @bzero B
  | Datatypes.S m => @bplus B (ncv_sum B x m) (x m)
  end.

(* 卷积行：Σ_{j<n} a_k·b_j *)
Definition ncv_row (B : BanachAlg) (a b : nat -> (@BA B)) (k n : nat) : (@BA B) :=
  ncv_sum B (fun j => @bmult B (a k) (b j)) n.

(* 卷积矩形部分和：C(m,n) = Σ_{k<m} Σ_{j<n} (a k)·(b j) *)
Fixpoint ncv_conv (B : BanachAlg) (a b : nat -> (@BA B)) (m n : nat) : (@BA B) :=
  match m with
  | 0%nat => @bzero B
  | Datatypes.S m' => @bplus B (ncv_conv B a b m' n) (ncv_row B a b m' n)
  end.

(* ============================================================ *)
(* S2a：Q 侧有限和引擎（nonneg/逐点保序/标量提出/尾和三件）       *)
(* ============================================================ *)

Lemma ncv_qsum_nonneg : forall (f : nat -> Q) (n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' 0 (ncv_qsum f n).
Proof.
  intros f n Hf. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + 0)%Q).
    + apply qeq_imp_qle. ring.
    + apply (Qplus_le_compat 0 (ncv_qsum f m) 0 (f m)).
      * apply QleT'_to_Qle. exact IH.
      * apply QleT'_to_Qle. exact (Hf m).
Qed.

Lemma ncv_qsum_le : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, QleT' (f k) (g k)) -> QleT' (ncv_qsum f n) (ncv_qsum g n).
Proof.
  intros f g n Hle. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. change (ncv_qsum g 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    change (ncv_qsum g (Datatypes.S m)) with (ncv_qsum g m + g m)%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + exact IH.
    + exact (Hle m).
Qed.

Lemma ncv_qsum_scalar_l : forall (c : Q) (f : nat -> Q) (n : nat),
  ncv_qsum (fun k => (c * f k)%Q) n == (c * ncv_qsum f n)%Q.
Proof.
  intros c f n. induction n as [| m IH].
  - change (ncv_qsum (fun k => (c * f k)%Q) 0%nat) with 0%Q.
    change (ncv_qsum f 0%nat) with 0%Q.
    ring.
  - change (ncv_qsum (fun k => (c * f k)%Q) (Datatypes.S m))
      with (ncv_qsum (fun k => (c * f k)%Q) m + (c * f m)%Q)%Q.
    change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    rewrite IH. ring.
Qed.

Lemma ncv_qtail_nonneg : forall (f : nat -> Q) (m n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' 0 (ncv_qtail f m n).
Proof.
  intros f m n Hf. induction n as [| n' IH].
  - change (ncv_qtail f m 0%nat) with 0%Q. apply qleT'_refl.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + 0)%Q).
    + apply qeq_imp_qle. ring.
    + apply (Qplus_le_compat 0 (ncv_qtail f m n') 0 (if Nat.leb m n' then f n' else 0%Q)).
      * apply QleT'_to_Qle. exact IH.
      * apply QleT'_to_Qle. destruct (Nat.leb m n').
        -- exact (Hf n').
        -- apply qleT'_refl.
Qed.

Lemma ncv_qtail_le_m : forall (f : nat -> Q) (m n : nat),
  (n <= m)%nat -> ncv_qtail f m n == 0%Q.
Proof.
  intros f m n Hn. induction n as [| n' IH].
  - reflexivity.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    assert (Hle : Nat.leb m n' = false).
    { apply (proj2 (Nat.leb_gt m n')). lia. }
    assert (Hn'le : (n' <= m)%nat) by lia.
    rewrite Hle. rewrite (IH Hn'le). ring.
Qed.

(* 尾和 ≤ 同端点前缀和（逐点非负；S4 用） *)
Lemma ncv_qtail_le_qsum : forall (f : nat -> Q) (m n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' (ncv_qtail f m n) (ncv_qsum f n).
Proof.
  intros f m n Hf. induction n as [| n' IH].
  - change (ncv_qtail f m 0%nat) with 0%Q.
    change (ncv_qsum f 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    change (ncv_qsum f (Datatypes.S n')) with (ncv_qsum f n' + f n')%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + exact IH.
    + destruct (Nat.leb m n').
      * apply qleT'_refl.
      * exact (Hf n').
Qed.

(* ============================================================ *)
(* S2b：范数三角引擎 —— ‖Σ x k‖ ≤ Σ ‖x k‖（次可加字段归纳）       *)
(* ============================================================ *)

Lemma ncv_norm_sum_le : forall (B : BanachAlg) (x : nat -> (@BA B)) (n : nat),
  QleT' (@bnorm B (ncv_sum B x n)) (ncv_qsum (fun k => @bnorm B (x k)) n).
Proof.
  intros B x n. induction n as [| m IH].
  - change (ncv_sum B x 0%nat) with (@bzero B).
    rewrite (@bnorm_zero B).
    change (ncv_qsum (fun k => @bnorm B (x k)) 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_sum B x (Datatypes.S m)) with (@bplus B (ncv_sum B x m) (x m)).
    change (ncv_qsum (fun k => @bnorm B (x k)) (Datatypes.S m))
      with (ncv_qsum (fun k => @bnorm B (x k)) m + @bnorm B (x m))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus B (ncv_sum B x m) (x m)).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IH.
      * apply qleT'_refl.
Qed.

(* 行范数界：‖Σ_{j<n} a_k·b_j‖ ≤ ‖a_k‖·Σ_{j<n}‖b_j‖ *)
Lemma ncv_norm_row_le : forall (B : BanachAlg) (a b : nat -> (@BA B)) (k n : nat),
  QleT' (@bnorm B (ncv_row B a b k n))
        (@bnorm B (a k) * ncv_qsum (fun j => @bnorm B (b j)) n)%Q.
Proof.
  intros B a b k n. unfold ncv_row.
  eapply qleT'_trans.
  - exact (ncv_norm_sum_le B (fun j => @bmult B (a k) (b j)) n).
  - eapply qleT'_trans.
    + apply (ncv_qsum_le (fun j => @bnorm B (@bmult B (a k) (b j)))
                         (fun j => (@bnorm B (a k) * @bnorm B (b j))%Q) n).
      intros j. exact (@bnorm_mult B (a k) (b j)).
    + apply qeq_leT'.
      exact (ncv_qsum_scalar_l (@bnorm B (a k)) (fun j => @bnorm B (b j)) n).
Qed.

(* 锚件：‖C(m,n)‖ ≤ (Σ_{k<m}‖a‖)·(Σ_{j<n}‖b‖) *)
Lemma ncv_norm_conv_le : forall (B : BanachAlg) (a b : nat -> (@BA B)) (m n : nat),
  QleT' (@bnorm B (ncv_conv B a b m n))
        (ncv_qsum (fun k => @bnorm B (a k)) m * ncv_qsum (fun j => @bnorm B (b j)) n)%Q.
Proof.
  intros B a b m n. induction m as [| m' IH].
  - change (ncv_conv B a b 0%nat n) with (@bzero B).
    rewrite (@bnorm_zero B).
    change (ncv_qsum (fun k => @bnorm B (a k)) 0%nat) with 0%Q.
    apply Qle_to_QleT'. apply qeq_imp_qle. ring.
  - change (ncv_conv B a b (Datatypes.S m') n)
      with (@bplus B (ncv_conv B a b m' n) (ncv_row B a b m' n)).
    change (ncv_qsum (fun k => @bnorm B (a k)) (Datatypes.S m'))
      with (ncv_qsum (fun k => @bnorm B (a k)) m' + @bnorm B (a m'))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus B (ncv_conv B a b m' n) (ncv_row B a b m' n)).
    + eapply qleT'_trans.
      * apply (qleT'_plus_compat _
                 (ncv_qsum (fun k => @bnorm B (a k)) m' * ncv_qsum (fun j => @bnorm B (b j)) n)%Q
                 _
                 ((@bnorm B (a m')) * ncv_qsum (fun j => @bnorm B (b j)) n)%Q).
        -- exact IH.
        -- exact (ncv_norm_row_le B a b m' n).
      * apply qeq_leT'. ring.
Qed.

(* ============================================================ *)
(* S3a：bae 层重排件（承 BanachExp middle_swap/opp_swap 同族）    *)
(* ============================================================ *)

(* 加法逆对合：-(-a) == a（bopp_unique 一步） *)
Lemma ncv_bopp_bopp : forall (B : BanachAlg) (a : (@BA B)),
  @bae B (@bopp B (@bopp B a)) a.
Proof.
  intros B a. apply (@bae_sym B a (@bopp B (@bopp B a))).
  apply (@bopp_unique B a (@bopp B a)).
  exact (@bplus_opp B a).
Qed.

(* -(y+v) == (-y)+(-v)（opp_swap + 对合） *)
Lemma ncv_bae_opp_plus : forall (B : BanachAlg) (y v : (@BA B)),
  @bae B (@bopp B (@bplus B y v)) (@bplus B (@bopp B y) (@bopp B v)).
Proof.
  intros B y v.
  eapply bae_trans.
  { apply (@bopp_wd B (@bplus B y v) (@bplus B y (@bopp B (@bopp B v)))).
    apply (@bplus_wd_r B v (@bopp B (@bopp B v)) y).
    apply (@bae_sym B _ _ (ncv_bopp_bopp B v)). }
  { apply (@bae_sym B _ _ (@bplus_opp_swap B y (@bopp B v))). }
Qed.

(* 差Join：x−z == (x−y)+(y−z)（插角重排，五步） *)
Lemma ncv_bae_diff_join : forall (B : BanachAlg) (x y z : (@BA B)),
  @bae B (@bplus B (@bplus B x (@bopp B y)) (@bplus B y (@bopp B z)))
        (@bplus B x (@bopp B z)).
Proof.
  intros B x y z.
  eapply bae_trans.
  { exact (@bplus_assoc B (@bplus B x (@bopp B y)) y (@bopp B z)). }
  eapply bae_trans.
  { exact (@bplus_wd_l B (@bplus B (@bplus B x (@bopp B y)) y)
             (@bplus B x (@bplus B (@bopp B y) y)) (@bopp B z)
             (@bae_sym B _ _ (@bplus_assoc B x (@bopp B y) y))). }
  eapply bae_trans.
  { exact (@bplus_wd_l B (@bplus B x (@bplus B (@bopp B y) y))
             (@bplus B x (@bplus B y (@bopp B y))) (@bopp B z)
             (@bplus_wd_r B (@bplus B (@bopp B y) y) (@bplus B y (@bopp B y)) x
                (@bplus_comm B (@bopp B y) y))). }
  eapply bae_trans.
  { exact (@bplus_wd_l B (@bplus B x (@bplus B y (@bopp B y))) (@bplus B x (@bzero B))
             (@bopp B z)
             (@bplus_wd_r B (@bplus B y (@bopp B y)) (@bzero B) x (@bplus_opp B y))). }
  exact (@bplus_wd_l B (@bplus B x (@bzero B)) x (@bopp B z) (@bplus_zero B x)).
Qed.

(* 四角重排：(x+u)−(y+v) == (x−y)+(u−v)（六步） *)
Lemma ncv_bae_quad : forall (B : BanachAlg) (x y u v : (@BA B)),
  @bae B (@bplus B (@bplus B x u) (@bopp B (@bplus B y v)))
        (@bplus B (@bplus B x (@bopp B y)) (@bplus B u (@bopp B v))).
Proof.
  intros B x y u v.
  eapply bae_trans.
  { exact (@bplus_wd_r B (@bopp B (@bplus B y v)) (@bplus B (@bopp B y) (@bopp B v))
             (@bplus B x u) (ncv_bae_opp_plus B y v)). }
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_assoc B x u (@bplus B (@bopp B y) (@bopp B v)))). }
  eapply bae_trans.
  { exact (@bplus_wd_r B (@bplus B u (@bplus B (@bopp B y) (@bopp B v)))
             (@bplus B (@bplus B (@bopp B y) u) (@bopp B v)) x
             (@bae_trans B _ _ _
                (@bplus_assoc B u (@bopp B y) (@bopp B v))
                (@bplus_wd_l B (@bplus B u (@bopp B y)) (@bplus B (@bopp B y) u)
                   (@bopp B v) (@bplus_comm B u (@bopp B y))))). }
  eapply bae_trans.
  { exact (@bplus_assoc B x (@bplus B (@bopp B y) u) (@bopp B v)). }
  eapply bae_trans.
  { exact (@bplus_wd_l B (@bplus B x (@bplus B (@bopp B y) u))
             (@bplus B (@bplus B x (@bopp B y)) u) (@bopp B v)
             (@bplus_assoc B x (@bopp B y) u)). }
  exact (@bae_sym B _ _ (@bplus_assoc B (@bplus B x (@bopp B y)) u (@bopp B v))).
Qed.

(* 范数差对称：‖x−y‖ ≈ ‖y−x‖（QeqT 运移形；Id 面 wd 弱化后不可达，
   语句面同步弱化——CLS-R2 沙箱偏差⑤放大位点处置实证） *)
Lemma ncv_norm_diff_sym : forall (B : BanachAlg) (x y : (@BA B)),
  QeqT (@bnorm B (@bplus B x (@bopp B y))) (@bnorm B (@bplus B y (@bopp B x))).
Proof.
  intros B x y.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm B (@bplus B (@bopp B y) x))).
  - apply qeqT_imp_qeq. exact (@bnorm_wd B _ _ (@bplus_comm B x (@bopp B y))).
  - apply (Qeq_trans _ (@bnorm B (@bopp B (@bplus B y (@bopp B x))))).
    + apply qeqT_imp_qeq. exact (@bnorm_wd B _ _ (@bplus_opp_swap B y x)).
    + rewrite (@bnorm_opp B (@bplus B y (@bopp B x))). apply Qeq_refl.
Qed.

(* 插角三角：‖x−z‖ ≤ ‖x−y‖ + ‖y−z‖ *)
Lemma ncv_norm_triangle_via : forall (B : BanachAlg) (x y z : (@BA B)),
  QleT' (@bnorm B (@bplus B x (@bopp B z)))
        (@bnorm B (@bplus B x (@bopp B y)) + @bnorm B (@bplus B y (@bopp B z)))%Q.
Proof.
  intros B x y z.
  eapply (QeqT_Qle_bool_cong _ _ _ (@bnorm_wd B _ _ (ncv_bae_diff_join B x y z))).
  exact (@bnorm_plus B (@bplus B x (@bopp B y)) (@bplus B y (@bopp B z))).
Qed.

(* 四角三角：‖(x+u)−(y+v)‖ ≤ ‖x−y‖ + ‖u−v‖ *)
Lemma ncv_norm_quad_le : forall (B : BanachAlg) (x y u v : (@BA B)),
  QleT' (@bnorm B (@bplus B (@bplus B x u) (@bopp B (@bplus B y v))))
        (@bnorm B (@bplus B x (@bopp B y)) + @bnorm B (@bplus B u (@bopp B v)))%Q.
Proof.
  intros B x y u v.
  eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd B _ _ (ncv_bae_quad B x y u v)))).
  exact (@bnorm_plus B (@bplus B x (@bopp B y)) (@bplus B u (@bopp B v))).
Qed.

(* ============================================================ *)
(* S3b：块范差界（行差/列差/行块），Mertens 的三块承重件          *)
(* ============================================================ *)

(* 行差界：n1≤n2 ⟹ ‖row_k(n2) − row_k(n1)‖ ≤ ‖a_k‖·Σ_{n1≤j<n2}‖b_j‖ *)
Lemma ncv_norm_row_diff_le : forall (B : BanachAlg) (a b : nat -> (@BA B)) (k n1 n2 : nat),
  (n1 <= n2)%nat ->
  QleT' (@bnorm B (@bplus B (ncv_row B a b k n2) (@bopp B (ncv_row B a b k n1))))
        (@bnorm B (a k) * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q.
Proof.
  intros B a b k n1 n2. revert n2.
  induction n2 as [| n' IH]; intros Hn2.
  - assert (Hn10 : n1 = 0%nat) by lia. subst n1.
    change (ncv_row B a b k 0%nat) with (@bzero B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd B _ _ (@bplus_opp B (@bzero B))))).
    rewrite (@bnorm_zero B).
    change (ncv_qtail (fun j => @bnorm B (b j)) 0%nat 0%nat) with 0%Q.
    apply Qle_to_QleT'. apply qeq_imp_qle. ring.
  - destruct (Nat.leb n1 n') eqn:En.
    + assert (Hn1n' : (n1 <= n')%nat) by (apply Nat.leb_le; exact En).
      change (ncv_row B a b k (Datatypes.S n'))
        with (@bplus B (ncv_row B a b k n') (@bmult B (a k) (b n'))).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd B _ _
        (@bplus_middle_swap B (ncv_row B a b k n') (@bmult B (a k) (b n'))
                            (@bopp B (ncv_row B a b k n1)))))).
      eapply qleT'_trans.
      * exact (@bnorm_plus B (@bplus B (ncv_row B a b k n') (@bopp B (ncv_row B a b k n1)))
                            (@bmult B (a k) (b n'))).
      * change (ncv_qtail (fun j => @bnorm B (b j)) n1 (Datatypes.S n'))
          with (ncv_qtail (fun j => @bnorm B (b j)) n1 n'
                + (if Nat.leb n1 n' then @bnorm B (b n') else 0%Q))%Q.
        rewrite En.
        eapply qleT'_trans.
        -- apply (qleT'_plus_compat _
                     (@bnorm B (a k) * ncv_qtail (fun j => @bnorm B (b j)) n1 n')%Q
                     _
                     (@bnorm B (a k) * @bnorm B (b n'))%Q).
           ++ exact (IH Hn1n').
           ++ exact (@bnorm_mult B (a k) (b n')).
        -- apply qeq_leT'. ring.
    + assert (Hn'1 : (n' < n1)%nat) by (apply (proj1 (Nat.leb_gt n1 n')); exact En).
      assert (Hn1S : n1 = Datatypes.S n') by lia. subst n1.
      change (ncv_row B a b k (Datatypes.S n'))
        with (@bplus B (ncv_row B a b k n') (@bmult B (a k) (b n'))).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd B _ _
        (@bplus_opp B (@bplus B (ncv_row B a b k n') (@bmult B (a k) (b n'))))))).
      rewrite (@bnorm_zero B).
      change (ncv_qtail (fun j => @bnorm B (b j)) (Datatypes.S n') (Datatypes.S n'))
        with (ncv_qtail (fun j => @bnorm B (b j)) (Datatypes.S n') n'
              + (if Nat.leb (Datatypes.S n') n' then @bnorm B (b n') else 0%Q))%Q.
      rewrite En.
      assert (Hq0 : (ncv_qtail (fun j => @bnorm B (b j)) (Datatypes.S n') n' + 0%Q)%Q == 0%Q).
      { rewrite (ncv_qtail_le_m (fun j => @bnorm B (b j)) (Datatypes.S n') n'
                   (Nat.le_succ_diag_r n')). ring. }
      assert (Hfull : ((@bnorm B (a k))
                       * (ncv_qtail (fun j => @bnorm B (b j)) (Datatypes.S n') n' + 0%Q))%Q
                      == 0%Q).
      { rewrite Hq0. ring. }
      apply Qle_to_QleT'.
      apply (qeq_imp_qle 0%Q
               (@bnorm B (a k)
                  * (ncv_qtail (fun j => @bnorm B (b j)) (Datatypes.S n') n' + 0%Q))%Q).
      symmetry. exact Hfull.
Qed.

(* 列差界：n1≤n2 ⟹ ‖C(M,n2) − C(M,n1)‖ ≤ (Σ_{k<M}‖a‖)·(b 尾 n1..n2) *)
Lemma ncv_norm_conv_coldiff_le : forall (B : BanachAlg) (a b : nat -> (@BA B)) (M n1 n2 : nat),
  (n1 <= n2)%nat ->
  QleT' (@bnorm B (@bplus B (ncv_conv B a b M n2) (@bopp B (ncv_conv B a b M n1))))
        (ncv_qsum (fun k => @bnorm B (a k)) M * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q.
Proof.
  intros B a b M. induction M as [| M' IH]; intros n1 n2 Hn.
  - change (ncv_conv B a b 0%nat n2) with (@bzero B).
    change (ncv_conv B a b 0%nat n1) with (@bzero B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd B _ _ (@bplus_opp B (@bzero B))))).
    rewrite (@bnorm_zero B).
    change (ncv_qsum (fun k => @bnorm B (a k)) 0%nat) with 0%Q.
    apply Qle_to_QleT'. apply qeq_imp_qle. ring.
  - change (ncv_conv B a b (Datatypes.S M') n2)
      with (@bplus B (ncv_conv B a b M' n2) (ncv_row B a b M' n2)).
    change (ncv_conv B a b (Datatypes.S M') n1)
      with (@bplus B (ncv_conv B a b M' n1) (ncv_row B a b M' n1)).
    eapply (QeqT_Qle_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd B _ _ (ncv_bae_quad B (ncv_conv B a b M' n2) (ncv_conv B a b M' n1)
                                         (ncv_row B a b M' n2) (ncv_row B a b M' n1))))).
    eapply qleT'_trans.
    + exact (@bnorm_plus B (@bplus B (ncv_conv B a b M' n2) (@bopp B (ncv_conv B a b M' n1)))
                          (@bplus B (ncv_row B a b M' n2) (@bopp B (ncv_row B a b M' n1)))).
    + change (ncv_qsum (fun k => @bnorm B (a k)) (Datatypes.S M'))
        with (ncv_qsum (fun k => @bnorm B (a k)) M' + @bnorm B (a M'))%Q.
      eapply qleT'_trans.
      * apply (qleT'_plus_compat _
                 (ncv_qsum (fun k => @bnorm B (a k)) M' * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q
                 _
                 ((@bnorm B (a M')) * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q).
        -- exact (IH n1 n2 Hn).
        -- exact (ncv_norm_row_diff_le B a b M' n1 n2 Hn).
      * apply qeq_leT'. ring.
Qed.

(* 行块界：M1≤M2 ⟹ ‖C(M2,n) − C(M1,n)‖ ≤ (a 尾 M1..M2)·(Σ_{j<n}‖b‖) *)
Lemma ncv_norm_conv_rowdiff_le : forall (B : BanachAlg) (a b : nat -> (@BA B)) (M1 M2 n : nat),
  (M1 <= M2)%nat ->
  QleT' (@bnorm B (@bplus B (ncv_conv B a b M2 n) (@bopp B (ncv_conv B a b M1 n))))
        (ncv_qtail (fun k => @bnorm B (a k)) M1 M2 * ncv_qsum (fun j => @bnorm B (b j)) n)%Q.
Proof.
  intros B a b M1 M2 n. revert M1.
  induction M2 as [| M2' IH]; intros M1 HM.
  - assert (HM10 : M1 = 0%nat) by lia. subst M1.
    change (ncv_conv B a b 0%nat n) with (@bzero B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd B _ _ (@bplus_opp B (@bzero B))))).
    rewrite (@bnorm_zero B).
    change (ncv_qtail (fun k => @bnorm B (a k)) 0%nat 0%nat) with 0%Q.
    apply Qle_to_QleT'. apply qeq_imp_qle. ring.
  - destruct (Nat.leb M1 M2') eqn:EM.
    + assert (HM1M2' : (M1 <= M2')%nat) by (apply Nat.leb_le; exact EM).
      change (ncv_conv B a b (Datatypes.S M2') n)
        with (@bplus B (ncv_conv B a b M2' n) (ncv_row B a b M2' n)).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd B _ _
        (@bplus_middle_swap B (ncv_conv B a b M2' n) (ncv_row B a b M2' n)
                            (@bopp B (ncv_conv B a b M1 n)))))).
      eapply qleT'_trans.
      * exact (@bnorm_plus B (@bplus B (ncv_conv B a b M2' n) (@bopp B (ncv_conv B a b M1 n)))
                            (ncv_row B a b M2' n)).
      * change (ncv_qtail (fun k => @bnorm B (a k)) M1 (Datatypes.S M2'))
          with (ncv_qtail (fun k => @bnorm B (a k)) M1 M2'
                + (if Nat.leb M1 M2' then @bnorm B (a M2') else 0%Q))%Q.
        rewrite EM.
        eapply qleT'_trans.
        -- apply (qleT'_plus_compat _
                     (ncv_qtail (fun k => @bnorm B (a k)) M1 M2' * ncv_qsum (fun j => @bnorm B (b j)) n)%Q
                     _
                     ((@bnorm B (a M2')) * ncv_qsum (fun j => @bnorm B (b j)) n)%Q).
           ++ exact (IH M1 HM1M2').
           ++ exact (ncv_norm_row_le B a b M2' n).
        -- apply qeq_leT'. ring.
    + assert (HM2'1 : (M2' < M1)%nat) by (apply (proj1 (Nat.leb_gt M1 M2')); exact EM).
      assert (HMEq : M1 = Datatypes.S M2') by lia. subst M1.
      change (ncv_conv B a b (Datatypes.S M2') n)
        with (@bplus B (ncv_conv B a b M2' n) (ncv_row B a b M2' n)).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd B _ _
        (@bplus_opp B (@bplus B (ncv_conv B a b M2' n) (ncv_row B a b M2' n)))))).
      rewrite (@bnorm_zero B).
      change (ncv_qtail (fun k => @bnorm B (a k)) (Datatypes.S M2') (Datatypes.S M2'))
        with (ncv_qtail (fun k => @bnorm B (a k)) (Datatypes.S M2') M2'
              + (if Nat.leb (Datatypes.S M2') M2' then @bnorm B (a M2') else 0%Q))%Q.
      rewrite EM.
      assert (Hq0 : (ncv_qtail (fun k => @bnorm B (a k)) (Datatypes.S M2') M2' + 0%Q)%Q == 0%Q).
      { rewrite (ncv_qtail_le_m (fun k => @bnorm B (a k)) (Datatypes.S M2') M2'
                   (Nat.le_succ_diag_r M2')). ring. }
      assert (Hfull : ((ncv_qtail (fun k => @bnorm B (a k)) (Datatypes.S M2') M2' + 0%Q)
                       * ncv_qsum (fun j => @bnorm B (b j)) n)%Q == 0%Q).
      { rewrite Hq0. ring. }
      apply Qle_to_QleT'.
      apply (qeq_imp_qle 0%Q
               ((ncv_qtail (fun k => @bnorm B (a k)) (Datatypes.S M2') M2' + 0%Q)
                * ncv_qsum (fun j => @bnorm B (b j)) n)%Q).
      symmetry. exact Hfull.
Qed.

(* ============================================================ *)
(* S3 主件：Mertens 核心形（QleT 面，显式界）                     *)
(*   前缀受控 Σ‖a‖≤Ba、Σ‖b‖≤Bb ⟹                                *)
(*   ‖C(m2,n2) − C(m1,n1)‖ ≤ Ba·(b 尾 n1..n2) + Bb·(a 尾 m1..m2)  *)
(* ============================================================ *)

Lemma ncv_mertens : forall (B : BanachAlg) (a b : nat -> (@BA B)) (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm B (b j)) K) Bb) ->
  forall m1 m2 n1 n2 : nat,
  (m1 <= m2)%nat -> (n1 <= n2)%nat ->
  QleT' (@bnorm B (@bplus B (ncv_conv B a b m2 n2) (@bopp B (ncv_conv B a b m1 n1))))
        (Ba * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
         + Bb * ncv_qtail (fun k => @bnorm B (a k)) m1 m2)%Q.
Proof.
  intros B a b Ba Bb Ha Hb m1 m2 n1 n2 Hm Hn.
  eapply (QeqT_Qle_bool_cong _ _ _
    (@bnorm_wd B _ _
    (ncv_bae_diff_join B (ncv_conv B a b m2 n2) (ncv_conv B a b m2 n1)
                        (ncv_conv B a b m1 n1)))).
  eapply qleT'_trans.
  - exact (@bnorm_plus B (@bplus B (ncv_conv B a b m2 n2) (@bopp B (ncv_conv B a b m2 n1)))
                        (@bplus B (ncv_conv B a b m2 n1) (@bopp B (ncv_conv B a b m1 n1)))).
  - apply (qleT'_trans
             (@bnorm B (@bplus B (ncv_conv B a b m2 n2) (@bopp B (ncv_conv B a b m2 n1)))
              + @bnorm B (@bplus B (ncv_conv B a b m2 n1) (@bopp B (ncv_conv B a b m1 n1))))%Q
             (ncv_qsum (fun k => @bnorm B (a k)) m2 * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
              + ncv_qtail (fun k => @bnorm B (a k)) m1 m2
                 * ncv_qsum (fun j => @bnorm B (b j)) n1)%Q
             (Ba * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
              + Bb * ncv_qtail (fun k => @bnorm B (a k)) m1 m2)%Q).
    + apply qleT'_plus_compat.
      * exact (ncv_norm_conv_coldiff_le B a b m2 n1 n2 Hn).
      * exact (ncv_norm_conv_rowdiff_le B a b m1 m2 n1 Hm).
    + apply (qleT'_trans
               (ncv_qsum (fun k => @bnorm B (a k)) m2
                  * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
                + ncv_qtail (fun k => @bnorm B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm B (b j)) n1)%Q
               (Ba * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
                + ncv_qtail (fun k => @bnorm B (a k)) m1 m2 * Bb)%Q
               (Ba * ncv_qtail (fun j => @bnorm B (b j)) n1 n2
                + Bb * ncv_qtail (fun k => @bnorm B (a k)) m1 m2)%Q).
      * apply qleT'_plus_compat.
        -- exact (qleT'_mult_compat_r (ncv_qsum (fun k => @bnorm B (a k)) m2) Ba
                    (ncv_qtail (fun j => @bnorm B (b j)) n1 n2)
                    (ncv_qtail_nonneg (fun j => @bnorm B (b j)) n1 n2
                       (fun j => @bnorm_pos B (b j)))
                    (Ha m2)).
        -- exact (qleT'_mult_compat_l (ncv_qsum (fun j => @bnorm B (b j)) n1) Bb
                    (ncv_qtail (fun k => @bnorm B (a k)) m1 m2)
                    (ncv_qtail_nonneg (fun k => @bnorm B (a k)) m1 m2
                       (fun k => @bnorm_pos B (a k)))
                    (Hb n1)).
      * apply qeq_leT'. ring.
Qed.


(* ============================================================ *)
(* S4：绝对收敛推卷积柯西（柯西判据组装）                         *)
(*   Q 侧尾判据（Σ‖a‖/Σ‖b‖ 的尾和任意小）+ Mertens 显式界         *)
(*   ⟹ 矩形部分和族 C(m,n) 四指标柯西 ⟹ 对角线序列 bcauchy。     *)
(*   阈值缩放：E := (Ba+Bb)+(1+1)，eps' := eps·/E，                *)
(*   则 (Ba+Bb)·eps' < E·eps' == eps（严格链全显式，零洞）。       *)
(* ============================================================ *)

(* 正 × 正 = 正（Qmult_lt_compat_r + qeq 运输，无 setoid 重写） *)
Lemma ncv_qmult_lt0 : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (x * y)%Q.
Proof.
  intros x y Hx Hy.
  apply (Qle_lt_trans 0 (0 * y)%Q (x * y)%Q).
  - apply qeq_imp_qle. ring.
  - apply (Qmult_lt_compat_r 0 x y Hy Hx).
Qed.

Lemma ncv_norm_conv_diff_sym : forall (B : BanachAlg) (a b : nat -> (@BA B))
                                         (p q r s : nat),
  QeqT (@bnorm B (@bplus B (ncv_conv B a b p q) (@bopp B (ncv_conv B a b r s))))
       (@bnorm B (@bplus B (ncv_conv B a b r s) (@bopp B (ncv_conv B a b p q)))).
Proof.
  intros B a b p q r s.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm B (@bplus B (@bopp B (ncv_conv B a b r s))
                                         (ncv_conv B a b p q)))).
  - apply qeqT_imp_qeq.
    exact (@bnorm_wd B _ _ (@bplus_comm B (ncv_conv B a b p q)
                                          (@bopp B (ncv_conv B a b r s)))).
  - apply (Qeq_trans _ (@bnorm B (@bopp B (@bplus B (ncv_conv B a b r s)
                                                   (@bopp B (ncv_conv B a b p q)))))).
    + apply qeqT_imp_qeq.
      exact (@bnorm_wd B _ _ (@bplus_opp_swap B (ncv_conv B a b r s)
                                              (ncv_conv B a b p q))).
    + rewrite (@bnorm_opp B (@bplus B (ncv_conv B a b r s)
                                      (@bopp B (ncv_conv B a b p q)))).
      apply Qeq_refl.
Qed.

Lemma ncv_conv_rect_cauchy : forall (B : BanachAlg) (a b : nat -> (@BA B))
                                              (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm B (b j)) K) Bb) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall u1 u2 : nat,
      NatLe T u1 -> NatLe T u2 -> QltT (ncv_qtail (fun k => @bnorm B (a k)) u1 u2) e)) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall v1 v2 : nat,
      NatLe T v1 -> NatLe T v2 -> QltT (ncv_qtail (fun j => @bnorm B (b j)) v1 v2) e)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m1 m2 n1 n2 : nat,
    NatLe N m1 -> NatLe N m2 -> NatLe N n1 -> NatLe N n2 ->
    QltT (@bnorm B (@bplus B (ncv_conv B a b m2 n2)
                            (@bopp B (ncv_conv B a b m1 n1)))) eps).
Proof.
  intros B a b Ba Bb Ha Hb Hta Htb eps Heps.
  assert (Ha0 : QleT' 0 Ba) by exact (Ha 0%nat).
  assert (Hb0 : QleT' 0 Bb) by exact (Hb 0%nat).
  assert (H0Ba : Qle 0 Ba) by (apply QleT'_to_Qle; exact Ha0).
  assert (H0Bb : Qle 0 Bb) by (apply QleT'_to_Qle; exact Hb0).
  assert (HtBB : Qle 0 (Ba + Bb)%Q).
  { apply (Qle_trans 0 (0 + 0)%Q (Ba + Bb)%Q).
    - apply qeq_imp_qle. ring.
    - apply (Qplus_le_compat 0 Ba 0 Bb); assumption. }
  (* E := (Ba+Bb) + 2 > 0 *)
  assert (HleE : Qle (1 + 1)%Q (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qle_trans (1 + 1)%Q ((1 + 1)%Q + 0%Q)
                     ((Ba + Bb)%Q + (1 + 1))%Q).
    - apply qeq_imp_qle. ring.
    - apply (Qle_trans ((1 + 1)%Q + 0%Q) ((1 + 1)%Q + (Ba + Bb)%Q)
                       ((Ba + Bb)%Q + (1 + 1))%Q).
      + apply (Qplus_le_compat (1 + 1)%Q (1 + 1)%Q 0%Q (Ba + Bb)%Q).
        * apply Qle_refl.
        * exact HtBB.
      + apply qeq_imp_qle. ring. }
  assert (H0E : Qlt 0 (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qlt_le_trans 0 (1 + 1)%Q ((Ba + Bb)%Q + (1 + 1))%Q).
    - reflexivity.
    - exact HleE. }
  assert (H0Einv : Qlt 0 (/ ((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qinv_lt_0_compat _ H0E). }
  assert (Hlt0epsD : Qlt 0 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q).
  { apply (ncv_qmult_lt0 _ _ (QltT_to_Qlt 0 eps Heps) H0Einv). }
  assert (HltT0epsD : QltT 0 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q).
  { apply (Qlt_to_QltT _ _ Hlt0epsD). }
  assert (Hcan : (((Ba + Bb)%Q + (1 + 1))%Q
                  * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q) == eps)
    by (field; apply q_neq_of_lt; exact H0E).
  assert (HltBD : Qlt (Ba + Bb)%Q (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qle_lt_trans (Ba + Bb)%Q ((Ba + Bb)%Q + 0%Q)
                        ((Ba + Bb)%Q + (1 + 1))%Q).
    - apply qeq_imp_qle. ring.
    - apply (proj2 (Qplus_lt_r 0 (1 + 1)%Q (Ba + Bb)%Q)). reflexivity. }
  destruct (Hta (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q HltT0epsD) as [Ta Htaf].
  destruct (Htb (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q HltT0epsD) as [Tb Htbf].
  (* 尾步：X ≤ Ba·eps' + Bb·eps' → X < eps *)
  assert (Hfin : forall X : Q,
    QleT' X (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q ->
    QltT X eps).
  { intros X HX.
    assert (Hr1 : (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                   + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                  == ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q) by ring.
    assert (Hs : ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q < eps).
    { pose proof (Qmult_lt_compat_r (Ba + Bb)%Q
                    ((Ba + Bb)%Q + (1 + 1))%Q
                    (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q
                    Hlt0epsD HltBD) as Hs0.
      setoid_rewrite Hcan in Hs0. exact Hs0. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans X ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q eps).
    - apply QleT'_to_Qle.
      exact (qleT'_trans X
               (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
               ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
               HX
               (qeq_leT' (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                          + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                         ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                         Hr1)).
    - exact Hs. }
  (* 列块缩放：qs_a(u)·qtb(v1,v2) ≤ Ba·eps'（v1,v2 双端 ≥ Tb） *)
  assert (HscA : forall (u v1 v2 : nat),
    NatLe Tb v1 -> NatLe Tb v2 ->
    QleT' (ncv_qsum (fun k => @bnorm B (a k)) u
           * ncv_qtail (fun j => @bnorm B (b j)) v1 v2)%Q
          (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros u v1 v2 Hv1 Hv2.
    apply (qleT'_trans
             (ncv_qsum (fun k => @bnorm B (a k)) u
              * ncv_qtail (fun j => @bnorm B (b j)) v1 v2)%Q
             (Ba * ncv_qtail (fun j => @bnorm B (b j)) v1 v2)%Q
             (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    - apply (qleT'_mult_compat_r (ncv_qsum (fun k => @bnorm B (a k)) u) Ba
               (ncv_qtail (fun j => @bnorm B (b j)) v1 v2)
               (ncv_qtail_nonneg (fun j => @bnorm B (b j)) v1 v2
                  (fun j => @bnorm_pos B (b j)))
               (Ha u)).
    - apply (qleT'_mult_compat_l (ncv_qtail (fun j => @bnorm B (b j)) v1 v2)
               (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q Ba Ha0).
      apply qltT_leT'. exact (Htbf v1 v2 Hv1 Hv2). }
  (* 行块缩放：qta(u1,u2)·qs_b(v) ≤ Bb·eps'（u1,u2 双端 ≥ Ta） *)
  assert (HscB : forall (u1 u2 v : nat),
    NatLe Ta u1 -> NatLe Ta u2 ->
    QleT' (ncv_qtail (fun k => @bnorm B (a k)) u1 u2
           * ncv_qsum (fun j => @bnorm B (b j)) v)%Q
          (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros u1 u2 v Hu1 Hu2.
    apply (qleT'_trans
             (ncv_qtail (fun k => @bnorm B (a k)) u1 u2
              * ncv_qsum (fun j => @bnorm B (b j)) v)%Q
             ((ncv_qtail (fun k => @bnorm B (a k)) u1 u2) * Bb)%Q
             (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    - apply (qleT'_mult_compat_l (ncv_qsum (fun j => @bnorm B (b j)) v) Bb
               (ncv_qtail (fun k => @bnorm B (a k)) u1 u2)
               (ncv_qtail_nonneg (fun k => @bnorm B (a k)) u1 u2
                  (fun k => @bnorm_pos B (a k)))
               (Hb v)).
    - apply (qleT'_trans
               ((ncv_qtail (fun k => @bnorm B (a k)) u1 u2) * Bb)%Q
               (Bb * ncv_qtail (fun k => @bnorm B (a k)) u1 u2)%Q
               (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
      + apply qeq_leT'. ring.
      + apply (qleT'_mult_compat_l (ncv_qtail (fun k => @bnorm B (a k)) u1 u2)
                 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q Bb Hb0).
        apply qltT_leT'. exact (Htaf u1 u2 Hu1 Hu2). }
  (* 组装器：‖x−z‖ 经插角 y 与双块缩放收尾（块序无关，gat/gbt 为两块终界） *)
  assert (Hfin2 : forall (x y z : (@BA B)) (ga gb gat gbt : Q),
    QleT' (@bnorm B (@bplus B x (@bopp B y))) ga ->
    QleT' (@bnorm B (@bplus B y (@bopp B z))) gb ->
    QleT' ga gat ->
    QleT' gb gbt ->
    QleT' (@bnorm B (@bplus B x (@bopp B z))) (gat + gbt)%Q).
  { intros x y z ga gb gat gbt Hxy Hyz Hga Hgb.
    apply (qleT'_trans
             (@bnorm B (@bplus B x (@bopp B z)))
             (@bnorm B (@bplus B x (@bopp B y))
              + @bnorm B (@bplus B y (@bopp B z)))%Q
             (gat + gbt)%Q
             (ncv_norm_triangle_via B x y z)
             (qleT'_plus_compat
                (@bnorm B (@bplus B x (@bopp B y))) gat
                (@bnorm B (@bplus B y (@bopp B z))) gbt
                (qleT'_trans
                   (@bnorm B (@bplus B x (@bopp B y))) ga gat Hxy Hga)
                (qleT'_trans
                   (@bnorm B (@bplus B y (@bopp B z))) gb gbt Hyz Hgb))). }
  (* 交叉分支（FT/FF）的加和序交换器 *)
  assert (Hswap : forall X : Q,
    QleT' X (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q ->
    QleT' X (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros X HX0.
    assert (Hr2 : (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                   + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                  == (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                      + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q) by ring.
    exact (qleT'_trans X
             (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
              + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
             (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
              + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
             HX0
             (qeq_leT' (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                        + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                       (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                        + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                       Hr2)). }
  exists (Nat.max Ta Tb).
  intros m1 m2 n1 n2 Hm1 Hm2 Hn1 Hn2.
  assert (HPa1 : NatLe Ta m1).
  { apply NatLe_lift.
    exact (Nat.le_trans Ta (Nat.max Ta Tb) m1
             (Nat.le_max_l Ta Tb) (NatLe_drop _ _ Hm1)). }
  assert (HPa2 : NatLe Ta m2).
  { apply NatLe_lift.
    exact (Nat.le_trans Ta (Nat.max Ta Tb) m2
             (Nat.le_max_l Ta Tb) (NatLe_drop _ _ Hm2)). }
  assert (HPb1 : NatLe Tb n1).
  { apply NatLe_lift.
    exact (Nat.le_trans Tb (Nat.max Ta Tb) n1
             (Nat.le_max_r Ta Tb) (NatLe_drop _ _ Hn1)). }
  assert (HPb2 : NatLe Tb n2).
  { apply NatLe_lift.
    exact (Nat.le_trans Tb (Nat.max Ta Tb) n2
             (Nat.le_max_r Ta Tb) (NatLe_drop _ _ Hn2)). }
  destruct (Nat.leb m1 m2) eqn:Em; destruct (Nat.leb n1 n2) eqn:En.
  - (* m1<=m2, n1<=n2：插角 (m2,n1) *)
    apply Hfin.
    apply (Hfin2 (ncv_conv B a b m2 n2) (ncv_conv B a b m2 n1)
                 (ncv_conv B a b m1 n1)
                 (ncv_qsum (fun k => @bnorm B (a k)) m2
                  * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q
                 (ncv_qtail (fun k => @bnorm B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm B (b j)) n1)%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + exact (ncv_norm_conv_coldiff_le B a b m2 n1 n2
               (proj1 (Nat.leb_le n1 n2) En)).
    + exact (ncv_norm_conv_rowdiff_le B a b m1 m2 n1
               (proj1 (Nat.leb_le m1 m2) Em)).
    + exact (HscA m2 n1 n2 HPb1 HPb2).
    + exact (HscB m1 m2 n1 HPa1 HPa2).
  - (* m1<=m2, n2<n1：插角 (m2,n1)，列块反向 *)
    apply Hfin.
    apply (Hfin2 (ncv_conv B a b m2 n2) (ncv_conv B a b m2 n1)
                 (ncv_conv B a b m1 n1)
                 (ncv_qsum (fun k => @bnorm B (a k)) m2
                  * ncv_qtail (fun j => @bnorm B (b j)) n2 n1)%Q
                 (ncv_qtail (fun k => @bnorm B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm B (b j)) n1)%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + eapply (QeqT_Qle_bool_cong _ _ _
               (ncv_norm_diff_sym B (ncv_conv B a b m2 n1) (ncv_conv B a b m2 n2))).
      exact (ncv_norm_conv_coldiff_le B a b m2 n2 n1
               (Nat.lt_le_incl n2 n1 (proj1 (Nat.leb_gt n1 n2) En))).
    + exact (ncv_norm_conv_rowdiff_le B a b m1 m2 n1
               (proj1 (Nat.leb_le m1 m2) Em)).
    + exact (HscA m2 n2 n1 HPb2 HPb1).
    + exact (HscB m1 m2 n1 HPa1 HPa2).
  - (* m2<m1, n1<=n2：插角 (m1,n2) *)
    apply Hfin.
    apply Hswap.
    apply (Hfin2 (ncv_conv B a b m2 n2) (ncv_conv B a b m1 n2)
                 (ncv_conv B a b m1 n1)
                 (ncv_qtail (fun k => @bnorm B (a k)) m2 m1
                  * ncv_qsum (fun j => @bnorm B (b j)) n2)%Q
                 (ncv_qsum (fun k => @bnorm B (a k)) m1
                  * ncv_qtail (fun j => @bnorm B (b j)) n1 n2)%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + eapply (QeqT_Qle_bool_cong _ _ _
               (ncv_norm_diff_sym B (ncv_conv B a b m1 n2) (ncv_conv B a b m2 n2))).
      exact (ncv_norm_conv_rowdiff_le B a b m2 m1 n2
               (Nat.lt_le_incl m2 m1 (proj1 (Nat.leb_gt m1 m2) Em))).
    + exact (ncv_norm_conv_coldiff_le B a b m1 n1 n2
               (proj1 (Nat.leb_le n1 n2) En)).
    + exact (HscB m2 m1 n2 HPa2 HPa1).
    + exact (HscA m1 n1 n2 HPb1 HPb2).
  - (* m2<m1, n2<n1：对称换角后插角 (m2,n1) *)
    eapply (QeqT_Qlt_bool_cong _ _ _
             (qeqT_sym_hw _ _ (ncv_norm_conv_diff_sym B a b m2 n2 m1 n1))).
    apply Hfin.
    apply Hswap.
    apply (Hfin2 (ncv_conv B a b m1 n1) (ncv_conv B a b m2 n1)
                 (ncv_conv B a b m2 n2)
                 (ncv_qtail (fun k => @bnorm B (a k)) m2 m1
                  * ncv_qsum (fun j => @bnorm B (b j)) n1)%Q
                 (ncv_qsum (fun k => @bnorm B (a k)) m2
                  * ncv_qtail (fun j => @bnorm B (b j)) n2 n1)%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + exact (ncv_norm_conv_rowdiff_le B a b m2 m1 n1
               (Nat.lt_le_incl m2 m1 (proj1 (Nat.leb_gt m1 m2) Em))).
    + exact (ncv_norm_conv_coldiff_le B a b m2 n2 n1
               (Nat.lt_le_incl n2 n1 (proj1 (Nat.leb_gt n1 n2) En))).
    + exact (HscB m2 m1 n1 HPa2 HPa1).
    + exact (HscA m2 n2 n1 HPb2 HPb1).
Qed.

(* 对角线部分和序列 u n := C(n,n) 的 bcauchy 形态（柯西积单序列面） *)
Corollary ncv_conv_diag_cauchy : forall (B : BanachAlg) (a b : nat -> (@BA B))
                                                  (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm B (b j)) K) Bb) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall u1 u2 : nat,
      NatLe T u1 -> NatLe T u2 -> QltT (ncv_qtail (fun k => @bnorm B (a k)) u1 u2) e)) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall v1 v2 : nat,
      NatLe T v1 -> NatLe T v2 -> QltT (ncv_qtail (fun j => @bnorm B (b j)) v1 v2) e)) ->
  bcauchy B (fun n => ncv_conv B a b n n).
Proof.
  intros B a b Ba Bb Ha Hb Hta Htb eps Heps.
  destruct (ncv_conv_rect_cauchy B a b Ba Bb Ha Hb Hta Htb eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  exact (HN n m n m Hn Hm Hn Hm).
Qed.
