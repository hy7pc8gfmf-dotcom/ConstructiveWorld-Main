(* ============================================================ *)
(* UpReqCStarDef.v —— C* 代数定义面 + 正元 Newton 平方根显式率          *)
(*                                                                     *)
(* 使命：在 BanachAlg（UpReqBanachExp，B 路基建）之上装配 C* 代数       *)
(*   （对合 Banach 代数 + C* 恒等式 ‖a*a‖=‖a‖²）的 Set/sigT 定义面，    *)
(*   并给严格正元 Newton 平方根的构造性收敛与显式率（经典证明用序       *)
(*   完备性；本件给显式模量与可提取 N）。分层结果：                     *)
(*   S1 = Class CStarAlg：BanachAlg 包装 + 对合 cst_star（反线性        *)
(*        add/mult/involution + star 1 + star 系数）+ C* 恒等式场       *)
(*        cst_norm_sq（QeqT 面）；派生 star 零/负、‖star a‖=‖a‖ 等距   *)
(*        （Q 双侧消去）。                                              *)
(*   S2 = Q 层 Newton 引擎：x0=a+1，x_{n+1}=(x_n+a/x_n)/2，精确恒等式   *)
(*        d_{n+1}=d_n²/(4·x_n²)（二次收敛系数化），几何率               *)
(*        d_m ≤ d0·(1/4)^m，显式 N 经 q_arch_geom 系数化。              *)
(*   S3 = 范数迁移：bcoef 嵌入面 ‖x_m²−bcoef q‖<eps（任意 BanachAlg，   *)
(*        显式 N 逐字继承；标量子代数嵌入面，如实降档登记）。           *)
(*   S4 = 正元锥（a = star b·b 形，sigT 见证——LPO 规避：正性一律走      *)
(*        见证形不走序判定）+ 正元自伴 + star 残差交换；锥级引理面。    *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp；   *)
(*   Stdlib QArith.QArith、QArith.Qabs、Arith.Arith、Lia。              *)
(* 对标：mathlib C*-algebra 基础定义与正元平方根构造。                  *)
(* 构造性注记：零承认、公理面为空、零中断件；语句面全 Set/sigT 零      *)
(*   Prop（bae/QeqT/QleT'/QltT/NatLe/sigT）；证内 Q 层 Prop（Qle/Qlt）  *)
(*   仅作引擎内衬，不落语句面。                                         *)
(* 编译配方：Rocq 9.1 直调 rocq c -Q . "" UpReqCStarDef.v，cpu_guard    *)
(*   包装；类投影实例参为隐式——类字段一律 @ 显式传实例参数；Q 层       *)
(*   积/商一律 %Q 显式作用域。                                          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* ============================================================ *)
(* S1：Class CStarAlg —— 对合 Banach 代数 + C* 恒等式（Set 面）   *)
(* ============================================================ *)

Class CStarAlg := {
  cbase : BanachAlg;                             (* 底 Banach 代数 *)

  cst_star : @BA cbase -> @BA cbase;             (* 对合 *)

  cst_star_wd : forall a b : @BA cbase,
    @bae cbase a b -> @bae cbase (cst_star a) (cst_star b);
  cst_star_add : forall a b : @BA cbase,
    @bae cbase (cst_star (@bplus cbase a b))
                 (@bplus cbase (cst_star a) (cst_star b));
  cst_star_mult : forall a b : @BA cbase,
    @bae cbase (cst_star (@bmult cbase a b))
                 (@bmult cbase (cst_star b) (cst_star a));
  cst_star_star : forall a : @BA cbase,
    @bae cbase (cst_star (cst_star a)) a;
  cst_star_one : @bae cbase (cst_star (@bone cbase)) (@bone cbase);
  cst_star_coef : forall q : Q,
    @bae cbase (cst_star (@bcoef cbase q)) (@bcoef cbase q);

  (* C* 恒等式：‖star a · a‖ = ‖a‖²（QeqT 面，零 Prop） *)
  cst_norm_sq : forall a : @BA cbase,
    QeqT (@bnorm cbase (@bmult cbase (cst_star a) a))
         ((@bnorm cbase a) * (@bnorm cbase a))%Q
}.

(* ============================================================ *)
(* Q 层内衬工具（Prop 面，仅证内用）                              *)
(* ============================================================ *)

Lemma cst_q_le_0_sq_zero : forall x : Q, Qle 0 x -> Qle (x * x) 0 -> x == 0.
Proof.
  intros x Hx0 Hsq.
  destruct (Qle_lt_or_eq 0 x Hx0) as [Hlt | Heq].
  - exfalso.
    assert (H2lt : Qlt 0 (x * x)) by (apply (Qmult_lt_0_compat x x); exact Hlt).
    assert (H2le : Qle 0 (x * x)) by (apply Qlt_le_weak; exact H2lt).
    assert (H0 : (x * x) == 0) by (apply Qle_antisym; [exact Hsq | exact H2le]).
    apply (q_neq_of_lt (x * x) H2lt H0).
  - apply Qeq_sym. exact Heq.
Qed.

Lemma cst_nat_q_le : forall n m : nat, (n <= m)%nat ->
  Qle (Z.of_nat n # 1) (Z.of_nat m # 1).
Proof.
  intros n m H. unfold Qle. simpl. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le n m)). exact H.
Qed.

(* Qeq 左运载：x == y 且 y <= z ⟹ x <= z（rewrite 进 Qeq 假设类型不达，改走运载件） *)
Lemma cst_qeq_le_l : forall x y z : Q, x == y -> Qle y z -> Qle x z.
Proof.
  intros x y z Hxy Hy. apply (Qle_trans x y z).
  - rewrite Hxy. apply Qle_refl.
  - exact Hy.
Qed.

(* Qeq 右运载：x <= y 且 y == z ⟹ x <= z *)
Lemma cst_qeq_le_r : forall x y z : Q, Qle x y -> y == z -> Qle x z.
Proof.
  intros x y z Hxy Hyz. apply (Qle_trans x y z).
  - exact Hxy.
  - rewrite Hyz. apply Qle_refl.
Qed.

(* 反比反单调：0 < B <= A 蕴含 /A <= /B *)
Lemma cst_qinv_anti : forall A B : Q, Qlt 0 B -> Qle B A -> Qle (/ A) (/ B).
Proof.
  intros A B HB HBA.
  assert (HAlt : Qlt 0 A) by (apply (Qlt_le_trans 0 B A); [exact HB | exact HBA]).
  assert (HAB : Qlt 0 (A * B)) by (apply (Qmult_lt_0_compat A B); assumption).
  assert (Hne : ~ (A * B == 0)) by (apply q_neq_of_lt; exact HAB).
  assert (HAn : ~ (A == 0)) by (apply q_neq_of_lt; exact HAlt).
  assert (HBn : ~ (B == 0)) by (apply q_neq_of_lt; exact HB).
  assert (Hinv : Qle 0 (/ (A * B))).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HAB. }
  assert (E1 : / A == B * / (A * B)) by (field; repeat split; assumption).
  assert (E2 : / B == A * / (A * B)) by (field; repeat split; assumption).
  pose proof (Qmult_le_compat_r B A (/ (A * B)) HBA Hinv) as Hm.
  rewrite E1, E2. exact Hm.
Qed.

(* ============================================================ *)
(* S1 派生：star 基础引理（bae 面直构）                           *)
(* ============================================================ *)

Lemma cst_bae_bopp_invol : forall (B : BanachAlg) (x : @BA B),
  @bae B x (@bopp B (@bopp B x)).
Proof. intros B x. exact (@bopp_unique B x (@bopp B x) (@bplus_opp B x)). Qed.

Lemma cst_star_zero : forall (C : CStarAlg),
  @bae (@cbase C) (@cst_star C (@bzero (@cbase C))) (@bzero (@cbase C)).
Proof.
  intros C.
  pose proof (bplus_zero_l (@cbase C) (@bzero (@cbase C))) as Hz.
  (* star 0 == star 0 + star 0（star_wd + star_add） *)
  assert (Hdup : @bae (@cbase C) (@cst_star C (@bzero (@cbase C)))
                   (@bplus (@cbase C) (@cst_star C (@bzero (@cbase C)))
                            (@cst_star C (@bzero (@cbase C))))).
  { eapply @bae_trans.
    - apply (@bae_sym (@cbase C) _ _
               (@cst_star_wd C (@bplus (@cbase C) (@bzero (@cbase C))
                                       (@bzero (@cbase C)))
                               (@bzero (@cbase C)) Hz)).
    - exact (@cst_star_add C (@bzero (@cbase C)) (@bzero (@cbase C))). }
  (* 两侧加 −star 0 完成（bopp_unique 传递链） *)
  apply @bae_sym.
  eapply @bae_trans.
  { apply (@bae_sym (@cbase C) _ _
             (@bplus_opp (@cbase C) (@cst_star C (@bzero (@cbase C))))). }
  eapply @bae_trans.
  { apply (@bplus_wd_l (@cbase C) (@cst_star C (@bzero (@cbase C)))
             (@bplus (@cbase C) (@cst_star C (@bzero (@cbase C)))
                                     (@cst_star C (@bzero (@cbase C))))
             (@bopp (@cbase C) (@cst_star C (@bzero (@cbase C)))) Hdup). }
  eapply @bae_trans.
  { apply (@bae_sym (@cbase C) _ _
             (@bplus_assoc (@cbase C) (@cst_star C (@bzero (@cbase C)))
                           (@cst_star C (@bzero (@cbase C)))
                           (@bopp (@cbase C) (@cst_star C (@bzero (@cbase C)))))). }
  eapply @bae_trans.
  { apply (@bplus_wd_r (@cbase C)
             (@bplus (@cbase C) (@cst_star C (@bzero (@cbase C)))
                      (@bopp (@cbase C) (@cst_star C (@bzero (@cbase C)))))
             (@bzero (@cbase C))
             (@cst_star C (@bzero (@cbase C)))
             (@bplus_opp (@cbase C) (@cst_star C (@bzero (@cbase C))))). }
  exact (@bplus_zero (@cbase C) (@cst_star C (@bzero (@cbase C)))).
Qed.

Lemma cst_star_opp : forall (C : CStarAlg) (a : @BA (@cbase C)),
  @bae (@cbase C) (@cst_star C (@bopp (@cbase C) a))
                 (@bopp (@cbase C) (@cst_star C a)).
Proof.
  intros C a.
  apply (@bopp_unique (@cbase C) (@cst_star C (@bopp (@cbase C) a))
                      (@cst_star C a)).
  eapply @bae_trans.
  { apply (@bplus_comm (@cbase C) (@cst_star C (@bopp (@cbase C) a))
                      (@cst_star C a)). }
  eapply @bae_trans.
  { apply (@bae_sym (@cbase C) _ _
             (@cst_star_add C a (@bopp (@cbase C) a))). }
  eapply @bae_trans.
  { apply (@cst_star_wd C (@bplus (@cbase C) a (@bopp (@cbase C) a))
             (@bzero (@cbase C)) (@bplus_opp (@cbase C) a)). }
  exact (@cst_star_zero C).
Qed.

(* cst_star_pow（star 与幂交换）裁剪显式假设：需同元幂交换引理
   bpow b n 乘 b 与 b 乘 bpow b n 相等（BanachAlg 无现货，归纳
   可证），下一注册波补装。 *)

(* C* 恒等式 ⟹ star 等距：‖star a‖ = ‖a‖（Q 双侧构造性消去） *)
Lemma cst_norm_star : forall (C : CStarAlg) (a : @BA (@cbase C)),
  QeqT (@bnorm (@cbase C) (@cst_star C a)) (@bnorm (@cbase C) a).
Proof.
  intros C a.
  pose proof (QleT'_to_Qle _ _ (@bnorm_pos (@cbase C) a)) as HA0.
  pose proof (QleT'_to_Qle _ _ (@bnorm_pos (@cbase C) (@cst_star C a))) as HS0.
  pose proof (qeqT_imp_qeq _ _ (@cst_norm_sq C a)) as Hsq1.
  assert (H1 : Qle ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) a))
                   ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) a))).
  { pose proof (QleT'_to_Qle _ _ (@bnorm_mult (@cbase C) (@cst_star C a) a)) as Hm.
    rewrite Hsq1 in Hm. exact Hm. }
  assert (H2 : Qle ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) (@cst_star C a)))
                   ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) (@cst_star C a)))).
  { pose proof (qeqT_imp_qeq _ _ (@cst_norm_sq C (@cst_star C a))) as Hsq2.
    pose proof (QleT'_to_Qle _ _ (@bnorm_mult (@cbase C) a (@cst_star C a))) as Hm.
    apply (cst_qeq_le_l _ _ _ (Qeq_sym _ _ Hsq2)).
    apply (Qle_trans _ (@bnorm (@cbase C)
              (@bmult (@cbase C) a (@cst_star C a)))).
    - apply (cst_qeq_le_l _ _ _
        (qeqT_imp_qeq _ _ (@bnorm_wd (@cbase C)
        (@bmult (@cbase C) (@cst_star C (@cst_star C a)) (@cst_star C a))
        (@bmult (@cbase C) a (@cst_star C a))
        (@bmult_wd (@cbase C) (@cst_star C (@cst_star C a)) (@cst_star C a)
                   a (@cst_star C a)
                   (@cst_star_star C a) (@bae_refl (@cbase C) (@cst_star C a)))))).
      apply Qle_refl.
    - exact Hm. }
  assert (Hcancel : (@bnorm (@cbase C) a) == (@bnorm (@cbase C) (@cst_star C a))).
  { destruct (Qle_lt_or_eq 0 (@bnorm (@cbase C) (@cst_star C a)) HS0) as [HSlt | HSeq].
    - destruct (Qle_lt_or_eq 0 (@bnorm (@cbase C) a) HA0) as [HAlt | HAeq].
      + (* A > 0 且 S > 0：双侧除 A、除 S 消去（field 面，构造性） *)
        assert (HAn : ~ ((@bnorm (@cbase C) a) == 0))
          by (apply q_neq_of_lt; exact HAlt).
        assert (HinvA : Qle 0 (/ (@bnorm (@cbase C) a)))
          by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HAlt).
        assert (EA : (@bnorm (@cbase C) a) * (@bnorm (@cbase C) a)
                       * (/ (@bnorm (@cbase C) a)) == (@bnorm (@cbase C) a))
          by (field; repeat split; assumption).
        assert (EB : ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) a))
                     * (/ (@bnorm (@cbase C) a))
                     == (@bnorm (@cbase C) (@cst_star C a)))
          by (field; repeat split; assumption).
        pose proof (Qmult_le_compat_r
          ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) a))
          ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) a))
          (/ (@bnorm (@cbase C) a)) H1 HinvA) as Hd1.
        rewrite EA, EB in Hd1.
        assert (HSn : ~ ((@bnorm (@cbase C) (@cst_star C a)) == 0))
          by (apply q_neq_of_lt; exact HSlt).
        assert (HinvS : Qle 0 (/ (@bnorm (@cbase C) (@cst_star C a))))
          by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HSlt).
        assert (EC : (@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) (@cst_star C a))
                     * (/ (@bnorm (@cbase C) (@cst_star C a)))
                     == (@bnorm (@cbase C) (@cst_star C a)))
          by (field; repeat split; assumption).
        assert (ED : ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) (@cst_star C a)))
                     * (/ (@bnorm (@cbase C) (@cst_star C a)))
                     == (@bnorm (@cbase C) a))
          by (field; repeat split; assumption).
        pose proof (Qmult_le_compat_r
          ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) (@cst_star C a)))
          ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) (@cst_star C a)))
          (/ (@bnorm (@cbase C) (@cst_star C a))) H2 HinvS) as Hd2.
        rewrite EC, ED in Hd2.
        apply Qle_antisym; assumption.
      + (* A == 0 ⟹ 由 H2 得 S == 0（Qeq 右运载，避嵌套 rewrite） *)
        apply Qeq_sym in HAeq.
        assert (HAeqS : ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) (@cst_star C a))) == 0)
          by (rewrite HAeq; apply Qmult_0_l).
        pose proof (cst_qeq_le_r
          ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) (@cst_star C a)))
          ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) (@cst_star C a)))
          0 H2 HAeqS) as H2'.
        assert (HSz : (@bnorm (@cbase C) (@cst_star C a)) == 0)
          by (apply (cst_q_le_0_sq_zero _ HS0); exact H2').
        rewrite HSz. exact HAeq.
    - (* S == 0 ⟹ 由 H1 得 A == 0（Qeq 右运载） *)
      apply Qeq_sym in HSeq.
      assert (HSeqA : ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) a)) == 0)
        by (rewrite HSeq; apply Qmult_0_l).
      pose proof (cst_qeq_le_r
        ((@bnorm (@cbase C) a) * (@bnorm (@cbase C) a))
        ((@bnorm (@cbase C) (@cst_star C a)) * (@bnorm (@cbase C) a))
        0 H1 HSeqA) as H1'.
      assert (HAz : (@bnorm (@cbase C) a) == 0)
        by (apply (cst_q_le_0_sq_zero _ HA0); exact H1').
      rewrite HSeq. exact HAz. }
  apply qeq_imp_qeqT. apply Qeq_sym. exact Hcancel.
Qed.

(* ============================================================ *)
(* S2：Q 层 Newton 平方根引擎（显式率主战场）                      *)
(* ============================================================ *)

Fixpoint cst_nseq (a : Q) (n : nat) : Q :=
  match n with
  | 0%nat => a + 1
  | Datatypes.S m => (cst_nseq a m + a / cst_nseq a m) / 2
  end.

(* 序列恒正 *)
Lemma cst_nseq_pos : forall (a : Q), Qlt 0 a -> forall n : nat, Qlt 0 (cst_nseq a n).
Proof.
  intros a Ha n. induction n as [| m IH].
  - apply (Qlt_le_trans 0 1 (a + 1)).
    + exact Z.lt_0_1.
    + pose proof (Qplus_le_compat 0 a 1 1
                    (Qlt_le_weak 0 a Ha) (Qle_refl 1)) as Hle.
      change (0 + 1)%Q with 1 in Hle. exact Hle.
  - change (cst_nseq a (Datatypes.S m))
      with ((cst_nseq a m + a / cst_nseq a m) / 2).
    assert (Hax : Qlt 0 (a / cst_nseq a m)).
    { apply (Qmult_lt_0_compat a (/ cst_nseq a m)); [exact Ha|].
      apply Qinv_lt_0_compat. exact IH. }
    assert (Hsum : Qlt 0 (cst_nseq a m + a / cst_nseq a m))
      by (apply (Qplus_lt_compat 0 (cst_nseq a m) 0 (a / cst_nseq a m));
          assumption).
    apply (Qmult_lt_0_compat (cst_nseq a m + a / cst_nseq a m) (/ 2));
      [exact Hsum | exact Z.lt_0_1].
Qed.

(* 残差恒非负：0 <= x_n² − a *)
Lemma cst_d_nonneg : forall (a : Q), Qlt 0 a -> forall n : nat,
  Qle 0 (cst_nseq a n * cst_nseq a n - a).
Proof.
  intros a Ha n. induction n as [| m IH].
  - change (cst_nseq a 0) with (a + 1).
    assert (Hid0 : ((a + 1) * (a + 1) - a) == (a * a + a + 1)) by ring.
    rewrite Hid0.
    apply Qlt_le_weak.
    apply (Qplus_lt_compat 0 (a * a + a) 0 1).
    + apply (Qplus_lt_compat 0 (a * a) 0 a).
      * apply (Qmult_lt_0_compat a a); exact Ha.
      * exact Ha.
    + exact Z.lt_0_1.
  - change (cst_nseq a (Datatypes.S m) * cst_nseq a (Datatypes.S m) - a)
      with (((cst_nseq a m + a / cst_nseq a m) / 2)
            * ((cst_nseq a m + a / cst_nseq a m) / 2) - a).
    assert (Hx0 : ~ (cst_nseq a m == 0))
      by (apply q_neq_of_lt; apply cst_nseq_pos; exact Ha).
    assert (H2n : ~ (2 == 0)) by (unfold Qeq; discriminate).
    assert (Hx2p : Qlt 0 (cst_nseq a m * cst_nseq a m))
      by (apply (Qmult_lt_0_compat (cst_nseq a m) (cst_nseq a m));
          apply cst_nseq_pos; exact Ha).
    assert (H4p : Qlt 0 (4 * (cst_nseq a m * cst_nseq a m)))
      by (apply (Qmult_lt_0_compat 4 (cst_nseq a m * cst_nseq a m));
          [exact (proj1 (Z.ltb_lt 0 4) eq_refl) | exact Hx2p]).
    assert (H4n : ~ (4 * (cst_nseq a m * cst_nseq a m) == 0))
      by (apply q_neq_of_lt; exact H4p).
    assert (Hid : ((cst_nseq a m + a / cst_nseq a m) / 2)
                  * ((cst_nseq a m + a / cst_nseq a m) / 2) - a
                == (cst_nseq a m * cst_nseq a m - a)
                   * (cst_nseq a m * cst_nseq a m - a)
                   / (4 * (cst_nseq a m * cst_nseq a m)))
      by (field; repeat split; assumption).
    rewrite Hid.
    apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat; [exact IH | exact IH].
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact H4p.
Qed.

(* 上界：x_n² − a <= x_n² *)
Lemma cst_d_le_x2 : forall (a : Q), Qlt 0 a -> forall n : nat,
  Qle (cst_nseq a n * cst_nseq a n - a) (cst_nseq a n * cst_nseq a n).
Proof.
  intros a Ha n.
  assert (Hneg : Qle (- a) 0).
  { pose proof (Qopp_le_compat 0 a (Qlt_le_weak 0 a Ha)) as H.
    change (- 0)%Q with 0 in H. exact H. }
  assert (Hstep : Qle (cst_nseq a n * cst_nseq a n + (- a))
                      (cst_nseq a n * cst_nseq a n + 0))
    by (apply (Qplus_le_compat (cst_nseq a n * cst_nseq a n)
                               (cst_nseq a n * cst_nseq a n) (- a) 0);
        [apply Qle_refl | exact Hneg]).
  assert (Hz0 : (cst_nseq a n * cst_nseq a n + 0)%Q
                == (cst_nseq a n * cst_nseq a n)) by ring.
  rewrite Hz0 in Hstep. exact Hstep.
Qed.

(* Newton 精确衰减：d_{n+1} <= d_n·(1/4)——二次收敛的几何系数化 *)
Lemma cst_d_step_le : forall (a : Q), Qlt 0 a -> forall n : nat,
  Qle (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
      ((cst_nseq a n * cst_nseq a n - a) * (1 / 4)).
Proof.
  intros a Ha n.
  pose proof (cst_nseq_pos a Ha n) as Hxp.
  assert (Hx0 : ~ (cst_nseq a n == 0)) by (apply q_neq_of_lt; exact Hxp).
  assert (H2n : ~ (2 == 0)) by (unfold Qeq; discriminate).
  pose proof (cst_d_nonneg a Ha n) as Hd.
  pose proof (cst_d_le_x2 a Ha n) as Hdle.
  assert (Hx2p : Qlt 0 (cst_nseq a n * cst_nseq a n))
    by (apply (Qmult_lt_0_compat (cst_nseq a n) (cst_nseq a n));
        apply cst_nseq_pos; exact Ha).
  assert (H4p : Qlt 0 (4 * (cst_nseq a n * cst_nseq a n)))
    by (apply (Qmult_lt_0_compat 4 (cst_nseq a n * cst_nseq a n));
        [exact (proj1 (Z.ltb_lt 0 4) eq_refl) | exact Hx2p]).
  assert (H4n : ~ (4 * (cst_nseq a n * cst_nseq a n) == 0))
    by (apply q_neq_of_lt; exact H4p).
  change (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
    with (((cst_nseq a n + a / cst_nseq a n) / 2)
          * ((cst_nseq a n + a / cst_nseq a n) / 2) - a).
  assert (Hid : ((cst_nseq a n + a / cst_nseq a n) / 2)
                * ((cst_nseq a n + a / cst_nseq a n) / 2) - a
              == (cst_nseq a n * cst_nseq a n - a)
                 * (cst_nseq a n * cst_nseq a n - a)
                 / (4 * (cst_nseq a n * cst_nseq a n)))
    by (field; repeat split; assumption).
  rewrite Hid.
  assert (Hinv0 : Qle 0 (/ (4 * (cst_nseq a n * cst_nseq a n))))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H4p).
  assert (Hdd : Qle ((cst_nseq a n * cst_nseq a n - a)
                     * (cst_nseq a n * cst_nseq a n - a))
                    ((cst_nseq a n * cst_nseq a n - a)
                     * (cst_nseq a n * cst_nseq a n))).
  { pose proof (Qmult_le_compat_r (cst_nseq a n * cst_nseq a n - a)
                    (cst_nseq a n * cst_nseq a n)
                    (cst_nseq a n * cst_nseq a n - a) Hdle Hd) as H1.
    rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n)
                        (cst_nseq a n * cst_nseq a n - a)) in H1.
    exact H1. }
  eapply (Qle_trans _ ((cst_nseq a n * cst_nseq a n - a)
                       * (cst_nseq a n * cst_nseq a n)
                       * (/ (4 * (cst_nseq a n * cst_nseq a n))))).
  - apply (Qmult_le_compat_r _ _ (/ (4 * (cst_nseq a n * cst_nseq a n))) Hdd Hinv0).
  - assert (E2 : (cst_nseq a n * cst_nseq a n - a) * (cst_nseq a n * cst_nseq a n)
                 * (/ (4 * (cst_nseq a n * cst_nseq a n)))
                 == (cst_nseq a n * cst_nseq a n - a) * (1 / 4))
      by (field; repeat split; assumption).
    rewrite E2. apply Qle_refl.
Qed.

(* 几何率：d_m <= d0·(1/4)^m *)
Lemma cst_d_geo : forall (a : Q), Qlt 0 a -> forall m : nat,
  Qle (cst_nseq a m * cst_nseq a m - a)
      ((cst_nseq a 0 * cst_nseq a 0 - a) * q_pow (1 / 4) m).
Proof.
  intros a Ha m. induction m as [| m IH].
  - rewrite Qmult_1_r. apply Qle_refl.
  - eapply (Qle_trans _
             ((cst_nseq a m * cst_nseq a m - a) * (1 / 4))).
    + apply (cst_d_step_le a Ha m).
    + change (q_pow (1 / 4) (Datatypes.S m)) with ((1 / 4) * q_pow (1 / 4) m).
      assert (Hr4 : ((1 / 4) * q_pow (1 / 4) m)
                    == (q_pow (1 / 4) m * (1 / 4))) by ring.
      rewrite Hr4.
      rewrite (Qmult_assoc (cst_nseq a 0 * cst_nseq a 0 - a)
                           (q_pow (1 / 4) m) (1 / 4)).
      apply (Qmult_le_compat_r _ _ (1 / 4) IH).
      unfold Qle. simpl. exact (proj1 (Z.leb_le 0 1) eq_refl).
Qed.

(* (1/4)^m 关于 m 反单调（NatLe 面） *)
Lemma cst_pow14_anti : forall k m : nat, NatLe k m ->
  Qle (q_pow (1 / 4) m) (q_pow (1 / 4) k).
Proof.
  intros k m. revert k. induction m as [| m IH]; intros k Hkm.
  - pose proof (NatLe_drop k 0%nat Hkm) as Hk0.
    assert (Hk : k = 0%nat)
      by exact (Nat.le_antisymm k 0%nat Hk0 (Nat.le_0_l k)).
    rewrite Hk. apply Qle_refl.
  - destruct (Nat.eq_dec (Datatypes.S m) k) as [Heq | Hne].
    + rewrite Heq. apply Qle_refl.
    + assert (Hkm' : (k <= m)%nat).
      { pose proof (NatLe_drop k (Datatypes.S m) Hkm) as Hle.
        destruct (proj1 (Nat.lt_eq_cases k (Datatypes.S m)) Hle) as [Hlt | Heq].
        - exact (proj1 (Nat.lt_succ_r k m) Hlt).
        - exfalso. apply Hne. exact (eq_sym Heq). }
      eapply (Qle_trans _ (q_pow (1 / 4) m)).
      * change (q_pow (1 / 4) (Datatypes.S m)) with ((1 / 4) * q_pow (1 / 4) m).
        eapply (Qle_trans _ (1 * q_pow (1 / 4) m)%Q).
        -- apply (Qmult_le_compat_r (1 / 4) 1 (q_pow (1 / 4) m)).
           ++ unfold Qle. simpl.
              exact (Z.le_trans 1 2 4 (Z.le_succ_diag_r 1)
                       (Z.le_trans 2 3 4 (Z.le_succ_diag_r 2)
                          (Z.le_succ_diag_r 3))).
           ++ apply q_pow_nonneg. unfold Qle. simpl.
              exact (proj1 (Z.leb_le 0 1) eq_refl).
        -- rewrite (Qmult_1_l (q_pow (1 / 4) m)). apply Qle_refl.
      * apply (IH k (NatLe_lift k m Hkm')).
Qed.

(* (1/2)^m 关于 m 反单调（NatLe 面）——arch_decay 依存形 *)
Lemma cst_pow12_anti : forall k m : nat, NatLe k m ->
  Qle (q_pow (1 / 2) m) (q_pow (1 / 2) k).
Proof.
  intros k m. revert k. induction m as [| m IH]; intros k Hkm.
  - pose proof (NatLe_drop k 0%nat Hkm) as Hk0.
    assert (Hk : k = 0%nat)
      by exact (Nat.le_antisymm k 0%nat Hk0 (Nat.le_0_l k)).
    rewrite Hk. apply Qle_refl.
  - destruct (Nat.eq_dec (Datatypes.S m) k) as [Heq | Hne].
    + rewrite Heq. apply Qle_refl.
    + assert (Hkm' : (k <= m)%nat).
      { pose proof (NatLe_drop k (Datatypes.S m) Hkm) as Hle.
        destruct (proj1 (Nat.lt_eq_cases k (Datatypes.S m)) Hle) as [Hlt | Heq].
        - exact (proj1 (Nat.lt_succ_r k m) Hlt).
        - exfalso. apply Hne. exact (eq_sym Heq). }
      eapply (Qle_trans _ (q_pow (1 / 2) m)).
      * change (q_pow (1 / 2) (Datatypes.S m)) with ((1 / 2) * q_pow (1 / 2) m).
        eapply (Qle_trans _ (1 * q_pow (1 / 2) m)%Q).
        -- apply (Qmult_le_compat_r (1 / 2) 1 (q_pow (1 / 2) m)).
           ++ unfold Qle. simpl. exact (Z.le_succ_diag_r 1).
           ++ apply q_pow_nonneg. unfold Qle. simpl.
              exact (proj1 (Z.leb_le 0 1) eq_refl).
        -- rewrite (Qmult_1_l (q_pow (1 / 2) m)). apply Qle_refl.
      * apply (IH k (NatLe_lift k m Hkm')).
Qed.

(* Newton 衰减（1/2 形）：d_{n+1} <= d_n·(1/2)——step_le 的弱化消耗形 *)
Lemma cst_d_step_le12 : forall (a : Q), Qlt 0 a -> forall n : nat,
  Qle (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
      ((cst_nseq a n * cst_nseq a n - a) * (1 / 2)).
Proof.
  intros a Ha n.
  eapply (Qle_trans _ ((cst_nseq a n * cst_nseq a n - a) * (1 / 4))).
  - apply (cst_d_step_le a Ha n).
  - rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n - a) (1 / 4)).
    rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n - a) (1 / 2)).
    apply (Qmult_le_compat_r (1 / 4) (1 / 2) (cst_nseq a n * cst_nseq a n - a)).
    + unfold Qle. simpl.
      exact (Z.le_trans 2 3 4 (Z.le_succ_diag_r 2) (Z.le_succ_diag_r 3)).
    + apply cst_d_nonneg; exact Ha.
Qed.

(* 几何率（1/2 形）：d_m <= d0·(1/2)^m——与 arch_decay 依存形精确配 *)
Lemma cst_d_geo12 : forall (a : Q), Qlt 0 a -> forall m : nat,
  Qle (cst_nseq a m * cst_nseq a m - a)
      ((cst_nseq a 0 * cst_nseq a 0 - a) * q_pow (1 / 2) m).
Proof.
  intros a Ha m. induction m as [| m IH].
  - rewrite Qmult_1_r. apply Qle_refl.
  - eapply (Qle_trans _ ((cst_nseq a m * cst_nseq a m - a) * (1 / 2))).
    + apply (cst_d_step_le12 a Ha m).
    + change (q_pow (1 / 2) (Datatypes.S m)) with ((1 / 2) * q_pow (1 / 2) m).
      assert (Hr2 : ((1 / 2) * q_pow (1 / 2) m)
                    == (q_pow (1 / 2) m * (1 / 2))) by ring.
      rewrite Hr2.
      rewrite (Qmult_assoc (cst_nseq a 0 * cst_nseq a 0 - a)
                           (q_pow (1 / 2) m) (1 / 2)).
      apply (Qmult_le_compat_r _ _ (1 / 2) IH).
      unfold Qle. simpl. exact (proj1 (Z.leb_le 0 1) eq_refl).
Qed.

(* S2 主定理：Newton 序列显式率（Q 层，N 显式可提取；
   N := arch_decay 见证后继——库内已证几何衰减件系数化依存） *)
Theorem cst_newton_rate : forall (a eps : Q), QltT 0 a -> QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    QltT (Qabs (cst_nseq a m * cst_nseq a m - a)) eps).
Proof.
  intros a eps Ha Heps.
  pose proof (QltT_to_Qlt 0 a Ha) as Haq.
  pose proof (cst_d_nonneg a Haq 0) as Hd0.
  destruct (arch_decay (cst_nseq a 0 * cst_nseq a 0 - a) eps
             (Qle_to_QleT' _ _ Hd0) Heps) as [t Hdec].
  exists (Datatypes.S t).
  intros m Hm.
  pose proof (cst_d_geo12 a Haq m) as Hgeo.
  pose proof (cst_d_nonneg a Haq m) as Hdm.
  assert (Hd0q : Qle 0 (cst_nseq a 0 * cst_nseq a 0 - a))
    by (apply (cst_d_nonneg a Haq 0)).
  assert (Hpow : Qle (q_pow (1 / 2) m) (q_pow (1 / 2) (Datatypes.S t)))
    by (apply (cst_pow12_anti (Datatypes.S t) m); exact Hm).
  assert (Hchain : Qle (cst_nseq a m * cst_nseq a m - a)
                       ((cst_nseq a 0 * cst_nseq a 0 - a)
                        * q_pow (1 / 2) (Datatypes.S t))).
  { eapply (Qle_trans _ ((cst_nseq a 0 * cst_nseq a 0 - a)
                         * q_pow (1 / 2) m)).
    - exact Hgeo.
    - rewrite (Qmult_comm (cst_nseq a 0 * cst_nseq a 0 - a)
                          (q_pow (1 / 2) m)).
      rewrite (Qmult_comm (cst_nseq a 0 * cst_nseq a 0 - a)
                          (q_pow (1 / 2) (Datatypes.S t))).
      apply (Qmult_le_compat_r _ _ (cst_nseq a 0 * cst_nseq a 0 - a) Hpow Hd0q). }
  assert (Habs : Qabs (cst_nseq a m * cst_nseq a m - a)
               == cst_nseq a m * cst_nseq a m - a)
    by (apply Qabs_pos; exact Hdm).
  apply Qlt_to_QltT. rewrite Habs.
  apply (Qle_lt_trans (cst_nseq a m * cst_nseq a m - a)
                      ((cst_nseq a 0 * cst_nseq a 0 - a)
                       * q_pow (1 / 2) (Datatypes.S t)) eps Hchain
                      (QltT_to_Qlt _ _ Hdec)).
Qed.

(* ============================================================ *)
(* S3：范数迁移——bcoef 嵌入面 ‖x_m² − bcoef q‖ < eps（任意 BA）   *)
(* ============================================================ *)

Lemma cst_bae_opp_one : forall (B : BanachAlg),
  @bae B (@bplus B (@bopp B (@bone B)) (@bone B)) (@bzero B).
Proof.
  intros B.
  eapply @bae_trans.
  { exact (@bplus_comm B (@bopp B (@bone B)) (@bone B)). }
  exact (@bplus_opp B (@bone B)).
Qed.

Lemma cst_bmult_opp_r : forall (B : BanachAlg) (x : @BA B),
  @bae B (@bmult B x (@bopp B (@bone B))) (@bopp B x).
Proof.
  intros B x.
  apply (@bopp_unique B (@bmult B x (@bopp B (@bone B))) x).
  eapply @bae_trans.
  { apply (@bplus_wd_r B x (@bmult B x (@bone B))
             (@bmult B x (@bopp B (@bone B)))
             (@bae_sym B _ _ (@bmult_one_r B x))). }
  eapply @bae_trans.
  { apply (@bae_sym B _ _ (@bdistrib_l B x (@bopp B (@bone B)) (@bone B))). }
  eapply @bae_trans.
  { apply (@bmult_wd B x (@bplus B (@bopp B (@bone B)) (@bone B)) x (@bzero B)
             (@bae_refl B x) (cst_bae_opp_one B)). }
  exact (@bmult_zero B x).
Qed.

Lemma cst_bcoef_mone : forall (B : BanachAlg),
  @bae B (@bcoef B (- 1)) (@bopp B (@bone B)).
Proof.
  intros B.
  assert (Hplus : @bae B (@bplus B (@bcoef B 1) (@bcoef B (- 1))) (@bzero B)).
  { eapply @bae_trans.
    { exact (@bcoef_plus B 1 (- 1)). }
    eapply @bae_trans.
    { apply (@bcoef_wd B (1 + (- 1))%Q 0%Q). exact (Qeq_refl 0). }
    exact (@bcoef_zero B). }
  pose proof (@bae_trans B _ _ _
    (@bplus_wd_l B (@bone B) (@bcoef B 1) (@bcoef B (- 1))
                 (@bae_sym B _ _ (@bcoef_one B))) Hplus) as H2.
  assert (H3 : @bae B (@bone B) (@bopp B (@bcoef B (- 1))))
    by (apply (@bopp_unique B (@bone B) (@bcoef B (- 1))); exact H2).
  apply (@bae_sym B _ _).
  eapply @bae_trans.
  { exact (@bopp_wd B (@bone B) (@bopp B (@bcoef B (- 1))) H3). }
  apply (@bae_sym B _ _ (@cst_bae_bopp_invol B (@bcoef B (- 1)))).
Qed.

Lemma cst_bcoef_opp : forall (B : BanachAlg) (q : Q),
  @bae B (@bcoef B (- q)) (@bopp B (@bcoef B q)).
Proof.
  intros B q.
  eapply @bae_trans.
  { apply (@bcoef_wd B (- q) (q * (- 1))). ring. }
  eapply @bae_trans.
  { exact (@bcoef_mult B q (- 1)). }
  eapply @bae_trans.
  { apply (@bmult_wd B (@bcoef B q) (@bcoef B (- 1))
             (@bcoef B q) (@bopp B (@bone B))
             (@bae_refl B (@bcoef B q)) (cst_bcoef_mone B)). }
  exact (cst_bmult_opp_r B (@bcoef B q)).
Qed.

(* S3 主定理：任意 BanachAlg 中标量正元的 Newton 序列范数收敛
   （显式 N 逐字继承自 Q 层引擎——保底件二的代数面结果） *)
Theorem cst_newton_alg : forall (B : BanachAlg) (q eps : Q),
  QltT 0 q -> QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    QltT (@bnorm B (@bplus B
             (@bmult B (@bcoef B (cst_nseq q m)) (@bcoef B (cst_nseq q m)))
             (@bopp B (@bcoef B q)))) eps).
Proof.
  intros B q eps Hq Heps.
  destruct (cst_newton_rate q eps Hq Heps) as [N HN].
  exists N. intros m Hm.
  specialize (HN m Hm).
  pose proof (@bcoef_mult B (cst_nseq q m) (cst_nseq q m)) as H1.
  pose proof (@bae_sym B _ _ (cst_bcoef_opp B q)) as H2s.
  assert (Hfin : @bae B
    (@bplus B (@bmult B (@bcoef B (cst_nseq q m)) (@bcoef B (cst_nseq q m)))
              (@bopp B (@bcoef B q)))
    (@bcoef B (cst_nseq q m * cst_nseq q m - q))).
  { eapply @bae_trans.
    { apply (@bplus_wd_l B (@bmult B (@bcoef B (cst_nseq q m))
                                       (@bcoef B (cst_nseq q m)))
               (@bcoef B (cst_nseq q m * cst_nseq q m))
               (@bopp B (@bcoef B q)) (@bae_sym B _ _ H1)). }
    eapply @bae_trans.
    { apply (@bplus_wd_r B (@bopp B (@bcoef B q)) (@bcoef B (- q))
               (@bcoef B (cst_nseq q m * cst_nseq q m)) H2s). }
    exact (@bcoef_plus B (cst_nseq q m * cst_nseq q m) (- q)). }
  assert (Hnorm : QeqT
    (@bnorm B (@bplus B
        (@bmult B (@bcoef B (cst_nseq q m)) (@bcoef B (cst_nseq q m)))
        (@bopp B (@bcoef B q))))
    (Qabs (cst_nseq q m * cst_nseq q m - q))).
  { pose proof (@bnorm_wd B _ _ Hfin) as Hw.
    pose proof (@bnorm_coef_qeq B (cst_nseq q m * cst_nseq q m - q)) as Hc.
    apply qeq_imp_qeqT.
    apply (Qeq_trans _ _ _ (qeqT_imp_qeq _ _ Hw)).
    exact Hc. }
  apply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ Hnorm)). exact HN.
Qed.

(* ============================================================ *)
(* S4：正元锥（sigT 见证形，LPO 规避）+ star 交换引理              *)
(* ============================================================ *)

(* 正元锥：a 正 iff 存在见证 b 使 a = star b · b（C* 锥标准形） *)
Definition cst_pos (C : CStarAlg) (a : @BA (@cbase C)) : Set :=
  sigT (fun b : @BA (@cbase C) =>
    @bae (@cbase C) (@bmult (@cbase C) (@cst_star C b) b) a).

(* 锥成员恒自伴：star a == a *)
Lemma cst_pos_selfadj : forall (C : CStarAlg) (a : @BA (@cbase C)),
  cst_pos C a -> @bae (@cbase C) (@cst_star C a) a.
Proof.
  intros C a [b Hb].
  eapply @bae_trans.
  { exact (@bae_sym (@cbase C)
             (@cst_star C (@bmult (@cbase C) (@cst_star C b) b))
             (@cst_star C a)
             (@cst_star_wd C (@bmult (@cbase C) (@cst_star C b) b) a Hb)). }
  eapply @bae_trans.
  { exact (@cst_star_mult C (@cst_star C b) b). }
  eapply @bae_trans.
  { exact (@bmult_wd (@cbase C) (@cst_star C b)
             (@cst_star C (@cst_star C b))
             (@cst_star C b) b
             (@bae_refl (@cbase C) (@cst_star C b)) (@cst_star_star C b)). }
  exact Hb.
Qed.

(* star 保锥：a 正 ⟹ star a 正（自伴 + 见证 b 逐字继承） *)
Lemma cst_star_preserves_pos : forall (C : CStarAlg) (a : @BA (@cbase C)),
  cst_pos C a -> cst_pos C (@cst_star C a).
Proof.
  intros C a [b Hb].
  exists b. apply (@bae_sym (@cbase C) _ _).
  eapply @bae_trans.
  { exact (cst_pos_selfadj C a (existT _ b Hb)). }
  exact (@bae_sym (@cbase C) (@bmult (@cbase C) (@cst_star C b) b) a Hb).
Qed.

(* star 残差交换：a 自伴时 star(x·x − a) == star x · star x − a
   （Newton 残差在对合下的交换面——star 与 sqrt 的交换引理级形） *)
Lemma cst_star_residual : forall (C : CStarAlg) (a x : @BA (@cbase C)),
  @bae (@cbase C) (@cst_star C a) a ->
  @bae (@cbase C)
    (@cst_star C (@bplus (@cbase C) (@bmult (@cbase C) x x)
                         (@bopp (@cbase C) a)))
    (@bplus (@cbase C) (@bmult (@cbase C) (@cst_star C x) (@cst_star C x))
                      (@bopp (@cbase C) a)).
Proof.
  intros C a x Hsa.
  eapply @bae_trans.
  { exact (@cst_star_add C (@bmult (@cbase C) x x) (@bopp (@cbase C) a)). }
  eapply @bae_trans.
  { apply (@bplus_wd_l (@cbase C)
             (@cst_star C (@bmult (@cbase C) x x))
             (@bmult (@cbase C) (@cst_star C x) (@cst_star C x))
             (@cst_star C (@bopp (@cbase C) a)) (@cst_star_mult C x x)). }
  apply (@bplus_wd_r (@cbase C) (@cst_star C (@bopp (@cbase C) a))
           (@bopp (@cbase C) a)
           (@bmult (@cbase C) (@cst_star C x) (@cst_star C x))).
  eapply @bae_trans.
  - exact (cst_star_opp C a).
  - exact (@bopp_wd (@cbase C) (@cst_star C a) a Hsa).
Qed.

(* ============================================================ *)
(* 显式假设（对称登记，不落承认件）：                                 *)
(*   ① 一般正元 a 的代数内 Newton 序列需反演面（x_n 可逆 + 与 a   *)
(*      交换的 sigT 见证）；本件 S3 结果 bcoef 嵌入面，一般元经    *)
(*      Neumann 级数反演 + C* 恒等式收紧属下一级。                *)
(*   ② x∞² == a 的 baé 闭合形：需 Q 列完备性破缺（INST3 判定在     *)
(*      案）或序列直接取极限面；本件以显式率邻域形结果。           *)
(*   ③ 锥上加法封闭/序面（Löwner）= 构造性谱定理开放带，对称显式假设。 *)
(*   ④ star 幂交换：需同元幂交换引理，归纳可证，下一注册波补装。   *)
(* ============================================================ *)

Print Assumptions cst_bae_bopp_invol.
