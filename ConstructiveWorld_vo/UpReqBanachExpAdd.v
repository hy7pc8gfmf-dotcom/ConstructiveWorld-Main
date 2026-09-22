(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bxadd_qmin_le_r（原 L43，1 句玩具证）                                *)
(*   bxadd_qmin_le_l（原 L40，1 句玩具证）                                *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ========================================================================= *)
(* UpReqBanachExpAdd.v — ConstructiveWorld 路径 B S3 总装席（BASM）          *)
(* 件名前缀 bxadd_。承重墙：极限乘法连续性 bxadd_bmult_lim。                  *)
(* 路线：e^a·e^b 与 e^(a+b) 同为 (esp n a·esp n b) 型序列的极限，             *)
(*       经 bxdef_exp_spec 邻域面 + bxadd_bmult_lim 夹逼。                   *)
(* 纯构造性：Set 层、零 Prop 泄露、零经典公理、零 lia（本环 lia 不吃 Q）。     *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachInvPre.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.

(* ============================================================ *)
(* 一、Q 层工具件（eps 记账与 Qmin 便利面；全手工，零 lia）       *)
(* ============================================================ *)

Lemma bxadd_qpos_plus_one : forall u : Q, Qle 0 u -> QltT 0 (u + 1)%Q.
Proof.
  intros u Hu. apply Qlt_to_QltT.
  apply (Qle_lt_trans 0 (u + 0)%Q (u + 1)%Q).
  - rewrite Qplus_0_r. exact Hu.
  - apply (proj2 (Qplus_lt_r 0%Q 1%Q u)).
    exact (QltT_to_Qlt 0%Q 1%Q qltT_0_1).
Qed.

Lemma bxadd_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (Qmin a b).
Proof.
  intros a b Ha Hb.
  destruct (Q.min_dec a b) as [Hq | Hq].
  - exact (qeq_ltT a (Qmin a b) (Qeq_sym (Qmin a b) a Hq) Ha).
  - exact (qeq_ltT b (Qmin a b) (Qeq_sym (Qmin a b) b Hq) Hb).
Qed.

Lemma bxadd_qmin_le_l : forall a b : Q, Qle (Qmin a b) a.
Proof. exact Q.le_min_l. Qed.

Lemma bxadd_qmin_le_r : forall a b : Q, Qle (Qmin a b) b.
Proof. exact Q.le_min_r. Qed.

(* 除法上界迁移：0 < b 且 a ≤ b·c ⟹ a/b ≤ c *)
Lemma bxadd_div_mul_le : forall a b c : Q,
  QltT 0 b -> Qle a (b * c) -> Qle (a / b) c.
Proof.
  intros a b c Hb Hac.
  assert (Hneq : ~ (b == 0)%Q)
    by (intro Hzz; exact (qltT_not_eq_zero b Hb Hzz)).
  apply (proj1 (Qmult_le_r (a / b) c b (QltT_to_Qlt 0%Q b%Q Hb))).
  assert (Eab : ((a / b) * b == a)%Q).
  { unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ b) b).
    rewrite (Qmult_inv_r b Hneq). rewrite Qmult_1_r. ring. }
  rewrite (Qmult_comm b c) in Hac. rewrite Eab. exact Hac.
Qed.

(* 三四折严格：0 < e ⟹ 3·(e/4) < e *)
Lemma bxadd_three_quarter_lt : forall e : Q, QltT 0 e -> QltT (3 * (e / 4))%Q e.
Proof.
  intros e He. apply Qlt_to_QltT.
  assert (H4 : ~ (4 == 0)%Q)
    by (intro Hfz; exact (qltT_not_eq_zero 4%Q qltT_0_4 Hfz)).
  assert (H4pos : Qlt 0 4%Q) by exact (QltT_to_Qlt 0%Q 4%Q qltT_0_4).
  assert (H34 : Qlt 3 4).
  { assert (H34T : QltT 3 4) by reflexivity.
    exact (QltT_to_Qlt 3%Q 4%Q H34T). }
  assert (Hstep : (3 * e < e * 4)%Q).
  { assert (Ecomm : (e * 4 == 4 * e)%Q) by ring.
    rewrite Ecomm. exact (Qmult_lt_compat_r 3 4 e (QltT_to_Qlt 0%Q e%Q He) H34). }
  apply (proj1 (Qmult_lt_r (3 * (e / 4)) e 4%Q H4pos)).
  assert (Eprod : ((3 * (e / 4)) * 4 == 3 * e)%Q).
  { unfold Qdiv. rewrite <- !Qmult_assoc. rewrite (Qmult_comm (/ 4) 4).
    rewrite (Qmult_inv_r 4 H4). rewrite Qmult_1_r. ring. }
  rewrite Eprod. exact Hstep.
Qed.

(* ============================================================ *)
(* 二、Banach 面：负元分配与差式拼接（bae 等词面）               *)
(* ============================================================ *)

(* z·(−x) ≡ −(z·x)（一般形；binv_mult_opp_r 只有 x·(−x) 特形） *)
Lemma bxadd_bmult_opp_r : forall (B : BanachAlg) (x z : (@BA B)),
  @bae B (@bmult B z (@bopp B x)) (@bopp B (@bmult B z x)).
Proof.
  intros B x z.
  apply (@bopp_unique B (@bmult B z (@bopp B x)) (@bmult B z x)).
  eapply bae_trans.
  - apply (@bae_sym B). exact (@bdistrib_l B z (@bopp B x) x).
  - eapply bae_trans.
    + apply (@bmult_wd B z (@bplus B (@bopp B x) x) z (@bzero B)).
      * apply (@bae_refl B).
      * apply (@bae_trans B _ (@bplus B x (@bopp B x)) _).
        -- exact (@bplus_comm B (@bopp B x) x).
        -- exact (@bplus_opp B x).
    + exact (@bmult_zero B z).
Qed.

(* x·z − y·z ≡ (x−y)·z *)
Lemma bxadd_bminus_mult_l : forall (B : BanachAlg) (x y z : (@BA B)),
  @bae B (@bplus B (@bmult B x z) (@bopp B (@bmult B y z)))
         (@bmult B (@bplus B x (@bopp B y)) z).
Proof.
  intros B x y z.
  eapply bae_trans.
  - apply (@bplus_wd_r B (@bopp B (@bmult B y z)) (@bmult B (@bopp B y) z)
             (@bmult B x z)).
    apply (@bae_sym B). exact (binv_bmult_opp_l B y z).
  - apply (@bae_sym B). exact (@bdistrib_r B x (@bopp B y) z).
Qed.

(* z·x − z·y ≡ z·(x−y) *)
Lemma bxadd_bminus_mult_r : forall (B : BanachAlg) (x y z : (@BA B)),
  @bae B (@bplus B (@bmult B z x) (@bopp B (@bmult B z y)))
         (@bmult B z (@bplus B x (@bopp B y))).
Proof.
  intros B x y z.
  eapply bae_trans.
  - apply (@bplus_wd_r B (@bopp B (@bmult B z y)) (@bmult B z (@bopp B y))
             (@bmult B z x)).
    apply (@bae_sym B). exact (bxadd_bmult_opp_r B y z).
  - apply (@bae_sym B). exact (@bdistrib_l B z x (@bopp B y)).
Qed.

(* (−a) + (a + b) ≡ b（中间消去） *)
Lemma bxadd_opp_plus_cancel : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bplus B (@bopp B a) (@bplus B a b)) b.
Proof.
  intros B a b.
  eapply bae_trans.
  - exact (@bplus_assoc B (@bopp B a) a b).
  - eapply bae_trans.
    + apply (@bplus_wd B).
      * apply (@bae_trans B _ (@bplus B a (@bopp B a)) _).
        -- exact (@bplus_comm B (@bopp B a) a).
        -- exact (@bplus_opp B a).
      * apply (@bae_refl B).
    + exact (@bplus_zero_l B b).
Qed.

(* x·y − lx·ly ≡ (x·y − lx·y) + (lx·y − lx·ly)（两点插角） *)
Lemma bxadd_prod_diff_join : forall (B : BanachAlg) (x y lx ly : (@BA B)),
  @bae B (@bplus B (@bmult B x y) (@bopp B (@bmult B lx ly)))
         (@bplus B (@bplus B (@bmult B x y) (@bopp B (@bmult B lx y)))
                  (@bplus B (@bmult B lx y) (@bopp B (@bmult B lx ly)))).
Proof.
  intros B x y lx ly.
  apply (@bae_sym B).
  eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bplus_assoc B (@bmult B x y) (@bopp B (@bmult B lx y))
             (@bplus B (@bmult B lx y) (@bopp B (@bmult B lx ly)))).
  - apply (@bplus_wd_r B
             (@bplus B (@bopp B (@bmult B lx y))
                (@bplus B (@bmult B lx y) (@bopp B (@bmult B lx ly))))
             (@bopp B (@bmult B lx ly)) (@bmult B x y)).
    exact (bxadd_opp_plus_cancel B (@bmult B lx y) (@bopp B (@bmult B lx ly))).
Qed.

(* u ≡ (u − l) + l（元素自拼接，供范数次可加消费） *)
Lemma bxadd_esp_join : forall (B : BanachAlg) (u l : (@BA B)),
  @bae B u (@bplus B (@bplus B u (@bopp B l)) l).
Proof.
  intros B u l.
  eapply bae_trans.
  - apply (@bae_sym B). exact (@bplus_zero B u).
  - apply (@bae_trans B (@bplus B u (@bzero B))
             (@bplus B u (@bplus B (@bopp B l) l))
             (@bplus B (@bplus B u (@bopp B l)) l)).
    + apply (@bplus_wd_r B (@bzero B) (@bplus B (@bopp B l) l) u).
      apply (@bae_trans B (@bzero B) (@bplus B l (@bopp B l))
               (@bplus B (@bopp B l) l)).
      * apply (@bae_sym B). exact (@bplus_opp B l).
      * apply (@bae_sym B). exact (@bplus_comm B (@bopp B l) l).
    + exact (@bplus_assoc B u (@bopp B l) l).
Qed.

(* ============================================================ *)
(* 三、承重墙主件：极限乘法连续性                                 *)
(*   x_n → lx 且 y_n → ly ⟹ x_n·y_n → lx·ly（blim 邻域形）      *)
(*   构造性三角展开：‖x_n y_n − lx ly‖ ≤ ‖x_n−lx‖‖y_n‖          *)
(*     + ‖lx‖‖y_n−ly‖；eb = min(eps/4,1) 封顶 + 除式换界记账。   *)
(* ============================================================ *)

Lemma bxadd_bmult_lim : forall (B : BanachAlg) (x y : nat -> (@BA B))
                                     (lx ly : (@BA B)),
  blim B x lx -> blim B y ly ->
  blim B (fun n : nat => @bmult B (x n) (y n)) (@bmult B lx ly).
Proof.
  intros B x y lx ly Hx Hy eps Heps.
  set (nlx := @bnorm B lx).
  set (nly := @bnorm B ly).
  assert (Hlx0 : Qle 0 nlx) by (apply QleT'_to_Qle; exact (@bnorm_pos B lx)).
  assert (Hly0 : Qle 0 nly) by (apply QleT'_to_Qle; exact (@bnorm_pos B ly)).
  assert (Hlx1 : Qle nlx (nlx + 1)%Q)
    by (exact (Qle_plus_nonneg_r nlx 1%Q Qle_0_1)).
  assert (Hly1 : Qle nly (nly + 1)%Q)
    by (exact (Qle_plus_nonneg_r nly 1%Q Qle_0_1)).
  assert (Hcx0 : QltT 0 (nlx + 1)%Q) by (apply bxadd_qpos_plus_one; exact Hlx0).
  assert (Hcy0 : QltT 0 (nly + 1)%Q) by (apply bxadd_qpos_plus_one; exact Hly0).
  assert (Hcxne : ~ ((nlx + 1) == 0)%Q)
    by (intro Hzz; exact (qltT_not_eq_zero (nlx + 1)%Q Hcx0 Hzz)).
  assert (Hcyne : ~ ((nly + 1) == 0)%Q)
    by (intro Hzz; exact (qltT_not_eq_zero (nly + 1)%Q Hcy0 Hzz)).
  assert (Hone_cx : Qle 1 (nlx + 1)%Q).
  { assert (Ec : ((nlx + 1) == 1 + nlx)%Q) by ring.
    rewrite Ec. exact (Qle_plus_nonneg_r 1%Q nlx Hlx0). }
  assert (Hone_cy : Qle 1 (nly + 1)%Q).
  { assert (Ec : ((nly + 1) == 1 + nly)%Q) by ring.
    rewrite Ec. exact (Qle_plus_nonneg_r 1%Q nly Hly0). }
  assert (He4 : QltT 0 (eps / 4)%Q)
    by (apply qltT_div_pos; [exact Heps | exact qltT_0_4]).
  set (eb := Qmin (eps / 4) 1%Q).
  assert (Heb0 : QltT 0 eb) by (apply bxadd_qmin_pos; [exact He4 | exact qltT_0_1]).
  assert (Heb1 : Qle eb 1%Q) by (apply bxadd_qmin_le_r).
  assert (Heb4 : Qle eb (eps / 4)%Q) by (apply bxadd_qmin_le_l).
  assert (Heb_bx : Qle eb (nlx + 1)%Q).
  { apply (Qle_trans eb 1%Q (nlx + 1)%Q); [exact Heb1 | exact Hone_cx]. }
  assert (Heb_by : Qle eb (nly + 1)%Q).
  { apply (Qle_trans eb 1%Q (nly + 1)%Q); [exact Heb1 | exact Hone_cy]. }
  assert (He1d : QltT 0 (eb / (nly + 1))%Q)
    by (apply qltT_div_pos; [exact Heb0 | exact Hcy0]).
  assert (Hcx1 : Qle (eb / (nlx + 1)) 1%Q).
  { apply (bxadd_div_mul_le eb (nlx + 1) 1%Q).
    - exact Hcx0.
    - assert (E1 : ((nlx + 1) * 1 == nlx + 1)%Q) by ring.
      rewrite E1. exact Heb_bx. }
  assert (Hcy1 : Qle (eb / (nly + 1)) 1%Q).
  { apply (bxadd_div_mul_le eb (nly + 1) 1%Q).
    - exact Hcy0.
    - assert (E1 : ((nly + 1) * 1 == nly + 1)%Q) by ring.
      rewrite E1. exact Heb_by. }
  (* 从 blim 取两路见证（eps 半径：Qmin(eb/(‖ly‖+1),1) 与 eb/(‖lx‖+1)） *)
  assert (Hpos1 : QltT 0 (Qmin (eb / (nly + 1)) 1%Q))
    by (apply bxadd_qmin_pos; [exact He1d | exact qltT_0_1]).
  assert (Hpos2 : QltT 0 (eb / (nlx + 1))%Q)
    by (apply qltT_div_pos; [exact Heb0 | exact Hcx0]).
  destruct (Hx (Qmin (eb / (nly + 1)) 1%Q) Hpos1) as [Nx HNx].
  destruct (Hy (eb / (nlx + 1))%Q Hpos2) as [Ny HNy].
  exists (Nat.max Nx Ny). intros n Hnmax.
  apply NatLe_drop in Hnmax.
  assert (Hn1 : (Nx <= n)%nat) by lia.
  assert (Hn2 : (Ny <= n)%nat) by lia.
  specialize (HNx n (NatLe_lift Nx n Hn1)).
  specialize (HNy n (NatLe_lift Ny n Hn2)).
  (* ‖y_n‖ < eb/(‖lx‖+1) + ‖ly‖ *)
  assert (Hyn : QltT (@bnorm B (y n)) (eb / (nlx + 1) + nly)%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd B (y n)
              (@bplus B (@bplus B (y n) (@bopp B ly)) ly)
              (bxadd_esp_join B (y n) ly)))).
    apply (qleT'_ltT_ltT _ (@bnorm B (@bplus B (y n) (@bopp B ly))
                              + @bnorm B ly)%Q _).
    - exact (@bnorm_plus B (@bplus B (y n) (@bopp B ly)) ly).
    - exact (qltT_plus_leT'_ltT
               (@bnorm B (@bplus B (y n) (@bopp B ly)))
               (eb / (nlx + 1)) (@bnorm B ly) (@bnorm B ly)
               HNy (qleT'_refl (@bnorm B ly))). }
  (* 第一项：‖x_n·y_n − lx·y_n‖ < 2·eb *)
  assert (Hd1 : QltT (@bnorm B (@bplus B (@bmult B (x n) (y n))
                                (@bopp B (@bmult B lx (y n)))))
                     (2 * eb)%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd B
        (@bplus B (@bmult B (x n) (y n)) (@bopp B (@bmult B lx (y n))))
        (@bmult B (@bplus B (x n) (@bopp B lx)) (y n))
        (bxadd_bminus_mult_l B (x n) lx (y n))))).
    (* ‖(x_n−lx)·y_n‖ ≤ e1·‖y_n‖ ≤ (eb/(‖ly‖+1))·‖y_n‖ < (eb/(‖ly‖+1))·(eb/(‖lx‖+1)+‖ly‖) ≤ 2eb *)
    assert (Hstep1 : QleT' (@bnorm B (@bmult B (@bplus B (x n) (@bopp B lx)) (y n)))
                           ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm B (y n))%Q).
    { apply (qleT'_trans _ (@bnorm B (@bplus B (x n) (@bopp B lx))
                              * @bnorm B (y n))%Q _).
      - exact (@bnorm_mult B (@bplus B (x n) (@bopp B lx)) (y n)).
      - apply Qle_to_QleT'.
        exact (Qmult_le_compat_r
                 (@bnorm B (@bplus B (x n) (@bopp B lx)))
                 (Qmin (eb / (nly + 1)) 1%Q) (@bnorm B (y n))
                 (QleT'_to_Qle (@bnorm B (@bplus B (x n) (@bopp B lx)))
                    (Qmin (eb / (nly + 1)) 1%Q)
                    (qltT_leT' (@bnorm B (@bplus B (x n) (@bopp B lx)))
                       (Qmin (eb / (nly + 1)) 1%Q) HNx))
                 (QleT'_to_Qle 0%Q (@bnorm B (y n))
                    (@bnorm_pos B (y n)))). }
    assert (Hstep2 : QleT' ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm B (y n))%Q
                           ((eb / (nly + 1)) * @bnorm B (y n))%Q).
    { apply Qle_to_QleT'.
      exact (Qmult_le_compat_r (Qmin (eb / (nly + 1)) 1%Q)
               (eb / (nly + 1)) (@bnorm B (y n))
               (bxadd_qmin_le_l (eb / (nly + 1)) 1%Q)
               (QleT'_to_Qle 0%Q (@bnorm B (y n))
                  (@bnorm_pos B (y n)))). }
    assert (Hsum : Qle (eb / (nlx + 1) + nly)
                       ((nly + 1) + (nly + 1))%Q).
    { apply (Qle_trans (eb / (nlx + 1) + nly) (1%Q + (nly + 1))
              ((nly + 1) + (nly + 1))).
      - exact (Qplus_le_compat (eb / (nlx + 1)) 1%Q nly (nly + 1)
                 Hcx1 Hly1).
      - exact (Qplus_le_compat 1%Q (nly + 1) (nly + 1) (nly + 1)
                 Hone_cy (Qle_refl (nly + 1))). }
    apply (qleT'_ltT_ltT _ ((eb / (nly + 1)) * @bnorm B (y n))%Q _).
    - exact (qleT'_trans
               (@bnorm B (@bmult B (@bplus B (x n) (@bopp B lx)) (y n)))
               ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm B (y n))
               ((eb / (nly + 1)) * @bnorm B (y n))
               Hstep1 Hstep2).
    - assert (Hcomm : QleT' ((eb / (nly + 1)) * @bnorm B (y n))
                             (@bnorm B (y n) * (eb / (nly + 1)))).
      { apply qeq_leT'.
        exact (Qmult_comm (eb / (nly + 1)) (@bnorm B (y n))). }
      assert (Hringc : QleT' ((eb / (nlx + 1) + nly) * (eb / (nly + 1)))
                              (2 * eb)%Q).
      { apply Qle_to_QleT'.
        apply (Qle_trans ((eb / (nlx + 1) + nly) * (eb / (nly + 1)))
                (((nly + 1) + (nly + 1)) * (eb / (nly + 1))) (2 * eb)).
        - exact (Qmult_le_compat_r (eb / (nlx + 1) + nly)
                   ((nly + 1) + (nly + 1)) (eb / (nly + 1)) Hsum
                   (QleT'_to_Qle 0%Q (eb / (nly + 1))
                      (qltT_leT' 0%Q (eb / (nly + 1))
                         (qltT_div_pos eb (nly + 1) Heb0 Hcy0)))).
        - apply qeq_imp_qle.
          unfold Qdiv. rewrite Qmult_plus_distr_l.
          rewrite !(Qmult_comm (nly + 1) (eb * / (nly + 1))).
          rewrite <- !Qmult_assoc.
          rewrite !(Qmult_comm (/ (nly + 1)) (nly + 1)).
          rewrite (Qmult_inv_r (nly + 1) Hcyne). rewrite !Qmult_1_r.
          ring. }
      exact (qleT'_ltT_ltT ((eb / (nly + 1)) * @bnorm B (y n))
               (@bnorm B (y n) * (eb / (nly + 1))) (2 * eb)
               Hcomm
               (qltT_leT'_ltT (@bnorm B (y n) * (eb / (nly + 1)))
                  ((eb / (nlx + 1) + nly) * (eb / (nly + 1))) (2 * eb)
                  (qltT_mult_ltT_compat_r (@bnorm B (y n))
                     (eb / (nlx + 1) + nly) (eb / (nly + 1))
                     (qltT_div_pos eb (nly + 1) Heb0 Hcy0) Hyn)
                  Hringc)). }
  (* 第二项：‖lx·y_n − lx·ly‖ < eb *)
  assert (Hd2 : QltT (@bnorm B (@bplus B (@bmult B lx (y n))
                                (@bopp B (@bmult B lx ly))))
                     eb%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd B
        (@bplus B (@bmult B lx (y n)) (@bopp B (@bmult B lx ly)))
        (@bmult B lx (@bplus B (y n) (@bopp B ly)))
        (bxadd_bminus_mult_r B (y n) ly lx)))).
    (* ‖lx·(y_n−ly)‖ ≤ ‖lx‖·‖y_n−ly‖ ≤ (‖lx‖+1)·‖y_n−ly‖ < (‖lx‖+1)·(eb/(‖lx‖+1)) == eb *)
    assert (Hstep1 : QleT' (@bnorm B (@bmult B lx (@bplus B (y n) (@bopp B ly))))
                           (nlx * @bnorm B (@bplus B (y n) (@bopp B ly)))%Q).
    { exact (@bnorm_mult B lx (@bplus B (y n) (@bopp B ly))). }
    assert (Hstep2 : QleT' (nlx * @bnorm B (@bplus B (y n) (@bopp B ly)))%Q
                           ((nlx + 1) * @bnorm B (@bplus B (y n) (@bopp B ly)))%Q).
    { apply Qle_to_QleT'.
      exact (Qmult_le_compat_r nlx (nlx + 1)
               (@bnorm B (@bplus B (y n) (@bopp B ly))) Hlx1
               (QleT'_to_Qle 0%Q (@bnorm B (@bplus B (y n) (@bopp B ly)))
                  (@bnorm_pos B (@bplus B (y n) (@bopp B ly))))). }
    apply (qleT'_ltT_ltT _
             ((nlx + 1) * @bnorm B (@bplus B (y n) (@bopp B ly)))%Q _).
    - exact (qleT'_trans
               (@bnorm B (@bmult B lx (@bplus B (y n) (@bopp B ly))))
               (nlx * @bnorm B (@bplus B (y n) (@bopp B ly)))
               ((nlx + 1) * @bnorm B (@bplus B (y n) (@bopp B ly)))
               Hstep1 Hstep2).
    - assert (Hcx : ((nlx + 1) * (eb / (nlx + 1)) == eb)%Q).
      { unfold Qdiv.
        rewrite (Qmult_comm (nlx + 1) (eb * / (nlx + 1))).
        rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ (nlx + 1)) (nlx + 1)).
        rewrite (Qmult_inv_r (nlx + 1) Hcxne). rewrite Qmult_1_r.
        reflexivity. }
      set (w := @bnorm B (@bplus B (y n) (@bopp B ly))) in *.
      assert (Hcomm1 : QleT' ((nlx + 1) * w) (w * (nlx + 1))).
      { apply qeq_leT'. exact (Qmult_comm (nlx + 1) w). }
      assert (Hcx2 : ((eb / (nlx + 1)) * (nlx + 1) == eb)%Q).
      { unfold Qdiv. rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ (nlx + 1)) (nlx + 1)).
        rewrite (Qmult_inv_r (nlx + 1) Hcxne). rewrite Qmult_1_r.
        reflexivity. }
      exact (qleT'_ltT_ltT ((nlx + 1) * w) (w * (nlx + 1)) eb Hcomm1
               (qltT_eq_compat_r eb ((eb / (nlx + 1)) * (nlx + 1))
                  (w * (nlx + 1))
                  (Qeq_sym ((eb / (nlx + 1)) * (nlx + 1)) eb Hcx2)
                  (qltT_mult_ltT_compat_r w (eb / (nlx + 1)) (nlx + 1)
                     Hcx0 HNy))).
  }
  (* 拼装：‖x_n y_n − lx ly‖ ≤ ‖d1‖+‖d2‖ < 3eb ≤ 3·(eps/4) < eps *)
  assert (Hjoin : QleT' (@bnorm B (@bplus B (@bmult B (x n) (y n))
                                    (@bopp B (@bmult B lx ly))))
                        (((@bnorm B (@bplus B (@bmult B (x n) (y n))
                                     (@bopp B (@bmult B lx (y n)))))
                            + @bnorm B (@bplus B (@bmult B lx (y n))
                                          (@bopp B (@bmult B lx ly)))))%Q).
  { eapply (QeqT_Qle_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd B
      (@bplus B (@bmult B (x n) (y n)) (@bopp B (@bmult B lx ly)))
      (@bplus B (@bplus B (@bmult B (x n) (y n)) (@bopp B (@bmult B lx (y n))))
               (@bplus B (@bmult B lx (y n)) (@bopp B (@bmult B lx ly))))
      (bxadd_prod_diff_join B (x n) (y n) lx ly)))).
    exact (@bnorm_plus B
             (@bplus B (@bmult B (x n) (y n)) (@bopp B (@bmult B lx (y n))))
             (@bplus B (@bmult B lx (y n)) (@bopp B (@bmult B lx ly)))). }
  assert (Hthree : QltT (@bnorm B (@bplus B (@bmult B (x n) (y n))
                                     (@bopp B (@bmult B lx (y n))))
                          + @bnorm B (@bplus B (@bmult B lx (y n))
                                     (@bopp B (@bmult B lx ly))))%Q
                        (2 * eb + eb)%Q).
  { exact (qltT_plus_ltT
             (@bnorm B (@bplus B (@bmult B (x n) (y n))
                          (@bopp B (@bmult B lx (y n))))) (2 * eb)
             (@bnorm B (@bplus B (@bmult B lx (y n))
                          (@bopp B (@bmult B lx ly)))) eb
             Hd1 Hd2). }
  assert (Hfin : QltT (2 * eb + eb) eps).
  { apply (qleT'_ltT_ltT _ (3 * (eps / 4))%Q).
    - apply Qle_to_QleT'.
      apply (Qle_trans (2 * eb + eb) (eb * 3) (3 * (eps / 4))).
      + apply qeq_imp_qle. ring.
      + apply (Qle_trans (eb * 3) ((eps / 4) * 3) (3 * (eps / 4))).
        * exact (Qmult_le_compat_r eb (eps / 4) 3%Q Heb4
                   (QleT'_to_Qle 0%Q 3%Q (qltT_leT' 0%Q 3%Q qltT_0_3))).
        * apply qeq_imp_qle. exact (Qmult_comm (eps / 4) 3).
    - exact (bxadd_three_quarter_lt eps Heps). }
  apply (qleT'_ltT_ltT
           (@bnorm B (@bplus B (@bmult B (x n) (y n))
                        (@bopp B (@bmult B lx ly))))
           ((@bnorm B (@bplus B (@bmult B (x n) (y n))
                          (@bopp B (@bmult B lx (y n)))))
              + @bnorm B (@bplus B (@bmult B lx (y n))
                             (@bopp B (@bmult B lx ly))))%Q).
  - exact Hjoin.
  - exact (qltT_leT'_ltT
             (((@bnorm B (@bplus B (@bmult B (x n) (y n))
                          (@bopp B (@bmult B lx (y n)))))
                 + @bnorm B (@bplus B (@bmult B lx (y n))
                                (@bopp B (@bmult B lx ly)))))%Q
              (2 * eb + eb) eps Hthree (qltT_leT' (2 * eb + eb) eps Hfin)).
Qed.

(* ============================================================ *)
(* 四、即刻推论：e^a·e^b 是 (esp n a·esp n b) 序列的极限           *)
(*   （总装左半；与 bxdef_exp_spec (a+b) 右半对接位）              *)
(* ============================================================ *)

Corollary bxadd_esp_prod_blim : forall (B : BanachAlg) (a b : (@BA B)),
  blim B (fun n : nat => @bmult B (exp_series_partial B a n)
                                  (exp_series_partial B b n))
         (@bmult B (bxdef_exp B a) (bxdef_exp B b)).
Proof.
  intros B a b.
  apply (bxadd_bmult_lim B
           (fun n : nat => exp_series_partial B a n)
           (fun n : nat => exp_series_partial B b n)).
  - exact (bxdef_exp_spec B a).
  - exact (bxdef_exp_spec B b).
Qed.
