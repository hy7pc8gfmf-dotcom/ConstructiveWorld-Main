(* ============================================================ *)
(* ToyR 玩具证替换件 —— T268 台账席 战役包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bxuq_lim_uniq（原 L185，4 句轻证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBanachLimUniq.v —— 席UNQ：极限唯一性席（20260913，路径 B）  *)
(* ============================================================ *)
(* 使命：把 bxce_sep 反可分性字段（UpReqBanachClassExt.v 二波）     *)
(*   兑现为 blim 意义下的极限唯一性 bxuq_lim_uniq，给 S3/S4        *)
(*   闭合（EXPADD2/装配席）递钥匙。                                *)
(* 遗留来源：BASM 报告「类缺反可分性字段 ⟹ 极限唯一性不可导出       *)
(*   ⟹ 等式形到顶」（bxadd_exp_add 双缺口之一）；B25 卡同因。      *)
(* 承重依存：bxadd_bmult_lim（UpReqBanachExpAdd.v 保底件）经        *)
(*   bxuq_prod_lim_joint 演示与唯一性合流。                        *)
(* 红线自审：                                                      *)
(*   - 语句面全 Set 层：主件返回型 bae；Q 层 Prop（Qlt/Qle）仅作     *)
(*     引擎内衬，与冻结件 UpReqBanachExp.v 同纪律；                 *)
(*   - 纯构造性：vernac 禁用面零命中、零经典逻辑；                    *)
(*   - 只 Require 上游件，禁改冻结类与席位件。                      *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachExpAdd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Q 层工具件（Prop 引擎内衬，语句面不落 Prop）                     *)
(* ============================================================ *)

(* 常量非零：2 ≠ 0（Qmult_inv_r 前提喂料） *)
Lemma bxuq_2_neq_0 : ~ (2 == 0)%Q.
Proof.
  intros Hz. vm_compute in Hz. discriminate.
Qed.

(* 半径正性：0 <T e ⟹ 0 <T e/2（检验 q3 验证形） *)
Lemma bxuq_half_pos : forall e : Q, QltT 0 e -> QltT 0 (e / 2).
Proof.
  intros e H.
  assert (Hm : (e / 2 * 2)%Q == e%Q).
  { unfold Qdiv.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (Qinv 2) 2).
    rewrite (Qmult_inv_r 2 bxuq_2_neq_0).
    apply Qmult_1_r. }
  apply Qlt_to_QltT.
  apply (proj1 (Qmult_lt_r 0 (e / 2) 2 (QltT_to_Qlt 0 2 qltT_0_2))).
  rewrite Qmult_0_l.
  setoid_replace (e / 2 * 2)%Q with e%Q by (exact Hm).
  exact (QltT_to_Qlt 0 e H).
Qed.

(* 半和等式：e/2 + e/2 == e（检验 q2 验证形；Qdiv 须显式 unfold） *)
Lemma bxuq_half_sum_eq : forall e : Q, (e / 2 + e / 2)%Q == e%Q.
Proof.
  intros e.
  unfold Qdiv.
  rewrite <- (Qmult_plus_distr_l e e (Qinv 2)).
  assert (Hee : (e + e)%Q == (2 * e)%Q) by ring.
  rewrite Hee.
  rewrite <- Qmult_assoc.
  rewrite (Qmult_comm 2 (e * Qinv 2)%Q).
  rewrite <- Qmult_assoc.
  rewrite (Qmult_comm (Qinv 2) 2).
  rewrite (Qmult_inv_r 2 bxuq_2_neq_0).
  apply Qmult_1_r.
Qed.

(* 半径求和：x < e/2 且 y < e/2 ⟹ x + y < e（检验 q6 验证形） *)
Lemma bxuq_sum_half_lt : forall x y e : Q,
  Qlt x (e / 2) -> Qlt y (e / 2) -> Qlt (x + y) e.
Proof.
  intros x y e Hx Hy.
  assert (Hs : (e / 2 + e / 2)%Q == e%Q) by (apply bxuq_half_sum_eq).
  assert (H1 : (x + y < e / 2 + e / 2)%Q)
    by (apply Qplus_lt_compat; assumption).
  rewrite Hs in H1.
  exact H1.
Qed.

(* ============================================================ *)
(* Banach 加法群工具件（B : BanachAlg 泛型，不依存 Ext 字段）        *)
(* ============================================================ *)

(* 加零转等：bae (a + (-b)) 0 ⟹ bae a b（bopp_unique 双步） *)
Lemma bxuq_add_opp_zero_eq : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bplus B a (@bopp B b)) (@bzero B) -> @bae B a b.
Proof.
  intros B a b H.
  eapply bae_trans.
  - exact (@bopp_unique B a (@bopp B b) H).
  - apply (@bae_sym B).
    exact (@bopp_unique B b (@bopp B b) (@bplus_opp B b)).
Qed.

(* 差拆：a - c == (a - b) + (b - c)（三角不等式的代数前提） *)
Lemma bxuq_diff_split : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B (@bplus B a (@bopp B c))
    (@bplus B (@bplus B a (@bopp B b)) (@bplus B b (@bopp B c))).
Proof.
  intros B a b c.
  assert (H1 : @bae B (@bplus B (@bopp B b) b) (@bzero B)).
  { exact (@bae_trans B _ _ _ (@bplus_comm B (@bopp B b) b)
                        (@bplus_opp B b)). }
  assert (H3 : @bae B (@bplus B (@bopp B b) (@bplus B b (@bopp B c)))
                      (@bopp B c)).
  { eapply bae_trans.
    { exact (@bplus_assoc B (@bopp B b) b (@bopp B c)). }
    eapply bae_trans.
    { exact (@bplus_wd_l B (@bplus B (@bopp B b) b) (@bzero B)
                          (@bopp B c) H1). }
    exact (bplus_zero_l B (@bopp B c)). }
  assert (H4 : @bae B (@bplus B a (@bplus B (@bopp B b)
                                       (@bplus B b (@bopp B c))))
                      (@bplus B a (@bopp B c))).
  { exact (@bplus_wd_r B _ _ a H3). }
  eapply bae_trans.
  { exact (@bae_sym B _ _ H4). }
  exact (@bplus_assoc B a (@bopp B b) (@bplus B b (@bopp B c))).
Qed.

(* 差取负：a - b ≡ -(b - a)（blim 给出 u−l 形、拆项代数给 l1−u 形的换向桥；
   由 diff_split 取 a:=a,c:=a 的特款 + bopp_unique 两步合成） *)
Lemma bxuq_diff_opp : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bplus B a (@bopp B b))
         (@bopp B (@bplus B b (@bopp B a))).
Proof.
  intros B a b.
  apply (@bopp_unique B (@bplus B a (@bopp B b))
                       (@bplus B b (@bopp B a))).
  eapply bae_trans.
  { exact (@bae_sym B _ _ (bxuq_diff_split B a b a)). }
  exact (@bplus_opp B a).
Qed.

(* ============================================================ *)
(* 小范数主引理：双极限 ⟹ 差范数任意小（纯三角 + Q 核算，泛型）       *)
(* ============================================================ *)

Lemma bxuq_lim_diff_small : forall (B : BanachAlg) (u : nat -> (@BA B))
    (l1 l2 : (@BA B)),
  blim B u l1 -> blim B u l2 ->
  forall eps : Q, QltT 0 eps ->
  QltT (@bnorm B (@bplus B l1 (@bopp B l2))) eps.
Proof.
  intros B u l1 l2 H1 H2 eps Heps.
  assert (He2 : QltT 0 (eps / 2)%Q) by (apply bxuq_half_pos; exact Heps).
  destruct (H1 (eps / 2)%Q He2) as [N1 HN1].
  destruct (H2 (eps / 2)%Q He2) as [N2 HN2].
  assert (Ha : QltT (@bnorm B (@bplus B (u (Nat.max N1 N2))
                                       (@bopp B l1))) (eps / 2)%Q).
  { exact (HN1 (Nat.max N1 N2) (NatLe_lift _ _ (Nat.le_max_l N1 N2))). }
  assert (Hb : QltT (@bnorm B (@bplus B (u (Nat.max N1 N2))
                                       (@bopp B l2))) (eps / 2)%Q).
  { exact (HN2 (Nat.max N1 N2) (NatLe_lift _ _ (Nat.le_max_r N1 N2))). }
  (* blim 见证为 u−l 形；拆项代数为 l1−u 形——经 diff_opp + bnorm_opp 换向
     （Id 面 rewrite 于 QltT 目标内，BASM 先例形） *)
  assert (Hal : QltT (@bnorm B (@bplus B l1
                                 (@bopp B (u (Nat.max N1 N2)))))
                     (eps / 2)%Q).
  { pose proof (@bnorm_wd B _ _ (bxuq_diff_opp B l1 (u (Nat.max N1 N2)))) as HWd.
    eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HWd)).
    rewrite (@bnorm_opp B (@bplus B (u (Nat.max N1 N2)) (@bopp B l1))).
    exact Ha. }
  (* ‖d‖ ≤T ‖R2‖ ≤T ‖l1-u‖ + ‖u-l2‖ <T eps（全程 QleT'/QltT 桥，Id 面
     rewrite 只在 QleT' 目标内——检验 q1a/q1b 已证结论：Qlt 目标内不可用） *)
  eapply qleT'_ltT_ltT.
  - eapply qleT'_trans.
    + eapply (QeqT_Qle_bool_cong _ _ _
                (qeqT_sym_hw _ _ (@bnorm_wd B _ _
                  (bxuq_diff_split B l1 (u (Nat.max N1 N2)) l2)))).
      apply qleT'_refl.
    + exact (@bnorm_plus B (@bplus B l1 (@bopp B (u (Nat.max N1 N2))))
                           (@bplus B (u (Nat.max N1 N2)) (@bopp B l2))).
  - apply Qlt_to_QltT.
    apply (bxuq_sum_half_lt
             (@bnorm B (@bplus B l1 (@bopp B (u (Nat.max N1 N2)))))
             (@bnorm B (@bplus B (u (Nat.max N1 N2)) (@bopp B l2)))).
    + exact (QltT_to_Qlt _ _ Hal).
    + exact (QltT_to_Qlt _ _ Hb).
Qed.

(* ============================================================ *)
(* 主件：blim 极限唯一性（反可分性字段的兑现位）                     *)
(* ============================================================ *)

Theorem bxuq_lim_uniq : forall (E : BanachAlgExt) (u : nat -> (@BA (@bxce_base E)))
    (l1 l2 : (@BA (@bxce_base E))),
  blim (@bxce_base E) u l1 -> blim (@bxce_base E) u l2 ->
  @bae (@bxce_base E) l1 l2.
Proof.
  intros E u l1 l2 H1 H2.
  apply (@bxuq_add_opp_zero_eq (@bxce_base E) l1 l2).
  apply (@bxce_sep E (@bplus (@bxce_base E) l1 (@bopp (@bxce_base E) l2))).
  exact (bxuq_lim_diff_small (@bxce_base E) u l1 l2 H1 H2).
Qed.

(* ============================================================ *)
(* S3 钥匙演示：极限乘法（bxadd_bmult_lim）+ 唯一性合流——             *)
(* 部分和乘积列的两个极限必 bae 相等（EXPADD2/装配席依存位）          *)
(* ============================================================ *)

Corollary bxuq_prod_lim_joint : forall (E : BanachAlgExt)
    (a b : (@BA (@bxce_base E)))
    (la lb l : (@BA (@bxce_base E))),
  blim (@bxce_base E) (fun n : nat =>
    exp_series_partial (@bxce_base E) a n) la ->
  blim (@bxce_base E) (fun n : nat =>
    exp_series_partial (@bxce_base E) b n) lb ->
  blim (@bxce_base E) (fun n : nat =>
    @bmult (@bxce_base E) (exp_series_partial (@bxce_base E) a n)
                          (exp_series_partial (@bxce_base E) b n)) l ->
  @bae (@bxce_base E) l (@bmult (@bxce_base E) la lb).
Proof.
  intros E a b la lb l Ha Hb Hp.
  apply (bxuq_lim_uniq E
           (fun n : nat =>
              @bmult (@bxce_base E)
                (exp_series_partial (@bxce_base E) a n)
                (exp_series_partial (@bxce_base E) b n))).
  - exact Hp.
  - exact (bxadd_bmult_lim (@bxce_base E)
             (fun n : nat => exp_series_partial (@bxce_base E) a n)
             (fun n : nat => exp_series_partial (@bxce_base E) b n)
             la lb Ha Hb).
Qed.

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bxuq_lim_uniq.
