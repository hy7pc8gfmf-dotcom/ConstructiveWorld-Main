(* ==========================================================================)
   UpReqBanachInstPre —— S02 Real 载体上的 BanachAlgPre 具体实例；同域语句面
   使命：本件形式化S02 Real 载体上的 BanachAlgPre 具体实例。
   本件并载：路径 B exp_neg 元素化件；bxem_mult/bxem_one 定义、bxem_qeqT_cong_mult（QeqT 乘法外推）与 bxem_mult_assoc/one_l/；语句面弱化形下游的强形式恢复件；bxce_sep 字段定理化（Banach 完全等式面） 使命：「exp(0) 完全等式面」未消解项的转化件——bxce_sep 字段。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, UpReqBanachExp, UpReqBanachExpDef, QArith.QArith, QArith.Qabs, Arith.Arith
     Lia, UpReqBanachInstB, ZArith.ZArith, Extraction, UpReqBanachExpBasic, UpReqNormConv, UpReqBanachCauchyD, UpReqBanachInst,
     UpReqBanachInstReal, UpReqBanachClassExt, UpReqBanachLimUniq。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 路径 B exp_neg 元素化件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S2 主件：exp_neg 元素（bxdef_exp 于 bopp a 实例化）+ 收敛规格   *)
(* ============================================================ *)

(* exp_neg 元素定义：exp 在加法逆元处的取值（一行直构）。          *)
Definition bxn_exp_neg (B : BanachAlg) (a : (@BA B)) : (@BA B) :=
  bxdef_exp B (@bopp B a).

(* 收敛规格（零新证转引）：exp_neg 是 bopp a 处级数部分和的极限。  *)
Lemma bxn_exp_neg_spec : forall (B : BanachAlg) (a : (@BA B)),
  blim B (fun n => exp_series_partial B (@bopp B a) n) (bxn_exp_neg B a).
Proof.
  intros B a. exact (bxdef_exp_spec B (@bopp B a)).
Qed.

(* 收敛规格的 eps/N 展开形（下游免再 destruct 的便利面，同 B25）。 *)
Lemma bxn_exp_neg_spec_eps : forall (B : BanachAlg) (a : (@BA B)) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall n : nat,
    NatLe N n ->
    QltT (@bnorm B (@bplus B (exp_series_partial B (@bopp B a) n)
                              (@bopp B (bxn_exp_neg B a)))) eps).
Proof.
  intros B a eps Heps. exact (bxdef_exp_spec_eps B (@bopp B a) eps Heps).
Qed.

(* ============================================================ *)
(* S1 系列面：bopp a 处级数的形态定形                              *)
(* （Class 无 bneg 类字段——(−1)^k 载体取 bmult (bopp bone) 路线：  *)
(*   偶次 bae bone、奇次 bae (bopp bone)，符号交错定位。）         *)
(* ============================================================ *)

(* 负单位平方：bmult (bopp bone) (bopp bone) bae bone。            *)
(* （bopp_unique 于「单位逆 + 乘积 ≡ 0」：分配展开 + 单位清边。）   *)
Lemma bxn_mone_sq : forall (B : BanachAlg),
  @bae B (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B))) (@bone B).
Proof.
  intros B.
  eapply bae_trans.
  { apply (@bopp_unique B
        (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
        (@bopp B (@bone B))).
    (* bplus (乘积) (bopp bone) bae bzero *)
    eapply bae_trans.
    { exact (@bplus_comm B (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                           (@bopp B (@bone B))). }
    eapply bae_trans.
    { exact (@bae_sym B _ _
        (@bae_trans B _ _ _
          (@bdistrib_l B (@bopp B (@bone B)) (@bone B) (@bopp B (@bone B)))
          (@bplus_wd B (@bmult B (@bopp B (@bone B)) (@bone B))
                       (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                       (@bopp B (@bone B))
                       (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                       (@bmult_one_r B (@bopp B (@bone B)))
                       (@bae_refl B (@bmult B (@bopp B (@bone B))
                                              (@bopp B (@bone B))))))). }
    eapply bae_trans.
    { exact (@bmult_wd B (@bopp B (@bone B))
                         (@bplus B (@bone B) (@bopp B (@bone B)))
                         (@bopp B (@bone B)) (@bzero B)
                         (@bae_refl B (@bopp B (@bone B)))
                         (@bplus_opp B (@bone B))). }
    exact (@bmult_zero B (@bopp B (@bone B))).
  }
  exact (@bae_sym B _ _
    (@bopp_unique B (@bone B) (@bopp B (@bone B)) (@bplus_opp B (@bone B)))).
Qed.

(* 双步自然数（偶次序载体；库内自定义，避开 stdlib 名依赖）。      *)
Fixpoint bxn_double (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | Datatypes.S m => Datatypes.S (Datatypes.S (bxn_double m))
  end.

(* 符号交错偶次面：bpow (bopp bone) (bxn_double k) bae bone。      *)
Lemma bxn_series_mone_even : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bone B)) (bxn_double k)) (@bone B).
Proof.
  intros B k. induction k as [| j IHj].
  - exact (@bae_refl B (@bone B)).
  - change (bxn_double (Datatypes.S j))
      with (Datatypes.S (Datatypes.S (bxn_double j))).
    change (bpow B (@bopp B (@bone B))
                   (Datatypes.S (Datatypes.S (bxn_double j))))
      with (@bmult B (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double j))
                               (@bopp B (@bone B)))
                     (@bopp B (@bone B))).
    eapply bae_trans.
    { exact (@bmult_wd B
          (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double j))
                   (@bopp B (@bone B)))
          (@bopp B (@bone B))
          (@bmult B (@bone B) (@bopp B (@bone B))) (@bopp B (@bone B))
          (@bmult_wd B (bpow B (@bopp B (@bone B)) (bxn_double j))
                       (@bopp B (@bone B))
                       (@bone B) (@bopp B (@bone B))
                       IHj (@bae_refl B (@bopp B (@bone B))))
          (@bae_refl B (@bopp B (@bone B)))). }
    eapply bae_trans.
    { exact (@bmult_wd B (@bmult B (@bone B) (@bopp B (@bone B)))
                        (@bopp B (@bone B))
                        (@bopp B (@bone B)) (@bopp B (@bone B))
                        (@bmult_one_l B (@bopp B (@bone B)))
                        (@bae_refl B (@bopp B (@bone B)))). }
    exact (bxn_mone_sq B).
Qed.

(* 符号交错奇次面：bpow (bopp bone) (S (bxn_double k))             *)
(*   bae (bopp bone)。                                            *)
Lemma bxn_series_mone_odd : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bone B)) (Datatypes.S (bxn_double k)))
        (@bopp B (@bone B)).
Proof.
  intros B k.
  change (bpow B (@bopp B (@bone B)) (Datatypes.S (bxn_double k)))
    with (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double k))
                   (@bopp B (@bone B))).
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bopp B (@bone B)) (bxn_double k))
                      (@bopp B (@bone B))
                      (@bone B) (@bopp B (@bone B))
                      (bxn_series_mone_even B k)
                      (@bae_refl B (@bopp B (@bone B)))). }
  exact (@bmult_one_l B (@bopp B (@bone B))).
Qed.

(* ============================================================ *)
(* S3 加分：范数面（S4 尾界复用）+ exp_neg(0) 邻域面               *)
(* ============================================================ *)

(* 范数面出口：‖bopp a‖ == ‖a‖（Class 字段具名引出，S4 尾界直引）。 *)
Lemma bxn_bnorm_opp : forall (B : BanachAlg) (a : (@BA B)),
  Id (@bnorm B (@bopp B a)) (@bnorm B a).
Proof.
  intros B a. exact (@bnorm_opp B a).
Qed.

(* 幂范数面：‖(bopp a)^k‖ ≤T ‖a‖^k（尾界在 bopp a 处同界复用）。   *)
Lemma bxn_bnorm_bpow_opp : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  QleT' (@bnorm B (bpow B (@bopp B a) k)) (q_pow (@bnorm B a) k).
Proof.
  intros B a k.
  rewrite <- (@bnorm_opp B a).
  exact (bnorm_bpow B (@bopp B a) k).
Qed.

(* 负零面：bopp bzero bae bzero（单位消 + 加法逆两步）。           *)
Lemma bxn_opp_bzero : forall (B : BanachAlg),
  @bae B (@bopp B (@bzero B)) (@bzero B).
Proof.
  intros B.
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_zero B (@bopp B (@bzero B)))). }
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_comm B (@bzero B) (@bopp B (@bzero B)))). }
  exact (@bplus_opp B (@bzero B)).
Qed.

(* 负零幂尾：bpow (bopp bzero) (S k) bae bzero。                   *)
Lemma bxn_bpow_opp_zero_tail : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bzero B)) (Datatypes.S k)) (@bzero B).
Proof.
  intros B k. induction k as [| j IHj].
  - change (bpow B (@bopp B (@bzero B)) (Datatypes.S 0%nat))
      with (@bmult B (@bone B) (@bopp B (@bzero B))).
    eapply bae_trans.
    { exact (@bmult_one_l B (@bopp B (@bzero B))). }
    exact (bxn_opp_bzero B).
  - change (bpow B (@bopp B (@bzero B)) (Datatypes.S (Datatypes.S j)))
      with (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S j))
                     (@bopp B (@bzero B))).
    eapply bae_trans.
    { exact (@bmult_wd B (bpow B (@bopp B (@bzero B)) (Datatypes.S j))
                        (@bopp B (@bzero B))
                        (@bzero B) (@bzero B)
                        IHj (bxn_opp_bzero B)). }
    exact (@bmult_zero B (@bzero B)).
Qed.

(* 负零级数项退化：负零幂 × 系数 bae bzero。                       *)
Lemma bxn_esp_term_opp_zero : forall (B : BanachAlg) (k : nat) (q : Q),
  @bae B (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S k))
                   (@bcoef B q))
        (@bzero B).
Proof.
  intros B k q.
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bopp B (@bzero B)) (Datatypes.S k))
                      (@bcoef B q)
                      (@bzero B) (@bcoef B q)
                      (bxn_bpow_opp_zero_tail B k)
                      (@bae_refl B (@bcoef B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm B q (@bzero B)). }
  exact (@bmult_zero B (@bcoef B q)).
Qed.

(* exp_neg(0) 部分和恒一：esp (bopp bzero) n bae bone。            *)
(* （对接 BXB 的 bxb_series_zero 同族面：负零处级数列同退化。）     *)
Lemma bxn_series_opp_zero : forall (B : BanachAlg) (n : nat),
  @bae B (exp_series_partial B (@bopp B (@bzero B)) n) (@bone B).
Proof.
  intros B n. induction n as [| m IHm].
  - change (exp_series_partial B (@bopp B (@bzero B)) 0%nat) with (@bone B).
    exact (@bae_refl B (@bone B)).
  - change (exp_series_partial B (@bopp B (@bzero B)) (Datatypes.S m))
      with (@bplus B (exp_series_partial B (@bopp B (@bzero B)) m)
              (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S m))
                        (@bcoef B (/ q_fact (Datatypes.S m))))).
    eapply bae_trans.
    { exact (@bplus_wd B (exp_series_partial B (@bopp B (@bzero B)) m)
                        (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S m))
                                  (@bcoef B (/ q_fact (Datatypes.S m))))
                        (@bone B) (@bzero B)
                        IHm
                        (bxn_esp_term_opp_zero B m
                           (/ q_fact (Datatypes.S m)))). }
    exact (@bplus_zero B (@bone B)).
Qed.

(* exp_neg(0) 极限邻域面：bone 与 exp_neg(bzero) 范数任意贴近。     *)
(* （完全等式面被「范数任意小推 bae bzero」接口位缺失挡住——         *)
(*   承上游件同源未消解项，不作无依据凑形。）                      *)
Lemma bxn_exp_neg_zero_close : forall (B : BanachAlg) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm B (@bplus B (@bone B)
                           (@bopp B (bxn_exp_neg B (@bzero B))))) eps.
Proof.
  intros B eps Heps.
  destruct (bxn_exp_neg_spec B (@bzero B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
  pose proof (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bopp B (@bzero B)) N)
                (@bopp B (bxn_exp_neg B (@bzero B))))
      (@bplus B (@bone B) (@bopp B (bxn_exp_neg B (@bzero B))))
      (@bplus_wd B (exp_series_partial B (@bopp B (@bzero B)) N)
                  (@bopp B (bxn_exp_neg B (@bzero B)))
                  (@bone B) (@bopp B (bxn_exp_neg B (@bzero B)))
                  (bxn_series_opp_zero B N)
                  (@bae_refl B (@bopp B (bxn_exp_neg B (@bzero B)))))) as HWn.
  exact (QeqT_Qlt_bool_cong _ _ eps HWn HN).
Qed.

(* ============================================================ *)
(* 未消解项申报（对称，不落承认件）：                              *)
(*   ① S4 可逆性本体（(e^a)^{-1}=e^{-a}）：需 exp_add 装配         *)
(*      （BA/BT/BNC ）；本件已备齐其前置引用面：          *)
(*      bxn_exp_neg（元素）+ bxn_exp_neg_spec(_eps)（收敛规格）     *)
(*      + bxn_bnorm_opp/bxn_bnorm_bpow_opp（范数面）                *)
(*      + bxn_series_mone_even/odd（符号交错定形）。                *)
(*   ② 符号交错级数的正性面：非本件范围。                               *)
(*   ③ exp_neg(0)=bone 完全等式面：同上游件未消解项（接口位缺失），*)
(*      本件交至邻域面 bxn_exp_neg_zero_close。                     *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：载体面工具（head 评估 / 常值规范实数 / 种型等价 / 范数）      *)
(* ============================================================ *)

(* 首项评估：Real -> Q（定义级） *)
Definition bxip_head (x : Real) : Q := projT1 x 0%nat.

(* 常值实数构造器（S02 real_const 透明：head 定义级还原） *)
Definition bxip_cR (q : Q) : Real := real_const q.

Lemma bxip_head_cR : forall q : Q, Id (bxip_head (bxip_cR q)) q.
Proof.
  intro q.
  unfold bxip_head, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* 种型等价：规范种型（Set 层，全库唯一实例位） *)
Definition bxip_bae_germ (a b : Real) : Set :=
  Id (bxib_qnorm (bxip_head a)) (bxib_qnorm (bxip_head b)).

(* 范数：Qabs∘qnorm∘head（处方定形） *)
Definition bxip_bnorm_f (x : Real) : Q := Qabs (bxib_qnorm (bxip_head x)).

(* 运算面：首项有理运算后规范化，包常值实数 *)
Definition bxip_bplus_f (x y : Real) : Real :=
  bxip_cR (bxib_qnorm (bxip_head x + bxip_head y)%Q).
Definition bxip_bmult_f (x y : Real) : Real :=
  bxip_cR (bxib_qnorm (bxip_head x * bxip_head y)%Q).
Definition bxip_bopp_f (x : Real) : Real :=
  bxip_cR (bxib_qnorm (- bxip_head x)%Q).
Definition bxip_bzero_f : Real := bxip_cR 0%Q.
Definition bxip_bone_f : Real := bxip_cR 1%Q.
Definition bxip_bcoef_f (q : Q) : Real := bxip_cR (bxib_qnorm q).

(* head 面还原（运算输出位定义级消化） *)
Lemma bxip_head_bplus : forall x y : Real,
  Id (bxip_head (bxip_bplus_f x y)) (bxib_qnorm (bxip_head x + bxip_head y)%Q).
Proof.
  intros x y.
  unfold bxip_head, bxip_bplus_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* ============================================================ *)
(* S1：Q 层工作件（==-合同 / Qabs 助件 / 规范不动点）               *)
(* ============================================================ *)

(* QeqT 乘法合同（INSTB cong 机器补位） *)
Lemma bxip_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (a * c)%Q (b * d)%Q.
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq a b Hab), (qeqT_imp_qeq c d Hcd).
  apply Qeq_refl.
Qed.

(* |xy| = |x||y|（Qabs_mult 缺名，自建） *)
Lemma bxip_qabs_mult : forall x y : Q, Qabs (x * y)%Q == Qabs x * Qabs y%Q.
Proof.
  intros [n d] [m e].
  unfold Qabs, Qmult, Qeq; simpl.
  rewrite Z.abs_mul. ring.
Qed.

(* Qabs 非负（QleT' 叶；由 Qabs_nonneg 一步给出） *)
Lemma bxip_qleT_zero_abs_qn : forall x : Q, QleT' 0 (Qabs (bxib_qnorm x)).
Proof.
  intro x. exact (Qle_to_QleT' _ _ (Qabs_nonneg (bxib_qnorm x))).
Qed.

(* 规范正偶对不动点：互素正偶对的 qnorm 定义级自返 *)
Lemma bxip_qnorm_pos_pair_fix : forall w t : positive,
  (Z.gcd (Zpos w) (Z.pos t) = Z.pos 1)%Z ->
  Id (bxib_qnorm (Qmake (Zpos w) t)) (Qmake (Zpos w) t).
Proof.
  intros w t Hg1.
  rewrite bxib_qnorm_pos_shape, Hg1.
  repeat rewrite Z.div_1_r.
  reflexivity.
Qed.

(* Qabs 壳形偶对不动点（apply 统一友好形） *)
Lemma bxip_qnorm_abs_pair_fix : forall w t : positive,
  (Z.gcd (Zpos w) (Z.pos t) = Z.pos 1)%Z ->
  Id (bxib_qnorm (Qabs (Qmake (Zpos w) t))) (Qabs (Qmake (Zpos w) t)).
Proof.
  intros w t Hg1.
  change (Id (bxib_qnorm (Qmake (Zpos w) t)) (Qmake (Zpos w) t)).
  apply bxip_qnorm_pos_pair_fix. exact Hg1.
Qed.

(* INSTB 未消解项闭合：Qopp 与 qnorm 的 Qabs-范数不变 *)
(* 墙一弱化形（实为 Id 形直证）：种型等价的范数 Id-良定 *)
Lemma bxip_norm_wd : forall a b : Real,
  bxip_bae_germ a b -> Id (bxip_bnorm_f a) (bxip_bnorm_f b).
Proof.
  intros a b H.
  unfold bxip_bae_germ in H.
  unfold bxip_bnorm_f.
  exact (id_cong Qabs H).
Qed.

(* 墙一 QeqT 形 *)
Lemma bxip_norm_wd_qeqt : forall a b : Real,
  bxip_bae_germ a b -> QeqT (bxip_bnorm_f a) (bxip_bnorm_f b).
Proof.
  intros a b H.
  unfold bxip_bnorm_f.
  apply bxib_qeqT_of_id.
  unfold bxip_bae_germ in H.
  exact (id_cong Qabs H).
Qed.

(* 墙二弱化形：钉定面的 QeqT 形（原始 Qabs 右端，代表元级成立） *)
Lemma bxip_norm_coef_qeqt : forall q : Q,
  QeqT (bxip_bnorm_f (bxip_bcoef_f q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  unfold bxip_bnorm_f, bxip_bcoef_f.
  rewrite (bxip_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  apply (Qeq_trans _ (Qabs (bxib_qnorm q))).
  - apply Qabs_wd. apply Qeq_refl.
  - apply (Qeq_trans _ (Qabs q)).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply Qeq_refl.
Qed.

(* 原始钉定墙固化：Id 形 Qabs-原始钉定在规范形下不可满足 *)
Lemma bxip_raw_pin_wall :
  Id (bxip_bnorm_f (bxip_bcoef_f (2#4)%Q)) (Qabs (2#4)%Q) ->
  Id (1#2)%Q (2#4)%Q.
Proof.
  intro H.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (2#4)%Q))) (Qabs (2#4)%Q)) in H.
  rewrite bxib_qnorm_fix_id in H.
  exact H.
Qed.

Lemma bxip_raw_pin_absurd : Id (1#2)%Q (2#4)%Q -> False.
Proof.
  intro H.
  apply (id_cong Qnum) in H.
  change (Id (Zpos 1) (Zpos 2)) in H.
  inversion H.
Qed.

(* ============================================================ *)
(* S3：BanachAlgPre 弱化类（39 字段＝两字段扩容对齐后的同构副本，       *)
(*   钉定面按处方修正）＋首例装配                                  *)
(* ============================================================ *)

Class bxip_BanachAlgPre := {
  bxip_BA : Set;
  bxip_bae : bxip_BA -> bxip_BA -> Set;
  bxip_bae_refl   : forall a : bxip_BA, bxip_bae a a;
  bxip_bae_sym    : forall a b : bxip_BA, bxip_bae a b -> bxip_bae b a;
  bxip_bae_trans  : forall a b c : bxip_BA,
    bxip_bae a b -> bxip_bae b c -> bxip_bae a c;
  bxip_bzero : bxip_BA;
  bxip_bone : bxip_BA;
  bxip_bplus : bxip_BA -> bxip_BA -> bxip_BA;
  bxip_bmult : bxip_BA -> bxip_BA -> bxip_BA;
  bxip_bopp : bxip_BA -> bxip_BA;
  bxip_bcoef : Q -> bxip_BA;
  bxip_bnorm : bxip_BA -> Q;
  bxip_bplus_assoc : forall a b c : bxip_BA,
    bxip_bae (bxip_bplus a (bxip_bplus b c)) (bxip_bplus (bxip_bplus a b) c);
  bxip_bplus_comm  : forall a b : bxip_BA,
    bxip_bae (bxip_bplus a b) (bxip_bplus b a);
  bxip_bplus_zero  : forall a : bxip_BA, bxip_bae (bxip_bplus a bxip_bzero) a;
  bxip_bplus_opp   : forall a : bxip_BA,
    bxip_bae (bxip_bplus a (bxip_bopp a)) bxip_bzero;
  bxip_bmult_assoc : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult a (bxip_bmult b c)) (bxip_bmult (bxip_bmult a b) c);
  bxip_bmult_one_l : forall a : bxip_BA, bxip_bae (bxip_bmult bxip_bone a) a;
  bxip_bmult_one_r : forall a : bxip_BA, bxip_bae (bxip_bmult a bxip_bone) a;
  bxip_bdistrib_l  : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult a (bxip_bplus b c))
             (bxip_bplus (bxip_bmult a b) (bxip_bmult a c));
  bxip_bdistrib_r  : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult (bxip_bplus a b) c)
             (bxip_bplus (bxip_bmult a c) (bxip_bmult b c));
  bxip_bmult_zero  : forall a : bxip_BA,
    bxip_bae (bxip_bmult a bxip_bzero) bxip_bzero;
  bxip_bplus_wd : forall a b c d : bxip_BA,
    bxip_bae a c -> bxip_bae b d -> bxip_bae (bxip_bplus a b) (bxip_bplus c d);
  bxip_bmult_wd : forall a b c d : bxip_BA,
    bxip_bae a c -> bxip_bae b d -> bxip_bae (bxip_bmult a b) (bxip_bmult c d);
  bxip_bopp_wd  : forall a b : bxip_BA,
    bxip_bae a b -> bxip_bae (bxip_bopp a) (bxip_bopp b);
  bxip_bnorm_wd : forall a b : bxip_BA,
    bxip_bae a b -> Id (bxip_bnorm a) (bxip_bnorm b);
  bxip_bcoef_zero : bxip_bae (bxip_bcoef 0%Q) bxip_bzero;
  bxip_bcoef_one  : bxip_bae (bxip_bcoef 1%Q) bxip_bone;
  bxip_bcoef_mult : forall q r : Q,
    bxip_bae (bxip_bcoef (q * r)%Q) (bxip_bmult (bxip_bcoef q) (bxip_bcoef r));
  bxip_bcoef_comm : forall (q : Q) (a : bxip_BA),
    bxip_bae (bxip_bmult a (bxip_bcoef q)) (bxip_bmult (bxip_bcoef q) a);
(* ---- 两字段扩容联动：Pre 副本扩容（37→39，                    *)
(*   语句形逐字承 UpReqBanachInst.v 同构副本）---- *)
  bxip_bcoef_plus : forall q r : Q,
    bxip_bae (bxip_bplus (bxip_bcoef q) (bxip_bcoef r)) (bxip_bcoef (q + r)%Q);
  bxip_bcoef_wd : forall q r : Q, q == r -> bxip_bae (bxip_bcoef q) (bxip_bcoef r);
  bxip_bnorm_zero : Id (bxip_bnorm bxip_bzero) 0%Q;
  bxip_bnorm_one  : Id (bxip_bnorm bxip_bone) 1%Q;
  bxip_bnorm_opp  : forall a : bxip_BA, QeqT (bxip_bnorm (bxip_bopp a)) (bxip_bnorm a);
  bxip_bnorm_pos  : forall a : bxip_BA, QleT' 0 (bxip_bnorm a);
  bxip_bnorm_plus : forall a b : bxip_BA,
    QleT' (bxip_bnorm (bxip_bplus a b)) (bxip_bnorm a + bxip_bnorm b)%Q;
  bxip_bnorm_mult : forall a b : bxip_BA,
    QleT' (bxip_bnorm (bxip_bmult a b)) (bxip_bnorm a * bxip_bnorm b)%Q;
  bxip_bnorm_coef : forall q : Q, Id (bxip_bnorm (bxip_bcoef q)) (Qabs (bxib_qnorm q));
}.

(* Pre 上的完备性语句（与 INS bxin_pre_complete 逐字同构） *)
Definition bxip_pre_complete (p : bxip_BanachAlgPre) : Set :=
  forall (u : nat -> (@bxip_BA p)),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n ->
        QltT (@bxip_bnorm p
          (@bxip_bplus p (u m) (@bxip_bopp p (u n)))) eps)) ->
    sigT (fun l : (@bxip_BA p) => forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bxip_bnorm p
          (@bxip_bplus p (u n) (@bxip_bopp p l))) eps)).

(* ---- 字段 discharge 件（种型载体） ---- *)

Lemma bxip_f_plus_assoc : forall a b c : Real,
  bxip_bae_germ (bxip_bplus_f a (bxip_bplus_f b c))
                (bxip_bplus_f (bxip_bplus_f a b) c).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a (bxip_bplus_f b c)).
  rewrite (bxip_head_bplus b c).
  rewrite (bxip_head_bplus (bxip_bplus_f a b) c).
  rewrite (bxip_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxib_qnorm (bxip_head b + bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a + bxip_head b)%Q + bxip_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a + (bxip_head b + bxip_head c))%Q).
  - apply bxib_qeqT_cong_plus; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a + bxip_head b + bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qplus_assoc.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxip_head_bmult : forall x y : Real,
  Id (bxip_head (bxip_bmult_f x y)) (bxib_qnorm (bxip_head x * bxip_head y)%Q).
Proof.
  intros x y.
  unfold bxip_head, bxip_bmult_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_head_bopp : forall x : Real,
  Id (bxip_head (bxip_bopp_f x)) (bxib_qnorm (- bxip_head x)%Q).
Proof.
  intro x.
  unfold bxip_head, bxip_bopp_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* ---- 等价三律 ---- *)

Lemma bxip_f_refl : forall a : Real, bxip_bae_germ a a.
Proof.
  intro a.
  unfold bxip_bae_germ.
  exact (@id_refl _ (bxib_qnorm (bxip_head a))).
Qed.

Lemma bxip_f_sym : forall a b : Real, bxip_bae_germ a b -> bxip_bae_germ b a.
Proof.
  intros a b H.
  unfold bxip_bae_germ in H |- *.
  exact (id_sym H).
Qed.

Lemma bxip_f_trans : forall a b c : Real,
  bxip_bae_germ a b -> bxip_bae_germ b c -> bxip_bae_germ a c.
Proof.
  intros a b c H1 H2.
  unfold bxip_bae_germ in H1 |- *.
  unfold bxip_bae_germ in H2.
  exact (@id_trans _ (bxib_qnorm (bxip_head a))
            (bxib_qnorm (bxip_head b)) (bxib_qnorm (bxip_head c)) H1 H2).
Qed.

(* ---- 加法群 ---- *)

Lemma bxip_f_plus_comm : forall a b : Real,
  bxip_bae_germ (bxip_bplus_f a b) (bxip_bplus_f b a).
Proof.
  intros a b. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a b), (bxip_head_bplus b a).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head b + bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qplus_comm.
Qed.

Lemma bxip_f_plus_zero : forall a : Real,
  bxip_bae_germ (bxip_bplus_f a bxip_bzero_f) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a bxip_bzero_f).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a + 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (bxip_head a)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
Qed.

Lemma bxip_f_plus_opp : forall a : Real,
  bxip_bae_germ (bxip_bplus_f a (bxip_bopp_f a)) bxip_bzero_f.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a (bxip_bopp_f a)).
  rewrite (bxip_head_bopp a).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxib_qnorm (- bxip_head a)%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a + (- bxip_head a))%Q).
  - apply bxib_qeqT_cong_plus;
      [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- 乘法群 ---- *)

Lemma bxip_f_mult_assoc : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f a (bxip_bmult_f b c))
                (bxip_bmult_f (bxip_bmult_f a b) c).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bmult_f b c)).
  rewrite (bxip_head_bmult b c).
  rewrite (bxip_head_bmult (bxip_bmult_f a b) c).
  rewrite (bxip_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm (bxip_head b * bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head b)%Q * bxip_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a * (bxip_head b * bxip_head c))%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head b * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply bxip_qeqT_cong_mult;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxip_f_mult_one_l : forall a : Real,
  bxip_bae_germ (bxip_bmult_f bxip_bone_f a) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult bxip_bone_f a).
  unfold bxip_bone_f.
  rewrite (bxip_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (1%Q * bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxip_f_mult_one_r : forall a : Real,
  bxip_bae_germ (bxip_bmult_f a bxip_bone_f) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a bxip_bone_f).
  unfold bxip_bone_f.
  rewrite (bxip_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a * 1%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

Lemma bxip_f_distrib_l : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f a (bxip_bplus_f b c))
                (bxip_bplus_f (bxip_bmult_f a b) (bxip_bmult_f a c)).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bplus_f b c)).
  rewrite (bxip_head_bplus b c).
  rewrite (bxip_head_bplus (bxip_bmult_f a b) (bxip_bmult_f a c)).
  rewrite (bxip_head_bmult a b), (bxip_head_bmult a c).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm (bxip_head b + bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head b)%Q
                              + bxib_qnorm (bxip_head a * bxip_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a * (bxip_head b + bxip_head c))%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head b + bxip_head a * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxip_f_distrib_r : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f (bxip_bplus_f a b) c)
                (bxip_bplus_f (bxip_bmult_f a c) (bxip_bmult_f b c)).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult (bxip_bplus_f a b) c).
  rewrite (bxip_head_bplus a b).
  rewrite (bxip_head_bplus (bxip_bmult_f a c) (bxip_bmult_f b c)).
  rewrite (bxip_head_bmult a c), (bxip_head_bmult b c).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a + bxip_head b)%Q * bxip_head c)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head c)%Q
                              + bxib_qnorm (bxip_head b * bxip_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ ((bxip_head a + bxip_head b) * bxip_head c)%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qnorm_fix | apply bxib_qeqT_refl].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head c + bxip_head b * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxip_f_mult_zero : forall a : Real,
  bxip_bae_germ (bxip_bmult_f a bxip_bzero_f) bxip_bzero_f.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a bxip_bzero_f).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a * 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ---- 良定三件 ---- *)

Lemma bxip_f_plus_wd : forall a b c d : Real,
  bxip_bae_germ a c -> bxip_bae_germ b d ->
  bxip_bae_germ (bxip_bplus_f a b) (bxip_bplus_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a b), (bxip_head_bplus c d).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head c + bxip_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_mult_wd : forall a b c d : Real,
  bxip_bae_germ a c -> bxip_bae_germ b d ->
  bxip_bae_germ (bxip_bmult_f a b) (bxip_bmult_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a b), (bxip_head_bmult c d).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head c * bxip_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxip_qeqT_cong_mult.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_opp_wd : forall a b : Real,
  bxip_bae_germ a b -> bxip_bae_germ (bxip_bopp_f a) (bxip_bopp_f b).
Proof.
  intros a b Hab. unfold bxip_bae_germ.
  rewrite (bxip_head_bopp a), (bxip_head_bopp b).
  rewrite (bxib_qnorm_fix_id (- bxip_head a)%Q).
  rewrite (bxib_qnorm_fix_id (- bxip_head b)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_of_id. exact Hab.
    + apply bxib_qnorm_fix.
Qed.

(* ---- 标量嵌入面 ---- *)

Lemma bxip_f_coef_zero : bxip_bae_germ (bxip_bcoef_f 0%Q) bxip_bzero_f.
Proof.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bzero_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_f_coef_one : bxip_bae_germ (bxip_bcoef_f 1%Q) bxip_bone_f.
Proof.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bone_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

Lemma bxip_f_coef_mult : forall q r : Q,
  bxip_bae_germ (bxip_bcoef_f (q * r)%Q)
                (bxip_bmult_f (bxip_bcoef_f q) (bxip_bcoef_f r)).
Proof.
  intros q r. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (q * r)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxib_qnorm r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym.
  apply bxip_qeqT_cong_mult; apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_coef_comm : forall (q : Q) (a : Real),
  bxip_bae_germ (bxip_bmult_f a (bxip_bcoef_f q))
                (bxip_bmult_f (bxip_bcoef_f q) a).
Proof.
  intros q a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bcoef_f q)).
  rewrite (bxip_head_bmult (bxip_bcoef_f q) a).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm q)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ---- W6a 二字段 discharge（INST3 已建 qnorm 机器同款链） ---- *)

(* bcoef_plus：q+r 嵌入＝嵌入和（种型载体上归 qnorm 环链一发修） *)
Lemma bxip_f_coef_plus : forall q r : Q,
  bxip_bae_germ (bxip_bplus_f (bxip_bcoef_f q) (bxip_bcoef_f r))
                (bxip_bcoef_f (q + r)%Q).
Proof.
  intros q r. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

(* bcoef_wd：Qeq 代表元无关（QeqT 过桥 qnorm 良定） *)
Lemma bxip_f_coef_wd : forall q r : Q,
  q == r -> bxip_bae_germ (bxip_bcoef_f q) (bxip_bcoef_f r).
Proof.
  intros q r Hqr. unfold bxip_bae_germ, bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ---- 范数面 ---- *)

Lemma bxip_f_norm_zero : Id (bxip_bnorm_f bxip_bzero_f) 0%Q.
Proof.
  unfold bxip_bnorm_f, bxip_bzero_f, bxip_head, real_const, bxib_qnorm, Qabs.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_f_norm_one : Id (bxip_bnorm_f bxip_bone_f) 1%Q.
Proof.
  unfold bxip_bnorm_f, bxip_bone_f, bxip_head, real_const, bxib_qnorm, Qabs.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

Lemma bxip_f_norm_opp : forall a : Real,
  QeqT (bxip_bnorm_f (bxip_bopp_f a)) (bxip_bnorm_f a).
Proof.
  intro a. unfold bxip_bnorm_f.
  rewrite (bxip_head_bopp a).
  rewrite (bxib_qnorm_fix_id (- bxip_head a)%Q).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (- bxip_head a)%Q)).
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - rewrite Qabs_opp.
    apply (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))).
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_norm_pos : forall a : Real, QleT' 0 (bxip_bnorm_f a).
Proof.
  intro a.
  exact (Qle_to_QleT' _ _ (Qabs_nonneg (bxib_qnorm (bxip_head a)))).
Qed.

Lemma bxip_f_norm_plus : forall a b : Real,
  QleT' (bxip_bnorm_f (bxip_bplus_f a b))
        (bxip_bnorm_f a + bxip_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxip_bnorm_f.
  rewrite (bxip_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxip_head a + bxip_head b)%Q)).
  - apply qeq_imp_qle.
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - apply (Qle_trans _ (Qabs (bxip_head a) + Qabs (bxip_head b))%Q).
    + apply Qabs_triangle.
    + apply qeq_imp_qle.
      apply (@Qplus_comp (Qabs (bxip_head a)) (Qabs (bxib_qnorm (bxip_head a)))
           (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))
                (Qabs_wd (bxib_qnorm (bxip_head a)) (bxip_head a)
                     (qeqT_imp_qeq (bxib_qnorm (bxip_head a)) (bxip_head a)
                          (bxib_qnorm_fix (bxip_head a)))))
           (Qabs (bxip_head b)) (Qabs (bxib_qnorm (bxip_head b)))
           (Qeq_sym (Qabs (bxib_qnorm (bxip_head b))) (Qabs (bxip_head b))
                (Qabs_wd (bxib_qnorm (bxip_head b)) (bxip_head b)
                     (qeqT_imp_qeq (bxib_qnorm (bxip_head b)) (bxip_head b)
                          (bxib_qnorm_fix (bxip_head b)))))).
Qed.

Lemma bxip_f_norm_mult : forall a b : Real,
  QleT' (bxip_bnorm_f (bxip_bmult_f a b))
        (bxip_bnorm_f a * bxip_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxip_bnorm_f.
  rewrite (bxip_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxip_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxip_head a) * Qabs (bxip_head b))%Q).
  - apply qeq_imp_qle.
    apply (Qeq_trans (Qabs (bxib_qnorm (bxip_head a * bxip_head b)%Q))
                     (Qabs (bxip_head a * bxip_head b)%Q)
                     (Qabs (bxip_head a) * Qabs (bxip_head b))%Q).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply bxip_qabs_mult.
  - apply qeq_imp_qle.
    apply (@Qmult_comp (Qabs (bxip_head a)) (Qabs (bxib_qnorm (bxip_head a)))
         (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))
              (Qabs_wd (bxib_qnorm (bxip_head a)) (bxip_head a)
                   (qeqT_imp_qeq (bxib_qnorm (bxip_head a)) (bxip_head a)
                        (bxib_qnorm_fix (bxip_head a)))))
         (Qabs (bxip_head b)) (Qabs (bxib_qnorm (bxip_head b)))
         (Qeq_sym (Qabs (bxib_qnorm (bxip_head b))) (Qabs (bxip_head b))
              (Qabs_wd (bxib_qnorm (bxip_head b)) (bxip_head b)
                   (qeqT_imp_qeq (bxib_qnorm (bxip_head b)) (bxip_head b)
                        (bxib_qnorm_fix (bxip_head b)))))).
Qed.

Lemma bxip_f_norm_coef : forall q : Q,
  Id (bxip_bnorm_f (bxip_bcoef_f q)) (Qabs (bxib_qnorm q)).
Proof.
  intro q. unfold bxip_bnorm_f, bxip_bcoef_f.
  rewrite (bxip_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  reflexivity.
Qed.

(* ---- 首例装配（B 路第一个具体实例，弱化形） ---- *)

Instance bxip_real_pre : bxip_BanachAlgPre := {|
  bxip_BA := Real;
  bxip_bae := bxip_bae_germ;
  bxip_bae_refl := bxip_f_refl;
  bxip_bae_sym := bxip_f_sym;
  bxip_bae_trans := bxip_f_trans;
  bxip_bzero := bxip_bzero_f;
  bxip_bone := bxip_bone_f;
  bxip_bplus := bxip_bplus_f;
  bxip_bmult := bxip_bmult_f;
  bxip_bopp := bxip_bopp_f;
  bxip_bcoef := bxip_bcoef_f;
  bxip_bnorm := bxip_bnorm_f;
  bxip_bplus_assoc := bxip_f_plus_assoc;
  bxip_bplus_comm := bxip_f_plus_comm;
  bxip_bplus_zero := bxip_f_plus_zero;
  bxip_bplus_opp := bxip_f_plus_opp;
  bxip_bmult_assoc := bxip_f_mult_assoc;
  bxip_bmult_one_l := bxip_f_mult_one_l;
  bxip_bmult_one_r := bxip_f_mult_one_r;
  bxip_bdistrib_l := bxip_f_distrib_l;
  bxip_bdistrib_r := bxip_f_distrib_r;
  bxip_bmult_zero := bxip_f_mult_zero;
  bxip_bplus_wd := bxip_f_plus_wd;
  bxip_bmult_wd := bxip_f_mult_wd;
  bxip_bopp_wd := bxip_f_opp_wd;
  bxip_bnorm_wd := bxip_norm_wd;
  bxip_bcoef_zero := bxip_f_coef_zero;
  bxip_bcoef_one := bxip_f_coef_one;
  bxip_bcoef_mult := bxip_f_coef_mult;
  bxip_bcoef_comm := bxip_f_coef_comm;
  bxip_bcoef_plus := bxip_f_coef_plus;
  bxip_bcoef_wd := bxip_f_coef_wd;
  bxip_bnorm_zero := bxip_f_norm_zero;
  bxip_bnorm_one := bxip_f_norm_one;
  bxip_bnorm_opp := bxip_f_norm_opp;
  bxip_bnorm_pos := bxip_f_norm_pos;
  bxip_bnorm_plus := bxip_f_norm_plus;
  bxip_bnorm_mult := bxip_f_norm_mult;
  bxip_bnorm_coef := bxip_f_norm_coef;
|}.

(* 装配检验：实例投影面（bcoef 1 ~ bone，经实例字段） *)
Lemma bxip_inst_smoke :
  @bxip_bae bxip_real_pre
    (@bxip_bcoef bxip_real_pre 1%Q)
    (@bxip_bone bxip_real_pre).
Proof.
  unfold bxip_bae, bxip_bcoef, bxip_bone.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bone_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

(* 装配检验：W6a 二字段投影位（bcoef plus/wd 经实例字段） *)
Lemma bxip_inst_smoke_plus : forall q r : Q,
  @bxip_bae bxip_real_pre
    (@bxip_bplus bxip_real_pre (@bxip_bcoef bxip_real_pre q)
                               (@bxip_bcoef bxip_real_pre r))
    (@bxip_bcoef bxip_real_pre (q + r)%Q).
Proof.
  intros q r.
  unfold bxip_bae, bxip_bcoef, bxip_bplus.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ.
  rewrite (bxip_head_bplus (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

Lemma bxip_inst_smoke_wd : forall q r : Q,
  q == r ->
  @bxip_bae bxip_real_pre
    (@bxip_bcoef bxip_real_pre q) (@bxip_bcoef bxip_real_pre r).
Proof.
  intros q r Hqr.
  unfold bxip_bae, bxip_bcoef.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ, bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ============================================================ *)
(* 提取检验 + 假设面自审                                      *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction bxip_bnorm_f bxip_qeqT_cong_mult bxip_qabs_mult bxip_raw_pin_wall bxip_norm_wd_qeqt
  bxip_norm_coef_qeqt bxip_f_coef_plus bxip_f_coef_wd.

Print Assumptions bxip_raw_pin_wall.
Print Assumptions bxip_norm_wd_qeqt.
Print Assumptions bxip_f_plus_assoc.
Print Assumptions bxip_f_norm_mult.
Print Assumptions bxip_inst_smoke.
Print Assumptions bxip_f_coef_plus.
Print Assumptions bxip_f_coef_wd.
Print Assumptions bxip_inst_smoke_plus.
Print Assumptions bxip_inst_smoke_wd.

(* ============================ §2 bxem_mult/bxem_one 定义、bxem_qeqT_cong_mult（QeqT 乘法外推）与 bxem_mult_assoc/one_l/ ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* E0：乘法定义与单位元（构造子位选型，零新算术）                   *)
(* ============================================================ *)

Definition bxem_mult (a b : bxib_E) : bxib_E := bxib_emult a b.

Definition bxem_one : bxib_E := bxib_esc 1%Q.

(* ---- QeqT 乘法cong（与 INSTB bxib_qeqT_cong_plus 同构，stdlib 缺口） ---- *)

Lemma bxem_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (Qmult a c) (Qmult b d).
Proof.
  intros a b c d Hab Hcd. apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in Hab. apply qeqT_imp_qeq in Hcd.
  rewrite <- Hab, <- Hcd. apply Qeq_refl.
Qed.

(* ---- 通用桥：bae x y -> QeqT (ev x) (ev y)（bae 判据开锁件） ---- *)

Lemma bxem_qeqT_of_bae : forall a b : bxib_E,
  bxib_bae a b -> QeqT (bxib_ev a) (bxib_ev b).
Proof.
  intros a b H.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev a)) _).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev b)) _).
    + exact (bxib_qeqT_of_id _ _ H).
    + apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* E1：保底件②——bxem_mult_wd（bae-良定义）                        *)
(*   双 qnorm 退化（fix_id）+ 求值像 Q 层 cong_mult + id_of_qeqT。  *)
(* ============================================================ *)

Lemma bxem_mult_wd : forall a b c d : bxib_E,
  bxib_bae a c -> bxib_bae b d ->
  bxib_bae (bxem_mult a b) (bxem_mult c d).
Proof.
  intros a b c d Hac Hbd. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a b))
    with (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b))).
  change (bxib_ev (bxib_emult c d))
    with (bxib_qnorm (Qmult (bxib_ev c) (bxib_ev d))).
  pose proof (bxem_qeqT_cong_mult (bxib_ev a) (bxib_ev c)
                (bxib_ev b) (bxib_ev d)
                (bxem_qeqT_of_bae a c Hac) (bxem_qeqT_of_bae b d Hbd)) as H.
  exact (id_trans
    (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) (bxib_ev b)))
              (bxib_qnorm_id_of_qeqT _ _ H))
    (id_sym (bxib_qnorm_fix_id (Qmult (bxib_ev c) (bxib_ev d))))).
Qed.

(* ============================================================ *)
(* E2：保底件③——bxem_mult_assoc（结合律，R2L 向对齐               *)
(*   bxin_bmult_assoc：bae (mult a (mult b c)) (mult (mult a b) c)） *)
(* ============================================================ *)

Lemma bxem_mult_assoc : forall a b c : bxib_E,
  bxib_bae (bxem_mult a (bxem_mult b c))
           (bxem_mult (bxem_mult a b) c).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_emult b c)))
    with (bxib_qnorm (Qmult (bxib_ev a)
            (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c))))).
  change (bxib_ev (bxib_emult (bxib_emult a b) c))
    with (bxib_qnorm (Qmult (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
                            (bxib_ev c))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (bxib_ev a) (Qmult (bxib_ev b) (bxib_ev c))) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_ev a)
             (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c)))) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qeqT_refl.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _
      (Qmult (Qmult (bxib_ev a) (bxib_ev b)) (bxib_ev c)) _).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply (bxib_qeqT_trans _
        (Qmult (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
               (bxib_ev c)) _).
      * apply bxem_qeqT_cong_mult.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_refl.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* E3：主件——单位律 / 分配律 / 交换律 / 零吸收（乘法群成套）        *)
(* ============================================================ *)

Lemma bxem_mult_one_l : forall a : bxib_E,
  bxib_bae (bxem_mult bxem_one a) a.
Proof.
  intro a. unfold bxem_mult, bxem_one, bxib_bae.
  change (bxib_ev (bxib_emult (bxib_esc 1%Q) a))
    with (bxib_qnorm (Qmult 1%Q (bxib_ev a))).
  apply (id_trans (bxib_qnorm_fix_id (Qmult 1%Q (bxib_ev a)))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxem_mult_one_r : forall a : bxib_E,
  bxib_bae (bxem_mult a bxem_one) a.
Proof.
  intro a. unfold bxem_mult, bxem_one, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_esc 1%Q)))
    with (bxib_qnorm (Qmult (bxib_ev a) 1%Q)).
  apply (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) 1%Q))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

Lemma bxem_distrib_l : forall a b c : bxib_E,
  bxib_bae (bxem_mult a (bxib_eplus b c))
           (bxib_eplus (bxem_mult a b) (bxem_mult a c)).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_eplus b c)))
    with (bxib_qnorm (Qmult (bxib_ev a)
            (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c))))).
  change (bxib_ev (bxib_eplus (bxib_emult a b) (bxib_emult a c)))
    with (bxib_qnorm (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
                            (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c))))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c))) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_ev a)
             (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c)))) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qeqT_refl.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _
      (Qplus (Qmult (bxib_ev a) (bxib_ev b))
             (Qmult (bxib_ev a) (bxib_ev c))) _).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply (bxib_qeqT_trans _
        (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
               (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))) _).
      * apply bxib_qeqT_cong_plus.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxem_distrib_r : forall a b c : bxib_E,
  bxib_bae (bxem_mult (bxib_eplus a b) c)
           (bxib_eplus (bxem_mult a c) (bxem_mult b c)).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult (bxib_eplus a b) c))
    with (bxib_qnorm (Qmult (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b)))
                            (bxib_ev c))).
  change (bxib_ev (bxib_eplus (bxib_emult a c) (bxib_emult b c)))
    with (bxib_qnorm (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))
                            (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c))))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c)) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b)))
             (bxib_ev c)) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qnorm_fix.
      * apply bxib_qeqT_refl.
  - apply (bxib_qeqT_trans _
      (Qplus (Qmult (bxib_ev a) (bxib_ev c))
             (Qmult (bxib_ev b) (bxib_ev c))) _).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply (bxib_qeqT_trans _
        (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))
               (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c)))) _).
      * apply bxib_qeqT_cong_plus.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxem_mult_comm : forall a b : bxib_E,
  bxib_bae (bxem_mult a b) (bxem_mult b a).
Proof.
  intros a b. unfold bxem_mult, bxib_bae.
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qnorm_qeqT_of_qeqT. apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

Lemma bxem_mult_zero : forall a : bxib_E,
  bxib_bae (bxem_mult a bxib_ez) bxib_ez.
Proof.
  intro a. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a bxib_ez))
    with (bxib_qnorm (Qmult (bxib_ev a) 0%Q)).
  change (bxib_ev bxib_ez) with (0#1)%Q.
  apply (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) 0%Q))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ============================================================ *)
(* E4：附带供给——INSTB 未消解项 ⓪′/⓪ 的 wd 位（同款退化技术顺带闭合）*)
(*   （bxem_bplus_wd / bxem_bopp_wd：装配位与类字段 bplus_wd/       *)
(*    bopp_wd 逐字同形，W6 可直取。）                              *)
(* ============================================================ *)

Lemma bxem_bplus_wd : forall a b c d : bxib_E,
  bxib_bae a c -> bxib_bae b d ->
  bxib_bae (bxib_eplus a b) (bxib_eplus c d).
Proof.
  intros a b c d Hac Hbd. unfold bxib_bae.
  change (bxib_ev (bxib_eplus a b))
    with (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))).
  change (bxib_ev (bxib_eplus c d))
    with (bxib_qnorm (Qplus (bxib_ev c) (bxib_ev d))).
  pose proof (bxib_qeqT_cong_plus (bxib_ev a) (bxib_ev c)
                (bxib_ev b) (bxib_ev d)
                (bxem_qeqT_of_bae a c Hac) (bxem_qeqT_of_bae b d Hbd)) as H.
  exact (id_trans
    (id_trans (bxib_qnorm_fix_id (Qplus (bxib_ev a) (bxib_ev b)))
              (bxib_qnorm_id_of_qeqT _ _ H))
    (id_sym (bxib_qnorm_fix_id (Qplus (bxib_ev c) (bxib_ev d))))).
Qed.

Lemma bxem_bopp_wd : forall a b : bxib_E,
  bxib_bae a b -> bxib_bae (bxib_eopp a) (bxib_eopp b).
Proof.
  intros a b H. unfold bxib_bae.
  change (bxib_ev (bxib_eopp a)) with (Qopp (bxib_ev a)).
  change (bxib_ev (bxib_eopp b)) with (Qopp (bxib_ev b)).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp. apply bxem_qeqT_of_bae. exact H.
Qed.

(* ============================================================ *)
(* 提取检验                                                       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bxem_mult bxem_one bxem_mult_wd bxem_mult_assoc
  bxem_mult_one_l bxem_mult_one_r bxem_distrib_l bxem_distrib_r
  bxem_mult_comm bxem_mult_zero bxem_bplus_wd bxem_bopp_wd.

Print Assumptions bxem_mult_wd.
Print Assumptions bxem_mult_assoc.
Print Assumptions bxem_mult_one_l.
Print Assumptions bxem_mult_one_r.
Print Assumptions bxem_distrib_l.
Print Assumptions bxem_distrib_r.
Print Assumptions bxem_mult_comm.
Print Assumptions bxem_mult_zero.
Print Assumptions bxem_bplus_wd.
Print Assumptions bxem_bopp_wd.

(* ============================ §3 语句面弱化形下游的强形式恢复件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachExpBasic.
Require Import UpReqBanachExpDef.
Require Import UpReqNormConv.
Require Import UpReqBanachCauchyD.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* S0：qnorm 字面规范支持件                                       *)
(* ============================================================ *)

(* 1 的 gcd 正规化定义级不动（qnorm 1 = 1，iota/zeta 即闭） *)
Lemma bxst_qnorm_one : Id (bxib_qnorm 1%Q) 1%Q.
Proof.
  unfold bxib_qnorm.
  cbv iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

(* Qabs∘qnorm 在 1 位的不动形（钉定面规范位） *)
(* 经 bxst_qnorm_one 与 Qabs 的合同性（id_cong）一步得出，不再重演 Z 正规化 *)
Lemma bxst_qabs_qnorm_one : Id (Qabs (bxib_qnorm 1%Q)) (Qabs 1%Q).
Proof.
  exact (id_cong Qabs bxst_qnorm_one).
Qed.

(* ============================================================ *)
(* S1 核心恢复件①：关键引理一 bnorm_wd 的 Id 强形式（规范形恢复）  *)
(*   原 Id 形：bae a b -> Id (bnorm a) (bnorm b)                  *)
(*   恢复形：规范形位置 Id（qnorm 链；抽象层全量恢复不可能如头注） *)
(* ============================================================ *)

Lemma bxst_norm_wd_id : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B a b -> Id (bxib_qnorm (@bnorm B a)) (bxib_qnorm (@bnorm B b)).
Proof.
  intros B a b H.
  apply bxib_qnorm_id_of_qeq.
  apply qeqT_imp_qeq.
  exact (@bnorm_wd B a b H).
Qed.

(* S1 核心恢复件②：关键引理二 bnorm_coef 的 Id 强形式（规范形恢复）
   原 Id 形：Id (bnorm (bcoef q)) (Qabs q) *)
Lemma bxst_norm_coef_id : forall (B : BanachAlg) (q : Q),
  Id (bxib_qnorm (@bnorm B (@bcoef B q))) (bxib_qnorm (Qabs q)).
Proof.
  intros B q.
  apply bxib_qnorm_id_of_qeq.
  apply qeqT_imp_qeq.
  exact (@bnorm_coef B q).
Qed.

(* S1 伴件：标量 1 位的全量字面 Id 形（qnorm 1 = 1 收尾） *)
Lemma bxst_norm_coef_one : forall (B : BanachAlg),
  Id (bxib_qnorm (@bnorm B (@bcoef B 1%Q))) 1%Q.
Proof.
  intros B.
  apply (id_trans (bxib_qnorm_id_of_qeqT _ _ (@bnorm_coef B 1%Q))).
  unfold bxib_qnorm, Qabs.
  cbv iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

(* S1 伴件：INSTB 规范实例同位语句的全量 Id 形（定义级；INSTB 已证，
   此处同位再出口使本件自足） *)
Lemma bxst_inst_norm_wd_id : forall (a b : bxib_E),
  bxib_bae a b -> Id (bxib_bnorm a) (bxib_bnorm b).
Proof.
  intros a b H.
  unfold bxib_bae in H.
  unfold bxib_bnorm.
  exact (id_cong Qabs H).
Qed.

(* ============================================================ *)
(* S2 主件：四处语句面弱化位点的强形式对应件                      *)
(* ============================================================ *)

(* 主件①：ExpBasic bxb_norm_series_zero（原 Id (bnorm (esp B bzero m)) 1） *)
Lemma bxst_bxb_norm_series_zero_strong : forall (B : BanachAlg) (m : nat),
  Id (bxib_qnorm (@bnorm B (exp_series_partial B (@bzero B) m))) 1%Q.
Proof.
  intros B m.
  pose proof (bxib_qnorm_fix (@bnorm B (exp_series_partial B (@bzero B) m))) as Hf.
  apply (id_trans (id_sym (bxib_qnorm_id_of_qeqT _ _ Hf))).
  apply (id_trans (bxib_qnorm_id_of_qeqT _ _
                     (bxib_qeqT_trans _ _ _ Hf (bxb_norm_series_zero B m)))).
  exact bxst_qnorm_one.
Qed.

(* 主件②：ExpDef bxdef_esp_zero_bnorm（原 Id (bnorm (esp B bzero n)) 1） *)
Lemma bxst_bxdef_esp_zero_bnorm_strong : forall (B : BanachAlg) (n : nat),
  Id (bxib_qnorm (@bnorm B (exp_series_partial B (@bzero B) n))) 1%Q.
Proof.
  intros B n.
  pose proof (bxib_qnorm_fix (@bnorm B (exp_series_partial B (@bzero B) n))) as Hf.
  apply (id_trans (id_sym (bxib_qnorm_id_of_qeqT _ _ Hf))).
  apply (id_trans (bxib_qnorm_id_of_qeqT _ _
                     (bxib_qeqT_trans _ _ _ Hf (bxdef_esp_zero_bnorm B n)))).
  exact bxst_qnorm_one.
Qed.

(* 主件③：NormConv ncv_norm_diff_sym
   （原 Id (bnorm (bplus x (bopp y))) (bnorm (bplus y (bopp x)))） *)
Lemma bxst_ncv_norm_diff_sym_strong : forall (B : BanachAlg) (x y : (@BA B)),
  Id (bxib_qnorm (@bnorm B (@bplus B x (@bopp B y))))
     (bxib_qnorm (@bnorm B (@bplus B y (@bopp B x)))).
Proof.
  intros B x y.
  exact (id_sym (bxib_qnorm_id_of_qeqT _ _ (ncv_norm_diff_sym B y x))).
Qed.

(* 主件④：CauchyD bxcd_prod_close
   （原 Id (bnorm (bplus (bmult (esp a n) (esp (bopp a) n)) (bopp bone))) (bnorm U)） *)
Lemma bxst_bxcd_prod_close_strong : forall (B : BanachAlg) (a : (@BA B)) (n : nat)
                                           (U : (@BA B)),
  @bae B (@bmult B (exp_series_partial B a n)
                   (exp_series_partial B (@bopp B a) n))
         (@bplus B (@bone B) U) ->
  Id (bxib_qnorm (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                             (exp_series_partial B (@bopp B a) n))
                                   (@bopp B (@bone B)))))
     (bxib_qnorm (@bnorm B U)).
Proof.
  intros B a n U H.
  pose proof (bxib_qnorm_fix (@bnorm B (@bplus B (@bmult B (exp_series_partial B a n)
                                                (exp_series_partial B (@bopp B a) n))
                                      (@bopp B (@bone B))))) as Hf.
  apply (id_trans (id_sym (bxib_qnorm_id_of_qeqT _ _ Hf))).
  apply (bxib_qnorm_id_of_qeqT _ _).
  exact (bxib_qeqT_trans _ _ _ Hf (bxcd_prod_close B a n U H)).
Qed.

(* —— 完结：两个关键引理恢复 + 四处语句面弱化位点强形式全对应 —— *)

(* ============================ §4 bxce_sep 字段定理化（Banach 完全等式面） 使命：「exp(0) 完全等式面」未消解项的转化件——bxce_sep 字段 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInst.
Require Import UpReqBanachInstReal.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
From Stdlib Require Import QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* S0：① Q 引擎件                                                     *)
(* ============================================================ *)

(* 桥消解件：|x| == 0 ⟹ x == 0（三分构造子级直拆，Qabs 定义级归约） *)
Lemma spt_qabs_eq0_inv : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H.
  unfold Qeq in H. unfold Qeq.
  destruct n as [|p|p].
  - exact H.
  - exfalso. simpl in H. discriminate H.
  - exfalso. simpl in H. discriminate H.
Qed.

(* 引擎主件：|x| 小于任意正 eps ⟹ x == 0（三分判定构造）        *)
Theorem spt_q_abs_arb_small_eq0 : forall x : Q,
  (forall eps : Q, QltT 0 eps -> QltT (Qabs x) eps) -> x == 0.
Proof.
  intros x Hall.
  destruct (Qlt_le_dec 0 (Qabs x)) as [Hpos | Hnonpos].
  - (* 正臂 0 < |x|：eps := 0·|x|（=½·|x| 的乘积正性形），Hall 给
       |x| < 0·|x| < ½·|x| ≤ 1·|x| = |x| 自反矛盾 *)
    exfalso.
    assert (Hhalfpos : Qlt 0 (1#2)%Q) by exact Z.lt_0_1.
    assert (Hhalf_le : Qle (1#2)%Q 1%Q).
    { unfold Qle. simpl. exact (Z.le_succ_diag_r 1). }
    assert (Heps : QltT 0 ((1#2)%Q * Qabs x)%Q).
    { pose proof (proj2 (Qmult_lt_r 0 (1#2)%Q (Qabs x) Hpos) Hhalfpos) as Hp.
      setoid_rewrite (Qmult_0_l (Qabs x)) in Hp.
      apply Qlt_to_QltT. exact Hp. }
    assert (Hle : Qle ((1#2)%Q * Qabs x) (Qabs x)).
    { pose proof (Qmult_le_compat_r (1#2)%Q 1%Q (Qabs x) Hhalf_le
                    (Qabs_nonneg x)) as Hle0.
      setoid_rewrite (Qmult_1_l (Qabs x)) in Hle0.
      exact Hle0. }
    exact (Qlt_irrefl (Qabs x)
             (Qlt_le_trans (Qabs x) ((1#2)%Q * Qabs x) (Qabs x)
                (QltT_to_Qlt _ _ (Hall ((1#2)%Q * Qabs x)%Q Heps)) Hle)).
  - (* 负臂 |x| ≤ 0：与非负性（Qabs_nonneg）合流 ⟹ |x| == 0 ⟹ 消桥 *)
    exact (spt_qabs_eq0_inv x (Qle_antisym (Qabs x) 0 Hnonpos
                                        (Qabs_nonneg x))).
Qed.

(* ============================================================ *)
(* S1：② 载体特化——范数处方的 Qabs 换代表元桥                          *)
(* ============================================================ *)

Lemma spt_qabs_qnorm_head : forall q : Q, QeqT (Qabs (bxib_qnorm q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  apply Qabs_wd.
  apply qeqT_imp_qeq.
  apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* S1.5：③ 核心件（具体 Id 面算法形，G3 提取出口——类投影型语句面       *)
(* 提取必生类型擦除产物（bxin_bae＝__，bxra_real_pre 实例同因），        *)
(* 故提取走本件；主件保持字段面语句、经本件定义级转换衔接）              *)
(* ============================================================ *)

Definition spt_bxce_sep_core (a : Real)
  (Hall : forall eps : Q,
    QltT 0 eps -> QltT (Qabs (bxib_qnorm (bxra_head a))) eps) :
  Id (bxib_qnorm (bxra_head a)) (bxib_qnorm (bxra_head bxra_bzero_f)) :=
  bxib_qnorm_id_of_qeqT (bxra_head a) 0%Q
    (qeq_imp_qeqT (bxra_head a) 0%Q
       (spt_q_abs_arb_small_eq0 (bxra_head a)
          (fun eps Heps =>
            bxra_qltT_wd (Qabs (bxib_qnorm (bxra_head a)))
                         (Qabs (bxra_head a)) eps
              (spt_qabs_qnorm_head (bxra_head a)) (Hall eps Heps)))).

(* ============================================================ *)
(* S2：③ 主件——bxce_sep 字段语句面在 bxra_real_pre 上的定理化          *)
(* （目标形逐字，承自 Pre 实例投影：bnorm＝Qabs∘qnorm∘head，            *)
(*   bae＝规范种型 Id(qnorm(head ·))(qnorm(head ·))，bzero＝const 0）  *)
(* ============================================================ *)

Theorem spt_bxce_sep_real : forall a : Real,
  (forall eps : Q, QltT 0 eps -> QltT (@bxin_bnorm bxra_real_pre a) eps) ->
  @bxin_bae bxra_real_pre a (@bxin_bzero bxra_real_pre).
Proof.
  intros a Hall.
  exact (spt_bxce_sep_core a Hall).
Qed.

(* ============================================================ *)
(* S3：装配位使用（条件件，完备性闸门 Hc＝显式 Set 参数）               *)
(* ============================================================ *)

(* bxce_sep 参数位定理化面（Ext 装配位点：桥产物 BanachAlg 上的字段形） *)
Lemma spt_ext_sep_slot_theorem :
  forall (Hc : bxin_pre_complete bxra_real_pre)
         (a : (@BA (bxra_BanachAlg_of_real Hc))),
    (forall eps : Q,
      QltT 0 eps -> QltT (@bnorm (bxra_BanachAlg_of_real Hc) a) eps) ->
    @bae (bxra_BanachAlg_of_real Hc) a (@bzero (bxra_BanachAlg_of_real Hc)).
Proof.
  intros Hc a Hall.
  exact (spt_bxce_sep_real a Hall).
Qed.

(* 全装配：bxce_mk 三引理桥，sp 参数位由定理供给（落地时直接接入）   *)
Definition spt_ext_of_real (Hc : bxin_pre_complete bxra_real_pre) :
  BanachAlgExt :=
  bxce_mk (bxra_BanachAlg_of_real Hc)
          (@bcoef_plus (bxra_BanachAlg_of_real Hc))
          (@bcoef_wd (bxra_BanachAlg_of_real Hc))
          (spt_ext_sep_slot_theorem Hc).

(* 接入件：极限唯一性未消解项第二件在条件装配下的实现演示——
   bxuq_lim_uniq 使用 spt_ext_of_real，泛型双极限 ⟹ bae 相等 *)
Lemma spt_uniq_reap :
  forall (Hc : bxin_pre_complete bxra_real_pre)
         (u : nat -> (@BA (@bxce_base (spt_ext_of_real Hc))))
         (l1 l2 : (@BA (@bxce_base (spt_ext_of_real Hc)))),
    blim (@bxce_base (spt_ext_of_real Hc)) u l1 ->
    blim (@bxce_base (spt_ext_of_real Hc)) u l2 ->
    @bae (@bxce_base (spt_ext_of_real Hc)) l1 l2.
Proof.
  intros Hc u l1 l2 H1 H2.
  exact (bxuq_lim_uniq (spt_ext_of_real Hc) u l1 l2 H1 H2).
Qed.

(* ============================================================ *)
(* 尾注（G1 面）：本件零公理、零承认、零中断；语句面 Prop 泄露仅        *)
(*   x == 0（Qeq，ClassExt 既有形）；出口闭包自检见编译 stdout。       *)
(* ============================================================ *)

(* ============================================================ *)
(* G3 面：提取检验 + 出口闭包自检                                      *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "../attn/_taa7_bak/ml".
Separate Extraction spt_qabs_eq0_inv spt_q_abs_arb_small_eq0
  spt_qabs_qnorm_head spt_bxce_sep_core.

Print Assumptions spt_q_abs_arb_small_eq0.
Print Assumptions spt_bxce_sep_core.
Print Assumptions spt_bxce_sep_real.
Print Assumptions spt_ext_of_real.
Print Assumptions spt_uniq_reap.
