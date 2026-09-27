(* ==========================================================================)
   BanachS3Chain.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：bxoo_lim_esp_zero_bone、bxoo_nearone_blim、bxoo_bmult_assoc_sym、bxoo_uniq_shape、bxoo_bzero_eq_bone_assembly、bxoo_exp_opp_one_assembly、bxoo_bzero_eq_bone、bxoo_exp_opp_one、s3c_hplus_of。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
Require Import UpReqBanachCauchyD.
From Stdlib Require Import Lia.
Require Import UpReqBanachProd.
Require Import UpReqBanachAdd.
Require Import UpReqBanachDouble.
Require Import BanachNoHyp.
Require Import UpReqBanachExpAddEq.
Require Import UpReqBanachInvPre.

(* ================= §1 bxoo_lim_esp_zero_bone 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S1 机械件一（bzero 邻域换骨）：零元级数部分和序列收敛到 bone。  *)
(*   部分和恒一（bxdef_esp_zero_series/BXB bxb_series_zero 同面） *)
(*   ⟹ 距离恒为 ‖bone+(−bone)‖=0 ⟹ N=0 闭式证书。               *)

Lemma bxoo_lim_esp_zero_bone : forall (B : BanachAlg),
  blim B (fun n : nat => exp_series_partial B (@bzero B) n) (@bone B).
Proof.
  intros B q Hq.
  refine (existT (fun N : nat => forall n : nat, NatLe N n ->
            QltT (@bnorm B (@bplus B (exp_series_partial B (@bzero B) n)
                                     (@bopp B (@bone B)))) q) 0%nat _).
  intros n Hn.
  pose proof (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bzero B) n)
               (@bopp B (@bone B)))
      (@bplus B (@bone B) (@bopp B (@bone B)))
      (@bplus_wd B (exp_series_partial B (@bzero B) n)
                  (@bopp B (@bone B))
                  (@bone B) (@bopp B (@bone B))
                  (bxdef_esp_zero_series B n)
                  (@bae_refl B (@bopp B (@bone B))))) as HW1.
  pose proof (@bnorm_wd B
      (@bplus B (@bone B) (@bopp B (@bone B)))
      (@bzero B)
      (@bplus_opp B (@bone B))) as HW2.
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW1)).
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW2)).
  rewrite (@bnorm_zero B).
  exact Hq.
Qed.

(* S1 机械件二（CD3 形→blim 换骨）：near-one 邻域形与 blim 形     *)
(*   在 l=bone 处逐字同构（blim u bone 展开=本假设形）。          *)
(*   CD3 连接槽：若 bxcd_prod_near_one 实形为                    *)
(*     forall B a q, QltT 0 q -> sigT N, forall n, NatLe N n ->  *)
(*       QltT (bnorm (bplus (esp a n·esp(bopp a) n) (bopp bone))) q*)
(*   则 bxoo_nearone_blim B _ (bxcd_prod_near_one B a) 一步上桥。 *)

Lemma bxoo_nearone_blim : forall (B : BanachAlg) (S : nat -> (@BA B)),
  (forall q : Q, QltT 0 q ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (@bnorm B (@bplus B (S n) (@bopp B (@bone B)))) q)) ->
  blim B S (@bone B).
Proof.
  intros B S H q Hq. exact (H q Hq).
Qed.

(* S1 机械件三（emul 整理件）：乘法结合对称面（非交换类下唯一     *)
(*   保安的整理形；类无 bmult_comm，交换面不可造，如实不强造）。   *)

Lemma bxoo_bmult_assoc_sym : forall (B : BanachAlg) (x y z : (@BA B)),
  @bae B (@bmult B (@bmult B x y) z) (@bmult B x (@bmult B y z)).
Proof.
  intros B x y z. exact (@bae_sym B _ _ (@bmult_assoc B x y z)).
Qed.

(* S2 UNQ 连接形状（Set 面）：同序列双极限 bae 相等——            *)
(*   主件必要件的形状钉。UNQ 落盘后若 bxuq_lim_uniq 与此同形，    *)
(*   连接= exact (bxuq_lim_uniq B)；若参序/类索引异形，           *)
(*   按本形状包一层换序适配（eps 留记为零，纯参序迁移）。          *)

Definition bxoo_uniq_shape (B : BanachAlg) : Set :=
  forall (u : nat -> (@BA B)) (x y : (@BA B)),
    blim B u x -> blim B u y -> @bae B x y.

(* S3 尾件（④，参数化于③）：bxdef_exp bzero == bone。            *)
(*   两条极限链同喂唯一性：bxdef_exp_spec（ExpDef 出口）+         *)
(*   bxoo_lim_esp_zero_bone（S1 机械件一）。                      *)

Lemma bxoo_bzero_eq_bone_assembly : forall (B : BanachAlg),
  bxoo_uniq_shape B -> @bae B (bxdef_exp B (@bzero B)) (@bone B).
Proof.
  intros B Hunq.
  exact (Hunq (fun n : nat => exp_series_partial B (@bzero B) n)
              (bxdef_exp B (@bzero B)) (@bone B)
              (bxdef_exp_spec B (@bzero B))
              (bxoo_lim_esp_zero_bone B)).
Qed.

(* S4 主装配件（①+②+③+④ 合取闭合，参数化于②③两闸门）：         *)
(*   bae (e^a·e^(−a)) (e^0) := bae_trans                          *)
(*     (唯一性：序列左极限 e^a·e^(−a) == 近邻极限 bone)            *)
(*     (对称(④尾件))。                                            *)
(*   全部装配步骤真实现（bae_trans 合取 + 唯一性两次使用 +         *)
(*   对称换向），唯②的 blim 槽与③的 uniq 槽为显式假设。           *)

Theorem bxoo_exp_opp_one_assembly : forall (B : BanachAlg) (a : (@BA B)),
  bxoo_uniq_shape B ->
  blim B (fun n : nat => @bmult B (exp_series_partial B a n)
                                  (exp_series_partial B (bopp a) n))
         (@bone B) ->
  @bae B (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
        (bxdef_exp B (@bzero B)).
Proof.
  intros B a Hunq Hnear.
  exact (@bae_trans B
           (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
           (@bone B)
           (bxdef_exp B (@bzero B))
           (Hunq (fun n : nat => @bmult B (exp_series_partial B a n)
                                  (exp_series_partial B (bopp a) n))
                 (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
                 (@bone B)
                 (bxadd_esp_prod_blim B a (bopp a))
                 Hnear)
           (@bae_sym B (bxdef_exp B (@bzero B)) (@bone B)
             (bxoo_bzero_eq_bone_assembly B Hunq))).
Qed.

(* S5 UNQ 闸闭合件（ o 落盘，检验预验后   *)
(* 正册获取）：bxdef_exp bzero == bone——Ext 层无条件 bae 全等式，  *)
(* B25 留记②「exp(0)=one 完全等式面」对 Ext 实例兑现。             *)

Corollary bxoo_bzero_eq_bone : forall (E : BanachAlgExt),
  @bae (@bxce_base E)
    (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E)))
    (@bone (@bxce_base E)).
Proof.
  intros E.
  apply (bxoo_bzero_eq_bone_assembly (@bxce_base E)).
  exact (bxuq_lim_uniq E).
Qed.

(*   ② CD12 真件 bxcd_prod_near_one（，          *)
(*     调用位随之去 bxce_coef_plus/bxce_coef_wd 两实参——             *)
(*     hplus/hwd 摘除后无须再喂字段，终面钉 Ext 层不变。              *)
(*   ③ bxuq_lim_uniq E 剥 E 后=bxoo_uniq_shape base 同构。          *)
(*   主件 bxoo_exp_opp_one：无条件 bae 全等式——                     *)
(*     bae_trans（唯一性：序列左极限 e^a·e^(−a) == 近邻极限 bone）   *)
(*     （对称（④尾件）），与 S4 装配件合取面逐字一致。              *)

Theorem bxoo_exp_opp_one : forall (E : BanachAlgExt)
  (a : (@BA (@bxce_base E))),
  @bae (@bxce_base E)
    (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                   (bxdef_exp (@bxce_base E) (@bopp (@bxce_base E) a)))
    (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E))).
Proof.
  intros E a.
  apply (bxoo_exp_opp_one_assembly (@bxce_base E) a
           (bxuq_lim_uniq E)).
  apply (bxoo_nearone_blim (@bxce_base E)).
  exact (bxcd_prod_near_one (@bxce_base E) a).
Qed.
(* ================= §2 s3c_hplus_of 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* 类字段→显式假设形供给锚（bnh 锚一同位：字段形≡假设形） *)
Definition s3c_hplus_of (B : BanachAlg)
  : forall q r : Q,
    @bae B (@bplus B (@bcoef B q) (@bcoef B r)) (@bcoef B (q + r)%Q)
  := @bcoef_plus B.

Definition s3c_hwd_of (B : BanachAlg)
  : forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)
  := fun q r Hq => @bcoef_wd B q r Hq.

(* ① E 载体无条件 exp_add（消 bxae_exp_add 的 hplus/hwd 显式钉）    *)

Theorem s3c_exp_add_base : forall (E : BanachAlgExt)
  (a b : (@BA (@bxce_base E))),
  @bae (@bxce_base E) (@bmult (@bxce_base E) a b)
       (@bmult (@bxce_base E) b a) ->
  @bae (@bxce_base E)
       (@bxdef_emul (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                    (bxdef_exp (@bxce_base E) b))
       (bxdef_exp (@bxce_base E) (@bplus (@bxce_base E) a b)).
Proof.
  intros E a b hab.
  exact (bxae_exp_add E a b hab).
Qed.

(* ② plain B 载体 exp_add 装配（六环合流：⑤左极限 + ④差小移位      *)
(*   + ⑥唯一性（假设化）；唯一性槽以 bxoo_uniq_shape 显式给出——     *)
(*   plain 类无 sep 字段，与 bxoo_exp_opp_one_assembly 同口径）      *)

Theorem s3c_exp_add_plain : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  bxoo_uniq_shape B ->
  @bae B (@bxdef_emul B (bxdef_exp B a) (bxdef_exp B b))
         (bxdef_exp B (@bplus B a b)).
Proof.
  intros B a b hab Hunq.
  unfold bxdef_emul.
  apply (Hunq (fun n : nat =>
                 @bmult B (exp_series_partial B a n)
                          (exp_series_partial B b n))).
  - (* ⑤ 左极限：部分积序列 → e^a·e^b *)
    exact (bxadd_esp_prod_blim B a b).
  - (* ④ 差小移位：部分积序列 → e^(a+b) *)
    apply (bxae_lim_shift B
             (fun n : nat =>
                @bmult B (exp_series_partial B a n)
                         (exp_series_partial B b n))
             (fun n : nat => exp_series_partial B (@bplus B a b) n)
             (bxdef_exp B (@bplus B a b))
             (bxdef_exp_spec B (@bplus B a b))).
    intros eps Heps.
    destruct (bxae_diff_small B a b hab eps Heps) as [N HN].
    exists N. intros n Hn.
    exact (HN n (NatLe_drop N n Hn)).
Qed.

(* ③ 可逆性合流：(e^a) 的逆元 = e^{-a}                              *)
(*   ③a Ext 载体无条件：e^a·e^{-a} == e^0 与 e^0 == bone 两绿件      *)

Theorem s3c_exp_opp_one_base : forall (E : BanachAlgExt)
  (a : (@BA (@bxce_base E))),
  @bae (@bxce_base E)
       (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                    (bxdef_exp (@bxce_base E) (@bopp (@bxce_base E) a)))
       (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E))).
Proof.
  intros E a. exact (bxoo_exp_opp_one E a).
Qed.

Theorem s3c_exp_inv_base : forall (E : BanachAlgExt)
  (a : (@BA (@bxce_base E))),
  @bae (@bxce_base E)
       (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                    (bxdef_exp (@bxce_base E) (@bopp (@bxce_base E) a)))
       (@bone (@bxce_base E)).
Proof.
  intros E a.
  apply (@bae_trans (@bxce_base E)
           (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                        (bxdef_exp (@bxce_base E) (@bopp (@bxce_base E) a)))
           (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E)))
           (@bone (@bxce_base E))).
  - exact (bxoo_exp_opp_one E a).
  - exact (bxoo_bzero_eq_bone E).
Qed.

(*   ③b plain 载体：bxoo_exp_opp_one_assembly 的 Hnear 槽闭合——     *)
(*   bxcd_prod_near_one 的 hplus/hwd 显式假设喂基类字段（S6 注记     *)
(*   「plain 喂不进」系类迁移前旧账，bnh 锚一后即通）。               *)

Theorem s3c_exp_opp_one_plain : forall (B : BanachAlg) (a : (@BA B)),
  bxoo_uniq_shape B ->
  @bae B (@bmult B (bxdef_exp B a) (bxdef_exp B (@bopp B a)))
         (bxdef_exp B (@bzero B)).
Proof.
  intros B a Hunq.
  apply (bxoo_exp_opp_one_assembly B a Hunq).
  apply (bxoo_nearone_blim B
           (fun n : nat =>
              @bmult B (exp_series_partial B a n)
                       (exp_series_partial B (@bopp B a) n))).
  exact (bxcd_prod_near_one B a).
Qed.

Theorem s3c_exp_inv_plain : forall (B : BanachAlg) (a : (@BA B)),
  bxoo_uniq_shape B ->
  @bae B (@bmult B (bxdef_exp B a) (bxdef_exp B (@bopp B a)))
         (@bone B).
Proof.
  intros B a Hunq.
  apply (@bae_trans B
           (@bmult B (bxdef_exp B a) (bxdef_exp B (@bopp B a)))
           (bxdef_exp B (@bzero B))
           (@bone B)).
  - exact (s3c_exp_opp_one_plain B a Hunq).
  - exact (bxoo_bzero_eq_bone_assembly B Hunq).
Qed.

(* G4 假设面自证（PA≥1：主件四件）                                  *)
Print Assumptions s3c_exp_add_base.
Print Assumptions s3c_exp_add_plain.
Print Assumptions s3c_exp_inv_base.
Print Assumptions s3c_exp_inv_plain.
