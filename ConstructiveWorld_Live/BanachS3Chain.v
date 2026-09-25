(* ============================================================ *)
(* Banach 路径 B S3 链对账收口 + 总装（纯装配层，零重证）          *)
(* ============================================================ *)
(* 使命：UpReqBanachExp.v:470 S3 挂账「交换 exp_add 总装 +        *)
(*   (e^a)^{-1}=e^{-a} 可逆性」的真缺口收口。对账定谳：            *)
(*   上游全绿——bnh_bpow_add（BanachNoHyp 二项式，hplus/hwd 双摘除）*)
(*   + bxae 中段件（UpReqBanachExpAddEq plain B 级数重组链）        *)
(*   + bd2_diag/esp_prod_square（UpReqBanachDouble/CauchyD）。      *)
(*   真缺三处（本件施工面，全部消费已证件装配，不重写任何 bxae_/    *)
(*   bnh_/binv_/bxoo_/bxcd_ 定理）：                                *)
(*   ① E 载体无条件面：bxae_exp_add 钉着显式 hplus/hwd，而基类      *)
(*      BanachAlg 已迁入 bcoef_plus/bcoef_wd 字段（bnh 锚一已定谳   *)
(*      「字段形≡假设形」）——直接喂参消钉。                        *)
(*   ② plain B 载体版 exp_add：bxadd_esp_prod_blim（左极限）+       *)
(*      bxae_lim_shift（差小移位）+ bxae_diff_small（尾差估计，喂    *)
(*      类字段）+ bxoo_uniq_shape（假设化唯一性，plain 无 sep 字段） *)
(*      四件合流。                                                  *)
(*   ③ 可逆性合流：bxoo_exp_opp_one（e^a·e^{-a}==e^0，Ext 无条件）  *)
(*      与 bxoo_bzero_eq_bone（e^0==bone）两件在库但从未合流——补     *)
(*      bae_trans 合流件（Ext 面无条件）+ plain 面两槽收口           *)
(*      （bxcd_prod_near_one 喂类字段 + bxoo_bzero_eq_bone_assembly）*)
(*      得 (e^a) 的逆元见证 e^{-a}：e^a·e^{-a}==bone。               *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachProd.
Require Import UpReqBanachAdd.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachDouble.
Require Import UpReqBanachCauchyD.
Require Import UpReqBanachLimUniq.
Require Import UpReqBanachClassExt.
Require Import BanachNoHyp.
Require Import UpReqBanachExpAddEq.
Require Import UpReqBanachExpOppOne.
Require Import UpReqBanachInvPre.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* 类字段→显式假设形喂参锚（bnh 锚一同位：字段形≡假设形） *)
Definition s3c_hplus_of (B : BanachAlg)
  : forall q r : Q,
    @bae B (@bplus B (@bcoef B q) (@bcoef B r)) (@bcoef B (q + r)%Q)
  := @bcoef_plus B.

Definition s3c_hwd_of (B : BanachAlg)
  : forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)
  := fun q r Hq => @bcoef_wd B q r Hq.

(* ============================================================ *)
(* ① E 载体无条件 exp_add（消 bxae_exp_add 的 hplus/hwd 显式钉）    *)
(* ============================================================ *)

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

(* ============================================================ *)
(* ② plain B 载体 exp_add 总装（六环合流：⑤左极限 + ④差小移位      *)
(*   + ⑥唯一性（假设化）；唯一性槽以 bxoo_uniq_shape 显式给出——     *)
(*   plain 类无 sep 字段，与 bxoo_exp_opp_one_assembly 同口径）      *)
(* ============================================================ *)

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

(* ============================================================ *)
(* ③ 可逆性合流：(e^a) 的逆元 = e^{-a}                              *)
(*   ③a Ext 载体无条件：e^a·e^{-a} == e^0 与 e^0 == bone 两绿件      *)
(*      bae_trans 合流——正册两件分立、无合流位（对账实缺）。         *)
(* ============================================================ *)

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

(*   ③b plain 载体：bxoo_exp_opp_one_assembly 的 Hnear 槽收口——     *)
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

(* ============================================================ *)
(* G4 假设面自证（PA≥1：主件四件）                                  *)
(* ============================================================ *)
Print Assumptions s3c_exp_add_base.
Print Assumptions s3c_exp_add_plain.
Print Assumptions s3c_exp_inv_base.
Print Assumptions s3c_exp_inv_plain.
