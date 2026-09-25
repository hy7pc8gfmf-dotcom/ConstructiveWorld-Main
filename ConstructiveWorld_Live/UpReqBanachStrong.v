(* ═════════════════════════════════════════════════════════════════════ *)
(* UpReqBanachStrong.v —— 语句面弱化形下游的强形式恢复件                    *)
(* 使命：本件形式化 INSTB qnorm 规范形位置上的 Id 强形式：bnorm_wd 与       *)
(*       bnorm_coef 两个核心引理的 Id 恢复形，以及 bxb_norm_series_zero／   *)
(*       bxdef_esp_zero_bnorm／ncv_norm_diff_sym／bxcd_prod_close 四处      *)
(*       QeqT 弱化位点的 bxst_<原名>_strong 强形式对应件。                  *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp、       *)
(*       UpReqBanachInstB、UpReqBanachExpBasic、UpReqBanachExpDef、         *)
(*       UpReqNormConv、UpReqBanachCauchyD。                               *)
(* 对标：stdlib ZArith 的 gcd／div 正规化；Banach 代数范数公理组。          *)
(* 构造性注记：Set 层承载——语句面全 Id/QeqT/sigT，Prop 仅作证明引擎内衬     *)
(*   不落语句面；零承认、公理面为空、零经典逻辑；纯加性新文件，零改既有件，  *)
(*   本件前缀 bxst_；非平凡交付；Proof./Qed. 配平。                        *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 温控包装，-Q 单根。                   *)
(* ═════════════════════════════════════════════════════════════════════ *)
(* 使命背景：bnorm_wd/bnorm_coef 余域由 Id 改为 QeqT 后，下游四件语句面被   *)
(* 改写为 QeqT 弱化形。本件恢复强形式：Require 使用弱化件 + INSTB qnorm 链  *)
(* （bxib_qnorm gcd 正规化），逐位点恢复强形式。                            *)
(*                                                                       *)
(* 强形式语义（诚实边界，INSTB 同位先例）：                                 *)
(*  - 一般抽象层无 QeqT→Id 桥，Qabs 原始钉定位的全量 Id 恢复被              *)
(*    bxib_canon_pin_wall 阻断（会逼出 Id (2#4) (1#2) 假等式），故抽象层    *)
(*    全量 Id 恢复为不可能目标，完备性类未消解项维持；                      *)
(*  - 但经 bxib_qnorm 正规化，规范形位置的 Id 强形式定义级可证：            *)
(*    QeqT x y -> Id (bxib_qnorm x) (bxib_qnorm y)（bxib_qnorm_id_of_qeqT）； *)
(*  - INSTB 实例（bnorm:=Qabs∘qnorm∘head 规范架构）上同位语句为全量 Id 形  *)
(*    （bxib_bnorm_wd），本件以 bxst_inst_norm_wd_id 同位再出口。           *)
(*                                                                       *)
(* 分层结构：                                                               *)
(*  S0 字面规范支持件  bxst_qnorm_one / bxst_qabs_qnorm_one                 *)
(*  S1 核心恢复件      bxst_norm_wd_id / bxst_norm_coef_id（两个核心引理    *)
(*                     的 Id 强形式恢复）+ bxst_norm_coef_one /              *)
(*                     bxst_inst_norm_wd_id                                 *)
(*  S2 主件            四处语句面弱化位点的强形式对应件                     *)
(*                     （bxst_<原名>_strong）：                             *)
(*                     bxb_norm_series_zero / bxdef_esp_zero_bnorm /        *)
(*                     ncv_norm_diff_sym / bxcd_prod_close                  *)
(*                                                                       *)
(* 自审：公理面零新增（纯 Require 使用+结构化证明）；零承认件、零经典逻辑； *)
(* 语句面全 Set 层（Id/QeqT/sigT 承载）；Prop 仅作证明引擎内衬不落语句面。  *)
(* ═════════════════════════════════════════════════════════════════════ *)

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
