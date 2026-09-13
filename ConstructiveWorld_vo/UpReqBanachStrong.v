(* ========================================================================= *)
(* UpReqBanachStrong.v —— 席W8：路径 B 补强轨（双轨纪律的非弱化轨，20260913） *)
(* ========================================================================= *)
(* 使命：W5a 类手术把 bnorm_wd/bnorm_coef 余域 Id→QeqT 后，下游四件语句面被  *)
(* 运移形改写为 QeqT 弱化形。本席实现补强而非弱化：纯加性新文件，Require 消费 *)
(* 弱化件 + INSTB qnorm 链（bxib_qnorm gcd 正规化），逐位点恢复强形式。        *)
(* 零改任何既有件（双轨轨1=W7 注册的弱化形件保持原状）；本件前缀 bxst_。      *)
(*                                                                           *)
(* 强形式语义（诚实边界，INSTB 同位先例）：                                   *)
(*  - 一般抽象层无 QeqT→Id 桥（W5b 坑4），Qabs 原始钉定位的全量 Id 恢复被     *)
(*    bxib_canon_pin_wall 封死（会逼出 Id (2#4) (1#2) 假等式），故抽象层全量  *)
(*    Id 恢复为不可能目标，本席不做硬凑（完备性类挂账维持）；                 *)
(*  - 但经 bxib_qnorm 正规化，规范形位置的 Id 强形式定义级可证：              *)
(*    QeqT x y -> Id (bxib_qnorm x) (bxib_qnorm y)（bxib_qnorm_id_of_qeqT）； *)
(*  - INSTB 实例（bnorm:=Qabs∘qnorm∘head 规范架构）上同位语句为全量 Id 形    *)
(*    （bxib_bnorm_wd），本件以 bxst_inst_norm_wd_id 同位再出口。             *)
(*                                                                           *)
(* 交付分层：                                                                 *)
(*  S0 支持  bxst_qnorm_one / bxst_qabs_qnorm_one（字面规范件）               *)
(*  S1 保底  bxst_norm_wd_id / bxst_norm_coef_id（核心两墙 Id 强形式恢复）    *)
(*           + bxst_norm_coef_one / bxst_inst_norm_wd_id                     *)
(*  S2 主件  四处语句面弱化位点的强形式对应件（bxst_<原名>_strong）：          *)
(*           bxb_norm_series_zero / bxdef_esp_zero_bnorm /                   *)
(*           ncv_norm_diff_sym / bxcd_prod_close                             *)
(*                                                                           *)
(* 自审：公理面零新增（纯 Require 消费+结构化证明）；零承认件、零经典逻辑；   *)
(* 语句面全 Set 层（Id/QeqT/sigT 承载）；Prop 仅作证明引擎内衬不落语句面。    *)
(* ========================================================================= *)

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
Proof. apply id_refl. Qed.

(* Qabs∘qnorm 在 1 位的不动形（钉定面规范位） *)
Lemma bxst_qabs_qnorm_one : Id (Qabs (bxib_qnorm 1%Q)) (Qabs 1%Q).
Proof. apply id_refl. Qed.

(* ============================================================ *)
(* S1 保底件①：核心墙一 bnorm_wd 的 Id 强形式（规范形恢复）       *)
(*   原 Id 形：bae a b -> Id (bnorm a) (bnorm b)                  *)
(*   恢复形：规范形位置 Id（qnorm 链；抽象层全量恢复不可能如头注） *)
(* ============================================================ *)

Lemma bxst_norm_wd_id : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B a b -> Id (bxib_qnorm (@bnorm B a)) (bxib_qnorm (@bnorm B b)).
Proof.
  intros B a b H.
  exact (bxib_qnorm_id_of_qeqT _ _ (@bnorm_wd B a b H)).
Qed.

(* S1 保底件②：核心墙二 bnorm_coef 的 Id 强形式（规范形恢复）
   原 Id 形：Id (bnorm (bcoef q)) (Qabs q) *)
Lemma bxst_norm_coef_id : forall (B : BanachAlg) (q : Q),
  Id (bxib_qnorm (@bnorm B (@bcoef B q))) (bxib_qnorm (Qabs q)).
Proof.
  intros B q.
  exact (bxib_qnorm_id_of_qeqT _ _ (@bnorm_coef B q)).
Qed.

(* S1 伴件：标量 1 位的全量字面 Id 形（qnorm 1 = 1 收尾） *)
Lemma bxst_norm_coef_one : forall (B : BanachAlg),
  Id (bxib_qnorm (@bnorm B (@bcoef B 1%Q))) 1%Q.
Proof.
  intros B.
  exact (id_trans (bxst_norm_coef_id B 1%Q) bxst_qnorm_one).
Qed.

(* S1 伴件：INSTB 规范实例同位语句的全量 Id 形（定义级，INSTB 已证，
   本席同位再出口使补强轨自足） *)
Lemma bxst_inst_norm_wd_id : forall (a b : bxib_E),
  bxib_bae a b -> Id (bxib_bnorm a) (bxib_bnorm b).
Proof. exact bxib_bnorm_wd. Qed.

(* ============================================================ *)
(* S2 主件：四处语句面弱化位点的强形式对应件                      *)
(* ============================================================ *)

(* 主件①：ExpBasic bxb_norm_series_zero（原 Id (bnorm (esp B bzero m)) 1） *)
Lemma bxst_bxb_norm_series_zero_strong : forall (B : BanachAlg) (m : nat),
  Id (bxib_qnorm (@bnorm B (exp_series_partial B (@bzero B) m))) 1%Q.
Proof.
  intros B m.
  exact (id_trans (bxib_qnorm_id_of_qeqT _ _ (bxb_norm_series_zero B m))
                  bxst_qnorm_one).
Qed.

(* 主件②：ExpDef bxdef_esp_zero_bnorm（原 Id (bnorm (esp B bzero n)) 1） *)
Lemma bxst_bxdef_esp_zero_bnorm_strong : forall (B : BanachAlg) (n : nat),
  Id (bxib_qnorm (@bnorm B (exp_series_partial B (@bzero B) n))) 1%Q.
Proof.
  intros B n.
  exact (id_trans (bxib_qnorm_id_of_qeqT _ _ (bxdef_esp_zero_bnorm B n))
                  bxst_qnorm_one).
Qed.

(* 主件③：NormConv ncv_norm_diff_sym
   （原 Id (bnorm (bplus x (bopp y))) (bnorm (bplus y (bopp x)))） *)
Lemma bxst_ncv_norm_diff_sym_strong : forall (B : BanachAlg) (x y : (@BA B)),
  Id (bxib_qnorm (@bnorm B (@bplus B x (@bopp B y))))
     (bxib_qnorm (@bnorm B (@bplus B y (@bopp B x)))).
Proof.
  intros B x y.
  exact (bxib_qnorm_id_of_qeqT _ _ (ncv_norm_diff_sym B x y)).
Qed.

(* 主件④：CauchyD bxcd_prod_close（W5b 语句面运移位 L584；
   原 Id (bnorm (bplus (bmult (esp a n) (esp (bopp a) n)) (bopp bone))) (bnorm U)） *)
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
  exact (bxib_qnorm_id_of_qeqT _ _ (bxcd_prod_close B a n U H)).
Qed.

(* —— 席W8 补强轨收口：保底两墙 + 四处语句面弱化位点强形式全对应 —— *)
