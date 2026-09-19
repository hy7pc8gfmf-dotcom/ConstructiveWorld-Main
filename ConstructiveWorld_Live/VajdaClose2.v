Set Printing Width 500.
(* ============================================================ *)
(* VajdaClose2.v —— 席 CZV13（批次 E-STAGING-CZV13）                 *)
(*   T84 真欠账前两笔攻歼（T84 §4 UpReqVajdaBound 残账 2 笔）：        *)
(*                                                                *)
(*   靶1 vjc_kl_term_self：UpReqVajdaBound :116-120 挂账槽           *)
(*      vb_kl_term_self 独立收口（端点锐性 kl_term 自形）。           *)
(*      实勘勘误（以源件实形为准）：T84 勘账「卡点=库内缺            *)
(*      real_eq_opp_compat」已陈旧——RealSetoid.real_eq_opp_compat    *)
(*      在库（S07_RealSetoidExpLog.v:255），且源件 :592 已在消费；    *)
(*      源件内该逻辑只以 vb_sharp_endpoint_zero 证内 assert Hgen      *)
(*      （:575-597）inline 存在，无独立定名件。本靶按该配方独立成件。  *)
(*                                                                *)
(*   靶2 vjc_vajda_sat_log2_direct：:135 申报直形收口。               *)
(*      实勘偏差（以源件实形为准）：T84 勘账「vb_vajda_sat_log2 仅    *)
(*      :135 注记」与源件不符——§W8 :820 已落地 conjunction 形         *)
(*      vb_vajda_sat_log2（vo 基座四关绿在案）。本件不改写已落地件    *)
(*      （CXC4 防重复施工），补两件：① QleT' Set 层交叉相乘数值证书   *)
(*      vjc_l2hi9_cap_T（n=9 上包络 vb_l2hi9 ≤ 18/25，vm_compute     *)
(*      判定 Qle_bool，交叉积 836623175 ≤ 838053216 的计算反映）；    *)
(*      ② :135 申报直形 c3e_ln2_real ≤_B KL₂（V ≥ 17/20 段），        *)
(*      消费自产证书链 + 已落地 vb_ln2_upper_env / vb_vajda_sat。     *)
(*                                                                *)
(* 消费面（全只读）：219（S02 QleT' 桥 / S07 RealSetoid 相容族 /       *)
(*   S08 real_kl_term·real_log·real_inv_pos 族）、UpRealLeB           *)
(*   real_le_to_le_b、UpReqPinskerTransport pnt_le_b_trans·           *)
(*   pnt_ring_eq、UpReqConstEnvelope c3e_ln2_real、PinskerTwoPoint    *)
(*   p2_tvsq、UpReqVajdaBound vb_opp_zero·vb_const_le·vb_l2hi9·      *)
(*   vb_ln2_upper_env·vb_vajda_sat。                                  *)
(* 红线自审：公理面零禁用件（本头注为自审句，不引禁词字面量）；          *)
(*   新语句面全 Set（real_eq / real_le_b / QleT'），零新造 Prop 命题； *)
(*   Prop 仅证码内消费（QleT'_to_Qle 桥进 vb_const_le 既有签名）；     *)
(*   全真证 Qed 零 Admitted；Extraction 探针验 Obj.magic=0。           *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lqa Lia.
From Stdlib Require Import Arith.Arith.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqTVAbsEps.
Require Import UpReqPinskerTransport.
Require Import UpReqConstEnvelope.
Require Import PinskerTwoPoint.
Require Import UpReqVajdaBound.

(* ============================================================ *)
(* §A 靶1：vb_kl_term_self 独立收口                                  *)
(*   语句形 = 挂账注释 :116-120 预期（real_kl_term p p 逐点 == 0）：   *)
(*   p·inv p == 1 一致 → real_log_wd → real_log_one →                *)
(*   mult/opp 相容链（RealSetoid.real_eq_opp_compat 在库直喂）→       *)
(*   pnt_ring_eq 收口。                                               *)
(* ============================================================ *)

Theorem vjc_kl_term_self : forall (p : Real) (Hp : real_lt real_zero p),
  real_eq (real_kl_term p p Hp Hp) real_zero.
Proof.
  intros p Hp.
  assert (Hone : real_eq (real_mult p (real_inv_pos p Hp)) real_one)
    by exact (real_inv_pos_correct p Hp).
  assert (Hlog : real_eq (real_log (real_mult p (real_inv_pos p Hp))
                             (real_mult_positive p (real_inv_pos p Hp) Hp
                                (real_inv_pos_pos p Hp)))
                         real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - apply (real_log_wd _ real_one _ real_lt_zero_one Hone).
    - exact (real_log_one real_lt_zero_one). }
  unfold real_kl_term.
  apply (real_eq_trans _ (real_mult p (real_opp real_zero)) _).
  - apply (RealSetoid.real_eq_mult_compat p
             (real_opp (real_log (real_mult p (real_inv_pos p Hp))
                                    (real_mult_positive p (real_inv_pos p Hp) Hp
                                       (real_inv_pos_pos p Hp)))) p (real_opp real_zero)).
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_opp_compat. exact Hlog.
  - apply (real_eq_trans _ (real_mult p real_zero) _).
    + apply (RealSetoid.real_eq_mult_compat p (real_opp real_zero) p real_zero).
      * apply real_eq_refl.
      * exact vb_opp_zero.
    + pnt_ring_eq.
Qed.

(* ============================================================ *)
(* §B 靶2：QleT' 交叉相乘数值证书 + :135 申报直形                     *)
(* ============================================================ *)

(* B1 n=9 上包络帽的 Set 层判定证书：vb_l2hi9 = Σ₉ + 1/20 ≤ 18/25。
   Qle_bool 对闭项计算判定（交叉积 836623175 ≤ 838053216 的 bool 反映），
   Id true 由 reflexivity 收——与源件 vb_l2sum9_cap（Qle/Prop 面
   Qle_bool_imp_le + vm_compute）互为冗余双证书，本件走 Set 面。 *)
Lemma vjc_l2hi9_cap_T : QleT' vb_l2hi9 (18#25).
Proof. unfold QleT'. vm_compute. reflexivity. Qed.

(* B2 帽提升到 Real 层常值序（QleT' → Qle 经 S02 双向桥，进既有
   vb_const_le 装载；语句面 real_le_b 为 Set）。 *)
Lemma vjc_l2hi9_cap_le_b : real_le_b (real_const vb_l2hi9) (real_const (18#25)).
Proof.
  apply real_le_to_le_b. apply vb_const_le.
  apply QleT'_to_Qle. exact vjc_l2hi9_cap_T.
Qed.

(* B3 :135 申报直形：饱和段（289/400 ≤ TV²）下 ln 2 柯西实数 ≤_B KL₂。
   直形 = c3e_ln2_real ≤ 18/25（vb_ln2_upper_env n=9 单边上包络 +
   B1 自产帽）接 18/25 ≤ KL₂（已落地 vb_vajda_sat），pnt_le_b_trans 焊接。
   注：源件 :820 落地的是 conjunction 形（18/25 ≤ KL₂ 且 ln2 ≤ 18/25），
   本直形为其 trans 闭合新语句，非重复施工。 *)
Theorem vjc_vajda_sat_log2_direct : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hne : Or (real_lt p q) (real_lt q p))
  (Hsat : real_le (real_const (289#400)) (p2_tvsq p q)),
  real_le_b c3e_ln2_real (vb_kl2 p q Hp Hq H1p H1q).
Proof.
  intros p q Hp Hq H1p H1q Hne Hsat.
  apply (pnt_le_b_trans c3e_ln2_real (real_const (18#25))
           (vb_kl2 p q Hp Hq H1p H1q)).
  - apply (pnt_le_b_trans c3e_ln2_real (real_const vb_l2hi9)
             (real_const (18#25))).
    + exact vb_ln2_upper_env.
    + exact vjc_l2hi9_cap_le_b.
  - exact (vb_vajda_sat p q Hp Hq H1p H1q Hne Hsat).
Qed.

Print Assumptions vjc_kl_term_self.
Print Assumptions vjc_vajda_sat_log2_direct.

Extraction "vjc_ex_probe.ml" vjc_kl_term_self vjc_vajda_sat_log2_direct.
