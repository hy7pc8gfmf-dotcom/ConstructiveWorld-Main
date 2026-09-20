(* ============================================================ *)
(* UpAblSlackMix.v —— 席 N1：非几何率·松弛形算法化（2026-09-20）       *)
(*                                                                *)
(* 三件（slm_ 前缀；全树 grep 零撞名 20260920 实测）：                  *)
(*   件① slm_slack_select（±_le）—— 抽象松弛组合定理：                  *)
(*     对任意率 κ、松弛基量 A、预算 B，给四正性/界证书 + 「松弛率界」     *)
(*     接口前件 Hsl（照 cf2_tv_iter_mu0 界形：rate n ≤ κⁿ·A + n·eps      *)
(*     逐 eps），则返回显式步 k := S k_g 使 rate k < B（_le 形一跳）。    *)
(*     路线 = 预算劈半：几何半边消费 UpReqMixingTime 的无条件件选择器     *)
(*     mix_k_select（前件仅四正性/界，零 k₀、零几何前提）对 (κ,A,B/2)    *)
(*     取 k_g；收缩腿 κ^{S k_g}·A ≤ κ^{k_g}·A 自建 slm_pow_mult_nonneg   *)
(*     供给（κ 幂乘积非负）；线性半边 eps := (1/n)·(B/4) 于候选点         *)
(*     n := S k_g 自举（reqd_nat_to_R 正性 + cf2_inv_cancel 消逆得       *)
(*     n·eps req= B/4）；合流 = B/4 < B/2（cf2_inv2_lt_one）+            *)
(*     B/2 + B/2 = B（cf2_two_inv_budget）。                             *)
(*   件② slm_cf2_mixing_full —— Fin2 无条件升级（零 k₀ 前件版）：        *)
(*     ∀B>0, sigT k, cf2_tv(titer k mu0, titer k nu0) < B。              *)
(*     消费件①（rate := cf2_tv ∘ titer 对、κ := cf2_omd、A := TV₀）      *)
(*     + cf2_tv_iter_mu0 供 Hsl + cf2_omd_pos/cf2_tv_nonneg 供证书；     *)
(*     κ < 1 由 slm_omd_lt_one 自 cf2_ds_pos + cf2_aux_ds_omd 构造       *)
(*     （igr_lt_plus_r 严格平移）。升级声明：非降档——原 T7 旗舰          *)
(*     cf2_mixing_time_le 的 k₀ 输入前件与几何衰减前提由此被内部化       *)
(*     消去（k₀ 从输入变为件①内部算出），原形作为推论完整保留。          *)
(*   件③ slm_cf2_le_of_full —— 换装推论（向后兼容）：原 cf2_mixing_     *)
(*     time_le 的语句面从件②一跳直推（k₀/几何前件在此为冗余，本件照      *)
(*     原语句面全数保留，向后兼容旧消费面）。                             *)
(*                                                                *)
(* 上游（零改母本）：CW219 基座伞壳 + UpTVDoeblin（tv_rpow 面仅供       *)
(*   mix_k_select 消费换形）+ UpReqIterGeomRate（igr_lt_plus_r）+        *)
(*   UpReqConcFin2（cf2 界形/inv_two/inv_cancel/two_inv_budget 帮件族）  *)
(*   + UpReqMixingTime（mix_k_select 无条件 k 选择器）。                 *)
(*   换形垫片说明：tv_rpow/real_mult/real_lt 面与 req_r_pow/mult/lt 面    *)
(*   在 Real 基座上同体（RealEnhancedReal 实例字段逐位绑定 real_* 族，    *)
(*   两个 Fixpoint 归约同形），mix_k_select 结论经转换一跳直喂，零新增   *)
(*   独立垫片件。                                                        *)
(* 红线自审：①全件零承认字面、零经典逻辑（证明仅 destruct/精确项式）；   *)
(*   ②语句面全 Set 层（量词 nat/Real；比较全 lt/le/req；sigT 第二分量    *)
(*   为 Set）；③三主件全非平凡真实现、全 Defined 可提取。                *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 清空，cpu_guard 包裹全量编译）：  *)
(*   coqc -q -native-compiler no -Q . "" UpAblSlackMix.v                 *)
(* ============================================================ *)
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqConcFin2.
Require Import UpReqMixingTime.
Import RealInterfaceEnhancedMod.

(* ---- 帮件一：κ 幂乘积非负（收缩腿的证书供给，对任意 κ ≤ 1 与 A ≥ 0） ---- *)

Lemma slm_pow_mult_nonneg : forall (kappa A : Real),
  le zero kappa -> le kappa one -> le zero A ->
  forall (n : nat), le zero (mult (req_r_pow kappa n) A).
Proof.
  intros kappa A Hk0 Hk1 HA n.
  induction n as [| m IH].
  - exact (le_id_r zero A (mult (req_r_pow kappa 0%nat) A)
             (req_sym _ _ (cf2_mult_one_l A)) HA).
  - assert (Hmid : le (mult kappa (mult (req_r_pow kappa m) A))
                      (mult (req_r_pow kappa m) A))
      by (exact (cf2_le_mult_one kappa (mult (req_r_pow kappa m) A) IH Hk1)).
    assert (Hz : le zero (mult kappa (mult (req_r_pow kappa m) A)))
      by (exact (le_id_l zero (mult zero (mult (req_r_pow kappa m) A))
                   (mult kappa (mult (req_r_pow kappa m) A))
                   (req_sym _ _
                      (req_trans (mult zero (mult (req_r_pow kappa m) A))
                                 (mult (mult (req_r_pow kappa m) A) zero)
                                 zero
                                 (mult_comm zero
                                    (mult (req_r_pow kappa m) A))
                                 (mult_zero (mult (req_r_pow kappa m) A))))
                   (le_mult_compat_weak zero kappa
                      (mult (req_r_pow kappa m) A) IH Hk0))).
    exact (le_id_r zero (mult kappa (mult (req_r_pow kappa m) A))
             (mult (mult kappa (req_r_pow kappa m)) A)
             (mult_assoc kappa (req_r_pow kappa m) A) Hz).
Defined.

(* ---- 帮件二：tv_rpow 面与 req_r_pow 面的换形垫片（归纳桥，req 逐位） ----
   两 Fixpoint 参数结构不同（req_r_pow 带 R/RIS 参数），stuck 点上转换
   不闭合，故按归纳构造 req 桥；基座 Real 上两幂同体归约。 *)

Lemma slm_rpow_tvpow : forall (kappa : Real) (n : nat),
  req (req_r_pow kappa n) (tv_rpow kappa n).
Proof.
  intros kappa n.
  induction n as [| m IH].
  - exact (req_refl (tv_rpow kappa 0%nat)).
  - exact (req_mult_compat kappa kappa (req_r_pow kappa m)
             (tv_rpow kappa m) (req_refl kappa) IH).
Defined.

(* ---- 件①：抽象松弛组合定理（率界接口 + 无条件选择器，零 k₀ 前件） ----
   四证书照 mix_k_select 前件面（0<κ<1、0≤A、0<B）；Hsl 为「松弛率界」
   接口：rate n ≤ κⁿ·A + n·eps 对每个 eps>0（cf2_tv_iter_mu0 界形的
   抽象化）。结论：显式返回 k := S k_g 使 rate k < B（_le 形推论随后）。 *)

Theorem slm_slack_select : forall (rate : nat -> Real) (kappa A budget : Real),
  lt zero kappa -> lt kappa one ->
  le zero A -> lt zero budget ->
  (forall (n : nat) (eps : Real), lt zero eps ->
     le (rate n) (plus (mult (req_r_pow kappa n) A)
                       (mult (reqd_nat_to_R n) eps))) ->
  sigT (fun k : nat => lt (rate (Datatypes.S k)) budget).
Proof.
  intros rate kappa A budget Hk1 Hk2 HA Hbudget Hsl.
  assert (Hk0 : le zero kappa)
    by (exact (lt_le_iff zero kappa (inl Hk1))).
  assert (Hk2le : le kappa one)
    by (exact (lt_le_iff kappa one (inl Hk2))).
  assert (Hinv2pos : lt zero cf2_inv_two)
    by (exact (inv_pos_pos (plus one one) req_two_pos)).
  assert (HX0 : lt zero (mult cf2_inv_two budget))
    by (exact (mult_positive cf2_inv_two budget Hinv2pos Hbudget)).
  assert (HY0 : lt zero (mult cf2_inv_two (mult cf2_inv_two budget)))
    by (exact (mult_positive cf2_inv_two (mult cf2_inv_two budget)
                Hinv2pos HX0)).
  (* 几何半边：无条件件选择器对 (κ, A, B/2) 取 k_g（零 k₀、零几何前提） *)
  destruct (mix_k_select kappa A (mult cf2_inv_two budget) Hk1 Hk2 HA HX0)
    as [kg Hkg].
  (* 换形垫片：tv_rpow/real_mult 面 -> req_r_pow/mult 面
     （slm_rpow_tvpow 归纳桥 + req_mult_compat/req_lt_compat 换形） *)
  assert (HkgI : lt (mult (req_r_pow kappa kg) A)
                    (mult cf2_inv_two budget)).
  { exact (req_lt_compat (mult (tv_rpow kappa kg) A)
             (mult (req_r_pow kappa kg) A)
             (mult cf2_inv_two budget) (mult cf2_inv_two budget)
             (req_mult_compat (tv_rpow kappa kg) (req_r_pow kappa kg) A A
                (req_sym _ _ (slm_rpow_tvpow kappa kg)) (req_refl A))
             (req_refl (mult cf2_inv_two budget))
             Hkg). }
  (* 收缩腿：κ^{S k_g}·A ≤ κ^{k_g}·A *)
  assert (Hshr : le (mult (req_r_pow kappa (Datatypes.S kg)) A)
                    (mult (req_r_pow kappa kg) A)).
  { exact (le_id_l (mult (mult kappa (req_r_pow kappa kg)) A)
             (mult kappa (mult (req_r_pow kappa kg) A))
             (mult (req_r_pow kappa kg) A)
             (req_sym _ _ (mult_assoc kappa (req_r_pow kappa kg) A))
             (cf2_le_mult_one kappa (mult (req_r_pow kappa kg) A)
                (slm_pow_mult_nonneg kappa A Hk0 Hk2le HA kg) Hk2le)). }
  assert (Hgeolt : lt (mult (req_r_pow kappa (Datatypes.S kg)) A)
                      (mult cf2_inv_two budget))
    by (exact (le_lt_trans _ _ _ Hshr HkgI)).
  (* 线性半边：eps := (1/n)·(B/4) 于候选点 n := S k_g 自举（正性 + 消逆） *)
  assert (Heps : lt zero (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                          (reqd_nat_to_R_pos kg))
                               (mult cf2_inv_two (mult cf2_inv_two budget))))
    by (exact (mult_positive (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                       (reqd_nat_to_R_pos kg))
                             (mult cf2_inv_two (mult cf2_inv_two budget))
                             (inv_pos_pos (reqd_nat_to_R (Datatypes.S kg))
                                          (reqd_nat_to_R_pos kg))
                             HY0)).
  assert (Hiter : le (rate (Datatypes.S kg))
                    (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                          (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (le_id_r (rate (Datatypes.S kg))
             (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                   (mult (reqd_nat_to_R (Datatypes.S kg))
                      (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                     (reqd_nat_to_R_pos kg))
                            (mult cf2_inv_two (mult cf2_inv_two budget)))))
             (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (req_plus_compat
                (mult (req_r_pow kappa (Datatypes.S kg)) A)
                (mult (req_r_pow kappa (Datatypes.S kg)) A)
                (mult (reqd_nat_to_R (Datatypes.S kg))
                   (mult (inv_pos (reqd_nat_to_R (Datatypes.S kg))
                                  (reqd_nat_to_R_pos kg))
                         (mult cf2_inv_two (mult cf2_inv_two budget))))
                (mult cf2_inv_two (mult cf2_inv_two budget))
                (req_refl (mult (req_r_pow kappa (Datatypes.S kg)) A))
                (cf2_inv_cancel (mult cf2_inv_two (mult cf2_inv_two budget))
                   kg))
             (Hsl (Datatypes.S kg) _ Heps)). }
  (* 合流：B/4 < B/2 严格腿 + B/2 + B/2 = B 找零（cf2 帮件族逐字轨） *)
  assert (HYX : lt (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult cf2_inv_two budget)).
  { exact (lt_id_r (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult one (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (cf2_mult_one_l (mult cf2_inv_two budget))
             (lt_mult_compat cf2_inv_two one (mult cf2_inv_two budget)
                HX0 cf2_inv2_lt_one)). }
  assert (Hcomb : lt (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                           (mult cf2_inv_two (mult cf2_inv_two budget)))
                     (plus (mult cf2_inv_two budget)
                           (mult cf2_inv_two budget))).
  { exact (cf2_lt_plus_compat_lt_le
             (mult (req_r_pow kappa (Datatypes.S kg)) A)
             (mult cf2_inv_two budget)
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             Hgeolt (lt_le_iff (mult cf2_inv_two (mult cf2_inv_two budget))
                        (mult cf2_inv_two budget) (inl HYX))). }
  exact (existT (fun k : nat => lt (rate (Datatypes.S k)) budget)
           kg
           (le_lt_trans (rate (Datatypes.S kg))
              (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                    (mult cf2_inv_two (mult cf2_inv_two budget)))
              budget Hiter
              (lt_id_r (plus (mult (req_r_pow kappa (Datatypes.S kg)) A)
                             (mult cf2_inv_two (mult cf2_inv_two budget)))
                       (plus (mult cf2_inv_two budget)
                             (mult cf2_inv_two budget))
                       budget (cf2_two_inv_budget budget) Hcomb))).
Defined.

(* ---- 件① le 形推论（一跳：严格腿走 Or 左支） ---- *)

Corollary slm_slack_select_le :
  forall (rate : nat -> Real) (kappa A budget : Real),
  lt zero kappa -> lt kappa one ->
  le zero A -> lt zero budget ->
  (forall (n : nat) (eps : Real), lt zero eps ->
     le (rate n) (plus (mult (req_r_pow kappa n) A)
                       (mult (reqd_nat_to_R n) eps))) ->
  sigT (fun k : nat => le (rate (Datatypes.S k)) budget).
Proof.
  intros rate kappa A budget Hk1 Hk2 HA Hbudget Hsl.
  destruct (slm_slack_select rate kappa A budget Hk1 Hk2 HA Hbudget Hsl)
    as [k Hk].
  exact (existT (fun k : nat => le (rate (Datatypes.S k)) budget) k
           (lt_le_iff (rate (Datatypes.S k)) budget (inl Hk))).
Defined.

(* ---- 帮件二：cf2_omd < 1（δ* > 0 严格平移：omd < omd + δ* = 1） ---- *)

Lemma slm_omd_lt_one : lt cf2_omd one.
Proof.
  exact (lt_id_r cf2_omd (plus cf2_omd cf2_delta_star) one
           (req_trans (plus cf2_omd cf2_delta_star)
                      (plus cf2_delta_star cf2_omd) one
                      (plus_comm cf2_omd cf2_delta_star)
                      cf2_aux_ds_omd)
           (igr_lt_plus_r cf2_omd cf2_delta_star cf2_ds_pos)).
Defined.

(* ---- 件②：Fin2 无条件升级（零 k₀ 前件版） ----
   原 T7 旗舰 cf2_mixing_time_le 的 k₀ 输入前件与几何衰减前提
   （omd^{k0}·TV₀ ≤ B/2）由此内部化消去：k₀ 不再是输入，而由件①的
   无条件选择器在预算劈半内算出。升级声明：非降档。 *)

Theorem slm_cf2_mixing_full : forall budget : Real,
  lt zero budget ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget Hbudget.
  destruct (slm_slack_select
              (fun n : nat => cf2_tv (cf2_titer n cf2_mu0)
                                     (cf2_titer n cf2_nu0))
              cf2_omd (cf2_tv cf2_mu0 cf2_nu0) budget
              cf2_omd_pos slm_omd_lt_one cf2_tv_nonneg Hbudget
              cf2_tv_iter_mu0) as [k Hk].
  exact (existT (fun k : nat =>
            lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget)
           (Datatypes.S k) Hk).
Defined.

(* ---- 件③：换装推论（向后兼容） ----
   原 cf2_mixing_time_le 的完整语句面（k₀ + 几何衰减前提）从件②一跳
   直推：几何前提与 k₀ 在件②下为冗余前件，照原面全数保留以兼容旧
   消费面——原形由此成为件② + 冗余前件的换装读法。 *)

Corollary slm_cf2_le_of_full : forall (budget : Real) (k0 : nat),
  lt zero budget ->
  le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 Hbudget Hgeo.
  exact (slm_cf2_mixing_full budget Hbudget).
Defined.

(* ============================================================ *)
(* G2 审计口（绿核件，全 Closed 预期）                                    *)
(* ============================================================ *)

Print Assumptions slm_pow_mult_nonneg.
Print Assumptions slm_slack_select.
Print Assumptions slm_slack_select_le.
Print Assumptions slm_omd_lt_one.
Print Assumptions slm_cf2_mixing_full.
Print Assumptions slm_cf2_le_of_full.
