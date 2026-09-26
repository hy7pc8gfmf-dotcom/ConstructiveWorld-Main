(* ==========================================================================)
   UpAblSlackMix.v — 非几何率与松弛形的三主件构造
   使命: slm_slack_select（抽象松弛组合定理：预算劈半——几何半边 mix_k_select 与线性半边 eps:=(1/n)·(B/4) 合流）、slm_cf2_mixing_full（Fin2 无条件形，k₀ 前提内部化消去）、slm_cf2_le_of_full（向后兼容推论）。
   依赖: List、CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqSampling、UpTVDoeblin、UpReqIterGeomRate、UpReqConcFin2、UpReqMixingTime。
   对标: 混合链收敛率的松弛组合界（马尔可夫链混合时间）。
   构造性: 全件零承认词面、零经典逻辑（证明仅 destruct/精确项式）；语句面全 Set 层；三主件为实质构造（非平凡）、全 Defined 可提取。
   编译配方: Rocq 9.1 直调 coqc 与 cpu_guard（-LoadLimit 85 -CoreN 2），输出至临时目录，树内零写入。
   ========================================================================== *)
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqConcFin2.
Require Import UpReqMixingTime.
Import RealInterfaceEnhancedMod.

(* ---- 帮件一：κ 幂乘积非负（收缩环节的见证供给，对任意 κ ≤ 1 与 A ≥ 0） ---- *)

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

(* ---- 帮件二：tv_rpow 面与 req_r_pow 面的形态转换适配引理（归纳桥，req 逐位） ----
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

(* ---- 件①：抽象松弛组合定理（率界接口 + 无条件选择器，零 k₀ 前提） ----
   四证书照 mix_k_select 前提面（0<κ<1、0≤A、0<B）；Hsl 为「松弛率界」
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
  (* 形态转换适配：tv_rpow/real_mult 面 -> req_r_pow/mult 面
     （slm_rpow_tvpow 归纳桥 + req_mult_compat/req_lt_compat 转换） *)
  assert (HkgI : lt (mult (req_r_pow kappa kg) A)
                    (mult cf2_inv_two budget)).
  { exact (req_lt_compat (mult (tv_rpow kappa kg) A)
             (mult (req_r_pow kappa kg) A)
             (mult cf2_inv_two budget) (mult cf2_inv_two budget)
             (req_mult_compat (tv_rpow kappa kg) (req_r_pow kappa kg) A A
                (req_sym _ _ (slm_rpow_tvpow kappa kg)) (req_refl A))
             (req_refl (mult cf2_inv_two budget))
             Hkg). }
  (* 收缩环节：κ^{S k_g}·A ≤ κ^{k_g}·A *)
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
  (* 线性半边：eps := (1/n)·(B/4) 于候选点 n := S k_g 构造（正性 + 消逆） *)
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
  (* 合流：B/4 < B/2 严格不等式 + B/2 + B/2 = B 合成（cf2 辅助引理族） *)
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

(* ---- 件① le 形推论（一步推得：严格不等式走 Or 左支） ---- *)

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
  exact (lt_id_r cf2_omd (plus cf2_omd cf2_delta_star) one           (req_trans (plus cf2_omd cf2_delta_star)                      (plus cf2_delta_star cf2_omd) one                      (plus_comm cf2_omd cf2_delta_star)                      cf2_aux_ds_omd)           (igr_lt_plus_r cf2_omd cf2_delta_star cf2_ds_pos)).
Defined.

(* ---- 件②：Fin2 无条件形（零 k₀ 前提版） ----
   原 cf2_mixing_time_le 的 k₀ 输入前提与几何衰减前提
   （omd^{k0}·TV₀ ≤ B/2）由此内部化消去：k₀ 不再是输入，而由件①的
   无条件选择器在预算劈半内算出（强化：原形见件③推论）。 *)

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

(* ---- 件③：转换推论（向后兼容） ----
   原 cf2_mixing_time_le 的完整语句面（k₀ + 几何衰减前提）从件②一步
   直推：几何前提与 k₀ 在件②下为冗余前提，照原面全数保留以兼容旧
   使用面——原形由此成为件② + 冗余前提的转换读法。 *)

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
(* 假设审计（零承认件，全 Closed 预期）                                    *)
(* ============================================================ *)

Print Assumptions slm_pow_mult_nonneg.
Print Assumptions slm_slack_select.
Print Assumptions slm_slack_select_le.
Print Assumptions slm_omd_lt_one.
Print Assumptions slm_cf2_mixing_full.
Print Assumptions slm_cf2_le_of_full.
