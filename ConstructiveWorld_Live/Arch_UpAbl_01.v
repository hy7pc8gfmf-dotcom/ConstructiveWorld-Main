(* ==========================================================================)
   Arch_UpAbl_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：uabT2a_rppo_log_req_compat、abl_S12_sf_log_antitone_le、uabT2a_ralt_log_req_compat、uabT13b_tv_delta_le_one、uabT13_sigm2_b_mult_cancel、uabT9_sigm_pft_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import G05_LogSmall.
Require Import RateTheoryAblation.
From Stdlib Require Import List.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Require Import UpReqSumD.
Require Import UpSigMigrate.

(* ================= §1 uabT2a_rppo_log_req_compat 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←  rppo_log_req_compat（ReqPPOAdvantage 节；逐字，载体已 Real） ---- *)
Theorem uabT2a_rppo_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_rppo_log_req_compat.
(* ================= §2 abl_S12_sf_log_antitone_le 族 ================= *)
(* ################ sf_log_antitone_le（源版本 L12061-12064 逐字参数形） ################ *)
Theorem abl_S12_sf_log_antitone_le :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b ->
    real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (real_log_le_mono a b Ha Hb Hab).
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_S12_sf_log_antitone_le.
(* ================= §3 uabT2a_ralt_log_req_compat 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ---- 位1 ←  ralt_log_req_compat（ReqRestACore 节；逐字，R:=Real） ---- *)
Theorem uabT2a_ralt_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- PA 收尾段（逐件 Closed 判读） ---- *)
Print Assumptions uabT2a_ralt_log_req_compat.
(* ================= §4 uabT13b_tv_delta_le_one 族 ================= *)
Theorem uabT13b_tv_delta_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
    (forall i : list Real,
       real_eq (real_list_sum (list Real) (K i) states) real_one) ->
    real_eq (real_list_sum (list Real) u states) real_one ->
    (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
    real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  exact (@rta_delta_le_one_of_minorization states K u delta HKrow Hunorm Hmin).
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_tv_delta_le_one.
(* ================= §5 uabT13_sigm2_b_mult_cancel 族 ================= *)
Import RealInterfaceEnhancedMod.

Section UabT13Sigm2.

Context {RI0 : RealInterfaceEnhanced}.

Theorem uabT13_sigm2_b_mult_cancel :
  forall a x : @S01_BaseRing.R RI0,
    lt zero a -> req (mult a x) zero -> req x zero.
Proof.
  intros a x Ha H.
  assert (Hid : Id (@S01_BaseRing.mult RI0 a x) (@S01_BaseRing.zero RI0)) by exact H.
  exact (@mult_cancel_l RI0 a x zero Ha
          (S01_BaseRing.id_trans Hid
             (S01_BaseRing.id_sym (@S01_BaseRing.mult_zero RI0 a)))).
Qed.

End UabT13Sigm2.

(* ---- 收尾段（逐件假设面打印，判读全闭） ---- *)
Print Assumptions uabT13_sigm2_b_mult_cancel.
(* ================= §6 uabT9_sigm_pft_pos 族 ================= *)
Import RealInterfaceEnhancedMod.

Theorem uabT9_sigm_pft_pos :
  forall (S : Set) (enum : list S) (Hne : Not (enum = nil))
         (z : S -> Real) (T : Real) (T_pos : lt zero T),
    lt zero (@sigm_partition_function_temp Real RealEnhancedReal S
               (sumd_sumf S enum) T T_pos z).
Proof.
  intros S enum Hne z T T_pos.
  unfold sigm_partition_function_temp, sigm_exp_pos_fn.
  exact (sumd_sum_pos S enum _ Hne
           (fun s : S => exp_neg_pos (opp (mult (inv_pos T T_pos) (z s))))).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_sigm_pft_pos.
