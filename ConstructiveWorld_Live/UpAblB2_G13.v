(* ==========================================================================)
   UpAblB2_G13.v — Gibbs 不等式与等号面的抽象复核及剩余前提收窄
   使命: b_gibbs_pos/b_gibbs_sum_eps/b_gibbs_eq 三语句在抽象接口载体上显式前提全参复核，两点 Real 载体上实例化并将剩余前提收窄为显式携带的定理（log-le/log-eq 前提的构造性边界注记在册）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpSigMigrate2、UpStepKL、UpRealLeB、S08_RealMainlineDPO、G08_Gibbs、UpReqCEqDispersion（只读使用）。
   对标: Gibbs 不等式（相对熵非负性）及等号情形（分布相等当且仅当相对熵为零）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；接口面为 Set 层序谓词；文末对十条结论逐一 Print Assumptions 全 Closed。
   编译配方: Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹限载；输出一律 -o 临时目录，树内 .vo 不重写。
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpSigMigrate2.
Require Import UpStepKL.
Require Import UpRealLeB.
Require Import G08_Gibbs.
Require Import UpReqCEqDispersion.
Import RealInterfaceEnhancedMod.

(* ======== §1 · 抽象载体全参出节形复核（三语句逐一显式前提） ====== *)
Section UabB2Abs.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- b_gibbs_pos 复核：全参六前提 ext/add/linear/le/log-inv/log-le ---- *)
Theorem uabB2_bgibbs_pos_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (kl_a S sumf p q Hp Hq).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality R RIS S sumf Hext Hadd Hlin Hle Hloginv Hlogle                               p q Hp Hq Hnp Hnq).
Qed.

(* ---- b_gibbs_sum_eps 复核：前者加 le_plus_compat 链，零新增前提 ------ *)
Theorem uabB2_bgibbs_sum_eps_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q)
         (eps : R) (Heps : lt zero eps),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (plus (kl_a S sumf p q Hp Hq) eps).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps (plus (kl_a S sumf p q Hp Hq) eps)                    (lt_le_iff zero eps (inl Heps))                    (le_id_l eps (plus zero eps)                               (plus (kl_a S sumf p q Hp Hq) eps)                               (req_sym (plus zero eps) eps                                          (req_trans (plus zero eps) (plus eps zero) eps                                                     (plus_comm zero eps)                                                     (plus_zero eps)))                               (le_plus_compat zero (kl_a S sumf p q Hp Hq)                                               eps eps                                               (uabB2_bgibbs_pos_full S sumf Hext Hadd                                                                      Hlin Hle Hloginv Hlogle                                                                      p q Hp Hq Hnp Hnq)                                               (le_refl eps)))).
Qed.

(* ---- b_gibbs_eq 复核（等号面本体：全参七前提，znn/log-eq 显式在列；     *)
(*        log-le/log-eq 为构造性未决前提，随件显式携带不隐藏） -------------- *)
Theorem uabB2_bgibbs_eq_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hznn : forall f : S -> R,
                   (forall s : S, le zero (f s)) -> req (sumf f) zero ->
                   forall s : S, req (f s) zero)
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : R) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    req (kl_a S sumf p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality R RIS S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq                             p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== §2 · 抽象载体上的两点供给引理（znn 前提的构造） ========== *)
(* 两点和 uabB2_t2sum：与 hzlogd_aud_sum（G08_Gibbs）同形，展开均为 plus (f true) (f false) *)
Definition uabB2_t2sum (f : bool -> R) : R := plus (f true) (f false).

Lemma uabB2_opp_zero : req (opp zero) zero.
Proof.
  apply (req_trans (opp zero) (plus zero (opp zero)) zero).
  - apply (req_trans (opp zero) (plus (opp zero) zero) (plus zero (opp zero))).
    + apply (req_sym (plus (opp zero) zero) (opp zero)).
      apply plus_zero.
    + apply plus_comm.
  - apply plus_opp.
Qed.

(* znn 前提（零和非负消去）的两点构造（新建供给引理）：                      *)
(*   逐点非负 + 两点和为零 ⟹ 逐点为零（le_antisym 与左消去的纯代数链）。   *)
Lemma uabB2_znn_abs :
  forall f : bool -> R,
    (forall s : bool, le zero (f s)) ->
    req (uabB2_t2sum f) zero ->
    forall s : bool, req (f s) zero.
Proof.
  intros f Hpos Hsum.
  assert (D : req (plus (opp (f false)) (f false)) zero).
  { apply (req_trans (plus (opp (f false)) (f false))
                     (plus (f false) (opp (f false))) zero).
    - apply plus_comm.
    - apply plus_opp. }
  assert (E : req (plus (f true) (f false)) (plus (opp (f false)) (f false))).
  { apply (req_trans (plus (f true) (f false)) zero (plus (opp (f false)) (f false))).
    - exact Hsum.
    - apply (req_sym (plus (opp (f false)) (f false)) zero).
      exact D. }
  assert (Htf : req (f true) (opp (f false))).
  { apply (req_plus_cancel_l (f false) (f true) (opp (f false))).
    apply (req_trans (plus (f false) (f true))
                     (plus (f true) (f false))
                     (plus (f false) (opp (f false)))).
    - apply plus_comm.
    - apply (req_trans (plus (f true) (f false))
                       (plus (opp (f false)) (f false))
                       (plus (f false) (opp (f false)))).
      + exact E.
      + apply plus_comm. }
  assert (Ht0 : req (f true) zero).
  { apply (le_antisym (f true) zero).
    - apply (le_trans (f true) (opp (f false)) zero).
      + apply (le_id_r (f true) (f true) (opp (f false)) Htf (le_refl (f true))).
      + apply (le_id_r (opp (f false)) (opp zero) zero uabB2_opp_zero).
        apply (opp_le_compat zero (f false) (Hpos false)).
    - exact (Hpos true). }
  intro s. destruct s.
  - exact Ht0.
  - assert (F : req (plus zero (f false)) zero).
    { apply (req_trans (plus zero (f false))
                       (plus (f true) (f false)) zero).
      - apply (req_sym (plus (f true) (f false)) (plus zero (f false))).
        apply (req_plus_compat (f true) zero (f false) (f false) Ht0 (req_refl (f false))).
      - exact Hsum. }
    apply (req_trans (f false) (plus (f false) zero) zero).
    + apply (req_sym (plus (f false) zero) (f false)).
      apply plus_zero.
    + apply (req_trans (plus (f false) zero) (plus zero (f false)) zero).
      * apply plus_comm.
      * exact F.
Qed.

End UabB2Abs.

(* ======== §3 · Real 载体上的 log-inv 前提实例 ================ *)
(* 前提实例：kl_log_inv（UpStepKL）经接口投影转换一步落成                   *)
(*   （req:=real_eq、log 经 real_log 到 cw_log、inv_pos 到 real_inv_pos 全展开）。   *)
Lemma uabB2_loginv_real :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (kl_log_inv x Hx Hi).
Qed.

(* ======== §4 · 两点 Real 载体的剩余前提定理（未决前提的定理级定位） ====== *)
(* 载体：S:=bool、sumf:=hzlogd_aud_sum（G08_Gibbs）；                       *)
(*   前提供给：ext/add/linear/le = hzlogd_sum2_*（G08_Gibbs），             *)
(*               znn = uabB2_znn_abs（同形转换），log-inv = uabB2_loginv_real。     *)
(* uabB2_bgibbs_pos_resW4：剩余前提 = {log-le} ------------------------- *)
Theorem uabB2_bgibbs_pos_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    le zero (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq).
Proof.
  intros Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality Real RealEnhancedReal bool hzlogd_aud_sum             hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear hzlogd_sum2_le             uabB2_loginv_real Hlogle p q Hp Hq Hnp Hnq).
Qed.

(* uabB2_bgibbs_sumeps_resW4：剩余前提 = {log-le} --------------------- *)
Theorem uabB2_bgibbs_sumeps_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q)
         (eps : Real) (Heps : lt zero eps),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    le zero (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) eps).
Proof.
  intros Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps                    (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) eps)                    (lt_le_iff zero eps (inl Heps))                    (le_id_l eps (plus zero eps)                               (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq)                                     eps)                               (req_sym (plus zero eps) eps                                          (req_trans (plus zero eps) (plus eps zero) eps                                                     (plus_comm zero eps)                                                     (plus_zero eps)))                               (le_plus_compat zero                                 (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq)                                 eps eps                                 (uabB2_bgibbs_pos_resW4 Hlogle p q Hp Hq Hnp Hnq)                                 (le_refl eps)))).
Qed.

(* uabB2_bgibbs_eq_resW4：剩余前提 = {log-le, log-eq}（等号面未决对） ------ *)
Theorem uabB2_bgibbs_eq_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : Real) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    req (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) zero ->
    forall s : bool, req (p s) (q s).
Proof.
  intros Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality Real RealEnhancedReal bool hzlogd_aud_sum             hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear             uabB2_znn_abs uabB2_loginv_real Hlogle Hlogeq             p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== §4·b、等号面剩余前提再收窄：log-eq 前提在具体 Real 载体          *)
(*   可实例化——t34_log_eq_linear_weak（UpReqCEqDispersion；实三分           *)
(*   real_weak_trich 的双否定形，直觉主义有效、无外部未证假设）恰为该前提   *)
(*   的 Real 实例；代入后等号面两点剩余前提自 {log-le, log-eq} 收窄至       *)
(*   {log-le}——载体分层：抽象接口载体（无三分/比较字段）维持为前提，        *)
(*   具体 Regular-Real 载体上 log-eq 可实例化（本件定理级实证）。---------- *)
Theorem uabB2_bgibbs_eq_res_logle_only :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    req (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) zero ->
    forall s : bool, req (p s) (q s).
Proof.
  intros Hlogle p q Hp Hq Hnp Hnq Hkl0.
  exact (uabB2_bgibbs_eq_resW4 Hlogle t34_log_eq_linear_weak p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== §5 · pos 面的 B 形替代路线（Bishop 序，零额外前提） ===== *)
(* gibbsd_gibbs_inequality（G08_Gibbs）：0 ≤_B 有限和 KL（Bishop 序），零额外 *)
(*   前提——pos 面在 B 形序上无条件成立，为独立可达的替代路线。               *)
(*   eq 面无此替代（库内无 B 形或任意形的 gibbs_eq 对应件，如实注明）。 ---- *)
Theorem uabB2_gibbs_pos_Bform_list :
  forall (l : list bool) (p q : bool -> Real)
         (Hp : forall s : bool, lt zero (p s)) (Hq : forall s : bool, lt zero (q s))
         (Hnormp : req (real_list_sum bool p l) one)
         (Hnormq : req (real_list_sum bool q l) one),
    real_le_b zero
      (real_list_sum bool (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros l p q Hp Hq Hnormp Hnormq.
  exact (gibbsd_gibbs_inequality bool l p q Hp Hq Hnormp Hnormq).
Qed.

(* ======== §6 · 假设审计（Print Assumptions 全 Closed 为判据） ============ *)
Print Assumptions uabB2_bgibbs_pos_full.
Print Assumptions uabB2_bgibbs_sum_eps_full.
Print Assumptions uabB2_bgibbs_eq_full.
Print Assumptions uabB2_znn_abs.
Print Assumptions uabB2_loginv_real.
Print Assumptions uabB2_bgibbs_pos_resW4.
Print Assumptions uabB2_bgibbs_sumeps_resW4.
Print Assumptions uabB2_bgibbs_eq_resW4.
Print Assumptions uabB2_bgibbs_eq_res_logle_only.
Print Assumptions uabB2_gibbs_pos_Bform_list.
