(* ==========================================================================)
   UpReqEntropyUniqueNeg.v —— 熵最大化唯一性：温度档正性、C 档假设位批量消解
   与显式分歧见证逆否形
   使命：本件形式化三段。其一，熵唯一性的温度档机器：bool 两点求和机
     （t22_bool_sum_pos / _ext / _linear / _add）、等熵蕴含 KL 零的
     t22_entropy_eq_kl_zero 与 t22_entropy_max_unique_temp_bool。其二，C 档
     假设位批量消解：log_req_compat 九位（ReqLogBridge / ReqAlignCore /
     ReqKLProjection / Req2AlignCore / Req3AlignCore / ReqU2FixedPoint /
     ReqFEPAttn / ReqFEPLogZ / AlignGapReq）的 Real 层闭合证书与点名下游件的
     Real 实例化。其三，定理 4.6c(b) 的显式分歧见证逆否形：
     t22b_lt_squeeze_le / _sym、t22b_list_sum_pos_ne、
     t22b_entropy_deficit_pos_of_kl_pos、t22b_not_optimal_of_kl_pos、
     t22b_entropy_strict_divergence_le / _or / _bool 与主件
     t22b_entropy_max_unique_neg（分歧见证 ⟹ KL>0 ⟹ 严格熵亏 ⟹ 非最优）。
   依赖：S01_BaseRing 至 S15_TailFEPUp 基座链（十五件顺序直调）、UpReqTempDefs、
     UpReqEntropyDeficitTemp、UpReqKLSTangent、G08_Gibbs、UpRealLeB、
     G05_LogSmall、UpReqAlgebra、UpReqAlign、UpReqAlign2、UpReqAlign3、
     UpReqU2、UpReqFEPAttn、UpAlignIdReq、G07_KLWall；Stdlib List；
     RealInterfaceEnhancedMod 接口内联。
   对标：Gibbs 分布熵差（Boltzmann 分布族的熵最大化唯一性）；stdlib List 求和。
   构造性：Set 层承载——结论面全 real_lt/real_eq，Or 见证 sigT 形零 Prop；
     零承认、公理面为空；全 Qed 闭合；可提取。
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.

From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* bool 具体载体实例（件 3 使用；求和面=两点表和）                       *)
(* ============================================================ *)

Definition t22_bool_sumf (f : bool -> Real) : Real :=
  real_list_sum bool f [true; false].

Lemma t22_bool_sum_pos :
  forall f : bool -> Real,
    (forall w : bool, real_lt real_zero (f w)) ->
    real_lt real_zero (t22_bool_sumf f).
Proof.
  intros f Hf.
  unfold t22_bool_sumf.
  apply (real_list_sum_pos bool f [true; false] Hf).
  intro Hc.
  discriminate Hc.
Qed.

Lemma t22_bool_sum_ext :
  forall f g : bool -> Real,
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (t22_bool_sumf f) (t22_bool_sumf g).
Proof.
  intros f g Hfg.
  unfold t22_bool_sumf.
  exact (real_list_sum_ext bool f g [true; false] Hfg).
Qed.

Lemma t22_bool_sum_linear :
  forall (a : Real) (f : bool -> Real),
    real_eq (t22_bool_sumf (fun s : bool => real_mult a (f s)))
            (real_mult a (t22_bool_sumf f)).
Proof.
  intros a f.
  unfold t22_bool_sumf.
  exact (real_list_sum_linear bool a f [true; false]).
Qed.

Lemma t22_bool_sum_add :
  forall f g : bool -> Real,
    real_eq (t22_bool_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (t22_bool_sumf f) (t22_bool_sumf g)).
Proof.
  intros f g.
  unfold t22_bool_sumf.
  exact (real_list_sum_add bool f g [true; false]).
Qed.

(* ============================================================ *)
(* Section RealEntropyUniqueTemp：求和面/温度/能量参数照                 *)
(*   UpReqTempDefs Section 同名同序（供 T6/T6b 件全 arity 显式应用）。       *)
(* ============================================================ *)
Section RealEntropyUniqueTemp.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 件 0：切点式谓词（显式接口形的逐点结论面，Set 值 real_eq 形）         *)
(*   对位 G08 gibbe2 注入位的逐点结论：                                 *)

(* ---------------------------------------------------------- *)
Definition t22_tangent_eq
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (real_inv_pos (p s) (Hp s)))
       (real_mult_positive
          (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
             T T_pos energy s)
          (real_inv_pos (p s) (Hp s))
          (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
             T T_pos energy s)
          (real_inv_pos_pos (p s) (Hp s))))
    (real_plus
       (real_mult (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (real_inv_pos (p s) (Hp s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：等值核（全实）——同能量+同熵 ⟹ Σ real_kl_term ≡ 0              *)
(*   链：熵亏温度版（T6b 主件 13 参显式应用）⟹ 同熵换载 + real_plus_opp     *)
(*   （Id minus_self_zero 参数位）⟹ KL ≡ 0 ⟹ 桥（T6b 件 5）运输到           *)
(*   Σ real_kl_term 面（gibbs_equality 参数位输入形）。                     *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_eq_kl_zero :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    real_eq (real_sum_over_S (fun s : S =>
               real_kl_term (p s)
                 (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                    T T_pos energy s)
                 (Hp s)
                 (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                    T T_pos energy s)))
            real_zero.
Proof.
  intros p Hp Hnp Henergy Hent.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S pT HpT).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：熵亏温度版（T6b 主件全 arity 13 参显式应用；Id Hdef 对位；          *)
  (*   real_minus_r 定义性展开 real_plus Spt (real_opp Sp)） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnp Henergy). }
  (* 步 2：等熵 ⟹ S[p_T] − S[p] ≡ 0（Id minus_self_zero 参数位：同熵换载 +   *)
  (*   real_plus_opp；x 参数位传换载对 (Spt, Sp)，y 参数位传逐字余项） *)
  assert (Hmz : real_eq (real_plus Spt (real_opp Sp)) real_zero).
  { apply (real_eq_trans
             (real_plus Spt (real_opp Sp))
             (real_plus Sp (real_opp Sp)) real_zero).
    - exact (RealSetoid.real_eq_plus_compat_adapt Spt Sp
               (real_opp Sp) (real_opp Sp)
               (real_eq_sym Sp Spt Hent) (real_eq_refl (real_opp Sp))).
    - exact (real_plus_opp Sp). }
  (* 步 3：KL ≡ 0（Id id_trans (id_sym Hdef) Hmz 对位） *)
  assert (Hkl : real_eq KL real_zero).
  { exact (real_eq_trans KL (real_plus Spt (real_opp Sp)) real_zero
             (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef) Hmz). }
  (* 步 4：桥（T6b 件 5 全 arity 9 参显式应用）运输到 Σ real_kl_term 面 *)
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
           KL real_zero).
  - exact (real_eq_sym KL
             (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
             (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
                real_sum_over_S_ext T T_pos energy p Hp)).
  - exact Hkl.
Qed.

(* ---------------------------------------------------------- *)
(* 件 1b：等值核 KL 形（Id relative_entropy ≡ zero 参数位对位）              *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_eq_KL_zero :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    real_eq (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy
               p Hp)
            real_zero.
Proof.
  intros p Hp Hnp Henergy Hent.
  apply (real_eq_trans
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s)
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy s)
                (Hp s)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy s)))
           real_zero).
  - exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp).
  - exact (t22_entropy_eq_kl_zero p Hp Hnp Henergy Hent).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：可达形 (a)——gibbe2 式显式前提形（抽象载体）                     *)
(*   同能量+同熵（⟹ Σ real_kl_term ≡ 0，件 1）+ 显式接口前提             *)
(*   （Σ ≡ 0 ⟹ 逐点切点式，件 0 谓词）⟹ 逐点 p s ≡ p_T s。              *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去（gibbsd_p_mult_ratio）。 *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_max_unique_temp_explicit :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    (* 显式接口前提位（载体诚实接口）：Σ real_kl_term ≡ 0 ⟹ 逐点切点式；
*)
    (real_eq (real_sum_over_S (fun s : S =>
                real_kl_term (p s)
                  (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (Hp s)
                  (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)))
             real_zero ->
     forall s : S, t22_tangent_eq p Hp s) ->
    forall s : S,
      real_eq (p s)
              (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                 T T_pos energy s).
Proof.
  intros p Hp Hnp Henergy Hent Htan0 s.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  (* 第 1 步：等值核（件 1）：Σ real_kl_term ≡ 0 *)
  assert (Hkl0 : real_eq
                   (real_sum_over_S (fun s0 : S => real_kl_term (p s0) (pT s0)
                                       (Hp s0) (HpT s0)))
                   real_zero).
  { exact (t22_entropy_eq_kl_zero p Hp Hnp Henergy Hent). }
  assert (Hu1 : real_eq (real_mult (pT s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (t1_log_eq_linear_inject
             (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (pT s) (real_inv_pos (p s) (Hp s))
                (HpT s) (real_inv_pos_pos (p s) (Hp s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ p s ≡ p_T s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (pT s) (real_inv_pos (p s) (Hp s))))
           (pT s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (pT s) (real_inv_pos (p s) (Hp s))))).
    + exact (real_eq_sym (real_mult (p s) real_one) (p s) (real_mult_one (p s))).
    + exact (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
                            real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (pT s) (Hp s)).
Qed.

End RealEntropyUniqueTemp.

(* ============================================================ *)
(* 件 3：可达形 (a) bool 完成——gibbe2 样板载体零接口前提形               *)
(*   （KL≡0 ⟹ 逐点 p≡p_T 直达：G08 逐项钳零件族 le_b 反对称构造闭合     *)
(*   「和零⟹逐项零」提取，注入位由 t1_log_eq_linear_inject 无条件供给）： *)
(*   gibbe2 样板载体上 (a) 形物理前提之外零接口前提。                    *)
(* ============================================================ *)
Theorem t22_entropy_max_unique_temp_bool :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (t22_bool_sumf p) real_one ->
    real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
            (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
    real_eq (real_entropy_dist bool t22_bool_sumf p Hp)
            (real_entropy_dist bool t22_bool_sumf
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy)) ->
    forall s : bool,
      real_eq (p s)
              (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                 T T_pos energy s).
Proof.
  intros energy T T_pos p Hp Hnp Henergy Hent s.
  exact (t1_gibbe2_gibbs_equality_bool p
           (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
              T T_pos energy)
           Hp
           (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
              T T_pos energy)
           Hnp
           (real_boltzmann_dist_temp_normalized bool t22_bool_sumf t22_bool_sum_pos
              t22_bool_sum_ext t22_bool_sum_linear T T_pos energy)
           (t22_entropy_eq_kl_zero bool t22_bool_sumf t22_bool_sum_pos
              t22_bool_sum_ext t22_bool_sum_linear t22_bool_sum_add
              T T_pos energy p Hp Hnp Henergy Hent) s).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                              *)
(* ============================================================ *)

Print Assumptions t22_entropy_eq_kl_zero.
Print Assumptions t22_entropy_eq_KL_zero.
Print Assumptions t22_entropy_max_unique_temp_explicit.
Print Assumptions t22_entropy_max_unique_temp_bool.

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
Require Import UpRealLeB.
Require Import G05_LogSmall.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpReqU2.
Require Import UpReqFEPAttn.
Require Import UpAlignIdReq.

Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part A：9 位 log_req_compat 语句 Real 层闭合证书（同形批，B1 显式应用） *)
(*   参数形（源文件原文）：                                            *)

(*   RIS := RealEnhancedReal（S07 Instance，Export 链入域）。        *)
(* ============================================================ *)

(* 参数位 s1：UpReqAlgebra ReqLogBridge *)
Theorem t26_s1_algebra_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s2：UpReqAlign ReqAlignCore *)
Theorem t26_s2_align_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s3：UpReqAlign ReqKLProjection *)
Theorem t26_s3_alignklp_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s4：UpReqAlign2 Req2AlignCore *)
Theorem t26_s4_align2_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s5：UpReqAlign3 Req3AlignCore *)
Theorem t26_s5_align3_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s6：UpReqU2 ReqU2FixedPoint *)
Theorem t26_s6_u2_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s7：UpReqFEPAttn ReqFEPAttn *)
Theorem t26_s7_fepattn_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s8：UpReqFEPAttn ReqFEPLogZ *)
Theorem t26_s8_feplogz_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 参数位 s9：UpAlignIdReq AlignGapReq *)
Theorem t26_s9_alignid_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* Part B：bool 两点求和载面（下游实例化的 sumf 供给位）                    *)
(*   载体复用 t22_bool_sumf（= real_list_sum bool f [true;false]，         *)
(*   本件 temp 段；raw real_eq/real_lt 满足证四件同在盘）。   *)
(* ============================================================ *)

Definition t26_bsum (f : bool -> Real) : Real := t22_bool_sumf f.

(* ============================================================ *)
(* Part C：点名下游件 Real 实例化（compat 参数位代入 B1、log_inv_exp_neg_req *)
(*   参数位代入 B4；sum 面参数位为接口型——见头注诚实边界）                 *)
(* ============================================================ *)

(* ---- s1 UpReqAlgebra ReqLogBridge（点名 req_log_inv_one_inv@1519、  *)
(*      req_log_div@1536；本节无节参，compat 单参数位显式应用，全 Concrete） ---- *)

Theorem t26_s1_req_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlgebra.req_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s1_req_log_div :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req (log (mult a (inv_pos b Hb))
             (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
        (req_minus (log a Ha) (log b Hb)).
Proof.
  intros a b Ha Hb.
  exact (@UpReqAlgebra.req_log_div Real RealEnhancedReal
           logd_log_compat_real a b Ha Hb).
Qed.

(* ---- s2 UpReqAlign ReqAlignCore（点名 req_free_energy_align_ext@251； *)
(*      载体 S:=bool、sumf:=t26_bsum；sum_ext 参数位接口型） ---- *)

Theorem t26_s2_req_free_energy_align_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (reward : bool -> Real) (beta : Real)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (f g : bool -> Real)
    (Hf : UpReqAlign.pos_dist bool f) (Hg : UpReqAlign.pos_dist bool g),
    (forall s : bool, req (f s) (g s)) ->
    req (UpReqAlign.F_align_req bool t26_bsum reward beta pi_ref pi_ref_pos f Hf)
        (UpReqAlign.F_align_req bool t26_bsum reward beta pi_ref pi_ref_pos g Hg).
Proof.
  intros sum_ext reward beta pi_ref pi_ref_pos f g Hf Hg Hfg.
  exact (@UpReqAlign.req_free_energy_align_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           reward beta pi_ref pi_ref_pos f g Hf Hg Hfg).
Qed.

(* ---- s3 UpReqAlign ReqKLProjection（点名 rkl_log_inv_one_inv@871、  *)
(*      req_log_proj_pass@910；后者零 sum 参数位，全 Concrete） ---- *)

Theorem t26_s3_rkl_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign.rkl_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s3_req_log_proj_pass :
  forall (post_aud : bool -> bool) (p : bool -> Real)
    (Hp_pos : forall s : bool, lt zero (p s))
    (HZ : lt zero (UpReqAlign.Z_aud_req bool t26_bsum post_aud p))
    (s : bool) (E : post_aud s = true),
    req (log (UpReqAlign.projected_distribution_req bool t26_bsum post_aud p HZ s)
             (UpReqAlign.req_projected_pass_pos bool t26_bsum post_aud p Hp_pos HZ s E))
        (plus (log (p s) (Hp_pos s))
              (log (inv_pos (UpReqAlign.Z_aud_req bool t26_bsum post_aud p) HZ)
                   (inv_pos_pos (UpReqAlign.Z_aud_req bool t26_bsum post_aud p) HZ))).
Proof.
  intros post_aud p Hp_pos HZ s E.
  exact (@UpReqAlign.req_log_proj_pass Real RealEnhancedReal
           bool t26_bsum logd_log_compat_real
           post_aud p Hp_pos HZ s E).
Qed.

(* ---- s4 UpReqAlign2 Req2AlignCore（点名 req2_log_inv_one_inv@335）-- *)

Theorem t26_s4_req2_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign2.req2_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

(* ---- s5 UpReqAlign3 Req3AlignCore（点名 r2_log_inv_opp@1511、        *)
(*      w_F_t_rel_decomp@163；后者四 sum 参数位接口型 + B4 显式应用）       ---- *)

Theorem t26_s5_r2_log_inv_opp :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign3.r2_log_inv_opp Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s5_w_F_t_rel_decomp :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (sum_pos : forall f : bool -> Real,
            (forall s : bool, lt zero (f s)) -> lt zero (t26_bsum f))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (eta : Real)
    (pi_t : bool -> Real) (Hpi_t : UpReqAlign3.pos3 bool pi_t),
    UpReqAlign3.nrm bool t26_bsum pi_t ->
    req (UpReqAlign3.FE bool t26_bsum
           (UpReqAlign3.ET bool reward beta pi_ref pi_ref_pos eta pi_t Hpi_t)
           beta pi_t Hpi_t)
        (plus (UpReqAlign3.FE bool t26_bsum
                 (UpReqAlign3.ET bool reward beta pi_ref pi_ref_pos eta pi_t Hpi_t)
                 beta
                 (UpReqAlign3.NPX bool t26_bsum sum_pos reward beta beta_pos
                    pi_ref pi_ref_pos eta pi_t Hpi_t)
                 (UpReqAlign3.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                    pi_ref pi_ref_pos eta pi_t Hpi_t))
              (mult beta
                 (UpReqAlign3.KLE bool t26_bsum pi_t
                    (UpReqAlign3.NPX bool t26_bsum sum_pos reward beta beta_pos
                       pi_ref pi_ref_pos eta pi_t Hpi_t)
                    Hpi_t
                    (UpReqAlign3.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                       pi_ref pi_ref_pos eta pi_t Hpi_t)))).
Proof.
  intros sum_ext sum_add sum_linear sum_pos
         reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t Hnrm.
  exact (@UpReqAlign3.w_F_t_rel_decomp Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear sum_pos
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t Hnrm).
Qed.

(* ---- s6 UpReqU2 ReqU2FixedPoint（点名 r2u_FA_witness_ext@392；       *)


Theorem t26_s6_r2u_FA_witness_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (reward : bool -> Real) (beta : Real)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (p : bool -> Real) (Hp Hq : UpReqU2.pos3 bool p),
    req (UpReqU2.FA bool t26_bsum reward beta pi_ref pi_ref_pos p Hp)
        (UpReqU2.FA bool t26_bsum reward beta pi_ref pi_ref_pos p Hq).
Proof.
  intros sum_ext reward beta pi_ref pi_ref_pos p Hp Hq.
  exact (@UpReqU2.r2u_FA_witness_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           reward beta pi_ref pi_ref_pos p Hp Hq).
Qed.

(* ---- s7 UpReqFEPAttn ReqFEPAttn（普查点名 req_fep_F_ext@180） -------- *)

Theorem t26_s7_req_fep_F_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (z : bool -> Real) (T : Real) (p q : bool -> Real)
    (Hp : forall s : bool, lt zero (p s))
    (Hq : forall s : bool, lt zero (q s)),
    req (t26_bsum p) one ->
    req (t26_bsum q) one ->
    (forall s : bool, req (p s) (q s)) ->
    req (UpReqFEPAttn.F_attn bool t26_bsum z T p Hp)
        (UpReqFEPAttn.F_attn bool t26_bsum z T q Hq).
Proof.
  intros sum_ext z T p q Hp Hq Hnp Hnq Hpq.
  exact (@UpReqFEPAttn.req_fep_F_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           z T p q Hp Hq Hnp Hnq Hpq).
Qed.

(* ---- s8 UpReqFEPAttn ReqFEPLogZ（普查点名 req_fep_F_ext_logz@395） ---- *)

Theorem t26_s8_req_fep_F_ext_logz :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (z : bool -> Real) (T : Real) (p q : bool -> Real)
    (Hp : forall s : bool, lt zero (p s))
    (Hq : forall s : bool, lt zero (q s)),
    (forall s : bool, req (p s) (q s)) ->
    req (UpReqFEPAttn.lz_F_attn bool t26_bsum z T p Hp)
        (UpReqFEPAttn.lz_F_attn bool t26_bsum z T q Hq).
Proof.
  intros sum_ext z T p q Hp Hq Hpq.
  exact (@UpReqFEPAttn.req_fep_F_ext_logz Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           z T p q Hp Hq Hpq).
Qed.

(* ---- s9 UpAlignIdReq AlignGapReq（普查点名 w_gap_base@172、              *)
(*      w_subgap_base@187；四 sum 参数位接口型 + B4 显式应用）             ---- *)

Theorem t26_s9_w_gap_base :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (sum_pos : forall f : bool -> Real,
            (forall s : bool, lt zero (f s)) -> lt zero (t26_bsum f))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (eta : Real) (eta_pos : lt zero eta)
    (pi_t : bool -> Real) (Hpi_t : UpAlignIdReq.pos3 bool pi_t),
    UpAlignIdReq.nrm bool t26_bsum pi_t ->
    req (req_minus
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos
              (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t)
              (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t))
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos pi_t Hpi_t))
        (mult beta
           (plus (mult (req_minus (inv_pos eta eta_pos) one)
                    (UpAlignIdReq.KLE bool t26_bsum
                       (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       pi_t
                       (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       Hpi_t))
                 (mult (inv_pos eta eta_pos)
                    (UpAlignIdReq.KLE bool t26_bsum pi_t
                       (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       Hpi_t
                       (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t))))).
Proof.
  intros sum_ext sum_add sum_linear sum_pos
         reward beta beta_pos pi_ref pi_ref_pos eta eta_pos pi_t Hpi_t Hnrm.
  exact (@UpAlignIdReq.w_gap_base Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear sum_pos
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos eta eta_pos pi_t Hpi_t Hnrm).
Qed.

Theorem t26_s9_w_subgap_base :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (ZAL_pos : lt zero
                 (UpAlignIdReq.ZAL bool t26_bsum reward beta beta_pos pi_ref))
    (p : bool -> Real) (Hp : UpAlignIdReq.pos3 bool p),
    UpAlignIdReq.nrm bool t26_bsum p ->
    req (req_minus
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos
              (UpAlignIdReq.PSTR bool t26_bsum reward beta beta_pos pi_ref ZAL_pos)
              (UpAlignIdReq.PSTR_pos bool t26_bsum reward beta beta_pos pi_ref
                 pi_ref_pos ZAL_pos))
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos p Hp))
        (mult beta
           (UpAlignIdReq.KLE bool t26_bsum p
              (UpAlignIdReq.PSTR bool t26_bsum reward beta beta_pos pi_ref ZAL_pos)
              Hp
              (UpAlignIdReq.PSTR_pos bool t26_bsum reward beta beta_pos pi_ref
                 pi_ref_pos ZAL_pos))).
Proof.
  intros sum_ext sum_add sum_linear
         reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hnrm.
  exact (@UpAlignIdReq.w_subgap_base Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hnrm).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全件 Print Assumptions）                             *)
(* ============================================================ *)
Print Assumptions t26_s1_algebra_log_compat.
Print Assumptions t26_s2_align_log_compat.
Print Assumptions t26_s3_alignklp_log_compat.
Print Assumptions t26_s4_align2_log_compat.
Print Assumptions t26_s5_align3_log_compat.
Print Assumptions t26_s6_u2_log_compat.
Print Assumptions t26_s7_fepattn_log_compat.
Print Assumptions t26_s8_feplogz_log_compat.
Print Assumptions t26_s9_alignid_log_compat.
Print Assumptions t26_s1_req_log_inv_one_inv.
Print Assumptions t26_s1_req_log_div.
Print Assumptions t26_s2_req_free_energy_align_ext.
Print Assumptions t26_s3_rkl_log_inv_one_inv.
Print Assumptions t26_s3_req_log_proj_pass.
Print Assumptions t26_s4_req2_log_inv_one_inv.
Print Assumptions t26_s5_r2_log_inv_opp.
Print Assumptions t26_s5_w_F_t_rel_decomp.
Print Assumptions t26_s6_r2u_FA_witness_ext.
Print Assumptions t26_s7_req_fep_F_ext.
Print Assumptions t26_s8_req_fep_F_ext_logz.
Print Assumptions t26_s9_w_gap_base.
Print Assumptions t26_s9_w_subgap_base.

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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import G07_KLWall.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)

(*   real_le a b（Set 层 Or (real_lt a b) (real_eq a b)）+ 分歧 Or 见证  *)
(*   ⟹ real_lt a b。三分支：lt 直达／eq+前向 lt 直达／eq+后向 lt 经      *)
(*   real_lt_compat 运输 + real_lt_irrefl 反证完成（对称支内部消化）。   *)
(* ============================================================ *)

Lemma t22b_lt_squeeze_le :
  forall a b : Real,
    real_le a b ->
    Or (real_lt a b) (real_lt b a) ->
    real_lt a b.
Proof.
  intros a b Hle Hdiv.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - destruct Hdiv as [Hlt | Hlt'].
    + exact Hlt.
    + exact (match real_lt_irrefl b
               (RealSetoid.real_lt_compat b b a b
                  (real_eq_refl b) Heq Hlt') with end).
Qed.

(* 对称辅件：弱序反向（real_le b a）+ 分歧 Or 见证 ⟹ 后向严格。 *)
Lemma t22b_lt_squeeze_le_sym :
  forall a b : Real,
    real_le b a ->
    Or (real_lt a b) (real_lt b a) ->
    real_lt b a.
Proof.
  intros a b Hle Hdiv.
  destruct Hdiv as [Hab | Hba].
  - exact (t22b_lt_squeeze_le b a Hle (inr Hab)).
  - exact (t22b_lt_squeeze_le b a Hle (inl Hba)).
Qed.

(* ============================================================ *)
(* 件 N0b：list 载体和正性件（l₁++s₀::l₂ 非空，结构位 discharge 用）     *)
(* ============================================================ *)

Lemma t22b_list_sum_pos_ne :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ f Hf.
  apply (real_list_sum_pos X f (l₁ ++ s₀ :: l₂) Hf).
  intro Hc. destruct l₁.
  - discriminate Hc.
  - discriminate Hc.
Qed.

(* list 载体求和面与正性结构位（件 N1 实例化共用，零接口前提） *)
Definition t22b_list_sumf (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) :
  (X -> Real) -> Real :=
  fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂).

Definition t22b_list_sum_pos_w (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) :
  forall f : X -> Real,
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (t22b_list_sumf X l₁ s₀ l₂ f) :=
  fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
    t22b_list_sum_pos_ne X l₁ s₀ l₂ f Hf.

(* ============================================================ *)
(* Section RealEntropyUniqueNeg：求和面/温度/能量参数照                  *)
(*   UpReqTempDefs Section 同名同序（供 T6b 两件全 arity 显式应用；          *)
(*   同节先定义件只按自身全称量词口使用）。                             *)
(* ============================================================ *)
Section RealEntropyUniqueNeg.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 件 N1a：严格熵亏尾链——Σ kl_term > 0 ⟹ S[p_T] − S[p] > 0              *)
(*   链：T6b 件 5 桥（KL 分布拉零规范形）⟹ real_lt_compat 运输 ⟹        *)
(*   KL > 0 ⟹ T6b 主件熵亏恒等（real_minus_r 定义性展开                  *)
(*   real_plus Spt (real_opp Sp)，Id S04 L3903 参数位）⟹ 再运输 ⟹ 严格熵亏。 *)
(* ---------------------------------------------------------- *)
Theorem t22b_entropy_deficit_pos_of_kl_pos :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_lt real_zero
      (real_sum_over_S (fun s : S =>
         real_kl_term (p s)
           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s)
           (Hp s)
           (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s))) ->
    real_lt real_zero
      (real_plus
         (real_entropy_dist S real_sum_over_S
            (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy)
            (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
               T T_pos energy))
         (real_opp (real_entropy_dist S real_sum_over_S p Hp))).
Proof.
  intros p Hp Hnormp Henergy Hkl.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S pT HpT).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：KL 分布拉零规范形桥（T6b 件 5，全 arity 9 参显式应用） *)
  assert (Hbrid : real_eq KL
                    (real_sum_over_S (fun s : S =>
                       real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp). }
  (* 步 2：KL > 0（沿桥自 Σ kl_term 面运输） *)
  assert (HKLpos : real_lt real_zero KL).
  { exact (RealSetoid.real_lt_compat real_zero real_zero
             (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
             KL
             (real_eq_refl real_zero)
             (real_eq_sym KL
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                Hbrid)
             Hkl). }
  (* 步 3：熵亏恒等（T6b 主件，全 arity 13 参显式应用；real_minus_r 定义性    *)
  (*   展开为 real_plus Spt (real_opp Sp)——同参数位对位） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnormp Henergy). }
  (* 步 4：沿熵亏恒等运输：S[p_T] − S[p] > 0（严格熵亏） *)
  exact (RealSetoid.real_lt_compat real_zero real_zero
           KL (real_plus Spt (real_opp Sp))
           (real_eq_refl real_zero)
           (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef) HKLpos).
Qed.

(* ---------------------------------------------------------- *)
(* 件 N1b：非最优尾链——Σ kl_term > 0 ⟹ S[p] < S[p_T]（熵严格小）         *)
(*   一跳：S07 real_lt_zero_minus（0 < y − x ⟹ x < y，eps 见证不变）。   *)
(* ---------------------------------------------------------- *)
Theorem t22b_not_optimal_of_kl_pos :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_lt real_zero
      (real_sum_over_S (fun s : S =>
         real_kl_term (p s)
           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s)
           (Hp s)
           (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s))) ->
    real_lt (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)).
Proof.
  intros p Hp Hnormp Henergy Hkl.
  apply (real_lt_zero_minus           (real_entropy_dist S real_sum_over_S p Hp)           (real_entropy_dist S real_sum_over_S              (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved                 T T_pos energy)              (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved                 T T_pos energy))).
  exact (t22b_entropy_deficit_pos_of_kl_pos p Hp Hnormp Henergy Hkl).
Qed.

End RealEntropyUniqueNeg.

(* ============================================================ *)
(* 件 N2：可达形 (b) 单向可比版（list 载体，klst_kl_sum_strict 输入）     *)
(*   逐项 p ≤ p_T（诚实接口前提）+ s₀ 处分歧 Or 见证 ⟹ 件 N0 挤压出      *)
(*   前向严格见证 ⟹ G07 klst_kl_sum_strict ⟹ KL>0 ⟹ 件 N1b ⟹ p 非最优。 *)
(*   方向对位：klst 原件吃 p≤q + p s₀ < q s₀；本件 p=p、q=p_T，          *)
(*   与 T6b 熵亏恒等式 KL(p‖p_T) 同向（余留警示参数位已对位）。        *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_le :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (T : Real) (T_pos : real_lt real_zero T) (energy : X -> Real)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (t22b_list_sumf X l₁ s₀ l₂ p) real_one ->
  real_eq (t22b_list_sumf X l₁ s₀ l₂ (fun s : X => real_mult (p s) (energy s)))
          (real_energy_exp_temp X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy) ->
  (forall s : X,
     real_le (p s)
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)) ->
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀))
      (real_lt (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
               (p s₀))) ->
  real_lt
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂) p Hp)
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂)
       (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
       (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)).
Proof.
  intros X l₁ s₀ l₂ T T_pos energy p Hp Hnormp Henergy Hpq Hdiv.
  (* 步 1：p_T 归一化（list 载体实例，normalized 件 8 参显式应用） *)
  assert (Hnormq : real_eq
                     (t22b_list_sumf X l₁ s₀ l₂
                        (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                           (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂)
             (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
             T T_pos energy). }
  (* 步 2：le→lt 严格挤压（件 N0）：分歧 Or 见证 ⟹ 前向严格见证 *)
  assert (Hdiv' : real_lt (p s₀)
                    (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                       (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)).
  { exact (t22b_lt_squeeze_le (p s₀)
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
             (Hpq s₀) Hdiv). }
  (* 步 3：KL > 0（G07 klst_kl_sum_strict 显式应用：逐项 p≤p_T + s₀ 严格） *)
  assert (Hkl : real_lt real_zero
                  (t22b_list_sumf X l₁ s₀ l₂
                     (fun s : X =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)))).
  { exact (klst_kl_sum_strict X l₁ s₀ l₂ p
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hpq Hnormp Hnormq Hdiv'). }
  (* 步 4：非最优（件 N1b list 实例：KL>0 ⟹ 熵严格小） *)
  exact (t22b_not_optimal_of_kl_pos X (t22b_list_sumf X l₁ s₀ l₂)
           (t22b_list_sum_pos_w X l₁ s₀ l₂)
           (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
              real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
           (fun (a : Real) (f : X -> Real) =>
              real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
           (fun f g : X -> Real => real_list_sum_add X f g (l₁ ++ s₀ :: l₂))
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N3：可达形 (b) 双向见证版（list 载体，klst_kl_energy_nonconst 输入） *)
(*   逐项双向可比（Or 承载，诚实接口位）+ s₀ 分歧 Or 见证 ⟹ G07 双向件    *)
(*   显式应用（q>p 支原件内部消化，免挤压）⟹ KL>0 ⟹ 件 N1b ⟹ p 非最优。      *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_or :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (T : Real) (T_pos : real_lt real_zero T) (energy : X -> Real)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (t22b_list_sumf X l₁ s₀ l₂ p) real_one ->
  real_eq (t22b_list_sumf X l₁ s₀ l₂ (fun s : X => real_mult (p s) (energy s)))
          (real_energy_exp_temp X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy) ->
  (forall s : X,
     Or (real_le (p s)
                  (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                     (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s))
        (real_le (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                    (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                 (p s))) ->
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀))
      (real_lt (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
               (p s₀))) ->
  real_lt
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂) p Hp)
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂)
       (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
       (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)).
Proof.
  intros X l₁ s₀ l₂ T T_pos energy p Hp Hnormp Henergy Hpq Hdiv.
  assert (Hnormq : real_eq
                     (t22b_list_sumf X l₁ s₀ l₂
                        (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                           (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂)
             (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
             T T_pos energy). }
  assert (Hkl : real_lt real_zero
                  (t22b_list_sumf X l₁ s₀ l₂
                     (fun s : X =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)))).
  { exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hpq Hnormp Hnormq Hdiv). }
  exact (t22b_not_optimal_of_kl_pos X (t22b_list_sumf X l₁ s₀ l₂)
           (t22b_list_sum_pos_w X l₁ s₀ l₂)
           (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
              real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
           (fun (a : Real) (f : X -> Real) =>
              real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
           (fun f g : X -> Real => real_list_sum_add X f g (l₁ ++ s₀ :: l₂))
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N4：可达形 (b) bool 完成——件 N3 在 [true; false] 载体的实例        *)
(*   （s₀ := true，l₁ := []，l₂ := [false]；结构四组引理显式应用 t22_bool 辅件）  *)
(*   t22_bool_* helpers；[] ++ true :: [false] 与 [true; false] 定义     *)
(*   可转换，exact 直过）。                                             *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_bool :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (t22_bool_sumf p) real_one ->
  real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
          (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
  (forall s : bool,
     Or (real_le (p s)
                  (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                     T T_pos energy s))
        (real_le (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy s)
                 (p s))) ->
  (Or (real_lt (p true)
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy true))
      (real_lt (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy true)
               (p true))) ->
  real_lt
    (real_entropy_dist bool t22_bool_sumf p Hp)
    (real_entropy_dist bool t22_bool_sumf
       (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
          T T_pos energy)
       (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
          T T_pos energy)).
Proof.
  intros energy T T_pos p Hp Hnormp Henergy Hpq Hdiv.
  assert (Hnormq : real_eq
                     (t22_bool_sumf
                        (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                           T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized bool t22_bool_sumf t22_bool_sum_pos
             t22_bool_sum_ext t22_bool_sum_linear T T_pos energy). }
  assert (Hkl : real_lt real_zero
                  (t22_bool_sumf
                     (fun s : bool =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                             T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                             T T_pos energy s)))).
  { exact (klst_kl_energy_nonconst bool [] true [false] p
             (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                T T_pos energy)
             Hpq Hnormp Hnormq Hdiv). }
  exact (t22b_not_optimal_of_kl_pos bool t22_bool_sumf t22_bool_sum_pos
           t22_bool_sum_ext t22_bool_sum_linear t22_bool_sum_add
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N5：组装件（bool 载体，prod 双函数记录——Set 层 And 形零 Prop）      *)
(*   定理 4.6c 两形合取载体：(a) 支＝同熵同能量逐点等链（            *)
(*   零接口前提整链消解）× (b) 肢＝件 N4（逐项可比 + s₀ 分歧见证 ⟹       *)
(*   熵严格小）。(b) 逆否形至此与 (a) 形合流闭合。                        *)
(* ============================================================ *)
Theorem t22b_entropy_max_unique_neg :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (t22_bool_sumf p) real_one ->
  real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
          (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
  prod
    (real_eq (real_entropy_dist bool t22_bool_sumf p Hp)
             (real_entropy_dist bool t22_bool_sumf
                (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)) ->
     forall s : bool,
       real_eq (p s)
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy s))
    ((forall s : bool,
        Or (real_le (p s)
                     (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                        T T_pos energy s))
           (real_le (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                       T T_pos energy s)
                    (p s))) ->
     Or (real_lt (p true)
                 (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy true))
        (real_lt (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy true)
                 (p true)) ->
     real_lt (real_entropy_dist bool t22_bool_sumf p Hp)
             (real_entropy_dist bool t22_bool_sumf
                (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy))).
Proof.
  intros energy T T_pos p Hp Hnormp Henergy.
  split.
  - exact (t22_entropy_max_unique_temp_bool energy T T_pos p Hp Hnormp Henergy).
  - exact (t22b_entropy_strict_divergence_bool energy T T_pos p Hp Hnormp Henergy).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                              *)
(* ============================================================ *)

Print Assumptions t22b_lt_squeeze_le.
Print Assumptions t22b_lt_squeeze_le_sym.
Print Assumptions t22b_list_sum_pos_ne.
Print Assumptions t22b_entropy_deficit_pos_of_kl_pos.
Print Assumptions t22b_not_optimal_of_kl_pos.
Print Assumptions t22b_entropy_strict_divergence_le.
Print Assumptions t22b_entropy_strict_divergence_or.
Print Assumptions t22b_entropy_strict_divergence_bool.
Print Assumptions t22b_entropy_max_unique_neg.
