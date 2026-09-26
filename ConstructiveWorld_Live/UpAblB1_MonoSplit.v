(* ==========================================================================)
   UpAblB1_MonoSplit.v — 温度参数化 Gibbs 熵族在单点载体上的具体无假设实例
   使命: 九项接口参数取单点具体值、三条节级前提（归一化/能量钉/KL 归零）实算成立，源模块出节五定理（熵单峰分裂）全参应用为具体实例 uab1_discharge_*。
   依赖: CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、UpReqEntropyMonoSplit。
   对标: 温度参数化 Gibbs 族的熵单峰性（统计力学；mathlib/stdlib 无直接对应物）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；序比较均为序 Or 的构造见证形（inl/inr）；文末对十条主要结论逐一 Print Assumptions 全 Closed。
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMonoSplit.

(* ============ §1 · 实例供给：九项接口/数据参数的具体值 ============ *)

Definition uab1_sum : (unit -> Real) -> Real :=
  fun f : unit -> Real => f tt.

Definition uab1_sumpos
  : forall f : unit -> Real,
      (forall s : unit, real_lt real_zero (f s)) ->
      real_lt real_zero (uab1_sum f) :=
  fun (f : unit -> Real)
      (Hf : forall s : unit, real_lt real_zero (f s)) => Hf tt.

Definition uab1_ext : forall f g : unit -> Real,
    (forall s : unit, real_eq (f s) (g s)) ->
    real_eq (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_eq (f s) (g s)) => H tt.

Definition uab1_le : forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_le (f s) (g s)) => H tt.

Definition uab1_linear : forall (a : Real) (f : unit -> Real),
    real_eq (uab1_sum (fun s : unit => real_mult a (f s)))
            (real_mult a (uab1_sum f)) :=
  fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)).

Definition uab1_add : forall f g : unit -> Real,
    real_eq (uab1_sum (fun s : unit => real_plus (f s) (g s)))
            (real_plus (uab1_sum f) (uab1_sum g)) :=
  fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)).

Definition uab1_T_star : Real := real_one.
Definition uab1_T_star_pos : real_lt real_zero uab1_T_star := real_lt_zero_one.
Definition uab1_energy : unit -> Real := fun _ : unit => real_one.

(* ============ §2 · 源模块速记件的显式参形（与源模块 Let 速记同体展开） ============ *)

Definition uab1_bd (u : Real) (Hu : real_lt real_zero u) : unit -> Real :=
  real_boltzmann_dist_temp unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_bd_pos (u : Real) (Hu : real_lt real_zero u)
  : forall s : unit, real_lt real_zero (uab1_bd u Hu s) :=
  real_boltzmann_dist_temp_pos unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_ent (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_entropy_dist unit uab1_sum (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* KL 方向注记：uab1_kl u = KL(p_u ‖ p_{t*})——p_u 居第一分布位， *)
(* p_{t*} 居参考位；uab1_T_star 全参取 real_one。 *)
Definition uab1_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp unit uab1_sum uab1_sumpos uab1_T_star uab1_T_star_pos uab1_energy
               (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* ============ §3 · 工具引理（单位元/零元的左恒等，环律两行自证） ============ *)

Lemma uab1_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Qed.

Lemma uab1_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_plus_comm real_zero x) (real_plus_zero x)).
Qed.

(* ============ §4 · 链 A：Gibbs 族归一化（uab1_bt_pt_one） ============ *)
(* 单点载体温 t 处 p_t(tt) == 1：配分函数 Z_t 定义性收敛到能量因子自身，    *)
(* 乘积经 real_mult_comm 换序后由 real_inv_pos_correct 一步归一。           *)

Lemma uab1_bt_pt_one : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (uab1_bd t Ht tt) real_one.
Proof.
  intros t Ht.
  pose proof
    (real_inv_pos_correct
       (real_Z_temp unit uab1_sum t Ht uab1_energy)
       (real_Z_temp_pos unit uab1_sum uab1_sumpos
          t Ht uab1_energy)) as Hinv.
  assert (Hswap : real_eq (uab1_bd t Ht tt)
                    (real_mult
                       (real_boltzmann_factor_temp unit t Ht uab1_energy tt)
                       (real_inv_pos
                          (real_Z_temp unit uab1_sum t Ht uab1_energy)
                          (real_Z_temp_pos unit uab1_sum uab1_sumpos
                             t Ht uab1_energy)))).
  { exact (real_mult_comm
             (real_inv_pos
                (real_Z_temp unit uab1_sum t Ht uab1_energy)
                (real_Z_temp_pos unit uab1_sum uab1_sumpos
                   t Ht uab1_energy))
             (real_boltzmann_factor_temp unit t Ht uab1_energy tt)). }
  exact (real_eq_trans (uab1_bd t Ht tt)
           (real_mult
              (real_boltzmann_factor_temp unit t Ht uab1_energy tt)
              (real_inv_pos
                 (real_Z_temp unit uab1_sum t Ht uab1_energy)
                 (real_Z_temp_pos unit uab1_sum uab1_sumpos
                    t Ht uab1_energy)))
           real_one Hswap Hinv).
Qed.

(* ============ §5 · 链 B：能量钉前提（uab1_Hpinned） ============ *)
(* 语句形＝源模块节级前提 Hpinned 的全参具体化：                              *)
(*   sum (fun s => p_u(s)·e(s)) == E(p_{t*})。                              *)
(* 实算：两侧各自经 real_mult_one 归到 p(·)(tt)，再由链 A 在温 u 与          *)
(* 温 T_star=1 两实例下各归一为 1。                                         *)
(* 能量取任意非零函数即成立（本件取常值 1）——归一化谱系全链给出。          *)

Lemma uab1_Hpinned :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (uab1_sum
         (fun s : unit =>
            real_mult (uab1_bd u Hu s) (uab1_energy s)))
      (real_energy_exp_temp unit uab1_sum uab1_sumpos
         uab1_T_star uab1_T_star_pos uab1_energy).
Proof.
  intros u Hu.
  apply (real_eq_trans
           (uab1_sum
              (fun s : unit =>
                 real_mult (uab1_bd u Hu s) (uab1_energy s)))
           (uab1_bd u Hu tt)
           (real_energy_exp_temp unit uab1_sum uab1_sumpos
              uab1_T_star uab1_T_star_pos uab1_energy)).
  - exact (real_mult_one (uab1_bd u Hu tt)).
  - exact (real_eq_trans
             (uab1_bd u Hu tt)
             real_one
             (real_energy_exp_temp unit uab1_sum uab1_sumpos
                uab1_T_star uab1_T_star_pos uab1_energy)
             (uab1_bt_pt_one u Hu)
             (real_eq_sym
                (real_energy_exp_temp unit uab1_sum uab1_sumpos
                   uab1_T_star uab1_T_star_pos uab1_energy)
                real_one
                (real_eq_trans
                   (real_energy_exp_temp unit uab1_sum uab1_sumpos
                      uab1_T_star uab1_T_star_pos uab1_energy)
                   (uab1_bd uab1_T_star uab1_T_star_pos tt)
                   real_one
                   (real_mult_one (uab1_bd uab1_T_star uab1_T_star_pos tt))
                   (uab1_bt_pt_one uab1_T_star uab1_T_star_pos)))).
Qed.

(* ============ §6 · 链 C：KL 归零（uab1_kl_zero） ============ *)
(* KL(p_u‖p_{t*}) ≡ Σ p_u·(log p_u − log p_{t*}) 单点求和收敛为             *)
(* p_u(tt)·(log p_u(tt) − log p_{t*}(tt))；两对数经链 A、real_log_wd 与     *)
(* real_log_one 各归零，再经加/乘兼容引理收拢为零。                         *)

Lemma uab1_kl_zero : forall (u : Real) (Hu : real_lt real_zero u),
  real_eq (uab1_kl u Hu) real_zero.
Proof.
  intros u Hu.
  assert (Hlu : real_eq
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd u Hu tt) real_one
                (uab1_bd_pos u Hu tt) real_lt_zero_one
                (uab1_bt_pt_one u Hu))
             (real_log_one real_lt_zero_one)). }
  assert (Hl1 : real_eq
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd uab1_T_star uab1_T_star_pos tt) real_one
                (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)
                real_lt_zero_one
                (uab1_bt_pt_one uab1_T_star uab1_T_star_pos))
             (real_log_one real_lt_zero_one)). }
  apply (real_eq_trans
           (uab1_kl u Hu)
           (real_mult
              (uab1_bd u Hu tt)
              (real_plus
                 (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                 (real_opp
                    (real_log
                       (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
           real_zero).
  - exact (real_eq_refl
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))).
  - exact (real_eq_trans
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
             (real_mult real_one (real_plus real_zero (real_opp real_zero)))
             real_zero
             (RealSetoid.real_eq_mult_compat_adapt
                (uab1_bd u Hu tt) real_one
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))))
                (real_plus real_zero (real_opp real_zero))
                (uab1_bt_pt_one u Hu)
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   real_zero
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))
                   (real_opp real_zero)
                   Hlu
                   (RealSetoid.real_eq_opp_compat
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
                      real_zero
                      Hl1)))
             (real_eq_trans
                (real_mult real_one (real_plus real_zero (real_opp real_zero)))
                (real_mult real_one real_zero)
                real_zero
                (RealSetoid.real_eq_mult_compat_adapt
                   real_one real_one
                   (real_plus real_zero (real_opp real_zero))
                   real_zero
                   (real_eq_refl real_one)
                   (real_plus_opp real_zero))
                (uab1_mult_one_l real_zero))).
Qed.

(* ============ §7 · KL 增长前提（uab1_Hkl_right，eps 松弛形） ============ *)
(* 语句形＝源模块节级前提 Hkl_right 的全参具体化（uab1_T_star 取 real_one）。   *)
(* 实算：KL(v)==KL(u)==0（链 C）⟹(KL_v−KL_u)+eps==eps，再经 0<eps 序迁移。   *)

Lemma uab1_Hkl_right :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  pose proof (uab1_kl_zero v Hv) as Hv0.
  pose proof (uab1_kl_zero u Hu) as Hu0.
  assert (Hdiff : real_eq
                    (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                    real_zero).
  { exact (RealSetoid.real_eq_plus_compat_adapt
             (uab1_kl v Hv) real_zero
             (real_opp (uab1_kl u Hu)) (real_opp real_zero)
             Hv0
             (RealSetoid.real_eq_opp_compat (uab1_kl u Hu) real_zero Hu0)). }
  assert (Hsum : real_eq
                   (real_plus
                      (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                      eps)
                   eps).
  { exact (real_eq_trans
             (real_plus
                (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                eps)
             (real_plus real_zero eps)
             eps
             (RealSetoid.real_eq_plus_compat_adapt
                (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                real_zero
                eps eps
                Hdiff
                (real_eq_refl eps))
             (uab1_plus_zero_l eps)). }
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                    eps)
                 eps
                 Hsum)
              Heps)).
Qed.

(* ============ §8 · KL 衰减前提（uab1_Hkl_left，与增长前提对偶） ============ *)

Lemma uab1_Hkl_left :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  pose proof (uab1_kl_zero u Hu) as Hu0.
  pose proof (uab1_kl_zero v Hv) as Hv0.
  assert (Hdiff : real_eq
                    (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                    real_zero).
  { exact (RealSetoid.real_eq_plus_compat_adapt
             (uab1_kl u Hu) real_zero
             (real_opp (uab1_kl v Hv)) (real_opp real_zero)
             Hu0
             (RealSetoid.real_eq_opp_compat (uab1_kl v Hv) real_zero Hv0)). }
  assert (Hsum : real_eq
                   (real_plus
                      (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                      eps)
                   eps).
  { exact (real_eq_trans
             (real_plus
                (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                eps)
             (real_plus real_zero eps)
             eps
             (RealSetoid.real_eq_plus_compat_adapt
                (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                real_zero
                eps eps
                Hdiff
                (real_eq_refl eps))
             (uab1_plus_zero_l eps)). }
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                    eps)
                 eps
                 Hsum)
              Heps)).
Qed.

(* ============ §9 · 源模块出节五定理的全参落实（具体无假设实例） ============ *)

(* uab1_discharge_pinned_kl_entropy_eq（约束片熵亏恒等式）：KL + S == S_star。 *)
Theorem uab1_discharge_pinned_kl_entropy_eq :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_plus (uab1_kl u Hu) (uab1_ent u Hu))
            (uab1_ent uab1_T_star uab1_T_star_pos).
Proof.
  intros u Hu.
  exact (ems_pinned_kl_entropy_eq
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned u Hu).
Qed.

(* uab1_discharge_antitone_above（降支）：t* ≤ u ≤ v ⟹ S(p_v) ≤ S(p_u) + eps。 *)
Theorem uab1_discharge_antitone_above :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps).
Proof.
  intros u v Hu Hv Htu Huv eps Heps.
  exact (snd
           (ems_entropy_split_at_peak
              unit uab1_sum uab1_sumpos
              uab1_ext uab1_linear uab1_add
              uab1_T_star uab1_T_star_pos uab1_energy
              uab1_Hpinned uab1_Hkl_right uab1_Hkl_left)
           u v Hu Hv Htu Huv eps Heps).
Qed.

(* uab1_discharge_mono_below（升支）：u ≤ v ≤ t* ⟹ S(p_u) ≤ S(p_v) + eps。 *)
Theorem uab1_discharge_mono_below :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps).
Proof.
  intros u v Hu Hv Huv Hvt eps Heps.
  exact (fst
           (ems_entropy_split_at_peak
              unit uab1_sum uab1_sumpos
              uab1_ext uab1_linear uab1_add
              uab1_T_star uab1_T_star_pos uab1_energy
              uab1_Hpinned uab1_Hkl_right uab1_Hkl_left)
           u v Hu Hv Huv Hvt eps Heps).
Qed.

(* uab1_discharge_peak_bound（峰界；源模块出节形另含 le 接口参数）：          *)
(* 一切正温的熵 ≤ 峰熵 + eps。 *)
Theorem uab1_discharge_peak_bound :
  forall (u : Real) (Hu : real_lt real_zero u),
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu)
              (real_plus (uab1_ent uab1_T_star uab1_T_star_pos) eps).
Proof.
  intros u Hu eps Heps.
  exact (ems_entropy_peak_bound_above
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_le uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned
           u Hu eps Heps).
Qed.

(* uab1_discharge_split（分裂主件）：升支与降支两全称语句的乘积合取形。 *)
Theorem uab1_discharge_split :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v uab1_T_star ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps)) *
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le uab1_T_star u -> real_le u v ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps)).
Proof.
  split.
  - exact uab1_discharge_mono_below.
  - exact uab1_discharge_antitone_above.
Qed.

(* ============ §10 · 假设审计（Print Assumptions 全 Closed 为判据） ============ *)
Print Assumptions uab1_bt_pt_one.
Print Assumptions uab1_Hpinned.
Print Assumptions uab1_kl_zero.
Print Assumptions uab1_Hkl_right.
Print Assumptions uab1_Hkl_left.
Print Assumptions uab1_discharge_pinned_kl_entropy_eq.
Print Assumptions uab1_discharge_antitone_above.
Print Assumptions uab1_discharge_mono_below.
Print Assumptions uab1_discharge_peak_bound.
Print Assumptions uab1_discharge_split.
