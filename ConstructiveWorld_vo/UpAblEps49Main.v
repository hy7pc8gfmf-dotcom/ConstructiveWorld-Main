(* ==========================================================================)
   UpAblEps49Main.v — KL 分解恒等式两形闭合在具体载体上的完全实例
   使命: bool 二点状态空间与二点求和上把四结构前提（求和 ext/add/linear 与配分正性）全部内证，给出仅余 (Hp, Hnormp) 的完全实例化 e49m_real_kl_decomp_full_bool。
   依赖: QArith.Qring、CW_ConstructiveWorld_219、UpAblEps49RKDBase、Extraction。
   对标: 有限和上的 KL 分解恒等式（自由能与相对熵关系）。
   构造性: 零承认词面；Set 层承载（语句面全 forall 型）；提取零魔术常量；未触碰任何既有文件。
   编译配方: Rocq 9.1 直调与 cpu_guard；编译输出 -o 临时目录，树内不动。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
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
Require Import UpAblEps49RKDBase.

(* ============================================================ *)
(* §1 具体载体：bool 二点状态空间与二点求和                                      *)
(* ============================================================ *)

Definition e49m_esum2 (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

(* 结构前提一：外延性（逐点相等 ⟹ 求和相等） *)
Lemma e49m_esum2_ext : forall (f g : bool -> Real),
  (forall s : bool, real_eq (f s) (g s)) -> real_eq (e49m_esum2 f) (e49m_esum2 g).
Proof.
  intros f g H. unfold e49m_esum2.
  exact (RealSetoid.real_eq_plus_compat_adapt
           (f true) (g true) (f false) (g false) (H true) (H false)).
Qed.

(* 结构前提二：加法分配 *)
Lemma e49m_esum2_add : forall (f g : bool -> Real),
  real_eq (e49m_esum2 (fun s : bool => real_plus (f s) (g s)))
          (real_plus (e49m_esum2 f) (e49m_esum2 g)).
Proof. intros f g. unfold e49m_esum2. rkd_alg. Qed.

(* 结构前提三：标量线性 *)
Lemma e49m_esum2_linear : forall (a : Real) (f : bool -> Real),
  real_eq (e49m_esum2 (fun s : bool => real_mult a (f s)))
          (real_mult a (e49m_esum2 f)).
Proof. intros a f. unfold e49m_esum2. rkd_alg. Qed.

(* 二正相加仍正（由 real_plus_zero 与 real_lt_plus_compat 两步）             *)
Lemma e49m_esum2_pos2 : forall (x y : Real),
  real_lt real_zero x -> real_lt real_zero y ->
  real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                                  (real_plus x y)).
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero x real_zero y).
    + exact Hx.
    + exact Hy.
Qed.

(* 配分正性（结构前提四的内证：real_exp_neg_pos 两支 + 二正相加）                     *)
Lemma e49m_partition2_pos : forall (e : bool -> Real) (D : Real)
  (D_pos : real_lt real_zero D),
  real_lt real_zero
    (e49m_esum2 (fun s : bool => real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (e s)))).
Proof.
  intros e D D_pos. unfold e49m_esum2. apply e49m_esum2_pos2.
  - apply real_exp_neg_pos.
  - apply real_exp_neg_pos.
Qed.

(* ============================================================ *)
(* §2 一般 Z 形：结论与 S08 假设全局形逐字同构                                   *)
(*   数学前提 Hnormb：任意 Z 下不可免，为原假设所缺，如实标示。                          *)
(*   签名对齐的直接证据：证明体 exact 直引 rkd_kl_decomp_full。                  *)
(* ============================================================ *)

Theorem e49m_real_kl_decomp_full :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (e : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S e D D_pos Z Z_pos)) real_one),
  real_eq (real_free_energy S sumf e D p Hp)
          (real_plus
             (real_free_energy S sumf e D
                (real_boltzmann_dist_r S e D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos S e D D_pos Z Z_pos))
             (real_mult D
                (sumf (fun s : S =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r S e D D_pos Z Z_pos s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos S e D D_pos Z Z_pos s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear e D D_pos Z Z_pos p Hp Hnormp Hnormb.
  exact (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear
           e D D_pos Z Z_pos p Hp Hnormp Hnormb).
Qed.

(* ============================================================ *)
(* §3 伴生命题：具体载体上的 Boltzmann 归一化                                  *)
(*   Z 取配分定义形，Hpart 为 real_eq_refl，归一化 Σ p_b == 1 内证。            *)
(* ============================================================ *)

Theorem e49m_boltzmann_normalized_bool :
  forall (e : bool -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_eq
    (e49m_esum2 (real_boltzmann_dist_r bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos)))
    real_one.
Proof.
  intros e D D_pos.
  exact (rkd_boltzmann_normalized bool e49m_esum2 e49m_esum2_ext
           e49m_esum2_linear e D D_pos
           (e49m_esum2 (fun s : bool => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (e s))))
           (e49m_partition2_pos e D D_pos)
           (real_eq_refl _)).
Qed.

(* ============================================================ *)
(* §4 主定理：S08 假设形（仅 Hp Hnormp）的完全实例化                             *)
(*   载体全具体：S := bool，sumf := e49m_esum2（三结构前提内证），                *)
(*   Z := 配分定义形（正性内证）。前提与 S08 原假设逐字同形。                           *)
(* ============================================================ *)

Theorem e49m_real_kl_decomp_full_bool :
  forall (e : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s))
    (Hnormp : real_eq (e49m_esum2 p) real_one),
  real_eq (real_free_energy bool e49m_esum2 e D p Hp)
          (real_plus
             (real_free_energy bool e49m_esum2 e D
                (real_boltzmann_dist_r bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos))
                (real_boltzmann_dist_r_pos bool e D D_pos
                   (e49m_esum2 (fun s : bool => real_exp_neg
                                    (real_mult (real_inv_pos D D_pos) (e s))))
                   (e49m_partition2_pos e D D_pos)))
             (real_mult D
                (e49m_esum2 (fun s : bool =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r bool e D D_pos
                        (e49m_esum2 (fun s0 : bool => real_exp_neg
                                         (real_mult (real_inv_pos D D_pos) (e s0))))
                        (e49m_partition2_pos e D D_pos) s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos bool e D D_pos
                        (e49m_esum2 (fun s0 : bool => real_exp_neg
                                         (real_mult (real_inv_pos D D_pos) (e s0))))
                        (e49m_partition2_pos e D D_pos) s))))).
Proof.
  intros e D D_pos p Hp Hnormp.
  exact (rkd_kl_decomp_full_partition bool e49m_esum2 e49m_esum2_ext
           e49m_esum2_add e49m_esum2_linear e D D_pos p Hp Hnormp
           (e49m_partition2_pos e D D_pos)).
Qed.

(* ============================================================ *)
(* 依赖审计：零外部未证假设；独立目录提取                                           *)
(* ============================================================ *)

Print Assumptions e49m_esum2_ext.
Print Assumptions e49m_esum2_add.
Print Assumptions e49m_esum2_linear.
Print Assumptions e49m_partition2_pos.
Print Assumptions e49m_real_kl_decomp_full.
Print Assumptions e49m_boltzmann_normalized_bool.
Print Assumptions e49m_real_kl_decomp_full_bool.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../attn/_ab3_g3_ext".
Separate Extraction e49m_real_kl_decomp_full_bool.
Separate Extraction e49m_boltzmann_normalized_bool.
Separate Extraction e49m_real_kl_decomp_full.
