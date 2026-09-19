(* ============================================================ *)
(* UpAblEps49Main.v —— AB3 席：定理 4.9 诚实接口族承重件消融·实例供给 *)
(*   （N-3 承重主件 real_kl_decomp_full 解锁件），2026-09-19         *)
(* ============================================================ *)
(* 【对象语句实形定性（盘面复核）】                                   *)
(*   S08_RealMainlineDPO.v Section RealRLHFMain（2467–2731）内       *)
(*   Variable real_kl_decomp_full（2527 行）：真开放槽。区变量        *)
(*   S / real_sum_over_S(+ext/add) / real_base_loss / D / D_pos /    *)
(*   Z_align_r / Z_align_r_pos 全抽象。槽语句：                      *)
(*     forall p Hp Hnormp,                                           *)
(*       real_eq (real_free_energy p Hp)                             *)
(*         (real_plus (real_free_energy p_b p_b_pos)                   *)
(*                    (real_mult D (sumf (fun s => real_kl_term …))))) *)
(*   消费点实锤：real_rlhf_optimal_eps（2601）证明体 2613 行           *)
(*     by exact (real_kl_decomp_full pi Hpi Hnormpi)。                *)
(* 【数学定性（承 CWF 席 E458 定谳，本席逐字复核同判）】               *)
(*   F(p)−F(p_b)−D·Σkl = D·logZ·(Σp_b−1)，故 Z 抽象时槽语句为假，      *)
(*   诚实闭合仅两形：一般 Z 携 Hnormb（Σp_b==1）；或 Z 取配分函数      *)
(*   定义形内证归一化。本文件两形并交付。                              *)
(* 【本席增量（相对 CWF 席 RealKLDecomp.v 的真空白）】                  *)
(*   rkd_kl_decomp_full_partition 仍带四结构前提（求和 ext/add/linear  *)
(*   + 配分正性 Zp）。本席在具体载体（bool 二点状态空间 + 二点求和）    *)
(*   上把四前提全部内证，交付槽真前件形（仅 Hp Hnormp）的完全放电       *)
(*   实例——接口族「Real 层可实例化」自评的首个逐字达标实例。            *)
(* 【红线自检】纯构造性零承认件；Set 层零泄露（语句面全 forall 型，     *)
(*   序谓词全沿家族标准 Set 值位形）；提取零魔术常量；未触碰任何        *)
(*   既有文件。                                                        *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblEps49RKDBase.

(* ============================================================ *)
(* 第 1 部分：具体载体——bool 二点状态空间与二点求和                     *)
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

(* 二正相加仍正（S08 求和正性同款两步：零自等换形 + 双正相容） *)
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

(* 配分正性（第四建设内证：exp 恒正两支 + 二正相加） *)
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
(* 第 2 部分：alpha 桥——一般 Z 形（结论面与 S08 槽全局形零间隙）        *)
(*   诚实前提 Hnormb：任意 Z 下不可免（E458 定谳），槽形缺位申报。      *)
(*   本件即「签名对齐」实证：exact 直喂成功本身即对齐证书。             *)
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
(* 第 3 部分：伴件——具体载体上 Boltzmann 归一化（家族第 2 槽伴锁）      *)
(*   Z 取配分定义形，Hpart 逐字自反，归一化 Σp_b == 1 内证。            *)
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
(* 第 4 部分：主件——S08 槽真前件形（仅 Hp Hnormp）的完全放电实例       *)
(*   载体全 concrete：S := bool，sumf := e49m_esum2（三结构内证），      *)
(*   Z := 配分定义形（正性内证）。前提面与 S08:2527 槽逐字同形。        *)
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
(* 证据区：零外部未证假设 + 独立目录提取                                *)
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
