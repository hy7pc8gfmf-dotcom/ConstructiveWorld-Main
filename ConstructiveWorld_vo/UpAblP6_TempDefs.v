(* ===================================================================== *)
(* UpAblP6_TempDefs.v —— 温度分布族（Boltzmann/配分/熵）的单点载体实例化    *)
(*                                                                       *)
(* 使命：论文 6 源模块 UpReqTempDefs 温度节参族的独立链实例化——零 Require *)
(*   源模块，以单点空间 S := unit 加点态求和载体为实例，自证求和接口四引理 *)
(*   （uap6t_sum1_pos/ext/linear/add），逐枚给出源模块 12 声明的对应实例。 *)
(*                                                                       *)
(* 载体：Section Uap6TInst，节参数 T : Real（前提 T_pos : real_lt real_zero T） *)
(*   与 energy : unit -> Real；uap6t_bf(s) := e^{−e(s)/T}，uap6t_Z := Σ bf， *)
(*   uap6t_dist(s) := inv(Z)·bf(s)，uap6t_energy_exp := Σ p·e，           *)
(*   uap6t_entropy_dist := Σ p·(−log p)。                                 *)
(*                                                                       *)
(* 七证件证明路径：uap6t_bf_pos＝real_exp_neg_pos 直接推得；uap6t_Z_pos＝ *)
(*   uap6t_sum1_pos 加 uap6t_bf_pos 两步；uap6t_dist_pos＝                *)
(*   real_mult_pos_compat（inv 正 × 因子正）；uap6t_dist_normalized＝     *)
(*   线性提取加 real_mult_comm 与 real_inv_pos_correct；                  *)
(*   uap6t_log_inv_Z_aux＝real_log_mult 拆解加加法群律；                  *)
(*   uap6t_neg_log_boltzmann_point＝此件加 real_log_exp_neg 两步换形；     *)
(*   uap6t_entropy_temp_explicit＝点态换形→分配律→求和可加→β/logZ         *)
(*   两项分别提取（β 经线性提取，logZ 经 uap6t_dist_normalized 归一化）。 *)
(* 构造性注记：全件 Qed 闭合、零承认词面、纯构造性；语句面零 Prop 泄露    *)
(*   （全 real_eq/real_lt 值面）；11 项 Print Assumptions 全 Closed。      *)
(* 依赖：CW_ConstructiveWorld_219（Real/real_exp_neg/real_log 族所在）。  *)
(* 对标：统计力学 Boltzmann 分布与 Gibbs 熵公式（构造性离散单点实例）。   *)
(* 编译配方：Rocq 9.1 coqc 直调＋cpu_guard 包裹，输出经 -o 临时目录。     *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.

(* ============ 载体供给：单点求和（接口四引理自证） ============ *)

Definition uap6t_sum1 (f : unit -> Real) : Real := f tt.

Lemma uap6t_sum1_pos :
  forall f : unit -> Real,
    (forall s : unit, real_lt real_zero (f s)) ->
    real_lt real_zero (uap6t_sum1 f).
Proof.
  intros f H. exact (H tt).
Qed.

Lemma uap6t_sum1_ext :
  forall f g : unit -> Real,
    (forall s : unit, real_eq (f s) (g s)) ->
    real_eq (uap6t_sum1 f) (uap6t_sum1 g).
Proof.
  intros f g H. exact (H tt).
Qed.

Lemma uap6t_sum1_linear :
  forall (a : Real) (f : unit -> Real),
    real_eq (uap6t_sum1 (fun s : unit => real_mult a (f s)))
            (real_mult a (uap6t_sum1 f)).
Proof.
  intros a f. apply real_eq_refl.
Qed.

Lemma uap6t_sum1_add :
  forall f g : unit -> Real,
    real_eq (uap6t_sum1 (fun s : unit => real_plus (f s) (g s)))
            (real_plus (uap6t_sum1 f) (uap6t_sum1 g)).
Proof.
  intros f g. apply real_eq_refl.
Qed.

(* ============ 实例化：温度节参（T 任意正，能量任意） ============ *)

Section Uap6TInst.

Variables T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : unit -> Real.

(* 件①（定义）：Boltzmann 因子实例 bf(s) := e^{−e(s)/T} *)
Definition uap6t_bf (s : unit) : Real :=
  real_exp_neg (real_mult (real_inv_pos T T_pos) (energy s)).

(* 件②（证明）：因子正性——由 real_exp_neg_pos 直接推得 *)
Lemma uap6t_bf_pos : forall s : unit, real_lt real_zero (uap6t_bf s).
Proof.
  intro s. unfold uap6t_bf. apply real_exp_neg_pos.
Qed.

(* 件③（定义）：配分函数实例 Z := Σ bf（单点载体下即 bf(tt)） *)
Definition uap6t_Z : Real := uap6t_sum1 uap6t_bf.

(* 件④（证明）：配分正性——uap6t_sum1_pos 加件②两步 *)
Theorem uap6t_Z_pos : real_lt real_zero uap6t_Z.
Proof.
  unfold uap6t_Z. apply uap6t_sum1_pos.
  intro s. apply uap6t_bf_pos.
Qed.

(* 件⑤（定义）：分布实例 p(s) := inv(Z)·bf(s)（逐字段同源模块） *)
Definition uap6t_dist (s : unit) : Real :=
  real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) (uap6t_bf s).

(* 件⑥（证明）：分布逐点正性——real_mult_pos_compat（inv 正 × 因子正） *)
Lemma uap6t_dist_pos : forall s : unit, real_lt real_zero (uap6t_dist s).
Proof.
  intro s. unfold uap6t_dist.
  apply (real_mult_pos_compat
           (real_inv_pos uap6t_Z uap6t_Z_pos)
           (uap6t_bf s)).
  - apply real_inv_pos_pos.
  - apply uap6t_bf_pos.
Qed.

(* 件⑦（证明）：归一化——Σ p ≡ inv(Z)·Z ≡ 1（uap6t_sum1_linear 一步加   *)
(*   real_mult_comm 与 real_inv_pos_correct；单点载体下 Z 定义性等于 bf(tt)） *)
Theorem uap6t_dist_normalized : real_eq (uap6t_sum1 uap6t_dist) real_one.
Proof.
  apply (real_eq_trans
           (uap6t_sum1 uap6t_dist)
           (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) (uap6t_sum1 uap6t_bf))
           real_one).
  - exact (uap6t_sum1_linear (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_bf).
  - apply (real_eq_trans
             (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) (uap6t_sum1 uap6t_bf))
             (real_mult (uap6t_sum1 uap6t_bf) (real_inv_pos uap6t_Z uap6t_Z_pos))
             real_one).
    + exact (real_mult_comm (real_inv_pos uap6t_Z uap6t_Z_pos) (uap6t_sum1 uap6t_bf)).
    + exact (real_inv_pos_correct (uap6t_sum1 uap6t_bf) uap6t_Z_pos).
Qed.

(* 件⑩（证明）：log invZ 辅助恒等——real_log_mult 拆解加加法群律 *)
Lemma uap6t_log_inv_Z_aux :
  real_eq (real_log (real_inv_pos uap6t_Z uap6t_Z_pos)
                    (real_inv_pos_pos uap6t_Z uap6t_Z_pos))
          (real_opp (real_log uap6t_Z uap6t_Z_pos)).
Proof.
  set (X := real_log (real_inv_pos uap6t_Z uap6t_Z_pos)
                     (real_inv_pos_pos uap6t_Z uap6t_Z_pos)).
  set (LZ := real_log uap6t_Z uap6t_Z_pos).
  assert (Hsum : real_eq (real_plus X LZ) real_zero).
  { apply (real_eq_trans (real_plus X LZ)
             (real_log (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z)
                       (real_mult_positive (real_inv_pos uap6t_Z uap6t_Z_pos)
                          uap6t_Z (real_inv_pos_pos uap6t_Z uap6t_Z_pos)
                          uap6t_Z_pos))
             real_zero).
    - apply real_eq_sym.
      exact (real_log_mult (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z
              (real_inv_pos_pos uap6t_Z uap6t_Z_pos) uap6t_Z_pos).
    - apply (real_eq_trans
               (real_log (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z)
                         (real_mult_positive (real_inv_pos uap6t_Z uap6t_Z_pos)
                            uap6t_Z (real_inv_pos_pos uap6t_Z uap6t_Z_pos)
                            uap6t_Z_pos))
               (real_log real_one real_lt_zero_one)
               real_zero).
      + apply (real_log_wd
                 (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z)
                 real_one
                 (real_mult_positive (real_inv_pos uap6t_Z uap6t_Z_pos)
                    uap6t_Z (real_inv_pos_pos uap6t_Z uap6t_Z_pos)
                    uap6t_Z_pos)
                 real_lt_zero_one).
        exact (real_eq_trans
                 (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z)
                 (real_mult uap6t_Z (real_inv_pos uap6t_Z uap6t_Z_pos))
                 real_one
                 (real_mult_comm (real_inv_pos uap6t_Z uap6t_Z_pos) uap6t_Z)
                 (real_inv_pos_correct uap6t_Z uap6t_Z_pos)).
      + exact (real_log_one real_lt_zero_one). }
  apply (real_eq_trans X (real_plus X real_zero) (real_opp LZ)).
  - apply real_eq_sym. exact (real_plus_zero X).
  - apply (real_eq_trans
             (real_plus X real_zero)
             (real_plus X (real_plus LZ (real_opp LZ)))
             (real_opp LZ)).
    + apply (RealSetoid.real_eq_plus_compat_adapt X X real_zero
               (real_plus LZ (real_opp LZ)) (real_eq_refl X)).
      apply real_eq_sym. exact (real_plus_opp LZ).
    + apply (real_eq_trans
               (real_plus X (real_plus LZ (real_opp LZ)))
               (real_plus (real_plus X LZ) (real_opp LZ))
               (real_opp LZ)).
      * exact (real_plus_assoc X LZ (real_opp LZ)).
      * apply (real_eq_trans
                 (real_plus (real_plus X LZ) (real_opp LZ))
                 (real_plus real_zero (real_opp LZ))
                 (real_opp LZ)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus X LZ) real_zero (real_opp LZ) (real_opp LZ)
                    Hsum (real_eq_refl (real_opp LZ))).
        -- apply (real_eq_trans
                    (real_plus real_zero (real_opp LZ))
                    (real_plus (real_opp LZ) real_zero)
                    (real_opp LZ)).
           ++ exact (real_plus_comm real_zero (real_opp LZ)).
           ++ exact (real_plus_zero (real_opp LZ)).
Qed.

(* 件⑪（证明）：点态负 log 恒等——件⑩加 real_log_exp_neg 两步换形 *)
Lemma uap6t_neg_log_boltzmann_point :
  forall s : unit,
    real_eq (real_opp (real_log (uap6t_dist s) (uap6t_dist_pos s)))
            (real_plus (real_mult (real_inv_pos T T_pos) (energy s))
                       (real_log uap6t_Z uap6t_Z_pos)).
Proof.
  intro s.
  set (bta := real_inv_pos T T_pos).
  set (Hi := real_inv_pos_pos uap6t_Z uap6t_Z_pos).
  set (LZ := real_log uap6t_Z uap6t_Z_pos).
  apply (real_eq_trans
           (real_opp (real_log (uap6t_dist s) (uap6t_dist_pos s)))
           (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
           (real_plus (real_mult bta (energy s)) LZ)).
  - apply (RealSetoid.real_eq_opp_compat
             (real_log (uap6t_dist s) (uap6t_dist_pos s))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    apply (real_eq_trans
             (real_log (uap6t_dist s) (uap6t_dist_pos s))
             (real_plus (real_log (real_inv_pos uap6t_Z uap6t_Z_pos) Hi)
                        (real_log (real_exp_neg (real_mult bta (energy s)))
                                  (real_exp_neg_pos (real_mult bta (energy s)))))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    + apply (real_eq_trans
               (real_log (uap6t_dist s) (uap6t_dist_pos s))
               (real_log (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos)
                                    (real_exp_neg (real_mult bta (energy s))))
                         (real_mult_positive (real_inv_pos uap6t_Z uap6t_Z_pos)
                            (real_exp_neg (real_mult bta (energy s))) Hi
                            (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_log (real_inv_pos uap6t_Z uap6t_Z_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))).
      * exact (real_log_wd
                 (uap6t_dist s)
                 (real_mult (real_inv_pos uap6t_Z uap6t_Z_pos)
                            (real_exp_neg (real_mult bta (energy s))))
                 (uap6t_dist_pos s)
                 (real_mult_positive (real_inv_pos uap6t_Z uap6t_Z_pos)
                    (real_exp_neg (real_mult bta (energy s))) Hi
                    (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_eq_refl (uap6t_dist s))).
      * exact (real_log_mult (real_inv_pos uap6t_Z uap6t_Z_pos)
                 (real_exp_neg (real_mult bta (energy s))) Hi
                 (real_exp_neg_pos (real_mult bta (energy s)))).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos uap6t_Z uap6t_Z_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_opp LZ) (real_opp (real_mult bta (energy s))))
               (real_opp (real_plus LZ (real_mult bta (energy s))))).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos uap6t_Z uap6t_Z_pos) Hi)
                 (real_opp LZ)
                 (real_log (real_exp_neg (real_mult bta (energy s)))
                           (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_opp (real_mult bta (energy s)))
                 uap6t_log_inv_Z_aux
                 (real_log_exp_neg (real_mult bta (energy s)))).
      * apply real_eq_sym.
        exact (real_opp_plus LZ (real_mult bta (energy s))).
  - apply (real_eq_trans
             (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
             (real_plus LZ (real_mult bta (energy s)))
             (real_plus (real_mult bta (energy s)) LZ)).
    + exact (real_opp_opp (real_plus LZ (real_mult bta (energy s)))).
    + apply real_plus_comm.
Qed.

(* 件⑧（定义）：能量期望实例 E := Σ p·e *)
Definition uap6t_energy_exp : Real :=
  uap6t_sum1 (fun s : unit => real_mult (uap6t_dist s) (energy s)).

(* 件⑨（定义）：分布熵实例（参数序同源模块：正性前提居前） *)
Definition uap6t_entropy_dist
  (p : unit -> Real) (Hp : forall s : unit, real_lt real_zero (p s)) : Real :=
  uap6t_sum1 (fun s : unit => real_mult (p s) (real_opp (real_log (p s) (Hp s)))).
(* 件⑫（证明）：熵显式公式——点态换形→分配律→求和可加→β/logZ 双提取      *)
(*   （源模块配方在自持载体上复验） *)
Theorem uap6t_entropy_temp_explicit :
  real_eq (uap6t_entropy_dist uap6t_dist uap6t_dist_pos)
          (real_plus (real_mult (real_inv_pos T T_pos) uap6t_energy_exp)
                     (real_log uap6t_Z uap6t_Z_pos)).
Proof.
  unfold uap6t_entropy_dist.
  set (bta := real_inv_pos T T_pos).
  set (p := uap6t_dist).
  set (Hp := uap6t_dist_pos).
  set (LZ := real_log uap6t_Z uap6t_Z_pos).
  apply (real_eq_trans
           (uap6t_sum1 (fun s : unit => real_mult (p s) (real_opp (real_log (p s) (Hp s)))))
           (uap6t_sum1 (fun s : unit => real_mult (p s)
                              (real_plus (real_mult bta (energy s)) LZ)))
           (real_plus (real_mult bta uap6t_energy_exp) LZ)).
  - (* 步 1：逐点换形（应用件⑪） *)
    apply uap6t_sum1_ext.
    intro s.
    apply (RealSetoid.real_eq_mult_compat_adapt (p s) (p s)
             (real_opp (real_log (p s) (Hp s)))
             (real_plus (real_mult bta (energy s)) LZ)
             (real_eq_refl (p s))
             (uap6t_neg_log_boltzmann_point s)).
  - (* 步 2-4：real_distrib 逐点拆积和 → uap6t_sum1_add 分和 → β/logZ 双提取 *)
    apply (real_eq_trans
             (uap6t_sum1 (fun s : unit => real_mult (p s)
                                (real_plus (real_mult bta (energy s)) LZ)))
             (real_plus
                (uap6t_sum1 (fun s : unit => real_mult (p s) (real_mult bta (energy s))))
                (uap6t_sum1 (fun s : unit => real_mult (p s) LZ)))
             (real_plus (real_mult bta uap6t_energy_exp) LZ)).
    + apply (real_eq_trans
               (uap6t_sum1 (fun s : unit => real_mult (p s)
                                  (real_plus (real_mult bta (energy s)) LZ)))
               (uap6t_sum1 (fun s : unit =>
                  real_plus (real_mult (p s) (real_mult bta (energy s)))
                            (real_mult (p s) LZ)))
               (real_plus
                  (uap6t_sum1 (fun s : unit => real_mult (p s) (real_mult bta (energy s))))
                  (uap6t_sum1 (fun s : unit => real_mult (p s) LZ)))).
      * apply uap6t_sum1_ext.
        intro s. apply real_distrib.
      * apply (uap6t_sum1_add
                 (fun s : unit => real_mult (p s) (real_mult bta (energy s)))
                 (fun s : unit => real_mult (p s) LZ)).
    + apply (RealSetoid.real_eq_plus_compat_adapt
               (uap6t_sum1 (fun s : unit => real_mult (p s) (real_mult bta (energy s))))
               (real_mult bta uap6t_energy_exp)
               (uap6t_sum1 (fun s : unit => real_mult (p s) LZ))
               LZ).
      * (* β 项：Σ p·(β·e) ≡ β·E（逐点重排 → 线性提取 → 定义性相等） *)
        apply (real_eq_trans
                 (uap6t_sum1 (fun s : unit => real_mult (p s) (real_mult bta (energy s))))
                 (real_mult bta (uap6t_sum1 (fun s : unit => real_mult (p s) (energy s))))
                 (real_mult bta uap6t_energy_exp)).
        -- apply (real_eq_trans
                    (uap6t_sum1 (fun s : unit => real_mult (p s) (real_mult bta (energy s))))
                    (uap6t_sum1 (fun s : unit => real_mult bta (real_mult (p s) (energy s))))
                    (real_mult bta (uap6t_sum1 (fun s : unit => real_mult (p s) (energy s))))).
           ++ apply uap6t_sum1_ext.
              intro s.
              apply (real_eq_trans
                       (real_mult (p s) (real_mult bta (energy s)))
                       (real_mult (real_mult (p s) bta) (energy s))
                       (real_mult bta (real_mult (p s) (energy s)))).
              ** exact (real_mult_assoc (p s) bta (energy s)).
              ** apply (real_eq_trans
                          (real_mult (real_mult (p s) bta) (energy s))
                          (real_mult (real_mult bta (p s)) (energy s))
                          (real_mult bta (real_mult (p s) (energy s)))).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt
                              (real_mult (p s) bta) (real_mult bta (p s))
                              (energy s) (energy s)
                              (real_mult_comm (p s) bta) (real_eq_refl (energy s))).
                 --- apply real_eq_sym.
                     exact (real_mult_assoc bta (p s) (energy s)).
           ++ apply (uap6t_sum1_linear bta
                       (fun s : unit => real_mult (p s) (energy s))).
        -- exact (real_eq_refl (real_mult bta uap6t_energy_exp)).
      * (* logZ 项：Σ p·LZ ≡ LZ·Σ p ≡ LZ·1 ≡ LZ（应用件⑦归一化） *)
        apply (real_eq_trans
                 (uap6t_sum1 (fun s : unit => real_mult (p s) LZ))
                 (real_mult LZ (uap6t_sum1 p))
                 LZ).
        -- apply (real_eq_trans
                    (uap6t_sum1 (fun s : unit => real_mult (p s) LZ))
                    (uap6t_sum1 (fun s : unit => real_mult LZ (p s)))
                    (real_mult LZ (uap6t_sum1 p))).
           ++ apply uap6t_sum1_ext.
              intro s. apply real_mult_comm.
           ++ apply (uap6t_sum1_linear LZ p).
        -- apply (real_eq_trans
                    (real_mult LZ (uap6t_sum1 p))
                    (real_mult LZ real_one)
                    LZ).
           ++ apply (RealSetoid.real_eq_mult_compat_adapt LZ LZ
                       (uap6t_sum1 p) real_one
                       (real_eq_refl LZ) uap6t_dist_normalized).
           ++ exact (real_mult_one LZ).
Qed.

End Uap6TInst.

(* ============ 假设审计（全 Closed） ============ *)

Print Assumptions uap6t_sum1_pos.
Print Assumptions uap6t_sum1_ext.
Print Assumptions uap6t_sum1_linear.
Print Assumptions uap6t_sum1_add.
Print Assumptions uap6t_bf_pos.
Print Assumptions uap6t_Z_pos.
Print Assumptions uap6t_dist_pos.
Print Assumptions uap6t_dist_normalized.
Print Assumptions uap6t_log_inv_Z_aux.
Print Assumptions uap6t_neg_log_boltzmann_point.
Print Assumptions uap6t_entropy_temp_explicit.
