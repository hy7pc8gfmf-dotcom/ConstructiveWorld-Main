(* ============================================================ *)
(* UpDebtDual.v —— 债务清理打包席（件 2，方案三 b）              *)
(*   缩放-温度对偶族 Real 层：抽象层 scale_temp_duality           *)
(*   （CW214KL_scan L28515–28529）与配套缩放族（L28440–28543）   *)
(*   的 Real 层镜像。                                            *)
(*                                                              *)
(*   定义族：                                                    *)
(*     real_softmax_scaled c z s      := e^{c·z_s}/Σ e^{c·z}     *)
(*     real_softmax_temp_param T z s  := e^{z/T}/Σ e^{z/T}       *)
(*   主定理：                                                    *)
(*     real_scale_temp_duality：∀c>0,                            *)
(*       real_softmax_scaled (1/c) == real_softmax_temp_param c  *)
(*   配套：缩放族正性/归一化 + real_scale_inv_T_eq_softmax_temp  *)
(*   （1/T 缩放族 == 库式温度化 softmax，配分定义性相等经        *)
(*   real_inv_pos_ext——纯恒等链）。                              *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/And）；全部 Qed 收口。                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section RealScaleDual.

(* 抽象状态空间（Real 层 Section 自声明，同 RealAttnMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* ---- 缩放族：real_softmax_scaled ---- *)

(* 缩放配分函数：Z_c(z) := Σ_s e^{c·z_s}（c 任意实） *)
Definition real_partition_function_scaled (c : Real) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s))).

(* 缩放配分正性：exp 恒正 × sum_pos_preserved *)
Lemma real_partition_function_scaled_pos :
  forall (c : Real) (z : S -> Real), real_lt real_zero (real_partition_function_scaled c z).
Proof.
  intros c z.
  unfold real_partition_function_scaled, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 缩放 softmax：sc(z; c)_s := e^{c·z_s}·inv(Z_c(z))（c 任意实） *)
Definition real_softmax_scaled (c : Real) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult c (z s)))
            (real_inv_pos (real_partition_function_scaled c z)
                          (real_partition_function_scaled_pos c z)).

(* 缩放族概率公理：正性（exp 恒正 × inv 正） *)
Theorem real_softmax_scaled_pos :
  forall (c : Real) (z : S -> Real) (s : S), real_lt real_zero (real_softmax_scaled c z s).
Proof.
  intros c z s.
  unfold real_softmax_scaled, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 缩放族概率公理：归一化 Σ_s sc(z;c)_s == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 线性提取
   （sum_linear）→ inv(Z_c)·Z_c == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_scaled_normalized :
  forall (c : Real) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_scaled c z s)) real_one.
Proof.
  intros c z.
  unfold real_softmax_scaled.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult c (z s)))
                             (real_inv_pos (real_partition_function_scaled c z)
                                           (real_partition_function_scaled_pos c z))))
          (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                   (real_partition_function_scaled_pos c z))
                     (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult c (z s)))
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))
                               (real_exp_pos_fn (real_mult c (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_c)·Z_c == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_partition_function_scaled c z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z))
                         (real_partition_function_scaled c z))
              (real_mult (real_partition_function_scaled c z)
                         (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 温度参数化族：(T0, HT0) 显式版 ---- *)

(* 温度参数化配分函数：Z_T0(z) := Σ_s e^{z_s/T0} *)
Definition real_partition_function_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s))).

(* 温度参数化配分正性 *)
Lemma real_partition_function_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_lt real_zero (real_partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold real_partition_function_temp_param, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 温度参数化 softmax：e^{z_s/T0}·inv(Z_T0(z)) *)
Definition real_softmax_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
            (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                          (real_partition_function_temp_param_pos T0 HT0 z)).

(* 温度参数化正性（配套） *)
Theorem real_softmax_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S),
    real_lt real_zero (real_softmax_temp_param T0 HT0 z s).
Proof.
  intros T0 HT0 z s.
  unfold real_softmax_temp_param, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 温度参数化归一化（配套） *)
Theorem real_softmax_temp_param_normalized :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_temp_param T0 HT0 z s)) real_one.
Proof.
  intros T0 HT0 z.
  unfold real_softmax_temp_param.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                             (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                           (real_partition_function_temp_param_pos T0 HT0 z))))
          (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                   (real_partition_function_temp_param_pos T0 HT0 z))
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
          real_one).
  - apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_partition_function_temp_param T0 HT0 z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z))
                         (real_partition_function_temp_param T0 HT0 z))
              (real_mult (real_partition_function_temp_param T0 HT0 z)
                         (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 主定理（件 2 核心）：缩放-温度对偶 ----
   ∀ c > 0：以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax。
   unfold 后两侧首因子（分子 e^{(1/c)·z_s}）逐字相同，mult_compat
   refl 消去；配分函数定义性相等（两侧都 unfold 为同一 Σ）⟹
   real_inv_pos_ext + real_eq_refl。纯恒等链，零新公理。 *)
Theorem real_scale_temp_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_scaled (real_inv_pos c Hc) z s)
            (real_softmax_temp_param c Hc z s).
Proof.
  intros c Hc z s.
  unfold real_softmax_scaled, real_softmax_temp_param.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos c Hc) z)
                        (real_partition_function_scaled_pos (real_inv_pos c Hc) z))
          (real_inv_pos (real_partition_function_temp_param c Hc z)
                        (real_partition_function_temp_param_pos c Hc z))
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos c Hc) z)
            (real_partition_function_temp_param c Hc z)
            (real_partition_function_scaled_pos (real_inv_pos c Hc) z)
            (real_partition_function_temp_param_pos c Hc z)
            (real_eq_refl _))).
Qed.

(* 反向对称：温度 c 的 softmax == 以 1/c 缩放的 softmax（real_eq_sym） *)
Lemma real_temp_is_scale_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_temp_param c Hc z s)
            (real_softmax_scaled (real_inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  apply real_eq_sym.
  apply real_scale_temp_duality.
Qed.

(* ---- Section 温度版桥：1/T 缩放族 == 库式温度化 softmax ----
   库式 softmax_temp（L28104 型）的温度 T/配分 Z_T 为 Section
   变量显式定义（不带参数化前件）；此处重建该形态，并以
   real_inv_pos_ext + real_eq_refl 桥接（配分定义性相等）。 *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable z_logits : S -> Real.

(* 库式温度化配分（Section 温度形态） *)
Definition real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma real_partition_function_temp_pos : real_lt real_zero real_partition_function_temp.
Proof.
  unfold real_partition_function_temp, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 库式温度化 softmax（Section 温度形态） *)
Definition real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos real_partition_function_temp real_partition_function_temp_pos).

(* 桥（对偶引理 c := T 实例 + 配分定义性相等） *)
Lemma real_scale_inv_T_eq_softmax_temp :
  forall s : S,
    real_eq (real_softmax_scaled (real_inv_pos T T_pos) z_logits s)
            (real_softmax_temp s).
Proof.
  intro s.
  unfold real_softmax_scaled, real_softmax_temp.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
                        (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits))
          (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp
            (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp_pos
            (real_eq_refl _))).
Qed.

End RealScaleDual.
