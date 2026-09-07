(* ============================================================ *)
(* UpDebtGibbsT.v —— 债务清理打包席（件 1，方案三 c）            *)
(*   attention_is_gibbs_temp 的 Real 层复刻：任意温度下          *)
(*   softmax == Boltzmann。                                      *)
(*                                                              *)
(*   模板 = 根内单位温度版 real_attention_is_gibbs               *)
(*   （CW214KL_scan L43231）逐字平移：                           *)
(*     温度相等前提 real_eq (inv T) (inv D)                      *)
(*     + energy == −logits + 配分相等                            *)
(*     ⟹ 逐点 real_eq (real_softmax_temp s) (real_boltzmann_dist_attn s). *)
(*                                                              *)
(*   Real 层原本无温度化 softmax/配分定义，此处先建：            *)
(*     real_partition_function_temp := Σ e^{z/T}，               *)
(*     real_softmax_temp s := e^{z_s/T}·inv(Z_T)，               *)
(*   并配套正性/归一化小引理。证明核：real_inv 代数 +            *)
(*   cauchy_real_exp_wd + real_inv_pos_ext + real_mult_comm ——   *)
(*   单位温度版每一步都有对应。                                  *)
(*                                                              *)
(*   世界选择跟随根内 real_attention_is_gibbs（CW214KL_scan；    *)
(*   CW_ConstructiveWorld_219.vo 与本地 9.0/9.1 平台 vo 版本号   *)
(*   不兼容，见交付报告）。                                      *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/库内 And）；全部 Qed 收口。                            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section RealAttnGibbsTemp.

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

(* 温度（推理侧 T 与热力学侧 D）、能量、logits（Real 层） *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* ---- 基础助手：real_exp_neg 的 real_eq 外延 ---- *)
(*（cauchy_real_exp_wd 的 real_exp_neg 形态；real_exp_neg x       *)
(*  定义性 = cauchy_real_exp (−x)）                              *)
Lemma real_exp_neg_wd : forall a b : Real,
  real_eq a b -> real_eq (real_exp_neg a) (real_exp_neg b).
Proof.
  intros a b H. unfold real_exp_neg.
  apply cauchy_real_exp_wd.
  apply (RealSetoid.real_eq_opp_compat a b H).
Qed.

(* ---- 温度化配分函数（Real 层）：Z_T := Σ_s e^{z_s/T} ---- *)
Definition real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma real_partition_function_temp_pos : real_lt real_zero real_partition_function_temp.
Proof.
  unfold real_partition_function_temp, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* ---- 温度化 softmax（Real 层）：e^{z_s/T}·inv(Z_T) ---- *)
Definition real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos real_partition_function_temp real_partition_function_temp_pos).

(* 配套正性：exp 恒正 × inv 正（real_mult_pos_compat） *)
Theorem real_softmax_temp_pos : forall s : S, real_lt real_zero (real_softmax_temp s).
Proof.
  intro s. unfold real_softmax_temp, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 配套归一化：Σ_s softmax_temp(s) == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 标量线性提取
   （sum_linear）→ inv(Z_T)·Z_T == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_temp_normalized :
  real_eq (real_sum_over_S (fun s => real_softmax_temp s)) real_one.
Proof.
  unfold real_softmax_temp.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                             (real_inv_pos real_partition_function_temp
                                           real_partition_function_temp_pos)))
          (real_mult (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                               (real_inv_pos real_partition_function_temp
                                             real_partition_function_temp_pos)))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos real_partition_function_temp
                                             real_partition_function_temp_pos)
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_T)·Z_T == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            (real_mult (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
                       real_partition_function_temp)
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
                         real_partition_function_temp)
              (real_mult real_partition_function_temp
                         (real_inv_pos real_partition_function_temp real_partition_function_temp_pos))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- Boltzmann 侧（同单位温度版结构） ---- *)
(* Boltzmann 因子（Real 层）：e^{−e(s)/D} *)
Definition real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* 热力学配分（Real 层）：Σ_s boltzmann_factor *)
Definition real_Z_thermo : Real := real_sum_over_S real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero real_Z_thermo.

(* Boltzmann 分布（Real 层）：inv(Z_thermo)·factor *)
Definition real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos real_Z_thermo real_Z_thermo_pos) (real_boltzmann_factor s).

(* ---- 旗舰（件 1）：任意温度下 softmax == Boltzmann ----
   前提：① 1/T == 1/D（温度统一，real_inv_pos 按位相等）
         ② energy == −logits（逐 s）
         ③ Z_thermo == Z_T（配分相等）
   结论：逐 s：real_softmax_temp s == real_boltzmann_dist_attn s。
   证明核（单位温度版每步对应）：
     因子桥（real_opp_mult + 温度统一 + energy 替换 + exp 外延）
     → 逆元统一（HZ + real_inv_pos_ext）
     → 组装（mult 交换 + mult_compat 四槽按位）。 *)
Theorem real_attention_is_gibbs_temp :
  (real_eq (real_inv_pos T T_pos) (real_inv_pos D D_pos)) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq real_Z_thermo real_partition_function_temp ->
  forall s : S, real_eq (real_softmax_temp s) (real_boltzmann_dist_attn s).
Proof.
  intros HDT Henergy HZ s.
  unfold real_softmax_temp, real_boltzmann_dist_attn, real_boltzmann_factor, real_exp_pos_fn.
  (* 1. 因子桥：e^{-(-z(s)/T)} == e^{-e(s)/D} *)
  assert (Hf : real_eq (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).
  {
    apply real_exp_neg_wd.
    apply (real_eq_trans _ (real_mult (real_inv_pos D D_pos) (real_opp (z_logits s))) _).
    - apply (real_eq_trans _ (real_mult (real_inv_pos T T_pos) (real_opp (z_logits s))) _).
      + (* −(z/T) == (1/T)·(−z)（real_opp_mult） *)
        apply real_opp_mult.
      + (* (1/T)·(−z) == (1/D)·(−z)（温度统一 HDT） *)
        apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos T T_pos) (real_inv_pos D D_pos)
                (real_opp (z_logits s)) (real_opp (z_logits s))
                HDT (real_eq_refl _)).
    - (* (1/D)·(−z) == (1/D)·e（energy == −logits，对称） *)
      apply (RealSetoid.real_eq_mult_compat_adapt
              (real_inv_pos D D_pos) (real_inv_pos D D_pos)
              (real_opp (z_logits s)) (energy s)
              (real_eq_refl _) (real_eq_sym _ _ (Henergy s))).
  }
  (* 2. 逆元统一：inv(Z_thermo) == inv(Z_T)（HZ + real_inv_pos_ext） *)
  assert (Hie : real_eq (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                        (real_inv_pos real_partition_function_temp
                                      real_partition_function_temp_pos)).
  { apply (real_inv_pos_ext real_Z_thermo real_partition_function_temp
                            real_Z_thermo_pos real_partition_function_temp_pos).
    exact HZ. }
  (* 3. 组装（镜像单位温度版第 3 步） *)
  apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                    (real_inv_pos real_partition_function_temp
                                                  real_partition_function_temp_pos)) _).
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                      (real_inv_pos real_Z_thermo real_Z_thermo_pos)) _).
    + apply (RealSetoid.real_eq_mult_compat_adapt
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
              (real_inv_pos real_Z_thermo real_Z_thermo_pos)
              (real_eq_refl _) (real_eq_sym _ _ Hie)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                                        (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))) _).
      * apply real_mult_comm.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                (real_eq_refl _) Hf).
Qed.

End RealAttnGibbsTemp.
