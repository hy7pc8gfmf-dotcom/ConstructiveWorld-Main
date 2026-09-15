(* ============================================================ *)
(* UpReqSteadyThermo.v *)
(* *)
(* 目的： 定理 4.9 steady_state_boltzmann 的 Real 层构造。 *)
(* 主件： real_steady_state_boltzmann：稳态分布的 Boltzmann 形（热力学侧载体）。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 本件为换载体改道（注意力侧载体到热力学侧载体）；Id 层 Variable 位逐位对位照抄，不弱化不加码（诚实前提申报）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqSteadyThermo.v —— 席T2：定理 4.9 steady_state_boltzmann         *)
(*   Real 层等式复刻（热力学侧稳态方程）2026-09-11                      *)
(* ------------------------------------------------------------------ *)
(* 【使命】论文正式版 L387 标注「Real 层无逐字复刻」、附录 B L1389      *)
(*   「方程形态无逐字复刻（未迁移）」——本件闭合后摘除该标签。           *)
(*   Id 锚：S04_RealExpLogConv.v Section BoltzmannSteadyState（L1853）  *)
(*   的 steady_state_boltzmann（L1904）：                               *)
(*     Σ_{s'} p(s')·T(s',s) == p(s)（详细平衡 ⟹ 稳态）。                *)
(* ------------------------------------------------------------------ *)
(* 【黄金参照】S08_RealMainlineDPO.v L2076-2130 Section RealAttnSteady  *)
(*   的 real_steady_state_boltzmann_attn（注意力侧稳态 Real 复刻，      *)
(*   论文定理 5.3a；经验卡 E246）：同构五步链——                          *)
(*     步1 逐点 detailed balance 替换（real_detailed_balance）          *)
(*     步2 求和外延（real_sum_over_S_ext）                              *)
(*     步3 线性提取 p(s)（real_sum_over_S_linear）                      *)
(*     步4 核归一化（real_transition_normalization）                    *)
(*     步5 real_mult_one 完成                                           *)
(*   本件=换载体改道：注意力侧载体 → 热力学侧载体                        *)
(*     real_boltzmann_prob := inv_pos Z_r · exp_neg(inv_pos D · energy s) *)
(*   （rfep_boltzmann_normalized_real / UpReqRealFEP.v L331 同款形态，  *)
(*   partition 前提显式入节）。                                         *)
(* ------------------------------------------------------------------ *)
(* 【诚实前提申报（Id 层 Variable 位逐位对位——照抄位，不弱化不加码）】  *)
(*   Id 位 → 本件槽：                                                   *)
(*     base_loss            → energy : S -> Real                        *)
(*     D / D_pos            → D / D_pos : real_lt real_zero D           *)
(*     Z / Z_pos            → Z_r / Z_r_pos : real_lt real_zero Z_r     *)
(*     partition_condition  → real_partition_condition（real_eq 载体，  *)
(*                            rfep L331 Hpart 同款轴向）                *)
(*     transition           → real_transition                          *)
(*     transition_nonneg    → real_transition_nonneg（real_le Set 载体；*)
(*                            五步链零消费，纯对位保留，同 Id 层原样）   *)
(*     transition_normalization → real_transition_normalization        *)
(*     detailed_balance     → real_detailed_balance（Id 同向：          *)
(*         p s·T s s' == p s'·T s' s；施用实参序 (s' s) 与 Id 原证       *)
(*         一致，E246 坑1 实参序=绑定序纪律）                           *)
(*   求和载体三槽（S/ext/linear）为 Real 层平行接口（S08 同位，          *)
(*   E246 坑2）。全件无非推导假设：Print Assumptions 闭（G3 探针）。    *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（real_eq/real_lt/real_le 全     *)
(*   Set 载体，S02 L456/L460）；real_eq 非 Id 禁改写——全链              *)
(*   real_eq_trans + RealSetoid compat（E393 纪律）；全件 Qed 闭合。    *)
(* 编译配方：_t2_build.cmd + cpu_guard（CoreN 3，LoadLimit 65）          *)


(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* Section RealThermoSteady：与 Id 层 BoltzmannSteadyState 同构         *)
(* ============================================================ *)
Section RealThermoSteady.

(* 求和载体（Real 层平行接口，S08 RealAttnSteady 同位） *)
Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* Id 位：base_loss / D / D_pos / Z / Z_pos *)
Variable energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_r : Real.
Variable Z_r_pos : real_lt real_zero Z_r.

(* Id 位：partition_condition（real_eq 载体，rfep_boltzmann_normalized_real 同款轴向） *)
Variable real_partition_condition :
  real_eq Z_r
          (real_sum_over_S
             (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).

(* Id 位：boltzmann_unnorm / boltzmann_prob（热力学侧载体） *)
Definition real_boltzmann_unnorm (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).
Definition real_boltzmann_prob (s : S) : Real :=
  real_mult (real_inv_pos Z_r Z_r_pos) (real_boltzmann_unnorm s).

(* Id 位：transition / transition_nonneg / transition_normalization / detailed_balance *)
Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall (s s' : S),
  real_le real_zero (real_transition s s').
Variable real_transition_normalization : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_transition s s')) real_one.
Variable real_detailed_balance : forall (s s' : S),
  real_eq (real_mult (real_boltzmann_prob s) (real_transition s s'))
          (real_mult (real_boltzmann_prob s') (real_transition s' s)).

(* ============================================================ *)
(* 旗舰：稳态方程（定理 4.9 Real 层等式复刻）                           *)
(*   Σ_{s'} p(s')·T(s',s) == p(s)                                      *)
(*   五步链：①detailed balance 逐点 → ②ext 求和外延 → ③linear 提取     *)
(*   → ④核归一化（mult_compat）→ ⑤mult_one 完成                        *)
(* ============================================================ *)
Theorem real_steady_state_boltzmann : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s)))
          (real_boltzmann_prob s).
Proof.
  intro s.
  (* 步②：求和外延壳（real_sum_over_S_ext）——逐点前提即步① *)
  apply (real_eq_trans _
           (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s')))
           _).
  - apply (real_sum_over_S_ext
             (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s))
             (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s'))).
    (* 步①：逐点 detailed balance 替换（实参序 (s' s)，Id 原证同款） *)
    intro s'. exact (real_detailed_balance s' s).
  - (* 步③：线性提取 p(s)（real_sum_over_S_linear） *)
    apply (real_eq_trans _
             (real_mult (real_boltzmann_prob s) (real_sum_over_S (fun s' : S => real_transition s s')))
             _).
    + apply (real_sum_over_S_linear (real_boltzmann_prob s) (fun s' : S => real_transition s s')).
    + (* 步④：核归一化（real_transition_normalization 经 mult_compat 对角入位） *)
      apply (real_eq_trans _ (real_mult (real_boltzmann_prob s) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat (real_boltzmann_prob s)
                 (real_sum_over_S (fun s' : S => real_transition s s'))
                 (real_boltzmann_prob s) real_one
                 (real_eq_refl _) (real_transition_normalization s)).
      * (* 步⑤：p(s)·1 == p(s)（real_mult_one 完成） *)
        exact (real_mult_one (real_boltzmann_prob s)).
Qed.

End RealThermoSteady.
