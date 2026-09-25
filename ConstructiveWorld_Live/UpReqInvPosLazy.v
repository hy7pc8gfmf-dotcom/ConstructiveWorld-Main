(* UpReqInvPosLazy.v —— inv_pos 运行瓶颈·惰性化主轨（门定理形）          *) (* 使命: 把急切选 k 的求值路径替换为按需强制的定理门：k 站位由调用方    *)
(*     给定（N 显式入参），门不等式（Q 层可核）真 ⟹ 终装语句 sigT k     *)
(*     （k = S N）当站闭合；使 inv_pos 载体归约与无界选 k 链均不入      *)
(*     求值路径。                                                       *)
(* 依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSampling、UpReqConcSoftmax、UpReqConcB1、UpReqConcMixSel、UpReqDist、UpAblMetaWorld3、UpAblMetaWindow、UpReqConcB2Time、UpAblB2WindowTie。 *)
(* 【根因判定】                                                  *)
(*   P1：inv_pos 位=证明载体归约病理（擦除即愈，非本件对象）；              *)
(*   P2：kernel/titer/终装 k 链=无界螺旋（双侧同根）——            *)
(*        病灶在 cmk 终装以 real_arch 锚「急切选 k」：inv_pos·arch·       *)
(*        证书链在选站位时被一次性强制到底。                              *)
(* 【惰性化重述（A1 UpReqMixLazy 门定理路线同款，B2 链版）】               *)
(*   把急切选 k 替换为按需交付的定理门：k 站位由调用方给定（N 显式入参），  *)
(*   门不等式（Q 层可核）真 ⟹ 终装语句 sigT k（k = S N）当站闭合。         *)
(*   组装＝两条已证链的给定-k 剖面：                                      *)
(*     · 收缩支：rsq_bounded_softmax_tv_iter（Doeblin 迭代收缩，           *)
(*       TV(T^k) ≤ κ^k·TV₀，κ = 1 − δ星；上游成品零改直接代入）；              *)
(*     · 预算支：cmk_pow_tail（@ums_pow_tail 本就收 N 为参——arch 锚        *)
(*       只是它的一个调用方；本件换成调用方直接代入，arch 从求值路径除名）。    *)
(* 【thunk/Share 装置（本件运行语义核心）】                                *)
(*   全部重证书支（收缩支/预算支/门证书/质量前件）以不透明引用收束         *)
(*   （Qed 收束=按引用共享的 thunk），运行位只强制 witness（k 站位）；      *)
(*   故 vm 取 k 沿途零展开 inv_pos/kernel 载体——P1 载体病理与 P2 无界      *)
(*   螺旋均不入求值路径。数值内容独立性由 Q 层复核道单独承担。             *)
(* 【运行证据（mu=nu=one/T=1/Δ=3/预算=1/2）】                  *)
(*   ivl_run：vm_compute 真跑出 k；ivl_recheck：κ^1·TV₀ < 1/2 Q 层 true；  *)
(*   ivl_kneed：泛型几何界对照站（TV₀=1 最坏档 Q 层扫描）。                *)
(* 构造性注记（红线自审）：纯构造性；语句面全 Set 层（req/le/lt/sigT 均基座 Set 面）；  *)
(*   零公理零承认零参数化零弃权（红线八词零命中）；新件全透明可提取；      *)
(*   本件零提取，Obj.magic 记 0（家规轨）；ivl_ 前缀全库防撞已核。         *)
(* 编译配方：Rocq 9.1 bash 直调，-Q 单根，unset COQLIB/ROCQLIB，cpu_guard 绑核。 *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSampling.
Require Import UpReqConcSoftmax.
Require Import UpReqConcB1.
Require Import UpReqConcMixSel.
Require Import UpReqDist.
Require Import UpAblMetaWorld3.
Require Import UpAblMetaWindow.
Require Import UpReqConcB2Time.
Require Import UpAblB2WindowTie.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* 一、收缩率具体件（副本 cmk 链 Let 形，逐 delta 可转换）                  *)
(* ============================================================ *)

Definition ivl_invT : Real := inv_pos cbt_temp cbt_temp_pos.
Definition ivl_lo : Real := rsq_exp_pos_fn (mult ivl_invT (opp cbt_Delta)).
Definition ivl_delta_star : Real := mult ivl_lo ivl_lo.
Definition ivl_omd : Real := req_minus one ivl_delta_star.

Lemma ivl_ds_pos : lt zero ivl_delta_star.
Proof.
  exact (mult_positive ivl_lo ivl_lo
           (epp_pos (mult ivl_invT (opp cbt_Delta)))
           (epp_pos (mult ivl_invT (opp cbt_Delta)))).
Qed.

Lemma ivl_ds_lt_one : lt ivl_delta_star one.
Proof.
  exact (rsq_bs_delta_star_lt_one cbt_temp cbt_temp_pos cbt_Delta cbt_Delta_pos).
Qed.

(* ============================================================ *)
(* 二、给定-k 剖面两支（重证书支全 thunk 收束）                             *)
(* ============================================================ *)

(* 预算支：门（站位 N 的 arch 不等式形，Q 层可核）⟹ κ^(S N)·TV₀ < budget *)
Lemma ivl_leg_tail : forall (mu nu : unit -> Real)
    (Hmu : req (cbt_sumf mu) one) (Hnu : req (cbt_sumf nu) one)
    (budget : Real) (Hbudget : lt zero budget) (N : nat),
  lt (mult (cbt_tv mu nu)
        (inv_pos (mult ivl_delta_star budget)
                 (mult_positive ivl_delta_star budget ivl_ds_pos Hbudget)))
     (cmk_scale (Datatypes.S N) one) ->
  lt (mult (cmk_r_pow ivl_omd (Datatypes.S N)) (cbt_tv mu nu)) budget.
Proof.
  intros mu nu Hmu Hnu budget Hbudget N Hgate.
  (* cmk_pow_tail 的 witness 逐 delta 定义性即 S N（检验实证 reflexivity 道）；
     接驳位须内联常量（context local 不入 tactic 展开道） *)
  assert (Heq : projT1 (cmk_pow_tail real_lt_plus_compat_lt_le ivl_omd (cbt_tv mu nu) budget
                    ivl_delta_star N
                    (mult_positive ivl_delta_star budget ivl_ds_pos Hbudget)
                    ivl_ds_pos ivl_ds_lt_one
                    (req_refl (req_minus one ivl_delta_star))
                    (cbt_tv0 mu nu Hmu Hnu)
                    (lt_le_iff zero budget (inl Hbudget))
                    Hgate) = Datatypes.S N) by reflexivity.
  rewrite <- Heq.
  exact (projT2 (cmk_pow_tail real_lt_plus_compat_lt_le ivl_omd (cbt_tv mu nu) budget
                    ivl_delta_star N
                    (mult_positive ivl_delta_star budget ivl_ds_pos Hbudget)
                    ivl_ds_pos ivl_ds_lt_one
                    (req_refl (req_minus one ivl_delta_star))
                    (cbt_tv0 mu nu Hmu Hnu)
                    (lt_le_iff zero budget (inl Hbudget))
                    Hgate)).
Qed.

(* 收缩支：TV(T^k μ, T^k ν) ≤ κ^k · TV₀，κ = 1 − δ星（Doeblin 收缩直接代入） *)
Lemma ivl_leg_iter : forall (mu nu : unit -> Real)
    (Hmu : req (cbt_sumf mu) one) (Hnu : req (cbt_sumf nu) one) (k : nat),
  le (cbt_tv (cbt_titer k mu) (cbt_titer k nu))
     (mult (cmk_r_pow ivl_omd k) (cbt_tv mu nu)).
Proof.
  intros mu nu Hmu Hnu k.
  exact (le_id_r (cbt_tv (cbt_titer k mu) (cbt_titer k nu))
           (mult (req_r_pow ivl_omd k) (cbt_tv mu nu))
           (mult (cmk_r_pow ivl_omd k) (cbt_tv mu nu))
           (req_mult_compat (req_r_pow ivl_omd k) (cmk_r_pow ivl_omd k)
              (cbt_tv mu nu) (cbt_tv mu nu)
              (req_sym _ _ (cmk_r_pow_req_r_pow ivl_omd k))
              (req_refl (cbt_tv mu nu)))
           (rsq_bounded_softmax_tv_iter unit cbt_sumf
              (csm_sum_ext unit [tt]) (csm_sum_linear unit [tt])
              (csm_sum_add unit [tt]) (csm_sum_le unit [tt]) cbt_abs_sum_le
              [tt] cbt_enum_ne cbt_temp cbt_temp_pos cbt_Delta cbt_Delta_pos
              cbt_z cbt_z_lb cbt_z_ub
              (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
              cb1_bs_abs real_lt_plus_compat_lt_le cbt_sum_eq_list
              k mu nu Hmu Hnu)).
Qed.

(* ============================================================ *)
(* 三、门定理（本件主语）：站位 N 显式入参 + 门真 ⟹ 终装语句当站闭合         *)
(*   终装语句与 cbt_unconditional_mixing_time 结论同形；差异只在 k 的来源：  *)
(*   arch 锚急切选站 → 调用方按需交付（Q 层核门后进站）。                   *)
(* ============================================================ *)

Theorem ivl_budget_at : forall (mu nu : unit -> Real)
    (Hmu : req (cbt_sumf mu) one) (Hnu : req (cbt_sumf nu) one)
    (budget : Real) (Hbudget : lt zero budget) (N : nat),
  lt (mult (cbt_tv mu nu)
        (inv_pos (mult ivl_delta_star budget)
                 (mult_positive ivl_delta_star budget ivl_ds_pos Hbudget)))
     (cmk_scale (Datatypes.S N) one) ->
  sigT (fun k : nat =>
    lt (cbt_tv (cbt_titer k mu) (cbt_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget N Hgate.
  exists (Datatypes.S N).
  exact (le_lt_trans (cbt_tv (cbt_titer (Datatypes.S N) mu)
                             (cbt_titer (Datatypes.S N) nu))
           (mult (cmk_r_pow ivl_omd (Datatypes.S N)) (cbt_tv mu nu))
           budget
           (ivl_leg_iter mu nu Hmu Hnu (Datatypes.S N))
           (ivl_leg_tail mu nu Hmu Hnu budget Hbudget N Hgate)).
Defined.

(* ============================================================ *)
(* 四、显式输入组实例与运行证据                               *)
(* ============================================================ *)

(* 输入组：mu = nu = const one（单点世界唯一归一分布）；预算 = 1/2 *)
Definition ivl_mu : unit -> Real := fun _ => one.
Definition ivl_nu : unit -> Real := fun _ => one.

Lemma ivl_mass : req (cbt_sumf ivl_mu) one.
Proof. exact (ubt_sumf_of_point ivl_mu (req_refl one)). Qed.

Lemma ivl_nmass : req (cbt_sumf ivl_nu) one.
Proof. exact (ubt_sumf_of_point ivl_nu (req_refl one)). Qed.

Definition ivl_budget : Real := cbt_inv_two.

Lemma ivl_budget_pos : lt zero ivl_budget.
Proof. exact (inv_pos_pos (plus one one) req_two_pos). Qed.

(* 门证书（本组 TV₀ ≡ 0：mu=nu 质量一 ⟹ 差 ≡ 0；常量证书道，零载体强制） *)
Lemma ivl_gate0 : lt (mult (cbt_tv ivl_mu ivl_nu)
                       (inv_pos (mult ivl_delta_star ivl_budget)
                                (mult_positive ivl_delta_star ivl_budget
                                   ivl_ds_pos ivl_budget_pos)))
                  (cmk_scale (Datatypes.S 0) one).
Proof.
  apply (lt_id_l (mult (cbt_tv ivl_mu ivl_nu)
                   (inv_pos (mult ivl_delta_star ivl_budget)
                            (mult_positive ivl_delta_star ivl_budget
                               ivl_ds_pos ivl_budget_pos)))
              zero (cmk_scale (Datatypes.S 0) one)).
  - exact (req_trans _ _ _
            (req_trans _ _ _
               (req_mult_compat (cbt_tv ivl_mu ivl_nu) zero
                  (inv_pos (mult ivl_delta_star ivl_budget)
                           (mult_positive ivl_delta_star ivl_budget
                              ivl_ds_pos ivl_budget_pos))
                  (inv_pos (mult ivl_delta_star ivl_budget)
                           (mult_positive ivl_delta_star ivl_budget
                              ivl_ds_pos ivl_budget_pos))
                  (ubt_b2_tv0_zero ivl_mu ivl_nu ivl_mass ivl_nmass) (req_refl _))
               (mult_comm zero (inv_pos (mult ivl_delta_star ivl_budget)
                            (mult_positive ivl_delta_star ivl_budget
                               ivl_ds_pos ivl_budget_pos))))
            (mult_zero (inv_pos (mult ivl_delta_star ivl_budget)
                         (mult_positive ivl_delta_star ivl_budget
                            ivl_ds_pos ivl_budget_pos)))).
  - exact (cmk_scale_S_pos real_lt_plus_compat_lt_le one 0%nat one_pos).
Qed.

(* 终装实例：门定理在本输入组 N=0 站闭合（k = 1，一步退化站）。
   接驳走 reflexivity 道（statement 级转换，检验实证；tactic 级不展开常量） *)
Lemma ivl_terminal :
  lt (cbt_tv (cbt_titer 1%nat ivl_mu) (cbt_titer 1%nat ivl_nu)) ivl_budget.
Proof.
  assert (Heq : projT1 (ivl_budget_at ivl_mu ivl_nu ivl_mass ivl_nmass
                          ivl_budget ivl_budget_pos 0%nat ivl_gate0) = 1%nat)
    by reflexivity.
  rewrite <- Heq.
  exact (projT2 (ivl_budget_at ivl_mu ivl_nu ivl_mass ivl_nmass
                   ivl_budget ivl_budget_pos 0%nat ivl_gate0)).
Qed.

(* thunk 封装：witness 显式前置、证书按引用共享（运行位只强制前者） *)
Definition ivl_run :
  sigT (fun k : nat =>
    lt (cbt_tv (cbt_titer k ivl_mu) (cbt_titer k ivl_nu)) ivl_budget) :=
  existT _ 1%nat ivl_terminal.

(* ---- 运行关：vm_compute 真跑出 k（witness 位；证书链零强制） ---- *)
Eval vm_compute in projT1 ivl_run.

(* kernel 侧交付凭据（惰性归约道，与 vm 道双证） *)
Lemma ivl_run_wit : projT1 ivl_run = 1%nat.
Proof. exact (@eq_refl nat 1%nat). Qed.

(* ---- 输入组常数记录：Δ=3（Q5；温度 T=1 为 cbt_temp=one 固定） ---- *)
Eval vm_compute in projT1 cbt_Delta 5%nat.

(* ---- 复核关：Q 层独立数值复核道 ---- *)
Definition ivl_exp3_q : Q := projT1 (rsq_exp_pos_fn (reqd_nat_to_R 3)) 5%nat.
Eval vm_compute in ivl_exp3_q.

Definition ivl_lo_q : Q := (1 / ivl_exp3_q)%Q.              (* lo = e^{-Δ/T} *)
Definition ivl_kappa_q : Q := (1 - ivl_lo_q * ivl_lo_q)%Q.  (* κ = 1 − lo²  *)
Eval vm_compute in ivl_lo_q.
Eval vm_compute in ivl_kappa_q.

Definition ivl_tv0_q : Q := 0%Q.
Definition ivl_prod_q : Q := (ivl_kappa_q * ivl_tv0_q)%Q.
Eval vm_compute in Qlt_bool ivl_prod_q (1#2)%Q.

Lemma ivl_recheck : Qlt_bool ivl_prod_q (1#2)%Q = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 对照档：泛型几何界最小站（TV₀=1 最坏档 Q 层扫描，窗定理价值可见） ---- *)
Fixpoint ivl_q_pow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | Datatypes.S m => (q * ivl_q_pow q m)%Q
  end.

Fixpoint ivl_kn_ge (cap : nat) : nat :=
  match cap with
  | O => O
  | Datatypes.S c =>
      if negb (Qlt_bool (ivl_q_pow ivl_kappa_q c) (1#2)%Q) then c else ivl_kn_ge c
  end.

Definition ivl_kneed : nat := Datatypes.S (ivl_kn_ge 300).
Eval vm_compute in ivl_kneed.

(* ============================================================ *)
(* 五、审计口（全 Closed 预期；语句账=本件零新增假设的机器判据）             *)
(* ============================================================ *)

Print Assumptions ivl_ds_pos.
Print Assumptions ivl_ds_lt_one.
Print Assumptions ivl_leg_tail.
Print Assumptions ivl_leg_iter.
Print Assumptions ivl_budget_at.
Print Assumptions ivl_terminal.
Print Assumptions ivl_run.
Print Assumptions ivl_run_wit.
Print Assumptions ivl_recheck.
