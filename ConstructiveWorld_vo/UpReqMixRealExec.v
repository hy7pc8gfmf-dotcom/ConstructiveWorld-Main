(* ============================================================ *)
(* UpReqMixRealExec.v —— Real 层选择器可执行化（见证/证明分离＋惰性化）  *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard 节流包裹，-o 临时目录输出。   *)
(* ============================================================ *)
(* 使命：把论文7 §10.2 第 11 项的「Real 层选择器可执行化」从设计变实测。    *)
(*   背景（已证结论）：源文件 mix_k_select 的提取闭包 native 运行          *)
(*   在 mix_bernoulli_upper 单一急切绑定处挂死（其 HeqR 支经               *)
(*   mix_mult_swap → real_eq_mult_compat 急切调 real_norm_bounded，        *)
(*   模链 T(d)=2·T(d-1)；大预算档复现运行超界）。              *)
(* R1 见证/证明分离（本件核心）：                                          *)
(*   ① 计算面 mrx_arch_n / mrx_k_compute —— 纯计算 Definition，           *)
(*      选择器消费的是它，不消费证明项；                                   *)
(*   ② 证明面 mrx_k_spec —— 独立引理 Qed 封闭，零语句面角色；              *)
(*   ③ 封装面 mrx_k_exec —— existT _ 计算面 证明面 组装 sigT，            *)
(*      projT1 归约与证明面无关（机检小引理 mrx_projT1_exec 固定）；       *)
(*   ④ 非负 TV0 放宽形 mrx_k_select_*（对齐源文件 mix_k_select 口径）。      *)
(* R3 惰性化（承 UpReqMixLazy 已验证惰性化形，全链复用）：                 *)
(*   证明面走 κ 形 Bernoulli（mix2_bernoulli）+ 常量环式恒等证书               *)
(*   （mix2_swap_ring / mix2_step_ring，提取后零成本）+ 数据件 lt/le 桥，  *)
(*   零 real_eq_mult_compat 幂炸面、零 boost-inv 传递支。                  *)
(* 验收（论文 §10.2 第 11 项）：TV0=1, budget=1/2, kappa=1/2 下提取程序    *)
(*   实际运行并打印 k（提取闭包运行通过；时限指标属验收记录）。    *)
(* 红线自审：语句面全 Set 层（real_lt/real_le/real_eq/sigT/nat）；零       *)
(*   经典逻辑位；零承认件；全文件零字面禁词；可提取面闭包零魔数零桩。      *)
(* 依赖：CW_ConstructiveWorld_219 + UpTVDoeblin + UpReqIterGeomRate        *)
(*   + UpReqMixingTime（mix_scale/mix_rpow_pos/mix_mult_one_l 等）         *)
(*   + UpReqMixLazy（mix2_bernoulli/mix2_swap_ring 惰性化形）。            *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixingTime.
Require Import UpReqMixLazy.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：计算面（纯计算，提取后即 OCaml 侧 nat 函数）                    *)
(* ============================================================ *)

(* Archimedean 见证 nat 面投影：real_arch 外层 sigT 第一分量。 *)
Definition mrx_arch_n (x : Real) : nat := projT1 (real_arch x).

(* k 计算器：与源文件 mix_pow_budget 同一 arch 锚站（保守上界口径）。
   N = 0 支不可达（real_arch 保 N ≥ 2），值面取 1 仅作全定义性占位，
   证明面 mrx_k_spec 中以 Hge2 排除。 *)
Definition mrx_k_compute (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget) : nat :=
  match mrx_arch_n (real_mult TV0
           (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
              (real_mult_pos_compat (real_minus_r real_one kappa) budget
                 (tv_omd_pos_of_lt kappa hk2) hb))) with
  | Datatypes.O => 1%nat
  | Datatypes.S m => Datatypes.S m
  end.

(* 非负 TV0 放宽形的 k 计算器（对齐源文件 mix_k_select 的 Or 逐支）：      *)
(*   左支（0 < TV0）走严格支计算器；右支（TV0 == 0）k := 0 一发闭合。     *)
Definition mrx_k_select_compute (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget) : nat :=
  match ha with
  | inl hlt => mrx_k_compute kappa TV0 budget hk1 hk2 hlt hb
  | inr _heq => 0%nat
  end.

(* ============================================================ *)
(* Part 1：证明面（Qed 封闭；体承 mix2_pow_budget 已验证惰性化形）          *)
(* ============================================================ *)

Lemma mrx_k_spec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa
            (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)) TV0) budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold mrx_k_compute, mrx_arch_n.
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                (real_mult_pos_compat (real_minus_r real_one kappa) budget
                   (tv_omd_pos_of_lt kappa Hk2) Hbudget)))) as [N [Hge2 HN]].
  cbn [projT1].
  destruct N as [| N'].
  - exfalso. exact (Nat.nle_succ_0 1 Hge2).
  - (* ---- 以下承 mix2_pow_budget 主链（κ 形 Bernoulli + 常量桥尾） ---- *)
    (* 证书统一面：real_inv_pos 证书 proof-relevant，全链只准消费同一
       证书应用——把 HN 内拼出的证书应用 remember 为唯一变量 Hwb。 *)
    set (w := real_minus_r real_one kappa) in *.
    set (wb := real_mult w budget) in *.
    remember (real_mult_pos_compat w budget
                (tv_omd_pos_of_lt kappa Hk2) Hbudget) as Hwb eqn:EHwb.
    set (Ms := mix_scale (Datatypes.S N') w) in *.
    set (boost := real_plus real_one Ms) in *.
    set (mR := real_const (Z.of_nat (Datatypes.S N') # 1)).
    (* ---- 预算支：TV0 < budget·boost（全 O(N') 数据/常量件） ---- *)
    assert (Hstep : real_lt (real_mult (real_mult TV0
                                   (real_inv_pos wb Hwb)) wb)
                         (real_mult mR wb))
      by exact (real_mult_lt_compat _ _ _ HN Hwb).
    assert (HeqL : real_eq (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                         TV0).
    { apply (real_eq_trans _ (real_mult wb (real_mult TV0 (real_inv_pos wb Hwb)))).
      - exact (real_mult_comm _ _).
      - exact (real_mult_div wb TV0 Hwb). }
    assert (HeqR : real_eq (real_mult mR wb) (real_mult Ms budget)).
    { apply (real_eq_trans _ (mix_scale (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_eq_const (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_mult_distrib (Datatypes.S N') w budget)). }
    assert (Hb0 : real_lt TV0 (real_mult Ms budget)).
    { exact (real_lt_eq_lt TV0 (real_mult mR wb) (real_mult Ms budget)
               (real_eq_lt_lt TV0
                  (real_mult (real_mult TV0 (real_inv_pos wb Hwb)) wb)
                  (real_mult mR wb) (real_eq_sym _ _ HeqL) Hstep)
               HeqR). }
    assert (HeqBud : real_eq (real_mult budget boost)
                         (real_plus budget (real_mult Ms budget))).
    { apply (real_eq_trans _
               (real_plus (real_mult budget real_one)
                  (real_mult budget Ms))).
      - exact (real_distrib budget real_one Ms).
      - apply (RealSetoid.real_eq_plus_compat (real_mult budget real_one)
                 (real_mult budget Ms) budget (real_mult Ms budget)
                 (real_mult_one budget) (real_mult_comm budget Ms)). }
    assert (Hbud : real_lt TV0 (real_mult budget boost)).
    { apply (real_lt_eq_lt TV0 (real_plus (real_mult Ms budget) budget)
               (real_mult budget boost)).
      - exact (real_lt_le_trans TV0 (real_mult Ms budget)
                 (real_plus (real_mult Ms budget) budget) Hb0
                 (igr_le_plus_r (real_mult Ms budget) budget Hbudget)).
      - exact (real_eq_trans (real_plus (real_mult Ms budget) budget)
                 (real_plus budget (real_mult Ms budget))
                 (real_mult budget boost)
                 (real_plus_comm (real_mult Ms budget) budget)
                 (real_eq_sym _ _ HeqBud)). }
    (* ---- 主链（κ 形 Bernoulli + 常量桥尾，零幂传递零 compat 幂炸） ---- *)
    assert (Hk0 : real_le real_zero kappa).
    { apply (RealSetoid.real_lt_le_iff_req real_zero kappa). left.
      exact Hk1. }
    assert (Hk1le : real_le kappa real_one).
    { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left.
      exact Hk2. }
    assert (Hbern : real_le
              (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
              real_one)
      by exact (mix2_bernoulli kappa (Datatypes.S N') Hk0 Hk1 Hk1le Hk2).
    assert (HPk : real_lt real_zero (tv_rpow kappa (Datatypes.S N')))
      by exact (mix_rpow_pos kappa (Datatypes.S N') Hk1).
    assert (Hstep2 : real_lt (real_mult TV0 (tv_rpow kappa (Datatypes.S N')))
                       (real_mult (real_mult budget boost)
                                  (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_lt_compat TV0 (real_mult budget boost)
                  (tv_rpow kappa (Datatypes.S N')) Hbud HPk).
    assert (E1 : real_eq (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                         (real_mult TV0 (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_mult_comm _ _).
    assert (Hlt1 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N'))))
      by exact (real_eq_lt_lt _ _ _ E1 Hstep2).
    assert (E2 : real_eq (real_mult (real_mult budget boost)
                                (tv_rpow kappa (Datatypes.S N')))
                       (real_mult budget
                          (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_eq_trans _ _ _
                  (mix2_swap_ring budget boost
                     (tv_rpow kappa (Datatypes.S N')))
                  (real_eq_sym _ _
                     (real_mult_assoc budget
                        (tv_rpow kappa (Datatypes.S N')) boost))).
    assert (Hlt2 : real_lt (real_mult (tv_rpow kappa (Datatypes.S N')) TV0)
                     (real_mult budget
                        (real_mult (tv_rpow kappa (Datatypes.S N')) boost)))
      by exact (real_lt_eq_lt _ _ _ Hlt1 E2).
    assert (Hbern' : real_le (real_mult budget
                                (real_mult (tv_rpow kappa (Datatypes.S N')) boost))
                       (real_mult budget real_one)).
    { apply (real_le_trans _
               (real_mult (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                          budget)).
      - apply (RealSetoid.real_eq_le).
        exact (real_mult_comm budget
                 (real_mult (tv_rpow kappa (Datatypes.S N')) boost)).
      - apply (real_le_trans _ (real_mult real_one budget)).
        + exact (real_le_mult_compat
                   (real_mult (tv_rpow kappa (Datatypes.S N')) boost)
                   real_one budget Hbudget Hbern).
        + apply (RealSetoid.real_eq_le).
          exact (real_mult_comm real_one budget). }
    assert (E3 : real_eq (real_mult budget real_one) budget)
      by exact (real_eq_trans _ _ _
                  (real_mult_comm budget real_one) (mix_mult_one_l budget)).
    exact (real_lt_le_trans _ _ _
             Hlt2
             (real_le_trans _
                (real_mult budget real_one)
                budget
                Hbern'
                (RealSetoid.real_eq_le _ _ E3))).
Qed.

(* 非负 TV0 放宽形的证明面（对齐源文件 mix_k_select 的 Or 逐支） *)
Lemma mrx_k_select_spec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa
            (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)) TV0) budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold mrx_k_select_compute. destruct Ha as [Hlt | Heq].
  - exact (mrx_k_spec kappa TV0 budget Hk1 Hk2 Hlt Hbudget).
  - (* TV0 == 0 支：k := 0 一发闭合（承源文件同构） *)
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                 real_one TV0 (real_eq_refl real_one) (real_eq_refl TV0)).
      * exact (real_eq_trans (real_mult real_one TV0) TV0 real_zero
                 (mix_mult_one_l TV0) (real_eq_sym _ _ Heq)).
    + exact Hbudget.
Qed.

(* ============================================================ *)
(* Part 2：封装面（sigT 组装；计算面与证明面在 existT 下并置）              *)
(* ============================================================ *)

Definition mrx_k_exec (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)
           (mrx_k_spec kappa TV0 budget hk1 hk2 ha hb).

Definition mrx_k_select_exec (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)
           (mrx_k_select_spec kappa TV0 budget hk1 hk2 ha hb).

(* 机检小引理（设计文档 §1.3 R1 接口字段要求）：projT1 归约只由第一分量        *)
(*   决定，与第二分量（Qed 封闭的证明面）无关——证明不透明不传染见证。      *)
Lemma mrx_projT1_exec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_lt real_zero TV0) (hb : real_lt real_zero budget),
  projT1 (mrx_k_exec kappa TV0 budget hk1 hk2 ha hb)
  = mrx_k_compute kappa TV0 budget hk1 hk2 ha hb.
Proof. intros.
  exact (@eq_refl nat (mrx_k_compute kappa TV0 budget hk1 hk2 ha hb)). Qed.

Lemma mrx_projT1_select_exec : forall (kappa TV0 budget : Real)
  (hk1 : real_lt real_zero kappa) (hk2 : real_lt kappa real_one)
  (ha : real_le real_zero TV0) (hb : real_lt real_zero budget),
  projT1 (mrx_k_select_exec kappa TV0 budget hk1 hk2 ha hb)
  = mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb.
Proof. intros.
  exact (@eq_refl nat (mrx_k_select_compute kappa TV0 budget hk1 hk2 ha hb)). Qed.

(* ============================================================ *)
(* 审计口（全 Closed 预期）                                              *)
(* ============================================================ *)

Print Assumptions mrx_k_compute.
Print Assumptions mrx_k_spec.
Print Assumptions mrx_k_select_spec.
Print Assumptions mrx_k_exec.
Print Assumptions mrx_k_select_exec.
Print Assumptions mrx_projT1_exec.
Print Assumptions mrx_projT1_select_exec.
