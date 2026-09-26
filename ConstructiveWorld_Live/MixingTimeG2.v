(* ============================================================ *)
(* MixingTimeG2.v —— 席位 CZF13（批次 E-STAGING-CZF13）             *)
(*   T61b C5：UpReqMixingTime G2/G3 复活件（mtg_ 前缀防撞）         *)
(*                                                                *)
(* 墙体定性（T61b 勘察定谳，本件开工三查实证）：                      *)
(*   G2 原挂账的 TV₀ 符号分叉需「real_le real_zero TV0」的居住者；    *)
(*   real_le = Or(real_lt, real_eq)（Set 层 Or 编码），该 Or-Set      *)
(*   无基座可构造居住者=可判定墙实体。本件追加实证：墙体对具体        *)
(*   TV 面（tv_doeblin = (1/2)·Σ|μ−ν|）同样成立——0 ≤ |x| 的 Or 分叉  *)
(*   需逐点判定 x==0 ∨ x≠0，构造性不可消；改 B 形路线受制于 n 元      *)
(*   ≤_B 求和提升未入库（E380 冻结表第③前沿），按诚实边界登记。       *)
(*   故恢复路线定谳=接口显式携带 TV₀ 符号证书前提（与 κ∈(0,1) 证书    *)
(*   打包），绕开 Or 分解——对照 mix_k_select（UpReqMixingTime:620，  *)
(*   Defined 可提取）的 sigT 步数见证形重建真证件。                   *)
(*                                                                *)
(* 本件承载（全 mtg_ 前缀）：                                        *)
(*   A  mtg_kappa_cert —— δ 证书 → κ := tv_omd δ ∈ (0,1) 打包        *)
(*       （prod 证书形；消费 tv_omd_pos_of_lt + mix_omd_lt_one，     *)
(*        后者内部即 UpReqIterGeomRate igr_lt_plus_r 率收口）。       *)
(*   B  mtg_mixing_time_explicit_k —— C5 主件（证书前提形）：          *)
(*       给定 κ∈(0,1) 证书包（And := prod）与 0≤TV₀ 证书，产出        *)
(*       sigT k 使 κ^k·TV₀ < budget；Defined 可提取。                *)
(*   B2 mtg_mixing_time_rate_explicit —— 率形（κ := tv_omd δ，        *)
(*       几何率收口）：δ 双证书 ⟹ tv_omd δ ^k·TV₀ < budget。          *)
(*   C  mtg_mixing_time_TV —— G2 旗舰（链面合龙）：TVRealWorld        *)
(*       消费面（states/K/K_row/u/u_norm/δ≤1/minorization/Labs）      *)
(*       × tv_doeblin_iter × B 件组装；TV₀ 符号证书随接口显式携带；   *)
(*       δ≤1 的 Or 两支分决：δ<1 支走选取器，δ==1 支 k:=1 一发        *)
(*       闭合（κ^1·TV₀==0< budget）——承草案「δ=1/TV₀=0 支 k:=1        *)
(*       一发闭合」设计。                                            *)
(*   D  mtg_k_calc / mtg_k_calc_correct —— G3 复活（Defined k-       *)
(*       计算器 + 正确性件，见证提取口）。                            *)
(*   E  mtg_budget_slack / mtg_k_slack —— igr 腿：0<e 预算放宽，      *)
(*       消费 UpReqIterGeomRate igr_le_plus_r（#273 已收口件）。      *)
(*                                                                *)
(* 逐件四要素核销宣言：                                              *)
(*   [A] 语句面=prod(real_lt,real_lt) 全 Set；证明面=term 直连两件     *)
(*        已收口率件；依赖面=UpTVDoeblin/UpReqMixingTime；公理面=零。  *)
(*   [B] 语句面=prod 证书前提 + sigT nat 见证 + real_lt 严格结论       *)
(*        全 Set；证明面=mix_k_select 全参直连；依赖面=UpReqMixingTime；*)
(*        公理面=零。                                                *)
(*   [C] 语句面=链面 14 参接口 + sigT nat + real_lt 全 Set；证明面=    *)
(*        tv_doeblin_iter × mix_k_select 组装 + δ==1 支环账（plus/opp  *)
(*        compat 链，零经典逻辑）；依赖面=UpTVDoeblin/UpReqMixingTime； *)
(*        公理面=零。                                                *)
(*   [D] 语句面=nat 出口 + real_lt 正确性全 Set；证明面=projT1/projT2  *)
(*        透明抽取；依赖面=本件 B 件；公理面=零。                      *)
(*   [E] 语句面=real_lt/real_plus 全 Set；证明面=igr_le_plus_r 直连；  *)
(*        依赖面=UpReqIterGeomRate；公理面=零。                       *)
(*                                                                *)
(* 诚实边界（对照 GEOM-B R2.2 先例，非虚报）：                        *)
(*   ① 具体 TV 面非负（Or 形）与 B 形 TV 面非负均不可由现库消解——      *)
(*      前者撞 Or 判定墙本体，后者缺 n 元 ≤_B 求和提升（E380 前沿）；   *)
(*      故 TV₀ 符号证书在链面接口显式携带，此即最强可证形。            *)
(*   ② δ==1 支的环账腿 real_eq (tv_omd real_one) real_zero 以          *)
(*      plus_opp 恒等式链闭合（real_one 不展开双关，见证内注释）。     *)
(*                                                                *)
(* 验证：G1 五禁词零 / side-compile（P7E 配方，/tmp/czf13_side）/     *)
(*   Extraction Obj.magic 探针。日志 Live/logs/czf13-*。              *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixingTime.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part A：κ 率证书包（几何率收口：δ 双证书 → κ := tv_omd δ ∈ (0,1)）   *)
(* ============================================================ *)

Theorem mtg_kappa_cert : forall delta : Real,
  real_lt real_zero delta -> real_lt delta real_one ->
  prod (real_lt real_zero (tv_omd delta)) (real_lt (tv_omd delta) real_one).
Proof.
  intros delta Hd0 Hd1.
  exact (pair (tv_omd_pos_of_lt delta Hd1) (mix_omd_lt_one delta Hd0)).
Qed.

(* ============================================================ *)
(* Part B：C5 主件——证书前提显式形（sigT 步数见证，Defined 可提取）     *)
(* ============================================================ *)

Theorem mtg_mixing_time_explicit_k : forall (kappa TV0 budget : Real),
  prod (real_lt real_zero kappa) (real_lt kappa real_one) ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hcert Ha Hb.
  exact (mix_k_select kappa TV0 budget (fst Hcert) (snd Hcert) Ha Hb).
Defined.

(* ---- B2：率形（κ := tv_omd δ，几何率收口实例） ---- *)

Theorem mtg_mixing_time_rate_explicit : forall (delta TV0 budget : Real),
  real_lt real_zero delta -> real_lt delta real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat =>
    real_lt (real_mult (tv_rpow (tv_omd delta) k) TV0) budget).
Proof.
  intros delta TV0 budget Hd0 Hd1 Ha Hb.
  destruct (mtg_kappa_cert delta Hd0 Hd1) as [Hk1 Hk2].
  exact (mtg_mixing_time_explicit_k (tv_omd delta) TV0 budget
           (pair Hk1 Hk2) Ha Hb).
Defined.

(* ============================================================ *)
(* Part C：G2 旗舰——链面合龙（tv_doeblin_iter × B 件，δ≤1 两支）       *)
(* ============================================================ *)

Theorem mtg_mixing_time_TV :
  forall (states : list (list Real))
         (K : list Real -> list Real -> Real)
         (K_row : forall i : list Real,
            real_eq (real_list_sum (list Real) (K i) states) real_one)
         (u : list Real -> Real)
         (u_norm : real_eq (real_list_sum (list Real) u states) real_one)
         (delta : Real)
         (Hd1 : real_le delta real_one)
         (Hmin : forall i j : list Real,
            real_le (real_mult delta (u j)) (K i j))
         (Labs : forall f : list Real -> Real,
            real_le (real_abs (real_list_sum (list Real) f states))
                    (real_list_sum (list Real)
                       (fun w : list Real => real_abs (f w)) states))
         (mu nu : list Real -> Real),
    real_eq (real_list_sum (list Real) mu states) real_one ->
    real_eq (real_list_sum (list Real) nu states) real_one ->
    real_le real_zero (tv_doeblin states mu nu) ->
    real_lt real_zero delta ->
    forall budget : Real,
      real_lt real_zero budget ->
      sigT (fun k : nat =>
        real_lt (tv_doeblin states (tv_titer states K k mu)
                                (tv_titer states K k nu)) budget).
Proof.
  intros states K K_row u u_norm delta Hd1 Hmin Labs mu nu
         Hmu Hnu TV0nn Hd0 budget Hbudget.
  assert (Hd1' : real_le delta real_one) by exact Hd1.
  unfold real_le in Hd1. destruct Hd1 as [Hdlt | Hdeq].
  - (* δ < 1 支：κ := tv_omd δ ∈ (0,1)，选取器出 k，迭代件收口 *)
    assert (Hk1 : real_lt real_zero (tv_omd delta))
      by exact (tv_omd_pos_of_lt delta Hdlt).
    assert (Hk2 : real_lt (tv_omd delta) real_one)
      by exact (mix_omd_lt_one delta Hd0).
    destruct (mix_k_select (tv_omd delta) (tv_doeblin states mu nu) budget
                Hk1 Hk2 TV0nn Hbudget) as [k Hk].
    exists k.
    apply (real_le_lt_trans
             (tv_doeblin states (tv_titer states K k mu)
                         (tv_titer states K k nu))
             (real_mult (tv_rpow (tv_omd delta) k)
                        (tv_doeblin states mu nu))
             budget).
    + exact (tv_doeblin_iter states K K_row u u_norm delta Hd1' Hmin Labs
               k mu nu Hmu Hnu).
    + exact Hk.
  - (* δ == 1 支：κ == 0，k := 1 一发闭合（κ^1·TV₀ == 0 < budget） *)
    exists 1%nat.
    assert (Hiter : real_le
              (tv_doeblin states (tv_titer states K 1%nat mu)
                          (tv_titer states K 1%nat nu))
              (real_mult (tv_rpow (tv_omd delta) 1%nat)
                         (tv_doeblin states mu nu)))
      by exact (tv_doeblin_iter states K K_row u u_norm delta Hd1' Hmin Labs
                  1%nat mu nu Hmu Hnu).
    assert (Homd : real_eq (tv_omd delta) real_zero).
    { (* tv_omd δ ≡ (one + opp δ) == (δ + opp δ) == 0
        （δ==1 证书经 real_eq_minus_compat 入账；real_one 不展开） *)
      apply (real_eq_trans (tv_omd delta)
               (real_plus delta (real_opp delta)) real_zero).
      - exact (real_eq_minus_compat real_one delta delta delta
                 (real_eq_sym _ _ Hdeq) (real_eq_refl delta)).
      - exact (real_plus_opp delta). }
    assert (Hpow1 : real_eq (tv_rpow (tv_omd delta) 1%nat) real_zero).
    { exact (real_eq_trans (tv_rpow (tv_omd delta) 1%nat)
               (tv_omd delta) real_zero
               (mix_rpow_one (tv_omd delta)) Homd). }
    assert (Hzero : real_eq
              (real_mult (tv_rpow (tv_omd delta) 1%nat)
                         (tv_doeblin states mu nu))
              real_zero).
    { exact (real_eq_trans
               (real_mult (tv_rpow (tv_omd delta) 1%nat)
                          (tv_doeblin states mu nu))
               (real_mult real_zero (tv_doeblin states mu nu))
               real_zero
               (RealSetoid.real_eq_mult_compat
                  (tv_rpow (tv_omd delta) 1%nat)
                  (tv_doeblin states mu nu)
                  real_zero (tv_doeblin states mu nu)
                  Hpow1 (real_eq_refl (tv_doeblin states mu nu)))
               (real_eq_trans (real_mult real_zero (tv_doeblin states mu nu))
                  (real_mult (tv_doeblin states mu nu) real_zero) real_zero
                  (real_mult_comm real_zero (tv_doeblin states mu nu))
                  (real_mult_zero (tv_doeblin states mu nu)))). }
    apply (real_le_lt_trans
             (tv_doeblin states (tv_titer states K 1%nat mu)
                         (tv_titer states K 1%nat nu))
             real_zero budget).
    + apply (real_le_trans
               (tv_doeblin states (tv_titer states K 1%nat mu)
                           (tv_titer states K 1%nat nu))
               (real_mult (tv_rpow (tv_omd delta) 1%nat)
                          (tv_doeblin states mu nu))
               real_zero).
      * exact Hiter.
      * apply (RealSetoid.real_eq_le). exact Hzero.
    + exact Hbudget.
Defined.

(* ============================================================ *)
(* Part D：G3 复活——Defined k-计算器与正确性件（见证提取口）           *)
(* ============================================================ *)

Definition mtg_k_calc (kappa TV0 budget : Real)
  (Hcert : prod (real_lt real_zero kappa) (real_lt kappa real_one))
  (Ha : real_le real_zero TV0)
  (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb).

Theorem mtg_k_calc_correct : forall (kappa TV0 budget : Real)
  (Hcert : prod (real_lt real_zero kappa) (real_lt kappa real_one))
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa (mtg_k_calc kappa TV0 budget Hcert Ha Hb))
                     TV0) budget.
Proof.
  intros kappa TV0 budget Hcert Ha Hb.
  exact (projT2 (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb)).
Qed.

(* ============================================================ *)
(* Part E：igr 腿——预算放宽（UpReqIterGeomRate #273 已收口件消费）      *)
(* ============================================================ *)

Lemma mtg_budget_slack : forall (a b e : Real),
  real_lt real_zero e -> real_lt a b -> real_lt a (real_plus b e).
Proof.
  intros a b e He Hab.
  exact (real_lt_le_trans a b (real_plus b e) Hab (igr_le_plus_r b e He)).
Qed.

Theorem mtg_k_slack : forall (kappa TV0 budget e : Real),
  prod (real_lt real_zero kappa) (real_lt kappa real_one) ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  real_lt real_zero e ->
  sigT (fun k : nat =>
    real_lt (real_mult (tv_rpow kappa k) TV0) (real_plus budget e)).
Proof.
  intros kappa TV0 budget e Hcert Ha Hb He.
  destruct (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb)
    as [k Hk].
  exists k. exact (mtg_budget_slack _ _ e He Hk).
Defined.

(* ============================================================ *)
(* G4 审计口（绿核件，全 Closed 预期）                                 *)
(* ============================================================ *)

Print Assumptions mtg_kappa_cert.
Print Assumptions mtg_mixing_time_explicit_k.
Print Assumptions mtg_mixing_time_rate_explicit.
Print Assumptions mtg_mixing_time_TV.
Print Assumptions mtg_k_calc_correct.
Print Assumptions mtg_k_slack.
