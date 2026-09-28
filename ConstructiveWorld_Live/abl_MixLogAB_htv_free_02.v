(* ==========================================================================)
   abl_MixLogAB_htv_free_02.v — UpReqMixLogA/B 选择器主定理 Htv 槽消解消融件
   （Htv-free 独立消融件，不并入目标模块）
   使命: 消除两件选择器主定理的 Htv 假设槽
     （Htv : sigT (fun v : Q => real_le TV0 (real_const v))，Q 上界证书）：
     ① mixa_k_select_log（UpReqMixLogA.v:L1223）Htv-free 重述——原证按
       real_le real_zero TV0 展开（Or=Set 层和型）分两支：TV0=0 支（real_eq 支）
       零消费 Htv（k:=0：tv_rpow κ 0==1、mixa_mult_one_l、real_eq_sym Haq 计算链）；
       TV0>0 支（real_lt 支）原证取用 Htv 走 mixa_pow_budget_log_cert——本件改引同
       件无 Htv 件（L1133），上界证书由 real_arch TV0 内供（v:=Nv#1，inl 装配
       real_le=Or(real_lt,real_eq) 左支），与 mixa_pow_budget_log（L1212，无 Htv）
       同一内供通路。拆分重述：两支合并陈述=原陈述减 Htv 槽。
     ② mixb_k_select_log（UpReqMixLogB.v:L1216）Htv-free 重述——证书内化：原证
       顶楼 destruct Htv 为 [v Hvc]，两支经 mixb_real_chain 实质使用 Hvc；本件以
       real_arch TV0 内造证书（exists (Qmake (Z.of_nat Nv) 1) + inl Hvarch）替补
       Htv 槽，κ0 提取桥（Hk2→κ0:=1−μ(epsK)，B 路特有前件机器）以下全链原样保真。
   弱化语义: 两重述结论面与原陈述逐字相同，前件面减 Htv 一槽（域严格扩大）；
     原陈述任意实参组合上新件同值——原 Htv 可由内部 real_arch 证书顶替；
     A 件零支「Htv 零消费」论证原样转写。语义等价性=结论同面+前件单调减弱。
   源件: ConstructiveWorld_Live/UpReqMixLogA.v:L1133,L1212-1245 与
     ConstructiveWorld_Live/UpReqMixLogB.v:L1047-1297（只读对照，零触碰零加载）。
   依赖: 两源件 Require 面并集（S01_BaseRing 至 S15_TailFEPUp、UpTVDoeblin、
     UpReqIterGeomRate、KLWallClosed、UpReqMixLogA、UpReqMixLogB）；Stdlib Extraction。
   构造性: 全件 Defined 闭合；语句面 Set 层承载（real_lt/real_le/sigT、
     Or:=A+B 为 S01:79 Set 层和型别名）；零经典逻辑零承认词面；
     Extraction 后 Obj.magic 计数应为 0。
   编译配方: 隔离池 /tmp/x2pool 依赖件真拷贝拓扑序，cpu_guard 包裹
     rocq c -Q /tmp/x2pool "" 本件（cwd 异地，发起前进程 <3）。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoid.
From Stdlib Require Import Extraction.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import KLWallClosed.
Require Import UpReqMixLogA.
Require Import UpReqMixLogB.

(* ============================================================ *)
(* Part 1：A 件——mixa_k_select_log 的 Htv-free 重述（拆分重述+证书内供）    *)
(* ============================================================ *)
Theorem abl_mixa_k_select_log_htv_free : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 ->
  real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hb. unfold real_le in Ha.
  destruct Ha as [Halt | Haq].
  - (* TV0>0 支：原证在此取用 Htv；本件改引无 Htv 件 mixa_pow_budget_log_cert，
       上界证书 real_arch TV0 内供（同 mixa_pow_budget_log 通路），Htv 槽消除 *)
    destruct (real_arch TV0) as [Nv [Hge Hv]].
    exact (mixa_pow_budget_log_cert kappa TV0 budget (Qmake (Z.of_nat Nv) 1)
             Hk1 Hk2 Halt (inl Hv) Hb).
  - (* TV0=0 支：原证 Htv 在此零消费——k := 0 计算链原样转写（保真） *)
    exists 0%nat.
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                   real_one TV0
                   (real_eq_refl real_one) (real_eq_refl TV0)).
      * apply (real_eq_trans (real_mult real_one TV0) TV0 real_zero).
        -- exact (mixa_mult_one_l TV0).
        -- exact (real_eq_sym _ _ Haq).
    + exact Hb.
Defined.

(* ============================================================ *)
(* Part 2：B 件——mixb_k_select_log 的 Htv-free 重述（证书内化，全链保真）   *)
(* ============================================================ *)
Definition abl_mixb_k_select_log_htv_free (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct Hk2 as [epsK [HepsK [NK HNK]]].
  destruct Hb as [epsB [HepsB [NB HNB]]].
  (* Htv 槽消解（证书内化）：上界证书 real_arch TV0 内供，
     顶替原证 destruct Htv as [v Hvc]；以下 κ0 提取桥全链原样保真 *)
  destruct (real_arch TV0) as [Nv [HgeN Hvarch]].
  assert (Htv : sigT (fun v : Q => real_le TV0 (real_const v))).
  { exists (Qmake (Z.of_nat Nv) 1). exact (inl Hvarch). }
  destruct Htv as [v Hvc].
  assert (Hk0 : 0 < 1 - mixb_mu epsK)
    by (apply mixb_kappa0_pos; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hk0lt : 1 - mixb_mu epsK < 1)
    by (apply mixb_kappa0_lt_one; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hb0 : 0 < epsB * (1 # 2)).
  { apply (Qmult_lt_0_compat epsB (1 # 2)).
    - exact (QltT_to_Qlt 0 epsB HepsB).
    - exact mixb_q_12_pos. }
  assert (Hk0le : real_le kappa (real_const (1 - mixb_mu epsK))).
  { apply (RealSetoid.real_lt_le_iff_req). left.
    exact (mixb_kappa0_bridge kappa epsK NK HepsK HNK). }
  assert (Hc0pos : real_lt real_zero (real_const (1 - mixb_mu epsK)))
    by exact (mixb_qpos_const_lt _ Hk0).
  assert (Hbb : real_lt (real_const (epsB * (1 # 2))) budget)
    by exact (mixb_b0_bridge budget epsB NB HepsB HNB).
  assert (Hv0 : 0 <= v) by exact (mixb_v_nonneg TV0 v Ha Hvc).
  destruct (mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) 0%nat) eqn:Hq0.
  - (* k := 0：TV0′ ≤ b0 已达标 *)
    exists 0%nat.
    exact (mixb_real_chain kappa TV0 budget (1 - mixb_mu epsK) v (epsB * (1 # 2)) 0%nat
             Hk1 Hk0le Hc0pos Ha Hvc Hbb Hq0).
  - (* 倍增+二分：real_arch 兜底窗口（裁决 1(b)），Q 引擎精确定位 *)
    pose (k0 := (1 - mixb_mu epsK)%Q).
    pose (wb := ((1 - k0) * (epsB * (1 # 2)))%Q).
    assert (Hwbpos : 0 < wb).
    { pose proof (mixb_mu_pos epsK (QltT_to_Qlt 0 epsK HepsK)) as Hmu.
      unfold wb, k0.
      apply (Qmult_lt_0_compat (1 - (1 - mixb_mu epsK)) (epsB * (1 # 2)));
        [lra | exact Hb0]. }
    assert (Hwbne : ~ (wb == 0)).
    { intro He. apply (Qlt_not_eq 0 wb Hwbpos). apply mixb_qeq_sym. exact He. }
    destruct (real_arch (real_const (v * Qinv wb))) as [nA Hpair].
    destruct Hpair as [Hnge2 Harchlt].
    assert (Hqarch : Qlt (v * Qinv wb) (Z.of_nat nA # 1))
      by exact (mixb_const_lt_to_Qlt _ _ Harchlt).
    assert (Hwin : Qle v ((Z.of_nat nA # 1) * wb)).
    { apply Qlt_le_weak.
      apply (Qle_lt_trans v ((v * Qinv wb) * wb) ((Z.of_nat nA # 1) * wb)).
      - apply qeq_le. apply mixb_qeq_sym.
        exact (mixb_qmul_inv_cancel v wb Hwbpos).
      - exact (Qmult_lt_compat_r (v * Qinv wb) (Z.of_nat nA # 1) wb Hwbpos Hqarch). }
    assert (HpassnA : mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA = true).
    { apply (mixb_window_test_true (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA
               Hk0 Hk0lt Hv0 Hb0); [lia | exact Hwin]. }
    destruct (mixb_qsel (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA) as [r c] eqn:Hsel.
    destruct (mixb_qsel_account_ex (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA r c
                Hk0 Hk0lt Hv0 Hnge2
                (ex_intro _ nA (conj (Nat.le_refl nA) HpassnA)) Hq0 Hsel)
      as [Hrpass [Hrmin Hcnt]].
    exists r.
    exact (mixb_real_chain kappa TV0 budget (1 - mixb_mu epsK) v (epsB * (1 # 2)) r
             Hk1 Hk0le Hc0pos Ha Hvc Hbb Hrpass).
Defined.
(* ============================================================ *)
(* 提取审计口（可提取 Obj.magic=0；全 Closed）                             *)
(* ============================================================ *)

Extraction "abl_MixLogAB_htv_free_02_probe.ml"
  abl_mixa_k_select_log_htv_free abl_mixb_k_select_log_htv_free.

Print Assumptions abl_mixa_k_select_log_htv_free.
Print Assumptions abl_mixb_k_select_log_htv_free.
