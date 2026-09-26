(* UpArchAttn.v —— 几何收敛接口前提 r_arch_pow_attn 的 Real 层依赖模块。 *) (* 使命： 本件为根文件注意力收敛区的几何击破接口前提提供 Real 层  *) (*   显式预算实例：0 < δ < 1、0 < a、0 < eps ⟹ 存在 N 使          *) (*   a·(1−δ)^N < eps；并给出 TV 序列的几何衰减链与迭代收敛的      *)
(*   sigT 显式预算定理。                                         *) (* 依赖： CW_ConstructiveWorld_219、UpBudgetReal。               *)
(* 构造性： Set 层语句（real_lt/real_le/real_eq/sigT）；零假设位； *) (*   全部 Qed 闭合；只依存根内与 UpBudgetReal 已证机器；可提取。  *)
(* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。  *) (* 主件： r_arch_pow_attn_real——接口前提在具体 Real 层的实例化，  *)
(*   形态对齐见下方背景块。                                      *) (* 件 2： tv_iter_decay_real（TV 几何衰减链）与                   *)
(*   attention_iterate_converges_real（迭代收敛 sigT 预算定理，   *) (*   组装预演形）。                                              *)
(* 对标： 与 ConvergenceCauchy 区 r_arch_pow 同构（抽象接口版几何幂预算）， *) (* 背景：根文件注意力收敛区的接口前提                            *)
(* 根文件 CW_ConstructiveWorld_219 注意力收敛区的接口前提          *) (*   Variable r_arch_pow_attn :                                  *)
(*     forall (a : R), lt zero a -> forall eps : R, lt zero eps -> *) (*       sigT (fun N : nat =>                                    *)
(*         lt (mult a (r_pow (minus one delta) N)) eps),          *) (*   是几何击破假设 attention_iterate_converges 的 N 供给口。      *)
(*   它与收敛区已升级的 r_arch_pow（ConvergenceCauchy 区）同构，却从未 *) (*   连接到已验收的 Real 层预算机器 UpBudgetReal.r_arch_pow_real    *)
(*   （0<κ<1、0<a、0<eps 时 sigT N，a·κ^N < eps）。本文件消除该断连。 *) (* 件 1（主件）r_arch_pow_attn_real：接口前提在具体 Real 层的实例化。 *)
(*   形态对齐映射（检验结论）：                                    *) (*     R（抽象，RealInterfaceEnhanced 实例参数）                   *)
(*         ⟿ Real（柯西实数 sigT (u : Qseq) (cauchy u)）          *) (*     lt zero / lt ⟿ real_lt real_zero / real_lt（Type 版）       *)
(*     mult ⟿ real_mult                                          *) (*     minus one delta ⟿ real_plus real_one (real_opp delta)      *)
(*       （Real 层无减法记号，x−y := x+(−y)，同根文件惯例）        *) (*     r_pow（根文件 Fixpoint：O ↦ one, S m ↦ mult x (pow x m)，   *)
(*       左乘形态）⟿ real_pow（UpBudgetReal Fixpoint：             *) (*       O ↦ real_one, S m ↦ real_mult x (pow x m)——同为左乘形态，  *)
(*       定义同构确认：桥为定义级实例化（根 r_pow 活在抽象 R 世界，  *) (*       跨世界 real_eq 桥不可类型化；UpBudgetReal 已设 Notation    *)
(*       r_pow := real_pow，接口名与函数在 Real 层合一）。          *) (*     Section Variable delta/delta_pos/delta_lt_one（闭合后消失）  *)
(*         ⟿ 语句显式前提。                                       *) (* 件 2（组装预演）attention_iterate_converges_real：              *)
(*   依存件 1 + 根 attention_tv_iter_contraction 结论的 Real 副本链 *) (*   tv_n ≤ (1−δ)^n·tv_0（幂反单调 Real 副本即                     *)
(*   UpBudgetReal.real_pow_anti_mono，直接复用，不重证），          *) (*   给出 sigT 预算 N 见证定理。覆盖面注记：根定理的语义对象        *)
(*   attention_step/tv_dist/boltzmann_dist_attn 生活在抽象 Section  *) (*   世界，其实例化需在 Real 层整体消解 detailed_balance/           *)
(*   minorization/sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等 *) (*   接口前提（工程量大，不属本件范围）；以 Real 序列               *)
(*   tv_seq := n ↦ TV(iterate n μ₀, p_b) 承载最小骨架，每步几何     *) (*   收缩作为副本前提 Hstep 显式列出。主件 1 不受影响。             *)
(* 件表：one_minus_delta_pos_real / one_minus_delta_lt_one_real    *) (*   （κ := 1−δ 的序前提两件）+ r_arch_pow_attn_real（主件）+       *)
(*   tv_iter_decay_real（衰减链）+ attention_iterate_converges_real *) (*   （收敛定理）。                                               *)
(* 纪律：纯构造性；Set 层语句（real_lt/real_le/real_eq/sigT）；     *) (*       全部 Qed 闭合；只依存根内/UpBudgetReal 已证机器；          *)
(*       语句零 Prop 出面，零假设位，可提取。                       *) (* 提取面：核心件为全显式项组装，提取零 Obj.magic（独立检验文件   *)
(*       验证，主文件保持零字节日志）。                           *)

From Stdlib Require Import QArith.QArith.
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
Require Import UpBudgetReal.
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
Require Import UpBudgetReal.

Local Open Scope Q_scope.

(* ============ 1. 1−δ 的 Real 层序引理（κ := 1−δ 良定前提） ============ *)

(* 根文件 one_minus_kappa_pos 的 Real 层副本：δ < 1 ⟹ 0 < 1−δ *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd.
  exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* 根注意力区前提的对称支 Real 副本：0 < δ ⟹ 1−δ < 1
   （逐点差零 + real_lt_eq_lt：1−(1−δ) == δ 逐点 ring） *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    rewrite (real_plus_proj real_one
               (real_opp (real_plus real_one (real_opp delta))) n).
    rewrite (real_opp_proj (real_plus real_one (real_opp delta)) n).
    rewrite (real_plus_proj real_one (real_opp delta) n).
    rewrite (real_opp_proj delta n).
    cbn [projT1].
    ring.
Qed.

(* ============ 2. 件 1 主件：接口前提的 Real 层实例化 ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd2)           (one_minus_delta_lt_one_real delta Hd1)           a Ha eps Heps).
Qed.

(* ============ 3. 件 2 组装预演：TV 几何衰减链（Real 副本） ============ *)

(* 根文件 attention_tv_iter_contraction 结论的 Real 副本链：
   每步 tv_{n+1} ≤ (1−δ)·tv_n ⟹ tv_n ≤ (1−δ)^n·tv₀。
   （幂反单调的 Real 副本即 UpBudgetReal.real_pow_anti_mono，
     件 2 主定理直接复用，不重证。） *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* κ^0 ≡ one：1·tv₀ == tv₀ *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} ≤ κ·tv_n ≤ κ·(κ^n·tv₀) == κ^{n+1}·tv₀ *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. 件 2 主定理：迭代收敛的 sigT 显式预算见证 ============ *)

(* 根文件 attention_iterate_converges 的 Real 层副本组装：
   预算 N 由件 1（r_arch_pow_attn_real）构造；尾界 n ≥ N 由
   tv 衰减链（本文件件 2 前置）+ 幂反单调（real_pow_anti_mono）
   + 件 1 的 a·κ^N < eps 消解。
   覆盖面注记：tv_seq 即根语义对象 n ↦ TV(iterate attention_step n μ₀,
   boltzmann_dist_attn) 的 Real 承载；每步收缩 Hstep 对应根
   attention_tv_contraction 的结论形态。根抽象 Section 的完整
   Real 层实例化需整体消解 detailed_balance/minorization/
   sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等接口前提，
   工程量大，不属本件范围（主件 1 不受影响）。 *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n Hn).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. 提取检验（G3：零 Obj.magic） ============ *)
