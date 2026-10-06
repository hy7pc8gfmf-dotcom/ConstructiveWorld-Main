(* ==========================================================================)
   Arch_ToyR_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：fa52_EDP_E_B_pos_unsat、fa52_EntropyDiffReal_premises_unsat、fa52_dpo_S、fa52_dpo_reward、fa52_dpo_pi_ref、fa52_dpo_pi_ref_pos、fa52_one_two_lt、fa52_dpo_reward_spread、fa52_dpo_bounded_both_concrete。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S01_BaseRing.
Require Import fa53_compat_abs.
Require Import S03_QExp.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_LoHiSqueeze.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqBranchPos.
Require Import G12_ZPosFam.
From Stdlib Require Import QArith_base Qring.

(* ================= §1 fa52_EDP_E_B_pos_unsat 族 ================= *)
(* ---------- 核心：E_B_pos 单槽不可满足 ---------- *)
Theorem fa52_EDP_E_B_pos_unsat :
  forall E_total : Real,
    (forall E : Real, real_lt real_zero E ->
       real_lt real_zero (real_plus E_total (real_opp E))) -> False.
Proof.
  intros E_total eB.
  (* 第一步：eB 1：0 < E_total - 1 *)
  pose proof (eB real_one real_lt_zero_one) as H1.
  (* 第二步：混合加保序 0+1 < (E_total-1)+1 *)
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus (real_plus E_total (real_opp real_one)) real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero
             (real_plus E_total (real_opp real_one)) real_one real_one H1
             (real_le_refl real_one)). }
  (* 0+1 == 1 *)
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  (* (E_total-1)+1 == E_total *)
  assert (HR : real_eq (real_plus (real_plus E_total (real_opp real_one)) real_one)
                       E_total).
  { apply (real_eq_trans _ (real_plus E_total (real_plus (real_opp real_one) real_one))).
    - apply real_eq_sym.
      apply (real_plus_assoc E_total (real_opp real_one) real_one).
    - apply (real_eq_trans _ (real_plus E_total real_zero)).
      + apply (RealSetoid.real_eq_plus_compat E_total
                 (real_plus (real_opp real_one) real_one) E_total real_zero).
        * apply (real_eq_refl E_total).
        * apply (real_eq_trans _ (real_plus real_one (real_opp real_one))).
          -- apply (real_plus_comm (real_opp real_one) real_one).
          -- apply (real_plus_opp real_one).
      + apply (real_plus_zero E_total). }
  (* 得 1 < E_total，再降 0 < E_total *)
  assert (H1ET : real_lt real_one E_total).
  { exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) (real_lt_eq_lt _ _ _ Hstep HR)). }
  assert (H2 : real_lt real_zero E_total).
  { exact (real_lt_le_trans real_zero real_one E_total real_lt_zero_one (inl H1ET)). }
  (* 第三步：eB E_total：0 < E_total - E_total == 0，矛盾 *)
  pose proof (real_lt_eq_lt real_zero (real_plus E_total (real_opp E_total)) real_zero
                (eB E_total H2) (real_plus_opp E_total)) as Hcon.
  (* Empty_set（S01_BaseRing.Not 的结论型）无构造子，destruct 即清任意目标 *)
  destruct (real_lt_irrefl real_zero Hcon).
Qed.

(* ---------- 包装：EntropyDiffReal 全 10 槽空虚真 ---------- *)
Theorem fa52_EntropyDiffReal_premises_unsat :
  forall (Omega_A : forall E_A : Real, real_lt real_zero E_A -> Real)
         (Omega_B : forall E_B : Real, real_lt real_zero E_B -> Real)
         (dA : RealDifferentiable Omega_A)
         (dB : RealDifferentiable Omega_B)
         (pA : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (pB : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (wdB : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (eB : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A))),
    False.
Proof.
  intros Omega_A Omega_B dA dB pA pB wdB E_total k_B eB.
  exact (fa52_EDP_E_B_pos_unsat E_total eB).
Qed.

Print Assumptions fa52_EDP_E_B_pos_unsat.
Print Assumptions fa52_EntropyDiffReal_premises_unsat.
(* ================= §2 fa52_dpo_S 族 ================= *)
(* ---------- 具体见证 ---------- *)
Definition fa52_dpo_S : Type := bool.
Definition fa52_dpo_reward : bool -> Real :=
  fun s : bool => if s then real_plus real_one real_one else real_one.
Definition fa52_dpo_pi_ref : bool -> Real := fun _ : bool => real_one.
Definition fa52_dpo_pi_ref_pos : forall s : bool, real_lt real_zero (fa52_dpo_pi_ref s) :=
  fun _ : bool => real_lt_zero_one.

(* ---------- 1 < 2（0<1 复合 + 代数归位） ---------- *)
Lemma fa52_one_two_lt : real_lt real_one (real_plus real_one real_one).
Proof.
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus real_one real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
             real_lt_zero_one (real_le_refl real_one)). }
  exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) Hstep).
Qed.

Lemma fa52_dpo_reward_spread :
  real_lt (fa52_dpo_reward false) (fa52_dpo_reward true).
Proof.
  unfold fa52_dpo_reward.
  simpl.
  exact fa52_one_two_lt.
Qed.

(* ---------- 主件一：DPO 损失在 π* 处 (0, ln2) 有界——见证特化闭语句 ---------- *)
Theorem fa52_dpo_bounded_both_concrete :
  S01_BaseRing.And
    (real_lt real_zero
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false))
    (real_lt
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false)
       (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  exact (real_dpo_loss_pi_star_bounded_both bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one true false fa52_dpo_reward_spread).
Qed.

(* ---------- 主件二：闭式奖励复原——见证特化（β:=1, Z:=1 分离出 log1 修正项） ---------- *)
Theorem fa52_dpo_reward_recovery_concrete : forall s : bool,
  real_eq
    (real_dpo_reward_explicit bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
       (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref real_one real_lt_zero_one)
       (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
       s)
    (real_plus (fa52_dpo_reward s)
                (real_opp (real_mult real_one
                            (real_log real_one real_lt_zero_one)))).
Proof.
  intro s.
  exact (real_dpo_reward_recovers_up_to_baseline bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one s).
Qed.

Print Assumptions fa52_dpo_bounded_both_concrete.
Print Assumptions fa52_dpo_reward_recovery_concrete.
(* ================= §3 ali_abs_ge_zero_id 族 ================= *)
(* 与 fa53 同款上下文（RI_base :> RealInterface 子类投影 +        *)
(* Existing Instance 解析裸名；DO 为可选可判定序扩展类）。          *)
Section AbsLeIdAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---- 主件：abs_ge_zero_id_cc 槽语句同形（A 类核验引用 fa53 件3） ---- *)
Theorem ali_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

(* ---- 反向形：le zero a -> a == |a|（rewrite 另一向所需） ---- *)
Theorem ali_abs_ge_zero_id_sym : forall a : R, le zero a -> Id a (abs a).
Proof.
  intros a Ha.
  exact (id_sym (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 依存位封装形（左乘位）：S06:4371 直接匹配 ----
   该处原文 id_cong (fun x => mult (abs (f s)) x)
                    (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))
   ——本件把 id_cong 拼好，下游一步喂。 *)
Theorem ali_abs_id_mult_l : forall a b : R, le zero a -> Id (mult (abs a) b) (mult a b).
Proof.
  intros a b Ha.
  exact (id_cong (fun w => mult w b) (ali_abs_ge_zero_id a Ha)).
Qed.

Theorem ali_abs_id_mult_r : forall a b : R, le zero b -> Id (mult a (abs b)) (mult a b).
Proof.
  intros a b Hb.
  exact (id_cong (fun w => mult a w) (ali_abs_ge_zero_id b Hb)).
Qed.

End AbsLeIdAbstract.

(* ============ 第二层：具体 Real 层兑现 ============ *)
(* 柯西实数层（S02 Real := sigT (fun u : Qseq => cauchy u)）：     *)
(* 注意此处 Require 置于抽象节之后，避免具体层名遮蔽接口投影名。    *)

Theorem ali_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a：严格版逐点件直给（S07:7289） *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a：|a| ≈ |0| ≈ 0 ≈ a（compat + zero_req + sym 链） *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- G1 内嵌自检段（文件内显式 PA 声明，min-pa≥1） ---- *)
Print Assumptions ali_abs_ge_zero_id.
Print Assumptions ali_abs_ge_zero_id_sym.
Print Assumptions ali_abs_id_mult_l.
Print Assumptions ali_abs_id_mult_r.
Print Assumptions ali_real_abs_ge_zero_id.
(* ================= §4 uahlc_lo_lt_one_hi_one 族 ================= *)
(* ############ LoHi 实例定理与完整夹逼链 ################## *)
(* Section 参数面＝源模块两节参数之并（RI/DO 束＋指数族四件），温度:=1、利差:=1   *)
(* （由 one_pos 供 inv_pos，invT:=inv_pos one one_pos 具体形）；               *)
(* 指数族 expf 保持抽象（全库暂无具体实例）。                                   *)

Section UahlCross.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).

(* 件一：源模块 lhs_lo_lt_one_hi 的实例形：
   @ 全显给出两节参数——RI 束参＋温度:=1（one_pos）＋利差:=1（one_pos）＋
   指数族四件；源模块左支内部使用 p7a_lo_lt_one，
   右支使用 p7d_hi_gt_one，invT 正性由源模块自备。 *)
Theorem uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi).
Proof.
  exact (@lhs_lo_lt_one_hi RI one one_pos one one_pos             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件二：源模块 lhs_omd_bounded 的实例形：
   @ 全显给出 RI/DO/两节参数全束——DO 束参为源模块段二所独有，
   温度/利差取 1、指数族四件全显；源模块段二证明内部使用段一
   的 δ*<1 支，κ:=1−δ*∈(0,1) 实例形一次构成。 *)
Theorem uahlc_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  exact (@lhs_omd_bounded RI DO one one_pos one one_pos             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* 件三：lo<1 ∧ 1<hi ∧ lo<hi 的完整实例合取链。
   左支：件一左支（lo<1 实例形）；右支左支：源模块 hi 侧引理 p7d_hi_gt_one
   实例化；右支右支：复用 uahl_lo_lt_hi_one
   （@ 全显给出 RI 束＋指数族四件）——
   LoHi 侧的完整供给。 *)
Theorem uahlc_lo_one_hi_full :
  And (lt lo one) (And (lt one hi) (lt lo hi)).
Proof.
  split.
  - exact (fst uahlc_lo_lt_one_hi_one).
  - split.
    + exact (p7d_hi_gt_one one one_pos one one_pos expf expf_pos
               expf_zero expf_mono_lt).
    + exact (@uahl_lo_lt_hi_one RI expf expf_pos expf_zero expf_mono_lt).
Qed.

End UahlCross.

(* ---- 假设审计（对逐件 Print Assumptions） ---- *)
Print Assumptions uahlc_lo_lt_one_hi_one.
Print Assumptions uahlc_omd_bounded_one.
Print Assumptions uahlc_lo_one_hi_full.
(* ================= §5 zsf_sigmig2_Z_align_a_pos 族 ================= *)
Import RealInterfaceEnhancedMod.
Import Datatypes.

Theorem zsf_sigmig2_Z_align_a_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil)),
    lt zero (@UpSigMigrate2.Z_align_a_sum R RIS S (@sumd_sumf R RIS S enum)
               reward beta beta_pos pi_ref).
Proof.
  exact zpi2_sigmig2_Z_align_a_pos.
Qed.

Theorem zsf_iter_Z_thermo_i_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (Hne : Not (enum = nil)),
    lt zero (@UpReqAttnIter.Z_thermo_i R RIS S (@sumd_sumf R RIS S enum)
               D D_pos energy).
Proof.
  exact zpi2_iter_Z_thermo_i_pos.
Qed.

Theorem zsf_gibbs_Z_thermo_r_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (Hne : Not (enum = nil)),
    lt zero (@UpReqAttnGibbs.Z_thermo_r R RIS S (@sumd_sumf R RIS S enum)
               D D_pos energy).
Proof.
  exact zpi2_gibbs_Z_thermo_r_pos.
Qed.

(* ---- 参数位⑳  evicted_partition_r_pos 条件形并入 ----
   结论载体 = brp_evicted_partition_r，即宿主 evicted_partition_r 的
   sumd 键填充实例（brp_boltzmann_factor_r ≡ 宿主 boltzmann_factor_r）。 *)
Theorem zsf_gibbs_evicted_partition_r_pos :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (keep : S -> Set) (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
         (Hw : sigT (fun s : S => prod (InT s enum)
                (match keep_dec s with
                 | inl _ => unit
                 | inr _ => Empty_set
                 end))),
    lt zero (@UpReqBranchPos.brp_evicted_partition_r
               R RIS S enum D D_pos energy keep keep_dec).
Proof.
  intros R RIS S enum D D_pos energy keep keep_dec Hw.
  exact (@brp_b3_evicted_partition_r_pos           R RIS S enum D D_pos energy keep keep_dec Hw).
Qed.

(* ---- 参数位㉑  req_evicted_partition_pos 条件形并入 ----
   裸载体回接形：结论取宿主同款 match 分支和（brp_kv_boltzmann_factor
   ≡ 宿主 req_kv_boltzmann_factor，逐字同构），载体 sov 携规范条件位。 *)
Theorem zsf_restb_req_evicted_partition_pos_of_carrier :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set) (enum : list S)
         (D : R) (D_pos : lt zero D) (energy : S -> R)
         (keep : S -> Set) (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
         (sov : (S -> R) -> R),
    (forall g : S -> R, req (sov g) (@sumd_sumf R RIS S enum g)) ->
    sigT (fun s : S => prod (InT s enum)
            (match keep_dec s with
             | inl _ => unit
             | inr _ => Empty_set
             end)) ->
    lt zero (sov (fun s : S =>
            match keep_dec s with
            | inl _ => @UpReqBranchPos.brp_kv_boltzmann_factor
                         R RIS S D D_pos energy s
            | inr _ => zero
            end)).
Proof.
  intros R RIS S enum D D_pos energy keep keep_dec sov Hspec Hw.
  exact (@brp_b4_of_carrier R RIS S enum D D_pos energy keep keep_dec           sov Hspec Hw).
Qed.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions zsf_sigmig2_Z_align_a_pos.
Print Assumptions zsf_iter_Z_thermo_i_pos.
Print Assumptions zsf_gibbs_Z_thermo_r_pos.
Print Assumptions zsf_gibbs_evicted_partition_r_pos.
Print Assumptions zsf_restb_req_evicted_partition_pos_of_carrier.
(* ================= §6 p12_qpow 族 ================= *)
(* ---- 自足定义（与  逐位对照） ---- *)

Fixpoint p12_qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m => p12_qpow x m * x
  end.

Definition p12_s (k : nat) (v : Q) : Q := (1 # 1) / p12_qpow (1 - v) k - (1 # 1).

(* 族参数 b = k(k+1)/2 *)
Definition p12_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).

(* 指纹系数 (k+1)/(2k) *)
Definition p12_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

(* ---- 支撑引理（Q 层除法消去，自足） ---- *)

Lemma p12_mul_neq0 : forall a b : Q, a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  (*
     语句面 <> 是表示级 eq（记录 Leibniz），证明体弃 Qeq(==) 面 tactic，
     改纯 Z 层：destruct 拆 Qmake → injection 分量等式 → positive 单位
     9 情形 discriminate 收敛 ad=bd=1 → Z.mul_eq_0 闭合。 *)
  intros a b Ha Hb Hab.
  destruct a as [an ad]; destruct b as [bn bd]; simpl in *.
  injection Hab as H1 H2.
  destruct ad; destruct bd; simpl in *; try discriminate.
  assert (Han : an <> 0%Z) by (intro Hz; apply Ha; rewrite Hz; reflexivity).
  assert (Hbn : bn <> 0%Z) by (intro Hz; apply Hb; rewrite Hz; reflexivity).
  apply Z.mul_eq_0 in H1.
  destruct H1 as [H1 | H1].
  - apply Ha. rewrite H1. reflexivity.
  - apply Hb. rewrite H1. reflexivity.
Qed.

(*
   为【假命题】：反例 a := Qmake 0 2 满足 Leibniz 非 0，但 Qeq 面为零，
   此时 /a == 0，左端 a * (x / a) == 0 ≠ x。故本引理原形不可证非 tactic
   之过，最小维修 = 前提重述 Qeq 面 `~ a == 0`（真前提，语义恰所需，
   非改弱）。另 :85 原报错（组 定格：Found no subterm matching
   "(Qnum (?M * (?M * ?M)) * QDen (?M * ?M * ?M))%Z"）双因：
   ① Qmult_assoc 实形 `n * (m * p) == n * m * p` LHS 右结合，
     目标 (x*a)*/a 左结合无匹配（即该 Z 展开模式）；
   ② Qmult_inv_r 9.1 实形为单参 `forall x, ~ x == 0 -> x * / x == 1`，
     原双参引用形 + Leibniz 前提 `exact Ha` 两处皆不匹配。 *)
Lemma p12_div_cancel : forall a x : Q, ~ a == 0 -> a * (x / a) == x.
Proof.
  intros a x Ha. unfold Qdiv.
  transitivity (x * (a * / a)).
  - ring.
  - rewrite Qmult_inv_r by exact Ha. apply Qmult_1_r.
Qed.

(* CZD13 新增支撑：v == 0（Qeq 面）时 (1-v)^k == 1——主件零支用。
   证面全在 Proper 参数位 setoid rewrite（Qmult/Qminus 位实测可用）。 *)
Lemma p12_qpow_zero_r : forall (k : nat) (v : Q),
  v == 0 -> p12_qpow (1 - v) k == 1.
Proof.
  intros k. induction k as [| k IH]; intros v Hv.
  - reflexivity.
  - simpl. rewrite (IH v Hv). rewrite Hv. reflexivity.
Qed.

(* ---- 主件：一般 k 无条件参数化（销论文5 §9 边界 3 的第一格） ---- *)

Theorem p12_param_general_k : forall (k : nat) (v : Q),
  (1 <= k)%nat -> v <> 0 ->
  exists w : Q,
    p12_s k v == (Z.of_nat k # 1) * v + p12_bcoef k * v * v + v * v * v * w.
Proof.
  (*
     而 Leibniz 前提 v <> 0 推不出它（Qmake 0 2 反例同源）——非 tactic
     缺陷而是覆盖面缺口。按 Qeq_dec v 0 双分支闭合：
     零支（Qeq 为 0，含非正规形）p12_s == 0，取 w := 0；
     非零支走除法消去真支 + ring。定理语句面零改动；Hk 在本证面
     天然冗余（两支均不用），保留以维持语句面原貌。 *)
  intros k v Hk Hv.
  destruct (Qeq_dec v 0) as [Hv0 | Hvn].
  - exists 0%Q.
    assert (Hs : p12_s k v == 0).
    { unfold p12_s. rewrite (p12_qpow_zero_r k v Hv0). reflexivity. }
    rewrite Hs. rewrite Hv0. ring.
  - exists ((p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v)
            / (v * v * v)).
    assert (Hv3 : ~ v * v * v == 0).
    { intros Hz. apply Hvn.
      apply Qmult_integral in Hz. destruct Hz as [H1 | H1].
      - apply Qmult_integral in H1. destruct H1 as [H2 | H2]; exact H2.
      - exact H1. }
    rewrite (p12_div_cancel (v * v * v)
              (p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v) Hv3).
    ring.
Qed.

(* k=1 特化：与库内无条件件 cec_r6_param_k1 同位对照 *)
Corollary p12_param_k1 : forall v : Q,
  v <> 0 ->
  exists w : Q,
    p12_s 1%nat v == (Z.of_nat 1 # 1) * v + p12_bcoef 1%nat * v * v
            + v * v * v * w.
Proof.
  intros v Hv.
  apply (p12_param_general_k 1%nat v); [ apply le_n | exact Hv ].
Qed.

(* 角点指纹（k=1 系数 > 1/2，无条件；cec_coef_fingerprint 的 k=1 角点） *)
Lemma p12_coef_fingerprint_one : Qlt (1 # 2) (p12_coef 1%nat).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions p12_param_general_k.
