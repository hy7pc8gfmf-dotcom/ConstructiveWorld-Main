(* ============================================================ *)
(* UpAblP1T1_AlignCert.v                                         *)
(*                                                               *)
(* 使命：本件形式化 S05_AlignmentGRPO 对齐假设簇六束的供给实例——      *)
(*   beta 正性、参考分布逐点正性、分布归一性，以及 eta 参数的         *)
(*   数据位、正性与不超过一。                                      *)
(*                                                               *)
(*   各束与假设位对应（母本 S05_AlignmentGRPO）：                     *)
(*   beta_pos（S05 假设形 lt zero beta）：对任意正有理 q，                 *)
(*     beta := real_const q 给出 Real 载体上的正性实例                *)
(*     （p1t1_beta_pos_supply）；                                  *)
(*   positive_dist（S05 假设形 forall s, lt zero (pi_ref s)）：于单点       *)
(*     SumOver 实例世界（UpAblT13c_G13 的 uab_ssUnit 与 uab_soUnit）    *)
(*     取常值一核，由接口字段 one_pos 直接推得                         *)
(*     （p1t1_pi_ref_pos_supply）；                                  *)
(*   normalized（S05 假设形 Id (sum_over_S pi_ref) one）：同一实例世界      *)
(*     上和退化为核元素取值，故常值一核的求和即 one                     *)
(*     （p1t1_pi_ref_norm_supply）；                                *)
(*   eta 数据位、eta_pos、eta_le_one（S05 三条对应假设）：取           *)
(*     (0,1) 内有理见证族 p1t1_eta_family q := real_const q，            *)
(*     正性与 beta_pos 束共享证明，不超过一由 real_lt 的逐点展开          *)
(*     与 Qmult_lt_compat_r 推得（p1t1_eta_pos_supply、                  *)
(*     p1t1_eta_le_one_supply、p1t1_eta_supply）；                       *)
(*   端点补全：eta := one 的正性与自反的不超过一                         *)
(*     （p1t1_eta_one_pos、p1t1_eta_one_le_one）。                       *)
(*                                                               *)
(* 依赖：CW_ConstructiveWorld_219、UpAblT13c_G13（单点 SumOver 实例    *)
(*   世界）、stdlib QArith。                                        *)
(*                                                               *)
(* 对标：mathlib mul_lt_mul_of_pos_right（正数乘法保序；本件以          *)
(*   stdlib QArith 的 Qmult_lt_compat_r 表达）。                      *)
(*                                                               *)
(* 构造性：纯构造性、零承认、全 Qed；语句面全 Set 层（Id/sigT/And/Or    *)
(*   别名形，裸命题不进入语句与前提位置）；标识符前缀 p1t1_。             *)
(*                                                               *)
(* 编译：Rocq 9.1 直调 coqc，cpu_guard 限核包裹。验证编译一律         *)
(*   -o 临时目录，树内 .vo 不重写。                                  *)
(*                                                               *)
(*                                                               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblT13c_G13.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Extraction.

(* ################ beta_pos 的供给：正有理常数的构造 ######################## *)
(* 假设位形：S05:45 lt zero beta（beta 为数据位）。供给定理给出 Real 载体实例：    *)
(* 任取正有理 q，beta := real_const q 满足该正性位形。                           *)
Theorem p1t1_beta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof.
  intros q Hq.
  assert (Hq' : Qlt (0#1)%Q q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists (q * (1#2)%Q).
  split.
  - apply Qlt_to_QltT.
    assert (H2 : Qlt (0 * (1#2)%Q) (q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q q (1#2)%Q H02 Hq'). }
    setoid_rewrite Qmult_0_l in H2. exact H2.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hc. setoid_rewrite Hz.
    assert (Hr1 : (q - 0)%Q == (1#1)%Q * q) by ring. setoid_rewrite Hr1.
    assert (Hr2 : q * (1#2)%Q == (1#2)%Q * q) by ring. setoid_rewrite Hr2.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q q Hq' Hhalf).
Qed.

(* ################ normalized 的供给：单点实例世界上的常值一核 ################ *)
(* 假设位形：S05:48 Id (sum_over_S pi_ref) one（S05:785 pi_old_norm 同形）。      *)
(* 单点 SumOver 实例世界：和退化为核元素取值，故常值一核的求和即 one。            *)
Theorem p1t1_pi_ref_norm_supply : forall RI0 : RealInterfaceEnhanced,
  Id (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
        (fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0)) (@one RI0).
Proof. intros RI0. exact id_refl. Qed.

(* ################ positive_dist 的供给：常值一核逐点正 ###################### *)
(* 假设位形：S05:47 forall s, lt zero (pi_ref s)；由接口字段 one_pos 直接推得。   *)
Theorem p1t1_pi_ref_pos_supply : forall (RI0 : RealInterfaceEnhanced)
    (s : @S RI0 (@uab_ssUnit (@RI_base RI0))),
  @lt RI0 (@zero RI0)
    ((fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0) s).
Proof. intros RI0 s. apply (@one_pos RI0). Qed.

(* ################ eta 数据位、eta_pos、eta_le_one 共享：eta 见证族（(0,1) 内有理族） ## *)
Definition p1t1_eta_family (q : Q) : Real := real_const q.

(* ################ eta_pos 的供给：见证族正性（证明与 beta_pos 共享） ########## *)
Theorem p1t1_eta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (p1t1_eta_family q).
Proof. intros q Hq. exact (p1t1_beta_pos_supply q Hq). Qed.

(* ################ eta_le_one 的供给：见证族不超过一 ######################## *)
Theorem p1t1_eta_le_one_supply : forall q : Q, QltT q (1#1)%Q ->
  real_le (p1t1_eta_family q) real_one.
Proof.
  intros q Hq.
  assert (Hq' : Qlt q (1#1)%Q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  assert (H0m : Qlt 0%Q (1 - q)%Q)
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (H0 : Qlt 0 ((1#1)%Q + (- q)))
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (Hlt : real_lt (real_const q) real_one).
  { unfold real_lt.
    exists ((1 - q) * (1#2)%Q)%Q.
    split.
    - apply Qlt_to_QltT.
      assert (H2a : Qlt (0 * (1#2)%Q) ((1 - q)%Q * (1#2)%Q)).
      { exact (Qmult_lt_compat_r 0%Q (1 - q)%Q (1#2)%Q H02 H0m). }
      setoid_rewrite Qmult_0_l in H2a. exact H2a.
    - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
      assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
      assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc. setoid_rewrite Ho.
      assert (HrB : (1 - q)%Q == (1#1)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrB at 2.
      assert (HrA : (1 - q)%Q * (1#2)%Q
                    == (1#2)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrA.
      exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q ((1#1)%Q + (- q)) H0 Hhalf). }
  unfold real_le.
  exact (@inl (real_lt (real_const q) real_one)
              (real_eq (real_const q) real_one) Hlt).
Qed.

(* ################ eta 数据位的供给：sigT 封装（见证与性质合取封装） ########## *)
(* 假设位形：S05:2530 eta : 数据位。对 (0,1) 内任取 q 给出带证的 eta 见证。       *)
Theorem p1t1_eta_supply : forall q : Q, QltT (0#1)%Q q -> QltT q (1#1)%Q ->
  sigT (fun e : Real => And (real_lt real_zero e) (real_le e real_one)).
Proof.
  intros q Hq0 Hq1.
  exact (existT (fun e : Real => And (real_lt real_zero e) (real_le e real_one))
                (p1t1_eta_family q)
                ((p1t1_eta_pos_supply q Hq0), (p1t1_eta_le_one_supply q Hq1))).
Qed.

(* #### 端点补全：eta := one（区间 (0,1] 的右端点） ########################## *)
Theorem p1t1_eta_one_pos : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Qed.

Theorem p1t1_eta_one_le_one : real_le real_one real_one.
Proof. exact (real_le_refl real_one). Qed.

(* ---- 提取核验：p1t1_eta_pick 的计算内容提取 ----------------------------- *)
Definition p1t1_eta_pick (n : nat) : Q := (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp1t1_g3out".
Extraction "p1t1_G3_AlignCert.ml" p1t1_eta_pick.

(* ---- 假设闭包核验：以下各定理的假设闭包应为空（Closed） ---- *)
Print Assumptions p1t1_beta_pos_supply.
Print Assumptions p1t1_pi_ref_norm_supply.
Print Assumptions p1t1_pi_ref_pos_supply.
Print Assumptions p1t1_eta_pos_supply.
Print Assumptions p1t1_eta_le_one_supply.
Print Assumptions p1t1_eta_supply.
Print Assumptions p1t1_eta_one_pos.
Print Assumptions p1t1_eta_one_le_one.
