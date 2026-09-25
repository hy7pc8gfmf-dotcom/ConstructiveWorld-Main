(* ==========================================================================)
   PA_ToyR_SupplyAssembly.v — ln2 无理性证明的供给装配件
   使命: 实例化 Ln2Bridge L1 的 ln2i_pade_supply（五层存在型）并经 L4 ln2b_irrational_from_supply 闭合 sa_ln2_irrational；A_n 整数面、clo_n 正性肢、θ<1 上界肢三肢构造与两段式条件形 sa_supply_assemble。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqIrrationalCriterion、UpReqLn2Irrational、BeukersLists、BeukersIdentity、Ln2Escape、Ln2Bridge；Stdlib QArith、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Lra、Qfield、Extraction。
   对标: ln2 无理性的 Padé 逼近证明（有理逼近论经典结果）。
   构造性: 语句面全 Set（sigT/And/QltT/QleT′/QeqT/real_le/real_lt）；Q 层支撑引理仅服务推理；可提取；文末 Separate Extraction 与 Print Assumptions 复核。
   编译配方: coqc 9.1 直调（无 -Q），cpu_guard 包裹，-o 输出临时目录，树内 .vo 不重写。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §1 A_n 整数面（肢②）+ 归一桥换算                                     *)
(* ============================================================ *)

(* A_n := 2^{n+1}·q̃_n 的整数面（nat 承载 Z 化） *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* A_n 的 Q 承载 == 2^{n+1}·q̃_n（bi_q_pow_2 + bk_Qmul_nat 换算） *)
Lemma sa_A_q : forall n : nat,
  ((sa_A n) # 1)%Q
  == ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. rewrite bi_q_pow_2. symmetry. apply bk_Qmul_nat.
Qed.

(* 肢②真证：0 < |A_n|（q̃_n ≥ 3^n ≥ 1 ⟹ A_n ≥ 2） *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (bk_Qn_ge_3pow_nat n) as H3.
    pose proof (bi_pow3_pos n) as Hp.
    pose proof (ln2b_pow_ge1 2 n ltac:(lia)) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* sa_norm_bridge：sa_A n # 1 == 2^{2n+1}·Q_n(1/2)（由 bi_norm_factor
   全等换算；真归一因子 2^{n+1}·q̃_n 的闭式落点） *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. exact (bi_norm_factor n). Qed.

(* ============================================================ *)
(* §2 clo_n 正性肢（肢③）+ 载体整性/上界支撑面                          *)
(* ============================================================ *)

(* 载体：clo_n := lne_B n = ∫₀¹ tⁿ(1−t)ⁿ dt 的闭式 (n!)²/(2n+1)! *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* 肢③真证：0 < clo_n（由 lne_B_posT） *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. apply lne_B_posT. Qed.

(* sa_clo_int：载体整性面 clo_n·(2n+1)! == (n!)² ∈ Z（存在型见证——
   B_n 整数面的组合原料；分子侧 Z 化即走此面） *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* sa_clo_le_p4：载体上界面 clo_n ≤ 4^{−n}（I_n ≤ 2^{n+1}·clo_n ≤
   2^{1−n} 的 Q 端原料；积分端半边 1/(1−t/2)^{n+1} ≤ 2^{n+1} 待本体到货） *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* ============================================================ *)
(* §3 θ 档（肢①）+ 半幂换算                                            *)
(* ============================================================ *)

Definition sa_theta : Q := (1 # 2)%Q.

(* 肢①真证：θ = 1/2 < 1 *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* sa_theta_posT：θ 正性（ln2b_decay 的前置面） *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* 1 的幂 *)
Lemma sa_qpow_one_q : forall n : nat, q_pow (1 # 1)%Q n == (1 # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

(* 半幂逆：q_pow (1/2) n · q_pow 2 n == 1（ln2b_qpow_inv 换算） *)
Lemma sa_half_pow : forall n : nat,
  q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n == (1 # 1)%Q.
Proof.
  intro n. rewrite (ln2b_qpow_inv 1%Z 2%positive n).
  apply sa_qpow_one_q.
Qed.

(* 半幂逆换算：2^{−n} == (1/2)^n *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  Qinv (q_pow (2 # 1)%Q n) == q_pow (1 # 2)%Q n.
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E. pose proof (bi_q_pow_pos2 n) as Hp.
    apply (Qlt_not_eq 0%Q (q_pow (2 # 1)%Q n) Hp). exact (Qeq_sym _ _ E). }
  assert (Hm := sa_half_pow n).
  assert (H1 : (Qinv (q_pow (2 # 1)%Q n) * q_pow (2 # 1)%Q n)%Q
               == (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n)%Q).
  { rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite Hm. reflexivity. }
  apply (lne_mult_canc _ _ (q_pow (2 # 1)%Q n)); [exact H1 | exact Hnz].
Qed.

(* sa_Qinv_le：Q 逆单调 0 < a ≤ b ⟹ 1/b ≤ 1/a（Q 层支撑引理，Z 分段 nia） *)
Lemma sa_Qinv_le : forall a b : Q, Qlt 0%Q a -> Qle a b -> Qle (Qinv b) (Qinv a).
Proof.
  intros [an ad] [bn bd] Ha Hab.
  unfold Qlt, Qle in Ha, Hab. cbn [Qnum Qden] in Ha, Hab.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* sa_theta_leg_scaffold（纯 Q 换算，真证）：1/(2^{n+1}·q̃_n) ≤
   (1/2)^n = θ^n——误差端 2^{−2n}/q̃_n ≤ θ^n 的收尾档（q̃_n ≥ 3^n ≥ 1） *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'.
  setoid_rewrite <- (sa_theta_pow_inv2 n).
  apply sa_Qinv_le.
  - apply bi_q_pow_pos2.
  - assert (Hq1 : (1 <= bk_Qn_qtilde n)%nat).
    { pose proof (bk_Qn_ge_3pow_nat n) as H3.
      pose proof (bi_pow3_pos n) as Hp. lia. }
    setoid_rewrite (bi_q_pow_2 (Datatypes.S n)).
    setoid_rewrite (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n)).
    setoid_rewrite (bi_q_pow_2 n).
    apply bk_Qle_nat. rewrite Nat.pow_succ_r'. nia.
Qed.

(* sa_clo_in_theta_window（真证）：clo_n < θ^n（n ≥ 1）——载体严格落入
   θ 档判定窗（lne_B_lt_p2 的 2^{−n} 窗经 sa_theta_pow_inv2 换算） *)
Theorem sa_clo_in_theta_window : forall n : nat, (1 <= n)%nat ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (QltT_to_Qlt _ _ (lne_B_lt_p2 n Hn)).
  - reflexivity.
  - unfold sa_theta.
    rewrite ln2i_p2_Z. rewrite <- (bi_q_pow_2 n).
    apply sa_theta_pow_inv2.
Qed.

(* ============================================================ *)
(* §4 三肢独立封装件（①②③已装面）                                      *)
(* ============================================================ *)

(* sa_supply_head：supply 五肢之①②③的独立封装 *)
Definition sa_supply_head : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun clo : nat -> Q =>
      sigT (fun th : Q =>
        And (QltT th (1 # 1))
          (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
               (forall n : nat, QltT 0 (clo n)))))).

Theorem sa_supply_three_legs : sa_supply_head.
Proof.
  exists sa_A. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + apply sa_clo_posT.
Qed.

(* ============================================================ *)
(* §5 条件接口（④⑤肢）+ 两段式装配闭合                                  *)
(* ============================================================ *)

(* sa_supply_rem：条件接口 B_n 整数面 + ④下界/⑤上界两实数肢——恒等式
   本体（I_n = 2^{n+1}·q̃_n·X − r_n，三子件见头注）到货后的实例化消解槽。
   语义精确：本接口非空性即 θ 档 Padé 逼近列的存在性，本件不妄断。 *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* sa_supply_assemble：两段式装配——三肢已装面 + 条件接口 ⟹ supply 全型 *)
Theorem sa_supply_assemble : forall Hm : sa_supply_rem, ln2i_pade_supply.
Proof.
  intros [B [Hlow Hup]].
  exists sa_A. exists B. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + split.
      * apply sa_clo_posT.
      * split.
        -- exact Hlow.
        -- exact Hup.
Qed.

(* sa_ln2_irrational：ln2 无理数两段式闭合——由 Ln2Bridge L4 源模块
   ln2b_irrational_from_supply（真走 lic_irrational_criterion，零旁路）。
   语句面 = L4 结论面的展开形（全 Set：sigT/And/QltT/real_lt）。 *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q.
  exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* ============================================================ *)
(* §6 数值锚组（vm_compute 精确判定：A_1 = 2²·q̃_1 = 12，                 *)
(*    A_2 = 2³·q̃_2 = 104，clo_1 = 1/6，θ² 半幂锚）                      *)
(* ============================================================ *)

Theorem sa_A1_anchor : QeqT ((sa_A 1) # 1)%Q (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_A2_anchor : QeqT ((sa_A 2) # 1)%Q (104 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_clo1_anchor : QeqT (sa_clo 1) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_theta2_anchor : QeqT (q_pow sa_theta 2) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 提取复核与假设审计                                                 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.

Print Assumptions sa_ln2_irrational.
Print Assumptions sa_clo_le_p4.
Print Assumptions sa_clo_int.
Print Assumptions sa_clo_posT.
Print Assumptions sa_norm_bridge.
