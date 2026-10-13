(* 五字段指针｜模块：piu1890_carrier_recast.v。
   数学使命：π 分离核门控载具（leibsep_q_kernel_gate_carrier）内链的
   显式重建——三面：①K 的组合量上界接合肢：BF/BFd 的逐项绝对值
   有限和界 κ₁/κ₀ 经单调 Q-算术传入 K ≤ Kcap，供 Kcap 阀形接口
   直插；②门控内链重建件：与注册载具同前提面的前提位承载形，门真支
   见证显式取 piu1872_wit eps0 = 2·(eps0·(1/8)) 且链内下界
   QleT' (1/den) c 入语句面，门假支以岸线双着陆矛盾消解；配套
   见证两形（eps1 形与 eps2 形）的链内下界 QleT' 面；③终式闭式件：
   F 在 q 端点的交错和终式逐项显式化（符号判定基座）。
   依赖清单：Stdlib QArith/QArith.Qabs/QArith.Qminmax/Lia/ZArith/
   Arith.Arith；S02_CauchyComplete/S03_QExp/LW0PiIrrational/
   LW0LeibSeparation（gate_open 系/kernel_guarded/shore 两肢/
   false_branch_contra）；leibsep_band_domain/leibsep_band_ck_assembly
   （链量对应件与 margin 肢）；piu1886_kbounds（κ₁/κ₀ nsel 合流面）；
   piu1880_valve_qchain（Kcap 接口）。
   对标行：leibsep_q_kernel_gate_carrier（同前提面）与
   piu1872_band_ck_assembly §7（margin 前提位面）的链内下界深化。
   构造性注记：零公理/零承认式/零经典逻辑；主语句以
   QleT'/QltT/sigT（Set 面）承载，定义 Defined 透明；门假支收尾
   沿注册载具 Id false true 矛盾消解形；等值面与有限和引擎沿库件
   惯例，作用域限主语句取用。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <vo>/Local ""
   -Q <vo> "" -Q <W1872> "" -Q <sbx1886> "" -Q <sbx1880> ""（cwd
   本件沙箱；cpu_guard v3 包裹；SW2 全字面双 export COQLIB/
   ROCQLIB；魔数 436f712100015ff4 一致性核验）。命名：piu1890_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import LW0PiIrrational.
Require Import LW0MLicBridge.
Require Import Local.LW0LeibSeparation.
Require Import leibsep_band_domain.
Require Import leibsep_band_ck_assembly.
Require Import piu1886_kbounds.
Require Import piu1880_valve_qchain.

(* ========== §A K ≤ Kcap 界量接合肢（κ₁/κ₀ → Kcap 阀形接口） ========== *)

Definition piu1890_c1 : Q := ((11 # 3)%Q * piu1872_S973 + (1 # 4))%Q.
Definition piu1890_c2 : Q := (piu1872_S973 + (1 # 4))%Q.

Lemma piu1890_c1_pos : Qlt 0 piu1890_c1.
Proof. unfold piu1890_c1, piu1872_S973. vm_compute. reflexivity. Qed.

Lemma piu1890_c2_pos : Qlt 0 piu1890_c2.
Proof. unfold piu1890_c2, piu1872_S973. vm_compute. reflexivity. Qed.

Theorem piu1890_K_le_Kcap : forall BF BFd k1 k0 : Q,
  Qle BF k1 -> Qle BFd k0 ->
  Qle (piu1872_K BF BFd) (piu1872_K k1 k0).
Proof.
  intros BF BFd k1 k0 HB HBd. unfold piu1872_K.
  assert (Hc1 : Qle 0 piu1890_c1) by (apply Qlt_le_weak; exact piu1890_c1_pos).
  assert (Hc2 : Qle 0 piu1890_c2) by (apply Qlt_le_weak; exact piu1890_c2_pos).
  assert (Hm1 : Qle (BF * piu1890_c1) (k1 * piu1890_c1))
    by (apply Qmult_le_compat_r; [ exact HB | exact Hc1 ]).
  assert (Hm2 : Qle (BFd * piu1890_c2) (k0 * piu1890_c2))
    by (apply Qmult_le_compat_r; [ exact HBd | exact Hc2 ]).
  apply (Qplus_le_compat (BF * piu1890_c1 + BFd * piu1890_c2)%Q
           (k1 * piu1890_c1 + k0 * piu1890_c2)%Q (1 # 8)%Q (1 # 8)%Q).
  - apply (Qplus_le_compat (BF * piu1890_c1) (k1 * piu1890_c1)
             (BFd * piu1890_c2) (k0 * piu1890_c2)).
    + exact Hm1.
    + exact Hm2.
  - apply Qle_refl.
Qed.

Definition piu1890_nsel (b : positive) : nat :=
  (lw0_n_select (10 * lw0_pi_d0_of (Zpos b # 1)%Q) 0 + 1)%nat.

Theorem piu1890_K_le_Kcap_nsel : forall (a : Z) (b : positive),
  Qle (piu1872_K
        (Qabs (qpoly_eval (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q
                                 (piu1890_nsel b)) (piu1890_nsel b))
                          ((a # b)%Q)))
        (Qabs (qpoly_eval (qpoly_deriv
                 (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q
                            (piu1890_nsel b)) (piu1890_nsel b)))
                ((a # b)%Q))))
       (piu1872_K (piu1886_k1 a b (piu1890_nsel b))
                  (piu1886_k0 a b (piu1890_nsel b))).
Proof.
  intros a b. unfold piu1890_nsel.
  apply piu1890_K_le_Kcap; apply QleT'_to_Qle.
  - apply piu1886_bf_le_k1_nsel.
  - apply piu1886_bfd_le_k0_nsel.
Qed.

Theorem piu1890_valve_up_of_kcap_nsel :
  forall (a : Z) (b : positive) (h : nat) (K : Q),
    Qle K (piu1872_K (piu1886_k1 a b (piu1890_nsel b))
                     (piu1886_k0 a b (piu1890_nsel b))) ->
    Qle ((8 # 1)%Q * piu1872_K (piu1886_k1 a b (piu1890_nsel b))
                               (piu1886_k0 a b (piu1890_nsel b)))
         (piu1872_valve_den h (piu1890_nsel b)) ->
    piu1872_valve_up K h (piu1890_nsel b).
Proof.
  intros a b h K HK Hcap.
  apply (piu1880_valve_up_from_Kcap K
           (piu1872_K (piu1886_k1 a b (piu1890_nsel b))
                      (piu1886_k0 a b (piu1890_nsel b))) h (piu1890_nsel b));
    assumption.
Qed.

(* ========== §B 门控内链重建（见证两形·链内下界） ========== *)

Section CarrierRecast1890.

Variable q eps0 s t den : Q.
Variable N0 Nv M0 : nat.

(* kernel 内链字面形的节内帮助定义（δ 可逆至注册载具字面） *)
Definition b0q : Q := (Zpos (Qden q) # 1)%Q.
Definition n0q : nat := (lw0_n_select (10 * lw0_pi_d0_of b0q) 0 + 1)%nat.

(* 注册载具前提面（leibsep_q_kernel_gate_carrier 七槽） *)
Hypothesis Heps0 : QltT 0 eps0.
Hypothesis HN0gap : forall n : nat, NatLe N0 n ->
  QltT eps0 (projT1 (real_const (10 / 3)) n - projT1 real_pi_geom n)%Q.
Hypothesis HNv : forall n : nat, (Nv <= n)%nat ->
  QltT (lw0m_e n) (eps0 * (1 # 4))%Q.
Hypothesis Hs : forall m : nat, (M0 <= m)%nat ->
  QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s.
Hypothesis Ht : forall m : nat, (M0 <= m)%nat ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t.
Hypothesis HP1 : QleT'
  (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0q n0q) n0q) q) * t
   + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0q n0q) n0q)) q) * s
   + eps0 * (1 # 8))%Q
  (1 # 2)%Q.
Hypothesis HP2 : QltT
  (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0q n0q) n0q) q) * t
   + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0q n0q) n0q)) q) * s
   + eps0 * (1 # 8))%Q
  (q_fact n0q * (lw0_Wb b0q q n0q 0%nat - lw0_Wb b0q q n0q 1%nat))%Q.

(* margin 前提位（链内下界承载位） *)
Hypothesis Hdenpos : Qlt 0 den.
Hypothesis Hmarg : Qle ((4 # 1)%Q / den) eps0.

Lemma piu1890_recast_wit_lower :
  Qle (1 / den)%Q (piu1872_wit eps0).
Proof.
  apply (piu1872_wit_lower eps0 den); [ exact Hdenpos | exact Hmarg ].
Qed.

(* 门控内链重建件：门真支见证显式取 piu1872_wit eps0（2·(eps0·(1/8))），
   链内下界 QleT' (1/den) c 入语句面；门假支沿注册载具矛盾消解形。 *)
Theorem piu1890_carrier_recast :
  sigT (fun c : Q => And (QltT 0 c)
    (And (QleT' (1 / den)%Q c)
      (sigT (fun N : nat => forall m : nat, NatLe N m ->
        QltT c (Qabs ((lw0m_xL m - q)%Q)))))).
Proof.
  assert (HN1 : (1 <= Nat.max Nv 1)%nat) by lia.
  assert (Hj01 : (1 <= 1)%nat) by lia.
  assert (Hc8lt : Qlt 0 (eps0 * (1 # 8)))
    by (apply (Qmult_lt_0_compat eps0 (1 # 8));
        [ apply QltT_to_Qlt; exact Heps0 | vm_compute; reflexivity ]).
  assert (Hc8ltT : QltT 0 (eps0 * (1 # 8))%Q) by (apply Qlt_to_QltT; exact Hc8lt).
  destruct (leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q) eqn:Egate.
  - (* 门真支：见证显式形 *)
    assert (Hguard : QltT (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL (Nat.max Nv 1) - q)%Q)))
      by (apply leibsep_gate_open_true; exact Egate).
    destruct (leibsep_q_kernel_guarded q (Nat.max Nv 1) (eps0 * (1 # 8))%Q HN1 Hguard)
      as [M HM].
    exists (piu1872_wit eps0). split.
    + unfold piu1872_wit. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 (eps0 * (1 # 8)));
        [ vm_compute; reflexivity | exact Hc8lt ].
    + split.
      * apply Qle_to_QleT'. exact piu1890_recast_wit_lower.
      * exists M. exact HM.
  - (* 门假支：岸线双着陆矛盾消解（注册载具 Id false true 收尾形） *)
    assert (Hq103 : QleT' q (10 / 3)%Q)
      by exact (leibsep_shore_q_le_ten_thirds q eps0 N0 Nv Heps0 HN0gap HNv Egate).
    assert (Hq : QltT 0 q)
      by exact (leibsep_shore_q_pos q eps0 N0 Nv Heps0 HN0gap HNv Egate).
    assert (Hcontra : Id false true).
    { exact (leibsep_false_branch_contra q 0 1 s t M0 (eps0 * (1 # 8))%Q
               Hq Hq103 Hc8ltT Hj01 Hs Ht HP1 HP2). }
    discriminate Hcontra || inversion Hcontra.
Qed.

End CarrierRecast1890.

(* 见证两形链内下界（eps1 形与 eps2 形·QleT' Set 面·valve_den 坐标） *)

Theorem piu1890_witness_form_eps1 :
  forall (h nsel : nat) (eg el K : Q),
    (2 <= nsel)%nat -> Qlt 0 K ->
    Qle ((8 # 1)%Q * K) (piu1872_valve_den h nsel) ->
    Qle ((4 # 1)%Q / piu1872_valve_den h nsel) eg ->
    Qle ((4 # 1)%Q / piu1872_valve_den h nsel) el ->
    QleT' (1 / piu1872_valve_den h nsel)%Q
          (piu1872_wit (piu1872_eps1 eg el K)).
Proof.
  intros h nsel eg el K Hns2 HK Hup Hceg Hcel.
  apply Qle_to_QleT'.
  apply (piu1872_wit_lower (piu1872_eps1 eg el K) (piu1872_valve_den h nsel)).
  - unfold piu1872_valve_den. apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - apply (piu1872_eps1_leg eg el K (piu1872_valve_den h nsel));
      [ exact Hceg | exact Hcel | exact HK | exact Hup
      | apply (piu1872_den_ge24 h nsel); exact Hns2 ].
Qed.

Theorem piu1890_witness_form_eps2 :
  forall (h nsel : nat) (eg el K WING : Q),
    (2 <= nsel)%nat -> Qlt 0 K ->
    Qle ((8 # 1)%Q * K) (piu1872_valve_den h nsel) ->
    piu1866_valve_R1 WING K h nsel ->
    Qle ((4 # 1)%Q / piu1872_valve_den h nsel) eg ->
    Qle ((4 # 1)%Q / piu1872_valve_den h nsel) el ->
    QleT' (1 / piu1872_valve_den h nsel)%Q
          (piu1872_wit (piu1872_eps2 (piu1872_eps1 eg el K) WING K)).
Proof.
  intros h nsel eg el K WING Hns2 HK Hup HR1 Hceg Hcel.
  apply Qle_to_QleT'.
  apply (piu1872_wit_lower (piu1872_eps2 (piu1872_eps1 eg el K) WING K)
           (piu1872_valve_den h nsel)).
  - unfold piu1872_valve_den. apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - unfold piu1872_eps2.
    apply (Q.min_glb (piu1872_eps1 eg el K) (WING / (2 * K)%Q)
             ((4 # 1)%Q / piu1872_valve_den h nsel)).
    + apply (piu1872_eps1_leg eg el K (piu1872_valve_den h nsel));
        [ exact Hceg | exact Hcel | exact HK | exact Hup
        | apply (piu1872_den_ge24 h nsel); exact Hns2 ].
    + apply (piu1872_valve_R1_leg WING K h nsel HK HR1).
Qed.

(* ========== §C 终式闭式件（符号判定基座） ========== *)

Lemma piu1890_qsum_congr : forall (f g : nat -> Q) (m : nat),
  (forall i : nat, (i <= m)%nat -> f i == g i) ->
  lw0_qsum f m == lw0_qsum g m.
Proof.
  intros f g m H. induction m as [|m IH].
  - cbn [lw0_qsum]. apply (H 0%nat). lia.
  - cbn [lw0_qsum]. assert (Hsm : (Datatypes.S m <= Datatypes.S m)%nat) by lia.
    rewrite (H (Datatypes.S m) Hsm).
    rewrite IH; [ reflexivity | ].
    intros i Hi. apply (H i). lia.
Qed.

Theorem piu1890_terminal_form : forall (a : Z) (b : positive) (n : nat),
  qpoly_eval (lw0_F (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n) ((a # b)%Q)
  == lw0_qsum (fun j : nat =>
         lw0_alt j *
         (if Nat.leb n (2 * j)%nat
          then lw0_z_lo a (Zpos b) n (2 * j)%nat
          else (0 # 1)%Q)) n.
Proof.
  intros a b n.
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n ((a # b)%Q)).
  apply piu1890_qsum_congr. intros i Hi.
  destruct (Nat.leb n (2 * i)%nat) eqn:E.
  - apply Nat.leb_le in E.
    rewrite (piu1886_niven_deriv_even_q a b n i E). reflexivity.
  - apply Nat.leb_gt in E.
    rewrite (piu1886_niven_deriv_even_q_zero a b n i E). reflexivity.
Qed.

(* ========== 编译出口核对 ========== *)

Check piu1890_c1_pos.
Check piu1890_c2_pos.
Check piu1890_K_le_Kcap.
Check piu1890_K_le_Kcap_nsel.
Check piu1890_valve_up_of_kcap_nsel.
Check piu1890_carrier_recast.
Check piu1890_witness_form_eps1.
Check piu1890_witness_form_eps2.
Check piu1890_qsum_congr.
Check piu1890_terminal_form.

Print Assumptions piu1890_K_le_Kcap.
Print Assumptions piu1890_K_le_Kcap_nsel.
Print Assumptions piu1890_valve_up_of_kcap_nsel.
Print Assumptions piu1890_carrier_recast.
Print Assumptions piu1890_witness_form_eps1.
Print Assumptions piu1890_witness_form_eps2.
Print Assumptions piu1890_qsum_congr.
Print Assumptions piu1890_terminal_form.
