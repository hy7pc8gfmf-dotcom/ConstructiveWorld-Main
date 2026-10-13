(* ===================================================================== *)
(*  u5c_dm_e2_measure_qcore.v —— e² := exp(2) 的测度实例件                  *)
(*  模块名：u5c_dm_e2_measure_qcore（u5c_dm_e_measure_qcore 的 B=2 换参面）。 *)
(*  使命：e² := exp(2) = lim Σ_{k≥0} 2^k/k! 的逐 q 测度实例。勘验结论        *)
(*        （响亮申报）：阶乘分母机制对 B=2 只「半通用」——量化隙半边          *)
(*        （n!·(q − s(n)) 呈 (整数/b) 形）逐字通用，但 CaseA 闭合窗对 B=2     *)
(*        结构性死亡：首尾项 2^{n+1}/(n+1)! ≥ 1/(b·n!) 对一切 b ≥ 1、         *)
(*        n ≥ 0 恒真（由 2^{n+1} ≥ n+1），故 e 机的「隙 − 尾 ≥ c > 0」前提    *)
(*        永不可满足——本件以 dme2_gap_le_firsttail + dme2_caseA_route_dead   *)
(*        两件在机形式化此否定（换参路线的 CaseA 支不可闭合的在机证书）。     *)
(*  三向内容：                                                              *)
(*   ① CaseB 闭式支 dme2_e2_qcore / u5c_e2_caseB_measure——q 命中部分和      *)
(*      s(b+6) 时，与 e 机同族闭式常元 c := 1/(4·b·(b+7)!) 分离成立；         *)
(*   ② 条件形实层装配件 u5c_e2_conditional_measure——q 在 n0 处逃出尾窗       *)
(*      dme2_tb n0（QltT 可判定前提·诚实接口显式披露）时，闭式余量            *)
(*      c := (|q−s(n0)| − tb(n0))/2 与 e² 柯西极限分离（经                   *)
(*      dmec_escape_to_dist_any 参数化桥直链）；                             *)
(*   ③ 死窗否定件（见上）——后续方向据此转向 Hermite–Padé 型线性形式机        *)
(*      （N1 族）或 e^{1/k}（k ≥ 2）易装实例。                               *)
(*  尾控组：几何比 r̂ := 2/(n+2)（对一切 n ≥ 1 严格小于 1，免 e 机            *)
(*   1/(n+1) 的 n=1 奇点），尾和 < (2^{n+1}/(n+1)!)·((n+2)/n)；消失性经      *)
(*   (n+1)! ≥ 6·4^{n−2}（n ≥ 2）压到 tb(n) ≤ 16/2^n，显式 N := 5 +           *)
(*   16·den(eps)。                                                         *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、     *)
(*        UpReqBanachNormOpp、UpReqIrrationalCriterion、                     *)
(*        u5c_dm_e_measure_qcore（dmeq_ 微件组全量复用——e 系基座迁移面）、    *)
(*        u5c_dm_escape_to_dist_any（参数化分离桥）。                        *)
(*  对标：e 的无理性证明（Hermite 1873 型阶乘分母机制）之测度实例化。         *)
(*  构造性注记：语句面全 Set 层（sigT/And/QltT/QleT'/QeqT/Id），零 Prop      *)
(*        前提位；零承认、零经典逻辑、零全局假设；主定理见证提取实跑          *)
(*        （dme2_run_* 三检验·RunAlive 三向 true）。                         *)
(*  编译配方：rocq c -native-compiler no -q -Q . ""                          *)
(*        u5c_dm_e2_measure_qcore.v。                                       *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_dm_e_measure_qcore.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：2 的幂与阶乘下界微件（nat/Z 层）＋ Qmake 算术桥                  *)
(* ============================================================ *)

Lemma dme2_pow2_ge_succ : forall m : nat, (m + 1 <= 2 ^ m)%nat.
Proof.
  induction m as [| m IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

Lemma dme2_pow2_Zpos : forall m : nat, (0 < 2 ^ Z.of_nat m)%Z.
Proof.
  intro m. assert (Hn : (0 < 2 ^ m)%nat)
    by (pose proof (dme2_pow2_ge_succ m); lia).
  replace (2 ^ Z.of_nat m)%Z with (Z.of_nat (2 ^ m)%nat)
    by (rewrite Nat2Z.inj_pow; reflexivity).
  replace 0%Z with (Z.of_nat 0%nat) by lia.
  apply (proj1 (Nat2Z.inj_lt _ _)). exact Hn.
Qed.

Lemma dme2_pow2_add : forall a b : nat, (2 ^ (a + b) = 2 ^ a * 2 ^ b)%nat.
Proof.
  intros a b. induction a as [| a IH].
  - cbn [Nat.pow Nat.add]. nia.
  - cbn [Nat.pow Nat.add]. rewrite IH. nia.
Qed.

Lemma dme2_pow4_eq : forall m : nat, (4 ^ m = 2 ^ (2 * m))%nat.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (4 ^ Datatypes.S m)%nat with (4 * 4 ^ m)%nat
      by (cbn [Nat.pow]; lia).
    replace (2 ^ (2 * Datatypes.S m))%nat with (2 ^ (2 + 2 * m))%nat
      by (f_equal; lia).
    rewrite dme2_pow2_add.
    replace (2 ^ 2)%nat with 4%nat by reflexivity.
    rewrite IH. lia.
Qed.

Lemma dme2_factS_Z : forall m : nat,
  Z.of_nat (fact (Datatypes.S m)) = (Z.of_nat (Datatypes.S m) * Z.of_nat (fact m))%Z.
Proof.
  intro m. cbn [fact]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma dme2_fact_ge_pow4 : forall m : nat, (3 <= m)%nat -> (6 * 4 ^ (m - 3) <= fact m)%nat.
Proof.
  intros m. induction m as [| m IH]; intro Hm.
  - lia.
  - cbn [fact].
    destruct (le_lt_dec 3 m) as [H3 | Hlt].
    + replace (Datatypes.S m - 3)%nat with (Datatypes.S (m - 3))%nat by lia.
      cbn [Nat.pow].
      pose proof (IH H3) as IH'.
      nia.
    + assert (Hm2 : (m = 2)%nat) by lia. subst m.
      cbn [fact Nat.pow Nat.sub]. lia.
Qed.

Lemma dme2_qpow2_Z : forall n : nat,
  q_pow (2#1)%Q n == ((2 ^ Z.of_nat n)%Z # 1)%Q.
Proof.
  induction n as [| n IH].
  - cbn [q_pow Z.of_nat Z.pow]. reflexivity.
  - cbn [q_pow]. rewrite IH.
    replace (Z.of_nat (Datatypes.S n))%Z with (Z.succ (Z.of_nat n))%Z
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite (Z.pow_succ_r 2 (Z.of_nat n) (Nat2Z.is_nonneg n)).
    unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul].
    first [ring | nia | lia].
Qed.

Lemma dme2_qpow2_ge0 : forall n : nat, QleT' 0%Q (q_pow (2#1)%Q n).
Proof.
  induction n as [| n IH].
  - apply Qle_to_QleT'. cbn [q_pow]. unfold Qle. cbn [Qnum Qden]. lia.
  - cbn [q_pow]. apply dmeq_mul_ge0.
    + apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

Lemma dme2_term_ge0 : forall m : nat,
  Qle 0%Q ((q_pow (2#1)%Q m / q_fact m)%Q).
Proof.
  intro m. apply QleT'_to_Qle. apply dmeq_mul_ge0.
  - apply dme2_qpow2_ge0.
  - apply Qle_to_QleT'. apply Qlt_le_weak.
    exact (Qinv_lt_0_compat (q_fact m) (q_fact_pos m)).
Qed.

Lemma dme2_Qnum_make : forall z : Z, Qnum (z # 1)%Q = z.
Proof. intro z. reflexivity. Qed.

Lemma dme2_QDen_make : forall p : positive, QDen (1 # p)%Q = Z.pos p.
Proof. intro p. reflexivity. Qed.

Lemma dme2_mul_inv_self : forall x : Q, ~ (x == 0%Q) -> x * Qinv x == 1%Q.
Proof.
  intros x Hx. apply (Qeq_trans _ (x * (1%Q / x))%Q).
  - apply (sif_mult_comp_r (Qinv x) (1%Q / x) x).
    apply Qeq_sym. apply Qmult_1_l.
  - apply bno_mul_div_self. exact Hx.
Qed.

Lemma dme2_Zmake_mul : forall x y : Z,
  ((x # 1)%Q * (y # 1)%Q)%Q == ((x * y)%Z # 1)%Q.
Proof.
  intros x y. unfold Qeq, Qmult.
  cbn [Qnum Qden Qmult Pos.mul]. first [ring | nia | lia].
Qed.

(* ============================================================ *)
(* S1：量化隙（B=2 正半边：n!·(q − s₂(n)) 呈 (整数/b) 形）               *)
(* ============================================================ *)

Fixpoint dme2_Zc (n : nat) : Z :=
  match n with
  | O => 1%Z
  | Datatypes.S m =>
      (Z.of_nat (Datatypes.S m) * dme2_Zc m + 2 ^ Z.of_nat (Datatypes.S m))%Z
  end.

Lemma dme2_Zc_bridge : forall n : nat,
  ((Z.of_nat (fact n)) # 1)%Q * exp_series n 2%Q == ((dme2_Zc n) # 1)%Q.
Proof.
  induction n as [| m IH].
  - cbn [exp_series fact dme2_Zc]. cbn [q_pow]. cbn [Qmult Pos.mul].
    first [reflexivity | lia | ring].
  - cbn [exp_series fact dme2_Zc].
    assert (Hpow : q_pow (2#1)%Q (Datatypes.S m)
                   == ((2 ^ Z.of_nat (Datatypes.S m))%Z # 1)%Q)
      by apply dme2_qpow2_Z.
    assert (HNF0 : ~ (((Z.of_nat (fact (Datatypes.S m))) # 1)%Q == 0%Q)).
    { intro Hc. pose proof (dmeq_Zfact_pos (Datatypes.S m)) as HP.
      unfold Qeq in Hc. cbn [Qnum Qden Qmult Pos.mul] in Hc. lia. }
    assert (HEQNF : ((Z.of_nat (Datatypes.S m * fact m))%Z # 1)%Q
                    == ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q).
    { unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul].
      rewrite dme2_factS_Z. rewrite Nat2Z.inj_mul. reflexivity. }
    assert (HNF2 : ((Z.of_nat (Datatypes.S m * fact m))%Z # 1)%Q
                   == (((Z.of_nat (Datatypes.S m) * Z.of_nat (fact m))%Z) # 1)%Q).
    { unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul].
      rewrite Nat2Z.inj_mul. reflexivity. }
    rewrite Qmult_plus_distr_r.
    apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m) * dme2_Zc m) # 1)%Q
                        + ((2 ^ Z.of_nat (Datatypes.S m))%Z # 1)%Q)%Q).
    + apply sif_plus_comp.
      * apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m) * Z.of_nat (fact m))%Z # 1)%Q
                            * exp_series m 2%Q)%Q).
        -- apply sif_mult_comp_l. exact HNF2.
        -- rewrite <- (dme2_Zmake_mul (Z.of_nat (Datatypes.S m))
                         (Z.of_nat (fact m))).
           rewrite <- (Qmult_assoc ((Z.of_nat (Datatypes.S m)) # 1)%Q
                                   ((Z.of_nat (fact m)) # 1)%Q
                                   (exp_series m 2%Q)).
           rewrite IH. reflexivity.
      * rewrite Hpow.
        rewrite (sif_qfact_Z (Datatypes.S m)).
        apply (Qeq_trans _ (((Z.of_nat (fact (Datatypes.S m))) # 1)%Q
                            * (((2 ^ Z.of_nat (Datatypes.S m))%Z # 1)%Q
                               / ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q))%Q).
        -- apply sif_mult_comp_l. exact HEQNF.
        -- unfold Qdiv.
           rewrite Qmult_assoc.
           rewrite (Qmult_comm ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q
                               ((2 ^ Z.of_nat (Datatypes.S m))%Z # 1)%Q).
           rewrite <- (Qmult_assoc ((2 ^ Z.of_nat (Datatypes.S m))%Z # 1)%Q
                                   ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q
                                   (Qinv ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q)).
           rewrite (dme2_mul_inv_self ((Z.of_nat (fact (Datatypes.S m))) # 1)%Q HNF0).
           rewrite Qmult_1_r. reflexivity.
    + unfold Qeq, Qplus, Qmult. cbn [Qnum Qden Qplus Qmult Pos.mul]. lia.
Qed.

Definition dme2_d (q : Q) (n : nat) : Z :=
  Qnum q * Z.of_nat (fact n) - dme2_Zc n * Z.pos (Qden q).

Lemma dme2_frac_prod : forall (q : Q) (n : nat),
  (q_fact n * (q - exp_series n 2)%Q)%Q == ((dme2_d q n) # (Qden q))%Q.
Proof.
  intros q n.
  apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1)
                      * (q - exp_series n 2)%Q)%Q).
  - apply sif_mult_comp_l. apply sif_qfact_Z.
  - apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1) * q%Q
                        + (- (((Z.of_nat (fact n)) # 1)
                              * exp_series n 2%Q))%Q)%Q).
    + unfold Qminus. rewrite Qmult_plus_distr_r.
      rewrite (sif_mult_opp_r _ _). reflexivity.
    + apply (Qeq_trans _ ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q)
                           - ((dme2_Zc n) # 1))%Q)).
      * apply sif_plus_comp.
        -- apply (Qeq_trans _
                    ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q))%Q)).
           ++ apply sif_mult_comp_r. symmetry. apply sif_Qmake_eta.
           ++ unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
              first [lia | ring | nia | reflexivity].
        -- apply sif_opp_comp. exact (dme2_Zc_bridge n).
      * destruct q as [a b]. unfold dme2_d in *. unfold Qminus, Qeq.
        cbn [Qnum Qden Qplus Qopp Qmult Pos.mul] in *.
        rewrite (sif_Zpos_mul b 1).
        first [lia | ring | nia | reflexivity].
Qed.

(* 量化隙（B=2 正半边）：q ≠ s₂(n) ⟹ 1/(b·n!) ≤ |q − s₂(n)| *)
Lemma dme2_gap : forall (q : Q) (n : nat),
  ~ ((q == exp_series n 2)%Q) ->
  QleT' ((1%Q / ((Z.pos (Qden q)) # 1)%Q)
         * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q
        (Qabs ((q - exp_series n 2)%Q)).
Proof.
  intros q n Hne. apply Qle_to_QleT'.
  pose proof (dme2_frac_prod q n) as HF.
  assert (HA : Qabs ((q_fact n * (q - exp_series n 2)%Q)%Q)
               == ((Z.abs (dme2_d q n)) # (Qden q))%Q).
  { rewrite dme2_frac_prod. cbn [Qabs]. reflexivity. }
  pose proof (q_fact_pos n) as Hqp.
  assert (Hqf0 : ~ (q_fact n == 0%Q)).
  { intro Hc. exact (Qlt_not_eq 0%Q _ Hqp (Qeq_sym _ _ Hc)). }
  assert (Hd0 : dme2_d q n <> 0%Z).
  { intro Hd.
    assert (Hz : ((dme2_d q n) # (Qden q))%Q == 0%Q)
      by (rewrite Hd; unfold Qeq; cbn [Qnum Qden Qmult]; lia).
    rewrite Hz in HF.
    assert (H1 : ((1%Q / q_fact n) * (q_fact n * (q - exp_series n 2)%Q))%Q
                 == ((1%Q / q_fact n) * 0%Q)%Q)
      by (apply sif_mult_comp_r; exact HF).
    rewrite Qmult_assoc in H1.
    rewrite (Qmult_comm (1%Q / q_fact n) (q_fact n)) in H1.
    rewrite (bno_mul_div_self (q_fact n) Hqf0) in H1.
    rewrite Qmult_1_l in H1.
    rewrite (qeqT_imp_qeq _ _ (dmeq_mult_0_r (1%Q / q_fact n))) in H1.
    assert (H2 : q == ((q - exp_series n 2) + exp_series n 2)%Q)
      by (apply qeqT_imp_qeq; apply dmeq_minus_plus_cancel).
    rewrite H1 in H2. rewrite Qplus_0_l in H2.
    exact (Hne H2). }
  assert (Habs1 : (1 <= Z.abs (dme2_d q n))%Z).
  { destruct (dme2_d q n) as [| zz | zz]; cbn [Z.abs].
    - lia.
    - assert (0 < Z.pos zz)%Z by apply sif_posZ. lia.
    - assert (0 < Z.pos zz)%Z by apply sif_posZ. lia. }
  assert (HC : Qabs (q_fact n) == q_fact n).
  { apply Qabs_pos. exact (Qlt_le_weak 0%Q _ Hqp). }
  rewrite (Qabs_Qmult (q_fact n) ((q - exp_series n 2)%Q)) in HA.
  rewrite HC in HA.
  assert (H2 : ((1%Q / q_fact n) * (q_fact n * Qabs ((q - exp_series n 2)%Q)))%Q
               == ((1%Q / q_fact n) * ((Z.abs (dme2_d q n)) # (Qden q))%Q)%Q)
    by (apply sif_mult_comp_r; exact HA).
  rewrite Qmult_assoc in H2.
  rewrite (Qmult_comm (1%Q / q_fact n) (q_fact n)) in H2.
  rewrite (bno_mul_div_self (q_fact n) Hqf0) in H2.
  rewrite Qmult_1_l in H2.
  rewrite (sif_qfact_Z n) in H2.
  assert (HF0 : (0 < Z.of_nat (fact n))%Z) by apply dmeq_Zfact_pos.
  assert (Hb0 : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
  assert (H3 : ((1%Q / ((Z.of_nat (fact n)) # 1)%Q)
                * ((Z.abs (dme2_d q n)) # (Qden q))%Q)%Q
               == (((Z.abs (dme2_d q n)) # (Qden q))%Q
                   * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q).
  { symmetry. apply Qmult_comm. }
  rewrite H3 in H2.
  rewrite H2.
  destruct (Z.of_nat (fact n)) as [| Fq | Fq] eqn:HFq.
  - lia.
  - unfold Qle, Qdiv, Qinv. cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
  - exfalso. exact (dmeq_Zofnat_neqneg (fact n) Fq HFq).
Qed.

(* ============================================================ *)
(* S2：锚与尾窗定义＋Z 形正典桥                                          *)
(* ============================================================ *)

Definition dme2_anchor (n : nat) : Q :=
  (q_pow (2#1)%Q (Datatypes.S n) / q_fact (Datatypes.S n))%Q.

Definition dme2_tb (n : nat) : Q :=
  ((dme2_anchor n) * (((Z.of_nat n + 2)%Z # 1)%Q
                      * (1%Q / ((Z.of_nat n)%Z # 1)%Q)))%Q.

Definition dme2_gapc (bb : positive) (n : nat) : Q :=
  ((1%Q / ((Z.pos bb) # 1)%Q) * (1%Q / ((Z.of_nat (fact n)) # 1)%Q))%Q.

Lemma dme2_anchor_Z : forall n : nat,
  dme2_anchor n == ((2 ^ Z.of_nat (Datatypes.S n))%Z # 1)%Q
                   * (1%Q / ((Z.of_nat (fact (Datatypes.S n))) # 1)%Q).
Proof.
  intro n. unfold dme2_anchor.
  rewrite (dme2_qpow2_Z (Datatypes.S n)), (sif_qfact_Z (Datatypes.S n)).
  unfold Qeq, Qmult, Qdiv, Qinv.
  cbn [Qnum Qden Qmult Qinv Pos.mul].
  destruct (Z.of_nat (fact (Datatypes.S n))) as [| Fn | Fn] eqn:HF.
  - pose proof (dmeq_Zfact_pos (Datatypes.S n)) as HP. lia.
  - cbn [Qinv Qnum Qden Qmult Pos.mul]. first [reflexivity | ring | nia | lia].
  - exfalso. exact (dmeq_Zofnat_neqneg (fact (Datatypes.S n)) Fn HF).
Qed.

(* ============================================================ *)
(* S3：几何级数组（比 r̂ := 2/(n+2)）                                    *)
(* ============================================================ *)

Definition dme2_rp (n : nat) : Q := (2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q.

Fixpoint dme2_rpG (n j : nat) : Q :=
  match j with
  | O => 1%Q
  | Datatypes.S i => dme2_rp n * dme2_rpG n i
  end.

Fixpoint dme2_gsum (n K : nat) : Q :=
  match K with
  | O => 1%Q
  | Datatypes.S k => dme2_gsum n k + dme2_rpG n (Datatypes.S k)
  end.

Lemma dme2_rpG_succ : forall n j : nat,
  QeqT (dme2_rpG n (Datatypes.S j)) (dme2_rp n * dme2_rpG n j)%Q.
Proof. intros n j. apply qeq_imp_qeqT. cbn [dme2_rpG]. reflexivity. Qed.

Lemma dme2_rp_pos : forall n : nat, QltT 0%Q (dme2_rp n).
Proof.
  intro n. apply Qlt_to_QltT. unfold dme2_rp. unfold Qdiv.
  apply (Qmult_lt_0_compat (2#1)%Q (Qinv ((Z.of_nat n + 2)%Z # 1)%Q)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - exact (Qinv_lt_0_compat ((Z.of_nat n + 2)%Z # 1)%Q
              ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia)).
Qed.

Lemma dme2_rpG_ge0 : forall n j : nat, QleT' 0%Q (dme2_rpG n j).
Proof.
  intros n j. induction j as [| j IH].
  - apply Qle_to_QleT'. unfold Qle. cbn [dme2_rpG Qnum Qden]. lia.
  - cbn [dme2_rpG]. apply dmeq_mul_ge0.
    + apply Qle_to_QleT'. apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _ (dme2_rp_pos n)).
    + exact IH.
Qed.

Lemma dme2_rp_G : forall n : nat, (1 <= n)%nat ->
  QeqT (dme2_rp n * (((Z.of_nat n + 2)%Z # 1)%Q
                     * (1%Q / ((Z.of_nat n)%Z # 1)%Q)))%Q
       (((2#1)%Q / ((Z.of_nat n)%Z # 1)%Q))%Q.
Proof.
  intros n Hn. apply qeq_imp_qeqT. unfold dme2_rp.
  assert (HY0 : ~ (((Z.of_nat n + 2)%Z # 1)%Q == 0%Q))
    by (intro Hc; unfold Qeq in Hc; cbn [Qnum Qden Qmult] in Hc; lia).
  unfold Qdiv.
  rewrite Qmult_assoc.
  rewrite <- (Qmult_assoc (2#1)%Q (Qinv ((Z.of_nat n + 2)%Z # 1)%Q)
                          ((Z.of_nat n + 2)%Z # 1)%Q).
  rewrite (Qmult_comm (Qinv ((Z.of_nat n + 2)%Z # 1)%Q)
                      ((Z.of_nat n + 2)%Z # 1)%Q).
  rewrite (dme2_mul_inv_self ((Z.of_nat n + 2)%Z # 1)%Q HY0).
  rewrite (Qmult_1_r (2#1)%Q).
  rewrite (Qmult_1_l (Qinv ((Z.of_nat n)%Z # 1)%Q)). reflexivity.
Qed.

Lemma dme2_gsum_split : forall n k : nat,
  QeqT (dme2_gsum n k + dme2_rpG n (Datatypes.S k))%Q
       (1%Q + dme2_rp n * dme2_gsum n k)%Q.
Proof.
  intros n k. apply qeq_imp_qeqT. induction k as [| k IH].
  - cbn [dme2_gsum dme2_rpG]. reflexivity.
  - cbn [dme2_gsum]. rewrite (qeqT_imp_qeq _ _ (dme2_rpG_succ n (Datatypes.S k))).
    apply (Qeq_trans _ (((1%Q + dme2_rp n * dme2_gsum n k)%Q
                         + dme2_rp n * dme2_rpG n (Datatypes.S k))%Q)).
    + apply sif_plus_comp.
      * exact IH.
      * reflexivity.
    + rewrite Qmult_plus_distr_r.
      unfold Qplus, Qeq. cbn [Qnum Qden Qmult]. first [ring | nia | lia].
Qed.

Lemma dme2_gsum_lt : forall n K : nat, (1 <= n)%nat ->
  QltT (dme2_gsum n K)
       (((Z.of_nat n + 2)%Z # 1)%Q * (1%Q / ((Z.of_nat n)%Z # 1)%Q))%Q.
Proof.
  intros n K Hn.
  assert (Hbase : Qlt 1%Q (((Z.of_nat n + 2)%Z # 1)%Q
                           * (1%Q / ((Z.of_nat n)%Z # 1)%Q))%Q).
  { unfold Qeq, Qlt, Qmult, Qdiv, Qinv.
    destruct (Z.of_nat n) as [| Np | Np] eqn:HN.
    - pose proof (dmeq_Zofnat_eq0 n HN) as H0. subst n.
      cbn [Qnum Qden Qmult Qinv Pos.mul]. lia.
    - cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
    - exfalso. exact (dmeq_Zofnat_neqneg n Np HN). }
  assert (H3 : (1%Q + ((2#1)%Q / ((Z.of_nat n)%Z # 1)%Q))%Q
               == (((Z.of_nat n + 2)%Z # 1)%Q
                   * (1%Q / ((Z.of_nat n)%Z # 1)%Q))%Q).
  { unfold Qeq, Qplus, Qmult, Qdiv, Qinv.
    destruct (Z.of_nat n) as [| Np | Np] eqn:HN.
    - pose proof (dmeq_Zofnat_eq0 n HN) as H0. subst n.
      cbn [Qnum Qden Qmult Qinv Pos.mul]. lia.
    - cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
    - exfalso. exact (dmeq_Zofnat_neqneg n Np HN). }
  induction K as [| k IH].
  + cbn [dme2_gsum]. apply Qlt_to_QltT. exact Hbase.
  + apply Qlt_to_QltT.
    change (dme2_gsum n (Datatypes.S k))%Q
      with (dme2_gsum n k + dme2_rpG n (Datatypes.S k))%Q.
    rewrite (qeqT_imp_qeq _ _ (dme2_gsum_split n k)).
    pose proof (QltT_to_Qlt _ _ (dme2_rp_pos n)) as Hrp.
    assert (H1 : Qlt ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q * dme2_gsum n k)%Q
                     (((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)
                      * (((Z.of_nat n + 2)%Z # 1)%Q
                         * (1%Q / ((Z.of_nat n)%Z # 1)%Q)))%Q).
    { pose proof (Qmult_lt_compat_r _ _ _ Hrp (QltT_to_Qlt _ _ IH)) as HH.
      rewrite (Qmult_comm (dme2_gsum n k)
                 ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)) in HH.
      rewrite (Qmult_comm (((Z.of_nat n + 2)%Z # 1)%Q
                           * (1%Q / ((Z.of_nat n)%Z # 1)%Q))
                 ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)) in HH.
      exact HH. }
    pose proof (lic_qlt_add_l 1%Q
                  ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q * dme2_gsum n k)%Q
                  (((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)
                   * (((Z.of_nat n + 2)%Z # 1)%Q
                      * (1%Q / ((Z.of_nat n)%Z # 1)%Q)))%Q H1) as H2.
    rewrite (qeqT_imp_qeq _ _ (dme2_rp_G n Hn)) in H2.
    rewrite H3 in H2. exact H2.
Qed.

(* ============================================================ *)
(* S4：尾和组（差分解＋逐项几何压制＋消失性）                            *)
(* ============================================================ *)

Fixpoint dme2_rsum (n K : nat) : Q :=
  match K with
  | O => 0%Q
  | Datatypes.S k =>
      dme2_rsum n k + (q_pow (2#1)%Q (n + Datatypes.S k)
                       / q_fact (n + Datatypes.S k))%Q
  end.

Lemma dme2_exp_diff : forall n K : nat,
  (exp_series (n + K) 2%Q - exp_series n 2%Q)%Q == dme2_rsum n K.
Proof.
  intros n K. induction K as [| k IH].
  - rewrite Nat.add_0_r. cbn [dme2_rsum]. unfold Qminus. ring.
  - cbn [dme2_rsum].
    replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    apply (Qeq_trans _ ((exp_series (n + k) 2%Q - exp_series n 2%Q
                         + (q_pow (2#1)%Q (Datatypes.S (n + k))
                            / q_fact (Datatypes.S (n + k)))%Q)%Q)).
    + cbn [exp_series]. unfold Qminus. ring.
    + rewrite IH. reflexivity.
Qed.

Lemma dme2_rsum_ge0 : forall n K : nat, Qle 0%Q (dme2_rsum n K).
Proof.
  intros n K. induction K as [| k IH].
  - cbn [dme2_rsum]. apply Qle_refl.
  - cbn [dme2_rsum].
    apply (Qle_trans 0%Q (dme2_rsum n k)
             (dme2_rsum n k
              + (q_pow (2#1)%Q (n + Datatypes.S k)
                 / q_fact (n + Datatypes.S k))%Q)).
    + exact IH.
    + apply QleT'_to_Qle. apply dmeq_le_add_r.
      apply Qle_to_QleT'. exact (dme2_term_ge0 (n + Datatypes.S k)).
Qed.

Lemma dme2_rsum_mono : forall n K : nat,
  QleT' (dme2_rsum n K) (dme2_rsum n (Datatypes.S K)).
Proof.
  intros n K. cbn [dme2_rsum]. apply dmeq_le_add_r. apply Qle_to_QleT'.
  exact (dme2_term_ge0 (n + Datatypes.S K)).
Qed.

Lemma dme2_rsum_mono_K : forall n j K : nat, (j <= K)%nat ->
  QleT' (dme2_rsum n j) (dme2_rsum n K).
Proof.
  intros n j K H. apply Qle_to_QleT'. induction H as [| K Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (dme2_rsum n K));
      [exact IH | apply QleT'_to_Qle; apply dme2_rsum_mono].
Qed.

Lemma dme2_anchor_ge0 : forall n : nat, QleT' 0%Q (dme2_anchor n).
Proof.
  intro n. apply Qle_to_QleT'. unfold dme2_anchor.
  exact (dme2_term_ge0 (Datatypes.S n)).
Qed.

Lemma dme2_anchor_pos : forall n : nat, Qlt 0%Q (dme2_anchor n).
Proof.
  intro n. rewrite (dme2_anchor_Z n). unfold Qlt, Qmult, Qdiv, Qinv.
  cbn [Qnum Qden Qmult Qinv Pos.mul].
  pose proof (dme2_pow2_Zpos (Datatypes.S n)) as Hpz.
  destruct (Z.of_nat (fact (Datatypes.S n))) as [| Fn | Fn] eqn:HF.
  - pose proof (dmeq_Zfact_pos (Datatypes.S n)) as HP. lia.
  - cbn [Qinv Qnum Qden Qmult Pos.mul]. nia.
  - exfalso. exact (dmeq_Zofnat_neqneg (fact (Datatypes.S n)) Fn HF).
Qed.

Lemma dme2_term_succ : forall m : nat,
  QeqT ((q_pow (2#1)%Q (Datatypes.S m) / q_fact (Datatypes.S m))%Q)
       (((q_pow (2#1)%Q m / q_fact m)
         * ((2#1)%Q / ((Z.of_nat (Datatypes.S m)) # 1)%Q))%Q).
Proof.
  intro m.
  assert (HP7 : (2 ^ Z.of_nat (Datatypes.S m) = 2 * 2 ^ Z.of_nat m)%Z).
  { replace (Z.of_nat (Datatypes.S m))%Z with (Z.succ (Z.of_nat m))%Z
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite (Z.pow_succ_r 2 (Z.of_nat m) (Nat2Z.is_nonneg m)). lia. }
  assert (HFS : Z.of_nat (fact (Datatypes.S m))
                = (Z.of_nat (Datatypes.S m) * Z.of_nat (fact m))%Z)
    by apply dme2_factS_Z.
  apply qeq_imp_qeqT.
  rewrite (dme2_qpow2_Z m), (dme2_qpow2_Z (Datatypes.S m)).
  rewrite (sif_qfact_Z m), (sif_qfact_Z (Datatypes.S m)).
  unfold Qeq, Qmult, Qdiv, Qinv.
  cbn [Qnum Qden Qmult Qinv Pos.mul].
  destruct (Z.of_nat (Datatypes.S m)) as [| N7 | N7] eqn:HM7.
  - exfalso. discriminate HM7.
  - destruct (Z.of_nat (fact m)) as [| Fm | Fm] eqn:HF.
    * pose proof (dmeq_Zfact_pos m) as HP. exfalso. lia.
    * destruct (Z.of_nat (fact (Datatypes.S m))) as [| F7 | F7] eqn:H7.
      -- pose proof (dmeq_Zfact_pos (Datatypes.S m)) as HP. exfalso. lia.
      -- cbn [Qnum Qden Pos.mul].
         rewrite Pos2Z.inj_mul. rewrite HP7. rewrite HFS. nia.
      -- exfalso. exact (dmeq_Zofnat_neqneg (fact (Datatypes.S m)) F7 H7).
    * exfalso. exact (dmeq_Zofnat_neqneg (fact m) Fm HF).
  - exfalso. exact (dmeq_Zofnat_neqneg (Datatypes.S m) N7 HM7).
Qed.

Lemma dme2_term_le : forall n j : nat, (1 <= n)%nat ->
  QleT' ((q_pow (2#1)%Q (n + Datatypes.S j) / q_fact (n + Datatypes.S j))%Q)
        ((dme2_anchor n * dme2_rpG n j)%Q).
Proof.
  intros n j Hn. apply Qle_to_QleT'. induction j as [| j IH].
  - cbn [dme2_rpG]. replace (n + 1)%nat with (Datatypes.S n)%nat by lia.
    unfold dme2_anchor. rewrite Qmult_1_r. apply Qle_refl.
  - rewrite Nat.add_succ_r.
    rewrite (qeqT_imp_qeq _ _ (dme2_term_succ (n + Datatypes.S j))).
    assert (Hposd : QleT' 0%Q ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)).
    { apply dmeq_mul_ge0.
      - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
      - apply Qle_to_QleT'. apply Qlt_le_weak.
        exact (Qinv_lt_0_compat ((Z.of_nat n + 2)%Z # 1)%Q
                 ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia)). }
    assert (Hdel : QleT' ((2#1)%Q / ((Z.of_nat (Datatypes.S (n + Datatypes.S j))) # 1)%Q)
                          ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)).
    { apply dmeq_mult_le_compat_l.
      - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
      - apply dmeq_inv_le_mono.
        + apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Qmult]. lia.
        + apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult]. lia. }
    assert (Hrew : (((dme2_anchor n * dme2_rpG n j)
                     * ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q))%Q
                   == (dme2_anchor n * dme2_rpG n (Datatypes.S j))%Q)).
    { rewrite (qeqT_imp_qeq _ _ (dme2_rpG_succ n j)). unfold dme2_rp.
      rewrite <- (Qmult_assoc (dme2_anchor n) (dme2_rpG n j)
                    ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)).
      rewrite (Qmult_comm (dme2_rpG n j)
                 ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q)).
      reflexivity. }
    apply (Qle_trans _ (((q_pow (2#1)%Q (n + Datatypes.S j)
                          / q_fact (n + Datatypes.S j))
                         * ((2#1)%Q / ((Z.of_nat n + 2)%Z # 1)%Q))%Q)).
    + apply QleT'_to_Qle. apply dmeq_mult_le_compat_l.
      * unfold Qdiv. apply dmeq_mul_ge0.
        -- apply dme2_qpow2_ge0.
        -- apply Qle_to_QleT'. apply Qlt_le_weak.
           exact (Qinv_lt_0_compat (q_fact (n + Datatypes.S j))
                    (q_fact_pos (n + Datatypes.S j))).
      * exact Hdel.
    + rewrite <- Hrew. apply QleT'_to_Qle. apply dmeq_mult_le_compat_r.
      * exact Hposd.
      * exact (Qle_to_QleT' _ _ IH).
Qed.

Lemma dme2_rsum_le : forall n K : nat, (1 <= n)%nat ->
  QleT' (dme2_rsum n K) ((dme2_anchor n * dme2_gsum n K)%Q).
Proof.
  intros n K Hn. apply Qle_to_QleT'.
  assert (Haux : forall k : nat,
           Qle (dme2_rsum n (Datatypes.S k))
               ((dme2_anchor n * dme2_gsum n k)%Q)).
  { intro k. induction k as [| k IH].
    - cbn [dme2_rsum dme2_gsum]. rewrite Qplus_0_l.
      replace (n + 1)%nat with (Datatypes.S n)%nat by lia.
      unfold dme2_anchor. rewrite Qmult_1_r. apply Qle_refl.
    - assert (Hrec : dme2_rsum n (Datatypes.S (Datatypes.S k))
                     == (dme2_rsum n (Datatypes.S k)
                         + (q_pow (2#1)%Q (n + Datatypes.S (Datatypes.S k))
                            / q_fact (n + Datatypes.S (Datatypes.S k)))%Q)%Q)
        by reflexivity.
      cbn [dme2_gsum].
      apply (Qle_trans _ ((dme2_anchor n * dme2_gsum n k
                           + dme2_anchor n * dme2_rpG n (Datatypes.S k))%Q)).
      + rewrite Hrec. apply Qplus_le_compat.
        * exact IH.
        * exact (QleT'_to_Qle _ _ (dme2_term_le n (Datatypes.S k) Hn)).
      + apply qeq_le. apply Qeq_sym. cbn [dme2_gsum]. apply Qmult_plus_distr_r. }
  destruct K as [| k].
  - cbn [dme2_rsum dme2_gsum]. apply QleT'_to_Qle. apply dmeq_mul_ge0.
    + apply dme2_anchor_ge0.
    + apply Qle_to_QleT'. cbn [dme2_gsum]. unfold Qle. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ ((dme2_anchor n * dme2_gsum n k)%Q)).
    + exact (Haux k).
    + apply QleT'_to_Qle. apply dmeq_mult_le_compat_l.
      * apply dme2_anchor_ge0.
      * cbn [dme2_gsum]. apply dmeq_le_add_r. apply dme2_rpG_ge0.
Qed.

Lemma dme2_rsum_geo : forall n K : nat, (1 <= n)%nat ->
  QltT (dme2_rsum n K) (dme2_tb n).
Proof.
  intros n K Hn. apply Qlt_to_QltT. unfold dme2_tb.
  apply (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ (dme2_rsum_le n K Hn))).
  pose proof (Qmult_lt_compat_r _ _ _
           (dme2_anchor_pos n)
           (QltT_to_Qlt _ _ (dme2_gsum_lt n K Hn))) as Hlt.
  rewrite (Qmult_comm (dme2_gsum n K) (dme2_anchor n)) in Hlt.
  rewrite (Qmult_comm (((Z.of_nat n + 2)%Z # 1)%Q
                       * (1%Q / ((Z.of_nat n)%Z # 1)%Q))
                      (dme2_anchor n)) in Hlt.
  exact Hlt.
Qed.

Lemma dme2_tail_bounded : lic_tail_bounded (fun n : nat => exp_series n 2%Q) dme2_tb.
Proof.
  intros n k Hn1 Hnk. remember (k - n)%nat as K eqn:HK.
  assert (Hk : k = (n + K)%nat) by (rewrite HK; lia).
  rewrite Hk.
  assert (Habs : Qabs ((exp_series (n + K) 2%Q - exp_series n 2%Q)%Q)
                 == dme2_rsum n K).
  { rewrite dme2_exp_diff. apply Qabs_pos. exact (dme2_rsum_ge0 n K). }
  apply Qlt_to_QltT. rewrite Habs. apply QltT_to_Qlt.
  apply dme2_rsum_geo. exact Hn1.
Qed.

(* 消失性微件：tb(n) ≤ 16/2^n（n ≥ 3）＋ 2^n 的显式下压 *)
Lemma dme2_vanish : lic_vanish dme2_tb.
Proof.
  intro eps. destruct eps as [pn pd]. intro Heps.
  pose proof (sif_posZ pd) as Hpd.
  assert (Hpn : (0 < pn)%Z)
    by (pose proof (QltT_to_Qlt _ _ Heps) as Hx;
        unfold Qlt in Hx; cbn [Qnum Qden] in Hx; lia).
  exists (5 + 16 * Z.to_nat (Z.pos pd))%nat.
  intros n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (Hn3 : (3 <= n)%nat) by lia.
  pose proof (dme2_pow2_ge_succ (16 * Z.to_nat (Z.pos pd))) as Hp1.
  assert (H2 : (16 * Z.to_nat (Z.pos pd) + 1
                <= 2 ^ (16 * Z.to_nat (Z.pos pd) + 5))%nat).
  { pose proof (Nat.pow_le_mono_r 2 (16 * Z.to_nat (Z.pos pd))
                  (16 * Z.to_nat (Z.pos pd) + 5) ltac:(lia) ltac:(lia)) as HH.
    lia. }
  assert (HZ2N : (Z.pos pd <= Z.of_nat (Z.to_nat (Z.pos pd)))%Z)
    by (pose proof (Z2Nat.id (Z.pos pd) (Z.lt_le_incl 0%Z _ Hpd)); lia).
  assert (Hbig : (16 * Z.pos pd < 2 ^ Z.of_nat n)%Z).
  { assert (Hnat : (16 * Z.to_nat (Z.pos pd) < 2 ^ n)%nat).
    { pose proof (Nat.pow_le_mono_r 2 (16 * Z.to_nat (Z.pos pd) + 5) n
                    ltac:(lia) ltac:(lia)) as HM.
      lia. }
    replace (2 ^ Z.of_nat n)%Z with (Z.of_nat (2 ^ n)%nat)
      by (rewrite Nat2Z.inj_pow; reflexivity).
    assert (HZ : (Z.of_nat (16 * Z.to_nat (Z.pos pd)) < Z.of_nat (2 ^ n))%Z)
      by (apply (proj1 (Nat2Z.inj_lt _ _)); exact Hnat).
    rewrite Nat2Z.inj_mul in HZ. lia. }
  remember (2 ^ Z.of_nat n)%Z as Wp eqn:HWp in Hbig.
  destruct Wp as [| Pp | Pp].
  - exfalso. lia.
  - assert (HP7 : (2 ^ Z.of_nat (Datatypes.S n) = 2 * Z.pos Pp)%Z).
    { replace (Z.of_nat (Datatypes.S n))%Z with (Z.succ (Z.of_nat n))%Z
        by (rewrite Nat2Z.inj_succ; lia).
      rewrite (Z.pow_succ_r 2 (Z.of_nat n) (Nat2Z.is_nonneg n)), <- HWp. lia. }
    assert (HPP : (Z.pos Pp = 4 * Z.of_nat (2 ^ (n - 2)))%Z).
    { rewrite HWp.
      replace (2 ^ Z.of_nat n)%Z with (Z.of_nat (2 ^ n)%nat)
        by (rewrite Nat2Z.inj_pow; reflexivity).
      assert (Hsp : (2 ^ n = 4 * 2 ^ (n - 2))%nat).
      { replace n with ((n - 2) + 2)%nat at 1 by lia.
        rewrite dme2_pow2_add. cbn [Nat.pow]. lia. }
      rewrite Hsp. rewrite Nat2Z.inj_mul. lia. }
    assert (H4 : (6 * 4 ^ (Datatypes.S n - 3) <= fact (Datatypes.S n))%nat)
      by (apply dme2_fact_ge_pow4; lia).
    replace (Datatypes.S n - 3)%nat with (n - 2)%nat in H4 by lia.
    rewrite dme2_pow4_eq in H4.
    replace (2 * (n - 2))%nat with ((n - 2) + (n - 2))%nat in H4 by lia.
    rewrite (dme2_pow2_add (n - 2) (n - 2)) in H4.
    assert (HFK : (6 * Z.of_nat (2 ^ (n - 2)) * Z.of_nat (2 ^ (n - 2))
                   <= Z.of_nat (fact (Datatypes.S n)))%Z).
    { replace (6 * Z.of_nat (2 ^ (n - 2)) * Z.of_nat (2 ^ (n - 2)))%Z
        with (Z.of_nat (6 * 2 ^ (n - 2) * 2 ^ (n - 2)))%Z.
      - apply (proj1 (Nat2Z.inj_le _ _)). lia.
      - rewrite !Nat2Z.inj_mul. lia. }
    assert (Hs1 : (2 * Z.of_nat (2 ^ (n - 2)) * Z.of_nat (2 ^ (n - 2))
                   * (Z.of_nat n + 2)
                   <= 12 * Z.of_nat (2 ^ (n - 2)) * Z.of_nat (2 ^ (n - 2))
                      * Z.of_nat n)%Z)
      by nia.
    assert (Hs2 : (12 * Z.of_nat (2 ^ (n - 2)) * Z.of_nat (2 ^ (n - 2))
                   * Z.of_nat n
                   <= 2 * Z.of_nat (fact (Datatypes.S n)) * Z.of_nat n)%Z)
      by nia.
    assert (Hle : Qle (dme2_tb n)
                      (((16#1)%Q) * (1%Q / ((Z.pos Pp) # 1)%Q))).
    { unfold dme2_tb. rewrite (dme2_anchor_Z n).
      unfold Qle, Qmult, Qdiv, Qinv. cbn [Qnum Qden Qmult Qinv Pos.mul].
      rewrite HP7. rewrite HPP.
      assert (HU : (0 < Z.of_nat (2 ^ (n - 2)))%Z).
      { replace 0%Z with (Z.of_nat 0%nat) by lia.
        apply (proj1 (Nat2Z.inj_lt _ _)).
        pose proof (dme2_pow2_ge_succ (n - 2)). lia. }
      destruct (Z.of_nat (fact (Datatypes.S n))) as [| F7 | F7] eqn:HF7;
        try (exfalso;
             pose proof (dmeq_Zfact_pos (Datatypes.S n)) as HP1;
             lia);
        destruct (Z.of_nat n + 2)%Z as [| S2 | S2] eqn:HS2;
        try (exfalso; lia);
        destruct (Z.of_nat n) as [| Nn | Nn] eqn:HNn;
        try (exfalso; assert (HNg : (0 < Z.of_nat n)%Z) by lia; lia);
        rewrite Pos2Z.inj_mul.
      cbn [Qinv Qnum Qden Qmult Pos.mul]. nia. }
    apply Qlt_to_QltT. apply (Qle_lt_trans _ _ _ Hle).
    unfold Qlt, Qmult, Qdiv, Qinv. cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
  - exfalso. lia.
Qed.

Definition dme2_X_e2 : Real :=
  existT (fun u : Qseq => cauchy u) (fun n : nat => exp_series n 2%Q)
         (lic_seq_cauchy (fun n : nat => exp_series n 2%Q) dme2_tb
                         dme2_tail_bounded dme2_vanish).

(* ============================================================ *)
(* S5：CaseB 闭式支（q 命中 s₂(n0)·同族常元 1/(4b·(b+7)!))               *)
(* ============================================================ *)

Lemma dme2_margin_to_sep : forall c B : Q,
  QltT c ((B - c)%Q) -> QleT' 0%Q c -> QltT c B.
Proof.
  intros c B H H0.
  pose proof (QltT_to_Qlt _ _ H) as H1.
  pose proof (lic_qlt_add_l c c ((B - c)%Q) H1) as H2.
  rewrite (Qplus_comm c ((B - c)%Q)) in H2.
  rewrite (lic_qlt_minus_add_r B c) in H2.
  pose proof (QleT'_to_Qle _ _ (dmeq_le_add_r c c H0)) as H3.
  apply Qlt_to_QltT. exact (Qle_lt_trans _ _ _ H3 H2).
Qed.

Lemma dme2_const_pos : forall (a : Z) (bb : positive),
  QltT 0%Q ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
Proof.
  intros a bb.
  assert (HF : (0 < Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7)))%Z)
    by apply dmeq_Zfact_pos.
  destruct (Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) as [| Fp | Fp] eqn:HFc.
  - lia.
  - apply Qlt_to_QltT. unfold Qlt, Qdiv, Qinv.
    cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
  - exfalso. exact (dmeq_Zofnat_neqneg (fact (Z.to_nat (Z.pos bb) + 7)) Fp HFc).
Qed.

Lemma dme2_caseB2 : forall (q : Q) (n0 k : nat),
  (1 <= n0)%nat -> (Datatypes.S n0 <= k)%nat ->
  (q == exp_series n0 2%Q) ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
       ((Qabs ((q - exp_series k 2%Q)%Q)
         - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
Proof.
  intros q n0 k Hn01 HkN Heq.
  remember (k - n0)%nat as K eqn:HK.
  assert (Hk2 : k = (n0 + K)%nat) by (rewrite HK; lia).
  assert (HK1 : (1 <= K)%nat) by lia.
  assert (HE : (exp_series k 2%Q - q)%Q == dme2_rsum n0 K).
  { rewrite Hk2. rewrite Heq. rewrite dme2_exp_diff. reflexivity. }
  assert (Hge0 : Qle 0%Q (exp_series k 2%Q - q)%Q)
    by (rewrite HE; apply dme2_rsum_ge0).
  assert (Habs : Qabs ((exp_series k 2%Q - q)%Q) == (exp_series k 2%Q - q)%Q)
    by (apply Qabs_pos; exact Hge0).
  assert (Hmono : Qle (dme2_rsum n0 1%nat) (dme2_rsum n0 K))
    by (apply QleT'_to_Qle; apply (dme2_rsum_mono_K n0 1 K); exact HK1).
  assert (H1 : dme2_rsum n0 1%nat == dme2_anchor n0).
  { cbn [dme2_rsum]. rewrite Qplus_0_l.
    replace (n0 + 1)%nat with (Datatypes.S n0)%nat by lia.
    unfold dme2_anchor. reflexivity. }
  assert (Hchain : Qle (dme2_anchor n0) (exp_series k 2%Q - q)%Q).
  { rewrite HE. rewrite <- H1. exact Hmono. }
  assert (Hc2 : Qlt ((2#1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q
                     (dme2_anchor n0)).
  { rewrite (dme2_anchor_Z n0).
    pose proof (dme2_pow2_Zpos (Datatypes.S n0)) as Hpz.
    assert (HF7 : (0 < Z.of_nat (fact (Datatypes.S n0)))%Z)
      by apply dmeq_Zfact_pos.
    assert (Hb0 : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
    unfold Qlt, Qdiv, Qinv.
    destruct (Z.of_nat (fact (Datatypes.S n0))) as [| Fp | Fp] eqn:HF7c.
    + lia.
    + cbn [Qnum Qden Qmult].
      assert (Hmz : (0 < 2 ^ Z.of_nat (Datatypes.S n0) * Z.pos (Qden q))%Z)
        by (apply Zmult_lt_0_compat; lia).
      nia.
    + exfalso. exact (dmeq_Zofnat_neqneg _ _ HF7c). }
  assert (Hcc : (((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                 + ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                    * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
                == ((2#1)%Q * ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                               * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q)))%Q).
  { unfold Qeq, Qplus, Qmult. cbn [Qnum Qden Qmult]. nia. }
  pose proof (Qlt_le_trans _ _ _ Hc2 Hchain) as Hltc.
  rewrite <- Hcc in Hltc.
  assert (Hfin : Qlt ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
                     ((exp_series k 2%Q - q)%Q
                      - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                         * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
  { apply (lic_qlt_add_r_cancel_r
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q
             ((exp_series k 2%Q - q)%Q
              - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
             ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    rewrite (lic_qlt_minus_add_r (exp_series k 2%Q - q)%Q
               ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
    exact Hltc. }
  assert (Hbr : ((exp_series k 2%Q - q)%Q
                 - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                    * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
                == ((Qabs ((q - exp_series k 2%Q)%Q))
                    - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                       * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q).
  { assert (Habs2 : Qabs ((q - exp_series k 2%Q)%Q)
                    == Qabs ((exp_series k 2%Q - q)%Q)).
    { rewrite (Qabs_Qminus q (exp_series k 2%Q)). reflexivity. }
    apply (sif_plus_comp
             ((exp_series k 2%Q - q)%Q)
             (- ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)
             ((Qabs ((q - exp_series k 2%Q)%Q)))
             (- ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                 * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)).
    - apply (Qeq_trans _ (Qabs ((exp_series k 2%Q - q)%Q))).
      + apply Qeq_sym. exact Habs.
      + apply Qeq_sym. exact Habs2.
    - reflexivity. }
  apply (lic_qltt_comp_r
            ((exp_series k 2%Q - q)%Q
             - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
            ((Qabs ((q - exp_series k 2%Q)%Q))
             - ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
                * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q)%Q
            ((1 # 4)%Q * (1%Q / ((Z.pos (Qden q)) # 1)%Q)
             * (1%Q / ((Z.of_nat (fact (Datatypes.S n0))) # 1)%Q))%Q).
  - exact Hbr.
  - apply Qlt_to_QltT. exact Hfin.
Qed.

Theorem dme2_e2_qcore : forall (a : Z) (bb : positive) (k : nat),
  ((Z.to_nat (Z.pos bb) + 7)%nat <= k)%nat ->
  ((a # bb)%Q == exp_series (Z.to_nat (Z.pos bb) + 6) 2%Q) ->
  QltT ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
        * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
       (Qabs (((a # bb)%Q - exp_series k 2%Q)%Q)).
Proof.
  intros a bb k Hk7 Heq.
  apply (dme2_margin_to_sep
          ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q
          (Qabs (((a # bb)%Q - exp_series k 2%Q)%Q))).
  - assert (H7 : (Z.to_nat (Z.pos bb) + 7)%nat
                 = Datatypes.S (Z.to_nat (Z.pos bb) + 6))
      by (rewrite Nat.add_succ_r; reflexivity).
    rewrite H7 in Hk7.
    rewrite H7.
    exact (dme2_caseB2 ((a # bb)%Q) (Z.to_nat (Z.pos bb) + 6) k
            ltac:(lia) Hk7 Heq).
  - apply Qle_to_QleT'. apply Qlt_le_weak.
    exact (QltT_to_Qlt _ _ (dme2_const_pos a bb)).
Qed.

(* ============================================================ *)
(* S6：条件形实层装配件（经 dmec_escape_to_dist_any 参数化桥）            *)
(* ============================================================ *)

Theorem u5c_e2_conditional_measure : forall (a : Z) (bb : positive) (n0 : nat),
  (1 <= n0)%nat ->
  QltT (dme2_tb n0) (Qabs (((a # bb)%Q - exp_series n0 2%Q)%Q)) ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric dme2_X_e2 (real_const ((a # bb)%Q))))).
Proof.
  intros a bb n0 Hn0 Hesc.
  apply (dmec_escape_to_dist_any (fun n : nat => exp_series n 2%Q) dme2_tb
           dme2_tail_bounded dme2_vanish ((a # bb)%Q) n0 Hn0 Hesc
           (((Qabs (((a # bb)%Q - exp_series n0 2%Q)%Q) - dme2_tb n0)
             * (1 # 2))%Q)).
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat
             (Qabs (((a # bb)%Q - exp_series n0 2%Q)%Q) - dme2_tb n0)%Q
             (1 # 2)%Q).
    + apply lic_qlt_0_minus. exact (QltT_to_Qlt _ _ Hesc).
    + unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qle_to_QleT'. apply qeq_le.
    assert (Hh : ((1 # 2)%Q + (1 # 2)%Q)%Q == 1%Q)
      by (unfold Qeq, Qplus, Qmult; cbn [Qnum Qden Qmult]; lia).
    rewrite <- (Qmult_plus_distr_r
                  (Qabs (((a # bb)%Q - exp_series n0 2%Q)%Q) - dme2_tb n0)%Q
                  (1 # 2)%Q (1 # 2)%Q).
    rewrite Hh. rewrite Qmult_1_r. reflexivity.
Qed.

(* ============================================================ *)
(* S7：CaseB 实层装配件（u5c_e_closed_measure 同构）                      *)
(* ============================================================ *)

Theorem u5c_e2_caseB_measure : forall (a : Z) (bb : positive),
  ((a # bb)%Q == exp_series (Z.to_nat (Z.pos bb) + 6) 2%Q) ->
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                  * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)
         (real_lt (real_const ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)
            (real_metric dme2_X_e2 (real_const ((a # bb)%Q)))))).
Proof.
  intros a bb Heq.
  exists ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
          * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
  split.
  - exact (dme2_const_pos a bb).
  - split.
    + apply qeq_imp_qeqT. reflexivity.
    + unfold real_lt.
      exists ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
              * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q.
      split.
      * exact (dme2_const_pos a bb).
      * exists (Z.to_nat (Z.pos bb) + 7)%nat. intros k HkN.
        apply NatLe_drop in HkN.
        assert (HPr : projT1 (real_metric dme2_X_e2
                                  (real_const ((a # bb)%Q))) k
                      == Qabs ((exp_series k 2%Q - (a # bb)%Q)%Q))
          by apply lic_metric_proj.
        apply (lic_qltt_comp_r
                  ((Qabs (((a # bb)%Q - exp_series k 2%Q)%Q))
                   - ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                      * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q)%Q
                  (projT1 (real_metric dme2_X_e2 (real_const ((a # bb)%Q))) k
                   - projT1 (real_const ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                                         * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q) k)
                  ((1 # 4)%Q * (1%Q / ((Z.pos bb) # 1)%Q)
                   * (1%Q / ((Z.of_nat (fact (Z.to_nat (Z.pos bb) + 7))) # 1)%Q))%Q).
        -- rewrite real_const_proj. rewrite HPr.
           rewrite (Qabs_Qminus ((a # bb)%Q) (exp_series k 2%Q)). reflexivity.
        -- assert (H7 : (Z.to_nat (Z.pos bb) + 7)%nat
                       = Datatypes.S (Z.to_nat (Z.pos bb) + 6))
             by (rewrite Nat.add_succ_r; reflexivity).
           rewrite H7 in HkN. rewrite H7.
           exact (dme2_caseB2 ((a # bb)%Q) (Z.to_nat (Z.pos bb) + 6) k
                   ltac:(lia) HkN Heq).
Qed.

(* ============================================================ *)
(* S8：死窗否定件（CaseA 路线对 B=2 结构性不可闭合·在机证书）              *)
(* ============================================================ *)

Lemma dme2_gap_le_firsttail : forall (bb : positive) (n : nat),
  QleT' (dme2_gapc bb n) (dme2_anchor n).
Proof.
  intros bb n. unfold dme2_gapc. apply Qle_to_QleT'.
  rewrite (dme2_anchor_Z n). unfold Qle, Qmult, Qdiv, Qinv.
  assert (Hzs : (Z.of_nat (Datatypes.S n) <= 2 ^ Z.of_nat (Datatypes.S n))%Z).
  { replace (2 ^ Z.of_nat (Datatypes.S n))%Z
      with (Z.of_nat (2 ^ Datatypes.S n)%nat)
      by (rewrite Nat2Z.inj_pow; reflexivity).
    apply (proj1 (Nat2Z.inj_le _ _)).
    pose proof (dme2_pow2_ge_succ (Datatypes.S n)). lia. }
  pose proof (dmeq_Zfact_pos n) as HPF.
  destruct (Z.of_nat (fact (Datatypes.S n))) as [| F7 | F7] eqn:H7.
  - pose proof (dmeq_Zfact_pos (Datatypes.S n)) as HP. lia.
  - pose proof (dme2_factS_Z n) as HFS. rewrite H7 in HFS.
    destruct (Z.of_nat (fact n)) as [| Ff | Ff] eqn:HF.
    + lia.
    + cbn [Qnum Qden Qmult].
      pose proof (sif_posZ bb) as Hbb.
      assert (Hmb : (Z.of_nat (Datatypes.S n)
                     <= 2 ^ Z.of_nat (Datatypes.S n) * Z.pos bb)%Z) by nia.
      assert (Hfin : (Z.pos F7 <= 2 ^ Z.of_nat (Datatypes.S n)
                                        * (Z.pos bb * Z.pos Ff))%Z).
      { rewrite HFS.
        replace (2 ^ Z.of_nat (Datatypes.S n) * (Z.pos bb * Z.pos Ff))%Z
          with ((2 ^ Z.of_nat (Datatypes.S n) * Z.pos bb) * Z.pos Ff)%Z by ring.
        apply (Zmult_le_compat_r _ _ _ Hmb (Z.lt_le_incl _ _ HPF)). }
      lia.
    + exfalso. exact (dmeq_Zofnat_neqneg (fact n) Ff HF).
  - exfalso. exact (dmeq_Zofnat_neqneg (fact (Datatypes.S n)) F7 H7).
Qed.

Lemma dme2_caseA_route_dead : forall (bb : positive) (n0 : nat), (1 <= n0)%nat ->
  Not (QltT (dme2_tb n0) (dme2_gapc bb n0)).
Proof.
  intros bb n0 Hn0 Hlt.
  pose proof (QleT'_to_Qle _ _ (dme2_gap_le_firsttail bb n0)) as H1.
  assert (H3 : Qle (dme2_anchor n0) (dme2_tb n0)).
  { unfold dme2_tb.
    assert (HE : (((Z.of_nat n0 + 2)%Z # 1)%Q
                  * (1%Q / ((Z.of_nat n0)%Z # 1)%Q))%Q
                 == (1%Q + ((2#1)%Q * (1%Q / ((Z.of_nat n0)%Z # 1)%Q)))%Q).
    { destruct (Z.of_nat n0) as [| Nn | Nn] eqn:HN.
      - pose proof (dmeq_Zofnat_eq0 n0 HN) as H0. lia.
      - unfold Qeq, Qplus, Qmult, Qdiv, Qinv.
        cbn [Qnum Qden Qmult Qinv Pos.mul]. nia.
      - exfalso. exact (dmeq_Zofnat_neqneg n0 Nn HN). }
    rewrite HE. rewrite Qmult_plus_distr_r. rewrite Qmult_1_r.
    apply QleT'_to_Qle. apply dmeq_le_add_r.
    apply dmeq_mul_ge0.
    + apply dme2_anchor_ge0.
    + apply dmeq_mul_ge0.
      * apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
      * apply Qle_to_QleT'. apply Qlt_le_weak.
        exact (lic_qlt_comp_r _ _ _
                 (Qeq_sym _ _ (Qmult_1_l (Qinv ((Z.of_nat n0)%Z # 1)%Q)))
                 (Qinv_lt_0_compat ((Z.of_nat n0)%Z # 1)%Q
                    ltac:(unfold Qlt; cbn [Qnum Qden Qmult]; lia))). }
  pose proof (QltT_to_Qlt _ _ Hlt) as H2.
  assert (H4 : Qlt (dme2_tb n0) (dme2_anchor n0))
    by exact (Qlt_le_trans _ _ _ H2 H1).
  exact (match (Qlt_irrefl _ (Qle_lt_trans _ _ _ H3 H4)) with end).
Qed.

(* ============================================================ *)
(* S9：提取检验＋假设面自审＋主定理见证实跑                               *)
(* ============================================================ *)

Definition dme2_run_escape_ok : bool :=
  Qlt_bool (dme2_tb 8%nat) (Qabs ((3 # 1)%Q - exp_series 8 2%Q)%Q).

Definition dme2_run_caseB_ok : bool :=
  Qlt_bool ((1 # 4)%Q * (1%Q / ((Z.pos 1) # 1)%Q)
            * (1%Q / ((Z.of_nat (fact 7)) # 1)%Q))%Q
            (Qabs ((exp_series 7 2%Q - exp_series 9 2%Q)%Q)).

Definition dme2_run_dead_ok : bool :=
  match Qlt_bool (dme2_tb 3%nat) (dme2_gapc 5%positive 3%nat) with
  | true => false
  | false => true
  end.

From Stdlib Require Import Extraction.
Separate Extraction dme2_run_escape_ok dme2_run_caseB_ok dme2_run_dead_ok
  u5c_e2_conditional_measure u5c_e2_caseB_measure dme2_e2_qcore
  dme2_caseA_route_dead dme2_gap dme2_frac_prod dme2_tail_bounded dme2_vanish
  dme2_anchor dme2_tb dme2_gapc dme2_X_e2.

Print Assumptions dme2_e2_qcore.
Print Assumptions u5c_e2_caseB_measure.
Print Assumptions u5c_e2_conditional_measure.
Print Assumptions dme2_caseA_route_dead.
Print Assumptions dme2_gap.
Print Assumptions dme2_tail_bounded.
Print Assumptions dme2_vanish.
