(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ln2b_irrational_from_supply（原 L671，2 句玩具证）                   *)
(*   ln2b_X_proj（原 L68，2 句玩具证）                                    *)
(* ============================================================ *)

(* ============================================================ *)
(* Ln2Bridge.v —— ln2 无理数 supply 接口件：供给型 ln2i_pade_supply 与    *)
(*   由其导出的 δ 提取、逃逸规格、无理性推论三件，另附平凡三元组反例      *)
(*   ln2b_supply_trivial_hit。                                          *)
(*                                                                     *)
(* 基准对象：ln2b_X = ln2i_x 的柯西极限（存在性由母件 UpReqLn2Irrational *)
(*   的尾控制 ln2i_tail 与消失条件 ln2i_vanish 供给）；整系数线性形式    *)
(*   ln2b_line A B n = |A_n·X − B_n|，第 k 投影为 Q 层 |A_n·x_k − B_n|。 *)
(*                                                                     *)
(* ln2i_pade_supply（供给型，sigT 五层）：对整系数 A B : nat→Z、载体      *)
(*   clo : nat→Q、底 θ : Q，合取五个组成条件：① QltT θ 1；              *)
(*   ② ∀n, QltT 0 |A_n|（A_n ≠ 0 的 Q 层编码）；③ ∀n, QltT 0 (clo n)；   *)
(*   ④⑤ 下/上界肢 ln2b_line_lower / ln2b_line_upper：                  *)
(*   clo_n ≤ |A_n·X − B_n| ≤ θ^n（real_le 面承载）。                    *)
(*                                                                     *)
(* ln2b_delta_of_supply：由 supply 与有理数 q = u/v 提取显式正 δ 与阈值  *)
(*   K，使 δ ≤ |q − x_k|（∀k ≥ K）。以 Z.eq_dec 对 u·A_{n₀} = v·B_{n₀}    *)
(*   作可判定分叉（零 LPO），分两支各给显式 δ：                          *)
(*   · 否支（u·A_{n₀} ≠ v·B_{n₀}）：δ := ((1/v − θ^{n₀})/2)·|A_{n₀}|⁻¹； *)
(*   · 中支（u·A_{n₀} = v·B_{n₀}）：δ := (clo_{n₀}/2)·|A_{n₀}|⁻¹，正性   *)
(*     由条件 ③ 供给。若 X = q，下界肢给出 clo_{n₀} ≤ |A_{n₀}·X − B_{n₀}| *)
(*     = 0，与 ③ 矛盾——伪 supply 于中支自相矛盾                        *)
(*     （反例 ln2b_supply_trivial_hit 实证其 δ ≤ 0）。                   *)
(*                                                                     *)
(* ln2b_escape_of_supply：supply ⟹ ln2i_escape_spec。取指标              *)
(*   m := S(max K N)：ln2i_vanish 于 δ 给显式 N，与终归点式肢在 m 处      *)
(*   合取：ln2i_e m < δ ≤ |q − x_m|。                                    *)
(*                                                                     *)
(* ln2b_irrational_from_supply：结论面直接应用母定理 lic_irrational_criterion。 *)
(*                                                                     *)
(* ln2b_supply_trivial_hit（反例见证）：平凡三元组 A:=1、B:=0、clo:=0    *)
(*   于 q:=0 命中中支判据（0·A₀ = 1·B₀）而中支 δ ≤ 0——组成条件 ③ 对     *)
(*   中支正性不可省。                                                   *)
(*                                                                     *)
(* 接口地位：ln2i_pade_supply 是 Hermite–Beukers 候选一构造的输出接口：   *)
(*   其 (A_n, B_n, clo_n, θ) 一旦满足上述五个组成条件，δ 提取与逃逸      *)
(*   两件即可应用。Ln2Escape.v 的 lne_B n = (n!)²/(2n+1)! 是 clo_n 与    *)
(*   整性条件的候选实例（本件不 Require 之，仅记述）。                   *)
(*                                                                     *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、  *)
(*   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqLn2Irrational；  *)
(*   Stdlib QArith、ZArith、Arith、Lia、Setoid、Morphisms、Lra、Qfield。 *)
(* 构造性注记：语句面全 Set（QltT/QleT'/QeqT/real_lt/real_le/sigT/       *)
(*   S01.And）；证明内 Prop（Qlt/Qle）仅作 Q 层推理辅助；零承认；可提取。 *)
(* 编译配方：coqc 9.1 直调无 -Q，cpu_guard 包裹，-o 临时目录（树内 .vo 不动）。 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Lra Qfield.

(* ============================================================ *)
(* §0 基准实数 X = lim ln2i_x 与 line 投影面                           *)
(* ============================================================ *)

(* 基准实数：ln2i_x 的柯西极限（极限存在性由 ln2i_tail 尾控制与 ln2i_vanish 两条件供给） *)
Definition ln2b_X : Real :=
  existT (fun u : Qseq => cauchy u) ln2i_x
    (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish).

Lemma ln2b_X_proj : forall k : nat, projT1 ln2b_X k == ln2i_x k.
Proof. intro k. unfold ln2b_X. cbn [projT1]. exact (Qeq_refl (ln2i_x k)). Qed.

(* 整系数有理线性形式在基准实数上的绝对值（supply 的 real 面界所约束的对象）：
   ln2b_line A B n = |A_n·X − B_n|，其第 k 投影 = |A_n·x_k − B_n|（Q 层）。 *)
Definition ln2b_line (A B : nat -> Z) (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const ((A n) # 1)%Q) ln2b_X)
                      (real_opp (real_const ((B n) # 1)%Q))).

Lemma ln2b_line_pt : forall (A B : nat -> Z) (n k : nat),
  projT1 (ln2b_line A B n) k == Qabs (((((A n) # 1)%Q) * ln2i_x k - ((B n) # 1)%Q)%Q).
Proof.
  intros A B n k. unfold ln2b_line.
  rewrite real_abs_proj, real_plus_proj, real_mult_proj, real_opp_proj,
          real_const_proj, ln2b_X_proj.
  reflexivity.
Qed.

(* ============================================================ *)
(* §1 ln2i_pade_supply：供给型（sigT 五层，五个 Set 面组成条件） *)
(* ============================================================ *)

(* 下界肢：载体条件 clo_n ≤ |A_n·X − B_n|（real_le Or-编码） *)
Definition ln2b_line_lower (A B : nat -> Z) (clo : nat -> Q) : Set :=
  forall n : nat, real_le (real_const (clo n)) (ln2b_line A B n).

(* 上界肢：|A_n·X − B_n| ≤ θ^n（Q 层幂 q_pow θ n 承载） *)
Definition ln2b_line_upper (A B : nat -> Z) (th : Q) : Set :=
  forall n : nat, real_le (ln2b_line A B n) (real_const (q_pow th n)).

(* 供给型：Hermite–Beukers 候选一构造的输出接口。
   五个组成条件：① θ<1；② 0<|A_n|（A_n≠0 的 Set 面 Q 编码）；③ 0<clo_n；
   ④⑤ 下/上界 real 肢。 *)
Definition ln2i_pade_supply : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      sigT (fun clo : nat -> Q =>
        sigT (fun th : Q =>
          And (QltT th (1 # 1))
            (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
              (And (forall n : nat, QltT 0 (clo n))
                (And (ln2b_line_lower A B clo)
                     (ln2b_line_upper A B th)))))))).

(* ============================================================ *)
(* §2 供给面的逐点形式：real_le 的终归 slack 形 *)
(* ============================================================ *)

(* Q 层引理：a ≤ |a| *)
Lemma ln2b_abs_ge : forall a : Q, Qle a (Qabs a).
Proof.
  intros [an ad]. unfold Qle, Qabs. cbn [Qnum Qden].
  destruct an; cbn; lia.
Qed.

(* Q 层引理：|a| < b ⟹ a < b *)
Lemma ln2b_abs_lt : forall a b : Q, Qlt (Qabs a) b -> Qlt a b.
Proof.
  intros [an ad] [bn bd]. unfold Qlt, Qabs in *. cbn [Qnum Qden] in *.
  destruct an; cbn in *; lia.
Qed.

(* real_le 的终归 slack 形：x ≤ y（real_le Or-编码两支统一）⟹
   ∀eps>0 ∃K ∀k≥K，x_k < y_k + eps。
   情形 lt：x_k < y_k（严格分离，加 eps 更松）；情形 eq：|x_k−y_k| < eps
   且 x_k ≤ (x_k−y_k)+y_k ≤ |x_k−y_k|+y_k < y_k+eps。零 LPO。 *)
Lemma ln2b_le_pt_slack : forall (x y : Real), real_le x y ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
    QltT (projT1 x k) ((projT1 y k + eps)%Q)).
Proof.
  intros x y H eps Heps.
  destruct H as [Hlt | Heq].
  - (* 情形 lt：x < y 的严格分离支 *)
    destruct Hlt as [e [He0 [N HN]]].
    exists N. intros k Hk.
    pose proof (HN k (NatLe_lift _ _ Hk)) as HNk.
    pose proof (QltT_to_Qlt _ _ He0) as He0'.
    pose proof (QltT_to_Qlt _ _ HNk) as HNk'.
    assert (Hyx : Qlt 0 ((projT1 y k - projT1 x k)%Q))
      by (eapply Qlt_trans; eassumption).
    assert (Hxy : Qlt (projT1 x k) (projT1 y k)).
    { assert (Hr : ((projT1 x k + (projT1 y k - projT1 x k))%Q) == projT1 y k)
        by ring.
      apply (lic_qlt_lt_add_r (projT1 x k)
               ((projT1 y k - projT1 x k)%Q)) in Hyx.
      rewrite Hr in Hyx. exact Hyx. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (projT1 x k) (projT1 y k) ((projT1 y k + eps)%Q)).
    + exact Hxy.
    + assert (Hle : Qle (projT1 y k + 0%Q) ((projT1 y k + eps)%Q)).
      { apply (Qplus_le_compat (projT1 y k) (projT1 y k) 0%Q eps).
        - apply Qle_refl.
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps. }
      apply (Qle_trans (projT1 y k) (projT1 y k + 0%Q)
               ((projT1 y k + eps)%Q)).
      * apply qeq_le. symmetry. apply Qplus_0_r.
      * exact Hle.
  - (* 情形 eq：|x_k−y_k| < eps ⟹ x_k ≤ |x_k−y_k|+y_k < y_k+eps *)
    destruct (Heq eps Heps) as [N HN].
    exists N. intros k Hk.
    pose proof (HN k (NatLe_lift _ _ Hk)) as HNk.
    pose proof (QltT_to_Qlt _ _ HNk) as Habs.
    (* x_k ≤ (x_k−y_k)+y_k ≤ |x_k−y_k|+y_k < e0+y_k == y_k+e0 *)
    assert (Hstep : Qle (projT1 x k)
                     ((Qabs ((projT1 x k - projT1 y k)%Q) + projT1 y k)%Q)).
    { assert (Hshift : ((projT1 x k - projT1 y k)%Q + projT1 y k)%Q
                       == projT1 x k) by ring.
      apply (Qle_trans (projT1 x k)
               ((projT1 x k - projT1 y k)%Q + projT1 y k)%Q
               (Qabs ((projT1 x k - projT1 y k)%Q) + projT1 y k)%Q).
      - apply qeq_le. rewrite Hshift. apply Qeq_refl.
      - apply (Qplus_le_compat (projT1 x k - projT1 y k)%Q
                 (Qabs ((projT1 x k - projT1 y k)%Q))
                 (projT1 y k) (projT1 y k)).
        + apply ln2b_abs_ge.
        + apply Qle_refl. }
    assert (Hadd : Qlt (projT1 y k + Qabs ((projT1 x k - projT1 y k)%Q))%Q
                       (projT1 y k + eps)%Q)
      by (apply (lic_qlt_add_l (projT1 y k)
                   (Qabs ((projT1 x k - projT1 y k)%Q)) eps); exact Habs).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (projT1 x k)
            (Qabs ((projT1 x k - projT1 y k)%Q) + projT1 y k)%Q
            ((projT1 y k + eps)%Q)).
    + exact Hstep.
    + setoid_rewrite (Qplus_comm (projT1 y k)
                        (Qabs ((projT1 x k - projT1 y k)%Q))) in Hadd.
      exact Hadd.
Qed.

(* ============================================================ *)
(* §3 衰减引理：0 < θ < 1 ⟹ 显式 n₀ 使 θ^{n₀} < 1/v（零 LPO，全显式） *)
(* ============================================================ *)

(* q_pow 分母 1 形：q_pow ((c#1)) n == (c^n)#1)（分母恒 1，cbn 可归约，
   归约无残留 Qinv——Q 构造子正分母只收 positive，Z 幂不可入，不经除法形） *)
Lemma ln2b_qpow_num : forall (c : Z) (n : nat),
  q_pow ((c # 1)%Q) n == ((c ^ (Z.of_nat n)) # 1)%Q.
Proof.
  intros c n. induction n as [| n IH].
  - reflexivity.
  - rewrite q_pow_succ. rewrite IH.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* 跨分母乘法引理：q_pow (a#b) n · q_pow (b#1) n == q_pow (a#1) n
   （(a/b)^n·b^n = a^n；Q 环重排与归纳假设，无残留形） *)
Lemma ln2b_ab_b : forall (a : Z) (b : positive),
  ((a # b)%Q * ((Z.pos b # 1)%Q))%Q == ((a # 1)%Q).
Proof.
  intros a b. unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

Lemma ln2b_qpow_inv : forall (a : Z) (b : positive) (n : nat),
  q_pow ((a # b)%Q) n * q_pow ((Z.pos b # 1)%Q) n == q_pow ((a # 1)%Q) n.
Proof.
  intros a b n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow].
    transitivity ((q_pow ((a # b)%Q) n * q_pow ((Z.pos b # 1)%Q) n)
                   * (((a # b)%Q) * ((Z.pos b # 1)%Q)))%Q.
    + ring.
    + rewrite ln2b_ab_b. rewrite IH. ring.
Qed.

(* q_pow (c#1) n 的正性（作 Qmult_lt_r 的正乘子） *)
Lemma ln2b_qpow_pos1 : forall (c : Z) (n : nat), (0 < c)%Z ->
  Qlt 0 (q_pow ((c # 1)%Q) n).
Proof.
  intros c n Hc. rewrite ln2b_qpow_num.
  induction n as [| n IHn].
  - unfold Qlt. cbn. lia.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    assert (Heq : (((c # 1)%Q) * ((c ^ (Z.of_nat n)) # 1)%Q)%Q
                   == ((c * c ^ (Z.of_nat n)) # 1)%Q)
      by (unfold Qmult, Qeq; cbn [Qnum Qden Pos.mul]; lia).
    rewrite <- Heq.
    apply Qmult_lt_0_compat.
    + unfold Qlt. cbn. lia.
    + exact IHn.
Qed.

(* nat 幂 ≥ 1 *)
Lemma ln2b_pow_ge1 : forall A k : nat, (1 <= A)%nat -> (1 <= A ^ k)%nat.
Proof.
  intros A k HA. induction k as [| k IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* nat 层 Bernoulli 幂不等式：A^n + n·A^{n−1} ≤ (A+1)^n（n ≥ 1） *)
Lemma ln2b_pow_bern : forall A n : nat,
  (1 <= A)%nat -> (1 <= n)%nat -> (A ^ n + n * A ^ (n - 1) <= (A + 1) ^ n)%nat.
Proof.
  intros A n HA. induction n as [| n IH].
  - intro Hn. cbn [Nat.pow Nat.sub]. lia.
  - intro Hn. destruct (Nat.eq_dec n 0) as [H0 | Hne].
    + subst n. cbn [Nat.pow Nat.sub]. lia.
    + assert (Hn1 : (1 <= n)%nat) by lia.
      specialize (IH Hn1).
      replace (Datatypes.S n - 1)%nat with n by lia.
      rewrite (Nat.pow_succ_r' A n).
      rewrite (Nat.pow_succ_r' (A + 1) n).
      assert (Hmono : ((A + 1) * (A ^ n + n * A ^ (n - 1))
                       <= (A + 1) * ((A + 1) ^ n))%nat)
        by (apply Nat.mul_le_mono_l; exact IH).
      assert (Hbb : (A ^ n = A * A ^ (n - 1))%nat).
      { replace n with (Datatypes.S (n - 1))%nat at 1 by lia.
        rewrite Nat.pow_succ_r'. reflexivity. }
      assert (Hbridge : (A * (n * A ^ (n - 1)) = n * A ^ n)%nat).
      { rewrite Hbb. ring. }
      assert (Hexp : ((A + 1) * (A ^ n + n * A ^ (n - 1))
                      = A * A ^ n + A * (n * A ^ (n - 1))
                        + A ^ n + n * A ^ (n - 1))%nat)
        by ring.
      lia.
Qed.

(* 显式指标不等式：V·A^{V·A} < (A+1)^{V·A}（V,A ≥ 1） *)
Lemma ln2b_pow_core : forall V A : nat,
  (1 <= V)%nat -> (1 <= A)%nat -> (V * A ^ (V * A) < (A + 1) ^ (V * A))%nat.
Proof.
  intros V A HV HA.
  assert (HN : (1 <= V * A)%nat) by lia.
  pose proof (ln2b_pow_bern A (V * A) HA HN) as HB.
  assert (Hpow : (A ^ (V * A) = A * A ^ (V * A - 1))%nat).
  { replace (V * A)%nat with (Datatypes.S (V * A - 1))%nat at 1 by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  rewrite Hpow in HB.
  pose proof (ln2b_pow_ge1 A (V * A - 1) HA) as Hge1.
  rewrite Hpow.
  lia.
Qed.

(* 幂不等式 nat → Z 提升（指数/底经 Nat2Z 单射搬运） *)
Lemma ln2b_pow_lift : forall V' A' B' : nat,
  (1 <= V')%nat -> (1 <= A')%nat ->
  (V' * A' ^ (V' * A') < B' ^ (V' * A'))%nat ->
  (Z.of_nat V' * (Z.of_nat A') ^ (Z.of_nat V' * Z.of_nat A')
   < (Z.of_nat B') ^ (Z.of_nat V' * Z.of_nat A'))%Z.
Proof.
  intros V' A' B' HV' HA' Hnat.
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hnat) as E1.
  rewrite (Nat2Z.inj_mul V' (A' ^ (V' * A'))) in E1.
  rewrite (Nat2Z.inj_pow A' (V' * A')) in E1.
  rewrite (Nat2Z.inj_pow B' (V' * A')) in E1.
  rewrite (Nat2Z.inj_mul V' A') in E1.
  exact E1.
Qed.

(* 衰减引理：0 < θ < 1、分母 v（positive）⟹ 显式 n₀ = v·num(θ) 使
   证明：θ = a/b（a ≥ 1、b ≥ a+1），取 n₀ := v·a，
   Bernoulli 给 (a+1)^{n₀} ≥ a^{n₀} + n₀·a^{n₀−1} = (v+1)·a^{n₀}
   > v·a^{n₀}，又 b^{n₀} ≥ (a+1)^{n₀}。零 LPO（全显式指标）。 *)
Lemma ln2b_decay : forall th : Q, QltT 0 th -> QltT th (1 # 1) ->
  forall v : positive,
  sigT (fun n0 : nat => QltT (q_pow th n0) ((1 # v)%Q)).
Proof.
  intros th H0 H1 v.
  pose proof (QltT_to_Qlt 0 th H0) as H0q.
  pose proof (QltT_to_Qlt th (1 # 1) H1) as H1q.
  destruct th as [a b].
  assert (Ha : (0 < a)%Z).
  { unfold Qlt in H0q. cbn [Qnum Qden] in H0q.
    assert (Hdv : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos. lia. }
  assert (Hltb : (a < Z.pos b)%Z).
  { unfold Qlt in H1q. cbn [Qnum Qden] in H1q.
    assert (Hdv : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos. lia. }
  assert (Hid : Z.of_nat (Z.to_nat (Z.pos v * a)) = (Z.pos v * a)%Z)
    by (apply Z2Nat.id; lia).
  exists (Z.to_nat (Z.pos v * a)).
  apply Qlt_to_QltT.
  assert (Hpos : Qlt 0 (q_pow ((Z.pos b # 1)%Q) (Z.to_nat (Z.pos v * a))))
    by (apply ln2b_qpow_pos1; lia).
  apply (proj1 (Qmult_lt_r (q_pow ((a # b)%Q) (Z.to_nat (Z.pos v * a)))
                  (1 # v)%Q
                  (q_pow ((Z.pos b # 1)%Q) (Z.to_nat (Z.pos v * a))) Hpos)).
  rewrite ln2b_qpow_inv. rewrite ln2b_qpow_num. rewrite ln2b_qpow_num. rewrite Hid.
  (* 终归 Z 不等式：a^{v·a}·v < b^{v·a} *)
  assert (Hcore : ((Z.pos v) * a ^ (Z.pos v * a)
                   < Z.pos b ^ (Z.pos v * a))%Z).
  { pose proof (ln2b_pow_core (Z.to_nat (Z.pos v)) (Z.to_nat a)
                  ltac:(lia) ltac:(lia)) as Hnat.
    assert (Hstep : ((Z.to_nat a + 1) ^ (Z.to_nat (Z.pos v) * Z.to_nat a)
                     <= Z.to_nat (Z.pos b) ^ (Z.to_nat (Z.pos v) * Z.to_nat a))%nat).
    { apply Nat.pow_le_mono_l. lia. }
    assert (Hfin : (Z.to_nat (Z.pos v) * Z.to_nat a ^ (Z.to_nat (Z.pos v) * Z.to_nat a)
                    < Z.to_nat (Z.pos b) ^ (Z.to_nat (Z.pos v) * Z.to_nat a))%nat)
      by lia.
    pose proof (ln2b_pow_lift (Z.to_nat (Z.pos v)) (Z.to_nat a)
                  (Z.to_nat (Z.pos b)) ltac:(lia) ltac:(lia) Hfin) as Hz.
    rewrite (Z2Nat.id (Z.pos v) ltac:(lia)) in Hz.
    rewrite (Z2Nat.id a ltac:(lia)) in Hz.
    rewrite (Z2Nat.id (Z.pos b) ltac:(lia)) in Hz.
    exact Hz. }
  unfold Qlt. cbn [Qmult Qnum Qden Pos.mul]. lia.
Qed.

(* ============================================================ *)
(* §4 δ 提取 ln2b_delta_of_supply：整判定两支显式正 δ（零 LPO） *)
(* ============================================================ *)

(* q_pow 的一次幂 *)
Lemma ln2b_qpow_one : forall th : Q, q_pow th 1 == th.
Proof.
  intro th. rewrite q_pow_succ. cbn [q_pow]. ring.
Qed.

(* 半值引理：a < b + a/2 ⟹ a/2 < b（destruct-Q nia） *)
Lemma ln2b_half_lt : forall a b : Q, Qlt a (b + a * (1 # 2))%Q ->
  Qlt (a * (1 # 2)) b.
Proof.
  intros [an ad] [bn bd]. unfold Qlt in *. cbn [Qnum Qden Qplus Qmult Pos.mul] in *.
  nia.
Qed.

(* 除法反向形式：0 < A、c < A·M ⟹ c·A⁻¹ < M *)
Lemma ln2b_div_lt_of : forall c A M : Q, QltT 0 A -> Qlt c (A * M)%Q ->
  Qlt (c * Qinv A) M.
Proof.
  intros c A M HA Hlt.
  assert (HA0 : ~ (A == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q A (QltT_to_Qlt _ _ HA)).
    exact (Qeq_sym _ _ E). }
  assert (HposI : Qlt 0 (Qinv A))
    by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; exact HA).
  pose proof (Qmult_lt_compat_r c (A * M)%Q (Qinv A) HposI Hlt) as Hlt2.
  assert (Hprod : ((A * M)%Q * Qinv A)%Q == M%Q).
  { rewrite (Qmult_comm A M). rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r A HA0). ring. }
  exact (lic_qlt_comp_r ((A * M)%Q * Qinv A) M (c * Qinv A) Hprod Hlt2).
Qed.

(* 整系数 Q 线性式的通分：(a#1)·(u#v) − (b#1) == (u·a − v·b)#v *)
Lemma ln2b_line_q : forall (a b u : Z) (v : positive),
  (((a # 1)%Q * ((u # v)%Q) - ((b # 1)%Q))%Q) == (((u * a - Z.pos v * b) # v)%Q).
Proof.
  intros a b u v.
  unfold Qmult, Qminus, Qplus, Qopp, Qeq. cbn [Qnum Qden Pos.mul].
  lia.
Qed.

(* 中支行等式：A₀·q == B₀ ⟹ |A₀·x_k − B₀| == |A₀|·|x_k − q| *)
Lemma ln2b_hit_line : forall (A0 B0 : Z) (q : Q) (k : nat),
  (((A0 # 1)%Q * q - (B0 # 1)%Q)%Q == 0%Q) ->
  Qabs (((A0 # 1)%Q * ln2i_x k - (B0 # 1)%Q)%Q)
  == Qabs ((A0 # 1)%Q) * Qabs ((ln2i_x k - q)%Q).
Proof.
  intros A0 B0 q k Hhit.
  assert (HB : ((B0 # 1)%Q) == ((A0 # 1)%Q * q)%Q).
  { symmetry.
    transitivity (((A0 # 1)%Q * q - (B0 # 1)%Q + (B0 # 1)%Q)%Q).
    - ring.
    - rewrite Hhit. ring. }
  rewrite HB.
  assert (Hfac : ((A0 # 1)%Q * ln2i_x k - (A0 # 1)%Q * q)%Q
                 == ((A0 # 1)%Q * (ln2i_x k - q)%Q)%Q) by ring.
  rewrite Hfac. rewrite Qabs_Qmult. reflexivity.
Qed.

(* δ 提取主件：供给型 + 有理数 q ⟹ 显式正 δ 与终归点式肢
   δ ≤ |q − x_k|（k ≥ K）。分情形（Z.eq_dec 可判定）：
   - 否支（u·A_{n₀} ≠ v·B_{n₀}）：δ := ((1/v − θ^{n₀})/2)·|A_{n₀}|⁻¹；
   - 中支（u·A_{n₀} = v·B_{n₀}）：δ := (clo_{n₀}/2)·|A_{n₀}|⁻¹
     （正性由载体条件 clo>0 供给——若 X = q 则下界肢与 clo>0 矛盾，
      伪 supply 被排除，见反例 ln2b_supply_trivial_hit）。 *)
Theorem ln2b_delta_of_supply : forall (Hs : ln2i_pade_supply) (q : Q),
  sigT (fun d : Q => And (QltT 0 d)
    (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       QleT' d (Qabs ((q - ln2i_x k)%Q))))).
Proof.
  intros Hs q.
  destruct Hs as [A [B [clo [th [Hth1 [HA [Hclo [Hlow Hup]]]]]]]].
  destruct q as [u v].
  assert (Hv0 : (0 < Z.pos v)%Z) by lia.
  (* —— θ > 0：下界肢/上界肢的 slack 形在公共指标 k₀ 夹出 —— *)
  assert (Heps1 : QltT 0 (((clo 1)%nat) * (1 # 2))%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply (Hclo 1%nat).
    - unfold Qlt. cbn. lia. }
  destruct (ln2b_le_pt_slack (real_const ((clo 1)%nat)) (ln2b_line A B 1%nat) (Hlow 1%nat)
             (((clo 1)%nat) * (1 # 2))%Q Heps1) as [K1 HK1].
  assert (Heps2 : QltT 0 (((clo 1)%nat) * (1 # 4))%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply (Hclo 1%nat).
    - unfold Qlt. cbn. lia. }
  destruct (ln2b_le_pt_slack (ln2b_line A B 1%nat) (real_const (q_pow th 1)) (Hup 1%nat)
             (((clo 1)%nat) * (1 # 4))%Q Heps2) as [K2 HK2].
  pose proof (HK1 (Nat.max K1 K2) (Nat.le_max_l _ _)) as HK1k.
  pose proof (HK2 (Nat.max K1 K2) (Nat.le_max_r _ _)) as HK2k.
  pose proof (QltT_to_Qlt _ _ HK1k) as HK1q.
  pose proof (QltT_to_Qlt _ _ HK2k) as HK2q.
  rewrite (real_const_proj ((clo 1)%nat) (Nat.max K1 K2)) in HK1q.
  rewrite (real_const_proj (q_pow th 1%nat) (Nat.max K1 K2)) in HK2q.
  rewrite (ln2b_qpow_one th) in HK2q.
  pose proof (ln2b_half_lt ((clo 1)%nat)
                (projT1 (ln2b_line A B 1%nat) (Nat.max K1 K2)) HK1q) as Hlowk0.
  assert (H4 : (((clo 1)%nat) * (1 # 2))%Q == (((clo 1)%nat) * (1 # 4) + ((clo 1)%nat) * (1 # 4))%Q)
    by ring.
  rewrite H4 in Hlowk0.
  assert (Hthq : (((clo 1)%nat) * (1 # 4) + ((clo 1)%nat) * (1 # 4))%Q
                 < (th + ((clo 1)%nat) * (1 # 4))%Q).
  { apply (Qlt_trans (((clo 1)%nat) * (1 # 4) + ((clo 1)%nat) * (1 # 4))%Q
             (projT1 (ln2b_line A B 1%nat) (Nat.max K1 K2))
             (th + ((clo 1)%nat) * (1 # 4))%Q).
    - exact Hlowk0.
    - exact HK2q. }
  assert (Hthq2 : (((clo 1)%nat) * (1 # 4))%Q < th)
    by (apply (lic_qlt_add_r_cancel_r (((clo 1)%nat) * (1 # 4)) th
                 (((clo 1)%nat) * (1 # 4)) Hthq)).
  assert (Hc14 : Qlt 0 (((clo 1)%nat) * (1 # 4))%Q).
  { apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply (Hclo 1%nat).
    - unfold Qlt. cbn. lia. }
  assert (Hth0q : Qlt 0 th) by (apply (Qlt_trans _ _ _ Hc14 Hthq2)).
  (* —— 衰减：显式 n₀ 使 θ^{n₀} < 1/v —— *)
  assert (Hthpos : QltT 0 th) by (apply Qlt_to_QltT; exact Hth0q).
  destruct (ln2b_decay th Hthpos Hth1 v) as [n0 Hdec].
  pose proof (QltT_to_Qlt _ _ Hdec) as Hdecq.
  (* —— 上界肢在 n₀ 的 slack：line_k < 1/v − Δ（Δ := (1/v − θ^{n₀})/2） —— *)
  assert (Hdelta0 : QltT 0 (((1 # v)%Q - q_pow th n0) * (1 # 2))%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply lic_qlt_0_minus. exact Hdecq.
    - unfold Qlt. cbn. lia. }
  destruct (ln2b_le_pt_slack (ln2b_line A B n0) (real_const (q_pow th n0))
             (Hup n0) (((1 # v)%Q - q_pow th n0) * (1 # 2))%Q Hdelta0)
    as [Ku HKu].
  assert (Hmid : (q_pow th n0 + ((1 # v)%Q - q_pow th n0) * (1 # 2))%Q
                 == ((1 # v)%Q - ((1 # v)%Q - q_pow th n0) * (1 # 2))%Q) by ring.
  (* —— 整判定分叉（Z 可判定，零 LPO） —— *)
  destruct (Z.eq_dec (u * A n0) (Z.pos v * B n0)) as [Hhit | Hmiss].
  + (* —— 中支：δ := (clo_{n₀}/2)·|A_{n₀}|⁻¹ —— *)
    assert (HhitQ : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q == 0%Q).
    { rewrite ln2b_line_q. rewrite Hhit.
      unfold Qeq. cbn [Qnum Qden Pos.mul]. lia. }
    assert (HepsN : QltT 0 (((clo n0)%nat) * (1 # 2))%Q).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - apply QltT_to_Qlt. apply (Hclo n0).
      - unfold Qlt. cbn. lia. }
    destruct (ln2b_le_pt_slack (real_const ((clo n0)%nat)) (ln2b_line A B n0)
               (Hlow n0) (((clo n0)%nat) * (1 # 2))%Q HepsN) as [Kl HKl].
    exists (((clo n0)%nat) * (1 # 2) * Qinv (Qabs ((A n0) # 1)%Q))%Q. split.
    * apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      -- apply Qmult_lt_0_compat.
         ++ apply QltT_to_Qlt. apply (Hclo n0).
         ++ unfold Qlt. cbn. lia.
      -- apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (HA n0)).
    * exists Kl. intros k Hk.
      pose proof (HKl k Hk) as HKlq0.
      pose proof (QltT_to_Qlt _ _ HKlq0) as HKlq.
      rewrite (real_const_proj ((clo n0)%nat) k) in HKlq.
      pose proof (ln2b_half_lt ((clo n0)%nat)
                    (projT1 (ln2b_line A B n0) k) HKlq) as Hlowk.
      rewrite ln2b_line_pt in Hlowk.
      rewrite (ln2b_hit_line (A n0) (B n0) ((u # v)%Q) k HhitQ) in Hlowk.
      apply Qle_to_QleT'. apply Qlt_le_weak.
      rewrite (Qabs_Qminus (u # v)%Q (ln2i_x k)).
      apply (ln2b_div_lt_of (((clo n0)%nat) * (1 # 2)) (Qabs ((A n0) # 1)%Q)
               (Qabs ((ln2i_x k - (u # v)%Q)%Q))).
      ++ apply (HA n0).
      ++ exact Hlowk.
  + (* —— 否支：δ := ((1/v − θ^{n₀})/2)·|A_{n₀}|⁻¹ —— *)
    set (w := (u * A n0 - Z.pos v * B n0)%Z).
    assert (Hw0 : w <> 0%Z) by (intro E; apply Hmiss; lia).
    assert (Hw1 : (1 <= Z.abs w)%Z).
    { pose proof (proj2 (Z.abs_pos w) Hw0) as Hwpos. lia. }
    assert (Hbook : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q
                    == ((w # v)%Q))
      by (apply ln2b_line_q).
    exists ((((1 # v)%Q - q_pow th n0) * (1 # 2))
              * Qinv (Qabs ((A n0) # 1)%Q))%Q. split.
    * apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      -- apply QltT_to_Qlt. exact Hdelta0.
      -- apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (HA n0)).
    * exists Ku. intros k Hk.
      pose proof (HKu k Hk) as HKuq0.
      pose proof (QltT_to_Qlt _ _ HKuq0) as HKuq.
      rewrite (real_const_proj (q_pow th n0) k) in HKuq.
      rewrite Hmid in HKuq.
      (* 三角：|A·q − B| ≤ |A|·|q − x_k| + line_k *)
      assert (Hsplit : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q
                       == (((A n0) # 1)%Q * ((u # v)%Q - ln2i_x k)
                           + (((A n0) # 1)%Q * ln2i_x k - ((B n0) # 1)%Q))%Q)
        by ring.
      assert (Htri : Qle (Qabs ((w # v)%Q))
                       (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                        + projT1 (ln2b_line A B n0) k)%Q).
      assert (Hleg1 : Qle (Qabs ((w # v)%Q))
                        (Qabs (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q))).
      { apply qeq_le. apply Qeq_sym. apply Qabs_wd. exact Hbook. }
      assert (Hleg2 : Qle (Qabs (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q))
                       (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                        + projT1 (ln2b_line A B n0) k)%Q).
      { assert (Hleg2a : Qle (Qabs (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q))
                           (Qabs (((A n0) # 1)%Q * ((u # v)%Q - ln2i_x k)
                                   + (((A n0) # 1)%Q * ln2i_x k - ((B n0) # 1)%Q)))).
        { apply qeq_le. apply Qabs_wd. exact Hsplit. }
        pose proof (Qabs_triangle (((A n0) # 1)%Q * ((u # v)%Q - ln2i_x k))
                      (((A n0) # 1)%Q * ln2i_x k - ((B n0) # 1)%Q)) as HT.
        assert (HE : (Qabs (((A n0) # 1)%Q * ((u # v)%Q - ln2i_x k))
                      + Qabs (((A n0) # 1)%Q * ln2i_x k - ((B n0) # 1)%Q))%Q
                     == (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                         + projT1 (ln2b_line A B n0) k)%Q).
        { rewrite Qabs_Qmult. rewrite <- (ln2b_line_pt A B n0 k). reflexivity. }
        pose proof (Qle_trans _ _ _ HT (qeq_le _ _ HE)) as Hcomb.
        exact (Qle_trans _ _ _ Hleg2a Hcomb).
      }
      exact (Qle_trans _ _ _ Hleg1 Hleg2).
      (* 1/v ≤ |w#v| ≤ |A|·|q−x_k| + line_k < |A|·|q−x_k| + (1/v − Δ) ⟹ Δ < |A|·|q−x_k| *)
      assert (Hge : Qle ((1 # v)%Q) (Qabs ((w # v)%Q))).
      { unfold Qle, Qabs. cbn [Qnum Qden]. nia. }
      pose proof (Qle_trans _ _ _ Hge Htri) as Hchain1.
      assert (Hchain2 : Qlt (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - ln2i_x k)%Q)
                              + projT1 (ln2b_line A B n0) k)%Q
                              (Qabs ((A n0) # 1)%Q
                               * Qabs (((u # v)%Q - ln2i_x k)%Q)
                               + ((1 # v)%Q - ((1 # v)%Q - q_pow th n0)
                                   * (1 # 2)))%Q)
        by (apply (lic_qlt_add_l (Qabs ((A n0) # 1)%Q
                                   * Qabs (((u # v)%Q - ln2i_x k)%Q)));
            exact HKuq).
      assert (Hpre : Qlt ((1 # v)%Q)
                       (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                        + ((1 # v)%Q - ((1 # v)%Q - q_pow th n0) * (1 # 2)))%Q)
        by (apply (Qle_lt_trans (1 # v)%Q
                    (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                     + projT1 (ln2b_line A B n0) k)%Q); assumption).
      assert (Hchain : Qlt (((1 # v)%Q - q_pow th n0) * (1 # 2))
                         (Qabs ((A n0) # 1)%Q
                          * Qabs (((u # v)%Q - ln2i_x k)%Q))).
      { pose proof (proj1 (Qlt_minus_iff (1 # v)%Q
                             (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - ln2i_x k)%Q)
                              + ((1 # v)%Q - ((1 # v)%Q - q_pow th n0) * (1 # 2)))%Q)
                     Hpre) as Hm.
        (* 中间断言 Hm : 0 < (P + W) − 1/v，其中 W := 1/v − Δ ⟹ 0 < P − Δ
           （恒等式 Hring：P + W − 1/v == P − Δ，Δ := ((1/v) − θ^{n₀})·(1/2)）
           注记：右端必须写成 P − Δ 方为恒等式；写成 P − (1/v − Δ) 则
            不成立，ring 判拒绝是正确行为。 *)
        assert (Hring : ((Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                           + ((1 # v)%Q - ((1 # v)%Q - q_pow th n0) * (1 # 2)))
                          - (1 # v)%Q)%Q
                        == (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)
                            - ((1 # v)%Q - q_pow th n0) * (1 # 2))%Q)
          by ring.
        rewrite Hring in Hm.
        (* Δ + (P − Δ) == P；0 < P − Δ ⟹ Δ < P *)
        assert (Hring2 : ((((1 # v)%Q - q_pow th n0) * (1 # 2))
                            + (Qabs ((A n0) # 1)%Q
                               * Qabs (((u # v)%Q - ln2i_x k)%Q)
                               - ((1 # v)%Q - q_pow th n0) * (1 # 2)))%Q
                         == (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q)))
          by ring.
        apply (lic_qlt_comp_r
                 _ (Qabs ((A n0) # 1)%Q * Qabs (((u # v)%Q - ln2i_x k)%Q))
                 (((1 # v)%Q - q_pow th n0) * (1 # 2))
                 Hring2 (lic_qlt_lt_add_r _ _ Hm)).
      }
      apply Qle_to_QleT'. apply Qlt_le_weak.
      apply (ln2b_div_lt_of (((1 # v)%Q - q_pow th n0) * (1 # 2))
               (Qabs ((A n0) # 1)%Q)
               (Qabs (((u # v)%Q - ln2i_x k)%Q))).
      -- apply (HA n0).
      -- exact Hchain.
Qed.

(* ============================================================ *)
(* §5 ln2b_escape_of_supply：supply -> ln2i_escape_spec（条件形收口） *)
(* ============================================================ *)

(* 逃逸主件（与 T97 §1.2 草案的构造差异：指标不取 2v+4，不用
   ln2i_pow_ge 与反三角路径）：以 vanish 与 δ 点式两条件直接收口——
   ln2i_vanish 于 eps:=δ 给显式 N（n≥N ⟹ ln2i_e n < δ），与 δ 提取件的
   终归点式肢（δ ≤ |q−x_k|，k≥K）在 m := S(max K N) 处合取：
   ln2i_e m < δ ≤ |q−x_m|。指标 m 全显式，零 LPO。 *)
Theorem ln2b_escape_of_supply : forall (Hs : ln2i_pade_supply),
  ln2i_escape_spec.
Proof.
  intros Hs q.
  destruct (ln2b_delta_of_supply Hs q) as [d [Hd0 [K HK]]].
  destruct (ln2i_vanish d Hd0) as [N HN].
  exists (Datatypes.S (Nat.max K N)). split.
  - lia.
  - assert (Hwin : QltT (ln2i_e (Datatypes.S (Nat.max K N))) d).
    { apply (HN (Datatypes.S (Nat.max K N))). lia. }
    pose proof (HK (Datatypes.S (Nat.max K N)) ltac:(lia)) as Hgap.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (ln2i_e (Datatypes.S (Nat.max K N))) d
            (Qabs ((q - ln2i_x (Datatypes.S (Nat.max K N)))%Q))).
    + apply QltT_to_Qlt. exact Hwin.
    + apply QleT'_to_Qle. exact Hgap.
Qed.

(* ============================================================ *)
(* §6 ln2b_irrational_from_supply：supply 条件下应用 lic_irrational_criterion *)
(* ============================================================ *)

(* 主件：语句面为 ln2i_irrational_criterion_cond 的结论面（X 取
   ln2b_X 的展开形式），逃逸规格由 ln2b_escape_of_supply 供给，
   直接应用母定理 lic_irrational_criterion。 *)
Theorem ln2b_irrational_from_supply : forall (Hs : ln2i_pade_supply) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hs q.
  exact (lic_irrational_criterion ln2i_x ln2i_e ln2i_tail           (ln2b_escape_of_supply Hs) ln2i_vanish q).
Qed.

(* ============================================================ *)
(* §7 反例见证：平凡三元组（排除伪 supply） *)
(* ============================================================ *)

(* 平凡三元组 A:=1, B:=0, clo:=0：供给型五个组成条件之 ③(0<clo)
   缺席，故非合法 supply。反例以全 Set 面实证两点：
   ① q:=0（即 u:=0,v:=1，0·A₀ == 1·B₀）处中支判据成立——Z.eq_dec
      分叉取左支，δ 提取件取中支；
   ② 中支 δ 公式 (clo/2)·|A|⁻¹ 输出 0（QleT' 面 ≤0）——中支正性
      无处可得：其必须由载体条件 clo>0 供给，伪 supply 由此排除。 *)
Definition ln2b_tri_A : nat -> Z := fun _ => 1%Z.
Definition ln2b_tri_B : nat -> Z := fun _ => 0%Z.
Definition ln2b_tri_clo : nat -> Q := fun _ => 0%Q.

Lemma ln2b_supply_trivial_hit :
  And (QeqT ((((ln2b_tri_A 0%nat) # 1)%Q * 0%Q
               - ((ln2b_tri_B 0%nat) # 1)%Q)%Q) 0%Q)
      (QleT' (((ln2b_tri_clo 0%nat) * (1 # 2)
                * Qinv (Qabs (((ln2b_tri_A 0%nat) # 1)%Q)))%Q) 0%Q).
Proof.
  split.
  - apply qeq_imp_qeqT. unfold ln2b_tri_A, ln2b_tri_B. reflexivity.
  - apply qeq_leT'. unfold ln2b_tri_clo. reflexivity.
Qed.

(* ============================================================ *)
(* §8 提取与假设审计 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction ln2b_irrational_from_supply ln2b_escape_of_supply
  ln2b_delta_of_supply ln2b_supply_trivial_hit ln2i_pade_supply
  ln2b_X ln2b_line ln2b_le_pt_slack ln2b_decay.
Print Assumptions ln2b_irrational_from_supply.
Print Assumptions ln2b_escape_of_supply.
Print Assumptions ln2b_delta_of_supply.
Print Assumptions ln2b_supply_trivial_hit.
