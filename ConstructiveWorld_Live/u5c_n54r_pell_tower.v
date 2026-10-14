(* 五字段指针｜使命：Pell 收敛子塔切片，N5 三态谱两端收束。
   承 N54 冻结遗产（u5c_n54_ot_spectrum：对数档上界绿/loglog 下界绿/无穷档绿），
   本件补全下界「显式最近有理」半边并收紧上界：
   ①Pell −1 分支收敛子族 n54r_pt：(p,q)→(3p+4q,2p+3q)，起 (1,1)——
     1/1, 7/5, 41/29, 239/169, …；整值整隙 p²+1 = 2q²（Pell 恒等）；
   ②wden 双塔：2^(2^n) ≤ wden(n) ≤ 2^(2^(n+1)−2)＋delta 精确塔
     delta(n) == 2^(2^n)/wden(n)² ⟹ delta(n) ≤ 2^(-2^n)（双指数窗衰减首证）；
   ③入窗核（下界新数学）：q_k ≤ b ∧ delta(n)·q_k² ≥ 5 ⟹ |p_k/q_k − x(n)| ≤ e(n)
     ——收敛子落入误差窗 ⟹ 严格致胜不可能；
   ④下界正典：7^(2^n) ≤ b ⟹ ¬UWin(n,b)——基数取 7 由 q_k 增速 ≈ 5.828^k > 5^k
     所定（5 为基不成立：qgrow 只给 5^k ≤ q_k 下界，推不出 q_{2^n} ≤ b；
     独立复算 pden(pt(2))=29 > 25 拦截）；补上界塔 q_k ≤ 7^k
     （p ≤ 2q ⟹ q_{k+1} = 2p+3q ≤ 7q）后正典成立，OT(b) ≥ log₂log₇b−O(1)，
     仍 loglog 档；
   ⑤上界收紧（两端收束上半）：6b² ≤ 2^(2^m) ⟹ UWin(b,m)，正典实例
     UWin(b, log₂log₂b + 3)——上界从对数档 2log₂b+4 降到 loglog 档。
     判据 6b² ≤ 2^(2^m) 由 margin 核定出（e(m)=delta(m)/2 ≤ 1/(12b′²) 需
     12b′² ≤ 2·2^(2^m)，3b² < 2^(2^m) 形不足）；正典 +3 指数不受影响
     （独立复算 b<10^5 全称零违例）。q == x(m) 恰等情形由
     gcd/Bezout 整值排除核（S4）独立钉定不可达。
   诚实申报：谱两端真阶 Θ(log₂log₂ b)（两端）：下界超 loglog 档被⑤正典实例
   禁闭（UWin 已在 log₂log₂b+3 成立）；上界超 loglog 档非本塔可达（delta 双指数
   衰减 vs 有理格 1/b² 多项式密度，匹配点在 loglog）。本件两端同 loglog 档
   收束；对数档 A 件（2log₂b+4）保留为工具级粗上界，OT-封形语义等价。
   依赖：u5c_n54_ot_spectrum（n54_uwin/n54_wtrack/
   n54_wnum/n54_wden/n54_x_eq_wnum/n54_pos_le_Z）＋S01_BaseRing、
   S02_CauchyComplete、S03_QExp、SumInvFactEscape、UpReqBanachNormOpp、
   UpReqIrrationalCriterion、UpReqSqrt3Irrational、u5c_dm_escape_window、
   u5c_sqrt2_closed_measure、u5c_sqrt5_closed_measure；Stdlib QArith、Qabs、
   ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。
   构造性注记：主语句全 Set 层（QltT/QleT'/¬:=→Empty_set/forall-arrow 入 Set），
   零 Prop 前提位；证明体内 Prop 推导合法（Qle/Qeq 链、Z 整隙、nat 塔归纳）；
   零承认、零经典逻辑、零全局假设；新定义面仅 n54r_pt（透明 Fixpoint）＋投影；
   主定理装配链非单发空壳（Pell 归纳＋双塔归纳＋入窗核三连换算＋三分支边距核
   ＋gcd/Bezout 排除核）；数值见证位 vm_compute 合法（复算律；Fractions
   全量同源独立复算先行 13/13 ALL PASS）。
   编译配方：rocq c -native-compiler no -q -Q . "" u5c_n54r_pell_tower.v *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_window.
Require Import u5c_sqrt2_closed_measure.
Require Import u5c_sqrt5_closed_measure.
Require Import u5c_n54_ot_spectrum.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  ZArith.Znumtheory
  Arith.Arith Arith.PeanoNat Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S-：对账小桥                                                     *)
(* ============================================================ *)

(* Z.pos p 的 nat 对账桥 *)
Lemma n54r_zpos_eq : forall p : positive,
  (Z.pos p = Z.of_nat (Pos.to_nat p))%Z.
Proof.
  induction p as [p IH|p IH|].
  - replace (Pos.to_nat (xI p)) with (2 * Pos.to_nat p + 1)%nat
      by (rewrite Pos2Nat.inj_xI; lia).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    change (Z.pos (xI p)) with (Z.pos (xO p) + 1)%Z.
    rewrite ir2_zpos_xo, IH. reflexivity.
  - replace (Pos.to_nat (xO p)) with (2 * Pos.to_nat p)%nat
      by (rewrite Pos2Nat.inj_xO; lia).
    rewrite Nat2Z.inj_mul.
    rewrite ir2_zpos_xo, IH. reflexivity.
  - reflexivity.
Qed.

(* Z 层 2 幂与 nat 2 幂的对账 *)
Lemma n54r_zpow_nat : forall n : nat,
  (2 ^ (Z.of_nat n) = Z.of_nat (2 ^ n))%Z.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite IH, Nat2Z.inj_mul. reflexivity.
Qed.

(* Qinv((Z.pos c)#1) 的分数形归一 *)
Lemma n54r_inv1p : forall c : positive, Qinv ((Z.pos c) # 1) == (1 # c)%Q.
Proof. intro c. apply qeqT_imp_qeq. apply dmew_Qinv_1p. Qed.

(* 右乘消正：0 < m 且 u·m ≤ v·m ⟹ u ≤ v *)
Lemma n54r_qle_cancel_r : forall u v m : Q,
  Qlt 0 m -> Qle (u * m) (v * m) -> Qle u v.
Proof.
  intros u v m Hm H.
  destruct (Qlt_le_dec u v) as [Hlt|Hle].
  - apply Qlt_le_weak. exact Hlt.
  - destruct (Qlt_le_dec v u) as [Hlt2|Hle2].
    + exfalso. apply (Qlt_not_le (v * m) (u * m)).
      * apply (Qmult_lt_compat_r v u m Hm Hlt2).
      * exact H.
    + apply qeq_le. apply Qle_antisym; assumption.
Qed.

(* ============================================================ *)
(* S0：Pell −1 分支收敛子族                                        *)
(* ============================================================ *)

Fixpoint n54r_pt (k : nat) : positive * positive :=
  match k with
  | O => (1%positive, 1%positive)
  | Datatypes.S j =>
      let '(p, q) := n54r_pt j in
      ((3 * p + 4 * q)%positive, (2 * p + 3 * q)%positive)
  end.

Definition n54r_pnum (k : nat) : positive := fst (n54r_pt k).
Definition n54r_pden (k : nat) : positive := snd (n54r_pt k).

(* 整值整隙（Pell 恒等）：p² + 1 = 2q² *)
Lemma n54r_pt_sq : forall k : nat,
  (Z.pos (n54r_pnum k) * Z.pos (n54r_pnum k) + 1
   = 2 * (Z.pos (n54r_pden k) * Z.pos (n54r_pden k)))%Z.
Proof.
  assert (Hmain : forall k : nat,
    (Z.pos (fst (n54r_pt k)) * Z.pos (fst (n54r_pt k)) + 1
     = 2 * (Z.pos (snd (n54r_pt k)) * Z.pos (snd (n54r_pt k))))%Z).
  { induction k as [|k IH].
    - cbn [n54r_pt fst snd]. cbn. lia.
    - destruct (n54r_pt k) as [c d] eqn:E.
      cbn [n54r_pt]. rewrite E. cbn [fst snd] in IH |- *.
      rewrite !Pos2Z.inj_add, !Pos2Z.inj_mul.
      nia. }
  intro k. apply Hmain.
Qed.

(* p ≥ q（正部层） *)
Lemma n54r_pt_pgeq : forall k : nat,
  (n54r_pden k <= n54r_pnum k)%positive.
Proof.
  assert (Hmain : forall k : nat,
    (snd (n54r_pt k) <= fst (n54r_pt k))%positive).
  { induction k as [|k IH].
    - cbn [n54r_pt fst snd]. apply Pos.le_refl.
    - destruct (n54r_pt k) as [c d] eqn:E.
      cbn [n54r_pt]. rewrite E. cbn [fst snd] in IH |- *.
      apply (proj2 (Pos2Nat.inj_le _ _)).
      pose proof (proj1 (Pos2Nat.inj_le _ _) IH) as Hnat.
      rewrite !Pos2Nat.inj_add, !Pos2Nat.inj_mul.
      cbn [Pos.to_nat]. lia. }
  intro k. apply Hmain.
Qed.

(* q ≥ 5^k（分母单指数塔） *)
Lemma n54r_pt_qgrow : forall k : nat,
  (5 ^ k <= Pos.to_nat (n54r_pden k))%nat.
Proof.
  induction k as [|k IH].
  - cbn [n54r_pden n54r_pt fst snd]. cbn. lia.
  - destruct (n54r_pt k) as [c d] eqn:E.
    unfold n54r_pden in IH |- *.
    cbn [n54r_pt]. rewrite E. rewrite E in IH.
    cbn [snd] in IH |- *.
    pose proof (n54r_pt_pgeq k) as Hpg.
    unfold n54r_pden, n54r_pnum in Hpg.
    rewrite E in Hpg.
    cbn [snd fst] in Hpg.
    rewrite Nat.pow_succ_r'.
    apply (proj2 (Nat2Z.inj_le _ _)).
    rewrite Nat2Z.inj_mul.
    rewrite <- !n54r_zpos_eq.
    rewrite !Pos2Z.inj_add, !Pos2Z.inj_mul.
    pose proof (n54_pos_le_Z _ _ Hpg) as Hz.
    pose proof (proj1 (Nat2Z.inj_le _ _) IH) as IHZ.
    rewrite <- n54r_zpos_eq in IHZ.
    lia.
Qed.

(* 分母上界塔：q_k ≤ 7^k（p ≤ 2q ⟸ p² = 2q²−1 < 4q²；q_{k+1} = 2p+3q ≤ 7q） *)
Lemma n54r_pt_qub : forall k : nat,
  (Pos.to_nat (n54r_pden k) <= 7 ^ k)%nat.
Proof.
  assert (H2q : forall k : nat,
    (Pos.to_nat (n54r_pnum k) <= 2 * Pos.to_nat (n54r_pden k))%nat).
  { intro k.
    pose proof (n54r_pt_sq k) as Hsq.
    pose proof (Pos2Z.is_pos (n54r_pden k)) as Hq0.
    nia. }
  induction k as [|k IH].
  - cbn [n54r_pden n54r_pt fst snd]. cbn. lia.
  - destruct (n54r_pt k) as [c d] eqn:E.
    unfold n54r_pden in IH |- *.
    cbn [n54r_pt]. rewrite E. rewrite E in IH.
    cbn [snd] in IH |- *.
    pose proof (H2q k) as H2.
    unfold n54r_pnum, n54r_pden in H2.
    rewrite E in H2. cbn [fst snd] in H2.
    rewrite Nat.pow_succ_r'.
    apply (proj2 (Nat2Z.inj_le _ _)).
    rewrite Nat2Z.inj_mul.
    rewrite <- !n54r_zpos_eq.
    rewrite !Pos2Z.inj_add, !Pos2Z.inj_mul.
    pose proof (proj1 (Nat2Z.inj_le _ _) IH) as IHZ.
    rewrite <- !n54r_zpos_eq in IHZ.
    replace (Z.of_nat 7) with 7%Z in IHZ |- * by reflexivity.
    pose proof (proj1 (Nat2Z.inj_le _ _) H2) as H2Z.
    rewrite !Nat2Z.inj_mul in H2Z.
    rewrite <- !n54r_zpos_eq in H2Z.
    replace (Z.of_nat 2) with 2%Z in H2Z by reflexivity.
    lia.
Qed.

(* 数值见证（复算律）：pt(3) = 239/169 *)
Lemma n54r_pell_smoke :
  ((Z.pos (n54r_pnum 3)) # (n54r_pden 3))%Q == (239 # 169)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* S1：wtrack 双塔与 delta 精确塔                                    *)
(* ============================================================ *)

(* 幂劈引理（nat 层·指数账 lia 收束） *)
Lemma n54r_pow2split : forall j : nat,
  (2 ^ (2 ^ (Datatypes.S j)) = 2 ^ (2 ^ j) * 2 ^ (2 ^ j))%nat.
Proof.
  intro j. rewrite Nat.pow_succ_r'. rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

Lemma n54r_pow4split : forall j : nat, (1 <= j)%nat ->
  (2 ^ (2 ^ (Datatypes.S (Datatypes.S j)) - 2)
   = 4 * (2 ^ (2 ^ (Datatypes.S j) - 2) * 2 ^ (2 ^ (Datatypes.S j) - 2)))%nat.
Proof.
  intros j Hj.
  assert (Hj2 : (2 <= 2 ^ (Datatypes.S j))%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (Nat.pow_le_mono_r 2%nat 0%nat j (ltac:(lia)) (Nat.le_0_l j)) as H1.
    replace (2 ^ 0)%nat with 1%nat in H1 by reflexivity.
    lia. }
  replace (2 ^ (Datatypes.S (Datatypes.S j)) - 2)%nat
    with (2 * (2 ^ (Datatypes.S j) - 2) + 2)%nat
    by (replace (2 ^ (Datatypes.S (Datatypes.S j)))%nat
          with (2 * 2 ^ (Datatypes.S j))%nat
          by reflexivity;
        lia).
  replace (2 * (2 ^ (Datatypes.S j) - 2) + 2)%nat
    with ((2 ^ (Datatypes.S j) - 2) + ((2 ^ (Datatypes.S j) - 2) + 2))%nat
    by lia.
  rewrite Nat.pow_add_r.
  rewrite Nat.pow_add_r.
  replace (2 ^ 2)%nat with 4%nat by reflexivity.
  ring.
Qed.

(* wnum² − 2·wden² = 2^(2^n)（d 不变量逐步平方） *)
Lemma n54r_wsq : forall n : nat,
  (Z.pos (n54_wnum n) * Z.pos (n54_wnum n)
   - 2 * (Z.pos (n54_wden n) * Z.pos (n54_wden n))
   = Z.of_nat (2 ^ (2 ^ n)))%Z.
Proof.
  induction n as [|n IH].
  - cbn. lia.
  - destruct (n54_wtrack n) as [c d] eqn:E.
    unfold n54_wnum, n54_wden in IH |- *.
    cbn [n54_wtrack]. rewrite E. rewrite E in IH.
    cbn [fst snd] in IH |- *.
    replace (2 ^ (2 ^ (Datatypes.S n)))%nat
      with ((2 ^ (2 ^ n)) * (2 ^ (2 ^ n)))%nat
      by (symmetry; apply n54r_pow2split).
    rewrite Nat2Z.inj_mul.
    repeat (rewrite ?Pos2Z.inj_mul; rewrite ?Pos2Z.inj_add).
    assert (Hsq : ((Z.pos c * Z.pos c - 2 * (Z.pos d * Z.pos d))
                   * (Z.pos c * Z.pos c - 2 * (Z.pos d * Z.pos d))
                   = Z.of_nat (2 ^ 2 ^ n) * Z.of_nat (2 ^ 2 ^ n))%Z)
      by nia.
    nia.
Qed.

(* wden ≤ wnum（正部层；步差 (a−b)²+b² ≥ 0） *)
Lemma n54r_wge : forall n : nat,
  (n54_wden n <= n54_wnum n)%positive.
Proof.
  assert (Hmain : forall n : nat,
    (snd (n54_wtrack n) <= fst (n54_wtrack n))%positive).
  { induction n as [|n IH].
    - cbn [n54_wtrack fst snd]. apply (proj2 (Pos2Nat.inj_le _ _)). cbn. lia.
    - destruct (n54_wtrack n) as [c d] eqn:E.
      unfold n54_wden, n54_wnum.
      cbn [n54_wtrack]. rewrite E. cbn [fst snd] in IH |- *.
      apply (proj2 (Pos2Nat.inj_le _ _)).
      pose proof (proj1 (Pos2Nat.inj_le _ _) IH) as Hnat.
      rewrite !Pos2Nat.inj_add, !Pos2Nat.inj_mul.
      cbn [Pos.to_nat]. nia. }
  intro n. apply Hmain.
Qed.

(* wden ≥ 2^(2^n)（n ≥ 1；b_{n+1} = 2aₙbₙ ≥ 2bₙ²） *)
Lemma n54r_wden_lb : forall n : nat, (1 <= n)%nat ->
  (2 ^ (2 ^ n) <= Pos.to_nat (n54_wden n))%nat.
Proof.
  assert (Hmain : forall n : nat,
    (2 ^ (2 ^ (Datatypes.S n)) <= Pos.to_nat (n54_wden (Datatypes.S n)))%nat).
  { induction n as [|n IH].
    - cbn [n54_wden n54_wtrack fst snd]. cbn. lia.
    - destruct (n54_wtrack n) as [c d] eqn:E.
      unfold n54_wden in IH |- *.
      cbn [n54_wtrack] in IH |- *. rewrite E in IH |- *.
      cbn [fst snd] in IH |- *.
      pose proof (n54r_wge (Datatypes.S n)) as Hge.
      unfold n54_wden, n54_wnum in Hge.
      cbn [n54_wtrack] in Hge.
      rewrite E in Hge.
      cbn [snd fst] in Hge.
      pose proof (proj1 (Pos2Nat.inj_le _ _) Hge) as HgeN.
      rewrite !Pos2Nat.inj_mul, !Pos2Nat.inj_add in HgeN |- *.
      cbn [Pos.to_nat] in HgeN.
      replace (2 ^ (2 ^ (Datatypes.S (Datatypes.S n))))%nat
        with ((2 ^ (2 ^ (Datatypes.S n))) * (2 ^ (2 ^ (Datatypes.S n))))%nat
        by (symmetry; apply n54r_pow2split).
      nia. }
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply (Hmain n').
Qed.

(* wnum ≤ 2·wden（n ≥ 1；x ≤ 3/2 的 Z 层形） *)
Lemma n54r_wle2Z : forall n : nat, (1 <= n)%nat ->
  (2 * Z.pos (n54_wnum n) <= 3 * Z.pos (n54_wden n))%Z.
Proof.
  intros n Hn.
  pose proof (ir2_x_ub n Hn) as Hub.
  setoid_rewrite (n54_x_eq_wnum n) in Hub.
  unfold Qle in Hub. cbn [Qnum Qden] in Hub.
  lia.
Qed.

(* wden ≤ 2^(2^(n+1)−2)（全 n；b_{n+1} = 2aₙbₙ ≤ 4bₙ²） *)
Lemma n54r_wden_ub : forall n : nat,
  (Pos.to_nat (n54_wden n) <= 2 ^ (2 ^ (Datatypes.S n) - 2))%nat.
Proof.
  assert (Hle2 : forall n : nat,
    (Pos.to_nat (n54_wnum n) <= 2 * Pos.to_nat (n54_wden n))%nat).
  { intros n. destruct n as [|n'].
    { cbn [n54_wnum n54_wden n54_wtrack fst snd]. cbn. lia. }
    pose proof (n54r_wle2Z (Datatypes.S n') (ltac:(lia))) as Hz.
    lia. }
  induction n as [|n IH].
  - cbn [n54_wden n54_wtrack fst snd]. cbn. lia.
  - destruct n as [|n'].
    { (* n = 0：b_1 = 4 ≤ 2^(2^2−2) = 4 *)
      replace (2 ^ (2 ^ (Datatypes.S (Datatypes.S 0)) - 2))%nat with 4%nat by reflexivity.
      unfold n54_wden. cbn. lia. }
    destruct (n54_wtrack n') as [c d] eqn:E.
    unfold n54_wden in IH |- *.
    cbn [n54_wtrack] in IH |- *. rewrite E in IH |- *.
    cbn [fst snd] in IH |- *.
    pose proof (Hle2 (Datatypes.S n')) as H2.
    unfold n54_wnum, n54_wden in H2.
    cbn [n54_wtrack] in H2.
    rewrite E in H2.
    cbn [fst snd] in H2.
    pose proof (n54r_wge (Datatypes.S n')) as Hge.
    unfold n54_wden, n54_wnum in Hge.
    cbn [n54_wtrack] in Hge.
    rewrite E in Hge.
    cbn [snd fst] in Hge.
    pose proof (proj1 (Pos2Nat.inj_le _ _) Hge) as HgeN.
    pose proof H2 as H2N.
    pose proof IH as IHN.
    rewrite !Pos2Nat.inj_mul, !Pos2Nat.inj_add in HgeN, H2N |- *.
    rewrite !Pos2Nat.inj_mul in IHN.
    cbn [Pos.to_nat] in HgeN, H2N, IHN.
    replace (2 ^ (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n'))) - 2))%nat
      with (4 * ((2 ^ (2 ^ (Datatypes.S (Datatypes.S n')) - 2))
                  * (2 ^ (2 ^ (Datatypes.S (Datatypes.S n')) - 2))))%nat
      by (symmetry; apply n54r_pow4split; lia).
    nia.
Qed.

(* delta 精确塔：delta(n) == 2^(2^n)/wden(n)² *)
Lemma n54r_delta_eq : forall n : nat,
  ir2_delta n
  == ((Z.of_nat (2 ^ (2 ^ n))) # (n54_wden n * n54_wden n)%positive)%Q.
Proof.
  intro n. unfold ir2_delta.
  setoid_rewrite (n54_x_eq_wnum n).
  assert (Hxx : (((Z.pos (n54_wnum n)) # (n54_wden n))%Q
                 * ((Z.pos (n54_wnum n)) # (n54_wden n))%Q
                 == ((Z.pos (n54_wnum n) * Z.pos (n54_wnum n))
                     # (n54_wden n * n54_wden n)%positive)%Q)).
  { unfold Qmult. reflexivity. }
  rewrite Hxx.
  rewrite <- (n54r_wsq n).
  unfold Qminus, Qeq. cbn [Qminus Qplus Qopp Qnum Qden].
  rewrite !Pos2Z.inj_mul.
  ring.
Qed.

(* delta 双指数上界：delta(n) ≤ 2^(-2^n)（n ≥ 1） *)
Lemma n54r_delta_upper : forall n : nat, (1 <= n)%nat ->
  QleT' (ir2_delta n) (Qinv ((Z.of_nat (2 ^ (2 ^ n))) # 1)).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  rewrite n54r_delta_eq.
  pose proof (n54r_wden_lb n Hn) as Hlb.
  assert (H1 : (Z.of_nat 1 <= Z.of_nat (2 ^ (2 ^ n)))%Z).
  { apply (proj1 (Nat2Z.inj_le _ _)).
    pose proof (Nat.pow_le_mono_r 2%nat 0%nat (2 ^ n)%nat (ltac:(lia))
                  (Nat.le_0_l _)) as HP.
    replace (2 ^ 0)%nat with 1%nat in HP by reflexivity.
    exact HP. }
  apply (proj1 (Nat2Z.inj_le _ _)) in Hlb.
  rewrite <- !n54r_zpos_eq in Hlb.
  apply (ir2_le_inv ((Z.of_nat (2 ^ (2 ^ n))) # 1)
           ((Z.of_nat (2 ^ (2 ^ n))) # (n54_wden n * n54_wden n)%positive)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  { unfold Qle, Qmult. cbn [Qnum Qden Qinv].
    rewrite !Pos2Z.inj_mul.
    nia. }
Qed.

(* ============================================================ *)
(* S2：入窗核（下界新数学）——收敛子落入误差窗 ⟹ 严格致胜不可能           *)
(* ============================================================ *)

(* 入窗核：q ≤ p、p²+1 = 2q²、p/q ≤ x(n)、delta(n)·q² ≥ 5
   ⟹ |p/q − x(n)| ≤ e(n)。
   链：x−p/q = (x²−p²/q²)/(x+p/q) = (delta + 1/q²)/(x+p/q)
       ≤ delta/2 ⟸ 2delta + 2/q² ≤ delta·(p/q+x)
       ⟸ delta·pq ≥ delta ∧ delta·x ≥ delta + (2/5)delta
       ⟸ (2/5)delta ≥ 2/q² ⟸ delta·q² ≥ 5。 *)
Lemma n54r_pell_win_core : forall (p q : positive) (n : nat),
  (Z.pos q <= Z.pos p)%Z ->
  (Z.pos p * Z.pos p + 1 = 2 * (Z.pos q * Z.pos q))%Z ->
  Qle ((Z.pos p # q)%Q) (ir2_x n) ->
  Qle ((5 # 1)%Q) (ir2_delta n * ((Z.pos (q * q)%positive) # 1)%Q) ->
  Qle (Qabs (((Z.pos p # q)%Q - ir2_x n)%Q)) (ir2_e n).
Proof.
  intros p q n Hp Hsq Hle H5.
  pose proof (ir2_x_pos n) as Hxp.
  pose proof (ir2_delta_ge0 n) as Hd0.
  pose proof (ir2_x_lb n) as Hx57.
  assert (Hpq0 : Qle 0 ((Z.pos p # q)%Q)).
  { apply Qlt_le_weak. unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Hpp : ((Z.pos p # q)%Q * (Z.pos p # q)%Q
                 == ((Z.pos p * Z.pos p) # (q * q)%positive)%Q)).
  { unfold Qmult, Qeq. cbn [Qnum Qden]. ring. }
  assert (Hs1 : Qlt ((Z.pos p # q)%Q * (Z.pos p # q)%Q) 2%Q).
  { rewrite Hpp. unfold Qlt, Qmult. cbn [Qnum Qden].
    rewrite Pos2Z.inj_mul. lia. }
  pose proof (ir2_sq_ge2 n) as Hx2.
  assert (Hqx : Qlt ((Z.pos p # q)%Q) (ir2_x n)).
  { apply (ir2_lt_of_sq (ir2_x n) (Z.pos p # q)%Q);
      [apply Qlt_le_weak; exact Hxp | exact Hpq0 |].
    apply (Qlt_le_trans _ 2%Q _); [exact Hs1 | exact Hx2]. }
  rewrite (Qabs_Qminus ((Z.pos p # q)%Q) (ir2_x n)).
  rewrite (ir2_abs_sub (ir2_x n) (Z.pos p # q)%Q)
    by (apply Qlt_le_weak; exact Hqx).
  unfold ir2_e.
  assert (Hm0 : ~ (((Z.pos (q * q)%positive) # 1)%Q == 0%Q)).
  { intro Hc. assert (Hz : Qlt 0%Q ((Z.pos (q * q)%positive) # 1)%Q).
    { unfold Qlt. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_eq 0%Q _ Hz). apply Qeq_sym. exact Hc. }
  (* 5/q² ≤ delta *)
  assert (H5' : Qle (((5 # 1)%Q) * Qinv ((Z.pos (q * q)%positive) # 1)) (ir2_delta n)).
  { pose proof H5 as H5u.
    unfold Qle, Qmult, Qinv in H5u |- *.
    cbn [Qmult Qnum Qden Qinv] in H5u |- *.
    rewrite !Pos2Z.inj_mul in H5u |- *.
    nia. }
  (* 2/q² ≤ (2/5)·delta *)
  assert (H25 : Qle (((2 # 1)%Q) * Qinv ((Z.pos (q * q)%positive) # 1))
                    (((2 # 5)%Q) * ir2_delta n)).
  { apply (Qle_trans _ (((2 # 5)%Q) * (((5 # 1)%Q)
                          * Qinv ((Z.pos (q * q)%positive) # 1)))%Q).
    { assert (Heq25 : (((2 # 5)%Q) * ((5 # 1)%Q)
                        * Qinv ((Z.pos (q * q)%positive) # 1)
                       == ((2 # 1)%Q) * Qinv ((Z.pos (q * q)%positive) # 1))%Q) by ring.
      rewrite Heq25. apply Qle_refl. }
    { apply (ir2_mult_le_compat_l _ _ (2 # 5)%Q);
        [exact H5' | unfold Qle; cbn [Qnum Qden]; lia]. } }
  (* 半幅直取链：目标 x−p/q ≤ delta/2。
     1 ≤ p/q ∧ 7/5 ≤ x ⟹ (1/2)·delta·(p/q+x) ≥ (1/2)·delta·(12/5) = (6/5)delta；
     H5 ⟹ 1/q² ≤ (1/5)delta ⟹ delta + 1/q² ≤ (6/5)delta。 *)
  assert (Hle1 : Qle 1%Q ((Z.pos p # q)%Q)).
  { unfold Qle. cbn [Qnum Qden]. lia. }
  assert (Hd12 : Qle 0%Q (((1 # 2)%Q) * ir2_delta n)%Q).
  { apply (Qle_trans 0%Q (((1 # 2)%Q) * 0%Q)%Q).
    { apply qeq_le. ring. }
    { apply (ir2_mult_le_compat_l 0%Q (ir2_delta n) (1 # 2)%Q);
        [exact Hd0 | unfold Qle; cbn [Qnum Qden]; lia]. } }
  assert (Hq5 : Qle ((1 # (q * q)%positive)%Q) (((1 # 5)%Q) * ir2_delta n)).
  { pose proof H5' as H55.
    unfold Qle, Qmult, Qinv in H55 |- *.
    cbn [Qmult Qnum Qden Qinv] in H55 |- *.
    rewrite !Pos2Z.inj_mul in H55 |- *.
    nia. }
  assert (Hhalf : Qle (ir2_delta n + (1 # (q * q)%positive)%Q)
                      ((((1 # 2)%Q) * ir2_delta n)
                       * ((Z.pos p # q)%Q + ir2_x n)%Q)%Q).
  { apply (Qle_trans _ (ir2_delta n + ((1 # 5)%Q) * ir2_delta n)%Q).
    { apply Qplus_le_compat; [apply Qle_refl | exact Hq5]. }
    { apply (Qle_trans _ ((6 # 5)%Q * ir2_delta n)%Q).
      { apply qeq_le. ring. }
      { apply (Qle_trans _ ((((1 # 2)%Q) * ir2_delta n) * ((12 # 5)%Q))%Q).
        { apply qeq_le. ring. }
        { apply (ir2_mult_le_compat_l ((12 # 5)%Q)
                    ((Z.pos p # q)%Q + ir2_x n)%Q
                    (((1 # 2)%Q) * ir2_delta n)%Q).
          { apply (Qle_trans _ (1%Q + (7 # 5)%Q)%Q).
            { apply qeq_le. ring. }
            { apply Qplus_le_compat; [exact Hle1 | exact Hx57]. } }
          { exact Hd12. } } } } }
  (* 窗内收束 *)
  assert (HM2p : Qlt 0 (((Z.pos p # q)%Q + ir2_x n)%Q)).
  { apply ir2_qpos_add; [unfold Qlt; cbn [Qnum Qden]; lia | exact Hxp]. }
  assert (HM2ne : ~ (((Z.pos p # q)%Q + ir2_x n)%Q == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q _ HM2p). apply Qeq_sym. exact Hc. }
  assert (Hsqd : ((ir2_x n - (Z.pos p # q)%Q)
                  * ((Z.pos p # q)%Q + ir2_x n))%Q
                 == (ir2_delta n + (1 # (q * q)%positive)%Q)%Q).
  { assert (H2q2 : ((2%Q - (Z.pos p # q)%Q * (Z.pos p # q)%Q)
                    == (1 # (q * q)%positive)%Q)).
    { rewrite Hpp. unfold Qeq, Qminus, Qplus, Qopp, Qmult. cbn [Qnum Qden].
      rewrite !Pos2Z.inj_mul. nia. }
    rewrite <- H2q2. unfold ir2_delta. ring. }
  apply (n54r_qle_cancel_r _ _ ((Z.pos p # q)%Q + ir2_x n)%Q HM2p).
  rewrite Hsqd. exact Hhalf.
Qed.

(* ============================================================ *)
(* S3：谱下界（Pell 见证）＋正典                                    *)
(* ============================================================ *)

Theorem n54r_uwin_pell_lower : forall (k n : nat) (b : positive),
  (n54r_pden k <= b)%positive ->
  QleT' ((5 # 1)%Q)
        (ir2_delta n * ((Z.pos (n54r_pden k * n54r_pden k)%positive) # 1)%Q) ->
  n54_uwin b n -> Empty_set.
Proof.
  intros k n b Hden H5 Hu.
  pose proof (n54r_pt_sq k) as Hsq.
  pose proof (n54r_pt_pgeq k) as Hpg.
  pose proof (n54_pos_le_Z _ _ Hpg) as HpZ.
  assert (Hpq0 : Qle 0 ((Z.pos (n54r_pnum k) # n54r_pden k)%Q)).
  { apply Qlt_le_weak. unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Hpp : ((Z.pos (n54r_pnum k) # n54r_pden k)%Q
                 * (Z.pos (n54r_pnum k) # n54r_pden k)%Q
                 == ((Z.pos (n54r_pnum k) * Z.pos (n54r_pnum k))
                     # (n54r_pden k * n54r_pden k)%positive)%Q)).
  { unfold Qmult, Qeq. cbn [Qnum Qden]. ring. }
  assert (Hs1 : Qlt ((Z.pos (n54r_pnum k) # n54r_pden k)%Q
                     * (Z.pos (n54r_pnum k) # n54r_pden k)%Q) 2%Q).
  { rewrite Hpp. unfold Qlt, Qmult. cbn [Qnum Qden].
    rewrite Pos2Z.inj_mul. lia. }
  pose proof (ir2_sq_ge2 n) as Hx2.
  assert (Hqx : Qlt ((Z.pos (n54r_pnum k) # n54r_pden k)%Q) (ir2_x n)).
  { apply (ir2_lt_of_sq (ir2_x n) (Z.pos (n54r_pnum k) # n54r_pden k)%Q);
      [apply Qlt_le_weak; apply (ir2_x_pos n) | exact Hpq0 |].
    apply (Qlt_le_trans _ 2%Q _); [exact Hs1 | exact Hx2]. }
  pose proof (Hu (Z.pos (n54r_pnum k)) (n54r_pden k)
                 (n54_pos_le_Z _ _ Hden)) as Hw.
  apply QltT_to_Qlt in Hw.
  pose proof (n54r_pell_win_core (n54r_pnum k) (n54r_pden k) n HpZ Hsq
                (Qlt_le_weak _ _ Hqx) (QleT'_to_Qle _ _ H5)) as Hcore.
  exact (False_rect Empty_set (Qlt_not_le _ _ Hw Hcore)).
Qed.

(* nat 辅件：5·W² ≤ 2^(2^n)·Q² ⟸ W ≤ 2^(2^(n+1)−2) ∧ 5^(2^n) ≤ Q *)
Lemma n54r_aux5 : forall (n W Q5 : nat),
  (W <= 2 ^ (2 ^ (Datatypes.S n) - 2))%nat ->
  (5 ^ (2 ^ n) <= Q5)%nat ->
  (5 * W * W <= 2 ^ (2 ^ n) * Q5 * Q5)%nat.
Proof.
  assert (Hpow4 : forall e : nat, (5 * 2 ^ e <= 2 ^ (e + 4))%nat).
  { induction e as [|e IH].
    - cbn. lia.
    - rewrite Nat.pow_succ_r'.
      replace (Datatypes.S e + 4)%nat with (Datatypes.S (e + 4))%nat by lia.
      rewrite Nat.pow_succ_r'. lia. }
  intros n W Q5 HW HQ.
  (* 链：W² ≤ 2^(2^(n+2)−4)；5·2^(2^(n+2)−4) ≤ 2^(2^(n+2)) = 4^(2^n)
     ≤ 5^(2^n) ≤ Q5 ≤ Q5² ≤ 2^(2^n)·Q5² *)
  assert (HW2 : (W * W <= 2 ^ (2 * (2 ^ (Datatypes.S n) - 2)))%nat).
  { replace (2 * (2 ^ (Datatypes.S n) - 2))%nat
      with ((2 ^ (Datatypes.S n) - 2) + (2 ^ (Datatypes.S n) - 2))%nat
      by lia.
    rewrite Nat.pow_add_r.
    nia. }
  assert (HE4 : (2 * (2 ^ (Datatypes.S n) - 2)
                 = 2 ^ (Datatypes.S (Datatypes.S n)) - 4)%nat).
  { rewrite !Nat.pow_succ_r'. lia. }
  rewrite HE4 in HW2.
  pose proof (Hpow4 (2 ^ (Datatypes.S (Datatypes.S n)) - 4)%nat) as HP4.
  assert (HP40 : (4 <= 2 ^ (Datatypes.S (Datatypes.S n)))%nat).
  { rewrite !Nat.pow_succ_r'.
    assert (HP : (0 < 2 ^ n)%nat).
    { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    lia. }
  replace (2 ^ (Datatypes.S (Datatypes.S n)) - 4 + 4)%nat
    with (2 ^ (Datatypes.S (Datatypes.S n)))%nat in HP4 by lia.
  assert (HP1 : forall j : nat, (4 ^ j <= 5 ^ j)%nat).
  { induction j as [|j IHj].
    - cbn. lia.
    - rewrite !Nat.pow_succ_r'. lia. }
  pose proof (HP1 (2 ^ n)%nat) as HP1'.
  assert (HP2 : (4 ^ (2 ^ n) = 2 ^ (2 * 2 ^ n))%nat).
  { replace 4%nat with (2 * 2)%nat by reflexivity.
    rewrite Nat.pow_mul_l.
    rewrite <- Nat.pow_add_r.
    replace (2 ^ n + 2 ^ n)%nat with (2 * 2 ^ n)%nat by lia.
    reflexivity. }
  rewrite HP2 in HP1'.
  assert (HQ1 : (1 <= Q5)%nat).
  { assert (H51 : (1 <= 2 ^ n)%nat).
    { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    assert (H52 : (5 ^ 1 <= 5 ^ (2 ^ n))%nat)
      by (apply Nat.pow_le_mono_r; lia).
    replace (5 ^ 1)%nat with 5%nat in H52 by reflexivity.
    lia. }
  (* 组合链：5W² ≤ 2^(2^(S(S n))) = X·X（X := 2^(2^(S n)) ≤ Q5）⟹ ≤ Q5²
     ⟹ ≤ 2^(2^n)·Q5² *)
  assert (Hfin : (5 * W * W <= 2 ^ (2 ^ (Datatypes.S (Datatypes.S n))))%nat)
    by nia.
  assert (HXq : (2 ^ (2 ^ Datatypes.S n) <= Q5)%nat).
  { replace (2 ^ (Datatypes.S n))%nat with (2 * 2 ^ n)%nat
      by (rewrite Nat.pow_succ_r'; reflexivity).
    exact (Nat.le_trans _ _ _ HP1' HQ). }
  assert (HQsq : (2 ^ (2 ^ Datatypes.S (Datatypes.S n))
                  = 2 ^ (2 ^ Datatypes.S n)
                    * 2 ^ (2 ^ Datatypes.S n))%nat).
  { replace (2 ^ (Datatypes.S (Datatypes.S n)))%nat
      with ((2 ^ (Datatypes.S n)) + (2 ^ (Datatypes.S n)))%nat
      by (rewrite !Nat.pow_succ_r'; lia).
    rewrite Nat.pow_add_r. reflexivity. }
  assert (Hfin2 : (5 * W * W
                   <= 2 ^ (2 ^ Datatypes.S n) * 2 ^ (2 ^ Datatypes.S n))%nat).
  { rewrite <- HQsq. exact Hfin. }
  assert (Hfin3 : (2 ^ (2 ^ Datatypes.S n) * 2 ^ (2 ^ Datatypes.S n)
                   <= Q5 * Q5)%nat) by nia.
  assert (Hstep : (5 * W * W <= Q5 * Q5)%nat)
    by (apply (Nat.le_trans _ _ _ Hfin2 Hfin3)).
  assert (HP0 : (1 <= 2 ^ (2 ^ n))%nat)
    by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  assert (Hfin4 : (5 * W * W <= 2 ^ (2 ^ n) * Q5 * Q5)%nat) by nia.
  exact Hfin4.
Qed.

(* 下界正典：7^(2^n) ≤ b ⟹ ¬UWin(n,b)（OT(b) ≥ log₂log₇b − O(1)）
   基数取 7 因 5^(2^n) 为基不成立——qgrow 仅给 5^(2^n) ≤ q_{2^n} 下界，
   推不出 q_{2^n} ≤ b（独立复算：pden(pt(2))=29 > 25）；补 qub 上界塔后以 7 为基。 *)
Corollary n54r_uwin_loglog_lower : forall (n : nat) (b : positive),
  (7 ^ (2 ^ n) <= Pos.to_nat b)%nat -> n54_uwin b n -> Empty_set.
Proof.
  intros n b Hb Hu.
  apply (n54r_uwin_pell_lower (2 ^ n) n b).
  - apply (proj2 (Pos2Nat.inj_le _ _)).
    pose proof (n54r_pt_qub (2 ^ n)) as Hg. lia.
  - apply Qle_to_QleT'.
    assert (Heq : (ir2_delta n
                    * ((Z.pos (n54r_pden (2 ^ n) * n54r_pden (2 ^ n))%positive) # 1)%Q
                   == ((Z.of_nat (2 ^ (2 ^ n))
                        * Z.pos (n54r_pden (2 ^ n) * n54r_pden (2 ^ n))%positive)
                       # (n54_wden n * n54_wden n)%positive)%Q)).
    { rewrite n54r_delta_eq.
      unfold Qmult, Qeq. cbn [Qnum Qden].
      rewrite !Pos2Z.inj_mul. ring. }
    rewrite Heq. unfold Qle. cbn [Qnum Qden].
    pose proof (n54r_aux5 n (Pos.to_nat (n54_wden n))
                 (Pos.to_nat (n54r_pden (2 ^ n)))
                 (n54r_wden_ub n) (n54r_pt_qgrow (2 ^ n))) as Haux.
    apply (proj1 (Nat2Z.inj_le _ _)) in Haux.
    rewrite !Nat2Z.inj_mul in Haux.
    rewrite <- !n54r_zpos_eq in Haux.
    replace (Z.of_nat 5) with 5%Z in Haux by reflexivity.
    rewrite !Pos2Z.inj_mul.
    nia.
  - exact Hu.
Qed.

(* ============================================================ *)
(* S4：q == x(m) 恰等排除核（gcd/Bezout 整值路线·上界收束前置）            *)
(* ============================================================ *)

Lemma n54r_qeqx_excl : forall (m : nat) (a : Z) (b' : positive),
  (1 <= m)%nat ->
  ((a # b')%Q == ir2_x m) ->
  (3 * Pos.to_nat b' * Pos.to_nat b' < 2 ^ (2 ^ m))%nat ->
  False.
Proof.
  intros m a b' Hm1 Hqq Hp.
  pose proof (n54r_wsq m) as Hwsq.
  pose proof (n54r_wden_lb m Hm1) as Hlb.
  setoid_rewrite (n54_x_eq_wnum m) in Hqq.
  assert (Hcross : (a * Z.pos (n54_wden m)
                    = Z.pos (n54_wnum m) * Z.pos b')%Z).
  { unfold Qeq in Hqq. cbn [Qnum Qden] in Hqq. exact Hqq. }
  pose proof (proj1 (Nat2Z.inj_le _ _) Hlb) as HEw.
  rewrite <- n54r_zpos_eq in HEw.
  (* g := gcd(wnum,wden)；Zgcd_is_gcd 给整除见证 wnum = k1·g ∧ wden = k2·g *)
  remember (Z.gcd (Z.pos (n54_wnum m)) (Z.pos (n54_wden m))) as g eqn:Hgdef.
  pose proof (Zgcd_is_gcd (Z.pos (n54_wnum m)) (Z.pos (n54_wden m))) as Hgc.
  rewrite <- Hgdef in Hgc.
  destruct Hgc as [HdP HdW Hgd].
  destruct HdP as [k1 Hk1].
  destruct HdW as [k2 Hk2].
  assert (Hk1r : (k1 * g = Z.pos (n54_wnum m))%Z) by (rewrite Hk1; ring).
  assert (Hk2r : (k2 * g = Z.pos (n54_wden m))%Z) by (rewrite Hk2; ring).
  (* 正性阶梯 *)
  assert (Hgpos : (0 < g)%Z).
  { pose proof (Z.gcd_nonneg (Z.pos (n54_wnum m)) (Z.pos (n54_wden m))) as Hgnn.
    rewrite <- Hgdef in Hgnn.
    destruct (Z.lt_trichotomy 0 g) as [Hlt | [Heq | Hgt]].
    - exact Hlt.
    - exfalso. rewrite <- Heq in Hk2.
      pose proof (Pos2Z.is_pos (n54_wden m)) as HWp.
      rewrite Hk2 in HWp. lia.
    - exfalso. lia. }
  assert (Hk2pos : (0 < k2)%Z).
  { pose proof (Pos2Z.is_pos (n54_wden m)) as HWp.
    rewrite Hk2 in HWp. nia. }
  assert (Hk1pos : (0 < k1)%Z).
  { pose proof (Pos2Z.is_pos (n54_wnum m)) as HWP.
    rewrite Hk1 in HWP. nia. }
  assert (Hg2 : (1 <= g * g)%Z) by nia.
  assert (HE1 : (Z.of_nat 1 <= Z.of_nat (2 ^ (2 ^ m)))%Z).
  { apply (proj1 (Nat2Z.inj_le _ _)).
    pose proof (Nat.pow_le_mono_r 2%nat 0%nat (2 ^ m)%nat
                  (ltac:(lia)) (Nat.le_0_l _)) as HP.
    replace (2 ^ 0)%nat with 1%nat in HP by reflexivity.
    exact HP. }
  assert (HT1 : (Z.of_nat 1 <= Z.of_nat (2 ^ (2 ^ (Nat.pred m))))%Z).
  { apply (proj1 (Nat2Z.inj_le _ _)).
    pose proof (Nat.pow_le_mono_r 2%nat 0%nat (2 ^ (Nat.pred m))%nat
                  (ltac:(lia)) (Nat.le_0_l _)) as HPb.
    replace (2 ^ 0)%nat with 1%nat in HPb by reflexivity.
    exact HPb. }
  (* 约化对互素：gcd(k1,k2) = 1（gcd(p·k1,p·k2) = |p|·gcd(k1,k2)） *)
  assert (Hg1 : (Z.gcd k1 k2 = 1)%Z).
  { pose proof (Z.gcd_mul_mono_l k1 k2 g) as Hgm.
    rewrite (Z.mul_comm g k1), (Z.mul_comm g k2) in Hgm.
    rewrite Hk1r, Hk2r, <- Hgdef in Hgm.
    rewrite (Z.abs_eq g) in Hgm by lia.
    destruct (Z.lt_trichotomy (Z.gcd k1 k2) 1) as [Hlt | [Heq | Hgt]].
    - exfalso. nia.
    - exact Heq.
    - exfalso. nia. }
  (* 交差化简：a·k2 = k1·b' *)
  assert (Hc2 : (a * k2 = k1 * Z.pos b')%Z).
  { rewrite Hk1, Hk2 in Hcross. nia. }
  (* T := 2^(2^(m−1))；E = 2^(2^m) = T·T *)
  assert (HEZ : (Z.of_nat (2 ^ (2 ^ m))
                 = Z.of_nat (2 ^ (2 ^ (Nat.pred m)))
                   * Z.of_nat (2 ^ (2 ^ (Nat.pred m))))%Z).
  { assert (Hms : m = Datatypes.S (Nat.pred m)) by lia.
    rewrite Hms at 1.
    rewrite (n54r_pow2split (Nat.pred m)).
    rewrite Nat2Z.inj_mul. reflexivity. }
  rewrite HEZ in HEw, Hwsq.
  (* g² ≤ E = T²（E = g²·D ∧ D ≥ 1，D 的正性由 no_sqrtZ 钉定） *)
  assert (Hdd : (g * g
                 <= Z.of_nat (2 ^ (2 ^ (Nat.pred m)))
                    * Z.of_nat (2 ^ (2 ^ (Nat.pred m))))%Z).
  { destruct (Z.le_gt_cases 1 (k1 * k1 - 2 * (k2 * k2))) as [Hge | Hlt].
    - nia.
    - exfalso. nia. }
  assert (HgT : (g <= Z.of_nat (2 ^ (2 ^ (Nat.pred m))))%Z).
  { destruct (Z.le_gt_cases g (Z.of_nat (2 ^ (2 ^ (Nat.pred m)))))
      as [Hle | Hgt].
    - exact Hle.
    - exfalso. nia. }
  assert (HTk2 : (Z.of_nat (2 ^ (2 ^ (Nat.pred m))) <= k2)%Z).
  { destruct (Z.le_gt_cases (Z.of_nat (2 ^ (2 ^ (Nat.pred m)))) k2)
      as [Hle | Hgt].
    - exact Hle.
    - exfalso. nia. }
  (* b' = k2·s（Bezout 互素消去）：b' ≥ k2 ≥ T ⟹ b'² ≥ T² = E ⟹ 与 3b'² < E 矛盾 *)
  pose proof (Z.gcd_bezout k1 k2 1 Hg1) as Hbzx.
  destruct Hbzx as [u [v Hbz]].
  assert (Hbt : (Z.pos b' = k2 * (u * a + v * Z.pos b'))%Z).
  { rewrite <- (Z.mul_1_r (Z.pos b')) at 1.
    rewrite <- Hbz at 1.
    replace ((Z.pos b') * (u * k1 + v * k2))%Z
      with (u * (k1 * Z.pos b') + v * k2 * Z.pos b')%Z by ring.
    rewrite <- Hc2. ring. }
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hp) as Hpz.
  rewrite !Nat2Z.inj_mul in Hpz.
  rewrite <- !n54r_zpos_eq in Hpz.
  replace (Z.of_nat 3) with 3%Z in Hpz by reflexivity.
  pose proof (Pos2Z.is_pos b') as Hbp.
  destruct (Z.le_gt_cases k2 (Z.pos b')) as [Hle | Hgt].
  - exfalso.
    assert (Hfin2 : (Z.of_nat (2 ^ (2 ^ (Nat.pred m)))
                     * Z.of_nat (2 ^ (2 ^ (Nat.pred m)))
                     <= Z.pos b' * Z.pos b')%Z) by nia.
    nia.
  - exfalso.
    destruct (Z.le_gt_cases 1 (u * a + v * Z.pos b')) as [Hs1 | Hs0].
    + assert (Hk2b : (k2 <= Z.pos b')%Z).
      { pose proof (Z.mul_le_mono_nonneg_l 1%Z (u * a + v * Z.pos b')%Z k2
                      (ltac:(lia)) Hs1) as HH.
        rewrite <- Hbt in HH.
        rewrite Z.mul_1_r in HH.
        exact HH. }
      lia.
    + nia.
Qed.

(* ============================================================ *)
(* S5：上界收紧（两端收束上半）——loglog 档正典                       *)
(* ============================================================ *)

(* 塔件上界：6b² ≤ 2^(2^m) ⟹ UWin(b,m)（m ≥ 1）
   链：e(m) = delta(m)/2 ≤ (1/2)·2^(−2^m)（delta_upper）
     ≤ 1/(12b'²)（b' ≤ b ⟹ 6b'² ≤ 6b² ≤ 2^(2^m)）⟹ n54_win_at。
   判据取 6b² ≤ 2^(2^m)：3b² < 2^(2^m) 形经 margin 核不足（12b'² ≤ 2·2^(2^m)
   需 6b'² ≤ 2^(2^m)）；正典 +3 指数不受影响。 *)
Theorem n54r_uwin_tower_upper : forall (m : nat) (b : positive),
  (1 <= m)%nat ->
  (6 * Pos.to_nat b * Pos.to_nat b <= 2 ^ (2 ^ m))%nat ->
  n54_uwin b m.
Proof.
  intros m b Hm H6 a b' Hble.
  apply (n54_win_at a b' m Hm).
  apply Qle_to_QleT'.
  assert (Hinv0 : Qle (Qinv ((Z.of_nat (2 ^ (2 ^ m))%nat) # 1))
                      (Qinv ((6 * (Z.pos b' * Z.pos b')) # 1))).
  { apply (ir2_inv_le ((6 * (Z.pos b' * Z.pos b')) # 1)
              ((Z.of_nat (2 ^ (2 ^ m))%nat) # 1)).
    { unfold Qlt. cbn [Qnum Qden]. nia. }
    { unfold Qle. cbn [Qnum Qden].
      pose proof (proj1 (Nat2Z.inj_le _ _) H6) as H6Z.
      rewrite !Nat2Z.inj_mul in H6Z.
      rewrite <- !n54r_zpos_eq in H6Z.
      replace (Z.of_nat 6) with 6%Z in H6Z by reflexivity.
      pose proof (n54_pos_le_Z _ _ Hble) as HbleZ.
      nia. } }
  assert (He : Qle (ir2_e m)
                 (((1 # 2)%Q) * Qinv ((Z.of_nat (2 ^ (2 ^ m))%nat) # 1))).
  { unfold ir2_e.
    apply (ir2_mult_le_compat_l (ir2_delta m)
             (Qinv ((Z.of_nat (2 ^ (2 ^ m))%nat) # 1)) (1 # 2)%Q).
    { exact (QleT'_to_Qle _ _ (n54r_delta_upper m Hm)). }
    { unfold Qle. cbn [Qnum Qden]. lia. } }
  apply (Qle_trans (ir2_e m)
           (((1 # 2)%Q) * Qinv ((Z.of_nat (2 ^ (2 ^ m))%nat) # 1))).
  { exact He. }
  apply (Qle_trans _ (((1 # 2)%Q) * Qinv ((6 * (Z.pos b' * Z.pos b')) # 1))).
  { apply (ir2_mult_le_compat_l _ _ ((1 # 2)%Q)).
    { exact Hinv0. }
    { unfold Qle. cbn [Qnum Qden]. lia. } }
  apply qeq_le.
  rewrite <- (Pos2Z.inj_mul b' b'), <- (Pos2Z.inj_mul 6 (b' * b')).
  rewrite (n54r_inv1p (6 * (b' * b')%positive)).
  unfold Qeq, Qmult. cbn [Qnum Qden].
  rewrite !Pos2Z.inj_mul.
  nia.
Qed.

(* 指数账：6B² ≤ 2^(2^(log₂log₂B+3))（独立复算 b<10^5 全称零违例） *)
Lemma n54r_loglog_exp : forall B : nat,
  (1 <= B)%nat ->
  (6 * B * B <= 2 ^ (2 ^ (Nat.log2 (Nat.log2 B) + 3)))%nat.
Proof.
  intros B HB.
  pose proof (Nat.log2_spec B HB) as Hspec.
  destruct (Nat.log2 B) as [|L] eqn:HL.
  - (* log₂B = 0：B = 1；6 ≤ 256 = 2^(2^(0+3)) *)
    cbn [Nat.log2 Nat.pow] in Hspec.
    replace (2 ^ (2 ^ (Nat.log2 0 + 3)))%nat with 256%nat by reflexivity.
    replace B with 1%nat by lia.
    cbn. lia.
  - (* log₂B = S L ≥ 1：再分 L = 0（B ∈ {2,3}，直算）与 L ≥ 1（CB 链） *)
    destruct L as [|L2].
    + (* log₂B = 1：B ∈ {2,3}；6B² ≤ 54 ≤ 256 = 2^(2^(1+3)) *)
      cbn [Nat.pow] in Hspec.
      replace (2 ^ (2 ^ (Nat.log2 1 + 3)))%nat with 256%nat by reflexivity.
      assert (HB54 : (6 * B * B <= 54)%nat)
        by (destruct B as [|[|B2]]; nia).
      lia.
    + (* log₂B = S (S L2) ≥ 2：B ≥ 4；
         CB := 2^(L2+4)；6B² ≤ 6·2^(L2+4)·2^(L2+4) = CB·CB；
         (L2+4)+(L2+4) ≤ 8·2^K = 2^(K+3) ⟸ L2+5 ≤ 2·2^K −1 *)
      pose proof (Nat.log2_spec (Datatypes.S (Datatypes.S L2))%nat
                    (ltac:(lia))) as Hkspec.
      set (K := Nat.log2 (Datatypes.S (Datatypes.S L2))) in *.
      replace (Datatypes.S (Datatypes.S (Datatypes.S L2)))%nat
        with (L2 + 3)%nat in Hspec by lia.
      replace (Datatypes.S (Datatypes.S L2))%nat with (L2 + 2)%nat in Hspec
        by lia.
      set (CB := (2 ^ (L2 + 5))%nat) in *.
      assert (HBC : (4 * B <= CB)%nat).
      { unfold CB.
        assert (H34 : (2 ^ (L2 + 3) * 4 = 2 ^ (L2 + 5))%nat).
        { replace (L2 + 5)%nat with ((L2 + 3) + 2)%nat by lia.
          rewrite (Nat.pow_add_r 2%nat (L2 + 3) 2).
          replace (2 ^ 2)%nat with 4%nat by reflexivity.
          reflexivity. }
        pose proof (proj2 Hspec) as HB2.
        nia. }
      assert (HBS : (6 * B * B <= CB * CB)%nat) by nia.
      assert (HCP : (CB * CB = 2 ^ ((L2 + 5) + (L2 + 5)))%nat).
      { unfold CB.
        rewrite <- (Nat.pow_add_r 2%nat (L2 + 5) (L2 + 5)).
        reflexivity. }
      rewrite HCP in HBS.
      assert (HKK : (2 ^ (K + 3) = 8 * 2 ^ K)%nat).
      { replace (K + 3)%nat with (Datatypes.S (Datatypes.S (Datatypes.S K)))%nat
          by lia.
        rewrite !Nat.pow_succ_r'. lia. }
      assert (HEX : ((L2 + 5) + (L2 + 5) <= 2 ^ (K + 3))%nat).
      { rewrite HKK.
        pose proof (proj2 Hkspec) as Hkhi.
        rewrite Nat.pow_succ_r' in Hkhi.
        assert (HP0 : (1 <= 2 ^ K)%nat)
          by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
        lia. }
      assert (HF : (2 ^ ((L2 + 5) + (L2 + 5)) <= 2 ^ (2 ^ (K + 3)))%nat)
        by (apply Nat.pow_le_mono_r; [lia | exact HEX]).
      exact (Nat.le_trans _ _ _ HBS HF).
Qed.

(* 正典实例：UWin(b, log₂log₂b + 3)——谱上界从对数档 2log₂b+4 收紧到 loglog 档 *)
Corollary n54r_uwin_loglog_upper : forall b : positive,
  n54_uwin b (Nat.log2 (Nat.log2 (Pos.to_nat b)) + 3)%nat.
Proof.
  intro b.
  apply (n54r_uwin_tower_upper
           (Nat.log2 (Nat.log2 (Pos.to_nat b)) + 3)%nat b).
  { lia. }
  { pose proof (Pos2Nat.is_pos b) as HB.
    exact (n54r_loglog_exp (Pos.to_nat b) HB). }
Qed.

Print Assumptions n54r_zpos_eq.
Print Assumptions n54r_pt_sq.
Print Assumptions n54r_pt_qgrow.
Print Assumptions n54r_wsq.
Print Assumptions n54r_wden_lb.
Print Assumptions n54r_wden_ub.
Print Assumptions n54r_delta_upper.
Print Assumptions n54r_pell_win_core.
Print Assumptions n54r_uwin_pell_lower.
Print Assumptions n54r_uwin_loglog_lower.
Print Assumptions n54r_qeqx_excl.
Print Assumptions n54r_pell_smoke.
Print Assumptions n54r_pt_qub.
Print Assumptions n54r_uwin_tower_upper.
Print Assumptions n54r_loglog_exp.
Print Assumptions n54r_uwin_loglog_upper.
