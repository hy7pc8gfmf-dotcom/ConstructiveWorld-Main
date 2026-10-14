(* 五字段指针｜使命：N5+N4 对象级新数学主定理——超越窗指数 OT(b) 三态谱的
   对象级正典化。
   对象：统一逃逸窗致胜谓词 UWin(n,b)（√2 Newton 序列项在指标 n 已严格胜过
   一切分母 ≤ b 的有理数——Q 层承载，dmew 统一窗 n₀=den+3 逐 q 版到全 q 版）。
   施工五件：
   ①对数档上界（A）：UWin(2·log₂b+4, b)——√2 族窗指数对数档上界
     （log2 谱界塔＋Qinv 反向＋dmcm 四分支边距核重用）；
   ②库窗线性对照（B）：UWin(b+3, b)——库统一窗保形复核（A/B 对比承载
     「同一统一窗在族上的松弛谱」：b+3 对 √2 远松于 2log₂b+4）；
   ③自见证下界（C/C2）：追踪对 (num,den) 显式伴随序列 x(n) == (num#den)
     ＋增长塔 num+den ≤ 2^(2^(n+2)−2) ⟹ loglog 档下界封形（den ≤ b 时
     致胜不可能：序列项自身即分母 ≤ b 的有理点，距离 0）。
     诚实申报：下界为 loglog 档，非勘形级速算的 Θ(log b) 两端——「显式
     最近有理 1/(2b) 压小 n」需收敛子 Pell 显式族塔件（留待后续件）；
   ④无穷档（INF）：任意序列 s、有理目标 r、den(r) ≤ b 时致胜谓词永不成立
     （有理目标点自身距离 0 恒压严格致胜）——「窗口永不闭合」有理性半边
     钉定为全称定理（Leibniz/arctan 部分和族实例化位）；
   ⑤N4 首锚（E）：√5 斜率 1/4 证书失败见证——|x₂−9/4| < 1/64（Q 层逐字
     vm_compute：1292/92736 < 1/64），斜率 1/(4b²) 型全-b 证书在 9/4 处
     不可达。诚实申报：实层 |√5−9/4| ≤ |x₂−9/4| 上距桥与斜率 1/5 达标题
     （K*=5 全-b 整数斜率钉定）留待后续件。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_dm_escape_window（dmew_e_pow_le/dmew_e_bnd/dmew_Qinv_1p）、
   u5c_sqrt2_closed_measure（dmcm_margin_closed）、
   u5c_sqrt5_closed_measure（dms5_x）；Stdlib QArith、Qabs、ZArith、Arith、
   Bool、Lia、Setoid、Morphisms、Qfield。
   构造性注记：语句面全 Set 层（QltT/¬:=→Empty_set/forall-arrow 入 Set），
   零 Prop 前提位；证明体内 Prop 推导合法（Qeq/Qle 链、Z 整隙、log2 谱界、
   nat 增长塔）；零承认、零经典逻辑、零全局假设；新定义面仅 n54_uwin/
   n54_grow/n54_wtrack（透明 Fixpoint），无新 Inductive；主定理装配链非
   单发空壳（log2 塔＋Qinv 反向＋边距核＋增长塔归纳＋Qeq 步进恒等式）；
   数值见证位 vm_compute 合法（具体数值判定，复算律）。
   编译配方：rocq c -native-compiler no -q -Q . "" u5c_n54_ot_spectrum.v *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：致胜谓词（Q 层承载·OT(b) 语句面核心）与增长塔                     *)
(* ============================================================ *)

(* UWin(n,b)：√2 Newton 序列项 x(n) 在指标 n 严格胜过一切分母 ≤ b 的有理数 *)
Definition n54_uwin (b : positive) (n : nat) : Set :=
  forall (a : Z) (b' : positive), (Z.pos b' <= Z.pos b)%Z ->
    QltT (ir2_e n) (Qabs (((a # b')%Q - ir2_x n)%Q)).

(* 增长塔 T(n) := 2^(2^(n+2)−2)（自见证下界封形） *)
Definition n54_grow (n : nat) : nat :=
  (2 ^ (2 ^ (Datatypes.S (Datatypes.S n)) - 2))%nat.

(* ============================================================ *)
(* S1：致胜核心（边距核重用：e(n) ≤ 1/(12b'²) ⟹ 致胜于 (a,b')）        *)
(* ============================================================ *)

Lemma n54_win_at : forall (a : Z) (b' : positive) (n : nat),
  (1 <= n)%nat ->
  QleT' (ir2_e n) ((1 # (12 * (b' * b')))%Q) ->
  QltT (ir2_e n) (Qabs (((a # b')%Q - ir2_x n)%Q)).
Proof.
  intros a b' n Hn1 He.
  pose proof (QleT'_to_Qle _ _ (dmcm_margin_closed a b' n Hn1 He)) as Hm.
  assert (Hc0 : QltT 0 ((1 # (12 * (b' * b')))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. nia. }
  assert (Hw0 : Qlt 0 ((1 # (12 * (b' * b')))%Q + (1 # (12 * (b' * b')))%Q)%Q).
  { apply (ir2_qpos_add (1 # (12 * (b' * b')))%Q (1 # (12 * (b' * b')))%Q).
    - apply QltT_to_Qlt. exact Hc0.
    - apply QltT_to_Qlt. exact Hc0. }
  pose proof (ir2_add_lt_r 0%Q
               ((1 # (12 * (b' * b')))%Q + (1 # (12 * (b' * b')))%Q)%Q
               (ir2_e n) Hw0) as Hlt0.
  rewrite (Qplus_comm 0%Q (ir2_e n)) in Hlt0.
  apply Qlt_to_QltT.
  setoid_rewrite <- (Qplus_0_r (ir2_e n)).
  apply (Qlt_le_trans (ir2_e n + 0)%Q
          ((1 # (12 * (b' * b')))%Q + (1 # (12 * (b' * b')))%Q + ir2_e n)%Q).
  - exact Hlt0.
  - exact Hm.
Qed.

(* ============================================================ *)
(* S2：对数档上界（A）——log2 谱界塔                                  *)
(* ============================================================ *)

(* 塔件：p < 2^(L+1)（Z 层）⟹ 12p² ≤ 2^(2L+6)（12 ≤ 64 由指数 +4 吸收） *)
Lemma n54_pow12_log : forall (p : positive) (L : nat),
  (Z.pos p < 2 ^ (Z.succ (Z.of_nat L)))%Z ->
  (12 * (Z.pos p * Z.pos p) <= Z.of_nat (2 ^ (2 * L + 6)))%Z.
Proof.
  intros p L Hp.
  assert (HL0 : (0 < 2 ^ L)%nat).
  { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
  pose proof (proj1 (Nat2Z.inj_lt 0%nat (2 ^ L)%nat) HL0) as HW0.
  cbn [Z.of_nat] in HW0.
  assert (Hs : (2 ^ (Z.succ (Z.of_nat L)) = 2 * Z.of_nat (2 ^ L))%Z).
  { rewrite Z.pow_succ_r by (apply Nat2Z.is_nonneg).
    rewrite Nat2Z.inj_pow. reflexivity. }
  rewrite Hs in Hp.
  replace (2 * L + 6)%nat with ((L + 3) + (L + 3))%nat by lia.
  rewrite (Nat.pow_add_r 2%nat (L + 3) (L + 3)).
  rewrite Nat2Z.inj_mul.
  replace (L + 3)%nat with (Datatypes.S (Datatypes.S (Datatypes.S L)))%nat by lia.
  rewrite !Nat.pow_succ_r'.
  replace (2 * (2 * (2 * 2 ^ L)))%nat with (8 * 2 ^ L)%nat by ring.
  rewrite Nat2Z.inj_mul.
  cbn [Z.of_nat] in *.
  nia.
Qed.

(* 对数档主定理：UWin(2·log₂b + 4, b) *)
Theorem n54_uwin_log_upper : forall b : positive,
  n54_uwin b (2 * Z.to_nat (Z.log2 (Z.pos b)) + 4)%nat.
Proof.
  intros b a b' Hble.
  assert (Hn1 : (1 <= 2 * Z.to_nat (Z.log2 (Z.pos b)) + 4)%nat) by lia.
  assert (Hmono : (Z.log2 (Z.pos b') <= Z.log2 (Z.pos b))%Z).
  { apply Z.log2_le_mono; solve [exact Hble | apply Pos2Z.is_pos]. }
  pose proof (Z.log2_spec (Z.pos b') (Pos2Z.is_pos b')) as [Hlo Hhi].
  assert (HLb : Z.of_nat (Z.to_nat (Z.log2 (Z.pos b))) = Z.log2 (Z.pos b))
    by (apply Z2Nat.id; apply Z.log2_nonneg).
  assert (Hlt : (Z.pos b' < 2 ^ (Z.succ (Z.log2 (Z.pos b))))%Z).
  { apply (Z.lt_le_trans (Z.pos b') (2 ^ (Z.succ (Z.log2 (Z.pos b'))))
             (2 ^ (Z.succ (Z.log2 (Z.pos b))))).
    - exact Hhi.
    - apply Z.pow_le_mono_r;
        solve [lia | exact Hmono | apply Z.succ_le_mono; exact Hmono
             | apply Z.log2_nonneg]. }
  rewrite <- HLb in Hlt.
  pose proof (n54_pow12_log b' (Z.to_nat (Z.log2 (Z.pos b))) Hlt) as H12.
  pose proof (dmew_e_pow_le (2 * Z.to_nat (Z.log2 (Z.pos b)) + 4)%nat Hn1) as Hep.
  replace (Datatypes.S (Datatypes.S (2 * Z.to_nat (Z.log2 (Z.pos b)) + 4)))%nat
    with (2 * Z.to_nat (Z.log2 (Z.pos b)) + 6)%nat in Hep by lia.
  assert (Hq' : Qinv ((12 * (Z.pos b' * Z.pos b')) # 1)
                == (1 # (12 * (b' * b')))%Q).
  { rewrite <- (Pos2Z.inj_mul b' b'), <- (Pos2Z.inj_mul 12 (b' * b')).
    apply qeqT_imp_qeq. apply dmew_Qinv_1p. }
  apply (n54_win_at a b' (2 * Z.to_nat (Z.log2 (Z.pos b)) + 4)%nat Hn1).
  apply Qle_to_QleT'.
  rewrite <- Hq'.
  apply (Qle_trans (ir2_e (2 * Z.to_nat (Z.log2 (Z.pos b)) + 4))
          (Qinv ((Z.of_nat (2 ^ (2 * Z.to_nat (Z.log2 (Z.pos b)) + 6))) # 1))).
  - exact (QleT'_to_Qle _ _ Hep).
  - apply (ir2_inv_le ((12 * (Z.pos b' * Z.pos b')) # 1)
            ((Z.of_nat (2 ^ (2 * Z.to_nat (Z.log2 (Z.pos b)) + 6))) # 1)).
    + pose proof (Pos2Z.is_pos b') as Hb0.
      unfold Qlt. cbn [Qnum Qden Qinv]. nia.
    + unfold Qle. cbn [Qnum Qden Qinv]. lia.
Qed.

(* ============================================================ *)
(* S3：库窗线性对照（B）——统一窗 n₀ = b+3 保形复核                      *)
(* ============================================================ *)

Theorem n54_uwin_lin_upper : forall b : positive,
  n54_uwin b (Z.to_nat (Z.pos b) + 3)%nat.
Proof.
  intros b a b' Hble.
  assert (Hn1 : (1 <= Z.to_nat (Z.pos b) + 3)%nat) by lia.
  pose proof (dmew_e_bnd b (Z.to_nat (Z.pos b) + 3)%nat
               (Nat.le_refl (Z.to_nat (Z.pos b) + 3))) as Heb.
  assert (Hq' : Qinv ((12 * (Z.pos b' * Z.pos b')) # 1)
                == (1 # (12 * (b' * b')))%Q).
  { rewrite <- (Pos2Z.inj_mul b' b'), <- (Pos2Z.inj_mul 12 (b' * b')).
    apply qeqT_imp_qeq. apply dmew_Qinv_1p. }
  apply (n54_win_at a b' (Z.to_nat (Z.pos b) + 3)%nat Hn1).
  apply Qle_to_QleT'.
  rewrite <- Hq'.
  apply (Qle_trans (ir2_e (Z.to_nat (Z.pos b) + 3))
          (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))).
  - exact (QleT'_to_Qle _ _ Heb).
  - apply (ir2_inv_le ((12 * (Z.pos b' * Z.pos b')) # 1)
            ((12 * (Z.pos b * Z.pos b)) # 1)).
    + pose proof (Pos2Z.is_pos b') as Hb0.
      unfold Qlt. cbn [Qnum Qden Qinv]. nia.
    + pose proof (Pos2Z.is_pos b) as Hb1.
      unfold Qle. cbn [Qnum Qden Qinv]. nia.
Qed.

(* ============================================================ *)
(* S4：自见证下界（C/C2）——正追踪伴随序列与增长塔                       *)
(* ============================================================ *)

(* 正追踪对：分子分母皆 positive（√2 Newton 各步分子分母恒正），
   x(n) == (wnum n # wden n)%Q 全程 Q 层显式。 *)
Fixpoint n54_wtrack (n : nat) : positive * positive :=
  match n with
  | O => (2%positive, 1%positive)
  | Datatypes.S m =>
      let '(a, b) := n54_wtrack m in
      ((a * a + 2 * (b * b))%positive, (2 * (a * b))%positive)
  end.

Definition n54_wnum (n : nat) : positive := fst (n54_wtrack n).
Definition n54_wden (n : nat) : positive := snd (n54_wtrack n).

(* Qeq 步进恒等式（√2 Newton 一步的显式形态；全 positive 载体） *)
Lemma n54_stepQ : forall p q : positive,
  (((Z.pos p # q)%Q + 2%Q / (Z.pos p # q)%Q) * (1 # 2)%Q
   == ((Z.pos (p * p + 2 * (q * q))) # (2 * (p * q)))%Q).
Proof.
  intros p q.
  unfold Qeq.
  cbn [Qnum Qden Qplus Qmult Qdiv Qinv].
  repeat (rewrite ?Pos2Z.inj_mul; rewrite ?Pos2Z.inj_add).
  ring.
Qed.

Lemma n54_x_eq_wnum : forall n : nat,
  ir2_x n == ((Z.pos (n54_wnum n)) # (n54_wden n))%Q.
Proof.
  assert (Hmain : forall n : nat,
    ir2_x n == ((Z.pos (fst (n54_wtrack n))) # (snd (n54_wtrack n)))%Q).
  { induction n as [|n IH].
    - reflexivity.
    - cbn [ir2_x]. setoid_rewrite IH.
      cbn [n54_wtrack fst snd].
      destruct (n54_wtrack n) as [a b] eqn:E.
      cbn [fst snd].
      apply n54_stepQ. }
  intros n. apply Hmain.
Qed.

(* 增长塔：Pos.to_nat (wnum) + Pos.to_nat (wden) ≤ T(n) *)
Lemma n54_tower : forall n : nat,
  (Pos.to_nat (n54_wnum n) + Pos.to_nat (n54_wden n) <= n54_grow n)%nat.
Proof.
  assert (Hstep : forall j : nat, (2 <= j)%nat ->
    (2 * 2 ^ (j - 2) * 2 ^ (j - 2) <= 2 ^ (2 * j - 2))%nat).
  { intros j Hj.
    replace (2 * j - 2)%nat with (Datatypes.S (Datatypes.S ((j - 2) + (j - 2))))%nat by lia.
    rewrite !Nat.pow_succ_r'.
    rewrite Nat.pow_add_r.
    lia. }
  assert (Hmain : forall n : nat,
    (Pos.to_nat (fst (n54_wtrack n)) + Pos.to_nat (snd (n54_wtrack n))
      <= n54_grow n)%nat).
  { induction n as [|n IH].
    - cbn [n54_wtrack fst snd n54_grow]. cbn. lia.
    - destruct (n54_wtrack n) as [a b] eqn:E.
      cbn [fst snd] in IH |- *.
      unfold n54_wnum, n54_wden, n54_grow in IH |- *.
      cbn [n54_wtrack]. rewrite E. cbn [fst snd].
      rewrite !Pos2Nat.inj_mul, !Pos2Nat.inj_add.
      cbn [Pos.to_nat].
      replace (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))%nat
        with (2 * 2 ^ (Datatypes.S (Datatypes.S n)))%nat
        by (rewrite Nat.pow_succ_r'; reflexivity).
      assert (Hpow : (2 <= 2 ^ (Datatypes.S (Datatypes.S n)))%nat).
      { assert (HL0 : (0 < 2 ^ n)%nat).
        { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
        rewrite !Nat.pow_succ_r'. lia. }
      pose proof (Hstep (2 ^ (Datatypes.S (Datatypes.S n)))%nat Hpow) as Hs.
      remember (Pos.to_nat a) as ua eqn:Hua.
      remember (Pos.to_nat b) as ub eqn:Hub.
      assert (Hsq : (ua * ua + 2 * (ub * ub) + 2 * (ua * ub)
                     <= 2 * ((ua + ub) * (ua + ub)))%nat) by nia.
      assert (Hmono : ((ua + ub) * (ua + ub)
                       <= (2 ^ (2 ^ (Datatypes.S (Datatypes.S n)) - 2))
                          * (2 ^ (2 ^ (Datatypes.S (Datatypes.S n)) - 2)))%nat) by nia.
      lia. }
  intros n. apply Hmain.
Qed.

(* 小桥：Q 自减为零（stdlib Qsub_diag 不在册，ring 自证） *)
Lemma n54_sub_diag : forall u : Q, (u - u) == 0%Q.
Proof. intros u. ring. Qed.

(* 小桥：positive ≤ 转 Z 层（Pos2Z.inj_le 不在册，以 Pos2Nat/Nat2Z 双跳自建） *)
Lemma n54_pos_le_Z : forall p q : positive,
  (p <= q)%positive -> (Z.pos p <= Z.pos q)%Z.
Proof. exact (Pos2Z.pos_le_pos). Qed.

(* 致胜不可能（自见证）：追踪分母 ≤ b 时，见证点取 x(n) 自身（距离 0） *)
Theorem n54_uwin_witness_fail : forall (n : nat) (b : positive),
  (n54_wden n <= b)%positive -> n54_uwin b n -> Empty_set.
Proof.
  intros n b Hden Hu.
  pose proof (Hu (Z.pos (n54_wnum n)) (n54_wden n)
               (n54_pos_le_Z _ _ Hden)) as Hw.
  apply QltT_to_Qlt in Hw.
  pose proof (n54_x_eq_wnum n) as Hxe.
  setoid_rewrite <- Hxe in Hw.
  setoid_rewrite (n54_sub_diag (ir2_x n)) in Hw.
  cbn [Qabs] in Hw.
  pose proof (ir2_delta_pos n) as Hd.
  pose proof (Qmult_lt_0_compat (1 # 2)%Q (ir2_delta n)
               (ltac:(unfold Qlt; cbn [Qnum Qden]; lia)) Hd) as Hepos.
  exact (False_rect Empty_set
          (Qlt_not_le (ir2_e n) 0%Q Hw (Qlt_le_weak _ _ Hepos))).
Qed.

(* loglog 档下界封形：T(n) ≤ b ⟹ 致胜不可能 *)
Theorem n54_uwin_loglog_lower : forall (n : nat) (b : positive),
  (n54_grow n <= Pos.to_nat b)%nat -> n54_uwin b n -> Empty_set.
Proof.
  intros n b Hg Hu.
  apply (n54_uwin_witness_fail n b).
  - apply (proj2 (Pos2Nat.inj_le (n54_wden n) b)).
    pose proof (n54_tower n) as Ht.
    unfold n54_wnum, n54_wden in Ht |- *.
    lia.
  - exact Hu.
Qed.

(* ============================================================ *)
(* S5：无穷档（INF）——有理目标窗口永不闭合（任意序列）                   *)
(* ============================================================ *)

(* 吸收位：Qabs(u) ≥ 0 ⟹ Qlt_bool (Qabs u) 0 = false *)
Lemma n54_abs_nlt0 : forall u : Q, Qlt_bool (Qabs u) 0%Q = false.
Proof.
  intros [zn pd]. unfold Qabs, Qlt_bool. cbn [Qnum Qden].
  destruct zn; reflexivity.
Qed.

Theorem n54_win_inf : forall (s : nat -> Q) (r : Q) (n : nat) (b : positive),
  (Qden r <= b)%positive ->
  (forall (a : Z) (b' : positive), (Z.pos b' <= Z.pos b)%Z ->
     QltT (Qabs ((r - s n)%Q)) (Qabs ((r - (a # b'))%Q)%Q)) ->
  Empty_set.
Proof.
  intros s r n b Hden Hw.
  pose proof (Hw (Qnum r) (Qden r) (n54_pos_le_Z _ _ Hden)) as Hspec.
  assert (Hqq : r == (Qnum r # Qden r)%Q) by reflexivity.
  assert (Hz : Qabs ((r - (Qnum r # Qden r))%Q) == 0%Q).
  { setoid_rewrite <- Hqq. setoid_rewrite (n54_sub_diag r). reflexivity. }
  apply QltT_to_Qlt in Hspec.
  setoid_rewrite Hz in Hspec.
  cbn [Qabs] in Hspec.
  assert (Hge : (0 <= Qabs (r - s n))%Q) by (apply Qabs_nonneg).
  exact (False_rect Empty_set (Qlt_not_le _ _ Hspec Hge)).
Qed.

(* ============================================================ *)
(* S6：N4 首锚（E）——√5 斜率 1/4 证书失败见证（9/4 处）                  *)
(* ============================================================ *)

(* 数值见证（复算律：谱点全量 vm_compute）：
   |x₂ − 9/4| < 1/64 ⟹ 斜率 1/(4b²) 型全-b 证书在 9/4 处不可达
   （实层 |√5−9/4| ≤ |x₂−9/4| 上距桥留待后续件）。 *)
Lemma n54_sqrt5_quarter_witness :
  QltT (Qabs (((9 # 4)%Q - dms5_x 2)%Q)) ((1 # (4 * (4 * 4)))%Q).
Proof.
  vm_compute. reflexivity.
Qed.

Print Assumptions n54_win_at.
Print Assumptions n54_uwin_log_upper.
Print Assumptions n54_uwin_lin_upper.
Print Assumptions n54_uwin_witness_fail.
Print Assumptions n54_uwin_loglog_lower.
Print Assumptions n54_win_inf.
Print Assumptions n54_sqrt5_quarter_witness.
