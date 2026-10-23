(* 五字段指针｜模块：piu_zz_tau_enclosure。使命：深水债② t1 τ 面/LOW 面/非零源
   文献常数有理夹包诚实体——τ 窗口闭合主证书件。依赖：piu_zz_poincare_engine
   （qpow/tau_pref/tau_step_k/mono/mul/powbase 单调链）、piu_zz_padic_clearing
   （zz_L/zz_Phi/zz_lcm_range 窗口积）、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   构造性：全树内闭合或引用池内 born 件；PNT 假设位=§D 两条（Section 参数化，
   出节全称化）；近期四引理证明体谱界分步链重构（语句面逐字节未动）。
   编译配方: rocq c -native-compiler no -q -Q . "" piu_zz_tau_enclosure.v
   以下为 born 修理登记史注： *)
(* piu_zz_tau_enclosure.v — 深水债② t1 铸造：τ 面/LOW 面/非零源的
   文献常数有理夹包诚实体。铸件 GD2铸造登记，照 GD2设计书语句面施工。
   供给来源标注随行；PNT 假设位=§D 两条（Section 参数化，出节全称化），
   其余全树内闭合或引用池内 born 件（engine/padic_clearing）。
   born 修理登记（C 条款·语句形批量修，详见 _tgedan2_铸造登记_夹包铸造回执）：
   W1 设计书 §二 613 步链系 8356/5120000 减法伤（实差 3356/5120000=1/1525.6）
      → k:=1526，even/odd 守卫 1226/1839→3052/4578，n0zz 4000→9200；
   W2 Vieta 接口被除数 (512#27)/(27x)=512/(729x) 与 §二 口径 512/(27x) 不符
      → 改 (512#27)/x（=Vieta 恒等 z·t(z)==512/27 的直接读形）；
   W3 rho_l 接口补 0<x 前提（原形对 x≤0 为假）；
   W4 c2fac_even 补 1≤m 前提（m=0 时 nat 减法截断为假）；
   W5 tau_face 守卫 n0zz≤n→N0≤n（n0zz 入 max 见证；eventual 形自洽）；
   W6 wq_pos 结论 QltT' 不在 engine 载体动物园 → 改 QneqT（非零本体形）。
   W9 qinv_anti·E1 assoc 方向伤（修理登记 验证 p1-p4 判定：E1 ←assoc 无匹配位红、
      E2 原链本绿；修=E1 改正向 Qmult_assoc 一记号，E2 不动）。
   本环境 Q 侧无 boolean 比较记号（Qlt_bool 不存在）：B1a/B1b 采 Qcompare ?= Lt 形。 *)

From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* ================================================================== *)
(* §H 工艺面：qpow / 序载体小件（全树内闭合）                           *)
(* ================================================================== *)

Lemma piu_zz_QleT_refl : forall a : Q, QleT' a a.
Proof. intros a. apply qleT_intro. apply Qle_refl. Qed.

Lemma piu_zz_QleT_trans : forall a b c : Q, QleT' a b -> QleT' b c -> QleT' a c.
Proof. intros a b c [H1] [H2]. apply qleT_intro. apply (Qle_trans a b c); assumption. Qed.

Lemma piu_zz_QleT_eq_l : forall a a' b : Q, QeqT a a' -> QleT' a b -> QleT' a' b.
Proof. intros a a' b [Hq] [Hle]. apply qleT_intro. rewrite <- Hq. exact Hle. Qed.

Lemma piu_zz_QleT_eq_r : forall a b b' : Q, QeqT b b' -> QleT' a b -> QleT' a b'.
Proof. intros a b b' [Hq] [Hle]. apply qleT_intro. rewrite <- Hq. exact Hle. Qed.

Lemma piu_zz_QeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof. intros a b [Hq]. apply qeqT_intro. apply (Qeq_sym a b Hq). Qed.

Lemma piu_zz_QeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof. intros a b c [H1] [H2]. apply qeqT_intro. apply (Qeq_trans a b c H1 H2). Qed.

Lemma piu_zz_QeqT_mul_l : forall x y z : Q, QeqT y z -> QeqT (x * y) (x * z)%Q.
Proof.
  intros x y z [H]. apply qeqT_intro.
  exact (Qmult_comp x x (Qeq_refl x) y z H).
Qed.

Lemma piu_zz_QeqT_mul_r : forall x y z : Q, QeqT x y -> QeqT (x * z) (y * z)%Q.
Proof.
  intros x y z [H]. apply qeqT_intro.
  exact (Qmult_comp x y H z z (Qeq_refl z)).
Qed.

Lemma piu_zz_QeqT_of_eq : forall a b : Q, a = b -> QeqT a b.
Proof. intros a b H. apply qeqT_intro. rewrite H. reflexivity. Qed.

Lemma piu_zz_Qle_of_eq : forall a b : Q, a == b -> QleT' a b.
Proof. intros a b H. apply qleT_intro. rewrite <- H. apply Qle_refl. Qed.

Lemma piu_zz_qpow_Qeq : forall (a b : Q) (n : nat), QeqT a b ->
  QeqT (piu_zz_qpow a n) (piu_zz_qpow b n)%Q.
Proof.
  intros a b n H. destruct H as [Hq].
  induction n as [|k IH].
  - apply qeqT_intro. reflexivity.
  - apply qeqT_intro. cbn [piu_zz_qpow]. destruct IH as [IH]. rewrite IH.
    rewrite Hq. reflexivity.
Qed.

Lemma piu_zz_qpow_mul : forall (a : Q) (m n : nat),
  QeqT (piu_zz_qpow a (m + n)%nat) (piu_zz_qpow a m * piu_zz_qpow a n)%Q.
Proof.
  intros a m n. induction n as [|k IH].
  - rewrite Nat.add_0_r. apply qeqT_intro. cbn [piu_zz_qpow]. ring.
  - replace (m + S k)%nat with (S (m + k))%nat by lia.
    cbn [piu_zz_qpow]. apply qeqT_intro. destruct IH as [IH]. rewrite IH. ring.
Qed.

Lemma piu_zz_qpow_pair : forall (a b : Q) (n : nat),
  QeqT (piu_zz_qpow a n * piu_zz_qpow b n) (piu_zz_qpow (a * b) n)%Q.
Proof.
  intros a b n. induction n as [|k IH].
  - apply qeqT_intro. cbn [piu_zz_qpow]. ring.
  - cbn [piu_zz_qpow]. apply qeqT_intro. destruct IH as [IH].
    transitivity ((a * b)%Q * (piu_zz_qpow a k * piu_zz_qpow b k))%Q.
    + ring.
    + rewrite IH. reflexivity.
Qed.

Lemma piu_zz_qpow_sq : forall (a : Q) (m : nat),
  QeqT (piu_zz_qpow a (2 * m)%nat) (piu_zz_qpow (a * a) m)%Q.
Proof.
  intros a m. replace (2 * m)%nat with (m + m)%nat by lia.
  apply (piu_zz_QeqT_trans _ (piu_zz_qpow a m * piu_zz_qpow a m)%Q).
  - exact (piu_zz_qpow_mul a m m).
  - exact (piu_zz_qpow_pair a a m).
Qed.

Lemma piu_zz_qpow_powbase : forall (a : Q) (k j : nat),
  QeqT (piu_zz_qpow a (j * k)%nat) (piu_zz_qpow (piu_zz_qpow a k) j)%Q.
Proof.
  intros a k j. induction j as [|i IH].
  - replace (0 * k)%nat with 0%nat by lia.
    apply qeqT_intro. cbn [piu_zz_qpow]. ring.
  - replace (S i * k)%nat with (k + i * k)%nat by lia.
    apply (piu_zz_QeqT_trans _ (piu_zz_qpow a k * piu_zz_qpow a (i * k)%nat)%Q).
    + exact (piu_zz_qpow_mul a k (i * k)%nat).
    + apply qeqT_intro.
      replace (piu_zz_qpow (piu_zz_qpow a k) (S i))%Q
        with (piu_zz_qpow a k * piu_zz_qpow (piu_zz_qpow a k) i)%Q
        by reflexivity.
      apply (piu_zz_QeqT_mul_l (piu_zz_qpow a k)
               (piu_zz_qpow a (i * k)%nat) (piu_zz_qpow (piu_zz_qpow a k) i)).
      exact IH.
Qed.

Lemma piu_zz_qpow_one : forall n : nat, QeqT (piu_zz_qpow 1%Q n) 1%Q.
Proof.
  intros n. induction n as [|k IH].
  - apply qeqT_intro. cbn [piu_zz_qpow]. reflexivity.
  - cbn [piu_zz_qpow]. apply qeqT_intro. destruct IH as [IH]. rewrite IH. ring.
Qed.

Lemma piu_zz_qpow_nonneg : forall (n : nat) (q : Q), (0 <= q)%Q ->
  QleT' 0%Q (piu_zz_qpow q n).
Proof.
  intros n q Hq. apply qleT_intro. induction n as [|k IH].
  - cbn [piu_zz_qpow]. unfold Qle, Qnum, Qden. cbn. lia.
  - cbn [piu_zz_qpow]. apply Qmult_le_0_compat; assumption.
Qed.

Lemma piu_zz_qpow_mono : forall (n : nat) (a b : Q), (0 <= a)%Q -> (a <= b)%Q ->
  QleT' (piu_zz_qpow a n) (piu_zz_qpow b n).
Proof.
  intros n a b Ha Hab. induction n as [|k IH].
  - apply piu_zz_QleT_refl.
  - cbn [piu_zz_qpow]. apply qleT_intro. apply Qmult_le_compat_nonneg.
    + split; [exact Ha | exact Hab].
    + split; [destruct (piu_zz_qpow_nonneg k a Ha) as [H1]; exact H1 | destruct IH as [IH]; exact IH].
Qed.

Lemma piu_zz_qpow_anti_exp : forall (a : Q) (n p : nat), (0 < a)%Q -> (a <= 1)%Q ->
  (n <= p)%nat -> QleT' (piu_zz_qpow a p) (piu_zz_qpow a n).
Proof.
  intros a n p Ha Hap Hnp.
  replace p with (n + (p - n))%nat by lia.
  apply (piu_zz_QleT_trans (piu_zz_qpow a (n + (p - n))%nat)
           (piu_zz_qpow a n * piu_zz_qpow a (p - n))%Q (piu_zz_qpow a n)).
  - apply (piu_zz_QleT_eq_r (piu_zz_qpow a (n + (p - n))%nat)
             (piu_zz_qpow a (n + (p - n))%nat)
             (piu_zz_qpow a n * piu_zz_qpow a (p - n))%Q).
    + exact (piu_zz_qpow_mul a n (p - n)%nat).
    + apply piu_zz_QleT_refl.
  - assert (Hle1 : QleT' (piu_zz_qpow a (p - n)) 1%Q).
    { apply (piu_zz_QleT_eq_r (piu_zz_qpow a (p - n)) (piu_zz_qpow 1%Q (p - n)) 1%Q).
      - apply piu_zz_qpow_one.
      - apply (piu_zz_qpow_mono (p - n) a 1%Q (Qlt_le_weak 0%Q a Ha) Hap). }
    destruct Hle1 as [Hle1].
    apply (piu_zz_QleT_eq_r (piu_zz_qpow a n * piu_zz_qpow a (p - n))%Q
             (piu_zz_qpow a n * 1%Q) (piu_zz_qpow a n)).
    + apply qeqT_intro. ring.
    + apply qleT_intro.
      apply (Qmult_le_compat_nonneg (piu_zz_qpow a n) (piu_zz_qpow a n)
               (piu_zz_qpow a (p - n)) 1%Q).
      * split; [destruct (piu_zz_qpow_nonneg n a ltac:(apply (Qlt_le_weak 0%Q a Ha))) as [H1]; exact H1 | apply Qle_refl].
      * split; [destruct (piu_zz_qpow_nonneg (p - n)%nat a ltac:(apply (Qlt_le_weak 0%Q a Ha))) as [H1]; exact H1 | exact Hle1].
Qed.

Lemma piu_zz_mul3_mono : forall a b c a' b' c' : Q,
  QleT' a a' -> QleT' b b' -> QleT' c c' ->
  (0 <= a)%Q -> (0 <= b)%Q -> (0 <= c)%Q ->
  QleT' (a * b * c) (a' * b' * c').
Proof.
  intros a b c a' b' c' Ha Hb Hc Ha0 Hb0 Hc0.
  destruct Ha as [Ha]. destruct Hb as [Hb]. destruct Hc as [Hc].
  assert (Ha'0 : (0 <= a')%Q) by (apply (Qle_trans 0%Q a a'); assumption).
  assert (Hb'0 : (0 <= b')%Q) by (apply (Qle_trans 0%Q b b'); assumption).
  apply qleT_intro.
  apply Qmult_le_compat_nonneg.
  - split.
    + apply Qmult_le_0_compat; assumption.
    + apply Qmult_le_compat_nonneg; [split; assumption | split; assumption].
  - split; [exact Hc0 | exact Hc].
Qed.

Lemma piu_zz_bernoulli_1526 : forall i : nat,
  QleT' (1 + zq (Z.of_nat i) * ((1) # 1525)%Q)
        (piu_zz_qpow (1 + ((1) # 1525)%Q) i).
Proof.
  intros i. apply qleT_intro. induction i as [|k IH].
  - cbn [piu_zz_qpow]. unfold zq, Qle, Qnum, Qden, Qmult, Qplus. cbn [Qnum Qden]. lia.
  - assert (Fut : (0 <= zq (Z.of_nat k) * ((1) # 1525)%Q)%Q).
    { apply Qmult_le_0_compat.
      - unfold zq, Qle, Qnum, Qden; cbn [Qnum Qden]. lia.
      - unfold Qle, Qnum, Qden; cbn; lia. }
    assert (HzS : zq (Z.of_nat (S k)) == (zq (Z.of_nat k) + 1)%Q).
    { unfold zq, Qeq, Qnum, Qden, Qplus, Qmult. cbn [Qnum Qden]. lia. }
    cbn [piu_zz_qpow]. rewrite HzS.
    apply (Qle_trans _ (piu_zz_qpow (1 + ((1) # 1525)%Q) k
                      + ((1) # 1525)%Q * piu_zz_qpow (1 + ((1) # 1525)%Q) k)%Q).
    + apply (Qle_trans _ ((1 + zq (Z.of_nat k) * ((1) # 1525)%Q)
                         + ((1) # 1525)%Q)%Q).
      * assert (E : (1 + (zq (Z.of_nat k) + 1) * ((1) # 1525)%Q
                     == (1 + zq (Z.of_nat k) * ((1) # 1525)%Q)
                        + ((1) # 1525)%Q)%Q) by ring.
        rewrite E. apply Qle_refl.
      * apply Qplus_le_compat.
        -- exact IH.
        -- apply (Qle_trans ((1) # 1525)%Q (1 * ((1) # 1525)%Q)%Q).
           ++ destruct (piu_zz_Qle_of_eq ((1) # 1525)%Q (1 * ((1) # 1525)%Q)%Q
                          (Qeq_sym (1 * ((1) # 1525)%Q) ((1) # 1525)%Q
                             (Qmult_1_l ((1) # 1525)%Q))) as [Hq1].
              exact Hq1.
           ++ rewrite (Qmult_comm ((1) # 1525)%Q
                         (piu_zz_qpow (1 + ((1) # 1525)%Q) k)).
              apply (Qmult_le_compat_r 1%Q
                       (piu_zz_qpow (1 + ((1) # 1525)%Q) k) ((1) # 1525)%Q).
              ** apply (Qle_trans 1%Q
                           (1 + zq (Z.of_nat k) * ((1) # 1525)%Q)%Q).
                 --- apply (Qplus_le_compat 1%Q 1%Q 0%Q
                              (zq (Z.of_nat k) * ((1) # 1525)%Q)).
                     +++ apply Qle_refl.
                     +++ exact Fut.
                 --- exact IH.
              ** unfold Qle, Qnum, Qden; cbn; lia.
    + assert (Hr : (1 + ((1) # 1525)%Q) * piu_zz_qpow (1 + ((1) # 1525)%Q) k
                   == piu_zz_qpow (1 + ((1) # 1525)%Q) k
                      + ((1) # 1525)%Q * piu_zz_qpow (1 + ((1) # 1525)%Q) k)
          by ring.
      rewrite Hr. apply Qle_refl.
Qed.

Lemma piu_zz_qinv_anti : forall x y : Q, (0 < x)%Q -> (0 < y)%Q -> (y <= x)%Q ->
  QleT' (/x) (/y).
Proof.
  intros x y Hx Hy Hle. apply qleT_intro.
  assert (Hxy : (0 < x * y)%Q) by (apply Qmult_lt_0_compat; assumption).
  apply (Qmult_lt_0_le_reg_r (/x) (/y) (x * y)); [exact Hxy |].
  assert (Hx0 : ~ x == 0%Q).
  { intro He. rewrite He in Hx. exact (Qlt_irrefl 0%Q Hx). }
  assert (Hy0 : ~ y == 0%Q).
  { intro He. rewrite He in Hy. exact (Qlt_irrefl 0%Q Hy). }
  assert (E1 : /x * (x * y) == y%Q).
  { rewrite Qmult_assoc. rewrite (Qmult_comm (/x) x).
    rewrite (Qmult_inv_r x Hx0). apply Qmult_1_l. }
  assert (E2 : /y * (x * y) == x%Q).
  { rewrite (Qmult_comm (/y) (x * y)).
    rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r y Hy0). apply Qmult_1_r. }
  rewrite E1, E2. exact Hle.
Qed.

(* W10 供给补铸（修理登记）：piu_zz_qdiv_anti 全树原无定义，由 §B' 两调用点反推
   签名铸出（0<c<=x 时正 a 反单调）；调用点 1 第 2 弹原证 0<=x 系设计伤，
   同步改证 0<c。 *)
Lemma piu_zz_qdiv_anti : forall a x c : Q, (0 < a)%Q -> (0 < c)%Q -> (c <= x)%Q ->
  QleT' (a / x) (a / c).
Proof.
  intros a x c Ha Hc Hcx. apply qleT_intro.
  assert (Hx : (0 < x)%Q) by (apply (Qlt_le_trans 0%Q c x); assumption).
  assert (Hinv0 : QleT' (/x) (/c)) by (apply piu_zz_qinv_anti; assumption).
  destruct Hinv0 as [Hinv].
  unfold Qdiv.
  rewrite (Qmult_comm a (/x)). rewrite (Qmult_comm a (/c)).
  apply (Qmult_le_compat_r (/x) (/c) a).
  - exact Hinv.
  - apply Qlt_le_weak. exact Ha.
Qed.

(* ================================================================== *)
(* §A 常数面（选取理由=设计书 §二 闭合总表；n0zz 见 W1 修理登记）    *)
(* ================================================================== *)

Section PiuzzTauEnclosure.

Definition piu_zz_rho_u : Q := (13 # 400)%Q.
Definition piu_zz_rho_l : Q := (294 # 10000)%Q.
Definition piu_zz_lam_u : Q := (29 # 1)%Q.
Definition piu_zz_lam_l : Q := (28 # 1)%Q.
Definition piu_zz_n0zz : nat := (4600 + 4600)%nat.

(* ================================================================== *)
(* §B 纯 Q 证书面（V0 首验令 born：bool 等式/比较形 vm_compute Closed）  *)
(* ================================================================== *)

(* B1a【机验✓】N3 下界符号：charpoly_int 在 18000 取负（Qcompare 形） *)
Lemma piu_zz_N3lo_sign :
  ((piu_zz_charpoly_int ((18000) # 1)%Q) ?= 0%Q)%Q = Lt.
Proof. vm_compute. reflexivity. Qed.

(* B1b/B1c【V0 首验✓】N3 上界符号（21900 形，W1 改窗后之形） *)
Lemma piu_zz_N3hi_sign :
  (0%Q ?= (piu_zz_charpoly_int ((21900) # 1)%Q))%Q = Lt.
Proof. vm_compute. reflexivity. Qed.

(* B2a【机验✓】rho_u 窗闭合：512*160000 < 169*(27*18000) *)
Lemma piu_zz_rho_u_win : (512 * 160000 <? 169 * (27 * 18000))%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* B2b【V0 首验✓】rho_l 窗闭合：86436*(27*21900) < 512*10^8 *)
Lemma piu_zz_rho_l_win : (86436 * (27 * 21900) <? 512 * 100000000)%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* B4 三件【V0 首验✓】τ 闭合裕度 *)
Lemma piu_zz_tau_margin : (9 * 142129 <=? 8 * 160000)%Z = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piu_zz_tau_step : (5116644 <? 5120000)%Z = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piu_zz_tau_pref : (2262 <=? 3200)%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* W1 修理新证：step = 5116644/5120000 ≤ 1−1/1526（设计书 613 系减法伤） *)
Lemma piu_zz_tau_step_k : (5116644 * 1526 <=? 1525 * 5120000)%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* W1 反证两件（fail-loud 审计 trail）：设计书原守卫不足的机械证书。
   语义：1 ≤ 4·step^1226 与 1 ≤ 4·step^2000——若原守卫成立应有 ≤ 1。 *)
Lemma piu_zz_w1_design_guard_refuted :
  Qle_bool (1 # 1)%Q ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 1226) = true.
Proof.
  assert (Hs0 : (0 <= (5116644 # 5120000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (H16b : Qle_bool ((9895 # 10000)%Q)
                   (piu_zz_qpow (5116644 # 5120000) 16) = true)
    by (vm_compute; reflexivity).
  assert (H16 : ((9895 # 10000)%Q <= piu_zz_qpow (5116644 # 5120000) 16)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) H16b). }
  assert (Hlo0 : (0 <= (9895 # 10000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hfinb : Qle_bool (1 # 1)%Q (piu_zz_qpow ((9895 # 10000)%Q) 76
                            * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 10))
                   = true)
    by (vm_compute; reflexivity).
  assert (Hfin : ((1 # 1)%Q <= piu_zz_qpow ((9895 # 10000)%Q) 76
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 10))%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) Hfinb). }
  assert (Hgoal : ((1 # 1)%Q
                   <= (4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 1226)%Q).
  { replace (1226)%nat with (76 * 16 + 10)%nat by reflexivity.
    destruct (piu_zz_qpow_mul (5116644 # 5120000)%Q (76 * 16)%nat 10%nat)
      as [Hm].
    rewrite Hm.
    destruct (piu_zz_qpow_powbase (5116644 # 5120000)%Q 16%nat 76%nat)
      as [Hp].
    rewrite Hp.
    destruct (piu_zz_qpow_mono 76%nat ((9895 # 10000)%Q)
                (piu_zz_qpow (5116644 # 5120000) 16) Hlo0 H16) as [Hmono].
    assert (HX0 : (0 <= ((4 # 1)%Q
                          * piu_zz_qpow (5116644 # 5120000) 10)%Q)%Q).
    { apply Qmult_le_0_compat.
      - unfold Qle, Qnum, Qden; cbn; lia.
      - destruct (piu_zz_qpow_nonneg 10%nat (5116644 # 5120000)%Q Hs0)
          as [H10].
        exact H10. }
    assert (E : ((4 # 1)%Q
                   * (piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 76
                      * piu_zz_qpow (5116644 # 5120000) 10)
                 == piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 76
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 10))%Q)
      by ring.
    rewrite E.
    apply (Qle_trans _ (piu_zz_qpow ((9895 # 10000)%Q) 76
                          * ((4 # 1)%Q
                             * piu_zz_qpow (5116644 # 5120000) 10))%Q).
    - exact Hfin.
    - apply (Qmult_le_compat_r _ _
               ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 10)%Q).
      + exact Hmono.
      + exact HX0. }
  unfold Qle_bool.
  apply (proj2 (Z.leb_le _ _)).
  exact Hgoal.
Qed.
Lemma piu_zz_w1_n0zz4000_refuted :
  Qle_bool (1 # 1)%Q ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 2000) = true.
Proof.
  assert (H16b : Qle_bool ((9895 # 10000)%Q)
                   (piu_zz_qpow (5116644 # 5120000) 16) = true)
    by (vm_compute; reflexivity).
  assert (H16 : ((9895 # 10000)%Q <= piu_zz_qpow (5116644 # 5120000) 16)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) H16b). }
  assert (Hlo0 : (0 <= (9895 # 10000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hfinb : Qle_bool (1 # 1)%Q (piu_zz_qpow ((9895 # 10000)%Q) 125
                            * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 0))
                   = true)
    by (vm_compute; reflexivity).
  assert (Hfin : ((1 # 1)%Q <= piu_zz_qpow ((9895 # 10000)%Q) 125
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 0))%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) Hfinb). }
  assert (Hgoal : ((1 # 1)%Q
                   <= (4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 2000)%Q).
  { replace (2000)%nat with (125 * 16 + 0)%nat by reflexivity.
    destruct (piu_zz_qpow_mul (5116644 # 5120000)%Q (125 * 16)%nat 0%nat)
      as [Hm].
    rewrite Hm.
    destruct (piu_zz_qpow_powbase (5116644 # 5120000)%Q 16%nat 125%nat)
      as [Hp].
    rewrite Hp.
    destruct (piu_zz_qpow_mono 125%nat ((9895 # 10000)%Q)
                (piu_zz_qpow (5116644 # 5120000) 16) Hlo0 H16) as [Hmono].
    assert (HX0 : (0 <= ((4 # 1)%Q
                          * piu_zz_qpow (5116644 # 5120000) 0)%Q)%Q).
    { apply Qmult_le_0_compat.
      - unfold Qle, Qnum, Qden; cbn; lia.
      - unfold Qle, Qnum, Qden; cbn; lia. }
    assert (E : ((4 # 1)%Q
                   * (piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 125
                      * piu_zz_qpow (5116644 # 5120000) 0)
                 == piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 125
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 0))%Q)
      by ring.
    rewrite E.
    apply (Qle_trans _ (piu_zz_qpow ((9895 # 10000)%Q) 125
                          * ((4 # 1)%Q
                             * piu_zz_qpow (5116644 # 5120000) 0))%Q).
    - exact Hfin.
    - apply (Qmult_le_compat_r _ _
               ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 0)%Q).
      + exact Hmono.
      + exact HX0. }
  unfold Qle_bool.
  apply (proj2 (Z.leb_le _ _)).
  exact Hgoal.
Qed.

(* W1 守卫闭式见证：even m=3052 处 4·step^m ≤ 1；odd m=4578 处 (377/100)·step^m ≤ 1 *)
Lemma piu_zz_tau_even_guard :
  Qle_bool ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 3052) (1 # 1)%Q = true.
Proof.
  assert (Hs0 : (0 <= (5116644 # 5120000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (HB0 : (0 <= piu_zz_qpow (5116644 # 5120000) 16)%Q).
  { destruct (piu_zz_qpow_nonneg 16%nat (5116644 # 5120000)%Q Hs0) as [H0].
    exact H0. }
  assert (H16b : Qle_bool (piu_zz_qpow (5116644 # 5120000) 16)
                   ((99 # 100)%Q) = true)
    by (vm_compute; reflexivity).
  assert (H16 : (piu_zz_qpow (5116644 # 5120000) 16 <= (99 # 100)%Q)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) H16b). }
  assert (Hfinb : Qle_bool (piu_zz_qpow ((99 # 100)%Q) 190
                            * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 12))
                   (1 # 1)%Q = true)
    by (vm_compute; reflexivity).
  assert (Hfin : (piu_zz_qpow ((99 # 100)%Q) 190
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 12)
                    <= (1 # 1)%Q)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) Hfinb). }
  assert (Hgoal : (((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 3052)
                   <= (1 # 1)%Q)%Q).
  { replace (3052)%nat with (190 * 16 + 12)%nat by reflexivity.
    destruct (piu_zz_qpow_mul (5116644 # 5120000)%Q (190 * 16)%nat 12%nat)
      as [Hm].
    rewrite Hm.
    destruct (piu_zz_qpow_powbase (5116644 # 5120000)%Q 16%nat 190%nat)
      as [Hp].
    rewrite Hp.
    destruct (piu_zz_qpow_mono 190%nat (piu_zz_qpow (5116644 # 5120000) 16)
                ((99 # 100)%Q) HB0 H16) as [Hmono].
    assert (HX0 : (0 <= ((4 # 1)%Q
                          * piu_zz_qpow (5116644 # 5120000) 12)%Q)%Q).
    { apply Qmult_le_0_compat.
      - unfold Qle, Qnum, Qden; cbn; lia.
      - exact HB0. }
    assert (E : ((4 # 1)%Q
                   * (piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 190
                      * piu_zz_qpow (5116644 # 5120000) 12)
                 == piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 190
                    * ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 12))%Q)
      by ring.
    rewrite E.
    apply (Qle_trans _ (piu_zz_qpow ((99 # 100)%Q) 190
                          * ((4 # 1)%Q
                             * piu_zz_qpow (5116644 # 5120000) 12))%Q).
    - apply (Qmult_le_compat_r _ _
               ((4 # 1)%Q * piu_zz_qpow (5116644 # 5120000) 12)%Q).
      + exact Hmono.
      + exact HX0.
    - exact Hfin. }
  unfold Qle_bool.
  apply (proj2 (Z.leb_le _ _)).
  exact Hgoal.
Qed.
Lemma piu_zz_tau_odd_guard :
  Qle_bool ((2262 # 400)%Q * piu_zz_qpow (5116644 # 5120000) 4578) (1 # 1)%Q
    = true.
Proof.
  assert (Hs0 : (0 <= (5116644 # 5120000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (HB0 : (0 <= piu_zz_qpow (5116644 # 5120000) 16)%Q).
  { destruct (piu_zz_qpow_nonneg 16%nat (5116644 # 5120000)%Q Hs0) as [H0].
    exact H0. }
  assert (H16b : Qle_bool (piu_zz_qpow (5116644 # 5120000) 16)
                   ((99 # 100)%Q) = true)
    by (vm_compute; reflexivity).
  assert (H16 : (piu_zz_qpow (5116644 # 5120000) 16 <= (99 # 100)%Q)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) H16b). }
  assert (Hfinb : Qle_bool (piu_zz_qpow ((99 # 100)%Q) 286
                            * ((2262 # 400)%Q
                               * piu_zz_qpow (5116644 # 5120000) 2))
                   (1 # 1)%Q = true)
    by (vm_compute; reflexivity).
  assert (Hfin : (piu_zz_qpow ((99 # 100)%Q) 286
                    * ((2262 # 400)%Q * piu_zz_qpow (5116644 # 5120000) 2)
                    <= (1 # 1)%Q)%Q).
  { unfold Qle. exact (proj1 (Z.leb_le _ _) Hfinb). }
  assert (Hgoal : (((2262 # 400)%Q * piu_zz_qpow (5116644 # 5120000) 4578)
                   <= (1 # 1)%Q)%Q).
  { replace (4578)%nat with (286 * 16 + 2)%nat by reflexivity.
    destruct (piu_zz_qpow_mul (5116644 # 5120000)%Q (286 * 16)%nat 2%nat)
      as [Hm].
    rewrite Hm.
    destruct (piu_zz_qpow_powbase (5116644 # 5120000)%Q 16%nat 286%nat)
      as [Hp].
    rewrite Hp.
    destruct (piu_zz_qpow_mono 286%nat (piu_zz_qpow (5116644 # 5120000) 16)
                ((99 # 100)%Q) HB0 H16) as [Hmono].
    assert (HX0 : (0 <= ((2262 # 400)%Q
                          * piu_zz_qpow (5116644 # 5120000) 2)%Q)%Q).
    { apply Qmult_le_0_compat.
      - unfold Qle, Qnum, Qden; cbn; lia.
      - destruct (piu_zz_qpow_nonneg 2%nat (5116644 # 5120000)%Q Hs0)
          as [H2].
        exact H2. }
    assert (E : ((2262 # 400)%Q
                   * (piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 286
                      * piu_zz_qpow (5116644 # 5120000) 2)
                 == piu_zz_qpow (piu_zz_qpow (5116644 # 5120000) 16) 286
                    * ((2262 # 400)%Q
                       * piu_zz_qpow (5116644 # 5120000) 2))%Q)
      by ring.
    rewrite E.
    apply (Qle_trans _ (piu_zz_qpow ((99 # 100)%Q) 286
                          * ((2262 # 400)%Q
                             * piu_zz_qpow (5116644 # 5120000) 2))%Q).
    - apply (Qmult_le_compat_r _ _
               ((2262 # 400)%Q * piu_zz_qpow (5116644 # 5120000) 2)%Q).
      + exact Hmono.
      + exact HX0.
    - exact Hfin. }
  unfold Qle_bool.
  apply (proj2 (Z.leb_le _ _)).
  exact Hgoal.
Qed.

(* B5 两件【V0 首验✓】LOW 闭合 *)
Lemma piu_zz_low_margin : (100000000 <=? 50 * (8232 * 8232))%Z = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piu_zz_rho_l_above_cage : (13 * 10000 <? 294 * 800)%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* §B' Vieta 消去接口（纯 Q 蕴含形；W2/W3 修形：
       |N1|^2 = 512/(27·x) 即 (512#27)/x，x>0 与窗口由引用侧证书自带）   *)
(* ================================================================== *)

Lemma piu_zz_rho_u_sq : QeqT (piu_zz_qpow piu_zz_rho_u 2) ((169) # 160000)%Q.
Proof. apply qeqT_intro. unfold piu_zz_rho_u. cbn [piu_zz_qpow]. ring. Qed.

Lemma piu_zz_rho_l_sq :
  QeqT (piu_zz_qpow piu_zz_rho_l 2) ((86436) # 100000000)%Q.
Proof. apply qeqT_intro. unfold piu_zz_rho_l. cbn [piu_zz_qpow]. ring. Qed.

Lemma piu_zz_lamrho_u : QeqT (piu_zz_lam_u * piu_zz_rho_u) (377 # 400)%Q.
Proof. apply qeqT_intro. unfold piu_zz_lam_u, piu_zz_rho_u. ring. Qed.

Lemma piu_zz_absN1sq_lt_rho_u : forall x : Q, (((18000) # 1) <= x)%Q ->
  QleT' ((512 # 27)%Q / x) (piu_zz_qpow piu_zz_rho_u 2).
Proof.
  intros x Hx.
  apply (piu_zz_QleT_trans ((512 # 27)%Q / x)
           ((512 # 27)%Q / ((18000) # 1)%Q) (piu_zz_qpow piu_zz_rho_u 2)).
  - apply (piu_zz_qdiv_anti ((512) # 27)%Q x ((18000) # 1)%Q).
    + unfold Qlt, Qnum, Qden; cbn; lia.
    + unfold Qlt, Qnum, Qden; cbn; lia.
    + exact Hx.
  - apply (piu_zz_QleT_eq_r ((512 # 27)%Q / ((18000) # 1)%Q)
             ((169) # 160000)%Q (piu_zz_qpow piu_zz_rho_u 2)).
    + apply piu_zz_QeqT_sym. apply piu_zz_rho_u_sq.
    + apply qleT_intro. unfold Qle, Qdiv, Qinv, Qmult, Qnum, Qden; cbn; lia.
Qed.

Lemma piu_zz_rho_l_lt_absN1sq : forall x : Q, (0 < x)%Q -> (x <= (21900) # 1)%Q ->
  QleT' (piu_zz_qpow piu_zz_rho_l 2) ((512 # 27)%Q / x).
Proof.
  intros x Hx0 Hx.
  apply (piu_zz_QleT_trans (piu_zz_qpow piu_zz_rho_l 2)
           ((512 # 27)%Q / ((21900) # 1)%Q) ((512 # 27)%Q / x)).
  - apply (piu_zz_QleT_eq_l (piu_zz_qpow piu_zz_rho_l 2)
             ((86436) # 100000000)%Q ((512 # 27)%Q / ((21900) # 1)%Q)).
    + apply piu_zz_QeqT_sym. apply piu_zz_rho_l_sq.
    + apply qleT_intro. unfold Qle, Qdiv, Qinv, Qmult, Qnum, Qden; cbn; lia.
  - apply (piu_zz_qdiv_anti ((512) # 27)%Q ((21900) # 1)%Q x).
    + unfold Qlt, Qnum, Qden; cbn; lia.
    + exact Hx0.
    + exact Hx.
Qed.

(* ================================================================== *)
(* §C 辅助面（纯 Q/nat 闭合）                                           *)
(* ================================================================== *)

Definition piu_zz_fl (n : nat) : nat := Nat.div (5 * n) 2.
Definition piu_zz_c2fac (n : nat) : Q :=
  (1 # Pos.of_nat (2 ^ Nat.sub (piu_zz_fl n) 2))%Q.

Lemma piu_zz_fl_ge2 : forall n : nat, (1 <= n)%nat ->
  (Nat.leb 2 (piu_zz_fl n)) = true.
Proof.
  intros n Hn. apply (proj2 (Nat.leb_le 2 (piu_zz_fl n))). unfold piu_zz_fl.
  assert (H2 : (2 <> 0)%nat) by lia.
  pose proof (Nat.div_mod (5 * n) 2 H2) as Hd.
  pose proof (Nat.mod_upper_bound (5 * n) 2 H2) as Hb.
  lia.
Qed.

Lemma piu_zz_fl_even : forall m : nat, piu_zz_fl (2 * m)%nat = (5 * m)%nat.
Proof.
  intros m. unfold piu_zz_fl.
  replace (5 * (2 * m))%nat with ((5 * m) * 2)%nat by lia.
  apply Nat.div_mul. lia.
Qed.

Lemma piu_zz_c2fac_even_canon : forall m : nat, (1 <= m)%nat ->
  piu_zz_c2fac (2 * m)%nat = ((1) # Pos.of_nat (2 ^ (5 * m - 2)))%Q.
Proof.
  intros m Hm. unfold piu_zz_c2fac. rewrite piu_zz_fl_even. reflexivity.
Qed.

Lemma piu_zz_c2fac_odd_canon : forall m : nat,
  piu_zz_c2fac (2 * m + 1)%nat = ((1) # Pos.of_nat (2 ^ (5 * m)))%Q.
Proof.
  intros m.
  assert (H2 : (2 <> 0)%nat) by lia.
  pose proof (Nat.div_mod (5 * (2 * m + 1)) 2 H2) as Hd.
  pose proof (Nat.mod_upper_bound (5 * (2 * m + 1)) 2 H2) as Hb.
  assert (Hfl : Nat.div (5 * (2 * m + 1)) 2 = (5 * m + 2)%nat) by lia.
  unfold piu_zz_c2fac, piu_zz_fl. rewrite Hfl.
  replace (5 * m + 2 - 2)%nat with (5 * m)%nat by lia.
  reflexivity.
Qed.

Lemma piu_zz_qpow_inv32 : forall m : nat,
  QeqT (piu_zz_qpow (1 # 32)%Q m) ((1) # Pos.of_nat (32 ^ m))%Q.
Proof.
  intros m. induction m as [|k IH].
  - apply qeqT_intro. cbn [piu_zz_qpow]. reflexivity.
  - rewrite Nat.pow_succ_r by lia.
    assert (Hn2 : (32 ^ k <> 0)%nat) by (apply Nat.pow_nonzero; lia).
    cbn [piu_zz_qpow]. apply qeqT_intro. destruct IH as [IH]. rewrite IH.
    rewrite Nat2Pos.inj_mul by (solve [lia | assumption]).
    cbn [Pos.of_nat].
    unfold Qeq, Qmult, Qnum, Qden. lia.
Qed.

Lemma piu_zz_c2fac_even : forall m : nat, (1 <= m)%nat ->
  QeqT (piu_zz_c2fac (2 * m)%nat) (zq 4 * piu_zz_qpow (1 # 32)%Q m)%Q.
Proof.
  intros m Hm.
  rewrite (piu_zz_c2fac_even_canon m Hm).
  apply qeqT_intro.
  destruct (piu_zz_qpow_inv32 m) as [Hi]. rewrite Hi.
  assert (Hpow : (32 ^ m)%nat = (4 * 2 ^ (5 * m - 2))%nat).
  { replace 32%nat with ((2 ^ 5)%nat) at 1 by reflexivity.
    rewrite <- Nat.pow_mul_r.
    replace (5 * m)%nat with (2 + (5 * m - 2))%nat at 1 by lia.
    rewrite Nat.pow_add_r. reflexivity. }
  rewrite Hpow.
  assert (Hn1 : (4 <> 0)%nat) by lia.
  assert (Hn2 : (2 ^ (5 * m - 2) <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  assert (Hrel : Z.pos (1 * Pos.of_nat (4 * 2 ^ (5 * m - 2)))%positive
                 = (4 * 1 * Z.pos (Pos.of_nat (2 ^ (5 * m - 2))))%Z).
  { rewrite Nat2Pos.inj_mul by assumption.
    cbn [Pos.of_nat]. lia. }
  unfold zq, Qeq, Qmult, Qnum, Qden. rewrite Hrel. lia.
Qed.

Lemma piu_zz_c2fac_odd : forall m : nat,
  QeqT (piu_zz_c2fac (2 * m + 1)%nat) (piu_zz_qpow (1 # 32)%Q m)%Q.
Proof.
  intros m.
  apply (piu_zz_QeqT_trans (piu_zz_c2fac (2 * m + 1)%nat)
           ((1) # Pos.of_nat (2 ^ (5 * m)))%Q (piu_zz_qpow (1 # 32)%Q m)).
  - apply piu_zz_QeqT_of_eq. apply piu_zz_c2fac_odd_canon.
  - apply (piu_zz_QeqT_trans ((1) # Pos.of_nat (2 ^ (5 * m)))%Q
             ((1) # Pos.of_nat (32 ^ m))%Q (piu_zz_qpow (1 # 32)%Q m)).
    + apply piu_zz_QeqT_of_eq.
      assert (Hpow : (32 ^ m)%nat = (2 ^ (5 * m))%nat).
      { replace 32%nat with ((2 ^ 5)%nat) at 1 by reflexivity.
        rewrite Nat.pow_mul_r. reflexivity. }
      rewrite Hpow. reflexivity.
    + apply piu_zz_QeqT_sym. apply piu_zz_qpow_inv32.
Qed.

(* 几何衰减核（W8 专化形：k:=1526 字面，泛-k 符号-denominator lia 沼沼避免） *)
Lemma piu_zz_base1526_prod : QeqT ((1526 # 1525)%Q * (1525 # 1526)%Q) 1%Q.
Proof. apply qeqT_intro. ring. Qed.

Lemma piu_zz_geo_1526 : forall j : nat,
  QleT' (piu_zz_qpow (1525 # 1526)%Q (j * 1526)%nat) (piu_zz_qpow (1 # 2)%Q j).
Proof.
  intros j.
  apply (piu_zz_QleT_trans _ (piu_zz_qpow (piu_zz_qpow (1525 # 1526)%Q 1526) j)).
  - eapply piu_zz_QleT_eq_r.
    + exact (piu_zz_qpow_powbase (1525 # 1526)%Q 1526 j).
    + apply piu_zz_QleT_refl.
  - apply (piu_zz_qpow_mono j (piu_zz_qpow (1525 # 1526)%Q 1526) ((1) # 2)%Q).
    + destruct (piu_zz_qpow_nonneg 1526 ((1525) # 1526)%Q
                 ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
      exact H1.
    + assert (Hpos1526 : (0 < (1525) # 1526)%Q)
        by (unfold Qlt, Qnum, Qden; cbn; lia).
      assert (Hcore : QleT' (piu_zz_qpow (1525 # 1526)%Q 1526) ((1) # 2)%Q).
      { destruct (piu_zz_qpow_pos 1526 ((1525) # 1526)%Q Hpos1526) as [Hpos].
        assert (Hb2 : (2 <= piu_zz_qpow (1526 # 1525)%Q 1526)%Q).
        { apply (Qle_trans 2%Q
                   (1 + zq (Z.of_nat 1526) * ((1) # 1525)%Q)%Q
                   (piu_zz_qpow (1 + ((1) # 1525)%Q) 1526)).
          - unfold zq, Qle, Qnum, Qden, Qplus, Qmult; cbn [Qnum Qden]; lia.
          - destruct (piu_zz_bernoulli_1526 1526) as [Hb26]. exact Hb26. }
        assert (Hprod : piu_zz_qpow (1526 # 1525)%Q 1526
                        * piu_zz_qpow (1525 # 1526)%Q 1526 == 1%Q).
        { assert (Hpt : QeqT (piu_zz_qpow (1526 # 1525)%Q 1526
                              * piu_zz_qpow (1525 # 1526)%Q 1526) 1%Q).
          { apply (piu_zz_QeqT_trans _
                     (piu_zz_qpow ((1526 # 1525)%Q * (1525 # 1526)%Q) 1526)).
            - exact (piu_zz_qpow_pair (1526 # 1525)%Q (1525 # 1526)%Q 1526).
            - apply (piu_zz_QeqT_trans _ (piu_zz_qpow 1%Q 1526) 1%Q).
              + apply piu_zz_qpow_Qeq. apply piu_zz_base1526_prod.
              + apply piu_zz_qpow_one. }
          destruct Hpt as [Hpr]. exact Hpr. }
        assert (H2le : (2 * piu_zz_qpow (1525 # 1526)%Q 1526
                        <= piu_zz_qpow (1526 # 1525)%Q 1526
                           * piu_zz_qpow (1525 # 1526)%Q 1526)%Q).
        { apply Qmult_le_compat_r;
            [exact Hb2 | apply (Qlt_le_weak 0%Q _); exact Hpos]. }
        rewrite Hprod in H2le.
        rewrite (Qmult_comm 2%Q (piu_zz_qpow (1525 # 1526)%Q 1526)) in H2le.
        assert (Hh2 : ((1 # 2)%Q * 2%Q) == 1%Q) by ring.
        apply qleT_intro.
        apply (Qmult_lt_0_le_reg_r (piu_zz_qpow (1525 # 1526)%Q 1526)
                 ((1 # 2)%Q) ((2 # 1)%Q)).
        - unfold Qlt, Qnum, Qden; cbn; lia.
        - rewrite Hh2. exact H2le. }
      destruct Hcore as [Hcr]. exact Hcr.
Qed.

(* 闭式基平方件 *)
Lemma piu_zz_qpow_sq_Qeq : forall (a B : Q) (m : nat), QeqT (a * a) B ->
  QeqT (piu_zz_qpow a (2 * m)%nat) (piu_zz_qpow B m)%Q.
Proof.
  intros a B m H.
  apply (piu_zz_QeqT_trans _ (piu_zz_qpow (a * a) m)).
  - apply piu_zz_qpow_sq.
  - apply piu_zz_qpow_Qeq. exact H.
Qed.

Lemma piu_zz_q36 : forall m : nat,
  QeqT (piu_zz_qpow (1 # 6)%Q (2 * m)%nat) (piu_zz_qpow (1 # 36)%Q m)%Q.
Proof. intros m. apply piu_zz_qpow_sq_Qeq. apply qeqT_intro. ring. Qed.

Lemma piu_zz_q40 : forall m : nat,
  QeqT (piu_zz_qpow (1 # 40)%Q (2 * m)%nat) (piu_zz_qpow (1 # 1600)%Q m)%Q.
Proof. intros m. apply piu_zz_qpow_sq_Qeq. apply qeqT_intro. ring. Qed.

Lemma piu_zz_qpow_half2 : QeqT (piu_zz_qpow (1 # 2)%Q 2) ((1) # 4)%Q.
Proof. apply qeqT_intro. cbn [piu_zz_qpow]. ring. Qed.

Lemma piu_zz_qpow_half3 : QeqT (piu_zz_qpow (1 # 2)%Q 3) ((1) # 8)%Q.
Proof. apply qeqT_intro. cbn [piu_zz_qpow]. ring. Qed.

(* τ 侧配对/合并恒等（W1 修理链） *)
Lemma piu_zz_tau_pair_eq : forall m : nat,
  QeqT (piu_zz_qpow piu_zz_lam_u (2 * m)%nat * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
       (piu_zz_qpow (142129 # 160000)%Q m)%Q.
Proof.
  intros m.
  apply (piu_zz_QeqT_trans _
           (piu_zz_qpow (piu_zz_lam_u * piu_zz_rho_u)%Q (2 * m)%nat)).
  - apply piu_zz_qpow_pair.
  - apply (piu_zz_QeqT_trans _
             (piu_zz_qpow ((piu_zz_lam_u * piu_zz_rho_u)%Q
                           * (piu_zz_lam_u * piu_zz_rho_u)%Q) m)).
    + apply piu_zz_qpow_sq.
    + apply piu_zz_qpow_Qeq. apply qeqT_intro.
      unfold piu_zz_lam_u, piu_zz_rho_u. ring.
Qed.

Lemma piu_zz_tau_merge_eq : forall m : nat,
  QeqT (piu_zz_qpow (1 # 32)%Q m * piu_zz_qpow (142129 # 160000)%Q m)
       (piu_zz_qpow (5116644 # 5120000)%Q m * piu_zz_qpow (1 # 36)%Q m)%Q.
Proof.
  intros m.
  apply (piu_zz_QeqT_trans _
           (piu_zz_qpow ((1 # 32)%Q * (142129 # 160000)%Q) m)).
  - apply piu_zz_qpow_pair.
  - apply (piu_zz_QeqT_trans _
             (piu_zz_qpow ((5116644 # 5120000)%Q * (1 # 36)%Q) m)).
    + apply piu_zz_qpow_Qeq. apply qeqT_intro. ring.
    + apply piu_zz_QeqT_sym. apply piu_zz_qpow_pair.
Qed.

Lemma piu_zz_low_merge_eq : forall m : nat,
  QeqT (piu_zz_qpow (1 # 32)%Q m * piu_zz_qpow (67765824 # 100000000)%Q m)
       (piu_zz_qpow (67765824 # 3200000000)%Q m)%Q.
Proof.
  intros m.
  apply (piu_zz_QeqT_trans _
           (piu_zz_qpow ((1 # 32)%Q * (67765824 # 100000000)%Q) m)).
  - apply piu_zz_qpow_pair.
  - apply piu_zz_qpow_Qeq. apply qeqT_intro. ring.
Qed.

(* τ 偶闭合核（W1：守卫 3052=2·1526） *)
Lemma piu_zz_tau_even_core : forall m : nat, (3052 <= m)%nat ->
  QleT' (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_u (2 * m)%nat
         * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
        (piu_zz_qpow (1 # 6)%Q (2 * m)%nat).
Proof.
  intros m Hm.
  destruct (piu_zz_c2fac_even m ltac:(lia)) as [Ec].
  destruct (piu_zz_tau_pair_eq m) as [Ep].
  destruct (piu_zz_tau_merge_eq m) as [Em].
  destruct (piu_zz_q36 m) as [Eq36].
  assert (Eall : (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_u (2 * m)%nat
                  * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
                 == (zq 4 * piu_zz_qpow (5116644 # 5120000)%Q m
                     * piu_zz_qpow (1 # 36)%Q m)%Q).
  { rewrite <- (Qmult_assoc (piu_zz_c2fac (2 * m)%nat)
              (piu_zz_qpow piu_zz_lam_u (2 * m)%nat)
              (piu_zz_qpow piu_zz_rho_u (2 * m)%nat)).
    rewrite Ep. rewrite Ec.
    rewrite <- (Qmult_assoc (zq 4) (piu_zz_qpow (1 # 32)%Q m)
                 (piu_zz_qpow (142129 # 160000)%Q m)).
    rewrite Em.
    rewrite <- (Qmult_assoc (zq 4) (piu_zz_qpow (5116644 # 5120000)%Q m)
               (piu_zz_qpow (1 # 36)%Q m)).
    reflexivity. }
  assert (Hs0 : (0 <= (5116644 # 5120000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hkle : ((5116644 # 5120000)%Q <= (1525 # 1526)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hkpos : (0 < (1525 # 1526)%Q)%Q) by (unfold Qlt, Qnum, Qden; cbn; lia).
  assert (Hkunit : ((1525 # 1526)%Q <= 1)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hstep : QleT' (piu_zz_qpow (5116644 # 5120000)%Q m) ((1) # 4)%Q).
  { apply (piu_zz_QleT_trans _ (piu_zz_qpow (1525 # 1526)%Q m)).
    - exact (piu_zz_qpow_mono m (5116644 # 5120000)%Q (1525 # 1526)%Q Hs0 Hkle).
    - apply (piu_zz_QleT_trans _ (piu_zz_qpow (1525 # 1526)%Q (2 * 1526)%nat)).
      + apply (piu_zz_qpow_anti_exp (1525 # 1526)%Q (2 * 1526)%nat m Hkpos Hkunit).
        lia.
      + apply (piu_zz_QleT_trans _ (piu_zz_qpow ((1) # 2)%Q 2)).
         * apply (piu_zz_geo_1526 2).
        * apply (piu_zz_QleT_eq_r (piu_zz_qpow (1 # 2)%Q 2)
                   (piu_zz_qpow (1 # 2)%Q 2) ((1) # 4)%Q).
          -- apply piu_zz_qpow_half2.
          -- apply piu_zz_QleT_refl. }
  assert (Hb1 : QleT' (zq 4 * piu_zz_qpow (5116644 # 5120000)%Q m) (1 # 1)%Q).
  { apply (piu_zz_QleT_trans _ (zq 4 * ((1) # 4)%Q)%Q).
    - apply qleT_intro. apply Qmult_le_compat_nonneg.
      + split; [unfold zq, Qle, Qnum, Qden; cbn; lia | apply Qle_refl].
      + split.
        * destruct (piu_zz_qpow_nonneg m ((5116644) # 5120000)%Q
                    ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
          exact H1.
        * destruct Hstep as [Hstep]; exact Hstep.
    - apply (piu_zz_QleT_eq_r (zq 4 * ((1) # 4)%Q) (zq 4 * ((1) # 4)%Q)
               ((1) # 1)%Q).
      + apply qeqT_intro. unfold zq. ring.
      + apply piu_zz_QleT_refl. }
  assert (Hfin : QleT' ((1 # 1)%Q * piu_zz_qpow (1 # 36)%Q m)
                   (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
  { apply (piu_zz_QleT_eq_r ((1 # 1)%Q * piu_zz_qpow (1 # 36)%Q m)
             ((1 # 1)%Q * piu_zz_qpow (1 # 36)%Q m)
             (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
    - apply (piu_zz_QeqT_trans ((1 # 1)%Q * piu_zz_qpow (1 # 36)%Q m)
               (piu_zz_qpow (1 # 36)%Q m) (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
      + apply qeqT_intro. ring.
      + apply piu_zz_QeqT_sym. exact (piu_zz_q36 m).
    - apply piu_zz_QleT_refl. }
  apply (piu_zz_QleT_eq_l
           (zq 4 * piu_zz_qpow (5116644 # 5120000)%Q m * piu_zz_qpow (1 # 36)%Q m)
           (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_u (2 * m)%nat
            * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
           (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
  - apply piu_zz_QeqT_sym. apply qeqT_intro. exact Eall.
  - apply (piu_zz_QleT_trans _
             ((1 # 1)%Q * piu_zz_qpow (1 # 36)%Q m)).
    + apply qleT_intro. apply Qmult_le_compat_r.
      * destruct Hb1 as [Hb1]; exact Hb1.
      * destruct (piu_zz_qpow_nonneg m ((1) # 36)%Q
                  ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
    + exact Hfin.
Qed.

(* τ 奇侧配对/合并 *)
Lemma piu_zz_tau_pair_eq_odd : forall m : nat,
  QeqT (piu_zz_qpow piu_zz_lam_u (2 * m + 1)%nat
        * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
       ((piu_zz_lam_u * piu_zz_rho_u)%Q * piu_zz_qpow (142129 # 160000)%Q m)%Q.
Proof.
  intros m.
  replace (2 * m + 1)%nat with (S (2 * m))%nat by lia.
  cbn [piu_zz_qpow]. apply qeqT_intro.
  transitivity ((piu_zz_lam_u * piu_zz_rho_u)%Q
                * (piu_zz_qpow piu_zz_lam_u (2 * m)%nat
                   * piu_zz_qpow piu_zz_rho_u (2 * m)%nat))%Q.
  - ring.
  - destruct (piu_zz_tau_pair_eq m) as [Ep]. rewrite Ep. reflexivity.
Qed.

Lemma piu_zz_tau_odd_core : forall m : nat, (4578 <= m)%nat ->
  QleT' (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_u (2 * m + 1)%nat
         * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
        (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat).
Proof.
  intros m Hm.
  assert (Esn : forall X : Q,
            QeqT (piu_zz_qpow X (2 * m + 1)%nat) (X * piu_zz_qpow X (2 * m)%nat)%Q).
  { intros X. replace (2 * m + 1)%nat with (S (2 * m))%nat by lia.
    apply qeqT_intro. cbn [piu_zz_qpow]. ring. }
  destruct (piu_zz_c2fac_odd m) as [Ec].
  destruct (piu_zz_tau_pair_eq m) as [Ep].
  destruct (piu_zz_tau_merge_eq m) as [Em].
  destruct (piu_zz_q36 m) as [Eq36].
  destruct (piu_zz_lamrho_u) as [Elr].
  assert (Eall : (piu_zz_c2fac (2 * m + 1)%nat
                  * piu_zz_qpow piu_zz_lam_u (2 * m + 1)%nat
                  * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
                 == (((377 # 400)%Q * piu_zz_qpow (5116644 # 5120000)%Q m)
                     * piu_zz_qpow (1 # 36)%Q m)%Q).
  {
    destruct (Esn piu_zz_lam_u) as [E1]. rewrite E1.
    destruct (Esn piu_zz_rho_u) as [E2]. rewrite E2. rewrite Ec.
    transitivity ((piu_zz_lam_u * piu_zz_rho_u)%Q
                  * (piu_zz_qpow (1 # 32)%Q m
                     * (piu_zz_qpow piu_zz_lam_u (2 * m)%nat
                        * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)))%Q.
    - ring.
    - rewrite Ep. rewrite Em. rewrite Elr.
      rewrite <- (Qmult_assoc ((377 # 400)%Q)
                 (piu_zz_qpow (5116644 # 5120000)%Q m)
                 (piu_zz_qpow (1 # 36)%Q m)).
      reflexivity. }
  assert (Hs0 : (0 <= (5116644 # 5120000)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hkle : ((5116644 # 5120000)%Q <= (1525 # 1526)%Q)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hkpos : (0 < (1525 # 1526)%Q)%Q) by (unfold Qlt, Qnum, Qden; cbn; lia).
  assert (Hkunit : ((1525 # 1526)%Q <= 1)%Q)
    by (unfold Qle, Qnum, Qden; cbn; lia).
  assert (Hstep : QleT' (piu_zz_qpow (5116644 # 5120000)%Q m) ((1) # 8)%Q).
  { apply (piu_zz_QleT_trans _ (piu_zz_qpow (1525 # 1526)%Q m)).
    - exact (piu_zz_qpow_mono m (5116644 # 5120000)%Q (1525 # 1526)%Q Hs0 Hkle).
    - apply (piu_zz_QleT_trans _ (piu_zz_qpow (1525 # 1526)%Q (3 * 1526)%nat)).
      + apply (piu_zz_qpow_anti_exp (1525 # 1526)%Q (3 * 1526)%nat m Hkpos Hkunit).
        lia.
      + apply (piu_zz_QleT_trans _ (piu_zz_qpow ((1) # 2)%Q 3)).
         * apply (piu_zz_geo_1526 3).
        * apply (piu_zz_QleT_eq_r (piu_zz_qpow (1 # 2)%Q 3)
                   (piu_zz_qpow (1 # 2)%Q 3) ((1) # 8)%Q).
          -- apply piu_zz_qpow_half3.
          -- apply piu_zz_QleT_refl. }
  assert (Hb1 : QleT' ((377 # 400)%Q * piu_zz_qpow (5116644 # 5120000)%Q m)
                  (1 # 6)%Q).
  { apply (piu_zz_QleT_trans _ ((377 # 400)%Q * ((1) # 8)%Q)%Q).
    - apply qleT_intro. apply Qmult_le_compat_nonneg.
      + split; [unfold Qle, Qnum, Qden; cbn; lia | apply Qle_refl].
      + split.
        * destruct (piu_zz_qpow_nonneg m ((5116644) # 5120000)%Q
                    ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
          exact H1.
        * destruct Hstep as [Hstep]; exact Hstep.
    - apply (piu_zz_QleT_trans ((377 # 400)%Q * ((1) # 8)%Q)
               ((377) # 3200)%Q (1 # 6)%Q).
      + apply (piu_zz_QleT_eq_r ((377 # 400)%Q * ((1) # 8)%Q)
                 ((377 # 400)%Q * ((1) # 8)%Q) ((377) # 3200)%Q).
        * apply qeqT_intro. ring.
        * apply piu_zz_QleT_refl.
      + apply qleT_intro. unfold Qle, Qnum, Qden; cbn; lia. }
  assert (Hfin : QleT' ((1 # 6)%Q * piu_zz_qpow (1 # 36)%Q m)
                   (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat)).
  { apply (piu_zz_QleT_eq_r ((1 # 6)%Q * piu_zz_qpow (1 # 36)%Q m)
             ((1 # 6)%Q * piu_zz_qpow (1 # 36)%Q m)
             (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat)).
    - apply (piu_zz_QeqT_trans ((1 # 6)%Q * piu_zz_qpow (1 # 36)%Q m)
               ((1 # 6)%Q * piu_zz_qpow (1 # 6)%Q (2 * m)%nat)
               (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat)).
      + apply (piu_zz_QeqT_mul_l (1 # 6)%Q (piu_zz_qpow (1 # 36)%Q m)
                 (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
        apply (piu_zz_QeqT_sym _ _ (piu_zz_q36 m)).
      + apply (piu_zz_QeqT_sym _ _ (Esn (1 # 6)%Q)).
    - apply piu_zz_QleT_refl. }
  apply (piu_zz_QleT_eq_l
           (((377 # 400)%Q * piu_zz_qpow (5116644 # 5120000)%Q m)
            * piu_zz_qpow (1 # 36)%Q m)
           (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_u (2 * m + 1)%nat
            * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
           (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat)).
  - apply piu_zz_QeqT_sym. apply qeqT_intro. exact Eall.
  - apply (piu_zz_QleT_trans _
             ((1 # 6)%Q * piu_zz_qpow (1 # 36)%Q m)).
    + apply qleT_intro. apply Qmult_le_compat_r.
      * destruct Hb1 as [Hb1]; exact Hb1.
      * destruct (piu_zz_qpow_nonneg m ((1) # 36)%Q
                  ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
    + exact Hfin.
Qed.

(* LOW 侧配对/合并/双核 *)
Lemma piu_zz_low_pair_eq : forall m : nat,
  QeqT (piu_zz_qpow piu_zz_lam_l (2 * m)%nat * piu_zz_qpow piu_zz_rho_l (2 * m)%nat)
       (piu_zz_qpow (67765824 # 100000000)%Q m)%Q.
Proof.
  intros m.
  apply (piu_zz_QeqT_trans _
           (piu_zz_qpow (piu_zz_lam_l * piu_zz_rho_l)%Q (2 * m)%nat)).
  - apply piu_zz_qpow_pair.
  - apply (piu_zz_QeqT_trans _
             (piu_zz_qpow ((piu_zz_lam_l * piu_zz_rho_l)%Q
                           * (piu_zz_lam_l * piu_zz_rho_l)%Q) m)).
    + apply piu_zz_qpow_sq.
    + apply piu_zz_qpow_Qeq. apply qeqT_intro.
      unfold piu_zz_lam_l, piu_zz_rho_l. ring.
Qed.

Lemma piu_zz_c2fac_nonneg : forall n : nat, QleT' 0%Q (piu_zz_c2fac n).
Proof.
  intros n. apply qleT_intro. destruct n as [|k].
  - unfold piu_zz_c2fac, piu_zz_fl, Qle, Qnum, Qden.
    cbn [Nat.div Nat.sub Nat.pow Z.of_nat]. lia.
  - pose proof (piu_zz_fl_ge2 (S k) ltac:(lia)) as Hf.
    apply (proj1 (Nat.leb_le 2 (piu_zz_fl (S k)))) in Hf.
    unfold piu_zz_c2fac, Qle, Qnum, Qden. cbn [Qnum Qden]. lia.
Qed.

Lemma piu_zz_zL_nonneg : forall n : nat, QleT' 0%Q (zq (zz_L n)).
Proof.
  intros n. apply qleT_intro. unfold zq, zz_L.
  assert (Ha : forall K : nat, (0 <= zz_lcm_range K)%Z).
  { intro K. induction K as [|i IH].
    - cbn [zz_lcm_range]. lia.
    - cbn [zz_lcm_range]. exact (Z.lcm_nonneg _ _). }
  assert (Hb : (0 < zz_Phi n)%Z)
    by (unfold zz_Phi; apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat)));
        apply zz_prodf_pos).
  assert (Hz : (0 <= Z.div (zz_lcm_range (4 * n)%nat) (zz_Phi n))%Z)
    by (apply Z.div_pos; [apply Ha | exact Hb]).
  unfold Qle, Qnum, Qden. cbn [Qnum Qden]. lia.
Qed.

Lemma piu_zz_chain_neg : forall (n : nat) (u : Q),
  (0 <= piu_zz_c2fac n * zq (zz_L n))%Q -> (u < 0)%Q ->
  (0 < piu_zz_qpow (1 # 6)%Q n)%Q ->
  QleT' (piu_zz_c2fac n * zq (zz_L n) * u)%Q (piu_zz_qpow (1 # 6)%Q n).
Proof.
  intros n u Hp Hu Ht.
  apply qleT_intro.
  apply (Qlt_le_weak (piu_zz_c2fac n * zq (zz_L n) * u)
           (piu_zz_qpow (1 # 6)%Q n)).
  apply (Qle_lt_trans (piu_zz_c2fac n * zq (zz_L n) * u) 0%Q
           (piu_zz_qpow (1 # 6)%Q n)).
  - rewrite (Qmult_comm (piu_zz_c2fac n * zq (zz_L n)) u).
    apply (Qle_trans (u * (piu_zz_c2fac n * zq (zz_L n)))%Q
             (0%Q * (piu_zz_c2fac n * zq (zz_L n)))%Q 0%Q).
    + apply Qmult_le_compat_r.
      * apply (Qlt_le_weak u 0%Q Hu).
      * exact Hp.
    + assert (Hr0 : (0%Q * (piu_zz_c2fac n * zq (zz_L n)))%Q == 0%Q) by ring.
      rewrite Hr0. apply Qle_refl.
  - exact Ht.
Qed.

Lemma piu_zz_low_even_core : forall m : nat,
  QleT' (piu_zz_qpow (1 # 40)%Q (2 * m)%nat)
        (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_l (2 * m)%nat
         * piu_zz_qpow piu_zz_rho_l (2 * m)%nat).
Proof.
  intros m. destruct (Nat.eq_dec m 0) as [Hm0 | Hmne].
  - subst m. apply qleT_intro.
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [piu_zz_qpow].
    unfold piu_zz_c2fac, piu_zz_fl, Qle, Qnum, Qden, Qmult.
    cbn. lia.
  - destruct (piu_zz_c2fac_even m ltac:(lia)) as [Ec].
    destruct (piu_zz_low_pair_eq m) as [Ep].
    destruct (piu_zz_low_merge_eq m) as [Em].
    destruct (piu_zz_q40 m) as [Eq40].
    assert (Eall : (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_l (2 * m)%nat
                    * piu_zz_qpow piu_zz_rho_l (2 * m)%nat)
                   == (zq 4 * piu_zz_qpow (67765824 # 3200000000)%Q m)%Q).
    { rewrite <- (Qmult_assoc (piu_zz_c2fac (2 * m)%nat)
                 (piu_zz_qpow piu_zz_lam_l (2 * m)%nat)
                 (piu_zz_qpow piu_zz_rho_l (2 * m)%nat)).
      rewrite Ep. rewrite Ec.
      rewrite <- (Qmult_assoc (zq 4) (piu_zz_qpow (1 # 32)%Q m)
                   (piu_zz_qpow (67765824 # 100000000)%Q m)).
      rewrite Em. reflexivity. }
    assert (Hmono : QleT' (piu_zz_qpow (1 # 1600)%Q m)
                      (piu_zz_qpow (67765824 # 3200000000)%Q m)).
    { apply (piu_zz_qpow_mono m ((1) # 1600)%Q ((67765824) # 3200000000)%Q);
        unfold Qle, Qnum, Qden; cbn; lia. }
    apply (piu_zz_QleT_eq_r (piu_zz_qpow (1 # 40)%Q (2 * m)%nat)
             (zq 4 * piu_zz_qpow (67765824 # 3200000000)%Q m)
             (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_l (2 * m)%nat
              * piu_zz_qpow piu_zz_rho_l (2 * m)%nat)).
    + apply piu_zz_QeqT_sym. apply qeqT_intro. exact Eall.
    + apply (piu_zz_QleT_eq_l (piu_zz_qpow (1 # 1600)%Q m)
               (piu_zz_qpow (1 # 40)%Q (2 * m)%nat)
               (zq 4 * piu_zz_qpow (67765824 # 3200000000)%Q m)).
      * apply piu_zz_QeqT_sym. apply piu_zz_q40.
      * apply (piu_zz_QleT_trans (piu_zz_qpow (1 # 1600)%Q m)
                 (piu_zz_qpow (67765824 # 3200000000)%Q m)
                 (zq 4 * piu_zz_qpow (67765824 # 3200000000)%Q m)).
        -- exact Hmono.
        -- apply (piu_zz_QleT_eq_l ((1 # 1)%Q * piu_zz_qpow (67765824 # 3200000000)%Q m)
                   (piu_zz_qpow (67765824 # 3200000000)%Q m)
                   (zq 4 * piu_zz_qpow (67765824 # 3200000000)%Q m)).
          ++ apply qeqT_intro. ring.
          ++ apply qleT_intro. apply Qmult_le_compat_r.
             ** unfold Qle, Qnum, Qden; cbn; lia.
             ** destruct (piu_zz_qpow_nonneg m ((67765824) # 3200000000)%Q
                          ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
                exact H1.
Qed.

Lemma piu_zz_low_odd_core : forall m : nat,
  QleT' (piu_zz_qpow (1 # 40)%Q (2 * m + 1)%nat)
        (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_l (2 * m + 1)%nat
         * piu_zz_qpow piu_zz_rho_l (2 * m + 1)%nat).
Proof.
  intros m.
  assert (Esn : forall X : Q,
            QeqT (piu_zz_qpow X (2 * m + 1)%nat) (X * piu_zz_qpow X (2 * m)%nat)%Q).
  { intros X. replace (2 * m + 1)%nat with (S (2 * m))%nat by lia.
    apply qeqT_intro. cbn [piu_zz_qpow]. ring. }
  destruct (piu_zz_c2fac_odd m) as [Ec].
  destruct (piu_zz_low_pair_eq m) as [Ep].
  destruct (piu_zz_low_merge_eq m) as [Em].
  destruct (piu_zz_q40 m) as [Eq40].
  assert (Elr : QeqT (piu_zz_lam_l * piu_zz_rho_l) (8232 # 10000)%Q).
  { apply qeqT_intro. unfold piu_zz_lam_l, piu_zz_rho_l. ring. }
  assert (Eall : (piu_zz_c2fac (2 * m + 1)%nat
                  * piu_zz_qpow piu_zz_lam_l (2 * m + 1)%nat
                  * piu_zz_qpow piu_zz_rho_l (2 * m + 1)%nat)
                 == ((8232 # 10000)%Q * piu_zz_qpow (67765824 # 3200000000)%Q m)%Q).
  {
    destruct (Esn piu_zz_lam_l) as [E1]. rewrite E1.
    destruct (Esn piu_zz_rho_l) as [E2]. rewrite E2. rewrite Ec.
    transitivity ((piu_zz_lam_l * piu_zz_rho_l)%Q
                  * (piu_zz_qpow (1 # 32)%Q m
                     * (piu_zz_qpow piu_zz_lam_l (2 * m)%nat
                        * piu_zz_qpow piu_zz_rho_l (2 * m)%nat)))%Q.
    - ring.
    - rewrite Ep. destruct Elr as [Elr']. rewrite Elr'. rewrite Em. reflexivity. }
  apply (piu_zz_QleT_eq_l ((1 # 40)%Q * piu_zz_qpow (1 # 1600)%Q m)
           (piu_zz_qpow (1 # 40)%Q (2 * m + 1)%nat)
           (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_l (2 * m + 1)%nat
            * piu_zz_qpow piu_zz_rho_l (2 * m + 1)%nat)).
  - apply piu_zz_QeqT_sym.
    apply (piu_zz_QeqT_trans (piu_zz_qpow (1 # 40)%Q (2 * m + 1)%nat)
             ((1 # 40)%Q * piu_zz_qpow (1 # 40)%Q (2 * m)%nat)
             ((1 # 40)%Q * piu_zz_qpow (1 # 1600)%Q m)).
    + exact (Esn (1 # 40)%Q).
    + apply qeqT_intro.
      destruct (piu_zz_q40 m) as [H40]. rewrite H40. reflexivity.
  - apply (piu_zz_QleT_eq_r ((1 # 40)%Q * piu_zz_qpow (1 # 1600)%Q m)
             ((8232 # 10000)%Q * piu_zz_qpow (67765824 # 3200000000)%Q m)
             (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_l (2 * m + 1)%nat
              * piu_zz_qpow piu_zz_rho_l (2 * m + 1)%nat)).
    + apply piu_zz_QeqT_sym. apply qeqT_intro. exact Eall.
    + apply (piu_zz_QleT_trans ((1 # 40)%Q * piu_zz_qpow (1 # 1600)%Q m)
               ((1 # 40)%Q * piu_zz_qpow (67765824 # 3200000000)%Q m)
               ((8232 # 10000)%Q * piu_zz_qpow (67765824 # 3200000000)%Q m)).
      * apply qleT_intro. apply Qmult_le_compat_nonneg.
        -- split; [unfold Qle, Qnum, Qden; cbn; lia | apply Qle_refl].
        -- split.
           ++ destruct (piu_zz_qpow_nonneg m ((1) # 1600)%Q
                        ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
              exact H1.
           ++ apply (piu_zz_qpow_mono m ((1) # 1600)%Q ((67765824) # 3200000000)%Q);
                unfold Qle, Qnum, Qden; cbn; lia.
      * apply qleT_intro. apply Qmult_le_compat_nonneg.
        -- split; unfold Qle, Qnum, Qden; cbn; lia.
        -- split.
           ++ destruct (piu_zz_qpow_nonneg m ((67765824) # 3200000000)%Q
                        ltac:(unfold Qle, Qnum, Qden; cbn; lia)) as [H1].
              exact H1.
           ++ apply Qle_refl.
Qed.

(* ================================================================== *)
(* §D PNT 假设槽（本包唯一诚实假设位；率型最小形，逐点可判定）
   献值锚：lim log Φ_n/n = π/(2√3)−ln(3√3/4)=0.64527561…（ZZ 2020 v2
   式(10)）＋PNT（ψ(x)~x ⟹ lim log lcm(1..4n)/n = 4）
   ⟹ lim L_n^{1/n}=e^{3.35472…}=28.6315…（机外；与 A01 §3.4 World
   record 常数内嵌 4−W 恒等互证）。28 < 28.6315 < 29。
   承载注记：两条假设均为 sigT 承载（Set），出节后作为显式参数全称化，
   非全局未闭位；Λu=29 的正确性由本假设内容自身承载（样点带 256/512/1024
   处 up=false 实测——N0 领地远超样点带，恰证其 PNT 级诚实性）。 *)
(* ================================================================== *)

Hypothesis HLn_rate_up : { N0 : nat & forall n : nat, (N0 <= n)%nat ->
  QleT' (zq (zz_L n)) (piu_zz_qpow piu_zz_lam_u n) }.
Hypothesis HLn_rate_lo : { N0 : nat & forall n : nat, (N0 <= n)%nat ->
  QleT' (piu_zz_qpow piu_zz_lam_l n) (zq (zz_L n)) }.
(* 共享令：HLn_rate_up 系全工程唯一 L_n 上率假设——σ 面（s1/s2 两路）
   Require 本包引用，禁另立。 *)

(* ================================================================== *)
(* §E 引擎接口槽（按 设计书异常#1 发形令：单面 cage 两件新形）       *)
(* ================================================================== *)

Definition piu_zz_eventual_le (r : Q) (mag : nat -> Q) : Set :=
  { N : nat & forall n : nat, (N <= n)%nat ->
      QleT' (mag n) (piu_zz_qpow r n) }.
Definition piu_zz_eventual_ge (r : Q) (mag : nat -> Q) : Set :=
  { N : nat & forall n : nat, (N <= n)%nat ->
      QleT' (piu_zz_qpow r n) (mag n) }.

(* 偶奇 Set 级决策（Prop 版 Even_or_Odd 禁打 Set 目标；本包自带，零假设） *)
Lemma piu_zz_even_odd_sig : forall n : nat,
  { m : nat & (n = 2 * m)%nat } + { m : nat & (n = 2 * m + 1)%nat }.
Proof.
  intros n. induction n as [|k IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[m Hm] | [m Hm]].
    + right. exists m. rewrite Hm. lia.
    + left. exists (S m). rewrite Hm. lia.
Qed.

(* ================================================================== *)
(* §F 主交付：τ 面 / LOW 面 / 渐近非零（mag 抽象；E 侧载体债=①/衔接件，
   本包全部输出对任意 mag : nat -> Q 有效；W5：守卫 N0≤n，n0zz 入见证）  *)
(* ================================================================== *)

Theorem piu_zz_tau_face (mag : nat -> Q)
  (Hcage : piu_zz_eventual_le piu_zz_rho_u mag) :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
    QleT' (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q
          (piu_zz_qpow (1 # 6)%Q n) }.
Proof.
  destruct HLn_rate_up as [Nu Hu]. destruct Hcage as [Nc Hc].
  exists (Nat.max piu_zz_n0zz (Nat.max Nu Nc)).
  intros n Hn. apply Nat.max_lub_iff in Hn. destruct Hn as [Hn1 Hn2].
  apply Nat.max_lub_iff in Hn2. destruct Hn2 as [Hn2 Hn3].
  unfold piu_zz_n0zz in Hn1.
  assert (HL0 := piu_zz_zL_nonneg n).
  destruct HL0 as [HL0].
  assert (Hrn0 : QleT' 0%Q (piu_zz_qpow piu_zz_rho_u n))
    by (apply (piu_zz_qpow_nonneg n piu_zz_rho_u);
        unfold piu_zz_rho_u, Qle, Qnum, Qden; cbn; lia).
  destruct Hrn0 as [Hrn].
  destruct (Hc n Hn3) as [Hc'].
  apply (piu_zz_QleT_trans
           (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q
           (piu_zz_c2fac n * zq (zz_L n) * piu_zz_qpow piu_zz_rho_u n)%Q
           (piu_zz_qpow (1 # 6)%Q n)).
  - apply qleT_intro.
    rewrite (Qmult_comm (piu_zz_c2fac n * zq (zz_L n)) (mag n)).
    rewrite (Qmult_comm (piu_zz_c2fac n * zq (zz_L n))
              (piu_zz_qpow piu_zz_rho_u n)).
    apply Qmult_le_compat_r.
    + exact Hc'.
    + apply Qmult_le_0_compat;
        [destruct (piu_zz_c2fac_nonneg n) as [H1]; exact H1 | exact HL0].
  - destruct (piu_zz_even_odd_sig n) as [[m Hm] | [m Hm]]; subst n.
    + apply (piu_zz_QleT_trans
               (piu_zz_c2fac (2 * m)%nat * zq (zz_L (2 * m)%nat)
                * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
               (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_u (2 * m)%nat
                * piu_zz_qpow piu_zz_rho_u (2 * m)%nat)
               (piu_zz_qpow (1 # 6)%Q (2 * m)%nat)).
      * apply piu_zz_mul3_mono.
        -- apply piu_zz_QleT_refl.
        -- apply Hu. exact Hn2.
        -- apply piu_zz_QleT_refl.
        -- destruct (piu_zz_c2fac_nonneg (2 * m)%nat) as [H1]. exact H1.
        -- exact HL0.
        -- exact Hrn.
      * apply piu_zz_tau_even_core. lia.
    + apply (piu_zz_QleT_trans
               (piu_zz_c2fac (2 * m + 1)%nat * zq (zz_L (2 * m + 1)%nat)
                * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
               (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_u (2 * m + 1)%nat
                * piu_zz_qpow piu_zz_rho_u (2 * m + 1)%nat)
               (piu_zz_qpow (1 # 6)%Q (2 * m + 1)%nat)).
      * apply piu_zz_mul3_mono.
        -- apply piu_zz_QleT_refl.
        -- apply Hu. exact Hn2.
        -- apply piu_zz_QleT_refl.
        -- destruct (piu_zz_c2fac_nonneg (2 * m + 1)%nat) as [H1]. exact H1.
        -- exact HL0.
        -- exact Hrn.
      * apply piu_zz_tau_odd_core. lia.
Qed.

Theorem piu_zz_low_face (mag : nat -> Q)
  (Hcage : piu_zz_eventual_ge piu_zz_rho_l mag) :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
    QleT' (piu_zz_qpow (1 # 40)%Q n)
          (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q }.
Proof.
  destruct HLn_rate_lo as [Nl Hl]. destruct Hcage as [Nc Hc].
  exists (Nat.max Nl Nc).
  intros n Hn. apply Nat.max_lub_iff in Hn. destruct Hn as [Hnl Hnc].
  destruct (piu_zz_even_odd_sig n) as [[m Hm] | [m Hm]]; subst n.
  - apply (piu_zz_QleT_trans (piu_zz_qpow (1 # 40)%Q (2 * m)%nat)
             (piu_zz_c2fac (2 * m)%nat * piu_zz_qpow piu_zz_lam_l (2 * m)%nat
              * piu_zz_qpow piu_zz_rho_l (2 * m)%nat)
             (piu_zz_c2fac (2 * m)%nat * zq (zz_L (2 * m)%nat) * mag (2 * m)%nat)).
    + apply piu_zz_low_even_core.
    + apply piu_zz_mul3_mono.
      * apply piu_zz_QleT_refl.
      * apply Hl. exact Hnl.
      * apply Hc. exact Hnc.
      * destruct (piu_zz_c2fac_nonneg (2 * m)%nat) as [H1]. exact H1.
      * destruct (piu_zz_qpow_nonneg (2 * m) piu_zz_lam_l
                   ltac:(unfold piu_zz_lam_l, Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
      * destruct (piu_zz_qpow_nonneg (2 * m) piu_zz_rho_l
                   ltac:(unfold piu_zz_rho_l, Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
  - apply (piu_zz_QleT_trans (piu_zz_qpow (1 # 40)%Q (2 * m + 1)%nat)
             (piu_zz_c2fac (2 * m + 1)%nat * piu_zz_qpow piu_zz_lam_l (2 * m + 1)%nat
              * piu_zz_qpow piu_zz_rho_l (2 * m + 1)%nat)
             (piu_zz_c2fac (2 * m + 1)%nat * zq (zz_L (2 * m + 1)%nat)
              * mag (2 * m + 1)%nat)).
    + apply piu_zz_low_odd_core.
    + apply piu_zz_mul3_mono.
      * apply piu_zz_QleT_refl.
      * apply Hl. exact Hnl.
      * apply Hc. exact Hnc.
      * destruct (piu_zz_c2fac_nonneg (2 * m + 1)%nat) as [H1]. exact H1.
      * destruct (piu_zz_qpow_nonneg (2 * m + 1) piu_zz_lam_l
                   ltac:(unfold piu_zz_lam_l, Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
      * destruct (piu_zz_qpow_nonneg (2 * m + 1) piu_zz_rho_l
                   ltac:(unfold piu_zz_rho_l, Qle, Qnum, Qden; cbn; lia)) as [H1].
        exact H1.
Qed.

Theorem piu_zz_wq_pos (mag : nat -> Q)
  (Hcage : piu_zz_eventual_ge piu_zz_rho_l mag) :
  { N0 : nat & forall n : nat, (N0 <= n)%nat ->
    QneqT 0%Q (piu_zz_c2fac n * zq (zz_L n) * mag n)%Q }.
Proof.
  destruct (piu_zz_low_face mag Hcage) as [N0 Hlow].
  exists N0. intros n Hn. destruct (Hlow n Hn) as [Hle].
  apply qneqT_intro. intro Heq.
  assert (Hlt : (0 < piu_zz_c2fac n * zq (zz_L n) * mag n)%Q).
  { apply (Qlt_le_trans 0%Q (piu_zz_qpow (1 # 40)%Q n)
             (piu_zz_c2fac n * zq (zz_L n) * mag n)).
    - destruct (piu_zz_qpow_pos n ((1) # 40)%Q
          ltac:(unfold Qlt, Qnum, Qden; cbn; lia)) as [Ht40].
      exact Ht40.
    - exact Hle. }
  rewrite <- Heq in Hlt.
  unfold Qlt, Qnum, Qden in Hlt. cbn in Hlt. lia.
Qed.

(* ================================================================== *)
(* §V 样点带（V1：真值冻结；设计书「up 全 true」系机外预估伤——
   8/16/32/128 红，照 V1 条上报不换样不改假设；扩样 256/512/1024 本件
   增测（响亮登记）：up 全 false、lo 全 true——N0 领地在样点带之外）     *)
(* ================================================================== *)

Definition piu_zz_up_ok (n : nat) : bool :=
  Qle_bool (zq (zz_L n)) (piu_zz_qpow piu_zz_lam_u n).
Definition piu_zz_lo_ok (n : nat) : bool :=
  Qle_bool (piu_zz_qpow piu_zz_lam_l n) (zq (zz_L n)).

(* ---------------------------------------------------------------- *)
(* 大尺寸样点的字面值链：zz_lcm_range 与 zz_prodf 的区间段分解。       *)
(* 每个字面值引理的核验成本是一次已规格化整数上的乘除或一段定宽迭代，  *)
(* 各字面值由计算等式逐段自证，样点判定最终只留一次布尔比较。          *)
(* ---------------------------------------------------------------- *)

Fixpoint piu_zz_zlcm_seg (lo len : nat) {struct len} : Z :=
  match len with
  | 0%nat => 1%Z
  | S l => Z.lcm (piu_zz_zlcm_seg lo l) (Z.of_nat (S (lo + l))%nat)
  end.

Lemma piu_zz_zlcm_range_nonneg : forall K : nat, (0 <= zz_lcm_range K)%Z.
Proof.
  intros K. induction K as [|K' IH].
  - cbn [zz_lcm_range]. lia.
  - cbn [zz_lcm_range]. apply Z.lcm_nonneg.
Qed.

Lemma piu_zz_zlcm_one_r : forall z : Z, (0 <= z)%Z -> Z.lcm z 1%Z = z.
Proof. intros z Hz. rewrite Z.lcm_1_r. apply Z.abs_eq. exact Hz. Qed.

Lemma piu_zz_zlcm_range_seg : forall k len : nat,
  zz_lcm_range (k + len)%nat = Z.lcm (zz_lcm_range k) (piu_zz_zlcm_seg k len).
Proof.
  intros k len. induction len as [|l IH].
  - cbn [piu_zz_zlcm_seg]. rewrite Nat.add_0_r.
    rewrite piu_zz_zlcm_one_r by apply piu_zz_zlcm_range_nonneg. reflexivity.
  - replace (k + S l)%nat with (S (k + l))%nat by lia.
    cbn [zz_lcm_range piu_zz_zlcm_seg]. rewrite IH.
    symmetry. apply Z.lcm_assoc.
Qed.

Fixpoint piu_zz_zprod_seg (n lo len : nat) {struct len} : Z :=
  match len with
  | 0%nat => 1%Z
  | S l =>
      piu_zz_zprod_seg n lo l
      * (if zz_in_Pn n (S (lo + l))%nat then Z.of_nat (S (lo + l))%nat else 1%Z)
  end.

Lemma piu_zz_zprod_merge : forall n x y : nat,
  zz_prodf n (x + y)%nat = zz_prodf n x * piu_zz_zprod_seg n x y.
Proof.
  intros n x y. induction y as [|c IH].
  - cbn [piu_zz_zprod_seg]. rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
  - replace (x + S c)%nat with (S (x + c))%nat by lia.
    cbn [zz_prodf piu_zz_zprod_seg]. rewrite IH.
    destruct (zz_in_Pn n (S (x + c))%nat).
    + symmetry. apply Z.mul_assoc.
    + rewrite Z.mul_1_r. reflexivity.
Qed.

(* 试除的整除命中：区间内存在因子时 zz_nodiv_upto 判 false。 *)
Lemma piu_zz_zofnat_ltb2 : forall m : nat, (2 <= m)%nat -> Z.ltb (Z.of_nat m) 2 = false.
Proof. intros m Hm. apply Z.ltb_ge. lia. Qed.

Lemma piu_zz_nodiv_upto_hit : forall (k : Z) (d e : nat),
  (2 <= e)%nat -> (e <= d)%nat ->
  (k mod Z.of_nat e)%Z = 0%Z ->
  zz_nodiv_upto k d = false.
Proof.
  intros k d e H2 Hle Hmod. induction d as [|d' IH].
  - exfalso. lia.
  - assert (Hg : Z.ltb (Z.of_nat (S d')) 2 = false) by (apply Z.ltb_ge; lia).
    cbn [zz_nodiv_upto]. rewrite Hg.
    destruct (Nat.eq_dec e (S d')) as [Heq | Hne].
    + subst e. rewrite Hmod. reflexivity.
    + assert (Hle' : (e <= d')%nat) by lia.
      rewrite (IH Hle').
      destruct (Z.eqb (k mod Z.of_nat (S d')) 0); reflexivity.
Qed.
(* zz_lcm_range 字面值链：512 基准与 1024/2048/4096 单段合并。 *)
Definition piu_zz_lit_lcm_512 : Z := 37502641566909080909774372402973685284974612296925670251719288153975177600052224658419106726814633548114580543484744358444505293773294084252491062491589656945636456083649455529431070527198260042812115280192232693996980672000%Z.
Lemma piu_zz_lcmr_512 : zz_lcm_range 512 = piu_zz_lit_lcm_512.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_lcmseg_512_512 : Z := 15161806181366890704755537519628428221282838501257142250824360639698299050776571382489681778825684381429314058890905101687022024744606800532531764952734582389201393752832486383043169059475949454418063248428056646723694341952991408637386677631205400831455008554143754794994126167401137152222379676492247471515691285702536834646805381995650206229354446213284302569283840180834930263739794772017863585682362821412785936104792844891075228278568320000%Z.
Lemma piu_zz_lcmseg_512_512 : piu_zz_zlcm_seg 512 512 = piu_zz_lit_lcmseg_512_512.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_lcm_1024 : Z := 15161806181366890704755537519628428221282838501257142250824360639698299050776571382489681778825684381429314058890905101687022024744606800532531764952734582389201393752832486383043169059475949454418063248428056646723694341952991408637386677631205400831455008554143754794994126167401137152222379676492247471515691285702536834646805381995650206229354446213284302569283840180834930263739794772017863585682362821412785936104792844891075228278568320000%Z.
Lemma piu_zz_lcmr_1024 : zz_lcm_range 1024 = piu_zz_lit_lcm_1024.
Proof.
  replace 1024%nat with (512 + 512)%nat by lia.
  rewrite piu_zz_zlcm_range_seg, piu_zz_lcmr_512, piu_zz_lcmseg_512_512.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_lcmseg_1024_1024 : Z := 20591953221176029912065848883808743401938953974014254537658744318254458241899705686371760507721376952232041902698117643280246024072164894629410126914658512554389865666743223280511943175030355269218674185776403068973029211588501999878119266063164313169778293938522228862495231753667229602303898459702537377893101866470303824280752528437009109012601467993814743071065478560255854516319174739158421224152048481946665821119656661287994438368148294903214822604900483351709160774817653653257742944598803657723538937637013730136488226555560677903403803958055598674481339415054538859296661358768579464651725929477210769416560674308771428943859968917656640318808248101864574519691909094949018864513281412019224917841768142327436578093184142649070684643493518379582291447547053388901688986757901078174223933970334898454126055046929101300469699420821890261913274691652885600434442253193938571520000%Z.
Lemma piu_zz_lcmseg_1024_1024 : piu_zz_zlcm_seg 1024 1024 = piu_zz_lit_lcmseg_1024_1024.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_lcm_2048 : Z := 20591953221176029912065848883808743401938953974014254537658744318254458241899705686371760507721376952232041902698117643280246024072164894629410126914658512554389865666743223280511943175030355269218674185776403068973029211588501999878119266063164313169778293938522228862495231753667229602303898459702537377893101866470303824280752528437009109012601467993814743071065478560255854516319174739158421224152048481946665821119656661287994438368148294903214822604900483351709160774817653653257742944598803657723538937637013730136488226555560677903403803958055598674481339415054538859296661358768579464651725929477210769416560674308771428943859968917656640318808248101864574519691909094949018864513281412019224917841768142327436578093184142649070684643493518379582291447547053388901688986757901078174223933970334898454126055046929101300469699420821890261913274691652885600434442253193938571520000%Z.
Lemma piu_zz_lcmr_2048 : zz_lcm_range 2048 = piu_zz_lit_lcm_2048.
Proof.
  replace 2048%nat with (1024 + 1024)%nat by lia.
  rewrite piu_zz_zlcm_range_seg, piu_zz_lcmr_1024, piu_zz_lcmseg_1024_1024.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_lcmseg_2048_2048 : Z := 30775068816701134298207426969956249464889492250759610008953942871958345023607415651718561640076862588289151161014914885838383595000589437531779091217718444413042260933800586775731372356680018323349333639964179046087670924256844033023976357294465609837450896293470092363846597394119591147041820947728511577908597258937440448691028574113193082192256282521623141369722116564576291006772932683843223020535777443974782766685045588727737830062549515944486076320242513264645325050850314035151522103645363855180521430199812544536785080574799545414895316213153065707391507474649948494031013979774842329773328527619587273065023375841436788087361553872383524160912781058479973203647725738216832496930699453145954860671353600141323604350756466379670010161755529634798210656938394970456954147767894958883347543933508318081176447378021037038430137948930174739191815943316377457736015204434676547529016610820783455770257348481657283825396069451069788089106264394178683874382222775691961203063164077705582770820460075660712461568134253046293493355839884813875874365360136006362392826210010012899558680116246518407899801002969488044149110244972628209061248963893120367195235629751860866410741709407480985718287351558306349152284599607390566295904113504518699900753571671949913717879782134957489931053214662957559529015781388948439423308088586244536448614340485773410276639114149202697905398516429234210131052738474334737855097823779968757304304244220362723445581122327623605272661142224349931601167857126951880680263741187519638701863179829573543524703057358108643221224920065635288859939933713033060415960979338157107720469072980604510644806045341445027645345314190890888126597045288160250428514683552233600759289271101459214666203013436741790431180840659114316559267241245075997095302435263142400000%Z.
Lemma piu_zz_lcmseg_2048_2048 : piu_zz_zlcm_seg 2048 2048 = piu_zz_lit_lcmseg_2048_2048.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_lcm_4096 : Z := 30775068816701134298207426969956249464889492250759610008953942871958345023607415651718561640076862588289151161014914885838383595000589437531779091217718444413042260933800586775731372356680018323349333639964179046087670924256844033023976357294465609837450896293470092363846597394119591147041820947728511577908597258937440448691028574113193082192256282521623141369722116564576291006772932683843223020535777443974782766685045588727737830062549515944486076320242513264645325050850314035151522103645363855180521430199812544536785080574799545414895316213153065707391507474649948494031013979774842329773328527619587273065023375841436788087361553872383524160912781058479973203647725738216832496930699453145954860671353600141323604350756466379670010161755529634798210656938394970456954147767894958883347543933508318081176447378021037038430137948930174739191815943316377457736015204434676547529016610820783455770257348481657283825396069451069788089106264394178683874382222775691961203063164077705582770820460075660712461568134253046293493355839884813875874365360136006362392826210010012899558680116246518407899801002969488044149110244972628209061248963893120367195235629751860866410741709407480985718287351558306349152284599607390566295904113504518699900753571671949913717879782134957489931053214662957559529015781388948439423308088586244536448614340485773410276639114149202697905398516429234210131052738474334737855097823779968757304304244220362723445581122327623605272661142224349931601167857126951880680263741187519638701863179829573543524703057358108643221224920065635288859939933713033060415960979338157107720469072980604510644806045341445027645345314190890888126597045288160250428514683552233600759289271101459214666203013436741790431180840659114316559267241245075997095302435263142400000%Z.
Lemma piu_zz_lcmr_4096 : zz_lcm_range 4096 = piu_zz_lit_lcm_4096.
Proof.
  replace 4096%nat with (2048 + 2048)%nat by lia.
  rewrite piu_zz_zlcm_range_seg, piu_zz_lcmr_2048, piu_zz_lcmseg_2048_2048.
  vm_compute. reflexivity.
Qed.

(* zz_in_Pn 逐点表：合数走最小素因子见证，败叶走廉价叶计算，
   过窗素数保留一次全量试除。 *)
End PiuzzTauEnclosure.
