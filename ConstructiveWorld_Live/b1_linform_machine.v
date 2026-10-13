(* 模块：b1_linform_machine.v —— π 系数整值线性形式机
   （Euler arctan 连分式脊柱）。使命：arctan(1) = π/4 的 Euler 连分式
   1/(1 + 1²/(3 + 2²/(5 + 3²/(7 + …)))) 的收敛子对 (p_n, q_n) ∈ Z²，
   三项递归 p_n = (2n+1)p_n + n²p_{n−1}（一步对偶态 (P_n, P_{n−1}) 携带）
   显式生成；闭合面：
     ①行列式恒等式 b1cf_detT n = p_{Sn}q_n − p_n q_{Sn} = (−1)ⁿ(n!)²
       （一步折叠 b1cf_det_step：D_{Sn} = −(Sn)²·D_n，双步归一案）；
     ②分母正性 q_n ≥ 1 与单调 q_n ≤ q_{Sn}（QltT Set 桥）；
     ③增长率肢 q_{Sn} ≤ (Sn)²·q_n 与望远镜 q_n ≤ (n!)²；
     ④数值锚（p/q 表、行列式——独立复算比对点）。
   与 Beukers 积分 I_n 的 |q_n·π/4 − p_n| = D_n·I_n 型恒等式需实积分
   语义，由竞争判定件的具名供给槽承载（不在本件）。
   依赖：S01_BaseRing（QeqT/QltT/Id）、S02_CauchyComplete、
   b1_kernel_pointwise；Stdlib ZArith/Arith/Factorial/Lia。
   对标：witness 先例件的四可迁移机形对位迁移线。
   构造性：主语句面全 Set（QeqT/QltT）；证明体 Z 层为命题面推理载体
   （律二：体内构造性 Prop 推导合法），Set 面经显式桥引理由 Z 事实补全；
   Z 层环恒等式经 micromega 线性化（合法辅助整理步；本机 Z-ring 战术
   损坏已在册登记，线性化通路不受影响）；零公理、零承认、零经典逻辑。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" b1_linform_machine.v。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith
  Arith.Factorial Lia.
From Stdlib Require Import Setoid Morphisms Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import b1_kernel_pointwise.

Open Scope Z_scope.
Open Scope Q_scope.

(* ========== §0 Z→Q Set 桥与算术证书 ========== *)

(* Z 相等 → QeqT(#1 嵌入) *)
Lemma b1_zeq_qeqT1 : forall a b : Z, (a = b)%Z -> QeqT (a # 1) (b # 1).
Proof.
  intros a b Hab.
  assert (Hq : (a # 1)%Q == (b # 1)%Q).
  { unfold Qeq. cbn [Qnum Qden].
    rewrite Z.mul_1_r, Z.mul_1_r, Hab. reflexivity. }
  exact (qeq_imp_qeqT ((a # 1)%Q) ((b # 1)%Q) Hq).
Qed.

(* Z 序 1 ≤ z → QltT 0 (z#1)（严格档） *)
Lemma b1_zle1_qltT0 : forall z : Z, (1 <= z)%Z -> QltT 0 (z # 1).
Proof.
  intros z Hz. unfold QltT, Qlt_bool, Qcompare, Qle. cbn [Qnum Qden].
  rewrite Z.mul_0_l, Z.mul_1_r.
  destruct (0 ?= z)%Z eqn:Ez.
  - exfalso. apply (proj1 (Z.compare_eq_iff 0 z)) in Ez. lia.
  - reflexivity.
  - exfalso. apply (proj1 (Z.compare_gt_iff 0 z)) in Ez. lia.
Qed.

(* 2k+3 ≤ (k+2)²（完全平方折叠：(k+2)² = (k+1)² + (2k+3)，(k+1)² ≥ 0） *)
Lemma b1_sq_ge_2k3 : forall k : Z, (2 * k + 3 <= (k + 2) * (k + 2))%Z.
Proof.
  intro k.
  assert (Hp : (0 <= (k + 1) * (k + 1))%Z) by (apply b1_zsq_nonneg).
  replace ((k + 2) * (k + 2))%Z
    with ((k + 1) * (k + 1) + (2 * k + 3))%Z by lia.
  apply (Z.le_trans (2 * k + 3) (0 + (2 * k + 3))%Z
                    ((k + 1) * (k + 1) + (2 * k + 3))%Z).
  - rewrite Z.add_0_l. apply Z.le_refl.
  - apply (Zplus_le_compat_r 0 ((k + 1) * (k + 1)) (2 * k + 3)). exact Hp.
Qed.

(* 1 ≤ S n（nat 局部件） *)
Lemma b1_1leS : forall n : nat, (1 <= Datatypes.S n)%nat.
Proof. intro n. apply (proj1 (Nat.succ_le_mono 0 n)). apply Nat.le_0_l. Qed.

(* 1 ≤ z → Z.pos (Z.to_pos z) = z（positive 读形还原） *)
Lemma b1_zpos_of : forall z : Z, (1 <= z)%Z -> Z.pos (Z.to_pos z) = z.
Proof.
  intro z. destruct z as [| p | p]; cbn [Z.to_pos];
    [ lia | reflexivity | lia ].
Qed.

(* ========== §1 连分式收敛子（一步对偶态递归，守卫安全形） ========== *)

Fixpoint b1cfP (n : nat) : Z * Z :=
  match n with
  | O => (0%Z, 0%Z)
  | Datatypes.S n0 =>
      match n0 with
      | O => (1%Z, 0%Z)
      | Datatypes.S k =>
          let (p1, p2) := b1cfP n0 in
          ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * p1
            + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * p2)%Z,
           p1)
      end
  end.

Fixpoint b1cfQ (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 1%Z)
  | Datatypes.S n0 =>
      match n0 with
      | O => (1%Z, 1%Z)
      | Datatypes.S k =>
          let (q1, q2) := b1cfQ n0 in
          ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * q1
            + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * q2)%Z,
           q1)
      end
  end.

Definition b1cf_p (n : nat) : Z := fst (b1cfP n).
Definition b1cf_q (n : nat) : Z := fst (b1cfQ n).

Lemma b1cf_p0 : b1cf_p 0 = 0%Z. Proof. reflexivity. Qed.
Lemma b1cf_p1 : b1cf_p 1 = 1%Z. Proof. reflexivity. Qed.
Lemma b1cf_q0 : b1cf_q 0 = 1%Z. Proof. reflexivity. Qed.
Lemma b1cf_q1 : b1cf_q 1 = 1%Z. Proof. reflexivity. Qed.

(* 二步展开（定义性；iota 全约简） *)
Lemma b1cfP_stepS : forall k : nat,
  b1cfP (Datatypes.S (Datatypes.S k))
  = let (p1, p2) := b1cfP (Datatypes.S k) in
    ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * p1
      + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * p2)%Z, p1).
Proof. intros k. reflexivity. Qed.

Lemma b1cfQ_stepS : forall k : nat,
  b1cfQ (Datatypes.S (Datatypes.S k))
  = let (q1, q2) := b1cfQ (Datatypes.S k) in
    ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * q1
      + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * q2)%Z, q1).
Proof. intros k. reflexivity. Qed.

(* 一步递归展开（对偶态；n ≥ 1 域，基档例外由前提排除） *)
Lemma b1cf_p_unfold1 : forall n : nat, (1 <= n)%nat ->
  b1cf_p (Datatypes.S n)
  = (Z.of_nat ((2 * n + 1)%nat) * fst (b1cfP n)
     + Z.of_nat n * Z.of_nat n * snd (b1cfP n))%Z.
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - unfold b1cf_p.
    rewrite (b1cfP_stepS k).
    destruct (b1cfP (Datatypes.S k)) as [a b].
    reflexivity.
Qed.

Lemma b1cf_q_unfold1 : forall n : nat, (1 <= n)%nat ->
  b1cf_q (Datatypes.S n)
  = (Z.of_nat ((2 * n + 1)%nat) * fst (b1cfQ n)
     + Z.of_nat n * Z.of_nat n * snd (b1cfQ n))%Z.
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - unfold b1cf_q.
    rewrite (b1cfQ_stepS k).
    destruct (b1cfQ (Datatypes.S k)) as [a b].
    reflexivity.
Qed.

(* 对偶态第二位面（fst 形）：snd (b1cfP (S n)) = P_n、snd (b1cfQ (S n)) = Q_n *)
Lemma b1cf_p_snd_f : forall n : nat, snd (b1cfP (Datatypes.S n)) = fst (b1cfP n).
Proof.
  intros n. destruct n as [| k].
  - reflexivity.
  - rewrite (b1cfP_stepS k).
    destruct (b1cfP (Datatypes.S k)) as [a b].
    reflexivity.
Qed.

Lemma b1cf_q_snd_f : forall n : nat, snd (b1cfQ (Datatypes.S n)) = fst (b1cfQ n).
Proof.
  intros n. destruct n as [| k].
  - reflexivity.
  - rewrite (b1cfQ_stepS k).
    destruct (b1cfQ (Datatypes.S k)) as [a b].
    reflexivity.
Qed.

(* ========== §2 行列式恒等式（主铸承重） ========== *)

(* D_n := p_{Sn}·q_n − p_n·q_{Sn} *)
Definition b1cf_detT (n : nat) : Z :=
  (b1cf_p (Datatypes.S n) * b1cf_q n - b1cf_p n * b1cf_q (Datatypes.S n))%Z.

(* 线性形式消去核：(t·a + v·b)·c − a·(t·c + v·d) = −v·(a·d − b·c)
   （全整数变元恒等式；纯分配律＋对消） *)
Lemma b1_z_lform_core : forall a b c d t v : Z,
  ((t * a + v * b) * c - a * (t * c + v * d)
   = (-(v)) * (a * d - b * c))%Z.
Proof. intros a b c d t v. lia. Qed.

(* 行列式步核：−(x²)·(p f²) = (−p)·(xf)·(xf)（全整数变元恒等式） *)
Lemma b1_z_det_core : forall x f p : Z,
  ((-(x * x)) * (p * f * f) = (Z.opp 1 * p) * (x * f) * (x * f))%Z.
Proof. intros x f p. lia. Qed.

(* 一步折叠：D_{Sn} = −(Sn)²·D_n（双步递归展开＋线性形式消去核） *)
Lemma b1cf_det_step : forall n : nat,
  b1cf_detT (Datatypes.S n)
  = (-(Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))
     * b1cf_detT n)%Z.
Proof.
  intro n.
  unfold b1cf_detT.
  rewrite (b1cf_p_unfold1 (Datatypes.S n) (b1_1leS n)).
  rewrite (b1cf_q_unfold1 (Datatypes.S n) (b1_1leS n)).
  rewrite (b1cf_p_snd_f n).
  rewrite (b1cf_q_snd_f n).
  unfold b1cf_p, b1cf_q.
  apply (b1_z_lform_core
          (fst (b1cfP (Datatypes.S n))) (fst (b1cfP n))
          (fst (b1cfQ (Datatypes.S n))) (fst (b1cfQ n))
          (Z.of_nat ((2 * Datatypes.S n + 1)%nat))
          (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))).
Qed.

(* 行列式恒等式（Z 核）：D_n = (−1)ⁿ·(n!)² *)
Theorem b1cf_det_eq : forall n : nat,
  b1cf_detT n
  = (Z.pow (Z.opp 1) (Z.of_nat n) * Z.of_nat (fact n) * Z.of_nat (fact n))%Z.
Proof.
  induction n as [| n IH].
  - unfold b1cf_detT. rewrite b1cf_p1, b1cf_p0, b1cf_q1, b1cf_q0.
    cbn [fact]. reflexivity.
  - rewrite (b1cf_det_step n). rewrite IH.
    (* 本 stdlib 无 Nat.fact_succ/Z.pow_succ_r'（probe 实锤）：fact (S n)
       定义性换岸（cbn [fact] iota＋inj_mul）＋ Z.pow_succ_r（0≤m 前提档，
       m=Z.of_nat n 由 Nat2Z.is_nonneg 供给）显式补全。 *)
    replace (Z.of_nat (fact (Datatypes.S n)))
      with ((Z.of_nat (Datatypes.S n) * Z.of_nat (fact n))%Z)
      by (cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
    replace (Z.of_nat (Datatypes.S n)) with (Z.succ (Z.of_nat n))
      by (rewrite Nat2Z.inj_succ; reflexivity).
    replace (Z.pow (Z.opp 1) (Z.succ (Z.of_nat n)))
      with ((Z.opp 1 * Z.pow (Z.opp 1) (Z.of_nat n))%Z)
      by (symmetry; apply Z.pow_succ_r; apply Nat2Z.is_nonneg).
    apply (b1_z_det_core (Z.succ (Z.of_nat n)) (Z.of_nat (fact n))
                         (Z.pow (Z.opp 1) (Z.of_nat n))).
Qed.

(* 行列式恒等式（Set 证书形） *)
Theorem b1cf_det : forall n : nat,
  QeqT ((b1cf_detT n) # 1)
       ((Z.pow (Z.opp 1) (Z.of_nat n) * Z.of_nat (fact n) * Z.of_nat (fact n)) # 1).
Proof.
  intros n. apply b1_zeq_qeqT1. exact (b1cf_det_eq n).
Qed.

(* ========== §3 分母正性、单调与增长率（Z 核＋Set 桥） ========== *)

(* q ≥ 1（Z 核；双基档对归纳，全部线性链） *)
Lemma b1cf_q_ge1 : forall n : nat, (1 <= b1cf_q n)%Z.
Proof.
  intro n.
  assert (Hpair : forall k : nat,
            (1 <= b1cf_q k)%Z /\ (1 <= b1cf_q (Datatypes.S k))%Z).
  { induction k as [| k IHk].
    - split; [rewrite b1cf_q0 | rewrite b1cf_q1]; apply Z.le_refl.
    - destruct IHk as [H0 H1].
      split.
      + exact H1.
      + rewrite (b1cf_q_unfold1 (Datatypes.S k) (b1_1leS k)).
        (* 本 stdlib 无 Z.mul_le_mono_l/Z.le_add_r（probe 实锤）：
           0≤p 前提档 Z.mul_le_mono_nonneg_l/r ＋ Y≥0 证书 lia 收束替岸 *)
        assert (Hq2 : (1 <= snd (b1cfQ (Datatypes.S k)))%Z).
        { rewrite b1cf_q_snd_f. exact H0. }
        assert (Hx : (0 <= Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k)
                            * snd (b1cfQ (Datatypes.S k)))%Z).
        { assert (Hs0 : (0 <= snd (b1cfQ (Datatypes.S k)))%Z) by lia.
          pose proof (Z.mul_le_mono_nonneg_r 0
            (Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k))
            (snd (b1cfQ (Datatypes.S k))) Hs0
            (b1_zsq_nonneg (Z.of_nat (Datatypes.S k)))) as HH.
          rewrite Z.mul_0_l in HH. exact HH. }
        apply (Z.le_trans 1
                 (Z.of_nat ((2 * Datatypes.S k + 1)%nat)
                  * fst (b1cfQ (Datatypes.S k)))%Z _).
        * apply (Z.le_trans 1
                   (Z.of_nat ((2 * Datatypes.S k + 1)%nat) * 1)%Z _).
          -- rewrite Z.mul_1_r. lia.
          -- apply Z.mul_le_mono_nonneg_l.
             ++ apply Nat2Z.is_nonneg.
             ++ exact H1.
        * lia. }
  exact (proj1 (Hpair n)).
Qed.

(* 分母正性（Set 证书形，严格档） *)
Theorem b1cf_q_pos : forall n : nat, QltT 0 ((b1cf_q n) # 1).
Proof.
  intros n. apply b1_zle1_qltT0. exact (b1cf_q_ge1 n).
Qed.

(* 单调：q_n ≤ q_{Sn}（Z 核；基档两枚＋步档加法支配） *)
Theorem b1cf_q_mono : forall n : nat,
  (b1cf_q n <= b1cf_q (Datatypes.S n))%Z.
Proof.
  intro n.
  assert (Hpair : forall k : nat,
            (b1cf_q k <= b1cf_q (Datatypes.S k))%Z
            /\ (b1cf_q (Datatypes.S k)
                <= b1cf_q (Datatypes.S (Datatypes.S k)))%Z).
  { induction k as [| k IHk].
    - split.
      + rewrite b1cf_q0, b1cf_q1. apply Z.le_refl.
      + rewrite (b1cf_q_unfold1 1 (Nat.le_refl 1)).
        change (b1cf_q 1) with 1%Z.
        change (Z.of_nat ((2 * Datatypes.S 0 + 1)%nat)) with 3%Z.
        change (Z.of_nat (Datatypes.S 0)) with 1%Z.
        change (fst (b1cfQ (Datatypes.S 0))) with 1%Z.
        change (snd (b1cfQ (Datatypes.S 0))) with 1%Z.
        lia.
    - destruct IHk as [H0 H1].
      split.
      + exact H1.
      + rewrite (b1cf_q_unfold1 (Datatypes.S (Datatypes.S k))
                   (b1_1leS (Datatypes.S k))).
        unfold b1cf_q. rewrite b1cf_q_snd_f.
        (* 本 stdlib 无 Z.le_add_l（probe 实锤）：B ≤ c·B（1≤B·1≤c 乘子链）
           ＋ T2 ≥ 0 证书后 lia 收束替岸 *)
        assert (H1B : (1 <= fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z)
          by exact (b1cf_q_ge1 (Datatypes.S (Datatypes.S k))).
        assert (HB : (fst (b1cfQ (Datatypes.S (Datatypes.S k)))
                    <= Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat)
                      * fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z).
        { assert (H0B : (0 <= fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z) by lia.
          assert (Hc1 : (1 <= Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat))%Z)
            by lia.
          pose proof (Z.mul_le_mono_nonneg_r 1
            (Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat))
            (fst (b1cfQ (Datatypes.S (Datatypes.S k)))) H0B Hc1) as HH.
          rewrite Z.mul_1_l in HH. exact HH. }
        assert (HT2 : (0 <= Z.of_nat (Datatypes.S (Datatypes.S k))
                             * Z.of_nat (Datatypes.S (Datatypes.S k))
                             * fst (b1cfQ (Datatypes.S k)))%Z).
        { assert (H1A2 : (1 <= fst (b1cfQ (Datatypes.S k)))%Z)
            by exact (b1cf_q_ge1 (Datatypes.S k)).
          assert (H0A2 : (0 <= fst (b1cfQ (Datatypes.S k)))%Z) by lia.
          pose proof (Z.mul_le_mono_nonneg_r 0
            (Z.of_nat (Datatypes.S (Datatypes.S k)) * Z.of_nat (Datatypes.S (Datatypes.S k)))
            (fst (b1cfQ (Datatypes.S k))) H0A2
            (b1_zsq_nonneg (Z.of_nat (Datatypes.S (Datatypes.S k))))) as HH.
          rewrite Z.mul_0_l in HH. exact HH. }
        lia. }
  exact (proj1 (Hpair n)).
Qed.

(* 平方移位恒等式：(2k+3) + (k+1)² = (k+2)²（Z 读形） *)
Lemma b1_z_sq_shift : forall k : nat,
  (Z.of_nat ((2 * Datatypes.S k + 1)%nat)
  + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k)
  = Z.of_nat (Datatypes.S (Datatypes.S k))
    * Z.of_nat (Datatypes.S (Datatypes.S k)))%Z.
Proof. intro k. lia. Qed.

(* 增长率步：q_{Sn} ≤ (Sn)²·q_n（单调肢＋平方移位） *)
Theorem b1cf_q_growth : forall n : nat,
  (b1cf_q (Datatypes.S n)
   <= Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n) * b1cf_q n)%Z.
Proof.
  induction n as [| n IHn].
  - rewrite b1cf_q1, b1cf_q0.
    change (Z.of_nat (Datatypes.S 0)) with 1%Z.
    apply Z.le_refl.
  - rewrite (b1cf_q_unfold1 (Datatypes.S n) (b1_1leS n)).
    apply (Z.le_trans _ ((Z.of_nat (2 * Datatypes.S n + 1)%nat
                          + Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))
                         * b1cf_q (Datatypes.S n))%Z _).
    + rewrite Z.mul_add_distr_r.
      apply Zplus_le_compat.
      * apply Z.le_refl.
      * apply Z.mul_le_mono_nonneg_l.
        -- apply b1_zsq_nonneg.
        -- rewrite b1cf_q_snd_f. exact (b1cf_q_mono n).
    + rewrite <- (b1_z_sq_shift n). apply Z.le_refl.
Qed.

(* 平方乘积重排：(a²)(f²) = (af)²（Z 恒等式） *)
Lemma b1_z_sq_mul_sq : forall a f : Z,
  ((a * a) * (f * f) = (a * f) * (a * f))%Z.
Proof. intros a f. lia. Qed.

(* 望远镜：q_n ≤ (n!)² *)
Theorem b1cf_q_le_fact_sq : forall n : nat,
  (b1cf_q n <= Z.of_nat (fact n) * Z.of_nat (fact n))%Z.
Proof.
  induction n as [| n IH].
  - rewrite b1cf_q0. cbn [fact].
    change (Z.of_nat 1) with 1%Z. apply Z.le_refl.
  - apply (Z.le_trans _ (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n)
                           * (Z.of_nat (fact n) * Z.of_nat (fact n)))%Z _).
    + apply (Z.le_trans _ (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n)
                             * b1cf_q n)%Z _).
      * exact (b1cf_q_growth n).
      * apply Z.mul_le_mono_nonneg_l.
        -- apply b1_zsq_nonneg.
        -- exact IH.
    + replace (Z.of_nat (fact (Datatypes.S n)))
        with ((Z.of_nat (Datatypes.S n) * Z.of_nat (fact n))%Z)
        by (cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
      rewrite (b1_z_sq_mul_sq (Z.of_nat (Datatypes.S n))
                              (Z.of_nat (fact n))).
      apply Z.le_refl.
Qed.

(* ========== §4 数值锚（独立复算比对点） ========== *)

(* 锚一：p_3 = 19（连分式收敛子 19/24 的分子） *)
Lemma b1cf_p_anchor3 : Id (b1cf_p 3) (19%Z).
Proof. reflexivity. Qed.

(* 锚二：q_3 = 24（分母） *)
Lemma b1cf_q_anchor3 : Id (b1cf_q 3) (24%Z).
Proof. reflexivity. Qed.

(* 锚三：p_4 = 160, q_4 = 204（40/51 的未约分形） *)
Lemma b1cf_p_anchor4 : Id (b1cf_p 4) (160%Z).
Proof. reflexivity. Qed.

Lemma b1cf_q_anchor4 : Id (b1cf_q 4) (204%Z).
Proof. reflexivity. Qed.

(* 锚四：行列式 D_3 = p_4q_3 − p_3q_4 = 3840 − 3876 = −36 = (−1)³·(3!)² *)
Lemma b1cf_det_anchor3 : Id (b1cf_detT 3) ((-36)%Z).
Proof. reflexivity. Qed.

(* 锚五：D_2 = p_3q_2 − p_2q_3 = 76 − 72 = 4 = (−1)²·(2!)² *)
Lemma b1cf_det_anchor2 : Id (b1cf_detT 2) (4%Z).
Proof. reflexivity. Qed.

(* ========== §5 在件检验与假设审计 ========== *)

Check b1cf_det.
Check b1cf_det_eq.
Check b1cf_q_pos.
Check b1cf_q_mono.
Check b1cf_q_growth.
Check b1cf_q_le_fact_sq.

Print Assumptions b1cf_det.
Print Assumptions b1cf_det_eq.
Print Assumptions b1cf_q_pos.
Print Assumptions b1cf_q_mono.
Print Assumptions b1cf_q_le_fact_sq.
