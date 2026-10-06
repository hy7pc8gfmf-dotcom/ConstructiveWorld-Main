(* ============================================================ *)
(* abl_Pr_erdos_core.v —— 素数域第 8 件：Erdős 路线首段核心引理件     *)
(* 模块名：abl_Pr_erdos_core                                        *)
(* 数学使命：DR 件登记「Erdős 全强度未称——二项式系数素数幂分析」     *)
(*   的核心引理件三组：                                              *)
(*   ①层 1a 二项式中项下界：4^n ≤ (2n+1)·C(2n,n)（行和 = 2^{2n}       *)
(*     = 4^n ＋中项为行极大逐点压制，全初等 nat 归纳）；并附严格       *)
(*     上界加强 C(2n,n)+2 ≤ 4^n（n ≥ 1）。                            *)
(*   ②层 1b 素数幂恰一次（Erdős 关键观察，Legendre 定理推论的直接     *)
(*     形）：n < p ≤ 2n 素 p 在 C(2n,n) 中恰出现一次——主语句         *)
(*     pec_mid_exactly_once 给出 { z & C = p·z ∧ C = p·(p·w) → False }；*)
(*     支撑链：Euclid 引理自证（p 素 ∧ p ∣ i·a → p ∣ i ∨ p ∣ a，       *)
(*     良基归纳于 i，试除素性 pr_prime 直接驱动）＋ Pascal 形二项式    *)
(*     的阶乘恒等式 C(m,k)·k!·(m−k)! = m! ＋ fact m 的单 p 分解。     *)
(*   ③层 2 骨架不等式：∏_{n<p≤2n} p 整除 C(2n,n)（窗口素数升积       *)
(*     pec_winprod 的 sigT 整除见证）＋ pec_winprod ≤ C(2n,n) ≤ 4^n   *)
(*     ＋严格形 C(2n,n)+2 ≤ 4^n——Bertrand 全强度核心不等式骨架的      *)
(*     构造性形（配 HansonLcm.hl_central_binom_le 上界半边对拍）。    *)
(*   设计依据：N 素数域设计文书 §③第 3 条（Erdős 路线独立后件）          *)
(*   ＋ Hanson 卡对照                                                   *)
(*   （自建 nat 二项式机先例）。                                      *)
(* 依赖清单：件 1（abl_Pr_core_01：pr_prime／pr_prime_bool，池内拷入   *)
(*   链编）＋HansonLcm（统一缓存根供：hl_binom／hl_binom_S／hl_pow4／  *)
(*   hl_le_t／hl_le_to_le_t／hl_central_binom_le）＋纯 Stdlib         *)
(*   （Arith.Arith／Arith.Factorial／Bool／List／Lia）。               *)
(* 构造性注记：主语句面全 Set 承载——层 1b/层 2 整除主件全 sigT 见证形  *)
(*   （见证项为可计算表达式 pec_mid n / p、pec_mid n / pec_winprod n，  *)
(*   经 pec_dvd_div_eq 整除-除法判定桥装配）；层 1a 下界/严格上界走    *)
(*   hl_le_t（Id (Nat.leb _ _) true，Set 面）承载；Prop 面谓词         *)
(*   （pr_prime、pec_dvd、整除否定肢）仅作推理脚手架（core_01 先例），  *)
(*   否定形自持 P -> False，全件零 not／~／<> 记号书写；零公理零承认   *)
(*   零经典逻辑；良基归纳用 well_founded_induction_type Wf_nat.lt_wf   *)
(*   （core_01 同款，显式 IH）；计算件 pec_sum／pec_win／pec_winprod／  *)
(*   pec_mid 皆一阶 nat Fixpoint 可提取；文末 Separate Extraction＋    *)
(*   Print Assumptions 取证面，Obj.magic 计数零为交付判据之一。        *)
(* 编译配方（链编次序：本池 abl_Pr_core_01 先行，本件随后）：          *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/     *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&    *)
(*   nice -19 rocq c -native-compiler no -Q                            *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 "" *)
(*   -Q . "" abl_Pr_erdos_core.v                                       *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Bool Lia List.
Require Import HansonLcm.
Require Import abl_Pr_core_01.

(* ---- §1 二项式基础面（hl_binom 补引理：对角/越界/首列） ---- *)

(* 越界为零：m < k → C(m,k) = 0（Pascal 形直接归纳） *)
Lemma pec_binom_out : forall m k : nat, m < k -> hl_binom m k = 0.
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - destruct k as [|k'].
    + lia.
    + reflexivity.
  - destruct k as [|k'].
    + lia.
    + rewrite hl_binom_S.
      rewrite (IH k') by lia.
      rewrite (IH (S k')) by lia.
      reflexivity.
Qed.

(* 首列：C(m,0) = 1（fix 仅在首参构造子头部时展开——分档转换，
   内核判定：变量首参连 reflexivity 都无法展开） *)
Lemma pec_binom_zero_r : forall m : nat, hl_binom m 0 = 1.
Proof.
  destruct m as [|m'].
  - reflexivity.
  - reflexivity.
Qed.

(* 对角线：C(m,m) = 1 *)
Lemma pec_binom_diag : forall m : nat, hl_binom m m = 1.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - rewrite hl_binom_S. rewrite IH.
    rewrite (pec_binom_out m (S m) (Nat.lt_succ_diag_r m)).
    reflexivity.
Qed.

(* 非负性下界：k ≤ m → 1 ≤ C(m,k) *)
Lemma pec_binom_pos : forall m k : nat, k <= m -> 1 <= hl_binom m k.
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [|k'].
    + cbn [hl_binom]. lia.
    + rewrite hl_binom_S.
      assert (H1 : 1 <= hl_binom m k') by (apply IH; lia).
      assert (H2 : 0 <= hl_binom m (S k')) by apply Nat.le_0_l.
      lia.
Qed.

(* 第二列：C(m,1) = m *)
Lemma pec_binom_1 : forall m : nat, hl_binom m 1 = m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - change (hl_binom (S m) 1) with (hl_binom (S m) (S 0)).
    rewrite hl_binom_S. rewrite pec_binom_zero_r. rewrite IH. lia.
Qed.

(* ---- §2 折叠和机：pec_sum f n = Σ_{i<n} f i ---- *)

Fixpoint pec_sum (f : nat -> nat) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => pec_sum f n' + f n'
  end.

Lemma pec_sum_first : forall (n : nat) (f : nat -> nat),
  pec_sum f (S n) = f 0 + pec_sum (fun i => f (S i)) n.
Proof.
  induction n as [|n IH]; intros f.
  - cbn [pec_sum]. lia.
  - assert (Hsp : pec_sum f (S (S n)) = pec_sum f (S n) + f (S n)) by reflexivity.
    rewrite Hsp. rewrite IH. cbn [pec_sum] in *. lia.
Qed.

Lemma pec_sum_add : forall (n : nat) (f g : nat -> nat),
  pec_sum (fun i => f i + g i) n = pec_sum f n + pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g.
  - reflexivity.
  - cbn [pec_sum]. rewrite IH. lia.
Qed.

Lemma pec_sum_ext : forall (n : nat) (f g : nat -> nat),
  (forall i : nat, i < n -> f i = g i) -> pec_sum f n = pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g H.
  - reflexivity.
  - cbn [pec_sum]. rewrite (IH f g) by (intros i Hi; apply H; lia).
    rewrite (H n (Nat.lt_succ_diag_r n)). reflexivity.
Qed.

Lemma pec_sum_le : forall (n : nat) (f g : nat -> nat),
  (forall i : nat, i < n -> f i <= g i) -> pec_sum f n <= pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g H.
  - cbn [pec_sum]. lia.
  - cbn [pec_sum].
    assert (Hrec : pec_sum f n <= pec_sum g n) by (apply IH; intros i Hi; apply H; lia).
    pose proof (H n (Nat.lt_succ_diag_r n)). lia.
Qed.

Lemma pec_sum_const : forall n c : nat, pec_sum (fun _ => c) (S n) = S n * c.
Proof.
  induction n as [|n IH]; intros c.
  - cbn [pec_sum]. lia.
  - assert (Hsp : pec_sum (fun _ => c) (S (S n)) = pec_sum (fun _ => c) (S n) + c)
      by reflexivity.
    rewrite Hsp, IH. lia.
Qed.

Lemma pec_sum_ge : forall (n i : nat) (f : nat -> nat), i < n -> f i <= pec_sum f n.
Proof.
  induction n as [|n IH]; intros i f Hi.
  - lia.
  - cbn [pec_sum]. destruct (Nat.eq_dec i n) as [E|NE].
    + subst i. lia.
    + assert (Hrec : f i <= pec_sum f n) by (apply IH; lia).
      lia.
Qed.

(* 行和主件：Σ_{k≤m} C(m,k) = 2^m（Pascal 双拆：首项 1 ＋ 移位行
   = (2^m−1) + (2^m−1)，全部原子化 lia 闭合） *)
Lemma pec_row_sum : forall m : nat, pec_sum (hl_binom m) (S m) = 2 ^ m.
Proof.
  induction m as [|m IH].
  - cbn [pec_sum hl_binom Nat.pow]. lia.
  - assert (Hsp : pec_sum (hl_binom (S m)) (S (S m))
                = pec_sum (hl_binom (S m)) (S m) + hl_binom (S m) (S m))
      by reflexivity.
    rewrite Hsp. rewrite pec_binom_diag.
    rewrite (pec_sum_first m (hl_binom (S m))).
    cbn [hl_binom].
    rewrite pec_sum_add.
    assert (H1 : pec_sum (hl_binom m) m + 1 = 2 ^ m).
    { assert (Hsp1 : pec_sum (hl_binom m) (S m) = pec_sum (hl_binom m) m + hl_binom m m)
        by reflexivity.
      rewrite pec_binom_diag in Hsp1. rewrite IH in Hsp1. lia. }
    assert (H2 : 1 + pec_sum (fun i => hl_binom m (S i)) m = 2 ^ m).
    { pose proof (pec_sum_first m (hl_binom m)) as Hf.
      rewrite pec_binom_zero_r in Hf. rewrite IH in Hf. lia. }
    rewrite Nat.pow_succ_r'. lia.
Qed.

(* ---- §3 行单调面：中项为行极大 ---- *)

(* 对称律：k ≤ m → C(m,k) = C(m,m−k)（双肢归纳：越界归零＋对角＋Pascal） *)
Lemma pec_binom_sym : forall m k : nat, k <= m -> hl_binom m k = hl_binom m (m - k).
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [|k'].
    + replace (S m - 0) with (S m) by reflexivity.
      rewrite pec_binom_diag. apply pec_binom_zero_r.
    + rewrite hl_binom_S.
      replace (S m - S k') with (m - k') by reflexivity.
      destruct (m - k') as [|i] eqn:Hi.
      * assert (Hkm : k' = m) by lia. subst k'.
        rewrite pec_binom_diag. rewrite pec_binom_zero_r.
        rewrite pec_binom_out by lia. reflexivity.
      * rewrite (hl_binom_S m i).
        assert (E1 : hl_binom m k' = hl_binom m (S i)).
        { replace (S i) with (m - k') by (rewrite Hi; reflexivity).
          apply (IH k'). lia. }
        assert (E2 : hl_binom m (S k') = hl_binom m i).
        { replace i with (m - S k') by lia.
          apply (IH (S k')). lia. }
        lia.
Qed.

(* 爬升引理：2k+1 ≤ m → C(m,k) ≤ C(m,k+1)。吸收恒等式（自足归纳：
   C(m,k+1)·(k+1) = C(m,k)·(m−k)，S k ≤ m；含 S(k)=a 边界分档）
   ＋乘法单调＋正因子消去。 *)
Lemma pec_mono : forall m k : nat, k + k + 1 <= m -> hl_binom m k <= hl_binom m (S k).
Proof.
  intros m k Hk.
  assert (Hgen : forall a b : nat, S b <= a ->
              hl_binom a (S b) * S b = hl_binom a b * (a - b)).
  { intros a. induction a as [|a IHa]; intros b Hb.
    - lia.
    - destruct b as [|b'].
      + rewrite pec_binom_1. rewrite pec_binom_zero_r.
        replace (S a - 0) with (S a) by reflexivity.
        rewrite Nat.mul_1_r. rewrite Nat.mul_1_l. reflexivity.
      + destruct (Nat.eq_dec (S b') a) as [Eb | NEb].
        * subst a.
          rewrite pec_binom_diag.
          rewrite Nat.mul_1_l.
          rewrite pec_binom_sym by lia.
          replace (S (S b') - S b') with 1 by lia.
          rewrite pec_binom_1.
          rewrite Nat.mul_1_r.
          reflexivity.
        * assert (Hba : S (S b') <= a) by lia.
          rewrite hl_binom_S. replace (S a - S b') with (a - b') by reflexivity.
          rewrite hl_binom_S.
          rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_r.
          rewrite (IHa (S b') Hba).
          assert (Hb' : b' < a) by lia.
          rewrite <- (IHa b' Hb').
          rewrite <- Nat.mul_add_distr_l. rewrite <- Nat.mul_add_distr_l.
          replace (S (S b') + (a - S b')) with (S a) by lia.
          replace (S b' + (a - b')) with (S a) by lia.
          reflexivity. }
  assert (Hab : hl_binom m (S k) * S k = hl_binom m k * (m - k))
    by (apply Hgen; lia).
  assert (HkB : S k <= m - k) by lia.
  assert (Hpos : 0 < m - k) by lia.
  assert (Hstep : hl_binom m (S k) * S k <= hl_binom m (S k) * (m - k))
    by (apply Nat.mul_le_mono_l; exact HkB).
  rewrite Hab in Hstep.
  apply (proj2 (Nat.mul_le_mono_pos_r (hl_binom m k) (hl_binom m (S k)) (m - k) Hpos)).
  exact Hstep.
Qed.

(* 链式爬升：a ≤ b ∧ b+b ≤ m → C(m,a) ≤ C(m,b) *)
Lemma pec_mono_chain : forall m b a : nat,
  a <= b -> b + b <= m -> hl_binom m a <= hl_binom m b.
Proof.
  intros m b. induction b as [|b IH]; intros a Ha Hb.
  - assert (a = 0) by lia. subst a. apply Nat.le_refl.
  - destruct (Nat.eq_dec a (S b)) as [E|NE].
    + subst a. apply Nat.le_refl.
    + assert (Hstep : hl_binom m b <= hl_binom m (S b)) by (apply pec_mono; lia).
      assert (Hrec : hl_binom m a <= hl_binom m b) by (apply IH; lia).
      lia.
Qed.

(* 中项极大：k ≤ 2n → C(2n,k) ≤ C(2n,n)（k ≤ n 直爬；k > n 对称回爬） *)
Lemma pec_max_mid : forall n k : nat, k <= 2 * n -> hl_binom (2 * n) k <= hl_binom (2 * n) n.
Proof.
  intros n k Hk. destruct (le_lt_dec k n) as [Hle | Hgt].
  - apply (pec_mono_chain (2 * n) n k Hle). lia.
  - assert (Hsym : hl_binom (2 * n) k = hl_binom (2 * n) (2 * n - k))
      by (apply pec_binom_sym; lia).
    rewrite Hsym.
    apply (pec_mono_chain (2 * n) n (2 * n - k)); lia.
Qed.

(* ---- §4 层 1a：二项式中项下界（4^n ≤ (2n+1)·C(2n,n)）与严格上界 ---- *)

Lemma pec_lower_nat : forall n : nat, 4 ^ n <= (2 * n + 1) * hl_binom (2 * n) n.
Proof.
  intros n. rewrite hl_pow4. replace (2 * n + 1) with (S (2 * n)) by lia.
  rewrite <- (pec_sum_const (2 * n) (hl_binom (2 * n) n)).
  rewrite <- (pec_row_sum (2 * n)).
  apply pec_sum_le. intros i Hi. apply pec_max_mid. lia.
Qed.

(* 层 1a 主语句（Set 面承载：hl_le_t） *)
Theorem pec_lower : forall n : nat,
  hl_le_t (4 ^ n)%nat ((2 * n + 1) * hl_binom (2 * n) n).
Proof.
  intro n. apply hl_le_to_le_t. exact (pec_lower_nat n).
Qed.

(* 严格上界加强：n ≥ 1 → C(2n,n)+2 ≤ 4^n（行和中另两项 C(2n,0)=1
   与 C(2n,2n)=1 与中项同在——首项拆出＋末端对角＋中项逐点压制） *)
Lemma pec_central_lt : forall n : nat, 1 <= n -> hl_binom (2 * n) n + 2 <= 4 ^ n.
Proof.
  intros n Hn. rewrite hl_pow4. rewrite <- (pec_row_sum (2 * n)).
  rewrite (pec_sum_first (2 * n) (hl_binom (2 * n))).
  rewrite pec_binom_zero_r.
  assert (Htwo : forall (f : nat -> nat) (m i j : nat),
            i < j -> j < m -> f i + f j <= pec_sum f m).
  { intros f m. induction m as [|m IH]; intros i j Hij Hjm.
    - lia.
    - cbn [pec_sum]. destruct (Nat.eq_dec j m) as [Ej | NEj].
      + subst j.
        assert (Hfi : f i <= pec_sum f m) by (apply (pec_sum_ge m i f); lia).
        lia.
      + assert (Hrec : f i + f j <= pec_sum f m) by (apply IH; lia).
        lia. }
  assert (Hij : n - 1 < 2 * n - 1) by lia.
  assert (Hjm : 2 * n - 1 < 2 * n) by lia.
  pose proof (Htwo (fun i => hl_binom (2 * n) (S i)) (2 * n) (n - 1) (2 * n - 1)
              Hij Hjm) as Htwoi.
  cbv beta in Htwoi.
  replace (S (n - 1)) with n in Htwoi by lia.
  replace (S (2 * n - 1)) with (2 * n) in Htwoi by lia.
  rewrite pec_binom_diag in Htwoi.
  lia.
Qed.

(* ---- §5 自足整除面（pec_dvd 显式见证形）与 Euclid 引理 ---- *)

Definition pec_dvd (d n : nat) : Prop := exists z : nat, n = d * z.

Lemma pec_dvd_of_eq : forall d n z : nat, n = d * z -> pec_dvd d n.
Proof. intros d n z H. exists z. exact H. Qed.

Lemma pec_dvd_mul_r : forall d a q : nat, pec_dvd d a -> pec_dvd d (q * a).
Proof.
  intros d a q [z Hz]. exists (q * z). rewrite Hz. ring.
Qed.

(* 整除加法消去：d ∣ x ∧ d ∣ (x+y) → d ∣ y（mul_sub_distr_r 截断恒等式，
   全确定性） *)
Lemma pec_dvd_add_r : forall d x y : nat,
  pec_dvd d x -> pec_dvd d (x + y) -> pec_dvd d y.
Proof.
  intros d x y [z1 Hz1] [z2 Hz2]. exists (z2 - z1).
  rewrite Hz1 in Hz2.
  rewrite Nat.mul_sub_distr_l. lia.
Qed.

(* 整除-除法判定桥：d ∣ n → n = d·(n/d)（Set 面见证装配的支点件） *)
Lemma pec_dvd_div_eq : forall d n : nat, pec_dvd d n -> n = d * (n / d).
Proof.
  intros d n [z Hz]. destruct d as [|d'].
  - rewrite Nat.mul_0_l in Hz. subst n. reflexivity.
  - assert (Hne : S d' <> 0) by lia.
    pose proof (Nat.div_mod n (S d') Hne) as Hdm.
    assert (Hm0 : n mod S d' = 0).
    { apply (proj2 (Nat.Div0.mod_divides n (S d'))).
      exists z. exact Hz. }
    rewrite Hm0 in Hdm. rewrite Nat.add_0_r in Hdm. exact Hdm.
Qed.

(* 原子积 contra 分档件（nia 不可形，经检验改确定性分档） *)
Lemma pec_small_prod_contra : forall p r w : nat,
  2 <= p -> 1 <= r -> r < p -> r = p * w -> False.
Proof.
  intros p r w Hp2 Hr1 Hrp Hw. destruct w as [|w0].
  - rewrite Nat.mul_0_r in Hw. lia.
  - destruct w0 as [|w1].
    + rewrite Nat.mul_1_r in Hw. lia.
    + rewrite Nat.mul_succ_r in Hw. rewrite Nat.mul_succ_r in Hw. lia.
Qed.

Lemma pec_two_p_contra : forall p m w : nat,
  2 <= p -> p <= m -> m < 2 * p -> m <> p -> m = p * w -> False.
Proof.
  intros p m w Hp2 Hpm Hm2p Hne Hw. destruct w as [|w0].
  - rewrite Nat.mul_0_r in Hw. lia.
  - destruct w0 as [|w1].
    + rewrite Nat.mul_1_r in Hw. lia.
    + rewrite Nat.mul_succ_r in Hw. rewrite Nat.mul_succ_r in Hw. lia.
Qed.

(* Euclid 引理（强形式，i < p 肢）：p 素 ∧ 1 ≤ i < p ∧ p ∣ i·a → p ∣ a。
   良基归纳于 i（core_01 同款 well_founded_induction_type，显式 IH）；
   p = q·i + r 分档：r = 0 时 i ∣ p 与素性矛盾；r ≥ 1 时 p·a =
   (p/i)·(i·a) + r·a 定代数和消去得 p ∣ r·a，降到 IH。 *)
Lemma pec_euclid_aux : forall p i a : nat, pr_prime p -> 1 <= i -> i < p ->
  pec_dvd p (i * a) -> pec_dvd p a.
Proof.
  intros p.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun i => forall a : nat, pr_prime p -> 1 <= i -> i < p ->
       pec_dvd p (i * a) -> pec_dvd p a)).
  intros i IH a Hp Hi1 Hip Hdvd.
  destruct (Nat.eq_dec i 1) as [E1 | NE1].
  - subst i. destruct Hdvd as [z Hz]. cbn [Nat.mul] in Hz.
    rewrite Nat.add_0_r in Hz. exists z. exact Hz.
  - assert (Hi2 : 2 <= i) by lia.
    assert (Hne : i <> 0) by lia.
    pose proof (Nat.div_mod p i Hne) as Hdm.
    destruct (Nat.eq_dec (p mod i) 0) as [Hr0 | Hr0].
    + exfalso. unfold pr_prime in Hp. destruct Hp as [_ Hno].
      apply (Hno i Hi2 Hip).
      assert (Hfin : p = p / i * i).
      { rewrite Hdm at 1. rewrite Hr0. rewrite Nat.add_0_r. apply Nat.mul_comm. }
      exists (p / i). exact Hfin.
    + assert (Hr1 : 1 <= p mod i) by lia.
      assert (Hri : p mod i < i) by (apply (Nat.mod_upper_bound p i Hne)).
      assert (Hip2 : p mod i < p) by lia.
      assert (Hra : pec_dvd p (p mod i * a)).
      { destruct Hdvd as [zv Hzv].
        assert (Hsum : p * a = (p / i) * (p * zv) + p mod i * a).
        { assert (Hs : i * (p / i) + p mod i = p) by (symmetry; exact Hdm).
          assert (Hdistr : (i * (p / i) + p mod i) * a
                           = (p / i) * (i * a) + p mod i * a)
            by (rewrite Nat.mul_add_distr_r; ring).
          rewrite Hs in Hdistr. rewrite Hzv in Hdistr. exact Hdistr. }
        assert (Hge : (p / i) * zv <= a).
        { assert (Hp0 : 0 < p) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; lia).
          apply (proj2 (Nat.mul_le_mono_pos_r ((p / i) * zv) a p Hp0)).
          lia. }
        exists (a - (p / i) * zv).
        rewrite Nat.mul_sub_distr_l. lia. }
      exact (IH (p mod i) Hri a Hp Hr1 Hip2 Hra).
Qed.

(* Euclid 引理（全量）：p 素 ∧ p ∣ i·a → p ∣ i ∨ p ∣ a。
   i ≥ p 时先以 i mod p 降维（i = (i/p)·p + r），r = 0 得左肢；
   i < p 时 r = i 直取 aux 肢。 *)
Lemma pec_euclid : forall p i a : nat, pr_prime p ->
  pec_dvd p (i * a) -> pec_dvd p i \/ pec_dvd p a.
Proof.
  intros p.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun i => forall a : nat, pr_prime p ->
       pec_dvd p (i * a) -> pec_dvd p i \/ pec_dvd p a)).
  intros i IH a Hp Hdvd.
  destruct (Nat.eq_dec i 0) as [E0 | NE0].
  - subst i. left. exists 0. lia.
  - assert (Hi1 : 1 <= i) by lia.
    assert (Hne : p <> 0) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; lia).
    pose proof (Nat.mod_upper_bound i p Hne) as Hrb.
    pose proof (Nat.div_mod i p Hne) as Hdm.
    destruct (Nat.eq_dec (i mod p) 0) as [Hr0 | Hr0].
    + left.
      assert (Hfin : i = p * (i / p)).
      { rewrite Hdm at 1. rewrite Hr0. rewrite Nat.add_0_r. reflexivity. }
      exists (i / p). exact Hfin.
    + assert (Hr1 : 1 <= i mod p) by lia.
      assert (Hra : pec_dvd p (i mod p * a)).
      { destruct Hdvd as [zv Hzv].
        assert (Hsum : p * zv = p * (i / p) * a + i mod p * a).
        { assert (Hdistr : (p * (i / p) + i mod p) * a
                           = p * (i / p) * a + i mod p * a)
            by (rewrite Nat.mul_add_distr_r; reflexivity).
          rewrite <- Hdm in Hdistr. rewrite Hzv in Hdistr. exact Hdistr. }
        assert (Hge : (i / p) * a <= zv).
        { assert (Hp0 : 0 < p) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; lia).
          apply (proj2 (Nat.mul_le_mono_pos_r ((i / p) * a) zv p Hp0)).
          lia. }
        exists (zv - (i / p) * a).
        rewrite Nat.mul_sub_distr_l. lia. }
      destruct (le_lt_dec p i) as [Hpi | Hip].
      * assert (Hri : i mod p < i) by lia.
        destruct (IH (i mod p) Hri a Hp Hra) as [Hl | Hr2].
        -- exfalso. destruct Hl as [w Hw].
           unfold pr_prime in Hp. destruct Hp as [Hp2 _].
           exact (pec_small_prod_contra p (i mod p) w Hp2 Hr1 Hrb Hw).
        -- right. exact Hr2.
      * assert (Hreq : i mod p = i) by (apply Nat.mod_small; lia).
        rewrite Hreq in Hra.
        right. exact (pec_euclid_aux p i a Hp Hi1 Hip Hra).
Qed.

(* 素除素：p ∣ q 且双双素 → p = q *)
Lemma pec_prime_dvd_prime : forall p q : nat,
  pr_prime p -> pr_prime q -> pec_dvd p q -> p = q.
Proof.
  intros p q Hp Hq Hd. destruct Hd as [w Hw].
  unfold pr_prime in Hp. destruct Hp as [Hp2 _].
  unfold pr_prime in Hq. destruct Hq as [Hq2 Hqn].
  destruct (lt_eq_lt_dec p q) as [[Hlt | Heq] | Hgt].
  - exfalso. apply (Hqn p Hp2 Hlt).
    exists w. rewrite Nat.mul_comm. exact Hw.
  - exact Heq.
  - exfalso. assert (Hq1 : 1 <= q) by lia.
    exact (pec_small_prod_contra p q w Hp2 Hq1 Hgt Hw).
Qed.

(* 组合引理：x 素、x ∤ P、x ∣ C、P ∣ C → x·P ∣ C（C = P·w 中 Euclid 拆 w） *)
Lemma pec_combine : forall x P C : nat,
  pr_prime x -> (pec_dvd x P -> False) ->
  pec_dvd x C -> pec_dvd P C -> pec_dvd (x * P) C.
Proof.
  intros x P C Hp HnP HdC HdP.
  destruct HdP as [w Hw].
  assert (HdC2 : pec_dvd x (P * w)) by (rewrite <- Hw; exact HdC).
  destruct (pec_euclid x P w Hp HdC2) as [Hd1 | Hdw].
  - exfalso. apply HnP. exact Hd1.
  - destruct Hdw as [u Hu]. exists u. rewrite Hw, Hu. ring.
Qed.

(* ---- §6 阶乘恒等式与素-阶乘交互 ---- *)

Lemma pec_fact_step : forall n : nat, fact (S n) = S n * fact n.
Proof. intro n. cbn [fact]. ring. Qed.

(* Pascal 形二项式的阶乘恒等式：k ≤ m → C(m,k)·k!·(m−k)! = m!。
   归纳步三档：k=0 直算；k=m 对角＋越界；k<m 双 IH ＋ sum 分配恒等式
   （transitivity + ring + 双 IH 重写，全确定性无引擎依赖）。 *)
Lemma pec_binom_fact : forall m k : nat, k <= m ->
  hl_binom m k * fact k * fact (m - k) = fact m.
Proof.
  induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [|k'].
    + cbn [hl_binom]. rewrite Nat.sub_0_r. cbn [fact]. ring.
    + assert (Hk' : k' <= m) by lia.
      destruct (Nat.eq_dec k' m) as [E | NE].
      * subst k'. rewrite pec_binom_diag.
        replace (S m - S m) with 0 by lia. cbn [fact]. ring.
      * assert (Hk2 : S k' <= m) by lia.
        pose proof (IH k' Hk') as H1.
        pose proof (IH (S k') Hk2) as H2.
        rewrite hl_binom_S.
        replace (S m - S k') with (m - k') by reflexivity.
        rewrite pec_fact_step. rewrite (pec_fact_step m).
        rewrite pec_fact_step in H2.
        assert (Hv : fact (m - k') = S (m - S k') * fact (m - S k')).
        { replace (m - k') with (S (m - S k')) by lia. apply pec_fact_step. }
        rewrite Hv in H1.
        rewrite Hv.
        assert (Hsum : S k' + S (m - S k') = S m) by lia.
        transitivity (S k' * (hl_binom m k' * fact k' * (S (m - S k') * fact (m - S k')))
                    + S (m - S k') * (hl_binom m (S k') * (S k' * fact k') * fact (m - S k'))).
        -- ring.
        -- rewrite H1, H2. rewrite <- Hsum. rewrite Nat.mul_add_distr_r. reflexivity.
Qed.

(* 素除阶乘：p 素 ∧ p ≤ m → p ∣ m!（归纳：p = S m 直取；p < S m 传 IH） *)
Lemma pec_prime_dvd_fact : forall p m : nat, pr_prime p -> p <= m -> pec_dvd p (fact m).
Proof.
  intros p m Hp. induction m as [|m IH]; intros Hm.
  - unfold pr_prime in Hp. destruct Hp as [Hp2 _]. lia.
  - destruct (Nat.eq_dec p (S m)) as [E | NE].
    + subst p. exists (fact m). apply pec_fact_step.
    + assert (Hpm : p <= m) by lia.
      destruct (IH Hpm) as [z Hz].
      exists (S m * z). rewrite pec_fact_step, Hz. ring.
Qed.

(* 素不除阶乘：p 素 ∧ n < p → p ∤ n!（Euclid aux 于 S n·fact n 逐层下压） *)
Lemma pec_prime_not_dvd_fact : forall p n : nat, pr_prime p -> n < p ->
  pec_dvd p (fact n) -> False.
Proof.
  intros p n Hp. induction n as [|n IH]; intros Hn Hd.
  - destruct Hd as [z Hz]. cbn [fact] in Hz.
    unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. lia.
    + rewrite Nat.mul_succ_r in Hz. lia.
  - rewrite pec_fact_step in Hd.
    assert (Hdf : pec_dvd p (fact n)).
    { apply (pec_euclid_aux p (S n) (fact n) Hp); [lia | exact Hn | exact Hd]. }
    exfalso. apply IH; [lia | exact Hdf].
Qed.

(* ---- §7 层 1b：中项 C(2n,n) 的素数幂恰一次（Erdős 关键观察） ---- *)

Definition pec_mid (n : nat) : nat := hl_binom (2 * n) n.

Lemma pec_mid_fact_eq : forall n : nat, pec_mid n * fact n * fact n = fact (2 * n).
Proof.
  intro n. unfold pec_mid.
  pose proof (pec_binom_fact (2 * n) n ltac:(lia)) as H.
  replace (2 * n - n) with n in H by lia. exact H.
Qed.

(* 素除中项（Prop 肢）：n < p ≤ 2n 素 → p ∣ C(2n,n)。
   fact(2n) = p·z0 与 C·n!·n! = fact(2n) 拼接，Euclid 两刀压掉 n!²。 *)
Lemma pec_mid_dvd_prop : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  pec_dvd p (pec_mid n).
Proof.
  intros n p Hnp Hp2n Hp.
  assert (Hd20 : pec_dvd p (fact (2 * n)))
    by (apply pec_prime_dvd_fact; [exact Hp | lia]).
  assert (Hdfn : pec_dvd p (fact n) -> False)
    by (apply pec_prime_not_dvd_fact; [exact Hp | exact Hnp]).
  pose proof (pec_mid_fact_eq n) as Hmid.
  assert (HdC : pec_dvd p (pec_mid n * (fact n * fact n))).
  { destruct Hd20 as [z0 Hz0]. exists z0.
    rewrite Nat.mul_assoc. rewrite Hmid. exact Hz0. }
  destruct (pec_euclid p (pec_mid n) (fact n * fact n) Hp HdC) as [H1 | H12].
  - exact H1.
  - destruct (pec_euclid p (fact n) (fact n) Hp H12) as [H2 | H2].
    + exfalso. apply (Hdfn H2).
    + exfalso. apply (Hdfn H2).
Qed.

(* 素除中项（层 1b(a) 主语句，Set 面 sigT：见证 z = C/p 可计算） *)
Theorem pec_mid_prime_dvd : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  { z : nat & pec_mid n = p * z }.
Proof.
  intros n p Hnp Hp2n Hp. exists (pec_mid n / p).
  apply (pec_dvd_div_eq p (pec_mid n)).
  apply (pec_mid_dvd_prop n p Hnp Hp2n Hp).
Defined.

(* 单 p 分解：p ≤ m < 2p → m! = p·z 且 p ∤ z（sigT，归纳于 m：
   m = p 取 z = fact(p−1)；p < m 传 IH 后 Euclid 分档压出） *)
Lemma pec_fact_single_p : forall p m : nat, pr_prime p -> p <= m -> m < 2 * p ->
  { z : nat & fact m = p * z /\ (forall w : nat, fact m = p * (p * w) -> False) }.
Proof.
  intros p m Hp. induction m as [|m IH]; intros Hpm Hm2p.
  - exfalso. unfold pr_prime in Hp. destruct Hp as [Hp2 _]. lia.
  - destruct (Nat.eq_dec (S m) p) as [E | NE].
    + subst p. exists (fact m). split.
      * apply pec_fact_step.
      * intros w Hw.
        assert (Hne0 : S m <> 0) by lia.
        assert (Hc : fact m = S m * w).
        { apply (proj1 (Nat.mul_cancel_l (fact m) (S m * w) (S m) Hne0)).
          rewrite pec_fact_step in Hw. exact Hw. }
        exfalso.
        apply (pec_prime_not_dvd_fact (S m) m Hp (Nat.lt_succ_diag_r m)).
        exists w. exact Hc.
    + assert (Hpm' : p <= m) by lia.
      assert (Hm2' : m < 2 * p) by lia.
      destruct (IH Hpm' Hm2') as [z1 [Hz1 Hz1n]].
      exists (S m * z1). split.
      * rewrite pec_fact_step, Hz1. ring.
      * intros w Hw.
        assert (Hne0 : p <> 0) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; lia).
        rewrite pec_fact_step in Hw. rewrite Hz1 in Hw.
        assert (Hc : S m * z1 = p * w).
        { apply (proj1 (Nat.mul_cancel_l (S m * z1) (p * w) p Hne0)).
          rewrite Nat.mul_assoc. rewrite (Nat.mul_comm p (S m)).
          rewrite <- Nat.mul_assoc. exact Hw. }
        assert (Hdvd : pec_dvd p (S m * z1)) by (exists w; exact Hc).
        destruct (pec_euclid p (S m) z1 Hp Hdvd) as [Hd1 | Hd2].
        -- exfalso. destruct Hd1 as [w2 Hw2].
           unfold pr_prime in Hp. destruct Hp as [Hp2 _].
           assert (HpmS : p <= S m) by lia.
           exact (pec_two_p_contra p (S m) w2 Hp2 HpmS Hm2p NE Hw2).
        -- exfalso. destruct Hd2 as [w2 Hw2]. apply (Hz1n w2).
           rewrite Hz1, Hw2. reflexivity.
Defined.

(* 素平方不除中项（层 1b(b)）：p² ∣ C(2n,n) → False。
   fact(2n) 单 p（2n < 2p 由 n < p），若 C = p·(p·w) 则
   fact(2n) = C·n!·n! 的 p-重数 ≥ 2 与单 p 矛盾。 *)
Theorem pec_mid_not_sq_dvd : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  pec_dvd (p * p) (pec_mid n) -> False.
Proof.
  intros n p Hnp Hp2n Hp [w Hw].
  assert (Ha : p <= 2 * n) by lia.
  assert (Hb : 2 * n < 2 * p) by lia.
  destruct (pec_fact_single_p p (2 * n) Hp Ha Hb) as [z [Hz Hzn]].
  apply (Hzn (w * fact n * fact n)).
  pose proof (pec_mid_fact_eq n) as Hmid.
  rewrite <- Hmid, Hw. ring.
Qed.

(* 层 1b 主语句：素数幂恰一次（(a)+(b) 合装，Set 面 sigT） *)
Theorem pec_mid_exactly_once : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  { z : nat & pec_mid n = p * z /\ (forall w : nat, pec_mid n = p * (p * w) -> False) }.
Proof.
  intros n p Hnp Hp2n Hp. exists (pec_mid n / p). split.
  - apply (pec_dvd_div_eq p (pec_mid n)). apply (pec_mid_dvd_prop n p Hnp Hp2n Hp).
  - intros w Hw. apply (pec_mid_not_sq_dvd n p Hnp Hp2n Hp). exists w.
    replace (p * p * w) with (p * (p * w)) by ring. exact Hw.
Defined.

(* ---- §8 层 2：窗口素数升积整除中项与骨架不等式 ---- *)

(* 窗口素数表：pec_win a k = (a, a+k] 内全部素数（降序构造，布尔判定器） *)
Fixpoint pec_win (a k : nat) : list nat :=
  match k with
  | O => nil
  | S k' => let x := a + S k' in
            if pr_prime_bool x then x :: pec_win a k' else pec_win a k'
  end.

Definition pec_winprod (n : nat) : nat := fold_right Nat.mul 1 (pec_win n n).

Lemma pec_win_in : forall a k p : nat,
  In p (pec_win a k) -> pr_prime p /\ a < p /\ p <= a + k.
Proof.
  intros a k. induction k as [|k IH]; intros p Hin.
  - cbn [pec_win] in Hin. destruct Hin.
  - cbn [pec_win] in Hin. destruct (pr_prime_bool (a + S k)) eqn:Eb.
    + destruct Hin as [Heq | Hin].
      * subst p. split; [apply pr_prime_bool_true; exact Eb | split; lia].
      * destruct (IH p Hin) as [H1 [H2 H3]]. split; [exact H1 | split; lia].
    + destruct (IH p Hin) as [H1 [H2 H3]]. split; [exact H1 | split; lia].
Qed.

(* 素除升积 → 积中一员被除（Euclid 沿折叠下压） *)
Lemma pec_prime_dvd_prod_in : forall (p : nat) (l : list nat),
  pr_prime p -> pec_dvd p (fold_right Nat.mul 1 l) ->
  exists q : nat, In q l /\ pec_dvd p q.
Proof.
  intros p l Hp. induction l as [|q l IH]; intros Hd.
  - cbn [fold_right] in Hd. destruct Hd as [z Hz].
    unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. lia.
    + rewrite Nat.mul_succ_r in Hz. lia.
  - cbn [fold_right] in Hd.
    destruct (pec_euclid p q (fold_right Nat.mul 1 l) Hp Hd) as [Hq | Hl].
    + exists q. split; [left; reflexivity | exact Hq].
    + destruct (IH Hl) as [q' [Hin Hq']]. exists q'. split; [right; exact Hin | exact Hq'].
Qed.

(* 窗口升积整除中项（Prop 肢，归纳于窗宽 k ≤ n：表头 x = n+S k 为窗内
   最大素，x ∣ C（恰一次肢 a）＋ x ∤ 升积（成员被除则 x = q > n+k 矛盾）
   ＋ pec_combine 升积合并） *)
Lemma pec_winprod_dvd_eq : forall n k : nat, k <= n ->
  exists z : nat, pec_mid n = fold_right Nat.mul 1 (pec_win n k) * z.
Proof.
  intros n k. induction k as [|k IH]; intros Hk.
  - exists (pec_mid n). cbn [pec_win fold_right]. ring.
  - cbn [pec_win]. destruct (pr_prime_bool (n + S k)) eqn:Eb.
    + assert (Hpx : pr_prime (n + S k)) by (apply pr_prime_bool_true; exact Eb).
      assert (Hxn : n < n + S k) by lia.
      assert (Hx2 : n + S k <= 2 * n) by lia.
      destruct (pec_mid_prime_dvd n (n + S k) Hxn Hx2 Hpx) as [vx Hvx].
      assert (HnP : pec_dvd (n + S k) (fold_right Nat.mul 1 (pec_win n k)) -> False).
      { intros Hd.
        destruct (pec_prime_dvd_prod_in (n + S k) (pec_win n k) Hpx Hd) as [q [Hin Hq]].
        destruct (pec_win_in n k q Hin) as [Hq1 [Hq2 Hq3]].
        assert (Heq : n + S k = q) by (apply (pec_prime_dvd_prime (n + S k) q Hpx Hq1 Hq)).
        lia. }
      assert (Hk' : k <= n) by lia.
      destruct (IH Hk') as [z' Hz'].
      assert (HdP : pec_dvd (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n))
        by (apply (pec_dvd_of_eq (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n) z' Hz')).
      destruct (pec_combine (n + S k) (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n)
                            Hpx HnP (pec_dvd_of_eq (n + S k) (pec_mid n) vx Hvx) HdP)
        as [u Hu].
      exists u. cbn [fold_right]. exact Hu.
    + assert (Hk' : k <= n) by lia.
      destruct (IH Hk') as [z' Hz']. exists z'. exact Hz'.
Qed.

(* 窗口升积整除中项（层 2 主语句 a，Set 面 sigT：z = C/∏ 可计算） *)
Theorem pec_win_dvd_mid : forall n : nat,
  { z : nat & pec_mid n = pec_winprod n * z }.
Proof.
  intro n.
  assert (Hd : pec_dvd (pec_winprod n) (pec_mid n)).
  { unfold pec_winprod.
    destruct (pec_winprod_dvd_eq n n (Nat.le_refl n)) as [z0 Hz0].
    apply (pec_dvd_of_eq (fold_right Nat.mul 1 (pec_win n n)) (pec_mid n) z0 Hz0). }
  exists (pec_mid n / pec_winprod n).
  apply (pec_dvd_div_eq (pec_winprod n) (pec_mid n) Hd).
Defined.

(* 层 2 骨架不等式（构造性合装）：∏_{n<p≤2n} p ∣ C(2n,n) ∧
   ∏ ≤ C(2n,n) ≤ 4^n（上界半边直引 HansonLcm.hl_central_binom_le） *)
Theorem pec_erdos_skeleton : forall n : nat,
  { z : nat & pec_mid n = pec_winprod n * z }
  * (hl_le_t (pec_winprod n) (pec_mid n) * hl_le_t (pec_mid n) (4 ^ n)%nat).
Proof.
  intro n. split.
  - apply pec_win_dvd_mid.
  - split.
    + apply hl_le_to_le_t.
      destruct (pec_win_dvd_mid n) as [z Hz].
      assert (Hpos : 1 <= pec_mid n) by (unfold pec_mid; apply pec_binom_pos; lia).
      destruct z as [|z'].
      * rewrite Nat.mul_0_r in Hz. lia.
      * rewrite Nat.mul_succ_r in Hz. lia.
    + unfold pec_mid. apply hl_central_binom_le.
Defined.

(* 骨架严格上界肢：n ≥ 1 → C(2n,n)+2 ≤ 4^n（Set 面） *)
Theorem pec_skeleton_lt : forall n : nat, 1 <= n -> hl_le_t (pec_mid n + 2) (4 ^ n)%nat.
Proof.
  intros n Hn. unfold pec_mid. apply hl_le_to_le_t. apply pec_central_lt. exact Hn.
Qed.

(* ---- §9 数值定装烟测（小实例 ≤ 10，unary 打点纪律，vm_compute） ---- *)

Lemma pec_smoke_lower5 : (Nat.leb (4 ^ 5) (11 * hl_binom 10 5))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_lower8 : (Nat.leb (4 ^ 4) (9 * hl_binom 8 4))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_mid4 : hl_binom 8 4 = 70.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_win4 : pec_win 4 4 = (7 :: 5 :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_prod4 : pec_winprod 4 = 35.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_dvd4 : (hl_binom 8 4 mod pec_winprod 4)%nat = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_notsq4 : (hl_binom 8 4 mod (5 * 5))%nat = 20.
Proof. vm_compute. reflexivity. Qed.

(* ---- §10 公理审计（Print Assumptions 取证面）与提取检验 ---- *)

Print Assumptions pec_row_sum.
Print Assumptions pec_lower.
Print Assumptions pec_central_lt.
Print Assumptions pec_euclid_aux.
Print Assumptions pec_euclid.
Print Assumptions pec_binom_fact.
Print Assumptions pec_mid_prime_dvd.
Print Assumptions pec_mid_not_sq_dvd.
Print Assumptions pec_mid_exactly_once.
Print Assumptions pec_winprod_dvd_eq.
Print Assumptions pec_win_dvd_mid.
Print Assumptions pec_erdos_skeleton.
Print Assumptions pec_skeleton_lt.

From Stdlib Require Import Extraction.
Separate Extraction pec_sum pec_win pec_winprod pec_mid.
