(* ============================================================ *)
(* Hanson3Pow.v — 席位 D023（批次 E-STAGING-D023，20260919 施工）    *)
(*                                                               *)
(* 使命：T123 件①攻坚切片——lcm(1..n) < 3^n 构造性证明攻坚。         *)
(*   新建件（照任务书 B 案），Require HansonLcm，h3_ 前缀零撞名。     *)
(*                                                               *)
(* 路线判定（开工三查 + 数值锚定 n=1..15 打表，详见 T123 报告）：      *)
(*   路线 α（素数幂和）：stdlib 9.1 nat 层零素数库（T106 开工勘定     *)
(*     定格），素数面 3–5 席超窗——维持判否。                        *)
(*   路线 β（二项式整除桥）：数值打表判否——L(n) ∤ C(n+⌊n/2⌋,n) 对     *)
(*     n=2..15 全灭（n=5: L(5)=60 ∤ C(7,5)=21）；L(n) ∣ n!·C(2n,n)   *)
(*     虽真但被 L(n) ∣ n! 平凡蕴含（桥无增益）；Farhi 全等式          *)
(*     L(n+1) = (n+1)·lcm_k C(n,k) 数值成立但其界出仍需 p-adic。      *)
(*     → 判否登记，T106 判否补充新例。                              *)
(*   路线 γ（半程二项式桥，本席交付）：免素数新定理                   *)
(*     ★ h3_lcm_double_divide : L(2n) ∣ C(2n,n)·n! （n=1..15 锚定全绿）*)
(*     + 半程上界 h3_lcm_le_halfbinom : L(n) ≤ C(2⌈n/2⌉,⌈n/2⌉)·⌈n/2⌉! *)
(*     （严格强化 HansonLcm 件①占位 L(n) ≤ n!，两件兼容零改既有定理）。*)
(*     核心新算术 = 吸收恒等式 h3_binom_absorb :                     *)
(*     C(S n,S k)·S k = S n·C(n,k)（stdlib nat 层无库存二项式，       *)
(*     双参数归纳自建，照 hl_binom_le_pow2 先例）。                   *)
(*   更锐桥 L(2n) ∣ C(2n,n)·L(n)（数值 n=1..15 成立）其证明本质为     *)
(*     p-adic 赋值/Kummer 进位（需素数面）——卡点登记 T123 报告，      *)
(*     本件不虚报。                                                 *)
(*   3^n 档判定：α/β 均不可达，按任务书纪律诚实交付 γ 半程桥+弱化界，   *)
(*     显式标注【非 3^n 档】——半程界仍含 (n/2)! 档因子，超指数档；      *)
(*     升级方向=素数面席（Nat.prime 自建+素数枚举 Fixpoint+Hanson     *)
(*     ψ 分解），T106 路线判定维持。禁止虚报 3^n。                    *)
(* 红线四要素宣言（逐件）：                                         *)
(*   - 纯构造性：全件 Qed，零公理声明词、零认授、零经典逻辑；           *)
(*   - Set 层：旗舰件 h3_lcm_le_halfbinom_t : Set（hl_le_t 承载，      *)
(*     与 HansonLcm 件①占位同构）；支撑引理 nat 层 Prop 面仅作        *)
(*     推理脚手架（Ln2Escape/HansonLcm 先例）；                       *)
(*   - 非平凡：吸收恒等式双参数归纳 + 半程桥折叠整除机皆真构造；        *)
(*   - 可提取：h3_prod_from/h3_binom 皆 Fixpoint 可执行；G3 探针      *)
(*     Extraction 验证 Obj.magic 计数 = 0。                          *)
(*   - 打点纪律：零数值实例打点（CZR14 卡：kernel conv divmod 链       *)
(*     分钟级墙钟坑），可执行性见证由 G3 提取面承担。                  *)
(* 依赖：Stdlib Arith/Factorial/Lia + HansonLcm（side 现编，零项目件，  *)
(*   G2 免基座墙）。                                                *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.

(* ============================================================ *)
(* §A 二项式算术：吸收恒等式（本席核心新件）                            *)
(* ============================================================ *)

(* k=0 边缘：hl_binom n 0 = 1 全 n 成立（首参递减 fix 对非 constructor
   首参不约化，故独立成件——h3_prod_binom_fact base 用） *)
Lemma h3_binom_k0 : forall n : nat, hl_binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

(* C(S n, 1) = S n（边缘件，吸收恒等式 k=0 腿用） *)
Lemma h3_binom_1 : forall n : nat, hl_binom (S n) 1 = S n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite (hl_binom_S (S n) 0).
    assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
    rewrite E0. rewrite IH. lia.
Qed.

(* ★ 吸收恒等式：C(S n, S k)·S k = S n·C(n,k)。
   双参数归纳：外层 n，步内消费外层 IH 于 k 与 S k 两点
   （照 hl_binom_le_pow2 双参数先例；stdlib nat 层无库存）。 *)
Lemma h3_binom_absorb : forall n k : nat,
  hl_binom (S n) (S k) * (S k) = (S n) * hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k'].
    + rewrite (hl_binom_S (S n) 0).
      assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
      rewrite E0. rewrite h3_binom_1. lia.
    + rewrite (hl_binom_S (S n) (S k')).
      pose proof (IH k') as H1. pose proof (IH (S k')) as H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S (S k'))) (S k')) in H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S k')
                 + hl_binom (S n) (S (S k'))) (S k')).
      rewrite (Nat.mul_add_distr_r (hl_binom (S n) (S k'))
                 (hl_binom (S n) (S (S k'))) (S k')).
      rewrite H1.
      assert (HA : hl_binom (S n) (S k') = hl_binom n k' + hl_binom n (S k'))
        by reflexivity.
      assert (HAm : S n * hl_binom (S n) (S k') =
                    S n * hl_binom n k' + S n * hl_binom n (S k'))
        by (rewrite HA; ring).
      assert (HR : S (S n) * hl_binom (S n) (S k') =
                   S n * hl_binom (S n) (S k') + hl_binom (S n) (S k')) by ring.
      rewrite HR. lia.
Qed.

(* 二项式非零下界：k ≤ n ⟹ 1 ≤ C(n,k)（半程界整除腿的正性用） *)
Lemma h3_binom_ge1 : forall n k : nat, k <= n -> 1 <= hl_binom n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. lia.
    + rewrite (hl_binom_S n k').
      apply (Nat.le_trans 1 (hl_binom n k')).
      * apply IH. lia.
      * apply Nat.le_add_r.
Qed.

(* ============================================================ *)
(* §B 区间乘积机：h3_prod_from a k = Π_{i=0}^{k-1} (a+i)               *)
(* ============================================================ *)

Fixpoint h3_prod_from (a k : nat) : nat :=
  match k with
  | O => 1
  | S k' => (a + k') * h3_prod_from a k'
  end.

(* 区间元整除：a ≤ m < a+k ⟹ m ∣ Π(a..a+k-1)（m 本身是因子） *)
Lemma h3_prod_divide : forall k a m : nat,
  a <= m -> m < a + k -> Nat.divide m (h3_prod_from a k).
Proof.
  induction k as [| k IH]; intros a m H1 H2.
  - lia.
  - cbn [h3_prod_from].
    destruct (Nat.eq_dec m (a + k)) as [E|NE].
    + rewrite E. exists (h3_prod_from a k). ring.
    + destruct (IH a m H1 ltac:(lia)) as [p Hp].
      exists (p * (a + k))%nat. rewrite Hp. ring.
Qed.

(* ★ 主恒等式（一般形）：Π_{i=1}^{k} (m+i) = C(m+k, k)·k!
   归纳 k，步闭环全靠吸收恒等式（除法自由的乘法形式）。
   数值锚定 n=1..15：Π(n+1..2n) = C(2n,n)·n! 全绿。 *)
Lemma h3_prod_binom_fact : forall m k : nat,
  h3_prod_from (S m) k = hl_binom (m + k) k * fact k.
Proof.
  intros m k. induction k as [| k IH].
  - rewrite h3_binom_k0. reflexivity.
  - cbn [h3_prod_from fact].
    rewrite Nat.add_succ_r, Nat.mul_assoc.
    pose proof (h3_binom_absorb (m + k) k) as HA.
    rewrite HA.
    replace (S (m + k)) with (S m + k) by lia.
    rewrite IH. ring.
Qed.

(* ============================================================ *)
(* §C lcm 折叠机强化：全数整除 ⟹ 折叠值整除（stdlib lcm_least 承载）     *)
(* ============================================================ *)

(* m ≤ n ⟹ m ∣ n!（乘积元整除，归纳） *)
Lemma h3_fact_divide : forall n m : nat,
  1 <= m -> m <= n -> Nat.divide m (fact n).
Proof.
  induction n as [| n IH]; intros m H1 H2.
  - lia.
  - destruct (Nat.eq_dec m (S n)) as [E|NE].
    + rewrite E. exists (fact n). cbn [fact]. ring.
    + destruct (IH m H1 ltac:(lia)) as [p Hp].
      exists (p * S n)%nat. cbn [fact]. rewrite Hp. ring.
Qed.

(* 折叠公倍数闭包：1..N 全数整除 D ⟹ L(N) ∣ D（stdlib Nat.lcm_least） *)
Lemma h3_lcm_fold_divide : forall N D : nat,
  (forall m : nat, 1 <= m -> m <= N -> Nat.divide m D) ->
  Nat.divide (hl_lcm_upto N) D.
Proof.
  intros N D H. induction N as [| N IHN].
  - cbn [hl_lcm_upto]. exists D. ring.
  - cbn [hl_lcm_upto]. apply Nat.lcm_least.
    + apply IHN. intros m H1 H2. apply H; lia.
    + apply H; lia.
Qed.

(* L(n) ∣ n!（折叠闭包实例；供正性腿） *)
Lemma h3_lcm_upto_fact_divide : forall n, Nat.divide (hl_lcm_upto n) (fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  apply h3_fact_divide; lia.
Qed.

(* 阶乘正性（独立件，供正性腿） *)
Lemma h3_fact_pos : forall n, 0 < fact n.
Proof.
  induction n as [| n IH].
  - cbn [fact]. lia.
  - cbn [fact]. apply Nat.mul_pos_pos; lia.
Qed.

(* 正性：1 ≤ L(n)（整除 + 阶乘正） *)
Lemma h3_lcm_pos : forall n, 1 <= hl_lcm_upto n.
Proof.
  intro n. destruct (h3_lcm_upto_fact_divide n) as [p Hp].
  pose proof (h3_fact_pos n) as Hf.
  destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct (hl_lcm_upto n) as [| L'].
    + rewrite Nat.mul_0_r in Hp. lia.
    + lia.
Qed.

(* 整除⟹≤（双正性腿；b=0 反例封死） *)
Lemma h3_divide_le : forall a b : nat,
  Nat.divide a b -> 1 <= a -> 0 < b -> a <= b.
Proof.
  intros a b Hd Ha Hb. destruct Hd as [p Hp]. destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct a as [| a'].
    + lia.
    + rewrite Hp. replace (S p' * S a') with (S a' + p' * S a') by ring. lia.
Qed.

(* 折叠单调性：n ≤ m ⟹ L(n) ∣ L(m)（逐层 divide_lcm_l 链） *)
Lemma h3_lcm_mono_divide : forall n m : nat,
  n <= m -> Nat.divide (hl_lcm_upto n) (hl_lcm_upto m).
Proof.
  intros n m. induction m as [| m IHm]; intro H.
  - assert (n = 0) by lia. subst n. apply Nat.divide_refl.
  - destruct (Nat.eq_dec n (S m)) as [E|NE].
    + rewrite E. apply Nat.divide_refl.
    + cbn [hl_lcm_upto].
      apply (hl_div_trans (hl_lcm_upto n) (hl_lcm_upto m)
               (Nat.lcm (hl_lcm_upto m) (S m))).
      * apply IHm. lia.
      * apply Nat.divide_lcm_l.
Qed.

(* ============================================================ *)
(* §D 【件①攻坚】半程二项式桥（免素数）——显式标注【非 3^n 档】          *)
(* ============================================================ *)

(* ★ 主定理：L(2n) ∣ C(2n,n)·n!。
   论证：m ≤ n 则 m ∣ n!；n < m ≤ 2n 则 m ∣ Π(n+1..2n) = C(2n,n)·n!
   （区间元整除 + 主恒等式）；折叠公倍数闭包收口。
   数值锚定 n=1..15 全绿（T123 报告打表）。 *)
Theorem h3_lcm_double_divide : forall n : nat,
  Nat.divide (hl_lcm_upto (2 * n)) (hl_binom (2 * n) n * fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  destruct (Nat.le_gt_cases m n) as [Hle|Hgt].
  - apply (hl_div_trans m (fact n) (hl_binom (2 * n) n * fact n)).
    + apply h3_fact_divide; lia.
    + exists (hl_binom (2 * n) n). ring.
  - apply (hl_div_trans m (h3_prod_from (S n) n)
             (hl_binom (2 * n) n * fact n)).
    + apply h3_prod_divide; lia.
    + rewrite (h3_prod_binom_fact n n).
      replace (2 * n) with (n + n) by lia.
      exists 1. ring.
Qed.

(* 半程上界（件①可达最强弱化形，严格强化 HansonLcm.hl_lcm_le_fact 的
   n! 占位）：L(n) ≤ C(2⌈n/2⌉,⌈n/2⌉)·⌈n/2⌉!。
   【非 3^n 档】显式标注：界仍含 ⌈n/2⌉! 档因子，超指数档；3^n 需素数面
   （T106/T123 卡点定位），禁虚报。 *)
Theorem h3_lcm_le_halfbinom : forall n : nat,
  hl_lcm_upto n <= hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)).
Proof.
  intro n.
  assert (H2n0 : 2 <> 0) by lia.
  pose proof (Nat.div_mod n 2 H2n0) as Hdm.
  pose proof (Nat.mod_upper_bound n 2 H2n0) as Hmod.
  assert (Hn : n <= 2 * S (n / 2)) by lia.
  apply (Nat.le_trans (hl_lcm_upto n) (hl_lcm_upto (2 * S (n / 2)))
           (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))).
  - pose proof (h3_lcm_pos (2 * S (n / 2))) as Hp1.
    apply h3_divide_le.
    + apply h3_lcm_mono_divide. exact Hn.
    + apply h3_lcm_pos.
    + lia.
  - pose proof (h3_lcm_pos (2 * S (n / 2))) as Hp2.
    assert (Hb : 1 <= hl_binom (2 * S (n / 2)) (S (n / 2)))
      by (apply h3_binom_ge1; lia).
    assert (Hf2 : 0 < fact (S (n / 2))) by apply h3_fact_pos.
    assert (Hd2 : 0 < hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))
      by (apply Nat.mul_pos_pos; lia).
    apply h3_divide_le.
    + apply h3_lcm_double_divide.
    + lia.
    + exact Hd2.
Qed.

(* 旗舰 Set 面全称重述（hl_le_t 承载，与 HansonLcm 件①占位同构——
   本件为其真强化；【非 3^n 档】注记同上，禁虚报） *)
Theorem h3_lcm_le_halfbinom_t : forall n : nat,
  hl_le_t (hl_lcm_upto n)
    (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))%nat.
Proof. intro n. apply hl_le_to_le_t. apply h3_lcm_le_halfbinom. Qed.

(* 自审面：主件零假设声明（G1 PA≥1 口径，与 G4 rocq check 同源） *)
Print Assumptions h3_lcm_double_divide.
Print Assumptions h3_lcm_le_halfbinom_t.
