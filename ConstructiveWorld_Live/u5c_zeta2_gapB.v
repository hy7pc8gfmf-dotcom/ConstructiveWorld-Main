(* ===================================================================== *)
(* 模块：u5c_zeta2_gapB                                                  *)
(* 使命：ζ(2) 缺口件 B——Hanson 合拢链供给面。目标语句 hl_lcm_upto n ≤ 3^n（Hanson 1972） *)
(* 是整性分离面 zb2_dc_sep_small 前提 I（d ≤ 3^(m+1)）的供给位。本件交付： ① C-链方程与正性：fact n = z2v_den n n · z2v_C n（1 ≤ n）、1 ≤ z2v_C n（全 n）；  *)
(* ② 分母积步进机：z2v_den k n = z2v_den k (n−1) · z2gb_G k n，z2gb_G k n := ∏_{j<k}（a_{j+1} ∣ n 时取 n/a_{j+1}，否则取 1），每档因子即 fact(⌊n/a⌋)/fact(⌊(n−1)/a⌋)  *)
(* 的精确比值；③ 引擎恒等式一（C 的精确步进递归）：z2v_C (S m) · z2gb_G (S m) (S m) = S m · z2v_C m（m ≥ 1）；④ 引擎恒等式二（Sylvester 增值积的满档再注入）：  *)
(* z2gb_G k (z2d_sylv_P k) · z2d_sylv_P k = (z2d_sylv_P k)^k（P_k 处每个 Sylvester 数 都整除，增值积满档注入）；⑤ M3′ 合拢链（全强度）：整除（valbridge z2v_lcm_dvd_C）＋  *)
(*     上界前提 ⟹ hl_le_t (hl_lcm_upto n) (3^n)；⑥ 验收语句（Q 层 Set 面）：                   *)
(*     z2d_lcm_le_3pow : ∀n, 1 ≤ n → z2v_C n ≤ 3^n → QleT' (Z.of_nat (hl_lcm_upto n) # 1)%Q    *)
(*     (Z.of_nat (3^n) # 1)%Q。 *)
(* 收窄申报（诚实律，禁虚报）：核心证书 M2′（即 Hanson 原文 p.35–36 的 Sylvester 熵不等式      *)
(* Σ(ln a_i)/a_i < ln 3 的 nat 化）本件未铸，故 ⑤⑥ 以该证书为显式前提位而非公理， Print Assumptions 仍全零。收窄实况：(a) 逐因子粗糙 nat 界全部超预算（60 > 12），每单位  *)
(*   Σs_i 的加性熵损耗即穿底，Σ(ln a_i)/a_i ≈ 1.083 与 ln 3 ≈ 1.0986 之间余量仅约 0.0156n；      *)
(* (b) 库内 Chebyshev 档（pec_prim N ≤ 4^(2N)，即 θ ≤ 4ln2·N）常数不够 3^n 档 （4ln2 ≈ 2.77 > ln 3），免素数路线碰壁实录在案；(c) 步进归纳需乘法再注入的全局账本  *)
(* （n 含 Sylvester 除子逐层续满、素数段按 3/n 衰减），为篇幅级论证，候后续件以熵不等式的 nat 化（或等价形）收拢终口。  *)
(*   本件状态＝M3′ 全链闭合＋引擎件全铸＋单前提位候合拢（不符即收窄如实申报）；缺口件 A          *)
(*   （sep_small 前提 II）系 ζ(2) 线另一件，本件零触及。 *)
(* 数学内容：Hanson, Canad. Math. Bull. 15 (1972), 33–37 引理组；C(n) := n!/∏_i⌊n/a_i⌋!          *)
(* （a_i 为 Sylvester 序列 2,3,7,43,…），承载沿用 dub3（z2d_sylv_a/z2d_sylv_P）与 valbridge （z2v_den/z2v_C）。  *)
(* 依赖：Stdlib（QArith.QArith/ZArith.ZArith/Arith.Arith/Arith.Factorial/Lia）；HansonLcm、       *)
(*   Hanson3Pow、S02_CauchyComplete（QleT' 供给位）；abl_z2_dub3、abl_z2_valbridge。 *)
(* 构造性：全件 Qed，零公理声明、零承认式语句、零经典逻辑；语句假设位非公理位；主语句面          *)
(*   hl_le_t/QleT' 皆 Set 层；支撑引理为 nat 层 Prop 面、仅服务推理；z2gb_G 为 Fixpoint 可计算；   *)
(*   文尾 Print Assumptions 全语句清单复核。 *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd 池目录   *)
(*   && nice -19 rocq c -native-compiler no -q -Q . "" u5c_zeta2_gapB.v（依赖件 vo 经 -Q 映射挂源根；  *)
(* abl_z2_dub3/abl_z2_valbridge 居 abl_tmine04_pool/zeta2 池）。 技术注记：QArith 引入即全局开启 Q_scope 劫持 nat 面记法，本件以 Close Scope Q_scope、Q 处  *)
(*   局部 %Q 标注——后续混域件照守。 *)
(* 对标：Hanson 1972（同上）引理三上界档。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith.
From Stdlib Require Import Arith.Factorial Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import S02_CauchyComplete.
Require Import abl_z2_dub3.
Require Import abl_z2_valbridge.

(* QArith 引入即全局开启 Q_scope 并劫持 nat 面记法——就地关闭，
   Q 层语句一律局部 %Q 标注（z2d_lcm_le_3pow 面已标注） *)
Close Scope Q_scope.

(* ===================================================================== *)
(* §0 Q 层嵌入桥与基础面                                                  *)
(* ===================================================================== *)

(* 非负数值面：0 ≤ (n)#1（任意 nat） *)
Lemma zb2gb_natQ_ge0 : forall n : nat, (0 <= Z.of_nat n # 1)%Q.
Proof.
  intro n. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* Q 层同分母序反射：a ≤ b（nat）⟹ (a#1) ≤ (b#1)（QleT' Set 承载） *)
Lemma zb2gb_Qnat_le : forall a b : nat,
  (a <= b)%nat -> QleT' ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b Hab. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 幂正性：1 ≤ 3^n（任意 nat 指数） *)
Lemma zb2gb_3pow_pos : forall n : nat, (1 <= 3 ^ n)%nat.
Proof.
  intro n. assert (Hne : (3 ^ n <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  lia.
Qed.

(* ===================================================================== *)
(* §1 C-链方程与正性                                                     *)
(* ===================================================================== *)

(* C-链方程（精确）：1 ≤ n 则 fact n = z2v_den n n · z2v_C n。
   （z2v_den n n 整除 fact n（valbridge z2v_den_dvd），除法定义式回读。） *)
Lemma zb2gb_C_fact_eq : forall n : nat,
  (1 <= n)%nat -> fact n = z2v_den n n * z2v_C n.
Proof.
  intros n Hn. unfold z2v_C.
  destruct (z2v_den_dvd n Hn) as [t Ht].
  pose proof (z2v_den_pos n n) as Hdp.
  rewrite Ht.
  rewrite Nat.div_mul by lia.
  ring.
Qed.

(* C 正性：1 ≤ z2v_C n（全 n；n = 0 档直算 z2v_C 0 = 1） *)
Lemma zb2gb_C_pos : forall n : nat, (1 <= z2v_C n)%nat.
Proof.
  intro n. destruct n as [| m].
  - vm_compute. lia.
  - destruct (z2v_C (S m)) eqn:EC.
    + exfalso. pose proof (zb2gb_C_fact_eq (S m) ltac:(lia)) as Heq.
      rewrite EC in Heq.
      rewrite Nat.mul_0_r in Heq.
      pose proof (h3_fact_pos (S m)). lia.
    + lia.
Qed.

(* 整除⟹≤ 三前提形（若漏被除式正性，整除 0 即成反例） *)
Lemma zb2gb_dvd_le : forall a b : nat,
  Nat.divide a b -> (1 <= a)%nat -> (1 <= b)%nat -> (a <= b)%nat.
Proof.
  intros a b Hd Ha Hb. destruct Hd as [p Hp].
  assert (Hp1 : (1 <= p)%nat).
  { destruct p as [| p']; [rewrite Nat.mul_0_l in Hp; lia | lia]. }
  rewrite Hp, (Nat.mul_comm p a).
  rewrite <- (Nat.mul_1_r a) at 1.
  apply Nat.mul_le_mono_l. exact Hp1.
Qed.

(* ===================================================================== *)
(* §2 Sylvester 增值积 z2gb_G 与分母积步进机                              *)
(* ===================================================================== *)

(* 增值积承载：z2gb_G k n := ∏_{j<k} f_j，f_j = n/a_{j+1}（若 a_{j+1} ∣ n）
   否则 1。这是分母积 fact(⌊n/a⌋) 在 n 增一时的精确比值积。 *)
Fixpoint z2gb_G (k n : nat) : nat :=
  match k with
  | O => 1
  | S k' =>
      z2gb_G k' n *
      (if Nat.eqb (n mod z2d_sylv_a k') 0 then n / z2d_sylv_a k' else 1)
  end.

(* 阶乘的层商步进（每档比值核）：1 ≤ a 则
   fact(S m/a) = fact(m/a)·[a ∣ S m 时的 S m/a，否则 1]。
   （z2v_inc：层商在 a ∣ S m 档恰跳一。） *)
Lemma zb2gb_fact_step : forall m a : nat,
  (1 <= a)%nat ->
  fact (S m / a) =
  fact (m / a) * (if Nat.eqb (S m mod a) 0 then S m / a else 1).
Proof.
  intros m a Ha.
  pose proof (z2v_inc m a Ha) as Hinc.
  destruct (Nat.eq_dec (S m mod a) 0) as [Hz | Hnz].
  - rewrite Hz in Hinc.
    rewrite Nat.eqb_refl in Hinc.
    change (if true then 1 else 0) with 1 in Hinc.
    rewrite Hz.
    rewrite Nat.eqb_refl.
    change (if true then S m / a else 1) with (S m / a).
    rewrite Hinc.
    rewrite Nat.add_1_r.
    cbn [fact]. ring.
  - apply Nat.eqb_neq in Hnz.
    rewrite Hnz in Hinc.
    change (if false then 1 else 0) with 0 in Hinc.
    rewrite Hnz.
    change (if false then S m / a else 1) with 1.
    assert (Hzero : (S m / a = m / a)%nat) by lia.
    rewrite Hzero. ring.
Qed.

(* 增值积正性：1 ≤ n 则 1 ≤ z2gb_G k n（全 k） *)
Lemma zb2gb_G_ge1 : forall k n : nat, (1 <= n)%nat -> (1 <= z2gb_G k n)%nat.
Proof.
  induction k as [| k IH]; intros n Hn.
  - cbn [z2gb_G]. lia.
  - cbn [z2gb_G].
    destruct (Nat.eq_dec (n mod z2d_sylv_a k) 0) as [Hm0 | Hm0].
    + rewrite Hm0.
      rewrite Nat.eqb_refl.
      change (if true then n / z2d_sylv_a k else 1)
        with (n / z2d_sylv_a k).
      destruct (n / z2d_sylv_a k) as [| q'] eqn:Ed.
      * exfalso.
        pose proof (Nat.div_mod_eq n (z2d_sylv_a k)) as Hdm.
        rewrite Ed in Hdm.
        rewrite Hm0 in Hdm.
        lia.
      * pose proof (IH n Hn).
        change (1 * 1 <= z2gb_G k n * S q')%nat.
        apply Nat.mul_le_mono; lia.
    + rewrite (proj2 (Nat.eqb_neq (n mod z2d_sylv_a k) 0) Hm0).
      change (if false then n / z2d_sylv_a k else 1) with 1.
      pose proof (IH n Hn). lia.
Qed.

(* P ≥ 2^k：Sylvester 累乘的下指数锚（P_0 = 1 = 2^0，步档翻番） *)
Lemma zb2gb_sylvP_ge_pow2 : forall k : nat, (2 ^ k <= z2d_sylv_P k)%nat.
Proof.
  induction k as [| k IH].
  - cbn [z2d_sylv_P Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. cbn [z2d_sylv_P].
    apply Nat.le_trans with (m := 2 * z2d_sylv_P k).
    + apply Nat.mul_le_mono_l. exact IH.
    + pose proof (z2d_sylv_P_pos k) as Hp.
      rewrite (Nat.mul_comm 2 (z2d_sylv_P k)).
      apply Nat.mul_le_mono_l. lia.
Qed.

(* 分母积的层界正性：m < a_k 则分母积多折一层不变（a_k > m ⟹ ⌊m/a_k⌋ = 0） *)
Lemma zb2gb_den_tail1 : forall k m : nat,
  (m < z2d_sylv_a k)%nat -> z2v_den (S k) m = z2v_den k m.
Proof.
  intros k m Hlt. cbn [z2v_den].
  rewrite (Nat.div_small m (z2d_sylv_a k) Hlt).
  cbn [fact]. lia.
Qed.

(* 分母积步进机（本件核心机一）：1 ≤ n 则
   z2v_den k n = z2v_den k (n−1) · z2gb_G k n。
   每档：a ∣ n 时 fact(n/a) = fact((n−1)/a)·(n/a)（层商恰跳一），
   a ∤ n 时商不变、因子为 1——逐档即 zb2gb_fact_step。 *)
Lemma zb2gb_den_G : forall k n : nat,
  (1 <= n)%nat -> z2v_den k n = z2v_den k (n - 1) * z2gb_G k n.
Proof.
  intros k n Hn. destruct n as [| m]; [lia |].
  induction k as [| k IH].
  - cbn [z2v_den z2gb_G]. lia.
  - cbn [z2v_den z2gb_G].
    replace (S m - 1) with m by lia.
    pose proof (z2d_sylv_a_neq0 k) as Hak.
    assert (Hone : (1 <= z2d_sylv_a k)%nat) by lia.
    remember ((if Nat.eqb (S m mod z2d_sylv_a k) 0
               then S m / z2d_sylv_a k else 1)) as F eqn:EF.
    rewrite (zb2gb_fact_step m (z2d_sylv_a k) Hone).
    rewrite <- EF.
    replace (S m - 1) with m in IH by lia.
    rewrite IH. ring.
Qed.

(* ===================================================================== *)
(* §3 引擎恒等式一：C 的精确步进递归                                      *)
(* ===================================================================== *)

(* C 步进恒等式（无条件·全强度）：m ≥ 1 则
   z2v_C (S m) · z2gb_G (S m) (S m) = S m · z2v_C m。
   链序：fact (S m) 的两个精确表达式（C-链方程顶底各一）配
   分母积步进机（§2，配 a_m > m 的层界正性收尾档）对账消去。 *)
Lemma zb2gb_C_step : forall m : nat,
  (1 <= m)%nat -> z2v_C (S m) * z2gb_G (S m) (S m) = S m * z2v_C m.
Proof.
  intros m Hm.
  pose proof (zb2gb_C_fact_eq (S m) ltac:(lia)) as Etop.
  pose proof (zb2gb_C_fact_eq m Hm) as Ebot.
  pose proof (zb2gb_den_G (S m) (S m) ltac:(lia)) as EG1.
  replace (S m - 1) with m in EG1 by lia.
  assert (Ham : (m < z2d_sylv_a m)%nat).
  { unfold z2d_sylv_a.
    pose proof (zb2gb_sylvP_ge_pow2 m) as Hp2.
    pose proof (Nat.pow_gt_lin_r 2 m ltac:(lia)) as Hgt. lia. }
  pose proof (zb2gb_den_tail1 m m Ham) as Et.
  pose proof (z2v_den_pos m m) as Hdp.
  assert (Hdnz : (z2v_den m m <> 0)%nat) by lia.
  assert (E2 : fact (S m) = (z2v_C (S m) * z2gb_G (S m) (S m)) * z2v_den m m).
  { rewrite Etop. rewrite EG1. rewrite Et. ring. }
  assert (E1 : fact (S m) = (S m * z2v_C m) * z2v_den m m).
  { cbn [fact]. rewrite Ebot. ring. }
  pose proof (proj1 (Nat.mul_cancel_r (z2v_C (S m) * z2gb_G (S m) (S m))
                       (S m * z2v_C m) (z2v_den m m) Hdnz)
               (eq_trans (eq_sym E2) E1)) as Ef.
  exact Ef.
Qed.

(* 数值锚（小实例直算）：z2gb_G 6 6 = 6（2·3 整除 6，其余档因子 1）；
   与 C 步进恒等式在 n = 6 的直算闭合 60·6 = 6·60。 *)
Lemma zb2gb_G_smoke_6 : z2gb_G 6 6 = 6.
Proof. reflexivity. Qed.

Lemma zb2gb_C_step_smoke : z2v_C 6 * z2gb_G 6 6 = 6 * z2v_C 5.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §4 引擎恒等式二：增值积的满档再注入（P_k 处的账本续满位）               *)
(* ===================================================================== *)

(* 增值积的倍程恒等式：诸 a_j（j<k）整除 X 时，
   z2gb_G k (c·X) = z2gb_G k X · c^k
   （每档因子 c·X/a_j = c·(X/a_j)，k 档合出 c^k——照 z2d_sylv_sum_mul 同型）。 *)
Lemma zb2gb_G_scale : forall k c X : nat,
  (forall j : nat, (j < k)%nat -> Nat.divide (z2d_sylv_a j) X) ->
  z2gb_G k (c * X) = z2gb_G k X * (c ^ k)%nat.
Proof.
  induction k as [| k IH]; intros c X Hd.
  - reflexivity.
  - cbn [z2gb_G].
    destruct (Hd k (Nat.lt_succ_diag_r k)) as [q Hq].
    pose proof (z2d_sylv_a_neq0 k) as Ha0.
    assert (Hmod1 : (X mod z2d_sylv_a k = 0)%nat).
    { rewrite Hq. rewrite Nat.Div0.mod_mul. lia. }
    assert (Hmodx : Nat.eqb (X mod z2d_sylv_a k) 0 = true)
      by (apply Nat.eqb_eq; exact Hmod1).
    assert (Hdiv1 : X / z2d_sylv_a k = q)
      by (rewrite Hq at 1; apply Nat.div_mul; exact Ha0).
    assert (Hmodc : Nat.eqb ((c * X) mod z2d_sylv_a k) 0 = true).
    { apply Nat.eqb_eq. rewrite Hq at 1.
      rewrite Nat.mul_assoc. rewrite Nat.Div0.mod_mul. lia. }
    assert (Hdivc : (c * X) / z2d_sylv_a k = c * (X / z2d_sylv_a k)).
    { rewrite Hq at 1. rewrite Nat.mul_assoc.
      rewrite Nat.div_mul by exact Ha0.
      rewrite Hdiv1. reflexivity. }
    rewrite Hmodx.
    change (if true then X / z2d_sylv_a k else 1) with (X / z2d_sylv_a k).
    rewrite Hdiv1.
    rewrite Hmodc.
    change (if true then c * (X / z2d_sylv_a k) else 1)
      with (c * (X / z2d_sylv_a k)).
    rewrite Hdivc.
    rewrite Hdiv1.
    rewrite (IH c X) by (intros j Hj; apply Hd; lia).
    rewrite Nat.pow_succ_r'. ring.
Qed.

(* 满档再注入恒等式（无条件·全强度）：
   z2gb_G k (z2d_sylv_P k) · z2d_sylv_P k = (z2d_sylv_P k)^k。
   P_k 处诸 a_j（j<k）全整除（z2d_sylv_dvd），增值积满档；步档配
   P_{k+1} = a_{k+1}·P_k 与倍程恒等式闭合。这是 C 步进账本在
   Sylvester 锚点处的续满引擎。 *)
Lemma zb2gb_G_sylv : forall k : nat,
  z2gb_G k (z2d_sylv_P k) * z2d_sylv_P k = ((z2d_sylv_P k) ^ k)%nat.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - assert (Hdvd : forall j : nat, (j < k)%nat -> Nat.divide (z2d_sylv_a j) (z2d_sylv_P k))
      by (intros j Hj; apply z2d_sylv_dvd; exact Hj).
    cbn [z2gb_G].
    assert (Hmodstep : Nat.eqb (z2d_sylv_P (S k) mod z2d_sylv_a k) 0 = true).
    { apply Nat.eqb_eq. unfold z2d_sylv_a, z2d_sylv_P.
      rewrite Nat.Div0.mod_mul. lia. }
    rewrite Hmodstep.
    change (if true then z2d_sylv_P (S k) / z2d_sylv_a k else 1)
      with (z2d_sylv_P (S k) / z2d_sylv_a k).
    assert (Hdivstep : z2d_sylv_P (S k) / z2d_sylv_a k = z2d_sylv_P k).
    { unfold z2d_sylv_a, z2d_sylv_P. apply Nat.div_mul.
      pose proof (z2d_sylv_P_pos k). lia. }
    rewrite Hdivstep.
    assert (Hfold : z2d_sylv_P (S k) = z2d_sylv_a k * z2d_sylv_P k).
    { unfold z2d_sylv_a, z2d_sylv_P. rewrite Nat.mul_comm. reflexivity. }
    rewrite Hfold.
    rewrite (zb2gb_G_scale k (z2d_sylv_a k) (z2d_sylv_P k) Hdvd).
    rewrite Nat.pow_succ_r'.
    rewrite Nat.pow_mul_l.
    rewrite <- IH. ring.
Qed.

(* 数值锚：z2gb_G 3 (z2d_sylv_P 3) · 42 = 42^3
   （P_3 = 42 = 2·3·7，增值积 = 21·14·6，21·14·6·42 = 74088 = 42^3） *)
Lemma zb2gb_G_sylv_smoke_3 :
  z2gb_G 3 (z2d_sylv_P 3) * z2d_sylv_P 3 = ((z2d_sylv_P 3) ^ 3)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §5 M3′ 合拢链（整除 + 正性 + 上界 ⟹ 3^n 界）                          *)
(* ===================================================================== *)

(* M3′ 合拢主链（Set 面·hl_id 承载）：C 上界给定则 lcm ≤ 3^n。
   链序：z2v_lcm_dvd_C（valbridge 全强度整除）⟹ lcm ≤ C（三前提形）
   ⟹ lcm ≤ 3^n。 *)
Theorem zb2gb_lcm_le_3pow_cond : forall n : nat,
  (1 <= n)%nat -> (z2v_C n <= 3 ^ n)%nat ->
  hl_le_t (hl_lcm_upto n) (3 ^ n)%nat.
Proof.
  intros n Hn HC. apply hl_le_to_le_t.
  pose proof (z2v_lcm_dvd_C n) as Hdd.
  pose proof (h3_lcm_pos n) as Hlp.
  pose proof (zb2gb_C_pos n) as Hcp.
  pose proof (zb2gb_3pow_pos n) as H3p.
  pose proof (zb2gb_dvd_le (hl_lcm_upto n) (z2v_C n) Hdd Hlp Hcp) as Hle.
  lia.
Qed.

(* ===================================================================== *)
(* §6 验收语句（勘形 §3 验收判据名·Q 层 Set 面·显式前提位）                *)
(* ===================================================================== *)

(* 验收语句（响亮登记：前提 z2v_C n ≤ 3^n 即未竟核心 M2′ 的接口位，
   到位后本句即无条件化；此前提为语句假设位，非公理，零承认）。 *)
Theorem z2d_lcm_le_3pow : forall n : nat,
  (1 <= n)%nat -> (z2v_C n <= 3 ^ n)%nat ->
  QleT' ((Z.of_nat (hl_lcm_upto n) # 1)%Q) ((Z.of_nat (3 ^ n) # 1)%Q).
Proof.
  intros n Hn HC. apply zb2gb_Qnat_le.
  pose proof (hl_le_t_to_le (hl_lcm_upto n) (3 ^ n)%nat
                (zb2gb_lcm_le_3pow_cond n Hn HC)) as Hle. exact Hle.
Qed.

(* 数值冒烟（Set 面可执行）：n = 6 实例全链直算
   （lcm(1..6) = 60 ≤ 3^6 = 729；C(6) = 60 ≤ 729 前提直算） *)
Lemma zb2gb_smoke_6 : hl_le_t (hl_lcm_upto 6) (3 ^ 6)%nat.
Proof.
  apply (zb2gb_lcm_le_3pow_cond 6).
  - lia.
  - vm_compute. lia.
Qed.

(* ===================================================================== *)
(* §7 尾舱：主语句公理面自检                                              *)
(* ===================================================================== *)

Print Assumptions zb2gb_natQ_ge0.
Print Assumptions zb2gb_Qnat_le.
Print Assumptions zb2gb_3pow_pos.
Print Assumptions zb2gb_C_fact_eq.
Print Assumptions zb2gb_C_pos.
Print Assumptions zb2gb_dvd_le.
Print Assumptions zb2gb_fact_step.
Print Assumptions zb2gb_G_ge1.
Print Assumptions zb2gb_sylvP_ge_pow2.
Print Assumptions zb2gb_den_tail1.
Print Assumptions zb2gb_den_G.
Print Assumptions zb2gb_C_step.
Print Assumptions zb2gb_G_smoke_6.
Print Assumptions zb2gb_C_step_smoke.
Print Assumptions zb2gb_G_scale.
Print Assumptions zb2gb_G_sylv.
Print Assumptions zb2gb_G_sylv_smoke_3.
Print Assumptions zb2gb_lcm_le_3pow_cond.
Print Assumptions z2d_lcm_le_3pow.
Print Assumptions zb2gb_smoke_6.
