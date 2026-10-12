(* ============================================================ *)
(* u5c_pr_bertrand_close.v                                        *)
(* 模块名：u5c_pr_bertrand_close                                   *)
(* 数学使命：Erdős 路线的全强度 Bertrand 定理——∀n≥2，(n,2n] 内存在   *)
(*   素数（sigT 见证，主定理 u5c_bertrand_full）。四段：§1/§1b 锐化    *)
(*   primorial 上界：pec_prim N ≤ 4^N（将依赖件 abl_Pr_erdos_theta 的  *)
(*   pec_theta_bound 常数 4^(2N) 锐化一半；偶步恒等式                  *)
(*   pec_prim(2n)=pec_prim n·∏_{n<p≤2n} p 直推，上界半边硬前置）。      *)
(*   §2/§2b/§2c/§2d 素数表成员桥与 Legendre 型主机：素 q、2≤q≤N ⟹     *)
(*     q ∈ (1,N] 窗表且 q ∣ pec_prim N；互素面素幂合并与消去；        *)
(*     Qp 分割、指数和、余因子；中项主语句 C(2n,n) 的 p-指数完全      *)
(*     提取（sigT Set 面）。                                          *)
(*   §7 数值主链：2^t ≥ t²、Bernoulli 型块估计 (a+8)^E·(a−8E) ≤        *)
(*     a^(E+1)、根号分块 [2m²,2(m+1)²)、块内步长 4、基例 m-归纳         *)
(*     （stride-3，吸 4^(4m+6)），终局不等式                            *)
(*     (2n+1)(2n)^(⌊√(2n)/2⌋+2) < 4^(⌊n/3⌋) ∀n≥512。                  *)
(*   §8 装配：互素面 C=A·C′ 分裂与方消＋值域素归纳＋表域 [2,512]       *)
(*     拼接＋≥512 解析反证，合成 u5c_bertrand_full。                  *)
(* 依赖清单：HansonLcm（hl_le_t）＋abl_Pr_erdos_core                  *)
(*   （pec_erdos_skeleton 两肢）＋abl_Pr_erdos_theta（pec_prim／        *)
(*   pec_winprod_le／pec_prim_monotone／pec_win_app／pec_prod_app）＋   *)
(*   纯 Stdlib（Arith.Arith／Bool／List／Lia）。                        *)
(* 构造性注记：否定形自持 P 蕴含 False，全件零否定记号与不等记号（含   *)
(*   内部）；零公理零承认零经典逻辑；pec_prim 沿依赖件可提取；文尾      *)
(*   Print Assumptions 取证面。                                        *)
(* 编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/       *)
(*   toolchain/env.sh && cd <池> && bash cpu_guard.sh -Direct --       *)
(*   rocq c -native-compiler no -q -Q . "" u5c_pr_bertrand_close.v     *)
(*   （依赖件 vo 经 -Q 映射挂源根，只读引用）                           *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Bool Lia List.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_erdos_core.
Require Import abl_Pr_erdos_theta.
Require Import abl_Pr_bertrand.

(* ---- §1 锐化 primorial 上界：pec_prim N ≤ 4^N ---- *)

(* 偶步恒等式：pec_prim(2n) ＝ pec_prim n · ∏_{n<p≤2n} p
   （(1,2n] 窗表按高段 (n,2n] ++ 低段 (1,n] 二分，积对拼接可乘） *)
Lemma u5c_prim_even : forall n : nat, pec_prim (2 * n) = pec_prim n * pec_winprod n.
Proof.
  intro n. destruct n as [|m].
  - unfold pec_prim, pec_winprod. reflexivity.
  - unfold pec_prim, pec_winprod.
    assert (Hs : 2 * S m - 1 = m + S m) by lia.
    rewrite Hs. rewrite pec_win_app. rewrite pec_prod_app.
    assert (H1 : 1 + m = S m) by lia.
    rewrite H1.
    assert (H2 : S m - 1 = m) by lia.
    rewrite H2.
    rewrite Nat.mul_comm. reflexivity.
Qed.

(* ---- §1b 奇步上界机器：奇数行中央二项式与奇窗积整除 ----
   （奇数步 N=2m+1 的锐化走 Erdős 标准路线：pec_prim(2m+1) =
     pec_prim(m+1)·∏_{(m+1,2m+1]}，后者整除奇数行中央二项式
     C(2m+1,m) ≤ 4^m——行和中两个相等的中央项给出上界） *)

(* 除法定值：p·q ≤ a < p·(S q) ⟹ a / p = q *)
Lemma u5c_div_eq : forall p a q : nat, p * q <= a -> a < p * S q -> a / p = q.
Proof.
  intros p a q Hlo Hhi.
  assert (Hp : p <> 0) by lia.
  pose proof (Nat.div_mod_eq a p) as Hdm.
  pose proof (Nat.mod_upper_bound a p Hp) as Hm.
  assert (Hup0 : a / p < S q) by (apply Nat.div_lt_upper_bound; assumption).
  assert (Hup : a / p <= q) by lia.
  destruct (Nat.eq_dec q (a / p)) as [E | NE].
  - symmetry. exact E.
  - exfalso.
    assert (Hlt : a / p < q) by lia.
    assert (Hle1 : p * (a / p) <= p * (q - 1)) by (apply Nat.mul_le_mono_l; lia).
    assert (Hstep : p * (q - 1) + p = p * q).
    { destruct q as [|q'].
      - lia.
      - replace (S q' - 1) with q' by lia. lia. }
    lia.
Qed.

(* 乘法左结合（方向自钉，immune to stdlib assoc 方向） *)
Lemma u5c_mul_assoc_l : forall a b c : nat, (a * b) * c = a * (b * c).
Proof. intros a b c. symmetry. apply Nat.mul_assoc. Qed.

(* 商归零：d ≠ 0、a < d ⟹ a / d = 0 *)
Lemma u5c_div_eq_zero : forall d a : nat, d <> 0 -> a < d -> a / d = 0.
Proof.
  intros d a Hd Hlt.
  assert (Hlt1 : a / d < 1) by (apply (Nat.div_lt_upper_bound a d 1); [exact Hd | lia]).
  lia.
Qed.

(* 折叠和两项压制：i < j < m ⟹ f i + f j ≤ Σ_{k<m} f k *)
Lemma u5c_sum_two : forall (f : nat -> nat) (m i j : nat),
  i < j -> j < m -> f i + f j <= pec_sum f m.
Proof.
  intros f m. induction m as [|m IH]; intros i j Hij Hjm.
  - lia.
  - cbn [pec_sum]. destruct (Nat.eq_dec j m) as [Ej | NEj].
    + subst j.
      assert (Hfi : f i <= pec_sum f m) by (apply (pec_sum_ge m i f); lia).
      lia.
    + assert (Hrec : f i + f j <= pec_sum f m) by (apply IH; lia).
      lia.
Qed.

(* 奇数行中央二项式：C(2m+1, m) ≤ 4^m
   （行和 2^(2m+1) = 2·4^m 中第 m 与 m+1 项相等，两项和 ≤ 全行和） *)
Lemma u5c_binom_odd_le : forall m : nat, hl_binom (2 * m + 1) m <= 4 ^ m.
Proof.
  intro m.
  assert (Htwo : hl_binom (2 * m + 1) m + hl_binom (2 * m + 1) (m + 1)
                 <= pec_sum (hl_binom (2 * m + 1)) (S (2 * m + 1))).
  { apply (u5c_sum_two (hl_binom (2 * m + 1)) (S (2 * m + 1)) m (m + 1)); lia. }
  rewrite pec_row_sum in Htwo.
  assert (Hsym : hl_binom (2 * m + 1) m = hl_binom (2 * m + 1) (m + 1)).
  { replace (m + 1) with (2 * m + 1 - m) by lia.
    apply pec_binom_sym. lia. }
  assert (Hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m).
  { replace (2 * m + 1) with (S (2 * m)) by lia.
    rewrite Nat.pow_succ_r'.
    rewrite hl_pow4. reflexivity. }
  lia.
Qed.

(* 一般窗积整除：窗内素数个个整除 C、窗宽 ≤ 窗起点 ⟹ 折叠积 ∣ C
   （窗头 x = a+S w 为最大素：x ∣ C、x ∤ 余表折叠积（成员素数更小）、
     pec_combine 合并；归纳于窗宽 w） *)
Lemma u5c_winprod_dvd_gen : forall a w C : nat, w <= a ->
  (forall p : nat, pr_prime p -> a < p -> p <= a + w -> pec_dvd p C) ->
  exists z : nat, C = fold_right Nat.mul 1 (pec_win a w) * z.
Proof.
  intros a w C. induction w as [|w IH]; intros Hw Hdiv.
  - exists C. cbn [pec_win fold_right]. rewrite Nat.mul_1_l. reflexivity.
  - cbn [pec_win]. destruct (pr_prime_bool (a + S w)) eqn:Eb.
    + assert (Hpx : pr_prime (a + S w)) by (apply pr_prime_bool_true; exact Eb).
      assert (Hd1 : pec_dvd (a + S w) C) by (apply Hdiv; [exact Hpx | lia | lia]).
      assert (HnP : pec_dvd (a + S w) (fold_right Nat.mul 1 (pec_win a w)) -> False).
      { intros Hd.
        destruct (pec_prime_dvd_prod_in (a + S w) (pec_win a w) Hpx Hd)
          as [q [Hin Hq]].
        destruct (pec_win_in a w q Hin) as [Hq1 [Hq2 Hq3]].
        assert (Heq : a + S w = q)
          by (apply (pec_prime_dvd_prime (a + S w) q Hpx Hq1 Hq)).
        lia. }
      assert (Hw' : w <= a) by lia.
      assert (Hhyp : forall p : nat, pr_prime p -> a < p -> p <= a + w ->
                pec_dvd p C).
      { intros p Hp1 Hp2 Hp3. apply Hdiv; [exact Hp1 | exact Hp2 | lia]. }
      destruct (IH Hw' Hhyp) as [z' Hz'].
      assert (HdP : pec_dvd (fold_right Nat.mul 1 (pec_win a w)) C)
        by (apply (pec_dvd_of_eq _ _ z' Hz')).
      destruct (pec_combine (a + S w) (fold_right Nat.mul 1 (pec_win a w)) C
                            Hpx HnP Hd1 HdP) as [u Hu].
      exists u. cbn [fold_right]. exact Hu.
    + assert (Hw' : w <= a) by lia.
      assert (Hhyp : forall p : nat, pr_prime p -> a < p -> p <= a + w ->
                pec_dvd p C).
      { intros p Hp1 Hp2 Hp3. apply Hdiv; [exact Hp1 | exact Hp2 | lia]. }
      apply (IH Hw' Hhyp).
Qed.

(* 奇窗素整除：S m < p ≤ 2m+1 素 ⟹ p ∣ C(2m+1, m)
   （p 整除 (2m+1)! 而不整除 m!·(m+1)!，Euclid 两刀压出） *)
Lemma u5c_odd_prime_dvd : forall m p : nat, pr_prime p -> S m < p -> p <= 2 * m + 1 ->
  pec_dvd p (hl_binom (2 * m + 1) m).
Proof.
  intros m p Hp Hsm Hp2m.
  assert (Hdf : pec_dvd p (fact (2 * m + 1)))
    by (apply pec_prime_dvd_fact; [exact Hp | lia]).
  assert (Hd1 : pec_dvd p (fact m) -> False)
    by (apply pec_prime_not_dvd_fact; [exact Hp | lia]).
  assert (Hd2 : pec_dvd p (fact (S m)) -> False)
    by (apply pec_prime_not_dvd_fact; [exact Hp | lia]).
  pose proof (pec_binom_fact (2 * m + 1) m ltac:(lia)) as Hbf.
  replace (2 * m + 1 - m) with (S m) in Hbf by lia.
  assert (HdC : pec_dvd p (hl_binom (2 * m + 1) m * (fact m * fact (S m)))).
  { destruct Hdf as [z0 Hz0]. exists z0.
    rewrite Nat.mul_assoc. rewrite Hbf. exact Hz0. }
  destruct (pec_euclid p (hl_binom (2 * m + 1) m) (fact m * fact (S m)) Hp HdC)
    as [H1 | H12].
  - exact H1.
  - destruct (pec_euclid p (fact m) (fact (S m)) Hp H12) as [H2 | H2].
    + exfalso. apply Hd1. exact H2.
    + exfalso. apply Hd2. exact H2.
Qed.

(* 主上界：N ≥ 1 ⟹ pec_prim N ≤ 4^N
   （偶数：偶步 pec_prim(2k) = pec_prim k·∏_{(k,2k]} 两半乘；
     奇数：pec_prim(2m+1) = pec_prim(m+1)·∏_{(m+1,2m+1]}，
     奇窗积整除 C(2m+1,m) ≤ 4^m——θ(N) 的 nat 线性常数由 4·ln2
     锐化至 2·ln2） *)
Lemma u5c_prim_le_pow4 : forall N : nat, 1 <= N -> pec_prim N <= 4 ^ N.
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun N => 1 <= N -> pec_prim N <= 4 ^ N)).
  intros N IH HN.
  destruct (Nat.Even_or_Odd N) as [[k Hk] | [k Hk]].
  - assert (Hk1 : 1 <= k) by lia.
    assert (Hkn : k < N) by lia.
    specialize (IH k Hkn Hk1).
    rewrite Hk. rewrite u5c_prim_even.
    replace (2 * k) with (k + k) by lia.
    rewrite Nat.pow_add_r. apply Nat.mul_le_mono; [exact IH | apply pec_winprod_le].
  - rewrite Hk. destruct k as [|k'].
    + cbn. lia.
    + unfold pec_prim.
      replace (2 * S k' + 1 - 1) with (S k' + S k') by lia.
      rewrite (pec_win_app 1 (S k') (S k')). rewrite pec_prod_app.
      replace (1 + S k') with (S (S k')) by lia.
      replace (fold_right Nat.mul 1 (pec_win 1 (S k')))
        with (pec_prim (S (S k'))) by reflexivity.
      replace (2 * S k' + 1) with (S k' + S (S k')) by lia.
      rewrite Nat.pow_add_r.
      assert (Hprim : pec_prim (S (S k')) <= 4 ^ S (S k')) by (apply IH; lia).
      assert (HC : hl_binom (2 * S k' + 1) (S k') <= 4 ^ S k')
        by apply u5c_binom_odd_le.
      assert (Hfold : fold_right Nat.mul 1 (pec_win (S (S k')) (S k'))
                      <= hl_binom (2 * S k' + 1) (S k')).
      { assert (Hpos : 1 <= hl_binom (2 * S k' + 1) (S k'))
          by (apply pec_binom_pos; lia).
        assert (Hhyp : forall p : nat, pr_prime p -> S (S k') < p ->
                  p <= S (S k') + S k' ->
                  pec_dvd p (hl_binom (2 * S k' + 1) (S k'))).
        { intros p Hp1 Hp2 Hp3.
          apply (u5c_odd_prime_dvd (S k') p); [exact Hp1 | lia | lia]. }
        destruct (u5c_winprod_dvd_gen (S (S k')) (S k')
                    (hl_binom (2 * S k' + 1) (S k')) ltac:(lia) Hhyp)
          as [z Hz].
        assert (H1f : 1 <= fold_right Nat.mul 1 (pec_win (S (S k')) (S k'))).
        { apply pec_prod_ge1. intros x Hx. apply pec_win_in in Hx.
          destruct Hx as [Hpx _]. unfold pr_prime in Hpx.
          destruct Hpx as [Hpx2 _]. lia. }
        assert (H2f : 1 <= z).
        { destruct z as [|z'].
          - rewrite Nat.mul_0_r in Hz. lia.
          - rewrite Nat.mul_succ_r in Hz. lia. }
        apply Nat.le_trans with
          (fold_right Nat.mul 1 (pec_win (S (S k')) (S k')) * 1).
        - rewrite Nat.mul_1_r. apply Nat.le_refl.
        - rewrite Hz. apply Nat.mul_le_mono_l. exact H2f. }
      assert (Hcomb : fold_right Nat.mul 1 (pec_win (S (S k')) (S k'))
                      * pec_prim (S (S k'))
                      <= 4 ^ S k' * 4 ^ S (S k')).
      { apply Nat.mul_le_mono.
        - apply Nat.le_trans with (hl_binom (2 * S k' + 1) (S k')).
          + exact Hfold.
          + exact HC.
        - apply Nat.le_trans with (pec_prim (S (S k'))).
          + apply Nat.le_refl.
          + exact Hprim. }
      exact Hcomb.
Qed.

(* ---- §2 素数表成员桥 ---- *)

(* 素 q、2 ≤ q ≤ N ⟹ q 入 (1,N] 窗表（沿窗表构造归纳，头值 1+S k'） *)
Lemma u5c_win_in_ex : forall N q : nat, 2 <= q -> q <= N -> pr_prime q ->
  In q (pec_win 1 (N - 1)).
Proof.
  induction N as [|N IH]; intros q H2 HN Hq.
  - lia.
  - destruct N as [|N'].
    + lia.
    + replace (S (S N') - 1) with (S N') by lia.
      cbn [pec_win].
      destruct (Nat.eq_dec q (S (S N'))) as [E | NE].
      * subst q. destruct (pr_prime_bool (1 + S N')) eqn:Eb.
        -- left. reflexivity.
        -- exfalso.
           assert (Hbt : pr_prime_bool (S (S N')) = true)
             by (apply pr_prime_bool_false; exact Hq).
           replace (1 + S N') with (S (S N')) in Eb by lia.
           rewrite Hbt in Eb. discriminate.
      * replace (S N' - 1) with N' in IH by lia.
        destruct (pr_prime_bool (1 + S N')).
        -- right.
           assert (Hqn : q <= S N') by lia.
           exact (IH q H2 Hqn Hq).
        -- assert (Hqn : q <= S N') by lia.
           exact (IH q H2 Hqn Hq).
Qed.

(* 表成员折叠整除：d 入表 ⟹ d ∣ 折叠积 *)
Lemma u5c_dvd_fold_in : forall (l : list nat) (d : nat),
  In d l -> pec_dvd d (fold_right Nat.mul 1 l).
Proof.
  induction l as [|q l IH]; intros d Hin.
  - destruct Hin.
  - cbn [fold_right]. destruct Hin as [E | Hin].
    + subst d. exists (fold_right Nat.mul 1 l). reflexivity.
    + apply pec_dvd_mul_r. apply IH. exact Hin.
Qed.

(* 素 q ≤ N ⟹ q ∣ pec_prim N *)
Lemma u5c_prime_dvd_prim : forall N q : nat, 2 <= q -> q <= N -> pr_prime q ->
  pec_dvd q (pec_prim N).
Proof.
  intros N q H2 HN Hq. unfold pec_prim.
  apply (u5c_dvd_fold_in (pec_win 1 (N - 1)) q).
  apply (u5c_win_in_ex N q); [exact H2 | exact HN | exact Hq].
Qed.

(* ---- §2b 互素面：素幂合并与无公因子消去 ---- *)

(* 素除素幂：d 素、p 素、d ∣ p^a ⟹ d = p *)
Lemma u5c_dvd_pow_eq : forall p a d : nat,
  2 <= p -> pr_prime p -> pr_prime d -> pec_dvd d (p ^ a) -> d = p.
Proof.
  intros p a. induction a as [|a IH]; intros d Hp2 Hpp Hd Hdv.
  - destruct Hd as [Hd2 _]. destruct Hdv as [z Hz].
    cbn [Nat.pow] in Hz.
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. lia.
    + assert (Hm : d * 1 <= d * S z') by (apply Nat.mul_le_mono_l; lia).
      rewrite Nat.mul_1_r in Hm. lia.
  - replace (p ^ S a) with (p * p ^ a) in Hdv
      by (rewrite Nat.pow_succ_r'; reflexivity).
    destruct (pec_euclid d p (p ^ a) Hd Hdv) as [H1 | H2].
    + apply (pec_prime_dvd_prime d p Hd Hpp H1).
    + apply IH; assumption.
Qed.

(* 无公因子消去：a ∣ b·x、a 与 b 无公共素因子 ⟹ a ∣ x
   （强归纳于 a：a≥2 取最小素因子 p，a = p·a1 降维，前提沿整除传递下降） *)
Lemma u5c_coprime_cancel : forall b a x : nat,
  1 <= a -> pec_dvd a (b * x) ->
  (forall d : nat, pr_prime d -> pec_dvd d a -> pec_dvd d b -> False) ->
  pec_dvd a x.
Proof.
  intros b a.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun a => forall x : nat, 1 <= a -> pec_dvd a (b * x) ->
       (forall d : nat, pr_prime d -> pec_dvd d a -> pec_dvd d b -> False) ->
       pec_dvd a x)).
  intros m IH x H1 Hdv Hnd.
  destruct m as [|m'].
  - exfalso. lia.
  - destruct (Nat.eq_dec (S m') 1) as [E1 | NE1].
    + replace m' with 0 by lia. exists x. symmetry. apply Nat.mul_1_l.
    + assert (Ha2 : 2 <= S m') by lia.
      destruct (pr_min_factor_exists (S m') Ha2) as [p [Hpa Hpp]].
      destruct Hpa as [a1 Ha1].
      rewrite (Nat.mul_comm a1 p) in Ha1.
      assert (Hp2 : 2 <= p)
        by (unfold pr_prime in Hpp; destruct Hpp as [Hp2 _]; exact Hp2).
      assert (Hp0 : p <> 0) by lia.
      assert (Hdv' : pec_dvd p (b * x)).
      { destruct Hdv as [u Hu]. exists (a1 * u).
        rewrite Hu, Ha1. rewrite Nat.mul_assoc. reflexivity. }
      destruct (pec_euclid p b x Hpp Hdv') as [Hb | Hx].
      * exfalso. exact (Hnd p Hpp (pec_dvd_of_eq p (S m') a1 Ha1) Hb).
      * destruct Hx as [w Hw].
        destruct Hdv as [u Hu].
        rewrite Hw, Ha1 in Hu.
        assert (H2 : p * (b * w) = p * (a1 * u)).
        { transitivity (b * (p * w)).
          - ring.
          - rewrite Hu. ring. }
        assert (Hbw : b * w = a1 * u).
        { apply (proj1 (Nat.mul_cancel_l (b * w) (a1 * u) p Hp0)). exact H2. }
        assert (Ha1pos : a1 <> 0).
        { intro Hz0. rewrite Hz0 in Ha1. rewrite Nat.mul_0_r in Ha1. lia. }
        assert (Ha1lt : a1 < S m').
        { destruct a1 as [|a1''].
          - exfalso. apply Ha1pos. reflexivity.
          - assert (H2p : 2 * S a1'' <= p * S a1'')
              by (apply Nat.mul_le_mono_r; lia).
            rewrite <- Ha1 in H2p. lia. }
        assert (Hnd1 : forall d0 : nat, pr_prime d0 -> pec_dvd d0 a1 ->
                  pec_dvd d0 b -> False).
        { intros d0 Hd0 Hda Hdb. apply (Hnd d0 Hd0).
          - destruct Hda as [t Ht].
            apply (pec_dvd_of_eq d0 (S m') (p * t)).
            rewrite Ha1, Ht. ring.
          - exact Hdb. }
        assert (Hrec : pec_dvd a1 w).
        { apply (IH a1 Ha1lt w); [lia | exact (pec_dvd_of_eq a1 (b * w) u Hbw)
                                  | exact Hnd1]. }
        destruct Hrec as [v Hv].
        exists v. rewrite Hw, Hv, Ha1. ring.
Qed.

(* 素幂合并：p^a ∣ C、P ∣ C、p ∤ P ⟹ p^a·P ∣ C *)
Lemma u5c_combine_pow : forall p a P C : nat,
  2 <= p -> pr_prime p -> 1 <= P ->
  pec_dvd (p ^ a) C -> pec_dvd P C -> (pec_dvd p P -> False) ->
  pec_dvd (p ^ a * P) C.
Proof.
  intros p a P C Hp2 Hpp HP Hdpa HdP HnP.
  destruct Hdpa as [z Hz]. destruct HdP as [w Hw].
  assert (Hd1 : pec_dvd P (p ^ a * z)).
  { exists w. rewrite <- Hz. exact Hw. }
  assert (Hnd : forall d : nat, pr_prime d -> pec_dvd d P ->
           pec_dvd d (p ^ a) -> False).
  { intros d Hd HdP' Hdpa'.
    rewrite (u5c_dvd_pow_eq p a d Hp2 Hpp Hd Hdpa') in HdP'.
    apply HnP. exact HdP'. }
  destruct (u5c_coprime_cancel (p ^ a) P z HP Hd1 Hnd) as [t Ht].
  exists t. rewrite Hz, Ht. ring.
Qed.

(* 逐素幂合并：无重复素表 l、逐 x 有 x^(S(e x)) ∣ C ⟹ 折叠积 ∣ C
   （指数取后继形：e x = 0 时 x 不整除折叠积，反例——
     C = 3、l = [2,3]、e = (0,1) 即反例；装配使用点指数恒 ≥ 1） *)
Lemma u5c_fold_dvd : forall (l : list nat) (e : nat -> nat) (C : nat),
  NoDup l ->
  (forall x : nat, In x l -> pr_prime x) ->
  (forall x : nat, In x l -> pec_dvd (x ^ S (e x)) C) ->
  pec_dvd (fold_right Nat.mul 1 l) C.
Proof.
  intros l. induction l as [|q l IH]; intros ee C Hnd Hprime Hpow.
  - exists C. cbn [fold_right]. rewrite Nat.mul_1_l. reflexivity.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd'].
    assert (Hq : pr_prime q) by (apply Hprime; left; reflexivity).
    assert (Hq2 : 2 <= q)
      by (unfold pr_prime in Hq; destruct Hq as [Hq2 _]; exact Hq2).
    assert (Hq1 : 1 <= q) by lia.
    assert (HnP : pec_dvd q (fold_right Nat.mul 1 l) -> False).
    { intros Hd.
      destruct (pec_prime_dvd_prod_in q l Hq Hd) as [r [Hin Hr]].
      assert (Hrq : q = r).
      { apply (pec_prime_dvd_prime q r);
          [exact Hq | apply Hprime; right; exact Hin | exact Hr]. }
      apply Hnin. rewrite <- Hrq in Hin. exact Hin. }
    assert (HP : 1 <= fold_right Nat.mul 1 l).
    { apply pec_prod_ge1. intros x Hx.
      assert (Hpx : pr_prime x) by (apply Hprime; right; exact Hx).
      unfold pr_prime in Hpx. destruct Hpx as [Hx2 _]. lia. }
    assert (Hpowq : pec_dvd (q ^ S (ee q)) C) by (apply Hpow; left; reflexivity).
    assert (Hpowrest : pec_dvd (fold_right Nat.mul 1 l) C).
    { apply (IH ee C); [exact Hnd' | intros x Hx; apply Hprime; right; exact Hx
                 | intros x Hx; apply Hpow; right; exact Hx]. }
    destruct (u5c_combine_pow q (S (ee q)) (fold_right Nat.mul 1 l) C
                Hq2 Hq HP Hpowq Hpowrest HnP) as [u Hu].
    exists (q ^ ee q * u). cbn [fold_right].
    rewrite Hu. replace (S (ee q)) with (ee q + 1) by lia.
    rewrite Nat.pow_add_r, Nat.pow_1_r. ring.
Qed.

(* ---- §2c Legendre 主机：Qp 分割、指数和、余因子 ---- *)

(* Qp：(1..m] 内 p 非倍数之积 *)
Fixpoint u5c_Qp (p m : nat) : nat :=
  match m with
  | 0 => 1
  | S m' => if Nat.eqb (S m' mod p) 0 then u5c_Qp p m' else S m' * u5c_Qp p m'
  end.

(* 余因子无隙：p 素 ⟹ p ∤ Qp p m *)
Lemma u5c_Qp_not_dvd : forall p m : nat, pr_prime p ->
  pec_dvd p (u5c_Qp p m) -> False.
Proof.
  intros p m Hp. pose proof Hp as Hpp.
  destruct Hp as [Hp2 _]. induction m as [|m IH]; intros Hd.
  - cbn [u5c_Qp] in Hd. destruct Hd as [z Hz].
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. lia.
    + rewrite Nat.mul_succ_r in Hz. lia.
  - cbn [u5c_Qp] in Hd. destruct (Nat.eqb (S m mod p) 0) eqn:E.
    + apply Nat.eqb_eq in E. apply IH. exact Hd.
    + apply Nat.eqb_neq in E. destruct Hd as [z Hz].
      assert (Hd2 : pec_dvd p (S m * u5c_Qp p m)) by (exists z; exact Hz).
      destruct (pec_euclid p (S m) (u5c_Qp p m) Hpp Hd2) as [H1 | H2].
      * exfalso.
        assert (Hdiv : Nat.divide p (S m))
          by (destruct H1 as [w Hw]; exists w; rewrite Nat.mul_comm; exact Hw).
        pose proof (pr_dvd_mod0 p (S m) ltac:(lia) Hdiv) as Hmod.
        rewrite Hmod in E. lia.
      * exfalso. apply IH. exact H2.
Qed.

(* Legendre 分割：fact m = p^(m/p)·fact(m/p)·Qp p m *)
Lemma u5c_fact_split : forall p m : nat, pr_prime p ->
  fact m = p ^ (m / p) * fact (m / p) * u5c_Qp p m.
Proof.
  intros p m Hp.
  assert (Hp0 : p <> 0) by (unfold pr_prime in Hp; destruct Hp as [Hp0 _]; lia).
  induction m as [|m IH].
  - rewrite Nat.Div0.div_0_l. reflexivity.
  - rewrite pec_fact_step. cbn [u5c_Qp].
    destruct (Nat.eqb (S m mod p) 0) eqn:E.
    + apply Nat.eqb_eq in E.
      pose proof (Nat.div_mod_eq (S m) p) as Hdm0.
      rewrite E in Hdm0. rewrite Nat.add_0_r in Hdm0.
      assert (Hdm1 : m = p * (m / p) + m mod p) by apply Nat.div_mod_eq.
      assert (Hubb : m mod p < p) by (apply Nat.mod_upper_bound; exact Hp0).
      destruct (S m / p) as [|q0] eqn:Eq.
      * lia.
      * assert (Hexpand : p * S q0 = p * q0 + p) by ring.
        assert (Hm1 : p * q0 <= m) by lia.
        assert (Hii : m < p * S q0) by lia.
        assert (Hmp : m / p = q0) by (apply (u5c_div_eq p m q0); assumption).
        rewrite IH, Hmp.
        rewrite (pec_fact_step q0). rewrite (Nat.pow_succ_r' p q0).
        rewrite Hdm0. ring.
    + apply Nat.eqb_neq in E.
      pose proof (Nat.div_mod_eq m p) as Hdm1.
      assert (Hubb : m mod p < p) by (apply Nat.mod_upper_bound; exact Hp0).
      assert (Hcase : m mod p < p - 1).
      { destruct (Nat.eq_dec (m mod p) (p - 1)) as [Heq | Hne].
        - exfalso. apply E.
          assert (Hdv : Nat.divide p (S m)) by (exists (S (m / p)); lia).
          pose proof (pr_dvd_mod0 p (S m) ltac:(lia) Hdv) as Hmod.
          exact Hmod.
        - lia. }
      assert (Hsp : S m / p = m / p).
      { apply (u5c_div_eq p (S m) (m / p)); lia. }
      rewrite Hsp, IH. ring.
Qed.

(* Legendre 指数和：leg p m K = ⌊m/p⌋ + ⌊m/p²⌋ + … + ⌊m/p^(K+1)⌋ *)
Fixpoint u5c_leg (p m K : nat) : nat :=
  match K with
  | 0 => m / p
  | S K' => m / p ^ S (S K') + u5c_leg p m K'
  end.

(* 指数和位移：leg p m (S K) = m/p + leg p (m/p) K *)
Lemma u5c_leg_shift : forall p m K : nat, 2 <= p ->
  u5c_leg p m (S K) = m / p + u5c_leg p (m / p) K.
Proof.
  intros p m K Hp. induction K as [|K IH].
  - assert (Hl1 : u5c_leg p m 1 = m / p ^ S (S 0) + m / p) by reflexivity.
    assert (Hl2 : u5c_leg p (m / p) 0 = (m / p) / p) by reflexivity.
    rewrite Hl1, Hl2.
    replace (p ^ S (S 0)) with (p * p) by (cbn [Nat.pow]; lia).
    rewrite <- Nat.Div0.div_div. lia.
  - assert (Hl1 : u5c_leg p m (S (S K))
              = m / p ^ S (S (S K)) + u5c_leg p m (S K)) by reflexivity.
    assert (Hl2 : u5c_leg p (m / p) (S K)
              = (m / p) / p ^ S (S K) + u5c_leg p (m / p) K) by reflexivity.
    rewrite Hl1, IH, Hl2.
    replace (p ^ S (S (S K))) with (p * p ^ S (S K))
      by (rewrite Nat.pow_succ_r'; reflexivity).
    rewrite <- Nat.Div0.div_div. lia.
Qed.

(* 余因子：R p m K = fact(m/p^(K+1))·∏_{k≤K} Qp(m/p^k) *)
Fixpoint u5c_R (p m K : nat) : nat :=
  match K with
  | 0 => fact (m / p) * u5c_Qp p m
  | S K' => u5c_R p (m / p) K' * u5c_Qp p m
  end.

(* 余因子分解：fact m = p^(leg p m K)·R p m K *)
Lemma u5c_R_spec : forall p K m : nat, pr_prime p ->
  fact m = p ^ (u5c_leg p m K) * u5c_R p m K.
Proof.
  intros p K. induction K as [|K IH]; intros m Hp.
  - cbn [u5c_leg u5c_R]. rewrite Nat.mul_assoc.
    apply u5c_fact_split. exact Hp.
  - assert (Hp2 : 2 <= p)
      by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; exact Hp2).
    assert (Hl : u5c_leg p m (S K) = m / p + u5c_leg p (m / p) K)
      by (apply u5c_leg_shift; exact Hp2).
    assert (Hr : u5c_R p m (S K) = u5c_R p (m / p) K * u5c_Qp p m)
      by reflexivity.
    rewrite Hl, Hr, (u5c_fact_split p m Hp), (IH (m / p) Hp).
    rewrite Nat.pow_add_r. ring.
Qed.

(* 余因子无隙：m/p^(K+1) = 0 ⟹ p ∤ R p m K *)
Lemma u5c_R_not_dvd : forall p K m : nat, pr_prime p ->
  m / p ^ (S K) = 0 -> pec_dvd p (u5c_R p m K) -> False.
Proof.
  intros p K. induction K as [|K IH]; intros m Hp Hz Hd.
  - assert (Hmp : m / p = 0).
    { replace (p ^ S 0) with p in Hz by (rewrite Nat.pow_1_r; reflexivity).
      exact Hz. }
    cbn [u5c_R] in Hd. rewrite Hmp in Hd. cbn [fact] in Hd.
    apply (u5c_Qp_not_dvd p m Hp).
    destruct Hd as [z Hz2]. cbn [Nat.mul] in Hz2.
    rewrite Nat.add_0_r in Hz2. exists z. exact Hz2.
  - assert (Hz' : (m / p) / p ^ (S K) = 0).
    { replace (p ^ S (S K)) with (p * p ^ S K) in Hz
        by (rewrite Nat.pow_succ_r'; reflexivity).
      rewrite <- Nat.Div0.div_div in Hz. exact Hz. }
    destruct Hd as [z Hz2].
    assert (Hdv : pec_dvd p (u5c_R p (m / p) K * u5c_Qp p m))
      by (exists z; exact Hz2).
    destruct (pec_euclid p (u5c_R p (m / p) K) (u5c_Qp p m) Hp Hdv)
      as [H1 | H2].
    + exfalso. apply (IH (m / p) Hp Hz' H1).
    + exfalso. apply (u5c_Qp_not_dvd p m Hp H2).
Qed.

(* 均摊估计：(2n)/d ≤ 2·(n/d) + 1 *)
Lemma u5c_eps1 : forall d n : nat, (2 * n) / d <= 2 * (n / d) + 1.
Proof.
  intros d n.
  destruct d as [|d'].
  - cbn [Nat.div]. lia.
  - pose proof (Nat.div_mod_eq n (S d')) as H1.
    pose proof (Nat.mod_upper_bound n (S d') ltac:(lia)) as H2.
    assert (H3 : (2 * n) / (S d') < 2 * (n / (S d')) + 2).
    { apply Nat.div_lt_upper_bound; [lia |].
      assert (Hs : 2 * n = S d' * (2 * (n / (S d'))) + 2 * (n mod (S d'))).
      { replace (2 * n)
          with (2 * (S d' * (n / (S d')) + n mod (S d'))) by lia.
        ring. }
      lia. }
    lia.
Qed.

(* 计数器：cnt p b K = #{k ∈ [1,K] : p^k ≤ b} *)
Fixpoint u5c_cnt (p b K : nat) : nat :=
  match K with
  | 0 => if Nat.leb (p ^ S 0) b then 1 else 0
  | S K' => (if Nat.leb (p ^ S (S K')) b then 1 else 0) + u5c_cnt p b K'
  end.

Lemma u5c_cnt_le : forall p b K : nat, u5c_cnt p b K <= S K.
Proof.
  intros p b K. induction K as [|K IH].
  - cbn [u5c_cnt]. destruct (Nat.leb (p ^ S 0) b); lia.
  - cbn [u5c_cnt]. destruct (Nat.leb (p ^ S (S K)) b); lia.
Qed.

(* 计数上界：p^(cnt p b K) ≤ b *)
Lemma u5c_cnt_pow_le : forall p b K : nat, 2 <= p -> 1 <= b ->
  p ^ u5c_cnt p b K <= b.
Proof.
  intros p b K Hp Hb. induction K as [|K IH].
  - cbn [u5c_cnt]. destruct (Nat.leb (p ^ S 0) b) eqn:Eb.
    + apply Nat.leb_le in Eb.
      replace (p ^ S 0) with p in Eb by (rewrite Nat.pow_1_r; reflexivity).
      rewrite Nat.pow_1_r. exact Eb.
    + apply Nat.leb_gt in Eb. rewrite Nat.pow_0_r. exact Hb.
  - cbn [u5c_cnt]. destruct (Nat.leb (p ^ S (S K)) b) eqn:Eb.
    + apply Nat.leb_le in Eb.
      replace (1 + u5c_cnt p b K) with (S (u5c_cnt p b K)) by reflexivity.
      replace (p * p ^ u5c_cnt p b K) with (p ^ S (u5c_cnt p b K))
        by (rewrite Nat.pow_succ_r'; reflexivity).
      apply Nat.le_trans with (p ^ S (S K)).
      * apply Nat.pow_le_mono_r; [lia |].
        pose proof (u5c_cnt_le p b K) as Hcle. lia.
      * exact Eb.
    + apply Nat.leb_gt in Eb. apply IH.
Qed.

(* 指数差定界：leg p (2n) K − 2·leg p n K ≤ cnt p (2n) K *)
Lemma u5c_e_le_cnt : forall p n K : nat, 2 <= p ->
  u5c_leg p (2 * n) K - 2 * u5c_leg p n K <= u5c_cnt p (2 * n) K.
Proof.
  intros p n K Hp. induction K as [|K IH].
  - cbn [u5c_leg u5c_cnt].
    replace (p ^ S 0) with p by (rewrite Nat.pow_1_r; reflexivity).
    destruct (Nat.leb p (2 * n)) eqn:Eb.
    + apply Nat.leb_le in Eb.
      pose proof (u5c_eps1 p n) as He. lia.
    + apply Nat.leb_gt in Eb.
      assert (H1 : (2 * n) / p = 0)
        by (apply (u5c_div_eq_zero p (2 * n)); lia).
      assert (H2 : n / p = 0)
        by (apply (u5c_div_eq_zero p n); lia).
      lia.
  - cbn [u5c_leg u5c_cnt].
    destruct (Nat.leb (p ^ S (S K)) (2 * n)) eqn:Eb.
    + apply Nat.leb_le in Eb.
      pose proof (u5c_eps1 (p ^ S (S K)) n) as He. lia.
    + apply Nat.leb_gt in Eb.
      assert (H1 : (2 * n) / p ^ S (S K) = 0)
        by (apply (u5c_div_eq_zero (p ^ S (S K)) (2 * n));
            [apply Nat.pow_nonzero; lia | lia]).
      assert (H2 : n / p ^ S (S K) = 0)
        by (apply (u5c_div_eq_zero (p ^ S (S K)) n);
            [apply Nat.pow_nonzero; lia | lia]).
      lia.
Qed.

(* 商的双倍单调：2·(n/d) ≤ (2n)/d *)
Lemma u5c_le_div : forall b a c : nat, b <> 0 -> b * c <= a -> c <= a / b.
Proof.
  intros b a c Hb Hle.
  destruct (le_lt_dec c (a / b)) as [H | H]; [exact H |].
  exfalso.
  assert (H1 : b * (a / b) <= b * (c - 1)) by (apply Nat.mul_le_mono_l; lia).
  pose proof (Nat.div_mod_eq a b) as Hdm.
  pose proof (Nat.mod_upper_bound a b Hb) as Hm.
  assert (Hstep : b * (c - 1) + b = b * c).
  { destruct c as [|c']; [lia |].
    replace (S c' - 1) with c' by lia. ring. }
  lia.
Qed.

Lemma u5c_div_double : forall d n : nat, 2 * (n / d) <= (2 * n) / d.
Proof.
  intros d n. destruct d as [|d'].
  - cbn [Nat.div]. lia.
  - pose proof (Nat.div_mod_eq n (S d')) as H1.
    apply (u5c_le_div (S d') (2 * n) (2 * (n / (S d')))); [lia | lia].
Qed.

(* 指数和的折叠和形：leg p m K = Σ_{i≤K} ⌊m/p^(i+1)⌋ *)
Lemma u5c_leg_sum : forall p m K : nat,
  u5c_leg p m K = pec_sum (fun i => m / p ^ S i) (S K).
Proof.
  intros p m K. induction K as [|K IH].
  - cbn [u5c_leg pec_sum].
    replace (p ^ S 0) with p by (rewrite Nat.pow_1_r; reflexivity).
    lia.
  - assert (Hsp : pec_sum (fun i => m / p ^ S i) (S (S K))
                = pec_sum (fun i => m / p ^ S i) (S K)
                + (fun i => m / p ^ S i) (S K)) by reflexivity.
    cbn [u5c_leg]. rewrite Hsp, IH. cbv beta. lia.
Qed.

(* ---- §2d 中项主语句：C(2n,n) 的 p-指数完全提取（sigT Set 面） ----
   2≤p 素、n/p^K = 0 ⟹ 存在 e＝leg p (2n) K − 2·leg p n K：
   C·R1·R1 = p^e·R2 ∧ p^e ∣ C ∧ p^e ≤ 2n ∧ e 取该定义式
   （R1:=u5c_R p n K、R2:=u5c_R p (2n) K，二者 p-无隙） *)
Lemma u5c_mid_master : forall p n K : nat, 2 <= p -> pr_prime p -> 1 <= n ->
  n / p ^ K = 0 ->
  { e : nat & (pec_mid n * u5c_R p n K * u5c_R p n K
               = p ^ e * u5c_R p (2 * n) K)
              /\ pec_dvd (p ^ e) (pec_mid n)
              /\ p ^ e <= 2 * n
              /\ e = u5c_leg p (2 * n) K - 2 * u5c_leg p n K }.
Proof.
  intros p n K Hp2 Hpp Hn1 Hz.
  assert (Hpk : p ^ K <> 0) by (apply Nat.pow_nonzero; lia).
  assert (Hlt : n < p ^ K).
  { pose proof (Nat.div_mod_eq n (p ^ K)) as Hdm.
    pose proof (Nat.mod_upper_bound n (p ^ K) Hpk) as Hub.
    rewrite Hz in Hdm. rewrite Nat.mul_0_r in Hdm.
    rewrite Nat.add_0_l in Hdm. lia. }
  assert (HsK : p ^ S K = p * p ^ K) by (rewrite Nat.pow_succ_r'; reflexivity).
  assert (Hpge : 2 * p ^ K <= p * p ^ K) by (apply Nat.mul_le_mono_r; lia).
  assert (H2n : 2 * n < p ^ S K) by (rewrite HsK; lia).
  assert (HmonoK : p ^ K <= p ^ S K) by (apply Nat.pow_le_mono_r; lia).
  assert (H0n : n / p ^ S K = 0).
  { apply (u5c_div_eq_zero (p ^ S K) n);
      [apply Nat.pow_nonzero; lia | lia]. }
  assert (H02n : 2 * n / p ^ S K = 0).
  { apply (u5c_div_eq_zero (p ^ S K) (2 * n));
      [apply Nat.pow_nonzero; lia | exact H2n]. }
  assert (HnR1 : pec_dvd p (u5c_R p n K) -> False)
    by (apply (u5c_R_not_dvd p K n Hpp H0n)).
  assert (HnR2 : pec_dvd p (u5c_R p (2 * n) K) -> False)
    by (apply (u5c_R_not_dvd p K (2 * n) Hpp H02n)).
  pose proof (u5c_R_spec p K n Hpp) as Hsp1.
  pose proof (u5c_R_spec p K (2 * n) Hpp) as Hsp2.
  pose proof (pec_mid_fact_eq n) as Hmid.
  rewrite Hsp1, Hsp2 in Hmid.
  assert (Hge : 2 * u5c_leg p n K <= u5c_leg p (2 * n) K).
  { rewrite (u5c_leg_sum p n K). rewrite (u5c_leg_sum p (2 * n) K).
    replace (2 * pec_sum (fun i => n / p ^ S i) (S K))
      with (pec_sum (fun i => n / p ^ S i) (S K)
            + pec_sum (fun i => n / p ^ S i) (S K)) by lia.
    rewrite <- (pec_sum_add (S K) (fun i => n / p ^ S i)
                            (fun i => n / p ^ S i)).
    apply pec_sum_le. intros i Hi. cbv beta.
    replace (n / p ^ S i + n / p ^ S i) with (2 * (n / p ^ S i)) by lia.
    apply u5c_div_double. }
  assert (Heq : p ^ (2 * u5c_leg p n K) * (pec_mid n * u5c_R p n K * u5c_R p n K)
              = p ^ (u5c_leg p (2 * n) K) * u5c_R p (2 * n) K).
  { assert (Hpow2 : p ^ (2 * u5c_leg p n K)
                  = p ^ (u5c_leg p n K) * p ^ (u5c_leg p n K))
      by (replace (2 * u5c_leg p n K)
            with (u5c_leg p n K + u5c_leg p n K) by lia;
          apply Nat.pow_add_r).
    assert (Hrearr : p ^ (u5c_leg p n K) * p ^ (u5c_leg p n K)
                     * (pec_mid n * u5c_R p n K * u5c_R p n K)
                   = pec_mid n * (p ^ (u5c_leg p n K) * u5c_R p n K)
                     * (p ^ (u5c_leg p n K) * u5c_R p n K)) by ring.
    rewrite Hpow2, Hrearr. exact Hmid. }
  assert (HL2 : u5c_leg p (2 * n) K
              = 2 * u5c_leg p n K
                + (u5c_leg p (2 * n) K - 2 * u5c_leg p n K)) by lia.
  rewrite HL2, Nat.pow_add_r in Heq.
  rewrite (u5c_mul_assoc_l (p ^ (2 * u5c_leg p n K))
             (p ^ (u5c_leg p (2 * n) K - 2 * u5c_leg p n K))
             (u5c_R p (2 * n) K)) in Heq.
  assert (Hcancel : p ^ (2 * u5c_leg p n K) <> 0)
    by (apply Nat.pow_nonzero; lia).
  assert (Hcore : pec_mid n * u5c_R p n K * u5c_R p n K
                = p ^ (u5c_leg p (2 * n) K - 2 * u5c_leg p n K)
                  * u5c_R p (2 * n) K).
  { exact (proj1 (Nat.mul_cancel_l _ _ _ Hcancel) Heq). }
  assert (Hdvd : pec_dvd (p ^ (u5c_leg p (2 * n) K - 2 * u5c_leg p n K))
                   (pec_mid n)).
  { apply (u5c_coprime_cancel (u5c_R p n K * u5c_R p n K)
             (p ^ (u5c_leg p (2 * n) K - 2 * u5c_leg p n K)) (pec_mid n)).
    - apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia.
    - apply (pec_dvd_of_eq _ _ (u5c_R p (2 * n) K)).
      rewrite <- Hcore. ring.
    - intros d Hd Hdpe HdRR.
      apply HnR1.
      rewrite (u5c_dvd_pow_eq p
                 (u5c_leg p (2 * n) K - 2 * u5c_leg p n K) d
                 Hp2 Hpp Hd Hdpe) in HdRR.
      destruct (pec_euclid p (u5c_R p n K) (u5c_R p n K) Hpp HdRR)
        as [H1 | H2].
      + exact H1.
      + exact H2. }
  assert (Hle : p ^ (u5c_leg p (2 * n) K - 2 * u5c_leg p n K) <= 2 * n).
  { apply Nat.le_trans with (p ^ u5c_cnt p (2 * n) K).
    - apply Nat.pow_le_mono_r.
      + apply (proj2 (Nat.neq_0_lt_0 p)).
        apply (Nat.lt_le_trans 0 1 p); [apply Nat.lt_0_1 |].
        apply (Nat.le_trans 1 2 p); [apply Nat.le_succ_diag_r | exact Hp2].
      + apply (u5c_e_le_cnt p n K Hp2).
    - exact (u5c_cnt_pow_le p (2 * n) K Hp2
               (Nat.le_trans 1 (2 * 1) (2 * n)
                  (Nat.le_succ_diag_r 1)
                  (Nat.mul_le_mono_l 1 n 2 Hn1))). }
  exists (u5c_leg p (2 * n) K - 2 * u5c_leg p n K).
  split; [exact Hcore | split; [exact Hdvd | split; [exact Hle | reflexivity]]].
Defined.

(* 中项 p-无隙：2n/3 < p ≤ n 且 p² > 2n ⟹ p ∤ C(2n,n) *)
Lemma u5c_mid_no_dvd : forall p n : nat, 2 <= p -> pr_prime p -> p <= n ->
  2 * n < 3 * p -> 2 * n < p * p ->
  pec_dvd p (pec_mid n) -> False.
Proof.
  intros p n Hp2 Hpp Hpn H3 Hsq Hd.
  assert (Hsq2 : p ^ 2 = p * p) by (cbn [Nat.pow]; ring).
  assert (Hp3v : p ^ S 2 = p * p * p)
    by (rewrite Nat.pow_succ_r'; rewrite Hsq2; ring).
  assert (Hp1 : 1 <= p).
  { apply (Nat.le_trans 1 2 p); [apply Nat.le_succ_diag_r | exact Hp2]. }
  assert (Hppos : 0 < p) by (apply (Nat.lt_le_trans 0 1 p); [apply Nat.lt_0_1 | exact Hp1]).
  assert (Hpne0 : p <> 0) by (exact (proj2 (Nat.neq_0_lt_0 p) Hppos)).
  assert (Hppos2 : 0 < p * p) by (apply (Nat.mul_pos_pos p p Hppos Hppos)).
  assert (Hpp0 : p * p <> 0) by (exact (proj2 (Nat.neq_0_lt_0 (p * p)) Hppos2)).
  assert (Hppos3 : 0 < p * p * p).
  { replace (p * p * p) with (p * (p * p))
      by (rewrite u5c_mul_assoc_l; reflexivity).
    exact (Nat.mul_pos_pos p (p * p) Hppos Hppos2). }
  assert (Hppp0 : p * p * p <> 0)
    by (exact (proj2 (Nat.neq_0_lt_0 (p * p * p)) Hppos3)).
  assert (Hpp1 : p * p <= p * p * p).
  { assert (Hpple : p <= p * p).
    { assert (Hx : p * 1 <= p * p) by (apply Nat.mul_le_mono_l; exact Hp1).
      rewrite Nat.mul_1_r in Hx. exact Hx. }
    replace (p * p * p) with (p * (p * p))
      by (rewrite u5c_mul_assoc_l; reflexivity).
    apply (Nat.mul_le_mono_l p (p * p) p Hpple). }
  assert (Hn1 : 1 <= n).
  { apply (Nat.le_trans 1 p n).
    - apply (Nat.le_trans 1 2 p); [apply Nat.le_succ_diag_r | exact Hp2].
    - exact Hpn. }
  assert (Hnle : n <= 2 * n).
  { replace (2 * n) with (n + n) by ring. apply Nat.le_add_r. }
  assert (Hnlt : n < 2 * n).
  { apply (Nat.lt_le_trans n (S n) (2 * n)).
    - apply Nat.lt_succ_diag_r.
    - replace (S n) with (1 + n) by reflexivity.
      replace (2 * n) with (n + n) by ring.
      apply (Nat.add_le_mono 1 n n n); [exact Hn1 | apply Nat.le_refl]. }
  assert (Hz : n / p ^ 2 = 0).
  { apply (u5c_div_eq_zero (p ^ 2) n);
      [apply Nat.pow_nonzero; exact Hpne0
       | rewrite Hsq2; exact (Nat.lt_le_trans n (2 * n) (p * p) Hnlt (Nat.lt_le_incl (2 * n) (p * p) Hsq))]. }
  destruct (u5c_mid_master p n 2 Hp2 Hpp Hn1 Hz) as [e [Heq [Hdvd [Hle He4]]]].
  assert (Hv2 : (2 * n) / p = 2) by (apply (u5c_div_eq p (2 * n) 2); lia).
  assert (Hv1 : n / p = 1) by (apply (u5c_div_eq p n 1); lia).
  assert (Hq0a : (2 * n) / (p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p) (2 * n)); [exact Hpp0 | exact Hsq]).
  assert (Hq0b : n / (p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p) n);
        [exact Hpp0 | exact (Nat.lt_le_trans n (2 * n) (p * p) Hnlt (Nat.lt_le_incl (2 * n) (p * p) Hsq))]).
  assert (Hq0c : (2 * n) / (p * p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p * p) (2 * n));
        [exact Hppp0 | exact (Nat.lt_le_trans (2 * n) (p * p) (p * p * p)
                                 Hsq Hpp1)]).
  assert (Hq0d : n / (p * p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p * p) n);
        [exact Hppp0 | exact (Nat.lt_le_trans n (2 * n) (p * p * p) Hnlt
         (Nat.le_trans (2 * n) (p * p) (p * p * p)
            (Nat.lt_le_incl (2 * n) (p * p) Hsq) Hpp1))]).
  cbn [u5c_leg] in He4.
  replace (p ^ S (S 1)) with (p * p * p) in He4 by (cbn [Nat.pow]; ring).
  replace (p ^ S (S 0)) with (p * p) in He4 by (cbn [Nat.pow]; ring).
  rewrite Hq0c, Hq0a, Hv2, Hq0d, Hq0b, Hv1 in He4.
  assert (He0 : e = 0) by lia.
  rewrite He0, Nat.pow_0_r, Nat.mul_1_l in Heq.
  apply (u5c_R_not_dvd p 2 (2 * n) Hpp).
  - rewrite Hp3v. exact Hq0c.
  - assert (HdC : pec_dvd p ((u5c_R p n 2 * u5c_R p n 2) * pec_mid n))
      by (apply (pec_dvd_mul_r p (pec_mid n)
                   (u5c_R p n 2 * u5c_R p n 2) Hd)).
    assert (Hrw : (u5c_R p n 2 * u5c_R p n 2) * pec_mid n
                = pec_mid n * u5c_R p n 2 * u5c_R p n 2) by ring.
    rewrite Hrw, Heq in HdC. exact HdC.
Qed.

(* 中项素平方无隙：p² > 2n 且 p ≤ 2n ⟹ p² ∤ C(2n,n) *)
Lemma u5c_mid_not_sq : forall p n : nat, 2 <= p -> pr_prime p -> p <= 2 * n ->
  2 * n < p * p ->
  pec_dvd (p * p) (pec_mid n) -> False.
Proof.
  intros p n Hp2 Hpp Hp2n Hsq Hd.
  assert (Hsq2 : p ^ 2 = p * p) by (cbn [Nat.pow]; ring).
  assert (Hp3v : p ^ S 2 = p * p * p)
    by (rewrite Nat.pow_succ_r'; rewrite Hsq2; ring).
  assert (Hp1 : 1 <= p).
  { apply (Nat.le_trans 1 2 p); [apply Nat.le_succ_diag_r | exact Hp2]. }
  assert (Hppos : 0 < p) by (apply (Nat.lt_le_trans 0 1 p); [apply Nat.lt_0_1 | exact Hp1]).
  assert (Hpne0 : p <> 0) by (exact (proj2 (Nat.neq_0_lt_0 p) Hppos)).
  assert (Hppos2 : 0 < p * p) by (apply (Nat.mul_pos_pos p p Hppos Hppos)).
  assert (Hpp0 : p * p <> 0) by (exact (proj2 (Nat.neq_0_lt_0 (p * p)) Hppos2)).
  assert (Hppos3 : 0 < p * p * p).
  { replace (p * p * p) with (p * (p * p))
      by (rewrite u5c_mul_assoc_l; reflexivity).
    exact (Nat.mul_pos_pos p (p * p) Hppos Hppos2). }
  assert (Hppp0 : p * p * p <> 0)
    by (exact (proj2 (Nat.neq_0_lt_0 (p * p * p)) Hppos3)).
  assert (Hpp1 : p * p <= p * p * p).
  { assert (Hpple : p <= p * p).
    { assert (Hx : p * 1 <= p * p) by (apply Nat.mul_le_mono_l; exact Hp1).
      rewrite Nat.mul_1_r in Hx. exact Hx. }
    replace (p * p * p) with (p * (p * p))
      by (rewrite u5c_mul_assoc_l; reflexivity).
    apply (Nat.mul_le_mono_l p (p * p) p Hpple). }
  assert (Hn1 : 1 <= n).
  { destruct n as [|n'].
    - exfalso. apply Nat.le_0_r in Hp2n.
      rewrite Hp2n in Hp2.
      replace 2 with (S 1) in Hp2 by reflexivity.
      exact (Nat.nle_succ_0 1 Hp2).
    - exact (le_n_S 0 n' (Nat.le_0_l n')). }
  assert (Hnle : n <= 2 * n).
  { replace (2 * n) with (n + n) by ring. apply Nat.le_add_r. }
  assert (Hnlt : n < 2 * n).
  { apply (Nat.lt_le_trans n (S n) (2 * n)).
    - apply Nat.lt_succ_diag_r.
    - replace (S n) with (1 + n) by reflexivity.
      replace (2 * n) with (n + n) by ring.
      apply (Nat.add_le_mono 1 n n n); [exact Hn1 | apply Nat.le_refl]. }
  assert (Hz : n / p ^ 2 = 0).
  { apply (u5c_div_eq_zero (p ^ 2) n);
      [apply Nat.pow_nonzero; exact Hpne0
       | rewrite Hsq2; exact (Nat.lt_le_trans n (2 * n) (p * p) Hnlt (Nat.lt_le_incl (2 * n) (p * p) Hsq))]. }
  destruct (u5c_mid_master p n 2 Hp2 Hpp Hn1 Hz) as [e [Heq [Hdvd [Hle He4]]]].
  assert (Hq0a : (2 * n) / (p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p) (2 * n)); [exact Hpp0 | exact Hsq]).
  assert (Hq0b : n / (p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p) n);
        [exact Hpp0 | exact (Nat.lt_le_trans n (2 * n) (p * p) Hnlt (Nat.lt_le_incl (2 * n) (p * p) Hsq))]).
  assert (Hq0c : (2 * n) / (p * p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p * p) (2 * n));
        [exact Hppp0 | exact (Nat.lt_le_trans (2 * n) (p * p) (p * p * p)
                                 Hsq Hpp1)]).
  assert (Hq0d : n / (p * p * p) = 0)
    by (apply (u5c_div_eq_zero (p * p * p) n);
        [exact Hppp0 | exact (Nat.lt_le_trans n (2 * n) (p * p * p) Hnlt
         (Nat.le_trans (2 * n) (p * p) (p * p * p)
            (Nat.lt_le_incl (2 * n) (p * p) Hsq) Hpp1))]).
  cbn [u5c_leg] in He4.
  replace (p ^ S (S 1)) with (p * p * p) in He4 by (cbn [Nat.pow]; ring).
  replace (p ^ S (S 0)) with (p * p) in He4 by (cbn [Nat.pow]; ring).
  rewrite Hq0c, Hq0a, Hq0d, Hq0b in He4.
  pose proof (u5c_eps1 p n) as Heps.
  assert (Hele1 : e <= 1) by lia.
  destruct (Nat.eq_dec e 0) as [He0 | He1].
  - rewrite He0, Nat.pow_0_r, Nat.mul_1_l in Heq.
    apply (u5c_R_not_dvd p 2 (2 * n) Hpp).
    + rewrite Hp3v. exact Hq0c.
    + assert (HdC : pec_dvd (p * p)
                      ((u5c_R p n 2 * u5c_R p n 2) * pec_mid n))
        by (apply (pec_dvd_mul_r (p * p) (pec_mid n)
                     (u5c_R p n 2 * u5c_R p n 2) Hd)).
      assert (Hrw : (u5c_R p n 2 * u5c_R p n 2) * pec_mid n
                  = pec_mid n * u5c_R p n 2 * u5c_R p n 2) by ring.
      rewrite Hrw in HdC.
      destruct HdC as [z Hz2].
      exists (p * z). rewrite <- Heq, Hz2, Nat.mul_assoc. reflexivity.
  - assert (Hev : e = 1) by lia.
    rewrite Hev, Nat.pow_1_r in Heq.
    apply (u5c_R_not_dvd p 2 (2 * n) Hpp).
    + rewrite Hp3v. exact Hq0c.
    + assert (HdC : pec_dvd (p * p)
                      ((u5c_R p n 2 * u5c_R p n 2) * pec_mid n))
        by (apply (pec_dvd_mul_r (p * p) (pec_mid n)
                     (u5c_R p n 2 * u5c_R p n 2) Hd)).
      assert (Hrw : (u5c_R p n 2 * u5c_R p n 2) * pec_mid n
                  = pec_mid n * u5c_R p n 2 * u5c_R p n 2) by ring.
      rewrite Hrw, Heq in HdC.
      destruct HdC as [z Hz2].
      assert (Hcancel : u5c_R p (2 * n) 2 = p * z).
      { apply (proj1 (Nat.mul_cancel_l (u5c_R p (2 * n) 2) (p * z) p
                   ltac:(exact Hpne0))).
        rewrite Nat.mul_assoc. exact Hz2. }
      exists z. exact Hcancel.
Qed.

(* ---- §3 锐化上界的即时推论：θ 常数减半的 nat 面 ---- *)

Theorem u5c_primorial_sharp : forall N : nat, 1 <= N -> pec_prim N <= 4 ^ N.
Proof.
  intros N HN. exact (u5c_prim_le_pow4 N HN).
Qed.

(* ---- §4 数值烟测（小实例，vm_compute） ---- *)

Lemma u5c_smoke_prim10 : pec_prim 10 = 210.
Proof. vm_compute. reflexivity. Qed.

Lemma u5c_smoke_pow4_10 : (Nat.leb (pec_prim 10) (4 ^ 10))%bool = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值纪律：pec_prim 40 一元表示约 7.4e12 节点不可 vm_compute，
   烟测改 12 以内小实例 *)
Lemma u5c_smoke_prim12 : pec_prim 12 = 2310.
Proof. vm_compute. reflexivity. Qed.

(* ---- §5 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions u5c_prim_even.
Print Assumptions u5c_div_eq.
Print Assumptions u5c_sum_two.
Print Assumptions u5c_binom_odd_le.
Print Assumptions u5c_winprod_dvd_gen.
Print Assumptions u5c_odd_prime_dvd.
Print Assumptions u5c_prim_le_pow4.
Print Assumptions u5c_win_in_ex.
Print Assumptions u5c_dvd_fold_in.
Print Assumptions u5c_prime_dvd_prim.
Print Assumptions u5c_primorial_sharp.
Print Assumptions u5c_dvd_pow_eq.
Print Assumptions u5c_coprime_cancel.
Print Assumptions u5c_combine_pow.
Print Assumptions u5c_fold_dvd.
Print Assumptions u5c_Qp_not_dvd.
Print Assumptions u5c_fact_split.
Print Assumptions u5c_leg_shift.
Print Assumptions u5c_R_spec.
Print Assumptions u5c_R_not_dvd.
Print Assumptions u5c_eps1.
Print Assumptions u5c_cnt_pow_le.
Print Assumptions u5c_e_le_cnt.
Print Assumptions u5c_leg_sum.
Print Assumptions u5c_le_div.
Print Assumptions u5c_div_double.
Print Assumptions u5c_mid_master.
Print Assumptions u5c_mid_no_dvd.
Print Assumptions u5c_mid_not_sq.

(* ============================================================ *)
(* §7 数值主链：2^t ≥ t²、Bernoulli 型块估计、平方根见证、        *)
(*    基例段 m ≥ 16 与主链 n ≥ 512                               *)
(*                                                              *)
(*    技术注记：上下文含变元幂（Nat.pow）假设时 lia 全域失灵，    *)
(*    故凡 lia 可及的线性义务一律外提为幂-free 独立引理，         *)
(*    主体证明内只保留项级推理（ring / rewrite / le_trans 链）。  *)
(* ============================================================ *)

(* ---- 线性助手件（幂-free，可安全 lia） ---- *)

Lemma u5c_lin_2t1 : forall t : nat, 4 <= t -> 2 * t + 1 <= t * t.
Proof.
  intros t Ht.
  assert (H3 : 3 * t <= t * t) by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

Lemma u5c_lin_step : forall t : nat, 2 * t + 1 <= t * t ->
  S t * S t <= 2 * (t * t).
Proof.
  intros t H1.
  replace (S t * S t) with (t * t + (2 * t + 1)) by ring.
  replace (2 * (t * t)) with (t * t + t * t) by ring.
  lia.
Qed.

Lemma u5c_le_4_512 : 4 <= 512.
Proof.
  apply (proj1 (Nat.succ_le_mono 3 511)).
  apply (proj1 (Nat.succ_le_mono 2 510)).
  apply (proj1 (Nat.succ_le_mono 1 509)).
  apply (proj1 (Nat.succ_le_mono 0 508)).
  apply Nat.le_0_l.
Qed.

Lemma u5c_lt_half : forall a b : nat, a + a < b -> a < b.
Proof. intros a b H. lia. Qed.

Lemma u5c_sub4_lt : forall n : nat, 4 <= n -> n - 4 < n.
Proof. intros n H. lia. Qed.

Lemma u5c_div_step3_aux : forall a b c m1 m2 n : nat,
  a = 3 * b + m1 -> m1 < 3 -> n = 3 * c + m2 -> m2 < 3 -> a + 4 = n ->
  b + 1 <= c.
Proof. intros a b c m1 m2 n H1 H2 H3 H4 H5. lia. Qed.

Lemma u5c_div_step3 : forall n : nat, 512 <= n ->
  (n - 4) / 3 + 1 <= n / 3.
Proof.
  intros n Hn.
  pose proof (Nat.div_mod_eq (n - 4) 3) as H1.
  pose proof (Nat.div_mod_eq n 3) as H2.
  pose proof (Nat.mod_upper_bound (n - 4) 3 ltac:(lia)) as H3.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as H4.
  apply (u5c_div_step3_aux (n - 4) ((n - 4) / 3) (n / 3)
           ((n - 4) mod 3) (n mod 3) n H1 H3 H2 H4).
  apply (Nat.sub_add 4 n).
  apply (Nat.le_trans 4 512 n).
  - apply (proj1 (Nat.succ_le_mono 3 511)).
    apply (proj1 (Nat.succ_le_mono 2 510)).
    apply (proj1 (Nat.succ_le_mono 1 509)).
    apply (proj1 (Nat.succ_le_mono 0 508)).
    apply Nat.le_0_l.
  - exact Hn.
Qed.

Lemma u5c_third_sum_aux : forall b c m1 m2 a : nat,
  a = 3 * b + m1 -> m1 < 3 -> 2 * a = 3 * c + m2 -> m2 < 3 ->
  b + c <= a.
Proof. intros b c m1 m2 a H1 H2 H3 H4. lia. Qed.

Lemma u5c_third_sum : forall n : nat, n / 3 + (2 * n) / 3 <= n.
Proof.
  intro n.
  pose proof (Nat.div_mod_eq n 3) as H1.
  pose proof (Nat.div_mod_eq (2 * n) 3) as H2.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as H3.
  pose proof (Nat.mod_upper_bound (2 * n) 3 ltac:(lia)) as H4.
  exact (u5c_third_sum_aux (n / 3) ((2 * n) / 3) (n mod 3) ((2 * n) mod 3)
           n H1 H3 H2 H4).
Qed.

Lemma u5c_gt_div3_aux : forall q m n r : nat,
  2 * n = 3 * q + m -> m < 3 -> q < r -> 2 * n < 3 * r.
Proof. intros q m n r H1 H2 H3. lia. Qed.

Lemma u5c_gt_div3 : forall n r : nat, (2 * n) / 3 < r -> 2 * n < 3 * r.
Proof.
  intros n r H.
  pose proof (Nat.div_mod_eq (2 * n) 3) as H1.
  pose proof (Nat.mod_upper_bound (2 * n) 3 ltac:(lia)) as H2.
  exact (u5c_gt_div3_aux ((2 * n) / 3) ((2 * n) mod 3) n r H1 H2 H).
Qed.

Lemma u5c_gt_sqrt : forall n s r : nat,
  2 * n < (S s) * (S s) -> s < r -> 2 * n < r * r.
Proof.
  intros n s r H1 H2.
  assert (H3 : (S s) * (S s) <= r * r) by (apply Nat.mul_le_mono; lia).
  lia.
Qed.

Lemma u5c_dvd_le : forall C X : nat, 1 <= X -> pec_dvd C X -> C <= X.
Proof.
  intros C X HX [z Hz].
  assert (Hz1 : 1 <= z).
  { destruct z as [|z'].
    - rewrite Nat.mul_0_r in Hz. lia.
    - lia. }
  rewrite Hz.
  apply Nat.le_trans with (C * 1).
  - rewrite Nat.mul_1_r. apply Nat.le_refl.
  - apply Nat.mul_le_mono_l. exact Hz1.
Qed.

Lemma u5c_dvd_trans : forall a b c : nat,
  pec_dvd a b -> pec_dvd b c -> pec_dvd a c.
Proof.
  intros a b c [z1 Hz1] [z2 Hz2]. exists (z1 * z2).
  rewrite Hz2, Hz1. ring.
Qed.

Lemma u5c_pow_ge1 : forall x e : nat, 1 <= x -> 1 <= x ^ e.
Proof.
  intros x e H. induction e as [|e IH].
  - rewrite Nat.pow_0_r. apply Nat.le_refl.
  - rewrite Nat.pow_succ_r'.
    assert (Hm : x * 1 <= x * x ^ e) by (apply Nat.mul_le_mono_l; exact IH).
    rewrite Nat.mul_1_r in Hm. apply Nat.le_trans with x; [exact H | exact Hm].
Qed.

Lemma u5c_prim_ge1 : forall N : nat, 1 <= pec_prim N.
Proof.
  intro N. unfold pec_prim. apply pec_prod_ge1.
  intros y Hy. destruct (pec_win_in 1 (N - 1) y Hy) as [Hy1 _].
  unfold pr_prime in Hy1. destruct Hy1 as [H _].
  apply (Nat.le_trans 1 2 y); [apply Nat.le_succ_diag_r | exact H].
Qed.

Lemma u5c_fact_pos : forall n : nat, 0 < fact n.
Proof.
  induction n as [|n IH].
  - cbn [fact]. lia.
  - cbn [fact]. lia.
Qed.

(* 2^t ≥ t²（t ≥ 4）：t ≥ 4 走归纳，S t = 4 单点直算 *)
Lemma u5c_pow2_ge_sq : forall t : nat, 4 <= t -> t * t <= 2 ^ t.
Proof.
  intros t Ht. induction t as [|t IH].
  - cbn [Nat.pow]. lia.
  - destruct (le_lt_dec 4 t) as [H4 | H3].
    + replace (2 ^ S t) with (2 * 2 ^ t)
        by (rewrite Nat.pow_succ_r'; reflexivity).
      apply Nat.le_trans with (2 * (t * t)).
      * apply u5c_lin_step. apply u5c_lin_2t1. exact H4.
      * apply Nat.mul_le_mono_l. apply IH. exact H4.
    + clear IH.
      assert (H1 : S t = 4) by lia.
      rewrite H1. cbn [Nat.pow]. lia.
Qed.

(* Bernoulli 型块估计：1 ≤ a、8E < a ⟹ (a+8)^E·(a−8E) ≤ a^(E+1)
   （归纳 E；步内关键线性事实外提） *)
Lemma u5c_bern8_fact : forall a E : nat, 8 * S E < a ->
  8 * S E <= a /\ 8 * E < a.
Proof. intros a E H. split; lia. Qed.

Lemma u5c_bern8_key : forall a E : nat, 1 <= a -> 8 * S E <= a ->
  (a + 8) * (a - 8 * S E) <= a * (a - 8 * E).
Proof.
  intros a E Ha H8.
  assert (Hd : a - 8 * E = a - 8 * S E + 8) by lia.
  assert (Hle : a - 8 * S E <= a) by lia.
  assert (Hs : (a + 8) * (a - 8 * S E)
             = a * (a - 8 * S E) + 8 * (a - 8 * S E)) by ring.
  assert (Ht : a * (a - 8 * E) = a * (a - 8 * S E) + 8 * a)
    by (rewrite Hd; ring).
  apply Nat.le_trans with (a * (a - 8 * S E) + 8 * a).
  - rewrite Hs. apply Nat.add_le_mono.
    + apply Nat.le_refl.
    + apply Nat.mul_le_mono_l. exact Hle.
  - lia.
Qed.

Lemma u5c_bern8 : forall a E : nat, 1 <= a -> 8 * E < a ->
  (a + 8) ^ E * (a - 8 * E) <= a ^ (E + 1).
Proof.
  intros a E Ha H8. induction E as [|E IH].
  - rewrite Nat.pow_0_r, Nat.mul_1_l, Nat.mul_0_r, Nat.sub_0_r.
    replace (0 + 1) with 1 by reflexivity.
    rewrite Nat.pow_1_r. apply Nat.le_refl.
  - destruct (u5c_bern8_fact a E H8) as [H8le H8prev].
    assert (Hkey := u5c_bern8_key a E Ha H8le).
    replace ((a + 8) ^ S E) with ((a + 8) * (a + 8) ^ E)
      by (rewrite Nat.pow_succ_r'; reflexivity).
    replace (S E + 1) with (S (E + 1)) by reflexivity.
    rewrite Nat.pow_succ_r'.
    replace ((a + 8) * (a + 8) ^ E * (a - 8 * S E))
      with ((a + 8) ^ E * ((a + 8) * (a - 8 * S E))) by ring.
    apply Nat.le_trans with ((a + 8) ^ E * (a * (a - 8 * E))).
    + apply Nat.mul_le_mono_l. exact Hkey.
    + replace ((a + 8) ^ E * (a * (a - 8 * E)))
        with (a * ((a + 8) ^ E * (a - 8 * E))) by ring.
      apply Nat.mul_le_mono_l. apply IH. exact H8prev.
Qed.

(* 块内步进：3 ≤ a、32E ≤ a ⟹ (a+9)(a+8)^E ≤ 4(a+1)·a^E *)
Lemma u5c_step4_pos : forall a E : nat, 3 <= a -> 32 * E <= a ->
  1 <= a /\ 8 * E < a /\ 0 < a - 8 * E /\ 3 * a <= 4 * (a - 8 * E).
Proof.
  intros a E Ha H. repeat split; lia.
Qed.

Lemma u5c_step4_mid : forall a E : nat, 3 <= a -> 32 * E <= a ->
  (a + 9) * a <= (a + 1) * (4 * (a - 8 * E)).
Proof.
  intros a E Ha H32.
  assert (H3a : 3 * a <= 4 * (a - 8 * E)) by lia.
  assert (H9 : a + 9 <= 3 * a + 3) by lia.
  apply Nat.le_trans with ((3 * a + 3) * a).
  - apply Nat.mul_le_mono_r. exact H9.
  - replace ((3 * a + 3) * a) with ((a + 1) * (3 * a)) by ring.
    apply Nat.mul_le_mono_l. exact H3a.
Qed.

Lemma u5c_step4 : forall a E : nat, 3 <= a -> 32 * E <= a ->
  4 * (a + 1) * a ^ E >= (a + 9) * (a + 8) ^ E.
Proof.
  intros a E Ha H32.
  destruct (u5c_step4_pos a E Ha H32) as [H1a [H8 [Hdpos H3a]]].
  assert (Hbern := u5c_bern8 a E H1a H8).
  replace (a ^ (E + 1)) with (a * a ^ E) in Hbern
    by (replace (E + 1) with (S E) by (symmetry; apply Nat.add_1_r);
        rewrite Nat.pow_succ_r'; reflexivity).
  assert (Hmid := u5c_step4_mid a E Ha H32).
  assert (Hb1 : (a + 9) * ((a + 8) ^ E * (a - 8 * E))
              <= (a + 9) * (a * a ^ E))
    by (apply Nat.mul_le_mono_l; exact Hbern).
  assert (Hb2 : (a + 9) * (a * a ^ E)
              <= (a + 1) * (4 * (a - 8 * E)) * a ^ E).
  { replace ((a + 9) * (a * a ^ E)) with (((a + 9) * a) * a ^ E) by ring.
    replace ((a + 1) * (4 * (a - 8 * E)) * a ^ E)
      with (((a + 1) * (4 * (a - 8 * E))) * a ^ E) by ring.
    apply Nat.mul_le_mono_r. exact Hmid. }
  apply (proj2 (Nat.mul_le_mono_pos_l ((a + 9) * (a + 8) ^ E)
                  (4 * (a + 1) * a ^ E) (a - 8 * E) Hdpos)).
  replace ((a - 8 * E) * ((a + 9) * (a + 8) ^ E))
    with (((a + 9) * (a + 8) ^ E) * (a - 8 * E)) by ring.
  replace ((a - 8 * E) * (4 * (a + 1) * a ^ E))
    with ((4 * (a + 1) * a ^ E) * (a - 8 * E)) by ring.
  apply Nat.le_trans with ((a + 1) * (4 * (a - 8 * E)) * a ^ E).
  + replace ((a + 9) * ((a + 8) ^ E * (a - 8 * E)))
      with (((a + 9) * (a + 8) ^ E) * (a - 8 * E)) in Hb1 by ring.
    replace ((a + 9) * (a * a ^ E))
      with (((a + 9) * a) * a ^ E) in Hb1 by ring.
    replace ((a + 9) * (a * a ^ E))
      with (((a + 9) * a) * a ^ E) in Hb2 by ring.
    replace ((a + 1) * (4 * (a - 8 * E)) * a ^ E)
      with (((a + 1) * (4 * (a - 8 * E))) * a ^ E) by ring.
    apply Nat.le_trans with (((a + 9) * a) * a ^ E).
    * exact Hb1.
    * exact Hb2.
  + replace ((a + 1) * (4 * (a - 8 * E)) * a ^ E)
      with ((4 * (a + 1) * a ^ E) * (a - 8 * E)) by ring.
    apply Nat.le_refl.
Qed.

(* 平方根 sigT 见证 *)
Lemma u5c_sqrt_ex : forall x : nat, { s : nat & s * s <= x /\ x < (S s) * (S s) }.
Proof.
  induction x as [|x IH].
  - exists 0. split; lia.
  - destruct IH as [s [Hlo Hhi]].
    destruct (le_lt_dec (S s * S s) (S x)) as [Hcase | Hcase].
    + exists (S s). split.
      * exact Hcase.
      * assert (Hle : S s * S s + 1 <= S (S s) * S (S s)).
        { assert (Hm : S s * S s <= S s * S s + (S s + S s)) by lia. lia. }
        lia.
    + exists s. split; lia.
Qed.

(* 基例辅助件 Q：625·m^6 ≤ 4^(3m+1)（m ≥ 16；2-幂改写） *)
Lemma u5c_le_34_98 : 34 <= 98.
Proof. lia. Qed.

Lemma u5c_pos_ne0 : forall x : nat, 1 <= x -> x <> 0.
Proof. intros x H. lia. Qed.

Lemma u5c_le_mul_id : forall a b : nat, 1 <= b -> a <= a * b.
Proof.
  intros a b H.
  apply Nat.le_trans with (a * 1).
  - rewrite Nat.mul_1_r. apply Nat.le_refl.
  - apply Nat.mul_le_mono_l. exact H.
Qed.

Lemma u5c_lt_mul_id : forall a b : nat, 0 < a -> 1 < b -> a < a * b.
Proof.
  intros a b Ha H.
  destruct a as [|p].
  - exfalso. apply (Nat.lt_irrefl 0). exact Ha.
  - destruct b as [|b'].
    + exfalso. lia.
    + destruct b' as [|k].
      * exfalso. lia.
      * rewrite Nat.mul_succ_r. rewrite Nat.mul_succ_r.
        apply Nat.lt_le_trans with (S p + S p).
        -- apply (Nat.lt_le_trans (S p) (S (S p)) (S p + S p)).
           ++ apply Nat.lt_succ_diag_r.
           ++ lia.
        -- lia.
Qed.

Lemma u5c_k7_pos : forall m : nat, 0 < 4 * (m * m) + 7.
Proof. intro m. lia. Qed.

Lemma u5c_sq_mul : forall m : nat, m ^ 2 = m * m.
Proof.
  intro m. rewrite Nat.pow_succ_r'.
  rewrite Nat.pow_1_r. reflexivity.
Qed.

Lemma u5c_base_q_shift : forall d : nat,
  3 * (16 + S d) + 1 = 3 * (16 + d) + 1 + 3.
Proof. intro d. lia. Qed.

Lemma u5c_3le_shift : forall d : nat, 3 <= 3 * (16 + d) + 1.
Proof. intro d. lia. Qed.

Lemma u5c_base_q_scale : forall A B C : nat, A * B <= C -> A * (64 * B) <= C * 64.
Proof.
  intros A B C H.
  rewrite (Nat.mul_assoc A 64 B).
  rewrite (Nat.mul_comm A 64).
  rewrite <- (Nat.mul_assoc 64 A B).
  rewrite (Nat.mul_comm C 64).
  apply Nat.mul_le_mono_l. exact H.
Qed.

Lemma u5c_base_q_base : 625 * 16 ^ 6 <= 4 ^ 49.
Proof.
  assert (H625 : 625 <= 2 ^ 10) by (change (625 <= 1024); lia).
  assert (H16 : 16 = 2 ^ 4) by reflexivity.
  assert (H6 : 16 ^ 6 = 2 ^ 24).
  { rewrite H16 at 1. replace 24 with (4 * 6) by reflexivity.
    symmetry. apply Nat.pow_mul_r. }
  rewrite H6. replace (3 * 16 + 1) with 49 by reflexivity.
  assert (Hr : 4 ^ 49 = 2 ^ 98) by (rewrite hl_pow4; reflexivity).
  rewrite Hr.
  apply Nat.le_trans with (2 ^ 10 * 2 ^ 24).
  - apply Nat.mul_le_mono_r. exact H625.
  - rewrite <- Nat.pow_add_r.
    replace (10 + 24) with 34 by reflexivity.
    apply Nat.pow_le_mono_r.
    + intro Hc; discriminate Hc.
    + exact u5c_le_34_98.
Qed.

Lemma u5c_lin_16Sd : forall d : nat, 16 + S d <= 2 * (16 + d).
Proof. intro d. lia. Qed.

Lemma u5c_base_q : forall d : nat, 625 * (16 + d) ^ 6 <= 4 ^ (3 * (16 + d) + 1).
Proof.
  induction d as [|d IH].
  - replace (16 + 0) with 16 by lia.
    replace (3 * 16 + 1) with 49 by reflexivity.
    exact u5c_base_q_base.
  - assert (Hstep : (16 + S d) ^ 6 <= 64 * (16 + d) ^ 6).
    { apply Nat.le_trans with ((2 * (16 + d)) ^ 6).
      - apply Nat.pow_le_mono_l.
        + apply u5c_lin_16Sd.
      - rewrite Nat.pow_mul_l. reflexivity. }
    replace (3 * (16 + S d) + 1) with (3 * (16 + d) + 1 + 3)
      by (symmetry; apply u5c_base_q_shift).
    rewrite Nat.pow_add_r.
    assert (H43 : 4 ^ 3 = 64) by reflexivity.
    rewrite H43.
    apply Nat.le_trans with (625 * (64 * (16 + d) ^ 6)).
    + apply Nat.mul_le_mono_l. exact Hstep.
    + apply u5c_base_q_scale. exact IH.
Qed.

(* 基例辅助件 M：5·(4m²+6)^3 ≤ 4^(3m+1)（m ≥ 16） *)
Lemma u5c_base_mid_ne0 : forall m : nat, 4 * (m * m) + 6 <> 0.
Proof. intro m. lia. Qed.

Lemma u5c_base_mid_le : forall m : nat, 9 <= m * m ->
  4 * (m * m) + 6 <= 5 * (m * m).
Proof. intros m H. lia. Qed.

Lemma u5c_base_mid : forall m : nat, 16 <= m ->
  5 * (4 * (m * m) + 6) ^ 3 <= 4 ^ (3 * m + 1).
Proof.
  intros m Hm.
  assert (Hq : 625 * m ^ 6 <= 4 ^ (3 * m + 1)).
  { replace m with (16 + (m - 16)) by lia.
    apply u5c_base_q. }
  assert (Hb : (4 * (m * m) + 6) ^ 3 <= (5 * (m * m)) ^ 3).
  { apply Nat.pow_le_mono_l.
    - apply u5c_base_mid_le.
      assert (H9 : 9 <= m * m) by (apply (Nat.mul_le_mono 3 m 3 m); lia).
      exact H9. }
  rewrite Nat.pow_mul_l in Hb.
  replace (5 ^ 3) with 125 in Hb by reflexivity.
  assert (H6 : (m * m) ^ 3 = m ^ 6).
  { replace 6 with (2 * 3) by ring. rewrite Nat.pow_mul_r.
    rewrite u5c_sq_mul. reflexivity. }
  rewrite H6 in Hb.
  apply Nat.le_trans with (5 * (125 * m ^ 6)).
  - apply (Nat.mul_le_mono_l ((4 * (m * m) + 6) ^ 3) (125 * m ^ 6) 5).
    exact Hb.
  - replace (5 * (125 * m ^ 6)) with (625 * m ^ 6) by ring.
    exact Hq.
Qed.

(* 基例步进：P(m) → P(m+3)（指数恰增 4m+6；
   松弛因子 5 由基例辅助件 M 吸收：5(4m²+6)³ ≤ 4^(3m+1)） *)
Lemma u5c_m5_shift : forall m : nat, 3 + (m + 2) = m + 5.
Proof. intro m. lia. Qed.

Lemma u5c_base_step_k : forall m : nat,
  2 * ((m + 3) * (m + 3)) / 3 = 2 * (m * m) / 3 + (4 * m + 6).
Proof.
  intro m.
  replace ((m + 3) * (m + 3)) with (m * m + 6 * m + 9) by ring.
  replace (2 * (m * m + 6 * m + 9)) with ((4 * m + 6) * 3 + 2 * (m * m)) by ring.
  rewrite Nat.div_add_l by lia. lia.
Qed.

Lemma u5c_base_step_exp : forall m X : nat,
  m + 5 + (3 * m + 1 + X) = X + (4 * m + 6).
Proof. intros m X. lia. Qed.

Lemma u5c_base_step_ne0b : forall m : nat, 4 * ((m + 3) * (m + 3)) + 6 <> 0.
Proof. intro m. lia. Qed.

Lemma u5c_base_step_mA : forall m : nat, 16 <= m ->
  4 * ((m + 3) * (m + 3)) + 7 <= 5 * (4 * (m * m) + 7).
Proof.
  intros m Hm.
  assert (H1 : 24 * m <= (2 * m) * m) by (apply Nat.mul_le_mono_r; lia).
  assert (H2 : 43 <= m * m).
  { assert (Ha : 7 * 7 <= 7 * m) by (apply Nat.mul_le_mono_l; lia).
    assert (Hb : 7 * m <= m * m) by (apply Nat.mul_le_mono_r; lia). lia. }
  replace ((m + 3) * (m + 3)) with (m * m + 6 * m + 9) by ring.
  lia.
Qed.

Lemma u5c_base_step_mB : forall m : nat, 16 <= m ->
  4 * ((m + 3) * (m + 3)) + 6 <= 4 * (4 * (m * m) + 6).
Proof.
  intros m Hm.
  assert (H1 : 24 * m <= (2 * m) * m) by (apply Nat.mul_le_mono_r; lia).
  assert (H2 : 42 <= 12 * (m * m)).
  { assert (Ha : 9 <= m * m) by (apply (Nat.mul_le_mono 3 m 3 m); lia).
    assert (Hb : 10 * 9 <= 10 * (m * m)) by (apply Nat.mul_le_mono_l; lia). lia. }
  replace ((m + 3) * (m + 3)) with (m * m + 6 * m + 9) by ring.
  lia.
Qed.

Lemma u5c_5le_pow : forall m : nat, 16 <= m -> 5 <= 4 ^ (3 * m + 1).
Proof.
  intros m Hm.
  apply Nat.le_trans with (4 ^ 2).
  - replace (4 ^ 2) with 16 by reflexivity. lia.
  - apply Nat.pow_le_mono_r.
    + intro Hc; discriminate Hc.
    + assert (H2 : 2 <= 3 * m + 1) by lia. exact H2.
Qed.

Lemma u5c_y2_ge1 : forall m : nat, 1 <= (4 * (m * m) + 6) ^ (m + 2).
Proof.
  intro m. apply u5c_pow_ge1. lia.
Qed.

Lemma u5c_y2_gt1 : forall m : nat, 16 <= m ->
  1 < (4 * (m * m) + 6) ^ (m + 2).
Proof.
  intros m Hm.
  apply (Nat.lt_le_trans 1 2 ((4 * (m * m) + 6) ^ (m + 2))).
  - apply Nat.lt_succ_diag_r.
  - apply Nat.le_trans with (4 * (m * m) + 6).
    + replace (4 * 1 + 6) with 10 by reflexivity. lia.
    + replace (m + 2) with (S (m + 1)) by lia.
      rewrite Nat.pow_succ_r'.
      apply (u5c_le_mul_id (4 * (m * m) + 6)
               ((4 * (m * m) + 6) ^ (m + 1))).
      apply u5c_pow_ge1. lia.
Qed.

Lemma u5c_k7_lt_y3 : forall m : nat, 16 <= m ->
  4 * (m * m) + 7 < (4 * (m * m) + 6) ^ 3.
Proof.
  intro m. intro Hm.
  apply Nat.lt_le_trans with ((4 * (m * m) + 6) * 2).
  - lia.
  - rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
    rewrite Nat.pow_1_r.
    apply Nat.le_trans with ((4 * (m * m) + 6) * (4 * (m * m) + 6)).
    + apply Nat.mul_le_mono_l. lia.
    + apply Nat.mul_le_mono_l.
      apply (u5c_le_mul_id (4 * (m * m) + 6) (4 * (m * m) + 6)).
      assert (Hs : 9 <= m * m) by (apply (Nat.mul_le_mono 3 m 3 m); lia).
      lia.
Qed.

Lemma u5c_p5_ge1 : forall m : nat, 1 <= 4 ^ (m + 5).
Proof.
  intro m.
  apply Nat.le_trans with (4 ^ 2).
  - replace (4 ^ 2) with 16 by reflexivity. lia.
  - apply Nat.pow_le_mono_r.
    + intro Hc; discriminate Hc.
    + assert (H2 : 2 <= m + 5) by lia. exact H2.
Qed.

Lemma u5c_y3_ge1 : forall m : nat, 1 <= (4 * (m * m) + 6) ^ 3.
Proof.
  intro m.
  apply Nat.le_trans with (4 * (m * m) + 6).
  - lia.
  - apply Nat.le_trans with ((4 * (m * m) + 6) * (4 * (m * m) + 6)).
    + apply (u5c_le_mul_id (4 * (m * m) + 6) (4 * (m * m) + 6)). lia.
    + rewrite <- u5c_sq_mul.
      apply Nat.pow_le_mono_r.
      * apply u5c_pos_ne0. lia.
      * lia.
Qed.

Lemma u5c_W_ge1 : forall m : nat,
  1 <= 4 ^ (m + 5) * ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2)).
Proof.
  intro m.
  apply Nat.le_trans with (4 ^ (m + 5)).
  - apply u5c_p5_ge1.
  - apply (u5c_le_mul_id (4 ^ (m + 5))
             ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2))).
    apply Nat.le_trans with ((4 * (m * m) + 6) ^ 3).
    + apply u5c_y3_ge1.
    + apply (u5c_le_mul_id ((4 * (m * m) + 6) ^ 3)
               ((4 * (m * m) + 6) ^ (m + 2))).
      apply u5c_y2_ge1.
Qed.

Lemma u5c_base_step : forall m : nat, 16 <= m ->
  (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2) < 4 ^ (2 * (m * m) / 3) ->
  (4 * ((m + 3) * (m + 3)) + 7) * (4 * ((m + 3) * (m + 3)) + 6) ^ (m + 5)
  < 4 ^ (2 * ((m + 3) * (m + 3)) / 3).
Proof.
  intros m Hm IH.
  assert (Hk := u5c_base_step_k m).
  assert (HmA := u5c_base_step_mA m Hm).
  assert (HmB := u5c_base_step_mB m Hm).
  assert (Hmid : 5 * (4 * (m * m) + 6) ^ 3 <= 4 ^ (3 * m + 1))
    by (apply u5c_base_mid; exact Hm).
  assert (Hpos31 : 0 < 4 ^ (3 * m + 1))
    by (apply (proj1 (Nat.neq_0_lt_0 _)); apply Nat.pow_nonzero;
        intro Hc; discriminate Hc).
  assert (Hk7lt : 4 * (m * m) + 7 < 4 ^ (2 * (m * m) / 3)).
  { apply Nat.lt_le_trans with ((4 * (m * m) + 7) * ((4 * (m * m) + 6) ^ (m + 2))).
    - apply (u5c_lt_mul_id (4 * (m * m) + 7) ((4 * (m * m) + 6) ^ (m + 2))
               (u5c_k7_pos m)).
      apply (u5c_y2_gt1 m Hm).
    - apply Nat.lt_le_incl. exact IH. }
  assert (Hstep : (4 * ((m + 3) * (m + 3)) + 7)
                * (4 * ((m + 3) * (m + 3)) + 6) ^ (m + 5)
              <= (5 * (4 * (m * m) + 7))
                 * (4 ^ (m + 5)
                      * ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2)))).
  { apply (Nat.mul_le_mono (4 * ((m + 3) * (m + 3)) + 7) (5 * (4 * (m * m) + 7))
             ((4 * ((m + 3) * (m + 3)) + 6) ^ (m + 5))
             (4 ^ (m + 5) * ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2)))).
    - exact HmA.
    - apply Nat.le_trans with ((4 * (4 * (m * m) + 6)) ^ (m + 5)).
      + apply Nat.pow_le_mono_l.
        * exact HmB.
      + rewrite Nat.pow_mul_l.
        replace (m + 5) with (3 + (m + 2)) at 2 by (apply u5c_m5_shift).
        rewrite Nat.pow_add_r. rewrite Nat.pow_add_r. reflexivity. }
  rewrite (Nat.mul_comm (5 * (4 * (m * m) + 7))
             (4 ^ (m + 5) * ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2)))) in Hstep.
  assert (HposW : 0 < 4 ^ (m + 5)
    * ((4 * (m * m) + 6) ^ 3 * (4 * (m * m) + 6) ^ (m + 2))).
  { apply Nat.lt_le_trans with 1.
    - apply Nat.lt_0_1.
    - apply u5c_W_ge1. }
  assert (HposW2 : 0 < 4 ^ (m + 5))
    by (apply (proj1 (Nat.neq_0_lt_0 _)); apply Nat.pow_nonzero;
        intro Hc; discriminate Hc).
  assert (Hinner : (4 * (m * m) + 6) ^ 3 * 5
    * ((4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2))
    < 4 ^ (3 * m + 1) * 4 ^ (2 * (m * m) / 3)).
  { apply Nat.le_lt_trans with (4 ^ (3 * m + 1)
      * ((4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2))).
    - apply Nat.mul_le_mono_r.
      rewrite (Nat.mul_comm ((4 * (m * m) + 6) ^ 3) 5). exact Hmid.
    - apply (proj1 (Nat.mul_lt_mono_pos_l (4 ^ (3 * m + 1))
                 ((4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2))
                 (4 ^ (2 * (m * m) / 3)) Hpos31)).
      exact IH. }
  apply Nat.le_lt_trans with (4 ^ (m + 5)
    * ((4 * (m * m) + 6) ^ 3 * 5
         * ((4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2)))).
  - ring_simplify in Hstep. ring_simplify. exact Hstep.
  - apply Nat.lt_le_trans with (4 ^ (m + 5)
      * (4 ^ (3 * m + 1) * 4 ^ (2 * (m * m) / 3))).
    + apply (proj1 (Nat.mul_lt_mono_pos_l _ _ _ HposW2)).
      exact Hinner.
    + rewrite <- Nat.pow_add_r. rewrite <- Nat.pow_add_r.
      rewrite Hk. apply Nat.pow_le_mono_r;
        [intro Hc; discriminate Hc |].
      rewrite (u5c_base_step_exp m (2 * (m * m) / 3)).
      apply Nat.le_refl.
Qed.

(* 基例小段（m ∈ [16,18]；2-幂改写，零大数计算） *)
Lemma u5c_base_small_exp : forall m : nat, 16 <= m -> m <= 18 ->
  11 * (m + 3) < 2 * (2 * (m * m) / 3).
Proof.
  intros m Hm1 Hm2.
  destruct (Nat.eq_dec m 16) as [E16 | NE16].
  - subst m. vm_compute. lia.
  - destruct (Nat.eq_dec m 17) as [E17 | NE17].
    + subst m. vm_compute. lia.
    + destruct (Nat.eq_dec m 18) as [E18 | NE18].
      * subst m. vm_compute. lia.
      * exfalso. lia.
Qed.

Lemma u5c_base_small : forall m : nat, 16 <= m -> m <= 18 ->
  (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2) < 4 ^ (2 * (m * m) / 3).
Proof.
  intros m Hm1 Hm2.
  assert (H2ne : 2 <> 0) by discriminate.
  assert (Hexp := u5c_base_small_exp m Hm1 Hm2).
  assert (Hb7 : 4 * (m * m) + 7 <= 2 ^ 11).
  { assert (Hsq : m * m <= 324)
      by (replace 324 with (18 * 18) by reflexivity;
          apply Nat.mul_le_mono; lia).
    replace (2 ^ 11) with 2048 by reflexivity.
    clear Hexp. lia. }
  assert (Hb6 : 4 * (m * m) + 6 <= 2 ^ 11).
  { assert (Hsq : m * m <= 324)
      by (replace 324 with (18 * 18) by reflexivity;
          apply Nat.mul_le_mono; lia).
    replace (2 ^ 11) with 2048 by reflexivity.
    clear Hexp. lia. }
  assert (HpowL : (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2)
                <= 2 ^ (11 * (m + 3))).
  { apply Nat.le_trans with (2 ^ 11 * (2 ^ 11) ^ (m + 2)).
    - apply Nat.mul_le_mono; [exact Hb7 |].
      apply Nat.pow_le_mono_l. exact Hb6.
    - rewrite <- Nat.pow_mul_r. rewrite <- Nat.pow_add_r.
      assert (Hidx : 11 + 11 * (m + 2) = 11 * (m + 3)) by lia.
      rewrite Hidx. apply Nat.le_refl. }
  assert (H4 : 4 ^ (2 * (m * m) / 3) = 2 ^ (2 * (2 * (m * m) / 3)))
    by (rewrite hl_pow4; reflexivity).
  rewrite H4.
  apply Nat.le_lt_trans with (2 ^ (11 * (m + 3))).
  - exact HpowL.
  - apply Nat.pow_lt_mono_r.
    + apply Nat.lt_succ_diag_r.
    + exact Hexp.
Qed.

(* 基例主件 u5c_base：∀m ≥ 16，(4m²+7)·(4m²+6)^(m+2) < 4^(⌊2m²/3⌋)
   （强归纳：m ≤ 18 走基例；m ≥ 19 走 stride-3 步进） *)
Lemma u5c_base_pre : forall m : nat, 18 < m ->
  16 <= m - 3 /\ m - 3 < m.
Proof. intros m H. split; lia. Qed.

Lemma u5c_sub3_eq : forall m : nat, 18 < m -> m = m - 3 + 3.
Proof. intros m H. lia. Qed.

Lemma u5c_base : forall m : nat, 16 <= m ->
  (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2) < 4 ^ (2 * (m * m) / 3).
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun m => 16 <= m ->
      (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2) < 4 ^ (2 * (m * m) / 3))).
  intros m IH Hm.
  destruct (le_lt_dec m 18) as [Hs | Hl].
  - apply u5c_base_small; assumption.
  - destruct (u5c_base_pre m Hl) as [Hm3 Hlt].
    specialize (IH (m - 3) Hlt Hm3).
    replace m with (m - 3 + 3) by (symmetry; apply u5c_sub3_eq; exact Hl).
    replace (m - 3 + 3 + 2) with (m - 3 + 5) by lia.
    apply (u5c_base_step (m - 3)); assumption.
Qed.

(* 块引理：s² ≤ 2n < (S s)² ⟹ 2m² ≤ n < 2(m+1)²（m := s/2） *)
Lemma u5c_block_lo : forall s m r n : nat,
  s = 2 * m + r -> r < 2 -> s * s <= 2 * n -> 2 * m * m <= n.
Proof. intros s m r n H1 H2 H3. lia. Qed.

Lemma u5c_block_hi : forall s m r n : nat,
  s = 2 * m + r -> r < 2 -> 2 * n < (S s) * (S s) ->
  n < 2 * (S m) * (S m).
Proof.
  intros s m r n H1 H2 H3.
  assert (Hb : S s <= 2 * S m) by lia.
  assert (Hc : (S s) * (S s) <= (2 * S m) * (2 * S m))
    by (apply Nat.mul_le_mono; exact Hb).
  assert (Hstep : 2 * n < (2 * S m) * (2 * S m)).
  { apply (Nat.lt_le_trans (2 * n) ((S s) * (S s)) ((2 * S m) * (2 * S m)));
      [exact H3 | exact Hc]. }
  assert (Hring : (2 * S m) * (2 * S m) = 2 * (2 * (S m) * (S m))) by ring.
  rewrite Hring in Hstep.
  lia.
Qed.

Lemma u5c_block : forall n s : nat, s * s <= 2 * n -> 2 * n < (S s) * (S s) ->
  2 * (s / 2) * (s / 2) <= n /\ n < 2 * (S (s / 2)) * (S (s / 2)).
Proof.
  intros n s Hlo Hhi.
  pose proof (Nat.div_mod_eq s 2) as Hdm.
  pose proof (Nat.mod_upper_bound s 2 ltac:(lia)) as Hmod.
  split.
  - exact (u5c_block_lo s (s / 2) (s mod 2) n Hdm Hmod Hlo).
  - exact (u5c_block_hi s (s / 2) (s mod 2) n Hdm Hmod Hhi).
Qed.

(* 块足 m ≥ 16（n ≥ 512） *)
Lemma u5c_spine_m16_aux : forall m n : nat,
  512 <= n -> n < 2 * (S m) * (S m) -> 16 <= m.
Proof.
  intros m n H1 H2.
  destruct (le_lt_dec 16 m) as [H | H]; [exact H |].
  exfalso.
  assert (Hc : (S m) * (S m) <= 16 * 16)
    by (apply Nat.mul_le_mono; lia).
  replace (16 * 16) with 256 in Hc by reflexivity.
  assert (H2lt : 2 * (S m) * (S m) <= 2 * 256).
  { replace (2 * (S m) * (S m)) with (2 * ((S m) * (S m))) by ring.
    apply Nat.mul_le_mono_l. exact Hc. }
  replace (2 * 256) with 512 in H2lt by reflexivity.
  lia.
Qed.

Lemma u5c_spine_m16 : forall n s : nat, 512 <= n ->
  s * s <= 2 * n -> 2 * n < (S s) * (S s) -> 16 <= s / 2.
Proof.
  intros n s Hn Hlo Hhi.
  pose proof (Nat.div_mod_eq s 2) as Hdm.
  pose proof (Nat.mod_upper_bound s 2 ltac:(lia)) as Hmod.
  apply (u5c_spine_m16_aux (s / 2) n Hn).
  exact (u5c_block_hi s (s / 2) (s mod 2) n Hdm Hmod Hhi).
Qed.

(* 块唯一性：k 与 k+4 分属 m1、m2 块 ⟹ m1 = m2
   （块宽 4m+4 ≥ 68 > 4，k ≥ 2m₂² 时跨界不可能） *)
Lemma u5c_block_uniq : forall m1 m2 k : nat,
  2 * m1 * m1 <= k -> k < 2 * (S m1) * (S m1) ->
  2 * m2 * m2 <= k -> k + 4 < 2 * (S m2) * (S m2) ->
  m1 = m2.
Proof.
  intros m1 m2 k A B C0 D.
  destruct (le_lt_dec m1 m2) as [H | H].
  - destruct (Nat.eq_dec m1 m2) as [E | NE]; [exact E |].
    exfalso.
    assert (Hlt : m1 < m2) by lia.
    assert (H1 : 2 * (S m1) * (S m1) <= 2 * m2 * m2).
    { replace (2 * (S m1) * (S m1)) with (2 * ((S m1) * (S m1))) by ring.
      replace (2 * m2 * m2) with (2 * (m2 * m2)) by ring.
      apply Nat.mul_le_mono; [exact (Nat.le_refl 2) |].
      apply (Nat.mul_le_mono (S m1) m2 (S m1) m2); exact Hlt. }
    lia.
  - exfalso.
    assert (Hlt : m2 < m1) by lia.
    assert (H1 : 2 * (S m2) * (S m2) <= 2 * m1 * m1).
    { replace (2 * (S m2) * (S m2)) with (2 * ((S m2) * (S m2))) by ring.
      replace (2 * m1 * m1) with (2 * (m1 * m1)) by ring.
      apply Nat.mul_le_mono; [exact (Nat.le_refl 2) |].
      apply (Nat.mul_le_mono (S m2) m1 (S m2) m1); exact Hlt. }
    lia.
Qed.

Lemma u5c_div_mono2_aux : forall x q1 m1 q2 m2 n : nat,
  x = 3 * q1 + m1 -> m1 < 3 -> n = 3 * q2 + m2 -> m2 < 3 -> x <= n ->
  q1 <= q2.
Proof. intros x q1 m1 q2 m2 n H1 H2 H3 H4 H5. lia. Qed.

Lemma u5c_div_mono2 : forall m n : nat, 2 * m * m <= n ->
  2 * (m * m) / 3 <= n / 3.
Proof.
  intros m n H.
  assert (H2mm : 2 * (m * m) <= n).
  { replace (2 * (m * m)) with (2 * m * m) by ring. exact H. }
  pose proof (Nat.div_mod_eq (2 * (m * m)) 3) as H1.
  pose proof (Nat.mod_upper_bound (2 * (m * m)) 3 ltac:(lia)) as H2.
  pose proof (Nat.div_mod_eq n 3) as H3.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as H4.
  exact (u5c_div_mono2_aux (2 * (m * m)) ((2 * (m * m)) / 3) ((2 * (m * m)) mod 3)
           (n / 3) (n mod 3) n H1 H2 H3 H4 H2mm).
Qed.

Lemma u5c_spine_base_le : forall m n : nat, 2 * m * m <= n ->
  n <= 2 * m * m + 3 ->
  (2 * n + 1) * (2 * n) ^ (m + 2)
  <= (4 * (m * m) + 7) * (4 * (m * m) + 6) ^ (m + 2).
Proof.
  intros m n Hlo Hhi.
  assert (H1 : 2 * n <= 4 * (m * m) + 6) by lia.
  assert (H2 : 2 * n + 1 <= 4 * (m * m) + 7) by lia.
  apply Nat.mul_le_mono.
  - exact H2.
  - apply Nat.pow_le_mono_l. exact H1.
Qed.

Lemma u5c_spine_Hn4 : forall m n : nat, 16 <= m -> 2 * m * m + 3 < n ->
  512 <= n - 4.
Proof.
  intros m n Hm H.
  assert (Hq : 256 <= m * m) by (apply (Nat.mul_le_mono 16 m 16 m); lia).
  lia.
Qed.

Lemma u5c_spine_H32 : forall m n : nat, 16 <= m -> 2 * m * m + 3 < n ->
  32 * (m + 2) <= 2 * (n - 4).
Proof.
  intros m n Hm H.
  assert (Hq : 16 * m <= m * m) by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

Lemma u5c_spine_eq1 : forall n : nat, 4 <= n -> 2 * n + 1 = 2 * (n - 4) + 9.
Proof. intros n H. lia. Qed.

Lemma u5c_spine_eq2 : forall n : nat, 4 <= n -> 2 * n = 2 * (n - 4) + 8.
Proof. intros n H. lia. Qed.

Lemma u5c_2n4_pos : forall n : nat, 512 <= n -> 0 < 2 * (n - 4).
Proof. intros n H. lia. Qed.

Lemma u5c_2n4_ge3 : forall n : nat, 512 <= n -> 3 <= 2 * (n - 4).
Proof. intros n H. lia. Qed.

Lemma u5c_spine_lt4 : forall a X : nat, 0 < X -> 3 <= a ->
  (2 * a + 9) * X < 4 * ((2 * a + 1) * X).
Proof.
  intros a X HX Ha.
  assert (H : 2 * a + 9 < 4 * (2 * a + 1)) by lia.
  replace (4 * ((2 * a + 1) * X)) with ((4 * (2 * a + 1)) * X) by ring.
  apply (proj1 (Nat.mul_lt_mono_pos_r _ _ _ HX)). exact H.
Qed.

(* 主链 u5c_spine：n ≥ 512 ⟹ (2n+1)·(2n)^(⌊√(2n)/2⌋+2) < 4^(⌊n/3⌋)
   （显式平方根见证 s；强归纳 n：块首四点走 u5c_base，
     n ≥ 2m²+4 时 n−4 同块，stride-4 走 u5c_step4） *)
Lemma u5c_spine : forall n s : nat, 512 <= n -> s * s <= 2 * n ->
  2 * n < (S s) * (S s) ->
  (2 * n + 1) * (2 * n) ^ (s / 2 + 2) < 4 ^ (n / 3).
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun n => forall s : nat, 512 <= n -> s * s <= 2 * n ->
      2 * n < (S s) * (S s) ->
      (2 * n + 1) * (2 * n) ^ (s / 2 + 2) < 4 ^ (n / 3))).
  intros n IH s Hn Hlo Hhi.
  destruct (u5c_block n s Hlo Hhi) as [Hblo Hbhi].
  pose proof (u5c_spine_m16 n s Hn Hlo Hhi) as Hm16.
  destruct (le_lt_dec n (2 * (s / 2) * (s / 2) + 3)) as [Hbase | Hstep].
  - assert (Hsp := u5c_spine_base_le (s / 2) n Hblo Hbase).
    assert (Hb := u5c_base (s / 2) Hm16).
    apply Nat.le_lt_trans with ((4 * (s / 2 * (s / 2)) + 7)
        * (4 * (s / 2 * (s / 2)) + 6) ^ (s / 2 + 2)).
    + exact Hsp.
    + apply Nat.lt_le_trans with (4 ^ (2 * (s / 2 * (s / 2)) / 3)).
      * exact Hb.
      * apply Nat.pow_le_mono_r.
        -- intro Hc; discriminate Hc.
        -- apply u5c_div_mono2. exact Hblo.
  - assert (Hn4 : 512 <= n - 4) by (apply (u5c_spine_Hn4 (s / 2) n Hm16 Hstep)).
    destruct (u5c_sqrt_ex (2 * (n - 4))) as [s' [Hlo' Hhi']].
    specialize (IH (n - 4) (u5c_sub4_lt n (Nat.le_trans 4 512 n u5c_le_4_512 Hn))
                   s' Hn4 Hlo' Hhi').
    destruct (u5c_block (n - 4) s' Hlo' Hhi') as [Hblo' Hbhi'].
    assert (Hm2 : 2 * (s / 2) * (s / 2) <= n) by exact Hblo.
    assert (Hm2lo : 2 * (s / 2) * (s / 2) <= n - 4) by lia.
    assert (Hbhi4 : n - 4 + 4 < 2 * S (s / 2) * S (s / 2)) by lia.
    pose proof (u5c_block_uniq (s' / 2) (s / 2) (n - 4)
      Hblo' Hbhi' Hm2lo Hbhi4) as Heq.
    rewrite Heq in IH.
    assert (H32 : 32 * (s / 2 + 2) <= 2 * (n - 4))
      by (apply (u5c_spine_H32 (s / 2) n Hm16 Hstep)).
    pose proof (u5c_step4 (2 * (n - 4)) (s / 2 + 2) (u5c_2n4_ge3 n Hn) H32) as Hst.
    assert (Hd3 := u5c_div_step3 n).
    assert (Hpow1 : 4 ^ ((n - 4) / 3 + 1) = 4 * 4 ^ ((n - 4) / 3)).
    { replace ((n - 4) / 3 + 1) with (S ((n - 4) / 3))
        by (symmetry; apply Nat.add_1_r).
      rewrite Nat.pow_succ_r'. reflexivity. }
    replace (2 * n + 1) with (2 * (n - 4) + 9)
      by (symmetry; apply u5c_spine_eq1;
          exact (Nat.le_trans 4 512 n u5c_le_4_512 Hn)).
    replace (2 * n) with (2 * (n - 4) + 8)
      by (symmetry; apply u5c_spine_eq2;
          exact (Nat.le_trans 4 512 n u5c_le_4_512 Hn)).
    apply Nat.lt_le_trans with (4 * 4 ^ ((n - 4) / 3)).
    { apply Nat.le_lt_trans with (4 * (2 * (n - 4) + 1) * (2 * (n - 4)) ^ (s / 2 + 2)).
      { exact Hst. }
      { replace (4 * (2 * (n - 4) + 1) * (2 * (n - 4)) ^ (s / 2 + 2))
          with (4 * ((2 * (n - 4) + 1) * (2 * (n - 4)) ^ (s / 2 + 2))) by ring.
        assert (H04 : 0 < 4) by lia.
        apply (proj1 (Nat.mul_lt_mono_pos_l 4 _ _ H04)).
        exact IH. } }
    { rewrite <- Hpow1.
      apply Nat.pow_le_mono_r.
      { intro Hc; discriminate Hc. }
      { exact (Hd3 Hn). } }
Qed.
(* ============================================================ *)
(* §8 装配：C(2n,n) 的窗吸收与 primorial 归宿 →                  *)
(*    u5c_bertrand_full（表域 [2,512] 拼接 + ≥512 解析）          *)
(* ============================================================ *)

(* ---- 基础助手（幂-free，可安全 lia） ---- *)

Lemma u5c_le_1_512 : 1 <= 512.
Proof. apply (proj1 (Nat.succ_le_mono 0 511)). apply Nat.le_0_l. Qed.

Lemma u5c_prime_ne0 : forall p : nat, pr_prime p -> p <> 0.
Proof.
  intros p Hp. unfold pr_prime in Hp. destruct Hp as [H _]. lia.
Qed.

Lemma u5c_prime_ge2 : forall p : nat, pr_prime p -> 2 <= p.
Proof.
  intros p Hp. unfold pr_prime in Hp. destruct Hp as [H _]. exact H.
Qed.

Lemma u5c_div_lt : forall d a : nat, d <> 0 -> a / d = 0 -> a < d.
Proof.
  intros d a Hd H0.
  pose proof (Nat.div_mod_eq a d) as Hdm.
  pose proof (Nat.mod_upper_bound a d Hd) as Hub.
  rewrite H0 in Hdm. rewrite Nat.mul_0_r in Hdm.
  rewrite Nat.add_0_l in Hdm. rewrite Hdm. exact Hub.
Qed.

Lemma u5c_div3_le_aux : forall q m a : nat, a = 3 * q + m -> m < 3 -> q <= a.
Proof. intros q m a H1 H2. lia. Qed.

Lemma u5c_div3_le : forall a : nat, a / 3 <= a.
Proof.
  intro a.
  pose proof (Nat.div_mod_eq a 3) as H1.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as H2.
  exact (u5c_div3_le_aux (a / 3) (a mod 3) a H1 H2).
Qed.

Lemma u5c_prim3_ge1 : forall n : nat, 512 <= n -> 1 <= (2 * n) / 3.
Proof.
  intros n H.
  apply (Nat.le_trans 1 ((2 * 512) / 3) ((2 * n) / 3)).
  - replace ((2 * 512) / 3) with 341 by reflexivity.
    apply (proj1 (Nat.succ_le_mono 0 340)). apply Nat.le_0_l.
  - apply Nat.div_le_mono.
    + intro Hc; discriminate Hc.
    + apply Nat.mul_le_mono_l.
      apply (Nat.le_trans 512 512 n); [apply Nat.le_refl | exact H].
Qed.

(* 指数封顶：r^v ∣ r^e·Y 且 r ∤ Y ⟹ v ≤ e *)
Lemma u5c_pow_dvd_le : forall r v e Y : nat, pr_prime r ->
  pec_dvd (r ^ v) (r ^ e * Y) -> pec_dvd r Y -> False -> v <= e.
Proof.
  intros r v e Y Hr Hd HY HnY.
  destruct (le_lt_dec v e) as [H | H]; [exact H |].
  exfalso.
  assert (Hrp0 : r <> 0) by (apply u5c_prime_ne0; exact Hr).
  assert (Hlt : e < v) by exact H.
  destruct Hd as [z Hz].
  replace (r ^ v) with (r ^ e * r ^ (v - e)) in Hz
    by (replace v with (e + (v - e)) at 2 by lia;
        rewrite Nat.pow_add_r; reflexivity).
  assert (HY2 : Y = r ^ (v - e) * z).
  { apply (proj1 (Nat.mul_cancel_l Y (r ^ (v - e) * z) (r ^ e)
                   (Nat.pow_nonzero r e Hrp0))).
    rewrite Hz. ring. }
  destruct (v - e) as [|k'] eqn:Ek.
  - apply (Nat.sub_0_le v e) in Ek.
    exfalso. apply (Nat.lt_irrefl e). apply (Nat.lt_le_trans e v e Hlt Ek).
  - exact HnY.
Qed.

(* master 证书指数封顶：r^v ∣ C、C·R1·R1 = r^e·R2、2n/r^(S s) = 0 ⟹ v ≤ e *)
Lemma u5c_master_bound : forall p n s e v : nat, pr_prime p ->
  pec_dvd (p ^ v) (pec_mid n) ->
  pec_mid n * u5c_R p n (S s) * u5c_R p n (S s)
  = p ^ e * u5c_R p (2 * n) (S s) ->
  2 * n / p ^ (S s) = 0 ->
  v <= e.
Proof.
  intros p n s e v Hp Hdv Heq H0.
  destruct (le_lt_dec v e) as [Hve | Hgt]; [exact Hve |].
  exfalso.
  assert (Hps0 : p ^ S s <> 0)
    by (apply Nat.pow_nonzero; apply u5c_prime_ne0; exact Hp).
  assert (HltS : 2 * n < p ^ S s) by (apply (u5c_div_lt _ _ Hps0 H0)).
  assert (H0' : 2 * n / p ^ S (S s) = 0).
  { apply (u5c_div_eq_zero (p ^ S (S s)) (2 * n)).
    - apply Nat.pow_nonzero. apply u5c_prime_ne0. exact Hp.
    - apply (Nat.lt_le_trans (2 * n) (p ^ S s) (p ^ S (S s))).
      + exact HltS.
      + apply Nat.pow_le_mono_r; [apply u5c_prime_ne0; exact Hp | apply Nat.le_succ_diag_r]. }
  destruct Hdv as [z Hz].
  assert (Hpe0 : p ^ e <> 0)
    by (apply Nat.pow_nonzero; apply u5c_prime_ne0; exact Hp).
  assert (HX : p ^ e * u5c_R p (2 * n) (S s)
             = p ^ e * (p ^ (v - e) * z * (u5c_R p n (S s) * u5c_R p n (S s)))).
  { rewrite <- Heq.
    rewrite Hz.
    replace (p ^ v) with (p ^ e * p ^ (v - e))
      by (rewrite <- (Nat.pow_add_r p e (v - e));
          replace (e + (v - e)) with v by lia; reflexivity).
    ring. }
  assert (HR2 : u5c_R p (2 * n) (S s)
              = p ^ (v - e) * z * (u5c_R p n (S s) * u5c_R p n (S s))).
  { apply (proj1 (Nat.mul_cancel_l (u5c_R p (2 * n) (S s))
                   (p ^ (v - e) * z * (u5c_R p n (S s) * u5c_R p n (S s)))
                   (p ^ e) Hpe0)).
    exact HX. }
  assert (Hge1 : S 0 <= v - e) by lia.
  destruct (v - e) as [|w] eqn:Ew.
  - lia.
  - apply (u5c_R_not_dvd p (S s) (2 * n) Hp H0').
    exists (p ^ w * (z * (u5c_R p n (S s) * u5c_R p n (S s)))).
    rewrite HR2.
    replace (p ^ S w) with (p * p ^ w)
      by (rewrite Nat.pow_succ_r'; reflexivity).
    ring.
Qed.

(* ---- 吸收归纳：逐素幂可归宿 ⟹ 整体整除
   （最小素因子强归纳；w0 为 p-余子，r ≠ p 走无公共素因子消去） ---- *)
Lemma u5c_cprime_gen : forall C : nat,
  forall X : nat, 1 <= C ->
  (forall r v : nat, pr_prime r -> pec_dvd (r ^ v) C -> pec_dvd (r ^ v) X) ->
  pec_dvd C X.
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun C => forall X : nat, 1 <= C ->
      (forall r v : nat, pr_prime r -> pec_dvd (r ^ v) C -> pec_dvd (r ^ v) X) ->
      pec_dvd C X)).
  intros m IH X H1 Hpow.
  destruct m as [|m'].
  - exfalso. inversion H1.
  - destruct m' as [|m''].
    + exists X. symmetry. apply Nat.mul_1_l.
    + assert (H2 : 2 <= S (S m'')).
      { apply (proj1 (Nat.succ_le_mono 1 (S m''))).
        apply (proj1 (Nat.succ_le_mono 0 m'')). apply Nat.le_0_l. }
      destruct (pr_min_factor_exists (S (S m'')) H2) as [p [Hpa Hpp]].
      destruct Hpa as [a1 Ha1].
      rewrite (Nat.mul_comm a1 p) in Ha1.
      assert (Hpne0 : p <> 0) by (apply u5c_prime_ne0; exact Hpp).
      assert (Hpm : pec_dvd p (S (S m'')))
        by (apply (pec_dvd_of_eq p _ a1); exact Ha1).
      assert (Hpx : pec_dvd p X).
      { destruct Hpm as [z Hz].
        assert (Hp1 : pec_dvd (p ^ 1) (S (S m''))).
        { exists z. rewrite Nat.pow_1_r. exact Hz. }
        destruct (Hpow p 1 Hpp Hp1) as [w Hw].
        exists w. rewrite Hw. rewrite Nat.pow_1_r. reflexivity. }
      destruct Hpx as [w0 Hw0].
      assert (Ha11 : 1 <= a1).
      { destruct a1 as [|a1'].
        - rewrite Nat.mul_0_r in Ha1. inversion Ha1.
        - apply (proj1 (Nat.succ_le_mono 0 a1')). apply Nat.le_0_l. }
      assert (Ha1lt : a1 < S (S m'')).
      { rewrite Ha1.
        assert (H1p : 1 < p).
        { apply (Nat.lt_le_trans 1 2 p).
          - apply Nat.lt_succ_diag_r.
          - apply u5c_prime_ge2. exact Hpp. }
        rewrite (Nat.mul_comm p a1).
        apply u5c_lt_mul_id.
        - apply (proj1 (Nat.neq_0_lt_0 a1)). apply u5c_pos_ne0. exact Ha11.
        - exact H1p. }
      assert (Hr2of : forall r : nat, pr_prime r -> 2 <= r)
        by (intros r Hr; apply u5c_prime_ge2; exact Hr).
      assert (Hpow1 : forall r v : nat, pr_prime r -> pec_dvd (r ^ v) a1 ->
                pec_dvd (r ^ v) w0).
      { intros r v Hr Hdv.
        assert (Hr2 := Hr2of r Hr).
        destruct (Nat.eq_dec r p) as [Hrp | Hrnp].
        + subst r.
          destruct Hdv as [u Hu].
          assert (HdC : pec_dvd (p ^ S v) (S (S m''))).
          { replace (p ^ S v) with (p * p ^ v)
              by (rewrite Nat.pow_succ_r'; reflexivity).
            exists u. rewrite Ha1, Hu. ring. }
          assert (HdX : pec_dvd (p ^ S v) X) by (apply (Hpow p (S v) Hpp HdC)).
          destruct HdX as [w Hw].
          exists w.
          apply (proj1 (Nat.mul_cancel_l w0 (p ^ v * w) p Hpne0)).
          rewrite <- Hw0. rewrite Hw. rewrite Nat.pow_succ_r'. ring.
        + assert (HdvC : pec_dvd (r ^ v) (S (S m''))).
          { destruct Hdv as [u Hu].
            apply (pec_dvd_of_eq (r ^ v) _ (p * u)).
            rewrite Ha1, Hu. ring. }
          assert (HdX : pec_dvd (r ^ v) X) by (apply (Hpow r v Hr HdvC)).
          destruct HdX as [w1 Hw1].
          assert (Hdp0 : pec_dvd (r ^ v) (p * w0)).
          { exists w1. rewrite <- Hw0. exact Hw1. }
          apply (u5c_coprime_cancel p (r ^ v) w0).
          * apply u5c_pow_ge1.
            apply (proj1 (Nat.neq_0_lt_0 _)). apply u5c_prime_ne0. exact Hr.
          * exact Hdp0.
          * intros d Hdpr Hdrr Hdp.
            assert (Hdr : d = r).
            { apply (u5c_dvd_pow_eq r v d).
              - exact Hr2.
              - exact Hr.
              - exact Hdpr.
              - exact Hdrr. }
            apply Hrnp. rewrite Hdr in Hdp.
            apply (pec_prime_dvd_prime r p Hr Hpp Hdp). }
      destruct (IH a1 Ha1lt w0 Ha11 Hpow1) as [z Hz].
      exists z. rewrite Ha1, Hw0, Hz.
      rewrite <- (Nat.mul_assoc p a1 z). reflexivity.
Qed.

(* ---- 下界：4^n ≤ C(2n,n)·(2n+1)
   （fact 恒等式：4^n·(n!)² ≤ (2n)!·(2n+1) 归纳） ---- *)
Lemma u5c_binom_step_lin : forall n : nat,
  4 * (S n * S n) <= (2 * n + 2) * (2 * n + 3).
Proof. intro n. lia. Qed.

Lemma u5c_binom_lower : forall n : nat,
  4 ^ n * fact n * fact n <= fact (2 * n) * (2 * n + 1).
Proof.
  induction n as [|n IH].
  - replace (2 * 0) with 0 by lia.
    cbn [fact Nat.pow]. lia.
  - replace (2 * S n) with (S (S (n + n))) by lia.
    replace (fact (S (S (n + n))))
      with (S (S (n + n)) * S (n + n) * fact (n + n))
      by (cbn [fact]; ring).
    replace (fact (S n)) with (S n * fact n)
      by (cbn [fact]; reflexivity).
    replace (n + n) with (2 * n) by lia.
    assert (Hstep : 4 * (S n * S n) * (4 ^ n * fact n * fact n)
                  <= fact (2 * n) * (2 * n + 1) * ((2 * n + 2) * (2 * n + 3))).
    { replace (fact (2 * n) * (2 * n + 1) * ((2 * n + 2) * (2 * n + 3)))
        with (((2 * n + 2) * (2 * n + 3)) * (fact (2 * n) * (2 * n + 1))) by ring.
      apply Nat.mul_le_mono; [apply u5c_binom_step_lin | exact IH]. }
    apply Nat.le_trans with (4 * (S n * S n) * (4 ^ n * fact n * fact n)).
    + rewrite Nat.pow_succ_r'.
      replace (4 * 4 ^ n * (S n * fact n) * (S n * fact n))
        with (4 * (S n * S n) * (4 ^ n * fact n * fact n)) by ring.
      apply Nat.le_refl.
    + apply Nat.le_trans with
        (fact (2 * n) * (2 * n + 1) * ((2 * n + 2) * (2 * n + 3))).
      * exact Hstep.
      * replace (S (S (2 * n)) * S (2 * n) * fact (2 * n) * (S (S (2 * n)) + 1))
          with (fact (2 * n) * (2 * n + 1) * ((2 * n + 2) * (2 * n + 3)))
          by ring.
        apply Nat.le_refl.
Qed.

Lemma u5c_mid_lower : forall n : nat, 4 ^ n <= pec_mid n * (2 * n + 1).
Proof.
  intro n.
  assert (Hbin := u5c_binom_lower n).
  assert (Hmid := pec_mid_fact_eq n).
  assert (HposF : 0 < fact n * fact n).
  { apply (Nat.mul_pos_pos (fact n) (fact n)); apply u5c_fact_pos. }
  rewrite <- Hmid in Hbin.
  apply (proj2 (Nat.mul_le_mono_pos_l (4 ^ n) (pec_mid n * (2 * n + 1))
                  (fact n * fact n) HposF)).
  replace ((fact n * fact n) * 4 ^ n) with (4 ^ n * fact n * fact n) by ring.
  replace ((fact n * fact n) * (pec_mid n * (2 * n + 1)))
    with (pec_mid n * fact n * fact n * (2 * n + 1)) by ring.
  exact Hbin.
Qed.

(* ---- 中段主语句薄包与指数函数（p 无关事实外提） ---- *)

(* 中段主语句薄包：2≤p 前提由 prime 自取 *)
Lemma u5c_mid_master' : forall p n K : nat, pr_prime p -> 1 <= n ->
  n / p ^ K = 0 ->
  { e : nat & (pec_mid n * u5c_R p n K * u5c_R p n K
               = p ^ e * u5c_R p (2 * n) K)
              /\ pec_dvd (p ^ e) (pec_mid n)
              /\ p ^ e <= 2 * n
              /\ e = u5c_leg p (2 * n) K - 2 * u5c_leg p n K }.
Proof.
  intros p n K Hpp Hn1 Hz.
  apply (u5c_mid_master p n K).
  - apply u5c_prime_ge2. exact Hpp.
  - exact Hpp.
  - exact Hn1.
  - exact Hz.
Defined.

(* 素底商零：p 素、4≤t、2n < t² ⟹ n / p^t = 0 *)
Lemma u5c_div0_prime : forall n t p : nat, pr_prime p -> 4 <= t ->
  2 * n < t * t -> n / p ^ t = 0.
Proof.
  intros n t p Hp H4 H2n.
  assert (Hne : p ^ t <> 0)
    by (apply Nat.pow_nonzero; apply u5c_prime_ne0; exact Hp).
  assert (H1 : t * t <= 2 ^ t) by (apply u5c_pow2_ge_sq; exact H4).
  assert (H2 : 2 ^ t <= p ^ t).
  { apply Nat.pow_le_mono_l.
    - apply u5c_prime_ge2. exact Hp. }
  apply (u5c_div_eq_zero (p ^ t) n); [exact Hne |].
  apply (Nat.lt_le_trans n (t * t) (p ^ t)).
  - apply u5c_lt_half. replace (n + n) with (2 * n) by ring. exact H2n.
  - apply (Nat.le_trans (t * t) (2 ^ t) (p ^ t)); [exact H1 | exact H2].
Qed.

(* 总指数函数：全素 p 给 master 指数，非素给 0 *)
Definition u5c_expf_sig (p n s : nat) (Hs : 2 * n < (S s) * (S s)) (H4 : 4 <= S s)
  (Hn1 : 1 <= n) :
  { e : nat & (pr_prime p ->
               (pec_mid n * u5c_R p n (S s) * u5c_R p n (S s)
                = p ^ e * u5c_R p (2 * n) (S s)
                /\ pec_dvd (p ^ e) (pec_mid n)
                /\ p ^ e <= 2 * n
                /\ e = u5c_leg p (2 * n) (S s) - 2 * u5c_leg p n (S s)))
              \/ (e = 0 /\ pr_prime_bool p = false) } :=
  match pr_prime_bool p as b
        return (pr_prime_bool p = b ->
                { e : nat & (pr_prime p ->
                             (pec_mid n * u5c_R p n (S s) * u5c_R p n (S s)
                              = p ^ e * u5c_R p (2 * n) (S s)
                              /\ pec_dvd (p ^ e) (pec_mid n)
                              /\ p ^ e <= 2 * n
                              /\ e = u5c_leg p (2 * n) (S s) - 2 * u5c_leg p n (S s)))
                            \/ (e = 0 /\ pr_prime_bool p = false) })
  with
  | true => fun Eb =>
      match u5c_mid_master' p n (S s) (pr_prime_bool_true p Eb) Hn1
              (u5c_div0_prime n (S s) p (pr_prime_bool_true p Eb) H4 Hs) with
      | existT _ e P => existT _ e (or_introl (fun _ => P))
      end
  | false => fun Eb => existT _ 0 (or_intror (conj eq_refl Eb))
  end eq_refl.

Definition u5c_expf (p n s : nat) (Hs : 2 * n < (S s) * (S s)) (H4 : 4 <= S s)
  (Hn1 : 1 <= n) : nat :=
  projT1 (u5c_expf_sig p n s Hs H4 Hn1).

(* expf 谱：p 素时 expf 即 master 全指数，并携四合取肢 *)
Lemma u5c_expf_spec : forall (p n s : nat)
    (Hs : 2 * n < (S s) * (S s)) (H4 : 4 <= S s) (Hn1 : 1 <= n),
  pr_prime p ->
  { e : nat & u5c_expf p n s Hs H4 Hn1 = e
              /\ pec_mid n * u5c_R p n (S s) * u5c_R p n (S s)
                 = p ^ e * u5c_R p (2 * n) (S s)
              /\ pec_dvd (p ^ e) (pec_mid n)
              /\ p ^ e <= 2 * n
              /\ e = u5c_leg p (2 * n) (S s) - 2 * u5c_leg p n (S s) }.
Proof.
  intros p n s Hs H4 Hn1 Hpr.
  unfold u5c_expf.
  destruct (u5c_expf_sig p n s Hs H4 Hn1) as [e Hor].
  exists e. split.
  - reflexivity.
  - destruct Hor as [H | [E0 Hfb]].
    + exact (H Hpr).
    + exfalso. rewrite (pr_prime_bool_false p Hpr) in Hfb. discriminate Hfb.
Defined.

(* 窗表 NoDup（成员严格降） *)
Lemma u5c_win_nodup : forall a k : nat, NoDup (pec_win a k).
Proof.
  intros a k. induction k as [|k IH].
  - cbn [pec_win]. constructor.
  - cbn [pec_win]. destruct (pr_prime_bool (a + S k)).
    + constructor; [| exact IH].
      intros Hin. destruct (pec_win_in a k (a + S k) Hin) as [_ [_ Hle]]. lia.
    + exact IH.
Qed.

(* 单射 map 保 NoDup *)
Lemma u5c_map_nodup : forall (f : nat -> nat) (l : list nat),
  (forall x y : nat, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros f l Hinj. induction l as [|a l IH]; intros Hnd.
  - cbn [map]. constructor.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd'].
    constructor.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
      assert (Ha : y = a) by (apply Hinj; exact Hy).
      subst y. exact (Hnin Hiny).
    + apply IH. exact Hnd'.
Qed.

(* 纯原子窗址换算：奇素 p∈(2,s+1] 落址 k1−1 ∈ seq 0 (S k2) *)
Lemma u5c_win_len_aux : forall p s k1 r1 k2 r2 : nat,
  p = 2 * k1 + r1 -> r1 < 2 -> s = 2 * k2 + r2 -> r2 < 2 ->
  r1 <> 0 -> 3 <= p -> p <= 1 + s ->
  2 * (k1 - 1) + 3 = p /\ 0 <= k1 - 1 /\ k1 - 1 < S k2.
Proof.
  intros p s k1 r1 k2 r2 H1 H2 H3 H4 H5 H6 H7.
  split; [lia | split; lia].
Qed.

(* 窗表长度 ≤ s/2 + 2：参照表 2::map(2k+3)(seq 0 (S (s/2))) *)
Lemma u5c_win_len : forall s : nat, length (pec_win 1 s) <= s / 2 + 2.
Proof.
  intro s.
  assert (Hnd : NoDup (2 :: map (fun k : nat => 2 * k + 3) (seq 0 (S (s / 2))))).
  { constructor.
    - intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy _]]. lia.
    - apply u5c_map_nodup.
      + intros x y Hxy. lia.
      + apply seq_NoDup. }
  assert (Hincl : incl (pec_win 1 s)
                    (2 :: map (fun k : nat => 2 * k + 3) (seq 0 (S (s / 2))))).
  { intros p Hin. destruct (pec_win_in 1 s p Hin) as [Hpp [_ Hple]].
    destruct (Nat.eq_dec p 2) as [E | NE].
    - left. symmetry. exact E.
    - right. apply in_map_iff.
      assert (Hpr2 : pr_prime 2).
      { unfold pr_prime. split; [lia |]. intros d Hd2 Hlt _. lia. }
      assert (Hmod : p mod 2 <> 0).
      { intros H0.
        assert (Hdvd0 : Nat.divide 2 p) by (apply (pr_mod0_dvd 2 p ltac:(lia)); exact H0).
        assert (Hdvd : pec_dvd 2 p).
        { unfold pec_dvd, Nat.divide in Hdvd0. destruct Hdvd0 as [z Hz].
          exists z. rewrite Hz. ring. }
        assert (Heq : 2 = p)
          by (apply (pec_prime_dvd_prime 2 p Hpr2 Hpp Hdvd)).
        lia. }
      pose proof (Nat.div_mod_eq p 2) as Hdm.
      pose proof (Nat.mod_upper_bound p 2 ltac:(lia)) as Hub.
      pose proof (Nat.div_mod_eq s 2) as Hdm2.
      pose proof (Nat.mod_upper_bound s 2 ltac:(lia)) as Hub2.
      assert (Hp3 : 3 <= p).
      { destruct (le_lt_dec 3 p) as [H | H]; [exact H |].
        exfalso.
        assert (Hge : 2 <= p) by (apply u5c_prime_ge2; exact Hpp).
        lia. }
      destruct (u5c_win_len_aux p s (p / 2) (p mod 2) (s / 2) (s mod 2)
                  Hdm Hub Hdm2 Hub2 Hmod Hp3 Hple) as [E1 [E2 E3]].
      exists (p / 2 - 1). split.
      + exact E1.
      + apply in_seq. split; [exact E2 | exact E3]. }
  pose proof (NoDup_incl_length (u5c_win_nodup 1 s) Hincl) as HL.
  pose proof (length_seq (S (s / 2)) 0) as HSL.
  pose proof (length_map (fun k : nat => 2 * k + 3) (seq 0 (S (s / 2)))) as HML.
  cbn [length] in HL. rewrite HML in HL. lia.
Qed.

(* 折叠积-成员分解：x 入表 ⟹ 折叠（带幂映射）＝ f x·W *)
Lemma u5c_fold_in_mul : forall (f : nat -> nat) (l : list nat) (x : nat),
  In x l -> exists W : nat, fold_right Nat.mul 1 (map f l) = f x * W.
Proof.
  intros f l. induction l as [|a l IH]; intros x Hin.
  - destruct Hin.
  - cbn [map fold_right]. destruct Hin as [E | Hin].
    + subst a. exists (fold_right Nat.mul 1 (map f l)). reflexivity.
    + destruct (IH x Hin) as [W HW]. exists (f a * W).
      rewrite HW. ring.
Qed.

(* 折叠积上界：逐项 ≤ B ⟹ 折叠 ≤ B^length *)
Lemma u5c_fold_pow_le : forall (f : nat -> nat) (l : list nat) (B : nat),
  (forall x : nat, In x l -> f x <= B) ->
  fold_right Nat.mul 1 (map f l) <= B ^ length l.
Proof.
  intros f l B. induction l as [|a l IH]; intros Hle.
  - cbn [map fold_right length]. rewrite Nat.pow_0_r. apply Nat.le_refl.
  - cbn [map fold_right length].
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono.
    + apply Hle. left. reflexivity.
    + apply IH. intros x Hx. apply Hle. right. exact Hx.
Qed.

(* 一般指数折叠整除（零指数容许；u5c_combine_pow 逐位合并） *)
Lemma u5c_fold_dvd0 : forall (l : list nat) (e : nat -> nat) (C : nat),
  NoDup l ->
  (forall x : nat, In x l -> pr_prime x) ->
  (forall x : nat, In x l -> pec_dvd (x ^ e x) C) ->
  pec_dvd (fold_right Nat.mul 1 (map (fun x : nat => x ^ e x) l)) C.
Proof.
  intros l. induction l as [|q l IH]; intros e C Hnd Hpr Hpow.
  - exists C. cbn [map fold_right]. rewrite Nat.mul_1_l. reflexivity.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd'].
    assert (Hq : pr_prime q) by (apply Hpr; left; reflexivity).
    assert (Hq2 : 2 <= q) by (apply u5c_prime_ge2; exact Hq).
    assert (Hq1 : 1 <= q).
    { apply (Nat.le_trans 1 2 q); [apply Nat.le_succ_diag_r | exact Hq2]. }
    assert (HP : 1 <= fold_right Nat.mul 1 (map (fun x : nat => x ^ e x) l)).
    { apply pec_prod_ge1. intros y Hy.
      apply in_map_iff in Hy. destruct Hy as [x [Hfx Hinx]].
      rewrite <- Hfx. apply u5c_pow_ge1.
      apply (proj1 (Nat.neq_0_lt_0 _)). apply u5c_prime_ne0.
      apply Hpr. right. exact Hinx. }
    assert (HnP : pec_dvd q (fold_right Nat.mul 1 (map (fun x : nat => x ^ e x) l))
                -> False).
    { intros Hd.
      destruct (pec_prime_dvd_prod_in q (map (fun x : nat => x ^ e x) l) Hq Hd)
        as [y [Hin Hdy]].
      apply in_map_iff in Hin. destruct Hin as [x [Hfx Hinx]].
      assert (Hxp : pr_prime x) by (apply Hpr; right; exact Hinx).
      assert (Hqx : q = x).
      { apply (u5c_dvd_pow_eq x (e x) q).
        - apply u5c_prime_ge2. exact Hxp.
        - exact Hxp.
        - exact Hq.
        - rewrite Hfx. exact Hdy. }
      apply Hnin. rewrite Hqx. exact Hinx. }
    assert (Hpowq : pec_dvd (q ^ e q) C) by (apply Hpow; left; reflexivity).
    assert (Hpowrest : pec_dvd (fold_right Nat.mul 1 (map (fun x : nat => x ^ e x) l)) C)
      by (apply (IH e C); [exact Hnd' | intros x Hx; apply Hpr; right; exact Hx
                 | intros x Hx; apply Hpow; right; exact Hx]).
    destruct (u5c_combine_pow q (e q) (fold_right Nat.mul 1 (map (fun x : nat => x ^ e x) l)) C
                Hq2 Hq HP Hpowq Hpowrest HnP) as [u Hu].
    exists u. cbn [map fold_right]. exact Hu.
Qed.

(* ---- 吸收主机：窗内全指数归 A，窗外素因子归 prim(⌊2n/3⌋) ---- *)

Lemma u5c_absorb_dvd : forall (n s : nat)
    (Hs : 2 * n < (S s) * (S s)) (H4 : 4 <= S s) (Hn1 : 1 <= n)
    (Hneg : forall q : nat, pr_prime q -> n < q -> q <= 2 * n -> False),
  pec_dvd (pec_mid n)
    (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
     * pec_prim ((2 * n) / 3)).
Proof.
  intros n s Hs H4 Hn1 Hneg.
  apply (u5c_cprime_gen (pec_mid n) _).
  - unfold pec_mid. apply pec_binom_pos. lia.
  - intros r v Hr Hdv.
    assert (Hr2 := u5c_prime_ge2 r Hr).
    destruct (le_lt_dec r (S s)) as [Hws | Hgt].
    + assert (Hmem : In r (pec_win 1 s)).
      { pose proof (u5c_win_in_ex (S s) r Hr2 Hws Hr) as Hm0.
        replace (S s - 1) with s in Hm0 by lia. exact Hm0. }
      destruct (u5c_expf_spec r n s Hs H4 Hn1 Hr) as [e [Hef [Heq [Hdvd [Hle Hdef]]]]].
      apply (u5c_dvd_trans (r ^ v) (r ^ e)
              (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
               * pec_prim ((2 * n) / 3))).
      * assert (H02n : 2 * n / r ^ (S s) = 0).
        { apply (u5c_div_eq_zero (r ^ S s) (2 * n)).
          - apply Nat.pow_nonzero. apply u5c_prime_ne0. exact Hr.
          - apply (Nat.lt_le_trans (2 * n) (S s * S s) (r ^ S s)).
            + exact Hs.
            + apply (Nat.le_trans (S s * S s) (2 ^ S s) (r ^ S s)).
              * apply (u5c_pow2_ge_sq (S s) H4).
              * apply Nat.pow_le_mono_l.
                -- exact Hr2. }
        assert (Hve : v <= e)
          by (apply (u5c_master_bound r n s e v Hr Hdv Heq H02n)).
        apply (pec_dvd_of_eq (r ^ v) (r ^ e) (r ^ (e - v))).
        rewrite <- (Nat.pow_add_r r v (e - v)).
        replace (v + (e - v)) with e by lia.
        reflexivity.
      * apply (u5c_dvd_trans (r ^ e)
              (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s)))
              (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
               * pec_prim ((2 * n) / 3))).
        -- destruct (u5c_fold_in_mul (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1)
                       (pec_win 1 s) r Hmem) as [Wp HWp].
           rewrite <- Hef.
           apply (pec_dvd_of_eq (r ^ u5c_expf r n s Hs H4 Hn1) _ Wp).
           exact HWp.
        -- apply (pec_dvd_of_eq _ _ (pec_prim ((2 * n) / 3))). reflexivity.
    + assert (Hsq2 : 2 * n < r * r) by (apply (u5c_gt_sqrt n s r Hs (Nat.lt_trans s (S s) r (Nat.lt_succ_diag_r s) Hgt))).
      destruct (le_lt_dec r ((2 * n) / 3)) as [Hlo3 | Hhi3].
      * destruct v as [|v'].
        -- set (B := fold_right Nat.mul 1
                     (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
                     * pec_prim ((2 * n) / 3)).
           exists B. rewrite Nat.pow_0_r. symmetry. apply Nat.mul_1_l.
        -- destruct v' as [|v''].
           ++ assert (HdC : pec_dvd r (pec_mid n)).
              { destruct Hdv as [z0 Hz0].
                replace (r ^ 1) with r in Hz0
                  by (rewrite Nat.pow_1_r; reflexivity).
                apply (pec_dvd_of_eq r _ z0). exact Hz0. }
              rewrite Nat.pow_1_r. apply pec_dvd_mul_r.
              apply (u5c_prime_dvd_prim ((2 * n) / 3) r Hr2 Hlo3 Hr).
           ++ exfalso.
              destruct Hdv as [z0 Hz0].
              assert (Hsqf : pec_dvd (r * r) (pec_mid n)).
              { apply (u5c_dvd_trans (r * r) (r ^ S (S v'')) (pec_mid n)).
                { replace (r ^ S (S v'')) with (r * r * r ^ v'')
                    by (rewrite !Nat.pow_succ_r'; ring).
                  exists (r ^ v''). ring. }
                { exists z0. exact Hz0. } }
              apply (u5c_mid_not_sq r n Hr2 Hr).
              { apply (Nat.le_trans r ((2 * n) / 3) (2 * n));
                  [exact Hlo3 | apply u5c_div3_le]. }
              { exact Hsq2. }
              { exact Hsqf. }
      * destruct (le_lt_dec r n) as [Hlen | Hgtn].
        -- destruct v as [|v'].
           ++ set (B := fold_right Nat.mul 1
                        (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
                        * pec_prim ((2 * n) / 3)).
              exists B. rewrite Nat.pow_0_r. symmetry. apply Nat.mul_1_l.
           ++ exfalso. apply (u5c_mid_no_dvd r n Hr2 Hr Hlen).
              { apply (u5c_gt_div3 n r Hhi3). }
              { exact Hsq2. }
              { apply (u5c_dvd_trans r (r ^ S v') (pec_mid n)).
                - apply (pec_dvd_of_eq r (r ^ S v') (r ^ v')).
                  rewrite Nat.pow_succ_r'. reflexivity.
                - exact Hdv. }
        -- destruct v as [|v'].
           ++ set (B := fold_right Nat.mul 1
                        (map (fun p : nat => p ^ u5c_expf p n s Hs H4 Hn1) (pec_win 1 s))
                        * pec_prim ((2 * n) / 3)).
              exists B. rewrite Nat.pow_0_r. symmetry. apply Nat.mul_1_l.
           ++ exfalso.
            assert (HdC : pec_dvd r (pec_mid n)).
            { apply (u5c_dvd_trans r (r ^ S v') (pec_mid n)).
              - apply (pec_dvd_of_eq r (r ^ S v') (r ^ v')).
                rewrite Nat.pow_succ_r'. reflexivity.
              - exact Hdv. }
            assert (Hdfact : pec_dvd r (fact (2 * n))).
            { destruct HdC as [z0 Hz0].
              apply (pec_dvd_of_eq r _ (z0 * (fact n * fact n))).
              rewrite <- pec_mid_fact_eq. rewrite Hz0. ring. }
            assert (Hr2n : r <= 2 * n).
            { destruct (le_lt_dec r (2 * n)) as [Hle2 | Hgt2]; [exact Hle2 |].
              exfalso. apply (pec_prime_not_dvd_fact r (2 * n) Hr Hgt2).
              exact Hdfact. }
            apply (Hneg r Hr Hgtn Hr2n).
Qed.

(* ---- 反证主机与终局定理 ---- *)

Lemma u5c_no_prime_contra : forall n : nat, 512 <= n ->
  (forall q : nat, pr_prime q -> n < q -> q <= 2 * n -> False) -> False.
Proof.
  intros n Hn Hneg.
  destruct (u5c_sqrt_ex (2 * n)) as [s [Hs1 Hs2]].
  assert (Hs4 : 4 <= S s).
  { assert (H32 : 32 <= S s).
    { destruct (le_lt_dec 32 (S s)) as [H | H]; [exact H |].
      exfalso. assert (Hc : (S s) * (S s) <= 32 * 32)
        by (apply Nat.mul_le_mono; lia).
      lia. }
    lia. }
  assert (Hn1 : 1 <= n) by (apply (Nat.le_trans 1 512 n); [exact u5c_le_1_512 | exact Hn]).
  assert (Hnne0 : n <> 0) by (intro E; rewrite E in Hn; inversion Hn).
  assert (H2npos : 0 < 2 * n).
  { apply (Nat.lt_le_trans 0 1 (2 * n)); [apply Nat.lt_0_1 |].
    apply (Nat.le_trans 1 2 (2 * n)).
    - apply Nat.le_succ_diag_r.
    - apply u5c_le_mul_id. exact Hn1. }
  pose proof (u5c_spine n s Hn Hs1 Hs2) as Hsp.
  assert (Hdvd : pec_dvd (pec_mid n)
    (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
     * pec_prim ((2 * n) / 3))) by (apply (u5c_absorb_dvd n s Hs2 Hs4 Hn1 Hneg)).
  assert (HA : fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
             <= (2 * n) ^ (s / 2 + 2)).
  { apply Nat.le_trans with ((2 * n) ^ length (pec_win 1 s)).
    - apply (u5c_fold_pow_le (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1)
               (pec_win 1 s) (2 * n)).
      intros x Hx.
      destruct (pec_win_in 1 s x Hx) as [Hxp _].
      destruct (u5c_expf_spec x n s Hs2 Hs4 Hn1 Hxp) as [e [Hef [_ [_ [Hle _]]]]].
      rewrite Hef. exact Hle.
    - apply Nat.pow_le_mono_r.
      + apply (proj2 (Nat.neq_0_lt_0 _)). exact H2npos.
      + apply (Nat.le_trans (length (pec_win 1 s)) (s / 2 + 2));
          [apply u5c_win_len | apply Nat.le_refl]. }
  assert (H1A : 1 <= fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))).
  { apply pec_prod_ge1. intros y Hy.
    apply in_map_iff in Hy. destruct Hy as [x [Hfx Hinx]].
    rewrite <- Hfx. apply u5c_pow_ge1.
    apply (proj1 (Nat.neq_0_lt_0 _)). apply u5c_prime_ne0.
    destruct (pec_win_in 1 s x Hinx) as [Hxp _]. exact Hxp. }
  assert (H3 : 1 <= fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
                 * pec_prim ((2 * n) / 3)).
  { apply (Nat.le_trans 1 (1 * pec_prim ((2 * n) / 3))
             (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
              * pec_prim ((2 * n) / 3))).
    - rewrite Nat.mul_1_l. apply u5c_prim_ge1.
    - apply Nat.mul_le_mono; [exact H1A | apply Nat.le_refl]. }
  assert (Hle : pec_mid n <= fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
                  * pec_prim ((2 * n) / 3))
    by (apply (u5c_dvd_le _ _ H3 Hdvd)).
  assert (Hlow : 4 ^ n <= pec_mid n * (2 * n + 1)) by (apply u5c_mid_lower).
  assert (Hpos4F : 0 < 4 ^ ((2 * n) / 3)).
  { apply (proj1 (Nat.neq_0_lt_0 _)). apply Nat.pow_nonzero.
    intro Hc; discriminate Hc. }
  apply (Nat.lt_irrefl (4 ^ n)).
  apply (Nat.lt_le_trans (4 ^ n) (4 ^ (n / 3 + (2 * n) / 3)) (4 ^ n)).
  - apply (Nat.le_lt_trans (4 ^ n)
             ((2 * n + 1) * ((2 * n) ^ (s / 2 + 2) * 4 ^ ((2 * n) / 3)))
             (4 ^ (n / 3 + (2 * n) / 3))).
    + apply (Nat.le_trans (4 ^ n)
               ((2 * n + 1) * (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
                               * pec_prim ((2 * n) / 3)))
               ((2 * n + 1) * ((2 * n) ^ (s / 2 + 2) * 4 ^ ((2 * n) / 3)))).
      * apply (Nat.le_trans (4 ^ n) (pec_mid n * (2 * n + 1))
                 ((2 * n + 1) * (fold_right Nat.mul 1 (map (fun p : nat => p ^ u5c_expf p n s Hs2 Hs4 Hn1) (pec_win 1 s))
                                 * pec_prim ((2 * n) / 3)))).
        -- exact Hlow.
        -- rewrite (Nat.mul_comm (pec_mid n) (2 * n + 1)).
           apply Nat.mul_le_mono_l. exact Hle.
      * apply Nat.mul_le_mono_l. apply Nat.mul_le_mono; [exact HA |].
        apply u5c_prim_le_pow4. apply u5c_prim3_ge1. exact Hn.
    + rewrite (Nat.pow_add_r 4 (n / 3) ((2 * n) / 3)).
      replace ((2 * n + 1) * ((2 * n) ^ (s / 2 + 2) * 4 ^ ((2 * n) / 3)))
        with (((2 * n + 1) * (2 * n) ^ (s / 2 + 2)) * 4 ^ ((2 * n) / 3)) by ring.
      apply (proj1 (Nat.mul_lt_mono_pos_r _ _ _ Hpos4F)).
      exact Hsp.
  - apply Nat.pow_le_mono_r.
    + intro Hc; discriminate Hc.
    + apply u5c_third_sum.
Qed.

(* 终局定理：∀n≥2，(n,2n] 内存在素数（sigT 见证，Defined）
   n ≤ 512 拼 pbr_bertrand_table；n ≥ 512 走 pbr_scan 解析 + 反证主机 *)
Theorem u5c_bertrand_full : forall n : nat, 2 <= n ->
  { p : nat & n < p /\ pr_prime p /\ p <= 2 * n }.
Proof.
  intros n H2.
  destruct (pbr_scan n n) as [p | Hnone] eqn:E.
  - destruct (pbr_scan_some n n p E) as [Hlt [Hle Hpr]].
    exists p. split; [exact Hlt | split; [exact Hpr | lia]].
  - destruct (le_lt_dec 512 n) as [Hbig | Hsmall].
    + exfalso. apply (u5c_no_prime_contra n Hbig).
      intros q Hq Hn1 Hn2.
      destruct (pbr_scan_hit n n q Hn1 ltac:(lia) Hq) as [p' Hp'].
      rewrite E in Hp'. discriminate Hp'.
    + exact (pbr_bertrand_table n H2 ltac:(unfold pbr_N; lia)).
Defined.

Print Assumptions u5c_base.
Print Assumptions u5c_spine.
Print Assumptions u5c_expf_spec.
Print Assumptions u5c_absorb_dvd.
Print Assumptions u5c_no_prime_contra.
Print Assumptions u5c_bertrand_full.
