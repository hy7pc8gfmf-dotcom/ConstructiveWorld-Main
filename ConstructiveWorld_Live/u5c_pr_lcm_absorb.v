(* ============================================================ *)
(* u5c_pr_lcm_absorb.v —— lcm(1..n) 的 p-adic 赋值特征面＋逐素幂环带吸收步 *)
(* 模块名：u5c_pr_lcm_absorb                                      *)
(* 数学使命：Hanson 1972 路线基建——lcm(1..n) 赋值特征与 L(2m) 分裂的逐素幂吸收步。 *)
(*   主件 A（Set 面）：plw_v_lcm_upto_id——素 p 的 L(n) 赋值等于「不超过 n 的最大 p 幂指数」 *)
(*     （plw_maxpow 爬攀机），即 Hanson 分解 L(n)=Π_{p≤n} p^{max{w:p^w≤n}} 的赋值特征面； *)
(*     两侧皆一阶 nat 可计算，hl_id Set 面承载（abl_Pr_lcm_eq 指数位为自指形，本件升为显式形）。 *)
(*     A'（Prop spec）：plw_pow_dvd_lcm_iff——p^w∣L(n) ⟺ p^w≤n（p 素，1≤n）。 *)
(*   主件 B（逐素幂环带吸收步）：plw_annulus_pow_dvd——素幂 p^w 落于环带 (m,2m] ⟹ *)
(*     p^w ∣ C(2m,m)·L(m)·p：w=1（素数位）由免 Legendre 的素环带计数闭合（p>m ⟹ p∤m!， *)
(*     plm_gauss 吸收入二项式）；w≥2（素数幂位）由 p^{w-1}≤m 的幂预算吸收入 L(m)。 *)
(*     此即 L(2m)∣C(2m,m)·L(m) 的逐素幂形式。B'（逐素点态形）：plw_lcm2m_v_le_carry—— *)
(*     v_p(L(2m)) ≤ v_p(C(2m,m)·L(m)·p)。 *)
(*   诚实边界：3^n（Hanson 档）本件未闭合——半程分裂链 L(n)∣C(n,⌊n/2⌋)·L(⌈n/2⌉) 配 C(2m,m)≤4^m *)
(*     的链式上限为 4^n（Nagell 档），距 3^n 差 (4/3)^{n/2}，二项式链式容器不可达 3^n； *)
(*     3^n 需全素幂 Kummer/Legendre 计数（v_p(C(2m,m)) 的 ⌊2m/p^j⌋−2⌊m/p^j⌋ 逐层结构）。 *)
(*     升级方向：主件 B 的跨素合并（枚举表＋相异位互素合并）得 L(2m)∣C(2m,m)·L(m)，再接 Hanson ψ 分解。 *)
(* 依赖清单：HansonLcm（hl_id/hl_le_t/hl_lcm_upto/hl_lcm_divide_all/hl_binom）＋Hanson3Pow *)
(*   （h3_prod_from/h3_prod_divide/h3_prod_binom_fact）＋abl_Pr_core_01（pr_prime）＋ *)
(*   abl_Pr_lcmdecomp_04（plm_v/plm_v_dvd/plm_v_max/plm_gauss/plm_prime_dvd_mul）＋纯 Stdlib（Arith.Arith/Lia）。 *)
(* 构造性注记：Set 面承载——主件 A 为两 nat 闭式之 hl_id（Set 值等式归纳型）；plw_maxpow 为 *)
(*   一阶 nat Fixpoint 可提取；Prop 面谓词仅推理脚手架；否定面全走 -> False 形（全件零否定记号书写，含证明内部）； *)
(*   零公理零承认零经典逻辑；主定理收尾零 solver（lia 仅限支撑算术位）；数值定装走小实例 vm_compute。 *)
(* 编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh && unset COQLIB ROCQLIB && *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler no -q -Q . "" u5c_pr_lcm_absorb.v *)
(*   （依赖件 vo 经 -Q 映射挂源根，只读引用） *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ---- §0 零星元件 ---- *)

(* 幂单调整除：e ≤ f ⟹ p^e ∣ p^f（1 ≤ p） *)
Lemma plw_pow_le_dvd : forall p e f : nat,
  1 <= p -> e <= f -> Nat.divide (p ^ e) (p ^ f).
Proof.
  intros p e f Hp Hef. exists (p ^ (f - e)).
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

(* 乘积整除双乘：a∣b ⟹ c∣d ⟹ a·c∣b·d *)
Lemma plw_dvd_mul_mono : forall a b c d : nat,
  Nat.divide a b -> Nat.divide c d -> Nat.divide (a * c) (b * d).
Proof.
  intros a b c d [q Hq] [r Hr]. exists (q * r).
  rewrite Hq, Hr. ring.
Qed.

(* 乘法左消去（stdlib Nat.mul_cancel_l IFF 包装） *)
Lemma plw_mul_cancel_l : forall a x y : nat,
  a <> 0 -> a * x = a * y -> x = y.
Proof. intros a x y Ha H. exact (proj1 (Nat.mul_cancel_l x y a Ha) H). Qed.

(* 幂非零正座：1 ≤ p ⟹ 1 ≤ p^e *)
Lemma plw_pow_pos : forall p e : nat,
  1 <= p -> 1 <= p ^ e.
Proof.
  intros p e Hp.
  apply Nat.neq_0_lt_0. intro Hz.
  assert (Hpnz : p <> 0) by lia.
  pose proof (Nat.pow_nonzero p e Hpnz).
  lia.
Qed.

(* 幂严格单调（反向座）：e < f ⟹ p^e < p^f（2 ≤ p）——经
   Nat.pow_le_mono_r 步进座闭合，免依赖 pow_lt_mono_r 签名 *)
Lemma plw_pow_lt_mono : forall p e f : nat,
  2 <= p -> e < f -> p ^ e < p ^ f.
Proof.
  intros p e f Hp Hlt.
  assert (Hs : S e <= f) by lia.
  assert (Hle : p ^ S e <= p ^ f)
    by (apply Nat.pow_le_mono_r; lia).
  rewrite Nat.pow_succ_r' in Hle.
  assert (H1 : 1 <= p ^ e) by (apply plw_pow_pos; lia).
  assert (Hstep : 2 * p ^ e <= p * p ^ e)
    by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

(* ---- §1 赋值特征核：plm_v 的完整刻画 ---- *)

(* 赋值上界肢：e ≤ plm_v p k ⟹ p^e ∣ k（由 plm_v_dvd 幂缩减） *)
Lemma plw_v_dvd_le : forall p k e : nat,
  1 <= p ->
  Nat.divide (p ^ plm_v p k) k -> e <= plm_v p k ->
  Nat.divide (p ^ e) k.
Proof.
  intros p k e Hp Hd Hle.
  apply (Nat.divide_trans (p ^ e) (p ^ plm_v p k) k).
  - apply plw_pow_le_dvd; lia.
  - exact Hd.
Qed.

(* 赋值下界肢：p^e ∣ k ∧ 1 ≤ k ∧ 1 < p ⟹ e ≤ plm_v p k
   （超界幂 p^{S v}∣p^e∣k 破 plm_v 最大性） *)
Lemma plw_v_le_dvd : forall p k e : nat,
  1 < p -> 1 <= k -> Nat.divide (p ^ e) k -> e <= plm_v p k.
Proof.
  intros p k e Hp Hk Hd.
  destruct (le_lt_dec e (plm_v p k)) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    apply (plm_v_max p k Hp Hk).
    apply (Nat.divide_trans (p ^ S (plm_v p k)) (p ^ e) k).
    + apply plw_pow_le_dvd; lia.
    + exact Hd.
Qed.

(* 赋值特征（⟺，1 ≤ k）：p^e ∣ k ⟺ e ≤ plm_v p k *)
Lemma plw_v_char : forall p k e : nat,
  1 < p -> 1 <= k ->
  Nat.divide (p ^ e) k <-> e <= plm_v p k.
Proof.
  intros p k e Hp Hk. split.
  - intro Hd. exact (plw_v_le_dvd p k e Hp Hk Hd).
  - intro Hle. apply (plw_v_dvd_le p k e).
    + lia.
    + apply plm_v_dvd.
    + exact Hle.
Qed.

(* 素底赋值定点：plm_v p (p^e) = e（1 < p）
   ≤ 肢：p^v∣p^e ⟹ p^v≤p^e ⟹ v≤e；≥ 肢：v<e ⟹ p^{S v}∣p^e 破最大性 *)
Lemma plw_pow_v_eq : forall p e : nat,
  1 < p -> plm_v p (p ^ e) = e.
Proof.
  intros p e Hp.
  assert (Hk : 1 <= p ^ e) by (apply plw_pow_pos; lia).
  apply Nat.le_antisymm.
  - assert (Hdvd : Nat.divide (p ^ plm_v p (p ^ e)) (p ^ e))
      by apply plm_v_dvd.
    assert (Hle : p ^ plm_v p (p ^ e) <= p ^ e)
      by (apply Nat.divide_pos_le; [lia | exact Hdvd]).
    destruct (le_lt_dec (plm_v p (p ^ e)) e) as [| Hlt].
    + lia.
    + exfalso.
      assert (Hlt2 : p ^ e < p ^ plm_v p (p ^ e))
        by (apply (plw_pow_lt_mono p e (plm_v p (p ^ e))); [lia | lia]).
      lia.
  - destruct (le_lt_dec e (plm_v p (p ^ e))) as [| Hlt].
    + lia.
    + exfalso.
      apply (plm_v_max p (p ^ e) Hp Hk).
      apply (plw_pow_le_dvd p (S (plm_v p (p ^ e))) e); lia.
Qed.

(* ---- §2 乘积/gcd/lcm 赋值核（素底） ---- *)

(* 尾因子无素性：a = p^v·a' ∧ p^{S v}∤a ⟹ p∤a' *)
Lemma plw_tail_nop : forall p v a t : nat,
  1 < p -> a = p ^ v * t ->
  (Nat.divide (p ^ S v) a -> False) ->
  (Nat.divide p t -> False).
Proof.
  intros p v a t Hp Ha Hceil [u Hu].
  apply Hceil. exists u. rewrite Ha, Hu.
  rewrite Nat.pow_succ_r'. ring.
Qed.

(* 乘积赋值：plm_v p (a·b) = plm_v p a + plm_v p b（p 素，a,b≥1） *)
Lemma plw_v_mul : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (a * b) = plm_v p a + plm_v p b.
Proof.
  intros p a b Hpp Ha Hb.
  destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  assert (Hab : 1 <= a * b) by (apply (Nat.mul_le_mono 1 a 1 b); lia).
  apply Nat.le_antisymm.
  - (* ≤：p^{v_ab}∣ab，剥 p^{va}·p^{vb} 后余部无 p，若 v_ab 超和则
       p∣余部 经素分解破 a 或 b 的最大性 *)
    assert (Hd : Nat.divide (p ^ plm_v p (a * b)) (a * b))
      by apply plm_v_dvd.
    destruct Hd as [q Hq].
    destruct (plm_v_dvd p a) as [a' Ha'].
    destruct (plm_v_dvd p b) as [b' Hb'].
    assert (Ha'f : a = p ^ plm_v p a * a') by (rewrite Ha' at 1; ring).
    assert (Hb'f : b = p ^ plm_v p b * b') by (rewrite Hb' at 1; ring).
    assert (Hta : Nat.divide p a' -> False).
    { apply (plw_tail_nop p (plm_v p a) a a'); [lia | exact Ha'f |].
      intro Hd2. exact (plm_v_max p a Hp1 Ha Hd2). }
    assert (Htb : Nat.divide p b' -> False).
    { apply (plw_tail_nop p (plm_v p b) b b'); [lia | exact Hb'f |].
      intro Hd2. exact (plm_v_max p b Hp1 Hb Hd2). }
    destruct (le_lt_dec (plm_v p (a * b))
                (plm_v p a + plm_v p b)) as [| Hlt].
    + lia.
    + exfalso.
      (* p^{S(va+vb)} ∣ ab（v_ab ≥ S(va+vb) 传递） *)
      assert (Hdd : Nat.divide (p ^ S (plm_v p a + plm_v p b)) (a * b)).
      { apply (Nat.divide_trans (p ^ S (plm_v p a + plm_v p b))
                  (p ^ plm_v p (a * b)) (a * b)).
        - apply plw_pow_le_dvd; lia.
        - apply plm_v_dvd. }
      destruct Hdd as [u Hu].
      (* 剥幂方程：p^{va+vb}·(a'·b') = p^{S(va+vb)}·u ⟹ 消去 ⟹ p∣a'·b' *)
      assert (Hab2 : a * b
                     = p ^ (plm_v p a + plm_v p b) * (a' * b')).
      { rewrite Ha' at 1. rewrite Hb' at 1. rewrite Nat.pow_add_r. ring. }
      assert (Hq2 : p ^ (plm_v p a + plm_v p b) * (a' * b')
                    = p ^ (plm_v p a + plm_v p b) * (p * u)).
      { rewrite <- Hab2, Hu, Nat.pow_succ_r'. ring. }
      assert (Hcancel : a' * b' = p * u).
      { apply (plw_mul_cancel_l (p ^ (plm_v p a + plm_v p b))
                 (a' * b') (p * u)).
        - pose proof (plw_pow_pos p (plm_v p a + plm_v p b) ltac:(lia)).
          lia.
        - exact Hq2. }
      assert (Hdv : Nat.divide p (a' * b')).
      { exists u. rewrite Hcancel. ring. }
      destruct (plm_prime_dvd_mul p a' b' (conj Hp2 Hpd) Hdv)
        as [Hda | Hdb].
      * exact (Hta Hda).
      * exact (Htb Hdb).
  - (* ≥：p^{va}∣a, p^{vb}∣b ⟹ p^{va+vb}∣ab *)
    apply (plw_v_le_dvd p (a * b) (plm_v p a + plm_v p b) Hp1 Hab).
    rewrite Nat.pow_add_r.
    apply (plw_dvd_mul_mono (p ^ plm_v p a) a (p ^ plm_v p b) b).
    + apply plm_v_dvd.
    + apply plm_v_dvd.
Qed.

(* gcd 赋值：plm_v p (gcd a b) = min（p 素，a,b≥1） *)
Lemma plw_v_gcd : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (Nat.gcd a b) = Nat.min (plm_v p a) (plm_v p b).
Proof.
  intros p a b Hpp Ha Hb. destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  assert (Hga : 1 <= Nat.gcd a b).
  { apply Nat.neq_0_lt_0. intro Hz.
    assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
    rewrite Hz in Hd. apply Nat.divide_0_l in Hd. lia. }
  apply Nat.le_antisymm.
  - assert (H1 : plm_v p (Nat.gcd a b) <= plm_v p a).
    { apply (plw_v_le_dvd p a (plm_v p (Nat.gcd a b)) Hp1 Ha).
      apply (Nat.divide_trans (p ^ plm_v p (Nat.gcd a b))
                (Nat.gcd a b) a).
      + apply plm_v_dvd.
      + apply Nat.gcd_divide_l. }
    assert (H2 : plm_v p (Nat.gcd a b) <= plm_v p b).
    { apply (plw_v_le_dvd p b (plm_v p (Nat.gcd a b)) Hp1 Hb).
      apply (Nat.divide_trans (p ^ plm_v p (Nat.gcd a b))
                (Nat.gcd a b) b).
      + apply plm_v_dvd.
      + apply Nat.gcd_divide_r. }
    lia.
  - apply (plw_v_le_dvd p (Nat.gcd a b)
             (Nat.min (plm_v p a) (plm_v p b)) Hp1 Hga).
    apply Nat.gcd_greatest.
    + apply (plw_v_dvd_le p a (Nat.min (plm_v p a) (plm_v p b))).
      * lia.
      * apply plm_v_dvd.
      * apply Nat.le_min_l.
    + apply (plw_v_dvd_le p b (Nat.min (plm_v p a) (plm_v p b))).
      * lia.
      * apply plm_v_dvd.
      * apply Nat.le_min_r.
Qed.

(* lcm·gcd = a·b（stdlib lcm 展开形 a·(b/gcd) 直算，含零边） *)
Lemma plw_lcm_gcd_mul : forall a b : nat,
  Nat.lcm a b * Nat.gcd a b = a * b.
Proof.
  intros a b.
  unfold Nat.lcm.
  destruct (Nat.eq_dec (Nat.gcd a b) 0) as [Ez | Nz].
  - assert (Ha : a = 0).
    { assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
      rewrite Ez in Hd. apply Nat.divide_0_l in Hd. exact Hd. }
    assert (Hb : b = 0).
    { assert (Hd : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      rewrite Ez in Hd. apply Nat.divide_0_l in Hd. exact Hd. }
    rewrite Ez, Ha, Hb. reflexivity.
  - assert (Hb0 : b = Nat.gcd a b * (b / Nat.gcd a b)).
    { pose proof (Nat.div_mod_eq b (Nat.gcd a b)) as Hdm.
      assert (Hm0 : b mod Nat.gcd a b = 0).
      { apply (proj2 (Nat.mod_divide b (Nat.gcd a b) Nz)).
        apply Nat.gcd_divide_r. }
      rewrite Hm0, Nat.add_0_r in Hdm. exact Hdm. }
    rewrite <- (Nat.mul_assoc a (b / Nat.gcd a b) (Nat.gcd a b)).
    rewrite (Nat.mul_comm (b / Nat.gcd a b) (Nat.gcd a b)).
    rewrite <- Hb0. reflexivity.
Qed.

(* lcm 正性（1 ≤ a,b）：经 lcm·gcd = a·b 反证 *)
Lemma plw_lcm_pos_gen : forall a b : nat,
  1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb.
  assert (Hab : 1 <= a * b) by (apply (Nat.mul_le_mono 1 a 1 b); lia).
  apply Nat.neq_0_lt_0. intro Hz.
  pose proof (plw_lcm_gcd_mul a b) as Hmul.
  rewrite Hz, Nat.mul_0_l in Hmul.
  lia.
Qed.

(* lcm 赋值：plm_v p (lcm a b) = max（p 素，a,b≥1）
   经 lcm·gcd=a·b 方程：v(lcm)+v(gcd)=v(a)+v(b)，gcd=min ⟹ lcm=max *)
Lemma plw_v_lcm : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (Nat.lcm a b) = Nat.max (plm_v p a) (plm_v p b).
Proof.
  intros p a b Hpp Ha Hb. destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  assert (Hg1 : 1 <= Nat.gcd a b).
  { apply Nat.neq_0_lt_0. intro Hz.
    assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
    rewrite Hz in Hd. apply Nat.divide_0_l in Hd. lia. }
  assert (Hl1 : 1 <= Nat.lcm a b)
    by (apply plw_lcm_pos_gen; assumption).
  assert (Hvl : plm_v p (Nat.lcm a b) + plm_v p (Nat.gcd a b)
                = plm_v p a + plm_v p b).
  { rewrite <- (plw_v_mul p (Nat.lcm a b) (Nat.gcd a b) (conj Hp2 Hpd)
                  Hl1 Hg1).
    rewrite (plw_lcm_gcd_mul a b).
    apply (plw_v_mul p a b (conj Hp2 Hpd) Ha Hb). }
  rewrite (plw_v_gcd p a b (conj Hp2 Hpd) Ha Hb) in Hvl.
  lia.
Qed.

(* ---- §3 主件 A：L(n) 的 p-adic 赋值特征（Hanson 分解赋值面） ---- *)

(* lcm 折叠正性：1 ≤ L(n)（lcm=a·(b/g) 展开形归纳） *)
Lemma plw_lcm_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto].
    apply plw_lcm_pos_gen; [exact IH | lia].
Qed.

(* 折叠步赋值：v_p(L(S n)) = max(v_p(L n), v_p(S n))（p 素） *)
Lemma plw_v_lcm_upto_S : forall p n : nat,
  pr_prime p ->
  plm_v p (hl_lcm_upto (S n))
  = Nat.max (plm_v p (hl_lcm_upto n)) (plm_v p (S n)).
Proof.
  intros p n Hpp. cbn [hl_lcm_upto].
  apply (plw_v_lcm p (hl_lcm_upto n) (S n) Hpp).
  - apply plw_lcm_pos.
  - lia.
Qed.

(* 【主件 A'】L 的整除特征：p^w ∣ L(n) ⟺ p^w ≤ n（p 素，1≤n）。
   ⟸：hl_lcm_divide_all（p^w 本身是 1..n 成员）；⟹：归纳，步位
   w ≤ max(v(L m), v(S m)) 分半——w≤v(L m) 回归纳，w≤v(S m) 直出。 *)
Lemma plw_pow_dvd_lcm_iff : forall p n w : nat,
  pr_prime p -> 1 <= n ->
  Nat.divide (p ^ w) (hl_lcm_upto n) <-> p ^ w <= n.
Proof.
  intros p n. induction n as [| m IH]; intros w Hpp Hn.
  - exfalso. lia.
  - destruct Hpp as [Hp2 Hpd].
    assert (Hp1 : 1 < p) by lia.
    assert (Hpw : 1 <= p ^ w) by (apply plw_pow_pos; lia).
    split.
    + intro Hd.
      apply (plw_v_le_dvd p (hl_lcm_upto (S m)) w Hp1
               (plw_lcm_pos (S m))) in Hd.
      assert (Hdmax : w <= Nat.max (plm_v p (hl_lcm_upto m))
                        (plm_v p (S m))).
      { rewrite <- (plw_v_lcm_upto_S p m (conj Hp2 Hpd)). exact Hd. }
      destruct (le_lt_dec w (plm_v p (hl_lcm_upto m))) as [Hc | Hc].
      * (* w ≤ v(L m)：回归纳 *)
        assert (Hdm : Nat.divide (p ^ w) (hl_lcm_upto m))
          by (apply (plw_v_dvd_le p (hl_lcm_upto m) w);
              [lia | apply plm_v_dvd | exact Hc]).
        destruct m as [| m'].
        -- simpl in Hdm.
           apply Nat.divide_1_r in Hdm.
           rewrite Hdm. lia.
        -- pose proof (proj1 (IH w (conj Hp2 Hpd) ltac:(lia)) Hdm) as Hle.
           lia.
      * (* w ≤ v(S m)：p^w∣S m 直出 *)
        assert (Hds : Nat.divide (p ^ w) (S m))
          by (apply (plw_v_dvd_le p (S m) w);
              [lia | apply plm_v_dvd | lia]).
        apply Nat.divide_pos_le; [lia | exact Hds].
    + intro Hle.
      apply (hl_lcm_divide_all (S m) (p ^ w)); [exact Hpw | exact Hle].
Qed.

(* maxpow 爬攀机：不超过 n 的最大 p 幂指数（一阶 nat Fixpoint，
   界 n 保险：p^w≤n ⟹ w≤n；结构与 plm_vmax 同型） *)
Fixpoint plw_maxpow (p n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
           then S (plw_maxpow p m)
           else plw_maxpow p m
  end.

(* maxpow 肢一：p^{maxpow p n} ≤ n 或 n=0 *)
Lemma plw_maxpow_dvd_upto : forall p n : nat,
  p ^ plw_maxpow p n <= n \/ n = 0.
Proof.
  intros p n. induction n as [| m IH].
  - right. reflexivity.
  - change (plw_maxpow p (S m))
      with (if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
            then S (plw_maxpow p m) else plw_maxpow p m).
    destruct (Nat.leb (p ^ S (plw_maxpow p m)) (S m)) eqn:Eb.
    + left. apply Nat.leb_le in Eb. exact Eb.
    + apply Nat.leb_gt in Eb.
      destruct IH as [Hle | Hm0].
      * change (if false then S (plw_maxpow p m)
                else plw_maxpow p m)
          with (plw_maxpow p m).
        left. lia.
      * subst m. change (plw_maxpow p 0) with 0.
        change (if false then S 0 else 0) with 0.
        rewrite Nat.pow_0_r. left. lia.
Qed.

(* maxpow 肢二：n < p^{S(maxpow p n)}（1<p，登攀不越顶） *)
Lemma plw_maxpow_ceil : forall p n : nat,
  1 < p -> n < p ^ S (plw_maxpow p n).
Proof.
  intros p n Hp. induction n as [| m IH].
  - cbn [plw_maxpow]. rewrite Nat.pow_succ_r', Nat.pow_0_r. lia.
  - change (plw_maxpow p (S m))
      with (if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
            then S (plw_maxpow p m) else plw_maxpow p m).
    destruct (Nat.leb (p ^ S (plw_maxpow p m)) (S m)) eqn:Eb.
    + apply Nat.leb_le in Eb.
      change (if true then S (plw_maxpow p m) else plw_maxpow p m)
        with (S (plw_maxpow p m)).
      assert (Hsm : m < p ^ S (plw_maxpow p m)) by exact IH.
      assert (Hge : p ^ S (plw_maxpow p m) * 2
                    <= p ^ S (plw_maxpow p m) * p)
        by (apply Nat.mul_le_mono_l; lia).
      assert (Hstep : p ^ S (S (plw_maxpow p m))
                      = p ^ S (plw_maxpow p m) * p)
        by (rewrite Nat.pow_succ_r'; ring).
      rewrite Hstep. lia.
    + apply Nat.leb_gt in Eb. exact Eb.
Qed.

(* 特征装配：v_p(L(n)) = maxpow p n（p 素）
   n=0 双零直合；n≥1 经 iff 唯一性双 antisymm，幂严格单调两侧夹逼 *)
Lemma plw_v_lcm_upto : forall p n : nat,
  pr_prime p -> plm_v p (hl_lcm_upto n) = plw_maxpow p n.
Proof.
  intros p n Hpp. destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  assert (Hpos : 1 <= hl_lcm_upto n) by apply plw_lcm_pos.
  destruct n as [| m].
  - cbn [hl_lcm_upto plw_maxpow].
    assert (Hv : plm_v p 1 = 0).
    { destruct (plm_v p 1) as [| v'] eqn:Ev.
      - reflexivity.
      - exfalso.
        destruct (plm_v_dvd p 1) as [t Ht].
        rewrite Ev in Ht.
        assert (Hge : 2 <= p ^ S v')
          by (apply Nat.le_trans with (p ^ 1);
              [rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia]).
        assert (Hle : p ^ S v' <= 1)
          by (apply Nat.divide_pos_le;
              [lia | exact (ex_intro _ t Ht)]).
        lia. }
    rewrite Hv. reflexivity.
  - assert (Hn : 1 <= S m) by lia.
    pose proof (plw_maxpow_dvd_upto p (S m)) as Hdu.
    destruct Hdu as [Hdu | Hm0].
    2:{ exfalso. lia. }
    pose proof (plw_maxpow_ceil p (S m) Hp1) as Hcl.
    assert (Hvd : p ^ plm_v p (hl_lcm_upto (S m)) <= S m).
    { apply (proj1 (plw_pow_dvd_lcm_iff p (S m)
                    (plm_v p (hl_lcm_upto (S m))) (conj Hp2 Hpd) Hn)).
      apply plm_v_dvd. }
    assert (Hvc : p ^ S (plm_v p (hl_lcm_upto (S m))) <= S m -> False).
    { intro Hle2.
      apply (plm_v_max p (hl_lcm_upto (S m)) Hp1 Hpos).
      exact (proj2 (plw_pow_dvd_lcm_iff p (S m)
              (S (plm_v p (hl_lcm_upto (S m)))) (conj Hp2 Hpd) Hn) Hle2). }
    apply Nat.le_antisymm.
    + destruct (le_lt_dec (plm_v p (hl_lcm_upto (S m)))
                  (plw_maxpow p (S m))) as [Hle3 | Hgt].
      * exact Hle3.
      * exfalso.
        assert (Hmono : p ^ S (plw_maxpow p (S m))
                        <= p ^ plm_v p (hl_lcm_upto (S m)))
          by (apply Nat.pow_le_mono_r; lia).
        lia.
    + destruct (le_lt_dec (plw_maxpow p (S m))
                  (plm_v p (hl_lcm_upto (S m)))) as [Hle3 | Hgt].
      * exact Hle3.
      * exfalso.
        assert (Hmono : p ^ S (plm_v p (hl_lcm_upto (S m)))
                        <= p ^ plw_maxpow p (S m))
          by (apply Nat.pow_le_mono_r; lia).
        apply Hvc. lia.
Qed.

(* 【主件 A·Set 面】L(n) 的 p-adic 赋值 = maxpow 的 hl_id 等式：
   Hanson 分解 L(n)=Π_{p≤n} p^{max{w:p^w≤n}} 的赋值特征承载
   （照 pr_lcm_eq_decomp 宿主口径，指数位升显式 maxpow 形） *)
Theorem plw_v_lcm_upto_id : forall p n : nat,
  pr_prime p -> hl_id (plm_v p (hl_lcm_upto n)) (plw_maxpow p n).
Proof.
  intros p n Hpp.
  rewrite (plw_v_lcm_upto p n Hpp). apply hl_idrefl.
Qed.

(* ---- §4 主件 B：逐素幂环带吸收步 ---- *)

(* 素数阶乘无整除：p 素 ∧ m < p ⟹ p∤fact m
   （p∣阶乘则 p∣某因子 ≤ m < p，破素性；归纳步素分解双定向） *)
Lemma plw_nodvd_fact : forall m p : nat,
  pr_prime p -> m < p -> (Nat.divide p (fact m) -> False).
Proof.
  intros m p Hpp. destruct Hpp as [Hp2 Hpd].
  induction m as [| m IH]; intros Hlt Hd.
  - cbn [fact] in Hd. apply Nat.divide_1_r in Hd. lia.
  - cbn [fact] in Hd. rewrite Nat.mul_comm in Hd.
    destruct (plm_prime_dvd_mul p (fact m) (S m)
                (conj Hp2 Hpd) Hd) as [H1 | H2].
    + exact (IH ltac:(lia) H1).
    + assert (Hle : p <= S m)
        by (apply Nat.divide_pos_le; [lia | exact H2]).
      lia.
Qed.

(* 素数尾互素座：素 p ∧ p∤x ⟹ gcd p x = 1（gcd 三分定向） *)
Lemma plw_gcd_1_of_nodvd : forall p x : nat,
  pr_prime p -> (Nat.divide p x -> False) -> Nat.gcd p x = 1.
Proof.
  intros p x [Hp2 Hpd] Hnd.
  destruct (Nat.eq_dec (Nat.gcd p x) 1) as [E1 | NE1].
  - exact E1.
  - exfalso.
    assert (Hgp : Nat.divide (Nat.gcd p x) p) by apply Nat.gcd_divide_l.
    assert (Hgm : Nat.divide (Nat.gcd p x) x) by apply Nat.gcd_divide_r.
    assert (Hle : Nat.gcd p x <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hgp]).
    remember (Nat.gcd p x) as g eqn:Eg.
    destruct g as [| [| g']].
    + apply Nat.divide_0_l in Hgp. lia.
    + apply NE1. reflexivity.
    + assert (Hg2 : Nat.gcd p x = p).
      { destruct (Nat.eq_dec (Nat.gcd p x) p) as [Eg2 | NEg2].
        - exact Eg2.
        - exfalso.
          assert (Hlt2 : S (S g') < p).
          { destruct (le_lt_dec p (S (S g'))) as [Hge | Hlt2].
            - exfalso. apply NEg2. apply Nat.le_antisymm;
                [rewrite <- Eg; exact Hle | rewrite <- Eg; exact Hge].
            - exact Hlt2. }
          exact (Hpd (S (S g')) ltac:(lia) Hlt2 Hgp). }
      rewrite Eg, Hg2 in Hgm. apply Hnd. exact Hgm.
Qed.

(* 素环带吸收（w=1 位）：m < p ≤ 2m 素 ⟹ p ∣ C(2m,m)。
   免 Legendre：p 是 Π_{m+1}^{2m} 的字面因子（h3_prod_divide）且
   p>m ⟹ p∤m!（plw_nodvd_fact），plm_gauss 吸收入二项式。 *)
Lemma plw_annulus_prime_dvd_binom : forall m p : nat,
  pr_prime p -> m < p -> p <= 2 * m ->
  Nat.divide p (hl_binom (2 * m) m).
Proof.
  intros m p Hpp Hlt Hle.
  replace (2 * m) with (m + m) by lia.
  assert (Hprod : Nat.divide p (h3_prod_from (S m) m)).
  { apply (h3_prod_divide m (S m) p); lia. }
  rewrite (h3_prod_binom_fact m m) in Hprod.
  apply (plm_gauss p (fact m)).
  - apply (plw_gcd_1_of_nodvd p (fact m) Hpp).
    intro Hd. exact (plw_nodvd_fact m p Hpp Hlt Hd).
  - rewrite Nat.mul_comm. exact Hprod.
Qed.

(* 【主件 B】逐素幂环带吸收步：素幂 p^w 落于 (m,2m] ⟹
   p^w ∣ C(2m,m)·L(m)·p。
   w=0：平凡；w=1：素环带位（plw_annulus_prime_dvd_binom）；
   w≥2：p^{w-1} ≤ m（p^{w-1}·2 ≤ p^{w-1}·p = p^w ≤ 2m）⟹
   p^{w-1}∣L(m)（hl_lcm_divide_all），配 p∣p 双乘并入。 *)
Theorem plw_annulus_pow_dvd : forall p m w : nat,
  pr_prime p -> m < p ^ w -> p ^ w <= 2 * m ->
  Nat.divide (p ^ w) (hl_binom (2 * m) m * hl_lcm_upto m * p).
Proof.
  intros p m w Hpp Hlt Hle.
  destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  destruct w as [| w'].
  - rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - destruct w' as [| w''].
    + (* w=1：素环带位 *)
      rewrite Nat.pow_1_r in Hlt, Hle.
      rewrite Nat.pow_1_r.
      destruct (plw_annulus_prime_dvd_binom m p (conj Hp2 Hpd) Hlt Hle)
        as [q Hq].
      exists (q * (hl_lcm_upto m * p)). rewrite Hq. ring.
    + (* w≥2：p^{S w''} 预算吸收入 L(m)，p∣p 双乘 *)
      assert (Heq : p ^ S (S w'') = p ^ S w'' * p)
        by (rewrite Nat.pow_succ_r'; ring).
      rewrite Heq in Hle. rewrite Heq.
      replace (hl_binom (2 * m) m * hl_lcm_upto m * p)
        with (hl_lcm_upto m * (hl_binom (2 * m) m * p)) by ring.
      apply (plw_dvd_mul_mono (p ^ S w'') (hl_lcm_upto m) p
               (hl_binom (2 * m) m * p)).
      * apply (hl_lcm_divide_all m (p ^ S w'')).
        -- assert (Hnz : 0 < p ^ S w'').
           { apply Nat.neq_0_lt_0.
             pose proof (Nat.pow_nonzero p (S w'')). lia. }
           lia.
        -- assert (Hm2 : p ^ S w'' * 2 <= p ^ S w'' * p)
             by (apply Nat.mul_le_mono_l; lia).
           lia.
      * exists (hl_binom (2 * m) m). ring.
Qed.

(* 二项式系数正性：k ≤ n ⟹ 1 ≤ C(n,k)（折叠递归归纳） *)
Lemma plw_binom_pos : forall n k : nat,
  k <= n -> 1 <= hl_binom n k.
Proof.
  intros n. induction n as [| n IH]; intros k Hk.
  - assert (Hk0 : k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. lia.
    + cbn [hl_binom].
      assert (H1 : 1 <= hl_binom n k') by (apply IH; lia).
      lia.
Qed.

(* Hanson 半程步的逐素点态形（主件 A' 与主件 B 的直接装配收窄档）：
   对每个素数 p，L(2m) 的 p-赋值不超过 C(2m,m)·L(m)·p 的 p-赋值，
   即逐素点态意义下的 L(2m)∣C(2m,m)·L(m)·p（p-adic 路线可闭的准确
   上界档）。全局跨素合并为单一 divide 形需相异素幂两两互素的合并
   机制，仍为登记缺口（另案）。 *)
Theorem plw_lcm2m_v_le_carry : forall p m : nat,
  pr_prime p -> 1 <= m ->
  plm_v p (hl_lcm_upto (2 * m))
  <= plm_v p (hl_binom (2 * m) m * hl_lcm_upto m * p).
Proof.
  intros p m Hpp Hm.
  destruct Hpp as [Hp2 Hpd].
  assert (Hp1 : 1 < p) by lia.
  assert (Hm2 : 1 <= 2 * m) by lia.
  assert (HL : 1 <= hl_lcm_upto m) by apply plw_lcm_pos.
  assert (Hb : 1 <= hl_binom (2 * m) m) by (apply plw_binom_pos; lia).
  assert (HX : 1 <= hl_binom (2 * m) m * hl_lcm_upto m)
    by (apply (Nat.mul_le_mono 1 (hl_binom (2 * m) m) 1
                (hl_lcm_upto m)); lia).
  assert (HY : 1 * p <= hl_binom (2 * m) m * hl_lcm_upto m * p)
    by (apply Nat.mul_le_mono_r; lia).
  assert (Hpos : 1 <= hl_binom (2 * m) m * hl_lcm_upto m * p) by lia.
  assert (HdL : Nat.divide (hl_lcm_upto m)
                  (hl_binom (2 * m) m * hl_lcm_upto m * p)).
  { exists (hl_binom (2 * m) m * p). ring. }
  assert (Hd2 : Nat.divide (p ^ plm_v p (hl_lcm_upto (2 * m)))
                  (hl_lcm_upto (2 * m))) by apply plm_v_dvd.
  pose proof (proj1 (plw_pow_dvd_lcm_iff p (2 * m)
              (plm_v p (hl_lcm_upto (2 * m))) (conj Hp2 Hpd) Hm2)
              Hd2) as Hle2.
  destruct (le_lt_dec (p ^ plm_v p (hl_lcm_upto (2 * m))) m)
    as [Hcase | Hcase].
  - (* p^{v} ≤ m：预算吸收入 L(m) *)
    assert (HdmL : Nat.divide (p ^ plm_v p (hl_lcm_upto (2 * m)))
                    (hl_lcm_upto m)).
    { apply (proj2 (plw_pow_dvd_lcm_iff p m
              (plm_v p (hl_lcm_upto (2 * m))) (conj Hp2 Hpd) Hm)).
      exact Hcase. }
    apply (plw_v_le_dvd p
            (hl_binom (2 * m) m * hl_lcm_upto m * p));
      [lia | exact Hpos |].
    apply (Nat.divide_trans (p ^ plm_v p (hl_lcm_upto (2 * m)))
              (hl_lcm_upto m)
              (hl_binom (2 * m) m * hl_lcm_upto m * p)).
    + exact HdmL.
    + exact HdL.
  - (* m < p^{v} ≤ 2m：环带吸收（主件 B） *)
    apply (plw_v_le_dvd p
            (hl_binom (2 * m) m * hl_lcm_upto m * p));
      [lia | exact Hpos |].
    exact (plw_annulus_pow_dvd p m (plm_v p (hl_lcm_upto (2 * m)))
             (conj Hp2 Hpd) Hcase Hle2).
Qed.

(* ---- §5 数值定装烟测（maxpow 爬攀小实例 vm_compute 零公设；
   plm_v 大实例耗时长，禁用作定装路径） ---- *)

Lemma plw_maxpow_smoke_2_6 : plw_maxpow 2 6 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_2_8 : plw_maxpow 2 8 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_3_9 : plw_maxpow 3 9 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_2_1 : plw_maxpow 2 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(* 环带实例：p=3,m=2：3 ∈ (2,4]，3 ∣ C(4,2)·L(2)·3 = 6·2·3 *)
Lemma plw_annulus_smoke_3_2 :
  Nat.eqb ((hl_binom (2 * 2) 2 * hl_lcm_upto 2 * 3) mod 3) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- §6 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions plw_v_char.
Print Assumptions plw_pow_v_eq.
Print Assumptions plw_v_mul.
Print Assumptions plw_v_gcd.
Print Assumptions plw_v_lcm.
Print Assumptions plw_pow_dvd_lcm_iff.
Print Assumptions plw_v_lcm_upto.
Print Assumptions plw_v_lcm_upto_id.
Print Assumptions plw_annulus_prime_dvd_binom.
Print Assumptions plw_annulus_pow_dvd.
Print Assumptions plw_binom_pos.
Print Assumptions plw_lcm2m_v_le_carry.
Print Assumptions plw_maxpow_smoke_2_6.

(* ---- §7 提取检查（Separate Extraction：可执行核 plw_maxpow 直提） ---- *)

From Stdlib Require Import Extraction.
Separate Extraction plw_maxpow.
