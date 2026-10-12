(* ============================================================ *)
(* u5c_pr_lcm_divide.v —— lcm(1..n) 的全局整除半程步：L(2m) ∣ C(2m,m)·L(m) *)
(* 模块名：u5c_pr_lcm_divide                                      *)
(* 数学使命：将逐素点态半程上界（u5c_pr_lcm_absorb 的 B' 档，带 p 因子余量）锐化为全局单一整除形： *)
(*   hl_lcm_upto (2*m) ∣ hl_binom (2*m) m * hl_lcm_upto m。交付六面： *)
(*   ①互素折叠两件：列表两两互素且逐项整除则积整除；相异素数的幂两两互素。 *)
(*   ②环带层数计数面：p 幂布尔见证机（mod 递降＋燃料封顶）与 (m,2m] 内 p 幂值的过滤计数 plw_lvl_cnt。 *)
(*   ③Legendre 走廊：fact n = p^(n/p)·fact(n/p)·(p 自由部) 的抽取式与赋值递推 *)
(*     plm_v p (fact n) = n/p + plm_v p (fact (n/p))，经偶端/奇端两式配对归纳得 *)
(*     v_p(C(2m,m)) ≥ #{j≥1 : m < p^j ≤ 2m}。 *)
(*   ④指数桥：plw_maxpow p (2m) ≤ plw_maxpow p m ＋ 层数计数（幂值单射入计数表，NoDup_incl_length）。 *)
(*   ⑤商抽取：L(2m) = L(m)·M，逐素 p^(v_p M) ∣ C(2m,m)。 *)
(*   ⑥全局合并机：逐素幂整除界则整体整除（plw_dvd_of_prime_pows，最小素因子强归纳），装配主定理 plw_lcm2m_divide。 *)
(* 依赖清单：HansonLcm（hl_lcm_upto/hl_lcm_divide_all/hl_binom）＋Hanson3Pow（h3_prod_from/h3_prod_binom_fact）＋ *)
(*   abl_Pr_core_01（pr_prime/pr_min_factor_exists/pr_mod0_dvd/pr_dvd_mod0）＋abl_Pr_lcmdecomp_04 *)
(*   （plm_v/plm_v_dvd/plm_v_max/plm_coprime_prod_dvd/plm_prime_gcd_1/plm_gcd_pow/plm_prime_dvd_mul）＋ *)
(*   u5c_pr_lcm_absorb（plw_v_char/plw_v_mul/plw_pow_v_eq/plw_pow_dvd_lcm_iff/plw_maxpow_dvd_upto/ *)
(*   plw_maxpow_ceil/plw_pow_le_dvd/plw_dvd_mul_mono/plw_mul_cancel_l/plw_pow_pos/plw_pow_lt_mono/ *)
(*   plw_lcm_pos/plw_binom_pos/plw_v_lcm_upto）＋纯 Stdlib（Arith.Arith/Arith.Factorial/List/Lia）。 *)
(* 对标行：Hanson 1972（Acta Arith.）lcm(1,…,n) < 3^n 分解第一行 L(2n) ∣ C(2n,n)·L(n)；Nagell 半程链的逐素锐化档。 *)
(* 构造性注记：Set 面承载——计算件 plw_ispw_f/plw_ispw/plw_multp 皆一阶 nat Fixpoint/Definition 可提取 *)
(*   （Separate Extraction）；Prop 面谓词仅推理脚手架；否定面全走 -> False 形（零否定记号书写，含证明内部）； *)
(*   零公理零承认零经典逻辑；主定理收尾零 solver（lia 仅限支撑算术位）；数值定装走小实例 vm_compute（≤10，环带实例底数≤3）。 *)
(* 编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh && ulimit -s 65532 && cd <池> && *)
(*   nice -19 rocq c -native-compiler no -q -Q . "" u5c_pr_lcm_divide.v（依赖件 vo 经 -Q 映射挂源根，只读引用） *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Bool List Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import u5c_pr_lcm_absorb.
Import ListNotations.

(* ---- §0 列表、fold、除法与整除小件 ---- *)

Lemma plw_len_map : forall (f : nat -> nat) (l : list nat),
  length (map f l) = length l.
Proof.
  intros f. induction l as [| x l IH]; cbn [map length].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma plw_fold_app : forall (l1 l2 : list nat),
  fold_right Nat.mul 1 (l1 ++ l2)
  = fold_right Nat.mul 1 l1 * fold_right Nat.mul 1 l2.
Proof.
  induction l1 as [| x l1 IH]; intros l2; cbn [app fold_right].
  - lia.
  - rewrite IH. ring.
Qed.

Lemma plw_filter_partition : forall (g : nat -> bool) (l : list nat),
  length (filter g l) + length (filter (fun x => negb (g x)) l) = length l.
Proof.
  intros g. induction l as [| x l IH]; cbn [filter length].
  - reflexivity.
  - destruct (g x); cbn [negb length]; lia.
Qed.

Lemma plw_fold_partition : forall (g : nat -> bool) (l : list nat),
  fold_right Nat.mul 1 l
  = fold_right Nat.mul 1 (filter g l)
    * fold_right Nat.mul 1 (filter (fun x => negb (g x)) l).
Proof.
  intros g. induction l as [| x l IH]; cbn [filter fold_right].
  - reflexivity.
  - destruct (g x); cbn [negb filter fold_right]; rewrite IH; ring.
Qed.

Lemma plw_filter_none : forall (g : nat -> bool) (l : list nat),
  (forall k, In k l -> g k = false) -> filter g l = [].
Proof.
  intros g. induction l as [| x l IH]; intros Hall; cbn [filter].
  - reflexivity.
  - rewrite (Hall x (or_introl eq_refl)).
    apply IH. intros k Hk. apply Hall. apply in_cons. exact Hk.
Qed.

Lemma plw_filter_in : forall (g : nat -> bool) (l : list nat) (k : nat),
  In k (filter g l) -> In k l /\ g k = true.
Proof.
  intros g. induction l as [| x l IH]; intros k H.
  - cbn [filter] in H. destruct H.
  - cbn [filter] in H. destruct (g x) eqn:Ex; cbn in H.
    + destruct H as [H | H].
      * subst k. split; [apply in_eq | exact Ex].
      * destruct (IH k H) as [Hin Hg].
        split; [apply in_cons; exact Hin | exact Hg].
    + destruct (IH k H) as [Hin Hg].
      split; [apply in_cons; exact Hin | exact Hg].
Qed.

Lemma plw_filter_in_rev : forall (g : nat -> bool) (l : list nat) (k : nat),
  In k l -> g k = true -> In k (filter g l).
Proof.
  intros g. induction l as [| x l IH]; intros k Hin Hg; cbn [filter].
  - destruct Hin.
  - destruct (g x) eqn:Ex.
    + destruct Hin as [H | H].
      * subst k. apply in_eq.
      * apply in_cons. apply IH; assumption.
    + destruct Hin as [H | H].
      * subst k. rewrite Ex in Hg. discriminate.
      * apply IH; assumption.
Qed.

Lemma plw_length_seq : forall (len start : nat), length (seq start len) = len.
Proof.
  induction len as [| len IH]; intros start; cbn [seq length].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma plw_NoDup_map_inj : forall (fi : nat -> nat) (l : list nat),
  (forall x y, In x l -> In y l -> fi x = fi y -> x = y) ->
  NoDup l -> NoDup (map fi l).
Proof.
  intros fi. induction l as [| x l IH]; intros Hinj Hnd; cbn [map].
  - constructor.
  - inversion Hnd as [| x' l' Hnin Hnd']; subst. constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]].
      assert (Hxy : x = y)
        by (apply Hinj; [apply in_eq | apply in_cons; exact Hiny | symmetry; exact Hfy]).
      subst y. contradiction.
    + apply IH; [| exact Hnd'].
      intros x' y' Hx' Hy' Hf.
      apply Hinj; [apply in_cons; exact Hx' | apply in_cons; exact Hy' | exact Hf].
Qed.

Lemma plw_div_0 : forall p : nat, 0 / p = 0.
Proof. intros p. destruct p; reflexivity. Qed.

(* 除法唯一性（div_mod_unique 包装） *)
Lemma plw_div_unique_gen : forall n p q r : nat,
  p <> 0 -> r < p -> n = p * q + r -> n / p = q.
Proof.
  intros n p q r Hp Hr Hn.
  pose proof (Nat.div_mod_eq n p) as H1.
  pose proof (Nat.mod_upper_bound n p ltac:(lia)) as H2.
  assert (Heq : p * (n / p) + n mod p = p * q + r)
    by lia.
  apply (proj1 (Nat.div_mod_unique p (n / p) q (n mod p) r H2 Hr Heq)).
Qed.

(* a*p/p = a（p ≠ 0） *)
Lemma plw_div_mul : forall a p : nat, p <> 0 -> a * p / p = a.
Proof.
  intros a p Hp.
  apply (plw_div_unique_gen (a * p) p a 0); [exact Hp | lia | lia].
Qed.

(* p ∣ n 且 n ≥ 1 时退一格：(n−1)/p = n/p − 1 *)
Lemma plw_div_pred : forall n p : nat, 0 < p -> Nat.divide p n -> 1 <= n ->
  (n - 1) / p = n / p - 1.
Proof.
  intros n p Hp Hd Hn.
  assert (Hq1 : 1 <= n / p).
  { destruct (n / p) as [| q] eqn:Eq; [| lia].
    exfalso.
    assert (Hnp : p <= n) by (apply Nat.divide_pos_le; [lia | exact Hd]).
    pose proof (Nat.div_mod_eq n p) as Hdm.
    pose proof (Nat.mod_upper_bound n p ltac:(lia)) as Hmb.
    rewrite Eq, Nat.mul_0_r, Nat.add_0_l in Hdm. lia. }
  destruct (n / p) as [| q] eqn:Eq.
  { exfalso. lia. }
  replace (S q - 1) with q by (destruct q; reflexivity).
  apply (plw_div_unique_gen (n - 1) p q (p - 1)); [lia | lia |].
  pose proof (Nat.div_mod_eq n p) as Hdm.
  assert (Hm0 : n mod p = 0) by (apply pr_dvd_mod0; [lia | exact Hd]).
  rewrite Hm0, Nat.add_0_r, Eq in Hdm. lia.
Qed.

(* p ∤ n 时平移不变：(n−1)/p = n/p *)
Lemma plw_div_step : forall n p : nat, 0 < p -> n mod p <> 0 ->
  (n - 1) / p = n / p.
Proof.
  intros n p Hp Hm.
  pose proof (Nat.div_mod_eq n p) as H1.
  pose proof (Nat.mod_upper_bound n p ltac:(lia)) as H2.
  apply (plw_div_unique_gen (n - 1) p (n / p) (n mod p - 1)); [lia | lia |].
  lia.
Qed.

(* 倍增降档形一：(2n)/p ∈ {2(n/p), 2(n/p)+1} *)
Lemma plw_div2_even : forall n p : nat, 0 < p ->
  (2 * n) / p = 2 * (n / p) \/ (2 * n) / p = 2 * (n / p) + 1.
Proof.
  intros n p Hp.
  pose proof (Nat.div_mod_eq n p) as Hd.
  replace (2 * n) with ((2 * (n / p)) * p + 2 * (n mod p)).
  2:{ rewrite Hd at 3. ring. }
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.mod_upper_bound n p ltac:(lia)) as Hmb.
  pose proof (Nat.Div0.div_lt_upper_bound (2 * (n mod p)) p 2 ltac:(lia)) as Hlt.
  assert (H0 : 0 <= (2 * (n mod p)) / p) by lia.
  destruct (Nat.eq_dec ((2 * (n mod p)) / p) 0) as [E | E].
  - left. lia.
  - right. assert ((2 * (n mod p)) / p = 1) by lia. lia.
Qed.

(* 倍增降档形二：(2n+1)/p ∈ {2(n/p), 2(n/p)+1} *)
Lemma plw_div2_odd : forall n p : nat, 0 < p ->
  (2 * n + 1) / p = 2 * (n / p) \/ (2 * n + 1) / p = 2 * (n / p) + 1.
Proof.
  intros n p Hp.
  pose proof (Nat.div_mod_eq n p) as Hd.
  replace (2 * n + 1) with ((2 * (n / p)) * p + (2 * (n mod p) + 1)).
  2:{ rewrite Hd at 3. ring. }
  rewrite Nat.div_add_l by lia.
  pose proof (Nat.mod_upper_bound n p ltac:(lia)) as Hmb.
  pose proof (Nat.Div0.div_lt_upper_bound (2 * (n mod p) + 1) p 2 ltac:(lia)) as Hlt.
  assert (H0 : 0 <= (2 * (n mod p) + 1) / p) by lia.
  destruct (Nat.eq_dec ((2 * (n mod p) + 1) / p) 0) as [E | E].
  - left. lia.
  - right. assert ((2 * (n mod p) + 1) / p = 1) by lia. lia.
Qed.

(* 2(a/p) ≤ (2a)/p *)
Lemma plw_div_double : forall a p : nat, 0 < p -> 2 * (a / p) <= (2 * a) / p.
Proof.
  intros a p Hp.
  replace (2 * a) with ((2 * (a / p)) * p + 2 * (a mod p))
    by (rewrite (Nat.div_mod_eq a p) at 3; ring).
  rewrite Nat.div_add_l by lia. lia.
Qed.

(* 正指数幂恒不低于 2 *)
Lemma plw_pow_le_base : forall a b e : nat, a <= b -> a ^ e <= b ^ e.
Proof.
  intros a b e H. induction e as [| e IH].
  - rewrite Nat.pow_0_r, Nat.pow_0_r. lia.
  - rewrite Nat.pow_succ_r', Nat.pow_succ_r'.
    apply Nat.mul_le_mono; assumption.
Qed.

(* 同底倍增严格增 *)
Lemma plw_lt_mul_same : forall p a : nat, 2 <= p -> 1 <= a -> a < p * a.
Proof.
  intros p a Hp Ha. destruct p as [| [| p']].
  - lia.
  - rewrite Nat.mul_succ_l. lia.
  - rewrite Nat.mul_succ_l, Nat.mul_succ_l. lia.
Qed.

(* 减法补偿：A ≤ T 时 S T ≤ S A + (T − A) *)
Lemma plw_succ_add_sub : forall A T : nat, A <= T -> S T <= S A + (T - A).
Proof. intros A T H. lia. Qed.

Lemma plw_pow_ge2 : forall p e : nat, 2 <= p -> 1 <= e -> 2 <= p ^ e.
Proof.
  intros p e Hp He.
  apply Nat.le_trans with (2 ^ e).
  - apply Nat.le_trans with (2 ^ 1).
    + rewrite Nat.pow_1_r. lia.
    + apply Nat.pow_le_mono_r; lia.
  - apply plw_pow_le_base; lia.
Qed.

(* ---- §1 切片一：互素折叠整除 ---- *)

Theorem plw_coprime_fold_dvd : forall (l : list nat) (N : nat),
  (forall x, In x l -> Nat.divide x N) ->
  (forall x y, In x l -> In y l -> Nat.gcd x y = 1) ->
  Nat.divide (fold_right Nat.mul 1 l) N.
Proof.
  intros l N Hdiv Hpw.
  exact (plm_coprime_prod_dvd l N Hdiv Hpw).
Qed.

(* ---- §2 切片二：相异素数幂互素 ---- *)

Theorem plw_pow_coprime_of_prime_coprime : forall p q w u : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) ->
  Nat.gcd (p ^ w) (q ^ u) = 1.
Proof.
  intros p q w u Hpp Hqq Hne.
  apply (plm_gcd_pow p q w u).
  exact (plm_prime_gcd_1 p q Hpp Hqq Hne).
Qed.

(* ---- §3 p 幂布尔见证机 ---- *)

Definition plw_multp (p k : nat) : bool := Nat.eqb (k mod p) 0.

Lemma plw_multp_false_inv : forall p k : nat, 1 <= p ->
  plw_multp p k = false -> (Nat.divide p k -> False).
Proof.
  intros p k Hp Hm Hd. unfold plw_multp in Hm.
  apply Nat.eqb_neq in Hm.
  apply Hm. apply pr_dvd_mod0; [exact Hp | exact Hd].
Qed.

(* 燃料递降幂见证：k 为 p 的正幂（j ≥ 1，2 ≤ p）判 true；
   递归形 k = p 或（p ∣ k 且 k/p 仍为正幂），燃料封顶防发散 *)
Fixpoint plw_ispw_f (p k fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      if Nat.eqb k 1 then false
      else if Nat.eqb k p then true
      else andb (Nat.eqb (k mod p) 0) (plw_ispw_f p (k / p) f)
  end.

Definition plw_ispw (p k : nat) : bool := plw_ispw_f p k (S k).

(* 可靠性：true ⟹ 存在正指数幂表示 *)
Lemma plw_ispw_f_sound : forall fuel p k : nat, 2 <= p ->
  plw_ispw_f p k fuel = true -> exists j : nat, 1 <= j /\ p ^ j = k.
Proof.
  induction fuel as [| f IH]; intros p k Hp H; [discriminate |].
  cbn [plw_ispw_f] in H.
  destruct (Nat.eqb k 1) eqn:E1; [discriminate |].
  destruct (Nat.eqb k p) eqn:Ep.
  - apply Nat.eqb_eq in Ep.
    exists 1. split; [lia | rewrite Nat.pow_1_r; symmetry; exact Ep].
  - apply andb_true_iff in H. destruct H as [Hmod Hrec].
    apply Nat.eqb_eq in Hmod.
    destruct (IH p (k / p) Hp Hrec) as [j [Hj Hkj]].
    exists (S j). split; [lia |].
    pose proof (Nat.div_mod_eq k p) as Hdm.
    rewrite Hmod in Hdm.
    rewrite Nat.pow_succ_r', Hkj. symmetry. lia.
Qed.

Lemma plw_ispw_sound : forall p k : nat, 2 <= p ->
  plw_ispw p k = true -> exists j : nat, 1 <= j /\ p ^ j = k.
Proof.
  intros p k Hp H. unfold plw_ispw in H.
  exact (plw_ispw_f_sound (S k) p k Hp H).
Qed.

(* 完备性：正幂必判 true（燃料 ≥ 幂值即足） *)
Lemma plw_ispw_f_pow : forall j p fuel : nat, 2 <= p -> 1 <= j -> p ^ j <= fuel ->
  plw_ispw_f p (p ^ j) fuel = true.
Proof.
  intros j. induction j as [| j IH]; intros p fuel Hp Hj Hf.
  - lia.
  - destruct (Nat.eq_dec j 0) as [E0 | Hj0].
    + subst j. destruct fuel as [| f];
        [rewrite Nat.pow_1_r in Hf; lia |].
      rewrite Nat.pow_1_r. cbn [plw_ispw_f].
      rewrite (proj2 (Nat.eqb_neq p 1) ltac:(lia)).
      rewrite Nat.eqb_refl. reflexivity.
    + assert (Hp2 : 2 <= p ^ S j).
      { apply plw_pow_ge2; lia. }
      destruct fuel as [| f]; [lia |].
      cbn [plw_ispw_f].
      assert (E1 : Nat.eqb (p ^ S j) 1 = false).
      { apply Nat.eqb_neq.
        pose proof (plw_pow_pos p (S j) ltac:(lia)) as Hpos.
        assert (Hge : 2 <= p ^ S j).
        { apply plw_pow_ge2; lia. }
        lia. }
      rewrite E1.
      assert (Ep : Nat.eqb (p ^ S j) p = false).
      { apply Nat.eqb_neq. intro E.
        assert (Hc : p ^ j = 1).
        { apply (plw_mul_cancel_l p); [lia |].
          rewrite <- (Nat.pow_succ_r' p j), E, Nat.mul_1_r. reflexivity. }
        assert (Hge : 2 <= p ^ j).
        { apply plw_pow_ge2; lia. }
        lia. }
      rewrite Ep.
      assert (Emod : Nat.eqb (p ^ S j mod p) 0 = true).
      { apply Nat.eqb_eq.
        replace (p ^ S j) with (p ^ j * p) by (rewrite Nat.pow_succ_r'; ring).
        apply pr_dvd_mod0; [lia | exists (p ^ j); rewrite Nat.mul_comm; reflexivity]. }
      rewrite Emod.
      replace (p ^ S j / p) with (p ^ j).
      2:{ replace (p ^ S j) with (p ^ j * p) by (rewrite Nat.pow_succ_r'; ring).
          symmetry. apply plw_div_mul. lia. }
      cbn [andb].
      apply IH; [lia | lia |].
      rewrite Nat.pow_succ_r' in Hf.
      assert (HposA : 1 <= p ^ j) by (apply plw_pow_pos; lia).
      assert (HBA : p ^ j < p * p ^ j)
        by (apply plw_lt_mul_same; lia).
      lia.
Qed.

Lemma plw_ispw_pow : forall p j : nat, 2 <= p -> 1 <= j ->
  plw_ispw p (p ^ j) = true.
Proof.
  intros p j Hp Hj. unfold plw_ispw.
  apply plw_ispw_f_pow; [exact Hp | exact Hj | lia].
Qed.

(* ---- §4 环带层数计数面 ---- *)

Definition plw_lvl_pred (p m : nat) : nat -> bool :=
  fun k => andb (Nat.ltb m k) (plw_ispw p k).

Definition plw_lvl_list (p m a n : nat) : list nat :=
  filter (plw_lvl_pred p m) (seq a n).

Definition plw_lvl_cnt (p m a n : nat) : nat :=
  length (plw_lvl_list p m a n).

(* 层值单点指示：p 本身是否为 (a,t] 内层值 *)
Definition plw_ind_ge (a t p : nat) : nat :=
  if andb (Nat.ltb a p) (Nat.leb p t) then 1 else 0.

(* 计数表成员的幂见证提升 *)
Lemma plw_lvl_pred_pow : forall p m k : nat, pr_prime p ->
  plw_lvl_pred p m k = true ->
  exists j : nat, 1 <= j /\ p ^ j = k /\ m < k.
Proof.
  intros p m k Hpp H. unfold plw_lvl_pred in H.
  apply andb_true_iff in H. destruct H as [Hlt Hik].
  destruct (plw_ispw_sound p k (proj1 Hpp) Hik) as [j [Hj Hkj]].
  exists j. split; [exact Hj | split; [exact Hkj | apply Nat.ltb_lt; exact Hlt]].
Qed.

(* 除法单调：a ≤ t ⟹ a/p ≤ t/p *)
Lemma plw_div_le_mono_b : forall p a t : nat, 0 < p -> a <= t -> a / p <= t / p.
Proof.
  intros p a t Hp H.
  destruct (le_lt_dec (a / p) (t / p)) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    assert (Hstep : p * (t / p) + p <= p * (a / p))
      by (apply Nat.le_trans with (p * (t / p + 1));
          [rewrite Nat.mul_add_distr_l; lia | apply Nat.mul_le_mono_l; lia]).
    pose proof (Nat.div_mod_eq a p) as Hda.
    pose proof (Nat.div_mod_eq t p) as Hdt.
    pose proof (Nat.mod_upper_bound a p ltac:(lia)) as Hba.
    pose proof (Nat.mod_upper_bound t p ltac:(lia)) as Hbt.
    lia.
Qed.

(* 乘法比较的除法下桥：x < p·y ⟹ x/p < y *)
Lemma plw_div_lt_mul : forall p x y : nat, 0 < p -> x < p * y -> x / p < y.
Proof.
  intros p x y Hp Hlt.
  destruct (le_lt_dec y (x / p)) as [Hle | Hlt2]; [| exact Hlt2].
  exfalso.
  assert (pm : p * y <= p * (x / p)) by (apply Nat.mul_le_mono_l; exact Hle).
  pose proof (Nat.div_mod_eq x p) as Hda.
  pose proof (Nat.mod_upper_bound x p ltac:(lia)) as Hba.
  lia.
Qed.

(* 乘法比较的除法上桥：p·y ≤ t ⟹ y ≤ t/p *)
Lemma plw_div_le_mul : forall p y t : nat, 0 < p -> p * y <= t -> y <= t / p.
Proof.
  intros p y t Hp H.
  destruct (le_lt_dec y (t / p)) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
  assert (Hstep : p * (t / p) + p <= p * y).
  { apply Nat.le_trans with (p * (t / p + 1)).
    - rewrite Nat.mul_add_distr_l. lia.
    - apply Nat.mul_le_mono_l. lia. }
  pose proof (Nat.div_mod_eq t p) as Hdt.
  pose proof (Nat.mod_upper_bound t p ltac:(lia)) as Hbt.
  lia.
Qed.

(* 倍增降档计数恒等式：层值表 (a,t] ＝ 单点 p（若为层值）＋ 层值表
   (a/p, t/p]（经 k′ ↦ p·k′ 双向单射） *)
Lemma plw_lvl_cnt_descent : forall p a t : nat, pr_prime p ->
  1 <= a -> a <= t -> t <= 2 * a + 1 ->
  plw_lvl_cnt p a (S a) (t - a)
  = plw_ind_ge a t p + plw_lvl_cnt p (a / p) (S (a / p)) ((t / p) - (a / p)).
Proof.
  intros p a t [Hp2 Hpd] Ha H1 H2.
  assert (Hp1 : 1 < p) by lia.
  assert (Hpp0 : 0 < p) by lia.
  unfold plw_lvl_cnt, plw_lvl_list.
  set (L := filter (plw_lvl_pred p a) (seq (S a) (t - a))).
  set (R := filter (plw_lvl_pred p (a / p))
                   (seq (S (a / p)) ((t / p) - (a / p)))).
  assert (HnodL : NoDup L) by (unfold L; apply NoDup_filter; apply seq_NoDup).
  assert (HnodR : NoDup R) by (unfold R; apply NoDup_filter; apply seq_NoDup).
  assert (Hsplit : length (filter (fun k => Nat.eqb k p) L) = plw_ind_ge a t p).
  { unfold plw_ind_ge.
    destruct (andb (Nat.ltb a p) (Nat.leb p t)) eqn:Eind.
    - apply andb_true_iff in Eind. destruct Eind as [E1 E2'].
      apply Nat.ltb_lt in E1. apply Nat.leb_le in E2'.
      assert (HinL : In p L).
      { unfold L. apply plw_filter_in_rev.
        - rewrite in_seq. lia.
        - unfold plw_lvl_pred. apply andb_true_iff. split.
          + apply Nat.ltb_lt. exact E1.
          + unfold plw_ispw. cbn [plw_ispw_f].
            rewrite (proj2 (Nat.eqb_neq p 1) ltac:(lia)).
            rewrite Nat.eqb_refl. reflexivity. }
      assert (Hle1 : length (filter (fun k => Nat.eqb k p) L) <= 1).
      { apply Nat.le_trans with (length [p]).
        - apply NoDup_incl_length.
          + apply NoDup_filter. exact HnodL.
          + intros x Hx. apply plw_filter_in in Hx. destruct Hx as [_ Hx'].
            apply Nat.eqb_eq in Hx'. left. symmetry. exact Hx'.
        - cbn [length]. lia. }
      assert (Hge1 : 1 <= length (filter (fun k => Nat.eqb k p) L)).
      { assert (HinF : In p (filter (fun k => Nat.eqb k p) L))
          by (apply plw_filter_in_rev; [exact HinL | apply Nat.eqb_refl]).
        destruct (filter (fun k => Nat.eqb k p) L) as [| y Lf] eqn:EF.
        - destruct HinF.
        - cbn [length]. lia. }
      lia.
    - assert (Hnil : filter (fun k => Nat.eqb k p) L = []).
      { apply plw_filter_none. intros k Hk.
        unfold L in Hk. apply plw_filter_in in Hk.
        destruct Hk as [HkL Hk'].
        apply andb_true_iff in Hk'. destruct Hk' as [Hklt _].
        apply Nat.ltb_lt in Hklt.
        apply in_seq in HkL.
        apply Nat.eqb_neq. intro Hkp.
        apply andb_false_iff in Eind. destruct Eind as [Ef | Ef].
        - apply Nat.ltb_ge in Ef. lia.
        - apply Nat.leb_gt in Ef. lia. }
      rewrite Hnil. cbn [length]. lia. }
  assert (Hmain : length (filter (fun k => negb (Nat.eqb k p)) L) = length R).
  { assert (HinjR : NoDup (map (fun k' => p * k') R)).
    { apply plw_NoDup_map_inj; [| exact HnodR].
      intros x y _ _ Hf. apply (plw_mul_cancel_l p); [lia | exact Hf]. }
    assert (Hincl1 : incl (filter (fun k => negb (Nat.eqb k p)) L)
                          (map (fun k' => p * k') R)).
    { intros k Hk. apply plw_filter_in in Hk. destruct Hk as [HkL Hne].
      apply negb_true_iff in Hne. apply Nat.eqb_neq in Hne.
      unfold L in HkL. apply plw_filter_in in HkL.
      destruct HkL as [Hseq Hpred0].
      destruct (plw_lvl_pred_pow p a k (conj Hp2 Hpd) Hpred0)
        as [j [Hj [Hkj Hkl]]].
      assert (Hj2 : 2 <= j).
      { destruct j as [| j']; [lia |].
        destruct j' as [| j''].
        - exfalso. apply Hne. rewrite <- Hkj, Nat.pow_succ_r',
            Nat.pow_0_r, Nat.mul_1_r. reflexivity.
        - lia. }
      assert (Hkk' : k = p * (p ^ (j - 1))).
      { rewrite <- Nat.pow_succ_r'.
        replace (S (j - 1)) with j by lia. symmetry. exact Hkj. }
      apply in_map_iff. exists (p ^ (j - 1)).
      split; [symmetry; exact Hkk' |].
      unfold R. apply plw_filter_in_rev.
      - rewrite in_seq. split.
        + apply plw_div_lt_mul; [lia |].
          rewrite <- Hkk'. exact Hkl.
        + apply Nat.le_lt_trans with (m := t / p).
          * apply plw_div_le_mul; [lia |].
            replace (p * p ^ (j - 1)) with k by exact Hkk'.
            apply in_seq in Hseq. lia.
          * apply Nat.lt_le_trans with (m := S (t / p)).
            -- apply Nat.lt_succ_diag_r.
            -- assert (Hm : a / p <= t / p)
                 by (apply plw_div_le_mono_b; lia).
               apply plw_succ_add_sub. lia.
      - unfold plw_lvl_pred. apply andb_true_iff. split.
        + apply Nat.ltb_lt. apply plw_div_lt_mul.
          * lia.
          * rewrite <- Hkk'. exact Hkl.
        + apply plw_ispw_pow; [lia | lia]. }
    assert (Hincl2 : incl (map (fun k' => p * k') R)
                          (filter (fun k => negb (Nat.eqb k p)) L)).
    { intros x Hx. apply in_map_iff in Hx. destruct Hx as [k' [Hxk Hk'R]].
      unfold R in Hk'R. apply plw_filter_in in Hk'R.
      destruct Hk'R as [Hseq Hpred0].
      apply in_seq in Hseq.
      assert (Hpl : S (a / p) <= k').
      { apply andb_true_iff in Hpred0. apply Nat.ltb_lt.
        exact (proj1 Hpred0). }
      assert (Hxlt : a < x).
      { rewrite <- Hxk.
        pose proof (Nat.div_mod_eq a p) as Hda.
        pose proof (Nat.mod_upper_bound a p ltac:(lia)) as Hba.
        assert (Hx2 : p * (a / p) + p <= p * k').
        { rewrite <- Nat.mul_succ_r. apply Nat.mul_le_mono_l. lia. }
        lia. }
      destruct (plw_lvl_pred_pow p (a / p) k' (conj Hp2 Hpd) Hpred0)
        as [j [Hj [Hkj _]]].
      assert (Hxle : x <= t).
      { rewrite <- Hxk.
        assert (Hkle : k' <= t / p) by lia.
        assert (Hpk : p * k' <= p * (t / p)) by (apply Nat.mul_le_mono_l; exact Hkle).
        pose proof (Nat.div_mod_eq t p) as Hdt.
        pose proof (Nat.mod_upper_bound t p ltac:(lia)) as Hbt.
        lia. }
      assert (HinL : In x L).
      { unfold L. apply filter_In. split.
        - apply in_seq. lia.
        - unfold plw_lvl_pred. rewrite <- Hxk. apply andb_true_iff. split.
          + apply Nat.ltb_lt. lia.
          + rewrite <- Hkj, <- Nat.pow_succ_r'. apply plw_ispw_pow; lia. }
      apply (proj2 (filter_In (fun k => negb (Nat.eqb k p)) x L)).
      - split.
        + exact HinL.
        + apply negb_true_iff. apply Nat.eqb_neq. intro E.
          assert (Hk2 : 2 <= k').
          { rewrite <- Hkj. apply plw_pow_ge2; lia. }
          assert (Hk1 : k' = 1).
          { rewrite <- Hxk in E. apply (plw_mul_cancel_l p); [lia |].
            rewrite Nat.mul_1_r. exact E. }
          lia. }
    pose proof (NoDup_incl_length HinjR Hincl2) as Hlen1.
    rewrite plw_len_map in Hlen1.
      assert (HndF : NoDup (filter (fun k => negb (Nat.eqb k p)) L))
        by (apply NoDup_filter; exact HnodL).
      pose proof (NoDup_incl_length HndF Hincl1) as Hlen2.
    rewrite plw_len_map in Hlen2. lia. }
  unfold plw_lvl_cnt, plw_lvl_list. fold R. fold L.
  assert (Hpart : length L = length (filter (fun k => Nat.eqb k p) L) + length (filter (fun k => negb (Nat.eqb k p)) L)).
  { symmetry. apply plw_filter_partition. }
  rewrite Hpart, Hsplit, Hmain. reflexivity.
  Qed.

Lemma plw_cnt_exp_bound : forall p a t : nat, pr_prime p ->
  1 <= a -> 2 * a <= t -> t <= 2 * a + 1 ->
  plw_ind_ge a t p + 2 * (a / p) <= t / p.
Proof.
  intros p a t [Hp2 Hpd] Ha H1 H2.
  assert (Hpp0 : 0 < p) by lia.
  pose proof (plw_div_double a p Hpp0) as Hdbl.
  assert (Hmono : (2 * a) / p <= t / p) by (apply Nat.div_le_mono; lia).
  unfold plw_ind_ge.
  destruct (andb (Nat.ltb a p) (Nat.leb p t)) eqn:Eind.
  - apply andb_true_iff in Eind. destruct Eind as [E1 E2'].
    apply Nat.ltb_lt in E1. apply Nat.leb_le in E2'.
    assert (Ha0 : a / p = 0) by (apply (plw_div_unique_gen a p 0 a); lia).
    rewrite Ha0, Nat.mul_0_r, Nat.add_0_r.
    destruct (t / p) as [| q] eqn:Et; [| lia].
    exfalso.
    pose proof (Nat.div_mod_eq t p) as Hdt.
    pose proof (Nat.mod_upper_bound t p ltac:(lia)) as Hbt.
    rewrite Et, Nat.mul_0_r, Nat.add_0_l in Hdt. lia.
  - lia.
Qed.

(* ---- §5 Legendre 走廊：阶乘抽取式与赋值递推 ---- *)

Lemma plw_fact_pos : forall n : nat, 1 <= fact n.
Proof.
  induction n as [| n IH].
  - cbn [fact]. lia.
  - cbn [fact]. apply Nat.le_trans with (1 * 1).
    + lia.
    + apply Nat.mul_le_mono; lia.
Qed.

Lemma plw_fold_pos : forall (l : list nat),
  (forall x, In x l -> 1 <= x) -> 1 <= fold_right Nat.mul 1 l.
Proof.
  induction l as [| x l IH]; intros Hall; cbn [fold_right].
  - lia.
  - apply Nat.le_trans with (1 * 1).
    + lia.
    + apply Nat.mul_le_mono.
      * apply Hall. apply in_eq.
      * apply IH. intros y Hy. apply Hall. apply in_cons. exact Hy.
Qed.

Lemma plw_fact_seq : forall n : nat, fact n = fold_right Nat.mul 1 (seq 1 n).
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [fact]. rewrite IH.
    rewrite List.seq_S, plw_fold_app. cbn [fold_right].
    replace (1 + n) with (S n) by lia. ring.
Qed.

(* 倍数部 fold：filter(mod p = 0)(seq 1 n) 之积 = p^(n/p)·fact(n/p) *)
Lemma plw_mult_fold : forall n p : nat, 2 <= p ->
  fold_right Nat.mul 1 (filter (plw_multp p) (seq 1 n))
  = p ^ (n / p) * fold_right Nat.mul 1 (seq 1 (n / p)).
Proof.
  intros n. induction n as [| n IH]; intros p Hp.
  - rewrite plw_div_0.
    cbn [seq filter fold_right].
    rewrite Nat.pow_0_r. reflexivity.
  - rewrite List.seq_S, List.filter_app, plw_fold_app.
    replace (1 + n) with (S n) by lia.
    cbn [filter].
    destruct (plw_multp p (S n)) eqn:Em.
    + apply Nat.eqb_eq in Em.
      pose proof (Nat.div_mod_eq (S n) p) as Hdm.
      pose proof (Nat.mod_upper_bound (S n) p ltac:(lia)) as Hmb.
      rewrite Em in Hdm.
      assert (Hple : p <= S n).
      { apply (Nat.divide_pos_le p (S n)); [lia |].
        exists (S n / p). rewrite Nat.mul_comm. lia. }
      assert (Hq1 : 1 <= S n / p).
      { destruct (S n / p) as [| q] eqn:Eq; [| lia].
        exfalso. lia. }
      destruct (S n / p) as [| q] eqn:Eq.
      { exfalso. lia. }
      assert (Hsn : S n = p * S q) by lia.
      assert (Hmp : n / p = q).
      { assert (Hstep : (S n - 1) / p = S n / p - 1)
          by (apply plw_div_pred; [lia | exists (S q); rewrite Nat.mul_comm; lia | lia]).
        replace (S n - 1) with n in Hstep by lia.
        rewrite Eq in Hstep. lia. }
      rewrite (IH p Hp), Hmp, Hsn, Nat.pow_succ_r'.
      rewrite List.seq_S, plw_fold_app.
      cbn [fold_right]. replace (1 + q) with (S q) by lia.
      ring.
    + apply Nat.eqb_neq in Em.
      pose proof (plw_div_step (S n) p ltac:(lia) Em) as Hstep.
      replace (S n - 1) with n in Hstep by lia.
      rewrite (IH p Hp), Hstep.
      change (fold_right Nat.mul 1 (@nil nat)) with 1. ring.
Qed.

(* p 自由部不含 p *)
Lemma plw_nonmult_nodvd : forall p n : nat, pr_prime p ->
  Nat.divide p (fold_right Nat.mul 1
    (filter (fun k => negb (plw_multp p k)) (seq 1 n))) -> False.
Proof.
  intros p n Hpp. induction n as [| n IH]; intros Hd.
  - cbn [seq filter fold_right] in Hd. apply Nat.divide_1_r in Hd.
    destruct Hpp as [H2 _]. lia.
  - rewrite List.seq_S in Hd.
    replace (1 + n) with (S n) in Hd by lia.
    rewrite List.filter_app in Hd. cbn [filter] in Hd.
    destruct (plw_multp p (S n)) eqn:Em.
    + cbn [negb filter] in Hd.
      rewrite plw_fold_app in Hd.
      change (fold_right Nat.mul 1 (@nil nat)) with 1 in Hd.
      rewrite Nat.mul_1_r in Hd.
      exact (IH Hd).
    + cbn [negb filter] in Hd.
      rewrite plw_fold_app in Hd.
      change (fold_right Nat.mul 1 (S n :: nil)) with (S n * 1) in Hd.
      rewrite Nat.mul_1_r in Hd.
      assert (Hpp1 : 1 <= p) by (destruct Hpp as [H2 _]; lia).
      destruct (plm_prime_dvd_mul p
                  (fold_right Nat.mul 1
                     (filter (fun k => negb (plw_multp p k)) (seq 1 n)))
                  (S n) Hpp Hd) as [H1 | H2].
      * exact (IH H1).
      * exact (plw_multp_false_inv p (S n) Hpp1 Em H2).
Qed.

(* 阶乘抽取式：fact n = p^(n/p)·fact(n/p)·(p 自由部) *)
Lemma plw_fact_extract : forall p n : nat, 2 <= p ->
  fact n = p ^ (n / p) * fact (n / p)
          * fold_right Nat.mul 1
              (filter (fun k => negb (plw_multp p k)) (seq 1 n)).
Proof.
  intros p n Hp.
  rewrite plw_fact_seq.
  rewrite (plw_fold_partition (plw_multp p) (seq 1 n)).
  rewrite (plw_mult_fold n p Hp).
  rewrite <- (plw_fact_seq (n / p)).
  reflexivity.
Qed.

(* 赋值递推：v_p(fact n) = n/p + v_p(fact (n/p))（n ≥ 1） *)
Lemma plw_v_fact_descent : forall p n : nat, pr_prime p -> 1 <= n ->
  plm_v p (fact n) = n / p + plm_v p (fact (n / p)).
Proof.
  intros p n [Hp2 Hpd] Hn.
  assert (Hp1 : 1 < p) by lia.
  pose proof (plw_fact_extract p n Hp2) as Hx.
  pose proof (plw_fact_pos n) as Hf1.
  pose proof (plw_fact_pos (n / p)) as Hf2.
  assert (HR1 : 1 <= fold_right Nat.mul 1
                  (filter (fun k => negb (plw_multp p k)) (seq 1 n)))
    by (apply plw_fold_pos; intros x Hx0; apply plw_filter_in in Hx0;
        destruct Hx0 as [Hx0 _]; apply in_seq in Hx0; lia).
  assert (HR0 : plm_v p (fold_right Nat.mul 1
                  (filter (fun k => negb (plw_multp p k)) (seq 1 n))) = 0).
  { destruct (plm_v p (fold_right Nat.mul 1
        (filter (fun k => negb (plw_multp p k)) (seq 1 n)))) as [| v] eqn:Ev;
      [reflexivity | exfalso].
    assert (Hd1 : Nat.divide (p ^ 1) (fold_right Nat.mul 1
                  (filter (fun k => negb (plw_multp p k)) (seq 1 n)))).
    { apply (proj2 (plw_v_char p (fold_right Nat.mul 1
            (filter (fun k => negb (plw_multp p k)) (seq 1 n))) 1 Hp1 HR1)).
      lia. }
    rewrite Nat.pow_1_r in Hd1.
    exact (plw_nonmult_nodvd p n (conj Hp2 Hpd) Hd1). }
  rewrite Hx.
  rewrite (plw_v_mul p (p ^ (n / p) * fact (n / p))
             (fold_right Nat.mul 1
                 (filter (fun k => negb (plw_multp p k)) (seq 1 n)))
             (conj Hp2 Hpd)
             (Nat.mul_le_mono _ _ _ _
                (plw_pow_pos p (n / p) ltac:(lia)) Hf2)
             HR1).
  rewrite (plw_v_mul p (p ^ (n / p)) (fact (n / p)) (conj Hp2 Hpd)
             (plw_pow_pos p (n / p) ltac:(lia)) Hf2).
  rewrite plw_pow_v_eq by exact Hp1.
  rewrite HR0, Nat.add_0_r. reflexivity.
Qed.

(* 阶乘区间切分：fact (a+b) = fact a · Π_{a+1}^{a+b} *)
Lemma plw_fact_split : forall a b : nat,
  fact (a + b) = fact a * fold_right Nat.mul 1 (seq (S a) b).
Proof.
  intros a b. induction b as [| b IH].
  - rewrite Nat.add_0_r, Nat.mul_1_r. reflexivity.
  - replace (a + S b) with (S (a + b)) by lia.
    cbn [fact].
    rewrite IH.
    rewrite List.seq_S, plw_fold_app.
    cbn [fold_right].
    replace (S a + b) with (a + S b) by lia.
    ring.
Qed.

(* 区间积与 h3_prod_from 的桥 *)
Lemma plw_h3_seq : forall a n : nat,
  h3_prod_from a n = fold_right Nat.mul 1 (seq a n).
Proof.
  intros a n. induction n as [| n IH].
  - reflexivity.
  - rewrite List.seq_S, plw_fold_app.
    cbn [fold_right h3_prod_from]. rewrite IH.
    ring.
Qed.

Lemma plw_v_1 : forall p : nat, 1 < p -> plm_v p 1 = 0.
Proof.
  intros p Hp. destruct (plm_v p 1) as [| v] eqn:Ev; [reflexivity | exfalso].
  assert (Hd : Nat.divide (p ^ S v) 1) by (rewrite <- Ev; apply plm_v_dvd).
  apply Nat.divide_1_r in Hd.
  assert (Hge : 2 <= p ^ S v).
  { apply plw_pow_ge2; lia. }
  lia.
Qed.

(* ---- §6 偶端/奇端配对归纳：层计数入二项式赋值 ---- *)

Lemma plw_E_pair : forall p a : nat, pr_prime p ->
  (plw_lvl_cnt p a (S a) a + 2 * plm_v p (fact a) <= plm_v p (fact (2 * a)))
  /\ (plw_lvl_cnt p a (S a) (S a) + 2 * plm_v p (fact a)
        <= plm_v p (fact (2 * a + 1))).
Proof.
  intros p a. induction a as [a IH] using Wf_nat.lt_wf_ind.
  intros Hpp.
  destruct a as [| m].
  - assert (Hp1 : 1 < p) by (destruct Hpp as [H2 _]; lia).
    split.
    + cbn [plw_lvl_cnt plw_lvl_list seq filter length fact].
      rewrite plw_v_1 by exact Hp1. lia.
    + cbn [plw_lvl_cnt plw_lvl_list seq filter length fact
           plw_lvl_pred plw_ispw plw_ispw_f Nat.eqb andb Nat.ltb Nat.leb].
      rewrite plw_v_1 by exact Hp1. lia.
  - assert (Hp2 : 2 <= p) by (destruct Hpp as [H2 _]; exact H2).
    assert (Hpp0 : 0 < p) by lia.
    remember (S m / p) as ad eqn:Ead.
    assert (Hltad : ad < S m).
    { rewrite Ead. apply Nat.div_lt; lia. }
    destruct (IH ad Hltad Hpp) as [IH2 IH3].
    split.
    + pose proof (plw_lvl_cnt_descent p (S m) (2 * S m) Hpp
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hdc.
      replace (2 * S m - S m) with (S m) in Hdc by lia.
      pose proof (plw_v_fact_descent p (2 * S m) Hpp ltac:(lia)) as Hv2.
      pose proof (plw_v_fact_descent p (S m) Hpp ltac:(lia)) as Hv1.
      pose proof (plw_div2_even (S m) p Hpp0) as Hb2.
      rewrite <- Ead in Hb2.
      pose proof (plw_cnt_exp_bound p (S m) (2 * S m) Hpp
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hal.
      rewrite <- Ead in Hal.
      destruct Hb2 as [Hb2 | Hb2].
      * rewrite Hb2 in Hv2, Hdc, Hal.
        replace (2 * ad - S m / p) with ad in Hdc by lia.
        rewrite Hdc, Hv2, Hv1.
        rewrite <- Ead.
        lia.
      * rewrite Hb2 in Hv2, Hdc, Hal.
        replace (2 * ad + 1 - S m / p) with (S ad) in Hdc by lia.
        rewrite Hdc, Hv2, Hv1.
        rewrite <- Ead.
        lia.
    + pose proof (plw_lvl_cnt_descent p (S m) (2 * S m + 1) Hpp
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hdc.
      replace (2 * S m + 1 - S m) with (S (S m)) in Hdc by lia.
      pose proof (plw_v_fact_descent p (2 * S m + 1) Hpp ltac:(lia)) as Hv3.
      pose proof (plw_v_fact_descent p (S m) Hpp ltac:(lia)) as Hv1.
      pose proof (plw_div2_odd (S m) p Hpp0) as Hb3.
      rewrite <- Ead in Hb3.
      pose proof (plw_cnt_exp_bound p (S m) (2 * S m + 1) Hpp
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hal.
      rewrite <- Ead in Hal.
      destruct Hb3 as [Hb3 | Hb3].
      * rewrite Hb3 in Hv3, Hdc, Hal.
        replace (2 * ad - S m / p) with ad in Hdc by lia.
        rewrite Hdc, Hv3, Hv1.
        rewrite <- Ead.
        lia.
      * rewrite Hb3 in Hv3, Hdc, Hal.
        replace (2 * ad + 1 - S m / p) with (S ad) in Hdc by lia.
        rewrite Hdc, Hv3, Hv1.
        rewrite <- Ead.
        lia.
Qed.

(* ---- §7 勘形切片三：v_p(C(2m,m)) ≥ 环带层数 ---- *)

Theorem plw_binom_ge_annulus_levels : forall p m : nat,
  pr_prime p -> 1 <= m ->
  plw_lvl_cnt p m (S m) m <= plm_v p (hl_binom (2 * m) m).
Proof.
  intros p m Hpp Hm.
  destruct (plw_E_pair p m Hpp) as [HE2 _].
  assert (Hid : hl_binom (2 * m) m * fact m * fact m = fact (2 * m)).
  { replace (2 * m) with (m + m) by lia.
    rewrite plw_fact_split, <- plw_h3_seq, h3_prod_binom_fact.
    ring. }
  rewrite <- Hid in HE2.
  rewrite (plw_v_mul p (hl_binom (2 * m) m * fact m) (fact m) Hpp
             (Nat.mul_le_mono _ _ _ _ (plw_binom_pos (2 * m) m ltac:(lia))
                (plw_fact_pos m))
             (plw_fact_pos m)) in HE2.
  rewrite (plw_v_mul p (hl_binom (2 * m) m) (fact m) Hpp
             (plw_binom_pos (2 * m) m ltac:(lia)) (plw_fact_pos m)) in HE2.
  lia.
Qed.

(* ---- §8 指数桥：maxpow(2m) ≤ maxpow(m) ＋ 层数计数 ---- *)

Lemma plw_maxpow_split : forall p m j : nat, pr_prime p -> 1 <= m ->
  p ^ j <= 2 * m -> j <= plw_maxpow p m + plw_lvl_cnt p m (S m) m.
Proof.
  intros p m j [Hp2 Hpd] Hm Hpj.
  assert (Hp1 : 1 < p) by lia.
  set (l1 := filter (fun i => Nat.leb (p ^ i) m) (seq 1 j)).
  set (l2 := filter (fun i => negb (Nat.leb (p ^ i) m)) (seq 1 j)).
  assert (Hpart : length l1 + length l2 = j).
  { unfold l1, l2.
    pose proof (plw_filter_partition (fun i => Nat.leb (p ^ i) m) (seq 1 j)) as Hp0.
    rewrite plw_length_seq in Hp0. exact Hp0. }
  assert (Hl1 : length l1 <= plw_maxpow p m).
  { assert (Hnd : NoDup l1) by (unfold l1; apply NoDup_filter; apply seq_NoDup).
    assert (Hincl : incl l1 (seq 1 (plw_maxpow p m))).
    { intros i Hi. unfold l1 in Hi. apply plw_filter_in in Hi.
      destruct Hi as [Hin Hleb]. apply Nat.leb_le in Hleb.
      apply in_seq in Hin. destruct Hin as [Hgei Hij].
      apply in_seq. split; [lia |].
      destruct (le_lt_dec i (plw_maxpow p m)) as [Hle | Hgt]; [lia |].
      exfalso.
      pose proof (plw_maxpow_ceil p m Hp1) as Hcl.
      assert (Hpj2 : p ^ S (plw_maxpow p m) <= p ^ i)
        by (apply Nat.pow_le_mono_r; lia).
      lia. }
    apply Nat.le_trans with (length (seq 1 (plw_maxpow p m))).
    - apply NoDup_incl_length; assumption.
    - rewrite plw_length_seq. apply Nat.le_refl. }
  assert (Hl2 : length l2 <= plw_lvl_cnt p m (S m) m).
  { assert (Hmap : NoDup (map (fun i => p ^ i) l2)).
    { apply plw_NoDup_map_inj.
      - unfold l2. intros x y Hx Hy Hf.
        apply plw_filter_in in Hx. apply plw_filter_in in Hy.
        destruct Hx as [Hx _]. destruct Hy as [Hy _].
        apply in_seq in Hx. apply in_seq in Hy.
        destruct (le_lt_dec x y) as [Hle | Hlt].
        + destruct (Nat.eq_dec x y) as [Exy | Nxy]; [exact Exy |].
          exfalso. assert (Hxy : x < y) by lia.
          pose proof (plw_pow_lt_mono p x y Hp1 Hxy). lia.
        + exfalso. pose proof (plw_pow_lt_mono p y x Hp1 Hlt). lia.
      - unfold l2. apply NoDup_filter. apply seq_NoDup. }
    assert (Hincl : incl (map (fun i => p ^ i) l2) (plw_lvl_list p m (S m) m)).
    { intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [Hxi Hin]].
      unfold l2 in Hin. apply plw_filter_in in Hin.
      destruct Hin as [Hin Hnb]. apply negb_true_iff in Hnb.
      apply Nat.leb_gt in Hnb.
      unfold plw_lvl_list. apply plw_filter_in_rev.
      - apply in_seq. split.
        + lia.
        + assert (Hpi2 : p ^ i <= 2 * m).
          { apply Nat.le_trans with (p ^ j); [| exact Hpj].
            apply Nat.pow_le_mono_r; [lia |].
            apply in_seq in Hin. lia. }
          lia.
      - unfold plw_lvl_pred. apply andb_true_iff. split.
        + apply Nat.ltb_lt. rewrite <- Hxi. exact Hnb.
        + rewrite <- Hxi. apply plw_ispw_pow; [lia |]. apply in_seq in Hin. lia. }
    pose proof (NoDup_incl_length Hmap Hincl) as Hlen.
    rewrite plw_len_map in Hlen.
    unfold plw_lvl_cnt. exact Hlen. }
  rewrite <- Hpart.
  lia.
Qed.

(* ---- §9 锐化逐素步：p^maxpow(2m) ∣ L(m)·C(2m,m)（无 p 余量） ---- *)

Theorem plw_lcm2m_pow_dvd_sharp : forall p m : nat, pr_prime p -> 1 <= m ->
  Nat.divide (p ^ plw_maxpow p (2 * m))
             (hl_lcm_upto m * hl_binom (2 * m) m).
Proof.
  intros p m Hpp Hm.
  assert (Hp1 : 1 < p) by (destruct Hpp as [H2 _]; lia).
  pose proof (plw_maxpow_dvd_upto p (2 * m)) as Hdu.
  destruct Hdu as [Hle2 | Hzero]; [| exfalso; lia].
  pose proof (plw_maxpow_split p m (plw_maxpow p (2 * m)) Hpp Hm Hle2) as Hsplit.
  assert (Hd1 : Nat.divide (p ^ plw_maxpow p m) (hl_lcm_upto m)).
  { apply (proj2 (plw_pow_dvd_lcm_iff p m (plw_maxpow p m) Hpp Hm)).
    destruct (plw_maxpow_dvd_upto p m) as [H | H0]; [exact H | exfalso; lia]. }
  assert (Hd2 : Nat.divide (p ^ plw_lvl_cnt p m (S m) m) (hl_binom (2 * m) m)).
  { apply (proj2 (plw_v_char p (hl_binom (2 * m) m)
             (plw_lvl_cnt p m (S m) m) Hp1
             (plw_binom_pos (2 * m) m ltac:(lia)))).
    apply plw_binom_ge_annulus_levels; assumption. }
  assert (Hcomb : Nat.divide
                    (p ^ (plw_maxpow p m + plw_lvl_cnt p m (S m) m))
                    (hl_lcm_upto m * hl_binom (2 * m) m)).
  { rewrite Nat.pow_add_r. apply plw_dvd_mul_mono; assumption. }
  apply (Nat.divide_trans (p ^ plw_maxpow p (2 * m))
           (p ^ (plw_maxpow p m + plw_lvl_cnt p m (S m) m)));
    [apply plw_pow_le_dvd; lia | exact Hcomb].
Qed.

(* ---- §10 勘形切片四：商抽取与逐素幂界 ---- *)

Lemma plw_dvd_lcm_l : forall a b : nat, Nat.divide a (Nat.lcm a b).
Proof.
  intros a b. unfold Nat.lcm.
  exists (b / Nat.gcd a b). ring.
Qed.

Lemma plw_lcm_upto_dvd_mono : forall n k : nat,
  Nat.divide (hl_lcm_upto n) (hl_lcm_upto (n + k)).
Proof.
  intros n k. induction k as [| k IH].
  - rewrite Nat.add_0_r. apply Nat.divide_refl.
  - replace (n + S k) with (S (n + k)) by lia.
    cbn [hl_lcm_upto].
    apply (Nat.divide_trans (hl_lcm_upto n) (hl_lcm_upto (n + k))).
    + exact IH.
    + apply plw_dvd_lcm_l.
Qed.

Theorem plw_lcm2m_split : forall m : nat, 1 <= m ->
  exists M : nat, hl_lcm_upto (2 * m) = hl_lcm_upto m * M /\
    (forall p : nat, pr_prime p ->
       Nat.divide (p ^ plm_v p M) (hl_binom (2 * m) m)).
Proof.
  intros m Hm.
  assert (Hmono : Nat.divide (hl_lcm_upto m) (hl_lcm_upto (2 * m))).
  { replace (2 * m) with (m + m) by lia. apply plw_lcm_upto_dvd_mono. }
  destruct Hmono as [M Hd].
  exists M. split.
  - rewrite Hd. ring.
  - intros p Hpp.
    assert (Hp1 : 1 < p) by (destruct Hpp as [H2 _]; lia).
    assert (HposM : 1 <= M).
    { destruct M as [| M']; [| lia].
      exfalso. pose proof (plw_lcm_pos (2 * m)) as Hp2.
      rewrite Hd, Nat.mul_0_l in Hp2. lia. }
    assert (HL : 1 <= hl_lcm_upto m) by apply plw_lcm_pos.
    assert (HC : 1 <= hl_binom (2 * m) m) by (apply plw_binom_pos; lia).
    assert (Hval : plw_maxpow p (2 * m) = plw_maxpow p m + plm_v p M).
    { rewrite <- (plw_v_lcm_upto p (2 * m) Hpp).
      rewrite Hd.
      rewrite (plw_v_mul p M (hl_lcm_upto m) Hpp HposM HL).
      rewrite <- (plw_v_lcm_upto p m Hpp).
      lia. }
    pose proof (plw_lcm2m_pow_dvd_sharp p m Hpp Hm) as Hsharp.
    assert (HvC : plw_maxpow p (2 * m)
                  <= plm_v p (hl_lcm_upto m * hl_binom (2 * m) m)).
    { apply (plw_v_le_dvd p (hl_lcm_upto m * hl_binom (2 * m) m)
               (plw_maxpow p (2 * m)) Hp1).
      - apply Nat.le_trans with (1 * 1); [lia |].
        apply Nat.mul_le_mono; assumption.
      - exact Hsharp. }
    rewrite (plw_v_mul p (hl_lcm_upto m) (hl_binom (2 * m) m) Hpp HL HC) in HvC.
    rewrite <- (plw_v_lcm_upto p m Hpp) in Hval.
    apply (proj2 (plw_v_char p (hl_binom (2 * m) m) (plm_v p M) Hp1 HC)).
    lia.
Qed.

(* ---- §11 全局合并机：逐素幂界则整体整除 ---- *)

(* 素整除幂 ⟹ 底相等 *)
Lemma plw_prime_dvd_pow_eq : forall p q d : nat,
  pr_prime p -> pr_prime q -> Nat.divide q (p ^ d) -> p = q.
Proof.
  intros p q d [Hp2 Hpd] [Hq2 Hqd] Hd.
  assert (Hqle : q <= p ^ d)
    by (apply Nat.divide_pos_le; [apply plw_pow_pos; lia | exact Hd]).
  induction d as [| d IH].
  - rewrite Nat.pow_0_r in Hqle. lia.
  - destruct (plm_prime_dvd_mul q p (p ^ d) (conj Hq2 Hqd) Hd) as [H | H].
    + assert (Hqp : q <= p)
        by (apply Nat.divide_pos_le; [lia | exact H]).
      destruct (le_lt_dec p q) as [Hge | Hlt].
      * lia.
      * exfalso. exact (Hpd q Hq2 Hlt H).
    + assert (Hqle2 : q <= p ^ d)
        by (apply Nat.divide_pos_le; [apply plw_pow_pos; lia | exact H]).
      exact (IH H Hqle2).
Qed.

(* 相异底：r 幂的 r 赋值为零（诚实修复：p 须素——原语句 p=4,r=2 反例） *)
Lemma plw_v_pow_zero : forall r p d : nat,
  pr_prime r -> pr_prime p -> (p = r -> False) -> plm_v r (p ^ d) = 0.
Proof.
  intros r p d [Hr2 Hrd] [Hp2 Hpd] Hne.
  assert (Hp1 : 1 < r) by lia.
  destruct (plm_v r (p ^ d)) as [| v] eqn:Ev; [reflexivity | exfalso].
  assert (Hk1 : 1 <= p ^ d).
  { destruct (Nat.eq_dec (p ^ d) 0) as [Ez | Ez]; [| lia].
    exfalso. rewrite Ez in Ev.
    change (plm_v r 0) with 0 in Ev. discriminate. }
  assert (Hd1 : Nat.divide (r ^ 1) (p ^ d)).
  { apply (proj2 (plw_v_char r (p ^ d) 1 Hp1 Hk1)). lia. }
  assert (Hrd2 : Nat.divide r (p ^ d)).
  { apply (Nat.divide_trans r (r ^ 1) (p ^ d));
      [rewrite Nat.pow_1_r; apply Nat.divide_refl | exact Hd1]. }
  apply Hne. exact (plw_prime_dvd_pow_eq p r d (conj Hp2 Hpd) (conj Hr2 Hrd) Hrd2).
Qed.

(* 素幂与无该素部互素 *)
Lemma plw_gcd_powcoprime : forall p d x : nat,
  pr_prime p -> (Nat.divide p x -> False) -> Nat.gcd (p ^ d) x = 1.
Proof.
  intros p d x [Hp2 Hpd] Hnd.
  destruct (Nat.eq_dec (Nat.gcd (p ^ d) x) 1) as [E1 | NE1]; [exact E1 |].
  exfalso.
  assert (Hg1 : 1 <= Nat.gcd (p ^ d) x).
  { apply Nat.neq_0_lt_0. intro Hz.
    assert (Hgd : Nat.divide (Nat.gcd (p ^ d) x) (p ^ d))
      by apply Nat.gcd_divide_l.
    rewrite Hz in Hgd. apply Nat.divide_0_l in Hgd.
    pose proof (plw_pow_pos p d ltac:(lia)) as Hpos. lia. }
  assert (Hg2 : 2 <= Nat.gcd (p ^ d) x) by lia.
  destruct (pr_min_factor_exists (Nat.gcd (p ^ d) x) Hg2) as [r [Hrg Hrr]].
  assert (Hrpd : Nat.divide r (p ^ d)).
  { apply (Nat.divide_trans r (Nat.gcd (p ^ d) x) (p ^ d));
      [exact Hrg | apply Nat.gcd_divide_l]. }
  assert (Hpr : p = r)
    by (apply (plw_prime_dvd_pow_eq p r d);
        [exact (conj Hp2 Hpd) | exact Hrr | exact Hrpd]).
  apply Hnd. apply (Nat.divide_trans p (Nat.gcd (p ^ d) x) x).
  - rewrite <- Hpr in Hrg. exact Hrg.
  - apply Nat.gcd_divide_r.
Qed.

(* 全局合并：每素幂位入 C 则整体入 C（最小素因子强归纳） *)
Theorem plw_dvd_of_prime_pows : forall M C : nat,
  1 <= M ->
  (forall p : nat, pr_prime p -> Nat.divide p M ->
     Nat.divide (p ^ plm_v p M) C) ->
  Nat.divide M C.
Proof.
  intro M. induction M as [M IH] using Wf_nat.lt_wf_ind.
  intros C Hm Hpow.
  destruct M as [| M'].
  - exfalso. lia.
  - destruct (Nat.eq_dec (S M') 1) as [E1 | Hne].
    + rewrite E1. apply Nat.divide_1_l.
    + assert (Hm2 : 2 <= S M') by lia.
      destruct (pr_min_factor_exists (S M') Hm2) as [p [Hpm Hpp]].
      assert (Hp1 : 1 < p) by (destruct Hpp as [Hp2 _]; lia).
      remember (plm_v p (S M')) as vpp eqn:Evpp.
      pose proof Hpow as Hpow0.
      specialize (Hpow p Hpp Hpm).
      assert (Hdv : Nat.divide (p ^ plm_v p (S M')) (S M')) by apply plm_v_dvd.
      destruct Hdv as [q Hq].
      assert (Hq1 : 1 <= q).
      { destruct q as [| q']; [| lia].
        rewrite Nat.mul_0_l in Hq. lia. }
      assert (Hpnd : Nat.divide p q -> False).
      { intros [t Ht].
        remember (plm_v p (S M')) as w eqn:Ew.
        assert (Hbig : Nat.divide (p ^ S w) (S M')).
        { rewrite Hq. exists t. rewrite Ht, Nat.pow_succ_r'. ring. }
        rewrite Ew in Hbig.
        exact (plm_v_max p (S M') Hp1 ltac:(lia) Hbig). }
      assert (HMlt : q < S M').
      { rewrite Hq.
        assert (Hv1 : 1 <= plm_v p (S M')).
        { destruct (plm_v p (S M')) eqn:Evw; [| lia].
          exfalso. apply (plm_v_max p (S M') Hp1 ltac:(lia)).
          rewrite Evw, Nat.pow_1_r. exact Hpm. }
        assert (H2p : 2 <= p ^ plm_v p (S M')) by (apply plw_pow_ge2; lia).
        assert (Hq2 : q * 1 < q * p ^ plm_v p (S M')).
        { apply (proj1 (Nat.mul_lt_mono_pos_l q 1 (p ^ plm_v p (S M')) ltac:(lia))); lia. }
        rewrite Nat.mul_1_r in Hq2. exact Hq2. }
      assert (HqM : Nat.divide q (S M')).
      { exists (p ^ plm_v p (S M')). rewrite Hq at 1. ring. }
      assert (HqC : Nat.divide q C).
      { apply (IH q HMlt C Hq1).
        intros r Hrr Hrq.
        specialize (Hpow0 r Hrr (Nat.divide_trans r q (S M') Hrq HqM)).
        assert (Hne2 : p = r -> False).
        { intro Hpr. rewrite <- Hpr in Hrq. exact (Hpnd Hrq). }
        assert (Hvr : plm_v r (S M') = plm_v r q).
        { rewrite Hq.
          rewrite (plw_v_mul r q (p ^ plm_v p (S M')) Hrr Hq1
                     (plw_pow_pos p (plm_v p (S M')) ltac:(lia))).
          rewrite (plw_v_pow_zero r p (plm_v p (S M')) Hrr Hpp Hne2). lia. }
        rewrite <- Hvr. exact Hpow0. }
      assert (Hgcd : Nat.gcd (p ^ plm_v p (S M')) q = 1)
        by (apply (plw_gcd_powcoprime p (plm_v p (S M')) q); [exact Hpp | exact Hpnd]).
      assert (Hfin : Nat.divide (p ^ plm_v p (S M') * q) C).
      { apply (plm_dvd_mul_coprime (p ^ plm_v p (S M')) q C); [exact Hpow | exact HqC | exact Hgcd]. }
      remember (p ^ plm_v p (S M') * q) as B2 eqn:EB2.
      assert (Hsq : S M' = q * p ^ plm_v p (S M')) by (rewrite Hq at 1; reflexivity).
      clear Hq. rename Hsq into Hq.
      assert (HB2 : B2 = p ^ plm_v p (S M') * q) by (rewrite EB2; ring).
      clear EB2.
      apply (Nat.divide_trans (S M') B2 C).
      * rewrite Hq. rewrite HB2. exists 1. ring.
      * exact Hfin.
Qed.

(* ---- §12 勘形切片五：全局单一整除形装配 ---- *)

Theorem plw_lcm2m_divide : forall m : nat, 1 <= m ->
  Nat.divide (hl_lcm_upto (2 * m)) (hl_binom (2 * m) m * hl_lcm_upto m).
Proof.
  intros m Hm.
  destruct (plw_lcm2m_split m Hm) as [M [Heq Hpp]].
  assert (HM : Nat.divide M (hl_binom (2 * m) m)).
  { apply (plw_dvd_of_prime_pows M (hl_binom (2 * m) m)).
    - destruct M as [| M']; [| lia].
      exfalso. pose proof (plw_lcm_pos (2 * m)) as Hp2.
      rewrite Heq, Nat.mul_0_r in Hp2. lia.
    - intros p Hp _. apply Hpp. exact Hp. }
  rewrite Heq, (Nat.mul_comm (hl_binom (2 * m) m) (hl_lcm_upto m)).
  apply plw_dvd_mul_mono; [apply Nat.divide_refl | exact HM].
Qed.

(* ---- §13 数值定装烟测（小实例 vm_compute 零公设） ---- *)

Lemma plw_ispw_smoke_2_8 : plw_ispw 2 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_ispw_smoke_2_12 : plw_ispw 2 12 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_ispw_smoke_3_9 : plw_ispw 3 9 = true.
Proof. vm_compute. reflexivity. Qed.

(* 环带层数计数：p=2 时 (5,10] 内层值 {8} 计 1；(2,4] 内 {4} 计 1 *)
Lemma plw_lvl_cnt_smoke_2_5 : plw_lvl_cnt 2 5 6 5 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_lvl_cnt_smoke_2_2 : plw_lvl_cnt 2 2 3 2 = 1.
Proof. vm_compute. reflexivity. Qed.

(* 主定理实例：L(10)=2520 ∣ C(10,5)·L(5)=252·60；L(6)=60 ∣ 20·3 *)
Lemma plw_lcm2m_divide_smoke_5 :
  Nat.eqb ((hl_binom 10 5 * hl_lcm_upto 5) mod hl_lcm_upto 10) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_lcm2m_divide_smoke_3 :
  Nat.eqb ((hl_binom 6 3 * hl_lcm_upto 3) mod hl_lcm_upto 6) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- §14 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions plw_coprime_fold_dvd.
Print Assumptions plw_pow_coprime_of_prime_coprime.
Print Assumptions plw_ispw_sound.
Print Assumptions plw_ispw_pow.
Print Assumptions plw_lvl_pred_pow.
Print Assumptions plw_lvl_cnt_descent.
Print Assumptions plw_cnt_exp_bound.
Print Assumptions plw_v_fact_descent.
Print Assumptions plw_E_pair.
Print Assumptions plw_binom_ge_annulus_levels.
Print Assumptions plw_maxpow_split.
Print Assumptions plw_lcm2m_pow_dvd_sharp.
Print Assumptions plw_lcm2m_split.
Print Assumptions plw_dvd_of_prime_pows.
Print Assumptions plw_lcm2m_divide.
Print Assumptions plw_ispw_smoke_2_8.

(* ---- §15 提取检查（Separate Extraction：可执行核直提） ---- *)

From Stdlib Require Import Extraction.
Separate Extraction plw_ispw.
