(* ============================================================ *)
(* 模块名：abl_Pr_enum_02 —— 素数域成域件单第 3 件（素数枚举＋primorial＋互素） *)
(* 使命：nat 层素数枚举面四组——①素数计数机 pen_count_upto（[2,n] 内  *)
(*   素数个数）＋pen_count_seg（(m,m+d] 内素数个数）＋可加性 split    *)
(*   与「无素则零／唯一素则一」两向引理；②下一素数搜索               *)
(*   pen_next_prime（燃料递降、起点升扫，pr_prime_bool 判定）＋四联   *)
(*   正确性 spec（返回素、在窗内、窗内最小素）；③第 k 素枚举器       *)
(*   pen_nth_prime（第 k 槽结构递归，第 0 槽回退 1）＋spec 双件＋     *)
(*   sigT 见证形 pen_nth_prime_exists（Defined）；④素数列表与        *)
(*   primorial 互素面：pen_primes_upto（升序素数表）＋In 刻画＋       *)
(*   pen_primorial（不大于 n 的素数之积）＋primorial 后继互素构造性   *)
(*   版（Euclid 结构枚举侧形态，n!+1 线平行）＋pen_euclid_new_prime   *)
(*   （对每个 n 构造性给出整除 primorial n + 1 且大于 n 的新素，      *)
(*   sigT Defined）＋素数无界 pen_prime_unbounded＋相异素数互素       *)
(*   pen_coprime_of_neq。设计依据：素数域成域件单设计文书 §成域件单。 *)
(* 依赖清单：件 1（abl_Pr_core_01，同池供 Require）＋纯 Stdlib        *)
(*   （Arith.Arith／List／Bool／Lia）。零其他项目件。                 *)
(* 构造性注记：Set 面承载——三件主语句 sigT 见证形（pen_nth_prime_    *)
(*   exists／pen_euclid_new_prime／pen_prime_unbounded，皆 Defined）；*)
(*   「互素」以整除消去形承载（primorial 后继面：凡整除 primorial n   *)
(*   且整除其后继者必为一）；否定形自持 P -> False（本安装无 Not，    *)
(*   全件零否定记号与不等号书写）；零公理零承认零经典逻辑；           *)
(*   计算件 pen_count_upto／pen_count_seg／pen_next_prime／           *)
(*   pen_nth_prime／pen_primes_upto／pen_primorial 皆一阶 nat／bool／ *)
(*   list Fixpoint 可提取；燃料充足性以「窗内存在第 k 素」假设形      *)
(*   诚实承载；数值定装走小实例 vm_compute（实例 ≤ 10）。             *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB &&      *)
(*   ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q <池>，  *)
(*   先编 abl_Pr_core_01.v 再同配方编本件（件 1 由本池路径供 Require）。*)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.

(* ---- §1 素数计数机（「第 k 个」的可计算形式化基础） ----
   pen_count_upto n = [2, n] 内素数个数；
   pen_count_seg m d = (m, m + d] 内素数个数。 *)

Fixpoint pen_count_upto (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => pen_count_upto m + (if pr_prime_bool (S m) then 1 else 0)
  end.

Fixpoint pen_count_seg (m d : nat) : nat :=
  match d with
  | 0 => 0
  | S d' => pen_count_seg m d' + (if pr_prime_bool (m + S d') then 1 else 0)
  end.

(* 定义展开式（结构等式，免 simpl 误展开判定器） *)
Lemma pen_count_upto_S : forall m : nat,
  pen_count_upto (S m) =
  pen_count_upto m + (if pr_prime_bool (S m) then 1 else 0).
Proof. reflexivity. Qed.

Lemma pen_count_seg_S : forall m d : nat,
  pen_count_seg m (S d) =
  pen_count_seg m d + (if pr_prime_bool (m + S d) then 1 else 0).
Proof. reflexivity. Qed.

(* 计数可加性：[2, n+d] 素数个数 = [2, n] 个数 + (n, n+d] 个数 *)
Lemma pen_count_split : forall n d : nat,
  pen_count_upto (n + d) = pen_count_upto n + pen_count_seg n d.
Proof.
  intros n d. induction d as [|d IH].
  - rewrite Nat.add_0_r. change (pen_count_seg n 0) with 0.
    rewrite Nat.add_0_r. reflexivity.
  - assert (Hs : n + S d = S (n + d)) by apply Nat.add_succ_r.
    rewrite Hs. rewrite pen_count_upto_S. rewrite pen_count_seg_S.
    rewrite <- Hs. rewrite IH. symmetry. apply Nat.add_assoc.
Qed.

(* 窗内无素则计数为零（反向：无素窗口计数归零） *)
Lemma pen_count_seg_none : forall d m : nat,
  (forall q : nat, pr_prime q -> m < q -> q <= m + d -> False) ->
  pen_count_seg m d = 0.
Proof.
  intros d. induction d as [|d IH]; intros m Hnone.
  - reflexivity.
  - rewrite pen_count_seg_S.
    assert (Hb0 : pr_prime_bool (m + S d) = false).
    { destruct (pr_prime_bool (m + S d)) eqn:Eb; [|reflexivity].
      exfalso. apply (Hnone (m + S d)).
      - apply pr_prime_bool_true. exact Eb.
      - lia.
      - lia. }
    rewrite Hb0. change (if false then 1 else 0) with 0.
    rewrite Nat.add_0_r. apply IH.
    intros q Hq Hmq Hqle.
    destruct (Nat.eq_dec q (m + S d)) as [Hqe|Hqne].
    + exfalso. rewrite Hqe in Hq.
      rewrite (pr_prime_bool_false _ Hq) in Hb0. discriminate.
    + apply (Hnone q Hq Hmq). lia.
Qed.

(* 窗内恰有一素（唯一素 p 落窗）则计数为一 *)
Lemma pen_count_seg_one : forall d m p : nat, pr_prime p -> m < p -> p <= m + d ->
  (forall q : nat, pr_prime q -> m < q -> q <= m + d -> q = p) ->
  pen_count_seg m d = 1.
Proof.
  intros d. induction d as [|d IH]; intros m p Hp Hmp Hple Huniq.
  - lia.
  - rewrite pen_count_seg_S.
    destruct (le_lt_dec p (m + d)) as [Hpd|Hplt].
    + (* p 落内窗：外端点 m + S d 必非素，δ = 0，由 IH 即得 *)
      assert (Hb0 : pr_prime_bool (m + S d) = false).
      { destruct (pr_prime_bool (m + S d)) eqn:Eb; [|reflexivity].
        exfalso.
        assert (Hpmd : pr_prime (m + S d)) by (apply pr_prime_bool_true; exact Eb).
        assert (Heq : m + S d = p) by (apply (Huniq (m + S d) Hpmd); lia).
        lia. }
      rewrite Hb0. change (if false then 1 else 0) with 0.
      rewrite Nat.add_0_r. apply (IH m p Hp Hmp Hpd).
      intros q Hq Hmq Hqle. apply (Huniq q Hq); [exact Hmq | lia].
    + (* p = m + S d：内窗无素（否则违唯一），δ = 1 *)
      assert (Heq : p = m + S d) by lia.
      assert (Hb : pr_prime_bool (m + S d) = true).
      { apply pr_prime_bool_false. rewrite <- Heq. exact Hp. }
      assert (Hseg0 : pen_count_seg m d = 0).
      { apply pen_count_seg_none. intros q Hq Hmq Hqle.
        assert (Hqe : q = p) by (apply (Huniq q Hq); [exact Hmq | lia]).
        lia. }
      rewrite Hb. change (if true then 1 else 0) with 1.
      rewrite Hseg0. reflexivity.
Qed.

(* 计数基本件：1 处读数、素点步进、单调、最大素提取、素上严格单调与单射 *)
Lemma pen_count_upto_1 : pen_count_upto 1 = 0.
Proof. reflexivity. Qed.

Lemma pen_count_upto_step : forall n : nat, 1 <= n -> pr_prime n ->
  pen_count_upto n = pen_count_upto (n - 1) + 1.
Proof.
  intros n Hn Hp. destruct n as [|m]; [exfalso; lia|].
  rewrite pen_count_upto_S.
  assert (Hb : pr_prime_bool (S m) = true) by (apply pr_prime_bool_false; exact Hp).
  rewrite Hb. change (if true then 1 else 0) with 1.
  assert (Hsm : S m - 1 = m) by lia. rewrite Hsm. reflexivity.
Qed.

Lemma pen_count_mono : forall a b : nat, a <= b -> pen_count_upto a <= pen_count_upto b.
Proof.
  intros a b. induction b as [|m IH]; intros Hab.
  - assert (Ha0 : a = 0) by lia. subst a. apply Nat.le_refl.
  - destruct (Nat.eq_dec a (S m)) as [Hae|Hane].
    + rewrite Hae. apply Nat.le_refl.
    + assert (Ham : a <= m) by lia.
      specialize (IH Ham). rewrite pen_count_upto_S. lia.
Qed.

(* 素数计数非零则存在不大于 n 的最大素（计数读数不变） *)
Lemma pen_count_upto_largest : forall n : nat, 1 <= pen_count_upto n ->
  exists r : nat, pr_prime r /\ r <= n /\ pen_count_upto r = pen_count_upto n.
Proof.
  intros n. induction n as [|m IH]; intros Hpos.
  - exfalso. simpl in Hpos. lia.
  - destruct (pr_prime_bool (S m)) eqn:Hb.
    + exists (S m). split.
      * apply pr_prime_bool_true. exact Hb.
      * split; [lia | reflexivity].
    + assert (Hcount : pen_count_upto (S m) = pen_count_upto m).
      { rewrite pen_count_upto_S, Hb. change (if false then 1 else 0) with 0.
        rewrite Nat.add_0_r. reflexivity. }
      assert (Hpos' : 1 <= pen_count_upto m) by (rewrite Hcount in Hpos; exact Hpos).
      destruct (IH Hpos') as [r [Hr [Hrle Hrc]]].
      exists r. split; [exact Hr |]. split; [lia |]. rewrite Hcount. exact Hrc.
Qed.

(* 素上计数严格单调：p 与 r 皆素且 p 小于 r 则读数严格小 *)
Lemma pen_count_lt_prime : forall p r : nat, pr_prime p -> pr_prime r -> p < r ->
  pen_count_upto p < pen_count_upto r.
Proof.
  intros p r [Hp2 Hpd] [Hr2 Hrd] Hlt.
  assert (Hstep : pen_count_upto r = pen_count_upto (r - 1) + 1).
  { apply (pen_count_upto_step r); [lia | split; [exact Hr2 | exact Hrd]]. }
  assert (Hmono : pen_count_upto p <= pen_count_upto (r - 1)) by (apply pen_count_mono; lia).
  lia.
Qed.

(* 计数在素数上单射：两素读数相等则相等 *)
Lemma pen_count_inj : forall p r : nat, pr_prime p -> pr_prime r ->
  pen_count_upto p = pen_count_upto r -> p = r.
Proof.
  intros p r Hp Hr Heq.
  destruct (lt_eq_lt_dec p r) as [[Hlt|Heqr]|Hgt].
  - exfalso.
    assert (Hltc : pen_count_upto p < pen_count_upto r)
      by (apply (pen_count_lt_prime p r Hp Hr Hlt)).
    lia.
  - exact Heqr.
  - exfalso.
    assert (Hgtc : pen_count_upto r < pen_count_upto p)
      by (apply (pen_count_lt_prime r p Hr Hp Hgt)).
    lia.
Qed.

(* ---- §2 下一素数搜索（燃料 f 递降、起点 m 升扫，pr_prime_bool 判定） ----
   pen_next_prime f m：在窗 [m, m + f) 内升扫取首个素数；燃料尽回退 0。 *)

Fixpoint pen_next_prime (f m : nat) : nat :=
  match f with
  | 0 => 0
  | S f' => if pr_prime_bool m then m else pen_next_prime f' (S m)
  end.

Lemma pen_next_prime_S : forall f m : nat,
  pen_next_prime (S f) m =
  (if pr_prime_bool m then m else pen_next_prime f (S m)).
Proof. reflexivity. Qed.

(* 四联正确性：窗内确有素则返回值素、起点达标、落窗内、且为窗内最小素 *)
Theorem pen_next_prime_spec : forall f m : nat,
  (exists q : nat, pr_prime q /\ m <= q /\ q < m + f) ->
  pr_prime (pen_next_prime f m) /\
  m <= pen_next_prime f m /\
  pen_next_prime f m < m + f /\
  (forall q : nat, pr_prime q -> m <= q -> pen_next_prime f m <= q).
Proof.
  intros f. induction f as [|f IH]; intros m Hget.
  - exfalso. destruct Hget as [q [Hq [Hq1 Hq2]]]. lia.
  - rewrite pen_next_prime_S. destruct (pr_prime_bool m) eqn:Hb.
    + change (if true then m else pen_next_prime f (S m)) with m.
      split; [|split; [|split]].
      * apply pr_prime_bool_true. exact Hb.
      * lia.
      * lia.
      * intros q0 Hq0 Hmq0. lia.
    + change (if false then m else pen_next_prime f (S m)) with (pen_next_prime f (S m)).
      assert (Hmnp : pr_prime m -> False).
      { intros Hpm. rewrite (pr_prime_bool_false m Hpm) in Hb. discriminate. }
      destruct Hget as [q [Hq [Hq1 Hq2]]].
      assert (Hqm : S m <= q).
      { destruct (Nat.eq_dec q m) as [Hqe|Hqne].
        - exfalso. apply Hmnp. rewrite <- Hqe. exact Hq.
        - lia. }
      assert (Hwin : exists q0 : nat, pr_prime q0 /\ S m <= q0 /\ q0 < S m + f).
      { exists q. split; [exact Hq | split; [exact Hqm | lia]]. }
      destruct (IH (S m) Hwin) as [Hp [Hp1 [Hp2 Hp4]]].
      split; [|split; [|split]].
      * exact Hp.
      * lia.
      * lia.
      * intros q0 Hq0 Hmq0.
        destruct (Nat.eq_dec q0 m) as [Hqe|Hqne].
        -- exfalso. apply Hmnp. rewrite <- Hqe. exact Hq0.
        -- apply Hp4; [exact Hq0 | lia].
Qed.

(* 计数读数：下一素数搜索的返回值恰把计数推到「起点前读数 + 1」 *)
Lemma pen_count_next_prime : forall f m : nat, 1 <= m ->
  (exists q : nat, pr_prime q /\ m <= q /\ q < m + f) ->
  pen_count_upto (pen_next_prime f m) = pen_count_upto (m - 1) + 1.
Proof.
  intros f m Hm Hget.
  destruct (pen_next_prime_spec f m Hget) as [Hp [Hmle [Hplt Hmin]]].
  assert (Hsplit : pen_next_prime f m = (m - 1) + (pen_next_prime f m - (m - 1))) by lia.
  rewrite Hsplit, pen_count_split.
  assert (Hseg : pen_count_seg (m - 1) (pen_next_prime f m - (m - 1)) = 1).
  { apply (pen_count_seg_one (pen_next_prime f m - (m - 1)) (m - 1) (pen_next_prime f m)).
    - exact Hp.
    - lia.
    - lia.
    - intros q Hq Hmq Hqle.
      assert (Hmq2 : m <= q) by lia.
      specialize (Hmin q Hq Hmq2). lia. }
  rewrite Hseg. reflexivity.
Qed.

(* ---- §3 第 k 素枚举器（第 k 槽结构递归；第 0 槽回退 1，spec 只覆盖 S k） ---- *)

Fixpoint pen_nth_prime (f k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => pen_next_prime f (S (pen_nth_prime f k'))
  end.

(* 枚举器核心 spec：窗 [2, 2+f) 内存在第 S k 素（计数刻画）则
   pen_nth_prime f (S k) 返回值素且读数恰为 S k（即「素且为第 S k 个」） *)
Theorem pen_nth_prime_spec : forall k f : nat,
  (exists q : nat, pr_prime q /\ pen_count_upto q = S k /\ q < 2 + f) ->
  pr_prime (pen_nth_prime f (S k)) /\
  pen_count_upto (pen_nth_prime f (S k)) = S k.
Proof.
  intros k. induction k as [|k IH]; intros f Hget.
  - (* 第 1 素：起点 2，窗内素 q 自证 *)
    destruct Hget as [q [Hq [Hcq Hqlt]]].
    destruct Hq as [Hq2 Hqd].
    assert (Hwin : exists q0 : nat, pr_prime q0 /\ 2 <= q0 /\ q0 < 2 + f).
    { exists q. split; [split; [exact Hq2 | exact Hqd] | split; [exact Hq2 | exact Hqlt]]. }
    assert (Hstep : pen_nth_prime f 1 = pen_next_prime f 2) by reflexivity.
    rewrite Hstep.
    destruct (pen_next_prime_spec f 2 Hwin) as [Hp [Hp1 [Hp2s Hp4]]].
    split; [exact Hp|].
    assert (Hm2 : 1 <= 2) by lia.
    rewrite (pen_count_next_prime f 2 Hm2 Hwin).
    assert (Hc1 : pen_count_upto (2 - 1) = 0) by reflexivity.
    rewrite Hc1. reflexivity.
  - (* 第 S (S k) 素：先取前驱素 r（第 S k 素），升扫其紧后 *)
    destruct Hget as [q [Hq [Hcq Hqlt]]].
    destruct Hq as [Hq2 Hqd].
    assert (Hstepq : pen_count_upto q = pen_count_upto (q - 1) + 1).
    { apply (pen_count_upto_step q); [lia | split; [exact Hq2 | exact Hqd]]. }
    assert (Hcq1 : pen_count_upto (q - 1) = S k) by lia.
    assert (Hprev : exists r : nat, pr_prime r /\ r <= q - 1 /\
                                   pen_count_upto r = pen_count_upto (q - 1))
      by (apply (pen_count_upto_largest (q - 1)); lia).
    destruct Hprev as [r [Hr [Hrle Hrc]]].
    assert (Hr2 : 2 <= r) by (destruct Hr as [Hr2 _]; exact Hr2).
    assert (Hrwin : exists r0 : nat, pr_prime r0 /\ pen_count_upto r0 = S k /\ r0 < 2 + f).
    { exists r. split; [exact Hr | split; [lia | lia]]. }
    destruct (IH f Hrwin) as [Hp Hpc].
    (* IH 返回值与前驱素 r 由计数单射重合 *)
    assert (Hpr : pen_nth_prime f (S k) = r).
    { apply (pen_count_inj (pen_nth_prime f (S k)) r Hp Hr).
      rewrite Hpc, Hrc. lia. }
    assert (Hwin : exists q0 : nat, pr_prime q0 /\
                                   S (pen_nth_prime f (S k)) <= q0 /\
                                   q0 < S (pen_nth_prime f (S k)) + f).
    { exists q. split; [split; [exact Hq2 | exact Hqd] | split; [lia | lia]]. }
    assert (Hstep2 : pen_nth_prime f (S (S k)) =
                     pen_next_prime f (S (pen_nth_prime f (S k)))) by reflexivity.
    rewrite Hstep2.
    destruct (pen_next_prime_spec f (S (pen_nth_prime f (S k))) Hwin) as [Hpp2 [Hpm [Hplt Hmin]]].
    split; [exact Hpp2|].
    assert (Hm1 : 1 <= S (pen_nth_prime f (S k))) by lia.
    rewrite (pen_count_next_prime f (S (pen_nth_prime f (S k))) Hm1 Hwin).
    assert (Hsub : pen_count_upto (S (pen_nth_prime f (S k)) - 1) =
                   pen_count_upto (pen_nth_prime f (S k))).
    { assert (Hz : S (pen_nth_prime f (S k)) - 1 = pen_nth_prime f (S k)) by lia.
      rewrite Hz. reflexivity. }
    rewrite Hsub, Hpc. lia.
Qed.

(* sigT 见证形：返回值素、读数 S k（第 S k 个）、且即枚举器计算值 *)
Theorem pen_nth_prime_exists : forall k f : nat,
  (exists q : nat, pr_prime q /\ pen_count_upto q = S k /\ q < 2 + f) ->
  { p : nat | pr_prime p /\ pen_count_upto p = S k /\ pen_nth_prime f (S k) = p }.
Proof.
  intros k f Hget.
  exists (pen_nth_prime f (S k)).
  destruct (pen_nth_prime_spec k f Hget) as [Hp Hc].
  split; [exact Hp | split; [exact Hc | reflexivity]].
Defined.

(* ---- §4 素数列表、primorial 与互素面（Euclid 结构枚举侧形态） ---- *)

Fixpoint pen_primes_upto (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => pen_primes_upto m ++ (if pr_prime_bool (S m) then S m :: nil else nil)
  end.

Lemma pen_primes_upto_S : forall n : nat,
  pen_primes_upto (S n) =
  pen_primes_upto n ++ (if pr_prime_bool (S n) then S n :: nil else nil).
Proof. reflexivity. Qed.

(* In 刻画：入表当且仅当素且不大于 n *)
Theorem pen_in_primes_upto : forall p n : nat,
  In p (pen_primes_upto n) <-> pr_prime p /\ p <= n.
Proof.
  intros p n. induction n as [|m IH].
  - split.
    + intros H. destruct H.
    + intros [Hp Hle]. exfalso. destruct Hp as [Hp2 _]. lia.
  - rewrite pen_primes_upto_S. split.
    + intros Hin.
      remember (pr_prime_bool (S m)) as b eqn:Hb.
      destruct b.
      * change (if true then S m :: nil else nil) with (S m :: nil) in Hin.
        apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        -- apply IH in Hin. destruct Hin as [Hp Hle]. split; [exact Hp | lia].
        -- simpl in Hin. destruct Hin as [Heq|Hf].
           ++ rewrite <- Heq. split.
              ** apply pr_prime_bool_true. symmetry. exact Hb.
              ** lia.
           ++ destruct Hf.
      * change (if false then S m :: nil else nil) with (@nil nat) in Hin.
        apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        -- apply IH in Hin. destruct Hin as [Hp Hle]. split; [exact Hp | lia].
        -- simpl in Hin. destruct Hin.
    + intros [Hp Hle]. destruct (le_lt_dec p m) as [Hpm|Hpgt].
      * apply in_or_app. left. apply IH. split; [exact Hp | exact Hpm].
      * assert (Hpe : p = S m) by lia.
        assert (Hb : pr_prime_bool (S m) = true).
        { apply pr_prime_bool_false. rewrite <- Hpe. exact Hp. }
        rewrite Hb. change (if true then S m :: nil else nil) with (S m :: nil).
        apply in_or_app. right. simpl. left. lia.
Qed.

(* 素因子皆达标则折积达标 *)
Lemma pen_fold_mul_pos : forall l : list nat,
  (forall x : nat, In x l -> 1 <= x) -> 1 <= fold_right Nat.mul 1 l.
Proof.
  intros l. induction l as [|a l IH]; intros Hall.
  - simpl. lia.
  - simpl.
    assert (H1 : 1 <= a) by (apply Hall; left; reflexivity).
    assert (H2 : 1 <= fold_right Nat.mul 1 l)
      by (apply IH; intros x Hx; apply Hall; right; exact Hx).
    assert (Hstep : a * 1 <= a * fold_right Nat.mul 1 l)
      by (apply (Nat.mul_le_mono_l 1 (fold_right Nat.mul 1 l) a); exact H2).
    rewrite Nat.mul_1_r in Hstep. lia.
Qed.

(* primorial：不大于 n 的素数之积（n 取第 k 素时即「前 k 素之积」） *)
Definition pen_primorial (n : nat) : nat :=
  fold_right Nat.mul 1 (pen_primes_upto n).

Lemma pen_primorial_pos : forall n : nat, 1 <= pen_primorial n.
Proof.
  intros n. apply pen_fold_mul_pos. intros x Hx.
  apply (proj1 (pen_in_primes_upto x n)) in Hx.
  destruct Hx as [Hp _]. destruct Hp as [Hp2 _]. lia.
Qed.

(* 列表成员整除折积 *)
Lemma pen_fold_in_divide : forall (x : nat) (l : list nat),
  In x l -> Nat.divide x (fold_right Nat.mul 1 l).
Proof.
  intros x l. induction l as [|a l IH]; intros Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq|Hin].
    + subst a. exists (fold_right Nat.mul 1 l). apply Nat.mul_comm.
    + destruct (IH Hin) as [c Hc].
      exists (a * c). rewrite Hc.
      rewrite <- (Nat.mul_assoc a c x). reflexivity.
Qed.

(* 素 p 不大于 n 则整除 primorial n *)
Lemma pen_primorial_divide : forall p n : nat, pr_prime p -> p <= n ->
  Nat.divide p (pen_primorial n).
Proof.
  intros p n Hp Hle. unfold pen_primorial.
  apply (pen_fold_in_divide p).
  apply (proj2 (pen_in_primes_upto p n)). split; [exact Hp | exact Hle].
Qed.

(* primorial 与其后继的互素构造性版：凡整除 primorial n 又整除其后继者必为一 *)
Theorem pen_primorial_coprime_succ : forall n : nat,
  forall d : nat, Nat.divide d (pen_primorial n) ->
                  Nat.divide d (S (pen_primorial n)) -> d = 1.
Proof.
  intros n d Hd1 Hd2.
  assert (Hs : S (pen_primorial n) - pen_primorial n = 1) by lia.
  assert (Hd3 : Nat.divide d 1).
  { rewrite <- Hs.
    apply (Nat.divide_sub_r d (S (pen_primorial n)) (pen_primorial n));
      [exact Hd2 | exact Hd1]. }
  apply (Nat.divide_1_r d Hd3).
Qed.

(* Euclid 结构枚举侧构造性版：整除 primorial n + 1 的最小素因子必大于 n
   ——对每个 n 显式给出一个表外新素（与 n!+1 线平行） *)
Theorem pen_euclid_new_prime : forall n : nat,
  { p : nat | pr_prime p /\ Nat.divide p (S (pen_primorial n)) /\ n < p }.
Proof.
  intros n.
  assert (HP2 : 2 <= S (pen_primorial n)).
  { assert (H1 : 1 <= pen_primorial n) by apply pen_primorial_pos. lia. }
  destruct (pr_min_factor_exists (S (pen_primorial n)) HP2) as [p [Hpn Hpp]].
  exists p. split; [exact Hpp | split; [exact Hpn |]].
  destruct (le_lt_dec p n) as [Hpn2|Hpgt]; [|exact Hpgt].
  exfalso.
  destruct Hpp as [Hp2 Hpd].
  assert (Hdv : Nat.divide p (pen_primorial n))
    by (apply (pen_primorial_divide p n (conj Hp2 Hpd) Hpn2)).
  assert (Hs : S (pen_primorial n) - pen_primorial n = 1) by lia.
  assert (Hd1 : Nat.divide p 1).
  { rewrite <- Hs.
    apply (Nat.divide_sub_r p (S (pen_primorial n)) (pen_primorial n));
      [exact Hpn | exact Hdv]. }
  assert (Hp1 : p = 1) by (apply Nat.divide_1_r; exact Hd1).
  lia.
Defined.

(* 素数无界（构造性）：对每个 n 给出大于 n 的素 *)
Theorem pen_prime_unbounded : forall n : nat,
  { p : nat | pr_prime p /\ n < p }.
Proof.
  intros n. destruct (pen_euclid_new_prime n) as [p [Hpp [Hd Hlt]]].
  exists p. split; [exact Hpp | exact Hlt].
Defined.

(* 相异素数互素：两相异素数的最大公因数为一 *)
Theorem pen_coprime_of_neq : forall p q : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) -> Nat.gcd p q = 1.
Proof.
  intros p q Hp Hq Hpq.
  assert (Hgp : Nat.divide (Nat.gcd p q) p) by apply Nat.gcd_divide_l.
  assert (Hgq : Nat.divide (Nat.gcd p q) q) by apply Nat.gcd_divide_r.
  destruct (le_lt_dec 2 (Nat.gcd p q)) as [Hg2|Hg1].
  - (* 公因数达标 2：必等于 p，遂整除 q，遂 p = q，违相异 *)
    exfalso.
    assert (Hgle : Nat.gcd p q <= p).
    { destruct Hgp as [c Hc]. destruct c as [|c'].
      - rewrite Nat.mul_0_l in Hc. exfalso. destruct Hp as [Hp2 _]. lia.
      - assert (Hstep : 1 * Nat.gcd p q <= S c' * Nat.gcd p q)
          by (apply (Nat.mul_le_mono_r 1 (S c') (Nat.gcd p q)); lia).
        rewrite Nat.mul_1_l in Hstep. lia. }
    assert (Hgeqp : Nat.gcd p q = p).
    { destruct (Nat.eq_dec (Nat.gcd p q) p) as [H|H]; [exact H|].
      exfalso.
      destruct Hp as [Hp2 Hpd].
      destruct (le_lt_dec (Nat.gcd p q) p) as [Hle|Hlt].
      - assert (Hglt : Nat.gcd p q < p) by lia.
        apply (Hpd (Nat.gcd p q) Hg2 Hglt Hgp).
      - lia. }
    rewrite Hgeqp in Hgq.
    assert (Hple : p <= q).
    { destruct Hgq as [c Hc]. destruct c as [|c'].
      - rewrite Nat.mul_0_l in Hc. exfalso. destruct Hq as [Hq2 _]. lia.
      - assert (Hstep : 1 * p <= S c' * p)
          by (apply (Nat.mul_le_mono_r 1 (S c') p); lia).
        rewrite Nat.mul_1_l in Hstep. lia. }
    destruct Hq as [Hq2 Hqd].
    destruct (Nat.eq_dec p q) as [H|H].
    + apply Hpq. exact H.
    + apply (Hqd p (proj1 Hp)); [lia | exact Hgq].
  - (* 公因数不过 1：又非零（零整除 p 则 p 归零违素），故为一 *)
    assert (Hg0 : Nat.gcd p q = 0 -> False).
    { intros H0. rewrite H0 in Hgp.
      apply (Nat.divide_0_l p) in Hgp.
      destruct Hp as [Hp2 _]. lia. }
    assert (Hgpos : 1 <= Nat.gcd p q).
    { destruct (le_lt_dec 1 (Nat.gcd p q)) as [Hge|Hlt1].
      - exact Hge.
      - exfalso. apply Hg0. lia. }
    lia.
Qed.

(* ---- §5 数值定装烟测（小实例 ≤ 10，vm_compute 直算零公设） ---- *)

Lemma pen_nth_1 : pen_nth_prime 8 1 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_2 : pen_nth_prime 8 2 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_3 : pen_nth_prime 8 3 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_4 : pen_nth_prime 8 4 = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_count_10 : pen_count_upto 10 = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_list_10 : pen_primes_upto 10 = 2 :: 3 :: 5 :: 7 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_primorial_5 : pen_primorial 5 = 30.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_primorial_10 : pen_primorial 10 = 210.
Proof. vm_compute. reflexivity. Qed.

(* ---- §6 公理审计（Print Assumptions 取证块） ---- *)

Print Assumptions pen_count_split.
Print Assumptions pen_count_seg_none.
Print Assumptions pen_count_seg_one.
Print Assumptions pen_count_upto_step.
Print Assumptions pen_count_mono.
Print Assumptions pen_count_upto_largest.
Print Assumptions pen_count_lt_prime.
Print Assumptions pen_count_inj.
Print Assumptions pen_next_prime_spec.
Print Assumptions pen_count_next_prime.
Print Assumptions pen_nth_prime_spec.
Print Assumptions pen_nth_prime_exists.
Print Assumptions pen_in_primes_upto.
Print Assumptions pen_fold_mul_pos.
Print Assumptions pen_primorial_pos.
Print Assumptions pen_fold_in_divide.
Print Assumptions pen_primorial_divide.
Print Assumptions pen_primorial_coprime_succ.
Print Assumptions pen_euclid_new_prime.
Print Assumptions pen_prime_unbounded.
Print Assumptions pen_coprime_of_neq.
