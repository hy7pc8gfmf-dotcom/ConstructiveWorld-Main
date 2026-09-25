(* ============================================================ *)
(* UpAblMixBSharp.v —— mixb 两相选择器二分相计数界的紧化（常数 5 → 4）    *)
(* 数学使命：UpReqMixLogB 的 mixb_bsearch 求值计数上界原为燃料加一         *)
(*   （mixb_bsearch_c_le 的燃料零基例以 0 ≤ 1 收束，松弛沿归纳传播；      *)
(*   mixb_bsearch_account 结论同为 c ≤ S f）。本件按 mixb_bsearch 定义    *)
(*   实形逐枝计数：燃料零层返回 (hi, 0)，求值次数为零，诚实上界为        *)
(*   0 ≤ 0；递归层计数至多加一且归纳假设给出 c' ≤ f'；早退层计数为一      *)
(*   而燃料 S f' 至少为一。故无条件计数                                   *)
(*   snd (mixb_bsearch test f lo hi) ≤ f 对全体燃料成立；在端点夹逼、      *)
(*   单调性与窗口前提之下可靠性结论 r = k 与计数 c ≤ f 一并成立；         *)
(*   量级定理随之从 c ≤ 2·log₂K + 5 紧化为 c ≤ 2·log₂K + 4               *)
(*   （倍增相配给 log₂K + 2 不变，二分相燃料 log₂K + 2 的基例松弛消除）。*)
(* ------------------------------------------------------------ *)
(* 依赖：UpReqMixLogB（mixb_gallop / mixb_bsearch / mixb_sel /           *)
(*   mixb_mono / mixb_bsearch_S / mixb_sel_eq / mixb_gallop_c_le /       *)
(*   mixb_gallop_account / mixb_gallop_width_le）；stdlib 仅 PeanoNat    *)
(*   与 Lia。                                                          *)
(* 对标：UpReqMixLogB.v 的 mixb_bsearch_c_le / mixb_bsearch_account /    *)
(*   mixb_sel_count / mixb_sel_scale（本件为四者的紧化对偶形）；stdlib    *)
(*   Nat.log2_spec。                                                   *)
(* 构造性注记：全部语句为 nat 面的等式与序（Prop 层，Qed 收束）；零       *)
(*   承认；算术收束一律 lia。                                            *)
(* 编译配方：9.1 直调 coqc -q -Q . ""；进程环境零 COQLIB/ROCQLIB 注入。  *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Require Import UpReqMixLogB.

(* ================= §1 二分相计数紧形（无条件） ================= *)

(** 计数紧形：mixb_bsearch 的谓词求值次数不超过燃料（无需单调性、
    端点通过性或任何窗口前提）。对燃料归纳：
    燃料零层返回 (hi, 0)，求值次数为零，界 0 ≤ 0 无松弛成立；
    递归层按定义展开后计数为 S c'，归纳假设给出 c' ≤ f'；
    中点索引比较 Nat.ltb 为假时的早退层计数为一，而燃料 S f' ≥ 1。 *)
Lemma msharp_bsearch_c_le : forall (test : nat -> bool) (f lo hi : nat),
  (snd (mixb_bsearch test f lo hi) <= f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [mixb_bsearch fst snd]. lia.
  - cbn [mixb_bsearch]. destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)).
    + destruct (test (Nat.div2 (lo + hi)%nat)).
      * cbv zeta. cbn [fst snd].
        specialize (IH lo (Nat.div2 (lo + hi)%nat)). cbn [fst snd] in IH. lia.
      * cbv zeta. cbn [fst snd].
        specialize (IH (Nat.div2 (lo + hi)%nat) hi). cbn [fst snd] in IH. lia.
    + cbn [fst snd]. lia.
Qed.

(** 复合计数紧形：两相选择器 mixb_sel 的谓词求值次数不超过双相燃料之和
    （对 mixb_sel_count 的 S(f1+f2) 同步去松弛；倍增相计数界
    mixb_gallop_c_le 原本即为紧形 c1 ≤ f1）。 *)
Theorem msharp_sel_count : forall (test : nat -> bool) (f1 f2 : nat),
  (snd (mixb_sel test f1 f2) <= (f1 + f2))%nat.
Proof.
  intros test f1 f2.
  destruct (mixb_gallop test f1 0%nat 1%nat) as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test f2 l h) as [r c2] eqn:Eb.
  pose proof (mixb_gallop_c_le test f1 0%nat 1%nat) as H1.
  rewrite Eg in H1. cbn [fst snd] in H1.
  pose proof (msharp_bsearch_c_le test f2 l h) as H2.
  rewrite Eb in H2. cbn [fst snd] in H2.
  assert (Hs : mixb_sel test f1 f2 = (r, (c1 + c2)%nat))
    by exact (mixb_sel_eq test f1 f2 l h c1 r c2 Eg Eb).
  rewrite Hs. cbn [snd]. lia.
Qed.

(* ================= §2 二分相可靠性合取与量级定理紧形 ================= *)

(** 二分相可靠性合取紧形：在单调性、端点夹逼（lo < hi、test lo = false、
    test hi = true）、过站前提（test k = true 与下方全假）与窗口宽
    hi - lo ≤ 2 ^ f 之下，mixb_bsearch 返回恰为最小通过站 k，
    且求值次数 c ≤ f（对 mixb_bsearch_account 的 c ≤ S f 去松弛）。
    对燃料归纳：燃料零层返回 (hi, 0)，窗口宽 ≤ 1 迫使 hi = lo + 1，
    端点夹逼给出 k = hi，计数 0 ≤ 0；递归层由归纳假设 c' ≤ f'
    得 S c' ≤ S f'；早退层窗口宽 ≤ 2^(S f') 与中点 ≤ lo 迫使
    hi = lo + 1，返回 (hi, 1) 而 S f' ≥ 1。 *)
Lemma msharp_bsearch_account : forall (test : nat -> bool) (f k lo hi r c : nat),
  mixb_mono test -> (lo < hi)%nat -> test lo = false -> test hi = true ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (hi - lo <= 2 ^ f)%nat ->
  mixb_bsearch test f lo hi = (r, c) ->
  (r = k /\ c <= f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros k lo hi r c
    Hmono Hlt Hlo Hhi Htk Hmin Hw Heq.
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    cbn [Nat.pow] in Hw. cbn [mixb_bsearch] in Heq.
    injection Heq; intros; subst.
    split; [lia | lia].
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    assert (H2 : (2 <> 0)%nat) by lia.
    pose proof (Nat.div_mod (lo + hi)%nat 2%nat H2) as Hdm.
    pose proof (Nat.mod_upper_bound (lo + hi)%nat 2%nat H2) as Hm.
    rewrite mixb_bsearch_S in Heq.
    destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)) eqn:Eltb.
    + assert (Hmidlo : (lo < Nat.div2 (lo + hi)%nat)%nat)
        by (apply Nat.ltb_lt; exact Eltb).
      assert (Hmidhi : (Nat.div2 (lo + hi)%nat < hi)%nat).
      { rewrite Nat.div2_div. lia. }
      assert (Hwd : (hi - lo <= 2 * 2 ^ f)%nat).
      { replace (2 ^ Datatypes.S f)%nat with (2 * 2 ^ f)%nat in Hw
          by (cbn [Nat.pow]; lia).
        lia. }
      destruct (test (Nat.div2 (lo + hi)%nat)) eqn:Emid.
      * assert (Hkmid : (k <= Nat.div2 (lo + hi)%nat)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exact Hc.
          - exfalso. rewrite (Hmin (Nat.div2 (lo + hi)%nat) Hc) in Emid.
            discriminate Emid. }
        assert (Hw2 : (Nat.div2 (lo + hi)%nat - lo <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (lo + Nat.div2 (hi - lo) - lo)%nat
            with (Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_le. exact Hwd. }
        destruct (mixb_bsearch test f lo (Nat.div2 (lo + hi)%nat))
          as [r1 c1] eqn:E1.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k lo (Nat.div2 (lo + hi)%nat) r1 c1
                    Hmono Hmidlo Hlo Emid Htk Hmin Hw2 E1) as [Hr1 Hc1].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr1 | lia].
      * assert (Hmidk : (Nat.div2 (lo + hi)%nat < k)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exfalso. rewrite (Hmono k (Nat.div2 (lo + hi)%nat) Hc Htk) in Emid.
            discriminate Emid.
          - exact Hc. }
        assert (Hw2 : (hi - Nat.div2 (lo + hi)%nat <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (hi - (lo + Nat.div2 (hi - lo)))%nat
            with ((hi - lo) - Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_split. exact Hwd. }
        destruct (mixb_bsearch test f (Nat.div2 (lo + hi)%nat) hi)
          as [r2 c2] eqn:E2.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k (Nat.div2 (lo + hi)%nat) hi r2 c2
                    Hmono Hmidhi Emid Hhi Htk Hmin Hw2 E2) as [Hr2 Hc2].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr2 | lia].
    + assert (Hmle : (Nat.div2 (lo + hi)%nat <= lo)%nat)
        by (apply Nat.ltb_ge; exact Eltb).
      rewrite Nat.div2_div in Hmle.
      assert (Hheq : (hi = lo + 1)%nat) by lia.
      cbn [fst snd] in Heq. injection Heq; intros; subst.
      split; [lia | lia].
Qed.

(** 量级定理紧形：双相燃料 S(S(log2 K)) 配给下，mixb_sel 返回恰为
    可判定谓词的最小通过站，且谓词求值次数 ≤ 2·log₂K + 4。
    倍增相计数 c1 ≤ S(S(log2 K)) 由 mixb_gallop_account 给出（原本即紧）；
    二分相宽度前提 h - l ≤ 2^(S(S(log2 K))) 由 mixb_gallop_width_le 的
    末站宽度交割供给；二分相计数 c2 ≤ S(S(log2 K)) 由
    msharp_bsearch_account 的紧形给出；两相计数相加
    (log₂K + 2) + (log₂K + 2) = 2·log₂K + 4 由 lia 收束。 *)
Theorem msharp_sel_scale : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k -> k <= K -> 2 <= K ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  r = k /\ c <= 2 * (Nat.log2 K) + 4)%nat.
Proof.
  intros test K k r c Hmono H0 Htk Hmin Hk1 HkK HK2 Hsel.
  pose proof (Nat.log2_spec K) as Hspec.
  assert (HK0 : (0 < K)%nat) by lia.
  specialize (Hspec HK0).
  assert (Hlt01 : (0 < 1)%nat) by exact (Nat.lt_0_succ 0).
  destruct (mixb_gallop test (Datatypes.S (Datatypes.S (Nat.log2 K))) 0%nat 1%nat)
    as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test (Datatypes.S (Datatypes.S (Nat.log2 K))) l h)
    as [r2 c2] eqn:Eb.
  assert (Hselc : mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r2, (c1 + c2)%nat))
    by exact (mixb_sel_eq test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                (Datatypes.S (Datatypes.S (Nat.log2 K))) l h c1 r2 c2 Eg Eb).
  rewrite Hselc in Hsel. injection Hsel; intros; subst.
  assert (Hreach : (k <= 1 + (1 - 0) * 2 ^ (Datatypes.S (Nat.log2 K)))%nat).
  { replace (2 ^ Datatypes.S (Nat.log2 K))%nat
      with (2 * 2 ^ Nat.log2 K)%nat by (cbn [Nat.pow]; lia).
    destruct Hspec as [_ Hup]. cbn [Nat.pow] in Hup. lia. }
  pose proof (mixb_gallop_account test (Datatypes.S (Nat.log2 K)) k 0%nat 1%nat
                l h c1 Hmono Hlt01 H0 Htk Hmin Hreach Eg) as Hgl.
  destruct Hgl as [Hgl1 [Hgl2 [Hgl3 Hgl4]]].
  pose proof (mixb_gallop_width_le test (Datatypes.S (Nat.log2 K)) 0%nat 1%nat
                l h c1 Hlt01 Eg) as Hwd.
  replace (1 - 0)%nat with 1%nat in Hwd by lia.
  replace (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)) * 1)%nat
    with (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)))%nat in Hwd by lia.
  pose proof (msharp_bsearch_account test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                k l h r c2 Hmono Hgl1 Hgl3 Hgl2 Htk Hmin Hwd Eb) as Hbs.
  destruct Hbs as [Hbs1 Hbs2].
  split; [exact Hbs1 | lia].
Qed.

(* 追印面：全部证明件预期零承认闭 *)
Print Assumptions msharp_bsearch_c_le.
Print Assumptions msharp_sel_count.
Print Assumptions msharp_bsearch_account.
Print Assumptions msharp_sel_scale.
