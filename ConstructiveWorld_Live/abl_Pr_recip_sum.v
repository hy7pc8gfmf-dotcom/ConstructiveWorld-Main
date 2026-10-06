(* ============================================================ *)
(* abl_Pr_recip_sum.v —— 素数域第 7 件：素数倒数和发散（Euler 无理性  *)
(*   路线关键件）层 1 闭合件                                        *)
(* 模块名：abl_Pr_recip_sum                                       *)
(* 数学使命：素数倒数和发散 ∑_{p≤n} 1/p → ∞ 的构造性前件件。         *)
(*   本切片交付：                                                   *)
(*   【层 1 闭合】调和级数发散核（dyadic 块增益，纯 nat 承载）：       *)
(*     prs_hsum N C = Σ_{k=1}^{N} C/k（nat 整除逐项；floor 只降不升，  *)
(*     是实值调和和的保守下界）；主引理                              *)
(*     prs_harm_dyad：2·prs_hsum (2^m) (2^{2m}) ≥ (m+1)·2^{2m}，      *)
(*     即 n = 2^m 处 H_n ≥ (m+1)/2——log(n+1) 型下界的 log-free        *)
(*     nat 承载（dyadic 块：区间 (2^j, 2^{j+1}] 贡献 2^{2m-1}，逐块    *)
(*     精确，无 Q 无 log 依赖）；Set 面主语句                        *)
(*     prs_harm_diverge：∀K，sigT 见证 m = 2K 使                     *)
(*     K·2^{2m} ≤ Σ_{k≤2^m} 2^{2m}/k（发散证书可计算可提取）。        *)
(*   【层 2 砖】单素 Euler 因子恒等式 prs_geo_euler（Set 面 hl_id     *)
(*     承载）：(p−1)·(1+p+…+p^e) + 1 = p^{e+1}，即                   *)
(*     1/(1−1/p) 的有限展开因子——∏_{p≤n}(1−1/p)^{-1} 的逐素因子。     *)
(*   【层 2/3 障碍登记（fail-loud，缺口不掩饰）】见文末 §8 登记块。      *)
(* 依赖清单：纯 Stdlib（Arith.Arith／List／Bool／Lia）＋ HansonLcm    *)
(*   （hl_id／hl_idrefl，缓存根 vo_local_world_unified_0930 -Q 只读，  *)
(*   照 abl_Pr_lcm_eq 先例）。层 1 与 Euler 砖均不使用素数枚举面       *)
(*   （pr_*／pen_*／plm_*）——素数六件与 Bertrand 件、LW0FactGrowth   *)
(*   桥的使用位属层 2/3 续件（障碍登记 §8），本件未使用故不拷入链编。  *)
(* 构造性注记：Set 面承载——两条主语句 prs_harm_diverge（sigT 见证形， *)
(*   Defined 透明，见证 m = 2K 可计算）与 prs_geo_euler（hl_id Set 面 *)
(*   等式，Defined）；计算件 prs_hsum／prs_geo 皆一阶 nat Fixpoint     *)
(*   可提取；Prop 面不等式/等式仅作推理脚手架（core_01 先例同构）；    *)
(*   否定形自持 P -> False（照 AQ 坑卡，全件零 not／~／<> 书写，含    *)
(*   证明内部）；零公理零承认零经典逻辑；非线性步全走 Nat.mul_le_mono  *)
(*   显式乘法步，lia 仅承担线性核；数值定装走小实例 vm_compute        *)
(*   （N ≤ 64，照 CZR14 大数值 Qed 打点墙纪律）。                     *)
(* 红线四条自审：                                                   *)
(*   - 红线一（零公理声明词）：全件 Qed/Defined，PA 取证块收尾；       *)
(*   - Set 层：主承载＝sigT 发散证书＋hl_id Euler 因子等式，非平凡      *)
(*     数学内容（dyadic 块增益归纳、尺度加倍、几何和 Euler 恒等式）    *)
(*     全在证明面；                                                  *)
(*   - 非平凡：层 1 发散核全强度闭合（任意 K 的显式见证），层 2 未达    *)
(*     部分显式登记（§8）非默默降级；                                *)
(*   - 可提取：prs_hsum／prs_geo／两主语句 Define 面，G3 提取检验      *)
(*     zz_prs_extract.v 验 Obj.magic = 0。                           *)
(* 编译配方：                                                       *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/    *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&   *)
(*   nice -19 rocq c -native-compiler no \                            *)
(*   -Q /Users/apple/Desktop/ConstructiveWorld/                       *)
(*   vo_local_world_unified_0930 "" -Q . "" abl_Pr_recip_sum.v        *)
(*   （复核：rocq chk 同 -Q 口径）                                   *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.

(* ---- §1 幂与整除的线性支撑件（全 nat 层，零否定记号） ---- *)

Fixpoint prs_hsum (N C : nat) : nat :=
  match N with
  | 0 => 0
  | S N' => C / S N' + prs_hsum N' C
  end.

Lemma prs_hsum_S : forall N C : nat,
  prs_hsum (S N) C = C / S N + prs_hsum N C.
Proof. reflexivity. Qed.

Lemma prs_pow_succ : forall j : nat, 2 ^ (S j) = 2 * 2 ^ j.
Proof. intros j. simpl. lia. Qed.

Lemma prs_pow2_pos : forall b : nat, 1 <= 2 ^ b.
Proof.
  induction b as [|b IH].
  - simpl. lia.
  - rewrite prs_pow_succ. lia.
Qed.

Lemma prs_pow2_double : forall j : nat, 2 ^ j + 2 ^ j = 2 ^ (S j).
Proof. intros j. rewrite prs_pow_succ. lia. Qed.

Lemma prs_pow2_sq : forall m : nat, 2 ^ m * 2 ^ m = 2 ^ (2 * m).
Proof.
  intros m. replace (2 * m) with (m + m) by lia.
  symmetry. apply Nat.pow_add_r.
Qed.

Lemma prs_pow_div : forall a b : nat, b <= a -> 2 ^ a / 2 ^ b = 2 ^ (a - b).
Proof.
  intros a b H.
  assert (Hm : 2 ^ b * 2 ^ (a - b) = 2 ^ a).
  { rewrite <- Nat.pow_add_r. f_equal. lia. }
  assert (Hz : 2 ^ b = 0 -> False).
  { intros H0. pose proof (prs_pow2_pos b) as Hp. lia. }
  rewrite <- Hm.
  rewrite (Nat.mul_comm (2 ^ b) (2 ^ (a - b))).
  apply Nat.div_mul. exact Hz.
Qed.

(* 乘法换位（宿主 stdlib 无 mul_swap，assoc+comm 自建） *)
Lemma prs_mul_swap : forall a b c : nat, a * (b * c) = b * (a * c).
Proof.
  intros a b c.
  rewrite Nat.mul_assoc, (Nat.mul_comm a b), <- Nat.mul_assoc. reflexivity.
Qed.

(* 整除下商：d·(C/d) ≤ C（Nat.div_mod 装配，线性核） *)
Lemma prs_mul_div_le : forall d C : nat, 1 <= d -> d * (C / d) <= C.
Proof.
  intros d C Hd. destruct d as [|d'].
  - exfalso. lia.
  - assert (Hz : S d' = 0 -> False) by discriminate.
    assert (Hdm : C = S d' * (C / S d') + C mod S d')
      by (apply Nat.div_mod; exact Hz).
    lia.
Qed.

(* 商下界：k·q ≤ C 且 1 ≤ k 则 q ≤ C/k（乘法步显式 mul_le_mono，
   其余全线性——零非线性缺据步） *)
Lemma prs_div_lower : forall C k q : nat,
  1 <= k -> k * q <= C -> q <= C / k.
Proof.
  intros C k q Hk Hpq. destruct k as [|k'].
  - exfalso. lia.
  - assert (Hz : S k' = 0 -> False) by discriminate.
    assert (Hmod : C mod S k' < S k') by (apply Nat.mod_upper_bound; exact Hz).
    assert (Hdm : C = S k' * (C / S k') + C mod S k')
      by (apply Nat.div_mod; exact Hz).
    destruct (le_lt_dec q (C / S k')) as [Hle | Hlt].
    + exact Hle.
    + exfalso.
      assert (Hq1 : C / S k' + 1 <= q) by lia.
      assert (Hmul : S k' * (C / S k' + 1) <= S k' * q)
        by (apply Nat.mul_le_mono_l; exact Hq1).
      assert (Hex : S k' * (C / S k' + 1) = S k' * (C / S k') + S k').
      { rewrite Nat.mul_add_distr_l. lia. }
      lia.
Qed.

(* ---- §2 块增益引理（dyadic 块的和裂解——层 1 发散核引擎） ----
   尾段 (N, N+M] 逐项 C/k ≥ q 时，整段和至少增益 M·q。 *)

Lemma prs_hsum_block : forall M N C q : nat,
  (forall k : nat, N < k -> k <= N + M -> q <= C / k) ->
  prs_hsum N C + M * q <= prs_hsum (N + M) C.
Proof.
  intros M. induction M as [|M IH]; intros N C q Hall.
  - replace (N + 0) with N by lia. lia.
  - replace (N + S M) with (S (N + M)) by lia.
    rewrite prs_hsum_S.
    assert (IH' : prs_hsum N C + M * q <= prs_hsum (N + M) C).
    { apply IH. intros k H1 H2. apply Hall; lia. }
    assert (Hq : q <= C / S (N + M)) by (apply Hall; lia).
    rewrite Nat.mul_succ_l. lia.
Qed.

(* ---- §3 尺度加倍引理（C ↦ 2C 逐项保序，调和尺随块翻番） ---- *)

Lemma prs_hsum_scale2 : forall N C : nat,
  2 * prs_hsum N C <= prs_hsum N (2 * C).
Proof.
  intros N C. induction N as [|N IH].
  - simpl. lia.
  - rewrite !prs_hsum_S.
    assert (Hd : 2 * (C / S N) <= 2 * C / S N).
    { apply prs_div_lower.
      - lia.
      - assert (H1 : S N * (C / S N) <= C) by (apply prs_mul_div_le; lia).
        assert (H2 : S N * (2 * (C / S N)) = 2 * (S N * (C / S N))).
        { apply prs_mul_swap. }
        rewrite H2. apply Nat.mul_le_mono_l. exact H1. }
    lia.
Qed.

(* ---- §4 主引理（层 1 发散核闭合）：dyadic 点处 H ≥ (m+1)/2 ----
   2·Σ_{k≤2^m} 2^{2m}/k ≥ (m+1)·2^{2m}，即 H_{2^m} ≥ (m+1)/2；
   每块 (2^j, 2^{j+1}] 精确增益 2^{2m-1}（floor 零损耗路径）。 *)

Lemma prs_harm_dyad : forall m : nat,
  2 * prs_hsum (2 ^ m) (2 ^ (2 * m)) >= S m * 2 ^ (2 * m).
Proof.
  induction m as [|m IH].
  - vm_compute. lia.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    rewrite (prs_pow_succ (S (2 * m))).
    rewrite (prs_pow_succ (2 * m)).
    rewrite <- (prs_pow2_double m).
    (* 尺度加倍：大和 2C 尺度与小和 C 尺度挂钩 *)
    assert (Hs_small : 2 * prs_hsum (2 ^ m) (2 ^ (2 * m))
                       <= prs_hsum (2 ^ m) (2 * 2 ^ (2 * m)))
      by (apply prs_hsum_scale2).
    assert (Hs_big1 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 ^ (2 * m))
                      <= prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m)))
      by (apply prs_hsum_scale2).
    assert (Hs_big2 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m))
                      <= prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m))))
      by (apply prs_hsum_scale2).
    (* 块增益（尺度 2C，增益恰为 2^{2m}） *)
    assert (Hval : 2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m) = 2 ^ m).
    { replace (2 * 2 ^ (2 * m)) with (2 ^ S (2 * m))
        by (apply prs_pow_succ).
      rewrite (prs_pow2_double m).
      replace (2 ^ m) with (2 ^ (S (2 * m) - S m)) by (f_equal; lia).
      apply prs_pow_div. lia. }
    assert (HX : 2 ^ m * (2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m)) = 2 ^ (2 * m)).
    { rewrite Hval. apply prs_pow2_sq. }
    assert (Hb : prs_hsum (2 ^ m) (2 * 2 ^ (2 * m))
                 + 2 ^ m * (2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m))
                 <= prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m))).
    { apply prs_hsum_block. intros k H1 H2.
      apply prs_div_lower; [lia |].
      rewrite Hval.
      apply (Nat.le_trans _ ((2 ^ m + 2 ^ m) * 2 ^ m)).
      - apply Nat.mul_le_mono_r. exact H2.
      - rewrite Nat.mul_add_distr_r, prs_pow2_sq. lia. }
    (* 合拢：乘法步显式，线性核 lia *)
    assert (Hstep : S (S m) * (2 * (2 * 2 ^ (2 * m)))
                    <= 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m)))).
    { rewrite Nat.mul_succ_l.
      assert (Hsw : S m * (2 * (2 * 2 ^ (2 * m)))
                    = 2 * (S m * (2 * 2 ^ (2 * m))))
        by (apply (prs_mul_swap (S m) 2 (2 * 2 ^ (2 * m)))).
      rewrite Hsw.
      assert (H1 : S m * (2 * 2 ^ (2 * m))
                   <= 2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m)))).
      { rewrite (prs_mul_swap (S m) 2 (2 ^ (2 * m))).
        apply Nat.mul_le_mono_l. exact IH. }
      assert (H2 : 2 * (S m * (2 * 2 ^ (2 * m)))
                   <= 2 * (2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m))))).
      { apply Nat.mul_le_mono_l. exact H1. }
      assert (H3 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m)))
                   >= 2 * (2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m))))
                      + 2 * 2 ^ (2 * m)).
      { lia. }
      lia. }
    lia.
Qed.

(* ---- §5 Set 面主语句（sigT 发散证书，Defined 透明） ---- *)

Theorem prs_harm_diverge : forall K : nat,
  { m : nat & K * 2 ^ (2 * m) <= prs_hsum (2 ^ m) (2 ^ (2 * m)) }.
Proof.
  intros K. exists (2 * K).
  pose proof (prs_harm_dyad (2 * K)) as Hd.
  assert (Hsplit : S (2 * K) * 2 ^ (2 * (2 * K))
                   = 2 * (K * 2 ^ (2 * (2 * K))) + 2 ^ (2 * (2 * K))).
  { rewrite Nat.mul_succ_l.
    rewrite (Nat.mul_assoc 2 K (2 ^ (2 * (2 * K)))). lia. }
  rewrite Hsplit in Hd.
  lia.
Defined.

(* ---- §6 层 2 砖：单素 Euler 因子恒等式（Set 面 hl_id 承载） ----
   有限 Euler 因子：(p−1)·(1+p+…+p^e) + 1 = p^{e+1}，
   即 (1−1/p)^{-1} = p/(p−1) 的有限几何展开因子。 *)

Fixpoint prs_geo (p e : nat) : nat :=
  match e with
  | 0 => 1
  | S e' => 1 + p * prs_geo p e'
  end.

Lemma prs_geo_S : forall p e : nat,
  prs_geo p (S e) = 1 + p * prs_geo p e.
Proof. reflexivity. Qed.

(* Prop 面脚手架（等式归纳） *)
Lemma prs_geo_euler_eq : forall p e : nat,
  1 <= p -> 1 + (p - 1) * prs_geo p e = p ^ (S e).
Proof.
  intros p e Hp. induction e as [|e IH].
  - simpl. rewrite Nat.mul_1_r. lia.
  - change (prs_geo p (S e)) with (1 + p * prs_geo p e).
    replace (p ^ (S (S e))) with (p * p ^ (S e)) by (apply Nat.pow_succ_r; lia).
    replace (p * p ^ (S e)) with (p * (1 + (p - 1) * prs_geo p e))
      by (f_equal; exact IH).
    rewrite (Nat.mul_add_distr_l p 1 ((p - 1) * prs_geo p e)).
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    rewrite (prs_mul_swap (p - 1) p (prs_geo p e)).
    lia.
Qed.

(* Set 面主承载：hl_id 等式（HansonLcm 承载，照 lcm_eq 先例） *)
Theorem prs_geo_euler : forall p e : nat,
  1 <= p -> hl_id (1 + (p - 1) * prs_geo p e) (p ^ (S e)).
Proof.
  intros p e Hp.
  assert (Heq : 1 + (p - 1) * prs_geo p e = p ^ (S e))
    by (apply prs_geo_euler_eq; exact Hp).
  rewrite Heq. apply hl_idrefl.
Defined.

(* ---- §7 数值定装烟测（小实例 vm_compute，零公设） ---- *)

Lemma prs_hsum_4_16 : prs_hsum 4 16 = 33.
Proof. vm_compute. reflexivity. Qed.

Lemma prs_hsum_8_64 : prs_hsum 8 64 = 172.
Proof. vm_compute. reflexivity. Qed.

Lemma prs_hsum_16_256 : prs_hsum 16 256 = 861.
Proof. vm_compute. reflexivity. Qed.

Lemma prs_dyad_smoke_2 : 2 * prs_hsum (2 ^ 2) (2 ^ (2 * 2)) >= S 2 * 2 ^ (2 * 2).
Proof. vm_compute. lia. Qed.

Lemma prs_dyad_smoke_3 : 2 * prs_hsum (2 ^ 3) (2 ^ (2 * 3)) >= S 3 * 2 ^ (2 * 3).
Proof. vm_compute. lia. Qed.

Lemma prs_diverge_smoke_3 : 3 * 2 ^ (2 * 6) <= prs_hsum (2 ^ 6) (2 ^ (2 * 6)).
Proof. vm_compute. lia. Qed.

Lemma prs_geo_2_4 : prs_geo 2 4 = 31.
Proof. vm_compute. reflexivity. Qed.

Lemma prs_geo_euler_smoke : hl_id (1 + (2 - 1) * prs_geo 2 4) (2 ^ 5).
Proof. vm_compute. apply hl_idrefl. Qed.

(* ---- §8 障碍登记（fail-loud：层 2 全量与层 3 未达，未达面显式登记） ----
   【O1·层 2 全量（Euler 乘积公式有限版）】
   目标 nat 承载形：σ(L)·∏_{p≤n}(p−1) ≤ L·∏_{p≤n} p，
   其中 L = hl_lcm_upto n，σ(L) = Σ_{d | L} d。
   下半已在本件就位：Σ_{k≤n} L/k ≤ σ(L) 仅需 hl_lcm_divide_all
   （k ≤ n ⟹ k ∣ L，缓存根现成）＋除子枚举和；单素因子恒等式
   prs_geo_euler 已闭（§6）。
   缺口（本切片不闭合）：σ(L) ≤ ∏_{p≤n} prs_geo p (plm_v p L) 需
   ①指数向量单射性（同一 nat 值的素幂折积分解唯一：
   p^a ∣ ∏_q q^{b_q} 且 p ∤ 其余 ⟹ a ≤ b_p——可用
   plm_dvd_mul_coprime/plm_gcd_pow 两段归纳重建，约百行）；    ②除子
   枚举机的和分解（σ(∏p^{e_p}) 折积分配律）。合计量级超本切片预算。
   【O2·层 3（Mertens 弱版）】Σ_{p≤n} 1/p ≥ log log(n+1) 需 Q 层
   log 函数：缓存根 Q 面（S02_CauchyComplete/S03_QExp）具备有理幂
   与 QleT'，无 log。层 1 的 dyadic 核（§4）即 log-free 替代承载：
   n = 2^m 处 H_n ≥ (m+1)/2（prs_harm_dyad），层 2 闭合后经
   ∏(1−1/p)^{-1} ≥ H_n 传递即得素数倒数和无界，log log 形留续件。
   【使用位指引（续件）】素数六件（pr_*／pen_*／plm_*）＋Bertrand
   （pbr_*）＋LW0FactGrowth 桥（pfb_*）＋HansonLcm/hl_lcm_upto ——
   全部使用位在 O1 的两缺口，本件零消费（依赖面最小化）。 *)

(* ---- §9 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions prs_mul_div_le.
Print Assumptions prs_div_lower.
Print Assumptions prs_hsum_block.
Print Assumptions prs_hsum_scale2.
Print Assumptions prs_harm_dyad.
Print Assumptions prs_harm_diverge.
Print Assumptions prs_geo_euler_eq.
Print Assumptions prs_geo_euler.
