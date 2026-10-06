(* ===================================================================== *)
(*  abl_ln2_bsum_cauchy.v —— ln2 无理性链·lns_bsum Cauchy 见证 Cb 槽闭合件    *)
(*  （DK·lns_bsum Cauchy 见证 Cb 槽闭合·DE 尾登记下片）              *)
(*  使命: 闭合装配件 abl_ln2_reorder_assembly §E 勘录①——lns_bsum 的         *)
(*        Cauchy 见证 Cb 显式悬置槽。配方照 DE 原文「下片工单」执行:          *)
(*        lns_btail_pterm4 尾隙 ⟹ lnt_bkC_le_pow2 二幂桥 ⟹ Archimedean      *)
(*        多项式衰减 N 公式，lnr_cauchy 同构重排（p=0 档/p≥1 档双档）。四层:  *)
(*        ①显式 N 公式件 lnb2_N（CL 最小性见证形态：p=0 支 N:=8·den(eps)，   *)
(*          p≥1 支 N:=2p+2^{S p}·den(eps)；den(eps) 即 DE 配方 log₂(1/eps)   *)
(*          的 Archimedean 倍增替代，配方 diff 见头注与 §A 注记）；          *)
(*        ②p=0 形族件：k!/(k+1)! = 1/(k+1) 与 2^{-k} = 2/2^{S k} 两分数     *)
(*          等式（lnb2_qfrac_eq 交叉乘工器件闭合）⟹ lnf_bterm 0 k = 2·u(0,k) *)
(*          （lnb2_b0_eq）⟹ p=0 加法形模量 lnb2_gap_mod0（8·u 形）；         *)
(*        ③多项式二幂桥（本件新数学）：4·u(n,k) ≤ 2^{S n}/(S k)（n ≥ 1，     *)
(*          lnb2_pterm4_le——bkC(n+k,n) ≤ 2^{n+k} ⟹ 4·bkC ≤ 2^{S n}·2^{S k}, *)
(*          全 k 无窗口，较 DE 配方的 4·u(n,SM) 窗口形更免窗口）；           *)
(*        ④消失引擎＋Cauchy 本体：lnb2_vanish0（N:=8·den eps）/              *)
(*          lnb2_vanish4（N:=2n+2^{S n}·den eps，含 2n 窗口保障项，即 DE     *)
(*          「N:=SM+2n+…」形的定装）⟹ lnb2_cauchy（lnr_cauchy 同构重排：     *)
(*          WLOG leb 劈分＋单调非负 Qabs 消解＋模量传送）——assembly §E 的    *)
(*          Cb 槽就此有主：lnb2_Ireal 装配读出＋腿重定向闭合实例             *)
(*          lnb2_identity_leg_bterm_closed＋vm_compute 数值锚（小 eps 定装）。*)
(*  与 DE 配方 diff（三条，均在增严方向）:                                   *)
(*        ①DE 配方用 lns_btail_pterm4（4·u 窗口形，2n ≤ M+4）；本件在二幂桥  *)
(*          处改用全 k 无窗口的 bkC 二幂上界，窗口仅在 cauchy 本体模量段     *)
(*          使用（2n ≤ K+4 由 N ≥ 2n 保障）；                                *)
(*        ②DE 配方 u ≤ 2^{n−1}/(SM+1)——本件直取 4·u ≤ 2^{S n}/(S k)，       *)
(*          免去 n−1 分裂（同一不等式的 4 倍归并形）；                       *)
(*        ③DE 配方 N:=…+log₂(1/eps)——本件 N:=2n+2^{S n}·den(eps)（          *)
(*          Archimedean 定装，lnr_cauchy/lnr_vanish 同款纪律）。             *)
(*        ④任务指令所列尾隙名 lnw_wgap_geo_quarter（DH 新常数 2^{n+2}）全树    *)
(*          无定义（世界树/现役池/attn 检索零命中）——本件改使用链内实存      *)
(*          尾隙件 lnt_pterm_tail/lns_btail_pterm4/lnt_bkC_le_pow2，另立     *)
(*          2^{S n} 常数桥 lnb2_pterm4_le（4·u ≤ 2^{S n}/(S k)，全 k 无窗口） *)
(*          沿用该新常数配方口径（4=2² 归并形，见 diff ①②）。               *)
(*  依赖: Stdlib QArith/Arith(Arith.Factorial:fact)/ZArith/Lia；S01_BaseRing  *)
(*        S02_CauchyComplete S03_QExp；PolyIntegral PadeErrorIntegral        *)
(*        BeukersLists BeukersVariant PintMono；PsQReindex RealIdentity；     *)
(*        池内拷贝链 abl_ln2_tail_bound（AP）→ abl_ln2_sharp_weight（CO）→   *)
(*        abl_ln2_ireal（BH）→ abl_ln2_reorder（DA）→ abl_ln2_reorder_       *)
(*        assembly（DE）→ 本件。                                             *)
(*  对标: DE 报告 lns_bsum 真族载体与 §E Cb 槽悬置（前件 abl_ln2_reorder_    *)
(*        assembly.v 头注勘录①）；BH lnr_cauchy 双档骨架（lnb2_cauchy 同构  *)
(*        重排源）；AP lnt_pterm_tail/lnt_pterm_gap/lnt_bkC_le_pow2；        *)
(*        AE 报告 §3 子件(c)「尾项控制走柯西胶水」；CL 最小性见证形态        *)
(*        （N 公式作显式定义件入语句）。                                     *)
(*  构造性: 全件 Qed、零承认；Set 语句主形全 QeqT/QleT'/QltT/sigT（cauchy    *)
(*        本体即 sigT Set 形见证），Qeq/Qle/Qlt 仅 Prop 推理面；nat 归纳零    *)
(*        公理；可提取（文尾 Separate Extraction lnb2_N/lnb2_Ireal）；文尾   *)
(*        Print Assumptions 全 Closed。                                      *)
(*  编译配方: source <Live>/toolchain/env.sh && rocq c -native-compiler no   *)
(*        -Q <world>/vo_local_world_unified_0930 ""（独占沙箱池 ln2_cauchy/， *)
(*        道闸≤1；同池链序 tail_bound → sharp_weight → ireal → reorder →     *)
(*        reorder_assembly → 本件）。工艺注记: Qeq 桥一律 setoid_rewrite；    *)
(*        QltT 无 Proper 实例——等式传送一律走 lnr_qltT_transfer_l/r；        *)
(*        nat_scope 下算式显式 %Q/%nat 标注。                                *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex RealIdentity.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.
Require Import abl_ln2_reorder.
Require Import abl_ln2_reorder_assembly.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 显式 N 公式件（CL 最小性见证形态）                                        *)
(* ============================================================ *)

(* ★ N 公式：p=0 支 N := 8·den(eps)；p ≥ 1 支 N := 2p + 2^{S p}·den(eps)。
   den(eps) 即 DE 配方 log₂(1/eps) 的 Archimedean 定装替代位
   （lnr_cauchy/lnr_vanish 同款纪律）；p≥1 支的 2p 项为模量窗口保障项。 *)
Definition lnb2_N (p : nat) (eps : Q) : nat :=
  match p with
  | 0 => 8 * Z.to_nat (Z.pos (Qden eps))
  | Datatypes.S p' =>
      2 * Datatypes.S p'
        + 2 ^ Datatypes.S (Datatypes.S p') * Z.to_nat (Z.pos (Qden eps))
  end.

(* den 正分数的 nat 下界桥：Z.to_nat (Z.pos pd) ≥ 1 *)
Lemma lnb2_den_ge1 : forall pd : positive, (1 <= Z.to_nat (Z.pos pd))%nat.
Proof.
  intro pd.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  assert (H : (0 < Z.to_nat (Z.pos pd))%nat).
  { apply (proj1 (Z2Nat.inj_lt 0 (Z.pos pd) ltac:(lia) ltac:(lia))). exact Hpd. }
  lia.
Qed.

(* N 公式窗口保障：p ≥ 1 ⟹ 2p ≤ N(p,eps) *)
Lemma lnb2_N_ge2p : forall (p : nat) (eps : Q),
  (1 <= p)%nat -> (2 * p <= lnb2_N p eps)%nat.
Proof.
  intros p eps Hp. destruct p as [| p']; [lia |].
  destruct eps as [pn pd].
  unfold lnb2_N. cbn [Qden].
  pose proof (lnb2_den_ge1 pd). lia.
Qed.

(* ============================================================ *)
(* §B Q 分数交叉乘等式工器件（Qinv 免归一化）                                    *)
(* ============================================================ *)

(* 交叉乘等式：0 < b、0 < d 且 a·d == c·b ⟹ a·b⁻¹ == c·d⁻¹。
   （Qinv 不归一化：消去经 lnt_qinv_mul_cancel，全程 Qeq_trans/ring。） *)
Lemma lnb2_qfrac_eq : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> (a * d == c * b)%Q -> ((a * Qinv b) == (c * Qinv d))%Q.
Proof.
  intros a b c d Hb Hd H.
  assert (Hb0 : ~ (b == 0%Q)) by (apply lnt_qneq_of_eq0; exact Hb).
  assert (Hd0 : ~ (d == 0%Q)) by (apply lnt_qneq_of_eq0; exact Hd).
  assert (Eb : (Qinv b * b)%Q == 1%Q) by (apply lnt_qinv_mul_cancel; exact Hb0).
  assert (Ed : (Qinv d * d)%Q == 1%Q) by (apply lnt_qinv_mul_cancel; exact Hd0).
  assert (Ed' : (d * Qinv d)%Q == 1%Q).
  { rewrite (Qmult_comm d (Qinv d)). exact Ed. }
  assert (Ebd : (Qinv (b * d) * (b * d))%Q == 1%Q).
  { apply lnt_qinv_mul_cancel. intro Hz.
    assert (Hb2 : ((b * d) * Qinv d)%Q == 0%Q) by (rewrite Hz; reflexivity).
    assert (E3 : ((b * d) * Qinv d)%Q == (b * (d * Qinv d))%Q) by ring.
    rewrite E3, Ed', Qmult_1_r in Hb2. exact (Hb0 Hb2). }
  assert (E1 : ((a * Qinv b) * (b * d))%Q == (a * d)%Q).
  { apply (Qeq_trans _ ((a * d) * (Qinv b * b))%Q).
    - ring.
    - rewrite Eb. ring. }
  assert (E2 : ((c * Qinv d) * (b * d))%Q == (c * b)%Q).
  { apply (Qeq_trans _ ((c * b) * (Qinv d * d))%Q).
    - ring.
    - rewrite Ed. ring. }
  assert (Ec : ((a * Qinv b) * (b * d))%Q == ((c * Qinv d) * (b * d))%Q).
  { rewrite E1, E2. exact H. }
  assert (EM : ((b * d) * Qinv (b * d))%Q == 1%Q).
  { rewrite (Qmult_comm (b * d) (Qinv (b * d))). exact Ebd. }
  apply (Qeq_trans _ (((a * Qinv b) * (b * d)) * Qinv (b * d))%Q).
  - apply (Qeq_trans _ ((a * Qinv b) * ((b * d) * Qinv (b * d)))%Q).
    + rewrite EM. symmetry. apply Qmult_1_r.
    + ring.
  - apply (Qeq_trans _ (((c * Qinv d) * (b * d)) * Qinv (b * d))%Q).
    + rewrite Ec. reflexivity.
    + apply (Qeq_trans _ ((c * Qinv d) * ((b * d) * Qinv (b * d)))%Q).
      * ring.
      * rewrite EM. apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* §C p=0 形族件：lnf_bterm 0 k = 2·u(0,k)                                      *)
(* ============================================================ *)

(* 分数等式①：k!/(k+1)! = 1/(k+1)（q_fact 面，lns_qfact_Zofnat 桥） *)
Lemma lnb2_fact_frac : forall k : nat,
  ((q_fact 0 * q_fact (0 + k)) * Qinv (q_fact (2 * 0 + k + 1)))%Q
  == ((1 # 1)%Q * Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q))%Q.
Proof.
  intro k.
  assert (Ek : 0 + k = k) by reflexivity. rewrite Ek.
  rewrite !lns_qfact_Zofnat.
  assert (Ef : fact (2 * 0 + k + 1) = Datatypes.S k * fact k).
  { replace (2 * 0 + k + 1) with (Datatypes.S k) by lia. apply lns_fact_succ. }
  rewrite Ef, Nat2Z.inj_mul.
  assert (Ef0 : fact 0 = 1%nat) by reflexivity. rewrite Ef0.
  change (Z.of_nat 1) with 1%Z.
  apply lnb2_qfrac_eq.
  - (* 0 < (Z.of_nat (S k)·Z.of_nat (fact k)) # 1 *)
    apply rx_Qlt_Z1.
    assert (H1 : (0 < Z.of_nat (Datatypes.S k))%Z)
      by (apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S k))); lia).
    assert (H2 : (0 < Z.of_nat (fact k))%Z)
      by (apply (proj1 (Nat2Z.inj_lt 0 (fact k)));
          apply (proj1 (Nat.neq_0_lt_0 (fact k))); apply fact_neq_0).
    assert (H2' : (1 <= Z.of_nat (fact k))%Z) by lia.
    nia.
  - apply rx_Qlt_Z1. lia.
  - (* 交叉乘 Z 核 *)
    unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul].
    rewrite !Z.mul_1_r, ?Pos.mul_1_r. ring.
Qed.

(* 分数等式②：2^{-k} = 2/2^{S k}（q_pow 面，q_pow_succ 桥） *)
Lemma lnb2_pow2_frac : forall k : nat,
  Qinv (q_pow (2 # 1)%Q k)
  == ((2 # 1)%Q * Qinv (q_pow (2 # 1)%Q (Datatypes.S k)))%Q.
Proof.
  intro k.
  apply (Qeq_trans _ ((1 # 1)%Q * Qinv (q_pow (2 # 1)%Q k))%Q).
  - rewrite Qmult_1_l. reflexivity.
  - apply (lnb2_qfrac_eq (1 # 1)%Q (q_pow (2 # 1)%Q k) (2 # 1)%Q
                         (q_pow (2 # 1)%Q (Datatypes.S k))).
    + apply lnt_pow2_pos.
    + apply lnt_pow2_pos.
    + rewrite Qmult_1_l. apply q_pow_succ.
Qed.

(* ★ p=0 形族读出：lnf_bterm 0 k = (1/2^k)·(k!/(k+1)!) = 2·u(0,k) *)
Lemma lnb2_b0_eq : forall k : nat,
  QeqT (lnf_bterm 0 k) ((2 # 1)%Q * lnt_pterm 0 k)%Q.
Proof.
  intro k. apply qeq_imp_qeqT.
  unfold lnf_bterm, lnt_pterm, Qdiv.
  setoid_rewrite lnb2_fact_frac.
  setoid_rewrite lnb2_pow2_frac.
  assert (Eb : bkC (0 + k) 0 = 1%nat).
  { replace (0 + k) with k by lia. destruct k as [| k']; reflexivity. }
  rewrite Eb.
  rewrite (Qinv_mult_distr ((Z.of_nat (Datatypes.S k) # 1)%Q)
                           (q_pow (2 # 1)%Q (Datatypes.S k))).
  ring.
Qed.

(* ============================================================ *)
(* §D 加法形模量件（lnr_gap_mod0/lnr_gap_mod 的真族同构重排）                     *)
(* ============================================================ *)

(* p=0 加法形模量：S_{M+d} − S_M ≤ 8·u(0,S M)（lnb2_b0_eq＋lnt_pterm_tail） *)
Lemma lnb2_gap_mod0 : forall M d : nat,
  QleT' (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q
        ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q.
Proof.
  intros M d. apply Qle_to_QleT'.
  apply (Qle_trans _ (lns_bsum 0 M
                      + ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q
                      - lns_bsum 0 M)%Q).
  - apply (Qplus_le_compat (lns_bsum 0 (M + d))
                           (lns_bsum 0 M
                            + ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)
                           (- lns_bsum 0 M) (- lns_bsum 0 M)).
    + apply (Qle_trans _ (sum_upto d (fun i : nat => lnf_bterm 0 (M + Datatypes.S i))
                          + lns_bsum 0 M)%Q).
      * assert (Hr : lns_bsum 0 (M + d)
                     == sum_upto d (fun i : nat => lnf_bterm 0 (M + Datatypes.S i))
                        + lns_bsum 0 M)
          by (rewrite lns_bsum_range; ring).
        apply qeq_le. exact Hr.
      * rewrite (Qplus_comm (lns_bsum 0 M)
                  ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q).
        apply lnr_Qplus_le_compat_r.
        apply (Qle_trans _ (sum_upto d (fun i : nat =>
                                       (2 # 1)%Q * lnt_pterm 0 (M + Datatypes.S i)))%Q).
        -- apply QleT'_to_Qle. apply lnt_sum_le.
           intros i Hi. apply Qle_to_QleT'. apply qeq_le.
           apply qeqT_imp_qeq. apply lnb2_b0_eq.
        -- apply (Qle_trans _ ((2 # 1)%Q
                               * sum_upto d (fun i : nat =>
                                             lnt_pterm 0 (M + Datatypes.S i)))%Q).
           ++ apply qeq_le. apply lnt_sum_scale.
           ++ apply (Qle_trans _ ((2 # 1)%Q
                                  * ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)%Q).
              ** apply QleT'_to_Qle.
                 apply (qleT'_mult_compat_l
                          (sum_upto d (fun i : nat =>
                                        lnt_pterm 0 (M + Datatypes.S i)))%Q
                          ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q
                          (2 # 1)%Q).
                 --- apply Qle_to_QleT'. unfold Qle. cbn. lia.
                 --- exact (lnt_pterm_tail 0 M d ltac:(lia)).
              ** apply qeq_le. ring.
    + apply Qle_refl.
  - apply qeq_le. ring.
Qed.

(* p ≥ 1 加法形模量：S_{M+d} − S_M ≤ 4·u(n,S M)（lns_bsum_range＋ *)
(* lns_btail_pterm4——DE 配方的尾隙件直接使用） *)
Lemma lnb2_gap_mod4 : forall n M d : nat,
  (1 <= n)%nat -> (2 * n <= M + 4)%nat ->
  QleT' (lns_bsum n (M + d) - lns_bsum n M)%Q
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
Proof.
  intros n M d Hn HM. apply Qle_to_QleT'.
  apply (Qle_trans _ (lns_bsum n M
                      + ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q
                      - lns_bsum n M)%Q).
  - apply (Qplus_le_compat (lns_bsum n (M + d))
                           (lns_bsum n M
                            + ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)
                           (- lns_bsum n M) (- lns_bsum n M)).
    + apply (Qle_trans _ (sum_upto d (fun i : nat => lnf_bterm n (M + Datatypes.S i))
                          + lns_bsum n M)%Q).
      * assert (Hr : lns_bsum n (M + d)
                     == sum_upto d (fun i : nat => lnf_bterm n (M + Datatypes.S i))
                        + lns_bsum n M)
          by (rewrite lns_bsum_range; ring).
        apply qeq_le. exact Hr.
      * rewrite (Qplus_comm (lns_bsum n M)
                  ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
        apply lnr_Qplus_le_compat_r. apply QleT'_to_Qle.
        apply lns_btail_pterm4; assumption.
    + apply Qle_refl.
  - apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* §E 多项式二幂桥（本件新数学③）：4·u(n,k) ≤ 2^{S n}/(S k)                      *)
(* ============================================================ *)

Theorem lnb2_pterm4_le : forall n k : nat,
  (1 <= n)%nat ->
  QleT' ((4 # 1)%Q * lnt_pterm n k)%Q
        ((Z.of_nat (2 ^ Datatypes.S n) # 1)%Q
         * Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q))%Q.
Proof.
  intros n k Hn. apply Qle_to_QleT'.
  unfold lnt_pterm, Qdiv.
  rewrite lnt_qpow_Zofnat.
  assert (Eshape : ((4 # 1)%Q * ((Z.of_nat (bkC (n + k) n) # 1)%Q
                                 * Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q
                                         * (Z.of_nat (2 ^ Datatypes.S k) # 1)%Q)))%Q
                == (((4 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)%Q)%Q
                    * Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q
                            * (Z.of_nat (2 ^ Datatypes.S k) # 1)%Q))) by ring.
  rewrite Eshape.
  apply (lns_qdiv_le
          (((4 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)%Q))%Q
          ((Z.of_nat (Datatypes.S k) # 1)%Q
           * (Z.of_nat (2 ^ Datatypes.S k) # 1)%Q)%Q
          (Z.of_nat (2 ^ Datatypes.S n) # 1)%Q
          (Z.of_nat (Datatypes.S k) # 1)%Q).
  - apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + apply rx_Qlt_Z1.
      apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S k))).
      pose proof (lnt_pow2_ge1 (Datatypes.S k)). lia.
  - apply rx_Qlt_Z1. lia.
  - (* a·d ≤ c·b 的 Z 核：4·bkC ≤ 2^{S n}·2^{S k}（lnt_bkC_le_pow2 桥） *)
    assert (HZsk : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
    assert (Hbk : (bkC (n + k) n <= 2 ^ (n + k))%nat)
      by (apply lnt_bkC_le_pow2; lia).
    assert (Hpow : (2 ^ Datatypes.S n * 2 ^ Datatypes.S k
                    = 2 ^ (Datatypes.S n + Datatypes.S k))%nat)
      by (symmetry; apply Nat.pow_add_r).
    assert (H1 : (4 * bkC (n + k) n
                  <= 2 ^ Datatypes.S n * 2 ^ Datatypes.S k)%nat).
    { apply Nat.le_trans with (4 * 2 ^ (n + k))%nat.
      - apply Nat.mul_le_mono_l. exact Hbk.
      - rewrite Hpow.
        replace (Datatypes.S n + Datatypes.S k)
          with (Datatypes.S (Datatypes.S (n + k))) by lia.
        cbn [Nat.pow]. lia. }
    assert (HZ : (Z.of_nat (4 * bkC (n + k) n)
                  <= Z.of_nat (2 ^ Datatypes.S n * 2 ^ Datatypes.S k))%Z)
      by (apply Nat2Z.inj_le; exact H1).
    rewrite (Nat2Z.inj_mul 4 (bkC (n + k) n)) in HZ.
    change (Z.of_nat 4) with 4%Z in HZ.
    rewrite (Nat2Z.inj_mul (2 ^ Datatypes.S n) (2 ^ Datatypes.S k)) in HZ.
    assert (Eg : (Z.of_nat (2 ^ Datatypes.S n)
                  * (Z.of_nat (Datatypes.S k) * Z.of_nat (2 ^ Datatypes.S k))
                  = (Z.of_nat (2 ^ Datatypes.S n) * Z.of_nat (2 ^ Datatypes.S k))
                  * Z.of_nat (Datatypes.S k))%Z) by ring.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    rewrite !Z.mul_1_r, ?Pos.mul_1_r.
    first [ nia
          | (rewrite Eg; apply Z.mul_le_mono_nonneg_r;
             [ exact HZsk | exact HZ ]) ].
Qed.

(* ============================================================ *)
(* §F 消失引擎（显式 N 公式入语句）                                              *)
(* ============================================================ *)

(* p=0 消失引擎：N := 8·den(eps)，K ≥ N ⟹ 8·u(0,S K) < eps（QltT Set 面） *)
Theorem lnb2_vanish0 : forall eps : Q, QltT 0 eps ->
  forall K : nat, (lnb2_N 0 eps <= K)%nat ->
  QltT ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S K)) eps.
Proof.
  intros [pn pd] Heps K HK.
  pose proof (QltT_to_Qlt 0%Q (pn # pd)%Q Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  assert (Hpd1 := lnb2_den_ge1 pd).
  unfold lnb2_N in HK. cbn [Qden] in HK.
  (* 形重排：8·u(0,S K) == 8·(1·dv⁻¹)，dv = (K+2)·2^{K+2} *)
  apply Qlt_to_QltT.
  apply (lnr_qlt_transfer_l
          ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S K))%Q
          ((8 # 1)%Q
           * ((1 # 1)%Q
              * Qinv (((Z.of_nat (Datatypes.S (Datatypes.S K)))
                       * Z.of_nat (2 ^ Datatypes.S (Datatypes.S K))) # 1)%Q))%Q
          ((pn # pd)%Q)).
  { unfold lnt_pterm, Qdiv. rewrite lnt_qpow_Zofnat.
    assert (Eb : bkC (0 + Datatypes.S K) 0 = 1%nat) by reflexivity.
    rewrite Eb. apply Qeq_refl. }
  apply (lnr_qdiv_lt_intro_pre ((8 # 1)%Q) ((1 # 1)%Q) ((pn # pd)%Q)
           (((Z.of_nat (Datatypes.S (Datatypes.S K)))
             * Z.of_nat (2 ^ Datatypes.S (Datatypes.S K))) # 1)%Q).
  - apply rx_Qlt_Z1.
    assert (HA : (0 < Z.of_nat (Datatypes.S (Datatypes.S K)))%Z)
      by (apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S (Datatypes.S K)))); lia).
    assert (HB : (1 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S K)))%Z).
    { apply (proj1 (Nat2Z.inj_le 1 (2 ^ Datatypes.S (Datatypes.S K)))).
      pose proof (lnt_pow2_ge1 (Datatypes.S (Datatypes.S K))). lia. }
    nia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    rewrite !Z.mul_1_r, !Pos.mul_1_r.
    assert (H8n : (8 * Z.to_nat (Z.pos pd) + 2
                   <= Datatypes.S (Datatypes.S K))%nat) by lia.
    assert (H8 : (Z.of_nat (8 * Z.to_nat (Z.pos pd) + 2)
                  <= Z.of_nat (Datatypes.S (Datatypes.S K)))%Z)
      by (apply Nat2Z.inj_le; exact H8n).
    rewrite Nat2Z.inj_add in H8.
    rewrite (Nat2Z.inj_mul 8 (Z.to_nat (Z.pos pd))) in H8.
    rewrite (Z2Nat.id (Z.pos pd)) in H8 by lia.
    change (Z.of_nat 8) with 8%Z in H8.
    change (Z.of_nat 2) with 2%Z in H8.
    assert (HP : (1 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S K)))%Z).
    { apply (proj1 (Nat2Z.inj_le 1 (2 ^ Datatypes.S (Datatypes.S K)))).
      pose proof (lnt_pow2_ge1 (Datatypes.S (Datatypes.S K))). lia. }
    assert (HPn : (1 <= pn)%Z) by lia.
    nia.
Qed.

(* p ≥ 1 消失引擎：N := 2n + 2^{S n}·den(eps)（DE「N:=SM+2n+…」形定装）， *)
(* K ≥ N ⟹ 4·u(n,S K) < eps（二幂桥 lnb2_pterm4_le 直接使用，QltT Set 面） *)
Theorem lnb2_vanish4 : forall (n : nat) (eps : Q),
  (1 <= n)%nat -> QltT 0 eps ->
  forall K : nat, (lnb2_N n eps <= K)%nat ->
  QltT ((4 # 1)%Q * lnt_pterm n (Datatypes.S K)) eps.
Proof.
  intros n eps Hn Heps K HK.
  destruct n as [| n']; [lia |].
  destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd)%Q Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  assert (Hpd1 := lnb2_den_ge1 pd).
  unfold lnb2_N in HK. cbn [Qden] in HK.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans
          ((4 # 1)%Q * lnt_pterm (Datatypes.S n') (Datatypes.S K))%Q
          ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n')) # 1)%Q
           * Qinv ((Z.of_nat (Datatypes.S (Datatypes.S K)) # 1)%Q))%Q
          ((pn # pd)%Q)).
  - apply QleT'_to_Qle. apply lnb2_pterm4_le. lia.
  - apply (lnr_qdiv_lt_intro_pre
             ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n')) # 1)%Q)
             ((1 # 1)%Q) ((pn # pd)%Q)
             ((Z.of_nat (Datatypes.S (Datatypes.S K)) # 1)%Q)).
    + apply rx_Qlt_Z1. lia.
    + unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
      rewrite !Z.mul_1_r, !Pos.mul_1_r.
      assert (HZKn : (2 ^ Datatypes.S (Datatypes.S n')
                      * Z.to_nat (Z.pos pd) + 2
                      <= Datatypes.S (Datatypes.S K))%nat) by lia.
      assert (HZK : (Z.of_nat (2 ^ Datatypes.S (Datatypes.S n')
                                     * Z.to_nat (Z.pos pd) + 2)
                     <= Z.of_nat (Datatypes.S (Datatypes.S K)))%Z)
        by (apply Nat2Z.inj_le; exact HZKn).
      rewrite Nat2Z.inj_add in HZK.
      rewrite (Nat2Z.inj_mul (2 ^ Datatypes.S (Datatypes.S n'))
                             (Z.to_nat (Z.pos pd))) in HZK.
      rewrite (Z2Nat.id (Z.pos pd)) in HZK by lia.
      change (Z.of_nat 2) with 2%Z in HZK.
      assert (HPn : (1 <= pn)%Z) by lia.
      nia.
Qed.

(* sigT 形读出（DE 配方语句形：∀eps>0, ∃N, ∀K≥N, 模量 < eps） *)
Theorem lnb2_vanish0_sigT : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall K : nat, (N <= K)%nat ->
          QltT ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S K)) eps).
Proof.
  intros eps Heps. exists (lnb2_N 0 eps). intros K HK.
  apply lnb2_vanish0; assumption.
Qed.

Theorem lnb2_vanish4_sigT : forall (n : nat) (eps : Q),
  (1 <= n)%nat -> QltT 0 eps ->
  sigT (fun N : nat => forall K : nat, (N <= K)%nat ->
          QltT ((4 # 1)%Q * lnt_pterm n (Datatypes.S K)) eps).
Proof.
  intros n eps Hn Heps. exists (lnb2_N n eps). intros K HK.
  apply lnb2_vanish4; assumption.
Qed.

(* ============================================================ *)
(* §G Cauchy 本体（Cb 槽见证：lnr_cauchy 同构重排）                              *)
(* ============================================================ *)

(* ★ Cb 槽见证：forall p, cauchy (lns_bsum p)——assembly §E 悬置位就此闭合。
   p=0 支走 8·u 档（lnb2_gap_mod0/lnb2_vanish0），p≥1 支走 4·u 档
   （lnb2_gap_mod4/lnb2_vanish4）；WLOG leb 劈分＋单调非负 Qabs 消解。 *)
Theorem lnb2_cauchy : forall p : nat, cauchy (lns_bsum p).
Proof.
  intro p. destruct p as [| p'].
  - (* p = 0：N := 8·den(eps) *)
    intros eps Heps. destruct eps as [pn pd].
    exists (lnb2_N 0 (pn # pd)%Q).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lns_bsum 0 m - lns_bsum 0 n)%Q
                     == (lns_bsum 0 m - lns_bsum 0 n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lns_bsum 0 n - lns_bsum 0 n)%Q).
        - apply qeq_le. ring.
        - apply (Qplus_le_compat (lns_bsum 0 n) (lns_bsum 0 m)
                                 (- lns_bsum 0 n)%Q (- lns_bsum 0 n)%Q).
          + apply lns_bsum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S n))%Q).
      * apply QleT'_to_Qle. apply lnb2_gap_mod0.
      * apply QltT_to_Qlt. apply lnb2_vanish0; [exact Heps | lia].
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lns_bsum 0 m - lns_bsum 0 n)%Q
                     == (lns_bsum 0 n - lns_bsum 0 m)%Q).
      { assert (Hmono : Qle (lns_bsum 0 m) (lns_bsum 0 n))
          by (apply lns_bsum_mono; lia).
        assert (Hneg : Qle (lns_bsum 0 m - lns_bsum 0 n)%Q 0%Q).
        { apply (Qle_trans _ (lns_bsum 0 n - lns_bsum 0 n)%Q).
          - apply (Qplus_le_compat (lns_bsum 0 m) (lns_bsum 0 n)
                                   (- lns_bsum 0 n)%Q (- lns_bsum 0 n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply qeq_le. ring. }
        apply Qeq_trans with (-(lns_bsum 0 m - lns_bsum 0 n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S m))%Q).
      * apply QleT'_to_Qle. apply lnb2_gap_mod0.
      * apply QltT_to_Qlt. apply lnb2_vanish0; [exact Heps | lia].
  - (* p = S p' ≥ 1：N := 2p + 2^{S p}·den(eps) *)
    intros eps Heps. destruct eps as [pn pd].
    exists (lnb2_N (Datatypes.S p') (pn # pd)%Q).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    assert (Hw : (2 * Datatypes.S p' <= n + 4)%nat
                 /\ (2 * Datatypes.S p' <= m + 4)%nat).
    { pose proof (lnb2_N_ge2p (Datatypes.S p') (pn # pd)%Q ltac:(lia)).
      split; lia. }
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lns_bsum (Datatypes.S p') m
                           - lns_bsum (Datatypes.S p') n)%Q
                     == (lns_bsum (Datatypes.S p') m
                         - lns_bsum (Datatypes.S p') n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lns_bsum (Datatypes.S p') n
                            - lns_bsum (Datatypes.S p') n)%Q).
        - apply qeq_le. ring.
        - apply (Qplus_le_compat (lns_bsum (Datatypes.S p') n)
                                 (lns_bsum (Datatypes.S p') m)
                                 (- lns_bsum (Datatypes.S p') n)%Q
                                 (- lns_bsum (Datatypes.S p') n)%Q).
          + apply lns_bsum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _
              ((4 # 1)%Q * lnt_pterm (Datatypes.S p') (Datatypes.S n))%Q).
      * apply QleT'_to_Qle. apply lnb2_gap_mod4; lia.
      * apply QltT_to_Qlt. apply lnb2_vanish4; [lia | exact Heps | exact Hn].
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lns_bsum (Datatypes.S p') m
                           - lns_bsum (Datatypes.S p') n)%Q
                     == (lns_bsum (Datatypes.S p') n
                         - lns_bsum (Datatypes.S p') m)%Q).
      { assert (Hmono : Qle (lns_bsum (Datatypes.S p') m)
                            (lns_bsum (Datatypes.S p') n))
          by (apply lns_bsum_mono; lia).
        assert (Hneg : Qle (lns_bsum (Datatypes.S p') m
                            - lns_bsum (Datatypes.S p') n)%Q 0%Q).
        { apply (Qle_trans _ (lns_bsum (Datatypes.S p') n
                              - lns_bsum (Datatypes.S p') n)%Q).
          - apply (Qplus_le_compat (lns_bsum (Datatypes.S p') m)
                                   (lns_bsum (Datatypes.S p') n)
                                   (- lns_bsum (Datatypes.S p') n)%Q
                                   (- lns_bsum (Datatypes.S p') n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply qeq_le. ring. }
        apply Qeq_trans with (-(lns_bsum (Datatypes.S p') m
                                - lns_bsum (Datatypes.S p') n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _
              ((4 # 1)%Q * lnt_pterm (Datatypes.S p') (Datatypes.S m))%Q).
      * apply QleT'_to_Qle. apply lnb2_gap_mod4; lia.
      * apply QltT_to_Qlt. apply lnb2_vanish4; [lia | exact Heps | exact Hm].
Qed.

(* Cb 槽装配读出：lns_Ibreal 的具身版（Cb := lnb2_cauchy 有主） *)
Definition lnb2_Ireal (p : nat) : Real :=
  lnr_Ireal_pack (lns_bsum p) (lnb2_cauchy p).

Lemma lnb2_Ireal_proj : forall (p k : nat),
  projT1 (lnb2_Ireal p) k == lns_bsum p k.
Proof. intros p k. reflexivity. Qed.

(* ★ 腿重定向全闭合实例：assembly §E lns_identity_leg_bterm_transfer 在   *)
(* Cb := lnb2_cauchy 处的定装——Cb 槽不再悬置 *)
Theorem lnb2_identity_leg_bterm_closed : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnb2_Ireal p)) ->
  ri_identity_leg (fun p => lnb2_Ireal p) ->
  ri_identity_leg I.
Proof.
  intros I HI Hleg.
  exact (lns_identity_leg_bterm_transfer I lnb2_cauchy HI Hleg).
Qed.

(* ============================================================ *)
(* §H vm_compute 数值锚（小 eps 定装：eps = 1/1000）                             *)
(* ============================================================ *)

(* N 公式读出锚①：p=1 支 N := 2·1 + 2²·1000 = 4002 *)
Theorem lnb2_N1_anchor : NatLe (lnb2_N 1 (1 # 1000)%Q) 4002.
Proof. vm_compute. reflexivity. Qed.

(* N 公式读出锚②：p=0 支 N := 8·1000 = 8000 *)
Theorem lnb2_N0_anchor : NatLe (lnb2_N 0 (1 # 1000)%Q) 8000.
Proof. vm_compute. reflexivity. Qed.

(* 模量消失数值锚：N 公式阈值处（K = 4002）4·u(1,4003) < 1/1000 定装 *)
Theorem lnb2_modulus_anchor :
  QltT ((4 # 1)%Q * lnt_pterm 1 4003)%Q ((1 # 1000)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 可提取闭合（Set 层 witness 面）                                              *)
(* ============================================================ *)

Separate Extraction lnb2_N lnb2_Ireal.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。                *)
(* ============================================================ *)

Print Assumptions lnb2_b0_eq.
Print Assumptions lnb2_gap_mod0.
Print Assumptions lnb2_gap_mod4.
Print Assumptions lnb2_pterm4_le.
Print Assumptions lnb2_vanish0.
Print Assumptions lnb2_vanish4.
Print Assumptions lnb2_vanish0_sigT.
Print Assumptions lnb2_vanish4_sigT.
Print Assumptions lnb2_cauchy.
Print Assumptions lnb2_identity_leg_bterm_closed.
Print Assumptions lnb2_Ireal_proj.
Print Assumptions lnb2_N1_anchor.
Print Assumptions lnb2_N0_anchor.
Print Assumptions lnb2_modulus_anchor.
