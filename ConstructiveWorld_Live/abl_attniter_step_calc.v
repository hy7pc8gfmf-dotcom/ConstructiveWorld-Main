(* ==========================================================================)
   abl_attniter_step_calc.v — 收敛计算器系列第六件（UpReqAttnIter 收缩迭代面，aic_ 前缀）
   使命：UpReqAttnIter.v 的 agq_ 收缩迭代链（率证书在案、主定理 2 agq_tv_iter 语句面显式率 req_r_pow
      omd n、主定理 3 的 sigT N 走 arch_pow_i 阿基米德坑）缺「精度到步数」Defined 计算器。本件补齐
      三段：率抽取（omd := req_minus one delta）直使用宿主出节双证书；nat 定点档首破严格档＋首破
      最小性见证两件；req 实面逐形对应 Section（证书子集 22 槽，Prop 序界面 NatLe Set 形重述）。
   对标行：mathlib 马尔可夫链混合时间界（Doeblin minorization 几何收缩）的构造性 Set 层 req 面对应物；
      UpReqAttnIter.v §ReqAttnIter 证书面；同系列 dsc_/asc_/cmc_/mtc2_ 体例。
   三段主面：Part 2 nat 定点档（真 Fixpoint，语句面全 Set 形：aic_ceil_div/aic_iter/aic_pow_iter/aic_k_enum
      严格首破枚举＋correct/logface 两正确性＋首破最小性见证两件＋严格衰减三件＋燃料充足性三件＋
      auto_half）；Part 1 req 实面对应（率抽取双证书＋幂单调 Set 形重述＋诚实 arch 槽计算器＋主定理 2
      直使用＋主件 step_calc(_correct)＋模量 sigT＋端到端双投影三件）。
   Set 形纪律：语句面零 Prop——存在以 sigT、合取以 prod、nat 序界以 NatLe（NatLe_drop/NatLe_lift 双向桥）；
      严格序界以 NatLe (S ·) 表达；宿主 (N <= n) Prop 界在对应面以 NatLe 重述，Prop 界只经 NatLe_drop
      进证明体；假设位零 Hypothesis/零 Prop 型（证书槽均 Set 值语句）。
   已知边界：主机 arch_pow_i 证书槽为诚实接口参数位（构造性居住而无算法内容，同系列边界口径），可执行
      面由 Part 2 nat 定点档承载（真 Fixpoint，Obj.magic=0 附加证）；任意实数率的实面 ceil 构造性桥库内
      确缺，有理数据实面桥由系列前件各 Part 3 在役承载；燃料充足性限衰减域（half 域 2·p ≤ q、E ≥ 2；
      qbound 域 q ≤ E、任意 p<q）；严格档与 le 档语义分立，读数可差一步（各自正确）。
   依赖清单：S01_BaseRing（NatLe/NatLe_drop/NatLe_lift）；S07_RealSetoidExpLog（类与 Import 模块）；
      UpReqAlgebra（req_minus）；UpReqSampling（req_r_pow）；UpReqAttnIter（agq_ 证书族：omd_pos/
      omd_lt_one/r_pow_dec_iter/tv_nonneg/tv_iter/iterate_converges/boltzmann_dist_i/tv_i/
      attention_iter_i）；PeanoNat/Lia/Arith。全部 Require-only 零改动。
   构造性注记：纯构造性/Set 层零 Prop 语句面（nat 面算术不消入实面目标）；非平凡（aic_k_enum 为真
      Fixpoint 首破枚举）；可提取（Separate Extraction Obj.magic=0 附加证）；零公理（尾 PA 全 Closed
      预期）。工艺红线：term-mode 全显式实参；Eval vm_compute 烟测入日志；注释内禁右括号星杠字面。
   编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q vo_local_world_unified_0930 "" abl_attniter_step_calc.v（池内执行）。
   查重登记：顶层名 31 枚全 aic_ 新前缀，与宿主 agq_ 族、系列 asc_/dsc_/cmc_/mtc2_ 前缀零撞零交。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import UpReqAlgebra.
Require Import UpReqSampling.
Require Import UpReqAttnIter.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 2：收缩率定点枚举解算器（真 Fixpoint/首破严格档/Set 形）        *)
(*   收缩率 kappa=p/q（0<p<q）、初值 A、预算 E 的定点表示，首破枚举 N    *)
(*   使 powIter N A < E（严格）。序界全走 NatLe Set 形，严格序界以        *)
(*   NatLe (S ·) 表达。本段含首破最小性见证两件与燃料充足性三件。        *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition aic_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma aic_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (aic_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold aic_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition aic_iter (p q x : nat) : nat := aic_ceil_div (x * p) q.

Lemma aic_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (aic_iter p q x * q).
Proof.
  intros p q x Hq. unfold aic_iter. apply (aic_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：aic_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint aic_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => aic_iter p q (aic_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma aic_pow_iter_comm : forall p q x k,
  aic_pow_iter p q (aic_iter p q x) k = aic_iter p q (aic_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x < e 首破即停（返回已走步数），
   否则走衰减步再搜（Nat.ltb 判定，严格档停机面） *)
Fixpoint aic_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (aic_k_enum f p q (aic_iter p q x) e)
  end.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma aic_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (aic_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (aic_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (aic_iter_step_bound p q (aic_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (aic_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (aic_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (aic_iter p q (aic_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (aic_iter p q (aic_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* 正确性（首破严格面）：燃料内可达，枚举返回的 N 步处上取整值 < e
   （NatLe (S ·) e 严格序界形）。可达见证为 sigT＋prod＋NatLe 全 Set 形。 *)
Theorem aic_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (aic_pow_iter p q x k)) e))) ->
  NatLe (Datatypes.S (aic_pow_iter p q x (aic_k_enum fuel p q x e))) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm.
  - destruct Hterm as [k [Hk Hbound]].
    pose proof (NatLe_drop k 0 Hk) as Hk'.
    assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + apply (NatLe_lift _ _). exact (proj1 (Nat.ltb_lt x e) Hlt).
    + assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      destruct Hterm as [k [Hk Hbound]].
      pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
      destruct k as [| k'].
      * pose proof (NatLe_drop (Datatypes.S (aic_pow_iter p q x 0)) e Hbound)
          as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (aic_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (aic_pow_iter p q (aic_iter p q x) k0)) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (aic_iter p q x) e Hterm').
        simpl.
        rewrite <- (aic_pow_iter_comm p q x
                      (aic_k_enum f p q (aic_iter p q x) e)).
        exact IH.
Qed.

(* 首破最小性见证（本件新数学）：燃料内可达，则对每个早于返回步数 N 的
   步 j（S j ≤ N），第 j 步上取整值仍 ≥ e——枚举读数是首个跌破预算的步。
   （「枚举器最小性未证」边界的 nat 面闭合件。） *)
Theorem aic_k_enum_minimal : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (aic_pow_iter p q x k)) e))) ->
  forall j : nat, NatLe (Datatypes.S j) (aic_k_enum fuel p q x e) ->
  NatLe e (aic_pow_iter p q x j).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm j Hj.
  - exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl in Hj. rewrite Hlt in Hj.
      exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
    + simpl in Hj. rewrite Hlt in Hj.
      assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      pose proof (NatLe_drop (Datatypes.S j)
                    (Datatypes.S (aic_k_enum f p q (aic_iter p q x) e)) Hj)
        as Hj'.
      destruct j as [| j'].
      * simpl. apply (NatLe_lift e x). exact Hge.
      * simpl in Hj'.
        assert (Hj2 : NatLe (Datatypes.S j')
                        (aic_k_enum f p q (aic_iter p q x) e))
          by (apply (NatLe_lift _ _); lia).
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (aic_pow_iter p q (aic_iter p q x) k0)) e))).
        { destruct Hterm as [k [Hk Hbound]].
          pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
          destruct k as [| k'].
          - pose proof (NatLe_drop (Datatypes.S (aic_pow_iter p q x 0)) e Hbound)
              as Hb'.
            simpl in Hb'. lia.
          - simpl in Hbound.
            rewrite <- (aic_pow_iter_comm p q x k') in Hbound.
            assert (Hk2 : (k' <= f)%nat) by lia.
            exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (aic_iter p q x) e Hterm' j' Hj2).
        simpl. rewrite <- (aic_pow_iter_comm p q x j'). exact IH.
Qed.

(* 首破见证封装（本件新数学）：燃料内可达，则枚举读数 N 携带双证书——
   第 N 步跌破预算（严格）＋每个早步仍保预算。sigT＋prod＋forall nat 全
   Set 形。 *)
Theorem aic_k_enum_first_break : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (aic_pow_iter p q x k)) e))) ->
  sigT (fun N : nat =>
    prod (NatLe (Datatypes.S (aic_pow_iter p q x N)) e)
         (forall j : nat, NatLe (Datatypes.S j) N ->
                          NatLe e (aic_pow_iter p q x j))).
Proof.
  intros fuel p q x e H.
  exists (aic_k_enum fuel p q x e). split.
  - exact (aic_k_enum_correct fuel p q x e H).
  - exact (aic_k_enum_minimal fuel p q x e H).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N ≤ e·q^N（log 单调下的等价面；
   严格首破面 y < e 由 NatLe (S y) e 一跳降为 y ≤ e） *)
Theorem aic_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (aic_pow_iter p q x k)) e))) ->
  NatLe (x * p ^ aic_k_enum fuel p q x e)
        (e * q ^ aic_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (aic_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (aic_pow_iter_exact_ge p q x (aic_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (aic_pow_iter p q x (aic_k_enum fuel p q x e)
              * q ^ aic_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ aic_k_enum fuel p q x e)).
    lia.
Qed.

(* ---------- 严格衰减三件与燃料充足性见证（调用侧 Hterm 闭合） ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据 d·q ≤ a < x·q） *)
Lemma aic_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (aic_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold aic_iter, aic_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  assert (Hcore : (Nat.div (x * p + q - 1) q < x)%nat).
  { destruct (Nat.lt_ge_cases (Nat.div (x * p + q - 1) q) x) as [Hlt | Hge].
    - exact Hlt.
    - exfalso.
      assert (Hmon : (x * q <= Nat.div (x * p + q - 1) q * q)%nat)
        by (apply Nat.mul_le_mono_r; exact Hge).
      pose proof (Nat.div_mod_eq (x * p + q - 1) q) as Hdm.
      pose proof (Nat.mod_upper_bound (x * p + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
      lia. }
  apply (NatLe_lift _ _). lia.
Qed.

(* half 域衰减：2·p ≤ q 且 x ≥ 2 时走步严格递降（x·(q−p) ≥ 2(q−p) ≥ q） *)
Lemma aic_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (aic_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (aic_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma aic_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (aic_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (aic_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H1 : (1 <= q - p)%nat) by lia.
    assert (H2le : (q * 1 <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono; lia).
    rewrite Nat.mul_1_r in H2le.
    rewrite Hsplit. lia.
Qed.

(* 燃料充足性（泛形·严格版）：凡预算位及以上走步严格递降，则 fuel := x
   必产首破步（结论 NatLe (S ·) 严格序界形）。结构归纳，见证 sigT＋
   prod＋NatLe 全 Set 形。 *)
Theorem aic_fuel_sufficient_gen : forall fuel p q x E,
  NatLe x fuel ->
  (forall y : nat, NatLe E y ->
                   NatLe (Datatypes.S (aic_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (aic_pow_iter p q x k)) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    destruct E as [| E'].
    + exfalso.
      pose proof (Hdecay 0%nat (NatLe_lift 0 0 (Nat.le_refl 0))) as Hd.
      pose proof (NatLe_drop (Datatypes.S (aic_iter p q 0)) 0 Hd) as Hd'.
      lia.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S E')). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift 1 (Datatypes.S E')). lia.
  - intros p q x E Hx Hdecay.
    destruct (Nat.ltb x E) eqn:Hlt.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S f)). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift _ _). exact (proj1 (Nat.ltb_lt x E) Hlt).
    + assert (Hge : (E <= x)%nat) by (apply (proj1 (Nat.ltb_ge x E)); exact Hlt).
      pose proof (NatLe_drop x (Datatypes.S f) Hx) as Hx'.
      assert (Hdec : NatLe (Datatypes.S (aic_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift E x). exact Hge. }
      pose proof (NatLe_drop (Datatypes.S (aic_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (aic_iter p q x <= f)%nat) by lia.
      destruct (IH p q (aic_iter p q x) E (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (aic_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 2，fuel := x 即足（严格首破面） *)
Theorem aic_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (aic_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (aic_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (aic_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 2 E HE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q、任意 p<q，fuel := x 即足（严格首破面） *)
Theorem aic_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (aic_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (aic_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (aic_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即首破步数（Hterm 供给面闭合） *)
Theorem aic_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe (Datatypes.S E) A ->
  NatLe (Datatypes.S (aic_pow_iter p q A (aic_k_enum A p q A E))) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (aic_k_enum_correct A p q A E).
  apply (aic_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* 定点档烟测一（数值定装）：kappa=1/2、A=1000、E=5 的减半首破枚举
   （衰减链 1000→500→250→125→63→32→16→8→4，4 < 5 首破于第 8 步） *)
Eval vm_compute in (aic_k_enum 50 1 2 1000 5).

(* 定点档烟测二：kappa=3/4、A=50、E=4 严格档（衰减链至第 10 步达 4，
   4 < 4 不破，第 11 步达 3 首破——与 CD le 档同数据读 10 对照，语义分立
   实拍） *)
Eval vm_compute in (aic_k_enum 50 3 4 50 4).

(* ============================================================ *)
(* Part 1：req 实面逐形对应（UpReqAttnIter §ReqAttnIter 证书子集 22 槽）——   *)
(*   率 omd := req_minus one delta（即 1−δ）。率双证书 exact 直使用宿主      *)
(*   出节件（出节签名经 Check @ 直接钉死：agq_omd_pos 五参无 delta_pos、    *)
(*   agq_omd_lt_one 五参有 delta_pos——discharge 最小化分立）；幂单调支      *)
(*   以 NatLe Set 形重述；诚实 arch 槽计算器；宿主主定理 2 直使用；         *)
(*   主件（均匀 TV 收缩 NatLe 面）＋sigT 模量见证；端到端主定理 3           *)
(*   双投影三件（零重放纯投影）。                                           *)
(* ============================================================ *)

Section AicAttnIterCalc.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和与 abs 诚实接口（宿主证书子集逐形对应，逐位同型） ---- *)
Variable sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Variable sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Variable sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Variable sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Variable sum_nonneg_h :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumf f).
Variable abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).
Variable abs_nonneg_h : forall a : R, le zero (abs a).

(* ---- Boltzmann 侧证书子集 ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable Z_thermo_i_pos : lt zero (Z_thermo_i S sumf D D_pos energy).

(* ---- Markov 侧证书子集 ---- *)
Variable transition : S -> S -> R.
Variable transition_row_i :
  forall s : S, req (sumf (fun s' : S => transition s s')) one.
Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.

Let bdist := boltzmann_dist_i S sumf D D_pos energy Z_thermo_i_pos.
Let omd := req_minus one delta.

Variable minorization :
  forall s s' : S, le (mult delta (bdist s')) (transition s s').
Variable lt_plus_compat_lt_le_i :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt_i :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Variable sum_swap_i : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable abs_ge_zero_i : forall a : R, le zero a -> req (abs a) a.
Variable p_steady_i :
  forall s' : S,
    req (sumf (fun s : S => mult (bdist s) (transition s s'))) (bdist s').
(* 几何击穿诚实接口槽（宿主 arch_pow_i 逐位对应；幂底换 req_r_pow omd） *)
Variable arch_pow_i :
  forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => lt (mult a (req_r_pow (req_minus one delta) N)) eps).

(* ===== 率抽取双证书（exact 直使用宿主出节件；出节实参经直接钉死：      *)
(*   agq_omd_pos 五参（无 delta_pos）、agq_omd_lt_one 五参（有 delta_pos） *)
(*   ——同一节两主证书出节参数面分立，使用前逐件 Check @ 钉序。 ========== *)

Lemma aic_rate_pos : lt zero omd.
Proof.
  exact (agq_omd_pos delta delta_lt_one lt_plus_compat_lt_le_i).
Qed.

Lemma aic_rate_lt_one : lt omd one.
Proof.
  exact (agq_omd_lt_one delta delta_pos lt_plus_compat_le_lt_i).
Qed.

(* ===== 幂单调支的 Set 形重述（宿主 agq_r_pow_dec_iter 的 Prop 序界面   *)
(*   (m <= n)%nat 在本件语句面以 NatLe 重述；Prop 界只经 NatLe_drop 进证明 *)
(*   体，零 Prop 消入 Set。） ============================================ *)

Lemma aic_r_pow_dec_iter_set : forall m n : nat,
  NatLe m n -> le (req_r_pow omd n) (req_r_pow omd m).
Proof.
  intros m n Hmn.
  exact (agq_r_pow_dec_iter delta delta_pos delta_lt_one
           lt_plus_compat_lt_le_i m n (NatLe_drop m n Hmn)).
Qed.

(* ===== 诚实 arch 槽计算器（精度到步数的见证读数） ====================== *)

Definition aic_arch_k (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (arch_pow_i a Ha eps Heps).

Theorem aic_arch_k_budget : forall (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps),
  lt (mult a (req_r_pow omd (aic_arch_k a Ha eps Heps))) eps.
Proof.
  intros a Ha eps Heps. exact (projT2 (arch_pow_i a Ha eps Heps)).
Qed.

(* ===== 宿主主定理 2 直使用（收缩脊柱读出面：率 req_r_pow omd n 显式在   *)
(*   语句面） =========================================================== *)

Theorem aic_tv_iter_proj : forall (n : nat) (mu : S -> R),
  req (sumf mu) one ->
  le (tv_i S sumf (attention_iter_i S sumf transition n mu) bdist)
     (mult (req_r_pow omd n) (tv_i S sumf mu bdist)).
Proof.
  intros n mu Hmu.
  exact (agq_tv_iter S sumf sum_ext sum_linear sum_add sum_le abs_sum_le_h
           D D_pos energy Z_thermo_i_pos transition transition_row_i
           delta delta_lt_one minorization lt_plus_compat_lt_le_i sum_swap_i
           abs_ge_zero_i p_steady_i n mu Hmu).
Qed.

(* ===== K7 主件：精度到步数计算器＋均匀收缩正确性 ======================= *)
(*   aic_step_calc：TV0 := tv(mu0,p) > 0 的 arch 槽读数（projT1）；       *)
(*   aic_step_calc_correct：对全部 n ≥ N（NatLe 序界），迭代 TV 严格低于   *)
(*   预算 eps——agq_iterate_converges 同链 NatLe 重述（agq_tv_iter 支＋   *)
(*   NatLe 幂单调支＋arch 预算支，le_lt_trans 双段换轨）。 ================ *)

Definition aic_step_calc (mu0 : S -> R) (Hmu : req (sumf mu0) one)
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv_i S sumf mu0 bdist))
  : nat :=
  projT1 (arch_pow_i (tv_i S sumf mu0 bdist) Htv0 eps Heps).

Theorem aic_step_calc_correct : forall (mu0 : S -> R)
  (Hmu : req (sumf mu0) one) (eps : R) (Heps : lt zero eps)
  (Htv0 : lt zero (tv_i S sumf mu0 bdist)) (n : nat),
  NatLe (aic_step_calc mu0 Hmu eps Heps Htv0) n ->
  lt (tv_i S sumf (attention_iter_i S sumf transition n mu0) bdist) eps.
Proof.
  intros mu0 Hmu eps Heps Htv0. unfold aic_step_calc.
  destruct (arch_pow_i (tv_i S sumf mu0 bdist) Htv0 eps Heps) as [N HN].
  intros n Hn.
  apply (le_lt_trans _ (mult (req_r_pow omd n) (tv_i S sumf mu0 bdist)) _).
  - exact (aic_tv_iter_proj n mu0 Hmu).
  - apply (le_lt_trans _ (mult (req_r_pow omd N) (tv_i S sumf mu0 bdist)) _).
    + apply (le_mult_compat_weak (req_r_pow omd n) (req_r_pow omd N)
               (tv_i S sumf mu0 bdist)).
      * exact (agq_tv_nonneg S sumf sum_nonneg_h abs_nonneg_h mu0 bdist).
      * exact (aic_r_pow_dec_iter_set N n Hn).
    + exact (lt_id_l _ _ _
               (mult_comm (req_r_pow omd N) (tv_i S sumf mu0 bdist)) HN).
Qed.

(* sigT 封装（均匀 TV 收缩模量见证型；宿主主定理 3 结论面的 NatLe 形） *)
Theorem aic_mixing_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : req (sumf mu0) one) (eps : R) (Heps : lt zero eps)
  (Htv0 : lt zero (tv_i S sumf mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv_i S sumf (attention_iter_i S sumf transition n mu0) bdist) eps).
Proof.
  intros mu0 Hmu eps Heps Htv0.
  exists (aic_step_calc mu0 Hmu eps Heps Htv0).
  intros n Hn. exact (aic_step_calc_correct mu0 Hmu eps Heps Htv0 n Hn).
Defined.

(* ===== 端到端主定理 3 双投影（零重放纯投影：步数读数 projT1、均匀收缩   *)
(*   正确性 projT2 经 NatLe_drop 桥、sigT 封装） ======================== *)

Definition aic_conv_step_calc (mu0 : S -> R) (Hmu : req (sumf mu0) one)
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv_i S sumf mu0 bdist))
  : nat :=
  projT1 (agq_iterate_converges S sumf sum_ext sum_linear sum_add sum_le
            sum_nonneg_h abs_sum_le_h abs_nonneg_h
            D D_pos energy Z_thermo_i_pos transition transition_row_i
            delta delta_pos delta_lt_one minorization lt_plus_compat_lt_le_i
            sum_swap_i abs_ge_zero_i p_steady_i arch_pow_i
            mu0 Hmu eps Heps Htv0).

Theorem aic_conv_step_correct : forall (mu0 : S -> R)
  (Hmu : req (sumf mu0) one) (eps : R) (Heps : lt zero eps)
  (Htv0 : lt zero (tv_i S sumf mu0 bdist)) (n : nat),
  NatLe (aic_conv_step_calc mu0 Hmu eps Heps Htv0) n ->
  lt (tv_i S sumf (attention_iter_i S sumf transition n mu0) bdist) eps.
Proof.
  intros mu0 Hmu eps Heps Htv0. unfold aic_conv_step_calc.
  destruct (agq_iterate_converges S sumf sum_ext sum_linear sum_add sum_le
              sum_nonneg_h abs_sum_le_h abs_nonneg_h
              D D_pos energy Z_thermo_i_pos transition transition_row_i
              delta delta_pos delta_lt_one minorization lt_plus_compat_lt_le_i
              sum_swap_i abs_ge_zero_i p_steady_i arch_pow_i
              mu0 Hmu eps Heps Htv0) as [N HN].
  intros n Hn.
  exact (HN n (NatLe_drop _ _ Hn)).
Qed.

(* sigT 封装（端到端均匀收缩模量见证型） *)
Theorem aic_conv_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : req (sumf mu0) one) (eps : R) (Heps : lt zero eps)
  (Htv0 : lt zero (tv_i S sumf mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv_i S sumf (attention_iter_i S sumf transition n mu0) bdist) eps).
Proof.
  intros mu0 Hmu eps Heps Htv0.
  exists (aic_conv_step_calc mu0 Hmu eps Heps Htv0).
  intros n Hn. exact (aic_conv_step_correct mu0 Hmu eps Heps Htv0 n Hn).
Defined.

End AicAttnIterCalc.

(* ============================================================ *)
(* 审计口：公理面（全 Closed 预期）＋可提取强证（照系列模板模式）        *)
(* ============================================================ *)

Print Assumptions aic_k_enum_correct.
Print Assumptions aic_k_enum_minimal.
Print Assumptions aic_k_enum_first_break.
Print Assumptions aic_k_enum_logface.
Print Assumptions aic_fuel_sufficient_half.
Print Assumptions aic_fuel_sufficient_qbound.
Print Assumptions aic_k_enum_auto_half.
Print Assumptions aic_rate_pos.
Print Assumptions aic_rate_lt_one.
Print Assumptions aic_arch_k_budget.
Print Assumptions aic_tv_iter_proj.
Print Assumptions aic_step_calc_correct.
Print Assumptions aic_mixing_modulus_sigT.
Print Assumptions aic_conv_step_correct.
Print Assumptions aic_conv_modulus_sigT.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction aic_ceil_div aic_iter aic_pow_iter aic_k_enum.
