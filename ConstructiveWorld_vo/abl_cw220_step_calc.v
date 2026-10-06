(* ==========================================================================)
   abl_cw220_step_calc.v — 收敛计算器系列第八件（CW220_Extensions 收缩收敛面，
   cw2_ 前缀）
   使命: 按定量完备性矿脉表 K 表——CW220_Extensions.v 的收缩收敛面（史前层
     件 1663 行，勘其依赖 S01-S15 直连；BudgetReal＋UpArchAttn 两区:
     率 kappa := real_plus real_one (real_opp delta) 即 1−delta 语句面显式在
     案，率双证书 one_minus_delta_pos_real/one_minus_delta_lt_one_real、闭合
     arch 主件 r_arch_pow_attn_real（经 bernoulli_pow＋real_arch 全证闭合，
     非接口假设）、几何衰减链 tv_iter_decay_real、端到端主定理 attention_
     iterate_converges_real、论文 4 定理 4.10 尾界 budget_min_tail）缺「精度
     到步数」Defined 计算器。本件补齐三段:
     率抽取（显式直用——cw2_rate_pos/cw2_rate_lt_one exact 直接使用宿主双证书，
       零新增抽取步，同 cfc_rate_pos 先例）；
     nat 定点档（真 Fixpoint，CL 第六件范本滚转: cw2_ceil_div/cw2_iter/
       cw2_pow_iter/cw2_k_enum 有界燃料上取整衰减枚举＋正确性两半＋首破
       最小性见证两件＋严格衰减三件＋燃料充足性三件＋auto_half）；
     实面 Real 载体平行形（本件 K 面增量）: 闭合 arch 槽步数读数 cw2_arch_k/
       cw2_step_calc——系列首见 arch 槽由宿主全证闭合、无诚实接口槽（CL 面
       arch_pow_i 为 Variable 槽，本面 r_arch_pow_attn_real 为已证定理）；
       宿主主定理 Prop 序界 (N <= n) 面在本件语句面以 NatLe Set 载体重述
       （cw2_step_calc_correct/cw2_conv_step_correct/cw2_min_tail_correct，
       Prop 界只经 NatLe_drop 进证明体）；sigT 模量见证三件（cw2_mixing_
       modulus_sigT/cw2_conv_modulus_sigT/cw2_min_tail_modulus_sigT）。
   覆盖核验与定位记录: ①率显式性——kappa := 1−delta 在 r_arch_pow_attn_real/
       tv_iter_decay_real/attention_iterate_converges_real 三件语句面直书，
       双证书根级在案，按任务令「显式直用」，零隐式抽取；②覆盖复核——CD
       件（cfc_，UpReqConcFin2 面）标注 CW220_Extensions「备选位无需启用」、
       CL 件（aic_，UpReqAttnIter 面）标注「留后续增量」、CF 件（tvc_）宿主
       非本面，全池 grep 零 cw2_/abl_cw220 使用件——真缺口，本件就地闭合，
       无转位（备选位 p2a_AttnClimClose/Arch_PA_04/S06 无需启用）。
   件名与前缀: abl_cw220_step_calc.v，cw2_ 前缀（施工前全库 grep 防撞:
     编译树 vo_local_world_unified_0930 与 abl_tmine04_pool 全池零命中）。
   本件陈述（两段，33 个 cw2_ 常数）:
     Part 2 nat 定点档（真 Fixpoint，语句面全 Set 载体）: cw2_ceil_div/
       cw2_ceil_div_le/cw2_iter/cw2_iter_step_bound/cw2_pow_iter/cw2_pow_
       iter_comm/cw2_pow_iter_exact_ge/cw2_k_enum（Nat.ltb 首破停机——严格
       档）＋正确性两半（cw2_k_enum_correct 严格面 NatLe (S ·) 形/cw2_k_
       enum_logface 精确面 x·p^N ≤ e·q^N）＋首破最小性见证两件（cw2_k_enum_
       minimal 每早步 j 仍 ≥ e/cw2_k_enum_first_break sigT＋prod 封装）＋
       严格衰减三件（cw2_iter_lt_decay/lt_half/lt_q）＋燃料充足性三件
       （cw2_fuel_sufficient_gen/half/qbound）＋cw2_k_enum_auto_half。
     Part 1 实面 Real 载体平行形（CW220 收缩收敛面直接使用，全显式参数化——
       宿主为闭式定理，免 CL 面 22 槽 Section 复制）: 率抽取双证书（cw2_
       rate_pos/cw2_rate_lt_one）＋幂反单调 NatLe 载体重述件（cw2_r_pow_
       anti_mono_set）＋闭合 arch 步数读数两件（cw2_arch_k/cw2_arch_k_
       budget）＋宿主衰减链直接使用件（cw2_tv_decay）＋K 面主件两件（cw2_
       step_calc/cw2_step_calc_correct，均匀于全部 n ≥ N 的几何衰减，NatLe
       序界面）＋sigT 模量见证（cw2_mixing_modulus_sigT）＋端到端主定理双
       投影三件（cw2_conv_step_calc/cw2_conv_step_correct/cw2_conv_modulus_
       sigT，零重放纯投影）＋论文 4.10 尾界三件（cw2_min_tail_k/cw2_min_
       tail_correct/cw2_min_tail_modulus_sigT）。
   Set 载体纪律（语句面零 Prop）: 存在以 sigT、合取以 prod、nat 序界以
     NatLe（S01 的 leb 判定型 Set 载体，NatLe_drop/NatLe_lift 双向桥）；严
     格序界以 NatLe (S ·) 表达；实面比较以 S02 柯西实数面 real_lt/real_le/
     real_eq（全 Set 型语句）；步数见证以 sigT nat。宿主 attention_iterate_
     converges_real/budget_min_tail 的 (N <= n)%nat/(N <= Nat.min p q)%nat
     Prop 序界在本件语句面一律 NatLe 重述，Prop 界只经 NatLe_drop 进证明
     体；假设位零 Hypothesis/零 Prop 型；零 not/~/<> 书写面。
   fail-loud 记录: Real 面步数读数（cw2_arch_k/cw2_step_calc/cw2_conv_step_
     calc/cw2_min_tail_k）取 projT1 于宿主 Qed 闭合定理，读数不规约（同系
     列 arch 槽口径；本面 arch 由宿主全证闭合，无接口槽——较 CL 面少一诚
     实槽）；可执行面由 Part 2 nat 定点档承载（真 Fixpoint，Obj.magic=0 附
     加证）；tv_seq 为宿主主定理同款抽象 Real 序列（每步收缩 Hstep 显式前
     提——宿主覆盖面注记原文: 注意力语义对象完整实例化需天级工程，本件继
     承宿主边界不扩scope）；燃料充足性限衰减域（half 域 2·p ≤ q、E ≥ 2；
     qbound 域 q ≤ E、任意 p<q——严格版预算位）；严格档与 le 档语义分立:
     首破「x < e」与首达「x ≤ e」读数可差一步（烟测实拍: 同数据严格
     档 11、le 档 10，各自正确于本档语义）。
   依赖: S01_BaseRing（NatLe/NatLe_drop/NatLe_lift）；S02_CauchyComplete
     （Real/real_lt/real_le/real_eq/real_mult/real_eq_lt_lt/real_le_lt_
     trans/real_mult_comm）；S07_RealSetoidExpLog（real_le_mult_compat）；
     S14_B5BatchBlock（real_lt_le_bridge）；CW220_Extensions（one_minus_
     delta_pos_real/one_minus_delta_lt_one_real/r_arch_pow_attn_real/tv_
     iter_decay_real/attention_iterate_converges_real＋Import BudgetReal:
     real_pow/real_pow_anti_mono/budget_min_tail）；PeanoNat/Lia/Arith。
     全部 Require-only 零改动，Live/注册面/缓存根零触碰（史前层件依赖 AA
     在册 S01-S15 直连，CW220_Extensions.vo 在树实测 Require 绿）。
   对标: mathlib 马尔可夫链混合时间界（几何收缩显式迭代预算）的构造性 Set
     层柯西实数面对应物；同系列 dsc_/asc_/cmc_/mtc2_/atn_/cfc_/aic_ 的 K 表
     CW220 面补全。
   构造性: 纯构造性/Set 层零 Prop 载体（步数见证 nat 面 sigT；序谓词均 Set
     层值；nat 面算术不消入实面目标）；非平凡（cw2_k_enum 为真 Fixpoint 首
     破枚举）；可提取（Separate Extraction Obj.magic=0 附加证）；零公理（尾
     Print Assumptions 全 Closed 预期）。
   工艺红线: term-mode 全显式实参；数值定装（Eval vm_compute 烟测入日志）；
     注释内禁右括号星杠字面。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q
     vo_local_world_unified_0930 "" abl_cw220_step_calc.v（池内执行）。
   ========================================================================== *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S14_B5BatchBlock.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：收缩率定点枚举解算器（真 Fixpoint/严格档/Set 载体）——          *)
(*   CL 第六件范本滚转（aic_ 系 rename cw2_ 系），宿主无关。收缩率         *)
(*   kappa=p/q（0<p<q）、初值 A、预算 E 的定点表示，首破枚举 N 使           *)
(*   powIter N A < E（严格）。序界全走 NatLe Set 载体，严格序界以          *)
(*   NatLe (S ·) 表达。本段含首破最小性见证两件与燃料充足性三件。          *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition cw2_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma cw2_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (cw2_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold cw2_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition cw2_iter (p q x : nat) : nat := cw2_ceil_div (x * p) q.

Lemma cw2_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (cw2_iter p q x * q).
Proof.
  intros p q x Hq. unfold cw2_iter. apply (cw2_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：cw2_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint cw2_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => cw2_iter p q (cw2_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma cw2_pow_iter_comm : forall p q x k,
  cw2_pow_iter p q (cw2_iter p q x) k = cw2_iter p q (cw2_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x < e 首破即停（返回已走步数），
   否则走衰减步再搜（Nat.ltb 判定，严格档停机面） *)
Fixpoint cw2_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (cw2_k_enum f p q (cw2_iter p q x) e)
  end.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma cw2_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (cw2_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (cw2_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (cw2_iter_step_bound p q (cw2_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (cw2_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (cw2_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (cw2_iter p q (cw2_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (cw2_iter p q (cw2_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* 正确性（首破严格面）：燃料内可达，枚举返回的 N 步处上取整值 < e
   （NatLe (S ·) e 严格序界载体）。可达见证为 sigT＋prod＋NatLe 全 Set 载体。 *)
Theorem cw2_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  NatLe (Datatypes.S (cw2_pow_iter p q x (cw2_k_enum fuel p q x e))) e.
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
      * pose proof (NatLe_drop (Datatypes.S (cw2_pow_iter p q x 0)) e Hbound)
          as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (cw2_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (cw2_pow_iter p q (cw2_iter p q x) k0)) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (cw2_iter p q x) e Hterm').
        simpl.
        rewrite <- (cw2_pow_iter_comm p q x
                      (cw2_k_enum f p q (cw2_iter p q x) e)).
        exact IH.
Qed.

(* 首破最小性见证（承首破新数学）：燃料内可达，则对每个早于返回
   步数 N 的步 j（S j ≤ N），第 j 步上取整值仍 ≥ e——枚举读数是首个跌破
   预算的步。 *)
Theorem cw2_k_enum_minimal : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  forall j : nat, NatLe (Datatypes.S j) (cw2_k_enum fuel p q x e) ->
  NatLe e (cw2_pow_iter p q x j).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm j Hj.
  - exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl in Hj. rewrite Hlt in Hj.
      exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
    + simpl in Hj. rewrite Hlt in Hj.
      assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      pose proof (NatLe_drop (Datatypes.S j)
                    (Datatypes.S (cw2_k_enum f p q (cw2_iter p q x) e)) Hj)
        as Hj'.
      destruct j as [| j'].
      * simpl. apply (NatLe_lift e x). exact Hge.
      * simpl in Hj'.
        assert (Hj2 : NatLe (Datatypes.S j')
                        (cw2_k_enum f p q (cw2_iter p q x) e))
          by (apply (NatLe_lift _ _); lia).
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (cw2_pow_iter p q (cw2_iter p q x) k0)) e))).
        { destruct Hterm as [k [Hk Hbound]].
          pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
          destruct k as [| k'].
          - pose proof (NatLe_drop (Datatypes.S (cw2_pow_iter p q x 0)) e Hbound)
              as Hb'.
            simpl in Hb'. lia.
          - simpl in Hbound.
            rewrite <- (cw2_pow_iter_comm p q x k') in Hbound.
            assert (Hk2 : (k' <= f)%nat) by lia.
            exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (cw2_iter p q x) e Hterm' j' Hj2).
        simpl. rewrite <- (cw2_pow_iter_comm p q x j'). exact IH.
Qed.

(* 首破见证封装：燃料内可达，则枚举读数 N 携带双证书——第 N 步跌破预算
   （严格）＋每个早步仍保预算。sigT＋prod＋forall nat 全 Set 载体。 *)
Theorem cw2_k_enum_first_break : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  sigT (fun N : nat =>
    prod (NatLe (Datatypes.S (cw2_pow_iter p q x N)) e)
         (forall j : nat, NatLe (Datatypes.S j) N ->
                          NatLe e (cw2_pow_iter p q x j))).
Proof.
  intros fuel p q x e H.
  exists (cw2_k_enum fuel p q x e). split.
  - exact (cw2_k_enum_correct fuel p q x e H).
  - exact (cw2_k_enum_minimal fuel p q x e H).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N ≤ e·q^N（log 单调下的等价面；
   严格首破面 y < e 由 NatLe (S y) e 一跳降为 y ≤ e） *)
Theorem cw2_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  NatLe (x * p ^ cw2_k_enum fuel p q x e)
        (e * q ^ cw2_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (cw2_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (cw2_pow_iter_exact_ge p q x (cw2_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (cw2_pow_iter p q x (cw2_k_enum fuel p q x e)
              * q ^ cw2_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ cw2_k_enum fuel p q x e)).
    lia.
Qed.

(* ---------- 严格衰减三件与燃料充足性见证（调用侧 Hterm 闭合） ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据 d·q ≤ a < x·q） *)
Lemma cw2_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold cw2_iter, cw2_ceil_div.
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
Lemma cw2_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (cw2_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma cw2_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (cw2_iter_lt_decay p q x).
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
   必产首破步（结论 NatLe (S ·) 严格序界载体）。结构归纳，见证 sigT＋
   prod＋NatLe 全 Set 载体。 *)
Theorem cw2_fuel_sufficient_gen : forall fuel p q x E,
  NatLe x fuel ->
  (forall y : nat, NatLe E y ->
                   NatLe (Datatypes.S (cw2_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    destruct E as [| E'].
    + exfalso.
      pose proof (Hdecay 0%nat (NatLe_lift 0 0 (Nat.le_refl 0))) as Hd.
      pose proof (NatLe_drop (Datatypes.S (cw2_iter p q 0)) 0 Hd) as Hd'.
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
      assert (Hdec : NatLe (Datatypes.S (cw2_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift E x). exact Hge. }
      pose proof (NatLe_drop (Datatypes.S (cw2_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (cw2_iter p q x <= f)%nat) by lia.
      destruct (IH p q (cw2_iter p q x) E (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (cw2_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 2，fuel := x 即足（严格首破面） *)
Theorem cw2_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (cw2_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (cw2_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 2 E HE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q、任意 p<q，fuel := x 即足（严格首破面） *)
Theorem cw2_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (cw2_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (cw2_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即首破步数（Hterm 供给面闭合） *)
Theorem cw2_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe (Datatypes.S E) A ->
  NatLe (Datatypes.S (cw2_pow_iter p q A (cw2_k_enum A p q A E))) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (cw2_k_enum_correct A p q A E).
  apply (cw2_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* 定点档烟测一（数值定装）：kappa=1/2、A=1000、E=5 的减半首破枚举
   （衰减链 1000→500→250→125→63→32→16→8→4，4 < 5 首破于第 8 步） *)
Eval vm_compute in (cw2_k_enum 50 1 2 1000 5).

(* 定点档烟测二：kappa=3/4、A=50、E=4 严格档（衰减链至第 10 步达 4，
   4 < 4 不破，第 11 步达 3 首破——le 档同数据读 10 对照，语义分立实拍） *)
Eval vm_compute in (cw2_k_enum 50 3 4 50 4).

(* ============================================================ *)
(* Part 1：实面 Real 载体平行形（CW220_Extensions 收缩收敛面直接使用）——      *)
(*   率 kappa := cw2_kappa delta := real_plus real_one (real_opp delta)    *)
(*   即 1−delta，语句面显式直书。率双证书 exact 直接使用宿主根级出节件；      *)
(*   幂反单调腿以 NatLe Set 载体重述；闭合 arch 槽步数读数（宿主全证闭     *)
(*   合，无诚实接口槽）；宿主衰减链直接使用；K 面主件（均匀几何衰减 NatLe    *)
(*   面）＋sigT 模量见证；端到端主定理双投影三件（零重放纯投影）；论文     *)
(*   4.10 尾界三件。全显式参数化——宿主为闭式定理，免 Section 证书参数位复制。 *)
(* ============================================================ *)

(* 率的载体定义（1−delta；宿主语句面同形直书） *)
Definition cw2_kappa (delta : Real) : Real :=
  real_plus real_one (real_opp delta).

(* ===== 率抽取双证书（显式直用，exact 直接使用宿主根级证书——零新增抽取步） *)

Lemma cw2_rate_pos : forall delta : Real,
  real_lt delta real_one -> real_lt real_zero (cw2_kappa delta).
Proof.
  intros delta Hd. exact (one_minus_delta_pos_real delta Hd).
Qed.

Lemma cw2_rate_lt_one : forall delta : Real,
  real_lt real_zero delta -> real_lt (cw2_kappa delta) real_one.
Proof.
  intros delta Hd. exact (one_minus_delta_lt_one_real delta Hd).
Qed.

(* ===== 幂反单调腿的 Set 载体重述（宿主 BudgetReal.real_pow_anti_mono 的   *)
(*   Prop 序界 (p <= q)%nat 面在本件语句面以 NatLe 重述；Prop 界只经        *)
(*   NatLe_drop 进证明体，零 Prop 消入 Set。） ============================ *)

Lemma cw2_r_pow_anti_mono_set : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (m n : nat),
  NatLe m n ->
  real_le (real_pow (cw2_kappa delta) n) (real_pow (cw2_kappa delta) m).
Proof.
  intros delta Hd1 Hd2 m n Hmn.
  exact (real_pow_anti_mono (cw2_kappa delta)
           (cw2_rate_pos delta Hd2)
           (real_lt_le_bridge (cw2_kappa delta) real_one
              (cw2_rate_lt_one delta Hd1))
           m n (NatLe_drop m n Hmn)).
Qed.

(* ===== 闭合 arch 槽步数读数（系列首见: 宿主 r_arch_pow_attn_real 为已证   *)
(*   定理——bernoulli_pow＋real_arch 闭合——本面无诚实接口槽） ============== *)

Definition cw2_arch_k (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (a : Real) (Ha : real_lt real_zero a)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (r_arch_pow_attn_real delta Hd1 Hd2 a Ha eps Heps).

Theorem cw2_arch_k_budget : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps),
  real_lt (real_mult a
             (real_pow (cw2_kappa delta) (cw2_arch_k delta Hd1 Hd2 a Ha eps Heps)))
          eps.
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (projT2 (r_arch_pow_attn_real delta Hd1 Hd2 a Ha eps Heps)).
Qed.

(* ===== 宿主衰减链直接使用（每步收缩前提 Hstep 显式，同宿主 tv_iter_decay_  *)
(*   real 签名；结论面 kappa 以 cw2_kappa delta 承载） ==================== *)

Lemma cw2_tv_decay : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (cw2_kappa delta) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
Qed.

(* ===== K 面主件：精度到步数计算器＋均匀几何衰减正确性 ================== *)
(*   cw2_step_calc: 预算 eps 下以 tv₀ 为幅位的闭合 arch 读数（projT1）；   *)
(*   cw2_step_calc_correct: 对全部 n ≥ N（NatLe 序界），tv_seq n < eps——   *)
(*   衰减链腿＋NatLe 幂反单调腿＋arch 预算腿，real_le_lt_trans 双段换轨，  *)
(*   链幂以 real_mult_comm 对齐宿主 arch 结论的乘序。 ==================== *)

Definition cw2_step_calc (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) : nat :=
  projT1 (r_arch_pow_attn_real delta Hd1 Hd2 (tv_seq Datatypes.O) Htv0
            eps Heps).

Theorem cw2_step_calc_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) (n : nat),
  NatLe (cw2_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0) n ->
  real_lt (tv_seq n) eps.
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  unfold cw2_step_calc.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2 (tv_seq Datatypes.O) Htv0
              eps Heps) as [N HN].
  intros n Hn.
  apply (real_le_lt_trans (tv_seq n)
           (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O))
           eps).
  - exact (cw2_tv_decay delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans
             (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O))
             (real_mult (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O))
             eps).
    + exact (real_le_mult_compat (real_pow (cw2_kappa delta) n)
               (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O)
               Htv0 (cw2_r_pow_anti_mono_set delta Hd1 Hd2 N n Hn)).
    + exact (real_eq_lt_lt
               (real_mult (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow (cw2_kappa delta) N))
               eps
               (real_mult_comm (real_pow (cw2_kappa delta) N)
                  (tv_seq Datatypes.O))
               HN).
Qed.

(* sigT 封装（均匀几何衰减模量见证型；宿主主定理结论面的 NatLe 载体形） *)
Theorem cw2_mixing_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n -> real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  exists (cw2_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0).
  intros n Hn.
  exact (cw2_step_calc_correct delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0 n Hn).
Defined.

(* ===== 端到端主定理双投影（零重放纯投影: 步数读数 projT1、均匀收缩正确  *)
(*   性 projT2 经 NatLe_drop 桥、sigT 封装——宿主 attention_iterate_       *)
(*   converges_real 的 (N <= n)%nat Prop 序界只经 NatLe_drop 进证明体） == *)

Definition cw2_conv_step_calc (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) : nat :=
  projT1 (attention_iterate_converges_real delta Hd1 Hd2 tv_seq Hstep
            eps Heps Htv0).

Theorem cw2_conv_step_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) (n : nat),
  NatLe (cw2_conv_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0) n ->
  real_lt (tv_seq n) eps.
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  unfold cw2_conv_step_calc.
  destruct (attention_iterate_converges_real delta Hd1 Hd2 tv_seq Hstep
              eps Heps Htv0) as [N HN].
  intros n Hn.
  exact (HN n (NatLe_drop _ _ Hn)).
Qed.

(* sigT 封装（端到端均匀几何衰减模量见证型） *)
Theorem cw2_conv_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n -> real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  exists (cw2_conv_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0).
  intros n Hn.
  exact (cw2_conv_step_correct delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0 n Hn).
Defined.

(* ===== 论文 4 定理 4.10 尾界（宿主 BudgetReal.budget_min_tail 直接使用:    *)
(*   预算 N 对全部 min p q ≥ N 的双尾同时有效——NatLe (N <= Nat.min p q)   *)
(*   面重述） ============================================================ *)

Definition cw2_min_tail_k (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (a : Real) (Ha : real_lt real_zero a)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (budget_min_tail (cw2_kappa delta) a eps (cw2_rate_pos delta Hd2)
            (cw2_rate_lt_one delta Hd1) Ha Heps).

Theorem cw2_min_tail_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps) (p q : nat),
  NatLe (cw2_min_tail_k delta Hd1 Hd2 a Ha eps Heps) (Nat.min p q) ->
  real_lt (real_mult a
             (real_pow (cw2_kappa delta) (Nat.min p q))) eps.
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps p q Hpq.
  exact (projT2 (budget_min_tail (cw2_kappa delta) a eps
                   (cw2_rate_pos delta Hd2) (cw2_rate_lt_one delta Hd1)
                   Ha Heps)
           p q (NatLe_drop _ _ Hpq)).
Qed.

(* sigT 封装（4.10 尾界模量见证型） *)
Theorem cw2_min_tail_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps),
  sigT (fun N : nat =>
    forall p q : nat, NatLe N (Nat.min p q) ->
      real_lt (real_mult a
                 (real_pow (cw2_kappa delta) (Nat.min p q))) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exists (cw2_min_tail_k delta Hd1 Hd2 a Ha eps Heps).
  intros p q Hpq.
  exact (cw2_min_tail_correct delta Hd1 Hd2 a Ha eps Heps p q Hpq).
Defined.

(* ============================================================ *)
(* 审计口：公理面（全 Closed 预期）＋可提取强证（照系列模板模式）          *)
(* ============================================================ *)

Print Assumptions cw2_k_enum_correct.
Print Assumptions cw2_k_enum_minimal.
Print Assumptions cw2_k_enum_first_break.
Print Assumptions cw2_k_enum_logface.
Print Assumptions cw2_fuel_sufficient_half.
Print Assumptions cw2_fuel_sufficient_qbound.
Print Assumptions cw2_k_enum_auto_half.
Print Assumptions cw2_rate_pos.
Print Assumptions cw2_rate_lt_one.
Print Assumptions cw2_r_pow_anti_mono_set.
Print Assumptions cw2_arch_k_budget.
Print Assumptions cw2_tv_decay.
Print Assumptions cw2_step_calc_correct.
Print Assumptions cw2_mixing_modulus_sigT.
Print Assumptions cw2_conv_step_correct.
Print Assumptions cw2_conv_modulus_sigT.
Print Assumptions cw2_min_tail_correct.
Print Assumptions cw2_min_tail_modulus_sigT.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction cw2_ceil_div cw2_iter cw2_pow_iter cw2_k_enum.
