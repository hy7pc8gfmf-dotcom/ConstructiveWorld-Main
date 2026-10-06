(* ==========================================================================)
   abl_s06_step_calc.v — 收敛计算器系列第十一件（S06_DiffSamplingGibbs 收缩
   收敛面，sdc_ 前缀，K3 位补全）
   使命: 按定量完备性矿脉表 K3——S06_DiffSamplingGibbs.v 可微层基座柱的
     AttentionGibbsBridge 收缩收敛面（率证书 one_minus_delta_pos/
     one_minus_delta_lt_one 在案、单步主定理 attention_tv_contraction 语句面
     直书率 1−δ、几何迭代件 attention_tv_iter_contraction 语句面显式率
     r_pow (minus one delta) n、端到端主定理 attention_iterate_converges 的
     sigT N 走 r_arch_pow_attn 阿基米德坑）缺「精度到步数」Defined 计算器。
     本件补齐三段:
     率抽取（omd := minus one delta，即 1−δ）直接使用宿主出节双证书；
     nat 定点档首破严格档（CL 范本直滚）并含首破最小性见证两件与燃料充足
     性三件；Id 层实面对应形 Section（宿主证书子集同形对应 16 槽，attention_tv_
     contraction／attention_tv_iter_contraction／attention_iterate_converges
     出节件直接使用，宿主 Prop 序界 (N ≤ n) 面以 NatLe Set 载体重述）。
     率形态判定: 本面收缩率为几何形（1−δ 的幂）语句面直书——S06 系可微层，
     其 Lipschitz 材料（inner_lipschitz/op_lipschitz）服务可微性预算面而非收
     敛面，「Lipschitz⟹几何率」抽率桥本面不触发，抽率步为零。
   件名与前缀: abl_s06_step_calc.v，sdc_ 前缀（施工前全库 grep 防撞: 编译树
     vo_local_world_unified_0930 与 abl_tmine04_pool 全池零命中）。
   覆盖核验: 六代滚件（dsc_/asc_/cmc_/mtc2_/aic_/cw2_）grep
     attention_tv_iter_contraction／attention_iterate_converges／r_arch_pow_
     attn 本面定理名全数零使用（asc_ 件使用 S06.tv_dist 限定名并自建 omd_
     arch 对应参数位＝证书模式同款而非本面定理使用；cw2_/ap4_/p2c_ 命中均为
     r_arch_pow_attn_real 异件注释级引用）——K3 真缺口，本件就地闭合，无转位。
   本件陈述（三段，33 个 sdc_ 常数）:
     Part 2 nat 定点档（真 Fixpoint，语句面全 Set 载体，宿主无关）: sdc_ceil_
       div/sdc_iter/sdc_pow_iter/sdc_k_enum（有界燃料上取整衰减枚举，Nat.ltb
       首破停机——严格档）＋正确性两半（sdc_k_enum_correct 严格面 NatLe
       (S ·) 形 / sdc_k_enum_logface 精确面 x·p^N ≤ e·q^N）＋首破最小性
       见证两件（sdc_k_enum_minimal 每早步 j 仍 ≥ e / sdc_k_enum_first_
       break  sigT＋prod 封装）＋严格衰减三件（sdc_iter_lt_decay/lt_half/
       lt_q）＋燃料充足性三件（sdc_fuel_sufficient_gen/half/qbound，严格版
       结论）＋sdc_k_enum_auto_half。
     Part 1 Id 层实面对应形（Section SdcGibbsCalc，宿主证书子集 16 槽）:
       率抽取双证书（sdc_rate_pos/sdc_rate_lt_one，exact 直接使用宿主出节件，
       出节实参经检验确定: one_minus_delta_pos 四参无 delta_pos、
       one_minus_delta_lt_one 四参无 delta_lt_one——discharge 最小化分立）＋
       幂单调 Set 载体重述件（sdc_r_pow_dec_iter_set，宿主 r_pow_dec_iter_
       attn 的 Prop 序界 (m ≤ n) 面 NatLe 化）＋单步 Doeblin 收缩投影
       （sdc_tv_single_proj，六代模板面均无单步件——K3 首发增量）＋几何
       迭代腿直接使用（sdc_tv_iter_proj）＋TV 非负投影（sdc_tv_nonneg）＋
       诚实 arch 槽计算器两件（sdc_arch_k/sdc_arch_k_budget，对应宿主
       r_arch_pow_attn Variable 槽）＋K3 主件两件（sdc_step_calc/
       sdc_step_calc_correct，均匀于全部 n ≥ N 的 TV 收缩，NatLe 序界面）＋
       sigT 模量见证（sdc_mixing_modulus_sigT）＋端到端主定理双投影三件
       （sdc_conv_step_calc/sdc_conv_step_correct/sdc_conv_modulus_sigT，
       零重放纯投影）。
   Set 载体纪律（语句面零 Prop）: 存在以 sigT、合取以 prod、nat 序界以
     NatLe（S01 的 leb 判定型 Set 载体，NatLe_drop/NatLe_lift 双向桥）；严格
     序界以 NatLe (S ·) 表达；实面比较以 Id 层 RI 接口字段 lt/le（Set 层值）；
     步数见证以 sigT nat。语句面零 Prop 版存在/合取/序界（宿主
     attention_iterate_converges 的 (N ≤ n) Prop 界在本件对应形面以 NatLe 重
     述，Prop 界只经 NatLe_drop 进证明体）；假设位零 Hypothesis/零 Prop 型；
     零 not/~/<> 书写面。
   fail-loud 记录: 宿主 r_arch_pow_attn 证书槽为诚实接口参数位（Variable，
     构造性居住而无算法内容，同系列 CL arch_pow_i 边界口径），可执行面由
     Part 2 nat 定点档承载（真 Fixpoint，Obj.magic=0 附加证）；任意实数率的
     实面 ceil 构造性桥库内确缺（系列结论不变），有理数据实面桥由系列前件
     （dsc_/asc_/cmc_/mtc2_ 各 Part 3）在役承载，本件不重复滚转；燃料充足性
     限衰减域（half 域 2·p ≤ q、E ≥ 2；qbound 域 q ≤ E、任意 p 小于 q）；
     严格档与 le 档语义分立: 首破「x 小于 e」与首达「x 至多 e」读数可差一步
     （系列烟测实拍: kappa=3/4、A=50、E=4 严格档读 11，le 档同数据读 10）。
   依赖: S01_BaseRing（NatLe/NatLe_drop/NatLe_lift/iterate/RealInterface
     Enhanced/StateSpace/SumOver）；S04_RealExpLogConv（r_pow）；
     S06_DiffSamplingGibbs（Require 不 Import——全限定使用 one_minus_delta_
     pos/one_minus_delta_lt_one/r_pow_dec_iter_attn/attention_tv_contraction/
     attention_tv_iter_contraction/attention_iterate_converges/tv_dist_nonneg/
     tv_dist/attention_step/boltzmann_dist_attn）；PeanoNat/Lia/Arith。全部
     Require-only 零改动，Live/注册面/缓存根零触碰。
   对标: mathlib 马尔可夫链混合时间界（Doeblin minorization 几何收缩）的构
     造性 Set 层 Id 面对应物；同系列 dsc_/asc_/cmc_/mtc2_/aic_/cw2_/p2c_/
     ap4_ 的 K3 面补全——几何收缩族 k 计算器批件在册末位补全。
   构造性: 纯构造性/Set 层零 Prop 载体（步数见证 nat 面 sigT；序谓词均
     Set 层值；nat 面算术不消入实面目标）；非平凡（sdc_k_enum 为真
     Fixpoint 首破枚举）；可提取（Separate Extraction Obj.magic=0 附加证）；
     零公理（尾 Print Assumptions 全 Closed 预期）。
   工艺红线: term-mode 全显式实参；数值定装（Eval vm_compute 烟测入日志）；
     注释内禁右括号星杠字面。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q
     vo_local_world_unified_0930 "" abl_s06_step_calc.v（池内执行）。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：收缩率定点枚举解算器（真 Fixpoint/首破严格档/Set 载体）      *)
(*   收缩率 kappa=p/q（0 小于 p 小于 q）、初值 A、预算 E 的定点表示，    *)
(*   首破枚举 N 使 powIter N A 严格低于 E。序界全走 NatLe Set 载体，     *)
(*   严格序界以 NatLe (S ·) 表达。本段含首破最小性见证两件与燃料充足    *)
(*   性三件。                                                          *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition sdc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma sdc_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (sdc_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold sdc_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition sdc_iter (p q x : nat) : nat := sdc_ceil_div (x * p) q.

Lemma sdc_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (sdc_iter p q x * q).
Proof.
  intros p q x Hq. unfold sdc_iter. apply (sdc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：sdc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint sdc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => sdc_iter p q (sdc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma sdc_pow_iter_comm : forall p q x k,
  sdc_pow_iter p q (sdc_iter p q x) k = sdc_iter p q (sdc_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x 严格低于 e 首破即停（返回已走步数），
   否则走衰减步再搜（Nat.ltb 判定，严格档停机面） *)
Fixpoint sdc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (sdc_k_enum f p q (sdc_iter p q x) e)
  end.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k 至多 iter^k(x)·q^k） *)
Lemma sdc_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (sdc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (sdc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (sdc_iter_step_bound p q (sdc_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (sdc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (sdc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (sdc_iter p q (sdc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (sdc_iter p q (sdc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* 正确性（首破严格面）：燃料内可达，枚举返回的 N 步处上取整值严格低于 e
   （NatLe (S ·) e 严格序界载体）。可达见证为 sigT＋prod＋NatLe 全 Set 载体。 *)
Theorem sdc_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  NatLe (Datatypes.S (sdc_pow_iter p q x (sdc_k_enum fuel p q x e))) e.
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
      * pose proof (NatLe_drop (Datatypes.S (sdc_pow_iter p q x 0)) e Hbound)
          as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (sdc_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (sdc_pow_iter p q (sdc_iter p q x) k0)) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (sdc_iter p q x) e Hterm').
        simpl.
        rewrite <- (sdc_pow_iter_comm p q x
                      (sdc_k_enum f p q (sdc_iter p q x) e)).
        exact IH.
Qed.

(* 首破最小性见证：燃料内可达，则对每个早于返回步数 N 的步 j（S j ≤ N），
   第 j 步上取整值仍 ≥ e——枚举读数是首个跌破预算的步。 *)
Theorem sdc_k_enum_minimal : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  forall j : nat, NatLe (Datatypes.S j) (sdc_k_enum fuel p q x e) ->
  NatLe e (sdc_pow_iter p q x j).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm j Hj.
  - exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl in Hj. rewrite Hlt in Hj.
      exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
    + simpl in Hj. rewrite Hlt in Hj.
      assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      pose proof (NatLe_drop (Datatypes.S j)
                    (Datatypes.S (sdc_k_enum f p q (sdc_iter p q x) e)) Hj)
        as Hj'.
      destruct j as [| j'].
      * simpl. apply (NatLe_lift e x). exact Hge.
      * simpl in Hj'.
        assert (Hj2 : NatLe (Datatypes.S j')
                        (sdc_k_enum f p q (sdc_iter p q x) e))
          by (apply (NatLe_lift _ _); lia).
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (sdc_pow_iter p q (sdc_iter p q x) k0)) e))).
        { destruct Hterm as [k [Hk Hbound]].
          pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
          destruct k as [| k'].
          - pose proof (NatLe_drop (Datatypes.S (sdc_pow_iter p q x 0)) e Hbound)
              as Hb'.
            simpl in Hb'. lia.
          - simpl in Hbound.
            rewrite <- (sdc_pow_iter_comm p q x k') in Hbound.
            assert (Hk2 : (k' <= f)%nat) by lia.
            exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (sdc_iter p q x) e Hterm' j' Hj2).
        simpl. rewrite <- (sdc_pow_iter_comm p q x j'). exact IH.
Qed.

(* 首破见证封装：燃料内可达，则枚举读数 N 携带双证书——第 N 步跌破预算
   （严格）＋每个早步仍保预算。sigT＋prod＋forall nat 全 Set 载体。 *)
Theorem sdc_k_enum_first_break : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  sigT (fun N : nat =>
    prod (NatLe (Datatypes.S (sdc_pow_iter p q x N)) e)
         (forall j : nat, NatLe (Datatypes.S j) N ->
                          NatLe e (sdc_pow_iter p q x j))).
Proof.
  intros fuel p q x e H.
  exists (sdc_k_enum fuel p q x e). split.
  - exact (sdc_k_enum_correct fuel p q x e H).
  - exact (sdc_k_enum_minimal fuel p q x e H).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N 至多 e·q^N（log 单调下的等价面；
   严格首破面 y 低于 e 由 NatLe (S y) e 一跳降为 y 至多 e） *)
Theorem sdc_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  NatLe (x * p ^ sdc_k_enum fuel p q x e)
        (e * q ^ sdc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (sdc_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (sdc_pow_iter_exact_ge p q x (sdc_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (sdc_pow_iter p q x (sdc_k_enum fuel p q x e)
              * q ^ sdc_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ sdc_k_enum fuel p q x e)).
    lia.
Qed.

(* ---------- 严格衰减三件与燃料充足性见证（调用侧 Hterm 闭合） ---------- *)

(* 衰减核：x·p + q 至多 x·q 时上取整走步严格递降（floor 判据 d·q ≤ a 低于 x·q） *)
Lemma sdc_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold sdc_iter, sdc_ceil_div.
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
Lemma sdc_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (sdc_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p 低于 q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma sdc_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (sdc_iter_lt_decay p q x).
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
Theorem sdc_fuel_sufficient_gen : forall fuel p q x E,
  NatLe x fuel ->
  (forall y : nat, NatLe E y ->
                   NatLe (Datatypes.S (sdc_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    destruct E as [| E'].
    + exfalso.
      pose proof (Hdecay 0%nat (NatLe_lift 0 0 (Nat.le_refl 0))) as Hd.
      pose proof (NatLe_drop (Datatypes.S (sdc_iter p q 0)) 0 Hd) as Hd'.
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
      assert (Hdec : NatLe (Datatypes.S (sdc_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift E x). exact Hge. }
      pose proof (NatLe_drop (Datatypes.S (sdc_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (sdc_iter p q x <= f)%nat) by lia.
      destruct (IH p q (sdc_iter p q x) E (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (sdc_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 2，fuel := x 即足（严格首破面） *)
Theorem sdc_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (sdc_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (sdc_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 2 E HE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q、任意 p 低于 q，fuel := x 即足（严格首破面） *)
Theorem sdc_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (sdc_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (sdc_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即首破步数（Hterm 供给面闭合） *)
Theorem sdc_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe (Datatypes.S E) A ->
  NatLe (Datatypes.S (sdc_pow_iter p q A (sdc_k_enum A p q A E))) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (sdc_k_enum_correct A p q A E).
  apply (sdc_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* 定点档烟测一（数值定装）：kappa=1/2、A=1000、E=5 的减半首破枚举
   （衰减链 1000→500→250→125→63→32→16→8→4，4 严格低于 5 首破于第 8 步） *)
Eval vm_compute in (sdc_k_enum 50 1 2 1000 5).

(* 定点档烟测二：kappa=3/4、A=50、E=4 严格档（衰减链至第 10 步达 4，
   4 严格低于 4 不破，第 11 步达 3 首破——与 le 档同数据读 10 对照，
   语义分立实拍） *)
Eval vm_compute in (sdc_k_enum 50 3 4 50 4).

(* ============================================================ *)
(* Part 1：Id 层实面对应形（S06 AttentionGibbsBridge 证书子集 16 槽）——    *)
(*   率 omd := minus one delta（即 1−δ）。率双证书 exact 直接使用宿主出节    *)
(*   件（出节签名经 Check @ 检验确定: one_minus_delta_pos 四参无 delta_    *)
(*   pos、one_minus_delta_lt_one 四参无 delta_lt_one、attention_tv_iter_   *)
(*   contraction 无 lt_plus_compat_le_lt、attention_iterate_converges 全  *)
(*   证书＋arch 槽——discharge 最小化分立全数实拍）；幂单调腿以 NatLe     *)
(*   Set 载体重述；单步 Doeblin 收缩投影（K3 首发增量）；诚实 arch 槽    *)
(*   计算器；K3 主件（均匀 TV 收缩 NatLe 面）＋sigT 模量见证；端到端主   *)
(*   定理双投影三件（零重放纯投影）。                                     *)
(* ============================================================ *)

Section SdcGibbsCalc.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let minus := @minus RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* ---- Boltzmann 侧证书子集 ---- *)
Variable sum_pos_preserved :
  forall (f : S -> R), (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Let bdist := @S06_DiffSamplingGibbs.boltzmann_dist_attn RI SS SO
               sum_pos_preserved D D_pos energy.
Let tv := @S06_DiffSamplingGibbs.tv_dist RI SS SO.

(* ---- Markov 侧证书子集 ---- *)
Variable transition : S -> S -> R.
Variable transition_normalization :
  forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.

Let astepf := @S06_DiffSamplingGibbs.attention_step RI SS SO transition.

Variable detailed_balance :
  forall s s' : S,
    Id (mult (bdist s) (transition s s')) (mult (bdist s') (transition s' s)).

Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.

Let omd := minus one delta.

Variable minorization :
  forall s s' : S, le (mult delta (bdist s')) (transition s s').
Variable lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.

(* 几何击穿诚实接口槽（宿主 r_arch_pow_attn Variable 参数位同形对应） *)
Variable r_arch_pow_i :
  forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => lt (mult a (r_pow omd N)) eps).

(* ===== 率抽取双证书（exact 直接使用宿主出节件；出节实参经检验确定:        *)
(*   one_minus_delta_pos 四参无 delta_pos、one_minus_delta_lt_one 四参    *)
(*   无 delta_lt_one——同一节双主证书出节参数面分立，逐件 @ 全显参。 ====== *)

Lemma sdc_rate_pos : lt zero omd.
Proof.
  exact (@S06_DiffSamplingGibbs.one_minus_delta_pos RI delta delta_lt_one
           lt_plus_compat_lt_le).
Qed.

Lemma sdc_rate_lt_one : lt omd one.
Proof.
  exact (@S06_DiffSamplingGibbs.one_minus_delta_lt_one RI delta delta_pos
           lt_plus_compat_le_lt).
Qed.

(* ===== 幂单调腿的 Set 载体重述（宿主 r_pow_dec_iter_attn 的 Prop 序界面  *)
(*   (m ≤ n)%nat 在本件语句面以 NatLe 重述；Prop 界只经 NatLe_drop 进证明  *)
(*   体，零 Prop 消入 Set。） ============================================ *)

Lemma sdc_r_pow_dec_iter_set : forall m n : nat,
  NatLe m n -> le (r_pow omd n) (r_pow omd m).
Proof.
  intros m n Hmn.
  exact (@S06_DiffSamplingGibbs.r_pow_dec_iter_attn RI delta delta_pos
           delta_lt_one lt_plus_compat_lt_le lt_plus_compat_le_lt
           m n (NatLe_drop m n Hmn)).
Qed.

(* ===== 单步 Doeblin 收缩投影（宿主主定理 attention_tv_contraction 直接使用 *)
(*   ——六代模板面均无单步件，K3 首发增量。出节实参序经检验确定: 无        *)
(*   delta_pos、无 lt_plus_compat_le_lt。） ============================== *)

Theorem sdc_tv_single_proj : forall mu : S -> R,
  Id (sum_over_S mu) one ->
  (forall s : S, le zero (mu s)) ->
  le (tv (astepf mu) bdist) (mult omd (tv mu bdist)).
Proof.
  intros mu Hmu_norm Hmu_nonneg.
  exact (@S06_DiffSamplingGibbs.attention_tv_contraction RI SS SO
           sum_pos_preserved D D_pos energy transition
           transition_normalization detailed_balance delta delta_lt_one
           minorization lt_plus_compat_lt_le sum_swap_cc abs_ge_zero_id_cc
           mu Hmu_norm Hmu_nonneg).
Qed.

(* ===== 几何迭代腿直接使用（收缩脊柱读出面: 率 r_pow omd n 显式在语句面） == *)

Theorem sdc_tv_iter_proj : forall (mu : S -> R) (n : nat),
  Id (sum_over_S mu) one ->
  (forall s : S, le zero (mu s)) ->
  le (tv (iterate astepf n mu) bdist) (mult (r_pow omd n) (tv mu bdist)).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  exact (@S06_DiffSamplingGibbs.attention_tv_iter_contraction RI SS SO
           sum_pos_preserved D D_pos energy transition
           transition_normalization detailed_balance delta delta_pos
           delta_lt_one minorization lt_plus_compat_lt_le sum_swap_cc
           abs_ge_zero_id_cc mu n Hmu_norm Hmu_nonneg).
Qed.

(* ===== TV 非负投影（宿主 tv_dist_nonneg 直接使用——零证书直投面） ======== *)

Theorem sdc_tv_nonneg : forall mu nu : S -> R, le zero (tv mu nu).
Proof.
  intros mu nu. exact (@S06_DiffSamplingGibbs.tv_dist_nonneg RI SS SO mu nu).
Qed.

(* ===== 诚实 arch 槽计算器（精度到步数的见证读数） ====================== *)

Definition sdc_arch_k (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (r_arch_pow_i a Ha eps Heps).

Theorem sdc_arch_k_budget : forall (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps),
  lt (mult a (r_pow omd (sdc_arch_k a Ha eps Heps))) eps.
Proof.
  intros a Ha eps Heps. exact (projT2 (r_arch_pow_i a Ha eps Heps)).
Qed.

(* ===== K3 主件: 精度到步数计算器＋均匀收缩正确性 ======================= *)
(*   sdc_step_calc: TV0 := tv(mu0, bdist) 严格正的 arch 槽读数（projT1）； *)
(*   sdc_step_calc_correct: 对全部 n ≥ N（NatLe 序界），迭代 TV 严格低于    *)
(*   预算 eps——宿主 attention_iterate_converges 同链 NatLe 重述（几何迭代 *)
(*   腿＋NatLe 幂单调腿＋arch 预算腿，le_lt_trans 双段换轨）。 ============ *)

Definition sdc_step_calc (mu0 : S -> R) (Hmu : Id (sum_over_S mu0) one)
  (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist))
  : nat :=
  projT1 (r_arch_pow_i (tv mu0 bdist) Htv0 eps Heps).

Theorem sdc_step_calc_correct : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)) (n : nat),
  NatLe (sdc_step_calc mu0 Hmu Hmu0 eps Heps Htv0) n ->
  lt (tv (iterate astepf n mu0) bdist) eps.
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0. unfold sdc_step_calc.
  destruct (r_arch_pow_i (tv mu0 bdist) Htv0 eps Heps) as [N HN].
  intros n Hn.
  apply (le_lt_trans _ (mult (r_pow omd n) (tv mu0 bdist)) _).
  - exact (sdc_tv_iter_proj mu0 n Hmu Hmu0).
  - apply (le_lt_trans _ (mult (r_pow omd N) (tv mu0 bdist)) _).
    + apply (le_mult_compat_weak (r_pow omd n) (r_pow omd N)
               (tv mu0 bdist)).
      * exact (sdc_tv_nonneg mu0 bdist).
      * exact (sdc_r_pow_dec_iter_set N n Hn).
    + exact (lt_id_l _ _ _
               (mult_comm (r_pow omd N) (tv mu0 bdist)) HN).
Qed.

(* sigT 封装（均匀 TV 收缩模量见证型; 宿主主定理结论面的 NatLe 载体形） *)
Theorem sdc_mixing_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv (iterate astepf n mu0) bdist) eps).
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0.
  exists (sdc_step_calc mu0 Hmu Hmu0 eps Heps Htv0).
  intros n Hn. exact (sdc_step_calc_correct mu0 Hmu Hmu0 eps Heps Htv0 n Hn).
Defined.

(* ===== 端到端主定理双投影（零重放纯投影: 步数读数 projT1、均匀收缩      *)
(*   正确性经 NatLe_drop 桥、sigT 封装。出节实参序经检验确定: 全证书＋    *)
(*   arch 槽在前、mu0 三参与 eps 三参在后。） ============================ *)

Definition sdc_conv_step_calc (mu0 : S -> R) (Hmu : Id (sum_over_S mu0) one)
  (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist))
  : nat :=
  projT1 (@S06_DiffSamplingGibbs.attention_iterate_converges RI SS SO
            sum_pos_preserved D D_pos energy transition
            transition_normalization detailed_balance delta delta_pos
            delta_lt_one minorization lt_plus_compat_lt_le
            lt_plus_compat_le_lt sum_swap_cc abs_ge_zero_id_cc r_arch_pow_i
            mu0 Hmu Hmu0 eps Heps Htv0).

Theorem sdc_conv_step_correct : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)) (n : nat),
  NatLe (sdc_conv_step_calc mu0 Hmu Hmu0 eps Heps Htv0) n ->
  lt (tv (iterate astepf n mu0) bdist) eps.
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0. unfold sdc_conv_step_calc.
  destruct (@S06_DiffSamplingGibbs.attention_iterate_converges RI SS SO
              sum_pos_preserved D D_pos energy transition
              transition_normalization detailed_balance delta delta_pos
              delta_lt_one minorization lt_plus_compat_lt_le
              lt_plus_compat_le_lt sum_swap_cc abs_ge_zero_id_cc r_arch_pow_i
              mu0 Hmu Hmu0 eps Heps Htv0) as [N HN].
  intros n Hn.
  exact (HN n (NatLe_drop _ _ Hn)).
Qed.

(* sigT 封装（端到端均匀收缩模量见证型） *)
Theorem sdc_conv_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv (iterate astepf n mu0) bdist) eps).
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0.
  exists (sdc_conv_step_calc mu0 Hmu Hmu0 eps Heps Htv0).
  intros n Hn. exact (sdc_conv_step_correct mu0 Hmu Hmu0 eps Heps Htv0 n Hn).
Defined.

End SdcGibbsCalc.

(* ============================================================ *)
(* 审计口: 公理面（全 Closed 预期）＋可提取强证（照系列模板模式）        *)
(* ============================================================ *)

Print Assumptions sdc_k_enum_correct.
Print Assumptions sdc_k_enum_minimal.
Print Assumptions sdc_k_enum_first_break.
Print Assumptions sdc_k_enum_logface.
Print Assumptions sdc_fuel_sufficient_half.
Print Assumptions sdc_fuel_sufficient_qbound.
Print Assumptions sdc_k_enum_auto_half.
Print Assumptions sdc_rate_pos.
Print Assumptions sdc_rate_lt_one.
Print Assumptions sdc_r_pow_dec_iter_set.
Print Assumptions sdc_tv_nonneg.
Print Assumptions sdc_tv_single_proj.
Print Assumptions sdc_tv_iter_proj.
Print Assumptions sdc_arch_k_budget.
Print Assumptions sdc_step_calc_correct.
Print Assumptions sdc_mixing_modulus_sigT.
Print Assumptions sdc_conv_step_correct.
Print Assumptions sdc_conv_modulus_sigT.

(* 提取口: nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction sdc_ceil_div sdc_iter sdc_pow_iter sdc_k_enum.
