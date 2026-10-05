(* ==========================================================================)
   abl_mixchain_step_calc.v — 收敛计算器系列第四件（MixTimeChain 面，mtc2_ 前缀）
   使命：MixTimeChain.v 的 mtc_ 链（率双证书在案、主件 mtc_attention_mixing_time_local 吃通用选择器
      mix_k_select、端到端推论 mtc_mixing_time_cauchy_exp）缺「精度到步数」Defined 计算器。本件补齐
      三段：率抽取（kappa := tv_omd delta_star := tv_omd(lo·lo)、lo := expf(invT·opp Delta) 柯西面形）直
      使用宿主出节双证书；通用率面计算器两代＋具体率计算器与 sigT 模量见证＋宿主主件双投影＋零
      expf 前件柯西实例端到端读数三件＋nat 定点档十七件与 RI 泛型实面桥。
   对标行：mathlib 马尔可夫链混合时间界（geometric drift）的构造性 Set 层对应物；MixTimeChain.v §2 MtcCauchySoftmax 证书面；同系列 mtg_k_calc/mti_amt_attention_mixing_time 体例。
   三段主面：Part 2 nat 定点档（定点枚举与 correct/logface 两正确性、严格衰减三件、燃料充足性三件）；
      Part 3 实面桥（幂分裂三件、逆唯一两件、nat 单调嵌入桥两件、有理数据实面正确性）；Part 1 具体面
      逐形对应（率抽取双证书、通用率面计算器两代、具体率计算器三件、宿主主件双投影、柯西实例三件）。
   Set 形纪律：语句面零 Prop——存在以 sigT、合取以 prod、nat 序界以 NatLe（NatLe_drop/NatLe_lift 双向桥）；
      严格序界以 NatLe (S ·) 表达；实面比较以 real_lt/real_le（Set 层）；步数见证以 sigT nat；假设位零
      Prop 型（real_lt/real_eq/NatLe 均 Set 值）；零 not/~/<> 书写面；零 Qeq 坑。
   已知边界：mix_k_select 出节七参无 Arch 槽（实拍），mix_k_compute 仅需 budget 正性；实数 log 到 nat
      ceil 的构造性桥库内确缺，实面正确性以有理数据 kappa:=p/q 闭合（有界精度档）；燃料充足性见证限
      衰减域（half 域 2·p ≤ q 任意 E ≥ 1，qbound 域 E ≥ q−1 任意 p<q；p/q 逼近 1 且 E<q−1 时走步可
      停滞）；nat 面 kappa=1/2 烟测读数 8、3/4 读数 10（手核逐行一致）。
   依赖清单：S01_BaseRing–S04_RealExpLogConv（RealInterfaceEnhanced 面/le_mult_compat/r_pow_pos/
      lt_le_iff/le_id_l/le_id_r/NatLe/NatLe_drop/NatLe_lift 等在役）；S03_QExp（cauchy_real_exp 实例族）；
      Arch_PA_02（nat_to_R/nat_to_R_mult_hom）；UpTVDoeblin（tv_omd/tv_rpow）；UpReqMixingTime
      （mix_k_select/mix_k_compute/mix_k_spec）；MixTimeChain（mtc_kappa_pos/mtc_kappa_lt_one/
      mtc_attention_mixing_time_local/mtc_mixing_time_cauchy_exp）。Require-only 零改动。
   构造性注记：纯构造性/Set 层零 Prop 语句面（步数见证 nat 面 sigT；误差谓词 real_lt/real_le 为 Set 层
      值；nat 面算术不消入实面目标）；非平凡（mtc2_k_enum 为真 Fixpoint 上取整枚举）；可提取（Obj.magic=0
      附加证）；零公理（尾 PA 全 Closed 预期）。工艺红线：term-mode 全显式实参（Id 面）；Eval vm_compute
      烟测入日志；注释内禁右括号星杠字面。
   编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q vo_local_world_unified_0930 "" abl_mixchain_step_calc.v（池内执行）。
   查重登记：顶层名 40 枚全 mtc2_ 新前缀（宿主 MixTimeChain.v 在役 mtc_ 前缀；mtc2_ 全库 grep 零命中）。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.
Require Import MixTimeChain.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：log 模量方程的 nat 定点枚举解算器（真 Fixpoint/ceil 形）    *)
(*   模量方程 log(a·kappa^N) ≤ log eps 的 nat 面：以 kappa=p/q（0<p<q）、 *)
(*   初值 a=A、预算 eps=E 的公共尺度定点表示，枚举 N 使 A·p^N ≤ E·q^N。  *)
(*   枚举器用上取整衰减步（ceil 除法保上界方向）。序界全走 NatLe         *)
(*   Set 形（leb 判定型），严格序界以 NatLe (S ·) 表达。本段含严格        *)
(*   衰减与燃料充足性见证六件（调用侧 Hterm 供给面闭合）。               *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition mtc2_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma mtc2_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (mtc2_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold mtc2_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition mtc2_iter (p q x : nat) : nat := mtc2_ceil_div (x * p) q.

Lemma mtc2_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (mtc2_iter p q x * q).
Proof.
  intros p q x Hq. unfold mtc2_iter. apply (mtc2_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：mtc2_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint mtc2_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => mtc2_iter p q (mtc2_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma mtc2_pow_iter_comm : forall p q x k,
  mtc2_pow_iter p q (mtc2_iter p q x) k = mtc2_iter p q (mtc2_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x ≤ E 即停（返回已走步数），否则走衰减步再搜 *)
Fixpoint mtc2_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (mtc2_k_enum f p q (mtc2_iter p q x) e)
  end.

(* 正确性（上取整面）：燃料内可达，枚举返回的 N 步处上取整值 ≤ e。
   可达见证为 sigT＋prod＋NatLe 全 Set 形。 *)
Theorem mtc2_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q x k) e))) ->
  NatLe (mtc2_pow_iter p q x (mtc2_k_enum fuel p q x e)) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm.
  - destruct Hterm as [k [Hk Hbound]].
    pose proof (NatLe_drop k 0 Hk) as Hk'.
    assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.leb x e) eqn:Hle.
    + simpl. apply (NatLe_lift x e). exact (proj1 (Nat.leb_le x e) Hle).
    + assert (Hgt : (e < x)%nat) by (apply (proj1 (Nat.leb_gt x e)); exact Hle).
      destruct Hterm as [k [Hk Hbound]].
      pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
      destruct k as [| k'].
      * pose proof (NatLe_drop (mtc2_pow_iter p q x 0) e Hbound) as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (mtc2_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (mtc2_pow_iter p q (mtc2_iter p q x) k0) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (mtc2_iter p q x) e Hterm').
        simpl.
        rewrite <- (mtc2_pow_iter_comm p q x (mtc2_k_enum f p q (mtc2_iter p q x) e)).
        exact IH.
Qed.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma mtc2_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (mtc2_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (mtc2_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (mtc2_iter_step_bound p q (mtc2_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (mtc2_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (mtc2_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (mtc2_iter p q (mtc2_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (mtc2_iter p q (mtc2_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N ≤ e·q^N（log 单调下的等价面） *)
Theorem mtc2_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q x k) e))) ->
  NatLe (x * p ^ mtc2_k_enum fuel p q x e)
        (e * q ^ mtc2_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (mtc2_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (mtc2_pow_iter_exact_ge p q x (mtc2_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (mtc2_pow_iter p q x (mtc2_k_enum fuel p q x e)
              * q ^ mtc2_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ mtc2_k_enum fuel p q x e)). exact H1'.
Qed.

(* ---------- 严格衰减三件与燃料充足性见证（调用侧 Hterm 闭合） ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据 d·q ≤ a < x·q） *)
Lemma mtc2_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold mtc2_iter, mtc2_ceil_div.
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
Lemma mtc2_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (mtc2_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma mtc2_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (mtc2_iter_lt_decay p q x).
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

(* 燃料充足性（泛形）：凡预算以上走步严格递降，则 A 步燃料必达预算内。
   结构归纳（燃料单调），见证 sigT＋prod＋NatLe 全 Set 形。 *)
Lemma mtc2_fuel_sufficient_gen : forall fuel p q x E,
  NatLe 1 q -> NatLe 1 E -> NatLe x fuel ->
  (forall y : nat, NatLe (Datatypes.S E) y ->
                   NatLe (Datatypes.S (mtc2_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hq HE Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    exists 0%nat. split.
    + apply (NatLe_lift 0 0). apply Nat.le_refl.
    + simpl. apply (NatLe_lift 0 E). apply Nat.le_0_l.
  - intros p q x E Hq HE Hx Hdecay.
    destruct (Nat.leb x E) eqn:Hle.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S f)). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift x E). exact (proj1 (Nat.leb_le x E) Hle).
    + assert (Hgt : (E < x)%nat) by (apply (proj1 (Nat.leb_gt x E)); exact Hle).
      pose proof (NatLe_drop x (Datatypes.S f) Hx) as Hx'.
      assert (Hdec : NatLe (Datatypes.S (mtc2_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift (Datatypes.S E) x). lia. }
      pose proof (NatLe_drop (Datatypes.S (mtc2_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (mtc2_iter p q x <= f)%nat) by lia.
      destruct (IH p q (mtc2_iter p q x) E Hq HE (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (mtc2_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 1，fuel := x 即足 *)
Theorem mtc2_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (mtc2_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (2 * p) q H2p). lia.
  - exact HE.
  - exact Hx.
  - intros y Hy. apply (mtc2_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 1 E HE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q−1、任意 p<q，fuel := x 即足 *)
Theorem mtc2_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (mtc2_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (Datatypes.S p) q Hpq). lia.
  - apply (NatLe_lift 1 E).
    pose proof (NatLe_drop (Datatypes.S p) q Hpq).
    pose proof (NatLe_drop q E HqE). lia.
  - exact Hx.
  - intros y Hy. apply (mtc2_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即正确步数（Hterm 供给面闭合） *)
Theorem mtc2_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe (Datatypes.S E) A ->
  NatLe (mtc2_pow_iter p q A (mtc2_k_enum A p q A E)) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (mtc2_k_enum_correct A p q A E).
  apply (mtc2_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* 定点档烟测一（数值定装）：kappa=1/2、A=1000、E=5 的减半枚举 *)
Eval vm_compute in (mtc2_k_enum 30 1 2 1000 5).

(* 定点档烟测二：kappa=3/4（qbound 域 E=4 ≥ q−1=3）、A=50、E=4 *)
Eval vm_compute in (mtc2_k_enum 30 3 4 50 4).

(* ============================================================ *)
(* Part 3：实面桥——定点档计算器在具体有理数据上的实面正确性            *)
(*   （RI 泛型 Section；nat 序界面以 NatLe Set 形承载，不消入实面        *)
(*   目标——leb 判定＋差值等式 replace 的嵌入桥照系列模板滚转）          *)
(* ============================================================ *)

Section Mtc2EnumReal.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

(* 左单位律补桥（Id 面一跳） *)
Lemma mtc2_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Qed.

(* 逆元唯一性：y·z == 1 则 z == inv y *)
Lemma mtc2_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (mtc2_mult_one_l (inv_pos y Hy))))))).
Qed.

(* 幂对乘法的分裂：r_pow(a·b,n) == r_pow(a,n)·r_pow(b,n)（库缺，系列补件；
   Id 面 rewrite 匹配不可靠，全链 term-mode） *)
Lemma mtc2_rpow_mult : forall (a b : R) (n : nat),
  Id (r_pow (mult a b) n) (mult (r_pow a n) (r_pow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - simpl. exact (id_sym (mult_one one)).
  - simpl.
    exact (id_trans
             (id_cong (fun t => mult (mult a b) t) IH)
             (id_trans (id_sym (mult_assoc a b (mult (r_pow a n) (r_pow b n))))
             (id_trans (id_cong (fun t => mult a t) (mult_assoc b (r_pow a n) (r_pow b n)))
             (id_trans (id_cong (fun t => mult a t)
                                (id_cong (fun t => mult t (r_pow b n)) (mult_comm b (r_pow a n))))
             (id_trans (id_cong (fun t => mult a t) (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Qed.

(* nat_to_R 与幂交换：r_pow(nat_to_R k,n) == nat_to_R(k^n)（乘法同态归纳） *)
Lemma mtc2_nat_r_pow : forall k n : nat,
  Id (r_pow (nat_to_R k) n) (nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - exact (id_sym (plus_zero one)).
  - exact (id_trans
             (id_cong (fun t => mult (nat_to_R k) t) IH)
             (id_sym (nat_to_R_mult_hom k (k ^ n)%nat))).
Qed.

(* 幂对逆的分裂：r_pow(inv x,n) == inv(r_pow x,n)（逆唯一性归纳；
   逆的正性证书 Hp 作显式槽——防 Qed 不透明常数上的换形） *)
Lemma mtc2_rpow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (mtc2_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (mtc2_inv_unique (mult x (r_pow x n))
                             (mult (inv_pos x Hx)
                                   (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                             Hp
                             (id_trans
                                (id_sym (mult_assoc x (r_pow x n)
                                           (mult (inv_pos x Hx)
                                                 (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (mult_assoc (r_pow x n) (inv_pos x Hx)
                                                     (inv_pos (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult t (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                                                  (mult_comm (r_pow x n) (inv_pos x Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_sym (mult_assoc (inv_pos x Hx) (r_pow x n)
                                                        (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult (inv_pos x Hx) t)
                                                  (inv_pos_correct (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t) (mult_one (inv_pos x Hx)))
                                (inv_pos_correct x Hx))))))))).
Qed.

(* nat 序界到实面 le 嵌入单调桥（库缺，系列滚转件）。
   消除纪律：NatLe 形不消入实面目标——leb 判定分支＋差值等式
   replace，nat 归纳走 Set 层加法辅助件，零 Prop 消除。 *)
Lemma mtc2_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
Proof.
  intros n m. induction n as [| n IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_trans _ (nat_to_R (n + m)%nat)).
    + exact IH.
    + apply (le_id_l (nat_to_R (n + m)) (plus (nat_to_R (n + m)) zero)
              (plus one (nat_to_R (n + m)))
              (id_sym (plus_zero (nat_to_R (n + m))))).
      apply (le_id_r (plus (nat_to_R (n + m)) zero) (plus (nat_to_R (n + m)) one)
              (plus one (nat_to_R (n + m))) (plus_comm (nat_to_R (n + m)) one)).
      apply (le_plus_compat (nat_to_R (n + m)) (nat_to_R (n + m)) zero one
               (le_refl (nat_to_R (n + m)))).
      exact (lt_le_iff zero one (inl one_pos)).
Qed.

Lemma mtc2_nat_le_embed : forall m n : nat,
  NatLe m n -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. destruct (Nat.leb n m) eqn:E.
  - assert (Hle : (n <= m)%nat) by (apply (proj1 (Nat.leb_le n m)); exact E).
    pose proof (NatLe_drop m n Hmn) as Hmn'.
    assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact Hle.
      - exact Hmn'. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      pose proof (NatLe_drop m (Datatypes.S n') Hmn) as HmnD.
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (mtc2_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* 定点档主件：有理数据 kappa:=p/q、a:=A、eps:=E 上，枚举 N 的实面正确性
   （le 形，零 arch 依赖——全桥由本件幂分裂定律闭合） *)
Theorem mtc2_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  NatLe 1 p -> NatLe 1 q -> NatLe 1 A -> NatLe 1 E ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q A k) E))) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (mtc2_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq HA HE Hterm.
  set (N := mtc2_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (mtc2_k_enum_logface fuel p q A E Hp Hq Hterm) as Hlog.
  pose proof (mtc2_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
  assert (Hsplit : le (mult (nat_to_R A) (nat_to_R (p ^ N)))
                      (mult (nat_to_R E) (nat_to_R (q ^ N)))).
  { apply (le_id_l (mult (nat_to_R A) (nat_to_R (p ^ N)))
                   (nat_to_R (A * p ^ N))).
    - exact (id_sym (nat_to_R_mult_hom A (p ^ N))).
    - apply (le_id_r (nat_to_R (A * p ^ N))
                     (nat_to_R (E * q ^ N))
                     (mult (nat_to_R E) (nat_to_R (q ^ N)))
                     (nat_to_R_mult_hom E (q ^ N))).
      exact Hemb. }
  assert (H3 : le (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                  (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w))
    by exact (le_mult_compat (mult (nat_to_R A) (nat_to_R (p ^ N)))
                             (mult (nat_to_R E) (nat_to_R (q ^ N))) w
                             (inv_pos_pos (r_pow (nat_to_R q) N)
                                (r_pow_pos (nat_to_R q) N Hqr))
                             Hsplit).
  assert (HL : Id (mult (nat_to_R A)
                        (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                  (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)).
  { pose proof (mtc2_rpow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
    pose proof (mtc2_nat_r_pow p N) as Hpo.
    pose proof (mtc2_rpow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
    assert (Hs2 : Id (mult (r_pow (nat_to_R p) N)
                           (r_pow (inv_pos (nat_to_R q) Hqr) N))
                     (mult (nat_to_R (p ^ N)) w)).
    { apply (id_trans
               (id_cong (fun u => mult u (r_pow (inv_pos (nat_to_R q) Hqr) N)) Hpo)).
      exact (id_cong (fun u => mult (nat_to_R (p ^ N)) u) Hpi). }
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hpm)).
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hs2)).
    exact (mult_assoc (nat_to_R A) (nat_to_R (p ^ N)) w). }
  assert (HR : Id (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w) (nat_to_R E)).
  { exact (id_trans
             (id_sym (mult_assoc (nat_to_R E) (nat_to_R (q ^ N)) w))
             (id_trans
                (id_cong (fun t => mult (nat_to_R E) t)
                         (id_trans
                            (id_cong (fun u => mult u w)
                                     (id_sym (mtc2_nat_r_pow q N)))
                            (inv_pos_correct (r_pow (nat_to_R q) N)
                                             (r_pow_pos (nat_to_R q) N Hqr))))
                (mult_one (nat_to_R E)))). }
  apply (le_id_l (mult (nat_to_R A)
                         (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                 (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (nat_to_R E) HL).
  apply (le_id_r (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)
                 (nat_to_R E) HR H3).
Qed.

End Mtc2EnumReal.

(* ============================================================ *)
(* Part 1：具体面逐形对应（MixTimeChain §2 MtcCauchySoftmax 证书子集）——   *)
(*   kappa := tv_omd delta_star、delta_star := lo·lo、                  *)
(*   lo := expf(invT·opp Delta)。率双证书 exact 直使用宿主出节件；       *)
(*   通用率面计算器两代（mix_k_select 形 + mix_k_compute 提取形）；      *)
(*   具体率计算器与 sigT 模量见证；宿主主件 projT1/projT2 双投影。       *)
(* ============================================================ *)

Section Mtc2FaceCalc.

Variable invT : Real.
Variable invT_pos : real_lt real_zero invT.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable expf : Real -> Real.
Variable expf_pos : forall x : Real, real_lt real_zero (expf x).
Variable expf_zero : real_eq (expf real_zero) real_one.
Variable expf_mono_lt : forall a b : Real, real_lt a b -> real_lt (expf a) (expf b).

Let lo := expf (real_mult invT (real_opp Delta)).
Let delta_star := real_mult lo lo.
Let kappa := tv_omd delta_star.

(* ===== 率抽取双证书（exact 直使用宿主出节件；出节实参序经直接钉死：     *)
(*   mtc_kappa_pos 八参、mtc_kappa_lt_one 出节最小化仅四参） ============ *)

Lemma mtc2_rate_pos : real_lt real_zero kappa.
Proof.
  exact (mtc_kappa_pos invT invT_pos Delta Delta_pos
           expf expf_pos expf_zero expf_mono_lt).
Qed.

Lemma mtc2_rate_lt_one : real_lt kappa real_one.
Proof.
  exact (mtc_kappa_lt_one invT Delta expf expf_pos).
Qed.

(* ===== 通用率面计算器两代 ========================================= *)
(*   其一：mtg_k_calc 同构（mix_k_select 七参直连，le 面 Or 分决）；      *)
(*   其二：见证/证明分离提取形（mix_k_compute 透明读数走 real_arch        *)
(*   显式 nat；mix_k_spec 不透明证书承载正确性，运行时不强制求值）。      *)

Definition mtc2_rate_step_calc (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget) : nat :=
  projT1 (mix_k_select krate TV0 budget Hk1 Hk2 Ha Hb).

Theorem mtc2_rate_step_calc_correct : forall (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow krate (mtc2_rate_step_calc krate TV0 budget Hk1 Hk2 Ha Hb))
             TV0)
          budget.
Proof.
  intros krate TV0 budget Hk1 Hk2 Ha Hb.
  exact (projT2 (mix_k_select krate TV0 budget Hk1 Hk2 Ha Hb)).
Qed.

Definition mtc2_rate_step_compute (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Hb : real_lt real_zero budget) : nat :=
  mix_k_compute krate TV0 budget Hk1 Hk2 Hb.

Theorem mtc2_rate_step_compute_correct : forall (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_lt real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow krate (mtc2_rate_step_compute krate TV0 budget Hk1 Hk2 Hb))
             TV0)
          budget.
Proof.
  intros krate TV0 budget Hk1 Hk2 Ha Hb.
  exact (mix_k_spec krate TV0 budget Hk1 Hk2 Ha Hb).
Qed.

(* ===== 抽取率上的具体计算器：kappa := tv_omd(lo·lo) =============== *)
(*   lo·lo 即 e^(-2·Delta·invT) 的柯西面形（delta_star），率双证书       *)
(*   mtc2_rate_pos/mtc2_rate_lt_one 已由宿主出节件直使用闭合。           *)

Definition mtc2_kappa_step_compute (TV0 budget : Real)
  (Hb : real_lt real_zero budget) : nat :=
  mix_k_compute kappa TV0 budget mtc2_rate_pos mtc2_rate_lt_one Hb.

Theorem mtc2_kappa_step_compute_correct : forall (TV0 : Real)
  (Ha : real_lt real_zero TV0) (budget : Real) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow kappa (mtc2_kappa_step_compute TV0 budget Hb))
             TV0)
          budget.
Proof.
  intros TV0 Ha budget Hb.
  exact (mix_k_spec kappa TV0 budget mtc2_rate_pos mtc2_rate_lt_one Ha Hb).
Qed.

(* sigT 封装（率面）：精度预算到步数的见证型（mix_k_select_r1 同构：      *)
(*   witness=计算器读数、proof=正确性证书，projT1 归约固定） *)
Theorem mtc2_kappa_modulus_sigT : forall (TV0 : Real)
  (Ha : real_lt real_zero TV0) (budget : Real) (Hb : real_lt real_zero budget),
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 Ha budget Hb.
  exists (mtc2_kappa_step_compute TV0 budget Hb).
  exact (mtc2_kappa_step_compute_correct TV0 Ha budget Hb).
Defined.

(* ===== 宿主主件双投影：le 面计算器（mtc_attention_mixing_time_local） *)

Definition mtc2_mix_step_calc (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
            expf expf_pos expf_zero expf_mono_lt TV0 budget Ha Hb).

Theorem mtc2_mix_step_correct : forall (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow kappa (mtc2_mix_step_calc TV0 budget Ha Hb))
             TV0)
          budget.
Proof.
  intros TV0 budget Ha Hb.
  exact (projT2 (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
                   expf expf_pos expf_zero expf_mono_lt TV0 budget Ha Hb)).
Qed.

(* sigT 封装（TV 面）：混合时间模量见证型 *)
Theorem mtc2_mixing_modulus_sigT : forall (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 budget Ha Hb.
  exists (mtc2_mix_step_calc TV0 budget Ha Hb).
  exact (mtc2_mix_step_correct TV0 budget Ha Hb).
Defined.

End Mtc2FaceCalc.

(* ===== 端到端柯西实例：零 expf 前件的计算器读数（宿主推论双投影） ======
   以 cauchy_real_exp 实例消解 expf 迷你接口（宿主 mtc_mixing_time_cauchy_exp
   同款）：只需温度倒数与 logit 直径为正，计算器即返回步数。 *)

Definition mtc2_cauchy_exp_step_calc (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtc_mixing_time_cauchy_exp invT Delta HinvT HDelta TV0 budget Ha Hb).

Theorem mtc2_cauchy_exp_step_correct : forall (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow
                (tv_omd (real_mult
                            (cauchy_real_exp (real_mult invT (real_opp Delta)))
                            (cauchy_real_exp (real_mult invT (real_opp Delta)))))
                (mtc2_cauchy_exp_step_calc invT HinvT Delta HDelta TV0 Ha budget Hb))
             TV0)
          budget.
Proof.
  intros invT HinvT Delta HDelta TV0 Ha budget Hb.
  exact (projT2 (mtc_mixing_time_cauchy_exp invT Delta HinvT HDelta TV0 budget Ha Hb)).
Qed.

(* sigT 封装（端到端柯西面）：混合时间模量见证型 *)
Theorem mtc2_cauchy_exp_modulus_sigT : forall (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget),
  sigT (fun k : nat =>
    real_lt (real_mult
               (tv_rpow
                  (tv_omd (real_mult
                              (cauchy_real_exp (real_mult invT (real_opp Delta)))
                              (cauchy_real_exp (real_mult invT (real_opp Delta)))))
                  k)
               TV0)
            budget).
Proof.
  intros invT HinvT Delta HDelta TV0 Ha budget Hb.
  exists (mtc2_cauchy_exp_step_calc invT HinvT Delta HDelta TV0 Ha budget Hb).
  exact (mtc2_cauchy_exp_step_correct invT HinvT Delta HDelta TV0 Ha budget Hb).
Defined.

(* ============================================================ *)
(* 审计口：公理面（全 Closed 预期）＋可提取强证（照系列模板模式）        *)
(* ============================================================ *)

Print Assumptions mtc2_k_enum_correct.
Print Assumptions mtc2_k_enum_logface.
Print Assumptions mtc2_fuel_sufficient_half.
Print Assumptions mtc2_fuel_sufficient_qbound.
Print Assumptions mtc2_enum_real_correct.
Print Assumptions mtc2_rate_step_calc_correct.
Print Assumptions mtc2_rate_step_compute_correct.
Print Assumptions mtc2_kappa_step_compute_correct.
Print Assumptions mtc2_kappa_modulus_sigT.
Print Assumptions mtc2_mix_step_correct.
Print Assumptions mtc2_mixing_modulus_sigT.
Print Assumptions mtc2_cauchy_exp_step_correct.
Print Assumptions mtc2_cauchy_exp_modulus_sigT.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction mtc2_ceil_div mtc2_iter mtc2_pow_iter mtc2_k_enum.
