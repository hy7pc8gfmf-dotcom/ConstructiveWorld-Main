(* ==========================================================================)
   abl_concfin_step_calc.v — 收敛计算器系列第七件（UpReqConcFin2 面，cfc_ 前缀，
   定量完备性矿脉表 K10 位）
   使命: 为 UpReqConcFin2.v 收缩收敛面（bool 二态世界 cf2 链: 率 cf2_omd :=
     1 − δ*、δ* := lo·lo、lo := rsq_exp_pos_fn(invT·opp Delta)、主件 cf2_mixing_
     time_le 以显式参 k0 承载几何衰减前提）补齐「精度到步数」计算器: nat 定点
     档真 Fixpoint 计算器＋实面有理桥＋率抽取（cf2_omd_pos 显式直用）＋K10 缺
     口主闭合件——精度数据枚举出 k0 后逐支输入宿主 cf2_mixing_time_le 的端到
     端 sigT 混合见证（cfc_k0_feeds_mixing: 有理上界率证书 Homd ＋ TV₀ 上界嵌
     入 HTV ＋半预算下界嵌入 HB2 三槽诚实申报）。
   本件陈述（三段，33 个 cfc_ 常数）: nat 定点档（真 Fixpoint）: cfc_ceil_div/cfc_iter/
     cfc_pow_iter/cfc_k_enum＋正确性两半＋严格衰减三件＋燃料充足性三件＋auto_half；
     实面桥（S07 实例面 req 承载，Id 面范本按环境面 setoid 重绑转写）: 左单位/逆唯一＋
     幂分裂＋reqd 嵌入幂＋幂正性/幂单调＋nat 单调嵌入两件＋cfc_enum_real_correct；
     cf2 具体面: cfc_rate_pos＋cfc_k0_select＋cfc_k0_feeds_mixing＋宿主双投影三件。
   语义边界: 实数 log 到 nat ceil 的构造性桥库内确缺（系列四代同录），实面正确
     性以有理数据 kappa:=p/q 闭合（有界精度档）；cf2_omd 为柯西实数非有理，端
     到端件率槽以「有理上界证书」申报（le 档只需上界），其构造性供给位留开放
     登记；燃料充足性限衰减域；nat 烟测读数 8/10（同算法手核一致）。
   依赖: S01_BaseRing–S04_RealExpLogConv＋S07_RealSetoidExpLog（NatLe 系/实例
     面 req/lt/le/mult 字段在役）；UpReqDist（reqd_nat_to_R 系——透传不导出故自
     Require）；UpReqSampling（req_r_pow）；Arch_PA_02；UpReqConcFin2（cf2_omd/cf2_omd_pos/
     cf2_tv/cf2_mixing_time_le 系）；Stdlib Arith/Lia。Require-only 零改动。
   对标: 同系列计算器族（mtc2_/atn_ 等）K10 位补全；CD 矫正范本滚转合并。
   构造性: 纯构造性/Set 层零 Prop；非平凡（cfc_k_enum 真 Fixpoint 上取整枚举）；
     可提取（Obj.magic=0 附加证）；零公理（尾 Print Assumptions 全 Closed 预期）。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s
     65532 && nice -19 rocq c -native-compiler no -Q vo_local_world_unified_0930
     "" abl_concfin_step_calc.v（池内执行）。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：log 模量方程的 nat 定点枚举解算器（真 Fixpoint/ceil 形）    *)
(*   模量方程 log(a·kappa^N) ≤ log eps 的 nat 面：以 kappa=p/q（0<p<q）、 *)
(*   初值 a=A、预算 eps=E 的公共尺度定点表示，枚举 N 使 A·p^N ≤ E·q^N。  *)
(*   序界全走 NatLe Set 承载（leb 判定型），严格序界以 NatLe (S ·) 表达。 *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition cfc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma cfc_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (cfc_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold cfc_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition cfc_iter (p q x : nat) : nat := cfc_ceil_div (x * p) q.

Lemma cfc_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (cfc_iter p q x * q).
Proof.
  intros p q x Hq. unfold cfc_iter. apply (cfc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：cfc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint cfc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => cfc_iter p q (cfc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma cfc_pow_iter_comm : forall p q x k,
  cfc_pow_iter p q (cfc_iter p q x) k = cfc_iter p q (cfc_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x ≤ E 即停（返回已走步数），否则走衰减步再搜 *)
Fixpoint cfc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (cfc_k_enum f p q (cfc_iter p q x) e)
  end.

(* 正确性（上取整面）：燃料内可达，枚举返回的 N 步处上取整值 ≤ e。
   可达见证为 sigT＋prod＋NatLe 全 Set 承载。 *)
Theorem cfc_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (cfc_pow_iter p q x k) e))) ->
  NatLe (cfc_pow_iter p q x (cfc_k_enum fuel p q x e)) e.
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
      * pose proof (NatLe_drop (cfc_pow_iter p q x 0) e Hbound) as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (cfc_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (cfc_pow_iter p q (cfc_iter p q x) k0) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (cfc_iter p q x) e Hterm').
        simpl.
        rewrite <- (cfc_pow_iter_comm p q x (cfc_k_enum f p q (cfc_iter p q x) e)).
        exact IH.
Qed.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma cfc_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (cfc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (cfc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (cfc_iter_step_bound p q (cfc_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (cfc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (cfc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (cfc_iter p q (cfc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (cfc_iter p q (cfc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N ≤ e·q^N（log 单调下的等价面） *)
Theorem cfc_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (cfc_pow_iter p q x k) e))) ->
  NatLe (x * p ^ cfc_k_enum fuel p q x e)
        (e * q ^ cfc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (cfc_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (cfc_pow_iter_exact_ge p q x (cfc_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (cfc_pow_iter p q x (cfc_k_enum fuel p q x e)
              * q ^ cfc_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ cfc_k_enum fuel p q x e)). exact H1'.
Qed.

(* ---------- 严格衰减三件与燃料充足性见证（调用侧 Hterm 闭合） ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据 d·q ≤ a < x·q） *)
Lemma cfc_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (cfc_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold cfc_iter, cfc_ceil_div.
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
Lemma cfc_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (cfc_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (cfc_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma cfc_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (cfc_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (cfc_iter_lt_decay p q x).
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
   结构归纳（燃料单调），见证 sigT＋prod＋NatLe 全 Set 承载。 *)
Lemma cfc_fuel_sufficient_gen : forall fuel p q x E,
  NatLe 1 q -> NatLe 1 E -> NatLe x fuel ->
  (forall y : nat, NatLe (Datatypes.S E) y ->
                   NatLe (Datatypes.S (cfc_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (cfc_pow_iter p q x k) E)).
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
      assert (Hdec : NatLe (Datatypes.S (cfc_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift (Datatypes.S E) x). lia. }
      pose proof (NatLe_drop (Datatypes.S (cfc_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (cfc_iter p q x <= f)%nat) by lia.
      destruct (IH p q (cfc_iter p q x) E Hq HE (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (cfc_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 1，fuel := x 即足 *)
Theorem cfc_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (cfc_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (cfc_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (2 * p) q H2p). lia.
  - exact HE.
  - exact Hx.
  - intros y Hy. apply (cfc_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 1 E HE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q−1、任意 p<q，fuel := x 即足 *)
Theorem cfc_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (cfc_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (cfc_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (Datatypes.S p) q Hpq). lia.
  - apply (NatLe_lift 1 E).
    pose proof (NatLe_drop (Datatypes.S p) q Hpq).
    pose proof (NatLe_drop q E HqE). lia.
  - exact Hx.
  - intros y Hy. apply (cfc_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即正确步数（Hterm 供给面闭合） *)
Theorem cfc_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe (Datatypes.S E) A ->
  NatLe (cfc_pow_iter p q A (cfc_k_enum A p q A E)) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (cfc_k_enum_correct A p q A E).
  apply (cfc_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* 定点档烟测一（数值定装）：kappa=1/2、A=1000、E=5 的减半枚举 *)
Eval vm_compute in (cfc_k_enum 30 1 2 1000 5).

(* 定点档烟测二：kappa=3/4（qbound 域 E=4 ≥ q−1=3）、A=50、E=4 *)
Eval vm_compute in (cfc_k_enum 30 3 4 50 4).

(* ============================================================ *)
(* Part 3：实面桥——定点档计算器在具体有理数据上的实面正确性            *)
(*   （S07 实例面 req 承载；CD 范本的 Id 面按环境面 setoid 重绑转写:       *)
(*   id_trans→req_trans、id_cong→req_mult_compat、nat_to_R→reqd_nat_to_R、 *)
(*   r_pow→req_r_pow；nat 序界面以 NatLe Set 承载承载，不消入实面目标）    *)
(* ============================================================ *)

(* 左单位律补桥（req 面一跳：mult_comm 换形＋右单位 mult_one） *)
Lemma cfc_mult_one_l : forall t : Real, req (mult one t) t.
Proof.
  intros t.
  exact (req_trans (mult one t) (mult t one) t (mult_comm one t) (mult_one t)).
Qed.

(* 逆元唯一性：y·z == 1 则 z == inv y（req 面 term-mode 全链） *)
Lemma cfc_inv_unique : forall (y z : Real) (Hy : lt zero y),
  req (mult y z) one -> req z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (req_trans z (mult z one) (inv_pos y Hy)
           (req_sym (mult z one) z (mult_one z))
           (req_trans (mult z one) (mult z (mult y (inv_pos y Hy)))
                      (inv_pos y Hy)
                      (req_mult_compat z z one (mult y (inv_pos y Hy))
                         (req_refl z)
                         (req_sym (mult y (inv_pos y Hy)) one (inv_pos_correct y Hy)))
                      (req_trans (mult z (mult y (inv_pos y Hy)))
                                 (mult (mult z y) (inv_pos y Hy))
                                 (inv_pos y Hy)
                                 (mult_assoc z y (inv_pos y Hy))
                                 (req_trans (mult (mult z y) (inv_pos y Hy))
                                            (mult (mult y z) (inv_pos y Hy))
                                            (inv_pos y Hy)
                                            (req_mult_compat (mult z y) (mult y z)
                                               (inv_pos y Hy) (inv_pos y Hy)
                                               (mult_comm z y)
                                               (req_refl (inv_pos y Hy)))
                                            (req_trans (mult (mult y z) (inv_pos y Hy))
                                                       (mult one (inv_pos y Hy))
                                                       (inv_pos y Hy)
                                                       (req_mult_compat (mult y z) one
                                                          (inv_pos y Hy) (inv_pos y Hy)
                                                          Hz
                                                          (req_refl (inv_pos y Hy)))
                                                       (cfc_mult_one_l
                                                          (inv_pos y Hy))))))).
Qed.

(* 幂对乘法的分裂：req_r_pow(a·b,n) == req_r_pow(a,n)·req_r_pow(b,n)
   （库缺，系列补件；req 面 rewrite 匹配不可靠，全链 term-mode） *)
Lemma cfc_rpow_mult : forall (a b : Real) (n : nat),
  req (req_r_pow (mult a b) n) (mult (req_r_pow a n) (req_r_pow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - simpl. exact (req_sym (mult one one) one (mult_one one)).
  - simpl.
    pose proof (req_mult_compat (mult a b) (mult a b)
                           (req_r_pow (mult a b) n)
                           (mult (req_r_pow a n) (req_r_pow b n))
                           (req_refl (mult a b)) IH) as T1.
    pose proof (req_sym (mult a (mult b (mult (req_r_pow a n) (req_r_pow b n))))
                       (mult (mult a b) (mult (req_r_pow a n) (req_r_pow b n)))
                       (mult_assoc a b (mult (req_r_pow a n) (req_r_pow b n)))) as S1.
    pose proof (req_mult_compat a a
               (mult b (mult (req_r_pow a n) (req_r_pow b n)))
               (mult (mult b (req_r_pow a n)) (req_r_pow b n))
               (req_refl a)
               (mult_assoc b (req_r_pow a n) (req_r_pow b n))) as S2.
    pose proof (req_mult_compat a a
               (mult (mult b (req_r_pow a n)) (req_r_pow b n))
               (mult (mult (req_r_pow a n) b) (req_r_pow b n))
               (req_refl a)
               (req_mult_compat (mult b (req_r_pow a n)) (mult (req_r_pow a n) b)
                  (req_r_pow b n) (req_r_pow b n)
                  (mult_comm b (req_r_pow a n))
                  (req_refl (req_r_pow b n)))) as S3.
    pose proof (req_mult_compat a a
               (mult (mult (req_r_pow a n) b) (req_r_pow b n))
               (mult (req_r_pow a n) (mult b (req_r_pow b n)))
               (req_refl a)
               (req_sym (mult (req_r_pow a n) (mult b (req_r_pow b n)))
                          (mult (mult (req_r_pow a n) b) (req_r_pow b n))
                          (mult_assoc (req_r_pow a n) b (req_r_pow b n)))) as S4.
    pose proof (mult_assoc a (req_r_pow a n) (mult b (req_r_pow b n))) as S5.
    exact (req_trans (mult (mult a b) (req_r_pow (mult a b) n))
                     (mult a (mult b (mult (req_r_pow a n) (req_r_pow b n))))
                     (mult (mult a (req_r_pow a n)) (mult b (req_r_pow b n)))
                     (req_trans (mult (mult a b) (req_r_pow (mult a b) n))
                                (mult (mult a b)
                                      (mult (req_r_pow a n) (req_r_pow b n)))
                                (mult a (mult b (mult (req_r_pow a n) (req_r_pow b n))))
                                T1 S1)
                     (req_trans (mult a (mult b (mult (req_r_pow a n) (req_r_pow b n))))
                                (mult a (mult (mult (req_r_pow a n) b)
                                              (req_r_pow b n)))
                                (mult (mult a (req_r_pow a n))
                                      (mult b (req_r_pow b n)))
                                (req_trans
                                   (mult a (mult b (mult (req_r_pow a n) (req_r_pow b n))))
                                   (mult a (mult (mult b (req_r_pow a n))
                                                 (req_r_pow b n)))
                                   (mult a (mult (mult (req_r_pow a n) b)
                                                 (req_r_pow b n)))
                                   S2 S3)
                                (req_trans
                                   (mult a (mult (mult (req_r_pow a n) b)
                                                 (req_r_pow b n)))
                                   (mult a (mult (req_r_pow a n)
                                                 (mult b (req_r_pow b n))))
                                   (mult (mult a (req_r_pow a n))
                                         (mult b (req_r_pow b n)))
                                   S4 S5))).
Qed.

(* reqd_nat_to_R 与幂交换：req_r_pow(reqd k,n) == reqd(k^n)
   （乘法同态归纳；change 定点展开防 reqd 侧过归约） *)
Lemma cfc_reqd_r_pow : forall k n : nat,
  req (req_r_pow (reqd_nat_to_R k) n) (reqd_nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - simpl. exact (req_sym (plus one zero) one (plus_zero one)).
  - change (req (mult (reqd_nat_to_R k) (req_r_pow (reqd_nat_to_R k) n))
                (reqd_nat_to_R (k * k ^ n)%nat)).
    exact (req_trans (mult (reqd_nat_to_R k) (req_r_pow (reqd_nat_to_R k) n))
                     (mult (reqd_nat_to_R k) (reqd_nat_to_R (k ^ n)%nat))
                     (reqd_nat_to_R (k * k ^ n)%nat)
                     (req_mult_compat (reqd_nat_to_R k) (reqd_nat_to_R k)
                        (req_r_pow (reqd_nat_to_R k) n)
                        (reqd_nat_to_R (k ^ n)%nat)
                        (req_refl (reqd_nat_to_R k)) IH)
                     (req_sym (reqd_nat_to_R (k * k ^ n)%nat)
                        (mult (reqd_nat_to_R k) (reqd_nat_to_R (k ^ n)%nat))
                        (reqd_nat_to_R_mult_hom k (k ^ n)%nat))).
Qed.

(* 幂正性：底正则幂正（mult_positive 逐级归纳；S04 r_pow_pos 的实例面自持版） *)
Lemma cfc_req_r_pow_pos : forall (x : Real) (Hx : lt zero x) (n : nat),
  lt zero (req_r_pow x n).
Proof.
  intros x Hx n. induction n as [| n IH].
  - simpl. exact one_pos.
  - simpl. exact (mult_positive x (req_r_pow x n) Hx IH).
Qed.

(* 非负底幂单调：0 ≤ x ≤ y ⟹ x^n ≤ y^n（leg1 右乘、leg2 左乘） *)
Lemma cfc_req_r_pow_le_mono : forall (x y : Real)
  (Hx0 : lt zero x) (Hxy : le x y) (n : nat),
  le (req_r_pow x n) (req_r_pow y n).
Proof.
  intros x y Hx0 Hxy n. induction n as [| n IH].
  - apply (le_refl (req_r_pow x 0)).
  - simpl.
    exact (le_trans (mult x (req_r_pow x n)) (mult y (req_r_pow x n))
                    (mult y (req_r_pow y n))
                    (le_mult_compat x y (req_r_pow x n)
                       (cfc_req_r_pow_pos x Hx0 n) Hxy)
                    (le_id_l (mult y (req_r_pow x n))
                             (mult (req_r_pow x n) y)
                             (mult y (req_r_pow y n))
                             (mult_comm y (req_r_pow x n))
                             (le_trans (mult (req_r_pow x n) y)
                                       (mult (req_r_pow y n) y)
                                       (mult y (req_r_pow y n))
                                       (le_mult_compat (req_r_pow x n)
                                          (req_r_pow y n) y
                                          (lt_le_trans zero x y Hx0 Hxy) IH)
                                       (le_id_r (mult (req_r_pow y n) y)
                                                (mult (req_r_pow y n) y)
                                                (mult y (req_r_pow y n))
                                                (mult_comm (req_r_pow y n) y)
                                                (le_refl
                                                   (mult (req_r_pow y n) y)))))).
Qed.

(* 幂对逆的分裂：req_r_pow(inv x,n) == inv(req_r_pow x,n)（逆唯一性归纳；
   逆的正性证书 Hp 作显式槽——防 Qed 不透明常数上的换形） *)
Lemma cfc_rpow_inv : forall (x : Real) (Hx : lt zero x) (n : nat)
  (Hp : lt zero (req_r_pow x n)),
  req (req_r_pow (inv_pos x Hx) n) (inv_pos (req_r_pow x n) Hp).
Proof.
  intros x Hx n.
  assert (Hpair : forall m : nat,
            req (mult (req_r_pow x m)
                      (req_r_pow (inv_pos x Hx) m)) one).
  { intro m. induction m as [| m IH].
    - exact (mult_one one).
    - simpl.
      assert (Hre : req (mult (mult x (req_r_pow x m))
                              (mult (inv_pos x Hx)
                                    (req_r_pow (inv_pos x Hx) m)))
                         (mult (mult x (inv_pos x Hx))
                               (mult (req_r_pow x m)
                                     (req_r_pow (inv_pos x Hx) m)))).
      { exact (req_trans
                 (mult (mult x (req_r_pow x m))
                       (mult (inv_pos x Hx)
                             (req_r_pow (inv_pos x Hx) m)))
                 (mult x
                       (mult (req_r_pow x m)
                             (mult (inv_pos x Hx)
                                   (req_r_pow (inv_pos x Hx) m))))
                 (mult (mult x (inv_pos x Hx))
                       (mult (req_r_pow x m)
                             (req_r_pow (inv_pos x Hx) m)))
                 (req_sym (mult x
                            (mult (req_r_pow x m)
                                  (mult (inv_pos x Hx)
                                        (req_r_pow (inv_pos x Hx) m))))
                       (mult (mult x (req_r_pow x m))
                             (mult (inv_pos x Hx)
                                   (req_r_pow (inv_pos x Hx) m)))
                       (mult_assoc x (req_r_pow x m)
                          (mult (inv_pos x Hx)
                                (req_r_pow (inv_pos x Hx) m))))
                 (req_trans
                    (mult x
                          (mult (req_r_pow x m)
                                (mult (inv_pos x Hx)
                                      (req_r_pow (inv_pos x Hx) m))))
                    (mult x
                          (mult (inv_pos x Hx)
                                (mult (req_r_pow x m)
                                      (req_r_pow (inv_pos x Hx) m))))
                    (mult (mult x (inv_pos x Hx))
                          (mult (req_r_pow x m)
                                (req_r_pow (inv_pos x Hx) m)))
                    (req_mult_compat x x
                       (mult (req_r_pow x m)
                             (mult (inv_pos x Hx)
                                   (req_r_pow (inv_pos x Hx) m)))
                       (mult (inv_pos x Hx)
                             (mult (req_r_pow x m)
                                   (req_r_pow (inv_pos x Hx) m)))
                       (req_refl x)
                       (req_trans (mult (req_r_pow x m)
                                          (mult (inv_pos x Hx)
                                                (req_r_pow (inv_pos x Hx) m)))
                                  (mult (mult (req_r_pow x m) (inv_pos x Hx))
                                        (req_r_pow (inv_pos x Hx) m))
                                  (mult (inv_pos x Hx)
                                        (mult (req_r_pow x m)
                                              (req_r_pow (inv_pos x Hx) m)))
                                  (mult_assoc (req_r_pow x m) (inv_pos x Hx)
                                     (req_r_pow (inv_pos x Hx) m))
                                  (req_trans
                                     (mult (mult (req_r_pow x m) (inv_pos x Hx))
                                           (req_r_pow (inv_pos x Hx) m))
                                     (mult (mult (inv_pos x Hx) (req_r_pow x m))
                                           (req_r_pow (inv_pos x Hx) m))
                                     (mult (inv_pos x Hx)
                                           (mult (req_r_pow x m)
                                                 (req_r_pow (inv_pos x Hx) m)))
                                     (req_mult_compat
                                        (mult (req_r_pow x m) (inv_pos x Hx))
                                        (mult (inv_pos x Hx) (req_r_pow x m))
                                        (req_r_pow (inv_pos x Hx) m)
                                        (req_r_pow (inv_pos x Hx) m)
                                        (mult_comm (req_r_pow x m) (inv_pos x Hx))
                                        (req_refl (req_r_pow (inv_pos x Hx) m)))
                                     (req_sym (mult (inv_pos x Hx)
                                                (mult (req_r_pow x m)
                                                      (req_r_pow (inv_pos x Hx) m)))
                                           (mult (mult (inv_pos x Hx)
                                                       (req_r_pow x m))
                                                 (req_r_pow (inv_pos x Hx) m))
                                           (mult_assoc (inv_pos x Hx)
                                                       (req_r_pow x m)
                                                       (req_r_pow (inv_pos x Hx) m))))))
                    (mult_assoc x (inv_pos x Hx)
                       (mult (req_r_pow x m)
                             (req_r_pow (inv_pos x Hx) m))))). }
      exact (req_trans (mult (mult x (req_r_pow x m))
                             (mult (inv_pos x Hx)
                                   (req_r_pow (inv_pos x Hx) m)))
                       (mult (mult x (inv_pos x Hx))
                             (mult (req_r_pow x m)
                                   (req_r_pow (inv_pos x Hx) m)))
                       one
                       Hre
                       (req_trans (mult (mult x (inv_pos x Hx))
                                        (mult (req_r_pow x m)
                                              (req_r_pow (inv_pos x Hx) m)))
                                  (mult one
                                        (mult (req_r_pow x m)
                                              (req_r_pow (inv_pos x Hx) m)))
                                  one
                                  (req_mult_compat
                                     (mult x (inv_pos x Hx)) one
                                     (mult (req_r_pow x m)
                                           (req_r_pow (inv_pos x Hx) m))
                                     (mult (req_r_pow x m)
                                           (req_r_pow (inv_pos x Hx) m))
                                     (inv_pos_correct x Hx)
                                     (req_refl (mult (req_r_pow x m)
                                                     (req_r_pow (inv_pos x Hx) m))))
                                  (cfc_mult_one_l (mult (req_r_pow x m)
                                                        (req_r_pow (inv_pos x Hx) m))))). }
  intros Hp.
  intros Hp.
  exact (cfc_inv_unique (req_r_pow x n) (req_r_pow (inv_pos x Hx) n)
           Hp (Hpair n)).
Qed.

(* nat 序界到实面 le 嵌入单调桥（reqd 面，库缺系列滚转件）。
   消除纪律：NatLe 承载不消入实面目标——leb 判定分支＋差值等式
   replace，nat 归纳走 Set 层加法辅助件，零 Prop 消除。 *)
Lemma cfc_nat_le_plus_aux : forall n m : nat,
  le (reqd_nat_to_R m) (reqd_nat_to_R (n + m)%nat).
Proof.
  intros n m. induction n as [| n IH].
  - apply (le_refl (reqd_nat_to_R (0 + m)%nat)).
  - cbn [reqd_nat_to_R].
    exact (le_trans (reqd_nat_to_R m) (reqd_nat_to_R (n + m)%nat)
                    (plus one (reqd_nat_to_R (n + m)%nat))
                    IH
                    (le_id_l (reqd_nat_to_R (n + m)%nat)
                             (plus (reqd_nat_to_R (n + m)%nat) zero)
                             (plus one (reqd_nat_to_R (n + m)%nat))
                             (req_sym (plus (reqd_nat_to_R (n + m)%nat) zero)
                                        (reqd_nat_to_R (n + m)%nat)
                                        (plus_zero (reqd_nat_to_R (n + m)%nat))))
                    (le_id_r (plus (reqd_nat_to_R (n + m)%nat) zero)
                             (plus (reqd_nat_to_R (n + m)%nat) one)
                             (plus one (reqd_nat_to_R (n + m)%nat))
                             (plus_comm (reqd_nat_to_R (n + m)%nat) one)
                             (le_plus_compat (reqd_nat_to_R (n + m)%nat)
                                (reqd_nat_to_R (n + m)%nat) zero one
                                (le_refl (reqd_nat_to_R (n + m)%nat))
                                (lt_le_iff zero one (inl one_pos))))).
Qed.

Lemma cfc_nat_le_embed : forall m n : nat,
  NatLe m n -> le (reqd_nat_to_R m) (reqd_nat_to_R n).
Proof.
  intros m n Hmn. destruct (Nat.leb n m) eqn:E.
  - assert (Hle : (n <= m)%nat) by (apply (proj1 (Nat.leb_le n m)); exact E).
    pose proof (NatLe_drop m n Hmn) as Hmn'.
    assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact Hle.
      - exact Hmn'. }
    rewrite Heq. exact (le_refl (reqd_nat_to_R m)).
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      pose proof (NatLe_drop m (Datatypes.S n') Hmn) as HmnD.
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (cfc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* 定点档主件：有理数据 kappa:=p/q、a:=A、eps:=E 上，枚举 N 的实面正确性
   （le 形，零 arch 依赖——全桥由幂分裂定律闭合） *)
Theorem cfc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (reqd_nat_to_R q)),
  NatLe 1 p -> NatLe 1 q -> NatLe 1 A -> NatLe 1 E ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (cfc_pow_iter p q A k) E))) ->
  le (mult (reqd_nat_to_R A)
            (req_r_pow (mult (reqd_nat_to_R p)
                             (inv_pos (reqd_nat_to_R q) Hqr))
                       (cfc_k_enum fuel p q A E)))
     (reqd_nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq HA HE Hterm.
  set (N := cfc_k_enum fuel p q A E).
  set (w := inv_pos (req_r_pow (reqd_nat_to_R q) N)
                    (cfc_req_r_pow_pos (reqd_nat_to_R q) Hqr N)).
  pose proof (cfc_k_enum_logface fuel p q A E Hp Hq Hterm) as Hlog.
  pose proof (cfc_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
  assert (Hsplit : le (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N)))
                      (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N)))).
  { exact (le_id_l (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N)))
                   (reqd_nat_to_R (A * p ^ N))
                   (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N)))
                   (req_sym (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N)))
                              (reqd_nat_to_R (A * p ^ N))
                              (reqd_nat_to_R_mult_hom A (p ^ N)))
                   (le_id_r (reqd_nat_to_R (A * p ^ N))
                            (reqd_nat_to_R (E * q ^ N))
                            (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N)))
                            (reqd_nat_to_R_mult_hom E (q ^ N))
                            Hemb)). }
  assert (H3 : le (mult (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N))) w)
                  (mult (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N))) w))
    by exact (le_mult_compat (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N)))
                             (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N))) w
                             (inv_pos_pos (req_r_pow (reqd_nat_to_R q) N)
                                (cfc_req_r_pow_pos (reqd_nat_to_R q) Hqr N))
                             Hsplit).
  assert (HL : req (mult (reqd_nat_to_R A)
                         (req_r_pow (mult (reqd_nat_to_R p)
                                          (inv_pos (reqd_nat_to_R q) Hqr)) N))
                   (mult (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N))) w)).
  { pose proof (cfc_rpow_mult (reqd_nat_to_R p)
                  (inv_pos (reqd_nat_to_R q) Hqr) N) as Hpm.
    pose proof (cfc_reqd_r_pow p N) as Hpo.
    pose proof (cfc_rpow_inv (reqd_nat_to_R q) Hqr N
                  (cfc_req_r_pow_pos (reqd_nat_to_R q) Hqr N)) as Hpi.
    assert (Hs2 : req (mult (req_r_pow (reqd_nat_to_R p) N)
                            (req_r_pow (inv_pos (reqd_nat_to_R q) Hqr) N))
                      (mult (reqd_nat_to_R (p ^ N)) w))
      by exact (req_mult_compat Hpo Hpi).
    exact (req_trans (mult (reqd_nat_to_R A)
                           (req_r_pow (mult (reqd_nat_to_R p)
                                            (inv_pos (reqd_nat_to_R q) Hqr)) N))
                     (mult (reqd_nat_to_R A)
                           (mult (req_r_pow (reqd_nat_to_R p) N)
                                 (req_r_pow (inv_pos (reqd_nat_to_R q) Hqr) N)))
                     (mult (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N))) w)
                     (req_mult_compat (reqd_nat_to_R A) (reqd_nat_to_R A)
                         (req_r_pow (mult (reqd_nat_to_R p)
                                          (inv_pos (reqd_nat_to_R q) Hqr)) N)
                         (mult (req_r_pow (reqd_nat_to_R p) N)
                               (req_r_pow (inv_pos (reqd_nat_to_R q) Hqr) N))
                         (req_refl (reqd_nat_to_R A)) Hpm)
                     (req_trans (mult (reqd_nat_to_R A)
                                      (mult (req_r_pow (reqd_nat_to_R p) N)
                                            (req_r_pow (inv_pos (reqd_nat_to_R q) Hqr) N)))
                                (mult (reqd_nat_to_R A)
                                      (mult (reqd_nat_to_R (p ^ N)) w))
                                (mult (mult (reqd_nat_to_R A)
                                            (reqd_nat_to_R (p ^ N))) w)
                                (req_mult_compat (reqd_nat_to_R A) (reqd_nat_to_R A)
                                   (mult (req_r_pow (reqd_nat_to_R p) N)
                                         (req_r_pow (inv_pos (reqd_nat_to_R q) Hqr) N))
                                   (mult (reqd_nat_to_R (p ^ N)) w)
                                   (req_refl (reqd_nat_to_R A)) Hs2)
                                (mult_assoc (reqd_nat_to_R A)
                                            (reqd_nat_to_R (p ^ N)) w))). }
  assert (HR : req (mult (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N))) w)
                   (reqd_nat_to_R E)).
  { exact (req_trans (mult (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N))) w)
                     (mult (reqd_nat_to_R E)
                           (mult (reqd_nat_to_R (q ^ N)) w))
                     (reqd_nat_to_R E)
                     (req_sym (mult (reqd_nat_to_R E)
                                       (mult (reqd_nat_to_R (q ^ N)) w))
                                (mult (mult (reqd_nat_to_R E)
                                            (reqd_nat_to_R (q ^ N))) w)
                                (mult_assoc (reqd_nat_to_R E)
                                            (reqd_nat_to_R (q ^ N)) w))
                     (req_trans (mult (reqd_nat_to_R E)
                                      (mult (reqd_nat_to_R (q ^ N)) w))
                                (mult (reqd_nat_to_R E) one)
                                (reqd_nat_to_R E)
                                (req_mult_compat (reqd_nat_to_R E) (reqd_nat_to_R E)
                                   (mult (reqd_nat_to_R (q ^ N)) w) one
                                   (req_refl (reqd_nat_to_R E))
                                   (req_trans (mult (reqd_nat_to_R (q ^ N)) w)
                                              one
                                              (reqd_nat_to_R E)
                                              (req_mult_compat
                                                 (reqd_nat_to_R (q ^ N))
                                                 (req_r_pow (reqd_nat_to_R q) N)
                                                 w w
                                                 (req_sym (req_r_pow (reqd_nat_to_R q) N)
                                                          (reqd_nat_to_R (q ^ N))
                                                          (cfc_reqd_r_pow q N))
                                                 (req_refl w))
                                              (inv_pos_correct
                                                 (req_r_pow (reqd_nat_to_R q) N)
                                                 (cfc_req_r_pow_pos
                                                    (reqd_nat_to_R q) N Hqr))))
                                (mult_one (reqd_nat_to_R E)))). }
  exact (le_id_l (mult (reqd_nat_to_R A)
                       (req_r_pow (mult (reqd_nat_to_R p)
                                        (inv_pos (reqd_nat_to_R q) Hqr)) N))
                 (mult (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N))) w)
                 (reqd_nat_to_R E)
                 HL
                 (le_id_r (mult (mult (reqd_nat_to_R A) (reqd_nat_to_R (p ^ N))) w)
                          (mult (mult (reqd_nat_to_R E) (reqd_nat_to_R (q ^ N))) w)
                          (reqd_nat_to_R E) HR H3)).
Qed.

(* ============================================================ *)
(* Part 1：cf2 具体面（UpReqConcFin2 收缩收敛面，K10 缺口闭合）——        *)
(*   率 cf2_omd 宿主显式在案（显式直用）；K10 判定「无 k 选择器」由        *)
(*   cfc_k0_select（nat 定点档）＋cfc_k0_feeds_mixing（端到端输入宿主      *)
(*   cf2_mixing_time_le 得 sigT 混合见证）闭合；宿主双投影三件。          *)
(* ============================================================ *)

(* ===== 率抽取（显式直用）：cf2_omd 正性证书 exact 直接使用宿主出节件 ===== *)

Lemma cfc_rate_pos : lt zero cf2_omd.
Proof.
  exact cf2_omd_pos.
Qed.

(* ===== K10 k 选择器：精度到步数（nat 定点档） ==================== *)

Definition cfc_k0_select (fuel p q A E : nat) : nat :=
  cfc_k_enum fuel p q A E.

(* ===== 端到端主闭合件：精度数据枚举 k0 输入宿主 cf2_mixing_time_le ====
   前件（诚实申报，三嵌入槽）：①Hqr 有理率分母正性＋NatLe 1 p/1 q；
   ②Hterm 燃料充足性见证（cfc_fuel_sufficient_half/qbound 供给）；
   ③Homd 率上界证书（有界精度档：p/q 为 cf2_omd 的实面上界——le 档只需
   上界）；④HTV TV₀ 上界嵌入；⑤HB2 半预算下界嵌入；⑥HB 预算正性。
   链：幂单调→有理枚举桥→嵌入槽传递，得宿主几何前提，
   输入 cf2_mixing_time_le 得 sigT 混合见证（步数 = S k0）。 *)

Theorem cfc_k0_feeds_mixing : forall (fuel p q A E : nat) (budget : Real)
  (Hqr : lt zero (reqd_nat_to_R q))
  (Hnp : NatLe 1 p) (Hnq : NatLe 1 q) (HA1 : NatLe 1 A) (HE1 : NatLe 1 E)
  (Hterm : sigT (fun k : nat =>
            prod (NatLe k fuel) (NatLe (cfc_pow_iter p q A k) E)))
  (Homd : le cf2_omd (mult (reqd_nat_to_R p)
                           (inv_pos (reqd_nat_to_R q) Hqr)))
  (HTV : le (cf2_tv cf2_mu0 cf2_nu0) (reqd_nat_to_R A))
  (HB2 : le (reqd_nat_to_R E) (mult cf2_inv_two budget))
  (HB : lt zero budget),
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros fuel p q A E budget Hqr Hnp Hnq HA1 HE1 Hterm Homd HTV HB2 HB.
  destruct p as [| p'].
  - exfalso.
    pose proof (NatLe_drop 1 0 Hnp) as H0.
    lia.
  - set (N := cfc_k0_select (Datatypes.S p') q A E).
    assert (Hpp : lt zero (reqd_nat_to_R (Datatypes.S p')))
      by exact (reqd_nat_to_R_pos p').
    set (pq := mult (reqd_nat_to_R (Datatypes.S p'))
                    (inv_pos (reqd_nat_to_R q) Hqr)).
    assert (Hpq : lt zero pq).
    { unfold pq. exact (mult_positive (reqd_nat_to_R (Datatypes.S p'))
                          (inv_pos (reqd_nat_to_R q) Hqr)
                          Hpp (inv_pos_pos (reqd_nat_to_R q) Hqr)). }
    assert (Hleg2 : le (req_r_pow cf2_omd N) (req_r_pow pq N)).
    { unfold pq. exact (cfc_req_r_pow_le_mono cf2_omd
                          (mult (reqd_nat_to_R (Datatypes.S p'))
                                (inv_pos (reqd_nat_to_R q) Hqr))
                          cfc_rate_pos Homd N). }
    assert (H12 : le (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                     (mult (req_r_pow pq N) (cf2_tv cf2_mu0 cf2_nu0))).
    { exact (le_mult_compat (req_r_pow cf2_omd N) (req_r_pow pq N)
               (cf2_tv cf2_mu0 cf2_nu0) cf2_tv_pos Hleg2). }
    assert (H3 : le (mult (cf2_tv cf2_mu0 cf2_nu0) (req_r_pow pq N))
                    (mult (reqd_nat_to_R A) (req_r_pow pq N))).
    { exact (le_mult_compat (cf2_tv cf2_mu0 cf2_nu0) (reqd_nat_to_R A)
               (req_r_pow pq N) Hpq HTV). }
    assert (H4 : le (mult (req_r_pow pq N) (cf2_tv cf2_mu0 cf2_nu0))
                    (mult (reqd_nat_to_R A) (req_r_pow pq N))).
    { apply (le_id_l (mult (req_r_pow pq N) (cf2_tv cf2_mu0 cf2_nu0))
               (mult (cf2_tv cf2_mu0 cf2_nu0) (req_r_pow pq N))
               (mult (reqd_nat_to_R A) (req_r_pow pq N))
               (mult_comm (req_r_pow pq N) (cf2_tv cf2_mu0 cf2_nu0)) H3). }
    assert (H5 : le (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                    (mult (reqd_nat_to_R A) (req_r_pow pq N))).
    { exact (le_trans (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                      (mult (req_r_pow pq N) (cf2_tv cf2_mu0 cf2_nu0))
                      (mult (reqd_nat_to_R A) (req_r_pow pq N)) H12 H4). }
    pose proof (cfc_enum_real_correct (Datatypes.S p') q A E Hqr
                  Hnp Hnq HA1 HE1 Hterm) as H6.
    unfold pq in H6.
    assert (H7 : le (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                    (reqd_nat_to_R E)).
    { exact (le_trans (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                      (mult (reqd_nat_to_R A)
                            (req_r_pow (mult (reqd_nat_to_R (Datatypes.S p'))
                                             (inv_pos (reqd_nat_to_R q) Hqr)) N))
                      (reqd_nat_to_R E) H5 H6). }
    exact (cf2_mixing_time_le budget N HB
             (le_trans (mult (req_r_pow cf2_omd N) (cf2_tv cf2_mu0 cf2_nu0))
                       (reqd_nat_to_R E)
                       (mult cf2_inv_two budget) H7 HB2)).
Qed.

(* ===== 宿主主件双投影：给定几何前提位的显式 k0（mtc2_mix_step_calc 同构） *)

Definition cfc_mixing_step_sel (budget : Real) (k0 : nat)
  (HB : lt zero budget)
  (Hgeo : le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
             (mult cf2_inv_two budget)) : nat :=
  projT1 (cf2_mixing_time_le budget k0 HB Hgeo).

Theorem cfc_mixing_step_sel_correct : forall (budget : Real) (k0 : nat)
  (HB : lt zero budget)
  (Hgeo : le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
             (mult cf2_inv_two budget)),
  lt (cf2_tv (cf2_titer (cfc_mixing_step_sel budget k0 HB Hgeo) cf2_mu0)
             (cf2_titer (cfc_mixing_step_sel budget k0 HB Hgeo) cf2_nu0))
     budget.
Proof.
  intros budget k0 HB Hgeo.
  exact (projT2 (cf2_mixing_time_le budget k0 HB Hgeo)).
Qed.

(* sigT 合并（TV 面）：混合时间模量见证型（witness=双投影读数、proof=正确性） *)
Theorem cfc_mixing_modulus_sigT : forall (budget : Real) (k0 : nat)
  (HB : lt zero budget)
  (Hgeo : le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
             (mult cf2_inv_two budget)),
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 HB Hgeo.
  exists (cfc_mixing_step_sel budget k0 HB Hgeo).
  exact (cfc_mixing_step_sel_correct budget k0 HB Hgeo).
Defined.

(* ============================================================ *)
(* 审计口：公理面（全 Closed 预期）＋可提取强证（照系列模板模式）        *)
(* ============================================================ *)

Print Assumptions cfc_k_enum_correct.
Print Assumptions cfc_k_enum_logface.
Print Assumptions cfc_fuel_sufficient_half.
Print Assumptions cfc_fuel_sufficient_qbound.
Print Assumptions cfc_enum_real_correct.
Print Assumptions cfc_req_r_pow_pos.
Print Assumptions cfc_req_r_pow_le_mono.
Print Assumptions cfc_rate_pos.
Print Assumptions cfc_k0_feeds_mixing.
Print Assumptions cfc_mixing_step_sel_correct.
Print Assumptions cfc_mixing_modulus_sigT.

(* 提取口：nat 面计算器五件（真 Fixpoint，无桩无截断） *)
Separate Extraction cfc_ceil_div cfc_iter cfc_pow_iter cfc_k_enum cfc_k0_select.
