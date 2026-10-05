(* ==========================================================================)
   abl_attn_step_calc.v — AttnDoeblin 收缩面的步数见证件（asc_ 前缀）
   使命：把 AttnDoeblin.v 收缩收敛面的纯率性陈述升级为 mtg_k_calc 式可提取步数见证。率材料：
      bs_minorization（现档 :693，δ-star := lo·lo = e^{−2Δ/T}）＋相邻收缩迭代件 bounded_softmax_tv_iter
      （:751，率 (1−δ)ⁿ 显式在案，δ 即 delta_star）。
   五件主陈述：①asc_step_calc——mtg_k_calc 同构 Defined 计算器：初值 TV₀ 精度 eps → 步数 nat（omd_arch 证书）。
      ②asc_step_calc_budget／asc_step_calc_correct——正确性两半：预算半 lt (TV₀·omd^N) eps＋TV 迭代半
      ∀n≥N tv(iterⁿ) < eps（omd := 1−δ；u_tv_iter 闭包＋r_pow_dec_iter 幂单调桥；delta_pos 供 n≥N 单调支）。
      ③asc_mixing_modulus_sigT——混合模量 {N | ∀n≥N ∀mu nu, ...< eps} 的 sigT 居住（Defined）。
      ④asc_k_enum——nat 定点枚举解算器（真 Fixpoint，Nat.ltb「首次跌破」严格停机；strict_correct／ltface
      两正确性＝x·p^N < e·q^N 严格 nat 形）。⑤Part 3 实面桥：幂定律 4 件＋asc_nat_le_embed＋
      asc_enum_real_correct＋asc_omd_enum_budget（omd == p/q 读数满足实面 le (A·omd^N) E）。
   已知边界：库内 log→nat ceil 构造性桥仍缺——nat 计算器以定点枚举承载（提取 Obj.magic=0）；实形严格档
      依赖「单侧严格平移」（库内唯 fa53/fa57 供给且需 DecidableOrder 证书）；本件 lt 形经 omd_arch 证书承载，
      Part 3 计算器读数为 le 形（S04 r_arch_pow／S06 r_arch_pow_attn 在役模式同款）。
   依赖清单：S01_BaseRing–S04_RealExpLogConv（le_mult_compat/_r、lt_mult_compat、le/lt_id_l/_r、
      le_lt_trans/lt_le_trans、le_plus_compat、plus_assoc/comm/zero/opp、opp_plus/plus_opp）；AttnDoeblin
      （u_tv_iter/u_titer 闭包——Require 不 Import，防其 AlgHelpers 局部 nat_to_R 遮蔽 S04 同名件）；
      Arch_PA_02（nat_to_R_mult_hom）；S06_DiffSamplingGibbs（tv_dist 限定名）；Stdlib Arith/Lia。
   构造性注记：纯构造性/Set 层零 Prop 语句面（步数见证 nat 面 sigT；误差谓词 le/lt Set 层）；非平凡
      （asc_k_enum 为真 Fixpoint）；可提取（Separate Extraction Obj.magic=0 附加证）；零公理（尾 Print
      Assumptions 全 Closed 预期）。工艺红线：零 not/~/<> 书写；term-mode 全显式实参；Eval 烟测定装；
      Id 代数全走 term-mode id_trans 链；nat≤/nat< Prop 不消入 Set（Nat.leb/Nat.ltb＋destruct＋lia replace）。
   编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q vo_local_world_unified_0930 "" abl_attn_step_calc.v（池内执行）；验证＝
      EXIT=0＋Print Assumptions 全 Closed。
   查重登记：顶层名全 asc_ 新前缀，防撞在册编译树 vo_local_world_unified_0930 零命中；在册外同前缀为
      Q 层平方/abs 件，本件件名集与其零交。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
Require AttnDoeblin.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：几何衰减的 nat 定点枚举解算器（真 Fixpoint/严格档）        *)
(*   收缩率 omd := 1−δ 以 κ := p/q（0<p<q）、初值 A、预算 E 的公共    *)
(*   尺度定点表示，枚举首次跌破（x < e 严格停机）的步数。              *)
(*   严格档（Nat.ltb 停机面）——le 档之升级。                          *)
(* ============================================================ *)

(* ceil 整除：⌈a/q⌉ := (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition asc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma asc_ceil_div_le : forall a q, (0 < q)%nat -> (a <= asc_ceil_div a q * q)%nat.
Proof.
  intros a q Hq. unfold asc_ceil_div.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq)) as Hmb.
  lia.
Qed.

(* 衰减步：x ↦ ⌈x·p/q⌉（κ=p/q 的定点乘步） *)
Definition asc_iter (p q x : nat) : nat := asc_ceil_div (x * p) q.

Lemma asc_iter_step_bound : forall p q x, (0 < q)%nat ->
  (x * p <= asc_iter p q x * q)%nat.
Proof.
  intros p q x Hq. unfold asc_iter. apply (asc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：asc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint asc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => asc_iter p q (asc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 == 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma asc_pow_iter_comm : forall p q x k,
  asc_pow_iter p q (asc_iter p q x) k = asc_iter p q (asc_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x < e 即停（严格档首破停机），否则走衰减步再搜 *)
Fixpoint asc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (asc_k_enum f p q (asc_iter p q x) e)
  end.

(* 正确性（严格面）：燃料内可达 ⟹ 枚举返回的 N 步处上取整值 < e *)
Theorem asc_k_enum_strict_correct : forall fuel p q x e,
  (exists k : nat, (k <= fuel)%nat /\ (asc_pow_iter p q x k < e)%nat) ->
  (asc_pow_iter p q x (asc_k_enum fuel p q x e) < e)%nat.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e [k [Hk Hbound]].
  - assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl. exact (proj1 (Nat.ltb_lt x e) Hlt).
    + assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      destruct k as [| k'].
      * simpl in Hbound. lia.
      * simpl in Hbound.
        rewrite <- (asc_pow_iter_comm p q x k') in Hbound.
        assert (Hexists' : (exists k0 : nat,
                            (k0 <= f)%nat /\
                            (asc_pow_iter p q (asc_iter p q x) k0 < e)%nat)).
        { exists k'. split.
          - lia.
          - exact Hbound. }
        specialize (IH p q (asc_iter p q x) e Hexists').
        simpl.
        rewrite <- (asc_pow_iter_comm p q x (asc_k_enum f p q (asc_iter p q x) e)).
        exact IH.
Qed.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma asc_pow_iter_exact_ge : forall p q x k, (0 < p)%nat -> (0 < q)%nat ->
  (x * p ^ k <= asc_pow_iter p q x k * q ^ k)%nat.
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - simpl. lia.
  - simpl.
    pose proof (asc_iter_step_bound p q (asc_pow_iter p q x k) Hq) as Hstep.
    apply (Nat.le_trans _ (asc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH.
    + rewrite <- (Nat.mul_assoc (asc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (asc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (asc_iter p q (asc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep.
      * rewrite (Nat.mul_assoc (asc_iter p q (asc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* q^k 正性（nat 面） *)
Lemma asc_pow_pos : forall q k, (0 < q)%nat -> (0 < q ^ k)%nat.
Proof.
  intros q k Hq. induction k as [| k IH].
  - simpl. lia.
  - simpl.
    assert (H1q : (1 <= q)%nat) by lia.
    assert (H1k : (1 <= q ^ k)%nat) by lia.
    pose proof (Nat.mul_le_mono _ _ _ _ H1q H1k) as Hm.
    simpl in Hm. lia.
Qed.

(* log 模量方程的严格 nat 形：枚举终止 ⟹ x·p^N < e·q^N（log 单调下等价面；
   本件严格升级） *)
Theorem asc_k_enum_ltface : forall fuel p q x e,
  (0 < p)%nat -> (0 < q)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (asc_pow_iter p q x k < e)%nat) ->
  (x * p ^ asc_k_enum fuel p q x e < e * q ^ asc_k_enum fuel p q x e)%nat.
Proof.
  intros fuel p q x e Hp Hq Hterm.
  set (N := asc_k_enum fuel p q x e).
  pose proof (asc_k_enum_strict_correct fuel p q x e Hterm) as H1.
  pose proof (asc_pow_iter_exact_ge p q x N Hp Hq) as H2.
  pose proof (asc_pow_pos q N Hq) as HqN.
  apply (Nat.le_lt_trans _ (asc_pow_iter p q x N * q ^ N) _).
  - exact H2.
  - exact (proj1 (Nat.mul_lt_mono_pos_r (q ^ N) (asc_pow_iter p q x N) e HqN) H1).
Qed.

(* 定点档烟测：κ=7/10、A=1000、E=10 的严格档首破枚举 *)
Eval vm_compute in (asc_k_enum 50 7 10 1000 10).

(* ============================================================ *)
(* Part 1 + Part 3：实面（RI 泛型 Section，AttnDoeblin UContraction    *)
(* 证书子集逐形对应）——mtg_k_calc 同构计算器＋混合模量＋实面桥。       *)
(* ============================================================ *)

Section AscAttnStepCalc.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 解包 RealInterface 字段（BQ 同款） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let minus := @minus RI.
Let S := @S RI SS.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @S06_DiffSamplingGibbs.tv_dist RI SS SO.

(* 诚实接口证书（AttnDoeblin UContraction u_tv_iter 证书子集逐形对应，
   签名经 @u_tv_iter 直接对齐；transition_nonneg 被闭包裁剪故不携带） *)
Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable delta_pos : lt zero delta.
Variable transition : S -> S -> R.
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* 均匀迭代（AttnDoeblin u_titer 闭包，transition 实参化） *)
Let asc_titer (n : nat) (mu : S -> R) : S -> R :=
  @AttnDoeblin.u_titer RI SS SO transition n mu.

(* 几何击破证书（S06 r_arch_pow_attn 同款：Real 层阿基米德面） *)
Variable omd_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (r_pow (minus one delta) N)) eps).

Let omd := minus one delta.

(* 1−δ > 0（AttnDoeblin u_omd_pos_next 同款） *)
Lemma asc_omd_pos : lt zero omd.
Proof.
  unfold omd, minus.
  apply (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta))
                 (id_sym (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Qed.

(* 1−δ < 1（δ > 0 供能；乘法单调走 lt_plus_compat_lt_le_h 混合支——
   u_omd_pos_next 同款技法；吸收律 Id 面走 S01 assoc/comm/opp 运河，
   不用 fa57 严格平移，免 DecidableOrder 证书） *)
Lemma asc_omd_lt_one : lt omd one.
Proof.
  assert (Habsorb : Id (plus delta omd) one).
  { unfold omd, minus.
    exact (id_trans (plus_assoc delta one (opp delta))
           (id_trans (id_cong (fun w => plus w (opp delta)) (plus_comm delta one))
           (id_trans (id_sym (plus_assoc one delta (opp delta)))
           (id_trans (id_cong (fun w => plus one w) (plus_opp delta))
                     (plus_zero one))))). }
  apply (lt_id_r omd (plus delta omd) one Habsorb).
  exact (lt_id_l omd (plus zero omd) (plus delta omd)
                 (id_trans (id_sym (plus_zero omd)) (plus_comm omd zero))
                 (lt_plus_compat_lt_le_h zero delta omd omd delta_pos
                                         (le_refl omd))).
Qed.

(* ===== Part 1：mtg_k_calc 同构——Defined 步数计算器（K8 升格面） ===== *)

Definition asc_step_calc (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (omd_arch TV0 HTV0 eps Heps).

(* 正确性半 1：几何率预算面（N := 计算器读数） *)
Theorem asc_step_calc_budget : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps),
  lt (mult TV0 (r_pow omd (asc_step_calc TV0 HTV0 eps Heps))) eps.
Proof.
  intros TV0 HTV0 eps Heps.
  exact (projT2 (omd_arch TV0 HTV0 eps Heps)).
Qed.

(* 正确性半 2：TV 迭代面——∀n≥N、∀归一化对 mu nu：tv(mu,nu) ≤ TV₀ ⟹
   tv(iterⁿ) < eps（使用 AttnDoeblin u_tv_iter＋r_pow_dec_iter 单调桥；
   乘法单调走 le_mult_compat 因右字段——同款形） *)
Theorem asc_step_calc_correct : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps)
  (mu nu : S -> R) (Hmu : Id (sum_over_S mu) one) (Hnu : Id (sum_over_S nu) one)
  (HTV : le (tv mu nu) TV0) (n : nat),
  (asc_step_calc TV0 HTV0 eps Heps <= n)%nat ->
  lt (tv (asc_titer n mu) (asc_titer n nu)) eps.
Proof.
  intros TV0 HTV0 eps Heps mu nu Hmu Hnu HTV n Hn.
  pose proof (@AttnDoeblin.u_tv_iter RI SS SO u u_norm delta delta_lt_one transition
              transition_row minorization sum_swap_cc abs_ge_zero_id_cc
              lt_plus_compat_lt_le_h n mu nu Hmu Hnu) as Hdec.
  pose proof (@r_pow_dec_iter RI omd asc_omd_pos asc_omd_lt_one
              (asc_step_calc TV0 HTV0 eps Heps) n Hn) as Hmono.
  pose proof (asc_step_calc_budget TV0 HTV0 eps Heps) as Hbud0.
  pose proof (lt_id_l (mult (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)
                      (mult TV0 (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)))
                      eps
                      (mult_comm (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)
                      Hbud0) as Hbud.
  apply (le_lt_trans _ (mult (r_pow omd n) TV0)).
  - apply (le_trans _ (mult (r_pow omd n) (tv mu nu))).
    + exact Hdec.
    + exact (le_mult_compat_r (r_pow omd n) (tv mu nu) TV0
               (lt_le_iff zero (r_pow omd n)
                  (inl (r_pow_pos omd n asc_omd_pos))) HTV).
  - apply (le_lt_trans _ (mult (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)).
    + exact (le_mult_compat (r_pow omd n)
                            (r_pow omd (asc_step_calc TV0 HTV0 eps Heps))
                            TV0 HTV0 Hmono).
    + exact Hbud.
Qed.

(* sigT 封装：混合时间模量 {N | ∀n≥N ∀归一化对, tv(iterⁿ) < eps}（Defined） *)
Theorem asc_mixing_modulus_sigT : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps),
  sigT (fun N : nat => forall (mu nu : S -> R),
        Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
        le (tv mu nu) TV0 ->
        forall n : nat, (N <= n)%nat ->
        lt (tv (asc_titer n mu) (asc_titer n nu)) eps).
Proof.
  intros TV0 HTV0 eps Heps.
  exists (asc_step_calc TV0 HTV0 eps Heps).
  exact (asc_step_calc_correct TV0 HTV0 eps Heps).
Defined.

(* ===== Part 3：实面桥——定点档计算器的有理数据实面正确性 ===== *)

(* 左单位律补桥（Id 面一跳） *)
Lemma asc_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Qed.

(* 逆元唯一性：y·z == 1 ⟹ z == inv y *)
Lemma asc_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (asc_mult_one_l (inv_pos y Hy))))))).
Qed.

(* 幂对乘法的分裂：r_pow(a·b,n) == r_pow(a,n)·r_pow(b,n)（库缺，沿 BQ 补） *)
Lemma asc_r_pow_mult : forall (a b : R) (n : nat),
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
             (id_trans (id_cong (fun t => mult a t)
                                (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Qed.

(* nat_to_R 与幂交换：r_pow(nat_to_R k,n) == nat_to_R(k^n)（乘法同态归纳） *)
Lemma asc_nat_r_pow : forall k n : nat,
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
Lemma asc_r_pow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (asc_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (asc_inv_unique (mult x (r_pow x n))
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

(* nat ≤ → 实面 le 嵌入单调桥（库缺，沿 BQ 补）。
   消除纪律：nat ≤ 是 Prop 归纳、不得消入 Set 目标——走 Set 层 nat 归纳
   （加法辅助件）＋Nat.leb 判定＋Nat.sub_add 差值提取，零 Prop 消除。） *)
Lemma asc_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
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

Lemma asc_nat_le_embed : forall m n : nat, (m <= n)%nat -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. destruct (Nat.leb n m) eqn:E.
  - assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact (proj1 (Nat.leb_le n m) E).
      - exact Hmn. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (asc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* 几何装配 Id 面（BQ H3 的 HL/HR 因式化）：
   LHS：A·(p/q)^N == (A·p^N)·q^{-N} *)
Lemma asc_geom_lhs_id : forall (A p q : nat) (Hqr : lt zero (nat_to_R q)) (N : nat),
  Id (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
     (mult (mult (nat_to_R A) (nat_to_R (p ^ N)))
           (inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr))).
Proof.
  intros A p q Hqr N.
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (asc_r_pow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
  pose proof (asc_nat_r_pow p N) as Hpo.
  pose proof (asc_r_pow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
  assert (Hs2 : Id (mult (r_pow (nat_to_R p) N)
                         (r_pow (inv_pos (nat_to_R q) Hqr) N))
                   (mult (nat_to_R (p ^ N)) w)).
  { apply (id_trans
             (id_cong (fun u => mult u (r_pow (inv_pos (nat_to_R q) Hqr) N)) Hpo)).
    exact (id_cong (fun u => mult (nat_to_R (p ^ N)) u) Hpi). }
  apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hpm)).
  apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hs2)).
  exact (mult_assoc (nat_to_R A) (nat_to_R (p ^ N)) w).
Qed.

(* 几何装配 Id 面：RHS：(E·q^N)·q^{-N} == E *)
Lemma asc_geom_rhs_id : forall (E q : nat) (Hqr : lt zero (nat_to_R q)) (N : nat),
  Id (mult (mult (nat_to_R E) (nat_to_R (q ^ N)))
           (inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)))
     (nat_to_R E).
Proof.
  intros E q Hqr N.
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  exact (id_trans
           (id_sym (mult_assoc (nat_to_R E) (nat_to_R (q ^ N)) w))
           (id_trans
              (id_cong (fun t => mult (nat_to_R E) t)
                       (id_trans
                          (id_cong (fun u => mult u w)
                                   (id_sym (asc_nat_r_pow q N)))
                          (inv_pos_correct (r_pow (nat_to_R q) N)
                                           (r_pow_pos (nat_to_R q) N Hqr))))
              (mult_one (nat_to_R E)))).
Qed.

(* 定点档主件 le 档：有理数据 κ:=p/q 上，严格档枚举读数 N 满足实面
   le (A·κ^N) E（Set 形陈述，asc_step_calc 系的无证书版对偶） *)
Theorem asc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  (0 < p)%nat -> (0 < q)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (asc_pow_iter p q A k < E)%nat) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (asc_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq Hterm.
  set (N := asc_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (asc_k_enum_ltface fuel p q A E Hp Hq Hterm) as Hltf.
  pose proof (Nat.lt_le_incl _ _ Hltf) as Hlog.
  pose proof (asc_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
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
                  (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)).
  { exact (le_mult_compat (mult (nat_to_R A) (nat_to_R (p ^ N)))
                          (mult (nat_to_R E) (nat_to_R (q ^ N))) w
                          (inv_pos_pos (r_pow (nat_to_R q) N)
                             (r_pow_pos (nat_to_R q) N Hqr))
                          Hsplit). }
  apply (le_id_l (mult (nat_to_R A)
                         (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                 (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (nat_to_R E)
                 (asc_geom_lhs_id A p q Hqr N)).
  apply (le_id_r (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)
                 (nat_to_R E)
                 (asc_geom_rhs_id E q Hqr N) H3).
Qed.

(* 定点档 omd 直连版 le 档：omd == p/q 证书下，枚举读数 N 满足
   实面 le (A·omd^N) E——K8 步数见证的实形（计算器读数直供率预算） *)
Theorem asc_omd_enum_budget : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  (0 < p)%nat -> (0 < q)%nat ->
  Id omd (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) ->
  (exists k : nat, (k <= fuel)%nat /\ (asc_pow_iter p q A k < E)%nat) ->
  le (mult (nat_to_R A) (r_pow omd (asc_k_enum fuel p q A E))) (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq Homd Hterm.
  apply (le_id_l (mult (nat_to_R A) (r_pow omd (asc_k_enum fuel p q A E)))
                 (mult (nat_to_R A)
                       (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                              (asc_k_enum fuel p q A E)))
                 (nat_to_R E)
                 (id_cong (fun t => mult (nat_to_R A) t)
                          (id_cong (fun t => r_pow t (asc_k_enum fuel p q A E))
                                   Homd))).
  exact (asc_enum_real_correct fuel p q A E Hqr Hp Hq Hterm).
Qed.

End AscAttnStepCalc.

(* ============================================================ *)
(* G4 审计口：公理面（全 Closed 预期）＋可提取强证（照 BF/BQ 模式）      *)
(* ============================================================ *)

Print Assumptions asc_step_calc_budget.
Print Assumptions asc_step_calc_correct.
Print Assumptions asc_mixing_modulus_sigT.
Print Assumptions asc_k_enum_strict_correct.
Print Assumptions asc_k_enum_ltface.
Print Assumptions asc_enum_real_correct.
Print Assumptions asc_omd_enum_budget.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction asc_ceil_div asc_iter asc_pow_iter asc_k_enum.
