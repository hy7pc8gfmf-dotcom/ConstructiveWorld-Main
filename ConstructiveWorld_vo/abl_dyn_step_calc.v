(* ==========================================================================)
   abl_dyn_step_calc.v — BQ·熵梯度 dynamics 收敛的步数计算器首件（dsc_ 前缀）
   卷次: ConstructiveWorld BQ 卷（tmine04，45 分钟切片，born-green 交付）
   使命: 按 K 头号矿脉 K1/K14——把 S04:1128 dynamics_converges 的纯定性收敛
     (ExistsT lim) 升级为 mtg_k_calc 式可提取步数见证；率材料照 K 勘定取自
     亲兄弟件 S04:893 iterate_cauchy_explicit_N 的 log 模量方程
     (log(a·κ^N) ≤ log eps，a := |η|·|g(x₀)|·1/(1−κ))。
   件名与前缀: abl_dyn_step_calc.v，dsc_ 前缀（施工前 grep 防撞：全库零命中）。
   五件陈述（本片闭合）:
     1. dsc_step_calc —— mtg_k_calc 同构 Defined 计算器：projT1(iterate_cauchy_
        explicit_N)，精度 eps → 步数 nat（K14 升格面）。
     2. dsc_step_calc_log_budget / dsc_step_calc_cauchy_correct —— 正确性两半：
        log 模量方程半（le (log(a·κ^N)) (log eps)）＋柯西半（∀m,n≥N, metric<eps），
        全 Set 形陈述。
     3. dsc_cauchy_modulus_sigT —— sigT 封装 {N | ∀m,n≥N, metric(x_m,x_n)<eps}。
     4. dsc_limit_rate_witness —— K1 组合器（lim＋cauchy ⟹ 到极限的率见证）：
        sigT N, ∀n≥N, metric(x_n, E_star) < eps，使用 lim_metric_approx 证书
        （K1 勘定的「lim＋cauchy ⟹ 到极限距离受率闭合」surfacing 面）。
     5. Part 2 nat 面：log 模量方程的定点枚举解算器 dsc_k_enum（真 Fixpoint/
        ceil 形：dsc_ceil_div=⌈·/·⌉，dsc_iter=x·p/q 上取整衰减步）＋两正确性
        （dsc_k_enum_correct 上取整面 / dsc_k_enum_logface 精确面=x·p^N≤e·q^N，
        即 log 模量方程的 nat 形）；Part 3 实面桥 dsc_nat_le_embed＋幂定律
        （dsc_r_pow_mult/dsc_nat_r_pow/dsc_r_pow_inv/dsc_inv_unique）＋
        dsc_enum_real_correct（定点档计算器在具体有理数据上的实面 le 正确性）。
   fail-loud 记录: 实数 log→nat ceil 的构造性桥不在库（r_arch_pow 为 Variable、
     库无 r_pow_mult/nat 单调桥——本件已补 nat_to_R 同态使用面），故按任务指令
     降档「有界精度档」：nat 计算器以定点枚举承载（真 Fixpoint，提取 Obj.magic
     =0），实面由 dsc_enum_real_correct 以有理数据 κ:=p/q 闭合；S04 的
     iterate_cauchy_explicit_N 之 N 走 r_arch_pow 证书（非计算性），以诚实
     边界登记于 attn 报告。
   依赖: S01_BaseRing–S04_RealExpLogConv（iterate_cauchy_explicit_N/
     one_minus_kappa_pos/r_pow_pos/lt_id_r/le_id_l/le_id_r/lt_le_iff/
     le_plus_compat/half_pos/half_twice/two_pos/one_pos 均在役）；Arch_PA_02
     （nat_to_R/nat_to_R_mult_hom）；Stdlib Arith/Lia。Require-only 零改动。
   构造性: 纯构造性/Set 层零 Prop 载体（步数见证 nat 面 sigT；误差谓词 real_lt/
     real_le Set 层）；非平凡（dsc_k_enum 为真 Fixpoint，ceil 枚举非平凡归纳）；
     可提取（Separate Extraction Obj.magic=0 附加证，照 BF 模式）；零公理
     （尾 Print Assumptions 全 Closed 预期）。
   工艺红线: 零 not/~/<> 书写；Qeq 面（本件 nat 面不用 Q，零 Qeq 坑）；term-
     mode 全显式实参（BN 坑卡）；数值定装（BB 坑卡：Eval 烟测入日志）。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532 && nice -19 rocq c -native-compiler no
     -Q vo_local_world_unified_0930 "" abl_dyn_step_calc.v（池内执行）。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：log 模量方程的 nat 定点枚举解算器（真 Fixpoint/ceil 形）    *)
(*   模量方程 log(a·κ^N) ≤ log eps 的 nat 面：以 κ=p/q（0<p<q）、      *)
(*   初值 a=A、预算 eps=E 的公共尺度定点表示，枚举最小 N 使            *)
(*   A·p^N ≤ E·q^N。枚举器用上取整衰减步（ceil 除法保上界方向）。      *)
(* ============================================================ *)

(* ceil 整除：⌈a/q⌉ := (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition dsc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma dsc_ceil_div_le : forall a q, (0 < q)%nat -> (a <= dsc_ceil_div a q * q)%nat.
Proof.
  intros a q Hq. unfold dsc_ceil_div.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq)) as Hmb.
  lia.
Qed.

(* 衰减步：x ↦ ⌈x·p/q⌉（κ=p/q 的定点乘步） *)
Definition dsc_iter (p q x : nat) : nat := dsc_ceil_div (x * p) q.

Lemma dsc_iter_step_bound : forall p q x, (0 < q)%nat ->
  (x * p <= dsc_iter p q x * q)%nat.
Proof.
  intros p q x Hq. unfold dsc_iter. apply (dsc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：dsc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint dsc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => dsc_iter p q (dsc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 == 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma dsc_pow_iter_comm : forall p q x k,
  dsc_pow_iter p q (dsc_iter p q x) k = dsc_iter p q (dsc_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x ≤ e 即停（返回已走步数），否则走衰减步再搜 *)
Fixpoint dsc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (dsc_k_enum f p q (dsc_iter p q x) e)
  end.

(* 正确性（上取整面）：燃料内可达 ⟹ 枚举返回的 N 步处上取整值 ≤ e *)
Theorem dsc_k_enum_correct : forall fuel p q x e,
  (exists k : nat, (k <= fuel)%nat /\ (dsc_pow_iter p q x k <= e)%nat) ->
  (dsc_pow_iter p q x (dsc_k_enum fuel p q x e) <= e)%nat.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e [k [Hk Hbound]].
  - assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.leb x e) eqn:Hle.
    + simpl. exact (proj1 (Nat.leb_le x e) Hle).
    + assert (Hgt : (e < x)%nat) by (apply (proj1 (Nat.leb_gt x e)); exact Hle).
      destruct k as [| k'].
      * simpl in Hbound. lia.
      * simpl in Hbound.
        rewrite <- (dsc_pow_iter_comm p q x k') in Hbound.
        assert (Hexists' : (exists k0 : nat,
                            (k0 <= f)%nat /\
                            (dsc_pow_iter p q (dsc_iter p q x) k0 <= e)%nat)).
        { exists k'. split.
          - lia.
          - exact Hbound. }
        specialize (IH p q (dsc_iter p q x) e Hexists').
        simpl.
        rewrite <- (dsc_pow_iter_comm p q x (dsc_k_enum f p q (dsc_iter p q x) e)).
        exact IH.
Qed.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma dsc_pow_iter_exact_ge : forall p q x k, (0 < p)%nat -> (0 < q)%nat ->
  (x * p ^ k <= dsc_pow_iter p q x k * q ^ k)%nat.
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - simpl. lia.
  - simpl.
    pose proof (dsc_iter_step_bound p q (dsc_pow_iter p q x k) Hq) as Hstep.
    apply (Nat.le_trans _ (dsc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH.
    + rewrite <- (Nat.mul_assoc (dsc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (dsc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (dsc_iter p q (dsc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep.
      * rewrite (Nat.mul_assoc (dsc_iter p q (dsc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* log 模量方程的 nat 形：枚举终止 ⟹ x·p^N ≤ e·q^N（log 单调下的等价面） *)
Theorem dsc_k_enum_logface : forall fuel p q x e,
  (0 < p)%nat -> (0 < q)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (dsc_pow_iter p q x k <= e)%nat) ->
  (x * p ^ dsc_k_enum fuel p q x e <= e * q ^ dsc_k_enum fuel p q x e)%nat.
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (dsc_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (dsc_pow_iter_exact_ge p q x (dsc_k_enum fuel p q x e) Hp Hq) as H2.
  apply (Nat.le_trans _
           (dsc_pow_iter p q x (dsc_k_enum fuel p q x e)
              * q ^ dsc_k_enum fuel p q x e)).
  - exact H2.
  - apply (Nat.mul_le_mono_r _ _ (q ^ dsc_k_enum fuel p q x e)). exact H1.
Qed.

(* 定点档烟测（BB 数值定装）：κ=7/10、A=1000、E=10 的衰减枚举，日志面证据 *)
Eval vm_compute in (dsc_k_enum 50 7 10 1000 10).

(* ============================================================ *)
(* Part 1 + Part 3：实面（RI 泛型 Section，S04 ConvergenceCauchy      *)
(* 证书子集对应形）——mtg_k_calc 同构计算器＋K1 组合器＋实面桥。          *)
(* ============================================================ *)

Section DscDynStepCalc.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段（S04 ConvergenceCauchy 同构） *)
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
Let lim := @lim RI.
Let metric := @metric RI.

(* 诚实接口证书（S04:308-839 在役 Variable 子集，签名经检验实拍对齐） *)
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable metric_abs : forall a b : R, Id (metric a b) (abs (minus a b)).
Variable kappa : R.
Variable kappa_pos : lt zero kappa.
Variable kappa_lt_one : lt kappa one.
Variable gradient_abs_decay : forall (E_A : R) (n : nat),
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult kappa (abs (entropy_gradient (iterate dynamics n E_A)))).
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable r_arch_pow : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps).
Variable eta_abs_pos : lt zero (abs eta).
Variable log_lt_mono_cc : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b).

(* ===== Part 1：mtg_k_calc 同构——Defined 步数计算器（K14 升格面） ===== *)

Definition dsc_step_calc (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
            dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
            gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
            log_lt_mono_cc E_A Hg0 eps Heps).

(* 正确性半 1：log 模量方程 log(a·κ^N) ≤ log eps（N := 计算器读数） *)
Theorem dsc_step_calc_log_budget : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps),
  le (log (mult
        (mult (mult (abs eta)
                    (abs (entropy_gradient (iterate dynamics 0 E_A))))
              (inv_pos (minus one kappa)
                       (one_minus_kappa_pos kappa kappa_lt_one lt_plus_compat_lt_le)))
        (r_pow kappa (dsc_step_calc E_A Hg0 eps Heps))))
     (log eps).
Proof.
  intros E_A Hg0 eps Heps.
  exact (fst (@projT2 _ _
          (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
             dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
             gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
             log_lt_mono_cc E_A Hg0 eps Heps))).
Qed.

(* 正确性半 2：柯西面——∀m,n ≥ N, metric(x_m,x_n) < eps（Set 形） *)
Theorem dsc_step_calc_cauchy_correct : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps) (m n : nat),
  (dsc_step_calc E_A Hg0 eps Heps <= m)%nat ->
  (dsc_step_calc E_A Hg0 eps Heps <= n)%nat ->
  lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps.
Proof.
  intros E_A Hg0 eps Heps m n Hm Hn.
  exact (snd (@projT2 _ _
          (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
             dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
             gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
             log_lt_mono_cc E_A Hg0 eps Heps)) m n Hm Hn).
Qed.

(* sigT 封装：{N | ∀m,n ≥ N, metric(x_m,x_n) < eps} *)
Theorem dsc_cauchy_modulus_sigT : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps),
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
        lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps).
Proof.
  intros E_A Hg0 eps Heps.
  exists (dsc_step_calc E_A Hg0 eps Heps).
  exact (dsc_step_calc_cauchy_correct E_A Hg0 eps Heps).
Defined.

(* ===== K1 组合器：lim＋cauchy ⟹ 到极限的率见证（surfacing 面） ===== *)

Theorem dsc_limit_rate_witness : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (E_star : R)
  (Hlim : lim (fun n => iterate dynamics n E_A) E_star)
  (Happrox : forall eps : R, lt zero eps ->
              sigT (fun N : nat => forall n : nat, NatLe N n ->
                    lt (metric (iterate dynamics n E_A) E_star) eps))
  (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
        lt (metric (iterate dynamics n E_A) E_star) eps).
Proof.
  intros E_A Hg0 E_star Hlim Happrox eps Heps.
  pose (eps2 := mult (inv_pos (plus one one) two_pos) eps).
  assert (Heps2 : lt zero eps2) by exact (half_pos eps Heps).
  destruct (Happrox eps2 Heps2) as [N1 HN1].
  destruct (dsc_cauchy_modulus_sigT E_A Hg0 eps2 Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  assert (Hn2n : (N2 <= n)%nat) by lia.
  apply (lt_id_r _ (plus eps2 eps2) eps (half_twice eps)).
  apply (le_lt_trans _
           (plus (metric (iterate dynamics n E_A)
                          (iterate dynamics (Nat.max N1 N2) E_A))
                 (metric (iterate dynamics (Nat.max N1 N2) E_A) E_star))).
  - exact (metric_triangle (iterate dynamics n E_A)
             (iterate dynamics (Nat.max N1 N2) E_A) E_star).
  - exact (lt_plus_compat _ _ _ _
              (HN2 n (Nat.max N1 N2) Hn2n (Nat.le_max_r N1 N2))
              (HN1 (Nat.max N1 N2)
                 (natle_of_le N1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)))).
Defined.

(* ===== Part 3：实面桥——定点档计算器的有理数据实面正确性 ===== *)

(* 左单位律补桥（Id 面一跳） *)
Lemma dsc_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Qed.

(* 逆元唯一性：y·z == 1 ⟹ z == inv y *)
Lemma dsc_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (dsc_mult_one_l (inv_pos y Hy))))))).
Qed.

(* 幂对乘法的分裂：r_pow(a·b,n) == r_pow(a,n)·r_pow(b,n)（库缺，本件补；
   注：库内 Id 面 rewrite 匹配不可靠（mult_one 检验实锤），全链 term-mode） *)
Lemma dsc_r_pow_mult : forall (a b : R) (n : nat),
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
Lemma dsc_nat_r_pow : forall k n : nat,
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
Lemma dsc_r_pow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (dsc_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (dsc_inv_unique (mult x (r_pow x n))
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

(* nat ≤ → 实面 le 嵌入单调桥（库缺，本件补）。
   消除纪律：nat ≤ 是 Prop 归纳、不得消入 Set 目标——走 Set 层 nat 归纳
   （加法辅助件）＋Nat.leb 判定＋Nat.sub_add 差值提取，零 Prop 消除。） *)
Lemma dsc_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
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

Lemma dsc_nat_le_embed : forall m n : nat, (m <= n)%nat -> le (nat_to_R m) (nat_to_R n).
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
      apply (dsc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* 定点档主件：有理数据 κ:=p/q、a:=A、eps:=E 上，枚举 N 的实面正确性（le 形）。
   即：nat 计算器读数 N 满足 a·κ^N ≤ eps 的实面（Set 形陈述，
   dsc_step_calc 系的无证书版对偶——log 模量方程的解算器面）。 *)
Theorem dsc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  (0 < p)%nat -> (0 < q)%nat -> (0 < A)%nat -> (0 < E)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (dsc_pow_iter p q A k <= E)%nat) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (dsc_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq HA HE Hterm.
  set (N := dsc_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (dsc_k_enum_logface fuel p q A E Hp Hq Hterm) as Hlog.
  pose proof (dsc_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
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
  { pose proof (dsc_r_pow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
    pose proof (dsc_nat_r_pow p N) as Hpo.
    pose proof (dsc_r_pow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
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
                                     (id_sym (dsc_nat_r_pow q N)))
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

End DscDynStepCalc.

(* ============================================================ *)
(* G4 审计口：公理面（全 Closed 预期）＋可提取强证（照 BF 模式）         *)
(* ============================================================ *)

Print Assumptions dsc_step_calc_log_budget.
Print Assumptions dsc_step_calc_cauchy_correct.
Print Assumptions dsc_cauchy_modulus_sigT.
Print Assumptions dsc_limit_rate_witness.
Print Assumptions dsc_k_enum_correct.
Print Assumptions dsc_k_enum_logface.
Print Assumptions dsc_enum_real_correct.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction dsc_ceil_div dsc_iter dsc_pow_iter dsc_k_enum.
