(* ============================================================ *)
(* ToyR 玩具证替换件 ——   工程包AB（tier2 十八批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   rkd_kl_decomp_full_partition（原 L850，3 句玩具证）                  *)
(* ============================================================ *)

(* ============================================================
   UpAblEps49RKDBase.v —— 相对熵（KL）分解定理：自由能恒等式
   F(p) == F(p_b) + D·Σ kl_term(p, p_b)（Boltzmann 分布 p_b、
   温度 D、配分函数 Z、抽象求和泛函 Σ），
   及其定义 Z 形的无条件版本。
   ============================================================ *)
(* 使命：把 UpRealLeB.v Section RealRLHFLeB 与 S08_RealMainlineDPO.v  *)
(*   Section RealRLHFMain 中以节 Variable 引入的假设 real_kl_decomp_full *)
(*   证为定理（下游使用处 real_rlhf_optimal_B / real_rlhf_optimal_eps）。    *)
(*                                                               *)
(* 记号：F = real_free_energy（自由能）；p_b = real_boltzmann_dist_r      *)
(*   （Boltzmann 分布）；kl_term = real_kl_term（逐点 KL）；Σ = sumf       *)
(*   （抽象求和泛函）；D 为温度参量（正）；Z 为配分函数。                                *)
(*   ext/add/linear 为 sumf 的结构前提：逐点相等外延、和的加法分配、                  *)
(*   数乘分配。                                                       *)
(*                                                               *)
(* 命题形状：结论 real_eq (F p) (F p_b + D·Σ kl_term(p s, p_b s))，      *)
(*   前提 (Hp, Hnormp)。数学事实：F(p)−F(p_b)−D·Σ kl =                   *)
(*   D·logZ·(Σ p_b − 1)；当 Z 为任意正 Variable 时该语句为假                 *)
(*   （反例：单点态空间、e=0、D=1、Z=2 ⟹ 左端 0 而右端                            *)
(*   (1/2)·log 2）。故无条件形必须取定义 Z := Σ exp(−e/D)                    *)
(*   （归一化 Σ p_b == 1 内证）；一般 Z 形携带数学前提                            *)
(*   Hnormb（Σ p_b == 1）。                                         *)
(*                                                               *)
(* 两个主定理：rkd_kl_decomp_full（一般 Z + Hnormb 条件形，结论与假设              *)
(*   逐字同构）；rkd_kl_decomp_full_partition（定义 Z 形，前提 =              *)
(*   求和代数接口 ext/add/linear + 定义 Z 的正性证书，零残留数学前提）。                *)
(*                                                               *)
(* 参数对照（与假设参数序逐参核对）：                                             *)
(*   假设序：S sumf ext add [linear] base D Dp Z Zp ｜ p Hp Hnormp    *)
(*   主件1序：S sumf ext add linear base D Dp Z Zp ｜ p Hp Hnormp Hnormb *)
(*   ① linear 为证明所需最小增补（原假设为 Variable，无需证明）；                     *)
(*   ② Hnormb 为归一化前提（任意 Z 下不可免，见上反例）。                            *)
(*   应用方式：以主件1前九参部分应用替换 real_kl_decomp_full 参数位                  *)
(*   （留 p Hp Hnormp Hnormb 为剩余参数）；主件2 适用于 Z 取真                   *)
(*   配分函数的实例化。                                                   *)
(*                                                               *)
(* 内容：§1 代数基元（rkd_mult_opp_r、rkd_inv_absorb、                     *)
(*   rkd_eq_cancel_r）；§2 逐点 log 恒等式（rkd_log_pB）与 KL 项            *)
(*   展开（rkd_kl_point）；§3 求和层负元（rkd_sum_opp）；                     *)
(*   §4 能量期望恒等式（rkd_energy_horse）；§5 求和层 KL 分解                   *)
(*   （rkd_kl_sum_bridge）与 Boltzmann 归一化                          *)
(*   （rkd_boltzmann_normalized）；§6 主定理（rkd_kl_decomp_full、       *)
(*   rkd_kl_decomp_full_partition）。文末 Print Assumptions 依赖审计。    *)
(*                                                               *)
(* 证明资源：retm_log_inv_pos_gen（log(1/x) == −log x 一般形）+            *)
(*   CW219 的 real_log_mult / real_log_exp_neg / real_log_wd /    *)
(*   real_inv_pos_correct；其余步骤的证明在本件内完成。                         *)
(*                                                               *)
(* 证明纪律：Set 层零 Prop 泄露（real_eq/real_lt 全 Set 值，语句面               *)
(*   纯 forall 型）；纯构造性；real_eq 非 Id 禁改写，转换经                       *)
(*   real_eq_trans 与 RealSetoid compat/adapt 成对使用；原子代数走          *)
(*   rkd_alg（real_eq_of_zero_diff + proj 剥离 + ring），含            *)
(*   one/zero 字面与 log/inv 处改走具名引理；全 Qed 闭合。                      *)
(*                                                               *)
(* 依赖：CW_ConstructiveWorld_219、RealEnergyTempMono                *)
(*   （使用 retm_log_inv_pos_gen）、Stdlib QArith.Qring。              *)
(*                                                               *)
(* 对标：mathlib KL 散度与 Gibbs 分解恒等式（测度论版本）；                         *)
(*   本件为抽象求和泛函版本。                                                *)
(*                                                               *)
(* 构造性注记：零承认；全件 Set 层承载；可提取。                                     *)
(*                                                               *)
(* 编译配方：Rocq 9.1 直调 + cpu_guard（双核上限）；编译输出 -o                    *)
(*   临时目录，树内 .vo/.glob 不动。                                       *)
(* (* ============================================================ *) *)

From Stdlib Require Import QArith.Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import RealEnergyTempMono.

(* 原子项代数：加/乘/负/原子项上的 real_eq 一步 ring（同 retm_alg；                 *)
(*   限纯原子代数——含 one/zero 字面与 log/inv 处改走具名引理链）                    *)
Ltac rkd_alg :=
  apply real_eq_of_zero_diff; intro n;
  repeat first [ rewrite real_plus_proj | rewrite real_mult_proj | rewrite real_opp_proj ];
  ring.

(* ============================================================ *)
(* §1 代数基元：乘法负元、inv 吸收与右消去                                       *)
(* ============================================================ *)

(* (−1)·x == −x（comm + mult_opp_l + mult_one 三步具名链） *)
Lemma rkd_mult_opp_r : forall x : Real,
  real_eq (real_mult (real_opp real_one) x) (real_opp x).
Proof.
  intro x.
  apply (real_eq_trans
           (real_mult (real_opp real_one) x)
           (real_mult x (real_opp real_one))
           (real_opp x)).
  - exact (real_mult_comm (real_opp real_one) x).
  - apply (real_eq_trans
             (real_mult x (real_opp real_one))
             (real_opp (real_mult x real_one))
             (real_opp x)).
    + exact (real_mult_opp_l x real_one).
    + exact (RealSetoid.real_eq_opp_compat (real_mult x real_one) x (real_mult_one x)).
Qed.

(* inv 吸收：x·(inv x · y) == y（由 real_inv_pos_correct；Bishop 构造位不走 rkd_alg） *)
Lemma rkd_inv_absorb : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x (real_mult (real_inv_pos x Hx) y)) y.
Proof.
  intros x y Hx.
  apply (real_eq_trans
           (real_mult x (real_mult (real_inv_pos x Hx) y))
           (real_mult (real_mult x (real_inv_pos x Hx)) y)
           y).
  - exact (real_mult_assoc x (real_inv_pos x Hx) y).
  - apply (real_eq_trans
             (real_mult (real_mult x (real_inv_pos x Hx)) y)
             (real_mult real_one y)
             y).
    + exact (RealSetoid.real_eq_mult_compat_adapt
               (real_mult x (real_inv_pos x Hx)) real_one y y
               (real_inv_pos_correct x Hx) (real_eq_refl y)).
    + apply (real_eq_trans
               (real_mult real_one y)
               (real_mult y real_one)
               y).
      * exact (real_mult_comm real_one y).
      * exact (real_mult_one y).
Qed.

(* 右消去：a == b + c ⟹ b == a + (−c)（原子代数链） *)
Lemma rkd_eq_cancel_r : forall a b c : Real,
  real_eq a (real_plus b c) -> real_eq b (real_plus a (real_opp c)).
Proof.
  intros a b c H.
  apply (real_eq_trans b (real_plus b real_zero) (real_plus a (real_opp c))).
  - apply real_eq_sym. exact (real_plus_zero b).
  - apply (real_eq_trans
             (real_plus b real_zero)
             (real_plus b (real_plus c (real_opp c)))
             (real_plus a (real_opp c))).
    + exact (RealSetoid.real_eq_plus_compat_adapt b b real_zero
               (real_plus c (real_opp c))
               (real_eq_refl b)
               (real_eq_sym (real_plus c (real_opp c)) real_zero (real_plus_opp c))).
    + apply (real_eq_trans
               (real_plus b (real_plus c (real_opp c)))
               (real_plus (real_plus b c) (real_opp c))
               (real_plus a (real_opp c))).
      * exact (real_plus_assoc b c (real_opp c)).
      * exact (RealSetoid.real_eq_plus_compat_adapt (real_plus b c) a
                 (real_opp c) (real_opp c) (real_eq_sym _ _ H)
                 (real_eq_refl (real_opp c))).
Qed.

(* ============================================================ *)
(* §2 逐点 log 恒等式与 KL 项展开（无求和前提）                                  *)
(* ============================================================ *)

(* log p_b(s) == −(e(s)/D + log Z)（无前提直接证明；log(inv Z) 一步         *)
(*   使用 retm_log_inv_pos_gen）                                    *)
Lemma rkd_log_pB : forall (S : Type) (real_base_loss : S -> Real)
  (D : Real) (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z) (s : S)
  (Hpb : real_lt real_zero (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)),
  real_eq (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hpb)
          (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                               (real_log Z Z_pos))).
Proof.
  intros S real_base_loss D D_pos Z Z_pos s Hpb.
  set (Hcanon := real_mult_positive
                   (real_inv_pos Z Z_pos)
                   (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                   (real_inv_pos_pos Z Z_pos)
                   (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
  apply (real_eq_trans
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hpb)
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hcanon)
           (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z Z_pos)))).
  - exact (real_log_wd
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
             Hpb Hcanon
             (real_eq_refl (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s))).
  - apply (real_eq_trans
             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hcanon)
             (real_plus (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                        (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                  (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
             (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                  (real_log Z Z_pos)))).
    + exact (real_log_mult
               (real_inv_pos Z Z_pos)
               (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
               (real_inv_pos_pos Z Z_pos)
               (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                          (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                    (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_plus (real_opp (real_log Z Z_pos))
                          (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
               (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                    (real_log Z Z_pos)))).
      * exact (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                 (real_opp (real_log Z Z_pos))
                 (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                           (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                 (retm_log_inv_pos_gen Z Z_pos)
                 (real_log_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log Z Z_pos))
                            (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 (real_plus (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                            (real_opp (real_log Z Z_pos)))
                 (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                      (real_log Z Z_pos)))).
        -- exact (real_plus_comm (real_opp (real_log Z Z_pos))
                    (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
        -- apply real_eq_sym.
           exact (real_opp_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z Z_pos)).
Qed.

(* kl_term 逐点展开：real_kl_term p q == p·(log p − log q) *)
Lemma rkd_kl_point : forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq. unfold real_kl_term.
  assert (Hinner : real_eq
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  { apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    - exact (RealSetoid.real_eq_opp_compat
               (real_log (real_mult q (real_inv_pos p Hp))
                         (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
               (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
               (real_eq_trans
                  (real_log (real_mult q (real_inv_pos p Hp))
                            (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
                  (real_plus (real_log q Hq)
                             (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                  (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
                  (real_log_mult q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))
                  (RealSetoid.real_eq_plus_compat_adapt
                     (real_log q Hq) (real_log q Hq)
                     (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                     (real_opp (real_log p Hp))
                     (real_eq_refl (real_log q Hq))
                     (retm_log_inv_pos_gen p Hp)))).
    - apply (real_eq_trans
               (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      + exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
      + apply (real_eq_trans
                 (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
                 (real_plus (real_opp (real_log q Hq)) (real_log p Hp))
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
        * exact (RealSetoid.real_eq_plus_compat_adapt
                   (real_opp (real_log q Hq)) (real_opp (real_log q Hq))
                   (real_opp (real_opp (real_log p Hp))) (real_log p Hp)
                   (real_eq_refl (real_opp (real_log q Hq)))
                   (real_opp_opp (real_log p Hp))).
        * exact (real_plus_comm (real_opp (real_log q Hq)) (real_log p Hp)). }
  exact (RealSetoid.real_eq_mult_compat_adapt p p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                               (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
           (real_eq_refl p) Hinner).
Qed.

(* ============================================================ *)
(* §3 求和层基元：和的负元                                                 *)
(* ============================================================ *)

(* Σ (−f) == −(Σ f)（sumf_ext 点态 + sumf_linear 两步）                *)
Lemma rkd_sum_opp : forall (S : Type) (sumf : (S -> Real) -> Real)
  (sumf_ext : forall (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
  (sumf_linear : forall (a : Real) (f : S -> Real),
    real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
  (f : S -> Real),
  real_eq (sumf (fun s : S => real_opp (f s))) (real_opp (sumf f)).
Proof.
  intros S sumf sumf_ext sumf_linear f.
  apply (real_eq_trans
           (sumf (fun s : S => real_opp (f s)))
           (real_mult (real_opp real_one) (sumf f))
           (real_opp (sumf f))).
  - apply (real_eq_trans
             (sumf (fun s : S => real_opp (f s)))
             (sumf (fun s : S => real_mult (real_opp real_one) (f s)))
             (real_mult (real_opp real_one) (sumf f))).
    + apply real_eq_sym. apply sumf_ext. intro s.
      exact (rkd_mult_opp_r (f s)).
    + exact (sumf_linear (real_opp real_one) f).
  - exact (rkd_mult_opp_r (sumf f)).
Qed.

(* ============================================================ *)
(* §4 能量期望恒等式（plus 形，任意正分布 q）                                    *)
(*   Σ q·e + D·Σ q·log p_b == −D·log Z（归一化 Σ q == 1 为前提）         *)
(* ============================================================ *)
Lemma rkd_energy_horse :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
    (Hnormq : real_eq (sumf q) real_one),
  real_eq
    (real_plus
       (sumf (fun s : S => real_mult (q s) (real_base_loss s)))
       (real_mult D
          (sumf (fun s : S => real_mult (q s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
    (real_opp (real_mult D (real_log Z Z_pos))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos q Hq Hnormq.
  set (LZ := real_log Z Z_pos).
  set (Spe := sumf (fun s : S => real_mult (q s) (real_base_loss s))).
  set (SLB := sumf (fun s : S => real_mult (q s)
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  (* 点态：e s == −D·log p_b(s) + −D·log Z *)
  assert (Hpt : forall s : S,
    real_eq (real_base_loss s)
            (real_plus
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_opp (real_mult D LZ)))).
  {
    intro s.
    assert (HL1 := rkd_log_pB S real_base_loss D D_pos Z Z_pos s
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)).
    (* D·log p_b(s) == −(e s + D·log Z) *)
    assert (HDL : real_eq
               (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
               (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
    { apply (real_eq_trans
               (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
               (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
               (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
      - exact (RealSetoid.real_eq_mult_compat_adapt D D _ _
                 (real_eq_refl D) HL1).
      - apply (real_eq_trans
                 (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                 (real_opp (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                      (real_mult D LZ)))
                 (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
        + exact (real_eq_trans
                   (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                   (real_opp (real_mult D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                   (real_opp (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                        (real_mult D LZ)))
                   (real_mult_opp_l D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))
                   (RealSetoid.real_eq_opp_compat
                      (real_mult D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))
                      (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                 (real_mult D LZ))
                      (real_distrib D (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))).
        + exact (RealSetoid.real_eq_opp_compat
                   (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                              (real_mult D LZ))
                   (real_plus (real_base_loss s) (real_mult D LZ))
                   (RealSetoid.real_eq_plus_compat_adapt
                      (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                      (real_base_loss s)
                      (real_mult D LZ) (real_mult D LZ)
                      (rkd_inv_absorb D (real_base_loss s) D_pos)
                      (real_eq_refl (real_mult D LZ)))).
    }
    (* opp(D·log p_b) == e s + D·log Z，再由 rkd_eq_cancel_r 右消去        *)
    assert (H4 : real_eq
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_plus (real_base_loss s) (real_mult D LZ))).
    { apply (real_eq_trans
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_opp (real_opp (real_plus (real_base_loss s) (real_mult D LZ))))
               (real_plus (real_base_loss s) (real_mult D LZ))).
      - exact (RealSetoid.real_eq_opp_compat
                 (real_mult D
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
                 (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))
                 HDL).
      - exact (real_opp_opp (real_plus (real_base_loss s) (real_mult D LZ))). }
    exact (rkd_eq_cancel_r
             (real_opp (real_mult D
                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
             (real_base_loss s) (real_mult D LZ) H4).
  }
  (* sumf_ext：Σ q·e == Σ q·(−D·log p_b + −D·log Z)                 *)
  assert (Hext : real_eq Spe
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))).
  { apply sumf_ext. intro w.
    exact (RealSetoid.real_eq_mult_compat_adapt (q w) (q w) _ _
             (real_eq_refl (q w)) (Hpt w)). }
  (* real_distrib 点态 + sumf_add：拆为两个子和                             *)
  assert (Hsplit : real_eq
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))
             (sumf (fun s : S => real_plus
                       (real_mult (q s)
                          (real_opp (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
                       (real_mult (q s) (real_opp (real_mult D LZ)))))
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))).
    - apply sumf_ext. intro w.
      exact (real_distrib (q w)
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))))
               (real_opp (real_mult D LZ))).
    - exact (sumf_add
               (fun s : S => real_mult (q s)
                  (real_opp (real_mult D
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
               (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))). }
  (* 第一项：Σ q·(−D·Lb) == −(D·SLB)                                   *)
  assert (HT1 : real_eq
             (sumf (fun s : S => real_mult (q s)
                      (real_opp (real_mult D
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (real_mult D SLB))).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s)
                      (real_opp (real_mult D
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (sumf (fun s : S => real_mult D
                         (real_mult (q s)
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (real_mult D SLB))).
    - apply (real_eq_trans
               (sumf (fun s : S => real_mult (q s)
                        (real_opp (real_mult D
                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
               (sumf (fun s : S => real_opp (real_mult D
                         (real_mult (q s)
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
               (real_opp (sumf (fun s : S => real_mult D
                           (real_mult (q s)
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
      + apply sumf_ext. intro w. rkd_alg.
      + exact (rkd_sum_opp S sumf sumf_ext sumf_linear
                 (fun s : S => real_mult D
                    (real_mult (q s)
                       (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
    - exact (RealSetoid.real_eq_opp_compat
               (sumf (fun s : S => real_mult D
                  (real_mult (q s)
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
               (real_mult D SLB)
               (sumf_linear D
                  (fun s : S => real_mult (q s)
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))). }
  (* 第二项：Σ q·(−D·log Z) == (−D)·log Z·Σ q，以 Hnormq 归一化消去 Σ q       *)
  assert (HT2 : real_eq
             (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ))))
             (real_mult (real_opp D) LZ)).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ))))
             (sumf (fun s : S => real_mult (real_mult (real_opp D) LZ) (q s)))
             (real_mult (real_opp D) LZ)).
    - apply sumf_ext. intro w. rkd_alg.
    - apply (real_eq_trans
               (sumf (fun s : S => real_mult (real_mult (real_opp D) LZ) (q s)))
               (real_mult (real_mult (real_opp D) LZ) (sumf q))
               (real_mult (real_opp D) LZ)).
      + exact (sumf_linear (real_mult (real_opp D) LZ) q).
      + exact (real_eq_trans
                 (real_mult (real_mult (real_opp D) LZ) (sumf q))
                 (real_mult (real_mult (real_opp D) LZ) real_one)
                 (real_mult (real_opp D) LZ)
                 (RealSetoid.real_eq_mult_compat_adapt
                    (real_mult (real_opp D) LZ) (real_mult (real_opp D) LZ)
                    (sumf q) real_one
                    (real_eq_refl (real_mult (real_opp D) LZ)) Hnormq)
                 (real_mult_one (real_mult (real_opp D) LZ))). }
  (* 合成：Spe == −D·SLB + (−D)·log Z（Hext、Hsplit、HT1、HT2）            *)
  assert (Hmain : real_eq Spe (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))).
  { exact (real_eq_trans Spe
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))
             (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))
             (real_eq_trans Spe
                (sumf (fun s : S => real_mult (q s)
                         (real_plus
                            (real_opp (real_mult D
                               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                            (real_opp (real_mult D LZ)))))
                (real_plus
                   (sumf (fun s : S => real_mult (q s)
                            (real_opp (real_mult D
                               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                   (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))
                Hext Hsplit)
             (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ HT1 HT2)). }
  apply (real_eq_trans
           (real_plus Spe (real_mult D SLB))
           (real_plus (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))
                      (real_mult D SLB))
           (real_opp (real_mult D LZ))).
  - exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ Hmain
             (real_eq_refl (real_mult D SLB))).
  - rkd_alg.
Qed.

(* ============================================================ *)
(* §5 求和层 KL 分解与 Boltzmann 归一化                                   *)
(* ============================================================ *)

(* Σ kl_term(p, p_b) == Σ p·log p − Σ p·log p_b（逐点 rkd_kl_point、 *)
(*   real_distrib、sumf_add、rkd_sum_opp 四步合成）                     *)
Lemma rkd_kl_sum_bridge :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq
    (sumf (fun s : S => real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
    (real_plus
       (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
       (real_opp
          (sumf (fun s : S => real_mult (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos p Hp.
  apply (real_eq_trans
           (sumf (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
           (real_plus
              (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
              (sumf (fun s : S => real_mult (p s)
                       (real_opp
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
           (real_plus
              (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
              (real_opp
                 (sumf (fun s : S => real_mult (p s)
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
  - apply (real_eq_trans
             (sumf (fun s : S => real_kl_term (p s)
                        (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                        (Hp s)
                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
             (sumf (fun s : S => real_plus
                        (real_mult (p s) (real_log (p s) (Hp s)))
                        (real_mult (p s)
                           (real_opp
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_plus
                (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
                (sumf (fun s : S => real_mult (p s)
                         (real_opp
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
    + apply sumf_ext. intro w.
      exact (real_eq_trans
               (real_kl_term (p w)
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                  (Hp w)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))
               (real_mult (p w)
                  (real_plus (real_log (p w) (Hp w))
                             (real_opp
                                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w)))))
               (real_plus
                  (real_mult (p w) (real_log (p w) (Hp w)))
                  (real_mult (p w)
                     (real_opp
                        (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w)))))
               (rkd_kl_point (p w)
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                  (Hp w)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))
               (real_distrib (p w) (real_log (p w) (Hp w))
                  (real_opp
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))))).
    + exact (sumf_add
               (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))
               (fun s : S => real_mult (p s)
                  (real_opp
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
  - apply (RealSetoid.real_eq_plus_compat_adapt
             (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
             (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
             (sumf (fun s : S => real_mult (p s)
                      (real_opp
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_opp
                (sumf (fun s : S => real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_eq_refl (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))))).
    exact (real_eq_trans
             (sumf (fun s : S => real_mult (p s)
                      (real_opp
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (sumf (fun s : S => real_opp
                      (real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_opp
                (sumf (fun s : S => real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (sumf_ext
                (fun s : S => real_mult (p s)
                   (real_opp
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                (fun s : S => real_opp
                   (real_mult (p s)
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                (fun s : S => real_mult_opp_l (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
             (rkd_sum_opp S sumf sumf_ext sumf_linear
                (fun s : S => real_mult (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
Qed.

(* 归一化：配分函数条件 Σ exp(−e/D) == Z ⟹ Σ p_b == 1                      *)
(*   （sumf_linear + real_inv_pos_correct 两步归一化）                  *)
Lemma rkd_boltzmann_normalized :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (Hpart : real_eq
               (sumf (fun s : S => real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
               Z),
  real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one.
Proof.
  intros S sumf sumf_ext sumf_linear real_base_loss D D_pos Z Z_pos Hpart.
  apply (real_eq_trans
           (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos))
           (real_mult (real_inv_pos Z Z_pos) Z)
           real_one).
  - apply (real_eq_trans
             (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos))
             (sumf (fun s : S => real_mult (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
             (real_mult (real_inv_pos Z Z_pos) Z)).
    + apply sumf_ext. intro s. exact (real_eq_refl _).
    + apply (real_eq_trans
               (sumf (fun s : S => real_mult (real_inv_pos Z Z_pos)
                         (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z Z_pos)
                  (sumf (fun s : S => real_exp_neg
                           (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z Z_pos) Z)).
      * exact (sumf_linear (real_inv_pos Z Z_pos)
                  (fun s : S => real_exp_neg
                                   (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * exact (RealSetoid.real_eq_mult_compat_adapt
                 (real_inv_pos Z Z_pos) (real_inv_pos Z Z_pos)
                 (sumf (fun s : S => real_exp_neg
                          (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 Z
                 (real_eq_refl (real_inv_pos Z Z_pos)) Hpart).
  - apply (real_eq_trans
             (real_mult (real_inv_pos Z Z_pos) Z)
             (real_mult Z (real_inv_pos Z Z_pos))
             real_one).
    + exact (real_mult_comm (real_inv_pos Z Z_pos) Z).
    + exact (real_inv_pos_correct Z Z_pos).
Qed.

(* ============================================================ *)
(* §6 主定理：real_kl_decomp_full（一般 Z 条件形与定义 Z 无条件形）                *)
(* ============================================================ *)

(* 主件1（一般 Z 条件形）：结论与 UpRealLeB / S08 中 real_kl_decomp_           *)
(*   full 假设逐字同构；前提 = 假设 (Hp, Hnormp) + 结构前提                     *)
(*   ext/add/linear + 数学前提 Hnormb（Σ p_b == 1）。                   *)
Theorem rkd_kl_decomp_full :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one),
  real_eq
    (real_free_energy S sumf real_base_loss D p Hp)
    (real_plus
       (real_free_energy S sumf real_base_loss D
          (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos))
       (real_mult D
          (sumf (fun s : S =>
             real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb.
  unfold real_free_energy.
  set (LZ := real_log Z Z_pos).
  set (A := sumf (fun s : S => real_mult (p s) (real_base_loss s))).
  set (B := sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))).
  set (C := sumf (fun s : S => real_mult (p s)
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  set (E := sumf (fun s : S => real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (real_base_loss s))).
  set (G := sumf (fun s : S => real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  set (K := sumf (fun s : S => real_kl_term (p s)
                    (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (Hp s)
                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))).
  assert (H1 : real_eq (real_plus A (real_mult D C)) (real_opp (real_mult D LZ))).
  { exact (rkd_energy_horse S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos p Hp Hnormp). }
  assert (H2 : real_eq (real_plus E (real_mult D G)) (real_opp (real_mult D LZ))).
  { exact (rkd_energy_horse S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos) Hnormb). }
  assert (H3 : real_eq K (real_plus B (real_opp C))).
  { exact (rkd_kl_sum_bridge S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos p Hp). }
  apply (real_eq_trans
           (real_plus A (real_mult D B))
           (real_plus (real_plus E (real_mult D G)) (real_mult D (real_plus B (real_opp C))))
           (real_plus (real_plus E (real_mult D G)) (real_mult D K))).
  - apply (real_eq_trans
             (real_plus A (real_mult D B))
             (real_plus (real_plus A (real_mult D C)) (real_mult D (real_plus B (real_opp C))))
             (real_plus (real_plus E (real_mult D G)) (real_mult D (real_plus B (real_opp C))))).
    + rkd_alg.
    + exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _
               (real_eq_trans (real_plus A (real_mult D C)) (real_opp (real_mult D LZ))
                              (real_plus E (real_mult D G)) H1 (real_eq_sym _ _ H2))
               (real_eq_refl (real_mult D (real_plus B (real_opp C))))).
  - exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _
             (real_eq_refl (real_plus E (real_mult D G)))
             (RealSetoid.real_eq_mult_compat_adapt D D
                (real_plus B (real_opp C)) K
                (real_eq_refl D) (real_eq_sym _ _ H3))).
Qed.

(* 主件2（定义 Z 无条件形）：Z := Σ exp(−e/D) 内联定义，正性证书 Zp                  *)
(*   为唯一额外前提（与 UpRealLeB 节内 Z_align_r_pos 同类）；Hnormb             *)
(*   由 rkd_boltzmann_normalized 与 partition 定义等式（real_eq_refl）   *)
(*   内证消去——零残留数学前提的无条件定理形。                                       *)
Theorem rkd_kl_decomp_full_partition :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Zp : real_lt real_zero
            (sumf (fun s : S => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (real_base_loss s))))),
  real_eq
    (real_free_energy S sumf real_base_loss D p Hp)
    (real_plus
       (real_free_energy S sumf real_base_loss D
          (real_boltzmann_dist_r S real_base_loss D D_pos
             (sumf (fun s : S => real_exp_neg
                       (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos
             (sumf (fun s : S => real_exp_neg
                       (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp))
       (real_mult D
          (sumf (fun s : S =>
             real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos
                  (sumf (fun s : S => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos
                  (sumf (fun s : S => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos p Hp Hnormp Zp.
  apply (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear           real_base_loss D D_pos           (sumf (fun s : S => real_exp_neg                     (real_mult (real_inv_pos D D_pos) (real_base_loss s))))           Zp p Hp Hnormp).
  exact (rkd_boltzmann_normalized S sumf sumf_ext sumf_linear           real_base_loss D D_pos           (sumf (fun s : S => real_exp_neg                     (real_mult (real_inv_pos D D_pos) (real_base_loss s))))           Zp (real_eq_refl _)).
Qed.

(* ============================================================ *)
(* 依赖审计：全件零外部未证假设                                                *)
(* ============================================================ *)
Print Assumptions rkd_mult_opp_r.
Print Assumptions rkd_inv_absorb.
Print Assumptions rkd_eq_cancel_r.
Print Assumptions rkd_log_pB.
Print Assumptions rkd_kl_point.
Print Assumptions rkd_sum_opp.
Print Assumptions rkd_energy_horse.
Print Assumptions rkd_kl_sum_bridge.
Print Assumptions rkd_boltzmann_normalized.
Print Assumptions rkd_kl_decomp_full.
Print Assumptions rkd_kl_decomp_full_partition.
