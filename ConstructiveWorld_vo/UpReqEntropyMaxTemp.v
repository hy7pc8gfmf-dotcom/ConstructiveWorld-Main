(* ============================================================ *)
(* UpReqEntropyMaxTemp.v —— 席T14：定理 4.6b max_entropy_is_boltzmann_temp *)
(*   Real 层序档组装席 ｜ 2026-09-11 ｜ 后台独立席位（独占 CoreN 7）        *)
(* ------------------------------------------------------------------ *)
(* 【使命】同约束能量 E(p) == E_T 下 S[p] ≤ S[p_T]（论文正式版 L321-323；  *)
(*   Id 原件 S04 L3935 max_entropy_is_boltzmann_temp）。档位：逐 eps 形。  *)
(* ------------------------------------------------------------------ *)
(* 【档位诚实标注】Id 层 gibbs_inequality 的 Real 层对应件为逐 eps 档：    *)
(*   CW219 real_gibbs_core_eps / real_gibbs_inequality_eps 全系 eps 形     *)
(*   （S08 L199/L493），故本席 4.6b 交付逐 eps 形：                        *)
(*     E(p) == E_T ⟹ real_le (S[p]) (real_plus S[p_T] eps)（eps > 0）     *)
(*   与库内 Gibbs 家族档位严格对齐，非缩水。                               *)
(* ------------------------------------------------------------------ *)
(* 【接口扩容（T6b 精确余留指认）】抽象求和面单调接口 real_sum_over_S_le： *)
(*   逐点 real_le ⟹ 求和面 real_le。抽象面仅 eq 三接口（ext/linear/add）  *)
(*   推不出单调提升，故按 G06_BForm L35 / UpRealLeB L268 同形先例以       *)
(*   Section Variable 扩容（引理前提不动——归一化/逐点正/同能量三口照 Id， *)
(*   仅求和面扩容，非加码）。具体载体实例已在库且非空：real_list_sum_le   *)
(*   （S08 L421，CW219 薄壳 Require Export S08 直达），本席位 0 件显式    *)
(*   给出载体满足证。逐点核 real_gibbs_core_eps（S08 L199）零载体依赖     *)
(*   直用（T6b 指认，Check 探针实证无 Section 残参）。                     *)
(* ------------------------------------------------------------------ *)
(* 【Id 层原件对位表（S04 L3935-3972 逐步实证）】                          *)
(*   Id intros t Ht p Hnp Hpp Henergy    ↦ 同口（T 正性证人在 T_pos 位；  *)
(*     Hp 前移为 real_entropy_dist 证人位，T6 real_entropy_dist 同位）    *)
(*   Id Hdef := entropy_deficit_kl_temp  ↦ Hdef :=                        *)
(*     real_entropy_deficit_kl_temp（T6b 主件全 arity 13 参直喂；         *)
(*     real_minus_r Spt Sp 定义性展开 real_plus Spt (real_opp Sp)）       *)
(*   Id Hkl := gibbs_inequality p p_T    ↦ real_KL_temp_ge_zero_eps       *)
(*     （本席件 2；Id gibbs 四前提 Real 对应：Hnp 前提位 + Hp 证人位 +    *)
(*     real_boltzmann_dist_temp_normalized 库件 + real_boltzmann_dist_    *)
(*     _temp_pos 库件；内部走 real_gibbs_core_eps + real_sum_over_S_le）  *)
(*   Id Hnonneg := le_id_r Hdef Hkl      ↦ real_le_id_r + eq 兼容腿      *)
(*     （real_eq_plus_compat_adapt Hdef换向 (refl eps)）                  *)
(*   Id Hplus := minus_plus_cancel      ↦ real_plus_neg_cancel_shift_eps  *)
(*     （本席工作马 B：Sp + ((Spt+(−Sp))+eps) ≡ Spt+eps，eps 形镜像）     *)
(*   Id Hle := le_plus_nonneg_r         ↦ real_le_plus_nonneg_r           *)
(*     （本席工作马 A：0 ≤ b ⟹ a ≤ a+b；le_plus_compat + plus_zero）     *)
(*   Id le_id_r 收口                    ↦ real_le_id_r + 工作马 B eq 腿   *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（语句全 real_eq/real_lt/real_le）；*)
(*   前提位照 Id 层对位（eps > 0 为 CW219 Gibbs eps 档既有证人位），       *)
(*   全 Qed 收口；零新承认件。                                            *)
(* 编译配方（同 T6b）：coqc -vos -Q . "" -Q "../001" ""                    *)
(*   -Q "../attn/_build_219" "" UpReqEntropyMaxTemp.v（秒审后全量）       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ---------------------------------------------------------- *)
(* 件 0：接口非空证（具体载体实例）：real_list_sum 载体的逐点-求和        *)
(*   单调提升件已在库（S08 L421），抽象接口扩容位有现货满足证。           *)
(* ---------------------------------------------------------- *)
Corollary real_sum_le_list_carrier_instance :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall w : X, real_le (f w) (g w)) ->
    real_le (real_list_sum X f l) (real_list_sum X g l).
Proof.
  exact (fun (X : Type) (f g : X -> Real) (l : list X)
           (H : forall w : X, real_le (f w) (g w)) =>
           real_list_sum_le X f g l H).
Qed.

(* ---------------------------------------------------------- *)
(* 工作马 A：0 ≤ b ⟹ a ≤ a+b（Id le_plus_nonneg_r Real 对位；            *)
(*   real_le_plus_compat + real_plus_zero（右零消去形 x+0 ≡ x））         *)
(* ---------------------------------------------------------- *)
Lemma real_le_plus_nonneg_r :
  forall a b : Real,
    real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)
           (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))).
  exact (real_le_plus_compat a a real_zero b (real_le_refl a) Hb).
Qed.

(* ---------------------------------------------------------- *)
(* 工作马 B：a + ((b + (−a)) + eps) ≡ b + eps                            *)
(*   （Id minus_plus_cancel 的 eps 形镜像；六腿换形链：assoc → 内层       *)
(*   assoc → comm → assoc 反向 → plus_opp → plus_zero）                   *)
(* ---------------------------------------------------------- *)
Lemma real_plus_neg_cancel_shift_eps :
  forall (a b eps : Real),
    real_eq (real_plus a (real_plus (real_plus b (real_opp a)) eps))
            (real_plus b eps).
Proof.
  intros a b eps.
  apply (real_eq_trans
           (real_plus a (real_plus (real_plus b (real_opp a)) eps))
           (real_plus (real_plus b real_zero) eps)
           (real_plus b eps)).
  - (* 腿 1a：换形五腿至 (b+0)+eps *)
    apply (real_eq_trans
             (real_plus a (real_plus (real_plus b (real_opp a)) eps))
             (real_plus (real_plus a (real_plus b (real_opp a))) eps)
             (real_plus (real_plus b real_zero) eps)).
    + exact (real_plus_assoc a (real_plus b (real_opp a)) eps).
    + apply (real_eq_trans
               (real_plus (real_plus a (real_plus b (real_opp a))) eps)
               (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
               (real_plus (real_plus b real_zero) eps)).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_plus a (real_plus b (real_opp a)))
                 (real_plus (real_plus a b) (real_opp a))
                 eps eps
                 (real_plus_assoc a b (real_opp a))
                 (real_eq_refl eps)).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                 (real_plus (real_plus b (real_plus a (real_opp a))) eps)
                 (real_plus (real_plus b real_zero) eps)).
        -- apply (real_eq_trans
                    (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                    (real_plus (real_plus (real_plus b a) (real_opp a)) eps)
                    (real_plus (real_plus b (real_plus a (real_opp a))) eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus a b) (real_opp a))
                       (real_plus (real_plus b a) (real_opp a))
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (real_plus a b) (real_plus b a)
                          (real_opp a) (real_opp a)
                          (real_plus_comm a b)
                          (real_eq_refl (real_opp a)))
                       (real_eq_refl eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus b a) (real_opp a))
                       (real_plus b (real_plus a (real_opp a)))
                       eps eps
                       (real_eq_sym (real_plus b (real_plus a (real_opp a)))
                                    (real_plus (real_plus b a) (real_opp a))
                                    (real_plus_assoc b a (real_opp a)))
                       (real_eq_refl eps)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus b (real_plus a (real_opp a)))
                    (real_plus b real_zero)
                    eps eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       b b
                       (real_plus a (real_opp a)) real_zero
                       (real_eq_refl b)
                       (real_plus_opp a))
                    (real_eq_refl eps)).
  - (* 腿 1b：(b+0)+eps ≡ b+eps（plus_zero 右零消去形） *)
    apply (RealSetoid.real_eq_plus_compat_adapt
             (real_plus b real_zero) b
             eps eps
             (real_plus_zero b)
             (real_eq_refl eps)).
Qed.

(* ============================================================ *)
(* Section RealEntropyMaxTemp：求和面/温度/能量参数照 UpReqTempDefs      *)
(*   同名同序；扩容位：real_sum_over_S_le（紧随 ext，接口单调位）。      *)
(* ============================================================ *)
Section RealEntropyMaxTemp.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
(* 接口扩容位（T6b 余留指认；G06_BForm L35 / UpRealLeB L268 同形先例；   *)
(*   具体载体实例见本文件件 0：real_list_sum_le，S08 L421 在库）。       *)
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 件 1：KL 逐 eps 非负（Id gibbs_inequality 温度特化 Real 对位）：       *)
(*   归一 p、逐点正、eps > 0 ⟹ 0 ≤ KL(p‖p_T) + eps。                     *)
(*   链：桥（T6b 件 5）→ 逐点核（real_gibbs_core_eps）→ 扩容接口提升     *)
(*   → LHS 坍缩（Σp−p_T ≡ 1−1 ≡ 0）→ 误差坍缩（Σp·eps ≡ eps）。          *)
(* ---------------------------------------------------------- *)
Theorem real_KL_temp_ge_zero_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Hepspos.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  (* 0. 桥：KL ≡ Σ real_kl_term（T6b 件 5，全 arity 9 参直喂） *)
  assert (Hbridge : real_eq
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp). }
  (* 1. 逐点核：p − p_T ≤ real_kl_term + p·eps（CW219 直喂；real_kl_term  *)
  (*    与 real_gibbs_core_eps RHS 首和项定义性一致，S08 L508 同款消费）  *)
  assert (Hpt : forall s : S,
           real_le (real_plus (p s) (real_opp (pT s)))
                   (real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps))).
  { intro s.
    exact (real_gibbs_core_eps (p s) (pT s) (Hp s) (HpT s) eps Hepspos). }
  (* 2. 求和面提升（扩容接口位） *)
  assert (Hsum : real_le
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))).
  { exact (real_sum_over_S_le
             (fun s : S => real_plus (p s) (real_opp (pT s)))
             (fun s : S => real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                                     (real_mult (p s) eps))
             Hpt). }
  (* 3. LHS 坍缩：Σ(p − p_T) ≡ Σp + −Σp_T ≡ 1 + (−1) ≡ 0 *)
  assert (HnormT : real_eq (real_sum_over_S pT) real_one).
  { exact (real_boltzmann_dist_temp_normalized S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear T T_pos energy). }
  assert (Hzero : real_eq
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           real_zero).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
             (real_plus (real_sum_over_S p)
                        (real_sum_over_S (fun s : S => real_opp (pT s))))
             real_zero).
    - exact (real_sum_over_S_add p (fun s : S => real_opp (pT s))).
    - apply (real_eq_trans
               (real_plus (real_sum_over_S p)
                          (real_sum_over_S (fun s : S => real_opp (pT s))))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_sum_over_S p) real_one
                 (real_sum_over_S (fun s : S => real_opp (pT s)))
                 (real_opp real_one)
                 Hnp
                 (real_eq_trans
                    (real_sum_over_S (fun s : S => real_opp (pT s)))
                    (real_opp (real_sum_over_S pT))
                    (real_opp real_one)
                    (real_sum_over_S_opp S real_sum_over_S real_sum_over_S_ext
                       real_sum_over_S_linear pT)
                    (RealSetoid.real_eq_opp_compat
                       (real_sum_over_S pT) real_one HnormT))).
      + exact (real_plus_opp real_one).
  }
  (* 4. 误差坍缩：Σ(p·eps) ≡ Σ(eps·p) ≡ eps·Σp ≡ eps·1 ≡ eps *)
  assert (Heps : real_eq (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (p s) eps))
             (real_sum_over_S (fun s : S => real_mult eps (p s)))
             eps).
    - apply real_sum_over_S_ext.
      intro s. exact (real_mult_comm (p s) eps).
    - apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult eps (p s)))
               (real_mult eps (real_sum_over_S p))
               eps).
      + exact (real_sum_over_S_linear eps p).
      + apply (real_eq_trans
                 (real_mult eps (real_sum_over_S p))
                 (real_mult eps real_one)
                 eps).
        * apply (RealSetoid.real_eq_mult_compat_adapt eps eps
                   (real_sum_over_S p) real_one
                   (real_eq_refl eps) Hnp).
        * exact (real_mult_one eps).
  }
  (* 5. RHS 换形：Σ(kl + p·eps) ≡ Σkl + eps *)
  assert (Hrhs : real_eq
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S =>
                real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                          (real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                (real_sum_over_S (fun s : S => real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                eps)).
    - exact (real_sum_over_S_add
               (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))
               (fun s : S => real_mult (p s) eps)).
    - apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps
               (real_eq_refl
                  (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))))
               Heps).
  }
  (* 6. 组装：le 0 Σ(kl+p·eps) → le 0 (Σkl+eps) → le 0 (KL+eps)（两跳换形） *)
  exact (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)
           (real_plus
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
              eps)
           (RealSetoid.real_eq_plus_compat_adapt
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
              eps eps
              (real_eq_sym _ _ Hbridge)
              (real_eq_refl eps))
           (RealSetoid.real_le_id_r real_zero
              (real_sum_over_S (fun s : S =>
                 real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                           (real_mult (p s) eps)))
              (real_plus
                 (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                 eps)
              Hrhs
              (RealSetoid.real_le_id_l real_zero
                 (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                 (real_sum_over_S (fun s : S =>
                    real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps)))
                 (real_eq_sym
                    (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                    real_zero
                    Hzero)
                 Hsum))).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2（主件）：定理 4.6b 逐 eps 形（Id max_entropy_is_boltzmann_temp   *)
(*   S04 L3935 逐槽对位）：同约束能量 E(p) == E_T ⟹ S[p] ≤ S[p_T] + eps。 *)
(*   链：熵亏温度版（T6b）→ KL 逐 eps 非负（件 1）→ le 链收口。          *)
(* ---------------------------------------------------------- *)
Theorem real_max_entropy_is_boltzmann_temp_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (real_entropy_dist S real_sum_over_S p Hp)
              (real_plus
                 (real_entropy_dist S real_sum_over_S
                    (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy)
                    (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy))
                 eps).
Proof.
  intros p Hp Hnp Henergy eps Hepspos.
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：熵亏温度版（T6b 主件全 arity 13 参直喂；Id Hdef 对位；          *)
  (*   real_minus_r 定义性展开 real_plus Spt (real_opp Sp)） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnp Henergy). }
  (* 步 2：KL 逐 eps 非负（件 1；Id Hkl 对位） *)
  assert (Hkl : real_le real_zero (real_plus KL eps)).
  { exact (real_KL_temp_ge_zero_eps p Hp Hnp eps Hepspos). }
  (* 步 3：换形到 Spt 腿（Id Hnonneg 对位；real_le_id_r + eq 兼容腿） *)
  assert (Hstep : real_le real_zero (real_plus (real_plus Spt (real_opp Sp)) eps)).
  { apply (RealSetoid.real_le_id_r real_zero (real_plus KL eps)
             (real_plus (real_plus Spt (real_opp Sp)) eps)
             (RealSetoid.real_eq_plus_compat_adapt KL (real_plus Spt (real_opp Sp))
                eps eps
                (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef)
                (real_eq_refl eps))).
    exact Hkl. }
  (* 步 4：非负加法腿（工作马 A；Id Hle 对位） *)
  assert (H1 : real_le Sp (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))).
  { exact (real_le_plus_nonneg_r Sp (real_plus (real_plus Spt (real_opp Sp)) eps)
             Hstep). }
  (* 步 5：收口（工作马 B eq 腿 + real_le_id_r；Id Hplus + 末步对位） *)
  exact (RealSetoid.real_le_id_r Sp
           (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))
           (real_plus Spt eps)
           (real_plus_neg_cancel_shift_eps Sp Spt eps)
           H1).
Qed.

End RealEntropyMaxTemp.
