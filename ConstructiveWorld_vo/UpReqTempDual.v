(* ============================================================ *)
(* UpReqTempDual.v *)
(* *)
(* 目的： 温度族 sigT 对偶闭环与定理 4.6d 组装。 *)
(* 主件： temp_energy_dual_closed_real / temp_energy_dual_closed_bool 双载体闭环。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、UpReqKLSTangent。 *)
(* 备注： 与第三档同源（4.3 边界）：无条件 Or 形不可达，取逐 eps 档；抽象载体为诚实接口前提。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqTempDual.v —— 席T13：温度族 sigT 对偶闭环 + 定理 4.6d 组装      *)

(* ------------------------------------------------------------------ *)
(* 【使命】席T6 交接欠件：论文正式版 L329-344 定理 4.6d                  *)
(*   （温度化最大熵对偶闭环，构造强度：见证构造档）的 Real 层 sigT 形    *)
(*   组装。基座 = UpReqTempDefs（席T6 四定义件+normalized/pos/explicit   *)
(*   三口）+ UpReqEntropyDeficitTemp（席T6b 4.6a 熵亏件）+               *)
(*   UpReqKLSTangent（席T1 t1_gibbe2_gibbs_equality_bool 无条件注入）。  *)
(*   组装手法承席T7（UpReqMinFreeEps）：分解件+Gibbs 腿+序代数消去，     *)
(*   换熵侧载体。                                                        *)
(* ------------------------------------------------------------------ *)
(* 【Id 层原件对位（五合取支逐位对照表，ConstructiveWorld L17788 全文）】*)
(*   Id sigT (fun pb => ...)              ↝ Real sigT×2（pb 正性证人     *)
(*     Hpb 升为第二见证位——real_entropy_dist 前提位所需；req 层模板      *)
(*     req_temp_energy_dual_closed（UpReqTempEntropy L1467）同构）。      *)
(*   Id And                              ↝ Real 乘积 *（Set 层，零 Prop） *)
(*   Id 支1a normalized pb               ↝ 支A：real_eq (Σ pb) one        *)
(*     （T6 real_boltzmann_dist_temp_normalized 全 arity 显式应用）           *)
(*   Id 支1b positive_dist pb            ↝ sigT 第二见证 Hpb（T6 pos 件） *)
(*   Id 支2 Id (E pb) (E_temp t)         ↝ 支B：real_eq (E pb) E_T        *)
(*     （real_energy_exp_temp 定义性收敛，real_eq_refl 完成）             *)
(*   Id 支3 le (S p) (S pb)              ↝ 支C：逐 eps 档                 *)
(*     real_le (S p) (S pb + eps)（∀eps>0）——Or 形 real_le 的比较界      *)
(*     与席T7 第三档同源（4.3 边界）：无条件 Or 形不可达，逐 eps 档为     *)
(*     最强可达形。链 = 4.6a 熵亏件（S[pb]−S[p] ≡ KL）+ Gibbs 腿         *)
(*     （抽象载体=诚实接口前提，S08 L2511 同形；bool 载体=                 *)
(*     real_gibbs_inequality_eps 实例化）+ 差正移项（real_lt_zero_minus   *)

(*   Id 支4 S p ≡ S pb ⟹ 逐点 p ≡ pb     ↝ 支D 两档：                    *)
(*     D1（全载体）熵等 ⟹ KL 归零（t13_entropy_eq_kl_zero，Setoid 代数）；*)
(*     D2（bool 载体全闭）KL≡0 ⟹ 逐点（t1_gibbe2_gibbs_equality_bool，   *)
(*     席T1 无条件注入形——无条件版唯一支在通用载体受三分判定界，          *)
(*     bool 为 gibbe2 样板可达档）。                                      *)
(*   总装件两枚：temp_energy_dual_closed_real（抽象载体对位骨架，        *)
(*   支A/B/C/D1 全闭；支C 带 Gibbs 腿接口前提、支D 结果 D1 档）+          *)
(*   temp_energy_dual_closed_bool（bool 载体全闭总装：支A/B/C/D2 全闭，  *)
(*   支C 逐 eps 档、支D 全点闭——见证构造档在 bool 模型的完整 sigT 闭环）。*)
(* ------------------------------------------------------------------ *)
(* 【温度-能量单调接口注记（如实登记）】Id energy_exp_temp_mono           *)
(*   （S04 L3733）的 Real 对位 real_energy_exp_temp_mono 全库零命中       *)
(*   （grep 实证，2026-09-11）：未建。可达强度预评：恒等档（β·(b1−b2)·   *)
(*   (E2−E1) ≡ KL1+KL2 类分解）原料同 Id 层；严格档需 KL 严格正接口       *)

(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性四条红线：零承认件；Set 层零 Prop 泄露（总装语句全     *)
(*   real_eq/real_lt/real_le 逐点 Set 值 + sigT/乘积组装）；G1 禁词条目   *)
(*   零命中（头注以中文转述）；全 Qed 完成。前置件只读：                  *)
(*   UpReqTempDefs/UpReqEntropyDeficitTemp/UpReqKLSTangent/S 模块。       *)

(*   后全量（去 -vos）；前置 .vo 全在 ConstructiveWorld_vo 树。           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqKLSTangent.

(* ============================================================ *)
(* Section RealTempDual：抽象载体对位骨架（参数面与 T6/T6b 同名同序）    *)
(* ============================================================ *)
Section RealTempDual.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* 简称（T6/T6b 全 arity 件， discharge 后展开为完整项） *)
Let tB : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy.
Let tBpos : forall s : S, real_lt real_zero (tB s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy.
Let tE : Real :=
  real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy.
Let tKL (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp.
Let tH (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)) : Real :=
  real_entropy_dist S real_sum_over_S q Hq.
Let tEen (q : S -> Real) : Real :=
  real_sum_over_S (fun s : S => real_mult (q s) (energy s)).

(* ---------------------------------------------------------- *)
(* 工作马 1：差正移项（0 ≤ z − x ⟹ x ≤ z）。                              *)
(*   lt 支：real_lt_zero_minus（S07，eps 见证不变）；eq 支：               *)
(*   Setoid 代数链（x ≡ x+0 ≡ x+(z−x) ≡ x+((−x)+z) ≡ 0+z ≡ z）。           *)
(* ---------------------------------------------------------- *)
Lemma t13_le_plus_opp_shift :
  forall (x z : Real),
    real_le real_zero (real_plus z (real_opp x)) -> real_le x z.
Proof.
  intros x z H. unfold real_le in H. destruct H as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req x z). left.
    exact (real_lt_zero_minus x z Hlt).
  - apply (RealSetoid.real_lt_le_iff_req x z). right.
    apply (real_eq_trans x (real_plus x real_zero) z).
    + apply real_eq_sym. exact (real_plus_zero x).
    + apply (real_eq_trans (real_plus x real_zero)
               (real_plus x (real_plus z (real_opp x))) z).
      * apply (RealSetoid.real_eq_plus_compat_adapt x x real_zero
                 (real_plus z (real_opp x)) (real_eq_refl x) Heq).
      * apply (real_eq_trans (real_plus x (real_plus z (real_opp x)))
                 (real_plus x (real_plus (real_opp x) z)) z).
        -- apply (RealSetoid.real_eq_plus_compat_adapt x x
                     (real_plus z (real_opp x)) (real_plus (real_opp x) z)
                     (real_eq_refl x) (real_plus_comm z (real_opp x))).
        -- apply (real_eq_trans (real_plus x (real_plus (real_opp x) z))
                     (real_plus (real_plus x (real_opp x)) z) z).
           ++ exact (real_plus_assoc x (real_opp x) z).
           ++ apply (real_eq_trans (real_plus (real_plus x (real_opp x)) z)
                        (real_plus real_zero z) z).
              ** apply (RealSetoid.real_eq_plus_compat_adapt
                           (real_plus x (real_opp x)) real_zero z z
                           (real_plus_opp x) (real_eq_refl z)).
              ** apply (real_eq_trans (real_plus real_zero z)
                           (real_plus z real_zero) z).
                 --- exact (real_plus_comm real_zero z).
                 --- exact (real_plus_zero z).
Qed.

(* ---------------------------------------------------------- *)
(* 工作马 2（4.6d 唯一支·前半）：熵等 ⟹ KL 归零（全载体）。               *)
(*   链 = 4.6a 熵亏件（KL ≡ S[pb]−S[p]）反向 + 熵等换载 + plus_opp。       *)
(* ---------------------------------------------------------- *)
Lemma t13_entropy_eq_kl_zero :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (tEen p) tE ->
    real_eq (tH p Hp) (tH tB tBpos) ->
    real_eq (tKL p Hp) real_zero.
Proof.
  intros p Hp Hnormp Henergy HeqH.
  apply (real_eq_trans (tKL p Hp)
           (real_plus (tH tB tBpos) (real_opp (tH p Hp))) real_zero).
  - apply real_eq_sym.
    exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnormp Henergy).
  - apply (real_eq_trans (real_plus (tH tB tBpos) (real_opp (tH p Hp)))
             (real_plus (tH p Hp) (real_opp (tH p Hp))) real_zero).
    + apply (RealSetoid.real_eq_plus_compat_adapt (tH tB tBpos) (tH p Hp)
               (real_opp (tH p Hp)) (real_opp (tH p Hp))
               (real_eq_sym _ _ HeqH)
               (real_eq_refl (real_opp (tH p Hp)))).
    + exact (real_plus_opp (tH p Hp)).
Qed.

(* ---------------------------------------------------------- *)
(* 工作马 3（4.6d 最大支·逐 eps 档）：同能量 + Gibbs 腿接口               *)
(*   ⟹ S[p] ≤ S[pb] + eps（∀eps>0）。                                     *)
(*   Gibbs 腿（0 ≤ KL+eps）为诚实接口前提（S08 L2511 real_gibbs_sum_eps   *)
(*   同形；bool 载体实例化见下半节）。链 = Gibbs 腿 + 4.6a 熵亏件换载     *)
(*   + 工作马 1 移项（z := S[pb]+eps）。                                   *)
(* ---------------------------------------------------------- *)
Lemma t13_max_entropy_le_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (tEen p) tE ->
    (forall eps : Real, real_lt real_zero eps ->
       real_le real_zero (real_plus (tKL p Hp) eps)) ->
    forall eps : Real, real_lt real_zero eps ->
    real_le (tH p Hp) (real_plus (tH tB tBpos) eps).
Proof.
  intros p Hp Hnormp Henergy Hgibbs eps Heps.
  apply (t13_le_plus_opp_shift (tH p Hp) (real_plus (tH tB tBpos) eps)).
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus (tKL p Hp) eps)
           (real_plus (real_plus (tH tB tBpos) eps) (real_opp (tH p Hp)))).
  - apply (real_eq_trans
             (real_plus (tKL p Hp) eps)
             (real_plus (real_plus (tH tB tBpos) (real_opp (tH p Hp))) eps)
             (real_plus (real_plus (tH tB tBpos) eps) (real_opp (tH p Hp)))).
    + apply (RealSetoid.real_eq_plus_compat_adapt (tKL p Hp)
               (real_plus (tH tB tBpos) (real_opp (tH p Hp))) eps eps).
      * apply real_eq_sym.
        exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
                 real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
                 T T_pos energy p Hp Hnormp Henergy).
      * apply real_eq_refl.
    + apply (real_eq_trans
               (real_plus (real_plus (tH tB tBpos) (real_opp (tH p Hp))) eps)
               (real_plus (tH tB tBpos) (real_plus (real_opp (tH p Hp)) eps))
               (real_plus (real_plus (tH tB tBpos) eps) (real_opp (tH p Hp)))).
      * apply real_eq_sym.
        exact (real_plus_assoc (tH tB tBpos) (real_opp (tH p Hp)) eps).
      * apply (real_eq_trans
                 (real_plus (tH tB tBpos) (real_plus (real_opp (tH p Hp)) eps))
                 (real_plus (tH tB tBpos) (real_plus eps (real_opp (tH p Hp))))
                 (real_plus (real_plus (tH tB tBpos) eps) (real_opp (tH p Hp)))).
        -- apply (RealSetoid.real_eq_plus_compat_adapt (tH tB tBpos) (tH tB tBpos)
                    (real_plus (real_opp (tH p Hp)) eps)
                    (real_plus eps (real_opp (tH p Hp)))
                    (real_eq_refl (tH tB tBpos))
                    (real_plus_comm (real_opp (tH p Hp)) eps)).
        -- exact (real_plus_assoc (tH tB tBpos) eps (real_opp (tH p Hp))).
  - exact (Hgibbs eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 总装件 1：temp_energy_dual_closed_real（抽象载体对位骨架 sigT 形）。    *)
(*   支A（归一化）+ 支B（能量口）+ 支C（最大支逐 eps 档，Gibbs 腿为       *)
(*   逐支接口前提）+ 支D1（唯一支 KL 归零档）全闭；pb 正性证人升 sigT      *)
(*   第二见证位（real_entropy_dist 前提位所需，req 层模板同构）。          *)
(* ---------------------------------------------------------- *)
Theorem temp_energy_dual_closed_real :
  sigT (fun pb : S -> Real =>
    sigT (fun Hpb : forall s : S, real_lt real_zero (pb s) =>
      prod (real_eq (real_sum_over_S pb) real_one)
        (prod (real_eq (tEen pb) tE)
          (prod (forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
                  real_eq (real_sum_over_S p) real_one ->
                  real_eq (tEen p) tE ->
                  (forall eps : Real, real_lt real_zero eps ->
                     real_le real_zero (real_plus (tKL p Hp) eps)) ->
                  forall eps : Real, real_lt real_zero eps ->
                  real_le (tH p Hp) (real_plus (tH pb Hpb) eps))
                (forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
                  real_eq (real_sum_over_S p) real_one ->
                  real_eq (tEen p) tE ->
                  real_eq (tH p Hp) (tH pb Hpb) ->
                  real_eq (tKL p Hp) real_zero))))).
Proof.
  exists tB. exists tBpos.
  split.
  - exact (real_boltzmann_dist_temp_normalized S real_sum_over_S
             real_sum_pos_preserved real_sum_over_S_ext real_sum_over_S_linear
             T T_pos energy).
  - split.
    + exact (real_eq_refl (tEen tB)).
    + split.
      * intros p Hp Hnormp Henergy Hgibbs eps Heps.
        exact (t13_max_entropy_le_eps p Hp Hnormp Henergy Hgibbs eps Heps).
      * intros p Hp Hnormp Henergy HeqH.
        exact (t13_entropy_eq_kl_zero p Hp Hnormp Henergy HeqH).
Qed.

End RealTempDual.

(* ============================================================ *)
(* Section RealTempDualBool：bool 载体（两态模型，cons 字面 t13_bstate）  *)
(*   全闭总装。sumf := real_list_sum bool（S08 四接口实例化），Gibbs 腿   *)
(*   由 real_gibbs_inequality_eps（S08）实例化消解，唯一支全点闭由         *)
(*   t1_gibbe2_gibbs_equality_bool（席T1 无条件注入形）完成。              *)
(* ============================================================ *)

(* 两态表（cons 显式构造，免 scope 记法依赖；与 [true; false] 同一项） *)
Definition t13_bstate : list bool := cons true (cons false (@nil bool)).

Section RealTempDualBool.

Variable T0 : Real.
Variable T0_pos : real_lt real_zero T0.
Variable e0 : bool -> Real.

Let bsumf : (bool -> Real) -> Real :=
  fun f : bool -> Real => real_list_sum bool f t13_bstate.
Let bpos : forall f : bool -> Real,
    (forall s : bool, real_lt real_zero (f s)) -> real_lt real_zero (bsumf f) :=
  fun (f : bool -> Real) (Hf : forall s : bool, real_lt real_zero (f s)) =>
    real_list_sum_pos bool f t13_bstate Hf ltac:(discriminate).
Let bext : forall (f g : bool -> Real),
    (forall s : bool, real_eq (f s) (g s)) -> real_eq (bsumf f) (bsumf g) :=
  fun (f g : bool -> Real) (Hfg : forall s : bool, real_eq (f s) (g s)) =>
    real_list_sum_ext bool f g t13_bstate Hfg.
Let blinear : forall (a : Real) (f : bool -> Real),
    real_eq (bsumf (fun s : bool => real_mult a (f s)))
            (real_mult a (bsumf f)) :=
  fun (a : Real) (f : bool -> Real) => real_list_sum_linear bool a f t13_bstate.
Let badd : forall (f g : bool -> Real),
    real_eq (bsumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (bsumf f) (bsumf g)) :=
  fun (f g : bool -> Real) => real_list_sum_add bool f g t13_bstate.

Let bB : bool -> Real :=
  real_boltzmann_dist_temp bool bsumf bpos T0 T0_pos e0.
Let bBpos : forall s : bool, real_lt real_zero (bB s) :=
  real_boltzmann_dist_temp_pos bool bsumf bpos T0 T0_pos e0.
Let bE_T : Real :=
  real_energy_exp_temp bool bsumf bpos T0 T0_pos e0.
Let bH (q : bool -> Real) (Hq : forall s : bool, real_lt real_zero (q s)) : Real :=
  real_entropy_dist bool bsumf q Hq.
Let bKL (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)) : Real :=
  real_KL_temp bool bsumf bpos T0 T0_pos e0 p Hp.
Let bEen (q : bool -> Real) : Real :=
  bsumf (fun s : bool => real_mult (q s) (e0 s)).

Let bBnorm : real_eq (bsumf bB) real_one :=
  real_boltzmann_dist_temp_normalized bool bsumf bpos bext blinear
    T0 T0_pos e0.

Let bBridge (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)) :
    real_eq (bKL p Hp)
            (bsumf (fun s : bool =>
               real_kl_term (p s) (bB s) (Hp s) (bBpos s))) :=
  real_KL_temp_kl_term_bridge bool bsumf bpos bext T0 T0_pos e0 p Hp.

(* ---------------------------------------------------------- *)
(* Gibbs 腿实例化（支C 消解）：real_gibbs_inequality_eps（S08）+          *)
(*   桥换载 ⟹ 0 ≤ bKL p + eps（∀eps>0）。                                 *)
(* ---------------------------------------------------------- *)
Lemma t13_bool_gibbs_leg :
  forall (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (bsumf p) real_one ->
    forall eps : Real, real_lt real_zero eps ->
    real_le real_zero (real_plus (bKL p Hp) eps).
Proof.
  intros p Hp Hnormp eps Heps.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus
              (bsumf (fun s : bool => real_kl_term (p s) (bB s) (Hp s) (bBpos s)))
              eps)
           (real_plus (bKL p Hp) eps)).
  - apply (RealSetoid.real_eq_plus_compat_adapt
             (bsumf (fun s : bool => real_kl_term (p s) (bB s) (Hp s) (bBpos s)))
             (bKL p Hp) eps eps).
    + exact (real_eq_sym _ _ (bBridge p Hp)).
    + apply real_eq_refl.
  - exact (real_gibbs_inequality_eps bool t13_bstate p bB Hp bBpos
             Hnormp bBnorm eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 支C 实例（抽象工作马 3 的 bool 消解）。                                 *)
(* ---------------------------------------------------------- *)
Lemma t13_bool_max_entropy_le_eps :
  forall (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (bsumf p) real_one ->
    real_eq (bEen p) bE_T ->
    forall eps : Real, real_lt real_zero eps ->
    real_le (bH p Hp) (real_plus (bH bB bBpos) eps).
Proof.
  intros p Hp Hnormp Henergy eps Heps.
  exact (t13_max_entropy_le_eps bool bsumf bpos bext blinear badd
           T0 T0_pos e0 p Hp Hnormp Henergy
           (t13_bool_gibbs_leg p Hp Hnormp) eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 支D2 实例（唯一支全点闭）：熵等 ⟹ KL≡0（抽象工作马 2）⟹ 桥换载        *)
(*   ⟹ t1_gibbe2_gibbs_equality_bool（席T1 无条件注入形）逐点完成。        *)
(* ---------------------------------------------------------- *)
Lemma t13_bool_entropy_eq_pointwise :
  forall (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (bsumf p) real_one ->
    real_eq (bEen p) bE_T ->
    real_eq (bH p Hp) (bH bB bBpos) ->
    forall s : bool, real_eq (p s) (bB s).
Proof.
  intros p Hp Hnormp Henergy HeqH s.
  apply (t1_gibbe2_gibbs_equality_bool p bB Hp bBpos Hnormp bBnorm).
  apply (real_eq_trans
           (bsumf (fun s0 : bool =>
              real_kl_term (p s0) (bB s0) (Hp s0) (bBpos s0)))
           (bKL p Hp) real_zero).
  - exact (real_eq_sym _ _ (bBridge p Hp)).
  - exact (t13_entropy_eq_kl_zero bool bsumf bpos bext blinear badd
             T0 T0_pos e0 p Hp Hnormp Henergy HeqH).
Qed.

(* ---------------------------------------------------------- *)
(* 总装件 2：temp_energy_dual_closed_bool（bool 载体全闭 sigT 形）。       *)
(*   支A（归一化）+ 支B（能量口）+ 支C（逐 eps 档，Gibbs 腿已消解，        *)
(*   零接口前提）+ 支D2（唯一支全点闭）——四支全闭， witnessing 档闭环。    *)
(* ---------------------------------------------------------- *)
Theorem temp_energy_dual_closed_bool :
  sigT (fun pb : bool -> Real =>
    sigT (fun Hpb : forall s : bool, real_lt real_zero (pb s) =>
      prod (real_eq (bsumf pb) real_one)
        (prod (real_eq (bEen pb) bE_T)
          (prod (forall (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
                  real_eq (bsumf p) real_one ->
                  real_eq (bEen p) bE_T ->
                  forall eps : Real, real_lt real_zero eps ->
                  real_le (bH p Hp) (real_plus (bH pb Hpb) eps))
                (forall (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
                  real_eq (bsumf p) real_one ->
                  real_eq (bEen p) bE_T ->
                  real_eq (bH p Hp) (bH pb Hpb) ->
                  forall s : bool, real_eq (p s) (pb s)))))).
Proof.
  exists bB. exists bBpos.
  split.
  - exact bBnorm.
  - split.
    + exact (real_eq_refl (bEen bB)).
    + split.
      * intros p Hp Hnormp Henergy eps Heps.
        exact (t13_bool_max_entropy_le_eps p Hp Hnormp Henergy eps Heps).
      * intros p Hp Hnormp Henergy HeqH.
        exact (t13_bool_entropy_eq_pointwise p Hp Hnormp Henergy HeqH).
Qed.

End RealTempDualBool.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                                *)
(* ============================================================ *)
Print Assumptions temp_energy_dual_closed_real.
Print Assumptions temp_energy_dual_closed_bool.
Print Assumptions t13_le_plus_opp_shift.
Print Assumptions t13_entropy_eq_kl_zero.
Print Assumptions t13_max_entropy_le_eps.
Print Assumptions t13_bool_gibbs_leg.
Print Assumptions t13_bool_max_entropy_le_eps.
Print Assumptions t13_bool_entropy_eq_pointwise.
