(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   t22b_not_optimal_of_kl_pos（原 L264，3 句玩具证）                    *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqEntropyUniqueNeg.v *)
(* *)
(* 目的： 定理 4.6c(b) 的显式分歧见证逆否形。 *)
(* 主件： t22b_entropy_max_unique_neg：经逆否与挤压论证的唯一性负向腿。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、UpReqEntropyUniqueTemp、G07_KLWall。 *)
(* 备注： 逆否腿以 sigT 分歧见证显式化；求和正性前提随载体声明。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqEntropyUniqueNeg.v —— 席T22b：定理 4.6c (b) 显式分歧见证逆否形   *)

(* ------------------------------------------------------------------ *)
(* 【使命】承席T22 精确余留：4.6c 的 (b) 逆否形——                       *)
(*   显式分歧见证（某 s₀ 处 p(s₀) ≠ p_T(s₀)，Set 层 Or (real_lt) 承载）  *)
(*   ⟹ KL(p‖p_T) > 0（严格，G07 klst 两件喂入）                        *)
(*   ⟹ S[p_T] − S[p] > 0（严格熵亏，T6b real_entropy_deficit_kl_temp    *)
(*   反解恒等式沿 real_lt 运输）                                        *)
(*   ⟹ p 非最优（S[p] < S[p_T]，real_lt_zero_minus 一跳；熵严格小）。   *)
(*   同席T15 件 5-8 骨架（UpReqMinUniqueTight (b) 腿），换温度族熵亏口。 *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（各步引用件名）】                                     *)
(*   件 N0 le→lt 严格挤压机 t22b_lt_squeeze_le：real_le a b（Set 层     *)
(*     Or (real_lt a b) (real_eq a b) 两支）+ 分歧 Or 见证两支 ⟹        *)
(*     real_lt a b（三分两支各配 real_lt 链：lt 支直达；eq+前向 lt 支    *)
(*     直达；eq+后向 lt 支经 real_lt_compat 运输 + real_lt_irrefl       *)
(*     反证完成——「另支 p(s₀) > p_T(s₀) 走对称」即在第三支内消化）。    *)
(*     对位 real_weak_trich 的正向见证对偶：弱三分自双重否定收敛  *)
(*     于 eq，本机自正向 Or 见证收敛于严格向；对称辅件                  *)
(*     t22b_lt_squeeze_le_sym 一跳同构。                                *)
(*   件 N0b 载体和正性件 t22b_list_sum_pos_ne：list 载体 l₁++s₀::l₂    *)
(*     非空 Witness（destruct l₁ 双支 discriminate），供                *)
(*     real_list_sum_pos 结构位（real_sum_pos_preserved 槽） discharge。 *)
(*   件 N1 严格熵亏尾链（抽象和面，Section）：                          *)
(*     N1a t22b_entropy_deficit_pos_of_kl_pos：Σ kl_term > 0 ⟹          *)
(*       S[p_T]−S[p] > 0。链：T6b 件 5 real_KL_temp_kl_term_bridge      *)
(*       （9 参）⟹ real_lt_compat 运输 ⟹ KL>0；T6b 主件                *)
(*       real_entropy_deficit_kl_temp（13 参，real_minus_r 定义性展开   *)
(*       real_plus Spt (real_opp Sp)，T22 件 1 同槽）⟹ 熵亏恒等 ⟹       *)
(*       real_lt_compat 再运输 ⟹ 严格熵亏。                             *)
(*     N1b t22b_not_optimal_of_kl_pos：Σ kl_term > 0 ⟹ S[p] < S[p_T]    *)
(*       （S07 real_lt_zero_minus 反向差正性桥一跳：0 < y−x ⟹ x < y）。 *)
(*   件 N2 可达形 (b) 单向可比版 t22b_entropy_strict_divergence_le      *)
(*     （list 载体）：逐项 p ≤ p_T（诚实接口前提）+ s₀ 处分歧 Or 见证    *)
(*     ⟹ 件 N0 挤压出前向严格见证 ⟹ G07 klst_kl_sum_strict ⟹ KL>0      *)
(*     ⟹ 件 N1b ⟹ p 非最优。                                           *)
(*   件 N3 可达形 (b) 双向见证版 t22b_entropy_strict_divergence_or      *)
(*     （list 载体）：逐项双向可比（Or 承载）+ s₀ 分歧 Or 见证 ⟹ G07    *)
(*     klst_kl_energy_nonconst ⟹ KL>0 ⟹ 件 N1b ⟹ p 非最优。            *)
(*   件 N4 bool 完成 t22b_entropy_strict_divergence_bool：件 N3 在      *)
(*     [true; false] 载体（s₀ := true，l₁ := []，l₂ := [false]），      *)
(*     结构四件套显式应用席T22 t22_bool_* helpers。                          *)
(*   件 N5 组装件 t22b_entropy_max_unique_neg（bool 载体，prod 双函数   *)
(*     记录——Set 层 And 形零 Prop）：(a) 腿＝席T22 件 3 整链 +          *)
(*     (b) 腿＝件 N4——定理 4.6c 两形合取（同熵 ⟹ 逐点等）×（分歧见证   *)
(*     ⟹ 熵严格小），席T22 精确余留至此闭合。                           *)
(* ------------------------------------------------------------------ *)
(* 【G07 klst 两件逐步对应表（喂入假设位）】                              *)
(*   klst_kl_sum_strict（单向弱序形）↩ 件 N2：                          *)
(*     Hpq  ↦ forall s, real_le (p s) (p_T s)（逐项单向弱序前提）        *)
(*     Hdiv ↦ 件 N0 挤压输出 real_lt (p s₀) (p_T s₀)（前向严格见证）    *)
(*     方向对位：原件 p≤q + p s₀ < q s₀ ⟹ 0 < Σ kl_term(p s, q s)；      *)
(*     本件 p=p、q=p_T，与 T6b 熵亏恒等式 KL(p‖p_T) 同向。              *)
(*   klst_kl_energy_nonconst（双向 Or 形）↩ 件 N3/N4：                   *)
(*     Hpq  ↦ forall s, Or (real_le (p s) (p_T s)) (real_le (p_T s) (p s)) *)
(*     Hdiv ↦ Or (real_lt (p s₀) (p_T s₀)) (real_lt (p_T s₀) (p s₀))    *)
(*     （分歧 Or 见证显式应用，免挤压；q>p 支由原件                          *)
(*     klst_gibbs_core_strict_neg 内部消化）——与 T15 件 6 同手法。      *)
(* ------------------------------------------------------------------ *)
(* 【Id 层原件对位表（001/ConstructiveWorld.v 4.6c (b) 逆否腿）】        *)
(*   分歧见证 s₀ ↦ Set 层 Or (real_lt …) (real_lt …)（实序不可判定，     *)
(*     显式见证输入；Id 层不等式的构造性承载）                           *)
(*   Id klst 严格正槽 ↦ G07 两件显式应用（对应表见上）                       *)
(*   Id entropy_deficit_kl_temp 反解槽 ↦ T6b 主件 + real_lt_compat 运输  *)
(*   Id 「p 非最优」结论面 ↦ real_lt S[p] S[p_T]（real_lt_zero_minus）   *)
(* ------------------------------------------------------------------ *)
(* 【可达强度如实标注】                                                 *)
(*   ① (b) 形逐项可比前提（件 N2 单向/件 N3 双向）为诚实接口位：去除     *)
(*     等价于对任意实对给序判定见证（LLPO 形），非直觉主义可证（席T15    *)
(*     头注 ② 同款结论）；s₀ 处分歧见证以 Set 层 Or (real_lt) 承载。     *)
(*   ② 挤压机（件 N0）为正向见证对偶件：前提集 {le, Or 见证} 在          *)
(*     eq 支内由 irrefl 反证完成，全程零序判定；third 支的消去是        *)
(*     构造性的（False 消去于 Set 目标合法，S15 先例在案）。            *)
(*   ③ list 载体（件 N2/N3）与抽象和面（件 N1）以「四结构位 discharge     *)
(*     + 全 arity 显式应用」衔接（T15 正典件接 list 载体同定式），零缩水：    *)
(*     熵亏恒等式的物理前提（归一化/同能量）逐字保留，不弱化不加码。     *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（结论面全 real_lt/real_eq；      *)
(*   Or 见证 sigT 形零 Prop 完成；Prop 仅现于反证消费位不外泄）；        *)
(*   全 Qed 完成；零新承认件；G1 表禁词字面零入文（含头注）；            *)
(*   UpReqEntropyUniqueTemp.v / UpReqEntropyDeficitTemp.v / G07 组 /     *)
(*   S 模块全程只读（只消费 .vo）。                                     *)
(* 编译配方（T22 同款，vo 树优先 + Live_X 兜底）：                       *)
(*   pwsh -File _t22b_run.ps1 -Target <件> [-Full]（cpu_guard 包装，     *)
(*   CoreN 7，LoadLimit 65）；预审 -vos 秒审后全量。                     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyUniqueTemp.
Require Import G07_KLWall.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)

(*   real_le a b（Set 层 Or (real_lt a b) (real_eq a b)）+ 分歧 Or 见证  *)
(*   ⟹ real_lt a b。三分支：lt 直达／eq+前向 lt 直达／eq+后向 lt 经      *)
(*   real_lt_compat 运输 + real_lt_irrefl 反证完成（对称支内部消化）。   *)
(* ============================================================ *)

Lemma t22b_lt_squeeze_le :
  forall a b : Real,
    real_le a b ->
    Or (real_lt a b) (real_lt b a) ->
    real_lt a b.
Proof.
  intros a b Hle Hdiv.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - destruct Hdiv as [Hlt | Hlt'].
    + exact Hlt.
    + exact (match real_lt_irrefl b
               (RealSetoid.real_lt_compat b b a b
                  (real_eq_refl b) Heq Hlt') with end).
Qed.

(* 对称辅件：弱序反向（real_le b a）+ 分歧 Or 见证 ⟹ 后向严格。 *)
Lemma t22b_lt_squeeze_le_sym :
  forall a b : Real,
    real_le b a ->
    Or (real_lt a b) (real_lt b a) ->
    real_lt b a.
Proof.
  intros a b Hle Hdiv.
  destruct Hdiv as [Hab | Hba].
  - exact (t22b_lt_squeeze_le b a Hle (inr Hab)).
  - exact (t22b_lt_squeeze_le b a Hle (inl Hba)).
Qed.

(* ============================================================ *)
(* 件 N0b：list 载体和正性件（l₁++s₀::l₂ 非空，结构位 discharge 用）     *)
(* ============================================================ *)

Lemma t22b_list_sum_pos_ne :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ f Hf.
  apply (real_list_sum_pos X f (l₁ ++ s₀ :: l₂) Hf).
  intro Hc. destruct l₁.
  - discriminate Hc.
  - discriminate Hc.
Qed.

(* list 载体求和面与正性结构位（件 N1 实例化共用，零接口前提） *)
Definition t22b_list_sumf (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) :
  (X -> Real) -> Real :=
  fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂).

Definition t22b_list_sum_pos_w (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X) :
  forall f : X -> Real,
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (t22b_list_sumf X l₁ s₀ l₂ f) :=
  fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
    t22b_list_sum_pos_ne X l₁ s₀ l₂ f Hf.

(* ============================================================ *)
(* Section RealEntropyUniqueNeg：求和面/温度/能量参数照                  *)
(*   UpReqTempDefs Section 同名同序（供 T6b 两件全 arity 显式应用；          *)
(*   同 Section 先定义件只吃自身 forall 口——T22 卡坑 1）。               *)
(* ============================================================ *)
Section RealEntropyUniqueNeg.

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

(* ---------------------------------------------------------- *)
(* 件 N1a：严格熵亏尾链——Σ kl_term > 0 ⟹ S[p_T] − S[p] > 0              *)
(*   链：T6b 件 5 桥（KL 分布拉零规范形）⟹ real_lt_compat 运输 ⟹        *)
(*   KL > 0 ⟹ T6b 主件熵亏恒等（real_minus_r 定义性展开                  *)
(*   real_plus Spt (real_opp Sp)，Id S04 L3903 槽）⟹ 再运输 ⟹ 严格熵亏。 *)
(* ---------------------------------------------------------- *)
Theorem t22b_entropy_deficit_pos_of_kl_pos :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_lt real_zero
      (real_sum_over_S (fun s : S =>
         real_kl_term (p s)
           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s)
           (Hp s)
           (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s))) ->
    real_lt real_zero
      (real_plus
         (real_entropy_dist S real_sum_over_S
            (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy)
            (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
               T T_pos energy))
         (real_opp (real_entropy_dist S real_sum_over_S p Hp))).
Proof.
  intros p Hp Hnormp Henergy Hkl.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S pT HpT).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：KL 分布拉零规范形桥（T6b 件 5，全 arity 9 参显式应用） *)
  assert (Hbrid : real_eq KL
                    (real_sum_over_S (fun s : S =>
                       real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp). }
  (* 步 2：KL > 0（沿桥自 Σ kl_term 面运输） *)
  assert (HKLpos : real_lt real_zero KL).
  { exact (RealSetoid.real_lt_compat real_zero real_zero
             (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
             KL
             (real_eq_refl real_zero)
             (real_eq_sym KL
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                Hbrid)
             Hkl). }
  (* 步 3：熵亏恒等（T6b 主件，全 arity 13 参显式应用；real_minus_r 定义性    *)
  (*   展开为 real_plus Spt (real_opp Sp)——T22 件 1 同槽对位） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnormp Henergy). }
  (* 步 4：沿熵亏恒等运输：S[p_T] − S[p] > 0（严格熵亏） *)
  exact (RealSetoid.real_lt_compat real_zero real_zero
           KL (real_plus Spt (real_opp Sp))
           (real_eq_refl real_zero)
           (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef) HKLpos).
Qed.

(* ---------------------------------------------------------- *)
(* 件 N1b：非最优尾链——Σ kl_term > 0 ⟹ S[p] < S[p_T]（熵严格小）         *)
(*   一跳：S07 real_lt_zero_minus（0 < y − x ⟹ x < y，eps 见证不变）。   *)
(* ---------------------------------------------------------- *)
Theorem t22b_not_optimal_of_kl_pos :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_lt real_zero
      (real_sum_over_S (fun s : S =>
         real_kl_term (p s)
           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s)
           (Hp s)
           (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
              T T_pos energy s))) ->
    real_lt (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)).
Proof.
  intros p Hp Hnormp Henergy Hkl.
  apply (real_lt_zero_minus           (real_entropy_dist S real_sum_over_S p Hp)           (real_entropy_dist S real_sum_over_S              (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved                 T T_pos energy)              (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved                 T T_pos energy))).
  exact (t22b_entropy_deficit_pos_of_kl_pos p Hp Hnormp Henergy Hkl).
Qed.

End RealEntropyUniqueNeg.

(* ============================================================ *)
(* 件 N2：可达形 (b) 单向可比版（list 载体，klst_kl_sum_strict 喂入）     *)
(*   逐项 p ≤ p_T（诚实接口前提）+ s₀ 处分歧 Or 见证 ⟹ 件 N0 挤压出      *)
(*   前向严格见证 ⟹ G07 klst_kl_sum_strict ⟹ KL>0 ⟹ 件 N1b ⟹ p 非最优。 *)
(*   方向对位：klst 原件吃 p≤q + p s₀ < q s₀；本件 p=p、q=p_T，          *)
(*   与 T6b 熵亏恒等式 KL(p‖p_T) 同向（余留任务书警示槽已对位）。        *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_le :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (T : Real) (T_pos : real_lt real_zero T) (energy : X -> Real)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (t22b_list_sumf X l₁ s₀ l₂ p) real_one ->
  real_eq (t22b_list_sumf X l₁ s₀ l₂ (fun s : X => real_mult (p s) (energy s)))
          (real_energy_exp_temp X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy) ->
  (forall s : X,
     real_le (p s)
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)) ->
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀))
      (real_lt (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
               (p s₀))) ->
  real_lt
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂) p Hp)
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂)
       (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
       (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)).
Proof.
  intros X l₁ s₀ l₂ T T_pos energy p Hp Hnormp Henergy Hpq Hdiv.
  (* 步 1：p_T 归一化（list 载体实例，normalized 件 8 参显式应用） *)
  assert (Hnormq : real_eq
                     (t22b_list_sumf X l₁ s₀ l₂
                        (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                           (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂)
             (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
             T T_pos energy). }
  (* 步 2：le→lt 严格挤压（件 N0）：分歧 Or 见证 ⟹ 前向严格见证 *)
  assert (Hdiv' : real_lt (p s₀)
                    (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                       (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)).
  { exact (t22b_lt_squeeze_le (p s₀)
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
             (Hpq s₀) Hdiv). }
  (* 步 3：KL > 0（G07 klst_kl_sum_strict 显式应用：逐项 p≤p_T + s₀ 严格） *)
  assert (Hkl : real_lt real_zero
                  (t22b_list_sumf X l₁ s₀ l₂
                     (fun s : X =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)))).
  { exact (klst_kl_sum_strict X l₁ s₀ l₂ p
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hpq Hnormp Hnormq Hdiv'). }
  (* 步 4：非最优（件 N1b list 实例：KL>0 ⟹ 熵严格小） *)
  exact (t22b_not_optimal_of_kl_pos X (t22b_list_sumf X l₁ s₀ l₂)
           (t22b_list_sum_pos_w X l₁ s₀ l₂)
           (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
              real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
           (fun (a : Real) (f : X -> Real) =>
              real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
           (fun f g : X -> Real => real_list_sum_add X f g (l₁ ++ s₀ :: l₂))
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N3：可达形 (b) 双向见证版（list 载体，klst_kl_energy_nonconst 喂入） *)
(*   逐项双向可比（Or 承载，诚实接口位）+ s₀ 分歧 Or 见证 ⟹ G07 双向件    *)
(*   显式应用（q>p 支原件内部消化，免挤压）⟹ KL>0 ⟹ 件 N1b ⟹ p 非最优。      *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_or :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (T : Real) (T_pos : real_lt real_zero T) (energy : X -> Real)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (t22b_list_sumf X l₁ s₀ l₂ p) real_one ->
  real_eq (t22b_list_sumf X l₁ s₀ l₂ (fun s : X => real_mult (p s) (energy s)))
          (real_energy_exp_temp X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy) ->
  (forall s : X,
     Or (real_le (p s)
                  (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                     (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s))
        (real_le (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                    (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                 (p s))) ->
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀))
      (real_lt (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                  (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s₀)
               (p s₀))) ->
  real_lt
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂) p Hp)
    (real_entropy_dist X (t22b_list_sumf X l₁ s₀ l₂)
       (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
       (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
          (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)).
Proof.
  intros X l₁ s₀ l₂ T T_pos energy p Hp Hnormp Henergy Hpq Hdiv.
  assert (Hnormq : real_eq
                     (t22b_list_sumf X l₁ s₀ l₂
                        (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                           (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized X (t22b_list_sumf X l₁ s₀ l₂)
             (t22b_list_sum_pos_w X l₁ s₀ l₂)
             (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
             T T_pos energy). }
  assert (Hkl : real_lt real_zero
                  (t22b_list_sumf X l₁ s₀ l₂
                     (fun s : X =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                             (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy s)))).
  { exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p
             (real_boltzmann_dist_temp X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos X (t22b_list_sumf X l₁ s₀ l₂)
                (t22b_list_sum_pos_w X l₁ s₀ l₂) T T_pos energy)
             Hpq Hnormp Hnormq Hdiv). }
  exact (t22b_not_optimal_of_kl_pos X (t22b_list_sumf X l₁ s₀ l₂)
           (t22b_list_sum_pos_w X l₁ s₀ l₂)
           (fun (f g : X -> Real) (Hfg : forall s : X, real_eq (f s) (g s)) =>
              real_list_sum_ext X f g (l₁ ++ s₀ :: l₂) Hfg)
           (fun (a : Real) (f : X -> Real) =>
              real_list_sum_linear X a f (l₁ ++ s₀ :: l₂))
           (fun f g : X -> Real => real_list_sum_add X f g (l₁ ++ s₀ :: l₂))
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N4：可达形 (b) bool 完成——件 N3 在 [true; false] 载体的实例        *)
(*   （s₀ := true，l₁ := []，l₂ := [false]；结构四件套显式应用席T22          *)
(*   t22_bool_* helpers；[] ++ true :: [false] 与 [true; false] 定义     *)
(*   可转换，exact 直过——T15 卡定式）。                                  *)
(* ============================================================ *)
Theorem t22b_entropy_strict_divergence_bool :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (t22_bool_sumf p) real_one ->
  real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
          (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
  (forall s : bool,
     Or (real_le (p s)
                  (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                     T T_pos energy s))
        (real_le (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy s)
                 (p s))) ->
  (Or (real_lt (p true)
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy true))
      (real_lt (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy true)
               (p true))) ->
  real_lt
    (real_entropy_dist bool t22_bool_sumf p Hp)
    (real_entropy_dist bool t22_bool_sumf
       (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
          T T_pos energy)
       (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
          T T_pos energy)).
Proof.
  intros energy T T_pos p Hp Hnormp Henergy Hpq Hdiv.
  assert (Hnormq : real_eq
                     (t22_bool_sumf
                        (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                           T T_pos energy))
                     real_one).
  { exact (real_boltzmann_dist_temp_normalized bool t22_bool_sumf t22_bool_sum_pos
             t22_bool_sum_ext t22_bool_sum_linear T T_pos energy). }
  assert (Hkl : real_lt real_zero
                  (t22_bool_sumf
                     (fun s : bool =>
                        real_kl_term (p s)
                          (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                             T T_pos energy s)
                          (Hp s)
                          (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                             T T_pos energy s)))).
  { exact (klst_kl_energy_nonconst bool [] true [false] p
             (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                T T_pos energy)
             Hp
             (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                T T_pos energy)
             Hpq Hnormp Hnormq Hdiv). }
  exact (t22b_not_optimal_of_kl_pos bool t22_bool_sumf t22_bool_sum_pos
           t22_bool_sum_ext t22_bool_sum_linear t22_bool_sum_add
           T T_pos energy p Hp Hnormp Henergy Hkl).
Qed.

(* ============================================================ *)
(* 件 N5：组装件（bool 载体，prod 双函数记录——Set 层 And 形零 Prop）      *)
(*   定理 4.6c 两形合取载体：(a) 腿＝席T22 件 3（同熵+同能量 ⟹ 逐点等，  *)
(*   零接口前提整链消解）× (b) 腿＝件 N4（逐项可比 + s₀ 分歧见证 ⟹       *)
(*   熵严格小）。席T22 精确余留（(b) 逆否形）至此与 (a) 形合流闭合。      *)
(* ============================================================ *)
Theorem t22b_entropy_max_unique_neg :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (t22_bool_sumf p) real_one ->
  real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
          (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
  prod
    (real_eq (real_entropy_dist bool t22_bool_sumf p Hp)
             (real_entropy_dist bool t22_bool_sumf
                (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)) ->
     forall s : bool,
       real_eq (p s)
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy s))
    ((forall s : bool,
        Or (real_le (p s)
                     (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                        T T_pos energy s))
           (real_le (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                       T T_pos energy s)
                    (p s))) ->
     Or (real_lt (p true)
                 (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy true))
        (real_lt (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                    T T_pos energy true)
                 (p true)) ->
     real_lt (real_entropy_dist bool t22_bool_sumf p Hp)
             (real_entropy_dist bool t22_bool_sumf
                (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                   T T_pos energy))).
Proof.
  intros energy T T_pos p Hp Hnormp Henergy.
  split.
  - exact (t22_entropy_max_unique_temp_bool energy T T_pos p Hp Hnormp Henergy).
  - exact (t22b_entropy_strict_divergence_bool energy T T_pos p Hp Hnormp Henergy).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                              *)
(* ============================================================ *)

Print Assumptions t22b_lt_squeeze_le.
Print Assumptions t22b_lt_squeeze_le_sym.
Print Assumptions t22b_list_sum_pos_ne.
Print Assumptions t22b_entropy_deficit_pos_of_kl_pos.
Print Assumptions t22b_not_optimal_of_kl_pos.
Print Assumptions t22b_entropy_strict_divergence_le.
Print Assumptions t22b_entropy_strict_divergence_or.
Print Assumptions t22b_entropy_strict_divergence_bool.
Print Assumptions t22b_entropy_max_unique_neg.
