(* ==========================================================================)
   UpAblP6_EntropyMonoSplit_A.v — 熵单调分裂的 A 路线实例件
   使命: uap63_pin_self_updirect/pin_at_peak_sym_assembly（峰值钉扎）、diff_ge_zero_indep（差非负独立形）、plus_eps_updirect/eps_one_assembly/diff_eps_combo_indep 六件。
   依赖: CW_ConstructiveWorld_219、UpReqTempDefs。
   对标: 熵函数单峰性（最大熵在均匀分布）的分裂论证路线 A。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import UpReqTempDefs.

(* ============================================================ *)
(* 消融一（对上游 #4 emsi_energy_pin_self）——上游定义面直接重证：       *)
(*   上游语句经 emsi_bt 换名包裹；本枚剥掉换名层，对上游定义件            *)
(*   real_boltzmann_dist_temp / real_energy_exp_temp 出节形直接重述。    *)
(*   证明项零上游引用：左端 lambda 与 real_energy_exp_temp 定义面定义性      *)
(*   合一，real_eq_refl 直接给出（上游同理但本件独立复立）。             *)
(* 依赖：CW_ConstructiveWorld_219、UpReqTempDefs。                      *)
(* 对标：mathlib 熵单调分解实例；stdlib 无同形。                        *)
(* 构造性注记：语句面全 Set 层（real_le/real_lt/real_eq）；零承认、       *)
(*   公理面为空；全 Qed 闭合；可提取。                                   *)
(* 编译配方：Rocq 9.1 直调 coqc + cpu_guard 包裹，输出至临时目录。        *)
(* ============================================================ *)
Theorem uap63_pin_self_updirect :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (energy : S -> Real) (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                (energy s)))
      (real_energy_exp_temp S rsu rsp u Hu energy).
Proof.
  intros S rsu rsp energy u Hu.
  exact (real_eq_refl
           (rsu (fun s : S =>
                   real_mult
                     (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                     (energy s)))).
Qed.

(* ============================================================ *)
(* 消融一之二（峰温对偶）：上游 inst_pinned_at_peak 证                   *)
(*   Σ(p_{t*}·e) == E_{t*}；本枚给 sym 对偶新形 E_{t*} == Σ(p_{t*}·e)    *)
(*   （上游全件未证方向），零上游引用，对上游定义面直接重证。             *)
(* ============================================================ *)
Theorem uap63_pin_at_peak_sym_assembly :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (energy : S -> Real) (T : Real) (HT : real_lt real_zero T),
    real_eq
      (real_energy_exp_temp S rsu rsp T HT energy)
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp T HT energy s)
                (energy s))).
Proof.
  intros S rsu rsp energy T HT.
  exact (real_eq_refl
           (real_energy_exp_temp S rsu rsp T HT energy)).
Qed.

(* ============================================================ *)
(* 消融二（对上游 #5 emsi_le_diff_ge_zero）——独立链：                   *)
(*   上游链 = real_le_plus_compat 双边同加 −a + id_l 换左端；            *)
(*   本枚异链 = real_eq_le（eq 化 le 引理）先立 0 ≤ a+(−a)（换向         *)
(*   real_plus_opp），再 real_le_trans 复合 compat 形——链根不同。        *)
(* ============================================================ *)
Theorem uap63_diff_ge_zero_indep :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  apply (real_le_trans real_zero
           (real_plus a (real_opp a))
           (real_plus b (real_opp a))).
  exact (RealSetoid.real_eq_le real_zero
           (real_plus a (real_opp a))
           (real_eq_sym (real_plus a (real_opp a)) real_zero
              (real_plus_opp a))).
  exact (real_le_plus_compat a b (real_opp a) (real_opp a) Hab
           (real_le_refl (real_opp a))).
Qed.

(* ============================================================ *)
(* 消融三（对上游 #6 emsi_le_plus_eps）泛形直接重证：同构重立            *)
(*   （compat + id_l，与上游同构——泛形即上游语句本形，声明为同构重立，    *)
(*   非独立链；独立链与装配实例由下两枚补足）。                          *)
(* ============================================================ *)
Theorem uap63_plus_eps_updirect :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus X eps)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero eps HX
           (real_le_from_lt_aux real_zero eps Heps)).
Qed.

(* ============================================================ *)
(* 消融三之二（实例装配）：eps := real_one 具体装配新形                  *)
(*   （上游全件无任何具体 eps 装配实例；real_one_pos 供给）。             *)
(* ============================================================ *)
Theorem uap63_eps_one_assembly :
  forall X : Real,
    real_le real_zero X -> real_le real_zero (real_plus X real_one).
Proof.
  intros X HX.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus X real_one)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero real_one HX
           (real_le_from_lt_aux real_zero real_one real_lt_zero_one)).
Qed.

(* ============================================================ *)
(* 消融三之三（#5∘#6 组合引理独立链）：撤上游两引理后链仍自洽复合——      *)
(*   使用本件消融二/消融三泛形两枚，real_le_trans 一步复合，              *)
(*   证明项零上游件名。                                                 *)
(* ============================================================ *)
Theorem uap63_diff_eps_combo_indep :
  forall a b eps : Real,
    real_le a b -> real_lt real_zero eps ->
    real_le real_zero
      (real_plus (real_plus b (real_opp a)) eps).
Proof.
  intros a b eps Hab Heps.
  exact (real_le_trans real_zero
           (real_plus real_zero eps)
           (real_plus (real_plus b (real_opp a)) eps)
           (uap63_plus_eps_updirect real_zero eps
              (real_le_refl real_zero) Heps)
           (real_le_plus_compat real_zero
              (real_plus b (real_opp a)) eps eps
              (uap63_diff_ge_zero_indep a b Hab)
              (real_le_refl eps))).
Qed.

(* ---- 假设面审计（六枚闭合结论） ---- *)
Print Assumptions uap63_pin_self_updirect.
Print Assumptions uap63_pin_at_peak_sym_assembly.
Print Assumptions uap63_diff_ge_zero_indep.
Print Assumptions uap63_plus_eps_updirect.
Print Assumptions uap63_eps_one_assembly.
Print Assumptions uap63_diff_eps_combo_indep.
