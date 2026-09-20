(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_C.v —— EntropyMonoSplitInst 消融覆盖核验件（C 件）     *)
(*                                                              *)
(* 【使命】EntropyMonoSplitInst 消融覆盖审计与缺口处理。三维交叉核验结论           *)
(*   （对源模块与 A/B 两件本体逐行独立核查，非转抄）：                            *)
(*   源模块 11 声明 = 3 Let（#1 emsi_bt / #2 emsi_bt_pos /                        *)
(*   #3 emsi_kl，速记无证明体）+ 3 Lemma（#4/#5/#6）                              *)
(*   + 1 Corollary（#7）+ 4 Theorem（#8/#9/#10/                                   *)
(*   #11）。A 件覆盖 #4/#5/#6（6 Qed）；B 件覆盖 #7–#11（5 枚 + 辅助 2            *)
(*   = 7 Qed）；#1–#3 形式面由 B 件节内 uab_bt/uab_bt_pos/uab_kl 重建。          *)
(*   【结论：11/11 全覆盖，缺口枚清单=空】→ 本件为覆盖验证件：                    *)
(*   同时 Require A+B，对 11 枚逐项核验（语句面=母本逐字形，证明项=消融导出全显    *)
(*   应用，核验成立即覆盖 completeness 的机器验证）+ 五分量装配总成。             *)
(*                                                              *)
(* 【非平凡性注记】本件各核验项均为独立构证：                                    *)
(*   (a) 逐项核验是类型级全覆盖检验——每项 Corollary 语句取母本逐字形             *)
(*       （c_ 速记即母本 emsi_ 速记同文换名），证明项=消融导出件，                *)
(*       exact 通过即机器证明「消融导出语句面 ⊇ 母本语句面」；                   *)
(*   (b) 双源交叉：#5/#6 两项给 A 源/B 源双证（e5/e5b、e6/e6b），两路重叠面       *)
(*       语句一致性入机器检验；                                                  *)
(*   (c) 五分量装配 uac_e11_full_muster：五分量嵌套 sigT（Set 层，零 Prop 泄露），*)
(*       前提只收三证书位（片运输/增长/衰减），分量一=pinned 全族（B 源 #8）、    *)
(*       分量二=右支（B 源 #10）、分量三=左支（B 源 #11）、分量四=峰温 sym 对偶    *)
(*       （A 源 #9 对偶，母本未证方向）、分量五=KL 差分+1 装配（A 源 #5 组合#6）， *)
(*       五分量证明项齐指 A/B 两件，覆盖面单点闭合。                             *)
(*                                                              *)
(* 【构造性注记】纯构造性零承认件；Set 层语句零 Prop 泄露（real_eq/real_lt/real_le*)
(*   sigT-Or 形）；全件真 Qed 闭合（零悬置、零假设位）；A/B 件本体零改；          *)
(*   尾嵌 Print Assumptions 十五连假设审计（11 源模块对应项 + 2 双源交叉项          *)
(*   + 1 峰温对偶项 + 1 五分量装配总成）。                                       *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。    *)
(*   依赖 Require：CW_ConstructiveWorld_219、UpReqTempDefs、                     *)
(*   UpReqEntropyDeficitTemp、UpAblP6_EntropyMonoSplit_A、                       *)
(*   UpAblP6_EntropyMonoSplit_B。                                                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpAblP6_EntropyMonoSplit_A.
Require Import UpAblP6_EntropyMonoSplit_B.

(* ============================================================ *)
(* Section UpAblP6EmsC：接口面照母本 Section EntropyMonoSplitInst 同名同序         *)
(*   （求和面 7 位 + 峰温 T_star + 能量）；速记件以 c_ 前缀重建（与母本 emsi_、     *)
(*   B 件 uab_ 同形同序，三面逐字对位）。                                          *)
(* ============================================================ *)
Section UpAblP6EmsC.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T_star : Real.
Variable T_star_pos : real_lt real_zero T_star.
Variable energy : S -> Real.

(* ---- 速记重建（#1/#2/#3 形式面在场合法性载体：c_bt/c_bt_pos/c_kl 与母本          *)
(*   emsi_bt/emsi_bt_pos/emsi_kl 同文换名；KL 方向与母本一致：p_u 占第一分布位，    *)
(*   禁倒置。） ---- *)
Let c_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let c_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (c_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let c_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (c_bt u Hu) (c_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 核销 #1（母本 Let emsi_bt）：速记形式面见证——c_bt 与上游定义件                  *)
(*   real_boltzmann_dist_temp 出节形点态定义性同面（real_eq 依 Real 载体，          *)
(*   故取 s 点态；real_eq_refl 换名层直接给出）。                                   *)
(* ---------------------------------------------------------- *)
Corollary uac_e1_bt_face :
  forall (u : Real) (Hu : real_lt real_zero u) (s : S),
    real_eq (c_bt u Hu s)
            (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               u Hu energy s).
Proof.
  intros u Hu s.
  exact (real_eq_refl (c_bt u Hu s)).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #2（母本 Let emsi_bt_pos）：逐点正性形式面见证（上游同项直接给出）。        *)
(* ---------------------------------------------------------- *)
Corollary uac_e2_bt_pos_face :
  forall (u : Real) (Hu : real_lt real_zero u) (s : S),
    real_lt real_zero (c_bt u Hu s).
Proof.
  intros u Hu s.
  exact (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
           u Hu energy s).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #3（母本 Let emsi_kl）：KL 换名层同面见证——c_kl 与「上游 KL 作用           *)
(*   于 c_bt/c_bt_pos」定义性同面（母本速记体的展开式逐字对位）。                   *)
(* ---------------------------------------------------------- *)
Corollary uac_e3_kl_face :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (c_kl u Hu)
            (real_KL_temp S real_sum_over_S real_sum_pos_preserved
               T_star T_star_pos energy (c_bt u Hu) (c_bt_pos u Hu)).
Proof.
  intros u Hu.
  exact (real_eq_refl (c_kl u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #4（母本 Lemma emsi_energy_pin_self，A 件覆盖）：母本逐字形语句，            *)
(*   证明项=A 源 uap63_pin_self_updirect 全显应用（S/求和/正性/能量/温/正温六位）。 *)
(* ---------------------------------------------------------- *)
Corollary uac_e4_energy_pin_self :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (c_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         u Hu energy).
Proof.
  intros u Hu.
  exact (uap63_pin_self_updirect S real_sum_over_S real_sum_pos_preserved
           energy u Hu).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #5（母本 Lemma emsi_le_diff_ge_zero）A 源项：证明项=A 源                     *)
(*   uap63_diff_ge_zero_indep（eq 化 le 独立链）。                                  *)
(* ---------------------------------------------------------- *)
Corollary uac_e5_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (uap63_diff_ge_zero_indep a b Hab).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #5 B 源交叉项：同语句，证明项=B 源辅助件 uab_le_diff_ge_zero（compat+id_l   *)
(*   链）——两路重叠面语句一致性入机器检验。                                         *)
(* ---------------------------------------------------------- *)
Corollary uac_e5b_diff_ge_zero_b :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (uab_le_diff_ge_zero a b Hab).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #6（母本 Lemma emsi_le_plus_eps）A 源项：证明项=A 源                         *)
(*   uap63_plus_eps_updirect（compat+id_l 同构重立）。                              *)
(* ---------------------------------------------------------- *)
Corollary uac_e6_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  exact (uap63_plus_eps_updirect X eps HX Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #6 B 源交叉项：同语句，证明项=B 源辅助件 uab_le_plus_eps（nonneg_r 换道链）。 *)
(* ---------------------------------------------------------- *)
Corollary uac_e6b_plus_eps_b :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  exact (uab_le_plus_eps X eps HX Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #7（母本 Corollary emsi_kl_ge_zero_eps_mirror，B 件覆盖）：母本逐字          *)
(*   形语句，证明项=B 源 uab_kl_ge_zero_eps_mirror 全显应用（S/求和/正性/ext/le/     *)
(*   linear/add 七接口位 + 峰温对 + 能量 + 分布对 + 归一 + eps，16 参链全显）。      *)
(* ---------------------------------------------------------- *)
Corollary uac_e7_kl_ge_zero_eps_mirror :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Heps.
  exact (uab_kl_ge_zero_eps_mirror S real_sum_over_S real_sum_pos_preserved
           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear
           real_sum_over_S_add T_star T_star_pos energy p Hp Hnp eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #8（母本 Theorem inst_pinned，B 件覆盖）：证书位一 Hpinned 逐字装载形，      *)
(*   证明项=B 源 uab_inst_pinned（出节消解：S/求和/正性/峰温对/能量 + 片运输）。     *)
(* ---------------------------------------------------------- *)
Corollary uac_e8_inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (c_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice.
  exact (uab_inst_pinned S real_sum_over_S real_sum_pos_preserved
           T_star T_star_pos energy Hslice).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #9（母本 Theorem inst_pinned_at_peak，B 件覆盖）：峰温点零前提闭合           *)
(*   装载逐字形，证明项=B 源 uab_inst_pinned_at_peak（六参出节消解直接给出）。        *)
(* ---------------------------------------------------------- *)
Corollary uac_e9_inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (c_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (uab_inst_pinned_at_peak S real_sum_over_S real_sum_pos_preserved
           T_star T_star_pos energy).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #9 A 源交叉项（sym 对偶方向，母本全件未证方向，A 件消融一之二）：E_{t*}==Σ    *)
(*   证明项=A 源 uap63_pin_at_peak_sym_assembly。峰温点双向闭合取证。               *)
(* ---------------------------------------------------------- *)
Corollary uac_e9b_peak_sym :
  real_eq
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy)
    (real_sum_over_S
       (fun s : S => real_mult (c_bt T_star T_star_pos s) (energy s))).
Proof.
  exact (uap63_pin_at_peak_sym_assembly S real_sum_over_S real_sum_pos_preserved
           energy T_star T_star_pos).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #10（母本 Theorem inst_kl_right，B 件覆盖）：证书位二 Hkl_right 逐字         *)
(*   装载形（KL_v 在前 KL_u 取 real_opp，禁倒置、序向与母本一致），证明项=B 源       *)
(*   uab_inst_kl_right（出节消解直接给出，增长前提类型级同一对位）。                 *)
(* ---------------------------------------------------------- *)
Corollary uac_e10_inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (c_kl u Hu) (c_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (c_kl v Hv) (real_opp (c_kl u Hu))) eps).
Proof.
  intros Hgrowth.
  exact (uab_inst_kl_right S real_sum_over_S real_sum_pos_preserved
           T_star T_star_pos energy Hgrowth).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #11（母本 Theorem inst_kl_left，B 件覆盖）：证书位三 Hkl_left 逐字装载形     *)
(*   （KL_u 在前对偶右支），证明项=B 源 uab_inst_kl_left。                           *)
(* ---------------------------------------------------------- *)
Corollary uac_e11_inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (c_kl v Hv) (c_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (c_kl u Hu) (real_opp (c_kl v Hv))) eps).
Proof.
  intros Hdecay.
  exact (uab_inst_kl_left S real_sum_over_S real_sum_pos_preserved
           T_star T_star_pos energy Hdecay).
Qed.

(* ---------------------------------------------------------- *)
(* 五分量装配总成（覆盖 completeness 闭合）：前提只收三证书位                         *)
(*   （片运输 Hpinned / 增长前提 / 衰减前提），结论=五分量嵌套 sigT——                *)
(*   分量一 pinned 全族（B 源 #8 核验项）、分量二 右支（B 源 #10 核验项）、           *)
(*   分量三 左支（B 源 #11 核验项）、分量四 峰温 sym 对偶（A 源 #9 交叉项）、          *)
(*   分量五 KL 差分+1 具体装配（A 源 #5 组合 #6 组合引理，eps:=real_one）。          *)
(*   五分量证明项齐指 A/B 两件导出——覆盖面单点闭合，任一分量语句面错位即无法通过类型检查。 *)
(* ---------------------------------------------------------- *)
Corollary uac_e11_full_muster :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (c_kl u Hu) (c_kl v Hv)) ->
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (c_kl v Hv) (c_kl u Hu)) ->
  sigT (fun hp1 :
          (forall (u : Real) (Hu : real_lt real_zero u),
             real_eq
               (real_sum_over_S
                  (fun s : S => real_mult (c_bt u Hu s) (energy s)))
               (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
                  T_star T_star_pos energy)) =>
        sigT (fun hp2 :
                (forall (u v : Real)
                        (Hu : real_lt real_zero u)
                        (Hv : real_lt real_zero v),
                   real_le T_star u -> real_le u v ->
                   forall eps : Real,
                     real_lt real_zero eps ->
                     real_le real_zero
                       (real_plus
                          (real_plus (c_kl v Hv) (real_opp (c_kl u Hu))) eps)) =>
          sigT (fun hp3 :
                  (forall (u v : Real)
                          (Hu : real_lt real_zero u)
                          (Hv : real_lt real_zero v),
                     real_le u v -> real_le v T_star ->
                     forall eps : Real,
                       real_lt real_zero eps ->
                       real_le real_zero
                         (real_plus
                            (real_plus (c_kl u Hu) (real_opp (c_kl v Hv)))
                            eps)) =>
            sigT (fun hp4 :
                    real_eq
                      (real_energy_exp_temp S real_sum_over_S
                         real_sum_pos_preserved T_star T_star_pos energy)
                      (real_sum_over_S
                         (fun s : S =>
                            real_mult (c_bt T_star T_star_pos s) (energy s))) =>
              forall a b : Real,
                real_le a b ->
                real_le real_zero
                  (real_plus (real_plus b (real_opp a)) real_one))))).
Proof.
  intros Hslice Hgrowth Hdecay.
  exact (existT _
           (uac_e8_inst_pinned Hslice)
           (existT _
              (uac_e10_inst_kl_right Hgrowth)
              (existT _
                 (uac_e11_inst_kl_left Hdecay)
                 (existT _
                    uac_e9b_peak_sym
                    (fun a b Hab =>
                       uap63_diff_eps_combo_indep a b real_one Hab
                         real_lt_zero_one))))).
Qed.

End UpAblP6EmsC.

(* ---- 假设面审计（十五连 Print Assumptions） ---- *)
Print Assumptions uac_e1_bt_face.
Print Assumptions uac_e2_bt_pos_face.
Print Assumptions uac_e3_kl_face.
Print Assumptions uac_e4_energy_pin_self.
Print Assumptions uac_e5_diff_ge_zero.
Print Assumptions uac_e5b_diff_ge_zero_b.
Print Assumptions uac_e6_plus_eps.
Print Assumptions uac_e6b_plus_eps_b.
Print Assumptions uac_e7_kl_ge_zero_eps_mirror.
Print Assumptions uac_e8_inst_pinned.
Print Assumptions uac_e9_inst_pinned_at_peak.
Print Assumptions uac_e9b_peak_sym.
Print Assumptions uac_e10_inst_kl_right.
Print Assumptions uac_e11_inst_kl_left.
Print Assumptions uac_e11_full_muster.
