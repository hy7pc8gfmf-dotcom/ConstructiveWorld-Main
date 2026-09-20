(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_C.v —— 战役席 PA6-08R2（T218·EMS 合龙审计）C 件        *)
(*                                                              *)
(* 【使命】EntropyMonoSplitInst 消融合龙审计与缺口处理。三维交叉对账结论           *)
(*   （本席独立实勘母件 Live 树 + A/B 两件本体逐行实测，非转抄）：                *)
(*   母件 11 声明 = 3 Let（#1 emsi_bt :81 / #2 emsi_bt_pos :83 /               *)
(*   #3 emsi_kl :86，速记无证明体）+ 3 Lemma（#4 :97 / #5 :117 / #6 :136）      *)
(*   + 1 Corollary（#7 :161）+ 4 Theorem（#8 :193 / #9 :222 / #10 :244 /        *)
(*   #11 :273）。A 件认领 #4/#5/#6（6 Qed）；B 件认领 #7–#11（5 枚 + 辅助 2      *)
(*   = 7 Qed）；#1–#3 形式面由 B 件节内 uab_bt/uab_bt_pos/uab_kl 重建。         *)
(*   【判词：11/11 全覆盖，缺口枚清单=空】→ 按任务书条款，C 件=合龙验证件：       *)
(*   同时 Require A+B，对 11 枚逐格核销（语句面=母本逐字形，证项=消融导出全显    *)
(*   应用，核销成立即覆盖 completeness 的机器验证）+ 一揽子已消融总装。          *)
(*                                                              *)
(* 【非平凡性宣言】本件非转发冒充：                                              *)
(*   (a) 逐格核销是类型级全覆盖检验——每格 Corollary 语句取母本逐字形             *)
(*       （c_ 速记即母本 emsi_ 速记同文换名），证项槽位=消融导出件，              *)
(*       exact 通过即机器证明「消融导出语句面 ⊇ 母本语句面」；                   *)
(*   (b) 双源交叉：#5/#6 两格给 A 源/B 源双证（e5/e5b、e6/e6b），两腿重叠面       *)
(*       语句一致性入机器检验；                                                  *)
(*   (c) 一揽子总装 uac_e11_full_muster：五分量嵌套 sigT（Set 层，零 Prop 泄露），*)
(*       前提只收三证书槽供位（片运输/增长/衰减），分量一=pinned 全族（B 源 #8）、*)
(*       分量二=右支（B 源 #10）、分量三=左支（B 源 #11）、分量四=峰温 sym 对偶    *)
(*       （A 源 #9 对偶腿，母本未证方向）、分量五=KL 差分+1 装配（A 源 #5 组合#6）， *)
(*       五分量证项齐指 A/B 两件，合龙面单点收口。                               *)
(*                                                              *)
(* 【纪律】纯构造性零承认件；Set 层语句零 Prop 泄露（real_eq/real_lt/real_le     *)
(*   sigT-Or 形）；全件真 Qed 收口（零悬置、零假设位）；A/B 件本体零改；          *)
(*   Live 树与 vo_9.1 只读；.vo 只落 /tmp/pa7_work；尾嵌 Print Assumptions       *)
(*   十五连自检段。                                                              *)
(* 编译配方：source Live/toolchain/env.sh 后                                      *)
(*   cd /tmp/pa7_work && bash cpu_guard.sh -- rocq c -Q /tmp/pa7_work ""          *)
(*     -Q /tmp/pa6_side "" -Q /tmp/czn14_union_full ""                            *)
(*     UpAblP6_EntropyMonoSplit_C.v（9.1 live 轨）                                 *)
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
(*   emsi_bt/emsi_bt_pos/emsi_kl 同文换名；KL 方向红线照抄：p_u 占第一分布位，      *)
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
(* 核销 #1（母本 Let emsi_bt :81）：速记形式面证人——c_bt 与上游注册面               *)
(*   real_boltzmann_dist_temp 出节形点态定义性同面（real_eq 依 Real 载体，          *)
(*   故取 s 点态；real_eq_refl 换名层真装）。                                       *)
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
(* 核销 #2（母本 Let emsi_bt_pos :83）：逐点正性形式面证人（上游直击同项）。        *)
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
(* 核销 #3（母本 Let emsi_kl :86）：KL 换名层同面证人——c_kl 与「上游 KL 作用        *)
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
(* 核销 #4（母本 Lemma emsi_energy_pin_self :97，A 件认领）：母本逐字形语句，        *)
(*   证项=A 源 uap63_pin_self_updirect 全显应用（S/求和/正性/能量/温/正温六位）。   *)
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
(* 核销 #5（母本 Lemma emsi_le_diff_ge_zero :117）A 源格：证项=A 源                  *)
(*   uap63_diff_ge_zero_indep（eq 升格独立链）。                                    *)
(* ---------------------------------------------------------- *)
Corollary uac_e5_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (uap63_diff_ge_zero_indep a b Hab).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #5 B 源交叉格：同语句，证项=B 源辅助件 uab_le_diff_ge_zero（compat+id_l     *)
(*   链）——两腿重叠面语句一致性入机器检验。                                         *)
(* ---------------------------------------------------------- *)
Corollary uac_e5b_diff_ge_zero_b :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (uab_le_diff_ge_zero a b Hab).
Qed.

(* ---------------------------------------------------------- *)
(* 核销 #6（母本 Lemma emsi_le_plus_eps :136）A 源格：证项=A 源                      *)
(*   uap63_plus_eps_updirect（compat+id_l 同构复装）。                              *)
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
(* 核销 #6 B 源交叉格：同语句，证项=B 源辅助件 uab_le_plus_eps（nonneg_r 换道链）。  *)
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
(* 核销 #7（母本 Corollary emsi_kl_ge_zero_eps_mirror :161，B 件认领）：母本逐字     *)
(*   形语句，证项=B 源 uab_kl_ge_zero_eps_mirror 全显应用（S/求和/正性/ext/le/       *)
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
(* 核销 #8（母本 Theorem inst_pinned :193，B 件认领）：槽位1 Hpinned 逐字装载形，    *)
(*   证项=B 源 uab_inst_pinned（出节 discharge：S/求和/正性/峰温对/能量 + 片运输）。 *)
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
(* 核销 #9（母本 Theorem inst_pinned_at_peak :222，B 件认领）：峰温点零前提封闭      *)
(*   装载逐字形，证项=B 源 uab_inst_pinned_at_peak（六参 discharge 直喂）。          *)
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
(* 核销 #9 A 源交叉格（sym 对偶方向，母本全件未证方向，A 件甲2 腿）：E_{t*}==Σ        *)
(*   证项=A 源 uap63_pin_at_peak_sym_assembly。峰温点双向闭合合龙取证。             *)
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
(* 核销 #10（母本 Theorem inst_kl_right :244，B 件认领）：槽位2 Hkl_right 逐字       *)
(*   装载形（KL_v 在前 KL_u 取 real_opp，禁倒置红线照抄），证项=B 源                 *)
(*   uab_inst_kl_right（出节 discharge 直喂，增长供位类型级同一对位）。              *)
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
(* 核销 #11（母本 Theorem inst_kl_left :273，B 件认领）：槽位3 Hkl_left 逐字装载形   *)
(*   （KL_u 在前镜像右支），证项=B 源 uab_inst_kl_left。                             *)
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
(* 一揽子已消融总装（覆盖 completeness 收口）：前提只收三证书槽供位                   *)
(*   （片运输 Hpinned 供位 / 增长供位 / 衰减供位），结论=五分量嵌套 sigT——           *)
(*   分量一 pinned 全族（B 源 #8 核销格）、分量二 右支（B 源 #10 核销格）、           *)
(*   分量三 左支（B 源 #11 核销格）、分量四 峰温 sym 对偶（A 源 #9 交叉格）、          *)
(*   分量五 KL 差分+1 具体装配（A 源 #5 组合 #6 组合桥，eps:=real_one）。            *)
(*   五分量证项齐指 A/B 两件导出——合龙面单点收口，任一分量语句面错位即本件拒编。     *)
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

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明十五连） ---- *)
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
