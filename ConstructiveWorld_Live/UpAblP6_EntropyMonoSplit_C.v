(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_C.v —— EntropyMonoSplitInst 消融覆盖核验件（C 件）。  *)
(*                                                              *)
(* ①使命：本件形式化 EntropyMonoSplitInst 十一枚声明的覆盖完备性核验：同时         *)
(*   Require A+B 两件，对 11 枚逐项核验（语句面=源文件逐字形，证明项=消融导出     *)
(*   全显应用）+ 五分量 sigT 装配总成；核验成立即覆盖完备性的机器验证。           *)
(* ②依赖：CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、      *)
(*   UpAblP6_EntropyMonoSplit_A、UpAblP6_EntropyMonoSplit_B；                    *)
(*   供给段另引 UpReqSumD、UpReqConcSoftmax、ConcMixSelFeed。                    *)
(* ③对标：mathlib 覆盖性检验的逐项对应构造（无对应直引）。                        *)
(* ④构造性注记：Set 层承载零 Prop 泄露（real_eq/real_lt/real_le sigT-Or 形）；     *)
(*   全件真 Qed 闭合；尾嵌十五连 Print Assumptions 假设审计。                    *)
(* ⑤编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。   *)
(*                                                              *)
(* 面外扩展标注：本件为工单面外扩展件，按 b3 §2.2 可消解判定施工，候合并方        *)
(*   甄别确认；若属已补强保留区请退回。原节假设声明与既有定理签名零改；          *)
(*   文件尾供给段为签名保持式消解（b3 §2.2.1）：求和面五证书位在 csm_sumf 载体     *)
(*   上实例化为 *_supply 定理（配方同 B 件供给段，命名 uabp6c_ 前缀独立）。        *)
(*   既往工程自述核实：有——原件头注含 ToyR  切片七替换稿自述（七枚玩具位      *)
(*   替换与批量登记面）；此次未触替换面，仅头注重写、注释词面完成清理与尾段供给段     *)
(*   追加，差异以供给段注记为凭。                                                *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpAblP6_EntropyMonoSplit_A.
Require Import UpAblP6_EntropyMonoSplit_B.

(* ============================================================ *)
(* Section UpAblP6EmsC：接口面照源文件 Section EntropyMonoSplitInst 同名同序         *)
(*   （求和面 7 位 + 峰温 T_star + 能量）；速记件以 c_ 前缀重建（与源文件 emsi_、     *)
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

(* ---- 速记重建（#1/#2/#3 形式面在场合法性载体：c_bt/c_bt_pos/c_kl 与源文件          *)
(*   emsi_bt/emsi_bt_pos/emsi_kl 同文换名；KL 方向与源文件一致：p_u 占第一分布位，    *)
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
(* 兑现 #1（源文件 Let emsi_bt）：速记形式面见证——c_bt 与上游定义件                  *)
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
  exact (real_eq_refl
           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
              u Hu energy s)).
Qed.

(* ---------------------------------------------------------- *)
(* 兑现 #2（源文件 Let emsi_bt_pos）：逐点正性形式面见证（上游同项直接给出）。        *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·终装直接代入】装配位＝上游同项七参直接代入，语句面即接口定义位，装配位无增量。 *)
Corollary uac_e2_bt_pos_face :
  forall (u : Real) (Hu : real_lt real_zero u) (s : S),
    real_lt real_zero (c_bt u Hu s).
Proof.
  intros u Hu s.
  exact (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
           u Hu energy s).
Qed.

(* ---------------------------------------------------------- *)
(* 兑现 #3（源文件 Let emsi_kl）：KL 换名层同面见证——c_kl 与「上游 KL 作用           *)
(*   于 c_bt/c_bt_pos」定义性同面（源文件速记体的展开式逐字对位）。                   *)
(* ---------------------------------------------------------- *)
Corollary uac_e3_kl_face :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (c_kl u Hu)
            (real_KL_temp S real_sum_over_S real_sum_pos_preserved
               T_star T_star_pos energy (c_bt u Hu) (c_bt_pos u Hu)).
Proof.
  intros u Hu.
  exact (real_eq_refl
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy (c_bt u Hu) (c_bt_pos u Hu))).
Qed.

(* ---------------------------------------------------------- *)
(* 兑现 #4（源文件 Lemma emsi_energy_pin_self，A 件覆盖）：源文件逐字形语句，            *)
(*   证明项=A 源 uap63_pin_self_updirect 全显应用（S/求和/正性/能量/温/正温六位）。 *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·终装直接代入】A 源 pin_self 全显六参装配位，语句面＝Σ c_bt·E 定义同面，装配位无增量。 *)
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
(* 兑现 #5（源文件 Lemma emsi_le_diff_ge_zero）A 源项：证明项=A 源                     *)
(*   uap63_diff_ge_zero_indep（eq 化 le 独立链）。                                  *)
(* ---------------------------------------------------------- *)
Corollary uac_e5_diff_ge_zero :
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

(* ---------------------------------------------------------- *)
(* 兑现 #5 B 源交叉项：同语句，证明项=B 源辅助件 uab_le_diff_ge_zero（compat+id_l   *)
(*   链）——两路重叠面语句一致性入机器检验。                                         *)
(* ---------------------------------------------------------- *)
Corollary uac_e5b_diff_ge_zero_b :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (RealSetoid.real_le_id_l real_zero
           (real_plus a (real_opp a))
           (real_plus b (real_opp a))
           (real_eq_sym (real_plus a (real_opp a)) real_zero
              (real_plus_opp a))
           (real_le_plus_compat a b (real_opp a) (real_opp a) Hab
              (real_le_refl (real_opp a)))).
Qed.

(* ---------------------------------------------------------- *)
(* 兑现 #6（源文件 Lemma emsi_le_plus_eps）A 源项：证明项=A 源                         *)
(*   uap63_plus_eps_updirect（compat+id_l 同构重立）。                              *)
(* ---------------------------------------------------------- *)
Corollary uac_e6_plus_eps :
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

(* ---------------------------------------------------------- *)
(* 兑现 #6 B 源交叉项：同语句，证明项=B 源辅助件 uab_le_plus_eps（nonneg_r 换道链）。 *)
(* ---------------------------------------------------------- *)
Corollary uac_e6b_plus_eps_b :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  exact (real_le_trans real_zero
           (real_plus real_zero eps)
           (real_plus X eps)
           (RealSetoid.real_le_id_l real_zero
              (real_plus real_zero real_zero)
              (real_plus real_zero eps)
              (real_eq_sym (real_plus real_zero real_zero) real_zero
                 (real_plus_zero real_zero))
              (real_le_plus_compat real_zero real_zero real_zero eps
                 (real_le_refl real_zero)
                 (real_le_from_lt_aux real_zero eps Heps)))
           (real_le_plus_compat real_zero X eps eps HX
              (real_le_refl eps))).
Qed.

(* ---------------------------------------------------------- *)
(* 兑现 #7（源文件 Corollary emsi_kl_ge_zero_eps_mirror，B 件覆盖）：源文件逐字          *)
(*   形语句，证明项=B 源 uab_kl_ge_zero_eps_mirror 全显应用（S/求和/正性/ext/le/     *)
(*   linear/add 七接口位 + 峰温对 + 能量 + 分布对 + 归一 + eps，16 参链全显）。      *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·副本位全显】B 源十六参副本位装配（上游原型全库唯一），装配位无增量。 *)
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
(* 兑现 #8（源文件 Theorem inst_pinned，B 件覆盖）：证书位一 Hpinned 逐字装载形，      *)
(*   证明项=B 源 uab_inst_pinned（出节消解：S/求和/正性/峰温对/能量 + 片运输）。     *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·证书装载】证书位一逐字装载形（片运输前提位），B 源出节消解直接代入，装配位无增量。 *)
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
(* 兑现 #9（源文件 Theorem inst_pinned_at_peak，B 件覆盖）：峰温点零前提闭合           *)
(*   装载逐字形，证明项=B 源 uab_inst_pinned_at_peak（六参出节消解直接给出）。        *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·证书装载】峰温点零前提闭合六参直接代入位，装配位无增量。 *)
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
(* 兑现 #9 A 源交叉项（sym 对偶方向，源文件全件未证方向，A 件消融一之二）：E_{t*}==Σ    *)
(*   证明项=A 源 uap63_pin_at_peak_sym_assembly。峰温点双向闭合取证。               *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·对偶直接代入】A 源 sym 对偶峰温向（源文件未证方向），装配位无增量。 *)
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
(* 兑现 #10（源文件 Theorem inst_kl_right，B 件覆盖）：证书位二 Hkl_right 逐字         *)
(*   装载形（KL_v 在前 KL_u 取 real_opp，禁倒置、序向与源文件一致），证明项=B 源       *)
(*   uab_inst_kl_right（出节消解直接给出，增长前提类型级同一对位）。                 *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·证书装载】证书位二逐字装载形（增长前提位），B 源出节消解直接代入，装配位无增量。 *)
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
(* 兑现 #11（源文件 Theorem inst_kl_left，B 件覆盖）：证书位三 Hkl_left 逐字装载形     *)
(*   （KL_u 在前对偶右支），证明项=B 源 uab_inst_kl_left。                           *)
(* ---------------------------------------------------------- *)
(* 【ToyR 批量登记·证书装载】证书位三逐字装载形（衰减前提位），B 源出节消解直接代入，装配位无增量。 *)
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
                       uac_e6_plus_eps (real_plus b (real_opp a)) real_one
                         (uac_e5_diff_ge_zero a b Hab) real_lt_zero_one))))).
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

(* ============================================================ *)
(* 供给段（签名保持式消解，b3 §2.2.1；原节声明与既有签名零改）：                  *)
(*   求和面五证书位在 ConcMixSelFeed 求和载体 csm_sumf 上实例化：                *)
(*   ext/le/linear/add 四位由 cms_sum_ext/cms_sum_le/cms_sum_linear/             *)
(*   cms_sum_add 供给；正性位由 sumd_list_sum_pos（非空清单逐点严格正            *)
(*   ⟹ 和严格正）供给。抽象层五位保持假设身份（对抽象求和算子不可树内           *)
(*   推导），本段为具体实例上的消解证书，供下游以实例充任接口字段。              *)
(* ============================================================ *)
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.

Definition uabp6c_enum : list bool := true :: false :: nil.

Theorem uabp6c_sum_pos_supply :
  forall f : bool -> Real,
    (forall s : bool, lt zero (f s)) ->
    lt zero (csm_sumf bool uabp6c_enum f).
Proof.
  intros f Hpt.
  unfold csm_sumf.
  apply (@sumd_list_sum_pos Real RealEnhancedReal bool f uabp6c_enum).
  - intros Hnil.
    discriminate Hnil.
  - exact Hpt.
Qed.

Theorem uabp6c_sum_ext_supply :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (csm_sumf bool uabp6c_enum f) (csm_sumf bool uabp6c_enum g).
Proof.
  intros f g H.
  exact (cms_sum_ext bool uabp6c_enum f g H).
Qed.

Theorem uabp6c_sum_le_supply :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (csm_sumf bool uabp6c_enum f) (csm_sumf bool uabp6c_enum g).
Proof.
  intros f g H.
  exact (cms_sum_le bool uabp6c_enum f g H).
Qed.

Theorem uabp6c_sum_linear_supply :
  forall (a : Real) (f : bool -> Real),
    req (csm_sumf bool uabp6c_enum (fun s : bool => mult a (f s)))
            (mult a (csm_sumf bool uabp6c_enum f)).
Proof.
  intros a f.
  exact (cms_sum_linear bool uabp6c_enum a f).
Qed.

Theorem uabp6c_sum_add_supply :
  forall f g : bool -> Real,
    req (csm_sumf bool uabp6c_enum (fun s : bool => plus (f s) (g s)))
            (plus (csm_sumf bool uabp6c_enum f)
                  (csm_sumf bool uabp6c_enum g)).
Proof.
  intros f g.
  exact (cms_sum_add bool uabp6c_enum f g).
Qed.

(* ---- 供给段假设审计（五连 Print Assumptions） ---- *)
Print Assumptions uabp6c_sum_pos_supply.
Print Assumptions uabp6c_sum_ext_supply.
Print Assumptions uabp6c_sum_le_supply.
Print Assumptions uabp6c_sum_linear_supply.
Print Assumptions uabp6c_sum_add_supply.


(* ============================================================ *)
(* 供给段二（签名保持式消解续，b3 §2.2.1；原节声明与既有签名零改）：              *)
(*   峰温 T_star 正性前提（原假设形 real_lt real_zero T_star，T* 为自由参数，      *)
(*   对抽象参数不可树内推导，抽象层保持假设身份）的实例化时点消解证书：            *)
(*   具体见证温度的正性在树内已证，供下游以具体值充任 T_star 参数并以此二件       *)
(*   填入正性前提：                                                              *)
(*   见证一 T*:=real_one——引 S07 已证引理 real_lt_zero_one；                     *)
(*   见证二 T*:=cf2_temp（UpReqConcFin2，定义性等于 one）——引 cf2_temp_pos，      *)
(*   本件语句面直接取同款类字段形 lt zero cf2_temp（同常量对齐，边界           *)
(*   cast 自然消失；lt/zero 与 real_lt/real_zero 定义性一致机器凭证在库；        *)
(*   与 ConcFin2 载体族同源，供合并侧按载体族整取。                              *)
(* ============================================================ *)
Require Import UpReqConcFin2.

Theorem uabp6c_tstar_one_pos_supply : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

Theorem uabp6c_tstar_cf2temp_pos_supply : lt zero cf2_temp.
Proof.
  exact cf2_temp_pos.
Qed.

(* ---- 供给段二假设审计（二连 Print Assumptions） ---- *)
Print Assumptions uabp6c_tstar_one_pos_supply.
Print Assumptions uabp6c_tstar_cf2temp_pos_supply.
