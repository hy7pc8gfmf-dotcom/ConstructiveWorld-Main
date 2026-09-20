(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_B.v —— 消融件乙：EntropyMonoSplitInst       *)
(*   尾五枚 Qed 证明件的独立重建。                                      *)
(*                                                              *)
(* 母本：EntropyMonoSplitInst.v（303 行，11 声明                          *)
(*   = 3 Let + 3 Lemma + 1 Corollary + 4 Theorem；与 Live 树同文）。      *)
(*   母本使命：UpReqEntropyMonoSplit.v Section                            *)
(*   EmsEntropyMonoSplit 三证书位装载件。                                 *)
(*                                                              *)
(* 本件范围：重建尾五枚 Qed 件——#7 emsi_kl_ge_zero_eps_mirror /          *)
(*   #8 inst_pinned / #9 inst_pinned_at_peak / #10 inst_kl_right /        *)
(*   #11 inst_kl_left；与前三枚（件甲，Qed 序 #4–#6）零交叠。             *)
(*                                                              *)
(* 消融口径：本件【零 Require EntropyMonoSplitInst】——母本整体不在        *)
(*   依赖闭包内，尾五枚逐枚自上游定义件独立重建，逐枚注明重证路线         *)
(*   （实例装配 / 直接重证 / 独立链）。逐枚重证路线：                     *)
(*   A1 uab_kl_ge_zero_eps_mirror（消融 #7）——实例装配·16 参全显给出：     *)
(*      上游原型引理全库唯一（real_KL_temp_ge_zero_eps，                   *)
(*      UpReqEntropyMaxTemp），10 接口位照本节同名同序代入，T := t*。      *)
(*   A2 uab_inst_pinned_at_peak（消融 #9）——直接重证·零前提：real_eq_refl  *)
(*      定义性合一（uab_bt δ→real_boltzmann_dist_temp 与                  *)
(*      real_energy_exp_temp δ 展开逐字同项），不经母本桥接引理一。        *)
(*   A3 uab_inst_pinned（消融 #8）——实例装配：自等步内联                   *)
(*      real_eq_refl + 片等式供给 Hslice（约束内容显式隔离不藏前提），     *)
(*      real_eq_trans 中项写字面。                                        *)
(*   A4 uab_inst_kl_right（消融 #10）——独立链：差分引理/eps 引理以新名重建 *)
(*      （uab_le_diff_ge_zero / uab_le_plus_eps），零引用母本 #5/#6；       *)
(*      其中 eps 引理换道——母本走 compat+id_l(0+0≡0) 换端，本件改走        *)
(*      nonneg_r(0≤0+eps) + compat + real_le_trans 三段链，组合序独立。    *)
(*   A5 uab_inst_kl_left（消融 #11）——独立链：A4 引理组对偶装配（KL_u 在前， *)
(*      禁倒置，序向与母本一致）。                                        *)
(*   差分引理（uab_le_diff_ge_zero）注记：raw Real 层差分向唯一通行        *)
(*      （compat + id_l(a+(−a)≡0) 换左端），以新名重建、属独立链辅助件      *)
(*      非消融对象。                                                      *)
(*                                                              *)
(* 五枚消融对象逐枚以逐字结论形重述（语句形与母本一致，证明独立）。        *)
(*                                                              *)
(*                                                              *)
(*                                                              *)
(* 构造性注记：纯构造性零承认件；Set 层语句零 Prop 泄露（全 real_eq/       *)
(*   real_lt/real_le sigT-Or 形）；全件真 Qed 闭合（零悬置、零假设位）；    *)
(*   尾嵌 Print Assumptions 五连假设审计。                                 *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，         *)
(*   树内零写入。依赖 Require：CW_ConstructiveWorld_219、                  *)
(*   UpReqTempDefs、UpReqEntropyDeficitTemp、UpReqEntropyMaxTemp。         *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section UpAblP6EmsB：接口面照母本 Section EntropyMonoSplitInst 同名同序         *)
(*   （求和面 7 位 + 峰温 T_star + 能量）；速记件以 uab_ 前缀重建                 *)
(*   （接口重建，母本整体不在依赖闭包内）。                                        *)
(* ============================================================ *)
Section UpAblP6EmsB.

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

(* ---- 速记重建（uab_bt / uab_bt_pos / uab_kl：与母本 Let 同形换名，             *)
(*   KL 方向与母本一致：KL(p_u 竖排 p_{t*})，p_u 占第一分布位，禁倒置。） ---- *)
Let uab_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let uab_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (uab_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let uab_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (uab_bt u Hu) (uab_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 独立链辅助件一（差分向）：a ≤ b 给 0 ≤ b + (−a)。                              *)
(*   raw Real 层差分向唯一通行：compat 双边同加 −a，再 id_l 经                     *)
(*   (a + −a) ≡ 0 换左端。新名重建，零引用母本 #5。                                *)
(* ---------------------------------------------------------- *)
Lemma uab_le_diff_ge_zero :
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
(* 独立链辅助件二（eps 松弛提升）：0 ≤ X 且 0 < eps 给 0 ≤ X + eps。               *)
(*   【换道注记】母本 #6 走 compat(0≤X)(0≤eps) + id_l((0+0)≡0) 换端；              *)
(*   本件组合序独立：nonneg_r（0 ≤ 0+eps）→ compat 左端 0≤X 提升                   *)
(*   （0+eps ≤ X+eps）→ real_le_trans 中项字面 (0+eps) 衔接。                      *)
(*   新名重建，零引用母本 #6。                                                    *)
(* ---------------------------------------------------------- *)
Lemma uab_le_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  exact (real_le_trans real_zero
           (real_plus real_zero eps)
           (real_plus X eps)
           (real_le_plus_nonneg_r real_zero eps
              (real_le_from_lt_aux real_zero eps Heps))
           (real_le_plus_compat real_zero X eps eps HX
              (real_le_refl eps))).
Qed.

(* ---------------------------------------------------------- *)
(* A1（消融 #7 emsi_kl_ge_zero_eps_mirror）：对偶 exact 孪生形。                    *)
(*   路线：实例装配·16 参全显给出（上游原型引理全库唯一：                          *)
(*   real_KL_temp_ge_zero_eps，UpReqEntropyMaxTemp），                              *)
(*   10 接口位照本节同名同序代入，温度位 T := t*。                                 *)
(* ---------------------------------------------------------- *)
Theorem uab_kl_ge_zero_eps_mirror :
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
  exact (real_KL_temp_ge_zero_eps
           S real_sum_over_S real_sum_pos_preserved
           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear
           real_sum_over_S_add
           T_star T_star_pos energy p Hp Hnp eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* A2（消融 #9 inst_pinned_at_peak）：峰温点零前提闭合语句。                        *)
(*   路线：上游定义面直接重证·零前提——real_eq_refl 定义性合一（uab_bt 与          *)
(*   real_energy_exp_temp δ 展开逐字同项，kernel 可转换），不经母本桥接引理一      *)
(*   （#4）亦成立。                                                                *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (uab_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (real_eq_refl
           (real_sum_over_S
              (fun s : S => real_mult (uab_bt T_star T_star_pos s) (energy s)))).
Qed.

(* ---------------------------------------------------------- *)
(* A3（消融 #8 inst_pinned）：证书位一 Hpinned 装载（逐字结论形）。                *)
(*   路线：实例装配——自等步内联 real_eq_refl（母本桥接引理一 #4 被消融，           *)
(*   定义性合一无桥直达）+ 片等式供给 Hslice（E_u == E_{t*}，约束内容              *)
(*   显式隔离不藏前提），real_eq_trans 中项写字面。                                *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (uab_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice u Hu.
  exact (real_eq_trans
           (real_sum_over_S
              (fun s : S => real_mult (uab_bt u Hu s) (energy s)))
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              u Hu energy)
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy)
           (real_eq_refl
              (real_sum_over_S
                 (fun s : S => real_mult (uab_bt u Hu s) (energy s))))
           (Hslice u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* A4（消融 #10 inst_kl_right）：证书位二 Hkl_right 装载（逐字结论形）。            *)
(*   路线：独立链——供给定型 plain growth（real_le KL_u KL_v）→ 新名                *)
(*   差分引理换形 → 新名 eps 引理（换道组合）提升。KL_v 在前 KL_u 取 real_opp，    *)
(*   禁倒置、序向与母本一致。零引用母本 #5/#6/#10。                                *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (uab_kl u Hu) (uab_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (uab_kl v Hv) (real_opp (uab_kl u Hu))) eps).
Proof.
  intros Hgrowth u v Hu Hv Htu Huv eps Heps.
  exact (uab_le_plus_eps
           (real_plus (uab_kl v Hv) (real_opp (uab_kl u Hu))) eps
           (uab_le_diff_ge_zero (uab_kl u Hu) (uab_kl v Hv)
              (Hgrowth u v Hu Hv Htu Huv))
           Heps).
Qed.

(* ---------------------------------------------------------- *)
(* A5（消融 #11 inst_kl_left）：证书位三 Hkl_left 装载（逐字结论形）。              *)
(*   路线：独立链——供给定型 plain decay（real_le KL_v KL_u，序前提                 *)
(*   u ≤ v ≤ t*）→ 同组新名引理对偶装配。KL_u 在前 KL_v 取 real_opp，              *)
(*   禁倒置、序向与母本一致。零引用母本 #5/#6/#11。                                *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (uab_kl v Hv) (uab_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (uab_kl u Hu) (real_opp (uab_kl v Hv))) eps).
Proof.
  intros Hdecay u v Hu Hv Huv Hvt eps Heps.
  exact (uab_le_plus_eps
           (real_plus (uab_kl u Hu) (real_opp (uab_kl v Hv))) eps
           (uab_le_diff_ge_zero (uab_kl v Hv) (uab_kl u Hu)
              (Hdecay u v Hu Hv Huv Hvt))
           Heps).
Qed.

End UpAblP6EmsB.

(* ---- 假设面审计（五连 Print Assumptions） ---- *)
Print Assumptions uab_kl_ge_zero_eps_mirror.
Print Assumptions uab_inst_pinned_at_peak.
Print Assumptions uab_inst_pinned.
Print Assumptions uab_inst_kl_right.
Print Assumptions uab_inst_kl_left.
