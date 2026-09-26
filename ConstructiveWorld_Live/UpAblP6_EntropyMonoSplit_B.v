(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_B.v —— 熵单调分解实例尾五枚定理件的独立重建件。       *)
(*                                                              *)
(* ①使命：本件形式化 EntropyMonoSplitInst 尾五枚结论（KL 非负 eps 余量镜件、      *)
(*   峰温 pinned 等式族、KL 增长/衰减前提的 eps 装载形），以 uab_ 前缀独立重建，  *)
(*   语句形与源文件 EntropyMonoSplitInst.v 逐字一致、证明独立。                  *)
(* ②依赖：CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、      *)
(*   UpReqEntropyMaxTemp；供给段另引 UpReqSumD、UpReqConcSoftmax、ConcMixSelFeed。 *)
(* ③对标：mathlib Gibbs 测度能量等式与 KL 散度非负的构造性直构（无对应直引）。    *)
(* ④构造性注记：Set 层承载零 Prop 泄露（全 real_eq/real_lt/real_le sigT-Or 形）；  *)
(*   全件真 Qed 闭合；尾嵌五连 Print Assumptions 假设审计。                      *)
(* ⑤编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。   *)
(*                                                              *)
(* 面外扩展标注：本件为工单面外扩展件，按 b3 §2.2 可消解判定施工，候合并方        *)
(*   甄别确认；若属已补强保留区请退回。原节假设声明与既有定理签名零改；          *)
(*   文件尾供给段为签名保持式消解（b3 §2.2.1）：求和面五证书位在 ConcMixSelFeed   *)
(*   求和载体 csm_sumf（S:=bool，enum:=true::false::nil）上实例化为              *)
(*   *_supply 定理（ext/le/linear/add 引 cms 系四件，pos 引 sumd_list_sum_pos     *)
(* ============================================================ *)
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
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section UpAblP6EmsB：接口面照源文件 Section EntropyMonoSplitInst 同名同序         *)
(*   （求和面 7 位 + 峰温 T_star + 能量）；速记件以 uab_ 前缀重建                 *)
(*   （接口重建，源文件整体不在依赖闭包内）。                                        *)
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

(* ---- 速记重建（uab_bt / uab_bt_pos / uab_kl：与源文件 Let 同形换名，             *)
(*   KL 方向与源文件一致：KL(p_u 竖排 p_{t*})，p_u 占第一分布位，禁倒置。） ---- *)
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
(*   (a + −a) ≡ 0 换左端。新名重建，零引用源文件 #5。                                *)
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
(*   【换道注记】源文件 #6 走 compat(0≤X)(0≤eps) + id_l((0+0)≡0) 换端；              *)
(*   本件组合序独立：nonneg_r（0 ≤ 0+eps）→ compat 左端 0≤X 提升                   *)
(*   （0+eps ≤ X+eps）→ real_le_trans 中项字面 (0+eps) 衔接。                      *)
(*   新名重建，零引用源文件 #6。                                                    *)
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
(*   real_energy_exp_temp δ 展开逐字同项，kernel 可转换），不经源文件桥接引理一      *)
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
(*   路线：实例装配——自等步内联 real_eq_refl（源文件桥接引理一 #4 被消融，           *)
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
(*   禁倒置、序向与源文件一致。零引用源文件 #5/#6/#10。                                *)
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
(*   禁倒置、序向与源文件一致。零引用源文件 #5/#6/#11。                                *)
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

Definition uabp6b_enum : list bool := true :: false :: nil.

Theorem uabp6b_sum_pos_supply :
  forall f : bool -> Real,
    (forall s : bool, lt zero (f s)) ->
    lt zero (csm_sumf bool uabp6b_enum f).
Proof.
  intros f Hpt.
  unfold csm_sumf.
  apply (@sumd_list_sum_pos Real RealEnhancedReal bool f uabp6b_enum).
  - intros Hnil.
    discriminate Hnil.
  - exact Hpt.
Qed.

Theorem uabp6b_sum_ext_supply :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (csm_sumf bool uabp6b_enum f) (csm_sumf bool uabp6b_enum g).
Proof.
  intros f g H.
  exact (cms_sum_ext bool uabp6b_enum f g H).
Qed.

Theorem uabp6b_sum_le_supply :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (csm_sumf bool uabp6b_enum f) (csm_sumf bool uabp6b_enum g).
Proof.
  intros f g H.
  exact (cms_sum_le bool uabp6b_enum f g H).
Qed.

Theorem uabp6b_sum_linear_supply :
  forall (a : Real) (f : bool -> Real),
    req (csm_sumf bool uabp6b_enum (fun s : bool => mult a (f s)))
            (mult a (csm_sumf bool uabp6b_enum f)).
Proof.
  intros a f.
  exact (cms_sum_linear bool uabp6b_enum a f).
Qed.

Theorem uabp6b_sum_add_supply :
  forall f g : bool -> Real,
    req (csm_sumf bool uabp6b_enum (fun s : bool => plus (f s) (g s)))
            (plus (csm_sumf bool uabp6b_enum f)
                  (csm_sumf bool uabp6b_enum g)).
Proof.
  intros f g.
  exact (cms_sum_add bool uabp6b_enum f g).
Qed.

(* ---- 供给段假设审计（五连 Print Assumptions） ---- *)
Print Assumptions uabp6b_sum_pos_supply.
Print Assumptions uabp6b_sum_ext_supply.
Print Assumptions uabp6b_sum_le_supply.
Print Assumptions uabp6b_sum_linear_supply.
Print Assumptions uabp6b_sum_add_supply.


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

Theorem uabp6b_tstar_one_pos_supply : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

Theorem uabp6b_tstar_cf2temp_pos_supply : lt zero cf2_temp.
Proof.
  exact cf2_temp_pos.
Qed.

(* ---- 供给段二假设审计（二连 Print Assumptions） ---- *)
Print Assumptions uabp6b_tstar_one_pos_supply.
Print Assumptions uabp6b_tstar_cf2temp_pos_supply.
