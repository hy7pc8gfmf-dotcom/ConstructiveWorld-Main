(* ============================================================ *)
(* UpReqEntropyUniqueTemp.v —— 席T22：定理 4.6c entropy_max_unique_temp *)
(*   Real 层可达形组装席 ｜ 2026-09-11 ｜ 后台独立席位（独占 CoreN 7）   *)
(* ------------------------------------------------------------------ *)
(* 【使命】同能量 E(p) == E_T + 同熵 S[p] == S[p_T] ⟹ 逐点 p s ≡ p_T s  *)
(*   （论文正式版 L325-327；Id 原件 001/ConstructiveWorld.v L17763       *)
(*   entropy_max_unique_temp）。〔构造强度〕等号条件档——承 4.3/4.6a      *)
(*   边界；席N1 判定（C6）：可达形同 C3——(a) gibbe2 式显式前提形；      *)
(*   无条件形不可行（LPO 机理，见「不可达判词」段如实登记）。           *)
(* ------------------------------------------------------------------ *)
(* 【交付三件（可达强度如实标注）】                                      *)
(*   件 1 等值核（全实，零接口前提）：同能量+同熵 ⟹                      *)
(*     Σ_s real_kl_term (p s) (p_T s) ≡ 0（T6b 熵亏主件反解：            *)
(*     KL ≡ S[p_T]−S[p]，同熵 ⟹ 差零，Id minus_self_zero 槽对位）；     *)
(*     附件 1b KL 形（real_KL_temp ≡ 0，Id relative_entropy 槽对位）。   *)
(*   件 2 可达形 (a)·抽象载体：显式接口前提位＝「Σ real_kl_term ≡ 0 ⟹   *)
(*     逐点切点式」（件 0 谓词 t22_tangent_eq，Set 值 real_eq 形）＋     *)
(*     席T1 t1_log_eq_linear_inject（切点⟹一，弱三分，无条件）＋         *)
(*     gibbsd_p_mult_ratio 尾链 ⟹ 逐点 p s ≡ p_T s。                    *)
(*   件 3 可达形 (a)·gibbe2 样板载体（bool 两点空间）收口：接口位由      *)
(*     席T1 整链放电（G08 逐项钳零件族：le_b 反对称逐 n 构造 +           *)
(*     KL≡0 ⟹ 逐点切点式 + 注入位无条件供给），物理前提之外零接口前提。  *)
(* ------------------------------------------------------------------ *)
(* 【不可达判词（9.3.3(a)/4.3 同族，如实登记）】无条件形「仅同能量+同熵  *)
(*   ⟹ 逐点等」在抽象求和面不可达：「和零⟹逐项零」提取的构造性终点是    *)
(*   切点等式的反向使用——log u ≡ u−1 ⟹ u ≡ 1 的无条件形需强三分        *)
(*   （LPO 形，CW219 L41224 定谳）；抽象面 eq 三接口（ext/linear/add）   *)
(*   亦推不出和零提取（T14 实证同界：单向 le 提升位不补提取面）。T1 弱形 *)
(*   「切点⟹一」为直觉主义可达下界，本件即以其为核；bool 具体载体经逐项  *)
(*   钳零（le_b 反对称）构造性闭合，为无条件形的最大可达实例。           *)
(* ------------------------------------------------------------------ *)
(* 【择型判词】择 (a) gibbe2 式显式前提形：本件熵亏链（件 1 全实）输出   *)
(*   Σ real_kl_term ≡ 0，正是 gibbs_equality 槽的输入面，顺接零间隙。   *)
(*   (b) 显式分歧见证逆否形（klst_kl_sum_strict / klst_kl_energy_nonconst *)
(*   ⟹ KL>0 ⟹ S[p_T]−S[p]>0 与同熵口矛盾）为备用路，需 le→lt 严格挤压   *)
(*   机（eps 收缩），本席不展开（精确余留，见交付报告）。                *)
(* ------------------------------------------------------------------ *)
(* 【Id 层原件对位表（001/ConstructiveWorld.v L17763-17780 逐槽实证）】  *)
(*   Id t Ht p Hnp Hpp Henergy Hent    ↦ 同口（T 正性证人在 T_pos 位；  *)
(*     Hp 前移为 real_entropy_dist 证人位，T6 同位；同熵口 Hent 新位）   *)
(*   Id Hdef := entropy_deficit_kl_temp ↦ real_entropy_deficit_kl_temp  *)
(*     （T6b 主件全 arity 13 参直喂；real_minus_r 定义性展开）           *)
(*   Id Hmz := minus_self_zero Spt Sp (id_sym Hent) ↦ 件 1 步 2：        *)
(*     Hent 换载（RealSetoid.real_eq_plus_compat_adapt）+ real_plus_opp  *)
(*   Id Hkl0 := id_trans (id_sym Hdef) Hmz ↦ 件 1 步 3（real_eq_trans   *)
(*     ＋ real_eq_sym 双实参形）                                         *)
(*   Id gibbs_equality p p_t … Hkl0 s   ↦ 可达形 (a) 两级：件 2（抽象    *)
(*     显式接口）／件 3（bool 整链放电，t1_gibbe2_gibbs_equality_bool    *)
(*     直达）                                                            *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（语句全 real_eq/real_lt；切点式  *)
(*   谓词为 Set 值 real_eq 形，零 Or 收口）；前提位照 Id 层对位（四口：  *)
(*   归一化/逐点正/同能量/同熵，不弱化不加码；接口位如实标注）；         *)
(*   全 Qed 收口；零新承认件。                                           *)
(* 编译配方（T15 同款，vo 树优先）：                                     *)
(*   coqc -q -vos -Q "<vo树>" "" -Q . "" UpReqEntropyUniqueTemp.v        *)
(*   （秒审后去 -vos 全量）；温控经 cpu_guard 包装 _t22_build.cmd。      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.

From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* bool 具体载体实例（件 3 消费；求和面=两点表和）                       *)
(* ============================================================ *)

Definition t22_bool_sumf (f : bool -> Real) : Real :=
  real_list_sum bool f [true; false].

Lemma t22_bool_sum_pos :
  forall f : bool -> Real,
    (forall w : bool, real_lt real_zero (f w)) ->
    real_lt real_zero (t22_bool_sumf f).
Proof.
  intros f Hf. unfold t22_bool_sumf.
  apply (real_list_sum_pos bool f [true; false] Hf).
  intro Hc. discriminate Hc.
Qed.

Lemma t22_bool_sum_ext :
  forall f g : bool -> Real,
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (t22_bool_sumf f) (t22_bool_sumf g).
Proof.
  intros f g Hfg. unfold t22_bool_sumf.
  exact (real_list_sum_ext bool f g [true; false] Hfg).
Qed.

Lemma t22_bool_sum_linear :
  forall (a : Real) (f : bool -> Real),
    real_eq (t22_bool_sumf (fun s : bool => real_mult a (f s)))
            (real_mult a (t22_bool_sumf f)).
Proof.
  intros a f. unfold t22_bool_sumf.
  exact (real_list_sum_linear bool a f [true; false]).
Qed.

Lemma t22_bool_sum_add :
  forall f g : bool -> Real,
    real_eq (t22_bool_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (t22_bool_sumf f) (t22_bool_sumf g)).
Proof.
  intros f g. unfold t22_bool_sumf.
  exact (real_list_sum_add bool f g [true; false]).
Qed.

(* ============================================================ *)
(* Section RealEntropyUniqueTemp：求和面/温度/能量参数照                 *)
(*   UpReqTempDefs Section 同名同序（供 T6/T6b 件全 arity 直喂）。       *)
(* ============================================================ *)
Section RealEntropyUniqueTemp.

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
(* 件 0：切点式谓词（显式接口形的逐点结论面，Set 值 real_eq 形）         *)
(*   对位 G08 gibbe2 注入位的逐点结论：                                 *)
(*   log(p_T s · (p s)⁻¹) ≡ (p_T s · (p s)⁻¹) − 1。                     *)
(* ---------------------------------------------------------- *)
Definition t22_tangent_eq
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (real_inv_pos (p s) (Hp s)))
       (real_mult_positive
          (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
             T T_pos energy s)
          (real_inv_pos (p s) (Hp s))
          (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
             T T_pos energy s)
          (real_inv_pos_pos (p s) (Hp s))))
    (real_plus
       (real_mult (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (real_inv_pos (p s) (Hp s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：等值核（全实）——同能量+同熵 ⟹ Σ real_kl_term ≡ 0              *)
(*   链：熵亏温度版（T6b 主件 13 参直喂）⟹ 同熵换载 + real_plus_opp     *)
(*   （Id minus_self_zero 槽）⟹ KL ≡ 0 ⟹ 桥（T6b 件 5）运输到           *)
(*   Σ real_kl_term 面（gibbs_equality 槽输入形）。                     *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_eq_kl_zero :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    real_eq (real_sum_over_S (fun s : S =>
               real_kl_term (p s)
                 (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                    T T_pos energy s)
                 (Hp s)
                 (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                    T T_pos energy s)))
            real_zero.
Proof.
  intros p Hp Hnp Henergy Hent.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S pT HpT).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：熵亏温度版（T6b 主件全 arity 13 参直喂；Id Hdef 对位；          *)
  (*   real_minus_r 定义性展开 real_plus Spt (real_opp Sp)） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnp Henergy). }
  (* 步 2：等熵 ⟹ S[p_T] − S[p] ≡ 0（Id minus_self_zero 槽：同熵换载 +   *)
  (*   real_plus_opp；x 槽传换载对 (Spt, Sp)，y 槽传逐字余项） *)
  assert (Hmz : real_eq (real_plus Spt (real_opp Sp)) real_zero).
  { apply (real_eq_trans
             (real_plus Spt (real_opp Sp))
             (real_plus Sp (real_opp Sp)) real_zero).
    - exact (RealSetoid.real_eq_plus_compat_adapt Spt Sp
               (real_opp Sp) (real_opp Sp)
               (real_eq_sym Sp Spt Hent) (real_eq_refl (real_opp Sp))).
    - exact (real_plus_opp Sp). }
  (* 步 3：KL ≡ 0（Id id_trans (id_sym Hdef) Hmz 对位） *)
  assert (Hkl : real_eq KL real_zero).
  { exact (real_eq_trans KL (real_plus Spt (real_opp Sp)) real_zero
             (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef) Hmz). }
  (* 步 4：桥（T6b 件 5 全 arity 9 参直喂）运输到 Σ real_kl_term 面 *)
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
           KL real_zero).
  - exact (real_eq_sym KL
             (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
             (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
                real_sum_over_S_ext T T_pos energy p Hp)).
  - exact Hkl.
Qed.

(* ---------------------------------------------------------- *)
(* 件 1b：等值核 KL 形（Id relative_entropy ≡ zero 槽对位）              *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_eq_KL_zero :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    real_eq (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy
               p Hp)
            real_zero.
Proof.
  intros p Hp Hnp Henergy Hent.
  apply (real_eq_trans
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s)
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy s)
                (Hp s)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy s)))
           real_zero).
  - exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp).
  - exact (t22_entropy_eq_kl_zero p Hp Hnp Henergy Hent).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：可达形 (a)——gibbe2 式显式前提形（抽象载体）                     *)
(*   同能量+同熵（⟹ Σ real_kl_term ≡ 0，件 1）+ 显式接口前提             *)
(*   （Σ ≡ 0 ⟹ 逐点切点式，件 0 谓词）⟹ 逐点 p s ≡ p_T s。              *)
(*   逐点消去链：切点式 + 席T1 t1_log_eq_linear_inject（切点⟹一，       *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去（gibbsd_p_mult_ratio）。 *)
(* ---------------------------------------------------------- *)
Theorem t22_entropy_max_unique_temp_explicit :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    real_eq (real_entropy_dist S real_sum_over_S p Hp)
            (real_entropy_dist S real_sum_over_S
               (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                  T T_pos energy)) ->
    (* 显式接口前提位（载体诚实接口）：Σ real_kl_term ≡ 0 ⟹ 逐点切点式；
       bool 样板载体上由件 3 整链放电（席T1 件直达），零残留。 *)
    (real_eq (real_sum_over_S (fun s : S =>
                real_kl_term (p s)
                  (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)
                  (Hp s)
                  (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                     T T_pos energy s)))
             real_zero ->
     forall s : S, t22_tangent_eq p Hp s) ->
    forall s : S,
      real_eq (p s)
              (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                 T T_pos energy s).
Proof.
  intros p Hp Hnp Henergy Hent Htan0 s.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  (* 第 1 步：等值核（件 1）：Σ real_kl_term ≡ 0 *)
  assert (Hkl0 : real_eq
                   (real_sum_over_S (fun s0 : S => real_kl_term (p s0) (pT s0)
                                       (Hp s0) (HpT s0)))
                   real_zero).
  { exact (t22_entropy_eq_kl_zero p Hp Hnp Henergy Hent). }
  (* 第 2 步：切点式 + 「切点⟹一」（席T1 无条件放电）⟹ 比值一 *)
  assert (Hu1 : real_eq (real_mult (pT s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (t1_log_eq_linear_inject
             (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (pT s) (real_inv_pos (p s) (Hp s))
                (HpT s) (real_inv_pos_pos (p s) (Hp s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ p s ≡ p_T s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (pT s) (real_inv_pos (p s) (Hp s))))
           (pT s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (pT s) (real_inv_pos (p s) (Hp s))))).
    + exact (real_eq_sym (real_mult (p s) real_one) (p s) (real_mult_one (p s))).
    + exact (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (pT s) (real_inv_pos (p s) (Hp s)))
                            real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (pT s) (Hp s)).
Qed.

End RealEntropyUniqueTemp.

(* ============================================================ *)
(* 件 3：可达形 (a) bool 收口——gibbe2 样板载体零接口前提形               *)
(*   显式接口位由席T1 t1_gibbe2_gibbs_equality_bool 整链放电            *)
(*   （KL≡0 ⟹ 逐点 p≡p_T 直达：G08 逐项钳零件族 le_b 反对称构造闭合     *)
(*   「和零⟹逐项零」提取，注入位由 t1_log_eq_linear_inject 无条件供给）： *)
(*   gibbe2 样板载体上 (a) 形物理前提之外零接口前提。                    *)
(* ============================================================ *)
Theorem t22_entropy_max_unique_temp_bool :
  forall (energy : bool -> Real) (T : Real) (T_pos : real_lt real_zero T)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (t22_bool_sumf p) real_one ->
    real_eq (t22_bool_sumf (fun s : bool => real_mult (p s) (energy s)))
            (real_energy_exp_temp bool t22_bool_sumf t22_bool_sum_pos T T_pos energy) ->
    real_eq (real_entropy_dist bool t22_bool_sumf p Hp)
            (real_entropy_dist bool t22_bool_sumf
               (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy)
               (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
                  T T_pos energy)) ->
    forall s : bool,
      real_eq (p s)
              (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
                 T T_pos energy s).
Proof.
  intros energy T T_pos p Hp Hnp Henergy Hent s.
  apply (t1_gibbe2_gibbs_equality_bool p
           (real_boltzmann_dist_temp bool t22_bool_sumf t22_bool_sum_pos
              T T_pos energy)
           Hp
           (real_boltzmann_dist_temp_pos bool t22_bool_sumf t22_bool_sum_pos
              T T_pos energy)
           Hnp
           (real_boltzmann_dist_temp_normalized bool t22_bool_sumf t22_bool_sum_pos
              t22_bool_sum_ext t22_bool_sum_linear T T_pos energy)).
  exact (t22_entropy_eq_kl_zero bool t22_bool_sumf t22_bool_sum_pos
           t22_bool_sum_ext t22_bool_sum_linear t22_bool_sum_add
           T T_pos energy p Hp Hnp Henergy Hent).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                              *)
(* ============================================================ *)

Print Assumptions t22_entropy_eq_kl_zero.
Print Assumptions t22_entropy_eq_KL_zero.
Print Assumptions t22_entropy_max_unique_temp_explicit.
Print Assumptions t22_entropy_max_unique_temp_bool.
