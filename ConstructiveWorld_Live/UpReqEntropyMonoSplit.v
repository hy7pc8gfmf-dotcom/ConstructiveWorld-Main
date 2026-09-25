(* ============================================================ *)
(* UpReqEntropyMonoSplit.v —— R120 批 2 波 3 W15 假设消解落件                     *)
(*                                                              *)
(* ①使命：本件形式化约束化熵单调性分离——峰温两侧熵单调（eps 余量）、约束片熵       *)
(*   峰界、与 prod 账统一分离定理（Section EmsEntropyMonoSplit 五件结论）。        *)
(* ②依赖：CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp、      *)
(*   UpReqEntropyMaxTemp；供给段另引 UpReqSumD、UpReqConcSoftmax、ConcMixSelFeed、 *)
(*   UpReqConcFin2。                                                             *)
(* ③对标：mathlib Gibbs 测度熵单峰与 KL 散度非负的构造性直构（无对应直引）。       *)
(* ④构造性注记：Set 层承载零 Prop 泄露（全 real_eq/real_lt/real_le sigT-Or 形）；  *)
(*   全件真 Qed 闭合；尾嵌假设审计；原节声明与既有定理签名零改。                    *)
(* ⑤编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-Q 影子池单根。                 *)
(*                                                              *)
(* 面外扩展标注：本件为工单面外扩展件（C2 底册 TOP2），按 b3 §2.2 可消解判定施工，  *)
(*   候融合方甄别确认；若属已补强保留区请退回。同族 UpAblP6_EntropyMonoSplit_A/B/C  *)
(*   为既往消融件已另行处置，勿混淆勿触碰。既往补强自述核实：本件 ToyR 头注自述     *)
(* 处置说明：原件全文逐字保留；历史注释按 G1 全件禁词映射同文改写（剥离层逐字节      *)
(*   签名保持式消解：求和面五证书位＋峰温正性位的实例化时点供给证书（三层显式        *)
(*   标注：头注层/段注层/件注层）；Hpinned/Hkl_right/Hkl_left 为真前提位原样        *)
(*   保留（约束片能量钉与 KL 增长/衰减证书为独立接口义务，禁硬证），详见文尾段注。   *)
(* ============================================================ *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ems_entropy_peak_bound_above（原 L640，2 句玩具证）                  *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，   *)
(* 为恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面   *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqEntropyMonoSplit.v *)
(* *)
(* 主件： ems_entropy_temp_antitone_above（降支，全库首件） /         *)
(*        ems_entropy_split_at_peak（升支+降支+峰界分离统一）。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqTempDefs、                   *)
(*        UpReqEntropyDeficitTemp、UpReqEntropyMaxTemp（四件全部在册）。 *)
(* ============================================================ *)

(* ============================================================ *)

(* ------------------------------------------------------------------ *)
(* 【使命】库内两线表面张力的定理化：防火墙线证「升温 ⟹ 熵不降」        *)
(*   （UpFirewall.v entropy_temp_mono，Id 层既件），TempUnimodalMax 线  *)
(*   证「熵在唯一温度处有峰」——两线蕴涵熵先升后降，但降支（t ≥ t* 段    *)
(* ------------------------------------------------------------------ *)
(* 【C5 结论的定理化（约束出现与否 = 显式证书）】                       *)
(*   防火墙升支的引擎是 ΔE ≥ 0（升温抬能量 ⟹ 抬熵）；降支的对称障碍 =   *)
(*   ΔE ≤ 0 在高温段不成立（能量随温度仍升）——降支的正确引擎不是 ΔE     *)
(*   反号，而是【约束片】：把 C5 张力的未命名变量「约束出现与否」升格    *)
(*   为显式 Section 证书 Hpinned（片上 E(p_u) == E_{t*} 对一切正温 u）。*)
(*   约束片上熵亏恒等式（已注册 real_entropy_deficit_kl_temp）给        *)
(*     KL(p_u‖p_{t*}) + S(p_u) == S(p_{t*})                             *)
(*   再配 KL 增长证书（eps 松弛 Bishop 形，副本已注册                    *)
(*   real_KL_temp_ge_zero_eps 的 0 ≤ KL+eps 形）：                      *)
(*     右支  0 ≤ KL(p_v‖p_{t*}) − KL(p_u‖p_{t*}) + eps   (t* ≤ u ≤ v)   *)
(*     左支  0 ≤ KL(p_u‖p_{t*}) − KL(p_v‖p_{t*}) + eps   (u ≤ v ≤ t_star) *)
(*   即得两侧单调性。峰界另由已注册 real_max_entropy_is_boltzmann_      *)
(*   temp_eps 一步实例给出。非圆性账：KL 证书是 eps 松弛的严格形而       *)
(*   分离定理的内容 = 「KL-V 形 ⟹ 熵单峰」这一真实蕴涵。               *)
(* ------------------------------------------------------------------ *)
(* 【前提诚实分类】                                                     *)
(*   Section 证书（接口假设，全库无根，逐条如实标注）：                 *)
(*     Hpinned   约束片能量钉（C5「约束出现」变量的定理化载体）；        *)
(*     Hkl_right / Hkl_left  峰温 KL 增长/衰减证书（eps 松弛形）。      *)
(*   Section 接口（照 UpReqEntropyMaxTemp Section 同名同序，含扩容位     *)
(*   real_sum_over_S_le；具体载体实例 real_list_sum_le 在库非空）。     *)
(*   既件（全部 Require 使用，零重建）：real_entropy_deficit_kl_temp    *)
(*   （13 参）/ real_max_entropy_is_boltzmann_temp_eps（16 参）/        *)
(*   real_le_plus_nonneg_r / RealSetoid.real_le_id_r 等工具箱。         *)
(* ------------------------------------------------------------------ *)
(* 【跨层红线注记】UpFirewall.v 的 entropy_temp_mono 属 Id 层           *)
(*   （real_eq/real_le）不同构，禁混引。升支左支以恒等式形态在本层       *)
(*   与 Id 层既件在各自层内自洽，不互为主件。Z15 互联注记：升支方向      *)
(*   与 fw_kl ≤ 熵增（TempMonoW2Mark 恒等式族）同侧；降支不涉 TV，      *)
(*   不触碰 UpFirewall scoping 红线（:44 不主张 TV-熵传递）。           *)
(* 【G3 注记（诚实处置，不设伪件）】                                    *)
(*   1) N=1 退化端点：t* = u（u==v）时两支前提同时成立，结论退化为       *)
(*      自反（S ≤ S + eps，real_le_refl 档），无新内容，不设件；        *)
(*      不越权（T_star 正性是 boltzmann 族定义面的硬前提）。            *)
(*   2) ΔE 反号障碍：约束片外（自由族）恒等式 ΔS == β·ΔE + KL 两项      *)
(* 【KL 方向性红线审计表（全文逐处核对）】                              *)
(*   ems_kl_peak u Hu := real_KL_temp … T_star T_star_pos energy        *)
(*      (ems_bt u Hu) (ems_bt_pos u Hu)  = KL(p_u ‖ p_{t*})：           *)
(*      p_u 占第一分布位（from），p_{t*} 占参考位（to）。与已注册       *)
(*      real_entropy_deficit_kl_temp 结论位同序（KL(q‖p_T)，q 前）。    *)
(*   Hkl_right 结论 real_le real_zero (KL_v − KL_u + eps)：KL_v 在前，   *)
(*      KL_u 取 real_opp——「KL 随温增」读向，禁倒置。                  *)
(*   Hkl_left  结论 real_le real_zero (KL_u − KL_v + eps)：副本，        *)
(*      「KL 向峰衰减」读向，禁倒置。                                  *)
(* 【红线】纯构造性零 公理/经典逻辑；Set 层零 Prop 泄露（比较全        *)
(*   real_le/real_lt sigT-Or 形）；分离账用 prod（A*B）Set 形；          *)
(*   公理面：零新承认件，依赖四件自身 Closed（文末 Print Assumptions    *)
(*   审计）。                                                           *)
(* 编译配方：coqc -q -native-compiler no -Q . "" UpReqEntropyMonoSplit.v *)
(*   （四关卡 9.1 配方：vos 秒审 → cpu_guard 全量 → 提取零 magic →      *)
(*   coqchk；环境钉 COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq） *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section EmsEntropyMonoSplit：求和面/温度/能量参数照                   *)
(*   UpReqEntropyMaxTemp Section 同名同序（前 7 接口位 + 温度 + 能量），  *)
(* ============================================================ *)
Section EmsEntropyMonoSplit.

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

(* ---------------------------------------------------------- *)
(* 速记（Section Let， discharge 时内联；UpFirewall Bt/Et 同形先例）    *)
(* ---------------------------------------------------------- *)
Let ems_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let ems_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (ems_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let ems_bt_norm (u : Real) (Hu : real_lt real_zero u) :
  real_eq (real_sum_over_S (ems_bt u Hu)) real_one :=
  real_boltzmann_dist_temp_normalized S real_sum_over_S real_sum_pos_preserved
    real_sum_over_S_ext real_sum_over_S_linear u Hu energy.
Let ems_ent (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_entropy_dist S real_sum_over_S (ems_bt u Hu) (ems_bt_pos u Hu).
Let ems_ent_star : Real :=
  real_entropy_dist S real_sum_over_S (ems_bt T_star T_star_pos)
                    (ems_bt_pos T_star T_star_pos).
Let ems_et (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
(* KL 方向红线：KL(p_u ‖ p_{t*})——p_u 第一分布位，p_{t*} 参考位。 *)
Let ems_kl_peak (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (ems_bt u Hu) (ems_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 证书位 1（约束片能量钉）：片上 E(p_u) == E_{t*} 对一切正温 u。        *)
(*   （C5 张力「约束出现与否」变量的定理化载体。）                      *)
(* ---------------------------------------------------------- *)
Hypothesis Hpinned :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_sum_over_S (fun s : S => real_mult (ems_bt u Hu s) (energy s)))
            (ems_et T_star T_star_pos).

(* ---------------------------------------------------------- *)
(* 证书位 2/3（峰温 KL 增长/衰减，eps 松弛 Bishop 形；                  *)
(*   副本已注册 real_KL_temp_ge_zero_eps 的 0 ≤ KL+eps 形）。           *)
(* ---------------------------------------------------------- *)
Hypothesis Hkl_right :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (ems_kl_peak v Hv) (real_opp (ems_kl_peak u Hu))) eps).
Hypothesis Hkl_left :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (ems_kl_peak u Hu) (real_opp (ems_kl_peak v Hv))) eps).

(* ---------------------------------------------------------- *)
(* 件 0：约束片熵亏恒等式（KL + S == S_star）。                          *)
(*   链：已注册 real_entropy_deficit_kl_temp（13 参全显式）→            *)
(*   real_minus_r 定义性展开（S12_B5RecycleSF L13234）→ AC 消去。        *)
(* ---------------------------------------------------------- *)
Lemma ems_pinned_kl_entropy_eq :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_plus (ems_kl_peak u Hu) (ems_ent u Hu)) ems_ent_star.
Proof.
  intros u Hu.
  assert (Hdef : real_eq (real_minus_r ems_ent_star (ems_ent u Hu)) (ems_kl_peak u Hu)).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T_star T_star_pos energy
             (ems_bt u Hu) (ems_bt_pos u Hu) (ems_bt_norm u Hu) (Hpinned u Hu)). }
  apply (real_eq_trans
           (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
           (real_plus (real_minus_r ems_ent_star (ems_ent u Hu)) (ems_ent u Hu))
           ems_ent_star).
  - apply (RealSetoid.real_eq_plus_compat_adapt
             (ems_kl_peak u Hu) (real_minus_r ems_ent_star (ems_ent u Hu))
             (ems_ent u Hu) (ems_ent u Hu)
             (real_eq_sym _ _ Hdef)
             (real_eq_refl (ems_ent u Hu))).
  - apply (real_eq_trans
             (real_plus (real_minus_r ems_ent_star (ems_ent u Hu)) (ems_ent u Hu))
             (real_plus (real_plus ems_ent_star (real_opp (ems_ent u Hu)))
                        (ems_ent u Hu))
             ems_ent_star).
    + apply (RealSetoid.real_eq_plus_compat_adapt
               (real_minus_r ems_ent_star (ems_ent u Hu))
               (real_plus ems_ent_star (real_opp (ems_ent u Hu)))
               (ems_ent u Hu) (ems_ent u Hu)
               (real_eq_refl (real_plus ems_ent_star (real_opp (ems_ent u Hu))))
               (real_eq_refl (ems_ent u Hu))).
    + apply (real_eq_trans
               (real_plus (real_plus ems_ent_star (real_opp (ems_ent u Hu)))
                          (ems_ent u Hu))
               (real_plus ems_ent_star
                          (real_plus (real_opp (ems_ent u Hu)) (ems_ent u Hu)))
               ems_ent_star).
      * exact (real_eq_sym _ _
                 (real_plus_assoc ems_ent_star (real_opp (ems_ent u Hu))
                                  (ems_ent u Hu))).
      * apply (real_eq_trans
                 (real_plus ems_ent_star
                            (real_plus (real_opp (ems_ent u Hu)) (ems_ent u Hu)))
                 (real_plus ems_ent_star real_zero)
                 ems_ent_star).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    ems_ent_star ems_ent_star
                    (real_plus (real_opp (ems_ent u Hu)) (ems_ent u Hu)) real_zero
                    (real_eq_refl ems_ent_star)
                    (real_eq_trans (real_plus (real_opp (ems_ent u Hu)) (ems_ent u Hu))
                                   (real_plus (ems_ent u Hu) (real_opp (ems_ent u Hu)))
                                   real_zero
                                   (real_plus_comm (real_opp (ems_ent u Hu)) (ems_ent u Hu))
                                   (real_plus_opp (ems_ent u Hu)))).
        -- exact (real_plus_zero ems_ent_star).
Qed.

(* ---------------------------------------------------------- *)
(* 件 1（G1 主定理·降支，全库首件）：峰右侧熵不增。                        *)
(*   t* ≤ u ≤ v（eps 松弛）⟹ S(p_v) ≤ S(p_u) + eps。                    *)
(*   引擎：件 0（约束片熵亏）×2 + Hkl_right（KL 增长证书）。            *)
(* ---------------------------------------------------------- *)
Theorem ems_entropy_temp_antitone_above :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (ems_ent v Hv) (real_plus (ems_ent u Hu) eps).
Proof.
  intros u v Hu Hv Htu Huv eps Heps.
  assert (H0 : real_le real_zero
                 (real_plus (real_plus (ems_kl_peak v Hv) (real_opp (ems_kl_peak u Hu)))
                            eps)).
  { exact (Hkl_right u v Hu Hv Htu Huv eps Heps). }
  assert (H1 : real_le (ems_ent v Hv)
                 (real_plus (ems_ent v Hv)
                            (real_plus (real_plus (ems_kl_peak v Hv)
                                                  (real_opp (ems_kl_peak u Hu)))
                                       eps))).
  { exact (real_le_plus_nonneg_r (ems_ent v Hv)
             (real_plus (real_plus (ems_kl_peak v Hv) (real_opp (ems_kl_peak u Hu))) eps)
             H0). }
  (* 九步 AC 链：Sv + (KLv − KLu + eps) == Su + eps（KLv/Su 各经件 0 坍缩） *)
  assert (H2 : real_eq
                 (real_plus (ems_ent v Hv)
                            (real_plus (real_plus (ems_kl_peak v Hv)
                                                  (real_opp (ems_kl_peak u Hu)))
                                       eps))
                 (real_plus (ems_ent u Hu) eps)).
  { apply (real_eq_trans
             (real_plus (ems_ent v Hv)
                        (real_plus (real_plus (ems_kl_peak v Hv)
                                              (real_opp (ems_kl_peak u Hu)))
                                   eps))
             (real_plus (real_plus (ems_ent v Hv)
                                   (real_plus (ems_kl_peak v Hv)
                                              (real_opp (ems_kl_peak u Hu))))
                        eps)
               (real_plus (ems_ent u Hu) eps)).
    - exact (real_plus_assoc (ems_ent v Hv)
               (real_plus (ems_kl_peak v Hv) (real_opp (ems_kl_peak u Hu))) eps).
    - apply (real_eq_trans
               (real_plus (real_plus (ems_ent v Hv)
                                     (real_plus (ems_kl_peak v Hv)
                                                (real_opp (ems_kl_peak u Hu))))
                          eps)
               (real_plus (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                     (real_opp (ems_kl_peak u Hu)))
                          eps)
               (real_plus (ems_ent u Hu) eps)).
      + exact (RealSetoid.real_eq_plus_compat_adapt
                 (real_plus (ems_ent v Hv)
                            (real_plus (ems_kl_peak v Hv) (real_opp (ems_kl_peak u Hu))))
                 (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                            (real_opp (ems_kl_peak u Hu)))
                 eps eps
                 (real_plus_assoc (ems_ent v Hv) (ems_kl_peak v Hv)
                                  (real_opp (ems_kl_peak u Hu)))
                 (real_eq_refl eps)).
      + apply (real_eq_trans
                 (real_plus (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                       (real_opp (ems_kl_peak u Hu)))
                            eps)
                 (real_plus (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                       (real_opp (ems_kl_peak u Hu)))
                            eps)
                 (real_plus (ems_ent u Hu) eps)).
        * apply (RealSetoid.real_eq_plus_compat_adapt
                   (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                              (real_opp (ems_kl_peak u Hu)))
                   (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                              (real_opp (ems_kl_peak u Hu)))
                   eps eps
                   (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                      (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                      (real_opp (ems_kl_peak u Hu)) (real_opp (ems_kl_peak u Hu))
                      (real_plus_comm (ems_ent v Hv) (ems_kl_peak v Hv))
                      (real_eq_refl (real_opp (ems_kl_peak u Hu))))
                   (real_eq_refl eps)).
        * apply (real_eq_trans
                   (real_plus (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                         (real_opp (ems_kl_peak u Hu)))
                              eps)
                   (real_plus (real_plus ems_ent_star (real_opp (ems_kl_peak u Hu)))
                              eps)
                   (real_plus (ems_ent u Hu) eps)).
          -- apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                 (real_opp (ems_kl_peak u Hu)))
                      (real_plus ems_ent_star (real_opp (ems_kl_peak u Hu)))
                      eps eps
                      (RealSetoid.real_eq_plus_compat_adapt
                         (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                         ems_ent_star
                         (real_opp (ems_kl_peak u Hu)) (real_opp (ems_kl_peak u Hu))
                         (ems_pinned_kl_entropy_eq v Hv)
                         (real_eq_refl (real_opp (ems_kl_peak u Hu))))
                      (real_eq_refl eps)).
          -- apply (real_eq_trans
                       (real_plus (real_plus ems_ent_star (real_opp (ems_kl_peak u Hu)))
                                  eps)
                       (real_plus
                          (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                     (real_opp (ems_kl_peak u Hu)))
                          eps)
                       (real_plus (ems_ent u Hu) eps)).
            ++ apply (RealSetoid.real_eq_plus_compat_adapt
                        (real_plus ems_ent_star (real_opp (ems_kl_peak u Hu)))
                        (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                   (real_opp (ems_kl_peak u Hu)))
                        eps eps
                        (RealSetoid.real_eq_plus_compat_adapt
                           ems_ent_star
                           (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                           (real_opp (ems_kl_peak u Hu)) (real_opp (ems_kl_peak u Hu))
                           (real_eq_sym _ _ (ems_pinned_kl_entropy_eq u Hu))
                           (real_eq_refl (real_opp (ems_kl_peak u Hu))))
                        (real_eq_refl eps)).
            ++ apply (real_eq_trans
                         (real_plus
                            (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                       (real_opp (ems_kl_peak u Hu)))
                            eps)
                         (real_plus
                            (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                       (real_opp (ems_kl_peak u Hu)))
                            eps)
                         (real_plus (ems_ent u Hu) eps)).
              ** apply (RealSetoid.real_eq_plus_compat_adapt
                          (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                     (real_opp (ems_kl_peak u Hu)))
                          (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                     (real_opp (ems_kl_peak u Hu)))
                          eps eps
                          (RealSetoid.real_eq_plus_compat_adapt
                             (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                             (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                             (real_opp (ems_kl_peak u Hu)) (real_opp (ems_kl_peak u Hu))
                             (real_plus_comm (ems_kl_peak u Hu) (ems_ent u Hu))
                             (real_eq_refl (real_opp (ems_kl_peak u Hu))))
                          (real_eq_refl eps)).
              ** apply (real_eq_trans
                           (real_plus
                              (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                         (real_opp (ems_kl_peak u Hu)))
                              eps)
                           (real_plus
                              (real_plus (ems_ent u Hu)
                                         (real_plus (ems_kl_peak u Hu)
                                                    (real_opp (ems_kl_peak u Hu))))
                              eps)
                           (real_plus (ems_ent u Hu) eps)).
                --- apply (RealSetoid.real_eq_plus_compat_adapt
                             (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                        (real_opp (ems_kl_peak u Hu)))
                             (real_plus (ems_ent u Hu)
                                        (real_plus (ems_kl_peak u Hu)
                                                   (real_opp (ems_kl_peak u Hu))))
                             eps eps
                             (real_eq_sym _ _
                                (real_plus_assoc (ems_ent u Hu) (ems_kl_peak u Hu)
                                                 (real_opp (ems_kl_peak u Hu))))
                             (real_eq_refl eps)).
                --- apply (real_eq_trans
                             (real_plus
                                (real_plus (ems_ent u Hu)
                                           (real_plus (ems_kl_peak u Hu)
                                                      (real_opp (ems_kl_peak u Hu))))
                                eps)
                             (real_plus (real_plus (ems_ent u Hu) real_zero) eps)
                             (real_plus (ems_ent u Hu) eps)).
                    +++ apply (RealSetoid.real_eq_plus_compat_adapt
                                 (real_plus (ems_ent u Hu)
                                            (real_plus (ems_kl_peak u Hu)
                                                       (real_opp (ems_kl_peak u Hu))))
                                 (real_plus (ems_ent u Hu) real_zero)
                                 eps eps
                                 (RealSetoid.real_eq_plus_compat_adapt
                                    (ems_ent u Hu) (ems_ent u Hu)
                                    (real_plus (ems_kl_peak u Hu)
                                               (real_opp (ems_kl_peak u Hu)))
                                    real_zero
                                    (real_eq_refl (ems_ent u Hu))
                                    (real_plus_opp (ems_kl_peak u Hu)))
                                 (real_eq_refl eps)).
                    +++ apply (RealSetoid.real_eq_plus_compat_adapt
                                 (real_plus (ems_ent u Hu) real_zero)
                                 (ems_ent u Hu)
                                 eps eps
                                 (real_plus_zero (ems_ent u Hu))
                                 (real_eq_refl eps)).
  }
  (* 组装：Sv ≤ Sv + (KLv − KLu + eps) [H1] 经 H2 换向至 Sv ≤ Su + eps *)
  exact (RealSetoid.real_le_id_r (ems_ent v Hv)
           (real_plus (ems_ent v Hv)
                      (real_plus (real_plus (ems_kl_peak v Hv)
                                            (real_opp (ems_kl_peak u Hu)))
                                 eps))
           (real_plus (ems_ent u Hu) eps)
           H2 H1).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2（左支重组·升支恒等式形态，如实标注）：峰左侧熵不降。             *)
(*   u ≤ v ≤ t*（eps 松弛）⟹ S(p_u) ≤ S(p_v) + eps。                    *)
(*   注：与 Id 层既件 UpFirewall entropy_temp_mono（ΔE≥0 引擎，全温域） *)
(*   不同构不互引；本件为约束片上 KL 衰减证书驱动的副本件。             *)
(* ---------------------------------------------------------- *)
Theorem ems_entropy_temp_mono_below :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (ems_ent u Hu) (real_plus (ems_ent v Hv) eps).
Proof.
  intros u v Hu Hv Huv Hvt eps Heps.
  assert (H0 : real_le real_zero
                 (real_plus (real_plus (ems_kl_peak u Hu) (real_opp (ems_kl_peak v Hv)))
                            eps)).
  { exact (Hkl_left u v Hu Hv Huv Hvt eps Heps). }
  assert (H1 : real_le (ems_ent u Hu)
                 (real_plus (ems_ent u Hu)
                            (real_plus (real_plus (ems_kl_peak u Hu)
                                                  (real_opp (ems_kl_peak v Hv)))
                                       eps))).
  { exact (real_le_plus_nonneg_r (ems_ent u Hu)
             (real_plus (real_plus (ems_kl_peak u Hu) (real_opp (ems_kl_peak v Hv))) eps)
             H0). }
  assert (H2 : real_eq
                 (real_plus (ems_ent u Hu)
                            (real_plus (real_plus (ems_kl_peak u Hu)
                                                  (real_opp (ems_kl_peak v Hv)))
                                       eps))
                 (real_plus (ems_ent v Hv) eps)).
  { apply (real_eq_trans
             (real_plus (ems_ent u Hu)
                        (real_plus (real_plus (ems_kl_peak u Hu)
                                              (real_opp (ems_kl_peak v Hv)))
                                   eps))
             (real_plus (real_plus (ems_ent u Hu)
                                   (real_plus (ems_kl_peak u Hu)
                                              (real_opp (ems_kl_peak v Hv))))
                        eps)
               (real_plus (ems_ent v Hv) eps)).
    - exact (real_plus_assoc (ems_ent u Hu)
               (real_plus (ems_kl_peak u Hu) (real_opp (ems_kl_peak v Hv))) eps).
    - apply (real_eq_trans
               (real_plus (real_plus (ems_ent u Hu)
                                     (real_plus (ems_kl_peak u Hu)
                                                (real_opp (ems_kl_peak v Hv))))
                          eps)
               (real_plus (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                     (real_opp (ems_kl_peak v Hv)))
                          eps)
               (real_plus (ems_ent v Hv) eps)).
      + exact (RealSetoid.real_eq_plus_compat_adapt
                 (real_plus (ems_ent u Hu)
                            (real_plus (ems_kl_peak u Hu) (real_opp (ems_kl_peak v Hv))))
                 (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                            (real_opp (ems_kl_peak v Hv)))
                 eps eps
                 (real_plus_assoc (ems_ent u Hu) (ems_kl_peak u Hu)
                                  (real_opp (ems_kl_peak v Hv)))
                 (real_eq_refl eps)).
      + apply (real_eq_trans
                 (real_plus (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                                       (real_opp (ems_kl_peak v Hv)))
                            eps)
                 (real_plus (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                       (real_opp (ems_kl_peak v Hv)))
                            eps)
                 (real_plus (ems_ent v Hv) eps)).
        * apply (RealSetoid.real_eq_plus_compat_adapt
                   (real_plus (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                              (real_opp (ems_kl_peak v Hv)))
                   (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                              (real_opp (ems_kl_peak v Hv)))
                   eps eps
                   (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (ems_ent u Hu) (ems_kl_peak u Hu))
                      (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                      (real_opp (ems_kl_peak v Hv)) (real_opp (ems_kl_peak v Hv))
                      (real_plus_comm (ems_ent u Hu) (ems_kl_peak u Hu))
                      (real_eq_refl (real_opp (ems_kl_peak v Hv))))
                   (real_eq_refl eps)).
        * apply (real_eq_trans
                   (real_plus (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                         (real_opp (ems_kl_peak v Hv)))
                              eps)
                   (real_plus (real_plus ems_ent_star (real_opp (ems_kl_peak v Hv)))
                              eps)
                   (real_plus (ems_ent v Hv) eps)).
          -- apply (RealSetoid.real_eq_plus_compat_adapt
                      (real_plus (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                                 (real_opp (ems_kl_peak v Hv)))
                      (real_plus ems_ent_star (real_opp (ems_kl_peak v Hv)))
                      eps eps
                      (RealSetoid.real_eq_plus_compat_adapt
                         (real_plus (ems_kl_peak u Hu) (ems_ent u Hu))
                         ems_ent_star
                         (real_opp (ems_kl_peak v Hv)) (real_opp (ems_kl_peak v Hv))
                         (ems_pinned_kl_entropy_eq u Hu)
                         (real_eq_refl (real_opp (ems_kl_peak v Hv))))
                      (real_eq_refl eps)).
          -- apply (real_eq_trans
                       (real_plus (real_plus ems_ent_star (real_opp (ems_kl_peak v Hv)))
                                  eps)
                       (real_plus
                          (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                     (real_opp (ems_kl_peak v Hv)))
                          eps)
                       (real_plus (ems_ent v Hv) eps)).
            ++ apply (RealSetoid.real_eq_plus_compat_adapt
                        (real_plus ems_ent_star (real_opp (ems_kl_peak v Hv)))
                        (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                   (real_opp (ems_kl_peak v Hv)))
                        eps eps
                        (RealSetoid.real_eq_plus_compat_adapt
                           ems_ent_star
                           (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                           (real_opp (ems_kl_peak v Hv)) (real_opp (ems_kl_peak v Hv))
                           (real_eq_sym _ _ (ems_pinned_kl_entropy_eq v Hv))
                           (real_eq_refl (real_opp (ems_kl_peak v Hv))))
                        (real_eq_refl eps)).
            ++ apply (real_eq_trans
                         (real_plus
                            (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                       (real_opp (ems_kl_peak v Hv)))
                            eps)
                         (real_plus
                            (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                       (real_opp (ems_kl_peak v Hv)))
                            eps)
                         (real_plus (ems_ent v Hv) eps)).
              ** apply (RealSetoid.real_eq_plus_compat_adapt
                          (real_plus (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                                     (real_opp (ems_kl_peak v Hv)))
                          (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                     (real_opp (ems_kl_peak v Hv)))
                          eps eps
                          (RealSetoid.real_eq_plus_compat_adapt
                             (real_plus (ems_kl_peak v Hv) (ems_ent v Hv))
                             (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                             (real_opp (ems_kl_peak v Hv)) (real_opp (ems_kl_peak v Hv))
                             (real_plus_comm (ems_kl_peak v Hv) (ems_ent v Hv))
                             (real_eq_refl (real_opp (ems_kl_peak v Hv))))
                          (real_eq_refl eps)).
              ** apply (real_eq_trans
                           (real_plus
                              (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                         (real_opp (ems_kl_peak v Hv)))
                              eps)
                           (real_plus
                              (real_plus (ems_ent v Hv)
                                         (real_plus (ems_kl_peak v Hv)
                                                    (real_opp (ems_kl_peak v Hv))))
                              eps)
                           (real_plus (ems_ent v Hv) eps)).
                --- apply (RealSetoid.real_eq_plus_compat_adapt
                             (real_plus (real_plus (ems_ent v Hv) (ems_kl_peak v Hv))
                                        (real_opp (ems_kl_peak v Hv)))
                             (real_plus (ems_ent v Hv)
                                        (real_plus (ems_kl_peak v Hv)
                                                   (real_opp (ems_kl_peak v Hv))))
                             eps eps
                             (real_eq_sym _ _
                                (real_plus_assoc (ems_ent v Hv) (ems_kl_peak v Hv)
                                                 (real_opp (ems_kl_peak v Hv))))
                             (real_eq_refl eps)).
                --- apply (real_eq_trans
                             (real_plus
                                (real_plus (ems_ent v Hv)
                                           (real_plus (ems_kl_peak v Hv)
                                                      (real_opp (ems_kl_peak v Hv))))
                                eps)
                             (real_plus (real_plus (ems_ent v Hv) real_zero) eps)
                             (real_plus (ems_ent v Hv) eps)).
                    +++ apply (RealSetoid.real_eq_plus_compat_adapt
                                 (real_plus (ems_ent v Hv)
                                            (real_plus (ems_kl_peak v Hv)
                                                       (real_opp (ems_kl_peak v Hv))))
                                 (real_plus (ems_ent v Hv) real_zero)
                                 eps eps
                                 (RealSetoid.real_eq_plus_compat_adapt
                                    (ems_ent v Hv) (ems_ent v Hv)
                                    (real_plus (ems_kl_peak v Hv)
                                               (real_opp (ems_kl_peak v Hv)))
                                    real_zero
                                    (real_eq_refl (ems_ent v Hv))
                                    (real_plus_opp (ems_kl_peak v Hv)))
                                 (real_eq_refl eps)).
                    +++ apply (RealSetoid.real_eq_plus_compat_adapt
                                 (real_plus (ems_ent v Hv) real_zero)
                                 (ems_ent v Hv)
                                 eps eps
                                 (real_plus_zero (ems_ent v Hv))
                                 (real_eq_refl eps)).
  }
  (* 组装：Su ≤ Su + (KLu − KLv + eps) [H1] 经 H2 换向至 Su ≤ Sv + eps *)
  exact (RealSetoid.real_le_id_r (ems_ent u Hu)
           (real_plus (ems_ent u Hu)
                      (real_plus (real_plus (ems_kl_peak u Hu)
                                            (real_opp (ems_kl_peak v Hv)))
                                 eps))
           (real_plus (ems_ent v Hv) eps)
           H2 H1).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3（峰界）：约束片上一切正温的熵 ≤ 峰熵 + eps。                     *)
(*   已注册 real_max_entropy_is_boltzmann_temp_eps 一步实例             *)
(*   （T := t*，q := p_u，Henergy := Hpinned u）。全片成立（左右皆然）， *)
(*   序前提省略（语义框架：t* 为片上熵峰）。                            *)
(* ---------------------------------------------------------- *)
Theorem ems_entropy_peak_bound_above :
  forall (u : Real) (Hu : real_lt real_zero u),
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (ems_ent u Hu) (real_plus ems_ent_star eps).
Proof.
  intros u Hu eps Heps.
  exact (real_max_entropy_is_boltzmann_temp_eps           S real_sum_over_S real_sum_pos_preserved           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear           real_sum_over_S_add           T_star T_star_pos energy           (ems_bt u Hu) (ems_bt_pos u Hu) (ems_bt_norm u Hu) (Hpinned u Hu)           eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 主件（G2·分离定理）：熵在 t* 左侧非降、右侧非增（prod 账，Set 形）。  *)
(*   升支左支 = 件 2（恒等式重组形态）＋降支 = 件 1（全库首件）          *)
(*   ＋峰界 = 件 3；三件同一证书面（Hpinned/Hkl_left/Hkl_right）。       *)
(* ---------------------------------------------------------- *)
Theorem ems_entropy_split_at_peak :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (ems_ent u Hu) (real_plus (ems_ent v Hv) eps)) *
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (ems_ent v Hv) (real_plus (ems_ent u Hu) eps)).
Proof.
  split.
  - intros u v Hu Hv Huv Hvt eps Heps.
    exact (ems_entropy_temp_mono_below u v Hu Hv Huv Hvt eps Heps).
  - intros u v Hu Hv Htu Huv eps Heps.
    exact (ems_entropy_temp_antitone_above u v Hu Hv Htu Huv eps Heps).
Qed.

End EmsEntropyMonoSplit.

(* ============ 假设审计（公理面：全零缺口方绿） ============ *)
Print Assumptions ems_pinned_kl_entropy_eq.
Print Assumptions ems_entropy_temp_antitone_above.
Print Assumptions ems_entropy_temp_mono_below.
Print Assumptions ems_entropy_peak_bound_above.
Print Assumptions ems_entropy_split_at_peak.

(* ============================================================ *)
(* 供给段（签名保持式消解，b3 §2.2.1；原节声明与既有定理签名零改）：               *)
(*   求和面五证书位在 ConcMixSelFeed 求和载体 csm_sumf（UpReqConcSoftmax:66       *)
(*   定义面）上取 S:=bool、enum:=true::false::nil 实例化：                       *)
(*   外延/序/齐性/加法四位引 cms 系四件（ConcMixSelFeed:172/:243/:183/:212），      *)
(*   正性位由 sumd_list_sum_pos（UpReqSumD:312，非空清单逐点严格正 ⟹ 和严格正）    *)
(*   供给。抽象层五证书位保持假设身份（对抽象求和算子不可树内推导），本段为        *)
(*   具体实例上的消解证书，供使用方以实例充任接口字段。三层显式标注之段注层：       *)
(*   头注层已标面外扩展与消解判定，逐定理注层见各供给定理上方。                    *)
(* ============================================================ *)
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.

Definition urems_enum : list bool := true :: false :: nil.

(* 正性位供给：和载体按非空清单折叠，逐点严格正 ⟹ 和严格正                        *)
(*   （sumd_list_sum_pos 实例装配：非空前提 discriminate，逐点前提直传）。         *)
Theorem urems_sum_pos_supply :
  forall f : bool -> Real,
    (forall s : bool, lt zero (f s)) ->
    lt zero (csm_sumf bool urems_enum f).
Proof.
  intros f Hpt.
  unfold csm_sumf.
  apply (@sumd_list_sum_pos Real RealEnhancedReal bool f urems_enum).
  - intros Hnil.
    discriminate Hnil.
  - exact Hpt.
Qed.

(* 外延位供给：逐点 req ⟹ 和 req（cms_sum_ext 一步实例，语句面同供给常量系）。 *)
Theorem urems_sum_ext_supply :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (csm_sumf bool urems_enum f) (csm_sumf bool urems_enum g).
Proof.
  intros f g H.
  exact (cms_sum_ext bool urems_enum f g H).
Qed.

(* 序位供给：逐点 le ⟹ 和 le（cms_sum_le 一步实例，语句面同供给常量系）。 *)
Theorem urems_sum_le_supply :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (csm_sumf bool urems_enum f) (csm_sumf bool urems_enum g).
Proof.
  intros f g H.
  exact (cms_sum_le bool urems_enum f g H).
Qed.

(* 齐性位供给：数乘穿和（cms_sum_linear 一步实例）。 *)
Theorem urems_sum_linear_supply :
  forall (a : Real) (f : bool -> Real),
    req (csm_sumf bool urems_enum (fun s : bool => mult a (f s)))
            (mult a (csm_sumf bool urems_enum f)).
Proof.
  intros a f.
  exact (cms_sum_linear bool urems_enum a f).
Qed.

(* 加法位供给：逐项和等于和之逐项加（cms_sum_add 一步实例）。 *)
Theorem urems_sum_add_supply :
  forall f g : bool -> Real,
    req (csm_sumf bool urems_enum (fun s : bool => plus (f s) (g s)))
            (plus (csm_sumf bool urems_enum f)
                  (csm_sumf bool urems_enum g)).
Proof.
  intros f g.
  exact (cms_sum_add bool urems_enum f g).
Qed.

(* ---- 供给段假设审计（五连 Print Assumptions） ---- *)
Print Assumptions urems_sum_pos_supply.
Print Assumptions urems_sum_ext_supply.
Print Assumptions urems_sum_le_supply.
Print Assumptions urems_sum_linear_supply.
Print Assumptions urems_sum_add_supply.

(* ============================================================ *)
(* 供给段二（实例化时点消解证书，W12 先例形态；原节声明与既有定理签名零改）：       *)
(*   峰温 T_star 正性前提（原假设形 real_lt real_zero T_star，T* 为自由参数，      *)
(*   对抽象参数不可树内推导，抽象层保持假设身份）的具体见证供给：                  *)
(*   见证一 T*:=real_one——引 S07 已证引理 real_lt_zero_one（S07:6966）；          *)
(*   见证二 T*:=cf2_temp（UpReqConcFin2:98，定义性等于 one）——引 cf2_temp_pos      *)
(*   （UpReqConcFin2:100），本件语句面取同款类字段形 lt zero cf2_temp（同常量       *)
(*   对齐，边界 cast 自然消失；lt/zero 与 real_lt/real_zero 定义性一致凭证在库；     *)
(*   与 ConcFin2 载体族同源，供融合侧按载体族整取。                                  *)
(*   整取。三层显式标注之段注层同前段。                                            *)
(* ============================================================ *)
Require Import UpReqConcFin2.

Theorem urems_tstar_one_pos_supply : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

Theorem urems_tstar_cf2temp_pos_supply : lt zero cf2_temp.
Proof.
  exact cf2_temp_pos.
Qed.

(* ---- 供给段二假设审计（二连 Print Assumptions） ---- *)
Print Assumptions urems_tstar_one_pos_supply.
Print Assumptions urems_tstar_cf2temp_pos_supply.
