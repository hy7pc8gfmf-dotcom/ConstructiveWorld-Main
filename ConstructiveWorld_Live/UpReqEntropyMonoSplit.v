(* ============================================================ *)
(* UpReqEntropyMonoSplit.v *)
(* *)
(* 目的： 约束化熵单调性分离定理（EXPL1 候选 C5 深探席 Q5）。 *)
(* 主件： ems_entropy_temp_antitone_above（降支，全库首件） /         *)
(*        ems_entropy_split_at_peak（升支+降支+峰界分离统一）。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqTempDefs、                   *)
(*        UpReqEntropyDeficitTemp、UpReqEntropyMaxTemp（四件全部在册）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqEntropyMonoSplit.v —— 席Q5：约束化熵单调性分离定理席           *)

(* ------------------------------------------------------------------ *)
(* 【使命】库内两线表面张力的定理化：防火墙线证「升温 ⟹ 熵不降」        *)
(*   （UpFirewall.v entropy_temp_mono，Id 层既件），TempUnimodalMax 线  *)
(*   证「熵在唯一温度处有峰」——两线蕴涵熵先升后降，但降支（t ≥ t* 段    *)
(*   熵不增）全库 0 件。本席补齐降支 + 峰温分界统一定理。               *)
(* ------------------------------------------------------------------ *)
(* 【C5 判词的定理化（约束出现与否 = 显式证书）】                       *)
(*   防火墙升支的引擎是 ΔE ≥ 0（升温抬能量 ⟹ 抬熵）；降支的对称障碍 =   *)
(*   ΔE ≤ 0 在高温段不成立（能量随温度仍升）——降支的正确引擎不是 ΔE     *)
(*   反号，而是【约束片】：把 C5 张力的未命名变量「约束出现与否」升格    *)
(*   为显式 Section 证书 Hpinned（片上 E(p_u) == E_{t*} 对一切正温 u）。*)
(*   约束片上熵亏恒等式（已注册 real_entropy_deficit_kl_temp）给        *)
(*     KL(p_u‖p_{t*}) + S(p_u) == S(p_{t*})                             *)
(*   再配 KL 增长证书（eps 松弛 Bishop 形，镜像已注册                    *)
(*   real_KL_temp_ge_zero_eps 的 0 ≤ KL+eps 形）：                      *)
(*     右支  0 ≤ KL(p_v‖p_{t*}) − KL(p_u‖p_{t*}) + eps   (t* ≤ u ≤ v)   *)
(*     左支  0 ≤ KL(p_u‖p_{t*}) − KL(p_v‖p_{t*}) + eps   (u ≤ v ≤ t_star) *)
(*   即得两侧单调性。峰界另由已注册 real_max_entropy_is_boltzmann_      *)
(*   temp_eps 一步实例给出。非圆性账：KL 证书是 eps 松弛的严格形而       *)
(*   结论带 eps 松弛，且 KL 证书是独立接口假设（非本席所证），          *)
(*   分离定理的内容 = 「KL-V 形 ⟹ 熵单峰」这一真实蕴涵。               *)
(* ------------------------------------------------------------------ *)
(* 【前提诚实分类】                                                     *)
(*   Section 证书（接口假设，全库无根，逐条如实标注）：                 *)
(*     Hpinned   约束片能量钉（C5「约束出现」变量的定理化载体）；        *)
(*     Hkl_right / Hkl_left  峰温 KL 增长/衰减证书（eps 松弛形）。      *)
(*   Section 接口（照 UpReqEntropyMaxTemp Section 同名同序，含扩容位     *)
(*   real_sum_over_S_le；具体载体实例 real_list_sum_le 在库非空）。     *)
(*   既件（全部 Require 消费，零重建）：real_entropy_deficit_kl_temp    *)
(*   （13 参）/ real_max_entropy_is_boltzmann_temp_eps（16 参）/        *)
(*   real_le_plus_nonneg_r / RealSetoid.real_le_id_r 等工具箱。         *)
(* ------------------------------------------------------------------ *)
(* 【跨层红线注记】UpFirewall.v 的 entropy_temp_mono 属 Id 层           *)
(*   （RealInterfaceEnhanced + Id/le/lt），与本席 raw Real 层           *)
(*   （real_eq/real_le）不同构，禁混引。升支左支以恒等式形态在本层       *)
(*   重组（任务书允许档，如实标注）：重组件 ems_entropy_temp_mono_below  *)
(*   与 Id 层既件在各自层内自洽，不互为主件。Z15 互联注记：升支方向      *)
(*   与 fw_kl ≤ 熵增（TempMonoW2Mark 恒等式族）同侧；降支不涉 TV，      *)
(*   不触碰 UpFirewall scoping 红线（:44 不主张 TV-熵传递）。           *)
(* 【G3 注记（诚实处置，不设伪件）】                                    *)
(*   1) N=1 退化端点：t* = u（u==v）时两支前提同时成立，结论退化为       *)
(*      自反（S ≤ S + eps，real_le_refl 档），无新内容，不设件；        *)
(*      t* 端点 0/∞ 需 real_lt real_zero T_star 之外的扩展接口，本席    *)
(*      不越权（T_star 正性是 boltzmann 族定义面的硬前提）。            *)
(*   2) ΔE 反号障碍：约束片外（自由族）恒等式 ΔS == β·ΔE + KL 两项      *)
(*      皆非负，降支不可达——此即本席必须走约束片的诚实理由。            *)
(* 【KL 方向性红线审计表（全文逐处核对）】                              *)
(*   ems_kl_peak u Hu := real_KL_temp … T_star T_star_pos energy        *)
(*      (ems_bt u Hu) (ems_bt_pos u Hu)  = KL(p_u ‖ p_{t*})：           *)
(*      p_u 占第一分布位（from），p_{t*} 占参考位（to）。与已注册       *)
(*      real_entropy_deficit_kl_temp 结论位同序（KL(q‖p_T)，q 前）。    *)
(*   Hkl_right 结论 real_le real_zero (KL_v − KL_u + eps)：KL_v 在前，   *)
(*      KL_u 取 real_opp——「KL 随温增」读向，禁倒置。                  *)
(*   Hkl_left  结论 real_le real_zero (KL_u − KL_v + eps)：镜像，        *)
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
(*   温度位固定为峰温 T_star；其后三证书位（本席新增接口假设）。         *)
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
(*   镜像已注册 real_KL_temp_ge_zero_eps 的 0 ≤ KL+eps 形）。           *)
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
(* 件 1（G1 旗舰·降支，全库首件）：峰右侧熵不增。                        *)
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
(*   不同构不互引；本件为约束片上 KL 衰减证书驱动的镜像件。             *)
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
  exact (real_max_entropy_is_boltzmann_temp_eps
           S real_sum_over_S real_sum_pos_preserved
           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear
           real_sum_over_S_add
           T_star T_star_pos energy
           (ems_bt u Hu) (ems_bt_pos u Hu) (ems_bt_norm u Hu) (Hpinned u Hu)
           eps Heps).
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
