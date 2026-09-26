(* ============================================================
   使命：本件定理/引理声明面所述性质的形式化（原头注为历史注记块，
         实质整编候后波；本块为五字段指针）。
   依赖：件内 Require 声明面所列库件。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)

(* ============================================================ *)
(* UpReqMinUniqueTight.v *)
(* *)
(* 目的： 定理 4.5 free_energy_min_unique 的 Real 层两可达形。 *)
(* 主件： t15_free_energy_min_unique 与 t15_fe_eq_kl_zero 等价核；严格分歧肢 t15_fe_strict_*。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqRealFEP、UpReqFEPCanon、G07_KLWall、UpReqKLSTangent、G08_Gibbs。 *)
(* 备注： 承定理 4.3 构造性边界；bool 形与 Or 形双编码并存。 *)
(* 构造性注记：Set 层承载、零承认、可提取。 *)
(* 编译配方：rocq 9.1 直调 + cpu_guard。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqMinUniqueTight.v —— 定理 4.5 free_energy_min_unique *)

(* ------------------------------------------------------------------ *)
(* 【使命】判定（C3）：定理 4.5（论文正式版 L284-286：若            *)
(*   F[p] = F[p_b] 则 p 与 p_b 逐点相等；〔构造强度〕「等式/唯一性档——  *)
(*   承定理 4.3 的构造性边界；Real 层无复刻」）的 Real 层两可达形：      *)
(*   (a) gibbe2 式显式前提形：log 切线收缩前提 + KL≡0 ⟹ 逐点 real_eq；  *)
(*   (b) 严格见证逆否形：显式分歧见证（某 s₀ 处 Or 见证）⟹ KL>0 ⟹      *)
(*       F[p] − F[p_b] = D·KL > 0 ⟹ F 严格差（D>0）。                  *)
(* ------------------------------------------------------------------ *)
(*   F[p]        ↔ real_free_energy S sumf real_base_loss D p Hp        *)
(*   p_b（锚）   ↔ real_boltzmann_dist_r（π* 锚闭式解实例）             *)
(*   KL 逐项和   ↔ Σ real_kl_term(p s, p_b s)                           *)
(*   F 严格差    ↔ real_lt (F[p_b]) (F[p])（real_lt 为 Set 层 eps 见证）*)
(*   分歧见证    ↔ Or (real_lt (p s₀) (p_b s₀)) (real_lt (p_b s₀) (p s₀)) *)
(*   逐点等      ↔ real_eq（RealSetoid 等值载体）                       *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（各步引用件名）】                                     *)
(*   件 0 切点谓词 t15_tangent_eq（显式前提形的逐点结论面，Set 层）。    *)
(*   件 1 等值核 t15_fe_eq_kl_zero：F 等（Feq）沿 X2 正典分解件         *)
(*     real_kl_decomp_full_canon 运输 ⟹ F[p_b] ≡ F[p_b] + D·KL ⟹       *)
(*     加法消去（S08 real_eq_plus_cancel_l）⟹ D·KL ≡ 0 ⟹ D>0 右因子    *)
(*     消去（S08 real_eq_mult_cancel_r + real_mult_comm 两跳）⟹        *)
(*     ELBO 等值核。）                                                  *)
(*   件 2 可达形 (a) 显式前提形 t15_fe_eq_unique_explicit（抽象载体）：  *)
(*     件 1 + 显式接口前提「KL≡0 ⟹ 逐点切点式」（gibbe2 主件注入位     *)
(*     的载体级抬升）+ t1_log_eq_linear_inject（「切点⟹一」，      *)
(*     无条件消解）+ gibbe2 主件尾链同款比值一消去（G08                 *)
(*     gibbsd_p_mult_ratio）⟹ 逐点 p s ≡ p_b s。                       *)
(*   件 3 可达形 (a) bool 完成 t15_fe_eq_unique_bool：件 1 的 bool      *)
(*     载体实例 + t1_gibbe2_gibbs_equality_bool 整链消解（KL≡0    *)
(*     ⟹ 逐点等直达）——样板载体上零接口前提。                          *)
(*   件 4 严格尾链 t15_fe_strict_of_kl_pos（list 载体）：KL>0 ⟹         *)
(*     D·KL>0（S07 real_mult_pos_compat）⟹ 加法平移（S07               *)
(*     real_lt_plus_translate）⟹ real_lt_compat 运输两跳 ⟹             *)
(*     F[p_b] < F[p]（real_lt，Set 层 eps 见证）。                      *)
(*   件 5 可达形 (b) 单向可比版 t15_fe_strict_divergence_le：逐项       *)
(*     p ≤ p_b + s₀ 处严格分离 ⟹ G07 klst_kl_sum_strict ⟹ 件 4。       *)
(*   件 6 可达形 (b) 双向见证版 t15_fe_strict_divergence_or：逐项双向   *)
(*     可比（Or 承载，诚实接口位）+ s₀ 处双向严格分离见证 ⟹ G07        *)
(*     klst_kl_energy_nonconst ⟹ 件 4。                                *)
(*   件 7 可达形 (b) bool 完成 t15_fe_strict_divergence_bool：件 6      *)
(*     在 [true; false] 载体、s₀ := true 的实例。                       *)
(*   件 8 组装件 t15_free_energy_min_unique（bool 载体，prod 双函数     *)
(*     记录——Set 层 And 形，零 Prop）：(Feq ⟹ 逐点等) × (可比 +        *)
(*     见证 ⟹ F 严格差)。(a) 肢零接口前提；(b) 肢保留逐项可比的        *)
(*     诚实接口位。                                                     *)
(* ------------------------------------------------------------------ *)
(* 【可达强度如实标注】                                                 *)
(*   ① 可达形 (a) 两档：抽象载体为显式接口形（件 2，接口位=「KL≡0 ⟹    *)
(*     逐点」非负提取步的载体诚实接口）；bool 样板载体由整链件     *)
(*     完全消解（件 3/件 8 (a) 肢，零接口残留）。                       *)
(*   ② 无条件形不可达机理（如实标注）：仅凭 Feq : F[p] ≡ F[p_b]（无     *)
(*     收缩前提、无分歧见证）得逐点等，其机理链需「KL≡0 ⟹ 逐点切点式」 *)


(*     结论在案，构造性不可达。本件改用其弱形「切点⟹一」（         *)
(*     t1_log_eq_linear_inject：弱三分 + 双支切线，不触判定边界），     *)
(*     该弱形在盘无条件闭合，件 2/3 即弱形闭合实例。                    *)
(*   ③ 可达形 (b) 逐项可比前提为诚实接口位：去除逐项 Or (real_le)       *)
(*     (real_le) 等价于对任意实对给三分判定见证（LLPO 形），非直觉主义  *)
(*     可证（在库结论）；s₀ 处分歧见证以 Set 层 Or (real_lt) 承载    *)
(*     （实序不可判定，显式见证输入）。F[p]−F[p_b] = D·KL 核算由正典   *)
(*     分解逐字保留（D 因子不吸收、不缩水），严格肢 = D>0 × KL>0。      *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_eq/real_lt/real_le 全 Set 值，组装载体   *)
(*   prod 双函数记录）；全 Qed 闭合；禁词条目零命中（头注以中文转述，   *)
(*   不引英文原词）；real_eq 非 Id 禁改写，全链 real_eq_trans /         *)
(*   RealSetoid 运输；D 因子逐字保留。禁改红线：UpReqRealFEP.v /        *)
(*   UpReqFEPCanon.v / UpReqKLSTangent.v / G07_KLWall.v / G08_Gibbs.v   *)
(*   / S 模块全程只读（只使用 .vo）。                                   *)

(*   全量 -Q vo 树；前置 .vo 全在 ConstructiveWorld_vo/。               *)
(* ============================================================ *)

From Stdlib Require Import List.
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
Require Import UpReqRealFEP.
Require Import UpReqFEPCanon.
Require Import G07_KLWall.
Require Import UpReqKLSTangent.
Require Import G08_Gibbs.
Import ListNotations.

(* ---------------------------------------------------------- *)
(* 件 0：切点式谓词（显式前提形的逐点结论面，Set 层）                    *)
(*   对位 G08 gibbe2 注入位的逐点结论：                                 *)

(* ---------------------------------------------------------- *)

Definition t15_tangent_eq
  (S : Type) (real_base_loss : S -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (Z_align_r : Real)
  (Z_align_r_pos : real_lt real_zero Z_align_r)
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (s : S) :=
  real_eq
    (real_log
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (p s) (Hp s)))
       (real_mult_positive
          (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos (p s) (Hp s))
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (real_inv_pos_pos (p s) (Hp s))))
    (real_plus
       (real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                  (real_inv_pos (p s) (Hp s)))
       (real_opp real_one)).

(* ---------------------------------------------------------- *)
(* 件 1：等值核——F[p] ≡ F[p_b] ⟹ KL ≡ 0（抽象载体）                    *)
(*   链：Feq 沿正典分解件运输 ⟹ F[p_b] ≡ F[p_b] + D·KL ⟹ 加法消去     *)
(*   ⟹ D·KL ≡ 0 ⟹ D>0 右因子消去 ⟹ KL ≡ 0。                           *)
(* ---------------------------------------------------------- *)

Lemma t15_fe_eq_kl_zero :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_free_energy S real_sum_over_S real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  real_eq (real_sum_over_S
             (fun s : S => real_kl_term (p s)
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
          real_zero.
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Feq.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (KLsum := real_sum_over_S (fun s : S => real_kl_term (p s) (pb s) (Hp s) (pbpos s))).
  set (Fp := real_free_energy S real_sum_over_S real_base_loss D p Hp).
  set (Fb := real_free_energy S real_sum_over_S real_base_loss D pb pbpos).
  (* 第 1 步：正典分解（X2 real_kl_decomp_full_canon）：F[p] ≡ F[p_b] + D·KL *)
  assert (Hdec : real_eq Fp (real_plus Fb (real_mult D KLsum))).
  { exact (real_kl_decomp_full_canon S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb). }
  (* 第 2 步：Feq 沿分解运输：F[p_b] ≡ F[p_b] + D·KL *)
  assert (Hloop : real_eq Fb (real_plus Fb (real_mult D KLsum))).
  { exact (real_eq_trans Fb Fp (real_plus Fb (real_mult D KLsum))
             (real_eq_sym Fp Fb Feq) Hdec). }
  (* 第 3 步：加法消去：D·KL ≡ 0（S08 real_eq_plus_cancel_l） *)
  assert (Hdk : real_eq (real_mult D KLsum) real_zero).
  { apply (real_eq_plus_cancel_l Fb (real_mult D KLsum) real_zero).
    apply (real_eq_trans (real_plus Fb (real_mult D KLsum)) Fb (real_plus Fb real_zero)).
    - exact (real_eq_sym Fb (real_plus Fb (real_mult D KLsum)) Hloop).
    - exact (real_eq_sym (real_plus Fb real_zero) Fb (real_plus_zero Fb)). }
  (* 第 4 步：D>0 消去：KL ≡ 0（comm 两跳 + S08 右因子消去） *)
  apply (real_eq_mult_cancel_r KLsum real_zero D D_pos).
  apply (real_eq_trans (real_mult KLsum D) real_zero (real_mult real_zero D)).
  - apply (real_eq_trans (real_mult KLsum D) (real_mult D KLsum) real_zero).
    + exact (real_mult_comm KLsum D).
    + exact Hdk.
  - exact (real_eq_trans real_zero (real_mult D real_zero) (real_mult real_zero D)
             (real_eq_sym (real_mult D real_zero) real_zero (real_mult_zero D))
             (real_mult_comm D real_zero)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 2：可达形 (a)——gibbe2 式显式前提形（抽象载体）                    *)
(*   F[p] ≡ F[p_b]（⟹ KL ≡ 0，件 1）+ 显式接口前提（KL≡0 ⟹ 逐点切点式）*)
(*   ⟹ 逐点 p s ≡ p_b s。                                               *)
(*   逐点消去链：切点式 + t1_log_eq_linear_inject（切点⟹一，       *)
(*   无条件）⟹ 比值一 ⟹ gibbe2 主件尾链同款消去 ⟹ p s ≡ p_b s。        *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_eq_unique_explicit :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  (* 显式接口前提位（载体诚实接口）：KL ≡ 0 ⟹ 逐点切点式；
     bool 样板载体上由件 3 整链消解（整链件直达），零残留。 *)
  (real_eq (real_sum_over_S
              (fun s : S => real_kl_term (p s)
                 (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (Hp s)
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
           real_zero ->
   forall s : S,
     t15_tangent_eq S real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp s) ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_free_energy S real_sum_over_S real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  forall s : S,
    real_eq (p s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros S real_sum_over_S sumf_ext sumf_add sumf_linear
         real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Htan0 Feq s.
  set (pb := real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos).
  (* 第 1 步：等值核（件 1）：KL ≡ 0 *)
  assert (Hkl0 : real_eq (real_sum_over_S
                            (fun s0 : S => real_kl_term (p s0) (pb s0) (Hp s0) (pbpos s0)))
                         real_zero).
  { exact (t15_fe_eq_kl_zero S real_sum_over_S sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq). }
  (* 第 2 步：切点式 + 「切点⟹一」（无条件消解）⟹ 比值一 *)
  assert (Hu1 : real_eq (real_mult (pb s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (t1_log_eq_linear_inject (real_mult (pb s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (pb s) (real_inv_pos (p s) (Hp s))
                (pbpos s) (real_inv_pos_pos (p s) (Hp s)))).
    exact (Htan0 Hkl0 s). }
  (* 第 3 步：比值一 ⟹ p s ≡ p_b s（gibbe2 主件尾链同款） *)
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (pb s) (real_inv_pos (p s) (Hp s))))
           (pb s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (pb s) (real_inv_pos (p s) (Hp s))))).
    + exact (real_eq_sym (real_mult (p s) real_one) (p s) (real_mult_one (p s))).
    + exact (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (pb s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (pb s) (real_inv_pos (p s) (Hp s))) real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (pb s) (Hp s)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 3：可达形 (a) bool 完成——显式接口前提整链消解形                   *)
(*   显式前提位由t1_gibbe2_gibbs_equality_bool 整链消解            *)
(*   （KL≡0 ⟹ 逐点 p≡p_b 直达，注入位由 t1_log_eq_linear_inject        *)
(*   无条件供给）：gibbe2 样板载体上 (a) 形零接口前提（除物理前提）。    *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_eq_unique_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  real_eq (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D p Hp)
          (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false])
             real_base_loss D
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)) ->
  forall s : bool,
    real_eq (p s)
            (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq s.
  apply (t1_gibbe2_gibbs_equality_bool p
           (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hnormp Hnormb).
  exact (t15_fe_eq_kl_zero bool
           (fun f : bool -> Real => real_list_sum bool f [true; false])
           (fun (f g : bool -> Real)
                (Hfg : forall s : bool, real_eq (f s) (g s)) =>
              real_list_sum_ext bool f g [true; false] Hfg)
           (fun f g : bool -> Real => real_list_sum_add bool f g [true; false])
           (fun (a : Real) (f : bool -> Real) =>
              real_list_sum_linear bool a f [true; false])
           real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Feq).
Qed.

(* ---------------------------------------------------------- *)
(* 件 4：严格尾链——KL > 0 ⟹ F[p_b] < F[p]（list 载体，real_lt）         *)
(*   链：D·KL > 0（real_mult_pos_compat）⟹ 加法平移                    *)
(*   （real_lt_plus_translate）⟹ real_lt_compat 运输两跳 ⟹ 严格差。     *)
(*   F[p]−F[p_b] 核算由正典分解逐字保留（D 因子不吸收）。               *)
(* ---------------------------------------------------------- *)

Lemma t15_fe_strict_of_kl_pos :
  forall (X : Type) (L : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p L) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos) L)
          real_one ->
  real_lt real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s)
          (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
          (Hp s)
          (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       L) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f L) real_base_loss D p Hp).
Proof.
  intros X L real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hkl.
  set (pb := real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (pbpos := real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos).
  set (sumf := fun f : X -> Real => real_list_sum X f L).
  set (KLsum := real_list_sum X (fun s : X => real_kl_term (p s) (pb s) (Hp s) (pbpos s)) L).
  set (Fp := real_free_energy X sumf real_base_loss D p Hp).
  set (Fb := real_free_energy X sumf real_base_loss D pb pbpos).
  (* 第 1 步：正典分解：F[p] ≡ F[p_b] + D·KL *)
  assert (Hdec : real_eq Fp (real_plus Fb (real_mult D KLsum))).
  { exact (real_kl_decomp_full_canon X sumf
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g L Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g L)
             (fun (a : Real) (f : X -> Real) => real_list_sum_linear X a f L)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb). }
  (* 第 2 步：D·KL > 0（D>0 × KL>0） *)
  assert (HdK : real_lt real_zero (real_mult D KLsum)).
  { exact (real_mult_pos_compat D KLsum D_pos Hkl). }
  (* 第 3 步：加法平移：F[p_b] + 0 < F[p_b] + D·KL *)
  assert (Hshift : real_lt (real_plus Fb real_zero) (real_plus Fb (real_mult D KLsum))).
  { exact (real_lt_plus_translate Fb real_zero (real_mult D KLsum) HdK). }
  (* 第 4 步：零右端化简：F[p_b] < F[p_b] + D·KL *)
  assert (Hcore : real_lt Fb (real_plus Fb (real_mult D KLsum))).
  { exact (RealSetoid.real_lt_compat (real_plus Fb real_zero) Fb
             (real_plus Fb (real_mult D KLsum)) (real_plus Fb (real_mult D KLsum))
             (real_plus_zero Fb)
             (real_eq_refl (real_plus Fb (real_mult D KLsum)))
             Hshift). }
  (* 第 5 步：沿分解运输：F[p_b] < F[p] *)
  exact (RealSetoid.real_lt_compat Fb Fb
           (real_plus Fb (real_mult D KLsum)) Fp
           (real_eq_refl Fb)
           (real_eq_sym Fp (real_plus Fb (real_mult D KLsum)) Hdec)
           Hcore).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：可达形 (b) 单向可比版——逐项 p ≤ p_b + s₀ 处严格分离            *)
(*   ⟹ G07 klst_kl_sum_strict ⟹ KL > 0 ⟹ 件 4 ⟹ F 严格差。            *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_le :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (forall s : X, real_le (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)) ->
  real_lt (p s₀)
    (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D p Hp).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hpq Hdiv.
  apply (t15_fe_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb).
  exact (klst_kl_sum_strict X l₁ s₀ l₂ p
           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hpq Hnormp Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 6：可达形 (b) 双向见证版——逐项双向可比（Or 承载，诚实接口位）+     *)
(*   s₀ 处双向严格分离见证 ⟹ G07 klst_kl_energy_nonconst ⟹ KL>0        *)
(*   ⟹ 件 4 ⟹ F 严格差。                                               *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_or :
  forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one ->
  real_eq (real_list_sum X
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (l₁ ++ s₀ :: l₂)) real_one ->
  (* 逐项双向可比（诚实接口位：去除等价 LLPO 形，非直觉主义可证） *)
  (forall s : X,
     Or (real_le (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (p s))) ->
  (* s₀ 处显式分歧见证（Set 层 Or 承载，任一方向） *)
  (Or (real_lt (p s₀)
               (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀))
      (real_lt (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos s₀)
               (p s₀))) ->
  real_lt (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy X
             (fun f : X -> Real => real_list_sum X f (l₁ ++ s₀ :: l₂)) real_base_loss D p Hp).
Proof.
  intros X l₁ s₀ l₂ real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb Hpq Hdiv.
  apply (t15_fe_strict_of_kl_pos X (l₁ ++ s₀ :: l₂) real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb).
  exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p
           (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hp
           (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r Z_align_r_pos)
           Hpq Hnormp Hnormb Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 7：可达形 (b) bool 完成——件 6 在 [true; false] 载体的实例          *)
(*   （s₀ := true，l₁ := []，l₂ := [false]）。                          *)
(* ---------------------------------------------------------- *)

Theorem t15_fe_strict_divergence_bool :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  (forall s : bool,
     Or (real_le (p s)
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
        (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                 (p s))) ->
  (Or (real_lt (p true)
               (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
      (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
               (p true))) ->
  real_lt (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false]) real_base_loss D
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
          (real_free_energy bool
             (fun f : bool -> Real => real_list_sum bool f [true; false]) real_base_loss D p Hp).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Hpq Hdiv.
  exact (t15_fe_strict_divergence_or bool [] true [false] real_base_loss D D_pos
           Z_align_r Z_align_r_pos p Hp Hnormp Hnormb Hpq Hdiv).
Qed.

(* ---------------------------------------------------------- *)
(* 件 8：组装件（bool 载体，prod 双函数记录——Set 层 And 形，零 Prop）    *)
(*   定理 4.5 两可达形的合取载体：(a) 肢（F 等 ⟹ 逐点等，零接口）×      *)
(*   (b) 肢（逐项可比 + s₀ 分歧见证 ⟹ F 严格差）。                      *)
(* ---------------------------------------------------------- *)

Theorem t15_free_energy_min_unique :
  forall (real_base_loss : bool -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : bool -> Real) (Hp : forall s : bool, real_lt real_zero (p s)),
  real_eq (real_list_sum bool p [true; false]) real_one ->
  real_eq (real_list_sum bool
             (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
             [true; false]) real_one ->
  prod (real_eq (real_free_energy bool
                   (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D p Hp)
                (real_free_energy bool
                   (fun f : bool -> Real => real_list_sum bool f [true; false])
                   real_base_loss D
                   (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
                   (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
        -> forall s : bool,
             real_eq (p s)
                     (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
       ((forall s : bool,
           Or (real_le (p s)
                         (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s))
              (real_le (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                       (p s)))
        -> (Or (real_lt (p true)
                        (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true))
               (real_lt (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos true)
                        (p true)))
        -> real_lt (real_free_energy bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D
                      (real_boltzmann_dist_r bool real_base_loss D D_pos Z_align_r Z_align_r_pos)
                      (real_boltzmann_dist_r_pos bool real_base_loss D D_pos Z_align_r Z_align_r_pos))
                   (real_free_energy bool
                      (fun f : bool -> Real => real_list_sum bool f [true; false])
                      real_base_loss D p Hp)).
Proof.
  intros real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp Hnormb.
  split.
  - exact (t15_fe_eq_unique_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             p Hp Hnormp Hnormb).
  - exact (t15_fe_strict_divergence_bool real_base_loss D D_pos Z_align_r Z_align_r_pos
             p Hp Hnormp Hnormb).
Qed.
