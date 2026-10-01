(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编尚待后续）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ============================================================ *)
(* 基准：Main/Live/G04ProjHook.v（565 注册面最新基线，只读零写）。      *)
(* 语句面/声明名序/依赖面/自检面与基准逐字一致。勘面已证结论：本件系闭名    *)
(* 喂定钩（CYC11 使命），Proj/Z_P 语句含 inv Z 因子阻断转换层重演，      *)
(* 独立重演须内联母定理 Z≡1 归一链＝引擎体重演，故仅换一处可独立闭合的   *)
(* 证明体：逐出支归零件不再把荒谬前提转发进 proj_drop_zero 引擎槽，      *)
(* 改在定义层直灭——g4p_P 恒真（beta/delta 透明），Id (g4p_P i) false     *)
(* 前提为构造子不相等式，判别引擎当场消解任意目标，零引擎使用。          *)
(* 红线自审：零公理零承认；零新增依赖；纯构造性 Set 层零泄露；真 Qed；   *)
(* Main 整目录只读；本稿落消融50 写区。                                 *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                              *)
(* 使命：CYB7 未决事项——G04 W2' 簇母定理回接实例化。fa57_ext.v      *)
(*       簇四（fa57_W2p_uniform_two_realized）已在 S01 接口R 世界  *)
(*       喂定 G04_ProjFam.v 投影母定理（ZP/proj 闭名），产出        *)
(*       「母定理在具体族上成立」的实例化定理九件。                 *)
(*                                                              *)
(* 对账结论（母定理参数面 vs 两点族供给面，差什么补什么）：          *)
(*   面 1 载体差：fa57 供件走 RealInterfaceEnhanced 的 @R RI 抽象  *)
(*      世界（Id／fa51_sumd）；母定理闭名走 S02 柯西 Real 具体层    *)
(*      （real_eq／real_list_sum）。两载体不同构，全库亦无         *)
(*      RealInterface 在 Real 上的实例可作接口桥——故相容桥取       *)
(*      「Real 层同构转换」：two := 1+1、half := inv(two)、         *)
(*      half+half==one 归一链逐段同构 fa57 簇四蓝图                 *)
(*      （mult_one×2 → distrib → mult_comm → inv_pos_correct）。    *)
(*   面 2 参序差（判例「用了谁泛化谁」，g4p_probe_sig 检验打表      *)
(*      实证）：ZP_pos 六参无 f_norm；ZP_le_one 六参无 P_witness；  *)
(*      proj_keep_ge／proj_minor_uncond 七参带 f_norm；             *)
(*      proj_kl_cost 六节参无 f_norm；KLqf 连 P／P_witness 都不收   *)
(*      （I f idx f_pos q Hq 五节参）；其余六参。                   *)
(*   面 3 逐出支差：本族 P 恒真（无假支），逐出槽语句按前提转发形    *)
(*      保持母形——荒谬前提 Id true false 只入签名不消去（零空匹配，  *)
(*      提取零魔力位），与 proj_kl_cost 的 Hq_fail 槽同法自喂。      *)
(*                                                              *)
(* 宿主零改动：只读使用 vorebuild_901 基座＋G04_ProjFam，           *)
(*   前缀 g4p_ 全库防同名冲突；语句全 Set 层；纯构造性零承认位。          *)
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
Require Import G04_ProjFam.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ==================== 第一步：Real 层两点族补给件 ==================== *)
(* fa57 簇四蓝图的 Real 层转换：two := 1+1、half := inv(two)。       *)

Definition g4p_two : Real := real_plus real_one real_one.

Lemma g4p_two_pos : real_lt real_zero g4p_two.
Proof.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_one)
           (real_eq_sym _ _ (real_plus_zero real_zero))).
  apply (real_lt_plus_compat real_zero real_one real_zero real_one
           real_lt_zero_one real_lt_zero_one).
Qed.

Definition g4p_half : Real := real_inv_pos g4p_two g4p_two_pos.

Lemma g4p_half_pos : real_lt real_zero g4p_half.
Proof.
  exact (real_inv_pos_pos g4p_two g4p_two_pos).
Qed.

(* 归一链：half+(half+0) == half+half == half·1+half·1
   == half·(1+1) == half·two == two·half == one（六段 real_eq 运河，
   与 fa57_half_plus_half 的 Id 四段链同构转换）。 *)
Lemma g4p_half_norm :
  real_eq (real_list_sum bool (fun _ : bool => g4p_half) [true; false]) real_one.
Proof.
  cbn [real_list_sum].
  apply (real_eq_trans _
           (real_plus (real_mult g4p_half real_one) (real_mult g4p_half real_one)) _).
  - apply (RealSetoid.real_eq_plus_compat g4p_half (real_plus g4p_half real_zero)
             (real_mult g4p_half real_one) (real_mult g4p_half real_one)).
    + apply real_eq_sym. apply real_mult_one.
    + apply (real_eq_trans _ g4p_half _).
      * apply real_plus_zero.
      * apply real_eq_sym. apply real_mult_one.
  - apply (real_eq_trans _ (real_mult g4p_half g4p_two) _).
    + apply real_eq_sym. apply real_distrib.
    + apply (real_eq_trans _ (real_mult g4p_two g4p_half) _).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* 保留见证：P 恒真、idx 两点、true 在列（@InT_here 显式喂，CYB7 卡口径）。 *)
Definition g4p_witness :
  sigT (fun i : bool => And (Id ((fun _ : bool => true) i) true) (InT i [true; false]))
  := existT (fun i : bool => And (Id ((fun _ : bool => true) i) true) (InT i [true; false]))
            true (id_refl, @InT_here bool true [false]).

(* ==================== 第二步：相容桥（W2' 七槽面 Real 层转换包） ==================== *)
(* fa57_W2p_uniform_two_realized 的 Real 层同构件：f_norm∧f_pos∧     *)
(* P_witness 三槽一次兑现包——母定理闭名只认此层面，故为喂定入口。      *)

Theorem g4p_W2p_two_uniform_bridge :
  And (real_eq (real_list_sum bool (fun _ : bool => g4p_half) [true; false]) real_one)
      (And (forall i : bool, real_lt real_zero ((fun _ : bool => g4p_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  exact (g4p_half_norm, ((fun _ : bool => g4p_half_pos), g4p_witness)).
Qed.

(* ==================== 第三步：母定理闭名实例化主件 ==================== *)
(* 实例：I := bool、f ≡ half、P ≡ true、idx := [true; false]。        *)
(* 缩写（透明定义，语句面可读；使用位全经 delta/β/ι 转换回母形）。      *)

Definition g4p_f : bool -> Real := fun _ : bool => g4p_half.
Definition g4p_P : bool -> bool := fun _ : bool => true.
Definition g4p_idx : list bool := [true; false].
Definition g4p_Z : Real := Z_P bool g4p_f g4p_P g4p_idx.
Definition g4p_Proj (i : bool) : Real :=
  Proj bool g4p_f g4p_P g4p_idx (fun _ : bool => g4p_half_pos) g4p_witness i.

(* 件 0a：保留质量正（ZP_pos 六参喂定，无 f_norm 位）。 *)
Theorem g4p_ZP_pos_two : real_lt real_zero g4p_Z.
Proof.
  exact (ZP_pos bool g4p_f g4p_P g4p_idx
                (fun _ : bool => g4p_half_pos) g4p_witness).
Qed.

(* 件 0b：保留质量 ≤ 1（ZP_le_one 六参喂定，无 P_witness 位）。 *)
Theorem g4p_ZP_le_one_two : real_le g4p_Z real_one.
Proof.
  exact (ZP_le_one bool g4p_f g4p_P g4p_idx
                   g4p_half_norm (fun _ : bool => g4p_half_pos)).
Qed.

(* 件 1：行归一化 Σ Proj == 1。 *)
Theorem g4p_proj_normalized_two :
  real_eq (real_list_sum bool g4p_Proj g4p_idx) real_one.
Proof.
  exact (proj_normalized bool g4p_f g4p_P g4p_idx
                         (fun _ : bool => g4p_half_pos) g4p_witness).
Qed.

(* 件 3：逐出支归零（前提转发形：本族 P 恒真无假支，荒谬前提只入签名）。 *)
Theorem g4p_proj_drop_zero_two :
  forall i : bool, Id (g4p_P i) false -> real_eq (g4p_Proj i) real_zero.
Proof.
  intro i. intro Hb.
  exact (match Hb in Id _ b return
           (match b with
            | true => unit
            | false => real_eq (g4p_Proj i) real_zero
            end) with
         | id_refl => tt
         end).
Qed.

(* 件 2：保留者放大 f ≤ Proj。 *)
Theorem g4p_proj_keep_ge_two :
  forall i : bool, Id (g4p_P i) true -> real_le (g4p_f i) (g4p_Proj i).
Proof.
  exact (fun (i : bool) (Hb : Id (g4p_P i) true) =>
           proj_keep_ge bool g4p_f g4p_P g4p_idx g4p_half_norm
                        (fun _ : bool => g4p_half_pos) g4p_witness i Hb).
Qed.

(* 件 6：退化象（P 恒真 ⟹ Proj ≡ f）＝温度极限象连接；
   全真前提由 id_refl 逐点喂定。 *)
Theorem g4p_proj_uniform_full_two :
  (forall i : bool, Id (g4p_P i) true) ->
  forall i : bool, real_eq (g4p_Proj i) (g4p_f i).
Proof.
  intros P_all i.
  exact (proj_uniform_full bool g4p_f g4p_P g4p_idx g4p_half_norm
                           (fun _ : bool => g4p_half_pos) g4p_witness P_all i).
Qed.

(* 件 5：minorization 传送（取 u := f、delta := 1；
   前提 1·half == half 由 b4_one_mult 经 real_eq_le 转换）。 *)
Theorem g4p_proj_minor_uncond_two :
  forall i : bool, real_le (real_mult real_one (g4p_f i)) (g4p_Proj i).
Proof.
  exact (fun i : bool =>
           proj_minor_uncond bool g4p_f g4p_P g4p_idx g4p_half_norm
                             (fun _ : bool => g4p_half_pos) g4p_witness
                             g4p_f real_one
                             (fun i0 : bool =>
                                RealSetoid.real_eq_le
                                  (real_mult real_one (g4p_f i0)) (g4p_f i0)
                                  (b4_one_mult (g4p_f i0)))
                             i).
Qed.

(* 件 4（母定理主件·代价恒等）：KL(q‖f) == KL(q‖Proj) + (−log Z)，
   q := Proj 自喂（归一＝件 1、逐点正＝keepK_pos 证书随身、
   逐出归零＝件 3 转发——母定理自使用闭环）。 *)
Definition g4p_kl_q : bool -> Real := g4p_Proj.

Definition g4p_kl_q_pos :
  forall i : bool, real_lt real_zero (g4p_kl_q i)
  := fun i : bool =>
       keepK_pos bool g4p_f g4p_P g4p_idx
                 (fun _ : bool => g4p_half_pos) g4p_witness i.

Definition g4p_KLqf : Real :=
  KLqf bool g4p_f g4p_idx
       (fun _ : bool => g4p_half_pos) g4p_kl_q g4p_kl_q_pos.

Definition g4p_KLqp : Real :=
  KLqp bool g4p_f g4p_P g4p_idx
       (fun _ : bool => g4p_half_pos) g4p_witness g4p_kl_q g4p_kl_q_pos.

Definition g4p_neglogZ : Real :=
  real_opp (real_log (ZK bool g4p_f g4p_P g4p_idx)
                     (ZP_pos bool g4p_f g4p_P g4p_idx
                             (fun _ : bool => g4p_half_pos) g4p_witness)).

Theorem g4p_kl_cost_two : real_eq g4p_KLqf (real_plus g4p_KLqp g4p_neglogZ).
Proof.
  exact (proj_kl_cost bool g4p_f g4p_P g4p_idx
                      (fun _ : bool => g4p_half_pos) g4p_witness
                      g4p_kl_q g4p_proj_normalized_two
                      g4p_kl_q_pos g4p_proj_drop_zero_two).
Qed.

(* ============ 假设面闭合申报（G4 前置，九件全查） ============ *)

Print Assumptions g4p_two_pos.
Print Assumptions g4p_half_pos.
Print Assumptions g4p_half_norm.
Print Assumptions g4p_W2p_two_uniform_bridge.
Print Assumptions g4p_ZP_pos_two.
Print Assumptions g4p_ZP_le_one_two.
Print Assumptions g4p_proj_normalized_two.
Print Assumptions g4p_proj_drop_zero_two.
Print Assumptions g4p_proj_keep_ge_two.
Print Assumptions g4p_proj_uniform_full_two.
Print Assumptions g4p_proj_minor_uncond_two.
Print Assumptions g4p_kl_cost_two.
