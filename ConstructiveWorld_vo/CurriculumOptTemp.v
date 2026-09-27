(* ============================================================ *)
(* CurriculumOptTemp.v — 课程学习最优温度 eps-见证区间                 *)
(* 使命: SFCurriculum（经薄壳 CW219:13 Require   Export 可达）× *) (* EnergyTempMonoB etm_energy_temp_mono_b（B 层单调）× *) (* EpsOptimalReach rae_pick_optimal（有限表 argmin 支配形） *) (* ⟹ 课程损失（能量期望型）在温度轴上的 eps-最优温度区间： *) (* 给定有限扫温表（冷端锚 tmin + 表体 tab），forall eps>0 存在表内 *) (* 温度 t*，表内任一点 t 有：损失在 t* 处 < 损失在 t 处 + eps。 *) (* 路线: ①正温度点型 cot_ptemp := {t : Real & 0 < t}（sigT 载证）， *) (* 损失面 cot_loss := retm_Eexp；②cot_energy_temp_mono_b：B 层单调 *) (* 实例化（etm 内部 = 恒等档 × Bishop KL≥0 real_gibbs_inequality_B）； *) (* ③cot_tab_min_exists：冷端锚低于表体时最小元存在（InT 见证 + 逐点 *) (* B 形支配；Real 层 le 无二分判定（LPO 等价），单调链代判定器， *) (* 冷端即 argmin）；④主件 cot_optimal_temp_interval：②×③ 逐 eps *) (* 闭合——支配面 real_le_b 在 eps 处展开即 eps-见证区间。 *) (* 注记: 「课程损失 = 能量期望」接口识别未闭合——课程件以 B 档交付： *) (* 课程损失面单调（sf_curriculum_monotone 薄壳复用）经 *) (* real_le_to_le_b 提升为 Bishop 档；接口识别落地后可复用扫温链。 *) (* 依赖: CW_ConstructiveWorld_219（SFCurriculum 薄壳）、 *) (* RealEnergyTempMono（retm_Eexp）、EnergyTempMonoB、UpRealLeB； *) (* Stdlib List。 *) (* 对标: rae_pick_optimal（argmin 支配 eps-见证形同款）。 *) (* 构造性: 全件 Qed 闭合、零承认语句；语句面全 Set（real_lt/real_le_b/ *) (* InT/sigT/And），零经典逻辑；文末 Print Assumptions 逐件留痕。 *) (* 编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树   *)
(*   同世界重编），COQLIB/ROCQLIB 全字面环境前缀。                       *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
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
Require Import RealEnergyTempMono.
Require Import EnergyTempMonoB.
Require Import UpRealLeB.

(* ============================================================ *)
(* Part 0：正温度点型 + 能量期望损失面                                 *)
(* ============================================================ *)

(* 正温度点：载证数据（温度值 + 正性证书随数据走，sigT Set 面） *)
Definition cot_ptemp : Set := sigT (fun t : Real => real_lt real_zero t).

(* 损失面：温度 t 处的能量期望 E(t) := Σ p_t·u（retm_Eexp 直供） *)
Definition cot_loss (X : Set) (u : X -> Real) (s0 : X) (l : list X)
           (p : cot_ptemp) : Real :=
  retm_Eexp X u s0 l (projT1 p) (projT2 p).

(* Bishop 形自反：x ≤_B x（real_lt_plus_r_zero：0<eps ⟹ x<x+eps 直供） *)
Lemma cot_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x eps Heps.
  exact (real_lt_plus_r_zero x eps Heps).
Qed.

(* ============================================================ *)
(* Part 1：支撑件 1——能量-温度单调实例化件（etm:217 接入）              *)
(* ============================================================ *)

(* 温度 p < q ⟹ 损失(p) ≤_B 损失(q)
   etm_energy_temp_mono_b 在 cot_ptemp 载体上的实例化（B 层 real_le_b
   链：etm 内部 = 恒等档 × Bishop KL≥0（Gibbs 界）× 负系数反变闭合）。 *)
Lemma cot_energy_temp_mono_b :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X) (p q : cot_ptemp),
    real_lt (projT1 p) (projT1 q) ->
    real_le_b (cot_loss X u s0 l p) (cot_loss X u s0 l q).
Proof.
  intros X u s0 l p q Ht.
  exact (etm_energy_temp_mono_b X u s0 l
           (projT1 p) (projT2 p) (projT1 q) (projT2 q) Ht).
Qed.

(* ============================================================ *)
(* Part 2：支撑件 2——有限扫温表最小值存在件（rae 面装配）               *)
(* ============================================================ *)

(* 冷端锚 tmin 温度低于表体 tab 任一点 ⟹ 表 {tmin}∪tab 上存在最小元：
   InT 成员见证 + 逐点 B 形支配（And 为 Set 值积）。
   rae_pick_optimal 有限表 argmin 支配形的 monotone 对位：Real 层 le
   无二分判定，单调链代判定器——冷端即 argmin。 *)
Lemma cot_tab_min_exists :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X)
    (tab : list cot_ptemp) (tmin : cot_ptemp),
    (forall t : cot_ptemp, InT t tab -> real_lt (projT1 tmin) (projT1 t)) ->
    sigT (fun ts => And (InT ts (tmin :: tab))
      (forall t : cot_ptemp, InT t (tmin :: tab) ->
        real_le_b (cot_loss X u s0 l ts) (cot_loss X u s0 l t))).
Proof.
  intros X u s0 l tab tmin Hlb.
  exists tmin. split.
  - apply InT_here.
  - intros t Ht. inversion Ht as [Heq | y0 l0 Hin]; subst.
    + (* t = tmin：自反支（B 形） *)
      apply cot_le_b_refl.
    + (* t ∈ tab：温度严格低于 ⟹ 损失 B 单调（支撑件 1） *)
      exact (cot_energy_temp_mono_b X u s0 l tmin t (Hlb t Hin)).
Qed.

(* ============================================================ *)
(* Part 3：主件——eps-见证最优温度区间                                   *)
(* ============================================================ *)

(* 有限扫温表（冷端锚 + 表体）上，forall eps>0 存在表内温度 t*：
   表内任一点 t，损失在 t* 处 < 损失在 t 处 + eps（eps-见证形；
   见证非恒真壳：t* 的 InT 成员 + 逐点支配链走温度单调 × Gibbs B 界）。 *)
Theorem cot_optimal_temp_interval :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X)
    (tab : list cot_ptemp) (tmin : cot_ptemp),
    (forall t : cot_ptemp, InT t tab -> real_lt (projT1 tmin) (projT1 t)) ->
    forall eps : Real, real_lt real_zero eps ->
    sigT (fun ts => sigT (fun _ : InT ts (tmin :: tab) =>
      forall t : cot_ptemp, InT t (tmin :: tab) ->
        real_lt (cot_loss X u s0 l ts) (real_plus (cot_loss X u s0 l t) eps))).
Proof.
  intros X u s0 l tab tmin Hlb eps Heps.
  destruct (cot_tab_min_exists X u s0 l tab tmin Hlb) as [ts [Hmem Hdom]].
  exists ts. exists Hmem.
  intros t Ht.
  exact (Hdom t Ht eps Heps).
Qed.

(* ============================================================ *)
(* Part 4：课程受体支路——SFCurriculum 薄壳复用 + B 档提升（留桥注记）     *)
(* ============================================================ *)
(* 语义注记（A4 预警缺口，如实留桥）：本支路与主件的接口识别——「课程损失  *)
(*   = 能量期望（retm_Eexp 面）」尚未闭合；课程件以 B 档提升档交付：  *)
(*   课程损失面单调（受体 fold 累计式真证）经 real_le_to_le_b 提升为    *)
(*   Bishop 档，与主件同面（real_le_b）；接口落地后即可换面复用         *)
(*   Part 1–3 扫温链得课程损失面的 eps-最优温度区间。                    *)

Section CotCurriculumFace.
Variable SFModel : Set.
Variable cot_train_step : SFModel -> SFVec -> SFModel.
Variable cot_cur_loss : SFModel -> Real.
Hypothesis cot_step_ok :
  forall (m : SFModel) (smp : SFVec),
    real_le (cot_cur_loss (cot_train_step m smp)) (cot_cur_loss m).

(* 课程损失面单调（B 档）：课程跑完不增损失的受体件（fold 累计式）
   经 real_le_to_le_b 单向桥提升——Or 形前提与受体 sf_step_ok 同位
   显式超参。 *)
Theorem cot_curriculum_mono_b :
  forall (samples : list SFVec) (m : SFModel),
    real_le_b (cot_cur_loss (sf_curriculum_run SFModel cot_train_step samples m))
              (cot_cur_loss m).
Proof.
  intros samples m.
  exact (real_le_to_le_b _ _
           (sf_curriculum_monotone SFModel cot_train_step cot_cur_loss
              cot_step_ok samples m)).
Qed.

End CotCurriculumFace.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设                                           *)
(* ============================================================ *)
Print Assumptions cot_le_b_refl.
Print Assumptions cot_energy_temp_mono_b.
Print Assumptions cot_tab_min_exists.
Print Assumptions cot_optimal_temp_interval.
Print Assumptions cot_curriculum_mono_b.
