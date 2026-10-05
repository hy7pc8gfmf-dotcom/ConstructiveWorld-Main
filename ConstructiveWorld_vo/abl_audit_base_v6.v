(* ===================================================================== *)
(*  abl_audit_base_v6.v —— 审计承载扩容 v6·S13 审计引擎自靠面直审闭合件 *)
(* ===================================================================== *)
(*  使命: S13 审计引擎自靠面（审计引擎自身的可靠性面——「审计者谁来审计」问 *)
(*        题在本库的具体形态）的甲形态直审闭合: 对三引擎五条真定理各铸一条轻 *)
(*        量真行使承载（使用＝证明体真实行使上游定理非空壳），共五承载十一使 *)
(*        用点——① abf_early_stop_fuel_and_run 序贯置信停止燃料账主定理在 *)
(*        threshold:=1、max_iter:=5、acc:=[[0]] 具体实例＋早停计算面（零步消 *)
(*        解、结果恒 [[0]]）And 并载；② abf_early_stop_all_pass_concrete 早停 *)
(*        合格主定理具体候选表实例；③ abf_top_p_cumulative_concrete top-p 截 *)
(*        断累计主定理 p:=1 实例（Qle 仅前提位，判例合规）；④ abf_q_branch_ *)
(*        weight_conserved PRNG 分支权重守恒主定理一般形直引＋种子实例双重使 *)
(*        用；⑤ abf_resample_fallback 重采样兜底主定理 default_seq:=[0] 部分 *)
(*        实例化（消解首参就位）＋兜底计算面并载。 *)
(*  依赖: S01_BaseRing S02_CauchyComplete S12_B5RecycleSF S13_NLiveAudit（-Q *)
(*        预编译树只读引用；QId/qid_intro 经 S12 直 Require 入域；LCAudit *)
(*        Module 包壳非自动导出，本件显式 Import）；Stdlib（QArith/List/Arith/ *)
(*        Lia/Extraction 出口舱）。 *)
(*  对标: 审计承载扩容系列 v4/v5 同口径直审件；S13 自靠面五主定理。 *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 承载: 合取全 S01.And、析取全 S01.Or、 *)
(*        等同全 S01.Id、比较结论面全 QleT'/QId（Set 型）；上游 top-p 主定理出 *)
(*        口前提位 Qle（stdlib Prop 原子谓词）沿前提位判例保留，证明体经 Qle_ *)
(*        bool 判定面反射供给后由 qle_to_qleT 桥升 Set 型出口；无 exists/Prop *)
(*        连词、无否定形书写；证明体全 exact/apply/id_refl 显式项直交。 *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s *)
(*        65532 && nice -19 rocq c -native-compiler no -Q vo_local_world_ *)
(*        unified_0930 "" abl_audit_base_v6.v（独占池）。 *)
(*  核实注: S13 五主定理出口签名以 repl Check 实拍为准；语句面逐条实拍皆非空壳（燃料账真析取/ *)
(*        结论具体比较/归纳证非平凡/守恒等式 field 闭合）；abf_ 前缀全树 grep 零命中。 *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
Local Open Scope Q_scope.
Import S13_NLiveAudit.LCAudit.

(* ============================================================ *)
(* §0 内部管件舱（常量生成器与具体对象，非承载语句）                 *)
(* ============================================================ *)

(* 常量抽取器：每次发放同一序列 [t] 并原样回传种子流（PRNG 流无关面）。 *)
Definition abf_const_draw (t : nat) : PRNG -> Sequence * PRNG :=
  fun p => (t :: nil, p).

(* 均匀权重：每 token 权 1（top-p 具体实例用）。 *)
Definition abf_uniform_w (t : nat) : Q := 1%Q.

(* 种子光线：位置原点、切线向 (1,0)、权 4、无历史比特、零累计偏转。 *)
Definition abf_seed_ray : QRay :=
  Build_QRay 0 0 1 0 4 nil 0.

(* ============================================================ *)
(* §1 承载一·序贯置信停止（甲）：燃料账主定理具体实例＋早停计算面     *)
(*    （Set 层 Id 翼×2，And 并载，双重使用）                           *)
(* ============================================================ *)

Theorem abf_early_stop_fuel_and_run :
  forall prng0 : PRNG,
    And (Id (orb (stop_condition 1
                   (fst (sample_until_confident 1 5%nat ((0%nat :: nil) :: nil)
                          (abf_const_draw 0) prng0)))
                (Nat.eqb (length (fst (sample_until_confident 1 5%nat
                              ((0%nat :: nil) :: nil) (abf_const_draw 0) prng0)))
                         (length ((0%nat :: nil) :: nil) + 5)%nat))
           true)
        (Id (fst (sample_until_confident 1 5%nat ((0%nat :: nil) :: nil)
                   (abf_const_draw 0) prng0))
            ((0%nat :: nil) :: nil)).
Proof.
  intros prng0. split.
  - (* 燃料账翼：主定理 threshold:=1、max_iter:=5、acc:=[[0]] 具体实例化 *)
    (* （真行使——let 包络经转换展开严合）。                          *)
    exact (early_stop_confidence 1 5%nat ((0%nat :: nil) :: nil)
             (abf_const_draw 0) prng0).
  - (* 早停计算面：唯一候选 [0] 自洽分 1≥1，停止条件计算为真，           *)
    (* 采样零步消解，结果恒 [[0]] 与种子流无关（id_refl 定义性计算）。    *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* §2 承载二·序贯置信停止（乙）：早停合格主定理具体实例——             *)
(*    停止即全员过线（结论 QleT' Set 型比较面）                        *)
(* ============================================================ *)

Theorem abf_early_stop_all_pass_concrete :
  forall prng0 : PRNG,
    And (Id (stop_condition 1 ((0%nat :: nil) :: nil)) true)
        (QleT' 1 (self_consistency_score (0%nat :: nil) ((0%nat :: nil) :: nil))).
Proof.
  intros prng0. split.
  - (* 停止条件计算实拍：forallb 全员 Qle_bool 1 1＝true。 *)
    exact id_refl.
  - (* 合格面：早停合格主定理 max_iter:=0 具体实例化，Hstop 槽喂第一翼，  *)
    (* InT 槽先约化采样零步消解形再落表头见证（真行使）。             *)
    apply (early_stop_confidence' 1 0%nat ((0%nat :: nil) :: nil)
             (abf_const_draw 0) prng0 id_refl (0%nat :: nil)).
    cbn [sample_until_confident fst]. apply InT_here.
Qed.

(* ============================================================ *)
(* §3 承载三·top-p 截断：累计主定理具体实例——截断前缀计算实拍＋        *)
(*    质量下界面（结论经 qle_to_qleT 桥升 QleT' Set 型，三使用点）      *)
(* ============================================================ *)

Theorem abf_top_p_cumulative_concrete :
  And (Id (top_p_prefix 1 (0%nat :: 1%nat :: nil) abf_uniform_w)
          (0%nat :: nil))
      (QleT' 1 (qsum_w abf_uniform_w
                 (top_p_prefix 1 (0%nat :: 1%nat :: nil) abf_uniform_w))).
Proof.
  split.
  - (* 截断计算实拍：p=1>0 不空转；w 0=1 封顶命中 → 前缀恰 [0]。 *)
    exact id_refl.
  - (* 质量下界面：累计主定理 p:=1、sorted:=[0;1]、均匀权具体实例化；      *)
    (* 前提 Qle 1 (1+(1+0)) 经 Qle_bool 判定面反射供给（前提位判例合规）， *)
    (* 结论 Qle 经 qle_to_qleT 桥升 Set 型出口（真行使）。             *)
    apply qle_to_qleT.
    apply (top_p_cumulative_ge 1 (0%nat :: 1%nat :: nil) abf_uniform_w).
    apply (proj1 (Qle_bool_iff 1 (qsum_w abf_uniform_w (0%nat :: 1%nat :: nil)))).
    exact eq_refl.
Qed.

(* ============================================================ *)
(* §4 承载四·PRNG 系随机游走：分支权重守恒主定理一般形直引＋           *)
(*    具体实例（种子光线权 4 对半分两子光线 2+2=4）双重使用              *)
(* ============================================================ *)

Theorem abf_q_branch_weight_conserved :
  And (forall (phi : Q) (r : QRay),
         QId (rw (fst (q_branch phi r)) + rw (snd (q_branch phi r))) (rw r))
      (QId (rw (fst (q_branch 1 abf_seed_ray))
            + rw (snd (q_branch 1 abf_seed_ray)))
           4%Q).
Proof.
  split.
  - (* 一般形：主定理逐字直引（跨件直审本翼）。 *)
    intros phi r. exact (q_branch_weight phi r).
  - (* 具体实例：rw 子光线各 4/2，QId 经 qid_intro 入 field 闭合。 *)
    cbn [abf_seed_ray q_branch rw fst snd].
    apply qid_intro. field.
Qed.

(* ============================================================ *)
(* §5 承载五·审计重采样兜底：主定理 default_seq:=[0] 部分实例化        *)
(*    （S01.Or:=A+B Set 层析取直出）＋兜底计算面双重使用                 *)
(* ============================================================ *)

Theorem abf_resample_fallback :
  And (forall (post_aud : PostAud) (g : nat -> Sequence) (attempts : nat),
         Or (Id (post_aud (resample_attempt (0%nat :: nil) post_aud g attempts))
                true)
            (Id (resample_attempt (0%nat :: nil) post_aud g attempts)
                (0%nat :: nil)))
      (Id (resample_attempt (0%nat :: nil) (fun _ => false) (fun _ => (1%nat :: nil)) 2%nat)
          (0%nat :: nil)).
Proof.
  split.
  - (* 一般形：兜底主定理消解首参 default_seq 就位 [0]（真行使）。 *)
    intros post_aud g attempts.
    exact (resample_terminates (0%nat :: nil) post_aud g attempts).
  - (* 具体实例：审计恒拒、生成恒 [1]、两次尝试后兜底回 [0]（计算实拍）。 *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* §6 尾舱·假设审计（S13 自靠面五主定理跨件直审＋本件五承载自审）      *)
(*    判读判据：十一条全输出 Closed under the global context。         *)
(*    前 6 条＝S13 审计引擎可靠性面主定理族的跨件追审（含 qle_to_qleT   *)
(*    桥——承载③第三使用点；自靠面此前全树 PA 直审缺位，Z 裸奔 Top 本体）； *)
(*    后 5 条＝本件五承载自审。                                        *)
(*    注：Require 闭包含 S01-S12 全链，coqchk 环境公理面沿 CT1B 判例    *)
(*    与逐定理 PA 定检分账，非本件引入。                                *)
(* ============================================================ *)

Print Assumptions S13_NLiveAudit.LCAudit.early_stop_confidence.
Print Assumptions S13_NLiveAudit.LCAudit.early_stop_confidence'.
Print Assumptions S13_NLiveAudit.LCAudit.top_p_cumulative_ge.
Print Assumptions S13_NLiveAudit.LCAudit.resample_terminates.
Print Assumptions S13_NLiveAudit.q_branch_weight.
Print Assumptions S13_NLiveAudit.LCAudit.qle_to_qleT.
Print Assumptions abf_early_stop_fuel_and_run.
Print Assumptions abf_early_stop_all_pass_concrete.
Print Assumptions abf_top_p_cumulative_concrete.
Print Assumptions abf_q_branch_weight_conserved.
Print Assumptions abf_resample_fallback.

(* ============================================================ *)
(* §7 出口舱：承载兼任提取端口（G3：提取面零魔数）                     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abf_early_stop_fuel_and_run
  abf_early_stop_all_pass_concrete abf_top_p_cumulative_concrete
  abf_q_branch_weight_conserved abf_resample_fallback.
