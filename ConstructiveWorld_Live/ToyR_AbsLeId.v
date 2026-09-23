(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ali_abs_id_mult_r（原 L75，2 句玩具证）                              *)
(*   ali_abs_id_mult_l（原 L67，2 句玩具证）                              *)
(*   ali_abs_ge_zero_id_sym（原 L57，2 句玩具证）                         *)
(*   ali_abs_ge_zero_id（原 L50，2 句玩具证）                             *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T317 恒等守恒更正注记】2026-09-21 包AV六 台账席（头注更正试点件） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，   *)
(* 经 T277（包AL）全量恒等核查已证结论、T287（包AV）抽验复核：本件实测   *)
(* 为恒等守恒——清单所列 4 槽证明体与 Main 现版原件逐字同文（刀体  *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。          *)
(* 更正口径：真替换 0 槽＋恒等守恒 4 槽；本注记为追加块，上方原头  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面   *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册。         *)
(* 附记：T277 人工逐行比对锚件  *)
(* ============================================================ *)

(* ============================================================ *)
(* AbsLeId.v — T40 消融50 席位CYB6（批次 E-STAGING-CYB6）真缺口施工件 *)
(*                                                               *)
(* 使命：VB 核验（T40-VB-核验.md:33）留下的真缺口——              *)
(*   S06_DiffSamplingGibbs.v:4035（Live 树）                      *)
(*     Variable abs_ge_zero_id_cc : forall a, le zero a -> Id (abs a) a *)
(*   （Section AttentionGibbsBridge :3186 内，Let 别名展开后      *)
(*   = forall a : @R (@RI_base RI), @le (@RI_base RI) ...）。      *)
(*   VB 结论：文件自带"诚实缺口"注记，接口 abs_pos（S01:293）仅   *)
(*   lt 版，le→(lt∨eq) 无 tightness 桥；"后续 C 候选"。本席兑现。  *)
(*                                                               *)
(* 侦查对照（防重复施工）：                                       *)
(*   fa53_compat_abs.v 件3 fa53_abs_ge_zero_id_dec（VC 席）——     *)
(*   语句面与本槽同形（le zero a -> Id (abs a) a），前提是可选    *)
(*   扩展类 DecidableOrder（S01:329，Set 层 Or 三分）。抽象层      *)
(*   主件按 A 类核验引用依存（只 Require 不改）；本件另交付：      *)
(*   (a) 反向形 ali_abs_ge_zero_id_sym（id_sym 运河）；            *)
(*   (b) S06 两个依存位封装形 ali_abs_id_mult_l/r                  *)
(*       （S06:4371 id_cong (fun x => mult (abs q) x) (...) 与     *)
(*         S06:4447 id_cong (fun x => mult x (abs b)) (...)        *)
(*       的直接匹配件，免下游再拼 id_cong）；                          *)
(*   (c) 具体 Real 层兑现 ali_real_abs_ge_zero_id——VB 核验给      *)
(*       路径（real_abs_pos_req + real_abs_zero_req + real_le 的   *)
(*       Or 编码 S02:469）本席首次施工：lt 支走 real_abs_pos_req   *)
(*       （S07:7289），eq 支走 real_eq_abs_compat（S07:410，       *)
(*       Module RealSetoid 内须限定）+ real_abs_zero_req           *)
(*       （S07:7266）+ real_eq_sym/trans 三步链。库内此前无        *)
(*       le 版真引理（VB 核验原话），此件补上。                    *)
(*                                                               *)
(* 纪律：语句面全 Set 层（Or/Not 用 S01:67-68 Set 层定义，        *)
(*   real_lt 为 sigT 见证 S02:465）；零 Prop 泄露；               *)
(*   无 公理/承认件/参数/猜想/弃证；               *)
(*   fa53_compat_abs 只 Require 依存零改；原树零改。              *)
(*   前缀 ali_ 全库防撞已 grep 核（消融50 内零命中）。             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ 第一层：抽象接口层（S06:4035 槽语句形） ============ *)
(* 与 fa53 同款上下文（RI_base :> RealInterface 子类投影 +        *)
(* Existing Instance 解析裸名；DO 为可选可判定序扩展类）。          *)
Section AbsLeIdAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---- 主件：abs_ge_zero_id_cc 槽语句同形（A 类核验引用 fa53 件3） ---- *)
Theorem ali_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

(* ---- 反向形：le zero a -> a == |a|（rewrite 另一向所需） ---- *)
Theorem ali_abs_ge_zero_id_sym : forall a : R, le zero a -> Id a (abs a).
Proof.
  intros a Ha.
  exact (id_sym (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 依存位封装形（左乘位）：S06:4371 直接匹配 ----
   该处原文 id_cong (fun x => mult (abs (f s)) x)
                    (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))
   ——本件把 id_cong 拼好，下游一步喂。 *)
Theorem ali_abs_id_mult_l : forall a b : R, le zero a -> Id (mult (abs a) b) (mult a b).
Proof.
  intros a b Ha.
  exact (id_cong (fun w => mult w b) (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 依存位封装形（右乘位）：S06:4447 直接匹配 ---- *)
Theorem ali_abs_id_mult_r : forall a b : R, le zero b -> Id (mult a (abs b)) (mult a b).
Proof.
  intros a b Hb.
  exact (id_cong (fun w => mult a w) (ali_abs_ge_zero_id b Hb)).
Qed.

End AbsLeIdAbstract.

(* ============ 第二层：具体 Real 层兑现（VB 给路径，本席施工） ============ *)
(* 柯西实数层（S02 Real := sigT (fun u : Qseq => cauchy u)）：     *)
(* real_le = Or real_lt real_eq（S02:469，Set 层 Or）两支分决。    *)
(* 注意此处 Require 置于抽象节之后，避免具体层名遮蔽接口投影名。    *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

Theorem ali_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a：严格版逐点件直给（S07:7289） *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a：|a| ≈ |0| ≈ 0 ≈ a（compat + zero_req + sym 链） *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- G1 内嵌自检段（文件内显式 PA 声明，min-pa≥1） ---- *)
Print Assumptions ali_abs_ge_zero_id.
Print Assumptions ali_abs_ge_zero_id_sym.
Print Assumptions ali_abs_id_mult_l.
Print Assumptions ali_abs_id_mult_r.
Print Assumptions ali_real_abs_ge_zero_id.
