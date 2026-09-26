(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ===================================================================== *)
(* r_max 左右参 plain 形对称交换桥 + rpl_clip_lower 回喂特化                  *)
(*                                                                       *)
(* 争议坐标（经验卡 E384）：                                              *)
(*   · UpReqRDF.v ReqDiffPlain 类 r_max_ge_plain : le a (r_max a b)        *)
(*     （左参 plain 槽，<- Id r_max_le_l 同构，T2① 零证明槽）；              *)
(*   · UpReqPPOPlain.v 节1 自持槽 r_max_le_r_plain : le b (r_max a b)      *)
(*     （右参 plain 槽，<- Id r_max_le_r 同构）。                           *)
(*   根因：req 层接口 RealInterfaceEnhancedSetoid 的 r_max le 方向仅有      *)
(*   逐 eps 形（r_max_le_l/_r : le _ (plus (r_max a b) eps)），plain 形     *)
(*   无接口支撑（「序无消去」，UpReqAlign3 裁定结论同因）；两槽单向重复占位，     *)
(*   库内无对称交换桥（E384 卡登记缺口）。                                  *)
(* 本件：                                                                  *)
(*   1. 交换槽 rms_r_max_comm（T2① 显式参非公理，实例化一次全桥解锁）；      *)
(*   2. 双向桥 rms_le_r_of_ge / rms_ge_of_le_r（req_le_compat 运输，        *)
(*      非平凡组合逻辑真证：任一侧 plain 槽 + 交换 ⟹ 另一侧 plain 形，       *)
(*      双槽占位可归一为「一侧槽 + 本桥」）；                                *)
(*   3. 复合回归件 rms_ge_roundtrip（桥系无漂移自检）；                      *)
(*   4. 回喂件 rms_rpl_clip_lower：结论与 UpReqPPOPlain.v rpl_clip_lower    *)
(*      逐字同形（minus 位 req_minus δ 透明随 rms_clip 语句面），槽源换为    *)
(*      RDP 左参槽 + 桥 B——自持右参槽 r_max_le_r_plain 消解。               *)
(* 纪律：纯构造性；Set 层语句零 Prop 泄露（req/le 均 Set 值）；纯项模式      *)
(*   （组合器逐段直引，零 Ltac 重写层）；假设位 = T2① 显式参非公理；         *)
(*   全链可提取。                                                          *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

Section RMaxSwap.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {RDP : ReqDiffPlain R}.
Variable epsilon : R.

(* ---- T2① 对称交换槽（E384 卡缺口位；显式参非公理） ----
   实例化来源注记：plain 形 req (r_max a b) (r_max b a) 在抽象接口层
   具体模型侧若提供 r_max 交换见证（逐坐标 Qmax 对称），本节全桥一次解锁。 *)
Hypothesis rms_r_max_comm : forall a b : R, req (r_max a b) (r_max b a).

(* ---- 桥 B（回喂方向）：左参 plain 槽 ⟹ 右参 plain 形 ----
   le b (r_max b a)（左参槽实例 Hge b a）经 req 运输 y 腿（交换）得
   le b (r_max a b)。 *)
Lemma rms_le_r_of_ge :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le b (r_max a b).
Proof.
  intros Hge a b.
  exact (req_le_compat b b (r_max b a) (r_max a b)
                        (req_refl b) (rms_r_max_comm b a) (Hge b a)).
Qed.

(* ---- 桥 A（消槽方向）：右参 plain 槽 ⟹ 左参 plain 形 ----
   le a (r_max b a)（右参槽实例 Hler b a）经同一运输得 le a (r_max a b)。 *)
Lemma rms_ge_of_le_r :
  forall (Hler : forall a b : R, le b (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hler a b.
  exact (req_le_compat a a (r_max b a) (r_max a b)
                        (req_refl a) (rms_r_max_comm b a) (Hler b a)).
Qed.

(* ---- 复合回归件：桥 A ∘ 桥 B 还原左参槽自身（桥系无漂移自检） ---- *)
Lemma rms_ge_roundtrip :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hge a b.
  exact (rms_ge_of_le_r (rms_le_r_of_ge Hge) a b).
Qed.

(* ---- Id ppo_clip L19506 / UpReqPPOPlain rpl_clip 同形定义 ----
   （minus 位 req_minus δ 透明 plus a (opp b)，语句面随之） *)
Definition rms_clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).

(* ---- rpl_clip_lower 回喂特化 ----
   结论与 UpReqPPOPlain.v rpl_clip_lower（Id L19518 req 同位）逐字同形；
   槽源 = RDP 左参槽（r_max_ge_plain）+ 桥 B，自持右参槽零需求。 *)
Lemma rms_rpl_clip_lower :
  forall r : R, le (req_minus one epsilon) (rms_clip r).
Proof.
  intro r. unfold rms_clip.
  exact (rms_le_r_of_ge (@r_max_ge_plain R _ RDP)
                        (min r (plus one epsilon)) (req_minus one epsilon)).
Qed.

End RMaxSwap.

Print Assumptions rms_rpl_clip_lower.
