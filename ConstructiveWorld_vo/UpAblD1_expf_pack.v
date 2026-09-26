(* ============================================================ *)
(* UpAblD1_expf_pack.v —— FA-D1 批 D1-② expf 五字段打包批             *)
(*   UpReqAttnMixTime expf 迷你接口六槽·打包放电逐槽引用形              *)
(*                                                              *)
(* 辖区（FA-D1 普查报告 attn/_tfad1_普查报告-20260919.md §④ D1-② 批，  *)
(*   UpReqAttnMixTime.v L94-99 六槽，现档 Live_X 逐字实测 2026-09-19）： *)
(*   槽1 L94  expf         : R -> R                                   *)
(*   槽2 L95  expf_pos     : forall x : R, lt zero (expf x)           *)
(*   槽3 L96  expf_zero    : Id (expf zero) one                       *)
(*   槽4 L97  expf_plus    : forall a b : R,                          *)
(*                             Id (expf (plus a b)) (mult (expf a) (expf b)) *)
(*   槽5 L98  expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b) *)
(*   槽6 L99  expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b) *)
(*                                                              *)
(* 放电母本（FA-D1 普查 §第0步.4 实测坐标，现档直取）：                 *)
(*   real_expf_realizable @ AttnDoeblin.v:758——expf 五字段一次性 sigT   *)
(*   打包件（pos/zero/plus/mono_lt/mono_le；P1:990 §9.1.1 先例）。      *)
(*   本件逐槽投影拆包：载体槽取签名投影（projT1），五字段槽取打包件      *)
(*   字段束投影（projT2 一次性分解→proj1/proj2 逐槽引用），零重证零注水。 *)
(*                                                              *)
(* 防双席先查（2026-09-19 实测）：全树 grep「Require Import             *)
(*   UpReqAttnMixTime」零命中——本件六槽全树首供，无既有放电件；          *)
(*   Live_X 无 UpAblP3S1_*/UpAblD1_* 重复立件。                         *)
(*                                                              *)
(* 载体分层（诚实降级登记，T2b §五.5 同款）：原槽世界为 RI/Id 面        *)
(*   （Section BoundedSoftmaxMixTime，Context {RI : RealInterfaceEnhanced}）； *)
(*   全树无 Real 载体上的 RealInterfaceEnhanced 具体实例（grep 实测      *)
(*   2026-09-19，仅 TempSoftmaxInstantiation.tsi_rie_setoid 一处         *)
(*   Build_RealInterfaceEnhancedSetoid 为 req 面），抽象 RI 上五字段     *)
(*   不可 discharge；本件按载体实例供给形在典范 Real 载体 req 面放电：   *)
(*   Instance RealEnhancedReal@S07_RealSetoidExpLog:8566 字段映照        *)
(*   lt:=real_lt / le:=real_le / req:=real_eq / zero:=real_zero /        *)
(*   one:=real_one / plus:=real_plus / mult:=real_mult——槽语句经字段     *)
(*   映照与本件 real_* 语句形可转换同体（req 面整体放电先例＝            *)
(*   cmk_expf_realizable@UpReqConcMixSel:921 exact 直喂；本件为其        *)
(*   逐槽拆包引用形，槽位消费面键定 UpReqAttnMixTime 六槽）。             *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、AttnDoeblin。 *)
(* 纪律：零新增疑设面；前缀 uabd1x_（全树 grep 零撞名 2026-09-19 实测）； *)
(*   文尾逐件 Print Assumptions 收尾。                                  *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblD1S1_expf_pack.*           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.

(* ---- 槽1（L94 expf : R -> R）：打包件签名投影＝载体函数槽的居住形 ---- *)
Definition uabd1x_expf : Real -> Real := projT1 real_expf_realizable.

(* ---- 打包件字段束一次性分解（五字段具名，逐槽引用公用） ---- *)
Lemma uabd1x_pack_fields :
  And (forall x : Real, real_lt real_zero (uabd1x_expf x))
    (And (real_eq (uabd1x_expf real_zero) real_one)
    (And (forall a b : Real,
          real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)))
    (And (forall a b : Real, real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b))
         (forall a b : Real, real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b))))).
Proof.
  unfold uabd1x_expf.
  exact (projT2 real_expf_realizable).
Qed.

(* 坑卡注记（F 探针门实测 2026-09-19）：Set 面 And（S01:66 定义 = A * B，    *)
(*   即 Stdlib prod）的投影是 fst/snd；proj1/proj2 在本树属 Prop 面 and 投影  *)
(*   ——面-面不可混（AT7 卡③同款教训），逐槽引用一律 fst/snd。               *)

(* ---- 槽2（L95 expf_pos）逐字引用形 ---- *)
Theorem uabd1x_expf_pos : forall x : Real, real_lt real_zero (uabd1x_expf x).
Proof. intros x. exact (fst uabd1x_pack_fields x). Qed.

(* ---- 槽3（L96 expf_zero；Id 面槽在典范载体 req 幺等下取 req 形）逐字引用形 ---- *)
Theorem uabd1x_expf_zero : real_eq (uabd1x_expf real_zero) real_one.
Proof. exact (fst (snd uabd1x_pack_fields)). Qed.

(* ---- 槽4（L97 expf_plus）逐字引用形 ---- *)
Theorem uabd1x_expf_plus : forall a b : Real,
  real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)).
Proof. exact (fst (snd (snd uabd1x_pack_fields))). Qed.

(* ---- 槽5（L98 expf_mono_lt）逐字引用形 ---- *)
Theorem uabd1x_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (fst (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ---- 槽6（L99 expf_mono_le；Or 拆支已在母本装箱体内逐支消解—— *)
(*      inl→cauchy_real_exp_mono / inr→cauchy_real_exp_wd，本件整槽引用 ---- *)
Theorem uabd1x_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (snd (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabd1x_expf.
Print Assumptions uabd1x_pack_fields.
Print Assumptions uabd1x_expf_pos.
Print Assumptions uabd1x_expf_zero.
Print Assumptions uabd1x_expf_plus.
Print Assumptions uabd1x_expf_mono_lt.
Print Assumptions uabd1x_expf_mono_le.
