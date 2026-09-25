(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabd2_do_ltle_iffdec_real（原 L121，2 句玩具证）                     *)
(*   uabd2_ri_reqface_abs_ge_zero_id（原 L108，1 句玩具证）               *)
(*   uabd2_ri_real_abs_ge_zero_id（原 L98，1 句玩具证）                   *)
(*   uabd2_ali_abs_ge_zero_id_explicit（原 L79，2 句玩具证）              *)
(*   uabd2_ali_abs_ge_zero_id_pair（原 L66，2 句玩具证）                  *)
(* ============================================================ *)

(* ============================================================ *)
(* （FA-D2 唯一施工项：AbsLeId 两 Context 槽 N3 实例供给）         *)
(*                                                               *)
(*   AbsLeId.v（P7）Section AbsLeIdAbstract（L43-81）两接口槽：    *)
(*     L45 Context {RI : RealInterfaceEnhanced}（接口束槽）        *)
(*     L47 Context {DO : DecidableOrder RI}（可判定序扩展槽，      *)
(*          类本体 S01_BaseRing:329 五字段全 Set 层）             *)
(*   槽语句主件 ali_abs_ge_zero_id（AbsLeId.v:50，被 AMT:103/     *)
(*   MixSel:770 等依存），本体证明 fa53:141 直接代入零循环。           *)
(*                                                               *)
(* 交付三面（逐位对普查表）：                                      *)
(*  ①RI 槽（N1，库内实例化消解件直接代入）：具体 Real 载体字段映照          *)
(*    （le 映 real_le / zero 映 real_zero / abs 映 real_abs /      *)
(*    Id 映 real_eq）下，槽语句的载体形即 AbsLeId.v:91            *)
(*    ali_real_abs_ge_zero_id（在库自证）——本件逐字引用两形：      *)
(*    real 面一件 + RealEnhancedReal（S07:8566）实例投影 req 面    *)
(*    一件（两语句经实例字段展开可转换同体，同母本闭合）。          *)
(*    注：全树 Real 载体上无 Id 面接口束具体实例（唯 req 面一件）  *)
(*    ——按 FA-D1S1 载体分层供给形登记，零重证。                   *)
(*  ②DO 槽（N3，出节全参供给对）：ali_abs_ge_zero_id 语句          *)
(*    （AbsLeId.v:50 逐字）复现两形：                              *)
(*    (a) 节内副本形（AbsLeId L43-54 同款语境，出节 RI0/DO0 消为    *)
(*        实例隐式参——与 AbsLeId 自身出节形同款，Check 实证）；     *)
(*    (b) 显式全参形（T2b 节7 同款）：RI0/DO0/a 顶层 forall 显式    *)
(*        全参，母本 fa53_abs_ge_zero_id_dec（fa53:141）exact       *)
(*        直接代入——任意 (RI0,DO0) 对喂即得。                          *)
(*  ③DO 槽具体层（诚实分账）：                                    *)
(*    - 可构造面：字段5（lt_le_iff_dec 载体形）一件，T 档显式       *)
(*      登记（real_le 于 S02:469 定义性展开即同款 Or，exact 闭合，  *)
(*      防注水口径：不计非平凡战果）；                             *)
(*    - 墙登记（可判定序三分/非退化判定族，不发全实例件）：         *)
(*      字段1 ord_le_dec / 字段2 lt_dec / 字段3 eq_dec /           *)
(*      字段4 not_le_lt 在柯西载体的可判定化属 LPO/Markov 族——     *)
(*      E225 判定（G09_MiscSmall:566「可判定序=整体三分律=LPO      *)
(*      等价、全库零实例」）+ S01 序三分律注记（构造性模型不可      *)
(*      满足）+ AA15R SqWall 与 rLPO 等价判例。全树实例构造        *)
(*      两处投影解构形）。邻接 N 坐标：fa53:141（抽象面供给）/      *)
(*      AbsLeId.v:91（具体面供给）。定理化路线遗留：DO 类参数       *)
(*      需 Id 面接口实例，全树该实例亦为零，墙语句面无法库内        *)
(*      内化——登记不施工（FA3 墙件处置三要素齐备）。               *)
(*                                                               *)
(* 依赖（只读依存零改）：S01_BaseRing / fa53_compat_abs /          *)
(*   S02_CauchyComplete / S03_QExp / S07_RealSetoidExpLog /        *)
(*   AbsLeId（N1 母本所在，仅引用 ali_real_abs_ge_zero_id）。       *)
(* 纪律：语句面全 Set 层（Or/Not/Id 均为 S01:67-70 Set 层定义）；   *)
(*   公理面零新增；无禁用收尾词；前缀 uabd2_ 全库防撞已 grep 核    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ ② DO 槽：出节全参供给对（N3，fa53:141 直接代入） ====== *)
(* 与 AbsLeId L43-54 同款语境（RI_base 实例解析投影裸名）；出节后  *)
(* RI0/DO0 消为显式头参（全参形，节后 Check 实证）。               *)
Section UabD2PairWorld.

Context {RI0 : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO0 : DecidableOrder RI0}.

(* 槽语句逐字（AbsLeId.v:50）：主件 ali_abs_ge_zero_id 复现形 *)
Theorem uabd2_ali_abs_ge_zero_id_pair :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

End UabD2PairWorld.

(* 出节形实证（FA3 纪律6：节参消失不对称 Check 实证） *)
Check uabd2_ali_abs_ge_zero_id_pair.

(* —— 出节显式全参形（T2b 节7 同款；检验 t1 形逐字，fa53:141 直接代入） —— *)
Theorem uabd2_ali_abs_ge_zero_id_explicit :
  forall (RI1 : RealInterfaceEnhanced) (DO1 : DecidableOrder RI1)
         (a : @S01_BaseRing.R RI1),
    @S01_BaseRing.le RI1 (@S01_BaseRing.zero RI1) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI1) (@S01_BaseRing.abs RI1 a) a.
Proof.
  intros RI1 DO1 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI1 DO1 a Ha).
Qed.

(* ============ ① RI 槽：具体 Real 载体直接匹配（N1，双形） =========== *)
(* 具体层 Require 置于抽象节后（AbsLeId L86 遮蔽注记同款）。       *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import AbsLeId.

(* real 面：槽语句字段映照载体形=N1 母本 ali_real_abs_ge_zero_id   *)
(* （AbsLeId.v:91，在库自证）逐字引用。                            *)
Theorem uabd2_ri_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* req 面：RealEnhancedReal（S07:8566）实例投影形——投影常量居于     *)
(* S07_RealSetoidExpLog.RealInterfaceEnhancedMod 模块（Locate 实证， *)
(* T2b 节7 前缀同款）；le/zero/abs/req 四字段展开与 real_* 面       *)
(* delta/iota 可转换同体，同母本闭合。                              *)
Theorem uabd2_ri_reqface_abs_ge_zero_id :
  forall a : Real,
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal) a ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.abs Real RealInterfaceEnhancedMod.RealEnhancedReal a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* ============ ③ DO 槽具体层：可构造面（字段5，T 档） ============ *)
(* 字段5 载体形：real_le（S02:469）定义性展开即同款 Set 层 Or——    *)
(* 透明展开一行闭合，T 档显式登记（防注水口径，不计非平凡战果）。   *)
Theorem uabd2_do_ltle_iffdec_real :
  forall a b : Real,
    S01_BaseRing.Or (real_lt a b) (real_eq a b) -> real_le a b.
Proof.
  intros a b H.
  exact H.
Qed.

(* ---- 字段1-4 墙登记见文件头注（三分/非退化判定族，不发全实例件） ---- *)

(* ============ PA 自审段（G2 前置：逐件 Closed 判读） ============ *)
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_do_ltle_iffdec_real.

Print Assumptions uabd2_do_ltle_iffdec_real.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
