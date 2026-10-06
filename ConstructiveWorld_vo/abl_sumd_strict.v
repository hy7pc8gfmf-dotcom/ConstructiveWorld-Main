(* ============================================================ *)
(* abl_sumd_strict.v —— UpReqSumD 泛型严格和单调（正性前提形）独立闭合件     *)
(*                                                                          *)
(* 【件名】abl_sumd_strict.v（甲形态·新独立件·零级联：不改宿主、              *)
(*   零 Require 面变化、零注册面级联；照 AN 件 A2 同款先例）。              *)
(*  使命: 闭合 RC-1 泛型严格和单调的降档换形案（AG 开工包三·正性前提形）： *)
(*   非空列表 + 逐点严格正性 + 逐点严格 f<g ⟹ 和 f < 和 g。                  *)
(*   C 原草案（逐点 lt+非空、无正性前提）核验落 RW-MIX 混合保序墙          *)
(*   （UpReqAlgebra.v ReqStrictOrderBridge 节禁硬证登记位），禁做原形；       *)
(*   本件按主会话裁决只做换形案。                                            *)
(*   语句前缀 dsu_：全库 grep（ConstructiveWorld_Live +                      *)
(*   vo_local_world_unified_0930）0 命中（实拍防撞）。               *)
(*  依赖: UpReqSumD（sumd_list_sum／sumd_sumf 有限和机器，零宿主改动）；     *)
(*   S07_RealSetoidExpLog（RealInterfaceEnhancedMod：Set 值序字段            *)
(*   lt_plus_compat 双严格加法保序／req_lt_compat 严格换形／plus_zero）。     *)
(*  构造性: 零承认语句、零经典逻辑、零未证前提位；语句面纯 Set           *)
(*   （lt/le 均 RealInterfaceEnhancedSetoid 的 Set 值谓词，SumD 头注 :56     *)
(*   同一口径）；唯一否定位=非空前提（UpReqSampling 签名变化 7 同形同阶      *)
(*   在档先例：sumd_list_sum_pos:322／sumd_sum_pos:331，不放大主张）。       *)
(*   证明体零触碰 RW-MIX 墙形：严格性仅经双严格字段 lt_plus_compat 装配       *)
(*   （两肢皆逐点严格 lt），基例 plus_zero 换形走 req_lt_compat（req 换形     *)
(*   非「严格从弱」产生子）；全程未用/未假设任何混合形产生子（接口层与        *)
(*   具体层的混合补两项在本件源文中零出现）。正性前提按裁决形态保留于        *)
(*   两语句面（正性前提形标记；诚实边界：在逐点严格前提下对该结论为冗余      *)
(*   前提，承载位注记见 attn AQ 报告）。                                     *)
(*  编译配方: 池内 rocq c 直编（绿判 EXIT=0｜无 Error｜魔数 436f712100015ff4）│ *)
(*   尾 Print Assumptions 全 Closed。                                        *)
(* ============================================================ *)

Require Import UpReqSumD.
(* RealInterfaceEnhancedSetoid 类与 RealInterfaceEnhancedMod 定义于
   S07（S07_RealSetoidExpLog.v:7934-8698 实拍）；透传 Require 不再导出
   短名，本件自 Import（首版红于 Cannot find module，核验补面）。 *)
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* 工具链适配（fail-loud 核验）：本 Rocq 9.1.0 安装 Corelib.Init.Logic
   无 Not（Locate 实证 "No object of basename Not"，沙箱裸探实证），
   而非空前提 datum 需否定词；按 Not 原定义（P -> False）件内自持，
   语句 datum 形与宿主 sumd_sum_pos:331（Not (enum = nil) 位）保持同形。
   dsu_ 前缀防撞（全库 grep=0）。 *)
Definition dsu_neg (P : Prop) : Prop := P -> False.

(* ============================================================ *)
(* Section DsuStrictSum：泛型严格和单调（正性前提形）                          *)
(*   Context/Variables 与宿主 UpReqSumD Section SumDischarge 同形对应          *)
(*   （G12_ZPosFam 使用者先例同款），和机器直引宿主 sumd_list_sum／            *)
(*   sumd_sumf（有限和定义面零重写）。                                        *)
(* ============================================================ *)
Section DsuStrictSum.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable enum : list S.

(* ============ 主件 1：cons 形（列表头 witness 泛型严格和单调） ============ *)
(* f 逐点严格正（正性前提形前提，裁决形态保留）+ f<g 逐点严格
   ⟹ 头和严格增。证明：对尾段 l 结构归纳——基例尾和为零，
   plus_zero 换形走 req_lt_compat（req 换形，零墙接触）；
   归纳步头项严格腿 + 尾段同头 IH 双严格 lt_plus_compat 装配。
   泛型无正性前提形（弱+一处严格）落 RW-MIX 混合保序墙
   （UpReqAlgebra ReqStrictOrderBridge 禁硬证登记），去向待裁，不在此碰。 *)
Lemma dsu_list_sum_lt_cons : forall (f g : S -> R) (x : S) (l : list S),
  (forall s : S, lt zero (f s)) ->
  (forall s : S, lt (f s) (g s)) ->
  lt (sumd_list_sum S f (x :: l)) (sumd_list_sum S g (x :: l)).
Proof.
  intros f g x l Hfp Hlt. revert x.
  induction l as [| y t IH]; intro x.
  - (* 基例 l=nil：sumd_list_sum 归约至 plus _ zero，plus_zero 换形收一。
       核验纠正（首版红于方向倒置）：req_lt_compat 换形向为
       req x1 x2 -> req y1 y2 -> lt x1 y1 -> lt x2 y2（从 req 源侧
       运载到目标侧），故以 req_sym 翻转 plus_zero 腿入参。 *)
    simpl.
    exact (req_lt_compat (f x) (plus (f x) zero)
             (g x) (plus (g x) zero)
             (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
             (req_sym (plus (g x) zero) (g x) (plus_zero (g x)))
             (Hlt x)).
  - (* 归纳步 l=y::t：头项严格腿（Hlt x）+ 尾段同头形 IH（y），
       lt_plus_compat 双严格加法保序一次装配（接口字段，S07 req 面） *)
    exact (lt_plus_compat (f x) (g x)
             (sumd_list_sum S f (y :: t)) (sumd_list_sum S g (y :: t))
             (Hlt x) (IH y)).
Qed.

(* ============ 主件 2：槽形（非空 enum·正性前提形主件） ============ *)
(* 与宿主 sumd_sum_pos:331 同位 datum：非空前提显式参
   （dsu_neg (enum = nil) 位=Not 位同形，签名变化 7 同形同阶在档先例；
   Not 缺位适配见 dsu_neg 定义处注记）；nil 肢爆炸、cons 肢
   一行直引主件 1（照宿主 sumd_list_sum_pos:325-327 逐字同构）。 *)
Lemma dsu_sum_lt_pos : forall f g : S -> R,
  (forall s : S, lt zero (f s)) -> (forall s : S, lt (f s) (g s)) ->
  dsu_neg (enum = nil) -> lt (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros f g Hfp Hlt Hne.
  unfold sumd_sumf.
  destruct enum as [| x t].
  - destruct (Hne eq_refl).
  - exact (dsu_list_sum_lt_cons f g x t Hfp Hlt).
Qed.

End DsuStrictSum.

(* ============ 取证段 ============ *)
Print Assumptions dsu_list_sum_lt_cons.
Print Assumptions dsu_sum_lt_pos.
