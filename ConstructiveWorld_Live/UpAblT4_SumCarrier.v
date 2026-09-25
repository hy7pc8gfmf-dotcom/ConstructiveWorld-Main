(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(*                                                              *)
(* 阶段工单：_tt4a_｜辖区＝FA1 普查第⑤批 sum 载体四槽（rows 1-40）：       *)
(*   G02_Debt:165-175（RealScaleDual）与 471-491（RealAttnGibbsTemp）       *)
(*   ｜S08_RealMainlineDPO:1984/2090/2093/2326-2331/2470-2473 sum 槽族      *)
(*   ｜CW220_Extensions:169/662 sumf 槽｜S10_KVQuantTrig:61 求和槽          *)
(*                                                              *)
(* 消融路线（E-STAGING-FA3 三分类·N3 实例供给／N2 已证件导出）：            *)
(*   主件 uabt4_sum_carrier4_realized＝fa57_sum_carrier_realizes:63 的      *)
(*   Real 层转换同构（G04ProjHook 先例：fa57 供件走 S01 接口抽象世界，       *)
(*   母槽闭名走 S02 柯西 Real 具体层，故按蓝图转换）；载体＝S08:288          *)
(*   real_list_sum 列表折叠，pos/ext/linear 三组件由 in-tree                *)
(*   real_list_sum_pos:463/ext:295/linear:362 直接给出（E389/E703 与            *)
(*   fa56b_sumd_cong:155、fa56_sumd_mult_const:65 的 Real 层同构件）。      *)
(*   出节 discharge 全参形（RateTheoryAblation §2 式）：以槽见证喂           *)
(*   G02/S08 节定理出节全参调用位。                                        *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219 薄壳。              *)
(* 备注：语句面全 Set 层（Id/Or/Not 用基座 Set 层定义，零 Prop 泄露；         *)
(*   载体非空前提沿 fa57 用基座 Not/Id，喂 in-tree 件时经消去桥转写）；      *)
(*   纯构造性零承认位；公理面零新增；文末逐件 Print Assumptions 留痕。       *)
(* 分级申报：uabt4_sum_carrier4_realized＝N3（四槽一次兑现包）；            *)
(*   uabt4_rsum_le＝T（in-tree real_list_sum_le:432 直接给出一行桥，普查        *)
(*   「list折叠单调归纳」路线已被库内现成件闭合，如实降 T 禁注水）；        *)
(*   三件出节 discharge＝N2（源版本直连全参喂，前提减薄后仍非平凡）；          *)
(*   uabt4_rsum_add／uabt4_rsum_ext_brid＝T（in-tree 已证件透明一行桥，      *)
(*   合并申报不计非平凡战果）。                                            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G02_Debt.
From Stdlib Require Import Extraction.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ==================== 主件：载体四槽一次兑现包（N3） ==================== *)
(* 对照 fa57_ext.v:63-81（S01 接口层原装）与 G02_Debt.v:168-176 槽语句逐字： *)
(*   pos：逐点正 ⟹ 和正；ext：逐点相等 ⟹ 和相等；linear：和(a·f)==a·和 f。 *)
(*   sigT 见证＝real_list_sum X 列表折叠（S08:288），三组件按 in-tree        *)
(*   pos/ext/linear 直接给出；非空前提 Hne 经消去桥转写喂 real_list_sum_pos。    *)
Theorem uabt4_sum_carrier4_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> Real) -> Real =>
            And (forall f : X -> Real,
                   (forall w : X, real_lt real_zero (f w)) -> real_lt real_zero (sumf f))
                (And (forall f g : X -> Real,
                        (forall w : X, real_eq (f w) (g w)) -> real_eq (sumf f) (sumf g))
                     (forall (a : Real) (f : X -> Real),
                        real_eq (sumf (fun w => real_mult a (f w)))
                                (real_mult a (sumf f))))).
Proof.
  intros X enum Hne.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (existT _
                (fun f => real_list_sum X f enum)
                ((fun f Hf => real_list_sum_pos X f enum Hf Hne'),
                 ((fun f g Hpt => real_list_sum_ext X f g enum Hpt),
                  (fun a f => real_list_sum_linear X a f enum)))).
Qed.

(* ==================== 载体槽件：折叠单调（N2） ==================== *)
(* 槽语句对照 S08:2328-2330（RealPPOMain real_sum_over_S_le）与            *)
(* UpRealLeB:277（RealPPOLeB 同名位，普查 N·「list折叠单调归纳」）。         *)
(* 证明＝real_le 的 Set 和两支分解：lt 支走 S02:3195 real_lt_plus_compat，  *)
(* eq 支走 RealSetoid.real_eq_plus_compat，逐位归纳闭合。                   *)
Theorem uabt4_rsum_le :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    (forall w : X, real_le (f w) (g w)) ->
    real_le (real_list_sum X f enum) (real_list_sum X g enum).
Proof. exact (fun X f g enum Hle => real_list_sum_le X f g enum Hle). Qed.

(* ==================== T 件合并申报（透明一行桥×2） ==================== *)
(* 槽语句对照 S08:2331-2333（PPO add）/2089-（Steady ext）；in-tree      *)
(* real_list_sum_add:340/ext:295 直接给出，一行桥（T 级，合并申报）。            *)
Corollary uabt4_rsum_add :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    real_eq (real_list_sum X (fun w => real_plus (f w) (g w)) enum)
            (real_plus (real_list_sum X f enum) (real_list_sum X g enum)).
Proof. exact (fun X f g enum => real_list_sum_add X f g enum). Qed.

Corollary uabt4_rsum_ext_brid :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    (forall w : X, real_eq (f w) (g w)) ->
    real_eq (real_list_sum X f enum) (real_list_sum X g enum).
Proof. exact (fun X f g enum Hpt => real_list_sum_ext X f g enum Hpt). Qed.

(* ==================== 出节 discharge×3（N2，源版本直连全参喂） ==================== *)

(* —— G02 RealScaleDual:184 配分正性槽 discharge —— *)
(* 源版本节定理 real_partition_function_scaled_pos（G02:184-191，使用         *)
(* pos 槽）出节全参调用位：X＋载体＋pos 见证喂定。                          *)
Theorem uabt4_g02_partition_scaled_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (c : Real) (z : X -> Real),
      real_lt real_zero
        (real_partition_function_scaled X (fun f => real_list_sum X f enum) c z).
Proof.
  intros X enum Hne c z.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (real_partition_function_scaled_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') c z).
Qed.

(* —— G02 RealAttnGibbsTemp:508 温度配分正性槽 discharge —— *)
(* 源版本节定理 gibbst_real_partition_function_temp_pos（G02:508-513，       *)
(* 使用 pos 槽；节内 T/T_pos/z_logits 随定义携带）出节全参喂定。            *)
Theorem uabt4_g02_gibbst_partition_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (T : Real) (T_pos : real_lt real_zero T) (z_logits : X -> Real),
      real_lt real_zero
        (gibbst_real_partition_function_temp X (fun f => real_list_sum X f enum)
           T T_pos z_logits).
Proof.
  intros X enum Hne T T_pos z_logits.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (gibbst_real_partition_function_temp_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') T T_pos z_logits).
Qed.

(* —— S08 RealAttnMain: 配分正性槽 discharge —— *)
(* 源版本节定理 real_partition_function_pos（S08:2001-，使用 pos 槽）    *)
(* 出节全参喂定（D/energy 位不被该件使用，不出参——P7B 消去规则）。          *)
Theorem uabt4_s08_partition_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (z : X -> Real),
      real_lt real_zero
        (real_partition_function X (fun f => real_list_sum X f enum) z).
Proof.
  intros X enum Hne z.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (real_partition_function_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') z).
Qed.

(* ==================== 提取检验（树外 ASCII 隔离目录） ==================== *)
Set Extraction Output Directory "C:/Users/Live/AppData/Local/Temp/uabt4_ext".
Extraction "uabt4_rsum_le.ml" uabt4_rsum_le.
Extraction "uabt4_g02_partition_scaled_pos_realized.ml" uabt4_g02_partition_scaled_pos_realized.
Extraction "uabt4_s08_partition_pos_realized.ml" uabt4_s08_partition_pos_realized.

(* ==================== 假设面闭合申报 ==================== *)
Print Assumptions uabt4_sum_carrier4_realized.
Print Assumptions uabt4_rsum_le.
Print Assumptions uabt4_rsum_add.
Print Assumptions uabt4_rsum_ext_brid.
Print Assumptions uabt4_g02_partition_scaled_pos_realized.
Print Assumptions uabt4_g02_gibbst_partition_pos_realized.
Print Assumptions uabt4_s08_partition_pos_realized.
