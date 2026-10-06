(* ============================================================ *)
(* 模块名：abl_redischarge_sumd_inst —— abl_sumd_strict 实例化        *)
(*   消解＋dsu_neg 的 Set 层伴随载体件                                *)
(* 数学使命：①前件泛型严格和单调（正性前提形）在典范参数下的零参数   *)
(*   闭式推论：R 取 S02 Real 层（在役实例 RealEnhancedReal 复用，      *)
(*   S07:8596）、载体 S := unit、enum := tt::nil（最小非空枚举），     *)
(*   出 dsu_sum_lt_pos_u1／dsu_list_sum_lt_cons_u1 零 Section 参数    *)
(*   闭式；②载体升级：dsu_neg (P:Prop):Prop 增 Set 层伴随             *)
(*   dsu_neg_sb :={P}+{P->False}（sumbool，Set 类）判定件——           *)
(*   否定以 sumbool 承载，并给出表非空的具体判定件 dsu_list_ne_sb      *)
(*   （cons 肢否定数据自持；本安装无 Not，零 not/~/<> 书写）。         *)
(*   前件 Prop 定义 dsu_neg 原文保留（伴随为增量，零源文改动）。       *)
(* 依赖清单：前件 abl_sumd_strict（本池拷贝链编：dsu_neg／             *)
(*   dsu_sum_lt_pos／dsu_list_sum_lt_cons）；UpReqSumD（sumd 机器）；  *)
(*   S07_RealSetoidExpLog（RealInterfaceEnhancedSetoid＋               *)
(*   RealEnhancedReal 在役实例）；纯 Stdlib sumbool/List。             *)
(* 构造性注记：零承认／零经典逻辑；新增判定面全 Set 载体（sumbool）；   *)
(*   dsu_list_ne_sb Defined 出口保可提取（判定读数 vm_compute 可算）；  *)
(*   实例化推论为真消解（泛型定理直接使用，非重证非折算）。            *)
(* 编译配方：标准配方，本池链编                                        *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/     *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池>       *)
(*   && nice -19 rocq c -native-compiler no -Q                          *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 *)
(*   "" abl_sumd_strict.v（先）&& 同配方本件（后）。                    *)
(* ============================================================ *)

Require Import UpReqSumD.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Require Import abl_sumd_strict.

(* ---- §1 dsu_neg 的 Set 层伴随（sumbool 载体，Set 类） ---- *)
(*   P 的否定数据以 sumbool 承载：右肢即 P -> False（dsu_neg 同形），   *)
(*   左肢为肯定肢（判定件语义完整面）。                                  *)
Definition dsu_neg_sb (P : Prop) : Set := {P} + {P -> False}.

(* Prop 否定数据注入 sumbool 判定件（伴随桥，右向） *)
Theorem dsu_neg_sb_of_neg : forall P : Prop, dsu_neg P -> dsu_neg_sb P.
Proof.
  intros P H. exact (right H).
Qed.

(* ---- §2 表非空判定件（Set 层具体判定件；Defined 保可提取） ---- *)
(*   nil 肢左注（eq_refl）；cons 肢右注，否定数据自持（eq 消去空支）。   *)
Definition dsu_list_ne_sb (A : Set) (l : list A) : {l = []} + {dsu_neg (l = [])}.
Proof.
  destruct l as [| x t].
  - apply left. reflexivity.
  - apply right. intros H. discriminate H.
Defined.

(* 判定件读数一致性：dsu_neg 在手 ⟹ 判定件取右肢。 *)
Theorem dsu_list_ne_sb_neg_carry : forall (A : Set) (l : list A),
  dsu_neg (l = []) ->
  match dsu_list_ne_sb A l with
  | left _ => False
  | right _ => True
  end.
Proof.
  intros A l Hne. unfold dsu_list_ne_sb.
  destruct l as [| x t].
  - exact (False_ind _ (Hne eq_refl)).
  - exact I.
Qed.

(* ---- §3 主件实例化消解：unit 单点载体、tt::nil 最小非空枚举 ---- *)
(*   R 取 S02 Real（RealEnhancedReal 在役实例自动装填）；                *)
(*   非空前提由 dsu_neg 直证（tt::nil = [] 空消去）。                    *)
Theorem dsu_sum_lt_pos_u1 : forall f g : unit -> S02_CauchyComplete.Real,
  (forall s : unit, lt zero (f s)) ->
  (forall s : unit, lt (f s) (g s)) ->
  lt (sumd_sumf unit (tt :: nil) f) (sumd_sumf unit (tt :: nil) g).
Proof.
  intros f g Hfp Hlt.
  refine (dsu_sum_lt_pos unit (tt :: nil) f g Hfp Hlt _).
  intros H. discriminate H.
Qed.

(* cons 形主件同款消解（头 witness 形零参数闭式） *)
Theorem dsu_list_sum_lt_cons_u1 : forall f g : unit -> S02_CauchyComplete.Real,
  (forall s : unit, lt zero (f s)) ->
  (forall s : unit, lt (f s) (g s)) ->
  lt (sumd_list_sum unit f (tt :: nil)) (sumd_list_sum unit g (tt :: nil)).
Proof.
  intros f g Hfp Hlt.
  exact (dsu_list_sum_lt_cons unit f g tt nil Hfp Hlt).
Qed.

(* ---- §4 判定件数值烟测：tt::nil 判定为右肢（vm_compute 直算） ---- *)
Definition dsu_u1_ne_sb : {(tt :: nil) = []} + {dsu_neg ((tt :: nil) = [])} :=
  dsu_list_ne_sb unit (tt :: nil).

Lemma dsu_u1_ne_sb_right :
  match dsu_u1_ne_sb with left _ => false | right _ => true end = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- §5 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions dsu_neg_sb_of_neg.
Print Assumptions dsu_list_ne_sb_neg_carry.
Print Assumptions dsu_sum_lt_pos_u1.
Print Assumptions dsu_list_sum_lt_cons_u1.
Print Assumptions dsu_u1_ne_sb_right.
