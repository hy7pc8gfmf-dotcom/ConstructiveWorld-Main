(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(*
   接口引理显式项装配（req_refl/req_plus_compat/req_plus_exchange/plus_zero/mult_zero/
   distrib/req_sym/req_trans 复合链）。语句面逐字未动；零新增 Require；其余位逐字保留。 *)
(* ============================================================ *)
(* 辖区：G13_EvictFam.v EvictIdReq 节 sumf 接口面（L435/438/441 三位）            *)
(* 实例化消解源版本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 G13_EvictFam EvictIdReq 节的 req 求和接口面假设位逐条兑现消融定理：    *)
(*   假设位在具体有限和实例 sumf := sumd_sumf S enum 上全部无条件成立——          *)
(*   前提减薄为纯数据槽（枚举清单），假设位逐条消除。                            *)
(*                                                              *)
(*                                                              *)
(* 分级：3 件全 N1（库内实例化消解件直连；证明体非平凡内容在实例化消解件本体——               *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*   本批辖区无 pos/zero_nonneg 面（节内仅 linear/add/ext 三槽，源注自证）。      *)
(*                                                              *)
(* 依赖（全部只读使用，原树零改）：CW_ConstructiveWorld_219、UpReqSumD。          *)
(*   语句面逐字抽取自现档 G13_EvictFam.v（两树逐字节同验：Main/Live_X           *)
(*   md5 同 fa1cbb4f，917 行；L435/438/441 三位 sed 直取），                    *)
(*   仅 sumf → sumd_sumf S enum 换实例位。原节 Let 别名（zero/plus/mult 等为    *)
(*   接口投影 @R RIS 位）在出节全参形下经实例消解同轨。                          *)
(*                                                              *)
(* 备注：语句面全集合层；公理面零新增；文尾逐件 Print Assumptions 收尾。          *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ EvictIdReq（G13_EvictFam.v L414-442 接口面） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类           *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                                 *)

(* A1 ←L435 sum_linear（逐字：forall (a : R) (f : S -> R),
   req (sumf (fun s => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT12_g13_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (mult_zero _)).
  - simpl.
    exact (req_trans _ _ _
             (req_plus_compat _ _ _ _ (req_refl _) IH)
             (req_sym _ _ (distrib _ _ _))).
Qed.

(* A2 ←L438 sum_add（逐字：forall f g : S -> R,
   req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT12_g13_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (plus_zero _)).
  - simpl.
    exact (req_trans (plus (plus (f x) (g x)) (@sumd_list_sum _ _ _ (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat _ _ _ _ (req_refl _) IH) (req_trans (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_sym _ _ (plus_assoc (f x) (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (req_trans (plus (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (plus (f x) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t)))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat (f x) (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (plus (g x) (@sumd_list_sum _ _ _ f t)) (@sumd_list_sum _ _ _ g t)) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (plus_assoc (g x) (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)) (req_trans (plus (plus (g x) (@sumd_list_sum _ _ _ f t)) (@sumd_list_sum _ _ _ g t)) (plus (plus (@sumd_list_sum _ _ _ f t) (g x)) (@sumd_list_sum _ _ _ g t)) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat (plus (g x) (@sumd_list_sum _ _ _ f t)) (plus (@sumd_list_sum _ _ _ f t) (g x)) (@sumd_list_sum _ _ _ g t) (@sumd_list_sum _ _ _ g t) (plus_comm (g x) (@sumd_list_sum _ _ _ f t)) (req_refl (@sumd_list_sum _ _ _ g t))) (req_sym _ _ (plus_assoc (@sumd_list_sum _ _ _ f t) (g x) (@sumd_list_sum _ _ _ g t)))))) (plus_assoc (f x) (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t)))))).
Qed.

(* A3 ←L441 sum_ext（逐字：forall f g : S -> R,
   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT12_g13_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl _).
  - simpl. exact (req_plus_compat _ _ _ _ (H x) IH).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT12_g13_sum_linear.
Print Assumptions uabT12_g13_sum_add.
Print Assumptions uabT12_g13_sum_ext.
