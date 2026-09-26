(* ToyR 消融刀位注记（T259 台账席·包T·tier2十批）：本件三玩具位（sumd 族单 exact 直喂）
   按结构性推导口径落刀重证：unfold sumd_sumf 定义层展开＋enum 列表归纳＋simpl 定义层化简，
   接口引理显式项装配（req_refl/req_plus_compat/req_plus_exchange/plus_zero/mult_zero/
   distrib/req_sym/req_trans 复合链）。语句面逐字未动；零新增 Require；其余位逐字保留。 *)
(* ============================================================ *)
(* UpAblT6_UpSigMigrate2.v —— 假设消融战役 T6 批·席 a（T3a 移交同根余量前 ≤25 位之 3 位） *)
(* 辖区：UpSigMigrate2.v ReqFECore 节 sumf 接口面（L97-102 三位）                *)
(* 放电母本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 UpSigMigrate2 的 sumf 接口面假设位逐条兑现消融定理：                  *)
(*   假设位在具体有限和实例 sumf := sumd_sumf S enum 上全部无条件成立——          *)
(*   前提减薄为纯数据槽（枚举清单），假设位逐条消除。                            *)
(*                                                              *)
(* 主件清单（3 件，前缀 uabT6_，逐件标注被消融位坐标与放电件）：                  *)
(*    A1 uabT6_sigmig2_sum_ext    ←L97 sum_ext    放电 sumd_sum_ext@UpReqSumD:112 *)
(*    A2 uabT6_sigmig2_sum_add    ←L99 sum_add    放电 sumd_sum_add@:161 *)
(*    A3 uabT6_sigmig2_sum_linear ←L102 sum_linear 放电 sumd_sum_linear@:135 *)
(*                                                              *)
(* 分级：3 件全 N1（库内放电件直连；证明体非平凡内容在放电件本体——               *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*   本批辖区无 pos/zero_nonneg 面（L93/96 sumf/L107-111 数据位与 L109 D_pos     *)
(*   属 T 批辖区，FA2 表判 T，未纳入）；W 面：本模块无。                          *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqSumD。         *)
(*   语句面逐字抽取自现档 UpSigMigrate2.v（两树逐字节同验：Main/Live_X          *)
(*   md5 同 e1430b0e，2026-09-15 版，与 FA2 普查表行号逐位核对一致），            *)
(*   仅 sumf → sumd_sumf S enum 换实例位（源语句面 fun s => 无类型注形逐字保留）。*)
(*                                                              *)
(* 备注：语句面全集合层；公理面零新增；文尾逐件 Print Assumptions 收尾。          *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblT6_UpSigMigrate2.log。             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ ReqFECore（UpSigMigrate2.v L92-104） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类           *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                                 *)

(* A1 ←L97 sum_ext（逐字：forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT6_sigmig2_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl _).
  - simpl. exact (req_plus_compat _ _ _ _ (H x) IH).
Qed.

(* A2 ←L99 sum_add（逐字：forall f g : S -> R, req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT6_sigmig2_sum_add :
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

(* A3 ←L102 sum_linear（逐字：forall (a : R) (f : S -> R), req (sumf (fun s => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT6_sigmig2_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s => mult a (f s))) (mult a (sumd_sumf S enum f)).
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

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT6_sigmig2_sum_ext.
Print Assumptions uabT6_sigmig2_sum_add.
Print Assumptions uabT6_sigmig2_sum_linear.
