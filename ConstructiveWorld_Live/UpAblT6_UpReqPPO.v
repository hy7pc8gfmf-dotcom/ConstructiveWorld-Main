(* ToyR 消融刀位注记（T259 台账席·包T·tier2十批）：本件三玩具位（sumd 族单 exact 直喂）
   按结构性推导口径落刀重证：unfold sumd_sumf 定义层展开＋enum 列表归纳＋simpl 定义层化简，
   接口引理显式项装配（req_refl/req_plus_compat/req_plus_exchange/plus_zero/mult_zero/
   distrib/req_sym/req_trans 复合链）。语句面逐字未动；零新增 Require；其余位逐字保留。 *)
(* ============================================================ *)
(* UpAblT6_UpReqPPO.v —— 假设消融战役 T6 批·席 a（T3a 移交同根余量前 ≤25 位之 3 位） *)
(* 辖区：UpReqPPO.v ReqPPOAdvantage 节 sumf 接口面（L72-77 三位）                *)
(* 放电母本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 UpReqPPO 的 sumf 接口面假设位逐条兑现消融定理：                       *)
(*   假设位在具体有限和实例 sumf := sumd_sumf S enum 上全部无条件成立——          *)
(*   前提减薄为纯数据槽（枚举清单），假设位逐条消除。                            *)
(*                                                              *)
(* 主件清单（3 件，前缀 uabT6_，逐件标注被消融位坐标与放电件）：                  *)
(*    A1 uabT6_rppo_sum_ext    ←L72 sum_ext    放电 sumd_sum_ext@UpReqSumD:112 *)
(*    A2 uabT6_rppo_sum_add    ←L74 sum_add    放电 sumd_sum_add@:161 *)
(*    A3 uabT6_rppo_sum_linear ←L77 sum_linear 放电 sumd_sum_linear@:135 *)
(*                                                              *)
(* 分级：3 件全 N1（库内放电件直连；证明体非平凡内容在放电件本体——               *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*                                                              *)
(* 载体注记（诚实申报，不注水）：原节 Context {R}{RIS} 在本文件消费面 occ=0      *)
(*   （FA2 普查表 UpReqPPO L67 位判 T：本文件直接用 Real 载体，P7B 出节消去      *)
(*   判例）——sumf 实际型为 (S -> Real) -> Real，语句面 req/plus/mult 在          *)
(*   Real 载体实例（RealInterfaceEnhancedSetoid Real，库内全局实例供给）上       *)
(*   解释。故本件消融形不携带 R/RIS 形参，R 钉 Real，sumd 族隐式 {R}{RIS}        *)
(*   经全局实例消解直连（放电机械对抽象 R 成立，Real 实例为其特例）。            *)
(*   本批辖区无 pos/zero_nonneg 面；W 面：本模块无（FA2 表 UpReqPPO 无 W 位）。   *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqSumD。         *)
(*   语句面逐字抽取自现档 UpReqPPO.v（两树逐字节同验：Main/Live_X               *)
(*   md5 同 5af053cb，2026-09-15 版，与 FA2 普查表行号逐位核对一致），            *)
(*   仅 sumf → sumd_sumf S enum 换实例位（源语句面 fun s => 无类型注形逐字保留）。*)
(*                                                              *)
(* 备注：语句面全集合层；公理面零新增；文尾逐件 Print Assumptions 收尾。          *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblT6_UpReqPPO.log。                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ ReqPPOAdvantage（UpReqPPO.v L67-79） ============ *)
(* 原节 Context {R}{RIS} occ=0（P7B 出节消去判例），sumf 实际型                  *)
(* (S -> Real) -> Real；本件 R 钉 Real（全局载体实例消解），sumf 换              *)
(* sumd_sumf S enum 实例。                                                     *)

(* A1 ←L72 sum_ext（逐字：forall f g : S -> Real, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT6_rppo_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl _).
  - simpl. exact (req_plus_compat _ _ _ _ (H x) IH).
Qed.

(* A2 ←L74 sum_add（逐字：forall f g : S -> Real, req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT6_rppo_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    req (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (plus_zero _)).
  - simpl.
    exact (req_trans (plus (plus (f x) (g x)) (@sumd_list_sum _ _ _ (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat _ _ _ _ (req_refl _) IH) (req_trans (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_sym _ _ (plus_assoc (f x) (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (req_trans (plus (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)))) (plus (f x) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t)))) (plus (plus (f x) (@sumd_list_sum _ _ _ f t)) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat (f x) (f x) (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t))) (plus (plus (g x) (@sumd_list_sum _ _ _ f t)) (@sumd_list_sum _ _ _ g t)) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (plus_assoc (g x) (@sumd_list_sum _ _ _ f t) (@sumd_list_sum _ _ _ g t)) (req_trans (plus (plus (g x) (@sumd_list_sum _ _ _ f t)) (@sumd_list_sum _ _ _ g t)) (plus (plus (@sumd_list_sum _ _ _ f t) (g x)) (@sumd_list_sum _ _ _ g t)) (plus (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t))) (req_plus_compat (plus (g x) (@sumd_list_sum _ _ _ f t)) (plus (@sumd_list_sum _ _ _ f t) (g x)) (@sumd_list_sum _ _ _ g t) (@sumd_list_sum _ _ _ g t) (plus_comm (g x) (@sumd_list_sum _ _ _ f t)) (req_refl (@sumd_list_sum _ _ _ g t))) (req_sym _ _ (plus_assoc (@sumd_list_sum _ _ _ f t) (g x) (@sumd_list_sum _ _ _ g t)))))) (plus_assoc (f x) (@sumd_list_sum _ _ _ f t) (plus (g x) (@sumd_list_sum _ _ _ g t)))))).
Qed.

(* A3 ←L77 sum_linear（逐字：forall (a : Real) (f : S -> Real), req (sumf (fun s => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT6_rppo_sum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    req (sumd_sumf S enum (fun s => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (mult_zero _)).
  - simpl.
    exact (req_trans _ _ _
             (req_plus_compat _ _ _ _ (req_refl _) IH)
             (req_sym _ _ (distrib _ _ _))).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT6_rppo_sum_ext.
Print Assumptions uabT6_rppo_sum_add.
Print Assumptions uabT6_rppo_sum_linear.
