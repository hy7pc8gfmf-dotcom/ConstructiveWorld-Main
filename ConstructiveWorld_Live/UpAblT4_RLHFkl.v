(* ============================================================ *)
(* UpAblT4_RLHFkl.v —— 第⑥批 gibbs/KL 旗舰消融件（T4a 施工席 20260919）      *)
(*                                                              *)
(* 批次工单：_tt4a_｜辖区＝FA1 普查第⑥批 gibbs/KL 旗舰（rows 1-40）：        *)
(*   S08_RealMainlineDPO:2522 real_gibbs_sum_eps／2527 real_kl_decomp_full   *)
(*   ｜UpRealLeB:215／227 同名位（RealRLHFLeB 供给槽）                       *)
(*   ｜S08:2501 real_boltzmann_log_decomp（T·零消费位，剪除即消融，不立件）   *)
(*   ｜S08:2508 real_kl_term_equiv（消费位重判，见偏差账，本批不立件）。      *)
(*                                                              *)
(* 消融路线（E-STAGING-FA3 三分类·N2 已证件导出，出节全参形）：              *)
(*   gibbs 槽 ← logd_gibbs_sum_eps_boltzmann_list（G05_LogSmall:1174，      *)
(*   Part E 槽填件）；KL 槽 ← rfep_real_kl_decomp_full（UpReqRealFEP:805     *)
(*   正典件，节闭全参形；RealKLDecomp:765/RealKLCorrMark:51 为其同构 mend   *)
(*   系，因该件 .vo 代际失配本批改走正典件——偏差账登记）。                 *)
(*   载体 sumf := fun f => real_list_sum X f enum（⑤批同款 Real 层列表      *)
(*   载体），ext/add/linear 三桥由 in-tree real_list_sum_ext:295/add:340/   *)
(*   linear:362 直配（rkd 主件1 的诚实结构增量位）。                        *)
(*   消融件实测行数（开工取证）：UpReqRealFEP 906→现档核对随报告。          *)
(*   旗舰结论喂 S08 real_rlhf_optimal_eps（S08:2602）与 UpRealLeB           *)
(*   real_rlhf_optimal_B（Bishop 形）出节全参调用位——即 E751 坑 2 式        *)
(*   消费位调用形逐参喂定（UpRealLeB:247 先例九参形）。                     *)
(* 诚实增量申报（RealKLCorrMark 勘误定谳沿袭）：原槽前提面仅 Hp/Hnormp，     *)
(*   一般正证书 Z 下结论面字面假（单点反例差 D·log Z·(Σp_b−1)）；本件按      *)
(*   mend 形携带 Hnormb : Σ p_b == 1（G05 Part E 供给槽同款显式位）。        *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219＋G05_LogSmall＋      *)
(*   RealKLDecomp＋UpRealLeB。                                              *)
(* 备注：语句面全 Set 层零 Prop 泄露；纯构造性零承认位；公理面零新增；        *)
(*   文末逐件 Print Assumptions 留痕。                                      *)
(* 分级申报：两件旗舰＝N2（G05:1174＋UpReqRealFEP:805 双件直连喂定，        *)
(*   载体实例化后仍非平凡）；S08:2501＝T（零消费位剪除即消融）；             *)
(*   S08:2508＝消费位重判挂账（见偏差账）。                                 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Require Import UpReqRealFEP.
Require Import UpRealLeB.
From Stdlib Require Import Extraction.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ==================== 旗舰件1：RLHF 最优性 eps 形 discharge（N2） ==================== *)
(* 母本消费位：S08 real_rlhf_optimal_eps（RealRLHFMain 节，出节全参十四位：  *)
(*   S sumf base D Dp Z Zp ＋ gibbs 槽 ＋ KL 槽 ＋ pi Hpi Hnormpi eps Heps， *)
(*   参序实测锚＝UpRealLeB:247 九参形喂法）。两槽分别由 G05:1174 与          *)
(*   RealKLDecomp:765 喂定，载体＝real_list_sum 列表折叠。                   *)
Theorem uabt4_rlhf_eps_realized :
  forall (X : Type) (enum : list X) (base : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p enum) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s) enum)
                real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le (real_opp (real_free_energy X (fun f => real_list_sum X f enum) base D p Hp))
          (real_plus
             (real_opp
                (real_free_energy X (fun f => real_list_sum X f enum) base D
                   (real_boltzmann_dist_r X base D D_pos Z Z_pos)
                   (real_boltzmann_dist_r_pos X base D D_pos Z Z_pos)))
             (real_mult D eps)).
Proof.
  intros X enum base D D_pos Z Z_pos p Hp Hnormp Hnormb eps Heps.
  exact (real_rlhf_optimal_eps X (fun f => real_list_sum X f enum) base D D_pos Z Z_pos
           (fun p0 Hp0 Hnormp0 eps0 Heps0 =>
              logd_gibbs_sum_eps_boltzmann_list X base D D_pos Z Z_pos enum
                p0 Hp0 Hnormp0 Hnormb eps0 Heps0)
           (fun p0 Hp0 Hnormp0 =>
              rfep_real_kl_decomp_full X (fun f => real_list_sum X f enum)
                (fun f g Hpt => real_list_sum_ext X f g enum Hpt)
                (fun f g => real_list_sum_add X f g enum)
                (fun a f => real_list_sum_linear X a f enum)
                base D D_pos Z Z_pos p0 Hp0 Hnormp0 Hnormb)
           p Hp Hnormp eps Heps).
Qed.

(* ==================== 旗舰件2：RLHF 最优性 Bishop 形 discharge（N2） ==================== *)
(* 母本消费位：UpRealLeB real_rlhf_optimal_B（RealRLHFLeB 节，L235；        *)
(*   两侧取负的 real_le_b 升格形）。同款双槽喂定——UpRealLeB:215／227        *)
(*   同名供给槽随本件一并销账。                                             *)
Theorem uabt4_rlhf_B_realized :
  forall (X : Type) (enum : list X) (base : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p enum) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s) enum)
                real_one),
  real_le_b (real_opp (real_free_energy X (fun f => real_list_sum X f enum) base D p Hp))
            (real_opp
               (real_free_energy X (fun f => real_list_sum X f enum) base D
                  (real_boltzmann_dist_r X base D D_pos Z Z_pos)
                  (real_boltzmann_dist_r_pos X base D D_pos Z Z_pos))).
Proof.
  intros X enum base D D_pos Z Z_pos p Hp Hnormp Hnormb.
  exact (real_rlhf_optimal_B X (fun f => real_list_sum X f enum) base D D_pos Z Z_pos
           (fun p0 Hp0 Hnormp0 eps0 Heps0 =>
              logd_gibbs_sum_eps_boltzmann_list X base D D_pos Z Z_pos enum
                p0 Hp0 Hnormp0 Hnormb eps0 Heps0)
           (fun p0 Hp0 Hnormp0 =>
              rfep_real_kl_decomp_full X (fun f => real_list_sum X f enum)
                (fun f g Hpt => real_list_sum_ext X f g enum Hpt)
                (fun f g => real_list_sum_add X f g enum)
                (fun a f => real_list_sum_linear X a f enum)
                base D D_pos Z Z_pos p0 Hp0 Hnormp0 Hnormb)
           p Hp Hnormp).
Qed.

(* ==================== 提取探针（树外 ASCII 隔离目录） ==================== *)
Set Extraction Output Directory "C:/Users/Live/AppData/Local/Temp/uabt4_ext".
Extraction "uabt4_rlhf_eps_realized.ml" uabt4_rlhf_eps_realized.
Extraction "uabt4_rlhf_B_realized.ml" uabt4_rlhf_B_realized.

(* ==================== 假设面收口申报 ==================== *)
Print Assumptions uabt4_rlhf_eps_realized.
Print Assumptions uabt4_rlhf_B_realized.
