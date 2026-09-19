(* ============================================================ *)
(* UpAblT9_UpReqSampling.v —— T9 批 Context 束两位 + TV 面两位·             *)
(*   UpReqSampling 辖区（sum/swap 面=T6a 已毕，零重叠）                     *)
(* 被消融位（普查表 §2 UpReqSampling 行）：                                *)
(*   位1 UpReqSampling.v:99   Context（Section ReqUContraction）           *)
(*   位2 UpReqSampling.v:701  Context（Section ReqBoundedSoftmax）         *)
(*   位3 UpReqSampling.v:126  delta_lt_one（TV 面，第⑦批坐标）             *)
(*   位4 UpReqSampling.v:131  minorization（TV 面，第⑦批坐标）             *)
(* 母本（零施工直喂，出节签名实测自 _tt9a_sig 探针）：                      *)
(*   位1 ←aux_delta_plus_omd@:153（omd 出节即 req_minus one delta）        *)
(*   位2 ←rsq_bs_list_const_sum@:790（纯 Context+list 数据位）             *)
(*   位3 ←rsq_bs_delta_star_lt_one@:935（delta_star 实例面）               *)
(*   位4 ←tvd_minorization@UpTVDoeblin:1933（跨模块实例面；req 层 le 在     *)
(*       RealEnhancedReal 实例位定义性=real_le，逐字 exact 喂参）           *)
(* 分级：四位全 N1。                                                       *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、     *)
(*   UpReqSumD、UpTVDoeblin、UpReqSampling。                               *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSumD.
Require Import UpTVDoeblin.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 位1 ←:99（rep@:153；R/RIS 实例位材料化） *)
Theorem uabT9_usamp_ctx_delta_plus_omd :
  forall delta : Real, req (plus delta (req_minus one delta)) one.
Proof.
  intro delta.
  exact (@aux_delta_plus_omd Real RealEnhancedReal delta).
Qed.

(* 位2 ←:701（rep@:790；R/RIS 实例位材料化，零接口前提） *)
Theorem uabT9_bsoft_ctx_list_const_sum :
  forall (S : Set) (c : Real) (l : list S),
    req (rsq_bs_list_sum S (fun _ : S => c) l)
       (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros S c l.
  exact (@rsq_bs_list_const_sum Real RealEnhancedReal S c l).
Qed.

(* 位3 ←:126（rep@:935；delta_star 具体实例材料化，TV 面） *)
Theorem uabT9_usamp_delta_star_lt_one :
  forall (temp : Real) (temp_pos : lt zero temp)
         (Delta : Real) (Delta_pos : lt zero Delta),
    lt (mult (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))
             (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))) one.
Proof.
  intros temp temp_pos Delta Delta_pos.
  exact (@rsq_bs_delta_star_lt_one Real RealEnhancedReal temp temp_pos Delta Delta_pos).
Qed.

(* 位4 ←:131（rep=UpTVDoeblin:1933 实例面；TV 面） *)
Theorem uabT9_usamp_minorization_tvd :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
         (z : list Real -> list Real -> Real),
    (forall i j : list Real, real_le (real_opp gamma) (z i j)) ->
    (forall i j : list Real, real_le (z i j) gamma) ->
    forall i j : list Real,
      le (mult (tvd_dstar Ttemp Ttemp_pos gamma) (tvd_u states n_pos j))
         (tvd_K states n_pos Ttemp Ttemp_pos z i j).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j.
  exact (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_usamp_ctx_delta_plus_omd.
Print Assumptions uabT9_bsoft_ctx_list_const_sum.
Print Assumptions uabT9_usamp_delta_star_lt_one.
Print Assumptions uabT9_usamp_minorization_tvd.
