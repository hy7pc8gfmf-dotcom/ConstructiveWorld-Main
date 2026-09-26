(* ==========================================================================)
   PA_TempSoftmaxInstantiation.v — 温度加权 softmax 的实例化面
   使命: tsi_twp_is_boltzmann_weight（温度加权概率 == Boltzmann 权）、tsi_temp_weighted_normalized/tsi_temp_weighted_mix_normalized（归一与凸混合归一）、tsi_temp_scale_duality（温度尺度对偶）与 tsi_temp_weighted_relative。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqAttnGibbs
   对标: 温度化 softmax/Boltzmann 加权的归一性、混合性与温度对偶（统计力学采样面）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAttnGibbs.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* 装配桥 B1 辅件：eps 伸张一步引理（le a (a+eps)，0<eps）                 *)
(* ===================================================================== *)
Lemma tsi_le_plus_eps_r :
  forall (RI : RealInterfaceEnhanced) (a eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI a eps).
Proof.
  intros RI a eps Hlt.
  apply (@S01_BaseRing.le_id_l RI a
           (@S01_BaseRing.plus RI a (@S01_BaseRing.zero RI))
           (@S01_BaseRing.plus RI a eps)).
  - exact (id_sym (@S01_BaseRing.plus_zero RI a)).
  - exact (@S01_BaseRing.le_plus_compat RI a a (@S01_BaseRing.zero RI) eps
             (@S01_BaseRing.le_refl RI a)
             (@S01_BaseRing.lt_le_iff RI (@S01_BaseRing.zero RI) eps (inl Hlt))).
Qed.

(* ===================================================================== *)
(* 装配桥 B1：RI → RealInterfaceEnhancedSetoid (@R RI) 总实例（req:=Id）  *)
(*   76 字段直引 + 13 逐 eps 形字段经 tsi_le_plus_eps_r + le_trans。      *)
(* ===================================================================== *)
Instance tsi_rie_setoid (RI : RealInterfaceEnhanced)
  : RealInterfaceEnhancedSetoid (@S01_BaseRing.R RI)
  := Build_RealInterfaceEnhancedSetoid (@S01_BaseRing.R RI)
  (* setoid 核心：req := Id（S01 Set 层幺等） *)
  (fun x y => Id x y)
  (fun x => @id_refl _ x)
  (fun x y p => @id_sym _ x y p)
  (fun x y z p q => @id_trans _ x y z p q)
  (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI)
  (@S01_BaseRing.plus RI) (@S01_BaseRing.mult RI) (@S01_BaseRing.opp RI)
  (@S01_BaseRing.abs RI) (@S01_BaseRing.lt RI) (@S01_BaseRing.le RI)
  (fun x1 x2 y1 y2 p q => @id_cong2 _ _ _ (@S01_BaseRing.plus RI) x1 x2 y1 y2 p q)
  (fun x1 x2 y1 y2 p q => @id_cong2 _ _ _ (@S01_BaseRing.mult RI) x1 x2 y1 y2 p q)
  (fun x y p => @id_cong _ _ (@S01_BaseRing.opp RI) x y p)
  (fun x y p => @id_cong _ _ (@S01_BaseRing.abs RI) x y p)
  (fun x1 x2 y1 y2 p q h =>
     @S01_BaseRing.lt_id_r RI x2 y1 y2 q (@S01_BaseRing.lt_id_l RI x2 x1 y1 (id_sym p) h))
  (fun x1 x2 y1 y2 p q h =>
     @S01_BaseRing.le_id_r RI x2 y1 y2 q (@S01_BaseRing.le_id_l RI x2 x1 y1 (id_sym p) h))
  (* 环代数（Id 形 = req 形逐字同） *)
  (@S01_BaseRing.plus_assoc RI) (@S01_BaseRing.plus_comm RI)
  (@S01_BaseRing.plus_zero RI) (@S01_BaseRing.plus_opp RI)
  (@S01_BaseRing.mult_assoc RI) (@S01_BaseRing.mult_comm RI)
  (@S01_BaseRing.mult_one RI) (@S01_BaseRing.distrib RI)
  (@S01_BaseRing.mult_zero RI)
  (@S01_BaseRing.lt_irrefl RI) (@S01_BaseRing.lt_trans RI)
  (@S01_BaseRing.le_refl RI) (@S01_BaseRing.le_trans RI)
  (@S01_BaseRing.le_antisym RI) (@S01_BaseRing.le_lt_trans RI)
  (@S01_BaseRing.lt_le_trans RI) (@S01_BaseRing.lt_le_iff RI)
  (@S01_BaseRing.le_id_l RI) (@S01_BaseRing.le_id_r RI)
  (@S01_BaseRing.lt_id_l RI) (@S01_BaseRing.lt_id_r RI)
  (@S01_BaseRing.inv_pos RI) (@S01_BaseRing.inv_pos_correct RI)
  (@S01_BaseRing.one_pos RI)
  (@S01_BaseRing.lt_plus_compat RI) (@S01_BaseRing.le_plus_compat RI)
  (@S01_BaseRing.plus_positive RI) (@S01_BaseRing.mult_positive RI)
  (@S01_BaseRing.lt_mult_compat RI) (@S01_BaseRing.le_mult_compat RI)
  (@S01_BaseRing.le_mult_compat_weak RI) (@S01_BaseRing.opp_lt_compat RI)
  (@S01_BaseRing.lt_zero_opp RI) (@S01_BaseRing.opp_le_compat RI)
  (@S01_BaseRing.inv_pos_pos RI) (@S01_BaseRing.inv_pos_ext RI)
  (@S01_BaseRing.inv_pos_le_compat RI)
  (* min：逐 eps 形 = 非 eps 字段 + eps 伸张 *)
  (@S01_BaseRing.min RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.min RI a b) a
       (@S01_BaseRing.plus RI a eps)
       (@S01_BaseRing.min_le_l RI a b) (tsi_le_plus_eps_r RI a eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.min RI a b) b
       (@S01_BaseRing.plus RI b eps)
       (@S01_BaseRing.min_le_r RI a b) (tsi_le_plus_eps_r RI b eps Heps))
  (@S01_BaseRing.min_pos RI)
  (* r_max：逐 eps 形同款 *)
  (@S01_BaseRing.r_max RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI a (@S01_BaseRing.r_max RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.r_max RI a b) eps)
       (@S01_BaseRing.r_max_le_l RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.r_max RI a b) eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI b (@S01_BaseRing.r_max RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.r_max RI a b) eps)
       (@S01_BaseRing.r_max_le_r RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.r_max RI a b) eps Heps))
  (@S01_BaseRing.r_max_l_iff RI) (@S01_BaseRing.r_max_r_iff RI)
  (@S01_BaseRing.pos_test RI) (@S01_BaseRing.pos_test_lt RI)
  (@S01_BaseRing.lt_pos_test RI)
  (@S01_BaseRing.pos_part RI) (@S01_BaseRing.pos_part_def RI)
  (fun a eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.pos_part RI a)
       (@S01_BaseRing.plus RI (@S01_BaseRing.pos_part RI a) eps)
       (@S01_BaseRing.pos_part_nonneg RI a)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.pos_part RI a) eps Heps))
  (@S01_BaseRing.r_if RI) (@S01_BaseRing.r_if_true RI) (@S01_BaseRing.r_if_false RI)
  (* abs：逐 eps 形同款 *)
  (fun a eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.abs RI a)
       (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) eps)
       (@S01_BaseRing.abs_nonneg RI a)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.abs RI a) eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.abs RI (@S01_BaseRing.plus RI a b))
       (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b)) eps)
       (@S01_BaseRing.abs_triangle RI a b)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b))
          eps Heps))
  (@S01_BaseRing.abs_zero RI) (@S01_BaseRing.abs_mult RI)
  (@S01_BaseRing.abs_opp RI) (@S01_BaseRing.abs_pos RI)
  (@S01_BaseRing.exp_neg RI) (@S01_BaseRing.exp_neg_pos RI)
  (@S01_BaseRing.exp_neg_zero RI) (@S01_BaseRing.exp_neg_plus RI)
  (@S01_BaseRing.exp_neg_decr RI) (@S01_BaseRing.exp_neg_le_decr RI)
  (* log 家：受体 log:R->R 丢弃正性指标；log_le_linear_eps 源 = Enhanced *)
  (*   log_le_linear 字段（le (log x) (x-1)，minus := plus x (opp one) δ） *)
  (fun x _ => @S01_BaseRing.log RI x)
  (fun a b Ha Hb => @S01_BaseRing.log_mult RI a b Ha Hb)
  (fun _ => @S01_BaseRing.log_one RI)
  (fun x Hx eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.log RI x)
       (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI)))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI))) eps)
       (@S01_BaseRing.log_le_linear RI x Hx)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI)))
          eps Heps))
  (fun x _ => @S01_BaseRing.log_inv RI x)
  (fun x Hx => @S01_BaseRing.log_inv_log RI x Hx)
  (fun x _ => @S01_BaseRing.exp_neg_log_inv RI x)
  (* metric/lim/cauchy：逐 eps 形同款 + Id 形直引 *)
  (@S01_BaseRing.metric RI) (@S01_BaseRing.metric_sym RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.metric RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b) eps)
       (@S01_BaseRing.metric_pos RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.metric RI a b) eps Heps))
  (@S01_BaseRing.metric_zero RI)
  (fun a b c eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.metric RI a c)
       (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b) (@S01_BaseRing.metric RI b c))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b)
             (@S01_BaseRing.metric RI b c)) eps)
       (@S01_BaseRing.metric_triangle RI a b c)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b)
             (@S01_BaseRing.metric RI b c)) eps Heps))
  (@S01_BaseRing.lim RI) (@S01_BaseRing.lim_unique RI)
  (@S01_BaseRing.cauchy_complete RI).

(* ===================================================================== *)
(* 装配桥 B2：受体定义出节 arity 桥（δ 闭合）                              *)
(* ===================================================================== *)
Theorem tsi_twp_is_boltzmann_weight :
  forall (RI : RealInterfaceEnhanced) (Token : Set)
         (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI)
         (t : @S01_BaseRing.R RI)
         (Ht : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) t)
         (prefix : list Token) (w : Token),
    Id (@temperature_weighted_prob RI Token neg_log_prob t Ht prefix w)
       (@S01_BaseRing.exp_neg RI
          (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht)
             (neg_log_prob prefix w))).
Proof. intros RI Token neg_log_prob t Ht prefix w. exact (@id_refl _ _). Qed.

(* ===================================================================== *)
(* 主件节：受体 LanguageModelExtensions 节面（RI Token neg_log_prob        *)
(*   temperature temperature_pos）⊕ 供体 ReqAttnGibbs 节求和机器槽。      *)
(* ===================================================================== *)
Section TsiMains.
Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI.
Variable temperature : @S01_BaseRing.R RI.
Variable temperature_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) temperature.

(* 求和机器诚实槽（供体节同款；BoltzmannBridgeDischarge 供给槽先例） *)
Variable sumf : (Token -> @S01_BaseRing.R RI) -> @S01_BaseRing.R RI.
Hypothesis Hsum_ext :
  forall f g : Token -> @S01_BaseRing.R RI,
    (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Hypothesis Hsum_linear :
  forall (a : @S01_BaseRing.R RI) (f : Token -> @S01_BaseRing.R RI),
    req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Hypothesis Hsum_add :
  forall f g : Token -> @S01_BaseRing.R RI,
    req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Hypothesis Hsum_pos :
  forall f : Token -> @S01_BaseRing.R RI,
    (forall w : Token, lt zero (f w)) -> lt zero (sumf f).

(* 主件 1【归一性】受体温度加权概率的归一化分布权重和 = 1                *)
(*   （供体 ag_softmax_temp_normalized@262 全参实例化；z := nlp prefix·） *)
Theorem tsi_temp_weighted_normalized :
  forall prefix : list Token,
    req (sumf (fun w : Token =>
           mult (@temperature_weighted_prob RI Token neg_log_prob
                   temperature temperature_pos prefix w)
                (inv_pos
                   (sumf (fun w0 : Token =>
                            @temperature_weighted_prob RI Token neg_log_prob
                              temperature temperature_pos prefix w0))
                   (Hsum_pos
                      (fun w0 : Token =>
                         @temperature_weighted_prob RI Token neg_log_prob
                           temperature temperature_pos prefix w0)
                      (fun w0 : Token =>
                         @S01_BaseRing.exp_neg_pos RI
                           (@S01_BaseRing.mult RI
                              (@S01_BaseRing.inv_pos RI temperature temperature_pos)
                              (neg_log_prob prefix w0)))))))
        one.
Proof.
  intro prefix.
  exact (@ag_softmax_temp_normalized (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_ext Hsum_linear Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob prefix w)).
Qed.

(* 主件 2【混合归一】两 prefix 预测分布的凸组合（alpha ⊕ (1−alpha)）     *)
(*   仍归一（供体 ag_softmax_temp_mix_normalized@282 全参实例化）         *)
Theorem tsi_temp_weighted_mix_normalized :
  forall (p q : list Token) (alpha : @S01_BaseRing.R RI),
    lt zero alpha -> lt zero (req_minus one alpha) ->
    req (sumf (fun w : Token =>
           plus (mult alpha
                      (mult (@temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos p w)
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        @temperature_weighted_prob RI Token
                                          neg_log_prob temperature temperature_pos
                                          p w0))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     @temperature_weighted_prob RI Token
                                       neg_log_prob temperature temperature_pos
                                       p w0)
                                  (fun w0 : Token =>
                                     @S01_BaseRing.exp_neg_pos RI
                                       (@S01_BaseRing.mult RI
                                          (@S01_BaseRing.inv_pos RI temperature
                                             temperature_pos)
                                          (neg_log_prob p w0)))))))
                (mult (req_minus one alpha)
                      (mult (@temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos q w)
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        @temperature_weighted_prob RI Token
                                          neg_log_prob temperature temperature_pos
                                          q w0))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     @temperature_weighted_prob RI Token
                                       neg_log_prob temperature temperature_pos
                                       q w0)
                                  (fun w0 : Token =>
                                     @S01_BaseRing.exp_neg_pos RI
                                       (@S01_BaseRing.mult RI
                                          (@S01_BaseRing.inv_pos RI temperature
                                             temperature_pos)
                                          (neg_log_prob q w0)))))))))
        one.
Proof.
  intros p q alpha Halpha Halpha1.
  exact (@ag_softmax_temp_mix_normalized (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_ext Hsum_linear Hsum_add Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob p w)           (fun w : Token => neg_log_prob q w)           alpha Halpha Halpha1).
Qed.

(* 主件 3【温度-尺度对偶】受体温度 c 加权概率的归一化分布 =               *)
(*   1/c 尺度 softmax（供体 ag_temp_is_scale_duality@477 全参实例化；     *)
(*   LHS = 受体定义在温度 c 处（inv_pos c Hc 即进入指数），对偶不过深、   *)
(*   不砍）                                                               *)
Theorem tsi_temp_scale_duality :
  forall (c : @S01_BaseRing.R RI) (Hc : lt zero c)
         (prefix : list Token) (w : Token),
    req (mult (@temperature_weighted_prob RI Token neg_log_prob c Hc prefix w)
              (inv_pos
                 (sumf (fun w0 : Token =>
                          @temperature_weighted_prob RI Token neg_log_prob
                            c Hc prefix w0))
                 (Hsum_pos
                    (fun w0 : Token =>
                       @temperature_weighted_prob RI Token neg_log_prob
                         c Hc prefix w0)
                    (fun w0 : Token =>
                       @S01_BaseRing.exp_neg_pos RI
                         (@S01_BaseRing.mult RI
                            (@S01_BaseRing.inv_pos RI c Hc)
                            (neg_log_prob prefix w0))))))
        (reqd_softmax_scaled Token sumf Hsum_pos (inv_pos c Hc)
           (fun w1 : Token => neg_log_prob prefix w1) w).
Proof.
  intros c Hc prefix w.
  exact (@ag_temp_is_scale_duality (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_pos c Hc           (fun w1 : Token => neg_log_prob prefix w1) w).
Qed.

(* 主件 4【相对形式】同 prefix 内两 token 归一化权重之 Boltzmann 相对式   *)
(*   （供体 ag_softmax_temp_relative@341 全参实例化；exp 加法同态真证面） *)
Theorem tsi_temp_weighted_relative :
  forall (prefix : list Token) (w w' : Token),
    req (mult (@temperature_weighted_prob RI Token neg_log_prob
                   temperature temperature_pos prefix w)
              (inv_pos
                 (sumf (fun w0 : Token =>
                          @temperature_weighted_prob RI Token neg_log_prob
                            temperature temperature_pos prefix w0))
                 (Hsum_pos
                    (fun w0 : Token =>
                       @temperature_weighted_prob RI Token neg_log_prob
                         temperature temperature_pos prefix w0)
                    (fun w0 : Token =>
                       @S01_BaseRing.exp_neg_pos RI
                         (@S01_BaseRing.mult RI
                            (@S01_BaseRing.inv_pos RI temperature temperature_pos)
                            (neg_log_prob prefix w0))))))
        (mult (mult (@temperature_weighted_prob RI Token neg_log_prob
                       temperature temperature_pos prefix w')
                    (inv_pos
                       (sumf (fun w0 : Token =>
                                @temperature_weighted_prob RI Token neg_log_prob
                                  temperature temperature_pos prefix w0))
                       (Hsum_pos
                          (fun w0 : Token =>
                             @temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos prefix w0)
                          (fun w0 : Token =>
                             @S01_BaseRing.exp_neg_pos RI
                               (@S01_BaseRing.mult RI
                                  (@S01_BaseRing.inv_pos RI temperature
                                     temperature_pos)
                                  (neg_log_prob prefix w0))))))
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (neg_log_prob prefix w)
                                        (neg_log_prob prefix w'))))).
Proof.
  intros prefix w w'.
  exact (@ag_softmax_temp_relative (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_pos temperature temperature_pos           (fun w1 : Token => neg_log_prob prefix w1) w w').
Qed.

End TsiMains.

(* ===================================================================== *)
(* G4 审查留痕面（Print Assumptions ≥1 达标：5 处）                        *)
(* ===================================================================== *)
Print Assumptions tsi_twp_is_boltzmann_weight.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_relative.

Print Assumptions tsi_temp_weighted_relative.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_rie_setoid.
