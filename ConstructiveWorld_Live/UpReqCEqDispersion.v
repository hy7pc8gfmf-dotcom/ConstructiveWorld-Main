(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqCEqDispersion.v *)
(* *)
(* 目的： CDispersion S 档等号槽的严格化（三件）。 *)
(* 主件： t34_log_eq_linear_weak 弱对数线性、t34_s6_w2_gibbs_eq 等号槽严格化。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqKLSTangent、G05_LogSmall、UpReqAlgebra、UpReqU2。 *)
(* 备注： 承前件头注诚实边界：等号槽需 log_eq_linear 强形，取弱形加严格化腿的可达组合。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqCEqDispersion.v —— ：CDispersion S         *)
(*   ； 头注诚实边界（UpReqCDispersion.v L26-28）：        *)
(*   「s6 w2_gibbs_eq / req_u2_fixed_point_unique 等还吃 log_le_linear /  *)

(*   T1 结果之前；A3 候选 A-3 判：T1 已建「切点⟹一」件，等号条件位      *)

(* ------------------------------------------------------------------ *)

(*   1. eq 槽定位：UpReqU2.v Section ReqU2FixedPoint L313-316 两个出口桥槽：*)
(*      log_le_linear : forall x Hx, le (log x Hx) (req_minus x one)      *)
(*      log_eq_linear : forall x Hx, req (log x Hx) (req_minus x one)     *)
(*                                    -> req x one                       *)
(*      使用位 = w2_gibbs_eq（L477，经 UpReqDist.req_gibbs_equality 出口   *)
(*      组装输入）与 req_u2_fixed_point_unique（L739，经 w2_gibbs_eq 间接）.*)


(*         (real_plus u (real_opp real_one)) -> real_eq u real_one        *)

(*         req_minus a b:=plus a (opp b)，δ 透明）——T1                *)

(*         同形。T1 链：real_weak_trich（S07:5710 弱三分，直觉主义有效）    *)
(*         + klst_log_tangent_neg/pos 双支 + real_lt_compat + 非自反收紧； *)
(*         弱于强三分/LPO 形，不可证旧判只封强形、不封此弱形。             *)
(*      b. log_le_linear 槽 Real 形 = real_le (Or 编码，S02:460) ——        *)
(*         逐 eps 形（S07 real_log_le_linear_eps / UpRealLeB              *)
(*         real_log_le_linear_B）到 Or 编码的逆向桥构造性不可证（登记表      *)

(*   3. 供给（全部上游在盘，vo 树今日全部通过）：                              *)
(*      B1 logd_log_compat_real      ——compat 槽 Real 闭合（ 同喂）     *)
(*      B4 logd_log_inv_exp_neg_real ——inv_exp_neg 槽 Real 闭合（ 同喂）*)

(*      sum 面（sum_ext/add/linear/pos/zero_nonneg）与 le 面槽、KL>=0 面    *)
(*      槽：接口型参数位（ 实测 raw→接口重述在提取层生成运行型转换残留， *)
(*      自段口径不 ship；载体与满足证上游在盘，接口形补上即全 Concrete）。  *)

(*   [桥接引理] t34_log_eq_linear_weak —— t1 切点⟹一件的接口形重曝：           *)

(*   [使用位 1] t34_s6_w2_gibbs_eq —— w2_gibbs_eq Real 实例化              *)
(*          （eq 槽喂桥接引理；le 槽诚实参数位；compat 槽喂 B1）；              *)
(*   [使用位 2] t34_s6_req_u2_fixed_point_unique —— U2 唯一性件 Real       *)
(*          实例化（w2_gibbs_eq 下游；eq 槽同喂；inv_exp_neg 槽喂 B4；      *)
(*          sum 面/KL>=0 面/le 面槽诚实参数位）。                          *)
(* 至此 s6 位三桥槽中 eq 槽（等号条件件）实现 Real 层无条件消解；            *)

(* 红线自查：无假设声明件（语句面全使用位假设参数）、无未闭合证明收尾、      *)
(*   无经典回溯导入；Set 层零 Prop 泄露（结论全 req/lt/le 接口 Set 值）；    *)
(*   全 Qed 闭合；既有文件零改；零 git；新名 t34_ 前缀（全库检索零命中）。   *)



(* ============================================================ *)

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
Require Import UpReqKLSTangent.
Require Import G05_LogSmall.
Require Import UpReqAlgebra.
Require Import UpReqU2.

Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part A：桥接引理——「切点⟹一」的 eq 槽接口形重曝                             *)
(*   槽形（UpReqU2 L315-316 出节形）：                                     *)
(*     forall x Hx, req (log x Hx) (req_minus x one) -> req x one          *)


(*   (opp b)），桥接引理零重证、零新假设。                                     *)
(* ============================================================ *)

Lemma t34_log_eq_linear_weak : forall (u : Real) (Hu : lt zero u),
  req (log u Hu) (req_minus u one) -> req u one.
Proof.
  intros u Hu Heqlin.
  exact (t1_log_eq_linear_inject u Hu Heqlin).
Qed.

(* ============================================================ *)
(* Part B：s6 位使用件 Real 实例化                                         *)
(*   签名照检验打表 post-End used-subset 转录（w2_gibbs_eq 不吃 sum_pos、   *)
(*   req_u2_fixed_point_unique 不吃 eta_le_one——出节已剪除）；              *)
(*   S 与 sumf 保持全称（比 bool 两点载体更强的 Real 层形）。               *)
(* ============================================================ *)

(* ---- 使用位 1：w2_gibbs_eq（UpReqU2 L477；普查 s6 ReqU2FixedPoint 位） ---- *)

Theorem t34_s6_w2_gibbs_eq :
  forall (S : Set) (sumf : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
  (forall f g : S -> Real,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))) ->
  (forall (a : Real) (f : S -> Real),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f))) ->
  (forall f : S -> Real,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero) ->
  (* log_le_linear 槽：plain-le Or 编码逆向桥不可及——诚实接口参数位 *)
  (forall (x : Real) (Hx : lt zero x),
    le (log x Hx) (req_minus x one)) ->
  forall (p q : S -> Real)
    (Hp : @UpReqU2.pos3 Real RealEnhancedReal S p)
    (Hq : @UpReqU2.pos3 Real RealEnhancedReal S q),
    @UpReqU2.nrm Real RealEnhancedReal S sumf p ->
    @UpReqU2.nrm Real RealEnhancedReal S sumf q ->
    req (@UpReqU2.KLE Real RealEnhancedReal S sumf p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros S sumf sum_ext sum_add sum_linear sum_zero_nonneg
         log_le_linear p q Hp Hq Hnp Hnq Hkl0 s.
  exact (@UpReqU2.w2_gibbs_eq Real RealEnhancedReal S sumf
           sum_ext sum_add sum_linear sum_zero_nonneg
           logd_log_compat_real
           log_le_linear
           t34_log_eq_linear_weak
           p q Hp Hq Hnp Hnq Hkl0 s).
Qed.

(* ---- 使用位 2：req_u2_fixed_point_unique（UpReqU2 L739；w2_gibbs_eq ---- *)
(*      下游——pi_t 不动点唯一性 ⟹ pi_t == PSTR 逐点） -------------------- *)

Theorem t34_s6_req_u2_fixed_point_unique :
  forall (S : Set) (sumf : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
  (forall f g : S -> Real,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))) ->
  (forall (a : Real) (f : S -> Real),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f))) ->
  forall (sum_pos : forall f : S -> Real,
            (forall s : S, lt zero (f s)) -> lt zero (sumf f)),
  (forall f : S -> Real,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero) ->
  
  (forall x : Real,
    req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
  (forall (x : Real) (Hx : lt zero x),
    le (log x Hx) (req_minus x one)) ->
  forall (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
    (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
    (eta : Real) (eta_pos : lt zero eta)
    (ZAL_pos : lt zero (@UpReqU2.ZAL Real RealEnhancedReal S sumf
                          reward beta beta_pos pi_ref))
    (req2_gibbs_inequality : forall (p q : S -> Real)
                               (Hp : @UpReqU2.pos3 Real RealEnhancedReal S p)
                               (Hq : @UpReqU2.pos3 Real RealEnhancedReal S q),
                             le zero (@UpReqU2.KLE Real RealEnhancedReal S sumf
                                        p q Hp Hq))
    (pi_t : S -> Real) (Hpi_t : @UpReqU2.pos3 Real RealEnhancedReal S pi_t),
    @UpReqU2.nrm Real RealEnhancedReal S sumf pi_t ->
    (forall s : S,
      req (@UpReqU2.NPX Real RealEnhancedReal S sumf sum_pos reward beta
             beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t s)
           (pi_t s)) ->
    forall s : S,
      req (pi_t s)
          (@UpReqU2.PSTR Real RealEnhancedReal S sumf reward beta beta_pos
             pi_ref ZAL_pos s).
Proof.
  intros S sumf sum_ext sum_add sum_linear sum_pos sum_zero_nonneg
         log_inv_exp_neg_req log_le_linear
         reward beta beta_pos pi_ref pi_ref_pos eta eta_pos
         ZAL_pos req2_gibbs_inequality pi_t Hpi_t Hn Hfix s.
  exact (@UpReqU2.req_u2_fixed_point_unique Real RealEnhancedReal S sumf
           sum_ext sum_add sum_linear sum_pos sum_zero_nonneg
           logd_log_compat_real
           logd_log_inv_exp_neg_real
           log_le_linear
           t34_log_eq_linear_weak
           reward beta beta_pos pi_ref pi_ref_pos eta eta_pos
           ZAL_pos req2_gibbs_inequality pi_t Hpi_t Hn Hfix s).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零外假设见证）                              *)
(* ============================================================ *)
Print Assumptions t34_log_eq_linear_weak.
Print Assumptions t34_s6_w2_gibbs_eq.
Print Assumptions t34_s6_req_u2_fixed_point_unique.
