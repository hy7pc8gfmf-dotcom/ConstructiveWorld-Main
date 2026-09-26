(* ============================================================ *)
(* UpAblT13c_UpSigMigrate2.v —— 消融清欠席 T13c（批9）b_gibbs 三位出节件      *)
(* 辖区（T13a-2/T13b D3 深施工单列移交·现档坐标）：                           *)
(*   位1 UpSigMigrate2.v:913 b_gibbs_pos     （ReqAlignCore）                 *)
(*   位2 UpSigMigrate2.v:916 b_gibbs_sum_eps （ReqAlignCore）                 *)
(*   位3 UpSigMigrate2.v:921 b_gibbs_eq      （ReqAlignCore）                 *)
(* 出节 discharge 形（诚实申报）：asum 三槽世界缺 le/pos 面与 log 桥面——      *)
(*   逐槽显式参兑现：                                                         *)
(*   位1 ← req_gibbs_inequality@UpReqDist:2128 全参直喂（槽=ext/add/linear/   *)
(*        sum-le/log-inv/log-le-linear 六件；kl_a≡req_relative_entropy、      *)
(*        pdist_a≡reqd_positive_dist、nrm_a≡reqd_normalized 定义展开同一）；   *)
(*   位2 ← 位1 + le_plus_compat 链（零新增槽）；                              *)
(*   位3 ← req_gibbs_equality@UpReqDist:2154 全参直喂（另带 zero-nonneg 与    *)
(*        log-eq-linear 槽）。                                                *)
(* 槽位可满足性分级（防注水）：sum-le 槽在 Real 载体可实例化                  *)
(*   （real_list_sum_le@S08:432 先例）；log 三槽=T2① 接口桥/W4 族——           *)
(*   log-le-linear 与 log-eq-linear 为 W4 墙本体（普查 §3-W4），任何具体       *)
(*   载体不可实例化：位1/位3 为条件 discharge（W4 族槽随件显式携带），         *)
(*   等号面真欠账=W4 邻接挂账，如实登记不降档。位2 的逐 eps 形另有 Real 层     *)
(*   real_gibbs_inequality_eps 绕法（R3）为独立可达路线。                     *)
(* 分级：位1/位3 = 条件 discharge（出节形·W4 族槽携带）；位2 = N3（位1 链）。  *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、        *)
(*   UpReqDist、UpSigMigrate2。                                               *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblT13c_*                            *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

Section UabT13cGibbs.

Context {R0 : Set} {RIS0 : RealInterfaceEnhancedSetoid R0}.

(* ---- 位1 ←:913（b_gibbs_pos 出节 discharge：六槽显式参，母本全参直喂） ---- *)
Theorem uabT13c_bgibbs_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R0, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (@kl_a R0 RIS0 S sumf p q Hp Hq).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality R0 RIS0 S sumf Hext Hadd Hlin Hle Hloginv Hlogle
                               p q Hp Hq Hnp Hnq).
Qed.

(* ---- 位2 ←:916（b_gibbs_sum_eps：位1+le_plus_compat 链，零新增槽） ------- *)
Theorem uabT13c_bgibbs_sum_eps :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R0, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q)
         (eps : R0) (Heps : lt zero eps),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps)
                    (lt_le_iff zero eps (inl Heps))
                    (le_id_l eps (plus zero eps)
                               (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps)
                               (req_sym (plus zero eps) eps
                                          (req_trans (plus zero eps) (plus eps zero) eps
                                                     (plus_comm zero eps) (plus_zero eps)))
                               (le_plus_compat zero (@kl_a R0 RIS0 S sumf p q Hp Hq)
                                               eps eps
                                               (uabT13c_bgibbs_pos S sumf Hext Hadd Hlin Hle
                                                                   Hloginv Hlogle p q Hp Hq Hnp Hnq)
                                               (le_refl eps)))).
Qed.

(* ---- 位3 ←:921（b_gibbs_eq 条件 discharge：八槽显式参，母本全参直喂；     *)
(*        log-eq-linear 槽=W4 墙本体，任何具体载体不可实例化，等号面真欠账    *)
(*        如实随件携带不隐藏） ---- *)
Theorem uabT13c_bgibbs_eq :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hznn : forall f : S -> R0,
                   (forall s : S, le zero (f s)) -> req (sumf f) zero ->
                   forall s : S, req (f s) zero)
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : R0) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    req (@kl_a R0 RIS0 S sumf p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality R0 RIS0 S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq
                             p q Hp Hq Hnp Hnq Hkl0).
Qed.

End UabT13cGibbs.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13c_bgibbs_pos.
Print Assumptions uabT13c_bgibbs_sum_eps.
Print Assumptions uabT13c_bgibbs_eq.
