(* ============================================================ *)
(* UpAblB2_G13.v —— 深施工席 B2：b_gibbs×3 等号面真重施工（T13c 移交件）   *)
(* 辖区（现档坐标·与 T13c 已立件槽位不重叠——本件独立新名 uabB2_*）：        *)
(*   位1 UpSigMigrate2.v:913 b_gibbs_pos     （ReqAlignCore 诚实桥）        *)
(*   位2 UpSigMigrate2.v:916 b_gibbs_sum_eps （ReqAlignCore 诚实桥）        *)
(*   位3 UpSigMigrate2.v:921 b_gibbs_eq      （ReqAlignCore 诚实桥·等号面）  *)
(* 真重施工三步（逐位裁决落件）：                                           *)
(*   一、抽象载体全参出节形独立复验：位1 六槽／位2 六槽+eps／位3 七槽        *)
(*      （ext/add/linear/〔le〕/znn/log-inv/log-le/〔log-eq〕逐槽显式在列，  *)
(*       req_gibbs_inequality@UpReqDist:2128 / req_gibbs_equality@:2154     *)
(*       全参直喂一步收口——kl_a≡req_relative_entropy 定义展开同一）。        *)
(*   二、两点 Real 世界（S:=bool，sumf:=hzlogd_aud_sum@G08:717）供给件真重： *)
(*      T13c 未立之 znn 槽（零和非负消去）与 log-inv 槽（kl_log_inv@        *)
(*      UpStepKL:583 δ 桥）两个具体面本席新建——等号面七槽中五槽由此在       *)
(*      具体载体落成（ext/add/linear 消费 hzlogd_sum2_*@G08，znn/log-inv    *)
(*      本席新建），残差收窄到 {log-le, log-eq} 恰为 W4 墙本体。             *)
(*   三、残差隔离定理（真重施工主件）：位1/位2 在两点 Real 世界仅剩 log-le   *)
(*      单槽、位3 仅剩 {log-le, log-eq} 双槽即可放电——b_gibbs×3 真欠账      *)
(*      被定理级收窄为 W4 墙对，零隐藏槽。                                  *)
(* W4 墙邻接裁决（如实登记，接 T13c O2 维持）：                             *)
(*   RealEnhancedReal 实例 le 字段 := real_le（Or 编码）；B 形引擎          *)
(*   real_log_le_linear_B@UpRealLeB:543 输出 Bishop 序 real_le_b，逆向桥    *)
(*   real_le_b→real_le 为 Or 形精确闭合=等号点 x=1 分支判定（LPO 族），     *)
(*   构造性不可证（G08 头注+UpRealLeB 尾注在案）——log-le 槽在具体载体       *)
(*   plain-le 形不可实例化，逐 eps 形（log_le_linear_eps 接口字段）与 B 形   *)
(*   在库为墙邻接在证；log-eq 槽需严格凹性定量机（x≠1 间隙），全库无此件，   *)
(*   等号面真欠账=W4 邻接挂账维持，不降档不隐藏。                           *)
(* 分级（fail-loud 如实）：                                                 *)
(*   位1/位2 抽象全参形+两点残差形 = 条件 discharge（W4 单槽残差随件显式）； *)
(*   位3 抽象全参形 = 条件 discharge；两点残差形双层申报：七槽形（log-eq     *)
(*   槽显式携带）与定谳形（log-eq 槽由 t34 具体实例喂入，残差仅 log-le       *)
(*   单槽——载体分层精化：抽象载体墙维持，Regular-Real 载体 log-eq 非墙）；  *)
(*   znn/log-inv 两供给件 = N3（实例供给）；B 形无槽面（gibbsd 双路在库）    *)
(*   为 pos 面独立可达路线 witness，eq 面无此面（如实缺席）。               *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqAlgebra、      *)
(*   UpReqDist、UpSigMigrate2、UpStepKL、UpRealLeB、S08_RealMainlineDPO、    *)
(*   G08_Gibbs。                                                           *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblB2_*                            *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpSigMigrate2.
Require Import UpStepKL.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import G08_Gibbs.
Require Import UpReqCEqDispersion.
Import RealInterfaceEnhancedMod.

(* ======== 一、抽象载体全参出节形（位1/位2/位3 独立复验+槽位对账定谳） ====== *)
Section UabB2Abs.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- 位1 ←:913（全参六槽：ext/add/linear/le/log-inv/log-le 逐槽显式） ---- *)
Theorem uabB2_bgibbs_pos_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (kl_a S sumf p q Hp Hq).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality R RIS S sumf Hext Hadd Hlin Hle Hloginv Hlogle
                               p q Hp Hq Hnp Hnq).
Qed.

(* ---- 位2 ←:916（位1+le_plus_compat 链，零新增槽） ---------------------- *)
Theorem uabB2_bgibbs_sum_eps_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q)
         (eps : R) (Heps : lt zero eps),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (plus (kl_a S sumf p q Hp Hq) eps).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps (plus (kl_a S sumf p q Hp Hq) eps)
                    (lt_le_iff zero eps (inl Heps))
                    (le_id_l eps (plus zero eps)
                               (plus (kl_a S sumf p q Hp Hq) eps)
                               (req_sym (plus zero eps) eps
                                          (req_trans (plus zero eps) (plus eps zero) eps
                                                     (plus_comm zero eps)
                                                     (plus_zero eps)))
                               (le_plus_compat zero (kl_a S sumf p q Hp Hq)
                                               eps eps
                                               (uabB2_bgibbs_pos_full S sumf Hext Hadd
                                                                      Hlin Hle Hloginv Hlogle
                                                                      p q Hp Hq Hnp Hnq)
                                               (le_refl eps)))).
Qed.

(* ---- 位3 ←:921（等号面本体：全参七槽，znn/log-eq 两槽显式在列；         *)
(*        log-le/log-eq = W4 墙本体残差，随件显式携带不隐藏） -------------- *)
Theorem uabB2_bgibbs_eq_full :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hext : forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R) (f : S -> R),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hznn : forall f : S -> R,
                   (forall s : S, le zero (f s)) -> req (sumf f) zero ->
                   forall s : S, req (f s) zero)
         (Hloginv : forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : R) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : S -> R) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    req (kl_a S sumf p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality R RIS S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq
                             p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== 二、两点世界抽象供给件（B2 新建：znn 槽任意载体构造） ========== *)
(* 两点和：与 G08 hzlogd_aud_sum 同形（δ 展开同一 plus (f true) (f false)） *)
Definition uabB2_t2sum (f : bool -> R) : R := plus (f true) (f false).

Lemma uabB2_opp_zero : req (opp zero) zero.
Proof.
  apply (req_trans (opp zero) (plus zero (opp zero)) zero).
  - apply (req_trans (opp zero) (plus (opp zero) zero) (plus zero (opp zero))).
    + apply (req_sym (plus (opp zero) zero) (opp zero)).
      apply plus_zero.
    + apply plus_comm.
  - apply plus_opp.
Qed.

(* znn 槽（零和非负消去）任意载体两点构造——T13c 未立之槽，本席新建：        *)
(*   逐点非负 + 两点和为零 ⟹ 逐点为零（le_antisym+左消去纯代数链）。        *)
Lemma uabB2_znn_abs :
  forall f : bool -> R,
    (forall s : bool, le zero (f s)) ->
    req (uabB2_t2sum f) zero ->
    forall s : bool, req (f s) zero.
Proof.
  intros f Hpos Hsum.
  assert (D : req (plus (opp (f false)) (f false)) zero).
  { apply (req_trans (plus (opp (f false)) (f false))
                     (plus (f false) (opp (f false))) zero).
    - apply plus_comm.
    - apply plus_opp. }
  assert (E : req (plus (f true) (f false)) (plus (opp (f false)) (f false))).
  { apply (req_trans (plus (f true) (f false)) zero (plus (opp (f false)) (f false))).
    - exact Hsum.
    - apply (req_sym (plus (opp (f false)) (f false)) zero).
      exact D. }
  assert (Htf : req (f true) (opp (f false))).
  { apply (req_plus_cancel_l (f false) (f true) (opp (f false))).
    apply (req_trans (plus (f false) (f true))
                     (plus (f true) (f false))
                     (plus (f false) (opp (f false)))).
    - apply plus_comm.
    - apply (req_trans (plus (f true) (f false))
                       (plus (opp (f false)) (f false))
                       (plus (f false) (opp (f false)))).
      + exact E.
      + apply plus_comm. }
  assert (Ht0 : req (f true) zero).
  { apply (le_antisym (f true) zero).
    - apply (le_trans (f true) (opp (f false)) zero).
      + apply (le_id_r (f true) (f true) (opp (f false)) Htf (le_refl (f true))).
      + apply (le_id_r (opp (f false)) (opp zero) zero uabB2_opp_zero).
        apply (opp_le_compat zero (f false) (Hpos false)).
    - exact (Hpos true). }
  intro s. destruct s.
  - exact Ht0.
  - assert (F : req (plus zero (f false)) zero).
    { apply (req_trans (plus zero (f false))
                       (plus (f true) (f false)) zero).
      - apply (req_sym (plus (f true) (f false)) (plus zero (f false))).
        apply (req_plus_compat (f true) zero (f false) (f false) Ht0 (req_refl (f false))).
      - exact Hsum. }
    apply (req_trans (f false) (plus (f false) zero) zero).
    + apply (req_sym (plus (f false) zero) (f false)).
      apply plus_zero.
    + apply (req_trans (plus (f false) zero) (plus zero (f false)) zero).
      * apply plus_comm.
      * exact F.
Qed.

End UabB2Abs.

(* ======== 三、两点 Real 世界具体供给件（log-inv 槽 δ 桥） ================ *)
(* log-inv 槽具体落成：kl_log_inv@UpStepKL:583 经接口投影 δ 桥一次收口      *)
(*   （req:=real_eq、log→real_log→cw_log、inv_pos→real_inv_pos 全展开）。   *)
Lemma uabB2_loginv_real :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (kl_log_inv x Hx Hi).
Qed.

(* ======== 四、残差隔离定理（真重施工主件：真欠账=W4 墙对的定理级收窄） === *)
(* 两点 Real 世界：S:=bool、sumf:=hzlogd_aud_sum@G08:717；                  *)
(*   五槽供给位：ext/add/linear/le = hzlogd_sum2_*@G08（消费），             *)
(*               znn = uabB2_znn_abs（δ 同形喂入），log-inv = 本席桥件。     *)
(* 位1 残差 = {log-le} 单槽 ------------------------------------------------ *)
Theorem uabB2_bgibbs_pos_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    le zero (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq).
Proof.
  intros Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality Real RealEnhancedReal bool hzlogd_aud_sum
             hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear hzlogd_sum2_le
             uabB2_loginv_real Hlogle p q Hp Hq Hnp Hnq).
Qed.

(* 位2 残差 = {log-le} 单槽 ------------------------------------------------ *)
Theorem uabB2_bgibbs_sumeps_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q)
         (eps : Real) (Heps : lt zero eps),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    le zero (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) eps).
Proof.
  intros Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps
                    (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) eps)
                    (lt_le_iff zero eps (inl Heps))
                    (le_id_l eps (plus zero eps)
                               (plus (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq)
                                     eps)
                               (req_sym (plus zero eps) eps
                                          (req_trans (plus zero eps) (plus eps zero) eps
                                                     (plus_comm zero eps)
                                                     (plus_zero eps)))
                               (le_plus_compat zero
                                 (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq)
                                 eps eps
                                 (uabB2_bgibbs_pos_resW4 Hlogle p q Hp Hq Hnp Hnq)
                                 (le_refl eps)))).
Qed.

(* 位3 残差 = {log-le, log-eq} 双槽（等号面真欠账恰为 W4 墙对） ------------- *)
Theorem uabB2_bgibbs_eq_resW4 :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : Real) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    req (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) zero ->
    forall s : bool, req (p s) (q s).
Proof.
  intros Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality Real RealEnhancedReal bool hzlogd_aud_sum
             hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear
             uabB2_znn_abs uabB2_loginv_real Hlogle Hlogeq
             p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== 四·b、等号面残差再收窄（深施工定谳件）：log-eq 槽在具体载体       *)
(*   可实例化——t34_log_eq_linear_weak@UpReqCEqDispersion:80（real_weak_     *)
(*   trich 双否形驱动，直觉主义有效、PA 全 Closed）恰为本槽 Real 实例，      *)
(*   喂入后等号面两点残差自 {log-le, log-eq} 收窄至 {log-le} 单槽——         *)
(*   T13c O2「W4 墙对」判词按载体分层精化：抽象载体（接口无三分/比较字段）   *)
(*   维持墙；具体 Regular-Real 载体 log-eq 非墙（本件定理级实证）。--------- *)
Theorem uabB2_bgibbs_eq_res_logle_only :
  forall (Hlogle : forall (x : Real) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : bool -> Real) (Hp : pdist_a bool p) (Hq : pdist_a bool q),
    nrm_a bool hzlogd_aud_sum p -> nrm_a bool hzlogd_aud_sum q ->
    req (@kl_a Real RealEnhancedReal bool hzlogd_aud_sum p q Hp Hq) zero ->
    forall s : bool, req (p s) (q s).
Proof.
  intros Hlogle p q Hp Hq Hnp Hnq Hkl0.
  exact (uabB2_bgibbs_eq_resW4 Hlogle t34_log_eq_linear_weak p q Hp Hq Hnp Hnq Hkl0).
Qed.

(* ======== 五、pos 面无槽替代 witness（B 形双路在库，逐 eps/切线双证） ===== *)
(* gibbsd_gibbs_inequality@G08:432：0 ≤_B 有限和 KL（Bishop 序），零槽——    *)
(*   pos 面在 B 形序上的无条件替代为独立可达路线（序异向=墙邻接机理在案）。   *)
(*   eq 面无此替代面（全库无 B 形/任意形 gibbs_eq 放电件，如实缺席）。 ------ *)
Theorem uabB2_gibbs_pos_Bform_list :
  forall (l : list bool) (p q : bool -> Real)
         (Hp : forall s : bool, lt zero (p s)) (Hq : forall s : bool, lt zero (q s))
         (Hnormp : req (real_list_sum bool p l) one)
         (Hnormq : req (real_list_sum bool q l) one),
    real_le_b zero
      (real_list_sum bool (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros l p q Hp Hq Hnormp Hnormq.
  exact (gibbsd_gibbs_inequality bool l p q Hp Hq Hnormp Hnormq).
Qed.

(* ======== 文尾 PA（全数 Closed 判读） ==================================== *)
Print Assumptions uabB2_bgibbs_pos_full.
Print Assumptions uabB2_bgibbs_sum_eps_full.
Print Assumptions uabB2_bgibbs_eq_full.
Print Assumptions uabB2_znn_abs.
Print Assumptions uabB2_loginv_real.
Print Assumptions uabB2_bgibbs_pos_resW4.
Print Assumptions uabB2_bgibbs_sumeps_resW4.
Print Assumptions uabB2_bgibbs_eq_resW4.
Print Assumptions uabB2_bgibbs_eq_res_logle_only.
Print Assumptions uabB2_gibbs_pos_Bform_list.
