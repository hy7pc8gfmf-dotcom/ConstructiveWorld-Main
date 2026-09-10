(* ============================================================ *)
(* UpReqLogD.v —— 槽放电战役 G6：log 不等式族放电（S 族 17 槽）          *)
(*   广义旗舰链 G6 执行席，2026-09-10                                   *)
(* ------------------------------------------------------------------ *)
(* 引擎坐标实读（普查 G6 节 L85-101 + §四 L380 落点纪律执行记录）：      *)
(*   ① Real 层 B 形引擎（UpRealLeB）：real_log_le_linear_B@535 /        *)
(*      real_gibbs_inequality_B@592 / real_le_to_le_b@78 /              *)
(*      real_log_one_plus_le_B@543 / real_exp_ge_linear_B@526。         *)
(*   ② 根件（CW219 sed 实读）：real_log_le_linear_eps@41058（Or 形逐    *)
(*      eps，接口字段 log_le_linear_eps@41134 在案——E354 旧判词「接口  *)
(*      无此字段」勘误）/ real_log_lt_mono@39059（log 严格递增）/        *)
(*      real_log_mult@40403 / real_log_one / real_two_pos@41807 /       *)
(*      real_gibbs_inequality_eps@41704 / real_kl_term@41696 /          *)
(*      real_boltzmann_dist_r@43686（Section RealRLHFMain 出口）。       *)
(*   ③ G5 供给（UpReqLogPrimD）：logd_log_inv_one_inv_real（log(1/x)    *)
(*      ≡ −log x）——UpReqGibbsD 台账 E-GIBBSD-2 记名缺口件，本席到位。  *)
(*   ④ 桥核对（红线）：real_le_to_le_b@78 / latb_real_lt_to_le_b@87 /   *)
(*      real_lt_le_bridge@UpLogMono:16 全单向（real_le/lt → real_le_b）；*)
(*      逆向 real_le_b → real_le = Or 形精确收口，构造性不可证。req 层   *)
(*      Or 形无条件槽（log_le_linear 全字面形）据此不放电，改逐 eps /    *)
(*      le_b 语言交付（§380 纪律 fallback，落点=Real 实例化定理）。      *)
(* ------------------------------------------------------------------ *)
(* 交付（槽放电件 = 槽被引擎填充的具体实例，T2 模板 ② 形态）：            *)
(*   [槽族 1：log_le_linear / dist_log_le_linear 双形，5 槽位]           *)
(*    logd_log_le_linear_eps —— 逐 eps Or 形（req 槽语句最近可达形；     *)
(*      real_log_le_linear_eps 直喂）；                                  *)
(*    logd_log_le_linear_B —— le_b 形（real_log_le_linear_B 直喂）。     *)
(*   [槽族 2：log 严格单调三槽] logd_log_lt_mono_real（UpReqCauchy:819   *)
(*      log_lt_mono_cc / UpReqAlignRestA:80 ralt_log_lt_mono 字面形；    *)
(*      real_log_lt_mono 直喂）；logd_log_two_pos_real（UpPredRelaxReq:  *)
(*      221 字面形；1<2 平移 + real_log_lt_mono + real_log_one 组装）。  *)
(*   [槽族 3：KL 字面形桥——G6 旗舰] logd_kl_term_minus_form：            *)
(*      real_kl_term p q ≡ p·(log p − log q)（real_log_mult 分解 + G5    *)
(*      log 逆消去）；b_gibbs_pos/b_gibbs_sum_eps（UpSigMigrate2 kl_a    *)
(*      = Σ p·(log p − log q) 字面形）与 req2_gibbs_inequality 的 Real   *)
(*      实例化供给件：logd_list_sum_kl_minus_form /                      *)
(*      logd_gibbs_inequality_minus_B（0 ≤_B Σ 字面形）/                 *)
(*      logd_gibbs_inequality_minus_eps（0 ≤ Σ 字面形 + eps）。          *)
(*      勘误：UpReqGibbsD 台账 E-GIBBSD-2「log 逆消去 CW219 未备、       *)
(*      字面形桥接留待」——本席经 G5 件闭合，字面形全通。                 *)
(*   [槽族 4：real_gibbs_sum_eps@UpRealLeB:206 槽]                       *)
(*      logd_gibbs_sum_eps_boltzmann_list —— real_sum_over_S :=          *)
(*      real_list_sum 实例化填件（q := real_boltzmann_dist_r；供给槽     *)
(*      Hnormb=Σp_b==1 显式位——诚实条件放电，G5 logd_pos_of_agree 同型； *)
(*      real_rlhf_optimal_B 供给链到此闭合）。                           *)
(* 判词表（17 槽清偿/精确阻塞；逐槽明细见尾注对账）：                    *)
(*   放电（Real 实例化）：log_le_linear / dist_log_le_linear /           *)
(*    log_lt_mono_cc / ralt_log_lt_mono / log_two_pos / real_gibbs_sum_  *)
(*    eps（条件）= 6；字面形供给（gibbs 族补强）：b_gibbs_pos /           *)
(*    b_gibbs_sum_eps / req2_gibbs_inequality = 3。                       *)
(*   X 阻塞（等号情形，红线不越）：log_eq_linear / dist_log_eq_linear /   *)
(*    b_gibbs_eq / bridge_free_energy_min_unique = 4——需 log 严格凹性    *)
(*    收口（CW219 L41199 注记：需强三分/LPO，构造性不可证）。            *)
(*   S 阻塞（复合，供给链已明）：entropy_tangent（entropy_gradient 抽象   *)
(*    无 spec，N 参）/ req_energy_exp_temp_mono /                        *)
(*    req_energy_exp_temp_strict_mono（fw_et 温度复合，供给=req_entropy_ *)
(*    temp_explicit 槽本身 S 阻塞，G5 判词表）/ bridge_min_free_energy    *)
(*    （Real 实例化已在盘=real_rlhf_optimal_B@UpRealLeB:237，req Or 形    *)
(*    阻塞=序桥红线）= 4。                                               *)
(* 防撞：logd_ 前缀与 G5 UpReqLogPrimD 同族；本席 10 个新名 + 文件名     *)
(*    全库 grep 实测零命中（建前 2026-09-10 逐名实查）。                  *)
(* 红线：Set 层零 Prop（real_le/real_lt/real_eq/real_le_b 全 Set 值，    *)
(*    语句与证明零 Prop 泄露）；全 Qed 闭合；零公理；既有文件零改；      *)
(*    双形并存（le_b/逐 eps 双形 + kl_term/字面形双形）；零 git；        *)
(*    温控 guard 错峰（_sqp_guard.ps1，CoreN 绑核）。                     *)
(* 编译配方：_sqp_guard.ps1 温控包装                                     *)
(*   coqc -Q . "" UpReqLogD.v（单核绑核，零裸调）                        *)
(* G4：coqchk -Q . "" -Q "..\001" "" UpReqLogD（长窗，禁 -o）            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqGibbsD.
Require Import UpReqLogPrimD.
From Stdlib Require Import List.

(* ============================================================ *)
(* Part A：Bishop 序代数补件（gibbsd_le_b_id_l 的右端对偶件）            *)
(* ============================================================ *)

(* A1：Bishop 序右端 real_eq 换形（req 层 le_id_r 的 le_b 对位） *)
Lemma logd_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hab. unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat a a
           (real_plus b eps) (real_plus c eps)).
  - apply real_eq_refl.
  - exact (RealSetoid.real_eq_plus_compat b eps c eps Hab
             (real_eq_refl eps)).
  - exact (H eps Heps).
Qed.

(* ============================================================ *)
(* Part B：槽族 1——log_le_linear / dist_log_le_linear 双形放电          *)
(*   （UpReqU2:313 / UpReqFEPAttn:90 / UpReqDist:1029 /                 *)
(*     UpReqTempEntropy:60 / UpFirewallReq:101；req 层 Or 全字面形 =     *)
(*     逆向桥红线不越，本件为 §380 fallback 落点）                       *)
(* ============================================================ *)

(* B1：逐 eps Or 形（req 槽语句最近可达形；real_log_le_linear_eps        *)
(*     @CW219:41058 直喂——接口字段 log_le_linear_eps 的根件，E354 勘误） *)
Lemma logd_log_le_linear_eps : forall (x eps : Real)
    (Hx : real_lt real_zero x),
  real_lt real_zero eps ->
  real_le (real_log x Hx) (real_plus (real_plus x (real_opp real_one)) eps).
Proof.
  intros x eps Hx Heps.
  exact (RealInterfaceEnhancedMod.real_log_le_linear_eps x eps Hx Heps).
Qed.

(* B2：le_b 形（槽形语句 Bishop 序版；real_log_le_linear_B@UpRealLeB:535 *)
(*     直喂——与 B1 双形并存） *)
Lemma logd_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx.
  exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part C：槽族 2——log 严格单调三槽（log_lt_mono_cc /                   *)
(*   ralt_log_lt_mono / log_two_pos；real_log_lt_mono@CW219:39059 供给） *)
(* ============================================================ *)

(* C1：log 严格单调字面形（UpReqCauchy:819 / UpReqAlignRestA:80 槽形；   *)
(*     real_log_lt_mono 直喂；cw_log ≡ real_log delta 换形在 exact 内）  *)
Lemma logd_log_lt_mono_real : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (real_log_lt_mono a b Ha Hb Hlt).
Qed.

(* C2：log 2 > 0（UpPredRelaxReq:221 槽形字面直喂；2>0 见证位 =
     real_plus_positive one one one_pos one_pos 与槽逐位同形） *)
Lemma logd_log_two_pos_real :
  real_lt real_zero
    (real_log (real_plus real_one real_one)
       (real_plus_positive real_one real_one
          real_lt_zero_one real_lt_zero_one)).
Proof.
  apply (RealSetoid.real_lt_compat
           (real_log real_one real_lt_zero_one) real_zero
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))).
  - exact (real_log_one real_lt_zero_one).
  - apply real_eq_refl.
  - apply (real_log_lt_mono real_one (real_plus real_one real_one)
             real_lt_zero_one
             (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one)).
    (* 1 < 2：0<1 加法平移 + one+zero==one 换形 *)
    apply (RealSetoid.real_lt_compat
             (real_plus real_one real_zero) real_one
             (real_plus real_one real_one) (real_plus real_one real_one)).
    + exact (real_plus_zero real_one).
    + apply real_eq_refl.
    + exact (real_lt_plus_translate real_one real_zero real_one
               real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Part D：槽族 3（旗舰）——KL 字面形桥                                   *)
(*   real_kl_term p q（CW219 规范形 p·(−log(q/p))）≡ p·(log p − log q)   *)
(*   （b_gibbs_* / req2_gibbs_inequality / fe_a 字面形）。链：            *)
(*   log(q/p) == log q + log(1/p)（real_log_mult）+ log(1/p) == −log p    *)
(*   （G5 logd_log_inv_one_inv_real——E-GIBBSD-2 记名缺口件到位）→        *)
(*   取负换序收口。零 log 逆消去阻塞，E-GIBBSD-2 就此勘误闭合。           *)
(* ============================================================ *)

(* D1【槽放电位】：real_kl_term 与字面形逐点恒等（req_kl_term_equiv 型    *)
(*    槽的 Real 实例化——Section RealRLHFMain 诚实接口 real_kl_term_equiv *)
(*    的填件方向之逆，双形并存） *)
Lemma logd_kl_term_minus_form : forall (p q : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp)
                                  (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (Hi := real_inv_pos_pos p Hp).
  set (Hr := real_mult_positive q (real_inv_pos p Hp) Hq Hi).
  (* log(q/p) == log q + (−log p)（log_mult 分解 + G5 log 逆消去） *)
  assert (Hlog : real_eq
                   (real_log (real_mult q (real_inv_pos p Hp)) Hr)
                   (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
  { apply (real_eq_trans
             (real_log (real_mult q (real_inv_pos p Hp)) Hr)
             (real_plus (real_log q Hq) (real_log (real_inv_pos p Hp) Hi))
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
    - exact (real_log_mult q (real_inv_pos p Hp) Hq Hi).
    - apply (RealSetoid.real_eq_plus_compat (real_log q Hq)
               (real_log (real_inv_pos p Hp) Hi) (real_log q Hq)
               (real_opp (real_log p Hp))).
      + apply real_eq_refl.
      + exact (logd_log_inv_one_inv_real p Hp Hi). }
  (* p·(−log(q/p)) == p·(log p − log q)：取负 + 换序 + opp 对合 *)
  apply (RealSetoid.real_eq_mult_compat p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr)) p
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr))
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    + apply (RealSetoid.real_eq_opp_compat
               (real_log (real_mult q (real_inv_pos p Hp)) Hr)
               (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
      exact Hlog.
    + apply (real_eq_trans
               (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq))
                          (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      * exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log q Hq))
                            (real_opp (real_opp (real_log p Hp))))
                 (real_plus (real_opp (real_opp (real_log p Hp)))
                            (real_opp (real_log q Hq)))
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
        -- apply real_plus_comm.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_opp (real_opp (real_log p Hp)))
                     (real_opp (real_log q Hq))
                     (real_log p Hp) (real_opp (real_log q Hq))).
           ++ exact (real_opp_opp (real_log p Hp)).
           ++ apply real_eq_refl.
Qed.

(* D2：求和层字面形恒等（real_list_sum_ext 逐点提升） *)
Lemma logd_list_sum_kl_minus_form :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq.
  apply real_list_sum_ext.
  intro s.
  exact (logd_kl_term_minus_form (p s) (q s) (Hp s) (Hq s)).
Qed.

(* D3【保底主件】：0 ≤_B Σ p·(log p − log q)——b_gibbs_pos 字面形的     *)
(*    Real 实例化（gibbsd_gibbs_inequality 规范形 + D2 换形；与 E.13     *)
(*    real_gibbs_inequality_B 规范形双形并存） *)
Lemma logd_gibbs_inequality_minus_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  apply (logd_le_b_id_r real_zero
           (real_list_sum X
              (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_list_sum X
              (fun s : X => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (q s) (Hq s))))) l)).
  - exact (gibbsd_gibbs_inequality X l p q Hp Hq Hnormp Hnormq).
  - exact (logd_list_sum_kl_minus_form X l p q Hp Hq).
Qed.

(* D4：0 ≤ Σ p·(log p − log q) + eps——b_gibbs_sum_eps 字面形的          *)
(*    Real 实例化（real_gibbs_inequality_eps 规范形 + D2 换形；与 D3     *)
(*    双形并存：Or 逐 eps 形 / Bishop 形） *)
Lemma logd_gibbs_inequality_minus_eps :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s)
                         (real_plus (real_log (p s) (Hp s))
                                    (real_opp (real_log (q s) (Hq s))))) l)
       eps).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq eps Heps.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
              eps)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)
              eps)).
  - exact (RealSetoid.real_eq_plus_compat
             (real_list_sum X
                (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
             eps
             (real_list_sum X
                (fun s : X => real_mult (p s)
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (q s) (Hq s))))) l)
             eps
             (logd_list_sum_kl_minus_form X l p q Hp Hq)
             (real_eq_refl eps)).
  - exact (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq eps Heps).
Qed.

(* ============================================================ *)
(* Part E：槽族 4——real_gibbs_sum_eps@UpRealLeB:206 槽填件               *)
(*   （Section RealRLHFLeB 供给槽；real_sum_over_S := real_list_sum      *)
(*     实例化；q := real_boltzmann_dist_r；供给槽 Hnormb = Σ p_b == 1    *)
(*     显式位——诚实条件放电（G5 logd_pos_of_agree 同型手法），           *)
(*     real_rlhf_optimal_B 供给链到此闭合到一条解析件）                   *)
(* ============================================================ *)

Lemma logd_gibbs_sum_eps_boltzmann_list :
  forall (X : Type) (base : X -> Real) (D : Real)
    (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z)
    (l : list X) (p : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s) l)
                real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_kl_term (p s)
                          (real_boltzmann_dist_r X base D D_pos Z Z_pos s)
                          (Hp s)
                          (real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)) l)
       eps).
Proof.
  intros X base D D_pos Z Z_pos l p Hp Hnormp Hnormb eps Heps.
  exact (real_gibbs_inequality_eps X l p
           (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s)
           Hp
           (fun s : X => real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)
           Hnormp Hnormb eps Heps).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全部放电件 Print Assumptions + 提取常数面）         *)
(* ============================================================ *)
Print Assumptions logd_le_b_id_r.
Print Assumptions logd_log_le_linear_eps.
Print Assumptions logd_log_le_linear_B.
Print Assumptions logd_log_lt_mono_real.
Print Assumptions logd_log_two_pos_real.
Print Assumptions logd_kl_term_minus_form.
Print Assumptions logd_list_sum_kl_minus_form.
Print Assumptions logd_gibbs_inequality_minus_B.
Print Assumptions logd_gibbs_inequality_minus_eps.
Print Assumptions logd_gibbs_sum_eps_boltzmann_list.

From Stdlib Require Import Extraction.
(* G3 全量提取面（10 件；magic 普查=73，全部位于 coq_RealEnhancedReal    *)
(*    类实例打包常量与 G5 UpReqLogPrimD 类投影链——本席 10 件自身证明体   *)
(*    零 magic，唯一触点=D1 消费 G5 logd_log_inv_one_inv_real 的强制     *)
(*    转型一处；见交付报告 G3 节） *)
Extraction "_logd_g3_extract.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real
  logd_kl_term_minus_form logd_list_sum_kl_minus_form
  logd_gibbs_inequality_minus_B logd_gibbs_inequality_minus_eps
  logd_gibbs_sum_eps_boltzmann_list.
(* G3 纯净面（5 件，零类实例依赖；magic=0 门证据件） *)
Extraction "_logd_g3_pure.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real.

(* ============================================================ *)
(* 对账（G6 交付清单，17 槽逐槽判词；索引回填行见交付报告卡尾）：         *)
(*   槽族 1（log_le_linear 双形，5 槽位）：                              *)
(*    - log_le_linear@UpReqU2:313 / @UpReqFEPAttn:90 —— Real 实例化放电  *)
(*      （B1/B2 双形）；req 层 Or 全字面形 = 逆向桥红线不越（§380）。    *)
(*    - dist_log_le_linear@UpReqDist:1029 / @UpReqTempEntropy:60 /       *)
(*      @UpFirewallReq:101 —— 同上（同语句独立声明，落点逐文件）。       *)
(*   槽族 2（log 严格单调，3 槽）：                                      *)
(*    - log_lt_mono_cc@UpReqCauchy:819 / ralt_log_lt_mono@               *)
(*      UpReqAlignRestA:80 —— 字面形放电（C1 直喂）。                    *)
(*    - log_two_pos@UpPredRelaxReq:221 —— 字面形放电（C2 组装）。        *)
(*   槽族 3（gibbs 字面形桥，4 槽）：                                    *)
(*    - b_gibbs_pos@UpSigMigrate2:913 / b_gibbs_sum_eps@916 —— 字面形    *)
(*      Real 实例化放电（D3/D4；kl_a 字面形逐位对齐）。                  *)
(*    - req2_gibbs_inequality@UpReqAlign3:1451 / @UpReqU2:356 —— 同上    *)
(*      供给（KLE 字面形=kl_a 同构；req 层 Or 形阻塞判词与                *)
(*      UpReqAlign3 台账「plain-le 形态不可由接口逐 eps 字段导出」一致）。*)
(*   X 阻塞 4 槽（等号情形，构造性不可证——CW219 L41199 注记强三分/LPO）： *)
(*    - log_eq_linear@UpReqU2:315 / @UpReqFEPAttn:92；                   *)
(*      dist_log_eq_linear@UpReqDist:1031 / @UpReqTempEntropy:62；       *)
(*      b_gibbs_eq@UpSigMigrate2:921；                                   *)
(*      bridge_free_energy_min_unique@UpReqAlign:288（FEP 唯一极小=      *)
(*      KL 等号情形）。普查 §373 席 l「可能留槽」预判成立。               *)
(*   S 阻塞 4 槽（复合/抽象，供给链已明）：                              *)
(*    - entropy_tangent@UpEntropyGainReq:77 / @UpReqCauchy:1383 ——       *)
(*      entropy_gradient 抽象无 spec（N 参「抽象 entropy 凹性」）。       *)
(*    - req_energy_exp_temp_mono@UpFirewallReq:135 /                     *)
(*      req_energy_exp_temp_strict_mono@138 —— fw_et 温度复合；供给=     *)
(*      req_entropy_temp_explicit 槽本身 S 阻塞（G5 判词表）；严格版另   *)
(*      需 KL>0 的 Or-lt 形（等号层 X）。                                *)
(*    - bridge_min_free_energy@UpReqAlign:285 —— Real 实例化已在盘       *)
(*      （real_rlhf_optimal_B@UpRealLeB:237，le_b 形；供给链经本席       *)
(*      Part E 闭合到唯一解析件 Σp_b==1）；req 层 Or 形=红线阻塞。        *)
(*   槽族 4：real_gibbs_sum_eps@UpRealLeB:206 —— 条件放电（Part E；      *)
(*      供给槽 Σ p_b == 1 的解析实例化留档）。                            *)
(* 沉淀卡（索引回填行见交付报告卡尾）：                                  *)
(*   E-LOGD-1：E354 勘误落地——接口字段 log_le_linear_eps@41134 /         *)
(*   log_mult / exp_neg_plus 在案，req 逐 eps 形直喂成立；E-GIBBSD-2     *)
(*   勘误落地——log 逆消去经 G5 logd_log_inv_one_inv_real 到位，          *)
(*   real_kl_term ↔ p·(log p − log q) 字面形桥全通（Part D），           *)
(*   Section RealRLHFMain 诚实接口 real_kl_term_equiv 槽自此可填。        *)
(*   E-LOGD-2：Bishop 序右端换形件 logd_le_b_id_r 为 gibbsd_le_b_id_l    *)
(*   对偶（Part A 可跨战役复用）；b_gibbs_* 字面形族放电只需              *)
(*   gibbsd 和层机 + 单点 D1，无需重建和层。                             *)
(* ============================================================ *)
