(* ==========================================================================)
   UpAblP7_WallEpsChain_A.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：uabp7we_mixed_f、uabp7we_sumd_twopt、uabp7we_csm_eps_twopt、uabp7we_twopt_mixed_sign、uabp7we_abs_row_eps_absK、uabp7we_rkern、uabp7we_rkern_nonneg、uabp7we_abs_row_eps、uabp7we_sum_ext_supply。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
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
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import ConcMixSelFeed.
Require Import UpReqConcFin2.
Require Import UpReqDist.

(* ================= §1 uabp7we_mixed_f 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ============ 二元变号载体上的逐 eps 实例面 ============ *)

(* 变号载体族：两点 bool 载体，系数 a 与 −b（a,b>0 的证明另附），
   正负两支各占一点——使三角不等式在变号系数下取实质形。 *)
Definition uabp7we_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 二元约简：折叠在二点清单上定义性归约为逐点加法（req 链两段：
   折叠的内部自归约 + 右端零消去） *)
Lemma uabp7we_sumd_twopt : forall g : bool -> Real,
  req (sumd_list_sum bool g (true :: false :: nil))
      (plus (g true) (g false)).
Proof.
  intro g.
  exact (req_trans
           (sumd_list_sum bool g (true :: false :: nil))
           (plus (g true) (plus (g false) zero))
           (plus (g true) (g false))
           (req_refl (plus (g true) (plus (g false) zero)))
           (req_plus_compat (g true) (g true)
              (plus (g false) zero) (g false)
              (req_refl (g true))
              (plus_zero (g false)))).
Qed.

(* 主例：二元变号载体上 |Σf| ≤ Σ|f| + eps（逐 eps 形）。
   由库件 csm_abs_sum_le_eps（UpReqConcSoftmax）直接实例化，
   二元载体为其具体实例。 *)
Lemma uabp7we_csm_eps_twopt : forall a b eps : Real,
  lt zero a -> lt zero b -> lt zero eps ->
  le (abs (csm_sumf bool (true :: false :: nil) (uabp7we_mixed_f a b)))
     (plus (csm_sumf bool (true :: false :: nil)
              (fun s : bool => abs (uabp7we_mixed_f a b s)))
           eps).
Proof.
  intros a b eps Ha Hb Heps.
  exact (csm_abs_sum_le_eps bool (true :: false :: nil)
           (uabp7we_mixed_f a b) eps Heps).
Qed.

(* 符号合取：正支在 true 点定义性等于 a（正），负支在 false 点定义性
   等于 −b，由 b>0 经 opp_lt_compat 反号保序得负——变号载体上
   两支符号在此逐点确定。两个见证以 sigT 依存对承载
   （Set 值面的合取不走 Prop 连接子，配对走依存对） *)
Lemma uabp7we_twopt_mixed_sign : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT (fun _ : lt zero (uabp7we_mixed_f a b true) =>
        lt (uabp7we_mixed_f a b false) zero).
Proof.
  intros a b Ha Hb.
  exact (existT _
           Ha
           (req_lt_id_r_loc (opp b) (opp zero) zero
              (req_trans (opp zero) (plus zero (opp zero)) zero
                 (req_sym (plus zero (opp zero)) (opp zero)
                    (req_plus_zero_l (opp zero)))
                 (plus_opp zero))
              (opp_lt_compat zero b Hb))).
Qed.

(* ============ 行加权和不等式的逐 eps 形重建 ============ *)

(* 抽象核：任意逐点非负核 K 上，行不等式（与 rsq_u_abs_row 同形）
   的逐 eps 形——求和三角前提取逐 eps 形（以 abs_sum_le_eps_h
   替代不带余量形 abs_sum_le_h），结论右端加 eps 余量。 *)
Section WallEpsRowAbs.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* 求和外延前提（与 rsq 同位） *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).

(* 逐 eps 三角前提：abs_sum_le_h 的 Bishop 逐 eps 形同位替换 *)
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).

(* 逐点非负核 K（与 rsq 核非负前提同形） *)
Variable K : S -> S -> R.
Hypothesis K_nonneg : forall s s' : S, le zero (K s s').

(* 绝对值非负定位前提（le zero a ⟹ abs a = a，与 rsq 同位） *)
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* 行不等式的逐 eps 重建（与 rsq_u_abs_row 同形）：
   右端多 eps 余量；证明链 = 乘积绝对值分解（abs_mult 与非负定位）经
   sum_ext 加法外延换元与 req_plus_compat，末端由逐 eps 三角前提给出。 *)
Theorem uabp7we_abs_row_eps_absK : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (K s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (le_id_r
           (abs (sumf (fun s : S => mult (f s) (K s s'))))
           (plus (sumf (fun s : S => abs (mult (f s) (K s s')))) eps)
           (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps)
           (req_plus_compat
              (sumf (fun s : S => abs (mult (f s) (K s s'))))
              (sumf (fun s : S => mult (abs (f s)) (K s s')))
              eps eps
              (sum_ext
                 (fun s : S => abs (mult (f s) (K s s')))
                 (fun s : S => mult (abs (f s)) (K s s'))
                 (fun s : S =>
                    req_trans
                      (abs (mult (f s) (K s s')))
                      (mult (abs (f s)) (abs (K s s')))
                      (mult (abs (f s)) (K s s'))
                      (abs_mult (f s) (K s s'))
                      (req_mult_compat (abs (f s)) (abs (f s))
                         (abs (K s s')) (K s s')
                         (req_refl (abs (f s)))
                         (abs_ge_zero_req (K s s') (K_nonneg s s')))))
              (req_refl eps))
           (abs_sum_le_eps_h (fun s : S => mult (f s) (K s s')) eps Heps)).
Qed.

End WallEpsRowAbs.

(* rsq 核实例节：以库件 rsq_u_r_kernel 的最小前提集实例化抽象核
   （rsq_u_r_nonneg 的出节签名即所需全部前提） *)
Section WallEpsRowRsq.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable u : S -> R.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable lpc : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* rsq 核同形定义（库件直连，无需重证） *)
Definition uabp7we_rkern (s s' : S) : R :=
  rsq_u_r_kernel S u delta delta_lt_one transition lpc s s'.

(* 核逐点非负：直接应用库件出节形（实参 R RIS S u delta
   delta_lt_one transition minorization lpc s s' 全显给出） *)
Lemma uabp7we_rkern_nonneg : forall s s' : S, le zero (uabp7we_rkern s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg R RIS S u delta delta_lt_one transition
           minorization lpc s s').
Qed.

(* 主定理：行不等式（rsq_u_abs_row）的逐 eps 形重建——
   抽象核以 K:=rsq 核全参实例化；rsq_u_abs_row 正是
   cmk_attention_mixing_time 链中该行不等式的库内原型（经 rsq 链继承） *)
Theorem uabp7we_abs_row_eps : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (uabp7we_rkern s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (uabp7we_rkern s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (@uabp7we_abs_row_eps_absK R RIS S sumf sum_ext abs_sum_le_eps_h
           uabp7we_rkern uabp7we_rkern_nonneg abs_ge_zero_req f s' eps Heps).
Qed.

End WallEpsRowRsq.

(* ============ 前提位的载体供给节（逐位消解） ============

   sum_ext（两节同位）与 abs_sum_le_eps_h（两节同位）为抽象求和算子
   sumf 的接口义务；本节在有限和载体 csm_sumf S0 enum（枚举清单折叠，
   UpReqConcSoftmax）上供给同构语句——两节同位语句同型，共件消解。
   供给锚：cms_sum_ext（ConcMixSelFeed）与 csm_abs_sum_le_eps
   （UpReqConcSoftmax，本件已引）。minorization 位为抽象核下界义务；
   本节在 Fin2 载体（delta:=cf2_delta_star、u:=cf2_Unif、
   transition:=cf2_kernel，UpReqConcFin2）上供给同构语句，供给锚=
   cf2_minorization。原抽象假设位声明与既有定理签名零改动。 *)

Section WallEpsSlotsSupply.
Variable S0 : Set.
Variable enum : list S0.

(* 位 sum_ext：求和外延（cms_sum_ext S0 enum 全参直引） *)
Theorem uabp7we_sum_ext_supply : forall (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) ->
  req (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_ext S0 enum). Qed.

(* 位 abs_sum_le_eps_h：逐 eps 三角（csm_abs_sum_le_eps S0 enum 全参直引） *)
Theorem uabp7we_abs_sum_le_eps_supply : forall (f : S0 -> Real) (eps : Real),
  lt zero eps ->
  le (abs (csm_sumf S0 enum f))
     (plus (csm_sumf S0 enum (fun s : S0 => abs (f s))) eps).
Proof. exact (csm_abs_sum_le_eps S0 enum). Qed.

(* 位 minorization：核下界的 Fin2 载体实例（cf2_minorization 全参直引） *)
Theorem uabp7we_minorization_supply : forall s s' : bool,
  le (mult cf2_delta_star (cf2_Unif s')) (cf2_kernel s s').
Proof. exact (cf2_minorization). Qed.

End WallEpsSlotsSupply.

(* ============ 假设审计（对逐件 Print Assumptions） ============ *)
Print Assumptions uabp7we_sumd_twopt.
Print Assumptions uabp7we_csm_eps_twopt.
Print Assumptions uabp7we_twopt_mixed_sign.
Print Assumptions uabp7we_abs_row_eps_absK.
Print Assumptions uabp7we_rkern_nonneg.
Print Assumptions uabp7we_abs_row_eps.
Print Assumptions uabp7we_sum_ext_supply.
Print Assumptions uabp7we_abs_sum_le_eps_supply.
Print Assumptions uabp7we_minorization_supply.
(* ================= §2 ua7c_le_plus_eps_r 族 ================= *)
Import RealInterfaceEnhancedMod.

Section WallEpsChainA.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和接口（与 rsq ReqUContraction 同位的最小集） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Let sum_minus := reqd_sum_minus S sumf sum_ext sum_add sum_linear.

(* 逐 eps 三角前提：abs_sum_le_h（与 UpReqSampling 同位）的 Bishop
   逐 eps 形同位替换——本件链根的前提，无不带余量形的替代 *)
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).

(* 绝对值非负定位前提（le zero a ⟹ abs a = a，与 rsq 同位） *)
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* 核：任意逐点非负核（与库件 rsq_u_r_kernel 同位的接口；其非负与
   行归一前提在库内已由 uabp7we_rkern_nonneg 给出） *)
Variable K : S -> S -> R.
Hypothesis K_nonneg : forall s s' : S, le zero (K s s').

(* 收缩数据：delta 与 delta < 1（与库件同位） *)
Variable delta : R.
Variable delta_lt_one : lt delta one.

Let omd : R := req_minus one delta.

(* 步函数：与库件 u_step（sumf∘mult∘transition）同形的接口化
   （分解前提 step_decomp 与 rsq_u_step_decomp 同形；本体无需重证） *)
Variable u : S -> R.
Variable step : (S -> R) -> S -> R.
Hypothesis step_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (step mu s')
      (plus (mult delta (u s'))
            (mult omd (sumf (fun s : S => mult (mu s) (K s s'))))).

(* ============ 件 1：单 eps 余量加项工具 ============ *)
(* le a b 的逐 eps 弱化：结论右端加正 eps 余量（链上各件从不带余量形 *)
(*   结论向逐 eps 形过渡的通用工具；由 lt_le_iff 的 Or 左支给出） *)
Lemma ua7c_le_plus_eps_r : forall (a b eps : R),
  le a b -> lt zero eps -> le a (plus b eps).
Proof.
  intros a b eps Hab Heps.
  exact (le_trans a b (plus b eps) Hab
           (req_le_plus_nonneg_r b eps (lt_le_iff zero eps (inl Heps)))).
Qed.

(* ============ 件 2：数乘对逐 eps 界的分配 ============ *)
(* 非负数乘 c 把逐 eps 界 a ≤ b+eps 分配为 c·a ≤ c·b + c·eps：
   件 4 与件 5 中 omd 缩放的分配用核。
   证明路径：req_le_mult_compat_r 数乘保序与 distrib，le_id_r 换尾。 *)
Lemma ua7c_mult_le_plus_distr_r : forall (c a b eps : R),
  le zero c -> le a (plus b eps) ->
  le (mult c a) (plus (mult c b) (mult c eps)).
Proof.
  intros c a b eps Hc Hab.
  exact (le_id_r (mult c a)
                 (mult c (plus b eps))
                 (plus (mult c b) (mult c eps))
                 (distrib c b eps)
                 (req_le_mult_compat_r c a (plus b eps) Hc Hab)).
Qed.

(* ============ 件 3：链根行不等式的逐 eps 形（直接实例化姊妹件） ============ *)
(* 与 rsq_u_abs_row 同形的逐 eps 版：@ 全显实例化姊妹件出节核
   uabp7we_abs_row_eps_absK，本节前提逐参对位。 *)
Lemma ua7c_abs_row_eps : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (K s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (@uabp7we_abs_row_eps_absK R RIS S sumf sum_ext abs_sum_le_eps_h
           K K_nonneg abs_ge_zero_req f s' eps Heps).
Qed.

(* ============ 件 4：逐点级步差界的逐 eps 形（Hpt 支） ============ *)
(* rsq_u_tv_contraction 的 Hpt 支的逐 eps 形：
   步差界以 omd 缩放的行和加 omd·eps 余量收束。证明路径：步差分解
   req 链（reqd_minus_compat、req_minus_plus_congr_l、req_minus_factor、
   reqd_sum_minus 反演、sum_ext、req_minus_factor_pt，纯 req 代数，
   不使用三角不等式）逐字对应，再经 req_abs_compat、abs_mult、
   abs_ge_zero_req 换入绝对值，末端由件 3 经件 2 收尾。此为边界注记
   所述可达的最大档：求和级全量形见文件头边界注记。 *)
Lemma ua7c_hpt_eps : forall (mu nu : S -> R) (s' : S) (eps : R),
  req (sumf mu) one -> req (sumf nu) one -> lt zero eps ->
  le (abs (req_minus (step mu s') (step nu s')))
     (plus (mult omd (sumf (fun s : S =>
              mult (abs (req_minus (mu s) (nu s))) (K s s'))))
           (mult omd eps)).
Proof.
  intros mu nu s' eps Hmu Hnu Heps.
  assert (Hge : le zero omd).
  { exact (req_le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one))). }
  assert (Hd : req (req_minus (step mu s') (step nu s'))
                   (mult omd (sumf (fun s : S =>
                      mult (req_minus (mu s) (nu s)) (K s s'))))).
  { apply (req_trans (req_minus (step mu s') (step nu s'))
             (req_minus (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (mu s) (K s s')))))
                        (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (nu s) (K s s')))))) _).
    - exact (reqd_minus_compat (step mu s')
                (plus (mult delta (u s'))
                      (mult omd (sumf (fun s : S => mult (mu s) (K s s')))))
                (step nu s')
                (plus (mult delta (u s'))
                      (mult omd (sumf (fun s : S => mult (nu s) (K s s')))))
                (step_decomp mu s' Hmu) (step_decomp nu s' Hnu)).
    - apply (req_trans _ (req_minus (mult omd
                (sumf (fun s : S => mult (mu s) (K s s'))))
                (mult omd (sumf (fun s : S => mult (nu s) (K s s'))))) _).
      + exact (req_minus_plus_congr_l (mult delta (u s'))
                  (mult omd (sumf (fun s : S => mult (mu s) (K s s'))))
                  (mult omd (sumf (fun s : S => mult (nu s) (K s s'))))).
      + apply (req_trans _ (mult omd (req_minus
                  (sumf (fun s : S => mult (mu s) (K s s')))
                  (sumf (fun s : S => mult (nu s) (K s s'))))) _).
        * exact (req_minus_factor omd
                    (sumf (fun s : S => mult (mu s) (K s s')))
                    (sumf (fun s : S => mult (nu s) (K s s')))).
        * apply (req_mult_compat omd omd
                     (req_minus (sumf (fun s : S => mult (mu s) (K s s')))
                                (sumf (fun s : S => mult (nu s) (K s s'))))
                     (sumf (fun s : S =>
                        mult (req_minus (mu s) (nu s)) (K s s')))
                     (req_refl omd)).
          apply (req_trans (req_minus (sumf (fun s : S => mult (mu s) (K s s')))
                                      (sumf (fun s : S => mult (nu s) (K s s'))))
                           (sumf (fun s : S =>
                              req_minus (mult (mu s) (K s s'))
                                        (mult (nu s) (K s s')))) _).
          -- exact (req_sym _ _
                      (sum_minus (fun s : S => mult (mu s) (K s s'))
                                 (fun s : S => mult (nu s) (K s s')))).
          -- exact (sum_ext (fun s : S =>
                   req_minus (mult (mu s) (K s s')) (mult (nu s) (K s s')))
                            (fun s : S => mult (req_minus (mu s) (nu s)) (K s s'))
                            (fun s : S => req_minus_factor_pt (mu s) (nu s) (K s s'))). }
  apply (le_id_l (abs (req_minus (step mu s') (step nu s')))
                 (mult omd (abs (sumf (fun s : S =>
                    mult (req_minus (mu s) (nu s)) (K s s')))))
                 (plus (mult omd (sumf (fun s : S =>
                    mult (abs (req_minus (mu s) (nu s))) (K s s'))))
                       (mult omd eps))).
  - apply (req_trans (abs (req_minus (step mu s') (step nu s')))
                     (abs (mult omd (sumf (fun s : S =>
                        mult (req_minus (mu s) (nu s)) (K s s'))))) _).
    + exact (req_abs_compat (req_minus (step mu s') (step nu s'))
                (mult omd (sumf (fun s : S =>
                   mult (req_minus (mu s) (nu s)) (K s s')))) Hd).
    + exact (req_trans (abs (mult omd (sumf (fun s : S =>
                 mult (req_minus (mu s) (nu s)) (K s s')))))
            (mult (abs omd) (abs (sumf (fun s : S =>
               mult (req_minus (mu s) (nu s)) (K s s'))))) _
            (abs_mult omd (sumf (fun s : S =>
               mult (req_minus (mu s) (nu s)) (K s s'))))
            (req_mult_compat (abs omd) omd
               (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (K s s'))))
               (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (K s s'))))
               (abs_ge_zero_req omd Hge) (req_refl _))).
  - exact (ua7c_mult_le_plus_distr_r omd
             (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (K s s'))))
             (sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (K s s')))
             eps Hge
             (ua7c_abs_row_eps (fun s : S => req_minus (mu s) (nu s)) s' eps Heps)).
Qed.

(* ============ 件 5：两步预算合成核（与 tv_iter 递归步对位） ============ *)
(* rsq_u_tv_iter 的递归步（收缩一步与率数乘对位）在逐 eps 预算下的
   合成形态：两步预算 eps1、eps2 合成为 plus (率²·基) (plus (率·eps1) eps2)。
   证明路径：件 2（率·预算分配）、le_plus_compat 同右端加项、
   plus_assoc 与 le_id_r 换尾。全量 n 步收束仍需文件头边界注记 (a)
   （有限世界路线），此处仅两步合成核。 *)
Let inv_two : R := inv_pos (plus one one) req_two_pos.
Let tvq (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

Lemma ua7c_budget_compose : forall (mu nu : S -> R) (eps1 eps2 : R),
  le zero omd ->
  le (tvq (step mu) (step nu)) (plus (mult omd (tvq mu nu)) eps1) ->
  le (tvq (step (step mu)) (step (step nu)))
     (plus (mult omd (tvq (step mu) (step nu))) eps2) ->
  le (tvq (step (step mu)) (step (step nu)))
     (plus (mult (mult omd omd) (tvq mu nu)) (plus (mult omd eps1) eps2)).
Proof.
  intros mu nu eps1 eps2 Hge H1 H2.
  assert (Hsc : le (mult omd (tvq (step mu) (step nu)))
                   (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1))).
  { exact (le_id_r (mult omd (tvq (step mu) (step nu)))
                   (plus (mult omd (mult omd (tvq mu nu))) (mult omd eps1))
                   (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1))
                   (req_plus_compat (mult omd (mult omd (tvq mu nu)))
                                    (mult (mult omd omd) (tvq mu nu))
                                    (mult omd eps1) (mult omd eps1)
                                    (mult_assoc omd omd (tvq mu nu))
                                    (req_refl (mult omd eps1)))
                   (ua7c_mult_le_plus_distr_r omd (tvq (step mu) (step nu))
                      (mult omd (tvq mu nu)) eps1 Hge H1)). }
  apply (le_trans (tvq (step (step mu)) (step (step nu)))
                  (plus (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1)) eps2)
                  (plus (mult (mult omd omd) (tvq mu nu)) (plus (mult omd eps1) eps2))).
  - exact (le_trans (tvq (step (step mu)) (step (step nu)))
                    (plus (mult omd (tvq (step mu) (step nu))) eps2)
                    (plus (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1)) eps2)
                    H2
                    (le_plus_compat (mult omd (tvq (step mu) (step nu)))
                                    (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1))
                                    eps2 eps2 Hsc (le_refl eps2))).
  - exact (le_id_l (plus (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1)) eps2)
                   (plus (mult (mult omd omd) (tvq mu nu)) (plus (mult omd eps1) eps2))
                   (plus (mult (mult omd omd) (tvq mu nu)) (plus (mult omd eps1) eps2))
                   (req_sym (plus (mult (mult omd omd) (tvq mu nu))
                                  (plus (mult omd eps1) eps2))
                            (plus (plus (mult (mult omd omd) (tvq mu nu)) (mult omd eps1)) eps2)
                            (plus_assoc (mult (mult omd omd) (tvq mu nu)) (mult omd eps1) eps2))
                   (le_refl (plus (mult (mult omd omd) (tvq mu nu)) (plus (mult omd eps1) eps2)))).
Qed.

End WallEpsChainA.

(* ============ 四前提位的载体供给节（逐位消解） ============

   sum_ext/sum_linear/sum_add/abs_sum_le_eps_h 为抽象求和算子 sumf 的
   接口义务；本节在有限和载体 csm_sumf S0 enum（枚举清单折叠，
   UpReqConcSoftmax）上逐位供给同构语句。供给锚：cms_sum_ext/
   cms_sum_linear/cms_sum_add（ConcMixSelFeed）与 csm_abs_sum_le_eps
   （UpReqConcSoftmax，本件已引）。原抽象假设位声明与既有定理签名
   零改动。 *)

Section WallEpsChainSupply.
Variable S0 : Set.
Variable enum : list S0.

(* 位 sum_ext：求和外延（cms_sum_ext S0 enum 全参直引） *)
Theorem ua7c_sum_ext_supply : forall (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) ->
  req (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_ext S0 enum). Qed.

(* 位 sum_linear：标量提取（cms_sum_linear S0 enum 全参直引） *)
Theorem ua7c_sum_linear_supply : forall (a : Real) (f : S0 -> Real),
  req (csm_sumf S0 enum (fun s : S0 => mult a (f s)))
      (mult a (csm_sumf S0 enum f)).
Proof. exact (cms_sum_linear S0 enum). Qed.

(* 位 sum_add：求和逐点加法分配（cms_sum_add S0 enum 全参直引） *)
Theorem ua7c_sum_add_supply : forall (f g : S0 -> Real),
  req (csm_sumf S0 enum (fun s : S0 => plus (f s) (g s)))
      (plus (csm_sumf S0 enum f) (csm_sumf S0 enum g)).
Proof. exact (cms_sum_add S0 enum). Qed.

(* 位 abs_sum_le_eps_h：逐 eps 三角（csm_abs_sum_le_eps S0 enum 全参直引） *)
Theorem ua7c_abs_sum_le_eps_supply : forall (f : S0 -> Real) (eps : Real),
  lt zero eps ->
  le (abs (csm_sumf S0 enum f))
     (plus (csm_sumf S0 enum (fun s : S0 => abs (f s))) eps).
Proof. exact (csm_abs_sum_le_eps S0 enum). Qed.

End WallEpsChainSupply.

(* ============ 假设审计（对逐件 Print Assumptions） ============ *)
Print Assumptions ua7c_le_plus_eps_r.
Print Assumptions ua7c_mult_le_plus_distr_r.
Print Assumptions ua7c_abs_row_eps.
Print Assumptions ua7c_hpt_eps.
Print Assumptions ua7c_budget_compose.
Print Assumptions ua7c_sum_ext_supply.
Print Assumptions ua7c_sum_linear_supply.
Print Assumptions ua7c_sum_add_supply.
Print Assumptions ua7c_abs_sum_le_eps_supply.
