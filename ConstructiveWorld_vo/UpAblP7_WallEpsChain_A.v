(* ============================================================ *)
(* UpAblP7_WallEpsChain_A.v —— rsq 链的行不等式逐 eps 前半段：五件工具与边界注记 *)
(*                                                              *)
(* 数学使命：本件形式化 rsq 收缩链「行不等式」的逐 eps 前半段：以姊妹件       *)
(*   UpAblP7_WallEps_CSM 的链根逐 eps 行不等式（uabp7we_abs_row_eps_absK）     *)
(*   为起点向链上推进——逐点级步差界的逐 eps 形（ua7c_hpt_eps）、单 eps 余量    *)
(*   工具（ua7c_le_plus_eps_r）、数乘分配核（ua7c_mult_le_plus_distr_r）与     *)
(*   两步预算合成核（ua7c_budget_compose）。                                   *)
(*                                                              *)
(* 边界注记（如实记录，非弱化）：rsq_u_tv_contraction 的求和级全量逐 eps 形    *)
(*   （le (Σ|Δs'|) (omd·Σ|Δμν| + eps)）在无限世界 S 上无单 eps 构造路线：      *)
(*   行不等式逐 eps 形的 eps 预算在逐行求和时累积为 Σ_{s'} 常数项（无限和      *)
(*   无界，无法构造性收束）。两条构造性绕行路线：                              *)
(*   (a) 有限世界路线：若 S 配有有限清单（enum），常数行预算 nR·c 有界，        *)
(*       单一总预算成立——归 UpReqConcMixSel 侧（ReqBoundedSoftmax 同位）；      *)
(*   (b) 显式预算链路线：行预算保持逐 eps 形（件 3），逐点级预算显式可搬       *)
(*       （件 2），预算按收缩率合成（件 5）——全量收束仍需 (a)。                *)
(*   本件五件的结论均在该边界以内，未引入不带余量形的替代。                    *)
(*                                                              *)
(* 主要结果（前缀 ua7c_，全 Qed）：                                            *)
(*   件 1 ua7c_le_plus_eps_r：le a b ⟹ lt zero eps ⟹ le a (b+eps)。            *)
(*   件 2 ua7c_mult_le_plus_distr_r：le zero c ⟹ le a (b+eps) ⟹               *)
(*     le (c·a) (c·b + c·eps)（数乘分配）。                                    *)
(*   件 3 ua7c_abs_row_eps：行不等式的逐 eps 形（rsq_u_abs_row 同形）。         *)
(*   件 4 ua7c_hpt_eps：逐点级步差界 ≤ omd·(行和) + omd·eps（Hpt 支逐 eps 形）。*)
(*   件 5 ua7c_budget_compose：两步预算合成（率²·基 + 率·eps1 + eps2）。        *)
(*                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqSumD、     *)
(*   UpReqConcSoftmax、UpReqSampling、UpAblP7_WallEps_CSM（链根起点）、         *)
(*   ConcMixSelFeed（cms_sum_ext/cms_sum_linear/cms_sum_add：求和位载体供给锚）；*)
(*   实数接口取 RealEnhancedReal 具体层实例（导入后类型类解析，与源模块同源）。 *)
(*                                                              *)
(* 证明要点：件 1 由 le_trans 与 req_le_plus_nonneg_r；件 2 由 distrib 与       *)
(*   req_le_mult_compat_r，le_id_r 换尾；件 3 为姊妹件出节核的全参实例化；      *)
(*   件 4 先以 req 代数链（reqd_minus_compat、req_minus_plus_congr_l、          *)
(*   req_minus_factor、reqd_sum_minus 反演、sum_ext、req_minus_factor_pt）      *)
(*   化简步差（不使用三角不等式），再经 req_abs_compat、abs_mult、              *)
(*   abs_ge_zero_req 换入绝对值，末端由件 2 与件 3 收尾；件 5 由件 2 的         *)
(*   率数乘分配、le_plus_compat 同右端加项与 plus_assoc 换尾合成。                    *)
(*                                                              *)
(* Section 前提的地位：sum_ext、sum_linear、sum_add、abs_sum_le_eps_h、         *)
(*   abs_ge_zero_req、K_nonneg、step_decomp 均为 Section 内假设（出节后量化     *)
(*   为定理前提），与库件 rsq_u_r_kernel 的出节签名同位；其中                   *)
(*   abs_sum_le_eps_h 即逐 eps 三角不等式，为本件链根的前提。                   *)
(*                                                              *)
(* 构造性注记：全件语句集合值面；零承认、零经典逻辑捷径、零排中律；              *)
(*   文尾对逐件 Print Assumptions 审计封闭。                                    *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。     *)
(*                                                              *)
(* 标识符约定：本件命名以前缀 ua7c_ 区分于库内 rsq_ 系列与姊妹件 uabp7we_；     *)
(*   步分解以抽象 step/step_decomp 承载（库件 rsq_u_step_decomp 同形接口化，    *)
(*   其本体无需重证）。                                                        *)
(*                                                              *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpAblP7_WallEps_CSM.
Require Import ConcMixSelFeed.
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
