(* ============================================================ *)
(* UpAblP7_WallEpsChain_A.v —— 论文7 专项消融战役 席 PA7-20（W1 链身 eps 化·甲腿） *)
(*                                                              *)
(* 假设任务：T154 申报的终装遗留——rsq 链身 eps 化前半段。链根行墙     *)
(*   eps 形（姊妹件 UpAblP7_WallEps_CSM 的 uabp7we_abs_row_eps_absK）  *)
(*   为起点，向链身上推：逐点级步差界（rsq_u_tv_contraction 之 Hpt    *)
(*   支）的逐 eps 镜像 + eps 搬运核 + 预算合成核（tv_iter 递归骨架的   *)
(*   eps 绕行件）。乙腿 = PA7-21（UpReqConcMixSel 侧 cmk_* 段），未碰。 *)
(*                                                              *)
(* 消费链地图（union 根现行版实测行号）：                              *)
(*   UpReqSampling.v:116/:719  abs_sum_le_h 槽（plain 形，两节同位）    *)
(*   UpReqSampling.v:488       rsq_u_abs_row 墙槽唯一深消费位           *)
(*   UpReqSampling.v:580       rsq_u_tv_contraction 消费行墙（Hpt 支内） *)
(*   UpReqSampling.v:682       rsq_u_tv_iter 消费收缩（几何率递归）      *)
(*   UpReqSampling.v:1153/:1166 B 节全显包装（喂 plain 墙槽）           *)
(*   UpReqConcMixSel.v:880/:911 cmk_attention_mixing_time/_le（乙腿辖区） *)
(*                                                              *)
(* 🔒 LPO 墙位定谳（本席如实申报，非降级）：                            *)
(*   rsq_u_tv_contraction 的全量 eps 形（即 Hsum 求和级                 *)
(*   le (Σ|Δs'|) (plus (omd·Σ|Δμν|) eps)）在无限世界 S 上无单 eps       *)
(*   诚实路线：行墙（rsq_u_abs_row）在 Hpt 支内逐行消费，逐 eps 形下    *)
(*   eps 预算按行逃逸至 Σ_{s'} 常数项（无限和无界，sum_le 逐点抬升      *)
(*   后 sum_add 分解出 Σ_{s'} (omd·eps)，无构造性封口）。此即链身真     *)
(*   墙位。绕行注记（两条，均构造性）：                                 *)
(*   (a) 有限世界绕行：若 S 配 enum 有限清单（乙腿 cmk 侧               *)
(*       ReqBoundedSoftmax 同位既有 enum/enum_nonempty 与 list 求和     *)
(*       机器），常数行预算 Σ_{s'} c = nR·c 有界，单总预算成立——       *)
(*       该路线归乙腿辖区，本席未开工；                                 *)
(*   (b) 显式预算链绕行：保持行墙消费为逐 eps 形（件 3），逐点级 eps    *)
(*       预算显式可搬（件 2 数乘分配），预算按收缩率有限合成（件 5，    *)
(*       tv_iter 递归骨架的 eps 形对位）——全量封口仍需 (a)。            *)
(*   本件五件真 Qed 全部落在墙位以下的诚实档位，零 plain 形冒充。        *)
(*                                                              *)
(* 分级申报：                                                          *)
(*   N1 库内放电件直连：uabp7we_abs_row_eps_absK（CSM 出节件，链根      *)
(*     起点位，@ 全显消费）、req_le_plus_nonneg_r、lt_le_iff、          *)
(*     req_le_mult_compat_r、distrib、req_le_minus_nonneg、             *)
(*     reqd_minus_compat、req_minus_plus_congr_l、req_minus_factor、    *)
(*     req_minus_factor_pt、reqd_sum_minus、abs_mult、req_abs_compat、  *)
(*     req_mult_compat、le_trans/le_id_l/le_id_r/le_refl、              *)
(*     le_plus_compat、plus_assoc、inv_pos、req_two_pos。               *)
(*   N2 已证导出：件 1/2（eps 尾注与搬运核）、件 4（步差分解 req 链     *)
(*     全镜像 + 行墙逐 eps 消费）、件 5（预算合成）。                   *)
(*   N3 实例供给：step 分解槽以抽象 step/step_decomp 承载（库件         *)
(*     rsq_u_step_decomp 同形接口化，其本体零重证、出节面诚实）。        *)
(*                                                              *)
(* 依赖清单（只读消费，原树零改）：CW_ConstructiveWorld_219、           *)
(*   UpReqAlgebra、UpReqDist、UpReqSumD、UpReqConcSoftmax、             *)
(*   UpReqSampling、UpAblP7_WallEps_CSM（姊妹件，链根起点）；           *)
(*   具体层 = S07 实例（模块导入后类型类解析，与母件同源同解析）。       *)
(*                                                              *)
(* 红线自审：全件语句集合值面；全件真证收口；无承认件、无未证断言、     *)
(*   无经典逻辑捷径、无选择公理、无排中律；文尾逐件假设审计全封闭。     *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpAblP7_WallEps_CSM.
Import RealInterfaceEnhancedMod.

Section WallEpsChainA.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和诚实接口（rsq ReqUContraction 同位最小集） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Let sum_minus := reqd_sum_minus S sumf sum_ext sum_add sum_linear.

(* 逐 eps 墙槽：plain abs_sum_le_h（UpReqSampling:116 同位）的 Bishop
   逐 eps 形同位替换——链身 eps 化的桩位，零 plain 形冒充 *)
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).

(* 绝对值非负定位证书（rsq 同位诚实假设面，UpReqSampling:135 同位） *)
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* 核镜像位：任意逐点非负核（库件 rsq_u_r_kernel 同位接口；其非负/
   行归一证书在库内出节实测——CSM 件 uabp7we_rkern_nonneg 已消费定谳） *)
Variable K : S -> S -> R.
Hypothesis K_nonneg : forall s s' : S, le zero (K s s').

(* 收缩数据（UpReqSampling:125-127 同位） *)
Variable delta : R.
Variable delta_lt_one : lt delta one.

Let omd : R := req_minus one delta.

(* 步函数镜像位：u_step 同形接口化（库件 u_step:=sumf∘mult∘transition
   与 rsq_u_step_decomp 同形分解槽；本体零重证） *)
Variable u : S -> R.
Variable step : (S -> R) -> S -> R.
Hypothesis step_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (step mu s')
      (plus (mult delta (u s'))
            (mult omd (sumf (fun s : S => mult (mu s) (K s s'))))).

(* ============ 件 1：单 eps 尾注工具 ============ *)
(* le a b 的逐 eps 弱化：结论右端加正 eps 余量（链身各件从 plain 档 *)
(* 结论向逐 eps 档过渡的通用尾注；消费 lt_le_iff 的 Or 左支） *)
Lemma ua7c_le_plus_eps_r : forall (a b eps : R),
  le a b -> lt zero eps -> le a (plus b eps).
Proof.
  intros a b eps Hab Heps.
  exact (le_trans a b (plus b eps) Hab
           (req_le_plus_nonneg_r b eps (lt_le_iff zero eps (inl Heps)))).
Qed.

(* ============ 件 2：链身 eps 搬运核 ============ *)
(* 非负数乘把逐 eps 界按分配律搬运：omd 缩放 Hpt 支的搬运用核。
   证明路径：req_le_mult_compat_r 数乘保序 + distrib 左分配 req 链 +
   le_id_r 换尾。 *)
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

(* ============ 件 3：链根行墙逐 eps 形（CSM 件直连消费） ============ *)
(* rsq_u_abs_row 同形逐 eps 版：@ 全显消费姊妹件出节核
   uabp7we_abs_row_eps_absK（起点位），本节桩位全参对位。 *)
Lemma ua7c_abs_row_eps : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (K s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (@uabp7we_abs_row_eps_absK R RIS S sumf sum_ext abs_sum_le_eps_h
           K K_nonneg abs_ge_zero_req f s' eps Heps).
Qed.

(* ============ 件 4：逐点级链身逐 eps 镜像（Hpt 支） ============ *)
(* rsq_u_tv_contraction 的 Hpt 支（UpReqSampling:506-580）逐 eps 形：
   步差界以 omd 缩放的行和加 omd·eps 余量封口。证明路径：步差分解
   req 链（reqd_minus_compat + req_minus_plus_congr_l + req_minus_factor
   + reqd_sum_minus 反演 + sum_ext + req_minus_factor_pt，纯 req 代数
   零墙消费）逐字镜像 + req_abs_compat/abs_mult/abs_ge_zero_req 换头 +
   件 3 行墙逐 eps 消费经件 2 搬运核封尾。此为墙位以下可达的最大档：
   求和级（Hsum）即 🔒（见头注）。 *)
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

(* ============ 件 5：预算合成核（tv_iter 递归骨架的 eps 绕行件） ============ *)
(* rsq_u_tv_iter（UpReqSampling:669-690）的递归步（收缩一步 + 率数乘
   对位）在逐 eps 预算记账下的合成形态：两步预算 eps1、eps2 按率有限
   合成为 plus (率²·基) (plus (率·eps1) eps2)。证明路径：件 2 搬运核
   （率·预算分配）+ le_plus_compat 预算并档 + plus_assoc/le_id_r 换尾。
   全量 n 步封口仍需 🔒 绕行注记 (a)（有限世界），此处仅合成核。 *)
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

(* ============ 审计收尾段（逐件封闭判读，节外全显） ============ *)
Print Assumptions ua7c_le_plus_eps_r.
Print Assumptions ua7c_mult_le_plus_distr_r.
Print Assumptions ua7c_abs_row_eps.
Print Assumptions ua7c_hpt_eps.
Print Assumptions ua7c_budget_compose.
