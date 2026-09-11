(* ============================================================ *)
(* UpReqTVAbsEps.v — 席T9：定理 5.10 伴随件 tvd_abs_sum_le_list_eps *)
(*                                                               *)
(* 使命（席T8 施工图 C2 执行版）：Or 编码下零接口 eps 余量伴随件      *)
(*   forall (l : list (list Real)) (f : list Real -> Real) (eps),  *)
(*     real_lt real_zero eps ->                                    *)
(*     real_le (real_abs (real_list_sum (list Real) f l))          *)
(*             (real_plus (real_list_sum (list Real)               *)
(*                            (fun w => real_abs (f w)) l) eps).   *)
(* 铁律：UpTVDoeblin.v L1971-1975 的 Or 形前提位禁动——Or 形精确版    *)
(* 与 LPO 等价，构造性不可证；本伴随件是唯一合法产出（禁碰本体）。    *)
(* 载体：归纳变元 = list 本身（real_list_sum 三参形态与 real_plus   *)
(* 直接咬合）。半量取 h := (1/(1+1))·eps，三角形件与归纳前提各吃 h，  *)
(* h+h == eps 倍半归一收尾。                                        *)
(* 环境：monolith CW219（-Q ../attn/_build_219 ""，Live_X 树零 vo）； *)
(* QArith.Qring 供逐点 ring（UpTVDoeblin 头部同款）。全部名字可见性  *)
(* 已经 _t9_probe.v 实测（含 Locate S：CW219 顶层常量 S 存在，       *)
(* 本文件标识符一律避用 S）。                                       *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.

(* ---- 0. 逐点环恒等外提（UpTVDoeblin tvd_rring 同款独立副本：
        real_eq 目标 → 逐点 Q 恒等（ring 放电）。
        real_plus/real_mult/real_opp/real_minus_r/real_one/real_zero
        均透明，cbn [projT1 ...] 后逐点化简为 Q 表达式；
        real_abs/real_inv_pos 保持不透明（作原子参与 ring）。 ---- *)
Ltac tv9_rring :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_list_sum real_of_nat] in *;
  ring.

(* ---- 1. 严格平移（UpRealLeB real_lt_plus_r_zero 六行内联：
        0 < eps → y < y + eps；lt 平移 + y+0==y 换形） ---- *)
Lemma tv9_lt_plus_r_zero : forall (y eps : Real),
  real_lt real_zero eps -> real_lt y (real_plus y eps).
Proof.
  intros y eps Heps.
  apply (RealSetoid.real_lt_id_l y (real_plus y real_zero) (real_plus y eps)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_lt_plus_translate y real_zero eps). exact Heps.
Qed.

(* ---- 2. 二的正性（UpTVDoeblin tv_two_pos 同款独立副本：
        0 < 1+1；本文件自建避免库内同名引理的节绑定） ---- *)
Lemma tv9_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

(* ---- 3. 半量：tv9_half := 1/(1+1)（UpTVDoeblin tv_half 同款独立副本） ---- *)
Definition tv9_half : Real :=
  real_inv_pos (real_plus real_one real_one) tv9_two_pos.

Lemma tv9_half_pos : real_lt real_zero tv9_half.
Proof. exact (real_inv_pos_pos (real_plus real_one real_one) tv9_two_pos). Qed.

(* ---- 4. 倍半归一：(t·e)+(t·e) == e（t := 1/(1+1)，即 h+h == eps） ----
   eq 链：(t·e)+(t·e) == ((1+1)·t)·e（ring）
           == real_one·e（倒数律 real_inv_pos_correct，x 在左侧）
           == e（ring）。 ---- *)
Lemma tv9_double_inv : forall (t e : Real),
  real_eq (real_mult (real_plus real_one real_one) t) real_one ->
  real_eq (real_plus (real_mult t e) (real_mult t e)) e.
Proof.
  intros t e Hinv.
  apply (real_eq_trans
           (real_plus (real_mult t e) (real_mult t e))
           (real_mult (real_mult (real_plus real_one real_one) t) e)
           e).
  - tv9_rring.
  - apply (real_eq_trans
             (real_mult (real_mult (real_plus real_one real_one) t) e)
             (real_mult real_one e)
             e).
    + exact (RealSetoid.real_eq_mult_compat _ _ _ _ Hinv (real_eq_refl e)).
    + tv9_rring.
Qed.

(* ---- 5. 三角+归纳前提合流器（步例核心件，eq 链全部在此消化） ----
   给定 h 正、h+h == e、三角形实例 |a+b| ≤ (|a|+|b|)+h、
   归纳前提 |b| ≤ c+h，收出 |a+b| ≤ (|a|+c)+e。
   链路：|a|+|b| ≤ |a|+(c+h)（plus_compat）
         (|a|+|b|)+h ≤ (|a|+(c+h))+h（plus_compat 第二段）
         换形 (|a|+(c+h))+h == ((|a|+c)+h)+h == (|a|+c)+(h+h)
             == (|a|+c)+e（assoc 两步 + 倍半归一，real_le_id_r 运回）。 ---- *)
Lemma tv9_abs_triangle_ih : forall (a b c h e : Real),
  real_lt real_zero h ->
  real_eq (real_plus h h) e ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) (real_abs b)) h) ->
  real_le (real_abs b) (real_plus c h) ->
  real_le (real_abs (real_plus a b)) (real_plus (real_plus (real_abs a) c) e).
Proof.
  intros a b c h e Hh Ehh HTri HIH.
  assert (P2 : real_le (real_plus (real_abs a) (real_abs b))
                       (real_plus (real_abs a) (real_plus c h))).
  { exact (real_le_plus_compat (real_abs a) (real_abs a) (real_abs b)
             (real_plus c h) (real_le_refl (real_abs a)) HIH). }
  assert (P3 : real_le (real_plus (real_plus (real_abs a) (real_abs b)) h)
                       (real_plus (real_plus (real_abs a) (real_plus c h)) h)).
  { exact (real_le_plus_compat _ _ h h P2 (real_le_refl h)). }
  assert (HT : real_le (real_abs (real_plus a b))
                       (real_plus (real_plus (real_abs a) (real_plus c h)) h)).
  { exact (real_le_trans _ _ _ HTri P3). }
  apply (RealSetoid.real_le_id_r
           (real_abs (real_plus a b))
           (real_plus (real_plus (real_abs a) (real_plus c h)) h)
           (real_plus (real_plus (real_abs a) c) e)).
  - apply (real_eq_trans
             (real_plus (real_plus (real_abs a) (real_plus c h)) h)
             (real_plus (real_plus (real_plus (real_abs a) c) h) h)
             (real_plus (real_plus (real_abs a) c) e)).
    + exact (RealSetoid.real_eq_plus_compat _ h _ h
               (real_plus_assoc (real_abs a) c h) (real_eq_refl h)).
    + apply (real_eq_trans
               (real_plus (real_plus (real_plus (real_abs a) c) h) h)
               (real_plus (real_plus (real_abs a) c) (real_plus h h))
               (real_plus (real_plus (real_abs a) c) e)).
      * exact (real_eq_sym _ _
                 (real_plus_assoc (real_plus (real_abs a) c) h h)).
      * exact (RealSetoid.real_eq_plus_compat _ (real_plus h h) _ e
                 (real_eq_refl _) Ehh).
  - exact HT.
Qed.

(* ============================================================ *)
(* 主件：定理 5.10 伴随件（零接口，Or 编码余量 eps 逐字入语句）      *)
(* ============================================================ *)
Lemma tvd_abs_sum_le_list_eps :
  forall (l : list (list Real)) (f : list Real -> Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_abs (real_list_sum (list Real) f l))
            (real_plus (real_list_sum (list Real)
                          (fun w => real_abs (f w)) l) eps).
Proof.
  intros l f. induction l as [| w rest IH]; intros eps Heps.
  - (* 基例 []：cbn 后 |real_zero| ≤ real_zero + eps，
       走 left 严格支（real_lt_plus_r_zero 内联件），
       |0|==0 换形（real_abs_zero_req）经 real_lt_id_l。 *)
    cbn [real_list_sum].
    apply (RealSetoid.real_lt_le_iff_req (real_abs real_zero)
             (real_plus real_zero eps)). left.
    apply (RealSetoid.real_lt_id_l (real_abs real_zero) real_zero
             (real_plus real_zero eps)).
    + exact real_abs_zero_req.
    + exact (tv9_lt_plus_r_zero real_zero eps Heps).
  - (* 步例 w::rest：cbn 咬合 real_plus 后，三角形件与归纳前提
       各吃半量 h := tv9_half·eps（正性 real_mult_pos_compat），
       倍半归一 h+h==eps（tv9_double_inv + real_inv_pos_correct）
       交 tv9_abs_triangle_ih 一步收口。 *)
    cbn [real_list_sum].
    apply (tv9_abs_triangle_ih (f w)
             (real_list_sum (list Real) f rest)
             (real_list_sum (list Real)
                (fun w0 : list Real => real_abs (f w0)) rest)
             (real_mult tv9_half eps) eps).
    + exact (real_mult_pos_compat tv9_half eps tv9_half_pos Heps).
    + exact (tv9_double_inv tv9_half eps
               (real_inv_pos_correct (real_plus real_one real_one)
                  tv9_two_pos)).
    + exact (real_abs_triangle_le_eps (f w)
               (real_list_sum (list Real) f rest)
               (real_mult tv9_half eps)
               (real_mult_pos_compat tv9_half eps tv9_half_pos Heps)).
    + exact (IH (real_mult tv9_half eps)
               (real_mult_pos_compat tv9_half eps tv9_half_pos Heps)).
Qed.
