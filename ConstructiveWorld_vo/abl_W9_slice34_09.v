(* ==========================================================================
   abl_W9_slice34_09.v — 片 3：S11 死规格处置 + 片 4：arctan' 活位落地评估（源件 ConstructiveWorld_Live/S11_TP3B5.v，只读对照）。
   使命: 其一，B5A_Ode 节三个死规格 Variable（real_arctan_deriv L7588 /
     real_deriv_bound_lipschitz L7603 / real_deriv_zero_const L7617）与
     B5A_Item1 重声明（L8606）的处置论证与内容构造性落地其二；其二，
     B5A_Item1B 节活位 real_arctan_deriv（L11855）的落地评估登记。
   死规格判定事实：(a) 四个 Variable 名全库零跨件命中，件内命中仅声明位
     自身——Coq 节泛化语义下零使用 Variable 不进任何定理语句面；
   (b) real_deriv_bound_lipschitz / real_deriv_zero_const 语句面把 ∃δ 嵌在
     ∀x 之下（逐点模），逐点模⟹区间整体 Lipschitz 界在构造性框架无有限
     论证通路（需紧性）——落地须先修规格（δ 提至 ∀x 外层为真均匀模），
     修复形登记为后继方向，本件不越权代修；
   (c) real_arctan_deriv 的内容库内已有落地链——real_arctan_deriv_linear
     （L4586，|x|≤1/2）与 b3rr_real_arctan_deriv_linear（L5521，|x|≤r<1）。
     本件 Part 2 以库件为基，把死规格自身形状（b5a_one_plus_sq_pos 正性
     见证 + inv·h 乘序）在两子域构造性落地——据此退役成立。
   活位评估：活位类型为逐点 |x_n|≤1（闭单位域），库内落地链覆盖
     |x|≤1/2 与 |x|≤r<1（需一致内界 r），闭域点不能由 b3rr 实例化——
     活位精确类型不可由库内现成件 inhabits（Part 3 逐字复刻机器可查）。
     剩余工作两轴：轴一=arctan 加法公式件 + 闭域 Real 层装配；轴二=
     引用链改域（S12 已完成主体，见 b5c_vdh_pts_r 等闭式化件）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、S07_RealSetoidExpLog、
     S11_TP3B5；Stdlib QArith、Extraction。
   构造性: 纯构造性（承认类与经典类语句零字面零实质）；Set 层语句
     （real_le/real_lt/real_eq/QleT' 全 Set 层）；非平凡（死规格内容经
     witness 桥在两子域真落地，为库件真组合非转发占位）；可提取（Q 层
     采样 + 导数项 Real 层信息项，尾验 Print Assumptions 全 Closed）。
   编译配方：隔离池 /tmp/x9pool（S01-S11 真拷链），cpu_guard 包裹
     rocq c -q -native-compiler no -Q /tmp/x9pool "" 本件。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S11_TP3B5.

(* ============================================================ *)
(* Part 1 · witness 桥（死规格形状 ↔ 库落地件形状）                       *)
(*   差分三处之二：正性见证（b5a_one_plus_sq_pos vs b3r_one_sq_real_pos）  *)
(*   与乘序（real_mult inv·h vs real_mult h·inv）。差分之三（arctan x 的   *)
(*   域见证）由落地件语句面自带（b3r_half_dom/b3rr_dom_r1），不占桥。      *)
(* ============================================================ *)

(* 导数项桥：real_inv_pos 沿正性证明参的 Extensionality（库件 real_inv_pos_ext
   + real_eq_refl）⟹ 两见证产生的逆元 real_eq 相等；再乘序交换（real_mult_comm）。
   注意 real_inv_pos 定义体 destruct 证明参（S03:6684），两见证的逆元非转换
   相等——桥必须走 real_eq 层，此件即本桥的核。 *)
Lemma abl09_deriv_term_bridge : forall (x h : Real),
  real_eq
    (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                              (b5a_one_plus_sq_pos x)) h)
    (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                               (b3r_one_sq_real_pos x))).
Proof.
  intros x h.
  apply (real_eq_trans
           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                     (b5a_one_plus_sq_pos x)) h)
           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                     (b3r_one_sq_real_pos x)) h)
           (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                      (b3r_one_sq_real_pos x)))).
  - (* 同乘数：逆元沿见证参的 ext（同值两证明）*)
    apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos (real_plus real_one (real_mult x x))
                           (b5a_one_plus_sq_pos x)) h
             (real_inv_pos (real_plus real_one (real_mult x x))
                           (b3r_one_sq_real_pos x)) h).
    + exact (real_inv_pos_ext
               (real_plus real_one (real_mult x x))
               (real_plus real_one (real_mult x x))
               (b5a_one_plus_sq_pos x) (b3r_one_sq_real_pos x)
               (real_eq_refl (real_plus real_one (real_mult x x)))).
    + apply real_eq_refl.
  - (* 乘序交换 *)
    exact (real_mult_comm (real_inv_pos (real_plus real_one (real_mult x x))
                                        (b3r_one_sq_real_pos x)) h).
Qed.

(* 误差项桥：死规格形状（inv·h 乘序+b5a 见证）与库落地件形状（h·inv 乘序+
   b3r 见证）的 arctan' 误差项在 real_abs 下 real_eq 相等——经 plus/opp/abs
   三层 compat（库件 RealSetoid.real_eq_plus_compat/RealSetoid.real_eq_opp_compat/RealSetoid.real_eq_abs_compat）
   逐层下推到导数项桥。 *)
Lemma abl09_err_term_bridge :
  forall (x h : Real)
         (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
         (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_eq
    (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x Hx1)
                          (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                (b5a_one_plus_sq_pos x)) h)))))
    (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x Hx1)
                          (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                   (b3r_one_sq_real_pos x))))))).
Proof.
  intros x h Hxh Hx1.
  apply RealSetoid.real_eq_abs_compat.
  apply (RealSetoid.real_eq_plus_compat (cauchy_real_arctan (real_plus x h) Hxh)
                             (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                        (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                              (b5a_one_plus_sq_pos x)) h)))
                             (cauchy_real_arctan (real_plus x h) Hxh)
                             (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                        (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                                 (b3r_one_sq_real_pos x)))))).
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_opp_compat.
    apply (RealSetoid.real_eq_plus_compat (cauchy_real_arctan x Hx1)
                               (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                  (b5a_one_plus_sq_pos x)) h)
                               (cauchy_real_arctan x Hx1)
                               (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b3r_one_sq_real_pos x)))).
    + apply real_eq_refl.
    + exact (abl09_deriv_term_bridge x h).
Qed.

(* real_le 沿左目 real_eq 的转移（库件 RealSetoid.real_le_compat 的本件工作形）：
   库落地件给的是「h·inv 乘序形状 ≤ 界」，本件经桥换得「inv·h 死规格形状 ≤ 同界」。 *)
Lemma abl09_le_swap_generic :
  forall (x h C : Real)
         (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
         (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))))) C ->
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b5a_one_plus_sq_pos x)) h))))) C.
Proof.
  intros x h C Hxh Hx1 Hle.
  apply (RealSetoid.real_le_compat
           (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b3r_one_sq_real_pos x)))))))
           (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                 (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                      (b5a_one_plus_sq_pos x)) h)))))
           C C).
  - exact (real_eq_sym _ _ (abl09_err_term_bridge x h Hxh Hx1)).
  - apply real_eq_refl.
  - exact Hle.
Qed.

(* ============================================================ *)
(* Part 2 · 片 3 主刀：B5A_Ode 死规格 real_arctan_deriv 内容构造性落地其二   *)
(*   死规格自身形状（b5a_one_plus_sq_pos 见证 + inv·h 乘序 + Hxh 闭域证书）  *)
(*   在 |x|≤1/2 与 |x|≤r<1 两子域落地。原 Variable 位（L7588/L8606）至此     *)
(*   「内容已由库链覆盖」机器可查；退役登记见文件头 (c)。                  *)
(* ============================================================ *)

(* 落地件一：|x|≤1/2 子域（库基 real_arctan_deriv_linear，L4586，30 Qed） *)
Theorem abl09_b5a_spec_half_dom :
  forall (x : Real) (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) (Qinv 2)),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hxb eps Heps.
  destruct (real_arctan_deriv_linear x Hxb eps Heps) as [d [Hd0 Hdh]].
  exists d. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    exact (abl09_le_swap_generic x h (real_plus (real_mult eps (real_abs h)) eps')
             Hxh (b3r_half_dom x Hxb) (Hdh h Hh Hxh eps' Heps')).
Qed.

(* 落地件二：|x|≤r<1 子域（库基 b3rr_real_arctan_deriv_linear，L5521，20 Qed，
   S12 已引用的同族件）——任意内界 r，覆盖全部严格内点 *)
Theorem abl09_b5a_spec_r_dom :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxb eps Heps.
  destruct (b3rr_real_arctan_deriv_linear r Hr0 Hr1 x Hxb eps Heps) as [d [Hd0 Hdh]].
  exists d. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    exact (abl09_le_swap_generic x h (real_plus (real_mult eps (real_abs h)) eps')
             Hxh (b3rr_dom_r1 x r Hxb Hr1) (Hdh h Hh Hxh eps' Heps')).
Qed.

(* ============================================================ *)
(* Part 3 · 片 4 评估机器锚：活位精确类型逐字复刻（L11855 原文）            *)
(*   本 Definition 通过类型检查即证「复刻与源件活位类型逐字一致」；           *)
(*   其不可由库内现成件 inhabits 的结论（闭域 vs 一致内界 r）见文件头 (b)(c) *)
(*   ——评估登记形态，非落地件。                                            *)
(* ============================================================ *)

Definition abl09_item1b_live_spec : Type :=
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* Part 4 · 可提取性检验（信息性面 + Obj.magic=0）                           *)
(*   Q 层采样：arctan' 导数形状 1/(1+t²) 的 Q 采样（本刀消融对象的计算核）。  *)
(*   Real 层信息项：导数项 real_inv_pos(1+x²) 信息性面（本刀桥对象的计算面）。*)
(* ============================================================ *)

Definition abl09_probe_q (t : Q) : Q := Qplus t (Qinv (Qplus (1 # 2) (t * t))).

Definition abl09_probe_deriv_term (x : Real) : Real :=
  real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x).

Recursive Extraction abl09_probe_q.
Recursive Extraction abl09_probe_deriv_term.

(* ============================================================ *)
(* Part 5 · 尾验：Print Assumptions 全件（3 桥 + 2 落地件 = 5 Qed 对账）    *)
(* ============================================================ *)

Print Assumptions abl09_deriv_term_bridge.
Print Assumptions abl09_err_term_bridge.
Print Assumptions abl09_le_swap_generic.
Print Assumptions abl09_b5a_spec_half_dom.
Print Assumptions abl09_b5a_spec_r_dom.
