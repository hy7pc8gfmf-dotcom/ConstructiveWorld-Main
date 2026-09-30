(* ==========================================================================)
   abl_arctan_cert_bridge_21.v — X24' Real 证书桥预制（arctan' 轴一支援件）      
   消融批 · 断点②判定接刀：Q 供给 4 件 → Real 层证书桥（独立新件）         
   ── 件名 ──────────────────────────────────────────────────────────────────
   abl_arctan_cert_bridge_21 · X24' 预制 · 消融批          
   ── 本片范围·数学使命（切片规格 ≤1h；X19' 登记册 §四·断点②「接续首刀」预制）：─────
   依赖：Q 供给 4 件（abl_arctan_diff_19：无除法多项式核 abl9_wsq_ring_id /
   abl9_wincr_ring_id ＋分母非零除法形 abl9_wsq_div_id / abl9_wincr_div_id）。
   输出=Real 层证书桥——把 Q 层恒等式经 cauchy Real 承载件（real_inv_pos /
   real_plus / real_mult / real_opp 投影件）升到 real 层陈述：
   （a）w Real 构造件 abl9_brg_w_real（w(u):=real_mult (u−v) (inv_pos (1+uv))）
        ＋终近逐点投影件 abl9_brg_w_proj ＋证书无关件 abl9_brg_w_ext
        （real_inv_pos_ext S07:L6757对齐——X19' 登记册点名目标）；
   （b）1+w² 恒等 Real 桥 abl9_brg_wsq_real（除法形，引擎=abl9_wsq_div_id）
        ＋其无除法核形 abl9_brg_wsq_real_kernel（引擎=abl9_wsq_ring_id）；
   （c）w 增量恒等 Real 桥 abl9_brg_wincr_real（除法形，引擎=abl9_wincr_div_id）
        ＋其无除法核形 abl9_brg_wincr_real_kernel（引擎=abl9_wincr_ring_id）；
   （d）|w|<1 全 n 域证书 abl9_brg_w_dom（|u|,|v|≤1/4 ⟹ |w|≤8/15<1——
        8/15 界；早尾两支实算：real_inv_pos 早项=Qinv(D_N0) 同受 15/16 界，
        承 S03:L6685 定义形）——cauchy_real_arctan 域证书 b3rr_dom_r1 配形。
   构造性注记：桥止于「Q恒等式→real 层 real_eq 陈述」；主公式
   abl9_atan_diff_formula 装配（phi 步界/常值判据/端点）仍属 9a-乙 主线断点，
   本件不越界（供主公式装配直接Require 闭合）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x24pool "" /tmp/x24pool/abl_arctan_cert_bridge_21.v
   （隔离池 /tmp/x24pool=x19pool 现势链真拷：S01–S11+abl_arctan_diff_16+
   abl_arctan_diff_19 born-in-place 绿 .vo 共 15；S11 md5 d571b0c0 与
   X19'/X19''登记册登记SAME（Live现势已漂，池以登记册认证值为准，保证与施工中
   件 19/20 同链）；abl_arctan_diff_20不入池（X19'' 施工中辖区，禁触）。
   Require 链退回 S11 单链，S12 出锥——承 X15''/X16/X19' 判定。）
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
Require Import abl_arctan_diff_19.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 基建：终近逐点相等 → real_eq（real_eq_of_zero_diff S02:L2317   *)
(*   的 N>0 版推广——桥的全部 real_eq 目标的统一闭合器）。           *)
(*   工法注：见证 N 显式入参（非 ex 假设）——Prop-ex 不可消去入     *)
(*   Set 层 real_eq 目标（排序纪律），见证改走实参通道。           *)
(* ============================================================ *)
Lemma abl9_brg_pt_eq : forall (X Y : Real) (N : nat),
  (forall n : nat, (N <= n)%nat -> projT1 X n == projT1 Y n) ->
  real_eq X Y.
Proof.
  intros X Y N HN eps Heps.
  exists N. intros n Hn.
  apply NatLe_drop in Hn.
  assert (Hz : projT1 X n - projT1 Y n == 0).
  { rewrite (HN n Hn). ring. }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hd : Qabs (projT1 X n - projT1 Y n) == 0) by (rewrite Hz; reflexivity).
  assert (Hcmp : Qcompare (Qabs (projT1 X n - projT1 Y n)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (projT1 X n - projT1 Y n)) eps = Qcompare 0 eps)
      by (exact (Qcompare_comp (Qabs (projT1 X n - projT1 Y n)) 0 Hd eps eps
                   (Qeq_refl eps))).
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(* Q 引擎 1：1+w² 恒等的点形（引擎=Q 供给构造 abl9_wsq_div_id；      *)
(*   Qinv(·) 积形经 Qinv_mult_distr 与 / 形对齐）。                 *)
(* ============================================================ *)
Lemma abl9_brg_wsq_pt : forall a b : Q,
  ~ (1 + a * b == 0) ->
  1 + (a - b) * Qinv (1 + a * b) * ((a - b) * Qinv (1 + a * b)) ==
  (1 + a * a) * (1 + b * b) * (Qinv (1 + a * b) * Qinv (1 + a * b)).
Proof.
  intros a b Hnz.
  assert (Hcore := abl9_wsq_div_id a b Hnz).
  unfold Qdiv in Hcore.
  rewrite (Qinv_mult_distr (1 + a * b) (1 + a * b)) in Hcore.
  apply (Qeq_trans
          (1 + (a - b) * Qinv (1 + a * b) * ((a - b) * Qinv (1 + a * b)))
          (1 + (a - b) * (a - b) * (Qinv (1 + a * b) * Qinv (1 + a * b)))
          ((1 + a * a) * (1 + b * b) * (Qinv (1 + a * b) * Qinv (1 + a * b)))).
  - ring.
  - exact Hcore.
Qed.

(* ============================================================ *)
(* Q 引擎 2：w 增量恒等的点形（引擎=Q 供给构造 abl9_wincr_div_id）。 *)
(* ============================================================ *)
Lemma abl9_brg_wincr_pt : forall a b s : Q,
  ~ (1 + (a + s) * b == 0) -> ~ (1 + a * b == 0) ->
  (a + s - b) * Qinv (1 + (a + s) * b) - (a - b) * Qinv (1 + a * b) ==
  s * (1 + b * b) * (Qinv (1 + (a + s) * b) * Qinv (1 + a * b)).
Proof.
  intros a b s H1 H2.
  assert (Hcore := abl9_wincr_div_id a b s H1 H2).
  unfold Qdiv in Hcore.
  rewrite (Qinv_mult_distr (1 + (a + s) * b) (1 + a * b)) in Hcore.
  exact Hcore.
Qed.

(* ============================================================ *)
(* Q 引擎 3：1+w² 核形的点形（引擎=Q 供给构造 abl9_wsq_ring_id；     *)
(*   D·Qinv D==1 经 Qmult_inv_r（非零形，Qeq 口径）。               *)
(* ============================================================ *)
Lemma abl9_brg_wsq_kernel_pt : forall a b : Q,
  ~ (1 + a * b == 0) ->
  (1 + a * b) * (1 + a * b)
    * (1 + (a - b) * Qinv (1 + a * b) * ((a - b) * Qinv (1 + a * b))) ==
  (1 + a * a) * (1 + b * b).
Proof.
  intros a b Hnz.
  assert (Hinv : (1 + a * b) * Qinv (1 + a * b) == 1)
    by (apply Qmult_inv_r; exact Hnz).
  assert (Hcore := abl9_wsq_ring_id a b).
  assert (Hstep : (1 + a * b) * (1 + a * b)
           * (1 + (a - b) * Qinv (1 + a * b) * ((a - b) * Qinv (1 + a * b)))
           == (1 + a * b) * (1 + a * b)
              + (a - b) * (a - b)
                * ((1 + a * b) * Qinv (1 + a * b))
                * ((1 + a * b) * Qinv (1 + a * b))).
  { ring. }
  rewrite Hstep. rewrite Hinv.
  apply (Qeq_trans _ ((1 + a * b) * (1 + a * b) + (a - b) * (a - b)) _).
  - ring.
  - exact Hcore.
Qed.

(* ============================================================ *)
(* Q 引擎 4：w 增量核形的点形（引擎=Q 供给构造 abl9_wincr_ring_id）。*)
(* ============================================================ *)
Lemma abl9_brg_wincr_kernel_pt : forall a b s : Q,
  ~ (1 + (a + s) * b == 0) -> ~ (1 + a * b == 0) ->
  (1 + (a + s) * b) * (1 + a * b)
    * ((a + s - b) * Qinv (1 + (a + s) * b) - (a - b) * Qinv (1 + a * b)) ==
  s * (1 + b * b).
Proof.
  intros a b s H1 H2.
  assert (Hinv1 : (1 + (a + s) * b) * Qinv (1 + (a + s) * b) == 1)
    by (apply Qmult_inv_r; exact H1).
  assert (Hinv2 : (1 + a * b) * Qinv (1 + a * b) == 1)
    by (apply Qmult_inv_r; exact H2).
  assert (Hcore := abl9_wincr_ring_id a b s).
  assert (Hshape : (1 + (a + s) * b) * (1 + a * b)
           * ((a + s - b) * Qinv (1 + (a + s) * b)
              - (a - b) * Qinv (1 + a * b))
           == (a + s - b)
              * ((1 + a * b)
                 * ((1 + (a + s) * b) * Qinv (1 + (a + s) * b)))
              - (a - b)
              * ((1 + (a + s) * b)
                 * ((1 + a * b) * Qinv (1 + a * b)))).
  { ring. }
  rewrite Hshape. rewrite Hinv1. rewrite Hinv2.
  apply (Qeq_trans _ ((a + s - b) * (1 + a * b)
                      - (a - b) * (1 + (a + s) * b)) _).
  - ring.
  - exact Hcore.
Qed.

(* ============================================================ *)
(* （a）w Real 构造件：w(u,v) := (u−v)·inv(1+uv)（real_inv_pos       *)
(*   承载，正性证书显式入参——X19' 登记册 §四·1(a) 原文形）。          *)
(* ============================================================ *)
Definition abl9_brg_w_real (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v))) : Real :=
  real_mult (real_plus u (real_opp v))
            (real_inv_pos (real_plus real_one (real_mult u v)) Huv).

(* w 的终近逐点投影件（real_inv_proj S09:L1446 单发直取；sigT Set 层形，   *)
(*   供任意目标层位 destruct——承 real_inv_proj 同款封装）。               *)
Lemma abl9_brg_w_proj : forall (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v))),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    projT1 (abl9_brg_w_real u v Huv) n ==
    (projT1 u n - projT1 v n) * Qinv (1 + projT1 u n * projT1 v n)).
Proof.
  intros u v Huv. unfold abl9_brg_w_real.
  destruct (real_inv_proj (real_plus real_one (real_mult u v)) Huv)
    as [Ninv HNinv].
  exists Ninv. intros n Hn.
  rewrite (real_mult_proj (real_plus u (real_opp v))
             (real_inv_pos (real_plus real_one (real_mult u v)) Huv) n).
  rewrite (real_plus_proj u (real_opp v) n).
  rewrite (real_opp_proj v n).
  rewrite (HNinv n Hn).
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  reflexivity.
Qed.

(* （a·对齐）证书无关件：real_inv_pos_ext（S07:L6757）对齐——        *)
(*   w 不依赖正性证书的选取（X19' 登记册点名对齐目标）。              *)
Lemma abl9_brg_w_ext : forall (u v : Real)
  (Huv Huv' : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq (abl9_brg_w_real u v Huv) (abl9_brg_w_real u v Huv').
Proof.
  intros u v Huv Huv'.
  unfold abl9_brg_w_real.
  apply (RealSetoid.real_eq_mult_compat (real_plus u (real_opp v))
          (real_inv_pos (real_plus real_one (real_mult u v)) Huv)
          (real_plus u (real_opp v))
          (real_inv_pos (real_plus real_one (real_mult u v)) Huv')).
  - apply real_eq_refl.
  - apply (real_inv_pos_ext (real_plus real_one (real_mult u v))
             (real_plus real_one (real_mult u v)) Huv Huv').
    apply real_eq_refl.
Qed.

(* D² 正性（real_mult_positive S07:L6999 直发——桥 B 的 RHS 证书） *)
Lemma abl9_brg_Dsq_pos : forall (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_lt real_zero
    (real_mult (real_plus real_one (real_mult u v))
               (real_plus real_one (real_mult u v))).
Proof.
  intros u v Huv.
  exact (real_mult_positive (real_plus real_one (real_mult u v))
           (real_plus real_one (real_mult u v)) Huv Huv).
Qed.

(* ============================================================ *)
(* （b）1+w² 恒等 Real 桥（除法形）：                               *)
(*   1+w² == (1+u²)(1+v²)·inv((1+uv)²)（real_eq 层）。              *)
(*   逐点引擎=Q 供给构造 abl9_wsq_div_id（经 abl9_brg_wsq_pt）。     *)
(* ============================================================ *)
Lemma abl9_brg_wsq_real : forall (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq
    (real_plus real_one
       (real_mult (abl9_brg_w_real u v Huv) (abl9_brg_w_real u v Huv)))
    (real_mult
       (real_mult (real_plus real_one (real_mult u u))
                  (real_plus real_one (real_mult v v)))
       (real_inv_pos (real_mult (real_plus real_one (real_mult u v))
                                (real_plus real_one (real_mult u v)))
                     (abl9_brg_Dsq_pos u v Huv))).
Proof.
  intros u v Huv.
  pose proof Huv as HuvC. destruct HuvC as [e0 [He0 [N0 HN0]]].
  destruct (abl9_brg_w_proj u v Huv) as [Nw HNw].
  destruct (real_inv_proj (real_mult (real_plus real_one (real_mult u v))
                            (real_plus real_one (real_mult u v)))
                          (abl9_brg_Dsq_pos u v Huv)) as [ND HND].
  apply (abl9_brg_pt_eq _ _ (Nat.max Nw (Nat.max ND N0))).
  intros n Hn.
  assert (Hnw : (Nw <= n)%nat) by lia.
  assert (Hnd : (ND <= n)%nat) by lia.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hlt : Qlt 0 (1 + projT1 u n * projT1 v n)).
  { apply (Qlt_le_trans 0 (projT1 (real_plus real_one (real_mult u v)) n
                             - projT1 real_zero n)
                         (1 + projT1 u n * projT1 v n)).
    - apply (Qlt_trans 0 e0 _).
      + apply QltT_to_Qlt. exact He0.
      + apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. exact Hn0.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one (real_mult u v) n).
      rewrite (real_mult_proj u v n).
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz : ~ (1 + projT1 u n * projT1 v n == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt).
    apply Qeq_sym. exact Hz. }
  rewrite (real_plus_proj real_one
             (real_mult (abl9_brg_w_real u v Huv)
                        (abl9_brg_w_real u v Huv)) n).
  rewrite (real_mult_proj (abl9_brg_w_real u v Huv)
             (abl9_brg_w_real u v Huv) n).
  rewrite (b3r_one_proj n).
  rewrite (HNw n Hnw).
  rewrite (real_mult_proj
             (real_mult (real_plus real_one (real_mult u u))
                        (real_plus real_one (real_mult v v)))
             (real_inv_pos (real_mult (real_plus real_one (real_mult u v))
                                      (real_plus real_one (real_mult u v)))
                           (abl9_brg_Dsq_pos u v Huv)) n).
  rewrite (real_mult_proj (real_plus real_one (real_mult u u))
             (real_plus real_one (real_mult v v)) n).
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (real_plus_proj real_one (real_mult v v) n).
  rewrite (real_mult_proj v v n).
  rewrite (b3r_one_proj n).
  rewrite (HND n Hnd).
  rewrite (real_mult_proj (real_plus real_one (real_mult u v))
             (real_plus real_one (real_mult u v)) n).
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  rewrite (Qinv_mult_distr (1 + projT1 u n * projT1 v n)
                           (1 + projT1 u n * projT1 v n)).
  apply (abl9_brg_wsq_pt (projT1 u n) (projT1 v n) Hnz).
Qed.

(* ============================================================ *)
(* （b·核形）1+w² 恒等 Real 桥（无除法形，交叉相乘）：               *)
(*   (1+uv)²·(1+w²) == (1+u²)(1+v²)（real_eq 层）。                 *)
(*   逐点引擎=Q 供给构造 abl9_wsq_ring_id（经abl9_brg_wsq_kernel_pt）。*)
(* ============================================================ *)
Lemma abl9_brg_wsq_real_kernel : forall (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq
    (real_mult (real_mult (real_plus real_one (real_mult u v))
                          (real_plus real_one (real_mult u v)))
               (real_plus real_one
                  (real_mult (abl9_brg_w_real u v Huv)
                             (abl9_brg_w_real u v Huv))))
    (real_mult (real_plus real_one (real_mult u u))
               (real_plus real_one (real_mult v v))).
Proof.
  intros u v Huv.
  pose proof Huv as HuvC. destruct HuvC as [e0 [He0 [N0 HN0]]].
  destruct (abl9_brg_w_proj u v Huv) as [Nw HNw].
  apply (abl9_brg_pt_eq _ _ (Nat.max Nw N0)).
  intros n Hn.
  assert (Hnw : (Nw <= n)%nat) by lia.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hlt : Qlt 0 (1 + projT1 u n * projT1 v n)).
  { apply (Qlt_le_trans 0 (projT1 (real_plus real_one (real_mult u v)) n
                             - projT1 real_zero n)
                         (1 + projT1 u n * projT1 v n)).
    - apply (Qlt_trans 0 e0 _).
      + apply QltT_to_Qlt. exact He0.
      + apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. exact Hn0.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one (real_mult u v) n).
      rewrite (real_mult_proj u v n).
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz : ~ (1 + projT1 u n * projT1 v n == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt).
    apply Qeq_sym. exact Hz. }
  rewrite (real_mult_proj (real_mult (real_plus real_one (real_mult u v))
                            (real_plus real_one (real_mult u v)))
             (real_plus real_one
                (real_mult (abl9_brg_w_real u v Huv)
                           (abl9_brg_w_real u v Huv))) n).
  rewrite (real_mult_proj (real_plus real_one (real_mult u v))
             (real_plus real_one (real_mult u v)) n).
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  rewrite (real_plus_proj real_one
             (real_mult (abl9_brg_w_real u v Huv)
                        (abl9_brg_w_real u v Huv)) n).
  rewrite (real_mult_proj (abl9_brg_w_real u v Huv)
             (abl9_brg_w_real u v Huv) n).
  rewrite (b3r_one_proj n).
  rewrite (HNw n Hnw).
  rewrite (real_mult_proj (real_plus real_one (real_mult u u))
             (real_plus real_one (real_mult v v)) n).
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (real_plus_proj real_one (real_mult v v) n).
  rewrite (real_mult_proj v v n).
  rewrite (b3r_one_proj n).
  apply (abl9_brg_wsq_kernel_pt (projT1 u n) (projT1 v n) Hnz).
Qed.

(* ============================================================ *)
(* （c）w 增量恒等 Real 桥（除法形）：                              *)
(*   w(u+h,v)−w(u,v) == h(1+v²)·inv((1+(u+h)v)(1+uv))（real_eq 层）。*)
(*   逐点引擎=Q 供给构造 abl9_wincr_div_id（经 abl9_brg_wincr_pt）。 *)
(* ============================================================ *)
Lemma abl9_brg_wincr_real : forall (u h v : Real)
  (H1 : real_lt real_zero
          (real_plus real_one (real_mult (real_plus u h) v)))
  (H2 : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq
    (real_plus (abl9_brg_w_real (real_plus u h) v H1)
               (real_opp (abl9_brg_w_real u v H2)))
    (real_mult
       (real_mult h (real_plus real_one (real_mult v v)))
       (real_inv_pos
          (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                     (real_plus real_one (real_mult u v)))
          (real_mult_positive
             (real_plus real_one (real_mult (real_plus u h) v))
             (real_plus real_one (real_mult u v)) H1 H2))).
Proof.
  intros u h v H1 H2.
  pose proof H1 as H1C. destruct H1C as [e1 [He1 [M1 HM1]]].
  pose proof H2 as H2C. destruct H2C as [e2 [He2 [M2 HM2]]].
  destruct (abl9_brg_w_proj (real_plus u h) v H1) as [Nw1 HNw1].
  destruct (abl9_brg_w_proj u v H2) as [Nw2 HNw2].
  destruct (real_inv_proj
              (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                         (real_plus real_one (real_mult u v)))
              (real_mult_positive
                 (real_plus real_one (real_mult (real_plus u h) v))
                 (real_plus real_one (real_mult u v)) H1 H2)) as [ND HND].
  apply (abl9_brg_pt_eq _ _
           (Nat.max Nw1 (Nat.max Nw2 (Nat.max ND (Nat.max M1 M2))))).
  intros n Hn.
  assert (Hnw1 : (Nw1 <= n)%nat) by lia.
  assert (Hnw2 : (Nw2 <= n)%nat) by lia.
  assert (Hnd : (ND <= n)%nat) by lia.
  assert (Hm1 : (M1 <= n)%nat) by lia.
  assert (Hm2 : (M2 <= n)%nat) by lia.
  assert (Huhp : projT1 (real_plus u h) n == projT1 u n + projT1 h n)
    by (apply real_plus_proj).
  assert (Hlt1 : Qlt 0 (1 + (projT1 u n + projT1 h n) * projT1 v n)).
  { apply (Qlt_le_trans 0
             (projT1 (real_plus real_one (real_mult (real_plus u h) v)) n
              - projT1 real_zero n)
             (1 + (projT1 u n + projT1 h n) * projT1 v n)).
    - apply (Qlt_trans 0 e1 _).
      + apply QltT_to_Qlt. exact He1.
      + apply QltT_to_Qlt. apply (HM1 n). apply NatLe_lift. exact Hm1.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one
                 (real_mult (real_plus u h) v) n).
      rewrite (real_mult_proj (real_plus u h) v n).
      rewrite Huhp.
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz1 : ~ (1 + (projT1 u n + projT1 h n) * projT1 v n == 0)).
  { intro Hz.
    apply (Qlt_not_eq 0 (1 + (projT1 u n + projT1 h n) * projT1 v n) Hlt1).
    apply Qeq_sym. exact Hz. }
  assert (Hlt2 : Qlt 0 (1 + projT1 u n * projT1 v n)).
  { apply (Qlt_le_trans 0 (projT1 (real_plus real_one (real_mult u v)) n
                             - projT1 real_zero n)
                         (1 + projT1 u n * projT1 v n)).
    - apply (Qlt_trans 0 e2 _).
      + apply QltT_to_Qlt. exact He2.
      + apply QltT_to_Qlt. apply (HM2 n). apply NatLe_lift. exact Hm2.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one (real_mult u v) n).
      rewrite (real_mult_proj u v n).
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz2 : ~ (1 + projT1 u n * projT1 v n == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt2).
    apply Qeq_sym. exact Hz. }
  rewrite (real_plus_proj (abl9_brg_w_real (real_plus u h) v H1)
             (real_opp (abl9_brg_w_real u v H2)) n).
  rewrite (real_opp_proj (abl9_brg_w_real u v H2) n).
  rewrite (HNw1 n Hnw1). rewrite Huhp.
  rewrite (HNw2 n Hnw2).
  rewrite (real_mult_proj
             (real_mult h (real_plus real_one (real_mult v v)))
             (real_inv_pos
                (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                           (real_plus real_one (real_mult u v)))
                (real_mult_positive
                   (real_plus real_one (real_mult (real_plus u h) v))
                   (real_plus real_one (real_mult u v)) H1 H2)) n).
  rewrite (real_mult_proj h (real_plus real_one (real_mult v v)) n).
  rewrite (real_plus_proj real_one (real_mult v v) n).
  rewrite (real_mult_proj v v n).
  rewrite (b3r_one_proj n).
  rewrite (HND n Hnd).
  rewrite (real_mult_proj (real_plus real_one (real_mult (real_plus u h) v))
             (real_plus real_one (real_mult u v)) n).
  rewrite (real_plus_proj real_one (real_mult (real_plus u h) v) n).
  rewrite (real_mult_proj (real_plus u h) v n).
  rewrite Huhp.
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  rewrite (Qinv_mult_distr (1 + (projT1 u n + projT1 h n) * projT1 v n)
                           (1 + projT1 u n * projT1 v n)).
  apply (abl9_brg_wincr_pt (projT1 u n) (projT1 v n) (projT1 h n) Hnz1 Hnz2).
Qed.

(* ============================================================ *)
(* （c·核形）w 增量恒等 Real 桥（无除法形，交叉相乘）：              *)
(*   (1+(u+h)v)(1+uv)·(w(u+h,v)−w(u,v)) == h(1+v²)（real_eq 层）。  *)
(*   逐点引擎=Q 供给构造 abl9_wincr_ring_id（经 abl9_brg_wincr_kernel_pt）。*)
(* ============================================================ *)
Lemma abl9_brg_wincr_real_kernel : forall (u h v : Real)
  (H1 : real_lt real_zero
          (real_plus real_one (real_mult (real_plus u h) v)))
  (H2 : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq
    (real_mult
       (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                  (real_plus real_one (real_mult u v)))
       (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                  (real_opp (abl9_brg_w_real u v H2))))
    (real_mult h (real_plus real_one (real_mult v v))).
Proof.
  intros u h v H1 H2.
  pose proof H1 as H1C. destruct H1C as [e1 [He1 [M1 HM1]]].
  pose proof H2 as H2C. destruct H2C as [e2 [He2 [M2 HM2]]].
  destruct (abl9_brg_w_proj (real_plus u h) v H1) as [Nw1 HNw1].
  destruct (abl9_brg_w_proj u v H2) as [Nw2 HNw2].
  apply (abl9_brg_pt_eq _ _ (Nat.max Nw1 (Nat.max Nw2 (Nat.max M1 M2)))).
  intros n Hn.
  assert (Hnw1 : (Nw1 <= n)%nat) by lia.
  assert (Hnw2 : (Nw2 <= n)%nat) by lia.
  assert (Hm1 : (M1 <= n)%nat) by lia.
  assert (Hm2 : (M2 <= n)%nat) by lia.
  assert (Huhp : projT1 (real_plus u h) n == projT1 u n + projT1 h n)
    by (apply real_plus_proj).
  assert (Hlt1 : Qlt 0 (1 + (projT1 u n + projT1 h n) * projT1 v n)).
  { apply (Qlt_le_trans 0
             (projT1 (real_plus real_one (real_mult (real_plus u h) v)) n
              - projT1 real_zero n)
             (1 + (projT1 u n + projT1 h n) * projT1 v n)).
    - apply (Qlt_trans 0 e1 _).
      + apply QltT_to_Qlt. exact He1.
      + apply QltT_to_Qlt. apply (HM1 n). apply NatLe_lift. exact Hm1.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one
                 (real_mult (real_plus u h) v) n).
      rewrite (real_mult_proj (real_plus u h) v n).
      rewrite Huhp.
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz1 : ~ (1 + (projT1 u n + projT1 h n) * projT1 v n == 0)).
  { intro Hz.
    apply (Qlt_not_eq 0 (1 + (projT1 u n + projT1 h n) * projT1 v n) Hlt1).
    apply Qeq_sym. exact Hz. }
  assert (Hlt2 : Qlt 0 (1 + projT1 u n * projT1 v n)).
  { apply (Qlt_le_trans 0 (projT1 (real_plus real_one (real_mult u v)) n
                             - projT1 real_zero n)
                         (1 + projT1 u n * projT1 v n)).
    - apply (Qlt_trans 0 e2 _).
      + apply QltT_to_Qlt. exact He2.
      + apply QltT_to_Qlt. apply (HM2 n). apply NatLe_lift. exact Hm2.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one (real_mult u v) n).
      rewrite (real_mult_proj u v n).
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz2 : ~ (1 + projT1 u n * projT1 v n == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt2).
    apply Qeq_sym. exact Hz. }
  rewrite (real_mult_proj
             (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                        (real_plus real_one (real_mult u v)))
             (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                        (real_opp (abl9_brg_w_real u v H2))) n).
  rewrite (real_mult_proj (real_plus real_one (real_mult (real_plus u h) v))
             (real_plus real_one (real_mult u v)) n).
  rewrite (real_plus_proj real_one (real_mult (real_plus u h) v) n).
  rewrite (real_mult_proj (real_plus u h) v n).
  rewrite Huhp.
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  rewrite (real_plus_proj (abl9_brg_w_real (real_plus u h) v H1)
             (real_opp (abl9_brg_w_real u v H2)) n).
  rewrite (real_opp_proj (abl9_brg_w_real u v H2) n).
  rewrite (HNw1 n Hnw1).
  rewrite (HNw2 n Hnw2).
  rewrite Huhp.
  rewrite (real_mult_proj h (real_plus real_one (real_mult v v)) n).
  rewrite (real_plus_proj real_one (real_mult v v) n).
  rewrite (real_mult_proj v v n).
  rewrite (b3r_one_proj n).
  apply (abl9_brg_wincr_kernel_pt (projT1 u n) (projT1 v n) (projT1 h n)
           Hnz1 Hnz2).
Qed.

(* ============================================================ *)
(* （d）|w|<1 域证书的 Q 点件：|a|,|b|≤1/4 ⟹ |(a−b)·Qinv(1+ab)|≤1。 *)
(*   算术链：|a−b|≤1/2；1+ab≥15/16>0 ⟹ Qinv(1+ab)≤16/15；           *)
(*   积 ≤ (1/2)(16/15)=8/15<1——8/15 界（X19' 登记册 §四·1(c)）。     *)
(* ============================================================ *)
Lemma abl9_brg_winv_bnd : forall a1 b1 a2 b2 : Q,
  QleT' (Qabs a1) (1 # 4) -> QleT' (Qabs b1) (1 # 4) ->
  QleT' (Qabs a2) (1 # 4) -> QleT' (Qabs b2) (1 # 4) ->
  QleT' (Qabs ((a1 - b1) * Qinv (1 + a2 * b2))) 1.
Proof.
  intros a1 b1 a2 b2 Ha1 Hb1 Ha2 Hb2.
  apply Qle_to_QleT'.
  assert (Hab : Qle (Qabs (a1 - b1)) (1 # 2)).
  { apply (Qle_trans _ (Qabs a1 + Qabs (- b1)) _).
    - apply (Qabs_triangle a1 (- b1)).
    - rewrite Qabs_opp.
      apply (Qle_trans _ ((1 # 4) + (1 # 4)) _).
      + apply Qplus_le_compat.
        * exact (QleT'_to_Qle _ _ Ha1).
        * exact (QleT'_to_Qle _ _ Hb1).
      + apply qeq_imp_qle. ring. }
  assert (Hd : Qle (15 # 16) (1 + a2 * b2)).
  { assert (Habnd : Qle (Qabs (a2 * b2)) (1 # 16)).
    { rewrite Qabs_Qmult.
      apply (Qmult_le_compat_nonneg (Qabs a2) (1 # 4) (Qabs b2) (1 # 4)).
      - split.
        + apply Qabs_nonneg.
        + exact (QleT'_to_Qle _ _ Ha2).
      - split.
        + apply Qabs_nonneg.
        + exact (QleT'_to_Qle _ _ Hb2). }
    assert (Hlow : Qle (- (1 # 16)) (a2 * b2)).
    { exact (proj1 (proj1 (Qabs_Qle_condition (a2 * b2) (1 # 16)) Habnd)). }
    apply (Qle_trans _ (1 + - (1 # 16)) _).
    - apply qeq_imp_qle. ring.
    - apply (Qplus_le_compat 1 1 (- (1 # 16)) (a2 * b2)).
      + apply Qle_refl.
      + exact Hlow. }
  assert (Hdpos : Qlt 0 (1 + a2 * b2)).
  { apply (Qlt_le_trans 0 (15 # 16) _).
    - unfold Qlt. simpl. lia.
    - exact Hd. }
  assert (H16 : Qlt 0 (15 # 16)) by (unfold Qlt; simpl; lia).
  assert (Hinv : Qle (Qinv (1 + a2 * b2)) (16 # 15)).
  { destruct (Qle_lt_or_eq (15 # 16) (1 + a2 * b2) Hd) as [Hlt | Heq].
    - apply Qlt_le_weak.
      exact (proj1 (Qinv_lt_contravar (15 # 16) (1 + a2 * b2) H16 Hdpos) Hlt).
    - rewrite (Qeq_sym _ _ Heq). apply Qle_refl. }
  assert (Hshape : Qabs ((a1 - b1) * Qinv (1 + a2 * b2))
                   == Qabs (a1 - b1) * Qinv (1 + a2 * b2)).
  { rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite (Qabs_pos (1 + a2 * b2) (Qlt_le_weak 0 (1 + a2 * b2) Hdpos)).
    reflexivity. }
  rewrite Hshape.
  apply (Qle_trans _ ((1 # 2) * (16 # 15)) _).
  - apply (Qmult_le_compat_nonneg (Qabs (a1 - b1)) (1 # 2)
             (Qinv (1 + a2 * b2)) (16 # 15)).
    + split; [apply Qabs_nonneg | exact Hab].
    + split.
      * apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hdpos.
      * exact Hinv.
  - apply (Qle_trans _ (8 # 15) _).
    + apply qeq_imp_qle. ring.
    + unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* （d）|w|<1 全 n 域证书：cauchy_real_arctan 域证书 b3rr_dom_r1      *)
(*   配形（假设面逐字=cauchy_real_arctan 的 Hx 型）。早尾两支实算：    *)
(*   real_inv_pos 早项=Qinv(D_N0)（S03:L6685 定义形），与 D_n 同受     *)
(*   15/16 界（Hu/Hv 对全 n 成立含 N0），两支同过 abl9_brg_winv_bnd。 *)
(* ============================================================ *)
Lemma abl9_brg_w_dom : forall (u v : Real)
  (Huv : real_lt real_zero (real_plus real_one (real_mult u v)))
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) (1 # 4))
  (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) (1 # 4)),
  forall n : nat, QleT' (Qabs (projT1 (abl9_brg_w_real u v Huv) n)) 1.
Proof.
  intros u v Huv Hu Hv n.
  destruct u as [un Hun]. destruct v as [vn Hvn].
  destruct Huv as [e0 [He0 [N0 HN0]]].
  unfold abl9_brg_w_real.
  cbn [projT1 real_plus real_opp real_mult real_one real_inv_pos].
  destruct (Nat.leb N0 n) eqn:E.
  - apply (abl9_brg_winv_bnd (un n) (vn n) (un n) (vn n)).
    + exact (Hu n).
    + exact (Hv n).
    + exact (Hu n).
    + exact (Hv n).
  - apply (abl9_brg_winv_bnd (un n) (vn n) (un N0) (vn N0)).
    + exact (Hu n).
    + exact (Hv n).
    + exact (Hu N0).
    + exact (Hv N0).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   对账三联：Lemma 名清单 14 = Qed 计数 14 = PA 语句 14，零差。     *)
(* ============================================================ *)
Print Assumptions abl9_brg_pt_eq.
Print Assumptions abl9_brg_wsq_pt.
Print Assumptions abl9_brg_wincr_pt.
Print Assumptions abl9_brg_wsq_kernel_pt.
Print Assumptions abl9_brg_wincr_kernel_pt.
Print Assumptions abl9_brg_w_proj.
Print Assumptions abl9_brg_w_ext.
Print Assumptions abl9_brg_Dsq_pos.
Print Assumptions abl9_brg_wsq_real.
Print Assumptions abl9_brg_wsq_real_kernel.
Print Assumptions abl9_brg_wincr_real.
Print Assumptions abl9_brg_wincr_real_kernel.
Print Assumptions abl9_brg_winv_bnd.
Print Assumptions abl9_brg_w_dom.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_brg_wsq_real abl9_brg_wincr_real abl9_brg_w_dom.
