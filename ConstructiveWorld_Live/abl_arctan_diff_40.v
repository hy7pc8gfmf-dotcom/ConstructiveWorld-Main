(* ==========================================================================)
   abl_arctan_diff_40.v — arctan 差公式Real 桥构造：abl9_slope_id 升层
   消融批 · 落件形态：新件 Require 件19/件20/件21（禁触 abl_arctan_diff_20.v）         
   ── 模块名与数学使命：──────────────────────────────────────────────────────
   链式规则斜率合成恒等式的Real 升层（登记册-abl_arctan_diff_20 §四·1 续点②
   本体）。设 w(u,v):=(u−v)·inv(1+uv)（由件21 abl9_brg_w_real 承载），Q 层
   恒等式 abl9_slope_id（件20）：h/(1+u²) − (w(u+h,v)−w(u,v))·(1+uv)²/
   ((1+u²)(1+v²)) == h²v/((1+(u+h)v)(1+u²))。本件升为 real 层 real_eq：
   abl9_slope_id_real——h·inv(1+u²) − (w(u+h,v)−w(u,v))·(1+uv)²·
   inv((1+u²)(1+v²)) == h·h·v·inv((1+(u+h)v)(1+u²))。工法=终近逐点相等
   闭合器 abl9_brg_pt_eq（件21）+ real_inv_proj（S09）逐点投影链：real_inv_pos
   的近似倒数误差项经见证率取 Nat.max 并入 eps 预算闭合（real_eq 只依赖终近
   率，早项不受控项被 N-max 吸收）；正性证书 b3r_one_sq_real_pos（S11，
   1+x²>0）与 real_mult_positive（S07）派生引擎所需 ~(...==0) 非零旁支；
   real_inv_pos_ext 的证书无关对齐由件21 abl9_brg_w_ext 供给。配套域证书走
   件20 D1 路线（§四·1(c) 点名）：abl9_q_path_den（|x|≤1、|t|≤1/4 ⟹
   3/4 ≤ 1+(x+t)x）逐点使用——abl9_wpath_pt_bnd（Q 点件：Qinv(D)≤4/3，
   |f·Qinv D| ≤ (1/4)(4/3)=1/3<1）与 abl9_brg_wpath_dom（real 层
   |w(x+t)|≤1 全 n 证书，real_inv_pos 早项=Qinv(D_N0) 与 D_n 同受 D1 界，
   早尾两支同过界），为 cauchy_real_arctan 的域证书 b3rr_dom_r1 配形。
   ── 依赖清单：──────────────────────────────────────────────────────────────
   S01–S11全链 + abl_arctan_diff_19（Q 供给构造）+ abl_arctan_diff_20
   （引擎 abl9_slope_id/abl9_q_path_den）+ abl_arctan_cert_bridge_21
   （abl9_brg_w_real/abl9_brg_w_proj/abl9_brg_pt_eq）+ Stdlib
   QArith/Setoid/Morphisms/Lia/Qminmax/GenericMinMax/Extraction。
   Require 链退回 S11 单链，S12 出锥（承 X15''/X16/X19' 判定）。
   ── 对标行：────────────────────────────────────────────────────────────────
   登记册-abl_arctan_diff_20 §四·1（②Real桥三点名：real_inv_proj +
   real_inv_pos_ext+预算闭合）；登记册-abl_arctan_cert_bridge_21 §四 表 
   （本件闭合其 B 桥使用位「承件 20 abl9_slope_id Q 形升 real」）；
   S11 b3rr 系 arctan 微分轴（real_inv_pos / b3r_one_sq_real_pos /
   b3r_one_proj / b3rr_dom_r1）。
   ── 构造性注记：────────────────────────────────────────────────────────────
   全构造：四件全 Qed，零承认件零公理；语句面无 Prop 命题
   （real_eq/real_lt/QleT' 均为 Set/Type 层）；Print Assumptions 全 Closed；
   提取检验 Obj.magic 计 0。非重复施工申明：件21 止于 wsq/wincr 两恒等桥与
   w 承载件（其 Q 引擎出件19），slope_id 斜率合成恒等的升层为本件独有交付。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x40pool "" /tmp/x40pool/abl_arctan_diff_40.v
   （隔离池 /tmp/x40pool：S01–S11+件16+件19+件20+件21 .vo 在链，件19/20/21
   vo 新于 v 且魔数 436f7121 0001 5ff4 实读；cwd=/tmp/x40work 异地空目录；
   发起前 rocq 进程 <3，窗满候窗禁硬闯。）
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
Require Import abl_arctan_diff_20.
Require Import abl_arctan_cert_bridge_21.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* Q 引擎：abl9_slope_id 的 Qinv 形包装（Qdiv 定义性展开）。          *)
(*   s/(1+u²) 等除法形逐项 Qdiv x y := x·Qinv y，与 real_inv_proj    *)
(*   投影产形（Qinv 乘式）直接对齐。                                  *)
(* ============================================================ *)
Lemma abl9_slope_id_pt : forall a b d : Q,
  ~ (1 + (a + d) * b == 0) -> ~ (1 + a * b == 0) ->
  d * Qinv (1 + a * a)
  - ((a + d - b) * Qinv (1 + (a + d) * b) - (a - b) * Qinv (1 + a * b))
    * ((1 + a * b) * (1 + a * b) * Qinv ((1 + a * a) * (1 + b * b))) ==
  d * d * b * Qinv ((1 + (a + d) * b) * (1 + a * a)).
Proof.
  intros a b d H1 H2.
  assert (Hcore := abl9_slope_id a b d H1 H2).
  unfold Qdiv in Hcore.
  exact Hcore.
Qed.

(* ============================================================ *)
(* Q 点件（D1 路线）：因子 f（== a1+t1−a1，显式等式超参——实例化时     *)
(*   f 逐字对上 real 层 cbn 形，免 QleT' 目标下的 Qeq 改写：QleT' 系   *)
(*   S02 自件 Type 层序，未注册改写位；改写一律在 Qle/Qeq 目标下做）    *)
(*   ⟹ |f·Qinv(1+(a2+t2)a2)| ≤ 1/3 < 1。                               *)
(*   链：|f|=|t1|≤1/4（Qabs_wd+qeq 桥）；D1 给 3/4 ≤ D ⟹ Qinv D ≤ 4/3  *)
(*   （Qinv_lt_contravar，等支 Qle_refl 收）；|f·Qinv D| = |f|·Qinv D  *)
(*   （Qabs_Qmult+Qabs_Qinv+Qabs_pos 正则化）；乘界 1/4·4/3=1/3 ≤ 1。  *)
(* ============================================================ *)
Lemma abl9_wpath_pt_bnd : forall f a1 t1 a2 t2 : Q,
  Qle (Qabs a1) 1 -> Qle (Qabs t1) (1 # 4) ->
  Qle (Qabs a2) 1 -> Qle (Qabs t2) (1 # 4) ->
  f == a1 + t1 + - a1 ->
  QleT' (Qabs (f * Qinv (1 + (a2 + t2) * a2))) 1.
Proof.
  intros f a1 t1 a2 t2 Ha1 Ht1 Ha2 Ht2 Ef.
  apply Qle_to_QleT'.
  assert (Ef2 : f == t1).
  { rewrite Ef. ring. }
  assert (Hf : Qle (Qabs f) (1 # 4)).
  { apply (Qle_trans (Qabs f) (Qabs t1) (1 # 4)).
    - apply qeq_imp_qle. apply abl9_Qabs_wd. exact Ef2.
    - exact Ht1. }
  assert (HD : QleT' (3 # 4) (1 + (a2 + t2) * a2))
    by (apply abl9_q_path_den; assumption).
  assert (HDq : Qle (3 # 4) (1 + (a2 + t2) * a2))
    by (exact (QleT'_to_Qle _ _ HD)).
  assert (H34 : Qlt 0 (3 # 4)) by (unfold Qlt; simpl; lia).
  assert (HDpos : Qlt 0 (1 + (a2 + t2) * a2)).
  { apply (Qlt_le_trans 0 (3 # 4) (1 + (a2 + t2) * a2)).
    - exact H34.
    - exact HDq. }
  assert (Hinv : Qle (Qinv (1 + (a2 + t2) * a2)) (4 # 3)).
  { destruct (Qle_lt_or_eq (3 # 4) (1 + (a2 + t2) * a2) HDq) as [Hlt | Heq].
    - apply Qlt_le_weak.
      exact (proj1 (Qinv_lt_contravar (3 # 4) (1 + (a2 + t2) * a2) H34 HDpos) Hlt).
    - rewrite (Qeq_sym _ _ Heq). apply Qle_refl. }
  assert (Hshape : Qabs (f * Qinv (1 + (a2 + t2) * a2))
                   == Qabs f * Qinv (1 + (a2 + t2) * a2)).
  { rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite (Qabs_pos (1 + (a2 + t2) * a2)
               (Qlt_le_weak 0 (1 + (a2 + t2) * a2) HDpos)).
    reflexivity. }
  rewrite Hshape.
  apply (Qle_trans (Qabs f * Qinv (1 + (a2 + t2) * a2)) ((1 # 4) * (4 # 3)) 1).
  - apply (Qmult_le_compat_nonneg (Qabs f) (1 # 4)
             (Qinv (1 + (a2 + t2) * a2)) (4 # 3)).
    + split; [apply Qabs_nonneg | exact Hf].
    + split.
      * apply Qinv_le_0_compat. apply Qlt_le_weak. exact HDpos.
      * exact Hinv.
  - apply (Qle_trans ((1 # 4) * (4 # 3)) (1 # 3) 1).
    + apply qeq_imp_qle. ring.
    + unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* ②·主件：abl9_slope_id 的 Real 升层（斜率合成恒等式，real_eq）。     *)
(*   h·inv(1+u²) − (w(u+h,v)−w(u,v))·(1+uv)²·inv((1+u²)(1+v²))        *)
(*     == h·h·v·inv((1+(u+h)v)(1+u²))，                               *)
(*   其中 w 承载=件21 abl9_brg_w_real；正性证书 Hu2/Hv2 由            *)
(*   b3r_one_sq_real_pos 供（装配位单发），H1/H2 为 w 的入参形。      *)
(* ============================================================ *)
Lemma abl9_slope_id_real : forall (u v h : Real)
  (H1 : real_lt real_zero (real_plus real_one (real_mult (real_plus u h) v)))
  (H2 : real_lt real_zero (real_plus real_one (real_mult u v)))
  (Hu2 : real_lt real_zero (real_plus real_one (real_mult u u)))
  (Hv2 : real_lt real_zero (real_plus real_one (real_mult v v))),
  real_eq
    (real_plus
       (real_mult h (real_inv_pos (real_plus real_one (real_mult u u)) Hu2))
       (real_opp
          (real_mult
             (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                        (real_opp (abl9_brg_w_real u v H2)))
             (real_mult
                (real_mult (real_plus real_one (real_mult u v))
                           (real_plus real_one (real_mult u v)))
                (real_inv_pos
                   (real_mult (real_plus real_one (real_mult u u))
                              (real_plus real_one (real_mult v v)))
                   (real_mult_positive (real_plus real_one (real_mult u u))
                                       (real_plus real_one (real_mult v v))
                                       Hu2 Hv2))))))
    (real_mult
       (real_mult (real_mult h h) v)
       (real_inv_pos
          (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                     (real_plus real_one (real_mult u u)))
          (real_mult_positive (real_plus real_one (real_mult (real_plus u h) v))
                              (real_plus real_one (real_mult u u)) H1 Hu2))).
Proof.
  intros u v h H1 H2 Hu2 Hv2.
  pose proof H1 as H1C. destruct H1C as [e1 [He1 [M1 HM1]]].
  pose proof H2 as H2C. destruct H2C as [e2 [He2 [M2 HM2]]].
  destruct (real_inv_proj (real_plus real_one (real_mult u u)) Hu2)
    as [Nu HNu].
  destruct (real_inv_proj
              (real_mult (real_plus real_one (real_mult u u))
                         (real_plus real_one (real_mult v v)))
              (real_mult_positive (real_plus real_one (real_mult u u))
                                  (real_plus real_one (real_mult v v))
                                  Hu2 Hv2)) as [ND HND].
  destruct (real_inv_proj
              (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                         (real_plus real_one (real_mult u u)))
              (real_mult_positive (real_plus real_one (real_mult (real_plus u h) v))
                                  (real_plus real_one (real_mult u u))
                                  H1 Hu2)) as [NE HNE].
  destruct (abl9_brg_w_proj (real_plus u h) v H1) as [Nw1 HNw1].
  destruct (abl9_brg_w_proj u v H2) as [Nw2 HNw2].
  apply (abl9_brg_pt_eq _ _
           (Nat.max Nu (Nat.max ND (Nat.max NE (Nat.max Nw1
              (Nat.max Nw2 (Nat.max M1 M2))))))).
  intros n Hn.
  assert (Hnu : (Nu <= n)%nat) by lia.
  assert (Hnd : (ND <= n)%nat) by lia.
  assert (Hne : (NE <= n)%nat) by lia.
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
      rewrite (real_plus_proj real_one (real_mult (real_plus u h) v) n).
      rewrite (real_mult_proj (real_plus u h) v n).
      rewrite Huhp.
      rewrite (b3r_one_proj n).
      cbn [real_zero projT1]. ring. }
  assert (Hnz1 : ~ (1 + (projT1 u n + projT1 h n) * projT1 v n == 0)).
  { intro Hz.
    apply (Qlt_not_eq 0 (1 + (projT1 u n + projT1 h n) * projT1 v n) Hlt1).
    apply Qeq_sym. exact Hz. }
  assert (Hlt2 : Qlt 0 (1 + projT1 u n * projT1 v n)).
  { apply (Qlt_le_trans 0
             (projT1 (real_plus real_one (real_mult u v)) n
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
  { intro Hz.
    apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt2).
    apply Qeq_sym. exact Hz. }
  (* LHS 逐点投影：先外层 plus，再逐层 mult/opp/inv 自外向内 *)
  rewrite (real_plus_proj
             (real_mult h (real_inv_pos (real_plus real_one (real_mult u u)) Hu2))
             (real_opp
                (real_mult
                   (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                              (real_opp (abl9_brg_w_real u v H2)))
                   (real_mult
                      (real_mult (real_plus real_one (real_mult u v))
                                 (real_plus real_one (real_mult u v)))
                      (real_inv_pos
                         (real_mult (real_plus real_one (real_mult u u))
                                    (real_plus real_one (real_mult v v)))
                         (real_mult_positive (real_plus real_one (real_mult u u))
                                             (real_plus real_one (real_mult v v))
                                             Hu2 Hv2))))) n).
  rewrite (real_mult_proj h
             (real_inv_pos (real_plus real_one (real_mult u u)) Hu2) n).
  rewrite (HNu n Hnu).
  rewrite (real_opp_proj
             (real_mult
                (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                           (real_opp (abl9_brg_w_real u v H2)))
                (real_mult
                   (real_mult (real_plus real_one (real_mult u v))
                              (real_plus real_one (real_mult u v)))
                   (real_inv_pos
                      (real_mult (real_plus real_one (real_mult u u))
                                 (real_plus real_one (real_mult v v)))
                      (real_mult_positive (real_plus real_one (real_mult u u))
                                          (real_plus real_one (real_mult v v))
                                          Hu2 Hv2)))) n).
  rewrite (real_mult_proj
             (real_plus (abl9_brg_w_real (real_plus u h) v H1)
                        (real_opp (abl9_brg_w_real u v H2)))
             (real_mult
                (real_mult (real_plus real_one (real_mult u v))
                           (real_plus real_one (real_mult u v)))
                (real_inv_pos
                   (real_mult (real_plus real_one (real_mult u u))
                              (real_plus real_one (real_mult v v)))
                   (real_mult_positive (real_plus real_one (real_mult u u))
                                       (real_plus real_one (real_mult v v))
                                       Hu2 Hv2))) n).
  rewrite (real_plus_proj (abl9_brg_w_real (real_plus u h) v H1)
             (real_opp (abl9_brg_w_real u v H2)) n).
  rewrite (real_opp_proj (abl9_brg_w_real u v H2) n).
  rewrite (HNw1 n Hnw1). rewrite Huhp.
  rewrite (HNw2 n Hnw2).
  rewrite (real_mult_proj
             (real_mult (real_plus real_one (real_mult u v))
                        (real_plus real_one (real_mult u v)))
             (real_inv_pos
                (real_mult (real_plus real_one (real_mult u u))
                           (real_plus real_one (real_mult v v)))
                (real_mult_positive (real_plus real_one (real_mult u u))
                                    (real_plus real_one (real_mult v v))
                                    Hu2 Hv2)) n).
  rewrite (real_mult_proj (real_plus real_one (real_mult u v))
             (real_plus real_one (real_mult u v)) n).
  rewrite (real_plus_proj real_one (real_mult u v) n).
  rewrite (real_mult_proj u v n).
  rewrite (b3r_one_proj n).
  rewrite (HND n Hnd).
  rewrite (real_mult_proj (real_plus real_one (real_mult u u))
             (real_plus real_one (real_mult v v)) n).
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (real_plus_proj real_one (real_mult v v) n).
  rewrite (real_mult_proj v v n).
  rewrite (b3r_one_proj n).
  (* RHS 逐点投影 *)
  rewrite (real_mult_proj (real_mult (real_mult h h) v)
             (real_inv_pos
                (real_mult (real_plus real_one (real_mult (real_plus u h) v))
                           (real_plus real_one (real_mult u u)))
                (real_mult_positive
                   (real_plus real_one (real_mult (real_plus u h) v))
                   (real_plus real_one (real_mult u u)) H1 Hu2)) n).
  rewrite (real_mult_proj (real_mult h h) v n).
  rewrite (real_mult_proj h h n).
  rewrite (HNE n Hne).
  rewrite (real_mult_proj (real_plus real_one (real_mult (real_plus u h) v))
             (real_plus real_one (real_mult u u)) n).
  rewrite (real_plus_proj real_one (real_mult (real_plus u h) v) n).
  rewrite (real_mult_proj (real_plus u h) v n).
  rewrite Huhp.
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (b3r_one_proj n).
  apply (abl9_slope_id_pt (projT1 u n) (projT1 v n) (projT1 h n) Hnz1 Hnz2).
Qed.

(* ============================================================ *)
(* 域证书（D1 路线）：|w(x+t)| ≤ 1 全 n——cauchy_real_arctan 域        *)
(*   证书 b3rr_dom_r1 配形。w(x,t):=t·inv(1+(x+t)x) 承载为            *)
(*   abl9_brg_w_real (real_plus x t) x（(x+t)−x==t）。早尾两支同过界： *)
(*   real_inv_pos 早项=Qinv(D_N0)（S03 定义形），D1 对全 n 成立故     *)
(*   N0 处同受 3/4 界；尾项=Qinv(D_n) 同理。                          *)
(* ============================================================ *)
Lemma abl9_brg_wpath_dom : forall (x t : Real)
  (Hxt : real_lt real_zero (real_plus real_one (real_mult (real_plus x t) x)))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Ht : forall n : nat, QleT' (Qabs (projT1 t n)) (1 # 4)),
  forall n : nat,
  QleT' (Qabs (projT1 (abl9_brg_w_real (real_plus x t) x Hxt) n)) 1.
Proof.
  intros x t Hxt Hx Ht n.
  destruct x as [xn Hxn]. destruct t as [tn Htn].
  destruct Hxt as [e0 [He0 [N0 HN0]]].
  unfold abl9_brg_w_real.
  cbn [projT1 real_plus real_opp real_mult real_one real_inv_pos].
  destruct (Nat.leb N0 n) eqn:E.
  - apply (abl9_wpath_pt_bnd (xn n + tn n + - xn n) (xn n) (tn n)
             (xn n) (tn n)).
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Ht n)).
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Ht n)).
    + ring.
  - apply (abl9_wpath_pt_bnd (xn n + tn n + - xn n) (xn n) (tn n)
             (xn N0) (tn N0)).
    + exact (QleT'_to_Qle _ _ (Hx n)).
    + exact (QleT'_to_Qle _ _ (Ht n)).
    + exact (QleT'_to_Qle _ _ (Hx N0)).
    + exact (QleT'_to_Qle _ _ (Ht N0)).
    + ring.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 4 = Qed 4 = PA 语句 4，零差。                      *)
(* ============================================================ *)
Print Assumptions abl9_slope_id_pt.
Print Assumptions abl9_slope_id_real.
Print Assumptions abl9_wpath_pt_bnd.
Print Assumptions abl9_brg_wpath_dom.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_slope_id_real abl9_brg_wpath_dom.
