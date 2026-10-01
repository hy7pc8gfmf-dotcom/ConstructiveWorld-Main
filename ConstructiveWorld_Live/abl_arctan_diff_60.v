(* ==========================================================================)
   abl_arctan_diff_60.v — 9a-乙 主公式续作（X60 形：         
   ②桥闭合 + GAP 勘定件组；落件形态=甲形态·新件 Require 件20/件21）
   消融批 · arctan 差公式件续作（接件20 674 行中断态）         
   ── 落件形态选型·依赖清单（甲形态·登记册说明）：──────────────────────────────────
   选型=新件 abl_arctan_diff_60.v（Require 件20+件21），非原地续写件20。理由：
   ①件20已冻结（登记册登记值在卷），其终验
   段（PA 17语句对账三联）系全通过终态，原地续写须整体搬移终验段、破对账三联
   结构；②件21系 X24' 预制明示「供主公式装配直接 Require 闭合」的桥构造，
   Require 直耗即其设计用途；③本片新勘两缺口（下）与拟文修订决策耦合，
   独立新件不污染已认证供给链。Require 链=S01–S11+件19/20/21，S12 出锥
   ——承 X15''/X16/X19' 判定。
   ── E12 实文勘定·两缺口·数学使命（本片响亮登记，条款 G）：──────────────────────
   【GAP-1·首勘（三前任未勘，X24' 桥构造亦未触及）】拟文RHS 槽 <w 域证书>
   （cauchy_real_arctan 的 ∀n |W_n|≤1 逐点域证书）在拟文假设下不可满足：
   实文勘定（S02:L392-469）cauchy 无早项界、real_lt 系终近形（∃N ∀n≥N）、
   real_inv_pos 早项=Qinv(D_N0)（S03:L6681 定义形）——Hh4 : real_lt
   (real_abs h) (real_const (1#4)) 只约束尾段坐标，h 的早项（n<N）可任意大
   （反例：h:=(1000,0,0,…) 满足 Hh4，而 W:=h·inv(1+x(x+h)) 的 W_0 可 >1，
   证书 ∀n |W_n|≤1 不可构）；且 phi 链中间点 |x_n+(i/N)h_n|≤1 证书同理只在
   尾段可推（P2 凸性核）。凡链内 cauchy_real_arctan 使用皆被阻断。
   【GAP-2·续登记（X19' 首勘，本片判定实质不可绕）】①件（b3rr 系）基点域
   要求 |u_n|≤ρ<1 严格（b3rr_M_lt1/q_pow 衰减实质用），拟文域 |x_n|≤1
   非严格——x 侧增量估计在 |x_n|→1 坐标不可配；内点化或边界机器（|u|=1
   交错级数尾估计，链内无此机器）属主会话级拟文/表示决策，非本切片权限。
   两缺口合取判定：主定理 abl9_atan_diff_formula 在拟文逐字域下，经在链
   机器不可闭合；拟文句不写（禁承认式），续作登记于登记册§四。      
   ── 本片交付七件·构造性注记（全不依赖两缺口的可闭合件，全 Qed）：─────────────────
   P1 abl9_slope_pt（Q 引擎·点形斜率恒等 Qinv 形——件20 abl9_slope_id 之
      点形引擎，field 闭合）；
   P2 abl9_conv_bnd_pt（Q 凸性核：|x|≤1、|x+h|≤1、0≤κ≤1 → |x+κh|≤1——
      GAP-1 尾段可构部分的算术核，路径中间点域证书直接供给）；
   P3 abl9_wsq_pos（1+w²>0 无条件件——P7 的 inv 正性证书）；
   P4 abl9_D_pos_cond（D1 升 Real 层单发：∀n 逐点界 → D:=1+(x+h)x 立即
      real_lt real_zero——拟文 <证书> 槽在逐点域假设下的闭合形）；
   P5 abl9_invq_bnd（W 域证书 Q 点核：D≥3/4、|h|≤1/4 → |inv(D)·h|≤1/3）；
   P5b abl9_inv_pos_shape（real_inv_pos 定义形披露件：投影逐点=if N0≤m
      then Qinv(D_m) else Qinv(D_N0)——reflexivity 全转换核验，P6 工法基）；
   P6 abl9_W_dom_cond（GAP-1 条件闭合件：HD 证书+∀n |x|≤1、|h|≤1/4 →
      ∀n |W_n|≤1/3——<w 域证书> 槽在逐点域假设下的闭合形；早项两支
      （n≥N0 取 Qinv(D_n)、n<N0 取 Qinv(D_N0)，real_inv_pos S03:L6681
      定义形）同过 D1 逐点 3/4 下界——任意证书 HD 皆可，无早项盲区）；
   P7 abl9_slope_real（②桥闭合·主交付：Real 层斜率恒等
      s·inv(1+u²) − Δw·inv(1+w₀²) == s²v·inv((1+(u+s)v)(1+u²))——
      件21 brg 桥（w_proj/wincr_pt/wsq_pt）+P1 点形引擎+P3 证书，
      abl9_brg_pt_eq见证 max 闭合；登记册 §四「接续首刀」点名件）；
   P8 abl9_W_cert_unit（P6 的 ≤1 拟文槽配形，qleT'_trans 单发）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x60pool "" /tmp/x60pool/abl_arctan_diff_60.v
   （隔离池 /tmp/x60pool：S01–S11+件16/19/20 认证 vo 真拷（件20 md5
   d8111457与登记册 SAME 实证）+件21 原位建成 绿验（EXIT=0/Closed×14/
   魔数 436f7121 0001 5ff4/vo 74274 字节新于 v）；cwd=/tmp/x60w4 异地空目录。）
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
(* P1·Q 引擎：点形斜率恒等（Qinv 形）——件20 abl9_slope_id 之点形      *)
(*   引擎：s/A − [Δw 点形]·[D²/G] == s²v/((1+(u+s)v)·A)，             *)
(*   A=1+u²、D=1+uv、G=(1+u²)(1+v²)、Δw 点形=件21 wincr_pt 形。         *)
(* ============================================================ *)
Lemma abl9_slope_pt : forall u v s : Q,
  Qlt 0 (1 + (u + s) * v) -> Qlt 0 (1 + u * v) ->
  s * Qinv (1 + u * u)
  + - ((s * (1 + v * v) * Qinv (1 + (u + s) * v) * Qinv (1 + u * v))
    * ((1 + u * v) * (1 + u * v) * Qinv ((1 + u * u) * (1 + v * v)))) ==
  s * s * v * Qinv ((1 + (u + s) * v) * (1 + u * u)).
Proof.
  intros u v s H1 H2.
  assert (Hne1 : ~ (1 + (u + s) * v == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + (u + s) * v) H1).
    apply Qeq_sym. exact Hz. }
  assert (Hne2 : ~ (1 + u * v == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + u * v) H2).
    apply Qeq_sym. exact Hz. }
  assert (HneA : ~ (1 + u * u == 0)) by apply abl9_q_pos_sq.
  assert (HneB : ~ (1 + v * v == 0)) by apply abl9_q_pos_sq.
  assert (Hne1c : ~ ((1 + (u + s) * v) * (1 + u * v) == 0)).
  { intros Hz. destruct (Qmult_integral (1 + (u + s) * v) (1 + u * v) Hz)
      as [Hz1 | Hz2].
    - exact (Hne1 Hz1).
    - exact (Hne2 Hz2). }
  assert (HneG : ~ ((1 + u * u) * (1 + v * v) == 0)).
  { intros Hz. destruct (Qmult_integral (1 + u * u) (1 + v * v) Hz)
      as [Hz1 | Hz2].
    - exact (HneA Hz1).
    - exact (abl9_q_pos_sq v Hz2). }
  field. repeat split; assumption.
Qed.

(* ============================================================ *)
(* P2·Q 凸性核：|x|≤1、|x+h|≤1、0≤κ≤1 → |x+κh|≤1                       *)
(*   （x+κh==(1−κ)x+κ(x+h) 环等+三角+非负系数配平）                     *)
(* ============================================================ *)
Lemma abl9_conv_bnd_pt : forall x t k : Q,
  Qle (Qabs x) 1 -> Qle (Qabs (x + t)) 1 ->
  Qle 0 k -> Qle k 1 ->
  Qle (Qabs (x + k * t)) 1.
Proof.
  intros x t k Hx Hxt Hk0 Hk1.
  assert (H1m : Qle 0 (1 - k)).
  { assert (Hopp : Qle (-1) (- k)) by (apply (Qopp_le_compat k 1); exact Hk1).
    assert (Hadd : Qle (-1 + 1) (- k + 1))
      by (apply (Qplus_le_compat (-1) (- k) 1 1);
            [exact Hopp | apply Qle_refl]).
    assert (E0 : 0 == -1 + 1) by ring.
    assert (E1 : - k + 1 == 1 - k) by ring.
    apply (Qle_trans 0 (-1 + 1) (1 - k)).
    - apply qeq_imp_qle. exact E0.
    - apply (Qle_trans (-1 + 1) (- k + 1) (1 - k)).
      + exact Hadd.
      + apply qeq_imp_qle. exact E1. }
  assert (Hsplit : x + k * t == (1 - k) * x + k * (x + t)) by ring.
  apply (Qle_trans (Qabs (x + k * t))
                   ((1 - k) * Qabs x + k * Qabs (x + t)) 1).
  - apply (Qle_trans (Qabs (x + k * t))
           (Qabs ((1 - k) * x + k * (x + t)))
           ((1 - k) * Qabs x + k * Qabs (x + t))).
    + apply qeq_imp_qle. apply Qabs_wd. exact Hsplit.
    + apply (Qle_trans (Qabs ((1 - k) * x + k * (x + t)))
             (Qabs ((1 - k) * x) + Qabs (k * (x + t)))
             ((1 - k) * Qabs x + k * Qabs (x + t))).
      * apply Qabs_triangle.
      * apply Qplus_le_compat.
        -- rewrite Qabs_Qmult.
           assert (Habs1m : Qabs (1 - k) == 1 - k)
             by (apply Qabs_pos; exact H1m).
           rewrite Habs1m. apply Qle_refl.
        -- rewrite Qabs_Qmult.
           assert (Habsk : Qabs k == k) by (apply Qabs_pos; exact Hk0).
           rewrite Habsk. apply Qle_refl.
  - apply (Qle_trans ((1 - k) * Qabs x + k * Qabs (x + t))
                     ((1 - k) * 1 + k * 1) 1).
    + apply Qplus_le_compat.
      * rewrite (Qmult_comm (1 - k) (Qabs x)). rewrite (Qmult_comm (1 - k) 1).
        apply (Qmult_le_compat_r (Qabs x) 1 (1 - k)).
        -- exact Hx.
        -- exact H1m.
      * rewrite (Qmult_comm k (Qabs (x + t))). rewrite (Qmult_comm k 1).
        apply (Qmult_le_compat_r (Qabs (x + t)) 1 k).
        -- exact Hxt.
        -- exact Hk0.
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* P3·1+w²>0 无条件件（平方非负+1/2 余量；P7 证书）                     *)
(* ============================================================ *)
Lemma abl9_wsq_pos : forall w : Real,
  real_lt real_zero (real_plus real_one (real_mult w w)).
Proof.
  intros w.
  exists (1 # 2). split.
  - reflexivity.
  - exists (0%nat). intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 # 2) 1
             (projT1 (real_plus real_one (real_mult w w)) n
              - projT1 real_zero n)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (1 + projT1 w n * projT1 w n)
             (projT1 (real_plus real_one (real_mult w w)) n
              - projT1 real_zero n)).
      * apply (Qle_trans 1 (1 + 0) (1 + projT1 w n * projT1 w n)).
        -- apply qeq_imp_qle. ring.
        -- apply (Qplus_le_compat 1 1 0 (projT1 w n * projT1 w n)).
           ++ apply Qle_refl.
           ++ apply Qsquare_nonneg.
      * apply qeq_imp_qle.
        rewrite (real_plus_proj real_one (real_mult w w) n).
        rewrite (real_mult_proj w w n).
        rewrite (b3r_one_proj n).
        cbn [projT1 real_zero]. ring.
Qed.

(* ============================================================ *)
(* P4·D1 升 Real 层单发：∀n 逐点界 → D:=1+(x+h)x 立即严格正             *)
(*   （拟文 <证书> 槽在逐点域假设下的闭合形；witness=(1/2, 0)）           *)
(* ============================================================ *)
Lemma abl9_D_pos_cond : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hhb : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)),
  real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)).
Proof.
  intros x h Hx Hhb.
  exists (1 # 2). split.
  - reflexivity.
  - exists (0%nat). intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 # 2) (3 # 4)
             (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
              - projT1 real_zero n)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans (3 # 4)
             (1 + (projT1 x n + projT1 h n) * projT1 x n)
             (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
              - projT1 real_zero n)).
      * apply QleT'_to_Qle.
        apply (abl9_q_path_den (projT1 x n) (projT1 h n)).
        -- apply QleT'_to_Qle. apply Hx.
        -- apply QleT'_to_Qle. apply Hhb.
      * apply qeq_imp_qle.
        rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
        rewrite (real_mult_proj (real_plus x h) x n).
        rewrite (real_plus_proj x h n).
        rewrite (b3r_one_proj n).
        cbn [projT1 real_zero]. ring.
Qed.

(* ============================================================ *)
(* P5·W 域证书 Q 点核：D≥3/4、|h|≤1/4 → |inv(D)·h|≤1/3                 *)
(*   （D≥3/4>0 → inv(D)≤4/3；两因非负配平 (4/3)(1/4)=1/3）              *)
(* ============================================================ *)
Lemma abl9_invq_bnd : forall Dq hq : Q,
  QleT' (3 # 4) Dq -> QleT' (Qabs hq) (1 # 4) ->
  QleT' (Qabs (Qinv Dq * hq)) (1 # 3).
Proof.
  intros Dq hq Hd Hh.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (Qinv Dq * hq))
           (Qabs (Qinv Dq) * Qabs hq) (1 # 3)).
  - apply qeq_imp_qle. apply Qabs_Qmult.
  - apply (Qle_trans (Qabs (Qinv Dq) * Qabs hq)
             ((4 # 3) * (1 # 4)) (1 # 3)).
    + apply (Qmult_le_compat_nonneg (Qabs (Qinv Dq)) (4 # 3)
               (Qabs hq) (1 # 4)).
      * split.
        -- apply Qabs_nonneg.
        -- assert (HdQ : Qle (3 # 4) Dq) by (apply QleT'_to_Qle; exact Hd).
           assert (Hpos : Qlt 0 Dq).
           { assert (H12 : Qlt 0 (1 # 2)) by (unfold Qlt; simpl; lia).
             assert (H34 : Qlt (1 # 2) (3 # 4)) by (unfold Qlt; simpl; lia).
             apply (Qlt_trans 0 (1 # 2) Dq).
             - exact H12.
             - exact (Qlt_le_trans (1 # 2) (3 # 4) Dq H34 HdQ). }
           assert (Habsinv : Qabs (Qinv Dq) == Qinv Dq).
           { apply (Qabs_pos (Qinv Dq)).
             apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hpos. }
           rewrite Habsinv.
           assert (H34pos : Qlt 0 (3 # 4)) by (unfold Qlt; simpl; lia).
           assert (Hinv34 : Qinv (3 # 4) == (4 # 3)) by reflexivity.
           destruct (Qle_lt_or_eq (3 # 4) Dq HdQ) as [Hlt | Heq].
           ++ rewrite <- Hinv34. apply Qlt_le_weak.
              exact (proj1 (Qinv_lt_contravar (3 # 4) Dq H34pos Hpos) Hlt).
           ++ rewrite (Qeq_sym _ _ Heq). apply Qle_refl.
      * split.
        -- apply Qabs_nonneg.
        -- apply QleT'_to_Qle. exact Hh.
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* P5b·real_inv_pos 定义形披露件（S03:L6681）：投影逐点=                  *)
(*   if (N0 ≤ m) then Qinv(D_m) else Qinv(D_N0)—— reflexivity 全转换      *)
(*   核验（P6 早项两支的稳健工法；cbn 系依赖 match 上有爆型风险，          *)
(*   本件以转换核验替代——战术固化）。                                      *)
(* ============================================================ *)
Lemma abl9_inv_pos_shape : forall (D : Real) (HD : real_lt real_zero D),
  sigT (fun N : nat => forall m : nat,
    projT1 (real_inv_pos D HD) m ==
    (if Nat.leb N m then Qinv (projT1 D m) else Qinv (projT1 D N))).
Proof.
  intros D HD.
  destruct D as [u Hu].
  destruct HD as [eps0 [Heps0 [N0 HN0]]].
  exists N0. intros m. reflexivity.
Qed.

(* ============================================================ *)
(* P6·GAP-1 条件闭合件：<w 域证书> 槽闭合形                             *)
(*   HD 证书（任意）+∀n |x_n|≤1、|h_n|≤1/4 → ∀n |W_n|≤1/3。             *)
(*   早项两支同过 D1 逐点 3/4 下界：n≥N0 支=Qinv(D_n)、n<N0 支=          *)
(*   Qinv(D_N0)（real_inv_pos S03:L6681 定义形）——任意证书皆可。        *)
(* ============================================================ *)
Lemma abl9_W_dom_cond : forall (x h : Real)
  (HD : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hhb : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)),
  forall n : nat,
  QleT' (Qabs (projT1 (real_mult (real_inv_pos
             (real_plus real_one (real_mult (real_plus x h) x)) HD) h) n))
        (1 # 3).
Proof.
  intros x h HD Hx Hhb n.
  destruct (abl9_inv_pos_shape
              (real_plus real_one (real_mult (real_plus x h) x)) HD)
    as [Ninv HNinv].
  assert (Hm : projT1 (real_mult (real_inv_pos
                     (real_plus real_one (real_mult (real_plus x h) x)) HD)
                     h) n
            == projT1 (real_inv_pos
                        (real_plus real_one (real_mult (real_plus x h) x)) HD) n
               * projT1 h n)
    by (rewrite (real_mult_proj (real_inv_pos
                    (real_plus real_one (real_mult (real_plus x h) x)) HD) h n);
        reflexivity).
  assert (Hd1n : projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
            == 1 + (projT1 x n + projT1 h n) * projT1 x n).
  { rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
    rewrite (real_mult_proj (real_plus x h) x n).
    rewrite (real_plus_proj x h n).
    rewrite (b3r_one_proj n). reflexivity. }
  assert (HdN : projT1 (real_plus real_one (real_mult (real_plus x h) x)) Ninv
            == 1 + (projT1 x Ninv + projT1 h Ninv) * projT1 x Ninv).
  { rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) Ninv).
    rewrite (real_mult_proj (real_plus x h) x Ninv).
    rewrite (real_plus_proj x h Ninv).
    rewrite (b3r_one_proj Ninv). reflexivity. }
  destruct (Nat.leb Ninv n) eqn:E.
  - (* n≥Ninv 支：Qinv(D_n)·h_n *)
    assert (Hshape : Qabs (projT1 (real_mult (real_inv_pos
                        (real_plus real_one (real_mult (real_plus x h) x)) HD)
                        h) n)
              == Qabs (Qinv (projT1 (real_plus real_one
                                (real_mult (real_plus x h) x)) n)
                       * projT1 h n)).
    { rewrite Hm. rewrite (HNinv n). rewrite E. reflexivity. }
    assert (Hfin : Qle (Qabs (projT1 (real_mult (real_inv_pos
                        (real_plus real_one (real_mult (real_plus x h) x)) HD)
                        h) n)) (1 # 3)).
    { rewrite Hshape.
      apply QleT'_to_Qle.
      apply (abl9_invq_bnd
               (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n)
               (projT1 h n)).
      + apply (qleT'_trans (3 # 4)
                 (1 + (projT1 x n + projT1 h n) * projT1 x n)
                 (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n)).
        * apply (abl9_q_path_den (projT1 x n) (projT1 h n)).
          -- apply QleT'_to_Qle. apply Hx.
          -- apply QleT'_to_Qle. apply Hhb.
        * apply qeq_leT'. apply Qeq_sym. exact Hd1n.
      + apply Hhb. }
    exact (Qle_to_QleT' _ _ Hfin).
  - (* n<Ninv 支：Qinv(D_Ninv)·h_n（|h_n|≤1/4 仍由 Hhb n 供） *)
    assert (Hshape : Qabs (projT1 (real_mult (real_inv_pos
                        (real_plus real_one (real_mult (real_plus x h) x)) HD)
                        h) n)
              == Qabs (Qinv (projT1 (real_plus real_one
                                (real_mult (real_plus x h) x)) Ninv)
                       * projT1 h n)).
    { rewrite Hm. rewrite (HNinv n). rewrite E. reflexivity. }
    assert (Hfin : Qle (Qabs (projT1 (real_mult (real_inv_pos
                        (real_plus real_one (real_mult (real_plus x h) x)) HD)
                        h) n)) (1 # 3)).
    { rewrite Hshape.
      apply QleT'_to_Qle.
      apply (abl9_invq_bnd
               (projT1 (real_plus real_one (real_mult (real_plus x h) x)) Ninv)
               (projT1 h n)).
      + apply (qleT'_trans (3 # 4)
                 (1 + (projT1 x Ninv + projT1 h Ninv) * projT1 x Ninv)
                 (projT1 (real_plus real_one (real_mult (real_plus x h) x)) Ninv)).
        * apply (abl9_q_path_den (projT1 x Ninv) (projT1 h Ninv)).
          -- apply QleT'_to_Qle. apply Hx.
          -- apply QleT'_to_Qle. apply Hhb.
        * apply qeq_leT'. apply Qeq_sym. exact HdN.
      + apply Hhb. }
    exact (Qle_to_QleT' _ _ Hfin).
Qed.

(* ============================================================ *)
(* P7·②桥闭合·主交付：Real 层斜率恒等                                  *)
(*   s·inv(1+u²) − Δw·inv(1+w₀²) == s²v·inv((1+(u+s)v)(1+u²))，         *)
(*   w₀:=w(u,v)、Δw:=w(u+s,v)−w(u,v)——phi'(t)=0 的 Real 层精确代数核。   *)
(*   逐点引擎=P1（Δw 点形经件21 wincr_pt 配形）；inv(1+w₀²) 经件21      *)
(*   wsq_pt 对齐 D²/G（Qinv 多 distr+involutive 链）。                  *)
(* ============================================================ *)
Lemma abl9_slope_real : forall (u v s : Real)
  (H1 : real_lt real_zero (real_plus real_one (real_mult (real_plus u s) v)))
  (H2 : real_lt real_zero (real_plus real_one (real_mult u v))),
  real_eq
    (real_plus
       (real_mult s (real_inv_pos (real_plus real_one (real_mult u u))
                       (b3r_one_sq_real_pos u)))
       (real_opp
          (real_mult
             (real_plus (abl9_brg_w_real (real_plus u s) v H1)
                        (real_opp (abl9_brg_w_real u v H2)))
             (real_inv_pos (real_plus real_one
                                (real_mult (abl9_brg_w_real u v H2)
                                           (abl9_brg_w_real u v H2)))
                          (abl9_wsq_pos (abl9_brg_w_real u v H2))))))
    (real_mult (real_mult (real_mult s s) v)
       (real_inv_pos
          (real_mult (real_plus real_one (real_mult (real_plus u s) v))
                     (real_plus real_one (real_mult u u)))
          (real_mult_positive
             (real_plus real_one (real_mult (real_plus u s) v))
             (real_plus real_one (real_mult u u)) H1
             (b3r_one_sq_real_pos u)))).
Proof.
  intros u v s H1 H2.
  pose proof H1 as H1C. destruct H1C as [e1 [He1 [M1 HM1]]].
  pose proof H2 as H2C. destruct H2C as [e2 [He2 [M2 HM2]]].
  destruct (abl9_brg_w_proj (real_plus u s) v H1) as [Nw1 HNw1].
  destruct (abl9_brg_w_proj u v H2) as [Nw2 HNw2].
  destruct (real_inv_proj (real_plus real_one (real_mult u u))
             (b3r_one_sq_real_pos u)) as [Nu HNu].
  destruct (real_inv_proj
              (real_mult (real_plus real_one (real_mult (real_plus u s) v))
                         (real_plus real_one (real_mult u u)))
              (real_mult_positive
                 (real_plus real_one (real_mult (real_plus u s) v))
                 (real_plus real_one (real_mult u u)) H1
                 (b3r_one_sq_real_pos u))) as [Nd HNd].
  destruct (real_inv_proj (real_plus real_one
                              (real_mult (abl9_brg_w_real u v H2)
                                         (abl9_brg_w_real u v H2)))
             (abl9_wsq_pos (abl9_brg_w_real u v H2))) as [Nw0 HNw0].
  apply (abl9_brg_pt_eq _ _
           (Nat.max Nw1 (Nat.max Nw2
              (Nat.max Nu (Nat.max Nd (Nat.max Nw0 (Nat.max M1 M2))))))).
  intros n Hn.
  assert (Hnw1 : (Nw1 <= n)%nat) by lia.
  assert (Hnw2 : (Nw2 <= n)%nat) by lia.
  assert (Hnu : (Nu <= n)%nat) by lia.
  assert (Hnd : (Nd <= n)%nat) by lia.
  assert (Hnw0 : (Nw0 <= n)%nat) by lia.
  assert (Hm1 : (M1 <= n)%nat) by lia.
  assert (Hm2 : (M2 <= n)%nat) by lia.
  assert (Huhp : projT1 (real_plus u s) n == projT1 u n + projT1 s n)
    by (apply real_plus_proj).
  (* 点值正性/非零（件21 工法） *)
  assert (Hlt1 : Qlt 0 (1 + (projT1 u n + projT1 s n) * projT1 v n)).
  { apply (Qlt_le_trans 0
             (projT1 (real_plus real_one (real_mult (real_plus u s) v)) n
              - projT1 real_zero n)
             (1 + (projT1 u n + projT1 s n) * projT1 v n)).
    - apply (Qlt_trans 0 e1 _).
      + apply QltT_to_Qlt. exact He1.
      + apply QltT_to_Qlt. apply (HM1 n). apply NatLe_lift. exact Hm1.
    - apply qeq_imp_qle.
      rewrite (real_plus_proj real_one (real_mult (real_plus u s) v) n).
      rewrite (real_mult_proj (real_plus u s) v n).
      rewrite Huhp.
      rewrite (b3r_one_proj n).
      cbn [projT1 real_zero]. ring. }
  assert (Hnz1 : ~ (1 + (projT1 u n + projT1 s n) * projT1 v n == 0)).
  { intro Hz.
    apply (Qlt_not_eq 0 (1 + (projT1 u n + projT1 s n) * projT1 v n) Hlt1).
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
      cbn [projT1 real_zero]. ring. }
  assert (Hnz2 : ~ (1 + projT1 u n * projT1 v n == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (1 + projT1 u n * projT1 v n) Hlt2).
    apply Qeq_sym. exact Hz. }
  (* inv(1+w₀²) 的 wsq 对齐链 *)
  assert (Hwsq := abl9_brg_wsq_pt (projT1 u n) (projT1 v n) Hnz2).
  assert (Hinvw0 :
    Qinv (1 + (projT1 u n - projT1 v n) * Qinv (1 + projT1 u n * projT1 v n)
              * ((projT1 u n - projT1 v n)
                 * Qinv (1 + projT1 u n * projT1 v n)))
    == (1 + projT1 u n * projT1 v n) * (1 + projT1 u n * projT1 v n)
       * Qinv ((1 + projT1 u n * projT1 u n)
               * (1 + projT1 v n * projT1 v n))).
  { rewrite Hwsq.
    rewrite (Qinv_mult_distr ((1 + projT1 u n * projT1 u n)
                              * (1 + projT1 v n * projT1 v n))
               (Qinv (1 + projT1 u n * projT1 v n)
                * Qinv (1 + projT1 u n * projT1 v n))).
    rewrite (Qinv_mult_distr (Qinv (1 + projT1 u n * projT1 v n))
               (Qinv (1 + projT1 u n * projT1 v n))).
    rewrite (Qinv_involutive (1 + projT1 u n * projT1 v n)).
    ring. }
  (* 全位投影展开（件21 工法） *)
  rewrite (real_plus_proj
             (real_mult s (real_inv_pos (real_plus real_one (real_mult u u))
                             (b3r_one_sq_real_pos u)))
             (real_opp
                (real_mult
                   (real_plus (abl9_brg_w_real (real_plus u s) v H1)
                              (real_opp (abl9_brg_w_real u v H2)))
                   (real_inv_pos (real_plus real_one
                                      (real_mult (abl9_brg_w_real u v H2)
                                                 (abl9_brg_w_real u v H2)))
                                (abl9_wsq_pos (abl9_brg_w_real u v H2)))))
             n).
  rewrite (real_opp_proj
             (real_mult
                (real_plus (abl9_brg_w_real (real_plus u s) v H1)
                           (real_opp (abl9_brg_w_real u v H2)))
                (real_inv_pos (real_plus real_one
                                   (real_mult (abl9_brg_w_real u v H2)
                                              (abl9_brg_w_real u v H2)))
                             (abl9_wsq_pos (abl9_brg_w_real u v H2)))) n).
  rewrite (real_mult_proj s (real_inv_pos (real_plus real_one (real_mult u u))
                              (b3r_one_sq_real_pos u)) n).
  rewrite (HNu n Hnu).
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (b3r_one_proj n).
  rewrite (real_mult_proj
             (real_plus (abl9_brg_w_real (real_plus u s) v H1)
                        (real_opp (abl9_brg_w_real u v H2)))
             (real_inv_pos (real_plus real_one
                                (real_mult (abl9_brg_w_real u v H2)
                                           (abl9_brg_w_real u v H2)))
                          (abl9_wsq_pos (abl9_brg_w_real u v H2))) n).
  rewrite (real_plus_proj (abl9_brg_w_real (real_plus u s) v H1)
             (real_opp (abl9_brg_w_real u v H2)) n).
  rewrite (real_opp_proj (abl9_brg_w_real u v H2) n).
  rewrite (HNw1 n Hnw1). rewrite Huhp.
  rewrite (HNw2 n Hnw2).
  rewrite (HNw0 n Hnw0).
  rewrite (real_plus_proj real_one
             (real_mult (abl9_brg_w_real u v H2) (abl9_brg_w_real u v H2)) n).
  rewrite (real_mult_proj (abl9_brg_w_real u v H2)
             (abl9_brg_w_real u v H2) n).
  rewrite (b3r_one_proj n).
  rewrite (HNw2 n Hnw2).
  rewrite (real_mult_proj (real_mult (real_mult s s) v)
             (real_inv_pos
                (real_mult (real_plus real_one (real_mult (real_plus u s) v))
                           (real_plus real_one (real_mult u u)))
                (real_mult_positive
                   (real_plus real_one (real_mult (real_plus u s) v))
                   (real_plus real_one (real_mult u u)) H1
                   (b3r_one_sq_real_pos u))) n).
  rewrite (real_mult_proj (real_mult s s) v n).
  rewrite (real_mult_proj s s n).
  rewrite (HNd n Hnd).
  rewrite (real_mult_proj (real_plus real_one (real_mult (real_plus u s) v))
             (real_plus real_one (real_mult u u)) n).
  rewrite (real_plus_proj real_one (real_mult (real_plus u s) v) n).
  rewrite (real_mult_proj (real_plus u s) v n).
  rewrite Huhp.
  rewrite (b3r_one_proj n).
  rewrite (real_plus_proj real_one (real_mult u u) n).
  rewrite (real_mult_proj u u n).
  rewrite (b3r_one_proj n).
  (* Δw 点形→wincr 形（件21），inv(1+w₀²)→D²/G（上链），P1 引擎 ring 桥闭合 *)
  rewrite (abl9_brg_wincr_pt (projT1 u n) (projT1 v n) (projT1 s n)
             Hnz1 Hnz2).
  rewrite Hinvw0.
  assert (Hsp := abl9_slope_pt (projT1 u n) (projT1 v n) (projT1 s n)
             Hlt1 Hlt2).
  transitivity (projT1 s n * Qinv (1 + projT1 u n * projT1 u n)
                + - ((projT1 s n * (1 + projT1 v n * projT1 v n)
                      * Qinv (1 + (projT1 u n + projT1 s n) * projT1 v n)
                      * Qinv (1 + projT1 u n * projT1 v n))
                     * ((1 + projT1 u n * projT1 v n)
                        * (1 + projT1 u n * projT1 v n)
                        * Qinv ((1 + projT1 u n * projT1 u n)
                                * (1 + projT1 v n * projT1 v n))))).
  - ring.
  - exact Hsp.
Qed.

(* ============================================================ *)
(* P8·拟文 <w 域证书> 槽配形：P6 经 qleT'_trans 升到 ≤1                  *)
(* ============================================================ *)
Lemma abl9_W_cert_unit : forall (x h : Real)
  (HD : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hhb : forall n : nat, QleT' (Qabs (projT1 h n)) (1 # 4)),
  forall n : nat,
  QleT' (Qabs (projT1 (real_mult (real_inv_pos
             (real_plus real_one (real_mult (real_plus x h) x)) HD) h) n)) 1.
Proof.
  intros x h HD Hx Hhb n.
  apply (qleT'_trans _ (1 # 3) _).
  - apply (abl9_W_dom_cond x h HD Hx Hhb n).
  - apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 名清单 9 = Qed 计数 9 = PA 语句 9，零差。           *)
(*   红线四条：纯构造性（全 Qed）；Set 层零 Prop 泄露（结论全            *)
(*   real_eq/real_lt/sigT/QleT' 形）；非平凡（P7 系②桥闭合主件：见证     *)
(*   max 全位投影+wsq 对齐链+wincr 配形+点形引擎，非薄转发）；           *)
(*   可提取（下检验，判据 Obj.magic 计 0）。                             *)
(* ============================================================ *)
Print Assumptions abl9_slope_pt.
Print Assumptions abl9_conv_bnd_pt.
Print Assumptions abl9_wsq_pos.
Print Assumptions abl9_D_pos_cond.
Print Assumptions abl9_invq_bnd.
Print Assumptions abl9_inv_pos_shape.
Print Assumptions abl9_W_dom_cond.
Print Assumptions abl9_slope_real.
Print Assumptions abl9_W_cert_unit.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_slope_real abl9_W_dom_cond abl9_conv_bnd_pt.
