(* ==========================================================================)
   abl9b_skeleton_30.v — 9b-1 装配骨架：域界①+w 界②+主装配骨架                  
   消融批 · arctan 导数活位 9b 装配片一（接续两前任：X30/X30' 均 ~67 分钟         
   纪律线停作，遗产=隔离池 /tmp/x30pool 55 件已建（S01–S11.v/.vo 五件套），落件/登记册
   未落——承前池复用（S11 md5 d571b0c02b1b8183228789bf10f9a646 抽查与 X27 规格/X14
   实查一致），骨架重落。）
   ── 切片规格·数学使命（X27 规格 §一①②＋§三 9b-1 行；实文判定条款 E12）：──────────
   目标 = 三件：
     ① 域界 abl9b_dom_pos：real_lt real_zero (1+(x+h)·x)，模板=b5a_one_plus_sq_pos
       （S11:L7554）同构替换，见证 (1#4)、N:=N4（Hh4 衰减位），逐点链
       x_n(x_n+h_n)=x_n²+x_n·h_n ≥ −|x_n||h_n| ≥ −|h_n|（Qsquare_nonneg＋Qabs 界），
       1+x_n(x_n+h_n) ≥ 3/4 > 1/4（Hx 逐点 ≤1、Hh4 逐点 |h_n|<1/4）。
     ② w 界 abl9b_w_bounds：w:=h·inv(1+x(x+h))；|w_n| ≤ (4/3)|h_n|（跨乘模板
       b5n_xinv_le S11:L11884）；|h_n|≤1/4 ⟹ |w_n| ≤ 1/3 Hw 证书原料（Qle_to_QleT'）。
     ③ abl9b 主装配骨架：依赖 9a-乙 差公式部分用显式假设位承载（Hdiff，注释
       「候 9a-乙 件19/20」），结论=活位原文逐字（X14登记册 §三·零，S11 L11854-11863
       Variable real_arctan_deriv 出节目标），δ 配方按 X27 总纲·2 修正
       δ := min(min(1/4, d8/2), eps/16)（d8=9a-甲(eps/8) 之 δ；含 (1/2) 收缩因子）。
   ── 依赖清单（条款 G·配方对实文的响亮登记）：───────────────────────────────────
   ① 9a-甲（abl_atan_small_incr）与 X16 辅件（abl9_qscale_pos）取 Require 池内
     已验落件 abl_arctan_smallincr_15 / abl_arctan_diff_16（真拷入 x30pool 编译绿，
     EXIT=0 实测；X19'/X19'' 落件 19/20 同款 Require 前件工法）；X27 规格所言
     「内联复制」针对 S11 内联集成（9b-4）场景，本骨架为独立落件，Require 是
     非环唯一通路（落件 Require S11，S11 不 Require 落件）。
   ② w证书全量卡点勘定（施工中新发现，条款 G）：|w_n|≤1 并非 ∀n 可得——
     real_inv_pos（S03:L6681）早位点取 Qinv(u_N0)，而 Hh4 之界是尾界，早段 h_n
     无界 ⟹ 早段 |w_n| 可爆。处置：w̃ := clamp(w)=real_min(real_max w (−1)) 1
     （real_min/real_max S07:L7214/7244 在册），clamp 与 w 逐点尾相等（域内恒等
     检验在案）⟹ real_eq 语义兼容（real_eq 系尾 ε 定义，S02:L399 实读），
     Hdiff 假设位即对 w̃ 陈述，9a-乙 终片对 raw w 的公式经尾传输即接入（不环）。
   ③ Qinv_le_mono 在带 Stdlib 无此名（检验实录 NameNotFound），跨乘改走 S11 在册
     b5n_xinv_le（1·(3/4) ≤ D 形实例）；Qabs 两界化用 Stdlib Qabs_Qle_condition /
     Qabs_Qlt_condition（Qabs.v 实读在册）。
   ── 红线自检·构造性注记：────────────────────────────────────────────────────────
   纯构造性（全链 Qed 真构造，零 Admitted/Axiom）；Set 层零 Prop 泄露      
   （sigT/And/real_lt/real_le/QleT' 全 Type/Set 形）；非平凡（①②为真构造，
   主件 δ 配方+min 拆分+w 域证书+9a-甲接入+逐点余项+margin 闭合全实链）；
   可提取（Print Assumptions 锚 + Recursive Extraction 检验，判据 Closed +
   Obj.magic=0）。
   编译配方：source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x30pool "" abl9b_skeleton_30.v
   （隔离池 /tmp/x30pool，S01–S11+落件15/16 共 13 件 .vo 在链，cwd 异地，
   发起前进程 <3，窗满等 60s 禁硬闯。）
   ── X52 修复登记（条款 G 响亮）───────────────────────────────────────────
   本件 9b-1 交付时主件 abl9b 未绿验（登记册编译节系空白区）。X52（9b-2 使用  
   方）入池编译实录【红】于 Hfin 链：原 L742 中项缺 |Δ3|=(1/2)en·hn 预算（数学
   断链）+L746 Qplus_le_compat 隐式分裂歧义+终段 nra 缺 en'≥0。修复三处：L522
   后新增 He1pos assert；Hfin 第二翼中项补 (1/2)en·hn；|Δ2|/|Δ3| 两翼显式定位。
   绿验证据见登记册-abl9b_skeleton_30 编译绿验节（X52 补录，池 /tmp/x52pool）。
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
Require Import abl_arctan_smallincr_15.
Require Import abl_arctan_diff_16.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* Q 层基建（检验件实证后转录：①域链/②跨乘链/clamp 名）           *)
(* ============================================================ *)

(* Qabs 两界化（Stdlib Qabs_Qle_condition） *)
Lemma abl9b_abs2 : forall (a : Q), Qle (Qabs a) 1 -> Qle (-1) a /\ Qle a 1.
Proof.
  intros a H. apply Qabs_Qle_condition in H. exact H.
Qed.

(* ① Q 核：|xn|≤1、|hn|<1/4 ⟹ 3/4 ≤ 1+(xn+hn)·xn 且 (1#4)<T 1+(xn+hn)·xn
   （链：x_n(x_n+h_n)=x_n²+x_nh_n ≥ 0−|xn||hn| ≥ −|hn|，X27 §一① 逐字） *)
Lemma abl9b_q_dom34 : forall (xn hn : Q),
  Qle (Qabs xn) 1 -> Qlt (Qabs hn) (1#4) -> Qle (3#4) (1 + (xn + hn) * xn).
Proof.
  intros xn hn Hx Hh.
  apply Qabs_Qle_condition in Hx.
  apply Qabs_Qlt_condition in Hh.
  assert (Hs : Qle 0 (xn * xn)) by apply Qsquare_nonneg.
  nra.
Qed.

Lemma abl9b_q_dom_T : forall (xn hn : Q),
  Qle (Qabs xn) 1 -> Qlt (Qabs hn) (1#4) -> QltT (1#4) (1 + (xn + hn) * xn).
Proof.
  intros xn hn Hx Hh.
  apply Qlt_to_QltT.
  assert (Hle : Qle (3#4) (1 + (xn + hn) * xn)) by (apply abl9b_q_dom34; assumption).
  apply Qabs_Qle_condition in Hx.
  apply Qabs_Qlt_condition in Hh.
  assert (Hs : Qle 0 (xn * xn)) by apply Qsquare_nonneg.
  nra.
Qed.

(* ② Q 核：D≥3/4、|hn|<1/4 ⟹ |hn·inv D| ≤ (4/3)|hn| ≤ 1/3
   （跨乘=b5n_xinv_le 1·(3/4)≤D 形实例；Qinv_le_mono 带内无此名，见头注③） *)
Lemma abl9b_q_wbnd : forall (hn D : Q),
  Qle (3#4) D -> Qlt (Qabs hn) (1#4) ->
  Qle (Qabs (hn * Qinv D)) (Qmult (4#3) (Qabs hn))
  /\ Qle (Qabs (hn * Qinv D)) (1#3).
Proof.
  intros hn D HD Hh.
  assert (Ha0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
  assert (HDpos : Qlt 0 D).
  { apply (Qlt_le_trans 0 (3#4) D); [unfold Qlt; simpl; lia | exact HD]. }
  assert (HDinv0 : Qlt 0 (Qinv D)) by (apply Qinv_lt_0_compat; exact HDpos).
  assert (Hinv1 : Qle (1 * Qinv D) (Qinv (3#4))).
  { apply (b5n_xinv_le 1 D (3#4)).
    - exact HDpos.
    - unfold Qlt; simpl; lia.
    - nra. }
  assert (Hinv : Qle (Qinv D) (4#3)).
  { apply (Qle_trans (Qinv D) (1 * Qinv D) (4#3)).
    - apply qeq_imp_qle. ring.
    - apply (Qle_trans (1 * Qinv D) (Qinv (3#4)) (4#3)).
      + exact Hinv1.
      + apply qeq_imp_qle. reflexivity. }
  assert (Habs : Qabs (hn * Qinv D) == Qabs hn * Qinv D).
  { rewrite Qabs_Qmult.
    rewrite (Qabs_pos (Qinv D) (Qlt_le_weak 0 (Qinv D) HDinv0)).
    reflexivity. }
  split.
  - rewrite Habs. nra.
  - rewrite Habs. nra.
Qed.

(* clamp 名检验转录：|Qmin(Qmax a,−1) 1| ≤ 1；域内 clamp 恒等 *)
Lemma abl9b_q_clamp_bnd : forall (a : Q), Qle (Qabs (Qmin (Qmax a (-1)) 1)) 1.
Proof.
  intros a.
  apply Qabs_Qle_condition. split.
  - apply Q.min_glb.
    + apply Q.le_max_r.
    + unfold Qle. simpl. lia.
  - apply Q.le_min_r.
Qed.

Lemma abl9b_q_clamp_id : forall (a : Q),
  Qle (-1) a -> Qle a 1 -> Qmin (Qmax a (-1)) 1 == a.
Proof.
  intros a H1 H2.
  rewrite (Q.max_l a (-1) H1).
  apply Q.min_l. exact H2.
Qed.

(* ============================================================ *)
(* ① 域界：0 < 1+x(x+h)（见证 (1#4)，N:=N4；b5a_one_plus_sq_pos   *)
(*    S11:L7554 同构替换——证书自建，不引 b5a 本体：x(x+h) 非 u²形） *)
(* ============================================================ *)

(* Hh4 尾提取：|h_n| < 1/4（n ≥ N4） *)
Lemma abl9b_h_abs_tail : forall (h : Real),
  real_lt (real_abs h) (real_const (1 # 4)) ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    Qlt (Qabs (projT1 h n)) (1 # 4)).
Proof.
  intros h Hh4.
  destruct Hh4 as [e4 [He4T [N4 HN4]]].
  exists N4. intros n Hn.
  assert (Hlt : Qlt e4 (Qminus (1#4) (Qabs (projT1 h n)))).
  { apply QltT_to_Qlt.
    apply (qltT_eq_compat_r (Qminus (1#4) (Qabs (projT1 h n)))
                            (Qminus (projT1 (real_const (1#4)) n)
                                    (projT1 (real_abs h) n)) e4).
    - rewrite (real_const_proj (1#4) n). rewrite (real_abs_proj h n). reflexivity.
    - exact (HN4 n Hn). }
  assert (He40 : Qlt 0 e4) by (apply QltT_to_Qlt; exact He4T).
  nra.
Qed.

(* 域界主件：real_lt real_zero (1+(x+h)·x)（X27 §一①，活位 inv 证书位） *)
Lemma abl9b_dom_pos : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4))),
  real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)).
Proof.
  intros x h Hx Hh4.
  destruct (abl9b_h_abs_tail h Hh4) as [N4 HN4].
  unfold real_lt.
  exists (1 # 4)%Q.
  split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists N4.
    intros n Hn.
    assert (Hxa : Qle (Qabs (projT1 x n)) 1) by (apply QleT'_to_Qle; apply Hx).
    (* 逐点等式：D_n − 0 == 1+(x_n+h_n)x_n（b5a_one_plus_sq_pos 位链同构） *)
    assert (Hq : projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
                 - projT1 real_zero n
                 == 1 + ((projT1 x n + projT1 h n) * projT1 x n)).
    { setoid_rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
      setoid_rewrite (real_mult_proj (real_plus x h) x n).
      setoid_rewrite (real_plus_proj x h n).
      cbn [projT1 real_one real_zero].
      ring. }
    apply (b5a_QltT_eq_r (1#4) _ _ Hq).
    apply abl9b_q_dom_T.
    + exact Hxa.
    + exact (HN4 n Hn).
Qed.

(* ============================================================ *)
(* ② w 定义与界：w := h·inv(1+x(x+h))；|w_n| ≤ (4/3)|h_n| 且       *)
(*    |h_n|<1/4 ⟹ |w_n| ≤ 1/3（Hw 证书原料，Qle_to_QleT' 前置）    *)
(* ============================================================ *)

Definition abl9b_w (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))) : Real :=
  real_mult h (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x)) Hd).

Lemma abl9b_w_bounds : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    And (QleT' (Qabs (projT1 (abl9b_w x h Hd) n)) (Qmult (4#3) (Qabs (projT1 h n))))
        (QleT' (Qabs (projT1 (abl9b_w x h Hd) n)) (1#3))).
(* X52 语句形修复（条款 G）：原稿 And 两翼取 Qle（Prop），在 sigT 下被提取器
   物化触发 prod-Prop 硬限（skel10.log L831 实录，X27 勘名 prod-Prop 墙）。
   两翼升 QleT'（S02 Set 形 Id (Qle_bool x y) true；Qle_to_QleT'/
   QleT'_to_Qle 双向桥在册），使用位三处解包（Hw13b×2、Hw43c）。 *)
Proof.
  intros x h Hx Hh4 Hd.
  destruct (abl9b_h_abs_tail h Hh4) as [N4 HN4].
  destruct (real_inv_proj (real_plus real_one (real_mult (real_plus x h) x)) Hd)
    as [Ninv HNinv].
  exists (Nat.max N4 Ninv).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
  assert (Hninv : (Ninv <= n)%nat) by lia.
  (* D_n 逐点位值与 3/4 界（① 链） *)
  assert (HDproj : projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
                   == 1 + ((projT1 x n + projT1 h n) * projT1 x n)).
  { setoid_rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
    setoid_rewrite (real_mult_proj (real_plus x h) x n).
    setoid_rewrite (real_plus_proj x h n).
    cbn [projT1 real_one].
    ring. }
  assert (HD34 : Qle (3#4) (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n)).
  { rewrite HDproj.
    apply abl9b_q_dom34.
    - apply QleT'_to_Qle. apply Hx.
    - exact (HN4 n Hn4). }
  (* w_n 逐点值 == h_n · Qinv D_n *)
  assert (Hwv : projT1 (abl9b_w x h Hd) n
                == projT1 h n * Qinv (projT1 (real_plus real_one
                       (real_mult (real_plus x h) x)) n)).
  { unfold abl9b_w.
    rewrite (real_mult_proj h (real_inv_pos (real_plus real_one
      (real_mult (real_plus x h) x)) Hd) n).
    rewrite (HNinv n Hninv).
    reflexivity. }
  (* ② Q 核实例化 + 沿点位等式传输 *)
  destruct (abl9b_q_wbnd (projT1 h n)
             (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n)
             HD34 (HN4 n Hn4)) as [Hb43 Hb13].
  assert (Hab : Qabs (projT1 (abl9b_w x h Hd) n)
                == Qabs (projT1 h n
                         * Qinv (projT1 (real_plus real_one
                              (real_mult (real_plus x h) x)) n))).
  { apply (Qabs_wd _ _). exact Hwv. }
  split.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs (projT1 h n
            * Qinv (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n))) _).
    + apply qeq_imp_qle. exact Hab.
    + exact Hb43.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs (projT1 h n
            * Qinv (projT1 (real_plus real_one (real_mult (real_plus x h) x)) n))) _).
    + apply qeq_imp_qle. exact Hab.
    + exact Hb13.
Qed.

(* w 的 clamp 代表元：w̃ := min(max(w,−1),1)（|w̃_n|≤1 全域证书；早段 h_n 无界
   卡点的处置，见头注②；clamp 与 w 逐点尾相等 ⟹ real_eq 尾语义兼容） *)
Definition abl9b_wc (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))) : Real :=
  real_min (real_max (abl9b_w x h Hd) (real_const (-1))) (real_const 1).

(* Hw 全域证书：∀n |w̃_n| ≤ 1（real_min/real_max 逐点投影 + Q 层 clamp 界） *)
Lemma abl9b_w_clamp_dom : forall (w : Real),
  forall n : nat,
  QleT' (Qabs (projT1 (real_min (real_max w (real_const (-1))) (real_const 1)) n)) 1.
Proof.
  intros w n.
  pose proof (real_min_proj (real_max w (real_const (-1))) (real_const 1) n) as H1.
  pose proof (real_max_proj w (real_const (-1)) n) as H2.
  rewrite H2 in H1.
  apply Qle_to_QleT'.
  rewrite H1.
  apply abl9b_q_clamp_bnd.
Qed.

(* clamp 域内恒等：|w_n| ≤ 1/3 点位 ⟹ w̃_n == w_n（点位） *)
Lemma abl9b_wc_id_pt : forall (w : Real) (n : nat),
  Qle (Qabs (projT1 w n)) (1#3) ->
  projT1 (real_min (real_max w (real_const (-1))) (real_const 1)) n == projT1 w n.
Proof.
  intros w n Hb.
  apply Qabs_Qle_condition in Hb.
  destruct Hb as [Hlo Hhi].
  rewrite (real_min_proj (real_max w (real_const (-1))) (real_const 1) n).
  rewrite (real_max_proj w (real_const (-1)) n).
  rewrite (real_const_proj (-1) n).
  rewrite (real_const_proj 1 n).
  apply abl9b_q_clamp_id.
  - apply (Qle_trans (-1) (-(1#3)) (projT1 w n)).
    + unfold Qle. simpl. lia.
    + exact Hlo.
  - apply (Qle_trans (projT1 w n) (1#3) 1).
    + exact Hhi.
    + unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* ③ 主装配骨架 abl9b（活位原文逐字=X14 登记册 §三·零；差公式=显式   *)
(*    假设位 Hdiff 候 9a-乙 件19/20；δ 配方=总纲·2 修正形           *)
(*    min(min(1/4, d8/2), eps/16)，d8=9a-甲(eps/8) 之 δ）          *)
(* ============================================================ *)

Lemma abl9b :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  (* —— 候 9a-乙 件19/20：差公式显式假设位（终片 ablated 时以差公式件实证替换；
        w 位取 clamp 代表元 abl9b_wc，其 Hw 全域证书=abl9b_w_clamp_dom 在案；
        9a-乙 raw-w 形经 clamp 域内恒等（|w|≤1/3 尾域）+real_eq 尾传输即接入） —— *)
  (forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
     (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
   real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
              (real_opp (cauchy_real_arctan x Hx)))
           (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
              (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4))))) ->
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
Proof.
  intros x Hx Hdiff eps Heps.
  (* —— 0. 9a-甲 (eps/8) 实例化与 δ 配方（总纲·2：(1/2) 收缩因子在案） —— *)
  assert (Hlt4 : Qlt 0 (1#4)) by (unfold Qlt; simpl; lia).
  assert (Hlt8 : Qlt 0 (1#8)) by (unfold Qlt; simpl; lia).
  assert (Hlt2 : Qlt 0 (1#2)) by (unfold Qlt; simpl; lia).
  assert (Hlt16 : Qlt 0 (1#16)) by (unfold Qlt; simpl; lia).
  assert (Heps8 : real_lt real_zero (real_mult (real_const (1#8)) eps))
    by (apply abl9_qscale_pos; [exact Hlt8 | exact Heps]).
  destruct (abl_atan_small_incr (real_mult (real_const (1#8)) eps) Heps8)
    as [d8 [Hd8pos Hstep8]].
  assert (Hd8h : real_lt real_zero (real_mult (real_const (1#2)) d8))
    by (apply abl9_qscale_pos; [exact Hlt2 | exact Hd8pos]).
  assert (Hepsc : real_lt real_zero (real_mult (real_const (1#16)) eps))
    by (apply abl9_qscale_pos; [exact Hlt16 | exact Heps]).
  exists (real_min (real_min (real_const (1#4)) (real_mult (real_const (1#2)) d8))
                  (real_mult (real_const (1#16)) eps)).
  split.
  - apply real_min_pos.
    + apply real_min_pos.
      * apply real_const_pos. apply Qlt_to_QltT. exact Hlt4.
      * exact Hd8h.
    + exact Hepsc.
  - intros h Hh Hxh eps' Heps'.
    (* —— A. δ 三臂拆分（real_min_lt_l/r，S08:L3979/4007 工法） —— *)
    assert (HhA : real_lt (real_abs h)
              (real_min (real_const (1#4)) (real_mult (real_const (1#2)) d8))).
    { apply (real_min_lt_l h (real_min (real_const (1#4)) (real_mult (real_const (1#2)) d8))
                             (real_mult (real_const (1#16)) eps)). exact Hh. }
    assert (Hh14 : real_lt (real_abs h) (real_const (1#4))).
    { apply (real_min_lt_l h (real_const (1#4)) (real_mult (real_const (1#2)) d8)). exact HhA. }
    assert (HhW : real_lt (real_abs h) (real_mult (real_const (1#2)) d8)).
    { apply (real_min_lt_r h (real_const (1#4)) (real_mult (real_const (1#2)) d8)). exact HhA. }
    assert (Hh16 : real_lt (real_abs h) (real_mult (real_const (1#16)) eps)).
    { apply (real_min_lt_r h (real_min (real_const (1#4)) (real_mult (real_const (1#2)) d8))
                             (real_mult (real_const (1#16)) eps)). exact Hh. }
    (* —— B. w/w̃ 与证书（Hd 用 set-let 绑定：与 Hdiff 假设位证书同一证明项——
          real_inv_pos 定义对证明项做 match，假设位不可转换，条款 G） —— *)
    set (Hd := abl9b_dom_pos x h Hx Hh14).
    assert (Hwb := abl9b_w_bounds x h Hx Hh14 Hd).
    destruct Hwb as [Nw HNw].
    (* —— C. real_lt (real_abs w̃) d8（总纲·2 e/4 见证构造） —— *)
    destruct Hd8pos as [ed [HedT [Nd HNd]]].
    destruct HhW as [eh8 [Heh8T [Nh8 HNh8]]].
    assert (Hed0 : Qlt 0 ed) by (apply QltT_to_Qlt; exact HedT).
    assert (Heh80 : Qlt 0 eh8) by (apply QltT_to_Qlt; exact Heh8T).
    assert (Hh8 : forall n : nat, (Nh8 <= n)%nat ->
              Qlt (Qabs (projT1 h n)) (Qmult (1#2) (projT1 d8 n))).
    { intros n Hn.
      assert (Heq : Qminus (Qmult (1#2) (projT1 d8 n)) (Qabs (projT1 h n))
                    == Qminus (projT1 (real_mult (real_const (1#2)) d8) n)
                              (projT1 (real_abs h) n)).
      { rewrite (real_mult_proj (real_const (1#2)) d8 n).
        rewrite (real_const_proj (1#2) n).
        rewrite (real_abs_proj h n). reflexivity. }
      pose proof (HNh8 n (NatLe_lift _ _ Hn)) as HH.
      assert (HH2 : QltT eh8 (Qminus (Qmult (1#2) (projT1 d8 n)) (Qabs (projT1 h n))))
        by (apply (qltT_eq_compat_r
                    (Qminus (Qmult (1#2) (projT1 d8 n)) (Qabs (projT1 h n)))
                    (Qminus (projT1 (real_mult (real_const (1#2)) d8) n)
                            (projT1 (real_abs h) n))
                    eh8 Heq HH)).
      apply QltT_to_Qlt in HH2.
      assert (Heh80' : Qlt 0 eh8) by (apply QltT_to_Qlt; exact Heh8T).
      nra. }
    assert (Hd8lt : forall n : nat, (Nd <= n)%nat -> Qlt ed (projT1 d8 n)).
    { intros n Hn. apply QltT_to_Qlt.
      apply (qltT_eq_compat_r (projT1 d8 n)
                              (Qminus (projT1 d8 n) (projT1 real_zero n)) ed).
      - cbn [projT1 real_zero]. ring.
      - exact (HNd n (NatLe_lift _ _ Hn)). }
    assert (Hwlt : real_lt (real_abs (abl9b_wc x h Hd)) d8).
    { unfold real_lt.
      exists (Qmult (1#4) ed).
      split.
      - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#4) ed).
        + exact Hlt4. + exact Hed0.
      - exists (Nat.max (Nat.max Nd Nh8) Nw).
        intros n Hn.
        apply NatLe_drop in Hn.
        assert (Hnd : (Nd <= n)%nat) by lia.
        assert (Hnh : (Nh8 <= n)%nat) by lia.
        assert (Hnw : NatLe Nw n) by (apply NatLe_lift; lia).
        destruct (HNw n Hnw) as [Hw43 Hw13b].
        (* X52：② 语句形升 QleT' 后，nra 不视 Id 形——就地解包 Q 形供使用 *)
        assert (Hw43q : Qle (Qabs (projT1 (abl9b_w x h Hd) n))
                          (Qmult (4#3) (Qabs (projT1 h n))))
          by (apply QleT'_to_Qle; exact Hw43).
        assert (Hw13q : Qle (Qabs (projT1 (abl9b_w x h Hd) n)) (1#3))
          by (apply QleT'_to_Qle; exact Hw13b).
        assert (Hcid : projT1 (abl9b_wc x h Hd) n == projT1 (abl9b_w x h Hd) n)
          by exact (abl9b_wc_id_pt (abl9b_w x h Hd) n Hw13q).
        apply (qltT_eq_compat_r (Qminus (projT1 d8 n) (projT1 (real_abs (abl9b_wc x h Hd)) n))
                                (Qminus (projT1 d8 n) (Qabs (projT1 (abl9b_wc x h Hd) n)))
                                (Qmult (1#4) ed)).
        + rewrite (real_abs_proj (abl9b_wc x h Hd) n). reflexivity.
        + apply (qltT_eq_compat_r (Qminus (projT1 d8 n) (Qabs (projT1 (abl9b_wc x h Hd) n)))
                                  (Qminus (projT1 d8 n) (Qabs (projT1 (abl9b_w x h Hd) n)))
                                  (Qmult (1#4) ed)).
          * rewrite Hcid. reflexivity.
          * apply Qlt_to_QltT.
            assert (Hh8' : Qlt (Qabs (projT1 h n)) (Qmult (1#2) (projT1 d8 n)))
              by (apply Hh8; exact Hnh).
            assert (Hd8' : Qlt ed (projT1 d8 n)) by (apply Hd8lt; exact Hnd).
            nra. }
    (* —— D. 9a-甲 接入（g:=w̃，eps'':=eps'/4）与 slack 逐点投影 —— *)
    assert (Heps14 : real_lt real_zero (real_mult (real_const (1#4)) eps'))
      by (apply abl9_qscale_pos; [exact Hlt4 | exact Heps']).
    assert (Hwc : forall n : nat, QleT' (Qabs (projT1 (abl9b_wc x h Hd) n)) 1)
      by exact (abl9b_w_clamp_dom (abl9b_w x h Hd)).
    specialize (Hstep8 (abl9b_wc x h Hd) Hwlt Hwc (real_mult (real_const (1#4)) eps') Heps14).
    destruct (b5i_abs_le_pointwise
                (real_plus (cauchy_real_arctan (abl9b_wc x h Hd) Hwc)
                           (real_opp (abl9b_wc x h Hd)))
                (real_plus (real_mult (real_mult (real_const (1#8)) eps)
                            (real_abs (abl9b_wc x h Hd)))
                           (real_mult (real_const (1#4)) eps'))
                Hstep8 (real_mult (real_const (1#4)) eps') Heps14)
      as [N1 HN1].
    (* —— E. eps'/eps 见证与 Hdiff 逐点提取 —— *)
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct Hh16 as [eh16 [Heh16T [Nh16 HNh16]]].
    assert (Heh160 : Qlt 0 eh16) by (apply QltT_to_Qlt; exact Heh16T).
    assert (Hh16lt : forall n : nat, (Nh16 <= n)%nat ->
              Qlt (Qabs (projT1 h n)) (Qmult (1#16) (projT1 eps n))).
    { intros n Hn.
      assert (Heq : Qminus (Qmult (1#16) (projT1 eps n)) (Qabs (projT1 h n))
                    == Qminus (projT1 (real_mult (real_const (1#16)) eps) n)
                              (projT1 (real_abs h) n)).
      { rewrite (real_mult_proj (real_const (1#16)) eps n).
        rewrite (real_const_proj (1#16) n).
        rewrite (real_abs_proj h n). reflexivity. }
      pose proof (HNh16 n (NatLe_lift _ _ Hn)) as HH.
      assert (HH2 : QltT eh16 (Qminus (Qmult (1#16) (projT1 eps n)) (Qabs (projT1 h n))))
        by (apply (qltT_eq_compat_r
                    (Qminus (Qmult (1#16) (projT1 eps n)) (Qabs (projT1 h n)))
                    (Qminus (projT1 (real_mult (real_const (1#16)) eps) n)
                            (projT1 (real_abs h) n))
                    eh16 Heq HH)).
      apply QltT_to_Qlt in HH2.
      assert (Heh160' : Qlt 0 eh16) by (apply QltT_to_Qlt; exact Heh16T).
      nra. }
    assert (HetaT : QltT 0 (Qmult (1#16) e1)).
    { apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#16) e1).
      - exact Hlt16.
      - apply QltT_to_Qlt. exact He1T. }
    destruct (Hdiff h Hh14 Hxh (Qmult (1#16) e1) HetaT) as [N2 HN2].
    (* —— F. 基础证书投影 —— *)
    destruct (abl9b_h_abs_tail h Hh14) as [N4 HN4t].
    destruct (real_inv_proj (real_plus real_one (real_mult (real_plus x h) x)) Hd)
      as [NinvD HNinvD].
    destruct (real_inv_proj (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x))
      as [Ninv2 HNinv2].
    (* —— G. 闭合（b5a_sin_atan_diff 尾段工法：left+eta+Nmax+逐点预算链） —— *)
    left.
    exists (Qmult (1#16) e1). split.
    + exact HetaT.
    + exists (Nat.max (Nat.max (Nat.max N1 N2) (Nat.max Nd Nh8))
             (Nat.max (Nat.max Nh16 Nw)
                      (Nat.max (Nat.max N4 NinvD)
                               (Nat.max (Nat.max Ninv2 Ne1) Ne0)))).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hnd : (Nd <= n)%nat) by lia.
      assert (Hnh : (Nh8 <= n)%nat) by lia.
      assert (Hnh16 : (Nh16 <= n)%nat) by lia.
      assert (Hnw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
      assert (HninvD : (NinvD <= n)%nat) by lia.
      assert (Hninv2 : (Ninv2 <= n)%nat) by lia.
      assert (Hne0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (Hne1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (wn := projT1 (abl9b_wc x h Hd) n).
      set (wnr := projT1 (abl9b_w x h Hd) n).
      set (xnp := projT1 x n). set (hnp := projT1 h n).
      set (Dv := 1 + ((xnp + hnp) * xnp)).
      set (Ev := 1 + (xnp * xnp)).
      set (atanxh := arctan_partial n (projT1 (real_plus x h) n)).
      set (atanx := arctan_partial n (projT1 x n)).
      set (atanw := arctan_partial n wn).
      assert (Hen' : Qle e1 en') by (apply Qlt_le_weak; exact (He1lt n Hne1)).
      (* X52 修复补件：en' ≥ 0（e1>0 且 e1≤en'）——终段 nra 预算链的必需非负元，
         骨架原稿缺失（L759 nra 不可闭），见登记册-abl9b_skeleton_30 编译绿验节。*)
      assert (He1pos : Qle 0 en')
        by (apply (Qle_trans 0 e1 en');
            [apply Qlt_le_weak; apply QltT_to_Qlt; exact He1T | exact Hen']).
      assert (Hepos : Qle 0 en).
      { apply (Qle_trans 0 e0 en).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (He0lt n Hne0). }
      assert (Hhn0 : Qle 0 hn) by apply Qabs_nonneg.
      assert (Hh16n : Qlt hn (Qmult (1#16) en)) by (apply Hh16lt; exact Hnh16).
      (* —— w 值链与各界 —— *)
      destruct (HNw n Hnw) as [Hw43 Hw13b].
      (* X52：就地解包 Q 形（② 语句形升 QleT' 后 nra 不视 Id 形） *)
      assert (Hw43q : Qle (Qabs (projT1 (abl9b_w x h Hd) n))
                        (Qmult (4#3) (Qabs (projT1 h n))))
        by (apply QleT'_to_Qle; exact Hw43).
      assert (Hw13q : Qle (Qabs (projT1 (abl9b_w x h Hd) n)) (1#3))
        by (apply QleT'_to_Qle; exact Hw13b).
      assert (Hcid : wn == wnr)
        by exact (abl9b_wc_id_pt (abl9b_w x h Hd) n Hw13q).
      assert (HDproj : projT1 (real_plus real_one (real_mult (real_plus x h) x)) n == Dv).
      { setoid_rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
        setoid_rewrite (real_mult_proj (real_plus x h) x n).
        setoid_rewrite (real_plus_proj x h n).
        cbn [projT1 real_one]. reflexivity. }
      assert (HD34 : Qle (3#4) Dv).
      { unfold Dv. apply abl9b_q_dom34.
        - apply QleT'_to_Qle. apply Hx.
        - exact (HN4t n Hn4). }
      assert (Hwv : wnr == hnp * Qinv Dv).
      { unfold wnr.
        rewrite (real_mult_proj h (real_inv_pos (real_plus real_one
                  (real_mult (real_plus x h) x)) Hd) n).
        rewrite (HNinvD n HninvD).
        rewrite HDproj. reflexivity. }
      assert (HEproj : projT1 (real_plus real_one (real_mult x x)) n == Ev).
      { setoid_rewrite (real_plus_proj real_one (real_mult x x) n).
        setoid_rewrite (real_mult_proj x x n).
        cbn [projT1 real_one]. reflexivity. }
      assert (HE1 : Qle 1 Ev).
      { unfold Ev. apply (Qle_trans 1 (1 + 0) (1 + xnp * xnp)).
        - unfold Qle. simpl. lia.
        - apply Qplus_le_compat.
          + unfold Qle. simpl. lia.
          + apply Qsquare_nonneg. }
      assert (Hiv : projT1 (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                 (b5a_one_plus_sq_pos x)) h) n
                == Qinv Ev * hnp).
      { rewrite (real_mult_proj (real_inv_pos (real_plus real_one (real_mult x x))
                   (b5a_one_plus_sq_pos x)) h n).
        rewrite (HNinv2 n Hninv2). rewrite HEproj. reflexivity. }
      (* arctan 投影恒等（definitional） *)
      assert (Hapw : projT1 (cauchy_real_arctan (abl9b_wc x h Hd)
                                (abl9b_w_clamp_dom (abl9b_w x h Hd))) n == atanw).
      { unfold atanw. apply arctan_real_proj. }
      (* —— 余项界：|wn − inv(1+x²)·h_n| ≤ (1/2 en)hn（精确差 + 跨乘） —— *)
      assert (HR2 : Qle (Qabs (wn - Qinv Ev * hnp)) (Qmult (Qmult (1#2) en) hn)).
      { assert (HpD : Qlt 0 Dv).
        { apply (Qlt_le_trans 0 (3#4) Dv); [unfold Qlt; simpl; lia | exact HD34]. }
        assert (HpE : Qlt 0 Ev).
        { apply (Qlt_le_trans 0 1 Ev); [unfold Qlt; simpl; lia | exact HE1]. }
        assert (HpDE : Qlt 0 (Dv * Ev))
          by (apply (Qmult_lt_0_compat Dv Ev); [exact HpD | exact HpE]).
        assert (HzDE : ~ (Dv * Ev == 0)).
        { intro Hz. rewrite Hz in HpDE.
          exact (Qlt_not_eq 0 0 HpDE (Qeq_refl 0)). }
        assert (HzD : ~ (Dv == 0)).
        { intro Hz.
          assert (Hle0 : Qle Dv 0) by (apply qeq_imp_qle; exact Hz).
          assert (Hbad : Qle (3#4) 0)
            by (apply (Qle_trans (3#4) Dv 0); [exact HD34 | exact Hle0]).
          exact (Qlt_not_eq 0 0 (Qlt_le_trans 0 (3#4) 0 Hlt4 Hbad) (Qeq_refl 0)). }
        assert (HzE : ~ (Ev == 0)).
        { intro Hz. rewrite Hz in HpE.
          exact (Qlt_not_eq 0 0 HpE (Qeq_refl 0)). }
        assert (HmD' : Qinv Dv * Dv == 1)
          by (rewrite Qmult_comm; apply Qmult_inv_r; exact HzD).
        assert (HmE' : Qinv Ev * Ev == 1)
          by (rewrite Qmult_comm; apply Qmult_inv_r; exact HzE).
        assert (HmDE : Dv * Ev * Qinv (Dv * Ev) == 1)
          by (apply Qmult_inv_r; exact HzDE).
        assert (Hs2 : (Qinv Dv - Qinv Ev) * (Dv * Ev) == Ev - Dv).
        { assert (Hfac : (Qinv Dv - Qinv Ev) * (Dv * Ev)
                         == (Qinv Dv * Dv) * Ev - (Qinv Ev * Ev) * Dv) by ring.
          rewrite Hfac, HmD', HmE'. ring. }
        assert (Hside : (Ev - Dv) * Qinv (Dv * Ev)
                        == (Qinv Dv - Qinv Ev) * (Dv * Ev) * Qinv (Dv * Ev)).
        { rewrite <- Hs2. reflexivity. }
        assert (Hsplit : Qinv Dv - Qinv Ev == (Ev - Dv) * Qinv (Dv * Ev)).
        { apply (Qeq_trans _ ((Qinv Dv - Qinv Ev) * (Dv * Ev) * Qinv (Dv * Ev))).
          - assert (Hassoc : (Qinv Dv - Qinv Ev) * (Dv * Ev) * Qinv (Dv * Ev)
                             == (Qinv Dv - Qinv Ev) * ((Dv * Ev) * Qinv (Dv * Ev))) by ring.
            rewrite Hassoc, HmDE. ring.
          - exact (Qeq_sym _ _ Hside). }
        assert (Hreg2 : wn - Qinv Ev * hnp == hnp * (Qinv Dv - Qinv Ev)).
        { rewrite Hcid. rewrite Hwv. ring. }
        assert (Hq : Qle (Qinv (Dv * Ev)) (4#3)).
        { assert (Ht1 : Qle (1 * Qinv (Dv * Ev)) (Qinv (3#4))).
          { apply (b5n_xinv_le 1 (Dv * Ev) (3#4)).
            - exact HpDE.
            - unfold Qlt. simpl. lia.
            - nra. }
          apply (Qle_trans (Qinv (Dv * Ev)) (1 * Qinv (Dv * Ev)) (4#3)).
          - apply qeq_imp_qle. ring.
          - apply (Qle_trans (1 * Qinv (Dv * Ev)) (Qinv (3#4)) (4#3)).
            + exact Ht1.
            + apply qeq_imp_qle. reflexivity. }
        assert (Hxa : Qle (Qabs xnp) 1) by (apply QleT'_to_Qle; apply Hx).
        assert (Hxa0 : Qle 0 (Qabs xnp)) by apply Qabs_nonneg.
        assert (Hq0 : Qle 0 (Qinv (Dv * Ev)))
          by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HpDE).
        assert (Hedv : Ev - Dv == -(xnp * hnp)).
        { unfold Dv, Ev. ring. }
        apply (Qle_trans _ (Qmult hn (Qabs (Qinv Dv - Qinv Ev))) _).
        - rewrite Hreg2. rewrite Qabs_Qmult.
          replace (Qabs hnp) with hn by reflexivity.
          apply Qle_refl.
        - rewrite Hsplit. rewrite Qabs_Qmult. rewrite Hedv. rewrite Qabs_opp.
          rewrite Qabs_Qmult.
          assert (Habsinv : Qabs (Qinv (Dv * Ev)) == Qinv (Dv * Ev))
            by (apply Qabs_pos; apply Qlt_le_weak;
                apply Qinv_lt_0_compat; exact HpDE).
          rewrite Habsinv.
          replace (Qabs hnp) with hn by reflexivity.
          apply (Qle_trans _ (Qmult (Qmult (4#3) hn) hn)).
          + rewrite (Qmult_comm hn (Qmult (Qmult (Qabs xnp) hn) (Qinv (Dv * Ev)))).
            apply Qmult_le_compat_r.
            * apply (Qle_trans _ (Qmult hn (Qinv (Dv * Ev)))).
              -- apply (Qmult_le_compat_r (Qmult (Qabs xnp) hn) hn (Qinv (Dv * Ev))).
                 ++ apply (Qle_trans _ (Qmult 1 hn)).
                    ** apply Qmult_le_compat_r.
                       --- nra.
                       --- exact Hhn0.
                    ** apply qeq_imp_qle. ring.
                 ++ exact Hq0.
              -- rewrite (Qmult_comm hn (Qinv (Dv * Ev))).
                 apply (Qmult_le_compat_r (Qinv (Dv * Ev)) (4#3) hn).
                 ++ nra.
                 ++ exact Hhn0.
            * exact Hhn0.
          + nra. }
      assert (Hw43c : Qle (Qabs wn) (Qmult (4#3) hn)).
      { assert (Hab : Qabs wn == Qabs wnr) by (apply (Qabs_wd _ _); exact Hcid).
        rewrite Hab. exact Hw43q. }
      (* —— T 界（9a-甲 slack 投影）：|atanw − wn| ≤ (1/8 en)|wn| + (1/2 en') —— *)
      assert (HT : Qle (Qabs (projT1 (real_plus (cauchy_real_arctan (abl9b_wc x h Hd) Hwc)
                              (real_opp (abl9b_wc x h Hd))) n))
                       (Qplus (Qmult (Qmult (1#8) en) (Qabs wn)) (Qmult (1#2) en'))).
      { apply (Qle_trans _ (Qplus (projT1 (real_plus (real_mult (real_mult (real_const (1#8)) eps)
              (real_abs (abl9b_wc x h Hd))) (real_mult (real_const (1#4)) eps')) n)
              (projT1 (real_mult (real_const (1#4)) eps') n)) _).
        - exact (HN1 n (NatLe_lift _ _ Hn1)).
        - assert (HeqB : Qplus (projT1 (real_plus (real_mult (real_mult (real_const (1#8)) eps)
              (real_abs (abl9b_wc x h Hd))) (real_mult (real_const (1#4)) eps')) n)
              (projT1 (real_mult (real_const (1#4)) eps') n)
              == Qplus (Qmult (Qmult (1#8) en) (Qabs wn)) (Qmult (1#2) en')).
          { setoid_rewrite (real_plus_proj (real_mult (real_mult (real_const (1#8)) eps)
              (real_abs (abl9b_wc x h Hd))) (real_mult (real_const (1#4)) eps') n).
            setoid_rewrite (real_mult_proj (real_mult (real_const (1#8)) eps)
              (real_abs (abl9b_wc x h Hd)) n).
            setoid_rewrite (real_mult_proj (real_const (1#8)) eps n).
            setoid_rewrite (real_const_proj (1#8) n).
            setoid_rewrite (real_abs_proj (abl9b_wc x h Hd) n).
            setoid_rewrite (real_mult_proj (real_const (1#4)) eps' n).
            setoid_rewrite (real_const_proj (1#4) n).
            fold wn. fold en. fold en'.
            ring. }
          rewrite HeqB. apply Qle_refl. }
      assert (HTval : projT1 (real_plus (cauchy_real_arctan (abl9b_wc x h Hd) Hwc)
                              (real_opp (abl9b_wc x h Hd))) n == atanw - wn).
      { setoid_rewrite (real_plus_proj (cauchy_real_arctan (abl9b_wc x h Hd) Hwc)
                          (real_opp (abl9b_wc x h Hd)) n).
        rewrite (arctan_real_proj (abl9b_wc x h Hd) Hwc n).
        setoid_rewrite (real_opp_proj (abl9b_wc x h Hd) n).
        reflexivity. }
      assert (HT2 : Qle (Qabs (atanw - wn))
                        (Qplus (Qmult (Qmult (1#8) en) (Qabs wn)) (Qmult (1#2) en'))).
      { rewrite <- HTval. exact HT. }
      (* —— Δ 与 A 的点位值链 —— *)
      assert (HApval : projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                (real_opp (cauchy_real_arctan x Hx))) n == atanxh - atanx).
      { setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                          (real_opp (cauchy_real_arctan x Hx)) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
        rewrite (arctan_real_proj x Hx n). reflexivity. }
      assert (HAp : projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                (real_opp (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                   (b5a_one_plus_sq_pos x)) h)))) n
                == atanxh - (atanx + Qinv Ev * hnp)).
      { setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                          (real_opp (real_plus (cauchy_real_arctan x Hx)
                             (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                     (b5a_one_plus_sq_pos x)) h))) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        setoid_rewrite (real_opp_proj (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                   (b5a_one_plus_sq_pos x)) h)) n).
        setoid_rewrite (real_plus_proj (cauchy_real_arctan x Hx)
                          (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                  (b5a_one_plus_sq_pos x)) h) n).
        rewrite (arctan_real_proj x Hx n).
        rewrite (real_mult_proj (real_inv_pos (real_plus real_one (real_mult x x))
                                  (b5a_one_plus_sq_pos x)) h n).
        rewrite (HNinv2 n Hninv2). rewrite HEproj. reflexivity. }
      assert (Hdfpt : Qlt (Qabs (atanxh - atanx - atanw)) (Qmult (1#16) e1)).
      { assert (HeqA : Qabs (projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                            (real_opp (cauchy_real_arctan x Hx))) n
                          - projT1 (cauchy_real_arctan (abl9b_wc x h Hd)
                              (abl9b_w_clamp_dom (abl9b_w x h Hd))) n)
                       == Qabs (atanxh - atanx - atanw)).
        { apply (Qabs_wd _ _). rewrite HApval. rewrite Hapw. ring. }
        apply QltT_to_Qlt.
        exact (qltT_eq_compat_l _ _ _ HeqA (HN2 n (NatLe_lift _ _ Hn2))). }
      (* —— 主界：|A_n| ≤ (2/3)en·hn + (5/8)en' + (1/16)e1 —— *)
      assert (Hfin : Qle (Qabs (atanxh - (atanx + Qinv Ev * hnp)))
                (Qplus (Qmult (2#3) (Qmult en hn))
                       (Qplus (Qmult (5#8) en') (Qmult (1#16) e1)))).
      { assert (Hreg3 : atanxh - (atanx + Qinv Ev * hnp)
                  == (atanxh - atanx - atanw)
                     + ((atanw - wn) + (wn - Qinv Ev * hnp)))
        by ring.
        rewrite Hreg3.
        apply (Qle_trans _ (Qplus (Qabs (atanxh - atanx - atanw))
                (Qabs ((atanw - wn) + (wn - Qinv Ev * hnp)))) _).
        - apply Qabs_triangle.
        - apply (Qle_trans _ (Qplus (Qabs (atanxh - atanx - atanw))
                (Qplus (Qabs (atanw - wn)) (Qabs (wn - Qinv Ev * hnp)))) _).
          + apply Qplus_le_compat. apply Qle_refl. apply Qabs_triangle.
          + (* X52 修复（条款 G，原稿编译红实录 /tmp/x52work/skel.log）：原中项
               (1/16)e1+((1/8)en|wn|+(1/2)en') 缺 |Δ3|=(1/2)en·hn 预算
               （|Δ2|+|Δ3|≤(1/8)en|wn|+(1/2)en' 不成立），且 |Δ2|/|Δ3| 两翼
               Qplus_le_compat 隐式分裂歧义（RHS b+d 拆错位致 HT2/HR2 对不上）。
               修复=中项补 (1/2)en·hn 翼+两翼显式定位；终段 nra 依赖 He1pos
               （en'≥0，上方新增 assert）。详证=登记册编译绿验节。*)
            apply (Qle_trans _ (Qplus (Qmult (1#16) e1)
                    (Qplus (Qplus (Qmult (Qmult (1#8) en) (Qabs wn)) (Qmult (1#2) en'))
                           (Qmult (Qmult (1#2) en) hn)))).
            * apply Qplus_le_compat.
              -- apply Qlt_le_weak. exact Hdfpt.
              -- apply (Qplus_le_compat (Qabs (atanw - wn))
                          (Qplus (Qmult (Qmult (1#8) en) (Qabs wn)) (Qmult (1#2) en'))
                          (Qabs (wn - Qinv Ev * hnp)) (Qmult (Qmult (1#2) en) hn)).
                 ++ exact HT2.
                 ++ exact HR2.
            * apply (Qle_trans _ (Qplus (Qmult (1#16) e1)
                    (Qplus (Qplus (Qmult (Qmult (1#8) en) (Qmult (4#3) hn))
                                  (Qmult (1#2) en'))
                           (Qmult (Qmult (1#2) en) hn)))).
              -- apply Qplus_le_compat.
                 ++ apply Qle_refl.
                 ++ apply Qplus_le_compat.
                    ** apply (Qplus_le_compat (Qmult (Qmult (1#8) en) (Qabs wn))
                                  (Qmult (Qmult (1#8) en) (Qmult (4#3) hn))
                                  (Qmult (1#2) en') (Qmult (1#2) en')).
                       --- apply (Qmult_le_compat_nonneg (Qmult (1#8) en)
                                     (Qmult (1#8) en) (Qabs wn) (Qmult (4#3) hn)).
                       +++ split.
                           { nra. }
                           { apply Qle_refl. }
                       +++ split.
                           { apply Qabs_nonneg. }
                           { exact Hw43c. }
                       --- apply Qle_refl.
                    ** apply Qle_refl.
              -- nra. }
      (* —— 终算术：eta=(1/16)e1 < en·hn + en' − |A_n| —— *)
      apply Qlt_to_QltT.
      setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
      setoid_rewrite (real_mult_proj eps (real_abs h) n).
      setoid_rewrite (real_abs_proj h n).
      setoid_rewrite (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                (real_opp (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                   (b5a_one_plus_sq_pos x)) h)))) n).
      rewrite HAp.
      (* X52 修复（条款 G）：setoid_rewrite 产出逐点投影展开形（projT1 eps n /
         projT1 eps' n / Qabs (projT1 h n)）与 set 变量 en/en'/hn 原子错配，
         终段 nra 找不到见证——三发 reflexivity 等式回折后一发 nra。 *)
      assert (HfE : projT1 eps n == en) by reflexivity.
      assert (HfE' : projT1 eps' n == en') by reflexivity.
      assert (HfH : Qabs (projT1 h n) == hn) by reflexivity.
      rewrite HfE, HfE', HfH.
      (* X52 修复之二：原稿终段 nra 缺严格性供给——(1/16)e1 < (3/8)en' 需
         0 < e1 ≤ en' 严格链，原稿仅备弱形 Hen'（e1≤en'），nra 判无见证正确。
         补 0<e1（He1T）与 e1<en'（He1lt 逐点严格形）两发。 *)
      assert (HltE1 : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1T).
      assert (HltEn : Qlt e1 en') by exact (He1lt n Hne1).
      nra.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                        *)
(*   对账：Qed 计 4（Q 基建 4 件+①②+clamp 域另 6 件辅助）——        *)
(*   主件=abl9b（骨架）+① abl9b_dom_pos+② abl9b_w_bounds。         *)
(* ============================================================ *)
Print Assumptions abl9b.
Print Assumptions abl9b_dom_pos.
Print Assumptions abl9b_w_bounds.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
(* X52 勘定与处置（条款 G 响亮）：原稿 Recursive Extraction abl9b 与 ②
   abl9b_w_bounds 触提取器硬限「informative inductive type prod has a Prop
   instance」（skel9/skel10.log 实录；X27 勘名 prod-Prop 单例墙同源）——
   病灶=② 语句 And 两翼取 Prop 形 Qle 在 sigT 下被物化。处置=② 语句形升
   QleT'（S02 Set 形）+三处使用位解包；主件检验恢复（墙预期同源解除，
   实证见登记册编译绿验节）。*)
Recursive Extraction abl9b_dom_pos.
Recursive Extraction abl9b_w_bounds.
Recursive Extraction abl9b.

