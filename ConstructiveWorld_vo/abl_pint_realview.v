(* ============================================================ *)
(* abl_pint_realview.v —— Q 积分值的 Real 读数桥（升脸读数四件，零前置）          *)
(*                                                                          *)
(* 【件名】abl_pint_realview.v（甲形态·新独立件·零级联：不改宿主、零 Require     *)
(*   面变化、零注册面级联；照 AS 件 abl_diffreal_family 同款先例）。             *)
(*  使命: AI 桥接件单 ②-A（AI 脸归一桥 §③件②-A）：    *)
(*   积分层 Q 脸独大（PolyIntegral pint_ 族、PintMono pm_ 单调机在役）而         *)
(*   Real 五脸全零——本件把 Q 层积分值读进 Real 宇宙（读数桥：非移植、            *)
(*   非积分机，真 Real 积分归件②-B，PolyIntegral:44 二期留记不越期约）。          *)
(*   四件：①pir_integral_real——Q 积分值的 Real 嵌入读数（定义件）；              *)
(*   ②pir_const_qeqT——QeqT→real_eq 常值升脸共用小件（AI 注明 ①-A/③-B 复用位）；  *)
(*   ③pir_integral_mono_real——单调性的 Real 面对接（前提照 AI 勘 4 勘正：        *)
(*   逐系数序 forall i, QleT' (pint_coeff p i) (pint_coeff q i)，非点态           *)
(*   函数序；免等长版 PintMono:281）；④pir_integral_one_real——∫1==1 的           *)
(*   Real 读法＋pir_integral_pos_real——非负性读数严格正形（PintMono:329          *)
(*   同法升脸）。                                                                *)
(*  依赖: 全在册零外前置：S01_BaseRing；S02_CauchyComplete（Real:=sigT:397／    *)
(*   real_eq:399／real_lt:468／real_le Or 形:472／QltT:48／QleT':99／             *)
(*   QleT'_to_Qle:103／QeqT:303／qeqT_imp_qeq:325／qeq_imp_qeqT:309／             *)
(*   QltT_to_Qlt:51／real_const_proj:1323／q_abs_self_zero:2006／                 *)
(*   real_eq_trans:2257／real_eq_of_zero_diff:2317）；PolyIntegral（               *)
(*   pint_integral:82／pint_pow_poly:85／pint_integral_one:209）；                *)
(*   PintMono（pm_pointwise_le_integral:281／pm_integral_pos_strict:329）；        *)
(*   S07_RealSetoidExpLog（real_const_pos:3772／real_const_lt:4577）；             *)
(*   Stdlib QArith（Qeq_trans／Qabs_wd／Qcompare_comp／Qeq_refl／Qlt_alt）。       *)
(*   透传 Require 不导出短名（AQ 坑卡①）：本件自 Require Import 全链。            *)
(*  构造性: 零承认语句、零经典逻辑、零未证前提位；语句面纯 Set                *)
(*   （real_eq/real_lt/real_le/QeqT/QleT'/QltT 全 Set 值，S02 实拍）；             *)
(*   real_le 为 Or 形 Set 谓词（AI 陈述草案 B 形照办）：Or 出口左肢 real_lt        *)
(*   走 real_const_lt 严格形、右肢 real_eq 走 pir_const_qeqT（AL 坑卡之            *)
(*   real_le_b 不触——本件语句面即 AI 指定的 real_le Or 形）。全部 Real 值由        *)
(*   real_const 常值柯西序列承载，读数四件纯为「Q 值→Real 读数」换算，零新        *)
(*   分析引擎。签名族前缀 pir_ 全库 grep 0 命中（实拍防撞）；             *)
(*   AI 存疑表②（Z→Q 系数换算轨）本件不触（无任何系数换算需求，与 AS 件           *)
(*   同判整体绕开）；real_one 与 real_const 1 非定义性相等（existT 证明位          *)
(*   异构），∫1 读法走 real_eq_trans 两肢而非 reflexivity，不虚报换算强度。        *)
(*  编译配方: ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler      *)
(*   no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930      *)
(*   "" abl_pint_realview.v                                                        *)
(* 【绿判】EXIT=0｜无 ^Error|Error:｜魔数 436f712100015ff4｜.vo 新于 .v｜          *)
(*   尾 Print Assumptions 四件全 Closed；rocqchk 复核附加强证。                    *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.
Require Import PintMono.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(* 件 1（定义件）：Q 积分值的 Real 嵌入读数                                        *)
(*   AI 陈述草案 pint_integral_real 逐型（名字按约定改 pir_ 前缀，语义零差）：     *)
(*   常值柯西序列 real_const 承载 Q 积分值，Real := sigT 柯西实数（S02:397）。     *)
(* ============================================================ *)
Definition pir_integral_real (p : list Q) : Real :=
  real_const (pint_integral p).

(* ============================================================ *)
(* 件 2（共用小件）：QeqT 常值升 real_eq                                           *)
(*   全部 Q 层会计（自差零 + Qcompare_comp 换形，real_const 定义体同款配方          *)
(*   S02:874-879）先行在 assert 内备妥（无逐点项）；N=0 肢再以 change 定义性        *)
(*   转换把 projT1 (real_const c) n 折到 c（real_const_proj 即 reflexivity          *)
(*   证，S02:1326）——QltT 为 Id bool 面、无 Proper 换形注册位，rewrite/setoid_     *)
(*   rewrite 于 QltT 目标内禁用（首例实录，见施工报告坑卡）。                   *)
(* ============================================================ *)
Lemma pir_const_qeqT : forall c d : Q,
  QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd eps Heps.
  assert (Hcd0 : c == d) by (apply qeqT_imp_qeq; exact Hcd).
  assert (Hab : Qabs (c - d) == 0).
  { apply (Qeq_trans (Qabs (c - d)) (Qabs (d - d)) 0).
    - apply Qabs_wd. rewrite Hcd0. reflexivity.
    - apply q_abs_self_zero. }
  assert (Hcmp : Qcompare (Qabs (c - d)) eps = Lt).
  { rewrite (Qcompare_comp (Qabs (c - d)) 0 Hab eps eps (Qeq_refl eps)).
    apply Qlt_alt. exact (QltT_to_Qlt 0 eps Heps). }
  exists 0%nat. intros n Hn.
  change (QltT (Qabs (c - d)) eps).
  unfold QltT, Qlt_bool. rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(* 件 3 支撑：QleT' 常值升 real_le（AI 配方原文：Or 组装——                          *)
(*   real_lt ∨ real_eq 两肢各落在役件）。AI 草案「QleT'→Qlt∨Qeq」的 Qle            *)
(*   划分在本环境不可走：Qle = Z.le 单命题（S02:100 注记实拍），Prop 划分           *)
(*   禁入 Set；改走 Qcompare 三分判定（comparison : Set 可拆，零经典）：            *)
(*   Eq→real_eq 肢、Lt→real_lt 肢、Gt→与 QleT' 的 bool 反映矛盾灭。                 *)
(* ============================================================ *)
Lemma pir_const_le : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  unfold QleT' in Hcd.
  destruct (Qcompare c d) eqn:E.
  - (* Eq：c == d → real_eq 肢 *)
    right. apply pir_const_qeqT. apply qeq_imp_qeqT.
    apply Qeq_alt. exact E.
  - (* Lt：c < d → real_lt 肢 *)
    left. apply real_const_lt. apply Qlt_alt. exact E.
  - (* Gt：与 QleT' 的 bool 反映（Gt→false≠true）矛盾灭 *)
    exfalso.
    unfold Qle_bool in Hcd. rewrite E in Hcd. inversion Hcd.
Qed.

(* ============================================================ *)
(* 件 3 主件：单调性的 Real 面对接                                                  *)
(*   前提＝逐系数序（AI 勘 4 照办：PintMono:281 前提 forall i, QleT'               *)
(*   (pint_coeff p i) (pint_coeff q i)，免等长版——非「点态函数序」，               *)
(*   本件语句面不虚报强度）。PintMono 单调机只使用不重编（一期刊物纪律）。          *)
(* ============================================================ *)
Theorem pir_integral_mono_real : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  real_le (pir_integral_real p) (pir_integral_real q).
Proof.
  intros p q Hcoeff.
  unfold pir_integral_real.
  apply pir_const_le.
  exact (pm_pointwise_le_integral p q Hcoeff).
Qed.

(* ============================================================ *)
(* 件 4-a：∫1 == 1 的 Real 读法（pint_integral_one:PolyIntegral:209 升脸）。        *)
(*   real_one（S02:2301，序列 fun _ => 1）与 real_const (1#1)（S02:859）的          *)
(*   existT 证明位异构、非定义性相等，故走 real_eq_trans（三显式实参，AS            *)
(*   坑卡）两肢：常值换 == 肢（件 2）＋逐点零差肢（real_eq_of_zero_diff:            *)
(*   S02:2317；projT1 real_one 投影先例 S07:2690 同款 cbn 闭合）。                  *)
(* ============================================================ *)
Theorem pir_integral_one_real :
  real_eq (pir_integral_real (pint_pow_poly 0)) real_one.
Proof.
  unfold pir_integral_real.
  apply (real_eq_trans
           (real_const (pint_integral (pint_pow_poly 0)))
           (real_const (1 # 1))
           real_one).
  - apply pir_const_qeqT. exact pint_integral_one.
  - apply real_eq_of_zero_diff. intros n.
    rewrite (real_const_proj (1 # 1) n).
    assert (Ho1 : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    rewrite Ho1. ring.
Qed.

(* ============================================================ *)
(* 件 4-b：非负性读数（严格正形）：全系数 QltT 0 ⟹ 0 < Real 读数                    *)
(*   （pm_integral_pos_strict:PintMono:329 ＋ real_const_pos:S07:3772，             *)
(*   AI 件②-A 陈述草案同名位同法升脸；语句面 real_lt 见证形 sigT，Set）。           *)
(* ============================================================ *)
Theorem pir_integral_pos_real : forall p : list Q,
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  real_lt real_zero (pir_integral_real p).
Proof.
  intros p H.
  unfold pir_integral_real.
  exact (real_const_pos (pint_integral p) (pm_integral_pos_strict p H)).
Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（编译期 stdout，verify 复核）                    *)
(* ============================================================ *)

Print Assumptions pir_const_qeqT.
Print Assumptions pir_integral_mono_real.
Print Assumptions pir_integral_one_real.
Print Assumptions pir_integral_pos_real.
