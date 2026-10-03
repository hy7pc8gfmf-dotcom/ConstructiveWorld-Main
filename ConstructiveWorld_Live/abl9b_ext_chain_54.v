(* ==========================================================================)
   abl9b_ext_chain_54.v — 延拓层装配件（A2+B3 合流·内点链 m→∞ 延拓层）
   ── 模块名与数学使命：─────────────────────────────────────────────────────
   本件构建缩放内点链 m→∞ 延拓层数学件，共四块：
   ① Qinv 于 [3/4,∞) 的 Lipschitz 辅助引理：Q 层核（|inva−invb| ≤ (16/9)|a−b|，
     域证书 QleT' (3/4) 形）+ real 层运输形（尾 3/4 下界 + 正间隙 sg 的
     real_lt 支形）；
   ② clamp（Qmin(Qmax(·,−1),1)，即件30 abl9b_wc 逐点语义）的 1-Lipschitz
     逐点辅助引理（构造性分情形）；
   ③ 缩放代数率辅助引理：(1−1/m)²·(x+h)·x 与 (x+h)·x 之差的显式 1/m 率
     （率恒等 (k²−1)=(k−1)(k+1)，k:=1−1/m，|k−1|=1/m，|k+1|≤2）；
   ④ 三项 eps 链骨架：以缩放对内点链给出的 LHS_m→LHS 与 RHS_m→RHS 收敛
     证书为通用前件，组装 |LHS−RHS| ≤ |LHS−LHS_m|+|LHS_m−RHS_m|+|RHS_m−RHS|
     的 real_eq 闭合；并以 b5b_ap_uniform（S11 一致连续核）实例化 LHS 侧
     收敛证书，走通实例化路径（前层产出后 Hinner/HconvR 两参数位代入）。
   ⑤ Hconv 参数位供给构造（B3合流接口位，件59 abl9b_rhs_sc_close
     留接口的甲侧供给）：缩放对 w_m := h_m·inv(D_m)，D_m := 1+k_m²(x+h)x，
     k_m := abl9b_ext_km(S m)（与件53 abl9b_ksc 同值）；点域事实
     |h_n|<1/4 尾界 ⟹ (x+h)x ≥ −1/4 ⟹ D 与 D_m 逐点 ≥ 3/4，块① 直用；
     |D_m−D| = (1−k_m²)·|(x+h)x| ≤ 2/(m+1)；合计 O(1/m) 显式系数 11/9；
     (M,Nv) 双见证闭合证书=件59 Hconv 参数位逐字形（系数证书+收敛证书两件）。
   ⑥ LHS real_eq↔(M1,M2) 尾语义互译包装（件59 交付报告 §七·2 点名合流
     件）：real_eq/cv 形与 (M1,Nv) 逐点尾形双向互译三件，供三项 eps 链与
     件59 (M1,M2) 闭合形无缝拼装。
   ── 依赖清单：────────────────────────────────────────────────────────────
   S01–S11（基础模块）+ abl9b_skeleton_30（abl9b_wc/abl9b_w/abl9b_w_clamp_dom/
   abl9b_dom_pos/abl9b_h_abs_tail）+ abl_arctan_diff_20 + Stdlib（QArith/Qabs/Qround/Qminmax/
   Setoid/Morphisms/Lia/Lqa/Extraction）。real_inv_proj 取自 S09（现势正本，
   旧代际行号已失效，本件以实读重定位为准）。
   ── 对标行（现势实读重定位）：──────────────────────────────────────────
   b5b_ap_uniform：S11_TP3B5.v L7044（与合流裁决行号一致）；
   clamp 构造：abl9b_skeleton_30.v L288-325；w 尾界 abl9b_w_bounds：L221（尾形
   sigT）；域界 abl9b_dom_pos：L183；q_arch_inv：S02 L1684；b5n_xinv_le：
   S11 L11884；b5i_abs_le_pointwise：S11 L9473；b5b_delta_pos：S11 L7122；
   real_le：S02 L472（Or(real_lt,real_eq) 编码，结论支取 real_lt 需显式正
   间隙见证，本件 real 层运输形按此取 sg>0 间隙参）；real_inv_proj：S09 L1446；
   arctan_real_proj：S11 L909；atan_third_sum：S11 L816；q_arch_inv_pos：S02
   L1741；real_plus/mult/opp/const_proj：S02 L1305-1323；QltT/QleT'：S02
   L48/L99；qltT_div_pos：S02 L350；qltT_eq_compat_r：S02 L373（实读
   重锚）。块⑤新增锚（实读）：real_inv_pos 定义体 S03
   L6681（if Nat.leb N0 n 分支形，透明可展开）；real_inv_proj S09（见证=
   域证书自身尾见证）；leb_correct 置真用法（S03 L6701/S09 L1456 同款）；
   Qle_lt_or_eq/Qinv_lt_contravar/Qmult_inv_r（Stdlib QArith）；
   b3r_one_proj：S11 L4395；件53 缩放对之接口（abl9b_ksc/xsc/hsc/sca_Hd，
   件53 正本只读参照；ksc m = m/(m+1) 与本件 abl9b_ext_km(S m) 同值）。
   ── 构造性注记：──────────────────────────────────────────────────────────
   本件为零承认件：全链逐件证体真构造、逐件闭合，零承认命令字面（含占位
   与中断类命令），零经典逻辑，零经典实数公理，零承认链短路策略（Q 序链
   以显式引理逐链组合：传递/三角/乘法合同/反号单调；代数闭合用 nra——
   Micromega 反射证明项，构造性，承认面由 Print Assumptions 核验为
   Closed）。语句面全 Set 形
   （QleT'/QltT/real_lt/real_le/sigT/And=A*B），零 Prop 泄露，假设位同检；
   Qle/Qlt 仅出现于证明内部。Q 序链走显式引理组合，代数闭合用 nra
   （Micromega 反射证明项，构造性，承认面由 Print Assumptions 核验为
   Closed）。clamp 分情形走 Q.max_case_strong/Q.min_case_strong 的构造性
   case 原理（P : Q -> Type 全类形，含合同支）。块⑤的 D_m 域证书
   abl9b_ext_sca_Hd 以定义透明（Defined）闭合，使 real_inv_pos 定义体的
   if 分支对见证 N4 定义性归约（(M,Nv) 闭合证书见证均匀性的构造基础）；
   提取检验沿件59 前例取安全形（witness 形豁免提取命令，登记于终验节）。
   ── 编译配方：────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && unset COQLIB ROCQLIB
   cd abl_a2b3_WASH3_pool && ulimit -s 65532
   nice -19 rocq c -native-compiler no -Q "$PWD" "" abl9b_ext_chain_54.v
   （编译道闸：起编前 ps 计 rocq ≤1，起编后全局 ≤2，禁两件并发。）
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
Require Import abl9b_skeleton_30.
Require Import abl_arctan_diff_20.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* Q 层基建：绝对值号定号辅助引理（分情形材料）                    *)
(*   |q| == q（0≤q）；|q| == −q（q≤0）；二者择一的 Set 形析取。    *)
(* ============================================================ *)

Lemma abl9b_ext_abs_eq : forall q : Q, QleT' 0 q -> Qabs q == q.
Proof.
  intros q H. apply Qabs_pos. apply QleT'_to_Qle. exact H.
Qed.

Lemma abl9b_ext_abs_pm : forall q : Q,
  Or (And (QleT' 0 q) (Qabs q == q)) (And (QleT' q 0) (Qabs q == (- q))).
Proof.
  intros q.
  destruct (Qle_bool q 0) eqn:Hd.
  - right. split.
    + apply Qle_to_QleT'.
      apply (proj1 (Qle_bool_iff q 0)). exact Hd.
    + apply (Qeq_trans (Qabs q) (Qabs (- q))).
      * apply (Qeq_sym _ _). apply Qabs_opp.
      * apply abl9b_ext_abs_eq.
        apply Qle_to_QleT'.
        assert (Hq : Qle q 0) by (apply (proj1 (Qle_bool_iff q 0)); exact Hd).
        nra.
  - left. split.
    + apply Qle_to_QleT'.
      assert (Hn : ~ Qle q 0).
      { intro Hc.
        assert (Ht : Qle_bool q 0 = true) by (apply (proj2 (Qle_bool_iff q 0)); exact Hc).
        rewrite Ht in Hd. discriminate Hd. }
      nra.
    + apply abl9b_ext_abs_eq.
      apply Qle_to_QleT'.
      assert (Hn : ~ Qle q 0).
      { intro Hc.
        assert (Ht : Qle_bool q 0 = true) by (apply (proj2 (Qle_bool_iff q 0)); exact Hc).
        rewrite Ht in Hd. discriminate Hd. }
      nra.
Qed.

(* ============================================================ *)
(* 块① Qinv Lipschitz（[3/4,∞) 闭半域）                          *)
(*   Q 层核：3/4≤a,b ⟹ |inva−invb| ≤ (16/9)|a−b|。                *)
(*   链：inva−invb == (b−a)·inv(a·b)（显式代数恒等），再           *)
(*   |inv(a·b)| == inv(a·b) ≤ inv(9/16) == 16/9（跨乘 b5n_xinv_le）。 *)
(* ============================================================ *)

Lemma abl9b_ext_qinv_lip : forall a b : Q,
  QleT' (3#4) a -> QleT' (3#4) b ->
  QleT' (Qabs (Qinv a - Qinv b)) ((16#9) * Qabs (a - b)).
Proof.
  intros a b Ha Hb.
  assert (Haq : Qle (3#4) a) by (apply QleT'_to_Qle; exact Ha).
  assert (Hbq : Qle (3#4) b) by (apply QleT'_to_Qle; exact Hb).
  assert (Hlt4 : Qlt 0 (3#4)) by (unfold Qlt; simpl; lia).
  assert (Hap : Qlt 0 a) by (apply (Qlt_le_trans 0 (3#4) a); [exact Hlt4 | exact Haq]).
  assert (Hbp : Qlt 0 b) by (apply (Qlt_le_trans 0 (3#4) b); [exact Hlt4 | exact Hbq]).
  assert (Habp : Qlt 0 (a * b)) by (apply (Qmult_lt_0_compat a b); assumption).
  assert (Hza : ~ (a == 0)).
  { intro Hz. assert (Hle0 : Qle a 0) by (apply qeq_imp_qle; exact Hz).
    assert (Hbad : Qle (3#4) 0) by (apply (Qle_trans (3#4) a 0); [exact Haq | exact Hle0]).
    exact (Qlt_not_eq 0 0 (Qlt_le_trans 0 (3#4) 0 Hlt4 Hbad) (Qeq_refl 0)). }
  assert (Hzb : ~ (b == 0)).
  { intro Hz. assert (Hle0 : Qle b 0) by (apply qeq_imp_qle; exact Hz).
    assert (Hbad : Qle (3#4) 0) by (apply (Qle_trans (3#4) b 0); [exact Hbq | exact Hle0]).
    exact (Qlt_not_eq 0 0 (Qlt_le_trans 0 (3#4) 0 Hlt4 Hbad) (Qeq_refl 0)). }
  assert (Hzab : ~ (a * b == 0)).
  { intro Hz. rewrite Hz in Habp.
    exact (Qlt_not_eq 0 0 Habp (Qeq_refl 0)). }
  assert (Hia : Qinv a * a == 1) by (rewrite Qmult_comm; apply Qmult_inv_r; exact Hza).
  assert (Hib : Qinv b * b == 1) by (rewrite Qmult_comm; apply Qmult_inv_r; exact Hzb).
  assert (HmDE : a * b * Qinv (a * b) == 1) by (apply Qmult_inv_r; exact Hzab).
  (* 显式代数：(inva−invb)(a·b) == b−a，两端乘 inv(a·b) 得差恒等 *)
  assert (Hs2 : (Qinv a - Qinv b) * (a * b) == b - a).
  { assert (Hfac : (Qinv a - Qinv b) * (a * b)
                   == (Qinv a * a) * b - (Qinv b * b) * a) by ring.
    rewrite Hfac, Hia, Hib. ring. }
  assert (Hsplit : Qinv a - Qinv b == (b - a) * Qinv (a * b)).
  { apply (Qeq_trans _ ((Qinv a - Qinv b) * (a * b) * Qinv (a * b))).
    - assert (Hassoc : (Qinv a - Qinv b) * (a * b) * Qinv (a * b)
                       == (Qinv a - Qinv b) * ((a * b) * Qinv (a * b))) by ring.
      rewrite Hassoc, HmDE. ring.
    - apply (Qeq_sym _ _). rewrite Hs2. reflexivity. }
  apply Qle_to_QleT'.
  assert (Hstep1 : Qabs (Qinv a - Qinv b) == Qabs ((b - a) * Qinv (a * b))).
  { apply Qabs_wd. exact Hsplit. }
  rewrite Hstep1.
  apply (Qle_trans _ (Qmult (Qabs (b - a)) (Qabs (Qinv (a * b)))) _).
  - apply qeq_imp_qle. apply Qabs_Qmult.
  - apply (Qle_trans _ (Qmult (Qabs (b - a)) (Qinv (a * b))) _).
    + rewrite (Qabs_pos (Qinv (a * b))
                (Qlt_le_weak 0 (Qinv (a * b)) (Qinv_lt_0_compat (a * b) Habp))).
      apply Qle_refl.
    + assert (Habsw : Qabs (b - a) == Qabs (a - b)).
      { assert (He : b - a == - (a - b)) by ring.
        rewrite He. apply Qabs_opp. }
      rewrite Habsw.
      assert (Hinv : Qle (Qinv (a * b)) (16#9)).
      { assert (Ht1 : Qle (1 * Qinv (a * b)) (Qinv (9#16)))
          by (apply (b5n_xinv_le 1 (a * b) (9#16));
              [exact Habp | unfold Qlt; simpl; lia | nra]).
        apply (Qle_trans _ (1 * Qinv (a * b)) _).
        - apply qeq_imp_qle. ring.
        - apply (Qle_trans _ (Qinv (9#16)) _).
          + exact Ht1.
          + apply qeq_imp_qle. reflexivity. }
      assert (Hsw : (16#9) * Qabs (a - b) == Qabs (a - b) * (16#9)) by ring.
      rewrite Hsw.
      rewrite (Qmult_comm (Qabs (a - b)) (Qinv (a * b))).
      rewrite (Qmult_comm (Qabs (a - b)) (16#9)).
      apply (Qmult_le_compat_r (Qinv (a * b)) (16#9) (Qabs (a - b))).
      * exact Hinv.
      * apply Qabs_nonneg.
Qed.

(* ============================================================ *)
(* 块① real 层运输                                               *)
(*   尾 3/4 下界 ⟹ 正性证书（ witnesses (1/2, ND) ）；            *)
(*   运输形：|inv D − inv E| ≤ (16/9)|D−E| + sg（sg>0 正间隙参，  *)
(*   real_le 的 Or 编码下取 real_lt 支，间隙见证 (1/2)·sg）。     *)
(* ============================================================ *)

Lemma abl9b_ext_dom34_pos : forall D : Real,
  sigT (fun N : nat => forall n : nat, NatLe N n -> QleT' (3#4) (projT1 D n)) ->
  real_lt real_zero D.
Proof.
  intros D HD. destruct HD as [ND HD].
  unfold real_lt. exists (1#2). split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists ND. intros n Hn.
    assert (H34 : Qle (3#4) (projT1 D n)) by (apply QleT'_to_Qle; exact (HD n Hn)).
    apply (qltT_eq_compat_r
            (Qminus (projT1 D n) (projT1 real_zero n))
            (projT1 D n) (1#2)).
    + cbn [projT1 real_zero]. ring.
    + apply Qlt_to_QltT. nra.
Qed.

Lemma abl9b_ext_inv_lip_real :
  forall (D E : Real)
    (HD34 : sigT (fun N : nat => forall n : nat, NatLe N n -> QleT' (3#4) (projT1 D n)))
    (HE34 : sigT (fun N : nat => forall n : nat, NatLe N n -> QleT' (3#4) (projT1 E n)))
    (sg : Q), QltT 0 sg ->
  real_le (real_abs (real_plus (real_inv_pos D (abl9b_ext_dom34_pos D HD34))
                                (real_opp (real_inv_pos E (abl9b_ext_dom34_pos E HE34)))))
          (real_plus (real_mult (real_const (16#9))
                                (real_abs (real_plus D (real_opp E))))
                     (real_const sg)).
Proof.
  intros D E HD34 HE34 sg Hsg.
  left. unfold real_lt.
  exists ((1#2) * sg). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1#2) sg).
    + unfold Qlt. simpl. lia.
    + apply QltT_to_Qlt. exact Hsg.
  - pose proof HD34 as HDc. destruct HDc as [ND HD].
    pose proof HE34 as HEc. destruct HEc as [NE HE].
    destruct (real_inv_proj D (abl9b_ext_dom34_pos D HD34)) as [NDi HDi].
    destruct (real_inv_proj E (abl9b_ext_dom34_pos E HE34)) as [NEi HEi].
    exists (Nat.max (Nat.max ND NE) (Nat.max NDi NEi)). intros n Hn.
    apply NatLe_drop in Hn.
    assert (HnD : NatLe ND n) by (apply NatLe_lift; lia).
    assert (HnE : NatLe NE n) by (apply NatLe_lift; lia).
    assert (HnDi : (NDi <= n)%nat) by lia.
    assert (HnEi : (NEi <= n)%nat) by lia.
    assert (HL : projT1 (real_abs (real_plus
                      (real_inv_pos D (abl9b_ext_dom34_pos D HD34))
                      (real_opp (real_inv_pos E (abl9b_ext_dom34_pos E HE34)))) ) n
                 == Qabs (Qinv (projT1 D n) - Qinv (projT1 E n))).
    { rewrite (real_abs_proj _ n).
      rewrite (real_plus_proj _ _ n). rewrite (real_opp_proj _ n).
      rewrite (HDi n HnDi). rewrite (HEi n HnEi). reflexivity. }
    assert (HR : projT1 (real_plus
                   (real_mult (real_const (16#9))
                              (real_abs (real_plus D (real_opp E))))
                   (real_const sg)) n
                 == (16#9) * Qabs (projT1 D n - projT1 E n) + sg).
    { rewrite (real_plus_proj _ _ n). rewrite (real_mult_proj _ _ n).
      rewrite (real_const_proj (16#9) n). rewrite (real_abs_proj _ n).
      rewrite (real_plus_proj D (real_opp E) n). rewrite (real_opp_proj E n).
      rewrite (real_const_proj sg n).
      assert (Hatom : Qabs (projT1 D n + - projT1 E n)
                      == Qabs (projT1 D n - projT1 E n)) by reflexivity.
      rewrite Hatom. reflexivity. }
    apply (qltT_eq_compat_r
            (Qminus (projT1 (real_plus
                       (real_mult (real_const (16#9))
                                  (real_abs (real_plus D (real_opp E))))
                       (real_const sg)) n)
                    (projT1 (real_abs (real_plus
                                (real_inv_pos D (abl9b_ext_dom34_pos D HD34))
                                (real_opp (real_inv_pos E (abl9b_ext_dom34_pos E HE34)))) ) n))
            ((16#9) * Qabs (projT1 D n - projT1 E n) + sg
             - Qabs (Qinv (projT1 D n) - Qinv (projT1 E n)))
            ((1#2) * sg)).
    + rewrite HR, HL. reflexivity.
    + apply Qlt_to_QltT.
      assert (H34D : QleT' (3#4) (projT1 D n)) by exact (HD n HnD).
      assert (H34E : QleT' (3#4) (projT1 E n)) by exact (HE n HnE).
      pose proof (abl9b_ext_qinv_lip (projT1 D n) (projT1 E n) H34D H34E) as HLip.
      assert (HLipq : Qle (Qabs (Qinv (projT1 D n) - Qinv (projT1 E n)))
                          ((16#9) * Qabs (projT1 D n - projT1 E n)))
        by (apply QleT'_to_Qle; exact HLip).
      assert (Hsgq : Qlt 0 sg) by (apply QltT_to_Qlt; exact Hsg).
      nra.
Qed.


(* ============================================================ *)
(* 块② clamp 1-Lipschitz（件30 abl9b_wc 逐点语义）                *)
(*   clamp x := Qmin (Qmax x (−1)) 1；结论 |clamp a − clamp b| ≤   *)
(*   |a − b|。证法：先立三点值刻画（x≤−1 ⟹ 值 −1；−1≤x≤1 ⟹ 值 x； *)
(*   1≤x ⟹ 值 1），再按 Qle_bool 反射三分（构造性判据，Set 层），  *)
(*   9 叶逐支以 nra 闭合；|a−b| 定号走块①的 Set 形析取辅助引理。  *)
(* ============================================================ *)

Lemma abl9b_ext_le_of_bool_false : forall x y : Q, Qle_bool x y = false -> Qle y x.
Proof.
  intros x y Hd.
  assert (Hn : ~ Qle x y).
  { intro Hc.
    assert (Ht : Qle_bool x y = true) by (apply (proj2 (Qle_bool_iff x y)); exact Hc).
    rewrite Ht in Hd. discriminate Hd. }
  nra.
Qed.

Lemma abl9b_ext_ge_of_bool_false : forall x : Q, Qle_bool x (-1) = false -> Qle (-1) x.
Proof.
  intros x Hd.
  apply (abl9b_ext_le_of_bool_false x (-1) Hd).
Qed.

Lemma abl9b_ext_clamp_lip : forall a b : Q,
  QleT' (Qabs (Qmin (Qmax a (-1)) 1 - Qmin (Qmax b (-1)) 1)) (Qabs (a - b)).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  assert (Hvalm : forall x : Q, Qle x (-1) -> Qmin (Qmax x (-1)) 1 == (-1)).
  { intros x Hx. rewrite (Q.max_r x (-1) Hx).
    apply Q.min_l. unfold Qle. simpl. lia. }
  assert (Hval0 : forall x : Q, Qle (-1) x -> Qle x 1 -> Qmin (Qmax x (-1)) 1 == x).
  { intros x H1 H2. rewrite (Q.max_l x (-1) H1). apply Q.min_l. exact H2. }
  assert (Hvalp : forall x : Q, Qle 1 x -> Qmin (Qmax x (-1)) 1 == 1).
  { intros x Hx. rewrite (Q.max_l x (-1)).
    - apply Q.min_r. exact Hx.
    - nra. }
  (* 三分（构造性）：每个分支先把 Qle 形序假设落入环境，供叶支 nra 读取 *)
  destruct (Qle_bool a (-1)) eqn:Ha1.
  - (* 支 A：a ≤ −1，clamp a == −1 *)
    assert (Hqa : Qle a (-1)) by (apply (proj1 (Qle_bool_iff a (-1))); exact Ha1).
    rewrite (Hvalm a Hqa).
    destruct (Qle_bool b (-1)) eqn:Hb1.
    + assert (Hqb : Qle b (-1)) by (apply (proj1 (Qle_bool_iff b (-1))); exact Hb1).
      rewrite (Hvalm b Hqb).
      destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
        [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
        | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
        apply Qabs_Qle_condition; nra.
    + assert (Hqgb : Qle (-1) b) by (apply abl9b_ext_ge_of_bool_false; exact Hb1).
      destruct (Qle_bool 1 b) eqn:Hb2.
      * assert (Hqbp : Qle 1 b) by (apply (proj1 (Qle_bool_iff 1 b)); exact Hb2).
        rewrite (Hvalp b Hqbp).
        destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
          [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
          | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
          apply Qabs_Qle_condition; nra.
      * assert (Hqbl : Qle b 1) by (apply abl9b_ext_le_of_bool_false; exact Hb2).
        rewrite (Hval0 b Hqgb Hqbl).
        destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
          [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
          | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
          apply Qabs_Qle_condition; nra.
  - destruct (Qle_bool 1 a) eqn:Ha2.
    + (* 支 B：1 ≤ a，clamp a == 1 *)
      assert (Hqap : Qle 1 a) by (apply (proj1 (Qle_bool_iff 1 a)); exact Ha2).
      rewrite (Hvalp a Hqap).
      destruct (Qle_bool b (-1)) eqn:Hb1.
      * assert (Hqb : Qle b (-1)) by (apply (proj1 (Qle_bool_iff b (-1))); exact Hb1).
        rewrite (Hvalm b Hqb).
        destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
          [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
          | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
          apply Qabs_Qle_condition; nra.
      * assert (Hqgb : Qle (-1) b) by (apply abl9b_ext_ge_of_bool_false; exact Hb1).
        destruct (Qle_bool 1 b) eqn:Hb2.
        -- assert (Hqbp : Qle 1 b) by (apply (proj1 (Qle_bool_iff 1 b)); exact Hb2).
           rewrite (Hvalp b Hqbp).
           destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
             [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
             | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
             apply Qabs_Qle_condition; nra.
        -- assert (Hqbl : Qle b 1) by (apply abl9b_ext_le_of_bool_false; exact Hb2).
           rewrite (Hval0 b Hqgb Hqbl).
           destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
             [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
             | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
             apply Qabs_Qle_condition; nra.
    + (* 支 C：−1 ≤ a ≤ 1，clamp a == a *)
      assert (Hqal : Qle a 1) by (apply abl9b_ext_le_of_bool_false; exact Ha2).
      assert (Hqga : Qle (-1) a) by (apply abl9b_ext_ge_of_bool_false; exact Ha1).
      rewrite (Hval0 a Hqga Hqal).
      destruct (Qle_bool b (-1)) eqn:Hb1.
      * assert (Hqb : Qle b (-1)) by (apply (proj1 (Qle_bool_iff b (-1))); exact Hb1).
        rewrite (Hvalm b Hqb).
        destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
          [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
          | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
          apply Qabs_Qle_condition; nra.
      * assert (Hqgb : Qle (-1) b) by (apply abl9b_ext_ge_of_bool_false; exact Hb1).
        destruct (Qle_bool 1 b) eqn:Hb2.
        -- assert (Hqbp : Qle 1 b) by (apply (proj1 (Qle_bool_iff 1 b)); exact Hb2).
           rewrite (Hvalp b Hqbp).
           destruct (abl9b_ext_abs_pm (a - b)) as [[Hs He] | [Hs He]]; rewrite He;
             [ assert (Hsq : Qle 0 (a - b)) by (apply QleT'_to_Qle; exact Hs)
             | assert (Hsq : Qle (a - b) 0) by (apply QleT'_to_Qle; exact Hs) ];
             apply Qabs_Qle_condition; nra.
        -- assert (Hqbl : Qle b 1) by (apply abl9b_ext_le_of_bool_false; exact Hb2).
           rewrite (Hval0 b Hqgb Hqbl).
           apply Qle_refl.
Qed.

(* ============================================================ *)
(* 块③ 缩放代数率                                                *)
(*   k_m := 1 − 1/m（分母取 S11 同款 (Z.of_nat m # 1) 除式形）；    *)
(*   率恒等 k²−1 == (k−1)(k+1)，|k−1| == 1/m，|k+1| ≤ 2，         *)
(*   故 |k²·u·x − u·x| ≤ (1/m)·2·|u||x| ≤ 2·(1/m)。              *)
(*   语句面率写为乘积形 2·(1/(Z.of_nat m # 1))，使全部代数闭合     *)
(*   目标保持对该原子线性（块①检验实测：二次除原子 nra 无 witness）。 *)
(* ============================================================ *)

Definition abl9b_ext_km (m : nat) : Q :=
  (1%Q - 1 / ((Z.of_nat m)%Z # 1)%Q)%Q.

Lemma abl9b_ext_km_pos : forall m : nat, NatLe 1 m ->
  Qle 0 (1 / ((Z.of_nat m)%Z # 1)%Q).
Proof.
  intros m Hm1.
  assert (Hn1 : (1 <= m)%nat) by (apply (NatLe_drop 1 m); exact Hm1).
  assert (Hzm : (1 <= Z.of_nat m)%Z) by lia.
  assert (Hpos : Qlt 0 ((Z.of_nat m)%Z # 1)%Q) by (unfold Qlt; simpl; lia).
  unfold Qdiv.
  apply (Qmult_le_0_compat 1 (Qinv ((Z.of_nat m)%Z # 1)%Q)).
  - unfold Qle. simpl. lia.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hpos.
Qed.

Lemma abl9b_ext_km_le1 : forall m : nat, NatLe 1 m ->
  Qle (1 / ((Z.of_nat m)%Z # 1)%Q) 1.
Proof.
  intros m Hm1.
  assert (Hn1 : (1 <= m)%nat) by (apply (NatLe_drop 1 m); exact Hm1).
  assert (Hzm : (1 <= Z.of_nat m)%Z) by lia.
  assert (Hpos : Qlt 0 ((Z.of_nat m)%Z # 1)%Q) by (unfold Qlt; simpl; lia).
  unfold Qdiv.
  apply (Qle_trans _ (Qinv 1) _).
  - apply (b5n_xinv_le 1 ((Z.of_nat m)%Z # 1)%Q 1);
      [exact Hpos | unfold Qlt; simpl; lia | unfold Qle; simpl; lia].
  - apply qeq_imp_qle. reflexivity.
Qed.

Lemma abl9b_ext_scaled_bnd : forall (m : nat) (xq : Q),
  NatLe 1 m -> QleT' (Qabs xq) 1 -> QleT' (Qabs (abl9b_ext_km m * xq)) 1.
Proof.
  intros m xq Hm1 Hx.
  pose proof (abl9b_ext_km_pos m Hm1) as Hqz.
  pose proof (abl9b_ext_km_le1 m Hm1) as Hq2.
  assert (Hkm0 : Qle 0 (abl9b_ext_km m)) by (unfold abl9b_ext_km; nra).
  assert (Hkm1 : Qle (abl9b_ext_km m) 1) by (unfold abl9b_ext_km; nra).
  apply Qle_to_QleT'.
  rewrite Qabs_Qmult.
  rewrite (Qabs_pos (abl9b_ext_km m) Hkm0).
  apply (Qle_trans _ (Qmult 1 (Qabs xq)) _).
  - apply (Qmult_le_compat_r (abl9b_ext_km m) 1 (Qabs xq));
      [exact Hkm1 | apply Qabs_nonneg].
  - rewrite (Qmult_comm 1 (Qabs xq)).
    apply (Qmult_le_compat_r (Qabs xq) 1 1);
      [apply QleT'_to_Qle; exact Hx | unfold Qle; simpl; lia].
Qed.

Lemma abl9b_ext_scale_rate : forall (m : nat) (xq uq : Q),
  NatLe 1 m -> QleT' (Qabs xq) 1 -> QleT' (Qabs uq) 1 ->
  QleT' (Qabs (abl9b_ext_km m * (abl9b_ext_km m * (uq * xq)) - uq * xq))
        (2 * (1 / ((Z.of_nat m)%Z # 1)%Q)).
Proof.
  intros m xq uq Hm1 Hx Hu.
  pose proof (abl9b_ext_km_pos m Hm1) as Hqz.
  pose proof (abl9b_ext_km_le1 m Hm1) as Hq2.
  assert (Hkm0 : Qle 0 (abl9b_ext_km m)) by (unfold abl9b_ext_km; nra).
  assert (Hk1 : Qabs (abl9b_ext_km m - 1) == (1 / ((Z.of_nat m)%Z # 1)%Q)).
  { assert (He : abl9b_ext_km m - 1 == - (1 / ((Z.of_nat m)%Z # 1)%Q))
      by (unfold abl9b_ext_km; ring).
    rewrite He. rewrite Qabs_opp.
    apply abl9b_ext_abs_eq.
    apply Qle_to_QleT'. exact Hqz. }
  assert (Hk2 : Qle (Qabs (abl9b_ext_km m + 1)) 2).
  { assert (Hkpos : Qle 0 (abl9b_ext_km m + 1)) by (unfold abl9b_ext_km; nra).
    rewrite (Qabs_pos (abl9b_ext_km m + 1) Hkpos).
    unfold abl9b_ext_km. nra. }
  assert (Hux : Qle (Qabs (uq * xq)) 1).
  { rewrite Qabs_Qmult.
    apply (Qle_trans _ (Qmult (Qabs uq) 1) _).
    - rewrite (Qmult_comm (Qabs uq) (Qabs xq)).
      rewrite (Qmult_comm (Qabs uq) 1).
      apply (Qmult_le_compat_r (Qabs xq) 1 (Qabs uq));
        [apply QleT'_to_Qle; exact Hx | apply Qabs_nonneg].
    - apply (Qmult_le_compat_r (Qabs uq) 1 1);
        [apply QleT'_to_Qle; exact Hu | unfold Qle; simpl; lia]. }
  apply Qle_to_QleT'.
  assert (Halg : abl9b_ext_km m * (abl9b_ext_km m * (uq * xq)) - uq * xq
                 == (abl9b_ext_km m - 1)
                    * ((abl9b_ext_km m + 1) * (uq * xq))) by ring.
  rewrite Halg, Qabs_Qmult, Qabs_Qmult, Hk1.
  apply (Qle_trans _ (Qmult (1 / ((Z.of_nat m)%Z # 1)%Q)
                            (Qmult 2 (Qabs (uq * xq)))) _).
  - rewrite (Qmult_comm (1 / ((Z.of_nat m)%Z # 1)%Q)
              (Qmult (Qabs (abl9b_ext_km m + 1)) (Qabs (uq * xq)))).
    rewrite (Qmult_comm (1 / ((Z.of_nat m)%Z # 1)%Q)
              (Qmult 2 (Qabs (uq * xq)))).
    apply (Qmult_le_compat_r
             (Qmult (Qabs (abl9b_ext_km m + 1)) (Qabs (uq * xq)))
             (Qmult 2 (Qabs (uq * xq)))
             (1 / ((Z.of_nat m)%Z # 1)%Q)).
    + apply (Qmult_le_compat_r (Qabs (abl9b_ext_km m + 1)) 2 (Qabs (uq * xq)));
        [exact Hk2 | apply Qabs_nonneg].
    + exact Hqz.
  - rewrite (Qmult_comm (1 / ((Z.of_nat m)%Z # 1)%Q)
              (Qmult 2 (Qabs (uq * xq)))).
    apply (Qle_trans _ (Qmult (Qmult 2 1) (1 / ((Z.of_nat m)%Z # 1)%Q)) _).
    + apply (Qmult_le_compat_r (Qmult 2 (Qabs (uq * xq))) (Qmult 2 1)
             (1 / ((Z.of_nat m)%Z # 1)%Q)).
      * rewrite (Qmult_comm 2 (Qabs (uq * xq))).
        rewrite (Qmult_comm 2 1).
        apply (Qmult_le_compat_r (Qabs (uq * xq)) 1 2);
          [exact Hux | unfold Qle; simpl; lia].
      * exact Hqz.
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 块④ 三项 eps 链闭合骨架（real_eq 语义，主公式代入点）          *)
(*   收敛证书 abl9b_ext_cv：Y_m→Y 的逐坐标 real_eq 形见证（取号    *)
(*   m ≥ m0 与 n ≥ N 二元一致）；链接证书 abl9b_ext_lk：           *)
(*   |Y_m−Z_m| ≤ δ_m 逐坐标；率证书 abl9b_ext_dm0：δ_m→0。骨架     *)
(*   定理 abl9b_ext_threeterm：|LHS−RHS| ≤ |LHS−LHS_m|+|LHS_m−    *)
(*   RHS_m|+|RHS_m−RHS| 三点三角链 + δ_m→0 ⟹ real_eq LHS RHS，    *)
(*   见证显式（m0/N 逐 eps 取号），零 case-split。                 *)
(* ============================================================ *)

Definition abl9b_ext_cv (Y : Real) (Ym : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun m0 : nat => sigT (fun N : nat =>
      forall m n : nat, NatLe m0 m -> NatLe N n ->
        QltT (Qabs (projT1 (Ym m) n - projT1 Y n)) eps)).

Definition abl9b_ext_lk (Ym Zm : nat -> Real) (dm : nat -> Q) : Set :=
  forall m n : nat,
    QleT' (Qabs (projT1 (Ym m) n - projT1 (Zm m) n)) (dm m).

Definition abl9b_ext_dm0 (dm : nat -> Q) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun m0 : nat => forall m : nat, NatLe m0 m -> QleT' (dm m) eps).

Lemma abl9b_ext_threeterm : forall (Y Z : Real) (Ym Zm : nat -> Real)
  (dm : nat -> Q),
  abl9b_ext_cv Y Ym -> abl9b_ext_cv Z Zm ->
  abl9b_ext_lk Ym Zm dm -> abl9b_ext_dm0 dm ->
  real_eq Y Z.
Proof.
  intros Y Z Ym Zm dm HcvY HcvZ Hlk Hdm0 eps Heps.
  pose (t := eps / 3).
  assert (H3 : QltT 0 t) by (apply (qltT_div_pos eps 3 Heps qltT_0_3)).
  destruct (Hdm0 t H3) as [md Hdm].
  destruct (HcvY t H3) as [mY [NY HcvY']].
  destruct (HcvZ t H3) as [mZ [NZ HcvZ']].
  exists (Nat.max NY NZ). intros n Hn.
  pose proof (NatLe_drop (Nat.max NY NZ) n Hn) as Hnle.
  assert (HnY : NatLe NY n) by (apply NatLe_lift; lia).
  assert (HnZ : NatLe NZ n) by (apply NatLe_lift; lia).
  set (M := Nat.max md (Nat.max mY mZ)).
  assert (Hmd : NatLe md M) by (apply NatLe_lift; lia).
  assert (HmY : NatLe mY M) by (apply NatLe_lift; lia).
  assert (HmZ : NatLe mZ M) by (apply NatLe_lift; lia).
  pose proof (Hdm M Hmd) as Hd.
  pose proof (HcvY' M n HmY HnY) as HY.
  pose proof (HcvZ' M n HmZ HnZ) as HZ.
  pose proof (Hlk M n) as HLK.
  apply Qlt_to_QltT.
  (* 三点三角链：|y−z| ≤ |ym−y| + (|ym−zm|+|zm−z|)，首项经取反定形 *)
  assert (Heq : projT1 Y n - projT1 Z n
                == - (projT1 (Ym M) n - projT1 Y n)
                   + ((projT1 (Ym M) n - projT1 (Zm M) n)
                      + (projT1 (Zm M) n - projT1 Z n))) by ring.
  rewrite Heq.
  pose proof (Qabs_triangle
    (- (projT1 (Ym M) n - projT1 Y n))
    ((projT1 (Ym M) n - projT1 (Zm M) n)
     + (projT1 (Zm M) n - projT1 Z n))) as Htri1.
  rewrite Qabs_opp in Htri1.
  apply (Qle_lt_trans _ (Qabs (projT1 (Ym M) n - projT1 Y n)
                          + Qabs ((projT1 (Ym M) n - projT1 (Zm M) n)
                                  + (projT1 (Zm M) n - projT1 Z n))) _).
  - exact Htri1.
  - apply (Qle_lt_trans _ (Qabs (projT1 (Ym M) n - projT1 Y n)
                           + (Qabs (projT1 (Ym M) n - projT1 (Zm M) n)
                              + Qabs (projT1 (Zm M) n - projT1 Z n))) _).
    + apply Qplus_le_compat; [apply Qle_refl | apply Qabs_triangle].
    + pose proof (QltT_to_Qlt _ _ HY) as HYq.
      pose proof (QltT_to_Qlt _ _ HZ) as HZq.
      pose proof (QleT'_to_Qle _ _ HLK) as HLKq.
      pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
      assert (Hs : Qle (t + (t + t)) eps)
        by (apply qeq_imp_qle; exact (atan_third_sum eps)).
      nra.
Qed.

(* δ_m := C·(1/m) 显式率证书（全非严格链：C/m ≤ C/(N+2) ≤        *)
(* C·(eps/(C+1)) ≤ eps，比值 C/(C+1) ≤ 1，零 case-split）         *)
Lemma abl9b_ext_dm_rate : forall C : Q, QleT' 0 C ->
  abl9b_ext_dm0 (fun m : nat => C * (1 / ((Z.of_nat m)%Z # 1)%Q)).
Proof.
  intros C HC eps Heps.
  assert (HC0 : Qle 0 C) by (apply QleT'_to_Qle; exact HC).
  assert (HCp : Qlt 0 (C + 1)) by nra.
  assert (HdivT : QltT 0 (eps / (C + 1)))
    by (apply (qltT_div_pos eps (C + 1));
        [exact Heps | apply Qlt_to_QltT; exact HCp]).
  pose proof (QltT_to_Qlt _ _ HdivT) as Hdivq.
  destruct (q_arch_inv (eps / (C + 1)) Hdivq) as [N HN].
  exists (N + 2)%nat. intros m Hm.
  assert (Hm2 : (N + 2 <= m)%nat) by (apply (NatLe_drop (N + 2) m); exact Hm).
  assert (Hinv : Qle (1 / ((Z.of_nat m)%Z # 1)%Q)
                     (1 / (Z.of_nat (N + 2) # 1))).
  { assert (HaDm : Qlt 0 ((Z.of_nat m)%Z # 1)%Q) by (unfold Qlt; simpl; lia).
    assert (HaDN : Qlt 0 ((Z.of_nat (N + 2)) # 1)) by (unfold Qlt; simpl; lia).
    (* 反序核：m ≥ N+2 时 Qinv 单调不增。等号支平凡；严格支走
       Qinv_lt_contravar（S02 q_arch_inv_mono 同款方向：p<q ⊢ /q</p），
       前稿把剩余目标立成 (N+2)<m 无严格前提故为假目标——此处以
       Nat.eq_dec 显式补严格间隙（构造性二分，无排中公理）。 *)
    assert (Hcore : Qle (Qinv ((Z.of_nat m)%Z # 1)%Q)
                        (Qinv (Z.of_nat (N + 2) # 1))).
    { destruct (Nat.eq_dec (N + 2) m) as [Heq | Hne].
      - rewrite Heq. apply Qle_refl.
      - assert (Hlt : (N + 2 < m)%nat) by lia.
        apply Qlt_le_weak.
        apply (proj1 (Qinv_lt_contravar ((Z.of_nat (N + 2)) # 1)
                  ((Z.of_nat m)%Z # 1)%Q HaDN HaDm)).
        unfold Qlt. simpl. lia. }
    apply (Qle_trans _ (Qinv ((Z.of_nat m)%Z # 1)%Q) _).
    - apply qeq_imp_qle. unfold Qdiv. ring.
    - apply (Qle_trans _ (Qinv (Z.of_nat (N + 2) # 1)) _).
      + exact Hcore.
      + apply qeq_imp_qle. unfold Qdiv. ring. }
  assert (Hs1 : Qle (C * (1 / ((Z.of_nat m)%Z # 1)%Q))
                    (C * (1 / (Z.of_nat (N + 2) # 1)))).
  { rewrite (Qmult_comm C (1 / ((Z.of_nat m)%Z # 1)%Q)).
    rewrite (Qmult_comm C (1 / (Z.of_nat (N + 2) # 1))).
    apply (Qmult_le_compat_r (1 / ((Z.of_nat m)%Z # 1)%Q)
                             (1 / (Z.of_nat (N + 2) # 1)) C);
      [exact Hinv | exact HC0]. }
  assert (Hs2 : Qle (C * (1 / (Z.of_nat (N + 2) # 1)))
                    (C * (eps / (C + 1)))).
  { rewrite (Qmult_comm C (1 / (Z.of_nat (N + 2) # 1))).
    rewrite (Qmult_comm C (eps / (C + 1))).
    apply (Qmult_le_compat_r (1 / (Z.of_nat (N + 2) # 1))
                             (eps / (C + 1)) C);
      [apply (Qlt_le_weak (1 / (Z.of_nat (N + 2) # 1)) (eps / (C + 1)));
       exact HN | exact HC0]. }
  assert (HCle : Qle C (C + 1)) by nra.
  assert (Heps0 : Qle 0 eps) by (apply (Qlt_le_weak 0 eps); apply QltT_to_Qlt; exact Heps).
  assert (Hu0 : Qle 0 (Qinv (C + 1)))
    by (apply (Qlt_le_weak 0 (Qinv (C + 1)));
        apply (Qinv_lt_0_compat (C + 1)); exact HCp).
  (* 比值锚：C·u ≤ 1，u := Qinv(C+1)。锚一 (C+1)·u == 1 由 Qmult_inv_r
     （u 为原子，此等式非 ring 方程，禁用 ring）；锚二 C ≤ C+1 跨乘。
     前稿把 Hratio 误立为 C·u ≤ 1·u（⟺ C ≤ 1，对 C>1 假命题）——不可证目标勘定重锚。 *)
  assert (Hzcp : ~ ((C + 1) == 0)).
  { intro Hz. rewrite Hz in HCp.
    exact (Qlt_not_eq 0 0 HCp (Qeq_refl 0)). }
  assert (Hcr : (C + 1) * Qinv (C + 1) == 1) by (apply Qmult_inv_r; exact Hzcp).
  assert (Hratio : Qle (C * Qinv (C + 1)) 1).
  { apply (Qle_trans _ ((C + 1) * Qinv (C + 1)) _).
    - apply (Qmult_le_compat_r C (C + 1) (Qinv (C + 1)));
        [exact HCle | exact Hu0].
    - apply qeq_imp_qle. rewrite Hcr. reflexivity. }
  assert (Hs3a : Qle (C * Qinv (C + 1) * eps) eps).
  { apply (Qle_trans _ (1 * eps) _).
    - apply (Qmult_le_compat_r (C * Qinv (C + 1)) 1 eps);
        [exact Hratio | exact Heps0].
    - apply qeq_imp_qle. ring. }
  (* 终装配：目标 LHS 是 C·(1/(m#1))（m 相关），走 Hs1→Hs2→比值锚三段；
     eps/(C+1) 与 eps·Qinv(C+1) 定义性可换，由 qeq_imp_qle+unfold Qdiv+ring
     闭合（前稿把终装配目标误立为 C·(eps/(C+1))——与其续作目标错位）。 *)
  apply Qle_to_QleT'.
  apply (Qle_trans _ (C * (1 / (Z.of_nat (N + 2) # 1))) _).
  - exact Hs1.
  - apply (Qle_trans _ (C * (eps / (C + 1))) _).
    + exact Hs2.
    + apply (Qle_trans _ (C * Qinv (C + 1) * eps) _).
      * apply qeq_imp_qle. unfold Qdiv. ring.
      * exact Hs3a.
Qed.

(* ============================================================ *)
(* 块④ LHS 侧 b5b_ap_uniform 实例化：缩放族 LHS_m → LHS 收敛证书  *)
(*   LHS := arctan(x+h) − arctan(x)（闭域 cw_unit 逐点证书）；     *)
(*   LHS_m := 同形于 (km·(x+h), km·x)，km := abl9b_ext_km(S m)；   *)
(*   逐坐标 |LHS_n−(LHS_m)_n| ≤ |S_n a−S_n ka|+|S_n kx−S_n x|     *)
(*   各以 b5b_ap_uniform（eps/2, d0）闭合；1/(S m) ≤ d0 由        *)
(*   q_arch_inv + b5n_xinv_le 反号单调显式取号。                   *)
(* ============================================================ *)

Lemma abl9b_ext_scx_proj : forall (k : Q) (x : Real) (n : nat),
  projT1 (real_mult (real_const k) x) n == k * projT1 x n.
Proof.
  intros k x n.
  rewrite (real_mult_proj (real_const k) x n).
  rewrite (real_const_proj k n).
  reflexivity.
Qed.

Lemma abl9b_ext_km_cwu : forall (m : nat) (x : Real) (Hx : cw_unit x),
  cw_unit (real_mult (real_const (abl9b_ext_km (Datatypes.S m))) x).
Proof.
  intros m x Hx n.
  (* Qeq 集合体重写不穿 QleT'（S02 自设关系无已注册等变实例），
     先降到 Qle（stdlib 注册族）再做投影重写，回程经 QleT'_to_Qle。 *)
  apply Qle_to_QleT'.
  rewrite abl9b_ext_scx_proj.
  apply QleT'_to_Qle.
  assert (Hm1 : NatLe 1 (Datatypes.S m)) by (apply NatLe_lift; lia).
  exact (abl9b_ext_scaled_bnd (Datatypes.S m) (projT1 x n) Hm1 (Hx n)).
Qed.

Lemma abl9b_ext_kmdiff_bnd : forall (m : nat) (z d0 : Q),
  QleT' (Qabs z) 1 ->
  Qle (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) d0 ->
  Qle (Qabs (z - abl9b_ext_km (Datatypes.S m) * z)) d0.
Proof.
  intros m z d0 Hz Hq.
  assert (Hm1 : NatLe 1 (Datatypes.S m)) by (apply NatLe_lift; lia).
  pose proof (abl9b_ext_km_pos (Datatypes.S m) Hm1) as Hq0.
  assert (He : z - abl9b_ext_km (Datatypes.S m) * z
               == (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) * z)
    by (unfold abl9b_ext_km; ring).
  rewrite He, Qabs_Qmult.
  rewrite (Qabs_pos (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) Hq0).
  apply (Qle_trans _ (Qmult (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) 1) _).
  - rewrite (Qmult_comm (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) (Qabs z)).
    rewrite (Qmult_comm (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) 1).
    apply (Qmult_le_compat_r (Qabs z) 1
             (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q));
      [apply QleT'_to_Qle; exact Hz | exact Hq0].
  - apply (Qle_trans _ (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) _).
    + apply qeq_imp_qle. ring.
    + exact Hq.
Qed.

Definition abl9b_ext_lhs_pt (x hx : Real) (Hx : cw_unit x)
  (Hxh : cw_unit (real_plus x hx)) : Real :=
  real_plus (cauchy_real_arctan (real_plus x hx) Hxh)
            (real_opp (cauchy_real_arctan x Hx)).

Definition abl9b_ext_lhs_sm (m : nat) (x hx : Real)
  (Hx : cw_unit x) (Hxh : cw_unit (real_plus x hx)) : Real :=
  real_plus
    (cauchy_real_arctan
       (real_mult (real_const (abl9b_ext_km (Datatypes.S m)))
                  (real_plus x hx))
       (abl9b_ext_km_cwu m (real_plus x hx) Hxh))
    (real_opp
       (cauchy_real_arctan
          (real_mult (real_const (abl9b_ext_km (Datatypes.S m))) x)
          (abl9b_ext_km_cwu m x Hx))).

Lemma abl9b_ext_lhs_conv : forall (x hx : Real) (Hx : cw_unit x)
  (Hxh : cw_unit (real_plus x hx)),
  abl9b_ext_cv (abl9b_ext_lhs_pt x hx Hx Hxh)
               (fun m : nat => abl9b_ext_lhs_sm m x hx Hx Hxh).
Proof.
  intros x hx Hx Hxh eps Heps.
  assert (H2q : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (Qinv 2)).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (b5b_ap_uniform (eps / 2) H2q) as [M [d0 [Hd0 Hcore]]].
  assert (Hd0q : Qlt 0 d0) by exact (QltT_to_Qlt 0 d0 Hd0).
  destruct (q_arch_inv d0 Hd0q) as [Nq HNq].
  exists (Nq + 2)%nat. exists M.
  intros m n Hm0 Hn.
  assert (Hm2 : (Nq + 2 <= m)%nat) by (apply (NatLe_drop (Nq + 2) m); exact Hm0).
  assert (Hq_d0 : Qle (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) d0).
  { assert (Hcore2 : Qle (1 * / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
                        (/ (Z.of_nat (Nq + 2) # 1))).
    { apply (b5n_xinv_le 1 ((Z.of_nat (Datatypes.S m))%Z # 1)%Q
                            ((Z.of_nat (Nq + 2)) # 1)).
      - unfold Qlt. simpl. lia.
      - unfold Qlt. simpl. lia.
      - rewrite (Qmult_1_l ((Z.of_nat (Nq + 2)) # 1)).
        unfold Qle. simpl. lia. }
    (* Qdiv 非展开记号：Qle 叶位 1/y（Qdiv 包裹形）与 /y（裸形）不可
       互换单化——桥接走 Qinv 裸形 Hcore2，两端 qeq 重述后 ring 闭合。 *)
    apply (Qle_trans _ (1 / (Z.of_nat (Nq + 2) # 1)) _).
    - apply (Qle_trans _ (1 * / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) _).
      + apply qeq_imp_qle. unfold Qdiv. ring.
      + apply (Qle_trans _ (/ (Z.of_nat (Nq + 2) # 1)) _).
        * exact Hcore2.
        * apply qeq_imp_qle. unfold Qdiv. ring.
    - exact (Qlt_le_weak _ _ HNq). }
  assert (HA3 : Qle (Qabs (projT1 (real_plus x hx) n
                           - abl9b_ext_km (Datatypes.S m)
                             * projT1 (real_plus x hx) n)) d0)
    by (apply (abl9b_ext_kmdiff_bnd m (projT1 (real_plus x hx) n) d0);
        [exact (Hxh n) | exact Hq_d0]).
  assert (HB3 : Qle (Qabs (projT1 x n
                           - abl9b_ext_km (Datatypes.S m) * projT1 x n)) d0)
    by (apply (abl9b_ext_kmdiff_bnd m (projT1 x n) d0);
        [exact (Hx n) | exact Hq_d0]).
  assert (HB3f : Qle (Qabs (abl9b_ext_km (Datatypes.S m) * projT1 x n
                           - projT1 x n)) d0).
  { assert (Ho : abl9b_ext_km (Datatypes.S m) * projT1 x n - projT1 x n
                 == - (projT1 x n - abl9b_ext_km (Datatypes.S m)
                                       * projT1 x n)) by ring.
    rewrite Ho, Qabs_opp. exact HB3. }
  assert (Hm1 : NatLe 1 (Datatypes.S m)) by (apply NatLe_lift; lia).
  assert (HA2 : QleT' (Qabs (abl9b_ext_km (Datatypes.S m)
                              * projT1 (real_plus x hx) n)) 1).
  { exact (abl9b_ext_scaled_bnd (Datatypes.S m) (projT1 (real_plus x hx) n)
            Hm1 (Hxh n)). }
  assert (HB2 : QleT' (Qabs (abl9b_ext_km (Datatypes.S m) * projT1 x n)) 1).
  { exact (abl9b_ext_scaled_bnd (Datatypes.S m) (projT1 x n) Hm1 (Hx n)). }
  (* 逐坐标投影 *)
  assert (HYp : projT1 (abl9b_ext_lhs_pt x hx Hx Hxh) n
                == arctan_partial n (projT1 (real_plus x hx) n)
                   - arctan_partial n (projT1 x n)).
  { unfold abl9b_ext_lhs_pt.
    rewrite (real_plus_proj (cauchy_real_arctan (real_plus x hx) Hxh)
              (real_opp (cauchy_real_arctan x Hx)) n).
    rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
    rewrite (arctan_real_proj (real_plus x hx) Hxh n).
    rewrite (arctan_real_proj x Hx n).
    reflexivity. }
  assert (HSp : projT1 (abl9b_ext_lhs_sm m x hx Hx Hxh) n
                == arctan_partial n (abl9b_ext_km (Datatypes.S m)
                                     * projT1 (real_plus x hx) n)
                   - arctan_partial n (abl9b_ext_km (Datatypes.S m)
                                       * projT1 x n)).
  { unfold abl9b_ext_lhs_sm.
    rewrite (real_plus_proj
              (cauchy_real_arctan
                 (real_mult (real_const (abl9b_ext_km (Datatypes.S m)))
                            (real_plus x hx))
                 (abl9b_ext_km_cwu m (real_plus x hx) Hxh))
              (real_opp
                 (cauchy_real_arctan
                    (real_mult (real_const (abl9b_ext_km (Datatypes.S m))) x)
                    (abl9b_ext_km_cwu m x Hx))) n).
    rewrite (real_opp_proj
              (cauchy_real_arctan
                 (real_mult (real_const (abl9b_ext_km (Datatypes.S m))) x)
                 (abl9b_ext_km_cwu m x Hx)) n).
    rewrite (arctan_real_proj
              (real_mult (real_const (abl9b_ext_km (Datatypes.S m)))
                         (real_plus x hx))
              (abl9b_ext_km_cwu m (real_plus x hx) Hxh) n).
    rewrite (arctan_real_proj
              (real_mult (real_const (abl9b_ext_km (Datatypes.S m))) x)
              (abl9b_ext_km_cwu m x Hx) n).
    rewrite (abl9b_ext_scx_proj (abl9b_ext_km (Datatypes.S m))
              (real_plus x hx) n).
    rewrite (abl9b_ext_scx_proj (abl9b_ext_km (Datatypes.S m)) x n).
    reflexivity. }
  set (p := arctan_partial n (projT1 (real_plus x hx) n)
            - arctan_partial n (abl9b_ext_km (Datatypes.S m)
                                * projT1 (real_plus x hx) n)).
  set (r := arctan_partial n (abl9b_ext_km (Datatypes.S m) * projT1 x n)
            - arctan_partial n (projT1 x n)).
  apply Qlt_to_QltT.
  rewrite (Qabs_Qminus (projT1 (abl9b_ext_lhs_sm m x hx Hx Hxh) n)
                       (projT1 (abl9b_ext_lhs_pt x hx Hx Hxh) n)).
  rewrite HYp. rewrite HSp.
  assert (Hsplit : arctan_partial n (projT1 (real_plus x hx) n)
                   - arctan_partial n (projT1 x n)
                   - (arctan_partial n (abl9b_ext_km (Datatypes.S m)
                                       * projT1 (real_plus x hx) n)
                      - arctan_partial n (abl9b_ext_km (Datatypes.S m)
                                          * projT1 x n))
                   == p + r) by (unfold p, r; ring).
  rewrite Hsplit.
  assert (Heps2 : Qle (eps / 2 + eps / 2) eps)
    by (apply qeq_imp_qle; unfold Qdiv; field).
  assert (Hc1 : Qlt (Qabs p) (eps / 2))
    by (exact (Hcore n (projT1 (real_plus x hx) n)
                  (abl9b_ext_km (Datatypes.S m) * projT1 (real_plus x hx) n)
                  Hn (Hxh n) HA2 HA3)).
  assert (Hc2 : Qlt (Qabs r) (eps / 2))
    by (exact (Hcore n (abl9b_ext_km (Datatypes.S m) * projT1 x n)
                  (projT1 x n) Hn HB2 (Hx n) HB3f)).
  apply (Qle_lt_trans _ (Qabs p + Qabs r) _).
  - apply Qabs_triangle.
  - apply (Qlt_le_trans _ (eps / 2 + eps / 2) _).
    + apply Qplus_lt_compat; [exact Hc1 | exact Hc2].
    + exact Heps2.
Qed.

(* ============================================================ *)
(* 块⑤ Hconv 参数位供给构造（件59 abl9b_rhs_sc_close 留接口的           *)
(*   甲侧供给，B3 合流位）                                           *)
(*   缩放对 (x_m,h_m) := k_m·(x,h)，k_m := abl9b_ext_km(S m)；          *)
(*   w_m := h_m·inv(D_m)，D_m := 1 + k_m²(x+h)x。点域事实：              *)
(*   x²≥0 与 hx ≥ −|h||x| ⟹ |h|<1/4 尾界下 (x+h)x ≥ −1/4 ⟹              *)
(*   D 与 D_m 逐点 ≥ 3/4（块① Qinv 内界 Lipschitz 直用域）；             *)
(*   |D_m−D| = (1−k_m²)·|(x+h)x| ≤ 2/(m+1)；首项 (1−k_m)·inv D_m ≤       *)
(*   (1/(m+1))·(4/3)；合计乘 |h|≤1/4 得显式率 (11/9)·(1/(m+1))。         *)
(* ============================================================ *)

(* 绝对值单侧辅助引理：a ≤ |a| 与 −|a| ≤ a（QleT' 承载，Set 层） *)
Lemma abl9b_ext_abs_ge_self : forall a : Q, QleT' a (Qabs a).
Proof.
  intros a. apply Qle_to_QleT'.
  destruct (abl9b_ext_abs_pm a) as [[Hs He] | [Hs He]].
  - rewrite He. apply Qle_refl.
  - rewrite He. assert (Hq : Qle a 0) by (apply QleT'_to_Qle; exact Hs). nra.
Qed.

Lemma abl9b_ext_abs_neg_le : forall a : Q, QleT' (- (Qabs a)) a.
Proof.
  intros a. apply Qle_to_QleT'.
  destruct (abl9b_ext_abs_pm a) as [[Hs He] | [Hs He]].
  - rewrite He. assert (Hq : Qle 0 a) by (apply QleT'_to_Qle; exact Hs). nra.
  - rewrite He. assert (Hq : Qle a 0) by (apply QleT'_to_Qle; exact Hs). nra.
Qed.

(* 点域下界核：|h|<1/4、|x|≤1、|x+h|≤1 ⟹ −1/4 ≤ (x+h)x
   （链：x²≥0；hx ≥ −|h||x| ≥ −(1/4)·1；和 ≥ −1/4） *)
Lemma abl9b_ext_pm_low : forall xq hxq : Q,
  Qlt (Qabs hxq) (1#4) -> Qle (Qabs xq) 1 -> Qle (Qabs (xq + hxq)) 1 ->
  Qle (- (1#4)) ((xq + hxq) * xq).
Proof.
  intros xq hxq Hh4 Hx Hxh.
  assert (Hx2 : Qle 0 (xq * xq)).
  { destruct (abl9b_ext_abs_pm xq) as [[Hs He] | [Hs He]].
    - apply Qmult_le_0_compat; apply QleT'_to_Qle; exact Hs.
    - assert (Hs' : Qle xq 0) by (apply QleT'_to_Qle; exact Hs).
      assert (Hn : Qle 0 (- xq)) by nra.
      assert (Hr : Qle 0 ((- xq) * (- xq)))
        by (apply Qmult_le_0_compat; exact Hn).
      apply (Qle_trans 0 ((- xq) * (- xq)) (xq * xq)).
      + exact Hr.
      + apply qeq_imp_qle. ring. }
  pose proof (abl9b_ext_abs_neg_le (hxq * xq)) as Hnb.
  assert (Hneg : Qle (- (Qabs hxq * Qabs xq)) (hxq * xq)).
  { apply QleT'_to_Qle in Hnb. rewrite Qabs_Qmult in Hnb. exact Hnb. }
  assert (Hb4 : Qle (Qabs hxq) (1#4))
    by (apply (Qlt_le_weak (Qabs hxq) (1#4)); exact Hh4).
  assert (Hfac : Qle (Qabs hxq * Qabs xq) ((1#4) * 1)).
  { apply (Qle_trans _ (Qabs xq * (1#4)) _).
    - rewrite (Qmult_comm (Qabs hxq) (Qabs xq)).
      apply (b3_qmult_le_l (Qabs hxq) (1#4) (Qabs xq)).
      + apply Qabs_nonneg.
      + exact Hb4.
    - rewrite (Qmult_comm (Qabs xq) (1#4)).
      apply (b3_qmult_le_l (Qabs xq) 1 (1#4)).
      + unfold Qle; simpl; lia.
      + exact Hx. }
  assert (Hchain : Qle (- (1#4)) (hxq * xq)).
  { apply (Qle_trans _ (- (Qabs hxq * Qabs xq)) _).
    - apply (Qle_trans _ (- ((1#4) * 1)) _).
      + apply qeq_imp_qle. ring.
      + apply (Qopp_le_compat (Qabs hxq * Qabs xq) ((1#4) * 1)). exact Hfac.
    - exact Hneg. }
  assert (Hrr : (xq + hxq) * xq == xq * xq + hxq * xq) by ring.
  rewrite Hrr.
  apply (Qle_trans _ (0 + (- (1#4))) _).
  - apply qeq_imp_qle. ring.
  - apply Qplus_le_compat; [exact Hx2 | exact Hchain].
Qed.

(* D 下界核：c∈[0,1] ⟹ 3/4 ≤ 1 + c·((x+h)x)（c:=1 得 D；c:=k² 得 D_m） *)
Lemma abl9b_ext_D_low : forall c xq hxq : Q,
  Qle 0 c -> Qle c 1 -> Qlt (Qabs hxq) (1#4) ->
  Qle (Qabs xq) 1 -> Qle (Qabs (xq + hxq)) 1 ->
  Qle (3#4) (1 + c * ((xq + hxq) * xq)).
Proof.
  intros c xq hxq Hc0 Hc1 Hh4 Hx Hxh.
  pose proof (abl9b_ext_pm_low xq hxq Hh4 Hx Hxh) as Hpm.
  assert (Hcp : Qle (- (1#4)) (c * ((xq + hxq) * xq))).
  { assert (Hm1 : Qle (c * (- (1#4))) (c * ((xq + hxq) * xq)))
      by (apply (b3_qmult_le_l (- (1#4)) ((xq + hxq) * xq) c);
          [exact Hc0 | exact Hpm]).
    assert (Hm2 : Qle ((1#4) * c) ((1#4) * 1))
      by (apply (b3_qmult_le_l c 1 (1#4));
          [unfold Qle; simpl; lia | exact Hc1]).
    assert (Hm2' : Qle (- (1#4)) (- ((1#4) * c))).
    { apply (Qle_trans _ (- ((1#4) * 1)) _).
      - apply qeq_imp_qle. ring.
      - apply (Qopp_le_compat ((1#4) * c) ((1#4) * 1)). exact Hm2. }
    apply (Qle_trans _ (- ((1#4) * c)) _).
    - exact Hm2'.
    - apply (Qle_trans _ (c * (- (1#4))) _).
      + apply qeq_imp_qle. ring.
      + exact Hm1. }
  apply (Qle_trans _ (1 + (- (1#4))) _).
  - apply qeq_imp_qle. ring.
  - apply Qplus_le_compat; [unfold Qle; simpl; lia | exact Hcp].
Qed.

(* 缩放坐标与 D_m 正性证书（见证 (1/4, N4)，N4=h 尾界见证、m 无关；
   Defined 透明闭合——real_inv_pos 定义体投影均匀性的构造基础） *)
Definition abl9b_ext_xsc (m : nat) (u : Real) : Real :=
  real_mult (real_const (abl9b_ext_km (Datatypes.S m))) u.

Lemma abl9b_ext_xsc_proj : forall (m : nat) (u : Real) (n : nat),
  projT1 (abl9b_ext_xsc m u) n == abl9b_ext_km (Datatypes.S m) * projT1 u n.
Proof.
  intros m u n.
  rewrite (real_mult_proj (real_const (abl9b_ext_km (Datatypes.S m))) u n).
  rewrite (real_const_proj (abl9b_ext_km (Datatypes.S m)) n).
  reflexivity.
Qed.

Lemma abl9b_ext_q14_pos : Qlt 0 (1#4).
Proof. unfold Qlt. simpl. lia. Qed.

(* D_m 点位正性（见证尾件）：|h_n|<1/4 ⟹ (1/4) < D_m,n（定义性投影前件） *)
Lemma abl9b_ext_sca_Hd_pt : forall (m : nat) (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1)
  (n : nat), NatLe N4 n ->
  QltT (1#4) (projT1 (real_plus real_one
         (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                    (abl9b_ext_xsc m x))) n
       - projT1 real_zero n).
Proof.
  intros m x hx N4 HN4 Hx Hxh n Hn.
  assert (Ht0 : Qle 0 (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q))
    by (apply abl9b_ext_km_pos; apply NatLe_lift; lia).
  assert (Ht1 : Qle (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) 1)
    by (apply abl9b_ext_km_le1; apply NatLe_lift; lia).
  assert (Hk0 : Qle 0 (abl9b_ext_km (Datatypes.S m)))
    by (unfold abl9b_ext_km; nra).
  assert (Hk1 : Qle (abl9b_ext_km (Datatypes.S m)) 1)
    by (unfold abl9b_ext_km; nra).
  assert (Hkk0 : Qle 0 (abl9b_ext_km (Datatypes.S m)
                         * abl9b_ext_km (Datatypes.S m))).
  { apply (Qmult_le_0_compat (abl9b_ext_km (Datatypes.S m))
             (abl9b_ext_km (Datatypes.S m))); exact Hk0. }
  assert (Hkk1 : Qle (abl9b_ext_km (Datatypes.S m)
                      * abl9b_ext_km (Datatypes.S m)) 1).
  { apply (Qle_trans _ (abl9b_ext_km (Datatypes.S m) * 1) _).
    - apply (b3_qmult_le_l (abl9b_ext_km (Datatypes.S m)) 1
               (abl9b_ext_km (Datatypes.S m))); [exact Hk0 | exact Hk1].
    - apply (Qle_trans _ (abl9b_ext_km (Datatypes.S m)) _).
      + apply qeq_imp_qle. ring.
      + exact Hk1. }
  assert (Hhn4 : Qlt (Qabs (projT1 hx n)) (1#4)) by (exact (HN4 n Hn)).
  assert (Hxn1 : Qle (Qabs (projT1 x n)) 1)
    by (apply QleT'_to_Qle; exact (Hx n)).
  assert (Hxhp : projT1 (real_plus x hx) n == projT1 x n + projT1 hx n)
    by (rewrite (real_plus_proj x hx n); reflexivity).
  assert (Hxhn1 : Qle (Qabs (projT1 x n + projT1 hx n)) 1).
  { assert (Ht : Qle (Qabs (projT1 (real_plus x hx) n)) 1)
      by (apply QleT'_to_Qle; exact (Hxh n)).
    rewrite Hxhp in Ht. exact Ht. }
  assert (HDp : projT1 (real_plus real_one
               (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                          (abl9b_ext_xsc m x))) n
              - projT1 real_zero n
              == 1 + abl9b_ext_km (Datatypes.S m) * abl9b_ext_km (Datatypes.S m)
                     * ((projT1 x n + projT1 hx n) * projT1 x n)).
  { rewrite (real_plus_proj real_one
              (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                         (abl9b_ext_xsc m x)) n).
    rewrite (real_mult_proj (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                            (abl9b_ext_xsc m x) n).
    rewrite (real_plus_proj (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx) n).
    rewrite (abl9b_ext_xsc_proj m x n). rewrite (abl9b_ext_xsc_proj m hx n).
    rewrite (b3r_one_proj n). cbn [projT1 real_zero]. ring. }
  apply (qltT_eq_compat_r
          (projT1 (real_plus real_one
             (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                        (abl9b_ext_xsc m x))) n
           - projT1 real_zero n)
          (1 + abl9b_ext_km (Datatypes.S m) * abl9b_ext_km (Datatypes.S m)
               * ((projT1 x n + projT1 hx n) * projT1 x n))
          (1#4)).
  - exact HDp.
  - apply Qlt_to_QltT.
    pose proof (abl9b_ext_D_low (abl9b_ext_km (Datatypes.S m)
                                 * abl9b_ext_km (Datatypes.S m))
                  (projT1 x n) (projT1 hx n) Hkk0 Hkk1 Hhn4 Hxn1 Hxhn1) as Hlow.
    apply (Qlt_le_trans (1#4) (3#4)
             (1 + abl9b_ext_km (Datatypes.S m) * abl9b_ext_km (Datatypes.S m)
                  * ((projT1 x n + projT1 hx n) * projT1 x n))).
    * unfold Qlt. simpl. lia.
    * exact Hlow.
Qed.

(* D_m 正性证书：纯项 Definition（见证 (1/4, N4) 语法可见——
   real_inv_pos 定义体 if 分支对 N4 定义性归约的构造基础） *)
Definition abl9b_ext_sca_Hd (m : nat) (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1)
  : real_lt real_zero (real_plus real_one
      (real_mult (real_plus (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx))
                 (abl9b_ext_xsc m x))) :=
  existT _ (1#4)
    (pair (Qlt_to_QltT 0 (1#4) abl9b_ext_q14_pos)
          (existT _ N4
             (fun (n : nat) (Hn : NatLe N4 n) =>
               abl9b_ext_sca_Hd_pt m x hx N4 HN4 Hx Hxh n Hn))).

(* 缩放 w 与点位投影（real_inv_pos 定义体直投影，见证 N4 均匀） *)
Definition abl9b_ext_ws (m : nat) (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1) : Real :=
  abl9b_w (abl9b_ext_xsc m x) (abl9b_ext_xsc m hx)
          (abl9b_ext_sca_Hd m x hx N4 HN4 Hx Hxh).

Lemma abl9b_ext_ws_proj : forall (m : nat) (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1)
  (n : nat), NatLe N4 n ->
  projT1 (abl9b_ext_ws m x hx N4 HN4 Hx Hxh) n
  == abl9b_ext_km (Datatypes.S m) * projT1 hx n
     * Qinv (1 + (abl9b_ext_km (Datatypes.S m) * (projT1 x n + projT1 hx n))
             * (abl9b_ext_km (Datatypes.S m) * projT1 x n)).
Proof.
  intros m x hx N4 HN4 Hx Hxh n Hn.
  assert (Hnle : (N4 <= n)%nat) by (apply (NatLe_drop N4 n); exact Hn).
  unfold abl9b_ext_ws, abl9b_w, abl9b_ext_sca_Hd.
  (* x/hx 一并 destruct：real_inv_pos 体内 x-match 先于证书 match，
     x 不破坏则证书 match 不可达（S09 real_inv_proj 同构证法）；
     证书为纯项 Definition，见证 N4 定义性可见，零 injection。 *)
  destruct x as [u Hu]. destruct hx as [v Hv].
  unfold real_inv_pos.
  cbn [projT1 real_plus real_one real_mult real_const abl9b_ext_xsc].
  rewrite (leb_correct _ _ Hnle).
  cbn [projT1 real_plus real_one real_mult real_const abl9b_ext_xsc].
  assert (Hrg : forall a b c : Q,
           1 + (c * a + c * b) * (c * a) == 1 + (c * (a + b)) * (c * a))
    by (intros; ring).
  rewrite (Hrg (u n) (v n) (abl9b_ext_km (Datatypes.S m))).
  reflexivity.
Qed.

(* 率核心（逐点原子形，t := 1/(m+1)）：O(1/m) 显式系数 11/9
   （首项 t·(4/3)，次项 (16/9)·2t，乘 |h|≤1/4；终叶 nra 线性闭合） *)
Lemma abl9b_ext_ws_rate_core : forall (h xn t : Q),
  Qlt (Qabs h) (1#4) ->
  Qle (Qabs xn) 1 -> Qle (Qabs (xn + h)) 1 ->
  Qle 0 t -> Qle t 1 ->
  Qle (Qabs ((1 - t) * h * Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
             - h * Qinv (1 + (xn + h) * xn)))
      ((11#9) * t).
Proof.
  intros h xn t Hh4 Hx Hxh Ht0 Ht1.
  assert (HabsHn : Qle (Qabs h) (1#4))
    by (apply (Qlt_le_weak (Qabs h) (1#4)); exact Hh4).
  assert (Hkksq0 : Qle 0 ((1 - t) * (1 - t))) by nra.
  assert (Hkksq1 : Qle ((1 - t) * (1 - t)) 1) by nra.
  assert (Hdm : Qle (3#4) (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))).
  { pose proof (abl9b_ext_D_low ((1 - t) * (1 - t)) xn h
                  Hkksq0 Hkksq1 Hh4 Hx Hxh) as Hdm0.
    apply (Qle_trans _ (1 + ((1 - t) * (1 - t)) * ((xn + h) * xn)) _).
    - exact Hdm0.
    - apply qeq_imp_qle. ring. }
  assert (Hc01 : Qle 0 1) by (unfold Qle; simpl; lia).
  assert (Hc11 : Qle 1 1) by (unfold Qle; simpl; lia).
  assert (Hdn : Qle (3#4) (1 + (xn + h) * xn)).
  { pose proof (abl9b_ext_D_low 1 xn h Hc01 Hc11 Hh4 Hx Hxh) as Hdn0.
    apply (Qle_trans _ (1 + 1 * ((xn + h) * xn)) _).
    - exact Hdn0.
    - apply qeq_imp_qle. ring. }
  assert (HdmP : Qlt 0 (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn)))
    by (apply (Qlt_le_trans 0 (3#4) _); [unfold Qlt; simpl; lia | exact Hdm]).
  assert (HdnP : Qlt 0 (1 + (xn + h) * xn))
    by (apply (Qlt_le_trans 0 (3#4) _); [unfold Qlt; simpl; lia | exact Hdn]).
  assert (H34p : Qlt 0 (3#4)) by (unfold Qlt; simpl; lia).
  assert (Hinv_m : Qle (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))) (4#3)).
  { destruct (Qle_lt_or_eq (3#4) (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn)) Hdm)
      as [Hlt | Heq].
    - apply (Qlt_le_weak _ (Qinv (3#4))).
      apply (proj1 (Qinv_lt_contravar (3#4) (1 + ((1 - t) * (xn + h))
                                        * ((1 - t) * xn)) H34p HdmP)).
      exact Hlt.
    - apply (Qle_trans _ (Qinv (3#4)) _).
      + apply qeq_imp_qle. apply Qinv_comp. apply (Qeq_sym _ _). exact Heq.
      + apply qeq_imp_qle. reflexivity. }
  assert (Hinv_n : Qle (Qinv (1 + (xn + h) * xn)) (4#3)).
  { destruct (Qle_lt_or_eq (3#4) (1 + (xn + h) * xn) Hdn) as [Hlt | Heq].
    - apply (Qlt_le_weak _ (Qinv (3#4))).
      apply (proj1 (Qinv_lt_contravar (3#4) (1 + (xn + h) * xn) H34p HdnP)).
      exact Hlt.
    - apply (Qle_trans _ (Qinv (3#4)) _).
      + apply qeq_imp_qle. apply Qinv_comp. apply (Qeq_sym _ _). exact Heq.
      + apply qeq_imp_qle. reflexivity. }
  assert (HLip : Qle (Qabs (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                              - Qinv (1 + (xn + h) * xn)))
                     ((16#9)
                      * Qabs ((1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                              - (1 + (xn + h) * xn)))).
  { apply QleT'_to_Qle. apply abl9b_ext_qinv_lip.
    - apply Qle_to_QleT'. exact Hdm.
    - apply Qle_to_QleT'. exact Hdn. }
  assert (HabsP : Qle (Qabs ((xn + h) * xn)) 1).
  { rewrite Qabs_Qmult.
    apply (Qle_trans _ (Qabs (xn + h) * 1) _).
    - apply (b3_qmult_le_l (Qabs xn) 1 (Qabs (xn + h))).
      + apply Qabs_nonneg.
      + exact Hx.
    - apply (Qle_trans _ (Qabs (xn + h)) _).
      + apply qeq_imp_qle. ring.
      + exact Hxh. }
  assert (Hdd : Qle (Qabs ((1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                           - (1 + (xn + h) * xn))) (2 * t)).
  { assert (Hald : (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                   - (1 + (xn + h) * xn)
                   == - ((1 - (1 - t) * (1 - t)) * ((xn + h) * xn))) by ring.
    rewrite Hald, Qabs_opp, Qabs_Qmult.
    assert (Hflip : Qabs (1 - (1 - t) * (1 - t)) == (1 - (1 - t) * (1 - t)))
      by (apply abl9b_ext_abs_eq; apply Qle_to_QleT'; nra).
    rewrite Hflip.
    apply (Qle_trans _ ((1 - (1 - t) * (1 - t)) * 1) _).
    - apply (b3_qmult_le_l (Qabs ((xn + h) * xn)) 1
               (1 - (1 - t) * (1 - t))).
      + nra.
      + exact HabsP.
    - apply (Qle_trans _ (1 - (1 - t) * (1 - t)) _).
      + apply qeq_imp_qle. ring.
      + nra. }
  assert (Halg : (1 - t) * h * Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                 - h * Qinv (1 + (xn + h) * xn)
                 == h * ((- t) * Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                         + (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                            - Qinv (1 + (xn + h) * xn)))) by ring.
  rewrite Halg, Qabs_Qmult.
  assert (HinvA0 : Qle 0 (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))))
    by (apply (Qlt_le_weak 0 _); apply (Qinv_lt_0_compat _); exact HdmP).
  set (A := (- t) * Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))).
  set (B := (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
             - Qinv (1 + (xn + h) * xn))).
  assert (HbA : Qle (Qabs A) (t * (4#3))).
  { unfold A. rewrite Qabs_Qmult, Qabs_opp.
    rewrite (Qabs_pos t Ht0).
    rewrite (Qabs_pos (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))) HinvA0).
    apply (b3_qmult_le_l (Qinv (1 + ((1 - t) * (xn + h)) * ((1 - t) * xn)))
             (4#3) t); [exact Ht0 | exact Hinv_m]. }
  assert (H160 : Qle 0 (16#9)) by (unfold Qle; simpl; lia).
  assert (HbB : Qle (Qabs B) ((16#9) * (2 * t))).
  { unfold B. apply (Qle_trans _ ((16#9) * Qabs ((1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                                       - (1 + (xn + h) * xn))) _).
    - exact HLip.
    - exact (b3_qmult_le_l (Qabs ((1 + ((1 - t) * (xn + h)) * ((1 - t) * xn))
                                    - (1 + (xn + h) * xn))) (2 * t) (16#9)
               H160 Hdd). }
  assert (HposS : Qle 0 (t * (4#3) + (16#9) * (2 * t))) by nra.
  assert (Hfin : Qle ((1#4) * (t * (4#3) + (16#9) * (2 * t))) ((11#9) * t)) by nra.
  apply (Qle_trans _ (Qabs h * (Qabs A + Qabs B)) _).
  - apply (b3_qmult_le_l (Qabs (A + B)) (Qabs A + Qabs B) (Qabs h)).
    + apply Qabs_nonneg.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (Qabs h * (t * (4#3) + (16#9) * (2 * t))) _).
    + apply (b3_qmult_le_l (Qabs A + Qabs B)
               (t * (4#3) + (16#9) * (2 * t)) (Qabs h)).
      * apply Qabs_nonneg.
      * apply Qplus_le_compat; [exact HbA | exact HbB].
    + apply (Qle_trans _ ((1#4) * (t * (4#3) + (16#9) * (2 * t))) _).
      * apply (Qmult_le_compat_r (Qabs h) (1#4)
                   (t * (4#3) + (16#9) * (2 * t)));
          [exact HabsHn | exact HposS].
      * exact Hfin.
Qed.

Lemma abl9b_ext_ws_rate : forall (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x hx) x))),
  sigT (fun Nv : nat => forall m n : nat, NatLe 1 m -> NatLe Nv n ->
    Qle (Qabs (projT1 (abl9b_ext_ws m x hx N4 HN4 Hx Hxh) n
               - projT1 (abl9b_w x hx Hd) n))
        ((11#9) * (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q))).
Proof.
  intros x hx N4 HN4 Hx Hxh Hd.
  destruct (real_inv_proj (real_plus real_one (real_mult (real_plus x hx) x)) Hd)
    as [NDn HDn].
  exists (Nat.max N4 NDn). intros m n Hm1 Hnv.
  pose proof (NatLe_drop (Nat.max N4 NDn) n Hnv) as Hnvle.
  assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
  assert (Hndn : (NDn <= n)%nat) by lia.
  assert (Ht0 : Qle 0 (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q))
    by (apply abl9b_ext_km_pos; apply NatLe_lift; lia).
  assert (Ht1 : Qle (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) 1)
    by (apply abl9b_ext_km_le1; apply NatLe_lift; lia).
  assert (Hk0 : Qle 0 (abl9b_ext_km (Datatypes.S m)))
    by (unfold abl9b_ext_km; nra).
  assert (Hkd : abl9b_ext_km (Datatypes.S m)
                == (1 - 1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)%Q)
    by (unfold abl9b_ext_km; reflexivity).
  assert (Hhn4 : Qlt (Qabs (projT1 hx n)) (1#4)) by (exact (HN4 n Hn4)).
  assert (Hxn1 : Qle (Qabs (projT1 x n)) 1) by (apply QleT'_to_Qle; exact (Hx n)).
  assert (Hxhp : projT1 (real_plus x hx) n == projT1 x n + projT1 hx n)
    by (rewrite (real_plus_proj x hx n); reflexivity).
  assert (Hxhn1 : Qle (Qabs (projT1 x n + projT1 hx n)) 1).
  { assert (Ht : Qle (Qabs (projT1 (real_plus x hx) n)) 1)
      by (apply QleT'_to_Qle; exact (Hxh n)).
    rewrite Hxhp in Ht. exact Ht. }
  pose proof (abl9b_ext_ws_proj m x hx N4 HN4 Hx Hxh n Hn4) as Hwmp.
  assert (Hw0p : projT1 (abl9b_w x hx Hd) n
                 == projT1 hx n * Qinv (1 + (projT1 x n + projT1 hx n)
                                        * projT1 x n)).
  { unfold abl9b_w.
    rewrite (real_mult_proj hx
               (real_inv_pos (real_plus real_one (real_mult (real_plus x hx) x)) Hd)
               n).
    rewrite (HDn n Hndn).
    assert (HDp : projT1 (real_plus real_one (real_mult (real_plus x hx) x)) n
                  == 1 + (projT1 x n + projT1 hx n) * projT1 x n).
    { rewrite (real_plus_proj real_one (real_mult (real_plus x hx) x) n).
      rewrite (real_mult_proj (real_plus x hx) x n).
      rewrite (real_plus_proj x hx n).
      rewrite (b3r_one_proj n). cbn [projT1 real_zero]. ring. }
    rewrite HDp. reflexivity. }
  rewrite Hwmp, Hw0p, Hkd.
  exact (abl9b_ext_ws_rate_core (projT1 hx n) (projT1 x n)
           (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
           Hhn4 Hxn1 Hxhn1 Ht0 Ht1).
Qed.

(* (M,Nv) 双见证闭合证书——件59 abl9b_rhs_sc_close 的 Hconv 参数位逐字形：
   对 d 取 m ≥ Nq+1（q_arch_inv 于 d·(9/11)），率 (11/9)/(m+1) ≤ d *)
Lemma abl9b_ext_ws_conv : forall (x hx : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 hx n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x hx) n)) 1)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x hx) x))),
  forall d : Q, Qlt 0 d ->
  sigT (fun M : nat => sigT (fun Nv : nat =>
    forall m : nat, (M <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
    Qle (Qabs (projT1 (abl9b_ext_ws m x hx N4 HN4 Hx Hxh) n
               - projT1 (abl9b_w x hx Hd) n)) d)).
Proof.
  intros x hx N4 HN4 Hx Hxh Hd d Hd0.
  destruct (abl9b_ext_ws_rate x hx N4 HN4 Hx Hxh Hd) as [Nv Hrate].
  assert (Hdp : Qlt 0 (d * (9#11)))
    by (apply (Qmult_lt_0_compat d (9#11)); [exact Hd0 | unfold Qlt; simpl; lia]).
  destruct (q_arch_inv (d * (9#11)) Hdp) as [Nq HNq].
  exists (Nq + 1)%nat. exists Nv. intros m Hm n Hn.
  assert (Hnv : NatLe Nv n) by (apply NatLe_lift; lia).
  assert (Hm1 : NatLe 1 m) by (apply NatLe_lift; lia).
  pose proof (Hrate m n Hm1 Hnv) as Hr.
  assert (Hminv : Qle (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
                      (1 / (Z.of_nat (Nq + 2) # 1))).
  { assert (HaDm : Qlt 0 ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
      by (unfold Qlt; simpl; lia).
    assert (HaDN : Qlt 0 ((Z.of_nat (Nq + 2)) # 1)) by (unfold Qlt; simpl; lia).
    assert (Hcore : Qle (Qinv ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
                        (Qinv (Z.of_nat (Nq + 2) # 1))).
    { destruct (Nat.eq_dec (Nq + 2) (Datatypes.S m)) as [Heq | Hne].
      - rewrite Heq. apply Qle_refl.
      - apply Qlt_le_weak.
        apply (proj1 (Qinv_lt_contravar (Z.of_nat (Nq + 2) # 1)
                  ((Z.of_nat (Datatypes.S m))%Z # 1)%Q HaDN HaDm)).
        unfold Qlt. simpl. lia. }
    apply (Qle_trans _ (Qinv ((Z.of_nat (Datatypes.S m))%Z # 1)%Q) _).
    - apply qeq_imp_qle. unfold Qdiv. ring.
    - apply (Qle_trans _ (Qinv (Z.of_nat (Nq + 2) # 1)) _).
      + exact Hcore.
      + apply qeq_imp_qle. unfold Qdiv. ring. }
  assert (H110 : Qle 0 (11#9)) by (unfold Qle; simpl; lia).
  apply (Qle_trans _ ((11#9) * (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)) _).
  - exact Hr.
  - apply (Qle_trans _ ((11#9) * (1 / (Z.of_nat (Nq + 2) # 1))) _).
    + exact (b3_qmult_le_l (1 / ((Z.of_nat (Datatypes.S m))%Z # 1)%Q)
               (1 / (Z.of_nat (Nq + 2) # 1)) (11#9) H110 Hminv).
    + apply (Qle_trans _ ((11#9) * (d * (9#11))) _).
      * apply (b3_qmult_le_l (1 / (Z.of_nat (Nq + 2) # 1)) (d * (9#11)) (11#9)).
        -- exact H110.
        -- apply (Qlt_le_weak _ _ HNq).
      * apply qeq_imp_qle. field.
Qed.

(* ============================================================ *)
(* 块⑥ LHS real_eq↔(M1,M2) 尾语义互译包装（件59 交付报告 §七·2        *)
(*   点名合流件，~三件）：real_eq/cv 形与 (M1,Nv) 逐点尾形双向互译，     *)
(*   供三项 eps 链与件59 (M1,M2) 闭合形无缝拼装。                      *)
(* ============================================================ *)

(* real_eq → (M1,Nv) 逐点尾形（M1:=0，无 m 依赖；Nv 取 eps/2 见证） *)
Lemma abl9b_ext_req_to_tail : forall (Y Z : Real),
  real_eq Y Z ->
  forall d : Q, Qlt 0 d ->
  sigT (fun M1 : nat => sigT (fun Nv : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
    Qle (Qabs (projT1 Y n - projT1 Z n)) d)).
Proof.
  intros Y Z Hreq d Hd0.
  assert (Hd2 : Qlt 0 (d / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat d (Qinv 2)).
    - exact Hd0.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (Hreq (d / 2) (Qlt_to_QltT _ _ Hd2)) as [N HN].
  exists 0%nat. exists N. intros m Hm n Hn.
  assert (Hnle : NatLe N n) by (apply NatLe_lift; lia).
  pose proof (HN n Hnle) as Hlt.
  apply (Qle_trans (Qabs (projT1 Y n - projT1 Z n)) (d / 2) d).
  - exact (Qlt_le_weak (Qabs (projT1 Y n - projT1 Z n)) (d / 2)
           (QltT_to_Qlt (Qabs (projT1 Y n - projT1 Z n)) (d / 2) Hlt)).
  - assert (Hhalf : (d / 2)%Q == d * Qinv 2) by (unfold Qdiv; ring).
    rewrite Hhalf.
    apply (Qle_trans _ (d * 1) _).
    + apply (b3_qmult_le_l (Qinv 2) 1 d).
      * exact (Qlt_le_weak 0 d Hd0).
      * apply (Qlt_le_weak (Qinv 2) 1). unfold Qlt. simpl. lia.
    + apply qeq_imp_qle. ring.
Qed.

(* cv 形 → (M1,Nv) 逐点尾形（m0/N 直传） *)
Lemma abl9b_ext_cv_to_tail : forall (Y : Real) (Ym : nat -> Real),
  abl9b_ext_cv Y Ym ->
  forall d : Q, Qlt 0 d ->
  sigT (fun M1 : nat => sigT (fun Nv : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
    Qle (Qabs (projT1 (Ym m) n - projT1 Y n)) d)).
Proof.
  intros Y Ym Hcv d Hd0.
  assert (Hd2 : Qlt 0 (d / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat d (Qinv 2)).
    - exact Hd0.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (Hcv (d / 2) (Qlt_to_QltT _ _ Hd2)) as [m0 [N HN]].
  exists m0. exists N. intros m Hm n Hn.
  assert (Hnm : NatLe m0 m) by (apply NatLe_lift; lia).
  assert (Hnle : NatLe N n) by (apply NatLe_lift; lia).
  pose proof (HN m n Hnm Hnle) as Hlt.
  apply (Qle_trans (Qabs (projT1 (Ym m) n - projT1 Y n)) (d / 2) d).
  - exact (Qlt_le_weak (Qabs (projT1 (Ym m) n - projT1 Y n)) (d / 2)
           (QltT_to_Qlt (Qabs (projT1 (Ym m) n - projT1 Y n)) (d / 2) Hlt)).
  - assert (Hhalf : (d / 2)%Q == d * Qinv 2) by (unfold Qdiv; ring).
    rewrite Hhalf.
    apply (Qle_trans _ (d * 1) _).
    + apply (b3_qmult_le_l (Qinv 2) 1 d).
      * exact (Qlt_le_weak 0 d Hd0).
      * apply (Qlt_le_weak (Qinv 2) 1). unfold Qlt. simpl. lia.
    + apply qeq_imp_qle. ring.
Qed.

(* (M1,Nv) 逐点尾形 → cv 形（eps/2 取号 + eps/2<eps 乘半间隙） *)
Lemma abl9b_ext_tail_to_cv : forall (Y : Real) (Ym : nat -> Real),
  (forall d : Q, Qlt 0 d ->
    sigT (fun M1 : nat => sigT (fun Nv : nat =>
      forall m : nat, (M1 <= m)%nat -> forall n : nat, (Nv <= n)%nat ->
      Qle (Qabs (projT1 (Ym m) n - projT1 Y n)) d))) ->
  abl9b_ext_cv Y Ym.
Proof.
  intros Y Ym Htail eps Heps.
  assert (Hd2 : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (Qinv 2)).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (Htail (eps / 2) Hd2) as [M1 [Nv HM]].
  exists M1. exists Nv. intros m n Hm Hn.
  pose proof (HM m (NatLe_drop M1 m Hm) n (NatLe_drop Nv n Hn)) as Hle.
  assert (Hhalf : Qlt (eps / 2) eps).
  { unfold Qdiv.
    apply (abl9_Qlt_transfer_l ((Qinv 2) * eps) (eps * Qinv 2) eps).
    - ring.
    - apply (abl9_Qlt_transfer_r ((Qinv 2) * eps) (1 * eps) eps).
      + ring.
      + apply (Qmult_lt_compat_r (Qinv 2) 1 eps).
        * apply QltT_to_Qlt. exact Heps.
        * unfold Qlt. simpl. lia. }
  apply Qlt_to_QltT.
  exact (Qle_lt_trans (Qabs (projT1 (Ym m) n - projT1 Y n)) (eps / 2) eps
           Hle Hhalf).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   承认面：全部主件逐件核验 Closed（下 Print Assumptions 组）。        *)
(*   提取检验：Q 层安全形（零 witness 位）四件 Separate Extraction，     *)
(*   Obj.magic 计数=0（交付报告落实测数）；witness 形（sca_Hd/ws_proj/  *)
(*   ws_rate/ws_conv/互译三件）沿件59 前例豁免提取命令（prod 实例化     *)
(*   硬错风险，fail-loud 登记），其计算内容由安全形与块③④实例覆盖。    *)
(* ============================================================ *)

Print Assumptions abl9b_ext_qinv_lip.
Print Assumptions abl9b_ext_inv_lip_real.
Print Assumptions abl9b_ext_clamp_lip.
Print Assumptions abl9b_ext_scale_rate.
Print Assumptions abl9b_ext_threeterm.
Print Assumptions abl9b_ext_dm_rate.
Print Assumptions abl9b_ext_lhs_conv.
Print Assumptions abl9b_ext_pm_low.
Print Assumptions abl9b_ext_D_low.
Print Assumptions abl9b_ext_sca_Hd.
Print Assumptions abl9b_ext_ws_rate_core.
Print Assumptions abl9b_ext_ws_rate.
Print Assumptions abl9b_ext_ws_conv.
Print Assumptions abl9b_ext_req_to_tail.
Print Assumptions abl9b_ext_cv_to_tail.
Print Assumptions abl9b_ext_tail_to_cv.

Set Extraction Output Directory "_log".
Separate Extraction abl9b_ext_abs_ge_self.
Separate Extraction abl9b_ext_pm_low.
Separate Extraction abl9b_ext_D_low.
Separate Extraction abl9b_ext_ws_rate_core.
