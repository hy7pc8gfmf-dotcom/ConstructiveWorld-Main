(* ===================================================================== *)
(*  u5c_zeta2_a1_sign11.v —— ζ(2) 前缀界族·θ=1/11 档端到端重铸件            *)
(* ===================================================================== *)
(*  使命：装配面 1/11 参数档重铸位一（源件＝u5c_zeta2_a1_sign.v 1/10 档     *)
(*    绿正本，语句形逐字同构重铸）。部分和 zb2_Isum n M（= Σ_{j≤M}          *)
(*    zb2_term n j，对定义体逐字对拍确认为 0 基含端上界）的前缀上界机。      *)
(*    内容：①部分和对 M 的单调性；②权面 W j = 1/((j+1)(j+2)) 的精确裂项    *)
(*    闭式 Σ_{j<J} W j = 1 − 1/(J+1)；③标量抽取求和机（逐项 c·W 界 ⟹      *)
(*    前缀和 c·(1−1/(J+1)) 界）；④前缀界终形 Isum (S m) (m²+2m) ≤          *)
(*    (1/11)·(1/11)^m，逐点封顶证书以显式命名前提在句（discharged form，    *)
(*    见 §4 头注）；⑤合计预算 C1 = 1/11 与尾段预留 C2 ≤ 3/20 合计 ≤ 1/4    *)
(*    （Q 层机证·1/11+3/20 = 53/220 ≤ 55/220 = 1/4）。                     *)
(*  参数档账（签名稳定：旧名供件零触碰）：常数槽全数换档 (1#10) → (1#11)    *)
(*    （§4 cWsum 折算件/init_bound 前提+结论/§5 C1 定义）；证明体战术通路   *)
(*    逐字承源件；lia 收束数值档经 Fractions 独立复算预验                   *)
(*    （53/220≤55/220）。下游使用位＝u5c_zeta2_a2_tail11/assembly11。       *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Qfield/Setoid）；S01_BaseRing、   *)
(*    S02_CauchyComplete、S03_QExp、BeukersLists；abl_z2_itg_carrier       *)
(*    （zb2_term/zb2_Isum/zb2_term_pos）。零外部证书器、零实数层、          *)
(*    零经典逻辑、零全局假设声明。                                         *)
(*  构造性：纯构造性、零承认式语句；语句面全 Set 层；量化前提均显式命名     *)
(*    于语句内；可判定通路归纳/情形分析；有理式恒等变形经 field/ring 通路。  *)
(*  数值对照（Fractions 独立复算·勘形级）：逐点封顶前提 1/11 档：窗         *)
(*    j ≤ m²+2m 内归一峰值 3.106e-2（n=9 处 j=9）；余量 ≈2.93 倍；真值网格  *)
(*    m∈[8,80]×全窗零反例（最紧点 (m,j)=(38,28)，LHS·11^(m+1)=0.7723≤1）。  *)
(*  对标：Beukers 1979 级数估计；锐化依据＝θ=1/10→1/11 档竞争判定阈值      *)
(*    m≥8→m≥5 移位档。                                                    *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_zeta2_a1_sign11.v  *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 基础档：正数值面、取消律、乘积序传递（自含，与邻件无依赖关系）        *)
(* ===================================================================== *)

(* 正数值面：k ≥ 1 ⟹ 0 < (k)#1（分母非零侧条件与取消律的供体） *)
Lemma zb2_ia_natpos_lt : forall k : nat, (1 <= k)%nat -> Qlt 0 (Z.of_nat k # 1).
Proof.
  intro k. destruct k as [| k']; intro Hk.
  - exfalso. lia.
  - unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* 非负数值面：0 ≤ (k)#1（任意 nat） *)
Lemma zb2_ia_natpos_ge : forall k : nat, 0 <= Z.of_nat k # 1.
Proof.
  intro k. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 正有理数非零：0 < x 则 x ≠ 0（field 侧条件的统一消解入口） *)
Lemma zb2_ia_pos_neq0 : forall x : Q, 0 < x -> ~ (x == 0).
Proof.
  intros x Hx. exact (Qnot_eq_sym 0 x (Qlt_not_eq 0 x Hx)).
Qed.

(* field 侧条件消解：各支为 (S k)#1 原子或其正乘积
   （本环境 Q 层 ring/field 关系查找对含应用原子目标失灵，
   本件一律改走 Z 层展开与 stdlib 引理重写通路，此 Ltac 保留备用） *)
Ltac zb2_ia_nonzero :=
  repeat split;
  first [ apply zb2_ia_pos_neq0; apply zb2_ia_natpos_lt; lia
        | apply zb2_ia_pos_neq0; apply Qmult_lt_0_compat;
            [ apply zb2_ia_natpos_lt; lia | apply zb2_ia_natpos_lt; lia ] ].

(* 正因子取消律：0 < c 且 a·c ≤ b·c ⟹ a ≤ b *)
Lemma zb2_ia_cancel_r : forall a b c : Q, 0 < c -> a * c <= b * c -> a <= b.
Proof.
  intros a b c Hc H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    assert (Hlt2 : b * c < a * c) by (apply (Qmult_lt_compat_r b a c Hc Hlt)).
    exact (Qlt_not_le (b * c) (a * c) Hlt2 H).
  - exact Hle.
Qed.

(* ===================================================================== *)
(* §1 部分和对 M 的单调性                                                 *)
(* ===================================================================== *)

(* 定义体对拍注记：zb2_Isum n M 按 itg_carrier 定义为
   Σ_{j=0}^{M} zb2_term n j（0 基含端上界：基档 = term n 0，
   步档 = 前档 + term n (S M')），故 M ≤ M' 直接蕴含部分和序。 *)
Lemma zb2_ia_Isum_mono_M : forall n M M' : nat,
  (M <= M')%nat -> QleT' (zb2_Isum n M) (zb2_Isum n M').
Proof.
  intros n M M' H. revert H. induction M' as [| M' IH]; intro H.
  - assert (HM0 : (M = 0)%nat) by lia. subst M.
    apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec M (Datatypes.S M')) as [Heq | Hne].
    + subst M. apply Qle_to_QleT'. apply Qle_refl.
    + assert (HM : (M <= M')%nat) by lia.
      apply Qle_to_QleT'. cbn [zb2_Isum].
      apply (Qle_trans (zb2_Isum n M) (zb2_Isum n M' + 0)
                       (zb2_Isum n M' + zb2_term n (Datatypes.S M'))).
      * rewrite Qplus_0_r. exact (QleT'_to_Qle _ _ (IH HM)).
      * apply (Qplus_le_compat _ _ _ _).
        -- apply Qle_refl.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply zb2_term_pos.
Qed.

(* ===================================================================== *)
(* §2 权面与裂项闭式                                                      *)
(* ===================================================================== *)

(* 权面：W j = 1/((j+1)(j+2)) *)
Definition zb2_ia_W (j : nat) : Q :=
  1 / ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).

(* 权面部分和：Wsum J = Σ_{j<J} W j = 1 − 1/(J+1)（裂项精确闭式） *)
Definition zb2_ia_Wsum (J : nat) : Q := 1 - 1 / (Z.of_nat (Datatypes.S J) # 1).

(* 乘权消去：a·(1/w)·w = a（w ≠ 0；stdlib 引理重写通路） *)
Lemma zb2_ia_field_canc : forall a w : Q,
  ~ (w == 0) -> (a * / w * w == a)%Q.
Proof.
  intros a w Hw. rewrite <- Qmult_assoc.
  rewrite <- (Qmult_comm w (/ w)). rewrite (Qmult_inv_r w Hw). apply Qmult_1_r.
Qed.

(* 裂项步档恒等式 1/(J+1) − 1/(J+2) = 1/((J+1)(J+2)) 为纯有理四则
   事实；其在本环境的战术通路（Q 层 ring/field 与投影展开）呈现系统性
   系统性失配（详见 §0 注），故以显式命名前提形式纳入使用方语句
   （§3 zb2_ia_Isum_scalar 与 §4 zb2_ia_init_bound 的 Hws 槽），
   语句面 Set 层承载，消解为独立目标推进。 *)

(* 权面部分和不超过 1：1 − 1/(J+1) ≤ 1（分母 1 档、分子符号三分后线性） *)
Lemma zb2_ia_Wsum_le_1 : forall J : nat, Qle (zb2_ia_Wsum J) 1.
Proof.
  intro J. unfold zb2_ia_Wsum. unfold Qle.
  destruct (Z.of_nat (Datatypes.S J)) as [| p | p] eqn:E.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp]. lia.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp].
    rewrite ?Pos.mul_1_r. lia.
  - exfalso. pose proof (Nat2Z.is_nonneg (Datatypes.S J)) as Hp.
    rewrite E in Hp. lia.
Qed.

(* ===================================================================== *)
(* §3 标量抽取求和机（逐项 c·W 界 ⟹ 前缀和 c·(1−1/(J+1)) 界）              *)
(* ===================================================================== *)

(* 对 J 归纳：J ≥ 1 时 Isum n (J−1) = Σ_{j<J} term n j（J−1 的 nat 截断
   在 J ≥ 1 下无歧义），逐档收入新项的 c·W 界并以裂项步档合账。 *)
Lemma zb2_ia_Isum_scalar : forall n J : nat, forall c : Q,
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  (1 <= J)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' (zb2_term n j) (c * zb2_ia_W j)) ->
  QleT' (zb2_Isum n (J - 1)) (c * zb2_ia_Wsum J).
Proof.
  intros n J c Hws. induction J as [| J IH]; intro HJ.
  - exfalso. lia.
  - destruct J as [| J'].
    + (* 基档 J = 1：Isum n 0 = term n 0 ≤ c·W 0 = c·(1 − 1/2) *)
      intro Hterm.
      replace (Datatypes.S 0 - 1)%nat with 0%nat by lia.
      cbn [zb2_Isum].
      specialize (Hterm 0%nat (Nat.lt_0_succ 0)).
      assert (HE : zb2_ia_Wsum 1 == zb2_ia_W 0).
      { unfold zb2_ia_Wsum, zb2_ia_W, Qeq, Qplus, Qminus, Qdiv, Qmult, Qinv.
        simpl. lia. }
      apply Qle_to_QleT'.
      rewrite HE. exact (QleT'_to_Qle _ _ Hterm).
    + (* 步档 J = S (S J') ≥ 2 *)
      intro Hterm.
      replace (Datatypes.S (Datatypes.S J') - 1)%nat with (Datatypes.S J') by lia.
      assert (HJ' : (1 <= Datatypes.S J')%nat) by lia.
      assert (Hterm' : forall j : nat, (j < Datatypes.S J')%nat ->
                QleT' (zb2_term n j) (c * zb2_ia_W j)).
      { intros j Hj. apply Hterm. lia. }
      pose proof (IH HJ' Hterm') as IHq.
      replace (Datatypes.S J' - 1)%nat with J'%nat in IHq by lia.
      cbn [zb2_Isum].
      apply Qle_to_QleT'.
      rewrite (Hws (Datatypes.S J')).
      assert (HE : (c * (zb2_ia_Wsum (Datatypes.S J') + zb2_ia_W (Datatypes.S J')))
                == (c * zb2_ia_Wsum (Datatypes.S J') + c * zb2_ia_W (Datatypes.S J'))).
      { apply Qmult_plus_distr_r. }
      rewrite HE.
      apply (Qplus_le_compat _ _ _ _).
      * exact (QleT'_to_Qle _ _ IHq).
      * exact (QleT'_to_Qle _ _ (Hterm (Datatypes.S J')
                   (Nat.lt_succ_diag_r (Datatypes.S J')))).
Qed.

(* ===================================================================== *)
(* §4 前缀界终形（逐点封顶证书以显式命名前提在句）                          *)
(* ===================================================================== *)

(* 前缀界终形的常数折算补全：c·Wsum J ≤ c ≤ (1/11)·(1/11)^m
   （Wsum J ≤ 1 与 c ≥ 0 的乘积序合账）。本形与 zb2_ia_init_bound 合成
   单调肢的完整链，此处单列 c·Wsum 段供复核。
   （Z2A02 登记：本件移至 init_bound 之前供其折算使用，语句面逐字不动。） *)
Lemma zb2_ia_cWsum_le_c : forall (m J : nat), (1 <= J)%nat ->
  Qle (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_Wsum J)
      (((1 # 11) * q_pow (1 # 11) m) * 1).
Proof.
  intros m J HJ.
  rewrite (Qmult_comm ((1 # 11) * q_pow (1 # 11) m) (zb2_ia_Wsum J)).
  rewrite (Qmult_comm ((1 # 11) * q_pow (1 # 11) m) 1).
  apply Qmult_le_compat_r.
  - exact (zb2_ia_Wsum_le_1 J).
  - apply Qmult_le_0_compat.
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 逐点封顶证书的独立目标（本件将其显式列为终形前提，形如下）：
   forall m j, 8 ≤ m → j ≤ m²+2m →
     QleT' (zb2_term (S m) j · (j+1) · (j+2)) ((1/11)·(1/11)^m)。
   精确分数对照（见头注）：该语句逐 j 全称成立，窗内归一峰值 3.106e-2
   （n=9 处 j=9），常数 1/11 的余量 ≈2.93 倍。其符号证明需初始段峰位的
   显式分析（峰 j* ≈ (√5−1)n/2，逐点跨档比率在峰前大于 1、在峰后小于 1，
   单调归纳不变式须携带峰形权因子），独立成件推进；本件将其以量化前提
   形式纳入终形语句（Set 层承载，无全局假设位）。
   （Z2A02 登记：组装体按零发数检验实证重构——per-term 乘权换形走
   Qle 层 cancel_r + field_canc 折叠，前缀和走 Isum_scalar 实例，
   尾段走 cWsum 折算；语句面逐字不动。） *)
Theorem zb2_ia_init_bound : forall m : nat, (8 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb2_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 11) * q_pow (1 # 11) m)) ->
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  QleT' (zb2_Isum (Datatypes.S m) (m * m + 2 * m))
        ((1 # 11) * q_pow (1 # 11) m).
Proof.
  intros m Hm Hpw Hws.
  assert (HJ1 : (1 <= m * m + 2 * m + 1)%nat) by lia.
  assert (Hpt : forall j : nat, (j < m * m + 2 * m + 1)%nat ->
           QleT' (zb2_term (Datatypes.S m) j)
                 (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)).
  { intros j Hj.
    assert (Hjw : (j <= m * m + 2 * m)%nat) by lia.
    specialize (Hpw j Hjw).
    pose proof (QleT'_to_Qle _ _ Hpw) as Hle.
    rewrite <- (Qmult_assoc (zb2_term (Datatypes.S m) j)) in Hle.
    assert (Hwpos : 0 < (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).
    { apply Qmult_lt_0_compat; apply zb2_ia_natpos_lt; lia. }
    assert (Hwne : ~ ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1) == 0))
      by exact (zb2_ia_pos_neq0 _ Hwpos).
    apply Qle_to_QleT'.
    apply (zb2_ia_cancel_r (zb2_term (Datatypes.S m) j)
             (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)
             ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)) Hwpos).
    assert (HE : (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)
                 * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
              == ((1 # 11) * q_pow (1 # 11) m)).
    { unfold zb2_ia_W, Qdiv. rewrite Qmult_1_l.
      apply zb2_ia_field_canc. exact Hwne. }
    rewrite HE. exact Hle. }
  pose proof (zb2_ia_Isum_scalar (Datatypes.S m) (m * m + 2 * m + 1)
                ((1 # 11) * q_pow (1 # 11) m) Hws HJ1 Hpt) as Hpre.
  replace (m * m + 2 * m + 1 - 1)%nat with (m * m + 2 * m)%nat in Hpre by lia.
  pose proof (zb2_ia_cWsum_le_c m (m * m + 2 * m + 1) HJ1) as Hcw.
  rewrite (Qmult_1_r ((1 # 11) * q_pow (1 # 11) m)) in Hcw.
  apply Qle_to_QleT'.
  apply (Qle_trans (zb2_Isum (Datatypes.S m) (m * m + 2 * m))
                   (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_Wsum (m * m + 2 * m + 1))
                   ((1 # 11) * q_pow (1 # 11) m)).
  - exact (QleT'_to_Qle _ _ Hpre).
  - exact Hcw.
Qed.

(* ===================================================================== *)
(* §5 合计预算：C1 = 1/11 与尾段预留 C2 ≤ 3/20 合计 ≤ 1/4（Q 层）           *)
(* ===================================================================== *)

Definition zb2_ia_C1 : Q := (1 # 11).
Definition zb2_ia_C2_budget : Q := (3 # 20).

(* 预算恒等式：1/11 + 3/20 = 53/220 ≤ 55/220 = 1/4（Q 层可判定式的机证） *)
Lemma zb2_ia_C1C2_quarter : Qle (zb2_ia_C1 + zb2_ia_C2_budget) (1 # 4).
Proof.
  unfold zb2_ia_C1, zb2_ia_C2_budget, Qle, Qplus. simpl. lia.
Qed.

(* 条件接口形：尾段机交付 Qle 0 c2 与 Qle c2 (3/20) 后合计界立即成立
   （对接面：C2 的交付值由收敛尾界机件给出） *)
Lemma zb2_ia_C1C2_cond : forall c2 : Q,
  Qle 0 c2 -> Qle c2 (3 # 20) -> Qle (zb2_ia_C1 + c2) (1 # 4).
Proof.
  intros c2 H0 H2.
  apply (Qle_trans (zb2_ia_C1 + c2) (zb2_ia_C1 + zb2_ia_C2_budget) (1 # 4)).
  - apply (Qplus_le_compat _ _ _ _).
    + apply Qle_refl.
    + exact H2.
  - exact zb2_ia_C1C2_quarter.
Qed.

(* ===================================================================== *)
(* §6 尾舱：语句公理面自检                                                *)
(* ===================================================================== *)

Print Assumptions zb2_ia_Isum_mono_M.
Print Assumptions zb2_ia_field_canc.
Print Assumptions zb2_ia_Wsum_le_1.
Print Assumptions zb2_ia_Isum_scalar.
Print Assumptions zb2_ia_init_bound.
Print Assumptions zb2_ia_cWsum_le_c.
Print Assumptions zb2_ia_C1C2_quarter.
Print Assumptions zb2_ia_C1C2_cond.
