(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   pkc_one_proj（原 L50，3 句玩具证）                                   *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                                *)
(* 使命：消费 CZI13 基建件 EpsTrichotomy（消融50/，etc_ 12 件全真证）   *)
(*   逐账攻 UpReqPinskerCore 四挂账（:20 常数2 / :991 S1近支判分 /      *)
(*   :1305 R8 S1近支-S2 / :2461 W3 截断桥）。前缀 pkc_ 全库零撞名。     *)
(*                                                                *)
(* 账-件对照（结论面取挂账语句的库内诚实变体，逐条如实登记）：        *)
(*   ① :20 常数 2 账 → pkc_sign_load（ε-三分符号支点级装载，          *)
(*      即挂账自述前置「p<q+δ 与 q<p+δ 的 Cauchy 点级比较」的装载件）   *)
(*      消费 etc_sign_tri + etc_eps_half_pos + etc_eps_half_add）。    *)
(*      常数 2 完整形（S1 近支/S2 二阶核本体）仍未落——见文尾挂账登记。  *)
(*   ② :991 / :1305 S1 近支判分账 → pkc_oneside_far_load /            *)
(*      pkc_oneside_near_load（etc_one_side 分账装载：把 Real 层       *)
(*      一侧分离前提逐坐标点裁决到 far/near 支，另一侧支点级排空）。    *)
(*      S1 近支 log 本体（二阶核）仍未落——库内 grep 核实无此引擎，     *)
(*      挂账 R8 如实登记。                                            *)
(*   ③ :2461 W3 账 → pkc_w3_qface（Q 层比较面装配：cec_cstar 尾段     *)
(*      常数面经 etc_compare_tri 三分裁决收拢到 Eq 支）。挂账语句所引   *)
(*      pnk_pinsker_trunc5（kl₂ 与 c*(k) 的 KL 语义桥）经全库 grep     *)
(*      （含 Live/build/）确认不在盘——依赖缺口如实登记，本件只交付     *)
(*      其 Q 层常数比较面。                                           *)
(*                                                                *)
(* 消费面：S01（Set 层 Id/And/Or/NatLe/sigT）、S02（QltT/QleT'/QeqT/  *)
(*   real_lt/桥族）、EpsTrichotomy（etc_ 件）、UpReqEngineCeiling      *)
(*   （cec_cstar_tail）、stdlib QArith（Qlt_minus_iff/Qplus_comp 等）。*)
(*                                                                *)
(* 红线自审：主件语句面全 Set 值（sigT/comparison/QltT/QeqT/And/Id），  *)
(*   零 Prop 型主语句、零新增假设公理；证内排空支一律 Id false true    *)
(*   显式两支消解（沿 etc_apart 先例）；全真证 Qed/Defined；           *)
(*   文尾 Print Assumptions 审计 + 提取探针。                          *)
(* 编译：source Live/toolchain/env.sh 后                              *)
(*   rocq c -q -Q <vo_901信任根> "" -Q /tmp/czi13_side "" -Q . ""      *)
(*   PinskerCoreClose.v（9.1 live 轨；vo_901 直载 + CZI13 侧根拼接）   *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring
               ZArith.Zorder Setoid Lia Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqEngineCeiling.
Require Import EpsTrichotomy.

(* ============================================================ *)
(* §0 单元面小件：real_one 逐坐标投影 + 减法等值面双保               *)
(* ============================================================ *)

(* real_one 逐坐标投影叶：projT1 real_one n == 1（real_one 定义面透明） *)
Lemma pkc_one_proj : forall n : nat, (projT1 real_one n == 1)%Q.
Proof. intro n. cbv [projT1 real_one]. exact (Qeq_refl 1%Q). Qed.

(* 左元减法等值面：a == b ⟹ x − a == x − b *)
Lemma pkc_minus_l_wd : forall a b x : Q, (a == b)%Q -> (x - a == x - b)%Q.
Proof.
  intros a b x H.
  apply (Qeq_trans (x + - a) (x + - b)).
  - apply Qplus_comp; [apply Qeq_refl | apply (Qopp_comp a b H) ].
  - apply Qeq_refl.
Qed.

(* 右元减法等值面：a == b ⟹ a − x == b − x *)
Lemma pkc_minus_r_wd : forall a b x : Q, (a == b)%Q -> (a - x == b - x)%Q.
Proof.
  intros a b x H.
  apply (Qeq_trans (a + - x) (b + - x)).
  - apply Qplus_comp; [exact H | apply Qeq_refl].
  - apply Qeq_refl.
Qed.

(* 左元严格小代换：x == y、x ＜ z ⟹ y ＜ z（CZI13 etc_qeq_lt_r 同配方，
   乘子取 Qden x 的 Z 层显式乘式链） *)
Lemma pkc_qeq_lt_l : forall x y z : Q, (x == y)%Q -> (x < z)%Q -> (y < z)%Q.
Proof.
  intros x y z He Hlt.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qlt in Hlt. unfold Qeq in He. unfold Qlt.
  apply (Zmult_lt_reg_r (Qnum y * Z.pos (Qden z))
           (Qnum z * Z.pos (Qden y)) (Z.pos (Qden x))).
  - exact Hdx.
  - replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_lt_compat_r (Qnum x * Z.pos (Qden z))
             (Qnum z * Z.pos (Qden x)) (Z.pos (Qden y))).
    + exact Hdy.
    + exact Hlt.
Qed.

(* 半量严格小：0 < e ⟹ (1#2)·e ＜ e（eps 分半的半-全比较叶：
   全程消费基建件 etc_eps_half_pos / etc_eps_half_add） *)
Lemma pkc_half_lt : forall e : Q, QltT 0 e -> QltT ((1#2) * e) e.
Proof.
  intros e H.
  assert (Hpos : QltT 0 ((1#2) * e)) by exact (etc_eps_half_pos e H).
  assert (Hlt : (0 < (1#2) * e)%Q) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hsub : ((1#2) * e == e - (1#2) * e)%Q).
  { assert (Ta : (((1#2) * e + (1#2) * e) + - ((1#2) * e))
                 == ((1#2) * e + ((1#2) * e + - ((1#2) * e))))
      by exact (Qeq_sym _ _
             (Qplus_assoc ((1#2) * e) ((1#2) * e) (- ((1#2) * e)))).
    assert (Tb : ((1#2) * e + ((1#2) * e + - ((1#2) * e)))
                 == ((1#2) * e + 0))
      by (apply Qplus_comp; [apply Qeq_refl | apply Qplus_opp_r]).
    assert (Tc : ((1#2) * e + 0) == (1#2) * e) by apply Qplus_0_r.
    assert (T4 : (((1#2) * e + (1#2) * e) + - ((1#2) * e)) == (1#2) * e)
      by exact (Qeq_trans _ _ _ Ta (Qeq_trans _ _ _ Tb Tc)).
    apply (Qeq_trans _ _ _ (Qeq_sym _ _ T4)).
    apply Qplus_comp; [exact (etc_eps_half_add e) | apply Qeq_refl]. }
  assert (Hsub' : (0 < e - (1#2) * e)%Q)
    by exact (etc_qeq_lt_r _ _ 0 Hsub Hlt).
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff ((1#2) * e) e)).
  unfold Qminus. exact Hsub'.
Qed.

(* ============================================================ *)
(* §1 :20 常数 2 账·其一——ε-三分符号支点级装载                       *)
(*   挂账自述前置：「两支的构造性证明需 ε-三分（p<q+δ 与 q<p+δ 的     *)
(*   Cauchy 点级比较）基建」。本件把 Real 层一侧分离（real_lt q p）    *)
(*   的见证逐坐标点装载为 Q 层符号三分裁决：对一切足够远坐标，         *)
(*   p_n − q_n 的 etc_sign_tri 判定必落正支（Lt 支），负支/零支       *)
(*   逐点排空（Id false true 显式消解）。                              *)
(* ============================================================ *)

Theorem pkc_sign_load : forall (p q : Real), real_lt q p ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => Id false true
      | Eq => Id false true
      | Gt => QltT 0 (projT1 p n - projT1 q n)
      end)).
Proof.
  intros p q Hpq. destruct Hpq as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNd : QltT d (projT1 p n - projT1 q n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  assert (HltD : (d < projT1 p n - projT1 q n)%Q) by (apply QltT_to_Qlt; exact HNd).
  destruct (etc_sign_tri (projT1 p n - projT1 q n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝p_n − q_n == 0 ⟹ d ＜ 0，与 0 ＜ d 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hlt0 : (d < 0)%Q) by exact (etc_qeq_lt_r _ 0 d Hc HltD).
    assert (Hcc : (0 < 0)%Q) by (apply Qlt_trans with d; [exact Hd | exact Hlt0]).
    destruct (Qlt_irrefl 0 Hcc).
  - (* Lt 支＝0 ＜ p_n − q_n：正支成立，装 Gt 标签 *)
    exists Gt. exact Hc.
  - (* Gt 支＝p_n − q_n ＜ 0 ⟹ d ＜ 负，与 0 ＜ d 矛盾 *)
    assert (Hneg : (projT1 p n - projT1 q n < 0)%Q) by (apply QltT_to_Qlt; exact Hc).
    assert (Hlt0 : (d < 0)%Q) by exact (Qlt_trans d _ _ HltD Hneg).
    assert (Hcc : (0 < 0)%Q) by (apply Qlt_trans with d; [exact Hd | exact Hlt0]).
    destruct (Qlt_irrefl 0 Hcc).
Defined.

(* ============================================================ *)
(* §2 :20 常数 2 账·其二——eps 分半余量装载                           *)
(*   消费 etc_eps_half_pos（半量正性）+ etc_eps_half_add（分半回接）：  *)
(*   一侧分离见证 δ 可安全减半：半量 δ/2 自身正、且逐坐标仍是           *)
(*   p_n − q_n 的严格下界（半-全比较经 pkc_half_lt）。                  *)
(* ============================================================ *)

Theorem pkc_half_slack_load : forall (p q : Real), real_lt q p ->
  sigT (fun d : Q =>
    And (QltT 0 d)
    (And (((1#2) * d + (1#2) * d == d)%Q)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT ((1#2) * d) (projT1 p n - projT1 q n))))).
Proof.
  intros p q Hpq. destruct Hpq as [e [He0 [N HN]]].
  exists e. split.
  - (* 见证正性 *)
    exact He0.
  - split.
    + (* 分半回接恒等：直接消费基建件 *)
      exact (etc_eps_half_add e).
    + exists N. intros n Hn.
      assert (Hhalf : QltT ((1#2) * e) e) by (apply pkc_half_lt; exact He0).
      assert (HNn : QltT e (projT1 p n - projT1 q n)) by (apply HN; exact Hn).
      apply QltT_to_Qlt in Hhalf.
      apply QltT_to_Qlt in HNn.
      apply Qlt_to_QltT.
      exact (Qlt_trans _ _ _ Hhalf HNn).
Defined.

(* ============================================================ *)
(* §3 :991 / :1305 S1 近支判分账——etc_one_side 分账装载               *)
(*   挂账语句：「t>1 给 t²(t−1)≥_B 0 …；t∈[0,1] 支挂账」（:991）与     *)
(*   「诚实边界：S1 近支/S2 未落，挂账 R8」（:1305）。本节交付其判分面： *)
(*   把 Real 层单位一侧分离前提逐坐标点裁决到 far 支（1 ＜ t_n，        *)
(*   :991 远支已落引擎的前提面）或 near 支（t_n ＜ 1），对侧支逐点      *)
(*   排空。log 本体（二阶核）不在盘，见文尾登记。                      *)
(* ============================================================ *)

(* 远支装载：real_lt real_one t ⟹ 足够远坐标全部落 1 ＜ t_n 支 *)
Theorem pkc_oneside_far_load : forall t : Real, real_lt real_one t ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => Id false true
      | Eq => Id false true
      | Gt => QltT 1 (projT1 t n)
      end)).
Proof.
  intros t H. destruct H as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNn : QltT d (projT1 t n - projT1 real_one n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  apply QltT_to_Qlt in HNn.
  assert (H1n : (projT1 t n - projT1 real_one n == projT1 t n - 1)%Q)
    by (apply pkc_minus_l_wd; apply pkc_one_proj).
  assert (HNn' : (d < projT1 t n - 1)%Q) by exact (etc_qeq_lt_r _ _ d H1n HNn).
  assert (Hpos : (0 < projT1 t n - 1)%Q) by exact (Qlt_trans 0 d _ Hd HNn').
  assert (Hfar : (1 < projT1 t n)%Q).
  { apply (proj2 (Qlt_minus_iff 1 (projT1 t n))). unfold Qminus. exact Hpos. }
  destruct (etc_one_side (projT1 t n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝t_n == 1，与 1 ＜ t_n 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (etc_qeq_lt_r _ 1 1 Hc Hfar).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Lt 支＝t_n ＜ 1，与 1 ＜ t_n 矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (Qlt_trans 1 _ _ Hfar Hc).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Gt 支＝1 ＜ t_n：far 支成立 *)
    exists Gt. exact Hc.
Defined.

(* 近支装载：real_lt t real_one ⟹ 足够远坐标全部落 t_n ＜ 1 支 *)
Theorem pkc_oneside_near_load : forall t : Real, real_lt t real_one ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => QltT (projT1 t n) 1
      | Eq => Id false true
      | Gt => Id false true
      end)).
Proof.
  intros t H. destruct H as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNn : QltT d (projT1 real_one n - projT1 t n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  apply QltT_to_Qlt in HNn.
  assert (H1n : (projT1 real_one n - projT1 t n == 1 - projT1 t n)%Q)
    by (apply pkc_minus_r_wd; apply pkc_one_proj).
  assert (HNn' : (d < 1 - projT1 t n)%Q) by exact (etc_qeq_lt_r _ _ d H1n HNn).
  assert (Hpos : (0 < 1 - projT1 t n)%Q) by exact (Qlt_trans 0 d _ Hd HNn').
  assert (Hnear : (projT1 t n < 1)%Q).
  { apply (proj2 (Qlt_minus_iff (projT1 t n) 1)). unfold Qminus. exact Hpos. }
  destruct (etc_one_side (projT1 t n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝t_n == 1，与 t_n ＜ 1 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (pkc_qeq_lt_l _ 1 1 Hc Hnear).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Lt 支＝t_n ＜ 1：near 支成立 *)
    exists Lt. exact Hc.
  - (* Gt 支＝1 ＜ t_n，与 t_n ＜ 1 矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (Qlt_trans 1 _ _ Hc Hnear).
    destruct (Qlt_irrefl 1 Hcc).
Defined.

(* ============================================================ *)
(* §4 :2461 W3 账——Q 层比较面装配                                     *)
(*   挂账语句：「与 KL 语义的桥接件（kl₂ ≥ c*(k)·TV²）即 W3 依赖的     *)
(*   pnk_pinsker_trunc5，未在盘，挂账如实登记」（:2459-2461）。        *)
(*   依赖缺口核实：pnk_pinsker_trunc5 经全库 grep（含 Live/build/）    *)
(*   确认不在盘（仅注释/报告提及）。本件交付 W3 所需的 Q 层常数比较面： *)
(*   天花板常数 c*(k)（k≥5 尾段）对 2 的 etc_compare_tri 三分裁决      *)
(*   收拢到 Eq 支（cec_cstar_tail 等值证书装载），Lt/Gt 支排空。        *)
(* ============================================================ *)

Theorem pkc_w3_qface : forall k : nat, (5 <= k)%nat ->
  sigT (fun c : comparison =>
    match c with
    | Lt => Id false true
    | Eq => QeqT (cec_cstar k) (1 + 1)%Q
    | Gt => Id false true
    end).
Proof.
  intros k Hk.
  assert (Ht : (cec_cstar k == 1 + 1)%Q) by (apply cec_cstar_tail; exact Hk).
  destruct (etc_compare_tri (cec_cstar k) (1 + 1)) as [c Hc]; destruct c.
  - (* etc Eq 支＝等值证书：W3 常数面 Eq 支装载 *)
    exists Eq. exact Hc.
  - (* etc Lt 支＝c*(k) ＜ 2，与尾段等值证书矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : ((1 + 1) < (1 + 1))%Q) by exact (pkc_qeq_lt_l _ _ _ Ht Hc).
    destruct (Qlt_irrefl (1 + 1)%Q Hcc).
  - (* etc Gt 支＝2 ＜ c*(k)，与尾段等值证书矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : ((1 + 1) < (1 + 1))%Q) by exact (etc_qeq_lt_r _ _ _ Ht Hc).
    destruct (Qlt_irrefl (1 + 1)%Q Hcc).
Defined.

(* ============================================================ *)
(* §5 提取探针（G3）：三分标签可计算、证明面擦除                       *)
(* ============================================================ *)

Definition pkc_pack_sign (p q : Real) (Hpq : real_lt q p)
  (n : nat) (Hn : NatLe (projT1 (pkc_sign_load p q Hpq)) n) : comparison :=
  projT1 (projT2 (pkc_sign_load p q Hpq) n Hn).

Definition pkc_pack_far (t : Real) (H : real_lt real_one t)
  (n : nat) (Hn : NatLe (projT1 (pkc_oneside_far_load t H)) n) : comparison :=
  projT1 (projT2 (pkc_oneside_far_load t H) n Hn).

Definition pkc_pack_near (t : Real) (H : real_lt t real_one)
  (n : nat) (Hn : NatLe (projT1 (pkc_oneside_near_load t H)) n) : comparison :=
  projT1 (projT2 (pkc_oneside_near_load t H) n Hn).

Definition pkc_pack_w3 (k : nat) (Hk : (5 <= k)%nat) : comparison :=
  projT1 (pkc_w3_qface k Hk).

Extraction "pkc13_out" pkc_pack_sign pkc_pack_far pkc_pack_near pkc_pack_w3
  pkc_half_lt.

(* ============================================================ *)
(* 公理面审计（G4 前置）                                              *)
(* ============================================================ *)
Print Assumptions pkc_sign_load.
Print Assumptions pkc_half_slack_load.
Print Assumptions pkc_oneside_far_load.
Print Assumptions pkc_oneside_near_load.
Print Assumptions pkc_w3_qface.
Print Assumptions pkc_half_lt.
Print Assumptions pkc_one_proj.

(* ============================================================ *)
(* 诚实边界登记（交付时同步入报告，不落语句面）                        *)
(*   ① 常数 2 完整形（kl₂ ≥ 2·TV²）未交付：其 S1 近支/S2 二阶级数核    *)
(*      本体需真二阶 log 引擎（W2 尾残差/交替级数截断环），库内在盘     *)
(*      引擎（上切线核+镜像切线+fracsum 合流）信息论上限为常数 1       *)
(*      （UpReqPinskerCore 头注 :26 与 :2448-2450 数值定谳同源），     *)
(*   ② S1 近支 log 本体（log(1+t) ≥ t−t²/2 于 t∈[0,1]）未交付：        *)
(*      库内 grep 无该引擎件（R6 头注 :989 提及的 pnk_log1p_ge_far     *)
(*      仅存在于注释，无定理本体）；§3 交付其判分装载面。              *)
(*   ③ W3 桥 pnk_pinsker_trunc5 不在盘（grep 实证）；§4 交付其 Q 层    *)
(*      常数比较面（cec_cstar 尾段 Eq 支收拢）。                       *)
(* ============================================================ *)
