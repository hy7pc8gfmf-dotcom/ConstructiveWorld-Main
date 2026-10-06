(* ===================================================================== *)
(*  abl_e_irrational2.v —— e 无理性第二段施工（层1+层2 连体首装）        *)
(*  【命名注记】eir_ 前缀与 abl_e_irrational 模块名位已被在册同名件占用     *)
(*  （在册占用勘定在卷），依「勘后共用或分池自建」命名纪律                *)
(*  分池 e_irr2/，前缀 eir2_，模块名 abl_e_irrational2。本件与 eir_ 件的   *)
(*  Stdlib-only 路线互补：本件使用生态契面 S01/S02（QeqT/QltT/NatLe/And   *)
(*  Set 面），语句面与 π 塔 LW0PiIrrational 主定理形态逐位同构。           *)
(*  模块名：abl_e_irrational2.                                            *)
(*  使命: e 无理性三塔纲领第二座的整性矛盾核（Fourier 1815 构造性核）      *)
(*    层1 级数构造面——eir2_q_fact（Q 层真 Fixpoint 阶乘，正性面+值等于    *)
(*      Z.of_nat(fact n) 的 Qeq 面）＋eir2_s（部分和真 Fixpoint，递推/    *)
(*      正性/单调）＋整性面：eir2_s_fact_int——n!·s_n 恒有显式整数见证     *)
(*      z（sigT 形，QeqT 语句面）；                                       *)
(*    层2 无理性矛盾核——给定 a:Z、b:nat（NatLe 1 b），取 n:=b，量        *)
(*      N:=b·n!·(a/b−s_n)（eir2_core_qty，显式可计算）的不可满足见证形：  *)
(*      N==(z#1) 为整数且 0<N<1（eir2_kernel_witness，sigT×2+And 链），   *)
(*      并收网为矛盾核 eir2_irrational_core : False——经典「b·n!·(e−s_n)  *)
(*      为正整数且落于 (0,1)」论证的零实数对象 Q 层闭合：「e=a/b」以两支  *)
(*      Q 序假设 eir2_hyp（Set 结构参数化位，层3 实层供）进入。            *)
(*  新数学: ①核语句新形——经典论证的「正整数落于 (0,1/b)」改铸为 Set 层    *)
(*    双 sigT 显式见证链 {n & {z & NatLe 1 n ∧ QeqT(N,z#1) ∧ 0<z#1 ∧     *)
(*    z#1<1}}，N:=b·n!·(a/b−s_n) 全程可计算（提取为 OCaml 整数程序）；    *)
(*    ②整除结构消解——经典论证需 b∣n!（n 取 b 倍数），本件以               *)
(*    eir2_s_fact_int（n!·s_n ∈ Z 对一切 n 归纳成立）＋b 因子一次外拉     *)
(*    （b·(n!·s_n) 型）把整除前提整型化为零前提——b∤n! 情形亦闭合，       *)
(*    强于经典陈述的消解点（「0<N<1/b」亦无损弱化为「0<N<1」，正整数      *)
(*    落 (0,1) 已足矛盾）；③层1 整性见证递归构造——n:=S k 步              *)
(*    fact(S k)·s(S k) = (S k)·(fact k·s k) + fact(S k)·(1/fact(S k))     *)
(*    = (S k)·z_k + 1 的 Qeq 链（Qmult_assoc/Qmult_comp/                  *)
(*    Qmult_plus_distr_r）＋Q 倒数自乘核 eir2_qdiv_mul_inv（QDen 分母位   *)
(*    positive 组件化后 lia 直证，零 Qinv/零 Qmult_inv_r 依赖）。          *)
(*  依赖: Stdlib QArith/Arith.Arith/Arith.Factorial(fact 面)/Lia/Setoid；  *)
(*    生态塔 S01_BaseRing（And/Id/NatLe Set 面）＋S02_CauchyComplete     *)
(*    （QeqT/QltT 面、qltT_0_1、qeq_imp_qeqT/qeqT_imp_qeq/qeq_imp_qle）   *)
(*    ——vo_local_world_unified_0930 编译缓存只读使用。                    *)
(*  对标: Fourier 1815/1826 e 无理性证明的构造性核；π 塔 LW0PiIrrational  *)
(*    主定理陈述形态（sigT+And+QltT，#187 Live 13830 行）为层3 接口样板；  *)
(*    ln2 塔 abl_ln2_integmachine_bridge 的假设消解纪律（零前提重述）。    *)
(*  构造性: 纯构造性、零公理/零承认件；语句面全 Set（sigT/And（S01 积）/  *)
(*    QeqT/QltT（S02 单态叶）/NatLe（S01 判定），零 Prop 载体位）；载体面  *)
(*    全 Set（Q/nat/Z）；Prop 面（Qlt/Qeq/<=）仅证体内作推理使用、经      *)
(*    Qlt_to_QltT/qeq_imp_qeqT/NatLe_lift 吸收入语句面；新立假设位=0      *)
(*    （eir2_hyp 为 Set 结构参数化位，层3 供件）；两个真 Fixpoint         *)
(*    （eir2_q_fact/eir2_s）＋多归纳构造非平凡；文尾 Print Assumptions    *)
(*    全 Closed＋Separate Extraction 独立提取验证。                        *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&     *)
(*    ulimit -s 65532 && nice -19 rocq c -native-compiler no              *)
(*    -Q <vo_local_world_unified_0930> "" -Q . "" abl_e_irrational2.v     *)
(*    （cwd=本池 e_irr2/；道闸≤1 单件串行）。                             *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia Setoid.
From Stdlib Require Import Arith.Factorial.

(* ============================================================ *)
(* §0 Z↔Q 边界与 Q 序运算件（Prop 体内推理，语句面 Set 闭合）   *)
(* ============================================================ *)

(* 单分母 Q 的序判读：z#1 的正性/小于 1 往返 Z 层 lia *)
Lemma eir2_zq_pos_of : forall z : Z, (0 < z)%Z -> QltT 0 (z#1).
Proof.
  intros z Hz.
  apply Qlt_to_QltT.
  unfold Qlt. cbn [Qnum Qden].
  lia.
Qed.

Lemma eir2_zq_qpos : forall z : Z, QltT 0 (z#1) -> (0 < z)%Z.
Proof.
  intros z H.
  apply QltT_to_Qlt in H.
  unfold Qlt in H. cbn [Qnum Qden] in H.
  lia.
Qed.

Lemma eir2_zq_qlt : forall z : Z, QltT (z#1) 1 -> (z < 1)%Z.
Proof.
  intros z H.
  apply QltT_to_Qlt in H.
  unfold Qlt in H. cbn [Qnum Qden] in H.
  lia.
Qed.

(* Qeq 在 Z 单分母上的三则（分量展开 lia 直证） *)
Lemma eir2_zq_zq_plus : forall u v : Z, Qeq ((u#1) + (v#1)) ((u+v)#1).
Proof.
  intros u v. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma eir2_zq_zq_mult : forall u v : Z, Qeq ((u#1) * (v#1)) ((u*v)#1).
Proof.
  intros u v. unfold Qeq, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* 带消缩放核：w≠0 时 ((w#1)·(v#1))·(c/w) == (v·c)#1（Qinv 三分组件化，   *)
(* 分母 positive 化后 lia 直证——F·(a/b) 型消去核）                        *)
Lemma eir2_qscale_div : forall v c w : Z, w <> 0%Z ->
  Qeq (((w#1) * (v#1)) * ((c#1) / (w#1))%Q) ((v*c)#1).
Proof.
  intros v c w Hw.
  destruct w as [| p | p].
  - exfalso. apply Hw. reflexivity.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
Qed.

(* 倒数保正：0 < x -> 0 < 1/x（Qinv 按 Qnum 三分，组件化 lia/nia） *)
Lemma eir2_qdiv_pos : forall x : Q, QltT 0 x -> QltT 0 ((1#1) / x).
Proof.
  intros [xn xd] Hx.
  apply QltT_to_Qlt in Hx.
  destruct xn as [| p | p].
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    exfalso. lia.
  - apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r.
    exfalso. nia.
Qed.

(* 正×正保正（乘法）：分量展开 nia 直证 *)
Lemma eir2_qmult_pos : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x * y).
Proof.
  intros [xn xd] [yn yd] Hx Hy.
  apply QltT_to_Qlt in Hx. apply QltT_to_Qlt in Hy.
  unfold Qlt in Hx, Hy. cbn [Qnum Qden] in Hx, Hy.
  apply Qlt_to_QltT.
  unfold Qlt, Qmult. cbn [Qnum Qden].
  nia.
Qed.

(* 正×正保正（加法）：分量展开 nia 直证 *)
Lemma eir2_qplus_pos : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x + y).
Proof.
  intros [xn xd] [yn yd] Hx Hy.
  apply QltT_to_Qlt in Hx. apply QltT_to_Qlt in Hy.
  unfold Qlt in Hx, Hy. cbn [Qnum Qden] in Hx, Hy.
  apply Qlt_to_QltT.
  unfold Qlt, Qplus. cbn [Qnum Qden].
  nia.
Qed.

(* 乘负号分配（右）：分量展开 lia 直证 *)
Lemma eir2_qmult_opp_r : forall x y : Q, Qeq (x * (-y)) (-(x * y)).
Proof.
  intros [xn xd] [yn yd].
  unfold Qmult, Qopp, Qeq. cbn [Qnum Qden].
  lia.
Qed.

(* 倒数自乘核：z·(1/z) == 1（Qinv 按 Qnum 三分；零 Qmult_inv_r 依赖） *)
Lemma eir2_qdiv_mul_inv : forall z : Q, QltT 0 z -> Qeq (z * ((1#1) / z)) (1#1).
Proof.
  intros [xn xd] Hx.
  apply QltT_to_Qlt in Hx.
  destruct xn as [| p | p].
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    exfalso. lia.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos2Z.inj_mul, ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    exfalso. nia.
Qed.

(* QeqT 横向传递两支（经 S02 的 qeq_imp_qle，零 setoid 依赖） *)
Lemma eir2_qltT_eq_l : forall a a' b : Q, Qeq a a' -> QltT a' b -> QltT a b.
Proof.
  intros a a' b Ha H.
  exact (Qlt_to_QltT _ _
    (Qle_lt_trans a a' b (qeq_imp_qle a a' Ha) (QltT_to_Qlt _ _ H))).
Qed.

Lemma eir2_qltT_eq_r : forall a b b' : Q, Qeq b b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Hb Hab.
  exact (Qlt_to_QltT _ _
    (Qlt_le_trans a b b' (QltT_to_Qlt _ _ Hab) (qeq_imp_qle b b' Hb))).
Qed.

(* 整性面（Set 层 sigT 见证）对加法/取负封闭 *)
Lemma eir2_intq_add : forall x y : Q,
  (sigT (fun z : Z => QeqT x (z#1))) ->
  (sigT (fun z : Z => QeqT y (z#1))) ->
  sigT (fun z : Z => QeqT (x + y) (z#1)).
Proof.
  intros x y [u Hu] [v Hv].
  exists (u + v)%Z.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ ((u#1) + (v#1))%Q _).
  - exact (Qplus_comp x (u#1) (qeqT_imp_qeq x (u#1) Hu)
                   y (v#1) (qeqT_imp_qeq y (v#1) Hv)).
  - apply eir2_zq_zq_plus.
Qed.

Lemma eir2_intq_opp : forall x : Q,
  (sigT (fun z : Z => QeqT x (z#1))) ->
  sigT (fun z : Z => QeqT (- x) (z#1)).
Proof.
  intros x [z Hz].
  exists (- z)%Z.
  apply qeq_imp_qeqT.
  apply (Qopp_comp x (z#1) (qeqT_imp_qeq x (z#1) Hz)).
Qed.

(* ============================================================ *)
(* §1 层1·阶乘面：Q 层真 Fixpoint + 正性 + 值面                 *)
(* ============================================================ *)

Fixpoint eir2_q_fact (n : nat) : Q :=
  match n with
  | Datatypes.O => 1#1
  | Datatypes.S k => ((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k
  end.

Lemma eir2_q_fact_pos : forall n : nat, QltT 0 (eir2_q_fact n).
Proof.
  induction n as [| k IH].
  - exact qltT_0_1.
  - cbn [eir2_q_fact].
    apply eir2_qmult_pos.
    + apply eir2_zq_pos_of. lia.
    + exact IH.
Qed.

Lemma eir2_q_fact_val : forall n : nat, Qeq (eir2_q_fact n) ((Z.of_nat (fact n))#1).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - cbn [eir2_q_fact].
    apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) * ((Z.of_nat (fact k))#1))%Q _).
    + exact (Qmult_comp ((Z.of_nat (Datatypes.S k))#1) ((Z.of_nat (Datatypes.S k))#1)
                        (Qeq_refl ((Z.of_nat (Datatypes.S k))#1))
                        (eir2_q_fact k) ((Z.of_nat (fact k))#1) IH).
    + change (fact (Datatypes.S k)) with (Datatypes.S k * fact k)%nat.
      rewrite Nat2Z.inj_mul.
      apply eir2_zq_zq_mult.
Qed.

(* ============================================================ *)
(* §2 层1·级数面：部分和真 Fixpoint + 递推 + 正性 + 单调        *)
(* ============================================================ *)

Definition eir2_term (n : nat) : Q := (1#1) / eir2_q_fact n.

Fixpoint eir2_s (n : nat) : Q :=
  match n with
  | Datatypes.O => 1#1
  | Datatypes.S k => eir2_s k + eir2_term (Datatypes.S k)
  end.

Lemma eir2_s_step : forall n : nat,
  QeqT (eir2_s (Datatypes.S n)) (eir2_s n + eir2_term (Datatypes.S n)).
Proof.
  intro n.
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* 项正性：1/fact(n) > 0（经倒数保正件） *)
Lemma eir2_term_pos : forall n : nat, QltT 0 (eir2_term n).
Proof.
  intro n.
  apply eir2_qdiv_pos.
  apply eir2_q_fact_pos.
Qed.

Lemma eir2_s_pos : forall n : nat, QltT 0 (eir2_s n).
Proof.
  induction n as [| k IH].
  - exact qltT_0_1.
  - cbn [eir2_s].
    apply eir2_qplus_pos.
    + exact IH.
    + apply eir2_term_pos.
Qed.

Lemma eir2_s_mono : forall n : nat, QltT (eir2_s n) (eir2_s (Datatypes.S n)).
Proof.
  intro n.
  apply Qlt_to_QltT.
  assert (H : Qlt (eir2_s n + 0) (eir2_s n + eir2_term (Datatypes.S n))).
  { apply (proj2 (Qplus_lt_r 0 (eir2_term (Datatypes.S n)) (eir2_s n))).
    apply QltT_to_Qlt. apply eir2_term_pos. }
  rewrite Qplus_0_r in H.
  exact H.
Qed.

(* ============================================================ *)
(* §3 层1·整性面：n!·s_n 的显式整数见证（sigT 形，归纳构造）    *)
(* ============================================================ *)

Theorem eir2_s_fact_int :
  forall n : nat, sigT (fun z : Z => QeqT (eir2_q_fact n * eir2_s n) (z#1)).
Proof.
  induction n as [| k [z0 IH]].
  - exists 1%Z.
    apply qeq_imp_qeqT.
    reflexivity.
  - exists (Z.of_nat (Datatypes.S k) * z0 + 1)%Z.
    cbn [eir2_q_fact eir2_s].
    unfold eir2_term. cbn [eir2_q_fact].
    assert (Hz0q : Qeq (eir2_q_fact k * eir2_s k) (z0#1))
      by (apply qeqT_imp_qeq; exact IH).
    assert (H1 : Qeq ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * eir2_s k)
                      (((Z.of_nat (Datatypes.S k)) * z0)#1)).
    { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) *
                          (eir2_q_fact k * eir2_s k))%Q _).
      - exact (Qeq_sym _ _ (Qmult_assoc ((Z.of_nat (Datatypes.S k))#1)
                           (eir2_q_fact k) (eir2_s k))).
      - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) * (z0#1))%Q _).
        + exact (Qmult_comp ((Z.of_nat (Datatypes.S k))#1) ((Z.of_nat (Datatypes.S k))#1)
                   (Qeq_refl ((Z.of_nat (Datatypes.S k))#1))
                   (eir2_q_fact k * eir2_s k) (z0#1) Hz0q).
        + apply eir2_zq_zq_mult. }
    assert (H2 : Qeq ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) *
                      ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k)))
                      (1#1)).
    { apply eir2_qdiv_mul_inv.
      apply eir2_qmult_pos.
      - apply eir2_zq_pos_of. lia.
      - apply eir2_q_fact_pos. }
    apply qeq_imp_qeqT.
    apply (Qeq_trans _
             (((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * eir2_s k) +
               ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k))))%Q _).
    + exact (Qmult_plus_distr_r
               (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k)
               (eir2_s k)
               ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k))).
    + apply (Qeq_trans _ (Qplus ((Z.of_nat (Datatypes.S k) * z0)#1) 1)%Q _).
      * exact (Qplus_comp _ _ H1 _ _ H2).
      * apply eir2_zq_zq_plus.
Qed.

(* ============================================================ *)
(* §4 层2·整性矛盾核：eir2_hyp 参数化位 + 显式见证 + 收网       *)
(* ============================================================ *)

(* 间隙 g_n := a/b − s_n（假设位供其两支序；a/b 以 Qdiv 除式表示） *)
Definition eir2_gap (a : Z) (b n : nat) : Q :=
  (((a#1) / ((Z.of_nat b)#1))%Q - eir2_s n)%Q.

(* 核量 N_{a,b,n} := n'·n!·(a/b − s_n)，n' := Z.of_nat n —— 取 n:=b 时   *)
(* 即为经典量 b·b!·(a/b−s_b)（n' 因子由 n:=b 一步到位）                   *)
Definition eir2_core_qty (a : Z) (b n : nat) : Q :=
  ((Z.of_nat n)#1) * eir2_q_fact n * eir2_gap a b n.

(* 假设位（Set 结构参数化）：n≥1 时 0 < a/b−s_n < 1/(n·n!)——层3 实层供 *)
Definition eir2_hyp (a : Z) (b : nat) : Set :=
  forall n : nat, NatLe 1 n ->
    And (QltT 0 (eir2_gap a b n))
        (QltT (eir2_gap a b n)
              ((1#1) / (((Z.of_nat n)#1) * eir2_q_fact n))).

(* 显式见证形：n:=b，N:=b·b!·(a/b−s_b) 有整数见证 z 且 0<z#1<1 *)
Theorem eir2_kernel_witness : forall (a : Z) (b : nat), NatLe 1 b -> eir2_hyp a b ->
  sigT (fun n : nat => sigT (fun z : Z =>
    And (NatLe 1 n)
    (And (QeqT (eir2_core_qty a b n) (z#1))
    (And (QltT 0 (z#1)) (QltT (z#1) 1))))).
Proof.
  intros a b Hb H.
  exists b.
  destruct (H b Hb) as [Hpos Hupper].
  assert (HF : QltT 0 (((Z.of_nat b)#1) * eir2_q_fact b)).
  { apply eir2_qmult_pos.
    - apply eir2_zq_pos_of.
      pose proof (NatLe_drop 1 b Hb). lia.
    - apply eir2_q_fact_pos. }
  assert (Hqty_pos : QltT 0 (eir2_core_qty a b b)).
  { unfold eir2_core_qty.
    apply eir2_qmult_pos; assumption. }
  assert (Hqty_lt : QltT (eir2_core_qty a b b) 1).
  { unfold eir2_core_qty.
    apply (eir2_qltT_eq_r _
             ((((Z.of_nat b)#1) * eir2_q_fact b) *
              ((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b)))%Q 1%Q).
    - apply eir2_qdiv_mul_inv. exact HF.
    - apply Qlt_to_QltT.
      rewrite (Qmult_comm (((Z.of_nat b)#1) * eir2_q_fact b) (eir2_gap a b b)).
      rewrite (Qmult_comm (((Z.of_nat b)#1) * eir2_q_fact b)
                           (((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b))%Q)).
      apply (Qmult_lt_compat_r (eir2_gap a b b)
               (((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b))%Q)
               (((Z.of_nat b)#1) * eir2_q_fact b)).
      + exact (QltT_to_Qlt _ _ HF).
      + exact (QltT_to_Qlt _ _ Hupper). }
  assert (Hqty_int : sigT (fun z : Z =>
    QeqT (((Z.of_nat b)#1) * eir2_q_fact b * eir2_gap a b b) (z#1))).
  { destruct (eir2_s_fact_int b) as [z0 Hz0].
    assert (Hz0q : Qeq (eir2_q_fact b * eir2_s b) (z0#1))
      by (apply qeqT_imp_qeq; exact Hz0).
    assert (Hw0 : (Z.of_nat b <> 0)%Z).
    { pose proof (NatLe_drop 1 b Hb). lia. }
    exists ((Z.of_nat (fact b) * a) - Z.of_nat b * z0)%Z.
    unfold eir2_core_qty, eir2_gap.
    assert (H1 : Qeq (((Z.of_nat b)#1) * eir2_q_fact b *
                      (((a#1) / ((Z.of_nat b)#1))%Q))
                      ((Z.of_nat (fact b) * a)#1)).
    { apply (Qeq_trans _ (((Z.of_nat b)#1) * ((Z.of_nat (fact b))#1) *
                          (((a#1) / ((Z.of_nat b)#1))%Q))%Q _).
      - exact (Qmult_comp
                 (((Z.of_nat b)#1) * eir2_q_fact b)
                 (((Z.of_nat b)#1) * ((Z.of_nat (fact b))#1))
                 (Qmult_comp ((Z.of_nat b)#1) ((Z.of_nat b)#1)
                    (Qeq_refl ((Z.of_nat b)#1))
                    (eir2_q_fact b) ((Z.of_nat (fact b))#1) (eir2_q_fact_val b))
                 (((a#1) / ((Z.of_nat b)#1))%Q)
                 (((a#1) / ((Z.of_nat b)#1))%Q)
                 (Qeq_refl (((a#1) / ((Z.of_nat b)#1))%Q))).
      - exact (eir2_qscale_div (Z.of_nat (fact b)) a (Z.of_nat b) Hw0). }
    assert (H2 : Qeq (((Z.of_nat b)#1) * eir2_q_fact b * (-(eir2_s b)))
                      ((- (Z.of_nat b * z0))#1)).
    { apply (Qeq_trans _
               (- (((Z.of_nat b)#1) * eir2_q_fact b * eir2_s b))%Q _).
      - apply eir2_qmult_opp_r.
      - assert (HFz : Qeq (((Z.of_nat b)#1) * eir2_q_fact b * eir2_s b)
                           ((Z.of_nat b * z0)#1)).
        { apply (Qeq_trans _ (((Z.of_nat b)#1) *
                              (eir2_q_fact b * eir2_s b))%Q _).
          - exact (Qeq_sym _ _ (Qmult_assoc ((Z.of_nat b)#1) (eir2_q_fact b) (eir2_s b))).
          - apply (Qeq_trans _ (((Z.of_nat b)#1) * (z0#1))%Q _).
            + exact (Qmult_comp ((Z.of_nat b)#1) ((Z.of_nat b)#1)
                       (Qeq_refl ((Z.of_nat b)#1))
                       (eir2_q_fact b * eir2_s b) (z0#1) Hz0q).
            + apply eir2_zq_zq_mult. }
        exact (Qopp_comp _ _ HFz). }
    apply qeq_imp_qeqT.
    apply (Qeq_trans _
             ((((Z.of_nat b)#1) * eir2_q_fact b) *
              (((a#1) / ((Z.of_nat b)#1))%Q) +
              (((Z.of_nat b)#1) * eir2_q_fact b) * (-(eir2_s b)))%Q _).
    + change ((((a#1) / ((Z.of_nat b)#1))%Q - eir2_s b)%Q)
        with ((((a#1) / ((Z.of_nat b)#1))%Q) + (-(eir2_s b)))%Q.
      exact (Qmult_plus_distr_r
               (((Z.of_nat b)#1) * eir2_q_fact b)
               (((a#1) / ((Z.of_nat b)#1))%Q) (-(eir2_s b))).
    + rewrite H1, H2.
      exact (eir2_zq_zq_plus
               (Z.of_nat (fact b) * a)
               (- (Z.of_nat b * z0))). }
  destruct Hqty_int as [z Hz].
  exists z.
  split; [ exact Hb | ].
  split.
  - exact Hz.
  - split.
    + apply (eir2_qltT_eq_r 0 (eir2_core_qty a b b) (z#1)).
      * apply qeqT_imp_qeq. exact Hz.
      * exact Hqty_pos.
    + apply (eir2_qltT_eq_l (z#1) (eir2_core_qty a b b) 1).
      * apply Qeq_sym. apply qeqT_imp_qeq. exact Hz.
      * exact Hqty_lt.
Qed.

(* 收网矛盾核：正整数落于 (0,1) 不可能——经典 e 无理性核 *)
Theorem eir2_irrational_core : forall (a : Z) (b : nat), NatLe 1 b -> eir2_hyp a b -> False.
Proof.
  intros a b Hb H.
  destruct (eir2_kernel_witness a b Hb H) as [n [z [_ [Heq [Hz0 Hz1]]]]].
  apply (eir2_zq_qpos z) in Hz0.
  apply (eir2_zq_qlt z) in Hz1.
  lia.
Qed.

(* ============================================================ *)
(* 取证块：Print Assumptions + Separate Extraction              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction eir2_q_fact eir2_s eir2_core_qty eir2_s_fact_int.

Print Assumptions eir2_q_fact_pos.
Print Assumptions eir2_q_fact_val.
Print Assumptions eir2_term_pos.
Print Assumptions eir2_s_pos.
Print Assumptions eir2_s_mono.
Print Assumptions eir2_s_fact_int.
Print Assumptions eir2_kernel_witness.
Print Assumptions eir2_irrational_core.
