(* ===================================================================== *)
(* abl_niven_isomorphism —— 三塔同构：Niven–Hermite 五段式无理性证明的       *)
(*   形式化抽象机器与两实例化装配件                                          *)
(*                                                                        *)
(* 使命: 形式化 π 塔与 ln2 塔两座无理性证明共有的五段式结构                 *)
(*   首次形式化为单一可复用机器：①积分表示（隙族的表示律）②锐权接口        *)
(*   （上/下界成对夹逼）③抽象整性（q 吸收传递引理）④极限分离器              *)
(*   （整数落入 (0,1) 的构造性否证机器）⑤无理性结论面（Set 载体重述：        *)
(*   有理见证 → 空型）。塔构造子 TowerBuilder 以型级接口承载                *)
(*   「权函数对+整性凭证 → 分离器」；ln2 塔实例绑定 Beukers 变体残差族      *)
(*   （q̃_n·tgt − p_n）并经吸收引理与 lcm 缩放双见证供给条件整性；           *)
(*   π 塔实例绑定 Niven 多项式核的缩放 Hermite 和族（端点项与节点项双端     *)
(*   分裂，b^n·n! 缩放），其整性面由构造显式闭合。两塔阶段对阶段的 Set 面    *)
(*   对应定理三则：表示律同形（niv_iso_stage1）、两条消解路线汇入同一        *)
(*   缩放整性槽（niv_iso_stage3）、同一矛盾门双塔实例化消解（niv_iso_exit_pair）。*)
(*   e 塔以类型级接口占位：接口与塔构造子可证重合，实例化义务（a+b·e        *)
(*   线性耦合与阶乘衰减凭证）留待 e 塔支线供给。                             *)
(*                                                                        *)
(* 依赖: Stdlib QArith/Qring/Qfield/List/Arith/Arith.Factorial/            *)
(*   ZArith/Lia/Extraction + S01_BaseRing（Set 层 Id 与 And 积载体）+        *)
(*   S02_CauchyComplete（QeqT/QleT'/QltT 与桥）+ S03_QExp（q_pow/sum_upto）  *)
(*   + HansonLcm（hl_lcm_upto/hl_binom）+ BeukersLists（bk_Qn_qtilde）+      *)
(*   BeukersVariant（bv_p）+ Ln2Integrality（lni_qlcm_int）+                 *)
(*   abl_qpoly_divmod / abl_qpoly_divmod_gen / abl_ln2_numer_int             *)
(*   （lni_bvp_lcm_int）+ abl_ln2_qpoly_consume + abl_ln2_tail_bound         *)
(*   （lnt_pterm）+ abl_ln2_sharp_weight（lnw_wterm 两侧面/lnw_wgap_geo）     *)
(*   + abl_niven_hermite_skeleton（nhs_int_gap_gate 矛盾门）。               *)
(*                                                                        *)
(* 对标: C. Hermite, C. R. Acad. Sci. Paris 77 (1873)（插值恒等式与        *)
(*   双端和结构）；I. Niven, Bull. Amer. Math. Soc. 53 (1947)（π 无理性     *)
(*   五段式原型：核多项式、端点导数整性、积分夹逼）；F. Beukers (1980)       *)
(*   （ln2 二重积分核与缩放残差，工程注册引用未在线复核）。                  *)
(*                                                                        *)
(* 构造性: 零公理零承认零经典。语句面全部 Set 载体形（Id/sigT/              *)
(*   And:=A*B 积）；Prop 层仅出现在证内脚手架（Qeq 降档桥与 Z 域 lia 叶位）。*)
(*   缩放整性槽谓词取条件形：隙族整性以「目标的有理见证」为前提，正性与      *)
(*   夹逼面无条件成立；ln2 塔与 π 塔的 ②④ 槽实例化凭证（隙族真值的锐权      *)
(*   包络与衰减实估计）属各自解析面，为两塔支线的下游义务，本件供其         *)
(*   ①③ 槽面、容器侧供面与全部对应定理。                                   *)
(*                                                                        *)
(* 编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532；两根挂载：-Q vo_local_world_unified_0930 "" -Q . ""；  *)
(*   链序：abl_qpoly_divmod → abl_qpoly_divmod_gen → abl_ln2_numer_int →     *)
(*   abl_ln2_qpoly_consume → abl_ln2_tail_bound → abl_ln2_sharp_weight       *)
(*   → abl_niven_hermite_skeleton → 本件；配方 nice -19 rocq c               *)
(*   -native-compiler no <两根> <件>.v。                                    *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith Arith.Factorial ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm BeukersLists BeukersVariant Ln2Integrality.
Require Import abl_qpoly_divmod abl_qpoly_divmod_gen.
Require Import abl_ln2_numer_int abl_ln2_qpoly_consume.
Require Import abl_ln2_tail_bound abl_ln2_sharp_weight.
Require Import abl_niven_hermite_skeleton.

(* ------------------------------------------------------------------ *)
(* §1 ⑤段结论面载体：有理见证与无理性面（Set 重述）                       *)
(*    目标的有理见证 = 分子/分母对及其相等凭证；无理性面 = 见证到空型      *)
(*    的函数（Id false true 为 Set 层空型），二者皆 Set 载体、零 Prop 面。 *)
(* ------------------------------------------------------------------ *)

Definition niv_rat_wit (tgt : Q) : Set :=
  sigT (fun p : Z => sigT (fun q : positive => QeqT tgt ((p # q)%Q))).

Definition niv_irr_face (tgt : Q) : Set := niv_rat_wit tgt -> Id false true.

(* ------------------------------------------------------------------ *)
(* §2 阶段③辅助：z # 1 的 Q 除法代数                                     *)
(* ------------------------------------------------------------------ *)

Lemma niv_qmul_div_z1 : forall (z w : Z), z <> 0%Z ->
  ((z # 1) * ((w # 1) / (z # 1)))%Q == ((w # 1)%Q).
Proof.
  intros z w Hz.
  assert (Hzq : (~ ((z # 1)%Q == 0%Q))).
  { intro He. apply Hz. destruct z as [z0|zp|zn].
    - reflexivity.
    - unfold Qeq in He. cbn [Qnum Qden] in He. lia.
    - unfold Qeq in He. cbn [Qnum Qden] in He. lia. }
  unfold Qdiv.
  rewrite Qmult_assoc.
  rewrite (Qmult_comm ((z # 1)%Q * (w # 1)%Q) (Qinv (z # 1)%Q)).
  rewrite Qmult_assoc.
  rewrite (Qmult_comm (Qinv (z # 1)%Q) (z # 1)%Q).
  rewrite (Qmult_inv_r (z # 1)%Q Hzq).
  rewrite Qmult_1_l. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* §3 阶段③主引理：q 吸收缩放整性传递（可复用整性引理·抽象条件）           *)
(*    隙族呈 A_n + B_n·tgt 两项式、且 L_n·A_n 与 L_n·B_n 各有整数见证时，  *)
(*    取缩放 q·L_n（q 为目标有理见证之分母），则 q·L_n·I_n 有整数见证。    *)
(*    这是 ln2 塔整性凭证的标准供给路线；见证元 za+q'zb 为显式构造。        *)
(* ------------------------------------------------------------------ *)

Theorem niv_int_absorb : forall (tgt : Q) (p : Z) (q : positive),
  QeqT tgt ((p # q)%Q) ->
  forall (L : nat -> Z) (ann bnn irep : nat -> Q),
  (forall n : nat, sigT (fun z : Z => QeqT ((L n # 1)%Q * ann n)%Q ((z # 1)%Q))) ->
  (forall n : nat, sigT (fun z : Z => QeqT ((L n # 1)%Q * bnn n)%Q ((z # 1)%Q))) ->
  (forall n : nat, QeqT (irep n) (ann n + bnn n * tgt)%Q) ->
  forall n : nat,
    sigT (fun z : Z =>
      QeqT (((Z.pos q * L n) # 1)%Q * irep n)%Q ((z # 1)%Q)).
Proof.
  intros tgt p q Htgt L ann bnn irep Ha Hb Hrep n.
  destruct (Ha n) as [za Ha'].
  destruct (Hb n) as [zb Hb'].
  exists (Z.pos q * za + p * zb)%Z.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (Hrep n)).
  transitivity (((Z.pos q * L n) # 1)%Q * ann n
                + ((Z.pos q * L n) # 1)%Q * (bnn n * tgt))%Q.
  - ring.
  - assert (E1 : ((Z.pos q * L n) # 1)%Q * ann n == ((Z.pos q * za) # 1)%Q).
    { rewrite <- lni_QmulZ. rewrite <- Qmult_assoc.
      rewrite (qeqT_imp_qeq _ _ Ha').
      rewrite lni_QmulZ. reflexivity. }
    assert (E2 : ((Z.pos q * L n) # 1)%Q * (bnn n * tgt) == ((p * zb) # 1)%Q).
    { rewrite <- lni_QmulZ. rewrite <- Qmult_assoc.
      rewrite (Qmult_assoc (L n # 1)%Q (bnn n) tgt).
      rewrite (qeqT_imp_qeq _ _ Hb').
      rewrite (qeqT_imp_qeq _ _ Htgt).
      unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring. }
    transitivity ((((Z.pos q * za) # 1) + ((p * zb) # 1))%Q).
    + rewrite E1. rewrite E2.
      unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring.
    + unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* §4 塔构造子：五槽束类型 + 机器 Section + 分离器                         *)
(*    ①积分表示槽 irep（隙族）；②锐权对 wlo/whi（成对夹逼，下界锐正）；    *)
(*    ③整性缩放族 D 与条件整性凭证；④衰减凭证（上权被缩放压到 1 之下）；   *)
(*    ⑤出口 = 无理性面。阶段②的隙正性与成对相干由夹逼非平凡推出。          *)
(* ------------------------------------------------------------------ *)

Definition niv_slots (tgt : Q) (W : niv_rat_wit tgt)
  (irep wlo whi : nat -> Q) (D : nat -> Z) : Set :=
  And (forall n : nat, QltT 0 (wlo n))
    (And (forall n : nat, QleT' (wlo n) (irep n))
    (And (forall n : nat, QleT' (irep n) (whi n))
    (And (forall n : nat, QltT 0 ((D n # 1)%Q))
    (And (forall n : nat,
            sigT (fun z : Z => QeqT ((D n # 1)%Q * irep n)%Q ((z # 1)%Q)))
         (forall n : nat,
            sigT (fun B : Q => And (QltT ((D n # 1)%Q * B)%Q 1%Q)
                                   (QleT' (whi n) B))))))).

Section NivenTowerMachine.

  Variable tgt : Q.
  Variable irep wlo whi : nat -> Q.
  Variable D : nat -> Z.

  Hypothesis hwlo_pos : forall n : nat, QltT 0 (wlo n).
  Hypothesis wsand_lo : forall n : nat, QleT' (wlo n) (irep n).
  Hypothesis wsand_hi : forall n : nat, QleT' (irep n) (whi n).
  Hypothesis hD_pos : forall n : nat, QltT 0 ((D n # 1)%Q).
  Hypothesis hint_w : niv_rat_wit tgt ->
    forall n : nat,
      sigT (fun z : Z => QeqT ((D n # 1)%Q * irep n)%Q ((z # 1)%Q)).
  Hypothesis hvan : niv_rat_wit tgt ->
    forall n : nat,
      sigT (fun B : Q => And (QltT ((D n # 1)%Q * B)%Q 1%Q)
                             (QleT' (whi n) B)).

  (* 阶段②成对相干：锐权下界 ≤ 锐权上界（经隙族传递） *)
  Theorem tb_pair_cohere : forall n : nat, QleT' (wlo n) (whi n).
  Proof.
    intro n. apply (qleT'_trans (wlo n) (irep n) (whi n)).
    - apply wsand_lo.
    - apply wsand_hi.
  Qed.

  (* 阶段②推隙正性：0 < 锐权下界 ≤ 隙 ⟹ 0 < 隙（替代裸正性接口参数） *)
  Theorem tb_gap_pos : forall n : nat, QltT 0 (irep n).
  Proof.
    intro n. apply (qltT_leT'_ltT 0%Q (wlo n) (irep n)).
    - apply hwlo_pos.
    - apply wsand_lo.
  Qed.

  (* 阶段④缩放隙正性：正缩放×正隙 *)
  Theorem tb_scaled_pos : niv_rat_wit tgt ->
    forall n : nat, QltT 0 ((D n # 1)%Q * irep n)%Q.
  Proof.
    intros W n. apply qmult_ltT_0_compat.
    - apply hD_pos.
    - apply tb_gap_pos.
  Qed.

  (* 阶段④缩放隙严格小于 1：隙 ≤ 上权 ≤ B 与 D·B < 1 的合流 *)
  Theorem tb_scaled_lt1 : niv_rat_wit tgt ->
    forall n : nat, QltT ((D n # 1)%Q * irep n)%Q 1%Q.
  Proof.
    intros W n. destruct (hvan W n) as [B [HB1 HB2]].
    apply (qleT'_ltT_ltT ((D n # 1)%Q * irep n)%Q ((D n # 1)%Q * B)%Q 1%Q).
    - apply (qleT'_trans ((D n # 1)%Q * irep n)%Q ((D n # 1)%Q * whi n)%Q
                         ((D n # 1)%Q * B)%Q).
      + apply qleT'_mult_compat_l.
        * apply qltT_leT'. apply hD_pos.
        * apply wsand_hi.
      + apply qleT'_mult_compat_l.
        * apply qltT_leT'. apply hD_pos.
        * exact HB2.
    - exact HB1.
  Qed.

  (* 阶段④⑤分离器：缩放隙整数面落入 (0,1)，同一矛盾门实例化消解 *)
  Theorem tb_separator : niv_rat_wit tgt -> Id false true.
  Proof.
    intro W.
    destruct (hint_w W 0) as [z Hz].
    apply (nhs_int_gap_gate z).
    - pose proof (tb_scaled_pos W 0) as Hp.
      apply QltT_to_Qlt in Hp.
      rewrite (qeqT_imp_qeq _ _ Hz) in Hp.
      apply Qlt_to_QltT. exact Hp.
    - pose proof (tb_scaled_lt1 W 0) as Hl.
      apply QltT_to_Qlt in Hl.
      rewrite (qeqT_imp_qeq _ _ Hz) in Hl.
      apply Qlt_to_QltT. exact Hl.
  Qed.

End NivenTowerMachine.

(* 塔构造子闭形：权函数对+整性凭证 → 分离器（⑤段无理性面） *)
Definition TowerBuilder (tgt : Q) : Set :=
  forall (W : niv_rat_wit tgt) (irep wlo whi : nat -> Q) (D : nat -> Z),
    niv_slots tgt W irep wlo whi D -> niv_irr_face tgt.

Theorem tb_build : forall (tgt : Q) (W : niv_rat_wit tgt)
  (irep wlo whi : nat -> Q) (D : nat -> Z),
  niv_slots tgt W irep wlo whi D -> niv_irr_face tgt.
Proof.
  intros tgt W irep wlo whi D slots W'.
  destruct slots as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  exact (tb_separator tgt irep wlo whi D H1 H2 H3 H4
                      (fun _ : niv_rat_wit tgt => H5)
                      (fun _ : niv_rat_wit tgt => H6) W').
Qed.

(* ------------------------------------------------------------------ *)
(* §5 ln2 塔实例化（Beukers 变体）：①表示律 + ③条件整性 + 容器侧供面      *)
(*   隙族取经典缩放残差形 lnt_gap n = q̃_n·tgt − p_n（q̃_n := bk_Qn_qtilde， *)
(*   p_n := bv_p n）。条件整性双见证：L·q̃ ∈ Z（lni_qlcm_int）与            *)
(*   L·p ∈ Z（lni_bvp_lcm_int），经 §3 吸收引理闭合；缩放族取 q·L_n。      *)
(*   容器侧锐权对与几何尾预算作为 ②④ 槽供面重述（lnt_supply_*）。          *)
(* ------------------------------------------------------------------ *)

Section Ln2TowerInst.

  Variable tgt : Q.

  Definition lnt_gap (n : nat) : Q :=
    ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q * tgt + Qopp (bv_p n))%Q.

  (* ① 表示律：隙族呈两项式 ann + bnn·tgt（见证为显式族） *)
  Theorem lnt_gap_repr : sigT (fun ann : nat -> Q => sigT (fun bnn : nat -> Q =>
    forall n : nat, QeqT (lnt_gap n) ((ann n + bnn n * tgt)%Q))).
  Proof.
    exists (fun n : nat => Qopp (bv_p n)),
           (fun n : nat => (Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
    intro n. apply qeq_imp_qeqT. unfold lnt_gap. ring.
  Qed.

  (* ③ 条件整性：q 吸收缩放族 q·L_n 下隙族有整数见证（双见证+吸收引理） *)
  Theorem lnt_gap_int : forall (p : Z) (q : positive), QeqT tgt ((p # q)%Q) ->
    forall n : nat,
      sigT (fun z : Z =>
        QeqT (((Z.pos q * Z.of_nat (hl_lcm_upto n)) # 1)%Q * lnt_gap n)%Q
             ((z # 1)%Q)).
  Proof.
    intros p q Htgt n.
    apply (niv_int_absorb tgt p q Htgt
            (fun m : nat => Z.of_nat (hl_lcm_upto m))
            (fun m : nat => Qopp (bv_p m))
            (fun m : nat => (Z.of_nat (bk_Qn_qtilde m) # 1)%Q)
            lnt_gap).
    - intro m. destruct (lni_bvp_lcm_int m) as [z Hz].
      exists (Z.opp z). apply qeq_imp_qeqT.
      transitivity (Qopp ((Z.of_nat (hl_lcm_upto m) # 1)%Q * bv_p m))%Q.
      + ring.
      + transitivity (Qopp ((z # 1)%Q)).
        * apply lni_Qopp_cong. unfold lni_lbvp.
          exact (qeqT_imp_qeq _ _ Hz).
        * apply (lni_QoppZ z).
    - intro m. exact (lni_qlcm_int m).
    - intro m. apply qeq_imp_qeqT. unfold lnt_gap. ring.
  Qed.

End Ln2TowerInst.

(* ②④ 容器侧供面：锐权对（下界/上界成对夹逼单权项） *)
Theorem lnt_supply_pair : forall n k : nat,
  And (QltT 0 (lnw_wterm n k))
    (And (QleT' (lnt_pterm n k) (lnw_wterm n k))
         (QleT' (lnw_wterm n k) ((2 # 1)%Q * lnt_pterm n k)%Q)).
Proof.
  intros n k. split.
  - apply lnw_wterm_pos.
  - split.
    + apply lnw_wterm_ge.
    + apply lnw_wterm_le2.
Qed.

(* ②④ 容器侧供面：几何尾预算（权重和的截断加尾包络） *)
Theorem lnt_supply_tail : forall n M d : nat, 1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM. exact (lnw_wgap_geo n M d Hn HM).
Qed.

(* ------------------------------------------------------------------ *)
(* §6 π 塔实例化（Niven 核）：b^n·n! 缩放的 Hermite 双端和族               *)
(*   设 π = a/b。核 g(x) = x^n(a−bx)^n，F = Σ_j (−1)^j f^{(2j)} 满足       *)
(*   F''+F = f，故 ∫ f·sin = F(0)+F(π)（双端和结构）。本件以显式整族承载   *)
(*   缩放双端和 b^n·n!·I_n 的代出面：端点项 t0 = g^{(2j)}(0)（(2j)!·组合    *)
(*   数·a/b 幂，n ≤ 2j ≤ 2n 带内），节点项 t1 = b^n·g^{(2j)}(a/b)          *)
(*   （a^{2n−2j}·b^{2j}·Σ_i (−1)^i C(n,i)·降阶乘，2j ≤ n+i 带内）；        *)
(*   未缩放隙族 pif_gap = gapZ / (b^n·n!)，其缩放整性由构造显式闭合。      *)
(*   ②④ 槽凭证（隙族真值正性与衰减）属 π 解析面，为 π 支线下游义务。       *)
(* ------------------------------------------------------------------ *)

Fixpoint znegpow (k : nat) : Z :=
  match k with
  | Datatypes.O => 1%Z
  | Datatypes.S k' => Z.opp (znegpow k')
  end.

Fixpoint niv_ff (m k : nat) : nat :=
  match k with
  | Datatypes.O => 1%nat
  | Datatypes.S k' => (m * niv_ff (m - 1) k')%nat
  end.

Fixpoint zsum (m : nat) (g : nat -> Z) : Z :=
  match m with
  | Datatypes.O => 0%Z
  | Datatypes.S m' => (zsum m' g + g m')%Z
  end.

Section PiTowerInst.

  Variable a : Z.
  Variable b : positive.

  (* 端点项：g^{(2j)}(0) = (2j)!·C(n,2j−n)·a^{2n−2j}·(−b)^{2j−n}（带内显式） *)
  Definition pif_t0 (n j : nat) : Z :=
    if andb (Nat.leb n (2 * j)) (Nat.leb (2 * j) (2 * n)) then
      (Z.of_nat (fact (2 * j) * hl_binom n (2 * j - n))
         * (Z.pow a (Z.of_nat (2 * n - 2 * j))
              * (znegpow (2 * j - n) * Z.pow (Z.pos b) (Z.of_nat (2 * j - n)))))%Z
    else 0%Z.

  (* 节点项内和项：i 带内取 C(n,i)·(n+i)!/(n+i−2j)!·(−1)^i，带外取零 *)
  Definition pif_ti (n j i : nat) : Z :=
    if Nat.leb (2 * j) (n + i) then
      (Z.of_nat (hl_binom n i * niv_ff (n + i) (2 * j)) * znegpow i)%Z
    else 0%Z.

  (* 节点项：b^n·g^{(2j)}(a/b) = a^{2n−2j}·b^{2j}·Σ_i pif_ti *)
  Definition pif_t1 (n j : nat) : Z :=
    (Z.pow a (Z.of_nat (2 * n - 2 * j))
       * (Z.pow (Z.pos b) (Z.of_nat (2 * j))
            * zsum (Datatypes.S n) (pif_ti n j)))%Z.

  (* 缩放双端和族（b^n·n!·I_n 的代出面） *)
  Definition pif_gapZ (n : nat) : Z :=
    zsum (Datatypes.S n) (fun j : nat => (pif_t0 n j + pif_t1 n j)%Z).

  (* 缩放族 D_n = b^n·n! *)
  Definition pif_D (n : nat) : Z := (Z.pow (Z.pos b) (Z.of_nat n) * Z.of_nat (fact n))%Z.

  (* 未缩放隙族（积分面代数像） *)
  Definition pif_gap (n : nat) : Q := ((pif_gapZ n # 1) / (pif_D n # 1))%Q.

  (* 缩放族正性：b^n > 0 与 n! > 0 的乘法传递 *)
  Theorem pif_pow_b_pos : forall n : nat, (0 < Z.pow (Z.pos b) (Z.of_nat n))%Z.
  Proof.
    intro n. induction n as [|n IHn].
    - replace (Z.of_nat 0) with 0%Z by lia.
      rewrite Z.pow_0_r. lia.
    - replace (Z.of_nat (Datatypes.S n)) with (Z.succ (Z.of_nat n)) by lia.
      rewrite Z.pow_succ_r by lia.
      apply Z.mul_pos_pos.
      + pose proof (Pos2Z.is_pos b). lia.
      + exact IHn.
  Qed.

  Theorem pif_D_pos : forall n : nat, (0 < pif_D n)%Z.
  Proof.
    intro n. unfold pif_D. apply Z.mul_pos_pos.
    - apply pif_pow_b_pos.
    - pose proof (lt_O_fact n). lia.
  Qed.

  (* ③ 缩放隙整性：D_n·pif_gap n = gapZ n，除法代数一步显式闭合 *)
  Theorem pif_scaled_int : forall n : nat,
    sigT (fun z : Z => QeqT ((pif_D n # 1)%Q * pif_gap n)%Q ((z # 1)%Q)).
  Proof.
    intro n. exists (pif_gapZ n). apply qeq_imp_qeqT. unfold pif_gap.
    apply (niv_qmul_div_z1 (pif_D n) (pif_gapZ n)).
    pose proof (pif_D_pos n) as HP. lia.
  Qed.

  (* ① 双端分裂定律：缩放和 = 端点项和 + 节点项和（Hermite 恒等式两端） *)
  Lemma niv_zsum_add : forall (m : nat) (u v : nat -> Z),
    zsum m (fun j : nat => (u j + v j)%Z) = (zsum m u + zsum m v)%Z.
  Proof.
    intro m. induction m as [|m IHm]; intros u v.
    - reflexivity.
    - cbn [zsum]. rewrite IHm. lia.
  Qed.

  Theorem pif_gap_split : forall n : nat,
    QeqT ((pif_gapZ n # 1)%Q)
         ((((zsum (Datatypes.S n) (pif_t0 n)) # 1)
             + ((zsum (Datatypes.S n) (pif_t1 n)) # 1))%Q).
  Proof.
    intro n. apply qeq_imp_qeqT. unfold pif_gapZ.
    rewrite niv_zsum_add. rewrite <- lni_QaddZ. reflexivity.
  Qed.

End PiTowerInst.

(* ------------------------------------------------------------------ *)
(* §7 阶段对应定理：两塔 Set 面逐阶段对应                                   *)
(*   槽谓词 niv_slot3 = 缩放整性槽（阶段③出口形）。对应一：两塔表示律      *)
(*   同形（两项式/双端分裂，各附显式见证族）；对应二：ln2 塔的吸收路线与    *)
(*   π 塔的构造代入路线汇入同一槽谓词；对应三：同一矛盾门双塔实例化消解。      *)
(* ------------------------------------------------------------------ *)

Definition niv_slot3 (gap : nat -> Q) (D : nat -> Z) : Set :=
  forall n : nat,
    sigT (fun z : Z => QeqT ((D n # 1)%Q * gap n)%Q ((z # 1)%Q)).

(* 对应一（阶段①）：表示律同形 *)
Theorem niv_iso_stage1 : forall (tgt : Q) (a : Z) (b : positive),
  And (sigT (fun ann : nat -> Q => sigT (fun bnn : nat -> Q =>
         forall n : nat, QeqT (lnt_gap tgt n) ((ann n + bnn n * tgt)%Q))))
      (sigT (fun endf : nat -> Q => sigT (fun nodef : nat -> Q =>
         forall n : nat, QeqT ((pif_gapZ a b n # 1)%Q)
                              ((endf n + nodef n)%Q)))).
Proof.
  intros tgt a b. split.
  - exact (lnt_gap_repr tgt).
  - exists (fun n : nat => (zsum (Datatypes.S n) (pif_t0 a b n) # 1)%Q),
           (fun n : nat => (zsum (Datatypes.S n) (pif_t1 a b n) # 1)%Q).
    intro n. exact (pif_gap_split a b n).
Qed.

(* 对应二（阶段③）：两条消解路线汇入同一缩放整性槽 *)
Theorem niv_iso_stage3 : forall (tgt : Q) (a : Z) (b : positive),
  And (forall (p : Z) (q : positive), QeqT tgt ((p # q)%Q) ->
        niv_slot3 (lnt_gap tgt)
                  (fun n : nat => (Z.pos q * Z.of_nat (hl_lcm_upto n))%Z))
      (niv_slot3 (pif_gap a b) (pif_D b)).
Proof.
  intros tgt a b. split.
  - intros p q H. intro n. exact (lnt_gap_int tgt p q H n).
  - intro n. exact (pif_scaled_int a b n).
Qed.

(* 对应三（阶段④⑤）：同一矛盾门双塔实例化消解——两塔各自的缩放隙整数面     *)
(*   落入 (0,1) 时，同一原子机器 nhs_int_gap_gate 分别实例化消解。            *)
Theorem niv_iso_exit_pair : forall (tgt : Q) (a : Z) (b : positive)
  (p : Z) (q : positive) (Htgt : QeqT tgt ((p # q)%Q)) (n : nat),
  And ((And (QltT 0 (((Z.pos q * Z.of_nat (hl_lcm_upto n)) # 1)%Q
                        * lnt_gap tgt n)%Q)
            (QltT (((Z.pos q * Z.of_nat (hl_lcm_upto n)) # 1)%Q
                     * lnt_gap tgt n)%Q 1%Q)) -> Id false true)
      ((And (QltT 0 (((pif_D b n) # 1)%Q * pif_gap a b n)%Q)
            (QltT (((pif_D b n) # 1)%Q * pif_gap a b n)%Q 1%Q)) -> Id false true).
Proof.
  intros tgt a b p q Htgt n. split.
  - intro Hpair. destruct Hpair as [Hpos Hlt].
    destruct (lnt_gap_int tgt p q Htgt n) as [zl Hzl].
    apply (nhs_int_gap_gate zl).
    + pose proof Hpos as Hp. apply QltT_to_Qlt in Hp.
      rewrite (qeqT_imp_qeq _ _ Hzl) in Hp. apply Qlt_to_QltT. exact Hp.
    + pose proof Hlt as Hl. apply QltT_to_Qlt in Hl.
      rewrite (qeqT_imp_qeq _ _ Hzl) in Hl. apply Qlt_to_QltT. exact Hl.
  - intro Hpair. destruct Hpair as [Hpos Hlt].
    destruct (pif_scaled_int a b n) as [zp Hzp].
    apply (nhs_int_gap_gate zp).
    + pose proof Hpos as Hp. apply QltT_to_Qlt in Hp.
      rewrite (qeqT_imp_qeq _ _ Hzp) in Hp. apply Qlt_to_QltT. exact Hp.
    + pose proof Hlt as Hl. apply QltT_to_Qlt in Hl.
      rewrite (qeqT_imp_qeq _ _ Hzp) in Hl. apply Qlt_to_QltT. exact Hl.
Qed.

(* ------------------------------------------------------------------ *)
(* §8 e 塔类型级接口占位                                                   *)
(*   e 塔的无理性证明（a_n + b_n·e 两项式与 q·n! 缩放）与本机器同构：       *)
(*   接口面与塔构造子可证重合（e_tower_interface_coincide），其缩放候选     *)
(*   e_tower_scale = q·n! 之正性就地闭合；实例化凭证（①表示律之部分和族、  *)
(*   ③两见证、②④锐权与衰减）留待 e 塔支线供给，本件零假设声明。            *)
(* ------------------------------------------------------------------ *)

Definition e_tower_scale (q0 : positive) (n : nat) : Z :=
  (Z.pos q0 * Z.of_nat (fact n))%Z.

Theorem e_tower_scale_pos : forall (q0 : positive) (n : nat),
  (0 < e_tower_scale q0 n)%Z.
Proof.
  intros q0 n. unfold e_tower_scale. apply Z.mul_pos_pos.
  - apply Pos2Z.is_pos.
  - pose proof (lt_O_fact n). lia.
Qed.

Definition e_tower_face (tgt : Q) : Set :=
  forall (W : niv_rat_wit tgt) (irep wlo whi : nat -> Q) (D : nat -> Z),
    niv_slots tgt W irep wlo whi D -> niv_irr_face tgt.

(* 接口重合：e 塔面即塔构造子面——实例化只需供给同一五槽束 *)
Theorem e_tower_interface_coincide : forall tgt : Q,
  e_tower_face tgt = TowerBuilder tgt.
Proof. intro tgt. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* §9 提取检验区与假设审计                                                 *)
(* ------------------------------------------------------------------ *)

Separate Extraction niv_qmul_div_z1 niv_int_absorb tb_pair_cohere tb_gap_pos
  tb_scaled_pos tb_scaled_lt1 tb_separator tb_build
  lnt_gap_repr lnt_gap_int lnt_supply_pair lnt_supply_tail
  pif_pow_b_pos pif_D_pos pif_scaled_int pif_gap_split
  niv_iso_stage1 niv_iso_stage3 niv_iso_exit_pair
  e_tower_scale_pos e_tower_interface_coincide.

Print Assumptions niv_qmul_div_z1.
Print Assumptions niv_int_absorb.
Print Assumptions tb_pair_cohere.
Print Assumptions tb_gap_pos.
Print Assumptions tb_scaled_pos.
Print Assumptions tb_scaled_lt1.
Print Assumptions tb_separator.
Print Assumptions tb_build.
Print Assumptions lnt_gap_repr.
Print Assumptions lnt_gap_int.
Print Assumptions lnt_supply_pair.
Print Assumptions lnt_supply_tail.
Print Assumptions pif_pow_b_pos.
Print Assumptions pif_D_pos.
Print Assumptions pif_scaled_int.
Print Assumptions pif_gap_split.
Print Assumptions niv_iso_stage1.
Print Assumptions niv_iso_stage3.
Print Assumptions niv_iso_exit_pair.
Print Assumptions e_tower_scale_pos.
Print Assumptions e_tower_interface_coincide.
