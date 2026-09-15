(* ============================================================ *)
(* SupKLMonoCompose.v                                           *)
(*                                                              *)
(* 目的：零上界（B 形因子）le_b 乘法保序合成器——补 UpReqGeomIter.v  *)
(*       :865-869 指出的缺口④「le_b 乘法保序闭包：a ≤_B b ∧ 0 ≤_B c *)
(*       ⟹ a·c ≤_B b·c」在 KL 场景的可全供给形（skm_ 前缀防撞）。   *)
(* 主件：skm_le_b_mult_r_nonneg_bfree : forall a b c L : Real,      *)
(*       real_le_b a b -> real_le_b real_zero c ->                  *)
(*       real_lt real_zero a -> real_le b real_one ->               *)
(*       real_le c L -> real_lt real_zero L ->                      *)
(*       real_le_b (real_mult a c) (real_mult b c)。                *)
(*       实例件 skm_pow_kl_mono_le_b_bfree（κ^{t1}·KL_0 ≤_B κ^t·KL_0） *)
(*       与主桥形 skm_policy_iter_kl_pow_mono_B_bfree；              *)
(*       归纳新件 skm_powb_le_one_or（powb 面 Or 形单位上界）。       *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                *)
(*       S07_RealSetoidExpLog、S08_RealMainlineDPO、S09_EntropyReal、 *)
(*       G01_CoreMicro、UpRealLeB、UpRealLeB2、G07_KLWall、           *)
(*       UpReqGeomD、UpReqGeomIter；Stdlib List（ListNotations）、     *)
(*       Extraction。                                                *)
(* 备注：消费位实测——主桥 geodi_policy_iter_kl_geom_iter_B 已由       *)
(*       real_le_closure_b_one 闭合，不缺④；④的消费位在              *)
(*       UpReqI4Bridge.v 件1/件2（i4b_pow_kl_mono_le_b 与             *)
(*       i4b_policy_iter_kl_pow_mono_B），二者均卡前提 Hkl0or :       *)
(*       real_le real_zero KL_0（Or 形非负证书），而库内只有 B 形      *)
(*       geodi_kl_nonneg_B，B⟹Or 构造性不可通。本件路线：c 的非负性   *)
(*       只吃 B 形（real_le_b real_zero c，伴件直供），代价是显式      *)
(*       供给三份 Or 形证书材料：a 严格正（powb_pos_lt）、b 单位上界   *)
(*       （skm_powb_le_one_or 新建归纳件）、c 上界 L                  *)
(*       （skb_sup_kl_log_inv_min 结论面直供）与 L 正性。              *)
(*       与件5 有界版（x3d_le_b_mult_r_nonneg_bnd）对照：本件把 c      *)
(*       非负降为 B 形、c 上界保持 Or 形，并新增 a 严格正、b ≤ 1 两    *)
(*       前提——KL 场景四者全有库内供给位。通用性边界如实申报：        *)
(*       抽象 a 无正性证书、b 无上界材料的场景本件不覆盖（交叉项       *)
(*       eta·eta 的配平需 a·eta ≥ 0 与 b·eta ≤ eta 两面），那是        *)
(*       B⟹Or 构造性不可通的同源剩余。                               *)
(*       证明路线（单 witness 三份额配平，全域无分支；关键在交叉项     *)
(*       处理）：给 W=eps>0，取 M := 3+W、X := W·inv(M)、              *)
(*       eta := X·inv(L+2)。链：a·c < a·(c+eta) < (b+eta)·(c+eta)      *)
(*       = (b·c + eta·c) + (b·eta + eta·eta)。小项三份额：             *)
(*       (i) eta·c ≤ eta·L ≤ eta·(L+2) == X（精确等式底座）；          *)
(*       (ii) b·eta ≤ eta ≤ X；(iii) eta·eta 经 inv(L+2) 因子精确      *)
(*       吸收后 X·eta ≤ X·X ≤ X（X ≤ 1 自乘收敛）。合计                *)
(*       (X+X)+X < eps（X+X+X == eps·(invM·3) < eps·(M·invM) == eps，  *)
(*       由 3 < M 严格左乘），逐 eps 闭合。证内 set（M/X/L2/eta 局部   *)
(*       缩写）为 tactic 层操作，语句面保持素颜。                      *)
(*       全件 Qed 零承认式；语句面全 Set（real_le_b 定义即 Set 层      *)
(*       forall 型，real_le/real_lt 为 Set 层 Or/lt 编码）。            *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import G01_CoreMicro.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpReqGeomIter.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* §1 Or 形幂上界归纳件（b ≤ 1 供给位；powb 面仅有 B 形 ≤_B 1（          *)
(*    powb_one_minus_eta_le_one），逐 eps 合成器需要 Or 形单位上界，     *)
(*    归纳直证补齐：base·base^m ≤ base·1 == base ≤ 1。）                 *)
(* ============================================================ *)

Lemma skm_powb_le_one_or : forall (base : Real) (t : nat),
  real_le real_zero base -> real_le base real_one ->
  real_le (powb_pow base t) real_one.
Proof.
  intros base t H0 H1. induction t as [| m IH].
  - cbn [powb_pow]. apply real_le_refl.
  - cbn [powb_pow].
    (* 9.1 全量适配：real_le_mult_compat_r 结论为 base·x ≤ base·one，
       距目标 base·x ≤ one 尚差 base ≤ one（H1）——外套 real_le_trans 两腿拼接 *)
    apply (real_le_trans (real_mult base (powb_pow base m)) base real_one).
    + apply (RealSetoid.real_le_id_r (real_mult base (powb_pow base m))
               (real_mult base real_one) base).
      * apply real_mult_one.
      * exact (real_le_mult_compat_r base (powb_pow base m) real_one
                 H0 IH).
    + exact H1.
Qed.

(* ============================================================ *)
(* §2 主合成器：纯 B 形因子 + 显式上界材料版④                           *)
(*   a ≤_B b ∧ 0 ≤_B c ∧ 0<a ∧ b≤1 ∧ c≤L ∧ 0<L ⟹ a·c ≤_B b·c。        *)
(* ============================================================ *)

Theorem skm_le_b_mult_r_nonneg_bfree :
  forall a b c L : Real,
  real_le_b a b ->
  real_le_b real_zero c ->
  real_lt real_zero a ->
  real_le b real_one ->
  real_le c L ->
  real_lt real_zero L ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c L Hab Hc Ha Hb1 HcL HLpos.
  unfold real_le_b. intros eps Heps.
  (* ============ 基础正性与证书 ============ *)
  assert (H2 : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one).
  assert (H3 : real_lt real_zero
                 (real_plus (real_plus real_one real_one) real_one))
    by exact (real_plus_positive (real_plus real_one real_one)
                real_one H2 real_lt_zero_one).
  assert (H12 : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one
             (real_plus real_one real_zero)
             (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - exact (real_lt_plus_translate real_one real_zero
               real_one real_lt_zero_one). }
  set (M := real_plus (real_plus (real_plus real_one real_one)
                  real_one) eps).
  assert (HMpos : real_lt real_zero M)
    by exact (real_plus_positive (real_plus (real_plus real_one real_one)
                                 real_one) eps H3 Heps).
  assert (HMinv : real_lt real_zero (real_inv_pos M HMpos))
    by exact (real_inv_pos_pos M HMpos).
  assert (H3ltM : real_lt
    (real_plus (real_plus real_one real_one) real_one) M).
  { apply (RealSetoid.real_lt_id_l
             (real_plus (real_plus real_one real_one) real_one)
             (real_plus (real_plus (real_plus real_one real_one)
                real_one) real_zero) M).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (RealSetoid.real_lt_id_r
               (real_plus (real_plus (real_plus real_one real_one)
                  real_one) real_zero)
               (real_plus (real_plus (real_plus real_one real_one)
                  real_one) eps) M).
      + apply real_eq_refl.
      + exact (real_lt_plus_translate
                 (real_plus (real_plus real_one real_one)
                    real_one) real_zero eps Heps). }
  assert (HepsleM : real_le eps M).
  { apply (RealSetoid.real_le_id_l eps (real_plus eps real_zero) M).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (RealSetoid.real_lt_le_iff_req
               (real_plus eps real_zero) M).
      left.
      apply (RealSetoid.real_lt_id_r (real_plus eps real_zero)
                 (real_plus eps (real_plus (real_plus real_one real_one)
                    real_one)) M).
      + apply real_plus_comm.
      + exact (real_lt_plus_translate eps real_zero
                 (real_plus (real_plus real_one real_one) real_one) H3). }
  set (X := real_mult eps (real_inv_pos M HMpos)).
  assert (HXpos : real_lt real_zero X)
    by exact (real_mult_positive eps (real_inv_pos M HMpos) Heps HMinv).
  assert (HXle1 : real_le X real_one).
  { apply (RealSetoid.real_le_id_r X (real_mult M (real_inv_pos M HMpos))
             real_one).
    - exact (real_inv_pos_correct M HMpos).
    - exact (real_le_mult_compat eps M (real_inv_pos M HMpos)
               HMinv HepsleM). }
  assert (HXle : real_le real_zero X)
    by exact (RealSetoid.real_lt_le_iff_req real_zero X (inl HXpos)).
  set (L2 := real_plus L (real_plus real_one real_one)).
  assert (HL2 : real_lt real_zero L2)
    by exact (real_plus_positive L (real_plus real_one real_one)
                HLpos H2).
  assert (HL2inv : real_lt real_zero (real_inv_pos L2 HL2))
    by exact (real_inv_pos_pos L2 HL2).
  assert (Hinvle1 : real_le (real_inv_pos L2 HL2) real_one).
  { apply (RealSetoid.real_le_id_r (real_inv_pos L2 HL2)
             (real_mult L2 (real_inv_pos L2 HL2)) real_one).
    - exact (real_inv_pos_correct L2 HL2).
    - apply (RealSetoid.real_le_id_l (real_inv_pos L2 HL2)
               (real_mult real_one (real_inv_pos L2 HL2))
               (real_mult L2 (real_inv_pos L2 HL2))).
      + exact (real_eq_trans (real_inv_pos L2 HL2)
                 (real_mult (real_inv_pos L2 HL2) real_one)
                 (real_mult real_one (real_inv_pos L2 HL2))
                 (real_eq_sym _ _ (real_mult_one (real_inv_pos L2 HL2)))
                 (real_mult_comm (real_inv_pos L2 HL2) real_one)).
      + apply (real_le_mult_compat real_one L2 (real_inv_pos L2 HL2)
                 HL2inv).
        apply (real_le_trans real_one (real_plus real_one L) L2).
        * exact (RealSetoid.real_le_id_l real_one
                   (real_plus real_one real_zero) (real_plus real_one L)
                   (real_eq_sym _ _ (real_plus_zero real_one))
                   (RealSetoid.real_lt_le_iff_req (real_plus real_one real_zero)
                      (real_plus real_one L)
                      (inl (real_lt_plus_translate real_one real_zero L
                              HLpos)))).
        * exact (RealSetoid.real_lt_le_iff_req (real_plus real_one L) L2
                   (inl (RealSetoid.real_lt_id_l (real_plus real_one L)
                           (real_plus L real_one) L2
                           (real_plus_comm real_one L)
                           (real_lt_plus_translate L real_one
                              (real_plus real_one real_one) H12)))). }
  set (eta := real_mult X (real_inv_pos L2 HL2)).
  assert (Hetapos : real_lt real_zero eta)
    by exact (real_mult_positive X (real_inv_pos L2 HL2) HXpos HL2inv).
  assert (Hetale : real_le real_zero eta)
    by exact (RealSetoid.real_lt_le_iff_req real_zero eta (inl Hetapos)).
  (* ============ 核心精确等式底座：eta·(L+2) == X ============ *)
  assert (HetaL2 : real_eq (real_mult eta L2) X).
  { apply (real_eq_trans _ (real_mult X (real_mult (real_inv_pos L2 HL2)
                                       L2)) _).
    - exact (real_eq_sym
               (real_mult X (real_mult (real_inv_pos L2 HL2) L2))
               (real_mult (real_mult X (real_inv_pos L2 HL2)) L2)
               (real_mult_assoc X (real_inv_pos L2 HL2) L2)).
    - exact (real_eq_trans
               (real_mult X (real_mult (real_inv_pos L2 HL2) L2))
               (real_mult X real_one) X
               (RealSetoid.real_eq_mult_compat X
                  (real_mult (real_inv_pos L2 HL2) L2) X real_one
                  (real_eq_refl X)
                  (real_eq_trans (real_mult (real_inv_pos L2 HL2) L2)
                     (real_mult L2 (real_inv_pos L2 HL2)) real_one
                     (real_mult_comm (real_inv_pos L2 HL2) L2)
                     (real_inv_pos_correct L2 HL2)))
               (real_mult_one X)). }
  assert (HetaXle : real_le eta X)
    by exact (RealSetoid.real_le_id_r
                (real_mult X (real_inv_pos L2 HL2))
                (real_mult X real_one) X
                (real_mult_one X)
                (real_le_mult_compat_r X (real_inv_pos L2 HL2) real_one
                   HXle Hinvle1)).
  assert (Hinvar : real_le (real_mult eta (real_inv_pos L2 HL2)) eta).
  { apply (RealSetoid.real_le_id_r
             (real_mult eta (real_inv_pos L2 HL2))
             (real_mult eta real_one) eta).
    - apply real_mult_one.
    - exact (real_le_mult_compat_r eta (real_inv_pos L2 HL2) real_one
               Hetale Hinvle1). }
  (* ============ 小项三份额 ============ *)
  (* (i) eta·c ≤ X *)
  assert (Hi : real_le (real_mult eta c) X).
  { apply (real_le_trans (real_mult eta c) (real_mult eta L2) X).
    - apply (real_le_trans (real_mult eta c) (real_mult eta L)
               (real_mult eta L2)).
      + exact (real_le_mult_compat_r eta c L Hetale HcL).
      + apply (real_le_mult_compat_r eta L L2 Hetale).
        apply (real_le_trans L (real_plus L real_one) L2).
        * exact (RealSetoid.real_le_id_l L (real_plus L real_zero)
                   (real_plus L real_one)
                   (real_eq_sym _ _ (real_plus_zero L))
                   (RealSetoid.real_lt_le_iff_req (real_plus L real_zero)
                      (real_plus L real_one)
                      (inl (real_lt_plus_translate L real_zero real_one
                              real_lt_zero_one)))).
        * exact (RealSetoid.real_lt_le_iff_req (real_plus L real_one) L2
                   (inl (real_lt_plus_translate L real_one
                           (real_plus real_one real_one) H12))).
    - exact (RealSetoid.real_eq_le _ _ HetaL2). }
  (* (ii) b·eta ≤ X *)
  assert (Hii : real_le (real_mult b eta) X).
  { apply (real_le_trans (real_mult b eta) (real_mult real_one eta) X).
    - exact (real_le_mult_compat b real_one eta Hetapos Hb1).
    - apply (real_le_trans (real_mult real_one eta) eta X).
      + apply (RealSetoid.real_le_id_l (real_mult real_one eta)
                 (real_mult eta real_one) eta).
        * apply real_mult_comm.
        * apply (RealSetoid.real_eq_le (real_mult eta real_one) eta).
          apply real_mult_one.
      + exact HetaXle. }
  (* (iii) eta·eta ≤ X（交叉项经 inv(L+2) 精确吸收后自乘收敛） *)
  assert (Hetaeq : real_eq eta (real_mult X (real_inv_pos L2 HL2))).
  { assert (H1 : real_eq (real_mult eta real_one)
                    (real_mult eta (real_mult L2 (real_inv_pos L2 HL2)))).
    { apply (RealSetoid.real_eq_mult_compat eta real_one eta
               (real_mult L2 (real_inv_pos L2 HL2))).
      - apply real_eq_refl.
      - exact (real_eq_sym _ _ (real_inv_pos_correct L2 HL2)). }
    assert (Hq2 : real_eq (real_mult eta (real_mult L2 (real_inv_pos L2 HL2)))
                   (real_mult (real_mult eta L2) (real_inv_pos L2 HL2))).
    { exact (real_mult_assoc eta L2 (real_inv_pos L2 HL2)). }
    assert (Hq3 : real_eq (real_mult (real_mult eta L2) (real_inv_pos L2 HL2))
                   (real_mult X (real_inv_pos L2 HL2))).
    { apply (RealSetoid.real_eq_mult_compat (real_mult eta L2)
               (real_inv_pos L2 HL2) X (real_inv_pos L2 HL2)).
      - exact HetaL2.
      - apply real_eq_refl. }
    exact (real_eq_trans eta (real_mult eta real_one)
             (real_mult X (real_inv_pos L2 HL2))
             (real_eq_sym _ _ (real_mult_one eta))
             (real_eq_trans (real_mult eta real_one)
                (real_mult eta (real_mult L2 (real_inv_pos L2 HL2)))
                (real_mult X (real_inv_pos L2 HL2)) H1
                (real_eq_trans
                   (real_mult eta (real_mult L2 (real_inv_pos L2 HL2)))
                   (real_mult (real_mult eta L2) (real_inv_pos L2 HL2))
                   (real_mult X (real_inv_pos L2 HL2)) Hq2 Hq3))). }
  assert (Heta1 : real_le eta real_one).
  { apply (real_le_trans eta (real_mult X (real_inv_pos L2 HL2)) real_one).
    - exact (inr Hetaeq).
    - exact (real_le_trans (real_mult X (real_inv_pos L2 HL2))
               (real_mult X real_one) real_one
               (real_le_mult_compat_r X (real_inv_pos L2 HL2) real_one
                  HXle Hinvle1)
               (real_le_trans (real_mult X real_one) X real_one
                  (RealSetoid.real_le_id_l (real_mult X real_one) X X
                     (real_mult_one X) (real_le_refl X))
                  HXle1)). }
  assert (Hiii : real_le (real_mult eta eta) X).
  { apply (real_le_trans (real_mult eta eta) (real_mult eta real_one) X).
    - exact (real_le_mult_compat_r eta eta real_one Hetale Heta1).
    - exact (RealSetoid.real_le_id_l (real_mult eta real_one) eta X
               (real_mult_one eta) HetaXle). }
  (* ============ 三份和与挤压缩 ============ *)
  assert (Hsum : real_le
    (real_plus (real_plus (real_mult eta c) (real_mult b eta))
       (real_mult eta eta))
    (real_plus (real_plus X X) X)).
  { apply (real_le_plus_compat
             (real_plus (real_mult eta c) (real_mult b eta))
             (real_plus X X) (real_mult eta eta) X).
    - apply (real_le_plus_compat (real_mult eta c) X
               (real_mult b eta) X Hi Hii).
    - exact Hiii. }
  assert (H3X : real_lt (real_plus (real_plus X X) X) eps).
  { assert (HinvM1 : real_eq (real_mult (real_inv_pos M HMpos) M) real_one).
    { exact (real_eq_trans (real_mult (real_inv_pos M HMpos) M)
               (real_mult M (real_inv_pos M HMpos)) real_one
               (real_mult_comm (real_inv_pos M HMpos) M)
               (real_inv_pos_correct M HMpos)). }
    assert (Hd1 : real_eq (real_mult X (real_plus (real_plus real_one real_one) real_one))
                    (real_plus (real_mult X (real_plus real_one real_one))
                       (real_mult X real_one))).
    { exact (real_distrib X (real_plus real_one real_one) real_one). }
    assert (Hd2 : real_eq (real_mult X (real_plus real_one real_one))
                    (real_plus (real_mult X real_one) (real_mult X real_one))).
    { exact (real_distrib X real_one real_one). }
    assert (Hp1 : real_eq (real_plus (real_mult X (real_plus real_one real_one))
                         (real_mult X real_one))
                    (real_plus (real_plus (real_mult X real_one) (real_mult X real_one))
                       (real_mult X real_one))).
    { apply (RealSetoid.real_eq_plus_compat
               (real_mult X (real_plus real_one real_one)) (real_mult X real_one)
               (real_plus (real_mult X real_one) (real_mult X real_one))
               (real_mult X real_one)).
      - exact Hd2.
      - apply real_eq_refl. }
    assert (Hp2 : real_eq (real_plus (real_plus (real_mult X real_one)
                         (real_mult X real_one)) (real_mult X real_one))
                    (real_plus (real_plus X X) X)).
    { apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult X real_one) (real_mult X real_one))
               (real_mult X real_one) (real_plus X X) X).
      - exact (RealSetoid.real_eq_plus_compat (real_mult X real_one)
                 (real_mult X real_one) X X
                 (real_mult_one X) (real_mult_one X)).
      - exact (real_mult_one X). }
    assert (He1 : real_eq (real_plus (real_plus X X) X)
                      (real_mult X (real_plus (real_plus real_one real_one) real_one))).
    { exact (real_eq_sym (real_mult X (real_plus (real_plus real_one real_one) real_one))
               (real_plus (real_plus X X) X)
               (real_eq_trans (real_mult X (real_plus (real_plus real_one real_one) real_one))
                  (real_plus (real_mult X (real_plus real_one real_one))
                     (real_mult X real_one))
                  (real_plus (real_plus X X) X) Hd1
                  (real_eq_trans _ _ _ Hp1 Hp2))). }
    apply (RealSetoid.real_lt_id_r
             (real_plus (real_plus X X) X)
             (real_mult X M) eps).
    - exact (real_eq_trans (real_mult X M)
               (real_mult eps (real_mult (real_inv_pos M HMpos) M)) eps
               (real_eq_sym _ _ (real_mult_assoc eps (real_inv_pos M HMpos) M))
               (real_eq_trans
                  (real_mult eps (real_mult (real_inv_pos M HMpos) M))
                  (real_mult eps real_one) eps
                  (RealSetoid.real_eq_mult_compat eps
                     (real_mult (real_inv_pos M HMpos) M) eps real_one
                     (real_eq_refl eps) HinvM1)
                  (real_mult_one eps))).
    - exact (RealSetoid.real_lt_id_l
               (real_plus (real_plus X X) X)
               (real_mult X (real_plus (real_plus real_one real_one) real_one))
               (real_mult X M)
               He1
               (real_mult_lt_compat_l
                  (real_plus (real_plus real_one real_one) real_one) M X
                  H3ltM HXpos)). }
  (* ============ 主链闭合 ============ *)
  assert (Hdist5 : real_eq
    (real_mult (real_plus b eta) (real_plus c eta))
    (real_plus (real_plus (real_mult b c) (real_mult eta c))
       (real_plus (real_mult b eta) (real_mult eta eta)))).
  { apply (real_eq_trans _
             (real_plus (real_mult (real_plus b eta) c)
                (real_mult (real_plus b eta) eta)) _).
    - apply real_distrib.
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_plus b eta) c)
               (real_mult (real_plus b eta) eta)
               (real_plus (real_mult b c) (real_mult eta c))
               (real_plus (real_mult b eta) (real_mult eta eta))).
      + exact (real_eq_trans (real_mult (real_plus b eta) c)
                   (real_plus (real_mult c b) (real_mult c eta))
                   (real_plus (real_mult b c) (real_mult eta c))
                   (real_eq_trans (real_mult (real_plus b eta) c)
                      (real_mult c (real_plus b eta))
                      (real_plus (real_mult c b) (real_mult c eta))
                      (real_mult_comm (real_plus b eta) c)
                      (real_distrib c b eta))
                   (RealSetoid.real_eq_plus_compat (real_mult c b)
                      (real_mult c eta) (real_mult b c) (real_mult eta c)
                      (real_eq_trans (real_mult c b) (real_mult b c)
                         (real_mult b c)
                         (real_mult_comm c b) (real_eq_refl (real_mult b c)))
                      (real_eq_trans (real_mult c eta) (real_mult eta c)
                         (real_mult eta c)
                         (real_mult_comm c eta)
                         (real_eq_refl (real_mult eta c))))).
      + exact (real_eq_trans (real_mult (real_plus b eta) eta)
                   (real_plus (real_mult eta b) (real_mult eta eta))
                   (real_plus (real_mult b eta) (real_mult eta eta))
                   (real_eq_trans (real_mult (real_plus b eta) eta)
                      (real_mult eta (real_plus b eta))
                      (real_plus (real_mult eta b) (real_mult eta eta))
                      (real_mult_comm (real_plus b eta) eta)
                      (real_distrib eta b eta))
                   (RealSetoid.real_eq_plus_compat (real_mult eta b)
                      (real_mult eta eta) (real_mult b eta)
                      (real_mult eta eta)
                      (real_eq_trans (real_mult eta b) (real_mult b eta)
                         (real_mult b eta)
                         (real_mult_comm eta b) (real_eq_refl (real_mult b eta)))
                      (real_eq_refl (real_mult eta eta)))). }
  assert (Hstep1lt : real_lt (real_mult a c)
    (real_mult a (real_plus c eta))).
  { apply (RealSetoid.real_lt_id_r (real_mult a c)
             (real_plus (real_mult a c) (real_mult a eta))
             (real_mult a (real_plus c eta))).
    - exact (real_eq_sym (real_mult a (real_plus c eta))
               (real_plus (real_mult a c) (real_mult a eta))
               (real_distrib a c eta)).
    - exact (real_lt_plus_r_zero (real_mult a c) (real_mult a eta)
                (real_mult_pos_compat a eta Ha Hetapos)). }
  assert (Hstep4 : real_lt (real_mult a (real_plus c eta))
    (real_mult (real_plus b eta) (real_plus c eta))).
  { exact (real_mult_lt_compat a (real_plus b eta) (real_plus c eta)
             (Hab eta Hetapos) (Hc eta Hetapos)). }
  assert (Hmain : real_lt (real_mult a c)
    (real_plus (real_plus (real_mult b c) (real_mult eta c))
       (real_plus (real_mult b eta) (real_mult eta eta)))).
  { exact (RealSetoid.real_lt_id_r (real_mult a c)
             (real_mult (real_plus b eta) (real_plus c eta))
             (real_plus (real_plus (real_mult b c) (real_mult eta c))
                (real_plus (real_mult b eta) (real_mult eta eta)))
             Hdist5 (real_lt_trans (real_mult a c)
                       (real_mult a (real_plus c eta))
                       (real_mult (real_plus b eta) (real_plus c eta))
                       Hstep1lt Hstep4)). }
  apply (real_lt_trans (real_mult a c)
           (real_plus (real_plus (real_mult b c) (real_mult eta c))
              (real_plus (real_mult b eta) (real_mult eta eta)))
           (real_plus (real_mult b c) eps)).
  - exact Hmain.
  - exact (real_eq_lt_lt
               (real_plus (real_plus (real_mult b c) (real_mult eta c))
                  (real_plus (real_mult b eta) (real_mult eta eta)))
               (real_plus (real_mult b c)
                  (real_plus (real_plus (real_mult eta c)
                     (real_mult b eta)) (real_mult eta eta)))
               (real_plus (real_mult b c) eps)
               (real_eq_trans
                  (real_plus (real_plus (real_mult b c) (real_mult eta c))
                     (real_plus (real_mult b eta) (real_mult eta eta)))
                  (real_plus (real_mult b c)
                     (real_plus (real_mult eta c)
                        (real_plus (real_mult b eta) (real_mult eta eta))))
                  (real_plus (real_mult b c)
                     (real_plus (real_plus (real_mult eta c)
                        (real_mult b eta)) (real_mult eta eta)))
                  (real_eq_sym
                     (real_plus (real_mult b c)
                        (real_plus (real_mult eta c)
                           (real_plus (real_mult b eta) (real_mult eta eta))))
                     (real_plus (real_plus (real_mult b c) (real_mult eta c))
                        (real_plus (real_mult b eta) (real_mult eta eta)))
                     (real_plus_assoc (real_mult b c) (real_mult eta c)
                        (real_plus (real_mult b eta) (real_mult eta eta))))
                  (RealSetoid.real_eq_plus_compat (real_mult b c)
                     (real_plus (real_mult eta c)
                        (real_plus (real_mult b eta) (real_mult eta eta)))
                     (real_mult b c)
                     (real_plus (real_plus (real_mult eta c)
                        (real_mult b eta)) (real_mult eta eta))
                     (real_eq_refl (real_mult b c))
                     (real_plus_assoc (real_mult eta c) (real_mult b eta)
                        (real_mult eta eta))))
                  (real_lt_plus_translate (real_mult b c)
                     (real_plus (real_plus (real_mult eta c)
                        (real_mult b eta)) (real_mult eta eta)) eps
                     (real_le_lt_trans
                        (real_plus (real_plus (real_mult eta c)
                           (real_mult b eta)) (real_mult eta eta))
                        (real_plus (real_plus X X) X) eps Hsum H3X))).
Qed.

(* ============================================================ *)
(* §3 KL 场景实例件：κ^{t1}·KL_0 ≤_B κ^t·KL_0（④∘③，i4b 件1 的          *)
(*    B 形因子版——Hkl0or 换为 B 形伴件 I + skb 上界三件套）              *)
(* ============================================================ *)

Lemma skm_pow_kl_mono_le_b_bfree :
  forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one)
    (t t1 : nat) (Hle : NatLe t t1)
    (L : Real)
    (Hkl0ub : real_le
                (geod_lsum n
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                L)
    (HLpos : real_lt real_zero L),
  real_le_b
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
               (geod_lsum n
                  (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n
                  (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros.
  exact (skm_le_b_mult_r_nonneg_bfree
           (powb_pow (real_plus real_one (real_opp eta)) t1)
           (powb_pow (real_plus real_one (real_opp eta)) t)
           (geod_lsum n
              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
           L
           (powb_one_minus_eta_mono_dec eta t t1 Heta Hlt1 Hle)
           (geodi_kl_nonneg_B n r p Hr Hp Hnormr Hnormp)
           (powb_pos_lt (real_plus real_one (real_opp eta)) t1
              (powb_one_minus_eta_pos eta Heta Hlt1))
           (skm_powb_le_one_or (real_plus real_one (real_opp eta)) t
              (RealSetoid.real_lt_le_iff_req real_zero
                 (real_plus real_one (real_opp eta))
                 (inl (powb_one_minus_eta_pos eta Heta Hlt1)))
              (powb_one_minus_eta_base_le_one eta Heta))
           Hkl0ub HLpos).
Qed.

(* ============================================================ *)
(* §4 主桥包：t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0（判词 I4 目标形在           *)
(*    B 形因子 + skb 上界材料下无条件闭合；镜像 i4b 件2，跳②换 §3 件）   *)
(* ============================================================ *)

Lemma skm_policy_iter_kl_pow_mono_B_bfree :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : S06_DiffSamplingGibbs.NatLt 0 n)
    (t t1 : nat) (Hle : NatLe t t1)
    (L : Real)
    (Hkl0ub : real_le
                (geod_lsum n
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                L)
    (HLpos : real_lt real_zero L),
  real_le_b
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn t1 i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n
                  (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros.
  apply (real_le_b_trans
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn t1 i)
                              (Hr i)
                              (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
              (geod_lsum n
                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
              (geod_lsum n
                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  - exact (geodi_policy_iter_kl_geom_iter_B n r Hr eta Heta Hlt1 p Hp
             Hnormr Hnormp Hn t1).
  - exact (skm_pow_kl_mono_le_b_bfree n r p Hr Hp Hnormr Hnormp eta Heta
             Hlt1 t t1 Hle L Hkl0ub HLpos).
Qed.

(* ============================================================ *)
(* §5 对照注记（注释面，非证题）                                        *)
(* ------------------------------------------------------------------ *)
(* 【与件5 对照】x3d_le_b_mult_r_nonneg_bnd（UpReqPowMonoBridge:206）    *)
(*   前提：real_le_b a b ∧ real_le real_zero c ∧ real_le c M——c 的      *)
(*   非负与上界全 Or 形；本件 skm_le_b_mult_r_nonneg_bfree 把 c 非负    *)
(*   降为 B 形（缺口④的"仅 B 形已知"本体），c 上界保持 Or 形（skb      *)
(*   面），代价新增 a 严格正与 b ≤ 1（Or 形）——KL 场景由 powb_pos_lt   *)
(*   与 skm_powb_le_one_or 供给。强度互不支配：件5 对任意 c≤M、a 任意； *)
(*   本件对 a>0、b≤1 的几何收缩场景零 Or 形非负前提。                   *)
(* 【skb 供给位】Hkl0ub 的消费实参 = skb_sup_kl_log_inv_min nat         *)
(*   (seq 0 n) p q Hp Hq Hp1 Hnormp m Hm Hmpos 的结论面——其载体          *)
(*   real_list_sum nat (kl_term…) (seq 0 n) 与 geod_lsum n (kl_term…)   *)
(*   定义性重合（UpReqGeomD:218 geod_lsum 即该 delta），exact 一步衔接。 *)
(*   HLpos 由 m<1 面（min q<1）供给，属消费位上游证书。                  *)
(* 【主桥替换注记】i4b_policy_iter_kl_pow_mono_B 的 Hkl0or 前提位可换用 *)
(*   本件 §4 引理（Hkl0ub+HLpos 三件套），缺口④目标形即在 B 形伴件 +    *)
(*   skb 上界材料下闭合；该替换属上游改动，本件零改上游。                *)
(* 【通用性边界】抽象 a 无正性证书、b 无上界材料的④仍不可由上界材料     *)
(*   单侧攻破（交叉项需 a·eta ≥ 0 与 b·eta ≤ eta 两面），如实留档。     *)
(* ============================================================ *)

(* ============ 提取探针（Obj.magic 计数，配套 skm_g3.v） ============ *)
Extraction "skm_G3.ml" skm_powb_le_one_or skm_le_b_mult_r_nonneg_bfree
  skm_pow_kl_mono_le_b_bfree skm_policy_iter_kl_pow_mono_B_bfree.

(* ============ 自证面：Print Assumptions 假设审计 ============ *)
Print Assumptions skm_powb_le_one_or.
Print Assumptions skm_le_b_mult_r_nonneg_bfree.
Print Assumptions skm_pow_kl_mono_le_b_bfree.
Print Assumptions skm_policy_iter_kl_pow_mono_B_bfree.
