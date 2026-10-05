(* ===================================================================== *)
(*  abl_ln2_ireal.v —— ln2 无理性链·Ireal_n 的 Real 包装本体 *)
(*  使命: 链段 S6 主缺口「Ireal_n 本体」——Beukers 通道极点级数承载（lnt_ 接口）的 Real 层构造性包装：① 定义件 lnr_Ireal（nat -> Real，lnr_Ireal_pack 通用包装点）；② Cauchy 模量本体 lnr_cauchy（使用 lnt_gap_geo 几何尾界＋(3/4)^K Bernoulli 直界消失引擎 lnr_vanish；p=0 分支走 lnt_pterm_gap 的 4·u 形＋Archimedean 消失）；③ 正性/非负 Bishop 两形（lnr_Ireal_pos 严格正 / _notneg 否定形）；④ 相容闭合两件：existT 证明位异构 seal（lnr_Ireal_compat，real_eq_of_zero_diff 支）与 ri_identity_leg 迁移件（lnr_identity_leg_transfer，real_eq_trans 三实参两支）；⑤ supply 对接挂点（lni_supply_pair 改型 A_n:=L_n·q̃_n、B_n:=L_n·p_n 的线对象 lnr_lineL 与 Z 对 seal/scale 两件）。ri_identity_leg 本证（有限 M 换序恒等式）不在本件，以 lnr_identity_leg_transfer 留陈述级挂点（对接面后续施工）。§0′ 增工器件五件（预乘除正消元/除整分数 Qlt 交叉化与反单调/Qeq 传送）服务 vanish/cauchy/compat/transfer 各肢。 *)
(*  依赖: Stdlib QArith/Qabs/Arith/ZArith/Lia；S01_BaseRing S02_CauchyComplete S03_QExp；HansonLcm BeukersLists BeukersVariant RealIdentity（ri_real/ri_lineabs/ri_identity_leg 面）PsQReindex（rx_Qlt_Z1）；池内拷贝件 abl_ln2_tail_bound（lnt_pterm/lnt_gap_geo/lnt_pterm_gap——同池编译副本）。 *)
(*  对标: RealIdentity ri_Iface/ri_identity_assembly（输入面一经供给即实例化的装配件——本件即其 Ireal 输入面的首个构造性供体）；「Ireal_n 本体（I_n 的 Real 承载＋ri_identity_leg）」前半；「Ireal_n 的 Real 包装所需 Cauchy 模量＋vanish 的 Q 层输入」使用面；UpReqLn2Irrational ln2i_vanish 的消失配方。 *)
(*  构造性: 全件 Qed、零承认；语句面全 Set（cauchy/real_eq/real_lt/sigT/QeqT/QltT/QleT'），Qle/Qlt 支撑引理仅 Prop 面作推理；vanish 见证为显式 nat（N := 2p + 3·2^{p+1}·den(eps) 配方）；可提取（文尾 Separate Extraction）；文尾 Print Assumptions 全 Closed。 *)
(*  编译配方: source <toolchain>/env.sh && rocq c -native-compiler no -Q vo_local_world_unified_0930 ""（编译目录 ln2_ireal/，并发限 1；同池先编 abl_ln2_tail_bound.v）。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm BeukersLists BeukersVariant.
Require Import RealIdentity PsQReindex.
Require Import UpReqLn2Irrational.
Require Import abl_ln2_tail_bound.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 通用工器件：半乘严格缩、QeqT 桥、正性传送                            *)
(* ============================================================ *)

(* 左乘严格保序（stdlib 缺 Qmult_lt_compat_l 的本件补件） *)
Lemma lnr_qmult_lt_compat_l : forall x y z : Q,
  Qlt 0 z -> Qlt x y -> Qlt (z * x) (z * y).
Proof.
  intros x y z Hz Hxy.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_lt_compat_r; assumption.
Qed.

(* 右加保序（stdlib 缺 Qplus_le_compat_r 的本件补件） *)
Lemma lnr_Qplus_le_compat_r : forall x y z : Q,
  Qle x y -> Qle (x + z) (y + z).
Proof.
  intros x y z H. apply (Qplus_le_compat x y z z).
  - exact H.
  - apply Qle_refl.
Qed.

(* 半乘严格缩：0 < q ⟹ (1/2)·q < q *)
Lemma lnr_qhalf_lt : forall q : Q, Qlt 0 q -> Qlt ((1 # 2)%Q * q) q.
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  unfold Qlt in Hq |- *. cbn [Qnum Qden Qmult] in *.
  lia.
Qed.

(* 级数项正性的 Qle 传送（非负性核算的原子） *)
Lemma lnr_pterm_pos_Qle : forall p k : nat, Qle 0 (lnt_pterm p k).
Proof.
  intros p k. apply Qlt_le_weak. apply QltT_to_Qlt. apply lnt_pterm_pos.
Qed.

(* 2^N ≥ N+1（p=0 分支消失的 nat 桥） *)
Lemma lnr_pow2_ge1 : forall N : nat, (N + 1 <= 2 ^ N)%nat.
Proof.
  induction N as [| N IH].
  - cbn. lia.
  - cbn [Nat.pow]. assert (Hg := lnt_pow2_ge1 N). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* §0′ 工器件： *)
(*   成因：Qinv 对符号 Z 分子受阻（match (Z.of_nat _ + _) 不归约），          *)
(*   直排 lia/nia 面对不归约 match 即「Cannot find witness」。                  *)
(*   对策两类：                                                              *)
(*   ① 除正消元（lnr_qdiv_lt_intro_pre）：Qinv 经 lnt_qinv_mul_cancel        *)
(*      与 dv 自身对消，全程免 Qinv 归一化；                                  *)
(*   ② 显式 case 分裂（lnr_q3divz_lt/lnr_qdivint_antitone）：对除数 Z 分子    *)
(*      destruct 三分，矛盾支 lia 收、生存支 cbn 后纯 Z 算术。               *)
(* ------------------------------------------------------------------ *)

(* Qeq 左端传送：x == y 且 y < z ⟹ x < z *)
Lemma lnr_qlt_transfer_l : forall x y z : Q, Qeq x y -> Qlt y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. apply (Qle_lt_trans x y z).
  - apply qeq_le. exact Hxy.
  - exact Hyz.
Qed.

(* Qeq 右端传送：x < y 且 y == z ⟹ x < z *)
Lemma lnr_qlt_transfer_r : forall x y z : Q, Qlt x y -> Qeq y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. apply (Qlt_le_trans x y z).
  - exact Hxy.
  - apply qeq_le. exact Hyz.
Qed.

(* QltT 左端传送（QltT 为 Id 面无 Proper 实例：
   Qeq 不得 rewrite 进 QltT 目标，一律以传送件代之） *)
Lemma lnr_qltT_transfer_l : forall x y z : Q, Qeq x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. apply Qlt_to_QltT. apply (Qle_lt_trans x y z).
  - apply qeq_le. exact Hxy.
  - apply QltT_to_Qlt. exact Hyz.
Qed.

(* QltT 右端传送 *)
Lemma lnr_qltT_transfer_r : forall x y z : Q, Qeq y z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hxy. apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hxy.
  - apply qeq_le. exact Hyz.
Qed.

(* 预乘形除正消元：0 < dv 且 a·b < eps·dv ⟹ a·(b·dv⁻¹) < eps。
   （Qinv 不归一化：dv⁻¹·dv 对消经 lnt_qinv_mul_cancel，两支 Qeq 传送） *)
Lemma lnr_qdiv_lt_intro_pre : forall a b eps dv : Q,
  Qlt 0 dv -> Qlt (a * b) (eps * dv) -> Qlt (a * (b * Qinv dv)) eps.
Proof.
  intros a b eps dv Hdv H.
  assert (Hinv : (Qinv dv * dv)%Q == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hdv).
  apply (lnr_qlt_transfer_l _ ((a * b) * Qinv dv)%Q).
  - ring.
  - apply (lnr_qlt_transfer_r _ ((eps * dv) * Qinv dv)%Q).
    + apply Qmult_lt_compat_r.
      * apply Qinv_lt_0_compat. exact Hdv.
      * exact H.
    + transitivity (eps * (Qinv dv * dv))%Q.
      * ring.
      * rewrite Hinv. ring.
Qed.

(* 除正整数分子分数的 Qlt 交叉化（①形）：0<c、0<z、0<pn 且
   c·3·pd < pn·z ⟹ (c#1)·((3#1)/(z#1)) < (pn#pd)。
   生存支（Zpos）cbn 后即纯 Z 算术；Z0/Zneg 支由前提矛盾 lia 收。 *)
Lemma lnr_q3divz_lt : forall (c z pn : Z) (pd : positive),
  (0 < c)%Z -> (0 < z)%Z -> (0 < pn)%Z ->
  (c * 3 * Z.pos pd < pn * z)%Z ->
  Qlt ((c # 1)%Q * ((3 # 1)%Q / ((z # 1)%Q))) ((pn # pd)%Q).
Proof.
  intros c z pn pd Hc Hz Hpn H.
  unfold Qlt, Qdiv.
  destruct z as [| p | p]; cbn in Hz |- *.
  all: try lia.
  all: cbn [Qnum Qden Qmult Qinv Pos.mul]; lia.
Qed.

(* 除正整数分子分数的反单调：0<c、0<z2、z2<z1 ⟹
   (c#1)/(z1#1) < (c#1)/(z2#1)（同①对策，生存支 nia 吃 c·1 因子） *)
Lemma lnr_qdivint_antitone : forall (c z1 z2 : Z),
  (0 < c)%Z -> (0 < z2)%Z -> (z2 < z1)%Z ->
  Qlt ((c # 1)%Q / ((z1 # 1)%Q)) ((c # 1)%Q / ((z2 # 1)%Q)).
Proof.
  intros c z1 z2 Hc H2 Hlt.
  unfold Qlt, Qdiv.
  destruct z1 as [| p | p] eqn:E1; cbn in Hlt, E1 |- *;
    destruct z2 as [| q | q] eqn:E2; cbn in H2, E2 |- *.
  all: try lia.
  all: cbn [Qnum Qden Qmult Qinv Pos.mul]; nia.
Qed.

(* ============================================================ *)
(* §A Q 层承载：极点级数部分和                                             *)
(* ============================================================ *)

(* 承载序列：lnr_psum p M := Σ_{k<S M} u(p,k)，u = lnt_pterm *)
Definition lnr_psum (p M : nat) : Q := sum_upto (Datatypes.S M) (lnt_pterm p).

(* 首项读出：S_0 = u(p,0)（严格正下界基例） *)
Lemma lnr_psum_head : forall p : nat, lnr_psum p 0 == lnt_pterm p 0.
Proof.
  intro p. unfold lnr_psum. cbn [sum_upto]. ring.
Qed.

(* 部分和单调：m ≤ k ⟹ S_m ≤ S_k（逐项正性的和传送） *)
Lemma lnr_psum_mono : forall p m k : nat,
  (m <= k)%nat -> Qle (lnr_psum p m) (lnr_psum p k).
Proof.
  intros p m k H.
  assert (Hk : (k = m + (k - m))%nat) by lia.
  remember (k - m)%nat as d eqn:Hd.
  subst k. clear Hd H.
  induction d as [| d IH].
  - replace (m + 0) with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d) with (Datatypes.S (m + d)) by lia.
    unfold lnr_psum in IH |- *. cbn [sum_upto].
    apply (Qle_trans _ (sum_upto (m + d) (lnt_pterm p)
                        + lnt_pterm p (m + d))%Q).
    + exact IH.
    + apply (Qle_trans _ (sum_upto (m + d) (lnt_pterm p)
                          + lnt_pterm p (m + d) + 0)%Q).
      * apply qeq_le. ring.
      * exact (Qplus_le_compat
                 (sum_upto (m + d) (lnt_pterm p) + lnt_pterm p (m + d))%Q
                 (sum_upto (m + d) (lnt_pterm p) + lnt_pterm p (m + d))%Q
                 0%Q (lnt_pterm p (Datatypes.S (m + d)))
                 (Qle_refl _)
                 (lnr_pterm_pos_Qle p (Datatypes.S (m + d)))).
Qed.

(* 部分和恒非负 *)
Lemma lnr_psum_ge0 : forall p k : nat, Qle 0 (lnr_psum p k).
Proof.
  intros p k. apply (Qle_trans _ (lnt_pterm p 0)).
  - apply lnr_pterm_pos_Qle.
  - rewrite <- (lnr_psum_head p). apply lnr_psum_mono. lia.
Qed.

(* ============================================================ *)
(* §B 几何消失引擎：(3/4)^K 的 Bernoulli 直界与模量消失                     *)
(* ============================================================ *)

(* Bernoulli 直界：(3/4)^K ≤ 3/(K+3)（归纳：9(K+4) ≤ 12(K+3)） *)
Lemma lnr_q34_pow_le3 : forall K : nat,
  Qle (q_pow (3 # 4)%Q K) ((3 # 1)%Q / ((Z.of_nat K + 3) # 1)%Q)%Q.
Proof.
  induction K as [| K IH].
  - cbn [q_pow]. unfold Qle, Qdiv. cbn. lia.
  - rewrite q_pow_succ.
    apply (Qle_trans _ ((3 # 4)%Q * ((3 # 1)%Q / ((Z.of_nat K + 3) # 1)%Q))%Q).
    + apply lnt_Qmult_le_compat_l.
      * apply Qlt_le_weak. apply rx_Qlt_Z1. lia.
      * exact IH.
    + unfold Qle, Qdiv.
      destruct (Z.of_nat K + 3)%Z as [| p1 | p1] eqn:E1; cbn in E1 |- *;
        destruct (Z.of_nat (Datatypes.S K) + 3)%Z as [| p2 | p2] eqn:E2;
          cbn in E2 |- *.
      all: try lia.
      all: cbn [Qnum Qden Qmult Qinv Pos.mul]; lia.
Qed.

(* 几何尾界形：g(p,m) := 2^{p+1}·(3/4)^{S m − 2p}（= lnt_gap_geo 尾项原形） *)
Definition lnr_gapbound (p m : nat) : Q :=
  (q_pow (2 # 1)%Q (Datatypes.S p) * q_pow (3 # 4)%Q (Datatypes.S m - 2 * p))%Q.

(* 消失引擎（p ≥ 1 窗）：显式配方 N := 2p + 3·2^{p+1}·den(eps)。
   链：g ≤ 2^{p+1}·3/(E+3) < 2^{p+1}·3/(K₀+3) = 3·2^{p+1}/(3·2^{p+1}·pd+3)
       < 1/pd ≤ eps（E := S m − 2p ≥ K₀+1）。 *)
Theorem lnr_vanish : forall (p : nat) (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, (N <= m)%nat -> QltT (lnr_gapbound p m) eps).
Proof.
  intros p [pn pd] Heps.
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (2 * p + (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd)))%nat.
  intros m Hm.
  assert (HE : (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd) + 1
                <= Datatypes.S m - 2 * p)%nat) by lia.
  assert (HA1 : (0 < Z.of_nat (2 ^ Datatypes.S p))%Z).
  { apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S p))).
    assert (Hg := lnt_pow2_ge1 (Datatypes.S p)). lia. }
  assert (HApos : Qlt 0 ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q))
    by (apply rx_Qlt_Z1; exact HA1).
  assert (HAw : (1 <= Z.of_nat (2 ^ Datatypes.S p))%Z) by lia.
  assert (HZK : (Z.of_nat (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd))
                = 3 * Z.of_nat (2 ^ Datatypes.S p) * Z.pos pd)%Z).
  { rewrite (Nat2Z.inj_mul (3 * 2 ^ Datatypes.S p) (Z.to_nat (Z.pos pd))).
    rewrite (Z2Nat.id (Z.pos pd)) by lia.
    rewrite (Nat2Z.inj_mul 3 (2 ^ Datatypes.S p)). lia. }
  apply Qlt_to_QltT.
  unfold lnr_gapbound. rewrite lnt_qpow_Zofnat.
  apply (Qlt_trans _ ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q
                      * ((3 # 1)%Q / ((Z.of_nat (3 * 2 ^ Datatypes.S p
                                            * Z.to_nat (Z.pos pd)) + 3) # 1)%Q))%Q).
  - apply (Qle_lt_trans _ ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q
                           * ((3 # 1)%Q / ((Z.of_nat (Datatypes.S m - 2 * p) + 3) # 1)%Q))%Q).
    + apply lnt_Qmult_le_compat_l.
      * apply Qlt_le_weak. exact HApos.
      * apply lnr_q34_pow_le3.
    + apply lnr_qmult_lt_compat_l.
      * exact HApos.
      * (* 3/(z1+3) < 3/(z2+3)：HE 给 z2+3 < z1+3，反单调工器件闭合 *)
        apply lnr_qdivint_antitone.
        -- lia.
        -- lia.
        -- lia.
  - (* (A#1)·((3#1)/(z2+3)) < (pn#pd)：除整 Qlt 交叉化工器件闭合 *)
    apply (lnr_q3divz_lt (Z.of_nat (2 ^ Datatypes.S p))
            (Z.of_nat (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd)) + 3)%Z
            pn pd).
    + exact HA1.
    + lia.
    + exact Hpn.
    + rewrite HZK. nia.
Qed.

(* ============================================================ *)
(* §C Cauchy 模量（lnt_gap_geo / lnt_pterm_gap 对接）与包装本体              *)
(* ============================================================ *)

(* p ≥ 1 加法形模量：S_{M+d} − S_M ≤ 2^{p+1}·(3/4)^{S M − 2p} *)
Lemma lnr_gap_modulus : forall (p M d : nat),
  (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
  QleT' (lnr_psum p (M + d) - lnr_psum p M)%Q (lnr_gapbound p M).
Proof.
  intros p M d Hp HM.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (lnr_psum p M + lnr_gapbound p M - lnr_psum p M)%Q).
  - apply (Qplus_le_compat (lnr_psum p (M + d))
                           (lnr_psum p M + lnr_gapbound p M)%Q
                           (- lnr_psum p M)%Q (- lnr_psum p M)%Q).
    + apply QleT'_to_Qle. exact (lnt_gap_geo p M d Hp HM).
    + apply Qle_refl.
  - apply qeq_le. ring.
Qed.

(* p = 0 加法形模量：S_{M+d} − S_0 ≤ 4·u(0,S M)（lnt_pterm_gap 全 p 形） *)
Lemma lnr_gap_mod0 : forall (M d : nat),
  QleT' (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q
        ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q.
Proof.
  intros M d.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (lnr_psum 0 M + (4 # 1)%Q * lnt_pterm 0 (Datatypes.S M)
                      - lnr_psum 0 M)%Q).
  - apply (Qplus_le_compat (lnr_psum 0 (M + d))
                           (lnr_psum 0 M + (4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q
                           (- lnr_psum 0 M)%Q (- lnr_psum 0 M)%Q).
    + apply QleT'_to_Qle. exact (lnt_pterm_gap 0 M d ltac:(lia)).
    + apply Qle_refl.
  - apply qeq_le. ring.
Qed.

(* ★ 本体①：承载序列的 Cauchy 性（p ≥ 1 几何档 / p = 0 Archimedean 档） *)
Theorem lnr_cauchy : forall p : nat, cauchy (lnr_psum p).
Proof.
  intro p. destruct p as [| p'].
  - (* p = 0：g ≤ 4·u(0,S M) = 4/((M+2)·2^{M+2})，N := 2·den(eps) *)
    intros eps Heps.
    destruct eps as [pn pd].
    pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
    unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
    assert (Hpn : (0 < pn)%Z) by lia.
    assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
    exists (2 * Z.to_nat (Z.pos pd)).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum 0 m - lnr_psum 0 n)%Q
                     == (lnr_psum 0 m - lnr_psum 0 n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lnr_psum 0 n - lnr_psum 0 n)%Q).
        - apply qeq_le. ring.
        - apply (Qplus_le_compat (lnr_psum 0 n) (lnr_psum 0 m)
                                 (- lnr_psum 0 n)%Q (- lnr_psum 0 n)%Q).
          + apply lnr_psum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S n))%Q).
      * apply QleT'_to_Qle. apply lnr_gap_mod0.
      * assert (HM2 : (2 * Z.to_nat (Z.pos pd) <= Datatypes.S n)%nat) by lia.
        assert (Eb : bkC (0 + Datatypes.S n) 0 = 1%nat) by reflexivity.
        assert (Hw2z : (2 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z).
        { assert (Hw2 : (2 <= 2 ^ Datatypes.S (Datatypes.S n))%nat).
          { assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S n))).
            cbn [Nat.pow] in Hg |- *. lia. }
          apply (proj1 (Nat2Z.inj_le 2 (2 ^ Datatypes.S (Datatypes.S n)))).
          exact Hw2. }
        assert (Hmul : (2 * Z.of_nat (Datatypes.S (Datatypes.S n))
                        <= Z.of_nat (Datatypes.S (Datatypes.S n))
                          * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z) by nia.
        unfold lnt_pterm, Qdiv.
        rewrite Eb, lnt_qpow_Zofnat.
        apply (lnr_qdiv_lt_intro_pre ((4 # 1)%Q) ((Z.of_nat 1 # 1)%Q)
                                     ((pn # pd)%Q)
                                     (((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)%Q
                                       * ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) # 1)%Q)%Q))).
        -- apply Qmult_lt_0_compat.
           ++ apply rx_Qlt_Z1. lia.
           ++ apply rx_Qlt_Z1.
              apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S (Datatypes.S n)))).
              assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S n))). lia.
        -- unfold Qlt. change (Z.of_nat 1) with 1%Z.
           cbn [Qnum Qden Qmult Pos.mul]. rewrite Pos.mul_1_r.
           assert (HM : (Z.of_nat (Datatypes.S (Datatypes.S n))
                         * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                         <= pn * (Z.of_nat (Datatypes.S (Datatypes.S n))
                                  * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))))%Z) by nia.
           lia.
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum 0 m - lnr_psum 0 n)%Q
                     == (lnr_psum 0 n - lnr_psum 0 m)%Q).
      { assert (Hmono : Qle (lnr_psum 0 m) (lnr_psum 0 n))
          by (apply lnr_psum_mono; lia).
        assert (Hneg : Qle (lnr_psum 0 m - lnr_psum 0 n)%Q 0%Q).
        { apply (Qle_trans _ (lnr_psum 0 n - lnr_psum 0 n)%Q).
          - apply (Qplus_le_compat (lnr_psum 0 m) (lnr_psum 0 n)
                                   (- lnr_psum 0 n)%Q (- lnr_psum 0 n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply qeq_le. ring. }
        apply Qeq_trans with (-(lnr_psum 0 m - lnr_psum 0 n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S m))%Q).
      * apply QleT'_to_Qle. apply lnr_gap_mod0.
      * assert (HM2 : (2 * Z.to_nat (Z.pos pd) <= Datatypes.S m)%nat) by lia.
        assert (Eb : bkC (0 + Datatypes.S m) 0 = 1%nat) by reflexivity.
        assert (Hw2z : (2 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)))%Z).
        { assert (Hw2 : (2 <= 2 ^ Datatypes.S (Datatypes.S m))%nat).
          { assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S m))).
            cbn [Nat.pow] in Hg |- *. lia. }
          apply (proj1 (Nat2Z.inj_le 2 (2 ^ Datatypes.S (Datatypes.S m)))).
          exact Hw2. }
        assert (Hmul : (2 * Z.of_nat (Datatypes.S (Datatypes.S m))
                        <= Z.of_nat (Datatypes.S (Datatypes.S m))
                          * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)))%Z) by nia.
        unfold lnt_pterm, Qdiv.
        rewrite Eb, lnt_qpow_Zofnat.
        apply (lnr_qdiv_lt_intro_pre ((4 # 1)%Q) ((Z.of_nat 1 # 1)%Q)
                                     ((pn # pd)%Q)
                                     (((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                                       * ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)) # 1)%Q)%Q))).
        -- apply Qmult_lt_0_compat.
           ++ apply rx_Qlt_Z1. lia.
           ++ apply rx_Qlt_Z1.
              apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S (Datatypes.S m)))).
              assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S m))). lia.
        -- unfold Qlt. change (Z.of_nat 1) with 1%Z.
           cbn [Qnum Qden Qmult Pos.mul]. rewrite Pos.mul_1_r.
           assert (HM : (Z.of_nat (Datatypes.S (Datatypes.S m))
                         * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m))
                         <= pn * (Z.of_nat (Datatypes.S (Datatypes.S m))
                                  * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m))))%Z) by nia.
           lia.
  - (* p = S p' ≥ 1：几何档（lnt_gap_geo + lnr_vanish） *)
    intros eps Heps.
    destruct (lnr_vanish (Datatypes.S p') eps Heps) as [N Hv].
    exists (Nat.max N (2 * Datatypes.S p')).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q
                     == (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lnr_psum (Datatypes.S p') n - lnr_psum (Datatypes.S p') n)%Q).
        - apply qeq_le. ring.
        - apply (Qplus_le_compat (lnr_psum (Datatypes.S p') n) (lnr_psum (Datatypes.S p') m)
                                 (- lnr_psum (Datatypes.S p') n)%Q (- lnr_psum (Datatypes.S p') n)%Q).
          + apply lnr_psum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ (lnr_gapbound (Datatypes.S p') n)).
      * apply QleT'_to_Qle. apply lnr_gap_modulus; lia.
      * apply QltT_to_Qlt. apply Hv. lia.
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q
                     == (lnr_psum (Datatypes.S p') n - lnr_psum (Datatypes.S p') m)%Q).
      { assert (Hmono : Qle (lnr_psum (Datatypes.S p') m) (lnr_psum (Datatypes.S p') n))
          by (apply lnr_psum_mono; lia).
        assert (Hneg : Qle (lnr_psum (Datatypes.S p') m
                            - lnr_psum (Datatypes.S p') n)%Q 0%Q).
        { apply (Qle_trans _ (lnr_psum (Datatypes.S p') n
                              - lnr_psum (Datatypes.S p') n)%Q).
          - apply (Qplus_le_compat (lnr_psum (Datatypes.S p') m)
                                   (lnr_psum (Datatypes.S p') n)
                                   (- lnr_psum (Datatypes.S p') n)%Q
                                   (- lnr_psum (Datatypes.S p') n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply qeq_le. ring. }
        apply Qeq_trans with (-(lnr_psum (Datatypes.S p') m
                                 - lnr_psum (Datatypes.S p') n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ (lnr_gapbound (Datatypes.S p') m)).
      * apply QleT'_to_Qle. apply lnr_gap_modulus; lia.
      * apply QltT_to_Qlt. apply Hv. lia.
Qed.

(* 通用包装点：任意柯西有理序列的 Real 包装（existT 证明位自由） *)
Definition lnr_Ireal_pack (u : Qseq) (Hu : cauchy u) : Real :=
  existT (fun u : Qseq => cauchy u) u Hu.

(* ★ 本体②：Ireal_n 定义件——极点级数承载的 Real 包装 *)
Definition lnr_Ireal (p : nat) : Real := lnr_Ireal_pack (lnr_psum p) (lnr_cauchy p).

(* 投影读出：包装不改变逐点读数 *)
Lemma lnr_Ireal_proj : forall (p k : nat), projT1 (lnr_Ireal p) k == lnr_psum p k.
Proof. intros p k. reflexivity. Qed.

(* ★ 相容闭合（第一支，real_eq_of_zero_diff）：任何以同一 Q 层承载为读数、
   自备 Cauchy 见证的再包装，与 lnr_Ireal p 实数相等——existT 证明位异构的 seal *)
Lemma lnr_Ireal_compat : forall (p : nat) (u : Qseq) (Hu : cauchy u),
  (forall k : nat, u k == lnr_psum p k) ->
  real_eq (lnr_Ireal_pack u Hu) (lnr_Ireal p).
Proof.
  intros p u Hu H. apply real_eq_of_zero_diff. intro k.
  unfold lnr_Ireal, lnr_Ireal_pack. cbn [projT1]. rewrite (H k). ring.
Qed.

(* ============================================================ *)
(* §D 正性/非负（Bishop 两形）                                             *)
(* ============================================================ *)

(* ★ 本体③（严格正）：real_zero < Ireal_n，分离见证 eps := (1/2)·u(p,0) *)
Theorem lnr_Ireal_pos : forall p : nat, real_lt real_zero (lnr_Ireal p).
Proof.
  intro p.
  assert (Hpt0 : Qlt 0 (lnt_pterm p 0)) by (apply QltT_to_Qlt; apply lnt_pterm_pos).
  exists ((1 # 2)%Q * lnt_pterm p 0)%Q.
  split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + exact Hpt0.
  - exists 0%nat. intros k Hk.
    apply NatLe_drop in Hk.
    unfold lnr_Ireal, lnr_Ireal_pack, real_zero. cbn [projT1].
    assert (Ez : lnr_psum p k == (lnr_psum p k - 0)%Q) by ring.
    apply (lnr_qltT_transfer_r _ _ _ Ez).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1 # 2)%Q * lnt_pterm p 0)%Q (lnt_pterm p 0)
                        (lnr_psum p k)).
    + apply lnr_qhalf_lt. exact Hpt0.
    + rewrite <- (lnr_psum_head p). apply lnr_psum_mono. lia.
Qed.

(* ★ 本体③（否定形）：Not (Ireal_n < 0)——由严格正经反自反传送 *)
Theorem lnr_Ireal_notneg : forall p : nat, Not (real_lt (lnr_Ireal p) real_zero).
Proof.
  intros p Hlt.
  apply (real_lt_irrefl (lnr_Ireal p)).
  exact (real_lt_trans (lnr_Ireal p) real_zero (lnr_Ireal p) Hlt (lnr_Ireal_pos p)).
Qed.

(* ★ 相容闭合（第二支，real_eq_trans 三实参两支）：
   ri_identity_leg 沿 real_eq 迁移——任何与 lnr_Ireal p 实数相等的再包装，
   只要在 lnr_Ireal p 上证得恒等式支，即得自身上的恒等式支（S6 对接主挂点：
   有限 M 换序证明于 lnr_Ireal 面的 ri_identity_leg 后，合成面任意取形） *)
Theorem lnr_identity_leg_transfer : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnr_Ireal p)) ->
  ri_identity_leg lnr_Ireal -> ri_identity_leg I.
Proof.
  intros I HI Hleg n.
  apply (real_eq_trans (I n) (lnr_Ireal n) (ri_lineabs n)).
  - apply HI.
  - apply Hleg.
Qed.

(* ============================================================ *)
(* §E supply 对接挂点（lni_supply_pair 改型 A_n := L_n·q̃_n、B_n := L_n·p_n） *)
(* ============================================================ *)

(* 改型分子对（Q 面，与前件 lni_supply_pair 见证 z#1/w#1 的 QeqT 对形） *)
Definition lnr_lA (n : nat) : Q :=
  (Z.of_nat (hl_lcm_upto n) # 1)%Q * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.
Definition lnr_lB (n : nat) : Q :=
  (Z.of_nat (hl_lcm_upto n) # 1)%Q * bv_p n.

(* 改型线对象（X := ri_real）：lnr_lineL = |L·q̃·X − L·p|，归一基线 lnr_lineq *)
Definition lnr_lineq (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)) ri_real)
                      (real_opp (real_const (bv_p n)))).
Definition lnr_lineL (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const (lnr_lA n)) ri_real)
                      (real_opp (real_const (lnr_lB n)))).

Lemma lnr_lineL_proj : forall (n k : nat),
  projT1 (lnr_lineL n) k == Qabs ((lnr_lA n * ln2i_x k - lnr_lB n)%Q).
Proof.
  intros n k. unfold lnr_lineL.
  rewrite real_abs_proj, real_plus_proj, real_mult_const_proj, real_opp_proj,
          real_const_proj, ri_real_proj.
  reflexivity.
Qed.

(* lcm(1..n) ≥ 1（线缩放的正性前提；gcd 整除 witnesses 显式构造） *)
Lemma lnr_hlcm_ge1 : forall n : nat, (1 <= hl_lcm_upto n)%nat.
Proof.
  induction n as [| m IH].
  - cbn. lia.
  - cbn [hl_lcm_upto].
    assert (Hdiv : Nat.divide (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)) (Datatypes.S m))
      by apply Nat.gcd_divide_r.
    destruct Hdiv as [k Hk].
    assert (Hk0 : (k <> 0)%nat).
    { intro Hk0. subst k. rewrite Nat.mul_0_l in Hk. discriminate. }
    assert (Hk1 : (1 <= k)%nat) by lia.
    assert (Hg0 : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m) <> 0)%nat).
    { intro Hg. rewrite Hg, Nat.mul_0_r in Hk. discriminate. }
    assert (Hgpos : (0 < Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat)
      by (apply Nat.neq_0_lt_0; exact Hg0).
    assert (Hgle : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m) <= Datatypes.S m)%nat).
    { pose proof (Nat.gcd_divide_r (hl_lcm_upto m) (Datatypes.S m)) as Hdv.
      destruct Hdv as [t Ht].
      assert (Ht0 : (0 < t)%nat).
      { apply Nat.neq_0_lt_0. intro Ht0. subst t.
        rewrite Nat.mul_0_l in Ht. discriminate. }
      assert (Hleg1 : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)
                       <= t * Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat).
      { pose proof (Nat.mul_le_mono_r 1 t
                      (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)) Ht0) as Hx.
        rewrite Nat.mul_1_l in Hx. exact Hx. }
      apply (Nat.le_trans _ (t * Nat.gcd (hl_lcm_upto m) (Datatypes.S m))).
      - exact Hleg1.
      - rewrite <- Ht. apply Nat.le_refl. }
    assert (Hd1 : (0 < Datatypes.S m / Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat)
      by (apply Nat.div_str_pos; split; lia).
    unfold Nat.lcm. nia.
Qed.

(* ★ supply 挂点一（Z 对 seal）：lni_supply_pair 见证 (z,w) 经 QeqT 对形后，
   线对象逐点等于整数系数线——合成面可用 z,w 直读 *)
Lemma lnr_supply_pair_hook : forall (n : nat) (z w : Z),
  QeqT (lnr_lA n) ((z # 1)%Q) -> QeqT (lnr_lB n) ((w # 1)%Q) ->
  real_eq (lnr_lineL n)
          (real_abs (real_plus (real_mult (real_const ((z # 1)%Q)) ri_real)
                               (real_opp (real_const ((w # 1)%Q))))).
Proof.
  intros n z w Hz Hw. apply real_eq_of_zero_diff. intro k.
  rewrite lnr_lineL_proj.
  assert (E2 : projT1 (real_abs (real_plus (real_mult (real_const ((z # 1)%Q)) ri_real)
                                           (real_opp (real_const ((w # 1)%Q))))) k
               == Qabs (((z # 1)%Q * ln2i_x k - (w # 1)%Q)%Q)).
  { rewrite real_abs_proj, real_plus_proj, real_mult_const_proj, real_opp_proj,
            real_const_proj, ri_real_proj. reflexivity. }
  rewrite E2.
  setoid_rewrite (qeqT_imp_qeq _ _ Hz).
  setoid_rewrite (qeqT_imp_qeq _ _ Hw).
  ring.
Qed.

(* ★ supply 挂点二（L 线缩放）：|L·q̃·X − L·p| == L·|q̃·X − p|
   （L := lcm(1..n) > 0；θ 档预算与 clo 下界的归一基线） *)
Lemma lnr_lineL_scale : forall n : nat,
  real_eq (lnr_lineL n)
          (real_mult (real_const ((Z.of_nat (hl_lcm_upto n) # 1)%Q)) (lnr_lineq n)).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  assert (HLM : Qlt 0 ((Z.of_nat (hl_lcm_upto n) # 1)%Q)).
  { apply rx_Qlt_Z1.
    apply (proj1 (Nat2Z.inj_lt 0 (hl_lcm_upto n))). apply lnr_hlcm_ge1. }
  assert (Hcore : Qabs ((lnr_lA n * ln2i_x k - lnr_lB n)%Q)
                  == (Z.of_nat (hl_lcm_upto n) # 1)%Q
                       * Qabs ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q * ln2i_x k - bv_p n)%Q).
  { unfold lnr_lA, lnr_lB.
    apply (Qeq_trans _ (Qabs (((Z.of_nat (hl_lcm_upto n) # 1)%Q
                               * ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q * ln2i_x k - bv_p n))%Q))).
    - apply Qabs_wd. ring.
    - rewrite Qabs_Qmult.
      rewrite (Qabs_pos (Z.of_nat (hl_lcm_upto n) # 1)%Q (Qlt_le_weak _ _ HLM)).
      ring. }
  rewrite lnr_lineL_proj.
  assert (E2 : projT1 (real_mult (real_const ((Z.of_nat (hl_lcm_upto n) # 1)%Q))
                                 (lnr_lineq n)) k
               == (Z.of_nat (hl_lcm_upto n) # 1)%Q
                    * Qabs ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q * ln2i_x k - bv_p n)%Q).
  { unfold lnr_lineq.
    rewrite real_mult_const_proj, real_abs_proj, real_plus_proj,
            real_mult_const_proj, real_opp_proj, real_const_proj, ri_real_proj.
    reflexivity. }
  rewrite E2, Hcore. ring.
Qed.

(* ============================================================ *)
(* §F 数值判定组（vm_compute 经投影精确判定）                                 *)
(* ============================================================ *)

(* 承载判定（p=1 几何档首四项 1/2+1/4+1/8+1/16 = 15/16） *)
Theorem lnr_psum1_anchor : QeqT (lnr_psum 1 3) (15 # 16)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 承载判定（p=0 前三项 1/2+1/8+1/24 = 2/3） *)
Theorem lnr_psum0_anchor : QeqT (lnr_psum 0 2) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 尾界判定（g(1,1) = 2²·(3/4)⁰ = 4） *)
Theorem lnr_gapbound1_anchor : QeqT (lnr_gapbound 1 1) (4 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 改型分子对判定（实算定装：L_1=hl_lcm_upto 1=1, q̃_1=3, p_1=bv_p 1=4#2
   ⟹ A_1=3、B_1=4#2）——QeqT 面 Set 级，不得入 Prop 合取（Set/Prop 混层），
   拆为两件；前稿 A_1=6/B_1=4 系 L_n 错位编号的臆值，本件实算勘正 *)
Theorem lnr_lA1_anchor : QeqT (lnr_lA 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lnr_lB1_anchor : QeqT (lnr_lB 1) (4 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 可提取验证（Set 层 witness 面）                                          *)
(* ============================================================ *)

Separate Extraction lnr_psum lnr_gapbound lnr_lA lnr_lB.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。          *)
(* ============================================================ *)

Print Assumptions lnr_cauchy.
Print Assumptions lnr_Ireal_compat.
Print Assumptions lnr_Ireal_pos.
Print Assumptions lnr_Ireal_notneg.
Print Assumptions lnr_identity_leg_transfer.
Print Assumptions lnr_supply_pair_hook.
Print Assumptions lnr_lineL_scale.
Print Assumptions lnr_gap_modulus.
Print Assumptions lnr_gap_mod0.
Print Assumptions lnr_vanish.
Print Assumptions lnr_hlcm_ge1.
Print Assumptions lnr_q34_pow_le3.
Print Assumptions lnr_psum1_anchor.
Print Assumptions lnr_gapbound1_anchor.
