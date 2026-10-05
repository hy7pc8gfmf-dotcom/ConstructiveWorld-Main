(* ===================================================================== *)
(*  abl_ln2_numer_int.v —— ln2 无理性链·真分子族整化核件 *)
(*  使命: sa_supply_rem' 改型下「改型分子 B·L_n 的整除供给」——定理草案 bvp_lcm_int 的闭合（最小核件）：改型分子 B_n := L_n·p_n ∈ Z 的整性见证直证（p_n := bv_p n 为 BeukersVariant 的 Laurent 闭式真分子，L_n := hl_lcm_upto n）。数学内容: bv_p n = −Σ_{j<S(2n), j≠n} c_j·(2^{j−n}−1)/(j−n)，其中 *)
(*        (i) j<n 段: c_j = (−1)^{n+j}·2^{n−j}·T_j（T_j = Σ_{a≤j} C(n,a)·C(n,j−a)·2^a ∈ Z，2 幂因子逐项提出），与 (2^{−d}−1)/(−d) = (2^d−1)/(d·2^d) 相乘后 2^d 恰好对消 ⟹ T_j·(2^d−1)/d； *)
(*        (ii) j>n 段: c_j = (−1)^{n+j}·S_j（S_j = Σ_{d≤a≤n} C(n,a)·C(n,j−a)·2^{a−d} ∈ Z 直接整），项为 S_j·(2^d−1)/d； *)
(*        (iii) 两段分母 d = |j−n| ∈ [1,n] 全被 L_n 整除（hl_lcm_divide_all），故 L_n·bv_p n = ±Σ (L_n/d)·U_j·(2^d−1) ∈ Z。谐和形先例 pi_Pn_int 为同型模板（Ln2Integrality 全套 pi_ 工具直接使用）。另交付 A 侧平凡肢 L_n·q̃_n ∈ Z（bk_Qmul_nat 一步）与改型分子对 (A·L_n, B·L_n) 的合成交付面 lni_supply_pair（sa_supply_rem' 改型参数化 A_n := L_n·q̃_n、B_n := L_n·p_n 的 Z 面整备，合成前置件）；θ 档预算另见 abl_ln2_tail_bound（lnt_gap_geo）。 *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists HansonLcm BeukersVariant Ln2Integrality（与检验件 abl_ln2_numer_probe.v 同一导入形态）。 *)
(*  对标: Ln2Integrality pi_Pn_int（谐和变体整化主件——本件为其真分子族对应物，被机器证伪判定③否证的 2 幂归一形的唯一可行替代，TrueNumerator 判定 r₃=2096/3 非整）；Ln2Bridge ln2b_escape_of_supply 前提的 sa_supply_rem' 改型对应件；abl_SupplyRemRefuted_07 证伪后的重构。 *)
(*  构造性: 全件 Qed、零承认、零经典逻辑；主件语句面 sigT/QeqT（Set 层），nat/Z 支撑引理仅作推理；见证全显式（Z 级有限和 lni_zsum 承载），可提取；Qeq 改写一律避开 Qminus/Qopp 嵌位（Qmult/Qplus 下改写有 pi_hsum_spec 先例背书，Qopp 传送走自证 lni_Qopp_cong/lni_QoppZ 数值路线）；文尾 Print Assumptions 取证块全 Closed（验收证据之一）。 *)
(*  编译配方: source <toolchain>/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && 编译目录 ln2_numer/ && nice -19 rocq c -native-compiler no -Q vo_local_world_unified_0930 "" 本件；并发限 1；编译通过后清理本件 .vo/.glob（abl_ln2_numer_probe.v 产物保留）。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm BeukersVariant Ln2Integrality.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 Q 层微桥（Qmult/Qplus 传送走 setoid 改写；Qopp 传送走数值路线）      *)
(* ============================================================ *)

(* Qeq 在 Qopp 下的传送（unfold Qeq 后 Z 层 ring，零 setoid 依赖） *)
Lemma lni_Qopp_cong : forall x y : Q, x == y -> (Qopp x) == (Qopp y).
Proof.
  intros x y H. unfold Qeq in *. cbn [Qopp Qnum Qden] in *.
  transitivity (Z.opp (Qnum x * Z.pos (Qden y))).
  - ring.
  - rewrite H. ring.
Qed.

(* Qopp 对整数值 Q 的显式形：Qopp (u#1) == (−u)#1（Qopp := (-Qnum x)#(Qden x) 定义面直算） *)
Lemma lni_QoppZ : forall u : Z, (Qopp (u # 1))%Q == ((Z.opp u) # 1)%Q.
Proof.
  intro u. unfold Qeq. cbn [Qopp Qnum Qden Pos.mul]. ring.
Qed.

(* Qeq 在乘法/加法/减法/除法下的传送（Qmult/Qplus 嵌位有 pi_hsum_spec 先例背书） *)
Lemma lni_Qmul_cong_r : forall x y z : Q, x == y -> (x * z) == (y * z).
Proof.
  intros x y z H. rewrite H. reflexivity.
Qed.

Lemma lni_Qmul_cong_l : forall x y z : Q, x == y -> (z * x) == (z * y).
Proof.
  intros x y z H. rewrite H. reflexivity.
Qed.

Lemma lni_Qplus_cong_l : forall x y c : Q, x == y -> (c + x) == (c + y).
Proof.
  intros x y c H. rewrite H. reflexivity.
Qed.

Lemma lni_Qminus_cong_l : forall x y c : Q, x == y -> (x - c) == (y - c).
Proof.
  intros x y c H. unfold Qminus. rewrite H. reflexivity.
Qed.

Lemma lni_Qdiv_cong_l : forall x y z : Q, x == y -> (x / z) == (y / z).
Proof.
  intros x y z H. unfold Qdiv. rewrite H. reflexivity.
Qed.

(* Z 数值桥：整数值 Q 的乘/加/减 *)
Lemma lni_QmulZ : forall u v : Z, ((u # 1) * (v # 1))%Q == ((u * v) # 1)%Q.
Proof.
  intros u v. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

Lemma lni_QaddZ : forall u v : Z, ((u # 1) + (v # 1))%Q == ((u + v) # 1)%Q.
Proof.
  intros u v. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring.
Qed.

Lemma lni_QsubZ : forall u v : Z, ((u # 1) - (v # 1))%Q == ((u - v) # 1)%Q.
Proof.
  intros u v. unfold Qeq, Qminus. cbn [Qopp Qnum Qden Qplus Pos.mul]. ring.
Qed.

(* q_pow 两个具体底数的 nat 闭式桥 *)
Lemma lni_qpow1 : forall N : nat, q_pow (1 # 1)%Q N == 1%Q.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma lni_qpow2_nat : forall k : nat, q_pow (2 # 1)%Q k == ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH.
    transitivity (((Z.of_nat 2) # 1) * ((Z.of_nat (2 ^ k)) # 1))%Q.
    { reflexivity. }
    rewrite bk_Qmul_nat. cbn [Nat.pow]. reflexivity.
Qed.

(* 负分母倒数的符号外出（零支数值直算；非零支 Cancellation，前提由 Qmult_inv_r 双侧供给） *)
Lemma lni_qinv_opp : forall u : Z, (/ (Qopp (u # 1)))%Q == (Qopp (/ (u # 1)))%Q.
Proof.
  intro u.
  destruct (Z.eq_dec u 0) as [Hu0 | Hne].
  - subst u. vm_compute. reflexivity.
  - assert (Hu : ~ ((u # 1) == 0)%Q).
    { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
      rewrite !Z.mul_1_r in Hc. lia. }
    assert (Hnz : ~ (Qopp (u # 1) == 0)%Q).
    { intro H0. unfold Qeq in H0. cbn [Qopp Qnum Qden] in H0.
      rewrite !Z.mul_1_r in H0.
      apply Hu. unfold Qeq. cbn [Qnum Qden]. rewrite !Z.mul_1_r. lia. }
    apply (pi_Qmul_cancel_r_to ((/ (Qopp (u # 1)))) ((Qopp (/ (u # 1))))
                               ((Qopp (u # 1)))).
    + exact Hnz.
    + transitivity (1%Q).
      * rewrite Qmult_comm. exact (Qmult_inv_r (Qopp (u # 1)) Hnz).
      * transitivity ((u # 1) * (/ (u # 1)))%Q.
        -- symmetry. exact (Qmult_inv_r (u # 1) Hu).
        -- ring.
Qed.

(* 唯一性引理：x·(1/x − 1) == 1 − x（低段 2 幂对消的核心代数件） *)
Lemma lni_qmul_inv_sub : forall x : Q, ~ (x == 0)%Q -> (x * ((/ x) - 1))%Q == (1%Q - x)%Q.
Proof.
  intros x Hx.
  assert (Hinv : (x * (/ x))%Q == 1%Q) by (apply Qmult_inv_r; exact Hx).
  apply (proj1 (Qplus_inj_r (x * ((/ x) - 1)) (1%Q - x) x)).
  transitivity (1%Q).
  - transitivity (x * (/ x))%Q.
    + ring.
    + exact Hinv.
  - ring.
Qed.

(* bv_negpow（(−1)^s 的 Q 承载）乘整数值 Q 后仍整，见证显式 *)
Lemma lni_negpow_Zmul : forall (s : nat) (u : Z),
  sigT (fun u' : Z => (bv_negpow s * (u # 1))%Q == ((u' # 1)%Q)).
Proof.
  induction s as [| s IH]; intro u.
  - exists u. cbn [bv_negpow]. ring.
  - destruct (IH u) as [u' Hu'].
    exists (Z.opp u').
    cbn [bv_negpow].
    transitivity ((Qopp (bv_negpow s * (u # 1)))%Q).
    { ring. }
    transitivity ((Qopp ((u' # 1)%Q))).
    { apply lni_Qopp_cong. exact Hu'. }
    apply lni_QoppZ.
Qed.

(* ============================================================ *)
(* §1 有限和承载：bk_psQ(·,N,1) 的逐项整化 ⟹ 整体整化                     *)
(* ============================================================ *)

Lemma lni_psQ_zsum_ex : forall (N : nat) (f : nat -> Q),
  (forall k : nat, k < N -> sigT (fun z : Z => f k == ((z # 1)%Q))) ->
  sigT (fun z : Z => bk_psQ f N 1%Q == ((z # 1)%Q)).
Proof.
  induction N as [| N IH]; intros f H.
  - exists 0%Z. cbn [bk_psQ]. ring.
  - assert (Hpre : forall k : nat, k < N -> sigT (fun z : Z => f k == ((z # 1)%Q))).
    { intros k Hk. apply H. lia. }
    destruct (IH f Hpre) as [z0 Hz0].
    destruct (H N (Nat.lt_succ_diag_r N)) as [z1 Hz1].
    exists (z0 + z1)%Z.
    cbn [bk_psQ].
    rewrite (lni_qpow1 N).
    rewrite Hz0, Hz1.
    transitivity (((z0 # 1)%Q + (z1 # 1)%Q)%Q).
    { ring. }
    apply lni_QaddZ.
Qed.

(* ============================================================ *)
(* §2 bv_c 分段闭式（真分子 Laurent 系数的整性两面）                       *)
(* ============================================================ *)

(* 低段（j<n）：c_j == (−1)^{n+j}·2^{n−j}·T_j，T_j ∈ Z 显式承载。
   逐项：guard 全真（a≤j<n），n−(j−a) = (n−j)+a，2 幂按 Nat.pow_add_r 拆出 2^{n−j}。 *)
Lemma lni_bvc_low : forall n j : nat, j < n ->
  sigT (fun t : Z =>
    bv_c n j == (bv_negpow (n + j) * ((Z.of_nat (2 ^ (n - j)) # 1) * (t # 1))%Q)%Q).
Proof.
  intros n j Hj.
  unfold bv_c.
  assert (Hpt : forall a : nat, a < Datatypes.S j ->
            sigT (fun z : Z => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q
                         == ((z # 1)%Q))).
  { intros a Ha. exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)). ring. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q) Hpt)
    as [t Ht].
  exists t.
  transitivity (bv_negpow (n + j) *
    bk_psQ (fun a : nat => ((Z.of_nat (2 ^ (n - j)) # 1) *
              ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1))%Q)
            (Datatypes.S j) 1%Q)%Q.
  { apply lni_Qmul_cong_l. apply pi_psQ_ext. intros a Ha.
    assert (Ha1 : Nat.leb a n = true) by (apply Nat.leb_le; lia).
    assert (Ha2 : Nat.leb (j - a) n = true) by (apply Nat.leb_le; lia).
    rewrite Ha1, Ha2. cbn [andb].
    replace (n - (j - a)) with ((n - j) + a) by lia.
    rewrite lni_qpow2_nat, Nat.pow_add_r.
    rewrite (Nat2Z.inj_mul (2 ^ (n - j)) (2 ^ a)).
    rewrite <- (lni_QmulZ (Z.of_nat (2 ^ (n - j))) (Z.of_nat (2 ^ a))).
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) *
                    ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) * (Z.of_nat (2 ^ a) # 1)))%Q).
    { ring. }
    rewrite bk_Qmul_nat. reflexivity. }
  transitivity (bv_negpow (n + j) *
    ((Z.of_nat (2 ^ (n - j)) # 1) *
       bk_psQ (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
              (Datatypes.S j) 1%Q))%Q.
  { apply lni_Qmul_cong_l.
    exact (pi_psQ_mul (Datatypes.S j) ((Z.of_nat (2 ^ (n - j)) # 1)%Q)
                      (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
                      1%Q). }
  rewrite Ht. ring.
Qed.

(* 高段（n≤j≤2n）：c_j == (−1)^{n+j}·S_j，S_j ∈ Z 显式承载（guard 截取 a∈[j−n,n]）。 *)
Lemma lni_bvc_high : forall n j : nat, n < j -> j <= 2 * n ->
  sigT (fun t : Z => bv_c n j == (bv_negpow (n + j) * (t # 1))%Q).
Proof.
  intros n j Hj1 Hj2.
  unfold bv_c.
  assert (Hpt : forall a : nat, a < Datatypes.S j ->
            sigT (fun z : Z => (if andb (Nat.leb a n) (Nat.leb (j - a) n)
                           then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                                 q_pow (2 # 1)%Q (n - (j - a)))%Q
                           else 0%Q) == ((z # 1)%Q))).
  { intros a Ha.
    destruct (andb (Nat.leb a n) (Nat.leb (j - a) n)) eqn:Eg.
    - apply andb_true_iff in Eg as [Eg1 Eg2].
      apply Nat.leb_le in Eg1. apply Nat.leb_le in Eg2.
      exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ (n - (j - a)))).
      cbv beta iota.
      rewrite lni_qpow2_nat, bk_Qmul_nat. reflexivity.
    - exists 0%Z. cbv beta iota. reflexivity. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat =>
                 if andb (Nat.leb a n) (Nat.leb (j - a) n)
                 then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                       q_pow (2 # 1)%Q (n - (j - a)))%Q
                 else 0%Q) Hpt) as [t Ht].
  exists t. rewrite Ht. reflexivity.
Qed.

(* ============================================================ *)
(* §3 逐项整化（分母 d=|j−n| 由 L_n 吸收的主代数）                          *)
(* ============================================================ *)

(* bv_p 求和项的显式承载（与 bv_p 体内 lambda 定义面相等） *)
Definition lni_bvpt (n : nat) : nat -> Q :=
  fun j : nat =>
    if Nat.eqb j n then 0%Q
    else (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1)))%Q.

(* 低段代数：j<n（d:=n−j ≥ 1）。2 幂对消 + d | L_n。
   核：L·(c_j·((2^{−d}−1)/(−d))) == (−1)^{n+j}·T_j·(2^d−1)·(L/d)。 *)
Lemma lni_low_branch : forall n j : nat, j < n ->
  sigT (fun z : Z =>
    ((Z.of_nat (hl_lcm_upto n) # 1) *
       (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                    ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
    == ((z # 1)%Q)).
Proof.
  intros n j Hj.
  assert (Hd1 : 1 <= n - j) by lia.
  assert (Hdn : n - j <= n) by lia.
  assert (Hp : 1 <= 2 ^ (n - j)) by apply hl_pow2_ge1.
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.opp (Z.of_nat (n - j))) by lia.
  destruct (lni_bvc_low n j Hj) as [t Ht].
  assert (HnzA2 : ~ (((Z.of_nat (2 ^ (n - j)) # 1)) == 0)%Q)
    by (apply (pi_Qneq0_nat (2 ^ (n - j))); exact Hp).
  (* bv_q2 负支闭式：bv_q2(−d) == 1/(2^d) *)
  assert (Hbq : bv_q2 (Z.opp (Z.of_nat (n - j))) == ((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q)).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.opp (Z.of_nat (n - j)))) with false
      by (symmetry; apply Z.leb_gt; lia).
    rewrite Z.opp_involutive. rewrite Nat2Z.id.
    rewrite lni_qpow2_nat. unfold Qdiv. ring. }
  (* 分母闭式：1/(−d) == −(1/d) *)
  assert (Hden : (/ ((Z.opp (Z.of_nat (n - j))) # 1))%Q
                 == (Qopp (/ ((Z.of_nat (n - j)) # 1)))%Q)
    by (apply (lni_qinv_opp (Z.of_nat (n - j)))).
  (* d | L_n 的 Q 层商桥 *)
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (n - j)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (n - j)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (n - j) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  (* (2^d−1) 的整值 Q 形 *)
  assert (Hsub1 : (((Z.of_nat (2 ^ (n - j)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (n - j) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (n - j)) - 1)%Z) # 1)%Q).
    { apply lni_QsubZ. }
    replace (Z.of_nat (2 ^ (n - j)) - 1)%Z with (Z.of_nat (2 ^ (n - j) - 1))%Z by lia.
    reflexivity. }
  (* L-部分核心代数：A2·(L·((2^{−d}−1)/(−d))) == (2^d−1)·(L/d) *)
  assert (HL2 : ((Z.of_nat (2 ^ (n - j)) # 1) *
                   ((Z.of_nat (hl_lcm_upto n) # 1) *
                      ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                       ((Z.opp (Z.of_nat (n - j))) # 1))))%Q
                == (((Z.of_nat (2 ^ (n - j) - 1)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n / (n - j)) # 1)))%Q).
  { transitivity ((Z.of_nat (2 ^ (n - j)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) *
                       (((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q) *
                        (Qopp (/ ((Z.of_nat (n - j)) # 1))))))%Q.
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_l.
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) /
                    ((Z.opp (Z.of_nat (n - j))) # 1))%Q.
      { apply lni_Qdiv_cong_l. apply lni_Qminus_cong_l. exact Hbq. }
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) *
                    (/ ((Z.opp (Z.of_nat (n - j))) # 1)))%Q.
      { unfold Qdiv. ring. }
      apply lni_Qmul_cong_l. exact Hden. }
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) * ((/ (Z.of_nat (2 ^ (n - j)) # 1)) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (Qopp (/ ((Z.of_nat (n - j)) # 1)))))%Q.
    { ring. }
    rewrite (lni_qmul_inv_sub (Z.of_nat (2 ^ (n - j)) # 1) HnzA2).
    transitivity ((((Z.of_nat (2 ^ (n - j)) # 1) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (n - j)) # 1))))%Q.
    { ring. }
    rewrite Hdiv2, Hsub1. reflexivity. }
  (* 合成 *)
  assert (Hcore : ((Z.of_nat (hl_lcm_upto n) # 1) *
                    (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                                 ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
                  == ((bv_negpow (n + j)) *
                      ((t * Z.of_nat (2 ^ (n - j) - 1) *
                        Z.of_nat (hl_lcm_upto n / (n - j))) # 1))%Q).
  { rewrite E.
    transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((bv_negpow (n + j) *
                      ((Z.of_nat (2 ^ (n - j)) # 1) * (t # 1))) *
                     ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                      ((Z.opp (Z.of_nat (n - j))) # 1))))%Q.
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_r. exact Ht. }
    transitivity ((bv_negpow (n + j)) *
                    ((t # 1) * ((Z.of_nat (2 ^ (n - j)) # 1) *
                       ((Z.of_nat (hl_lcm_upto n) # 1) *
                          ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                           ((Z.opp (Z.of_nat (n - j))) # 1))))))%Q.
    { ring. }
    rewrite HL2.
    transitivity ((bv_negpow (n + j)) *
                    (((t # 1) * ((Z.of_nat (2 ^ (n - j) - 1)) # 1)) *
                     ((Z.of_nat (hl_lcm_upto n / (n - j))) # 1)))%Q.
    { ring. }
    rewrite lni_QmulZ, lni_QmulZ.
    reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (n - j) - 1) * Z.of_nat (hl_lcm_upto n / (n - j))))
    as [z Hz].
  exists z.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (n - j) - 1) *
                  Z.of_nat (hl_lcm_upto n / (n - j))) # 1))%Q.
  { exact Hcore. }
  exact Hz.
Qed.

(* 高段代数：j>n（d:=j−n ≥ 1，j ≤ 2n ⟹ d ≤ n）。无 2 幂对消需求，直接 d | L_n。
   核：L·(c_j·((2^d−1)/d)) == (−1)^{n+j}·S_j·(2^d−1)·(L/d)。 *)
Lemma lni_high_branch : forall n j : nat, n < j -> j <= 2 * n ->
  sigT (fun z : Z =>
    ((Z.of_nat (hl_lcm_upto n) # 1) *
       (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                    ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
    == ((z # 1)%Q)).
Proof.
  intros n j Hj1 Hj2.
  assert (Hd1 : 1 <= j - n) by lia.
  assert (Hdn : j - n <= n) by lia.
  assert (Hp : 1 <= 2 ^ (j - n)) by apply hl_pow2_ge1.
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.of_nat (j - n)) by lia.
  destruct (lni_bvc_high n j Hj1 Hj2) as [t Ht].
  assert (Hbq2 : bv_q2 (Z.of_nat (j - n)) == ((Z.of_nat (2 ^ (j - n)) # 1))%Q).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.of_nat (j - n))) with true
      by (symmetry; apply Z.leb_le; exact (Nat2Z.is_nonneg (j - n))).
    rewrite Nat2Z.id. apply lni_qpow2_nat. }
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (j - n)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (j - n) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  assert (Hsub1 : (((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (j - n) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (j - n)) - 1)%Z) # 1)%Q).
    { apply lni_QsubZ. }
    replace (Z.of_nat (2 ^ (j - n)) - 1)%Z with (Z.of_nat (2 ^ (j - n) - 1))%Z by lia.
    reflexivity. }
  (* L-部分：L·((2^d−1)/d) == (2^d−1)·(L/d) *)
  assert (HL3 : ((Z.of_nat (hl_lcm_upto n) # 1) *
                   ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1)))%Q
                == (((Z.of_nat (2 ^ (j - n) - 1)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1)))%Q).
  { transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) *
                     (/ ((Z.of_nat (j - n)) # 1))))%Q.
    { apply lni_Qmul_cong_l.
      transitivity ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) /
                    ((Z.of_nat (j - n)) # 1))%Q.
      { apply lni_Qdiv_cong_l. apply lni_Qminus_cong_l. exact Hbq2. }
      unfold Qdiv. reflexivity. }
    transitivity ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (j - n)) # 1))))%Q.
    { ring. }
    rewrite Hdiv2, Hsub1. reflexivity. }
  (* 合成 *)
  assert (Hcore : ((Z.of_nat (hl_lcm_upto n) # 1) *
                    (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                                 ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
                  == ((bv_negpow (n + j)) *
                      ((t * Z.of_nat (2 ^ (j - n) - 1) *
                        Z.of_nat (hl_lcm_upto n / (j - n))) # 1))%Q).
  { rewrite E.
    transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((bv_negpow (n + j) * (t # 1)) *
                     ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1))))%Q.
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_r. exact Ht. }
    transitivity ((bv_negpow (n + j)) *
                    ((t # 1) * ((Z.of_nat (hl_lcm_upto n) # 1) *
                       ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1)))))%Q.
    { ring. }
    rewrite HL3.
    transitivity ((bv_negpow (n + j)) *
                    (((t # 1) * ((Z.of_nat (2 ^ (j - n) - 1)) # 1)) *
                     ((Z.of_nat (hl_lcm_upto n / (j - n))) # 1)))%Q.
    { ring. }
    rewrite lni_QmulZ, lni_QmulZ.
    reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (j - n) - 1) * Z.of_nat (hl_lcm_upto n / (j - n))))
    as [z Hz].
  exists z.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (j - n) - 1) *
                  Z.of_nat (hl_lcm_upto n / (j - n))) # 1))%Q.
  { exact Hcore. }
  exact Hz.
Qed.

(* ============================================================ *)
(* §4 主件：改型分子 B·L_n 的整除供给（sigT 见证，Set 面）                   *)
(* ============================================================ *)

Definition lni_lbvp (n : nat) : Q := ((Z.of_nat (hl_lcm_upto n) # 1) * bv_p n)%Q.

(* 逐项整化主桥：k ≤ 2n ⟹ L_n·(bv_p 求和项 k) ∈ Z（见证显式） *)
Lemma lni_term_int : forall n k : nat, k <= 2 * n ->
  sigT (fun z : Z => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q == ((z # 1)%Q)).
Proof.
  intros n k Hk. unfold lni_bvpt.
  destruct (Nat.eq_dec k n) as [Heq | Hne].
  - subst k. exists 0%Z. rewrite Nat.eqb_refl. ring.
  - assert (Eb : Nat.eqb k n = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite Eb.
    destruct (Nat.compare k n) eqn:Ecmp.
    + exfalso. apply Hne. apply Nat.compare_eq_iff. exact Ecmp.
    + apply (lni_low_branch n k). apply Nat.compare_lt_iff. exact Ecmp.
    + apply (lni_high_branch n k).
      * apply (proj1 (Nat.compare_gt_iff k n)). exact Ecmp.
      * exact Hk.
Qed.

Theorem lni_bvp_lcm_int : forall n : nat,
  sigT (fun z : Z => QeqT (lni_lbvp n) ((z # 1)%Q)).
Proof.
  intro n.
  assert (Hpt : forall k : nat, k < Datatypes.S (2 * n) ->
            sigT (fun z : Z => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q
                         == ((z # 1)%Q))).
  { intros k Hk. apply (lni_term_int n k). lia. }
  destruct (lni_psQ_zsum_ex (Datatypes.S (2 * n))
              (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n j)%Q) Hpt)
    as [w Hw].
  exists (Z.opp w). apply qeq_imp_qeqT.
  unfold lni_lbvp.
  change (bv_p n) with (Qopp (bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)).
  transitivity ((Qopp ((Z.of_nat (hl_lcm_upto n) # 1) *
                          bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)))%Q.
  { ring. }
  transitivity ((Qopp (bk_psQ (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n j)%Q)
                              (Datatypes.S (2 * n)) 1%Q)))%Q.
  { apply lni_Qopp_cong. symmetry.
    exact (pi_psQ_mul (Datatypes.S (2 * n)) ((Z.of_nat (hl_lcm_upto n) # 1)%Q)
                      (lni_bvpt n) 1%Q). }
  transitivity ((Qopp ((w # 1)%Q))).
  { apply lni_Qopp_cong. exact Hw. }
  apply lni_QoppZ.
Qed.

(* A 侧平凡肢：L_n·q̃_n ∈ Z（bk_Qmul_nat 一步） *)
Theorem lni_qlcm_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1)) ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n)).
  apply qeq_imp_qeqT. apply bk_Qmul_nat.
Qed.

(* 改型分子对合成交付：(A·L_n, B·L_n) ∈ Z×Z —— sa_supply_rem' 改型参数化
   （A_n := L_n·q̃_n、B_n := L_n·p_n 的 Z 面整备） *)
Theorem lni_supply_pair : forall n : nat,
  sigT (fun z : Z =>
    sigT (fun w : Z =>
      (QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1)) ((z # 1)%Q)
        * QeqT (lni_lbvp n) ((w # 1)%Q))%type)).
Proof.
  intro n.
  destruct (lni_qlcm_int n) as [z Hz].
  destruct (lni_bvp_lcm_int n) as [w Hw].
  exists z, w. split; assumption.
Qed.

(* ============================================================ *)
(* §5 数值判定组（vm_compute 精确判定；与检验件 lni_probe1 同源：L₃·p₃=262）   *)
(* ============================================================ *)

Theorem lni_lbvp_anchor0 : QeqT (lni_lbvp 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lni_lbvp_anchor1 : QeqT (lni_lbvp 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lni_lbvp_anchor2 : QeqT (lni_lbvp 2) (18 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lni_lbvp_anchor3 : QeqT (lni_lbvp 3) (262 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lni_lbvp_anchor4 : QeqT (lni_lbvp 4) (2670 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem lni_lbvp_anchor5 : QeqT (lni_lbvp 5) (69994 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（G4 取证块，BB 教训）                     *)
(* ============================================================ *)

Print Assumptions lni_psQ_zsum_ex.
Print Assumptions lni_bvc_low.
Print Assumptions lni_bvc_high.
Print Assumptions lni_term_int.
Print Assumptions lni_low_branch.
Print Assumptions lni_high_branch.
Print Assumptions lni_bvp_lcm_int.
Print Assumptions lni_qlcm_int.
Print Assumptions lni_supply_pair.
Print Assumptions lni_lbvp_anchor3.
