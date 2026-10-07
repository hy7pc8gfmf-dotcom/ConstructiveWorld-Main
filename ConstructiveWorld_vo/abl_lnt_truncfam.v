(* ===================================================================== *)
(*  abl_lnt_truncfam.v —— ln2 的 Beukers 型单积分见证族的截断恒等式。       *)
(*  模块名：abl_lnt_truncfam。使命：对 Beukers 型 ln2 逼近积分              *)
(*  ∫₀¹ tⁿ(1−t)ⁿ/(1+t)^{n+1} 的代数侧，建立 1/(1+t)^{n+1} 的 Taylor        *)
(*  截断恒等式（除法自由形）：B(n,M,t)=Σ_{m≤M}(−1)^m C(n+m,n)t^m           *)
(*  （lnt_ps）、Bu 同形于 C(n+m,n+1)（lnt_psu）、Q(n,M,t)=Σ_{i≤n}          *)
(*  C(M+i,i)(1+t)^i（lnt_pq）。证得①几何档 (1+t)B(0,M,t)=1−(−t)^{M+1}，   *)
(*  ②Pascal 档 B(n+1,M,t)=B+Bu，③位移档 (−t)B−(1+t)Bu=(−t)^{M+1}C(n+M+1,  *)
(*  n+1)，④恒等式（一切有理 t，无假设）(1+t)^{n+1}B+(−t)^{M+1}Q=1，其      *)
(*  等价读法 1−(1+t)^{n+1}B=(−t)^{M+1}Q 为余项显式分离面                   *)
(*  （lnt_remainder_sep，误差在 t=0 处零点阶 M+1 的代数根源），⑤序面：     *)
(*  1+t≥0（从而 0≤t）蕴含 Q≥0（Set 层 QleT' 见证）。积分与极限两面不在     *)
(*  本件。                                                            *)
(*  来源：本件为 abl_z2_truncfam 截断恒等式 (1−t)^{n+1}A+t^{M+1}P=1 在    *)
(*  t:=−t 处的参数化实例化（换形 1−t→1+t、t→−t），三族即 zb2 族在 −t      *)
(*  的取值，几何/Pascal/位移三档逐字取 zb2_ps_geom/zb2_ps_pascal/         *)
(*  zb2_shift/zb2_shift_su 的实例，恒等式与序面依其证明骨架重演（该件     *)
(*  0≤t≤1 假设在其证明中未被使用，故按无假设形陈述）。                  *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）、S01_BaseRing、        *)
(*  S02_CauchyComplete（QleT' 桥）、S03_QExp（q_pow）、BeukersLists       *)
(*  （bkC/bk_psQ）、abl_z2_truncfam（参数化来源件）；零外部证书器、       *)
(*  零实数层、零经典逻辑。构造性：纯构造、零假设声明，语句面为 Qeq 等式   *)
(*  与 Set 层 QleT' 见证，非线性组合步以显式 Pascal 恒等式证书闭合，未    *)
(*  引入有序域决策程序。编译配方：coqc -native-compiler no -q            *)
(*  -Q <本目录> "" -Q "D:/ComplexAnalysis/新算法实践/Live_X" "" 本件，   *)
(*  先行件 BeukersLists 与 abl_z2_truncfam 同参编译，经 cpu_guard 包裹。  *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.   *)
(*  London Math. Soc. 11 (1979) 268-272 中单积分见证的多项式恒等式步。     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
  abl_z2_truncfam.
Require Import PolyIntegral.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 截断族三定义（z2 族在 −t 的取值：1+t 与 (−t)^k 换形）              *)
(* ============================================================ *)

(* B(n,M,t) = Σ_{m≤M} (−1)^m C(n+m,n)·t^m：1/(1+t)^{n+1} 的 Taylor 截断 *)
Definition lnt_ps (n M : nat) (t : Q) : Q :=
  zb2_ps n M (0 - t).

(* Bu(n,M,t) = Σ_{m≤M} (−1)^m C(n+m,n+1)·t^m：Pascal 档伴生族 *)
Definition lnt_psu (n M : nat) (t : Q) : Q :=
  zb2_psu n M (0 - t).

(* Q(n,M,t) = Σ_{i≤n} C(M+i,i)·(1+t)^i：余项多项式族 *)
Definition lnt_pq (n M : nat) (t : Q) : Q :=
  zb2_pq n M (0 - t).

(* 换形桥：(1+t)^k = (1−(0−t))^k（q_pow 整体为原子，须逐 k 归纳过桥） *)
Lemma lnt_one_pt_bridge : forall (t : Q) (k : nat),
  q_pow (1 - (0 - t)) k == q_pow (1 + t) k.
Proof.
  intros t k. induction k as [| k IH].
  - reflexivity.
  - rewrite (q_pow_succ (1 - (0 - t)) k). rewrite (q_pow_succ (1 + t) k).
    transitivity ((1 - (0 - t)) * q_pow (1 + t) k)%Q.
    + rewrite IH. ring.
    + ring.
Qed.

(* 末项剥离（定义性）：B(n,M+1,t) = B(n,M,t) + C(n+M+1,n)·(−t)^{M+1} *)
Lemma lnt_ps_unfold : forall n M t,
  lnt_ps n (Datatypes.S M) t
  == (lnt_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
        * q_pow (0 - t) (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold lnt_ps. exact (zb2_ps_unfold n M (0 - t)).
Qed.

(* 末项剥离（定义性）：Bu(n,M+1,t) = Bu(n,M,t) + C(n+M+1,n+1)·(−t)^{M+1} *)
Lemma lnt_psu_unfold : forall n M t,
  lnt_psu n (Datatypes.S M) t
  == (lnt_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow (0 - t) (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold lnt_psu. exact (zb2_psu_unfold n M (0 - t)).
Qed.

(* ============================================================ *)
(* §2 等式面：几何档、Pascal 档、位移档（zb2 引理在 −t 的实例）            *)
(* ============================================================ *)

(* 几何档：(1+t)·Σ_{m≤M} (−t)^m = 1 − (−t)^{M+1} *)
Lemma lnt_ps_geom : forall M t,
  (1 + t) * lnt_ps 0 M t == 1 - q_pow (0 - t) (Datatypes.S M).
Proof.
  intros M t. unfold lnt_ps.
  transitivity ((1 - (0 - t)) * zb2_ps 0 M (0 - t))%Q.
  - ring.
  - exact (zb2_ps_geom M (0 - t)).
Qed.

(* Pascal 档：B(n+1,M,t) = B(n,M,t) + Bu(n,M,t) *)
Lemma lnt_ps_pascal : forall n M t,
  lnt_ps (Datatypes.S n) M t == (lnt_ps n M t + lnt_psu n M t)%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu. exact (zb2_ps_pascal n M (0 - t)).
Qed.

(* Pascal 步（定义性）：Q(n+1,M,t) = Q(n,M,t) + C(M+n+1,n+1)·(1+t)^{n+1} *)
Lemma lnt_pq_step : forall n M t,
  lnt_pq (Datatypes.S n) M t
  == (lnt_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 + t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold lnt_pq.
  rewrite <- (lnt_one_pt_bridge t (Datatypes.S n)).
  exact (zb2_pq_step n M (0 - t)).
Qed.

(* 位移档：(−t)·B − (1+t)·Bu = (−t)^{M+1}·C(n+M+1,n+1) *)
Lemma lnt_shift : forall n M t,
  (0 - t) * lnt_ps n M t - (1 + t) * lnt_psu n M t
  == (q_pow (0 - t) (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu.
  transitivity (((0 - t) * zb2_ps n M (0 - t)
                 - (1 - (0 - t)) * zb2_psu n M (0 - t))%Q).
  - ring.
  - exact (zb2_shift n M (0 - t)).
Qed.

(* 位移档换形（母恒等式归纳步用）：由位移档乘 (1+t)^{n+1} 重排。 *)
Lemma lnt_shift_su : forall n M t,
  (1 + t) * q_pow (1 + t) (Datatypes.S n) * lnt_psu n M t
  == ((0 - t) * (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
      - q_pow (1 + t) (Datatypes.S n)
        * (q_pow (0 - t) (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu.
  rewrite <- (lnt_one_pt_bridge t (Datatypes.S n)).
  transitivity (((1 - (0 - t)) * q_pow (1 - (0 - t)) (Datatypes.S n)
                 * zb2_psu n M (0 - t))%Q).
  - ring.
  - exact (zb2_shift_su n M (0 - t)).
Qed.

(* ============================================================ *)
(* §3 母恒等式与余项分离                                                *)
(* ============================================================ *)

(* 母恒等式：(1+t)^{n+1}·B + (−t)^{M+1}·Q = 1，对一切有理 t 成立。
   代数读法：1 − (1+t)^{n+2}(B+Bu) = [1−(1+t)^{n+1}B] + (1+t)^{n+1}[（−t)B−(1+t)Bu]，
   右端第一括号由归纳假设换为 (−t)^{M+1}Q，第二括号由位移档换为
   (−t)^{M+1}C(n+M+1,n+1)，与 Pascal 步的新增项相消。 *)
Lemma lnt_master : forall n M t,
  q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
  + q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t == 1.
Proof.
  intros n M t. revert M.
  induction n as [| n IH]; intro M.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ].
    change (q_pow (1 + t) (Datatypes.S 0)) with ((1 + t) * 1)%Q.
    change (q_pow (1 - (0 - t)) 0) with 1%Q.
    assert (Hm : (1 + t) * 1 * lnt_ps 0 M t == (1 + t) * lnt_ps 0 M t) by ring.
    rewrite Hm. rewrite lnt_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite zb2_bkC_zero; reflexivity).
    ring.
  - assert (E := lnt_shift_su n M t).
    rewrite lnt_ps_pascal. rewrite lnt_pq_step.
    rewrite (q_pow_succ (1 + t) (Datatypes.S n)).
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
                    + q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)
                   - (0 - t) * (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
                   + (1 + t) * q_pow (1 + t) (Datatypes.S n) * lnt_psu n M t
                   + q_pow (0 - t) (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 + t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* 余项显式分离面：1 − (1+t)^{n+1}·B = (−t)^{M+1}·Q。
   即截断误差恰含因子 (−t)^{M+1}，为后续积分面的衰减估计提供代数根源。 *)
Lemma lnt_remainder_sep : forall n M t,
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
  == q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t.
Proof.
  intros n M t.
  remember (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)%Q as A eqn:HA.
  remember (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)%Q as B eqn:HB.
  assert (Hm : A + B == 1).
  { rewrite HA. rewrite HB. exact (lnt_master n M t). }
  rewrite <- Hm. ring.
Qed.

(* ============================================================ *)
(* §4 序面：余项族非负（Set 层 QleT' 见证）                              *)
(* ============================================================ *)

(* Q ≥ 0：逐项 C(M+i,i)·(1+t)^i ≥ 0，假设 1+t ≥ 0。 *)
Lemma lnt_pq_ge0 : forall n M t, Qle 0 (1 + t) -> QleT' 0 (lnt_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t H.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow]. rewrite Nat.add_0_r.
    apply (zb2_qleT'_wd_r (Z.of_nat (bkC M 0) # 1)
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply zb2_bkC_Q_nonneg.
  - apply (zb2_qleT'_wd_r
             ((lnt_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 + t) (Datatypes.S n))%Q)
             (lnt_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (lnt_pq_step n M t)).
    + apply Qle_to_QleT'.
      apply (Qplus_le_compat 0 (lnt_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 + t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. exact H.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- apply (q_pow_nonneg (1 + t) (Datatypes.S n)). exact H.
Qed.

(* 序面推论：0 ≤ t 时 Q ≥ 0（积分区间 [0,1] 上的直接可用形）。 *)
Lemma lnt_pq_ge0_pos : forall n M t, Qle 0 t -> QleT' 0 (lnt_pq n M t).
Proof.
  intros n M t H. apply lnt_pq_ge0.
  assert (H1 : Qle 0 (1 + t)).
  { unfold Qle in *. cbn [Qnum Qden Qplus Qopp Qmult] in *. lia. }
  exact H1.
Qed.

(* ============================================================ *)
(* §5 数值复核（vm_compute 机械复算：定义面无换形错位）                    *)
(* ============================================================ *)

(* B(1,1,1/2) = C(1,1) − C(2,1)·(1/2) = 1 − 1 = 0 *)
Lemma lnt_ps_anchor1 : lnt_ps 1 1 (1 # 2) == 0.
Proof. vm_compute. reflexivity. Qed.

(* Q(1,1,1/2) = C(1,0) + C(2,1)·(3/2) = 1 + 3 = 4 *)
Lemma lnt_pq_anchor1 : lnt_pq 1 1 (1 # 2) == 4.
Proof. vm_compute. reflexivity. Qed.

(* 母恒等式实例：(3/2)²·0 + (1/4)·4 = 1 *)
Lemma lnt_master_anchor1 :
  q_pow (1 + (1 # 2)) 2 * lnt_ps 1 1 (1 # 2)
  + q_pow (0 - (1 # 2)) 2 * lnt_pq 1 1 (1 # 2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §6 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions lnt_one_pt_bridge.
Print Assumptions lnt_ps_unfold.
Print Assumptions lnt_psu_unfold.
Print Assumptions lnt_ps_geom.
Print Assumptions lnt_ps_pascal.
Print Assumptions lnt_pq_step.
Print Assumptions lnt_shift.
Print Assumptions lnt_shift_su.
Print Assumptions lnt_master.
Print Assumptions lnt_remainder_sep.
Print Assumptions lnt_pq_ge0.
Print Assumptions lnt_pq_ge0_pos.
Print Assumptions lnt_ps_anchor1.
Print Assumptions lnt_pq_anchor1.
Print Assumptions lnt_master_anchor1.

(* ============================================================ *)
(* §7 余项符号的奇偶分档（符号面）                                       *)
(* ============================================================ *)

(* 偶次幂换形：(0−t)^{2k} = t^{2k}，对 k 归纳。 *)
Lemma lnt_qpow_opp_even : forall (t : Q) (k : nat),
  q_pow (0 - t) (k + k) == q_pow t (k + k).
Proof.
  intros t k. induction k as [| k IH].
  - reflexivity.
  - replace (Datatypes.S k + Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (k + k)))%nat by lia.
    cbn [q_pow]. rewrite IH. ring.
Qed.

(* 奇次幂换形：(0−t)^{2k+1} = −t^{2k+1}，由偶次幂换形一步导出。 *)
Lemma lnt_qpow_opp_odd : forall (t : Q) (k : nat),
  q_pow (0 - t) (Datatypes.S (k + k)) == 0 - q_pow t (Datatypes.S (k + k)).
Proof.
  intros t k.
  rewrite (q_pow_succ (0 - t) (k + k)). rewrite (q_pow_succ t (k + k)).
  rewrite (lnt_qpow_opp_even t k). ring.
Qed.

(* 奇 M 档（M = 2k+1）：余项符号为正，1 − (1+t)^{n+1}B = t^{2k+2}·Q。 *)
Lemma lnt_rem_sign_odd : forall (n k : nat) (t : Q),
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t
  == q_pow t (Datatypes.S (Datatypes.S (k + k)))
     * lnt_pq n (Datatypes.S k + k) t.
Proof.
  intros n k t.
  transitivity (q_pow (0 - t) (Datatypes.S (Datatypes.S (k + k)))
                * lnt_pq n (Datatypes.S k + k) t)%Q.
  - rewrite <- (lnt_remainder_sep n (Datatypes.S k + k) t). reflexivity.
  - replace (Datatypes.S (Datatypes.S (k + k)))%nat
      with (Datatypes.S k + Datatypes.S k)%nat by lia.
    rewrite (lnt_qpow_opp_even t (Datatypes.S k)). reflexivity.
Qed.

(* 偶 M 档（M = 2k）：余项符号为负，1 − (1+t)^{n+1}B = −t^{2k+1}·Q。 *)
Lemma lnt_rem_sign_even : forall (n k : nat) (t : Q),
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t
  == (0 - q_pow t (Datatypes.S (k + k))) * lnt_pq n (k + k) t.
Proof.
  intros n k t.
  transitivity (q_pow (0 - t) (Datatypes.S (k + k)) * lnt_pq n (k + k) t)%Q.
  - rewrite <- (lnt_remainder_sep n (k + k) t). reflexivity.
  - rewrite (lnt_qpow_opp_odd t k). reflexivity.
Qed.

(* ============================================================ *)
(* §8 截断和的上界面（按 M 奇偶分档）                                    *)
(* ============================================================ *)

(* Set 层序见证的左端换形（与 zb2_qleT'_wd_r 的右端换形对偶）。 *)
Lemma lnt_qleT'_wd_l : forall x y z : Q, x == y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy Hy. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply qeq_imp_qle. exact Hxy.
  - apply QleT'_to_Qle. exact Hy.
Qed.

(* 幂的单元上界：0 ≤ t ≤ 1 蕴含 t^m ≤ 1，对 m 归纳。 *)
Lemma lnt_qpow_le_one : forall (t : Q) (m : nat), Qle 0 t -> Qle t 1 ->
  QleT' (q_pow t m) 1.
Proof.
  intros t m H0 H1. induction m as [| m IH].
  - apply qleT'_refl.
  - change (q_pow t (Datatypes.S m)) with (t * q_pow t m)%Q.
    assert (Hu : Qle (q_pow t m) 1) by (apply QleT'_to_Qle; exact IH).
    assert (Hq0 : Qle 0 (q_pow t m)) by (apply (q_pow_nonneg t m); exact H0).
    assert (Hstep : QleT' (t * q_pow t m) (q_pow t m * 1)).
    { apply (zb2_qleT'_wd_r (1 * q_pow t m)%Q (q_pow t m * 1)%Q (t * q_pow t m)%Q).
      - ring.
      - apply Qle_to_QleT'. exact (Qmult_le_compat_r t 1 (q_pow t m) H1 Hq0). }
    apply (qleT'_trans (t * q_pow t m) (q_pow t m * 1) 1 Hstep).
    apply (zb2_qleT'_wd_r (1 * 1)%Q 1 (q_pow t m * 1)%Q).
    + ring.
    + apply Qle_to_QleT'. exact (Qmult_le_compat_r (q_pow t m) 1 1 Hu Qle_0_1).
Qed.

(* 修正项受控：1 + t^{M+1}·Q ≤ 1 + Q（0 ≤ t ≤ 1 且 Q ≥ 0）。 *)
Lemma lnt_ps_ub_shift : forall (n M : nat) (t : Q), Qle 0 t -> Qle t 1 ->
  QleT' (1 + q_pow t (Datatypes.S M) * lnt_pq n M t) (1 + lnt_pq n M t).
Proof.
  intros n M t H0 H1.
  apply (zb2_qleT'_wd_r (1 + 1 * lnt_pq n M t)%Q (1 + lnt_pq n M t)%Q
                        (1 + q_pow t (Datatypes.S M) * lnt_pq n M t)%Q).
  - ring.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + apply (qleT'_mult_compat_r (q_pow t (Datatypes.S M)) 1 (lnt_pq n M t)).
      * exact (lnt_pq_ge0_pos n M t H0).
      * apply lnt_qpow_le_one; assumption.
Qed.

(* 奇 M 档直接上界：余项 t^{2k+2}·Q ≥ 0 给出 (1+t)^{n+1}·B ≤ 1。 *)
Lemma lnt_ps_ub_direct : forall (n k : nat) (t : Q), Qle 0 t ->
  QleT' (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t) 1.
Proof.
  intros n k t Ht.
  apply (zb2_qleT'_wd_r
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t
            + q_pow t (Datatypes.S (Datatypes.S (k + k)))
              * lnt_pq n (Datatypes.S k + k) t)%Q 1
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t)).
  - rewrite <- (lnt_rem_sign_odd n k t). ring.
  - apply qleT'_plus_nonneg_rT. apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply (q_pow_nonneg t (Datatypes.S (Datatypes.S (k + k)))). exact Ht.
    + apply QleT'_to_Qle. apply lnt_pq_ge0_pos. exact Ht.
Qed.

(* 偶 M 档修正上界：余项 −t^{2k+1}·Q ≤ 0 使直接上界失效，
   改得 (1+t)^{n+1}·B ≤ 1 + Q。 *)
Lemma lnt_ps_ub_qabs : forall (n k : nat) (t : Q), Qle 0 t -> Qle t 1 ->
  QleT' (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t)
        (1 + lnt_pq n (k + k) t).
Proof.
  intros n k t H0 H1.
  apply (lnt_qleT'_wd_l
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t)
           (1 + q_pow t (Datatypes.S (k + k)) * lnt_pq n (k + k) t)%Q
           (1 + lnt_pq n (k + k) t)).
  - transitivity (1 - (0 - q_pow t (Datatypes.S (k + k))) * lnt_pq n (k + k) t)%Q.
    + rewrite <- (lnt_rem_sign_even n k t). ring.
    + ring.
  - exact (lnt_ps_ub_shift n (k + k) t H0 H1).
Qed.

(* ============================================================ *)
(* §9 余项绝对值的全体 M 统一形                                         *)
(* ============================================================ *)

(* 相反数幂的绝对值：|(0−t)^m| = t^m（t ≥ 0），对 m 归纳。 *)
Lemma lnt_qabs_opp_pow : forall (t : Q) (m : nat), Qle 0 t ->
  Qabs (q_pow (0 - t) m) == q_pow t m.
Proof.
  intros t m Ht. induction m as [| m IH].
  - apply Qabs_pos. apply Qle_0_1.
  - change (q_pow (0 - t) (Datatypes.S m)) with ((0 - t) * q_pow (0 - t) m)%Q.
    change (q_pow t (Datatypes.S m)) with (t * q_pow t m)%Q.
    rewrite (Qabs_Qmult (0 - t) (q_pow (0 - t) m)). rewrite IH.
    assert (Ha : Qabs (0 - t) == t).
    { transitivity (Qabs (- t))%Q.
      - apply (Qabs_wd (0 - t) (- t)). ring.
      - rewrite (Qabs_opp t). apply Qabs_pos. exact Ht. }
    rewrite Ha. reflexivity.
Qed.

(* 全体 M 统一的余项绝对值等式：|1 − (1+t)^{n+1}B| = t^{M+1}·Q（t ≥ 0），
   符号随 M 奇偶的交替在绝对值内消解。 *)
Lemma lnt_rem_abs : forall (n M : nat) (t : Q), Qle 0 t ->
  Qabs (1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
  == q_pow t (Datatypes.S M) * lnt_pq n M t.
Proof.
  intros n M t Ht.
  transitivity (Qabs (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t))%Q.
  - apply (Qabs_wd (1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
                   (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)
                   (lnt_remainder_sep n M t)).
  - rewrite (Qabs_Qmult (q_pow (0 - t) (Datatypes.S M)) (lnt_pq n M t)).
    rewrite (lnt_qabs_opp_pow t (Datatypes.S M) Ht).
    assert (Hq : Qabs (lnt_pq n M t) == lnt_pq n M t)
      by (apply Qabs_pos; apply QleT'_to_Qle; apply lnt_pq_ge0_pos; exact Ht).
    rewrite Hq. reflexivity.
Qed.

(* ============================================================ *)
(* §10 尾舱续：新增主语句公理面自检                                      *)
(* ============================================================ *)

Print Assumptions lnt_qpow_opp_even.
Print Assumptions lnt_qpow_opp_odd.
Print Assumptions lnt_rem_sign_odd.
Print Assumptions lnt_rem_sign_even.
Print Assumptions lnt_qleT'_wd_l.
Print Assumptions lnt_qpow_le_one.
Print Assumptions lnt_ps_ub_shift.
Print Assumptions lnt_ps_ub_direct.
Print Assumptions lnt_ps_ub_qabs.
Print Assumptions lnt_qabs_opp_pow.
Print Assumptions lnt_rem_abs.

(* ============================================================ *)
(* §11 积分面与衰减面（[0,1] 核退常数承载）                               *)
(* ============================================================ *)

(* §11.0 积分面（PolyIntegral 基建档）：衰减核 t^{M+1} 在 [0,1] 上的积分
   质量显式等于 1/(M+2)。库内积分基建于多项式档（pint_integral，
   ∫x^k = 1/(k+1) 正确性锚在案）；有理函数被积函数不在其定义域，故衰减
   面按「积分=显式上界常数」处理：以闭式常数 c(n) = (n!)²/(2n+1)! 直接
   承载（§11.1-§11.2），免积分构造。 *)
Lemma lnt_kernel_mass : forall M : nat,
  QeqT (pint_integral (pint_pow_poly (Datatypes.S M)))
       (1 / (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1)).
Proof. intro M. exact (pint_integral_pow_poly (Datatypes.S M)). Qed.

Lemma lnt_kernel_mass_Q : forall M : nat,
  pint_integral (pint_pow_poly (Datatypes.S M))
  == 1 / (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1).
Proof. intro M. apply qeqT_imp_qeq. exact (lnt_kernel_mass M). Qed.

(* §11.1 闭式衰减常数：cden n = (2n+1)·C(2n,n)，cfac n = 1/cden n，
   即 Beukers 核 ∫₀¹ tⁿ(1−t)ⁿ dt 的闭式值 (n!)²/(2n+1)!。 *)
Definition lnt_cden (n : nat) : nat := (2 * n + 1) * bkC (n + n) n.
Definition lnt_cfac (n : nat) : Q := Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q.

(* Pascal 倍增：C(2n+2,n+1) ≥ 2·C(2n,n)。 *)
Lemma lnt_binom_double : forall n : nat,
  (2 * bkC (n + n) n
   <= bkC (Datatypes.S (Datatypes.S (n + n))) (Datatypes.S n))%nat.
Proof.
  intro n. destruct n as [| n].
  - cbn. lia.
  - assert (Hp : (bkC (Datatypes.S (Datatypes.S (Datatypes.S n + Datatypes.S n)))
                   (Datatypes.S (Datatypes.S n))
                  = bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                    (Datatypes.S n)
                  + bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                    (Datatypes.S (Datatypes.S n)))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S (Datatypes.S n + Datatypes.S n))
                 (Datatypes.S (Datatypes.S n))). reflexivity. }
    rewrite Hp.
    assert (Hr : (bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                   (Datatypes.S (Datatypes.S n))
                 = bkC (Datatypes.S n + Datatypes.S n) (Datatypes.S n)
                   + bkC (Datatypes.S n + Datatypes.S n)
                     (Datatypes.S (Datatypes.S n)))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S n + Datatypes.S n)
                 (Datatypes.S (Datatypes.S n))). reflexivity. }
    rewrite Hr.
    assert (Hq : (bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                   (Datatypes.S n)
                 = bkC (Datatypes.S n + Datatypes.S n) n
                   + bkC (Datatypes.S n + Datatypes.S n) (Datatypes.S n))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S n + Datatypes.S n)
                 (Datatypes.S n)). reflexivity. }
    rewrite Hq. lia.
Qed.

(* C(2n,n) ≥ 2ⁿ。 *)
Lemma lnt_binom_ge_pow2 : forall n : nat, (2 ^ n <= bkC (n + n) n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - assert (Hd := lnt_binom_double n).
    replace (Datatypes.S n + Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (n + n)))%nat in Hd by lia.
    replace (Datatypes.S n + Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (n + n)))%nat by lia.
    replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat
      by (apply eq_sym; apply Nat.pow_succ_r').
    apply Nat.le_trans with (m := (2 * bkC (n + n) n)%nat).
    + apply Nat.mul_le_mono.
      * lia.
      * exact IH.
    + exact Hd.
Qed.

(* cden n ≥ 1。 *)
Lemma lnt_cden_1 : forall n : nat, (1 <= lnt_cden n)%nat.
Proof.
  intro n. unfold lnt_cden.
  assert (Hb : (1 <= bkC (n + n) n)%nat) by (apply bkC_pos; lia).
  assert (Hp : (1 * bkC (n + n) n <= (2 * n + 1) * bkC (n + n) n)%nat)
    by (apply Nat.mul_le_mono; lia).
  assert (Hr : (1 * bkC (n + n) n = bkC (n + n) n)%nat) by ring.
  lia.
Qed.

(* cden n ≥ 2ⁿ。 *)
Lemma lnt_cden_ge_pow2 : forall n : nat, (2 ^ n <= lnt_cden n)%nat.
Proof.
  intro n. unfold lnt_cden.
  apply Nat.le_trans with (m := (bkC (n + n) n)%nat).
  - apply lnt_binom_ge_pow2.
  - assert (Hm : (1 * bkC (n + n) n <= (2 * n + 1) * bkC (n + n) n)%nat)
      by (apply Nat.mul_le_mono; lia).
    transitivity ((1 * bkC (n + n) n)%nat).
    + lia.
    + exact Hm.
Qed.

(* cden 的 Q 像为正（QltT 面）。 *)
Lemma lnt_cden_Qpos : forall n : nat, QltT 0 ((Z.of_nat (lnt_cden n)) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
  assert (H := lnt_cden_1 n). lia.
Qed.

(* cfac n = 1/cden n 为正。 *)
Lemma lnt_cfac_pos : forall n : nat, QltT 0 (lnt_cfac n).
Proof.
  intro n. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
  apply QltT_to_Qlt. apply lnt_cden_Qpos.
Qed.

(* 2ⁿ ≥ 1。 *)
Lemma lnt_pow2_ge1 : forall n : nat, (1 <= 2 ^ n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* (1/2)ⁿ 的乘积恒等桥：q_pow (1/2) n 与 2ⁿ 互逆。 *)
Lemma lnt_qpow_half_inv : forall n : nat,
  q_pow (1 # 2)%Q n * ((Z.of_nat (2 ^ n)) # 1)%Q == (1 # 1)%Q.
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - rewrite (q_pow_succ (1 # 2) n).
    assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)%Q
                 == ((2 # 1) * ((Z.of_nat (2 ^ n)) # 1))%Q).
    { replace (Z.of_nat (2 ^ Datatypes.S n))%Z
        with (2 * Z.of_nat (2 ^ n))%Z
        by (rewrite Nat.pow_succ_r'; rewrite Nat2Z.inj_mul; reflexivity).
      reflexivity. }
    rewrite E2.
    transitivity (((1 # 2) * (2 # 1))%Q
                  * (q_pow (1 # 2)%Q n * ((Z.of_nat (2 ^ n)) # 1)%Q))%Q.
    + ring.
    + rewrite IH. ring.
Qed.

(* 预算：cfac n = 1/cden n ≤ (1/2)ⁿ（双逆反序：D₂ ≤ D ⟹ 1/D ≤ 1/D₂）。 *)
Lemma lnt_cfac_budget : forall n : nat,
  QleT' (lnt_cfac n) (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'. unfold lnt_cfac.
  assert (Hle : Qle ((Z.of_nat (2 ^ n)) # 1) ((Z.of_nat (lnt_cden n)) # 1)).
  { unfold Qle. cbn [Qnum Qden].
    assert (Hn := lnt_cden_ge_pow2 n). lia. }
  assert (HD2pos : Qlt 0 ((Z.of_nat (2 ^ n)) # 1)).
  { unfold Qlt. cbn [Qnum Qden].
    assert (Hp1 := lnt_pow2_ge1 n). lia. }
  set (D := ((Z.of_nat (lnt_cden n)) # 1)%Q) in *.
  assert (HD2ne : ~ (((Z.of_nat (2 ^ n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (2 ^ n)) # 1)%Q).
    - exact HD2pos.
    - apply Qeq_sym. exact He. }
  assert (Einv2 : ((Z.of_nat (2 ^ n)) # 1)%Q
                  * Qinv ((Z.of_nat (2 ^ n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HD2ne).
  assert (HDne : ~ (D == 0%Q)).
  { intro He.
    apply (Qlt_not_eq 0 D).
    - apply QltT_to_Qlt. apply lnt_cden_Qpos.
    - apply Qeq_sym. exact He. }
  assert (EinvD : D * Qinv D == 1%Q) by (apply Qmult_inv_r; exact HDne).
  assert (Eform := lnt_qpow_half_inv n).
  assert (Ew : q_pow (1 # 2)%Q n == Qinv ((Z.of_nat (2 ^ n)) # 1)%Q).
  { transitivity (q_pow (1 # 2)%Q n
                  * (((Z.of_nat (2 ^ n)) # 1)%Q
                     * Qinv ((Z.of_nat (2 ^ n)) # 1)%Q))%Q.
    - rewrite Einv2. ring.
    - rewrite (Qmult_assoc (q_pow (1 # 2)%Q n) ((Z.of_nat (2 ^ n)) # 1)
                (Qinv ((Z.of_nat (2 ^ n)) # 1))).
      rewrite Eform. ring. }
  rewrite Ew.
  set (D2 := ((Z.of_nat (2 ^ n)) # 1)%Q) in *.
  assert (Hpr : Qle 0 (Qinv D2 * Qinv D)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD2pos.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply QltT_to_Qlt.
      apply lnt_cden_Qpos. }
  assert (Hmul := Qmult_le_compat_r D2 D (Qinv D2 * Qinv D) Hle Hpr).
  apply (Qle_trans (Qinv D) (D2 * (Qinv D2 * Qinv D))%Q).
  - apply qeq_imp_qle.
    rewrite (Qmult_assoc D2 (Qinv D2) (Qinv D)).
    rewrite Einv2. ring.
  - apply (Qle_trans (D2 * (Qinv D2 * Qinv D))%Q
             (D * (Qinv D2 * Qinv D))%Q).
    + exact Hmul.
    + apply qeq_imp_qle.
      rewrite (Qmult_comm (Qinv D2) (Qinv D)).
      rewrite (Qmult_assoc D (Qinv D) (Qinv D2)).
      rewrite EinvD. ring.
Qed.

(* ============================================================ *)
(* §12 尾舱续：§11 主语句公理面自检                                      *)
(* ============================================================ *)

Print Assumptions lnt_kernel_mass.
Print Assumptions lnt_kernel_mass_Q.
Print Assumptions lnt_binom_double.
Print Assumptions lnt_binom_ge_pow2.
Print Assumptions lnt_cden_1.
Print Assumptions lnt_pow2_ge1.
Print Assumptions lnt_cden_ge_pow2.
Print Assumptions lnt_cden_Qpos.
Print Assumptions lnt_cfac_pos.
Print Assumptions lnt_qpow_half_inv.
Print Assumptions lnt_cfac_budget.

(* ============================================================ *)
(* §13 供给面预形（θ 对齐・t=1 整数承载桥・下界序列显式化）                 *)
(* ============================================================ *)

(* θ 预算对齐：截断族预算面 (1/2)ⁿ 对齐供给面档位 (4/5)ⁿ（幂单调）。 *)
Lemma lnt_theta_align : forall n : nat,
  QleT' (q_pow (1 # 2)%Q n) (q_pow (4 # 5)%Q n).
Proof.
  intro n. apply Qle_to_QleT'. apply (q_pow_mono (1 # 2) (4 # 5) n).
  - unfold Qle. cbn [Qnum Qden]. lia.
  - unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* t=1 档整数承载桥：q_pow 2 n 与 2ⁿ 的 Q 像逐点恒等（母恒等式在 t=1
   取值时 (1+1)^{n+1}·B(n,M,1) + (−1)^{M+1}·Q(n,M,1) = 1 即整系数
   Bezout 面，本桥把左端幂归位到 Z 像承载）。 *)
Lemma lnt_qpow_two_Z : forall n : nat,
  q_pow (1 + 1)%Q n == ((Z.of_nat (2 ^ n)) # 1)%Q.
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - rewrite (q_pow_succ (1 + 1) n).
    replace ((Z.of_nat (2 ^ Datatypes.S n)) # 1)%Q
      with ((2 # 1) * ((Z.of_nat (2 ^ n)) # 1))%Q.
    + rewrite IH. ring.
    + replace (Z.of_nat (2 ^ Datatypes.S n))%Z
        with (2 * Z.of_nat (2 ^ n))%Z.
      * reflexivity.
      * rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 2ⁿ 的线性下界：n + 1 ≤ 2ⁿ（下界序列显式化的 nat 面引擎）。 *)
Lemma lnt_pow2_ge_lin : forall n : nat, (Datatypes.S n <= 2 ^ n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* 下界序列显式化：cfac n ≤ 1/(n+1)。链：预算面 cfac n ≤ (1/2)ⁿ
   （lnt_cfac_budget）＋(1/2)ⁿ = 1/2ⁿ（乘积恒等桥）＋双逆反序
   （n+1 ≤ 2ⁿ ⟹ 1/2ⁿ ≤ 1/(n+1)，两端正性）。 *)
Lemma lnt_cfac_le_inv : forall n : nat,
  QleT' (lnt_cfac n) (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. unfold lnt_cfac.
  assert (HD1pos : Qlt 0 ((Z.of_nat (Datatypes.S n)) # 1)%Q).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (HD1ne : ~ (((Z.of_nat (Datatypes.S n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (Datatypes.S n)) # 1)%Q).
    - exact HD1pos.
    - apply Qeq_sym. exact He. }
  assert (EinvD1 : ((Z.of_nat (Datatypes.S n)) # 1)%Q
                   * Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HD1ne).
  assert (HDcpos : Qlt 0 ((Z.of_nat (lnt_cden n)) # 1)%Q).
  { apply QltT_to_Qlt. apply lnt_cden_Qpos. }
  assert (HDcne : ~ (((Z.of_nat (lnt_cden n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (lnt_cden n)) # 1)%Q).
    - exact HDcpos.
    - apply Qeq_sym. exact He. }
  assert (EinvDc : ((Z.of_nat (lnt_cden n)) # 1)%Q
                   * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HDcne).
  assert (Hle : Qle ((Z.of_nat (Datatypes.S n)) # 1)
                    ((Z.of_nat (lnt_cden n)) # 1)%Q).
  { unfold Qle. cbn [Qnum Qden].
    assert (Hl := lnt_pow2_ge_lin n).
    assert (Hc := lnt_cden_ge_pow2 n). lia. }
  assert (Hpr : Qle 0 (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                        * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD1pos.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HDcpos. }
  assert (Hmul := Qmult_le_compat_r ((Z.of_nat (Datatypes.S n)) # 1)
                    ((Z.of_nat (lnt_cden n)) # 1)
                    (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                     * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q) Hle Hpr).
  apply (Qle_trans (Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q)
           (((Z.of_nat (Datatypes.S n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q).
  - apply qeq_imp_qle.
    rewrite (Qmult_assoc ((Z.of_nat (Datatypes.S n)) # 1)
              (Qinv ((Z.of_nat (Datatypes.S n)) # 1))
              (Qinv ((Z.of_nat (lnt_cden n)) # 1))).
    rewrite EinvD1. ring.
  - apply (Qle_trans (((Z.of_nat (Datatypes.S n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q
           (((Z.of_nat (lnt_cden n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q).
    + exact Hmul.
    + apply qeq_imp_qle.
      rewrite (Qmult_comm (Qinv ((Z.of_nat (Datatypes.S n)) # 1))
                (Qinv ((Z.of_nat (lnt_cden n)) # 1))).
      rewrite (Qmult_assoc ((Z.of_nat (lnt_cden n)) # 1)
                (Qinv ((Z.of_nat (lnt_cden n)) # 1))
                (Qinv ((Z.of_nat (Datatypes.S n)) # 1))).
      rewrite EinvDc. ring.
Qed.

(* ============================================================ *)
(* §14 尾舱续：§13 主语句公理面自检                                      *)
(* ============================================================ *)

Print Assumptions lnt_theta_align.
Print Assumptions lnt_qpow_two_Z.
Print Assumptions lnt_pow2_ge_lin.
Print Assumptions lnt_cfac_le_inv.
Require Import UpReqLn2Irrational.

(* ============================================================ *)
(* §15 t=1 档 Bezout 面（截断恒等式右端与 ln2 级数列的代数主体）            *)
(* ============================================================ *)

(* 幂的单元面：1^m = 1（t=1 取值的幂归位）。 *)
Lemma lnt_qpow_one : forall m : nat, q_pow 1 m == 1.
Proof.
  intro m. induction m as [| m IH].
  - reflexivity.
  - rewrite (q_pow_succ 1 m). rewrite IH. ring.
Qed.

(* 奇档 Bezout 面：2^{n+1}·B(n,2k+1,1) + Q(n,2k+1,1) = 1（Z 像承载形）。
   母恒等式在 t=1 的取值：(−1)^{2k+2} = 1 且 2^{n+1} 归位整数像；
   即截断值 B(n,2k+1,1) = (1 − Q)/2^{n+1} 的整数 Bezout 关系。 *)
Lemma lnt_bezout_odd : forall (n k : nat),
  ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n (Datatypes.S k + k) 1
  + lnt_pq n (Datatypes.S k + k) 1 == 1.
Proof.
  intros n k.
  assert (E := lnt_master n (Datatypes.S k + k) 1).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  replace (Datatypes.S (Datatypes.S k + k))%nat
    with (Datatypes.S k + Datatypes.S k)%nat in E by lia.
  rewrite (lnt_qpow_opp_even 1 (Datatypes.S k)) in E.
  rewrite (lnt_qpow_one (Datatypes.S k + Datatypes.S k)) in E.
  rewrite (Qmult_1_l (lnt_pq n (Datatypes.S k + k) 1)) in E.
  exact E.
Qed.

(* 偶档 Bezout 面：2^{n+1}·B(n,2k,1) − Q(n,2k,1) = 1（(−1)^{2k+1} = −1）。
   两档合读：截断值恒为分母 2^{n+1} 的既约分数胚。 *)
Lemma lnt_bezout_even : forall (n k : nat),
  ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n (k + k) 1
  + (0 - lnt_pq n (k + k) 1) == 1.
Proof.
  intros n k.
  assert (E := lnt_master n (k + k) 1).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  rewrite (lnt_qpow_opp_odd 1 k) in E.
  rewrite (lnt_qpow_one (Datatypes.S (k + k))) in E.
  assert (Em : ((0 - 1) * lnt_pq n (k + k) 1)%Q
               == (0 - lnt_pq n (k + k) 1)) by ring.
  rewrite Em in E. exact E.
Qed.

(* 右端统一绝对值面：|1 − 2^{n+1}·B(n,M,1)| = Q(n,M,1)（全体 M·Z 像形，
   符号随 M 奇偶的交替在绝对值内消解）。 *)
Lemma lnt_rem_abs_one : forall (n M : nat),
  Qabs (1 - ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n M 1)
  == lnt_pq n M 1.
Proof.
  intros n M.
  assert (E := lnt_rem_abs n M 1 Qle_0_1).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  rewrite (lnt_qpow_one (Datatypes.S M)) in E.
  rewrite (Qmult_1_l (lnt_pq n M 1)) in E.
  exact E.
Qed.

(* 右端显式间隙下界：Q(n,M,1) ≥ 1（余项族在 t=1 的常值项承载，
   逐项非负归纳——截断值与 2^{n+1} 倍数相差至少 1 的整数间隙面）。 *)
Lemma lnt_pq_one_ge1 : forall (n M : nat), QleT' 1 (lnt_pq n M 1).
Proof.
  intro n. induction n as [| n IH]; intro M.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow]. rewrite Nat.add_0_r.
    replace (Z.of_nat (bkC M 0) # 1) with (1 # 1)%Q
      by (rewrite zb2_bkC_zero; reflexivity).
    apply (zb2_qleT'_wd_r 1 ((1 # 1) * 1)%Q 1).
    + ring.
    + apply qleT'_refl.
  - apply (zb2_qleT'_wd_r
             ((lnt_pq n M 1
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 + 1) (Datatypes.S n))%Q)
             (lnt_pq (Datatypes.S n) M 1) 1).
    + exact (Qeq_sym _ _ (lnt_pq_step n M 1)).
    + apply Qle_to_QleT'.
      apply (Qplus_le_compat 1 (lnt_pq n M 1) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 + 1) (Datatypes.S n))).
      * exact (QleT'_to_Qle 1 (lnt_pq n M 1) (IH M)).
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- assert (H01 : Qle 0 ((1 + 1)%Q)).
           ++ unfold Qle. cbn [Qnum Qden Qplus Qmult]. lia.
           ++ exact (q_pow_nonneg (1 + 1) (Datatypes.S n) H01).
Qed.

(* 级数列第 k 投影的标度传送：|2^{n+1}·x_k − 2^{n+1}·B(n,M,1)|
   = 2^{n+1}·|x_k − B(n,M,1)|（x_k = ln2i_x k 为 ln2 的级数部分和列）。
   截断值 B(n,M,1) 与级数列在同一 2 幂标度下的绝对值分裂面，
   为线投影 |A·x − B| 形的供给侧准备。 *)
Lemma lnt_ln2i_proj_gap : forall (n M k : nat),
  Qabs (((Z.of_nat (2 ^ Datatypes.S n)) # 1) * ln2i_x k
        - ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n M 1)
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n M 1)%Q).
Proof.
  intros n M k.
  assert (Ha : Qle 0 ((Z.of_nat (2 ^ Datatypes.S n)) # 1)).
  { pose proof (ln2i_powZ_pos (Datatypes.S n)) as Hp.
    unfold Qle. cbn [Qnum Qden]. lia. }
  transitivity (Qabs (((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                      * (ln2i_x k - lnt_ps n M 1)%Q))%Q.
  - apply (Qabs_wd (((Z.of_nat (2 ^ Datatypes.S n)) # 1) * ln2i_x k
                    - ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                      * lnt_ps n M 1)%Q
                   (((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                    * (ln2i_x k - lnt_ps n M 1))%Q).
    ring.
  - rewrite (Qabs_Qmult ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
              ((ln2i_x k - lnt_ps n M 1)%Q)).
    rewrite (Qabs_pos ((Z.of_nat (2 ^ Datatypes.S n)) # 1) Ha).
    reflexivity.
Qed.

(* ============================================================ *)
(* §16 尾舱续：§15 主语句公理面自检                                      *)
(* ============================================================ *)

Print Assumptions lnt_qpow_one.
Print Assumptions lnt_bezout_odd.
Print Assumptions lnt_bezout_even.
Print Assumptions lnt_rem_abs_one.
Print Assumptions lnt_pq_one_ge1.
Print Assumptions lnt_ln2i_proj_gap.
Require Import Ln2Bridge.

(* ============================================================ *)
(* §17 real_le 终归 slack 形传送桥与截断调剂对线投影对接件                  *)
(* ============================================================ *)

(* 余项族的整承载见证：Q(n,M,1) 恒为分母 1 的有理数（Z 见证，Set 层 sigT）。
   归纳面：常值项为 1，逐项 (bkC·2^{n+1}) 皆整值，分母 1 的有理数对加法
   与乘法封闭（Qmake 算术展开即合）。 *)
Lemma lnt_pq_zpair : forall (n M : nat),
  sigT (fun j : Z => lnt_pq n M 1 == (j # 1)%Q).
Proof.
  intro n. induction n as [| n IH]; intro M.
  - exists 1%Z. unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    replace (Z.of_nat (bkC M 0) # 1) with (1 # 1)%Q
      by (rewrite zb2_bkC_zero; reflexivity).
    ring.
  - destruct (IH M) as [j Hj].
    exists (j + Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n))
              * Z.of_nat (2 ^ Datatypes.S n))%Z.
    rewrite (lnt_pq_step n M 1). rewrite Hj.
    rewrite (lnt_qpow_two_Z (Datatypes.S n)).
    unfold Qplus, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* real_le 终归 slack 形传送桥（上界方向）：若线投影读数对常数幂的
   距离终归一致地大于正数 e，则 real_le 取严格分离支（real_lt 编码的
   直接装配）。这是 Q 层终归面到 real_le 语句的最后一跳。 *)
Lemma lnt_line_upper_slack : forall (A B : nat -> Z) (n : nat) (th e : Q) (N : nat),
  QltT 0 e ->
  (forall k : nat, NatLe N k ->
    QltT e ((q_pow th n
             - Qabs (((A n) # 1)%Q * ln2i_x k - ((B n) # 1)%Q))%Q)) ->
  real_le (ln2b_line A B n) (real_const (q_pow th n)).
Proof.
  intros A B n th e N He0 Hface.
  left. unfold real_lt. exists e. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    rewrite (real_const_proj (q_pow th n) k).
    rewrite (ln2b_line_pt A B n k).
    exact (QltT_to_Qlt _ _ (Hface k Hk)).
Qed.

(* real_le 终归 slack 形传送桥（下界方向）：若线投影读数对常数 c 的
   越出量终归一致地大于正数 e，则 c ≤ 线取严格分离支。 *)
Lemma lnt_line_lower_slack : forall (A B : nat -> Z) (n : nat) (c e : Q) (N : nat),
  QltT 0 e ->
  (forall k : nat, NatLe N k ->
    QltT e ((Qabs (((A n) # 1)%Q * ln2i_x k - ((B n) # 1)%Q) - c)%Q)) ->
  real_le (real_const c) (ln2b_line A B n).
Proof.
  intros A B n c e N He0 Hface.
  left. unfold real_lt. exists e. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    rewrite (real_const_proj c k).
    rewrite (ln2b_line_pt A B n k).
    exact (QltT_to_Qlt _ _ (Hface k Hk)).
Qed.

(* 奇档线投影恒等：截断调剂对 (2^{n+1}, 1−j)（j 为 Q(n,2k+1,1) 的整
   见证）的线投影读数恰为标度传送形 2^{n+1}·|x_k − B(n,2k+1,1)|。
   链：Bezout 面 2^{n+1}·B + Q = 1 与整见证换算出 (1−j)#1 == 2^{n+1}·B，
   再由标度传送面闭合。 *)
Lemma lnt_line_truncdock_proj_odd : forall (n k : nat) (j : Z),
  lnt_pq n (Datatypes.S k + k) 1 == (j # 1)%Q ->
  projT1 (ln2b_line (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                    (fun _ : nat => (1 - j)%Z) (Datatypes.S k + k)) k
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n (Datatypes.S k + k) 1)%Q).
Proof.
  intros n k j Hj.
  assert (Ept := ln2b_line_pt (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                              (fun _ : nat => (1 - j)%Z)
                              (Datatypes.S k + k) k).
  cbv beta in Ept. rewrite Ept.
  assert (Ebez := lnt_bezout_odd n k). rewrite Hj in Ebez.
  assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
               * lnt_ps n (Datatypes.S k + k) 1 == (1 - (j # 1))%Q).
  { transitivity ((((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                   * lnt_ps n (Datatypes.S k + k) 1 + (j # 1))%Q
                  - (j # 1))%Q.
    - ring.
    - rewrite Ebez. ring. }
  assert (Ebr : (((1 - j)%Z) # 1)%Q == (1 - (j # 1))%Q)
    by (unfold Qminus, Qopp, Qplus, Qeq; cbn [Qnum Qden Pos.mul]; lia).
  rewrite Ebr. rewrite <- E2.
  exact (lnt_ln2i_proj_gap n (Datatypes.S k + k) k).
Qed.

(* 偶档线投影恒等：截断调剂对 (2^{n+1}, 1+j)（j 为 Q(n,2k,1) 的整见证）
   的线投影读数恰为标度传送形 2^{n+1}·|x_k − B(n,2k,1)|（Bezout 偶档
   2^{n+1}·B − Q = 1 换算 (1+j)#1 == 2^{n+1}·B）。 *)
Lemma lnt_line_truncdock_proj_even : forall (n k : nat) (j : Z),
  lnt_pq n (k + k) 1 == (j # 1)%Q ->
  projT1 (ln2b_line (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                    (fun _ : nat => (1 + j)%Z) (k + k)) k
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n (k + k) 1)%Q).
Proof.
  intros n k j Hj.
  assert (Ept := ln2b_line_pt (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                              (fun _ : nat => (1 + j)%Z) (k + k) k).
  cbv beta in Ept. rewrite Ept.
  assert (Ebez := lnt_bezout_even n k). rewrite Hj in Ebez.
  assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
               * lnt_ps n (k + k) 1 == (1 + (j # 1))%Q).
  { transitivity ((((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                   * lnt_ps n (k + k) 1 + (0 - (j # 1)))%Q
                  + (j # 1))%Q.
    - ring.
    - rewrite Ebez. ring. }
  assert (Ebr : (((1 + j)%Z) # 1)%Q == (1 + (j # 1))%Q)
    by (unfold Qminus, Qopp, Qplus, Qeq; cbn [Qnum Qden Pos.mul]; lia).
  rewrite Ebr. rewrite <- E2.
  exact (lnt_ln2i_proj_gap n (k + k) k).
Qed.

(* ============================================================ *)
(* §18 尾舱续：§17 主语句公理面自检                                      *)
(* ============================================================ *)

Print Assumptions lnt_pq_zpair.
Print Assumptions lnt_line_upper_slack.
Print Assumptions lnt_line_lower_slack.
Print Assumptions lnt_line_truncdock_proj_odd.
Print Assumptions lnt_line_truncdock_proj_even.
