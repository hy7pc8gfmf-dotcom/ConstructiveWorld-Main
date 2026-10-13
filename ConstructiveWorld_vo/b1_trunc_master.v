(* 模块：b1_trunc_master.v —— arctan 核截断母恒等式（Pascal 族同构换核）。
   使命：Taylor 截断的除法自由母恒等式
     (1−t)^{n+1}·A(n,M,t) + t^{M+1}·P(n,M,t) = 1，
   其中 A(n,M,t) = Σ_{m≤M} C(n+m,n)·t^m（截断和）、
   P(n,M,t) = Σ_{i≤n} C(M+i,i)·(1−t)^i（余项多项式）。
   本件为 zb2 塔截断族（abl_z2_truncfam，池 _lineage_b3 系谱在案）的
   同构换核再铸：母恒等式升级为 t 无条件（纯 Q 代数恒等式，去 zb2 版的
   0≤t≤1 前提）；新增 arctan 核换档实例 t := −x²（(1+x²)^{n+1} 读形）与
   该域上 P 的正性肢（−x² ≤ 1 全 x 成立）。两档为 Beukers-arctan 余项
   显式分离面（件①核界 × 本件截断恒等式）的后续装配承重件。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp（q_pow/q_pow_nonneg）、
   BeukersLists（bkC/bk_psQ）、b1_kernel_pointwise（b1_sub_ge0/b1_qsq_nonneg）。
   构造性：语句面全 Set（QeqT/QleT'）；证明体 n-归纳＋M 泛化＋显式 Pascal
   恒等式证书，ring 只入等式重排位；零公理、零经典逻辑。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" b1_trunc_master.v。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import BeukersLists.
Require Import b1_kernel_pointwise.

Open Scope Q_scope.

(* ========== §0 工具箱（bkC 有理像与指标和） ========== *)

(* 二项系数零档 *)
Lemma b1_bkC_zero : forall n : nat, bkC n 0 = 1%nat.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* 有理像系数和：单项分母 1 的 Q 像对 nat 加法分配 *)
Lemma b1_ofC_add : forall a b : nat,
  (Z.of_nat (a + b) # 1) == ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* Pascal 恒等式的有理像：C(N+1,n+1) = C(N,n) + C(N,n+1) *)
Lemma b1_pascalC : forall N n : nat,
  (Z.of_nat (bkC (Datatypes.S N) (Datatypes.S n)) # 1)
  == ((Z.of_nat (bkC N n) # 1) + (Z.of_nat (bkC N (Datatypes.S n)) # 1))%Q.
Proof.
  intros N n.
  assert (Hc := bkC_pascal_shift N (Datatypes.S n)).
  change ((bkC N n + bkC N (Datatypes.S n))%nat
          = bkC (Datatypes.S N) (Datatypes.S n)) in Hc.
  rewrite <- b1_ofC_add. rewrite Hc. reflexivity.
Qed.

(* 二项系数有理像的非负性（Set 层见证） *)
Lemma b1_bkC_Q_nonneg : forall n k : nat, QleT' 0 ((Z.of_nat (bkC n k) # 1)%Q).
Proof.
  intros n k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  destruct (le_lt_dec k n) as [Hle | Hlt].
  - assert (Hb : (1 <= bkC n k)%nat) by (apply bkC_pos; exact Hle).
    lia.
  - rewrite (bkC_out n k Hlt). cbn [Z.of_nat]. lia.
Qed.

(* Set 层序见证的右端换形 *)
Lemma b1_qleT'_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hz. apply Qle_to_QleT'.
  apply (Qle_trans z x y).
  - apply QleT'_to_Qle. exact Hz.
  - apply qeq_imp_qle. exact Hxy.
Qed.

(* 指标和的逐点加法外延 *)
Lemma b1_bk_psQ_add : forall (f g h : nat -> Q) (N : nat) (z : Q),
  (forall k : nat, (k < N)%nat -> f k == (g k + h k)%Q) ->
  bk_psQ f N z == (bk_psQ g N z + bk_psQ h N z)%Q.
Proof.
  intros f g h N. revert f g h.
  induction N as [| N IH]; intros f g h z Hfg.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g h z) by (intros k Hk; apply Hfg; lia).
    rewrite (Hfg N) by lia. ring.
Qed.

(* ========== §1 截断族三定义（接口面，签名定死） ========== *)

(* 截断和 A(n,M,t) = Σ_{k<S M} C(n+k,n)·t^k *)
Definition b1_ps (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) n) # 1)) (Datatypes.S M) t.

(* 伴和 U(n,M,t) = Σ_{k<S M} C(n+k,n+1)·t^k（Pascal 档用） *)
Definition b1_psu (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) (Datatypes.S n)) # 1)) (Datatypes.S M) t.

(* 余项多项式 P(n,M,t) = Σ_{i<S n} C(M+i,i)·(1−t)^i *)
Definition b1_pq (n M : nat) (t : Q) : Q :=
  bk_psQ (fun i => (Z.of_nat (bkC (M + i) i) # 1)) (Datatypes.S n) (1 - t).

(* 末项剥离（定义性）：A(n,M+1,t) = A(n,M,t) + C(n+M+1,n)·t^{M+1} *)
Lemma b1_ps_unfold : forall n M t,
  b1_ps n (Datatypes.S M) t
  == (b1_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold b1_ps. cbn [bk_psQ]. reflexivity.
Qed.

(* 末项剥离：U(n,M+1,t) = U(n,M,t) + C(n+M+1,n+1)·t^{M+1} *)
Lemma b1_psu_unfold : forall n M t,
  b1_psu n (Datatypes.S M) t
  == (b1_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold b1_psu. cbn [bk_psQ]. reflexivity.
Qed.

(* ========== §2 等式面：几何档、Pascal 档、位移档 ========== *)

(* 几何档：(1−t)·A(0,M,t) = 1 − t^{M+1} *)
Lemma b1_ps_geom : forall M t,
  (1 - t) * b1_ps 0 M t == 1 - q_pow t (Datatypes.S M).
Proof.
  intros M. induction M as [| M IH]; intro t.
  - unfold b1_ps. cbn [bk_psQ q_pow Nat.add bkC Z.of_nat]. ring.
  - rewrite b1_ps_unfold.
    transitivity (((1 - t) * b1_ps 0 M t
                   + (1 - t) * ((Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1)
                                * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1) with (1 # 1)%Q
        by (rewrite b1_bkC_zero; reflexivity).
      rewrite (q_pow_succ t (Datatypes.S M)). ring.
Qed.

(* Pascal 档：A(n+1,M,t) = A(n,M,t) + U(n,M,t) *)
Lemma b1_ps_pascal : forall n M t,
  b1_ps (Datatypes.S n) M t == (b1_ps n M t + b1_psu n M t)%Q.
Proof.
  intros n M t. apply b1_bk_psQ_add. intros k Hk.
  replace (Datatypes.S n + k)%nat with (Datatypes.S (n + k))%nat by reflexivity.
  rewrite (b1_pascalC (n + k) n). ring.
Qed.

(* Pascal 步（定义性）：P(n+1,M,t) = P(n,M,t) + C(M+n+1,n+1)·(1−t)^{n+1} *)
Lemma b1_pq_step : forall n M t,
  b1_pq (Datatypes.S n) M t
  == (b1_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 - t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold b1_pq. cbn [bk_psQ]. reflexivity.
Qed.

(* 位移档：t·A − (1−t)·U = t^{M+1}·C(n+M+1,n+1) *)
Lemma b1_shift : forall n M t,
  t * b1_ps n M t - (1 - t) * b1_psu n M t
  == (q_pow t (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M. revert n.
  induction M as [| M IH]; intros n t.
  - unfold b1_ps, b1_psu. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r. rewrite (bkC_diag n).
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    replace (n + Datatypes.S 0)%nat with (Datatypes.S n)%nat by lia.
    rewrite (bkC_diag (Datatypes.S n)).
    cbn [Z.of_nat]. ring.
  - rewrite b1_ps_unfold. rewrite b1_psu_unfold.
    transitivity (((t * b1_ps n M t - (1 - t) * b1_psu n M t)
                   + t * ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                          * q_pow t (Datatypes.S M))
                   + t * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                          * q_pow t (Datatypes.S M))
                   - ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                      * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (n + Datatypes.S (Datatypes.S M))%nat
        with (Datatypes.S (n + Datatypes.S M))%nat by lia.
      rewrite (b1_pascalC (n + Datatypes.S M) n).
      rewrite (q_pow_succ t (Datatypes.S M)). ring.
Qed.

(* 位移档换形（上界用辅助恒等式） *)
Lemma b1_shift_su : forall n M t,
  (1 - t) * q_pow (1 - t) (Datatypes.S n) * b1_psu n M t
  == (t * (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)
      - q_pow (1 - t) (Datatypes.S n)
        * (q_pow t (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. rewrite <- (b1_shift n M t). ring.
Qed.

(* ========== §3 母恒等式（t 无条件） ========== *)

(* 母恒等式：(1−t)^{n+1}·A + t^{M+1}·P = 1（纯 Q 代数恒等式，全 t）。
   代数读法：1 − (1−t)^{n+2}(A+U) = [1−(1−t)^{n+1}A] + (1−t)^{n+1}[tA−(1−t)U]，
   第一括号由归纳假设换为 t^{M+1}P，第二括号由位移档换为
   t^{M+1}C(n+M+1,n+1)，与 Pascal 步新增项相消。 *)
Theorem b1_master : forall n M t,
  q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
  + q_pow t (Datatypes.S M) * b1_pq n M t == 1.
Proof.
  intros n M t. revert M.
  induction n as [| n IH]; intro M.
  - unfold b1_pq. cbn [bk_psQ].
    change (q_pow (1 - t) (Datatypes.S 0)) with ((1 - t) * 1)%Q.
    change (q_pow (1 - t) 0) with 1%Q.
    assert (Hm : (1 - t) * 1 * b1_ps 0 M t == (1 - t) * b1_ps 0 M t) by ring.
    rewrite Hm. rewrite b1_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite b1_bkC_zero; reflexivity).
    ring.
  - assert (E := b1_shift_su n M t).
    rewrite b1_ps_pascal. rewrite b1_pq_step.
    rewrite (q_pow_succ (1 - t) (Datatypes.S n)).
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
                    + q_pow t (Datatypes.S M) * b1_pq n M t)
                   - t * (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)
                   + (1 - t) * q_pow (1 - t) (Datatypes.S n) * b1_psu n M t
                   + q_pow t (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 - t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* ========== §4 正性肢（t ≤ 1 域，含 arctan 换档域 t := −x²） ========== *)

(* P 的非负性：逐项 C(M+i,i)·(1−t)^i ≥ 0（t ≤ 1 即可） *)
Lemma b1_pq_ge0 : forall n M t, QleT' t 1 -> QleT' 0 (b1_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t Ht.
  - unfold b1_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    apply (b1_qleT'_wd_r ((Z.of_nat (bkC M 0) # 1))
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply b1_bkC_Q_nonneg.
  - apply (b1_qleT'_wd_r
             ((b1_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 - t) (Datatypes.S n))%Q)
             (b1_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (b1_pq_step n M t)).
    + apply Qle_to_QleT'.
      assert (Hsub : Qle 0 (1 - t)) by exact (b1_sub_ge0 t Ht).
      apply (Qplus_le_compat 0 (b1_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 - t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. exact Ht.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply b1_bkC_Q_nonneg.
        -- apply (q_pow_nonneg (1 - t) (Datatypes.S n)). exact Hsub.
Qed.

(* arctan 换档域正性：P(n,M,−x²) ≥ 0（全 x，由 −x² ≤ 1） *)
Lemma b1_pq_ge0_arctan : forall (n M : nat) (x : Q), QleT' 0 (b1_pq n M (-(x * x))).
Proof.
  intros n M x.
  apply (b1_pq_ge0 n M (-(x * x))).
  apply Qle_to_QleT'.
  apply (Qle_trans (-(x * x)) 0 1).
  - exact (Qopp_le_compat 0 (x * x) (b1_qsq_nonneg x)).
  - apply Qlt_le_weak. exact b1_0lt1.
Qed.

(* ========== §5 arctan 核换档实例（除法自由余项分离面） ========== *)

(* 换档母恒等式：(1+x²)^{n+1}·A(n,M,−x²) + (−x²)^{M+1}·P(n,M,−x²) = 1。
   即 1/(1+x²)^{n+1} = A(n,M,−x²) + (−x²)^{M+1}P/(1+x²)^{n+1} 的除法自由读形。 *)
Theorem b1_master_arctan : forall (n M : nat) (x : Q),
  q_pow (1 + x * x) (Datatypes.S n) * b1_ps n M (-(x * x))
  + q_pow (-(x * x)) (Datatypes.S M) * b1_pq n M (-(x * x)) == 1.
Proof.
  intros n M x.
  pose proof (b1_master n M (-(x * x))) as Hm.
  setoid_replace (1 - (-(x * x)))%Q with (1 + x * x)%Q in Hm by ring.
  exact Hm.
Qed.

(* 除法自由上界（zb2 ⑤ 同位）：0 ≤ t ≤ 1 ⟹ (1−t)^{n+1}·A ≤ 1 *)
Theorem b1_ps_bound : forall n M t,
  QleT' 0 t -> QleT' t 1 ->
  QleT' (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t) 1.
Proof.
  intros n M t Ht0 Ht1.
  apply (b1_qleT'_wd_r
           (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
            + q_pow t (Datatypes.S M) * b1_pq n M t) 1
           (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)).
  - exact (b1_master n M t).
  - apply qleT'_plus_nonneg_rT.
    apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply (q_pow_nonneg t (Datatypes.S M)). exact (QleT'_to_Qle _ _ Ht0).
    + apply QleT'_to_Qle. apply (b1_pq_ge0 n M t). exact Ht1.
Qed.

(* ========== §6 数值锚（独立复算比对点） ========== *)

(* 锚一：n=1, M=0, x=1：(1+1)²·A(1,0,−1) + (−1)¹·P(1,0,−1) = 4·1 − 3 = 1 *)
Lemma b1_master_anchor_110 :
  QeqT (q_pow (1 + (1 * 1)) (Datatypes.S 1) * b1_ps 1 0 (-(1 * 1))
        + q_pow (-(1 * 1)) (Datatypes.S 0) * b1_pq 1 0 (-(1 * 1))) (1 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚二：n=1, M=1, t=1/2：(1/2)²·A + (1/2)²·P = 1
   A(1,1,1/2) = 1 + 2·(1/2) = 2；P(1,1,1/2) = 1 + 2·(1/2) = 2；和 = 1 *)
Lemma b1_master_anchor_11half :
  QeqT (q_pow (1 - (1 # 2)) (Datatypes.S 1) * b1_ps 1 1 (1 # 2)
        + q_pow (1 # 2) (Datatypes.S 1) * b1_pq 1 1 (1 # 2)) (1 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* 锚三：P 正性实例：P(2,3,−4) = 1 + 4·5 + 10·25 = 271 > 0 *)
Lemma b1_pq_anchor :
  QeqT (b1_pq 2 3 (-(4 * 1))) (271 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* ========== §7 在件检验与假设审计 ========== *)

Check b1_master.
Check b1_master_arctan.
Check b1_pq_ge0.
Check b1_pq_ge0_arctan.
Check b1_ps_bound.
Check b1_ps_geom.
Check b1_shift.

Print Assumptions b1_master.
Print Assumptions b1_master_arctan.
Print Assumptions b1_pq_ge0.
Print Assumptions b1_pq_ge0_arctan.
Print Assumptions b1_ps_bound.
