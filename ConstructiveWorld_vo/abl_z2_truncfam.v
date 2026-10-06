(* ===================================================================== *)
(*  abl_z2_truncfam.v —— ζ(2) 有理性二重积分族的 Taylor 截断展开与余项分离面   *)
(*  模块名：abl_z2_truncfam。                                            *)
(*  使命：对几何级数与二项阶系数的部分和母恒等式建立有理算术表述。对          *)
(*        n,M ≥ 0 与有理数 t，记 A(n,M,t) = Σ_{m≤M} C(n+m,n)·t^m（zb2_ps）、  *)
(*        U(n,M,t) = Σ_{m≤M} C(n+m,n+1)·t^m（zb2_psu）、                   *)
(*        P(n,M,t) = Σ_{i≤n} C(M+i,i)·(1−t)^i（zb2_pq）。证得：            *)
(*        ① 几何档 (1−t)·A(0,M,t) = 1 − t^{M+1}；② Pascal 档              *)
(*        A(n+1,M,t) = A(n,M,t) + U(n,M,t)；③ 位移档（对 M 归纳）          *)
(*        t·A − (1−t)·U = t^{M+1}·C(n+M+1,n+1)，其 Pascal 步              *)
(*        C(N,n)+C(N,n+1) = C(N+1,n+1) 由显式组合恒等式证书闭合；           *)
(*        ④ 母恒等式（对 n 归纳、M 泛化）：在 0 ≤ t ≤ 1 上                 *)
(*        (1−t)^{n+1}·A + t^{M+1}·P = 1，即截断 Taylor 和的除法自由形，     *)
(*        等价读法为 1 − (1−t)^{n+1}·A = t^{M+1}·P（余项显式分离面）；      *)
(*        ⑤ 序面：P ≥ 0 且 (1−t)^{n+1}·A ≤ 1（Set 层 QleT' 见证）。        *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia）；缓存根 S01_BaseRing、          *)
(*        S02_CauchyComplete（QleT' 桥与传递族）、S03_QExp（q_pow）、        *)
(*        BeukersLists（bkC 二项阶系数与 bk_psQ 指标和）。零外部证书器、      *)
(*        零实数层、零经典逻辑。                                          *)
(*  构造性：纯构造性、零假设声明、零承认式语句、零悬置假设；主语句面为        *)
(*        Qeq 等式与 Set 层序见证 QleT'；非线性组合步以显式 Pascal 恒等式     *)
(*        证书闭合，未引入任何有序域决策程序。                              *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no           *)
(*        -Q vo_local_world_unified_0930 "" -Q . "" abl_z2_truncfam.v。    *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.    *)
(*        London Math. Soc. 11 (1979) 中多项式族的 Taylor 截断构造步。       *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 基础小件：零档二项系数、有理像的和与 Pascal 恒等式                *)
(* ============================================================ *)

(* 二项系数零档：C(n,0) = 1（对全体 n） *)
Lemma zb2_bkC_zero : forall n : nat, bkC n 0 = 1%nat.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* 有理像系数和：单项分母 1 的 Q 像对 nat 加法分配 *)
Lemma zb2_ofC_add : forall a b : nat,
  (Z.of_nat (a + b) # 1) == ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* Pascal 恒等式的有理像：C(N+1,n+1) = C(N,n) + C(N,n+1) *)
Lemma zb2_pascalC : forall N n : nat,
  (Z.of_nat (bkC (Datatypes.S N) (Datatypes.S n)) # 1)
  == ((Z.of_nat (bkC N n) # 1) + (Z.of_nat (bkC N (Datatypes.S n)) # 1))%Q.
Proof.
  intros N n.
  assert (Hc := bkC_pascal_shift N (Datatypes.S n)).
  change ((bkC N n + bkC N (Datatypes.S n))%nat
          = bkC (Datatypes.S N) (Datatypes.S n)) in Hc.
  rewrite <- zb2_ofC_add. rewrite Hc. reflexivity.
Qed.

(* 二项系数有理像的非负性（Set 层见证） *)
Lemma zb2_bkC_Q_nonneg : forall n k : nat, QleT' 0 ((Z.of_nat (bkC n k) # 1)%Q).
Proof.
  intros n k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  destruct (le_lt_dec k n) as [Hle | Hlt].
  - assert (Hb : (1 <= bkC n k)%nat) by (apply bkC_pos; exact Hle).
    lia.
  - rewrite (bkC_out n k Hlt). cbn [Z.of_nat]. lia.
Qed.

(* Set 层序见证的右端换形：x == y、0 端任意 z 的 QleT' z x ⟹ QleT' z y *)
Lemma zb2_qleT'_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hz. apply Qle_to_QleT'.
  apply (Qle_trans z x y).
  - apply QleT'_to_Qle. exact Hz.
  - apply qeq_imp_qle. exact Hxy.
Qed.

(* 指标和的逐点加法外延：逐项 f = g + h 蕴含 Σf = Σg + Σh *)
Lemma zb2_bk_psQ_add : forall (f g h : nat -> Q) (N : nat) (z : Q),
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

(* ============================================================ *)
(* §1 截断族三定义（接口面，签名定死）                                  *)
(* ============================================================ *)

Definition zb2_ps (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) n) # 1)) (Datatypes.S M) t.

Definition zb2_psu (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) (Datatypes.S n)) # 1)) (Datatypes.S M) t.

Definition zb2_pq (n M : nat) (t : Q) : Q :=
  bk_psQ (fun i => (Z.of_nat (bkC (M + i) i) # 1)) (Datatypes.S n) (1 - t).

(* 末项剥离（定义性）：A(n,M+1,t) = A(n,M,t) + C(n+M+1,n)·t^{M+1} *)
Lemma zb2_ps_unfold : forall n M t,
  zb2_ps n (Datatypes.S M) t
  == (zb2_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold zb2_ps. cbn [bk_psQ]. reflexivity.
Qed.

(* 末项剥离（定义性）：U(n,M+1,t) = U(n,M,t) + C(n+M+1,n+1)·t^{M+1} *)
Lemma zb2_psu_unfold : forall n M t,
  zb2_psu n (Datatypes.S M) t
  == (zb2_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold zb2_psu. cbn [bk_psQ]. reflexivity.
Qed.

(* ============================================================ *)
(* §2 等式面：几何档、Pascal 档、位移档                                 *)
(* ============================================================ *)

(* 几何档：(1−t)·Σ_{m≤M} t^m = 1 − t^{M+1} *)
Lemma zb2_ps_geom : forall M t,
  (1 - t) * zb2_ps 0 M t == 1 - q_pow t (Datatypes.S M).
Proof.
  intros M. induction M as [| M IH]; intro t.
  - unfold zb2_ps. cbn [bk_psQ q_pow Nat.add bkC Z.of_nat]. ring.
  - rewrite zb2_ps_unfold.
    transitivity (((1 - t) * zb2_ps 0 M t
                   + (1 - t) * ((Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1)
                                * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1) with (1 # 1)%Q
        by (rewrite zb2_bkC_zero; reflexivity).
      rewrite (q_pow_succ t (Datatypes.S M)). ring.
Qed.

(* Pascal 档：A(n+1,M,t) = A(n,M,t) + U(n,M,t) *)
Lemma zb2_ps_pascal : forall n M t,
  zb2_ps (Datatypes.S n) M t == (zb2_ps n M t + zb2_psu n M t)%Q.
Proof.
  intros n M t. apply zb2_bk_psQ_add. intros k Hk.
  replace (Datatypes.S n + k)%nat with (Datatypes.S (n + k))%nat by reflexivity.
  rewrite (zb2_pascalC (n + k) n). ring.
Qed.

(* Pascal 步（定义性）：P(n+1,M,t) = P(n,M,t) + C(M+n+1,n+1)·(1−t)^{n+1} *)
Lemma zb2_pq_step : forall n M t,
  zb2_pq (Datatypes.S n) M t
  == (zb2_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 - t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold zb2_pq. cbn [bk_psQ]. reflexivity.
Qed.

(* 位移档：t·A − (1−t)·U = t^{M+1}·C(n+M+1,n+1)（对 M 归纳；
   基档出界件 C(n,n+1)=0 与对角件，步档 Pascal 恒等式证书） *)
Lemma zb2_shift : forall n M t,
  t * zb2_ps n M t - (1 - t) * zb2_psu n M t
  == (q_pow t (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M. revert n.
  induction M as [| M IH]; intros n t.
  - unfold zb2_ps, zb2_psu. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r. rewrite (bkC_diag n).
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    replace (n + Datatypes.S 0)%nat with (Datatypes.S n)%nat by lia.
    rewrite (bkC_diag (Datatypes.S n)).
    cbn [Z.of_nat]. ring.
  - rewrite zb2_ps_unfold. rewrite zb2_psu_unfold.
    transitivity (((t * zb2_ps n M t - (1 - t) * zb2_psu n M t)
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
      rewrite (zb2_pascalC (n + Datatypes.S M) n).
      rewrite (q_pow_succ t (Datatypes.S M)). ring.
Qed.

(* ============================================================ *)
(* §3 母恒等式与序面                                                    *)
(* ============================================================ *)

(* 上界用辅助恒等式：(1−t)·U = t·(s'·A) − s'·(t^{M+1}·C(n+M+1,n+1))，
   其中 s' = (1−t)^{n+1}；由位移档换形。 *)
Lemma zb2_shift_su : forall n M t,
  (1 - t) * q_pow (1 - t) (Datatypes.S n) * zb2_psu n M t
  == (t * (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)
      - q_pow (1 - t) (Datatypes.S n)
        * (q_pow t (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. rewrite <- (zb2_shift n M t). ring.
Qed.

(* 母恒等式：0 ≤ t ≤ 1 上 (1−t)^{n+1}·A + t^{M+1}·P = 1。
   代数读法：1 − (1−t)^{n+2}(A+U) = [1−(1−t)^{n+1}A] + (1−t)^{n+1}[tA−(1−t)U]，
   右端第一括号由归纳假设换为 t^{M+1}P，第二括号由位移档换为
   t^{M+1}C(n+M+1,n+1)，与 Pascal 步的新增项相消。 *)
Lemma zb2_master : forall n M t, 0 <= t <= 1 ->
  q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
  + q_pow t (Datatypes.S M) * zb2_pq n M t == 1.
Proof.
  intros n M t Ht. revert M.
  induction n as [| n IH]; intro M.
  - unfold zb2_pq. cbn [bk_psQ].
    change (q_pow (1 - t) (Datatypes.S 0)) with ((1 - t) * 1)%Q.
    change (q_pow (1 - t) 0) with 1%Q.
    assert (Hm : (1 - t) * 1 * zb2_ps 0 M t == (1 - t) * zb2_ps 0 M t) by ring.
    rewrite Hm. rewrite zb2_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite zb2_bkC_zero; reflexivity).
    ring.
  - assert (E := zb2_shift_su n M t).
    rewrite zb2_ps_pascal. rewrite zb2_pq_step.
    rewrite (q_pow_succ (1 - t) (Datatypes.S n)).
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
                    + q_pow t (Datatypes.S M) * zb2_pq n M t)
                   - t * (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)
                   + (1 - t) * q_pow (1 - t) (Datatypes.S n) * zb2_psu n M t
                   + q_pow t (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 - t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* P 的非负性：逐项 C(M+i,i)·(1−t)^i ≥ 0 *)
Lemma zb2_pq_ge0 : forall n M t, 0 <= t <= 1 -> QleT' 0 (zb2_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t Ht.
  - unfold zb2_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    apply (zb2_qleT'_wd_r (Z.of_nat (bkC M 0) # 1)
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply zb2_bkC_Q_nonneg.
  - apply (zb2_qleT'_wd_r
             ((zb2_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 - t) (Datatypes.S n))%Q)
             (zb2_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (zb2_pq_step n M t)).
    + apply Qle_to_QleT'.
      destruct Ht as [Ht0 Ht1].
      assert (Hsub : Qle 0 (1 - t)).
      { unfold Qle in *. cbn [Qnum Qden Qminus Qplus Qopp Qmult] in *. lia. }
      apply (Qplus_le_compat 0 (zb2_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 - t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. split; assumption.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- apply (q_pow_nonneg (1 - t) (Datatypes.S n)). exact Hsub.
Qed.

(* 部分和的除法自由上界：(1−t)^{n+1}·A ≤ 1。
   由母恒等式 1 = (1−t)^{n+1}A + t^{M+1}P 与 t^{M+1}P ≥ 0。 *)
Lemma zb2_ps_bound : forall n M t, 0 <= t <= 1 ->
  QleT' (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t) 1.
Proof.
  intros n M t Ht.
  apply (zb2_qleT'_wd_r
           (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
            + q_pow t (Datatypes.S M) * zb2_pq n M t) 1
           (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)).
  - exact (zb2_master n M t Ht).
  - apply qleT'_plus_nonneg_rT.
    apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply (q_pow_nonneg t (Datatypes.S M)).
      destruct Ht as [Ht0 _]. exact Ht0.
    + apply QleT'_to_Qle. apply zb2_pq_ge0. exact Ht.
Qed.

(* 数值锚：A(1,1,1/2) = C(1,1) + C(2,1)·(1/2) = 1 + 1 = 2 *)
Lemma zb2_ps_anchor1 : zb2_ps 1 1 (1 # 2) == 2.
Proof.
  vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §4 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions zb2_ps_geom.
Print Assumptions zb2_ps_pascal.
Print Assumptions zb2_pq_step.
Print Assumptions zb2_shift.
Print Assumptions zb2_master.
Print Assumptions zb2_pq_ge0.
Print Assumptions zb2_ps_bound.
Print Assumptions zb2_ps_anchor1.
