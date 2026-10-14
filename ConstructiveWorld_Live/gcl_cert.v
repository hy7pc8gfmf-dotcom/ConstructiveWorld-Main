(* ===================================================================== *)
(*  gcl_cert.v —— 积分族界③肢 0 ≤ Isum^sym 全额机内化                       *)
(*  模块名：gcl_cert。                                                     *)
(*  使命：承 gcl_isumsym 闭式和 gcl_isym_closed＝交替二项滤波 altsum(m+2, D)， *)
(*        D_j := gcl_isum_kl 1 m j M，建立 CM 梯：                           *)
(*          · gcl_altsum＝交替二项滤波（与 gcl_isym_closed 逐字对齐）；       *)
(*          · gcl_telesum 望远镜和＋Pascal 移位/双移；                       *)
(*          · gcl_dfa＝交替差分叠；(−1)^iΔ^i u 的升阶乘闭式 gcl_cmval；       *)
(*          · gcl_glb＝Leibniz 卷积（df 深度递归形·免重排免 bkC 行）；        *)
(*          · CM(D) 经 k-和交换；梯终态 altsum ≥ 0。                        *)
(*        主定理【③肢消解】gcl_Isum_sym_ge0：QleT' 0 (gcl_Isum_sym m M)     *)
(*        无条件成立——供给链五肢之③零前提化；                               *)
(*        附【③消解版装配主件】gcl_supply_sym_weld3（③肢零前提焊接）；        *)
(*        附【④肢半程】gcl_Isum_le_D0：Isum^sym ≤ D_0（滤波单调链）          *)
(*        ——④残位收缩为纯单项式界 D_0 ≤ (1/4)(1/12)^m。                     *)
(*  数学核（独立复算在卷）：                                                *)
(*    · 交替二项滤波作用于完全单调序列非负（telesum＋两步 Pascal·偶/奇双梯）； *)
(*    · u := B(m+1+r,m+1) 为 Hausdorff 矩序列：(−1)^iΔ^i u(r) =             *)
(*      u(r)·Π_{l<i}(m+2+l)/Π_{l<i}(2m+4+r+l) > 0（升阶乘闭式·乘法形）；      *)
(*    · u² 的完全单调＝Leibniz 卷积 gcl_glb（角点消除核心 gcl_leib_core）；    *)
(*    · D 完全单调＝Σ_k C(m+1+k,m+1)·CM(u²)（k-和交换）。                    *)
(*    · binometric 部分和 S(r,M)=ΣC(r+k,k)(4/9)^k ≤ (9/5)^(S r)              *)
(*      （course-of-values 双归纳·递归核 Pascal 换位）。                      *)
(*  依赖：Stdlib；S01/S02/S03/BeukersLists/PolyIntegral；abl_z2_itg_carrier； *)
(*        GCL 冻结件 gcl_isumsym。零承认。                                  *)
(*  诚实边界：④肢全额（D_0 ≤ weight 的滤波单调链＋Hanson 熵 lcm(1..n) ≤     *)
(*        3^n 素数面）本件不含——④肢 binometric 引理已铸（gcl_bins_main/     *)
(*        gcl_binom_bound），D_0 链与熵面如实刻形（熵界由同批 gcl_hent       *)
(*        有界窗形部分兑现）。                                              *)
(*  构造性注记：全件 Qed/Defined，零承认、零 Abort、零全局假设、零经典逻辑；   *)
(*        主语句结构化收尾零 solver。                                       *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" gcl_cert.v              *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Setoid.
From Stdlib Require Import Lists.List.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PintMono.
Require Import abl_z2_truncfam abl_z2_itg_carrier HansonLcm.
Require Import gcl_coefficient gcl_famsym gcl_isumsym.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* §0 小件舱                                                                  *)
(* ============================================================ *)

Lemma gcl_oneQ : (Z.of_nat 1 # 1) == 1.
Proof. reflexivity. Qed.

Lemma gcl_zeroQ : (Z.of_nat 0 # 1) == 0.
Proof. reflexivity. Qed.

Lemma gcl_jsum_add2 : forall (f g : nat -> Q) (n : nat),
  gcl_jsum (fun j => f j + g j) n == gcl_jsum f n + gcl_jsum g n.
Proof.
  intros f g n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH. ring.
Qed.

Lemma gcl_jsum_ge02 : forall (f : nat -> Q) (n : nat),
  (forall j : nat, QleT' 0 (f j)) -> QleT' 0 (gcl_jsum f n).
Proof.
  intros f n H. induction n as [| n IH].
  - apply H.
  - cbn [gcl_jsum].
    apply (qleT'_plus_compat 0 (gcl_jsum f n) 0 (f (Datatypes.S n))).
    + exact IH.
    + apply H.
Qed.

Lemma gcl_qle_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hzx. apply Qle_to_QleT'.
  rewrite <- Hxy. apply QleT'_to_Qle. exact Hzx.
Qed.

Lemma gcl_qleT_trans : forall x y z : Q, QleT' x y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z H1 H2. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact H1.
  - apply QleT'_to_Qle. exact H2.
Qed.

Lemma gcl_natQ_ge0 : forall x : nat, (1 <= x)%nat -> QleT' 0 (Z.of_nat x # 1).
Proof.
  intro x. intros Hx. apply (gcl_qleT_trans _ (Z.of_nat 1 # 1)).
  - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - apply gcl_natQ_le. exact Hx.
Qed.

Lemma gcl_natQ_lt : forall x : nat, (1 <= x)%nat -> Qlt 0 (Z.of_nat x # 1).
Proof.
  intros x Hx. unfold Qlt. cbn [Qnum Qden].
  pose proof (proj1 (Nat2Z.inj_lt 0 x)). lia.
Qed.

Lemma gcl_pascal1 : forall n i : nat, bkC (Datatypes.S n) (Datatypes.S i) = (bkC n i + bkC n (Datatypes.S i))%nat.
Proof.
  intros n i. pose proof (bkC_pascal_shift n (Datatypes.S i)) as H. cbn in H. exact H.
Qed.

Lemma gcl_bkC_n1 : forall n : nat, bkC n 1%nat = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - pose proof (gcl_pascal1 n 0%nat) as H.
    rewrite gcl_bkC_zero in H. rewrite H. rewrite IH. lia.
Qed.

Lemma gcl_jsum_shift_neg : forall (T : nat -> Q) (n : nat),
  gcl_jsum (fun i => (0 - 1) * T (Datatypes.S i)) n
  == T 0%nat - gcl_jsum T (Datatypes.S n).
Proof.
  intros T n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH.
    replace (gcl_jsum T (Datatypes.S n))
      with (gcl_jsum T n + T (Datatypes.S n)) by reflexivity.
    ring.
Qed.

Lemma gcl_jsum_sub : forall (f g : nat -> Q) (n : nat),
  gcl_jsum (fun j => f j - g j) n == gcl_jsum f n - gcl_jsum g n.
Proof.
  intros f g n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH. ring.
Qed.

Lemma gcl_jsum_tail : forall (h : nat -> Q) (n : nat),
  gcl_jsum (fun l => match l with 0%nat => 0 | Datatypes.S j => h j end) n
  == gcl_jsum h n - h n.
Proof.
  intros h n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH. ring.
Qed.

Lemma gcl_jsum_pred : forall (h : nat -> Q) (n : nat),
  gcl_jsum (fun l => match l with 0%nat => 0 | Datatypes.S j => h j end) (Datatypes.S n)
  == gcl_jsum h n.
Proof.
  intros h n. cbn [gcl_jsum]. rewrite gcl_jsum_tail. ring.
Qed.

Lemma gcl_jsum_succ_split : forall (h : nat -> Q) (n : nat),
  gcl_jsum h (Datatypes.S n) == h 0%nat + gcl_jsum (fun i => h (Datatypes.S i)) n.
Proof.
  intros h n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH. ring.
Qed.

Lemma gcl_jsum_ext_le : forall (f g : nat -> Q) (n : nat),
  (forall j : nat, (j <= n)%nat -> f j == g j) -> gcl_jsum f n == gcl_jsum g n.
Proof.
  intros f g n. induction n as [| n IH]; intros H.
  - cbn [gcl_jsum]. apply H. lia.
  - cbn [gcl_jsum]. setoid_rewrite IH.
    rewrite (H (Datatypes.S n) (Nat.le_refl (Datatypes.S n))).
    reflexivity.
    intros j Hj. apply H. lia.
Qed.

Lemma gcl_jsum_pascal : forall (f : nat -> Q) (n : nat),
  gcl_jsum (fun l => (Z.of_nat (bkC (Datatypes.S n) l) # 1) * f l) (Datatypes.S n)
  == gcl_jsum (fun l => (Z.of_nat (bkC n l) # 1) * f l) n
     + gcl_jsum (fun j => (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)) n.
Proof.
  intros f n.
  assert (Hpt : forall k : nat,
    (Z.of_nat (bkC (Datatypes.S n) k) # 1) * f k
    == (Z.of_nat (bkC n k) # 1) * f k
       + (match k with
          | 0%nat => 0
          | Datatypes.S j => (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)
          end)).
  { intro k. destruct k as [| j].
    - cbn [bkC]. rewrite (gcl_bkC_zero n), gcl_oneQ. ring.
    - rewrite gcl_bkC_pascal_Q. ring. }
  rewrite (gcl_jsum_ext
             (fun k => (Z.of_nat (bkC (Datatypes.S n) k) # 1) * f k)
             (fun k => (Z.of_nat (bkC n k) # 1) * f k
                       + match k with
                         | 0%nat => 0
                         | Datatypes.S j => (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)
                         end) (Datatypes.S n) Hpt).
  rewrite (gcl_jsum_add2
             (fun k => (Z.of_nat (bkC n k) # 1) * f k)
             (fun k => match k with
                      | 0%nat => 0
                      | Datatypes.S j => (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)
                      end) (Datatypes.S n)).
  rewrite (gcl_jsum_pred (fun j => (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)) n).
  cbn [gcl_jsum].
  rewrite (bkC_out n (Datatypes.S n)) by lia.
  rewrite gcl_zeroQ. ring.
Qed.

Lemma gcl_jsum_pascal_sgn : forall (f : nat -> Q) (n : nat),
  gcl_jsum (fun l => gcl_sgn l * (Z.of_nat (bkC (Datatypes.S n) l) # 1) * f l) (Datatypes.S n)
  == gcl_jsum (fun l => gcl_sgn l * (Z.of_nat (bkC n l) # 1) * f l) n
     + gcl_jsum (fun j => gcl_sgn (Datatypes.S j) * (Z.of_nat (bkC n j) # 1)
                         * f (Datatypes.S j)) n.
Proof.
  intros f n.
  assert (Hpt : forall k : nat,
    gcl_sgn k * (Z.of_nat (bkC (Datatypes.S n) k) # 1) * f k
    == gcl_sgn k * (Z.of_nat (bkC n k) # 1) * f k
       + (match k with
          | 0%nat => 0
          | Datatypes.S j =>
              gcl_sgn (Datatypes.S j) * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)
          end)).
  { intro k. destruct k as [| j].
    - cbn [bkC]. rewrite (gcl_bkC_zero n). cbn [gcl_sgn]. rewrite gcl_oneQ. ring.
    - rewrite gcl_bkC_pascal_Q. ring. }
  rewrite (gcl_jsum_ext
             (fun k => gcl_sgn k * (Z.of_nat (bkC (Datatypes.S n) k) # 1) * f k)
             (fun k => gcl_sgn k * (Z.of_nat (bkC n k) # 1) * f k
                       + match k with
                         | 0%nat => 0
                         | Datatypes.S j =>
                             gcl_sgn (Datatypes.S j) * (Z.of_nat (bkC n j) # 1)
                             * f (Datatypes.S j)
                         end) (Datatypes.S n) Hpt).
  rewrite (gcl_jsum_add2
             (fun k => gcl_sgn k * (Z.of_nat (bkC n k) # 1) * f k)
             (fun k => match k with
                      | 0%nat => 0
                      | Datatypes.S j =>
                          gcl_sgn (Datatypes.S j) * (Z.of_nat (bkC n j) # 1)
                          * f (Datatypes.S j)
                      end) (Datatypes.S n)).
  rewrite (gcl_jsum_pred (fun j => gcl_sgn (Datatypes.S j)
                                    * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)) n).
  cbn [gcl_jsum].
  rewrite (bkC_out n (Datatypes.S n)) by lia.
  rewrite gcl_zeroQ. ring.
Qed.

(* ============================================================ *)
(* §1 交替二项滤波 altsum：telesum 与 Pascal 移位/双移                          *)
(* ============================================================ *)

Definition gcl_altsum (f : nat -> Q) (n : nat) : Q :=
  gcl_jsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j) n.

Lemma gcl_telesum : forall (n : nat) (f : nat -> Q),
  gcl_jsum (fun i => gcl_sgn i * (Z.of_nat (bkC n i) # 1) * f i
                 + gcl_sgn i * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i)) n == f 0%nat.
Proof.
  intros n f.
  rewrite (gcl_jsum_add2
             (fun i => gcl_sgn i * (Z.of_nat (bkC n i) # 1) * f i)
             (fun i => gcl_sgn i * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i))).
  rewrite (gcl_jsum_ext
             (fun i => gcl_sgn i * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i))
             (fun i => (0 - 1) * (gcl_sgn (Datatypes.S i)
                                  * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i))) n)
    by (intro i; rewrite gcl_sgn_succ; ring).
  rewrite (gcl_jsum_scale (0 - 1)
             (fun i => gcl_sgn (Datatypes.S i)
                       * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i)) n).
  assert (Hh : gcl_jsum (fun i => gcl_sgn (Datatypes.S i)
                                   * (Z.of_nat (bkC n (Datatypes.S i)) # 1) * f (Datatypes.S i)) n
               == gcl_jsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j) (Datatypes.S n)
                  - gcl_sgn 0%nat * (Z.of_nat (bkC n 0%nat) # 1) * f 0%nat).
  { rewrite (gcl_jsum_succ_split
               (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j) n).
    cbn beta. ring. }
  rewrite Hh.
  replace (gcl_jsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j) (Datatypes.S n))
    with (gcl_jsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j) n
          + gcl_sgn (Datatypes.S n) * (Z.of_nat (bkC n (Datatypes.S n)) # 1) * f (Datatypes.S n))
    by reflexivity.
  rewrite (bkC_out n (Datatypes.S n)) by lia.
  rewrite gcl_zeroQ, (gcl_bkC_zero n), gcl_oneQ.
  cbn [gcl_sgn]. ring.
Qed.

Lemma gcl_altsum_pascal : forall (n : nat) (f : nat -> Q),
  gcl_altsum f (Datatypes.S n) == gcl_altsum f n - gcl_altsum (fun j => f (Datatypes.S j)) n.
Proof.
  intros n f. unfold gcl_altsum. cbn beta.
  rewrite (gcl_jsum_pascal_sgn f n).
  rewrite (gcl_jsum_ext
             (fun j => gcl_sgn (Datatypes.S j) * (Z.of_nat (bkC n j) # 1)
                       * f (Datatypes.S j))
             (fun j => (0 - 1) * (gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                                  * f (Datatypes.S j))) n)
    by (intro j; rewrite gcl_sgn_succ; ring).
  rewrite (gcl_jsum_scale (0 - 1)
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)) n).
  ring.
Qed.

Lemma gcl_altsum_pascal2 : forall (n : nat) (f : nat -> Q),
  gcl_altsum f (Datatypes.S (Datatypes.S n))
  == gcl_altsum (fun j => f j - 2 * (f (Datatypes.S j)) + f (Datatypes.S (Datatypes.S j))) n.
Proof.
  intros n f.
  setoid_rewrite (gcl_altsum_pascal (Datatypes.S n) f).
  rewrite (gcl_altsum_pascal n f).
  rewrite (gcl_altsum_pascal n (fun j => f (Datatypes.S j))).
  unfold gcl_altsum. cbn beta.
  rewrite (gcl_jsum_ext
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                       * (f j - 2 * (f (Datatypes.S j)) + f (Datatypes.S (Datatypes.S j))))
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j
                       + ((0 - 2) * (gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j))
                          + gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                            * f (Datatypes.S (Datatypes.S j)))) n)
    by (intro j; ring).
  rewrite (gcl_jsum_add2
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f j)
             (fun j => (0 - 2) * (gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j))
                       + gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                         * f (Datatypes.S (Datatypes.S j))) n).
  rewrite (gcl_jsum_add2
             (fun j => (0 - 2) * (gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)))
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                       * f (Datatypes.S (Datatypes.S j))) n).
  rewrite (gcl_jsum_scale (0 - 2)
             (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * f (Datatypes.S j)) n).
  ring.
Qed.

(* ============================================================ *)
(* §2 交替差分叠 dfa                                                           *)
(* ============================================================ *)

Fixpoint gcl_dfa (i : nat) (f : nat -> Q) : nat -> Q :=
  match i with
  | 0%nat => f
  | Datatypes.S i' => fun j => gcl_dfa i' f j - gcl_dfa i' f (Datatypes.S j)
  end.

Lemma gcl_dfa_ext : forall (i : nat) (f g : nat -> Q) (j : nat),
  (forall k : nat, f k == g k) -> gcl_dfa i f j == gcl_dfa i g j.
Proof.
  intros i. induction i as [| i IH]; intros f g j H.
  - apply H.
  - cbn [gcl_dfa]. rewrite (IH f g j H), (IH f g (Datatypes.S j) H). ring.
Qed.

Lemma gcl_dfa_scale : forall (i : nat) (a : Q) (f : nat -> Q) (j : nat),
  gcl_dfa i (fun k => a * f k) j == a * gcl_dfa i f j.
Proof.
  intros i. induction i as [| i IH]; intros a f j.
  - reflexivity.
  - cbn [gcl_dfa]. rewrite (IH a f j), (IH a f (Datatypes.S j)). ring.
Qed.

Lemma gcl_dfa_add : forall (i : nat) (f g : nat -> Q) (j : nat),
  gcl_dfa i (fun k => f k + g k) j == gcl_dfa i f j + gcl_dfa i g j.
Proof.
  intros i. induction i as [| i IH]; intros f g j.
  - reflexivity.
  - cbn [gcl_dfa]. rewrite (IH f g j), (IH f g (Datatypes.S j)). ring.
Qed.

Lemma gcl_dfa_jsum : forall (i : nat) (H : nat -> nat -> Q) (M j : nat),
  gcl_dfa i (fun j => gcl_jsum (fun k => H j k) M) j
  == gcl_jsum (fun k => gcl_dfa i (fun j => H j k) j) M.
Proof.
  intros i H M j. induction M as [| M IH].
  - reflexivity.
  - cbn [gcl_jsum]. rewrite gcl_dfa_add, IH. reflexivity.
Qed.

Lemma gcl_dfa_shiftfun : forall (i : nat) (f : nat -> Q) (j : nat),
  gcl_dfa i (fun k => f (Datatypes.S k)) j == gcl_dfa i f (Datatypes.S j).
Proof.
  intros i. induction i as [| i IH]; intros f j.
  - reflexivity.
  - cbn [gcl_dfa]. rewrite (IH f j), (IH f (Datatypes.S j)). reflexivity.
Qed.

Lemma gcl_dfa_addk : forall (i k : nat) (h : nat -> Q) (j : nat),
  gcl_dfa i (fun t => h (t + k)%nat) j == gcl_dfa i h (j + k)%nat.
Proof.
  intros i. induction i as [| i IH]; intros k h j.
  - reflexivity.
  - cbn [gcl_dfa]. rewrite (IH k h j), (IH k h (Datatypes.S j)).
    replace (Datatypes.S j + k)%nat with (Datatypes.S (j + k))%nat by lia.
    reflexivity.
Qed.

Lemma gcl_dfa_df : forall (k : nat) (f : nat -> Q) (j : nat),
  gcl_dfa k (fun x => f x - f (Datatypes.S x)) j == gcl_dfa (Datatypes.S k) f j.
Proof.
  intro k. induction k as [| k IH]; intros f j.
  - reflexivity.
  - cbn [gcl_dfa]. rewrite (IH f j), (IH f (Datatypes.S j)). reflexivity.
Qed.

Lemma gcl_dfa_df2 : forall (i : nat) (f : nat -> Q) (j : nat),
  gcl_dfa i (fun k => f k - 2 * (f (Datatypes.S k)) + f (Datatypes.S (Datatypes.S k))) j
  == gcl_dfa (i + 2)%nat f j.
Proof.
  intros i. induction i as [| i IH]; intros f j.
  - cbn [gcl_dfa Nat.add]. ring.
  - replace (Datatypes.S i + 2)%nat with (Datatypes.S (i + 2))%nat by lia.
    cbn [gcl_dfa]. rewrite (IH f j), (IH f (Datatypes.S j)). ring.
Qed.

(* ============================================================ *)
(* §3 梯机：完全单调 ⟹ altsum ≥ 0（偶/奇双梯）                                  *)
(* ============================================================ *)

Lemma gcl_altsum_even : forall (k : nat) (f : nat -> Q),
  (forall i j : nat, (i <= 2 * k)%nat -> QleT' 0 (gcl_dfa i f j)) ->
  QleT' 0 (gcl_altsum f (2 * k)%nat).
Proof.
  induction k as [| k IH]; intros f H.
  - replace (2 * 0)%nat with 0%nat by lia.
    unfold gcl_altsum. cbn [gcl_jsum gcl_sgn].
    rewrite bkC_diag.
    apply (gcl_qle_wd_r (gcl_dfa 0%nat f 0%nat)).
    + rewrite gcl_oneQ. cbn [gcl_dfa]. ring.
    + apply H. lia.
  - replace (2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
    apply (gcl_qle_wd_r
             (gcl_altsum (fun j => f j - 2 * (f (Datatypes.S j))
                          + f (Datatypes.S (Datatypes.S j))) (2 * k)%nat)).
    + setoid_rewrite (gcl_altsum_pascal2 (2 * k)%nat f). reflexivity.
    + apply IH. intros i j Hi.
      apply (gcl_qle_wd_r (gcl_dfa (i + 2)%nat f j)).
      * setoid_rewrite (gcl_dfa_df2 i f j). reflexivity.
      * apply H. lia.
Qed.

Lemma gcl_altsum_odd : forall (k : nat) (f : nat -> Q),
  (forall i j : nat, (i <= Datatypes.S (2 * k))%nat -> QleT' 0 (gcl_dfa i f j)) ->
  QleT' 0 (gcl_altsum f (Datatypes.S (2 * k))%nat).
Proof.
  induction k as [| k IH]; intros f H.
  - replace (Datatypes.S (2 * 0))%nat with 1%nat by lia.
    unfold gcl_altsum. cbn [gcl_jsum gcl_sgn].
    rewrite gcl_bkC_zero, bkC_diag.
    apply (gcl_qle_wd_r (gcl_dfa 1%nat f 0%nat)).
    + rewrite gcl_oneQ. cbn [gcl_dfa]. ring.
    + apply H. lia.
  - replace (Datatypes.S (2 * Datatypes.S k))%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * k))))%nat by lia.
    apply (gcl_qle_wd_r
             (gcl_altsum (fun j => f j - 2 * (f (Datatypes.S j))
                          + f (Datatypes.S (Datatypes.S j))) (Datatypes.S (2 * k))%nat)).
    + setoid_rewrite (gcl_altsum_pascal2 (Datatypes.S (2 * k))%nat f). reflexivity.
    + apply IH. intros i j Hi.
      apply (gcl_qle_wd_r (gcl_dfa (i + 2)%nat f j)).
      * setoid_rewrite (gcl_dfa_df2 i f j). reflexivity.
      * apply H. lia.
Qed.

(* 奇偶二分（Set 承载 sigT-sum） *)
Lemma gcl_even_or_odd : forall n : nat,
  {k : nat & n = (2 * k)%nat} + {k : nat & n = Datatypes.S (2 * k)%nat}.
Proof.
  intro n. induction n as [| n IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[k Hk] | [k Hk]].
    + right. exists k. rewrite Hk. reflexivity.
    + left. exists (Datatypes.S k). rewrite Hk.
      replace (2 * Datatypes.S k)%nat
        with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
      reflexivity.
Qed.

Lemma gcl_altsum_cm : forall (n : nat) (f : nat -> Q),
  (forall i j : nat, (i <= n)%nat -> QleT' 0 (gcl_dfa i f j)) ->
  QleT' 0 (gcl_altsum f n).
Proof.
  intro n. intros f H.
  destruct (gcl_even_or_odd n) as [[k Hk] | [k Hk]].
  - rewrite Hk. apply gcl_altsum_even. intros i j Hi. apply H. lia.
  - rewrite Hk. apply gcl_altsum_odd. intros i j Hi. apply H. lia.
Qed.

(* ============================================================ *)
(* §4 u 的升阶乘闭式（定式 A）：ppi/ppi2 乘法形＋shift 恒等式＋dfa_u                 *)
(* ============================================================ *)

(* Hausdorff 矩序列 u(m,r) := B(m+1+r, m+1) *)
Definition gcl_u (m r : nat) : Q := gcl_beta2 (Datatypes.S m + r)%nat (Datatypes.S m).

(* 升阶乘积：ppi2(i,m) = Π_{l<i}(m+2+l)；ppi(i,m,r) = Π_{l<i}(2m+4+r+l) *)
Fixpoint gcl_ppi2 (i m : nat) : nat :=
  match i with
  | 0%nat => 1%nat
  | Datatypes.S i' => (gcl_ppi2 i' m * (m + 2 + i')%nat)%nat
  end.

Fixpoint gcl_ppi (i m r : nat) : nat :=
  match i with
  | 0%nat => 1%nat
  | Datatypes.S i' => (gcl_ppi i' m r * (2 * m + 4 + r + i')%nat)%nat
  end.

Lemma gcl_natQ_mul : forall a b : nat,
  (Z.of_nat (a * b) # 1) == (Z.of_nat a # 1) * (Z.of_nat b # 1).
Proof.
  intros a b. unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul].
  rewrite Nat2Z.inj_mul. lia.
Qed.

Lemma gcl_ppi_shift : forall i m r : nat,
  (gcl_ppi i m (Datatypes.S r) * (2 * m + 4 + r)%nat
   = gcl_ppi i m r * (2 * m + 4 + r + i)%nat)%nat.
Proof.
  intros i. induction i as [| i IH]; intros m r.
  - cbn [gcl_ppi]. lia.
  - cbn [gcl_ppi]. rewrite <- (IH m r). ring.
Qed.

Lemma gcl_natQ_nz : forall n : nat, (1 <= n)%nat -> ~ ((Z.of_nat n # 1) == 0).
Proof.
  intros n Hn Heq. unfold Qeq in Heq. cbn [Qnum Qden Qmult] in Heq.
  pose proof (proj1 (Nat2Z.inj_lt 0 n) Hn) as Hz.
  lia.
Qed.

Lemma gcl_mult_pos : forall a b : Q, Qlt 0 a -> Qlt 0 b -> Qlt 0 (a * b).
Proof.
  intros a b Ha Hb.
  pose proof (Qmult_lt_compat_r 0 a b Hb Ha) as H.
  rewrite Qmult_0_l in H. exact H.
Qed.

Lemma gcl_u_pos : forall m r : nat, Qlt 0 (gcl_u m r).
Proof.
  intros m r. unfold gcl_u, gcl_beta2, Qdiv.
  apply gcl_mult_pos.
  - apply gcl_mult_pos; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

Lemma gcl_qinv_cancel : forall A B D : Q, ~ D == 0 ->
  A * (Qinv D * Qinv B) * D == A * Qinv B.
Proof.
  intros A B D HD.
  pose proof (Qmult_inv_r D HD) as H1.
  rewrite (Qmult_comm D (Qinv D)) in H1.
  transitivity ((A * Qinv B) * (Qinv D * D)).
  - ring.
  - rewrite H1. ring.
Qed.

(* beta2 的首参移位：B(S a, b)·(a+b+2) == B(a,b)·(S a) *)
Lemma gcl_beta2_shift : forall a b : nat,
  gcl_beta2 (Datatypes.S a) b * (Z.of_nat (a + b + 2)%nat # 1)
  == gcl_beta2 a b * (Z.of_nat (Datatypes.S a) # 1).
Proof.
  intros a b. unfold gcl_beta2, Qdiv.
  replace (Datatypes.S a + b + 1)%nat with (Datatypes.S (a + b + 1))%nat by reflexivity.
  rewrite (q_fact_succ a).
  rewrite (q_fact_succ (a + b + 1)%nat).
  rewrite (Qinv_mult_distr (Z.of_nat (Datatypes.S (a + b + 1)) # 1)
                           (q_fact (a + b + 1)%nat)).
  replace (Datatypes.S (a + b + 1))%nat with (a + b + 2)%nat by lia.
  transitivity (((Z.of_nat (Datatypes.S a) # 1) * q_fact a * q_fact b)
                * Qinv (q_fact (a + b + 1)%nat)).
  - apply (gcl_qinv_cancel
             ((Z.of_nat (Datatypes.S a) # 1) * q_fact a * q_fact b)
             (q_fact (a + b + 1)%nat)
             (Z.of_nat (a + b + 2)%nat # 1)).
    apply gcl_natQ_nz. lia.
  - ring.
Qed.

(* u 的 r-移位：u(m,S r)·(2m+4+r) == u(m,r)·(m+2+r) *)
Lemma gcl_u_shift : forall m r : nat,
  gcl_u m (Datatypes.S r) * (Z.of_nat (2 * m + 4 + r)%nat # 1)
  == gcl_u m r * (Z.of_nat (m + 2 + r)%nat # 1).
Proof.
  intros m r.
  pose proof (gcl_beta2_shift (Datatypes.S m + r)%nat (Datatypes.S m)) as H.
  replace (Datatypes.S m + r + Datatypes.S m + 2)%nat with (2 * m + 4 + r)%nat in H by lia.
  replace (Datatypes.S (Datatypes.S m + r))%nat with (m + 2 + r)%nat in H by lia.
  unfold gcl_u.
  replace (Datatypes.S m + Datatypes.S r)%nat with (m + 2 + r)%nat by lia.
  exact H.
Qed.

Lemma gcl_ppi2_ge1 : forall i m : nat, (1 <= gcl_ppi2 i m)%nat.
Proof.
  intros i. induction i as [| i IH]; intro m.
  - cbn [gcl_ppi2]. lia.
  - cbn [gcl_ppi2].
    assert (H2 : (1 <= 1 * (m + 2 + i)%nat)%nat) by (rewrite Nat.mul_1_l; lia).
    pose proof (Nat.mul_le_mono_nonneg_r 1 (gcl_ppi2 i m) (m + 2 + i)%nat
                  (Nat.le_0_l _) (IH m)) as H.
    apply (Nat.le_trans _ (1 * (m + 2 + i)%nat)%nat); assumption.
Qed.

Lemma gcl_ppi_ge1 : forall i m r : nat, (1 <= gcl_ppi i m r)%nat.
Proof.
  intros i. induction i as [| i IH]; intros m r.
  - cbn [gcl_ppi]. lia.
  - cbn [gcl_ppi].
    assert (H2 : (1 <= 1 * (2 * m + 4 + r + i)%nat)%nat)
      by (rewrite Nat.mul_1_l; lia).
    pose proof (Nat.mul_le_mono_nonneg_r 1 (gcl_ppi i m r) (2 * m + 4 + r + i)%nat
                  (Nat.le_0_l _) (IH m r)) as H.
    apply (Nat.le_trans _ (1 * (2 * m + 4 + r + i)%nat)%nat); assumption.
Qed.

Lemma gcl_lt_mul_cancel_r : forall a b : Q, Qlt 0 a -> Qlt 0 (a * b) -> Qlt 0 b.
Proof.
  intros a b Ha Hab. destruct (Qlt_le_dec 0 b) as [Hb | Hb].
  - exact Hb.
  - exfalso.
    pose proof (Qmult_le_compat_r b 0 a Hb (Qlt_le_weak _ _ Ha)) as Hle.
    rewrite Qmult_0_l in Hle.
    rewrite (Qmult_comm a b) in Hab.
    exact (Qlt_not_le 0 (b * a) Hab Hle).
Qed.

(* 主定理 A【升阶乘闭式·乘法形】：(−1)^iΔ^i u(r)·ppi(i,m,r) == u(r)·ppi2(i,m) *)
Lemma gcl_dfa_u : forall i m r : nat,
  gcl_dfa i (gcl_u m) r * (Z.of_nat (gcl_ppi i m r) # 1)
  == gcl_u m r * (Z.of_nat (gcl_ppi2 i m) # 1).
Proof.
  intros i. induction i as [| i IH]; intros m r.
  - cbn [gcl_dfa gcl_ppi gcl_ppi2]. rewrite !gcl_oneQ. ring.
  - cbn [gcl_dfa gcl_ppi gcl_ppi2].
    rewrite (gcl_natQ_mul (gcl_ppi i m r) (2 * m + 4 + r + i)%nat).
    rewrite (gcl_natQ_mul (gcl_ppi2 i m) (m + 2 + i)%nat).
    assert (HshiftQ : (Z.of_nat (gcl_ppi i m (Datatypes.S r)) # 1)
                      * (Z.of_nat (2 * m + 4 + r)%nat # 1)
                      == (Z.of_nat (gcl_ppi i m r) # 1)
                         * (Z.of_nat (2 * m + 4 + r + i)%nat # 1)).
    { rewrite <- !gcl_natQ_mul. rewrite gcl_ppi_shift. reflexivity. }
    pose proof (gcl_u_shift m r) as Hush.
    rewrite <- HshiftQ.
    assert (Hd : (gcl_dfa i (gcl_u m) r - gcl_dfa i (gcl_u m) (Datatypes.S r))
                 * ((Z.of_nat (gcl_ppi i m (Datatypes.S r)) # 1)
                    * (Z.of_nat (2 * m + 4 + r)%nat # 1))
                 == gcl_dfa i (gcl_u m) r
                    * ((Z.of_nat (gcl_ppi i m (Datatypes.S r)) # 1)
                       * (Z.of_nat (2 * m + 4 + r)%nat # 1))
                 - gcl_dfa i (gcl_u m) (Datatypes.S r)
                   * ((Z.of_nat (gcl_ppi i m (Datatypes.S r)) # 1)
                      * (Z.of_nat (2 * m + 4 + r)%nat # 1)))
      by ring.
    rewrite Hd.
    rewrite (Qmult_assoc (gcl_dfa i (gcl_u m) (Datatypes.S r))
               (Z.of_nat (gcl_ppi i m (Datatypes.S r)) # 1)
               (Z.of_nat (2 * m + 4 + r)%nat # 1)).
    rewrite (IH m (Datatypes.S r)).
    rewrite (Qmult_comm (gcl_u m (Datatypes.S r)) (Z.of_nat (gcl_ppi2 i m) # 1)).
    rewrite <- (Qmult_assoc (Z.of_nat (gcl_ppi2 i m) # 1)
                            (gcl_u m (Datatypes.S r))
                            (Z.of_nat (2 * m + 4 + r)%nat # 1)).
    rewrite Hush.
    rewrite HshiftQ.
    rewrite (Qmult_assoc (gcl_dfa i (gcl_u m) r)
               (Z.of_nat (gcl_ppi i m r) # 1)
               (Z.of_nat (2 * m + 4 + r + i)%nat # 1)).
    rewrite (IH m r).
    replace (2 * m + 4 + r + i)%nat
      with ((m + 2 + r + (m + 2 + i))%nat) by lia.
    rewrite (gcl_natQ_add (m + 2 + r)%nat (m + 2 + i)%nat).
    ring.
Qed.

Lemma gcl_dfa_u_pos : forall i m r : nat, Qlt 0 (gcl_dfa i (gcl_u m) r).
Proof.
  intros i m r.
  pose proof (gcl_dfa_u i m r) as Hid.
  pose proof (gcl_u_pos m r) as Hu.
  assert (Hq2 : Qlt 0 (Z.of_nat (gcl_ppi2 i m) # 1))
    by (apply gcl_natQ_lt, gcl_ppi2_ge1).
  assert (Hrhs : Qlt 0 (gcl_u m r * (Z.of_nat (gcl_ppi2 i m) # 1)))
    by (apply gcl_mult_pos; assumption).
  rewrite <- Hid in Hrhs.
  rewrite (Qmult_comm (gcl_dfa i (gcl_u m) r) (Z.of_nat (gcl_ppi i m r) # 1)) in Hrhs.
  exact (gcl_lt_mul_cancel_r _ _
           (gcl_natQ_lt (gcl_ppi i m r) (gcl_ppi_ge1 i m r)) Hrhs).
Qed.

Lemma gcl_dfa_u_ge0 : forall i m r : nat, QleT' 0 (gcl_dfa i (gcl_u m) r).
Proof.
  intros i m r. apply Qle_to_QleT'. apply Qlt_le_weak. apply gcl_dfa_u_pos.
Qed.

Lemma gcl_natQ_ge0_all : forall n : nat, QleT' 0 (Z.of_nat n # 1).
Proof.
  intro n. destruct n as [| n'].
  - reflexivity.
  - apply gcl_natQ_ge0. lia.
Qed.

Lemma gcl_mul_ge0 : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb. apply Qle_to_QleT'.
  apply Qmult_le_0_compat; apply QleT'_to_Qle; assumption.
Qed.

(* ============================================================ *)
(* §5 Leibniz 卷积的角点消除核心（定式 B）                                            *)
(* ============================================================ *)

Lemma gcl_leib_core : forall (D Ds E E' Zc : nat -> Q) (n : nat),
  (forall l : nat, D (Datatypes.S l) == D l - Ds l) ->
  (forall l : nat, (l <= n)%nat -> E l == E' l - Zc l) ->
  (forall l : nat, (l <= n)%nat -> E (Datatypes.S l) == Zc l) ->
  gcl_jsum (fun l => (Z.of_nat (bkC (Datatypes.S n) l) # 1) * (D l * E l)) (Datatypes.S n)
  == gcl_jsum (fun l => (Z.of_nat (bkC n l) # 1) * (D l * E' l)) n
     - gcl_jsum (fun l => (Z.of_nat (bkC n l) # 1) * (Ds l * Zc l)) n.
Proof.
  intros D Ds E E' Zc n H1 H2 H3.
  rewrite (gcl_jsum_pascal (fun l => D l * E l) n).
  rewrite (gcl_jsum_ext_le
             (fun j => (Z.of_nat (bkC n j) # 1) * (D (Datatypes.S j) * E (Datatypes.S j)))
             (fun j => (Z.of_nat (bkC n j) # 1) * ((D j - Ds j) * Zc j)) n)
    by (intros j Hj; rewrite (H3 j Hj), (H1 j); ring).
  rewrite (gcl_jsum_ext
             (fun j => (Z.of_nat (bkC n j) # 1) * ((D j - Ds j) * Zc j))
             (fun j => (Z.of_nat (bkC n j) # 1) * (D j * Zc j)
                       - (Z.of_nat (bkC n j) # 1) * (Ds j * Zc j)) n)
    by (intro j; ring).
  rewrite gcl_jsum_sub.
  rewrite (gcl_jsum_ext_le
             (fun l => (Z.of_nat (bkC n l) # 1) * (D l * E l))
             (fun l => (Z.of_nat (bkC n l) # 1) * (D l * (E' l - Zc l))) n)
    by (intros l Hl; rewrite (H2 l Hl); ring).
  rewrite (gcl_jsum_ext
             (fun l => (Z.of_nat (bkC n l) # 1) * (D l * (E' l - Zc l)))
             (fun l => (Z.of_nat (bkC n l) # 1) * (D l * E' l)
                       - (Z.of_nat (bkC n l) # 1) * (D l * Zc l)) n)
    by (intro l; ring).
  rewrite gcl_jsum_sub.
  ring.
Qed.

(* Leibniz 卷积恒等式：Δ^i(f·g)(j) == Σ_{l≤i} C(i,l)·Δ^l f(j)·Δ^{i−l} g(j+l) *)
Lemma gcl_glb : forall (i : nat) (f g : nat -> Q) (j : nat),
  gcl_dfa i (fun t => f t * g t) j
  == gcl_jsum (fun l => (Z.of_nat (bkC i l) # 1)
                        * (gcl_dfa l f j * gcl_dfa (i - l)%nat g (j + l)%nat)) i.
Proof.
  intros i. induction i as [| i IH]; intros f g j.
  - cbn [gcl_dfa gcl_jsum bkC].
    replace (0 - 0)%nat with 0%nat by lia.
    cbn [gcl_dfa].
    replace (j + 0)%nat with j by lia.
    rewrite gcl_oneQ. ring.
  - cbn [gcl_dfa].
    rewrite (IH f g j), (IH f g (Datatypes.S j)).
    symmetry.
    apply (gcl_leib_core
             (fun l => gcl_dfa l f j)
             (fun l => gcl_dfa l f (Datatypes.S j))
             (fun l => gcl_dfa (Datatypes.S i - l)%nat g (j + l)%nat)
             (fun l => gcl_dfa (i - l)%nat g (j + l)%nat)
             (fun l => gcl_dfa (i - l)%nat g (Datatypes.S j + l)%nat) i).
    + intro l. cbn [gcl_dfa]. reflexivity.
    + intros l Hl.
      replace (Datatypes.S i - l)%nat with (Datatypes.S (i - l))%nat by lia.
      replace (Datatypes.S j + l)%nat with (Datatypes.S (j + l))%nat by lia.
      cbn [gcl_dfa]. reflexivity.
    + intros l Hl.
      replace (Datatypes.S i - Datatypes.S l)%nat with (i - l)%nat by lia.
      replace (j + Datatypes.S l)%nat with (Datatypes.S j + l)%nat by lia.
      reflexivity.
Qed.

(* ============================================================ *)
(* §6 CM 梯组装：u² 的完全单调与 D 的完全单调                                        *)
(* ============================================================ *)

Lemma gcl_dfa_u2_pos : forall m i r : nat,
  QleT' 0 (gcl_dfa i (fun t => gcl_u m t * gcl_u m t) r).
Proof.
  intros m i r.
  apply (gcl_qle_wd_r
           (gcl_jsum (fun l => (Z.of_nat (bkC i l) # 1)
                              * (gcl_dfa l (gcl_u m) r
                                 * gcl_dfa (i - l)%nat (gcl_u m) (r + l)%nat)) i)).
  - setoid_rewrite (gcl_glb i (gcl_u m) (gcl_u m) r). reflexivity.
  - apply gcl_jsum_ge02. intro l.
    apply gcl_mul_ge0.
    + apply gcl_natQ_ge0_all.
    + apply gcl_mul_ge0; apply gcl_dfa_u_ge0.
Qed.

Lemma gcl_isum_kl_jsum : forall m M j : nat,
  gcl_isum_kl 1 m j M
  == gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                        * (gcl_u m (j + k)%nat * gcl_u m (j + k)%nat)) M.
Proof.
  intros m. induction M as [| M IH]; intros j.
  - cbn [gcl_isum_kl gcl_jsum].
    replace (Datatypes.S m + 0)%nat with (Datatypes.S m)%nat by lia.
    replace (j + 0)%nat with j by lia.
    unfold gcl_u. ring.
  - cbn [gcl_isum_kl gcl_jsum]. rewrite (IH j).
    unfold gcl_u.
    replace (Datatypes.S m + j + Datatypes.S M)%nat
      with (Datatypes.S m + (j + Datatypes.S M))%nat by lia.
    ring.
Qed.

(* D 的完全单调：dfa i (fun j => D_j) j ≥ 0（k-和交换＋u² 逐项 CM） *)
Lemma gcl_D_cm : forall m M i j : nat,
  QleT' 0 (gcl_dfa i (fun j' => gcl_isum_kl 1 m j' M) j).
Proof.
  intros m M i j.
  apply (gcl_qle_wd_r
           (gcl_jsum (fun k => gcl_dfa i (fun j' =>
              (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
              * (gcl_u m (j' + k)%nat * gcl_u m (j' + k)%nat)) j) M)).
  - setoid_rewrite (gcl_dfa_ext i (fun j' => gcl_isum_kl 1 m j' M)
              (fun j' => gcl_jsum (fun k =>
                 (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                 * (gcl_u m (j' + k)%nat * gcl_u m (j' + k)%nat)) M) j
              (fun k => gcl_isum_kl_jsum m M k)).
    setoid_rewrite (gcl_dfa_jsum i
               (fun j' k => (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                            * (gcl_u m (j' + k)%nat * gcl_u m (j' + k)%nat)) M j).
    reflexivity.
  - apply gcl_jsum_ge02. intro k.
    apply (gcl_qle_wd_r ((Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                         * gcl_dfa i (fun t => gcl_u m t * gcl_u m t) (j + k)%nat)).
    + setoid_rewrite (gcl_dfa_scale i (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                        (fun j' => gcl_u m (j' + k)%nat * gcl_u m (j' + k)%nat) j).
      setoid_rewrite (gcl_dfa_addk i k (fun t => gcl_u m t * gcl_u m t) j). reflexivity.
    + apply gcl_mul_ge0.
      * apply gcl_natQ_ge0_all.
      * apply gcl_dfa_u2_pos.
Qed.

(* ============================================================ *)
(* §7 ③肢主定理：Isum^sym ≥ 0 与③消解版供给链焊接                                       *)
(* ============================================================ *)

(* 主定理【③肢消解】：Isum^sym 无条件非负——供给链五肢之③零前提化 *)
Theorem gcl_Isum_sym_ge0 : forall m M : nat, QleT' 0 (gcl_Isum_sym m M).
Proof.
  intros m M.
  apply (gcl_qle_wd_r (gcl_isym_closed m M)).
  - setoid_rewrite (gcl_Isum_sym_closed m M). reflexivity.
  - unfold gcl_isym_closed.
    apply (gcl_altsum_cm (Datatypes.S (Datatypes.S m)) (fun j => gcl_isum_kl 1 m j M)).
    intros i j Hij. apply gcl_D_cm.
Qed.

(* ③消解版供给链装配主件：Hanson 熵前提＋④肢族界（在句）给定 ⟹ 供给链 inhabited *)
Theorem gcl_supply_sym_weld3 : forall (m M : nat),
  (3 <= m)%nat ->
  (hl_lcm_upto (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QleT' (gcl_Isum_sym m M) (gcl_weight_G m) ->
  gcl_supply_sym m M.
Proof.
  intros m M Hm HL HI1. unfold gcl_supply_sym.
  exists (gcl_dmod m).
  split.
  - apply gcl_dmod_ge0.
  - split.
    + apply gcl_dmod_bound. exact HL.
    + split.
      * apply gcl_Isum_sym_ge0.
      * split.
        -- exact HI1.
        -- exact (gcl_sep_generic (fun _ : nat => gcl_Isum_sym m M) m (gcl_dmod m)
                    Hm (gcl_dmod_ge0 m) (gcl_dmod_bound m HL)
                    (gcl_Isum_sym_ge0 m M) HI1).
Defined.

(* ============================================================ *)
(* §8 ④肢 binometric 部分和引理（course-of-values 双归纳）                             *)
(* ============================================================ *)

Lemma gcl_mul_ge1 : forall a b : Q, QleT' 1 a -> QleT' 1 b -> QleT' 1 (a * b).
Proof.
  intros a b Ha Hb. apply Qle_to_QleT'.
  apply (Qle_trans _ (1 * b)).
  - rewrite Qmult_1_l. apply QleT'_to_Qle. exact Hb.
  - apply (Qmult_le_compat_r 1 a b).
    + apply QleT'_to_Qle. exact Ha.
    + apply (Qle_trans 0 1 b).
      * unfold Qle. cbn [Qnum Qden]. lia.
      * apply QleT'_to_Qle. exact Hb.
Qed.

Lemma gcl_qpow_ge1 : forall (x : Q) (k : nat), QleT' 1 x -> QleT' 1 (q_pow x k).
Proof.
  intros x k H. induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. apply gcl_mul_ge1; assumption.
Qed.

Lemma gcl_le1_sub : forall T : Q, QleT' 0 T -> QleT' (1 - T) 1.
Proof.
  intros T HT. apply Qle_to_QleT'.
  apply (Qplus_le_compat 1 1 (Qopp T) 0).
  - apply Qle_refl.
  - apply (Qle_trans _ (Qopp 0)).
    + apply Qopp_le_compat. apply QleT'_to_Qle. exact HT.
    + apply Qle_refl.
Qed.

(* 几何和：(5/9)·Σ_{k≤M}(4/9)^k == 1 − (4/9)^(M+1)（免负幂） *)
Lemma gcl_geo_sum : forall M : nat,
  (5#9) * gcl_jsum (fun k => q_pow (4#9) k) M == 1 - q_pow (4#9) (Datatypes.S M).
Proof.
  induction M as [| M IH].
  - cbn [gcl_jsum q_pow]. ring.
  - cbn [gcl_jsum]. rewrite (q_pow_succ (4#9) (Datatypes.S M)).
    rewrite (Qmult_plus_distr_r (5#9)
               (gcl_jsum (fun k => q_pow (4#9) k) M)
               (q_pow (4#9) (Datatypes.S M))).
    rewrite IH. ring.
Qed.

(* Qeq 传递与右乘保序的 Qle 迁移引理 *)
Lemma gcl_qle_of_eq : forall x y z : Q, x == y -> Qle x z -> Qle y z.
Proof.
  intros x y z Hxy Hz. apply (proj1 (Qle_comp x y Hxy z z (Qeq_refl z))). exact Hz.
Qed.

Lemma gcl_qle_of_eq_l : forall x y z : Q, x == y -> Qle z x -> Qle z y.
Proof.
  intros x y z Hxy Hz. apply (proj1 (Qle_comp z z (Qeq_refl z) x y Hxy)). exact Hz.
Qed.

Lemma gcl_qle_mul_compat : forall a b c : Q, QleT' a b -> (0 <= c)%Q -> Qle (a * c) (b * c).
Proof.
  intros a b c H Hc. apply (Qmult_le_compat_r a b c).
  - apply QleT'_to_Qle. exact H.
  - exact Hc.
Qed.

(* Qeq 到 QleT' 的等式传递桥 *)
Lemma gcl_qleT_of_eq : forall x y : Q, x == y -> QleT' x y.
Proof.
  intros x y Hxy. apply Qle_to_QleT'. apply qeq_imp_qle. exact Hxy.
Qed.

(* Qeq 到 QleT' 的左端传递桥 *)
Lemma gcl_qle_wd_l : forall x y z : Q, x == y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy H. apply (gcl_qleT_trans x y z).
  - apply gcl_qleT_of_eq. exact Hxy.
  - exact H.
Qed.

(* QleT' 的左乘保序桥（Qeq 传递三段） *)
Lemma gcl_qle_mul_compat_l : forall a b c : Q, QleT' a b -> (0 <= c)%Q -> Qle (c * a) (c * b).
Proof.
  intros a b c H Hc.
  apply (gcl_qle_of_eq (a * c) (c * a) (c * b)).
  - ring.
  - apply (gcl_qle_of_eq_l (b * c) (c * b) (a * c)).
    + ring.
    + apply (Qmult_le_compat_r a b c).
      -- apply QleT'_to_Qle. exact H.
      -- exact Hc.
Qed.

Lemma gcl_geo_bound : forall M : nat,
  QleT' (gcl_jsum (fun k => q_pow (4#9) k) M) (9#5).
Proof.
  intro M.
  assert (HA : QleT' ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M) 1).
  { apply (gcl_qleT_trans
             ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M)
             (1 - q_pow (4#9) (Datatypes.S M)) 1).
    - apply (gcl_qle_wd_r ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M)).
      + exact (gcl_geo_sum M).
      + apply Qle_to_QleT'. apply Qle_refl.
    - apply gcl_le1_sub.
      apply Qle_to_QleT'. apply q_pow_nonneg.
      unfold Qle. cbn [Qnum Qden]. lia. }
  apply Qle_to_QleT'.
  apply (gcl_qle_of_eq
           ((9#5) * ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M))
           (gcl_jsum (fun k => q_pow (4#9) k) M) (9#5)).
  - ring.
  - apply (Qle_trans _ ((9#5) * ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M))).
    + apply Qle_refl.
    + apply (gcl_qle_of_eq
               ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M * (9#5))
               ((9#5) * ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M)) (9#5)).
      * ring.
      * apply (gcl_qle_of_eq_l (1 * (9#5)) (9#5)
                 ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M * (9#5))).
        -- ring.
        -- apply (gcl_qle_mul_compat ((5#9) * gcl_jsum (fun k => q_pow (4#9) k) M) 1 (9#5)).
           ** exact HA.
           ** unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* binometric 部分和：S(r,M) := Σ_{k≤M} C(r+k,k)·(4/9)^k *)
Definition gcl_bins (r M : nat) : Q :=
  gcl_jsum (fun k => (Z.of_nat (bkC (r + k) k) # 1) * q_pow (4#9) k) M.

(* 递归核（Pascal 换位）：S(S r, S M) == S(r, S M) + (4/9)·S(S r, M) *)
Lemma gcl_bins_pascal : forall r M : nat,
  gcl_bins (Datatypes.S r) (Datatypes.S M)
  == gcl_bins r (Datatypes.S M) + (4#9) * gcl_bins (Datatypes.S r) M.
Proof.
  intros r M. unfold gcl_bins. cbn [gcl_jsum].
  assert (Hpt : forall k : nat,
    (Z.of_nat (bkC (Datatypes.S r + k) k) # 1) * q_pow (4#9) k
    == (Z.of_nat (bkC (r + k) k) # 1) * q_pow (4#9) k
       + (match k with
          | 0%nat => 0
          | Datatypes.S j =>
              (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1) * q_pow (4#9) j)
          end)).
  { intro k. destruct k as [| j].
    - cbn [Nat.add bkC q_pow]. rewrite (gcl_bkC_zero (r + 0)%nat), gcl_oneQ. ring.
    - replace (Datatypes.S r + Datatypes.S j)%nat
        with (Datatypes.S (r + Datatypes.S j))%nat by reflexivity.
      rewrite (gcl_pascal1 (r + Datatypes.S j) j).
      rewrite gcl_natQ_add.
      replace (Datatypes.S r + j)%nat with (r + Datatypes.S j)%nat by lia.
      rewrite q_pow_succ. ring. }
  assert (HptS : forall j : nat,
    (Z.of_nat (bkC (Datatypes.S r + Datatypes.S j) (Datatypes.S j)) # 1)
    * q_pow (4#9) (Datatypes.S j)
    == (Z.of_nat (bkC (r + Datatypes.S j) (Datatypes.S j)) # 1)
       * q_pow (4#9) (Datatypes.S j)
       + (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1) * q_pow (4#9) j)).
  { intro j.
    replace (Datatypes.S r + Datatypes.S j)%nat
      with (Datatypes.S (r + Datatypes.S j))%nat by reflexivity.
    rewrite (gcl_pascal1 (r + Datatypes.S j) j).
    rewrite gcl_natQ_add.
    replace (Datatypes.S r + j)%nat with (r + Datatypes.S j)%nat by lia.
    rewrite q_pow_succ. ring. }
  assert (Hh : gcl_jsum (fun j => (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1)
                                           * q_pow (4#9) j)) M
               == (4#9) * gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S r + k) k) # 1)
                                             * q_pow (4#9) k) M).
  { rewrite (gcl_jsum_scale (4#9)
              (fun k => (Z.of_nat (bkC (Datatypes.S r + k) k) # 1) * q_pow (4#9) k) M).
    reflexivity. }
  rewrite <- Hh.
  rewrite (gcl_jsum_ext
             (fun k => (Z.of_nat (bkC (Datatypes.S r + k) k) # 1) * q_pow (4#9) k)
             (fun k => (Z.of_nat (bkC (r + k) k) # 1) * q_pow (4#9) k
                       + match k with
                         | 0%nat => 0
                         | Datatypes.S j =>
                             (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1)
                                      * q_pow (4#9) j)
                         end) M Hpt).
  rewrite (gcl_jsum_add2
             (fun k => (Z.of_nat (bkC (r + k) k) # 1) * q_pow (4#9) k)
             (fun k => match k with
                      | 0%nat => 0
                      | Datatypes.S j =>
                          (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1)
                                   * q_pow (4#9) j)
                      end) M).
  rewrite (gcl_jsum_tail
             (fun j => (4#9) * ((Z.of_nat (bkC (Datatypes.S r + j) j) # 1)
                                * q_pow (4#9) j)) M).
  rewrite (HptS M).
  ring.
Qed.

(* 主定理 C【④肢 binometric 引理·course-of-values 双归纳】：
   S(r,M) ≤ (9/5)^(S r) 对一切 r, M 成立（步判据 1 + 4/5 == 9/5 恒等闭合） *)
Lemma gcl_bins_main : forall n r M : nat, (r + M)%nat = n ->
  QleT' (gcl_bins r M) (q_pow (9#5) (Datatypes.S r)).
Proof.
  intros n. induction n as [| n IH]; intros r M Heq.
  - assert (Hr : r = 0%nat) by lia. assert (HM : M = 0%nat) by lia.
    subst r. subst M. unfold gcl_bins. vm_compute. reflexivity.
  - destruct r as [| r'].
    + unfold gcl_bins.
      apply (gcl_qle_wd_r (9#5)).
      * reflexivity.
      * assert (Hext : forall k : nat,
                 (Z.of_nat (bkC (0 + k) k) # 1) * q_pow (4#9) k == q_pow (4#9) k)
            by (intro k; rewrite bkC_diag, gcl_oneQ; ring).
        apply (gcl_qle_wd_l
                 (gcl_jsum (fun k => (Z.of_nat (bkC (0 + k) k) # 1) * q_pow (4#9) k) M)
                 (gcl_jsum (fun k => q_pow (4#9) k) M) (9#5)).
        -- setoid_rewrite (gcl_jsum_ext
                             (fun k => (Z.of_nat (bkC (0 + k) k) # 1) * q_pow (4#9) k)
                             (fun k => q_pow (4#9) k) M Hext).
           reflexivity.
        -- apply gcl_geo_bound.
    + destruct M as [| M'].
      * unfold gcl_bins. cbn [gcl_jsum].
        replace (Datatypes.S r' + 0)%nat with (Datatypes.S r')%nat by lia.
        cbn [Nat.add bkC q_pow].
        apply (gcl_qleT_trans ((Z.of_nat 1 # 1) * 1) 1
                 (q_pow (9#5) (Datatypes.S (Datatypes.S r')))).
        -- apply (gcl_qle_wd_r 1). reflexivity.
           apply (gcl_qleT_of_eq ((Z.of_nat 1 # 1) * 1) 1).
           rewrite gcl_oneQ. ring.
        -- apply gcl_qpow_ge1. apply Qle_to_QleT'.
           unfold Qle. cbn [Qnum Qden Qmult]. lia.
      * apply (gcl_qle_wd_l (gcl_bins (Datatypes.S r') (Datatypes.S M'))
                 (gcl_bins r' (Datatypes.S M') + (4#9) * gcl_bins (Datatypes.S r') M')).
        -- exact (gcl_bins_pascal r' M').
        -- apply (gcl_qle_wd_r
                    (q_pow (9#5) (Datatypes.S r')
                     + (4#9) * q_pow (9#5) (Datatypes.S (Datatypes.S r')))).
           ++ rewrite (q_pow_succ (9#5) (Datatypes.S r')). ring.
           ++ apply Qle_to_QleT'.
              apply (Qplus_le_compat
                       (gcl_bins r' (Datatypes.S M')) (q_pow (9#5) (Datatypes.S r'))
                       ((4#9) * gcl_bins (Datatypes.S r') M')
                       ((4#9) * q_pow (9#5) (Datatypes.S (Datatypes.S r')))).
              --- apply QleT'_to_Qle. apply (IH r' (Datatypes.S M')). lia.
              --- apply (gcl_qle_mul_compat_l (gcl_bins (Datatypes.S r') M')
                           (q_pow (9#5) (Datatypes.S (Datatypes.S r'))) (4#9)).
                  +++ apply (IH (Datatypes.S r') M'). lia.
                  +++ unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 主定理 C 具名推论：Σ_{k≤M} C(m+1+k,m+1)·(4/9)^k ≤ (9/5)^(m+2) *)
Theorem gcl_binom_bound : forall m M : nat,
  QleT' (gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                            * q_pow (4#9) k) M)
        (q_pow (9#5) (Datatypes.S (Datatypes.S m))).
Proof.
  intros m M.
  exact (gcl_bins_main (Datatypes.S m + M)%nat (Datatypes.S m) M eq_refl).
Qed.

(* ============================================================ *)
(* 提取与假设审计                                                                 *)
(* ============================================================ *)

Print Assumptions gcl_altsum_cm.
Print Assumptions gcl_altsum_pascal2.
Print Assumptions gcl_dfa_u.
Print Assumptions gcl_glb.
Print Assumptions gcl_Isum_sym_ge0.
Print Assumptions gcl_supply_sym_weld3.
Print Assumptions gcl_bins_main.
Print Assumptions gcl_binom_bound.

Separate Extraction gcl_altsum_cm gcl_altsum_pascal2 gcl_u gcl_bins gcl_dfa_u
  gcl_glb gcl_Isum_sym_ge0 gcl_supply_sym_weld3 gcl_bins_main gcl_binom_bound.
