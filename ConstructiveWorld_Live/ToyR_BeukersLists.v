(* ==========================================================================)
   ToyR_BeukersLists.v — Beukers 序列的列表化构造与 3^n 下界
   使命: bkC 二项系数（Pascal 递归、对称 bk_Qn_sym、正性）、bk_psd 幂和格式（bk_psd_binom == 3^n）、bk_Qn_qtilde 平方和与 bk_Qn_ge_3pow_nat 下界、bkQ/bk_Qn_list 列表求值面。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib QArith
   对标: Apéry–Beukers 型序列 q_n = Σ_k C(n,k)^2 的构造性列表实现与 3^n 增长下界。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.

(* QArith 泄漏 Q_scope（裸数字被判读为 Q 构造元），压回 nat 优先 *)
Open Scope nat_scope.

(* ============================================================ *)
(* §A nat 层二项式系数（Pascal 递归）与对称引理                          *)
(* ============================================================ *)

(* Pascal 递归二项式系数 C(n,k)（名字 bkC 避免与 C 遮蔽冲突） *)
Fixpoint bkC (n k : nat) : nat :=
  match n with
  | 0 => match k with
         | 0 => 1
         | Datatypes.S _ => 0
         end
  | Datatypes.S n' =>
      match k with
      | 0 => 1
      | Datatypes.S k' => bkC n' k' + bkC n' (Datatypes.S k')
      end
  end.

(* 出界件：k > n 时 C(n,k) = 0 *)
Lemma bkC_out : forall n k : nat, n < k -> bkC n k = 0.
Proof.
  induction n as [| n IH]; intros k Hk.
  - destruct k as [| k'].
    + lia.
    + reflexivity.
  - destruct k as [| k'].
    + lia.
    + cbn [bkC].
      rewrite (IH k') by lia.
      rewrite (IH (Datatypes.S k')) by lia.
      reflexivity.
Qed.

(* 对角件：C(n,n) = 1 *)
Lemma bkC_diag : forall n : nat, bkC n n = 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [bkC].
    rewrite IH.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    reflexivity.
Qed.

(* 正性件：k ≤ n 时 C(n,k) ≥ 1 *)
Lemma bkC_pos : forall n k : nat, k <= n -> 1 <= bkC n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [bkC]. lia.
  - destruct k as [| k'].
    + cbn [bkC]. lia.
    + cbn [bkC].
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : 1 <= bkC n k') by (apply IH; lia).
        assert (H2 : 1 <= bkC n (Datatypes.S k')) by (apply IH; lia).
        lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        rewrite (bkC_out n (Datatypes.S n)) by lia.
        assert (H1 : 1 <= bkC n n) by (apply IH; lia).
        lia.
Qed.

(* 逐点 Pascal 恒等：shift(C n)(k) + C(n,k) = C(S n,k)（k 分支全定义性） *)
Lemma bkC_pascal_shift : forall n k : nat,
  (match k with
   | 0 => 0
   | Datatypes.S j => bkC n j
   end) + bkC n k = bkC (Datatypes.S n) k.
Proof.
  intros n k. destruct k as [| j].
  - destruct n as [| n']; reflexivity.
  - cbn [bkC]. reflexivity.
Qed.

(* 对称引理：C(n,k) = C(n,n−k)（后续恒等式归纳用——P2 接口件） *)
Lemma bk_Qn_sym : forall n k : nat, k <= n -> bkC n k = bkC n (n - k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [| k'].
    + replace (Datatypes.S n - 0) with (Datatypes.S n) by lia.
      rewrite (bkC_diag (Datatypes.S n)). reflexivity.
    + replace (Datatypes.S n - Datatypes.S k') with (n - k') by lia.
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : bkC n k' = bkC n (n - k')) by (apply IH; lia).
        assert (H2 : bkC n (Datatypes.S k') = bkC n (n - Datatypes.S k'))
          by (apply IH; lia).
        assert (Hn1 : n - k' = Datatypes.S (n - Datatypes.S k')) by lia.
        rewrite Hn1 in H1.
        rewrite Hn1.
        cbn [bkC]. lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        replace (n - n) with 0 by lia.
        rewrite (bkC_diag (Datatypes.S n)).
        reflexivity.
Qed.

(* ============================================================ *)
(* §B nat 层降幂加权和 bk_psd 与二项定理 (1+2)^n                        *)
(*   bk_psd f n = Σ_{k<n} f(k)·2^{n−1−k}，递归 bk_psd f (S m) =        *)
(*   2·bk_psd f m + f m（降幂步进恰为翻倍）。                           *)
(* ============================================================ *)

Fixpoint bk_psd (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => 2 * bk_psd f m + f m
  end.

Lemma bk_psd_ext : forall (N : nat) (f g : nat -> nat),
  (forall k : nat, k < N -> f k = g k) -> bk_psd f N = bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g H.
  - reflexivity.
  - cbn [bk_psd].
    rewrite (IH f g) by (intro k; intro Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma bk_psd_add : forall (N : nat) (f g : nat -> nat),
  bk_psd (fun k => f k + g k) N = bk_psd f N + bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g.
  - reflexivity.
  - cbn [bk_psd]. rewrite IH. lia.
Qed.

(* 移位件：系数行整体右移一位（头部垫零） ⟹ 和恰为原和降一档 *)
Lemma bk_psd_shift : forall (m : nat) (g : nat -> nat),
  bk_psd (fun k => match k with
                   | 0 => 0
                   | Datatypes.S j => g j
                   end) (Datatypes.S m) = bk_psd g m.
Proof.
  induction m as [| m IH]; intros g.
  - reflexivity.
  - assert (Hunf : bk_psd (fun k => match k with
                                    | 0 => 0
                                    | Datatypes.S j => g j
                                    end) (Datatypes.S (Datatypes.S m))
                 = 2 * bk_psd (fun k => match k with
                                        | 0 => 0
                                        | Datatypes.S j => g j
                                        end) (Datatypes.S m)
                   + g m)
      by reflexivity.
    rewrite Hunf, IH. reflexivity.
Qed.

(* 二项定理降幂形：Σ_{k≤n} C(n,k)·2^{n−k} = (1+2)^n = 3^n
   （stdlib 无二项定理，自建——库存勘定见头注） *)
Lemma bk_psd_binom : forall n : nat,
  bk_psd (fun k => bkC n k) (Datatypes.S n) = 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [bk_psd]. replace (2 * 0)%nat with 0%nat by lia. reflexivity.
  - replace (bk_psd (fun k => bkC (Datatypes.S n) k) (Datatypes.S (Datatypes.S n)))
      with (bk_psd (fun k => (match k with
                             | 0 => 0
                             | Datatypes.S j => bkC n j
                             end) + bkC n k) (Datatypes.S (Datatypes.S n)))
      by (apply bk_psd_ext; intro k; intro Hk; apply bkC_pascal_shift).
    rewrite bk_psd_add.
    assert (IH' : bk_psd (bkC n) (Datatypes.S n) = 3 ^ n) by exact IH.
    assert (Hsh : bk_psd (fun k => match k with
                                   | 0 => 0
                                   | Datatypes.S j => bkC n j
                                   end) (Datatypes.S (Datatypes.S n))
                = bk_psd (bkC n) (Datatypes.S n))
      by (apply (bk_psd_shift (Datatypes.S n) (bkC n))).
    assert (Hunf : bk_psd (bkC n) (Datatypes.S (Datatypes.S n))
                 = 2 * bk_psd (bkC n) (Datatypes.S n)
                   + bkC n (Datatypes.S n))
      by reflexivity.
    rewrite Hsh, Hunf, IH'.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

(* 单调件：逐点 ≤ ⟹ 和 ≤ *)
Lemma bk_psd_mono : forall (N : nat) (f h : nat -> nat),
  (forall k : nat, k < N -> f k <= h k) -> bk_psd f N <= bk_psd h N.
Proof.
  induction N as [| N IH]; intros f h H.
  - reflexivity.
  - cbn [bk_psd].
    assert (H1 : bk_psd f N <= bk_psd h N)
      by (apply IH; intro k; intro Hk; apply H; lia).
    assert (H2 : f N <= h N) by (apply H; lia).
    lia.
Qed.

(* ============================================================ *)
(* §C nat 层 q̃_n 与 3^n 下界（nat 脚手架面）                            *)
(* ============================================================ *)

(* q̃_n := Σ_{k≤n} C(n,k)²·2^{n−k}（= 2^n·Q_n(1/2) 的 nat 承载） *)
Definition bk_Qn_qtilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n).

Lemma bk_Qn_ge_3pow_nat : forall n : nat, 3 ^ n <= bk_Qn_qtilde n.
Proof.
  intro n.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n -> bkC n k <= bkC n k * bkC n k).
  { intro k. intro Hk.
    assert (Hk' : k <= n) by lia.
    assert (Hpos := bkC_pos n k Hk').
    nia. }
  assert (Hmono := bk_psd_mono (Datatypes.S n)
                     (fun k => bkC n k)
                     (fun k => bkC n k * bkC n k) Hpt).
  rewrite <- (bk_psd_binom n).
  exact Hmono.
Qed.

(* nat→Q 桥：Qle 的 nat 像 *)
Lemma bk_Qle_nat : forall a b : nat, (a <= b)%nat -> Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H.
  unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply Nat2Z.inj_le.
  exact H.
Qed.

(* ============================================================ *)
(* §D Q 层：Q_n 系数列表、求值面与整性见证                               *)
(* ============================================================ *)

(* Horner 折叠求值（头为常数项） *)
Fixpoint bkQ (p : list Q) (z : Q) : Q :=
  match p with
  | nil => 0%Q
  | c :: p' => c + z * bkQ p' z
  end.

(* 索引列表核：bk_idx N = [0;1;...;N−1]（列表 Fixpoint 承载字母） *)
Fixpoint bk_idx (N : nat) : list nat :=
  match N with
  | 0 => nil
  | Datatypes.S m => bk_idx m ++ (m :: nil)
  end.

Lemma bk_idx_seq : forall N : nat, bk_idx N = seq 0 N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [bk_idx]. rewrite IH.
    rewrite (seq_S N 0). reflexivity.
Qed.

(* Q_n 系数列表：第 k 项 = C(n,k)²（bkC 平方的 Q 像），k = 0..n *)
Definition bk_Qn_list (n : nat) : list Q :=
  map (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (bk_idx (Datatypes.S n)).

(* 求值函数（列表折叠面） *)
Definition bk_Qn_eval (n : nat) (z : Q) : Q := bkQ (bk_Qn_list n) z.

(* Q 层指标和核：bk_psQ f N z = Σ_{k<N} f(k)·z^k *)
Fixpoint bk_psQ (f : nat -> Q) (N : nat) (z : Q) : Q :=
  match N with
  | 0 => 0%Q
  | Datatypes.S m => bk_psQ f m z + f m * q_pow z m
  end.

Lemma bkQ_app : forall (p q : list Q) (z : Q),
  bkQ (p ++ q) z == bkQ p z + q_pow z (length p) * bkQ q z.
Proof.
  induction p as [| a p' IH]; intros q z.
  - cbn [app length bkQ q_pow]. ring.
  - cbn [app length bkQ].
    rewrite IH.
    rewrite (q_pow_succ z (length p')).
    ring.
Qed.

(* 列表↔指标和：bkQ (map f (seq 0 (S N))) z == Σ_{k<S N} f(k)·z^k *)
Lemma bkQ_seq_map : forall (N : nat) (f : nat -> Q) (z : Q),
  bkQ (map f (seq 0 (Datatypes.S N))) z == bk_psQ f (Datatypes.S N) z.
Proof.
  induction N as [| N IH]; intros f z.
  - cbn [seq map bkQ bk_psQ q_pow]. ring.
  - replace (seq 0 (Datatypes.S (Datatypes.S N)))
      with (seq 0 (Datatypes.S N) ++ (Datatypes.S N :: nil))
      by (rewrite (seq_S (Datatypes.S N) 0); reflexivity).
    rewrite map_app.
    rewrite bkQ_app.
    rewrite map_length, seq_length.
    cbn [map bkQ].
    rewrite IH.
    assert (Hunf : bk_psQ f (Datatypes.S (Datatypes.S N)) z
                 = (bk_psQ f (Datatypes.S N) z
                    + f (Datatypes.S N) * q_pow z (Datatypes.S N))%Q)
      by reflexivity.
    rewrite Hunf.
    ring.
Qed.

(* 逐项像：k 越界排除下 map+seq 的第 k 项 == f k *)
Lemma bk_nth_map_lt : forall (f : nat -> Q) (l : list nat) (k : nat) (d : Q),
  k < length l -> nth k (map f l) d == f (nth k l 0).
Proof.
  intros f l. induction l as [| a l' IH]; intros k d Hk.
  - exfalso. cbn [length] in Hk. lia.
  - destruct k as [| k'].
    + cbn [map nth]. apply Qeq_refl.
    + cbn [map nth]. apply IH. cbn [length] in Hk. lia.
Qed.

Lemma bk_nth_map_seq : forall (f : nat -> Q) (N k : nat) (d : Q),
  k < Datatypes.S N -> nth k (map f (seq 0 (Datatypes.S N))) d == f k.
Proof.
  intros f N k d Hk.
  replace (f k) with (f (nth k (seq 0 (Datatypes.S N)) 0)).
  - apply (bk_nth_map_lt f (seq 0 (Datatypes.S N)) k d).
    rewrite seq_length. lia.
  - apply f_equal. rewrite seq_nth by lia. reflexivity.
Qed.

(* 系数逐项刻画：第 k 项 == C(n,k)² 的 Q 像 *)
Lemma bk_Qn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Qn_list n) 0%Q == (Z.of_nat (bkC n k * bkC n k) # 1)%Q.
Proof.
  intros n k Hk.
  unfold bk_Qn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* ============================================================ *)
(* §D2 换基核心与整性见证（本件非平凡主件）                              *)
(* ============================================================ *)

Lemma bk_q_pow_mul : forall (x y : Q) (k : nat),
  q_pow (x * y) k == q_pow x k * q_pow y k.
Proof.
  intros x y k. induction k as [| k IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma bk_q_pow_one : forall k : nat, q_pow 1%Q k == 1%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

Lemma bk_Qmul_nat : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1))%Q == (Z.of_nat (a * b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_mul. reflexivity.
Qed.

Lemma bk_Qadd_nat : forall a b : nat,
  ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q == (Z.of_nat (a + b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* 换基核心（非平凡主件）：2^n·Σ_{k<S n} Q#f(k)·(1/2)^k == Q#Σ_{k<S n} f(k)2^{n−k}
   ——降幂 nat 和 bk_psd 承载，纯点算归纳，免对称重排 *)
Lemma bk_half_psd : forall (n : nat) (g : nat -> nat),
  q_pow (2 # 1)%Q n
    * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q) (Datatypes.S n) (1 # 2)%Q
  == (Z.of_nat (bk_psd g (Datatypes.S n)) # 1)%Q.
Proof.
  intros n g. induction n as [| n IH].
  - cbn [q_pow bk_psQ bk_psd].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - assert (Hhalf : (2 # 1)%Q * (1 # 2)%Q == 1%Q)
      by (compute; reflexivity).
    assert (Hunf : bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S (Datatypes.S n)) (1 # 2)%Q
                 = (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S n) (1 # 2)%Q
                   + ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))%Q)%Q)
      by reflexivity.
    rewrite Hunf.
    rewrite Qmult_plus_distr_r.
    assert (EA : q_pow (2 # 1)%Q (Datatypes.S n)
                   * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                       (Datatypes.S n) (1 # 2)%Q
                 == (Z.of_nat (2 * bk_psd g (Datatypes.S n)) # 1)%Q).
    { rewrite (q_pow_succ (2 # 1)%Q n).
      rewrite <- (Qmult_assoc (2 # 1)%Q (q_pow (2 # 1)%Q n)
                    (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                        (Datatypes.S n) (1 # 2)%Q)).
      rewrite IH.
      replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
      apply bk_Qmul_nat. }
    assert (EB : q_pow (2 # 1)%Q (Datatypes.S n)
                   * ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))
                 == (Z.of_nat (g (Datatypes.S n)) # 1) * 1%Q).
    { transitivity ((Z.of_nat (g (Datatypes.S n)) # 1)
                      * (q_pow (2 # 1)%Q (Datatypes.S n)
                           * q_pow (1 # 2)%Q (Datatypes.S n)))%Q.
      - ring.
      - rewrite <- (bk_q_pow_mul (2 # 1)%Q (1 # 2)%Q (Datatypes.S n)).
        rewrite Hhalf. rewrite bk_q_pow_one. reflexivity. }
    rewrite EA, EB, Qmult_1_r.
    apply bk_Qadd_nat.
Qed.

(* 半整数点闭式：bkQ (bk_Qn_list n) (1/2) 的 2^n 升格 == Q#q̃_n *)
Lemma bk_Qn_half_closed : forall n : nat,
  q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q
  == (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.
Proof.
  intro n.
  unfold bk_Qn_list.
  rewrite bk_idx_seq.
  rewrite bkQ_seq_map.
  apply bk_half_psd.
Qed.

(* 主件②：整性见证 q̃_n = 2^n·Q_n(1/2) ∈ Z（sigT + QeqT，Set 面） *)
Theorem bk_Qn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q) ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (bk_Qn_qtilde n)).
  apply qeq_imp_qeqT.
  apply bk_Qn_half_closed.
Qed.

(* 主件③：q̃_n ≥ 3^n（QleT' Set 面） *)
Theorem bk_Qn_ge_3pow : forall n : nat,
  QleT' ((Z.of_nat (3 ^ n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply bk_Qle_nat.
  apply bk_Qn_ge_3pow_nat.
Qed.

(* 求值面语义：bk_Qn_eval n z == Σ_{k≤n} C(n,k)²·z^k（QeqT Set 面） *)
Theorem bk_Qn_eval_sem : forall (n : nat) (z : Q),
  QeqT (bk_Qn_eval n z)
       (bk_psQ (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Qn_eval, bk_Qn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.

(* ============================================================ *)
(* ============================================================ *)

(* 谐和数 H_k = Σ_{j=1}^{k} 1/j（Q 层 Fixpoint） *)
Fixpoint bk_H (k : nat) : Q :=
  match k with
  | 0 => 0%Q
  | Datatypes.S k' => bk_H k' + (1%Q / (Z.of_nat (Datatypes.S k') # 1))%Q
  end.

(* P_n 系数列表：第 k 项 = C(n,k)²·H_k *)
Definition bk_Pn_list (n : nat) : list Q :=
  map (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
      (bk_idx (Datatypes.S n)).

(* 求值面：bkQ (bk_Pn_list n) z == Σ_{k≤n} C(n,k)²·H_k·z^k（QeqT Set 面） *)
Theorem bk_Pn_eval : forall (n : nat) (z : Q),
  QeqT (bkQ (bk_Pn_list n) z)
       (bk_psQ (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Pn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.

(* P_n 系数逐项刻画 *)
Lemma bk_Pn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Pn_list n) 0%Q == ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q.
Proof.
  intros n k Hk.
  unfold bk_Pn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（G4 复核位）                          *)
(* ============================================================ *)

Print Assumptions bk_Qn_sym.
Print Assumptions bk_psd_binom.
Print Assumptions bk_Qn_ge_3pow_nat.
Print Assumptions bk_Qn_int.
Print Assumptions bk_Qn_ge_3pow.
Print Assumptions bk_Qn_eval_sem.
Print Assumptions bk_Qn_list_nth.
Print Assumptions bk_Pn_eval.
Print Assumptions bk_Pn_list_nth.
