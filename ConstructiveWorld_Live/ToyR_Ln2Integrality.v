(* ============================================================ *)
(* ToyR_Ln2Integrality.v —— 消融落件：原件全文逐字保留，仅将文末清单所列 *)
(*   两定理之证明体替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证 *)
(*   直取／结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增 Require， *)
(*   证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留原件 Print Assumptions； *)
(*   清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体注一字未改，历史证据保全）。 *)
(*   清单：pi_den_divide（原 L462，3 句）、pi_Pn_eval_eq（原 L252，3 句）。 *)
(* Ln2Integrality.v —— 使命：Beukers/Hermite Padé [n/n] 的整性收束：p̃_n 整化 *)
(*   （2^n·D_n·P_n(1/2) ∈ Z 的见证构造）与 x'_n 分母显式化。 *)
(* 八件交付面（pi_ 前缀）：pi_bkC_hl：bkC ↔ hl_binom 双二项式桥； *)
(*   pi_div_Qeq：j ∣ D ⟹ Q#D·(1/Q#j) == Q#(D/j)（整除换商）； *)
(*   pi_hsum_spec：D_n·H_k == Q#(Σ_{j≤k} D_n/j)（H_k 整化主桥）； *)
(*   pi_psQ_ext：bk_psQ 逐点外延；pi_Pn_int：p̃_n := bk_psd (C²·S_k) (S n)， *)
(*   2^n·D_n·P_n(1/2) == Q#p̃_n（sigT+QeqT Set 面）； *)
(*   pi_Qn_le_8pow：q̃_n ≤ (n+1)·8^n（QleT' Set 面）； *)
(*   pi_x_n_frac：x'_n == p̃_n /(2·D_n·q̃_n)（分母以 Pos.of_succ_nat (Nat.pred M) *)
(*   显式构造）；pi_den_divide：正分母存在的 sigT 弱面。 *)
(* 防错注记：① 系数若取 C²·H_k，则与另一缘差 D_n 倍（S_k = D_n·H_k），等式仅 *)
(*   D_n = 1 时成立；故系数取 C²·D_n，主件链自洽。② Pos.of_nat M 数值为 M+1 *)
(*   （无零偏移），x'_n == p̃_n/(M+1) 为假命题；分母以 Pos.of_succ_nat (Nat.pred M) *)
(*   表数值 M（与 Z.of_nat (S k) = Z.pos (Pos.of_succ_nat k) 为定义性等换）。 *)
(* 依赖事实（不在本件重建）：q̃_n ∈ Z（bk_Qn_int）与 q̃_n ≥ 3^n（bk_Qn_ge_3pow） *)
(*   见 BeukersLists.v；D_n 整除面（hl_lcm_divide_all）与 C(n,k) ≤ 2^n *)
(*   （hl_binom_le_pow2）见 HansonLcm.v。 *)
(* 构造性注记：全件 Qed/Defined、零承认；主件语句面 sigT/QeqT/QleT'，零 Prop *)
(*   前提进语句面；nat/Z/Q 层支撑引理为 Prop 面、仅服务推理；pi_hsum/pi_ptilde *)
(*   皆可执行；文末 Print Assumptions 复核。 *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp + BeukersLists + HansonLcm。 *)
(* 编译配方：coqc 9.1 直调（无 -Q），cpu_guard 包裹，-o 输出临时目录，树内 .vo 不重写。 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Lists.List.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 幂与正性引理（nat 层）                                            *)
(* ============================================================ *)

Lemma pi_pow3_ge1 : forall n : nat, 1 <= 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pi_pow4b : forall n : nat, 4 ^ n = 2 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

Lemma pi_pow8 : forall n : nat, 8 ^ n = 4 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

(* bk_psd 常系数闭式：Σ_{k<N} c·2^{N−1−k} = c·(2^N−1) *)
Lemma pi_psd_const : forall (N c : nat),
  bk_psd (fun _ : nat => c) N = c * (2 ^ N - 1).
Proof.
  induction N as [| N IH]; intro c.
  - cbn [bk_psd Nat.pow]. lia.
  - cbn [bk_psd]. rewrite IH. rewrite Nat.pow_succ_r'.
    pose proof (hl_pow2_ge1 N). nia.
Qed.

(* ============================================================ *)
(* §B bkC ↔ hl_binom 双 Pascal 桥：pi_bkC_hl                             *)
(* ============================================================ *)

Lemma pi_bkC_hl : forall n k : nat, bkC n k = hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + reflexivity.
    + reflexivity.
  - destruct k as [| k'].
    + reflexivity.
    + cbn [bkC]. rewrite (IH k'). rewrite (IH (Datatypes.S k')).
      symmetry. apply hl_binom_S.
Qed.

(* ============================================================ *)
(* §C Q 层乘除微引理（Q 域域律，全部非零前提显式）                        *)
(* ============================================================ *)

(* 正分母分数乘整数：分母合并不展开 Qinv 分量 *)
Lemma pi_Qden_cancel : forall (u : Z) (p : positive),
  ((u # p) * ((Z.pos p) # 1))%Q == (u # 1)%Q.
Proof.
  intros u p. unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Pos.mul_1_r. ring.
Qed.

Lemma pi_Qneq0_Zpos : forall p : positive, ~ (((Z.pos p) # 1) == 0)%Q.
Proof.
  intros p Hc. unfold Qeq in Hc. vm_compute in Hc. discriminate Hc.
Qed.

Lemma pi_Qneq0_nat : forall m : nat, 1 <= m -> ~ ((Z.of_nat m # 1) == 0)%Q.
Proof.
  intros m Hm Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc. lia.
Qed.

(* pi_Qmul_cancel_r_to：Q 域右消去（由 stdlib Qmult_inv_r） *)
Lemma pi_Qmul_cancel_r_to : forall a b c : Q,
  ~ (c == 0)%Q -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc H.
  assert (Hc1 : (c * (/ c))%Q == 1%Q) by (apply Qmult_inv_r; exact Hc).
  transitivity (((a * c) * (/ c)))%Q.
  - rewrite <- Qmult_assoc, Hc1. symmetry. apply Qmult_1_r.
  - rewrite H. rewrite <- Qmult_assoc, Hc1. apply Qmult_1_r.
Qed.

(* 除法等式单侧引入：y≠0 ⟹ x == b·y ⟹ x/y == b *)
Lemma pi_Qdiv_eq_intro : forall x y b : Q,
  ~ (y == 0)%Q -> x == b * y -> x / y == b.
Proof.
  intros x y b Hy Hxy. unfold Qdiv. rewrite Hxy.
  assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
  rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* pi_Qmul_inv_r_eq：除法交叉等价（Q 域域律） *)
Lemma pi_Qmul_inv_r_eq : forall x y z : Q,
  ~ (y == 0)%Q -> ((x * (/ y)) == z <-> x == z * y).
Proof.
  intros x y z Hy. split; intro H.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    transitivity (((x * (/ y)) * y))%Q.
    + rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ y) y). rewrite Hy1.
      symmetry. apply Qmult_1_r.
    + rewrite H. reflexivity.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    rewrite H. rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* §D 整除换商与 H_k 整化主桥：pi_div_Qeq、pi_hsum_spec                   *)
(* ============================================================ *)

(* pi_div_Qeq：j ∣ D ⟹ Q#D·(1/Q#j) == Q#(D/j)（由 Nat.div_mul） *)
Lemma pi_div_Qeq : forall (D j : nat), 1 <= j -> Nat.divide j D ->
  ((Z.of_nat D # 1) * ((1 # 1) / (Z.of_nat j # 1)))%Q
  == (Z.of_nat (D / j) # 1)%Q.
Proof.
  intros D j Hj Hd. destruct Hd as [c Hc].
  assert (Hj0 : ~ ((Z.of_nat j # 1) == 0)%Q) by (apply pi_Qneq0_nat; exact Hj).
  assert (Hdq : D / j = c).
  { rewrite Hc. apply Nat.div_mul. lia. }
  rewrite Hdq. unfold Qdiv.
  transitivity ((((Z.of_nat D # 1) * (1 # 1)) * (/ (Z.of_nat j # 1))))%Q.
  - ring.
  - apply (proj2 (pi_Qmul_inv_r_eq _ _ _ Hj0)).
    rewrite Qmult_1_r.
    rewrite bk_Qmul_nat.
    rewrite Hc. reflexivity.
Qed.

(* 整化和承载：pi_hsum D k = Σ_{j=1}^{k} D/j（D 固定，变指标求商和） *)
Fixpoint pi_hsum (D k : nat) : nat :=
  match k with
  | 0 => 0
  | Datatypes.S m => pi_hsum D m + D / Datatypes.S m
  end.

(* pi_hsum_spec：D_n·H_k == Q#(Σ_{j≤k} D_n/j)；对 k 归纳，逐项由 hl_lcm_divide_all 与 pi_div_Qeq。 *)
Lemma pi_hsum_spec : forall (n k : nat), k <= n ->
  ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k. induction k as [| k IH]; intro Hk.
  - cbn [bk_H pi_hsum]. ring.
  - assert (Hle : k <= n) by lia.
    specialize (IH Hle).
    cbn [bk_H pi_hsum].
    rewrite Qmult_plus_distr_r.
    rewrite IH.
    assert (H1 : 1 <= Datatypes.S k) by lia.
    assert (Hd := hl_lcm_divide_all n (Datatypes.S k) H1 Hk).
    assert (Hdv := pi_div_Qeq (hl_lcm_upto n) (Datatypes.S k) H1 Hd).
    rewrite Hdv.
    apply bk_Qadd_nat.
Qed.

(* ============================================================ *)
(* §E bk_psQ 逐点外延与常数提出：pi_psQ_ext、pi_psQ_mul                   *)
(* ============================================================ *)

Lemma pi_psQ_ext : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, k < N -> f k == g k) -> bk_psQ f N z == bk_psQ g N z.
Proof.
  induction N as [| N IH]; intros f g z H.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g z) by (intros k Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma pi_psQ_mul : forall (N : nat) (c : Q) (f : nat -> Q) (z : Q),
  bk_psQ (fun k => (c * f k)%Q) N z == (c * bk_psQ f N z)%Q.
Proof.
  induction N as [| N IH]; intros c f z.
  - cbn [bk_psQ]. ring.
  - cbn [bk_psQ]. rewrite IH. ring.
Qed.

(* ============================================================ *)
(* §F p̃_n 整化主件：pi_Pn_int（系数取 C²·D_n，见头部防错注记①）          *)
(* ============================================================ *)

(* 系数整化（逐点）：(Z#(C²·D_n))·H_k == Z#(C²·S_k)，S_k := pi_hsum D_n k *)
Lemma pi_coeff_Zeq : forall (n k : nat), k <= n ->
  ((Z.of_nat (bkC n k * bkC n k * hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k Hk.
  rewrite <- (bk_Qmul_nat (bkC n k * bkC n k) (hl_lcm_upto n)).
  transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                  * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
  - ring.
  - rewrite (pi_hsum_spec n k Hk). apply bk_Qmul_nat.
Qed.

(* pi_ptilde：p̃_n := Σ_{k≤n} C(n,k)²·S_k，S_k := pi_hsum D_n k *)
Definition pi_ptilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k)
         (Datatypes.S n).

(* pi_Pn_eval_eq：bk_Pn_eval 的 Qeq 形（经 S02 qeqT_imp_qeq 转换，供 == 目标改写） *)
Lemma pi_Pn_eval_eq : forall (n : nat) (z : Q),
  bkQ (bk_Pn_list n) z
  == bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
          (Datatypes.S n) z.
Proof.
  intros n z.
  apply qeqT_imp_qeq.
  apply bk_Pn_eval.
Qed.

(* 半整数点闭式：D_n·2^n·P_n(1/2) == Q#p̃_n（p̃_n ∈ nat 承载） *)
Lemma pi_Pn_half : forall n : nat,
  ((Z.of_nat (hl_lcm_upto n) # 1)
     * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q
  == (Z.of_nat (pi_ptilde n) # 1)%Q.
Proof.
  intro n. unfold pi_ptilde.
  rewrite (pi_Pn_eval_eq n (1 # 2)%Q).
  assert (Hmul := pi_psQ_mul (Datatypes.S n)
                    (Z.of_nat (hl_lcm_upto n) # 1)%Q
                    (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
                    (1 # 2)%Q).
  transitivity ((q_pow (2 # 1)%Q n
    * ((Z.of_nat (hl_lcm_upto n) # 1)
         * bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) (1 # 2)%Q))%Q).
  - ring.
  - rewrite <- Hmul.
    assert (Hpt : forall k : nat, k < Datatypes.S n ->
        (((Z.of_nat (hl_lcm_upto n) # 1)
            * ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k))%Q)
        == ((Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1))%Q).
    { intro k. intro Hk. assert (Hle : k <= n) by lia.
      transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                      * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
      - ring.
      - rewrite (pi_hsum_spec n k Hle). apply bk_Qmul_nat. }
    rewrite (pi_psQ_ext (Datatypes.S n) _ _ _ Hpt).
    apply bk_half_psd.
Qed.

(* pi_Pn_int：p̃_n ∈ Z 的 sigT 整性见证（Set 面） *)

Theorem pi_Pn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT (q_pow (2 # 1)%Q n
            * ((Z.of_nat (hl_lcm_upto n) # 1) * bkQ (bk_Pn_list n) (1 # 2)%Q)%Q)
         ((z # 1)%Q)).
Proof.
  intro n. exists (Z.of_nat (pi_ptilde n)). apply qeq_imp_qeqT.
  transitivity ((Z.of_nat (hl_lcm_upto n) # 1)
                  * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q.
  - ring.
  - apply pi_Pn_half.
Qed.

(* ============================================================ *)
(* §G q̃_n ≤ (n+1)·8^n：pi_Qn_le_8pow（QleT' Set 面）                     *)
(* ============================================================ *)

Theorem pi_Qn_le_8pow : forall n : nat,
  QleT' ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
        ((Z.of_nat (Datatypes.S n * 8 ^ n) # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. apply bk_Qle_nat.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n ->
      bkC n k * bkC n k <= 4 ^ n).
  { intro k. intro Hk.
    assert (Hb := hl_binom_le_pow2 n k).
    rewrite <- (pi_bkC_hl n k) in Hb.
    rewrite (pi_pow4b n).
    nia. }
  assert (Hmono := bk_psd_mono (Datatypes.S n)
                     (fun k : nat => bkC n k * bkC n k)
                     (fun _ : nat => 4 ^ n) Hpt).
  rewrite pi_psd_const in Hmono.
  rewrite Nat.pow_succ_r' in Hmono.
  destruct n as [| n'].
  - cbn [bk_psd bkC Nat.pow] in *. lia.
  - assert (Hs1 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)
                  <= 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n'))
      by (apply Nat.mul_le_mono_l; lia).
    assert (Hs2 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')
                  = 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')) by ring.
    assert (Hs3 : 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')
                  <= Datatypes.S (Datatypes.S n') * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')).
    { apply Nat.mul_le_mono_r. lia. }
    rewrite (pi_pow8 (Datatypes.S n')).
    apply Nat.le_trans with
      (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)).
    + exact Hmono.
    + apply Nat.le_trans with
        (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')).
      * exact Hs1.
      * rewrite Hs2. exact Hs3.
Qed.

(* ============================================================ *)
(* §H x'_n 的显式分母：pi_x_n_frac 与 sigT 弱面 pi_den_divide             *)
(* ============================================================ *)

Lemma pi_lcm_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb. unfold Nat.lcm.
  destruct (Nat.gcd a b) as [| g] eqn:Eg.
  - exfalso.
    destruct (Nat.gcd_divide_r a b) as [q Hq].
    rewrite Eg, Nat.mul_0_r in Hq. lia.
  - assert (Hbg : 0 < b / Datatypes.S g).
    { apply Nat.div_str_pos.
      destruct (Nat.gcd_divide_r a b) as [q Hq]. rewrite Eg in Hq.
      destruct q as [| q'].
      - lia.
      - split.
        + lia.
        + assert (Hg1 : Datatypes.S g * 1 <= Datatypes.S g * Datatypes.S q')
            by (apply Nat.mul_le_mono_l; lia).
          rewrite Nat.mul_1_r in Hg1.
          rewrite Hq, Nat.mul_comm. exact Hg1. }
    nia.
Qed.

Lemma pi_lcm_upto_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. apply pi_lcm_pos.
    + exact IH.
    + lia.
Qed.

Lemma pi_qtilde_pos : forall n : nat, 1 <= bk_Qn_qtilde n.
Proof.
  intro n. pose proof (bk_Qn_ge_3pow_nat n). pose proof (pi_pow3_ge1 n). lia.
Qed.

(* pi_Qn_nz：2·Q_n(1/2) 非零（由 bk_Qn_half_closed 与 q̃_n ≥ 3^n > 0） *)
Lemma pi_Qn_nz : forall n : nat,
  ~ (((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q) == 0)%Q.
Proof.
  intro n. intro H0.
  assert (HQ : bkQ (bk_Qn_list n) (1 # 2)%Q == 0%Q).
  { apply (pi_Qmul_cancel_r_to (bkQ (bk_Qn_list n) (1 # 2)%Q) 0%Q (2 # 1)%Q).
    - apply pi_Qneq0_Zpos.
    - rewrite (Qmult_comm (bkQ (bk_Qn_list n) (1 # 2)%Q) (2 # 1)%Q).
      rewrite Qmult_0_l. exact H0. }
  assert (Hh := bk_Qn_half_closed n).
  rewrite HQ in Hh. rewrite Qmult_0_r in Hh.
  pose proof (bk_Qn_ge_3pow_nat n).
  unfold Qeq in Hh. cbn [Qnum Qden] in Hh.
  rewrite !Z.mul_1_r in Hh.
  replace 0%Z with (Z.of_nat 0) in Hh by reflexivity.
  apply Znat.Nat2Z.inj in Hh.
  pose proof (pi_pow3_ge1 n).
  lia.
Qed.

(* 交叉恒等式：P_n(1/2)·(2·D_n·q̃_n) == p̃_n·(2·Q_n(1/2))（Q 域纯环） *)
Lemma pi_x_cross : forall n : nat,
  (bkQ (bk_Pn_list n) (1 # 2)%Q
     * (Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n) # 1))%Q
  == ((Z.of_nat (pi_ptilde n) # 1)
        * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
Proof.
  intro n.
  replace (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q) by reflexivity.
  rewrite <- (bk_Qmul_nat (2 * hl_lcm_upto n) (bk_Qn_qtilde n)).
  rewrite <- (bk_Qmul_nat 2 (hl_lcm_upto n)).
  rewrite <- bk_Qn_half_closed.
  rewrite <- (pi_Pn_half n).
  ring.
Qed.

(* pi_x_n_frac：x'_n == p̃_n /(2·D_n·q̃_n)，分母显式构造。
   防错注记：Z.pos (Pos.of_nat M) 数值为 M+1（无零偏移），用它陈述为假命题；
   Pos.of_succ_nat (Nat.pred M) 数值恰为 M（定义性换算）。 *)
Theorem pi_x_n_frac : forall n : nat,
  QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
          / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
       ((Z.of_nat (pi_ptilde n)
           # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hm1 : 1 <= 2 * hl_lcm_upto n * bk_Qn_qtilde n)
    by (pose proof (pi_lcm_upto_pos n); pose proof (pi_qtilde_pos n); lia).
  assert (Hpm : Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
              = Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n)).
  { assert (Hs : Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))
               = 2 * hl_lcm_upto n * bk_Qn_qtilde n) by lia.
    transitivity (Z.of_nat (Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
    - reflexivity.
    - rewrite Hs. reflexivity. }
  apply pi_Qdiv_eq_intro.
  - apply pi_Qn_nz.
  - apply (pi_Qmul_cancel_r_to (bkQ (bk_Pn_list n) (1 # 2)%Q)
             (((Z.of_nat (pi_ptilde n)
                  # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
                 * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q)
             ((Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))) # 1)%Q)).
    + apply pi_Qneq0_Zpos.
    + rewrite Hpm.
      transitivity ((Z.of_nat (pi_ptilde n) # 1)
                      * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
      * exact (pi_x_cross n).
      * rewrite <- (pi_Qden_cancel (Z.of_nat (pi_ptilde n))
                          (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
        rewrite Hpm.
        ring.
Qed.

(* pi_den_divide：存在正分母 p 使 x'_n == p̃_n/p（sigT 弱面） *)
Theorem pi_den_divide : forall n : nat,
  sigT (fun p : positive =>
    QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
            / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
         ((Z.of_nat (pi_ptilde n) # p)%Q)).
Proof.
  intro n.
  exists (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))).
  apply pi_x_n_frac.
Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。         *)
(* ============================================================ *)

Print Assumptions pi_bkC_hl.
Print Assumptions pi_div_Qeq.
Print Assumptions pi_hsum_spec.
Print Assumptions pi_psQ_ext.
Print Assumptions pi_Pn_int.
Print Assumptions pi_Qn_le_8pow.
Print Assumptions pi_x_n_frac.
Print Assumptions pi_den_divide.
