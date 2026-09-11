(* ============================================================ *)
(* UpConstitution.v —— ASI 资源宪法：改进声明的 Set 层类型与可判定验证器 *)
(*                                                              *)
(* 理论来源：成果存档/新算法.txt 推导 3「无见证的无限承诺不合法」    *)
(*   ——自我改进系统的每一次改进声明必须输出 (κ, N, 击穿见证) 三元组；  *)
(*   这不是软约束：本文件给出可机器检查的宪法执行器。               *)
(*                                                              *)
(* 五件交付：                                                    *)
(*   件 1  claim_decl        改进声明的 Set 层 Record 类型          *)
(*   件 2  check_claim       可判定验证器（Defined 可执行，四门六证）  *)
(*   件 3  valid_claim_yields_breakthrough                        *)
(*                          验证器通过 ⟹ 击穿见证存在（健全性）      *)
(*   件 4  invalid_claim_counter_*                               *)
(*                          具体反例精确判定（可反驳性·E 模式）      *)
(*   件 5  claim_chain       两条有效声明的复合仍有效（宪法闭合）     *)
(*                                                              *)
(* 数学核心（nat/Q 层自足，不依赖 Real 层）：                       *)
(*   uc_bernoulli        (1+c)^n ≥ 1 + n·c 的 Q 形 Bernoulli       *)
(*   uc_growth_breaks    Q 层阿基米德击穿（Qarchimedean + 正 nat 预算）*)
(*   q_decay_breaks      Q 层几何衰减击穿 = r_arch_pow_real 的       *)
(*                       Q 层自足对应件（κ∈(0,1) ⟹ 有限预算存在）    *)
(*                                                              *)
(* 层位纪律：宪法面语句全 Set 层（QleT'/QltT/NatLe/Id/sigT/And/Or）；*)
(*   内部代数微件沿 LCAudit 先例口径（Qle/== 前提位）；  *)
(*   纯构造性：禁词零出现（见交付报告 G1）；全部 Qed 闭合。           *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpBudgetReal.
Require Import UpBudgetReal.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 件 1：改进声明的 Set 层类型                                 *)
(* ============================================================ *)
(* 形态裁决：任务书草案把 QleT/QltT 证挤进 sigT 类型，使 κ≥1 的声明   *)
(* 不可构造——与件 4「构造具体反例声明」直接冲突（反例必须可构造才能   *)
(* 被验证器拒收）。故裁决为：无约束 Record + 验证器判定。            *)
(* 语义：每步按 (1−κ) 收缩基线 c0，声明 N 步内严格跨过阈值 eps。      *)

Record claim_decl : Set := mk_claim {
  cl_c0 : Q;        (* 当前基线值 c0 *)
  cl_eps : Q;       (* 目标阈值 eps *)
  cl_kappa : Q;     (* 声明改进率 κ *)
  cl_N : nat;       (* 声明到达预算 N *)
  cl_id : nat       (* 声明 id *)
}.

(* ============================================================ *)
(* §1 Q 层代数微件（桥与换形；LCAudit 先例口径）                    *)
(* ============================================================ *)

Lemma uc_qeq_le : forall x y : Q, x == y -> Qle x y.
Proof. intros x y H. rewrite H. apply Qle_refl. Qed.

Lemma uc_qeq_le_l : forall x y z : Q, x == y -> Qle x z -> Qle y z.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_le_r : forall x y z : Q, x == y -> Qle z x -> Qle z y.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_lt_l : forall x y z : Q, x == y -> Qlt x z -> Qlt y z.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_lt_r : forall x y z : Q, x == y -> Qlt z x -> Qlt z y.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

(* 倒数正性（Q 层自足版；三分判定构造性收尾） *)
Lemma uc_inv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (1 / x).
Proof.
intros x Hx.
destruct (Q_dec 0 (1 / x)) as [[H | H] | H].
- exact H.
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - apply (Qlt_le_weak (1 / x) 0). exact H.
    - apply (Qlt_le_weak 0 x). exact Hx. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx. exact (Qlt_irrefl 0%Q Hx). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  apply (Qlt_irrefl 0%Q).
  apply (uc_qeq_lt_r (0 * x) 0%Q 0%Q).
  + ring.
  + exact Hlt0.
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - apply (uc_qeq_le (1 / x) 0%Q (Qeq_sym _ _ H)).
    - apply (Qlt_le_weak 0 x). exact Hx. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx. exact (Qlt_irrefl 0%Q Hx). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  apply (Qlt_irrefl 0%Q).
  apply (uc_qeq_lt_r (0 * x) 0%Q 0%Q).
  + ring.
  + exact Hlt0.
Qed.

(* 序的加 −x 换形 *)
Lemma uc_le_opp_shift : forall x y : Q, Qle x y -> Qle 0 (y + - x).
Proof.
intros x y H. apply (Qle_trans _ (x + - x) _).
- apply uc_qeq_le. ring.
- apply Qplus_le_compat.
  + exact H.
  + apply Qle_refl.
Qed.

Lemma uc_lt_opp_shift : forall x y : Q, Qlt x y -> Qlt 0 (y + - x).
Proof.
intros x y H.
assert (Hmid : Qlt ((- x) + x) ((- x) + y)).
{ apply (proj2 (Qplus_lt_r x y (- x))). exact H. }
apply (uc_qeq_lt_r ((- x) + y) (y + - x) 0%Q).
- ring.
- apply (uc_qeq_lt_l ((- x) + x) 0%Q ((- x) + y)).
  + ring.
  + exact Hmid.
Qed.

Lemma uc_lt_minus_inv : forall x y : Q, Qlt 0 (y + - x) -> Qlt x y.
Proof.
intros x y H.
assert (Hmid : Qlt (x + 0) (x + (y + - x))).
{ apply (proj2 (Qplus_lt_r 0 (y + - x) x)). exact H. }
apply (uc_qeq_lt_r (x + (y + - x)) y x).
- ring.
- apply (uc_qeq_lt_l (x + 0) x (x + (y + - x))).
  + ring.
  + exact Hmid.
Qed.

Lemma uc_opp_le_shift : forall x : Q, Qle 0 x -> Qle (- x) 0.
Proof.
intros x H. apply (Qle_trans _ ((- x) + x) _).
- apply (uc_qeq_le_l ((- x) + 0) (- x) ((- x) + x)).
  + ring.
  + apply Qplus_le_compat.
    * apply Qle_refl.
    * exact H.
- apply (uc_qeq_le_r ((- x) + x) 0%Q ((- x) + x)).
  + ring.
  + apply Qle_refl.
Qed.

(* 乘法右消去（严格版；Q_dec 三分构造性收尾） *)
Lemma uc_cancel_lt_r : forall a b p : Q,
  Qlt 0 p -> QltT (a * p) (b * p) -> QltT a b.
Proof.
intros a b p Hp Hlt. apply QltT_to_Qlt in Hlt.
destruct (Q_dec a b) as [[H1 | H2] | H3].
- apply Qlt_to_QltT. exact H1.
- exfalso. apply (Qlt_irrefl (b * p)).
  apply (Qlt_trans (b * p) (a * p) (b * p)).
  + apply (Qmult_lt_compat_r b a p Hp H2).
  + exact Hlt.
- exfalso. apply (Qlt_irrefl (a * p)).
  rewrite <- H3 in Hlt. exact Hlt.
Qed.

(* ============================================================ *)
(* §2 q_pow 幂代数（消费 q_pow）                      *)
(* ============================================================ *)

Lemma uc_pow_eq_compat : forall (x y : Q) (n : nat), x == y -> q_pow x n == q_pow y n.
Proof.
intros x y n Hxy. induction n as [| n IH]; simpl.
- reflexivity.
- rewrite IH. rewrite Hxy. reflexivity.
Qed.

Lemma uc_pow_add : forall (x : Q) (p q : nat),
  q_pow x (p + q)%nat == q_pow x p * q_pow x q.
Proof.
intros x p q. induction p as [| p IH]; simpl.
- ring.
- rewrite IH. ring.
Qed.

Lemma uc_pow_mul : forall (x y : Q) (n : nat),
  q_pow (x * y) n == q_pow x n * q_pow y n.
Proof.
intros x y n. induction n as [| n IH]; simpl.
- reflexivity.
- rewrite IH. ring.
Qed.

Lemma uc_pow_inv_pair : forall (a b : Q) (n : nat),
  a * b == 1 -> q_pow a n * q_pow b n == 1.
Proof.
intros a b n Hab. induction n as [| n IH]; simpl.
- reflexivity.
- assert (Hre : (a * q_pow a n) * (b * q_pow b n)
              == (a * b) * (q_pow a n * q_pow b n)) by ring.
  rewrite Hre. rewrite Hab. rewrite IH. reflexivity.
Qed.

(* 衰减指数下降：0 ≤ x ≤ 1 ⟹ x^(p+q) ≤ x^p（sc_qpow_dec 迭代） *)
Lemma uc_pow_le_drop : forall (x : Q) (p q : nat),
  Qle 0 x -> Qle x 1 -> Qle (q_pow x (p + q)%nat) (q_pow x p).
Proof.
intros x p q Hx0 Hx1. induction q as [| q IH].
- replace (p + 0)%nat with p by lia. apply Qle_refl.
- replace (p + Datatypes.S q)%nat with (Datatypes.S (p + q)) by lia.
  apply (Qle_trans _ (q_pow x (p + q)%nat) _).
  + apply (sc_qpow_dec x (p + q)%nat Hx0 Hx1).
  + exact IH.
Qed.

(* ============================================================ *)
(* §3 Q 形 Bernoulli：(1+c)^n ≥ 1 + n·c（c ≥ 0）                  *)
(* ============================================================ *)

Lemma uc_znat_pos : forall n : nat, Qle 0 (Z.of_nat n # 1).
Proof. intro n. unfold Qle. simpl. lia. Qed.

Lemma uc_bernoulli : forall (c : Q) (n : nat),
  QleT' 0 c -> QleT' (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n).
Proof.
intros c n HcT. pose proof (QleT'_to_Qle 0 c HcT) as Hc.
induction n as [| n IH].
- apply Qle_to_QleT'.
  replace (q_pow (1 + c) 0) with 1%Q by reflexivity.
  apply uc_qeq_le.
  replace (Z.of_nat 0 # 1) with (0 # 1)%Q by reflexivity.
  ring.
- apply Qle_to_QleT'.
  assert (Hs : (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + 1).
  { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c) _).
  + apply uc_qeq_le. rewrite Hs. ring.
  + apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) * (1 + c)) _).
    * (* (1 + n·c) + c ≤ (1+n·c)·(1+c)：差项 n·c·c ≥ 0 *)
      apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + (Z.of_nat n # 1) * c * c) _).
      -- apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + 0) _).
         ++ apply uc_qeq_le. ring.
         ++ apply Qplus_le_compat.
            ** apply Qle_refl.
            ** (* 0 ≤ (n#1·c)·c *)
               apply (Qle_trans _ (0 * c)%Q _).
               { apply uc_qeq_le. ring. }
               { pose proof (uc_znat_pos n) as Hzn.
                 assert (Hzc : Qle 0 ((Z.of_nat n # 1) * c)).
                 { apply (Qle_trans _ (0 * c)%Q _).
                   - apply uc_qeq_le. ring.
                   - apply (Qmult_le_compat_r 0 (Z.of_nat n # 1) c Hzn Hc). }
                 apply (Qle_trans _ (0 * c)%Q _).
                 - apply uc_qeq_le. ring.
                 - apply (Qmult_le_compat_r 0 ((Z.of_nat n # 1) * c) c Hzc Hc). }
      -- apply uc_qeq_le. ring.
    * (* (1+c) 单调放大（0 ≤ 1+c） *)
      rewrite (q_pow_succ (1 + c) n).
      rewrite (Qmult_comm (1 + c) (q_pow (1 + c) n)).
      apply (Qmult_le_compat_r (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n) (1 + c)
               (QleT'_to_Qle _ _ IH)).
      apply (Qle_trans _ 1%Q _).
      -- unfold Qle. simpl. lia.
      -- apply (uc_qeq_le_l (1 + 0) 1 (1 + c)).
         ++ ring.
         ++ apply Qplus_le_compat.
            ** apply Qle_refl.
            ** exact Hc.
Qed.

(* ============================================================ *)
(* §4 Q 层阿基米德击穿：真增长率必有正预算（Qarchimedean + Bernoulli）*)
(* ============================================================ *)

Lemma uc_growth_breaks : forall (c T : Q),
  Qlt 0 c -> Qlt 0 T ->
  sigT (fun N => And (NatLe 1 N) (QltT T (q_pow (1 + c) N))).
Proof.
intros c T Hc HT.
destruct (Qarchimedean (T / c)) as [p Hp].
exists (Datatypes.S (Pos.to_nat p)).
split.
- apply NatLe_lift. lia.
- apply Qlt_to_QltT.
  assert (Hconv : Z.of_nat (Pos.to_nat p) = Z.pos p) by (apply positive_nat_Z).
  assert (Hconv2 : Z.of_nat (Datatypes.S (Pos.to_nat p)) = (Z.pos p + 1)%Z) by lia.
  assert (Hid : (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) == (Z.pos p # 1) + 1).
  { rewrite Hconv2. unfold Qeq. simpl. lia. }
  assert (Hcancel : (T / c) * c == T).
  { field. intro Hz. rewrite Hz in Hc. exact (Qlt_irrefl 0%Q Hc). }
  assert (H0 : (T / c) * c < (Z.pos p # 1) * c).
  { apply (Qmult_lt_compat_r (T / c) (Z.pos p # 1) c Hc Hp). }
  rewrite Hcancel in H0.
  assert (H1 : (Z.pos p # 1) * c < (Z.pos p # 1) * c + c).
  { apply (uc_qeq_lt_l ((Z.pos p # 1) * c + 0) ((Z.pos p # 1) * c) ((Z.pos p # 1) * c + c)).
    - ring.
    - apply (proj2 (Qplus_lt_r 0%Q c ((Z.pos p # 1) * c))). exact Hc. }
  assert (H2 : (Z.pos p # 1) * c + c
             == (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { rewrite Hid. ring. }
  assert (H3 : T < (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.pos p # 1) * c) _).
    - exact H0.
    - apply (uc_qeq_lt_r _ _ _ H2). exact H1. }
  assert (H4 : T < 1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c) _).
    - exact H3.
    - apply (uc_qeq_lt_r ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)
                         (1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)).
      + ring.
      + apply (uc_qeq_lt_l ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 0)
                           ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)
                           ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)).
        * ring.
        * apply (proj2 (Qplus_lt_r 0%Q 1%Q
                          ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c))).
          unfold Qlt. simpl. lia. }
  pose proof (QleT'_to_Qle _ _
    (uc_bernoulli c (Datatypes.S (Pos.to_nat p))
       (Qle_to_QleT' 0 c (Qlt_le_weak 0 c Hc)))) as Hb.
  apply (Qlt_le_trans _ _ _ H4 Hb).
Qed.

(* ============================================================ *)
(* §5 Q 层几何衰减击穿（r_arch_pow_real 的 Q 层自足对应件）          *)
(*   κ∈(0,1)、c0>0、eps>0 ⟹ 存在正预算 N 使 c0·(1−κ)^N < eps        *)
(*   预算 N 的显式形态：Qarchimedean 在 c0/eps 除以 κ/(1−κ) 上解出。  *)
(* ============================================================ *)

Theorem q_decay_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N) (QltT (c0 * q_pow (1 - k) N) eps)).
Proof.
intros k c0 eps HkT0 HkT1 Hc0T HeT.
pose proof (QltT_to_Qlt 0 k HkT0) as Hk0.
pose proof (QltT_to_Qlt k 1 HkT1) as Hk1.
pose proof (QltT_to_Qlt 0 c0 Hc0T) as Hc0.
pose proof (QltT_to_Qlt 0 eps HeT) as He.
assert (H1k : Qlt 0 (1 - k)) by (apply (uc_lt_opp_shift k 1 Hk1)).
assert (Hinv : Qlt 0 (1 / (1 - k))) by (apply (uc_inv_pos (1 - k) H1k)).
assert (Hg : 1 / (1 - k) == 1 + k / (1 - k)).
{ field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
assert (HkcLt : Qlt 0 (k / (1 - k))).
{ apply (uc_qeq_lt_r (k * (1 / (1 - k))) (k / (1 - k)) 0%Q).
  - unfold Qdiv. ring.
  - apply (Qmult_lt_0_compat k (1 / (1 - k)) Hk0 Hinv). }
assert (Ht : Qlt 0 (c0 / eps)).
{ apply (uc_qeq_lt_r (c0 * (1 / eps)) (c0 / eps) 0%Q).
  - unfold Qdiv. ring.
  - apply (Qmult_lt_0_compat c0 (1 / eps) Hc0 (uc_inv_pos eps He)). }
destruct (uc_growth_breaks (k / (1 - k)) (c0 / eps) HkcLt Ht) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- pose proof (QltT_to_Qlt (c0 / eps) (q_pow (1 + k / (1 - k)) N) HN) as HN'.
  assert (Hpow : q_pow (1 / (1 - k)) N == q_pow (1 + k / (1 - k)) N)
    by (apply uc_pow_eq_compat; exact Hg).
  assert (Hcancel2 : (c0 / eps) * eps == c0).
  { field. intro Hz. rewrite Hz in He. exact (Qlt_irrefl 0%Q He). }
  assert (Hstep : (c0 / eps) * eps < eps * q_pow (1 + k / (1 - k)) N).
  { rewrite (Qmult_comm eps (q_pow (1 + k / (1 - k)) N)).
    apply (Qmult_lt_compat_r (c0 / eps) (q_pow (1 + k / (1 - k)) N) eps He HN'). }
  rewrite Hcancel2 in Hstep.
  assert (Hmul : c0 < eps * q_pow (1 / (1 - k)) N).
  { apply (uc_qeq_lt_r (eps * q_pow (1 + k / (1 - k)) N)
                       (eps * q_pow (1 / (1 - k)) N) c0).
    - rewrite Hpow. reflexivity.
    - exact Hstep. }
  assert (Hpair : q_pow (1 - k) N * q_pow (1 / (1 - k)) N == 1).
  { apply uc_pow_inv_pair.
    field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
  assert (HposGN : Qlt 0 (q_pow (1 / (1 - k)) N))
    by (apply (sc_qpow_pos N (1 / (1 - k)) Hinv)).
  apply (uc_cancel_lt_r (c0 * q_pow (1 - k) N) eps (q_pow (1 / (1 - k)) N) HposGN).
  apply Qlt_to_QltT.
  apply (uc_qeq_lt_l c0
           ((c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N)
           (eps * q_pow (1 / (1 - k)) N)).
  { assert (Hre : (c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N
                == c0 * (q_pow (1 - k) N * q_pow (1 / (1 - k)) N)) by ring.
    rewrite Hre. rewrite Hpair. rewrite Qmult_1_r. reflexivity. }
  { exact Hmul. }
Qed.

(* ============================================================ *)
(* §6 件 2：可判定验证器（Defined 可执行）                          *)
(*   六个单门判定器：bool 判定 + 依赖 match 同步发放 Set 层证书；      *)
(*   拒绝时发拒绝码（可反驳性：负向判定同样精确）。                   *)
(* ============================================================ *)

(* 拒绝码（E 模式：反例与陈述同权，负向判定携带可机器检查的理由） *)
Inductive claim_reject : Set :=
| rj_kappa   (* kappa 不在 [0,1)：零衰减捷径或负率 *)
| rj_budget  (* N = 0：即时报达声明 *)
| rj_data    (* c0 < 0 或 eps <= 0：基线/阈值不合法 *)
| rj_reach.  (* 预算 N 内不跨阈值：无见证承诺 *)

(* 通过证书：六证包（每门一张 Id 型 Set 层证） *)
Definition claim_pass (cl : claim_decl) : Set :=
  And (And (QleT' 0 (cl_kappa cl)) (QltT (cl_kappa cl) 1))
      (And (NatLe 1 (cl_N cl))
           (And (And (QleT' 0 (cl_c0 cl)) (QltT 0 (cl_eps cl)))
                (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                      (cl_eps cl)))).

(* 门 1a：0 <= kappa *)
Definition kap_low_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_kappa cl))
       (And (Id (Qle_bool 0 (cl_kappa cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_kappa cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* 门 1b：kappa < 1 *)
Definition kap_high_dec (cl : claim_decl)
  : Or (QltT (cl_kappa cl) 1)
       (And (Id (Qlt_bool (cl_kappa cl) 1) false) claim_reject) :=
  match Qlt_bool (cl_kappa cl) 1 as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* 门 2：N >= 1 *)
Definition bud_dec (cl : claim_decl)
  : Or (NatLe 1 (cl_N cl))
       (And (Id (Nat.leb 1 (cl_N cl)) false) claim_reject) :=
  match Nat.leb 1 (cl_N cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_budget)
  end.

(* 门 3a：0 <= c0 *)
Definition dat_c0_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_c0 cl))
       (And (Id (Qle_bool 0 (cl_c0 cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_c0 cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* 门 3b：0 < eps *)
Definition dat_eps_dec (cl : claim_decl)
  : Or (QltT 0 (cl_eps cl))
       (And (Id (Qlt_bool 0 (cl_eps cl)) false) claim_reject) :=
  match Qlt_bool 0 (cl_eps cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* 门 4：到达性——N 步内严格跨阈值 *)
Definition reach_dec (cl : claim_decl)
  : Or (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl))
       (And (Id (Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                          (cl_eps cl))
                 false)
            claim_reject) :=
  match Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl)
          as b return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_reach)
  end.

(* 宪法执行器本体：顺序过六门，全过发证书，首个不过发拒绝码 *)
Definition check_claim (cl : claim_decl) : Or (claim_pass cl) claim_reject :=
  match kap_low_dec cl with
  | inr (_, r) => inr r
  | inl hk0 =>
    match kap_high_dec cl with
    | inr (_, r) => inr r
    | inl hk1 =>
      match bud_dec cl with
      | inr (_, r) => inr r
      | inl hb =>
        match dat_c0_dec cl with
        | inr (_, r) => inr r
        | inl hc0 =>
          match dat_eps_dec cl with
          | inr (_, r) => inr r
          | inl he =>
            match reach_dec cl with
            | inr (_, r) => inr r
            | inl hr => inl (((hk0, hk1), (hb, ((hc0, he), hr))))
            end
          end
        end
      end
    end
  end.

(* 可判定总结报（vm_compute 友好输出形态） *)
Inductive claim_verdict : Set :=
| v_pass : claim_verdict
| v_reject : claim_reject -> claim_verdict.

Definition check_report (cl : claim_decl) : claim_verdict :=
  match check_claim cl with
  | inl _ => v_pass
  | inr r => v_reject r
  end.

(* 判定总全性：任何声明必得裁决 *)
Lemma check_claim_total : forall cl : claim_decl,
  Or (sigT (fun w : claim_pass cl => Id (check_claim cl) (inl w)))
     (sigT (fun r : claim_reject => Id (check_claim cl) (inr r))).
Proof.
intro cl. unfold check_claim.
destruct (kap_low_dec cl) as [hk0|[f0 r0]];
  [ | right; exists r0; reflexivity ];
destruct (kap_high_dec cl) as [hk1|[f1 r1]];
  [ | right; exists r1; reflexivity ];
destruct (bud_dec cl) as [hb|[f2 r2]];
  [ | right; exists r2; reflexivity ];
destruct (dat_c0_dec cl) as [hc0|[f3 r3]];
  [ | right; exists r3; reflexivity ];
destruct (dat_eps_dec cl) as [he|[f4 r4]];
  [ | right; exists r4; reflexivity ];
destruct (reach_dec cl) as [hr|[f5 r5]];
  [ | right; exists r5; reflexivity ].
left. exists (((hk0, hk1), (hb, ((hc0, he), hr)))). reflexivity.
Qed.

(* 证书 ⟹ 验证器判 inl（负向分支携带 bool=false 证据，可被证书证伪消解；
   inl 见证取判定器实际产出——Set 层 Id 不做证明项无关性比较） *)
Lemma check_claim_inl_of_pass : forall (cl : claim_decl),
  claim_pass cl -> sigT (fun w => Id (check_claim cl) (inl w)).
Proof.
intros cl [[hk0 hk1] [hb [[hc0 he] hr]]].
unfold check_claim.
destruct (kap_low_dec cl) as [g0|[f0 r0]].
- destruct (kap_high_dec cl) as [g1|[f1 r1]].
  + destruct (bud_dec cl) as [g2|[f2 r2]].
    * destruct (dat_c0_dec cl) as [g3|[f3 r3]].
      -- destruct (dat_eps_dec cl) as [g4|[f4 r4]].
         ++ destruct (reach_dec cl) as [g5|[f5 r5]].
            ** exists (((g0, g1), (g2, ((g3, g4), g5)))). reflexivity.
            ** exfalso. pose proof (id_trans (id_sym hr) f5) as Hc5. inversion Hc5.
         ++ exfalso. pose proof (id_trans (id_sym he) f4) as Hc4. inversion Hc4.
      -- exfalso. pose proof (id_trans (id_sym hc0) f3) as Hc3. inversion Hc3.
    * exfalso. pose proof (id_trans (id_sym hb) f2) as Hc2. inversion Hc2.
  + exfalso. pose proof (id_trans (id_sym hk1) f1) as Hc1. inversion Hc1.
- exfalso. pose proof (id_trans (id_sym hk0) f0) as Hc0x. inversion Hc0x.
Qed.

(* ============================================================ *)
(* §7 件 3：健全性——验证器通过 ⟹ 击穿见证存在                       *)
(* ============================================================ *)

Theorem valid_claim_yields_breakthrough : forall (cl : claim_decl) (w : claim_pass cl),
  Id (check_claim cl) (inl w) ->
  sigT (fun N' => And (NatLe N' (cl_N cl))
                      (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) N') (cl_eps cl))).
Proof.
intros cl w Hw. exists (cl_N cl). split.
- apply NatLe_lift. lia.
- destruct w as [[hk0 hk1] [hb [[hc0 he] hr]]]. exact hr.
Qed.

(* 严格证的降格：QltT x y ⟹ QleT' x y（Qle_bool 三分换形） *)
Lemma uc_qle_bool_false_inv : forall x y : Q, Qle_bool x y = false -> QltT y x.
Proof.
intros x y Hf.
destruct (Q_dec x y) as [[H1 | H2] | H3].
- exfalso. unfold Qle_bool, Qcompare in Hf.
  pose proof (proj2 (Qlt_alt x y) H1) as E. rewrite E in Hf. discriminate.
- apply Qlt_to_QltT. exact H2.
- exfalso. unfold Qle_bool, Qcompare in Hf.
  unfold Qeq in H3.
  pose proof (proj2 (Z.compare_eq_iff (Qnum x * QDen y) (Qnum y * QDen x)) H3) as E.
  rewrite E in Hf. discriminate.
Qed.

Lemma uc_qleT_of_ltT : forall x y : Q, QltT x y -> QleT' x y.
Proof.
intros x y H.
destruct (Qle_bool x y) eqn:Eb.
- apply RealSetoid.eq_Id. exact Eb.
- exfalso. apply (Qlt_irrefl y).
  pose proof (uc_qle_bool_false_inv x y Eb) as Hbad.
  pose proof (QltT_to_Qlt y x Hbad) as Hyx.
  pose proof (QltT_to_Qlt x y H) as Hxy.
  exact (Qlt_trans y x y Hyx Hxy).
Qed.

(* 宪法非空洞：真增长率必有可通过验证器的预算（q_decay_breaks 放电） *)
Theorem constitution_nonvacuous : forall (c0 eps k : Q) (i : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => sigT (fun w => Id (check_claim (mk_claim c0 eps k N i)) (inl w))).
Proof.
intros c0 eps k i Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N.
assert (Hp : claim_pass (mk_claim c0 eps k N i)).
{ repeat split.
  - exact (uc_qleT_of_ltT 0 k Hk0).
  - exact Hk1.
  - exact HN1.
  - exact (uc_qleT_of_ltT 0 c0 Hc0).
  - exact He.
  - exact HN. }
pose proof (check_claim_inl_of_pass (mk_claim c0 eps k N i) Hp) as Hw.
destruct Hw as [w Hwin]. exists w. exact Hwin.
Qed.

(* ============================================================ *)
(* §8 件 4：可反驳性——具体反例的精确判定（E 模式）                   *)
(* ============================================================ *)

(* 反例 1：kappa = 1 的零衰减捷径声明（(1-kappa)^N ≡ 0 作弊路径，宪法禁收） *)
Definition claim_bad_kappa1 : claim_decl := mk_claim (8 # 10) (1 # 10) 1 5 11.

(* 反例 2：负率声明 *)
Definition claim_bad_kappaneg : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (-1 # 2) 5 12.

(* 反例 3：N = 0 的即时报达声明 *)
Definition claim_bad_budget : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (1 # 2) 0 13.

(* 反例 4：边界恰不跨阈（1·(1/2)^1 = 1/2 不 < 1/2）——无见证承诺 *)
Definition claim_bad_reach : claim_decl := mk_claim 1 (1 # 2) (1 # 2) 1 14.

Theorem invalid_claim_counter_kappa1 :
  Id (check_report claim_bad_kappa1) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_kappaneg :
  Id (check_report claim_bad_kappaneg) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_budget :
  Id (check_report claim_bad_budget) (v_reject rj_budget).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_reach :
  Id (check_report claim_bad_reach) (v_reject rj_reach).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §9 件 5：声明复合——自我改进链的宪法闭合                          *)
(* ============================================================ *)

(* 复合声明：率并集复合 kA+kB-kA*kB，预算相加，接口闸 epsA == c0B *)
Definition chain_claim (A B : claim_decl) : claim_decl :=
  mk_claim (cl_c0 A) (cl_eps B)
           (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)
           (cl_N A + cl_N B)%nat
           (cl_id A).

Lemma uc_minus_opp : forall x y : Q, x - y == x + (- y).
Proof. intros x y. reflexivity. Qed.

Lemma uc_one_minus_comp : forall kA kB : Q,
  1 - (kA + kB - kA * kB) == (1 - kA) * (1 - kB).
Proof. intros kA kB. unfold Qminus. ring. Qed.

Lemma uc_kappa_comp_le : forall kA kB : Q,
  Qle 0 kA -> Qle 0 kB -> Qlt kB 1 -> Qle 0 (kA + kB - kA * kB).
Proof.
intros kA kB HkA0 HkB0 HkB1.
assert (Hid : kA + kB - kA * kB == kA * (1 - kB) + kB).
{ unfold Qminus. ring. }
apply (uc_qeq_le_r (kA * (1 - kB) + kB) (kA + kB - kA * kB) 0%Q
                   (Qeq_sym _ _ Hid)).
apply (Qle_trans _ (0 + 0)%Q _).
- apply uc_qeq_le. ring.
- apply Qplus_le_compat.
  + apply (Qle_trans _ (0 * (1 - kB)) _).
    * apply uc_qeq_le. ring.
    * apply (Qmult_le_compat_r 0 kA (1 - kB) HkA0).
      apply (uc_le_opp_shift kB 1 (Qlt_le_weak kB 1 HkB1)).
  + exact HkB0.
Qed.

Lemma uc_kappa_comp_lt : forall kA kB : Q,
  Qlt kA 1 -> Qlt kB 1 -> Qlt (kA + kB - kA * kB) 1.
Proof.
intros kA kB HkA1 HkB1.
apply uc_lt_minus_inv.
apply (uc_qeq_lt_r ((1 - kA) * (1 - kB)) (1 + - (kA + kB - kA * kB)) 0%Q).
- exact (Qeq_sym _ _ (uc_one_minus_comp kA kB)).
- apply (Qmult_lt_0_compat (1 - kA) (1 - kB)).
  + apply (uc_lt_opp_shift kA 1 HkA1).
  + apply (uc_lt_opp_shift kB 1 HkB1).
Qed.

(* 复合链到达性：c0 过 A 链跨 epsA、epsA 过 B 链跨 epsB
   ⟹ c0 以复合率在 NA+NB 内跨 epsB *)
Lemma uc_chain_reach : forall (c0 e1 e2 kA kB : Q) (NA NB : nat),
  Qle 0 c0 -> Qle 0 kA -> Qlt kA 1 -> Qle 0 kB -> Qlt kB 1 ->
  QltT (c0 * q_pow (1 - kA) NA) e1 ->
  QltT (e1 * q_pow (1 - kB) NB) e2 ->
  QltT (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat) e2.
Proof.
intros c0 e1 e2 kA kB NA NB Hc0 HkA0 HkA1 HkB0 HkB1 HrA HrB.
pose proof (QltT_to_Qlt (c0 * q_pow (1 - kA) NA) e1 HrA) as HrA'.
pose proof (QltT_to_Qlt (e1 * q_pow (1 - kB) NB) e2 HrB) as HrB'.
pose proof (uc_lt_opp_shift kA 1 HkA1) as H1kA.
pose proof (uc_lt_opp_shift kB 1 HkB1) as H1kB.
assert (Hle1kA : Qle 0 (1 - kA)) by (apply (Qlt_le_weak 0 (1 - kA) H1kA)).
assert (Hle1kB : Qle 0 (1 - kB)) by (apply (Qlt_le_weak 0 (1 - kB) H1kB)).
assert (Hb1kA : Qle (1 - kA) 1).
{ apply (uc_qeq_le_l (1 + - kA) (1 - kA) 1).
  - reflexivity.
  - apply (Qle_trans _ (1 + 0)%Q _).
    + apply Qplus_le_compat; [apply Qle_refl | apply (uc_opp_le_shift kA HkA0)].
    + apply uc_qeq_le. ring. }
assert (Hb1kB : Qle (1 - kB) 1).
{ apply (uc_qeq_le_l (1 + - kB) (1 - kB) 1).
  - reflexivity.
  - apply (Qle_trans _ (1 + 0)%Q _).
    + apply Qplus_le_compat; [apply Qle_refl | apply (uc_opp_le_shift kB HkB0)].
    + apply uc_qeq_le. ring. }
assert (Hcomp : q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
              == q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat).
{ assert (HcompEq : 1 - (kA + kB - kA * kB) == (1 - kA) * (1 - kB))
    by (apply uc_one_minus_comp).
  rewrite (uc_pow_eq_compat _ _ _ HcompEq).
  rewrite uc_pow_mul.
  rewrite (uc_pow_add (1 - kA) NA NB).
  rewrite (uc_pow_add (1 - kB) NA NB).
  reflexivity. }
assert (HdropA : Qle (q_pow (1 - kA) (NA + NB)%nat) (q_pow (1 - kA) NA))
  by (apply (uc_pow_le_drop (1 - kA) NA NB Hle1kA Hb1kA)).
assert (HdropB : Qle (q_pow (1 - kB) (NA + NB)%nat) (q_pow (1 - kB) NB)).
{ replace (NA + NB)%nat with (NB + NA)%nat by lia.
  apply (uc_pow_le_drop (1 - kB) NB NA Hle1kB Hb1kB). }
assert (Hboth : Qle (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)
                    (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
{ apply (Qle_trans _ (q_pow (1 - kA) NA * q_pow (1 - kB) (NA + NB)%nat) _).
  - apply (Qmult_le_compat_r (q_pow (1 - kA) (NA + NB)%nat)
                             (q_pow (1 - kA) NA) (q_pow (1 - kB) (NA + NB)%nat)
                             HdropA (q_pow_nonneg (1 - kB) (NA + NB)%nat Hle1kB)).
  - apply (Qle_trans _ (q_pow (1 - kB) (NA + NB)%nat * q_pow (1 - kA) NA) _).
    + apply uc_qeq_le. ring.
    + apply (Qle_trans _ (q_pow (1 - kB) NB * q_pow (1 - kA) NA) _).
      * apply (Qmult_le_compat_r (q_pow (1 - kB) (NA + NB)%nat)
                                 (q_pow (1 - kB) NB) (q_pow (1 - kA) NA)
                                 HdropB (q_pow_nonneg (1 - kA) NA Hle1kA)).
      * apply uc_qeq_le. ring. }
assert (Hmulc : Qle (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
                    (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ rewrite (Qmult_comm c0 (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)).
  rewrite (Qmult_comm c0 (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
  apply (Qmult_le_compat_r _ _ c0 Hboth Hc0). }
assert (HposB2 : Qlt 0 (q_pow (1 - kB) NB))
  by (apply (sc_qpow_pos NB (1 - kB) H1kB)).
assert (Hstep1 : c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB)
               < e1 * q_pow (1 - kB) NB).
{ apply (uc_qeq_lt_l
           ((c0 * q_pow (1 - kA) NA) * q_pow (1 - kB) NB)
           (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))
           (e1 * q_pow (1 - kB) NB)).
  - ring.
  - apply (Qmult_lt_compat_r (c0 * q_pow (1 - kA) NA) e1
             (q_pow (1 - kB) NB) HposB2 HrA'). }
assert (HXle : Qle (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
                   (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ apply (Qle_trans _ (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)) _).
  - assert (Hcomp2 : c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
                   == c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
      by (rewrite Hcomp; reflexivity).
    exact (uc_qeq_le _ _ Hcomp2).
  - exact Hmulc. }
apply Qlt_to_QltT.
apply (Qlt_trans
         (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
         (e1 * q_pow (1 - kB) NB) e2).
- apply (Qle_lt_trans
           (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
           (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))
           (e1 * q_pow (1 - kB) NB)).
  + exact HXle.
  + exact Hstep1.
- exact HrB'.
Qed.

(* 复合定理：两条有效声明接链后，复合声明仍过验证器 *)
Theorem claim_chain : forall (A B : claim_decl) (wA : claim_pass A) (wB : claim_pass B),
  Id (Qeq_bool (cl_eps A) (cl_c0 B)) true ->
  Id (check_claim A) (inl wA) -> Id (check_claim B) (inl wB) ->
  sigT (fun w => Id (check_claim (chain_claim A B)) (inl w)).
Proof.
intros A B wA wB Hface HHA HHB.
destruct wA as [[hk0A hk1A] [hbA [[hc0A heA] hrA]]].
destruct wB as [[hk0B hk1B] [hbB [[hc0B heB] hrB]]].
pose proof (QleT'_to_Qle 0 (cl_kappa A) hk0A) as HkA0.
pose proof (QltT_to_Qlt (cl_kappa A) 1 hk1A) as HkA1.
pose proof (NatLe_drop 1 (cl_N A) hbA) as HbA.
pose proof (QleT'_to_Qle 0 (cl_c0 A) hc0A) as Hc0A.
pose proof (QleT'_to_Qle 0 (cl_kappa B) hk0B) as HkB0.
pose proof (QltT_to_Qlt (cl_kappa B) 1 hk1B) as HkB1.
assert (Hface' : cl_eps A == cl_c0 B).
{ apply (proj1 (Qeq_bool_iff (cl_eps A) (cl_c0 B))).
  apply RealSetoid.Id_eq. exact Hface. }
assert (HrB' : Qlt (cl_eps A * q_pow (1 - cl_kappa B) (cl_N B)) (cl_eps B)).
{ rewrite Hface'. exact (QltT_to_Qlt _ _ hrB). }
assert (Hk0c : QleT' 0 (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)).
{ apply Qle_to_QleT'.
  apply (uc_kappa_comp_le (cl_kappa A) (cl_kappa B) HkA0 HkB0 HkB1). }
assert (Hk1c : QltT (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B) 1).
{ apply Qlt_to_QltT.
  apply (uc_kappa_comp_lt (cl_kappa A) (cl_kappa B) HkA1 HkB1). }
assert (Hbc : NatLe 1 (cl_N A + cl_N B)%nat).
{ apply NatLe_lift. lia. }
assert (Hreach : QltT
    (cl_c0 A * q_pow (1 - (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B))
                     (cl_N A + cl_N B)%nat)
    (cl_eps B)).
{ apply (uc_chain_reach (cl_c0 A) (cl_eps A) (cl_eps B)
           (cl_kappa A) (cl_kappa B) (cl_N A) (cl_N B)
           Hc0A HkA0 HkA1 HkB0 HkB1 hrA (Qlt_to_QltT _ _ HrB')). }
apply (check_claim_inl_of_pass (chain_claim A B)
         (((Hk0c, Hk1c), (Hbc, ((hc0A, heB), Hreach))))).
Qed.

(* ============================================================ *)
(* §10 Real 层对接件（并列形态）：r_arch_pow_real 的预算即             *)
(*     宪法的击穿预算——同一 sigT (fun N => ...) 形状，两套载体        *)
(* ============================================================ *)

Definition real_budget_witness (kappa a eps : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps)
  : sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps) :=
  r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps.

(* ============================================================ *)
(* §11 vm_compute 数值自测（G3 样例输出源）                          *)
(* ============================================================ *)

Definition demo_ok : claim_decl := mk_claim (8 # 10) (1 # 10) (1 # 2) 5 21.
(* c0=4/5, eps=1/10, kappa=1/2, N=5：4/5·(1/2)^5 = 1/40 < 1/10 —— 合法改进声明 *)

Eval vm_compute in check_report demo_ok.
Eval vm_compute in check_report claim_bad_kappa1.
Eval vm_compute in check_report claim_bad_kappaneg.
Eval vm_compute in check_report claim_bad_budget.
Eval vm_compute in check_report claim_bad_reach.

Lemma test_demo_ok_pass : Id (check_report demo_ok) v_pass.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §12 提取探针（G3：Obj.magic = 0）                                *)
(* ============================================================ *)

Set Warnings "-extraction-opaque-accessed".
