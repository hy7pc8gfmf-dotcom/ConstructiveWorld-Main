(* ============================================================ *)
(* TrueNumerator.v —— 本件形式化 Beukers 逼近真分子族的闭式与恒等性：        *)
(*   P*_n(1/2) = r_n/2^{2n}，r_n == 2^{n+1}·p_n（p_n 为 bv_p 的 Laurent       *)
(*   闭式），即 P*_n(1/2) == p_n·2^{1−n} == tn_Ps_half n；一般恒等            *)
(*   tn_x_eq_bv_x：x'_n == tn_x n == p_n/q̃_n == bv_x n。                     *)
(*                                                                          *)
(* 防错注记：P*_n(1/2) 若写成 r_n/2^n，则与 x'_1 = 2/3、P*_2(1/2) = 9/2      *)
(*   不符；自洽形为 r_n/2^{2n}（8/4 = 2、72/16 = 9/2）。                     *)
(*                                                                          *)
(* 数值锚（n=0..5）：                                                        *)
(*   p:  0, 2, 9, 131/3, 445/2, 34997/30                                     *)
(*   q̃:  1, 3, 13, 63, 321, 1683                                             *)
(*   x': 0, 2/3, 9/13, 131/189, 445/642, 34997/50490                         *)
(*   r:  0, 8, 72, 2096/3, 7120, 1119904/15                                  *)
(*   P*_n(1/2): 0, 2, 9/2, 131/12, 445/16, 34997/480                         *)
(*                                                                          *)
(* 整性事实：r_n = P*_n(1/2)·2^n：r_0 = 0、r_1 = 8、r_2 = 72、r_4 = 7120      *)
(*   为整；r_3 = 2096/3 与 r_5 = 1119904/15 非整（分母含奇素因子）；          *)
(*   真分子族自 n=3 起本质有理——q̃_n 含奇素因子，任何 2 幂归一不能挽回。       *)
(*                                                                          *)
(* 谐和型候选的否定对照：三候选（(1/2)·ΣC(n,k)²(H_k+H_{n−k})(1/2)^k、          *)
(*   ΣC(n,k)²(H_{n+k}−H_k)(1/2)^k、ΣC(n,k)²·H_k·(1/2)^k）自 n=1 起全不配      *)
(*   （见证 tn_harm1_anchor、tn_harm2_anchor）；根因：真分子含 2 幂尾项        *)
(*   （Laurent 2^{j−n}−1 结构），非纯谐和和。                                 *)
(*                                                                          *)
(* 主要结果：tn_r/tn_Ps_half/tn_x/tn_Qhalf（定义面）；tn_Pn_list（家族列表）   *)
(*   与 length/nth 求值面；tn_x_eq_bv_x（一般恒等桥，纯 Set）；x' 序列         *)
(*   n=0..5 数值锚组与跨变体对照锚（tn_x3_bv_anchor 等）；Q 层支撑引理         *)
(*   tn_qpow2_ne/tn_qpow2_inv/tn_Qinv_cong/tn_sh_one/tn_core_eq。             *)
(*                                                                          *)
(* 构造性注记：全件 Qed、零承认；主件 tn_x_eq_bv_x 与锚组取 QeqT 零前提       *)
(*   （纯 Set），nth 求值面带 k ≤ N 的 nat 前提；支撑引理仅服务推理；         *)
(*   可提取；文末 Print Assumptions 复核。                                    *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp + BeukersLists              *)
(*   BeukersVariant（传递依赖 PolyIntegral PadeErrorIntegral PintMono）。     *)
(*                                                                          *)
(* 编译配方：coqc 9.1 直调（无 -Q），cpu_guard 包裹，-o 输出临时目录，         *)
(*   树内 .vo 不重写。                                                       *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists BeukersVariant.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 真分子族定义面（r_n == 2^{n+1}·p_n 换算）                          *)
(* ============================================================ *)

(* Q_n(1/2)（库面：BeukersLists 系数列表 Horner 求值） *)
Definition tn_Qhalf (n : nat) : Q := bkQ (bk_Qn_list n) (1 # 2)%Q.

(* tn_r：r 家族 r_n == 2^{n+1}·p_n（跨变体换算） *)
Definition tn_r (n : nat) : Q := (q_pow (2 # 1)%Q (Datatypes.S n) * bv_p n)%Q.

(* 真分子在 1/2 的值：P*_n(1/2) = r_n/2^{2n} = p_n·2^{1−n}
   （写成 ·(1/2)^{n+n} 免 Qinv，定义面全乘法） *)
Definition tn_Ps_half (n : nat) : Q := (tn_r n * q_pow (1 # 2)%Q (n + n))%Q.

(* tn_x：约束形 x'_n = P*_n(1/2)/(2·Q_n(1/2)) *)
Definition tn_x (n : nat) : Q := (tn_Ps_half n / (2 * tn_Qhalf n))%Q.

(* 真分子族列表：[P*_0(1/2); ...; P*_N(1/2)]（列表 Fixpoint） *)
Fixpoint tn_Pn_list (N : nat) : list Q :=
  match N with
  | 0 => (tn_Ps_half 0)%Q :: nil
  | Datatypes.S m => tn_Pn_list m ++ ((tn_Ps_half (Datatypes.S m))%Q :: nil)
  end.

(* ============================================================ *)
(* §B Q 层支撑引理（Prop 面，仅服务推理）                                 *)
(* ============================================================ *)

(* 2 的 nat 幂非零（Qmult_inv_r 前提件） *)
Lemma tn_qpow2_ne : forall k : nat, ~ (q_pow (2 # 1)%Q k == 0%Q).
Proof.
  induction k as [| k IH]; intro H.
  - unfold Qeq in H. cbn [q_pow Qnum Qden Qmult] in H. lia.
  - cbn [q_pow] in H. destruct (Qmult_integral _ _ H) as [H1 | H1].
    + unfold Qeq in H1. cbn [Qnum Qden Qmult] in H1. lia.
    + exact (IH H1).
Qed.

(* tn_sh_one：q_pow 2 k · q_pow (1/2) k == 1（2 与 1/2 互逆） *)
Lemma tn_sh_one : forall k : nat, q_pow (2 # 1)%Q k * q_pow (1 # 2)%Q k == 1%Q.
Proof.
  intro k. rewrite <- (bk_q_pow_mul (2 # 1) (1 # 2) k).
  assert (H21 : ((2 # 1) * (1 # 2))%Q == (1 # 1)%Q) by reflexivity.
  rewrite H21. apply bk_q_pow_one.
Qed.

(* tn_qpow2_inv：/2^k == (1/2)^k（零前提，由 Qinv_mult_distr） *)
Lemma tn_qpow2_inv : forall k : nat, Qinv (q_pow (2 # 1)%Q k) == q_pow (1 # 2)%Q k.
Proof.
  intro k.
  assert (HA := tn_sh_one k).
  rewrite <- (Qmult_1_r (Qinv (q_pow (2 # 1)%Q k))).
  rewrite <- HA.
  rewrite Qmult_assoc.
  rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q k)) (q_pow (2 # 1)%Q k)).
  rewrite (Qmult_inv_r (q_pow (2 # 1)%Q k) (tn_qpow2_ne k)).
  apply Qmult_1_l.
Qed.

(* tn_half_inv：/2 == 1/2 *)
Lemma tn_half_inv : Qinv (2 # 1)%Q == (1 # 2)%Q.
Proof. reflexivity. Qed.

(* Qeq setoid 保持件：x == y ⟹ /y == /x（Qeq 逐点等，零前提；
   方向取 y==x 入 x==y 出，正接 bk_Qn_half_closed 原向） *)
Lemma tn_Qinv_cong : forall x y : Q, x == y -> Qinv y == Qinv x.
Proof. intros x y H. rewrite H. reflexivity. Qed.

(* tn_core_eq：s·h == 1 下 (2sh·p·h²)·((1/2)·/E) == p·(h·/E)
   —— tn_x_eq_bv_x 的剩余代数（环重排 + 两次注入改写） *)
Lemma tn_core_eq : forall p E s h : Q,
  s * h == 1 ->
  ((2 * s * p * (h * h)) * ((1 # 2)%Q * Qinv E))%Q == p * (h * Qinv E).
Proof.
  intros p E s h Hsh.
  (* s·h² ⟶ (s·h)·h 纯重排 *)
  transitivity ((2 * (s * h) * p * h) * ((1 # 2)%Q * Qinv E))%Q.
  - ring.
  - rewrite Hsh.
    (* 先融 2·(1/2) == 1 *)
    transitivity (2 * (1 # 2)%Q * p * h * Qinv E)%Q.
    + ring.
    + assert (H21 : ((2 # 1) * (1 # 2))%Q == (1 # 1)%Q) by reflexivity.
      rewrite H21. ring.
Qed.

(* ============================================================ *)
(* §C 一般恒等桥：tn_x_eq_bv_x（纯 Set 语句，零前提）                     *)
(*   tn_x n == bv_x n，即 x'_n = P*_n(1/2)/(2Q_n(1/2)) == p_n/q̃_n        *)
(* ============================================================ *)

Theorem tn_x_eq_bv_x : forall n : nat, QeqT (tn_x n) (bv_x n).
Proof.
  intro n. apply qeq_imp_qeqT.
  unfold tn_x, tn_Ps_half, tn_r, tn_Qhalf, bv_x. unfold Qdiv.
  (* 指数归一：2^{S n} ⟶ 2·2^n；(1/2)^{n+n} ⟶ (1/2)^n·(1/2)^n *)
  rewrite (q_pow_succ (2 # 1)%Q n).
  rewrite (q_pow_add (1 # 2)%Q n n).
  (* Qinv 分配拆解（stdlib 零前提分配律 Qinv_mult_distr + tn 换形） *)
  rewrite (Qinv_mult_distr (2 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  rewrite tn_half_inv.
  rewrite (tn_Qinv_cong ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q)
             ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
             (bk_Qn_half_closed n)).
  rewrite (Qinv_mult_distr (q_pow (2 # 1)%Q n) (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  rewrite (tn_qpow2_inv n).
  apply (tn_core_eq (bv_p n) (bkQ (bk_Qn_list n) (1 # 2)%Q)
                    (q_pow (2 # 1)%Q n) (q_pow (1 # 2)%Q n) (tn_sh_one n)).
Qed.

(* ============================================================ *)
(* §D tn_Pn_list 求值面：length 与 nth                                   *)
(* ============================================================ *)

Lemma tn_Pn_list_length : forall N : nat, length (tn_Pn_list N) = Datatypes.S N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [tn_Pn_list]. rewrite app_length. rewrite IH. cbn [length]. lia.
Qed.

Lemma tn_Pn_list_nth : forall N k : nat, k <= N ->
  nth k (tn_Pn_list N) 0%Q == tn_Ps_half k.
Proof.
  induction N as [| N IH]; intros k Hk.
  - assert (Hk0 : k = 0) by lia. subst k. cbn [tn_Pn_list nth]. reflexivity.
  - destruct (Nat.eq_dec k (Datatypes.S N)) as [Heq | Hne].
    + subst k. cbn [tn_Pn_list].
      rewrite app_nth2 by (rewrite tn_Pn_list_length; lia).
      rewrite tn_Pn_list_length.
      replace (Datatypes.S N - Datatypes.S N) with 0 by lia.
      cbn [nth]. reflexivity.
    + assert (HkN : k <= N) by lia.
      cbn [tn_Pn_list].
      rewrite app_nth1 by (rewrite tn_Pn_list_length; lia).
      apply IH. exact HkN.
Qed.

(* ============================================================ *)
(* §E x' 序列 n=0..5 数值锚组（各锚由 vm_compute 精确判定）               *)
(* ============================================================ *)

Theorem tn_x0_anchor : QeqT (tn_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x1_anchor : QeqT (tn_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x2_anchor : QeqT (tn_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x3_anchor : QeqT (tn_x 3) (131 # 189)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x4_anchor : QeqT (tn_x 4) (445 # 642)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x5_anchor : QeqT (tn_x 5) (34997 # 50490)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 跨变体对照锚：tn_x n == bv_x n 的数值验证（n=3..5） *)
Theorem tn_x3_bv_anchor : QeqT (tn_x 3) (bv_x 3).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x4_bv_anchor : QeqT (tn_x 4) (bv_x 4).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x5_bv_anchor : QeqT (tn_x 5) (bv_x 5).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* r 家族数值锚：r_0=0、r_1=8、r_2=72；破整见证 r_3、r_5；r_4=7120 为整 *)
Theorem tn_r0_anchor : QeqT (tn_r 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r1_anchor : QeqT (tn_r 1) (8 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r2_anchor : QeqT (tn_r 2) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r3_anchor : QeqT (tn_r 3) (2096 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r4_anchor : QeqT (tn_r 4) (7120 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r5_anchor : QeqT (tn_r 5) (1119904 # 15)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* P*_n(1/2) 数值锚（P*_2(1/2) = 9/2 非整之数值验证） *)
Theorem tn_Ps1_anchor : QeqT (tn_Ps_half 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_Ps2_anchor : QeqT (tn_Ps_half 2) (9 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_Ps3_anchor : QeqT (tn_Ps_half 3) (131 # 12)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 谐和不配对照锚：库 bk_Pn_list 谐和分子在 1/2 求值
   （真值 tn_Ps_half 1 == 2、tn_Ps_half 2 == 9/2，均不配） *)
Theorem tn_harm1_anchor : QeqT (bkQ (bk_Pn_list 1) (1 # 2)%Q) (1 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_harm2_anchor : QeqT (bkQ (bk_Pn_list 2) (1 # 2)%Q) (19 # 8)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。        *)
(* ============================================================ *)

Print Assumptions tn_x_eq_bv_x.
Print Assumptions tn_x5_anchor.
Print Assumptions tn_r5_anchor.
Print Assumptions tn_Pn_list_nth.
Print Assumptions tn_harm2_anchor.
