(* 五字段指针｜使命：周期 2 类收敛子族（D=6）——非折半线收敛子族周期分类画像
   第二档第二件：D=6·√6=[2; overline{2,4}]·周期 2。
   周期 2 ⟹ 2 步块矩阵 N=[[9,2],[4,1]]（det=+1＝T(2)·T(4)）常系数化——免状态机化 T=2 档。
   §C 载体层：d6pair/e6pair——对偶穿线（独立复算 ① 全域核对独立 CF
     发生器 n≤60）：(x_k,y_k)=(p_{2k+1},p_{2k}) 基 (5,2)｜(z_k,w_k)=(q_{2k+1},q_{2k})
     基 (2,1)｜2 步 N 递推 (9x+2y,4x+y)＋d6x/d6y/d6z/d6w＋rec 展开件＋正性层；
   §N 范数层：d6_norm_quad 四件不变式归纳（周期 2 全常数·无 powneg1 交替）：
     S1: x²−6z²=1（成员流·+1 子族·x²−6y²=−1 模 6 无解故 +1 单族）＋S2: y²−6w²=−2＋
     C: xy−6zw=−2＋G: yz−xw=−1＋d6_norm_x/y/abs2＋d6_det（子族行列式 2＝锐度证书
     常元 2——成员流在行 1 故取 B₁₂=2·复算勘定与常元表并轨）＋
     d6_nonsquare（6 非完全平方 2²<6<3² 界矛盾）；
   §Q 终形装配层：Zpos 桥直迁＋d6yp/d6wp＋d6_member（=p_{2k+1}/q_{2k+1}＝√6 第
     2k+1 收敛子·k=0 即 5/2）＋d6_family_sharp（相邻成员距=2/(z_k z_{k+1}) 精确等号）
     ＋d6_family_sep（分离证书·零前提位仅 gap≠0）＋d6_q_square_sharp（|member²−6|=
     1/z² 精确等号）＋d6_q_square_gap_instance（实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 5/2·49/20·范数
     |49²−6·20²|=1·锐度 |5/2−49/20|=1/20=2/(2·20) 精确等号·Q 平方锐度 1/4·N 步 (49,20)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS
   （载体↔真收敛子 n≤60｜四件不变式 n≤60｜det=2 n≤60｜sharp k≤12｜sep 全称网格
   24187 例·等号 26 例全 |gap|=1｜q_square_sharp k≤12｜6 非平方 c≤200｜√6 周期 2
   勘形＋Pell 锚 (5,2)/(49,20)/(485,198)/(4801,1960)）。
   依赖：S02_CauchyComplete＋fib_machine＋fib_qdomain＋pell_family（迁移件群零重证
     直迁调用·同 d3_family）；Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面为库内在册同款先例形；证明体内
     构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典逻辑；定义面透明；
     主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d6_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d6pair/e6pair 对偶穿线＋d6x/y/z/w＋递归展开＋正性层     *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[9,2],[4,1]]·基 (p_1,p_0)=(5,2) *)
Fixpoint d6pair (n : nat) : Z * Z :=
  match n with
  | O => (5%Z, 2%Z)
  | S k => match d6pair k with pair x y => ((9 * x + 2 * y)%Z, (4 * x + y)%Z) end
  end.

(* Q 流：同系数 2 步递推·基 (q_1,q_0)=(2,1) *)
Fixpoint e6pair (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 1%Z)
  | S k => match e6pair k with pair x y => ((9 * x + 2 * y)%Z, (4 * x + y)%Z) end
  end.

Definition d6x (n : nat) : Z := fst (d6pair n).
Definition d6y (n : nat) : Z := snd (d6pair n).
Definition d6z (n : nat) : Z := fst (e6pair n).
Definition d6w (n : nat) : Z := snd (e6pair n).

Lemma d6x_0 : d6x 0 = 5%Z.
Proof. reflexivity. Qed.

Lemma d6y_0 : d6y 0 = 2%Z.
Proof. reflexivity. Qed.

Lemma d6z_0 : d6z 0 = 2%Z.
Proof. reflexivity. Qed.

Lemma d6w_0 : d6w 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d6pair_unfold : forall n : nat,
  d6pair (S n) = ((9 * fst (d6pair n) + 2 * snd (d6pair n))%Z,
                  (4 * fst (d6pair n) + snd (d6pair n))%Z).
Proof. intro n. cbn [d6pair]. destruct (d6pair n) as [a b]. reflexivity. Qed.

Lemma e6pair_unfold : forall n : nat,
  e6pair (S n) = ((9 * fst (e6pair n) + 2 * snd (e6pair n))%Z,
                  (4 * fst (e6pair n) + snd (e6pair n))%Z).
Proof. intro n. cbn [e6pair]. destruct (e6pair n) as [a b]. reflexivity. Qed.

Lemma d6x_rec : forall n, d6x (S n) = (9 * d6x n + 2 * d6y n)%Z.
Proof. intro n. unfold d6x, d6y. rewrite d6pair_unfold. reflexivity. Qed.

Lemma d6y_rec : forall n, d6y (S n) = (4 * d6x n + d6y n)%Z.
Proof. intro n. unfold d6x, d6y. rewrite d6pair_unfold. reflexivity. Qed.

Lemma d6z_rec : forall n, d6z (S n) = (9 * d6z n + 2 * d6w n)%Z.
Proof. intro n. unfold d6z, d6w. rewrite e6pair_unfold. reflexivity. Qed.

Lemma d6w_rec : forall n, d6w (S n) = (4 * d6z n + d6w n)%Z.
Proof. intro n. unfold d6z, d6w. rewrite e6pair_unfold. reflexivity. Qed.

(* 正性层：x/y 流全 ≥1；z 流 ≥1、w 流 ≥0（Q 分母位与 Zpos 桥守卫） *)
Lemma d6xy_ge1 : forall n, (1 <= d6x n)%Z /\ (1 <= d6y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d6x_0 | rewrite d6y_0]; lia.
  - split; rewrite ?d6x_rec, ?d6y_rec; lia.
Qed.

Lemma d6zw_ge : forall n, (1 <= d6z n)%Z /\ (0 <= d6w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d6z_0 | rewrite d6w_0]; lia.
  - split; rewrite ?d6z_rec, ?d6w_rec; lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d6_norm_quad 四件不变式（全常数）＋det＋nonsquare        *)
(* ============================================================ *)

(* 四件不变式归纳（周期 2 全常数形）：基 (5,2)/(2,1) 直接 ring；步例
   S1'=81·S1+36·C+4·S2｜S2'=16·S1+8·C+S2｜C'=36·S1+17·C+2·S2｜G'=G·ring 分解闭合 *)
Lemma d6_norm_quad : forall n : nat,
  (d6x n * d6x n - 6 * (d6z n * d6z n) = 1)%Z /\
  (d6y n * d6y n - 6 * (d6w n * d6w n) = (-2))%Z /\
  (d6x n * d6y n - 6 * (d6z n * d6w n) = (-2))%Z /\
  (d6y n * d6z n - d6x n * d6w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d6x_rec n), (d6z_rec n).
      transitivity ((81 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 36 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + 4 * (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d6y_rec n), (d6w_rec n).
      transitivity ((16 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 8 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d6x_rec n), (d6y_rec n), (d6z_rec n), (d6w_rec n).
      transitivity ((36 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 17 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + 2 * (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d6y_rec n), (d6z_rec n), (d6x_rec n), (d6w_rec n).
      transitivity ((d6y n * d6z n - d6x n * d6w n)%Z).
      * ring.
      * exact H4.
Qed.

(* 主语句一（成员流范数）：x²−6z² = 1（+1 子族·复算①全域） *)
Theorem d6_norm_x : forall n : nat,
  (d6x n * d6x n - 6 * (d6z n * d6z n) = 1)%Z.
Proof. intro n. exact (proj1 (d6_norm_quad n)). Qed.

(* 主语句二（伴流范数）：y²−6w² = −2 *)
Theorem d6_norm_y : forall n : nat,
  (d6y n * d6y n - 6 * (d6w n * d6w n) = (-2))%Z.
Proof. intro n. exact (proj1 (proj2 (d6_norm_quad n))). Qed.

(* 族上整隙恰 2（伴流） *)
Theorem d6_norm_y_abs2 : forall n : nat,
  Z.abs (d6y n * d6y n - 6 * (d6w n * d6w n)) = 2%Z.
Proof. intro n. rewrite (d6_norm_y n). reflexivity. Qed.

(* 主语句三（子族行列式）：x_n·z_{n+1}−x_{n+1}·z_n = 2
   ——锐度证书常元 2（成员流行 1 的 B₁₂ 位） *)
Theorem d6_det : forall n : nat,
  (d6x n * d6z (S n) - d6x (S n) * d6z n = 2)%Z.
Proof.
  intro n. rewrite (d6z_rec n), (d6x_rec n).
  transitivity ((- (2 * (d6y n * d6z n - d6x n * d6w n)))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d6_norm_quad n)))). reflexivity.
Qed.

(* 6 非完全平方（2²<6<3² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d6_nonsquare : forall c : Z, (6 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 6)%Z) by lia.
  assert (Hgt : (2 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 2 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d6_member＋双定理＋Q 平方锐度               *)
(* ============================================================ *)

Definition d6yp (k : nat) : positive := Zpos_of (d6x k).
Definition d6wp (k : nat) : positive := Zpos_of (d6z k).

Lemma d6yp_pos : forall k, Z.pos (d6yp k) = d6x k.
Proof.
  intro k. unfold d6yp. apply Zpos_of_pos.
  destruct (d6xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d6wp_pos : forall k, Z.pos (d6wp k) = d6z k.
Proof.
  intro k. unfold d6wp. apply Zpos_of_pos.
  destruct (d6zw_ge k) as [Hz _]. lia.
Qed.

(* 族成员：p_{2k+1}/q_{2k+1}＝√6 第 2k+1 收敛子（x²−6y²=+1 子族·k=0 即 5/2） *)
Definition d6_member (k : nat) : Q := (Z.pos (d6yp k) # d6wp k)%Q.

(* 族证书锐度（主语句一）：相邻族成员距 = 2/(z_k z_{k+1}) 精确等号
   ——d6_det 常元 2 等号实现（d13_family_sharp 同构·常元 5→2 周期 2 形） *)
Theorem d6_family_sharp : forall k : nat,
  QeqT (Qabs (d6_member k - d6_member (S k)))
       ((Z.pos 2) # (d6wp k * d6wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d6_member k - d6_member (S k))%Q ==
               ((Z.pos (d6yp k) * Z.pos (d6wp (S k))
                 - Z.pos (d6yp (S k)) * Z.pos (d6wp k))
                 # (d6wp k * d6wp (S k)))%Q).
  { unfold d6_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d6yp_pos k), (d6yp_pos (S k)).
    assert (Hd2 : (d6x k * Z.pos (d6wp (S k))
                   - d6x (S k) * Z.pos (d6wp k) = 2)%Z).
    { pose proof (d6_det k) as Hdet.
      rewrite <- (d6wp_pos (S k)), <- (d6wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* 族分离证书（主语句二）：任意 a/b 到族成员距 ≥ 1/(b·z_k)
   （d13_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d6_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d6z k - d6x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d6wp k)) # 1))
        (Qabs ((a # b)%Q - d6_member k)).
Proof.
  intros a b k Hk. unfold d6_member.
  assert (Hk2 : (a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b <> 0)%Z).
  { rewrite (d6wp_pos k), (d6yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b)
                  # (b * d6wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d6yp k) # d6wp k)%Q))
          (Qinv ((Z.pos (b * d6wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d6yp k) # d6wp k)%Q))
                   (Qabs ((a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b)
                           # (b * d6wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d6wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主语句三）：|member²−6| = 1/z² 精确等号
   ——q_square_gap 下界 1/b² 在 +1 子族上恰被实现（d13_q_square_sharp 同构·
   常数范数 1 免 powneg1 分案） *)
Theorem d6_q_square_sharp : forall k : nat,
  QeqT (Qabs (d6_member k * d6_member k - (6 # 1)%Q))
       (Qinv ((Z.pos (d6wp k * d6wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d6_member k * d6_member k - (6 # 1))%Q ==
               ((Z.pos (d6yp k) * Z.pos (d6yp k)
                 - 6 * (Z.pos (d6wp k) * Z.pos (d6wp k)))
                 # (d6wp k * d6wp k))%Q).
  { unfold d6_member. apply (q_square_cross (Z.pos (d6yp k)) 6 (d6wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d6yp_pos k).
    assert (Hn2 : (d6x k * d6x k
                   - 6 * (Z.pos (d6wp k) * Z.pos (d6wp k)) = 1)%Z).
    { pose proof (d6_norm_x k) as Hn.
      rewrite <- (d6wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d6wp k * d6wp k)) with (Z.pos 1 # d6wp k * d6wp k)%Q.
    change (Qinv (Z.pos (d6wp k * d6wp k) # 1)) with (1 # d6wp k * d6wp k)%Q.
    apply Qeq_refl.
Qed.

(* q_square_gap 实例调用（FIB3 主语句在 D=6 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d6_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d6wp k * d6wp k)) # 1))
        (Qabs (d6_member k * d6_member k - (6 # 1)%Q)).
Proof.
  intro k. unfold d6_member.
  apply (q_square_gap 6 (Z.pos (d6yp k)) (d6wp k)).
  - cbn. lia.
  - intro c. apply (d6_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d6x_rec.
Print Assumptions d6y_rec.
Print Assumptions d6z_rec.
Print Assumptions d6w_rec.
Print Assumptions d6xy_ge1.
Print Assumptions d6zw_ge.
Print Assumptions d6_norm_quad.
Print Assumptions d6_norm_x.
Print Assumptions d6_norm_y.
Print Assumptions d6_norm_y_abs2.
Print Assumptions d6_det.
Print Assumptions d6_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d6yp_pos.
Print Assumptions d6wp_pos.
Print Assumptions d6_family_sep.
Print Assumptions d6_family_sharp.
Print Assumptions d6_q_square_sharp.
Print Assumptions d6_q_square_gap_instance.

(* 数值锚一（族成员）：member 0 = p_1/q_1 = 5/2（x²−6y²=+1） *)
Lemma smoke_member_5_2 : (Qeq_bool (d6_member 0) (5 # 2)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员）：member 1 = p_3/q_3 = 49/20（x²−6y²=+1） *)
Lemma smoke_member_49_20 : (Qeq_bool (d6_member 1) (49 # 20)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|49²−6·20²| = 1（d6_norm_x 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d6x 1 * d6x 1 - 6 * (d6z 1 * d6z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|5/2−49/20| = 1/20 = 2/(2·20) 精确等号（d6_family_sharp 实例） *)
Lemma smoke_sharp_1_20 :
  (Qeq_bool (Qabs (d6_member 0 - d6_member 1))
            ((Z.pos 2) # (d6wp 0 * d6wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(5/2)²−6| = 1/4（d6_q_square_sharp 实例） *)
Lemma smoke_qsq_1_4 :
  (Qeq_bool (Qabs (d6_member 0 * d6_member 0 - (6 # 1)%Q))
            (Qinv ((Z.pos (d6wp 0 * d6wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 49, z_1 = 20（p_3/q_3 载体值） *)
Lemma smoke_step_49_20 :
  (Z.eqb (d6x 1) 49%Z, Z.eqb (d6z 1) 20%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_5_2.
Print Assumptions smoke_member_49_20.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_20.
Print Assumptions smoke_qsq_1_4.
Print Assumptions smoke_step_49_20.

From Stdlib Require Import Extraction.
Separate Extraction d6pair e6pair d6x d6y d6z d6w d6yp d6wp
  d6_member d6_norm_y_abs2 d6_det d6_family_sep d6_family_sharp
  d6_q_square_sharp d6_q_square_gap_instance
  smoke_member_5_2 smoke_member_49_20 smoke_norm_1 smoke_sharp_1_20
  smoke_qsq_1_4 smoke_step_49_20.
