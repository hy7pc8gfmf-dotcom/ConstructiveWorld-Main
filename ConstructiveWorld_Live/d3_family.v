(* 五字段指针｜使命：周期 2 类收敛子族（D=3）——非折半线收敛子族周期分类画像
   第二档首攻：D=3·√3=[1; overline{1,2}]·周期 2。
   周期 2 ⟹ 2 步块矩阵 N=[[3,1],[2,1]]（det=+1＝T(1)·T(2)）常系数化：
     (p_{2(k+1)+1},p_{2k+1})=N·(p_{2k+1},p_{2k−0}·p_{2k})——免状态机化的 T=2 档。
   §C 载体层：d3pair/e3pair——对偶穿线（独立复算 ① 全域核对独立 CF
     发生器 n≤60）：(x_k,y_k)=(p_{2k+1},p_{2k}) 基 (2,1)｜(z_k,w_k)=(q_{2k+1},q_{2k})
     基 (1,1)｜2 步 N 递推 (3x+y,2x+y)＋d3x/d3y/d3z/d3w＋rec 展开件＋正性层；
   §N 范数层：d3_norm_quad 四件不变式归纳（周期 2 下全常数·无 powneg1 交替——对
     D=13 quad 的减重形）：S1: x²−3z²=1（成员流·+1 子族）＋S2: y²−3w²=−2＋
     C: xy−3zw=−1＋G: yz−xw=−1（det 内芯）＋d3_norm_x/y/abs2＋d3_det（子族行列式
     1＝锐度证书常元 1——复算勘定·成员流在行 1 故取 B₁₂=1·预估 2 经修正）
     ＋d3_nonsquare（3 非完全平方 1²<3<2² 界矛盾·q_square_gap 使用位前提供）；
   §Q 终形装配层：Zpos 桥（pell_family Zpos_of/Zpos_of_pos 直迁调用零重证）＋d3yp/d3wp＋
     d3_member（=p_{2k+1}/q_{2k+1}＝√3 第 2k+1 收敛子＝x²−3y²=+1 子族·k=0 即 2/1）＋
     d3_family_sharp（族证书锐度：相邻成员距=1/(z_k z_{k+1}) 精确等号）＋d3_family_sep
     （分离证书：任意 a/b 到族成员距≥1/(b·z_k)·零前提位仅 gap≠0）＋d3_q_square_sharp
     （|member²−3|=1/z² 精确等号——q_square_gap 下界在族上精确实现）＋
     d3_q_square_gap_instance（实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 2/1·7/4·范数
     |7²−3·4²|=1·锐度 |2−7/4|=1/4 精确等号·Q 平方锐度 1/1·N 步 (7,4)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS
   （载体↔真收敛子 n≤60｜四件不变式 n≤60｜det=1 n≤60｜sharp k≤12｜sep 全称网格
   24160 例·等号 82 例全 |gap|=1｜q_square_sharp k≤12｜3 非平方 c≤200｜√3 周期 2
   勘形＋Pell 锚 (2,1)/(7,4)/(26,15)/(97,56)）。
   依赖：S02_CauchyComplete（QeqT/QleT'/qeq_imp_qeqT）＋fib_machine（zabs 系/
     fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r 迁移件群）＋
     fib_qdomain（q_square_cross/q_square_gap）＋pell_family（Zpos_of/Zpos_of_pos）；
     Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面为库内在册同款先例形；证明体内
     构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典逻辑；定义面透明；
     主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d3_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d3pair/e3pair 对偶穿线＋d3x/y/z/w＋递归展开＋正性层     *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[3,1],[2,1]]·基 (p_1,p_0)=(2,1) *)
Fixpoint d3pair (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 1%Z)
  | S k => match d3pair k with pair x y => ((3 * x + y)%Z, (2 * x + y)%Z) end
  end.

(* Q 流：同系数 2 步递推·基 (q_1,q_0)=(1,1) *)
Fixpoint e3pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 1%Z)
  | S k => match e3pair k with pair x y => ((3 * x + y)%Z, (2 * x + y)%Z) end
  end.

Definition d3x (n : nat) : Z := fst (d3pair n).
Definition d3y (n : nat) : Z := snd (d3pair n).
Definition d3z (n : nat) : Z := fst (e3pair n).
Definition d3w (n : nat) : Z := snd (e3pair n).

Lemma d3x_0 : d3x 0 = 2%Z.
Proof. reflexivity. Qed.

Lemma d3y_0 : d3y 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3z_0 : d3z 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3w_0 : d3w 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3pair_unfold : forall n : nat,
  d3pair (S n) = ((3 * fst (d3pair n) + snd (d3pair n))%Z,
                  (2 * fst (d3pair n) + snd (d3pair n))%Z).
Proof. intro n. cbn [d3pair]. destruct (d3pair n) as [a b]. reflexivity. Qed.

Lemma e3pair_unfold : forall n : nat,
  e3pair (S n) = ((3 * fst (e3pair n) + snd (e3pair n))%Z,
                  (2 * fst (e3pair n) + snd (e3pair n))%Z).
Proof. intro n. cbn [e3pair]. destruct (e3pair n) as [a b]. reflexivity. Qed.

Lemma d3x_rec : forall n, d3x (S n) = (3 * d3x n + d3y n)%Z.
Proof. intro n. unfold d3x, d3y. rewrite d3pair_unfold. reflexivity. Qed.

Lemma d3y_rec : forall n, d3y (S n) = (2 * d3x n + d3y n)%Z.
Proof. intro n. unfold d3x, d3y. rewrite d3pair_unfold. reflexivity. Qed.

Lemma d3z_rec : forall n, d3z (S n) = (3 * d3z n + d3w n)%Z.
Proof. intro n. unfold d3z, d3w. rewrite e3pair_unfold. reflexivity. Qed.

Lemma d3w_rec : forall n, d3w (S n) = (2 * d3z n + d3w n)%Z.
Proof. intro n. unfold d3z, d3w. rewrite e3pair_unfold. reflexivity. Qed.

(* 正性层：x/y 流全 ≥1；z 流 ≥1、w 流 ≥0（Q 分母位与 Zpos 桥守卫） *)
Lemma d3xy_ge1 : forall n, (1 <= d3x n)%Z /\ (1 <= d3y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d3x_0 | rewrite d3y_0]; lia.
  - split; rewrite ?d3x_rec, ?d3y_rec; lia.
Qed.

Lemma d3zw_ge : forall n, (1 <= d3z n)%Z /\ (0 <= d3w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d3z_0 | rewrite d3w_0]; lia.
  - split; rewrite ?d3z_rec, ?d3w_rec; lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d3_norm_quad 四件不变式（全常数）＋det＋nonsquare        *)
(* ============================================================ *)

(* 四件不变式归纳（周期 2 全常数形）：基 (2,1)/(1,1) 直接 ring；步例
   S1'=9·S1+6·C+S2｜S2'=4·S1+4·C+S2｜C'=6·S1+5·C+S2｜G'=G·ring 分解闭合 *)
Lemma d3_norm_quad : forall n : nat,
  (d3x n * d3x n - 3 * (d3z n * d3z n) = 1)%Z /\
  (d3y n * d3y n - 3 * (d3w n * d3w n) = (-2))%Z /\
  (d3x n * d3y n - 3 * (d3z n * d3w n) = (-1))%Z /\
  (d3y n * d3z n - d3x n * d3w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d3x_rec n), (d3z_rec n).
      transitivity ((9 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 6 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3y_rec n), (d3w_rec n).
      transitivity ((4 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 4 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3x_rec n), (d3y_rec n), (d3z_rec n), (d3w_rec n).
      transitivity ((6 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 5 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3y_rec n), (d3z_rec n), (d3x_rec n), (d3w_rec n).
      transitivity ((d3y n * d3z n - d3x n * d3w n)%Z).
      * ring.
      * exact H4.
Qed.

(* 主语句一（成员流范数）：x²−3z² = 1（+1 子族·复算①全域） *)
Theorem d3_norm_x : forall n : nat,
  (d3x n * d3x n - 3 * (d3z n * d3z n) = 1)%Z.
Proof. intro n. exact (proj1 (d3_norm_quad n)). Qed.

(* 主语句二（伴流范数）：y²−3w² = −2 *)
Theorem d3_norm_y : forall n : nat,
  (d3y n * d3y n - 3 * (d3w n * d3w n) = (-2))%Z.
Proof. intro n. exact (proj1 (proj2 (d3_norm_quad n))). Qed.

(* 族上整隙恰 2（伴流） *)
Theorem d3_norm_y_abs2 : forall n : nat,
  Z.abs (d3y n * d3y n - 3 * (d3w n * d3w n)) = 2%Z.
Proof. intro n. rewrite (d3_norm_y n). reflexivity. Qed.

(* 主语句三（子族行列式）：x_n·z_{n+1}−x_{n+1}·z_n = 1
   ——锐度证书常元 1（成员流行 1 的 B₁₂ 位） *)
Theorem d3_det : forall n : nat,
  (d3x n * d3z (S n) - d3x (S n) * d3z n = 1)%Z.
Proof.
  intro n. rewrite (d3z_rec n), (d3x_rec n).
  transitivity ((- (d3y n * d3z n - d3x n * d3w n))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d3_norm_quad n)))). reflexivity.
Qed.

(* 3 非完全平方（1²<3<2² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d3_nonsquare : forall c : Z, (3 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 3)%Z) by lia.
  assert (Hgt : (1 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 1 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d3_member＋双定理＋Q 平方锐度               *)
(* ============================================================ *)

Definition d3yp (k : nat) : positive := Zpos_of (d3x k).
Definition d3wp (k : nat) : positive := Zpos_of (d3z k).

Lemma d3yp_pos : forall k, Z.pos (d3yp k) = d3x k.
Proof.
  intro k. unfold d3yp. apply Zpos_of_pos.
  destruct (d3xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d3wp_pos : forall k, Z.pos (d3wp k) = d3z k.
Proof.
  intro k. unfold d3wp. apply Zpos_of_pos.
  destruct (d3zw_ge k) as [Hz _]. lia.
Qed.

(* 族成员：p_{2k+1}/q_{2k+1}＝√3 第 2k+1 收敛子（x²−3y²=+1 子族·k=0 即 2/1） *)
Definition d3_member (k : nat) : Q := (Z.pos (d3yp k) # d3wp k)%Q.

(* 族证书锐度（主语句一）：相邻族成员距 = 1/(z_k z_{k+1}) 精确等号
   ——d3_det 常元 1 等号实现（d13_family_sharp 同构·常元 5→1 周期 2 形） *)
Theorem d3_family_sharp : forall k : nat,
  QeqT (Qabs (d3_member k - d3_member (S k)))
       ((Z.pos 1) # (d3wp k * d3wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d3_member k - d3_member (S k))%Q ==
               ((Z.pos (d3yp k) * Z.pos (d3wp (S k))
                 - Z.pos (d3yp (S k)) * Z.pos (d3wp k))
                 # (d3wp k * d3wp (S k)))%Q).
  { unfold d3_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d3yp_pos k), (d3yp_pos (S k)).
    assert (Hd2 : (d3x k * Z.pos (d3wp (S k))
                   - d3x (S k) * Z.pos (d3wp k) = 1)%Z).
    { pose proof (d3_det k) as Hdet.
      rewrite <- (d3wp_pos (S k)), <- (d3wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* 族分离证书（主语句二）：任意 a/b 到族成员距 ≥ 1/(b·z_k)
   （d13_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d3_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d3z k - d3x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d3wp k)) # 1))
        (Qabs ((a # b)%Q - d3_member k)).
Proof.
  intros a b k Hk. unfold d3_member.
  assert (Hk2 : (a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b <> 0)%Z).
  { rewrite (d3wp_pos k), (d3yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b)
                  # (b * d3wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d3yp k) # d3wp k)%Q))
          (Qinv ((Z.pos (b * d3wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d3yp k) # d3wp k)%Q))
                   (Qabs ((a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b)
                           # (b * d3wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d3wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主语句三）：|member²−3| = 1/z² 精确等号
   ——q_square_gap 下界 1/b² 在 +1 子族上恰被实现（d13_q_square_sharp 同构·
   常数范数 1 免 powneg1 分案） *)
Theorem d3_q_square_sharp : forall k : nat,
  QeqT (Qabs (d3_member k * d3_member k - (3 # 1)%Q))
       (Qinv ((Z.pos (d3wp k * d3wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d3_member k * d3_member k - (3 # 1))%Q ==
               ((Z.pos (d3yp k) * Z.pos (d3yp k)
                 - 3 * (Z.pos (d3wp k) * Z.pos (d3wp k)))
                 # (d3wp k * d3wp k))%Q).
  { unfold d3_member. apply (q_square_cross (Z.pos (d3yp k)) 3 (d3wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d3yp_pos k).
    assert (Hn2 : (d3x k * d3x k
                   - 3 * (Z.pos (d3wp k) * Z.pos (d3wp k)) = 1)%Z).
    { pose proof (d3_norm_x k) as Hn.
      rewrite <- (d3wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d3wp k * d3wp k)) with (Z.pos 1 # d3wp k * d3wp k)%Q.
    change (Qinv (Z.pos (d3wp k * d3wp k) # 1)) with (1 # d3wp k * d3wp k)%Q.
    apply Qeq_refl.
Qed.

(* q_square_gap 实例调用（FIB3 主语句在 D=3 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d3_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d3wp k * d3wp k)) # 1))
        (Qabs (d3_member k * d3_member k - (3 # 1)%Q)).
Proof.
  intro k. unfold d3_member.
  apply (q_square_gap 3 (Z.pos (d3yp k)) (d3wp k)).
  - cbn. lia.
  - intro c. apply (d3_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d3x_rec.
Print Assumptions d3y_rec.
Print Assumptions d3z_rec.
Print Assumptions d3w_rec.
Print Assumptions d3xy_ge1.
Print Assumptions d3zw_ge.
Print Assumptions d3_norm_quad.
Print Assumptions d3_norm_x.
Print Assumptions d3_norm_y.
Print Assumptions d3_norm_y_abs2.
Print Assumptions d3_det.
Print Assumptions d3_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d3yp_pos.
Print Assumptions d3wp_pos.
Print Assumptions d3_family_sep.
Print Assumptions d3_family_sharp.
Print Assumptions d3_q_square_sharp.
Print Assumptions d3_q_square_gap_instance.

(* 数值锚一（族成员）：member 0 = p_1/q_1 = 2/1（x²−3y²=+1） *)
Lemma smoke_member_2_1 : (Qeq_bool (d3_member 0) (2 # 1)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员）：member 1 = p_3/q_3 = 7/4（x²−3y²=+1） *)
Lemma smoke_member_7_4 : (Qeq_bool (d3_member 1) (7 # 4)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|7²−3·4²| = 1（d3_norm_x 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d3x 1 * d3x 1 - 3 * (d3z 1 * d3z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|2−7/4| = 1/4 = 1/(1·4) 精确等号（d3_family_sharp 实例） *)
Lemma smoke_sharp_1_4 :
  (Qeq_bool (Qabs (d3_member 0 - d3_member 1))
            ((Z.pos 1) # (d3wp 0 * d3wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|2²−3| = 1 = 1/1²（d3_q_square_sharp 实例） *)
Lemma smoke_qsq_1_1 :
  (Qeq_bool (Qabs (d3_member 0 * d3_member 0 - (3 # 1)%Q))
            (Qinv ((Z.pos (d3wp 0 * d3wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 7, z_1 = 4（p_3/q_3 载体值） *)
Lemma smoke_step_7_4 :
  (Z.eqb (d3x 1) 7%Z, Z.eqb (d3z 1) 4%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_2_1.
Print Assumptions smoke_member_7_4.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_4.
Print Assumptions smoke_qsq_1_1.
Print Assumptions smoke_step_7_4.

From Stdlib Require Import Extraction.
Separate Extraction d3pair e3pair d3x d3y d3z d3w d3yp d3wp
  d3_member d3_norm_y_abs2 d3_det d3_family_sep d3_family_sharp
  d3_q_square_sharp d3_q_square_gap_instance
  smoke_member_2_1 smoke_member_7_4 smoke_norm_1 smoke_sharp_1_4
  smoke_qsq_1_1 smoke_step_7_4.
