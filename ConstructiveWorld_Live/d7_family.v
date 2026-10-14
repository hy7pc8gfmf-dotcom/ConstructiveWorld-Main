(* 五字段指针｜使命：D=7 周期 4 类收敛子族（谱线 T=4 档补全第一件）——非折半线
   收敛子族谱线 T=4 档首件：D=7·√7=[2; overline{1,1,1,4}]·周期 4。
   周期 4 ⟹ 4 步块矩阵 N=T(1)·T(1)·T(1)·T(4)=[[14,3],[9,2]]（det=+1＝(−1)^4）常系数化
   （独立复算 CF 发生器 n≤100 全域核对裁定）：
     (p_{4(k+1)+3},p_{4k+3})=N·(p_{4k+3},p_{4k+2})——免状态机化的 T=4 档。
   子族谱判据（独立复算勘定·CSV 同余判据列核对）：x²≡−1 (mod 7) 无解（剩余 0..6 平方
     {0,1,2,4} 不含 6）⟹ 负 Pell x²−7y²=−1 无解 ⟹ +1 单族（T 偶常数形档·d3/d6 母版同构）
     ——成员流在 4k+3 位全泳范数 +1（见证 8²=64≡1 (mod 7)）。
   §C 载体层：d7pair/e7pair——对偶穿线：(x_k,y_k)=(p_{4k+3},p_{4k+2}) 基 (8,5)｜
     (z_k,w_k)=(q_{4k+3},q_{4k+2}) 基 (3,2)｜4 步 N 递推 (14x+3y,9x+2y)＋d7x/d7y/d7z/d7w
     ＋rec 展开件＋正性层；
   §N 范数层：d7_norm_quad 四件不变式归纳（周期 4 全常数形——常数化配方第二次复用）：
     S1: x²−7z²=1（成员流·+1 单族）＋S2: y²−7w²=−3＋C: xy−7zw=−2＋
     G: yz−xw=−1（det 内芯）＋d7_norm_x/y/abs3＋d7_det（子族行列式 3＝锐度证书常元 3
     ——独立复算勘定·成员流在行 1 故取 B₁₂=3＝q₃＝CSV B 三路核对）＋d7_nonsquare
     （7 非完全平方 2²<7<3² 界矛盾·q_square_gap 使用位前提供）；
   §Q 终形装配层：Zpos 桥（pell_family Zpos_of/Zpos_of_pos 直迁调用零重证）＋d7yp/d7wp＋
     d7_member（=p_{4k+3}/q_{4k+3}＝√7 第 4k+3 收敛子＝x²−7y²=+1 子族·k=0 即 8/3）＋
     d7_family_sharp（族证书锐度：相邻成员距=3/(z_k z_{k+1}) 精确等号）＋d7_family_sep
     （分离证书：任意 a/b 到族成员距≥1/(b·z_k)·零前提位仅 gap≠0）＋d7_q_square_sharp
     （|member²−7|=1/z² 精确等号——q_square_gap 下界在族上精确实现）＋
     d7_q_square_gap_instance（实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 8/3·127/48·范数
     |127²−7·48²|=1·锐度 |8/3−127/48|=1/48=3/(3·48) 精确等号·Q 平方锐度 1/9·N 步
     (127,48)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS 34/34 双件
     （载体↔真收敛子 k≤20｜四件不变式 k≤20 全常数｜det=3 k≤19｜sharp k≤12｜sep
     全称网格·等号 10 例全 |az−xb|=1｜q_square_sharp k≤12｜7 非平方 c≤200｜
     x²≡−1 (mod 7) 无解＝+1 单族勘定｜x²−7y²=−1 无解 y≤2000｜Pell 锚
     (8,3)/(127,48)/(2024,765)｜CSV 核对 B₁₂=3=q₃=csvB）。
   依赖：S02_CauchyComplete（QeqT/QleT'/qeq_imp_qeqT）＋fib_machine（zabs 系/
     fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r 迁移件群）＋
     fib_qdomain（q_square_cross/q_square_gap）＋pell_family（Zpos_of/Zpos_of_pos）；
     Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面为在册同款先例形；证明体内
     构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典逻辑；定义面透明；
     主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d7_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d7pair/e7pair 对偶穿线＋d7x/y/z/w＋递归展开＋正性层     *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[14,3],[9,2]]·基 (p_3,p_2)=(8,5) *)
Fixpoint d7pair (n : nat) : Z * Z :=
  match n with
  | O => (8%Z, 5%Z)
  | S k => match d7pair k with pair x y => ((14 * x + 3 * y)%Z, (9 * x + 2 * y)%Z) end
  end.

(* Q 流：同系数 4 步递推·基 (q_3,q_2)=(3,2) *)
Fixpoint e7pair (n : nat) : Z * Z :=
  match n with
  | O => (3%Z, 2%Z)
  | S k => match e7pair k with pair x y => ((14 * x + 3 * y)%Z, (9 * x + 2 * y)%Z) end
  end.

Definition d7x (n : nat) : Z := fst (d7pair n).
Definition d7y (n : nat) : Z := snd (d7pair n).
Definition d7z (n : nat) : Z := fst (e7pair n).
Definition d7w (n : nat) : Z := snd (e7pair n).

Lemma d7x_0 : d7x 0 = 8%Z.
Proof. reflexivity. Qed.

Lemma d7y_0 : d7y 0 = 5%Z.
Proof. reflexivity. Qed.

Lemma d7z_0 : d7z 0 = 3%Z.
Proof. reflexivity. Qed.

Lemma d7w_0 : d7w 0 = 2%Z.
Proof. reflexivity. Qed.

Lemma d7pair_unfold : forall n : nat,
  d7pair (S n) = ((14 * fst (d7pair n) + 3 * snd (d7pair n))%Z,
                  (9 * fst (d7pair n) + 2 * snd (d7pair n))%Z).
Proof. intro n. cbn [d7pair]. destruct (d7pair n) as [a b]. reflexivity. Qed.

Lemma e7pair_unfold : forall n : nat,
  e7pair (S n) = ((14 * fst (e7pair n) + 3 * snd (e7pair n))%Z,
                  (9 * fst (e7pair n) + 2 * snd (e7pair n))%Z).
Proof. intro n. cbn [e7pair]. destruct (e7pair n) as [a b]. reflexivity. Qed.

Lemma d7x_rec : forall n, d7x (S n) = (14 * d7x n + 3 * d7y n)%Z.
Proof. intro n. unfold d7x, d7y. rewrite d7pair_unfold. reflexivity. Qed.

Lemma d7y_rec : forall n, d7y (S n) = (9 * d7x n + 2 * d7y n)%Z.
Proof. intro n. unfold d7x, d7y. rewrite d7pair_unfold. reflexivity. Qed.

Lemma d7z_rec : forall n, d7z (S n) = (14 * d7z n + 3 * d7w n)%Z.
Proof. intro n. unfold d7z, d7w. rewrite e7pair_unfold. reflexivity. Qed.

Lemma d7w_rec : forall n, d7w (S n) = (9 * d7z n + 2 * d7w n)%Z.
Proof. intro n. unfold d7z, d7w. rewrite e7pair_unfold. reflexivity. Qed.

(* 正性层：x/y/z/w 流全 ≥1（Q 分母位与 Zpos 桥守卫） *)
Lemma d7xy_ge1 : forall n, (1 <= d7x n)%Z /\ (1 <= d7y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d7x_0 | rewrite d7y_0]; lia.
  - split; rewrite ?d7x_rec, ?d7y_rec; lia.
Qed.

Lemma d7zw_ge : forall n, (1 <= d7z n)%Z /\ (0 <= d7w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d7z_0 | rewrite d7w_0]; lia.
  - split; rewrite ?d7z_rec, ?d7w_rec; lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d7_norm_quad 四件不变式（全常数）＋det＋nonsquare        *)
(* ============================================================ *)

(* 四件不变式归纳（周期 4 全常数形）：基 (8,5)/(3,2) 直接 ring；步例
   S1'=196·S1+84·C+9·S2｜S2'=81·S1+36·C+4·S2｜C'=126·S1+55·C+6·S2｜G'=G
   （det N=+1 自恒等）·ring 分解闭合 *)
Lemma d7_norm_quad : forall n : nat,
  (d7x n * d7x n - 7 * (d7z n * d7z n) = 1)%Z /\
  (d7y n * d7y n - 7 * (d7w n * d7w n) = (-3))%Z /\
  (d7x n * d7y n - 7 * (d7z n * d7w n) = (-2))%Z /\
  (d7y n * d7z n - d7x n * d7w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
    + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
    + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
    + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d7x_rec n), (d7z_rec n).
      transitivity ((196 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 84 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 9 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d7y_rec n), (d7w_rec n).
      transitivity ((81 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 36 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 4 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d7x_rec n), (d7y_rec n), (d7z_rec n), (d7w_rec n).
      transitivity ((126 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 55 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 6 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d7y_rec n), (d7z_rec n), (d7x_rec n), (d7w_rec n).
      transitivity ((d7y n * d7z n - d7x n * d7w n)%Z).
      * ring.
      * exact H4.
Qed.

(* 主语句一（成员流范数）：x²−7z² = 1（+1 单族·独立复算全域） *)
Theorem d7_norm_x : forall n : nat,
  (d7x n * d7x n - 7 * (d7z n * d7z n) = 1)%Z.
Proof. intro n. exact (proj1 (d7_norm_quad n)). Qed.

(* 主语句二（伴流范数）：y²−7w² = −3 *)
Theorem d7_norm_y : forall n : nat,
  (d7y n * d7y n - 7 * (d7w n * d7w n) = (-3))%Z.
Proof. intro n. exact (proj1 (proj2 (d7_norm_quad n))). Qed.

(* 族上整隙恰 3（伴流） *)
Theorem d7_norm_y_abs3 : forall n : nat,
  Z.abs (d7y n * d7y n - 7 * (d7w n * d7w n)) = 3%Z.
Proof. intro n. rewrite (d7_norm_y n). reflexivity. Qed.

(* 主语句三（子族行列式）：x_n·z_{n+1}−x_{n+1}·z_n = 3
   ——锐度证书常元 3（成员流行 1 的 B₁₂ 位＝q₃＝CSV 三路核对） *)
Theorem d7_det : forall n : nat,
  (d7x n * d7z (S n) - d7x (S n) * d7z n = 3)%Z.
Proof.
  intro n. rewrite (d7z_rec n), (d7x_rec n).
  transitivity ((- (3 * (d7y n * d7z n - d7x n * d7w n)))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d7_norm_quad n)))). reflexivity.
Qed.

(* 7 非完全平方（2²<7<3² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d7_nonsquare : forall c : Z, (7 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 7)%Z) by lia.
  assert (Hgt : (2 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 2 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d7_member＋双定理＋Q 平方锐度               *)
(* ============================================================ *)

Definition d7yp (k : nat) : positive := Zpos_of (d7x k).
Definition d7wp (k : nat) : positive := Zpos_of (d7z k).

Lemma d7yp_pos : forall k, Z.pos (d7yp k) = d7x k.
Proof.
  intro k. unfold d7yp. apply Zpos_of_pos.
  destruct (d7xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d7wp_pos : forall k, Z.pos (d7wp k) = d7z k.
Proof.
  intro k. unfold d7wp. apply Zpos_of_pos.
  destruct (d7zw_ge k) as [Hz _]. lia.
Qed.

(* 族成员：p_{4k+3}/q_{4k+3}＝√7 第 4k+3 收敛子（x²−7y²=+1 子族·k=0 即 8/3） *)
Definition d7_member (k : nat) : Q := (Z.pos (d7yp k) # d7wp k)%Q.

(* 族证书锐度（主定理一）：相邻族成员距 = 3/(z_k z_{k+1}) 精确等号
   ——d7_det 常元 3 等号实现（d3_family_sharp 同构·常元 1→3 周期 4 形） *)
Theorem d7_family_sharp : forall k : nat,
  QeqT (Qabs (d7_member k - d7_member (S k)))
       ((Z.pos 3) # (d7wp k * d7wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d7_member k - d7_member (S k))%Q ==
               ((Z.pos (d7yp k) * Z.pos (d7wp (S k))
                 - Z.pos (d7yp (S k)) * Z.pos (d7wp k))
                 # (d7wp k * d7wp (S k)))%Q).
  { unfold d7_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d7yp_pos k), (d7yp_pos (S k)).
    assert (Hd2 : (d7x k * Z.pos (d7wp (S k))
                   - d7x (S k) * Z.pos (d7wp k) = 3)%Z).
    { pose proof (d7_det k) as Hdet.
      rewrite <- (d7wp_pos (S k)), <- (d7wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* 族分离证书（主定理二）：任意 a/b 到族成员距 ≥ 1/(b·z_k)
   （d3_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d7_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d7z k - d7x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d7wp k)) # 1))
        (Qabs ((a # b)%Q - d7_member k)).
Proof.
  intros a b k Hk. unfold d7_member.
  assert (Hk2 : (a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b <> 0)%Z).
  { rewrite (d7wp_pos k), (d7yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b)
                  # (b * d7wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d7yp k) # d7wp k)%Q))
          (Qinv ((Z.pos (b * d7wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d7yp k) # d7wp k)%Q))
                   (Qabs ((a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b)
                           # (b * d7wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d7wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主定理三）：|member²−7| = 1/z² 精确等号
   ——q_square_gap 下界 1/b² 在 +1 子族上恰被实现（d3_q_square_sharp 同构·
   常数范数 1 免 powneg1 分案） *)
Theorem d7_q_square_sharp : forall k : nat,
  QeqT (Qabs (d7_member k * d7_member k - (7 # 1)%Q))
       (Qinv ((Z.pos (d7wp k * d7wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d7_member k * d7_member k - (7 # 1))%Q ==
               ((Z.pos (d7yp k) * Z.pos (d7yp k)
                 - 7 * (Z.pos (d7wp k) * Z.pos (d7wp k)))
                 # (d7wp k * d7wp k))%Q).
  { unfold d7_member. apply (q_square_cross (Z.pos (d7yp k)) 7 (d7wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d7yp_pos k).
    assert (Hn2 : (d7x k * d7x k
                   - 7 * (Z.pos (d7wp k) * Z.pos (d7wp k)) = 1)%Z).
    { pose proof (d7_norm_x k) as Hn.
      rewrite <- (d7wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d7wp k * d7wp k)) with (Z.pos 1 # d7wp k * d7wp k)%Q.
    change (Qinv (Z.pos (d7wp k * d7wp k) # 1)) with (1 # d7wp k * d7wp k)%Q.
    apply Qeq_refl.
Qed.

(* q_square_gap 实例使用（FIB3 主语句在 D=7 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d7_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d7wp k * d7wp k)) # 1))
        (Qabs (d7_member k * d7_member k - (7 # 1)%Q)).
Proof.
  intro k. unfold d7_member.
  apply (q_square_gap 7 (Z.pos (d7yp k)) (d7wp k)).
  - cbn. lia.
  - intro c. apply (d7_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d7x_rec.
Print Assumptions d7y_rec.
Print Assumptions d7z_rec.
Print Assumptions d7w_rec.
Print Assumptions d7xy_ge1.
Print Assumptions d7zw_ge.
Print Assumptions d7_norm_quad.
Print Assumptions d7_norm_x.
Print Assumptions d7_norm_y.
Print Assumptions d7_norm_y_abs3.
Print Assumptions d7_det.
Print Assumptions d7_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d7yp_pos.
Print Assumptions d7wp_pos.
Print Assumptions d7_family_sep.
Print Assumptions d7_family_sharp.
Print Assumptions d7_q_square_sharp.
Print Assumptions d7_q_square_gap_instance.

(* 数值锚一（族成员）：member 0 = p_3/q_3 = 8/3（x²−7y²=+1） *)
Lemma smoke_member_8_3 : (Qeq_bool (d7_member 0) (8 # 3)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员）：member 1 = p_7/q_7 = 127/48（x²−7y²=+1） *)
Lemma smoke_member_127_48 : (Qeq_bool (d7_member 1) (127 # 48)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|127²−7·48²| = 1（d7_norm_x 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d7x 1 * d7x 1 - 7 * (d7z 1 * d7z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|8/3−127/48| = 1/48 = 3/(3·48) 精确等号（d7_family_sharp 实例） *)
Lemma smoke_sharp_1_48 :
  (Qeq_bool (Qabs (d7_member 0 - d7_member 1))
            ((Z.pos 3) # (d7wp 0 * d7wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(8/3)²−7| = 1/9 = 1/3²（d7_q_square_sharp 实例） *)
Lemma smoke_qsq_1_9 :
  (Qeq_bool (Qabs (d7_member 0 * d7_member 0 - (7 # 1)%Q))
            (Qinv ((Z.pos (d7wp 0 * d7wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 127, z_1 = 48（p_7/q_7 载体值） *)
Lemma smoke_step_127_48 :
  (Z.eqb (d7x 1) 127%Z, Z.eqb (d7z 1) 48%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_8_3.
Print Assumptions smoke_member_127_48.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_48.
Print Assumptions smoke_qsq_1_9.
Print Assumptions smoke_step_127_48.

From Stdlib Require Import Extraction.
Separate Extraction d7pair e7pair d7x d7y d7z d7w d7yp d7wp
  d7_member d7_norm_y_abs3 d7_det d7_family_sep d7_family_sharp
  d7_q_square_sharp d7_q_square_gap_instance
  smoke_member_8_3 smoke_member_127_48 smoke_norm_1 smoke_sharp_1_48
  smoke_qsq_1_9 smoke_step_127_48.
