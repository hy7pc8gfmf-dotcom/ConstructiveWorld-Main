(* 五字段指针｜使命：D=14 周期 4 类收敛子族（谱线 T=4 档补全第二件）——非折半线
   收敛子族谱线 T=4 档第二件：D=14·√14=[3; overline{1,2,1,6}]·周期 4。
   周期 4 ⟹ 4 步块矩阵 N=T(1)·T(2)·T(1)·T(6)=[[27,4],[20,3]]（det=+1＝(−1)^4）常系数化
   （独立复算 CF 发生器 n≤100 全域核对裁定）：
     (p_{4(k+1)+3},p_{4k+3})=N·(p_{4k+3},p_{4k+2})——免状态机化的 T=4 档。
   子族谱判据（独立复算勘定·CSV 同余判据列核对）：x²≡−1 (mod 14) 无解（mod 7 已无解：
   剩余 0..6 平方 {0,1,2,4} 不含 6）⟹ 负 Pell x²−14y²=−1 无解 ⟹ +1 单族（T 偶常数形档
   ·d3/d6 母版同构）——成员流在 4k+3 位全泳范数 +1（见证 15²=225≡1 (mod 14)）。
   §C 载体层：d14pair/e14pair——对偶穿线：(x_k,y_k)=(p_{4k+3},p_{4k+2}) 基 (15,11)｜
     (z_k,w_k)=(q_{4k+3},q_{4k+2}) 基 (4,3)｜4 步 N 递推 (27x+4y,20x+3y)＋d14x/d14y/
     d14z/d14w＋rec 展开件＋正性层；
   §N 范数层：d14_norm_quad 四件不变式归纳（周期 4 全常数形——常数化配方复用）：
     S1: x²−14z²=1（成员流·+1 单族）＋S2: y²−14w²=−5＋C: xy−14zw=−3＋
     G: yz−xw=−1（det 内芯）＋d14_norm_x/y/abs5＋d14_det（子族行列式 4＝锐度证书常元 4
     ——独立复算勘定·成员流在行 1 故取 B₁₂=4＝q₃＝CSV B 三路核对）＋d14_nonsquare
     （14 非完全平方 3²<14<4² 界矛盾·q_square_gap 使用位前提供）；
   §Q 终形装配层：Zpos 桥（pell_family Zpos_of/Zpos_of_pos 直迁调用零重证）＋d14yp/d14wp＋
     d14_member（=p_{4k+3}/q_{4k+3}＝√14 第 4k+3 收敛子＝x²−14y²=+1 子族·k=0 即 15/4）＋
     d14_family_sharp（族证书锐度：相邻成员距=4/(z_k z_{k+1}) 精确等号）＋d14_family_sep
     （分离证书：任意 a/b 到族成员距≥1/(b·z_k)·零前提位仅 gap≠0）＋d14_q_square_sharp
     （|member²−14|=1/z² 精确等号——q_square_gap 下界在族上精确实现）＋
     d14_q_square_gap_instance（实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 15/4·449/120·范数
     |449²−14·120²|=1·锐度 |15/4−449/120|=1/120=4/(4·120) 精确等号·Q 平方锐度 1/16·
     N 步 (449,120)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS 34/34 双件
     （载体↔真收敛子 k≤20｜四件不变式 k≤20 全常数｜det=4 k≤19｜sharp k≤12｜sep
     全称网格·等号 5 例全 |az−xb|=1｜q_square_sharp k≤12｜14 非平方 c≤200｜
     x²≡−1 (mod 14) 无解＝+1 单族勘定｜x²−14y²=−1 无解 y≤2000｜Pell 锚
     (15,4)/(449,120)/(13455,3596)｜CSV 核对 B₁₂=4=q₃=csvB）。
   依赖：S02_CauchyComplete（QeqT/QleT'/qeq_imp_qeqT）＋fib_machine（zabs 系/
     fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r 迁移件群）＋
     fib_qdomain（q_square_cross/q_square_gap）＋pell_family（Zpos_of/Zpos_of_pos）；
     Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面为在册同款先例形；证明体内
     构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典逻辑；定义面透明；
     主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d14_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d14pair/e14pair 对偶穿线＋d14x/y/z/w＋递归展开＋正性层   *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[27,4],[20,3]]·基 (p_3,p_2)=(15,11) *)
Fixpoint d14pair (n : nat) : Z * Z :=
  match n with
  | O => (15%Z, 11%Z)
  | S k => match d14pair k with pair x y => ((27 * x + 4 * y)%Z, (20 * x + 3 * y)%Z) end
  end.

(* Q 流：同系数 4 步递推·基 (q_3,q_2)=(4,3) *)
Fixpoint e14pair (n : nat) : Z * Z :=
  match n with
  | O => (4%Z, 3%Z)
  | S k => match e14pair k with pair x y => ((27 * x + 4 * y)%Z, (20 * x + 3 * y)%Z) end
  end.

Definition d14x (n : nat) : Z := fst (d14pair n).
Definition d14y (n : nat) : Z := snd (d14pair n).
Definition d14z (n : nat) : Z := fst (e14pair n).
Definition d14w (n : nat) : Z := snd (e14pair n).

Lemma d14x_0 : d14x 0 = 15%Z.
Proof. reflexivity. Qed.

Lemma d14y_0 : d14y 0 = 11%Z.
Proof. reflexivity. Qed.

Lemma d14z_0 : d14z 0 = 4%Z.
Proof. reflexivity. Qed.

Lemma d14w_0 : d14w 0 = 3%Z.
Proof. reflexivity. Qed.

Lemma d14pair_unfold : forall n : nat,
  d14pair (S n) = ((27 * fst (d14pair n) + 4 * snd (d14pair n))%Z,
                   (20 * fst (d14pair n) + 3 * snd (d14pair n))%Z).
Proof. intro n. cbn [d14pair]. destruct (d14pair n) as [a b]. reflexivity. Qed.

Lemma e14pair_unfold : forall n : nat,
  e14pair (S n) = ((27 * fst (e14pair n) + 4 * snd (e14pair n))%Z,
                   (20 * fst (e14pair n) + 3 * snd (e14pair n))%Z).
Proof. intro n. cbn [e14pair]. destruct (e14pair n) as [a b]. reflexivity. Qed.

Lemma d14x_rec : forall n, d14x (S n) = (27 * d14x n + 4 * d14y n)%Z.
Proof. intro n. unfold d14x, d14y. rewrite d14pair_unfold. reflexivity. Qed.

Lemma d14y_rec : forall n, d14y (S n) = (20 * d14x n + 3 * d14y n)%Z.
Proof. intro n. unfold d14x, d14y. rewrite d14pair_unfold. reflexivity. Qed.

Lemma d14z_rec : forall n, d14z (S n) = (27 * d14z n + 4 * d14w n)%Z.
Proof. intro n. unfold d14z, d14w. rewrite e14pair_unfold. reflexivity. Qed.

Lemma d14w_rec : forall n, d14w (S n) = (20 * d14z n + 3 * d14w n)%Z.
Proof. intro n. unfold d14z, d14w. rewrite e14pair_unfold. reflexivity. Qed.

(* 正性层：x/y/z/w 流全 ≥1（Q 分母位与 Zpos 桥守卫） *)
Lemma d14xy_ge1 : forall n, (1 <= d14x n)%Z /\ (1 <= d14y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d14x_0 | rewrite d14y_0]; lia.
  - split; rewrite ?d14x_rec, ?d14y_rec; lia.
Qed.

Lemma d14zw_ge : forall n, (1 <= d14z n)%Z /\ (0 <= d14w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d14z_0 | rewrite d14w_0]; lia.
  - split; rewrite ?d14z_rec, ?d14w_rec; lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d14_norm_quad 四件不变式（全常数）＋det＋nonsquare       *)
(* ============================================================ *)

(* 四件不变式归纳（周期 4 全常数形）：基 (15,11)/(4,3) 直接 ring；步例
   S1'=729·S1+216·C+16·S2｜S2'=400·S1+120·C+9·S2｜C'=540·S1+161·C+12·S2｜G'=G
   （det N=+1 自恒等）·ring 分解闭合 *)
Lemma d14_norm_quad : forall n : nat,
  (d14x n * d14x n - 14 * (d14z n * d14z n) = 1)%Z /\
  (d14y n * d14y n - 14 * (d14w n * d14w n) = (-5))%Z /\
  (d14x n * d14y n - 14 * (d14z n * d14w n) = (-3))%Z /\
  (d14y n * d14z n - d14x n * d14w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d14x_rec n), (d14z_rec n).
      transitivity ((729 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 216 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 16 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14y_rec n), (d14w_rec n).
      transitivity ((400 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 120 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 9 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14x_rec n), (d14y_rec n), (d14z_rec n), (d14w_rec n).
      transitivity ((540 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 161 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 12 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14y_rec n), (d14z_rec n), (d14x_rec n), (d14w_rec n).
      transitivity ((d14y n * d14z n - d14x n * d14w n)%Z).
      * ring.
      * exact H4.
Qed.

(* 主语句一（成员流范数）：x²−14z² = 1（+1 单族·独立复算全域） *)
Theorem d14_norm_x : forall n : nat,
  (d14x n * d14x n - 14 * (d14z n * d14z n) = 1)%Z.
Proof. intro n. exact (proj1 (d14_norm_quad n)). Qed.

(* 主语句二（伴流范数）：y²−14w² = −5 *)
Theorem d14_norm_y : forall n : nat,
  (d14y n * d14y n - 14 * (d14w n * d14w n) = (-5))%Z.
Proof. intro n. exact (proj1 (proj2 (d14_norm_quad n))). Qed.

(* 族上整隙恰 5（伴流） *)
Theorem d14_norm_y_abs5 : forall n : nat,
  Z.abs (d14y n * d14y n - 14 * (d14w n * d14w n)) = 5%Z.
Proof. intro n. rewrite (d14_norm_y n). reflexivity. Qed.

(* 主语句三（子族行列式）：x_n·z_{n+1}−x_{n+1}·z_n = 4
   ——锐度证书常元 4（成员流行 1 的 B₁₂ 位＝q₃＝CSV 三路核对） *)
Theorem d14_det : forall n : nat,
  (d14x n * d14z (S n) - d14x (S n) * d14z n = 4)%Z.
Proof.
  intro n. rewrite (d14z_rec n), (d14x_rec n).
  transitivity ((- (4 * (d14y n * d14z n - d14x n * d14w n)))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d14_norm_quad n)))). reflexivity.
Qed.

(* 14 非完全平方（3²<14<4² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d14_nonsquare : forall c : Z, (14 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 14)%Z) by lia.
  assert (Hgt : (3 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 3 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d14_member＋双定理＋Q 平方锐度              *)
(* ============================================================ *)

Definition d14yp (k : nat) : positive := Zpos_of (d14x k).
Definition d14wp (k : nat) : positive := Zpos_of (d14z k).

Lemma d14yp_pos : forall k, Z.pos (d14yp k) = d14x k.
Proof.
  intro k. unfold d14yp. apply Zpos_of_pos.
  destruct (d14xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d14wp_pos : forall k, Z.pos (d14wp k) = d14z k.
Proof.
  intro k. unfold d14wp. apply Zpos_of_pos.
  destruct (d14zw_ge k) as [Hz _]. lia.
Qed.

(* 族成员：p_{4k+3}/q_{4k+3}＝√14 第 4k+3 收敛子（x²−14y²=+1 子族·k=0 即 15/4） *)
Definition d14_member (k : nat) : Q := (Z.pos (d14yp k) # d14wp k)%Q.

(* 族证书锐度（主定理一）：相邻族成员距 = 4/(z_k z_{k+1}) 精确等号
   ——d14_det 常元 4 等号实现（d3_family_sharp 同构·常元 1→4 周期 4 形） *)
Theorem d14_family_sharp : forall k : nat,
  QeqT (Qabs (d14_member k - d14_member (S k)))
       ((Z.pos 4) # (d14wp k * d14wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d14_member k - d14_member (S k))%Q ==
               ((Z.pos (d14yp k) * Z.pos (d14wp (S k))
                 - Z.pos (d14yp (S k)) * Z.pos (d14wp k))
                 # (d14wp k * d14wp (S k)))%Q).
  { unfold d14_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d14yp_pos k), (d14yp_pos (S k)).
    assert (Hd2 : (d14x k * Z.pos (d14wp (S k))
                   - d14x (S k) * Z.pos (d14wp k) = 4)%Z).
    { pose proof (d14_det k) as Hdet.
      rewrite <- (d14wp_pos (S k)), <- (d14wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* 族分离证书（主定理二）：任意 a/b 到族成员距 ≥ 1/(b·z_k)
   （d3_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d14_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d14z k - d14x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d14wp k)) # 1))
        (Qabs ((a # b)%Q - d14_member k)).
Proof.
  intros a b k Hk. unfold d14_member.
  assert (Hk2 : (a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b <> 0)%Z).
  { rewrite (d14wp_pos k), (d14yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b)
                  # (b * d14wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d14yp k) # d14wp k)%Q))
          (Qinv ((Z.pos (b * d14wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d14yp k) # d14wp k)%Q))
                   (Qabs ((a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b)
                           # (b * d14wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d14wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主定理三）：|member²−14| = 1/z² 精确等号
   ——q_square_gap 下界 1/b² 在 +1 子族上恰被实现（d3_q_square_sharp 同构·
   常数范数 1 免 powneg1 分案） *)
Theorem d14_q_square_sharp : forall k : nat,
  QeqT (Qabs (d14_member k * d14_member k - (14 # 1)%Q))
       (Qinv ((Z.pos (d14wp k * d14wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d14_member k * d14_member k - (14 # 1))%Q ==
               ((Z.pos (d14yp k) * Z.pos (d14yp k)
                 - 14 * (Z.pos (d14wp k) * Z.pos (d14wp k)))
                 # (d14wp k * d14wp k))%Q).
  { unfold d14_member. apply (q_square_cross (Z.pos (d14yp k)) 14 (d14wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d14yp_pos k).
    assert (Hn2 : (d14x k * d14x k
                   - 14 * (Z.pos (d14wp k) * Z.pos (d14wp k)) = 1)%Z).
    { pose proof (d14_norm_x k) as Hn.
      rewrite <- (d14wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d14wp k * d14wp k)) with (Z.pos 1 # d14wp k * d14wp k)%Q.
    change (Qinv (Z.pos (d14wp k * d14wp k) # 1)) with (1 # d14wp k * d14wp k)%Q.
    apply Qeq_refl.
Qed.

(* q_square_gap 实例使用（FIB3 主语句在 D=14 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d14_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d14wp k * d14wp k)) # 1))
        (Qabs (d14_member k * d14_member k - (14 # 1)%Q)).
Proof.
  intro k. unfold d14_member.
  apply (q_square_gap 14 (Z.pos (d14yp k)) (d14wp k)).
  - cbn. lia.
  - intro c. apply (d14_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d14x_rec.
Print Assumptions d14y_rec.
Print Assumptions d14z_rec.
Print Assumptions d14w_rec.
Print Assumptions d14xy_ge1.
Print Assumptions d14zw_ge.
Print Assumptions d14_norm_quad.
Print Assumptions d14_norm_x.
Print Assumptions d14_norm_y.
Print Assumptions d14_norm_y_abs5.
Print Assumptions d14_det.
Print Assumptions d14_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d14yp_pos.
Print Assumptions d14wp_pos.
Print Assumptions d14_family_sep.
Print Assumptions d14_family_sharp.
Print Assumptions d14_q_square_sharp.
Print Assumptions d14_q_square_gap_instance.

(* 数值锚一（族成员）：member 0 = p_3/q_3 = 15/4（x²−14y²=+1） *)
Lemma smoke_member_15_4 : (Qeq_bool (d14_member 0) (15 # 4)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员）：member 1 = p_7/q_7 = 449/120（x²−14y²=+1） *)
Lemma smoke_member_449_120 : (Qeq_bool (d14_member 1) (449 # 120)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|449²−14·120²| = 1（d14_norm_x 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d14x 1 * d14x 1 - 14 * (d14z 1 * d14z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|15/4−449/120| = 1/120 = 4/(4·120) 精确等号（d14_family_sharp 实例） *)
Lemma smoke_sharp_1_120 :
  (Qeq_bool (Qabs (d14_member 0 - d14_member 1))
            ((Z.pos 4) # (d14wp 0 * d14wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(15/4)²−14| = 1/16 = 1/4²（d14_q_square_sharp 实例） *)
Lemma smoke_qsq_1_16 :
  (Qeq_bool (Qabs (d14_member 0 * d14_member 0 - (14 # 1)%Q))
            (Qinv ((Z.pos (d14wp 0 * d14wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 449, z_1 = 120（p_7/q_7 载体值） *)
Lemma smoke_step_449_120 :
  (Z.eqb (d14x 1) 449%Z, Z.eqb (d14z 1) 120%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_15_4.
Print Assumptions smoke_member_449_120.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_120.
Print Assumptions smoke_qsq_1_16.
Print Assumptions smoke_step_449_120.

From Stdlib Require Import Extraction.
Separate Extraction d14pair e14pair d14x d14y d14z d14w d14yp d14wp
  d14_member d14_norm_y_abs5 d14_det d14_family_sep d14_family_sharp
  d14_q_square_sharp d14_q_square_gap_instance
  smoke_member_15_4 smoke_member_449_120 smoke_norm_1 smoke_sharp_1_120
  smoke_qsq_1_16 smoke_step_449_120.
