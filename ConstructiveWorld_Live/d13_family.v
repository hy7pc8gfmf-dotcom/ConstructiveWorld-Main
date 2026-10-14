(* 五字段指针｜使命：D=13 周期类收敛子族（一般周期类第一实例）——非折半线收敛子族
   从周期一类 D=m²+1（pell_family 已绿）向周期 ≥2 的一般周期类扩张首攻：
   D=13·√13=[3; overline{1,1,1,1,6}]·周期 5（Markoff 类）。
   周期 5 ⟹ 5 步矩阵 N=[[33,20],[5,3]]（det=−1）常系数化：
     (p_{5(k+1)},p_{5(k+1)−1})=N·(p_{5k},p_{5k−1})·q 流同系数——周期一类 2m 单步递推的
     周期类对偶＝5 步块递推（变系数 CF 状态机的免状态机化）。
   §C 载体层：d13pair/e13pair——对偶穿线（独立复算 ① 全域核对真收敛子）：
     (x_k,y_k)=(p_{5k},p_{5k−1}) 基 (3,1)｜(z_k,w_k)=(q_{5k},q_{5k−1}) 基 (1,0)｜
     5 步 N 递推 (33x+20y,5x+3y)＋d13x/d13y/d13z/d13w＋rec 展开件＋正性层（w 流 ≥1 守卫）；
   §N 范数层：d13_norm_quad 四件不变式归纳（周期类新形·对 FIB4 三件 tri 增一件）：
     S1: x²−13z²=4·powneg1(S n)（范数 ±4 与 ±1 交替·周期 10——周期一类 ±1 单交替的一般化）
     ＋S2: y²−13w²=powneg1 n（±1 子族·Pell 主线）＋C: xy−13zw=3·powneg1 n（交叉）＋
     G: yz−xw=powneg1 n（伴生·det 内芯）＋d13_norm_x/y/abs1＋d13_det（子族行列式
     5·powneg1 n＝锐度证书常元 5——det N=−1 的 B₂₁ 位）＋d13_nonsquare（13 非完全平方
     3²<13<4² 界矛盾·q_square_gap 使用位前提供）；
   §Q 终形装配层：Zpos 桥（pell_family Zpos_of/Zpos_of_pos 直迁调用零重证）＋d13yp/d13wp＋
     d13_member（=p_{5k+4}/q_{5k+4}＝√13 第 5k+4 收敛子＝x²−13y²=±1 子族）＋
     d13_family_sharp（族证书锐度：相邻子族成员距=5/(w_{k+1}w_{k+2}) 精确等号·det=±5 等号
     实现——周期类常元 5 对周期一类常元 1）＋d13_family_sep（分离证书：任意 a/b 到族成员
     距≥1/(b·w_{k+1})·零前提位仅 gap≠0·fib_family_sep/pell_family_sep 同构）＋
     d13_q_square_sharp（|member²−13|=1/w² 精确等号——FIB3 q_square_gap 下界 1/b² 在族上
     精确实现·pell_q_square_sharp 同构）＋d13_q_square_gap_instance（实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 18/5·649/180·范数
     |18²−13·5²|=1·锐度 |18/5−649/180|=1/180 精确等号·Q 平方锐度 1/25·N 步 (119,33)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS
   （载体↔真收敛子 n≤60｜四件不变式 n≤60｜det n≤60｜sharp k≤12｜sep 全称网格 24197 例
   等号 ⟺ |gap|=1｜q_square_sharp k≤12｜13 非平方 c≤200｜√13 周期 5 勘形＋Pell 锚
   (18,5)/(649,180)/(23382,6485)）。
   依赖：S02_CauchyComplete（QeqT/QleT'/qeq_imp_qeqT）＋fib_machine（powneg1 系/zabs 系/
     fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r 迁移件群）＋
     fib_qdomain（q_square_cross/q_square_gap）＋pell_family（Zpos_of/Zpos_of_pos/powneg1_2
     直迁）；Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面（·=·)%Z 为 B5/FIB/FIB2/FIB3/FIB4
     在册同款先例形；证明体内构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典
     逻辑；定义面透明；主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d13_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d13pair/e13pair 对偶穿线＋d13x/y/z/w＋递归展开＋正性层   *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[33,20],[5,3]]·基 (p_0,p_{−1})=(3,1) *)
Fixpoint d13pair (n : nat) : Z * Z :=
  match n with
  | O => (3%Z, 1%Z)
  | S k => match d13pair k with pair x y => ((33 * x + 20 * y)%Z, (5 * x + 3 * y)%Z) end
  end.

(* Q 流：同系数 5 步递推·基 (q_0,q_{−1})=(1,0) *)
Fixpoint e13pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | S k => match e13pair k with pair x y => ((33 * x + 20 * y)%Z, (5 * x + 3 * y)%Z) end
  end.

Definition d13x (n : nat) : Z := fst (d13pair n).
Definition d13y (n : nat) : Z := snd (d13pair n).
Definition d13z (n : nat) : Z := fst (e13pair n).
Definition d13w (n : nat) : Z := snd (e13pair n).

Lemma d13x_0 : d13x 0 = 3%Z.
Proof. reflexivity. Qed.

Lemma d13y_0 : d13y 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d13z_0 : d13z 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d13w_0 : d13w 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma d13pair_unfold : forall n : nat,
  d13pair (S n) = ((33 * fst (d13pair n) + 20 * snd (d13pair n))%Z,
                   (5 * fst (d13pair n) + 3 * snd (d13pair n))%Z).
Proof. intro n. cbn [d13pair]. destruct (d13pair n) as [a b]. reflexivity. Qed.

Lemma e13pair_unfold : forall n : nat,
  e13pair (S n) = ((33 * fst (e13pair n) + 20 * snd (e13pair n))%Z,
                   (5 * fst (e13pair n) + 3 * snd (e13pair n))%Z).
Proof. intro n. cbn [e13pair]. destruct (e13pair n) as [a b]. reflexivity. Qed.

Lemma d13x_rec : forall n, d13x (S n) = (33 * d13x n + 20 * d13y n)%Z.
Proof. intro n. unfold d13x, d13y. rewrite d13pair_unfold. reflexivity. Qed.

Lemma d13y_rec : forall n, d13y (S n) = (5 * d13x n + 3 * d13y n)%Z.
Proof. intro n. unfold d13x, d13y. rewrite d13pair_unfold. reflexivity. Qed.

Lemma d13z_rec : forall n, d13z (S n) = (33 * d13z n + 20 * d13w n)%Z.
Proof. intro n. unfold d13z, d13w. rewrite e13pair_unfold. reflexivity. Qed.

Lemma d13w_rec : forall n, d13w (S n) = (5 * d13z n + 3 * d13w n)%Z.
Proof. intro n. unfold d13z, d13w. rewrite e13pair_unfold. reflexivity. Qed.

(* 正性层：x/y 流全 ≥1；z 流 ≥1、w 流 ≥0 且 w_{n+1} ≥1（Q 分母位与 Zpos 桥守卫） *)
Lemma d13xy_ge1 : forall n, (1 <= d13x n)%Z /\ (1 <= d13y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d13x_0 | rewrite d13y_0]; lia.
  - split; rewrite ?d13x_rec, ?d13y_rec; lia.
Qed.

Lemma d13zw_ge : forall n, (1 <= d13z n)%Z /\ (0 <= d13w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d13z_0 | rewrite d13w_0]; lia.
  - split; rewrite ?d13z_rec, ?d13w_rec; lia.
Qed.

Lemma d13w_ge1 : forall n, (1 <= d13w (S n))%Z.
Proof.
  intro n. rewrite d13w_rec. destruct (d13zw_ge n) as [Hz Hw]. lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d13_norm_quad 四件不变式＋det＋nonsquare                *)
(* ============================================================ *)

(* 四件不变式归纳：S1（x 流范数 ±4）＋S2（y 流范数 ±1）＋C（交叉 3·±1）＋G（伴生 ±1）
   ——5 步 N 矩阵下 S1'=1089·S1+1320·C+400·S2｜S2'=25·S1+30·C+9·S2｜
   C'=165·S1+199·C+60·S2｜G'=−G·ring 分解＋powneg1 交替闭合 *)
Lemma d13_norm_quad : forall n : nat,
  (d13x n * d13x n - 13 * (d13z n * d13z n) = 4 * powneg1 (S n))%Z /\
  (d13y n * d13y n - 13 * (d13w n * d13w n) = powneg1 n)%Z /\
  (d13x n * d13y n - 13 * (d13z n * d13w n) = 3 * powneg1 n)%Z /\
  (d13y n * d13z n - d13x n * d13w n = powneg1 n)%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
  - split; [| split; [| split]].
    + rewrite (d13x_rec n), (d13z_rec n), powneg1_2.
      transitivity ((1089 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 1320 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 400 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d13y_rec n), (d13w_rec n).
      transitivity ((25 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 30 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 9 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d13x_rec n), (d13y_rec n), (d13z_rec n), (d13w_rec n).
      transitivity ((165 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 199 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 60 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d13y_rec n), (d13z_rec n), (d13x_rec n), (d13w_rec n).
      transitivity ((- (d13y n * d13z n - d13x n * d13w n))%Z).
      * ring.
      * rewrite H4. rewrite powneg1_S. reflexivity.
Qed.

(* 主语句一（x 流范数·周期类新形）：x²−13z² = ±4 交替（p_{5k} 位·复算①全域） *)
Theorem d13_norm_x : forall n : nat,
  (d13x n * d13x n - 13 * (d13z n * d13z n) = 4 * powneg1 (S n))%Z.
Proof. intro n. exact (proj1 (d13_norm_quad n)). Qed.

(* 主语句二（y 流范数·Pell 主线）：y²−13w² = ±1 交替（p_{5k−1} 位＝±1 子族） *)
Theorem d13_norm_y : forall n : nat,
  (d13y n * d13y n - 13 * (d13w n * d13w n) = powneg1 n)%Z.
Proof. intro n. exact (proj1 (proj2 (d13_norm_quad n))). Qed.

(* 族上整隙恰 1（y 流·gen_gapD_ne 下界 ≥1 在族上精确实现） *)
Theorem d13_norm_y_abs1 : forall n : nat,
  Z.abs (d13y n * d13y n - 13 * (d13w n * d13w n)) = 1%Z.
Proof. intro n. rewrite (d13_norm_y n). apply zabs_powneg1. Qed.

(* 主语句三（子族行列式）：y_n·w_{n+1}−y_{n+1}·w_n = 5·powneg1 n
   ——锐度证书常元 5（det N=−1 的 B₂₁ 位）·pell_det 的周期类对偶 *)
Theorem d13_det : forall n : nat,
  (d13y n * d13w (S n) - d13y (S n) * d13w n = 5 * powneg1 n)%Z.
Proof.
  intro n. rewrite (d13w_rec n), (d13y_rec n).
  transitivity ((5 * (d13y n * d13z n - d13x n * d13w n))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d13_norm_quad n)))). reflexivity.
Qed.

(* 13 非完全平方（3²<13<4² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d13_nonsquare : forall c : Z, (13 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 13)%Z) by lia.
  assert (Hgt : (3 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 3 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d13_member＋双定理＋Q 平方锐度               *)
(* ============================================================ *)

Definition d13yp (k : nat) : positive := Zpos_of (d13y (S k)).
Definition d13wp (k : nat) : positive := Zpos_of (d13w (S k)).

Lemma d13yp_pos : forall k, Z.pos (d13yp k) = d13y (S k).
Proof.
  intro k. unfold d13yp. apply Zpos_of_pos.
  destruct (d13xy_ge1 (S k)) as [_ Hy]. lia.
Qed.

Lemma d13wp_pos : forall k, Z.pos (d13wp k) = d13w (S k).
Proof.
  intro k. unfold d13wp. apply Zpos_of_pos.
  pose proof (d13w_ge1 k). lia.
Qed.

(* 族成员：p_{5k+4}/q_{5k+4}＝√13 第 5k+4 收敛子（x²−13y²=±1 子族·k=0 即 18/5） *)
Definition d13_member (k : nat) : Q := (Z.pos (d13yp k) # d13wp k)%Q.

(* 族证书锐度（主语句一）：相邻子族成员距 = 5/(w_{k+1}w_{k+2}) 精确等号
   ——d13_det ±5 等号实现（pell_family_sharp 同构·常元 1→5 周期类形） *)
Theorem d13_family_sharp : forall k : nat,
  QeqT (Qabs (d13_member k - d13_member (S k)))
       ((Z.pos 5) # (d13wp k * d13wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d13_member k - d13_member (S k))%Q ==
               ((Z.pos (d13yp k) * Z.pos (d13wp (S k))
                 - Z.pos (d13yp (S k)) * Z.pos (d13wp k))
                 # (d13wp k * d13wp (S k)))%Q).
  { unfold d13_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d13yp_pos k), (d13yp_pos (S k)).
    assert (Hd2 : (d13y (S k) * Z.pos (d13wp (S k))
                   - d13y (S (S k)) * Z.pos (d13wp k) = 5 * powneg1 (S k))%Z).
    { pose proof (d13_det (S k)) as Hdet.
      rewrite <- (d13wp_pos (S k)), <- (d13wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden].
    rewrite Z.abs_mul, zabs_powneg1. cbn [Z.abs]. ring.
Qed.

(* 族分离证书（主语句二）：任意 a/b 到族成员距 ≥ 1/(b·w_{k+1})
   （pell_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d13_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d13w (S k) - d13y (S k) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d13wp k)) # 1))
        (Qabs ((a # b)%Q - d13_member k)).
Proof.
  intros a b k Hk. unfold d13_member.
  assert (Hk2 : (a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b <> 0)%Z).
  { rewrite (d13wp_pos k), (d13yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b)
                  # (b * d13wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d13yp k) # d13wp k)%Q))
          (Qinv ((Z.pos (b * d13wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d13yp k) # d13wp k)%Q))
                   (Qabs ((a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b)
                           # (b * d13wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d13wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主语句三·FIB3 分离证书族侧确证）：|member²−13| = 1/w² 精确等号
   ——q_square_gap 下界 1/b² 在 ±1 子族上恰被实现（pell_q_square_sharp 同构） *)
Theorem d13_q_square_sharp : forall k : nat,
  QeqT (Qabs (d13_member k * d13_member k - (13 # 1)%Q))
       (Qinv ((Z.pos (d13wp k * d13wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d13_member k * d13_member k - (13 # 1))%Q ==
               ((Z.pos (d13yp k) * Z.pos (d13yp k)
                 - 13 * (Z.pos (d13wp k) * Z.pos (d13wp k)))
                 # (d13wp k * d13wp k))%Q).
  { unfold d13_member. apply (q_square_cross (Z.pos (d13yp k)) 13 (d13wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d13yp_pos k).
    assert (Hn2 : (d13y (S k) * d13y (S k)
                   - 13 * (Z.pos (d13wp k) * Z.pos (d13wp k)) = powneg1 (S k))%Z).
    { pose proof (d13_norm_y (S k)) as Hn.
      rewrite <- (d13wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    destruct (powneg1 (S k)) as [|p|p] eqn:E.
    + exfalso. pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # d13wp k * d13wp k)) with (Z.pos 1 # d13wp k * d13wp k)%Q.
      change (Qinv (Z.pos (d13wp k * d13wp k) # 1)) with (1 # d13wp k * d13wp k)%Q.
      apply Qeq_refl.
    + pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # d13wp k * d13wp k)) with (Z.pos 1 # d13wp k * d13wp k)%Q.
      change (Qinv (Z.pos (d13wp k * d13wp k) # 1)) with (1 # d13wp k * d13wp k)%Q.
      apply Qeq_refl.
Qed.

(* q_square_gap 实例调用（FIB3 主语句在 D=13 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d13_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d13wp k * d13wp k)) # 1))
        (Qabs (d13_member k * d13_member k - (13 # 1)%Q)).
Proof.
  intro k. unfold d13_member.
  apply (q_square_gap 13 (Z.pos (d13yp k)) (d13wp k)).
  - cbn. lia.
  - intro c. apply (d13_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d13x_rec.
Print Assumptions d13y_rec.
Print Assumptions d13z_rec.
Print Assumptions d13w_rec.
Print Assumptions d13xy_ge1.
Print Assumptions d13zw_ge.
Print Assumptions d13w_ge1.
Print Assumptions d13_norm_quad.
Print Assumptions d13_norm_x.
Print Assumptions d13_norm_y.
Print Assumptions d13_norm_y_abs1.
Print Assumptions d13_det.
Print Assumptions d13_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d13yp_pos.
Print Assumptions d13wp_pos.
Print Assumptions d13_family_sep.
Print Assumptions d13_family_sharp.
Print Assumptions d13_q_square_sharp.
Print Assumptions d13_q_square_gap_instance.

(* 数值锚一（族成员）：member 0 = p_4/q_4 = 18/5（x²−13y²=−1） *)
Lemma smoke_member_18_5 : (Qeq_bool (d13_member 0) (18 # 5)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员）：member 1 = p_9/q_9 = 649/180（x²−13y²=+1） *)
Lemma smoke_member_649_180 : (Qeq_bool (d13_member 1) (649 # 180)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|18²−13·5²| = 1（d13_norm_y_abs1 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d13y 1 * d13y 1 - 13 * (d13w 1 * d13w 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|18/5−649/180| = 1/180 = 5/(5·180) 精确等号（d13_family_sharp 实例） *)
Lemma smoke_sharp_1_180 :
  (Qeq_bool (Qabs (d13_member 0 - d13_member 1))
            ((Z.pos 5) # (d13wp 0 * d13wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(18/5)²−13| = 1/25（d13_q_square_sharp 实例·FIB3 证书族侧等号） *)
Lemma smoke_qsq_1_25 :
  (Qeq_bool (Qabs (d13_member 0 * d13_member 0 - (13 # 1)%Q))
            (Qinv ((Z.pos (d13wp 0 * d13wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 119, z_1 = 33（p_5/q_5 载体值） *)
Lemma smoke_step_119_33 :
  (Z.eqb (d13x 1) 119%Z, Z.eqb (d13z 1) 33%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_18_5.
Print Assumptions smoke_member_649_180.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_180.
Print Assumptions smoke_qsq_1_25.
Print Assumptions smoke_step_119_33.

From Stdlib Require Import Extraction.
Separate Extraction d13pair e13pair d13x d13y d13z d13w d13yp d13wp
  d13_member d13_norm_y_abs1 d13_det d13_family_sep d13_family_sharp
  d13_q_square_sharp d13_q_square_gap_instance
  smoke_member_18_5 smoke_member_649_180 smoke_norm_1 smoke_sharp_1_180
  smoke_qsq_1_25 smoke_step_119_33.
