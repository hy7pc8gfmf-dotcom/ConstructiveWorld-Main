(* 五字段指针｜使命：D=41 周期 3 双族收敛子族（谱线延伸第一实例）——非折半线
   收敛子族从周期 2 类（d3/d6 已绿）与周期 5 类（d13 已绿）向周期 3 类扩张：
   D=41·√41=[6; overline{2,2,12}]·周期 3（B=5·首成员 32/5·次成员
   2049/320·CSV D=41 行锐度常元独立复算对表在卷）。
   双族判定：x²≡−1 (mod 41) 可解（见证 9·32）⟹ 负 Pell 可解 ⟹ 族成员在
   3k+2 位 ±1 交替（member 0 范数 −1·member 1 范数 +1·独立复算全泳交替实测）——
   d13 同款双族形（d3/d6 为 +1 单族·子族谱判据在册）。
   周期 3 ⟹ 3 步矩阵 N=[[62,25],[5,2]]（det=−1）常系数化：
     (p_{3(k+1)},p_{3(k+1)−1})=N·(p_{3k},p_{3k−1})·q 流同系数——d13 五步块的
     周期 3 版（免状态机化配方第三实例）。
   §C 载体层：d41pair/e41pair——对偶穿线（独立复算全域核对真收敛子 k≤20）：
     (x_k,y_k)=(p_{3k},p_{3k−1}) 基 (6,1)｜(z_k,w_k)=
     (q_{3k},q_{3k−1}) 基 (1,0)｜3 步 N 递推 (62x+25y,5x+2y)＋d41x/y/z/w＋
     rec 展开件＋正性层（w 流 ≥1 守卫）；
   §N 范数层：d41_norm_quad 四件不变式归纳（d13 交替形同构·周期 3·幅 5/1/6/1）：
     S1: x²−41z²=5·powneg1(S n)＋S2: y²−41w²=powneg1 n（±1 子族主线）＋
     C: xy−41zw=6·powneg1 n（交叉）＋G: yz−xw=powneg1 n（伴生·det 内芯）
     ——3 步 N 下 S1'=3844·S1+3100·C+625·S2｜S2'=25·S1+20·C+4·S2｜
     C'=310·S1+249·C+50·S2｜G'=−G·ring 分解＋powneg1 交替闭合＋
     d41_norm_x/y/abs1＋d41_det（子族行列式 5·powneg1 n＝锐度证书常元 5——
     det N=−1 的 B₂₁ 位·与 CSV B=5 三路核对）＋d41_nonsquare（41 非完全平方
     6²<41<7² 界矛盾·q_square_gap 使用位前提供）；
   §Q 终形装配层：Zpos 桥（pell_family Zpos_of/Zpos_of_pos 直迁调用零重证）＋
     d41yp/d41wp＋d41_member（=p_{3k+2}/q_{3k+2}＝√41 第 3k+2 收敛子＝
     x²−41y²=±1 双族·k=0 即 32/5 范数 −1·k=1 即 2049/320 范数 +1）＋
     d41_family_sharp（族证书锐度：相邻族成员距=5/(w_{k+1}w_{k+2}) 精确等号
     ·det=±5 等号实现——d13_family_sharp 同构）＋d41_family_sep（分离证书：
     任意 a/b 到族成员距≥1/(b·w_{k+1})·零前提位仅 gap≠0·d13_family_sep
     同构）＋d41_q_square_sharp（|member²−41|=1/w² 精确等号——FIB3
     q_square_gap 下界在 ±1 双族上精确实现）＋d41_q_square_gap_instance
     （实例调用）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（族成员 32/5·
     2049/320·范数 |32²−41·5²|=1·锐度 |32/5−2049/320|=1/320 精确等号·
     Q 平方锐度 1/25·N 步 (397,62)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS 22/22
     （√41=[6;overline{2,2,12}] 周期 3 勘形｜载体↔真收敛子 k≤20 全域核对｜
     四件不变式 k≤20｜det k≤19｜双族 ±1 交替全泳｜sharp k≤12 Fraction 精确｜
     sep 全称网格 8099 例·等号 2 例全 |gap|=1｜q_square_sharp k≤12｜
     41 非平方 c≤200｜x²≡−1 (mod 41) 见证 9·32｜
     1/(2√41)∈(1/14,1/12) 整数判定｜CSV 锚 32/5·2049/320·B=5 三路核对）。
   依赖：S02_CauchyComplete（QeqT/QleT'/qeq_imp_qeqT）＋fib_machine（powneg1 系/
     zabs 系/fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r
     迁移件群）＋fib_qdomain（q_square_cross/q_square_gap）＋pell_family
     （Zpos_of/Zpos_of_pos/powneg1_2 直迁）；Stdlib ZArith、Arith、Bool、
     Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面（·=·)%Z 为 B5/FIB 系
     在册同款先例形；证明体内构造性 Prop 推导合法；零承认、零 Abort、零全局
     假设、零经典逻辑；定义面透明；主语句（family_sep/sharp/q_square_sharp）
     结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" d41_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：d41pair/e41pair 对偶穿线＋d41x/y/z/w＋递归展开＋正性层   *)
(* ============================================================ *)

(* X 流：(x_{k+1},y_{k+1})=N·(x_k,y_k)·N=[[62,25],[5,2]]·基 (p_0,p_{−1})=(6,1) *)
Fixpoint d41pair (n : nat) : Z * Z :=
  match n with
  | O => (6%Z, 1%Z)
  | S k => match d41pair k with pair x y => ((62 * x + 25 * y)%Z, (5 * x + 2 * y)%Z) end
  end.

(* Q 流：同系数 3 步递推·基 (q_0,q_{−1})=(1,0) *)
Fixpoint e41pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | S k => match e41pair k with pair x y => ((62 * x + 25 * y)%Z, (5 * x + 2 * y)%Z) end
  end.

Definition d41x (n : nat) : Z := fst (d41pair n).
Definition d41y (n : nat) : Z := snd (d41pair n).
Definition d41z (n : nat) : Z := fst (e41pair n).
Definition d41w (n : nat) : Z := snd (e41pair n).

Lemma d41x_0 : d41x 0 = 6%Z.
Proof. reflexivity. Qed.

Lemma d41y_0 : d41y 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d41z_0 : d41z 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d41w_0 : d41w 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma d41pair_unfold : forall n : nat,
  d41pair (S n) = ((62 * fst (d41pair n) + 25 * snd (d41pair n))%Z,
                   (5 * fst (d41pair n) + 2 * snd (d41pair n))%Z).
Proof. intro n. cbn [d41pair]. destruct (d41pair n) as [a b]. reflexivity. Qed.

Lemma e41pair_unfold : forall n : nat,
  e41pair (S n) = ((62 * fst (e41pair n) + 25 * snd (e41pair n))%Z,
                   (5 * fst (e41pair n) + 2 * snd (e41pair n))%Z).
Proof. intro n. cbn [e41pair]. destruct (e41pair n) as [a b]. reflexivity. Qed.

Lemma d41x_rec : forall n, d41x (S n) = (62 * d41x n + 25 * d41y n)%Z.
Proof. intro n. unfold d41x, d41y. rewrite d41pair_unfold. reflexivity. Qed.

Lemma d41y_rec : forall n, d41y (S n) = (5 * d41x n + 2 * d41y n)%Z.
Proof. intro n. unfold d41x, d41y. rewrite d41pair_unfold. reflexivity. Qed.

Lemma d41z_rec : forall n, d41z (S n) = (62 * d41z n + 25 * d41w n)%Z.
Proof. intro n. unfold d41z, d41w. rewrite e41pair_unfold. reflexivity. Qed.

Lemma d41w_rec : forall n, d41w (S n) = (5 * d41z n + 2 * d41w n)%Z.
Proof. intro n. unfold d41z, d41w. rewrite e41pair_unfold. reflexivity. Qed.

(* 正性层：x/y 流全 ≥1；z 流 ≥1、w 流 ≥0 且 w_{n+1} ≥1（Q 分母位与 Zpos 桥守卫） *)
Lemma d41xy_ge1 : forall n, (1 <= d41x n)%Z /\ (1 <= d41y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d41x_0 | rewrite d41y_0]; lia.
  - split; rewrite ?d41x_rec, ?d41y_rec; lia.
Qed.

Lemma d41zw_ge : forall n, (1 <= d41z n)%Z /\ (0 <= d41w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d41z_0 | rewrite d41w_0]; lia.
  - split; rewrite ?d41z_rec, ?d41w_rec; lia.
Qed.

Lemma d41w_ge1 : forall n, (1 <= d41w (S n))%Z.
Proof.
  intro n. rewrite d41w_rec. destruct (d41zw_ge n) as [Hz Hw]. lia.
Qed.

(* ============================================================ *)
(* §N 范数层：d41_norm_quad 四件不变式＋det＋nonsquare                *)
(* ============================================================ *)

(* 四件不变式归纳：S1（x 流范数 5·±1）＋S2（y 流范数 ±1）＋C（交叉 6·±1）＋
   G（伴生 ±1）——3 步 N 矩阵下 S1'=3844·S1+3100·C+625·S2｜S2'=25·S1+20·C+4·S2｜
   C'=310·S1+249·C+50·S2｜G'=−G·ring 分解＋powneg1 交替闭合 *)
Lemma d41_norm_quad : forall n : nat,
  (d41x n * d41x n - 41 * (d41z n * d41z n) = 5 * powneg1 (S n))%Z /\
  (d41y n * d41y n - 41 * (d41w n * d41w n) = powneg1 n)%Z /\
  (d41x n * d41y n - 41 * (d41z n * d41w n) = 6 * powneg1 n)%Z /\
  (d41y n * d41z n - d41x n * d41w n = powneg1 n)%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
  - split; [| split; [| split]].
    + rewrite (d41x_rec n), (d41z_rec n), powneg1_2.
      transitivity ((3844 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 3100 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 625 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d41y_rec n), (d41w_rec n).
      transitivity ((25 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 20 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 4 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d41x_rec n), (d41y_rec n), (d41z_rec n), (d41w_rec n).
      transitivity ((310 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 249 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 50 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. rewrite powneg1_S. ring.
    + rewrite (d41y_rec n), (d41z_rec n), (d41x_rec n), (d41w_rec n).
      transitivity ((- (d41y n * d41z n - d41x n * d41w n))%Z).
      * ring.
      * rewrite H4. rewrite powneg1_S. reflexivity.
Qed.

(* 主语句一（x 流范数·周期类交替形）：x²−41z² = 5·±1 交替（p_{3k} 位·独立复算④全域） *)
Theorem d41_norm_x : forall n : nat,
  (d41x n * d41x n - 41 * (d41z n * d41z n) = 5 * powneg1 (S n))%Z.
Proof. intro n. exact (proj1 (d41_norm_quad n)). Qed.

(* 主语句二（y 流范数·Pell 主线）：y²−41w² = ±1 交替（p_{3k−1} 位＝±1 双族） *)
Theorem d41_norm_y : forall n : nat,
  (d41y n * d41y n - 41 * (d41w n * d41w n) = powneg1 n)%Z.
Proof. intro n. exact (proj1 (proj2 (d41_norm_quad n))). Qed.

(* 族上整隙恰 1（y 流·gen_gapD_ne 下界 ≥1 在族上精确实现） *)
Theorem d41_norm_y_abs1 : forall n : nat,
  Z.abs (d41y n * d41y n - 41 * (d41w n * d41w n)) = 1%Z.
Proof. intro n. rewrite (d41_norm_y n). apply zabs_powneg1. Qed.

(* 主语句三（子族行列式）：y_n·w_{n+1}−y_{n+1}·w_n = 5·powneg1 n
   ——锐度证书常元 5（det N=−1 的 B₂₁ 位·CSV D=41 行 B=5 三路核对） *)
Theorem d41_det : forall n : nat,
  (d41y n * d41w (S n) - d41y (S n) * d41w n = 5 * powneg1 n)%Z.
Proof.
  intro n. rewrite (d41w_rec n), (d41y_rec n).
  transitivity ((5 * (d41y n * d41z n - d41x n * d41w n))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d41_norm_quad n)))). reflexivity.
Qed.

(* 41 非完全平方（6²<41<7² 界矛盾——q_square_gap 使用位前提供） *)
Lemma d41_nonsquare : forall c : Z, (41 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 41)%Z) by lia.
  assert (Hgt : (6 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 6 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋d41_member＋双定理＋Q 平方锐度               *)
(* ============================================================ *)

Definition d41yp (k : nat) : positive := Zpos_of (d41y (S k)).
Definition d41wp (k : nat) : positive := Zpos_of (d41w (S k)).

Lemma d41yp_pos : forall k, Z.pos (d41yp k) = d41y (S k).
Proof.
  intro k. unfold d41yp. apply Zpos_of_pos.
  destruct (d41xy_ge1 (S k)) as [_ Hy]. lia.
Qed.

Lemma d41wp_pos : forall k, Z.pos (d41wp k) = d41w (S k).
Proof.
  intro k. unfold d41wp. apply Zpos_of_pos.
  pose proof (d41w_ge1 k). lia.
Qed.

(* 族成员：p_{3k+2}/q_{3k+2}＝√41 第 3k+2 收敛子（x²−41y²=±1 双族·k=0 即 32/5 范数 −1） *)
Definition d41_member (k : nat) : Q := (Z.pos (d41yp k) # d41wp k)%Q.

(* 族证书锐度（主定理一）：相邻族成员距 = 5/(w_{k+1}w_{k+2}) 精确等号
   ——d41_det ±5 等号实现（d13_family_sharp 同构·双族常元 5） *)
Theorem d41_family_sharp : forall k : nat,
  QeqT (Qabs (d41_member k - d41_member (S k)))
       ((Z.pos 5) # (d41wp k * d41wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d41_member k - d41_member (S k))%Q ==
               ((Z.pos (d41yp k) * Z.pos (d41wp (S k))
                 - Z.pos (d41yp (S k)) * Z.pos (d41wp k))
                 # (d41wp k * d41wp (S k)))%Q).
  { unfold d41_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d41yp_pos k), (d41yp_pos (S k)).
    assert (Hd2 : (d41y (S k) * Z.pos (d41wp (S k))
                   - d41y (S (S k)) * Z.pos (d41wp k) = 5 * powneg1 (S k))%Z).
    { pose proof (d41_det (S k)) as Hdet.
      rewrite <- (d41wp_pos (S k)), <- (d41wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden].
    rewrite Z.abs_mul, zabs_powneg1. cbn [Z.abs]. ring.
Qed.

(* 族分离证书（主定理二）：任意 a/b 到族成员距 ≥ 1/(b·w_{k+1})
   （d13_family_sep 同构·零前提位仅 gap≠0） *)
Theorem d41_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d41w (S k) - d41y (S k) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d41wp k)) # 1))
        (Qabs ((a # b)%Q - d41_member k)).
Proof.
  intros a b k Hk. unfold d41_member.
  assert (Hk2 : (a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b <> 0)%Z).
  { rewrite (d41wp_pos k), (d41yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b)
                  # (b * d41wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d41yp k) # d41wp k)%Q))
          (Qinv ((Z.pos (b * d41wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d41yp k) # d41wp k)%Q))
                   (Qabs ((a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b)
                           # (b * d41wp k))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d41wp k)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主定理三·FIB3 分离证书族侧已证结论）：|member²−41| = 1/w² 精确等号
   ——q_square_gap 下界 1/b² 在 ±1 双族上恰被实现（d13_q_square_sharp 同构） *)
Theorem d41_q_square_sharp : forall k : nat,
  QeqT (Qabs (d41_member k * d41_member k - (41 # 1)%Q))
       (Qinv ((Z.pos (d41wp k * d41wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d41_member k * d41_member k - (41 # 1))%Q ==
               ((Z.pos (d41yp k) * Z.pos (d41yp k)
                 - 41 * (Z.pos (d41wp k) * Z.pos (d41wp k)))
                 # (d41wp k * d41wp k))%Q).
  { unfold d41_member. apply (q_square_cross (Z.pos (d41yp k)) 41 (d41wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (d41yp_pos k).
    assert (Hn2 : (d41y (S k) * d41y (S k)
                   - 41 * (Z.pos (d41wp k) * Z.pos (d41wp k)) = powneg1 (S k))%Z).
    { pose proof (d41_norm_y (S k)) as Hn.
      rewrite <- (d41wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    destruct (powneg1 (S k)) as [|p|p] eqn:E.
    + exfalso. pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # d41wp k * d41wp k)) with (Z.pos 1 # d41wp k * d41wp k)%Q.
      change (Qinv (Z.pos (d41wp k * d41wp k) # 1)) with (1 # d41wp k * d41wp k)%Q.
      apply Qeq_refl.
    + pose proof (zabs_powneg1 (S k)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # d41wp k * d41wp k)) with (Z.pos 1 # d41wp k * d41wp k)%Q.
      change (Qinv (Z.pos (d41wp k * d41wp k) # 1)) with (1 # d41wp k * d41wp k)%Q.
      apply Qeq_refl.
Qed.

(* q_square_gap 实例使用（FIB3 主语句在 D=41 族上实例化——与锐度合取＝下界精确达到） *)
Lemma d41_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d41wp k * d41wp k)) # 1))
        (Qabs (d41_member k * d41_member k - (41 # 1)%Q)).
Proof.
  intro k. unfold d41_member.
  apply (q_square_gap 41 (Z.pos (d41yp k)) (d41wp k)).
  - cbn. lia.
  - intro c. apply (d41_nonsquare c).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions d41x_rec.
Print Assumptions d41y_rec.
Print Assumptions d41z_rec.
Print Assumptions d41w_rec.
Print Assumptions d41xy_ge1.
Print Assumptions d41zw_ge.
Print Assumptions d41w_ge1.
Print Assumptions d41_norm_quad.
Print Assumptions d41_norm_x.
Print Assumptions d41_norm_y.
Print Assumptions d41_norm_y_abs1.
Print Assumptions d41_det.
Print Assumptions d41_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d41yp_pos.
Print Assumptions d41wp_pos.
Print Assumptions d41_family_sep.
Print Assumptions d41_family_sharp.
Print Assumptions d41_q_square_sharp.
Print Assumptions d41_q_square_gap_instance.

(* 数值锚一（族成员·双族负侧）：member 0 = p_2/q_2 = 32/5（x²−41y²=−1） *)
Lemma smoke_member_32_5 : (Qeq_bool (d41_member 0) (32 # 5)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员·双族正侧）：member 1 = p_5/q_5 = 2049/320（x²−41y²=+1） *)
Lemma smoke_member_2049_320 : (Qeq_bool (d41_member 1) (2049 # 320)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|32²−41·5²| = 1（d41_norm_y_abs1 实例·双族交替锚） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d41y 1 * d41y 1 - 41 * (d41w 1 * d41w 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|32/5−2049/320| = 1/320 = 5/(5·320) 精确等号（d41_family_sharp 实例） *)
Lemma smoke_sharp_1_320 :
  (Qeq_bool (Qabs (d41_member 0 - d41_member 1))
            ((Z.pos 5) # (d41wp 0 * d41wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(32/5)²−41| = 1/25（d41_q_square_sharp 实例·FIB3 证书族侧等号） *)
Lemma smoke_qsq_1_25 :
  (Qeq_bool (Qabs (d41_member 0 * d41_member 0 - (41 # 1)%Q))
            (Qinv ((Z.pos (d41wp 0 * d41wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（N 矩阵步）：x_1 = 397, z_1 = 62（p_3/q_3 载体值） *)
Lemma smoke_step_397_62 :
  (Z.eqb (d41x 1) 397%Z, Z.eqb (d41z 1) 62%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_32_5.
Print Assumptions smoke_member_2049_320.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_320.
Print Assumptions smoke_qsq_1_25.
Print Assumptions smoke_step_397_62.

From Stdlib Require Import Extraction.
Separate Extraction d41pair e41pair d41x d41y d41z d41w d41yp d41wp
  d41_member d41_norm_y_abs1 d41_det d41_family_sep d41_family_sharp
  d41_q_square_sharp d41_q_square_gap_instance
  smoke_member_32_5 smoke_member_2049_320 smoke_norm_1 smoke_sharp_1_320
  smoke_qsq_1_25 smoke_step_397_62.
