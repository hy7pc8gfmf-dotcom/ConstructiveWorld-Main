(* 五字段指针｜使命：Pell 一般 D 收敛子族——非折半线收敛子族从 √2/√5 单例向一般 D 的扩张
   （二次冻结形）：按 √D 连分数周期类分档遇分类爆炸，落单类实例＋分类画像冻结——
   周期一类 D=m²+1（√D=[m; overline{2m}]·m≥1·D≤60 内清点 {2,5,10,17,26,37,50}，
   周期画像勘形在卷）以单参数 m 一致定理族承载，对齐 FIB fib_family_sep/sharp 双定理形：
   §C 载体层：pellpair/qelpair——D 参数化 fibpair 推广（Z 面对偶穿线·常系数 2m 线性递推
     (X_{n+1},X_n)=(2m·X_n+X_{n−1},X_n)·X_0=1,X_1=m｜Y_0=0,Y_1=1）＋pellx/pelly＋
     pellx_rec/pelly_rec（fibp_rec 同款 pair-threading 展开配方）；
   §N 范数层：pell_norm——X_n²−(m²+1)Y_n² = powneg1 n（一般 D 版 Cassini＝Pell 范数恒等·
     三件不变式归纳：范数 S_n＋交叉 C_n=X_nX_{n+1}−D·Y_nY_{n+1}=m·powneg1 n——递推
     S_{n+2}=4m²S_{n+1}+4mC_n+S_n·C_{n+1}=2mS_{n+1}+C_n·ring 分解＋powneg1 交替闭合）＋
     pell_norm_abs1（族上整隙恰 1——gen_gapD_ne 下界在族上精确实现）＋pell_det（行列式
     恒等 X_{n+1}Y_{n+2}−X_{n+2}Y_{n+1}=powneg1 (S n)·单步归纳）＋m1_nonsquare（m²+1 非完全
     平方——|c| 界矛盾·q_square_gap 使用位前提供给）；
   §Q 终形装配层：Zpos_of 正 Z→positive 桥（Zpos_of_pos·前提位守卫）＋pellxp/pellyp＋
     pell_member（族成员=X_{j+1}/Y_{j+1}＝√D 第 j 收敛子）＋pell_family_sharp（族证书锐度：
     相邻收敛子距=1/(Y_{j+1}Y_{j+2}) 精确等号·pell_det±1 等号实现·fib_family_sharp 同构）＋
     pell_family_sep（分离证书：k≠0 时任意 a/b 到族成员距≥1/(b·Y_{j+1})·fib_family_sep 同构）
     ＋pell_q_square_sharp（FIB3 q_square_gap 下界 1/b² 在族上精确等号实现：|member²−D|=1/Y²
     ——q_square_cross 直拼＋pell_norm 桥·FIB3 分离证书的族侧锐度确证）＋
     pell_q_square_gap_instance（q_square_gap 实例调用——上界与锐度合取＝族侧精确达到）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚六件（√2 族成员 3/2·√5 族成员 9/4·
     范数 |7²−2·5²|=1·锐度 1/10 精确等号·Q 平方锐度 1/4·Pell 数 (17,12)）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS
   （范数 m≤30 n≤41｜行列式全域｜锐度等号 650 例｜分离全称网格 40600 例·等号 ⟺ |k|=1｜
   Q 平方锐度全域｜m²+1 非平方 m≤199｜周期画像 D∈[2..60]）。
   依赖：S02_CauchyComplete（QeqT/QleT'）＋fib_machine（powneg1/zabs_powneg1/zabs_ge1/
     fib_cross_mult/fib_qabs_congr/fib_qle_abs_ge/fib_qleT_congr_r/fib_qeqT_one 形位）＋
     fib_qdomain（q_square_cross/q_square_gap）；Stdlib ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：语句面全 Set 承载（QeqT/QleT'）＋Z 面（·=·)%Z/(·<>0)%Z 为 B5/FIB/FIB2/FIB3
     在册同款先例形；证明体内构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典
     逻辑；定义面透明；主语句（family_sep/sharp/q_square_sharp）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" pell_family.v *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §C 载体层：pellpair/qelpair 对偶穿线＋pellx/pelly＋递归展开        *)
(* ============================================================ *)

(* X 流：(X_{n+1}, X_n)·X_0=1, X_1=m·X_{n+2}=2m·X_{n+1}+X_n *)
Fixpoint pellpair (m : Z) (n : nat) : Z * Z :=
  match n with
  | O => (m, 1%Z)
  | S k => match pellpair m k with pair x y => ((2 * m * x + y)%Z, x) end
  end.

(* Y 流：(Y_{n+1}, Y_n)·Y_0=0, Y_1=1·同系数递推 *)
Fixpoint qelpair (m : Z) (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | S k => match qelpair m k with pair x y => ((2 * m * x + y)%Z, x) end
  end.

Definition pellx (m : Z) (n : nat) : Z := snd (pellpair m n).
Definition pelly (m : Z) (n : nat) : Z := snd (qelpair m n).

Lemma pellx_0 : forall m : Z, pellx m 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma pellx_1 : forall m : Z, pellx m 1 = m%Z.
Proof. reflexivity. Qed.

Lemma pelly_0 : forall m : Z, pelly m 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma pelly_1 : forall m : Z, pelly m 1 = 1%Z.
Proof. reflexivity. Qed.

Lemma pellpair_unfold : forall (m : Z) (n : nat),
  pellpair m (S n) = ((2 * m * fst (pellpair m n) + snd (pellpair m n))%Z, fst (pellpair m n)).
Proof. intros m n. cbn [pellpair]. destruct (pellpair m n) as [a b]. reflexivity. Qed.

Lemma qelpair_unfold : forall (m : Z) (n : nat),
  qelpair m (S n) = ((2 * m * fst (qelpair m n) + snd (qelpair m n))%Z, fst (qelpair m n)).
Proof. intros m n. cbn [qelpair]. destruct (qelpair m n) as [a b]. reflexivity. Qed.

Lemma pellx_rec : forall (m : Z) (n : nat),
  pellx m (S (S n)) = (2 * m * pellx m (S n) + pellx m n)%Z.
Proof.
  intros m n. unfold pellx.
  rewrite (pellpair_unfold m (S n)).
  rewrite (pellpair_unfold m n).
  cbn [fst snd].
  reflexivity.
Qed.

Lemma pelly_rec : forall (m : Z) (n : nat),
  pelly m (S (S n)) = (2 * m * pelly m (S n) + pelly m n)%Z.
Proof.
  intros m n. unfold pelly.
  rewrite (qelpair_unfold m (S n)).
  rewrite (qelpair_unfold m n).
  cbn [fst snd].
  reflexivity.
Qed.

(* 正性层：m≥1 时 X_n/Y_{n+1} 全 ≥1（Q 分母位与 Zpos 桥守卫） *)
Lemma pellx_ge1_aux : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  (1 <= pellx m n)%Z /\ (1 <= pellx m (S n))%Z.
Proof.
  intros m Hm. induction n as [|n IH].
  - split.
    + rewrite pellx_0. lia.
    + rewrite pellx_1. exact Hm.
  - destruct IH as [IH1 IH2]. split.
    + exact IH2.
    + rewrite pellx_rec. pose proof IH1. pose proof IH2. nia.
Qed.

Lemma pelly_ge1_aux : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  (1 <= pelly m (S n))%Z /\ (1 <= pelly m (S (S n)))%Z.
Proof.
  intros m Hm. induction n as [|n IH].
  - split.
    + rewrite pelly_1. lia.
    + rewrite pelly_rec. rewrite pelly_1. rewrite pelly_0. nia.
  - destruct IH as [IH1 IH2]. split.
    + exact IH2.
    + rewrite pelly_rec. pose proof IH1. pose proof IH2. nia.
Qed.

Lemma pellx_ge1 : forall (m : Z), (1 <= m)%Z -> forall n : nat, (1 <= pellx m n)%Z.
Proof.
  intros m Hm n. destruct n as [|n].
  - apply (proj1 (pellx_ge1_aux m Hm 0)).
  - apply (proj2 (pellx_ge1_aux m Hm n)).
Qed.

Lemma pelly_ge1 : forall (m : Z), (1 <= m)%Z -> forall n : nat, (1 <= pelly m (S n))%Z.
Proof.
  intros m Hm n. apply (proj1 (pelly_ge1_aux m Hm n)).
Qed.

(* ============================================================ *)
(* §N 范数层：pell_norm（一般 D 版 Cassini）＋pell_det＋m1_nonsquare   *)
(* ============================================================ *)

Lemma powneg1_2 : forall n : nat, powneg1 (S (S n)) = powneg1 n.
Proof. intro n. rewrite !powneg1_S. lia. Qed.

(* 三件不变式归纳：S_n（范数）＋S_{n+1}＋C_n（交叉）——递推
   S_{n+2}=4m²S_{n+1}+4mC_n+S_n 与 C_{n+1}=2mS_{n+1}+C_n 仅用同窗三件 *)
Lemma pell_norm_tri : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  (pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n) = powneg1 n)%Z /\
  (pellx m (S n) * pellx m (S n) - (m*m+1) * (pelly m (S n) * pelly m (S n)) = powneg1 (S n))%Z /\
  (pellx m n * pellx m (S n) - (m*m+1) * (pelly m n * pelly m (S n)) = m * powneg1 n)%Z.
Proof.
  intros m Hm. induction n as [|n [H1 [H2 H3]]].
  - split; [| split].
    + unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
    + unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
    + unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
  - split; [| split].
    + exact H2.
    + rewrite (pellx_rec m n), (pelly_rec m n), powneg1_2.
      transitivity ((4*m*m*(pellx m (S n) * pellx m (S n) - (m*m+1) * (pelly m (S n) * pelly m (S n)))
                    + 4*m*(pellx m n * pellx m (S n) - (m*m+1) * (pelly m n * pelly m (S n)))
                    + (pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n)))%Z).
      * ring.
      * rewrite H2, H3, H1. rewrite powneg1_S. ring.
    + rewrite (pellx_rec m n), (pelly_rec m n).
      transitivity ((2*m*(pellx m (S n) * pellx m (S n) - (m*m+1) * (pelly m (S n) * pelly m (S n)))
                    + (pellx m n * pellx m (S n) - (m*m+1) * (pelly m n * pelly m (S n))))%Z).
      * ring.
      * rewrite H2, H3. rewrite powneg1_S. ring.
Qed.

(* 主语句：一般 D=m²+1 版 Cassini＝Pell 范数恒等（族上整隙恰 ±1 交替） *)
Theorem pell_norm : forall (m : Z) (n : nat), (1 <= m)%Z ->
  (pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n) = powneg1 n)%Z.
Proof.
  intros m n Hm. exact (proj1 (pell_norm_tri m Hm n)).
Qed.

(* 族上整隙恰 1（gen_gapD_ne 下界 ≥1 在族上精确实现） *)
Theorem pell_norm_abs1 : forall (m : Z) (n : nat), (1 <= m)%Z ->
  Z.abs (pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n)) = 1%Z.
Proof.
  intros m n Hm. rewrite (pell_norm m n Hm). apply zabs_powneg1.
Qed.

(* 行列式恒等：X_{n+1}Y_{n+2}−X_{n+2}Y_{n+1} = powneg1 (S n)（单步归纳） *)
Lemma pell_det : forall (m : Z) (n : nat),
  (pellx m (S n) * pelly m (S (S n)) - pellx m (S (S n)) * pelly m (S n) = powneg1 (S n))%Z.
Proof.
  intro m. induction n as [|n IH].
  - rewrite pellx_1, pelly_1.
    rewrite (pellx_rec m 0), (pelly_rec m 0).
    rewrite pellx_1, pellx_0, pelly_1, pelly_0.
    cbn [powneg1]. ring.
  - rewrite powneg1_S.
    transitivity ((- (pellx m (S n) * pelly m (S (S n)) - pellx m (S (S n)) * pelly m (S n)))%Z).
    + rewrite (pellx_rec m (S n)), (pelly_rec m (S n)),
        (pellx_rec m n), (pelly_rec m n). ring.
    + rewrite IH. reflexivity.
Qed.

(* D=m²+1 非完全平方（|c| 界矛盾——q_square_gap 使用位前提供） *)
Lemma m1_nonsquare : forall m c : Z, (1 <= m)%Z -> (m*m+1 <> c*c)%Z.
Proof.
  intros m c Hm Hc.
  pose proof (Z.abs_square c) as Habs.
  pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = m*m+1)%Z) by lia.
  assert (Hgt : (m < Z.abs c)%Z).
  { destruct (Z_lt_le_dec m (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* §Q 终形装配层：Zpos 桥＋pell_member＋双定理＋Q 平方锐度              *)
(* ============================================================ *)

(* 正 Z→positive 桥（前提位守卫：0<z 处给回真 positive·fail-loud 惯例＝非正落 1 且
   一切使用位带正性前提使桥成立） *)
Definition Zpos_of (z : Z) : positive :=
  match z with Zpos p => p | _ => 1%positive end.

Lemma Zpos_of_pos : forall z : Z, (0 < z)%Z -> Z.pos (Zpos_of z) = z.
Proof.
  intros z Hz. destruct z as [|p|p].
  - exfalso. cbn in Hz. lia.
  - reflexivity.
  - exfalso. cbn in Hz. pose proof (Pos2Z.is_pos p). lia.
Qed.

Definition pellxp (m : Z) (j : nat) : positive := Zpos_of (pellx m (S j)).
Definition pellyp (m : Z) (j : nat) : positive := Zpos_of (pelly m (S j)).

Lemma pellxp_pos : forall (m : Z) (j : nat), (1 <= m)%Z ->
  Z.pos (pellxp m j) = pellx m (S j).
Proof.
  intros m j Hm. unfold pellxp. apply Zpos_of_pos.
  pose proof (pellx_ge1 m Hm (S j)). lia.
Qed.

Lemma pellyp_pos : forall (m : Z) (j : nat), (1 <= m)%Z ->
  Z.pos (pellyp m j) = pelly m (S j).
Proof.
  intros m j Hm. unfold pellyp. apply Zpos_of_pos.
  pose proof (pelly_ge1 m Hm j). lia.
Qed.

(* 族成员：X_{j+1}/Y_{j+1}＝√(m²+1) 的第 j 收敛子（m=1 时即 √2 族） *)
Definition pell_member (m : Z) (j : nat) : Q := (Z.pos (pellxp m j) # pellyp m j)%Q.

(* 族证书锐度（主语句一）：相邻收敛子距 = 1/(Y_{j+1}Y_{j+2}) 精确等号
   ——pell_det ±1 等号实现（fib_family_sharp 同构） *)
Theorem pell_family_sharp : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QeqT (Qabs (pell_member m j - pell_member m (S j)))
       (Qinv ((Z.pos (pellyp m j * pellyp m (S j))) # 1)).
Proof.
  intros m j Hm.
  assert (Hd : (pell_member m j - pell_member m (S j))%Q ==
               ((Z.pos (pellxp m j) * Z.pos (pellyp m (S j))
                 - Z.pos (pellxp m (S j)) * Z.pos (pellyp m j))
                 # (pellyp m j * pellyp m (S j)))%Q).
  { unfold pell_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (pellxp_pos m j Hm), (pellxp_pos m (S j) Hm).
    assert (Hd2 : (pellx m (S j) * Z.pos (pellyp m (S j))
                   - pellx m (S (S j)) * Z.pos (pellyp m j) = powneg1 (S j))%Z).
    { pose proof (pell_det m j) as Hdet.
      rewrite <- (pellyp_pos m (S j) Hm), <- (pellyp_pos m j Hm) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    destruct (powneg1 (S j)) as [|p|p] eqn:E.
    + exfalso. pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # pellyp m j * pellyp m (S j))) with (Z.pos 1 # pellyp m j * pellyp m (S j))%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m (S j)) # 1)) with (1 # pellyp m j * pellyp m (S j))%Q.
      apply Qeq_refl.
    + pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # pellyp m j * pellyp m (S j))) with (Z.pos 1 # pellyp m j * pellyp m (S j))%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m (S j)) # 1)) with (1 # pellyp m j * pellyp m (S j))%Q.
      apply Qeq_refl.
Qed.

(* 族分离证书（主语句二）：k≠0 时任意 a/b 到族成员距 ≥ 1/(b·Y_{j+1})
   （fib_family_sep 同构·零前提位仅 k≠0 与 m≥1） *)
Theorem pell_family_sep : forall (m : Z) (j : nat) (a : Z) (b : positive), (1 <= m)%Z ->
  (a * pelly m (S j) - pellx m (S j) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * pellyp m j)) # 1))
        (Qabs ((a # b)%Q - pell_member m j)).
Proof.
  intros m j a b Hm Hk. unfold pell_member.
  assert (Hk2 : (a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b <> 0)%Z).
  { rewrite (pellyp_pos m j Hm), (pellxp_pos m j Hm). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b)
                  # (b * pellyp m j))%Q)
          (Qabs ((a # b)%Q - (Z.pos (pellxp m j) # pellyp m j)%Q))
          (Qinv ((Z.pos (b * pellyp m j)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (pellxp m j) # pellyp m j)%Q))
                   (Qabs ((a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b)
                           # (b * pellyp m j))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * pellyp m j)%positive).
    apply zabs_ge1. exact Hk2.
Qed.

(* Q 平方锐度（主语句三·FIB3 分离证书族侧确证）：|member²−D| = 1/Y² 精确等号
   ——q_square_gap 下界 1/b² 在族上恰被实现（独立复算 ③⑤ 全域精确） *)
Theorem pell_q_square_sharp : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QeqT (Qabs (pell_member m j * pell_member m j - ((m*m+1) # 1)%Q))
       (Qinv ((Z.pos (pellyp m j * pellyp m j)) # 1)).
Proof.
  intros m j Hm.
  assert (Hd : (pell_member m j * pell_member m j - ((m*m+1) # 1))%Q ==
               ((Z.pos (pellxp m j) * Z.pos (pellxp m j)
                 - (m*m+1) * (Z.pos (pellyp m j) * Z.pos (pellyp m j)))
                 # (pellyp m j * pellyp m j))%Q).
  { unfold pell_member. apply (q_square_cross (Z.pos (pellxp m j)) (m*m+1) (pellyp m j)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - rewrite (pellxp_pos m j Hm).
    assert (Hn2 : (pellx m (S j) * pellx m (S j)
                   - (m*m+1) * (Z.pos (pellyp m j) * Z.pos (pellyp m j)) = powneg1 (S j))%Z).
    { pose proof (pell_norm m (S j) Hm) as Hn.
      rewrite <- (pellyp_pos m j Hm) in Hn. exact Hn. }
    rewrite Hn2.
    destruct (powneg1 (S j)) as [|p|p] eqn:E.
    + exfalso. pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # pellyp m j * pellyp m j)) with (Z.pos 1 # pellyp m j * pellyp m j)%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m j) # 1)) with (1 # pellyp m j * pellyp m j)%Q.
      apply Qeq_refl.
    + pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # pellyp m j * pellyp m j)) with (Z.pos 1 # pellyp m j * pellyp m j)%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m j) # 1)) with (1 # pellyp m j * pellyp m j)%Q.
      apply Qeq_refl.
Qed.

(* q_square_gap 实例调用（FIB3 主语句在族上实例化——与锐度合取＝下界精确达到） *)
Lemma pell_q_square_gap_instance : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QleT' (Qinv ((Z.pos (pellyp m j * pellyp m j)) # 1))
        (Qabs (pell_member m j * pell_member m j - ((m*m+1) # 1)%Q)).
Proof.
  intros m j Hm. unfold pell_member.
  apply (q_square_gap (m*m+1) (Z.pos (pellxp m j)) (pellyp m j)).
  - nia.
  - intro c. apply (m1_nonsquare m c Hm).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                  *)
(* ============================================================ *)

Print Assumptions pellx_rec.
Print Assumptions pelly_rec.
Print Assumptions pellx_ge1.
Print Assumptions pelly_ge1.
Print Assumptions pell_det.
Print Assumptions pell_norm.
Print Assumptions pell_norm_abs1.
Print Assumptions m1_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions pell_family_sep.
Print Assumptions pell_family_sharp.
Print Assumptions pell_q_square_sharp.
Print Assumptions pell_q_square_gap_instance.

(* 数值锚一（√2 族成员）：member 1 1 = X_2/Y_2 = 3/2 *)
Lemma smoke_member_3_2 : (Qeq_bool (pell_member 1 1) (3 # 2)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（√5 族成员）：member 2 1 = X_2/Y_2 = 9/4 *)
Lemma smoke_member_9_4 : (Qeq_bool (pell_member 2 1) (9 # 4)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（范数层）：|X_3²−2·Y_3²| = |49−50| = 1（pell_norm_abs1 实例） *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (pellx 1 3 * pellx 1 3 - 2 * (pelly 1 3 * pelly 1 3))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（锐度层）：|3/2−7/5| = 1/10 = Qinv (pellyp 1 1 · pellyp 1 2)（pell_family_sharp 实例） *)
Lemma smoke_sharp_1_10 :
  (Qeq_bool (Qabs (pell_member 1 1 - pell_member 1 2))
            (Qinv ((Z.pos (pellyp 1 1 * pellyp 1 2)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方锐度）：|(3/2)²−2| = 1/4（pell_q_square_sharp 实例·FIB3 证书族侧等号） *)
Lemma smoke_qsq_1_4 :
  (Qeq_bool (Qabs (pell_member 1 1 * pell_member 1 1 - (2 # 1)%Q))
            (Qinv ((Z.pos (pellyp 1 1 * pellyp 1 1)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（Pell 数）：pellx 1 4 = 17, pelly 1 4 = 12（√2 收敛子 17/12 载体值） *)
Lemma smoke_pell_17_12 :
  (Z.eqb (pellx 1 4) 17%Z, Z.eqb (pelly 1 4) 12%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_3_2.
Print Assumptions smoke_member_9_4.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_10.
Print Assumptions smoke_qsq_1_4.
Print Assumptions smoke_pell_17_12.

From Stdlib Require Import Extraction.
Separate Extraction pellpair qelpair pellx pelly Zpos_of pellxp pellyp
  pell_member pell_norm_abs1 pell_family_sep pell_family_sharp
  pell_q_square_sharp pell_q_square_gap_instance
  smoke_member_3_2 smoke_member_9_4 smoke_norm_1 smoke_sharp_1_10
  smoke_qsq_1_4 smoke_pell_17_12.
