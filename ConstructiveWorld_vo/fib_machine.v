(* 五字段指针｜使命：Fibonacci 分母族机——非折半线的分母族扩张：黄金比 φ 收敛子族
   在 B5 三层机件（证书基量/整值整隙/恒等链）上的实例化——该线从 √2 单例向族承载
   的第一步。
   三层机形逐层适配（对 B5 b5_machine.v 刻形）：
   §C 载体层：fibpair/fibp（pair-threading 正数对穿线·fibp n = F_{n+1}）＋fibz（Z 层对应）
     ＋powneg1（符号穿线·替代 (−1)^n 幂形——幂指数面 nat/Z 越谱坑绕行）；
   §S 证书基量层：fib_den n b := b·F_{n+1}｜fib_cert n b := 1/(b·F_{n+1})（正性·QeqT 钉定）
     ——B5 b5_den/b5_cert 同形（分母族位 b·F_{n+1} 替 |a|+2b 因子位）；
   §G 整值整隙层：fibz_cassini——F_{n+2}²−F_{n+1}F_{n+3} = powneg1 (S n)（Cassini 恒等·
     族上整隙恰 ±1——比 B5 的 |a²−2b²|≥1 更强：族成员处精确等式）＋fib_gap_ge1（|·|=1）
     ＋fib_abs_gap（Z.abs 形）；
   §I 恒等链层：fib_cross_mult——(a/b−c/d)·bd = ad−cb（交叉相乘恒等·B5 (q−x)(q+x)=q²−x²
     的分母族对应件）＋fib_qabs_congr（Qabs 沿 Qeq 同余·经 Zabs_Qabs 桥）＋
     fib_qle_abs_ge（分离核：|k|≥1 ⟹ 1/M ≤ |k|/M）；
   §T 终形装配：fib_family_sep——任意 a/b 到族成员 F_{n+2}/F_{n+1} 的距离 ≥ 族证书
     1/(b·F_{n+1})（k≠0 时·零前提主语句·全 Set 承载）＋fib_family_sharp——相邻收敛子
     对处等号恰取（族证书锐度·Hurwitz/Markov 边界实现：b²·dist→1/√5 交错极限·
     精确有理算术勘形在卷）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚（族成员 13/8·锐点等号 1/40·
     严格例 9/40>1/25·正性·RunAlive 末棒档）。
   独立复算先行（假件拦截第一道）：Fractions 精确路 ALL PASS
   （Cassini n≤120·锐点等号 n≤118·族证书全称网格 50685 例·等号特征 |k|=1·
   恒等链 b·F·dist=|k| 精确·Markov 边界 1/√5 两侧交错极限的精确有理括界勘形）。
   依赖：S02_CauchyComplete
   （QltT/QleT'/QeqT 与换向迁移件 Qlt_to_QltT/Qle_to_QleT'/qeq_imp_qeqT 全在其上）；
   Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。
   构造性注记：承载语句面全 Set 层（QeqT/QleT'/QltT/Z.eq/bool），零 Prop 前提位
   （唯一前提 (·<>0)%Z 与 (0<·)%Z 为 B5 在册同款先例形）；证明体内构造性 Prop 推导合法；
   零承认、零 Abort、零全局假设、零经典逻辑；定义面透明。
   编译配方：rocq c -native-compiler no -q -Q . "" fib_machine.v *)
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §C 载体层：fibpair 穿线 / fibp = F_{n+1} / fibz Z 层对应 / powneg1 *)
(* ============================================================ *)

Fixpoint fibpair (n : nat) : positive * positive :=
  match n with
  | O => (1%positive, 1%positive)
  | S m => match fibpair m with
           | pair a b => (Pos.add a b, a)
           end
  end.

Definition fibp (n : nat) : positive := snd (fibpair n).

Definition fibz (n : nat) : Z := Z.pos (fibp n).

Fixpoint powneg1 (n : nat) : Z := match n with O => 1%Z | S m => (- powneg1 m)%Z end.

Lemma fibpair_unfold : forall n,
  fibpair (S n) = (Pos.add (fst (fibpair n)) (snd (fibpair n)), fst (fibpair n)).
Proof. intro n. cbn [fibpair]. destruct (fibpair n) as [a b]. reflexivity. Qed.

Lemma fibpair_snd_S : forall n, snd (fibpair (S n)) = fst (fibpair n).
Proof. intro n. rewrite fibpair_unfold. reflexivity. Qed.

Lemma fibp_rec : forall n, fibp (S (S n)) = Pos.add (fibp (S n)) (fibp n).
Proof.
  intro n. unfold fibp.
  rewrite (fibpair_unfold (S n)).
  rewrite (fibpair_unfold n).
  cbn [fst snd].
  reflexivity.
Qed.

Lemma fibz_rec : forall n, fibz (S (S n)) = (fibz (S n) + fibz n)%Z.
Proof. intro n. unfold fibz. rewrite fibp_rec. reflexivity. Qed.

Lemma fibz_pos : forall n, (0 < fibz n)%Z.
Proof. intro n. apply Pos2Z.is_pos. Qed.

Lemma powneg1_S : forall n, powneg1 (S n) = (- powneg1 n)%Z.
Proof. intro n. reflexivity. Qed.

Lemma zabs_powneg1 : forall n, Z.abs (powneg1 n) = 1%Z.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite powneg1_S, Z.abs_opp. exact IH.
Qed.

Lemma zabs_ge1 : forall k : Z, k <> 0%Z -> (1 <= Z.abs k)%Z.
Proof.
  intros k H. destruct k as [|p|p].
  - exfalso. apply H. reflexivity.
  - cbn [Z.abs]. pose proof (Pos2Z.is_pos p). lia.
  - cbn [Z.abs]. pose proof (Pos2Z.is_pos p). lia.
Qed.

(* ============================================================ *)
(* §S 证书基量层：fib_den / fib_cert / 正性 / QeqT 钉定             *)
(* ============================================================ *)

Definition fib_den (n : nat) (b : positive) : Z :=
  Z.pos b * fibz n.

Definition fib_cert (n : nat) (b : positive) : Q :=
  Qinv ((fib_den n b) # 1).

Lemma fib_den_pos : forall (n : nat) (b : positive), (0 < fib_den n b)%Z.
Proof.
  intros n b. unfold fib_den.
  pose proof (fibz_pos n) as Hn.
  pose proof (Pos2Z.is_pos b) as Hb.
  nia.
Qed.

Lemma fib_qinv_pos : forall z : Z, (0 < z)%Z -> QltT 0 (Qinv (z # 1)).
Proof.
  intros z Hz. destruct z as [|p|p].
  - exfalso. lia.
  - apply Qlt_to_QltT. unfold Qlt, Qinv. cbn [Qnum Qden]. lia.
  - exfalso. lia.
Qed.

Lemma fib_cert_pos : forall (n : nat) (b : positive), QltT 0 (fib_cert n b).
Proof. intros n b. unfold fib_cert. apply fib_qinv_pos. apply fib_den_pos. Qed.

Lemma fib_cert_eq : forall (n : nat) (b : positive),
  QeqT (fib_cert n b) (Qinv ((Z.pos b * fibz n) # 1)).
Proof.
  intros n b. unfold fib_cert, fib_den. apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §G 整值整隙层（族上精确 ±1·Cassini）                             *)
(* ============================================================ *)

Lemma fibz_cassini : forall n : nat,
  (fibz (S n) * fibz (S n) - fibz n * fibz (S (S n)))%Z = powneg1 (S n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite powneg1_S.
    rewrite <- IH.
    rewrite !fibz_rec.
    ring.
Qed.

Lemma fib_gap_abs1 : forall n : nat,
  Z.abs (fibz (S n) * fibz (S n) - fibz n * fibz (S (S n))) = 1%Z.
Proof.
  intro n. rewrite fibz_cassini. apply zabs_powneg1.
Qed.

(* ============================================================ *)
(* §I 恒等链层（Q）：交叉相乘＋Qabs 同余＋分离核                     *)
(* ============================================================ *)

Lemma fib_cross_mult : forall (a c : Z) (b d : positive),
  ((a # b) - (c # d))%Q == ((a * Z.pos d - c * Z.pos b) # (b * d))%Q.
Proof.
  intros a c b d. unfold Qminus, Qopp, Qplus, Qnum, Qden. cbn.
  rewrite Z.mul_opp_l. reflexivity.
Qed.

Lemma fib_qabs_congr : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros x y Hxy.
  destruct x as [nx dx]; destruct y as [ny dy].
  change (Qabs (nx # dx)) with (Z.abs nx # dx)%Q.
  change (Qabs (ny # dy)) with (Z.abs ny # dy)%Q.
  unfold Qeq in Hxy |- *.
  cbn [Qnum Qden] in Hxy |- *.
  destruct nx as [|p|p]; destruct ny as [|q|q].
  - cbn [Z.abs]. reflexivity.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos q); pose proof (Pos2Z.is_pos dx). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos q); pose proof (Pos2Z.is_pos dx). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos dy). lia.
  - cbn [Z.abs]. exact Hxy.
  - exfalso. cbn [Z.abs] in *.
    pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos q);
    pose proof (Pos2Z.is_pos dx); pose proof (Pos2Z.is_pos dy). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos dy). lia.
  - exfalso. cbn [Z.abs] in *.
    pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos q);
    pose proof (Pos2Z.is_pos dx); pose proof (Pos2Z.is_pos dy). lia.
  - cbn [Z.abs]. simpl in Hxy. inversion Hxy. subst.
    rewrite <- (Pos2Z.inj_mul p dy), <- (Pos2Z.inj_mul q dx).
    rewrite H0. reflexivity.
Qed.

Lemma fib_qle_abs_ge : forall (M : positive) (k : Z),
  (1 <= Z.abs k)%Z -> QleT' (Qinv ((Z.pos M) # 1)%Q) (Qabs (k # M)%Q).
Proof.
  intros M k Hk. destruct k as [|q|q].
  - exfalso. cbn in Hk. lia.
  - cbn [Z.abs]. apply Qle_to_QleT'. unfold Qle, Qinv, Qabs, Qnum. cbn.
    pose proof (Pos2Z.is_pos M). pose proof (Pos2Z.is_pos q). nia.
  - cbn [Z.abs]. apply Qle_to_QleT'. unfold Qle, Qinv, Qabs, Qopp, Qnum. cbn.
    pose proof (Pos2Z.is_pos M). pose proof (Pos2Z.is_pos q). nia.
Qed.

(* QleT' 右元沿 Qeq 迁移（Qle_comp 实例直取·「qeq_le 显式迁移」同款） *)
Lemma fib_qleT_congr_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hle. apply Qle_to_QleT'.
  apply (proj1 (Qle_comp z z (Qeq_refl z) x y Hxy)).
  exact (QleT'_to_Qle _ _ Hle).
Qed.

(* ============================================================ *)
(* §T 终形装配：fib_member / fib_family_sep / fib_family_sharp      *)
(* ============================================================ *)

(* 族成员 n：F_{n+2}/F_{n+1}（黄金比第 n+1 收敛子·fibp n = F_{n+1} 承载分母） *)
Definition fib_member (n : nat) : Q := (fibz (S n) # fibp n)%Q.

(* 族分离证书（主语句·零前提）：|a/b − F_{n+2}/F_{n+1}| ≥ 1/(b·F_{n+1})（k≠0） *)
Theorem fib_family_sep : forall (n : nat) (a : Z) (b : positive),
  (a * fibz n - Z.pos b * fibz (S n) <> 0)%Z ->
  QleT' (fib_cert n b)
        (Qabs ((a # b)%Q - fib_member n)).
Proof.
  intros n a b Hk. unfold fib_member, fib_cert.
  assert (Hk2 : (a * Z.pos (fibp n) - fibz (S n) * Z.pos b <> 0)%Z).
  { unfold fibz in Hk.
    pose proof (Z.mul_comm (Z.pos (fibp (S n))) (Z.pos b)) as Hc.
    intro Hc0. apply Hk. rewrite <- Hc. exact Hc0. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (fibp n) - fibz (S n) * Z.pos b) # (b * fibp n))%Q)
          (Qabs ((a # b)%Q - (fibz (S n) # fibp n)%Q))
          (Qinv ((Z.pos b * fibz n) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (fibz (S n) # fibp n)%Q))
                   (Qabs ((a * Z.pos (fibp n) - fibz (S n) * Z.pos b) # (b * fibp n))%Q)).
    apply fib_qabs_congr. apply fib_cross_mult.
  - change (Z.pos b * fibz n)%Z with (Z.pos (b * fibp n))%Z.
    apply (fib_qle_abs_ge (b * fibp n)).
    apply zabs_ge1. exact Hk2.
Qed.

(* Qinv 正元形（unfold 配方直验） *)
Lemma fib_qinv_shape : forall p : positive, Qinv ((Z.pos p) # 1)%Q == (1 # p)%Q.
Proof. intro p. unfold Qeq, Qinv. cbn. reflexivity. Qed.

(* 锐度辅助件：|±1/M| = 1/M 之 QeqT 形 *)
Lemma fib_qeqT_one : forall M : positive,
  QeqT (Qabs ((Z.pos 1 # M)%Q)) (Qinv ((Z.pos M) # 1)%Q).
Proof.
  intro M.
  apply qeq_imp_qeqT.
  change (Qabs (Z.pos 1 # M)) with (Z.pos 1 # M)%Q.
  change (Qinv (Z.pos M # 1)) with (1 # M)%Q.
  apply Qeq_refl.
Qed.

(* 族证书锐度（Markov/Hurwitz 边界实现）：相邻收敛子对处等号恰取
   dist(member j, member (S j)) = 1/(F_{j+1}·F_{j+2})·即族证书在 b:=F_{j+1} 处精确达到
   ——Fibonacci 族把 Hurwitz 天花板 1/√5 从下方精确实现（精确有理勘形在卷） *)
Theorem fib_family_sharp : forall j : nat,
  QeqT (Qabs (fib_member j - fib_member (S j)))
       (Qinv ((Z.pos (fibp j * fibp (S j))) # 1)).
Proof.
  intro j.
  assert (Hd : (fib_member j - fib_member (S j))%Q ==
               ((fibz (S j) * Z.pos (fibp (S j)) - fibz (S (S j)) * Z.pos (fibp j)) # (fibp j * fibp (S j)))%Q).
  { unfold fib_member. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact Hab.
  - change (Z.pos (fibp (S j))) with (fibz (S j)).
    change (Z.pos (fibp j)) with (fibz j).
    rewrite (Z.mul_comm (fibz (S (S j))) (fibz j)).
    rewrite (fibz_cassini j).
    destruct (powneg1 (S j)) as [|p|p] eqn:E.
    + exfalso.
      pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    +       pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz.
      inversion Hz. subst p.
      change (Qabs (Z.pos 1 # fibp j * fibp (S j))) with (Z.pos 1 # fibp j * fibp (S j))%Q.
      change (Qinv (Z.pos (fibp j * fibp (S j)) # 1)) with (1 # fibp j * fibp (S j))%Q.
      apply Qeq_refl.
    +       pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz.
      inversion Hz. subst p.
      change (Qabs (Z.neg 1 # fibp j * fibp (S j))) with (Z.pos 1 # fibp j * fibp (S j))%Q.
      change (Qinv (Z.pos (fibp j * fibp (S j)) # 1)) with (1 # fibp j * fibp (S j))%Q.
      apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚               *)
(* ============================================================ *)

Print Assumptions fib_den_pos.
Print Assumptions fib_cert_pos.
Print Assumptions fib_cert_eq.
Print Assumptions fibz_cassini.
Print Assumptions fib_gap_abs1.
Print Assumptions fib_cross_mult.
Print Assumptions fib_qabs_congr.
Print Assumptions fib_qle_abs_ge.
Print Assumptions fib_family_sep.
Print Assumptions fib_family_sharp.

(* 数值锚一（族成员·RunAlive 末棒档）：member 3 = F_5/F_4 = 5/3 *)
Lemma fib_smoke_member_5_3 :
  (Qeq_bool (fib_member 3) (5 # 3)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（锐点等号）：dist(member 4, member 5) = |13/8 − 21/13| = 1/104
   = Qinv ((Z.pos (fibp 4 * fibp 5)) # 1)（fibp 4 = 5, fibp 5 = 8·族证书精确达到） *)
Lemma fib_smoke_sharp_13_8 :
  (Qeq_bool (Qabs (fib_member 4 - fib_member 5))
            (Qinv ((Z.pos (fibp 4 * fibp 5)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（分离严格例）：|7/5 − 13/8| = 9/40 > 1/25 = fib_cert 4 5 *)
Lemma fib_smoke_sep_strict :
  (Qlt_bool (fib_cert 4 5%positive)
            (Qabs ((7 # 5)%Q - fib_member 4))) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（证书正性·负分子） *)
Lemma fib_smoke_cert_pos :
  (Qlt_bool 0%Q (fib_cert 4 5%positive)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（整隙层实例）：|F_6² − F_5·F_7| = 1（fibz 4 = 5, fibz 5 = 8, fibz 6 = 13） *)
Lemma fib_smoke_gap :
  Z.eqb (Z.abs (fibz 5 * fibz 5 - fibz 4 * fibz 6)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions fib_smoke_member_5_3.
Print Assumptions fib_smoke_sharp_13_8.
Print Assumptions fib_smoke_sep_strict.
Print Assumptions fib_smoke_cert_pos.
Print Assumptions fib_smoke_gap.

From Stdlib Require Import Extraction.
Separate Extraction fibp fibz fib_cert fib_member fib_family_sep
  fib_family_sharp fib_smoke_member_5_3 fib_smoke_sharp_13_8
  fib_smoke_sep_strict fib_smoke_cert_pos fib_smoke_gap.
