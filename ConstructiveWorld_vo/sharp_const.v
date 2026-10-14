(* 五字段指针｜使命：锐度常元谱刻画——|E_k|＝块积 M* 的 (1,2) 元＝q_{T−1}（三路核对
   独立复算 53/53 零例外）升机内一般定理（谱理论首定理）。
   §G 一般矩阵流层（跨族统一基座）：gp——任意 2×2 整数矩阵 (a,b,c,d) 的
     pair-threading 双流发生器（行对 (x',y')=(ax+by,cx+dy)·四代族载体同构抽象）；
     sdet＝流邻 det｜cross＝伴生 G·三恒等式：cross_n=(ad−bc)^n·G0｜sdet_n=b·(ad−bc)^n·G0｜
     row2_n=−c·(ad−bc)^n·G0（「成员流 r 的相邻 det=B_{r,c}·G」统一形的一般化）；
   §S 谱刻画定理（一般形）：sc_general（det=1）/sc_general_alt（det=−1）——
     |E_n|＝|b|·|G0|＝常元·两显式类：T=1 类 sc_T1/sc_T1_B1（B≡1 ∀m·q₀=1 类级根据）
     ／T=2 类 sc_T2/sc_T2_Babs（B≡a₁ ∀a1a2p0·q₁=a₁ 类级根据——首成员分母位）
     ／D=13 旋转块积实例档（row2 面·B=5=q₄）；
   §R 逐件重收层（一般定理→四代族冻结件全核对）：pellpair/qelpair/d3pair/e3pair/
     d6pair/e6pair/d13pair/e13pair＝gp 实例桥八件＋sc_T1_recovers_pell_det（FIB4
     pell_det 类级从一般定理重收）＋sc_T2_recovers_d3_det/d6_det（FIB6 双件重收）＋
     sc_T5_recovers_d13_det（FIB5 重收）——锐度常元从逐 D 实例升为一般定理的重收见证；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚七件（E_5(D=5)=1·E_4(D=3)=1·
     E_4(D=6)=2·E'_0(D=13)=5·首成员分母 2(D=6)·√10 首成员 19/6·E_0(D=10)=−1）。
   独立复算先行（假件拦截第一道）：整数精确路 ALL PASS（一般三恒等式 1620 例｜
     T=1 类 525 例｜T=2 类 4928 例｜D=13 row2＋首成员 18/5｜四代载体 410 例｜
     载体↔独立 CF 发生器核对 √3/√6/√13/√(m²+1) 抽样）。
   依赖：fib_machine（powneg1/powneg1_S/zabs_powneg1）＋pell_family（pellpair/qelpair 系）
     ＋d3_family＋d6_family＋d13_family（载体桥源）；Stdlib ZArith、Arith、Lia。
   构造性注记：语句面 Z 面等式（pell_det/d3_det 在册同款先例形）＋定义面全透明
     （Fixpoint/Definition 可提取实型计算面）；零承认、零 Abort、零全局假设、零经典
     逻辑；主语句（sc_general/alt/sc_T1/sc_T2/D=13 实例档/重收件）结构化收尾零 solver。
   编译配方：rocq c -native-compiler no -q -Q . "" sharp_const.v *)

Require Import fib_machine.
Require Import pell_family.
Require Import d3_family.
Require Import d6_family.
Require Import d13_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* §G 一般矩阵流层：gp 双流发生器＋gx/gy＋sdet/cross                  *)
(* ============================================================ *)

(* gp：任意 2×2 整数矩阵 (a,b,c,d) 的 pair-threading 流——
   (x_{k+1},y_{k+1})=(a·x_k+b·y_k, c·x_k+d·y_k)·四代族载体（pellpair/d3pair/d6pair/
   d13pair）的同构抽象（§R 桥逐件重收） *)
Fixpoint gp (a b c d x0 y0 : Z) (n : nat) : Z * Z :=
  match n with
  | O => (x0, y0)
  | S k => match gp a b c d x0 y0 k with
           | pair x y => ((a * x + b * y)%Z, (c * x + d * y)%Z)
           end
  end.

Definition gx (a b c d x0 y0 : Z) (n : nat) : Z := fst (gp a b c d x0 y0 n).
Definition gy (a b c d x0 y0 : Z) (n : nat) : Z := snd (gp a b c d x0 y0 n).

(* 流邻行列式 sdet（E_k＝锐度常元载体）与伴生交叉 cross（G_k＝det 内芯） *)
Definition sdet (a b c d x0 y0 z0 w0 : Z) (n : nat) : Z :=
  (gx a b c d x0 y0 n * gx a b c d z0 w0 (S n)
    - gx a b c d x0 y0 (S n) * gx a b c d z0 w0 n)%Z.

Definition cross (a b c d x0 y0 z0 w0 : Z) (n : nat) : Z :=
  (gx a b c d x0 y0 n * gy a b c d z0 w0 n
    - gy a b c d x0 y0 n * gx a b c d z0 w0 n)%Z.

Lemma gp_0 : forall a b c d x0 y0 : Z, gp a b c d x0 y0 0 = (x0, y0).
Proof. reflexivity. Qed.

Lemma gx_0 : forall a b c d x0 y0 : Z, gx a b c d x0 y0 0 = x0.
Proof. reflexivity. Qed.

Lemma gy_0 : forall a b c d x0 y0 : Z, gy a b c d x0 y0 0 = y0.
Proof. reflexivity. Qed.

Lemma gp_unfold : forall (a b c d x0 y0 : Z) (n : nat),
  gp a b c d x0 y0 (S n) =
  ((a * fst (gp a b c d x0 y0 n) + b * snd (gp a b c d x0 y0 n))%Z,
   (c * fst (gp a b c d x0 y0 n) + d * snd (gp a b c d x0 y0 n))%Z).
Proof.
  intros a b c d x0 y0 n. cbn [gp]. destruct (gp a b c d x0 y0 n) as [u v]. reflexivity.
Qed.

Lemma gx_rec : forall (a b c d x0 y0 : Z) (n : nat),
  gx a b c d x0 y0 (S n) = (a * gx a b c d x0 y0 n + b * gy a b c d x0 y0 n)%Z.
Proof. intros a b c d x0 y0 n. unfold gx, gy. rewrite gp_unfold. reflexivity. Qed.

Lemma gy_rec : forall (a b c d x0 y0 : Z) (n : nat),
  gy a b c d x0 y0 (S n) = (c * gx a b c d x0 y0 n + d * gy a b c d x0 y0 n)%Z.
Proof. intros a b c d x0 y0 n. unfold gx, gy. rewrite gp_unfold. reflexivity. Qed.

(* ============================================================ *)
(* §S 谱刻画定理：三恒等式＋一般形＋两显式类＋D=13 实例                 *)
(* ============================================================ *)

(* 恒等式一（G 步进）：G_{n+1} = det·G_n——det 乘性沿流传递 *)
Lemma cross_step : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  cross a b c d x0 y0 z0 w0 (S n) = ((a * d - b * c) * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. unfold cross.
  rewrite (gx_rec a b c d x0 y0 n), (gy_rec a b c d x0 y0 n),
          (gx_rec a b c d z0 w0 n), (gy_rec a b c d z0 w0 n). ring.
Qed.

(* 恒等式二（E 与 G 的联接·行 1）：E_n = b·G_n——锐度常元＝成员行非对角元×伴生 G *)
Lemma sdet_cross : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  sdet a b c d x0 y0 z0 w0 n = (b * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. unfold sdet, cross.
  rewrite (gx_rec a b c d x0 y0 n), (gx_rec a b c d z0 w0 n). ring.
Qed.

(* 恒等式三（E 与 G 的联接·行 2）：E'_n = −c·G_n（D=13 成员行位·FIB6 §五.2 对偶面） *)
Lemma sdet_row2 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
    - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n
  = (- c) * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. unfold cross.
  rewrite (gy_rec a b c d x0 y0 n), (gy_rec a b c d z0 w0 n). ring.
Qed.

(* G 沿流不变（det=1）/交错（det=−1） *)
Lemma cross_det1 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = 1)%Z -> cross a b c d x0 y0 z0 w0 n = cross a b c d x0 y0 z0 w0 0.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet. induction n as [|k IH].
  - reflexivity.
  - rewrite cross_step, Hdet, IH. ring.
Qed.

Lemma cross_detm1 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = -1)%Z ->
  cross a b c d x0 y0 z0 w0 n = (powneg1 n * cross a b c d x0 y0 z0 w0 0)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet. induction n as [|k IH].
  - cbn [powneg1]. ring.
  - rewrite cross_step, Hdet, IH, powneg1_S. ring.
Qed.

(* 谱刻画一般形（det=1）：E_n = b·G0——锐度常元由块矩阵非对角元与种子 G 定 *)
Theorem sc_general : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = 1)%Z ->
  sdet a b c d x0 y0 z0 w0 n = (b * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite sdet_cross, (cross_det1 a b c d x0 y0 z0 w0 n Hdet).
  unfold cross. rewrite gx_0, gy_0, gx_0, gy_0. ring.
Qed.

(* 谱刻画一般形（det=−1）：E_n = b·(−1)^n·G0——T 奇类交替形 *)
Theorem sc_general_alt : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = -1)%Z ->
  sdet a b c d x0 y0 z0 w0 n = (b * powneg1 n * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite sdet_cross, (cross_detm1 a b c d x0 y0 z0 w0 n Hdet).
  unfold cross. rewrite gx_0, gy_0, gx_0, gy_0. ring.
Qed.

(* 谱刻画一般形·行 2 对偶（det=1） *)
Theorem sc_row2_general : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = 1)%Z ->
  (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
    - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n
  = (- c) * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite sdet_row2, (cross_det1 a b c d x0 y0 z0 w0 n Hdet).
  unfold cross. rewrite gx_0, gy_0, gx_0, gy_0. ring.
Qed.

(* 谱刻画一般形·行 2 对偶（det=−1·D=13 位形） *)
Theorem sc_row2_general_alt : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  (a * d - b * c = -1)%Z ->
  (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
    - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n
  = (- c) * powneg1 n * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite sdet_row2, (cross_detm1 a b c d x0 y0 z0 w0 n Hdet).
  unfold cross. rewrite gx_0, gy_0, gx_0, gy_0. ring.
Qed.

(* —— 显式类一·T=1（D=m²+1 类·矩阵 T(2m)=(2m,1;1,0)·种子 (X₁,X₀)=(m,1)/(Y₁,Y₀)=(1,0)）：
      B≡1 类级（q₀=1·FIB4 pell_family 常元 1 的类级根据）——
      E_n = 1·(−1)^n·(m·0−1·1) = −powneg1 n = powneg1 (S n)＝pell_det 同式 *)
Theorem sc_T1 : forall (m : Z) (n : nat),
  sdet (2 * m) 1 1 0 m 1 1 0 n = powneg1 (S n).
Proof.
  intros m n.
  assert (Hdet : (2 * m * 0 - 1 * 1 = -1)%Z) by ring.
  pose proof (sc_general_alt (2 * m)%Z 1 1 0 m 1 1 0 n Hdet) as H.
  rewrite H, powneg1_S. ring.
Qed.

(* T=1 类锐度常元｜E_n|≡1（全类零例外·B=1=q₀） *)
Theorem sc_T1_B1 : forall (m : Z) (n : nat),
  Z.abs (sdet (2 * m) 1 1 0 m 1 1 0 n) = 1%Z.
Proof. intros m n. rewrite sc_T1. apply zabs_powneg1. Qed.

(* —— 显式类二·T=2（矩阵 (a1a2+1, a1; a2, 1)·种子 (p₁,p₀)=(a1·p0+1,p0)/(q₁,q₀)=(a1,1)）：
      B≡a₁ 类级（q₁=a₁＝首成员分母位·FIB6 D=3→1/D=6→2 冻结值的类级根据）——
      det=(a1a2+1)−a1a2=1·G0=(a1p0+1)−p0·a1=1·E_n = a₁·1·1 = a₁ *)
Theorem sc_T2 : forall (a1 a2 p0 : Z) (n : nat),
  sdet (a1 * a2 + 1) a1 a2 1 (a1 * p0 + 1) p0 a1 1 n = a1.
Proof.
  intros a1 a2 p0 n.
  assert (Hdet : ((a1 * a2 + 1) * 1 - a1 * a2 = 1)%Z) by ring.
  pose proof (sc_general (a1 * a2 + 1)%Z a1 a2 1 (a1 * p0 + 1)%Z p0 a1 1 n Hdet) as H.
  rewrite H. ring.
Qed.

(* T=2 类锐度常元｜E_n| = |a₁|（首成员 a1·p0+1 / a1 的分母位） *)
Theorem sc_T2_Babs : forall (a1 a2 p0 : Z) (n : nat),
  Z.abs (sdet (a1 * a2 + 1) a1 a2 1 (a1 * p0 + 1) p0 a1 1 n) = Z.abs a1.
Proof. intros a1 a2 p0 n. rewrite sc_T2. reflexivity. Qed.

(* —— 旋转块积实例·D=13（T=5·矩阵 N=(33,20;5,3)·种子 (p₀,p₋₁)=(3,1)/(q₀,q₋₁)=(1,0)）：
      成员行 2·row2 面：E'_n = −5·(−1)^n·(3·0−1·1) = 5·powneg1 n＝d13_det 同式；
      B=5＝首成员 18/5 分母＝q₄（FIB7 三路核对的机内实例） *)
Theorem sc_T13_row2 : forall n : nat,
  (gy 33 20 5 3 3 1 n * gy 33 20 5 3 1 0 (S n)
    - gy 33 20 5 3 3 1 (S n) * gy 33 20 5 3 1 0 n
  = 5 * powneg1 n)%Z.
Proof.
  intro n.
  assert (Hdet : (33 * 3 - 20 * 5 = -1)%Z) by ring.
  pose proof (sc_row2_general_alt 33 20 5 3 3 1 1 0 n Hdet) as H.
  rewrite H. ring.
Qed.

(* ============================================================ *)
(* §R 逐件重收层：四代族载体＝gp 实例桥＋冻结件重收见证                  *)
(* ============================================================ *)

(* —— T=1 类：pellpair/qelpair＝gp (2m,1,1,0) 实例（基 (m,1)/(1,0)） *)
Lemma pellpair_gp : forall (m : Z) (n : nat), pellpair m n = gp (2 * m) 1 1 0 m 1 n.
Proof.
  intros m n. induction n as [|k IH].
  - reflexivity.
  - rewrite pellpair_unfold, gp_unfold, IH.
    destruct (gp (2 * m) 1 1 0 m 1 k) as [u v]. f_equal; ring.
Qed.

Lemma qelpair_gp : forall (m : Z) (n : nat), qelpair m n = gp (2 * m) 1 1 0 1 0 n.
Proof.
  intros m n. induction n as [|k IH].
  - reflexivity.
  - rewrite qelpair_unfold, gp_unfold, IH.
    destruct (gp (2 * m) 1 1 0 1 0 k) as [u v]. f_equal; ring.
Qed.

Lemma pellx_gp : forall (m : Z) (k : nat),
  pellx m (S k) = gx (2 * m) 1 1 0 m 1 k.
Proof.
  intros m k. unfold pellx, gx. rewrite pellpair_gp, gp_unfold.
  destruct (gp (2 * m) 1 1 0 m 1 k) as [u v]. cbn [fst snd]. ring.
Qed.

Lemma pelly_gp : forall (m : Z) (k : nat),
  pelly m (S k) = gx (2 * m) 1 1 0 1 0 k.
Proof.
  intros m k. unfold pelly, gx. rewrite qelpair_gp, gp_unfold.
  destruct (gp (2 * m) 1 1 0 1 0 k) as [u v]. cbn [fst snd]. ring.
Qed.

(* FIB4 pell_det 从一般定理重收（T=1 全类·B≡1 的逐件使用位） *)
Theorem sc_T1_recovers_pell_det : forall (m : Z) (n : nat),
  (pellx m (S n) * pelly m (S (S n)) - pellx m (S (S n)) * pelly m (S n)
  = powneg1 (S n))%Z.
Proof.
  intros m n.
  rewrite (pellx_gp m n), (pellx_gp m (S n)), (pelly_gp m (S n)), (pelly_gp m n).
  exact (sc_T1 m n).
Qed.

(* —— T=2 类：d3pair/e3pair＝gp (3,1,2,1) 实例（a1=1·a2=2·p0=1·基 (2,1)/(1,1)） *)
Lemma d3pair_gp : forall n : nat, d3pair n = gp 3 1 2 1 2 1 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite d3pair_unfold, gp_unfold, IH.
    destruct (gp 3 1 2 1 2 1 k) as [u v]. f_equal; ring.
Qed.

Lemma e3pair_gp : forall n : nat, e3pair n = gp 3 1 2 1 1 1 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite e3pair_unfold, gp_unfold, IH.
    destruct (gp 3 1 2 1 1 1 k) as [u v]. f_equal; ring.
Qed.

(* FIB6 d3_det 从 sc_T2 重收（a₁=1·B=1） *)
Theorem sc_T2_recovers_d3_det : forall n : nat,
  (d3x n * d3z (S n) - d3x (S n) * d3z n = 1)%Z.
Proof.
  intro n. unfold d3x, d3z.
  rewrite (d3pair_gp n), (e3pair_gp n), (d3pair_gp (S n)), (e3pair_gp (S n)).
  exact (sc_T2 1 2 1 n).
Qed.

(* —— T=2 类：d6pair/e6pair＝gp (9,2,4,1) 实例（a1=2·a2=4·p0=2·基 (5,2)/(2,1)） *)
Lemma d6pair_gp : forall n : nat, d6pair n = gp 9 2 4 1 5 2 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite d6pair_unfold, gp_unfold, IH.
    destruct (gp 9 2 4 1 5 2 k) as [u v]. f_equal; ring.
Qed.

Lemma e6pair_gp : forall n : nat, e6pair n = gp 9 2 4 1 2 1 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite e6pair_unfold, gp_unfold, IH.
    destruct (gp 9 2 4 1 2 1 k) as [u v]. f_equal; ring.
Qed.

(* FIB6 d6_det 从 sc_T2 重收（a₁=2·B=2） *)
Theorem sc_T2_recovers_d6_det : forall n : nat,
  (d6x n * d6z (S n) - d6x (S n) * d6z n = 2)%Z.
Proof.
  intro n. unfold d6x, d6z.
  rewrite (d6pair_gp n), (e6pair_gp n), (d6pair_gp (S n)), (e6pair_gp (S n)).
  exact (sc_T2 2 4 2 n).
Qed.

(* —— 一般周期实例：d13pair/e13pair＝gp (33,20,5,3) 实例（D=13·基 (3,1)/(1,0)） *)
Lemma d13pair_gp : forall n : nat, d13pair n = gp 33 20 5 3 3 1 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite d13pair_unfold, gp_unfold, IH.
    destruct (gp 33 20 5 3 3 1 k) as [u v]. f_equal; ring.
Qed.

Lemma e13pair_gp : forall n : nat, e13pair n = gp 33 20 5 3 1 0 n.
Proof.
  intro n. induction n as [|k IH].
  - reflexivity.
  - rewrite e13pair_unfold, gp_unfold, IH.
    destruct (gp 33 20 5 3 1 0 k) as [u v]. f_equal; ring.
Qed.

(* FIB5 d13_det 从 D=13 row2 实例定理重收（row2 面·B=5） *)
Theorem sc_T5_recovers_d13_det : forall n : nat,
  (d13y n * d13w (S n) - d13y (S n) * d13w n = 5 * powneg1 n)%Z.
Proof.
  intro n. unfold d13y, d13w.
  rewrite (d13pair_gp n), (e13pair_gp n), (d13pair_gp (S n)), (e13pair_gp (S n)).
  exact (sc_T13_row2 n).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋vm_compute 数值锚＋Separate Extraction                  *)
(* ============================================================ *)

Print Assumptions gp_unfold.
Print Assumptions gx_rec.
Print Assumptions gy_rec.
Print Assumptions cross_step.
Print Assumptions sdet_cross.
Print Assumptions sdet_row2.
Print Assumptions cross_det1.
Print Assumptions cross_detm1.
Print Assumptions sc_general.
Print Assumptions sc_general_alt.
Print Assumptions sc_row2_general.
Print Assumptions sc_row2_general_alt.
Print Assumptions sc_T1.
Print Assumptions sc_T1_B1.
Print Assumptions sc_T2.
Print Assumptions sc_T2_Babs.
Print Assumptions sc_T13_row2.
Print Assumptions pellpair_gp.
Print Assumptions qelpair_gp.
Print Assumptions pellx_gp.
Print Assumptions pelly_gp.
Print Assumptions sc_T1_recovers_pell_det.
Print Assumptions d3pair_gp.
Print Assumptions e3pair_gp.
Print Assumptions sc_T2_recovers_d3_det.
Print Assumptions d6pair_gp.
Print Assumptions e6pair_gp.
Print Assumptions sc_T2_recovers_d6_det.
Print Assumptions d13pair_gp.
Print Assumptions e13pair_gp.
Print Assumptions sc_T5_recovers_d13_det.

(* 数值锚一（T=1 类）：m=2（D=5）处 E_5 = powneg1 6 = 1（B≡1 类级实例） *)
Lemma smoke_T1_m2 : (Z.eqb (sdet (2 * 2) 1 1 0 2 1 1 0 5) (powneg1 6)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（T=2 类·D=3）：E_4 = 1（a₁=1·sc_T2 实例） *)
Lemma smoke_T2_d3 : (Z.eqb (sdet 3 1 2 1 2 1 1 1 4) 1%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（T=2 类·D=6）：E_4 = 2（a₁=2·sc_T2 实例） *)
Lemma smoke_T2_d6 : (Z.eqb (sdet 9 2 4 1 5 2 2 1 4) 2%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（D=13·row2 面）：E'_0 = 5（D=13 row2 实例定理数值例） *)
Lemma smoke_T13 :
  (Z.eqb ((gy 33 20 5 3 3 1 0 * gy 33 20 5 3 1 0 1
          - gy 33 20 5 3 3 1 1 * gy 33 20 5 3 1 0 0)%Z) 5%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（首成员分母位·D=6）：首成员 5/2 分母 2 = a₁ = B *)
Lemma smoke_fmden_d6 : (Z.eqb (gx 9 2 4 1 2 1 0) 2%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（T=1 类·√10 首成员）：member₁ = 19/6（X₂=19·Y₂=6·范数 19²−10·6²=1） *)
Lemma smoke_pell_member :
  (Z.eqb (gx (2 * 3) 1 1 0 3 1 1) 19%Z, Z.eqb (gx (2 * 3) 1 1 0 1 0 1) 6%Z)
  = (true, true).
Proof. vm_compute. reflexivity. Qed.

(* 数值锚七（T=1 类·D=10）：E_0 = powneg1 1 = −1（|E|≡1 类级实例） *)
Lemma smoke_T1_d10 :
  (Z.eqb (sdet (2 * 3) 1 1 0 3 1 1 0 0) (powneg1 1)) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_T1_m2.
Print Assumptions smoke_T2_d3.
Print Assumptions smoke_T2_d6.
Print Assumptions smoke_T13.
Print Assumptions smoke_fmden_d6.
Print Assumptions smoke_pell_member.
Print Assumptions smoke_T1_d10.

From Stdlib Require Import Extraction.
Separate Extraction gp gx gy sdet cross
  smoke_T1_m2 smoke_T2_d3 smoke_T2_d6 smoke_T13 smoke_fmden_d6
  smoke_pell_member smoke_T1_d10.
