(* ===================================================================== *)
(*  u5c_ln2_s5e_hbint.v —— ln2 件② Hbint 整性肢                             *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_s5e_hbint。                                           *)
(*  使命：A' 清分母重缩放的 B' 整性机器证明——                              *)
(*      s5e_hbint : forall n, sigT (fun z:Z => QeqT (s5d_bq n) (z#1))       *)
(*    即 B'_n = Λ_n·2^{n+1}·bv_p n ∈ Z（Λ_n := hl_lcm_upto n = lcm(1..n)）。 *)
(*    这是 A' 清分母改道路径的钥匙肢：B' 整位到手后，勘录②                  *)
(*    恒等式的 B 伴位在正典实例即可为 Z。                                   *)
(*  实现注记（逐项分母吸收）：                                             *)
(*    bv_p n = -Σ_{j≤2n, j≠n} c_j·(2^{j−n}−1)/(j−n)（Laurent 系数和）。     *)
(*    逐 j≠n（|j−n|≤n≤2n）：                                               *)
(*    · j>n：2^{j−n}−1 为整值；(j−n) | Λ（hl_lcm_divide_all），             *)
(*      故 Λ·2^{n+1}·该项 = x·c_j·(2^{j−n}−1)∈Z（s5e_alg_pos）。            *)
(*    · j<n：2^{j−n}−1 = (1−2^{n−j})/2^{n−j}，分母 2 幂被 A 吸收            *)
(*      （A = pw·(y·x)，y:=j−n、pw:=2^{n−j}，s5e_alg_neg 一次吸收双分母）。  *)
(*    · bv_c n j ∈ Z（s5e_bvc_Z：negpow×bk_psQ 整值和）。                   *)
(*    Q 层等式一律 Qeq 面 cross-multiplication（unfold Qeq + cbn + ring，   *)
(*    BeukersLists 正典惯用法）；Qeq 传递/消去自制小件（池无 Qeq_trans）。   *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、HansonLcm、           *)
(*    BeukersLists、BeukersVariant、abl_ln2_reorder、abl_ln2_tail_bound、   *)
(*    u5c_ln2_gap2_bridge、u5c_ln2_s5d_shape、u5c_ln2_s5c_supply；          *)
(*    Stdlib：QArith/Qabs/ZArith/Arith/Lia/Setoid/Qfield。                  *)
(*  对标：abl_ln2_reorder_assembly 勘录②恒等式面；s5d_bq 冻结定义位        *)
(*    （u5c_ln2_s5d_shape）；HansonLcm 整除机（hl_lcm_divide_all）。        *)
(*  数值锚（精确有理算术全量独立复算在卷）：                                *)
(*    Λ_n·2^{n+1}·bv_p n ∈ Z 于 n=0..12 全 PASS（另 2^{n+1}bv_p n 于       *)
(*    n≥3 多数非整＝障碍表复现一致；未缩放 Λ_n·bv_p n 于 n≤12 亦整          *)
(*    ——机证取 Λ·2^{n+1} 档（与 s5d_bq 冻结定义逐字对齐），Λ 单档另账）。   *)
(*  构造性注记：零承认、零经典逻辑；主语句 sigT/Set 承载；ZQ 谓词为 Prop    *)
(*    推理脚手架（HansonLcm le/hl_le_t 桥先例）。                           *)
(*  诚实边界：本件只铸件② Hbint；件① Gosper 承载肢（勘录②闭式合一）       *)
(*    仍为供给链主缺口；件③ s5d 六肢合流与件④去参数化收束在合流前          *)
(*    另件承建。solver 登记：lia/nia 计量位（Z 线性/单项式整性，辅助面）；   *)
(*    主定理 s5e_hbint 收尾为 QeqT 构造链非 solver。                        *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_s5e_hbint.v     *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import HansonLcm.
Require Import BeukersLists.
Require Import BeukersVariant.
Require Import abl_ln2_reorder.
Require Import abl_ln2_tail_bound.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_s5d_shape.
Require Import u5c_ln2_s5c_supply.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 ZQ 载体（Prop 脚手架）与 Q 算术小件                                  *)
(* ============================================================ *)

Definition s5e_Zq (q : Q) : Set := sigT (fun z : Z => Qeq q ((z # 1)%Q)).

(* Qfield 以 Qeq 为 morphism 注册 Q 环：纯环运算形 = setoid-ring；
   Qmake 形等式 = unfold Qeq 交叉相乘（BeukersLists 正典） *)
Ltac s5e_qring := ring.
Ltac s5e_qxmult := unfold Qeq; cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul]; ring.

Lemma s5e_Zq_z : forall z : Z, s5e_Zq ((z # 1)%Q).
Proof. intro z. exists z. reflexivity. Qed.

Lemma s5e_Zq_add : forall a b : Q, s5e_Zq a -> s5e_Zq b -> s5e_Zq (a + b)%Q.
Proof.
  intros a b [za Ea] [zb Eb]. exists (za + zb)%Z.
  setoid_rewrite Ea. setoid_rewrite Eb. s5e_qxmult.
Qed.

Lemma s5e_zmul_zq : forall x y : Z, Qeq ((x # 1) * (y # 1))%Q (((x * y)%Z) # 1)%Q.
Proof. intros x y. reflexivity. Qed.

Lemma s5e_Zq_mul : forall a b : Q, s5e_Zq a -> s5e_Zq b -> s5e_Zq (a * b)%Q.
Proof.
  intros a b [za Ea] [zb Eb]. exists (za * zb)%Z.
  setoid_rewrite Ea. setoid_rewrite Eb. apply s5e_zmul_zq.
Qed.

Lemma s5e_Zq_neg : forall a : Q, s5e_Zq a -> s5e_Zq ((- a)%Q).
Proof.
  intros a [za Ea]. exists (Z.opp za). setoid_rewrite Ea. s5e_qxmult.
Qed.

Lemma s5e_qeqT_zq : forall (z : Z) (q : Q), Qeq q ((z # 1)%Q) -> QeqT q ((z # 1)%Q).
Proof. intros z q H. apply qeq_imp_qeqT. exact H. Qed.

Lemma s5e_z2nat_id : forall d : nat, Z.to_nat (Z.of_nat d) = d.
Proof.
  intro d. apply Nat2Z.inj.
  apply (Z2Nat.id (Z.of_nat d)).
  apply Nat2Z.is_nonneg.
Qed.

Lemma s5e_qpow1 : forall m : nat, q_pow (1 # 1)%Q m == 1%Q.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. s5e_qring.
Qed.

Lemma s5e_qpow2_Zexpl : forall m : nat,
  Qeq (q_pow (2 # 1)%Q m) ((Z.of_nat (2 ^ m)) # 1)%Q.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite Nat2Z.inj_mul. rewrite IH. reflexivity.
Qed.

(* Qeq 传递（自制：池无 Qeq_trans；Z 面 Qden 正性消去承载） *)
Lemma s5e_zmul_cancel_r : forall X Y p : Z,
  p <> 0%Z -> (X * p)%Z = (Y * p)%Z -> X = Y.
Proof.
  intros X Y p Hp Heq.
  assert (E : ((X - Y) * p)%Z = 0%Z).
  { replace ((X - Y) * p)%Z with ((X * p - Y * p)%Z) by ring. lia. }
  apply Z.mul_eq_0 in E.
  destruct E as [E | E].
  - lia.
  - exfalso. apply Hp. exact E.
Qed.

Lemma s5e_qeq_trans : forall a b c : Q, Qeq a b -> Qeq b c -> Qeq a c.
Proof.
  intros a b c H1 H2. unfold Qeq in H1, H2.
  assert (Hd : Z.pos (Qden b) <> 0%Z).
  { intro E. pose proof (Pos2Z.is_pos (Qden b)). lia. }
  apply (s5e_zmul_cancel_r (Qnum a * Z.pos (Qden c))%Z
                           (Qnum c * Z.pos (Qden a))%Z
                           (Z.pos (Qden b)) Hd).
  assert (E3 : (Qnum a * (Z.pos (Qden b) * Z.pos (Qden c)) =
                Qnum c * (Z.pos (Qden b) * Z.pos (Qden a)))%Z).
  { transitivity ((Qnum a * Z.pos (Qden b)) * Z.pos (Qden c))%Z.
    - ring.
    - transitivity ((Qnum b * Z.pos (Qden a)) * Z.pos (Qden c))%Z.
      + rewrite H1. reflexivity.
      + transitivity ((Qnum b * Z.pos (Qden c)) * Z.pos (Qden a))%Z.
        * ring.
        * transitivity ((Qnum c * Z.pos (Qden b)) * Z.pos (Qden a))%Z.
          -- rewrite H2. reflexivity.
          -- ring. }
  transitivity (Qnum a * (Z.pos (Qden b) * Z.pos (Qden c)))%Z.
  - ring.
  - transitivity (Qnum c * (Z.pos (Qden b) * Z.pos (Qden a)))%Z.
    + exact E3.
    + ring.
Qed.

(* s5e_Zq 的 Qeq 迁移（rewrite 不可穿透 s5e_Zq——无 morphism，走 compat） *)
Lemma s5e_Zq_compat : forall q q' : Q, Qeq q q' -> s5e_Zq q -> s5e_Zq q'.
Proof.
  intros q q' H [z Ez]. exists z.
  apply (s5e_qeq_trans q' q ((z # 1)%Q)); [apply (Qeq_sym _ _ H) | exact Ez].
Qed.

Lemma s5e_psQ1_Z : forall (N : nat) (f : nat -> Q),
  (forall k : nat, (k < N)%nat -> s5e_Zq (f k)) ->
  s5e_Zq (bk_psQ f N 1%Q).
Proof.
  intros N f. induction N as [| m IHN]; intro H.
  - exists 0%Z. cbn [bk_psQ]. reflexivity.
  - cbn [bk_psQ].
    apply (s5e_Zq_compat
             (bk_psQ f m 1%Q + f m)%Q
             (bk_psQ f m 1%Q + f m * q_pow (1 # 1)%Q m)%Q).
    + rewrite s5e_qpow1. rewrite Qmult_1_r. reflexivity.
    + apply s5e_Zq_add.
      * apply IHN. intros k Hk. apply H. lia.
      * apply H. lia.
Qed.

Lemma s5e_psQ_scal : forall (N : nat) (c : Q) (g : nat -> Q),
  Qeq (c * bk_psQ g N 1%Q)%Q (bk_psQ (fun k : nat => (c * g k)%Q) N 1%Q).
Proof.
  intros N c g. induction N as [| m IH].
  - cbn [bk_psQ]. s5e_qring.
  - cbn [bk_psQ].
    apply (s5e_qeq_trans _
             (c * bk_psQ g m 1%Q + c * (g m * q_pow (1 # 1)%Q m))%Q).
    + s5e_qring.
    + rewrite IH. s5e_qring.
Qed.

(* ============================================================ *)
(* §1 bv_c 整值与分母吸收代数                                              *)
(* ============================================================ *)

Lemma s5e_bvneg_Z : forall k : nat, s5e_Zq (bv_negpow k).
Proof.
  induction k as [| k IH].
  - exists 1%Z. reflexivity.
  - destruct IH as [z Ez]. exists (Z.opp z). unfold bv_negpow.
    setoid_rewrite Ez. s5e_qxmult.
Qed.

Lemma s5e_bvc_Z : forall n j : nat, s5e_Zq (bv_c n j).
Proof.
  intros n j. unfold bv_c.
  apply s5e_Zq_mul.
  - apply s5e_bvneg_Z.
  - apply s5e_psQ1_Z. intros k Hk. cbv beta.
    destruct (andb (Nat.leb k n) (Nat.leb (j - k) n)) eqn:Ec.
    + apply (s5e_Zq_mul ((Z.of_nat (bkC n k * bkC n (j - k))) # 1)%Q
                        (q_pow (2 # 1)%Q (n - (j - k)))).
      * apply s5e_Zq_z.
      * apply (s5e_Zq_compat ((Z.of_nat (2 ^ (n - (j - k)))) # 1)
                             (q_pow (2 # 1)%Q (n - (j - k)))
                             (Qeq_sym _ _ (s5e_qpow2_Zexpl (n - (j - k))))).
        exists (Z.of_nat (2 ^ (n - (j - k)))). reflexivity.
    + exists 0%Z. cbv iota. reflexivity.
Qed.

(* Qmake 三元积等式（Z 环面交叉相乘） *)
Lemma s5e_zq_prod3 : forall x y pw : Z,
  Qeq (((x * y * (pw - 1))%Z # 1)%Q)
      (((x # 1)%Q * ((y # 1)%Q * ((pw # 1)%Q - 1%Q)%Q))%Q).
Proof.
  intros x y pw. s5e_qxmult.
Qed.

Lemma s5e_zq_prod4 : forall x pw zc : Z,
  Qeq (((x * zc * (1 - pw))%Z # 1)%Q)
      ((((x # 1)%Q - ((pw * x)%Z # 1)%Q)%Q * ((zc # 1)%Q))%Q).
Proof.
  intros x pw zc. s5e_qxmult.
Qed.

(* 非零 Z 元的 (y#1) 非零（Qeq 面） *)
Lemma s5e_z1_nz : forall y : Z, y <> 0%Z -> ~ ((y # 1)%Q == 0%Q)%Q.
Proof.
  intros y Hy E. apply Hy.
  unfold Qeq in E. cbn [Qnum Qden Qmult] in E.
  rewrite !Z.mul_1_r in E. exact E.
Qed.

Lemma s5e_qinv_one : forall y : Z, y <> 0%Z ->
  ((y # 1)%Q * Qinv ((y # 1)%Q))%Q == 1%Q.
Proof. intros y Hy. apply Qmult_inv_r. apply s5e_z1_nz. exact Hy. Qed.

(* 分母消去律：((y·x)#1)·(1/(y#1)) == (x#1)（y≠0） *)
Lemma s5e_div_cancel : forall y x : Z, y <> 0%Z ->
  Qeq (((y * x)%Z # 1)%Q * Qinv ((y # 1)%Q)) ((x # 1)%Q).
Proof.
  intros y x Hy.
  assert (Einv := s5e_qinv_one y Hy).
  assert (E1 : Qeq ((x # 1)%Q)
                   (((x # 1)%Q * ((y # 1)%Q * Qinv ((y # 1)%Q)))%Q)).
  { setoid_rewrite Einv. exact (Qeq_sym _ _ (Qmult_1_r ((x # 1)%Q))). }
  assert (E2 : Qeq (((x # 1)%Q * ((y # 1)%Q * Qinv ((y # 1)%Q)))%Q)
                   ((((x # 1)%Q * ((y # 1)%Q)) * Qinv ((y # 1)%Q))%Q)) by s5e_qring.
  assert (E3 : Qeq (((x # 1)%Q * ((y # 1)%Q))%Q) (((y * x)%Z # 1)%Q)).
  { unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring. }
  apply (Qeq_sym _ _).
  apply (s5e_qeq_trans _ (((x # 1)%Q * ((y # 1)%Q * Qinv ((y # 1)%Q)))%Q)).
  - exact E1.
  - apply (s5e_qeq_trans _ ((((x # 1)%Q * ((y # 1)%Q)) * Qinv ((y # 1)%Q))%Q)).
    + exact E2.
    + setoid_rewrite E3. reflexivity.
Qed.

(* —— 分母吸收代数两肢（Qeq 构造链·零 solver） —— *)

(* 正支：j>n。A = y·x（y:=j−n 消去）⟹ A·c·(2^{j−n}−1)/y == x·c·(2^{j−n}−1) *)
Lemma s5e_alg_pos : forall (A y x pw zc : Z) (c : Q),
  y <> 0%Z -> A = (y * x)%Z -> Qeq c ((zc # 1)%Q) ->
  Qeq (((A)%Z # 1)%Q * (c * (((pw # 1)%Q - 1%Q) / ((y # 1)%Q))))%Q
      (((x * zc * (pw - 1))%Z # 1)%Q).
Proof.
  intros A y x pw zc c Hy0 HA Hc.
  setoid_rewrite Hc. rewrite HA.
  pose proof (qeqT_imp_qeq _ _ (s5c_qdiv_mult ((pw # 1)%Q - 1%Q)%Q ((y # 1)%Q))) as T1.
  setoid_rewrite T1.
  pose proof (s5e_div_cancel y x Hy0) as Ec.
  apply (s5e_qeq_trans _
           ((((y * x)%Z # 1)%Q * Qinv ((y # 1)%Q) *
             (((zc # 1)%Q) * (((pw # 1)%Q - 1%Q)%Q)))%Q)).
  - s5e_qring.
  - apply (s5e_qeq_trans _
             (((x # 1)%Q * ((zc # 1)%Q * (((pw # 1)%Q - 1%Q)%Q)))%Q)).
    + setoid_rewrite Ec. s5e_qring.
    + apply (Qeq_sym _ _ (s5e_zq_prod3 x zc pw)).
Qed.

(* 负支：j<n。A = pw·(y·x)（y:=j−n 消去，pw:=2^{n−j} 被 A 吸收）
   ⟹ A·c·((1/pw − 1)/y) == x·c·(1−pw) *)
Lemma s5e_alg_neg : forall (A y x pw zc : Z) (c : Q),
  y <> 0%Z -> pw <> 0%Z -> A = (pw * (y * x))%Z -> Qeq c ((zc # 1)%Q) ->
  Qeq (((A)%Z # 1)%Q
         * (c * ((((1 # 1)%Q / ((pw # 1)%Q))%Q - 1%Q)%Q / ((y # 1)%Q))))%Q
      (((x * zc * (1 - pw))%Z # 1)%Q).
Proof.
  intros A y x pw zc c Hy0 Hpw0 HA Hc.
  setoid_rewrite Hc. rewrite HA.
  pose proof (qeqT_imp_qeq _ _
    (s5c_qdiv_mult (((1 # 1)%Q / ((pw # 1)%Q))%Q - 1%Q)%Q ((y # 1)%Q))) as T1.
  setoid_rewrite T1.
  pose proof (qeqT_imp_qeq _ _ (s5c_qdiv_mult (1 # 1)%Q ((pw # 1)%Q))) as T2.
  setoid_rewrite T2.
  pose proof (s5e_div_cancel pw (y * x) Hpw0) as Ecp.
  pose proof (s5e_div_cancel y x Hy0) as Ecy.
  pose proof (s5e_div_cancel y (pw * x) Hy0) as Ecy2.
  assert (Eassoc : Qeq (((pw * (y * x))%Z # 1)%Q)
                        (((y * (pw * x))%Z # 1)%Q))
    by (unfold Qeq; cbn [Qnum Qden Qmult Pos.mul]; ring).
  apply (s5e_qeq_trans _
    ((((pw * (y * x))%Z # 1)%Q * Qinv ((pw # 1)%Q)
      - ((pw * (y * x))%Z # 1)%Q)%Q
      * (((zc # 1)%Q) * Qinv ((y # 1)%Q)))%Q).
  - s5e_qring.
  - setoid_rewrite Ecp.
    apply (s5e_qeq_trans _
      (((((y * x)%Z # 1)%Q * Qinv ((y # 1)%Q)
         - ((y * (pw * x))%Z # 1)%Q * Qinv ((y # 1)%Q))%Q
        * ((zc # 1)%Q))%Q)).
    + setoid_rewrite Eassoc. s5e_qring.
    + setoid_rewrite Ecy2. setoid_rewrite Ecy.
      apply (Qeq_sym _ _ (s5e_zq_prod4 x pw zc)).
Qed.

(* Qinv 迁移与 1/X 分母兼容（QeqT 面） *)
Lemma s5e_qinv_comp : forall X Y : Q, ~ (X == 0%Q)%Q -> Qeq X Y -> Qeq (Qinv X) (Qinv Y).
Proof.
  intros X Y HX0 H.
  pose proof (Qmult_inv_r X HX0) as EX.
  assert (EY : (Y * Qinv Y)%Q == 1%Q).
  { apply Qmult_inv_r. intro E0. apply HX0.
    exact (s5e_qeq_trans X Y 0%Q H E0). }
  assert (Hm : Qeq (Qinv X * Y) (Qinv X * X)).
  { pose proof (s5c_qeqT_mult_r (Qinv X) Y X
                  (qeq_imp_qeqT _ _ (Qeq_sym _ _
                     (qeqT_imp_qeq _ _ (qeq_imp_qeqT _ _ H))))) as HT.
    apply qeqT_imp_qeq.
    apply (gap2_qeqT_trans _ (Y * Qinv X)%Q).
    - apply qeq_imp_qeqT. ring.
    - apply (gap2_qeqT_trans _ (X * Qinv X)%Q).
      + exact HT.
      + apply qeq_imp_qeqT. ring. }
  apply (s5e_qeq_trans _ (Qinv X * 1%Q)%Q).
  - ring.
  - apply (s5e_qeq_trans _ ((Qinv X * Y) * Qinv Y)%Q).
    + rewrite <- EY. ring.
    + apply (s5e_qeq_trans _ ((Qinv X * X) * Qinv Y)%Q).
      * exact (qeqT_imp_qeq _ _ (s5c_qeqT_mult_r (Qinv Y) (Qinv X * Y)
                   (Qinv X * X) (qeq_imp_qeqT _ _ Hm))).
      * apply (s5e_qeq_trans _ (1%Q * Qinv Y)%Q).
        -- apply (s5e_qeq_trans _ ((X * Qinv X) * Qinv Y)%Q).
           ++ ring.
           ++ rewrite EX. ring.
        -- ring.
Qed.

Lemma s5e_qeqT_mult_l : forall c a b : Q, QeqT a b -> QeqT (c * a) (c * b).
Proof.
  intros c a b H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ H) as Hq. setoid_rewrite Hq. reflexivity.
Qed.

Lemma s5e_qdiv1_compat : forall X Y : Q, ~ (X == 0%Q)%Q -> QeqT X Y ->
  QeqT ((1 # 1)%Q / X) ((1 # 1)%Q / Y).
Proof.
  intros X Y HX0 H.
  pose proof (s5c_qdiv_mult (1 # 1)%Q X) as T1.
  pose proof (s5c_qdiv_mult (1 # 1)%Q Y) as T2.
  pose proof (s5e_qinv_comp X Y HX0 (qeqT_imp_qeq _ _ H)) as HQ.
  apply (gap2_qeqT_trans _ ((1 # 1)%Q * Qinv X)%Q).
  - exact T1.
  - apply (gap2_qeqT_trans _ ((1 # 1)%Q * Qinv Y)%Q).
    + exact (s5e_qeqT_mult_l (1 # 1)%Q (Qinv X) (Qinv Y)
               (qeq_imp_qeqT _ _ HQ)).
    + exact (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ T2))).
Qed.

(* ============================================================ *)
(* §2 bv_q2 分支迁移与 2 幂整除 witness                                    *)
(* ============================================================ *)

Lemma s5e_bvq2_pos : forall d : nat,
  QeqT (bv_q2 (Z.of_nat d)) (q_pow (2 # 1)%Q d).
Proof.
  intro d. unfold bv_q2.
  destruct (Z.leb 0 (Z.of_nat d)) eqn:Eb.
  - rewrite s5e_z2nat_id. cbv iota. apply qeq_imp_qeqT. reflexivity.
  - exfalso. apply (proj1 (Z.leb_gt _ _)) in Eb.
    pose proof (Nat2Z.is_nonneg d). lia.
Qed.

Lemma s5e_bvq2_neg : forall a b : nat, a < b ->
  QeqT (bv_q2 (Z.of_nat a - Z.of_nat b)%Z) (1 / q_pow (2 # 1)%Q (b - a))%Q.
Proof.
  intros a b Hlt. unfold bv_q2.
  destruct (Z.leb 0 (Z.of_nat a - Z.of_nat b)) eqn:Eb.
  - exfalso. apply Z.leb_le in Eb.
    assert (Z.of_nat a < Z.of_nat b)%Z by (apply Nat2Z.inj_lt; exact Hlt).
    lia.
  - replace (Z.opp (Z.of_nat a - Z.of_nat b)) with (Z.of_nat (b - a))%Z
      by (assert (Hs : (Z.of_nat (b - a) = Z.of_nat b - Z.of_nat a)%Z)
            by (apply Nat2Z.inj_sub; lia); lia).
    rewrite s5e_z2nat_id. cbv iota. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma s5e_pow2_divide : forall a b : nat, a <= b ->
  sigT (fun q : nat => 2 ^ a * q = 2 ^ b)%nat.
Proof.
  intros a b H. exists (2 ^ (b - a)).
  rewrite <- Nat.pow_add_r.
  replace (a + (b - a))%nat with b by lia. reflexivity.
Qed.

(* m | Λ(n) 的 sigT 见证（mod 判定桥：Prop 整除知识只用于 Prop 面矛盾，
   见证本体由 Nat.div_mod 可计算式承载——Set 承载律合规） *)
Lemma s5e_lcm_divide_sigt : forall n m : nat, (1 <= m)%nat -> (m <= n)%nat ->
  sigT (fun q : nat => hl_lcm_upto n = q * m)%nat.
Proof.
  intros n m H1 H2.
  assert (Hne : (m <> 0)%nat) by lia.
  pose proof (Nat.div_mod (hl_lcm_upto n) m Hne) as Hdm.
  destruct (Nat.eq_dec (hl_lcm_upto n mod m) 0) as [Ez | Enz].
  - exists (hl_lcm_upto n / m). rewrite Ez, Nat.add_0_r in Hdm.
    set (q := hl_lcm_upto n / m) in *. rewrite Hdm. symmetry.
    exact (Nat.mul_comm q m).
  - exfalso.
    pose proof (hl_lcm_divide_all n m H1 H2) as Hd.
    destruct Hd as [t Ht].
    rewrite Ht in Enz. rewrite Nat.mod_mul in Enz by exact Hne.
    exfalso. apply Enz. reflexivity.
Qed.

(* ============================================================ *)
(* §3 逐项整性（j≠n 双支）                                                 *)
(* ============================================================ *)

Lemma s5e_term_nz : forall (n k : nat), k <> n -> (k <= 2 * n)%nat ->
  s5e_Zq (((Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n)) # 1)%Q *
          (bv_c n k * ((bv_q2 (Z.of_nat k - Z.of_nat n)%Z - 1%Q) /
                       ((Z.of_nat k - Z.of_nat n)%Z # 1))%Q)).
Proof.
  intros n k Hne Hle2.
  destruct (lt_eq_lt_dec k n) as [[Hlt | Heq] | Hgt].
  - (* ---- 负支 k<n：分母 (j−n)·2^{n−j} 全被 A=Λ·2^{n+1} 吸收 ---- *)
    assert (Hm1 : (1 <= n - k)%nat) by lia.
    assert (Hmk : (n - k <= n)%nat) by lia.
    destruct (s5e_lcm_divide_sigt n (n - k) Hm1 Hmk) as [qn Hqn].
    destruct (s5e_pow2_divide (n - k) (Datatypes.S n)
                 (Nat.le_trans (n - k) n (Datatypes.S n) Hmk (Nat.le_succ_diag_r n))) as [q0 Hp0].
    destruct (s5e_bvc_Z n k) as [zc Hzc].
    assert (Harg : (Z.of_nat k - Z.of_nat n)%Z = (- Z.of_nat (n - k))%Z).
    { assert (Hs : (Z.of_nat (n - k) = Z.of_nat n - Z.of_nat k)%Z)
        by (apply Nat2Z.inj_sub; lia).
      lia. }
    pose proof (s5e_bvq2_neg k n Hlt) as E2.
    rewrite Harg in E2.
    pose proof (s5e_qpow2_Zexpl (n - k)) as EP.
    assert (E3 : QeqT (bv_q2 (- Z.of_nat (n - k))%Z)
                      ((1 # 1) / ((Z.of_nat (2 ^ (n - k))) # 1))%Q).
    { apply (gap2_qeqT_trans _ (1 / q_pow (2 # 1)%Q (n - k))%Q).
      - exact E2.
      - exact (s5e_qdiv1_compat (q_pow (2 # 1)%Q (n - k))
                                ((Z.of_nat (2 ^ (n - k))) # 1)
                                (fun E0 => (Qlt_not_eq 0%Q
                                              (q_pow (2 # 1)%Q (n - k))
                                              (lnt_pow2_pos (n - k))
                                              (Qeq_sym _ _ E0)))
                                (s5e_qeqT_zq (Z.of_nat (2 ^ (n - k)))
                                             (q_pow (2 # 1)%Q (n - k)) EP)). }
    exists ((- (Z.of_nat qn * Z.of_nat q0)) * zc *
            (1 - Z.of_nat (2 ^ (n - k))))%Z.
    rewrite Harg.
    setoid_rewrite (qeqT_imp_qeq _ _ E3).
    assert (HZ : Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n)
                 = (Z.of_nat (2 ^ (n - k)) *
                    ((- Z.of_nat (n - k)) *
                     (- (Z.of_nat qn * Z.of_nat q0)))%Z)%Z).
    { assert (Hs : (Z.of_nat (n - k) = Z.of_nat n - Z.of_nat k)%Z)
        by (apply Nat2Z.inj_sub; lia).
      unfold s5d_lam. rewrite Nat2Z.inj_mul. rewrite Hqn.
      rewrite !Nat2Z.inj_mul. rewrite <- Hp0.
      rewrite Nat2Z.inj_mul. rewrite Hs. ring. }
    assert (Hy0 : (- Z.of_nat (n - k))%Z <> 0%Z) by lia.
    assert (Hpw0 : (Z.of_nat (2 ^ (n - k)))%Z <> 0%Z).
    { intro E. change (Z.of_nat (2 ^ (n - k)) = Z.of_nat 0)%Z in E.
      apply Nat2Z.inj in E.
      assert (H2 : (2 <> 0)%nat) by lia.
      exact (Nat.pow_nonzero 2 (n - k) H2 E). }
    apply (s5e_alg_neg (Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n))
                       (- Z.of_nat (n - k))%Z
                       (- (Z.of_nat qn * Z.of_nat q0))%Z
                       (Z.of_nat (2 ^ (n - k))) zc (bv_c n k)).
    + exact Hy0.
    + exact Hpw0.
    + exact HZ.
    + exact Hzc.
  - (* ---- j=n：与 k≠n 矛盾 ---- *)
    exfalso. apply Hne. exact Heq.
  - (* ---- 正支 n<k ---- *)
    assert (Hm1 : (1 <= k - n)%nat) by lia.
    assert (Hmn : (k - n <= n)%nat) by lia.
    destruct (s5e_lcm_divide_sigt n (k - n) Hm1 Hmn) as [qn Hqn].
    destruct (s5e_bvc_Z n k) as [zc Hzc].
    assert (Harg : (Z.of_nat k - Z.of_nat n)%Z = Z.of_nat (k - n)) by lia.
    pose proof (s5e_bvq2_pos (k - n)) as E2.
    pose proof (s5e_qpow2_Zexpl (k - n)) as EP.
    assert (E3 : QeqT (bv_q2 (Z.of_nat (k - n)))
                      ((Z.of_nat (2 ^ (k - n))) # 1)%Q).
    { apply (gap2_qeqT_trans _ (q_pow (2 # 1)%Q (k - n))).
      - exact E2.
      - exact (s5e_qeqT_zq (Z.of_nat (2 ^ (k - n)))
                           (q_pow (2 # 1)%Q (k - n)) EP). }
    exists (Z.of_nat (qn * 2 ^ Datatypes.S n) * zc *
            (Z.of_nat (2 ^ (k - n)) - 1))%Z.
    rewrite Harg.
    setoid_rewrite (qeqT_imp_qeq _ _ E3).
    assert (HZ : Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n)
                 = (Z.of_nat (k - n) *
                    Z.of_nat (qn * 2 ^ Datatypes.S n))%Z).
    { unfold s5d_lam. rewrite Nat2Z.inj_mul. rewrite Hqn.
      rewrite !Nat2Z.inj_mul. ring. }
    assert (Hy0 : Z.of_nat (k - n) <> 0%Z) by lia.
    assert (Hpw0 : (Z.of_nat (2 ^ (k - n)))%Z <> 0%Z).
    { intro E. change (Z.of_nat (2 ^ (k - n)) = Z.of_nat 0)%Z in E.
      apply Nat2Z.inj in E.
      assert (H2 : (2 <> 0)%nat) by lia.
      exact (Nat.pow_nonzero 2 (k - n) H2 E). }
    apply (s5e_alg_pos (Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n))
                       (Z.of_nat (k - n))
                       (Z.of_nat (qn * 2 ^ Datatypes.S n))
                       (Z.of_nat (2 ^ (k - n))) zc (bv_c n k)).
    + exact Hy0.
    + exact HZ.
    + exact Hzc.
Qed.

(* ============================================================ *)
(* §4 主定理：Hbint —— B'_n = Λ_n·2^{n+1}·bv_p n ∈ Z                       *)
(* ============================================================ *)

Theorem s5e_hbint : forall n : nat,
  sigT (fun z : Z => QeqT (s5d_bq n) ((z # 1)%Q)).
Proof.
  intro n. unfold s5d_bq, bv_p.
  set (S := ((Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n)) # 1)%Q).
  set (g := fun j : nat =>
              if Nat.eqb j n then 0%Q
              else ((bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                                ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))%Q).
  assert (Hterms : forall k : nat, (k < Datatypes.S (2 * n))%nat ->
            s5e_Zq (S * g k)).
  { intros k Hk. unfold g. cbv beta.
    destruct (Nat.eqb k n) eqn:Ek.
    - cbv iota. exists 0%Z. s5e_qring.
    - apply Nat.eqb_neq in Ek.
      unfold S. apply s5e_term_nz.
      + exact Ek.
      + lia. }
  destruct (s5e_psQ1_Z (Datatypes.S (2 * n)) (fun k : nat => (S * g k)%Q)
             Hterms) as [zs Ez].
  assert (Hscal := s5e_psQ_scal (Datatypes.S (2 * n)) S g).
  exists (Z.opp zs). apply qeq_imp_qeqT.
  apply (s5e_qeq_trans _ ((- (S * bk_psQ g (Datatypes.S (2 * n)) 1))%Q)).
  - s5e_qring.
  - apply (s5e_qeq_trans _
             ((- (bk_psQ (fun k : nat => (S * g k)%Q) (Datatypes.S (2 * n)) 1))%Q)).
    + rewrite <- Hscal. s5e_qring.
    + setoid_rewrite Ez. s5e_qxmult.
Qed.

(* ============================================================ *)
(* §5 RunAlive 数值锚（vm_compute 精确判定·Fractions 独立复算在卷）          *)
(* ============================================================ *)

(* n=3：B'_3 = Λ_3·2⁴·(131/3) = 6·16·131/3 = 4192 ∈ Z（与 s5d_runalive_bq3 一致） *)
Theorem s5e_runalive_z3 : QeqT (s5d_bq 3) ((4192 # 1)%Q).
Proof. exact s5d_runalive_bq3. Qed.

(* n=4：Λ_4=12，bv_p 4 = 445/2（Fractions 独立复算），B'_4 = 12·32·445/2 = 85440 *)
Theorem s5e_runalive_z4 : QeqT (s5d_bq 4) ((85440 # 1)%Q).
Proof. unfold s5d_bq. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §6 提取与假设审计                                                       *)
(* ============================================================ *)

Separate Extraction s5d_bq.

Print Assumptions s5e_hbint.
Print Assumptions s5e_term_nz.
Print Assumptions s5e_runalive_z3.
Print Assumptions s5e_runalive_z4.
