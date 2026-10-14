(* 五字段指针｜使命：Q 层全有理数域装配——非折半线整隙层从 D=2、D=5 特例向任意非平方
   D 一般形的扩张：Hardy-Wright 一步矛盾法（最低项化＋gcd＋Gauss＋floor 界）替代逐素模
   分类，一般形 |a²−D·b²| ≥ 1（b≠0·D 非完全平方）零前提闭式，及 Q 层全有理数域装配
   |(a/b)² − D| ≥ 1/b²（QleT' 全 Set 承载·无需命名 √D）。
   机形（对 B5 b5_machine §G／FIB fib_machine §I·§T／FIB2 fib_norm_gap §N·§G）：
   §F floor 界件：sqrtD_floor——Z.sqrt_spec 桥＋非平方前提（∀c, D≠c²）给
     m² < D < (m+1)²（m := Z.sqrt D）；
   §Z 一般无平方层：genD_no_sqrtZ——Z.abs 归一＋Z.gcd 最低项化
     （Z.gcd_divide_l/r 见证＋Z.div_unique 商还原＋Z.gcd_div_gcd 互素）＋
     floor 界（m·k2 < k1 < (m+1)·k2）＋交叉相乘供给＋Z.gauss 一步矛盾：
     b1 | a1+mb1 ⟹ b1 | a1 ⟹ b1 | u:=a1−mb1 与 0<u<b1 矛盾
     ＋genD_no_sqrtZ_ne（b≠0 形·Z.abs 桥同 FIB2 sqrt5_no_sqrtZ_ne）；
   §M 偶奇非平方实例：sqrt2_nonsquare/sqrt3_nonsquare（Z.Even_or_Odd 分派·
     D ≡ 2,3 (mod 4) 路）＋sqrt5_nonsquare（sqrt5_no_sqrtZ b:=1 直收）；
   §G 一般整隙层：genD_gap（Z 函数计算面）／gen_gapD_ne（b≠0 全称件）／
     gen_gapD_pos（正分母位使用形）／gen_gapD_2·gen_gapD_3·gen_gapD_5
     （D=2/3/5 特例直得——一般形含 B5 |a²−2b²|≥1 与 FIB2 fib2_gap5_ne）；
   §Q 全有理数域装配层：q_square_cross（Qeq 交叉恒等·fib_cross_mult 平方形）＋
     q_square_gap——任意有理数 a/b 的平方与 D 的距离 ≥ 1/b²
     （fib_qleT_congr_r＋fib_qabs_congr＋fib_qle_abs_ge 三桥直拼·零 √D 命名）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚八件（Pell 对 (3,2)/(7,4)/
     (9,4)、floor 界 8、Q 平方隙精确等号 1/4 与严格例 11/9、计算面 genD_gap/
     genD_gapQ 直算）。
   独立复算先行（假件拦截第一道）：整数/Fraction 精确路 ALL PASS
   （floor 界 2..199 全域·非平方 D 零解 2..40 全域＋平方 D 有解对照·整隙 ≥1
   网格·Q 平方隙 Fraction 精确·交叉恒等 4000 例·偶奇实例勘形·范数=1 解画像）。
   依赖：S02_CauchyComplete（QleT'）＋fib_machine（zabs_ge1/fib_qabs_congr/
   fib_qle_abs_ge/fib_qleT_congr_r）＋fib_norm_gap（sqrt5_no_sqrtZ）；Stdlib
   ZArith、Arith、Bool、Lia、QArith、Qabs。
   构造性注记：Z 层反证语句面（-> False）为在册先例形（ir2_no_sqrtZ/
   sqrt5_no_sqrtZ 同位同形的一般化）；唯一前提位 (2 ≤ D)%Z·(∀c, D≠c²)%Z·
   (·<>0)%Z 为 B5/FIB 在册同款先例形；Q 层语句面 QleT' 全 Set 承载；证明体内
   构造性 Prop 推导合法（实质链＝最低项化＋Gauss＋floor 界整除矛盾，终局符号
   分派 nia 计量与 fib_norm_gap_ge1 的 nia 桥同位）；零承认、零 Abort、零全局
   假设、零经典逻辑；定义面透明。
   编译配方：rocq c -native-compiler no -q -Q . "" fib_qdomain.v *)
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_norm_gap.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* §F floor 界件：非平方 D 的 Z.sqrt 两侧严格界                        *)
(* ============================================================ *)

Lemma sqrtD_floor : forall D : Z, (2 <= D)%Z -> (forall c : Z, (D <> c * c)%Z) ->
  (Z.sqrt D * Z.sqrt D < D < Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D))%Z.
Proof.
  intros D HD Hns.
  assert (HD0 : (0 <= D)%Z) by lia.
  pose proof (Z.sqrt_spec D HD0) as H. cbv zeta in H.
  pose proof (Hns (Z.sqrt D)) as Hne.
  split.
  - lia.
  - exact (proj2 H).
Qed.

(* ============================================================ *)
(* §Z 一般无平方层：非平方 D 无有理平方根（最低项化＋Gauss 一步矛盾）      *)
(* ============================================================ *)

Lemma genD_no_sqrtZ : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> (0 < b)%Z -> (a * a = D * (b * b))%Z -> False.
Proof.
  intros D a b HD Hns Hb Heq.
  assert (Hfl := sqrtD_floor D HD Hns).
  pose proof (Z.abs_square a) as Habs.
  assert (Ha0 : (Z.abs a * Z.abs a = D * (b * b))%Z) by (rewrite Habs; exact Heq).
  assert (Ha0p : (0 <= Z.abs a)%Z) by apply Z.abs_nonneg.
  (* 最低项化：g := gcd(|a|, b)，整除见证 k1/k2 *)
  assert (Hg0 : (0 < Z.gcd (Z.abs a) b)%Z).
  { pose proof (Z.gcd_nonneg (Z.abs a) b) as H1.
    assert (H2 : Z.gcd (Z.abs a) b <> 0%Z).
    { intro Hc. apply (Z.gcd_eq_0 (Z.abs a) b) in Hc. lia. }
    lia. }
  pose proof (Z.gcd_div_gcd (Z.abs a) b (Z.gcd (Z.abs a) b)
              (ltac:(lia)) eq_refl) as Hcop0.
  pose proof (Z.gcd_divide_l (Z.abs a) b) as Hda.
  pose proof (Z.gcd_divide_r (Z.abs a) b) as Hdb.
  unfold Z.divide in Hda, Hdb.
  destruct Hda as [k1 Hk1]. destruct Hdb as [k2 Hk2].
  remember (Z.gcd (Z.abs a) b) as g eqn:Eg.
  (* 商还原：a0/g = k1，b/g = k2 *)
  assert (Hq1 : (Z.abs a / g = k1)%Z).
  { symmetry. apply Z.div_unique with (r := 0%Z).
    - left. lia.
    - lia. }
  assert (Hq2 : (b / g = k2)%Z).
  { symmetry. apply Z.div_unique with (r := 0%Z).
    - left. lia.
    - lia. }
  rewrite Hq1, Hq2 in Hcop0.
  (* 方程转移与正性 *)
  assert (Heq1 : (k1 * k1 = D * (k2 * k2))%Z).
  { rewrite Hk1, Hk2 in Ha0. nia. }
  assert (Hk2p : (0 < k2)%Z) by nia.
  assert (Hk1p : (0 < k1)%Z) by nia.
  (* floor 界：m·k2 < k1 < (m+1)·k2 *)
  assert (Hfl2 : (Z.sqrt D * Z.sqrt D < D)%Z) by lia.
  assert (Hfl3 : (D < (Z.sqrt D + 1) * (Z.sqrt D + 1))%Z) by lia.
  remember (Z.sqrt D) as m eqn:Em.
  assert (Hm0 : (0 <= m)%Z) by (rewrite Em; apply Z.sqrt_nonneg).
  assert (Hfb : (m * k2 < k1 < (m + 1) * k2)%Z).
  { split; nia. }
  (* 交叉相乘供给＋Gauss 一步矛盾 *)
  assert (Hcr : (k1 * (k1 + m * k2) = k2 * (m * k1 + D * k2))%Z).
  { replace (k1 * (k1 + m * k2))%Z with (k1 * k1 + m * k1 * k2)%Z by ring.
    rewrite Heq1. ring. }
  assert (Hsup : Z.divide k2 (k1 * (k1 + m * k2))).
  { unfold Z.divide. exists ((m * k1 + D * k2)%Z). lia. }
  assert (Hcop1 : Z.gcd k2 k1 = 1%Z) by (rewrite Z.gcd_comm; exact Hcop0).
  pose proof (Z.gauss k2 k1 (k1 + m * k2) Hsup Hcop1) as Hg1.
  assert (Hdm : Z.divide k2 (m * k2)) by
    (unfold Z.divide; exists (m%Z); ring).
  assert (Hgk1 : Z.divide k2 k1).
  { replace k1%Z with ((k1 + m * k2) + (-(m * k2)))%Z by ring.
    apply Z.divide_add_r. exact Hg1. apply Z.divide_opp_r. exact Hdm. }
  assert (Hgu : Z.divide k2 (k1 - m * k2)).
  { replace (k1 - m * k2)%Z with (k1 + (-(m * k2)))%Z by ring.
    apply Z.divide_add_r. exact Hgk1. apply Z.divide_opp_r. exact Hdm. }
  (* 终局：0 < u < k2 且 k2 | u 不可能 *)
  unfold Z.divide in Hgu. destruct Hgu as [k Hk].
  destruct k as [|p|p].
  - lia.
  - pose proof (Pos2Z.is_pos p). nia.
  - pose proof (Pos2Z.is_pos p). nia.
Qed.

(* b≠0 形（Z.abs 桥·FIB2 sqrt5_no_sqrtZ_ne 同款） *)
Lemma genD_no_sqrtZ_ne : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> b <> 0%Z -> (a * a = D * (b * b))%Z -> False.
Proof.
  intros D a b HD Hns Hb Heq.
  apply (genD_no_sqrtZ D a (Z.abs b) HD Hns).
  - apply Z.abs_pos. exact Hb.
  - rewrite <- (Z.abs_mul b b). rewrite (Z.abs_eq (b * b)) by lia. exact Heq.
Qed.

(* ============================================================ *)
(* §M 偶奇非平方实例（D ≡ 2,3 (mod 4) 路）＋√5 池件直收                  *)
(* ============================================================ *)

Lemma sqrt2_nonsquare : forall c : Z, (2 <> c * c)%Z.
Proof.
  intro c. destruct (Z.Even_or_Odd c) as [[k Hk] | [k Hk]].
  - subst c. lia.
  - subst c. assert (Hx : ((2*k+1)*(2*k+1) = 4*(k*k) + 4*k + 1)%Z) by ring. lia.
Qed.

Lemma sqrt3_nonsquare : forall c : Z, (3 <> c * c)%Z.
Proof.
  intro c. destruct (Z.Even_or_Odd c) as [[k Hk] | [k Hk]].
  - subst c. lia.
  - subst c. assert (Hx : ((2*k+1)*(2*k+1) = 4*(k*k) + 4*k + 1)%Z) by ring. lia.
Qed.

(* 池内 sqrt5_no_sqrtZ 直收（b := 1 一步） *)
Lemma sqrt5_nonsquare : forall c : Z, (5 <> c * c)%Z.
Proof.
  intro c. intro Hc. apply (sqrt5_no_sqrtZ c 1%Z); [ lia | lia ].
Qed.

(* ============================================================ *)
(* §G 一般整隙层：|a²−D·b²| ≥ 1（b≠0·D 非平方）＋特例直得                 *)
(* ============================================================ *)

(* 计算面（透明定义·可执行见证） *)
Definition genD_gap (D a b : Z) : Z := a * a - D * (b * b).
Definition genD_gapQ (D : Z) (a : Z) (b : positive) : Q :=
  (genD_gap D a (Z.pos b) # (b * b))%Q.

(* 全称件：任意整对 (a,b)·b≠0 ⟹ |a²−D·b²| ≥ 1 *)
Lemma gen_gapD_ne : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> b <> 0%Z ->
  (1 <= Z.abs (a * a - D * (b * b)))%Z.
Proof.
  intros D a b HD Hns Hb. apply zabs_ge1.
  intro H0. apply (genD_no_sqrtZ_ne D a b HD Hns Hb). lia.
Qed.

(* 正分母位使用形（B5 b5_gap_ge1／FIB2 fib_norm_gap5_pos 同位） *)
Lemma gen_gapD_pos : forall (D a : Z) (b : positive), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) ->
  (1 <= Z.abs (a * a - D * (Z.pos b * Z.pos b)))%Z.
Proof.
  intros D a b HD Hns. apply (gen_gapD_ne D a (Z.pos b) HD Hns).
  intro Hc. pose proof (Pos2Z.is_pos b). lia.
Qed.

(* D=2 特例直得（B5 |a²−2b²|≥1 一般化） *)
Lemma gen_gapD_2 : forall a b : Z, b <> 0%Z ->
  (1 <= Z.abs (a * a - 2 * (b * b)))%Z.
Proof.
  intros a b Hb. apply (gen_gapD_ne 2 a b); [ lia | exact sqrt2_nonsquare | exact Hb ].
Qed.

(* D=3 特例直得 *)
Lemma gen_gapD_3 : forall a b : Z, b <> 0%Z ->
  (1 <= Z.abs (a * a - 3 * (b * b)))%Z.
Proof.
  intros a b Hb. apply (gen_gapD_ne 3 a b); [ lia | exact sqrt3_nonsquare | exact Hb ].
Qed.

(* D=5 特例直得（FIB2 fib2_gap5_ne 一般形重推） *)
Lemma gen_gapD_5 : forall a b : Z, b <> 0%Z ->
  (1 <= Z.abs (a * a - 5 * (b * b)))%Z.
Proof.
  intros a b Hb. apply (gen_gapD_ne 5 a b); [ lia | exact sqrt5_nonsquare | exact Hb ].
Qed.

(* ============================================================ *)
(* §Q 全有理数域装配层：|(a/b)² − D| ≥ 1/b²（QleT' 全 Set 承载）          *)
(* ============================================================ *)

(* Qeq 交叉恒等（fib_cross_mult 平方形） *)
Lemma q_square_cross : forall (a D0 : Z) (b : positive),
  ((a # b)%Q * (a # b)%Q - (D0 # 1))%Q
  == ((a*a - D0*(Z.pos b * Z.pos b)) # (b * b))%Q.
Proof.
  intros a D0 b.
  unfold Qeq, Qminus, Qmult, Qopp, Qplus, Qnum, Qden. cbn.
  lia.
Qed.

(* 全有理数域装配主语句：任意有理数 a/b 的平方与 D 的距离 ≥ 1/b²
   （零 √D 命名·全 Set 承载·B5/FIB 分离证书的一般 D 形） *)
Lemma q_square_gap : forall (D : Z) (a : Z) (b : positive), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) ->
  QleT' (Qinv ((Z.pos b * Z.pos b) # 1))
        (Qabs (((a # b)%Q * (a # b)%Q - (D # 1))%Q)).
Proof.
  intros D a b HD Hns.
  assert (Hgap := gen_gapD_pos D a b HD Hns).
  apply (fib_qleT_congr_r
        (Qabs ((a*a - D*(Z.pos b * Z.pos b)) # (b * b))%Q)
        (Qabs (((a # b)%Q * (a # b)%Q - (D # 1))%Q))
        (Qinv ((Z.pos b * Z.pos b) # 1)%Q)).
  - apply fib_qabs_congr. apply Qeq_sym. apply (q_square_cross a D).
  - exact (fib_qle_abs_ge (b * b)%positive
      (a * a - D * (Z.pos b * Z.pos b)) Hgap).
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚                   *)
(* ============================================================ *)

Print Assumptions sqrtD_floor.
Print Assumptions genD_no_sqrtZ.
Print Assumptions genD_no_sqrtZ_ne.
Print Assumptions sqrt2_nonsquare.
Print Assumptions sqrt3_nonsquare.
Print Assumptions sqrt5_nonsquare.
Print Assumptions gen_gapD_ne.
Print Assumptions gen_gapD_pos.
Print Assumptions gen_gapD_2.
Print Assumptions gen_gapD_3.
Print Assumptions gen_gapD_5.
Print Assumptions q_square_cross.
Print Assumptions q_square_gap.

(* 数值锚一（Pell 对·D=2）：|3²−2·2²| = 1 *)
Lemma smoke_gapD2 : Z.eqb (Z.abs (3 * 3 - 2 * (2 * 2))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（Pell 对·D=3）：|7²−3·4²| = 1 *)
Lemma smoke_gapD3 : Z.eqb (Z.abs (7 * 7 - 3 * (4 * 4))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（Pell 对·D=5）：|9²−5·4²| = 1（FIB2 同对·一般形重达） *)
Lemma smoke_gapD5 : Z.eqb (Z.abs (9 * 9 - 5 * (4 * 4))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（floor 界实例·D=8 非平方）：2² < 8 < 3² *)
Lemma smoke_floor : (Z.eqb (Z.sqrt 8 * Z.sqrt 8) 4%Z,
                     Z.eqb ((Z.sqrt 8 + 1) * (Z.sqrt 8 + 1)) 9%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（Q 平方隙精确等号）：|(3/2)²−2| = 1/4 *)
Lemma smoke_q_square : Qeq_bool (Qabs (((3 # 2)%Q * (3 # 2)%Q - (2 # 1))%Q))
  (Qinv ((4 # 1)%Q)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（Q 平方隙严格例）：|(4/3)²−3| = 11/9 > 1/9 *)
Lemma smoke_q_square_strict : Qeq_bool (Qabs (((4 # 3)%Q * (4 # 3)%Q - (3 # 1))%Q))
  ((11 # 9)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚七（计算面直算·D=3）：genD_gap 3 7 4 = 1 *)
Lemma smoke_genD_gap : Z.eqb (Z.abs (genD_gap 3 7 4)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚八（Q 计算面直算·D=2）：Qabs (genD_gapQ 2 3 2) = 1/4 *)
Lemma smoke_genD_gapQ : Qeq_bool (Qabs (genD_gapQ 2 3 2)) (Qinv ((4 # 1)%Q)) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_gapD2.
Print Assumptions smoke_gapD3.
Print Assumptions smoke_gapD5.
Print Assumptions smoke_floor.
Print Assumptions smoke_q_square.
Print Assumptions smoke_q_square_strict.
Print Assumptions smoke_genD_gap.
Print Assumptions smoke_genD_gapQ.

From Stdlib Require Import Extraction.
Separate Extraction genD_gap genD_gapQ sqrtD_floor genD_no_sqrtZ
  genD_no_sqrtZ_ne sqrt2_nonsquare sqrt3_nonsquare sqrt5_nonsquare
  gen_gapD_ne gen_gapD_pos gen_gapD_2 gen_gapD_3 gen_gapD_5
  q_square_cross q_square_gap smoke_gapD2 smoke_gapD3 smoke_gapD5
  smoke_floor smoke_q_square smoke_q_square_strict smoke_genD_gap
  smoke_genD_gapQ.
