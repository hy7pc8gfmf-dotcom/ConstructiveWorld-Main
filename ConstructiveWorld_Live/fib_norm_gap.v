(* 五字段指针｜使命：FIB2【sqrt5_no_sqrtZ 全对整隙】——非折半线整隙层补全：√5 无有理平方根
   （无限下降法）直系下任意整数对整隙全称件 |a²−5b²| ≥ 1（b≠0），及黄金比 φ 范数形整隙
   |a²−ab−b²| ≥ 1（(2a−b)² = 5b² 代数桥直系）——Fibonacci 分母族分离证书
   （fib_family_sep）从「族内」扩至「全有理数域」的 Z 层地基。
   机形（对 B5 b5_machine §G 与 FIB fib_machine §C/§G 逐层）：
   §M 平方余态层：sqrt5_mod5_sq——z² ≡ 0 (mod 5) ⟹ z ≡ 0 (mod 5)
     （剩余 1..4 的平方各为 1 或 4 (mod 5)·Zmod_unique 逐格枚举）；
   §N 无平方层：sqrt5_no_sqrtZ——a² = 5b²（0 < b）不可能（对 Z.to_nat b 归纳的
     无穷下降：5|a² ⟹ 5|a ⟹ 5|b·b 严格缩减）＋sqrt5_no_sqrtZ_ne（b≠0 形·Z.abs 桥）；
   §G 整隙层：fib2_gap5_ne——任意整对 b≠0 ⟹ |a²−5b²| ≥ 1｜fib_norm_gap5_pos——
     正分母位（b:positive）使用形（B5 b5_gap_ge1 同位）｜fib_norm_gap_ge1——范数形
     |a²−ab−b²| ≥ 1（FIB 刻形·a²−ab−b² = N(a−bφ) 为 Z[φ] 范数）；
   §F 族桥层：fib_norm_member_abs1——族成员对 (F_{n+3},F_{n+2}) 处范数恰 ±1
     （Cassini 恒等直系·fib_family_sharp 的范数面：全对整隙 ≥1 在分母族上等号实现）；
   §A 审计：PA＋Separate Extraction＋vm_compute 数值锚五件（Pell 对 (9,4) 等号、
     族成员对 (13,8) 等号、严格例 (7,5)、族桥实例、mod5 余态）。
   独立复算先行（假件拦截第一道）：整数精确路 ALL PASS
   （零点无解 420300 对·全称网格 40×40 双形零违例·范数=1 解勘形＝Fibonacci 链
   (±F_{k+1},±F_k) 与反号链·族桥 n≤60 逐对 ±1·代数桥 (2a−b)²−5b²=4(a²−ab−b²) 全域）。
   依赖：fib_machine（zabs_ge1/fibz 系/fibz_cassini/zabs_powneg1）；
   Stdlib ZArith、Arith、Bool、Lia。
   构造性注记：语句面全 Z 层在册先例形（ir2_no_sqrtZ/b5_gap_ge1 同位同形）；唯一前提位
   (0<·)%Z 与 (·<>0)%Z 为 B5/FIB 在册同款先例形；
   证明体内构造性 Prop 推导合法；零承认、零 Abort、零全局假设、零经典逻辑；定义面透明。
   编译配方：rocq c -native-compiler no -q -Q . "" fib_norm_gap.v *)
Require Import fib_machine.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* §M 平方余态层：z² ≡ 0 (mod 5) ⟹ z ≡ 0 (mod 5)                  *)
(* ============================================================ *)

Lemma sqrt5_mod5_sq : forall z : Z, ((z * z) mod 5 = 0)%Z -> (z mod 5 = 0)%Z.
Proof.
  intros z H.
  assert (Hr : (z mod 5 = 0)%Z \/ (z mod 5 = 1)%Z \/ (z mod 5 = 2)%Z \/
               (z mod 5 = 3)%Z \/ (z mod 5 = 4)%Z).
  { pose proof (Z.mod_pos_bound z 5 (ltac:(lia))) as Hb. lia. }
  destruct Hr as [Hr | [Hr | [Hr | [Hr | Hr]]]]; [exact Hr | | | | ].
  - (* z = 5k+1：z² = 5·(5k²+2k)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 2 * k) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 2 * k)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+2：z² = 5·(5k²+4k)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 4 * k) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 4 * k)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+3：z² = 5·(5k²+6k+1)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 6 * k + 1) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 6 * k + 1)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+4：z² = 5·(5k²+8k+3)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 8 * k + 3) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 8 * k + 3)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
Qed.

(* ============================================================ *)
(* §N 无平方层：√5 无有理平方根（无限下降）                          *)
(* ============================================================ *)

Lemma sqrt5_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 5 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 5 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* 5|a、5|b、b 严格缩减（b ↦ b/5） *)
      assert (Ham : ((a * a) mod 5 = 0)%Z).
      { rewrite Heq.
        symmetry. apply (Zmod_unique ((5 * (b * b))%Z) 5%Z ((b * b)%Z) 0%Z); lia. }
      assert (Hae : (a mod 5 = 0)%Z) by (apply sqrt5_mod5_sq; exact Ham).
      pose proof (Z.div_mod a 5 (ltac:(lia))) as Hza. rewrite Hae in Hza.
      remember (a / 5)%Z as a1 eqn:Ea1.
      assert (Ha1 : (a = 5 * a1)%Z) by lia.
      clear Hza Ea1 Hae Ham.
      assert (Hbb : (b * b = 5 * (a1 * a1))%Z).
      { rewrite Ha1 in Heq.
        replace ((5 * a1)%Z * (5 * a1)%Z)%Z with (25 * (a1 * a1)%Z)%Z in Heq by ring.
        replace (25 * (a1 * a1)%Z)%Z with (5 * (5 * (a1 * a1)%Z)%Z)%Z in Heq by ring.
        lia. }
      assert (Hbm : ((b * b) mod 5 = 0)%Z).
      { rewrite Hbb.
        symmetry. apply (Zmod_unique ((5 * (a1 * a1))%Z) 5%Z ((a1 * a1)%Z) 0%Z); lia. }
      assert (Hbe : (b mod 5 = 0)%Z) by (apply sqrt5_mod5_sq; exact Hbm).
      pose proof (Z.div_mod b 5 (ltac:(lia))) as Hzb. rewrite Hbe in Hzb.
      remember (b / 5)%Z as b1 eqn:Eb1.
      assert (Hb1 : (b = 5 * b1)%Z) by lia.
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((5 * b1)%Z * (5 * b1)%Z)%Z with (25 * (b1 * b1)%Z)%Z in Hbb by ring.
        replace (25 * (b1 * b1)%Z)%Z with (5 * (5 * (b1 * b1)%Z)%Z)%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

(* b≠0 形（Z.abs 桥：|b|² = b²） *)
Lemma sqrt5_no_sqrtZ_ne : forall a b : Z, b <> 0%Z -> (a * a = 5 * (b * b))%Z -> False.
Proof.
  intros a b Hb Heq.
  apply (sqrt5_no_sqrtZ a (Z.abs b)).
  - apply Z.abs_pos. exact Hb.
  - rewrite <- (Z.abs_mul b b).
    rewrite (Z.abs_eq (b * b)) by lia.
    exact Heq.
Qed.

(* ============================================================ *)
(* §G 整隙层：任意整数对 |a²−5b²| ≥ 1 ＋ φ 范数形 |a²−ab−b²| ≥ 1      *)
(* ============================================================ *)

(* 计算面（透明定义·可执行见证）：范数形与 √5 整隙的 Z 函数面 *)
Definition fib2_norm (a b : Z) : Z := a * a - a * b - b * b.
Definition fib2_gap5 (a b : Z) : Z := a * a - 5 * (b * b).

(* 全称件（任务刻形）：任意整对 (a,b)·b≠0 ⟹ |a²−5b²| ≥ 1 *)
Lemma fib2_gap5_ne : forall a b : Z, b <> 0%Z -> (1 <= Z.abs (a * a - 5 * (b * b)))%Z.
Proof.
  intros a b Hb. apply zabs_ge1.
  intro H0. apply (sqrt5_no_sqrtZ_ne a b Hb). lia.
Qed.

(* 正分母位使用形（B5 b5_gap_ge1 同位·Q 层装配直用） *)
Lemma fib_norm_gap5_pos : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - 5 * (Z.pos b * Z.pos b)))%Z.
Proof.
  intros a b. apply (fib2_gap5_ne a (Z.pos b)).
  intro Hc. pose proof (Pos2Z.is_pos b). lia.
Qed.

(* φ 范数形整隙（FIB 刻形）：a²−ab−b² = N(a−bφ)·零点等价 (2a−b)² = 5b²
   ——b≠0 时与 √5 无平方直系矛盾 ⟹ 整隙 ≥ 1 全称成立 *)
Lemma fib_norm_gap_ge1 : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - a * Z.pos b - Z.pos b * Z.pos b))%Z.
Proof.
  intros a b.
  pose proof (Pos2Z.is_pos b) as Hb0.
  apply zabs_ge1.
  intro H0.
  assert (Hs : ((2 * a - Z.pos b) * (2 * a - Z.pos b)
                = 5 * (Z.pos b * Z.pos b))%Z) by nia.
  exact (sqrt5_no_sqrtZ (2 * a - Z.pos b) (Z.pos b) Hb0 Hs).
Qed.

(* ============================================================ *)
(* §F 族桥层：范数形整隙在分母族上等号实现                            *)
(* ============================================================ *)

(* 族成员对 (F_{n+3},F_{n+2}) 处范数恰 ±1（Cassini 直系：
   F_{n+3}² − F_{n+3}F_{n+2} − F_{n+2}² = −(F_{n+2}² − F_{n+1}F_{n+3})）
   ——fib_norm_gap_ge1 的下界 1 在 Fibonacci 族上被精确达到（fib_family_sharp 范数面） *)
Lemma fib_norm_member_abs1 : forall n : nat,
  Z.abs (fibz (S (S n)) * fibz (S (S n)) - fibz (S (S n)) * fibz (S n)
         - fibz (S n) * fibz (S n)) = 1%Z.
Proof.
  intro n.
  assert (Hc := fibz_cassini n).
  rewrite fibz_rec in Hc.
  rewrite fibz_rec.
  replace (((fibz (S n) + fibz n) * (fibz (S n) + fibz n)
            - (fibz (S n) + fibz n) * fibz (S n)
            - fibz (S n) * fibz (S n)))%Z
    with (- (fibz (S n) * fibz (S n) - fibz n * (fibz (S n) + fibz n)))%Z by ring.
  rewrite Hc.
  rewrite Z.abs_opp.
  apply zabs_powneg1.
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋vm_compute 数值锚               *)
(* ============================================================ *)

Print Assumptions sqrt5_mod5_sq.
Print Assumptions sqrt5_no_sqrtZ.
Print Assumptions sqrt5_no_sqrtZ_ne.
Print Assumptions fib2_gap5_ne.
Print Assumptions fib_norm_gap5_pos.
Print Assumptions fib_norm_gap_ge1.
Print Assumptions fib_norm_member_abs1.

(* 数值锚一（Pell 对等号实例）：|9²−5·4²| = 1 *)
Lemma fib2_smoke_pell_gap : Z.eqb (Z.abs (9 * 9 - 5 * (4 * 4))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚二（族成员对等号实例）：|13²−13·8−8²| = 1（(F_7,F_6)=(13,8)） *)
Lemma fib2_smoke_norm_fib : Z.eqb (Z.abs (13 * 13 - 13 * 8 - 8 * 8)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚三（严格例）：|7²−7·5−5²| = 11 ≥ 1（非族对·隙严格大于 1） *)
Lemma fib2_smoke_norm_strict : Z.eqb (Z.abs (7 * 7 - 7 * 5 - 5 * 5)) 11%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚四（族桥实例）：fibz 4 = 5、fibz 3 = 3 处 |5²−5·3−3²| = 1 *)
Lemma fib2_smoke_member : Z.eqb (Z.abs (fibz 4 * fibz 4 - fibz 4 * fibz 3 - fibz 3 * fibz 3)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚五（mod5 余态）：7² = 49 ≡ 4 (mod 5)——余态枚举面实例 *)
Lemma fib2_smoke_mod5 : Z.eqb ((7 * 7) mod 5) 4%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚六（计算面可执行见证）：fib2_norm 13 8 = 1（族成员对·函数面直算） *)
Lemma fib2_smoke_norm_fun : Z.eqb (Z.abs (fib2_norm 13 8)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions fib2_smoke_pell_gap.
Print Assumptions fib2_smoke_norm_fib.
Print Assumptions fib2_smoke_norm_strict.
Print Assumptions fib2_smoke_member.
Print Assumptions fib2_smoke_mod5.
Print Assumptions fib2_smoke_norm_fun.

From Stdlib Require Import Extraction.
Separate Extraction fib2_norm fib2_gap5 sqrt5_mod5_sq sqrt5_no_sqrtZ
  sqrt5_no_sqrtZ_ne fib2_gap5_ne fib_norm_gap5_pos fib_norm_gap_ge1
  fib_norm_member_abs1 fib2_smoke_pell_gap fib2_smoke_norm_fib
  fib2_smoke_norm_strict fib2_smoke_member fib2_smoke_mod5 fib2_smoke_norm_fun.
