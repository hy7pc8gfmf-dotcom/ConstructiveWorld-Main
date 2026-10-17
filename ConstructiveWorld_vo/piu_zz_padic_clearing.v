(* ===================================================================== *)
(* piu_zz_padic_clearing.v                                              *)
(* p-adic 清整件（E4 面）            *)
(* 文献源：Zeilberger–Zudilin 2020 (arXiv:1912.06345v2) Lemma 1 式(5) /   *)
(*        Lemma 2 v2 的 P_n 集 / Lemma 3 的 L_n（zz.txt 逐字照录为据）    *)
(* 使命: π 族 ZZ 链的 p-adic 清整件（L_n 整性与窗口离散化，判定见下）。  *)
(* 依赖清单: 仅 stdlib ZArith/NArith/QArith（Lia 例外见配方偏差登记）。  *)
(* 构造性注记: 全语句 Set 承载，零 Axiom/Admitted/经典逻辑。             *)
(* 编译配方: rocq c -native-compiler no -q -Q . "" piu_zz_padic_clearing.v *)
(* 语句面：自足 T 形（Bid=Set 承载恒等 + sigT 存在包 + Bdiv 构造性整除）   *)
(* 载体：纯 Z/nat；只 Require stdlib ZArith/NArith/QArith（B01 世界建成， *)
(*        树内依赖禁令——零树内 Require）。                                  *)
(* 边界登记（已证面 vs 留接续面）：                                      *)
(*   已证=本件十定理：P_n 构造定义+窗口离散 floor 形（⌊2n/p⌋=2⌊n/p⌋+1、  *)
(*   ⌊3n/p⌋=3⌊n/p⌋+1，即 Lemma 2 式(7) 的离散 ω 形）+有界性 p≤2n；       *)
(*   lcm(1..K) 整除传播（Lemma 3 式(11) 构造形）；Φ_n=∏P_n 与 Φ_n∣lcm     *)
(*   （L_n∈Z 整形）；Lemma 3 组合核（A_j 侧抽象为 f:nat->Z）；         *)
(*   Lemma 1 的 2-adic 指数不等式与 Gauss Z² 整性（乘法穿越形）。         *)
(*   留接续=A_j 本体（式(5) 系数和与偏分式展开(3)）/Lemma 2 结论本体      *)
(*   （Z(n,m,j)/超 Catalan/Freshman's Dream）/渐近式(10)（Γ/素数定理）/  *)
(*   Lemma 4-6/Prop 1-2/π 系数入口 ∫(1/(5+x)+1/(5-x))dx=πi/2/P_n 非空性  *)
(*   （小 n 实空：n=1,2 检算 ∅；大 n 密度性系式(10) 分析侧）——留         *)
(*   P2①③ 与 P3 接续。                                                  *)
(* 红线：无 Axiom/Admitted/Parameter/Conjecture/Abort/经典逻辑；语句面    *)
(*   全称形 Set 承载零 Prop 泄露（假设位全为 BidT/Bdiv=sigT 之 Set 形）。  *)
(* 符号纪律：本件零使用裸符号 R（A01 警告在案）。                         *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import QArith.
(* 配方偏差登记：「只 Require stdlib ZArith/NArith/QArith」
   的意图=禁树内件接触（B01 世界建成）。Lia 系 stdlib micromega 件，
   零树依赖，Rocq 9.1 的 ZArith 不再默认出口 lia——此处补入属 stdlib
   范围内最小扩充。 *)
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ==================================================================== *)
(* §0. Set 承载核：Bid（宅风 Id 形自足版）/ BidT / Bdiv                  *)
(* ==================================================================== *)

Inductive Bid (A : Type) (a : A) : A -> Set := BidRefl : Bid A a a.

Definition BidT (x : bool) : Set := Bid bool x true.

Definition Bdiv (a b : Z) : Set := sigT (fun z : Z => Bid Z (a * z) b).

Lemma Bid_elim : forall (A : Type) (a b : A), Bid A a b -> a = b.
Proof. intros A a b H. destruct H. reflexivity. Qed.

Lemma Bid_intro : forall (A : Type) (a b : A), a = b -> Bid A a b.
Proof. intros A a b H. rewrite H. apply BidRefl. Qed.

Lemma BidT_intro : forall x : bool, x = true -> BidT x.
Proof. intros x H. apply Bid_intro. exact H. Qed.

Lemma BidT_elim : forall x : bool, BidT x -> x = true.
Proof. intros x H. apply Bid_elim. exact H. Qed.

Lemma BidT_and : forall x y : bool, BidT x -> BidT y -> BidT (x && y).
Proof.
  intros x y Hx Hy. apply BidT_elim in Hx. apply BidT_elim in Hy.
  apply BidT_intro. rewrite Hx, Hy. reflexivity.
Qed.

(* Bdiv 的 bool 出口：a*z=b（Bid 见证）⟹ 可判定整除测试 b mod a =? 0 为真。
   （旧 Bdiv_to_divide 的 Prop 结论 Z.divide 面已除名；divide 的 Set 承载
   即 Bdiv 本体，Prop 形仅在使用方证明体内经 exists/Bid_elim 推出。） *)
Lemma Bdiv_eqb : forall a b : Z, Bdiv a b -> Z.eqb (b mod a) 0 = true.
Proof.
  intros a b [z H]. apply Bid_elim in H.
  destruct (Z.eq_dec a 0) as [Ha0 | Hane].
  - subst a. rewrite <- H. reflexivity.
  - apply (proj2 (Z.eqb_eq _ _)).
    apply (proj2 (Z.mod_divide b a Hane)).
    exists z. rewrite Z.mul_comm. symmetry. exact H.
Qed.

(* Prop 整除的合法 Set 包装：见证=Z.div（数据），mod=0 只作 Prop 证明位。
   （divide_to_Bdiv 之 Prop→Set 直拆非法——红线自查点，已弃用。） *)
Lemma Bdiv_of_mod : forall a b : Z, a <> 0 -> b mod a = 0 -> Bdiv a b.
Proof.
  intros a b H0 Hm. exists (b / a). apply Bid_intro.
  pose proof (Z.div_mod b a H0) as Hdm. rewrite Hm in Hdm.
  symmetry. lia.
Qed.

(* ==================================================================== *)
(* §1. Z 离散半分算术                                                    *)
(* ==================================================================== *)

Lemma zz_half_split : forall x : Z, 0 <= x -> (x + 1) / 2 + x / 2 = x.
Proof.
  intros x Hx.
  assert (H2 : 0 < 2) by lia.
  assert (H2ne : 2 <> 0) by lia.
  pose proof (Z.div_mod x 2 H2ne) as Hdmx.
  pose proof (Z.mod_pos_bound x 2 H2) as Hmb.
  destruct (Z.eq_dec (x mod 2) 0) as [Hr | Hr].
  - remember (x / 2) as q eqn:Hq.
    assert (Hc : x = 2 * q) by lia.
    assert (Hu : (x + 1) / 2 = q).
    { assert (Hmod : (x + 1) mod 2 = 1).
      { replace (x + 1) with (1 + q * 2) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      pose proof (Z.div_mod (x + 1) 2 H2ne) as Hd2.
      rewrite Hmod in Hd2. lia. }
    rewrite Hu, Hc. lia.
  - remember (x / 2) as q eqn:Hq.
    assert (Hc : x = 2 * q + 1) by lia.
    assert (Hu : (x + 1) / 2 = q + 1).
    { assert (Hmod : (x + 1) mod 2 = 0).
      { replace (x + 1) with (0 + (q + 1) * 2) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      pose proof (Z.div_mod (x + 1) 2 H2ne) as Hd2.
      rewrite Hmod in Hd2. lia. }
    rewrite Hu, Hc. lia.
Qed.

Lemma zz_half_floor_mono : forall a b : Z, a <= b -> Z.leb (a / 2) (b / 2) = true.
Proof. intros a b H. apply (proj2 (Z.leb_le _ _)). apply Z.div_le_mono; lia. Qed.

Lemma zz_half_ceil_mono : forall a b : Z,
  a <= b -> Z.leb ((a + 1) / 2) ((b + 1) / 2) = true.
Proof. intros a b H. apply (proj2 (Z.leb_le _ _)). apply Z.div_le_mono; lia. Qed.

Lemma zz_pow_shift : forall e1 e2 s c : Z,
  0 <= e1 -> 0 <= e2 -> 0 <= s -> s <= e1 + e2 ->
  Z.pow 2 e1 * (Z.pow 2 e2 * c) = Z.pow 2 s * (Z.pow 2 (e1 + e2 - s) * c).
Proof.
  intros e1 e2 s c H1 H2 H3 H4.
  assert (H12 : Z.pow 2 e1 * Z.pow 2 e2 = Z.pow 2 (e1 + e2)).
  { rewrite <- Z.pow_add_r by lia. reflexivity. }
  assert (He : e1 + e2 = s + (e1 + e2 - s)) by lia.
  assert (Hs2 : Z.pow 2 (e1 + e2) = Z.pow 2 s * Z.pow 2 (e1 + e2 - s)).
  { rewrite He at 1. rewrite Z.pow_add_r by lia. reflexivity. }
  replace (Z.pow 2 e1 * (Z.pow 2 e2 * c))
    with ((Z.pow 2 e1 * Z.pow 2 e2) * c) by lia.
  rewrite H12, Hs2. ring.
Qed.

(* ==================================================================== *)
(* §2. 高斯整数 Z² 载体（Lemma 1 的 (1±i) 整性核）                        *)
(* ==================================================================== *)

Definition gmul (u v : Z * Z) : Z * Z :=
  (fst u * fst v - snd u * snd v, fst u * snd v + snd u * fst v).

Fixpoint gpow (u : Z * Z) (s : nat) : Z * Z :=
  match s with
  | O => (1, 0)
  | S s' => gmul u (gpow u s')
  end.

Lemma gmul_pairL : forall p q1 q2 : Z, gmul (p, 0) (q1, q2) = (p * q1, p * q2).
Proof. intros p q1 q2. unfold gmul. cbn [fst snd]. f_equal; ring. Qed.

Lemma gmul_11_11 : forall a b : Z,
  gmul (1, 1) (gmul (1, 1) (a, b)) = (- 2 * b, 2 * a).
Proof. intros a b. unfold gmul. cbn [fst snd]. f_equal; ring. Qed.

(* 可计算单位因子：u_s = (1+i)^s / 2^{⌊s/2⌋} 的 Gaussian 表示，双步旋转。 *)
Fixpoint zz_gp (s : nat) : Z * Z :=
  match s with
  | O => (1, 0)
  | S O => (1, 1)
  | S (S s') => (- snd (zz_gp s'), fst (zz_gp s'))
  end.

Lemma zz_gsplit_eq : forall s : nat,
  gpow (1, 1) s =
    (Z.pow 2 (Z.of_nat s / 2) * fst (zz_gp s),
     Z.pow 2 (Z.of_nat s / 2) * snd (zz_gp s)).
Proof.
  intro s.
  assert (HQ : forall s : nat,
            gpow (1, 1) s =
              (Z.pow 2 (Z.of_nat s / 2) * fst (zz_gp s),
               Z.pow 2 (Z.of_nat s / 2) * snd (zz_gp s))
            /\
            gpow (1, 1) (S s) =
              (Z.pow 2 (Z.of_nat (S s) / 2) * fst (zz_gp (S s)),
               Z.pow 2 (Z.of_nat (S s) / 2) * snd (zz_gp (S s)))).
  { intro s0. induction s0 as [|s0 [IH1 IH2]].
    - split; reflexivity.
    - split.
      + exact IH2.
      + assert (Hq0 : 0 <= Z.of_nat s0 / 2) by (apply Z.div_pos; lia).
        cbn [gpow]. rewrite IH1, gmul_11_11.
        cbn [zz_gp fst snd].
        assert (HZ : Z.of_nat (S (S s0)) = Z.of_nat s0 + 2)
          by (rewrite Nat2Z.inj_succ; rewrite Nat2Z.inj_succ; lia).
        rewrite HZ.
        assert (Hdiv : (Z.of_nat s0 + 2) / 2 = Z.of_nat s0 / 2 + 1).
        { replace (Z.of_nat s0 + 2) with (1 * 2 + Z.of_nat s0) by lia.
          rewrite Z.div_add_l by lia. lia. }
        rewrite Hdiv, Z.pow_add_r by lia.
        replace (Z.pow 2 1) with 2 by reflexivity.
        f_equal; ring. }
  apply (proj1 (HQ s)).
Qed.

(* 定理 B1（Lemma 1 的 Z[i] 整性离散核）：
   (1+i)^s = 2^{⌊s/2⌋}·(c,d)，见证=可计算函数 zz_gp s——sigT 存在包。
   文献据点：Lemma 1 证明「(1±i)^2=±2i； hence 2^{⌈(3n-j)/2⌉}×
   (1-i)^{-m4}(1+i)^{-m5} ∈ Z[i]」。 *)
Theorem zz_gauss_split : forall s : nat,
  sigT (fun c : Z =>
        sigT (fun d : Z =>
              Bid (Z * Z) (gpow (1, 1) s)
                (Z.pow 2 (Z.of_nat s / 2) * c,
                 Z.pow 2 (Z.of_nat s / 2) * d))).
Proof.
  intro s. exists (fst (zz_gp s)), (snd (zz_gp s)).
  apply Bid_intro. apply zz_gsplit_eq.
Qed.

(* 定理 B2（Lemma 1 的 (1±i) 整性汇总形，乘法穿越避开逆元）：
   s <= t 时 2^{⌈t/2⌉}·(1+i)^s = 2^s·(c,d)（某高斯整数）。
   对应取 t=3n-j, s=m4+m5：即 2^{⌈(3n-j)/2⌉}(1-i)^{-m4}(1+i)^{-m5}∈Z[i]
   （(1-i) 侧由共轭对称，留接续备注）。 *)
Theorem zz_L1_gauss_integral : forall t s : nat, BidT (Nat.leb s t) ->
  sigT (fun c : Z =>
        sigT (fun d : Z =>
              Bid (Z * Z)
                (gmul (Z.pow 2 ((Z.of_nat t + 1) / 2), 0) (gpow (1, 1) s))
                (Z.pow 2 (Z.of_nat s) * c, Z.pow 2 (Z.of_nat s) * d))).
Proof.
  intros t s Hst. apply BidT_elim in Hst.
  apply (proj1 (Nat.leb_le s t)) in Hst.
  destruct (zz_gauss_split s) as [c0 [d0 Hsplit]].
  apply Bid_elim in Hsplit.
  assert (Hs0 : 0 <= Z.of_nat s) by apply Nat2Z.is_nonneg.
  assert (Hk0 : 0 <= Z.of_nat s / 2) by (apply Z.div_pos; lia).
  assert (Hh20 : 0 <= (Z.of_nat t + 1) / 2) by (apply Z.div_pos; lia).
  assert (Hhs : (Z.of_nat s + 1) / 2 + Z.of_nat s / 2 = Z.of_nat s)
    by (apply zz_half_split; lia).
  assert (Hmono : (Z.of_nat s + 1) / 2 <= (Z.of_nat t + 1) / 2).
  { apply (proj1 (Z.leb_le _ _)). apply zz_half_ceil_mono. lia. }
  assert (Hkf : Z.of_nat s / 2 <= (Z.of_nat s + 1) / 2).
  { apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia. }
  exists (Z.pow 2 ((Z.of_nat t + 1) / 2 + Z.of_nat s / 2 - Z.of_nat s) * c0),
         (Z.pow 2 ((Z.of_nat t + 1) / 2 + Z.of_nat s / 2 - Z.of_nat s) * d0).
  apply Bid_intro.
  rewrite Hsplit, gmul_pairL. f_equal.
  - apply (zz_pow_shift ((Z.of_nat t + 1) / 2) (Z.of_nat s / 2) (Z.of_nat s) c0); lia.
  - apply (zz_pow_shift ((Z.of_nat t + 1) / 2) (Z.of_nat s / 2) (Z.of_nat s) d0); lia.
Qed.

(* 定理 B3（Lemma 1 式(5) 的 2-adic 指数不等式 nat/Z 离散形）：
   ⌊(5n+3j)/2⌋ <= 4n+j+⌈(3n-j)/2⌉（j<=3n）。
   文献据点：式(5) 证明中 2^{-⌊(5n+3j)/2⌋+1}×2^{4n-1+j+m1}×
   2^{⌈(3n-j)/2⌉}(1∓i)^{-m}∈Z[i] 的指数接续（m1>=0 已吸收）。 *)
Theorem zz_L1_exponent : forall n j : nat,
  BidT (Z.leb (Z.of_nat j) (3 * Z.of_nat n)) ->
  BidT (Z.leb ((Z.of_nat n * 5 + Z.of_nat j * 3) / 2)
              (Z.of_nat n * 4 + Z.of_nat j +
               (Z.of_nat n * 3 - Z.of_nat j + 1) / 2)).
Proof.
  intros n j Hj. apply BidT_elim in Hj.
  apply (proj1 (Z.leb_le _ _)) in Hj.
  apply BidT_intro. apply (proj2 (Z.leb_le _ _)).
  transitivity ((Z.of_nat n * 5 + Z.of_nat j * 3 + 1) / 2).
  - apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia.
  - transitivity ((Z.of_nat n * 8 + Z.of_nat j * 2 +
                   (Z.of_nat n * 3 - Z.of_nat j + 1)) / 2).
    + apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia.
    + replace (Z.of_nat n * 8 + Z.of_nat j * 2)
        with ((Z.of_nat n * 4 + Z.of_nat j) * 2) by lia.
      rewrite Z.div_add_l by lia. lia.
Qed.

(* ==================================================================== *)
(* §3. zz_primeb：试除素性 bool（P_n 素性分量，构造性可提取）              *)
(* ==================================================================== *)

Fixpoint zz_nodiv_upto (k : Z) (d : nat) : bool :=
  match d with
  | O => true
  | S d' =>
      if Z.ltb (Z.of_nat (S d')) 2 then true
      else if Z.eqb (k mod Z.of_nat (S d')) 0 then false
      else zz_nodiv_upto k d'
  end.

Definition zz_primeb (k : nat) : bool :=
  andb (Nat.ltb 1 k) (zz_nodiv_upto (Z.of_nat k) (k - 1)%nat).

Lemma zz_nodiv_upto_spec : forall k d, zz_nodiv_upto k d = true ->
  forall e : nat, (2 <= e)%nat -> (e <= d)%nat ->
  Z.eqb (k mod Z.of_nat e) 0 = false.
Proof.
  intros k d. induction d as [|d IH]; intros H e H2 H3.
  - exfalso. lia.
  - destruct (Nat.eq_dec e (S d)) as [He | Hne].
    + subst e. unfold zz_nodiv_upto in H.
      destruct (Z.ltb (Z.of_nat (S d)) 2) eqn:Hlt.
      * apply Z.ltb_lt in Hlt. exfalso. lia.
      * destruct (Z.eqb (k mod Z.of_nat (S d)) 0) eqn:Heq.
        -- discriminate H.
        -- reflexivity.
    + unfold zz_nodiv_upto in H.
      destruct (Z.ltb (Z.of_nat (S d)) 2) eqn:Hlt.
      * apply Z.ltb_lt in Hlt. exfalso. lia.
      * destruct (Z.eqb (k mod Z.of_nat (S d)) 0) eqn:Heq.
        -- discriminate H.
        -- apply IH; [exact H | lia | lia].
Qed.

Lemma zz_primeb_prime : forall k : nat, zz_primeb k = true -> Nat.ltb 1 k = true.
Proof.
  intros k H. apply Bool.andb_true_iff in H. destruct H as [H1 _]. exact H1.
Qed.

(* Z 侧素性测度的 bool 承载形：对 0<=m<Z.of_nat k、m<>1，可判定测试
   Z.of_nat k mod m =? 0 为假（旧 Z.prime 结论面已除名；使用方重建
   Z.prime 于证明体内：1<k 由 zz_primeb_prime，无因子性质由此处直接给出）。 *)
Lemma zz_primeb_spec : forall k : nat, zz_primeb k = true ->
  forall m : Z, (0 <= m)%Z -> (m < Z.of_nat k)%Z -> m <> 1 ->
  Z.eqb (Z.of_nat k mod m) 0 = false.
Proof.
  intros k H m Hm0 Hmk Hm1.
  assert (Hnod : zz_nodiv_upto (Z.of_nat k) (k - 1)%nat = true).
  { apply Bool.andb_true_iff in H. destruct H as [_ H2]. exact H2. }
  pose proof (Z2Nat.id m Hm0) as Hzm.
  destruct (Z.eq_dec m 0) as [Hmz | Hmnz].
  - subst m. rewrite Z.mod_0_r. apply Z.eqb_neq. lia.
  - assert (He2 : (2 <= Z.to_nat m)%nat) by lia.
    assert (He3 : (Z.to_nat m <= k - 1)%nat) by lia.
    pose proof (zz_nodiv_upto_spec (Z.of_nat k) (k - 1)%nat Hnod
                  (Z.to_nat m) He2 He3) as Hne.
    rewrite Hzm in Hne. exact Hne.
Qed.

(* ==================================================================== *)
(* §4. P_n 构造性定义（ZZ 2020 v2 Lemma 2 语句面逐字离散化）              *)
(*   P_n = {p 素 : p > max{5, √(3n)} : 1/2 <= {n/p} < 2/3}              *)
(*   离散形：{n/p}=(n mod p)/p；1/2<={n/p} ⟺ 2·(n mod p) >= p；          *)
(*   {n/p}<2/3 ⟺ 3·(n mod p) < 2p；p>√(3n) ⟺ p²>3n。                    *)
(* ==================================================================== *)

Definition zz_in_Pn (n p : nat) : bool :=
  andb (zz_primeb p)
  (andb (Nat.ltb 5%nat p)
  (andb (Nat.ltb (3 * n)%nat (p * p)%nat)
  (andb (Nat.leb p (2 * (n mod p))%nat)
        (Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)))).

(* 窗口 spec（Prop→Set 消解改形）：
   旧 zz_Pn_window_Prop 的 Prop 三合取结论消解为 bool+Id 真形（Set 承载），
   仿照 zz_in_Pn 的 andb 组件——三组件即三不等式的 Set 形：
   zz_primeb p（⟹1<p）、Nat.leb p (2·(n mod p))、Nat.ltb (3·(n mod p)) (2p)。
   Z 不等式由使用方在证明体内经 Nat.leb_le/Nat.ltb_lt/Nat2Z 推出
   （证明体内构造性 Prop 推导合法——红线律律二正条）。
   律六迁移账：zz_Pn_window_Prop → zz_Pn_window_spec；
   本件使用 7 处（B4/B5/B6/B9/ clearing×3）同步改形；
   外件引用位已随其件同步改形毕。 *)
Lemma zz_Pn_window_spec : forall n p : nat, BidT (zz_in_Pn n p) ->
  (zz_primeb p &&
   (Nat.leb p (2 * (n mod p))%nat &&
    Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)) = true.
Proof.
  intros n p H. apply BidT_elim in H.
  unfold zz_in_Pn in H.
  apply Bool.andb_true_iff in H. destruct H as [Hp Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [_ Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [_ Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [Hw1 Hw2].
  apply Bool.andb_true_iff. split; [exact Hp |].
  apply Bool.andb_true_iff. split; [exact Hw1 | exact Hw2].
Qed.

(* 定理 B4（Lemma 2 证明式(7) 的 nat 离散地板形之一）：
   p ∈ P_n ⟹ ⌊2n/p⌋ = 2·⌊n/p⌋+1（离散 ω={n/p}∈[1/2,2/3) ⟹ ⌊2ω⌋=1）。 *)
Theorem zz_Pn_floor_two : forall n p : nat, BidT (zz_in_Pn n p) ->
  Bid Z (2 * Z.of_nat n / Z.of_nat p) (2 * (Z.of_nat n / Z.of_nat p) + 1).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2, Hp3.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  replace (2 * Z.of_nat n)
    with ((2 * q + 1) * Z.of_nat p + (2 * r - Z.of_nat p)) by lia.
  rewrite Z.div_add_l by exact Zpne.
  rewrite Z.div_small by lia.
  apply Bid_intro. lia.
Qed.

(* 定理 B5（同上之三）：p ∈ P_n ⟹ ⌊3n/p⌋ = 3·⌊n/p⌋+1（离散 ⌊3ω⌋=1）。 *)
Theorem zz_Pn_floor_three : forall n p : nat, BidT (zz_in_Pn n p) ->
  Bid Z (3 * Z.of_nat n / Z.of_nat p) (3 * (Z.of_nat n / Z.of_nat p) + 1).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2, Hp3.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  replace (3 * Z.of_nat n)
    with ((3 * q + 1) * Z.of_nat p + (3 * r - Z.of_nat p)) by lia.
  rewrite Z.div_add_l by exact Zpne.
  rewrite Z.div_small by lia. apply Bid_intro. lia.
Qed.

(* 定理 B6（窗口下界的有界性形）：p ∈ P_n ⟹ p ≤ 2n。
   （{n/p}>=1/2 ⟹ p ≤ 2·(n mod p) ≤ 2n；由此 P_n ⊆ [7,2n]、Φ_n 有限。）
   附登记：P_n 非空性非纯 Z 侧命题（n=1,2 实空），不 born。 *)
Theorem zz_Pn_bounded : forall n p : nat, BidT (zz_in_Pn n p) ->
  BidT (Nat.leb p (2 * n)%nat).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  assert (Hq0 : 0 <= q).
  { rewrite Hq. apply Z.div_pos; lia. }
  assert (Ht : 0 <= Z.of_nat p * q).
  { rewrite Hq, <- (Nat2Z.inj_div n p), <- (Nat2Z.inj_mul p (n / p)%nat).
    apply Nat2Z.is_nonneg. }
  assert (Hrn : r <= Z.of_nat n) by lia.
  apply BidT_intro. apply (proj2 (Nat.leb_le p (2 * n)%nat)).
  lia.
Qed.

(* ==================================================================== *)
(* §5. lcm(1..K) 与整除传播（Lemma 3 式(11)）                  *)
(* ==================================================================== *)

Fixpoint zz_lcm_range (K : nat) : Z :=
  match K with
  | O => 1
  | S K' => Z.lcm (zz_lcm_range K') (Z.of_nat (S K'))
  end.

(* 定理 B7（Lemma 3 证明首行「lcm(1..4n)×(1/j)∈Z」的构造性整除形）：
   1 <= j <= K ⟹ j ∣ lcm(1..K)，商见证由 sigT 承载。
   （Prop 核 + Bdiv_of_mod 合法包装。） *)
Lemma zz_j_div_lcm_P : forall K j : nat,
  (1 <= j)%nat -> (j <= K)%nat -> Bdiv (Z.of_nat j) (zz_lcm_range K).
Proof.
  intros K j H1 H2.
  assert (Hd : (Z.of_nat j | zz_lcm_range K)%Z).
  { revert H2. induction K as [|K IH]; intros H2.
    - exfalso. lia.
    - destruct (Nat.eq_dec j (S K)) as [Hej | Hlt].
      + subst j. apply Z.divide_lcm_r.
      + apply (Z.divide_trans (Z.of_nat j) (zz_lcm_range K) (zz_lcm_range (S K))).
        * apply IH. lia.
        * apply Z.divide_lcm_l. }
  apply Bdiv_of_mod; [lia |].
  apply (proj2 (Z.mod_divide (zz_lcm_range K) (Z.of_nat j) ltac:(lia))).
  exact Hd.
Qed.

Theorem zz_j_div_lcm : forall K j : nat,
  BidT (Nat.ltb 0 j && Nat.leb j K) ->
  Bdiv (Z.of_nat j) (zz_lcm_range K).
Proof.
  intros K j H. apply BidT_elim in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply (proj1 (Nat.ltb_lt 0 j)) in H1.
  apply (proj1 (Nat.leb_le j K)) in H2.
  apply zz_j_div_lcm_P; assumption.
Qed.

(* ==================================================================== *)
(* §6. Φ_n = ∏_{p∈P_n} p 与 Φ_n ∣ lcm(1..4n)（L_n∈Z）         *)
(* ==================================================================== *)

Fixpoint zz_prodf (n K : nat) : Z :=
  match K with
  | O => 1
  | S K' =>
      if zz_in_Pn n (S K') then zz_prodf n K' * Z.of_nat (S K')
      else zz_prodf n K'
  end.

Definition zz_Phi (n : nat) : Z := zz_prodf n (2 * n)%nat.

Definition zz_L (n : nat) : Z :=
  Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n)).

Lemma zz_prodf_nonneg : forall n K : nat, Z.leb 0 (zz_prodf n K) = true.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. reflexivity.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.leb_le _ _)).
      apply (proj1 (Z.leb_le 0 (zz_prodf n K))) in IH.
      nia.
    + exact IH.
Qed.

Lemma zz_prodf_pos : forall n K : nat, Z.ltb 0 (zz_prodf n K) = true.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. reflexivity.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.ltb_lt _ _)).
      apply (proj1 (Z.ltb_lt 0 (zz_prodf n K))) in IH.
      assert (H1 : 1 <= zz_prodf n K) by lia.
      assert (H2 : 1 <= Z.of_nat (S K)) by lia.
      assert (Hle : 1 * 1 <= zz_prodf n K * Z.of_nat (S K)).
      { apply (Z.mul_le_mono_nonneg 1 (zz_prodf n K) 1 (Z.of_nat (S K))); lia. }
      lia.
    + exact IH.
Qed.

Lemma zz_coprime_sym : forall a b : Z,
  Z.eqb (Z.gcd a b) 1 = true -> Z.eqb (Z.gcd b a) 1 = true.
Proof.
  intros a b H. apply Z.eqb_eq in H.
  apply (proj2 (Z.eqb_eq _ _)). rewrite Z.gcd_comm. exact H.
Qed.

Lemma zz_lcm_prod : forall a b : Z,
  Z.coprime a b -> 0 <= a -> 0 <= b -> Z.lcm a b = a * b.
Proof.
  intros a b Hcop Ha Hb. unfold Z.lcm.
  unfold Z.coprime in Hcop. rewrite Hcop. rewrite Z.div_1_r.
  rewrite Z.abs_eq by nia.
  reflexivity.
Qed.

Lemma zz_prodf_coprime : forall n K q,
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Z.eqb (Z.gcd (Z.of_nat k) q) 1 = true) ->
  Z.eqb (Z.gcd (zz_prodf n K) q) 1 = true.
Proof.
  intros n K q. induction K as [|K IH]; intros Hh.
  - cbn [zz_prodf]. rewrite Z.gcd_1_l. apply Z.eqb_refl.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.eqb_eq _ _)).
      assert (Hrest : Z.coprime (zz_prodf n K) q).
      { unfold Z.coprime. apply (proj1 (Z.eqb_eq _ _)). apply IH.
        intros k Hk Hinp. apply Hh.
        -- apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
           apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
        -- exact Hinp. }
      assert (Hsk : Z.coprime (Z.of_nat (S K)) q).
      { unfold Z.coprime. apply (proj1 (Z.eqb_eq _ _)). apply Hh.
        -- apply BidT_intro. apply (proj2 (Nat.leb_le (S K) (S K))). lia.
        -- apply BidT_intro. exact E. }
      exact (Z.coprime_mul_l _ _ _ Hrest Hsk).
    + apply IH. intros k Hk Hinp. apply Hh.
      * apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
        apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
      * exact Hinp.
Qed.

(* 定理 B8（两两互素整除乘积传播）：P_n 成员各自整除 M（互素由素性+相异
   自动保证）⟹ ∏_{p∈P_n, p≤K} p ∣ M。（Prop 核 + Bdiv_of_mod 包装。） *)
Lemma zz_prodf_divides_P : forall (n K : nat) (M : Z),
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Bdiv (Z.of_nat k) M) ->
  Bdiv (zz_prodf n K) M.
Proof.
  intros n K. induction K as [|K IH]; intros M Hhyp.
  - cbn [zz_prodf]. apply Bdiv_of_mod; [lia |].
    apply (proj2 (Z.mod_divide M 1 ltac:(lia))).
    apply Z.divide_1_l.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + assert (HrestM : Bdiv (zz_prodf n K) M).
      { apply IH. intros k Hk Hinp. apply Hhyp.
        - apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
          apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
        - exact Hinp. }
      assert (HpM : Bdiv (Z.of_nat (S K)) M).
      { apply Hhyp.
        - apply BidT_intro. apply (proj2 (Nat.leb_le (S K) (S K))). lia.
        - apply BidT_intro. exact E. }
      assert (Hpb : zz_primeb (S K) = true).
      { unfold zz_in_Pn in E. apply Bool.andb_true_iff in E.
        destruct E as [Epb _]. exact Epb. }
      assert (Hpk : Z.prime (Z.of_nat (S K))).
      { pose proof (zz_primeb_prime (S K) Hpb) as Hltb.
        apply (proj1 (Nat.ltb_lt 1 (S K))) in Hltb.
        split.
        - lia.
        - intros m Hm1 Hmd.
          exfalso.
          assert (Hm0 : (0 <= m)%Z) by lia.
          pose proof (proj2 (Z.mod_divide (Z.of_nat (S K)) m ltac:(lia)) Hmd) as Hmod0.
          pose proof (zz_primeb_spec (S K) Hpb m Hm0 ltac:(lia) ltac:(lia)) as Hb.
          rewrite Hmod0 in Hb. discriminate Hb. }
      assert (Hcop : Z.eqb (Z.gcd (zz_prodf n K) (Z.of_nat (S K))) 1 = true).
      { apply zz_prodf_coprime.
        intros k Hk Hinp. apply BidT_elim in Hk.
        apply (proj1 (Nat.leb_le k K)) in Hk.
        apply (proj2 (Z.eqb_eq _ _)).
        assert (Hcp : Z.coprime (Z.of_nat (S K)) (Z.of_nat k)).
        { apply (Z.coprime_prime_l (Z.of_nat (S K)) (Z.of_nat k)).
          - exact Hpk.
          - intro Hd.
            assert (Hpbk : zz_primeb k = true).
            { apply BidT_elim in Hinp. unfold zz_in_Pn in Hinp.
              apply Bool.andb_true_iff in Hinp. destruct Hinp as [Hpbin _].
              exact Hpbin. }
            assert (Hqk : Z.prime (Z.of_nat k)).
            { pose proof (zz_primeb_prime k Hpbk) as Hltb.
              apply (proj1 (Nat.ltb_lt 1 k)) in Hltb.
              split.
              - lia.
              - intros m Hm1 Hmd.
                exfalso.
                assert (Hm0 : (0 <= m)%Z) by lia.
                pose proof (proj2 (Z.mod_divide (Z.of_nat k) m ltac:(lia)) Hmd) as Hmod0.
                pose proof (zz_primeb_spec k Hpbk m Hm0 ltac:(lia) ltac:(lia)) as Hb.
                rewrite Hmod0 in Hb. discriminate Hb. }
            pose proof (Z.divide_prime_prime (Z.of_nat (S K)) (Z.of_nat k)
                          Hpk Hqk Hd) as Heq.
            apply Nat2Z.inj in Heq. lia. }
        unfold Z.coprime in Hcp. rewrite Z.gcd_comm in Hcp. exact Hcp. }
      assert (Hlcm : Z.lcm (zz_prodf n K) (Z.of_nat (S K)) =
                     zz_prodf n K * Z.of_nat (S K)).
      { apply zz_lcm_prod.
        - unfold Z.coprime. apply (proj1 (Z.eqb_eq _ _)). exact Hcop.
        - apply (proj1 (Z.leb_le 0 (zz_prodf n K))). apply zz_prodf_nonneg.
        - apply Nat2Z.is_nonneg. }
      assert (Hp : (0 < zz_prodf n K)%Z).
      { apply (proj1 (Z.ltb_lt 0 (zz_prodf n K))). apply zz_prodf_pos. }
      apply Bdiv_of_mod.
      * lia.
      * apply (proj2 (Z.mod_divide M (zz_prodf n K * Z.of_nat (S K)) ltac:(lia))).
        rewrite <- Hlcm. apply Z.lcm_divide_iff. split.
        -- destruct HrestM as [z Hz]. apply Bid_elim in Hz.
           exists z. rewrite Z.mul_comm. symmetry. exact Hz.
        -- destruct HpM as [z Hz]. apply Bid_elim in Hz.
           exists z. rewrite Z.mul_comm. symmetry. exact Hz.
    + apply IH. intros k Hk Hinp. apply Hhyp.
      * apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
        apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
      * exact Hinp.
Qed.

Theorem zz_prodf_divides : forall (n K : nat) (M : Z),
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Bdiv (Z.of_nat k) M) ->
  Bdiv (zz_prodf n K) M.
Proof.
  intros n K M Hhyp.
  apply zz_prodf_divides_P. exact Hhyp.
Qed.

(* 定理 B9（Lemma 3 的 L_n∈Z 形）：
   存在 L（=zz_L n=lcm(1..4n)/Φ_n 精确商）使 Φ_n·L = lcm(1..4n)。 *)
Theorem zz_L_integral : forall n : nat,
  sigT (fun L : Z => Bid Z ((zz_Phi n) * L) (zz_lcm_range (4 * n)%nat)).
Proof.
  intro n.
  assert (Hpos : (0 < (zz_Phi n))%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  assert (HdP : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  assert (HL : (zz_Phi n) * Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n))
             = zz_lcm_range (4 * n)%nat).
  { destruct HdP as [e He]. apply Bid_elim in He.
    replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n))
      by (rewrite Z.mul_comm; exact He).
    rewrite Z.div_mul by lia. apply Z.mul_comm. }
  exists (Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n))).
  apply Bid_intro. exact HL.
Qed.

(* ==================================================================== *)
(* §7. 定理 B10：Lemma 3 组合核（A_j 侧抽象为 f:nat->Z）                  *)
(*   文献：式(11) lcm×(1/j)∈Z ＋ 式(12)（p∈P_n, p∣j ⟹ p∣10^{-j}A_j，      *)
(*   即 Lemma 2 v2 结论——本件作假设位）⟹ L_n×10^{-j}A_j/j∈Z。            *)
(*   born 形：1<=j<=4n ＋ 每素清整假设（p∣j 以 Set 承载 bool 形            *)
(*   Z.eqb (j mod p) 0 表载）⟹ j ∣ L_n·f(j)（见证 sigT）。                *)
(* ==================================================================== *)

Theorem zz_clearing_propagation : forall (n j : nat) (f : nat -> Z),
  BidT (Nat.ltb 0 j && Nat.leb j (4 * n)%nat) ->
  (forall p : nat, BidT (zz_in_Pn n p) ->
     BidT (Z.eqb (Z.of_nat j mod Z.of_nat p) 0) ->
     Bdiv (Z.of_nat p) (f j)) ->
  Bdiv (Z.of_nat j) (zz_L n * f j).
Proof.
  intros n j f Hj Hclear.
  assert (Hpos : (0 < (zz_Phi n))%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  apply BidT_elim in Hj. apply Bool.andb_true_iff in Hj.
  destruct Hj as [Hj1 Hj2].
  apply (proj1 (Nat.ltb_lt 0 j)) in Hj1.
  apply (proj1 (Nat.leb_le j (4 * n)%nat)) in Hj2.
  assert (Hjpos : (0 < j)%nat) by lia.
  assert (HjLcm : (Z.of_nat j | zz_lcm_range (4 * n)%nat)%Z).
  { destruct (zz_j_div_lcm_P (4 * n)%nat j ltac:(lia) ltac:(lia)) as [z Hz].
    apply Bid_elim in Hz.
    exists z. rewrite Z.mul_comm. symmetry. exact Hz. }
  set (w := Z.div (zz_lcm_range (4 * n)%nat) (Z.of_nat j)).
  assert (Hjw : zz_lcm_range (4 * n)%nat = Z.of_nat j * w).
  { unfold w.
    apply (proj2 (Z.div_exact (zz_lcm_range (4 * n)%nat) (Z.of_nat j) ltac:(lia))).
    apply (proj2 (Z.mod_divide (zz_lcm_range (4 * n)%nat) (Z.of_nat j) ltac:(lia))).
    exact HjLcm. }
  assert (Hwf : Bdiv (zz_Phi n) (w * f j)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp.
    pose proof (zz_Pn_window_spec n k Hinp) as Hw.
    apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
    pose proof (zz_primeb_prime k Hpk) as Hwpos.
    apply (proj1 (Nat.ltb_lt 1 k)) in Hwpos.
    clear Hpk.
    assert (Hpbk : zz_primeb k = true).
    { apply BidT_elim in Hinp. unfold zz_in_Pn in Hinp.
      apply Bool.andb_true_iff in Hinp. destruct Hinp as [Hpb _].
      exact Hpb. }
    assert (Hprime : Z.prime (Z.of_nat k)).
    { pose proof (zz_primeb_prime k Hpbk) as Hltb.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hltb.
      split.
      - lia.
      - intros m Hm1 Hmd.
        exfalso.
        assert (Hm0 : (0 <= m)%Z) by lia.
        pose proof (proj2 (Z.mod_divide (Z.of_nat k) m ltac:(lia)) Hmd) as Hmod0.
        pose proof (zz_primeb_spec k Hpbk m Hm0 ltac:(lia) ltac:(lia)) as Hb.
        rewrite Hmod0 in Hb. discriminate Hb. }
    assert (HkL : (Z.of_nat k | zz_lcm_range (4 * n)%nat)%Z).
    { assert (Hk1 : (1 <= k)%nat) by lia.
      assert (Hk2 : (k <= 4 * n)%nat).
      { assert (Hb : BidT (Nat.leb k (2 * n)%nat))
          by (apply zz_Pn_bounded; exact Hinp).
        apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
        lia. }
      destruct (zz_j_div_lcm_P (4 * n)%nat k Hk1 Hk2) as [z Hz].
      apply Bid_elim in Hz.
      exists z. rewrite Z.mul_comm. symmetry. exact Hz. }
    destruct (Z.eqb (Z.of_nat j mod Z.of_nat k) 0) eqn:Hjeq.
    - (* k ∣ j：清整假设直接给 k ∣ f j，w 乘上即 k ∣ w·f j *)
      assert (HjeqbB : BidT (Z.eqb (Z.of_nat j mod Z.of_nat k) 0)).
      { apply BidT_intro. exact Hjeq. }
      destruct (Hclear k Hinp HjeqbB) as [zp Hbp].
      apply Bid_elim in Hbp.
      exists (w * zp). apply Bid_intro. rewrite <- Hbp. ring.
    - (* k ∤ j：k ∣ lcm = j·w ＋ 素性 ⟹ k ∣ w（Z.gauss），再乘 f j *)
      assert (Hnkdj : ~ (Z.of_nat k | Z.of_nat j)).
      { intro Hd.
        pose proof (proj2 (Z.mod_divide (Z.of_nat j) (Z.of_nat k) ltac:(lia)) Hd)
          as Hmod0.
        rewrite Hmod0 in Hjeq. discriminate Hjeq. }
      assert (Hcop : Z.coprime (Z.of_nat k) (Z.of_nat j)).
      { apply Z.coprime_prime_l.
        - exact Hprime.
        - exact Hnkdj. }
      assert (Hkw : (Z.of_nat k | w)%Z).
      { apply (Z.gauss (Z.of_nat k) (Z.of_nat j) w).
        + rewrite <- Hjw. exact HkL.
        + unfold Z.coprime in Hcop. exact Hcop. }
      assert (Hkne : Z.of_nat k <> 0) by lia.
      assert (Hmodw : w mod Z.of_nat k = 0).
      { apply (proj2 (Z.mod_divide w (Z.of_nat k) Hkne)). exact Hkw. }
      pose proof (Z.div_mod w (Z.of_nat k) Hkne) as Hdm.
      set (q := w / Z.of_nat k) in Hdm.
      rewrite Hmodw in Hdm.
      exists (q * f j). apply Bid_intro.
      rewrite Hdm. ring. }
  assert (HdP2 : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  assert (HΦL : (zz_Phi n) * zz_L n = zz_lcm_range (4 * n)%nat).
  { unfold zz_L.
    destruct HdP2 as [e He]. apply Bid_elim in He.
    replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n))
      by (rewrite Z.mul_comm; exact He).
    rewrite Z.div_mul by lia. apply Z.mul_comm. }
  (* Prop 核：j ∣ L_n·f j（见证 z0），再经 Bdiv_of_mod 合法升 Set *)
  apply Bdiv_of_mod.
  - lia.
  - apply (proj2 (Z.mod_divide (zz_L n * f j) (Z.of_nat j) ltac:(lia))).
    destruct Hwf as [z0 Hz0]. apply Bid_elim in Hz0.
    assert (Heq : (zz_Phi n) * (zz_L n * f j)
                = (zz_Phi n) * (Z.of_nat j * z0)).
    { rewrite Z.mul_assoc, HΦL, Hjw, <- Z.mul_assoc, <- Hz0. ring. }
    exists z0.
    apply (proj1 (Z.mul_cancel_l (zz_L n * f j) (z0 * Z.of_nat j)
                    ((zz_Phi n)) ltac:(lia))).
    rewrite Heq. ring.
Qed.

(* ==================================================================== *)
(* §8. G4 认证：全交付定理 Print Assumptions（期望全 Closed）             *)
(* ==================================================================== *)

Print Assumptions zz_gauss_split.
Print Assumptions zz_L1_gauss_integral.
Print Assumptions zz_L1_exponent.
Print Assumptions zz_Pn_floor_two.
Print Assumptions zz_Pn_floor_three.
Print Assumptions zz_Pn_bounded.
Print Assumptions zz_j_div_lcm.
Print Assumptions zz_prodf_divides.
Print Assumptions zz_L_integral.
Print Assumptions zz_clearing_propagation.
