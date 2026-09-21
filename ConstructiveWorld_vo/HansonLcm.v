(* ============================================================ *)
(* ToyR 玩具证替换件 —— T256 台账席 战役包Q（tier2 批量面第七批）  *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   hl_binom_S（eq_refl 显式见证项（Pascal 定义层展开位），1 刀）                 *)
(* ============================================================ *)

(* ============================================================ *)
(* HansonLcm.v — 席位 CZR14（批次 E-STAGING-CZR14，20260918）      *)
(*                                                               *)
(* 使命：T97 §4 P4 战役件——Hanson 引理战役组（纯 nat 层）。           *)
(*   目标三件：                                                  *)
(*   ① hl_lcm_lt_3pow：lcm(1..n) < 3^n（Hanson 1980）；            *)
(*   ② hl_central_binom_le：C(2n,n) ≤ 4^n（ln2 战役 d_n² 前置件）；  *)
(*   ③ hl_lcm_le_binom 型中转桥。                                 *)
(*                                                               *)
(* 所选路线（诚实溯源登记）：                                      *)
(*   开工 grep 库存实测：stdlib 9.1 nat 层【零素数库】（Arith 无     *)
(*   prime 定义，仅 Znumtheory 限 Z 层 gcd 面）、【零 nat binomial】  *)
(*   （仅 Reals/Binomial 实数面 binom_val）。Hanson 原证明的素数面   *)
(*   （素数枚举表 + Π_{p≤n} p^{⌊log_p n⌋} 素数幂表达 + primorial    *)
(*   ≤ 4^n 自举 + ψ(n) = Σ_k θ(n^{1/k}) 分解）合计 3–5 席工程量，   *)
(*   超本席 90 分钟窗。按任务书诚实边界纪律（对照 GEOM-B 先例）：    *)
(*   - 件② 全强度交付：自建 hl_binom（Pascal 递归）+ 单点界          *)
(*     hl_binom_le_pow2 : C(n,k) ≤ 2^n（双参数归纳）+ 4^n = 2^{2n}  *)
(*     换基，得 C(2n,n) ≤ 4^n——真证、非平凡、可提取；              *)
(*   - 件③ 中转桥全交付：hl_lcm_upto 列表机 + m≤n ⟹ m | L(n)        *)
(*     + L(n) ≤ n! 上界桥 + lcm ≤ 乘积核——供素数面续作席复用；      *)
(*   - 件① 诚实登记未达：3^n 界的数学内容本质在素数幂分解             *)
(*     L(n) = Π_{p≤n} p^{⌊log_p n⌋}（等价 ψ(n) = Σ θ(n^{1/k})），  *)
(*     无素数面即无可达的指数级界；以 hl_lcm_le_fact（L(n) ≤ n!，    *)
(*     弱界）如实占位并显式标注非 3^n，禁止虚报。                    *)
(*   与 Hanson 原论证对应关系：件②对应其 C(2m,m) ≤ 4^m 步（原证用于  *)
(*   primorial 自举的中段件）；件③对应其 lcm 的折叠语义承载；件①的  *)
(*   素数幂表达层即原证第一行，留续作（路线判定见 T106 报告）。       *)
(*   以全称 Set 面件 hl_lcm_le_fact_t（L(n) ≤ n! 的 T 形重述，弱界）  *)
(*   如实收尾并显式标注其非 3^n 档，禁止虚报。                       *)
(* 消融路线备份（任务书预判核实）：「lcm 整除 C(n+k,k) 二项式积」     *)
(*   路线经小例打表判否——n=4: lcm(1..4)=12 ∤ C(8,4)=70 与 4·70=280  *)
(*   （280 mod 12 = 4）；n=3: 6 ∤ C(6,3)=20 但 6 | 3·20=60，无一致   *)
(*   整除型，且 Farhi 型正确桥（lcm(1..n+1) | (n+1)·lcm_k C(n,k)）   *)
(*   的证明仍需素数幂 val 分析，工程量同级。判否登记。               *)
(* 红线四要素宣言（逐件）：                                        *)
(*   - 纯构造性：全件 Qed/Defined，零公理声明词、零认授、零经典逻辑；   *)
(*   - Set 层：主语句面 hl_le_t : Set（Id (Nat.leb a b) true 型，    *)
(*     与 S02 QleT' = Id (Qle_bool x y) true 同构，零 Prop 泄露；    *)
(*     支撑引理 nat 层 Prop 面仅作推理脚手架，照 Ln2Escape 先例）；  *)
(*   - 非平凡：hl_binom Pascal 递归定义 + 双参数归纳界 + lcm 列表机   *)
(*     整除/上界桥皆真构造，非占位；件①未达已显式登记非默默降级；    *)
(*   - 可提取：hl_lcm_upto/hl_binom 皆 Fixpoint 可执行；G3 探针       *)
(*     Separate Extraction 验证 Obj.magic = 0。                    *)
(* 依赖：纯 Stdlib（Arith/Factorial/Lia），零项目件、零自建 .vo——   *)
(*   G2 免基座墙，交付物仅本 .v 源码（信任缓存纪律）。               *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.

(* ============================================================ *)
(* §A Set 面比较器：hl_le_t（nat 层 QleT' 同构件）                     *)
(* ============================================================ *)

Inductive hl_id {A : Set} (x : A) : A -> Set :=
  hl_idrefl : hl_id x x.

(* hl_id 的等式抽取（大消去 Set→Prop，脚手架） *)
Lemma hl_id_eq : forall (A : Set) (x y : A), hl_id x y -> x = y.
Proof. intros A x y H. induction H. reflexivity. Qed.

Definition hl_le_t (a b : nat) : Set := hl_id (Nat.leb a b) true.

(* 四要素·宣言件：Prop 面 le 与 Set 面 hl_le_t 的双向桥（脚手架） *)
Lemma hl_le_to_le_t : forall a b : nat, a <= b -> hl_le_t a b.
Proof.
  intros a b H. apply Nat.leb_le in H.
  unfold hl_le_t. rewrite H. apply hl_idrefl.
Qed.

Lemma hl_le_t_to_le : forall a b : nat, hl_le_t a b -> a <= b.
Proof.
  intros a b H. apply Nat.leb_le. unfold hl_le_t in H.
  exact (hl_id_eq _ _ _ H).
Qed.

(* ============================================================ *)
(* §B 二项式系数（Pascal 递归，自建——stdlib nat 层无库存）             *)
(* ============================================================ *)

Fixpoint hl_binom (n k : nat) : nat :=
  match k with
  | O => 1
  | S k' =>
      match n with
      | O => 0
      | S n' => hl_binom n' k' + hl_binom n' (S k')
      end
  end.

(* Pascal 展开面（C(S n, S k) = C(n,k) + C(n,k+1)）的显式化脚手架 *)
Lemma hl_binom_S : forall n k : nat,
  hl_binom (S n) (S k) = hl_binom n k + hl_binom n (S k).
Proof. intros n k.
  exact (eq_refl (hl_binom n k + hl_binom n (S k))). Qed.

(* 幂换基：4^n = 2^{2n}（照 Ln2Escape.lne_pow4 同型） *)
Lemma hl_pow4 : forall n : nat, (4 ^ n = 2 ^ (2 * n))%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'. rewrite IH.
    replace (2 * S n)%nat with (S (S (2 * n)))%nat by lia.
    rewrite !Nat.pow_succ_r'. lia.
Qed.

(* 幂正性：1 ≤ 2^n（照 Ln2Escape.lne_pow_ge1 同型） *)
Lemma hl_pow2_ge1 : forall n : nat, 1 <= 2 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* 单点界核（非平凡主归纳）：任意二项式系数 ≤ 2^n（全 n,k，无前提——
   越界系数为 0 自动被归纳覆盖）。
   归纳步：C(S n, S k) = C(n,k) + C(n,k+1) ≤ 2^n + 2^n = 2^{S n}
   （双参数归纳假设 (n,k) 与 (n,k+1) 皆消费） *)
Lemma hl_binom_le_pow2 : forall n k : nat, hl_binom n k <= 2 ^ n.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + cbn [hl_binom Nat.pow]. lia.
    + cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. pose proof (hl_pow2_ge1 (S n)). lia.
    + rewrite hl_binom_S. rewrite Nat.pow_succ_r'.
      pose proof (IH k') as H1. pose proof (IH (S k')) as H2. lia.
Qed.

(* 【件②】C(2n,n) ≤ 4^n —— 全强度交付。
   对应 Hanson 原证明中段件：C(2m,m) ≤ 4^m（其 primorial 自举用）。 *)
Theorem hl_central_binom_le : forall n : nat,
  hl_le_t (hl_binom (2 * n) n) (4 ^ n)%nat.
Proof.
  intro n. apply hl_le_to_le_t.
  rewrite hl_pow4.
  apply hl_binom_le_pow2.
Qed.

(* ============================================================ *)
(* §C lcm 列表机与中转桥【件③】                                      *)
(* ============================================================ *)

(* lcm(1..n) 的折叠承载：L(0) = 1（空积），L(S m) = lcm(L m, S m) *)
Fixpoint hl_lcm_upto (n : nat) : nat :=
  match n with
  | O => 1
  | S m => Nat.lcm (hl_lcm_upto m) (S m)
  end.

(* 核不等式：lcm ≤ 乘积（Nat.lcm = a*(b/gcd a b) 展开面） *)
Lemma hl_lcm_le_mul : forall a b : nat, Nat.lcm a b <= a * b.
Proof.
  intros a b. unfold Nat.lcm.
  destruct a as [| a'].
  - rewrite Nat.mul_0_l. apply Nat.le_0_l.
  - assert (Hg : Nat.gcd (S a') b <> 0).
    { destruct (Nat.eq_dec (Nat.gcd (S a') b) 0) as [E|N]; [|exact N].
      exfalso.
      assert (Hd : Nat.divide (Nat.gcd (S a') b) (S a'))
        by apply Nat.gcd_divide_l.
      rewrite E in Hd. destruct Hd as [p Hp].
      rewrite Nat.mul_0_r in Hp. lia. }
    assert (Hpos : 1 <= Nat.gcd (S a') b) by lia.
    assert (Hd : b / Nat.gcd (S a') b <= b).
    { apply Nat.Private_NDivProp.div_le_upper_bound; [exact Hg|].
      apply (Nat.le_trans b (1 * b)%nat (Nat.gcd (S a') b * b)%nat).
      - rewrite Nat.mul_1_l. apply Nat.le_refl.
      - apply Nat.mul_le_mono_r. exact Hpos. }
    apply Nat.mul_le_mono_l. exact Hd.
Qed.

(* 整除传递（脚手架：q·(p·a) = (q·p)·a 归一） *)
Lemma hl_div_trans : forall a b c : nat,
  Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof.
  intros a b c H1 H2. destruct H1 as [p Hp]. destruct H2 as [q Hq].
  exists (q * p)%nat. rewrite Hq. rewrite Hp. ring.
Qed.

(* 中转桥一：1 ≤ m ≤ n ⟹ m | L(n)（逐层折叠，stdlib divide_lcm 双腿） *)
Lemma hl_lcm_divide_all : forall n m : nat,
  1 <= m -> m <= n -> Nat.divide m (hl_lcm_upto n).
Proof.
  induction n as [| n IH]; intros m H1 H2.
  - lia.
  - destruct (Nat.eq_dec m (S n)) as [E|NE].
    + rewrite E. cbn [hl_lcm_upto]. apply Nat.divide_lcm_r.
    + cbn [hl_lcm_upto].
      apply (hl_div_trans m (hl_lcm_upto n)
               (Nat.lcm (hl_lcm_upto n) (S n))).
      * apply IH; lia.
      * apply Nat.divide_lcm_l.
Qed.

(* 中转桥二（上界）：L(n) ≤ n!
   归纳步：L(S n) = lcm(L n, S n) ≤ L n·(S n) ≤ n!·(S n) = (S n)! *)
Lemma hl_lcm_le_fact : forall n : nat, hl_lcm_upto n <= fact n.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - cbn [hl_lcm_upto].
    transitivity (hl_lcm_upto n * S n)%nat.
    + apply hl_lcm_le_mul.
    + assert (Heq : fact (S n) = fact n * S n)
        by (cbn [fact]; ring).
      rewrite Heq. apply Nat.mul_le_mono_r. exact IH.
Qed.

(* ============================================================ *)
(* §D 【件①】Hanson 主件 3^n 界——诚实边界登记（未达，禁止虚报）        *)
(* ============================================================ *)

(* 登记注释（非虚报占位）：hl_lcm_lt_3pow 的数学内容 =
   素数幂分解 L(n) = Π_{p≤n 素} p^{⌊log_p n⌋}，stdlib 9.1 nat 层
   零素数库（开工 grep 实测），素数面（枚举机 + primorial ≤ 4^n
   自举 + ψ(n) 分解）3–5 席工程量，超本席窗。本节以可达的最强弱界
   hl_lcm_le_fact（L(n) ≤ n!）如实收尾并显式标注其【非】3^n 档；
   升级方向：素数面席（Nat.prime 自建 + 素数枚举 Fixpoint +
   Hanson 分解），路线判定详见 T106 报告。 *)

(* 件①当前可达面：L(n) ≤ n! 的 Set 面全称重述（信息性承载；
   显式标注此为【弱界非 3^n 档】）。
   打点纪律注记：数值实例等式（如 L(12) = 27720）不做 Qed 打点——
   kernel conv 在温控并发下对 divmod 链是分钟级墙钟坑
   （E-STAGING-CZR14 卡），可执行性见证改由 G3 提取面承担。 *)
Theorem hl_lcm_le_fact_t : forall n : nat, hl_le_t (hl_lcm_upto n) (fact n).
Proof. intro n. apply hl_le_to_le_t. apply hl_lcm_le_fact. Qed.

(* 与件②的耦合展示（战役接线预览）：C(24,12) ≤ 4^12 于 Set 面。
   打点纪律：12 实例上禁用 apply——unify 的 whd 会把 hl_binom 24 12
   完整数值化（unary 270 万构造子，温控并发下 14 分钟级墙钟坑，
   已实测入 E-STAGING-CZR14 卡）；exact 显式实例只比参数 conv，轻。 *)
Theorem hl_binom24_le_4pow12 : hl_le_t (hl_binom 24 12) (4 ^ 12)%nat.
Proof. exact (hl_central_binom_le 12). Qed.

(* 自审面：主件零假设声明（G1 PA≥1 口径，与 G4 rocq check 同源） *)
Print Assumptions hl_central_binom_le.
