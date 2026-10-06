(* ===================================================================== *)
(*  abl_ln2_growth_budget.v —— ln2 无理性链·L_n 增长预算供给模块（DP 二派       *)
(*  完成度图两大肢之一：上肢装配（θ 锐权界×换序恒等式）的预算面供给模块）        *)
(*  使命: A_n := 2ⁿ·q̃_n（Beukers 分母尺度，q̃_n = bk_Qn_qtilde =             *)
(*        Σ_{k≤n} C(n,k)²·2^{n−k}）的显式上界定理闭合：                      *)
(*        ①lng2_bkC_le_pow2（bkC n k ≤ 2ⁿ，Pascal 双归纳）；                 *)
(*        ②lng2_qtilde_le_6pow：q̃_n ≤ 6ⁿ（逐点 C² ≤ 2ⁿ·C + bk_psd_mono +    *)
(*          二项定理 bk_psd_binom：Σ C(n,k)·2^{n−k} = 3ⁿ，一跳归纳闭合）；     *)
(*        ③主件 lng2_An_le_12pow / lng2_An_le_16pow：A_n ≤ 12ⁿ ≤ 16ⁿ        *)
(*          （12ⁿ = 2ⁿ·6ⁿ 显式合成；16ⁿ 经 12ⁿ 单调闭合——粗界档达标，     *)
(*          且 12ⁿ 为更锐首档）；下界 lng2_An_ge_6pow（3ⁿ ≤ q̃_n 在册）。      *)
(*        ④数值锚组 n=0..4：A_n = 1/6/52/504/5136（vm_compute 精确判定；      *)
(*          与任务在册锚 6/52/504/5136 全吻合，anchor4 使用 qpoly_gen        *)
(*          lng_qtilde_pin_4（q̃_4=321））；                                  *)
(*        ⑤Q 面桥 lng2_AnQ_eq（使用 numer_int lni_qpow2_nat：               *)
(*          2ⁿ·q̃_nQ == A_nQ）与 Q 面锚；                                    *)
(*        ⑥L_n 肢使用面：lng2_Ln := hl_lcm_upto，L_n ≤ n! 的 Prop/Set       *)
(*          双面在册重述（HansonLcm hl_lcm_le_fact/hl_lcm_le_fact_t 直取）；  *)
(*        ⑦装配使用形 lng2_budget_compose（匹配 (4/3)ⁿ 的预算引理）：          *)
(*          A_n·(3/4)^{m−2n} ≤ (64/3)ⁿ·(3/4)^m（QleT' Set 面）——             *)
(*          合成率判定 κ := 64/3：12ⁿ = (64/3)ⁿ·(3/4)^{2n}，即增长预算        *)
(*          经强制 (4/3)^{2n} 抽出后与 (3/4)^{SM} 衰减同框；装配取           *)
(*          SM 斜率 c > log_{4/3}(64/3) ≈ 10.64（如 SM ≥ 11n+O(1)）即         *)
(*          κ·(3/4)^c < 1，增长不吞掉衰减。诚实边界见 §G 注记。               *)
(*  依赖: Stdlib QArith/Arith/Arith.Factorial/ZArith/Lia；S01_BaseRing       *)
(*        S02_CauchyComplete S03_QExp BeukersLists HansonLcm；前置池拷贝     *)
(*        链序 abl_ln2_numer_int → abl_qpoly_divmod → abl_qpoly_divmod_gen   *)
(*        → abl_ln2_qpoly_consume → abl_ln2_qpoly_gen → 本件（真使用：       *)
(*        numer_int lni_qpow2_nat；qpoly_gen lng_qtilde_pin_4/              *)
(*        lng_qpow_congr）。                                                *)
(*  对标: DP 二派完成度图「L_n 增长预算肢」；上肢装配（θ 锐权尾隙            *)
(*        ≤2^{n+2}·(3/4)^{SM−2n}）的预算面供给；AE §3.3 供给对               *)
(*        A_n := 2ⁿ·q̃_n 的分母尺度判定（BeukersLists bk_Qn_qtilde 面）。     *)
(*  构造性: 全件 Qed、零承认、零经典逻辑；主语句面 Set（hl_le_t/QeqT/       *)
(*        QleT'），nat ≤ 支撑面仅作推理（hl_lcm_le_fact 同口径）； witnesses  *)
(*        全显式可提取（lng2_An 为 Fixpoint 复合，G3 Separate Extraction     *)
(*        闭合）；文尾 Print Assumptions 取证块全 Closed（四关证据之一）。    *)
(*  编译配方: cd ConstructiveWorld && source Live/toolchain/env.sh &&       *)
(*        unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c        *)
(*        -native-compiler no -Q vo_local_world_unified_0930 "" 本件        *)
(*        （独占沙箱池 ln2_growth/，链内平铺使用；道闸≤1=单进程串行）。      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Arith.Arith Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_qpoly_gen.

Open Scope nat_scope.

(* ============================================================ *)
(* §A bkC 幂界：C(n,k) ≤ 2ⁿ（Pascal 双归纳，仿 hl_binom_le_pow2）          *)
(* ============================================================ *)

Lemma lng2_bkC_le_pow2 : forall n k : nat, bkC n k <= 2 ^ n.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. apply Nat.le_refl.
    + cbn [bkC Nat.pow]. apply Nat.le_0_l.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. assert (H := hl_pow2_ge1 n). lia.
    + cbn [bkC]. rewrite Nat.pow_succ_r'.
      assert (H1 := IH k'). assert (H2 := IH (Datatypes.S k')). lia.
Qed.

(* ============================================================ *)
(* §B q̃_n ≤ 6ⁿ：逐点 C² ≤ 2ⁿ·C ＋ bk_psd_mono ＋ 二项定理一跳               *)
(* ============================================================ *)

(* 常数提出：bk_psd 对逐项 c·f(k) 的线性（和内逐项提出 c） *)
Lemma lng2_psd_scale : forall (N c : nat) (f : nat -> nat),
  bk_psd (fun k => c * f k) N = c * bk_psd f N.
Proof.
  induction N as [| N IH]; intros c f.
  - cbn [bk_psd]. ring.
  - cbn [bk_psd]. rewrite (IH c f). ring.
Qed.

(* 底积分解：(a·b)ⁿ = aⁿ·bⁿ（stdlib 只有指数和 pow_add_r，底和自建） *)
Lemma lng2_pow_mul_l : forall a b n : nat, (a * b) ^ n = a ^ n * b ^ n.
Proof.
  intros a b n. induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

(* 主跳：q̃_n = Σ_{k≤n} C(n,k)²·2^{n−k} ≤ 2ⁿ·Σ_{k≤n} C(n,k)·2^{n−k} = 2ⁿ·3ⁿ = 6ⁿ *)
Lemma lng2_qtilde_le_6pow : forall n : nat, bk_Qn_qtilde n <= 6 ^ n.
Proof.
  intro n. unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n ->
            bkC n k * bkC n k <= 2 ^ n * bkC n k).
  { intro k. intro Hk. apply Nat.mul_le_mono_r. apply lng2_bkC_le_pow2. }
  pose proof (bk_psd_mono (Datatypes.S n) (fun k => bkC n k * bkC n k)
              (fun k => 2 ^ n * bkC n k) Hpt) as Hmono.
  transitivity (2 ^ n * bk_psd (fun k => bkC n k) (Datatypes.S n))%nat.
  - rewrite <- (lng2_psd_scale (Datatypes.S n) (2 ^ n) (fun k => bkC n k)).
    exact Hmono.
  - rewrite (bk_psd_binom n).
    replace 6 with (2 * 3)%nat by lia.
    rewrite lng2_pow_mul_l. lia.
Qed.

(* ============================================================ *)
(* §C A_n := 2ⁿ·q̃_n 定义与主界（12ⁿ 首档 / 16ⁿ 粗界档）                 *)
(* ============================================================ *)

Definition lng2_An (n : nat) : nat := 2 ^ n * bk_Qn_qtilde n.

(* 不同底幂的单调（12ⁿ ≤ 16ⁿ 闭合用） *)
Lemma lng2_pow_le_mono_base : forall a b n : nat, a <= b -> a ^ n <= b ^ n.
Proof.
  intros a b n H. induction n as [| n IH].
  - apply Nat.le_refl.
  - rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono. exact H. exact IH.
Qed.

Theorem lng2_An_le_12pow : forall n : nat, lng2_An n <= 12 ^ n.
Proof.
  intro n. unfold lng2_An.
  transitivity (2 ^ n * 6 ^ n)%nat.
  - apply Nat.mul_le_mono_l. apply lng2_qtilde_le_6pow.
  - replace 12 with (2 * 6)%nat by lia.
    rewrite lng2_pow_mul_l. lia.
Qed.

(* 粗界档：A_n ≤ 16ⁿ（经 12ⁿ 单调闭合） *)
Theorem lng2_An_le_16pow : forall n : nat, lng2_An n <= 16 ^ n.
Proof.
  intro n.
  apply (Nat.le_trans (lng2_An n) (12 ^ n) (16 ^ n)).
  - apply lng2_An_le_12pow.
  - apply (lng2_pow_le_mono_base 12 16 n). lia.
Qed.

(* Set 面全称重述（hl_le_t 同构件，装配直接使用形） *)
Theorem lng2_An_le_12pow_t : forall n : nat, hl_le_t (lng2_An n) (12 ^ n)%nat.
Proof. intro n. apply hl_le_to_le_t. apply lng2_An_le_12pow. Qed.

Theorem lng2_An_le_16pow_t : forall n : nat, hl_le_t (lng2_An n) (16 ^ n)%nat.
Proof. intro n. apply hl_le_to_le_t. apply lng2_An_le_16pow. Qed.

(* 下界锚：A_n ≥ 6ⁿ（3ⁿ ≤ q̃_n 在册 BeukersLists bk_Qn_ge_3pow_nat；
   6ⁿ ≤ A_n ≤ 12ⁿ 判定 K ∈ [6,12]，真实倍率见 §E 数值锚 ~×8.7..×10.2） *)
Theorem lng2_An_ge_6pow : forall n : nat, 6 ^ n <= lng2_An n.
Proof.
  intro n. unfold lng2_An.
  replace 6 with (2 * 3)%nat by lia.
  rewrite lng2_pow_mul_l. apply Nat.mul_le_mono.
  - apply Nat.le_refl.
  - apply bk_Qn_ge_3pow_nat.
Qed.

(* ============================================================ *)
(* §D 数值锚组（vm_compute 精确判定；与任务在册锚 6/52/504/5136 全吻合）      *)
(* ============================================================ *)

Theorem lng2_An_anchor0 : lng2_An 0 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem lng2_An_anchor1 : lng2_An 1 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem lng2_An_anchor2 : lng2_An 2 = 52%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem lng2_An_anchor3 : lng2_An 3 = 504%nat.
Proof. vm_compute. reflexivity. Qed.

(* anchor4 真使用 qpoly_gen 在册件 lng_qtilde_pin_4（q̃_4 = 321） *)
Theorem lng2_An_anchor4 : lng2_An 4 = 5136%nat.
Proof.
  unfold lng2_An. rewrite lng_qtilde_pin_4.
  vm_compute. reflexivity.
Qed.

(* Q 面锚桥（nat 锚 ⟹ QeqT，Set 面） *)
Lemma lng2_AnQ_of_nat : forall a b : nat, a = b ->
  QeqT ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b H. subst b. apply qeq_imp_qeqT. reflexivity.
Qed.

Theorem lng2_AnQ_anchor1 : QeqT ((Z.of_nat (lng2_An 1) # 1)%Q) (6 # 1)%Q.
Proof. apply (lng2_AnQ_of_nat 6 6 (lng2_An_anchor1)). Qed.

Theorem lng2_AnQ_anchor2 : QeqT ((Z.of_nat (lng2_An 2) # 1)%Q) (52 # 1)%Q.
Proof. apply (lng2_AnQ_of_nat 52 52 (lng2_An_anchor2)). Qed.

Theorem lng2_AnQ_anchor3 : QeqT ((Z.of_nat (lng2_An 3) # 1)%Q) (504 # 1)%Q.
Proof. apply (lng2_AnQ_of_nat 504 504 (lng2_An_anchor3)). Qed.

Theorem lng2_AnQ_anchor4 : QeqT ((Z.of_nat (lng2_An 4) # 1)%Q) (5136 # 1)%Q.
Proof. apply (lng2_AnQ_of_nat 5136 5136 (lng2_An_anchor4)). Qed.

(* ============================================================ *)
(* §E Q 面桥与合成预算引理（上肢装配使用形：匹配 (4/3)ⁿ 的预算）              *)
(* ============================================================ *)

(* A_n 的 Q 面（q_pow (2#1) n 承载 2ⁿ）：真使用 numer_int lni_qpow2_nat *)
Theorem lng2_AnQ_eq : forall n : nat,
  (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
  == ((Z.of_nat (lng2_An n) # 1)%Q).
Proof.
  intro n. unfold lng2_An. rewrite lni_qpow2_nat. apply bk_Qmul_nat.
Qed.

(* q_pow 指数可加 *)
Lemma lng2_qpow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b) == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction a as [| a IH].
  - cbn [Nat.add q_pow]. ring.
  - cbn [Nat.add q_pow]. rewrite IH. ring.
Qed.

(* 整底幂的 Q 面：q_pow (c#1) n == (cⁿ#1) *)
Lemma lng2_qpow_Znat : forall (c n : nat),
  q_pow ((Z.of_nat c # 1)%Q) n == ((Z.of_nat (c ^ n) # 1)%Q).
Proof.
  intros c n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH. apply bk_Qmul_nat.
Qed.

(* 合成率判定核：(64/3)ⁿ·(3/4)^m == 12ⁿ·(3/4)^{m−2n}
   ——12ⁿ = (64/3)ⁿ·(9/16)ⁿ = (64/3)ⁿ·(3/4)^{2n} 的 Q 面显式形 *)
Lemma lng2_budget_rhs_eq : forall (n m : nat), 2 * n <= m ->
  (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)
  == ((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n)).
Proof.
  intros n m Hm.
  pose proof (lng2_qpow_add (3 # 4)%Q (2 * n) (m - 2 * n)) as Hsplit.
  replace (2 * n + (m - 2 * n)) with m in Hsplit by lia.
  pose proof (lng2_qpow_add (3 # 4)%Q n n) as Hnn.
  replace (n + n) with (2 * n) in Hnn by lia.
  assert (Eb : ((64 # 3) * ((3 # 4) * (3 # 4)))%Q == (12 # 1)%Q) by reflexivity.
  transitivity ((q_pow (64 # 3)%Q n * (q_pow (3 # 4)%Q n * q_pow (3 # 4)%Q n))
                * q_pow (3 # 4)%Q (m - 2 * n))%Q.
  - rewrite Hsplit. rewrite Hnn. ring.
  - rewrite <- (lng2_qpow_Znat 12 n).
    transitivity (q_pow ((64 # 3) * ((3 # 4) * (3 # 4)))%Q n
                  * q_pow (3 # 4)%Q (m - 2 * n))%Q.
    + rewrite (bk_q_pow_mul (64 # 3)%Q ((3 # 4) * (3 # 4))%Q n).
      rewrite <- (bk_q_pow_mul (3 # 4)%Q (3 # 4)%Q n).
      reflexivity.
    + rewrite (lng_qpow_congr ((64 # 3) * ((3 # 4) * (3 # 4)))%Q (12 # 1)%Q n Eb).
      reflexivity.
Qed.

(* ★装配使用主件（匹配 (4/3)ⁿ 的预算引理，QleT' Set 面）：
   A_n·(3/4)^{m−2n} ≤ (64/3)ⁿ·(3/4)^m。
   装配读法：尾隙预算 (3/4)^{SM−2n} 配分母 A_n 后，增长全部折叠进
   κ := 64/3 的每 n 因子与 (3/4)^{SM} 的每 SM 因子；SM 斜率
   c > log_{4/3}(64/3) ≈ 10.64 时 κ·(3/4)^c < 1，增长不吞掉衰减。 *)
Theorem lng2_budget_compose : forall (n m : nat), 2 * n <= m ->
  QleT' ((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q)%Q)
        ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q).
Proof.
  intros n m Hm.
  assert (Hwpos : QleT' 0%Q (q_pow (3 # 4)%Q (m - 2 * n))).
  { apply Qle_to_QleT'. apply q_pow_nonneg.
    unfold Qle. cbn [Qnum Qden]. lia. }
  eapply qleT'_trans.
  - apply qleT'_mult_compat_l.
    + exact Hwpos.
    + apply Qle_to_QleT'. apply bk_Qle_nat. apply lng2_An_le_12pow.
  - apply qeq_leT'.
    symmetry.
    transitivity ((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q.
    + apply (lng2_budget_rhs_eq n m Hm).
    + apply Qmult_comm.
Qed.

(* ============================================================ *)
(* §F L_n 肢使用面（HansonLcm 在册件直取；L_n ≤ 4ⁿ 未达——见 §G 注记）       *)
(* ============================================================ *)

Definition lng2_Ln (n : nat) : nat := hl_lcm_upto n.

Theorem lng2_Ln_le_fact : forall n : nat, lng2_Ln n <= fact n.
Proof. intro n. unfold lng2_Ln. apply hl_lcm_le_fact. Qed.

Theorem lng2_Ln_le_fact_t : forall n : nat, hl_le_t (lng2_Ln n) (fact n).
Proof. intro n. unfold lng2_Ln. apply hl_lcm_le_fact_t. Qed.

(* ============================================================ *)
(* §G 诚实边界登记（非虚报占位）                                            *)
(* ============================================================ *)
(* ① K < 4/3 档对 A_n 不可能：锚 A_1 = 6 > 4/3·A_0 已否证（数值事实，       *)
(*    非形式缺陷）；装配预算走⑦的「匹配 (4/3)ⁿ」合成率形 κ = 64/3。          *)
(* ② L_n ≤ 4ⁿ 未达：stdlib 9.1 nat 层零素数库（HansonLcm 头注已勘定），      *)
(*    L(n) < 3ⁿ（Hanson）与 Nair 型 L(n) ≤ 4ⁿ 皆需素数面工程（枚举机 +       *)
(*    primorial ≤ 4ⁿ 自举 + ψ 分解），超本件窗；本件如实交付在册最弱界        *)
(*    L_n ≤ n!（hl_lcm_le_fact 直取）并显式标注其非 4ⁿ 档。                  *)
(* ③ K ∈ [6,12] 判定区间：6ⁿ ≤ A_n ≤ 12ⁿ 双侧显式；真实倍率由锚组            *)
(*    ×6/×8.67/×9.69/×10.19 逼近，K 精化（如 q̃ 递推 (a+b)² ≤ 2a²+2b² 的     *)
(*    Vandermonde 卷积跳）留后续件。                                        *)
(* ============================================================ *)

(* ============================================================ *)
(* 假设审计留痕（G1/G4 取证块）＋ 可执行见证提取闭合（G3）                    *)
(* ============================================================ *)

Print Assumptions lng2_qtilde_le_6pow.
Print Assumptions lng2_An_le_12pow.
Print Assumptions lng2_An_le_12pow_t.
Print Assumptions lng2_An_le_16pow_t.
Print Assumptions lng2_An_ge_6pow.
Print Assumptions lng2_An_anchor4.
Print Assumptions lng2_AnQ_anchor4.
Print Assumptions lng2_AnQ_eq.
Print Assumptions lng2_budget_compose.
Print Assumptions lng2_Ln_le_fact_t.

Separate Extraction lng2_An.
