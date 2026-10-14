(* ===================================================================== *)
(* 模块：u5c_z3_m2p_ledger.v                                              *)
(* 使命：M2′ 篇幅级主铸·第一层（骨架前代已铸·本件修复定稿）。      *)
(*   承 gapB 引擎件（zb2gb_C_step／zb2gb_G_sylv）与既有勘定（M2′=篇幅级：  *)
(*   步进归纳需乘法再注入的全局账本），铸该账本的骨架六件：                 *)
(*   §1 锚点账本方程（本件主定理·精确 nat 恒等式）：                         *)
(*      z2v_C (P_k) · P_k^(k−1) = P_k · z2v_C (P_k − 1)   （k ≥ 1）        *)
(*      ——「n 含 Sylvester 除子时增值积续满」的精确形态；锚点处增值积       *)
(*      G(P_k)(P_k) = P_k^(k−1)（满档再注入的 C 面读出）。                 *)
(*   §2 证书机（截断分母路线·面宽 n ≤ 42）：分母尾折叠桥                    *)
(*      z2v_den n n = z2v_den 4 n＋判定器 zb3m_Cden4／zb3m_leb_true／      *)
(*      zb3m_all_le。                                                     *)
(*   §3 反局部窗证书（编译化）：C(11) > 3^6·C(5) 且 C(13) > 3^7·C(6)       *)
(*      ——机器证明任何长度 ≤7 的窗口级步进归纳必假，全局账本必要性         *)
(*      在卷（三碰壁实录的编译确证）。计算路线＝C 步进机链：            *)
(*      C(11) = 924·C(6)、C(13) = 6006·C(6)——分子面不展开 fact 11/fact 13  *)
(*      （nat 一元表示下 ≈ 4e7／6.2e9 的 vm_compute 分子墙，直展路线       *)
(*      已核废）。                                                        *)
(*   §4 基座闭合起步段：∀n∈[1,10]，z2v_C n ≤ 3^n（递归判定证书             *)
(*      zb3m_all_le 10 = true，由步进机链式十档 C 值常数表折返；分母走      *)
(*      四因子截断面 z2v_den 4 n 桥回全积。计算边界=nat 一元表示            *)
(*      （fact 10 的内核一元转换实测 17+ CPU 分钟不归、fact 11 = 4e7 起      *)
(*      vm_compute 直展不可行——直展路线核废），11..42 档与熵段一并留残。    *)
(*      ——熵不等式分析段（n ≥ 43 档）的基座锚位。                          *)
(*   §5 HM2 槽接口显式披露（诚实接口律）：槽形 NatLe (z2v_C n) (3^n) 的    *)
(*      基座实例（[1,10] 档）＋全称形使用关系；残位=n ≥ 11 全段（11..42    *)
(*      档机器边界与 n ≥ 43 熵段一并留残），沿 gapB 自陈（Σ ln a_i / a_i  *)
(*      < ln 3 的 nat 化或等价强组合论证），非本件新增。                    *)
(* 诚实申报：§4 为有限域穷举判定（10 档逐档机器判定·步进机常数链）经        *)
(*   折返升格的 ∀ 语句，                                                   *)
(*   非解析证明——其证明地位=「K≤3 层的计算闭合」，与 gapB 数值锚同族但     *)
(*   为全称形；§1 为全强度解析骨架件（精确恒等式）；§3 两窗为精确 nat      *)
(*   不等式（步进机链式展开）。M2′ 终口仍开放。                            *)
(* 数学内容：Hanson, Canad. Math. Bull. 15 (1972) 引理组；C(n) :=          *)
(*   n!/∏_i⌊n/a_i⌋!（a_i 为 Sylvester 序列），P_k = a_1⋯a_k。              *)
(* 依赖：Stdlib（QArith/ZArith/Arith/Lia/Factorial）；缓存根 HansonLcm、    *)
(*   Hanson3Pow、S01_BaseRing、S02_CauchyComplete；池件 abl_z2_dub3、      *)
(*   abl_z2_valbridge、u5c_zeta2_gapB（引擎正本，零重述）。                *)
(* 构造性：零公理声明、零承认、零经典逻辑；主链为精确 nat 恒等式与有界判定； *)
(*   §3/§2 机器计算收尾系有界穷举判定（非空壳 exact），§1 全程代数推导；    *)
(*   Prop 面语句均为 nat 层支撑面（gapB 同款地位），Set 面出口=§4          *)
(*   zb3m_HM2_face（NatLe 承载）。                                        *)
(* 编译配方：rocq c -native-compiler no -q -Q . "" u5c_z3_m2p_ledger.v     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith.
From Stdlib Require Import Arith.Factorial Lia.
From Stdlib Require Import Extraction.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import abl_z2_dub3.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.

Close Scope Q_scope.

(* ===================================================================== *)
(* §0 基础面：P_k 与 2^k 的序关系                                          *)
(* ===================================================================== *)

(* 2^k ≥ 1（任意 k） *)
Lemma zb3m_pow2_pos : forall k : nat, (1 <= 2 ^ k)%nat.
Proof.
  induction k as [| k IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* P_k ≥ 1（2^k ≤ P_k 的直读） *)
Lemma zb3m_P_pos : forall k : nat, (1 <= z2d_sylv_P k)%nat.
Proof.
  intro k. pose proof (zb2gb_sylvP_ge_pow2 k). pose proof (zb3m_pow2_pos k). lia.
Qed.

(* k < 2^k（Sylvester 增长锚的自足版） *)
Lemma zb3m_pow2_gt : forall k : nat, (k < 2 ^ k)%nat.
Proof.
  induction k as [| k IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* P_k ≥ 2（k ≥ 1） *)
Lemma zb3m_P_ge2 : forall k : nat, (1 <= k)%nat -> (2 <= z2d_sylv_P k)%nat.
Proof.
  intros k Hk. pose proof (zb2gb_sylvP_ge_pow2 k) as H.
  pose proof (zb3m_pow2_pos k) as H2.
  destruct k as [| k']; [lia |].
  rewrite Nat.pow_succ_r' in H. rewrite Nat.pow_succ_r' in H2. lia.
Qed.

(* k ≤ P_k（k ≥ 1；锚点指标的合法性） *)
Lemma zb3m_k_le_P : forall k : nat, (1 <= k)%nat -> (k <= z2d_sylv_P k)%nat.
Proof.
  intros k Hk. pose proof (zb2gb_sylvP_ge_pow2 k) as H1.
  pose proof (zb3m_pow2_gt k) as H2. lia.
Qed.

(* ===================================================================== *)
(* §1 锚点账本方程（主定理）                                               *)
(* ===================================================================== *)

(* Sylvester a 序单调：a_j ≤ a_{S j}
   （a_k = P_k + 1，P_{S k} = P_k·(P_k+1) ≥ P_k） *)
Lemma zb3m_a_mono : forall j : nat, (z2d_sylv_a j <= z2d_sylv_a (Datatypes.S j))%nat.
Proof.
  intro j. unfold z2d_sylv_a. cbn [z2d_sylv_P].
  apply Nat.le_trans with (m := (z2d_sylv_P j * 1 + 1)%nat).
  - lia.
  - apply Nat.add_le_mono_r. apply Nat.mul_le_mono_l. pose proof (zb3m_P_pos j). lia.
Qed.

(* 链式单调：a_j ≤ a_{j+d} *)
Lemma zb3m_a_mono_chain : forall d j : nat,
  (z2d_sylv_a j <= z2d_sylv_a (j + d))%nat.
Proof.
  induction d as [| d IH]; intros j.
  - rewrite Nat.add_0_r. lia.
  - replace (j + Datatypes.S d) with (Datatypes.S j + d) by lia.
    pose proof (zb3m_a_mono j). pose proof (IH (Datatypes.S j)). lia.
Qed.

(* 增值积的尾折叠（本件核心机）：k ≤ N 且 n < a_k（n ≥ 1）则
   z2gb_G N n = z2gb_G k n——k 档以后诸因子为 1
   （a_{k} ≤ a_j、n < a_j ⟹ n mod a_j = n ≠ 0 ⟹ 因子取 1）。 *)
Lemma zb3m_G_ext : forall N k n : nat,
  (k <= N)%nat -> (1 <= n)%nat -> (n < z2d_sylv_a k)%nat ->
  z2gb_G N n = z2gb_G k n.
Proof.
  induction N as [| N' IH]; intros k n HkN Hn1 Hlt.
  - assert (Hk0 : (k = 0)%nat) by lia. subst k. reflexivity.
  - destruct (Nat.eq_dec k (Datatypes.S N')) as [Heq|Hne].
    + rewrite Heq. reflexivity.
    + assert (HkN' : (k <= N')%nat) by lia.
      assert (Ham : (n mod z2d_sylv_a N' = n)%nat).
      { apply Nat.mod_small.
        pose proof (zb3m_a_mono_chain (N' - k) k) as Hc.
        replace (k + (N' - k)) with N' in Hc by lia. lia. }
      cbn [z2gb_G].
      assert (Hb : Nat.eqb (n mod z2d_sylv_a N') 0 = false).
      { apply Nat.eqb_neq. rewrite Ham. pose proof (zb3m_P_pos N'). lia. }
      rewrite Hb.
      change (if false then n / z2d_sylv_a N' else 1) with 1.
      rewrite (IH k n HkN' Hn1 Hlt), Nat.mul_1_r. reflexivity.
Qed.

(* 锚点增值积折回：z2gb_G (P_k) (P_k) = z2gb_G k (P_k)
   （P_k < a_k = P_k + 1，k 档以后全 1 档） *)
Lemma zb3m_G_anchor : forall k : nat, (1 <= k)%nat ->
  z2gb_G (z2d_sylv_P k) (z2d_sylv_P k) = z2gb_G k (z2d_sylv_P k).
Proof.
  intros k Hk. apply zb3m_G_ext.
  - apply zb3m_k_le_P. exact Hk.
  - apply zb3m_P_pos.
  - unfold z2d_sylv_a. lia.
Qed.

(* 锚点增值积的幂形（满档再注入的 C 面读出）：
   z2gb_G (P_k) (P_k) = P_k^(k−1)（k ≥ 1）
   ——由 zb2gb_G_sylv（G k P_k · P_k = P_k^k）与尾折叠合成。 *)
Lemma zb3m_G_anchor_pow : forall k : nat, (1 <= k)%nat ->
  z2gb_G (z2d_sylv_P k) (z2d_sylv_P k) = (z2d_sylv_P k) ^ (k - 1)%nat.
Proof.
  intros k Hk.
  rewrite (zb3m_G_anchor k Hk).
  pose proof (zb2gb_G_sylv k) as HG.
  destruct k as [| k']; [lia |].
  replace (Datatypes.S k' - 1) with k' by lia.
  rewrite Nat.pow_succ_r' in HG.
  assert (Hnz : (z2d_sylv_P (Datatypes.S k') <> 0)%nat)
    by (pose proof (zb3m_P_pos (Datatypes.S k')); lia).
  rewrite (Nat.mul_comm (z2d_sylv_P (Datatypes.S k'))
             (z2d_sylv_P (Datatypes.S k') ^ k')) in HG.
  exact (proj1 (Nat.mul_cancel_r (z2gb_G (Datatypes.S k')
                    (z2d_sylv_P (Datatypes.S k')))
                 (z2d_sylv_P (Datatypes.S k') ^ k')
                 (z2d_sylv_P (Datatypes.S k')) Hnz) HG).
Qed.

(* 锚点账本方程（本件主定理·精确 nat 恒等式）：
   C(P_k) · P_k^(k−1) = P_k · C(P_k − 1)（k ≥ 1）。
   ——既有勘定所指「n 含 Sylvester 除子时增值积续满」的全局账本精确形态：
   锚点 n = P_k 处增值积满档 G = P_k^(k−1)，C 步进机的增量比恰为
   P_k / P_k^(k−1) = P_k^(2−k)。 *)
Theorem zb3m_C_anchor_ledger : forall k : nat, (1 <= k)%nat ->
  z2v_C (z2d_sylv_P k) * (z2d_sylv_P k) ^ (k - 1)
  = z2d_sylv_P k * z2v_C (z2d_sylv_P k - 1)%nat.
Proof.
  intros k Hk.
  pose proof (zb2gb_C_step (z2d_sylv_P k - 1)) as HC.
  assert (Hm1 : (1 <= z2d_sylv_P k - 1)%nat)
    by (pose proof (zb3m_P_ge2 k Hk); lia).
  specialize (HC Hm1).
  replace (Datatypes.S (z2d_sylv_P k - 1)) with (z2d_sylv_P k) in HC by lia.
  rewrite (zb3m_G_anchor_pow k Hk) in HC.
  exact HC.
Qed.

(* ===================================================================== *)
(* §2 证书机（截断分母路线·面宽 n ≤ 42）                                    *)
(* ===================================================================== *)
(* 计算性关键病灶（fail-loud 在卷）：z2v_den n n 全积迭代到 a_{n−1}，       *)
(*   n = 42 即须算 a_41（~万亿位）——vm_compute 结构性不可行（预演实测      *)
(*   实录）。故证书走四因子截断分母 z2v_den 4 n（只算 a_0..a_3 = 2,3,7,43），*)
(*   以尾折叠引理 zb3m_den_ext（逐层 zb2gb_den_tail1）桥回全积。            *)

(* 分母积尾折叠：m < a_k 则 z2v_den (k+d) m = z2v_den k m（d 层折叠） *)
Lemma zb3m_den_ext : forall d k m : nat,
  (m < z2d_sylv_a k)%nat -> z2v_den (k + d) m = z2v_den k m.
Proof.
  induction d as [| d IH]; intros k m Hlt.
  - rewrite Nat.add_0_r. reflexivity.
  - replace (k + Datatypes.S d) with (Datatypes.S (k + d)) by lia.
    pose proof (zb3m_a_mono_chain d k) as Hc.
    assert (Hc2 : (m < z2d_sylv_a (k + d))%nat) by lia.
    rewrite (zb2gb_den_tail1 (k + d) m Hc2).
    apply IH. exact Hlt.
Qed.

(* n < a_n（锚指标合法性） *)
Lemma zb3m_n_lt_a : forall n : nat, (n < z2d_sylv_a n)%nat.
Proof.
  intro n. unfold z2d_sylv_a. destruct n as [| n'].
  - cbn [z2d_sylv_P]. lia.
  - pose proof (zb3m_k_le_P (Datatypes.S n') ltac:(lia)). lia.
Qed.

(* a_4 = 1807 > 42（机器直算） *)
Lemma zb3m_a4_gt42 : (42 < z2d_sylv_a 4)%nat.
Proof. vm_compute. lia. Qed.

(* 四因子截断分母＝全积：n ≤ 42 < a_4 ⟹ z2v_den n n = z2v_den 4 n *)
Lemma zb3m_den4_eq : forall n : nat, (n <= 42)%nat -> z2v_den n n = z2v_den 4 n.
Proof.
  intros n Hn.
  assert (Hlt4 : (n < z2d_sylv_a 4)%nat) by (pose proof (zb3m_a4_gt42); lia).
  destruct (Nat.le_ge_cases n 4) as [Hle|Hge].
  - pose proof (zb3m_den_ext (4 - n) n n (zb3m_n_lt_a n)) as HE.
    replace (n + (4 - n)) with 4 in HE by lia.
    rewrite <- HE. reflexivity.
  - pose proof (zb3m_den_ext (n - 4) 4 n Hlt4) as HE.
    replace (4 + (n - 4)) with n in HE by lia.
    exact HE.
Qed.

(* 可提取判定器：截断分母 C 面 *)
Definition zb3m_Cden4 (n : nat) : nat := fact n / z2v_den 4 n.
Definition zb3m_leb_true (n : nat) : bool := Nat.leb (zb3m_Cden4 n) (3 ^ n).

(* 截断分母 C 面 = z2v_C（n ≤ 42 档） *)
Lemma zb3m_Cden4_eq : forall n : nat, (n <= 42)%nat -> zb3m_Cden4 n = z2v_C n.
Proof.
  intros n Hn. unfold zb3m_Cden4, z2v_C.
  rewrite (zb3m_den4_eq n Hn). reflexivity.
Qed.

(* ===================================================================== *)
(* §3 反局部窗证书（编译化·全局账本必要性确证）                             *)
(* ===================================================================== *)

(* 对角增值积折回（n ∈ [4,13]）：z2gb_G n n = z2gb_G 4 n
   （a_4 = 1807 起全 1 档，4 档以后诸因子为 1）。 *)
Lemma zb3m_G_diag_fold : forall n : nat, (4 <= n)%nat -> (n <= 13)%nat ->
  z2gb_G n n = z2gb_G 4 n.
Proof.
  intros n H1 H2. apply zb3m_G_ext; [lia | lia |].
  pose proof (zb3m_a4_gt42). lia.
Qed.

(* 对角增值积 1..13 档直读（截断面封闭小数·a_0..a_3 = 2,3,7,43）：
   C 步进机 1..12 档链所需的全部 G 值。 *)
Lemma zb3m_G_diag_vals :
  z2gb_G 1 1 = 1 /\ z2gb_G 2 2 = 1 /\ z2gb_G 3 3 = 1 /\
  z2gb_G 4 4 = 2 /\ z2gb_G 5 5 = 1 /\ z2gb_G 6 6 = 6 /\
  z2gb_G 7 7 = 1 /\ z2gb_G 8 8 = 4 /\ z2gb_G 9 9 = 3 /\
  z2gb_G 10 10 = 5 /\ z2gb_G 11 11 = 1 /\ z2gb_G 12 12 = 24 /\
  z2gb_G 13 13 = 1.
Proof.
  assert (H1 : z2gb_G 1 1 = 1) by reflexivity.
  assert (H2 : z2gb_G 2 2 = 1) by reflexivity.
  assert (H3 : z2gb_G 3 3 = 1) by reflexivity.
  assert (H4 : z2gb_G 4 4 = 2) by reflexivity.
  assert (H5 : z2gb_G 5 5 = 1).
  { rewrite (zb3m_G_diag_fold 5 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (H6 : z2gb_G 6 6 = 6).
  { rewrite (zb3m_G_diag_fold 6 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (H7 : z2gb_G 7 7 = 1).
  { rewrite (zb3m_G_diag_fold 7 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (H8 : z2gb_G 8 8 = 4).
  { rewrite (zb3m_G_diag_fold 8 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (H9 : z2gb_G 9 9 = 3).
  { rewrite (zb3m_G_diag_fold 9 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (HA : z2gb_G 10 10 = 5).
  { rewrite (zb3m_G_diag_fold 10 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (HB : z2gb_G 11 11 = 1).
  { rewrite (zb3m_G_diag_fold 11 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (HC : z2gb_G 12 12 = 24).
  { rewrite (zb3m_G_diag_fold 12 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (HD : z2gb_G 13 13 = 1).
  { rewrite (zb3m_G_diag_fold 13 ltac:(lia) ltac:(lia)). reflexivity. }
  (* 合取装配走纯项 exact（split 的 eq_refl 合一会对 z2gb_G n n 做全展
     转换，n ≥ 7 档即触发 a_6 ≈ 1.06e13 的一元表示——禁走）。 *)
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6
    (conj H7 (conj H8 (conj H9 (conj HA (conj HB (conj HC HD)))))))))))).
Qed.

(* C(6) > 0（截断分母四因子档直算，透明值 60） *)
Lemma zb3m_C6_pos : (0 < z2v_C 6)%nat.
Proof.
  pose proof (zb3m_Cden4_eq 6 ltac:(lia)) as E.
  rewrite <- E. vm_compute. lia.
Qed.

(* C(11) > 3^6 · C(5)：六步窗内归纳在 n=11 必假。
   计算路线＝C 步进机（zb2gb_C_step）5..10 档链：C(6) = C(5)、
   C(7) = 7·C(6)、C(8) = 2·C(7)、C(9) = 3·C(8)、C(10) = 2·C(9)、
   C(11) = 11·C(10)，合出 C(11) = 924·C(6)——全程不展开 fact 11
   （nat 一元表示分子墙在卷）。 *)
Lemma zb3m_window_fail_11 : (3 ^ 6 * z2v_C 5 < z2v_C 11)%nat.
Proof.
  destruct zb3m_G_diag_vals
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HA & HB & HC & HD).
  pose proof (zb2gb_C_step 5 ltac:(lia)) as E6.
  pose proof (zb2gb_C_step 6 ltac:(lia)) as E7.
  pose proof (zb2gb_C_step 7 ltac:(lia)) as E8.
  pose proof (zb2gb_C_step 8 ltac:(lia)) as E9.
  pose proof (zb2gb_C_step 9 ltac:(lia)) as EA.
  pose proof (zb2gb_C_step 10 ltac:(lia)) as EB.
  rewrite H6 in E6. rewrite H7 in E7. rewrite H8 in E8.
  rewrite H9 in E9. rewrite HA in EA. rewrite HB in EB.
  pose proof zb3m_C6_pos.
  replace (3 ^ 6) with 729 by reflexivity.
  lia.
Qed.

(* C(13) > 3^7 · C(6)：七步窗内归纳在 n=13 必假。
   计算路线＝C 步进机 6..12 档链：C(7) = 7·C(6)、…、C(11) = 924·C(6)、
   2·C(12) = C(11)、C(13) = 13·C(12)，合出 C(13) = 6006·C(6)——
   全程不展开 fact 13（同上分子墙）。 *)
Lemma zb3m_window_fail_13 : (3 ^ 7 * z2v_C 6 < z2v_C 13)%nat.
Proof.
  destruct zb3m_G_diag_vals
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HA & HB & HC & HD).
  pose proof (zb2gb_C_step 6 ltac:(lia)) as E7.
  pose proof (zb2gb_C_step 7 ltac:(lia)) as E8.
  pose proof (zb2gb_C_step 8 ltac:(lia)) as E9.
  pose proof (zb2gb_C_step 9 ltac:(lia)) as EA.
  pose proof (zb2gb_C_step 10 ltac:(lia)) as EB.
  pose proof (zb2gb_C_step 11 ltac:(lia)) as EC.
  pose proof (zb2gb_C_step 12 ltac:(lia)) as ED.
  rewrite H7 in E7. rewrite H8 in E8. rewrite H9 in E9.
  rewrite HA in EA. rewrite HB in EB. rewrite HC in EC. rewrite HD in ED.
  pose proof zb3m_C6_pos.
  replace (3 ^ 7) with 2187 by reflexivity.
  lia.
Qed.

(* ===================================================================== *)
(* §4 基座闭合（[1,10] 起步段）                                             *)
(* ===================================================================== *)

(* 判定器可靠性：布尔真 ⟹ 序界 *)
Lemma zb3m_leb_true_sound : forall n : nat, (n <= 42)%nat ->
  zb3m_leb_true n = true -> (z2v_C n <= 3 ^ n)%nat.
Proof.
  intros n Hn H. unfold zb3m_leb_true in H.
  rewrite (zb3m_Cden4_eq n Hn) in H.
  exact (proj1 (Nat.leb_le (z2v_C n) (3 ^ n)) H).
Qed.

(* 递归全称判定器：zb3m_all_le N = 逐档 1..N 全部通过 *)
Fixpoint zb3m_all_le (N : nat) : bool :=
  match N with
  | O => true
  | Datatypes.S N' => zb3m_all_le N' && zb3m_leb_true N
  end.

(* 全称判定器可靠性：n ≤ N 且证书真 ⟹ n 档通过 *)
Lemma zb3m_all_le_sound : forall N n : nat,
  (n <= N)%nat -> zb3m_all_le N = true -> (1 <= n)%nat ->
  zb3m_leb_true n = true.
Proof.
  induction N as [| N' IH]; intros n Hn Ha H1.
  - exfalso. lia.
  - cbn [zb3m_all_le] in Ha. apply andb_true_iff in Ha. destruct Ha as [Ha1 Ha2].
    destruct (Nat.eq_dec n (Datatypes.S N')) as [Heq|Hne].
    + rewrite Heq. exact Ha2.
    + assert (Hn' : (n <= N')%nat) by lia.
      exact (IH n Hn' Ha1 H1).
Qed.

(* 基座十档 C 值（步进机链式常数折出）：锚 C(1) = 1（一元小计算），
   1..9 档步进机 G 值代入后逐档线性解出——全程零大数材料化。 *)
Lemma zb3m_C_vals_chain :
  z2v_C 1 = 1 /\ z2v_C 2 = 2 /\ z2v_C 3 = 6 /\ z2v_C 4 = 12 /\
  z2v_C 5 = 60 /\ z2v_C 6 = 60 /\ z2v_C 7 = 420 /\ z2v_C 8 = 840 /\
  z2v_C 9 = 2520 /\ z2v_C 10 = 5040.
Proof.
  assert (V1 : z2v_C 1 = 1) by (vm_compute; reflexivity).
  destruct zb3m_G_diag_vals
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GA & GB & GC & GD).
  pose proof (zb2gb_C_step 1 ltac:(lia)) as E1.
  pose proof (zb2gb_C_step 2 ltac:(lia)) as E2.
  pose proof (zb2gb_C_step 3 ltac:(lia)) as E3.
  pose proof (zb2gb_C_step 4 ltac:(lia)) as E4.
  pose proof (zb2gb_C_step 5 ltac:(lia)) as E5.
  pose proof (zb2gb_C_step 6 ltac:(lia)) as E6.
  pose proof (zb2gb_C_step 7 ltac:(lia)) as E7.
  pose proof (zb2gb_C_step 8 ltac:(lia)) as E8.
  pose proof (zb2gb_C_step 9 ltac:(lia)) as E9.
  rewrite G2 in E1. rewrite G3 in E2. rewrite G4 in E3. rewrite G5 in E4.
  rewrite G6 in E5. rewrite G7 in E6. rewrite G8 in E7. rewrite G9 in E8.
  rewrite GA in E9.
  (* apply conj 纯结构拆分（split 的 eq_refl 合一会对 z2v_C k 做全展
     转换，k ≥ 7 档即触发 a_6 的一元表示墙——禁走）；数值逐档阶梯
     推进（逐档线性推进——十档合证超出 micromega 见证搜索界，
     实测 lia/nia 皆断，故禁一口并证）。 *)
  assert (W2 : z2v_C 2 = 2) by lia.
  assert (W3 : z2v_C 3 = 6) by lia.
  assert (W4 : z2v_C 4 = 12) by lia.
  assert (W5 : z2v_C 5 = 60) by lia.
  assert (W6 : z2v_C 6 = 60) by lia.
  assert (W7 : z2v_C 7 = 420) by lia.
  assert (W8 : z2v_C 8 = 840) by lia.
  assert (W9 : z2v_C 9 = 2520) by lia.
  (* 十档链接走精确代数消去：nat 字面量在 ≥ 5000 档被解释为
     Init.Nat.of_num_uint（abstract-large-number·防栈溢出官方行为），
     lia/zify 对该形态失能（内核转换不受影响）——故 tactic 内全部
     字面量压回 < 5000，以 2 * 2520 表 5040，末合取支由 exact 的
     转换容忍闭合。 *)
  assert (H5 : (5 <> 0)%nat) by discriminate.
  rewrite W9 in E9.
  rewrite (Nat.mul_comm (z2v_C 10) 5) in E9.
  change (10 * 2520) with (5 * (2 * 2520)) in E9.
  assert (WA' : z2v_C 10 = 2 * 2520)
    by exact (proj1 (Nat.mul_cancel_l (z2v_C 10) (2 * 2520) 5 H5) E9).
  exact (conj V1 (conj W2 (conj W3 (conj W4 (conj W5 (conj W6
    (conj W7 (conj W8 (conj W9 WA'))))))))).
Qed.

(* 基座证书本体：zb3m_all_le 10 = true。
   计算路线注记：布尔证书不经 vm_compute 直展——fact 10 的内核一元
   转换在本宿主实测 17+ CPU 分钟不归，直展路线核废（继承边界注记
   「fact 11 起 vm_compute 不可行」按本实测上修为含 fact 10 内核转换）；
   改由基座十档 C 值常数表（zb3m_C_vals_chain）经 Nat.leb_le 逐档
   折返为布尔真，判定地位不变。 *)
Lemma zb3m_base_cert_true : zb3m_all_le 10 = true.
Proof.
  assert (HC : forall n : nat, (1 <= n)%nat -> (n <= 10)%nat ->
               (z2v_C n <= 3 ^ n)%nat).
  { intros n Hn1 Hn10.
    pose proof zb3m_C_vals_chain
      as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VA).
    destruct n as [|[|[|[|[|[|[|[|[|[|[|n11]]]]]]]]]]].
    - lia.
    - rewrite V1. replace (3 ^ 1) with 3 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V2. replace (3 ^ 2) with 9 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V3. replace (3 ^ 3) with 27 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V4. replace (3 ^ 4) with 81 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V5. replace (3 ^ 5) with 243 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V6. replace (3 ^ 6) with 729 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V7. replace (3 ^ 7) with 2187 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V8. replace (3 ^ 8) with 6561 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite V9. replace (3 ^ 9) with 19683 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - rewrite VA. replace (3 ^ 10) with 59049 by reflexivity.
      apply Nat.leb_le. vm_compute. reflexivity.
    - lia. }
  assert (HL : forall n : nat, (1 <= n)%nat -> (n <= 10)%nat ->
               zb3m_leb_true n = true).
  { intros k Hk1 Hk10. unfold zb3m_leb_true.
    apply (proj2 (Nat.leb_le (zb3m_Cden4 k) (3 ^ k))).
    rewrite (zb3m_Cden4_eq k ltac:(lia)).
    apply HC; assumption. }
  assert (HA : forall n : nat, (n <= 10)%nat -> zb3m_all_le n = true).
  { intros k. induction k as [| k IH]; intro Hk.
    - reflexivity.
    - cbn [zb3m_all_le]. apply andb_true_iff. split.
      + apply IH. lia.
      + apply HL; lia. }
  apply (HA 10 (Nat.le_refl 10)).
Qed.

(* 基座闭合（n ≤ 10 起步段：a_3 = 7 已入账、a_4 = 1807 未及的机器可达前缀） *)
Theorem zb3m_C_le_3pow_base : forall n : nat,
  (1 <= n)%nat -> (n <= 10)%nat -> (z2v_C n <= 3 ^ n)%nat.
Proof.
  intros n H1 H10.
  apply (zb3m_leb_true_sound n); [lia |].
  exact (zb3m_all_le_sound 10 n H10 zb3m_base_cert_true H1).
Qed.

(* ===================================================================== *)
(* §5 HM2 槽接口显式披露（诚实接口律）                                     *)
(* ===================================================================== *)

(* HM2 槽形（与 u5c_z3_assembly_slot2 第三前提同型，NatLe Set 承载） *)
Definition zb3m_HM2_face (n : nat) : Set := NatLe (z2v_C n) (3 ^ n).

(* 槽的基座实例：n ∈ [1,10] 档已闭合（11..42 档机器边界留残） *)
Theorem zb3m_HM2_face_base : forall n : nat,
  (1 <= n)%nat -> (n <= 10)%nat -> zb3m_HM2_face n.
Proof.
  intros n H1 H42. unfold zb3m_HM2_face.
  apply NatLe_lift. apply zb3m_C_le_3pow_base; assumption.
Qed.

(* 槽的全称形使用关系：M2′ 全称形给定 ⟹ 装配槽 HM2 位逐点供给 *)
Theorem zb3m_HM2_face_from_M2 :
  (forall n : nat, (1 <= n)%nat -> zb3m_HM2_face n) ->
  forall m : nat, zb3m_HM2_face (Datatypes.S m).
Proof.
  intros H m. apply H. lia.
Qed.

(* ===================================================================== *)
(* §6 提取与假设审计                                                       *)
(* ===================================================================== *)

Separate Extraction zb3m_all_le zb3m_leb_true.

Print Assumptions zb3m_pow2_pos.
Print Assumptions zb3m_P_pos.
Print Assumptions zb3m_pow2_gt.
Print Assumptions zb3m_P_ge2.
Print Assumptions zb3m_k_le_P.
Print Assumptions zb3m_a_mono.
Print Assumptions zb3m_a_mono_chain.
Print Assumptions zb3m_G_ext.
Print Assumptions zb3m_G_anchor.
Print Assumptions zb3m_G_anchor_pow.
Print Assumptions zb3m_C_anchor_ledger.
Print Assumptions zb3m_window_fail_11.
Print Assumptions zb3m_window_fail_13.
Print Assumptions zb3m_leb_true_sound.
Print Assumptions zb3m_all_le_sound.
Print Assumptions zb3m_base_cert_true.
Print Assumptions zb3m_C_le_3pow_base.
Print Assumptions zb3m_HM2_face_base.
Print Assumptions zb3m_HM2_face_from_M2.
