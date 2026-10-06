(* ============================================================ *)
(* abl_Pr_erdos_theta.v —— 素数域第 9 件：Erdős 路线第二段桥接件      *)
(* 模块名：abl_Pr_erdos_theta                                        *)
(* 数学使命：素数计数函数 θ 的构造性 Chebyshev 型线性界（nat 全量形）。   *)
(*   经典 θ(N) ＝ Σ_{p ≤ N} ln p 在 nat 层以 primorial（N 以内全部素数   *)
(*   之积）承载：θ(N) ≤ 4·ln2·N 的构造性等价形为                       *)
(*     pec_prim N ≤ 4^(2N)。                                          *)
(*   证明结构（Erdős 二项式窗法的 dyadic 望远镜）：                     *)
(*   ①窗口拼接：pec_win a (k+k′) ＝ pec_win a k ++ pec_win (a+k) k′       *)
(*     （区间 (a, a+k+k′] 的素数表按二分段拆开），积对拼接可乘。          *)
(*   ②primorial 的倍步恒等式：pec_prim(2^(j+1)) ＝                       *)
(*     pec_prim(2^j) · ∏_{2^j < p ≤ 2^(j+1)} p——半开区间 (1,2^(j+1)]     *)
(*     的素数表按 (1,2^j] 与 (2^j,2^(j+1)] 二分。                       *)
(*   ③窗积上界：∏_{n < p ≤ 2n} p ≤ C(2n,n) ≤ 4^n（直引前任件             *)
(*     abl_Pr_erdos_core 的 pec_erdos_skeleton 两肢），并附严格形         *)
(*     ∏_{n<p≤2n} p ＋ 2 ≤ 4^n（中项 C(2n,n) 与行和两端两个 1 并存）。    *)
(*   ④dyadic 归纳：pec_prim(2^j) ≤ 4^(2^j − 1)；                        *)
(*   ⑤对数定位：每个 N ≥ 1 存在 K 使 2^K ≤ N < 2^(K+1)（Set 面 sigT      *)
(*     见证，构造性二分定位），单调性乘通后望远镜闭合：                   *)
(*     pec_prim N ≤ pec_prim(2^(K+1)) ≤ 4^(2^(K+1) − 1) ≤ 4^(2N)。       *)
(*   由此 θ(N) 的 Chebyshev 型线性常数取 4·ln2（经典 Erdős–Bertrand        *)
(*   论证的首段常数；进一步压常数需在窗积上累计 (2n+1) 分母，登记续建）。  *)
(* 依赖清单：件 1（abl_Pr_core_01：pr_prime／pr_prime_bool）＋前任件       *)
(*   abl_Pr_erdos_core（pec_win／pec_winprod／pec_mid／pec_erdos_skeleton／ *)
(*   pec_skeleton_lt）＋HansonLcm（hl_le_t／hl_le_to_le_t）＋纯 Stdlib    *)
(*   （Arith.Arith／Bool／List／Lia）。                                  *)
(* 构造性注记：全件零公理零承认零经典逻辑；主语句 pec_theta_bound 以      *)
(*   hl_le_t（Id (Nat.leb _ _) true，Set 面）承载，对数定位件 pec_log2_ex  *)
(*   以 sigT 给出可计算见证 K；Prop 面谓词（pr_prime、整除、下标成员）     *)
(*   仅作推理脚手架（前任件同款约定）；pec_prim／pec_win／pec_winprod      *)
(*   皆一阶 nat 定义可提取；文尾 Separate Extraction＋Print Assumptions   *)
(*   取证面，Obj.magic 计数零为交付判据之一。                             *)
(* 编译配方: 链编次序——本池 abl_Pr_core_01、abl_Pr_erdos_core 先行，        *)
(*   本件随后）：                                                        *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/       *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&      *)
(*   nice -19 rocq c -native-compiler no -Q                              *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 "" *)
(*   -Q . "" abl_Pr_erdos_theta.v                                       *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Bool Lia List.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_erdos_core.

(* ---- §1 窗口拼接与积代数 ---- *)

(* 空窗：区间 (a, a] 无素数（fix 首参无法展开，分档转换判定） *)
Lemma pec_win_nil : forall a : nat, pec_win a 0 = nil.
Proof.
  intros a. destruct a as [|a'].
  - reflexivity.
  - reflexivity.
Qed.

(* 素数窗拼接：区间 (a, a+k+k′] 的素数表（降序）＝ 高段 (a+k, a+k+k′] 表
   ++ 低段 (a, a+k] 表 *)
Lemma pec_win_app : forall a k k' : nat,
  pec_win a (k + k') = pec_win (a + k) k' ++ pec_win a k.
Proof.
  intros a k. induction k' as [|k' IH].
  - replace (k + 0) with k by lia.
    rewrite pec_win_nil. rewrite app_nil_l. reflexivity.
  - replace (k + S k') with (S (k + k')) by lia.
    cbn [pec_win].
    replace (a + S (k + k')) with (a + k + S k') by lia.
    destruct (pr_prime_bool (a + k + S k')) eqn:E.
    + rewrite IH. rewrite app_comm_cons. reflexivity.
    + exact IH.
Qed.

(* 折叠积对拼接可乘 *)
Lemma pec_prod_app : forall l1 l2 : list nat,
  fold_right Nat.mul 1 (l1 ++ l2) = fold_right Nat.mul 1 l1 * fold_right Nat.mul 1 l2.
Proof.
  induction l1 as [|q l1 IH]; intros l2.
  - cbn [fold_right app]. rewrite Nat.mul_1_l. reflexivity.
  - cbn [fold_right app]. rewrite IH. ring.
Qed.

(* 折叠积下界：成员全 ≥ 1 则积 ≥ 1 *)
Lemma pec_prod_ge1 : forall l : list nat,
  (forall x : nat, In x l -> 1 <= x) -> 1 <= fold_right Nat.mul 1 l.
Proof.
  induction l as [|q l IH]; intros H.
  - cbn [fold_right]. lia.
  - cbn [fold_right].
    assert (Hq : 1 <= q) by (apply H; left; reflexivity).
    assert (Hl : 1 <= fold_right Nat.mul 1 l)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    apply Nat.le_trans with (q * 1).
    + rewrite Nat.mul_1_r. exact Hq.
    + apply Nat.mul_le_mono_l. exact Hl.
Qed.

(* ---- §2 primorial 定义与窗积上界（使用前任件两肢） ---- *)

(* primorial：N 以内全部素数之积（区间 (1, N] 的素数表折叠；
   全部素数 ≥ 2 ＞ 1，故 (1, N] 表 ＝ N 以内素数全体） *)
Definition pec_prim (n : nat) : nat := fold_right Nat.mul 1 (pec_win 1 (n - 1)).

(* 窗积上界：∏_{n < p ≤ 2n} p ≤ C(2n,n) ≤ 4^n（pec_erdos_skeleton 两肢） *)
Lemma pec_winprod_le : forall n : nat, pec_winprod n <= 4 ^ n.
Proof.
  intro n. destruct (pec_erdos_skeleton n) as [_ [H1 H2]].
  apply Nat.le_trans with (pec_mid n).
  - apply hl_le_t_to_le. exact H1.
  - apply hl_le_t_to_le. exact H2.
Qed.

(* 窗积严格上界：n ≥ 1 → ∏_{n<p≤2n} p ＋ 2 ≤ 4^n（中项＋行和两端两个 1） *)
Lemma pec_winprod_lt : forall n : nat, 1 <= n -> pec_winprod n + 2 <= 4 ^ n.
Proof.
  intros n Hn. apply Nat.le_trans with (pec_mid n + 2).
  - apply Nat.add_le_mono.
    + apply hl_le_t_to_le. destruct (pec_erdos_skeleton n) as [_ [H1 _]]. exact H1.
    + apply Nat.le_refl.
  - apply hl_le_t_to_le. apply pec_skeleton_lt. exact Hn.
Qed.

(* ---- §3 倍步恒等式与 dyadic 归纳 ---- *)

(* 倍步恒等式：pec_prim(2^(j+1)) ＝ pec_prim(2^j) · ∏_{2^j < p ≤ 2^(j+1)} p *)
Lemma pec_prim_step : forall j : nat,
  pec_prim (2 ^ S j) = pec_prim (2 ^ j) * pec_winprod (2 ^ j).
Proof.
  intro j. unfold pec_prim.
  rewrite Nat.pow_succ_r'.
  replace (2 * 2 ^ j - 1) with (2 ^ j - 1 + 2 ^ j) by lia.
  rewrite (pec_win_app 1 (2 ^ j - 1) (2 ^ j)).
  rewrite pec_prod_app.
  assert (Hjp : 1 <= 2 ^ j) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  replace (1 + (2 ^ j - 1)) with (2 ^ j) by lia.
  rewrite Nat.mul_comm. reflexivity.
Qed.

(* dyadic 档界：pec_prim(2^j) ≤ 4^(2^j − 1)
   （归纳：每翻一档乘一个 ≤ 4^(2^j) 的窗积，指数 2^(j+1) − 1
   ＝ (2^j − 1) ＋ 2^j 恰账） *)
Lemma pec_prim_dyad_le : forall j : nat, pec_prim (2 ^ j) <= 4 ^ (2 ^ j - 1).
Proof.
  induction j as [|j IH].
  - cbn. lia.
  - rewrite pec_prim_step.
    apply Nat.le_trans with (4 ^ (2 ^ j - 1) * 4 ^ (2 ^ j)).
    + apply Nat.mul_le_mono; [exact IH | apply pec_winprod_le].
    + replace (2 ^ S j - 1) with (2 ^ j - 1 + 2 ^ j)
        by (rewrite Nat.pow_succ_r'; lia).
      rewrite Nat.pow_add_r. apply Nat.le_refl.
Qed.

(* ---- §4 对数定位与 primorial 单调性 ---- *)

(* 对数定位（Set 面 sigT，构造性二分）：N ≥ 1 → 存在 K 使
   2^K ≤ N < 2^(K+1)，见证 K 可计算 *)
Lemma pec_log2_ex : forall N : nat, 1 <= N ->
  { K : nat & 2 ^ K <= N /\ N < 2 ^ S K }.
Proof.
  intros N HN. induction N as [|N IH].
  - exfalso. lia.
  - destruct N as [|N'].
    + exists 0. split; cbn [Nat.pow]; lia.
    + assert (HN1 : 1 <= S N') by lia.
      destruct (IH HN1) as [K [Hlo Hhi]].
      destruct (le_lt_dec (2 ^ S K) (S (S N'))) as [Hle | Hgt].
      * exists (S K). split.
        -- exact Hle.
        -- rewrite Nat.pow_succ_r'. lia.
      * exists K. split; [lia | exact Hgt].
Qed.

(* primorial 单调：1 ≤ N ≤ M → pec_prim N ≤ pec_prim M
   （窗表前缀拼接：长表 ＝ 前段 ++ (N, M] 段，后段积 ≥ 1） *)
Lemma pec_prim_monotone : forall N M : nat,
  1 <= N -> N <= M -> pec_prim N <= pec_prim M.
Proof.
  intros N M HN HM. unfold pec_prim.
  replace (M - 1) with (N - 1 + (M - N)) by lia.
  rewrite (pec_win_app 1 (N - 1) (M - N)).
  rewrite pec_prod_app.
  replace (1 + (N - 1)) with N by lia.
  rewrite Nat.mul_comm.
  apply Nat.le_trans with (fold_right Nat.mul 1 (pec_win 1 (N - 1)) * 1).
  + rewrite Nat.mul_1_r. apply Nat.le_refl.
  + apply Nat.mul_le_mono_l. apply pec_prod_ge1.
    intros x Hx. apply pec_win_in in Hx. destruct Hx as [Hp _].
    unfold pr_prime in Hp. destruct Hp as [Hp2 _]. lia.
Qed.

(* ---- §5 主语句：θ 的 Chebyshev 型线性界（nat 构造形） ---- *)

(* 主定理（Set 面承载）：pec_prim N ≤ 4^(2N)
   ——θ(N) ≤ 4·ln2·N 的 nat 等价形。望远镜：N 落档 [2^K, 2^(K+1))
   → pec_prim N ≤ pec_prim(2^(K+1)) ≤ 4^(2^(K+1) − 1) ≤ 4^(2N)
   （末步用 2^(K+1) ＝ 2·2^K ≤ 2N）。 *)
Theorem pec_theta_bound : forall N : nat, 1 <= N ->
  hl_le_t (pec_prim N) (4 ^ (2 * N))%nat.
Proof.
  intros N HN. apply hl_le_to_le_t.
  destruct (pec_log2_ex N HN) as [K [Hlo Hhi]].
  apply Nat.le_trans with (pec_prim (2 ^ S K)).
  - apply pec_prim_monotone; [exact HN | lia].
  - apply Nat.le_trans with (4 ^ (2 ^ S K - 1)).
    + apply pec_prim_dyad_le.
    + apply (Nat.pow_le_mono_r 4 (2 ^ S K - 1) (2 * N)).
      * lia.
      * rewrite Nat.pow_succ_r'. lia.
Qed.

(* nat 面 ≤ 推论 *)
Theorem pec_primorial_linear : forall N : nat, 1 <= N -> pec_prim N <= 4 ^ (2 * N).
Proof.
  intros N HN. apply hl_le_t_to_le. apply pec_theta_bound. exact HN.
Qed.

(* ---- §6 数值定装烟测（unary 打点纪律，vm_compute） ---- *)

Lemma pec_smoke_prim1 : pec_prim 1 = 1.
Proof. cbn [pec_prim pec_win fold_right]. reflexivity. Qed.

Lemma pec_smoke_win19 : pec_win 1 9 = (7 :: 5 :: 3 :: 2 :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_prim10 : pec_prim 10 = 210.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_win49 : pec_win 4 9 = (13 :: 11 :: 7 :: 5 :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_theta6 : (Nat.leb (pec_prim 6) (4 ^ 6))%bool = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- §7 公理审计（Print Assumptions 取证面）与提取检验 ---- *)

Print Assumptions pec_win_app.
Print Assumptions pec_prod_app.
Print Assumptions pec_prod_ge1.
Print Assumptions pec_winprod_le.
Print Assumptions pec_winprod_lt.
Print Assumptions pec_prim_step.
Print Assumptions pec_prim_dyad_le.
Print Assumptions pec_log2_ex.
Print Assumptions pec_prim_monotone.
Print Assumptions pec_theta_bound.
Print Assumptions pec_primorial_linear.

From Stdlib Require Import Extraction.
Separate Extraction pec_prim pec_win pec_winprod.
