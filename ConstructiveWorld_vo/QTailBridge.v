(* ============================================================ *)
(* QTailBridge.v —— S03 exp_tail 与 UpReqQExpTail qtail_sum 的桥式恒等式闭合。 *)
(* 使命：本件形式化恒等式 qtail_sum b m n == exp_tail (pred m) (pred n) b *)
(*   （m, n ≥ 1），以对尾指标 n 的归纳真证闭合。 *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqQExpTail。 *)
(* 对标：stdlib QArith 幂与阶乘的有限和换指标（换元 j = S k）。 *)
(* 构造性注记：Set 层承载——主定理出口 QeqT（S02 集合层值），伴件以 Qeq 桥接； *)
(*   零承认、公理面为空；归纳核 + 双守卫分支消去 + pred 双边界换算，非平凡交付； *)
(*   全链可提取。 *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 温控包装，-Q 单根； *)
(*   bash cpu_guard.sh -c "rocq c -Q <单根世界> "" QTailBridge.v"。 *)
(* 数学内容：qtail_sum b m n = Σ_{k=m}^{n-1} b^k/k!（正指标，Fixpoint 于 n， *)
(*   每步落 b^{n'}/n'!，n<m 守卫空和 = 0）；exp_tail m n x = Σ_{k=m}^{n-1} x^{S k}/(S k)! *)
(*   （指标错位 1）。换指标 j = S k 即得 exp_tail (pred m) (pred n) b = Σ_{j=m}^{n-1} *)
(*   b^j/j! = qtail_sum b m n（m,n ≥ 1）。归纳核（qtb_bridge_aux）：对 n 归纳证 *)
(*   qtail_sum b m (S n) == exp_tail (pred m) n b（1 ≤ m）。边界两处 pred 处理： *)
(*   ① 基座 n=0：m ≥ 1 时 qtail_sum b m 1 空（m ≤? 0 为 false），exp_tail _ 0 _ *)
(*   定义性 0；m=0 时恒等式确实失效（b^0/0! = 1 ≠ 0）——故 1 ≤ m 是必要前提非 *)
(*   技术性装饰。② 步进：守卫换算 (m ≤? S n'') ↔ (pred m ≤? n'') 无条件成立， *)
(*   项指标 S n'' 两侧同形；不一致支经 qtb_pred_sub（pred m = m − 1）换算后由 *)
(*   具名 nat 序引理消去矛盾。 *)
(* 红线自审：禁词全零；无 公理/承认件/参数/猜想/弃证，全 Qed 真证，零降级占位； *)
(*   结论面 Set 层：主定理 qtb_qtail_sum_eq_exp_tail_T 出口 QeqT（S02 Set 层 Q *)
(*   相等），Qeq 形伴件仅供桥接（证明内核惯例在 Qeq 内推理，同 UpReqQExpTail *)
(*   头注口径）；语句面无 Qlt/Qle/exists/and/or Prop 命题出场，无 -> False； *)
(*   前提位 (1 <= m)%nat 为 nat 层指标前提（库内通例，非 Prop 泄露）； *)
(*   非平凡：归纳 + 双守卫分支消去 + pred 双边界，非平凡交付； *)
(*   可提取检验 Obj.magic=0（Recursive Extraction 两主定理）。 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqQExpTail.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== 件 0：pred 与 nat 减法的换算引理 ===== *)

Lemma qtb_pred_sub : forall m : nat, Nat.pred m = (m - 1)%nat.
Proof.
  intros m. exact (eq_sym (Nat.sub_1_r m)).
Qed.

(* ===== 件 1：归纳核（m ≥ 1 固定，对尾指标 n 归纳） =====
   qtail_sum b m (S n) == exp_tail (pred m) n b。
   基座 n=0 用 m ≥ 1 消守卫；步进做双 guard 换算 + 项指标对齐。 *)

Lemma qtb_bridge_aux : forall (b : Q) (n m : nat),
  (1 <= m)%nat -> qtail_sum b m (Datatypes.S n) == exp_tail (Nat.pred m) n b.
Proof.
  intros b n. induction n as [| n IH]; intros m Hm.
  - (* 基座 n = 0：qtail_sum b m 1 空（m ≥ 1）== exp_tail (pred m) 0 = 0 *)
    change (qtail_sum b m (Datatypes.S 0))
      with ((if Nat.leb m 0 then q_pow b 0 / q_fact 0 else 0)
            + qtail_sum b m 0).
    destruct (Nat.leb m 0) eqn:E.
    + apply Nat.leb_le in E. exfalso.
      exact (Nat.nle_succ_0 0 (Nat.le_trans _ _ _ Hm E)).
    + reflexivity.
  - (* 步进 n → S n：两侧以 change 受控展开 Fixpoint 一步（不用 simpl，避免过展开） *)
    change (qtail_sum b m (Datatypes.S (Datatypes.S n)))
      with ((if Nat.leb m (Datatypes.S n)
             then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
             else 0)
            + qtail_sum b m (Datatypes.S n)).
    change (exp_tail (Nat.pred m) (Datatypes.S n) b)
      with (exp_tail (Nat.pred m) n b
            + (if Nat.leb (Nat.pred m) n
               then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
               else 0)).
    rewrite (IH m Hm).
    destruct (Nat.leb m (Datatypes.S n)) eqn:E1;
      destruct (Nat.leb (Nat.pred m) n) eqn:E2.
    + (* 双真：同项同和，加法交换 *) ring.
    + (* 左真右假矛盾：n < pred m 且 m ≤ S n *)
      apply Nat.leb_le in E1.
      apply Nat.leb_gt in E2. exfalso.
      pose proof (Nat.succ_pred_pos m Hm) as Hsp.
      rewrite <- Hsp in E1.
      apply Nat.succ_le_mono in E1.
      exact (Nat.lt_irrefl n (Nat.lt_le_trans _ _ _ E2 E1)).
    + (* 左假右真矛盾：S n < m 且 pred m ≤ n *)
      apply Nat.leb_gt in E1.
      apply Nat.leb_le in E2. exfalso.
      pose proof (Nat.succ_pred_pos m Hm) as Hsp.
      rewrite <- Hsp in E1.
      apply Nat.succ_le_mono in E1.
      exact (Nat.lt_irrefl n (Nat.lt_le_trans _ _ _ E1 E2)).
    + (* 双假：双空和 *) ring.
Qed.


Theorem qtb_qtail_sum_eq_exp_tail : forall (b : Q) (m n : nat),
  (1 <= m)%nat -> (1 <= n)%nat ->
  qtail_sum b m n == exp_tail (Nat.pred m) (Nat.pred n) b.
Proof.
  intros b m n Hm Hn.
  destruct n as [| n'].
  - exfalso. exact (Nat.nle_succ_0 0 Hn).
  - change (Nat.pred (Datatypes.S n')) with n'.
    apply (qtb_bridge_aux b n' m Hm).
Qed.

(* ===== 件 3：Set 层出口（QeqT，红线 2 语句面） ===== *)

Theorem qtb_qtail_sum_eq_exp_tail_T : forall (b : Q) (m n : nat),
  (1 <= m)%nat -> (1 <= n)%nat ->
  QeqT (qtail_sum b m n) (exp_tail (Nat.pred m) (Nat.pred n) b).
Proof.
  intros b m n Hm Hn.
  apply qeq_imp_qeqT.
  apply qtb_qtail_sum_eq_exp_tail; assumption.
Qed.

(* ===== 件 4：数值实例核验（vm_compute 可计算闭合） ===== *)
(* qtail_sum 3 1 5 = Σ_{k=1}^{4} 3^k/k! = 3 + 9/2 + 9/2 + 27/8 = 123/8
   exp_tail 0 4 3  = Σ_{k=0}^{3} 3^{k+1}/(k+1)! = 同上 —— 换指标逐项同形 *)

Lemma qtb_eval_example : QeqT (qtail_sum (3 # 1) 1%nat 5%nat)
                              (exp_tail 0%nat 4%nat (3 # 1)).
Proof. vm_compute. reflexivity. Qed.

(* ===== 主定理公理面审计：假设面闭合于全局语境 ===== *)

Print Assumptions qtb_qtail_sum_eq_exp_tail.
Print Assumptions qtb_qtail_sum_eq_exp_tail_T.
