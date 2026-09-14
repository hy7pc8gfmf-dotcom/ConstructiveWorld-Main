(* ============================================================ *)
(* ExpNegPos.v —— 席CWG：exp_neg 符号交错级数正性面（Q 标量层闭合）  *)
(* （20260914/15；主对话直执席，批次 E-STAGING-CWG）                 *)
(* ============================================================ *)
(* 使命：清偿 UpReqBanachExpNeg.v 挂账②「符号交错级数的正性面：      *)
(*   非本席」（UpReqBanachExpNeg.v:286-294，BanachExpNeg 侧最后一笔   *)
(*   挂账）。                                                       *)
(*                                                                *)
(* 【正性面落点判定（本席侦查定谳）】BanachAlg 类无序接口（bae 为     *)
(*   Set 承载等词，无 ≤_B 位），符号交错级数的「正性」在 Banach 层    *)
(*   无语句面——其诚实落点是 Q 标量层：exp(−x) 的部分和（交错级数）    *)
(*   在 0 ≤ x ≤ 1 全段非负、0 ≤ x < 1 严格正、且恒有下界 1−x。       *)
(*   与「Class 无 bneg 字段」同款口径：Banach 侧 (−1)^k 载体面由      *)
(*   bxn_series_mone_even/odd（UpReqBanachExpNeg.v 定形件）承载，    *)
(*   本件交付其标量供给面。全 x ≥ 0 档需 exp_add 型乘积恒等式（S03    *)
(*   e/o 配对战役在飞），按分层保底纪律不在本件硬攻，登记为升级方向。  *)
(*                                                                *)
(* 【方法（自足两引理，零 altsum 引擎依赖）】t_k := x^k/k! 满足       *)
(*   t_{k+1} ≤ t_k（x ≤ 1，pow_fact_mono_int + q_le_div_le）；       *)
(*   奇和 S_{2m+3} = S_{2m+1} + (t_{2m+2} − t_{2m+3}) 递增 ⟹         *)
(*   S_{2m+1} ≥ 1−x；偶和 S_{2m+2} = S_{2m+1} + t_{2m+2} ≥ 奇和。    *)
(*   故一切 n：1−x ≤ S_n 且 0 ≤ S_n；x < 1 时严格正。语句面全         *)
(*   QleT'/QltT（S02 bool 反映形）；Qle/Qlt 仅证内转译。              *)
(*                                                                *)
(* 红线自审：公理面七项禁词扫描零命中（逐项记录见交付报告）；  *)
(*   语句面零 Prop 泄露（QleT'/QltT 全 Set）；全件 Qed 真证；         *)
(*   G3 提取探针 Obj.magic=0（配方沿 E-STAGING-CWA 卡）；            *)
(*   checker = rocqchk（沿 E-STAGING-CWF 卡）。                     *)
(* 编译配方（cpu_guard 包装零裸调）：                                *)
(*   bash Live/tools/cpu_guard.sh 包 source Live/toolchain/env.sh   *)
(*   与 cd Live/build 后 rocq c -Q 点空名 ExpNegPos.v。              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* 件 0：算术助手（S03/S02 现成件拼装）                               *)
(* ============================================================ *)

(* 1 ≤ (S k)#1（自然后继的 Q 形单位下界） *)
Lemma enp_one_le_succ : forall k : nat,
  Qle 1 ((Z.of_nat (Datatypes.S k)) # 1).
Proof.
  intros k. unfold Qle. change (1%Q) with (1 # 1). simpl.
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1)%Z by lia.
  lia.
Qed.

(* 项递减（除法形）：0 ≤ x ≤ 1 ⟹ x^{S k}/(S k)! ≤ x^k/k!
   （pow_fact_mono_int 交叉形 + q_le_div_le 桥，均 S03 现成件） *)
Lemma enp_decr : forall (x : Q) (k : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (q_pow x (Datatypes.S k) / q_fact (Datatypes.S k))
      (q_pow x k / q_fact k).
Proof.
  intros x k H0 H1.
  assert (Hb : Qle x ((Z.of_nat (Datatypes.S k)) # 1)).
  { apply (Qle_trans x 1 ((Z.of_nat (Datatypes.S k)) # 1)).
    - exact H1.
    - apply enp_one_le_succ. }
  apply (q_le_div_le (q_pow x (Datatypes.S k)) (q_fact (Datatypes.S k))
                     (q_pow x k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat (k + 1))%Z in Hb by lia.
    exact (pow_fact_mono_int x k H0 Hb).
Qed.

(* 除非负：0 ≤ x ⟹ 0 ≤ x^k/k!（同分母桥） *)
Lemma enp_term_nonneg : forall (x : Q) (k : nat),
  Qle 0 x -> Qle 0 (q_pow x k / q_fact k).
Proof.
  intros x k H0.
  apply (Qle_trans 0 (0 / q_fact k) (q_pow x k / q_fact k)).
  - apply (qeq_le 0 (0 / q_fact k)).
    assert (Hz3 : 0 == 0 / q_fact k) by (unfold Qdiv; ring).
    exact Hz3.
  - apply (Qle_div_same_denom 0 (q_pow x k) (q_fact k)).
    + apply q_fact_pos.
    + apply q_pow_nonneg. exact H0.
Qed.

(* ============================================================ *)
(* 件 1：两步展开与奇起配对恒等式                                     *)
(* ============================================================ *)

(* exp_partial 两步展开（定义性 replace-by-refl） *)
Lemma enp_expSS : forall (x : Q) (n : nat),
  exp_partial (Datatypes.S (Datatypes.S n)) (Qopp x)
  == exp_partial n (Qopp x)
     + q_pow (Qopp x) (Datatypes.S n) / q_fact (Datatypes.S n)
     + q_pow (Qopp x) (Datatypes.S (Datatypes.S n))
       / q_fact (Datatypes.S (Datatypes.S n)).
Proof.
  intros x n.
  replace (exp_partial (Datatypes.S (Datatypes.S n)) (Qopp x))
    with (exp_partial (Datatypes.S n) (Qopp x)
          + q_pow (Qopp x) (Datatypes.S (Datatypes.S n))
            / q_fact (Datatypes.S (Datatypes.S n))) by reflexivity.
  replace (exp_partial (Datatypes.S n) (Qopp x))
    with (exp_partial n (Qopp x)
          + q_pow (Qopp x) (Datatypes.S n) / q_fact (Datatypes.S n))
    by reflexivity.
  ring.
Qed.

(* 奇起两步配对：S_{2m+3} == S_{2m+1} + t_{2m+2} − t_{2m+3} *)
Lemma enp_two_step_odd : forall (x : Q) (m : nat),
  exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x)
  == exp_partial (2 * m + 1) (Qopp x)
     + q_pow x (2 * m + 2) / q_fact (2 * m + 2)
     + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3)).
Proof.
  intros x m.
  rewrite (enp_expSS x (2 * m + 1)).
  (* 指数归一：S(2m+1)=2m+2（偶次）、S(S(2m+1))=S(2m+2)（奇次） *)
  replace (Datatypes.S (2 * m + 1))%nat with (2 * m + 2)%nat by lia.
  replace (2 * m + 2)%nat with (2 * Datatypes.S m)%nat by lia.
  (* 2m+2 偶次 → 符号消失；S(2m+2)=2m+3 奇次 → 取负 *)
  rewrite (q_pow_neg_even x (Datatypes.S m)).
  rewrite (q_pow_neg_odd x (Datatypes.S m)).
  (* HV2 增量修：nat 指标归一 S(2*S m) == 2m+3（两不同原子，ring 不做 nat 归一） *)
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (2 * m + 3)%nat by lia.
  (* HV2 增量修②：Qopp 穿 Qdiv 原子结构差（ring 不穿除法），Qeq 桥归一同形 *)
  assert (Hod : Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))
                == Qopp (q_pow x (2 * m + 3)) / q_fact (2 * m + 3))
    by (unfold Qdiv; ring).
  rewrite Hod.
  ring.
Qed.

(* 奇和单步递增：S_{2m+3} ≥ S_{2m+1}（配对项非负：t_{2m+3} ≤ t_{2m+2}） *)
Lemma enp_odd_step : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x)).
Proof.
  intros x m H0 H1.
  assert (Hstep := enp_two_step_odd x m).
  assert (Hd := enp_decr x (2 * m + 2) H0 H1).
  pose proof (Qopp_le_compat _ _ Hd) as Hopp.
  (* AA21 第3轮修：Hopp 内 nat 指标归一 S(2m+2)==2m+3（HV2 续接配方照方） *)
  replace (Datatypes.S (2 * m + 2))%nat with (2 * m + 3)%nat in Hopp by lia.
  (* Hopp : Qopp t_{2m+3} ≤ Qopp t_{2m+2} *)
  assert (HAB : Qle 0 (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
                       + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3)))).
  { apply (Qle_trans 0
      (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
       + Qopp (q_pow x (2 * m + 2) / q_fact (2 * m + 2)))).
    - apply (qeq_le 0
        (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
         + Qopp (q_pow x (2 * m + 2) / q_fact (2 * m + 2)))).
      ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + exact Hopp. }
  apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
    (exp_partial (2 * m + 1) (Qopp x)
     + (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
        + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))))
    (exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x))).
  - (* AA21 第3轮修②：LHS 原子形不能与 Qplus_le_compat 的 x+z 统一，中转 A+0 归位 *)
    apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 1) (Qopp x) + 0)
      (exp_partial (2 * m + 1) (Qopp x)
       + (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
          + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))))).
    + apply (qeq_le _ _). ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact HAB.
  - apply qeq_le. rewrite Hstep. ring.
Qed.

(* ============================================================ *)
(* 件 2：Prop 内衬主面（奇和下界 + 偶和承载 + 全 n 下界）              *)
(* ============================================================ *)

(* 奇和下界：S_{2m+1} ≥ 1−x（奇和递增归纳） *)
Lemma enp_odd_ge : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 -> Qle (1 - x) (exp_partial (2 * m + 1) (Qopp x)).
Proof.
  intros x m H0 H1. induction m as [| m IH].
  - assert (Hv : exp_partial 1 (Qopp x) == 1 - x).
    { simpl. unfold Qdiv.
      replace (Qinv (1 * 1)) with 1 by reflexivity.
      ring. } (* AA21：Qdiv_1_r 系幻觉名；Qdiv=Qmult x (Qinv y)，Qinv(1*1) 非环原子须 reflexivity-replace 归约后 ring *)
    apply (qeq_le (1 - x) (exp_partial 1 (Qopp x))).
    exact (Qeq_sym _ _ Hv).
  - assert (Hstep := enp_odd_step x m H0 H1).
    replace (Datatypes.S (Datatypes.S (2 * m + 1)))
      with (2 * Datatypes.S m + 1)%nat in Hstep by lia.
    apply (Qle_trans (1 - x)
      (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * Datatypes.S m + 1) (Qopp x))).
    + exact IH.
    + exact Hstep.
Qed.

(* 偶和承载：S_{2m+2} ≥ S_{2m+1}（加非负项） *)
Lemma enp_even_ge_odd : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 2) (Qopp x)).
Proof.
  intros x m H0 H1.
  assert (Hu : exp_partial (Datatypes.S (2 * m + 1)) (Qopp x)
               == exp_partial (2 * m + 1) (Qopp x)
                  + q_pow (Qopp x) (Datatypes.S (2 * m + 1))
                    / q_fact (Datatypes.S (2 * m + 1))) by reflexivity.
  assert (Ht : q_pow (Qopp x) (Datatypes.S (2 * m + 1))
               == q_pow x (Datatypes.S (2 * m + 1))).
  { replace (Datatypes.S (2 * m + 1)) with (2 * Datatypes.S m)%nat by lia.
    apply q_pow_neg_even. }
  assert (Hn : Qle 0 (q_pow x (Datatypes.S (2 * m + 1))
                           / q_fact (Datatypes.S (2 * m + 1)))).
  { apply enp_term_nonneg. exact H0. }
  apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
    (exp_partial (2 * m + 1) (Qopp x)
     + q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1)))
    (exp_partial (2 * m + 2) (Qopp x))).
  - (* AA21 修④：原子LHS 不能与 Qplus_le_compat 的 x+z 统一，中转 A+0 归位（同修②） *)
    apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 1) (Qopp x) + 0)
      (exp_partial (2 * m + 1) (Qopp x)
       + q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1)))).
    + apply (qeq_le _ _). ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hn.
  - (* AA21 修⑤：nat 指标归一 2m+2==S(2m+1) 供 Hu 重写位匹配 *)
    replace (2 * m + 2)%nat with (Datatypes.S (2 * m + 1))%nat by lia.
    apply qeq_le. rewrite Hu. rewrite <- Ht. ring.
Qed.

(* 全 n 下界（Prop 内衬）：1−x ≤ S_n *)
Lemma enp_ge_all : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 ->
  Qle (1 - x) (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1.
  destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - subst n. destruct m as [| m'].
    + (* n = 0：S_0 = 1 ≥ 1−x ⟸ x ≥ 0 *)
      apply (Qle_trans (1 - x) (1 + Qopp x) 1).
      * apply (qeq_le (1 - x) (1 + Qopp x)). ring.
      * apply (Qle_trans (1 + Qopp x) (1 + 0) 1).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ (* AA21 修⑥：RHS 原子 0 与 Qopp_le_compat 结论 -b 不统一，Qopp 0 中转 *)
              apply (Qle_trans (Qopp x) (Qopp 0) 0).
              ** apply Qopp_le_compat. exact H0.
              ** apply (qeq_le _ _). ring.
        -- apply (qeq_le (1 + 0) 1). ring.
    + replace (2 * Datatypes.S m')%nat
        with (Datatypes.S (2 * m' + 1))%nat by lia.
      apply (Qle_trans (1 - x)
        (exp_partial (2 * m' + 1) (Qopp x))
        (exp_partial (Datatypes.S (2 * m' + 1)) (Qopp x))).
      * apply enp_odd_ge; assumption.
      * (* AA21 修⑦：nat 指标归一 S(2m'+1)==2m'+2 供 enp_even_ge_odd 消费位统一 *)
        replace (Datatypes.S (2 * m' + 1))%nat with (2 * m' + 2)%nat by lia.
        apply enp_even_ge_odd; assumption.
  - subst n. apply enp_odd_ge; assumption.
Qed.

(* ============================================================ *)
(* 件 3：Set 语句面出口（挂账②清偿三件）                              *)
(* ============================================================ *)

(* 主件 A（下界面）：0 ≤ x ≤ 1 ⟹ ∀n, 1−x ≤ exp_partial n (−x) *)
Theorem enp_exp_partial_ge : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' (1 - x) (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1.
  apply Qle_to_QleT'.
  apply enp_ge_all.
  - apply QleT'_to_Qle. exact H0.
  - apply QleT'_to_Qle. exact H1.
Qed.

(* 主件 B（非负面）：0 ≤ x ≤ 1 ⟹ ∀n, 0 ≤ exp_partial n (−x) *)
Theorem enp_exp_partial_nonneg : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' 0 (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1.
  (* AA21 修⑧：先 Qle_to_QleT' 桥归 Qle 层再 Qle_trans（原式 Qle_trans 直施 QleT' 目标不统一；对齐主件 A 结构） *)
  apply Qle_to_QleT'.
  apply (Qle_trans 0 (1 - x) (exp_partial n (Qopp x))).
  - (* AA21 修⑨：0 ≤ 1−x 的 Q 原生构造（lia 拒 Q；原 qeq_le+rewrite at 1 落点为 Qeq 展开形病） *)
    assert (H1le : Qle x 1) by (apply QleT'_to_Qle; exact H1).
    apply (Qle_trans 0 (1 + Qopp 1) (1 - x)).
    + apply (qeq_le 0 (1 + Qopp 1)). ring.
    + apply (Qle_trans (1 + Qopp 1) (1 + Qopp x) (1 - x)).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qopp_le_compat x 1 H1le).
      * apply (qeq_le (1 + Qopp x) (1 - x)). ring.
  - apply enp_ge_all.
    + apply QleT'_to_Qle. exact H0.
    + apply QleT'_to_Qle. exact H1.
Qed.

(* 主件 C（严格正面）：0 ≤ x < 1 ⟹ ∀n, 0 < exp_partial n (−x) *)
Theorem enp_exp_partial_pos : forall (x : Q) (n : nat),
  QleT' 0 x -> QltT x 1 ->
  QltT 0 (exp_partial n (Qopp x)).
Proof.
  intros x n H0 Hx1.
  assert (Hx1p : Qlt x 1) by (apply QltT_to_Qlt; exact Hx1).
  assert (H1 : QleT' x 1) by (apply qltT_leT'; exact Hx1).
  assert (Hge := enp_exp_partial_ge x n H0 H1).
  assert (Hlow : Qle (1 - x) (exp_partial n (Qopp x)))
    by (apply QleT'_to_Qle; exact Hge).
  (* AA21 修⑩：lia 拒 Q（WangWW 卡同款）；0 < 1−x 的 Q 原生构造：x<1 ⟹ −1<−x ⟹ 1+(−1)<1+(−x) ⟹ Qeq 桥归 *)
  assert (Hlt0 : Qlt 0 (1 - x)).
  { assert (Ho : Qlt (Qopp 1) (Qopp x)) by (apply Qopp_lt_compat; exact Hx1p).
    apply (Qle_lt_trans 0 (1 + Qopp 1) (1 - x)).
    - apply (qeq_le 0 (1 + Qopp 1)). ring.
    - apply (proj2 (Qplus_lt_r (Qopp 1) (Qopp x) 1)). exact Ho. }
  (* AA21 修⑪：Qlt_le_trans 产出 Prop 层 Qlt，出口 QltT 需 S02 Qlt_to_QltT 桥归 Set 层 *)
  exact (Qlt_to_QltT 0 (exp_partial n (Qopp x))
    (Qlt_le_trans 0 (1 - x) (exp_partial n (Qopp x)) Hlt0 Hlow)).
Qed.

(* ============================================================ *)
(* 件 4：数值例（vm_compute 端到端自检）                               *)
(* ============================================================ *)

(* S_4(−1) = 1 − 1 + 1/2 − 1/6 + 1/24 = 3/8（x=1 非负档实例） *)
Lemma enp_eval_example1 : exp_partial 4 (Qopp 1%Q) == 3 # 8.
Proof. vm_compute. reflexivity. Qed.

(* S_3(−1/2) = 1 − 1/2 + 1/8 − 1/48 = 29/48（x<1 严格档实例；AA21 修⑫：原 37/48 系算术误——
   48−24+6−1=29，假等式 vm_compute 判拒不可闭合，改真值并留痕） *)
Lemma enp_eval_example2 : exp_partial 3 (Qopp (1 # 2)) == 29 # 48.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions enp_exp_partial_ge.
Print Assumptions enp_exp_partial_nonneg.
Print Assumptions enp_exp_partial_pos.
