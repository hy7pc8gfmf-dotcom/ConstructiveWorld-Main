(* ============================================================ *)
(* ToyR 玩具证替换件 —— T268 台账席 战役包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bxcb_term_split（原 L129，2 句强证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBanachBinomBridge.v —— 席CBR：二项式系数桥（20260913）     *)
(* ============================================================ *)
(* 使命（BA 报告挂账③原文）：「系数桥：bpa_binom（Pascal 递归形）  *)
(*   ↔ q_choose（阶乘比形）等价件，供下游 #29 exp_term_split       *)
(*   （C(k,j)/k! = 1/(j!(k−j)!)）。」                             *)
(*                                                               *)
(* 普查账（两侧实形，20260913 实测）：                             *)
(*   左：UpReqBanachAdd L53 bpa_binom——对 n Pascal 递归 Fixpoint，  *)
(*       S-形匹配免 Nat.sub 截断；k>n 出界恒为零（bpa_binom_out）。 *)
(*   右：S07 L943 q_choose n k := q_fact n / (q_fact k * q_fact    *)
(*       (n−k))——纯阶乘比 Definition，无 k≤n 守卫；k>n 时 Nat.sub  *)
(*       截断使 q_choose n k == n!/k! ≠ 0（见 bxcb_q_choose_out）。 *)
(*                                                               *)
(* 【出界语义对齐，本桥第一坑】两侧仅在 0 ≤ k ≤ n 同义：无假设计   *)
(*   面命题 forall n k, bpa_binom n k == q_choose n k 可反驳       *)
(*   （反例 n=1,k=2：bpa 侧 0，q_choose 侧 1!/2!=1/2）。故主桥限定  *)
(*   (k <= n)%nat——这是两侧定义形决定的语义对齐，非缩水；出界面    *)
(*   另立 bxcb_q_choose_out（截断形显式）与 bpa_binom_out（零形）   *)
(*   配对成账，全值域两半皆有正式件。                              *)
(*                                                               *)
(* 复用账（不重写，普查实测）：Pascal 恒等式 q_choose_succ、边界    *)
(*   q_choose_0/q_choose_n、阶乘比分裂 q_choose_div_fact 全部取自   *)
(*   冻结 S07 ExpPlusStage2（B2Tv2 卡点名 L940-1600）；bpr2_q_choose *)
(*   （UpReqBanachProd2）与 q_choose 定义同构（delta 级），薄桥     *)
(*   bxcb_binom_eq_bpr2 接线分工。本文件零新算术引擎，纯桥接组装。  *)
(*                                                               *)
(* 红线自审：语句面全 Qeq（S07 同款面），nat 前提 (<=)%nat；证内    *)
(*   无经典逻辑（Nat.eq_dec 是 Set 层 sumbool）；无承认件。         *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpReqBanachAdd.
Require Import UpReqBanachProd2.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1：出界语义对齐件——q_choose 的 Nat.sub 截断形显式化            *)
(*                                                               *)
(* k>n 时 (n−k) 截断为 0，分母 q_fact 0 = 1，故 q_choose n k        *)
(*   == q_fact n / q_fact k == q_fact n * Qinv (q_fact k) ≠ 0，    *)
(* 与 bpa_binom_out（== 0）形成两侧出界语义分账。                  *)
(* ============================================================ *)

Lemma bxcb_q_choose_out : forall n k : nat, (n < k)%nat ->
  q_choose n k == q_fact n * Qinv (q_fact k).
Proof.
  intros n k H.
  unfold q_choose.
  assert (E : (n - k)%nat = 0%nat) by lia.
  rewrite E.
  change (q_fact 0%nat) with (1%Q).
  unfold Qdiv.
  setoid_rewrite (Qmult_1_r (q_fact k)).
  reflexivity.
Qed.

(* ============================================================ *)
(* S2：主桥 bxcb_binom_eq_choose（对 n 归纳 + k 分段）             *)
(*                                                               *)
(*   forall n k, (k <= n)%nat -> bpa_binom n k == q_choose n k    *)
(* 分段：k=0（bpa_binom_0 ↔ q_choose_0）；k=S n' 对角              *)
(*   （bpa_binom_diag ↔ q_choose_n）；S k' < S n' 递归步——左 Pascal *)
(*   是 bpa_binom 定义形（change/reflexivity 级，BA 手法），右      *)
(*   Pascal 取 S07 q_choose_succ（复用不重写），末尾 (S k'−1)≡k'    *)
(*   为 iota 转换取 Qeq_refl。                                    *)
(* ============================================================ *)

Lemma bxcb_binom_eq_choose : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == q_choose n k.
Proof.
  intros n. induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ apply Qeq_refl | lia ].
  - destruct k as [| k'].
    + rewrite bpa_binom_0.
      apply Qeq_sym. apply q_choose_0.
    + destruct (Nat.eq_dec k' n') as [Heq | Hne].
      * rewrite Heq.
        setoid_rewrite (bpa_binom_diag (Datatypes.S n')).
        apply Qeq_sym. apply q_choose_n.
      * change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
          with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
        setoid_rewrite (IH k' ltac:(lia)).
        setoid_rewrite (IH (Datatypes.S k') ltac:(lia)).
        setoid_rewrite (q_choose_succ n' (Datatypes.S k') ltac:(lia) ltac:(lia)).
        (* 项序与 sub 双坑：q_choose_succ 尾项是 (S k'−1)（变量 k' 下
           Nat.sub 不约化，S-形免截断手法的对照坑），lia 桥 nat 层等式
           换回 k'；bpa 定义形 k' 项在前，Qplus 非定义性交换再换位——
           两步后两侧同形，Qeq_refl 收口 *)
        assert (Esub : (Datatypes.S k' - 1)%nat = k'%nat) by lia.
        rewrite Esub.
        setoid_rewrite (Qplus_comm (q_choose n' k') (q_choose n' (Datatypes.S k'))).
        apply Qeq_refl.
Qed.

(* ============================================================ *)
(* S3：哨兵数值面（reflexivity/vm_compute 级烟测）                 *)
(* ============================================================ *)

Lemma bxcb_sentinel_bpa_4_2 : bpa_binom 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_qchoose_4_2 : q_choose 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 桥上对账：主桥在 (4,2) 的直接实例 ==6 两侧一致 *)
Lemma bxcb_sentinel_bridge_4_2 : bpa_binom 4%nat 2%nat == q_choose 4%nat 2%nat.
Proof. apply bxcb_binom_eq_choose. lia. Qed.

(* 出界哨兵对（反例实形入账）：n=1,k=2 两侧分歧——bpa 侧 0，        *)
(* q_choose 侧 1!/2! = 1/2（Qinv (2#1)）；两件合账即证无假设全值域    *)
(* 桥不可立，语义对齐 (k<=n) 面为必需。                            *)
Lemma bxcb_sentinel_out_bpa_1_2 : bpa_binom 1%nat 2%nat == 0%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_out_qchoose_1_2 : q_choose 1%nat 2%nat == Qinv (2 # 1).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* S4：主件 bxcb_term_split——C(k,j)/k! == 1/(j!·(k−j)!)            *)
(*                                                               *)
(* 下游 #29 exp_term_split 消费形。S07 已有同型原件                 *)
(*   q_choose_div_fact（B2Tv2 卡点名），复用不重写；另附 BA 侧      *)
(*   （bpa 系数）消费形 bxcb_term_split_binom。                    *)
(* ============================================================ *)

Lemma bxcb_term_split : forall k j : nat,
  q_choose k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j.
  apply (q_choose_div_fact k j).
Qed.

Lemma bxcb_term_split_binom : forall k j : nat, (j <= k)%nat ->
  bpa_binom k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j Hj.
  setoid_rewrite (bxcb_binom_eq_choose k j Hj).
  apply (q_choose_div_fact k j).
Qed.

(* ============================================================ *)
(* S5：薄桥——bpr2_q_choose（Prod2 阶乘比双层移植形）接线           *)
(*                                                               *)
(* bpr2_q_choose n k := q_fact n / (q_fact k * q_fact (Nat.sub n k)) *)
(* 与 q_choose n k 定义同构（delta 级），change 换形后主桥直用。    *)
(* 分工：S07 q_choose=冻结原件；bpr2_=Prod2 移植形；bpa_binom=      *)
(* Add Pascal 形。本桥把三形收拢到同一等价面。                     *)
(* ============================================================ *)

Lemma bxcb_binom_eq_bpr2 : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == bpr2_q_choose n k.
Proof.
  intros n k H.
  change (bpr2_q_choose n k) with (q_choose n k).
  apply bxcb_binom_eq_choose. exact H.
Qed.

(* ============================================================ *)
(* G3 探针记录（验后删，20260913）：四件 Print Assumptions 全部      *)
(*   「Closed under the global context」；Separate Extraction       *)
(*   UpReqBanachBinomBridge.ml Obj.magic 计数 =0；coqchk -o 全件     *)
(*   公理面 none。探针已删，终版无提取输出。                         *)
(* ============================================================ *)

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bxcb_term_split.
