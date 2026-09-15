(* ============================================================
   DTPT_ME2.v — MultiEntropyEval 相干性二波：从「数据束」升级为
   「自证证书」（热点升级单 X2-6，扫描席 DTPT-U16）
   原典映射：附录三「多熵评估套件」+ DTPT_Entropy.v L46-58 定义面
   ------------------------------------------------------------
   底座（只 Require DTPT / DTPT_Entropy / stdlib，零新前提）：
   - DTPT_Entropy.v：mkMEval/mkMEval_eta（S2 已证五投影，复用禁重证）、
     H_shannon_q_nonneg、xq_H_adj_nonneg、H_shannon_q_count_ub、
     H_adj_P0_min、H_cond_nonneg_guarded、mkMEval_Hms1_Hsh0、
     xq_Zlen_nonneg、xq_Qle_bool_le、qadd_nonneg
   - DTPT.v：H_ms、gate_pass、Qle_dec'、abs_eq、abs_neg、
     Qle_0_sub'、qmul_le_r、qadd_le、qsub 工具
   - stdlib：Qle_trans、Qle_refl、ring/lia
   ------------------------------------------------------------
   分层交付：
   - 保底（一档）：五字段逐一定义方程（组合复用 mkMEval_eta，零重证）
   - 旗舰（二档）：me_cert —— 载体一致 + 四熵等值 + Hadj/Hsh 非负 +
     Hsh 计数上界 + Hcond 三角界，九联合相干合取面
     （me_coherent 证书谓词 + mkMEval 构造见证）
   - 主件（三档）：X2-6 六件套件级 lifts + H_ms1→Hsh0 逆否桥 +
     |me_Hcond| 三角界/计数面证书版 + gate 双门桥
     （H_cond_abs_bound 在 ZeroLocus 盘面，按红线禁 Require，不消费）
   - 加分（四档）：me_total 等权聚合 + 守卫非负界 + 2 倍香农上界
   红线自查：承认件/中断件/经典排中面等禁词全零（字面自查见
   升级报告 G1 行），全程 Qed 收口；nat 全显式 %nat。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
Import ListNotations.
Open Scope Q_scope.
Require DTPT DTPT_Entropy.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_ME2.

(* ============================================================
   第 0 节 局部工具（abs 三角 / 聚合权 / dedup 计数）
   ============================================================ *)

(* 非负二元差 abs 三角：0 <= a、0 <= b -> |a - b| <= a + b
   （Qle_dec' 两分定形 + abs_eq/abs_neg，正负两支各经 Qle_0_sub' 移项） *)
Lemma me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> (Qabs (a - b) <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* 支一 a <= b：|a-b| = -(a-b) = b-a，经 (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply (proj2 (Qle_0_sub' (a - b) 0)).
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. apply (proj1 (Qle_0_sub' a b)). exact Hab. }
    rewrite (abs_neg (a - b) Hneg).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply (proj2 (Qle_0_sub' (b - a) (a + b))).
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply qadd_nonneg; exact Ha.
  - (* 支二 b <= a：|a-b| = a-b，经 (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply (proj1 (Qle_0_sub' b a)). exact Hba. }
    rewrite (abs_eq (a - b) Hpos).
    apply (proj2 (Qle_0_sub' (a - b) (a + b))).
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply qadd_nonneg; exact Hb.
Qed.

(* 聚合权 1/4 非负（字面 Qle_bool 计算） *)
Lemma me2_weight_nonneg : (0 <= (1 # 4)%Q)%Q.
Proof. apply xq_Qle_bool_le. reflexivity. Qed.

(* 非空表的 dedup 计数 >= 1（nat 全显式） *)
Lemma me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> (1 <= length (dedup l))%nat.
Proof.
  intros [| x xs] H.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. lia.
Qed.

(* ============================================================
   第一节 保底件：五字段逐一定义方程（复用 S2 mkMEval_eta，禁重证）
   ============================================================ *)

Theorem me2_carrier_eq : forall (l ctx : list Q),
  me_carrier (mkMEval l ctx) = l.
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc _]. exact Hc.
Qed.

Theorem me2_Hadj_eq : forall (l ctx : list Q),
  me_Hadj (mkMEval l ctx) == H_adj l.
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [Ha _]]. exact Ha.
Qed.

Theorem me2_Hms_eq : forall (l ctx : list Q),
  me_Hms (mkMEval l ctx) == H_ms l.
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [Hm _]]]. exact Hm.
Qed.

Theorem me2_Hsh_eq : forall (l ctx : list Q),
  me_Hsh (mkMEval l ctx) == H_devsum l.
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [Hs _]]]]. exact Hs.
Qed.

Theorem me2_Hcond_eq : forall (l ctx : list Q),
  me_Hcond (mkMEval l ctx) == H_cond l ctx.
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [_ Hc]]]]. exact Hc.
Qed.

(* ============================================================
   第二节 旗舰：me_cert —— mkMEval 自证证书（九联合相干合取面）
   载体一致 + 四熵等值 + Hadj/Hsh 非负 + Hsh 计数上界 + Hcond 三角界
   ============================================================ *)

Definition me_coherent (m : MultiEntropyEval) (l ctx : list Q) : Prop :=
  me_carrier m = l
  /\ me_Hadj m == H_adj l
  /\ me_Hms m == H_ms l
  /\ me_Hsh m == H_devsum l
  /\ me_Hcond m == H_cond l ctx
  /\ (0 <= me_Hadj m)%Q
  /\ (0 <= me_Hsh m)%Q
  /\ (me_Hsh m <= me_Hadj m * (Z.of_nat (length (me_carrier m)) # 1))%Q
  /\ (Qabs (me_Hcond m) <= me_Hsh m + H_devsum ctx)%Q.

Theorem me_cert : forall (l ctx : list Q),
  me_coherent (mkMEval l ctx) l ctx.
Proof.
  intros l ctx.
  destruct (mkMEval_eta l ctx) as [Hc [Ha [Hm [Hs Hcond]]]].
  (* repeat split 直收前五个定义性合取面（载体 eq + 四 Qeq，
     Z.eq 为 Prop 级单构造子，投影 delta 归约后 eq_refl 可解），
     余下四个 Qle 相干面逐条复用底座件 *)
  unfold me_coherent. repeat split.
  - rewrite Ha. apply xq_H_adj_nonneg.
  - rewrite Hs. apply H_shannon_q_nonneg.
  - rewrite Hs, Ha, Hc. apply H_shannon_q_count_ub.
  - rewrite Hcond, Hs. unfold H_cond.
    apply me2_abs_sub_triangle; apply H_shannon_q_nonneg.
Qed.

(* ============================================================
   第三节 主件：X2-6 套件级 lifts + 跨字段桥（证书版）
   ============================================================ *)

(* 3.1 P0 最小性提升：H_adj (P0 载体) <= me_Hadj *)
Theorem mkMEval_Hadj_min : forall (l ctx : list Q),
  (H_adj (P0 (me_carrier (mkMEval l ctx))) <= me_Hadj (mkMEval l ctx))%Q.
Proof.
  intros l ctx. rewrite me2_carrier_eq, me2_Hadj_eq. apply H_adj_P0_min.
Qed.

(* 3.2 香农字段非负 *)
Theorem mkMEval_Hsh_nonneg : forall (l ctx : list Q),
  (0 <= me_Hsh (mkMEval l ctx))%Q.
Proof.
  intros l ctx. rewrite me2_Hsh_eq. apply H_shannon_q_nonneg.
Qed.

(* 3.3 香农字段计数上界（H_adj × 长度系数） *)
Theorem mkMEval_Hsh_ub : forall (l ctx : list Q),
  (me_Hsh (mkMEval l ctx)
    <= me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1))%Q.
Proof.
  intros l ctx. rewrite me2_Hsh_eq, me2_Hadj_eq.
  apply H_shannon_q_count_ub.
Qed.

(* 3.4 多重集熵非空下界：载体非空 -> 1 <= me_Hms（Z 桥） *)
Theorem mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> (1 <= me_Hms (mkMEval l ctx))%Q.
Proof.
  intros l ctx Hl. rewrite me2_Hms_eq. unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.  (* 记录字段真名小写 Qden（S2 卡坑四） *)
Qed.

(* 3.5 条件熵负侧界：-H_sh ctx <= me_Hcond（H_shannon_q_nonneg 移项） *)
Theorem mkMEval_Hcond_lb : forall (l ctx : list Q),
  (- H_devsum ctx <= me_Hcond (mkMEval l ctx))%Q.
Proof.
  intros l ctx. rewrite me2_Hcond_eq. unfold H_cond.
  apply (proj2 (Qle_0_sub' (- H_devsum ctx)
                           (H_devsum l - H_devsum ctx))).
  assert (Hr : (H_devsum l - H_devsum ctx) - (- H_devsum ctx)
               == H_devsum l) by ring.
  rewrite Hr. apply H_shannon_q_nonneg.
Qed.

(* 3.6 双门同一 Qle_bool：低熵门 == gate_pass（跨定义面） *)
Theorem mkMEval_gate_bridge : forall (l ctx : list Q) (t : Q),
  gate_low_entropy (me_Hsh (mkMEval l ctx)) t
  = gate_pass t (H_devsum l).
Proof.
  intros l ctx t. unfold gate_low_entropy, gate_pass, mkMEval.
  cbn [me_Hsh]. destruct (Qle_bool (H_devsum l) t); reflexivity.
Qed.

(* 3.7 跨字段桥证书版：H_ms==1 -> Hsh==0 的逆否面
   （复用 S2 mkMEval_Hms1_Hsh0，零重证） *)
Theorem mkMEval_notHsh0_notHms1 : forall (l ctx : list Q),
  ~ (me_Hsh (mkMEval l ctx) == 0)%Q -> ~ (me_Hms (mkMEval l ctx) == 1)%Q.
Proof.
  intros l ctx H0 Hms1. apply H0. apply (mkMEval_Hms1_Hsh0 l ctx). exact Hms1.
Qed.

(* 3.8 三角界证书版：|me_Hcond| <= me_Hsh + H_sh ctx（Entropy 内件组合；
   H_cond_abs_bound 在 ZeroLocus 盘面按红线禁 Require，不消费） *)
Theorem mkMEval_Hcond_abs_ub : forall (l ctx : list Q),
  (Qabs (me_Hcond (mkMEval l ctx))
    <= me_Hsh (mkMEval l ctx) + H_devsum ctx)%Q.
Proof.
  intros l ctx. rewrite me2_Hcond_eq, me2_Hsh_eq. unfold H_cond.
  apply me2_abs_sub_triangle; apply H_shannon_q_nonneg.
Qed.

(* 3.9 计数面证书版：|me_Hcond| <= me_Hadj×n_l + H_adj ctx×n_ctx
   （3.8 三角界 × H_shannon_q_count_ub 双臂） *)
Theorem mkMEval_Hcond_count_ub : forall (l ctx : list Q),
  (Qabs (me_Hcond (mkMEval l ctx))
    <= me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)
       + H_adj ctx * (Z.of_nat (length ctx) # 1))%Q.
Proof.
  intros l ctx. rewrite me2_Hcond_eq, me2_Hadj_eq. unfold H_cond.
  apply (Qle_trans _ (H_devsum l + H_devsum ctx)%Q).
  - apply me2_abs_sub_triangle; apply H_shannon_q_nonneg.
  - apply qadd_le.
    + apply H_shannon_q_count_ub.
    + apply H_shannon_q_count_ub.
Qed.

(* ============================================================
   第四节 加分：聚合面 me_total（等权 1/4）+ 守卫非负界 + 2 倍上界
   ============================================================ *)

Definition me_total (m : MultiEntropyEval) : Q :=
  (1 # 4)%Q * (me_Hadj m + me_Hms m + me_Hsh m + me_Hcond m)%Q.

(* 聚合定义方程（mkMEval 上投影定义性） *)
Theorem me_total_eq : forall (l ctx : list Q),
  me_total (mkMEval l ctx)
  == (1 # 4)%Q * (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q.
Proof. intros l ctx. reflexivity. Qed.

(* 守卫非负界：H_sh ctx <= H_sh l -> 0 <= me_total
   （四熵在守卫下全非负，qadd_nonneg 链 + qmul_le_r） *)
Theorem me_total_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q ->
  (0 <= me_total (mkMEval l ctx))%Q.
Proof.
  intros l ctx Hle. rewrite me_total_eq.
  assert (Hc : (0 <= H_cond l ctx)%Q)
    by (apply H_cond_nonneg_guarded; exact Hle).
  assert (Hms : (0 <= H_ms l)%Q) by (unfold H_ms; apply xq_Zlen_nonneg).
  assert (Hsum : (0 <= H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
  { apply qadd_nonneg.
    - apply qadd_nonneg.
      + apply qadd_nonneg; [apply xq_H_adj_nonneg | exact Hms].
      + apply H_shannon_q_nonneg.
    - exact Hc. }
  apply xq_mul_nonneg.
  - apply me2_weight_nonneg.
  - exact Hsum.
Qed.

(* 聚合上界：me_total <= (1/4)×(H_adj + H_ms + 2×H_sh)
   （负侧恰由 H_cond <= H_sh l 吃掉：-H_sh ctx <= 0） *)
Theorem me_total_ub : forall (l ctx : list Q),
  (me_total (mkMEval l ctx)
    <= (1 # 4)%Q * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q)%Q.
Proof.
  intros l ctx. rewrite me_total_eq.
  assert (Hcc : (H_cond l ctx <= H_devsum l)%Q).
  { unfold H_cond. apply (proj2 (Qle_0_sub' _ _)).
    assert (Hr : H_devsum l - (H_devsum l - H_devsum ctx)
                 == H_devsum ctx) by ring.
    rewrite Hr. apply H_shannon_q_nonneg. }
  assert (Hsub : (H_devsum l + H_cond l ctx
                  <= (2 # 1)%Q * H_devsum l)%Q).
  { assert (Hr2 : (2 # 1)%Q * H_devsum l
                  == H_devsum l + H_devsum l) by ring.
    rewrite Hr2. apply qadd_le.
    - apply Qle_refl.
    - exact Hcc. }
  assert (Hassoc : (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q
                   == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q)
    by ring.
  rewrite Hassoc.
  assert (Hinner : (H_adj l + H_ms l + (H_devsum l + H_cond l ctx)
                    <= H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
  { apply qadd_le.
    - apply Qle_refl.
    - exact Hsub. }
  (* qmul_le_r 为右乘子形且要求同乘子：两侧权重各 ring 换序到右 *)
  assert (Hsw1 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
               == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
                    * (1 # 4)%Q) by ring.
  assert (Hsw2 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
               == (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
                    * (1 # 4)%Q) by ring.
  rewrite Hsw1, Hsw2. apply qmul_le_r.
  - exact Hinner.
  - apply me2_weight_nonneg.
Qed.

End DTPT_ME2.
Import DTPT_ME2.

(* ============================================================
   终验：旗舰零前提面（Closed = 零承认假设实证）
   ============================================================ *)

Print Assumptions me_cert.
Print Assumptions mkMEval_gate_bridge.
Print Assumptions mkMEval_Hcond_count_ub.
Print Assumptions me_total_ub.
