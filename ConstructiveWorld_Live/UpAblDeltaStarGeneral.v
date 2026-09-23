(* ============================================================
   使命行：Doeblin 常数 δ* = lo² 次优性从 2 态核到一般 nR≥2 态行随机
   核的构造性推广——显式 nR 态核族 dsgen_k（2 态 softmax 块的凸组合
   嵌入：K := (1−β)·块 + β·均匀，β := (1+lo²)/2），对一切 nR≥2 证：
   行随机性、δ* = lo² 是可行 Doeblin 常数、β 也是可行常数且
   lo² < β = (1+lo²)/2（QltT Set 层见证）；nR≥3 时进一步证 β 是最优
   常数（可行 + 极大，极大性由泄漏列条目 β/nR 的可达性经 Qmult_le_r
   消去回推）。显式间隙 dsgen_gap = (1−lo²)/2 > 0，且 ≥ 2 态核间隙
   mdsopt_gap = lo²(1−lo²)/(1+lo²)（常数倍 (1+lo²)/(2lo²) ≥ 1，
   dsgen_gap_ratio/dsgen_gap_ratio_ge1 给出闭式）。
   依赖：Stdlib QArith/Lia/List；S02_CauchyComplete（QltT 见证形
   Qlt_to_QltT）；UpAblDeltaStarSuboptimal（2 态核块 mdsopt_k* 与
   归一化 mdsopt_row*_norm、间隙闭式 mdsopt_gap，按任务书零改消费）。
   对标：论文7 §6.1 δ* 设计理由段（lo/hi = lo² 为比值界产物，非
   min，故一般 nR 下仍次优）；§10.2 开放工作第 4 项。
   数学内核：nR 态 s,j ∈ {0,…,nR−1}；参考分布均匀 U=1/nR，Doeblin
   条件 d·(1/nR) ≤ K(s,j)。核矩阵：
     行 0/1、列 0/1：(1−β)·mdsopt 块 + β/nR（凸组合，行和保持 1）
     行 0/1、列 ≥2：β/nR（泄漏列，核最小元所在）
     行 ≥2：1/nR（均匀行）
   核最小元 = β/nR（nR≥3 时由列 ≥2 取到），最优常数 = nR·(β/nR) = β；
   β > lo² ⟺ lo² < 1。nR=2 时无泄漏列，最优常数 ≥ β 仍 > lo²，
   2 态最优闭式 2lo²/(1+lo²) 见 UpAblDeltaStarSuboptimal（mdsopt_main）。
   构造性注记：语句层 Set 值见证形 QltT；无承认项、无经典逻辑；
   定义位全部纯 Q/nat 算术 Defined，透明可提取。Q 序链全部走
   Qlt_trans/Qplus_lt_r/Qmult_le_r/unfold+lia，零 Psatz（按卡
   E-STAGING-WangWW：Psatz 是 micromega 闭包经典公理隐性载体）。
   编译配方：cd attn/_dsnr_sbx 后按 E-STAGING-Q1015 卡②设
   COQLIB/ROCQLIB 至 9.1 库根，再 coqc -q -Q . "" UpAblDeltaStarGeneral.v。
   ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import UpAblDeltaStarSuboptimal.
Import ListNotations.

(* ========== §1 Q 算术基件（正性、非零、除法、加法单调） ========== *)

Lemma dsgen_2pos : (0 < 2)%Q.
Proof. unfold Qlt, Qnum, Qden; cbn; lia. Qed.

Lemma dsgen_ne_of_pos : forall d : Q, (0 < d)%Q -> ~ ((d) == 0)%Q.
Proof.
  intros d Hp Hz. rewrite Hz in Hp. exact (Qlt_irrefl 0 Hp).
Qed.

(* 除法回推（Qmult_lt_r iff 形，proj1 方向）：正分母下 0 < a/d
   归结为 0 < a（两端同乘 d，(a/d)*d == a 由 field 消去）。 *)
Lemma dsgen_div_cancel : forall a d : Q, ~ ((d) == 0)%Q -> ((a/d)*d == a)%Q.
Proof. intros a d Hd. field. exact Hd. Qed.

Lemma dsgen_div_pos : forall a d : Q, (0 < a)%Q -> (0 < d)%Q -> (0 < a/d)%Q.
Proof.
  intros a d Ha Hd.
  apply (proj1 (Qmult_lt_r 0 (a/d) d Hd)).
  rewrite Qmult_0_l.
  rewrite (dsgen_div_cancel a d (dsgen_ne_of_pos d Hd)). exact Ha.
Qed.

(* a/d == a·(1/d)：把除法化成乘法以便 Qmult_le_r/Qmult_lt_r 消去。 *)
Lemma dsgen_div_inv : forall a d : Q, ~ ((d) == 0)%Q -> ((a/d) == a*(1/d))%Q.
Proof. intros a d Hd. field. exact Hd. Qed.

(* 正×正=正（Qmult_lt_compat_r：0<z 在前，0*b 项 Qmult_0_l 清除）。 *)
Lemma dsgen_mul_pos : forall a b : Q, (0 < a)%Q -> (0 < b)%Q -> (0 < a*b)%Q.
Proof.
  intros a b Ha Hb.
  pose proof (Qmult_lt_compat_r 0 a b Hb Ha) as H.
  rewrite Qmult_0_l in H. exact H.
Qed.

(* 加正项保持 ≤：z ≤ z+w（Qplus_le_r iff 形 proj2 + Qplus_0_r）。 *)
Lemma dsgen_le_add_pos : forall z w : Q, (0 < w)%Q -> (z <= z + w)%Q.
Proof.
  intros z w Hw.
  pose proof (proj2 (Qplus_le_r 0 w z) (Qlt_le_weak 0 w Hw)) as H.
  rewrite Qplus_0_r in H. exact H.
Qed.

(* 对称形：w ≤ z+w（前提关于加项 z）。 *)
Lemma dsgen_le_add_pos2 : forall z w : Q, (0 < z)%Q -> (w <= z + w)%Q.
Proof.
  intros z w Hz. rewrite (Qplus_comm z w). apply dsgen_le_add_pos. exact Hz.
Qed.

(* x·2 == x+x：纯 Q 环恒等式，field 直闭。 *)
Lemma dsgen_two_mul_r : forall x : Q, ((x)*2 == x + x)%Q.
Proof. intros x. field. Qed.

(* ========== §2 状态数 nR 的 Q 承载 ========== *)

Definition dsgen_qN (nR : nat) : Q := (Z.of_nat nR)#1.

Lemma dsgen_qN_pos : forall nR : nat, (1 <= nR)%nat -> (0 < dsgen_qN nR)%Q.
Proof.
  intros [|n] Hn; [ inversion Hn
  | unfold dsgen_qN, Qlt, Qnum, Qden; cbn; lia ].
Qed.

(* qN(S n) == qN n + 1：Z.of_nat S 归约后 Qnum 面展开 lia（Z.eqb 目标）。 *)
Lemma dsgen_qN_S : forall n : nat, dsgen_qN (S n) == dsgen_qN n + 1.
Proof.
  intros n. unfold dsgen_qN.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  unfold Qeq, Qplus, Qnum, Qden. cbn. lia.
Qed.

(* ========== §3 β := (1+lo²)/2 的算术面 ========== *)

Definition dsgen_beta (lo : Q) : Q := (1 + lo*lo)/2.

Lemma dsgen_beta_pos : forall lo : Q, (0 < lo)%Q -> (0 < dsgen_beta lo)%Q.
Proof.
  intros lo H0. unfold dsgen_beta.
  apply dsgen_div_pos.
  - apply mdsopt_den_pos. exact H0.
  - exact dsgen_2pos.
Qed.

(* 0 < 1 − lo²：Qopp_lt_compat 移项 + Qplus_lt_r（iff 形）加合并。 *)
Lemma dsgen_1mlo2_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < 1 - lo*lo)%Q.
Proof.
  intros lo H0 H1.
  pose proof (Qopp_lt_compat (lo*lo) 1 (mdsopt_lt1 lo H0 H1)) as Ho.
  pose proof (proj2 (Qplus_lt_r (-1) (-(lo*lo)) 1) Ho) as Hm.
  rewrite Qplus_opp_r in Hm. exact Hm.
Qed.

(* 0 < 1−β：(1+lo²)/2 化 (1−lo²)/2 后除法正性。 *)
Lemma dsgen_omb_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < 1 - dsgen_beta lo)%Q.
Proof.
  intros lo H0 H1.
  assert (Hb : (1 - dsgen_beta lo == (1 - lo*lo)/2)%Q)
    by (unfold dsgen_beta; field; apply dsgen_ne_of_pos; exact dsgen_2pos).
  rewrite Hb. apply dsgen_div_pos.
  - apply dsgen_1mlo2_pos; assumption.
  - exact dsgen_2pos.
Qed.

Lemma dsgen_beta_le_1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (dsgen_beta lo <= 1)%Q.
Proof.
  intros lo H0 H1.
  assert (Hcore : (1 + lo*lo <= 2)%Q).
  { pose proof (proj2 (Qplus_lt_r (lo*lo) 1 1) (mdsopt_lt1 lo H0 H1)) as H.
    assert (Heq : (1+1 == 2)%Q) by reflexivity.
    rewrite Heq in H. exact (Qlt_le_weak _ _ H). }
  unfold dsgen_beta.
  (* 两端乘 2（Qmult_le_r iff 形 proj1 回推），左端分母 field 消去。 *)
  apply (proj1 (Qmult_le_r ((1 + lo*lo)/2) 1 2 dsgen_2pos)).
  rewrite (dsgen_div_cancel (1 + lo*lo) 2 (dsgen_ne_of_pos 2 dsgen_2pos)).
  rewrite Qmult_1_l. exact Hcore.
Qed.

(* lo² < β ⟺ 2lo² < 1+lo² ⟺ lo² < 1：Qmult_lt_r 乘 2 回推。 *)
Lemma dsgen_dstar_lt_beta : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (lo*lo < dsgen_beta lo)%Q.
Proof.
  intros lo H0 H1. unfold dsgen_beta.
  apply (proj1 (Qmult_lt_r (lo*lo) ((1 + lo*lo)/2) 2 dsgen_2pos)).
  rewrite (dsgen_div_cancel (1 + lo*lo) 2 (dsgen_ne_of_pos 2 dsgen_2pos)).
  rewrite dsgen_two_mul_r, (Qplus_comm 1 (lo*lo)).
  apply (proj2 (Qplus_lt_r (lo*lo) 1 (lo*lo))). apply mdsopt_lt1; assumption.
Qed.

Lemma dsgen_dstar_le_beta : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (lo*lo <= dsgen_beta lo)%Q.
Proof. intros lo H0 H1. apply Qlt_le_weak. apply dsgen_dstar_lt_beta; assumption. Qed.

(* ========== §4 2 态块条目正性（消费 UpAblDeltaStarSuboptimal） ========== *)

Lemma dsgen_onelo_pos : forall lo : Q, (0 < lo)%Q -> (0 < 1 + lo)%Q.
Proof.
  intros lo H0.
  pose proof (proj2 (Qplus_lt_r 0 1 lo) mdsopt_01) as Hx.
  rewrite Qplus_0_r in Hx.
  rewrite (Qplus_comm 1 lo).
  exact (Qlt_trans 0 lo (lo + 1) H0 Hx).
Qed.

Lemma dsgen_k00_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k00 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k00. apply dsgen_div_pos;
    [ exact H0 | apply dsgen_onelo_pos; exact H0 ].
Qed.

Lemma dsgen_k01_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k01 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k01. apply dsgen_div_pos;
    [ exact mdsopt_01 | apply dsgen_onelo_pos; exact H0 ].
Qed.

Lemma dsgen_k10_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k10 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k10. apply dsgen_div_pos;
    [ apply mdsopt_sq0; exact H0 | apply mdsopt_den_pos; exact H0 ].
Qed.

Lemma dsgen_k11_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k11 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k11. apply dsgen_div_pos;
    [ exact mdsopt_01 | apply mdsopt_den_pos; exact H0 ].
Qed.

(* ========== §5 nR 态核定义（凸组合嵌入，nR≥2 任意） ========== *)

(* K(s,j) = (1−β)·B(s,j) + β/nR：B 为 2 态块嵌入（行 ≥2 均匀、
   行 0/1 列 ≥2 零块），β/nR 为泄漏质量，行和保持 1。
   （匹配用 Datatypes.O/S 全限定构造子形：QArith 开 Q_scope 后
   数字字面模式会被解读为 Q 构造子，全限定形无歧义。） *)
Definition dsgen_k (nR : nat) (lo : Q) (s j : nat) : Q :=
  match s with
  | Datatypes.O => match j with
                   | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k00 lo
                                    + dsgen_beta lo / dsgen_qN nR
                   | Datatypes.S j' => match j' with
                                       | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k01 lo
                                                        + dsgen_beta lo / dsgen_qN nR
                                       | _ => dsgen_beta lo / dsgen_qN nR
                                       end
                   end
  | Datatypes.S s' => match s' with
                      | Datatypes.O => match j with
                                       | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k10 lo
                                                        + dsgen_beta lo / dsgen_qN nR
                                       | Datatypes.S j'' => match j'' with
                                                            | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k11 lo
                                                                             + dsgen_beta lo / dsgen_qN nR
                                                            | _ => dsgen_beta lo / dsgen_qN nR
                                                            end
                                       end
                      | _ => 1 / dsgen_qN nR
                      end
  end.

Definition dsgen_dsum (f : nat -> Q) (l : list nat) : Q :=
  fold_right Qplus 0 (map f l).

Definition dsgen_rowsum (nR : nat) (lo : Q) (s : nat) : Q :=
  dsgen_dsum (dsgen_k nR lo s) (seq 0 nR).

Definition dsgen_rowstoch (nR : nat) (lo : Q) : Prop :=
  forall s : nat, (s < nR)%nat -> dsgen_rowsum nR lo s == 1.

(* Doeblin 可行性（均匀参考 U=1/nR：d·(1/nR) ≤ K(s,j) 全条目）。 *)
Definition dsgen_feasible (nR : nat) (lo d : Q) : Prop :=
  forall s j : nat, (s < nR)%nat -> (j < nR)%nat ->
    (d * (1 / dsgen_qN nR) <= dsgen_k nR lo s j)%Q.

(* ========== §6 列表求和基件（seq 上 fold） ========== *)

(* Q 列表层 fold 拆拼接（cbn 只点 app/fold_right，防 Qeq 过展）。 *)
Lemma dsgen_fold_app : forall (l1 l2 : list Q),
  fold_right Qplus 0 (l1 ++ l2) == fold_right Qplus 0 l1 + fold_right Qplus 0 l2.
Proof.
  intros l1 l2. induction l1 as [|a l1 IH].
  - cbn [app fold_right]. symmetry. apply Qplus_0_l.
  - cbn [app fold_right]. rewrite IH. apply Qplus_assoc.
Qed.

Lemma dsgen_dsum_app : forall (f : nat -> Q) (l1 l2 : list nat),
  dsgen_dsum f (l1 ++ l2) == dsgen_dsum f l1 + dsgen_dsum f l2.
Proof. intros f l1 l2. unfold dsgen_dsum. rewrite map_app. apply dsgen_fold_app. Qed.

(* 常值段求和：n 项 c 之和 = n·c（seq_S 拆尾 + Z.of_nat S 归纳）。 *)
Lemma dsgen_dsum_const_seq : forall (f : nat -> Q) (c : Q) (n start : nat),
  (forall j : nat, In j (seq start n) -> f j == c) ->
  dsgen_dsum f (seq start n) == dsgen_qN n * c.
Proof.
  intros f c n. induction n as [|n IH]; intros start Hfib.
  - (* 空段和 ≡ 0，qN 0 ≡ 0：Qmult_0_l 整项转换给出 *)
    symmetry. exact (Qmult_0_l c).
  - rewrite seq_S. rewrite dsgen_dsum_app.
    assert (Hs : dsgen_dsum f ((start + n)%nat :: nil) == f (start + n)%nat + 0)
      by reflexivity.
    rewrite Hs, Qplus_0_r.
    rewrite IH by (intros j Hj; apply Hfib; apply in_seq in Hj;
                   apply in_seq; simpl in *; lia).
    rewrite <- (Hfib (start + n)%nat) by (apply in_seq; simpl; lia).
    rewrite dsgen_qN_S, Qmult_plus_distr_l, Qmult_1_l. reflexivity.
Qed.

(* ========== §7 行随机性（全体 nR≥2） ========== *)

(* qN(S(S m)) == qN(m)+2：Qnum 面展开后 lia（Z.eqb 目标）。 *)
Lemma dsgen_qN_split2 : forall m : nat,
  dsgen_qN (S (S m)) == dsgen_qN m + 2.
Proof.
  intros m. rewrite dsgen_qN_S, dsgen_qN_S. field.
Qed.

Lemma dsgen_seq_head2 : forall m : nat, seq 0 (S (S m)) = [0; 1]%nat ++ seq 2 m.
Proof. intros m. reflexivity. Qed.

(* 行 0/1 公共收尾：归组（field 环恒等式）后块和 == 1 消块项，
   泄漏段 qN·(β/qN) 经 Qmult_comm + 除法回推化成 β，剩 (1−β)+β == 1。 *)
Lemma dsgen_rowstoch_head : forall (m : nat) (lo : Q),
  (0 < lo)%Q ->
  (mdsopt_k00 lo + mdsopt_k01 lo == 1)%Q ->
  (mdsopt_k10 lo + mdsopt_k11 lo == 1)%Q ->
  dsgen_rowsum (S (S m)) lo 0 == 1 /\ dsgen_rowsum (S (S m)) lo 1 == 1.
Proof.
  intros m lo H0 Hn0 Hn1.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hq2 : (0 < dsgen_qN m + 2)%Q).
  { unfold dsgen_qN, Qlt, Qnum, Qden. cbn. lia. }
  assert (Hgrp : forall k0 k1 : Q,
    (1 - dsgen_beta lo) * k0 + dsgen_beta lo / dsgen_qN (S (S m))
    + ((1 - dsgen_beta lo) * k1 + dsgen_beta lo / dsgen_qN (S (S m)))
    + dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))
    == (1 - dsgen_beta lo) * (k0 + k1)
       + dsgen_qN (S (S m)) * (dsgen_beta lo / dsgen_qN (S (S m)))).
  { intros k0 k1. rewrite dsgen_qN_split2. field.
    apply dsgen_ne_of_pos. exact Hq2. }
  unfold dsgen_rowsum; split.
  - rewrite dsgen_seq_head2. rewrite dsgen_dsum_app.
    assert (Hhead : dsgen_dsum (dsgen_k (S (S m)) lo 0) [0; 1]%nat
                    == dsgen_k (S (S m)) lo 0 0
                       + (dsgen_k (S (S m)) lo 0 1 + 0)) by reflexivity.
    rewrite Hhead, Qplus_0_r.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo 0) (seq 2 m)
                    == dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo 0)
               (dsgen_beta lo / dsgen_qN (S (S m))) m 2).
      intros j Hj. apply in_seq in Hj.
      destruct j as [|[|j]]; [ lia | lia | ]. reflexivity. }
    rewrite Htail.
    cbn [dsgen_k]. rewrite Hgrp, Hn0, Qmult_1_r.
    rewrite (Qmult_comm (dsgen_qN (S (S m)))
                        (dsgen_beta lo / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    assert (Hfin : ((1 - dsgen_beta lo) + dsgen_beta lo == 1)%Q) by field.
    exact Hfin.
  - rewrite dsgen_seq_head2. rewrite dsgen_dsum_app.
    assert (Hhead : dsgen_dsum (dsgen_k (S (S m)) lo 1) [0; 1]%nat
                    == dsgen_k (S (S m)) lo 1 0
                       + (dsgen_k (S (S m)) lo 1 1 + 0)) by reflexivity.
    rewrite Hhead, Qplus_0_r.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo 1) (seq 2 m)
                    == dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo 1)
               (dsgen_beta lo / dsgen_qN (S (S m))) m 2).
      intros j Hj. apply in_seq in Hj.
      destruct j as [|[|j]]; [ lia | lia | ]. reflexivity. }
    rewrite Htail.
    cbn [dsgen_k]. rewrite Hgrp, Hn1, Qmult_1_r.
    rewrite (Qmult_comm (dsgen_qN (S (S m)))
                        (dsgen_beta lo / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    assert (Hfin : ((1 - dsgen_beta lo) + dsgen_beta lo == 1)%Q) by field.
    exact Hfin.
Qed.

Lemma dsgen_rowstoch_SS : forall (m : nat) (lo : Q), (0 < lo)%Q -> (lo < 1)%Q ->
  dsgen_rowstoch (S (S m)) lo.
Proof.
  intros m lo H0 H1 s Hs. destruct s as [|[|k]].
  - apply (proj1 (dsgen_rowstoch_head m lo H0
                    (mdsopt_row0_norm lo H0) (mdsopt_row1_norm lo H0))).
  - apply (proj2 (dsgen_rowstoch_head m lo H0
                    (mdsopt_row0_norm lo H0) (mdsopt_row1_norm lo H0))).
  - (* 行 ≥2：均匀行 nR·(1/nR) == 1 *)
    unfold dsgen_rowsum.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo (S (S k))) (seq 0 (S (S m)))
                    == dsgen_qN (S (S m)) * (1 / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo (S (S k)))
               (1 / dsgen_qN (S (S m))) (S (S m)) 0).
      intros j Hj. reflexivity. }
    rewrite Htail.
    assert (Hge : (1 <= S (S m))%nat) by lia.
    rewrite (Qmult_comm (dsgen_qN (S (S m))) (1 / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel 1 (dsgen_qN (S (S m)))
               (dsgen_ne_of_pos _ (dsgen_qN_pos (S (S m)) Hge))).
    reflexivity.
Qed.

(* ========== §8 可行性与最优性（nR≥3 时 β 恰为最优） ========== *)

(* β 可行：块条目 ≥ β/nR（正项加法单调 dsgen_le_add_pos2）、
   泄漏列取等、均匀行 ≥ β/nR（β ≤ 1 经 Qmult_le_compat_r）。 *)
Lemma dsgen_beta_feasible : forall (m : nat) (lo : Q), (0 < lo)%Q -> (lo < 1)%Q ->
  dsgen_feasible (S (S m)) lo (dsgen_beta lo).
Proof.
  intros m lo H0 H1 s j Hs Hj. unfold dsgen_feasible.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hbleak : (0 < dsgen_beta lo * (1 / dsgen_qN (S (S m))))%Q).
  { apply dsgen_mul_pos.
    - apply dsgen_beta_pos. exact H0.
    - apply dsgen_div_pos; [ exact mdsopt_01 | exact Hqpos ]. }
  destruct s as [|[|s]]; destruct j as [|[|j]]; cbn [dsgen_k].
  - (* (0,0) 块条目 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k00_pos; exact H0 ].
  - (* (0,1) 块条目 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k01_pos; exact H0 ].
  - (* (0, ≥2) 泄漏列取等 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply Qle_refl.
  - (* (1,0) 块条目 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k10_pos; exact H0 ].
  - (* (1,1) 块条目 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k11_pos; exact H0 ].
  - (* (1, ≥2) 泄漏列取等 *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply Qle_refl.
  - (* 均匀行条目：β·(1/nR) ≤ 1/nR（1/nR 与 /nR 核级可转换） *)
    apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact mdsopt_01 | exact Hqpos ] ].
    + apply Qle_refl.
  - apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact mdsopt_01 | exact Hqpos ] ].
    + apply Qle_refl.
  - apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact mdsopt_01 | exact Hqpos ] ].
    + apply Qle_refl.
Qed.

(* 极大性（nR≥3）：泄漏列条目 K(0,2) = β/nR 可达，任何可行 d 在该
   条目处 d·(1/nR) ≤ β/nR = β·(1/nR)，由 Qmult_le_r（iff 形）消去
   正因子 1/nR 得 d ≤ β。 *)
Lemma dsgen_beta_max : forall (m : nat) (lo d : Q), (1 <= m)%nat ->
  (forall s j : nat, (s < S (S m))%nat -> (j < S (S m))%nat ->
     (d * (1 / dsgen_qN (S (S m))) <= dsgen_k (S (S m)) lo s j)%Q) ->
  d <= dsgen_beta lo.
Proof.
  intros m lo d Hm Hd.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hhalf : (0 < 1 / dsgen_qN (S (S m)))%Q)
    by (apply dsgen_div_pos; [ exact mdsopt_01 | exact Hqpos ]).
  assert (Hb1 : (0 < S (S m))%nat) by lia.
  assert (Hb2 : (2 < S (S m))%nat) by lia.
  pose proof (Hd 0%nat 2%nat Hb1 Hb2) as H.
  cbn [dsgen_k] in H.
  rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne) in H.
  exact (proj1 (Qmult_le_r d (dsgen_beta lo) (1 / dsgen_qN (S (S m))) Hhalf) H).
Qed.

Theorem dsgen_optimal_ge3 : forall (m : nat) (lo : Q), (1 <= m)%nat ->
  (0 < lo)%Q -> (lo < 1)%Q ->
  dsgen_feasible (S (S m)) lo (dsgen_beta lo) /\
  (forall d : Q, dsgen_feasible (S (S m)) lo d -> d <= dsgen_beta lo).
Proof.
  intros m lo Hm H0 H1. split.
  - apply dsgen_beta_feasible; assumption.
  - intros d Hd. unfold dsgen_feasible in Hd.
    apply (dsgen_beta_max m lo d Hm Hd).
Qed.

(* ========== §9 主定理：行随机 + δ* 可行 + 严格次优（全体 nR≥2） ========== *)

Theorem dsgen_main_rowstoch : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> dsgen_rowstoch nR lo.
Proof.
  intros nR Hn lo H0 H1. destruct nR as [|[|m]]; [ lia | lia | ].
  apply dsgen_rowstoch_SS; assumption.
Qed.

Theorem dsgen_main_feasible : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> dsgen_feasible nR lo (lo*lo).
Proof.
  intros nR Hn lo H0 H1. destruct nR as [|[|m]]; [ lia | lia | ].
  intros s j Hs Hj. unfold dsgen_feasible.
  apply (Qle_trans (lo*lo * (1 / dsgen_qN (S (S m))))
                   (dsgen_beta lo * (1 / dsgen_qN (S (S m))))).
  - apply Qmult_le_compat_r.
    + apply Qlt_le_weak. apply dsgen_dstar_lt_beta; assumption.
    + apply Qlt_le_weak. apply dsgen_div_pos;
        [ exact mdsopt_01 | apply dsgen_qN_pos; lia ].
  - apply (dsgen_beta_feasible m lo H0 H1 s j Hs Hj).
Qed.

(* 主定理：δ* = lo² 在显式 nR 态核上严格次优（QltT Set 层见证，
   独立陈述以保 QltT 的 Set 位不被 Prop 合取吞并）。 *)
Theorem dsgen_main : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> QltT (lo*lo) (dsgen_beta lo).
Proof.
  intros nR Hn lo H0 H1.
  apply Qlt_to_QltT. apply dsgen_dstar_lt_beta; assumption.
Qed.

(* ========== §10 间隙件：闭式、严格正、≥ 2 态间隙（显式常数倍） ========== *)

Definition dsgen_gap (lo : Q) : Q := dsgen_beta lo - lo*lo.

Lemma dsgen_gap_eq : forall lo : Q, (0 < lo)%Q ->
  (dsgen_gap lo == (1 - lo*lo)/2)%Q.
Proof.
  intros lo H0. unfold dsgen_gap, dsgen_beta. field.
Qed.

Lemma dsgen_gap_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1. rewrite dsgen_gap_eq by exact H0.
  apply dsgen_div_pos.
  - apply dsgen_1mlo2_pos; assumption.
  - exact dsgen_2pos.
Qed.

(* 常数倍闭式：dsgen_gap = mdsopt_gap · (1+lo²)/(2lo²)。 *)
Lemma dsgen_gap_ratio : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_gap lo * ((1 + lo*lo)/(2*(lo*lo))) == dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1. unfold mdsopt_gap, dsgen_gap, dsgen_beta. field.
  - split.
    + apply dsgen_ne_of_pos. exact H0.
    + apply mdsopt_den_ne. exact H0.
Qed.

(* 常数倍 ≥ 1 ⟸ 1+lo² ≥ 2lo² ⟸ lo² ≤ 1。 *)
Lemma dsgen_gap_ratio_ge1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (1 <= (1 + lo*lo)/(2*(lo*lo)))%Q.
Proof.
  intros lo H0 H1.
  assert (Hd : (0 < 2*(lo*lo))%Q).
  { pose proof (proj2 (Qmult_lt_r 0 (lo*lo) 2 dsgen_2pos) (mdsopt_sq0 lo H0)) as H.
    rewrite Qmult_0_l, Qmult_comm in H. exact H. }
  apply (proj1 (Qmult_le_r 1 ((1 + lo*lo)/(2*(lo*lo))) (2*(lo*lo)) Hd)).
  rewrite (dsgen_div_cancel (1 + lo*lo) (2*(lo*lo)) (dsgen_ne_of_pos _ Hd)).
  rewrite Qmult_1_l, (Qmult_comm 2 (lo*lo)), dsgen_two_mul_r.
  rewrite (Qplus_comm 1 (lo*lo)).
  apply (proj2 (Qplus_le_r (lo*lo) 1 (lo*lo))).
  apply Qlt_le_weak. apply mdsopt_lt1; assumption.
Qed.

Lemma dsgen_gap_ge_mdsopt : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_gap lo <= dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1.
  rewrite <- (dsgen_gap_ratio lo H0 H1).
  pose proof (dsgen_gap_ratio_ge1 lo H0 H1) as Hr.
  pose proof (mdsopt_gap_pos lo H0 H1) as Hw.
  pose proof (proj2 (Qmult_le_r 1 ((1 + lo*lo)/(2*(lo*lo))) (mdsopt_gap lo) Hw) Hr) as Hle.
  rewrite Qmult_1_l in Hle.
  rewrite (Qmult_comm ((1 + lo*lo)/(2*(lo*lo))) (mdsopt_gap lo)) in Hle.
  exact Hle.
Qed.

(* ========== §11 提取出口（G3：独立目录，魔数=0 判据） ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_dsnr_g3out".
Separate Extraction dsgen_qN dsgen_beta dsgen_k dsgen_rowsum dsgen_gap.
