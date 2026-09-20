(* ============================================================ *)
(* UpReqSqrtOptimal.v —— 席Q14（EXPL1 候选 C13 深探席：            *)
(*   G10_LoebFam 注意力 √d 缩放界「+1 常数紧性」定理化）             *)
(* 日期：2026-09-17                                                *)
(*                                                                 *)
(* 攻击面（G10_LoebFam.v 实测坐标，本体只读）：                       *)
(*   :2783  Definition Delta := QK·w_root + 1（自注「+1 余量精确       *)
(*          吸收 (1/2)·w ≤ 2/3 < 1」）；w_root := real_inv_pos       *)
(*          (root_d kdim) (root_d_pos kdim)（:2781）；件 3           *)
(*          qk_logits_bounded（:2798）结论 real_le |logit| ≤ Δ。      *)
(*   :1528-1533 头注理想形：「|dotp| < 根积 + 1/2 ⟹ |logit| <        *)
(*          QK·inv(√d) + (1/2)·inv(√d) ≤ QK·inv(√d) + 1/2 <         *)
(*          QK·inv(√d) + 1 = Δ。+1 精确吸收 (1/2)·inv(√d) ≤ 1/2；    *)
(*          inv(√d) ≤ 1：√d ≥ 1 ⟹ inv 反序；1 ≤ √d（k=1 时相等、     *)
(*          k≥2 时严格）」。                                        *)
(*   G10 实证层是 Cauchy 尾段窗（√(k+1) 尾段 ≥ 3/4、w 尾段 ≤ 3/2，   *)
(*   (1/2)·w < 3/4 < 1），头注理想形此前只是注释——本件把它定理化。     *)
(*                                                                 *)
(* 方法（自注释反推的精确化，任书内两处猜测形式的裁定）：               *)
(*   从吸收恒等式反解：Δ − (根积 + 1/2)·inv(√d)                      *)
(*     = (QK − 根积)·inv(√d) + [1 − (1/2)·inv(√d)]，                 *)
(*   方括号 =「+1 吸收余量」。故紧性阈值不是 1−(1/2)·inv(√d)，          *)
(*   而是 c* = (1/2)·inv(√d) = 1/(2√d)：                             *)
(*     · c ≥ c* ⟹ 吸收链成立（充分，sqo_absorb_general/sqo_chain_bound）*)
(*     · c < c* ⟹ 在 根积=QK 点（x:=y，q:=k 可达）吸收链必破：         *)
(*       (x+1/2)·inv(√d) > x·inv(√d) + c 对一切 x 成立                 *)
(*       （构造性破界 sqo_absorb_breaks，无 existence-by-contradiction）*)
(*     · d=1 退化点：c* = 1/2，c < 1/2 时显式反例 (0+1/2)·/1 >        *)
(*       0·/1 + c（sqo_plus1_optimal 第三联）。                        *)
(*   诚实注记：「+1 不可去」在绝对真值层不成立——Cauchy–Schwarz 本身     *)
(*   给 |logit| ≤ QK·inv(√d)（c=0 即可）；紧性是「件 2 机制输出界       *)
(*   |dotp| < 根积 + 1/2 的吸收」这一层的紧性。本件定理化的正是这一层    *)
(*  （任务书「从 inline 证明体反推」要求的精确形态）。                  *)
(*                                                                 *)
(* 分层：                                                           *)
(*   S0 Q 桥件：sqo_qeq_le、sqo_mul_inv（逆根自乘恒等，Pos2Z 单跳）、   *)
(*      sqo_inv_sqrt_le_one / sqo_inv_sqrt_lt_one（1 ≤ s / 1 < s      *)
(*      ⟹ inv 反序——乘 /s 单调 + 自乘消去，Q 正性+平方单调单跳）。      *)
(*   S1（G1 保底）吸收最优性表征族：                                  *)
(*      sqo_one_le_sqrt（1 ≤ s·s ⟹ 1 ≤ s，Q 正性+平方单调）；          *)
(*      sqo_sqrt_eq_one / sqo_sq_one_of_one（s·s==1 ⟺ s==1）；         *)
(*      sqo_sqrt_gt_one（1 < s·s ⟹ 1 < s 严格）；                     *)
(*      sqo_one_le_sqrt_characterization（三联 And 账）；              *)
(*      见证接口形（√d 无 Q 全函数，按库内 sqrt 见证接口                *)
(*      root_of d := projT1 (real_sqrt_exists d Hd) 的 Q 层镜像：      *)
(*      前提 0 ≤ s ∧ s·s == d 承载）：                                *)
(*      sqo_sqrt_ge_one_of_d、sqo_absorb_half_le（(1/2)·inv(√d)        *)
(*      ≤ 1/2 头注①直译）、sqo_absorb_half_le_w（witness 形①）、        *)
(*      sqo_sqrt_eq_one_iff_d（d==1 ⟺ √d==1）、                        *)
(*      sqo_sqrt_gt_one_of_d（d>1 ⟹ 严格）。                           *)
(*   S2（G2 主件）紧性定理：                                          *)
(*      sqo_absorb_general（一般 h 一般 c 吸收链：h·inv(√d) ≤ c ⟹      *)
(*      (x+h)·inv(√d) ≤ y·inv(√d)+c——h 槽即件 2 的 eps 透传位）；       *)
(*      sqo_chain_bound（G10 头注链理想形整体：|·| ≤ 根积+1/2 形输入）；  *)
(*      sqo_absorb_breaks（c < 阈值 ⟹ 构造性违例，x 任意）；            *)
(*      sqo_plus1_optimal（四联账旗舰：充分+构造破界+d=1 退化反例+      *)
(*      余量恰为零表征）；                                            *)
(*      sqo_plus1_threshold_dec（阈值可判定二分，Set 层出口）；          *)
(*      sqo_plus1_margin（G10 Δ 的 +1 余量 1 − (1/2)·inv(√d) ≥ 1/2      *)
(*      恒正账——「+1 精确吸收」的余量定量）。                           *)
(*   S3（G3 加餐）分段精确形：                                        *)
(*      sqo_piecewise（d==1 ⟹ (1/2)·inv(√d) 恰 1/2；d>1 ⟹ 严格小于      *)
(*      1/2——头注「k=1 相等、k≥2 严格」的精确分段形）。eps 版对接由      *)
(*      sqo_absorb_general 的 h 自由参量承载（G10 件 2 的 h 槽）。      *)
(*                                                                 *)
(* 公理面：本文件语句面全 Set 层承载（Qeq/forall + 一个 sumbool 出口）； *)
(*   合取账用 Stdlib and（/\）承载——本件组件全 Prop（蕴涵/Qle/Qeq），    *)
(*   CW 世界的 And: Set->Set->Set 不适用；信息性出口由 threshold_dec 的  *)
(*   sumbool 承担；证内 Prop 仅作桥；零新增假设件、零 承认件、零       *)
(*   Hypothesis/Variable 位、零经典逻辑（分支全走 Qlt_le_dec/Qeq_dec    *)
(*   可判定二分）。Print Assumptions 应全 Closed——lia/lra/ring/       *)
(*   vm_compute 均 ax-free，Require 链（QArith/Qring/Lia/Lqa/Setoid）   *)
(*   不触 Psatz。提取面以 Separate Extraction 产物 Obj.magic 零命中准。 *)
(*                                                                 *)
(* 红线自审：纯构造性；反例全部给出显式违例见证（sqo_absorb_breaks     *)
(*   对任意 x 给出严格大于、d=1 反例是常量不等式）；非平凡真实现        *)
(*   （阈值 c*=(1/2)·inv(√d) 的充分/必要/退化/零余量四向刻画均为        *)
(*   新定理，非库件重述）；禁改既有文件一行——本席纯新文件。             *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Lia Lqa Setoid.

Open Scope Q_scope.

(* ################ 第 0 部分：Q 桥件 ########################### *)

(* Qeq → Qle 桥（分量交叉积直写，Q 正性无关） *)
Lemma sqo_qeq_le : forall x y : Q, x == y -> x <= y.
Proof.
  intros [nx dx] [ny dy] H.
  unfold Qeq, Qle in H |- *; cbn in *.
  lia.
Qed.

(* 坑位注记：Q_scope 的 <> 落 plain eq（not (@eq Q s 0)），不排除 0#ds
   类表示——Qeq 不等必须显式写 ~ (s == 0)。 *)
Lemma sqo_neq0_of_lt : forall s : Q, 0 < s -> ~ s == 0.
Proof.
  intros s Hps Heq.
  apply (Qlt_irrefl 0).
  apply (Qlt_le_trans 0 s 0).
  - exact Hps.
  - apply sqo_qeq_le. exact Heq.
Qed.

(* 逆根自乘恒等：s·/s == 1（Qeq 意义 s ≠ 0；Zpos/Zneg 分支 Pos2Z 单跳
   + ring；Z0 分支由 Qeq 否定给 0=0 矛盾） *)
Lemma sqo_mul_inv : forall s : Q, ~ s == 0 -> s * / s == 1.
Proof.
  intros [ns ds] Hne.
  destruct ns as [|p|p].
  - exfalso. apply Hne. unfold Qeq. reflexivity.
  - unfold Qeq. cbn. repeat rewrite Pos2Z.inj_mul. ring.
  - unfold Qeq. cbn. repeat rewrite Pos2Z.inj_mul. ring.
Qed.

(* 头注②：√d ≥ 1 ⟹ inv(√d) ≤ 1（乘 /s 单调 + 自乘消去，非分量法） *)
Lemma sqo_inv_sqrt_le_one : forall s : Q, 1 <= s -> / s <= 1.
Proof.
  intros s H.
  assert (Hps : 0 < s) by lra.
  assert (Hle0 : 0 <= / s) by (apply Qinv_le_0_compat; lra).
  assert (Hle : 1 * / s <= s * / s).
  { apply (Qmult_le_compat_r 1 s (/ s)); [exact H | exact Hle0]. }
  assert (Hcancel : s * / s == 1)
    by (apply sqo_mul_inv; apply sqo_neq0_of_lt; lra).
  setoid_replace (1 * / s) with (/ s) in Hle by (field; lra).
  setoid_replace (s * / s) with 1 in Hle by exact Hcancel.
  exact Hle.
Qed.

(* 头注②严格形：1 < s ⟹ /s < 1（k≥2 支的 inv 严格反序） *)
Lemma sqo_inv_sqrt_lt_one : forall s : Q, 1 < s -> / s < 1.
Proof.
  intros s H.
  assert (Hps : 0 < s) by lra.
  assert (Hpos : 0 < / s) by (apply Qinv_lt_0_compat; exact Hps).
  assert (Hlt : 1 * / s < s * / s).
  { apply (Qmult_lt_compat_r 1 s (/ s)); [exact Hpos | exact H]. }
  assert (Hcancel : s * / s == 1)
    by (apply sqo_mul_inv; apply sqo_neq0_of_lt; lra).
  setoid_replace (1 * / s) with (/ s) in Hlt by ring.
  setoid_replace (s * / s) with 1 in Hlt by exact Hcancel.
  exact Hlt.
Qed.

(* ################ 第 1 部分：G1 吸收最优性表征族 ############### *)

(* Q 正性 + 平方单调单跳：1 ≤ √d（非严格） *)
Lemma sqo_one_le_sqrt : forall s : Q, 0 <= s -> 1 <= s * s -> 1 <= s.
Proof.
  intros s H0 Hsq.
  destruct (Qlt_le_dec s 1) as [Hlt | Hle].
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s);
        [apply Qlt_le_weak; exact Hlt | exact H0]. }
    setoid_replace (1 * s) with s in Hb by ring.
    assert (H1 : 1 <= s) by (apply (Qle_trans 1 (s * s) s); assumption).
    apply (Qlt_irrefl 1). apply (Qle_lt_trans 1 s 1); [exact H1 | exact Hlt].
  - exact Hle.
Qed.

(* 等号分界：s·s == 1 ⟹ s == 1（0 ≤ s；两侧严格支构造排除） *)
Lemma sqo_sqrt_eq_one : forall s : Q, 0 <= s -> s * s == 1 -> s == 1.
Proof.
  intros s H0 Hsq.
  assert (Hss1 : 1 <= s * s)
    by (apply (sqo_qeq_le 1 (s * s)); apply Qeq_sym; exact Hsq).
  assert (Hss : s * s <= 1) by (apply (sqo_qeq_le (s * s) 1); exact Hsq).
  destruct (Qlt_le_dec s 1) as [Hlt | Hle].
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s);
        [apply Qlt_le_weak; exact Hlt | exact H0]. }
    setoid_replace (1 * s) with s in Hb by ring.
    assert (Hlt2 : s * s < 1)
      by (apply (Qle_lt_trans (s * s) s 1); [exact Hb | exact Hlt]).
    apply (Qlt_irrefl 1).
    apply (Qle_lt_trans 1 (s * s) 1); [exact Hss1 | exact Hlt2].
  - destruct (Qlt_le_dec 1 s) as [Hgt | Hge].
    + exfalso.
      assert (Hb : 1 * s <= s * s).
      { apply (Qmult_le_compat_r 1 s s);
          [apply Qlt_le_weak; exact Hgt | exact H0]. }
      setoid_replace (1 * s) with s in Hb by ring.
      assert (Hlt2 : 1 < s * s)
        by (apply (Qlt_le_trans 1 s (s * s)); [exact Hgt | exact Hb]).
      apply (Qlt_irrefl 1).
      apply (Qlt_le_trans 1 (s * s) 1); [exact Hlt2 | exact Hss].
    + apply Qle_antisym; assumption.
Qed.

(* 等号分界逆向：s == 1 ⟹ s·s == 1（平凡支，与上件合成 iff 账） *)
Lemma sqo_sq_one_of_one : forall s : Q, s == 1 -> s * s == 1.
Proof.
  intros s H. rewrite H. reflexivity.
Qed.

(* 严格分界：1 < s·s ⟹ 1 < s（d>1 支严格性） *)
Lemma sqo_sqrt_gt_one : forall s : Q, 0 <= s -> 1 < s * s -> 1 < s.
Proof.
  intros s H0 Hss.
  destruct (Qlt_le_dec 1 s) as [Hge | Hle].
  - exact Hge.
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s); [exact Hle | exact H0]. }
    setoid_replace (1 * s) with s in Hb by ring.
    apply (Qlt_irrefl 1).
    apply (Qlt_le_trans 1 (s * s) 1).
    + exact Hss.
    + apply (Qle_trans (s * s) s 1); [exact Hb | exact Hle].
Qed.

(* G1 旗舰账：1 ≤ √d ∧ 等号/严格分界三联（头注「1 ≤ √d（k=1 时相等、
   k≥2 时严格）」的定理化） *)
Theorem sqo_one_le_sqrt_characterization : forall s : Q, 0 <= s ->
  (1 <= s * s -> 1 <= s) /\
  ((s * s == 1 -> s == 1) /\ (1 < s * s -> 1 < s)).
Proof.
  intros s H0. split.
  - apply sqo_one_le_sqrt. exact H0.
  - split.
    + apply sqo_sqrt_eq_one. exact H0.
    + apply sqo_sqrt_gt_one. exact H0.
Qed.

(* 见证接口形（Q 层镜像 G10 root_of：√d 以 0 ≤ s ∧ s·s == d 承载）：
   1 ≤ d ⟹ 1 ≤ √d *)
Lemma sqo_sqrt_ge_one_of_d : forall d s : Q,
  0 <= s -> s * s == d -> 1 <= d -> 1 <= s.
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_one_le_sqrt; [exact H0 |].
  setoid_replace (s * s) with d by exact Hsd.
  exact Hd.
Qed.

(* 头注①直译：(1/2)·inv(√d) ≤ 1/2（⟺ inv(√d) ≤ 1，s 版） *)
Lemma sqo_absorb_half_le : forall s : Q, 1 <= s -> (1#2) * / s <= (1#2).
Proof.
  intros s H.
  setoid_replace ((1#2) * / s) with (/ s * (1#2)) by (field; lra).
  apply (Qle_trans (/ s * (1#2)) (1 * (1#2)) (1#2)).
  - apply (Qmult_le_compat_r (/ s) 1 (1#2)).
    + apply sqo_inv_sqrt_le_one. exact H.
    + lra.
  - apply (sqo_qeq_le (1 * (1#2)) (1#2)). reflexivity.
Qed.

(* 头注① witness 形：d ≥ 1 ⟹ (1/2)·inv(√d) ≤ 1/2（+1 精确吸收引理） *)
Lemma sqo_absorb_half_le_w : forall d s : Q,
  0 <= s -> s * s == d -> 1 <= d -> (1#2) * / s <= (1#2).
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_absorb_half_le.
  apply (sqo_sqrt_ge_one_of_d d s); assumption.
Qed.

(* d == 1 ⟺ √d == 1（等号点在维度侧的迁移） *)
Lemma sqo_sqrt_eq_one_iff_d : forall d s : Q,
  0 <= s -> s * s == d -> (s == 1 <-> d == 1).
Proof.
  intros d s H0 Hsd. split; intros H.
  - assert (Hs1 : s * s == 1) by (apply sqo_sq_one_of_one; exact H).
    setoid_replace d with (s * s) by (symmetry; exact Hsd).
    exact Hs1.
  - assert (Hs1 : s * s == 1).
    { setoid_replace (s * s) with d by exact Hsd. exact H. }
    apply sqo_sqrt_eq_one; assumption.
Qed.

(* d > 1 ⟹ √d > 1（严格性在维度侧的迁移） *)
Lemma sqo_sqrt_gt_one_of_d : forall d s : Q,
  0 <= s -> s * s == d -> 1 < d -> 1 < s.
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_sqrt_gt_one; [exact H0 |].
  setoid_replace d with (s * s) in Hd by (symmetry; exact Hsd).
  exact Hd.
Qed.

(* ################ 第 2 部分：G2 紧性定理 ##################### *)

(* 一般 h 一般 c 吸收链（h 槽 = G10 件 2 的 eps 透传位；本件 h := 1/2）：
   h·inv(√d) ≤ c ⟹ (x+h)·inv(√d) ≤ y·inv(√d) + c（x ≤ y）。
   吸收发生处：平方展开后 h·inv(√d) 被 c 吃掉——紧性阈值即 h·inv(√d)。 *)
Lemma sqo_absorb_general : forall x y s c h : Q,
  0 < s -> x <= y -> h * / s <= c -> (x + h) * / s <= y * / s + c.
Proof.
  intros x y s c h Hs Hxy Hhc.
  assert (Hinvs : 0 <= / s)
    by (apply Qinv_le_0_compat; apply Qlt_le_weak; exact Hs).
  apply (Qle_trans ((x + h) * / s) (x * / s + h * / s) (y * / s + c)).
  - apply (sqo_qeq_le ((x + h) * / s) (x * / s + h * / s)). field; lra.
  - apply (Qplus_le_compat (x * / s) (y * / s) (h * / s) c).
    + apply (Qmult_le_compat_r x y (/ s)); assumption.
    + exact Hhc.
Qed.

(* G10 头注链理想形整体：件 2 输出界形输入 X ≤ 根积 + 1/2、根积 ≤ QK、
   c ≥ (1/2)·inv(√d) ⟹ |logit| 形输出 X·inv(√d) ≤ QK·inv(√d) + c。
   （G10 实证结论是 real_le 非严格——此处忠实对齐。） *)
Theorem sqo_chain_bound : forall X D QC s c : Q,
  0 < s -> 1 <= s -> X <= D + (1#2) -> D <= QC ->
  (1#2) * / s <= c -> X * / s <= QC * / s + c.
Proof.
  intros X D QC s c Hs H1 HX HD Hc.
  assert (Hinvs : 0 <= / s)
    by (apply Qinv_le_0_compat; apply Qlt_le_weak; exact Hs).
  apply (Qle_trans (X * / s) ((D + (1#2)) * / s) (QC * / s + c)).
  - apply (Qmult_le_compat_r X (D + (1#2)) (/ s)); assumption.
  - apply (Qle_trans ((D + (1#2)) * / s) (D * / s + (1#2) * / s)
                     (QC * / s + c)).
    + apply (sqo_qeq_le ((D + (1#2)) * / s) (D * / s + (1#2) * / s)).
      field; lra.
    + apply (Qplus_le_compat (D * / s) (QC * / s) ((1#2) * / s) c).
      * apply (Qmult_le_compat_r D QC (/ s)); assumption.
      * exact Hc.
Qed.

(* 构造性破界（必要性）：c < (1/2)·inv(√d) ⟹ 吸收链在 根积=QK 点
   （x 任意，q:=k 可达）严格违例——显式见证，非反证法。 *)
Lemma sqo_absorb_breaks : forall x s c : Q,
  0 < s -> c < (1#2) * / s -> (x + (1#2)) * / s > x * / s + c.
Proof.
  intros x s c Hs Hc.
  setoid_replace ((x + (1#2)) * / s) with (x * / s + (1#2) * / s) by (field; lra).
  remember (/ s) as u.
  lra.
Qed.

(* G2 旗舰四联账：+1 换一般 c 的界保持条件完全刻画。
   联 1（充分）：c ≥ (1/2)·inv(√d) ⟹ 吸收链对所有 x ≤ y 成立。
   联 2（必要·构造破界）：c < (1/2)·inv(√d) ⟹ 对任意 x 严格违例。
   联 3（d=1 退化点显式反例）：c < 1/2 ⟹ (0+1/2)·/1 > 0·/1 + c。
   联 4（余量恰为零表征）：吸收恒等对全 x 成立 ⟺ c 恰为阈值
   (1/2)·inv(√d)——「吸收余量恰为零」的机器形态。 *)
Theorem sqo_plus1_optimal : forall s : Q, 0 < s ->
  (forall c x y : Q, (1#2) * / s <= c -> x <= y ->
        (x + (1#2)) * / s <= y * / s + c) /\
  ((forall c x : Q, c < (1#2) * / s ->
         (x + (1#2)) * / s > x * / s + c) /\
   ((forall c : Q, c < (1#2) -> (0 + (1#2)) * / 1 > 0 * / 1 + c) /\
    (forall c : Q, (forall x : Q, (x + (1#2)) * / s == x * / s + c) ->
                   c == (1#2) * / s))).
Proof.
  intros s Hs. split.
  - intros c x y Hc Hxy. exact (sqo_absorb_general x y s c (1#2) Hs Hxy Hc).
  - split.
    + intros c x Hc. exact (sqo_absorb_breaks x s c Hs Hc).
    + split.
      * intros c Hc.
        change (/ 1) with 1.
        setoid_replace ((0 + (1#2)) * 1) with ((1#2)) by ring.
        setoid_replace (0 * 1 + c) with c by ring.
        exact Hc.
      * intros c Hfam.
        assert (H0 : (0 + (1#2)) * / s == 0 * / s + c) by (apply Hfam).
        setoid_replace ((0 + (1#2)) * / s) with ((1#2) * / s) in H0 by (field; lra).
        setoid_replace (0 * / s + c) with c in H0 by (field; lra).
        exact (Qeq_sym _ _ H0).
Qed.

(* 阈值可判定二分（Set 层出口）：c ≥/＜ (1/2)·inv(√d) 构造可判 *)
Lemma sqo_plus1_threshold_dec : forall s c : Q,
  { (1#2) * / s <= c } + { c < (1#2) * / s }.
Proof.
  intros s c.
  destruct (Qlt_le_dec c ((1#2) * / s)) as [Hlt | Hle].
  - right. exact Hlt.
  - left. exact Hle.
Qed.

(* +1 余量定量账：G10 Δ 的吸收余量 1 − (1/2)·inv(√d) ≥ 1/2 恒正
   （在 d ≥ 1 全域；余量恰为零只在阈值 c* 处发生，见联 4） *)
Theorem sqo_plus1_margin : forall s : Q, 0 < s -> 1 <= s ->
  (1#2) <= 1 - (1#2) * / s.
Proof.
  intros s Hs H1.
  assert (Hab : (1#2) * / s <= (1#2)) by (apply sqo_absorb_half_le; exact H1).
  remember (/ s) as u.
  lra.
Qed.

(* ################ 第 3 部分：G3 分段精确形 ################### *)

(* 头注「k=1 时相等、k≥2 时严格」的精确分段形：
   d == 1 ⟹ (1/2)·inv(√d) 恰为 1/2；d > 1 ⟹ 严格小于 1/2。 *)
Theorem sqo_piecewise : forall d s : Q, 0 <= s -> s * s == d ->
  (d == 1 -> (1#2) * / s == (1#2)) /\
  (1 < d -> (1#2) * / s < (1#2)).
Proof.
  intros d s H0 Hsd. split.
  - intros Hd.
    assert (Hs1 : s * s == 1).
    { setoid_replace (s * s) with d by exact Hsd. exact Hd. }
    assert (Heq : s == 1) by (apply sqo_sqrt_eq_one; assumption).
    setoid_replace s with 1 by exact Heq.
    change (/ 1) with 1.
    reflexivity.
  - intros Hd.
    assert (Hgt1s : 1 < s).
    { apply sqo_sqrt_gt_one; [exact H0 |].
      setoid_replace d with (s * s) in Hd by (symmetry; exact Hsd).
      exact Hd. }
    assert (Hps : 0 < s) by lra.
    setoid_replace ((1#2) * / s) with (/ s * (1#2)) by (field; lra).
    apply (Qmult_lt_compat_r (/ s) 1 (1#2)).
    + lra.
    + apply sqo_inv_sqrt_lt_one. exact Hgt1s.
Qed.
