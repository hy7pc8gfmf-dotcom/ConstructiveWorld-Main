(* ===================================================================== *)
(*  abl_z2s_ps.v —— ζ(2) 级数部分和承载件（值面恒等式砖）                    *)
(*  模块名：abl_z2s_ps。                                                 *)
(*  使命：为 ζ(2) := Σ_{k≥1} 1/k² 建立部分和族 z2s_ps M = Σ_{k<M} 1/(k+1)²  *)
(*        的有理算术表述与值面恒等式面：级数项 1/(k+1)² 严格正（QltT）、     *)
(*        部分和递归展开、严格正与单调（QleT'）；零权 Beta 恒等面           *)
(*        z2s_term k == zb2_term 0 k 与部分和 == 闭式项和                   *)
(*        z2s_ps (S M) == zb2_Isum 0 M；截断展开恒等式 (1−t)^{n+1}A +       *)
(*        t^{M+1}P = 1 的 ζ(2) 侧双变量实例（t := xy 档）与余项分离序面      *)
(*        (1−xy)^{n+1}A ≤ 1；有理数值锚 z2s_ps 3 == 49/36。后续装配入口：    *)
(*        部分和的极限面与 ζ(2)=π²/6 评估桥自此件语句面起装。                *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；S01_BaseRing、          *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists、PolyIntegral、        *)
(*        PadeErrorIntegral（pei_div_eq 交义乘除法等式）；abl_z2_truncfam    *)
(*        （zb2_master/zb2_ps_bound）、abl_z2_itg_carrier（zb2_term/        *)
(*        zb2_Isum）。零外部证书器、零实数层、零经典逻辑。                   *)
(*  构造性：纯构造性、零假设声明、零承认式语句、零悬置假设；级数承载语句面    *)
(*        全部零前提（Qeq 传输面与 Set 层序见证）；双变量实例按              *)
(*        abl_z2_truncfam 同族形；除法恒等步以交义乘除法等式闭合，           *)
(*        未引入任何有序域决策程序。                                       *)
(*  编译配方：coqc -native-compiler no -q -Q <本件目录> ""                  *)
(*        -Q <认证 vo 世界根> "" abl_z2s_ps.v（COQLIB/ROCQLIB 全字面        *)
(*        指向 9.1 平台库）。                                              *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.    *)
(*        London Math. Soc. 11 (1979) 中 I_0 的级数表示步；ζ(2) 级数部分和  *)
(*        的经典有理逼近面。                                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam abl_z2_itg_carrier.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 承载定义（接口面，签名定死）                                      *)
(* ============================================================ *)

(* ζ(2) 级数第 k 项：1/(k+1)²（正整数平方倒数，Z 像分母形） *)
Definition z2s_term (k : nat) : Q :=
  1 / ((Z.of_nat (Datatypes.S k) # 1) * (Z.of_nat (Datatypes.S k) # 1))%Q.

(* ζ(2) 部分和：Σ_{k<M} 1/(k+1)²（M 项截断） *)
Fixpoint z2s_ps (M : nat) : Q :=
  match M with
  | O => 0
  | Datatypes.S M' => z2s_ps M' + z2s_term M'
  end.

(* 正整数 Z 像的严格正性（除法恒等步的正性证书） *)
Lemma z2s_pos_image : forall k : nat, Qlt 0 (Z.of_nat (Datatypes.S k) # 1).
Proof.
  intro k. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* §1 级数面：项正性、递归展开、和的正性与单调                            *)
(* ============================================================ *)

(* 级数项严格正：分子 1 > 0、分母为两个正因子之积 *)
Lemma z2s_term_pos : forall k : nat, QltT 0 (z2s_term k).
Proof.
  intro k. apply Qlt_to_QltT. unfold z2s_term, Qdiv.
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      apply z2s_pos_image.
Qed.

(* 级数项非负（Set 层见证；单调步用） *)
Lemma z2s_term_nonneg : forall k : nat, QleT' 0 (z2s_term k).
Proof.
  intro k. apply Qle_to_QleT'. apply Qlt_le_weak.
  apply QltT_to_Qlt. apply z2s_term_pos.
Qed.

(* 部分和递归展开（定义性） *)
Lemma z2s_ps_unfold : forall M : nat,
  z2s_ps (Datatypes.S M) == (z2s_ps M + z2s_term M)%Q.
Proof.
  intro M. cbn [z2s_ps]. reflexivity.
Qed.

(* Qeq 右端换形的严格正传输：a == b、0 < a ⟹ 0 < b（Set 层见证） *)
Lemma z2s_qeq_lt_r : forall a b : Q, a == b -> QltT 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha. apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 a b (QltT_to_Qlt _ _ Ha)).
  apply qeq_imp_qle. exact Hab.
Qed.

(* 部分和严格正：首项严格正，逐项累加非负项保持严格正 *)
Lemma z2s_ps_pos : forall M : nat, QltT 0 (z2s_ps (Datatypes.S M)).
Proof.
  induction M as [| M IH].
  - cbn [z2s_ps]. apply (z2s_qeq_lt_r (0 + z2s_term 0) (z2s_term 0)).
    + ring.
    + apply z2s_term_pos.
  - cbn [z2s_ps].
    apply Qlt_to_QltT.
    apply (pei_lt_le_plus (z2s_ps (Datatypes.S M))
                          (z2s_term (Datatypes.S M))).
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply z2s_term_pos.
Qed.

(* 部分和单调：z2s_ps M ≤ z2s_ps (S M)（Set 层见证） *)
Lemma z2s_ps_mono : forall M : nat, QleT' (z2s_ps M) (z2s_ps (Datatypes.S M)).
Proof.
  intro M.
  apply (zb2_qleT'_wd_r (z2s_ps M + z2s_term M)
                        (z2s_ps (Datatypes.S M)) (z2s_ps M)).
  - exact (Qeq_sym _ _ (z2s_ps_unfold M)).
  - apply qleT'_plus_nonneg_rT. apply z2s_term_nonneg.
Qed.

(* ============================================================ *)
(* §2 零权 Beta 恒等面：ζ(2) 级数项与部分和的闭式换算                     *)
(* ============================================================ *)

(* 零权比值恒等式：q_fact k / q_fact (S k) == 1/(S k)。
   由 q_fact_succ 换形后按交义乘除法等式（pei_div_eq）闭合。 *)
Lemma z2s_beta0_ratio : forall k : nat,
  (q_fact k / q_fact (Datatypes.S k))%Q
  == 1 / (Z.of_nat (Datatypes.S k) # 1)%Q.
Proof.
  intros k. apply pei_div_eq.
  - apply q_fact_pos.
  - apply z2s_pos_image.
  - rewrite (q_fact_succ k). ring.
Qed.

(* 零权 Beta 恒等面：ζ(2) 级数项 == Beukers 族零权重闭式项。
   zb2_term 0 k = C(k,0)·(k!·0!/(k+1)!)² = (k!/(k+1)!)²，与级数项相等。 *)
Lemma z2s_term_bridge : forall k : nat, z2s_term k == zb2_term 0 k.
Proof.
  intro k. unfold z2s_term, zb2_term. cbn [Nat.add].
  rewrite zb2_bkC_zero.
  replace (k + 0 + 1)%nat with (Datatypes.S k)%nat by lia.
  cbn [q_fact Z.of_nat]. rewrite Qmult_1_r.
  transitivity ((q_fact k / q_fact (Datatypes.S k)
                 * (q_fact k / q_fact (Datatypes.S k)))%Q).
  - rewrite (z2s_beta0_ratio k).
    unfold Qdiv. rewrite Qinv_mult_distr. rewrite !Qmult_1_l. reflexivity.
  - rewrite Qmult_1_l. reflexivity.
Qed.

(* 部分和 = 闭式项和：z2s_ps (S M) == zb2_Isum 0 M。
   ζ(2) 值面的代数换算面：M 项部分和与零权重二重积分族闭式项和逐项相等。 *)
Corollary z2s_Isum_bridge : forall M : nat,
  z2s_ps (Datatypes.S M) == zb2_Isum 0 M.
Proof.
  induction M as [| M IH].
  - cbn [z2s_ps zb2_Isum]. rewrite (z2s_term_bridge 0). ring.
  - cbn [z2s_ps zb2_Isum]. rewrite IH. rewrite (z2s_term_bridge (Datatypes.S M)).
    ring.
Qed.

(* 部分和严格正的闭式项和读法：zb2_Isum 0 M 严格正的直接传输 *)
Corollary z2s_ps_pos_via_Isum : forall M : nat, QltT 0 (zb2_Isum 0 M).
Proof.
  intro M. apply (z2s_qeq_lt_r (z2s_ps (Datatypes.S M)) (zb2_Isum 0 M)).
  - exact (z2s_Isum_bridge M).
  - apply z2s_ps_pos.
Qed.

(* ============================================================ *)
(* §3 截断展开恒等式的 ζ(2) 侧双变量实例（t := xy 档）                     *)
(* ============================================================ *)

(* 值域乘积复合件：0 ≤ x ≤ 1、0 ≤ y ≤ 1 ⟹ 0 ≤ xy ≤ 1 *)
Lemma z2s_range_mul : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= x * y <= 1.
Proof.
  intros x y Hx Hy. destruct Hx as [Hx0 Hx1]. destruct Hy as [Hy0 Hy1].
  split.
  - apply Qmult_le_0_compat; assumption.
  - assert (E : (1 * y)%Q == y) by apply Qmult_1_l.
    apply (Qle_trans (x * y) (1 * y) 1).
    + apply Qmult_le_compat_r; assumption.
    + apply (Qle_trans (1 * y) y 1).
      * apply qeq_imp_qle. exact E.
      * exact Hy1.
Qed.

(* 截断展开恒等式双变量实例（t := xy 档；同族参数化）：
   在 0 ≤ xy ≤ 1 上 (1−xy)^{n+1}·A(n,M,xy) + (xy)^{M+1}·P(n,M,xy) = 1。 *)
Lemma z2s_master_xy : forall (n M : nat) (x y : Q), 0 <= x * y <= 1 ->
  q_pow (1 - x * y) (Datatypes.S n) * zb2_ps n M (x * y)
  + q_pow (x * y) (Datatypes.S M) * zb2_pq n M (x * y) == 1.
Proof.
  intros n M x y Hxy. exact (zb2_master n M (x * y) Hxy).
Qed.

(* 余项显式分离序面（双变量实例）：(1−xy)^{n+1}·A(n,M,xy) ≤ 1。
   代数读法：1 − (1−xy)^{n+1}·A = (xy)^{M+1}·P ≥ 0（右端两因子非负）。 *)
Lemma z2s_master_rim : forall (n M : nat) (x y : Q), 0 <= x * y <= 1 ->
  QleT' (q_pow (1 - x * y) (Datatypes.S n) * zb2_ps n M (x * y)) 1.
Proof.
  intros n M x y Hxy. exact (zb2_ps_bound n M (x * y) Hxy).
Qed.

(* ============================================================ *)
(* §4 数值锚                                                            *)
(* ============================================================ *)

(* 有理数值锚：1 + 1/4 = 5/4 *)
Lemma z2s_ps_anchor2 : z2s_ps 2 == (5 # 4).
Proof. vm_compute. reflexivity. Qed.

(* 有理数值锚：1 + 1/4 + 1/9 = 49/36 *)
Lemma z2s_ps_anchor3 : z2s_ps 3 == (49 # 36).
Proof. vm_compute. reflexivity. Qed.

(* 桥面数值锚：零权重闭式项和与部分和在 M = 2 处同为 49/36 *)
Lemma z2s_Isum_bridge_anchor : zb2_Isum 0 2 == (49 # 36).
Proof.
  rewrite <- (z2s_Isum_bridge 2). exact z2s_ps_anchor3.
Qed.

(* ============================================================ *)
(* §5 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions z2s_term_pos.
Print Assumptions z2s_ps_unfold.
Print Assumptions z2s_ps_pos.
Print Assumptions z2s_ps_mono.
Print Assumptions z2s_beta0_ratio.
Print Assumptions z2s_term_bridge.
Print Assumptions z2s_Isum_bridge.
Print Assumptions z2s_range_mul.
Print Assumptions z2s_master_xy.
Print Assumptions z2s_master_rim.
Print Assumptions z2s_ps_anchor3.
Print Assumptions z2s_Isum_bridge_anchor.

(* ============================================================ *)
(* §6 极限面：尾界、有界与 Cauchy 模量                                  *)
(* ============================================================ *)

(* 二的幂减一的结构化承载：z2s_half_idx n = 2^n − 1（归纳定义），          *)
(* 因而 Datatypes.S (z2s_half_idx n) = 2^n 为定义性恒等，免幂函数换算。     *)
Fixpoint z2s_half_idx (n : nat) : nat :=
  match n with
  | O => O
  | Datatypes.S n' => (z2s_half_idx n' + (z2s_half_idx n' + 1))%nat
  end.

(* 二的幂的有理倒数：z2s_half_pow n = 1/2^n（Cauchy 模量的速率量） *)
Definition z2s_half_pow (n : nat) : Q :=
  1 / (Z.of_nat (Datatypes.S (z2s_half_idx n)) # 1)%Q.

(* ------------------------------------------------------------ *)
(* §6.0 极限面辅助族：QltT 的传输、传递与加法相容                            *)
(* ------------------------------------------------------------ *)

(* 正整数倒数严格正：1/(S k) > 0 *)
Lemma z2s_inv_pos : forall k : nat, QltT 0 (1 / (Z.of_nat (Datatypes.S k) # 1)%Q).
Proof.
  intro k. apply Qlt_to_QltT. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* QltT 传递 *)
Lemma z2s_ltT_trans : forall a b c : Q, QltT a b -> QltT b c -> QltT a c.
Proof.
  intros a b c H1 H2. apply Qlt_to_QltT. apply (Qlt_trans a b c).
  - apply QltT_to_Qlt. exact H1.
  - apply QltT_to_Qlt. exact H2.
Qed.

(* Qeq 左端传输：a == b、a < c ⟹ b < c（Set 层见证） *)
Lemma z2s_qeq_ltT : forall a b c : Q, a == b -> QltT a c -> QltT b c.
Proof.
  intros a b c Hab H. apply Qlt_to_QltT. apply (Qle_lt_trans b a c).
  - apply qeq_imp_qle. exact (Qeq_sym a b Hab).
  - apply QltT_to_Qlt. exact H.
Qed.

(* Qeq 右端传输：a == b、c < a ⟹ c < b（Set 层见证） *)
Lemma z2s_qeq_ltT_r : forall a b c : Q, a == b -> QltT c a -> QltT c b.
Proof.
  intros a b c Hab H. apply Qlt_to_QltT. apply (Qlt_le_trans c a b).
  - apply QltT_to_Qlt. exact H.
  - apply qeq_imp_qle. exact Hab.
Qed.

(* QltT 双端 Qeq 传输 *)
Lemma z2s_ltT_wd : forall a b c d : Q,
  a == c -> b == d -> QltT a b -> QltT c d.
Proof.
  intros a b c d Hac Hbd H. apply (z2s_qeq_ltT_r b d c Hbd).
  apply (z2s_qeq_ltT a c b Hac). exact H.
Qed.

(* 右加正常数保持严格小于：0 < b ⟹ a < a + b *)
Lemma z2s_lt_plus_pos : forall a b : Q, QltT 0 b -> QltT a (a + b).
Proof.
  intros a b Hb. apply (z2s_qeq_ltT_r (b + a) (a + b) a).
  - apply Qplus_comm.
  - apply (z2s_qeq_ltT (0 + a) a (b + a)).
    + apply Qplus_0_l.
    + apply Qlt_to_QltT. apply (proj2 (Qplus_lt_l 0 b a)).
      apply QltT_to_Qlt. exact Hb.
Qed.

(* QltT 右加相容：a < b ⟹ a + c < b + c *)
Lemma z2s_ltT_plus_compat_r : forall a b c : Q,
  QltT a b -> QltT (a + c) (b + c).
Proof.
  intros a b c H. apply Qlt_to_QltT.
  apply (proj2 (Qplus_lt_l a b c)). apply QltT_to_Qlt. exact H.
Qed.

(* 从和的严格小于中舍弃右侧正常项：(a + b) < (c + d)、0 < b ⟹ a < c + d *)
Lemma z2s_lt_drop_pos : forall a b c d : Q,
  QltT (a + b) (c + d) -> QltT 0 b -> QltT a (c + d).
Proof.
  intros a b c d H Hb.
  apply (z2s_ltT_trans a (a + b) (c + d)).
  - apply (z2s_lt_plus_pos a b). exact Hb.
  - exact H.
Qed.

(* ------------------------------------------------------------ *)
(* §6.1 伸缩分裂与部分和的尾界/有界/Cauchy 模量                             *)
(* ------------------------------------------------------------ *)

(* 分裂恒等式的 Z 域承载：0 < a、b == a + 1 ⟹
   1/b + 1/(a·b) == 1/a。倒数定义依分子符号构造逐例消解，
   消解后为单变量的多项式恒等式。 *)
Lemma z2s_qeq_split : forall a b : Z, (0 < a)%Z -> (b = a + 1)%Z ->
  1 / (b # 1)%Q + 1 / ((a * b) # 1)%Q == 1 / (a # 1)%Q.
Proof.
  intros a b Ha Hab.
  destruct a as [|pa|pa].
  - exfalso. exact (Z.lt_irrefl 0 Ha).
  - destruct b as [|pb|pb].
    + exfalso. lia.
    + assert (Hpd : (0 < Z.pos pa * Z.pos pb)%Z) by apply Pos2Z.is_pos.
      destruct (Z.pos pa * Z.pos pb)%Z as [|pd|pd] eqn:Epd.
      * exfalso. exact (Z.lt_irrefl _ Hpd).
      * unfold Qdiv, Qeq. cbn. nia.
      * exfalso. lia.
    + assert (Hpb := Pos2Z.is_pos pb).
      change (Z.neg pb) with (- Z.pos pb)%Z in Hab. exfalso. lia.
  - assert (Hpa := Pos2Z.is_pos pa).
    change (Z.neg pa) with (- Z.pos pa)%Z in Ha. exfalso. lia.
Qed.

(* 倒数比较的 Z 域承载：0 < a、0 < b、a < b ⟹
   1/b² < 1/(a·b)（对偶形交义乘读法，交义乘后归为 a < b）。 *)
Lemma z2s_qinv_pair_lt : forall a b : Z, (0 < a)%Z -> (0 < b)%Z -> (a < b)%Z ->
  QltT (1 / ((b # 1) * (b # 1))%Q) (1 / ((a * b) # 1)%Q).
Proof.
  intros a b Ha Hb Hab.
  destruct a as [|pa|pa].
  - exfalso. exact (Z.lt_irrefl 0 Ha).
  - destruct b as [|pb|pb].
    + exfalso. exact (Z.lt_irrefl 0 Hb).
    + apply Qlt_to_QltT. unfold Qdiv, Qlt. cbn [Qmult Qnum Qden].
      assert (Hpc : (0 < Z.pos pb * Z.pos pb)%Z) by apply Pos2Z.is_pos.
      assert (Hpd : (0 < Z.pos pa * Z.pos pb)%Z) by apply Pos2Z.is_pos.
      destruct (Z.pos pb * Z.pos pb)%Z as [|pc|pc] eqn:Epc.
      * exfalso. exact (Z.lt_irrefl _ Hpc).
      * destruct (Z.pos pa * Z.pos pb)%Z as [|pd|pd] eqn:Epd.
        -- exfalso. exact (Z.lt_irrefl _ Hpd).
        -- cbn. nia.
        -- exfalso. lia.
      * exfalso. lia.
    + assert (Hpb := Pos2Z.is_pos pb).
      change (Z.neg pb) with (- Z.pos pb)%Z in Hb. exfalso. lia.
  - assert (Hpa := Pos2Z.is_pos pa).
    change (Z.neg pa) with (- Z.pos pa)%Z in Ha. exfalso. lia.
Qed.

(* 伸缩分裂恒等式：1/j == 1/(j+1) + 1/(j(j+1))（j = S k）。
   Z 域分裂承载件（z2s_qeq_split）的直接实例。 *)
Lemma z2s_inv_split : forall k : nat,
  1 / (Z.of_nat (Datatypes.S k) # 1)%Q
  == 1 / (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q
     + 1 / ((Z.of_nat (Datatypes.S k)
             * Z.of_nat (Datatypes.S (Datatypes.S k))) # 1)%Q.
Proof.
  intro k.
  assert (Ha : (0 < Z.of_nat (Datatypes.S k))%Z) by lia.
  assert (Hb : (Z.of_nat (Datatypes.S (Datatypes.S k))
                = Z.of_nat (Datatypes.S k) + 1)%Z).
  { rewrite !Nat2Z.inj_succ. lia. }
  exact (Qeq_sym _ _ (z2s_qeq_split _ _ Ha Hb)).
Qed.

(* 伸缩比较：级数项严格小于分裂项 1/(j(j+1))，即
   1/(j+1)² < 1/(j(j+1))，交义乘后归为 j < j+1 的严格序。 *)
Lemma z2s_term_lt_split : forall k : nat,
  QltT (z2s_term (Datatypes.S k))
       (1 / ((Z.of_nat (Datatypes.S k)
              * Z.of_nat (Datatypes.S (Datatypes.S k))) # 1)%Q).
Proof.
  intro k. unfold z2s_term.
  apply (z2s_qinv_pair_lt (Z.of_nat (Datatypes.S k))
                          (Z.of_nat (Datatypes.S (Datatypes.S k)))).
  - lia.
  - lia.
  - lia.
Qed.

(* 加法结合置换（原子级，实例化时不限项形）：t + (p + i) == (p + t) + i *)
Lemma z2s_qeq_rotate : forall p t i : Q, t + (p + i) == (p + t) + i.
Proof. intros p t i. ring. Qed.

(* 加法交换聚合置换（原子级）：p + (i + j) == j + (p + i) *)
Lemma z2s_qeq_swap : forall p i j : Q, p + (i + j) == j + (p + i).
Proof. intros p i j. ring. Qed.

(* 递减步：ps(j+1) + 1/(j+1) < ps(j) + 1/j（j = S k）。
   量 ps(j) + 1/j 随 j 严格递减——伸缩分裂恒等式的逐项读法。 *)
Lemma z2s_ps_step_lt : forall k : nat,
  QltT (z2s_ps (Datatypes.S (Datatypes.S k))
        + 1 / (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q)
       (z2s_ps (Datatypes.S k) + 1 / (Z.of_nat (Datatypes.S k) # 1)%Q).
Proof.
  intro k. assert (HU := z2s_ps_unfold (Datatypes.S k)).
  assert (HI := z2s_inv_split k).
  apply (z2s_ltT_wd
    (z2s_term (Datatypes.S k)
     + (z2s_ps (Datatypes.S k)
        + 1 / (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q))
    (1 / ((Z.of_nat (Datatypes.S k)
           * Z.of_nat (Datatypes.S (Datatypes.S k))) # 1)%Q
     + (z2s_ps (Datatypes.S k)
        + 1 / (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q))).
  - rewrite HU. apply z2s_qeq_rotate.
  - rewrite HI.
    rewrite (Qplus_comm (1 / ((Z.of_nat (Datatypes.S k)
              * Z.of_nat (Datatypes.S (Datatypes.S k))) # 1)%Q)
              (z2s_ps (Datatypes.S k)
               + 1 / (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q)).
    symmetry. apply Qplus_assoc.
  - apply z2s_ltT_plus_compat_r. exact (z2s_term_lt_split k).
Qed.

(* 递减不变量的 N 步形式：
   ps(S(M+N)) + 1/(S(M+N)) < ps(S M) + 1/(S M)（对 N 归纳）。 *)
Lemma z2s_ps_inv_dec : forall M N : nat,
  QltT (z2s_ps (Datatypes.S (M + Datatypes.S N))
        + 1 / (Z.of_nat (Datatypes.S (M + Datatypes.S N)) # 1)%Q)
       (z2s_ps (Datatypes.S M) + 1 / (Z.of_nat (Datatypes.S M) # 1)%Q).
Proof.
  intros M N. induction N as [| N IH].
  - rewrite Nat.add_1_r. apply z2s_ps_step_lt.
  - rewrite Nat.add_succ_r.
    apply (z2s_ltT_trans _
      (z2s_ps (Datatypes.S (M + Datatypes.S N))
       + 1 / (Z.of_nat (Datatypes.S (M + Datatypes.S N)) # 1)%Q)).
    + apply z2s_ps_step_lt.
    + exact IH.
Qed.

(* 尾界：ps(S M + N) − ps(S M) 的加法读法
   ps(S M + N) < ps(S M) + 1/(S M)——ζ(2) 部分和的几何收敛速率。 *)
Lemma z2s_ps_tail_lt : forall M N : nat,
  QltT (z2s_ps (Datatypes.S M + N))
       (z2s_ps (Datatypes.S M) + 1 / (Z.of_nat (Datatypes.S M) # 1)%Q).
Proof.
  intros M N. destruct N as [| N'].
  - rewrite Nat.add_0_r. apply z2s_lt_plus_pos. apply z2s_inv_pos.
  - apply (z2s_lt_drop_pos (z2s_ps (Datatypes.S M + Datatypes.S N'))
                           (1 / (Z.of_nat (Datatypes.S M + Datatypes.S N') # 1)%Q)).
    + exact (z2s_ps_inv_dec M N').
    + apply z2s_inv_pos.
Qed.

(* 有界性：全部部分和严格小于 2（M = 0 显然；M ≥ 1 由尾界于基 1 处）。 *)
Lemma z2s_ps_bounded : forall M : nat, QltT (z2s_ps M) (2 # 1)%Q.
Proof.
  intro M. destruct M as [| M'].
  - cbn [z2s_ps]. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (z2s_qeq_ltT_r
      (z2s_ps 1 + 1 / (Z.of_nat (Datatypes.S 0) # 1)%Q) (2 # 1)%Q
      (z2s_ps (Datatypes.S M'))).
    + vm_compute. reflexivity.
    + exact (z2s_ps_tail_lt 0 M').
Qed.

(* Cauchy 模量：基点 2^n = S(z2s_half_idx n) 之后任意多项的部分和
   与基点部分和之差严格小于 1/2^n——显式速率的 Cauchy 承载。 *)
Lemma z2s_cauchy_mod : forall n N : nat,
  QltT (z2s_ps (Datatypes.S (z2s_half_idx n) + N)%nat)
       (z2s_ps (Datatypes.S (z2s_half_idx n)) + z2s_half_pow n).
Proof.
  intros n N. exact (z2s_ps_tail_lt (z2s_half_idx n) N).
Qed.

(* 模量数值锚：z2s_half_pow 3 = 1/8 *)
Lemma z2s_half_pow_anchor : z2s_half_pow 3 == (1 # 8)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 尾舱：极限面主语句公理面自检                                        *)
(* ============================================================ *)

Print Assumptions z2s_inv_split.
Print Assumptions z2s_term_lt_split.
Print Assumptions z2s_ps_step_lt.
Print Assumptions z2s_ps_inv_dec.
Print Assumptions z2s_ps_tail_lt.
Print Assumptions z2s_ps_bounded.
Print Assumptions z2s_cauchy_mod.
Print Assumptions z2s_half_pow_anchor.
Print Assumptions z2s_inv_pos.
Print Assumptions z2s_ltT_trans.
Print Assumptions z2s_qeq_ltT.
Print Assumptions z2s_qeq_ltT_r.
Print Assumptions z2s_ltT_wd.
Print Assumptions z2s_lt_plus_pos.
Print Assumptions z2s_ltT_plus_compat_r.
Print Assumptions z2s_lt_drop_pos.

(* ============================================================ *)
(* §8 聚合面：段积分列的单一系数表达                                        *)
(* ============================================================ *)

(* 整族被积式 Σ_{m≤M} C(n+m,n)·x^{n+m}(1−x)^n·y^{n+m}(1−y)^n 的公共因子为      *)
(* (x(1−x))^n(y(1−y))^n，其外的全体有理系数按 (xy)^m 的位置折进一张系数表；      *)
(* 段 m 的因子表自次数 n+m 起，逐位相加时 Horner 位置随 m 顺移错开，此处以        *)
(* 位偏移 k 承载该错位。本节把段积分列（C(n+m,n)·B(n+m,n)² 结构）聚合为          *)
(* 单一系数表的整族积分和，并给出整族逐点值的单表读法。                        *)

From Stdlib Require Import Lists.List.

(* 单一系数表：整族积分和的全部有理系数 [C(n+m,n)]_{m<S M}（头为 m = 0 项） *)
Definition z2a_coes (n M : nat) : list Q :=
  map (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q) (seq 0 (Datatypes.S M)).

(* pint_eval 与 bkQ 同为一阶 Horner 折叠（空表给 0、cons 给 a + x·递归值），   *)
(* 二者逐表相等。                                                         *)
Lemma z2a_eval_bkQ : forall (l : list Q) (t : Q), pint_eval l t == bkQ l t.
Proof.
  intros l t. induction l as [| a l' IH].
  - reflexivity.
  - cbn [pint_eval bkQ]. rewrite IH. reflexivity.
Qed.

(* 单一系数表的 Horner 折叠值 == 族部分和 zb2_ps n M t：
   位置 m 上的系数 C(n+m,n) 携带 (xy)^m 的错位因子。 *)
Lemma z2a_coes_eval : forall (n M : nat) (t : Q),
  pint_eval (z2a_coes n M) t == zb2_ps n M t.
Proof.
  intros n M t. unfold z2a_coes, zb2_ps.
  rewrite z2a_eval_bkQ.
  exact (bkQ_seq_map M (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q) t).
Qed.

(* 整族逐点聚合面：段列逐点值 = 公共因子 (x(1−x))^n(y(1−y))^n × 单表折叠值。 *)
Corollary z2a_beval_agg : forall (n M : nat) (x y : Q),
  zb2_beval_l (zb2_segl n M) x y
  == q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n
     * pint_eval (z2a_coes n M) (x * y).
Proof.
  intros n M x y. rewrite z2a_coes_eval. exact (zb2_beval_segl n M x y).
Qed.

(* 位移段积分和：Σ_{m≤M} zb2_term n (k+m)，k 为表位偏移。 *)
Fixpoint z2a_IsumK (n k M : nat) : Q :=
  match M with
  | O => zb2_term n k
  | Datatypes.S M' => z2a_IsumK n k M' + zb2_term n (k + Datatypes.S M')
  end.

(* 错位聚合积分折叠：单表逐位系数乘位偏移 k 处因子表 [0,1] 积分值的平方；      *)
(* 位偏移 k 即段 m 因子表自次数 n+m 起的错位 Horner 位置。 *)
Fixpoint z2a_Ifrom (n : nat) (cs : list Q) (k : nat) : Q :=
  match cs with
  | nil => 0
  | c :: cs' =>
      c * pint_integral (pei_list (n + k) n) * pint_integral (pei_list (n + k) n)
      + z2a_Ifrom n cs' (Datatypes.S k)
  end.

(* 单项折叠：单元素表的积分折叠 = 系数 × 位偏移处因子表积分值平方。 *)
Lemma z2a_Ifrom_one : forall (n : nat) (c : Q) (k : nat),
  z2a_Ifrom n (c :: nil) k
  == c * pint_integral (pei_list (n + k) n) * pint_integral (pei_list (n + k) n).
Proof.
  intros n c k. cbn [z2a_Ifrom]. ring.
Qed.

(* 折叠的表接合：折叠 (cs ++ ds) k = 折叠 cs k + 折叠 ds (k + 长cs)——错位      *)
(* 位置随已折叠表长顺移。                                                 *)
Lemma z2a_Ifrom_app : forall (n : nat) (cs ds : list Q) (k : nat),
  z2a_Ifrom n (cs ++ ds) k
  == z2a_Ifrom n cs k + z2a_Ifrom n ds (k + length cs).
Proof.
  intros n cs. induction cs as [| c cs' IH]; intros ds k.
  - cbn [app length z2a_Ifrom]. rewrite Nat.add_0_r. ring.
  - cbn [app length z2a_Ifrom]. rewrite (IH ds (Datatypes.S k)).
    rewrite Nat.add_succ_r.
    change (Datatypes.S k + length cs')%nat with
      (Datatypes.S (k + length cs'))%nat. ring.
Qed.

(* 错位聚合主恒等式：单表在位偏移 k 的积分折叠 == 位移段积分和。
   表接合把 seq 0 (S (S M)) 拆为首段加末项，末项系数 C(n+S M+k,n) 落在        *)
(* 位偏移 k + S M 处，其因子表积分值即 B(n+(k+S M),n)。 *)
Lemma z2a_Ifrom_IsumK : forall (n M k : nat),
  z2a_Ifrom n
    (map (fun m => (Z.of_nat (bkC (n + m + k) n) # 1)%Q)
         (seq 0 (Datatypes.S M))) k
  == z2a_IsumK n k M.
Proof.
  intros n M. induction M as [| M IH]; intros k.
  - cbn [seq map z2a_Ifrom z2a_IsumK]. rewrite Nat.add_0_r.
    rewrite !pei_beta_value. unfold zb2_term. ring.
  - replace (seq 0 (Datatypes.S (Datatypes.S M)))
      with ((seq 0 (Datatypes.S M) ++ (Datatypes.S M :: nil))%list)
      by (rewrite (seq_S (Datatypes.S M) 0); reflexivity).
    rewrite map_app. rewrite z2a_Ifrom_app.
    rewrite map_length. rewrite seq_length.
    rewrite (IH k). cbn [map]. cbn [z2a_IsumK].
    rewrite z2a_Ifrom_one.
    replace (n + Datatypes.S M + k)%nat with (n + (k + Datatypes.S M))%nat by lia.
    rewrite !pei_beta_value. unfold zb2_term. ring.
Qed.

(* 零偏移特例：位移段积分和于 k = 0 即整族积分和 zb2_Isum n M。 *)
Lemma z2a_IsumK_zero : forall n M : nat, z2a_IsumK n 0 M == zb2_Isum n M.
Proof.
  intros n M. induction M as [| M IH].
  - reflexivity.
  - cbn [z2a_IsumK zb2_Isum]. rewrite Nat.add_0_l. rewrite IH. reflexivity.
Qed.

(* 整族积分聚合面主语句：段积分列的单一系数表表达——单表 z2a_coes n M 在       *)
(* 零偏移处的错位积分折叠 == 整族积分和 zb2_Isum n M。逐位系数 C(n+m,n) 与      *)
(* 位偏移因子表积分值 B(n+m,n) 的乘积结构，供后续整除性分析按位取用。          *)
Theorem z2a_agg_I : forall n M : nat,
  z2a_Ifrom n (z2a_coes n M) 0 == zb2_Isum n M.
Proof.
  intros n M. unfold z2a_coes. rewrite <- z2a_IsumK_zero.
  replace (map (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q)
               (seq 0 (Datatypes.S M)))
    with (map (fun m => (Z.of_nat (bkC (n + m + 0) n) # 1)%Q)
               (seq 0 (Datatypes.S M))).
  - exact (z2a_Ifrom_IsumK n M 0).
  - apply map_ext. intro a. rewrite Nat.add_0_r. reflexivity.
Qed.

(* 数值锚：单表积分折叠于 n = 0、M = 2 给 49/36（与部分和锚 z2s_ps_anchor3    *)
(* 及零权闭式项和锚 z2s_Isum_bridge_anchor 同值）。 *)
Lemma z2a_agg_anchor : z2a_Ifrom 0 (z2a_coes 0 2) 0 == (49 # 36)%Q.
Proof. rewrite z2a_agg_I. exact z2s_Isum_bridge_anchor. Qed.

(* 数值锚（定义性直算）：单表积分折叠于 n = 0、M = 2 直算同为 49/36。 *)
Lemma z2a_agg_anchor_compute : z2a_Ifrom 0 (z2a_coes 0 2) 0 == (49 # 36)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚：单表 Horner 折叠于 n = 1、M = 2、t = 1/3 给 2（表 [1;2;3] 折叠值）。 *)
Lemma z2a_coes_eval_anchor : pint_eval (z2a_coes 1 2) (1 # 3) == 2%Q.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚：整族逐点聚合于 n = 1、M = 1、x = y = 1/2 给 3/32。 *)
Lemma z2a_beval_agg_anchor :
  zb2_beval_l (zb2_segl 1 1) (1 # 2) (1 # 2) == (3 # 32)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §9 尾舱：聚合面语句公理面自检                                          *)
(* ============================================================ *)

Print Assumptions z2a_eval_bkQ.
Print Assumptions z2a_coes_eval.
Print Assumptions z2a_beval_agg.
Print Assumptions z2a_Ifrom_one.
Print Assumptions z2a_Ifrom_app.
Print Assumptions z2a_Ifrom_IsumK.
Print Assumptions z2a_IsumK_zero.
Print Assumptions z2a_agg_I.
Print Assumptions z2a_agg_anchor.
Print Assumptions z2a_agg_anchor_compute.
Print Assumptions z2a_coes_eval_anchor.
Print Assumptions z2a_beval_agg_anchor.

(* ============================================================ *)
(* §10 整性面：d²·I 方向的 Q/Z 层承载段                                    *)
(* ============================================================ *)

(* 记 d_K := hl_lcm_upto K（1..K 的最小公倍数，Hanson 上界件）。被积因子表      *)
(* pei_list a b 的系数全为整数：由 0/1 列表经 ±1 数乘、尾垫零与逐位加法生成，    *)
(* 其第 i 项 [0,1] 积分贡献 a_i/(i+1)，分母不超过 a+b+1，故                    *)
(* d_{a+b+1}·B(a,b) 为整数；逐位系数 C(n+m,n) 为自然数，缩放二次方后           *)
(* d_{2n+m+1}²·C·B(n+m,n)² 仍为整数；族和取公共尺度 K = S(n+(n+M)) 即覆盖       *)
(* 全体位偏移。本节给出该整除链的 Q/Z 承载段：z2i_Zq 为 Q 中"取整数值"的       *)
(* Set 面见证类型（Z 像等式 sig 型），主语句 z2i_d2_Isum 给出                  *)
(* d_{S(n+(n+M))}²·zb2_Isum n M 的整数见证，并经 z2a_agg_I 与聚合面衔接。     *)

Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_z2_valbridge.

(* Q 中"取整数值"的 Set 面见证类型：存在 Z 像使 x 等于该像的有理形。 *)
Definition z2i_Zq (x : Q) : Set := sig (fun z : Z => x == (z # 1)%Q).

(* 逐项余数谱聚合：各表项 Qnum 对 Qden 的 Z 余数取绝对值后折为 nat 和。       *)
(* 逐项非负，为零当且仅当全体表项取整数值。整除见证以该可算余数数据承载。      *)
Definition z2i_densum (l : list Q) : Z :=
  fold_right (fun (c : Q) (acc : Z) =>
               (Z.modulo (Qnum c) (Zpos (Qden c)) + acc)%Z) 0%Z l.

(* 整数系数表谓词：聚合余数谱零判据的 hl_id 承载（余数索引为可算数据）。 *)
Definition z2i_allZq (l : list Q) : Set := hl_id (z2i_densum l) 0%Z.

(* 整数值对加法封闭。 *)
Lemma z2i_Zq_add : forall x y : Q,
  z2i_Zq x -> z2i_Zq y -> z2i_Zq (x + y)%Q.
Proof.
  intros x y Hx Hy. destruct Hx as [a Ha]. destruct Hy as [b Hb].
  refine (exist _ (a + b)%Z _). rewrite Ha, Hb. unfold Qeq; cbn; ring.
Qed.

(* 同值传输：等值的有理数，其整数性见证可相互传输。 *)
Lemma z2i_Zq_transport : forall x y : Q,
  x == y -> z2i_Zq x -> z2i_Zq y.
Proof.
  intros x y Hxy [z Hz]. refine (exist _ z _).
  exact (Qeq_trans y x (z # 1) (Qeq_sym x y Hxy) Hz).
Qed.

(* Reverse-direction transport: along the same equation, witnesses can equally be transported in reverse. *)
Lemma z2i_Zq_transport_back : forall x y : Q,
  x == y -> z2i_Zq y -> z2i_Zq x.
Proof.
  intros x y Hxy [z Hz]. refine (exist _ z _).
  exact (Qeq_trans x y (z # 1) Hxy Hz).
Qed.

(* 有理整数（Z 像分母形）的 Set 面见证。 *)
Lemma z2i_Zq_whole : forall k : nat, z2i_Zq (Z.of_nat k # 1)%Q.
Proof.
  intro k. unfold z2i_Zq. refine (exist _ (Z.of_nat k) _).
  unfold Qeq. cbn [Qnum Qden]. ring.
Qed.

(* sig 见证向余数判据的换算：x 取整数值时 Qnum x 对 Qden x 的 Z 余数为零。 *)
Lemma z2i_Zq_mod : forall x : Q,
  z2i_Zq x -> Z.modulo (Qnum x) (Zpos (Qden x)) = 0%Z.
Proof.
  intros x [z Hz]. unfold Qeq in Hz. cbn [Qnum Qden] in Hz.
  change (Z.pos 1%positive) with 1%Z in Hz. rewrite Z.mul_1_r in Hz.
  rewrite Hz. apply Z_mod_mult.
Qed.

(* 单项余数非负：正除子的 Z 余数落在非负半轴。 *)
Lemma z2i_mod_nonneg : forall c : Q,
  (0 <= Z.modulo (Qnum c) (Zpos (Qden c)))%Z.
Proof.
  intro c. assert (Hp : (0 < Z.pos (Qden c))%Z) by apply Pos2Z.is_pos.
  exact (proj1 (Z.mod_pos_bound (Qnum c) (Zpos (Qden c)) Hp)).
Qed.

(* 聚合余数谱非负。 *)
Lemma z2i_densum_nonneg : forall l : list Q, (0 <= z2i_densum l)%Z.
Proof.
  intro l. induction l as [| c l' IH].
  - cbn [z2i_densum fold_right]. lia.
  - assert (Hc : z2i_densum (c :: l')
                  = (Z.modulo (Qnum c) (Zpos (Qden c)) + z2i_densum l')%Z)
      by reflexivity.
    rewrite Hc. assert (Hna := z2i_mod_nonneg c). lia.
Qed.

(* 聚合余数谱的逐项读入：首项 Z 商见证与尾表证书。 *)
Lemma z2i_allZq_consE : forall (c : Q) (l : list Q),
  z2i_allZq (c :: l) -> z2i_Zq c * z2i_allZq l.
Proof.
  intros c l H. unfold z2i_allZq in H. apply hl_id_eq in H.
  assert (Hcons : z2i_densum (c :: l)
                  = (Z.modulo (Qnum c) (Zpos (Qden c)) + z2i_densum l)%Z)
    by reflexivity.
  rewrite Hcons in H.
  assert (Hna := z2i_mod_nonneg c).
  assert (Hnb := z2i_densum_nonneg l).
  assert (Hs1 : Z.modulo (Qnum c) (Zpos (Qden c)) = 0%Z) by lia.
  assert (Hmd : Z.modulo (Qnum c) (Zpos (Qden c)) = 0%Z) by exact Hs1.
  assert (Hs2 : z2i_densum l = 0%Z) by lia.
  split.
  - unfold z2i_Zq. refine (exist _ ((Qnum c / Zpos (Qden c))%Z) _).
    assert (Hd0 : (Zpos (Qden c) <> 0)%Z).
    { assert (Hp := Pos2Z.is_pos (Qden c)). lia. }
    assert (Hq := Z_div_mod_eq_full (Qnum c) (Zpos (Qden c))).
    rewrite Hmd in Hq.
    assert (Hq2 : (Qnum c = Zpos (Qden c) * (Qnum c / Zpos (Qden c)))%Z) by lia.
    unfold Qeq. cbn [Qnum Qden]. change (Z.pos 1%positive) with 1%Z.
    rewrite Hq2 at 1. ring.
  - unfold z2i_allZq. rewrite Hs2. exact (hl_idrefl 0%Z).
Qed.

(* 聚合余数谱的逐项读出：首项见证与尾表证书装配整表证书。 *)
Lemma z2i_allZq_consI : forall (c : Q) (l : list Q),
  z2i_Zq c -> z2i_allZq l -> z2i_allZq (c :: l).
Proof.
  intros c l Hc Hl. unfold z2i_allZq. unfold z2i_allZq in Hl.
  apply hl_id_eq in Hl.
  assert (Hcr := z2i_Zq_mod c Hc).
  assert (Hcons : z2i_densum (c :: l)
                  = (Z.modulo (Qnum c) (Zpos (Qden c)) + z2i_densum l)%Z)
    by reflexivity.
  rewrite Hcons, Hcr, Hl.
  cbn [Z.add].
  exact (hl_idrefl 0%Z).
Qed.

(* 基座幂多项式表全程为整数系数表（表项 1/1 与 0/1 皆为 Z 像分母形）。 *)
Lemma z2i_allZq_pow_poly : forall k : nat, z2i_allZq (pint_pow_poly k).
Proof.
  intro k. induction k as [| k IH].
  - cbn [pint_pow_poly]. apply z2i_allZq_consI.
    + exact (z2i_Zq_whole 1).
    + exact (hl_idrefl 0%Z).
  - cbn [pint_pow_poly]. apply z2i_allZq_consI.
    + exact (z2i_Zq_whole 0).
    + exact IH.
Qed.

(* 尾垫零保持整数系数表。 *)
Lemma z2i_allZq_ztail : forall p : list Q,
  z2i_allZq p -> z2i_allZq (pei_ztail p).
Proof.
  intro p. unfold pei_ztail. induction p as [| c p' IH]; intro H.
  - cbn [app]. apply z2i_allZq_consI.
    + exact (z2i_Zq_whole 0).
    + exact (hl_idrefl 0%Z).
  - cbn [app]. destruct (z2i_allZq_consE c p' H) as [Hc Hp].
    apply z2i_allZq_consI.
    + exact Hc.
    + exact (IH Hp).
Qed.

(* (-1) 数乘的单项见证：整数值的 (-1) 数乘仍取整数值。 *)
Lemma z2i_Zq_scale_m1_entry : forall c : Q, z2i_Zq c -> z2i_Zq ((- 1)%Q * c)%Q.
Proof.
  intros c H. destruct H as [z Hz].
  assert (Ho1 : (- 1)%Q * c == (- 1)%Q * (z # 1)%Q).
  { apply (@Qmult_comp (- 1)%Q (- 1)%Q (Qeq_refl (- 1)%Q) c (z # 1)%Q Hz). }
  assert (Ho2 : (- 1)%Q * (z # 1)%Q == ((- z) # 1)%Q).
  { unfold Qeq. cbn [Qmult Qnum Qden Pos.mul].
    change (Zneg 1%positive) with (-1)%Z. change (Zpos 1%positive) with 1%Z. ring. }
  apply (z2i_Zq_transport_back _ _ (Qeq_trans _ _ _ Ho1 Ho2)).
  unfold z2i_Zq. refine (exist _ (- z)%Z _).
  exact (Qeq_refl ((- z) # 1)%Q).
Qed.

(* (-1) 数乘保持整数系数表。 *)
Lemma z2i_allZq_scale_m1 : forall p : list Q,
  z2i_allZq p -> z2i_allZq (pint_scale (- 1)%Q p).
Proof.
  intro p. induction p as [| c p' IH]; intro H.
  - exact (hl_idrefl 0%Z).
  - cbn [pint_scale]. destruct (z2i_allZq_consE c p' H) as [Hc Hp].
    apply z2i_allZq_consI.
    + exact (z2i_Zq_scale_m1_entry c Hc).
    + exact (IH Hp).
Qed.

(* 逐位加法保持整数系数表。 *)
Lemma z2i_allZq_add : forall p q : list Q,
  z2i_allZq p -> z2i_allZq q -> z2i_allZq (pint_add p q).
Proof.
  intros p. induction p as [| a p' IH]; intros q Hpq Hqq.
  - exact Hqq.
  - destruct q as [| b q'].
    + exact Hpq.
    + destruct (z2i_allZq_consE a p' Hpq) as [Ha Hp'].
      destruct (z2i_allZq_consE b q' Hqq) as [Hb Hq'].
      cbn [pint_add]. apply z2i_allZq_consI.
      * exact (z2i_Zq_add a b Ha Hb).
      * exact (IH q' Hp' Hq').
Qed.

(* 因子表 pei_list a b 全程为整数系数表（0/1 经 ±1 数乘、尾垫零与逐位加法）。 *)
Lemma z2i_allZq_pei : forall a b : nat, z2i_allZq (pei_list a b).
Proof.
  intros a b. revert a. induction b as [| b' IH]; intro a.
  - apply z2i_allZq_pow_poly.
  - cbn [pei_list]. apply z2i_allZq_add.
    + apply z2i_allZq_ztail. apply IH.
    + apply z2i_allZq_scale_m1. apply IH.
Qed.

(* 整除链缩放主语句：整数系数表在起始偏移 k 的逐项积分和，其全体分母          *)
(* (k+i+1) 不超过 K 时，d_K 缩放后取整数值。归纳步对首项以                    *)
(* hl_lcm_divide_all 取 (k+1) 整除 d_K 的商，交义乘积比对闭合。              *)
Lemma z2i_lcm_scale_from : forall (l : list Q) (k K : nat),
  (k + length l <= K)%nat ->
  z2i_allZq l ->
  z2i_Zq ((Z.of_nat (hl_lcm_upto K) # 1)%Q * pint_integral_from l k).
Proof.
  intros l. induction l as [| c l' IH]; intros k K Hlen Hall.
  - refine (exist _ 0%Z _). rewrite Qmult_0_r. reflexivity.
  - destruct (z2i_allZq_consE c l' Hall) as [Hc Hl'].
    destruct Hc as [a Ha].
    cbn [length pint_integral_from pint_monomial_int].
    assert (Hqz2 : ((Z.of_nat (hl_lcm_upto K) # 1)%Q *
             (c / (Z.of_nat (Datatypes.S k) # 1)%Q +
              pint_integral_from l' (Datatypes.S k))) == ((Z.of_nat (hl_lcm_upto K) # 1)%Q *
            (c / (Z.of_nat (Datatypes.S k) # 1)%Q) +
            (Z.of_nat (hl_lcm_upto K) # 1)%Q *
            pint_integral_from l' (Datatypes.S k))%Q) by ring.
    apply (z2i_Zq_transport_back _ _ Hqz2).
    apply z2i_Zq_add.
      assert (H1 : (1 <= Datatypes.S k)%nat) by lia.
      assert (H2 : (Datatypes.S k <= K)%nat) by (cbn [length] in Hlen; lia).
      refine (exist _ (Z.of_nat (Nat.div (hl_lcm_upto K) (Datatypes.S k)) * a)%Z _).
      rewrite Ha.
      destruct (hl_lcm_divide_all K (Datatypes.S k) H1 H2) as [q Hq].
      rewrite Hq. rewrite Nat2Z.inj_mul.
      rewrite (Nat.div_mul q (Datatypes.S k)) by lia.
      unfold Qdiv, Qeq. cbn. ring.
    + apply IH with (K := K).
      * (cbn [length] in Hlen; lia).
      * exact Hl'.
Qed.

(* 二次缩放闭合：d·B 取整数值时，d²·C·B·B 对任意整数像 C 取整数值——          *)
(* d 的因子经 d·B 的整数见证吸收。 *)
Lemma z2i_sq_bit : forall (B : Q) (d : nat) (C : Z),
  z2i_Zq ((Z.of_nat d # 1)%Q * B) ->
  z2i_Zq ((Z.of_nat d # 1)%Q *
          ((Z.of_nat d # 1)%Q * ((C # 1)%Q * B * B))).
Proof.
  intros B d C H. destruct H as [a Ha].
  refine (exist _ (C * (a * a))%Z _).
  assert (Hqz : ((Z.of_nat d # 1)%Q *
           ((Z.of_nat d # 1)%Q * ((C # 1)%Q * B * B))) ==
          ((C # 1)%Q *
          (((Z.of_nat d # 1)%Q * B) * ((Z.of_nat d # 1)%Q * B)))%Q) by ring.
  rewrite Hqz. rewrite Ha. unfold Qeq; cbn; ring.
Qed.

(* 分母谱链的 Set 面形态：i 不超过 K 时 d_i 整除 d_K（mod 零判据，与          *)
(* abl_z2_valbridge 之 z2v_dvd_t 同承载 hl_id）。 *)
Lemma z2i_lcm_chain_t : forall i K : nat,
  (1 <= i)%nat -> (i <= K)%nat ->
  z2v_dvd_t (hl_lcm_upto i) (hl_lcm_upto K).
Proof.
  intros i K Hi HK. unfold z2v_dvd_t.
  assert (H1 : (1 <= hl_lcm_upto i)%nat) by apply h3_lcm_pos.
  assert (Hdv : forall K' : nat, (i <= K')%nat ->
                Nat.divide (hl_lcm_upto i) (hl_lcm_upto K')).
  { induction K' as [| K' IHK]; intro Hle.
    - assert (Hiz : (i = 0)%nat) by lia.
      rewrite Hiz. exists 1%nat. symmetry. apply Nat.mul_1_l.
    - destruct (Nat.eq_dec i (Datatypes.S K')) as [Heq | Hne].
      + subst i. exists 1%nat. symmetry. apply Nat.mul_1_l.
      + cbn [hl_lcm_upto].
        apply (hl_div_trans (hl_lcm_upto i) (hl_lcm_upto K')
                 (Nat.lcm (hl_lcm_upto K') (Datatypes.S K'))).
        * apply IHK. lia.
        * apply Nat.divide_lcm_l. }
  rewrite (pr_dvd_mod0 (hl_lcm_upto i) (hl_lcm_upto K) H1 (Hdv K HK)).
  apply hl_idrefl.
Qed.

(* 单表逐位的 d 缩放整数值：K 不小于 S(n+(n+m)) 时 d_K·B(n+m,n) 取整数值。 *)
Lemma z2i_d_bit : forall n m K : nat,
  (Datatypes.S (n + (n + m)) <= K)%nat ->
  z2i_Zq ((Z.of_nat (hl_lcm_upto K) # 1)%Q *
          pint_integral (pei_list (n + m) n)).
Proof.
  intros n m K HK. apply (z2i_lcm_scale_from (pei_list (n + m) n) 0 K).
  - unfold pint_integral. rewrite pei_list_length. lia.
  - apply z2i_allZq_pei.
Qed.

(* 错位折叠的公共尺度整除链：K 不小于 S(n+(n+M)) 时                          *)
(* d_K²·z2a_Ifrom n (z2a_coes n M) 0 取整数值——首段归纳加末位单项，           *)
(* 位偏移随已折叠表长顺移，全体分母谱被同一 d_K 覆盖。 *)
Lemma z2i_d2_fold_K : forall (n M K : nat),
  (Datatypes.S (n + (n + M)) <= K)%nat ->
  z2i_Zq ((Z.of_nat (hl_lcm_upto K) # 1)%Q *
          ((Z.of_nat (hl_lcm_upto K) # 1)%Q *
           z2a_Ifrom n (z2a_coes n M) 0)).
Proof.
  intros n M. induction M as [| M' IH]; intros K HK.
  - unfold z2a_coes. cbn [seq map].
    apply (z2i_Zq_transport_back _ _
             (@Qmult_comp _ _
                         (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                         (@Qmult_comp _ _
                                     (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                                     (z2a_Ifrom_one n
                                                     (Z.of_nat (bkC (n + 0) n) # 1)%Q
                                                     0)))).
    apply (z2i_sq_bit _ (hl_lcm_upto K) (Z.of_nat (bkC (n + 0) n))).
    apply (z2i_d_bit n 0 K). exact HK.
  - unfold z2a_coes.
    replace (seq 0 (Datatypes.S (Datatypes.S M')))
      with ((seq 0 (Datatypes.S M') ++ (Datatypes.S M' :: nil))%list)
      by (rewrite (seq_S (Datatypes.S M') 0); reflexivity).
    rewrite map_app.
    apply (z2i_Zq_transport_back _ _
             (@Qmult_comp _ _ (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                         (@Qmult_comp _ _ (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                                     (z2a_Ifrom_app n _ _ 0)))).
    rewrite map_length.
    rewrite seq_length. rewrite Nat.add_0_l.
    apply (z2i_Zq_transport_back _ _
             (@Qmult_comp _ _ (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                         (@Qmult_comp _ _ (Qeq_refl ((Z.of_nat (hl_lcm_upto K) # 1)%Q)) _ _
                                     (@Qplus_comp _ _
                                         (Qeq_refl (z2a_Ifrom n
                                             (map (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q)
                                                  (seq 0 (Datatypes.S M'))) 0)) _ _
                                         (z2a_Ifrom_one n
                                             (Z.of_nat (bkC (n + Datatypes.S M') n) # 1)%Q
                                             (Datatypes.S M')))))).
    assert (Hdist : (Z.of_nat (hl_lcm_upto K) # 1)%Q *

      ((Z.of_nat (hl_lcm_upto K) # 1)%Q *

      (z2a_Ifrom n

         (map (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q)

              (seq 0 (Datatypes.S M'))) 0 +

      (Z.of_nat (bkC (n + Datatypes.S M') n) # 1)%Q *

      pint_integral (pei_list (n + Datatypes.S M') n) *

      pint_integral (pei_list (n + Datatypes.S M') n))) ==

      (Z.of_nat (hl_lcm_upto K) # 1)%Q *

      ((Z.of_nat (hl_lcm_upto K) # 1)%Q *

      z2a_Ifrom n

         (map (fun m => (Z.of_nat (bkC (n + m) n) # 1)%Q)

              (seq 0 (Datatypes.S M'))) 0) +

      (Z.of_nat (hl_lcm_upto K) # 1)%Q *

      ((Z.of_nat (hl_lcm_upto K) # 1)%Q *

      ((Z.of_nat (bkC (n + Datatypes.S M') n) # 1)%Q *

      pint_integral (pei_list (n + Datatypes.S M') n) *

      pint_integral (pei_list (n + Datatypes.S M') n)))) by ring.


    apply (z2i_Zq_transport_back _ _ Hdist).
    apply z2i_Zq_add.
    + apply IH. lia.
    + apply (z2i_sq_bit _ (hl_lcm_upto K) (Z.of_nat (bkC (n + Datatypes.S M') n))).
      apply (z2i_d_bit n (Datatypes.S M') K). exact HK.
Qed.

(* 整性面主语句：d_{S(n+(n+M))}²·zb2_Isum n M 取整数值——经聚合面主恒等式      *)
(* z2a_agg_I 与错位折叠的整除链衔接。 *)
Theorem z2i_d2_Isum : forall n M : nat,
  z2i_Zq ((Z.of_nat (hl_lcm_upto (Datatypes.S (n + (n + M)))) # 1)%Q *
          ((Z.of_nat (hl_lcm_upto (Datatypes.S (n + (n + M)))) # 1)%Q *
           zb2_Isum n M)).
Proof.
  intros n M.
  apply (z2i_Zq_transport _ _
           (@Qmult_comp _ _
                       (Qeq_refl (Z.of_nat (hl_lcm_upto (Datatypes.S (n + (n + M)))) # 1)%Q) _ _
                       (@Qmult_comp _ _
                                   (Qeq_refl (Z.of_nat (hl_lcm_upto (Datatypes.S (n + (n + M)))) # 1)%Q) _ _
                                   (z2a_agg_I n M)))).
  apply z2i_d2_fold_K. apply le_n.
Qed.

(* 数值锚：d_3·B(1,1) = 6·1/6 = 1。 *)
Lemma z2i_d_B_anchor : (Z.of_nat (hl_lcm_upto 3) # 1)%Q *
  pint_integral (pei_list 1 1) == (1 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 数值锚：d_4²·zb2_Isum 1 1 = 144·1/24 = 6。 *)
Lemma z2i_d2_Isum_anchor : (Z.of_nat (hl_lcm_upto 4) # 1)%Q *
  ((Z.of_nat (hl_lcm_upto 4) # 1)%Q * zb2_Isum 1 1) == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §11 尾舱：整性面语句公理面自检                                         *)
(* ============================================================ *)

Print Assumptions z2i_Zq_add.
Print Assumptions z2i_allZq_pow_poly.
Print Assumptions z2i_allZq_ztail.
Print Assumptions z2i_allZq_scale_m1.
Print Assumptions z2i_allZq_add.
Print Assumptions z2i_allZq_pei.
Print Assumptions z2i_lcm_scale_from.
Print Assumptions z2i_sq_bit.
Print Assumptions z2i_lcm_chain_t.
Print Assumptions z2i_d_bit.
Print Assumptions z2i_d2_fold_K.
Print Assumptions z2i_d2_Isum.
Print Assumptions z2i_d_B_anchor.
Print Assumptions z2i_d2_Isum_anchor.

Print Assumptions z2i_mod_nonneg.
Print Assumptions z2i_densum_nonneg.
Print Assumptions z2i_Zq_whole.
Print Assumptions z2i_Zq_mod.
Print Assumptions z2i_allZq_consE.
Print Assumptions z2i_allZq_consI.
Print Assumptions z2i_Zq_scale_m1_entry.
(* ============================================================ *)
(* §12 过渡面：被积族逐点界到积分界的传送                                *)
(*                                                                    *)
(*   数学内容：截断被积族在 [0,1]^2 上的逐点上界（逐点衰减面             *)
(*   zb2_dc_carrier_decay 供给 F <= (1/4)(1/10)^m）传送到段列积分和      *)
(*   的对应上界 zb2_di_l <= w。传送的唯一数学内核是单变量多项式          *)
(*   定积分对逐点序的单调性（点态控制到积分控制的正线性泛函步），        *)
(*   本节将该内核以显式前提位形式隔离（z2t_di_l_le 第一前提），           *)
(*   其余环节全部构造性闭合：y 向已积系数表 z2t_gyint 与 x 向已积        *)
(*   系数表 z2t_gtab 的一对求值/积分互咬恒等式（z2t_gyint_eval、        *)
(*   z2t_gyint_integral）把二重积分的逐点控制归约为该内核的两次          *)
(*   应用；z2t_const_int 给出常函数积分恒等于权重自身的单位面。          *)
(*   主定理 z2t_Isum_le_weight 取用逐点衰减面并产出积分上界，           *)
(*   z2t_sep_small_core 供给整性分离主定理的积分上界前提槽。            *)
(*   数值锚（有理数预演一致）：zb2_Isum 1 2 = 59/1200 < 1/4，           *)
(*   zb2_Isum 2 2 = 439/176400 < 1/40。                                *)
(* ============================================================ *)

Require Import abl_z2_decay.

(* 单项式积分值的加法线性：pint_monomial_int (a+b) k = a 档 + b 档。      *)
Lemma z2t_mono_int_add : forall (a b : Q) (k : nat),
  pint_monomial_int (a + b) k == pint_monomial_int a k + pint_monomial_int b k.
Proof.
  intros a b k. unfold pint_monomial_int.
  apply pint_div_add_distr.
Qed.

(* 积分加法线性性（零垫求值语义自洽，无等长前提）：                        *)
(*   两多项式按系数表相加后的积分 = 积分之和。先证偏移形式。              *)
Lemma z2t_pint_add_from : forall (p q : list Q) (k : nat),
  pint_integral_from (pint_add p q) k
  == pint_integral_from p k + pint_integral_from q k.
Proof.
  intro p. induction p as [| a p' IH]; intros q k.
  - cbn [pint_add pint_integral_from]. ring.
  - cbn [pint_add]. destruct q as [| b q'].
    + cbn [pint_integral_from]. ring.
    + cbn [pint_integral_from]. rewrite z2t_mono_int_add.
      rewrite (IH q' (Datatypes.S k)). ring.
Qed.

(* 零偏移组装面。 *)
Lemma z2t_pint_add : forall p q : list Q,
  pint_integral (pint_add p q) == pint_integral p + pint_integral q.
Proof.
  intros p q. unfold pint_integral. apply z2t_pint_add_from.
Qed.

(* 单位面恒等式：常函数 w 在 [0,1] 上的定积分 = w。逐点前提中的          *)
(*   权重 w 由此取得面积权读数（两次单积分的单位面）。                    *)
Lemma z2t_const_int : forall w : Q,
  pint_integral (pint_scale w (pint_pow_poly 0)) == w.
Proof.
  intro w.
  assert (Hs := qeqT_imp_qeq _ _ (pint_integral_scale w (pint_pow_poly 0))).
  assert (H1 := qeqT_imp_qeq _ _ (pint_integral_one)).
  rewrite Hs. rewrite H1. apply Qmult_1_r.
Qed.

(* y 向已积系数表：段列在固定 x 处作为 y 的多项式的系数表。               *)
(*   第 s 段贡献 = 段系数 * x 因子表在 x 处的值，缩放 y 因子表。          *)
Fixpoint z2t_gyint (l : list zb2_seg) (x : Q) : list Q :=
  match l with
  | nil => nil
  | s :: l' =>
      pint_add (pint_scale (fst s * pint_eval (fst (snd s)) x) (snd (snd s)))
               (z2t_gyint l' x)
  end.

(* x 向已积系数表：段列先对 y 积分后的 x 多项式系数表（逐段 zb2_yint     *)
(*   之和）。                                                           *)
Fixpoint z2t_gtab (l : list zb2_seg) : list Q :=
  match l with
  | nil => nil
  | s :: l' => pint_add (zb2_yint s) (z2t_gtab l')
  end.

(* y 向表求值恒等式：y 向系数表在 y 处的值 = 段列在 (x,y) 处的值。        *)
(*   两次线性（求值对加法与数乘）交换的直写。                            *)
Lemma z2t_gyint_eval : forall (l : list zb2_seg) (x y : Q),
  pint_eval (z2t_gyint l x) y == zb2_beval_l l x y.
Proof.
  intro l. induction l as [| s l' IH]; intros x y.
  - reflexivity.
  - cbn [z2t_gyint zb2_beval_l].
    rewrite pei_eval_add. rewrite pei_eval_scale. rewrite IH.
    unfold zb2_beval. cbn [fst snd]. ring.
Qed.

(* 两向互咬恒等式：y 向表的积分 = x 向表的逐点值。二重积分按两次单       *)
(*   积分的线性核交换，与 Fubini 型换序的代数骨架一致（免交换次序引理）。 *)
Lemma z2t_gyint_integral : forall (l : list zb2_seg) (x : Q),
  pint_integral (z2t_gyint l x) == pint_eval (z2t_gtab l) x.
Proof.
  intro l. induction l as [| s l' IH]; intro x.
  - reflexivity.
  - cbn [z2t_gyint z2t_gtab].
    rewrite z2t_pint_add.
    assert (Hs1 := qeqT_imp_qeq _ _
             (pint_integral_scale (fst s * pint_eval (fst (snd s)) x)
                                  (snd (snd s)))).
    rewrite Hs1. rewrite IH.
    rewrite pei_eval_add.
    unfold zb2_yint. rewrite pei_eval_scale. cbn [fst snd]. ring.
Qed.

(* 段列积分和 = x 向表的积分（定义面直接衔接）。                          *)
Lemma z2t_di_l_gtab : forall l : list zb2_seg,
  zb2_di_l l == pint_integral (z2t_gtab l).
Proof.
  intro l. induction l as [| s l' IH].
  - reflexivity.
  - cbn [zb2_di_l z2t_gtab]. unfold zb2_di.
    rewrite IH. rewrite <- z2t_pint_add. reflexivity.
Qed.

(* 传送主定理：逐点界到段列积分和。第一前提为单变量定积分对逐点序         *)
(*   单调性的显式前提位（点态控制到积分控制的内核，按 w 实例化）；        *)
(*   第二前提为段列逐点界。结论由内核的两次应用闭合：先对 y 向固定        *)
(*   x 应用，再对 x 向应用。                                            *)
Theorem z2t_di_l_le : forall (l : list zb2_seg) (w : Q),
  (forall p : list Q,
     (forall x : Q, 0 <= x -> x <= 1 -> pint_eval p x <= w) ->
     pint_integral p <= w) ->
  (forall x y : Q, 0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
     zb2_beval_l l x y <= w) ->
  QleT' (zb2_di_l l) w.
Proof.
  intros l w core Hpt.
  assert (Hy : forall x : Q,
             0 <= x -> x <= 1 -> pint_integral (z2t_gyint l x) <= w).
  { intros x Hx1 Hx2. apply core. intros y Hy1 Hy2.
    rewrite z2t_gyint_eval. apply Hpt; assumption. }
  assert (Hx : forall x : Q,
             0 <= x -> x <= 1 -> pint_eval (z2t_gtab l) x <= w).
  { intros x Hx1 Hx2. rewrite <- z2t_gyint_integral. apply Hy; assumption. }
  apply Qle_to_QleT'. rewrite z2t_di_l_gtab. apply core. exact Hx.
Qed.

(* 积分上界主定理：截断被积族段列积分和 <= 逐点权。逐点侧由逐点衰减       *)
(*   面 zb2_dc_carrier_decay 供给（指数 n = m+1 档在 [0,1]^2 逐点        *)
(*   <= (1/4)(1/10)^m）；段列积分和与逐点求值的衔接由 itg_carrier 的     *)
(*   段列积分恒等式 zb2_di_l_segl 供给。唯一余留前提为单变量积分         *)
(*   单调内核。                                                         *)
Theorem z2t_Isum_le_weight : forall (m M : nat),
  (forall p : list Q,
     (forall x : Q, 0 <= x -> x <= 1 ->
        pint_eval p x <= (1 # 4) * q_pow (1 # 10) m) ->
     pint_integral p <= (1 # 4) * q_pow (1 # 10) m) ->
  QleT' (zb2_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 10) m).
Proof.
  intros m M core.
  apply Qle_to_QleT'.
  rewrite <- (zb2_di_l_segl (Datatypes.S m) M).
  apply (QleT'_to_Qle (zb2_di_l (zb2_segl (Datatypes.S m) M))
                       ((1 # 4) * q_pow (1 # 10) m)).
  apply (z2t_di_l_le _ ((1 # 4) * q_pow (1 # 10) m) core).
  intros x y Hx1 Hx2 Hy1 Hy2.
  apply QleT'_to_Qle.
  exact (zb2_dc_carrier_decay m M x y Hx1 Hx2 Hy1 Hy2).
Qed.

(* 合拢推论：整性分离主定理（显式前提形式 zb2_dc_sep_small）的积分       *)
(*   上界前提位由本节供给；权重 w 取 (1/4)(1/10)^m。分离链余留的独立     *)
(*   前提为单变量积分单调内核与除子上界 d <= 3^(m+1)。                   *)
Corollary z2t_sep_small_core : forall (m M : nat) (d : Q),
  (forall p : list Q,
     (forall x : Q, 0 <= x -> x <= 1 ->
        pint_eval p x <= (1 # 4) * q_pow (1 # 10) m) ->
     pint_integral p <= (1 # 4) * q_pow (1 # 10) m) ->
  (8 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QltT (d * d * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d core Hm Hd0 Hd.
  apply (zb2_dc_sep_small m M d Hm Hd0 Hd).
  apply (z2t_Isum_le_weight m M).
  exact core.
Qed.

(* 数值锚（n = 1, M = 2）：段积分和 = 59/1200。                          *)
Lemma z2t_anchor_Isum_1_2 : zb2_Isum 1 2 == (59 # 1200)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 过渡不等式两侧锚（n = 1 档，权 = 1/4）：59/1200 < 1/4。               *)
Lemma z2t_anchor_le_1_2 : QltT (zb2_Isum 1 2) (1 # 4)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

(* 数值锚（n = 2, M = 2）：段积分和 = 439/176400。                       *)
Lemma z2t_anchor_Isum_2_2 : zb2_Isum 2 2 == (439 # 176400)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 过渡不等式两侧锚（n = 2 档，权 = 1/40）：439/176400 < 1/40。          *)
Lemma z2t_anchor_le_2_1 : QltT (zb2_Isum 2 2) (1 # 40)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §13 尾舱：过渡面语句公理面自检                                        *)
(* ============================================================ *)

Print Assumptions z2t_pint_add_from.
Print Assumptions z2t_pint_add.
Print Assumptions z2t_const_int.
Print Assumptions z2t_gyint_eval.
Print Assumptions z2t_gyint_integral.
Print Assumptions z2t_di_l_gtab.
Print Assumptions z2t_di_l_le.
Print Assumptions z2t_Isum_le_weight.
Print Assumptions z2t_sep_small_core.
Print Assumptions z2t_anchor_Isum_1_2.
Print Assumptions z2t_anchor_le_1_2.
Print Assumptions z2t_anchor_Isum_2_2.
Print Assumptions z2t_anchor_le_2_1.
