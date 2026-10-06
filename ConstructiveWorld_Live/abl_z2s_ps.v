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
