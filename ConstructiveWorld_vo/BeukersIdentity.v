(* ============================================================ *)
(* BeukersIdentity.v —— 切片代理E（批次 E-STAGING-D016，20260918）     *)
(* P2 恒等式主体首攻切片：Beukers 恒等式的可证最强切片（bi_ 前缀）。    *)
(*                                                                 *)
(* 【勘误定谳（本席手算 n=0,1,2 验证，机器见证见 §D/§E）】              *)
(* T97 §1.1 所引恒等式                                                *)
(*     ln2 − x'_n == 2^{−(2n+1)}·I_n/Q_n(1/2)²                        *)
(* 有两处缺陷：                                                       *)
(*  ① 分母 Q_n(1/2)² 应为 Q_n(1/2)。真恒等式（数值验证）为：            *)
(*       I_n := ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt                         *)
(*            = 2^{n+1}·q̃_n·ln2 − r_n，  r_n ∈ Q（r: 0, 8, 72）        *)
(*       ln2 − x'_n = I_n/(2^{n+1}·q̃_n) = 2^{−(2n+1)}·I_n/Q_n(1/2)     *)
(*    其中 q̃_n = 2^n·Q_n(1/2) = Σ_k C(n,k)²2^{n−k}（BeukersLists        *)
(*    bk_Qn_qtilde 在册）。比较两侧 ln2 系数：LHS 系数 = 1，若原形      *)
(*    成立则强迫 Q_n(1/2) == 1；而 n≥1 时 Q_n(1/2) ≥ (3/2)^n > 1       *)
(*    （本件 bi_Qn_half_gt1 定谳），平方分离见证 bi_square_disc。       *)
(*  ② x'_n 的谐和分子 P_n（BeukersLists bk_Pn_list，H_k 系数）与本积分  *)
(*    不配：谐和 x'_1 = P_1(1/2)/(2Q_1(1/2)) = (1/2)/3 = 1/6，而真      *)
(*    近似 x'_1 = r_1/(2²·q̃_1) = 8/12 = 2/3（真配分子 P*_n(1/2) =      *)
(*    r_n/2^n: 0, 2, 4.5——P*_n 闭式待 P2 后续席确定）。                 *)
(* 数值锚（n=1）：I_1 = 12·ln2 − 8，q̃_1 = 3，2^{2·1+1}·Q_1(1/2) = 12，  *)
(* 误差 = I_1/12 = ln2 − 2/3；T97 形 RHS = (12ln2−8)/18，其 ln2 系数    *)
(* = 2/3 ≠ 1，反例固化。x' 序列（真）：0, 2/3, 9/13。                   *)
(*                                                                 *)
(* 【本席交付面（降档判定：恒等式本体需积分/部分分式引擎，窗内不可达；   *)
(*   交付任务书认可的「2^{−(2n+1)} 归一因子件」+ 平方归一死亡证书】）：   *)
(*  ① bi_D / bi_D_eq_qtilde / bi_core_qtilde：Delannoy 核心            *)
(*     D_n := Σ_{j≤n} C(n,j)²·2^j == q̃_n（[w^n](2+w)^n(1+w)^n 的        *)
(*     w^n 系数即 D_n——(2+w)^n 以 2^{n−a} 展开时恰为降幂形，与          *)
(*     q̃_n 逐项重合，无需反转；升幂像经镜像函数 bk_psd 承载）。          *)
(*  ② bi_norm_factor：2^{n+1}·q̃_n == 2^{2n+1}·Q_n(1/2)（QeqT）——       *)
(*     真归一因子的闭式（分部积分离散同构的归一档）。                   *)
(*  ③ bi_Qn_half_gt1 / bi_square_disc：Q_n(1/2) > 1（n≥1）与           *)
(*     x < x² 正分离（QeqT/QltT Set 面）——T97 平方归一的死亡证书。      *)
(*  ④ bi_n1_anchor / bi_Qn_half_n1：n=1 数值哨兵（vm_compute 档）。     *)
(*                                                                 *)
(* 剩余路径卡点定位（P2 下席续接）：                                    *)
(*  (a) 积分侧：部分分式/极点分解引擎（c₁ = 2^n·q̃_n，其中               *)
(*      [w^n]p(2+w) = q̃_n 即 bi_D 核心；∫₀¹(1−t/2)^{−k} 闭式：          *)
(*      k≥2 有理、k=1 = 2ln2），或改走 (1+t)^{n+1} 变体                  *)
(*      （I'_n = q̃_n·ln2 − p_n，p: 0,2,9 免 2 幂）+ P1 积分二期机；      *)
(*  (b) 分子侧：P*_n 闭式待定（谐和形不配，P*_2(1/2) = 4.5 非整）；      *)
(*  (c) real 层装配（ln2i_x 消费）另案（正性面不碰）。                   *)
(*                                                                 *)
(* 红线自审：① 零承认面（全件 Qed，零承认词，依赖全在册）；             *)
(*   ② 语句面 Set（主件 QeqT/QltT；nat/Z/Q 支撑引理 Prop 面仅作推理      *)
(*      脚手架，BeukersLists bk_Qn_ge_3pow_nat / Ln2Escape 先例同构）；  *)
(*   ③ 非平凡（归一因子闭式换算 + 正分离见证链 + 反转归位）；            *)
(*   ④ 可提取（G3 探针独立文件实测，Obj.magic 计数=0）。                 *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp（vo_901 信任根在册）  *)
(*   + BeukersLists（/tmp/e118_side 侧编在册）。零云端零 git。           *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia Psatz.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists.

Open Scope nat_scope.

(* ============================================================ *)
(* §A Delannoy 核心（升幂和承载）与反转归位                              *)
(*   bi_D n = Σ_{k≤n} C(n,n−k)²·2^{n−k}，换元 j = n−k 即升幂和          *)
(*   Σ_{j≤n} C(n,j)²·2^j（镜像函数承载，bk_psd 递归字母复用）。          *)
(* ============================================================ *)

Definition bi_D (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

(* 反转归位：C(n,k)² 对称（bk_Qn_sym）⟹ 镜像和 == q̃_n 逐项归位
   （bk_psd_ext 逐点窗口 k < S n ⟺ k ≤ n 恰在对称域内） *)
Lemma bi_D_eq_qtilde : forall n : nat, bi_D n = bk_Qn_qtilde n.
Proof.
  intro n. unfold bi_D, bk_Qn_qtilde.
  apply bk_psd_ext. intros k Hk.
  assert (Hkle : k <= n) by lia.
  rewrite (bk_Qn_sym n k Hkle).
  reflexivity.
Qed.

(* 主件①：Delannoy 核心 == q̃_n（QeqT Set 面） *)
Theorem bi_core_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bi_D n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  rewrite bi_D_eq_qtilde. reflexivity.
Qed.

(* Q 层 2 幂像：q_pow (2#1) n == Q#2^n（换算脚手架） *)
Lemma bi_q_pow_2 : forall n : nat, q_pow (2 # 1)%Q n == (Z.of_nat (2 ^ n) # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat by (cbn [Nat.pow]; lia).
    apply bk_Qmul_nat.
Qed.

(* ============================================================ *)
(* §B 主件②：真归一因子闭式 2^{n+1}·q̃_n == 2^{2n+1}·Q_n(1/2)            *)
(*   （真恒等式 ln2 − x'_n = I_n/(2^{n+1}·q̃_n) 的归一档；                *)
(*    2^{n+1}·q̃_n = 2^{2n+1}·Q_n(1/2) 即 2^{−(2n+1)} 归一的正确落点）    *)
(* ============================================================ *)

Theorem bi_norm_factor : forall n : nat,
  QeqT ((Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n) # 1)%Q)
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n)) * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  replace (Datatypes.S (2 * n))%nat with (Datatypes.S n + n)%nat by lia.
  rewrite q_pow_add.
  transitivity ((q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q).
  - rewrite bi_q_pow_2. apply Qeq_sym. apply bk_Qmul_nat.
  - assert (Hh := bk_Qn_half_closed n).
    rewrite <- Qmult_assoc. rewrite Hh. reflexivity.
Qed.

(* ============================================================ *)
(* §C Q 层支撑件（Prop 面推理脚手架）                                    *)
(* ============================================================ *)

(* 同分母 Qlt（Z 面直译） *)
Lemma bi_Qlt_same_den : forall (a b : Z) (d : positive),
  (a < b)%Z -> Qlt (a # d) (b # d).
Proof.
  intros a b d Hab.
  assert (Hd : (0 < Z.pos d)%Z) by apply Pos2Z.is_pos.
  unfold Qlt. cbn [Qnum Qden]. nia.
Qed.

(* Qlt 沿 Qeq 运输 *)
Lemma bi_qlt_eq : forall a b c d : Q, Qlt a b -> a == c -> b == d -> Qlt c d.
Proof.
  intros a b c d Hab Hac Hbd.
  rewrite <- Hac, <- Hbd. exact Hab.
Qed.

(* 正 q 幂 *)
Lemma bi_q_pow_pos2 : forall n : nat, Qlt 0%Q (q_pow (2 # 1)%Q n).
Proof.
  induction n as [| n IH].
  - cbn [q_pow]. unfold Qlt. cbn [Qnum Qden]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* 正乘消去：a·q < c·q 且 0 < q ⟹ a < c *)
Lemma bi_Qlt_mul_cancel_r : forall a c q : Q,
  Qlt 0%Q q -> Qlt (a * q)%Q (c * q)%Q -> Qlt a c.
Proof.
  intros a c q Hq0 Hlt.
  destruct (Qlt_le_dec a c) as [Hac | Hca].
  - exact Hac.
  - exfalso. apply (Qlt_not_le (a * q)%Q (c * q)%Q Hlt).
    apply Qmult_le_compat_r.
    + exact Hca.
    + apply Qlt_le_weak. exact Hq0.
Qed.

(* 3^k > 0（幂正性，供 nia/lia 消费） *)
Lemma bi_pow3_pos : forall k : nat, (0 < 3 ^ k)%nat.
Proof.
  intro k. induction k as [| k IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

(* 2^n < 3^n（n≥1） *)
Lemma bi_half_gt_nat : forall n : nat, 1 <= n -> (2 ^ n < 3 ^ n)%nat.
Proof.
  intros n. induction n as [| n IH]; intros Hn.
  - cbn [Nat.pow]. lia.
  - destruct n as [| m].
    + cbn [Nat.pow]. lia.
    + assert (Hm : 1 <= Datatypes.S m) by lia. specialize (IH Hm).
      assert (Hp := bi_pow3_pos (Datatypes.S m)).
      rewrite (Nat.pow_succ_r' 2 (Datatypes.S m)), (Nat.pow_succ_r' 3 (Datatypes.S m)).
      nia.
Qed.

(* ============================================================ *)
(* §D 主件③：Q_n(1/2) > 1（n≥1）——T97 平方归一不可救的核                *)
(* ============================================================ *)

Theorem bi_Qn_half_gt1 : forall n : nat, 1 <= n ->
  QltT (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q).
Proof.
  intros n Hn.
  assert (Hge := bk_Qn_ge_3pow_nat n).
  assert (H23 := bi_half_gt_nat n Hn).
  assert (Hq : (2 ^ n < bk_Qn_qtilde n)%nat) by lia.
  assert (Hz : (Z.of_nat (2 ^ n) < Z.of_nat (bk_Qn_qtilde n))%Z)
    by (apply Nat2Z.inj_lt; exact Hq).
  assert (HQ : Qlt (Z.of_nat (2 ^ n) # 1) (Z.of_nat (bk_Qn_qtilde n) # 1))
    by (apply bi_Qlt_same_den; exact Hz).
  assert (Hh := bk_Qn_half_closed n).
  assert (HQ2 : Qlt ((q_pow (2 # 1)%Q n * (1 # 1))%Q)
                    ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2))%Q)).
  { apply (bi_qlt_eq _ _ _ _ HQ).
    - rewrite bi_q_pow_2. symmetry. apply Qmult_1_r.
    - apply Qeq_sym. exact Hh. }
  assert (HQ3 : Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  { apply (bi_Qlt_mul_cancel_r (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
             (q_pow (2 # 1)%Q n)).
    - apply bi_q_pow_pos2.
    - apply (bi_qlt_eq _ _ _ _ HQ2); ring. }
  apply Qlt_to_QltT. exact HQ3.
Qed.

(* Q_n(1/2) ≠ 1（n≥1）——平方归一强迫 Q_n(1/2)==1 的否证件 *)
Lemma bi_half_not1 : forall n : nat, 1 <= n ->
  ~ (bkQ (bk_Qn_list n) (1 # 2)%Q == 1 # 1)%Q.
Proof.
  intros n Hn He.
  assert (Hlt := QltT_to_Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
                   (bi_Qn_half_gt1 n Hn)).
  exact (Qlt_not_eq (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q) Hlt (Qeq_sym _ _ He)).
Qed.

(* ============================================================ *)
(* §E 主件④：平方归一分离见证（x < x²，n≥1 全域）                        *)
(*   若 T97 形（除以 Q_n(1/2)²）与真形（除以 Q_n(1/2)）同为归一，        *)
(*   则强迫 Q_n(1/2)² == Q_n(1/2)，即 Q_n(1/2) == 1——被 §D 否证。        *)
(* ============================================================ *)

Theorem bi_square_disc : forall n : nat, 1 <= n ->
  QltT (bkQ (bk_Qn_list n) (1 # 2)%Q)
       ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intros n Hn.
  assert (Hlt := QltT_to_Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
                   (bi_Qn_half_gt1 n Hn)).
  assert (H2 : Qlt ((1 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)
                   ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q).
  { apply Qmult_lt_compat_r.
    - apply (Qlt_trans 0%Q (1 # 1)%Q).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact Hlt.
    - exact Hlt. }
  apply Qlt_to_QltT.
  apply (bi_qlt_eq _ _ _ _ H2); ring.
Qed.

(* ============================================================ *)
(* §F 数值锚（n=1 哨兵：q̃_1 = 3，2^{2·1+1}·Q_1(1/2) = 12，Q_1(1/2)=3/2） *)
(* ============================================================ *)

Theorem bi_n1_anchor : QeqT ((Z.of_nat (2 ^ 2 * bk_Qn_qtilde 1) # 1)%Q) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bi_Qn_half_n1 : QeqT (bkQ (bk_Qn_list 1) (1 # 2)%Q) (3 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（G4 复核位）                          *)
(* ============================================================ *)

Print Assumptions bi_core_qtilde.
Print Assumptions bi_norm_factor.
Print Assumptions bi_Qn_half_gt1.
Print Assumptions bi_square_disc.
Print Assumptions bi_n1_anchor.
Print Assumptions bi_Qn_half_n1.
