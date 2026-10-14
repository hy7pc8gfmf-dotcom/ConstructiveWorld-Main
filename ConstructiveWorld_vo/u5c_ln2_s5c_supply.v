(* ===================================================================== *)
(*  u5c_ln2_s5c_supply.v —— ln2 五层供给面合流收束件（供给链主件）           *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_s5c_supply。                                          *)
(*  使命：把 ⑥预算实供给沿预算面桥一次代入、face 兑现、④缝内容             *)
(*    （s4f_content）与 ②头肢四路合流，铸出 u5c_ln2i_pade_supply X 的      *)
(*    显式见证定理 s5c_supply_inhabited——五层供给面（θ<1、0<|A_n|、        *)
(*    0<clo_n、clo_n≤线对象、线对象≤θⁿ）自 w1 先例的四残余前提              *)
(*    {②,④缝,⑥预算,face} 收缩为两位：                                     *)
(*        Hrho（s4f_rho 挤压位·勘录② Padé 有限 M 形）                      *)
(*        与 ⑥ 预算实供给（线对象≤4ⁿ·(7/40)ⁿ）。                            *)
(*    收缩路径：②头肢经规范分子 s5c_lna（2^{n+1}·q̃_n；Delannoy 下界        *)
(*    3ⁿ≤q̃_n 承领 0<|A_n|）机械销案；④缝经 s4f_content 规范见证承领；      *)
(*    ⑤下界肢经 clo_n≤lnf_bterm n 0（阶乘核 s5c_nat_core）＋分离量         *)
(*    lnf_bterm n 2 的显式配方承领；                                       *)
(*    ⑥上界肢经 u5c_ln2_theta_slot_face_of_budget 一次代入承领。           *)
(*  实现注记：主定理证体＝六肢逐位填充（每肢使用一具名机件，非单发空壳）；  *)
(*    Qeq/Qle 仅 Prop 推理面；nat 核不等式走显式乘法单调链（nia 证书两处）。 *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、    *)
(*    BeukersLists、u5c_ln2_gap2_bridge、u5c_ln2_assembly、u5c_ln2_seam4、  *)
(*    u5c_ln2_s4fill、u5c_ln2_witness、u5c_ln2_theta_slot、                *)
(*    abl_ln2_reorder、abl_ln2_reorder_assembly、abl_ln2_bsum_cauchy；     *)
(*    Stdlib：QArith/Qabs/ZArith/Arith/Factorial/Lia/Setoid/Qfield。        *)
(*  对标：甲件实名账：lncv_d1_head_gen／lncv_d1_head_int_gen；q̃_n 离散核＝  *)
(*    BeukersLists bk_Qn_qtilde／bk_Qn_ge_3pow_nat；θ 规范值＝              *)
(*    u5c_lna_theta_mod=4/5。                                              *)
(*  数值锚（Fractions 独立复算在卷）：clo_2=1/105 < lnf_bterm 2 0=1/30；    *)
(*    lnf_bterm 1 1=1/12 < lns_bsum 1 3−clo_1=53/240；                     *)
(*    lns_bsum 2 20≈0.0873≤(7/10)²=0.49；q̃_2=13。                          *)
(*  构造性注记：语句面全 Set（QeqT/QltT/QleT'/sigT/real_eq/real_lt/         *)
(*    real_le/And）；零承认、零经典逻辑、零 solver。                        *)
(*  诚实边界：残余 Observable 两位（Print Assumptions 仍全 Closed）：       *)
(*    Hrho：树侧供给位＝勘录②「Σ_k lnf_bterm n k == 2^{n+1}·q̃_n·ln2 −      *)
(*       2^{n+1}·p_n」有限 M 形（abl_ln2_reorder_assembly 头注②）；         *)
(*    ⑥ 预算：内容＝线对象为归一化积分常数倍＋lnt2_hquad 7/40 二次衰减核，   *)
(*       归一化恒等式与 Hrho 同源（勘录②）。两位于本件显式参数位承载，      *)
(*       到货即闭合。w5-face 对真族载体的支配命题（u5c_bv_psum n m <        *)
(*       lns_bsum n k）经精确有理算术独立复算 n=1..3、m≤60 零违例，         *)
(*       数值面为真、机证候铸（已不在关键路径，如实注明）。                  *)
(*       ln2b_irrational_from_supply 去参数化出口（u5c_ln2_assembly 头注   *)
(*       登记位）候两位到货后机械收束，本件不冒领。                          *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_s5c_supply.v    *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import BeukersLists.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_assembly.
Require Import u5c_ln2_seam4.
Require Import u5c_ln2_s4fill.
Require Import u5c_ln2_witness.
Require Import u5c_ln2_theta_slot.
Require Import abl_ln2_reorder.
Require Import abl_ln2_reorder_assembly.
Require Import abl_ln2_bsum_cauchy.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Arith.Factorial.
From Stdlib Require Import Lia.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 规范分子与 ②头肢销案（Delannoy 离散核）                               *)
(* ============================================================ *)

Lemma s5c_fact_pos : forall m : nat, (0 < fact m)%nat.
Proof.
  induction m as [| m IH].
  - simpl. lia.
  - simpl. nia.
Qed.

(* 幂下界（nat 层原子）：1 ≤ bⁿ（b ≥ 1） *)
Lemma s5c_pow_ge1 : forall (b n : nat), (1 <= b)%nat -> (1 <= b ^ n)%nat.
Proof.
  intros b n Hb. induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

(* 规范分子：A_n := 2^{n+1}·q̃_n（RunAlive 归一形 2^{n+1}·q̃_n·X − 2^{n+1}·p_n
   的分子侧；q̃_n＝中心 Delannoy 数，bk_Qn_qtilde 离散承载） *)
Definition s5c_lna (n : nat) : Z :=
  Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n).

(* ②头肢销案：0 < A_n——3ⁿ ≤ q̃_n（bk_Qn_ge_3pow_nat）与 2^{n+1} ≥ 2 合成 *)
Theorem s5c_canA_pos : forall n : nat, QltT 0 ((s5c_lna n) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt, s5c_lna. cbn [Qnum Qden].
  pose proof (bk_Qn_ge_3pow_nat n) as H1.
  assert (H2 : (1 <= 3)%nat) by lia.
  pose proof (s5c_pow_ge1 3 n H2) as H3.
  assert (H4 : (1 <= 2)%nat) by lia.
  pose proof (s5c_pow_ge1 2 (Datatypes.S n) H4) as H5.
  assert (Hz : (Z.of_nat 0 < Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n))%Z)
    by (apply Nat2Z.inj_lt; nia).
  lia.
Qed.

(* 正性迁移到 Qabs（②肢语句面 QltT 0 (Qabs (A n # 1)) 的直接承载） *)
Lemma s5c_abs_posT : forall q : Q, QltT 0 q -> QltT 0 (Qabs q).
Proof.
  intros q Hq. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt 0 q Hq) as Hq'.
  destruct q as [n d].
  unfold Qlt, Qabs in Hq' |- *. cbn [Qnum Qden] in Hq' |- *.
  lia.
Qed.

(* ②肢（Qabs 形） *)
Theorem s5c_canA_abs_pos : forall n : nat, QltT 0 (Qabs ((s5c_lna n) # 1)%Q).
Proof. intro n. apply s5c_abs_posT. apply s5c_canA_pos. Qed.

(* ============================================================ *)
(* §1 见证 clo 的阶乘核与 clo_n ≤ lnf_bterm n 0                             *)
(* ============================================================ *)

(* wfact ＝ fact（定义体逐字同构） *)
Lemma s5c_wfact_Zeq : forall n : nat,
  Z.of_nat (u5c_ln2_wfact n) = Z.of_nat (fact n).
Proof.
  induction n as [| n IH]. reflexivity.
  cbn [u5c_ln2_wfact fact]. rewrite !Nat2Z.inj_mul, IH. reflexivity.
Qed.

(* Pos.of_succ_nat 的 Z 值（of_succ_nat (S k) 定义性折叠为 Pos.succ 形） *)
Lemma s5c_pos_succ_Z : forall k : nat,
  (Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))%Z.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [Pos.of_succ_nat]. rewrite Pos2Z.inj_succ. rewrite IH.
    rewrite (Nat2Z.inj_succ (Datatypes.S k)). reflexivity.
Qed.

(* wfactp（positive 阶乘）的 Z 值桥 *)
Lemma s5c_wfactp_Zeq : forall n : nat,
  QeqT ((Z.pos (u5c_ln2_wfactp n)) # 1)%Q ((Z.of_nat (fact n)) # 1)%Q.
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. reflexivity.
  - assert (Hzp : (Z.pos (u5c_ln2_wfactp (Datatypes.S n))
                    = Z.of_nat (fact (Datatypes.S n)))%Z).
    { cbn [u5c_ln2_wfactp fact]. rewrite Pos2Z.inj_mul, s5c_pos_succ_Z.
      assert (IHq2 : (Z.pos (u5c_ln2_wfactp n) = Z.of_nat (fact n))%Z).
      { pose proof (qeqT_imp_qeq _ _ IH) as H. unfold Qeq in H.
        cbn [Qnum Qden Qmult] in H. rewrite !Z.mul_1_r in H. exact H. }
      rewrite IHq2, (Nat2Z.inj_mul (Datatypes.S n) (fact n)). reflexivity. }
    apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qmult].
    rewrite Hzp. reflexivity.
Qed.

(* nat 核不等式：n!·(2n)!·(2n+1)! ≤ (n!)²·(3n+1)!
   （归纳步：2n+2/2n+3 各沿 fact(2n+1)、3n+4 沿 fact(3n+1) 展开，
   配合 fact(2n+1) = (2n+1)·fact(2n) 的恒等改写后为多项式证书一处） *)
Lemma s5c_nat_core : forall n : nat,
  (fact n * fact (2 * n) * fact (2 * n + 1)
     <= fact n * fact n * fact (3 * n + 1))%nat.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - assert (HE : (fact (2 * n + 1) = Datatypes.S (2 * n) * fact (2 * n))%nat).
    { replace (2 * n + 1)%nat with (Datatypes.S (2 * n))%nat by lia.
      reflexivity. }
    replace (2 * Datatypes.S n + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * n + 1)))%nat by lia.
    replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (2 * n + 1))%nat by lia.
    replace (3 * Datatypes.S n + 1)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (3 * n + 1))))%nat by lia.
    cbn [fact] in IH |- *.
    rewrite HE in IH |- *.
    (* 归纳步合成：目标＝系数积×IH（两侧），系数不等式与 IH 各自承领后重排 *)
    assert (Hm : (Datatypes.S n * Datatypes.S (2 * n + 1) * Datatypes.S (2 * n + 1)
                    * Datatypes.S (Datatypes.S (2 * n + 1)) * Datatypes.S (2 * n)
                    * (fact n * fact (2 * n) * (Datatypes.S (2 * n) * fact (2 * n)))
                  <= (Datatypes.S n * Datatypes.S n
                       * Datatypes.S (Datatypes.S (Datatypes.S (3 * n + 1)))
                       * Datatypes.S (Datatypes.S (3 * n + 1))
                       * Datatypes.S (3 * n + 1)
                       * (fact n * fact n * fact (3 * n + 1))))%nat).
    { apply Nat.mul_le_mono.
      - nia.
      - exact IH. }
    nia.
Qed.

(* Q 分式序：a/b ≤ c/d ⟸ a·d ≤ c·b（Ln2Escape lne_div_le_inv 同款双单乘法式，
   Qinv 全程抽象不展开；ring 仅做乘法重排） *)
Lemma s5c_qdiv_mult : forall p q : Q, QeqT (p / q) (p * Qinv q).
Proof. intros p q. apply qeq_imp_qeqT. unfold Qdiv. reflexivity. Qed.

Lemma s5c_qdiv_le : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qle (a * d) (c * b) -> Qle (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hle.
  assert (Hb0 : ~ (b == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q b Hb). exact (Qeq_sym _ _ E). }
  assert (Hd0 : ~ (d == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q d Hd). exact (Qeq_sym _ _ E). }
  assert (Ebb : (b * Qinv b)%Q == 1%Q) by (apply Qmult_inv_r; exact Hb0).
  assert (Edd : (d * Qinv d)%Q == 1%Q) by (apply Qmult_inv_r; exact Hd0).
  assert (H1 : Qle ((a * d) * Qinv b) (c * b * Qinv b)).
  { apply (Qmult_le_compat_r (a * d) (c * b)).
    - exact Hle.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hb. }
  assert (E3 : (c * b * Qinv b)%Q == (c * (b * Qinv b))%Q) by ring.
  assert (E4 : (c * 1)%Q == c%Q) by ring.
  rewrite E3, Ebb, E4 in H1.
  assert (H2 : Qle ((a * d) * Qinv b * Qinv d) (c * Qinv d)).
  { apply (Qmult_le_compat_r ((a * d) * Qinv b) c).
    - exact H1.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hd. }
  assert (E5 : (((a * d) * Qinv b) * Qinv d)%Q
               == (a * (d * Qinv d) * Qinv b)%Q) by ring.
  assert (E6 : (a * 1 * Qinv b)%Q == (a * Qinv b)%Q) by ring.
  rewrite E5, Edd, E6 in H2.
  apply (Qle_trans (a / b) (a * Qinv b) (c / d)).
  - apply qeq_le. apply qeqT_imp_qeq. apply (s5c_qdiv_mult a b).
  - apply (Qle_trans _ (c * Qinv d)).
    + exact H2.
    + apply qeq_le. apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (s5c_qdiv_mult c d))).
Qed.

(* 分母正元素桥：1/1 形与 qmake 除法形 *)
Lemma s5c_qone_div : QeqT ((1 # 1) / 1)%Q (1 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma s5c_qmake_div : forall (A : Z) (p : positive),
  QeqT ((A # p)%Q) (((A # 1) / ((Z.pos p) # 1))%Q).
Proof.
  intros A p. apply qeq_imp_qeqT. unfold Qdiv, Qinv, Qeq.
  simpl. ring.
Qed.

Lemma s5c_qdiv_den : forall (N : Z) (p : positive) (z : Z),
  QeqT ((Z.pos p) # 1)%Q ((z # 1)%Q) ->
  QeqT ((N # 1) / ((Z.pos p) # 1))%Q ((N # 1) / ((z # 1))%Q).
Proof.
  intros N p z H. apply qeq_imp_qeqT. unfold Qdiv. apply Qmult_comp.
  - apply Qeq_refl.
  - pose proof (qeqT_imp_qeq _ _ H) as Hq.
    unfold Qeq in Hq. cbn [Qnum Qden Qmult] in Hq.
    rewrite !Z.mul_1_r in Hq. rewrite <- Hq. reflexivity.
Qed.

Lemma s5c_qeqT_mult_r : forall c a b : Q, QeqT a b -> QeqT (a * c) (b * c).
Proof.
  intros c a b H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ H) as Hq. setoid_rewrite Hq. reflexivity.
Qed.

(* 分子同余：QeqT a b -> QeqT (a / q) (b / q)（纯 s5c_qdiv_mult／
   s5c_qeqT_mult_r 链式合成，Qdiv 定义面 p * Qinv q 承载） *)
Lemma s5c_qdiv_num_compat : forall a b q : Q, QeqT a b -> QeqT (a / q) (b / q).
Proof.
  intros a b q H.
  apply (gap2_qeqT_trans _ (b * Qinv q)).
  - apply (gap2_qeqT_trans _ (a * Qinv q)).
    + apply s5c_qdiv_mult.
    + apply (s5c_qeqT_mult_r _ _ _ H).
  - apply qeq_imp_qeqT. apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (s5c_qdiv_mult b q))).
Qed.

(* clo 桥：clo_n == (n!·(2n)!) / (3n+1)! 的 Z 分式除法形 *)
Lemma s5c_clo_form : forall n : nat,
  QeqT (u5c_ln2_clo_witness n)
       (((Z.of_nat (fact n * fact (2 * n))) # 1) /
        ((Z.of_nat (fact (3 * n + 1))) # 1))%Q.
Proof.
  intro n.
  assert (Hnum : QeqT (((Z.of_nat (u5c_ln2_wfact n) * Z.of_nat (u5c_ln2_wfact (2 * n))) # 1)%Q)
                       (((Z.of_nat (fact n * fact (2 * n))) # 1)%Q)).
  { apply qeq_imp_qeqT.
    rewrite (s5c_wfact_Zeq n), (s5c_wfact_Zeq (2 * n)).
    rewrite (Nat2Z.inj_mul (fact n) (fact (2 * n))). reflexivity. }
  apply (gap2_qeqT_trans _ (((Z.of_nat (u5c_ln2_wfact n) * Z.of_nat (u5c_ln2_wfact (2 * n))) # 1) /
           ((Z.pos (u5c_ln2_wfactp (3 * n + 1))) # 1))%Q).
  - apply s5c_qmake_div.
  - apply (gap2_qeqT_trans _ (((Z.of_nat (u5c_ln2_wfact n) * Z.of_nat (u5c_ln2_wfact (2 * n))) # 1) /
           ((Z.of_nat (fact (3 * n + 1))) # 1))%Q).
    + apply (s5c_qdiv_den _ _ _ (s5c_wfactp_Zeq (3 * n + 1))).
    + apply (s5c_qdiv_num_compat _ _ _ Hnum).
Qed.

(* lnf 首项桥：lnf_bterm n 0 == ((n!)²) / (2n+1)! 的 Z 分式除法形
   （bkC 对角与 q_pow/q_fact 桥经 setoid 重写一次到位） *)
Lemma s5c_lnf0_form : forall n : nat,
  QeqT (lnf_bterm n 0)
       ((((1 # 1) / 1) * (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1)) /
          (Z.of_nat (fact (2 * n + 1)) # 1)))%Q).
Proof.
  intro n. unfold lnf_bterm.
  replace (n + 0)%nat with n by lia.
  replace (2 * n + 0 + 1)%nat with (2 * n + 1)%nat by lia.
  rewrite bkC_diag. cbn [q_pow].
  apply qeq_imp_qeqT.
  setoid_rewrite (sif_qfact_Z n).
  setoid_rewrite (sif_qfact_Z (2 * n + 1)).
  reflexivity.
Qed.

(* 主不等式：clo_n ≤ lnf_bterm n 0 *)
Theorem s5c_clo_le_bterm0 : forall n : nat,
  QleT' (u5c_ln2_clo_witness n) (lnf_bterm n 0).
Proof.
  intro n.
  pose proof (s5c_clo_form n) as Hcf.
  pose proof (s5c_lnf0_form n) as Hlf.
  apply (qleT'_trans _ (((Z.of_nat (fact n * fact (2 * n))) # 1) /
          ((Z.of_nat (fact (3 * n + 1))) # 1))%Q).
  - apply qeq_leT'. apply qeqT_imp_qeq. exact Hcf.
  - apply (qleT'_trans _ ((((1 # 1) / 1) * (((Z.of_nat (fact n) # 1) *
              (Z.of_nat (fact n) # 1)) / (Z.of_nat (fact (2 * n + 1)) # 1))))%Q).
    + apply Qle_to_QleT'.
      apply (Qle_trans _ (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1)) /
              (Z.of_nat (fact (2 * n + 1)) # 1))%Q).
      * apply (s5c_qdiv_le ((Z.of_nat (fact n * fact (2 * n))) # 1)
              ((Z.of_nat (fact (3 * n + 1))) # 1)
              (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))%Q)
              ((Z.of_nat (fact (2 * n + 1))) # 1)).
        -- unfold Qlt. cbn [Qnum Qden].
           assert (Hz : (Z.of_nat 0 < Z.of_nat (fact (3 * n + 1)))%Z)
             by (apply Nat2Z.inj_lt; apply s5c_fact_pos).
           lia.
        -- unfold Qlt. cbn [Qnum Qden].
           assert (Hz : (Z.of_nat 0 < Z.of_nat (fact (2 * n + 1)))%Z)
             by (apply Nat2Z.inj_lt; apply s5c_fact_pos).
           lia.
        -- assert (Hz : (Z.of_nat (fact n * fact (2 * n) * fact (2 * n + 1))
                         <= Z.of_nat (fact n * fact n * fact (3 * n + 1)))%Z)
             by (apply Nat2Z.inj_le; apply s5c_nat_core).
           assert (E1 : (Z.of_nat (fact n * fact (2 * n) * fact (2 * n + 1))
                         = Z.of_nat (fact n * fact (2 * n))
                           * Z.of_nat (fact (2 * n + 1)))%Z)
             by (rewrite !Nat2Z.inj_mul; reflexivity).
           assert (E2 : (Z.of_nat (fact n * fact n * fact (3 * n + 1))
                         = Z.of_nat (fact n * fact n)
                           * Z.of_nat (fact (3 * n + 1)))%Z)
             by (rewrite !Nat2Z.inj_mul; reflexivity).
           assert (E0 : (Z.of_nat (fact n * fact n)
                         = Z.of_nat (fact n) * Z.of_nat (fact n))%Z)
             by (rewrite Nat2Z.inj_mul; reflexivity).
           unfold Qle, Qmult. cbn [Qnum Qden Qmult].
           rewrite E1, E2, E0 in Hz. nia.
      * apply qeq_le. apply (Qeq_sym _ _ (Qmult_1_l _)).
    + apply qeq_leT'.
      apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hlf)).
Qed.
(* ============================================================ *)
(* §2 ⑤下界肢：clo_n < 真族载体（分离量 lnf_bterm n 1）                     *)
(* ============================================================ *)

(* 0 < t ⟹ x < x + t（QltT 形） *)
Lemma s5c_ltT_add_r : forall x t : Q, QltT 0 t -> QltT x (x + t).
Proof.
  intros x t Ht.
  pose proof (QltT_to_Qlt 0 t Ht) as Hq.
  pose proof (proj2 (Qplus_lt_l 0 t x) Hq) as Hq2.
  apply (qltT_eq_compat_r (x + t)%Q (t + x)%Q x).
  - ring.
  - apply (qltT_eq_compat_l (0 + x)%Q x (t + x)).
    + ring.
    + apply Qlt_to_QltT. exact Hq2.
Qed.

(* 0 ≤ s ⟹ 0 < t + s（QltT/QleT' 合成） *)
Lemma s5c_ltT_plus_leT0 : forall t s : Q, QltT 0 t -> QleT' 0 s -> QltT 0 (t + s).
Proof.
  intros t s Ht Hs.
  apply (qltT_eq_compat_l (0 + 0)%Q 0 (t + s)).
  - ring.
  - apply (qltT_plus_leT'_ltT 0 t 0 s).
    + exact Ht.
    + exact Hs.
Qed.

(* ⑤下界肢：clo_n < 真族载体（真族部分和单调＋首两项支配＋正项分离量） *)
Theorem s5c_clo_lt_carrier : forall n : nat,
  real_lt (real_const (u5c_ln2_clo_witness n))
          (u5c_lns_Ibreal lns_bsum lnb2_cauchy n).
Proof.
  intro n. unfold real_lt.
  exists (lnf_bterm n 1). split.
  - apply Qlt_to_QltT. apply lnf_bterm_pos.
  - exists 2%nat. intros k Hk.
    assert (H2 : (2 <= k)%nat) by (apply NatLe_drop in Hk; exact Hk).
    change (projT1 (real_const (u5c_ln2_clo_witness n)) k)
      with (u5c_ln2_clo_witness n).
    unfold u5c_lns_Ibreal, u5c_lnr_Ireal_pack. cbn [projT1].
    pose proof (s5c_clo_le_bterm0 n) as Hclo.
    pose proof (QleT'_to_Qle _ _ Hclo) as Hcle.
    pose proof (lnf_bterm_pos n 2) as Hpos2.
    pose proof (lns_bsum_mono n 2 k H2) as Hge2.
    assert (H2eq : lns_bsum n 2
                   == (lnf_bterm n 0 + lnf_bterm n 2 + lnf_bterm n 1)%Q).
    { unfold lns_bsum. cbn [sum_upto]. ring. }
    assert (Hclt : QltT (u5c_ln2_clo_witness n)
                        (lnf_bterm n 0 + lnf_bterm n 2)%Q).
    { apply (qltT_leT'_ltT (u5c_ln2_clo_witness n)
               (u5c_ln2_clo_witness n + lnf_bterm n 2)%Q).
      - apply s5c_ltT_add_r. apply Qlt_to_QltT. exact Hpos2.
      - apply qleT'_plus_compat. exact Hclo. apply qleT'_refl. }
    pose proof (QltT_to_Qlt _ _ Hclt) as Hclt'.
    pose proof (proj2 (Qplus_lt_l _ _ (lnf_bterm n 1)) Hclt') as Hb'.
    assert (HB : QltT (u5c_ln2_clo_witness n + lnf_bterm n 1)%Q
                      (lnf_bterm n 0 + lnf_bterm n 2 + lnf_bterm n 1)%Q).
    { apply Qlt_to_QltT. exact Hb'. }
    assert (HC : QltT (u5c_ln2_clo_witness n + lnf_bterm n 1)%Q (lns_bsum n k)).
    { apply (qltT_leT'_ltT _ (lnf_bterm n 0 + lnf_bterm n 2 + lnf_bterm n 1)%Q).
      - exact HB.
      - apply (qleT'_trans _ (lns_bsum n 2)).
        + apply qeq_leT'.
          apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (qeq_imp_qeqT _ _ H2eq))).
        + apply Qle_to_QleT'. exact Hge2. }
    pose proof (QltT_to_Qlt _ _ HC) as Hcc.
    pose proof (proj2 (Qplus_lt_l _ _ ((- u5c_ln2_clo_witness n)%Q)) Hcc) as Hd.
    apply (qltT_eq_compat_l
             ((u5c_ln2_clo_witness n + lnf_bterm n 1)
               + (- u5c_ln2_clo_witness n))%Q
             (lnf_bterm n 1)
             (lns_bsum n k - u5c_ln2_clo_witness n)%Q).
    + field.
    + apply Qlt_to_QltT. exact Hd.
Qed.

(* ============================================================ *)
(* §3 五层供给面合流收束主件                                                *)
(* ============================================================ *)

Theorem s5c_supply_inhabited :
  forall (X : Real) (Bmod : nat -> Z),
    (forall n : nat, forall eps : Q, QltT 0 eps ->
       sigT (fun N : nat => forall k : nat, NatLe N k ->
               QltT (Qabs (s4f_rho X s5c_lna Bmod n k)) eps)) ->
    (forall n : nat,
       real_le (u5c_ln2b_line X s5c_lna Bmod n)
               (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
    u5c_ln2i_pade_supply X.
Proof.
  intros X Bmod Hrho Hbudget.
  apply (u5c_gap2_bridge X s5c_lna Bmod u5c_ln2_clo_witness (4 # 5)%Q
           (u5c_lns_Ibreal lns_bsum lnb2_cauchy)).
  unfold u5c_gap2_slot.
  split.
  - exact gap2_theta_45_lt1.
  - split.
    + intro n. apply s5c_canA_abs_pos.
    + split.
      * intro n. apply u5c_ln2_witness_pos.
      * split.
        -- intro n. exact (s4f_content X s5c_lna Bmod n (Hrho n)).
        -- split.
           ++ intro n. exact (inl (s5c_clo_lt_carrier n)).
           ++ intro n.
              exact (u5c_ln2_theta_slot_face_of_budget X s5c_lna Bmod
                       (u5c_lns_Ibreal lns_bsum lnb2_cauchy)
                       (fun n0 : nat => s4f_content X s5c_lna Bmod n0 (Hrho n0))
                       Hbudget n).
Qed.

(* ============================================================ *)
(* §4 RunAlive 数值锚（vm_compute 精确判定·Fractions 独立复算在卷）          *)
(* ============================================================ *)

Theorem s5c_runalive_clo2 :
  QltT (u5c_ln2_clo_witness 2) (lnf_bterm 2 0).
Proof. vm_compute. reflexivity. Qed.

Theorem s5c_runalive_sep13 :
  QltT (lnf_bterm 1 1) (lns_bsum 1 3 - u5c_ln2_clo_witness 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem s5c_runalive_budget2 :
  QleT' (lns_bsum 2 20) (q_pow (7 # 10)%Q 2).
Proof. vm_compute. reflexivity. Qed.

Theorem s5c_runalive_q2 :
  QeqT (Z.of_nat (bk_Qn_qtilde 2) # 1)%Q (13 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 提取与假设审计（零承认复核）                                           *)
(* ============================================================ *)

Separate Extraction u5c_ln2_clo_witness s5c_lna.

Print Assumptions s5c_canA_pos.
Print Assumptions s5c_canA_abs_pos.
Print Assumptions s5c_wfact_Zeq.
Print Assumptions s5c_wfactp_Zeq.
Print Assumptions s5c_nat_core.
Print Assumptions s5c_clo_le_bterm0.
Print Assumptions s5c_clo_lt_carrier.
Print Assumptions s5c_supply_inhabited.
Print Assumptions s5c_runalive_clo2.
Print Assumptions s5c_runalive_sep13.
Print Assumptions s5c_runalive_budget2.
Print Assumptions s5c_runalive_q2.
