(* 五字段指针｜模块：piu1880_valve_qchain.v。
   数学使命：A3 四缺件之③（浅深序第二位）——阀分母
   valve_den := (h+1)·(2·n_sel+2)! 的 Q 层换算链全件：
   ①高度坐标换算（使用 1864 耦合桥 2·n_sel+2 = 40h+48·
     piu1872_valve_den 高度面 == (h+1)·(40h+48)!·born 独立语句——
     1872 §8 Eden assert 的 born 化）；
   ②valve_up 高度面双肢（piu1866_valve_R1_height 之姊妹肢——
     1866 阀形高度面已 born·上界肢 valve_up 高度面本件补齐）；
   ③(h+1) 乘链后继形：den (S h) == den h + (2n_sel+2)!（加法展开）；
   ④阶乘 Q 化后继链：den h (S n_sel) == (2n+4)·(2n+3)·den h n_sel；
   ⑤单调双肢（h 肢＝(h+1) 乘链单调·n_sel 肢＝阶乘 Q 化单调）；
   ⑥正性肢＋⑦K-cap 接入面（缺件② κ₁/κ₀ 界的插入接口：
     K ≤ Kcap ∧ 8·Kcap ≤ den ⟹ valve_up K——高度面同款）。
   依赖：Stdlib QArith/Qminmax/Lia/ZArith；S03_QExp（q_fact/q_fact_succ/
   q_fact_pos）；LW1PiMeasure（lw1m_height）；leibsep_nsel_h_coupling
   （piu1864_two_nsel_height/piu1864_nsel_qden·1864 born 只读）；
   leibsep_band_domain（piu1866_Qeq_le_r/l·1866 born 只读·R 版补 Require）；
   leibsep_band_ck_assembly（piu1872_valve_den/valve_up/qfact_mono/
   Qeq_le_swap·1872 编译世界 -Q 引用·只读）。对标：mathlib/stdlib 无直接对应；高度面沿 LW1PiMeasure lw1m_height。
   构造性：零公理/零承认式/零经典逻辑；Q 面收尾显式链
   （Qmult_le_compat_r/Qmult_plus_distr_l/Qmult_1_l/Qle_refl/
   Qlt_le_weak/Qmult_lt_0_compat/piu1872_qfact_mono）；nat/Z 面
   lia＋Z2Nat.inj_lt/inj_le 桥（1872/1879 同款实名）；闭 Q 值叶
   vm_compute（closed-Qle closer＝vm_compute+discriminate·1872 实录）。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <vo>/Local ""
   -Q <vo> "" -Q <1872world> ""（cwd 本件沙箱；cpu_guard v3 包裹）。
   命名：piu1880_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith.
Require Import S03_QExp.
Require Import LW1PiMeasure.
Require Import leibsep_nsel_h_coupling.
Require Import leibsep_band_domain.
Require Import leibsep_band_ck_assembly.

(* ---------- §0 高度面链量缩写 ---------- *)

Definition piu1880_den_h (q : Q) : Q :=
  piu1872_valve_den (lw1m_height q) (piu1864_nsel (Qred q)).

(* ---------- §1 正性肢 ---------- *)

Lemma piu1880_valve_den_pos : forall h n_sel : nat,
  Qlt 0 (piu1872_valve_den h n_sel).
Proof.
  intros h n_sel. unfold piu1872_valve_den.
  apply Qmult_lt_0_compat.
  - assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z)
      by (apply Z2Nat.inj_lt; lia).
    unfold Qlt. cbn [Qnum Qden]. lia.
  - apply q_fact_pos.
Qed.

(* ---------- §2 高度坐标换算（使用 1864 耦合桥·40h+48） ---------- *)

Lemma piu1880_valve_den_height_conv : forall q : Q,
  piu1872_valve_den (lw1m_height q) (piu1864_nsel (Qred q)) ==
  ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
   * q_fact (40 * lw1m_height q + 48)%nat)%Q.
Proof.
  intros q. unfold piu1872_valve_den.
  rewrite (piu1864_two_nsel_height q). reflexivity.
Qed.

Lemma piu1880_den_h_conv : forall q : Q,
  piu1880_den_h q == ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
                      * q_fact (40 * lw1m_height q + 48)%nat)%Q.
Proof.
  intros q. unfold piu1880_den_h.
  apply piu1880_valve_den_height_conv.
Qed.

(* ---------- §3 valve_up 高度面双肢（1866 valve_R1_height 姊妹肢） ---------- *)

(* Qeq 除式桥（Qdiv=Qmult x /y 定义式展开＋Qeq 集合体 rewrite·Qinv_comp
   Proper 实例在册——经微型检验直接验证的配方） *)
Lemma piu1880_Qeq_div_r : forall (a x y : Q), x == y -> (a / x)%Q == (a / y)%Q.
Proof.
  intros a x y H. unfold Qdiv. rewrite H. reflexivity.
Qed.

Lemma piu1880_valve_up_height_iff : forall (K q : Q),
  piu1872_valve_up K (lw1m_height q) (piu1864_nsel (Qred q)) <->
  Qle ((8 # 1)%Q * K)
      (((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
        * q_fact (40 * lw1m_height q + 48)%nat)%Q).
Proof.
  intros K q. split; intros HH.
  - unfold piu1872_valve_up in HH.
    apply (piu1866_Qeq_le_r _ _ _ (piu1880_valve_den_height_conv q)). exact HH.
  - unfold piu1872_valve_up.
    apply (piu1866_Qeq_le_l _ _ _ (piu1880_valve_den_height_conv q)). exact HH.
Qed.

Lemma piu1880_valve_up_height : forall (K q : Q),
  Qle ((8 # 1)%Q * K)
      (((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
        * q_fact (40 * lw1m_height q + 48)%nat)%Q) ->
  piu1872_valve_up K (lw1m_height q) (piu1864_nsel (Qred q)).
Proof.
  intros K q HH. apply (proj2 (piu1880_valve_up_height_iff K q)). exact HH.
Qed.

(* ---------- §4 (h+1) 乘链后继形 ---------- *)

Lemma piu1880_valve_den_succ_h : forall (h n_sel : nat),
  piu1872_valve_den (Datatypes.S h) n_sel ==
  (piu1872_valve_den h n_sel + q_fact (2 * n_sel + 2)%nat)%Q.
Proof.
  intros h n_sel. unfold piu1872_valve_den.
  set (F := q_fact (2 * n_sel + 2)%nat).
  assert (EQ : (Z.of_nat (Datatypes.S (Datatypes.S h)) # 1)%Q
               == ((Z.of_nat (Datatypes.S h) + 1) # 1)%Q).
  { unfold Qeq. cbn [Qnum Qden]. rewrite Nat2Z.inj_succ. lia. }
  rewrite EQ.
  assert (EQ2 : ((Z.of_nat (Datatypes.S h) + 1) # 1)%Q
                == ((Z.of_nat (Datatypes.S h) # 1)%Q + (1 # 1)%Q)%Q)
    by (unfold Qeq, Qplus; cbn [Qnum Qden]; lia).
  rewrite EQ2, Qmult_plus_distr_l.
  rewrite Qmult_1_l. reflexivity.
Qed.

(* ---------- §5 阶乘 Q 化后继链（n_sel 侧） ---------- *)

Lemma piu1880_valve_den_succ_nsel : forall (h n_sel : nat),
  piu1872_valve_den h (Datatypes.S n_sel) ==
  ((Z.of_nat (Datatypes.S (Datatypes.S (2 * n_sel + 2))) # 1)%Q
   * ((Z.of_nat (Datatypes.S (2 * n_sel + 2)) # 1)%Q
      * piu1872_valve_den h n_sel)%Q)%Q.
Proof.
  intros h n_sel.
  assert (En : (2 * Datatypes.S n_sel + 2)%nat
               = Datatypes.S (Datatypes.S (2 * n_sel + 2))%nat) by lia.
  unfold piu1872_valve_den. rewrite En. rewrite !q_fact_succ. ring.
Qed.

(* ---------- §6 单调双肢 ---------- *)

Lemma piu1880_valve_den_mono_h : forall (h1 h2 n_sel : nat),
  (h1 <= h2)%nat -> Qle (piu1872_valve_den h1 n_sel) (piu1872_valve_den h2 n_sel).
Proof.
  intros h1 h2 n_sel Hle. unfold piu1872_valve_den.
  apply Qmult_le_compat_r.
  - assert (Hz : (Z.of_nat h1 <= Z.of_nat h2)%Z)
      by (apply Z2Nat.inj_le; lia).
    unfold Qle. cbn [Qnum Qden].
    pose proof (Nat2Z.inj_succ h1) as Hs1.
    pose proof (Nat2Z.inj_succ h2) as Hs2.
    lia.
  - apply Qlt_le_weak. apply q_fact_pos.
Qed.

Lemma piu1880_valve_den_mono_nsel : forall (h n1 n2 : nat),
  (n1 <= n2)%nat -> Qle (piu1872_valve_den h n1) (piu1872_valve_den h n2).
Proof.
  intros h n1 n2 Hle. unfold piu1872_valve_den.
  assert (Hm : Qle (q_fact (2 * n1 + 2)%nat
                      * (Z.of_nat (Datatypes.S h) # 1)%Q)
                    (q_fact (2 * n2 + 2)%nat
                       * (Z.of_nat (Datatypes.S h) # 1)%Q)).
  { apply Qmult_le_compat_r.
    - apply piu1872_qfact_mono. lia.
    - assert (Hh : (0 <= Z.of_nat (Datatypes.S h))%Z)
        by (apply Z2Nat.inj_le; lia).
      unfold Qle. cbn [Qnum Qden]. lia. }
  apply (piu1866_Qeq_le_r (q_fact (2 * n2 + 2)%nat
                             * (Z.of_nat (Datatypes.S h) # 1)%Q)%Q
                          ((Z.of_nat (Datatypes.S h) # 1)%Q
                             * q_fact (2 * n2 + 2)%nat)%Q
                          ((Z.of_nat (Datatypes.S h) # 1)%Q
                             * q_fact (2 * n1 + 2)%nat)%Q).
  - apply Qmult_comm.
  - apply (piu1872_Qeq_le_swap (q_fact (2 * n1 + 2)%nat
                                  * (Z.of_nat (Datatypes.S h) # 1)%Q)%Q
                               ((Z.of_nat (Datatypes.S h) # 1)%Q
                                  * q_fact (2 * n1 + 2)%nat)%Q
                               (q_fact (2 * n2 + 2)%nat
                                  * (Z.of_nat (Datatypes.S h) # 1)%Q)%Q).
    + apply Qmult_comm.
    + exact Hm.
Qed.

(* ---------- §7 K-cap 接入面（缺件② κ₁/κ₀ 界插入接口） ---------- *)

Theorem piu1880_valve_up_from_Kcap : forall (K Kcap : Q) (h n_sel : nat),
  Qle K Kcap ->
  Qle ((8 # 1)%Q * Kcap) (piu1872_valve_den h n_sel) ->
  piu1872_valve_up K h n_sel.
Proof.
  intros K Kcap h n_sel HK Hcap. unfold piu1872_valve_up.
  apply (Qle_trans ((8 # 1)%Q * K) ((8 # 1)%Q * Kcap)
                   (piu1872_valve_den h n_sel)).
  - assert (Hm : Qle (K * (8 # 1)%Q) (Kcap * (8 # 1)%Q))
      by (apply Qmult_le_compat_r;
            [ exact HK | vm_compute; discriminate ]).
    apply (piu1866_Qeq_le_r (Kcap * (8 # 1)%Q) ((8 # 1)%Q * Kcap)
                            ((8 # 1)%Q * K)).
    + apply Qmult_comm.
    + apply (piu1872_Qeq_le_swap (K * (8 # 1)%Q) ((8 # 1)%Q * K)
                                 (Kcap * (8 # 1)%Q)).
      * apply Qmult_comm.
      * exact Hm.
  - exact Hcap.
Qed.

Theorem piu1880_valve_up_height_from_Kcap : forall (K Kcap q : Q),
  Qle K Kcap ->
  Qle ((8 # 1)%Q * Kcap)
      (((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
        * q_fact (40 * lw1m_height q + 48)%nat)%Q) ->
  piu1872_valve_up K (lw1m_height q) (piu1864_nsel (Qred q)).
Proof.
  intros K Kcap q HK Hcap.
  apply (piu1880_valve_up_from_Kcap K Kcap); [ exact HK | ].
  apply (piu1866_Qeq_le_l _ _ _ (piu1880_valve_den_height_conv q)). exact Hcap.
Qed.

(* ========== 编译出口核对 ========== *)

Check piu1880_valve_den_pos.
Check piu1880_Qeq_div_r.
Check piu1880_valve_den_height_conv.
Check piu1880_den_h_conv.
Check piu1880_valve_up_height_iff.
Check piu1880_valve_up_height.
Check piu1880_valve_den_succ_h.
Check piu1880_valve_den_succ_nsel.
Check piu1880_valve_den_mono_h.
Check piu1880_valve_den_mono_nsel.
Check piu1880_valve_up_from_Kcap.
Check piu1880_valve_up_height_from_Kcap.

Print Assumptions piu1880_valve_den_pos.
Print Assumptions piu1880_Qeq_div_r.
Print Assumptions piu1880_valve_den_height_conv.
Print Assumptions piu1880_den_h_conv.
Print Assumptions piu1880_valve_up_height_iff.
Print Assumptions piu1880_valve_up_height.
Print Assumptions piu1880_valve_den_succ_h.
Print Assumptions piu1880_valve_den_succ_nsel.
Print Assumptions piu1880_valve_den_mono_h.
Print Assumptions piu1880_valve_den_mono_nsel.
Print Assumptions piu1880_valve_up_from_Kcap.
Print Assumptions piu1880_valve_up_height_from_Kcap.
