(* ===================================================================== *)
(*  zb3p_hpw.v —— ζ(3) 装配面①Hpw 逐点封顶证书闭合（无窗全称形·零前提）      *)
(* ===================================================================== *)
(*  一 使命：                                                            *)
(*    闭合 u5c_z3_assembly_slot3 第二前提位（Hpw 逐点封顶证书）：            *)
(*      forall m j, 5 ≤ m -> zb3_term (S m) j·(S j)·(j+2) ≤ (1/8)(1/40)^m。 *)
(*    证书实为无窗全称形（∀j 无界），严格强于槽前提（槽面窗 j ≤ m²+2m）。    *)
(*    路线＝ζ(2) band 链（A2R3 playbook）的立方适配，三件新机：             *)
(*      · 跨行比率律 z3r_row_ratio：                                        *)
(*        h(n,j)·(n+j+1)⁴(n+1)² == h(n+1,j)·(2n+j+2)³(2n+j+3)³              *)
(*        （bkC 桥＝zb2_ga_bkC_HG 第二件 k:=n+j, r:=n；q_fact 后继展开）；   *)
(*      · 跨行迁移 z3r_transfer：40·h(n+1,j) ≤ h(n,j) 对 ∀n∀j——             *)
(*        多项式核 (2a+b)⁶−40(a+b)⁴a² = 24a⁶+32a⁵b+20a²b⁴+12ab⁵+b⁶ ≥ 0      *)
(*        （a:=n+1, b:=j·系数全非负·零域约束）；                            *)
(*      · 行内下落链 z3r_h_fall_step/chain（n ≥ 6, j ≥ 2n−2 段单调降）：     *)
(*        移位展开 (u+2a+11)²(u+4a+24)³−(u+3a+17)⁴(u+2a+13) ≥ 0 系数全非负   *)
(*        （a:=n−6, u:=j−2n+2）；仅用于 m=5 基座行 6 的 j>35 段收拢。        *)
(*    归纳＝基座 m=5（行 6·窗 j≤35 三十六点 vm_compute 精确判定＋j>35 下落   *)
(*    链收拢到列 10）＋步档（纯跨行迁移·全称 j·零窗约束）。                  *)
(*  二【数值纪律】                                                        *)
(*    精确有理复算全网格零反例：跨行比率恒等式 n∈[1,20)×j<30；迁移 40·h     *)
(*    (n+1,j)≤h(n,j) 于 n∈[6,90)×j<400（P 率最小 46.07 @ (89,91)）；下落步   *)
(*    n∈[6,90)×j∈[2n−2,600)（率最小 1.0214）；基座窗 8·h(6,j)·40⁵≤1 于      *)
(*    j≤35 全真（最紧点边距倒数 ~3.4e-9·余量充分）。                        *)
(*  三 依赖：                                                            *)
(*    缓存根 S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists；库内     *)
(*    abl_z2_pointwise、abl_z3_itg_carrier（zb3_term/zb3_term_pos）、        *)
(*    u5c_zeta2_gapA（bkC_HG/取消律/正性）、u5c_zeta2_a1_sign、              *)
(*    u5c_zeta2_a2_tail、u5c_zeta2_gapB（zb2gb_Qnat_le）。                   *)
(*  四 构造性：                                                          *)
(*    纯构造性、零全局假设声明、零承认词面；语句结论全 Set 层（QleT'/QeqT）； *)
(*    nat 证书前提为语句假设位非公理位；代数步走 field/ring＋nia。           *)
(*  五 编译配方：                                                        *)
(*    rocq c -native-compiler no -q -Q . "" zb3p_hpw.v                      *)
(*  对标：Beukers, Bull. London Math. Soc. 11 (1979)；A2R3＝u5c_zeta2_band。 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_pointwise.
Require Import abl_z3_itg_carrier.
Require Import abl_z3_tail.
Require Import abl_z2_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign u5c_zeta2_a2_tail u5c_zeta2_gapB.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 逐点封顶量 h(n,j) 与正性                                             *)
(* ============================================================ *)

Lemma z3r_q_ge0 : forall k : nat, 0 <= (Z.of_nat k # 1)%Q.
Proof.
  intro k. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma z3r_qpos_ne : forall k : nat, (1 <= k)%nat -> ~ ((Z.of_nat k # 1) == 0).
Proof.
  intros k Hk. apply zb2_ga_pos_neq0. apply QltT_to_Qlt. apply zb2_ga_natpos_lt. exact Hk.
Qed.

Definition z3r_h (n j : nat) : Q :=
  zb3_term n j * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1).

Lemma z3r_h_pos : forall n j : nat, 0 < z3r_h n j.
Proof.
  intros n j. unfold z3r_h. apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; [ apply QltT_to_Qlt; apply zb3_term_pos
      | apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia ].
  - apply QltT_to_Qlt. apply zb2_ga_natpos_lt. lia.
Qed.

Lemma z3r_h_ge0 : forall n j : nat, 0 <= z3r_h n j.
Proof.
  intros n j. unfold z3r_h. apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; [ apply (Qlt_le_weak 0); apply QltT_to_Qlt; apply zb3_term_pos
      | apply z3r_q_ge0 ].
  - apply z3r_q_ge0.
Qed.

(* ============================================================ *)
(* §2 nat 层两件多项式不等式（迁移核＋下落核）                              *)
(* ============================================================ *)

(* 迁移核：(2n+j+2)³(2n+j+3)³ ≥ 40·(n+j+1)⁴(n+1)²。
   恒等式核：(2a+b)⁶ − 40(a+b)⁴a² = 24a⁶+32a⁵b+20a²b⁴+12ab⁵+b⁶（a:=n+1,b:=j）
   系数全非负·零域约束（精确有理复算 n∈[6,90)×j<400 零反例·P 率最小 46.07）。 *)
Theorem z3r_transfer_nat : forall n j : nat,
  (40 * (n + j + 1) * (n + j + 1) * (n + j + 1) * (n + j + 1) * (Datatypes.S n) * (Datatypes.S n)
   <= (2 * n + j + 2) * (2 * n + j + 2) * (2 * n + j + 2)
      * (2 * n + j + 3) * (2 * n + j + 3) * (2 * n + j + 3))%nat.
Proof.
  intros n j.
  assert (HW : ((2 * n + j + 2) * (2 * n + j + 2) * (2 * n + j + 2)
              <= (2 * n + j + 3) * (2 * n + j + 3) * (2 * n + j + 3))%nat) by nia.
  nia.
Qed.

(* 下落核：行内单调降（n ≥ 6, j ≥ 2n−2）。
   移位（a:=n−6, u:=j−2n+2）后差为全非负系数和（精确复算 n∈[6,90)×
   j∈[2n−2,600) 零反例·率最小 1.0214）。 *)
Theorem z3r_fall_nat : forall n j : nat,
  (6 <= n)%nat -> (2 * n <= j + 2)%nat ->
  ((n + j + 1) * (n + j + 1) * (n + j + 1) * (n + j + 1) * (j + 3)
   <= (Datatypes.S j) * (Datatypes.S j) * (2 * n + j + 2) * (2 * n + j + 2) * (2 * n + j + 2))%nat.
Proof.
  intros n j Hn Hj.
  remember (n - 6)%nat as a eqn:Ea.
  assert (Hn' : (n = 6 + a)%nat) by lia.
  remember (j - (2 * n - 2))%nat as u eqn:Eu.
  assert (Hj' : (j = u + 2 * a + 10)%nat) by lia.
  subst n. subst j.
  nia.
Qed.

(* 右嵌套拼形（供 HP0/HGQ 折叠后 exact——免裸 nia 的证书搜索爆炸） *)
Lemma z3r_HN_r : forall n j : nat,
  (40 * ((n + j + 1) * ((n + j + 1) * ((n + j + 1) * ((n + j + 1)
     * (Datatypes.S n * (Datatypes.S n))))))
   <= ((2 * n + j + 2) * ((2 * n + j + 2) * ((2 * n + j + 2)
      * ((2 * n + j + 3) * ((2 * n + j + 3) * (2 * n + j + 3)))))))%nat.
Proof.
  intros n j. pose proof (z3r_transfer_nat n j) as H.
  rewrite <- !Nat.mul_assoc in H. exact H.
Qed.

Lemma z3r_GN_r : forall n j : nat, (6 <= n)%nat -> (2 * n <= j + 2)%nat ->
  (((n + j + 1) * ((n + j + 1) * ((n + j + 1) * ((n + j + 1) * (j + 3))))
   <= (Datatypes.S j * (Datatypes.S j * ((2 * n + j + 2)
      * ((2 * n + j + 2) * (2 * n + j + 2)))))))%nat.
Proof.
  intros n j Hn Hj. pose proof (z3r_fall_nat n j Hn Hj) as H.
  rewrite <- !Nat.mul_assoc in H. exact H.
Qed.

(* 分母原子非零（本件自备·abl_z3_tail zb3_ga_nonzero 同型） *)
Ltac zb3p_ga_nonzero :=
  repeat split;
  first [ apply zb2_ga_pos_neq0; apply q_fact_pos
        | apply zb2_ga_pos_neq0; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia
        | apply zb2_ga_pos_neq0; apply Qmult_lt_0_compat; zb3p_ga_nonzero ].

(* ============================================================ *)
(* §3 跨行比率律（h 面立方版·本件核心恒等式）                               *)
(* ============================================================ *)

Theorem z3r_row_ratio : forall n j : nat,
  QeqT (z3r_h n j
        * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
           * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
              * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
       (z3r_h (Datatypes.S n) j
        * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
           * ((Z.of_nat (2 * n + j + 2) # 1)
              * ((Z.of_nat (2 * n + j + 3) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                 * (Z.of_nat (2 * n + j + 3) # 1))))))).
Proof.
  intros n j. unfold z3r_h, zb3_term.
  replace (Datatypes.S n + j + Datatypes.S n + 1)%nat with (Datatypes.S (n + j + n + 2))%nat by lia.
  replace (Datatypes.S n + j)%nat with (Datatypes.S (n + j))%nat by lia.
  apply qeq_imp_qeqT.
  pose proof (zb2_ga_bkC_HG (n + j)) as HG.
  destruct HG as [_ HG2].
  specialize (HG2 n (ltac:(lia))).
  assert (HBQ : (Z.of_nat (bkC (Datatypes.S (n + j)) (Datatypes.S n)) # 1)
                * (Z.of_nat (Datatypes.S n) # 1)
             == (Z.of_nat (bkC (n + j) n) # 1) * (Z.of_nat (Datatypes.S (n + j)) # 1)).
  { unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. rewrite <- !Nat2Z.inj_mul. rewrite HG2. lia. }
  assert (Hsn : ~ ((Z.of_nat (Datatypes.S n) # 1) == 0))
    by (apply zb2_ga_pos_neq0; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia).
  assert (HB2 : (Z.of_nat (bkC (Datatypes.S (n + j)) (Datatypes.S n)) # 1)
             == (Z.of_nat (bkC (n + j) n) # 1) * (Z.of_nat (Datatypes.S (n + j)) # 1)
                * / (Z.of_nat (Datatypes.S n) # 1)).
  { transitivity ((Z.of_nat (bkC (Datatypes.S (n + j)) (Datatypes.S n)) # 1)
                  * ((Z.of_nat (Datatypes.S n) # 1) * / (Z.of_nat (Datatypes.S n) # 1))).
    - rewrite (Qmult_inv_r (Z.of_nat (Datatypes.S n) # 1) Hsn).
      rewrite Qmult_1_r. ring.
    - rewrite Qmult_assoc. rewrite HBQ. ring. }
  rewrite (q_fact_succ (n + j)).
  rewrite (q_fact_succ n).
  rewrite (q_fact_succ (n + j + n + 2)).
  replace (n + j + n + 2)%nat with (Datatypes.S (n + j + n + 1))%nat by lia.
  rewrite (q_fact_succ (n + j + n + 1)).
  rewrite HB2.
  replace (Datatypes.S (n + j))%nat with (n + j + 1)%nat by lia.
  replace (Datatypes.S (n + j + n + 2))%nat with (2 * n + j + 3)%nat by lia.
  replace (Datatypes.S (n + j + n + 1))%nat with (2 * n + j + 2)%nat by lia.
  replace (Datatypes.S (2 * n + j + 2))%nat with (2 * n + j + 3)%nat by lia.
  field; zb3p_ga_nonzero.
Qed.

(* ============================================================ *)
(* §4 跨行迁移：40·h(n+1,j) ≤ h(n,j)（∀n∀j·零约束）                        *)
(* ============================================================ *)

Theorem z3r_transfer : forall n j : nat,
  QleT' (z3r_h (Datatypes.S n) j * (Z.of_nat 40 # 1)) (z3r_h n j).
Proof.
  intros n j. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (z3r_row_ratio n j)) as Hr.
  pose proof (z3r_transfer_nat n j) as HN.
  assert (HP0 : Qle ((Z.of_nat 40 # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                        * ((Z.of_nat (n + j + 1) # 1)
                           * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
                    (((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                     * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1)))))))).
  { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    rewrite <- !Nat2Z.inj_mul. rewrite !Z.mul_1_r.
    apply (proj1 (Nat2Z.inj_le _ _)). exact (z3r_HN_r n j). }
  assert (HDpos : (0 < ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                        * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                        * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1)))))))%Q).
  { repeat apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia. }
  (* 步1：compat_r——(40·P0)·h ≤ D·h *)
  assert (H1 : Qle (((Z.of_nat 40 # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                        * ((Z.of_nat (n + j + 1) # 1)
                           * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
                    * z3r_h n j)
                   (((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                     * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1))))))
                    * z3r_h n j)).
  { apply (Qmult_le_compat_r
             ((Z.of_nat 40 # 1) * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                   * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
             ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                   * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1))))))
             (z3r_h n j) HP0 (z3r_h_ge0 n j)). }
  (* 步2：右侧搬正 D·h == h·D *)
  assert (H2 : Qle (((Z.of_nat 40 # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                        * ((Z.of_nat (n + j + 1) # 1)
                           * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
                    * z3r_h n j)
                   (z3r_h n j * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                     * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1)))))))).
  { apply (Qle_trans _ (((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                          * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                          * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1))))))
                         * z3r_h n j)).
    - exact H1.
    - apply qeq_le. ring. }
  (* 步3：cancel D 后左端经 qeq_le 搬正（Qeq 面改写） *)
  apply (zb2_ga_cancel_r _ _
          (((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
           * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
           * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1))))))) HDpos).
  apply (Qle_trans _ (((Z.of_nat 40 # 1) * ((Z.of_nat (n + j + 1) # 1)
                       * ((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                          * ((Z.of_nat (n + j + 1) # 1)
                             * ((Z.of_nat (Datatypes.S n) # 1) * (Z.of_nat (Datatypes.S n) # 1)))))))
                      * z3r_h n j)).
  - apply qeq_le.
    transitivity ((Z.of_nat 40 # 1) * (z3r_h (Datatypes.S n) j
                   * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                      * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 3) # 1)
                      * ((Z.of_nat (2 * n + j + 3) # 1) * (Z.of_nat (2 * n + j + 3) # 1)))))))).
    + ring.
    + rewrite <- Hr. ring.
  - exact H2.
Qed.

Theorem z3r_h_fall_step : forall n j : nat,
  (6 <= n)%nat -> (2 * n <= j + 2)%nat ->
  QleT' (z3r_h n (Datatypes.S j)) (z3r_h n j).
Proof.
  intros n j Hn Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (zb3_term_ratio n j)) as Hr.
  replace (n + Datatypes.S j + n + 1)%nat with (2 * n + j + 2)%nat in Hr by lia.
  replace (n + Datatypes.S j)%nat with (n + j + 1)%nat in Hr by lia.
  pose proof (z3r_fall_nat n j Hn Hj) as HGN.
  assert (HDpos : (0 < ((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                        * ((Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))))%Q).
  { apply Qmult_lt_0_compat; [ apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia
    | repeat apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia ]. }
  assert (HGQ : Qle (((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))))
                    * (Z.of_nat (j + 3) # 1))
                    ((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (Datatypes.S j) # 1)
                    * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1)))))).
  { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    rewrite <- !Nat2Z.inj_mul. rewrite !Z.mul_1_r.
    apply (proj1 (Nat2Z.inj_le _ _)). nia. }
  (* 步1：compat_r——(E⁴·(j+3))·(t·(j+2)) ≤ ((S j)²·D³)·(t·(j+2)) *)
  assert (H1 : Qle (((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))))
                    * (Z.of_nat (j + 3) # 1) * (zb3_term n j * (Z.of_nat (j + 2) # 1)))
                   (((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (Datatypes.S j) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                        * (Z.of_nat (2 * n + j + 2) # 1)))))
                    * (zb3_term n j * (Z.of_nat (j + 2) # 1)))).
  { apply (Qmult_le_compat_r
             (((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
              * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))))
              * (Z.of_nat (j + 3) # 1))
             ((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (Datatypes.S j) # 1)
              * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                 * (Z.of_nat (2 * n + j + 2) # 1)))))
             (zb3_term n j * (Z.of_nat (j + 2) # 1)) HGQ
             (Qmult_le_0_compat (zb3_term n j) (Z.of_nat (j + 2) # 1)
                (Qlt_le_weak 0 (zb3_term n j) (QltT_to_Qlt 0 (zb3_term n j) (zb3_term_pos n j)))
                (z3r_q_ge0 (j + 2)))).
  }
  (* 步2：右侧搬正 X·(S j)²·D³ 的环归位（qeq_le） *)
  assert (H2 : Qle (((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                     * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))))
                    * (Z.of_nat (j + 3) # 1) * (zb3_term n j * (Z.of_nat (j + 2) # 1)))
                   (z3r_h n j * ((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                     * ((Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))))).
  { apply (Qle_trans _ (((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (Datatypes.S j) # 1)
                          * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                             * (Z.of_nat (2 * n + j + 2) # 1)))))
                         * (zb3_term n j * (Z.of_nat (j + 2) # 1)))).
    - exact H1.
    - apply qeq_le. unfold z3r_h. ring. }
  (* 步3：cancel (S j)·D³ 后左端经 qeq_le 搬正（Hr 的 Qeq 面改写） *)
  apply (zb2_ga_cancel_r _ _
          ((Z.of_nat (Datatypes.S j) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
           * ((Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))) HDpos).
  apply (Qle_trans _ (((Z.of_nat (n + j + 1) # 1) * ((Z.of_nat (n + j + 1) # 1)
                       * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))))
                      * (Z.of_nat (j + 3) # 1) * (zb3_term n j * (Z.of_nat (j + 2) # 1)))).
  - apply qeq_le.
    transitivity ((zb3_term n (Datatypes.S j) * ((Z.of_nat (Datatypes.S j) # 1)
                   * ((Z.of_nat (2 * n + j + 2) # 1) * ((Z.of_nat (2 * n + j + 2) # 1)
                      * (Z.of_nat (2 * n + j + 2) # 1))))) * ((Z.of_nat (j + 3) # 1)
                   * (Z.of_nat (j + 2) # 1))).
    + unfold z3r_h.
      replace (Datatypes.S (Datatypes.S j))%nat with (j + 2)%nat by lia.
      replace (Datatypes.S j + 2)%nat with (j + 3)%nat by lia.
      ring.
    + rewrite Hr. ring.
  - exact H2.
Qed.

Theorem z3r_h_fall_chain : forall n d j : nat,
  (6 <= n)%nat -> (2 * n <= j + 2)%nat ->
  QleT' (z3r_h n (j + d)) (z3r_h n j).
Proof.
  intros n d. induction d as [| d IH]; intros j Hn Hj.
  - rewrite Nat.add_0_r. apply Qle_to_QleT'. apply Qle_refl.
  - rewrite Nat.add_succ_r.
    apply Qle_to_QleT'.
    apply (Qle_trans (z3r_h n (Datatypes.S (j + d))) (z3r_h n (j + d)) (z3r_h n j)).
    + exact (QleT'_to_Qle _ _ (z3r_h_fall_step n (j + d) Hn ltac:(lia))).
    + exact (QleT'_to_Qle _ _ (IH j Hn ltac:(lia))).
Qed.

(* ============================================================ *)
(* §6 幂逆桥与基座窗（m=5·行 6·三十六点精确判定）                           *)
(* ============================================================ *)

Lemma z3r_qpow_pair : forall m : nat, q_pow (40 # 1) m * q_pow (1 # 40) m == 1.
Proof.
  intro m.
  transitivity (q_pow ((40 # 1) * (1 # 40)) m).
  - symmetry. apply zb2_q_pow_mul.
  - assert (Hx : ((40 # 1) * (1 # 40))%Q == 1) by ring.
    rewrite Hx. apply q_pow_one.
Qed.

Lemma zb3r_base5 : forall j : nat, (j <= 10)%nat ->
  QleT' (z3r_h 6 j * q_pow (40 # 1) 5) ((1 # 8)).
Proof.
  intro j. intro Hj.
  do 11 (destruct j; [ vm_compute; reflexivity | ]).
  exfalso. lia.
Qed.

(* ============================================================ *)
(* §7 封顶归纳与终形（无窗全称·严格强于槽前提）                             *)
(* ============================================================ *)

Theorem zb3r_cap : forall m : nat, (5 <= m)%nat ->
  forall j : nat, QleT' (z3r_h (Datatypes.S m) j * q_pow (40 # 1) m) ((1 # 8)).
Proof.
  intro m. induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (Nat.eq_dec m 4) as [H4 | Hne].
    + (* 基座 m=5：窗内精确判定＋窗外下落链收拢到列 10 *)
      subst m. intro j. destruct (le_lt_dec j 10) as [Hj | Hjgt].
      * apply (zb3r_base5 j Hj).
      * assert (Hchain : QleT' (z3r_h 6 j) (z3r_h 6 10)).
        { replace j with (10 + (j - 10))%nat by lia.
          apply (z3r_h_fall_chain 6 (j - 10) 10 ltac:(lia) ltac:(lia)). }
        pose proof (zb3r_base5 10 (Nat.le_refl 10)) as H10.
        apply Qle_to_QleT'.
        apply (Qle_trans (z3r_h 6 j * q_pow (40 # 1) 5)
                         (z3r_h 6 10 * q_pow (40 # 1) 5) (1 # 8)).
        -- apply (Qmult_le_compat_r (z3r_h 6 j) (z3r_h 6 10) (q_pow (40 # 1) 5)
                   (QleT'_to_Qle _ _ Hchain)
                   (q_pow_nonneg (40 # 1) 5 (ltac:(unfold Qle; cbn [Qnum Qden]; lia)))).
        -- apply QleT'_to_Qle. exact H10.
    + (* 步档：纯跨行迁移（全称 j·零窗约束） *)
      assert (Hm5 : (5 <= m)%nat) by lia.
      intro j.
      pose proof (z3r_transfer (Datatypes.S m) j) as Htr.
      apply Qle_to_QleT'.
      pose proof (q_pow_succ (40 # 1) m) as HS.
      rewrite HS.
      assert (E1 : (z3r_h (Datatypes.S (Datatypes.S m)) j
                    * ((Z.of_nat 40 # 1) * q_pow (40 # 1) m)
                 == (z3r_h (Datatypes.S (Datatypes.S m)) j * (Z.of_nat 40 # 1))
                    * q_pow (40 # 1) m)) by ring.
      rewrite E1.
      apply (Qle_trans ((z3r_h (Datatypes.S (Datatypes.S m)) j * (Z.of_nat 40 # 1))
                        * q_pow (40 # 1) m)
                       (z3r_h (Datatypes.S m) j * q_pow (40 # 1) m) (1 # 8)).
      * apply (Qmult_le_compat_r (z3r_h (Datatypes.S (Datatypes.S m)) j * (Z.of_nat 40 # 1))
                   (z3r_h (Datatypes.S m) j) (q_pow (40 # 1) m)
                   (QleT'_to_Qle _ _ Htr)
                   (q_pow_nonneg (40 # 1) m (ltac:(unfold Qle; cbn [Qnum Qden]; lia)))).
      * exact (QleT'_to_Qle _ _ (IH Hm5 j)).
Qed.

(* 终形＝slot3 第二前提位（Hpw）的零前提闭合（无窗全称形）。 *)
Theorem zb3r_Hpw_closed : forall m j : nat, (5 <= m)%nat ->
  QleT' (zb3_term (Datatypes.S m) j
         * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
        ((1 # 8) * q_pow (1 # 40) m).
Proof.
  intros m j Hm.
  assert (Hid : (zb3_term (Datatypes.S m) j * (Z.of_nat (Datatypes.S j) # 1)
                 * (Z.of_nat (j + 2) # 1)) == z3r_h (Datatypes.S m) j) by reflexivity.
  pose proof (zb3r_cap m Hm j) as Hcap.
  pose proof (z3r_qpow_pair m) as Hpair.
  assert (HE : z3r_h (Datatypes.S m) j
             == z3r_h (Datatypes.S m) j * (q_pow (40 # 1) m * q_pow (1 # 40) m)).
  { rewrite Hpair. ring. }
  apply Qle_to_QleT'.
  rewrite Hid. rewrite HE.
  apply (Qle_trans _ ((z3r_h (Datatypes.S m) j * q_pow (40 # 1) m) * q_pow (1 # 40) m)).
  - apply qeq_le. ring.
  - apply (Qmult_le_compat_r (z3r_h (Datatypes.S m) j * q_pow (40 # 1) m) (1 # 8)
             (q_pow (1 # 40) m) (QleT'_to_Qle _ _ Hcap)
             (q_pow_nonneg (1 # 40) m (ltac:(unfold Qle; cbn [Qnum Qden]; lia)))).
Qed.

(* ============================================================ *)
(* §8 数值锚（计算链判定件·辅助面豁免）                                    *)
(* ============================================================ *)

Lemma zb3r_h_6_10_anchor :
  QleT' (z3r_h 6 10 * q_pow (40 # 1) 5) ((1 # 8)).
Proof. vm_compute. reflexivity. Qed.

Lemma zb3r_ratio_anchor :
  z3r_h 6 6 * ((Z.of_nat 13 # 1) * ((Z.of_nat 13 # 1) * ((Z.of_nat 13 # 1)
   * ((Z.of_nat 13 # 1) * ((Z.of_nat 7 # 1) * (Z.of_nat 7 # 1))))))
  == z3r_h 7 6 * ((Z.of_nat 20 # 1) * ((Z.of_nat 20 # 1) * ((Z.of_nat 20 # 1)
     * ((Z.of_nat 21 # 1) * ((Z.of_nat 21 # 1) * (Z.of_nat 21 # 1)))))).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §9 尾舱：语句公理面自检                                                 *)
(* ============================================================ *)

Separate Extraction zb3r_Hpw_closed.

Print Assumptions z3r_transfer_nat.
Print Assumptions z3r_fall_nat.
Print Assumptions z3r_row_ratio.
Print Assumptions z3r_transfer.
Print Assumptions z3r_h_fall_step.
Print Assumptions z3r_h_fall_chain.
Print Assumptions z3r_qpow_pair.
Print Assumptions zb3r_base5.
Print Assumptions zb3r_cap.
Print Assumptions zb3r_Hpw_closed.
