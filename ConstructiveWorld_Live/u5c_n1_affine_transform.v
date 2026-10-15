(* 五字段指针｜使命：N1·仿射件——证书的钉定变换代数（仿射首例三族）。
   承 DM-NEW 探探单 §三 N1（对象级新数学族第 3 件·仿 N5 工艺）：
   对 √2 闭式分离证书（u5c_sqrt2_closed_measure 五实例统一语句形，
   常元 1/(12b²) QeqT 钉定），施工三族变换下的钉定提升定理：
   ①平移 x↦x+k（k:Z）：常元不变 1/(12b²) ↦ 1/(12b²)（钉定恒等式首例）；
   ②数乘 x↦kx（k:positive）：1/(12b²) ↦ 1/(12·k·b²)；
   ③倒数 x↦1/x：分母符号三分钉定——a ≤ 0 档常元 1/4（n₀=1 统一窗）、
     a = p > 0 档常元 1/(36·p·b)（双窗 n₀ ≥ (b+3)+(p+3)，ε = (3/5)e，
     ρ := 2p/(3b) 符号两案：ρ ≥ 3/5 直取；ρ < 3/5（10p < 9b）以 b 窗
     e 界 1/(12b²) 收束（D·e ≤ 1/(20b²) ≤ 2c 判据）——对照
     _mirror_n1.py Fractions 全网格先行 0 违例）。
   对象级新颖性申报：变换族的「逐字闭式常元映射」为库外不自然对象
   （经典 Liouville 闭合为存在式非钉定形）；内容初等如实登记（DM-NEW §三
   N1 低新度条款）。指数层和积复合＝经典开放域（真墙记录档），本件不触；
   一般 Möbius (a₀x+b₀)/(c₀x+d₀) 全定理＝切片（极点邻近估计为新增难度）。
   依赖：池内在册件（同根只读引用）：u5c_dm_escape_window、
   u5c_dm_escape_to_dist_any（边距参数化桥·Defined）、
   u5c_sqrt2_closed_measure（dmcm 四分支边距核＋dmcm_qle_add_cancel_r）、
   UpReqSqrt3Irrational（ir2 序列/界/ir2_tail/ir2_vanish）、S02（QltT/
   QleT'/QeqT/real 面）；Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、
   Setoid、Morphisms、Qfield。
   构造性注记：主语句全 Set 层（sigT/And/QltT/QeqT/real_lt），零 Prop 前提
   位；证明体内 Prop 推导合法；零承认、零经典逻辑、零全局假设；新定义面
   零新增（全 lemma/theorem）；主定理装配链非单发空壳（Qeq 恒等式桥＋abs
   分解＋dmcm 边距核重用＋ρ 两案组装）；数值见证位 vm_compute 合法（复算
   律，对照 _mirror_n1.py 先行）。
   编译配方：source Live/toolchain/env.sh 后
   bash cpu_guard.sh -Front 1 -Mid 1 -- rocq c -native-compiler no -q -Q . ""
     u5c_n1_affine_transform.v（并发=1·池限域 N54） *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_bridge.
Require Import u5c_dm_escape_window.
Require Import u5c_dm_escape_to_dist_any.
Require Import u5c_sqrt2_closed_measure.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：自携微件                                                        *)
(* ============================================================ *)

(* u > 0 档：|u·s| == |u|·s（abs 分解核正半档） *)
Lemma n1_abs_scale_pos : forall (s u : Q), Qlt 0 s -> Qlt 0 u ->
  Qabs (u * s)%Q == (Qabs u * s)%Q.
Proof.
  intros s u Hs Hu.
  rewrite (Qabs_pos u (Qlt_le_weak 0 u Hu)).
  assert (Hus : Qlt 0 ((u * s)%Q)).
  { pose proof (Qmult_lt_compat_r 0%Q u s Hs Hu) as HH.
    rewrite Qmult_0_l in HH. exact HH. }
  rewrite (Qabs_pos (u * s) (Qlt_le_weak 0 (u * s) Hus)).
  reflexivity.
Qed.

(* |u·s| == |u|·s（s > 0）——数乘/倒数两族 abs 分解核 *)
Lemma n1_abs_scale : forall (s u : Q), Qlt 0 s -> Qabs (u * s)%Q == (Qabs u * s)%Q.
Proof.
  intros s u Hs.
  destruct (Qlt_le_dec 0 u) as [Hup | Hun].
  - exact (n1_abs_scale_pos s u Hs Hup).
  - destruct (Qlt_le_dec u 0) as [Hun0 | Huz].
    + destruct u as [un ud].
      assert (Hnu : Qlt 0 ((Z.opp un # ud)%Q)).
      { unfold Qlt in *. cbn [Qnum Qden Qopp] in *. destruct un; lia. }
      assert (Hnus : Qlt 0 (((Z.opp un # ud)%Q * s)%Q)).
      { pose proof (Qmult_lt_compat_r 0%Q ((Z.opp un # ud)%Q) s Hs Hnu) as HH.
        rewrite Qmult_0_l in HH. exact HH. }
      assert (HA1 : Qabs ((un # ud) * s)%Q == Qabs ((Z.opp un # ud) * s)%Q).
      { assert (HE : ((Z.opp un # ud) * s)%Q == Qopp ((un # ud) * s)%Q)
          by (unfold Qmult, Qopp, Qeq; cbn [Qnum Qden Qmult Qopp]; nia).
        rewrite HE. rewrite Qabs_opp. reflexivity. }
      assert (HA2 : Qabs (un # ud)%Q == Qabs ((Z.opp un # ud)%Q)).
      { assert (HE : (Z.opp un # ud)%Q == Qopp (un # ud)%Q) by reflexivity.
        rewrite HE. rewrite Qabs_opp. reflexivity. }
      rewrite HA1, HA2.
      exact (n1_abs_scale_pos s (Z.opp un # ud) Hs Hnu).
    + assert (Huz0 : u == 0%Q) by (apply Qle_antisym; assumption).
      rewrite Huz0, Qmult_0_l.
      rewrite (Qabs_pos 0%Q (Qle_refl 0%Q)).
      rewrite Qmult_0_l. reflexivity.
Qed.

(* 右消：A == (A·w)·Qinv w（w ≠ 0） *)
Lemma n1_mul_cancel_r : forall (A w : Q), ~ (w == 0%Q) -> A == (A * w) * Qinv w%Q.
Proof.
  intros A w Hw. rewrite <- Qmult_assoc.
  rewrite (Qmult_inv_r w Hw). symmetry. apply Qmult_1_r.
Qed.

(* 减法右单调（0 ≤ t ⟹ c − t ≤ c） *)
Lemma n1_qle_minus_le : forall c t : Q, Qle 0 t -> Qle (c - t)%Q c.
Proof.
  intros c t Ht.
  apply (Qle_trans (c - t)%Q ((c - t)%Q + t) c).
  - apply (Qle_trans (c - t)%Q ((c - t)%Q + 0%Q) ((c - t)%Q + t)).
    + apply qeq_imp_qle. symmetry. apply Qplus_0_r.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Ht.
  - apply qeq_imp_qle. apply lic_qlt_minus_add_r.
Qed.

(* 减法右分配（Qeq 环等式的分解微件——ring 对 Qeq 失效域的替代） *)
Lemma n1_opp_mul_distr : forall (y w : Q), ((- y) * w)%Q == Qopp (y * w)%Q.
Proof.
  intros y w. destruct y as [yn yd]; destruct w as [wn wd].
  unfold Qmult, Qopp, Qeq; cbn [Qnum Qden Qopp Qmult]. nia.
Qed.

Lemma n1_mul_sub_distr : forall (x y w : Q), ((x - y) * w)%Q == (x * w - y * w)%Q.
Proof.
  intros x y w. unfold Qminus.
  rewrite Qmult_plus_distr_l.
  rewrite (n1_opp_mul_distr y w).
  reflexivity.
Qed.

(* Qinv 保正 *)
Lemma n1_qinv_pos : forall u : Q, Qlt 0 u -> Qlt 0 (Qinv u).
Proof.
  intros u Hu. destruct u as [pu pd].
  unfold Qlt, Qinv in *; cbn [Qnum Qden Qinv] in *;
    destruct pu; cbn in *; lia.
Qed.

(* Z#1 正性 *)
Lemma n1_zpos1_pos : forall p : positive, Qlt 0 ((Z.pos p # 1)%Q).
Proof. intro p. unfold Qlt. cbn [Qnum Qden]. lia. Qed.

(* Qabs 对 Qeq 的同余（变换恒等式入 Qlt/Qle 面的桥） *)
Lemma n1_qabs_comp : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof. intros x y H. rewrite H. reflexivity. Qed.

(* Qeq 同余入 Qlt/Qle 三桥（Qlt/Qle 头下禁集态重写的替代通路） *)
Lemma n1_qlt_comp : forall (u v w : Q), u == v -> Qlt v w -> Qlt u w.
Proof.
  intros u v w Huv Hvw. apply (Qle_lt_trans u v w).
  - apply qeq_imp_qle. exact Huv.
  - exact Hvw.
Qed.

Lemma n1_qlt_comp_r : forall (u v w : Q), v == w -> Qlt u v -> Qlt u w.
Proof.
  intros u v w Hvw Huv. apply (Qlt_le_trans u v w).
  - exact Huv.
  - apply qeq_imp_qle. exact Hvw.
Qed.

Lemma n1_qle_comp_r : forall (u v w : Q), v == w -> Qle u v -> Qle u w.
Proof.
  intros u v w Hvw Huv. apply (Qle_trans u v w).
  - exact Huv.
  - apply qeq_imp_qle. exact Hvw.
Qed.

(* e(n) ≥ 0 *)
Lemma n1_e_ge0 : forall n : nat, Qle 0 (ir2_e n).
Proof.
  intro n. unfold ir2_e.
  apply (Qle_trans 0%Q (((1 # 2) * 0%Q)%Q)).
  - apply qeq_le. reflexivity.
  - apply (ir2_mult_le_compat_l 0%Q (ir2_delta n) (1 # 2));
      [exact (ir2_delta_ge0 n) | unfold Qle; cbn [Qnum Qden]; lia].
Qed.

(* 正乘非负 *)
Lemma n1_posmul_ge0 : forall (s e : Q), Qlt 0 s -> Qle 0 e -> Qle 0 (s * e)%Q.
Proof.
  intros s e Hs He.
  destruct (Qlt_le_dec 0 e) as [Hep | Hen].
  - apply Qlt_le_weak. apply Qmult_lt_0_compat; assumption.
  - assert (He0 : e == 0%Q) by (apply Qle_antisym; assumption).
    rewrite He0, Qmult_0_r. apply Qle_refl.
Qed.



(* 数值见证（复算律）：x(1) = 3/2、1/x(1) = 2/3、e(1) = 1/8 *)
Lemma n1_x1 : ir2_x 1 == (3 # 2)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma n1_inv1 : Qinv (ir2_x 1) == (2 # 3)%Q.
Proof. rewrite n1_x1. vm_compute. reflexivity. Qed.

Lemma n1_e1 : ir2_e 1 == (1 # 8)%Q.
Proof. unfold ir2_e, ir2_delta. rewrite n1_x1. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* S1：平移族 x ↦ x + k（k:Z）——常元 1/(12b²) 钉定不变                  *)
(* ============================================================ *)

Lemma n1_shift_tail : forall k : Z,
  lic_tail_bounded (fun n => (ir2_x n + (k # 1))%Q) ir2_e.
Proof.
  intro k. red. intros n j Hn Hj.
  apply Qlt_to_QltT.
  assert (HEq : ((ir2_x j + (k # 1))%Q - (ir2_x n + (k # 1))%Q)%Q
                == (ir2_x j - ir2_x n)%Q)
    by (unfold Qminus, Qplus, Qopp, Qmult, Qeq;
        cbn [Qnum Qden Qplus Qopp Qminus]; nia).
  rewrite HEq. apply QltT_to_Qlt. apply ir2_tail; assumption.
Qed.

Lemma n1_shift_atom : forall (a k : Z) (b : positive),
  ((a # b)%Q - (k # 1))%Q == ((a - k * Z.pos b) # b)%Q.
Proof.
  intros a k b.
  unfold Qminus, Qplus, Qopp, Qmult, Qeq.
  cbn [Qnum Qden Qplus Qopp Qmult].
  nia.
Qed.

(* 主定理一（平移）：证书常元逐字不变——钉定恒等式首例 *)
Theorem n1_shift_measure : forall (k a : Z) (b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (12 * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u)
                                 (fun n => (ir2_x n + (k # 1))%Q)
                                 (lic_seq_cauchy (fun n => (ir2_x n + (k # 1))%Q)
                                                 ir2_e (n1_shift_tail k) ir2_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros k a b.
  destruct (dmew_escape_closed_window (a - k * Z.pos b) b) as [n0 [Hn3 Hesc]].
  assert (Hn01 : (1 <= n0)%nat) by lia.
  assert (Heb : QleT' (ir2_e n0) ((1 # (12 * (b * b)))%Q)).
  { apply Qle_to_QleT'.
    apply (Qle_trans (ir2_e n0) (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))
            (1 # (12 * (b * b)))%Q).
    - apply QleT'_to_Qle. exact (dmew_e_bnd b n0 Hn3).
    - apply qeq_le.
      replace (12 * (Z.pos b * Z.pos b))%Z with (Z.pos (12 * (b * b)))%Z
        by (rewrite (Pos2Z.inj_mul 12 (b * b)); rewrite (Pos2Z.inj_mul b b);
            reflexivity).
      reflexivity. }
  assert (HEk : ((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q
                == (((a - k * Z.pos b) # b)%Q - ir2_x n0)%Q).
  { transitivity ((((a # b)%Q - (k # 1))%Q - ir2_x n0)%Q).
    - ring.
    - rewrite (n1_shift_atom a k b). reflexivity. }
  assert (Hesc' : QltT (ir2_e n0)
            (Qabs (((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q))).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans (ir2_e n0)
            (Qabs (((a - k * Z.pos b) # b)%Q - ir2_x n0)%Q)
            (Qabs (((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q))).
    - apply QltT_to_Qlt. exact Hesc.
    - apply qeq_imp_qle.
      rewrite (n1_qabs_comp _ _ HEk). reflexivity. }
  pose proof (dmcm_margin_closed (a - k * Z.pos b) b n0 Hn01 Heb) as HrawT.
  pose proof (QleT'_to_Qle _ _ HrawT) as Hraw.
  rewrite <- (lic_qlt_minus_add_r
                (Qabs ((((a - k * Z.pos b) # b)%Q - ir2_x n0)%Q))
                (ir2_e n0)) in Hraw.
  assert (Hmargin : QleT' (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q))
                          (((Qabs (((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q))
                             - ir2_e n0)%Q)).
  { apply (dmcm_qle_add_cancel_r _ _ (ir2_e n0)).
    apply Qle_to_QleT'.
    apply (Qle_trans (((1 # (12 * (b * b)))%Q
                        + (1 # (12 * (b * b)))%Q
                        + ir2_e n0)%Q)
            ((((Qabs (((a - k * Z.pos b) # b)%Q - ir2_x n0)%Q))
                - ir2_e n0)%Q + ir2_e n0)%Q
            ((((Qabs (((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q))
                - ir2_e n0)%Q) + ir2_e n0)%Q).
    - exact Hraw.
    - apply qeq_imp_qle.
      rewrite (lic_qlt_minus_add_r
                (Qabs (((a - k * Z.pos b) # b)%Q - ir2_x n0)%Q) (ir2_e n0)).
      rewrite (lic_qlt_minus_add_r
                (Qabs (((a # b)%Q - (ir2_x n0 + (k # 1))%Q)%Q)) (ir2_e n0)).
      rewrite (n1_qabs_comp _ _ HEk). reflexivity. }
  assert (Hc0 : QltT 0 ((1 # (12 * (b * b)))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). lia. }
  exists ((1 # (12 * (b * b)))%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (projT2 (dmec_escape_to_dist_any
             (fun n => (ir2_x n + (k # 1))%Q) ir2_e (n1_shift_tail k) ir2_vanish
             ((a # b)%Q) n0 Hn01 Hesc' ((1 # (12 * (b * b)))%Q) Hc0 Hmargin))).
Qed.

(* ============================================================ *)
(* S2：数乘族 x ↦ k·x（k:positive）——常元 1/(12·k·b²)                   *)
(* ============================================================ *)

Lemma n1_scale_tail : forall k : positive,
  lic_tail_bounded (fun n => ir2_x n * (Z.pos k # 1)%Q)
                   (fun n => ir2_e n * (Z.pos k # 1)%Q).
Proof.
  intro k. red. intros n j Hn Hj.
  assert (Hs0 : Qlt 0 ((Z.pos k # 1)%Q)) by apply n1_zpos1_pos.
  apply Qlt_to_QltT.
  assert (HEq : ((ir2_x j * (Z.pos k # 1))%Q - (ir2_x n * (Z.pos k # 1))%Q)%Q
                == ((ir2_x j - ir2_x n) * (Z.pos k # 1))%Q)
    by (unfold Qminus, Qplus, Qopp, Qmult, Qeq;
        cbn [Qnum Qden Qplus Qopp Qminus Qmult]; nia).
  rewrite HEq. rewrite (n1_abs_scale _ _ Hs0).
  apply Qmult_lt_compat_r.
  - exact Hs0.
  - apply QltT_to_Qlt. apply ir2_tail; assumption.
Qed.

Lemma n1_scale_vanish : forall k : positive,
  lic_vanish (fun n => ir2_e n * (Z.pos k # 1)%Q).
Proof.
  intros k. red. intros eps Heps.
  assert (Hs0 : Qlt 0 ((Z.pos k # 1)%Q)) by apply n1_zpos1_pos.
  assert (Hsn0 : ~ ((Z.pos k # 1)%Q == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 ((Z.pos k # 1)%Q) Hs0). apply Qeq_sym. exact Hc. }
  assert (Hthr : QltT 0 ((eps * Qinv ((Z.pos k # 1))%Q)%Q)).
  { apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Heps).
    - apply n1_qinv_pos. exact Hs0. }
  destruct (ir2_vanish ((eps * Qinv ((Z.pos k # 1))%Q)%Q) Hthr) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ (HN n Hn)) as Hlt.
  apply (Qlt_le_trans (ir2_e n * (Z.pos k # 1))%Q
           ((eps * Qinv ((Z.pos k # 1))%Q) * (Z.pos k # 1))%Q eps).
  - apply Qmult_lt_compat_r; [exact Hs0 | exact Hlt].
  - apply qeq_imp_qle.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (Qinv ((Z.pos k # 1))%Q) ((Z.pos k # 1)%Q)).
    rewrite (Qmult_inv_r _ Hsn0). rewrite Qmult_1_r. apply Qeq_refl.
Qed.

Theorem n1_scale_measure : forall (k : positive) (a : Z) (b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (12 * k * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u)
                                 (fun n => ir2_x n * (Z.pos k # 1)%Q)
                                 (lic_seq_cauchy (fun n => ir2_x n * (Z.pos k # 1)%Q)
                                                 (fun n => ir2_e n * (Z.pos k # 1)%Q)
                                                 (n1_scale_tail k) (n1_scale_vanish k)))
               (real_const ((a # b)%Q)))))).
Proof.
  intros k a b.
  assert (Hs0 : Qlt 0 ((Z.pos k # 1)%Q)) by apply n1_zpos1_pos.
  destruct (dmew_escape_closed_window a (k * b)) as [n0 [Hn3 Hesc]].
  assert (Hn01 : (1 <= n0)%nat) by lia.
  assert (Heb : QleT' (ir2_e n0) ((1 # (12 * ((k * b) * (k * b))))%Q)).
  { apply Qle_to_QleT'.
    apply (Qle_trans (ir2_e n0)
            (Qinv ((12 * (Z.pos (k * b) * Z.pos (k * b)) # 1)))
            (1 # (12 * ((k * b) * (k * b))))%Q).
    - apply QleT'_to_Qle. exact (dmew_e_bnd (k * b) n0 Hn3).
    - apply qeq_le.
      replace (12 * (Z.pos (k * b) * Z.pos (k * b)))%Z
        with (Z.pos (12 * ((k * b) * (k * b))))%Z
        by (rewrite (Pos2Z.inj_mul 12 ((k * b) * (k * b)));
            rewrite (Pos2Z.inj_mul (k * b) (k * b)); reflexivity).
      reflexivity. }
  pose proof (dmcm_margin_closed a (k * b) n0 Hn01 Heb) as HrawT.
  assert (HA : ((a # (k * b))%Q * (Z.pos k # 1)%Q) == (a # b)%Q).
  { unfold Qmult, Qeq. cbn [Qmult Qnum Qden Pos.mul].
    rewrite (Pos.mul_1_r (k * b)).
    rewrite (Pos2Z.inj_mul k b). nia. }
  assert (HEs : ((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q
                == (((a # (k * b))%Q - ir2_x n0) * (Z.pos k # 1))%Q).
  { rewrite <- HA. ring. }
  assert (Hesc' : QltT ((ir2_e n0 * (Z.pos k # 1))%Q)
            (Qabs (((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q))).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans ((ir2_e n0 * (Z.pos k # 1))%Q)
            (Qabs ((((a # (k * b))%Q - ir2_x n0)) * (Z.pos k # 1))%Q)
            (Qabs (((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q))).
    - rewrite (n1_abs_scale _ _ Hs0).
      apply Qmult_lt_compat_r; [exact Hs0 | apply QltT_to_Qlt; exact Hesc].
    - apply qeq_imp_qle.
      rewrite (n1_qabs_comp _ _ HEs). reflexivity. }
  assert (HQ2 : ((Z.pos k # 1)%Q * (1 # (12 * ((k * b) * (k * b))))%Q)
                == (1 # (12 * k * (b * b)))%Q).
  { unfold Qmult, Qeq. cbn [Qmult Qnum Qden Pos.mul].
    rewrite ?Pos.mul_1_r.
    rewrite ?(Pos2Z.inj_mul (k * b) (k * b)).
    rewrite ?(Pos2Z.inj_mul k b). nia. }
  assert (Hmargin : QleT' (((1 # (12 * k * (b * b)))%Q
                              + (1 # (12 * k * (b * b)))%Q))
                         (((Qabs (((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q))
                            - (ir2_e n0 * (Z.pos k # 1))%Q)%Q)).
  { pose proof (QleT'_to_Qle _ _ HrawT) as Hm.
    pose proof (ir2_mult_le_compat_l _ _ (Z.pos k # 1) Hm
                  (Qlt_le_weak 0 (Z.pos k # 1) Hs0)) as HM.
    assert (HQ3 : ((Z.pos k # 1)%Q * (((1 # (12 * ((k * b) * (k * b))))%Q
                     + (1 # (12 * ((k * b) * (k * b))))%Q + ir2_e n0)%Q))%Q
                  == (((1 # (12 * k * (b * b)))%Q + (1 # (12 * k * (b * b)))%Q
                        + (ir2_e n0 * (Z.pos k # 1))%Q))%Q).
    { transitivity (((Z.pos k # 1)%Q * (1 # (12 * ((k * b) * (k * b))))%Q
                      + (Z.pos k # 1)%Q * (1 # (12 * ((k * b) * (k * b))))%Q
                      + (Z.pos k # 1)%Q * ir2_e n0)%Q).
      - ring.
      - rewrite HQ2, (Qmult_comm (Z.pos k # 1) (ir2_e n0)). reflexivity. }
    rewrite HQ3 in HM.
    rewrite (Qmult_comm (Z.pos k # 1)
              (Qabs (((a # (k * b))%Q - ir2_x n0)%Q))) in HM.
    assert (HmT : QleT' (((1 # (12 * k * (b * b)))%Q
                            + (1 # (12 * k * (b * b)))%Q
                            + (ir2_e n0 * (Z.pos k # 1))%Q))
                       ((Qabs (((a # (k * b))%Q - ir2_x n0)%Q))
                          * (Z.pos k # 1))%Q)
      by (apply Qle_to_QleT'; exact HM).
    apply (dmcm_qle_add_cancel_r _ _ ((ir2_e n0 * (Z.pos k # 1))%Q)).
    apply Qle_to_QleT'.
    apply (Qle_trans
            (((1 # (12 * k * (b * b)))%Q + (1 # (12 * k * (b * b)))%Q
              + (ir2_e n0 * (Z.pos k # 1))%Q)%Q)
            ((Qabs (((a # (k * b))%Q - ir2_x n0)%Q) * (Z.pos k # 1)%Q
              - (ir2_e n0 * (Z.pos k # 1))%Q
              + (ir2_e n0 * (Z.pos k # 1))%Q)%Q)
            ((Qabs (((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q)
              - (ir2_e n0 * (Z.pos k # 1))%Q
              + (ir2_e n0 * (Z.pos k # 1))%Q)%Q)).
    - pose proof (QleT'_to_Qle _ _ HmT) as HmQ.
      rewrite <- (lic_qlt_minus_add_r
                  ((Qabs (((a # (k * b))%Q - ir2_x n0)%Q)) * (Z.pos k # 1))%Q
                  ((ir2_e n0 * (Z.pos k # 1))%Q)) in HmQ.
      exact HmQ.
    - apply qeq_imp_qle.
      rewrite (lic_qlt_minus_add_r
                ((Qabs (((a # (k * b))%Q - ir2_x n0)%Q)) * (Z.pos k # 1))%Q
                ((ir2_e n0 * (Z.pos k # 1))%Q)).
      rewrite (lic_qlt_minus_add_r
                (Qabs (((a # b)%Q - ir2_x n0 * (Z.pos k # 1))%Q))
                ((ir2_e n0 * (Z.pos k # 1))%Q)).
      apply Qeq_sym.
      rewrite (n1_qabs_comp _ _ HEs).
      apply n1_abs_scale. exact Hs0. }
  assert (Hc0 : QltT 0 ((1 # (12 * k * (b * b)))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul.
    pose proof (Pos2Z.is_pos b). pose proof (Pos2Z.is_pos k). lia. }
  exists ((1 # (12 * k * (b * b)))%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (projT2 (dmec_escape_to_dist_any
             (fun n => ir2_x n * (Z.pos k # 1)%Q)
             (fun n => ir2_e n * (Z.pos k # 1)%Q)
             (n1_scale_tail k) (n1_scale_vanish k)
             ((a # b)%Q) n0 Hn01 Hesc' ((1 # (12 * k * (b * b)))%Q) Hc0 Hmargin))).
Qed.

(* ============================================================ *)
(* S3：倒数族 x ↦ 1/x——三分钉定                                          *)
(* ============================================================ *)

(* 倒数序列尾控：|1/x_j − 1/x_n| ≤ |x_j − x_n|·Qinv(x_j·x_n) < (3/5)·e(n) *)
Lemma n1_inv_tail :
  lic_tail_bounded (fun n => Qinv (ir2_x n)) (fun n => ((3 # 5) * ir2_e n)%Q).
Proof.
  red. intros n j Hn Hj.
  assert (Hjn : Qlt 0 (ir2_x n)).
  { apply (Qlt_le_trans 0%Q (7 # 5) (ir2_x n));
      [unfold Qlt; cbn; lia | apply ir2_x_lb]. }
  assert (Hjj : Qlt 0 (ir2_x j)).
  { apply (Qlt_le_trans 0%Q (7 # 5) (ir2_x j));
      [unfold Qlt; cbn; lia | apply ir2_x_lb]. }
  assert (Hjn0 : ~ (ir2_x j == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 (ir2_x j) Hjj). apply Qeq_sym. exact Hc. }
  assert (Hnn0 : ~ (ir2_x n == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 (ir2_x n) Hjn). apply Qeq_sym. exact Hc. }
  assert (Huv0 : ~ ((ir2_x j * ir2_x n)%Q == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 (ir2_x j * ir2_x n)%Q
                   (Qmult_lt_0_compat (ir2_x j) (ir2_x n) Hjj Hjn)).
    apply Qeq_sym. exact Hc. }
  assert (Hdif : (Qinv (ir2_x j) - Qinv (ir2_x n))%Q
                 == ((ir2_x n - ir2_x j) * Qinv (ir2_x j * ir2_x n))%Q).
  { assert (HT1 : (ir2_x j * (Qinv (ir2_x j) * Qinv (ir2_x n)))%Q
                  == Qinv (ir2_x n)%Q).
    { rewrite Qmult_assoc. rewrite (Qmult_inv_r (ir2_x j) Hjn0).
      apply Qmult_1_l. }
    assert (HT2 : (ir2_x n * (Qinv (ir2_x j) * Qinv (ir2_x n)))%Q
                  == Qinv (ir2_x j)%Q).
    { rewrite Qmult_assoc, (Qmult_comm (ir2_x n) (Qinv (ir2_x j))).
      rewrite <- Qmult_assoc. rewrite (Qmult_inv_r (ir2_x n) Hnn0).
      apply Qmult_1_r. }
    rewrite (Qinv_mult_distr (ir2_x j) (ir2_x n)).
    rewrite (n1_mul_sub_distr (ir2_x n) (ir2_x j)
               (Qinv (ir2_x j) * Qinv (ir2_x n))).
    rewrite HT2, HT1. reflexivity. }
  assert (Hshift : Qlt (Qabs (((ir2_x n - ir2_x j) * Qinv (ir2_x j * ir2_x n))%Q))
                     ((ir2_e n) * Qinv (ir2_x j * ir2_x n)%Q)%Q).
  { rewrite (n1_abs_scale _ _ (n1_qinv_pos _
              (Qmult_lt_0_compat (ir2_x j) (ir2_x n) Hjj Hjn))).
    rewrite (Qabs_Qminus (ir2_x n) (ir2_x j)).
    apply Qmult_lt_compat_r.
    - apply n1_qinv_pos. apply Qmult_lt_0_compat; assumption.
    - apply QltT_to_Qlt. apply ir2_tail; assumption. }
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (Qabs ((Qinv (ir2_x j) - Qinv (ir2_x n))%Q))
          ((ir2_e n) * Qinv (ir2_x j * ir2_x n)%Q)%Q
          (((3 # 5) * ir2_e n)%Q)).
  - rewrite (n1_qabs_comp _ _ (Qeq_sym _ _ Hdif)) in Hshift. exact Hshift.
  - apply (Qle_trans ((ir2_e n) * Qinv (ir2_x j * ir2_x n)%Q)%Q
            ((ir2_e n) * (25 # 49)%Q) (((3 # 5) * ir2_e n)%Q)).
    + apply (ir2_mult_le_compat_l (Qinv (ir2_x j * ir2_x n)) (25 # 49) (ir2_e n)).
      * apply (ir2_inv_le (49 # 25) (ir2_x j * ir2_x n)).
        -- unfold Qlt. cbn. lia.
        -- apply (Qle_trans (49 # 25)%Q ((7 # 5) * (7 # 5))%Q
                    (ir2_x j * ir2_x n)%Q).
           ++ unfold Qle. cbn [Qnum Qden Qmult]. lia.
           ++ apply (Qle_trans ((7 # 5) * (7 # 5))%Q
                     ((7 # 5) * ir2_x j)%Q (ir2_x j * ir2_x n)%Q).
              ** apply (ir2_mult_le_compat_l (7 # 5) (ir2_x j) (7 # 5));
                   [apply ir2_x_lb | unfold Qle; cbn; lia].
              ** rewrite (Qmult_comm (ir2_x j) (ir2_x n)).
                 apply Qmult_le_compat_r;
                   [apply ir2_x_lb | apply Qlt_le_weak; apply ir2_x_pos].
      * exact (n1_e_ge0 n).
    + rewrite (Qmult_comm (3 # 5) (ir2_e n)).
      apply (ir2_mult_le_compat_l (25 # 49) (3 # 5) (ir2_e n)).
      * unfold Qle. cbn. lia.
      * exact (n1_e_ge0 n).
Qed.

Lemma n1_inv_vanish : lic_vanish (fun n => ((3 # 5) * ir2_e n)%Q).
Proof.
  red. intros eps Heps.
  assert (Hthr : QltT 0 (((5 # 3) * eps)%Q)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - unfold Qlt. cbn. lia.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (ir2_vanish (((5 # 3) * eps)%Q) Hthr) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ (HN n Hn)) as Hlt.
  apply (Qlt_le_trans (((3 # 5) * ir2_e n)%Q)
           (((3 # 5) * ((5 # 3) * eps))%Q) eps).
  - rewrite (Qmult_comm (3 # 5) (ir2_e n)), (Qmult_comm (3 # 5) ((5 # 3) * eps)).
    apply Qmult_lt_compat_r; [unfold Qlt; cbn; lia | exact Hlt].
  - apply qeq_imp_qle.
    assert (Heq : ((3 # 5) * (5 # 3))%Q == 1%Q)
      by (unfold Qeq; cbn [Qnum Qden Qmult]; lia).
    rewrite Qmult_assoc, Heq. apply Qmult_1_l.
Qed.

(* ---------- 倒数档 1：a ≤ 0（n0 = 1 统一窗·常元 1/4） ---------- *)

Theorem n1_inv_nonpos_measure : forall (a : Z) (b : positive),
  (a <= 0)%Z ->
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # 4)%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u)
                                 (fun n => Qinv (ir2_x n))
                                 (lic_seq_cauchy (fun n => Qinv (ir2_x n))
                                                 (fun n => ((3 # 5) * ir2_e n)%Q)
                                                 n1_inv_tail n1_inv_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros a b Ha.
  assert (Hnb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hxb : (a # b)%Q <= 0%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Habs : Qabs (((a # b)%Q - (2 # 3))%Q) == ((2 # 3)%Q - (a # b)%Q)%Q).
  { rewrite (Qabs_Qminus (a # b) (2 # 3)).
    apply Qabs_pos. unfold Qle, Qminus, Qplus, Qopp.
    cbn [Qnum Qden Qminus Qplus Qopp]. lia. }
  assert (HEq1 : ((2 # 3)%Q - (a # b)%Q)
                 == (Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))).
  { transitivity (Qabs (((a # b)%Q - (2 # 3))%Q)).
    - apply Qeq_sym. exact Habs.
    - apply n1_qabs_comp. rewrite n1_inv1. reflexivity. }
  assert (Hesc' : QltT (((3 # 5) * ir2_e 1)%Q)
            (Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))).
  { apply Qlt_to_QltT.
    apply (n1_qlt_comp ((3 # 5) * ir2_e 1)%Q ((3 # 5) * (1 # 8))%Q
             (Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))).
    - rewrite n1_e1. reflexivity.
    - apply (n1_qlt_comp_r ((3 # 5) * (1 # 8))%Q
               ((2 # 3)%Q - (a # b)%Q)
               (Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))).
      + exact HEq1.
      + unfold Qlt, Qminus. cbn [Qnum Qden Qminus Qplus Qopp Qmult]. lia. }
  assert (Hmargin : QleT' (((1 # 4)%Q + (1 # 4)%Q))
                          (((Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))
                             - ((3 # 5) * ir2_e 1)%Q)%Q)).
  { apply Qle_to_QleT'.
    apply (n1_qle_comp_r (((1 # 4)%Q + (1 # 4)%Q))
             ((((2 # 3)%Q - (a # b)%Q) - ((3 # 5) * (1 # 8))%Q)%Q)
             (((Qabs (((a # b)%Q - Qinv (ir2_x 1))%Q))
                 - ((3 # 5) * ir2_e 1)%Q)%Q)).
    - transitivity (((2 # 3)%Q - (a # b)%Q)
                      - ((3 # 5) * ir2_e 1)%Q)%Q.
      + rewrite <- n1_e1. reflexivity.
      + rewrite HEq1. reflexivity.
    - unfold Qle, Qminus, Qplus. cbn [Qnum Qden Qminus Qplus Qopp Qmult]. lia. }
  assert (Hc0 : QltT 0 ((1 # 4)%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  exists ((1 # 4)%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (projT2 (dmec_escape_to_dist_any
             (fun n => Qinv (ir2_x n)) (fun n => ((3 # 5) * ir2_e n)%Q)
             n1_inv_tail n1_inv_vanish
             ((a # b)%Q) 1 (Nat.le_refl 1) Hesc' ((1 # 4)%Q) Hc0 Hmargin))).
Qed.

(* ---------- 倒数档 2：a = p > 0（双窗·常元 1/(36·p·b)） ---------- *)

(* 案 B 尾链：(3/5 − T)·e ≤ (1/(12p))·Qinv(x·b)（1/(20b²) 与 1/(18pb) 双中继） *)
Lemma n1_caseB_tail : forall (p b : positive) (n0 : nat),
  (10 * Z.pos p < 9 * Z.pos b)%Z ->
  Qle 0 (ir2_e n0) -> ir2_e n0 <= (1 # (12 * (b * b)))%Q ->
  Qle (2 # (3 * b))%Q (Qinv (ir2_x n0 * (Z.pos b # 1))%Q) ->
  Qle (((3 # 5)%Q - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q)) * ir2_e n0%Q)
      ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q).
Proof.
  intros p b n0 H109 He0 Heb_b' HsLB.
  assert (Hq1 : (1 # (20 * (b * b)))%Q
                == ((3 # 5)%Q * (1 # (12 * (b * b)))%Q)).
  { apply Qeq_sym. unfold Qmult, Qeq. cbn [Qnum Qden Qmult].
    rewrite (Pos2Z.inj_mul 20 (b * b)).
    rewrite (Pos2Z.inj_mul 5 (12 * (b * b))).
    rewrite (Pos2Z.inj_mul 12 (b * b)).
    lia. }
  assert (Hq2 : (1 # (18 * (p * b)))%Q
                == ((1 # (12 * p))%Q * (2 # (3 * b))%Q)).
  { unfold Qmult, Qeq. cbn [Qnum Qden Qmult].
    rewrite ?(Pos2Z.inj_mul 18 (p * b)).
    rewrite ?(Pos2Z.inj_mul p b).
    rewrite ?(Pos2Z.inj_mul 12 p).
    rewrite ?(Pos2Z.inj_mul 3 b).
    unfold Qle, Qmult. cbn [Qnum Qden Qmult].
    pose proof (Pos2Z.is_pos b). pose proof (Pos2Z.is_pos p). nia. }
  assert (Hhop1 : Qle (((3 # 5)%Q - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q))
                          * ir2_e n0%Q)
                       ((3 # 5)%Q * (1 # (12 * (b * b)))%Q)).
  { apply (Qle_trans _ ((3 # 5)%Q * ir2_e n0)%Q).
    - apply (Qle_trans _ (((3 # 5)%Q * ir2_e n0)%Q
                             - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q)
                               * ir2_e n0%Q)%Q).
      * apply qeq_imp_qle.
        rewrite <- (n1_mul_sub_distr (3 # 5)
                      ((Z.pos p # 1)%Q * (2 # (3 * b))%Q) (ir2_e n0)).
        reflexivity.
      * apply n1_qle_minus_le.
        apply n1_posmul_ge0.
        -- apply Qmult_lt_0_compat;
             [ apply n1_zpos1_pos | unfold Qlt; cbn; lia ].
        -- exact He0.
    - apply (ir2_mult_le_compat_l (ir2_e n0) (1 # (12 * (b * b))) (3 # 5));
        [ exact Heb_b' | unfold Qle; cbn; lia ]. }
  assert (Hhop2 : Qle (1 # (20 * (b * b)))%Q
                       ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
  { apply (Qle_trans _ (1 # (18 * (p * b)))%Q).
    - unfold Qle. cbn [Qnum Qden].
      pose proof (Pos2Z.is_pos b). pose proof (Pos2Z.is_pos p).
      pose proof H109. nia.
    - apply (Qle_trans _ ((1 # (12 * p))%Q * (2 # (3 * b))%Q)).
      + apply qeq_imp_qle. exact Hq2.
      + apply (ir2_mult_le_compat_l (2 # (3 * b))
                  (Qinv (ir2_x n0 * (Z.pos b # 1))) (1 # (12 * p)));
          [ exact HsLB | unfold Qle; cbn; lia ]. }
  apply (Qle_trans _ (1 # (20 * (b * b)))%Q).
  - apply (Qle_trans _ ((3 # 5)%Q * (1 # (12 * (b * b)))%Q)).
    + exact Hhop1.
    + apply qeq_imp_qle. symmetry. exact Hq1.
  - exact Hhop2.
Qed.

Lemma n1_inv_pos_margin : forall (p b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  (Z.to_nat (Z.pos b) + 3 <= n0)%nat ->
  (Z.to_nat (Z.pos p) + 3 <= n0)%nat ->
  QleT' ((((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
            + ((3 # 5) * ir2_e n0)%Q)%Q)
        (Qabs (((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q)).
Proof.
  intros p b n0 Hn01 Hb3 Hp3.
  assert (Hb1 : Qlt 0 ((Z.pos b # 1)%Q)) by apply n1_zpos1_pos.
  assert (Hp1 : Qlt 0 ((Z.pos p # 1)%Q)) by apply n1_zpos1_pos.
  assert (Hxub : Qle (ir2_x n0) ((3 # 2)%Q)) by (apply (ir2_x_ub n0); exact Hn01).
  assert (Hxb : Qle (ir2_x n0 * (Z.pos b # 1))%Q
                    (((3 # 2) * (Z.pos b # 1))%Q)).
  { apply Qmult_le_compat_r; [exact Hxub | apply Qlt_le_weak; exact Hb1]. }
  assert (Hxs : Qlt 0 (ir2_x n0 * (Z.pos b # 1))%Q).
  { apply Qmult_lt_0_compat; [apply ir2_x_pos | exact Hb1]. }
  assert (Hs0 : Qlt 0 (Qinv (ir2_x n0 * (Z.pos b # 1))%Q))
    by (apply n1_qinv_pos; exact Hxs).
  assert (Hsn0 : ~ ((ir2_x n0 * (Z.pos b # 1))%Q == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 _ Hxs). apply Qeq_sym. exact Hc. }
  assert (HsLB : Qle ((2 # (3 * b))%Q) (Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
  { assert (Hq : Qinv (((3 # 2) * (Z.pos b # 1))%Q) == (2 # (3 * b))%Q).
    { unfold Qmult, Qinv, Qeq.
      cbn [Qnum Qden Qmult Qinv Pos.mul Z.abs_nat]. reflexivity. }
    apply (Qle_trans (2 # (3 * b))%Q (Qinv ((3 # 2) * (Z.pos b # 1))%Q)
             (Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
    - apply qeq_imp_qle. exact Hq.
    - apply (ir2_inv_le (ir2_x n0 * (Z.pos b # 1))%Q
               (((3 # 2) * (Z.pos b # 1))%Q)).
      + exact Hxs.
      + exact Hxb. }
  assert (HAb : ((Z.pos p # b)%Q * (Z.pos b # 1)%Q) == (Z.pos p # 1)%Q).
  { unfold Qmult, Qeq. cbn [Qmult Qnum Qden Pos.mul].
    rewrite ?Pos.mul_1_r. nia. }
  assert (Hx0 : ~ (ir2_x n0 == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 _ (ir2_x_pos n0)). apply Qeq_sym. exact Hc. }
  (* 主恒等式 HEq *)
  assert (HEq : ((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q
    == (((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)
        * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q).
  { assert (HT0 : ((Z.pos p # b)%Q * (ir2_x n0 * (Z.pos b # 1)))%Q
                  == ((Z.pos p # 1)%Q * ir2_x n0)%Q).
    { rewrite Qmult_assoc. rewrite (Qmult_comm (Z.pos p # b) (ir2_x n0)).
      rewrite <- Qmult_assoc. rewrite HAb.
      rewrite (Qmult_comm (ir2_x n0) (Z.pos p # 1)). reflexivity. }
    assert (HT1 : (Qinv (ir2_x n0) * (ir2_x n0 * (Z.pos b # 1)))%Q
                  == (Z.pos b # 1)%Q).
    { rewrite Qmult_assoc. rewrite (Qmult_comm (Qinv (ir2_x n0)) (ir2_x n0)).
      rewrite (Qmult_inv_r (ir2_x n0) Hx0).
      apply Qmult_1_l. }
    assert (Hinner : ((((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q
                         * (ir2_x n0 * (Z.pos b # 1))%Q)%Q)
                     == ((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)%Q).
    { rewrite (n1_mul_sub_distr (Z.pos p # b)%Q (Qinv (ir2_x n0))
                (ir2_x n0 * (Z.pos b # 1))%Q).
      rewrite HT0. rewrite HT1. reflexivity. }
    transitivity ((((Z.pos p # b)%Q - Qinv (ir2_x n0))
                     * (ir2_x n0 * (Z.pos b # 1)))
                    * Qinv (ir2_x n0 * (Z.pos b # 1)))%Q.
    - apply n1_mul_cancel_r. exact Hsn0.
    - rewrite Hinner. reflexivity. }
  (* dmcm 于 (Z.pos b, p) *)
  assert (Heb_p : QleT' (ir2_e n0) ((1 # (12 * (p * p)))%Q)).
  { apply Qle_to_QleT'.
    apply (Qle_trans (ir2_e n0) (Qinv ((12 * (Z.pos p * Z.pos p)) # 1))
            (1 # (12 * (p * p)))%Q).
    - apply QleT'_to_Qle. exact (dmew_e_bnd p n0 Hp3).
    - apply qeq_le.
      replace (12 * (Z.pos p * Z.pos p))%Z with (Z.pos (12 * (p * p)))%Z
        by (rewrite (Pos2Z.inj_mul 12 (p * p)); rewrite (Pos2Z.inj_mul p p);
            reflexivity).
      reflexivity. }
  pose proof (dmcm_margin_closed (Z.pos b) p n0 Hn01 Heb_p) as HdmT.
  pose proof (QleT'_to_Qle _ _ HdmT) as Hdm.
  rewrite (Qabs_Qminus (Z.pos b # p) (ir2_x n0)) in Hdm.
  assert (Hstep1 : Qle ((((1 # (12 * (p * p)))%Q + (1 # (12 * (p * p)))%Q
                            + ir2_e n0)%Q) * (Z.pos p # 1))%Q
                       ((Qabs ((ir2_x n0 - (Z.pos b # p))%Q))
                          * (Z.pos p # 1))%Q).
  { apply Qmult_le_compat_r; [exact Hdm | apply Qlt_le_weak; exact Hp1]. }
  assert (Hc12 : ((1 # (12 * (p * p)))%Q * (Z.pos p # 1)%Q) == (1 # (12 * p))%Q).
  { unfold Qmult, Qeq. cbn [Qmult Qnum Qden Pos.mul].
    rewrite ?Pos.mul_1_r.
    rewrite ?(Pos2Z.inj_mul 12 (p * p)). rewrite ?(Pos2Z.inj_mul p p). nia. }
  assert (Hstep1x : Qle ((((1 # (12 * p))%Q + (1 # (12 * p))%Q)
                            + (ir2_e n0 * (Z.pos p # 1))%Q))
                         ((Qabs ((ir2_x n0 - (Z.pos b # p))%Q))
                            * (Z.pos p # 1))%Q).
  { pose proof Hstep1 as HH.
    assert (HE : ((((1 # (12 * (p * p)))%Q + (1 # (12 * (p * p)))%Q
                        + ir2_e n0)%Q) * (Z.pos p # 1))%Q
                  == ((((1 # (12 * (p * p)))%Q * (Z.pos p # 1))%Q
                        + ((1 # (12 * (p * p)))%Q * (Z.pos p # 1))%Q
                        + (ir2_e n0 * (Z.pos p # 1))%Q))%Q)
      by (unfold Qplus, Qmult, Qeq; cbn [Qnum Qden Qplus Qmult]; nia).
    rewrite HE in HH.
    rewrite Hc12 in HH. exact HH. }
  assert (Hstep2 : Qle ((((1 # (12 * p))%Q + (1 # (12 * p))%Q
                            + (ir2_e n0 * (Z.pos p # 1))%Q))
                          * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q
                       (((Qabs ((ir2_x n0 - (Z.pos b # p))%Q))
                           * (Z.pos p # 1))
                          * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q).
  { apply Qmult_le_compat_r; [exact Hstep1x | apply Qlt_le_weak; exact Hs0]. }
  (* |p·x − b| == |x − b/p|·(p#1) *)
  assert (HAbp : ((Z.pos p # 1)%Q * (Z.pos b # p)%Q) == (Z.pos b # 1)%Q).
  { unfold Qmult, Qeq. cbn [Qmult Qnum Qden Pos.mul].
    rewrite ?Pos.mul_1_r. nia. }
  assert (Habs2 : (Qabs ((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)%Q)
                  == ((Qabs ((ir2_x n0 - (Z.pos b # p))%Q))
                        * (Z.pos p # 1))%Q).
  { assert (HEq2 : ((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)%Q
                   == ((Z.pos p # 1)%Q * (ir2_x n0 - (Z.pos b # p))%Q)%Q).
    { rewrite <- HAbp. ring. }
    rewrite HEq2. rewrite (Qmult_comm (Z.pos p # 1) (ir2_x n0 - (Z.pos b # p))).
    rewrite (n1_abs_scale _ _ Hp1). reflexivity. }
  (* 展开三段 *)
  assert (HE3 : ((((1 # (12 * p))%Q + (1 # (12 * p))%Q
                       + (ir2_e n0 * (Z.pos p # 1))%Q))
                     * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q
                 == ((((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                       + ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                       + ((ir2_e n0 * (Z.pos p # 1))%Q
                            * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)))%Q)
    by (unfold Qplus, Qmult, Qeq; cbn [Qnum Qden Qplus Qmult]; nia).
  rewrite HE3 in Hstep2.
  assert (Hca : Qle ((1 # (36 * p * b))%Q)
                  ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
  { apply (Qle_trans _ ((1 # (12 * p))%Q * (2 # (3 * b))%Q)).
    - apply Qlt_le_weak. unfold Qlt. cbn [Qnum Qden Qmult].
      rewrite !Pos2Z.inj_mul. nia.
    - apply (ir2_mult_le_compat_l (2 # (3 * b))
              (Qinv (ir2_x n0 * (Z.pos b # 1))) (1 # (12 * p))).
      + exact HsLB.
      + unfold Qle. cbn. lia. }
  (* 段三：ρ 两案 *)
  assert (He0 : Qle 0 (ir2_e n0)) by exact (n1_e_ge0 n0).
  assert (HsGE : Qle (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
                     ((ir2_e n0 * (Z.pos p # 1)%Q)
                        * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
  { assert (HEa : ((ir2_e n0 * (Z.pos p # 1)%Q)
                    * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q
                  == ((Z.pos p # 1)%Q * ir2_e n0%Q
                        * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)
      by (unfold Qmult, Qeq; cbn [Qnum Qden Qmult]; nia).
    assert (HEb : (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)%Q
                  == ((Z.pos p # 1)%Q * ir2_e n0%Q * (2 # (3 * b))%Q)%Q)
      by (unfold Qmult, Qeq; cbn [Qnum Qden Qmult]; nia).
    rewrite HEa. rewrite HEb.
    apply (ir2_mult_le_compat_l (2 # (3 * b))
             (Qinv (ir2_x n0 * (Z.pos b # 1)))
             ((Z.pos p # 1)%Q * ir2_e n0)%Q);
    [ exact HsLB
    | apply n1_posmul_ge0; [exact Hp1 | exact He0] ]. }
  assert (Hpair : Qle (((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q))
                      ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
  { apply (Qle_trans _ ((1 # (12 * p))%Q * (2 # (3 * b))%Q)).
    - apply qeq_imp_qle. unfold Qle, Qplus, Qmult, Qeq.
      cbn [Qnum Qden Qplus Qmult]. nia.
    - apply (ir2_mult_le_compat_l (2 # (3 * b))
                (Qinv (ir2_x n0 * (Z.pos b # 1))) (1 # (12 * p)));
        [ exact HsLB | unfold Qle; cbn; lia ]. }
  destruct (Qlt_le_dec (((Z.pos p # 1)%Q * (2 # (3 * b))%Q)) ((3 # 5)%Q))
    as [HcaseB | HcaseA].
  - (* 案 B：T2p < 3/5 ⟹ 10p < 9b *)
    assert (H109 : (10 * Z.pos p < 9 * Z.pos b)%Z).
    { pose proof HcaseB as HH. unfold Qlt in HH.
      cbn [Qnum Qden Qmult] in HH. lia. }
    assert (Heb_b : QleT' (ir2_e n0) ((1 # (12 * (b * b)))%Q)).
    { apply Qle_to_QleT'.
      apply (Qle_trans (ir2_e n0) (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))
              (1 # (12 * (b * b)))%Q).
      - apply QleT'_to_Qle. exact (dmew_e_bnd b n0 Hb3).
      - apply qeq_le.
        replace (12 * (Z.pos b * Z.pos b))%Z with (Z.pos (12 * (b * b)))%Z
          by (rewrite (Pos2Z.inj_mul 12 (b * b)); rewrite (Pos2Z.inj_mul b b);
              reflexivity).
        reflexivity. }
    pose proof (QleT'_to_Qle _ _ Heb_b) as Heb_b'.
    assert (H3 : Qle (((3 # 5)%Q * ir2_e n0)%Q)
                   ((((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((ir2_e n0 * (Z.pos p # 1))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)))%Q).
    { assert (HEc : (((3 # 5)%Q * ir2_e n0)%Q)
        == ((((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
             + (((3 # 5)%Q - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q)))
                 * ir2_e n0%Q)%Q).
      apply Qeq_sym.
      rewrite (n1_mul_sub_distr (3 # 5)
                    ((Z.pos p # 1)%Q * (2 # (3 * b))%Q) (ir2_e n0)).
      rewrite (Qplus_comm (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
                (((3 # 5) * ir2_e n0)%Q
                   - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)).
      apply lic_qlt_minus_add_r.
      apply (Qle_trans _ ((((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
               + (((3 # 5)%Q - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q)))
                   * ir2_e n0%Q)%Q).
      - apply qeq_imp_qle. exact HEc.
      - rewrite (Qplus_comm
                  (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
                  ((((3 # 5)%Q - ((Z.pos p # 1)%Q * (2 # (3 * b))%Q)))
                     * ir2_e n0%Q)%Q).
        apply Qplus_le_compat.
        + apply (n1_caseB_tail p b n0 H109 He0 Heb_b' HsLB).
        + exact HsGE. }
    apply Qle_to_QleT'.
    apply (Qle_trans
            ((((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
                + ((3 # 5)%Q * ir2_e n0)%Q)%Q)
            (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
               + (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                    + ((ir2_e n0 * (Z.pos p # 1))%Q
                         * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)%Q)
            (Qabs (((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q))).
    + apply Qplus_le_compat.
      * exact Hpair.
      * exact H3.
    + apply (Qle_trans
              (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                 + (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((ir2_e n0 * (Z.pos p # 1))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)%Q)
              ((((Qabs ((ir2_x n0 - (Z.pos b # p))%Q) * (Z.pos p # 1))%Q)
                  * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)).
      * rewrite (Qplus_assoc ((1 # (12 * p))%Q
                                  * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                  ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                  ((ir2_e n0 * (Z.pos p # 1))%Q
                     * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
        exact Hstep2.
      * apply qeq_imp_qle.
        rewrite <- Habs2.
        rewrite <- (n1_abs_scale (Qinv (ir2_x n0 * (Z.pos b # 1)))
                      ((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)%Q Hs0).
        rewrite (n1_qabs_comp _ _ (Qeq_sym _ _ HEq)). reflexivity.
  - (* 案 A：T2p ≥ 3/5 *)
    assert (H3 : Qle (((3 # 5)%Q * ir2_e n0)%Q)
                   ((((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((ir2_e n0 * (Z.pos p # 1))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)))%Q).
    { apply (Qle_trans _ (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)).
      - apply Qmult_le_compat_r; [exact HcaseA | exact He0].
      - apply (Qle_trans (((Z.pos p # 1)%Q * (2 # (3 * b))%Q) * ir2_e n0%Q)
                ((ir2_e n0 * (Z.pos p # 1))%Q
                   * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                ((((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                    + ((ir2_e n0 * (Z.pos p # 1))%Q
                         * Qinv (ir2_x n0 * (Z.pos b # 1))%Q))%Q)).
        + exact HsGE.
        + apply (Qle_trans ((ir2_e n0 * (Z.pos p # 1))%Q
                              * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                  ((((ir2_e n0 * (Z.pos p # 1))%Q
                       * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((1 # (12 * p))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q))%Q)
                  ((((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((ir2_e n0 * (Z.pos p # 1))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q))%Q)).
          * apply (Qle_trans _ ((((ir2_e n0 * (Z.pos p # 1))%Q
                                    * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                                   + 0%Q)%Q)).
            -- apply qeq_imp_qle. apply Qeq_sym. apply Qplus_0_r.
            -- apply Qplus_le_compat;
                 [ apply Qle_refl
                 | apply n1_posmul_ge0; [exact Hp1 | apply Qlt_le_weak; exact Hs0] ].
          * apply qeq_imp_qle. apply Qplus_comm. }
    apply Qle_to_QleT'.
    apply (Qle_trans
            ((((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
                + ((3 # 5)%Q * ir2_e n0)%Q)%Q)
            (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
               + (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                    + ((ir2_e n0 * (Z.pos p # 1))%Q
                         * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)%Q)
            (Qabs (((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q))).
    + apply Qplus_le_compat.
      * exact Hpair.
      * exact H3.
    + apply (Qle_trans
              (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                 + (((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                      + ((ir2_e n0 * (Z.pos p # 1))%Q
                           * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)%Q)
              ((((Qabs ((ir2_x n0 - (Z.pos b # p))%Q) * (Z.pos p # 1))%Q)
                  * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)%Q)
              (Qabs (((Z.pos p # b)%Q - Qinv (ir2_x n0))%Q))).
      * rewrite (Qplus_assoc ((1 # (12 * p))%Q
                                  * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                  ((1 # (12 * p))%Q * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)
                  ((ir2_e n0 * (Z.pos p # 1))%Q
                     * Qinv (ir2_x n0 * (Z.pos b # 1))%Q)).
        exact Hstep2.
      * apply qeq_imp_qle.
        rewrite <- Habs2.
        rewrite <- (n1_abs_scale (Qinv (ir2_x n0 * (Z.pos b # 1)))
                      ((Z.pos p # 1)%Q * ir2_x n0 - (Z.pos b # 1)%Q)%Q Hs0).
        rewrite (n1_qabs_comp _ _ (Qeq_sym _ _ HEq)). reflexivity.
Qed.

Theorem n1_inv_pos_measure : forall (p b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (36 * p * b))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u)
                                 (fun n => Qinv (ir2_x n))
                                 (lic_seq_cauchy (fun n => Qinv (ir2_x n))
                                                 (fun n => ((3 # 5) * ir2_e n)%Q)
                                                 n1_inv_tail n1_inv_vanish))
               (real_const ((Z.pos p # b)%Q)))))).
Proof.
  intros p b.
  pose (m := (Z.to_nat (Z.pos b) + 3 + (Z.to_nat (Z.pos p) + 3))%nat).
  assert (Hm1 : (1 <= m)%nat) by (unfold m; lia).
  assert (Hmb3 : (Z.to_nat (Z.pos b) + 3 <= m)%nat) by (unfold m; lia).
  assert (Hmp3 : (Z.to_nat (Z.pos p) + 3 <= m)%nat) by (unfold m; lia).
  pose proof (n1_inv_pos_margin p b m Hm1 Hmb3 Hmp3) as HmargT.
  assert (Hc0 : QltT 0 ((1 # (36 * p * b))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul.
    pose proof (Pos2Z.is_pos b). pose proof (Pos2Z.is_pos p). lia. }
  assert (Hesc' : QltT (((3 # 5) * ir2_e m)%Q)
            (Qabs (((Z.pos p # b)%Q - Qinv (ir2_x m))%Q))).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans ((3 # 5) * ir2_e m)%Q
            (((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
               + ((3 # 5) * ir2_e m)%Q)%Q).
    - apply (n1_qlt_comp ((3 # 5) * ir2_e m)%Q
              (((3 # 5) * ir2_e m)%Q + 0%Q)%Q
              (((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
                 + ((3 # 5) * ir2_e m)%Q)%Q).
      + apply Qeq_sym. apply Qplus_0_r.
      + apply (Qlt_le_trans (((3 # 5) * ir2_e m)%Q + 0%Q)%Q
                (((3 # 5) * ir2_e m)%Q
                   + ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q))%Q).
        * apply (lic_qlt_add_l ((3 # 5) * ir2_e m)%Q 0%Q
                  ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)%Q).
          apply (Qlt_le_trans 0%Q (1 # (36 * p * b))%Q
                  ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)%Q).
          -- apply QltT_to_Qlt. exact Hc0.
          -- apply (Qle_trans (1 # (36 * p * b))%Q
                    ((1 # (36 * p * b))%Q + 0%Q)%Q
                    ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)%Q).
             ++ apply qeq_imp_qle. apply Qeq_sym. apply Qplus_0_r.
             ++ apply Qplus_le_compat.
                ** apply Qle_refl.
                ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hc0.
        * apply qeq_imp_qle. apply Qplus_comm.
    - exact (QleT'_to_Qle _ _ HmargT). }
  assert (Hmargin' : QleT' ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
                      ((Qabs (((Z.pos p # b)%Q - Qinv (ir2_x m))%Q))
                         - ((3 # 5) * ir2_e m)%Q)%Q).
  { apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ HmargT) as Hd.
    apply (Qle_trans ((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
            ((((1 # (36 * p * b))%Q + (1 # (36 * p * b))%Q)
                + ((3 # 5) * ir2_e m)%Q) - ((3 # 5) * ir2_e m)%Q)%Q
            ((Qabs (((Z.pos p # b)%Q - Qinv (ir2_x m))%Q))
               - ((3 # 5) * ir2_e m)%Q)%Q).
    - apply qeq_imp_qle. unfold Qminus.
      rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      apply Qeq_sym. apply Qplus_0_r.
    - unfold Qminus in Hd |- *.
      apply Qplus_le_compat; [exact Hd | apply Qle_refl]. }
  exists ((1 # (36 * p * b))%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (projT2 (dmec_escape_to_dist_any
             (fun n => Qinv (ir2_x n)) (fun n => ((3 # 5) * ir2_e n)%Q)
             n1_inv_tail n1_inv_vanish
             ((Z.pos p # b)%Q) m Hm1 Hesc' ((1 # (36 * p * b))%Q) Hc0 Hmargin'))).
Qed.

Print Assumptions n1_shift_measure.
Print Assumptions n1_scale_measure.
Print Assumptions n1_inv_nonpos_measure.
Print Assumptions n1_inv_pos_measure.
