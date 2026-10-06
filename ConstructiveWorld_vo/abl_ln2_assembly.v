(* ===================================================================== *)
(*  abl_ln2_assembly.v —— ln2 无理性链·sa_supply_rem' 改型装配件            *)
(*  使命: 把三积木接为链级 sigT 见证件——BD 的改型分子对 lni_supply_pair     *)
(*        （B_n:=L_n·p_n 整除供给）、BH 的 Ireal_n 本体（lnr_Ireal/lnr_lineL）*)
(*        与 AP 的几何尾界 lnt_gap_geo（经 lnr_gap_modulus 承载化），焊接成  *)
(*        单链级定理 lna_supply_chain_core：改型供给前提 A_n:=L_n·q̃_n、      *)
(*        B_n:=L_n·p_n 在 n 实例下的 Z 见证（sigT）＋supply×Ireal 线面对接    *)
(*        ＋Ireal×尾界绝对值形模量＋载体正性，六肢一线。另交付：两两对接      *)
(*        引理（lna_supply_pair_dock / lna_ireal_tail_dock(0)）、改型 rem    *)
(*        接口 lna_supply_rem' 的两段式装配（sa_supply_assemble 改型对应形，   *)
(*        B 侧已由 BD 见证实际填充——原 sa_supply_rem 任意 B 侧已不再悬空）、 *)
(*        规范 A 面 lna_Aface 与三头肢（θ=4/5<1、0<|A_n|、0<clo_n）、        *)
(*        n=1 数值锚（实算勘正后 A_1=3、B_1=4#2，经链面换算登记）。          *)
(*        诚实边界：⑤上界肢（θ^n 衰减，需 S6 恒等式腿＋锐权衰减）与④下界肢  *)
(*        （clo≤|A·X−B|，需 ri_identity_leg 本证）不在三积木内，lna_supply_  *)
(*        rem' 如实以两 real 肢为剩余前提，不虚报无条件形。                  *)
(*  依赖: Stdlib QArith/Qabs/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp；BeukersLists HansonLcm BeukersVariant Ln2Escape*)
(*        Ln2Bridge RealIdentity UpReqLn2Irrational；池内链序前件           *)
(*        abl_ln2_tail_bound → abl_ln2_numer_int → abl_ln2_ireal。          *)
(*  对标: SupplyAssembly sa_supply_rem（SupplyAssembly.v:219-223，原参数化  *)
(*        A=2^{n+1}q̃_n/θ=1/2，已被 abl_SupplyRemRefuted_07 机器证伪）的改型  *)
(*        重装；AE §3.3 路线③装配指令；Ln2Bridge ln2i_pade_supply 五肢面。   *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（sigT/S01.And/QeqT/QleT'/      *)
(*        QltT/real_eq/real_lt/real_le）；Z 见证经 projT1 投影取函数形       *)
(*        （Set 面，可提取）；Qeq/Qle 支撑件仅 Prop 面作推理；文尾           *)
(*        Print Assumptions 全 Closed＋Separate Extraction 闭合（四件套）。  *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q        *)
(*        vo_local_world_unified_0930 ""（链序：tail_bound→numer_int→      *)
(*        ireal→本件；道闸≤1=单进程串行）。                                 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm BeukersVariant.
Require Import Ln2Escape Ln2Bridge.
Require Import RealIdentity UpReqLn2Irrational.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_ireal.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 QeqT 传送微桥（链面锚换算用）                                      *)
(* ============================================================ *)

Lemma lna_qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply qeq_imp_qeqT.
  apply Qeq_sym. apply qeqT_imp_qeq. exact H.
Qed.

Lemma lna_qeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c H1 H2. apply qeq_imp_qeqT.
  apply (Qeq_trans a b c).
  - apply qeqT_imp_qeq. exact H1.
  - apply qeqT_imp_qeq. exact H2.
Qed.

(* ============================================================ *)
(* §1 改型分子对的 Z 承载（BD lni_supply_pair 的函数形投影）               *)
(*     A_n := L_n·q̃_n 的 Z 见证 z_n；B_n := L_n·p_n 的 Z 见证 w_n          *)
(* ============================================================ *)

Definition lna_Amod (n : nat) : Z := projT1 (lni_supply_pair n).
Definition lna_Bmod (n : nat) : Z := projT1 (projT2 (lni_supply_pair n)).

(* A 侧闭合：lnr_lA n（BH Q 面）== z_n#1 —— 与 lni_qlcm_int 前提定义性同形 *)
Lemma lna_lA_z : forall n : nat, QeqT (lnr_lA n) ((lna_Amod n) # 1)%Q.
Proof.
  intro n. unfold lnr_lA, lna_Amod.
  exact (fst (projT2 (projT2 (lni_supply_pair n)))).
Qed.

(* B 侧闭合：lnr_lB n == lni_lbvp n（定义性同形：同为 (L_n#1)·bv_p n）== w_n#1 *)
Lemma lna_lB_z : forall n : nat, QeqT (lnr_lB n) ((lna_Bmod n) # 1)%Q.
Proof.
  intro n. unfold lnr_lB, lna_Bmod.
  exact (snd (projT2 (projT2 (lni_supply_pair n)))).
Qed.

(* ============================================================ *)
(* §2 对接引理一（supply_pair×Ireal）：改型线对象经 Z 见证接入原 supply 面  *)
(*     lnr_lineL n（ri_real 基）≡_Real ln2b_line A B n（ln2b_X 基）——      *)
(*     两个独立包装的 X（BH ri_real 与 Ln2Bridge ln2b_X 逐点同读 ln2i_x）   *)
(*     在改型整数线上的 real_eq 焊接。                                     *)
(* ============================================================ *)

Theorem lna_supply_pair_dock : forall n : nat,
  real_eq (lnr_lineL n) (ln2b_line lna_Amod lna_Bmod n).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  rewrite lnr_lineL_proj, ln2b_line_pt.
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lA_z n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lB_z n)).
  ring.
Qed.

(* 规范 A 面（nat 乘积承载，供 0<|A_n| 头肢等算术面使用）与换算闭合 *)
Definition lna_Aface (n : nat) : Z := Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n).

Lemma lna_Aface_eq : forall n : nat, QeqT ((lna_Aface n) # 1)%Q (lnr_lA n).
Proof.
  intro n. apply qeq_imp_qeqT. unfold lna_Aface, lnr_lA.
  apply Qeq_sym. apply bk_Qmul_nat.
Qed.

(* 对接引理一（规范 A 面版）：任意以 lna_Aface 为系数面的 supply 肢经此迁移 *)
Theorem lna_supply_pair_dock_face : forall n : nat,
  real_eq (lnr_lineL n) (ln2b_line lna_Aface lna_Bmod n).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  rewrite lnr_lineL_proj, ln2b_line_pt.
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lB_z n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_Aface_eq n)).
  ring.
Qed.

(* ============================================================ *)
(* §3 对接引理二（Ireal×尾界）：AP lnt_gap_geo 经 BH 承载化的绝对值形模量    *)
(*     |S_{M+d} − S_M| ≤ 2^{p+1}·(3/4)^{S M − 2p}（p≥1）；p=0 档 Archimedean *)
(* ============================================================ *)

Theorem lna_ireal_tail_dock : forall (p M d : nat),
  (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
  QleT' (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q) (lnr_gapbound p M).
Proof.
  intros p M d Hp HM.
  assert (Hmono : Qle (lnr_psum p M) (lnr_psum p (M + d)))
    by (apply lnr_psum_mono; lia).
  assert (H0 : Qle 0 ((lnr_psum p (M + d) - lnr_psum p M)%Q)).
  { apply (Qle_trans 0%Q ((lnr_psum p M - lnr_psum p M)%Q)
                      ((lnr_psum p (M + d) - lnr_psum p M)%Q)).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat (lnr_psum p M) (lnr_psum p (M + d))
                             (- lnr_psum p M)%Q (- lnr_psum p M)%Q
                             Hmono (Qle_refl ((- lnr_psum p M)%Q))). }
  (* QleT'（Id 面）内禁 Qeq rewrite（坑卡 AU#1）——经 lnt_leT'_eq_l 传送 *)
  apply (lnt_leT'_eq_l (lnr_psum p (M + d) - lnr_psum p M)%Q
                       (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q)
                       (lnr_gapbound p M)).
  - apply Qeq_sym. exact (Qabs_pos (lnr_psum p (M + d) - lnr_psum p M)%Q H0).
  - apply lnr_gap_modulus; assumption.
Qed.

Theorem lna_ireal_tail_dock0 : forall (M d : nat),
  QleT' (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
        (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q).
Proof.
  intros M d.
  assert (Hmono : Qle (lnr_psum 0 M) (lnr_psum 0 (M + d)))
    by (apply lnr_psum_mono; lia).
  assert (H0 : Qle 0 ((lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)).
  { apply (Qle_trans 0%Q ((lnr_psum 0 M - lnr_psum 0 M)%Q)
                      ((lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat (lnr_psum 0 M) (lnr_psum 0 (M + d))
                             (- lnr_psum 0 M)%Q (- lnr_psum 0 M)%Q
                             Hmono (Qle_refl ((- lnr_psum 0 M)%Q))). }
  apply (lnt_leT'_eq_l (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q
                       (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
                       (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)).
  - apply Qeq_sym. exact (Qabs_pos (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q H0).
  - apply lnr_gap_mod0.
Qed.

(* ============================================================ *)
(* §4 改型 θ 档/载体与三头肢（对应 supply 五肢之①②③在改型参数化下）        *)
(*     θ' := 4/5（AE 路线③预算）；clo'_n := lne_B n/2^{n+1}（(1+t) 变体）   *)
(* ============================================================ *)

Definition lna_theta_mod : Q := (4 # 5)%Q.
Definition lna_clo_mod (n : nat) : Q :=
  (lne_B n / q_pow (2 # 1)%Q (Datatypes.S n))%Q.

Theorem lna_head_three_legs :
  And (QltT lna_theta_mod (1 # 1)%Q)
    (And (forall n : nat, QltT 0 (Qabs ((lna_Aface n) # 1)%Q))
         (forall n : nat, QltT 0 (lna_clo_mod n))).
Proof.
  split.
  - apply Qlt_to_QltT. unfold lna_theta_mod, Qlt. cbn [Qnum Qden]. lia.
  - split.
    + intro n. apply Qlt_to_QltT.
      assert (H1 : (1 <= hl_lcm_upto n)%nat) by apply lnr_hlcm_ge1.
      assert (H2 : (1 <= bk_Qn_qtilde n)%nat) by apply ri_qtilde_ge1.
      assert (H3 : (1 <= hl_lcm_upto n * bk_Qn_qtilde n)%nat) by nia.
      assert (Hx : (0 <= Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n))%Z)
        by apply Nat2Z.is_nonneg.
      assert (HQ : Qle 0 ((lna_Aface n) # 1)%Q).
      { unfold Qle. cbn [Qnum Qden]. unfold lna_Aface. lia. }
      rewrite (Qabs_pos ((lna_Aface n) # 1)%Q HQ).
      unfold Qlt, lna_Aface. cbn [Qnum Qden]. lia.
    + intro n. apply Qlt_to_QltT. unfold lna_clo_mod, Qdiv.
      apply Qmult_lt_0_compat.
      * exact (QltT_to_Qlt 0%Q (lne_B n) (lne_B_posT n)).
      * apply Qinv_lt_0_compat. apply lnt_pow2_pos.
Qed.

(* ============================================================ *)
(* §5 改型 rem 接口与两段式装配（sa_supply_rem/sa_supply_assemble 改型对应形） *)
(*     原 sa_supply_rem（SupplyAssembly.v:219-223，A=2^{n+1}q̃_n、θ=1/2）已被 *)
(*     t0_supply_rem_refuted 机器证伪；改型取 A_n:=L_n·q̃_n、B_n:=L_n·p_n、   *)
(*     θ:=4/5、clo:=lne_B/2^{n+1}。B 侧不再悬空：装配直接以 BD 见证填充。    *)
(* ============================================================ *)

Definition lna_supply_rem' : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower lna_Amod B lna_clo_mod)
        (ln2b_line_upper lna_Amod B lna_theta_mod)).

(* 两段式装配：仅余两 real 肢前提（S6 恒等式腿＋锐权衰减到货处）——
   B 侧已实际填充 lna_Bmod，非任意 B 悬接口 *)
Theorem lna_supply_rem'_assemble :
  And (ln2b_line_lower lna_Amod lna_Bmod lna_clo_mod)
      (ln2b_line_upper lna_Amod lna_Bmod lna_theta_mod) ->
  lna_supply_rem'.
Proof.
  intros [Hlo Hup]. exists lna_Bmod. split; assumption.
Qed.

(* ============================================================ *)
(* §6 链级装配件本体：改型供给前提 n 实例 sigT 见证件（六肢一线）            *)
(*     ①A 侧 Z 闭合 ②B 侧 Z 闭合 ③supply×Ireal 线面对接                    *)
(*     ④Ireal 载体严格正 ⑤Ireal×尾界模量（p≥1 几何档） ⑥（p=0 档）          *)
(* ============================================================ *)

Theorem lna_supply_chain_core :
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      And (forall n : nat, QeqT (lnr_lA n) ((A n) # 1)%Q)
        (And (forall n : nat, QeqT (lnr_lB n) ((B n) # 1)%Q)
          (And (forall n : nat, real_eq (lnr_lineL n) (ln2b_line A B n))
            (And (forall p : nat, real_lt real_zero (lnr_Ireal p))
              (And (forall (p M d : nat),
                      (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
                      QleT' (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q)
                            (lnr_gapbound p M))
                   (forall (M d : nat),
                      QleT' (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
                            (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)))))))).
Proof.
  exists lna_Amod. exists lna_Bmod. split.
  - apply lna_lA_z.
  - split.
    + apply lna_lB_z.
    + split.
      * intro n. apply lna_supply_pair_dock.
      * split.
        -- intro p. apply lnr_Ireal_pos.
        -- split.
           ++ intros p M d Hp HM. apply lna_ireal_tail_dock; assumption.
           ++ intros M d. apply lna_ireal_tail_dock0.
Qed.

(* ============================================================ *)
(* §7 数值锚组（n=1 实例，经链面换算登记；vm_compute 判定）                  *)
(*     实算勘正基线：L_1=hl_lcm_upto 1=1、q̃_1=3、p_1=bv_p 1=4#2             *)
(*     ⟹ A_1=3、B_1=4#2（BH 锚组同源）；链面新增：BD Z 见证与 3/4#2 的换算   *)
(* ============================================================ *)

Theorem lna_A1_anchor : QeqT (3 # 1)%Q ((lna_Amod 1) # 1)%Q.
Proof.
  apply lna_qeqT_trans with (b := lnr_lA 1).
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - apply lna_lA_z.
Qed.

Theorem lna_B1_anchor : QeqT (4 # 2)%Q ((lna_Bmod 1) # 1)%Q.
Proof.
  apply lna_qeqT_trans with (b := lnr_lB 1).
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - apply lna_lB_z.
Qed.

(* 链级模量实例锚：p=M=1、d=1 处 |S_2 − S_1| ≤ g(1,1)=4 的承载体现形 *)
Theorem lna_tail1_anchor :
  QleT' (Qabs (lnr_psum 1 (1 + 1) - lnr_psum 1 1)%Q) (lnr_gapbound 1 1).
Proof.
  apply lna_ireal_tail_dock; lia.
Qed.

(* ============================================================ *)
(* §8 陈述级挂点回执（S6 余量，不虚报闭合）                                 *)
(*     ri_identity_leg 本证（有限 M 换序恒等式）与锐权衰减件为链外缺口；     *)
(*     BH 迁移件保证：本证到货于 lnr_Ireal 面后，任意取形 I 即得腿。         *)
(* ============================================================ *)

Theorem lna_leg_transfer_hook : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnr_Ireal p)) ->
  ri_identity_leg lnr_Ireal -> ri_identity_leg I.
Proof. exact lnr_identity_leg_transfer. Qed.

(* ============================================================ *)
(* 可提取闭合（Set 层 witness 面：改型分子对 Z 函数＋规范 A 面＋θ/clo）      *)
(* ============================================================ *)

Separate Extraction lna_Amod lna_Bmod lna_Aface lna_theta_mod lna_clo_mod.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。          *)
(* ============================================================ *)

Print Assumptions lna_qeqT_sym.
Print Assumptions lna_qeqT_trans.
Print Assumptions lna_lA_z.
Print Assumptions lna_lB_z.
Print Assumptions lna_supply_pair_dock.
Print Assumptions lna_supply_pair_dock_face.
Print Assumptions lna_ireal_tail_dock.
Print Assumptions lna_ireal_tail_dock0.
Print Assumptions lna_head_three_legs.
Print Assumptions lna_supply_rem'.
Print Assumptions lna_supply_rem'_assemble.
Print Assumptions lna_supply_chain_core.
Print Assumptions lna_A1_anchor.
Print Assumptions lna_B1_anchor.
Print Assumptions lna_tail1_anchor.
Print Assumptions lna_leg_transfer_hook.
