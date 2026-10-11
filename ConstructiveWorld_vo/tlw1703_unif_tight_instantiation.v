(* ============================================================
   tlw1703_unif_tight_instantiation.v —— 一致型紧上界收尾件
   数学使命:幂率距离证书族 crt(一致常数 C0、指数 alpha 的全称下界形)到位后,
   换基搜索停点满足 n*(q) ≤ S(pie_modulus(crt q / 2)),其中 h(q) := lw1m_height q
   ——即「停点 ≤ 幂率深度选窗级」的一致型陈述(mu0 ≤ C·b^alpha 的构造性形式,
   窗口级刻度)。
   依赖清单:Stdlib QArith/Qabs/Bool/Arith/Lia/List(ListNotations);S01_BaseRing(NatLe/NatLe_lift/
   NatLe_drop);S02_CauchyComplete(QleT'_to_Qle/Qlt_to_QltT'/Id);S03_QExp
   (q_pow);PiEnvelope(pie_modulus/QltT');LW0LeibWindow(leiblw_Id/
   leiblw_id_intro);LW5SepComplexity(lw5n_sep_dec/lw5n_modulus_antitone);
   LW1PiMeasure(lw1m_height/lw1m_dist_pt);tlw1448_rebase;tlw1448_transfer
   (tlw1448_ck);tlw1448_l2escape(tlw1448_l2_escape);pdt_tan_table(tan 连分数
   表:Q 表算术/Z 缩放整序列/桥/衰减前提槽)。
   对标行:PiEnvelope :575/:579-625(pie_modulus/pie_modulus_bound);
   LW5SepComplexity :623(lw5n_modulus_antitone);LW1PiMeasure :48/:174;
   S03_QExp :36/:64;S02_CauchyComplete :103/:115;tlw1448_rebase :43/:47/:51/:71;
   tlw1448_transfer :50/:60;tlw1448_l2escape :45;pdt_tan_table :483/:611/:622。
   构造性注记:全 Set/Type 层;证书前提位以 Section Hypothesis 显式占位(接口契约
   UNIF-CERT-IFACE v1·四支全称链装载候重议);Section 关闭后导出全量化形,假设位
   转前提位(强度/档位分列登记);幂率变量取 lw1m_height(约分分母+1,表示不变量);
   换算支经 lw5n_modulus_antitone 砖取半径点 C0/(2*h^alpha);零 Axiom/Admitted;
   结论位承载于 NatLe/sigT/leiblw_Id;pdt_tan_table 供件锚于件末实名引用。
   编译配方:coqc -native-compiler no -q -Q . "" tlw1703_unif_tight_instantiation.v
   (全字面 COQLIB/ROCQLIB 双导出;工作目录=认证 vo 播种闭包;cpu_guard v3 包裹)
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround Bool.Bool Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0LeibWindow.
Require Import LW5SepComplexity.
Require Import LW1PiMeasure.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1448_l2escape.
Require Import pdt_tan_table.

Section UnifTightInstantiation.

Variable C0 : Q.          (* 一致常数 *)
Variable alpha : nat.     (* 幂率指数 *)
Variable crt : Q -> Q.    (* 幂率距离下界证书族 q |-> c_alpha(q) *)

(* —— 证书前提位四支(接口契约 UNIF-CERT-IFACE v1)—— *)
Hypothesis HC0_pos : QltT' 0 C0.
Hypothesis Hcrt_pos : forall q : Q, QltT' 0 (crt q).
(* 接入口形=lw1m_dist_pt 逐点尾段(margin_transfer 出口同形) *)
Hypothesis Hcrt_dist : forall q : Q, lw1m_dist_pt q (crt q).
(* 幂率下界主前提(全称形):crt q ≥ C0 / h(q)^alpha,h := lw1m_height *)
Hypothesis Hcert_pow : forall q : Q,
  QleT' ((C0 / q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q) (crt q).

(* 一致型换算界:U(C0,alpha,h) := S(Z.to_nat(Qceiling((8/C0)*h^alpha))) *)
Definition tlw1703_unif_bpow_c (C0 : Q) (alpha : nat) (h : nat) : nat :=
  Datatypes.S (Z.to_nat
    (Qceiling ((8 / C0 * q_pow ((Z.of_nat h # 1)%Q) alpha)%Q))).

(* 自铸辅助件:S03 仅 q_pow_nonneg Qle 形,严格 Qlt 形自铸 *)
Lemma tlw1703_unif_qpow_pos : forall (x : Q) (n : nat),
  Qlt 0 x -> Qlt 0 (q_pow x n).
Proof.
  intros x n Hx.
  induction n as [|n IH].
  - unfold Qlt. cbn [q_pow Qnum Qden]. lia.
  - cbn [q_pow]. apply (Qmult_lt_0_compat x (q_pow x n)).
    + exact Hx.
    + exact IH.
Qed.

(* Id→leiblw 一行桥(l2_escape 结论形 → rebase_least 前提形) *)
Lemma tlw1703_unif_id_bridge : forall (b : bool),
  Id b true -> leiblw_Id b true.
Proof.
  intros b H. destruct H. apply leiblw_id_intro.
Qed.

(* 换算支:证书窗阶 ≤ 幂率换算界(antitone 砖取半径点 C0/(2*h^alpha)) *)
Lemma tlw1703_unif_modulus_le : forall q : Q,
  (pie_modulus (crt q / 2)%Q
     <= tlw1703_unif_bpow_c C0 alpha (lw1m_height q))%nat.
Proof.
  intros q.
  assert (HC0Q : Qlt 0 C0) by (apply QltT'_to_Qlt; exact HC0_pos).
  assert (Hc : Qlt 0 (crt q)) by (apply QltT'_to_Qlt; exact (Hcrt_pos q)).
  assert (Hh1T : QltT' 0 ((Z.of_nat (lw1m_height q) # 1)%Q)).
  { unfold lw1m_height. apply lw1m_snq_pos. }
  assert (Hh1 : Qlt 0 ((Z.of_nat (lw1m_height q) # 1)%Q))
    by (apply QltT'_to_Qlt; exact Hh1T).
  assert (HhpQ : Qlt 0 (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)).
  { apply tlw1703_unif_qpow_pos. exact Hh1. }
  assert (Hhp : QltT' 0 (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha))
    by (apply Qlt_to_QltT'; exact HhpQ).
  pose proof (Hcert_pow q) as Hpow.
  apply QleT'_to_Qle in Hpow.
  (* 半径点 c' := C0 / (2*h^alpha),正性两侧 *)
  assert (Hc'pos : QltT' 0 (C0 / (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q)).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat C0
             (Qinv (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q)).
    - exact HC0Q.
    - apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat 2
               (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact HhpQ. }
  assert (Hhalfpos : QltT' 0 (crt q / 2)%Q).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat (crt q) (Qinv 2)).
    - exact Hc.
    - apply Qinv_lt_0_compat. unfold Qlt. cbn [Qnum Qden]. lia. }
  (* c' ≤ crt q/2:由 C0/h^alpha ≤ crt q 两侧乘 1/2 *)
  assert (Hle : Qle (C0 / (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q)
                    (crt q / 2)%Q).
  { assert (HhalfQ : Qlt 0 (1 # 2)%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
    assert (Hr1 : ((C0 / q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha) * (1 # 2))%Q
                  == (C0 / (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha))%Q).
    { unfold Qdiv. field.
      intro Hzz. apply (Qlt_not_eq 0 (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha) HhpQ).
      exact (Qeq_sym _ _ Hzz). }
    assert (Hr2 : (crt q * (1 # 2))%Q == (crt q / 2)%Q)
      by (unfold Qdiv; field).
    assert (Hm : Qle ((C0 / q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q * (1 # 2))
                     (crt q * (1 # 2))).
    { apply (Qmult_le_compat_r
               (C0 / q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q
               (crt q) (1 # 2)).
      - exact Hpow.
      - apply Qlt_le_weak. exact HhalfQ. }
    rewrite Hr1, Hr2 in Hm.
    exact Hm. }
  (* antitone 主链 *)
  pose proof (lw5n_modulus_antitone (crt q / 2)%Q
               (C0 / (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q)
               Hhalfpos Hc'pos Hle) as Hanti.
  unfold tlw1703_unif_bpow_c.
  unfold pie_modulus in Hanti.
  assert (Heq : (4 / (C0 / (2 * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q))%Q
                == ((8 / C0) * q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q).
  { unfold Qdiv. field.
    split.
    - intro Hzz. apply (Qlt_not_eq 0 C0 HC0Q). exact (Qeq_sym _ _ Hzz).
    - intro Hzz. apply (Qlt_not_eq 0 (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha) HhpQ).
      exact (Qeq_sym _ _ Hzz). }
  rewrite Heq in Hanti.
  exact Hanti.
Qed.

(* 主定理:一致型紧上界——停点 ≤ 幂率深度选窗级 *)
Theorem tlw1703_unif_tight_instantiation : forall q : Q,
  NatLe (tlw1448_nsep_rebase tlw1448_ck q)
        (Datatypes.S (pie_modulus (crt q / 2)%Q)).
Proof.
  intros q.
  pose proof (tlw1448_l2_escape q (crt q) (Hcrt_pos q) (Hcrt_dist q)) as Hhit.
  destruct (Nat.leb (Datatypes.S (pie_modulus (crt q / 2)%Q))
                    (tlw1448_bexp tlw1448_ck q)) eqn:Eleb.
  - apply Nat.leb_le in Eleb.
    apply NatLe_lift.
    exact (tlw1448_nsep_rebase_least tlw1448_ck q
             (Datatypes.S (pie_modulus (crt q / 2)%Q)) Eleb
             (tlw1703_unif_id_bridge _ Hhit)).
  - apply Nat.leb_gt in Eleb.
    apply NatLe_lift.
    pose proof (tlw1448_nsep_rebase_bound tlw1448_ck q) as Hb.
    lia.
Qed.

(* 推论:换基搜索停点不超过幂率换算界的后继(主定理与换算支经后继单调性合成) *)
Corollary tlw1703_unif_rebase_le_Sbpowc : forall q : Q,
  NatLe (tlw1448_nsep_rebase tlw1448_ck q)
        (Datatypes.S (tlw1703_unif_bpow_c C0 alpha (lw1m_height q))).
Proof.
  intros q.
  pose proof (tlw1703_unif_tight_instantiation q) as Hmain.
  pose proof (tlw1703_unif_modulus_le q) as Hle.
  apply NatLe_lift.
  apply Nat.le_trans with (m := Datatypes.S (pie_modulus (crt q / 2)%Q)).
  - apply NatLe_drop. exact Hmain.
  - apply le_n_S. exact Hle.
Qed.

End UnifTightInstantiation.

(* —— pdt_tan_table 供件锚实名引用(同名引理直引)—— *)
Lemma tlw1703_unif_pdt_table_anchor :
  bid (vleeq (tanU 3) (((15 # 1) :: ((-1) # 1) :: nil)%Q)) true.
Proof. exact tanU_anchor_3. Qed.

Lemma tlw1703_unif_pdt_decay_anchor :
  pdt_decay_premise 3 1 9 pdt_tan34_anchor.
Proof. exact pdt_decay_instance. Qed.

(* ---- 假设审计(应 Closed)---- *)
Print Assumptions tlw1703_unif_tight_instantiation.
Print Assumptions tlw1703_unif_modulus_le.
Print Assumptions tlw1703_unif_id_bridge.
Print Assumptions tlw1703_unif_qpow_pos.
Print Assumptions tlw1703_unif_rebase_le_Sbpowc.
