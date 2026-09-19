(* ============================================================ *)
(* UpAblP7_WallEps_CB2.v —— 论文7 专项消融战役席（墙件 eps/B 形消费件战役）   *)
(*   乙腿 W2：ConcB2 +1 松弛护墙侧（与姊妹席甲腿 W1/CSM 侧分工，互不碰件）      *)
(*                                                              *)
(* 母本坐标（UpReqConcB2.v，四树 MD5 同一 fce35de3fccb04ea6436a00329ca0dbf）     *)
(*   → 本件消费位对照表：                                                      *)
(*   UpReqConcB2.v:26  头注诚实挂账（字面 Delta:=temp·M 全零退化下 uniform      *)
(*                     eventual gap 形严格证书不存在）→ 乙腿 b 死亡证书定理化对象 *)
(*   UpReqConcB2.v:385 cb2_Delta_core := temp·max|dot|（字面形）→ a 组消费重建    *)
(*                     与 b 组死亡证书双重对象                                  *)
(*   UpReqConcB2.v:389 cb2_Delta := core+1（装配形）→ a 组实例证书对象            *)
(*   UpReqConcB2.v:394 cb2_Delta_pos（inl 严格支，eps:=1#2，N 取正性证书之 N0）   *)
(*                     → a-2 实例级逐行镜像重建母型                             *)
(*   UpReqConcB2.v:436 cb2_z_lb（In 形下界）→ a-4 实例级严格形重建母型            *)
(*   UpReqConcB2.v:514 cb2_z_ub（In 形上界）→ a-3 实例级严格形重建母型            *)
(*   UpReqConcB2.v:562 cb2_z_lb_all / :565 cb2_z_ub_all（槽位直喂形）→ a-5       *)
(*                     全参闭项打包（temp_pos/lmax_complete 参面实名消费）        *)
(*   UpReqConcB2.v:574 Cb2Smoke 全零退化实例面 → b 组退化对象实名复用              *)
(* 分级申报：N1 库内放电件直连（cb2_z_lb_all/cb2_z_ub_all 全参闭项打包）；N2 已证    *)
(*   导出（cb2_maxabs_nonneg/cb2_dot_le_max/cb2_qplus_one_gap/cb2_qminus_gap/     *)
(*   cb2_qhalf_lt_one/cb2_qhalf_pos/cb2_qlt_eq_r/cb2_qabs_ge/cb2_qopp_abs_le/     *)
(*   cb2_qle_minus/cb2_qmul_nonneg/cb2_qmul_nonneg_r）；N3 实例供给（非退化实例：   *)
(*   temp:=real_one、q/k 单位一维、lmax 含该 pair 且完备；全零退化实例复用母本      *)
(*   Cb2Smoke 面）。                                                           *)
(* 依赖清单：CW_ConstructiveWorld_219（real_lt/real_le/QltT/real_one 面）+        *)
(*   UpReqConcB2（母本全件）——只读消费，原树零改，姊妹席与在飞件零接触。            *)
(* 红线自审：全中文表述；零 公理/承认件/参数/猜想/弃证字面；全件真证收口；文尾        *)
(*   Print Assumptions 逐件全闭合；编译产物只落 /tmp（vo_9.1/Live 只读）。         *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.
Import ListNotations.
Require Import UpReqConcB2.

(* ============================================================ *)
(* §1 实例数据面（乙腿 a 组：非退化实例；乙腿 b 组复用母本 Cb2Smoke 全零面）       *)
(* ============================================================ *)

Definition cb2w_q : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_k : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_lmax : list (list Real * list Real) :=
  (real_one :: nil, real_one :: nil) :: nil.

(* 完备性证书（lmax 含唯一 pair，in_eq 一步） *)
Lemma cb2w_complete : forall s s' : unit, In (cb2w_q s, cb2w_k s') cb2w_lmax.
Proof. intros s s'. apply in_eq. Qed.

(* 非退化数值锚：z≡1、Delta≡2（与全零退化 z≡0/core≡0 形成对照计数面） *)
Lemma cb2w_z_pw_one : forall n : nat,
  projT1 (cb2_z unit cb2w_q cb2w_k real_one tt tt) n == 1%Q.
Proof. intro n. reflexivity. Qed.

Lemma cb2w_Delta_pw_two : forall n : nat,
  projT1 (cb2_Delta real_one cb2w_lmax) n == 2%Q.
Proof. intro n. reflexivity. Qed.

(* ============================================================ *)
(* §2 乙腿 a：+1 松弛实例件（inl 严格支装配，eps:=1#2 具体值，真证收口）            *)
(*   证明形逐行镜像母本 §四 证书链（cb2_Delta_pos/cb2_z_lb/cb2_z_ub），              *)
(*   实例化 temp:=real_one、lmax:=cb2w_lmax，证书链全走母本已证点态机器              *)
(*   （cb2_maxabs_nonneg/cb2_dot_le_max/cb2_qplus_one_gap/cb2_qminus_gap），        *)
(*   即 cb2_Delta_core 消费重建本体。                                            *)
(* ============================================================ *)

(* a-2：Delta 正性实例重建（镜像母本 :394 cb2_Delta_pos） *)
Theorem cb2w_Delta_pos_half : real_lt real_zero (cb2_Delta real_one cb2w_lmax).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (HM0 : Qle 0 (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_maxabs_nonneg cb2w_lmax n).
    assert (HX : Qle 0 (projT1 real_one n
                         * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by (apply cb2_qmul_nonneg; assumption).
    apply Qlt_to_QltT.
    unfold cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    change (projT1 real_zero n) with 0%Q.
    assert (HX1 : Qle 0 (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1. exact HX. }
    assert (Hzg : Qeq (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                      (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n
                       + 1 - 0)) by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
             (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1 - 0)
             (Qlt_le_trans (1#2)%Q 1%Q
                (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) HX1))
             Hzg).
Qed.

(* a-3：z 上界严格形实例重建（镜像母本 :514 cb2_z_ub 的 inl 支，语句强化为 real_lt 本体） *)
Theorem cb2w_z_ub_lt :
  real_lt (cb2_z unit cb2w_q cb2w_k real_one tt tt)
          (cb2_Delta real_one cb2w_lmax).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                      (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_dot_le_max cb2w_lmax (cb2w_q tt) (cb2w_k tt) n
                  (cb2w_complete tt tt)).
    assert (Huv : Qle (projT1 real_one n * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                      (projT1 real_one n
                        * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { apply cb2_qmul_nonneg_r.
      - exact Htn0.
      - apply (Qle_trans (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                         (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))).
        + apply cb2_qabs_ge.
        + exact Hbd. }
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    assert (Huv1 : Qle (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                       (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1. exact Huv. }
    exact (Qlt_le_trans (1#2)%Q 1%Q
             (Qminus (Qplus (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) 1)
                     (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
             cb2_qhalf_lt_one
             (cb2_qminus_gap
                (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)
                (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                Huv1)).
Qed.

(* a-4：z 下界严格形实例重建（镜像母本 :436 cb2_z_lb 的 inl 支，语句强化为 real_lt 本体） *)
Theorem cb2w_z_lb_lt :
  real_lt (real_opp (cb2_Delta real_one cb2w_lmax))
          (cb2_z unit cb2w_q cb2w_k real_one tt tt).
Proof.
  destruct one_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 real_one n - 0) (projT1 real_one n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 real_one n)).
    { apply (Qle_trans 0 e0 (projT1 real_one n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 real_one n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                      (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n))
      by exact (cb2_dot_le_max cb2w_lmax (cb2w_q tt) (cb2w_k tt) n
                  (cb2w_complete tt tt)).
    assert (Hdn_ge : Qle (Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                         (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
      by exact (cb2_qopp_abs_le (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)).
    assert (Hu : Qle (projT1 real_one n
                       * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                     (projT1 real_one n
                       * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
      by (apply cb2_qmul_nonneg_r; [exact Htn0 | exact Hdn_ge]).
    assert (Hw : Qle 0 (projT1 real_one n
                         * Qminus (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                             (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))))
      by (apply cb2_qmul_nonneg; [exact Htn0 | exact (cb2_qle_minus _ _ Hbd)]).
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_opp_proj. rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    assert (Hw1 : Qle 0 (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                          + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
    { rewrite <- H1.
      assert (Hzr : Qeq (projT1 real_one n
                          * Qminus (projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
                              (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                        (projT1 real_one n
                          * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                         + projT1 real_one n
                          * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)) by ring.
      rewrite <- Hzr. exact Hw. }
    assert (Htot1 : Qle 0 (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                           + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)).
    { apply (Qle_trans 0
               (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n))
                + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)
               (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n)).
      - exact Hw1.
      - apply Qplus_le_compat.
        + assert (Hu1 : Qle (1 * Qopp (Qabs (projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)))
                            (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n)).
          { rewrite <- H1. exact Hu. }
          exact Hu1.
        + apply Qle_refl. }
    assert (Hzg : Qeq (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                       + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                      (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                       - Qopp (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)))
      by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
              + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
             (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
              - Qopp (1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1))
             (Qlt_le_trans (1#2)%Q 1%Q
                (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                 + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (1 * projT1 (cb2_dot (cb2w_q tt) (cb2w_k tt)) n
                    + 1 * projT1 (cb2_list_max_abs real_zero cb2w_lmax) n) Htot1))
             Hzg).
Qed.

(* a-5：槽位直喂形全参闭项打包（temp_pos:=one_pos、lmax_complete:=cb2w_complete 实名消费） *)
Theorem cb2w_export_pack :
  real_le (real_opp (cb2_Delta real_one cb2w_lmax))
          (cb2_z unit cb2w_q cb2w_k real_one tt tt)
  * real_le (cb2_z unit cb2w_q cb2w_k real_one tt tt)
            (cb2_Delta real_one cb2w_lmax).
Proof.
  split.
  - exact (cb2_z_lb_all unit cb2w_q cb2w_k real_one one_pos
             cb2w_lmax cb2w_complete tt tt).
  - exact (cb2_z_ub_all unit cb2w_q cb2w_k real_one one_pos
             cb2w_lmax cb2w_complete tt tt).
Qed.

(* ============================================================ *)
(* §3 乙腿 b：全零退化对照件（母本 :26 挂账的死亡证书定理化——先例 PintPosGrid 范式）   *)
(*   机器内核：uniform eventual gap 形严格证书遇上点态恒零 gap 即自毁                  *)
(*   （0<eps 且 eps<0 矛盾，Qlt 传递 + 非自反收口，零经典逻辑）。                      *)
(* ============================================================ *)

(* b-1 通用退化机器：点态 gap 恒零的二元组上，real_lt 证书不存在（构造性否定） *)
Lemma cb2w_gap_zero_no_lt : forall x y : Real,
  (forall n : nat, projT1 y n - projT1 x n == 0%Q) -> real_lt x y -> False.
Proof.
  intros x y Hgap [eps [Heps [N0 HN]]].
  assert (HNn : QltT eps (projT1 y N0 - projT1 x N0)).
  { apply HN. exact (NatLe_lift N0 N0 (le_n N0)). }
  apply QltT_to_Qlt in HNn.
  rewrite (Hgap N0) in HNn.
  apply QltT_to_Qlt in Heps.
  assert (Hbad : Qlt 0 0%Q) by exact (Qlt_trans 0 eps 0%Q Heps HNn).
  exact (Qlt_irrefl 0%Q Hbad).
Qed.

(* b-2 字面形全零退化点态面：temp·max|dot| ≡ 0（母本 Cb2Smoke 面上逐点计算归零） *)
Lemma cb2w_core_zero_pw : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n == 0%Q.
Proof. intro n. reflexivity. Qed.

(* b-3 字面形 Delta 正性死亡证书：全零退化下 strict 正性证书不存在 *)
Theorem cb2w_core_pos_death :
  real_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax)
           (fun n => cb2w_core_zero_pw n)).
Qed.

(* b-4 字面形 z 上界 strict 证书死亡：gap ≡ 0 同机自毁（Or 两支双堵的 inl 支定谳） *)
Lemma cb2w_core_gap_zero : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n
  - projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) n == 0%Q.
Proof. intro n. reflexivity. Qed.

Theorem cb2w_z_ub_core_death :
  real_lt (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
          (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt
           (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
           (cb2_Delta_core real_one cb2_smoke_lmax)
           cb2w_core_gap_zero).
Qed.

(* b-5 死亡证书打包（点态零面 × 双 strict 证书不存在——挂账的定理化固化件） *)
Theorem cb2w_death_certificate :
  (forall n : nat, projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n == 0%Q)
  * ((real_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax) -> False)
      * (real_lt (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
                 (cb2_Delta_core real_one cb2_smoke_lmax) -> False)).
Proof.
  split.
  - exact cb2w_core_zero_pw.
  - split.
    + exact (fun H => cb2w_core_pos_death H).
    + exact (fun H => cb2w_z_ub_core_death H).
Qed.

(* ============================================================ *)
(* PA 收尾段（逐件闭合判读留痕）                                            *)
(* ============================================================ *)

Print Assumptions cb2w_complete.
Print Assumptions cb2w_z_pw_one.
Print Assumptions cb2w_Delta_pw_two.
Print Assumptions cb2w_Delta_pos_half.
Print Assumptions cb2w_z_ub_lt.
Print Assumptions cb2w_z_lb_lt.
Print Assumptions cb2w_export_pack.
Print Assumptions cb2w_gap_zero_no_lt.
Print Assumptions cb2w_core_zero_pw.
Print Assumptions cb2w_core_pos_death.
Print Assumptions cb2w_core_gap_zero.
Print Assumptions cb2w_z_ub_core_death.
Print Assumptions cb2w_death_certificate.
