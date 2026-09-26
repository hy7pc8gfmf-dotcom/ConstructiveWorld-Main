(* 玩具证替换件 —— 先行消融波落件（四刀清单见下）                  *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列四个裸反射      *)
(* 单跳玩具证之证明体替换为定义层受控展开闭合（实例壳层与源模块核层    *)
(* unfold 显式化后转换闭合，裸反射吞层改为分层显式），声明面与引用    *)
(* 面零改动，零新增 Require，证明结尾记号与原件逐件守恒，纯构造性    *)
(* 闭合，文尾保留原件 Print Assumptions 追印面。清单：              *)
(*   cb2w_z_pw_one（原 L55-57，裸反射单跳）                          *)
(*   cb2w_Delta_pw_two（原 L59-61，裸反射单跳）                      *)
(*   cb2w_core_zero_pw（原 L285-287，裸反射单跳）                    *)
(*   cb2w_core_gap_zero（原 L298-301，裸反射单跳）                   *)
(* UpAblP7_WallEps_CB2.v —— ConcB2 的 +1 松弛常数 Δ 与中心 z 的实例双侧界与严格形否定 *)
(* 数学使命：本件形式化库件 cb2_Delta = temp·max|dot| + 1 与 cb2_z 在两类实例上的 *)
(*   行为：a 组非退化实例（cb2w_q/cb2w_k/cb2w_lmax，z ≡ 1、Δ ≡ 2）上给出          *)
(*   cb2w_Delta_pos_half（Δ 严格正）、cb2w_z_ub_lt 与 cb2w_z_lb_lt（|z| < Δ 的    *)
(*   两个严格肢）与 cb2w_export_pack（z 的非严格双侧界合取）；b 组全零退化实例     *)
(*   （cb2_smoke_lmax 面）上证明两个严格见证均不存在（cb2w_death_certificate）。   *)
(* 对照意义：+1 松弛在非退化实例上给出严格间隙，在全零退化实例上严格化失效——      *)
(*   两侧合起来刻画 +1 松弛的严格性边界。                                        *)
(* 依赖清单：CW_ConstructiveWorld_219（实数接口面）、UpReqAlgebra、UpReqSumD、     *)
(*   UpReqConcB2（源模块全件：cb2_Delta/cb2_Delta_core/cb2_z、逐点不等式引理族      *)
(*   cb2_q* 系列、全参一般引理 cb2_z_lb_all/cb2_z_ub_all、退化面 cb2_smoke_*）。   *)
(* 证明要点：§2 三个严格形沿用源模块证明链的逐点结构：由 one_pos 取正性见证         *)
(*   N0，以 eps:=1#2 把 strict 拆为 Qlt (1#2) 1 与 1 ≤ … 两段，配合               *)
(*   cb2_maxabs_nonneg/cb2_dot_le_max/cb2_qplus_one_gap/cb2_qminus_gap/           *)
(*   cb2_qopp_abs_le/cb2_qle_minus/cb2_qmul_nonneg/cb2_qmul_nonneg_r/             *)
(*   cb2_qlt_eq_r 完成；§3 由 Qlt 传递性与 Qlt_irrefl 导出矛盾。                   *)
(* 构造性注记：全件语句集合值面；零承认、零经典逻辑；见证不存在以 False 值面      *)
(*   表达（构造性否定）；文尾 Print Assumptions 逐件全闭合。                      *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。       *)
(* 标识符约定：本件实例层命名以前缀 cb2w_ 区分于源模块 cb2_ 系列。                  *)

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
(* §1 实例数据面（a 组：非退化实例；b 组复用源模块 cb2_smoke_* 全零面）       *)
(* ============================================================ *)

Definition cb2w_q : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_k : unit -> list Real := fun _ => real_one :: nil.
Definition cb2w_lmax : list (list Real * list Real) :=
  (real_one :: nil, real_one :: nil) :: nil.

(* 完备性证明（lmax 含唯一 pair，由 in_eq 一步给出） *)
Lemma cb2w_complete : forall s s' : unit, In (cb2w_q s, cb2w_k s') cb2w_lmax.
Proof. intros s s'. apply in_eq. Qed.

(* 非退化数值锚：z ≡ 1、Delta ≡ 2（与全零退化实例 z ≡ 0、core ≡ 0 形成对照） *)
Lemma cb2w_z_pw_one : forall n : nat,
  projT1 (cb2_z unit cb2w_q cb2w_k real_one tt tt) n == 1%Q.
Proof.
  intro n.
  (* 刀：实例壳层（cb2w_q/cb2w_k 常量体）＋源模块核层（cb2_z = temp·dot）逐层
     unfold 显式化，转换闭合替代裸反射单跳吞层。 *)
  unfold cb2_z, cb2w_q, cb2w_k.
  reflexivity.
Qed.

Lemma cb2w_Delta_pw_two : forall n : nat,
  projT1 (cb2_Delta real_one cb2w_lmax) n == 2%Q.
Proof.
  intro n.
  (* 刀：装配面（cb2_Delta = core + one）与封顶核（cb2_Delta_core = temp·maxabs）
     及实例清单 cb2w_lmax 三层 unfold 显式化后转换闭合。 *)
  unfold cb2_Delta, cb2_Delta_core, cb2w_lmax.
  reflexivity.
Qed.

(* ============================================================ *)
(* §2 非退化实例上的严格形（eps:=1#2 具体值）                                     *)
(*   证明结构与源模块 UpReqConcB2 的证明链（cb2_Delta_pos/cb2_z_lb/cb2_z_ub）        *)
(*   逐行同构，实例化 temp:=real_one、lmax:=cb2w_lmax，逐点不等式全用源模块          *)
(*   已证引理（cb2_maxabs_nonneg/cb2_dot_le_max/cb2_qplus_one_gap/cb2_qminus_gap）， *)
(*   即 cb2_Delta_core 的实例化重建本体。                                        *)
(* ============================================================ *)

(* a-2：Delta 正性的实例化重建（同构于源模块 cb2_Delta_pos 的严格支） *)
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

(* a-3：z 上界严格形的实例化重建（同构于源模块 cb2_z_ub 的 inl 支，语句强化为 real_lt 本体） *)
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

(* a-4：z 下界严格形的实例化重建（同构于源模块 cb2_z_lb 的 inl 支，语句强化为 real_lt 本体） *)
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

(* a-5：库内全参一般引理的直接应用（cb2_z_lb_all / cb2_z_ub_all，实参 temp_pos:=one_pos、lmax_complete:=cb2w_complete） *)
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
(* §3 全零退化对照件（源模块 UpReqConcB2 头注如实记载的局限的定理化）：              *)
(*   uniform eventual gap 形的严格见证遇上点态恒零 gap 即自相矛盾                  *)
(*   （0<eps 且 eps<0，由 Qlt 传递性与非自反性导出矛盾，零经典逻辑）。             *)
(* ============================================================ *)

(* b-1 一般否定引理：点态 gap 恒零的二元组上 real_lt 见证不存在（构造性否定） *)
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

(* b-2 全零退化实例的逐点面：cb2_Delta_core ≡ 0（cb2_smoke_lmax 面上逐点计算归零） *)
Lemma cb2w_core_zero_pw : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n == 0%Q.
Proof.
  intro n.
  (* 刀：封顶核 cb2_Delta_core 与全零实例 cb2_smoke_lmax 两层 unfold 显式化
     （temp·maxabs 在零清单上逐点归零）后转换闭合。 *)
  unfold cb2_Delta_core, cb2_smoke_lmax.
  reflexivity.
Qed.

(* b-3 否定性见证：全零退化下 cb2_Delta_core 的严格正性见证不存在 *)
Theorem cb2w_core_pos_death :
  real_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt real_zero (cb2_Delta_core real_one cb2_smoke_lmax)
           (fun n => cb2w_core_zero_pw n)).
Qed.

(* b-4 z 上界严格见证的否定：gap ≡ 0，由 cb2w_gap_zero_no_lt 直接导出矛盾 *)
Lemma cb2w_core_gap_zero : forall n : nat,
  projT1 (cb2_Delta_core real_one cb2_smoke_lmax) n
  - projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) n == 0%Q.
Proof.
  intro n.
  (* 刀：封顶核与核值两源模块定义（cb2_Delta_core/cb2_z）连同 b 组实例三常量
     （cb2_smoke_lmax/cb2_smoke_q/cb2_smoke_k）五层 unfold 显式化，gap 逐点
     差在零核与零核值上转换归零闭合。 *)
  unfold cb2_Delta_core, cb2_smoke_lmax, cb2_z, cb2_smoke_q, cb2_smoke_k.
  reflexivity.
Qed.

Theorem cb2w_z_ub_core_death :
  real_lt (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
          (cb2_Delta_core real_one cb2_smoke_lmax) -> False.
Proof.
  exact (cb2w_gap_zero_no_lt
           (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
           (cb2_Delta_core real_one cb2_smoke_lmax)
           cb2w_core_gap_zero).
Qed.

(* b-5 否定性见证的合取封装：逐点恒零面 × 两个严格见证不存在 *)
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
(* 假设审计（对逐件 Print Assumptions） *)
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
