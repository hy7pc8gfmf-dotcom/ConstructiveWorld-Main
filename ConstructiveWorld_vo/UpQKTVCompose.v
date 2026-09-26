(* ==========================================================================)
   UpQKTVCompose.v — 注意力 Gibbs 核的 TV 迭代收缩
   使命: qktv_gamma/qktv_dstar（显式率 e^(−2γ′/T)）、qktv_K（attn_logit 上的 Gibbs 核）与 qk_tv_iter_contraction（TV 距离几何收缩迭代界）。
   依赖: CW_ConstructiveWorld_219、G10_LoebFam、UpTVDoeblin；Stdlib List、QArith、Lia、Lqa
   对标: 马尔可夫核的总变差几何收敛（Dobrushin 型显式率）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import G10_LoebFam.
Require Import UpTVDoeblin.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.
From Stdlib Require Import Lia Lqa.

(* ################ 桥接引理：abs 严格界的构造性双边提取 ################ *)

(* |x| < c ⟹ (−c < x ∧ x < c)。
   逐点走 real_abs_proj（|x|_n == Qabs x_n）+ Qle_abs_self（x_n ≤ |x_n|、
   −x_n ≤ |x_n|），分离编码下 lt 支的逐点余量原样传递。本桥接引理即
   「abs 界 → 双边界」的构造性代价具形处：仅严格（lt）形可行。 *)
Lemma qktv_abs_lt_two_side : forall (x c : Real),
  real_lt (real_abs x) c ->
  And (real_lt (real_opp c) x) (real_lt x c).
Proof.
  intros x c H.
  destruct H as [eps [Heps [N HN]]].
  split.
  - (* 首分量：−c < x。逐点：eps < c−|x| 且 −x ≤ |x| ⟹ eps < x+c *)
    unfold real_lt.
    exists eps. split.
    + exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      assert (HNq : Qlt eps (projT1 c n - projT1 (real_abs x) n)%Q)
        by (apply QltT_to_Qlt; exact HN).
      setoid_rewrite (real_abs_proj x n) in HNq.
      pose proof (Qle_abs_self (Qopp (projT1 x n))) as H0.
      setoid_rewrite (Qabs_opp (projT1 x n)) in H0.
      (* H0 : −x_n ≤ |x_n| *)
      pose proof (Qopp_le_compat (Qopp (projT1 x n))
                    (Qabs (projT1 x n)) H0) as Hm.
      setoid_rewrite (Qopp_involutive (projT1 x n)) in Hm.
      (* Hm : −|x_n| ≤ x_n *)
      pose proof (Qplus_le_compat (projT1 c n) (projT1 c n)
                    (Qopp (Qabs (projT1 x n))) (projT1 x n)
                    (Qle_refl (projT1 c n)) Hm) as Hp.
      setoid_rewrite (Qplus_comm (projT1 c n) (projT1 x n)) in Hp.
      (* Hp : c_n − |x_n| ≤ x_n + c_n *)
      apply Qlt_to_QltT.
      setoid_rewrite (real_opp_proj c n).
      unfold Qminus.
      setoid_rewrite (Qopp_involutive (projT1 c n)).
      exact (Qlt_le_trans eps (projT1 c n - Qabs (projT1 x n))%Q
               (projT1 x n + projT1 c n)%Q HNq Hp).
  - (* 次分量：x < c。逐点：eps < c−|x| 且 x ≤ |x| ⟹ eps < c−x *)
    unfold real_lt.
    exists eps. split.
    + exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      assert (HNq : Qlt eps (projT1 c n - projT1 (real_abs x) n)%Q)
        by (apply QltT_to_Qlt; exact HN).
      setoid_rewrite (real_abs_proj x n) in HNq.
      pose proof (Qopp_le_compat (projT1 x n) (Qabs (projT1 x n))
                    (Qle_abs_self (projT1 x n))) as Hm.
      (* Hm : −|x_n| ≤ −x_n *)
      pose proof (Qplus_le_compat (projT1 c n) (projT1 c n)
                    (Qopp (Qabs (projT1 x n))) (Qopp (projT1 x n))
                    (Qle_refl (projT1 c n)) Hm) as Hp.
      (* Hp : c_n − |x_n| ≤ c_n − x_n（Qminus 展开形） *)
      apply Qlt_to_QltT.
      exact (Qlt_le_trans eps (projT1 c n - Qabs (projT1 x n))%Q
               (projT1 c n - projT1 x n)%Q HNq Hp).
Qed.

(* ################ 组合件：γ′、率 δ*′、核 qktv_K ################ *)

(* γ′ := Δ + 1 = Qb·Kb·inv(√d) + 2：合成率常数（Δ 为 QK 端出节界） *)
Definition qktv_gamma (d : nat) (Qb Kb : Q) : Real :=
  real_plus (Delta d Qb Kb) (real_const 1).

(* 显式率 δ*′ := e^{−2γ′/T}（TV 端 tvd_dstar 于 γ := γ′ 实例） *)
Definition qktv_dstar (d : nat) (Qb Kb : Q) (Ttemp : Real)
  (HT : real_lt real_zero Ttemp) : Real :=
  tvd_dstar Ttemp HT (qktv_gamma d Qb Kb).

(* 合成核：注意力 logits 的 Gibbs 核（TV 端 tvd_K 于 z := attn_logit d） *)
Definition qktv_K (states : list (list Real))
  (Hn : real_lt real_zero (real_of_nat (length states)))
  (d : nat) (Ttemp : Real) (HT : real_lt real_zero Ttemp)
  (i j : list Real) : Real :=
  tvd_K states Hn Ttemp HT (attn_logit d) i j.

(* ################ 主定理：模块级单步合成定理 ################ *)

(* 范数界 + 温度 ⟹ 注意力 Gibbs 核迭代 TV 收缩、显式率 (1−δ*′)ⁿ。
   QK 端供给：γ′ 的数据源（Δ）与每对 |attn_logit d i j| ≤ Δ 证书；
   TV 端供给：Gibbs 核、δ 接口消解与迭代收缩主件。
   缺 QK 端：γ′ 与核 z 无供给；缺 TV 端：无收缩语汇——两端缺一不可。 *)
Theorem qk_tv_iter_contraction :
  forall (d : nat) (Qb Kb : Q),
    Qlt 0 Qb -> Qlt 0 Kb ->
    forall (states : list (list Real))
           (Hn : real_lt real_zero (real_of_nat (length states))),
      forall (Ttemp : Real) (HT : real_lt real_zero Ttemp)
             (HS : forall s : list Real, real_le real_zero (qkb_sql s)),
        (forall s : list Real,
           real_le (root_of (qkb_sql s) (HS s)) (real_const Qb)) ->
        (forall s : list Real,
           real_le (root_of (qkb_sql s) (HS s)) (real_const Kb)) ->
        (forall f : list Real -> Real,
           real_le (real_abs (real_list_sum (list Real) f states))
                   (real_list_sum (list Real)
                      (fun w : list Real => real_abs (f w)) states)) ->
        forall (n : nat) (mu nu : list Real -> Real),
          real_eq (real_list_sum (list Real) mu states) real_one ->
          real_eq (real_list_sum (list Real) nu states) real_one ->
          real_le
            (tv_doeblin states
               (tv_titer states (qktv_K states Hn d Ttemp HT) n mu)
               (tv_titer states (qktv_K states Hn d Ttemp HT) n nu))
            (real_mult (tv_rpow (tv_omd (qktv_dstar d Qb Kb Ttemp HT)) n)
                       (tv_doeblin states mu nu)).
Proof.
  intros d Qb Kb HQ HK states Hn Ttemp HT HS Hqb Hkb Labs n mu nu Hmu Hnu.
  (* Δ > 0（QK 端出节件首分量；以 nil 家族全局取一次，与 states 无关） *)
  assert (Hdpos : real_lt real_zero (Delta d Qb Kb)).
  { destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => Datatypes.nil)
                (fun _ : nat => Datatypes.nil)
                (fun _ : nat => HS Datatypes.nil)
                (fun _ : nat => HS Datatypes.nil)
                HQ HK
                (fun _ : nat => Hqb Datatypes.nil)
                (fun _ : nat => Hkb Datatypes.nil)) as [Hdp _].
    exact Hdp. }
  (* 0 < 1（QK 端常量正性件于 c := 1） *)
  assert (Hone : real_lt real_zero (real_const 1)).
  { apply qkb_real_const_pos.
    exact (proj2 (Qlt_alt 0 1) (@eq_refl comparison Lt)). }
  (* Δ < γ′（γ′ := Δ+1；右零恒等 + 平移） *)
  assert (Hgltp : real_lt (Delta d Qb Kb) (qktv_gamma d Qb Kb)).
  { unfold qktv_gamma.
    apply (RealSetoid.real_lt_id_l (Delta d Qb Kb)
             (real_plus (Delta d Qb Kb) real_zero)
             (real_plus (Delta d Qb Kb) (real_const 1))).
    - exact (real_eq_sym (real_plus (Delta d Qb Kb) real_zero)
               (Delta d Qb Kb) (real_plus_zero (Delta d Qb Kb))).
    - exact (real_lt_plus_translate (Delta d Qb Kb) real_zero
               (real_const 1) Hone). }
  (* 0 < γ′ *)
  assert (Hgpos : real_lt real_zero (qktv_gamma d Qb Kb)).
  { unfold qktv_gamma.
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (Delta d Qb Kb) (real_const 1))).
    - exact (real_eq_sym real_zero (real_plus real_zero real_zero)
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat_lt_le real_zero (Delta d Qb Kb)
               real_zero (real_const 1) Hdpos (tvd_lt_le real_zero (real_const 1) Hone)). }
  (* 每对 logits 的 QK 证书 → 严格化（+1 代价）→ 双边提取：z_hi *)
  assert (Hzhi : forall i j : list Real,
            real_le (attn_logit d i j) (qktv_gamma d Qb Kb)).
  { intros i j.
    destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => i) (fun _ : nat => j)
                (fun _ : nat => HS i) (fun _ : nat => HS j)
                HQ HK (fun _ : nat => Hqb i) (fun _ : nat => Hkb j))
      as [_ Habs].
    specialize (Habs 0%nat 0%nat).
    apply tvd_lt_le.
    apply (qktv_abs_lt_two_side (attn_logit d i j) (qktv_gamma d Qb Kb)).
    exact (real_le_lt_trans (real_abs (attn_logit d i j)) (Delta d Qb Kb)
             (qktv_gamma d Qb Kb) Habs Hgltp). }
  (* 同法：z_lo *)
  assert (Hzlo : forall i j : list Real,
            real_le (real_opp (qktv_gamma d Qb Kb)) (attn_logit d i j)).
  { intros i j.
    destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => i) (fun _ : nat => j)
                (fun _ : nat => HS i) (fun _ : nat => HS j)
                HQ HK (fun _ : nat => Hqb i) (fun _ : nat => Hkb j))
      as [_ Habs].
    specialize (Habs 0%nat 0%nat).
    apply tvd_lt_le.
    destruct (qktv_abs_lt_two_side (attn_logit d i j) (qktv_gamma d Qb Kb)
               (real_le_lt_trans (real_abs (attn_logit d i j))
                  (Delta d Qb Kb) (qktv_gamma d Qb Kb) Habs Hgltp))
      as [Hlo _].
    exact Hlo. }
  (* TV 端主定理于 γ := γ′、z := attn_logit d 一步消解 *)
  exact (tvd_dstar_iter_contraction states Hn Ttemp HT
           (qktv_gamma d Qb Kb) Hgpos
           (attn_logit d) Hzlo Hzhi Labs n mu nu Hmu Hnu).
Qed.

(* ============================================================ *)
(* G4 审计口（桥接引理 + 主定理，全 Closed 预期）                        *)
(* ============================================================ *)
Print Assumptions qktv_abs_lt_two_side.
Print Assumptions qk_tv_iter_contraction.
