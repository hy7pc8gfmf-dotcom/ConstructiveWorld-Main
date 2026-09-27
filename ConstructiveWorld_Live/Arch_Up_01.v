(* ==========================================================================)
   Arch_Up_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：qktv_abs_lt_two_side、qktv_gamma、qktv_dstar、qktv_K、qk_tv_iter_contraction、kvev_id_transport、kvev_single_le_sum、kvev_list_len_pos、Z_keep。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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
From Stdlib Require Import Lia Lqa.

(* ================= §1 qktv_abs_lt_two_side 族 ================= *)
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.

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

(* G4 审计口（桥接引理 + 主定理，全 Closed 预期）                        *)
Print Assumptions qktv_abs_lt_two_side.
Print Assumptions qk_tv_iter_contraction.
(* ================= §2 kvev_id_transport 族 ================= *)
(* ---------- 助推：非空有限表势的正性（states_ne 的直用形态） ---------- *)
(* 根内 vocab_len_pos 被无关段变量污染（token_eq_dec/count_token）， *)
(* 此处给出洁净版：Not (Id l nil) ⟹ 0 < of_nat |l|。                *)
Lemma kvev_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H.
  exact (match H with id_refl => p end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进入提取闭包，   *)
(* 保证 G3 提取 Obj.magic = 0；根内 single_le_sum_aux 的空 match    *)
(* 会产出 2 处 Obj.magic，故不复用）。                              *)
Lemma kvev_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma kvev_list_len_pos : forall (A : Set) (l : list A),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros A l. destruct l as [| w rest].
  - intro Hne. exact (match Hne (@id_refl (list A) nil) with end).
  - intro Hne2. cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest)))
             (real_of_nat (Datatypes.S (length rest)))).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* Section KVEv：逐出核世界                                       *)
Section KVEv.

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states nil).
Variable K : Tok -> Tok -> Real.                       (* 完整行随机核 *)
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').  (* 核逐点正 *)
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* keep 过滤行和：逐出后的失配质量（行归一化的分母） *)
Definition Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* 过滤项逐点非负（件 0 与 Z_keep_pos 的共用引理） *)
Lemma Z_keep_entry_nonneg : forall (s y : Tok),
  real_le real_zero (if keep y then K s y else real_zero).
Proof.
  intros s y. destruct (keep y).
  - apply real_le_from_lt_aux. apply Kpos.
  - apply real_le_refl.
Qed.

(* HZk_pos 升级为定理：keep 见证项 K(s,s0) > 0 且 ≤ Z_keep s *)
Theorem Z_keep_pos : forall s : Tok, real_lt real_zero (Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hb : keep s0 = true) by (apply sf_bool_id_true; exact Hk0).
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { rewrite Hb. apply Kpos. }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (Z_keep s)).
  { apply (kvev_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. apply Z_keep_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s)
             Hlt0 Heq).
Qed.

(* 均匀分布 U ≡ 1/|states|（对齐根内 bs_minorization 的 Unif 形态） *)
Definition N_R : Real := real_of_nat (length states).
Theorem N_R_pos : real_lt real_zero N_R.
Proof.
  exact (kvev_list_len_pos Tok states states_ne).
Qed.
Definition U (s' : Tok) : Real := real_inv_pos N_R N_R_pos.

(* δ 与其前提（对齐 ：delta + 上界 + minorization 前提） *)
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (U s')) (K s s').

(* 逐出核：保留项 K·inv(Z_keep)，逐出项零 *)
Definition K_ev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
  else real_zero.

(* ---------- 件 0：Z_keep s ≤ 1（keep 子和 ≤ 全和 + Krow 桥） ---------- *)
Theorem Z_keep_le_one : forall s : Tok, real_le (Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans _ (real_list_sum Tok (fun s' : Tok => K s s') states)).
  - apply (real_list_sum_le Tok
             (fun s' : Tok => if keep s' then K s s' else real_zero)
             (fun s' : Tok => K s s') states).
    intro y. destruct (keep y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply (RealSetoid.real_eq_le _ _). apply Krow.
Qed.

(* ---------- 件 1：行归一化 Σ K_ev == 1 ---------- *)
Theorem kev_row_normalized : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K_ev s s') states) real_one.
Proof.
  intro s.
  (* 第一步：逐点改写 K_ev 为 g(s')·inv(Z)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_mult (if keep s' then K s s' else real_zero)
                           (real_inv_pos (Z_keep s) (Z_keep_pos s)))
              states) _).
  { apply (real_list_sum_ext Tok (fun s' : Tok => K_ev s s') _ states).
    intro y. destruct (keep y) eqn:Hk.
    - unfold K_ev. rewrite Hk. apply real_eq_refl.
    - unfold K_ev. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s)) _).
  { apply (real_list_sum_linear_r Tok
             (real_inv_pos (Z_keep s) (Z_keep_pos s))
             (fun s' : Tok => if keep s' then K s s' else real_zero) states). }
  (* 第三步：inv(Z)·Z == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _
           (real_mult (Z_keep s) (real_inv_pos (Z_keep s) (Z_keep_pos s))) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 2：minorization 传送 δ·U(s') ≤ K_ev s s' ---------- *)
(* 用 kvev_id_transport 沿 Id (keep s') true 投影到 keep 支，        *)
(* 规避 destruct-eqn 对前提的隐式替换。                              *)
Theorem kev_minorization : forall s s' : Tok,
  Id (keep s') true -> real_le (real_mult delta (U s')) (K_ev s s').
Proof.
  intros s s' Hkeep.
  apply (kvev_id_transport bool true (keep s')
           (fun b : bool =>
              real_le (real_mult delta (U s'))
                (if b then
                   real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
                 else real_zero))).
  (* K ≤ K_ev：Z ≤ 1 ⟹ inv(1) ≤ inv(Z)（inv 反单调）⟹ 正乘保序 *)
  - apply (real_le_trans _ (K s s')).
    + apply delta_minor.
    + apply (real_le_trans _
               (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
      * (* K == K·inv(1) 的 eq→le 桥 *)
        apply (RealSetoid.real_eq_le (K s s')
                 (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
        apply real_eq_sym.
        apply (real_eq_trans _ (real_mult (K s s') real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (K s s') (real_inv_pos real_one real_lt_zero_one)
                    (K s s') real_one).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans _
                       (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
              ** apply real_eq_sym. apply b4_one_mult.
              ** apply real_inv_pos_correct.
        -- apply real_mult_one.
      * apply (real_le_mult_compat_r (K s s')
                 (real_inv_pos real_one real_lt_zero_one)
                 (real_inv_pos (Z_keep s) (Z_keep_pos s))).
        -- apply real_le_from_lt_aux. apply Kpos.
        -- apply (real_inv_pos_le_compat (Z_keep s) real_one
                    (Z_keep_pos s) real_lt_zero_one).
           apply Z_keep_le_one.
  - exact (id_sym Hkeep).
Qed.

(* ---------- 件 2b：drop 支零形态 + 逐点无条件版 ---------- *)
Theorem kev_drop_zero : forall s s' : Tok,
  Id (keep s') false -> real_eq (K_ev s s') real_zero.
Proof.
  intros s s' Hk.
  apply (kvev_id_transport bool false (keep s')
           (fun b : bool =>
              real_eq (if b then
                         real_mult (K s s')
                           (real_inv_pos (Z_keep s) (Z_keep_pos s))
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hk).
Qed.

Theorem kev_minorization_uncond : forall s s' : Tok,
  real_le (if keep s' then real_mult delta (U s') else real_zero) (K_ev s s').
Proof.
  intros s s'. destruct (keep s') eqn:Hk.
  - apply kev_minorization. apply sf_bool_true_id. exact Hk.
  - apply (RealSetoid.real_eq_le real_zero (K_ev s s')).
    + apply real_eq_sym. apply kev_drop_zero.
      rewrite Hk. apply id_refl.
Qed.

End KVEv.
(* ================= §3 minus_middle_t12 族 ================= *)
(* ---------- 副本 Section Alignment 的声明（同名同序；未用不声明） ---------- *)

Section AlignIdWorld.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align reward beta beta_pos pi_ref).
Variable eta : R.                  (* 副本步长 η > 0 *)
Variable eta_pos : lt zero eta.
Variable sum_over_S_pos : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* ---------- 差分代数封装（根内机器两步装配，供两主件共用） ---------- *)

(* 望远镜：已知 b 的公共项抽取。
   (a − b) − (c − b) == a − c
   装配：minus_minus_distr（(a−b)−c == a−(b+c)，根内 L19183）
       + minus_plus_cancel（b + (c−b) == c，根内 L668）。 *)
Lemma minus_middle_t12 : forall a b c : R,
  Id (minus (minus a b) (minus c b)) (minus a c).
Proof.
  intros a b c.
  exact (id_trans (minus_minus_distr a b (minus c b))
                  (id_cong (fun x => minus a x) (minus_plus_cancel b c))).
Qed.

(* 左消去：(a − b) − (a − c) == c − b（gap 下降量的换形核）。
   装配：minus_rearrange_four（根内 L19773，四元差分重排）
       + minus_self_zero（a − a == 0，根内 L984）
       + minus zero X == opp X（plus_comm/plus_zero）
       + opp_minus（根内 L706）+ plus_comm。 *)
Lemma minus_left_cancel_t12 : forall a b c : R,
  Id (minus (minus a b) (minus a c)) (minus c b).
Proof.
  intros a b c.
  assert (Hzero : Id (minus zero (minus b c)) (minus c b)).
  {
    assert (H1 : Id (minus zero (minus b c)) (opp (minus b c)))
      by exact (id_trans (plus_comm zero (opp (minus b c)))
                         (plus_zero (opp (minus b c)))).
    assert (H2 : Id (opp (minus b c)) (minus c b))
      by exact (id_trans (opp_minus b c) (plus_comm (opp b) c)).
    exact (id_trans H1 H2).
  }
  exact (id_trans (minus_rearrange_four a b a c)
                  (id_trans (id_cong2 minus (minus_self_zero a a id_refl) id_refl)
                            Hzero)).
Qed.

(* ---------- 件 A：次优间隙的单步精确分解恒等式 ---------- *)
(* gap(pi_{t+1}) == gap(pi_t) − β·[(1/η−1)·K1 + (1/η)·K2]
   装配 = 恒等式 + 恒等式 = 恒等式：
     gap(pi_t) == β·KL(pi_t‖pi_star)       （L20554）
     J(pi_{t+1}) − J(pi_t) == Δ              （L23000）
     望远镜：J* − J(pi_{t+1}) == (J* − J(pi_t)) − (J(pi_{t+1}) − J(pi_t))。 *)
Theorem policy_gap_next_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (align_objective reward beta pi_ref
                 (pi_star reward beta beta_pos pi_ref Z_align_pos))
              (align_objective reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (minus (mult beta (relative_entropy pi_t
                 (pi_star reward beta beta_pos pi_ref Z_align_pos)))
              (mult beta (plus
                 (mult (minus (inv_pos eta eta_pos) one)
                       (relative_entropy (pi_next reward beta beta_pos pi_ref
                                            eta sum_over_S_pos pi_t pi_t_pos)
                                         pi_t))
                 (mult (inv_pos eta eta_pos)
                       (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos)))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (id_sym (minus_middle_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np)))
           (id_cong2 minus Hgap Hdiff)).
Qed.

(* ---------- 件 A'：gap 递减量的精确恒等式（L23086 单调 ≤ 的精确化） ---------- *)
(* gap(pi_t) − gap(pi_{t+1}) == Δ；右端两 KL 均非负（根内 KL 机器），
   故单调 ≤ 为本恒等式的直接读出，且带精确步长。 *)
Corollary policy_gap_decrement_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref pi_t))
              (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref
                        (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                           pi_t pi_t_pos))))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_left_cancel_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np))
           Hdiff).
Qed.

(* ---------- 件 B：dpo_loss 单步精确差恒等式（换轴并列形态） ---------- *)
(* dpo_loss(pi) := opp (align_objective pi)（根内 ）。
   dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ。
   与根内 L23000 policy_iter_gap_diff 的关系：换轴并列——L23000 是 J 轴
   单步改进量，本件是 loss 轴单步下降量，二者经 minus_opp_opp 精确互逆
   （对偶轴上的显式陈述，供损失动态叙事直接引用）。 *)
Theorem dpo_loss_step_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (dpo_loss reward beta pi_ref pi_t)
              (dpo_loss reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  unfold dpo_loss.
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_opp_opp (align_objective reward beta pi_ref pi_t)
                                 (align_objective reward beta pi_ref Np))
                  Hdiff).
Qed.

(* ---------- 伴随件 C：后向 KL 递推的换轴精确恒等式 ---------- *)
(* β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2
   装配 = L22686（三 KL 恒等，除 β 版）整体乘 β（distrib + mult 交换
   吸收）+ 中项以 L20554 的 gap(pi_t) = J* − J(pi_t) 精确代换。
   定量解读：后向 KL 每步恰降 η·gap(pi_t)，并被前向步长 KL(β·K2) 抵消。 *)
Theorem policy_gap_backward_kl_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (mult beta (relative_entropy
             (pi_star reward beta beta_pos pi_ref Z_align_pos)
             (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                pi_t pi_t_pos)))
       (plus (mult (minus one eta)
                   (mult beta (relative_entropy
                          (pi_star reward beta beta_pos pi_ref Z_align_pos)
                          pi_t)))
             (plus (opp (mult eta
                          (minus (align_objective reward beta pi_ref
                                    (pi_star reward beta beta_pos pi_ref
                                       Z_align_pos))
                                 (align_objective reward beta pi_ref pi_t))))
                   (mult beta (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hnextpos : forall s : S, lt zero (Np s)).
  {
    intro s. unfold Np.
    exact (pi_next_pos reward beta beta_pos pi_ref eta sum_over_S_pos
                       pi_t pi_t_pos s).
  }
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  (* L22686 原始恒等（除 β 版三 KL） *)
  assert (Hb : Id (relative_entropy Ps Np)
                   (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                         (plus (opp (mult eta (relative_entropy pi_t Ps)))
                               (relative_entropy pi_t Np))))
    by exact (policy_iter_backward_kl_step reward beta beta_pos pi_ref
                                           pi_ref_pos Z_align_pos eta eta_pos
                                           sum_over_S_pos pi_t pi_t_pos
                                           pi_t_norm Hnextpos).
  (* β 缩放：β·(k·X) == k·(β·X)（结合-交换-反结合三步） *)
  assert (Hscale1 : Id (mult beta (mult (minus one eta) (relative_entropy Ps pi_t)))
                       (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))).
  {
    apply (id_trans (mult_assoc beta (minus one eta) (relative_entropy Ps pi_t))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy Ps pi_t))
                             (mult_comm beta (minus one eta)))).
    exact (id_sym (mult_assoc (minus one eta) beta (relative_entropy Ps pi_t))).
  }
  assert (Hswap2 : Id (mult beta (mult eta (relative_entropy pi_t Ps)))
                      (mult eta (mult beta (relative_entropy pi_t Ps)))).
  {
    apply (id_trans (mult_assoc beta eta (relative_entropy pi_t Ps))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t Ps))
                             (mult_comm beta eta))).
    exact (id_sym (mult_assoc eta beta (relative_entropy pi_t Ps))).
  }
  (* β·(opp (η·KLts)) == opp (η·gap(pi_t))：opp_mult_l + Hswap2 + Hgap 代换 *)
  assert (Hscale2 : Id (mult beta (opp (mult eta (relative_entropy pi_t Ps))))
                       (opp (mult eta
                              (minus (align_objective reward beta pi_ref Ps)
                                     (align_objective reward beta pi_ref pi_t))))).
  {
    apply (id_trans (opp_mult_l beta (mult eta (relative_entropy pi_t Ps)))).
    exact (id_cong opp
                   (id_trans Hswap2
                             (id_cong (fun z => mult eta z) (id_sym Hgap)))).
  }
  (* β 分配到后半树：β·(B + C) == β·B + β·C，B 项换形 *)
  assert (Hscale3 : Id (mult beta (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                        (relative_entropy pi_t Np)))
                       (plus (opp (mult eta
                                    (minus (align_objective reward beta pi_ref Ps)
                                           (align_objective reward beta pi_ref pi_t))))
                             (mult beta (relative_entropy pi_t Np))))
    by exact (id_trans (distrib beta (opp (mult eta (relative_entropy pi_t Ps)))
                                (relative_entropy pi_t Np))
                       (id_cong2 plus Hscale2 id_refl)).
  (* 全树 β 分配组装 *)
  assert (Hscale : Id (mult beta (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                                       (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                             (relative_entropy pi_t Np))))
                       (plus (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))
                             (plus (opp (mult eta
                                          (minus (align_objective reward beta pi_ref Ps)
                                                 (align_objective reward beta pi_ref pi_t))))
                                   (mult beta (relative_entropy pi_t Np)))))
    by exact (id_trans (distrib beta (mult (minus one eta) (relative_entropy Ps pi_t))
                                (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                      (relative_entropy pi_t Np)))
                       (id_cong2 plus Hscale1 Hscale3)).
  exact (id_trans (id_cong (mult beta) Hb) Hscale).
Qed.

End AlignIdWorld.

(* ---------- 提取检验（G3：Obj.magic = 0） ---------- *)

(* ---- 假设面追印：清单件逐件打印，判读全闭 ---- *)
Print Assumptions minus_middle_t12.
(* ================= §4 fw_energy_eta 族 ================= *)
Section FirewallLoop.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 解包接口字段（同根 FreeEnergyMinimization 区先例） *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)） *)

Variable base_loss : S -> R.
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall (t : R) (Ht : lt zero t),
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
(* 严格性接口（根 区同名 Variable 复刻） *)
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例；
   仅用于升温目标 t' := t+t 的严格性） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* 温度参数化 Boltzmann 族速记（全参显式） *)
Let Bt (t : R) (Ht : lt zero t) : S -> R :=
  boltzmann_dist_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.
Let Et (t : R) (Ht : lt zero t) : R :=
  energy_exp_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.

(* ===== 基础引理 ===== *)

(* 能量期望的 η-形式桥：energy_expectation (Bt t) 定义性 == Et t *)
Lemma fw_energy_eta : forall (t : R) (Ht : lt zero t),
  Id (energy_expectation base_loss (Bt t Ht)) (Et t Ht).
Proof. intros t Ht. exact (@id_refl _ (energy_expectation base_loss (Bt t Ht))). Qed.

(* 倍温严格升：t > 0 ⟹ t < t + t（升温目标的构造性证书）
   （接口 plus 抽象：plus zero t 与 t 非转换可互换，
     须走 id_transport——抽象层 Id 假设禁 rewrite 的标准通路） *)
Lemma fw_lt_double : forall t : R, forall Ht : lt zero t,
  lt t (plus t t).
Proof.
  intros t Ht.
  apply (id_transport (fun w => lt w (plus t t))
                      (id_trans (plus_comm zero t) (plus_zero t))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* 倍温正性：t > 0 ⟹ t + t > 0 *)
Lemma fw_double_pos : forall t : R, forall Ht : lt zero t,
  lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* ===== 件 2（主结果）：恢复增益精确恒等式 =====
   ΔH := H(p_{t2}) − H(p_{t1}) == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})
   三行证明：KL 温度分解 + 熵显式 + 纯 AC 重排。 *)
Theorem recovery_entropy_gain : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
           (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2.
  unfold minus.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := Et t1 Ht1). set (E2 := Et t2 Ht2).
  set (H1 := entropy_dist (Bt t1 Ht1)). set (H2 := entropy_dist (Bt t2 Ht2)).
  set (K := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  set (L2 := log (Z_temp t2)).
  (* 熵显式：H2 == b2·E2 + L2 *)
  assert (Hex2 : Id H2 (plus (mult b2 E2) L2))
    by exact (entropy_temp_explicit base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
  (* KL 温度分解：K == (−H1 + b2·E1) + 
     （energy_expectation (Bt t1) 定义性 == E1，fw_energy_eta 同 id_refl） *)
  assert (Hkl : Id K (plus (plus (opp H1) (mult b2 E1)) L2)).
  { apply (id_trans (relative_entropy_temp_decomp base_loss sum_over_S_pos Z_temp Z_temp_spec
                                  t2 Ht2 (Bt t1 Ht1)
                                  (boltzmann_dist_temp_normalized base_loss sum_over_S_pos
                                     Z_temp Z_temp_spec t1 Ht1))).
    apply (id_cong (fun x => plus (plus (opp H1) (mult b2 x)) L2)).
    apply fw_energy_eta. }
  (* 差的左分配：b2·(E2−E1) == b2·E2 + −(b2·E1) *)
  assert (Hd : Id (mult b2 (minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1)))).
  { apply (id_trans (mult_minus_distr_l b2 E2 E1)).
    unfold minus. apply id_refl. }
  (* 主代数链（纯 AC）：
     b2(E2−E1) + ((−H1+b2E1)+L2) == (b2E2 + −(b2E1)) + ((−H1+b2E1)+L2)
       == b2E2 + ((−(b2E1)) + ((−H1+b2E1)+L2))
       == b2E2 + ((−(b2E1)) + (b2E1 + (−H1+L2)))
       == b2E2 + ((−(b2E1) + b2E1) + (−H1+L2))
       == b2E2 + (−H1+L2)
       == (b2E2 + L2) + −H1 == H2 + −H1 *)
  assert (Hrot : forall aX : R,
    Id (plus (plus (opp H1) aX) L2) (plus aX (plus (opp H1) L2))).
  { intros aX.
    apply (id_trans (id_sym (plus_assoc (opp H1) aX L2))).
    apply (id_trans (id_cong (fun w => plus (opp H1) w) (plus_comm aX L2))).
    apply (id_trans (plus_assoc (opp H1) L2 aX)).
    apply (plus_comm (plus (opp H1) L2) aX). }
  assert (Hchain : Id (plus (mult b2 (minus E2 E1)) (plus (plus (opp H1) (mult b2 E1)) L2))
                      (plus H2 (opp H1))).
  { apply (id_trans (id_cong (fun x => plus x (plus (plus (opp H1) (mult b2 E1)) L2)) Hd)).
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (opp (mult b2 E1))
                                        (plus (plus (opp H1) (mult b2 E1)) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus (opp (mult b2 E1)) w))
                             (Hrot (mult b2 E1)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_assoc (opp (mult b2 E1)) (mult b2 E1)
                                         (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus w (plus (opp H1) L2)))
                             (id_trans (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                       (plus_opp (mult b2 E1))))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_comm zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w) (plus_comm (opp H1) L2))).
    apply (id_trans (plus_assoc (mult b2 E2) L2 (opp H1))).
    apply (id_cong (fun w => plus w (opp H1)) (id_sym Hex2)). }
  apply (id_sym (id_trans (id_cong (fun x => plus (mult b2 (minus E2 E1)) x) Hkl) Hchain)).
Qed.

(* ===== 件 1（主结果）：温度-熵单调 =====
   t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})。
   路径：能量单调（根）+ 件 2 恒等式 + KL ≥ 0（根 Gibbs）。 *)
Theorem entropy_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  (* E1 ≤ E2（根 主定理 energy_exp_temp_mono） *)
  assert (HdE : le zero (minus (Et t2 Ht2) (Et t1 Ht1))).
  { apply le_minus_nonneg.
    exact (energy_exp_temp_mono base_loss sum_over_S_pos inv_pos_lt_compat
             lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt). }
  (* KL(p_{t1} ‖ p_{t2}) ≥ 0（根 Gibbs 不等式） *)
  assert (Hkl : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  (* β₂ > 0 ⟹ β₂·ΔE ≥ 0 *)
  assert (Hb2 : le zero (inv_pos t2 Ht2)).
  { apply (lt_le_iff _ _). left. exact (inv_pos_pos t2 Ht2). }
  assert (Hterm : le zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                     (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
    - exact (id_sym (mult_zero (inv_pos t2 Ht2))).
    - exact (le_mult_compat_r (inv_pos t2 Ht2) zero (minus (Et t2 Ht2) (Et t1 Ht1)) Hb2 HdE). }
  (* 两非负项相加 ≥ 0 *)
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                        (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                        Hterm
                        (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                          (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl)).
  (* 件 2 恒等式迁移：ΔH ≥ 0 *)
  assert (Hfin : le zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))).
  { apply (le_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))).
    - exact (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  (* H1 + ΔH == H2（minus_plus_cancel）⟹ H1 ≤ H2 *)
  apply (le_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - exact (le_plus_nonneg_r (entropy_dist (Bt t1 Ht1))
                            (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))) Hfin).
Qed.

(* ===== 件 2 严格档：升温 ⟹ 熵严格恢复 =====
   显式条件（根 同款）：KL(p_{t2} ‖ p_{t1}) > 0
   （分布非平凡时满足；KL 退化为零仅当两温度分布逐点相同）。
   路径：根 energy_exp_temp_strict_mono 给 ΔE > 0 ⟹ β₂ΔE > 0，
   加 KL ≥ 0 后由件 2 恒等式迁移。 *)
Theorem entropy_temp_strict_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 ->
  lt zero (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)) ->
  lt (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (minus (Et t2 Ht2) (Et t1 Ht1)))
    by exact (energy_exp_temp_strict_mono base_loss sum_over_S_pos inv_pos_lt_compat
                lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (lt_le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                          Hterm
                          (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                            (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl21)).
  assert (Hfin : lt zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
    by exact (lt_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                  (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                       (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)) Hsum).
  apply (lt_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - (* lt H1 (H1 + ΔH)：两侧各走一次 id_transport
       （zero + H1 ↦ H1；ΔH + H1 ↦ H1 + ΔH；接口 plus 抽象不可换形） *)
    apply (id_transport
             (fun w => lt w (plus (entropy_dist (Bt t1 Ht1))
                                  (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))))
             (id_trans (plus_comm zero (entropy_dist (Bt t1 Ht1)))
                       (plus_zero (entropy_dist (Bt t1 Ht1))))).
    apply (id_transport
             (fun w => lt (plus zero (entropy_dist (Bt t1 Ht1))) w)
             (plus_comm (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                        (entropy_dist (Bt t1 Ht1)))).
    exact (lt_plus_compat_lt_le zero
                                (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                                (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t1 Ht1))
                                Hfin (le_refl (entropy_dist (Bt t1 Ht1)))).
Qed.

(* ===== 件 2 对偶形态：对称 KL 联立 =====
   与根 temp_strict_ident2（(β₁−β₂)ΔE == K12 + K21）联立消 (β₁−β₂)ΔE：
   ΔH == β₁·ΔE − K12（K12 := KL(p_{t2} ‖ p_{t1})）。
   三个恢复量（ΔH, ΔE, KL 组合）的完整系数表到此闭合。 *)
Theorem recovery_entropy_gain_alt : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (minus (mult (inv_pos t1 Ht1) (minus (Et t2 Ht2) (Et t1 Ht1)))
            (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (dE := minus (Et t2 Ht2) (Et t1 Ht1)).
  set (K12 := relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)).
  set (K21 := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  (* 对称 KL 恒等（根 temp_strict_ident2） *)
  assert (Hsym : Id (plus K12 K21) (mult (minus b1 b2) dE))
    by exact (temp_strict_ident2 base_loss sum_over_S_pos Z_temp Z_temp_spec t1 t2 Ht1 Ht2).
  (* b1 == b2 + (b1 − b2) *)
  assert (Hb1 : Id b1 (plus b2 (minus b1 b2))).
  { apply id_sym.
    apply (id_trans (plus_assoc b2 b1 (opp b2))).
    apply (id_trans (id_cong (fun w => plus w (opp b2)) (plus_comm b2 b1))).
    apply (id_trans (id_sym (plus_assoc b1 b2 (opp b2)))).
    apply (id_trans (id_cong (fun w => plus b1 w) (plus_opp b2))).
    apply (plus_zero b1). }
  (* 分配：b1·ΔE == b2·ΔE + (b1−b2)·ΔE *)
  assert (Hdistr : Id (mult b1 dE) (plus (mult b2 dE) (mult (minus b1 b2) dE))).
  { apply (id_trans (id_cong (fun w => mult w dE) Hb1)).
    apply (mult_plus_distr_r b2 (minus b1 b2) dE). }
  (* (b1−b2)·ΔE == K21 + K12（Hsym 对换） *)
  assert (Hsym' : Id (mult (minus b1 b2) dE) (plus K21 K12))
    by exact (id_trans (id_sym Hsym) (plus_comm K12 K21)).
  (* 减法消去：(K21 + K12) − K12 == K21 *)
  assert (Hcancel : Id (minus (plus K21 K12) K12) K21).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc K21 K12 (opp K12)))).
    apply (id_trans (id_cong (fun w => plus K21 w) (plus_opp K12))).
    apply (plus_zero K21). }
  (* 组装：ΔH == b2ΔE + K21（件 2）
       == (b2ΔE + (K21+K12)) − K12 == (b2ΔE + (b1−b2)ΔE) − K12 == b1ΔE − K12 *)
  assert (Hstep1 : Id (plus (mult b2 dE) K21)
                      (minus (plus (mult b2 dE) (plus K21 K12)) K12)).
  { apply (id_trans (id_cong (fun w => plus (mult b2 dE) w) (id_sym Hcancel))).
    apply (plus_assoc (mult b2 dE) (plus K21 K12) (opp K12)). }
  assert (Hstep2 : Id (minus (plus (mult b2 dE) (plus K21 K12)) K12)
                      (minus (mult b1 dE) K12)).
  { apply (id_cong (fun w => minus w K12)
                   (id_sym (id_trans Hdistr
                     (id_cong (fun w => plus (mult b2 dE) w) Hsym')))). }
  apply (id_trans (recovery_entropy_gain t1 t2 Ht1 Ht2)).
  exact (id_trans Hstep1 Hstep2).
Qed.

(* ===== 件 3：闭环封装（证书形态状态机） =====

   fw_verdict：健康判定 = Or 证书和（Set 层，非布尔判定器）
     - inl：健康证书 —— 熵过阈值 H_min 的 le 证书；
     - inr：退化报告 —— 量化缺口的 sigT 单元素类型（gap 恒等于
       当前熵 − H_min 的差值，携带"还差多少"的可提取实数）。
       （注意层级：Or 的分支是类型不是项——实数本身不能作分支，
         须经 sigT 单元素类型承载。）
   firewall_loop：闭环转移 —— 任一判定 ⟹ sigT 见证后继温度
     （健康：驻留 t' := t；退化：倍温 t' := t + t），
     携带转移证书（温度不降 + 熵不降 + 判定重装）。
   显式边界：单轮迭代不宣称"恢复健康"——退化支的重装判定
     仍是 inr（新一轮缺口报告）；健康与否由下一轮 fw_verdict
     证书回答。循环不变量 = 温度不降 ∧ 熵不降（件 1/2 供给）。 *)

Definition fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (entropy_dist (Bt t Ht)))
     (sigT (fun gap : R => Id gap (minus (entropy_dist (Bt t Ht)) Hmin))).

(* 检测-升温响应：退化报告 ⟹ sigT 见证升温目标 t' := t + t
   与恢复证书（熵不降 + 增量精确分解 = 件 2 恒等式） *)
Theorem fw_detect_warm : forall (Hmin : R) (t : R) (Ht : lt zero t)
                                (Hdef : sigT (fun gap : R =>
                                          Id gap (minus (entropy_dist (Bt t Ht)) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (Id (minus (entropy_dist (Bt t' Ht')) (entropy_dist (Bt t Ht)))
                 (plus (mult (inv_pos t' Ht') (minus (Et t' Ht') (Et t Ht)))
                       (relative_entropy (Bt t Ht) (Bt t' Ht'))))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

(* 闭环主定理：任一判定 ⟹ sigT 后继状态
   （温度不降 ∧ 熵不降 ∧ 判定重装）——逐轮可重复应用的
   证书状态机转移；健康支驻留、退化支倍温。 *)
Theorem firewall_loop : forall (Hmin : R) (t : R) (Ht : lt zero t)
                              (v : fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - (* 健康支：驻留 *)
    exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - (* 退化支：倍温 t' := t + t，熵恢复（件 1），判定重装（显式：仍 inr） *)
    assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + apply (lt_le_iff _ _). left. exact Hup.
    + split.
      * exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exact (existT _ (minus (entropy_dist (Bt (plus t t) Ht')) Hmin) id_refl).
Qed.

End FirewallLoop.

(* ============ 提取检验（可执行 OCaml，验收关卡） ============ *)
Set Warnings "-extraction-opaque-accessed".
(* ================= §5 eg_minus_def 族 ================= *)
Section EntropyGainQuant.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段（同根 ConvergenceCauchy 先例） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)，定义性展开） *)

(* ===== 显式接口（Variable 复刻根 ConvergenceCauchy 区） ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz : forall x y : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (minus x y))).
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).
(* 新增显式接口：|·| 的单边提取（le a (abs a)；根 abs_ge_zero_id_cc
   同族——le zero a -> |a| == a 的姊妹形态；构造性有序域标准性质，
   柯西实数模型可证，抽象层声明为接口字段，非经典公理） *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== 基础代数（Root 全局层无此三件的手工链） ===== *)

(* 减法定义（minus 透明，定义性相等） *)
Lemma eg_minus_def : forall a b : R, Id (minus a b) (plus a (opp b)).
Proof. intros a b. exact (@id_refl _ (plus a (opp b))). Qed.

(* 减法可逆：(a − b) + b == a *)
Lemma eg_minus_plus_cancel : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* K0 单步展开（差形式）：x' − x == η·g(x) *)
Lemma eg_step_diff : forall x : R,
  Id (minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_gradient_step x))).
  apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
  apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x)))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
  apply (plus_zero (mult eta (entropy_gradient x))).
Qed.

(* K0' 反向差：x − x' == −(η·g(x)) *)
Lemma eg_step_neg_diff : forall x : R,
  Id (minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus x z)
                           (id_cong opp (dynamics_gradient_step x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (opp_plus x (mult eta (entropy_gradient x))))).
  apply (id_trans (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x))))).
  apply (id_trans (id_cong (fun z => plus z (opp (mult eta (entropy_gradient x))))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (opp (mult eta (entropy_gradient x))))).
  apply (plus_zero (opp (mult eta (entropy_gradient x)))).
Qed.

(* 辅助：严格减正 a < b ⟹ 0 < b − a（根 ConvergenceCauchy 区 minus_pos 同构） *)
Lemma eg_minus_pos : forall u v : R, lt u v -> lt zero (minus v u).
Proof.
  intros u v Huv.
  unfold minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u)) (id_sym (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== 件 1 核 A：切线在 x' 处反向使用 ⟹ 增量 ≥ η·g(x)·g(x') =====
   切线（上界控制）在 x' 处取 y := x：
     e ≤ e' + g'·(x − x') = e' − g'·(η·g) ⟹ e' − e ≥ g'·(η·g) *)
Lemma eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* Ht 换形：minus x x' == −(η·g)；g'·(−η·g) == −(g'·(η·g)) *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r _ (plus (entropy (dynamics x))
                           (mult (entropy_gradient (dynamics x))
                                 (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => plus (entropy (dynamics x)) z)
                     (id_trans (id_cong (fun z => mult (entropy_gradient (dynamics x)) z)
                                        (eg_step_neg_diff x))
                               (opp_mult_l (entropy_gradient (dynamics x))
                                           (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* 两边加 W := g'·(η·g) 移项：le e (e' − W) ⟹ le (e + W) e'
     链：le_plus_compat Ht1 (le_refl W) 得 le (e + W) ((e' − W) + W)，
     右端 == e'（assoc + plus_opp + plus_zero），le_id_r 直接完成 *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat (entropy x)
                               (plus (entropy (dynamics x))
                                     (opp (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               Ht1 (le_refl (mult (entropy_gradient (dynamics x))
                                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (id_trans (id_sym (plus_assoc (entropy (dynamics x))
                                          (opp (mult (entropy_gradient (dynamics x))
                                                     (mult eta (entropy_gradient x))))
                                          (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                      (id_trans (id_cong (fun z => plus (entropy (dynamics x)) z)
                                         (id_trans (plus_comm (opp (mult (entropy_gradient (dynamics x))
                                                                            (mult eta (entropy_gradient x))))
                                                              (mult (entropy_gradient (dynamics x))
                                                                    (mult eta (entropy_gradient x))))
                                                   (plus_opp (mult (entropy_gradient (dynamics x))
                                                                   (mult eta (entropy_gradient x))))))
                                (plus_zero (entropy (dynamics x))))).
    - exact Hadd. }
  (* 两边加 opp e 提取：le (e + W) e' ⟹ le W (e' − e) == minus e' e *)
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))).
  - exact (id_trans (id_trans (id_sym (plus_zero (mult (entropy_gradient (dynamics x))
                                                      (mult eta (entropy_gradient x)))))
                              (id_cong (fun z => plus (mult (entropy_gradient (dynamics x))
                                                             (mult eta (entropy_gradient x))) z)
                                       (id_sym (plus_opp (entropy x)))))
                    (id_trans (plus_assoc (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))
                                          (entropy x) (opp (entropy x)))
                              (id_cong (fun z => plus z (opp (entropy x)))
                                       (plus_comm (mult (entropy_gradient (dynamics x))
                                                        (mult eta (entropy_gradient x)))
                                                  (entropy x))))).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== 件 1 核 B：Lipschitz 单边提取 ⟹ g' ≥ (1 − L·η)·g ===== *)
Lemma eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' − x| == η·g(x)（η>0、g>0：abs_pos + abs_mult + abs_opp） *)
  assert (Hstep : Id (minus (dynamics x) x) (mult eta (entropy_gradient x)))
    by exact (eg_step_diff x).
  assert (Hha : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) eta_pos Hgx).
  assert (Habsstep : Id (abs (minus (dynamics x) x))
                        (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs Hstep)).
    apply (id_trans (abs_mult eta (entropy_gradient x))).
    exact (id_cong2 (fun u v => mult u v) (abs_pos eta eta_pos) (abs_pos _ Hgx)). }
  assert (Habsneg : Id (abs (minus x (dynamics x)))
                       (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs (eg_step_neg_diff x))).
    apply (id_trans (abs_opp (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong abs (id_sym Hstep))).
    exact Habsstep. }
  (* (ii) Lipschitz 在 (x, x') 处：|g − g'| ≤ L·η·g *)
  assert (Hlip : le (abs (minus (entropy_gradient x) (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r _ (mult L (abs (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => mult L z) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) 单边提取：g − g' ≤ |g − g'| ≤ L·η·g（abs_ge_value） *)
  assert (Hone : le (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans _ (abs (minus (entropy_gradient x)
                                  (entropy_gradient (dynamics x)))) _).
    - exact (abs_ge_value (minus (entropy_gradient x)
                                 (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) 移项：g − (Lη)g ≤ g'，即 (1 − Lη)·g ≤ g'
        链：加 g' 得 le g ((Lη)g + g')；加 opp((Lη)g) 得 le (g − (Lη)g) g' *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (minus (entropy_gradient x)
                                (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))).
    - exact (id_sym (eg_minus_plus_cancel (entropy_gradient x)
                                          (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)) (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r _ (plus (plus (mult L (mult eta (entropy_gradient x)))
                                 (entropy_gradient (dynamics x)))
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (entropy_gradient (dynamics x))).
    - exact (id_trans (id_cong (fun z => plus z (opp (mult L (mult eta (entropy_gradient x)))))
                               (plus_comm (mult L (mult eta (entropy_gradient x)))
                                          (entropy_gradient (dynamics x))))
                      (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                                    (mult L (mult eta (entropy_gradient x)))
                                                    (opp (mult L (mult eta (entropy_gradient x))))))
                                (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                                                   (plus_opp (mult L (mult eta (entropy_gradient x)))))
                                          (plus_zero (entropy_gradient (dynamics x)))))).
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (v) 换形：g + opp((Lη)g) == (1 − Lη)·g
        链：opp((Lη)g) == opp((L·η)g) == (opp(Lη))·g；再
        g + (opp(Lη))·g == 1·g + (opp(Lη))·g == (1 + opp(Lη))·g *)
  apply (le_id_l (mult (minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (id_sym
             (id_trans (id_cong (fun z => plus (entropy_gradient x) z)
                                (id_trans (id_cong opp (mult_assoc L eta (entropy_gradient x)))
                                          (id_sym (opp_mult_r (mult L eta) (entropy_gradient x)))))
                       (id_trans (id_cong (fun z => plus z (mult (opp (mult L eta))
                                                                 (entropy_gradient x)))
                                          (id_trans (id_sym (mult_one (entropy_gradient x)))
                                                    (mult_comm (entropy_gradient x) one)))
                                 (id_sym (mult_plus_distr_r one (opp (mult L eta))
                                                            (entropy_gradient x)))))).
  - exact H2.
Qed.

(* ============================================================
   件 1（结果）：entropy_step_gain_lower —— 一步熵增定量下界
     g(x) > 0 ⟹
     η(1 − L·η)·g(x)² ≤ entropy(dynamics x) − entropy(x)
   组装：核 B 乘 g > 0 再乘 η > 0，与核 A 级联。
   ============================================================ *)
Theorem entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (eg_grad_lower x Hgx) as Hlow.
  (* 乘 g > 0（le_mult_compat）：(c₁·g)·g ≤ g'·g，左换形 assoc *)
  pose proof (le_mult_compat (mult (minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l _ (mult (mult (minus one (mult L eta)) (entropy_gradient x))
                           (entropy_gradient x)) _).
    - exact (mult_assoc (minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  (* 乘 η > 0（le_mult_compat_r，左乘）：η·((1−Lη)·g²) ≤ η·(g'·g) *)
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (le_mult_compat_r eta
                             (mult (minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x)))
                             (mult (entropy_gradient (dynamics x)) (entropy_gradient x))
                             Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l _ (mult eta (mult (minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x)))) _).
    - exact (id_sym (mult_assoc eta (minus one (mult L eta))
                                (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r _ (mult eta (mult (entropy_gradient (dynamics x))
                                       (entropy_gradient x))) _).
      + exact (id_trans (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                        (id_trans (id_cong (fun z => mult z (entropy_gradient x))
                                           (mult_comm eta (entropy_gradient (dynamics x))))
                                  (id_sym (mult_assoc (entropy_gradient (dynamics x))
                                                      eta (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans _ _ _ Hm2' (eg_tangent_shift x)).
Qed.

(* ============================================================
   件 2（结果）：entropy_gain_positive —— 增量正性充分条件版
     0 < η、0 < L、ηL < 1、g(x) > 0 ⟹ 0 < entropy(x') − entropy(x)
   （正性条件取 ηL < 1 而非草案 ημ < 1：μ 只控制上界不控制过冲，
     见文件头推导注记；负支 g < 0 需符号三分判定，构造性降级单侧版。）
   ============================================================ *)
Theorem entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (minus one (mult L eta)))
    by exact (eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (minus one (mult L eta))))
    by exact (mult_positive eta (minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero _ _ HA Hlow).
Qed.

(* ============================================================
   件 3（对照注记 + 结果推论）：second_law_quant
   根 L27778–27803 SecondLaw 区：strict_entropy_increase 是接口假设
   （Variable），second_law_irreversible = `apply strict_entropy_increase`
   （假设迁移，检验实证导出形态两处同现同一前提）。本件以具体熵梯度
   动力学 + 显式充分条件（ηL < 1、g(x) > 0）产出同一结论
   lt (entropy x) (entropy (dynamics x))——旧件可作退役注记：
   其接口前提在本件条件下由 entropy_gain_positive 构造性供给。
   ============================================================ *)
Theorem second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (id_trans (id_sym (plus_zero (entropy x)))
                      (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero (minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainQuant.
(* ================= §6 real_softplus 族 ================= *)
(* 件 1：real_softplus 定义、恒等桥、单调性                      *)

(* softplus x := log(1 + e^{−x})（DPO logit 损失的 softplus 形态；
   正性证书复用根内 real_sigmoid_denom_pos：1 + e^{−x} > 0）。 *)
Definition real_softplus (x : Real) : Real :=
  real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* 恒等桥：real_softplus x == real_dpo_logit x == −log σ(x)。 *)
Lemma real_softplus_eq_dpo_logit : forall x : Real,
  real_eq (real_softplus x) (real_dpo_logit x).
Proof. intro x. apply real_eq_sym. exact (real_softplus_sigmoid_eq x). Qed.

(* 单调性（递减）：x ≤ y ⟹ softplus y ≤ softplus x
   （exp_neg 递减给 1+e^{−y} ≤ 1+e^{−x}；log 保序完成）。 *)
Lemma real_softplus_mono : forall x y : Real, real_le x y ->
  real_le (real_softplus y) (real_softplus x).
Proof.
  intros x y Hxy.
  apply (real_log_le_mono (real_plus real_one (real_exp_neg y))
                          (real_plus real_one (real_exp_neg x))
                          (real_sigmoid_denom_pos y)
                          (real_sigmoid_denom_pos x)).
  exact (real_le_plus_compat real_one real_one
                             (real_exp_neg y) (real_exp_neg x)
                             (real_le_refl real_one)
                             (real_exp_neg_le_decr x y Hxy)).
Qed.

(* u ≤ 0 ⟹ 1 ≤ e^{−u}（e^0 == 1 换形 + exp_neg 递减）。 *)
Lemma real_one_le_exp_neg_of_le_zero : forall u : Real, real_le u real_zero ->
  real_le real_one (real_exp_neg u).
Proof.
  intros u Hu.
  apply (real_le_trans real_one (real_exp_neg real_zero) (real_exp_neg u)).
  - apply real_eq_le_bridge.
    apply real_eq_sym. exact real_exp_neg_zero.
  - exact (real_exp_neg_le_decr u real_zero Hu).
Qed.

(* b ≤ a ⟹ b − a ≤ 0（减法非正；加法保序 + a + (−a) == 0）。 *)
Lemma real_diff_le_zero : forall a b : Real, real_le b a ->
  real_le (real_plus b (real_opp a)) real_zero.
Proof.
  intros a b Hba.
  apply (real_le_trans (real_plus b (real_opp a))
                       (real_plus a (real_opp a)) real_zero).
  - exact (real_le_plus_compat b a (real_opp a) (real_opp a)
                                  Hba (real_le_refl (real_opp a))).
  - apply real_eq_le_bridge. exact (real_plus_opp a).
Qed.

(* 代数：e^{−b} == e^{−a}·e^{−(b−a)}（参数换形 + exp 加法性）。 *)
Lemma dpo_real_exp_neg_split : forall a b : Real,
  real_eq (real_exp_neg b)
          (real_mult (real_exp_neg a)
                     (real_exp_neg (real_plus b (real_opp a)))).
Proof.
  intros a b.
  apply (real_eq_trans (real_exp_neg b)
                       (real_exp_neg (real_plus a (real_plus b (real_opp a)))) _).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat b (real_plus a (real_plus b (real_opp a)))).
    apply real_eq_sym.
    (* a + (b − a) == b：assoc → comm → assoc⁻¹ → opp 消去 → 右零 *)
    apply (real_eq_trans (real_plus a (real_plus b (real_opp a)))
                         (real_plus (real_plus a b) (real_opp a)) b).
    + exact (real_plus_assoc a b (real_opp a)).
    + apply (real_eq_trans (real_plus (real_plus a b) (real_opp a))
                           (real_plus (real_plus b a) (real_opp a)) b).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                              (real_plus b a) (real_opp a)).
        -- exact (real_plus_comm a b).
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_plus (real_plus b a) (real_opp a))
                             (real_plus b (real_plus a (real_opp a))) b).
        -- apply real_eq_sym.
           exact (real_plus_assoc b a (real_opp a)).
        -- apply (real_eq_trans (real_plus b (real_plus a (real_opp a)))
                                (real_plus b real_zero) b).
           ++ apply (RealSetoid.real_eq_plus_compat b (real_plus a (real_opp a))
                                                    b real_zero).
              ** apply real_eq_refl.
              ** exact (real_plus_opp a).
           ++ exact (real_plus_zero b).
  - exact (real_exp_neg_plus a (real_plus b (real_opp a))).
Qed.

(* 件 2：序前提单侧核（Lipschitz 数学核）                        *)
(*   b ≤ a ⟹ softplus b − softplus a ≤ a − b                     *)
(* 数学核：1+e^{−b} ≤ e^{a−b} + e^{−b} == (1+e^{−a})·e^{a−b}     *)
(*   （e^{a−b} ≥ 1 由 b ≤ a），两侧取 log + log 加法性完成。      *)
Lemma real_softplus_diff_le : forall a b : Real, real_le b a ->
  real_le (real_plus (real_softplus b) (real_opp (real_softplus a)))
          (real_plus a (real_opp b)).
Proof.
  intros a b Hba.
  set (u := real_plus b (real_opp a)).
  set (E := real_exp_neg u).
  set (A := real_plus real_one (real_exp_neg a)).
  set (B := real_plus real_one (real_exp_neg b)).
  (* 步 1：E = e^{a−b} ≥ 1 *)
  assert (Hu0 : real_le u real_zero) by exact (real_diff_le_zero a b Hba).
  assert (HE1 : real_le real_one E) by exact (real_one_le_exp_neg_of_le_zero u Hu0).
  (* 步 2：恒等式 A·E == E + e^{−b} *)
  assert (HQ : real_eq (real_mult A E) (real_plus E (real_exp_neg b))).
  { apply (real_eq_trans (real_mult A E)
           (real_plus (real_mult E real_one) (real_mult E (real_exp_neg a))) _).
    - apply (real_eq_trans (real_mult A E)
              (real_mult E (real_plus real_one (real_exp_neg a))) _).
      + exact (real_mult_comm A E).
      + exact (real_distrib E real_one (real_exp_neg a)).
    - apply (RealSetoid.real_eq_plus_compat (real_mult E real_one)
                                            (real_mult E (real_exp_neg a))
                                            E (real_exp_neg b)).
      + exact (real_mult_one E).
      + (* E·e^{−a} == e^{−b}：dpo_real_exp_neg_split + 乘法交换 *)
        apply real_eq_sym.
        apply (real_eq_trans (real_exp_neg b)
                             (real_mult (real_exp_neg a) E) _).
        * exact (dpo_real_exp_neg_split a b).
        * exact (real_mult_comm (real_exp_neg a) E).
  }
  (* 步 3：B ≤ A·E（1 ≤ E 加法保序 + 恒等式换形） *)
  assert (HB : real_le B (real_mult A E)).
  { apply (real_le_trans B (real_plus E (real_exp_neg b)) (real_mult A E)).
    - exact (real_le_plus_compat real_one E (real_exp_neg b) (real_exp_neg b)
                                  HE1 (real_le_refl (real_exp_neg b))).
    - apply real_eq_le_bridge. apply real_eq_sym. exact HQ.
  }
  (* 步 4：log 完成：softplus b ≤ softplus a + (a − b) *)
  assert (Hlog : real_le (real_softplus b)
                         (real_plus (real_softplus a) (real_plus a (real_opp b)))).
  { apply (real_le_trans (real_softplus b)
             (real_log (real_mult A E)
                       (real_mult_positive A E (real_sigmoid_denom_pos a)
                                           (real_exp_neg_pos u))) _).
    - apply (real_log_le_mono B (real_mult A E) (real_sigmoid_denom_pos b)
              (real_mult_positive A E (real_sigmoid_denom_pos a)
                                      (real_exp_neg_pos u)) HB).
    - apply real_eq_le_bridge.
      apply (real_eq_trans (real_log (real_mult A E)
                (real_mult_positive A E (real_sigmoid_denom_pos a)
                                        (real_exp_neg_pos u)))
        (real_plus (real_log A (real_sigmoid_denom_pos a))
                   (real_log E (real_exp_neg_pos u))) _).
      + exact (real_log_mult A E (real_sigmoid_denom_pos a) (real_exp_neg_pos u)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log A (real_sigmoid_denom_pos a))
                 (real_log E (real_exp_neg_pos u))
                 (real_softplus a) (real_plus a (real_opp b))).
        * apply real_eq_refl.
        * 
          apply (real_eq_trans (real_log E (real_exp_neg_pos u))
                               (real_opp u) _).
          -- exact (log_inv_exp_neg_thm (real_opp u) (real_exp_neg_pos u)).
          -- apply (real_eq_trans (real_opp u)
                     (real_plus (real_opp b) (real_opp (real_opp a))) _).
             ++ exact (real_opp_plus b (real_opp a)).
             ++ apply (real_eq_trans (real_plus (real_opp b) (real_opp (real_opp a)))
                                     (real_plus (real_opp b) a) _).
                ** apply (RealSetoid.real_eq_plus_compat (real_opp b)
                            (real_opp (real_opp a)) (real_opp b) a).
                   --- apply real_eq_refl.
                   --- exact (real_opp_opp a).
                ** exact (real_plus_comm (real_opp b) a).
  }
  (* 步 5：移项：softplus b − softplus a ≤ a − b *)
  apply (real_le_trans (real_plus (real_softplus b) (real_opp (real_softplus a)))
                       (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                  (real_opp (real_softplus a))) _).
  - exact (real_le_plus_compat (real_softplus b)
                               (real_plus (real_softplus a) (real_plus a (real_opp b)))
                               (real_opp (real_softplus a)) (real_opp (real_softplus a))
                               Hlog (real_le_refl (real_opp (real_softplus a)))).
  - apply real_eq_le_bridge.
    apply (real_eq_trans (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                    (real_opp (real_softplus a)))
                         (real_plus (real_softplus a)
                                    (real_plus (real_plus a (real_opp b))
                                               (real_opp (real_softplus a)))) _).
    + apply real_eq_sym.
      exact (real_plus_assoc (real_softplus a) (real_plus a (real_opp b))
                             (real_opp (real_softplus a))).
    + apply (real_eq_trans (real_plus (real_softplus a)
                              (real_plus (real_plus a (real_opp b))
                                         (real_opp (real_softplus a))))
                           (real_plus (real_softplus a)
                              (real_plus (real_opp (real_softplus a))
                                         (real_plus a (real_opp b)))) _).
      * apply (RealSetoid.real_eq_plus_compat (real_softplus a)
                 (real_plus (real_plus a (real_opp b)) (real_opp (real_softplus a)))
                 (real_softplus a)
                 (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b)))).
        -- apply real_eq_refl.
        -- exact (real_plus_comm (real_plus a (real_opp b))
                                 (real_opp (real_softplus a))).
      * apply (real_eq_trans (real_plus (real_softplus a)
                   (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b))))
                (real_plus (real_plus (real_softplus a) (real_opp (real_softplus a)))
                           (real_plus a (real_opp b))) _).
        -- exact (real_plus_assoc (real_softplus a) (real_opp (real_softplus a))
                                  (real_plus a (real_opp b))).
        -- apply (real_eq_trans (real_plus (real_plus (real_softplus a)
                                             (real_opp (real_softplus a)))
                                           (real_plus a (real_opp b)))
                                (real_plus real_zero (real_plus a (real_opp b))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_softplus a) (real_opp (real_softplus a)))
                       (real_plus a (real_opp b))
                       real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_opp (real_softplus a)).
              ** apply real_eq_refl.
           ++ apply (real_eq_trans (real_plus real_zero (real_plus a (real_opp b)))
                                   (real_plus (real_plus a (real_opp b)) real_zero) _).
              ** exact (real_plus_comm real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_zero (real_plus a (real_opp b))).
Qed.

(* 件 2 完成：abs 消解工具 + Or 序前提 Lipschitz 主推论          *)

(* 0 ≤ d ⟹ |d| == d（real_abs_pos_req 的 le 版：Or 两支）。 *)
Lemma real_abs_nonneg_eq : forall d : Real, real_le real_zero d ->
  real_eq (real_abs d) d.
Proof.
  intros d Hd. destruct Hd as [Hlt | Heq].
  - exact (real_abs_pos_req d Hlt).
  - apply (real_eq_trans (real_abs d) real_zero d).
    + apply (real_eq_trans (real_abs d) (real_abs real_zero) real_zero).
      * apply (RealSetoid.real_eq_abs_compat d real_zero (real_eq_sym real_zero d Heq)).
      * exact real_abs_zero_req.
    + exact Heq.
Qed.

(* 减法式的反号形态：u − v == −(v − u)。 *)
Lemma real_minus_opp_form : forall u v : Real,
  real_eq (real_plus u (real_opp v)) (real_opp (real_plus v (real_opp u))).
Proof.
  intros u v.
  apply (real_eq_trans (real_plus u (real_opp v))
                       (real_plus (real_opp v) u) _).
  - exact (real_plus_comm u (real_opp v)).
  - apply (real_eq_trans (real_plus (real_opp v) u)
                         (real_plus (real_opp v) (real_opp (real_opp u))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                                            (real_opp v) (real_opp (real_opp u))).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (real_opp_opp u).
    + apply real_eq_sym. exact (real_opp_plus v (real_opp u)).
Qed.

(* d == −e 且 0 ≤ e ⟹ |d| == e（abs 经 opp 对称消解）。 *)
Lemma real_abs_opp_form : forall d e : Real,
  real_eq d (real_opp e) -> real_le real_zero e -> real_eq (real_abs d) e.
Proof.
  intros d e Hd He.
  apply (real_eq_trans (real_abs d) (real_abs e) e).
  - apply (real_eq_trans (real_abs d) (real_abs (real_opp e)) (real_abs e)).
    + apply (RealSetoid.real_eq_abs_compat d (real_opp e) Hd).
    + exact (real_abs_opp e).
  - exact (real_abs_nonneg_eq e He).
Qed.

(* 主推论：softplus 的 1-Lipschitz 敏感性界（metric 形态）。
   前提 Or (real_le x y) (real_le y x) 为显式 Set 层序二分
   （构造性实数上不可整体消去，见文件头诚实边界注记）。 *)
Theorem real_softplus_lipschitz : forall x y : Real,
  Or (real_le x y) (real_le y x) ->
  real_le (real_metric (real_softplus x) (real_softplus y))
          (real_metric x y).
Proof.
  intros x y Hor. unfold real_metric.
  destruct Hor as [Hxy | Hyx].
  - (* 分支 1：x ≤ y。|sp x − sp y| == sp x − sp y；|x − y| == y − x。 *)
    assert (Hdec : real_le (real_softplus y) (real_softplus x))
      by exact (real_softplus_mono x y Hxy).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus x) (real_opp (real_softplus y))))
      by exact (real_le_minus_nonneg_aux (real_softplus y) (real_softplus x) Hdec).
    assert (Hd2 : real_le real_zero (real_plus y (real_opp x)))
      by exact (real_le_minus_nonneg_aux x y Hxy).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus x) (real_opp (real_softplus y))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_nonneg_eq (real_plus (real_softplus x) (real_opp (real_softplus y))) Hd1).
    + apply (real_le_trans (real_plus (real_softplus x) (real_opp (real_softplus y)))
                           (real_plus y (real_opp x)) _).
      * exact (real_softplus_diff_le y x Hxy).
      * apply real_eq_le_bridge. apply real_eq_sym.
        exact (real_abs_opp_form (real_plus x (real_opp y))
                                 (real_plus y (real_opp x))
                                 (real_minus_opp_form x y) Hd2).
  - (* 分支 2：y ≤ x。|sp x − sp y| == sp y − sp x（opp 桥）；|x − y| == x − y。 *)
    assert (Hdec : real_le (real_softplus x) (real_softplus y))
      by exact (real_softplus_mono y x Hyx).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus y) (real_opp (real_softplus x))))
      by exact (real_le_minus_nonneg_aux (real_softplus x) (real_softplus y) Hdec).
    assert (Hd2 : real_le real_zero (real_plus x (real_opp y)))
      by exact (real_le_minus_nonneg_aux y x Hyx).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus y) (real_opp (real_softplus x))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_opp_form (real_plus (real_softplus x) (real_opp (real_softplus y)))
                               (real_plus (real_softplus y) (real_opp (real_softplus x)))
                               (real_minus_opp_form (real_softplus x) (real_softplus y))
                               Hd1).
    + apply (real_le_trans (real_plus (real_softplus y) (real_opp (real_softplus x)))
                           (real_plus x (real_opp y)) _).
      * exact (real_softplus_diff_le x y Hyx).
      * apply real_eq_le_bridge.
        apply real_eq_sym.
        exact (real_abs_nonneg_eq (real_plus x (real_opp y)) Hd2).
Qed.

(* 件 3：DPO 损失敏感性装配                                      *)
(*   |L(π; w, l) − L(π*; w, l)| ≤ |β(log_ratio 差分) − (r_w − r_l)| *)
(*   （条件化形态：序二分前提为显式 Set 层 Or）。                *)

(* metric 的 eq 兼容。 *)
Lemma real_metric_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_metric a b) (real_metric a' b').
Proof.
  intros a a' b b' Ha Hb. unfold real_metric.
  apply (RealSetoid.real_eq_abs_compat (real_plus a (real_opp b))
                                       (real_plus a' (real_opp b'))).
  apply (RealSetoid.real_eq_plus_compat a (real_opp b) a' (real_opp b') Ha).
  apply (RealSetoid.real_eq_opp_compat b b'). exact Hb.
Qed.

Section UpDpoSensMain.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* 策略 π 的 DPO logit 差：β·(log_ratio(π, w) − log_ratio(π, l))。 *)
Definition real_dpo_logit_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_plus (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_w))
            (real_opp (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_l))).

(* π* 的 DPO logit 差：真实奖励差分 r_w − r_l。 *)
Definition real_dpo_logit_star (s_w s_l : S) : Real :=
  real_plus (reward s_w) (real_opp (reward s_l)).

(* 桥 1：策略 DPO 损失 == softplus(logit 差)（定义性 + softplus 恒等桥）。 *)
Lemma real_dpo_loss_pair_eq_softplus : forall (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
          (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)).
Proof.
  intros pi Hpi s_w s_l.
  apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 桥 2：π* 处 DPO 损失 == softplus(真实奖励差分)
   （real_dpo_loss_at_pi_star + softplus 恒等桥）。 *)
Lemma real_dpo_loss_star_eq_softplus : forall s_w s_l : S,
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
             s_w s_l)
          (real_softplus (real_dpo_logit_star s_w s_l)).
Proof.
  intros s_w s_l.
  apply (real_eq_trans _ (real_dpo_logit (real_dpo_logit_star s_w s_l)) _).
  - exact (real_dpo_loss_at_pi_star S reward beta beta_pos pi_ref pi_ref_pos
                                    Z_align Z_align_pos s_w s_l).
  - apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 主件：DPO 损失敏感性界（metric 形态，序二分前提显式 Set 层 Or）。
   内容：metric L pi L_star ≤ metric logit pi logit_star
   （策略损失到 pi_star 损失的距离 ≤ logit 差分的距离）。 *)
Theorem real_dpo_pair_loss_sensitivity :
  forall (pi : S -> Real) (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  Or (real_le (real_dpo_logit_star s_w s_l) (real_dpo_logit_pair pi Hpi s_w s_l))
      (real_le (real_dpo_logit_pair pi Hpi s_w s_l) (real_dpo_logit_star s_w s_l)) ->
  real_le (real_metric (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                          s_w s_l))
          (real_metric (real_dpo_logit_pair pi Hpi s_w s_l)
                       (real_dpo_logit_star s_w s_l)).
Proof.
  intros pi Hpi s_w s_l Hor.
  assert (HL : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
    by exact (real_dpo_loss_pair_eq_softplus pi Hpi s_w s_l).
  assert (HS : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                             s_w s_l)
                       (real_softplus (real_dpo_logit_star s_w s_l)))
    by exact (real_dpo_loss_star_eq_softplus s_w s_l).
  apply (real_le_trans _ (real_metric (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_softplus (real_dpo_logit_star s_w s_l))) _).
  - apply real_eq_le_bridge.
    exact (real_metric_eq_compat _ _ _ _ HL HS).
  - unfold real_metric.
    destruct Hor as [H | H].
    + (* 分支 1：X* ≤ Xπ ⟹ Lπ ≤ L*；|Lπ − L*| == L* − Lπ ≤ Xπ − X* == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                             (real_softplus (real_dpo_logit_star s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_star s_w s_l)
                                     (real_dpo_logit_pair pi Hpi s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                           (real_softplus (real_dpo_logit_star s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                 (real_opp (real_dpo_logit_star s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_star s_w s_l)
                                           (real_dpo_logit_pair pi Hpi s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_opp_form (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                                 (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                                 (real_minus_opp_form (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                      (real_softplus (real_dpo_logit_star s_w s_l)))
                                 Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                             (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_opp (real_dpo_logit_star s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_dpo_logit_star s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_nonneg_eq (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                                (real_opp (real_dpo_logit_star s_w s_l))) Hd2).
    + (* 分支 2：Xπ ≤ X* ⟹ L* ≤ Lπ；|Lπ − L*| == Lπ − L* ≤ X* − Xπ == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_star s_w s_l))
                             (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_pair pi Hpi s_w s_l)
                                     (real_dpo_logit_star s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_star s_w s_l))
                                           (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_star s_w s_l)
                                 (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_pair pi Hpi s_w s_l)
                                           (real_dpo_logit_star s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_nonneg_eq (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                             (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                             (real_plus (real_dpo_logit_star s_w s_l)
                                        (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_star s_w s_l)
                                        (real_dpo_logit_pair pi Hpi s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_opp_form (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                               (real_opp (real_dpo_logit_star s_w s_l)))
                                    (real_plus (real_dpo_logit_star s_w s_l)
                                               (real_opp (real_dpo_logit_pair pi Hpi s_w s_l)))
                                    (real_minus_opp_form (real_dpo_logit_pair pi Hpi s_w s_l)
                                                         (real_dpo_logit_star s_w s_l))
                                    Hd2).
Qed.

End UpDpoSensMain.
