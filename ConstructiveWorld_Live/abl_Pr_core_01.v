(* ============================================================ *)
(* abl_Pr_core_01.v —— 素数域成域件单第 1 件（域地基）              *)
(* 模块名：abl_Pr_core_01                                         *)
(* 数学使命：nat 层素数面三件——①素性判定：pr_prime（试除形谓词，    *)
(*   2≤n ∧ [2,n) 内无因子，否定形自持 P->False）＋判定器            *)
(*   pr_prime_bool（bool 出口，spec 双向）；②最小素因子：           *)
(*   pr_min_factor（燃料递降 Fixpoint：燃料 k 递降、因子 d=n-k 自 2  *)
(*   升扫）＋正确性引理（找到的最小 d>1 必素）＋sigT 存在形           *)
(*   pr_min_factor_exists；③素因子分解存在形 pr_factor_exists       *)
(*   （n≥2 ⟶ 存在 sigT 见证的全素因子列表，fold_right 积==n，强归纳）。 *)
(*   设计依据：素数域成域件单设计文书 §成域件单 ①。                  *)
(* 依赖清单：纯 Stdlib（Arith.Arith / List / Lia / Bool）。零项目件   *)
(*   ——照 N 件单「件 1 零项目件」条款；HansonLcm 的 hl_binom/        *)
(*   hl_lcm_upto 衔接属件 2/件 4 自然依赖位，本件零依赖为最小形态。   *)
(* 构造性注记：Set 面承载——两条主存在语句（pr_min_factor_exists/     *)
(*   pr_factor_exists）全 sigT 见证形；Prop 面谓词 pr_prime 仅作推理  *)
(*   脚手架（Ln2Escape/HansonLcm 先例），否定形自持 P->False（本安装   *)
(*   无 Not，照 AQ 坑卡，全件零 not/~/<> 书写）；零公理零承认零经典    *)
(*   逻辑；计算件 pr_trial/pr_min_factor/pr_prime_bool 皆一阶         *)
(*   bool/nat Fixpoint 可提取；数值定装走小实例 vm_compute（≤12，     *)
(*   CZR14 大数值 Qed 打点墙纪律）。                                  *)
(* 编译配方：                                                       *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/    *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&   *)
(*   nice -19 rocq c -native-compiler no -Q                           *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_    *)
(*   0930 "" abl_Pr_core_01.v                                         *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.

(* ---- §0 素性谓词（试除形；否定自持 = P -> False 原定义形） ---- *)

Definition pr_prime (n : nat) : Prop :=
  2 <= n /\ (forall d : nat, 2 <= d -> d < n -> Nat.divide d n -> False).

(* ---- §1 mod 与 divide 的桥（除数 ≥ 1，双向） ---- *)

Lemma pr_dvd_mod0 : forall d n : nat,
  1 <= d -> Nat.divide d n -> n mod d = 0.
Proof.
  intros d n Hd [z Hz].
  destruct (Nat.Div0.mod_divides n d) as [_ Hbwd].
  apply Hbwd. exists z. rewrite Hz. apply Nat.mul_comm.
Qed.

Lemma pr_mod0_dvd : forall d n : nat,
  1 <= d -> n mod d = 0 -> Nat.divide d n.
Proof.
  intros d n Hd Hm.
  destruct (Nat.Div0.mod_divides n d) as [Hfwd _].
  apply Hfwd in Hm. destruct Hm as [c Hc].
  exists c. rewrite Hc. apply Nat.mul_comm.
Qed.

(* ---- §2 燃料递降布尔试除机（k 为燃料，d = n-k 扫描 [n-k, n)） ---- *)

Fixpoint pr_trial (k n : nat) : bool :=
  match k with
  | 0 => true
  | S k' => if Nat.eqb (n mod (n - S k')) 0 then false else pr_trial k' n
  end.

(* true 方向：pr_trial k n = true ⟹ [n-k, n) 内无 n 的因子 *)
Lemma pr_trial_true : forall n k : nat, 1 <= n ->
  pr_trial k n = true ->
  forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False.
Proof.
  intros n k. induction k as [|k IH]; intros Hn Htrue d Hd Hlt Hdvd.
  - lia.
  - simpl in Htrue. destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + discriminate.
    + destruct (Nat.eq_dec d (n - S k)) as [Hde|Hdne].
      * subst d. destruct (le_lt_dec 1 (n - S k)) as [H1|H1].
        -- exfalso. apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
           apply (pr_dvd_mod0 (n - S k) n H1) in Hdvd.
           rewrite Hdvd in Em. exfalso. apply Em. reflexivity.
        -- exfalso. assert (Hz : n - S k = 0) by lia.
           rewrite Hz in Hdvd. apply Nat.divide_0_l in Hdvd. lia.
      * apply (IH Hn Htrue d); try lia. exact Hdvd.
Qed.

(* false 方向：[n-k, n) 内无因子 ⟹ pr_trial k n = true *)
Lemma pr_trial_false : forall n k : nat, 1 <= n ->
  (forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False) ->
  pr_trial k n = true.
Proof.
  intros n k. induction k as [|k IH]; intros Hn Hall.
  - reflexivity.
  - simpl. destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + exfalso. apply Nat.eqb_eq in Em.
      destruct (le_lt_dec 1 (n - S k)) as [H1|H1].
      * apply (Hall (n - S k)); try lia.
        apply (pr_mod0_dvd (n - S k) n H1 Em).
      * assert (Hz : n - S k = 0) by lia.
        rewrite Hz in Em. rewrite Nat.mod_0_r in Em. lia.
    + apply IH; [lia|].
      intros d Hd Hlt Hdvd.
      destruct (Nat.eq_dec d (n - S k)) as [Hde|Hdne].
      * subst d. exfalso.
        destruct (le_lt_dec 1 (n - S k)) as [H1|H0].
        -- apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
           apply (pr_dvd_mod0 (n - S k) n H1) in Hdvd.
           apply Em. exact Hdvd.
        -- assert (Hz : n - S k = 0) by lia.
           rewrite Hz in Hdvd. apply Nat.divide_0_l in Hdvd. lia.
      * apply (Hall d); [lia | lia | exact Hdvd].
Qed.

(* 试除机 spec（双向 iff） *)
Theorem pr_trial_spec : forall n k : nat, 1 <= n ->
  pr_trial k n = true <->
  (forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False).
Proof.
  intros n k Hn. split.
  - apply pr_trial_true; assumption.
  - apply pr_trial_false; assumption.
Qed.

(* ---- §3 判定器 pr_prime_bool（bool 出口 + spec 双向） ---- *)

Definition pr_prime_bool (n : nat) : bool :=
  andb (Nat.leb 2 n) (pr_trial (n - 2) n).

Theorem pr_prime_bool_true : forall n : nat,
  pr_prime_bool n = true -> pr_prime n.
Proof.
  intros n H. unfold pr_prime. unfold pr_prime_bool in H.
  apply andb_prop in H. destruct H as [Hleb Htr].
  apply (proj1 (Nat.leb_le 2 n)) in Hleb. split; [exact Hleb|].
  intros d Hd2 Hlt Hdvd.
  assert (H1 : 1 <= n) by lia.
  apply (pr_trial_true n (n - 2) H1 Htr d); try lia. exact Hdvd.
Qed.

Theorem pr_prime_bool_false : forall n : nat,
  pr_prime n -> pr_prime_bool n = true.
Proof.
  intros n [H2 Hall]. unfold pr_prime_bool.
  apply andb_true_intro. split.
  - apply (proj2 (Nat.leb_le 2 n)). exact H2.
  - apply (pr_trial_false n (n - 2)). lia.
    intros d Hd Hlt Hdvd. apply (Hall d); try lia. exact Hdvd.
Qed.

Theorem pr_prime_bool_spec : forall n : nat,
  pr_prime_bool n = true <-> pr_prime n.
Proof.
  intros n. split.
  - apply pr_prime_bool_true.
  - apply pr_prime_bool_false.
Qed.

(* ---- §4 最小素因子（燃料递降 Fixpoint + soundness + sigT 存在形） ----
   pr_min_factor k n：余燃料 k 递降，受检因子 d = n-k 自 2 升扫；
   全程无因子则回退 n（n≥2 时 n 自身即因子，回退值合法）。 *)

Fixpoint pr_min_factor (k n : nat) : nat :=
  match k with
  | 0 => n
  | S k' => if Nat.eqb (n mod (n - S k')) 0 then n - S k' else pr_min_factor k' n
  end.

Lemma pr_min_factor_sound : forall n k : nat, 2 <= n -> k <= n - 2 ->
  (forall e : nat, 2 <= e -> e < n - k -> Nat.divide e n -> False) ->
  Nat.divide (pr_min_factor k n) n /\
  2 <= pr_min_factor k n /\
  pr_min_factor k n <= n /\
  (forall e : nat, 2 <= e -> e < pr_min_factor k n -> Nat.divide e n -> False).
Proof.
  intros n k. induction k as [|k IH]; intros Hn Hk Hall.
  - simpl. repeat split.
    + apply Nat.divide_refl.
    + lia.
    + lia.
    + intros e He Hlt Hdvd. apply (Hall e); try lia. exact Hdvd.
  - simpl.
    assert (Hk2 : k <= n - 2) by lia.
    assert (Hd2 : 2 <= n - S k) by lia.
    destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      repeat split.
      * apply (pr_mod0_dvd (n - S k) n); [lia | exact Em].
      * lia.
      * lia.
      * intros e He Hlt Hdvd. apply (Hall e); try lia. exact Hdvd.
    + apply IH; try lia.
      intros e He Hlt Hdvd.
      assert (Hsplit : e <= n - S k) by lia.
      destruct (Nat.eq_dec e (n - S k)) as [Hde|Hdne].
      * subst e.
        assert (Hm : n mod (n - S k) = 0).
        { apply (pr_dvd_mod0 (n - S k) n); [lia | exact Hdvd]. }
        apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
        apply Em. exact Hm.
      * apply (Hall e); [lia | lia | exact Hdvd].
Qed.

(* 正确性引理：找到的最小 d>1 必为素（试除形 pr_prime） *)
Theorem pr_min_factor_prime : forall n : nat,
  2 <= n -> pr_prime (pr_min_factor (n - 2) n).
Proof.
  intros n Hn. unfold pr_prime.
  assert (Hkvac : n - 2 <= n - 2) by apply Nat.le_refl.
  assert (Hvac : forall e : nat, 2 <= e -> e < n - (n - 2) -> Nat.divide e n -> False).
  { intros e He Hlt _. lia. }
  destruct (pr_min_factor_sound n (n - 2) Hn Hkvac Hvac) as [Hpn [Hp2 [Hpn' Hmin]]].
  split; [exact Hp2|].
  intros d Hd2 Hlt Hdvd.
  apply (Hmin d Hd2 Hlt).
  exact (Nat.divide_trans d (pr_min_factor (n - 2) n) n Hdvd Hpn).
Qed.

(* sigT 存在形：n≥2 ⟶ 见证 p，整除 n 且素 *)
Theorem pr_min_factor_exists : forall n : nat, 2 <= n ->
  { p : nat | Nat.divide p n /\ pr_prime p }.
Proof.
  intros n Hn. exists (pr_min_factor (n - 2) n). split.
  - assert (Hvac : forall e : nat, 2 <= e -> e < n - (n - 2) -> Nat.divide e n -> False).
    { intros e He Hlt _. lia. }
    destruct (pr_min_factor_sound n (n - 2) Hn (Nat.le_refl (n - 2)) Hvac) as [Hpn _].
    exact Hpn.
  - apply (pr_min_factor_prime n Hn).
Defined.

(* ---- §5 素因子分解存在形（sigT：全素因子列表，fold_right 积==n） ---- *)

Theorem pr_factor_exists : forall n : nat, 2 <= n ->
  { l : list nat | (forall p : nat, In p l -> pr_prime p) /\
                   fold_right Nat.mul 1 l = n }.
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun m : nat => 2 <= m ->
      { l : list nat | (forall p : nat, In p l -> pr_prime p) /\
                       fold_right Nat.mul 1 l = m })).
  intros n IH Hn.
  destruct (pr_min_factor_exists n Hn) as [p [Hpn Hpp]].
  unfold pr_prime in Hpp. destruct Hpp as [Hp2 Hpd].
  assert (Hpn0 : p = 0 -> False) by lia.
  assert (Hmod0 : n mod p = 0).
  { apply (pr_dvd_mod0 p n); [lia | exact Hpn]. }
  assert (Hdm : n = p * (n / p)).
  { assert (Hdm0 : n = p * (n / p) + n mod p) by (apply Nat.div_mod; exact Hpn0).
    rewrite Hmod0 in Hdm0. rewrite Nat.add_0_r in Hdm0. exact Hdm0. }
  destruct (Nat.eq_dec p n) as [Hpe|Hpne].
  - (* n 本身素：列表 [n] *)
    exists (p :: nil). split.
    + intros q Hin. simpl in Hin. destruct Hin as [Heq|Hf].
      * rewrite <- Heq. exact (conj Hp2 Hpd).
      * contradiction.
    + simpl. rewrite Nat.mul_1_r. exact Hpe.
  - (* p < n：对可计算商 n/p 递归，列表 p :: l_q *)
    assert (Hz1 : 1 <= n / p).
    { destruct (n / p) as [|z'] eqn:E.
      - rewrite Nat.mul_0_r in Hdm. lia.
      - lia. }
    assert (Hz2 : 2 <= n / p).
    { destruct (n / p) as [|z'] eqn:E.
      - rewrite Nat.mul_0_r in Hdm. lia.
      - destruct z' as [|z''].
        + exfalso. rewrite Nat.mul_1_r in Hdm.
          apply Hpne. symmetry. exact Hdm.
        + lia. }
    assert (Hq0 : 0 < n / p) by lia.
    assert (Hzltn : n / p < n).
    { assert (Hstep : (n / p) * 1 < (n / p) * p).
      { apply (proj1 (Nat.mul_lt_mono_pos_l (n / p) 1 p Hq0)). lia. }
      rewrite Nat.mul_1_r in Hstep.
      rewrite (Nat.mul_comm (n / p) p) in Hstep.
      rewrite <- Hdm in Hstep. exact Hstep. }
    assert (Hp0 : 0 < p) by lia.
    assert (Hpltn : p < n).
    { assert (Hstep2 : p * 1 < p * (n / p)).
      { apply (proj1 (Nat.mul_lt_mono_pos_l p 1 (n / p) Hp0)). lia. }
      rewrite Nat.mul_1_r in Hstep2. rewrite <- Hdm in Hstep2. exact Hstep2. }
    destruct (IH (n / p) Hzltn Hz2) as [lq [Hallq Hfoldq]].
    exists (p :: lq). split.
    + intros q Hin. simpl in Hin. destruct Hin as [Heq|Hin'].
      * rewrite <- Heq. exact (conj Hp2 Hpd).
      * apply Hallq. exact Hin'.
    + simpl. rewrite Hfoldq. symmetry. exact Hdm.
Defined.

(* ---- §6 数值定装烟测（小实例 ≤ 12，vm_compute 直算零公设） ---- *)

Lemma pr_prime_bool_2 : pr_prime_bool 2 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_3 : pr_prime_bool 3 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_4 : pr_prime_bool 4 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_5 : pr_prime_bool 5 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_9 : pr_prime_bool 9 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_11 : pr_prime_bool 11 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_bool_12 : pr_prime_bool 12 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_min_factor_35 : pr_min_factor 33 35 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_min_factor_49 : pr_min_factor 47 49 = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_trial_12 : pr_trial 10 12 = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- §7 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions pr_dvd_mod0.
Print Assumptions pr_mod0_dvd.
Print Assumptions pr_trial_spec.
Print Assumptions pr_prime_bool_spec.
Print Assumptions pr_min_factor_sound.
Print Assumptions pr_min_factor_prime.
Print Assumptions pr_min_factor_exists.
Print Assumptions pr_factor_exists.
