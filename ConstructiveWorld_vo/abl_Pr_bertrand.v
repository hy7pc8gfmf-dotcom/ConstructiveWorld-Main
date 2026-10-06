(* ============================================================ *)
(* abl_Pr_bertrand.v —— 素数域第 6 件：Bertrand 假设的构造性见证件   *)
(* 模块名：abl_Pr_bertrand                                        *)
(* 数学使命：Bertrand 假设（n<p≤2n）的构造性 witness 形三组——      *)
(*   ①升扫搜索机：pbr_scan n k 在 (n,n+k] 内升扫取首个素数         *)
(*   （bool 判定器逐点检验），pbr_search n 专扫 (n,2n]；双向一般形  *)
(*   spec：pbr_scan_some（找到即真见证，无条件）与 pbr_scan_hit    *)
(*   （窗内确有素则必找到，完备性）；条件形主语句                  *)
(*   pbr_bertrand_cond：存在前提 下搜索出口即 sigT 见证。          *)
(*   ②段表存在引擎：[2,512] 的逐点 Bertrand 见证以（起点,素数,段长）*)
(*   97 段字面段表 pbr_runs 给出；布尔检查器 pbr_runs_ok 逐段核验   *)
(*   素性、段内逐点 n<p≤2n 与段起点连续衔接（nil 端 ltb 守全长），   *)
(*   pbr_runs_good 单点 vm_compute 核验；由此得表域主语句           *)
(*   pbr_bertrand_table（2≤n≤512 的 sigT 见证，见证项为可计算       *)
(*   函数 pbr_pick）与 pbr_search_cert（搜索出口即认证见证）。      *)
(*   ③单调提升与延拓：pbr_lift（n 处见证提升为 (n,p) 内一切 m 处    *)
(*   见证）推出 pbr_bertrand_ext 把无条件覆盖延至 [2,520]；         *)
(*   pbr_bertrand_infinite：对每个 n 构造性给出 m≥n 使 (m,2m] 含素  *)
(*   （取 n 上方素数 p 与 m=p-1，Bertrand 良点集无界）。            *)
(* 设计依据：全强度 Bertrand 登记走 Erdős 二项式系数路线，           *)
(*   属独立后件；                                                    *)
(*   本件交付其表档弱版：一般形为条件形，具体形覆盖 [2,520]。        *)
(* 依赖清单：件 1（abl_Pr_core_01：pr_prime／pr_prime_bool）＋      *)
(*   件 2（abl_Pr_enum_02：pen_prime_unbounded）＋纯 Stdlib         *)
(*   （Arith.Arith／List／Bool／Lia）。五件前置已拷入本池链编；      *)
(*   Hanson 系（件 4/5 所需）由统一缓存根供，本件不使用。           *)
(* 构造性注记：主语句五条全为 sigT（Type 面）见证形——见证明项为     *)
(*   可计算函数（pbr_pick／pbr_opt_witness），严于 Prop 面 sig 承载； *)
(*   pr_prime 谓词仅作推理脚手架（件 1 先例）；否定形自持 P -> False，*)
(*   全件零 not／~／<> 记号（含证明内部）；零公理零承认零经典逻辑；  *)
(*   计算件 pbr_scan／pbr_pick／pbr_opt_witness／pbr_run_ok／       *)
(*   pbr_runs_ok／pbr_runs_len 皆一阶 nat/bool/list Fixpoint 可提取； *)
(*   数值核验口径：段表把 511 点压缩为 97 段，素性逐素仅验一次        *)
(*   （值域 ≤521），单点 vm_compute 一次通过；另附 ≤12 小实例与       *)
(*   纯表行走检验（pbr_pick_512_val 等零素性开销）。                 *)
(* 编译配方：                                                      *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/  *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&  *)
(*   nice -19 rocq c -native-compiler no -Q                          *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 "" *)
(*   -Q . "" abl_Pr_bertrand.v                                      *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.

(* ---- §0 表域常量与段表数据 ----
   段（n0,p,len）义：对每个 i<len，n=n0+i 的 Bertrand 见证同为 p。
   表覆盖 [2,512] 共 511 点、97 段；相邻段起点相差段长，首段起点为 2。 *)

Definition pbr_N : nat := 512.

Definition pbr_runs : list (nat * nat * nat) :=
  (2,3,1) :: (3,5,2) :: (5,7,2) :: (7,11,4) :: (11,13,2) :: (13,17,4) ::
  (17,19,2) :: (19,23,4) :: (23,29,6) :: (29,31,2) :: (31,37,6) :: (37,41,4) ::
  (41,43,2) :: (43,47,4) :: (47,53,6) :: (53,59,6) :: (59,61,2) :: (61,67,6) ::
  (67,71,4) :: (71,73,2) :: (73,79,6) :: (79,83,4) :: (83,89,6) :: (89,97,8) ::
  (97,101,4) :: (101,103,2) :: (103,107,4) :: (107,109,2) :: (109,113,4) :: (113,127,14) ::
  (127,131,4) :: (131,137,6) :: (137,139,2) :: (139,149,10) :: (149,151,2) :: (151,157,6) ::
  (157,163,6) :: (163,167,4) :: (167,173,6) :: (173,179,6) :: (179,181,2) :: (181,191,10) ::
  (191,193,2) :: (193,197,4) :: (197,199,2) :: (199,211,12) :: (211,223,12) :: (223,227,4) ::
  (227,229,2) :: (229,233,4) :: (233,239,6) :: (239,241,2) :: (241,251,10) :: (251,257,6) ::
  (257,263,6) :: (263,269,6) :: (269,271,2) :: (271,277,6) :: (277,281,4) :: (281,283,2) ::
  (283,293,10) :: (293,307,14) :: (307,311,4) :: (311,313,2) :: (313,317,4) :: (317,331,14) ::
  (331,337,6) :: (337,347,10) :: (347,349,2) :: (349,353,4) :: (353,359,6) :: (359,367,8) ::
  (367,373,6) :: (373,379,6) :: (379,383,4) :: (383,389,6) :: (389,397,8) :: (397,401,4) ::
  (401,409,8) :: (409,419,10) :: (419,421,2) :: (421,431,10) :: (431,433,2) :: (433,439,6) ::
  (439,443,4) :: (443,449,6) :: (449,457,8) :: (457,461,4) :: (461,463,2) :: (463,467,4) ::
  (467,479,12) :: (479,487,8) :: (487,491,4) :: (491,499,8) :: (499,503,4) :: (503,509,6) ::
  (509,521,4) :: nil.

(* ---- §1 升扫搜索机（option 出口；0 不作返回值，燃料即窗宽） ---- *)

Fixpoint pbr_scan (n k : nat) : option nat :=
  match k with
  | 0 => None
  | S k' => if pr_prime_bool (S n) then Some (S n) else pbr_scan (S n) k'
  end.

Definition pbr_search (n : nat) : option nat := pbr_scan n n.

Definition pbr_opt_witness (n : nat) : nat :=
  match pbr_search n with
  | Some p => p
  | None => 0
  end.

Lemma pbr_scan_S : forall n k : nat,
  pbr_scan n (S k) =
  (if pr_prime_bool (S n) then Some (S n) else pbr_scan (S n) k).
Proof. reflexivity. Qed.

(* 健全性：搜索返回值必为窗内素数（无条件，一般形） *)
Lemma pbr_scan_some : forall k n p : nat,
  pbr_scan n k = Some p -> n < p /\ p <= n + k /\ pr_prime p.
Proof.
  intros k. induction k as [|k IH]; intros n p H.
  - discriminate.
  - rewrite pbr_scan_S in H. destruct (pr_prime_bool (S n)) eqn:Eb.
    + injection H as Hp. subst p.
      split; [lia | split; [lia | apply pr_prime_bool_true; exact Eb]].
    + apply IH in H. destruct H as [H1 [H2 H3]].
      split; [lia | split; [lia | exact H3]].
Qed.

(* 完备性：窗内确有素则搜索必命中（无条件，一般形；终止性由燃料即
   窗宽自然给出，命中论证不需额外引理） *)
Lemma pbr_scan_hit : forall k n q : nat,
  n < q -> q <= n + k -> pr_prime q ->
  exists p : nat, pbr_scan n k = Some p.
Proof.
  intros k. induction k as [|k IH]; intros n q Hnq Hqk Hq.
  - exfalso. lia.
  - rewrite pbr_scan_S. destruct (pr_prime_bool (S n)) eqn:Eb.
    + exists (S n). reflexivity.
    + assert (Hq2 : S n < q).
      { destruct (Nat.eq_dec q (S n)) as [Heq|Hne].
        - exfalso.
          assert (Hb1 : pr_prime_bool (S n) = true).
          { rewrite <- Heq. apply pr_prime_bool_false. exact Hq. }
          rewrite Hb1 in Eb. discriminate.
        - lia. }
      apply (IH (S n) q); [exact Hq2 | lia | exact Hq].
Qed.

Lemma pbr_search_some : forall n p : nat,
  pbr_search n = Some p -> n < p /\ p <= 2 * n /\ pr_prime p.
Proof.
  intros n p H. unfold pbr_search in H.
  apply (pbr_scan_some n n p) in H. destruct H as [H1 [H2 H3]].
  split; [exact H1 | split; [lia | exact H3]].
Qed.

Lemma pbr_search_hit : forall n q : nat,
  n < q -> q <= 2 * n -> pr_prime q ->
  exists p : nat, pbr_search n = Some p.
Proof.
  intros n q Hnq Hqn Hq. unfold pbr_search.
  apply (pbr_scan_hit n n q); [exact Hnq | lia | exact Hq].
Qed.

(* 搜索出口的可计算见证读出（None 分支由前提排除） *)
Lemma pbr_opt_witness_eq : forall n : nat,
  (pbr_search n = None -> False) ->
  pbr_search n = Some (pbr_opt_witness n).
Proof.
  intros n Hne. revert Hne.
  destruct (pbr_search n) as [p|] eqn:E.
  - intros _. unfold pbr_opt_witness. rewrite E. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
Qed.

(* ---- §2 段表检查器与核验引理 ---- *)

Fixpoint pbr_run_ok (k p len : nat) : bool :=
  match len with
  | 0 => true
  | S len' => andb (andb (Nat.ltb k p) (Nat.leb p (2 * k))) (pbr_run_ok (S k) p len')
  end.

Fixpoint pbr_runs_ok (k : nat) (l : list (nat * nat * nat)) : bool :=
  match l with
  | nil => Nat.ltb pbr_N k
  | (n0, p, len) :: l' =>
      andb (Nat.eqb k n0)
           (andb (pr_prime_bool p)
                 (andb (pbr_run_ok k p len) (pbr_runs_ok (k + len) l')))
  end.

Fixpoint pbr_runs_len (l : list (nat * nat * nat)) : nat :=
  match l with
  | nil => 0
  | (n0, p, len) :: l' => len + pbr_runs_len l'
  end.

Fixpoint pbr_pick (n : nat) (l : list (nat * nat * nat)) : nat :=
  match l with
  | nil => 0
  | (n0, p, len) :: l' => if Nat.ltb n (n0 + len) then p else pbr_pick n l'
  end.

Lemma pbr_run_ok_S : forall k p len : nat,
  pbr_run_ok k p (S len) =
  andb (andb (Nat.ltb k p) (Nat.leb p (2 * k))) (pbr_run_ok (S k) p len).
Proof. reflexivity. Qed.

Lemma pbr_runs_ok_cons : forall k n0 p len l,
  pbr_runs_ok k ((n0, p, len) :: l) =
  andb (Nat.eqb k n0)
       (andb (pr_prime_bool p)
             (andb (pbr_run_ok k p len) (pbr_runs_ok (k + len) l))).
Proof. reflexivity. Qed.

Lemma pbr_runs_len_cons : forall n0 p len l,
  pbr_runs_len ((n0, p, len) :: l) = len + pbr_runs_len l.
Proof. reflexivity. Qed.

Lemma pbr_pick_cons : forall n n0 p len l,
  pbr_pick n ((n0, p, len) :: l) =
  (if Nat.ltb n (n0 + len) then p else pbr_pick n l).
Proof. reflexivity. Qed.

(* 段内逐点窗口：len 段上 k+i 处皆 k+i<p≤2(k+i) *)
Lemma pbr_run_ok_spec : forall len k p : nat,
  pbr_run_ok k p len = true ->
  forall i : nat, i < len -> k + i < p /\ p <= 2 * (k + i).
Proof.
  intros len. induction len as [|len IH]; intros k p Hok i Hi.
  - exfalso. lia.
  - rewrite pbr_run_ok_S in Hok.
    apply andb_true_iff in Hok. destruct Hok as [H1 Hok].
    apply andb_true_iff in H1. destruct H1 as [Hlt Hle].
    apply Nat.ltb_lt in Hlt. apply Nat.leb_le in Hle.
    destruct i as [|i'].
    + rewrite Nat.add_0_r. split; [exact Hlt | exact Hle].
    + assert (Hih : i' < len) by lia.
      destruct (IH (S k) p Hok i' Hih) as [Ha Hb].
      split; lia.
Qed.

(* 主核验引理：检查器通过则取值函数 pbr_pick 在表域逐点给出
   「严格落窗、素、窗上界」三重见证（覆盖与取值一体归纳） *)
Lemma pbr_runs_ok_pick : forall (l : list (nat * nat * nat)) (k n : nat),
  pbr_runs_ok k l = true -> k <= n -> n < k + pbr_runs_len l ->
  n < pbr_pick n l /\ pr_prime (pbr_pick n l) /\ pbr_pick n l <= 2 * n.
Proof.
  intros l. induction l as [| [[n0 p] len] l IH]; intros k n Hok Hkn Hlt.
  - exfalso. simpl in Hlt. lia.
  - rewrite pbr_runs_len_cons in Hlt.
    rewrite pbr_runs_ok_cons in Hok.
    apply andb_true_iff in Hok. destruct Hok as [Hke Hok].
    apply andb_true_iff in Hok. destruct Hok as [Hpb Hok].
    apply andb_true_iff in Hok. destruct Hok as [Hrun Hrest].
    apply Nat.eqb_eq in Hke. subst n0.
    assert (Hpp : pr_prime p) by (apply pr_prime_bool_true; exact Hpb).
    rewrite pbr_pick_cons.
    destruct (Nat.ltb n (k + len)) eqn:Hdec.
    + change (if true then p else pbr_pick n l) with p.
      apply Nat.ltb_lt in Hdec.
      assert (Hi : n - k < len) by lia.
      destruct (pbr_run_ok_spec len k p Hrun (n - k) Hi) as [Ha Hb].
      assert (Hk : k + (n - k) = n) by lia.
      rewrite Hk in Ha, Hb.
      split; [exact Ha | split; [exact Hpp | exact Hb]].
    + change (if false then p else pbr_pick n l) with (pbr_pick n l).
      apply Nat.ltb_ge in Hdec.
      apply (IH (k + len) n); [exact Hrest | lia | lia].
Qed.

(* ---- §3 段表核验点（vm_compute 机械核验） ---- *)

Lemma pbr_runs_len_val : pbr_runs_len pbr_runs = 511.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_runs_good : pbr_runs_ok 2 pbr_runs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_pick_512_val : pbr_pick 512 pbr_runs = 521.
Proof. vm_compute. reflexivity. Qed.

(* ---- §4 表域主语句（sigT 见证形；见证项为可计算函数） ---- *)

Theorem pbr_bertrand_table : forall n : nat, 2 <= n -> n <= pbr_N ->
  { p : nat & n < p /\ pr_prime p /\ p <= 2 * n }.
Proof.
  intros n H2 Hn. unfold pbr_N in Hn.
  assert (Hlt : n < 2 + pbr_runs_len pbr_runs) by (rewrite pbr_runs_len_val; lia).
  destruct (pbr_runs_ok_pick pbr_runs 2 n pbr_runs_good H2 Hlt) as [Ha [Hb Hc]].
  exists (pbr_pick n pbr_runs). split; [exact Ha | split; [exact Hb | exact Hc]].
Defined.

Theorem pbr_search_cert : forall n : nat, 2 <= n -> n <= pbr_N ->
  { p : nat & n < p /\ pr_prime p /\ p <= 2 * n /\ pbr_search n = Some p }.
Proof.
  intros n H2 Hn. unfold pbr_N in Hn.
  assert (Htab : n < pbr_pick n pbr_runs /\ pr_prime (pbr_pick n pbr_runs) /\
                 pbr_pick n pbr_runs <= 2 * n).
  { assert (Hlt : n < 2 + pbr_runs_len pbr_runs) by (rewrite pbr_runs_len_val; lia).
    exact (pbr_runs_ok_pick pbr_runs 2 n pbr_runs_good H2 Hlt). }
  destruct Htab as [Ht1 [Ht2 Ht3]].
  assert (Hhit : exists p0 : nat, pbr_search n = Some p0).
  { exact (pbr_search_hit n (pbr_pick n pbr_runs) Ht1 Ht3 Ht2). }
  assert (Hne : pbr_search n = None -> False).
  { intros Hnone. destruct Hhit as [p0 Hp0]. rewrite Hnone in Hp0. discriminate. }
  assert (Heq : pbr_search n = Some (pbr_opt_witness n)) by (apply pbr_opt_witness_eq; exact Hne).
  unfold pbr_search in Heq.
  destruct (pbr_scan_some n n (pbr_opt_witness n) Heq) as [Hs1 [Hs2 Hs3]].
  exists (pbr_opt_witness n).
  split; [exact Hs1 | split; [exact Hs3 | split; [lia | exact Heq]]].
Defined.

(* ---- §5 单调提升、表域延拓与良点无界 ---- *)

(* 区间单调提升：n 处见证 p 提升至 (n,p) 内一切 m 处
   （m>n 得 2m>2n≥p，m<p 由前提） *)
Lemma pbr_lift : forall n m q : nat,
  n < m -> m < q -> q <= 2 * n -> pr_prime q ->
  m < q /\ q <= 2 * m /\ pr_prime q.
Proof.
  intros n m q Hnm Hmq Hqn Hq.
  split; [exact Hmq | split; [lia | exact Hq]].
Qed.

(* 表域延拓：末段见证 521 覆盖 (512,521)，无条件覆盖延至 [2,520] *)
Theorem pbr_bertrand_ext : forall n : nat, 2 <= n -> n <= 520 ->
  { p : nat & n < p /\ pr_prime p /\ p <= 2 * n }.
Proof.
  intros n H2 Hn.
  destruct (le_gt_dec n pbr_N) as [Hle | Hgt].
  - exact (pbr_bertrand_table n H2 Hle).
  - assert (Hcov : 512 < pbr_pick 512 pbr_runs /\ pr_prime (pbr_pick 512 pbr_runs) /\
                   pbr_pick 512 pbr_runs <= 2 * 512).
    { apply (pbr_runs_ok_pick pbr_runs 2 512 pbr_runs_good).
      - lia.
      - rewrite pbr_runs_len_val. lia. }
    rewrite pbr_pick_512_val in Hcov.
    destruct Hcov as [Ha [Hb Hc]].
    assert (Hn521 : n < 521) by lia.
    destruct (pbr_lift 512 n 521 Hgt Hn521 Hc Hb) as [H1 [H2' H3]].
    exists 521. split; [exact H1 | split; [exact H3 | exact H2']].
Defined.

(* 良点无界：对每个 n 存在 m≥n 使 (m,2m] 含素——取 n 上方素数 p，
   m=p-1 即良点（m<p 且 p≤2m ⟺ p≥2）；Bertrand 良点集因此无界 *)
Theorem pbr_bertrand_infinite : forall n : nat,
  { m : nat & (n <= m) * { p : nat & m < p /\ pr_prime p /\ p <= 2 * m } }.
Proof.
  intros n.
  assert (Hpp : pr_prime (proj1_sig (pen_prime_unbounded n)) /\
                n < proj1_sig (pen_prime_unbounded n)).
  { destruct (pen_prime_unbounded n) as [q Hq]. exact Hq. }
  destruct Hpp as [Hpr Hn0]. destruct Hpr as [Hp02 Hpd].
  exists (proj1_sig (pen_prime_unbounded n) - 1). split; [lia | ].
  exists (proj1_sig (pen_prime_unbounded n)). split; [lia | ].
  split; [exact (conj Hp02 Hpd) | lia].
Defined.

(* ---- §6 条件形一般主语句（全强度 Bertrand 的条件化） ---- *)

Theorem pbr_bertrand_cond : forall n : nat,
  (exists q : nat, pr_prime q /\ n < q /\ q <= 2 * n) ->
  { p : nat & n < p /\ pr_prime p /\ p <= 2 * n /\ pbr_search n = Some p }.
Proof.
  intros n Hget.
  assert (Hne : pbr_search n = None -> False).
  { intros Hnone.
    assert (Hhit : exists p0 : nat, pbr_search n = Some p0).
    { destruct Hget as [q [Hq [Hnq Hqn]]].
      exact (pbr_search_hit n q Hnq Hqn Hq). }
    destruct Hhit as [p0 Hp0]. rewrite Hnone in Hp0. discriminate. }
  assert (Heq : pbr_search n = Some (pbr_opt_witness n)) by (apply pbr_opt_witness_eq; exact Hne).
  unfold pbr_search in Heq.
  destruct (pbr_scan_some n n (pbr_opt_witness n) Heq) as [Hs1 [Hs2 Hs3]].
  exists (pbr_opt_witness n).
  split; [exact Hs1 | split; [exact Hs3 | split; [lia | exact Heq]]].
Defined.

(* ---- §7 数值核验（小实例 vm_compute；≤12 与纯表行走） ---- *)

Lemma pbr_search_10 : pbr_search 10 = Some 11.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_search_12 : pbr_search 12 = Some 13.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_opt_4 : pbr_opt_witness 4 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_pick_100 : pbr_pick 100 pbr_runs = 101.
Proof. vm_compute. reflexivity. Qed.

(* ---- §8 公理检查（Print Assumptions 取证面） ---- *)

Print Assumptions pbr_scan_some.
Print Assumptions pbr_scan_hit.
Print Assumptions pbr_search_some.
Print Assumptions pbr_search_hit.
Print Assumptions pbr_run_ok_spec.
Print Assumptions pbr_runs_ok_pick.
Print Assumptions pbr_bertrand_table.
Print Assumptions pbr_search_cert.
Print Assumptions pbr_lift.
Print Assumptions pbr_bertrand_ext.
Print Assumptions pbr_bertrand_infinite.
Print Assumptions pbr_bertrand_cond.
