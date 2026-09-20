(* ============================================================ *)
(* UpAblRateAlgPkg.v —— 抽象率代数封装：可算法化率形的充分条件刻画           *)
(*                                                                *)
(* 使命：把 mix_k_select 的证明路线抽象为参数化率代数封装 rap_alg——         *)
(*   「何种率形可算法化」的正面刻画（充分条件方向；非必要条件完备刻画——     *)
(*   不可算法化一侧由 UpAblLogWall 的构造性不可达定理承载，两侧对照）。      *)
(* 本件为松弛形算法化件 UpAblSlackMix.v 的姊妹抽象层。                      *)
(*                                                                *)
(* 三件（rap_ 前缀）：                                                      *)
(*   件① 率代数接口 rap_alg（Record 形，Record/Class/Section 三形中         *)
(*     择 Record——与 mixb_sel 的纯 nat/bool 泛型函数形最贴合，且免出节     *)
(*     Module 限定名）。字段六：                                            *)
(*       rap_rate   : nat -> Real                    （率列）                *)
(*       rap_budget : Real                           （预算）                *)
(*       rap_test   : nat -> bool                    （可判定测试，包供给）  *)
(*       rap_mono   : mixb_mono rap_test             （过站集上闭性——单调    *)
(*       递减性的操作化形：率形递减 ⟺ 过站集上闭；接口取搜索核直接使用的    *)
(*       后者，率形递减由件③实例层 rap_geom_rate_dec 语义化）               *)
(*       rap_pass   : sigT k, rap_test k = true      （过站窗 existence——   *)
(*       取 bool 级窗（比 Real 级窗前提更弱、定理更强）；Real 级存在性       *)
(*       由 rap_bridge 与 rap_pass 一步推得，直接可得不另立定理面）          *)
(*       rap_bridge : forall n, rap_test n = true ->                        *)
(*                    real_lt (rap_rate n) rap_budget（Real 语义桥——       *)
(*                   测试真值 ⟹ Real 严格达标，包的语义条件）；              *)
(*   字段六皆为算法化的充分条件：用法见件②③。                              *)
(*   件② 主定理 rap_k_select：率代数封装 ⟹ sigT k, real_lt (rate k)        *)
(*     budget。证明 = mixb 泛型核 + 包字段合成：零站即过经桥一步闭合；      *)
(*     否则 igr_k_enum 于窗站 kw 内定位最小站 kmin（sound/min 两引理），     *)
(*     界 K := max(kw,2) 给定双相 fuel := S(S(log2 K))，mixb_sel           *)
(*     倍增+二分返回其输出站 r，rap_sel_true（经 mixb_sel_scale）           *)
(*     证 test r = true，经桥一步闭合。非平凡增量：返回站=最小过站，        *)
(*     且测试次数 ≤ 2·log₂K+5（rap_k_select_account 给出，Qed 面）。       *)
(*     + rap_k_select_le（_le 对偶，一步推得）。                            *)
(*   件③ 几何率实例 rap_geom_alg：rate k := κ^k·A（real_ 面                *)
(*     tv_rpow 形），使用 mixb 检测/窗/回传链全家（mixb_qtest 测试 +       *)
(*     mixb_qtest_mono 单调 + real_arch 窗底 + mixb_window_test_true       *)
(*     + mixb_real_chain 回传桥）——mix_k_select 语义的包级复现（语义      *)
(*     级实例，不逐字回替）；+ rap_geom_rate_dec（率形单调递减——          *)
(*     接口 rap_mono 字段在实例层的语义化，使用 mix_rpow_nonneg/           *)
(*     mix_mult_one_l）。                                                   *)
(* 范围注记（如实申报，零重复）：松弛率形实例（rate k := κ^k·A + k·eps     *)
(*   固定 eps）已由 UpAblSlackMix 覆盖——slm_slack_select 即该率形的        *)
(*   算法化（率界接口前提形，非 bool 测试形），本包不另做翻版，零重复。      *)
(* 诚实边界：本封装刻画=充分条件（入包即可算法化+最小站+对数测试次数界），  *)
(*   非必要条件完备刻画；无可判定测试的率形（如纯 Real 层不可判定测试形）   *)
(*   不入封装，其不可算法化一侧由 UpAblLogWall 的构造性不可达定理承载。     *)
(*                                                                *)
(* 上游（零改母本）：CW_ConstructiveWorld_219 基座 + UpReqIterGeomRate      *)
(*   （igr_k_enum 三引理）+ UpReqMixLogB（mixb_sel 搜索核/scale 引理/       *)
(*   qtest 全家——搜索直接使用 mixb_sel）+ UpTVDoeblin（tv_rpow，           *)
(*   件③用）+ UpReqMixingTime（mix_rpow_nonneg/mix_mult_one_l，            *)
(*   件③单调性用）。                                                       *)
(* 构造性注记：零承认、零经典逻辑（全件显式见证式构造）；语句面全 Set 层    *)
(*   （sigT 载荷 real_lt/real_le 全 Set；rap_mono 为 Qed 面字段、rap_pass   *)
(*   为 Type 层 sigT 窗，Defined 体内零 Prop 消去——Prop 只以 Qed 引理      *)
(*   应用形态进出）；主定理非平凡增量=最小站与对数测试次数界                *)
(*   （rap_k_select_account）；Set 组件 Separate Extraction 提取输出        *)
(*   不含 Obj.magic。                                                       *)
(* 编译配方：Rocq 9.1 直调 coqc + cpu_guard（-LoadLimit 85 -CoreN 2），     *)
(*   输出至临时目录，树内零写入。                                           *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogB.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.

(* ============================================================ *)
(* §1 率代数接口（件①）——可算法化率形的充分条件刻画                        *)
(* ============================================================ *)

Record rap_alg : Type := mk_rap_alg {
  rap_rate   : nat -> Real;
  rap_budget : Real;
  rap_test   : nat -> bool;
  rap_mono   : mixb_mono rap_test;
  rap_pass   : sigT (fun k : nat => rap_test k = true);
  rap_bridge : forall n : nat,
                 rap_test n = true -> real_lt (rap_rate n) rap_budget
}.

(* ============================================================ *)
(* §2 搜索辅助引理与主定理（件②）                                          *)
(* ============================================================ *)

(* bool 同站真假矛盾辅助引理（窗站穷尽矛盾情形用）                          *)
Lemma rap_bool_contra : forall b : bool, b = true -> b = false -> False.
Proof.
  intros b H1 H2. rewrite H1 in H2. discriminate H2.
Qed.

(* 辅助引理：双相 fuel 给定下 mixb_sel 的输出站必过测试                     *)
(*（mixb_sel_scale 第一合取支的 Set 面出口——Prop 只以引理应用形态       *)
(*  进 Defined 体，零 Prop 消去） *)
Lemma rap_sel_true : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false -> test k = true ->
  (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k)%nat -> (k <= K)%nat -> (2 <= K)%nat ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  test r = true.
Proof.
  intros test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel.
  destruct (mixb_sel_scale test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel)
    as [Hrk _].
  rewrite Hrk. exact Htk.
Qed.

(* 主定理：凡入封装率形皆可预算驱动返回步数（最小过站，对数测试）           *)
Definition rap_k_select (p : rap_alg) :
  sigT (fun k : nat => real_lt (rap_rate p k) (rap_budget p)).
Proof.
  destruct p as [rate budget test mono pass bridge].
  destruct (test 0%nat) eqn:E0.
  - (* 零站即过：k := 0 经桥一步闭合 *)
    exact (existT _ 0%nat (bridge 0%nat E0)).
  - (* 窗站 kw → 界 K := max(kw,2) → 最小站 kmin → 双相搜索 → 桥 *)
    destruct pass as [kw Hkw].
    destruct (igr_k_enum test kw) as [kmin|] eqn:Eenum.
    + pose proof (igr_k_enum_sound test kw kmin Eenum) as Hsnd.
      pose proof (igr_k_enum_min test kw kmin Eenum) as Hmin.
      pose proof (mixb_enum_le test kw kmin Eenum) as HminK.
      assert (H1 : (1 <= kmin)%nat).
      { destruct kmin as [| m]. exfalso. congruence. lia. }
      assert (HK : (kmin <= Nat.max kw 2)%nat)
        by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                    (Nat.le_max_l kw 2))).
      assert (HK2 : (2 <= Nat.max kw 2)%nat) by (apply Nat.le_max_r).
      destruct (mixb_sel test
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))))
        as [r c] eqn:Esel.
      exact (existT _ r
               (bridge r
                  (rap_sel_true test (Nat.max kw 2) kmin r c mono E0 Hsnd
                     Hmin H1 HK HK2 Esel))).
    + (* 无窗矛盾：kw ≤ kw 燃料下枚举必有站 *)
      exact (False_rect _
               (rap_bool_contra (test kw) Hkw
                  (igr_k_enum_none test kw Eenum kw (Nat.le_refl kw)))).
Defined.

(* _le 对偶（一步推得） *)
Definition rap_k_select_le (p : rap_alg) :
  sigT (fun k : nat => real_le (rap_rate p k) (rap_budget p)).
Proof.
  destruct (rap_k_select p) as [k Hk].
  exact (existT _ k
           (RealSetoid.real_lt_le_iff_req (rap_rate p k) (rap_budget p)
              (inl Hk))).
Defined.

(* 量级界（Qed 面）：返回站过、以下全败、测试次数 ≤ 2·log₂K+5              *)
Corollary rap_k_select_account : forall (p : rap_alg) (kw r c : nat),
  rap_test p 0%nat = false ->
  rap_test p kw = true ->
  mixb_sel (rap_test p)
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))) = (r, c) ->
  rap_test p r = true /\
  (forall j : nat, (j < r)%nat -> rap_test p j = false) /\
  (c <= 2 * (Nat.log2 (Nat.max kw 2)) + 5)%nat.
Proof.
  intros p kw r c H0 Hkw Esel.
  destruct (igr_k_enum (rap_test p) kw) as [kmin|] eqn:Eenum.
  - pose proof (igr_k_enum_sound (rap_test p) kw kmin Eenum) as Hsnd.
    pose proof (igr_k_enum_min (rap_test p) kw kmin Eenum) as Hmin.
    pose proof (mixb_enum_le (rap_test p) kw kmin Eenum) as HminK.
    assert (H1 : (1 <= kmin)%nat).
    { destruct kmin as [| m].
      - rewrite H0 in Hsnd. discriminate Hsnd.
      - lia. }
    assert (HK : (kmin <= Nat.max kw 2)%nat)
      by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                  (Nat.le_max_l kw 2))).
    destruct (mixb_sel_scale (rap_test p) (Nat.max kw 2) kmin r c
                (rap_mono p) H0 Hsnd Hmin H1 HK (Nat.le_max_r kw 2) Esel)
      as [Hrk Hcnt].
    rewrite Hrk.
    split; [ exact Hsnd | split; [ exact Hmin | exact Hcnt ] ].
  - exfalso.
    exact (rap_bool_contra (rap_test p kw) Hkw
             (igr_k_enum_none (rap_test p) kw Eenum kw (Nat.le_refl kw))).
Qed.

(* ============================================================ *)
(* §3 几何率实例（件③，real_ 面 tv_rpow 形）                               *)
(* ============================================================ *)

Local Open Scope Q_scope.

(* 包级实例：rate k := κ^k·A，测试 := mixb_qtest κ0 v b0（Q 层可判定），  *)
(* 桥 := mixb_real_chain 回传链，窗 := real_arch 兜底 + Q-Bernoulli 反解。 *)
(* 证书拆显式参数、构造器直出（体内零 destruct）——投影换算面保归约，    *)
(* 使用侧推论在自身体内做证书拆分。 *)
(* ——mix_k_select 语义的包级复现（语义级实例，不逐字回替）。 *)
Definition rap_geom_alg (kappa A B : Real) (v : Q)
  (Hk1 : real_lt real_zero kappa)
  (HA : real_le real_zero A)
  (epsK : Q) (HepsK : QltT 0 epsK) (NK : nat)
  (HNK : forall n : nat, NatLe NK n -> QltT epsK (projT1 real_one n - projT1 kappa n))
  (Hvc : real_le A (real_const v))
  (epsB : Q) (HepsB : QltT 0 epsB) (NB : nat)
  (HNB : forall n : nat, NatLe NB n -> QltT epsB (projT1 B n - projT1 real_zero n))
  : rap_alg.
Proof.
  assert (Hk0 : 0 < 1 - mixb_mu epsK)
    by (apply mixb_kappa0_pos; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hk0lt : 1 - mixb_mu epsK < 1)
    by (apply mixb_kappa0_lt_one; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hb0 : 0 < epsB * (1 # 2)).
  { apply (Qmult_lt_0_compat epsB (1 # 2)).
    - exact (QltT_to_Qlt 0 epsB HepsB).
    - exact mixb_q_12_pos. }
  assert (Hv0 : 0 <= v) by exact (mixb_v_nonneg A v HA Hvc).
  assert (Hk0le : real_le kappa (real_const (1 - mixb_mu epsK))).
  { apply (RealSetoid.real_lt_le_iff_req). left.
    exact (mixb_kappa0_bridge kappa epsK NK HepsK HNK). }
  assert (Hc0pos : real_lt real_zero (real_const (1 - mixb_mu epsK)))
    by exact (mixb_qpos_const_lt _ Hk0).
  assert (Hbb : real_lt (real_const (epsB * (1 # 2))) B)
    by exact (mixb_b0_bridge B epsB NB HepsB HNB).
  apply (mk_rap_alg (fun k : nat => real_mult (tv_rpow kappa k) A) B
           (mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)))).
  - (* 单调：Q 幂递减 × v 非负 ⟹ 过站集上闭 *)
    exact (mixb_qtest_mono (1 - mixb_mu epsK) v (epsB * (1 # 2)) Hk0
             (Qlt_le_weak (1 - mixb_mu epsK) 1 Hk0lt) Hv0).
  - (* 过站窗：real_arch 兜底 + Q-Bernoulli 反解 *)
    pose (wb := ((1 - (1 - mixb_mu epsK)) * (epsB * (1 # 2)))%Q).
    assert (Hwbpos : 0 < wb).
    { pose proof (mixb_mu_pos epsK (QltT_to_Qlt 0 epsK HepsK)) as Hmu.
      unfold wb.
      apply (Qmult_lt_0_compat (1 - (1 - mixb_mu epsK))
               (epsB * (1 # 2))); [ lra | exact Hb0 ]. }
    assert (Hwbne : ~ (wb == 0)).
    { intro He. apply (Qlt_not_eq 0 wb Hwbpos). apply mixb_qeq_sym.
      exact He. }
    destruct (real_arch (real_const (v * Qinv wb))) as [nA Hpair].
    destruct Hpair as [Hnge2 Harchlt].
    assert (Hqarch : Qlt (v * Qinv wb) (Z.of_nat nA # 1))
      by exact (mixb_const_lt_to_Qlt _ _ Harchlt).
    assert (Hwin : Qle v ((Z.of_nat nA # 1) * wb)).
    { apply Qlt_le_weak.
      apply (Qle_lt_trans v ((v * Qinv wb) * wb)
               ((Z.of_nat nA # 1) * wb)).
      - apply qeq_le. apply mixb_qeq_sym.
        exact (mixb_qmul_inv_cancel v wb Hwbpos).
      - exact (Qmult_lt_compat_r (v * Qinv wb) (Z.of_nat nA # 1) wb
                 Hwbpos Hqarch). }
    assert (HpassnA : mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA
                      = true).
    { apply (mixb_window_test_true (1 - mixb_mu epsK) v (epsB * (1 # 2))
               nA Hk0 Hk0lt Hv0 Hb0); [ lia | exact Hwin ]. }
    exact (existT _ nA HpassnA).
  - (* Real 语义桥：测试真值 ⟹ κ^n·A < B（mixb 回传链） *)
    intros n Hn.
    exact (mixb_real_chain kappa A B (1 - mixb_mu epsK) v (epsB * (1 # 2))
             n Hk1 Hk0le Hc0pos HA Hvc Hbb Hn).
Defined.

(* 包级语义复现：几何率形 κ^k·A 的预算驱动步返回（mix_k_select 语义）      *)
(* ——证书拆分在本推论体内完成，包构造器直出故投影换算一步闭合。           *)
Corollary rap_geom_k_select : forall (kappa A B : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A -> real_lt real_zero B ->
  sigT (fun v : Q => real_le A (real_const v)) ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) A) B).
Proof.
  intros kappa A B Hk1 Hk2 HA Hb Htv.
  destruct Hk2 as [epsK [HepsK [NK HNK]]].
  destruct Hb as [epsB [HepsB [NB HNB]]].
  destruct Htv as [v Hvc].
  exact (rap_k_select
           (rap_geom_alg kappa A B v Hk1 HA epsK HepsK NK HNK Hvc
              epsB HepsB NB HNB)).
Defined.

(* 率形单调递减（接口 rap_mono 字段的实例层语义化）：κ ≤ 1 收缩因子        *)
Theorem rap_geom_rate_dec : forall (kappa A : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A ->
  forall (n : nat),
  real_le (real_mult (tv_rpow kappa (Datatypes.S n)) A)
          (real_mult (tv_rpow kappa n) A).
Proof.
  intros kappa A Hk1 Hk2 HA n.
  assert (Hk2le : real_le kappa real_one).
  { exact (RealSetoid.real_lt_le_iff_req kappa real_one (inl Hk2)). }
  assert (Hnn : real_le real_zero (tv_rpow kappa n)).
  { exact (mix_rpow_nonneg kappa n
             (RealSetoid.real_lt_le_iff_req real_zero kappa (inl Hk1))). }
  assert (Hstep : real_le (real_mult kappa (tv_rpow kappa n))
                          (real_mult real_one (tv_rpow kappa n)))
    by (exact (real_le_mult_compat_weak kappa real_one (tv_rpow kappa n)
                 Hnn Hk2le)).
  apply (real_le_trans _ (real_mult (real_mult real_one (tv_rpow kappa n)) A)
                        (real_mult (tv_rpow kappa n) A)).
  - apply (real_le_trans _ (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + apply (RealSetoid.real_eq_le).
      exact (real_eq_refl (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + exact (real_le_mult_compat_weak
               (real_mult kappa (tv_rpow kappa n))
               (real_mult real_one (tv_rpow kappa n)) A HA Hstep).
  - apply (RealSetoid.real_eq_le).
    exact (RealSetoid.real_eq_mult_compat
             (real_mult real_one (tv_rpow kappa n)) A
             (tv_rpow kappa n) A
             (mix_mult_one_l (tv_rpow kappa n)) (real_eq_refl A)).
Qed.

(* ============================================================ *)
(* 假设审计（零承认件，全 Closed 预期）                                     *)
(* ============================================================ *)

Print Assumptions rap_sel_true.
Print Assumptions rap_k_select.
Print Assumptions rap_k_select_le.
Print Assumptions rap_k_select_account.
Print Assumptions rap_geom_alg.
Print Assumptions rap_geom_k_select.
Print Assumptions rap_geom_rate_dec.
