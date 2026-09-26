(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   mixa_qbern（原 L769，2 句玩具证）                                    *)
(* ============================================================ *)
(* ============================================================ *)
(* 【 恒等守恒修订注记】 包AW十四 （恒等头注修订第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* （包AL）全量恒等核查已证结论、（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此修订。 *)
(* 修订口径：真替换 0 参数位＋恒等守恒 1 参数位；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；记录册 *)
(* 承载见  附录／ 修正块／ 评估册／／／／／ 记录册。 *)
(* 附记： 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（ 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqMixLogA.v —— 赛马 A ：mix_k_select 的对数级升级件          *)
(* （路径一：有理化归约 + Q 层可判定二分；）                *)
(* ============================================================ *)
(* 【本稿状态：四关全部通过交付（tathP 三段承担补入完成， ）】  *)
(*   绿核（原 1-446 行）未回退；Part 5 续作段全部通过：qbern 全族/窗口件/      *)
(*   sel_accounts/k0+b0 双桥/五主件族（pow_budget_log±cert±min/           *)
(*   k_select_log±le/min_real_below）。四关：G1 双轨 0、G2 full+vos 双    *)
(*   EXIT=0+PA 25×Closed、G3 Obj.magic=0、G4 coqchk 通过。证据与对照表=   *)
(*   attn/_tathP_交付报告-.md。对存档稿 5 处陈述修正见报告 §3。   *)
(* 【原绿核交付态】Q 二分核 + 量级定理 + 可判定锚 +   *)
(*   单调桥 + Real 桥全套绿；Q-Bernoulli 窗口件 mixa_qbern 撞 Q-ring 墙  *)
(*   （Q 只注册 Add Field 未注册 Add Ring），主件族 mixa_pow_budget_log  *)
(*   等未闭合——fail-loud 显式遗留，见文末登记与 attn/_tathA_交付报告；   *)
(*   完整起草稿（961 行含主件族）存 attn/_tathA_bak/。配方在案。     *)
(* 使命：把 C10 mix_k_select 的返回 k 从线性量级压到对数量级。          *)
(*   设计依据 A 报告三修正案：①窗口 Q 层自算（mixa_win，地板+2 形）； *)
(*   ②幂单调 Q 层直证（复用 igr_qpow）；③归约链原料取 real_lt 定义面    *)
(*   sigT 见证（S02:456-458）。                                        *)
(*                                                                    *)
(* 本件承载（前缀 mixa_，先 grep 零撞名）：                             *)
(*   ① Q 核引擎：mixa_qpow_add_le/mixa_qpow_decr（igr_qpow 指数单调）；  *)
(*      mixa_test（Qlt_bool 严格锚 κ₀^m·v<b₀）；mixa_test_mono；      *)
(*      mixa_qbern（Q-Bernoulli：(1−w)^m·(1+m·w)≤1）；mixa_win_gt       *)
(*      （窗口 K:=2+⌊v/(w₀b₀)⌋ ⟹ v<K·w₀b₀，零 ceil 面）；              *)
(*      mixa_test_at_win（窗口处锚必真）。                            *)
(*   ② 二分核：mixa_bsearch（fuel+区间不变式）；mixa_bsearch_correct    *)
(*      （通过+最小两账，fuel 界 S(hi−lo)≤2^f）；mixa_fuel_log（量级：   *)
(*      S K ≤ 2^(⌊log₂(S K)⌋+1)，fuel 取 ⌊log₂K⌋+1 即足，每 fuel 结构上  *)
(*      至多一次比较）；mixa_k_log_of（Defined 选择器）；                *)
(*      mixa_sel_accounts（三账封装）。                                 *)
(*   ③ 有理化归约链：mixa_k0_bridge（real_lt kappa real_one 的 sigT      *)
(*      见证 ⟹ κ₀∈Q∩(0,1) 且 κ<κ₀；eps≥2 取 1/2，eps<2 取 1−eps/2）；   *)
(*      mixa_b0_bridge（real_lt zero budget ⟹ b₀:=eps/2 严格下内点）；   *)
(*      mixa_const_lt_inv（real_const 严格序的 Q 反射）；mixa_rpow_le/  *)
(*      mixa_prod_le（回传链换底幂单调×乘积单调）；mixa_const_mult/     *)
(*      mixa_rpow_const（tv_rpow(real_const q)==real_const(igr_qpow q)）。*)
(*   ④ 主件（全 Defined）：mixa_pow_budget_log_cert（证书形核心）；      *)
(*      mixa_pow_budget_log（与 C10 mix_pow_budget 同前提面，real_arch   *)
(*      兜底 TV₀′）；mixa_k_select_log（非负放宽+显式有理上界证书前提；  *)
(*      TV₀==0 支 k:=0）；mixa_k_select_log_le。                        *)
(*   ⑤ 伴生强声明（本赛车独有）：mixa_pow_budget_log_min（返回 k 为      *)
(*      可判定 Q 锚的精确最小通过站——k 通过 ∧ k 以下全不通过；线性     *)
(*      real_arch 代无此声明）；mixa_min_real_below（Real 回传：j<k ⟹    *)
(*      real_const b₀ ≤ κ₀^j·v——证书零松弛时即 Real 真最小步下向界）。   *)
(*                                                                    *)
(* 公理面自审：本件零新增公理；前提全为 Set 层显式证书（real_lt 的       *)
(*   sigT(eps:Q×QltT 0 eps×N) 编码 / real_le 的 Or 编码 / sigT 证书）；  *)
(*   文末 Print Assumptions 预期全 Closed。主件 sigT 载荷全 Set；伴生    *)
(*   三账的 bool 等式与 Prop 合取照抄 igr_k_select_min 分工（Qed 依存    *)
(*   件，不入提取签名）。                                               *)
(* 红线自审：纯构造性（判定全压 Q 层 Qlt_bool/Qle_bool；Real 层只进不出  *)
(*   的严格链依存）；Defined 选择器体内零 Prop 消去（纯布尔 match）；    *)
(*   诚实边界：①量级=结构上界（fuel=⌊log₂K⌋+1、每 fuel 至多一次比较），  *)
(*   未声明比较次数下界；②窗口取 2+⌊x⌋ 比 A 处方 1+⌈x⌉ 松常数 1 档，   *)
(*   换取零上取整除法面；③κ₀/b₀/TV₀′ 三层证书松弛不受控，k 与经典       *)
(*   ⌈ln(budget/TV₀)/ln κ⌉ 的比值不声明（全树未检索到先例可比口径）。    *)
(* 编译配方（9.1 直调轨）：_tathA_run.cmd（COQLIB/ROCQLIB 必设，WALL-2 坑） *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoid.
From Stdlib Require Import Extraction.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import KLWallClosed.

Local Open Scope Q_scope.

(* Q 只注册了 Add Field 未注册 Add Ring——Qeq 面的 ring 须先展开到 Z 面
   （Qeq/Qnum/Qmult/Qplus/Qminus/Qopp 全 unfold + simpl 归约投影，
   落到 Z 循环依赖清单后再 ring；承 C10 mix_const_succ 的 unfold-先行的坑卡口径） *)
Ltac mixa_ring :=
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp in *;
  simpl in *;
  ring.

(* ============================================================ *)
(* Part 0：小件（nat/Q 反射与常元桥）                                    *)
(* ============================================================ *)

Lemma mixa_natle_refl : forall n : nat, NatLe n n.
Proof. intro n. unfold NatLe. rewrite (Nat.leb_refl n). apply id_refl. Qed.

Lemma mixa_zero_const : real_eq real_zero (real_const 0%Q).
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_zero real_const]. ring.

Qed.
Lemma mixa_one_const : real_eq real_one (real_const (1#1)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_one real_const]. ring.

Qed.
Lemma mixa_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - exact (real_mult_comm real_one x).
  - exact (real_mult_one x).

Qed.
(* 基座 Qle_bool（Qcompare 反映形）双向反射 *)
Lemma mixa_qle_bool_true : forall x y : Q, Qle_bool x y = true -> Qle x y.
Proof.
  intros x y H. apply QleT'_to_Qle. unfold QleT'.
  rewrite H. apply id_refl.

Qed.
Lemma mixa_qle_bool_false : forall x y : Q, Qle_bool x y = false -> Qlt y x.
Proof.
  intros x y H. unfold Qle_bool in H.
  destruct (Qcompare x y) eqn:E; simpl in H; try discriminate H.
  apply Qgt_alt. exact E.

Qed.
Lemma mixa_zmul_pos : forall a b : Z, (0 < a)%Z -> (0 < b)%Z -> (0 < a * b)%Z.
Proof.
  intros a b Ha Hb.
  destruct a as [p| |p]; destruct b as [q| |q]; cbn; lia.

Qed.
Lemma mixa_qden_pos : forall x : Q, (0 < QDen x)%Z.
Proof. intro x. destruct x as [n d]. cbn [Qden]. exact (Pos2Z.is_pos d). Qed.

Lemma mixa_qmult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (Qmult x y).
Proof.
  intros [a b] [c d] Hx Hy.
  unfold Qlt in Hx, Hy. cbn [Qnum Qden] in Hx, Hy. simpl in Hx, Hy.
  unfold Qlt, Qmult. cbn [Qnum Qden Qmult].
  destruct a; destruct c; cbn; lia.

Qed.
Lemma mixa_qinv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (Qinv x).
Proof.
  intros [a b] Hx.
  unfold Qlt in Hx. cbn [Qnum Qden] in Hx. simpl in Hx.
  unfold Qinv, Qlt. cbn [Qnum Qden].
  destruct a; cbn [Qnum Qden Qinv]; simpl;
    try (apply Pos2Z.is_pos); try lia.

Qed.
(* real_const 严格序的 Q 反射：real_lt real_zero (real_const a) ⟹ 0 < a
   （常值序列直读证书，零 real_eq 依存——real_eq 系 eps-逼近形非逐点形） *)
Lemma mixa_const_lt_inv0 : forall (a : Q) (x : Real),
  real_lt real_zero (real_const a) -> Qlt 0 a.
Proof.
  intros a x H.
  destruct H as [eps [Hpos [N HN]]].
  specialize (HN N (mixa_natle_refl N)).
  cbn [projT1 real_zero real_const] in HN.
  apply QltT_to_Qlt in Hpos. apply QltT_to_Qlt in HN.
  destruct eps as [e1 e2]. destruct a as [a1 a2].
  unfold Qlt, Qminus in *.
  cbn [Qnum Qden] in *. simpl in *. lia.

Qed.
(* ============================================================ *)
(* Part 1：Q 核引擎（igr_qpow 复用；零 Real 依赖面）                     *)
(* ============================================================ *)

Lemma mixa_qnonneg : forall (q : Q) (m : nat),
  Qle 0 q -> Qle 0 (igr_qpow q m).
Proof.
  intros q m Hq. induction m as [| m IH].
  - unfold Qle. cbn [Qnum Qden igr_qpow]. simpl. lia.
  - cbn [igr_qpow]. apply Qmult_le_0_compat; [exact Hq | exact IH].

Qed.
Lemma mixa_qmult_le_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (Qmult z x) (Qmult z y).
Proof.
  intros x y z H H0.
  apply (Qle_trans _ (Qmult x z)).
  - exact (qeq_le _ _ (Qmult_comm z x)).
  - apply (Qle_trans _ (Qmult y z)).
    + exact (Qmult_le_compat_r x y z H H0).
    + exact (qeq_le _ _ (Qmult_comm y z)).

Qed.
Lemma mixa_qpow_decr : forall (q : Q), Qle 0 q -> Qle q (1#1) ->
  forall m m' : nat, Nat.le m m' -> Qle (igr_qpow q m') (igr_qpow q m).
Proof.
  intros q H0 H1 m m' Hle. induction Hle as [| m' Hle IH].
  - apply Qle_refl.
  - cbn [igr_qpow].
    apply (Qle_trans _ (Qmult q (igr_qpow q m))).
    + exact (mixa_qmult_le_l (igr_qpow q m') (igr_qpow q m) q IH H0).
    + apply (Qle_trans _ (Qmult (1#1) (igr_qpow q m))).
      * exact (Qmult_le_compat_r q (1#1) (igr_qpow q m) H1
                 (mixa_qnonneg q m H0)).
      * exact (qeq_le _ _ (Qmult_1_l (igr_qpow q m))).

Qed.
(* Q 层严格锚：κ₀^m·v < b₀（精确可判定） *)
Definition mixa_test (k0 v b0 : Q) (m : nat) : bool :=
  Qlt_bool (Qmult (igr_qpow k0 m) v) b0.

(* bool 账 → Qlt 桥（基座 Id 与 stdlib eq 分属两归纳族，须显式过桥） *)
Lemma mixa_test_qlt : forall (k0 v b0 : Q) (m : nat),
  mixa_test k0 v b0 m = true -> Qlt (Qmult (igr_qpow k0 m) v) b0.
Proof.
  intros k0 v b0 m H. unfold mixa_test in H.
  apply QltT_to_Qlt. unfold QltT. rewrite H. apply id_refl.

Qed.
(* Qlt → bool 账（反向桥；照 S02 Qlt_to_QltT 的 Qcompare 三分结构） *)
Lemma mixa_qlt_test : forall (k0 v b0 : Q) (m : nat),
  Qlt (Qmult (igr_qpow k0 m) v) b0 -> mixa_test k0 v b0 m = true.
Proof.
  intros k0 v b0 m H. unfold mixa_test, Qlt_bool.
  destruct (Qcompare (Qmult (igr_qpow k0 m) v) b0) eqn:E.
  - exfalso. apply (Qlt_irrefl b0).
    assert (Heq : (Qmult (igr_qpow k0 m) v) == b0) by (apply Qeq_alt; exact E).
    rewrite Heq in H. exact H.
  - reflexivity.
  - exfalso. apply (Qlt_irrefl (Qmult (igr_qpow k0 m) v)).
    assert (Hyx : b0 < (Qmult (igr_qpow k0 m) v)) by (apply Qgt_alt; exact E).
    eapply Qlt_trans. exact H. exact Hyx.

Qed.
Lemma mixa_test_mono : forall (k0 v b0 : Q) (m m' : nat),
  Qlt 0 k0 -> Qle k0 (1#1) -> Qle 0 v -> Nat.le m m' ->
  mixa_test k0 v b0 m = true -> mixa_test k0 v b0 m' = true.
Proof.
  intros k0 v b0 m m' Hk0 Hk1 Hv Hle Htm.
  assert (Htl : Qlt (Qmult (igr_qpow k0 m) v) b0)
    by exact (mixa_test_qlt k0 v b0 m Htm).
  assert (Hdec : Qle (igr_qpow k0 m') (igr_qpow k0 m)).
  { apply (mixa_qpow_decr k0).
    - exact (Qlt_le_weak 0 k0 Hk0).
    - exact Hk1.
    - exact Hle. }
  assert (Hlt : Qlt (Qmult (igr_qpow k0 m') v) b0).
  { apply (Qle_lt_trans _ (Qmult (igr_qpow k0 m) v) b0).
    - exact (Qmult_le_compat_r (igr_qpow k0 m') (igr_qpow k0 m) v Hdec Hv).
    - exact Htl. }
  exact (mixa_qlt_test k0 v b0 m' Hlt).


Qed.
(* ============================================================ *)
(* Part 2：二分核（fuel+区间不变式）                                     *)
(* ============================================================ *)

Fixpoint mixa_bsearch (test : nat -> bool) (f lo hi : nat) : nat :=
  match f with
  | Datatypes.O => lo
  | Datatypes.S f' =>
      if Nat.eqb lo hi then lo
      else if test (Nat.div2 (Nat.add lo hi))
        then mixa_bsearch test f' lo (Nat.div2 (Nat.add lo hi))
        else mixa_bsearch test f' (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi
  end.

Lemma mixa_bsearch_correct : forall (test : nat -> bool) (f lo0 : nat),
  (forall a b : nat, Nat.le a b -> test a = true -> test b = true) ->
  forall lo hi : nat,
  (forall j : nat, Nat.le lo0 j -> Nat.lt j lo -> test j = false) ->
  Nat.le lo0 lo -> Nat.le lo hi -> test hi = true ->
  Nat.le (Datatypes.S (Nat.sub hi lo)) (Nat.pow 2 f) ->
  test (mixa_bsearch test f lo hi) = true /\
  (forall j : nat, Nat.le lo0 j -> Nat.lt j (mixa_bsearch test f lo hi) ->
     test j = false).
Proof.
  intros test f. induction f as [| f IH]; intros lo0 Hmono lo hi Hbelow
    Hlo0 Hlo Hhi Hfuel.
  - simpl in Hfuel. assert (Elo : lo = hi) by lia.
    rewrite Elo in Hbelow. rewrite Elo. split.
    + exact Hhi.
    + exact Hbelow.
  - cbn [mixa_bsearch]. destruct (Nat.eqb lo hi) eqn:Eeq.
    + apply Nat.eqb_eq in Eeq. rewrite Eeq in Hbelow. rewrite Eeq. split.
      * exact Hhi.
      * exact Hbelow.
    + apply Nat.eqb_neq in Eeq.
      assert (Hlt : Nat.lt lo hi) by lia.
      assert (Hd2 : Nat.div2 (Nat.add lo hi) = Nat.div (Nat.add lo hi) 2)
        by apply Nat.div2_div.
      rewrite Hd2.
      pose proof (Nat.mod_upper_bound (Nat.add lo hi) 2 ltac:(lia)) as Hmod.
      pose proof (Nat.div_mod (Nat.add lo hi) 2 ltac:(lia)) as Hdm.
      assert (Hmlo : Nat.le lo (Nat.div (Nat.add lo hi) 2)) by lia.
      assert (Hmhi : Nat.lt (Nat.div (Nat.add lo hi) 2) hi) by lia.
      rewrite Nat.pow_succ_r' in Hfuel.
      destruct (test (Nat.div (Nat.add lo hi) 2)) eqn:Ht.
      * (* 通过支：hi ← mid *)
        assert (Hf1 : Nat.le (Datatypes.S (Nat.sub (Nat.div (Nat.add lo hi) 2) lo))
                        (Nat.pow 2 f)) by lia.
        destruct (IH lo0 Hmono lo (Nat.div (Nat.add lo hi) 2) Hbelow Hlo0 Hmlo Ht Hf1)
          as [Ht2 Hmin].
        split; [exact Ht2 | exact Hmin].
      * (* 失败支：lo ← mid+1；补 [lo₀,mid] 段无解账 *)
        assert (Hbl : forall j : nat, Nat.le lo0 j ->
                   Nat.lt j (Datatypes.S (Nat.div (Nat.add lo hi) 2)) ->
                   test j = false).
        { intros j Hj0 Hj.
          destruct (Nat.lt_ge_cases j (Nat.div (Nat.add lo hi) 2))
            as [Hltj | Hgej].
          -- destruct (test j) eqn:Htj; [| reflexivity].
             assert (Htm2 : test (Nat.div (Nat.add lo hi) 2) = true)
               by (apply (Hmono j (Nat.div (Nat.add lo hi) 2)); [lia | exact Htj]).
             rewrite Ht in Htm2. discriminate Htm2.
          -- assert (Heq : j = Nat.div (Nat.add lo hi) 2) by lia.
             rewrite Heq. exact Ht. }
        assert (Hf2 : Nat.le (Datatypes.S (Nat.sub hi
                          (Datatypes.S (Nat.div (Nat.add lo hi) 2))))
                        (Nat.pow 2 f)) by lia.
        destruct (IH lo0 Hmono (Datatypes.S (Nat.div (Nat.add lo hi) 2)) hi
                    Hbl ltac:(lia) ltac:(lia) Hhi Hf2) as [Ht2 Hmin].
        split; [exact Ht2 | exact Hmin].

Qed.
(* 量级定理：fuel = ⌊log₂K⌋+1 即足（每 fuel 结构上至多一次比较） *)
Theorem mixa_fuel_log : forall K : nat, Nat.lt 0 K ->
  Nat.le (Datatypes.S K) (Nat.pow 2 (Datatypes.S (Nat.log2 (Datatypes.S K)))).
Proof.
  intros K HK.
  destruct (Nat.log2_spec (Datatypes.S K) ltac:(lia)) as [_ Hlt].
  apply Nat.lt_le_incl. exact Hlt.
Qed.
(* Defined 选择器 mixa_k_log_of：遗留③（依赖 mixa_win 窗口件，见文末登记） *)

(* ============================================================ *)
(* Part 3：Real 桥（有理化归约链）                                       *)
(* ============================================================ *)

Lemma mixa_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b))
          (real_const (Qmult a b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const real_mult] in *. ring.

Qed.
Lemma mixa_rpow_const : forall (q : Q) (t : nat),
  real_eq (tv_rpow (real_const q) t) (real_const (igr_qpow q t)).
Proof.
  intros q t. induction t as [| t IH].
  - exact mixa_one_const.
  - cbn [tv_rpow igr_qpow].
    apply (real_eq_trans _
             (real_mult (real_const q) (real_const (igr_qpow q t)))).
    + exact (RealSetoid.real_eq_mult_compat (real_const q)
               (tv_rpow (real_const q) t)
               (real_const q) (real_const (igr_qpow q t))
               (real_eq_refl (real_const q)) IH).
    + exact (mixa_const_mult q (igr_qpow q t)).

Qed.
Lemma mixa_rpow_nonneg : forall (x : Real) (k : nat),
  real_le real_zero x -> real_le real_zero (tv_rpow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - apply (RealSetoid.real_lt_le_iff_req real_zero real_one).
    left. exact real_lt_zero_one.
  - cbn [tv_rpow]. exact (klc_mult_nonneg x (tv_rpow x k) Hx IH).

Qed.
(* 换底幂单调：κ ≤ κ₀ ⟹ κ^k ≤ κ₀^k（κ 严格正、κ₀ 非负） *)
Lemma mixa_rpow_le : forall (kappa k0c : Real) (k : nat),
  real_lt real_zero kappa -> real_le kappa k0c -> real_le real_zero k0c ->
  real_le (tv_rpow kappa k) (tv_rpow k0c k).
Proof.
  intros kappa k0c k Hk1 Hle Hk0. induction k as [| k IH].
  - exact (inr (real_eq_refl real_one)).
  - assert (Hk1le : real_le real_zero kappa)
      by (apply (RealSetoid.real_lt_le_iff_req real_zero kappa);
          left; exact Hk1).
    cbn [tv_rpow].
    apply (real_le_trans _ (real_mult k0c (tv_rpow kappa k))).
    + exact (klc_le_mult_r_weak kappa k0c (tv_rpow kappa k) Hle (mixa_rpow_nonneg kappa k Hk1le)).
    + apply (real_le_trans _ (real_mult (tv_rpow kappa k) k0c)).
      * apply (RealSetoid.real_eq_le).
        exact (real_mult_comm k0c (tv_rpow kappa k)).
      * apply (real_le_trans _ (real_mult (tv_rpow k0c k) k0c)).
        -- exact (klc_le_mult_r_weak (tv_rpow kappa k) (tv_rpow k0c k) k0c
                    IH Hk0).
        -- apply (RealSetoid.real_eq_le).
           exact (real_mult_comm (tv_rpow k0c k) k0c).

Qed.
(* 乘积单调合并肢：A ≤ B ∧ x ≤ y ∧ 0 ≤ x ∧ 0 ≤ B ⟹ A·x ≤ B·y *)
Lemma mixa_prod_le : forall (A B x y : Real),
  real_le A B -> real_le x y -> real_le real_zero x ->
  real_le real_zero B ->
  real_le (real_mult A x) (real_mult B y).
Proof.
  intros A B x y HAB Hxy Hx HB.
  apply (real_le_trans _ (real_mult B x)).
  - exact (klc_le_mult_r_weak A B x HAB Hx).
  - apply (real_le_trans _ (real_mult x B)).
    + apply (RealSetoid.real_eq_le). exact (real_mult_comm B x).
    + apply (real_le_trans _ (real_mult y B)).
      * exact (klc_le_mult_r_weak x y B Hxy HB).
      * apply (RealSetoid.real_eq_le). exact (real_mult_comm y B).

Qed.
(* κ₀ 提取：eps ≥ 2 ⟹ κ₀ := 1/2（κ_n < 1−eps ≤ −1 < 1/2）；
   eps < 2 ⟹ κ₀ := 1−eps/2（gap := eps/2） *)
Definition mixa_k0 (eps : Q) : Q :=
  if Qle_bool (2#1) eps then (1#2) else (1 - eps * (1#2))%Q.

Definition mixa_b0 (eps : Q) : Q := eps * (1#2).

(* mixa_k0_bridge / mixa_b0_bridge 有理化提取桥：遗留（文末登记）,完整实现体 *)
(* 存 attn/_tathA_bak/UpReqMixLogA_v1_full_draft.v:415-479 *)


(* ============================================================ *)
(* 遗留登记（fail-loud，显式申报）                                       *)
(* ============================================================ *)
(* 位内未达绿，完整起草稿存 attn/_tathA_bak/               *)
(* UpReqMixLogA_v1_full_draft.v（961 行），遗留四处：                   *)
(*   ① mixa_qbern（Q-Bernoulli）：le_S 分支的代数恒等式                 *)
(*      (1−w)·(B+w) == B − (c·w)·w（B==1+m'·w, c==m'+1）在 Qeq 面的     *)
(*      ring 受阻——本环境 Q 只注册 Add Field(Qfield.v:76) 未注册        *)
(*      Add Ring，Q-eq 上 ring/field 均「not a valid (field) equation」；*)
(*      lia/nia 不展开 Q-mult 的和积结构（检验实证 _tathA_probe.v）。    *)
(*      升级路径：照 C10 mix_ring_sc 的 Z 面配对展开引理口径，或以       *)
(*      Qmult_minus/plus_distr 引理链逐项重写（链已起草于存档稿）。      *)
(*   ② mixa_win_gt / mixa_test_at_win / mixa_win：依赖①的窗口件。       *)
(*   ③ mixa_sel_accounts / mixa_k_log_of 主实例化：依赖②。                *)
(*   ④ mixa_pow_budget_log(_cert/_min) / mixa_k_select_log(_le) /        *)
(*      mixa_min_real_below 主件族：依赖③。                             *)
(* 绿核交付面：Q 二分核（mixa_bsearch_correct+mixa_fuel_log 量级定理）   *)
(* 完整实现体续上注 *)
(*   + 可判定锚 mixa_test/单调/双向桥 + 有理化归约链桥（k0/b0 提取、   *)
(*   const_lt_inv0、rpow/prod 单调、const/rpow 精确桥）——按存档稿   *)
(*   ④→③→②→① 顺序补入即可闭合。                                        *)

Extraction "_tathA_G3.ml" mixa_bsearch mixa_test mixa_k0 mixa_b0
  mixa_qpow_decr mixa_test_mono mixa_qlt_test.

Print Assumptions mixa_bsearch_correct.
Print Assumptions mixa_fuel_log.
Print Assumptions mixa_test_mono.
Print Assumptions mixa_test_qlt.
Print Assumptions mixa_qlt_test.
Print Assumptions mixa_const_lt_inv0.
Print Assumptions mixa_rpow_const.
Print Assumptions mixa_rpow_le.
Print Assumptions mixa_prod_le.
Print Assumptions mixa_qpow_decr.
Print Assumptions mixa_qnonneg.
Print Assumptions mixa_qmult_pos.
(* ============================================================ *)
(* Part 5：PIT 续作段（tathP 承担 tathA 遗留补入，）          *)
(*   配方=A 报告§三（①qbern→②win/test_at_win→③k_log_of/sel_accounts   *)
(*   →④k0/b0_bridge+主件族）。Q-ring 墙解法=Z 面展开（destruct 配对 +   *)
(*   cbn 白名单 + Z.pos 积分裂 + ring），检验 _tathP_sbx 预验证绿。      *)
(*   igr_qpow 语境的 Qeq 恒等式不走 Z 面（投影停滞=假原子），改 stdlib  *)
(*   Qeq 引理链（Qmult_comp/assoc）；Qle 代数尾目标 cbn 后 nia。         *)
(* ============================================================ *)

Ltac mixa_qeq_zface :=
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp;
  cbn [Qnum Qden Qplus Qminus Qopp Qmult Pos.mul];
  repeat match goal with
         | |- context [Z.pos (?x * ?y)] =>
             replace (Z.pos (x * y))%Z with ((Z.pos x) * (Z.pos y))%Z
               by reflexivity
         end;
  ring.

(* 同族泛化：Pos2Z.inj_mul/inj_add 递归归一（任意 Pos.mul/Pos.add 嵌套形，
   含 cbn 的 xI 分支混合态——Pos2Z.inj_mul : Z.pos(p*q) = Z.pos p * Z.pos q） *)
Ltac mixa_qeq_zfold :=
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp;
  cbn [Qnum Qden Qplus Qminus Qopp Qmult];
  repeat match goal with
         | |- context [Z.pos (Pos.mul ?x ?y)] =>
             replace (Z.pos (Pos.mul x y))%Z
               with ((Z.pos x) * (Z.pos y))%Z by apply Pos2Z.inj_mul
         | |- context [Z.pos (Pos.add ?x ?y)] =>
             replace (Z.pos (Pos.add x y))%Z
               with ((Z.pos x) + (Z.pos y))%Z by apply Pos2Z.inj_add
         end;
  ring.

(* 双重否定消去（test_at_win 换基桥承重） *)
Lemma mixa_qsub_sub : forall x : Q, 1 - (1 - x) == x.
Proof. intros [a d]. mixa_qeq_zface. Qed.

(* 半量桥（配方 B：泛型引理化，destruct 内化；Pos2Z.inj 递归归一） *)
Lemma mixa_qhalf_bridge : forall k : Q, Qeq ((1#2) - k) ((-(1#2)) + (1 - k)).
Proof.
  intros [c d].
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp.
  cbn [Qnum Qden Qplus Qminus Qopp Qmult Pos.mul].
  repeat match goal with
         | |- context [Z.pos (Pos.mul ?x ?y)] =>
             replace (Z.pos (Pos.mul x y))%Z
               with ((Z.pos x) * (Z.pos y))%Z by apply Pos2Z.inj_mul
         | |- context [Z.pos (Pos.add ?x ?y)] =>
             replace (Z.pos (Pos.add x y))%Z
               with ((Z.pos x) + (Z.pos y))%Z by apply Pos2Z.inj_add
         end.
  ring.
Qed.

(* 减法重排桥：支B 同型泛化（检验 p_sub_swap 绿） *)
Lemma mixa_qsub_swap : forall x e k : Q, Qeq ((x - e) - k) ((-e) + (x - k)).
Proof.
  intros [xa xd] [ea ed] [ka kd].
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp.
  cbn [Qnum Qden Qplus Qminus Qopp Qmult Pos.mul].
  repeat match goal with
         | |- context [Z.pos (Pos.mul ?x ?y)] =>
             replace (Z.pos (Pos.mul x y))%Z
               with ((Z.pos x) * (Z.pos y))%Z by apply Pos2Z.inj_mul
         | |- context [Z.pos (Pos.add ?x ?y)] =>
             replace (Z.pos (Pos.add x y))%Z
               with ((Z.pos x) + (Z.pos y))%Z by apply Pos2Z.inj_add
         end.
  ring.
Qed.

(* PIT 泛化归一 pz（inj 版：cbn 无 Pos.mul——混合态根源剔除；零 nia） *)
Ltac mixa_pz :=
  unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp;
  cbn [Qnum Qden Qplus Qminus Qopp Qmult];
  repeat match goal with
         | |- context [Z.pos (Pos.mul ?x ?y)] =>
             replace (Z.pos (Pos.mul x y))%Z
               with ((Z.pos x) * (Z.pos y))%Z by apply Pos2Z.inj_mul
         | |- context [Z.pos (Pos.add ?x ?y)] =>
             replace (Z.pos (Pos.add x y))%Z
               with ((Z.pos x) + (Z.pos y))%Z by apply Pos2Z.inj_add
         end;
  ring.

Lemma mixa_qopp_add : forall x : Q, Qeq ((-x) + x) 0.
Proof. intros [a d]. mixa_pz. Qed.

Lemma mixa_qtwo_half : Qeq (2 * (1#2)) 1.
Proof. mixa_pz. Qed.

Lemma mixa_qsub_add : forall x y : Q, Qeq ((x - y) + y) x.
Proof. intros [xa xd] [ya yd]. mixa_pz. Qed.

Lemma mixa_qdouble : forall x : Q, Qeq x ((-x) + (x + x)).
Proof. intros [a d]. mixa_pz. Qed.

Lemma mixa_qsplit : forall x : Q, Qeq x (x * (1#2) + x * (1#2)).
Proof. intros [a d]. mixa_pz. Qed.

Lemma mixa_qsub_0 : forall x : Q, Qeq (x - 0) x.
Proof. intros [a d]. mixa_pz. Qed.

Lemma mixa_qsub_comm : forall x y : Q, Qeq (x - y) ((-y) + x).
Proof. intros [xa xd] [ya yd]. mixa_pz. Qed.

Lemma mixa_qopp_add_assoc : forall y x : Q, Qeq ((-y) + (x + y)) x.
Proof. intros [ya yd] [xa xd]. mixa_pz. Qed.

Lemma mixa_qminus_unfold : forall z y : Q, Qeq ((-y) + z) (z - y).
Proof. intros [za zd] [ya yd]. mixa_pz. Qed.

Lemma mixa_qlt_sub_r : forall x y z : Q, Qlt (x + y) z -> Qlt x (z - y).
Proof.
  intros x y z H.
  assert (Hs : Qlt ((-y) + (x + y)) ((-y) + z))
    by exact (proj2 (Qplus_lt_r (x + y) z (-y)) H).
  assert (E1 : Qeq ((-y) + (x + y)) x) by exact (mixa_qopp_add_assoc y x).
  assert (E2 : Qeq ((-y) + z) (z - y)) by exact (mixa_qminus_unfold z y).
  rewrite E1 in Hs. rewrite E2 in Hs. exact Hs.
Qed.

Lemma mixa_qle_add_r : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros [xa xd] [ya yd] H.
  unfold Qle in H. cbn [Qnum Qden] in H. simpl in H.
  unfold Qle. cbn [Qnum Qden Qplus Qminus Qopp Qmult].
  repeat match goal with
         | |- context [Z.pos (Pos.mul ?x ?y)] =>
             replace (Z.pos (Pos.mul x y))%Z
               with ((Z.pos x) * (Z.pos y))%Z by apply Pos2Z.inj_mul
         end.
  lia.
Qed.

Lemma mixa_qsub_lt : forall x y : Q, Qlt x y -> Qlt 0 (y - x).
Proof.
  intros x y H.
  assert (Hs : Qlt ((-x) + x) ((-x) + y))
    by exact (proj2 (Qplus_lt_r x y (-x)) H).
  assert (E : Qeq ((-x) + x) 0) by exact (mixa_qopp_add x).
  rewrite (Qplus_comm y (-x)).
  rewrite <- E. exact Hs.
Qed.

Lemma mixa_qomh_pos : forall e : Q, Qlt e (2#1) -> Qlt 0 (1 - e * (1#2)).
Proof.
  intros e He.
  assert (Hm : Qlt (e * (1#2)) (2 * (1#2)))
    by exact (Qmult_lt_compat_r e 2 (1#2)
                ltac:(unfold Qlt; cbn [Qnum Qden]; simpl; lia)
                He).
  rewrite mixa_qtwo_half in Hm.
  exact (mixa_qsub_lt (e * (1#2)) 1 Hm).
Qed.

Lemma mixa_qomh_lt1 : forall e : Q, Qlt 0 e -> Qlt (1 - e * (1#2)) (1#1).
Proof.
  intros e He.
  assert (Hh : Qlt 0 (e * (1#2))) by (apply mixa_qmult_pos;
    [ exact He | unfold Qlt; cbn [Qnum Qden]; simpl; lia ]).
  pose proof (proj2 (Qplus_lt_r 0 (e * (1#2)) (1 - e * (1#2))) Hh) as Hs.
  rewrite Qplus_0_r in Hs.
  assert (E : Qeq ((1 - e * (1#2)) + e * (1#2)) (1#1)) by mixa_pz.
  rewrite E in Hs. exact Hs.
Qed.

(* igr_qpow 的 Qeq 同余 *)
Lemma mixa_igr_qpow_wd : forall (x y : Q), x == y ->
  forall m : nat, igr_qpow x m == igr_qpow y m.
Proof.
  intros x y Hxy m. induction m as [| m IH].
  - apply Qeq_refl.
  - cbn [igr_qpow]. apply Qmult_comp; assumption.
Qed.

(* 乘法左因子交换（igr_qpow 语境 Qeq 恒等式的 stdlib 引理链承重件） *)
Lemma mixa_qmult_swap : forall x y z : Q,
  Qmult x (Qmult y z) == Qmult y (Qmult x z).
Proof.
  intros x y z.
  rewrite (Qmult_assoc x y z), (Qmult_comm x y), <- (Qmult_assoc y x z).
  apply Qeq_refl.
Qed.

(* Qlt 0 x ⟹ 0 < Qnum x（win_gt 正性桩；Z 面线性可闭） *)
Lemma mixa_qlt0_num : forall x : Q, Qlt 0 x -> (0 < Qnum x)%Z.
Proof.
  intros [a d] H. unfold Qlt in H. cbn [Qnum Qden] in H. simpl in H.
  cbn [Qnum]. lia.
Qed.

(* 0 < x ⟹ x < 1 + x（HvW2 承重；Z 面 nia） *)
Lemma mixa_qx_lt_1px : forall x : Q, Qlt 0 x -> Qlt x (1 + x).
Proof.
  intros x Hx. unfold Qlt. destruct x as [a d].
  cbn [Qnum Qden Qplus Qmult Pos.mul] in *.
  repeat match goal with
         | |- context [Z.pos (?p * ?q)] =>
             replace (Z.pos (p * q))%Z with ((Z.pos p) * (Z.pos q))%Z
               by reflexivity
         end.
  nia.
Qed.


(* 半量辅助：e ≥ 2 ⟹ e·½ ≤ e−½；0 ≤ e ⟹ e·½ ≤ e（桥的 ∀n 肢承重） *)
Lemma mixa_qhalf_le_sub : forall e : Q, Qle (2#1) e ->
  Qle (e * (1#2)) (e - (1#2)).
Proof.
  intros e He. destruct e as [a d].
  assert (H2 : (2 * Z.pos d <= a)%Z).
  { unfold Qle in He. cbn [Qnum Qden] in He. simpl in He. lia. }
  unfold Qle. cbn [Qnum Qden Qminus Qopp Qplus Qmult Pos.mul].
  repeat match goal with
         | |- context [Z.pos (?p * ?q)] =>
             replace (Z.pos (p * q))%Z with ((Z.pos p) * (Z.pos q))%Z
               by reflexivity
         end.
  nia.
Qed.

Lemma mixa_qhalf_le : forall e : Q, Qle 0 e -> Qle (e * (1#2)) e.
Proof.
  intros e He. destruct e as [a d].
  assert (H0 : (0 <= a)%Z).
  { unfold Qle in He. cbn [Qnum Qden] in He. simpl in He. lia. }
  unfold Qle. cbn [Qnum Qden Qminus Qopp Qplus Qmult Pos.mul].
  repeat match goal with
         | |- context [Z.pos (?p * ?q)] =>
             replace (Z.pos (p * q))%Z with ((Z.pos p) * (Z.pos q))%Z
               by reflexivity
         end.
  lia.
Qed.

(* ============================================================ *)
(* ① Q-Bernoulli：(1−w)^m·(1+m·w) ≤ 1（Z 面展开破 Q-ring 墙）           *)
(* ============================================================ *)
Lemma mixa_qbern_pair : forall (a : Z) (d : positive),
  Qlt 0 (Qmake a d) -> Qle 0 (1 - Qmake a d) ->
  forall m : nat,
  Qle (Qmult (igr_qpow (1 - Qmake a d) m)
             (Qplus (1#1) (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d))))
       (1#1).
Proof.
  intros a d Hw Hw1 m. induction m as [| m IH].
  - apply qeq_le. cbn [Z.of_nat igr_qpow]. mixa_qeq_zface.
  - replace (Z.of_nat (Datatypes.S m)) with ((Z.of_nat m) + 1)%Z by lia.
    (* X₁(折形式) ≡ X₂(和形式) 桥：之后全链固定在 X₂ 形 *)
    assert (EX : Qeq (Qplus (1#1) (Qmult (Qmake (Z.of_nat m + 1) 1) (Qmake a d)))
                     (Qplus (Qplus (1#1)
                                (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))
                            (Qmake a d)))
      by mixa_qeq_zface.
    rewrite EX.
    assert (Hc0 : Qle 0 (Qmake (Z.of_nat m + 1) 1)).
    { unfold Qle. cbn [Qnum Qden]. simpl. lia. }
    assert (Hw0 : Qle 0 (Qmake a d)) by exact (Qlt_le_weak 0 _ Hw).
    assert (HSC : Qle (Qmult (1 - Qmake a d)
                        (Qplus (Qplus (1#1)
                                   (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))
                              (Qmake a d)))
                       (Qplus (1#1) (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))).
    { assert (E : Qeq (Qmult (1 - Qmake a d)
                        (Qplus (Qplus (1#1)
                                   (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))
                              (Qmake a d)))
                       (Qminus (Qplus (1#1)
                                  (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))
                               (Qmult (Qmult (Qmake (Z.of_nat m + 1) 1)
                                        (Qmake a d))
                                      (Qmake a d))))
        by mixa_qeq_zface.
      rewrite E. unfold Qle.
      cbn [Qnum Qden Qplus Qminus Qopp Qmult Pos.mul].
      repeat match goal with
             | |- context [Z.pos (?x * ?y)] =>
                 replace (Z.pos (x * y))%Z
                   with ((Z.pos x) * (Z.pos y))%Z by reflexivity
             end.
      nia. }
    assert (HX0 : Qle 0 (igr_qpow (1 - Qmake a d) m))
      by exact (mixa_qnonneg (1 - Qmake a d) m Hw1).
    assert (E2 : Qeq (Qmult (Qmult (1 - Qmake a d)
                                (igr_qpow (1 - Qmake a d) m))
                           (Qplus (Qplus (1#1)
                                      (Qmult (Qmake (Z.of_nat m) 1)
                                         (Qmake a d)))
                                 (Qmake a d)))
                       (Qmult (igr_qpow (1 - Qmake a d) m)
                          (Qmult (1 - Qmake a d)
                             (Qplus (Qplus (1#1)
                                        (Qmult (Qmake (Z.of_nat m) 1)
                                           (Qmake a d)))
                                   (Qmake a d))))).
    { transitivity (Qmult (1 - Qmake a d)
                          (Qmult (igr_qpow (1 - Qmake a d) m)
                             (Qplus (Qplus (1#1)
                                        (Qmult (Qmake (Z.of_nat m) 1)
                                           (Qmake a d)))
                                   (Qmake a d)))).
      - apply Qeq_sym. apply Qmult_assoc.
      - apply (mixa_qmult_swap (1 - Qmake a d)
                 (igr_qpow (1 - Qmake a d) m)
                 (Qplus (Qplus (1#1)
                            (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d)))
                       (Qmake a d))). }
    rewrite E2.
    apply (Qle_trans _ (Qmult (igr_qpow (1 - Qmake a d) m)
                          (Qplus (1#1) (Qmult (Qmake (Z.of_nat m) 1) (Qmake a d))))).
    + exact (mixa_qmult_le_l _ _ _ HSC HX0).
    + exact IH.
Qed.

Lemma mixa_qbern : forall (w : Q), Qlt 0 w -> Qle 0 (1 - w) ->
  forall m : nat,
  Qle (Qmult (igr_qpow (1 - w) m)
             (Qplus (1#1) (Qmult (Qmake (Z.of_nat m) 1) w)))
       (1#1).
Proof.
  intros [a d] Hw Hw1 m.
  exact (mixa_qbern_pair a d Hw Hw1 m).
Qed.

(* 换基形：base == 1−w 时幂基直接写 base（test_at_win 免改写穿 Fixpoint） *)
Lemma mixa_qbern_base : forall (w base : Q), base == 1 - w -> Qlt 0 w ->
  Qle 0 base ->
  forall m : nat,
  Qle (Qmult (igr_qpow base m)
             (Qplus (1#1) (Qmult (Qmake (Z.of_nat m) 1) w)))
       (1#1).
Proof.
  intros w base Hbe Hw Hb1 m.
  rewrite (mixa_igr_qpow_wd base (1 - w) Hbe m).
  pose proof Hb1 as Hb1p. rewrite Hbe in Hb1p.
  exact (mixa_qbern w Hw Hb1p m).
Qed.

(* ============================================================ *)
(* ② 窗口件：mixa_win / mixa_win_gt / mixa_test_at_win                  *)
(* ============================================================ *)
Definition mixa_win (v w0 b0 : Q) : nat :=
  Datatypes.S (Datatypes.S
    (Z.to_nat (Z.div (Qnum v * QDen (Qmult w0 b0))
                     (QDen v * Qnum (Qmult w0 b0))))).

Lemma mixa_win_gt : forall v w0 b0 : Q,
  Qlt 0 v -> Qlt 0 (Qmult w0 b0) ->
  Qlt v (Qmult (Qmake (Z.of_nat (mixa_win v w0 b0)) 1) (Qmult w0 b0)).
Proof.
  intros [nv dv] [nw0 dw0] [nb db] Hv HW.
  assert (HnumW : (0 < nw0 * nb)%Z).
  { pose proof (mixa_qlt0_num _ HW) as Hn. cbn [Qnum Qmult Pos.mul] in Hn. lia. }
  assert (Hvpos : (0 < nv)%Z).
  { pose proof (mixa_qlt0_num _ Hv). cbn [Qnum Pos.mul] in H. lia. }
  assert (HdW : (0 < Z.pos (dw0 * db))%Z) by apply Pos2Z.is_pos.
  assert (Hnum : (0 < nv * Z.pos (dw0 * db))%Z)
    by exact (mixa_zmul_pos nv _ Hvpos HdW).
  assert (Hdv : (0 < Z.pos dv)%Z) by apply Pos2Z.is_pos.
  assert (Hden : (0 < Z.pos dv * (nw0 * nb))%Z)
    by exact (mixa_zmul_pos _ _ Hdv HnumW).
  assert (Hq0 : (0 <= Z.div (nv * Z.pos (dw0 * db))
                            (Z.pos dv * (nw0 * nb)))%Z).
  { apply Z_div_pos.
    - lia.
    - lia. }
  pose proof (Z.div_mod (nv * Z.pos (dw0 * db))
                        (Z.pos dv * (nw0 * nb))
                        ltac:(intro Hz; rewrite Hz in Hden; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (nv * Z.pos (dw0 * db))
                              (Z.pos dv * (nw0 * nb)) Hden) as Hrlt.
  assert (HZ2 : Z.of_nat (mixa_win (Qmake nv dv) (Qmake nw0 dw0) (Qmake nb db))
                = (Z.div (nv * Z.pos (dw0 * db))
                         (Z.pos dv * (nw0 * nb)) + 2)%Z).
  { unfold mixa_win. cbn [Qnum Qden Qmult Pos.mul].
    rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
    rewrite (Z2Nat.id (Z.div (nv * Z.pos (dw0 * db))
                             (Z.pos dv * (nw0 * nb))) ltac:(lia)).
    lia. }
  unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. rewrite HZ2. nia.
Qed.

(* 窗口处锚必真（换基 bernoulli 直取，免改写穿 igr_qpow） *)
Lemma mixa_test_at_win : forall k0 v b0 : Q,
  Qlt 0 k0 -> Qlt k0 (1#1) -> Qlt 0 v -> Qlt 0 b0 ->
  mixa_test k0 v b0 (mixa_win v (1 - k0) b0) = true.
Proof.
  intros [a d] [nv dv] [c e] Hk0 Hk1 Hv Hb.
  assert (Hk0le : Qle 0 (Qmake a d)) by exact (Qlt_le_weak 0 (Qmake a d) Hk0).
  assert (Hvle : Qle 0 (Qmake nv dv)) by exact (Qlt_le_weak 0 _ Hv).
  assert (Hw0 : Qlt 0 (1 - (Qmake a d)))
    by exact (proj1 (Qlt_minus_iff (Qmake a d) (1#1)) Hk1).
  assert (Hw1c : Qle 0 (1 - (Qmake a d))) by exact (Qlt_le_weak 0 (1 - (Qmake a d)) Hw0).
  assert (HW : Qlt 0 (Qmult (1 - (Qmake a d)) (Qmake c e))) by (apply mixa_qmult_pos; assumption).
  pose proof (mixa_win_gt (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e) Hv HW) as Hwin0.
  assert (Hwin : Qlt (Qmake nv dv) (Qmult (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                   (1 - (Qmake a d))) (Qmake c e))).
  { apply (Qlt_le_trans _ (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                             (Qmult (1 - (Qmake a d)) (Qmake c e)))).
    - exact Hwin0.
    - exact (qeq_le _ _ (Qmult_assoc (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                          (1 - (Qmake a d)) (Qmake c e))). }
  pose proof (mixa_qbern_base (1 - (Qmake a d)) (Qmake a d)
                (Qeq_sym _ _ (mixa_qsub_sub (Qmake a d))) Hw0 Hk0le
                (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) as Hb0.
  assert (HX0 : Qle 0 (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))))
    by exact (mixa_qnonneg (Qmake a d) _ Hk0le).
  assert (HMpos : Qlt 0 (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                               (1 - (Qmake a d)))).
  { apply mixa_qmult_pos.
    - unfold Qlt. cbn [Qnum Qden]. simpl. lia.
    - exact Hw0. }
  assert (H01 : Qlt 0 (1#1)) by (unfold Qlt; cbn [Qnum Qden]; simpl; lia).
  assert (HB10 : Qlt 0 (Qplus (1#1)
                          (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                             (1 - (Qmake a d))))).
  { pose proof (Qplus_lt_compat 0 (1#1) 0
                  (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                     (1 - (Qmake a d))) H01 HMpos) as HB.
    rewrite Qplus_0_l in HB. exact HB. }
  assert (Hscale : Qle (Qmult (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e)))
                                  (Qplus (1#1)
                                     (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                        (1 - (Qmake a d))))) (Qmake nv dv)) (Qmake nv dv)).
  { apply (Qle_trans _ (Qmult (1#1) (Qmake nv dv))).
    - apply (Qmult_le_compat_r _ _ _ Hb0 Hvle).
    - apply qeq_le. apply Qmult_1_l. }
  assert (HvW2 : Qlt (Qmult (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                (1 - (Qmake a d))) (Qmake c e))
                     (Qmult (Qplus (1#1)
                                 (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                    (1 - (Qmake a d)))) (Qmake c e))).
  { apply (Qmult_lt_compat_r _ _ (Qmake c e) Hb).
    apply mixa_qx_lt_1px. exact HMpos. }
  assert (Hc1 : Qlt (Qmult (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e)))
                              (Qplus (1#1)
                                 (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                    (1 - (Qmake a d))))) (Qmake nv dv))
                    (Qmult (Qplus (1#1)
                                (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                   (1 - (Qmake a d)))) (Qmake c e))).
  { apply (Qlt_le_trans _ (Qmult (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                    (1 - (Qmake a d))) (Qmake c e))).
    - apply (Qle_lt_trans _ (Qmake nv dv)).
      + exact Hscale.
      + exact Hwin.
    - exact (Qlt_le_weak _ _ HvW2). }
  assert (HB1n : ~ Qplus (1#1)
                     (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                        (1 - (Qmake a d))) == 0).
  { intro Hz. rewrite Hz in HB10. exact (Qlt_irrefl 0%Q HB10). }
  pose proof (Qmult_lt_compat_r _ _
                (Qinv (Qplus (1#1)
                          (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                             (1 - (Qmake a d)))))
                (mixa_qinv_pos _ HB10) Hc1) as Hmul.
  assert (E7 : Qeq (Qmult (Qmult (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d))))) (Qmake nv dv))
                             (Qinv (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d))))))
                    (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qmake nv dv))).
  { assert (Esw : Qeq (Qmult (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d))))) (Qmake nv dv))
                          (Qmult (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qmake nv dv)) (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d)))))).
    { transitivity (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qmult (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d)))) (Qmake nv dv))).
      - apply Qeq_sym. apply Qmult_assoc.
      - rewrite (Qmult_comm (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d)))) (Qmake nv dv)). apply Qmult_assoc. }
    rewrite Esw.
    rewrite <- (Qmult_assoc (Qmult (igr_qpow (Qmake a d) (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) (Qmake nv dv)) (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d)))) (Qinv (Qplus (1#1) (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1) (1 - (Qmake a d)))))).
    rewrite (Qmult_inv_r _ HB1n).
    apply Qmult_1_r. }
  assert (E8 : Qeq (Qmult (Qmult (Qplus (1#1)
                                     (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                        (1 - (Qmake a d)))) (Qmake c e))
                      (Qinv (Qplus (1#1)
                             (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                (1 - (Qmake a d))))))
                     (Qmake c e)).
  { rewrite <- (Qmult_assoc (Qplus (1#1)
                                (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                   (1 - (Qmake a d)))) (Qmake c e)
                   (Qinv (Qplus (1#1)
                          (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                             (1 - (Qmake a d)))))).
    rewrite (Qmult_comm (Qmake c e) (Qinv (Qplus (1#1)
                                   (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                      (1 - (Qmake a d)))))).
    rewrite (Qmult_assoc (Qplus (1#1)
                                (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                                   (1 - (Qmake a d))))
                   (Qinv (Qplus (1#1)
                          (Qmult (Qmake (Z.of_nat (mixa_win (Qmake nv dv) (1 - (Qmake a d)) (Qmake c e))) 1)
                             (1 - (Qmake a d))))) (Qmake c e)).
    rewrite (Qmult_inv_r _ HB1n). apply Qmult_1_l. }
  rewrite E7, E8 in Hmul.
  apply (mixa_qlt_test (Qmake a d) (Qmake nv dv) (Qmake c e)). exact Hmul.
Qed.

(* ============================================================ *)
(* ③ 选择器实例化：mixa_k_log_of / mixa_sel_accounts                      *)
(* ============================================================ *)
Definition mixa_k_log_of (k0 v b0 : Q) : nat :=
  mixa_bsearch (mixa_test k0 v b0)
    (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
    0 (mixa_win v (1 - k0) b0).

Lemma mixa_sel_accounts : forall k0 v b0 : Q,
  Qlt 0 k0 -> Qlt k0 (1#1) -> Qlt 0 v -> Qlt 0 b0 ->
  mixa_test k0 v b0 (mixa_k_log_of k0 v b0) = true /\
  (forall j : nat, Nat.lt j (mixa_k_log_of k0 v b0) ->
     mixa_test k0 v b0 j = false).
Proof.
  intros k0 v b0 Hk0 Hk1 Hv Hb.
  assert (Hwin2 : Nat.lt 0 (mixa_win v (1 - k0) b0)) by (unfold mixa_win; lia).
  destruct (mixa_bsearch_correct (mixa_test k0 v b0)
              (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
              0
              (fun (a b : nat) (Hab : Nat.le a b) (Hta : mixa_test k0 v b0 a = true) =>
                 mixa_test_mono k0 v b0 a b Hk0 (Qlt_le_weak k0 (1#1) Hk1) (Qlt_le_weak 0 v Hv) Hab Hta)
              0 (mixa_win v (1 - k0) b0)
              (fun (j : nat) (_ : Nat.le 0 j) (Hj : Nat.lt j 0) =>
                 False_ind (mixa_test k0 v b0 j = false) (Nat.nlt_0_r j Hj))
              (Nat.le_refl 0)
              (Nat.le_0_l (mixa_win v (1 - k0) b0))
              (mixa_test_at_win k0 v b0 Hk0 Hk1 Hv Hb)
              ltac:(rewrite Nat.sub_0_r; apply mixa_fuel_log; exact Hwin2))
    as [Ht Hmin].
  unfold mixa_k_log_of. split; [exact Ht |].
  intros j Hj. exact (Hmin j (Nat.le_0_l j) Hj).
Qed.

(* ============================================================ *)
(* ④ 提取桥与主件族（存档稿 :668-961 原形补入）                          *)
(* ============================================================ *)
Lemma mixa_k0_bridge : forall (kappa : Real) (eps : Q) (N : nat),
  QltT 0 eps ->
  (forall n : nat, NatLe N n -> QltT eps (projT1 real_one n - projT1 kappa n)) ->
  prod (QltT 0 (mixa_k0 eps))
       (prod (QltT (mixa_k0 eps) (1#1))
             (real_lt kappa (real_const (mixa_k0 eps)))).
Proof.
  intros kappa eps N Hpos HN.
  apply QltT_to_Qlt in Hpos.
  destruct kappa as [kn knc]. unfold mixa_k0.
  destruct (Qle_bool (2#1) eps) eqn:Hbr.
  - (* 支 A：κ₀ = 1/2 *)
    assert (H2le : Qle (2#1) eps) by (apply mixa_qle_bool_true; exact Hbr).
    split.
    + unfold QltT. vm_compute. reflexivity.
    + split.
      * unfold QltT. vm_compute. reflexivity.
      * exists (eps * (1#2)). split.
        -- apply Qlt_to_QltT.
           destruct eps as [a b2].
           unfold Qlt, Qmult in *. cbn [Qnum Qden] in *. simpl in *. lia.
        -- exists N. intros n Hn.
           specialize (HN n Hn).
           cbn [projT1 real_const] in *.
           apply QltT_to_Qlt in HN.
           apply Qlt_to_QltT.
           destruct eps as [a b2]. destruct (kn n) as [c d2].
           (* (Qmake a b2)·½ ≤ (Qmake a b2)−½ *)
           assert (Hle : Qle ((Qmake a b2) * (1#2)) ((Qmake a b2) - (1#2)))
             by (apply mixa_qhalf_le_sub; exact H2le).
           assert (Eo : Qeq ((Qmake a b2) - (1#2)) ((-(1#2)) + (Qmake a b2))) by mixa_qeq_zfold.
           assert (Ebr : Qeq ((1#2) - (c # d2))
                             ((-(1#2)) + (1 - (c # d2))))
             by exact (mixa_qhalf_bridge (c # d2)).
           apply (Qlt_le_trans _ ((-(1#2)) + (1 - (c # d2)))).
           { apply (Qle_lt_trans _ ((-(1#2)) + (Qmake a b2))).
             - rewrite <- Eo. exact Hle.
             - exact (proj2 (Qplus_lt_r (Qmake a b2) (1 - (c # d2)) (-(1#2)))
                        HN). }
           { exact (qeq_le _ _ (Qeq_sym _ _ Ebr)). }
  - (* 支 B：κ₀ = 1 − eps/2 *)
    assert (Hlt2 : Qlt eps (2#1)) by (apply mixa_qle_bool_false; exact Hbr).
    split.
    + apply Qlt_to_QltT.
      destruct eps as [a b2].
      apply mixa_qomh_pos. exact Hlt2.
    + split.
      * apply Qlt_to_QltT. apply mixa_qomh_lt1. exact Hpos.
      * exists (eps * (1#2)). split.
        -- apply Qlt_to_QltT.
           destruct eps as [a b2].
           unfold Qlt, Qmult in *. cbn [Qnum Qden] in *. simpl in *. lia.
        -- exists N. intros n Hn.
           specialize (HN n Hn).
           cbn [projT1 real_const] in *.
           apply QltT_to_Qlt in HN.
           apply Qlt_to_QltT.
           destruct eps as [a b2]. destruct (kn n) as [c d2].
           assert (Ebr : Qeq ((1 - (Qmake a b2) * (1#2)) - (c # d2))
                             ((-((Qmake a b2) * (1#2))) + (1 - (c # d2))))
             by exact (mixa_qsub_swap 1 (Qmake a b2 * (1#2)) (c # d2)).
           assert (HN2 : Qlt ((Qmake a b2) * (1#2) + (Qmake a b2) * (1#2))
                             (1 - (c # d2))).
           { apply (Qle_lt_trans _ (Qmake a b2)).
             - exact (qeq_le _ _ (Qeq_sym _ _ (mixa_qsplit (Qmake a b2)))).
             - exact HN. }
           apply (Qlt_le_trans _ ((-((Qmake a b2) * (1#2))) + (1 - (c # d2)))).
           { apply (Qle_lt_trans _ ((-((Qmake a b2) * (1#2)))
                                + ((Qmake a b2) * (1#2) + (Qmake a b2) * (1#2)))).
             - exact (qeq_le _ _ (mixa_qdouble ((Qmake a b2) * (1#2)))).
             - exact (proj2 (Qplus_lt_r ((Qmake a b2) * (1#2) + (Qmake a b2) * (1#2))
                              (1 - (c # d2)) (-((Qmake a b2) * (1#2)))) HN2). }
           { exact (qeq_le _ _ (Qeq_sym _ _ Ebr)). }
Qed.

Lemma mixa_b0_bridge : forall (budget : Real) (eps : Q) (N : nat),
  QltT 0 eps ->
  (forall n : nat, NatLe N n -> QltT eps (projT1 budget n - projT1 real_zero n)) ->
  prod (QltT 0 (mixa_b0 eps)) (real_lt (real_const (mixa_b0 eps)) budget).
Proof.
  intros budget eps N Hpos HN.
  apply QltT_to_Qlt in Hpos.
  destruct budget as [bn bnc]. unfold mixa_b0.
  split.
  - apply Qlt_to_QltT.
    destruct eps as [a b2].
    unfold Qlt, Qmult in *. cbn [Qnum Qden] in *. simpl in *. first [lia | nia].
  - exists (eps * (1#2)). split.
    + apply Qlt_to_QltT.
      destruct eps as [a b2].
      unfold Qlt, Qmult in *. cbn [Qnum Qden] in *. simpl in *. lia.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      cbn [projT1 real_zero] in HN.
      apply QltT_to_Qlt in HN.
      (* eps == bn n：经 sub_0 桥归一 HN *)
      assert (Ez : Qeq (bn n - 0) (bn n)) by exact (mixa_qsub_0 (bn n)).
      rewrite Ez in HN.
      apply Qlt_to_QltT.
      cbn [projT1 real_const].
      apply (mixa_qlt_sub_r (eps * (1#2)) (eps * (1#2)) (bn n)).
      apply (Qle_lt_trans _ eps).
      * exact (qeq_le _ _ (Qeq_sym _ _ (mixa_qsplit eps))).
      * exact HN.
Qed.

(* ============================================================ *)
(* 主件（Defined）与伴生强声明                                           *)
(* ============================================================ *)
Definition mixa_arch_v (T : Real) : Q :=
  Qmake (Z.of_nat (projT1 (real_arch T))) 1.

Theorem mixa_pow_budget_log_cert : forall (kappa TV0 budget : Real) (v : Q),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_le TV0 (real_const v) ->
  real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget v Hk1 Hk2 Ha Hvle Hb.
  destruct Hk2 as [epsk [Hposk [Nk HNk]]].
  destruct Hb as [epsb [Hposb [Nb HNb]]].
  destruct (mixa_k0_bridge kappa epsk Nk Hposk HNk)
    as [Hk0posT [Hk0lt1T Hk0real]].
  pose proof Hk0posT as Hk0posT0.
  destruct (mixa_b0_bridge budget epsb Nb Hposb HNb)
    as [Hb0posT Hb0real].
  apply QltT_to_Qlt in Hk0posT. apply QltT_to_Qlt in Hk0lt1T.
  apply QltT_to_Qlt in Hb0posT.
  assert (HvQ : Qlt 0 v).
  { apply (mixa_const_lt_inv0 v real_zero).
    exact (real_lt_le_trans real_zero TV0 (real_const v) Ha Hvle). }
  destruct (mixa_sel_accounts (mixa_k0 epsk) v (mixa_b0 epsb)
              Hk0posT Hk0lt1T HvQ Hb0posT)
    as [Htest Hmin].
  exists (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)).
  apply (real_le_lt_trans
           (real_mult (tv_rpow kappa
                         (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) TV0)
           (real_mult (tv_rpow (real_const (mixa_k0 epsk))
                         (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) (real_const v))
           budget).
  - apply (mixa_prod_le
             (tv_rpow kappa (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)))
             (tv_rpow (real_const (mixa_k0 epsk))
                (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)))
             TV0 (real_const v)).
    + apply (mixa_rpow_le kappa (real_const (mixa_k0 epsk))).
      * exact Hk1.
      * left. exact Hk0real.
      * left. exact (real_const_pos (mixa_k0 epsk) Hk0posT0).
    + exact Hvle.
    + left. exact Ha.
    + apply (mixa_rpow_nonneg).
      left. exact (real_const_pos (mixa_k0 epsk) Hk0posT0).
  - apply (real_eq_lt_lt
             (real_mult (tv_rpow (real_const (mixa_k0 epsk))
                        (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) (real_const v))
             (real_const (Qmult (igr_qpow (mixa_k0 epsk)
                            (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) v))
             budget).
    + exact (real_eq_trans
               (real_mult (tv_rpow (real_const (mixa_k0 epsk))
                          (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)))
                    (real_const v))
               (real_mult (real_const (igr_qpow (mixa_k0 epsk)
                              (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))))
                    (real_const v))
               (real_const (Qmult (igr_qpow (mixa_k0 epsk)
                              (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) v))
               (RealSetoid.real_eq_mult_compat
                  (tv_rpow (real_const (mixa_k0 epsk))
                     (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)))
                  (real_const v)
                  (real_const (igr_qpow (mixa_k0 epsk)
                     (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))))
                  (real_const v)
                  (mixa_rpow_const (mixa_k0 epsk)
                     (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)))
                  (real_eq_refl (real_const v)))
               (mixa_const_mult (igr_qpow (mixa_k0 epsk)
                    (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) v)).
    + apply (real_lt_trans
               (real_const (Qmult (igr_qpow (mixa_k0 epsk)
                              (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb))) v))
               (real_const (mixa_b0 epsb)) budget).
      * apply (real_const_lt _ _).
        exact (mixa_test_qlt (mixa_k0 epsk) v (mixa_b0 epsb)
                 (mixa_k_log_of (mixa_k0 epsk) v (mixa_b0 epsb)) Htest).
      * exact Hb0real.
Defined.

Theorem mixa_pow_budget_log : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hb.
  destruct (real_arch TV0) as [Nv [Hge Hv]].
  exact (mixa_pow_budget_log_cert kappa TV0 budget (Qmake (Z.of_nat Nv) 1)
           Hk1 Hk2 Ha (inl Hv) Hb).
Defined.

Theorem mixa_k_select_log : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 ->
  sigT (fun v : Q => real_le TV0 (real_const v)) ->
  real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hv Hb. unfold real_le in Ha.
  destruct Ha as [Halt | Haq].
  - destruct Hv as [v Hvc].
    exact (mixa_pow_budget_log_cert kappa TV0 budget v Hk1 Hk2 Halt Hvc Hb).
  - exists 0%nat.
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                   real_one TV0
                   (real_eq_refl real_one) (real_eq_refl TV0)).
      * apply (real_eq_trans (real_mult real_one TV0) TV0 real_zero).
        -- exact (mixa_mult_one_l TV0).
        -- exact (real_eq_sym _ _ Haq).
    + exact Hb.
Defined.

Corollary mixa_k_select_log_le : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 ->
  sigT (fun v : Q => real_le TV0 (real_const v)) ->
  real_lt real_zero budget ->
  sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hv Hb.
  destruct (mixa_k_select_log kappa TV0 budget Hk1 Hk2 Ha Hv Hb) as [k Hk].
  exists k. apply (RealSetoid.real_lt_le_iff_req). left. exact Hk.
Defined.

Theorem mixa_pow_budget_log_min : forall (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hb : real_lt real_zero budget),
  mixa_test (mixa_k0 (projT1 Hk2)) (mixa_arch_v TV0) (mixa_b0 (projT1 Hb))
            (mixa_k_log_of (mixa_k0 (projT1 Hk2)) (mixa_arch_v TV0)
                           (mixa_b0 (projT1 Hb))) = true
  /\ (forall j : nat,
        Nat.lt j (mixa_k_log_of (mixa_k0 (projT1 Hk2)) (mixa_arch_v TV0)
              (mixa_b0 (projT1 Hb))) ->
        mixa_test (mixa_k0 (projT1 Hk2)) (mixa_arch_v TV0)
                  (mixa_b0 (projT1 Hb)) j = false).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hb.
  destruct Hk2 as [epsk [Hposk [Nk HNk]]].
  destruct Hb as [epsb [Hposb [Nb HNb]]].
  destruct (mixa_k0_bridge kappa epsk Nk Hposk HNk) as [H1 [H2 _]].
  destruct (mixa_b0_bridge budget epsb Nb Hposb HNb) as [H3 _].
  apply QltT_to_Qlt in H1. apply QltT_to_Qlt in H2. apply QltT_to_Qlt in H3.
  unfold mixa_arch_v.
  destruct (real_arch TV0) as [Nv [Hge Hv]].
  cbn [projT1] in *.
  assert (Hvlt0 : real_lt real_zero (real_const (Qmake (Z.of_nat Nv) 1)))
    by exact (real_lt_trans real_zero TV0 (real_const (Qmake (Z.of_nat Nv) 1))
                Ha Hv).
  pose proof (mixa_const_lt_inv0 (Qmake (Z.of_nat Nv) 1) real_zero Hvlt0) as HvQ.
  apply mixa_sel_accounts.
  - exact H1.
  - exact H2.
  - exact HvQ.
  - exact H3.
Qed.

Theorem mixa_min_real_below : forall (k0 v b0 : Q) (j : nat),
  Qlt 0 k0 -> Qlt k0 (1#1) -> Qlt 0 v -> Qlt 0 b0 ->
  Nat.lt j (mixa_k_log_of k0 v b0) ->
  real_le (real_const b0)
          (real_mult (tv_rpow (real_const k0) j) (real_const v)).
Proof.
  intros k0 v b0 j Hk0 Hk1 Hv Hb Hj.
  destruct (mixa_sel_accounts k0 v b0 Hk0 Hk1 Hv Hb) as [_ Hmin].
  pose proof (Hmin j Hj) as Hf.
  assert (Hqle : Qle b0 (Qmult (igr_qpow k0 j) v)).
  { unfold mixa_test in Hf.
    destruct (Qlt_le_dec (Qmult (igr_qpow k0 j) v) b0) as [Hlt | Hle'].
    - rewrite (Qlt_to_QltT _ _ Hlt) in Hf. discriminate Hf.
    - exact Hle'. }
  apply Qle_to_QleT' in Hqle.
  apply (real_le_trans (real_const b0)
           (real_const (Qmult (igr_qpow k0 j) v))
           (real_mult (tv_rpow (real_const k0) j) (real_const v))).
  - exact (klc_const_le b0 (Qmult (igr_qpow k0 j) v) Hqle).
  - apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_const (Qmult (igr_qpow k0 j) v))
             (real_mult (real_const (igr_qpow k0 j)) (real_const v))
             (real_mult (tv_rpow (real_const k0) j) (real_const v))).
    + apply (real_eq_sym _ _).
      exact (mixa_const_mult (igr_qpow k0 j) v).
    + apply (real_eq_sym _ _).
      exact (RealSetoid.real_eq_mult_compat
               (tv_rpow (real_const k0) j) (real_const v)
               (real_const (igr_qpow k0 j)) (real_const v)
               (mixa_rpow_const k0 j) (real_eq_refl (real_const v))).
Qed.

Extraction "_tathP_G3.ml" mixa_pow_budget_log mixa_k_select_log
  mixa_k_select_log_le mixa_k_log_of mixa_bsearch mixa_test mixa_win
  mixa_k0 mixa_b0.

Print Assumptions mixa_qbern.
Print Assumptions mixa_qbern_base.
Print Assumptions mixa_win_gt.
Print Assumptions mixa_test_at_win.
Print Assumptions mixa_sel_accounts.
Print Assumptions mixa_k0_bridge.
Print Assumptions mixa_b0_bridge.
Print Assumptions mixa_pow_budget_log_cert.
Print Assumptions mixa_pow_budget_log.
Print Assumptions mixa_k_select_log.
Print Assumptions mixa_k_select_log_le.
Print Assumptions mixa_pow_budget_log_min.
Print Assumptions mixa_min_real_below.
