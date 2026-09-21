(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   mixb_bsearch_S（原 L571，2 句玩具证）                                *)
(*   mixb_gallop_S（原 L563，2 句玩具证）                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqMixLogB.v —— 席 tathB · Path B：倍增搜索（galloping）对数级选择器 *)
(*（AT11《对数级选择器设计分析-AT11-20260918》裁决 4 落地：k←1 起倍增    *)
(*  测试可判定 Q 谓词，末站区间二分定位精确最小 k；与 Path A（有理二分）  *)
(*  同场竞马，结构差异点见 attn/_tathB_交付报告-20260918.md。）          *)
(* ============================================================ *)
(* 依赖（全绿盘件，零改既有件）：                                        *)
(*   基座伞壳 CW_ConstructiveWorld_219（S01 And:66 Set 积型 /            *)
(*     S02 real_lt:465 sigT(eps:Q) 证书形 / real_le:469 Or 编码 /        *)
(*     real_arch S07:2772）；UpTVDoeblin（tv_rpow）；                    *)
(*     UpReqIterGeomRate（igr_qpow:1490 可复用件 + igr_k_enum 三账       *)
(*     sound/none/min 最小站扫描照抄消费）；Stdlib Lqa（lra Q 线性）。   *)
(* 本件承载（前缀 mixb_，全树 grep 零撞名）：                            *)
(*   ① Q 核：mixb_qtest / 幂单调四件 / mixb_qbernoulli（Q-Bernoulli      *)
(*      复刻：κ0^(S m)·(1+m·(1−κ0)) ≤ 1，纯 Q 环账零 exp/log）/          *)
(*      mixb_window_test_true（窗口命中账）。                            *)
(*   ② 搜索核（全 total·Defined·零 Prop 消去）：mixb_gallop（倍增，       *)
(*      尾差评支出合法站对）/ mixb_bsearch（区间二分）/ mixb_sel（复合）。*)
(*   ③ 账（Qed·Prop 伴生，igr 三账形）：                                 *)
(*      ★ mixb_sel_scale —— 量级定理（机器可陈述 nat 上界式）：双相       *)
(*        fuel:=S(S(log2 K)) 供给时返回恰为可判定谓词最小通过站，且       *)
(*        比较次数 c ≤ 2·log2 K + 5（「2·log₂K+O(1)」nat 形）；          *)
(*        mixb_sel_count（结构计数 ≤ S(f1+f2)，无条件成立）。            *)
(*   ④ Real 归约壳（AT11 裁决 1/2/3）：real_lt sigT 证书 → κ0:=1−μ       *)
(*      有理内点提取（μ:=min(eps/2,1/2) 双支 Defined）/ b0:=eps_b/2      *)
(*      提取 / TV0′ 显式证书前件 + 0≤TV0′ 桥 / 幂单调 Q 层直证 + Real    *)
(*      侧 tv_rpow 一次性归纳桥 / 窗口 real_arch 兜底（裁决 1(b)，免疫   *)
(*      Q 层上取整除法细节——裁决 3 窗端点陷阱排雷）。                    *)
(*   ⑤ 主件：mixb_k_select_log（Defined sigT nat：κ^k·TV0 < budget）      *)
(*      + mixb_k_select_log_le（Defined le 形）+ Q 引擎 mixb_qsel。      *)
(* 公理面：本件零新增公理；全部前提为 Set 层显式证书（real_lt sigT /      *)
(*   real_le Or / sigT TV0′ 证书），Print Assumptions 预期全 Closed。    *)
(* 红线自审（AT11 §红线三险点逐条）：                                    *)
(*   ①sigT 载荷只放 real_lt/real_le（Set）；最小性与计数为 Prop，一律     *)
(*     Qed 伴生件不入提取签名（igr 分工照抄）。                          *)
(*   ②Defined 体内零 Prop 消去：判据全 bool（Qle_bool/Nat.ltb）与        *)
(*     Set 型结构（sigT/Or/And 均 S01/S02 Set 层）；Prop 只以             *)
(*     「Qed 引理应用」形态进出（Prop→Set 箭头应用，非消去）。           *)
(*   ③语句面量词全 nat/Q/Real，比较全 Qle_bool/real_lt/real_le。         *)
(* 战术坑登记（本席探针定谳 _tathB_probe/_tathB_pA/_tathB_pC）：         *)
(*   lia/nia 不吃 Q（Q zify 缺位）；Q 线性阶目标用 Lqa 的 lra；Qeq 恒等   *)
(*   用 ring；replace-by-ring 撞 eq/Qeq 壁一律改 assert+rewrite；        *)
(*   Qabs 消去走 Qabs_case（Q→Type）+lra；Qed 内 Id/bool 判据照旧。      *)
(* 面界：Q 核零消费 Real 侧私有件；幂形统一 igr_qpow（Q）+ tv_rpow       *)
(*   （Real 一次性桥），勿信跨件幂 conversion（AT6 判词）。              *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——WALL-2 坑）：              *)
(*   cmd /c: set COQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq             *)
(*           set ROCQLIB=%COQLIB% & coqc.exe -q -Q . "" UpReqMixLogB.v   *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：Q/nat 环账小件                                                 *)
(* ============================================================ *)

Lemma mixb_q_12_pos : 0 < (1 # 2).
Proof. unfold Qlt. cbn. lia. Qed.

Lemma mixb_q_12_lt : (1 # 2) < 1.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma mixb_q_2_pos : 0 < 2.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma mixb_qle_0_1 : 0 <= 1.
Proof. unfold Qle. cbn. lia. Qed.

(* a ≤ b ⟹ 0 ≤ b − a *)
Lemma mixb_qle_sub : forall a b : Q, a <= b -> 0 <= b - a.
Proof. intros a b H. lra. Qed.

(* Qopp 保序（线性翻转件；lra 直证——单元上下文无单项式歧义） *)
Lemma mixb_qle_opp : forall u v : Q, u <= v -> - v <= - u.
Proof. intros u v H. lra. Qed.

(* Qeq 对称（S01/S02 只有 qeq_le；自建免疫 stdlib 漂移——Q18D 症状二口径） *)
Lemma mixb_qeq_sym : forall x y : Q, x == y -> y == x.
Proof. intros x y H. unfold Qeq in *. cbn [Qnum Qden] in *. lia. Qed.

Lemma mixb_qeq_trans : forall x y z : Q, x == y -> y == z -> x == z.
Proof. intros x y z H1 H2. transitivity y. assumption. assumption. Qed.

(* 0 ≤ D ⟹ A − D ≤ A *)
Lemma mixb_qsub_le_self : forall A D : Q, 0 <= D -> A - D <= A.
Proof. intros A D HD. lra. Qed.

(* Qeq 右替换保 ≤（环账桥通用件，禁裸 rewrite——探针 _tathB_pB 判词） *)
Lemma mixb_qle_eq_r : forall a b c : Q, b == c -> a <= b -> a <= c.
Proof.
  intros a b c Hbc Hab. apply (Qle_trans a b c).
  - exact Hab.
  - apply qeq_le. exact Hbc.
Qed.

Lemma mixb_qle_eq_l : forall a b c : Q, a == b -> b <= c -> a <= c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - apply qeq_le. exact Hab.
  - exact Hbc.
Qed.

(* 左乘保 ≤（stdlib Qmult_le_compat_l 缺位——IR3 卡先例，自建） *)
Lemma mixb_qmult_le_l : forall a x y : Q, x <= y -> 0 <= a -> a * x <= a * y.
Proof.
  intros a x y Hxy Ha.
  apply (Qle_trans (a * x) (x * a)).
  - apply qeq_le. ring.
  - apply (Qle_trans (x * a) (y * a)).
    + exact (Qmult_le_compat_r x y a Hxy Ha).
    + apply qeq_le. ring.
Qed.

(* 右加保 Qeq（Qplus_le_compat 双向 + antisym；B2 席增补） *)
Lemma mixb_qplus_wd_r : forall a x y : Q, x == y -> a + x == a + y.
Proof.
  intros a x y H. apply Qle_antisym.
  - apply (Qplus_le_compat a a x y).
    + apply Qle_refl.
    + apply qeq_le. exact H.
  - apply (Qplus_le_compat a a y x).
    + apply Qle_refl.
    + apply qeq_le. apply mixb_qeq_sym. exact H.
Qed.

(* Qeq 乘法保形（阶拆分 + lra 单项式归一；探针 _tathB_pD/_tathB_pG 判词： *)
(*   nia 不吃 Qeq 恒等目标/unfold-QDen 撞 Zpos 强转——此路线为替代正解）   *)
Lemma mixb_qmult_wd_l : forall a x y : Q, x == y -> a * x == a * y.
Proof.
  intros a x y Hxy.
  assert (Hx : x <= y) by (apply qeq_le; exact Hxy).
  assert (Hy : y <= x) by (apply qeq_le; apply mixb_qeq_sym; exact Hxy).
  destruct (Qle_bool 0 a) eqn:Ea0.
  - pose proof (proj1 (Qle_bool_iff 0 a) Ea0) as Ha0.
    apply Qle_antisym.
    + apply (Qle_trans (a * x) (x * a)).
      * apply qeq_le. ring.
      * apply (Qle_trans (x * a) (y * a)).
        -- exact (Qmult_le_compat_r x y a Hx Ha0).
        -- apply qeq_le. ring.
    + apply (Qle_trans (a * y) (y * a)).
      * apply qeq_le. ring.
      * apply (Qle_trans (y * a) (x * a)).
        -- exact (Qmult_le_compat_r y x a Hy Ha0).
        -- apply qeq_le. ring.
  - assert (Hn0 : ~ (0 <= a)).
    { intro Hc. assert (Ht : Qle_bool 0 a = true)
        by exact (proj2 (Qle_bool_iff 0 a) Hc).
      congruence. }
    assert (Ha0 : a <= 0) by lra.
    assert (H0a : 0 <= 0 - a) by lra.
    apply Qle_antisym.
    + apply (Qle_trans (a * x) ((- (x * (0 - a)))%Q)).
      * apply qeq_le. ring.
      * apply (Qle_trans (- (x * (0 - a))) (- (y * (0 - a)))).
        -- exact (mixb_qle_opp (y * (0 - a)) (x * (0 - a))
                    (Qmult_le_compat_r y x (0 - a) Hy H0a)).
        -- apply qeq_le. ring.
    + apply (Qle_trans (a * y) ((- (y * (0 - a)))%Q)).
      * apply qeq_le. ring.
      * apply (Qle_trans (- (y * (0 - a))) (- (x * (0 - a)))).
        -- exact (mixb_qle_opp (x * (0 - a)) (y * (0 - a))
                    (Qmult_le_compat_r x y (0 - a) Hx H0a)).
        -- apply qeq_le. ring.
Qed.

Lemma mixb_qmult_wd_r : forall a x y : Q, x == y -> x * a == y * a.
Proof.
  intros a x y Hxy.
  assert (Hx : x <= y) by (apply qeq_le; exact Hxy).
  assert (Hy : y <= x) by (apply qeq_le; apply mixb_qeq_sym; exact Hxy).
  destruct (Qle_bool 0 a) eqn:Ea0.
  - pose proof (proj1 (Qle_bool_iff 0 a) Ea0) as Ha0.
    apply Qle_antisym.
    + exact (Qmult_le_compat_r x y a Hx Ha0).
    + exact (Qmult_le_compat_r y x a Hy Ha0).
  - assert (Hn0 : ~ (0 <= a)).
    { intro Hc. assert (Ht : Qle_bool 0 a = true)
        by exact (proj2 (Qle_bool_iff 0 a) Hc).
      congruence. }
    assert (Ha0 : a <= 0) by lra.
    assert (H0a : 0 <= 0 - a) by lra.
    apply Qle_antisym.
    + apply (Qle_trans (x * a) ((- (x * (0 - a)))%Q)).
      * apply qeq_le. ring.
      * apply (Qle_trans (- (x * (0 - a))) (- (y * (0 - a)))).
        -- exact (mixb_qle_opp (y * (0 - a)) (x * (0 - a))
                    (Qmult_le_compat_r y x (0 - a) Hy H0a)).
        -- apply qeq_le. ring.
    + apply (Qle_trans (y * a) ((- (y * (0 - a)))%Q)).
      * apply qeq_le. ring.
      * apply (Qle_trans (- (y * (0 - a))) (- (x * (0 - a)))).
        -- exact (mixb_qle_opp (x * (0 - a)) (y * (0 - a))
                    (Qmult_le_compat_r x y (0 - a) Hx H0a)).
        -- apply qeq_le. ring.
Qed.

(* Qeq 右替换保乘 ≤ *)
Lemma mixb_qmult_le_wd_r : forall a x y : Q, x == y -> 0 <= a -> a * x <= a * y.
Proof.
  intros a x y Hxy Ha.
  apply (Qle_trans (a * x) (x * a)).
  - apply qeq_le. ring.
  - apply (Qle_trans (x * a) (y * a)).
    + apply (Qmult_le_compat_r x y a).
      * apply qeq_le. exact Hxy.
      * exact Ha.
    + apply qeq_le. ring.
Qed.

(* 0≤a、0≤b ⟹ 0≤a·b *)
Lemma mixb_qmult_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  intros a b Ha Hb.
  apply (Qle_trans 0 (0 * b) (a * b)).
  - apply qeq_le. apply mixb_qeq_sym. apply Qmult_0_l.
  - exact (Qmult_le_compat_r 0 a b Ha Hb).
Qed.

(* 桥用恒等：v·z⁻¹·z == v（0<z） *)
Lemma mixb_qmul_inv_cancel : forall v z : Q, 0 < z -> v * Qinv z * z == v.
Proof.
  intros v z Hz.
  assert (Hne : ~ (z == 0)).
  { intro He. apply (Qlt_not_eq 0 z Hz). apply mixb_qeq_sym. exact He. }
  assert (Hinv : (z * Qinv z)%Q == 1) by (apply Qmult_inv_r; exact Hne).
  apply (mixb_qeq_trans (v * Qinv z * z) (v * (z * Qinv z))).
  - ring.
  - apply (mixb_qeq_trans (v * (z * Qinv z)) (v * 1)).
    + apply (mixb_qmult_wd_l v (z * Qinv z) 1 Hinv).
    + apply Qmult_1_r.
Qed.

(* 半量严格缩：0 < x ⟹ x·½ < x *)
Lemma mixb_qhalf_lt : forall x : Q, 0 < x -> x * (1 # 2) < x.
Proof.
  intros x Hx.
  assert (Heq : (x * (1 # 2) * 2)%Q == x%Q) by field.
  lra.
Qed.

(* nat 幂正 *)
Lemma mixb_pow2_pos : forall m : nat, (1 <= 2 ^ m)%nat.
Proof.
  intro m. induction m as [| m IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

(* 1 ≤ u ⟹ d ≤ u·d（width 账用；避 nia 非线性证书） *)
Lemma mixb_le_mul_l : forall u d : nat, (1 <= u -> d <= u * d)%nat.
Proof.
  intros u d Hu.
  assert (H1 : (d * 1 <= d * u)%nat)
    by (apply (Nat.mul_le_mono_l 1 u d); exact Hu).
  replace (d * 1)%nat with d%nat in H1 by lia.
  replace (d * u)%nat with (u * d)%nat in H1 by lia.
  exact H1.
Qed.

(* div2 平移：div2(2·lo+x) = lo + div2 x *)
Lemma mixb_div2_shift : forall lo x : nat,
  (Nat.div2 (2 * lo + x) = lo + Nat.div2 x)%nat.
Proof.
  intros lo x. induction lo as [| lo IH].
  - replace (2 * 0 + x)%nat with (x)%nat by lia. rewrite Nat.div2_div. lia.
  - replace (2 * Datatypes.S lo + x)%nat with (Datatypes.S (Datatypes.S (2 * lo + x)))%nat by lia.
    cbn [Nat.div2]. rewrite IH. reflexivity.
Qed.

Lemma mixb_div2_le : forall d A : nat, (d <= 2 * A -> Nat.div2 d <= A)%nat.
Proof.
  intros d A H. rewrite Nat.div2_div.
  apply (Nat.div_le_upper_bound d 2%nat A); lia.
Qed.

Lemma mixb_div2_split : forall d A : nat, (d <= 2 * A -> d - Nat.div2 d <= A)%nat.
Proof.
  intros d A H.
  pose proof (Nat.div_mod d 2) as Hdm.
  pose proof (Nat.mod_upper_bound d 2) as Hm2.
  assert (H2 : (2 <> 0)%nat) by lia.
  pose proof (Hdm H2) as Hdm2. pose proof (Hm2 H2) as Hm2'.
  pose proof (mixb_div2_le d A H) as Hq.
  rewrite Nat.div2_div in Hq.
  rewrite Nat.div2_div.
  lia.
Qed.

(* ============================================================ *)
(* Part 1：Q 核——幂账、Q-Bernoulli 复刻、谓词/单调/窗口                   *)
(* ============================================================ *)

Lemma mixb_qpow_nonneg : forall (q : Q) (m : nat), 0 <= q -> 0 <= igr_qpow q m.
Proof.
  intros q m Hq. induction m as [| m IH].
  - replace (igr_qpow q 0) with 1%Q by reflexivity. apply mixb_qle_0_1.
  - cbn [igr_qpow]. exact (mixb_qmult_ge0 q (igr_qpow q m) Hq IH).
Qed.

Lemma mixb_qpow_pos : forall (q : Q) (m : nat), 0 < q -> 0 < igr_qpow q m.
Proof.
  intros q m Hq. induction m as [| m IH].
  - replace (igr_qpow q 0) with 1%Q by reflexivity. unfold Qlt. cbn. lia.
  - cbn [igr_qpow]. exact (Qmult_lt_0_compat q (igr_qpow q m) Hq IH).
Qed.

(* 指数上界：q ≤ 1 ⟹ q^m ≤ 1 *)
Lemma mixb_qpow_le_one : forall (q : Q) (m : nat),
  0 <= q -> q <= 1 -> igr_qpow q m <= 1.
Proof.
  intros q m Hq0 Hq1. induction m as [| m IH].
  - replace (igr_qpow q 0) with 1%Q by reflexivity. apply Qle_refl.
  - cbn [igr_qpow].
    apply (Qle_trans _ (1 * igr_qpow q m)%Q).
    + apply (Qmult_le_compat_r q 1 (igr_qpow q m)).
      * exact Hq1.
      * apply mixb_qpow_nonneg. exact Hq0.
    + apply (mixb_qle_eq_l (1 * igr_qpow q m) (igr_qpow q m) 1).
      * ring.
      * exact IH.
Qed.

(* 单步指数单调：q^(S m) ≤ q^m *)
Lemma mixb_qpow_dec : forall (q : Q) (m : nat),
  0 <= q -> q <= 1 -> igr_qpow q (Datatypes.S m) <= igr_qpow q m.
Proof.
  intros q m Hq0 Hq1. cbn [igr_qpow].
  apply (Qle_trans _ (1 * igr_qpow q m)%Q).
  - apply (Qmult_le_compat_r q 1 (igr_qpow q m)).
    + exact Hq1.
    + apply mixb_qpow_nonneg. exact Hq0.
  - apply (mixb_qle_eq_l (1 * igr_qpow q m) (igr_qpow q m) (igr_qpow q m)).
    + ring.
    + apply Qle_refl.
Qed.

(* 任意指数单调（j ≤ j'）：q^(j') ≤ q^j *)
Lemma mixb_qpow_dec_le : forall (q : Q) (j j' : nat),
  0 <= q -> q <= 1 -> (j <= j')%nat -> igr_qpow q j' <= igr_qpow q j.
Proof.
  intros q j j' Hq0 Hq1 Hle. induction Hle as [| j' Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (igr_qpow q j')).
    + apply (mixb_qpow_dec q j'); assumption.
    + exact IH.
Qed.

(* 换底单调：x ≤ y ⟹ x^m ≤ y^m *)
(* Q-Bernoulli 复刻：κ0^(S m)·(1 + m·(1−κ0)) ≤ 1（0<κ0≤1；纯 Q 环账） *)
Lemma mixb_qbernoulli : forall (q : Q) (m : nat),
  0 < q -> q <= 1 ->
  igr_qpow q (Datatypes.S m) * (1 + (Z.of_nat m # 1) * (1 - q)) <= 1.
Proof.
  intros q m Hq0 Hq1. induction m as [| m IH].
  - cbn [igr_qpow].
    assert (HZ : (Z.of_nat 0 # 1)%Q <= 0) by (unfold Qle; cbn; lia).
    assert (HZq : ((Z.of_nat 0 # 1) * (1 - q))%Q <= 0).
    { assert (Hq1le : 0 <= 1 - q) by exact (mixb_qle_sub q 1 Hq1).
      pose proof (Qmult_le_compat_r (Z.of_nat 0 # 1) 0 (1 - q) HZ Hq1le) as HH.
      assert (Hr0 : (0 * (1 - q))%Q == 0) by ring.
      rewrite Hr0 in HH. exact HH. }
    assert (HXle : (1 + (Z.of_nat 0 # 1) * (1 - q))%Q <= 1%Q).
    { apply (Qle_trans _ (1 + 0 * (1 - q))%Q).
      - apply (Qplus_le_compat 1 1 ((Z.of_nat 0 # 1) * (1 - q)) (0 * (1 - q))).
        + exact HZq.
        + apply (Qle_trans ((Z.of_nat 0 # 1) * (1 - q)) 0 (0 * (1 - q))).
          * exact HZq.
          * apply qeq_le. apply mixb_qeq_sym. apply Qmult_0_l.
      - assert (H1r : (1 + 0 * (1 - q))%Q == 1%Q) by ring.
        apply (mixb_qle_eq_l (1 + 0 * (1 - q)) 1 1 H1r).
        apply Qle_refl. }
    apply (Qle_trans _ (q * (1 + (Z.of_nat 0 # 1) * (1 - q)))%Q).
    + apply qeq_le. ring.
    + apply (Qle_trans _ (q * 1)%Q).
      * apply (mixb_qmult_le_l q (1 + (Z.of_nat 0 # 1) * (1 - q)) 1 HXle
                 (Qlt_le_weak 0 q Hq0)).
      * apply (mixb_qle_eq_l (q * 1) q 1).
        -- ring.
        -- exact Hq1.
  - cbn [igr_qpow].
    pose proof (mixb_qle_sub q 1 Hq1) as Hsq.
    assert (Hmpos : 0 <= (Z.of_nat (Datatypes.S m) # 1)).
    { unfold Qle. cbn. lia. }
    assert (Hm1 : (Z.of_nat (Datatypes.S m) # 1)%Q == ((Z.of_nat m # 1) + 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; lia).
    assert (HA0 : 0 <= (Z.of_nat (Datatypes.S m) # 1) * (1 - q))
      by exact (mixb_qmult_ge0 (Z.of_nat (Datatypes.S m) # 1) (1 - q) Hmpos Hsq).
    assert (HAq : (Z.of_nat (Datatypes.S m) # 1) * (1 - q) * q
                  <= (Z.of_nat (Datatypes.S m) # 1) * (1 - q)).
    { apply (mixb_qle_eq_r ((Z.of_nat (Datatypes.S m) # 1) * (1 - q) * q)
               ((Z.of_nat (Datatypes.S m) # 1) * (1 - q) * 1)
               ((Z.of_nat (Datatypes.S m) # 1) * (1 - q))).
      - ring.
      - exact (mixb_qmult_le_l ((Z.of_nat (Datatypes.S m) # 1) * (1 - q)) q 1
                 Hq1 HA0). }
    assert (Hm1wd : (Z.of_nat (Datatypes.S m) # 1) * (1 - q)
                    == ((Z.of_nat m # 1) + 1) * (1 - q))
      by exact (mixb_qmult_wd_r (1 - q) (Z.of_nat (Datatypes.S m) # 1)
                  ((Z.of_nat m # 1) + 1)%Q Hm1).
    (* Hstep：q·(1+(m+1)s) = q+(m+1)s·q ≤ q+(m+1)s = 1+m·s（s := 1−q） *)
    assert (Hstep : q * (1 + (Z.of_nat (Datatypes.S m) # 1) * (1 - q))
                    <= 1 + (Z.of_nat m # 1) * (1 - q)).
    { apply (Qle_trans _ (q + (Z.of_nat (Datatypes.S m) # 1) * (1 - q) * q)%Q).
      - apply qeq_le. ring.
      - apply (Qle_trans _ (q + (Z.of_nat (Datatypes.S m) # 1) * (1 - q))%Q).
        + apply (Qplus_le_compat q q
                   ((Z.of_nat (Datatypes.S m) # 1) * (1 - q) * q)
                   ((Z.of_nat (Datatypes.S m) # 1) * (1 - q))).
          * apply Qle_refl.
          * exact HAq.
        + apply (mixb_qle_eq_l (q + (Z.of_nat (Datatypes.S m) # 1) * (1 - q))
                   (q + ((Z.of_nat m # 1) + 1) * (1 - q))%Q
                   (1 + (Z.of_nat m # 1) * (1 - q))%Q).
          * apply (mixb_qplus_wd_r q
                     ((Z.of_nat (Datatypes.S m) # 1) * (1 - q))
                     (((Z.of_nat m # 1) + 1) * (1 - q)) Hm1wd).
          * apply qeq_le. ring. }
    apply (Qle_trans _ ((q * (1 + (Z.of_nat (Datatypes.S m) # 1) * (1 - q)))
                          * (q * igr_qpow q m))%Q).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((1 + (Z.of_nat m # 1) * (1 - q)) * (q * igr_qpow q m))%Q).
      * exact (Qmult_le_compat_r
                 (q * (1 + (Z.of_nat (Datatypes.S m) # 1) * (1 - q)))
                 (1 + (Z.of_nat m # 1) * (1 - q)) (q * igr_qpow q m) Hstep
                 (mixb_qmult_ge0 q (igr_qpow q m) (Qlt_le_weak 0 q Hq0)
                    (mixb_qpow_nonneg q m (Qlt_le_weak 0 q Hq0)))).
      * cbn [igr_qpow] in IH.
        apply (mixb_qle_eq_l ((1 + (Z.of_nat m # 1) * (1 - q)) * (q * igr_qpow q m))
                 (q * igr_qpow q m * (1 + (Z.of_nat m # 1) * (1 - q)))%Q 1).
        -- ring.
        -- exact IH.
Qed.

(* 可判定谓词：κ0^m·v ≤ b0（Qle_bool 哨兵） *)
Definition mixb_qtest (kappa0 v b0 : Q) (m : nat) : bool :=
  Qle_bool (Qmult (igr_qpow kappa0 m) v) b0.

(* 谓词单调（过站集上闭） *)
Definition mixb_mono (test : nat -> bool) : Prop :=
  forall j j' : nat, (j <= j')%nat -> test j = true -> test j' = true.

Lemma mixb_qtest_mono : forall kappa0 v b0 : Q,
  0 < kappa0 -> kappa0 <= 1 -> 0 <= v ->
  mixb_mono (mixb_qtest kappa0 v b0).
Proof.
  intros kappa0 v b0 Hk0 Hk1 Hv0 j j' Hjj Hj.
  unfold mixb_qtest in *. apply (proj2 (Qle_bool_iff _ _)).
  apply (Qle_trans _ (igr_qpow kappa0 j * v)%Q).
  - apply (Qmult_le_compat_r (igr_qpow kappa0 j') (igr_qpow kappa0 j) v).
    + apply (mixb_qpow_dec_le kappa0 j j');
        [lra | exact Hk1 | exact Hjj].
    + exact Hv0.
  - exact (proj1 (Qle_bool_iff _ _) Hj).
Qed.

(* 窗口命中账：v ≤ K·(1−κ0)·b0（K≥1）⟹ test(K)=true（Q-Bernoulli 反解） *)
Lemma mixb_window_test_true : forall (kappa0 v b0 : Q) (K : nat),
  0 < kappa0 -> kappa0 < 1 -> 0 <= v -> 0 < b0 -> (1 <= K)%nat ->
  Qle v ((Z.of_nat K # 1) * ((1 - kappa0) * b0)) ->
  mixb_qtest kappa0 v b0 K = true.
Proof.
  intros kappa0 v b0 K Hk0 Hk1 Hv0 Hb0 HK1 Hwin.
  destruct K as [| m]; [lia |].
  unfold mixb_qtest. apply (proj2 (Qle_bool_iff _ _)).
  pose proof (mixb_qbernoulli kappa0 m Hk0 (Qlt_le_weak kappa0 1 Hk1)) as Hbern.
  pose proof (mixb_qpow_nonneg kappa0 (Datatypes.S m) (Qlt_le_weak 0 kappa0 Hk0)) as Hpn.
  assert (Hb0nn : 0 <= b0) by exact (Qlt_le_weak 0 b0 Hb0).
  assert (Hbr : (Z.of_nat (Datatypes.S m) # 1) * (1 - kappa0)
                <= 1 + (Z.of_nat m # 1) * (1 - kappa0)).
  { assert (Hs : (Z.of_nat (Datatypes.S m) # 1)%Q == (1 + (Z.of_nat m # 1))%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; lia).
    apply (Qle_trans _ ((1 + (Z.of_nat m # 1)) * (1 - kappa0))).
    - apply qeq_le.
      exact (mixb_qmult_wd_r (1 - kappa0) (Z.of_nat (Datatypes.S m) # 1)
               (1 + (Z.of_nat m # 1)) Hs).
    - apply (Qle_trans _ (1 * (1 - kappa0)
                            + (Z.of_nat m # 1) * (1 - kappa0))).
      + apply qeq_le. ring.
      + apply (Qplus_le_compat (1 * (1 - kappa0)) 1
                 ((Z.of_nat m # 1) * (1 - kappa0)) ((Z.of_nat m # 1) * (1 - kappa0))).
        * apply (mixb_qle_eq_l (1 * (1 - kappa0)) (1 - kappa0) 1).
          -- ring.
          -- lra.
        * apply Qle_refl. }
  apply (Qle_trans _ (igr_qpow kappa0 (Datatypes.S m)
                        * ((Z.of_nat (Datatypes.S m) # 1) * ((1 - kappa0) * b0)))%Q).
  - exact (mixb_qmult_le_l (igr_qpow kappa0 (Datatypes.S m)) v
             ((Z.of_nat (Datatypes.S m) # 1) * ((1 - kappa0) * b0)) Hwin Hpn).
  - apply (Qle_trans _ ((igr_qpow kappa0 (Datatypes.S m)
                            * (1 + (Z.of_nat m # 1) * (1 - kappa0))) * b0)%Q).
    + apply (Qle_trans _ (igr_qpow kappa0 (Datatypes.S m)
                             * ((1 + (Z.of_nat m # 1) * (1 - kappa0)) * b0))%Q).
      * apply (mixb_qmult_le_l (igr_qpow kappa0 (Datatypes.S m))
                  ((Z.of_nat (Datatypes.S m) # 1) * ((1 - kappa0) * b0))
                  ((1 + (Z.of_nat m # 1) * (1 - kappa0)) * b0)).
        -- apply (mixb_qle_eq_l ((Z.of_nat (Datatypes.S m) # 1)
                                    * ((1 - kappa0) * b0))
                    ((Z.of_nat (Datatypes.S m) # 1) * (1 - kappa0) * b0)
                    ((1 + (Z.of_nat m # 1) * (1 - kappa0)) * b0)).
           ** ring.
           ** exact (Qmult_le_compat_r
                       ((Z.of_nat (Datatypes.S m) # 1) * (1 - kappa0))
                       (1 + (Z.of_nat m # 1) * (1 - kappa0)) b0 Hbr Hb0nn).
        -- exact Hpn.
      * apply (mixb_qle_eq_l (igr_qpow kappa0 (Datatypes.S m)
                                   * ((1 + (Z.of_nat m # 1) * (1 - kappa0)) * b0))
                 ((igr_qpow kappa0 (Datatypes.S m)
                     * (1 + (Z.of_nat m # 1) * (1 - kappa0))) * b0)
                 ((igr_qpow kappa0 (Datatypes.S m)
                     * (1 + (Z.of_nat m # 1) * (1 - kappa0))) * b0)).
        -- ring.
        -- apply Qle_refl.
    + apply (Qle_trans _ (1 * b0)%Q).
      * exact (Qmult_le_compat_r (igr_qpow kappa0 (Datatypes.S m)
                     * (1 + (Z.of_nat m # 1) * (1 - kappa0))) 1 b0 Hbern Hb0nn).
      * apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* Part 2：搜索核——倍增（galloping）+ 区间二分（全 total·Defined）         *)
(*   返回 (答案, 谓词求值次数)；每层 fuel 至多一次 test 应用。             *)
(* ============================================================ *)

Fixpoint mixb_gallop (test : nat -> bool) (f lo hi : nat) : ((nat * nat) * nat)%type :=
  match f with
  | Datatypes.O => ((lo, hi), 0%nat)
  | Datatypes.S f' =>
      if test hi
      then ((lo, hi), 1%nat)
      else let r := mixb_gallop test f' hi (hi + 2 * (hi - lo))%nat in
           ((fst (fst r), snd (fst r)), Datatypes.S (snd r))
  end.

Fixpoint mixb_bsearch (test : nat -> bool) (f lo hi : nat) : (nat * nat)%type :=
  match f with
  | Datatypes.O => (hi, 0%nat)
  | Datatypes.S f' =>
      if Nat.ltb lo (Nat.div2 (lo + hi)%nat)
      then (if test (Nat.div2 (lo + hi)%nat)
            then let r1 := mixb_bsearch test f' lo (Nat.div2 (lo + hi)%nat) in
                 (fst r1, Datatypes.S (snd r1))
            else let r2 := mixb_bsearch test f' (Nat.div2 (lo + hi)%nat) hi in
                 (fst r2, Datatypes.S (snd r2)))
      else (hi, 1%nat)
  end.

Definition mixb_sel (test : nat -> bool) (f1 f2 : nat) : (nat * nat)%type :=
  let g := mixb_gallop test f1 0%nat 1%nat in
  let b := mixb_bsearch test f2 (fst (fst g)) (snd (fst g)) in
  (fst b, (snd g + snd b)%nat).

(* —— B2 席加固三件：一步展开冻结 + 复合展开桥（防 cbn 过度下折/let 残留） —— *)
Lemma mixb_gallop_S : forall (test : nat -> bool) (f lo hi : nat),
  mixb_gallop test (Datatypes.S f) lo hi =
  (if test hi
   then ((lo, hi), 1%nat)
   else (let r := mixb_gallop test f hi (hi + 2 * (hi - lo))%nat in
         ((fst (fst r), snd (fst r)), Datatypes.S (snd r)))).
Proof. intros test f lo hi.
  exact (eq_refl (if test hi
                  then ((lo, hi), 1%nat)
                  else (let r := mixb_gallop test f hi (hi + 2 * (hi - lo))%nat in
                        ((fst (fst r), snd (fst r)), Datatypes.S (snd r))))).
Qed.

Lemma mixb_bsearch_S : forall (test : nat -> bool) (f lo hi : nat),
  mixb_bsearch test (Datatypes.S f) lo hi =
  (if Nat.ltb lo (Nat.div2 (lo + hi)%nat)
   then (if test (Nat.div2 (lo + hi)%nat)
         then (let r1 := mixb_bsearch test f lo (Nat.div2 (lo + hi)%nat) in
               (fst r1, Datatypes.S (snd r1)))
         else (let r2 := mixb_bsearch test f (Nat.div2 (lo + hi)%nat) hi in
               (fst r2, Datatypes.S (snd r2))))
   else (hi, 1%nat)).
Proof. intros test f lo hi.
  exact (eq_refl (if Nat.ltb lo (Nat.div2 (lo + hi)%nat)
                  then (if test (Nat.div2 (lo + hi)%nat)
                        then (let r1 := mixb_bsearch test f lo (Nat.div2 (lo + hi)%nat) in
                              (fst r1, Datatypes.S (snd r1)))
                        else (let r2 := mixb_bsearch test f (Nat.div2 (lo + hi)%nat) hi in
                              (fst r2, Datatypes.S (snd r2))))
                  else (hi, 1%nat))).
Qed.

Lemma mixb_sel_eq : forall (test : nat -> bool) (f1 f2 l h c1 r c2 : nat),
  mixb_gallop test f1 0%nat 1%nat = ((l, h), c1) ->
  mixb_bsearch test f2 l h = (r, c2) ->
  mixb_sel test f1 f2 = (r, (c1 + c2)%nat).
Proof.
  intros test f1 f2 l h c1 r c2 Eg Eb.
  unfold mixb_sel. rewrite Eg. cbv zeta. cbn [fst snd]. rewrite Eb. cbv zeta.
  cbn [fst snd]. reflexivity.
Qed.

(* 结构计数：谓词求值次数 ≤ fuel（无条件，量级定理的承重半边） *)
Lemma mixb_gallop_c_le : forall (test : nat -> bool) (f lo hi : nat),
  (snd (mixb_gallop test f lo hi) <= f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [mixb_gallop fst snd]. lia.
  - cbn [mixb_gallop]. destruct (test hi).
    + cbn [fst snd]. lia.
    + cbv zeta. cbn [fst snd].
      specialize (IH hi (hi + 2 * (hi - lo))%nat). cbn [fst snd] in IH. lia.
Qed.

Lemma mixb_bsearch_c_le : forall (test : nat -> bool) (f lo hi : nat),
  (snd (mixb_bsearch test f lo hi) <= Datatypes.S f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [mixb_bsearch fst snd]. lia.
  - cbn [mixb_bsearch]. destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)).
    + destruct (test (Nat.div2 (lo + hi)%nat)).
      * cbv zeta. cbn [fst snd].
        specialize (IH lo (Nat.div2 (lo + hi)%nat)). cbn [fst snd] in IH. lia.
      * cbv zeta. cbn [fst snd].
        specialize (IH (Nat.div2 (lo + hi)%nat) hi). cbn [fst snd] in IH. lia.
    + cbn [fst snd]. lia.
Qed.

(* 量级定理·计数半边：比较次数 ≤ S(f1+f2)（=2·log₂K+O(1) 的结构上界） *)
Theorem mixb_sel_count : forall (test : nat -> bool) (f1 f2 : nat),
  (snd (mixb_sel test f1 f2) <= Datatypes.S (f1 + f2))%nat.
Proof.
  intros test f1 f2.
  destruct (mixb_gallop test f1 0%nat 1%nat) as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test f2 l h) as [r c2] eqn:Eb.
  pose proof (mixb_gallop_c_le test f1 0%nat 1%nat) as H1.
  rewrite Eg in H1. cbn [fst snd] in H1.
  pose proof (mixb_bsearch_c_le test f2 l h) as H2.
  rewrite Eb in H2. cbn [fst snd] in H2.
  assert (Hs : mixb_sel test f1 f2 = (r, (c1 + c2)%nat))
    by exact (mixb_sel_eq test f1 f2 l h c1 r c2 Eg Eb).
  rewrite Hs. cbn [snd]. lia.
Qed.

(* ============================================================ *)
(* Part 3：搜索账——可靠/最小/量级（Prop 伴生，igr 三账形）                 *)
(* ============================================================ *)

(* 倍增宽度账：末站对宽度 ≤ 2^(S f)·初宽（bsearch fuel 配给的承重账） *)
Lemma mixb_gallop_width_le : forall (test : nat -> bool) (f lo hi l h c : nat),
  (lo < hi ->
  mixb_gallop test (Datatypes.S f) lo hi = ((l, h), c) ->
  h - l <= 2 ^ (Datatypes.S f) * (hi - lo))%nat.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi l h c Hlt Heq.
  - rewrite mixb_gallop_S in Heq. destruct (test hi) eqn:Ehi.
    + injection Heq; intros; subst. cbn [Nat.pow]. lia.
    + cbn [mixb_gallop] in Heq. cbv zeta in Heq. cbn [fst snd] in Heq.
      injection Heq; intros; subst. cbn [Nat.pow]. lia.
  - rewrite mixb_gallop_S in Heq. destruct (test hi) eqn:Ehi.
    + injection Heq; intros; subst. apply mixb_le_mul_l.
      apply mixb_pow2_pos.
    + destruct (mixb_gallop test (Datatypes.S f) hi (hi + 2 * (hi - lo))%nat)
        as [[l2 h2] c2] eqn:Eg2.
      cbv zeta in Heq. cbn [fst snd] in Heq.
      injection Heq; intros; subst.
      assert (Hlt2 : (hi < hi + 2 * (hi - lo))%nat) by lia.
      pose proof (IH hi (hi + 2 * (hi - lo))%nat l h c2 Hlt2 Eg2) as IHc.
      replace (hi + 2 * (hi - lo) - hi)%nat with (2 * (hi - lo))%nat in IHc
        by lia.
      cbn [Nat.pow] in IHc. cbn [Nat.pow].
      assert (Hb : (2 * (2 * 2 ^ f) * (hi - lo)
                    = (2 * 2 ^ f) * (2 * (hi - lo)))%nat) by lia.
      rewrite Hb. exact IHc.
Qed.

(* 倍增可靠+最小账：可达性 k ≤ hi+(hi−lo)·2^f 下，末站对必夹住过段        *)
(* （fail-fallback 支由可达性+单调性补账——total gallop 的良性出格）       *)
Lemma mixb_gallop_account : forall (test : nat -> bool) (f k lo hi l h c : nat),
  mixb_mono test -> (lo < hi)%nat -> test lo = false ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (k <= hi + (hi - lo) * 2 ^ f)%nat ->
  mixb_gallop test (Datatypes.S f) lo hi = ((l, h), c) ->
  (l < h /\ test h = true /\ test l = false /\ c <= Datatypes.S f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros k lo hi l h c
    Hmono Hlt Hlo Htk Hmin Hreach Heq.
  - cbn [Nat.pow] in Hreach.
    rewrite mixb_gallop_S in Heq. destruct (test hi) eqn:Ehi.
    + injection Heq; intros; subst.
      split; [lia |]. split; [exact Ehi |]. split; [exact Hlo | lia].
    + cbn [mixb_gallop] in Heq. cbv zeta in Heq. cbn [fst snd] in Heq.
      injection Heq as Hl Hh Hc.
      assert (Hkhi : (hi < k)%nat).
      { destruct (Nat.le_gt_cases k hi) as [Hkle | Hkgt].
        - exfalso. rewrite (Hmono k hi Hkle Htk) in Ehi. discriminate Ehi.
        - exact Hkgt. }
      rewrite <- Hl, <- Hh, <- Hc.
      split; [lia |].
      split.
      * apply (Hmono k (hi + 2 * (hi - lo))%nat); [lia | exact Htk].
      * split; [exact Ehi | lia].
  - rewrite mixb_gallop_S in Heq. destruct (test hi) eqn:Ehi.
    + injection Heq; intros; subst.
      split; [lia |]. split; [exact Ehi |]. split; [exact Hlo | lia].
    + destruct (mixb_gallop test (Datatypes.S f) hi (hi + 2 * (hi - lo))%nat)
        as [[l2 h2] c2] eqn:Eg2.
      cbv zeta in Heq. cbn [fst snd] in Heq.
      injection Heq as Hl Hh Hc.
      assert (Hlt2 : (hi < hi + 2 * (hi - lo))%nat) by lia.
      assert (Hr2 : (k <= (hi + 2 * (hi - lo))
                       + ((hi + 2 * (hi - lo)) - hi) * 2 ^ f)%nat).
      { replace (2 ^ Datatypes.S f)%nat with (2 * 2 ^ f)%nat in Hreach
          by (cbn [Nat.pow]; lia).
        lia. }
      pose proof (IH k hi (hi + 2 * (hi - lo))%nat l2 h2 c2
                    Hmono Hlt2 Ehi Htk Hmin Hr2 Eg2) as Hacc.
      rewrite <- Hl, <- Hh, <- Hc.
      destruct Hacc as [H1 [H2 [H3 H4]]].
      split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 | lia].
Qed.

(* 二分可靠+最小账：test lo=false、test hi=true、宽 ≤ 2^fuel 配给下       *)
(* 返回恰为最小通过站 k（k 的夹逼由单调性+最小性导出）                    *)
Lemma mixb_bsearch_account : forall (test : nat -> bool) (f k lo hi r c : nat),
  mixb_mono test -> (lo < hi)%nat -> test lo = false -> test hi = true ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (hi - lo <= 2 ^ f)%nat ->
  mixb_bsearch test f lo hi = (r, c) ->
  (r = k /\ c <= Datatypes.S f)%nat.
Proof.
  intros test f. induction f as [| f IH]; intros k lo hi r c
    Hmono Hlt Hlo Hhi Htk Hmin Hw Heq.
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    cbn [Nat.pow] in Hw. cbn [mixb_bsearch] in Heq.
    injection Heq; intros; subst.
    split; [lia | lia].
  - assert (Hklo : (lo < k)%nat).
    { destruct (Nat.le_gt_cases k lo) as [Hc | Hc].
      - exfalso. rewrite (Hmono k lo Hc Htk) in Hlo. discriminate Hlo.
      - exact Hc. }
    assert (Hkhi : (k <= hi)%nat).
    { destruct (Nat.le_gt_cases k hi) as [Hc | Hc].
      - exact Hc.
      - exfalso. rewrite (Hmin hi Hc) in Hhi. discriminate Hhi. }
    assert (H2 : (2 <> 0)%nat) by lia.
    pose proof (Nat.div_mod (lo + hi)%nat 2%nat H2) as Hdm.
    pose proof (Nat.mod_upper_bound (lo + hi)%nat 2%nat H2) as Hm.
    rewrite mixb_bsearch_S in Heq.
    destruct (Nat.ltb lo (Nat.div2 (lo + hi)%nat)) eqn:Eltb.
    + assert (Hmidlo : (lo < Nat.div2 (lo + hi)%nat)%nat)
        by (apply Nat.ltb_lt; exact Eltb).
      assert (Hmidhi : (Nat.div2 (lo + hi)%nat < hi)%nat).
      { rewrite Nat.div2_div. lia. }
      assert (Hwd : (hi - lo <= 2 * 2 ^ f)%nat).
      { replace (2 ^ Datatypes.S f)%nat with (2 * 2 ^ f)%nat in Hw
          by (cbn [Nat.pow]; lia).
        lia. }
      destruct (test (Nat.div2 (lo + hi)%nat)) eqn:Emid.
      * assert (Hkmid : (k <= Nat.div2 (lo + hi)%nat)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exact Hc.
          - exfalso. rewrite (Hmin (Nat.div2 (lo + hi)%nat) Hc) in Emid.
            discriminate Emid. }
        assert (Hw2 : (Nat.div2 (lo + hi)%nat - lo <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (lo + Nat.div2 (hi - lo) - lo)%nat
            with (Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_le. exact Hwd. }
        destruct (mixb_bsearch test f lo (Nat.div2 (lo + hi)%nat))
          as [r1 c1] eqn:E1.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k lo (Nat.div2 (lo + hi)%nat) r1 c1
                    Hmono Hmidlo Hlo Emid Htk Hmin Hw2 E1) as [Hr1 Hc1].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr1 | lia].
      * assert (Hmidk : (Nat.div2 (lo + hi)%nat < k)%nat).
        { destruct (Nat.le_gt_cases k (Nat.div2 (lo + hi)%nat)) as [Hc | Hc].
          - exfalso. rewrite (Hmono k (Nat.div2 (lo + hi)%nat) Hc Htk) in Emid.
            discriminate Emid.
          - exact Hc. }
        assert (Hw2 : (hi - Nat.div2 (lo + hi)%nat <= 2 ^ f)%nat).
        { assert (Hsh : (Nat.div2 (lo + hi)%nat = lo + Nat.div2 (hi - lo)%nat)%nat).
          { replace (lo + hi)%nat with (2 * lo + (hi - lo))%nat by lia.
            apply mixb_div2_shift. }
          rewrite Hsh.
          replace (hi - (lo + Nat.div2 (hi - lo)))%nat
            with ((hi - lo) - Nat.div2 (hi - lo))%nat by lia.
          apply mixb_div2_split. exact Hwd. }
        destruct (mixb_bsearch test f (Nat.div2 (lo + hi)%nat) hi)
          as [r2 c2] eqn:E2.
        cbv zeta in Heq. cbn [fst snd] in Heq.
        injection Heq as Eqr Eqc.
        destruct (IH k (Nat.div2 (lo + hi)%nat) hi r2 c2
                    Hmono Hmidhi Emid Hhi Htk Hmin Hw2 E2) as [Hr2 Hc2].
        rewrite <- Eqr, <- Eqc.
        split; [exact Hr2 | lia].
    + assert (Hmle : (Nat.div2 (lo + hi)%nat <= lo)%nat)
        by (apply Nat.ltb_ge; exact Eltb).
      rewrite Nat.div2_div in Hmle.
      assert (Hheq : (hi = lo + 1)%nat) by lia.
      cbn [fst snd] in Heq. injection Heq; intros; subst.
      split; [lia | lia].
Qed.

(* ★ 量级定理（机器可陈述 nat 上界式）：fuel 双相 S(S(log2 K)) 配给下，    *)
(*   选择器返回恰为可判定谓词的最小通过站，且谓词求值次数 ≤ 2·log2K+5。    *)
Theorem mixb_sel_scale : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false ->
  test k = true -> (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k -> k <= K -> 2 <= K ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  r = k /\ c <= 2 * (Nat.log2 K) + 5)%nat.
Proof.
  intros test K k r c Hmono H0 Htk Hmin Hk1 HkK HK2 Hsel.
  pose proof (Nat.log2_spec K) as Hspec.
  assert (HK0 : (0 < K)%nat) by lia.
  specialize (Hspec HK0).
  assert (Hlt01 : (0 < 1)%nat) by exact (Nat.lt_0_succ 0).
  destruct (mixb_gallop test (Datatypes.S (Datatypes.S (Nat.log2 K))) 0%nat 1%nat)
    as [[l h] c1] eqn:Eg.
  destruct (mixb_bsearch test (Datatypes.S (Datatypes.S (Nat.log2 K))) l h)
    as [r2 c2] eqn:Eb.
  assert (Hselc : mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r2, (c1 + c2)%nat))
    by exact (mixb_sel_eq test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                (Datatypes.S (Datatypes.S (Nat.log2 K))) l h c1 r2 c2 Eg Eb).
  rewrite Hselc in Hsel. injection Hsel; intros; subst.
  assert (Hreach : (k <= 1 + (1 - 0) * 2 ^ (Datatypes.S (Nat.log2 K)))%nat).
  { replace (2 ^ Datatypes.S (Nat.log2 K))%nat
      with (2 * 2 ^ Nat.log2 K)%nat by (cbn [Nat.pow]; lia).
    destruct Hspec as [_ Hup]. cbn [Nat.pow] in Hup. lia. }
  pose proof (mixb_gallop_account test (Datatypes.S (Nat.log2 K)) k 0%nat 1%nat
                l h c1 Hmono Hlt01 H0 Htk Hmin Hreach Eg) as Hgl.
  destruct Hgl as [Hgl1 [Hgl2 [Hgl3 Hgl4]]].
  pose proof (mixb_gallop_width_le test (Datatypes.S (Nat.log2 K)) 0%nat 1%nat
                l h c1 Hlt01 Eg) as Hwd.
  replace (1 - 0)%nat with 1%nat in Hwd by lia.
  replace (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)) * 1)%nat
    with (2 ^ Datatypes.S (Datatypes.S (Nat.log2 K)))%nat in Hwd by lia.
  pose proof (mixb_bsearch_account test (Datatypes.S (Datatypes.S (Nat.log2 K)))
                k l h r c2 Hmono Hgl1 Hgl3 Hgl2 Htk Hmin Hwd Eb) as Hbs.
  destruct Hbs as [Hbs1 Hbs2].
  split; [exact Hbs1 | lia].
Qed.

(* ============================================================ *)
(* Part 4：Real 归约壳——const 桥、μ 提取、幂桥、窗口、回传链              *)
(* ============================================================ *)

(* const-const 严格下钻：real_lt(const a)(const b) ⟹ Qlt a b *)
Lemma mixb_const_lt_to_Qlt : forall a b : Q,
  real_lt (real_const a) (real_const b) -> Qlt a b.
Proof.
  intros a b Hlt. destruct Hlt as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
  apply QltT_to_Qlt in HN.
  cbn [projT1 real_const] in HN.
  lra.
Qed.

(* const-const 上抬：Qlt a b ⟹ real_lt(const a)(const b) *)
Lemma mixb_Qlt_const_lt : forall a b : Q,
  Qlt a b -> real_lt (real_const a) (real_const b).
Proof.
  intros a b Hlt.
  exists ((b - a) * (1 # 2))%Q. split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b - a) (1 # 2)).
    + exact (proj1 (Qlt_minus_iff a b) Hlt).
    + exact mixb_q_12_pos.
  - exists 0%nat. intros n _. cbn [projT1 real_const].
    apply Qlt_to_QltT. apply mixb_qhalf_lt.
    exact (proj1 (Qlt_minus_iff a b) Hlt).
Qed.

(* const 保序：Qle ⟹ real_le（Or 双支） *)
Lemma mixb_qle_const_le : forall a b : Q,
  Qle a b -> real_le (real_const a) (real_const b).
Proof.
  intros a b H.
  assert (Eab : Qle_bool a b = true) by exact (proj2 (Qle_bool_iff a b) H).
  unfold real_le. destruct (Qle_bool b a) eqn:Eb.
  - right. intros eps Heps. exists 0%nat. intros n _. cbn [projT1 real_const].
    apply Qlt_to_QltT. apply QltT_to_Qlt in Heps.
    pose proof (proj1 (Qle_bool_iff b a) Eb) as Hba.
    apply (Qabs_case (a - b) (fun x => Qlt x eps)).
    + intro Hx0. assert (Hq : (Qabs (a - b))%Q == (a - b)%Q)
        by (apply Qabs_pos; exact Hx0). lra.
    + intro Hx0. assert (Hq : (Qabs (a - b))%Q == (- (a - b))%Q)
        by (apply Qabs_neg; exact Hx0). lra.
  - left. apply mixb_Qlt_const_lt.
    assert (Hn : ~ (b <= a)).
    { intro Hc. assert (Ht : Qle_bool b a = true)
        by exact (proj2 (Qle_bool_iff b a) Hc).
      congruence. }
    assert (Hab : a <= b) by exact (proj1 (Qle_bool_iff a b) Eab).
    lra.
Qed.

(* const 恒等下钻：real_eq(const a)(const b) ⟹ a == b（Qeq_dec 双支反证） *)
Lemma mixb_const_eq_to_Qeq : forall a b : Q,
  real_eq (real_const a) (real_const b) -> a == b.
Proof.
  intros a b He.
  destruct (Qeq_dec a b) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    destruct (Qle_bool a b) eqn:Eab.
    + pose proof (proj1 (Qle_bool_iff a b) Eab) as Hab.
      assert (Hlt : Qlt a b).
      { destruct (Qle_lt_or_eq a b Hab) as [Hx | Hx];
          [exact Hx | exfalso; apply Hneq; exact Hx]. }
      pose proof (He (b - a)%Q
                    (Qlt_to_QltT 0 (b - a) (proj1 (Qlt_minus_iff a b) Hlt))) as HN.
      destruct HN as [N HN]. specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
      cbn [projT1 real_const] in HN. apply QltT_to_Qlt in HN.
      apply (Qabs_case (a - b) (fun x => False)).
      * intro Hx0. assert (Hq : (Qabs (a - b))%Q == (a - b)%Q)
          by (apply Qabs_pos; exact Hx0).
        assert (Ha0 : a - b <= 0) by lra.
        lra.
      * intro Hx0. assert (Hq : (Qabs (a - b))%Q == (- (a - b))%Q)
          by (apply Qabs_neg; exact Hx0).
        lra.
    + assert (Hba : Qlt b a).
      { assert (Hn : ~ (a <= b)).
        { intro Hc. assert (Ht : Qle_bool a b = true)
            by exact (proj2 (Qle_bool_iff a b) Hc).
          congruence. }
        lra. }
      pose proof (He (a - b)%Q
                    (Qlt_to_QltT 0 (a - b) (proj1 (Qlt_minus_iff b a) Hba))) as HN.
      destruct HN as [N HN]. specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
      cbn [projT1 real_const] in HN. apply QltT_to_Qlt in HN.
      apply (Qabs_case (a - b) (fun x => False)).
      * intro Hx0. assert (Hq : (Qabs (a - b))%Q == (a - b)%Q)
          by (apply Qabs_pos; exact Hx0).
        lra.
      * intro Hx0. assert (Hq : (Qabs (a - b))%Q == (- (a - b))%Q)
          by (apply Qabs_neg; exact Hx0).
        assert (Hab0 : 0 <= a - b) by lra.
        lra.
Qed.

(* const 保序下钻：real_le(const a)(const b) ⟹ Qle a b *)
Lemma mixb_const_le_to_Qle : forall a b : Q,
  real_le (real_const a) (real_const b) -> Qle a b.
Proof.
  intros a b H. unfold real_le in H. destruct H as [Hlt | Heq].
  - apply Qlt_le_weak. exact (mixb_const_lt_to_Qlt a b Hlt).
  - apply qeq_le. exact (mixb_const_eq_to_Qeq a b Heq).
Qed.

(* const 分配：const(a·b) == const a·const b（real_eq_of_zero_diff 口径） *)
Lemma mixb_const_mult : forall a b : Q,
  real_eq (real_const (a * b)) (real_mult (real_const a) (real_const b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_const real_mult] in *. ring.
Qed.

(* const 幂恒等：tv_rpow(const q) m == const(igr_qpow q m)（幂形归一桥） *)
Lemma mixb_const_rpow_eq : forall (q : Q) (m : nat),
  real_eq (tv_rpow (real_const q) m) (real_const (igr_qpow q m)).
Proof.
  intros q m. induction m as [| m IH].
  - apply real_eq_of_zero_diff. intro n0.
    cbn [tv_rpow igr_qpow projT1 real_one real_const] in *. ring.
  - cbn [tv_rpow igr_qpow].
    apply (real_eq_trans _ (real_mult (real_const q) (real_const (igr_qpow q m)))).
    + apply (RealSetoid.real_eq_mult_compat (real_const q) (tv_rpow (real_const q) m)
               (real_const q) (real_const (igr_qpow q m))
               (real_eq_refl _) IH).
    + apply (real_eq_sym _ _). exact (mixb_const_mult q (igr_qpow q m)).
Qed.

Lemma mixb_zero_const_eq : real_eq real_zero (real_const 0).
Proof.
  apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_zero real_const] in *. ring.
Qed.

(* 幂正（Real 侧 tv_rpow 一次性归纳） *)
Lemma mixb_rpow_pos : forall (a : Real) (k : nat),
  real_lt real_zero a -> real_lt real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - cbn [tv_rpow]. exact real_lt_zero_one.
  - cbn [tv_rpow]. exact (real_mult_pos_compat a (tv_rpow a k) Ha IH).
Qed.

(* 幂换底单调（Real 侧归纳桥：双正 + κ ≤ κ0 ⟹ κ^k ≤ κ0^k） *)
Lemma mixb_rpow_le : forall (x y : Real) (k : nat),
  real_lt real_zero x -> real_le x y -> real_lt real_zero y ->
  real_le (tv_rpow x k) (tv_rpow y k).
Proof.
  intros x y k Hx0 Hxy Hy0. induction k as [| k IH].
  - apply (RealSetoid.real_eq_le). apply (real_eq_refl real_one).
  - cbn [tv_rpow].
    apply (real_le_trans _ (real_mult y (tv_rpow x k))).
    + apply (real_le_mult_compat x y (tv_rpow x k) (mixb_rpow_pos x k Hx0) Hxy).
    + apply (real_le_trans _ (real_mult (tv_rpow x k) y)).
      * apply (RealSetoid.real_eq_le). exact (real_mult_comm y (tv_rpow x k)).
      * apply (real_le_trans _ (real_mult (tv_rpow y k) y)).
        -- apply (real_le_mult_compat (tv_rpow x k) (tv_rpow y k) y Hy0 IH).
        -- apply (RealSetoid.real_eq_le). exact (real_mult_comm (tv_rpow y k) y).
Qed.

(* —— μ 提取：μ := min(eps/2, 1/2)（Qle_bool 双支，Defined 可计算） —— *)
Definition mixb_mu (eps : Q) : Q :=
  if Qle_bool (eps * (1 # 2)) (1 # 2) then eps * (1 # 2) else (1 # 2).

Lemma mixb_mu_pos : forall eps : Q, 0 < eps -> 0 < mixb_mu eps.
Proof.
  intros eps Heps. unfold mixb_mu.
  destruct (Qle_bool (eps * (1 # 2)) (1 # 2)).
  - apply (Qmult_lt_0_compat eps (1 # 2)); [exact Heps | exact mixb_q_12_pos].
  - exact mixb_q_12_pos.
Qed.

Lemma mixb_mu_le_half : forall eps : Q, mixb_mu eps <= (1 # 2).
Proof.
  intro eps. unfold mixb_mu.
  destruct (Qle_bool (eps * (1 # 2)) (1 # 2)) eqn:Eb.
  - exact (proj1 (Qle_bool_iff (eps * (1 # 2)) (1 # 2)) Eb).
  - apply Qle_refl.
Qed.

Lemma mixb_mu_le : forall eps : Q, mixb_mu eps <= eps * (1 # 2).
Proof.
  intro eps. unfold mixb_mu.
  destruct (Qle_bool (eps * (1 # 2)) (1 # 2)) eqn:EB.
  - apply Qle_refl.
  - assert (Hn : ~ (eps * (1 # 2) <= (1 # 2))).
    { intro Hc. assert (Ht : Qle_bool (eps * (1 # 2)) (1 # 2) = true)
        by exact (proj2 (Qle_bool_iff (eps * (1 # 2)) (1 # 2)) Hc).
      congruence. }
    lra.
Qed.

(* κ0 := 1 − μ 双支范围账 *)
Lemma mixb_kappa0_pos : forall eps : Q, 0 < eps -> 0 < 1 - mixb_mu eps.
Proof.
  intros eps Heps.
  apply (proj1 (Qlt_minus_iff (mixb_mu eps) 1)).
  apply (Qle_lt_trans (mixb_mu eps) (1 # 2) 1).
  - apply mixb_mu_le_half.
  - exact mixb_q_12_lt.
Qed.

Lemma mixb_kappa0_lt_one : forall eps : Q, 0 < eps -> 1 - mixb_mu eps < 1.
Proof.
  intros eps Heps.
  apply (proj2 (Qlt_minus_iff (1 - mixb_mu eps) 1)).
  pose proof (mixb_mu_pos eps Heps). lra.
Qed.

(* κ0 提取桥：real_lt κ 1 的 sigT 证书 ⟹ real_lt κ (const κ0)（gap := μ） *)
Lemma mixb_kappa0_bridge : forall (kappa : Real) (eps : Q) (N : nat),
  QltT 0 eps ->
  (forall n : nat, NatLe N n -> QltT eps (projT1 real_one n - projT1 kappa n)) ->
  real_lt kappa (real_const (1 - mixb_mu eps)).
Proof.
  intros kappa eps N Heps HN.
  exists (mixb_mu eps). split.
  - apply Qlt_to_QltT. exact (mixb_mu_pos eps (QltT_to_Qlt 0 eps Heps)).
  - exists N. intros n Hn.
    specialize (HN n Hn). apply QltT_to_Qlt in HN.
    cbn [projT1 real_one] in HN.
    cbn [projT1 real_const].
    apply Qlt_to_QltT.
    pose proof (mixb_mu_le eps) as Hmle.
    pose proof (mixb_mu_pos eps (QltT_to_Qlt 0 eps Heps)) as Hmpos.
    lra.
Qed.

(* b0 := eps_b/2 提取桥：real_lt 0 budget 证书 ⟹ real_lt (const b0) budget *)
Lemma mixb_b0_bridge : forall (budget : Real) (eps : Q) (N : nat),
  QltT 0 eps ->
  (forall n : nat, NatLe N n -> QltT eps (projT1 budget n - projT1 real_zero n)) ->
  real_lt (real_const (eps * (1 # 2))) budget.
Proof.
  intros budget eps N Heps HN.
  exists (eps * (1 # 2))%Q. split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps (1 # 2)).
    + exact (QltT_to_Qlt 0 eps Heps).
    + exact mixb_q_12_pos.
  - exists N. intros n Hn. specialize (HN n Hn).
    cbn [projT1 real_zero] in HN.
    cbn [projT1 real_const].
    apply Qlt_to_QltT. apply QltT_to_Qlt in HN.
    lra.
Qed.

(* 0 ≤ TV0′ 桥（TV0 非负 + 上界证书 ⟹ 证书值非负） *)
Lemma mixb_v_nonneg : forall (TV0 : Real) (v : Q),
  real_le real_zero TV0 -> real_le TV0 (real_const v) -> 0 <= v.
Proof.
  intros TV0 v Ha Hc. apply (mixb_const_le_to_Qle 0 v).
  apply (real_le_trans (real_const 0) real_zero (real_const v)).
  - apply (RealSetoid.real_eq_le). exact mixb_zero_const_eq.
  - apply (real_le_trans real_zero TV0 (real_const v) Ha Hc).
Qed.

Lemma mixb_qpos_const_lt : forall q : Q, 0 < q -> real_lt real_zero (real_const q).
Proof.
  intros q Hq. exists (q * (1 # 2))%Q. split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat q (1 # 2)); [exact Hq | exact mixb_q_12_pos].
  - exists 0%nat. intros n _. cbn [projT1 real_const real_zero].
    apply Qlt_to_QltT. lra.
Qed.

(* Q 谓词上抬：test(k)=true ⟹ real_le(tv_rpow(const κ0) k · const v) (const b0) *)
Lemma mixb_qpow_test_le : forall (kappa0 v b0 : Q) (k : nat),
  Qle (igr_qpow kappa0 k * v) b0 ->
  real_le (real_mult (tv_rpow (real_const kappa0) k) (real_const v)) (real_const b0).
Proof.
  intros kappa0 v b0 k H.
  apply (real_le_trans _ (real_const (igr_qpow kappa0 k * v))).
  - apply (RealSetoid.real_eq_le).
    apply (real_eq_trans _ (real_mult (real_const (igr_qpow kappa0 k))
                             (real_const v))).
    + apply (RealSetoid.real_eq_mult_compat (tv_rpow (real_const kappa0) k)
               (real_const v) (real_const (igr_qpow kappa0 k)) (real_const v)
               (mixb_const_rpow_eq kappa0 k) (real_eq_refl _)).
    + apply (real_eq_sym _ _). exact (mixb_const_mult (igr_qpow kappa0 k) v).
  - apply mixb_qle_const_le. exact H.
Qed.

(* ★ 回传链（裁决 3 尾链）：test(k)=true（Q）⟹ κ^k·TV0 < budget（Real 严格） *)
Lemma mixb_real_chain : forall (kappa TV0 budget : Real) (kappa0 v b0 : Q) (k : nat),
  real_lt real_zero kappa -> real_le kappa (real_const kappa0) ->
  real_lt real_zero (real_const kappa0) ->
  real_le real_zero TV0 -> real_le TV0 (real_const v) ->
  real_lt (real_const b0) budget ->
  mixb_qtest kappa0 v b0 k = true ->
  real_lt (real_mult (tv_rpow kappa k) TV0) budget.
Proof.
  intros kappa TV0 budget kappa0 v b0 k Hk1 Hk0le Hc0pos Ha Htv Hbb Htest.
  assert (HQ : Qle (igr_qpow kappa0 k * v) b0).
  { unfold mixb_qtest in Htest. exact (proj1 (Qle_bool_iff _ _) Htest). }
  assert (Hstep1 : real_le (real_mult (tv_rpow kappa k) TV0)
                     (real_mult (tv_rpow (real_const kappa0) k) TV0)).
  { apply (real_le_mult_compat_weak (tv_rpow kappa k) (tv_rpow (real_const kappa0) k) TV0 Ha).
    apply (mixb_rpow_le kappa (real_const kappa0) k Hk1 Hk0le Hc0pos). }
  assert (Hstep2 : real_le (real_mult (tv_rpow (real_const kappa0) k) TV0)
                     (real_mult (tv_rpow (real_const kappa0) k) (real_const v))).
  { pose proof (real_le_mult_compat TV0 (real_const v) (tv_rpow (real_const kappa0) k)
                  (mixb_rpow_pos (real_const kappa0) k Hc0pos) Htv) as HT.
    apply (real_le_trans _ (real_mult TV0 (tv_rpow (real_const kappa0) k))).
    - apply (RealSetoid.real_eq_le). exact (real_mult_comm (tv_rpow (real_const kappa0) k) TV0).
    - apply (real_le_trans _ (real_mult (real_const v) (tv_rpow (real_const kappa0) k))).
      + exact HT.
      + apply (RealSetoid.real_eq_le).
        exact (real_mult_comm (real_const v) (tv_rpow (real_const kappa0) k)). }
  assert (Hstep3 : real_le (real_mult (tv_rpow (real_const kappa0) k) (real_const v))
                     (real_const b0))
    by exact (mixb_qpow_test_le kappa0 v b0 k HQ).
  apply (real_le_lt_trans _ (real_const b0)).
  - apply (real_le_trans _ (real_mult (tv_rpow (real_const kappa0) k) TV0)).
    + exact Hstep1.
    + exact (real_le_trans _ _ _ Hstep2 Hstep3).
  - exact Hbb.
Qed.

(* ============================================================ *)
(* Part 5：Q 引擎——mixb_qsel 与复合账（igr 三账复用：最小站扫描）          *)
(* ============================================================ *)

Lemma mixb_enum_le : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k -> (k <= t)%nat.
Proof.
  intros test t. induction t as [| m IH]; intros k Hk.
  - cbn [igr_k_enum] in Hk. destruct (test 0%nat).
    + injection Hk; intros; subst. lia.
    + discriminate Hk.
  - cbn [igr_k_enum] in Hk. destruct (igr_k_enum test m) eqn:Em.
    + injection Hk; intros; subst. specialize (IH _ eq_refl). lia.
    + destruct (test (Datatypes.S m)).
      * injection Hk; intros; subst. lia.
      * discriminate Hk.
Qed.

(* Q 引擎：fuel 由窗口 K 的 log2 配给（Defined，纯 Q 判定） *)
Definition mixb_qsel (kappa0 v b0 : Q) (K : nat) : (nat * nat)%type :=
  mixb_sel (mixb_qtest kappa0 v b0)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))).

(* 复合账：窗口存在过站 + test 0 败 ⟹ 返回站过、以下全败、计数对数级 *)
Lemma mixb_qsel_account_ex : forall (kappa0 v b0 : Q) (K r c : nat),
  0 < kappa0 -> kappa0 < 1 -> 0 <= v -> (2 <= K)%nat ->
  (exists k : nat, (k <= K)%nat /\ mixb_qtest kappa0 v b0 k = true) ->
  mixb_qtest kappa0 v b0 0%nat = false ->
  mixb_qsel kappa0 v b0 K = (r, c) ->
  mixb_qtest kappa0 v b0 r = true /\
  (forall j : nat, (j < r)%nat -> mixb_qtest kappa0 v b0 j = false) /\
  (c <= 2 * (Nat.log2 K) + 5)%nat.
Proof.
  intros kappa0 v b0 K r c Hk0 Hk1 Hv0 HK2 Hhit H0 Hsel.
  destruct Hhit as [k0 [Hk0K Hk0pass]].
  destruct (igr_k_enum (mixb_qtest kappa0 v b0) K) as [kmin|] eqn:Eenum.
  - pose proof (igr_k_enum_sound _ _ _ Eenum) as Hpass.
    pose proof (igr_k_enum_min _ _ _ Eenum) as Hmin.
    pose proof (mixb_enum_le _ _ _ Eenum) as HminK.
    assert (Hkmin1 : (1 <= kmin)%nat).
    { destruct kmin as [| m]; [rewrite H0 in Hpass; discriminate Hpass | lia]. }
    destruct (mixb_sel_scale (mixb_qtest kappa0 v b0) K kmin r c
                (mixb_qtest_mono kappa0 v b0 Hk0 (Qlt_le_weak kappa0 1 Hk1) Hv0)
                H0 Hpass Hmin Hkmin1 HminK HK2 Hsel) as [Hr Hc].
    split.
    + rewrite Hr. exact Hpass.
    + split.
      * intros j Hj. apply Hmin. rewrite Hr in Hj. exact Hj.
      * exact Hc.
  - exfalso.
    pose proof (igr_k_enum_none _ _ Eenum k0 Hk0K) as HF.
    rewrite Hk0pass in HF. discriminate HF.
Qed.

(* ============================================================ *)
(* Part 6：主件——mixb_k_select_log（Defined sigT）+ le 形 + 审计口        *)
(* ============================================================ *)

Definition mixb_k_select_log (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget)
  (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct Hk2 as [epsK [HepsK [NK HNK]]].
  destruct Hb as [epsB [HepsB [NB HNB]]].
  destruct Htv as [v Hvc].
  assert (Hk0 : 0 < 1 - mixb_mu epsK)
    by (apply mixb_kappa0_pos; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hk0lt : 1 - mixb_mu epsK < 1)
    by (apply mixb_kappa0_lt_one; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hb0 : 0 < epsB * (1 # 2)).
  { apply (Qmult_lt_0_compat epsB (1 # 2)).
    - exact (QltT_to_Qlt 0 epsB HepsB).
    - exact mixb_q_12_pos. }
  assert (Hk0le : real_le kappa (real_const (1 - mixb_mu epsK))).
  { apply (RealSetoid.real_lt_le_iff_req). left.
    exact (mixb_kappa0_bridge kappa epsK NK HepsK HNK). }
  assert (Hc0pos : real_lt real_zero (real_const (1 - mixb_mu epsK)))
    by exact (mixb_qpos_const_lt _ Hk0).
  assert (Hbb : real_lt (real_const (epsB * (1 # 2))) budget)
    by exact (mixb_b0_bridge budget epsB NB HepsB HNB).
  assert (Hv0 : 0 <= v) by exact (mixb_v_nonneg TV0 v Ha Hvc).
  destruct (mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) 0%nat) eqn:Hq0.
  - (* k := 0：TV0′ ≤ b0 已达标 *)
    exists 0%nat.
    exact (mixb_real_chain kappa TV0 budget (1 - mixb_mu epsK) v (epsB * (1 # 2)) 0%nat
             Hk1 Hk0le Hc0pos Ha Hvc Hbb Hq0).
  - (* 倍增+二分：real_arch 兜底窗口（裁决 1(b)），Q 引擎精确定位 *)
    pose (k0 := (1 - mixb_mu epsK)%Q).
    pose (wb := ((1 - k0) * (epsB * (1 # 2)))%Q).
    assert (Hwbpos : 0 < wb).
    { pose proof (mixb_mu_pos epsK (QltT_to_Qlt 0 epsK HepsK)) as Hmu.
      unfold wb, k0.
      apply (Qmult_lt_0_compat (1 - (1 - mixb_mu epsK)) (epsB * (1 # 2)));
        [lra | exact Hb0]. }
    assert (Hwbne : ~ (wb == 0)).
    { intro He. apply (Qlt_not_eq 0 wb Hwbpos). apply mixb_qeq_sym. exact He. }
    destruct (real_arch (real_const (v * Qinv wb))) as [nA Hpair].
    destruct Hpair as [Hnge2 Harchlt].
    assert (Hqarch : Qlt (v * Qinv wb) (Z.of_nat nA # 1))
      by exact (mixb_const_lt_to_Qlt _ _ Harchlt).
    assert (Hwin : Qle v ((Z.of_nat nA # 1) * wb)).
    { apply Qlt_le_weak.
      apply (Qle_lt_trans v ((v * Qinv wb) * wb) ((Z.of_nat nA # 1) * wb)).
      - apply qeq_le. apply mixb_qeq_sym.
        exact (mixb_qmul_inv_cancel v wb Hwbpos).
      - exact (Qmult_lt_compat_r (v * Qinv wb) (Z.of_nat nA # 1) wb Hwbpos Hqarch). }
    assert (HpassnA : mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA = true).
    { apply (mixb_window_test_true (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA
               Hk0 Hk0lt Hv0 Hb0); [lia | exact Hwin]. }
    destruct (mixb_qsel (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA) as [r c] eqn:Hsel.
    destruct (mixb_qsel_account_ex (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA r c
                Hk0 Hk0lt Hv0 Hnge2
                (ex_intro _ nA (conj (Nat.le_refl nA) HpassnA)) Hq0 Hsel)
      as [Hrpass [Hrmin Hcnt]].
    exists r.
    exact (mixb_real_chain kappa TV0 budget (1 - mixb_mu epsK) v (epsB * (1 # 2)) r
             Hk1 Hk0le Hc0pos Ha Hvc Hbb Hrpass).
Defined.

Definition mixb_k_select_log_le (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget)
  (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
  : sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct (mixb_k_select_log kappa TV0 budget Hk1 Hk2 Ha Hb Htv) as [k Hk].
  exists k. apply (RealSetoid.real_lt_le_iff_req). left. exact Hk.
Defined.

(* ============================================================ *)
(* G4 审计口（全 Closed 预期）                                           *)
(* ============================================================ *)

Print Assumptions mixb_k_select_log.
Print Assumptions mixb_k_select_log_le.
Print Assumptions mixb_sel_scale.
Print Assumptions mixb_sel_count.
Print Assumptions mixb_qsel_account_ex.
