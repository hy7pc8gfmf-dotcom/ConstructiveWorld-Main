(* ===================================================================== *)
(*  zb3z_base42.v —— [16,42] 段 Z 换岸 born：C 值序界 [1,42] 全段闭合        *)
(*  （DM-Z3N2·承 DM-Z3N 探形配方／DM-Z3J base15 正本）             *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    将 M2′ 已证段自 [1,15]（zb3j_base15）扩张至 [1,42]：比较面整体渡 Z，  *)
(*    3^n 免 nat 一元物化（①定义面 n≥10／②nat 比较面 n≥19 两面真墙的      *)
(*    双绕行——Z 侧二进制 65 位即时）。三段机械件全池内全称件零重述：       *)
(*      · 步进机 zb2gb_C_step（gapB）：C(n)·G(n,n) = n·C(n−1)；           *)
(*      · 折返 zb3m_G_ext＋zb3m_a4_gt42：G(42,42) 折回四因子截断面；       *)
(*      · C(15) 值与 [1,15] 段直取 zb3j_C_vals_11_15／zb3j_base15。        *)
(*    块化 10 块逐块累积（切点=Z3N 对照比值曲线谷点配方）：                 *)
(*      [16][17,18][19,22][23,24][25,28][29,30][31,34][35,36][37,40][41,42] *)
(*    每块 born 绿判：块内逐点累积恒等式（链节 gear）＋逐点换岸比较（Z 桥）  *)
(*    ＋逐点拆封（mul_le_mono_pos_l）。验收锚：C(41) 因子化 Z-lift 再验。   *)
(*  依赖：                                                            *)
(*    缓存根 HansonLcm Hanson3Pow S01_BaseRing S02_CauchyComplete；池内    *)
(*    abl_z2_dub3、abl_z2_valbridge、u5c_zeta2_gapB、u5c_z3_m2p_ledger、    *)
(*    zb3j_base15（C(15) 值链正本＋[1,15] 段正本）。                       *)
(*  构造性注记：                                                      *)
(*    零假设声明、零承认、零经典逻辑；比较面 vm_compute 仅用于 Z 侧闭式    *)
(*    计算（二进制即时·nat 侧零一元物化——照 B4 判例与红线 3 实质律申报）。 *)
(*    诚实接口：Separate Extraction 落 .ml（NatLe 承载出口·与 zb3j 同款    *)
(*    闭式透明体；z2v_C 直算仍撞 fact 一元墙·判定义务由 Prop 链式累积＋Z  *)
(*    比较面承担）。                                                      *)
(*  编译配方：                                                        *)
(*    source Live/toolchain/env.sh；cpu_guard v3 包裹单飞；                *)
(*    cd 池 && rocq c -native-compiler no -q -Q . "" zb3z_base42.v         *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.ZArith Arith.Arith Arith.PeanoNat Lia.
From Stdlib Require Import Arith.Factorial.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import abl_z2_dub3.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.
Require Import u5c_z3_m2p_ledger.
Require Import zb3j_base15.

(* 本件全 nat 层（C 链与累积恒等式）——照 zb3j_base15 正本头部同款关 Q 作用域， *)
(* 防 Qmult 传染（Z3I 坑位·Z3P c1 红发实录）。                                *)
Close Scope Q_scope.

(* ============================================================ *)
(* §0 Z 换岸三件正典形（Nat2Z.inj_le／inj_mul／inj_pow·Set 承载比较面渡 Z）  *)
(*    Z3N 探形 probe1-A／probe2 born 绿判配方的池内正典化。                 *)
(* ============================================================ *)

(* 件一·比较渡岸（inj_le 承载）：nat 序界 ⟺ Z 布尔判定（双向正典形）*)
Lemma zb3z_Zcmp : forall a b : nat,
  (a <= b)%nat <-> (Z.of_nat a <=? Z.of_nat b)%Z = true.
Proof.
  intros a b. split.
  - intros Hn. apply Z.leb_le.
    exact (proj1 (Nat2Z.inj_le a b) Hn).
  - intros Hz. apply (proj2 (Nat2Z.inj_le a b)).
    apply Z.leb_le. exact Hz.
Qed.

(* 件二·乘法渡岸（inj_mul）：免 nat 侧物化大积 *)
Lemma zb3z_inj_mul : forall a b : nat,
  Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z.
Proof. intros a b. apply Nat2Z.inj_mul. Qed.

(* 件三·幂渡岸（inj_pow）：3^n 免 nat 物化过岸的关键件 *)
Lemma zb3z_inj_pow : forall a b : nat,
  Z.of_nat (a ^ b) = (Z.of_nat a ^ Z.of_nat b)%Z.
Proof. intros a b. apply Nat2Z.inj_pow. Qed.

(* 换岸比较面通用壳（各块 Hcmp 共用）：后向渡岸（probe1-A 原配方语义）*)
Ltac zb3z_Zcmp_tac :=
  apply (proj2 (zb3z_Zcmp _ _)); repeat rewrite zb3z_inj_mul;
  rewrite zb3z_inj_pow; vm_compute; reflexivity.

(* 验收锚：C(41) = 1.84e19 因子化 ≤ 3^41 Z-lift 秒级（Z3N probe1-A 判例再验）*)
Lemma zb3z_anchor41 : (3456 * 3675 * 2431 * 437 * 899 * 1517 <= 3 ^ 41)%nat.
Proof. zb3z_Zcmp_tac. Qed.

(* ============================================================ *)
(* §1 对角增值积 16..42 档折返值（zb3m_G_ext 折回四因子截断面·每点一式）    *)
(* ============================================================ *)

Lemma z3z_G16 : z2gb_G 16 16 = 8.
Proof.
  rewrite (zb3m_G_ext 16 4 16 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G17 : z2gb_G 17 17 = 1.
Proof.
  rewrite (zb3m_G_ext 17 4 17 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G18 : z2gb_G 18 18 = 54.
Proof.
  rewrite (zb3m_G_ext 18 4 18 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G19 : z2gb_G 19 19 = 1.
Proof.
  rewrite (zb3m_G_ext 19 4 19 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G20 : z2gb_G 20 20 = 10.
Proof.
  rewrite (zb3m_G_ext 20 4 20 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G21 : z2gb_G 21 21 = 21.
Proof.
  rewrite (zb3m_G_ext 21 4 21 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G22 : z2gb_G 22 22 = 11.
Proof.
  rewrite (zb3m_G_ext 22 4 22 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G23 : z2gb_G 23 23 = 1.
Proof.
  rewrite (zb3m_G_ext 23 4 23 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G24 : z2gb_G 24 24 = 96.
Proof.
  rewrite (zb3m_G_ext 24 4 24 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G25 : z2gb_G 25 25 = 1.
Proof.
  rewrite (zb3m_G_ext 25 4 25 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G26 : z2gb_G 26 26 = 13.
Proof.
  rewrite (zb3m_G_ext 26 4 26 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G27 : z2gb_G 27 27 = 9.
Proof.
  rewrite (zb3m_G_ext 27 4 27 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G28 : z2gb_G 28 28 = 56.
Proof.
  rewrite (zb3m_G_ext 28 4 28 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G29 : z2gb_G 29 29 = 1.
Proof.
  rewrite (zb3m_G_ext 29 4 29 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G30 : z2gb_G 30 30 = 150.
Proof.
  rewrite (zb3m_G_ext 30 4 30 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G31 : z2gb_G 31 31 = 1.
Proof.
  rewrite (zb3m_G_ext 31 4 31 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G32 : z2gb_G 32 32 = 16.
Proof.
  rewrite (zb3m_G_ext 32 4 32 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G33 : z2gb_G 33 33 = 11.
Proof.
  rewrite (zb3m_G_ext 33 4 33 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G34 : z2gb_G 34 34 = 17.
Proof.
  rewrite (zb3m_G_ext 34 4 34 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G35 : z2gb_G 35 35 = 5.
Proof.
  rewrite (zb3m_G_ext 35 4 35 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G36 : z2gb_G 36 36 = 216.
Proof.
  rewrite (zb3m_G_ext 36 4 36 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G37 : z2gb_G 37 37 = 1.
Proof.
  rewrite (zb3m_G_ext 37 4 37 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G38 : z2gb_G 38 38 = 19.
Proof.
  rewrite (zb3m_G_ext 38 4 38 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G39 : z2gb_G 39 39 = 13.
Proof.
  rewrite (zb3m_G_ext 39 4 39 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G40 : z2gb_G 40 40 = 20.
Proof.
  rewrite (zb3m_G_ext 40 4 40 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G41 : z2gb_G 41 41 = 1.
Proof.
  rewrite (zb3m_G_ext 41 4 41 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

Lemma z3z_G42 : z2gb_G 42 42 = 1764.
Proof.
  rewrite (zb3m_G_ext 42 4 42 ltac:(lia) ltac:(lia)
             ltac:(pose proof zb3m_a4_gt42; lia)).
  reflexivity.
Qed.

(* ============================================================ *)
(* §2 链节机械件：累积恒等式＋正性＋拆封比较（全符号·零一元物化）           *)
(* ============================================================ *)

(* 积正性（lia 原子域·零 vm）*)
Lemma zb3z_pos_mul : forall a b : nat,
  (0 < a)%nat -> (0 < b)%nat -> (0 < a * b)%nat.
Proof.
  intros a b Ha Hb.
  pose proof (proj1 (Nat.mul_le_mono_pos_l 1 b a ltac:(lia)) ltac:(lia)) as H1.
  pose proof (proj1 (Nat.mul_le_mono_pos_l 0 1 a Ha) ltac:(lia)) as H2.
  lia.
Qed.

(* 链节（累积恒等式的步进机齿轮）：已知至 n 档累积式与单步方程，得 n+1 档    *)
(* 累积式（左嵌积形）连带正性。 Algebra 面全显式实例 assoc/comm——防        *)
(* first-match 错位（Z3N probe2 红笔教训）。                               *)
Lemma zb3z_gear : forall n p g gm,
  (z2v_C (Datatypes.S n) * g = Datatypes.S n * z2v_C n)%nat ->
  (0 < g)%nat ->
  (z2v_C n * gm = p * (3 * (13 * (11 * 2520))))%nat ->
  (0 < gm)%nat ->
  (z2v_C (Datatypes.S n) * (gm * g) = (p * Datatypes.S n) * (3 * (13 * (11 * 2520))))%nat /\
  (0 < gm * g)%nat.
Proof.
  intros n p g gm E1 Hg E2 Hgm. split.
  - rewrite (Nat.mul_comm gm g).
    rewrite (Nat.mul_assoc (z2v_C (Datatypes.S n)) g gm).
    rewrite E1.
    rewrite <- (Nat.mul_assoc (Datatypes.S n) (z2v_C n) gm).
    rewrite E2.
    rewrite (Nat.mul_assoc (Datatypes.S n) p (3 * (13 * (11 * 2520)))).
    rewrite (Nat.mul_comm (Datatypes.S n) p).
    reflexivity.
  - apply zb3z_pos_mul; assumption.
Qed.

(* 拆封比较（Z 桥终站）：C(n)·g = p·C15f 与 p·C15f ≤ g·3^n（Z 侧已核）      *)
(*    ⟹ C(n) ≤ 3^n。乘数拆封回运 nat 侧（mul_le_mono_pos_l 取 proj2）。    *)
Lemma zb3z_link15 : forall n p g,
  (0 < g)%nat ->
  (z2v_C n * g = p * (3 * (13 * (11 * 2520))))%nat ->
  (p * (3 * (13 * (11 * 2520))) <= g * 3 ^ n)%nat ->
  (z2v_C n <= 3 ^ n)%nat.
Proof.
  intros n p g Hg Hid Hcmp.
  apply (proj2 (Nat.mul_le_mono_pos_l _ _ g ltac:(lia))).
  rewrite (Nat.mul_comm g (z2v_C n)). rewrite Hid. exact Hcmp.
Qed.

(* ============================================================ *)
(* §3 块化 10 块逐块累积（每块：块内逐点链节累积＋逐点换岸比较＋逐点拆封）   *)
(* ============================================================ *)

Lemma zb3z_blk1 :
  (z2v_C 16 <= 3 ^ 16)%nat /\
  ((z2v_C 16 * 8 = 16 * (3 * (13 * (11 * 2520))))%nat /\ (0 < 8)%nat).
Proof.
  destruct zb3j_C_vals_11_15 as (_ & _ & _ & _ & WF).
  pose proof (zb2gb_C_step 15 ltac:(lia)) as E16.
  rewrite z3z_G16 in E16. rewrite WF in E16.
  assert (Hc16 : (16 * (3 * (13 * (11 * 2520))) <= 8 * 3 ^ 16)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 16 16 8 ltac:(lia) E16 Hc16) as B16.
  assert (Hp16 : (0 < 8)%nat) by lia.
  exact (conj B16 (conj E16 Hp16)).
Qed.

Lemma zb3z_blk2 :
  (z2v_C 17 <= 3 ^ 17)%nat /\
  (z2v_C 18 <= 3 ^ 18)%nat /\
  ((z2v_C 18 * ((8 * 1) * 54) = ((16 * 17) * 18) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((8 * 1) * 54))%nat).
Proof.
  destruct zb3z_blk1 as (B16 & (I16 & Hp16)).
  pose proof (zb2gb_C_step 16 ltac:(lia)) as E17.
  rewrite z3z_G17 in E17.
  destruct (zb3z_gear 16 16 1 8 E17 ltac:(lia) I16 Hp16) as (I17 & Hp17).
  assert (Hc17 : ((16 * 17) * (3 * (13 * (11 * 2520))) <= (8 * 1) * 3 ^ 17)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 17 (16 * 17) (8 * 1) Hp17 I17 Hc17) as B17.
  pose proof (zb2gb_C_step 17 ltac:(lia)) as E18.
  rewrite z3z_G18 in E18.
  destruct (zb3z_gear 17 (16 * 17) 54 (8 * 1) E18 ltac:(lia) I17 Hp17) as (I18 & Hp18).
  assert (Hc18 : (((16 * 17) * 18) * (3 * (13 * (11 * 2520))) <= ((8 * 1) * 54) * 3 ^ 18)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 18 ((16 * 17) * 18) ((8 * 1) * 54) Hp18 I18 Hc18) as B18.
  exact (conj B17 (conj B18 (conj I18 Hp18))).
Qed.

Lemma zb3z_blk3 :
  (z2v_C 19 <= 3 ^ 19)%nat /\
  (z2v_C 20 <= 3 ^ 20)%nat /\
  (z2v_C 21 <= 3 ^ 21)%nat /\
  (z2v_C 22 <= 3 ^ 22)%nat /\
  ((z2v_C 22 * ((((((8 * 1) * 54) * 1) * 10) * 21) * 11) = ((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((8 * 1) * 54) * 1) * 10) * 21) * 11))%nat).
Proof.
  destruct zb3z_blk2 as (B17 & B18 & (I18 & Hp18)).
  pose proof (zb2gb_C_step 18 ltac:(lia)) as E19.
  rewrite z3z_G19 in E19.
  destruct (zb3z_gear 18 ((16 * 17) * 18) 1 ((8 * 1) * 54) E19 ltac:(lia) I18 Hp18) as (I19 & Hp19).
  assert (Hc19 : ((((16 * 17) * 18) * 19) * (3 * (13 * (11 * 2520))) <= (((8 * 1) * 54) * 1) * 3 ^ 19)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 19 (((16 * 17) * 18) * 19) (((8 * 1) * 54) * 1) Hp19 I19 Hc19) as B19.
  pose proof (zb2gb_C_step 19 ltac:(lia)) as E20.
  rewrite z3z_G20 in E20.
  destruct (zb3z_gear 19 (((16 * 17) * 18) * 19) 10 (((8 * 1) * 54) * 1) E20 ltac:(lia) I19 Hp19) as (I20 & Hp20).
  assert (Hc20 : (((((16 * 17) * 18) * 19) * 20) * (3 * (13 * (11 * 2520))) <= ((((8 * 1) * 54) * 1) * 10) * 3 ^ 20)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 20 ((((16 * 17) * 18) * 19) * 20) ((((8 * 1) * 54) * 1) * 10) Hp20 I20 Hc20) as B20.
  pose proof (zb2gb_C_step 20 ltac:(lia)) as E21.
  rewrite z3z_G21 in E21.
  destruct (zb3z_gear 20 ((((16 * 17) * 18) * 19) * 20) 21 ((((8 * 1) * 54) * 1) * 10) E21 ltac:(lia) I20 Hp20) as (I21 & Hp21).
  assert (Hc21 : ((((((16 * 17) * 18) * 19) * 20) * 21) * (3 * (13 * (11 * 2520))) <= (((((8 * 1) * 54) * 1) * 10) * 21) * 3 ^ 21)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 21 (((((16 * 17) * 18) * 19) * 20) * 21) (((((8 * 1) * 54) * 1) * 10) * 21) Hp21 I21 Hc21) as B21.
  pose proof (zb2gb_C_step 21 ltac:(lia)) as E22.
  rewrite z3z_G22 in E22.
  destruct (zb3z_gear 21 (((((16 * 17) * 18) * 19) * 20) * 21) 11 (((((8 * 1) * 54) * 1) * 10) * 21) E22 ltac:(lia) I21 Hp21) as (I22 & Hp22).
  assert (Hc22 : (((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * (3 * (13 * (11 * 2520))) <= ((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 3 ^ 22)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 22 ((((((16 * 17) * 18) * 19) * 20) * 21) * 22) ((((((8 * 1) * 54) * 1) * 10) * 21) * 11) Hp22 I22 Hc22) as B22.
  exact (conj B19 (conj B20 (conj B21 (conj B22 (conj I22 Hp22))))).
Qed.

Lemma zb3z_blk4 :
  (z2v_C 23 <= 3 ^ 23)%nat /\
  (z2v_C 24 <= 3 ^ 24)%nat /\
  ((z2v_C 24 * ((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) = ((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96))%nat).
Proof.
  destruct zb3z_blk3 as (B19 & B20 & B21 & B22 & (I22 & Hp22)).
  pose proof (zb2gb_C_step 22 ltac:(lia)) as E23.
  rewrite z3z_G23 in E23.
  destruct (zb3z_gear 22 ((((((16 * 17) * 18) * 19) * 20) * 21) * 22) 1 ((((((8 * 1) * 54) * 1) * 10) * 21) * 11) E23 ltac:(lia) I22 Hp22) as (I23 & Hp23).
  assert (Hc23 : ((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * (3 * (13 * (11 * 2520))) <= (((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 3 ^ 23)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 23 (((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) (((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) Hp23 I23 Hc23) as B23.
  pose proof (zb2gb_C_step 23 ltac:(lia)) as E24.
  rewrite z3z_G24 in E24.
  destruct (zb3z_gear 23 (((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) 96 (((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) E24 ltac:(lia) I23 Hp23) as (I24 & Hp24).
  assert (Hc24 : (((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * (3 * (13 * (11 * 2520))) <= ((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 3 ^ 24)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 24 ((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) ((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) Hp24 I24 Hc24) as B24.
  exact (conj B23 (conj B24 (conj I24 Hp24))).
Qed.

Lemma zb3z_blk5 :
  (z2v_C 25 <= 3 ^ 25)%nat /\
  (z2v_C 26 <= 3 ^ 26)%nat /\
  (z2v_C 27 <= 3 ^ 27)%nat /\
  (z2v_C 28 <= 3 ^ 28)%nat /\
  ((z2v_C 28 * ((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) = ((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56))%nat).
Proof.
  destruct zb3z_blk4 as (B23 & B24 & (I24 & Hp24)).
  pose proof (zb2gb_C_step 24 ltac:(lia)) as E25.
  rewrite z3z_G25 in E25.
  destruct (zb3z_gear 24 ((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) 1 ((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) E25 ltac:(lia) I24 Hp24) as (I25 & Hp25).
  assert (Hc25 : ((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * (3 * (13 * (11 * 2520))) <= (((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 3 ^ 25)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 25 (((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) (((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) Hp25 I25 Hc25) as B25.
  pose proof (zb2gb_C_step 25 ltac:(lia)) as E26.
  rewrite z3z_G26 in E26.
  destruct (zb3z_gear 25 (((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) 13 (((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) E26 ltac:(lia) I25 Hp25) as (I26 & Hp26).
  assert (Hc26 : (((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * (3 * (13 * (11 * 2520))) <= ((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 3 ^ 26)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 26 ((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) ((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) Hp26 I26 Hc26) as B26.
  pose proof (zb2gb_C_step 26 ltac:(lia)) as E27.
  rewrite z3z_G27 in E27.
  destruct (zb3z_gear 26 ((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) 9 ((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) E27 ltac:(lia) I26 Hp26) as (I27 & Hp27).
  assert (Hc27 : ((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * (3 * (13 * (11 * 2520))) <= (((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 3 ^ 27)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 27 (((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) (((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) Hp27 I27 Hc27) as B27.
  pose proof (zb2gb_C_step 27 ltac:(lia)) as E28.
  rewrite z3z_G28 in E28.
  destruct (zb3z_gear 27 (((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) 56 (((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) E28 ltac:(lia) I27 Hp27) as (I28 & Hp28).
  assert (Hc28 : (((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * (3 * (13 * (11 * 2520))) <= ((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 3 ^ 28)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 28 ((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) ((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) Hp28 I28 Hc28) as B28.
  exact (conj B25 (conj B26 (conj B27 (conj B28 (conj I28 Hp28))))).
Qed.

Lemma zb3z_blk6 :
  (z2v_C 29 <= 3 ^ 29)%nat /\
  (z2v_C 30 <= 3 ^ 30)%nat /\
  ((z2v_C 30 * ((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) = ((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150))%nat).
Proof.
  destruct zb3z_blk5 as (B25 & B26 & B27 & B28 & (I28 & Hp28)).
  pose proof (zb2gb_C_step 28 ltac:(lia)) as E29.
  rewrite z3z_G29 in E29.
  destruct (zb3z_gear 28 ((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) 1 ((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) E29 ltac:(lia) I28 Hp28) as (I29 & Hp29).
  assert (Hc29 : ((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * (3 * (13 * (11 * 2520))) <= (((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 3 ^ 29)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 29 (((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) (((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) Hp29 I29 Hc29) as B29.
  pose proof (zb2gb_C_step 29 ltac:(lia)) as E30.
  rewrite z3z_G30 in E30.
  destruct (zb3z_gear 29 (((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) 150 (((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) E30 ltac:(lia) I29 Hp29) as (I30 & Hp30).
  assert (Hc30 : (((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * (3 * (13 * (11 * 2520))) <= ((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 3 ^ 30)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 30 ((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) ((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) Hp30 I30 Hc30) as B30.
  exact (conj B29 (conj B30 (conj I30 Hp30))).
Qed.

Lemma zb3z_blk7 :
  (z2v_C 31 <= 3 ^ 31)%nat /\
  (z2v_C 32 <= 3 ^ 32)%nat /\
  (z2v_C 33 <= 3 ^ 33)%nat /\
  (z2v_C 34 <= 3 ^ 34)%nat /\
  ((z2v_C 34 * ((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) = ((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17))%nat).
Proof.
  destruct zb3z_blk6 as (B29 & B30 & (I30 & Hp30)).
  pose proof (zb2gb_C_step 30 ltac:(lia)) as E31.
  rewrite z3z_G31 in E31.
  destruct (zb3z_gear 30 ((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) 1 ((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) E31 ltac:(lia) I30 Hp30) as (I31 & Hp31).
  assert (Hc31 : ((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * (3 * (13 * (11 * 2520))) <= (((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 3 ^ 31)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 31 (((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) (((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) Hp31 I31 Hc31) as B31.
  pose proof (zb2gb_C_step 31 ltac:(lia)) as E32.
  rewrite z3z_G32 in E32.
  destruct (zb3z_gear 31 (((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) 16 (((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) E32 ltac:(lia) I31 Hp31) as (I32 & Hp32).
  assert (Hc32 : (((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 3 ^ 32)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 32 ((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) ((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) Hp32 I32 Hc32) as B32.
  pose proof (zb2gb_C_step 32 ltac:(lia)) as E33.
  rewrite z3z_G33 in E33.
  destruct (zb3z_gear 32 ((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) 11 ((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) E33 ltac:(lia) I32 Hp32) as (I33 & Hp33).
  assert (Hc33 : ((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * (3 * (13 * (11 * 2520))) <= (((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 3 ^ 33)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 33 (((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) (((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) Hp33 I33 Hc33) as B33.
  pose proof (zb2gb_C_step 33 ltac:(lia)) as E34.
  rewrite z3z_G34 in E34.
  destruct (zb3z_gear 33 (((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) 17 (((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) E34 ltac:(lia) I33 Hp33) as (I34 & Hp34).
  assert (Hc34 : (((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 3 ^ 34)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 34 ((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) ((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) Hp34 I34 Hc34) as B34.
  exact (conj B31 (conj B32 (conj B33 (conj B34 (conj I34 Hp34))))).
Qed.

Lemma zb3z_blk8 :
  (z2v_C 35 <= 3 ^ 35)%nat /\
  (z2v_C 36 <= 3 ^ 36)%nat /\
  ((z2v_C 36 * ((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) = ((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216))%nat).
Proof.
  destruct zb3z_blk7 as (B31 & B32 & B33 & B34 & (I34 & Hp34)).
  pose proof (zb2gb_C_step 34 ltac:(lia)) as E35.
  rewrite z3z_G35 in E35.
  destruct (zb3z_gear 34 ((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) 5 ((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) E35 ltac:(lia) I34 Hp34) as (I35 & Hp35).
  assert (Hc35 : ((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * (3 * (13 * (11 * 2520))) <= (((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 3 ^ 35)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 35 (((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) (((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) Hp35 I35 Hc35) as B35.
  pose proof (zb2gb_C_step 35 ltac:(lia)) as E36.
  rewrite z3z_G36 in E36.
  destruct (zb3z_gear 35 (((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) 216 (((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) E36 ltac:(lia) I35 Hp35) as (I36 & Hp36).
  assert (Hc36 : (((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 3 ^ 36)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 36 ((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) ((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) Hp36 I36 Hc36) as B36.
  exact (conj B35 (conj B36 (conj I36 Hp36))).
Qed.

Lemma zb3z_blk9 :
  (z2v_C 37 <= 3 ^ 37)%nat /\
  (z2v_C 38 <= 3 ^ 38)%nat /\
  (z2v_C 39 <= 3 ^ 39)%nat /\
  (z2v_C 40 <= 3 ^ 40)%nat /\
  ((z2v_C 40 * ((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) = ((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20))%nat).
Proof.
  destruct zb3z_blk8 as (B35 & B36 & (I36 & Hp36)).
  pose proof (zb2gb_C_step 36 ltac:(lia)) as E37.
  rewrite z3z_G37 in E37.
  destruct (zb3z_gear 36 ((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) 1 ((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) E37 ltac:(lia) I36 Hp36) as (I37 & Hp37).
  assert (Hc37 : ((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * (3 * (13 * (11 * 2520))) <= (((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 3 ^ 37)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 37 (((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) (((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) Hp37 I37 Hc37) as B37.
  pose proof (zb2gb_C_step 37 ltac:(lia)) as E38.
  rewrite z3z_G38 in E38.
  destruct (zb3z_gear 37 (((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) 19 (((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) E38 ltac:(lia) I37 Hp37) as (I38 & Hp38).
  assert (Hc38 : (((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 3 ^ 38)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 38 ((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) ((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) Hp38 I38 Hc38) as B38.
  pose proof (zb2gb_C_step 38 ltac:(lia)) as E39.
  rewrite z3z_G39 in E39.
  destruct (zb3z_gear 38 ((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) 13 ((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) E39 ltac:(lia) I38 Hp38) as (I39 & Hp39).
  assert (Hc39 : ((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * (3 * (13 * (11 * 2520))) <= (((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 3 ^ 39)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 39 (((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) (((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) Hp39 I39 Hc39) as B39.
  pose proof (zb2gb_C_step 39 ltac:(lia)) as E40.
  rewrite z3z_G40 in E40.
  destruct (zb3z_gear 39 (((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) 20 (((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) E40 ltac:(lia) I39 Hp39) as (I40 & Hp40).
  assert (Hc40 : (((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 3 ^ 40)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 40 ((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) ((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) Hp40 I40 Hc40) as B40.
  exact (conj B37 (conj B38 (conj B39 (conj B40 (conj I40 Hp40))))).
Qed.

Lemma zb3z_blk10 :
  (z2v_C 41 <= 3 ^ 41)%nat /\
  (z2v_C 42 <= 3 ^ 42)%nat /\
  ((z2v_C 42 * ((((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) * 1764) = ((((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) * 42) * (3 * (13 * (11 * 2520))))%nat /\
   (0 < ((((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) * 1764))%nat).
Proof.
  destruct zb3z_blk9 as (B37 & B38 & B39 & B40 & (I40 & Hp40)).
  pose proof (zb2gb_C_step 40 ltac:(lia)) as E41.
  rewrite z3z_G41 in E41.
  destruct (zb3z_gear 40 ((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) 1 ((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) E41 ltac:(lia) I40 Hp40) as (I41 & Hp41).
  assert (Hc41 : ((((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) * (3 * (13 * (11 * 2520))) <= (((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) * 3 ^ 41)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 41 (((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) (((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) Hp41 I41 Hc41) as B41.
  pose proof (zb2gb_C_step 41 ltac:(lia)) as E42.
  rewrite z3z_G42 in E42.
  destruct (zb3z_gear 41 (((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) 1764 (((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) E42 ltac:(lia) I41 Hp41) as (I42 & Hp42).
  assert (Hc42 : (((((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) * 42) * (3 * (13 * (11 * 2520))) <= ((((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) * 1764) * 3 ^ 42)%nat).
  { zb3z_Zcmp_tac. }
  pose proof (zb3z_link15 42 ((((((((((((((((((((((((((16 * 17) * 18) * 19) * 20) * 21) * 22) * 23) * 24) * 25) * 26) * 27) * 28) * 29) * 30) * 31) * 32) * 33) * 34) * 35) * 36) * 37) * 38) * 39) * 40) * 41) * 42) ((((((((((((((((((((((((((8 * 1) * 54) * 1) * 10) * 21) * 11) * 1) * 96) * 1) * 13) * 9) * 56) * 1) * 150) * 1) * 16) * 11) * 17) * 5) * 216) * 1) * 19) * 13) * 20) * 1) * 1764) Hp42 I42 Hc42) as B42.
  exact (conj B41 (conj B42 (conj I42 Hp42))).
Qed.

(* ============================================================ *)
(* §4 主语句合成：[1,42] 全段 C 值序界（[1,15] 肢直取 zb3j_base15 零重做）   *)
(* ============================================================ *)

Theorem zb3z_base42 : forall n : nat,
  (1 <= n)%nat -> (n <= 42)%nat -> (z2v_C n <= 3 ^ n)%nat.
Proof.
  intros n H1 H42.
  destruct zb3z_blk1 as (B16 & _).
  destruct zb3z_blk2 as (B17 & B18 & _).
  destruct zb3z_blk3 as (B19 & B20 & B21 & B22 & _).
  destruct zb3z_blk4 as (B23 & B24 & _).
  destruct zb3z_blk5 as (B25 & B26 & B27 & B28 & _).
  destruct zb3z_blk6 as (B29 & B30 & _).
  destruct zb3z_blk7 as (B31 & B32 & B33 & B34 & _).
  destruct zb3z_blk8 as (B35 & B36 & _).
  destruct zb3z_blk9 as (B37 & B38 & B39 & B40 & _).
  destruct zb3z_blk10 as (B41 & B42 & _).
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n43]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  - lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - apply zb3j_base15; lia.
  - exact B16.
  - exact B17.
  - exact B18.
  - exact B19.
  - exact B20.
  - exact B21.
  - exact B22.
  - exact B23.
  - exact B24.
  - exact B25.
  - exact B26.
  - exact B27.
  - exact B28.
  - exact B29.
  - exact B30.
  - exact B31.
  - exact B32.
  - exact B33.
  - exact B34.
  - exact B35.
  - exact B36.
  - exact B37.
  - exact B38.
  - exact B39.
  - exact B40.
  - exact B41.
  - exact B42.
  - lia.
Qed.

(* ============================================================ *)
(* §5 Set 面出口：HM2 面之 [1,42] 段实例（NatLe 承载·zb3j §4 同构）         *)
(* ============================================================ *)

Theorem zb3z_HM2_face_42 : forall n : nat,
  (1 <= n)%nat -> (n <= 42)%nat -> zb3m_HM2_face n.
Proof.
  intros n H1 H42. unfold zb3m_HM2_face.
  apply NatLe_lift. apply zb3z_base42; assumption.
Qed.

(* ============================================================ *)
(* §6 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction zb3z_HM2_face_42.

Print Assumptions zb3z_Zcmp.
Print Assumptions zb3z_inj_mul.
Print Assumptions zb3z_inj_pow.
Print Assumptions zb3z_anchor41.
Print Assumptions zb3z_pos_mul.
Print Assumptions zb3z_gear.
Print Assumptions zb3z_link15.
Print Assumptions zb3z_blk1.
Print Assumptions zb3z_blk2.
Print Assumptions zb3z_blk3.
Print Assumptions zb3z_blk4.
Print Assumptions zb3z_blk5.
Print Assumptions zb3z_blk6.
Print Assumptions zb3z_blk7.
Print Assumptions zb3z_blk8.
Print Assumptions zb3z_blk9.
Print Assumptions zb3z_blk10.
Print Assumptions zb3z_base42.
Print Assumptions zb3z_HM2_face_42.
