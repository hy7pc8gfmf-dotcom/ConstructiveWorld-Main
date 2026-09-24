(* ========================================================================= *)
(* 【ToyR 战役·包AW三·T300 台账席】玩具级定理同名非平凡替换稿（补标头注）    *)
(*                                                                           *)
(* 本稿系 ToyR 战役包AW三 替换落件（原名落件）；落件时头部漏植战役标记，     *)
(* 本块由 T326 异常修复席于 2026-09-22 补植：仅加头注，语句面／证明体／      *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/T300。       *)
(* 替换定理清单：sa_norm_bridge（共 1 刀，刀面以台账为权威）                 *)
(* 非平凡性口径：unfold sa_A 后 bi_norm_factor 本述展开形 delta 显式化       *)
(* 直取，无行拆分式假非平凡。                                                *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；补标零改动不触        *)
(* 证明面，落件录判绿承来源台账。                                            *)
(* ========================================================================= *)
(* ============================================================ *)
(* SupplyAssembly.v — 切片代理D034（批次 E-STAGING-D034，20260918）   *)
(*               T135 supply 装配攻坚（d_n² 战役收官件）。              *)
(*                                                               *)
(* 使命：实例化 Ln2Bridge L1 的 ln2i_pade_supply（sigT 五层五肢）并     *)
(*   依存 L4 ln2b_irrational_from_supply 出 ln2 无理数闭合。           *)
(*                                                               *)
(* 【装配判定（五件 API 实形择路，诚实降档登记）】                      *)
(*  A_n 整数面（已装）：sa_A n := 2^{n+1}·q̃_n 的 Z.of_nat nat 承载      *)
(*    ——q̃_n := bk_Qn_qtilde n ∈ nat 在册（BeukersLists），D016 勘误    *)
(*    真归一因子 2^{n+1}q̃_n == 2^{2n+1}Q_n(1/2)（bi_norm_factor）即    *)
(*    本面之归一桥（§4 sa_norm_bridge 全等换算）。肢② 0<|A_n| 由       *)
(*    q̃_n ≥ 3^n ≥ 1 供给（sa_A_nonzeroT 真证）。                      *)
(*    择路理由：B_n 候选两形皆无在册 Z 面——① r_n := 2^{n+1}p_n 形：     *)
(*    D021 bv_p3_anchor 锚定 p_3 == 131/3 非整 ⟹ r_3 = 2^4·131/3       *)
(*    非整（n=3 起整数面塌）；② 调和形 r'_n := 2^n·p̃_n/L_n（据          *)
(*    pi_x_n_frac 的 x'_n == p̃_n/(2L_nq̃_n) 强面换算）：L_n | 2^n p̃_n  *)
(*    无在册整除定理。故 B_n 取「任意整数面 + 两 real 肢」的缺口接口    *)
(*    sa_supply_rem 遗留（语义精确：实例化消解槽=④下界/⑤上界两个合取肢本身）。      *)
(*  clo_n 正性肢（已装）：sa_clo n := lne_B n = (n!)²/(2n+1)!，        *)
(*    肢③ 0 < clo_n 由 lne_B_posT（Beta 闭式正性，CZW13）直供；        *)
(*    另挂整性面 sa_clo_int（(n!)² ∈ Z 的 sigT 见证）作 B_n 组合原料。  *)
(*  θ<1 上界肢（θ 档已装，⑤本体遗留）：θ := 1/2。纯 Q 换算件           *)
(*    sa_theta_leg_scaffold 真证 1/(2^{n+1}q̃_n) ≤ (1/2)^n = θ^n——      *)
(*    即勘误恒等式误差端 I_n/(2^{n+1}q̃_n) ≤ 2^{1−n}/(2^{n+1}q̃_n)      *)
(*    = 2^{−2n}/q̃_n ≤ θ^n 的收尾档（I_n ≤ 2^{1−n} = 2^{n+1}·B_n      *)
(*    ≤ 2^{n+1}·4^{−n} 由 lne_B_le_p4 换算，其积分端半边亦遗留）。      *)
(*    窗匹配件 sa_clo_in_theta_window：clo_n < θ^n（n≥1，真证）——      *)
(*    载体严格落入 θ 档判定窗（lne_B_lt_p2 + 半幂逆换算）。             *)
(*  【精确卡点（⑤④肢遗留面，禁虚报 unconditional）】两 real 肢需要     *)
(*    P2 恒等式本体 I_n = 2^{n+1}q̃_n·X − r_n（X := ln2b_X = lim        *)
(*    ln2i_x）：五件 API 无任何已证定理把 A_n/B_n 组合与 X 连接          *)
(*    （D016 头注已证结论「恒等式本体需积分/部分分式引擎，窗内不可达」）。   *)
(*    本体拆三子件均未建：(a) 部分分式引擎（tⁿ(1−t)ⁿ/(1−t/2)^{n+1}     *)
(*    的多项式部+单极点 2 分解，∫₀¹(2−t)^{−1}dt = ln2 端）；            *)
(*    (b) 残数系数 c₁ = 2^n·q̃_n（Delannoy [w^n](2+w)^n(1+w)^n 抽取，  *)
(*    bi_D 核心在册可复用）；(c) ln2 = lim ln2i_x 与线积分核验          *)
(*    （级数 Σ 1/(k·2^k) 的积分表示）。三者到货后 sa_supply_rem 即可    *)
(*    实例化消解，经 sa_supply_assemble ⟹ sa_ln2_irrational 全链无条件形。    *)
(*  装配达成等级：**两段式条件形**——sa_supply_assemble（三肢已装 +      *)
(*    缺口接口 ⟹ ln2i_pade_supply 全型，真证）+ sa_ln2_irrational      *)
(*    （依存 L4 ln2b_irrational_from_supply，真走母定理零旁路）。        *)
(*    sa_supply_three_legs 为三肢独立封装件。零认授、零虚报。            *)
(*                                                               *)
(* 验证（本地信任缓存策略，t120g/d015/e118 配方）：G1 官方禁词 0；       *)
(*   G2 side-compile /tmp/d034_side（异地 cwd + czn14_union 并集根      *)
(*   单 -Q + t120g_side/e118_side 现编池 + cpu_guard，≤15 分钟）；      *)
(*   G3 Separate Extraction Obj.magic=0；G4 rocq check -o + PA 全       *)
(*   Closed 候 detached 链（台账 Live/logs/）。本地绿=放行信号，         *)
(*   终验归隔壁 CI。                                                    *)
(* 依赖（czn14_union 信任根 + side 现编池在册）：S01_BaseRing、         *)
(*   S02_CauchyComplete、S03_QExp、BeukersLists（e118/d015/e121）、     *)
(*   BeukersIdentity（e118）、Ln2Escape（本席 /tmp/d034_side 现编）、    *)
(*   Ln2Bridge（t120g）；Stdlib QArith、ZArith、Arith、Lia、Setoid、    *)
(*   Morphisms、Lra、Qfield。                                           *)
(* 语句面纪律：装配件全 Set（sigT/S01.And/QltT/QleT'/QeqT/real_le/      *)
(*   real_lt）；Q 层 Qeq/Qle 支撑引理仅作推理脚手架（Ln2Bridge 先例）。  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §1 A_n 整数面（肢②）+ 归一桥换算                                     *)
(* ============================================================ *)

(* A_n := 2^{n+1}·q̃_n 的整数面（nat 承载 Z 化） *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* A_n 的 Q 承载 == 2^{n+1}·q̃_n（bi_q_pow_2 + bk_Qmul_nat 换算） *)
Lemma sa_A_q : forall n : nat,
  ((sa_A n) # 1)%Q
  == ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. rewrite bi_q_pow_2. symmetry. apply bk_Qmul_nat.
Qed.

(* 肢②真证：0 < |A_n|（q̃_n ≥ 3^n ≥ 1 ⟹ A_n ≥ 2） *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (bk_Qn_ge_3pow_nat n) as H3.
    pose proof (bi_pow3_pos n) as Hp.
    pose proof (ln2b_pow_ge1 2 n ltac:(lia)) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* 归一桥换算件：sa_A n # 1 == 2^{2n+1}·Q_n(1/2)（bi_norm_factor 全等
   换算——D016 勘误真归一因子 2^{n+1}q̃_n 的闭式落点） *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. unfold sa_A. exact (bi_norm_factor n). Qed.

(* ============================================================ *)
(* §2 clo_n 正性肢（肢③）+ 载体整性/上界支撑面                          *)
(* ============================================================ *)

(* 载体：clo_n := lne_B n = ∫₀¹ tⁿ(1−t)ⁿ dt 的闭式 (n!)²/(2n+1)! *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* 肢③真证：0 < clo_n（Beta 闭式正性直供） *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. exact (lne_B_posT n). Qed.

(* 载体整性面：clo_n·(2n+1)! == (n!)² ∈ Z（sigT 见证——B_n 整数面
   组合原料，P2 分子侧到货后 r_n 的 Z 化即走此面） *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* 载体上界面：clo_n ≤ 4^{−n}（I_n ≤ 2^{n+1}·clo_n ≤ 2^{1−n} 的 Q 端
   原料；其积分端半边 1/(1−t/2)^{n+1} ≤ 2^{n+1} 随 P2 本体遗留） *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* ============================================================ *)
(* §3 θ 档（肢①）+ 半幂换算机                                          *)
(* ============================================================ *)

Definition sa_theta : Q := (1 # 2)%Q.

(* 肢①真证：θ = 1/2 < 1 *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* θ 正性（L2 衰减机 ln2b_decay 的前置面，登记备用） *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* 1 的幂 *)
Lemma sa_qpow_one_q : forall n : nat, q_pow (1 # 1)%Q n == (1 # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

(* 半幂逆：q_pow (1/2) n · q_pow 2 n == 1（ln2b_qpow_inv 换算） *)
Lemma sa_half_pow : forall n : nat,
  q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n == (1 # 1)%Q.
Proof.
  intro n. rewrite (ln2b_qpow_inv 1%Z 2%positive n).
  apply sa_qpow_one_q.
Qed.

(* 半幂逆换算：2^{−n} == (1/2)^n *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  Qinv (q_pow (2 # 1)%Q n) == q_pow (1 # 2)%Q n.
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E. pose proof (bi_q_pow_pos2 n) as Hp.
    apply (Qlt_not_eq 0%Q (q_pow (2 # 1)%Q n) Hp). exact (Qeq_sym _ _ E). }
  assert (Hm := sa_half_pow n).
  assert (H1 : (Qinv (q_pow (2 # 1)%Q n) * q_pow (2 # 1)%Q n)%Q
               == (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n)%Q).
  { rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite Hm. reflexivity. }
  apply (lne_mult_canc _ _ (q_pow (2 # 1)%Q n)); [exact H1 | exact Hnz].
Qed.

(* Q 逆单调：0 < a ≤ b ⟹ 1/b ≤ 1/a（Q 层脚手架，Z 分支 nia） *)
Lemma sa_Qinv_le : forall a b : Q, Qlt 0%Q a -> Qle a b -> Qle (Qinv b) (Qinv a).
Proof.
  intros [an ad] [bn bd] Ha Hab.
  unfold Qlt, Qle in Ha, Hab. cbn [Qnum Qden] in Ha, Hab.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* θ 肢纯 Q 换算件（真证）：1/(2^{n+1}·q̃_n) ≤ (1/2)^n = θ^n——
   勘误恒等式误差端 2^{−2n}/q̃_n ≤ θ^n 的收尾档（q̃_n ≥ 3^n ≥ 1） *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'.
  setoid_rewrite <- (sa_theta_pow_inv2 n).
  apply sa_Qinv_le.
  - apply bi_q_pow_pos2.
  - assert (Hq1 : (1 <= bk_Qn_qtilde n)%nat).
    { pose proof (bk_Qn_ge_3pow_nat n) as H3.
      pose proof (bi_pow3_pos n) as Hp. lia. }
    setoid_rewrite (bi_q_pow_2 (Datatypes.S n)).
    setoid_rewrite (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n)).
    setoid_rewrite (bi_q_pow_2 n).
    apply bk_Qle_nat. rewrite Nat.pow_succ_r'. nia.
Qed.

(* 窗匹配件（真证）：clo_n < θ^n（n ≥ 1）——载体严格落入 θ 档判定窗
   （lne_B_lt_p2 的 2^{−n} 窗经 sa_theta_pow_inv2 换算到 θ 档） *)
Theorem sa_clo_in_theta_window : forall n : nat, (1 <= n)%nat ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (QltT_to_Qlt _ _ (lne_B_lt_p2 n Hn)).
  - reflexivity.
  - unfold sa_theta.
    rewrite ln2i_p2_Z. rewrite <- (bi_q_pow_2 n).
    apply sa_theta_pow_inv2.
Qed.

(* ============================================================ *)
(* §4 三肢独立封装件（①②③已装面）                                      *)
(* ============================================================ *)

(* 三肢头型（supply 五肢之①②③的独立封装） *)
Definition sa_supply_head : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun clo : nat -> Q =>
      sigT (fun th : Q =>
        And (QltT th (1 # 1))
          (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
               (forall n : nat, QltT 0 (clo n)))))).

Theorem sa_supply_three_legs : sa_supply_head.
Proof.
  exists sa_A. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + apply sa_clo_posT.
Qed.

(* ============================================================ *)
(* §5 缺口接口（④⑤肢精确遗留）+ 两段式装配闭合                          *)
(* ============================================================ *)

(* 缺口接口：B_n 整数面 + ④下界/⑤上界两 real 肢——P2 恒等式本体
   （I_n = 2^{n+1}q̃_n·X − r_n，三子件见头注 (a)(b)(c)）到货后的实例化消解槽。
   语义精确：本接口非空性即 θ 档 Padé 逼近列的存在性，本席不虚判。 *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* 两段式装配：三肢已装面 + 缺口接口 ⟹ supply 全型（五层 sigT 全填） *)
Theorem sa_supply_assemble : forall Hm : sa_supply_rem, ln2i_pade_supply.
Proof.
  intros [B [Hlow Hup]].
  exists sa_A. exists B. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + split.
      * apply sa_clo_posT.
      * split.
        -- exact Hlow.
        -- exact Hup.
Qed.

(* ln2 无理数两段式闭合：依存 Ln2Bridge L4 源模块
   ln2b_irrational_from_supply（真走 lic_irrational_criterion 零旁路）。
   语句面 = L4 结论面焊开形（全 Set：sigT/And/QltT/real_lt）。 *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q. exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* ============================================================ *)
(* §6 数值锚（vm_compute 档：A_1 = 2²·q̃_1 = 12，A_2 = 2³·q̃_2 = 104，  *)
(*    clo_1 = 1/6，θ^n 档半幂锚）                                       *)
(* ============================================================ *)

Theorem sa_A1_anchor : QeqT ((sa_A 1) # 1)%Q (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_A2_anchor : QeqT ((sa_A 2) # 1)%Q (104 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_clo1_anchor : QeqT (sa_clo 1) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_theta2_anchor : QeqT (q_pow sa_theta 2) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 提取检验与 PA 自审（G3/G4 本地段）                                 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.
